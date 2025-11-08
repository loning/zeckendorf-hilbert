# eboc_minimal.py
import numpy as np, gzip, io, math
from typing import Tuple, List

# ---------- 1D, binary, radius-1 ECA ----------
class ECA:
    def __init__(self, rule_no: int):
        if not (0 <= rule_no <= 255):
            raise ValueError("Rule number must be in [0, 255].")
        self.rule_no = rule_no
        self.r = 1  # ECA 半径
        # bits[i] = 邻域 (l,c,r) 的输出；i = (l<<2)|(c<<1)|r, i∈[0,7]
        self.bits = np.array([(rule_no >> i) & 1 for i in range(8)], dtype=np.uint8)

    def step(self, state: np.ndarray) -> np.ndarray:
        """一次同步更新（周期边界）。"""
        L = state.shape[0]
        left  = np.roll(state, +1)
        right = np.roll(state, -1)
        idx = (left << 2) | (state << 1) | right
        return self.bits[idx]

    def simulate(self, L: int, T: int, init: np.ndarray = None, seed: int = 0) -> np.ndarray:
        """返回时空块 X，shape=(T, L)，X[t] 为时刻 t 的空间配置。"""
        if init is None:
            rng = np.random.default_rng(seed)
            cur = rng.integers(0, 2, size=L, dtype=np.uint8)
        else:
            cur = np.array(init, dtype=np.uint8)
            if cur.shape[0] != L:
                raise ValueError("init length must match L")
        X = np.zeros((T, L), dtype=np.uint8)
        X[0] = cur
        for t in range(1, T):
            cur = self.step(cur)
            X[t] = cur
        return X

# ---------- T4: 厚边界索引（time-slice 立方窗特例） ----------
def thick_boundary_indices(i0: int, i1: int, T: int, r: int) -> Tuple[int, int]:
    """
    W = [i0, i1) × [t0, t0+T-1] 的时间厚度为 T；
    T4 的 time-slice 特例给出：Δ_dep^-(W) = ( [i0, i1) + [-rT, rT] ) × {t0-1}.
    返回该一维边界在 t0-1 层的闭区间 [b0, b1]（含端点）。
    """
    return i0 - r*T, i1 - 1 + r*T

# ---------- T4: 仅用厚边界重建 W ----------
def reconstruct_W_from_boundary(eca: ECA,
                                boundary_at_tminus1: np.ndarray,
                                i0: int, i1: int, T: int) -> np.ndarray:
    """
    用 (t0-1) 层上的厚边界（长度 (i1-i0)+2*r*T）按 T4 的“层层推进”算法重建
    W = [i0, i1) × [t0, t0+T-1]。为防止依赖泄露，局部段内部演化不做环绕。
    """
    r = eca.r
    seg_left, seg_right = i0 - r*T, i1 - 1 + r*T
    seg_len = seg_right - seg_left + 1
    cur = boundary_at_tminus1.copy()
    assert cur.shape[0] == seg_len

    def step_local(state: np.ndarray) -> np.ndarray:
        # 只在段内做一次更新；端点的邻域在本算法里永不被查询（后续只取内层）
        left  = np.empty_like(state); left[1:]  = state[:-1]; left[0]  = 0
        right = np.empty_like(state); right[:-1]= state[1:] ; right[-1] = 0
        idx = (left << 2) | (state << 1) | right
        return eca.bits[idx]

    rows = []
    for j in range(T):
        nxt = step_local(cur)
        # t = t0 + j 时，所需空间范围是 [i0 - r*j, i1-1 + r*j]
        Lloc = (i0 - r*T)  # 全局 seg_left
        lo = (i0 - r*j) - Lloc
        hi = (i1 - 1 + r*j) - Lloc
        rows.append(nxt[lo:hi+1])
        cur = nxt

    # rows[j] 的长度为 (i1-i0) + 2*r*j；取其中心 (i1-i0) 段还原 W 的该层
    base_len = i1 - i0
    W = np.zeros((T, base_len), dtype=np.uint8)
    for j in range(T):
        start = (rows[j].shape[0] - base_len) // 2
        W[j] = rows[j][start:start+base_len]
    return W

# ---------- T3/T17: 观察（因子）π：读取中心元每 b 层一采样 ----------
def decode_center_trace(X: np.ndarray, center: int, t0: int, T: int, b: int = 1) -> np.ndarray:
    """
    叶序读取（leaf-by-leaf）：从 t0 开始每 b 层读取一次 center 位置（步长 b = <τ*,τ>）。
    返回长度 floor(T/b) 的 0/1 序列。
    """
    t_idx = np.arange(t0, t0 + T, b)
    return X[t_idx, center].astype(np.uint8)

# ---------- T5: gzip 作为 Kolmogorov 复杂度代理 ----------
def gzip_size(data: bytes) -> int:
    buf = io.BytesIO()
    with gzip.GzipFile(fileobj=buf, mode='wb') as f:
        f.write(data)
    return len(buf.getvalue())

def compress_ratio_of_trace(trace_bits: np.ndarray) -> Tuple[int, float]:
    """
    以 gzip 字节数作为 K(·) 的粗糙上界代理；返回 (压缩字节数, 每步字节数)。
    注意：仅为经验代理，用于观察“厚度归一化下的趋势”（T5 思想实验）。
    """
    s = ''.join('1' if b else '0' for b in trace_bits)
    z = gzip_size(s.encode('ascii'))
    return z, z / max(1, len(trace_bits))
