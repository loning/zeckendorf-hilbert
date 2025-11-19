# demo_eboc_T4_T5.py
import numpy as np, pandas as pd, json
from eboc_minimal import ECA, thick_boundary_indices, reconstruct_W_from_boundary, decode_center_trace, compress_ratio_of_trace

def run_demo(seed=42):
    e110 = ECA(110)   # Rule-110（通用计算，复杂）——论文示例同款
    e90  = ECA(90)    # Rule-90（线性）
    L = 512
    T_max = 600
    X110 = e110.simulate(L=L, T=T_max, seed=seed)
    X90  = e90.simulate(L=L, T=T_max, seed=seed+1)

    # ---- T4：厚边界重建（Rule-110）----
    i0, i1 = 180, 260     # 空间窗 [i0,i1)
    t0, T  = 200, 80      # 时间窗 [t0, t0+T-1]
    r = e110.r
    b0, b1 = thick_boundary_indices(i0, i1, T, r)
    boundary = X110[t0-1, b0:b1+1]          # 仅取 (t0-1) 层的厚边界
    W_recon = reconstruct_W_from_boundary(e110, boundary, i0, i1, T)
    W_true  = X110[t0:t0+T, i0:i1]
    mismatches = int(np.sum(W_true != W_recon))

    # ---- T5：时间厚度归一的压缩趋势（中心点轨迹）----
    center = L // 2
    rows = []
    for Tval in [64, 128, 256, 384, 512]:
        tr110 = decode_center_trace(X110, center=center, t0=50, T=Tval, b=1)
        z110, r110 = compress_ratio_of_trace(tr110)
        tr90  = decode_center_trace(X90, center=center, t0=50, T=Tval, b=1)
        z90, r90  = compress_ratio_of_trace(tr90)
        rows.append({"T": Tval, "Rule": "110", "gzip_bytes": z110, "bytes_per_step": r110})
        rows.append({"T": Tval, "Rule": "90",  "gzip_bytes": z90,  "bytes_per_step": r90})
    df = pd.DataFrame(rows)

    summary = {
        "T4_window": {"i0": i0, "i1": i1, "t0": t0, "T": T},
        "thick_boundary_len_at_(t0-1)": int(b1 - b0 + 1),
        "mismatches_reconstruction_vs_truth": mismatches
    }
    return summary, df

if __name__ == "__main__":
    summary, df = run_demo()
    print("T4 reconstruction summary:")
    print(json.dumps(summary, indent=2))
    print("\nFirst 10 rows of T5 compression proxy table:")
    print(df.head(10).to_string(index=False))
    df.to_csv("t5_compression_proxy.csv", index=False)
    print("\nSaved: t5_compression_proxy.csv")
