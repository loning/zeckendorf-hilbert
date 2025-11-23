# 附录 B：QCA 模拟指南

**Appendix B: Guide to Simulating QCA Universes**

物理学不仅仅是用来推导公式的，它也是用来**运行**的。本书所构建的"幺正计算宇宙"不仅存在于抽象的希尔伯特空间中，也完全可以在经典的数字计算机上进行模拟（尽管效率受限）。

本附录旨在为那些希望亲手"创造宇宙"的读者提供一份实用的编程指南。我们将展示如何用 Python 构建一个简单的、满足公理 $\Omega$ 的一维 Dirac-QCA 模型，并观察质量、波包扩散以及 Zitterbewegung 现象的涌现。

这不仅是对理论的验证，更是一次从"观察者"向"构建者"转型的初步尝试。

-----

## B.1 模拟器的基本架构

一个 QCA 模拟器主要由三个核心模块组成：

1. **状态寄存器（State Register）**：存储当前的全局波函数 $|\Psi(t)\rangle$。

2. **演化引擎（Evolution Engine）**：执行局域幺正算符 $\hat{U}$。

3. **观测模块（Measurement Module）**：计算可观测量（如位置概率分布、动量谱）。

### B.1.1 数据结构

在一维 QCA 中，我们有一个包含 $L$ 个格点的环（周期性边界条件）。每个格点有两个分量（左旋 $L$ 和右旋 $R$）。

因此，波函数可以用一个大小为 $(L, 2)$ 的复数数组表示。

```python
import numpy as np
import matplotlib.pyplot as plt

class QCAUniverse:
    def __init__(self, L, mass_theta):
        """
        初始化 QCA 宇宙
        L: 格点数 (空间大小)
        mass_theta: 质量参数 θ (对应 m*c^2*dt/hbar)
        """
        self.L = L
        self.theta = mass_theta
        
        # 波函数 psi[x, 0] = psi_L, psi[x, 1] = psi_R
        self.psi = np.zeros((L, 2), dtype=np.complex128)
        
        # 构建局域旋转矩阵 (Coin Operator)
        c, s = np.cos(self.theta), np.sin(self.theta)
        self.coin_op = np.array([[c, -1j*s], 
                                 [-1j*s, c]])
```

## B.2 演化算法：分裂算符法

根据狄拉克-QCA 模型（见正文第五章），单步演化算符分解为：

$$\hat{U} = \hat{S} \cdot \hat{C}(\theta)$$

其中 $\hat{C}$ 是局域旋转（混合左右手性），$\hat{S}$ 是条件平移。

### B.2.1 代码实现

```python
    def step(self):
        """执行一步时间演化: U = S * C"""
        
        # 1. Coin Step (局域旋转)
        # 对每个格点进行矩阵乘法: psi(x) = C . psi(x)
        # 使用 einsum 加速: 'ij,xj->xi' (i,j是自旋分量, x是空间)
        self.psi = np.einsum('ij,xj->xi', self.coin_op, self.psi)
        
        # 2. Shift Step (条件平移)
        # L 分量 (索引0) 向左移动 (x -> x-1) -> np.roll shift=-1
        # R 分量 (索引1) 向右移动 (x -> x+1) -> np.roll shift=+1
        # 注意：根据定义不同，方向可能相反，这里采用标准 QW 约定
        psi_L = np.roll(self.psi[:, 0], -1)
        psi_R = np.roll(self.psi[:, 1], 1)
        
        self.psi[:, 0] = psi_L
        self.psi[:, 1] = psi_R
```

## B.3 初始条件与观测

为了模拟一个粒子，我们需要初始化一个高斯波包。

```python
    def initialize_wavepacket(self, x0, k0, sigma):
        """
        初始化高斯波包
        x0: 中心位置
        k0: 初始动量
        sigma: 波包宽度
        """
        x = np.arange(self.L)
        # 高斯包络 * 平面波
        envelope = np.exp(-(x - x0)**2 / (4 * sigma**2))
        plane_wave = np.exp(1j * k0 * x)
        
        psi_init = envelope * plane_wave
        
        # 将其分配给 L 和 R 分量 (这里简单设为相等，对应自旋指向 x 方向)
        self.psi[:, 0] = psi_init / np.sqrt(2)
        self.psi[:, 1] = psi_init / np.sqrt(2)
        
        # 归一化
        norm = np.sqrt(np.sum(np.abs(self.psi)**2))
        self.psi /= norm

    def measure_probability(self):
        """返回位置概率分布 P(x)"""
        return np.sum(np.abs(self.psi)**2, axis=1)
    
    def measure_expectation_x(self):
        """计算位置期望值 <x>"""
        P = self.measure_probability()
        x = np.arange(self.L)
        # 处理周期性边界条件下的质心需要小心，这里假设波包远离边界
        return np.sum(x * P)
```

## B.4 实验脚本：验证 Zitterbewegung

现在，让我们运行这个宇宙，验证第五章的核心预言：**有质量粒子在微观上会颤动。**

```python
def run_zitterbewegung_experiment():
    L = 2000
    theta = 0.1  # 较小的质量参数
    steps = 500
    
    universe = QCAUniverse(L, theta)
    # 初始化动量为 0 的粒子
    universe.initialize_wavepacket(x0=L//2, k0=0, sigma=20)
    
    trajectory = []
    
    for t in range(steps):
        universe.step()
        x_avg = universe.measure_expectation_x()
        trajectory.append(x_avg)
        
    # 绘图
    t_axis = np.arange(steps)
    plt.plot(t_axis, trajectory)
    plt.title("Zitterbewegung Simulation (QCA)")
    plt.xlabel("Time Step")
    plt.ylabel("Expectation Position <x>")
    plt.show()

if __name__ == "__main__":
    run_zitterbewegung_experiment()
```

**预期结果**：

运行上述代码，你将看到 `<x>` 并不是一条直线（静止），而是在初始位置附近呈现出**高频、小幅度的正弦震荡**。

* 震荡频率 $\omega \approx 2\theta$。

* 这正是 Dirac 方程中 Zitterbewegung 现象的精确离散复现。

* 如果将 `theta` 设为 0（光子），震荡消失，波包将以速度 $c$ 分裂并飞向两端（或者保持静止如果不混合）。

## B.5 进阶挑战：弯曲时空模拟

要在 QCA 中模拟引力（第四章内容），我们需要引入**非均匀的折射率**。

这可以通过让质量参数 $\theta$ 或平移算符 $\hat{S}$ 依赖于位置 $x$ 来实现。

**修改思路**：

在 `step` 函数中，不使用统一的 `self.theta`，而是使用一个数组 `self.theta_field[x]`。

* 在"黑洞"附近，设置 `theta[x]` 非常大（接近 $\pi/2$），这将导致 $v_{int} \to c$，$v_{ext} \to 0$。

* 运行模拟，你会发现射入该区域的波包会急剧减速，波长被压缩，表现出引力红移和时空弯曲的特性。

通过这种方式，你不仅仅是在学习物理，你是在**编码物理**。每一个逻辑门，都是这个玩具宇宙的一条自然定律。

