**13.2 Gibbons-Hawking-York (GHY) 项的熵起源：边缘模式的配分函数**

在 13.1 节中，我们指出了爱因斯坦-希尔伯特作用量在狄利克雷边界条件下的变分不完备性：它留下了一个含度规法向导数的边界残项。本节将引入著名的 **Gibbons-Hawking-York (GHY)** 边界项来修复这一问题。

更重要的是，在本书构建的离散本体论框架下，GHY 项不再仅仅是一个为了数学自洽而引入的辅助项。我们将证明，在欧几里得路径积分表述中，**GHY 项正是全息熵 $S = A/4G$ 的真正来源**。它代表了时空边界上被"切断"的自由度——**边缘模式（Edge Modes）**——的配分函数对数。这一发现将数学上的变分完备性与物理上的全息原理完美统一。

### 13.2.1 GHY 边界项的构造与变分抵消证明

为了消除 13.1.1 节中导出的边界流项 $\int_{\partial M} v^\mu n_\mu$，我们需要在总作用量中添加一个反项（Counter-term）。

**定义 13.2.1 (Gibbons-Hawking-York 作用量)**

对于时空流形 $M$ 的边界 $\partial M$，设其诱导度规为 $h_{ab}$，外向单位法向量为 $n^\mu$（满足 $n^\mu n_\mu = \varepsilon = \pm 1$）。定义边界作用量为外微曲率（Extrinsic Curvature）的积分：

$$
I_{\text{GHY}} = \frac{\varepsilon}{8\pi G} \int_{\partial M} K \sqrt{|h|} \, \mathrm{d}^3y
$$

其中 $K = h^{ab} K_{ab} = \nabla_\mu n^\mu$ 是外微曲率张量的迹，描述了边界在法向流下的膨胀率。

**定理 13.2.2 (变分完备性定理)**

总作用量 $I_{\text{total}} = I_{\text{EH}} + I_{\text{GHY}}$ 在固定边界诱导度规（$\delta h_{ab} = 0$）的条件下是变分完备的。即：

$$
\delta I_{\text{total}} \Big|_{\delta h_{ab}=0} = \frac{1}{16\pi G} \int_M G_{\mu\nu} \delta g^{\mu\nu} \sqrt{-g} \, \mathrm{d}^4x
$$

边界上的法向导数项被精确抵消。

**证明**：

1.  **回顾 EH 作用量的边界项**：

    由 13.1 节，$\delta I_{\text{EH}}$ 产生的边界通量为：

    $$
    \delta I_{\text{EH}}^{\partial} = \frac{\varepsilon}{16\pi G} \int_{\partial M} (g^{\alpha\beta} \delta \Gamma^\mu_{\alpha\beta} - g^{\mu\alpha} \delta \Gamma^\beta_{\alpha\beta}) n_\mu \sqrt{|h|} \, \mathrm{d}^3y
    $$

    在固定 $h_{ab}$（即切向导数变分为零）下，主要贡献来自法向导数项 $\partial_n \delta g$。

2.  **计算 GHY 项的变分**：

    $$
    \delta I_{\text{GHY}} = \frac{\varepsilon}{8\pi G} \int_{\partial M} (\delta K \sqrt{|h|} + K \delta \sqrt{|h|})
    $$

    由于 $\delta h_{ab} = 0$，则 $\delta \sqrt{|h|} = \frac{1}{2}\sqrt{|h|} h^{ab} \delta h_{ab} = 0$。因此只需计算 $\delta K$。

    外微曲率 $K_{ab} = h_a^\mu h_b^\nu \nabla_\mu n_\nu$。其变分涉及法向量的变分 $\delta n_\mu$ 和联络的变分 $\delta \Gamma$。

    利用单位规范约束 $n^\mu n_\mu = \varepsilon$，可得 $\delta n_\mu = \frac{1}{2} \varepsilon n_\mu n^\rho n^\sigma \delta g_{\rho\sigma}$（在 $\delta h_{ab}=0$ 下此项通常为零，但在一般推导中保留）。

    关键项来自联络变分：

    $$
    \delta K \sim h^{\mu\nu} \delta (\nabla_\mu n_\nu) \sim h^{\mu\nu} n_\rho \delta \Gamma^\rho_{\mu\nu}
    $$

3.  **抵消验证**：

    将 $\delta \Gamma$ 展开为度规导数。可以证明，$\delta K$ 中的 $\partial_n \delta g$ 项系数恰好为 $-1/2$（相对于 EH 项中的系数）。

    由于 $I_{\text{GHY}}$ 前系数为 $1/8\pi G$（是 $I_{\text{EH}}$ 的 2 倍），二者精确抵消：

    $$
    \frac{1}{16\pi G} (\text{Flux}) + \frac{1}{8\pi G} (-\frac{1}{2} \text{Flux}) = 0
    $$

    $\square$

### 13.2.2 欧几里得路径积分与黑洞熵

在经典层面上，GHY 项只是一个数学修正。但在半经典引力（Semiclassical Gravity）中，它是熵的物理来源。

考虑欧几里得路径积分（Euclidean Path Integral），配分函数为：

$$
Z \approx e^{-I_E[g_{cl}]}
$$

其中 $I_E$ 是欧几里得作用量的鞍点值（On-shell Action）。热力学熵由 $S = (1 - \beta \partial_\beta) \ln Z$ 给出。

**定理 13.2.3 (GHY 熵生成定理)**

对于真空爱因斯坦引力（$R=0$），体作用量 $I_{\text{EH}}$ 在壳层上为零。系统的全部自由能和熵均来自边界项 $I_{\text{GHY}}$。对于史瓦西黑洞或其他具有基尔灵视界的热空间，由此导出的熵严格等于贝肯斯坦-霍金熵：

$$
S = \frac{A}{4G\hbar}
$$

**证明**：

以史瓦西黑洞为例，欧几里得度规为 $ds^2 = f(r) d\tau^2 + f(r)^{-1} dr^2 + r^2 d\Omega^2$，其中 $\tau$ 周期为 $\beta = 1/T_H$。

1.  **体积分**：$R=0$，故 $I_{\text{EH}} = 0$。

2.  **边界积分**：在 $r=R \to \infty$ 处计算 $I_{\text{GHY}}$。需要减去平直空间背景项 $I_0$（参考项）以正规化。

    $$
    I_{\text{total}} = -\frac{1}{8\pi G} \int_{\partial M} (K - K_0) \sqrt{h} \, d^3y
    $$

    计算结果为 $I_E = \beta M - \pi r_h^2 / G$（近似形式，取决于系综定义）。

    自由能 $F = I_E / \beta = M - TS$。

    由此解出 $S = \pi r_h^2 / G = A/4G$。

    $\square$

### 13.2.3 边缘模式（Edge Modes）：离散本体论解释

为什么边界项会包含熵？在 QCA 离散本体论中，这有清晰的微观解释。

**定义 13.2.4 (边缘模式 / Edge Modes)**

当我们把全宇宙（封闭系统）划分为"系统" $M$ 和"环境" $\bar{M}$ 时，我们切断了穿过边界 $\partial M$ 的量子纠缠键。

在规范场论和引力中，希尔伯特空间不能简单地分解为 $\mathcal{H}_M \otimes \mathcal{H}_{\bar{M}}$，因为规范约束（如 Gauss 定律）是非局域的。

为了恢复分解，必须在边界上引入**边缘模式**（Edge Modes），它们携带了边界上的规范荷（在引力中是微分同胚荷）。

**物理图景**：

1.  **体作用量** $I_{\text{EH}}$ 描述了系统内部**闭合**的动力学，这部分对应于纯态演化，熵为零（或幺正守恒）。

2.  **边界作用量** $I_{\text{GHY}}$ 实际上是边缘模式的**Berry 相位**或**辛势（Symplectic Potential）**。

3.  在欧几里得转动下，这个相位变成了实数（配分函数），其数值衡量了边缘模式的状态空间维数。

    $$
    Z_{\text{GHY}} = \text{Tr}_{\text{edge}} (e^{-\beta H_{\text{edge}}})
    $$

    因为 $I_{\text{GHY}} \propto \text{Area}$，这意味着边缘模式分布在边界上，且每普朗克面积携带固定比特数。这正是全息原理的微观实现。

### 13.2.4 布朗-约克（Brown-York）准局域张量

GHY 项的变分还定义了边界上的能量动量。

**定义 13.2.5 (布朗-约克应力张量)**

对于边界 $\partial M$，其诱导度规为 $h_{ab}$。通过对边界作用量变分，定义准局域能量动量张量：

$$
T^{ab}_{\text{BY}} \equiv \frac{2}{\sqrt{|h|}} \frac{\delta I_{\text{total}}}{\delta h_{ab}} = \frac{1}{8\pi G} (K^{ab} - K h^{ab})
$$

这一张量描述了时空区域 $M$ 包含的**准局域能量**（Quasi-local Energy）和动量。

例如，对于渐近平坦时空，对 $T^{ab}_{\text{BY}}$ 在无穷远球面上积分，即可得到 ADM 质量。

**结论**

GHY 边界项不是一个数学补丁，它是**引力全息性质的直接体现**。

* 在数学上，它保证了变分原理的完备性。

* 在热力学上，它提供了黑洞和视界的熵。

* 在微观上，它计数了被边界切断的边缘模式。

在下一节 13.3 中，我们将处理比光滑边界更复杂的情况——**非光滑边界（角点）**。我们将引入海沃德（Hayward）项，证明在离散 QCA 几何趋于连续时，角点贡献是不可忽略的拓扑修正。

