# 附录 C：核心定理证明集

**Appendix C: Proofs of Core Theorems**

本书正文中提出了许多具有颠覆性的物理命题，如"光程守恒"、"引力即熵力"以及"概率即计数"。虽然我们在正文中给出了物理图像和启发式推导，但作为一个严肃的理论体系，这些命题必须建立在严格的数学证明之上。

本附录汇集了支撑全书理论框架的三个最核心定理的完整数学证明。这些证明不依赖于模糊的类比，而是直接基于公理 $\Omega$（幺正 QCA）和标准的算子代数推导而来。

---

## C.1 光程守恒定理的算子代数证明

**命题**：在任意满足平移不变性和局域幺正性的离散 Dirac-QCA 模型中，单粒子激发态的外部群速度 $v_{ext}$ 与内部演化速度 $v_{int}$ 满足 $v_{ext}^2 + v_{int}^2 = c^2$。

**证明**：

1. **哈密顿量的正交分解**

   在连续极限下（$\Delta x, \Delta t \to 0$），一维 Dirac-QCA 的演化算符 $\hat{U}$ 可以生成一个有效的哈密顿量 $\hat{H}$。对于二分量旋量场 $\psi = (\psi_L, \psi_R)^T$，最通用的平移不变哈密顿量形式为：

   $$\hat{H} = c \hat{p} \sigma_z + m c^2 \sigma_x$$

   其中：

   * $c$ 是格点最大传播速度。

   * $\hat{p} = -i\hbar \partial_x$ 是动量算符。

   * $m$ 是由局域混合角 $\theta$ 决定的质量参数（见正文第五章）。

   * $\sigma_z, \sigma_x$ 是泡利矩阵，分别作用于内部手性空间。

2. **总演化速率的算符模长**

   量子态在希尔伯特空间中的总演化速率（Fubini-Study 速度）由哈密顿量的方差或模长决定。对于能量本征态 $|\psi_E\rangle$，其随时间演化的相位旋转速率的模方正比于 $E^2$：

   $$E^2 = \langle \psi_E | \hat{H}^2 | \psi_E \rangle$$

3. **利用反对易关系**

   计算算符 $\hat{H}^2$：

   $$
   \begin{aligned}
   \hat{H}^2 &= (c \hat{p} \sigma_z + m c^2 \sigma_x) (c \hat{p} \sigma_z + m c^2 \sigma_x) \\
   &= c^2 \hat{p}^2 \sigma_z^2 + m^2 c^4 \sigma_x^2 + c m c^2 \hat{p} (\sigma_z \sigma_x + \sigma_x \sigma_z)
   \end{aligned}
   $$

   利用泡利矩阵的代数性质：

   * $\sigma_z^2 = \mathbb{I}, \quad \sigma_x^2 = \mathbb{I}$

   * 反对易性：$\{ \sigma_z, \sigma_x \} = \sigma_z \sigma_x + \sigma_x \sigma_z = 0$

   交叉项消失，得到对角化的能量算符：

   $$\hat{H}^2 = (c^2 \hat{p}^2 + m^2 c^4) \mathbb{I}$$

4. **速度分量的映射**

   上式两边取期望值并除以 $E^2$（归一化）：

   $$1 = \frac{c^2 p^2}{E^2} + \frac{m^2 c^4}{E^2}$$

   * **外部速度项**：根据群速度定义 $v_g = \frac{\partial E}{\partial p}$。由色散关系 $E^2 = p^2 c^2 + m^2 c^4$ 微分可得 $2E dE = 2p c^2 dp$，故 $v_{ext} \equiv v_g = \frac{c^2 p}{E}$。

      因此，第一项 $\frac{c^2 p^2}{E^2} = \frac{v_{ext}^2}{c^2}$。

   * **内部速度项**：定义内部速度 $v_{int}$ 为静止能量（质量项）在总能量中的占比投影到光速上，即 $v_{int} = c \cdot \frac{m c^2}{E}$。

      因此，第二项 $\frac{m^2 c^4}{E^2} = \frac{v_{int}^2}{c^2}$。

5. **结论**

   代回原式：

   $$1 = \frac{v_{ext}^2}{c^2} + \frac{v_{int}^2}{c^2} \implies v_{ext}^2 + v_{int}^2 = c^2$$

   **证毕。**

---

## C.2 信息-引力变分原理 (IGVP) 的变分推导

**命题**：若时空几何是为了最大化全息纠缠熵而涌现的宏观结构，则度规场 $g_{\mu\nu}$ 必须满足爱因斯坦场方程 $G_{\mu\nu} = 8\pi G T_{\mu\nu}$。

**证明**：

1. **构造总熵泛函（Total Entropy Functional）**

   定义宇宙在一个局域因果菱形内的总熵 $S_{tot}$ 为几何熵 $S_{geom}$ 与物质熵 $S_{matter}$ 之和。根据热力学第二定律，平衡态对应于熵的极值点。

   泛函形式（作用量 $I = -S$）：

   $$I[g] = I_{geom}[g] + I_{matter}[g, \psi]$$

2. **几何熵项**

   根据 QCA 的离散结构，几何熵正比于网络连接的复杂度。在连续极限下，这是时空流形的曲率积分（Wald 熵的推广）：

   $$I_{geom} = \frac{1}{16\pi G} \int_{\mathcal{M}} d^4x \sqrt{-g} R$$

   其中 $G$ 是与普朗克面积元 $l_P^2$ 有关的常数。

3. **物质熵项**

   物质熵由物质场 $\psi$ 在弯曲背景下的配分函数 $Z[g]$ 决定，其对数对应于有效作用量：

   $$I_{matter} = \int_{\mathcal{M}} d^4x \sqrt{-g} \mathcal{L}_m$$

4. **对度规的变分**

   我们要寻找使得总作用量对于度规扰动 $\delta g^{\mu\nu}$ 为驻值的几何结构。

   $$\delta I = \delta I_{geom} + \delta I_{matter} = 0$$

   * **几何部分变分**：

     利用恒等式 $\delta \sqrt{-g} = -\frac{1}{2} \sqrt{-g} g_{\mu\nu} \delta g^{\mu\nu}$ 和帕拉蒂尼恒等式 $\delta R = R_{\mu\nu} \delta g^{\mu\nu} + \nabla_\mu v^\mu$（边界项忽略）：

     $$\delta I_{geom} = \frac{1}{16\pi G} \int d^4x \sqrt{-g} \left( R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} \right) \delta g^{\mu\nu}$$

   * **物质部分变分**：

     根据定义，应力-能量张量 $T_{\mu\nu}$ 是物质作用量对度规的响应：

     $$T_{\mu\nu} \equiv -\frac{2}{\sqrt{-g}} \frac{\delta I_{matter}}{\delta g^{\mu\nu}}$$

     因此：

     $$\delta I_{matter} = -\frac{1}{2} \int d^4x \sqrt{-g} T_{\mu\nu} \delta g^{\mu\nu}$$

5. **导出场方程**

   由 $\delta I = 0$，对任意 $\delta g^{\mu\nu}$ 成立，被积函数必须为零：

   $$\frac{1}{16\pi G} (R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu}) - \frac{1}{2} T_{\mu\nu} = 0$$

   整理得：

   $$R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} = 8\pi G T_{\mu\nu}$$

   **证毕。**

---

## C.3 波恩规则的迹类计数证明

**命题**：在离散、幺正且满足环境辅助不变性（Envariance）的 QCA 系统中，测量结果的概率 $P_k$ 唯一地由振幅模方 $|c_k|^2$ 决定。

**证明**：

1. **施密特分解**

   设系统 $S$ 与环境 $E$ 处于纠缠态：

   $$|\Psi\rangle = \sum_{k=1}^N c_k |s_k\rangle |e_k\rangle$$

   其中 $|s_k\rangle, |e_k\rangle$ 分别为正交基。

2. **有理数逼近与细粒化**

   假设 $|c_k|^2$ 为有理数（在离散系统中总是成立），令 $|c_k|^2 = n_k / M$，其中 $M = \sum n_k$ 是总微观状态数。

   我们可以将环境基底 $|e_k\rangle$ 进一步分解为 $n_k$ 个等权重的微观基底 $|e_{k, \alpha}\rangle$ 的叠加：

   $$|e_k\rangle \to \frac{1}{\sqrt{n_k}} \sum_{\alpha=1}^{n_k} |e_{k, \alpha}\rangle$$

   代入原态，并忽略总体相位：

   $$|\Psi'\rangle = \frac{1}{\sqrt{M}} \sum_{k=1}^N \sum_{\alpha=1}^{n_k} |s_k\rangle |e_{k, \alpha}\rangle$$

3. **环境交换对称性**

   现在，态 $|\Psi'\rangle$ 是 $M$ 个项的等权重叠加。每一项的形式为 $|s_k\rangle |e_{k, \alpha}\rangle$。

   对于环境微观态 $|e_{k, \alpha}\rangle$ 和 $|e_{j, \beta}\rangle$，存在幺正算符 $\hat{U}_E$ 可以交换它们而不改变 $|s_k\rangle$ 部分。

   根据 Envariance 原理，物理概率不应依赖于环境的标签。因此，每一个微观项 $|s_k\rangle |e_{k, \alpha}\rangle$ 出现的概率必须相等，均为 $p = 1/M$。

4. **宏观概率求和**

   观察者测得宏观状态 $|s_k\rangle$ 的概率 $P_k$，是所有与之兼容的微观项概率之和：

   $$P_k = \sum_{\alpha=1}^{n_k} p = n_k \cdot \frac{1}{M} = \frac{n_k}{M}$$

   回顾定义 $|c_k|^2 = n_k / M$，即得：

   $$P_k = |c_k|^2$$

   **证毕。**

---

**作者结语**：

这三个证明分别确立了本书在**运动学**（光程守恒）、**动力学**（场方程）和**测量论**（波恩规则）上的数学合法性。它们共同构成了一个逻辑闭环，证明了物理实在可以完全从"幺正计算"这一单一公理中涌现出来。

