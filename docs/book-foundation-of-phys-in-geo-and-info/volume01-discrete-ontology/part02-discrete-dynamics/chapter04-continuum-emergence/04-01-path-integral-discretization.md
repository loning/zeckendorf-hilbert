**第四章：从离散到连续的场论涌现**

在第一卷的前三章中，我们建立了一个完全离散的本体论框架：物理宇宙被建模为一个满足有限信息公理的量子元胞自动机（QCA）$\mathfrak{U} = (\Lambda, \mathcal{A}, U, \omega_0)$。在这个图景中，没有连续的时空流形，没有微分方程，只有离散格点上的代数演化。

然而，宏观物理学的巨大成功建立在连续场论（如量子电动力学和广义相对论）的基础之上。本章的核心任务是搭建一座坚实的数学桥梁，证明连续场论并非与离散本体论相悖，而是其在**长波极限（Long-wavelength Limit）**下的有效描述。我们将从最基本的费曼路径积分（Feynman Path Integral）开始，展示它如何自然地从 QCA 的幺正演化中涌现。

### 4.1 路径积分离散化：费曼核的格点求和表示与连续极限

在标准量子力学中，费曼路径积分提供了一种直观且强有力的量子化方法：粒子从一点运动到另一点的概率幅是所有可能路径的加权和。在连续时空中，这涉及到数学上微妙的测度定义问题。但在我们的离散 QCA 框架下，路径积分不再是一个需要正则化的形式定义，而是一个**严格的组合学恒等式**。

#### 4.1.1 离散传播子（Discrete Propagator）的定义

考虑 QCA 宇宙中的一步更新算符 $U$。对于任意两个格点 $x, y \in \Lambda$，我们定义从 $x$ 到 $y$ 经历 $t$ 步演化的**离散传播子**（或格点核）$K(y, t; x, 0)$ 为：

$$
K(y, t; x, 0) = \langle y | U^t | x \rangle
$$

这里 $|x\rangle$ 和 $|y\rangle$ 是局域希尔伯特空间 $\mathcal{H}_\Lambda$ 的基矢（为简化记号，暂时假设每个元胞为单态或考虑标量分量，推广到旋量仅需引入内部索引）。

根据矩阵乘法的定义，$U^t$ 可以写成 $t$ 个 $U$ 的乘积。插入 $t-1$ 组完备性关系 $\sum_{z \in \Lambda} |z\rangle\langle z| = \mathbb{1}$，我们得到：

$$
K(y, t; x, 0) = \sum_{x_1, x_2, \dots, x_{t-1} \in \Lambda} \langle y | U | x_{t-1} \rangle \langle x_{t-1} | U | x_{t-2} \rangle \cdots \langle x_1 | U | x \rangle
$$

这一公式是路径积分的**原初形态**。

#### 4.1.2 图上的历史求和：费曼棋盘（Feynman Checkerboard）

上式中的每一个序列 $\gamma = (x_0, x_1, \dots, x_t)$（其中 $x_0=x, x_t=y$）代表了粒子在离散时空网格 $\Lambda \times \mathbb{Z}$ 上的一条**世界线**（Worldline）或**历史**（History）。

**定义 4.1.1 (离散作用量 / Discrete Action)**

对于路径 $\gamma$，其对应的概率幅是各步转移矩阵元的乘积。我们可以将其写为指数形式：

$$
A[\gamma] = \prod_{k=0}^{t-1} \langle x_{k+1} | U | x_k \rangle \equiv \exp\left( i S_{\text{disc}}[\gamma] \right)
$$

其中 $S_{\text{disc}}[\gamma]$ 定义为**离散作用量**。若 $U$ 的矩阵元为复数 $u_{ba} = |u_{ba}|e^{i\phi_{ba}}$，则离散作用量包含两部分：

$$
S_{\text{disc}}[\gamma] = \sum_{k=0}^{t-1} \phi_{x_{k+1}, x_k} - i \sum_{k=0}^{t-1} \ln |u_{x_{k+1}, x_k}|
$$

如果 $U$ 是置换矩阵或阿达玛（Hadamard）类型的门，模长部分通常为常数，作用量主要由相位累积决定。

**定理 4.1.2 (格点路径求和公式)**

离散传播子严格等于所有连接 $(x, 0)$ 与 $(y, t)$ 的允许路径的加权和：

$$
K(y, t; x, 0) = \sum_{\gamma: x \to y} e^{i S_{\text{disc}}[\gamma]}
$$

由于 QCA 的有限传播半径 $R$（见 3.2 节），只有满足 $|x_{k+1} - x_k| \le R$ 的路径其振幅才非零。这意味着求和仅在**几何光锥**内的路径上进行，不存在发散问题。这被称为**费曼棋盘**模型的推广。

#### 4.1.3 连续极限与平滑化

现在我们考察宏观极限。引入离散化参数：格距 $\varepsilon$（对应物理长度 $a$）和时间步长 $\tau$（对应物理时间 $\Delta t$）。宏观坐标 $X = x\varepsilon, T = t\tau$。

我们要求在 $\varepsilon, \tau \to 0$ 的极限下，离散传播子 $K$ 能够收敛到连续量子力学的核 $K_{\text{cont}}(Y, T; X, 0)$。这需要对更新算符 $U$ 的参数进行精细调节。

考虑一维狄拉克型 QCA（如 3.3 节所述），其更新算符在动量空间为：

$$
U(k) = e^{-ik\sigma_z \varepsilon} e^{-i m \tau \sigma_x}
$$

（此处采用自然单位制，参数映射见定理 3.4）。

对于一条路径 $\gamma$，其在格点上的"大折线"运动对应于粒子的锯齿形轨迹。当 $\varepsilon \to 0$ 时，大量的微观"Zitterbewegung"（颤动）路径在统计上平均化。

**引理 4.1.3 (相位平稳性与经典路径)**

在路径求和 $\sum e^{i S_{\text{disc}}}$ 中，当作用量 $S_{\text{disc}}$ 远大于 $\hbar$（在我们的无量纲单位中即 $S \gg 1$）时，主要的贡献来自于那些使 $S_{\text{disc}}$ 对路径变分一阶导数为零的路径。这些路径对应于离散版本的欧拉-拉格朗日方程解，即**经典轨迹**。

在连续极限下，离散作用量 $S_{\text{disc}}[\gamma]$ 收敛为连续泛函：

$$
S_{\text{disc}}[\gamma] \xrightarrow{\varepsilon \to 0} \int_0^T \mathcal{L}(X, \dot{X}) \, dt
$$

其中拉格朗日量 $\mathcal{L}$ 由 $U$ 的微观参数决定。

#### 4.1.4 从求和到泛函积分

通过上述极限过程，离散的求和符号 $\sum_{\gamma}$ 形式上转化为连续的泛函积分符号 $\int \mathcal{D}X$。

**定理 4.1.4 (费曼核的涌现)**

设 QCA 满足狄拉克连续极限条件（定理 3.4）。对于宏观观测者，格点传播子 $K(y, t; x, 0)$ 在重整化后弱收敛于连续费曼核：

$$
\lim_{\varepsilon \to 0} Z(\varepsilon)^{-1} K(\lfloor X/\varepsilon \rfloor, \lfloor T/\tau \rfloor; \lfloor X_0/\varepsilon \rfloor, 0) = \int_{X(0)=X_0}^{X(T)=X} \mathcal{D}X(t) \exp\left( \frac{i}{\hbar} \int_0^T \mathcal{L}_{\text{Dirac}} \, dt \right)
$$

其中 $Z(\varepsilon)$ 是波函数重整化常数，$\mathcal{L}_{\text{Dirac}} = \bar{\psi}(i\gamma^\mu \partial_\mu - m)\psi$ 是狄拉克场的拉格朗日密度（在单粒子扇区对应于粒子的相对论性作用量）。

**物理诠释**：

这一结果表明，**路径积分并非量子力学的基本公理，而是离散幺正演化的组合学性质在连续极限下的统计涌现**。

1.  **正则化是不必要的**：在我们的理论中，$\varepsilon$ 是物理的普朗克尺度截断，而不是一个需要取为零的数学辅助量。路径积分在本体论上始终是有限求和。

2.  **虚时间的本质**：通常场论中的威克转动（Wick Rotation）$t \to -i\tau$ 将路径积分转化为统计配分函数。在 QCA 中，这对应于研究算符 $U$ 的谱性质与转移矩阵（Transfer Matrix）的最大本征值问题。

通过这一节，我们完成了从"跳跃的算符"到"流动的场"的关键一跃。在这个框架下，费曼图（Feynman Diagrams）不再仅仅是微扰论的计算工具，而是对底层离散时空网络中粒子实际传播历史的拓扑描述。接下来，我们将具体推导旋量场（狄拉克方程）是如何从这种离散行走中诞生的。

