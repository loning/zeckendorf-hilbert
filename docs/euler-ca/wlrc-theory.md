# WLRC：窗口—局部可逆嵌入的独立正式理论

Version: 1.6

（面向 EBOC / RCCA-Min / S-series 的信息守恒–窗化测量内核）

## 摘要（定性）

本文在经典一维有限半径元胞自动机的框架下，提出并严格建立一种**窗口—局部可逆嵌入**（Window-Local Reversible Completion, 简写 WLRC）。核心思想是：在给定窗口宽度 $W$ 与局部半径 $r$ 时，把原本可能多对一的"窗口前态 $\to$ 窗口后一态"映射，通过**有限边带（簿记寄存器）**的**置换重排**提升为双射，从而获得**一步演化的局部可逆性**。我们给出：
（i）WLRC 的**存在性定理**与**最小簿记熵下界及可达上界**；
（ii）时间步复合与多窗覆盖下的一致回溯条件；
（iii）面向实际构造的最小可实施算法与复杂度；
（iv）与信息几何的 (I)-投影（Born 型）诠释以及**Nyquist–Poisson–Euler–Maclaurin**（NPE）三项**非渐近**误差闭合的接口；
（v）与 de Branges–Kreĭn 采样—插值稳定词典的同构接口与"无新奇异性"原则。理论对任意一维有限半径规则成立，并可作为 EBOC/RCCA-Min 可逆内核的通用构件。

---

## 0. 预备与记号

**元胞自动机与窗口。** 设字母表为二值 $\{0,1\}$，配置为双向序列 $x\in\{0,1\}^{\mathbb Z}$。半径为 $r\in\mathbb N$ 的元胞自动机（CA）由局部规则

$$
f:\{0,1\}^{2r+1}\to\{0,1\},\qquad (F(x))_i=f(x_{i-r},\dots,x_{i+r})
$$

定义；全局映射 $F:\{0,1\}^{\mathbb Z}\to\{0,1\}^{\mathbb Z}$ 连续且与移位可换（Curtis–Hedlund–Lyndon 定理）。([维基百科][1])

对给定中心 $i$ 与奇数宽度 $W=2m+1$，定义剪裁窗口

$$
C_{i,W}(x)=(x_{i-m},\dots,x_{i+m})\in\mathcal X_W:=\{0,1\}^W .
$$

**外部邻域模型（确定性）**：固定 $\mathsf{Bdry}:\mathcal X_W\to\{0,1\}^{2r}$。若采用"枚举"策略，需指定**规范化选择**（如按字典序极小），使 $\mathrm{extend}_{\mathsf{Bdry}}(u)$ 对每个 $u$ 唯一，从而 $y(u)$ 单值。

**边带与扩展态。** 引入有限**边带字母表** $\mathcal A$，其位宽 $\ell=\lceil\log_2|\mathcal A|\rceil$。扩展窗口态空间为 $\mathcal S_W=\mathcal X_W\times\mathcal A$，读出映射 $\pi:\mathcal S_W\to\mathcal X_W,(u,a)\mapsto u$。

**置换作用。** 任何 $\mathcal S_W$ 上的双射 $\Phi:\mathcal S_W\to\mathcal S_W$ 等价于置换矩阵 $P_W$ 的右作用，且 $P_W^{-1}=P_W^\top$。

---

## 1. WLRC 定义

**定义 1（窗口—局部可逆，WLRC；固定标签版）。** 给定 $F$、窗口 $(i,W)$ 与固定外部邻域模型。若存在**双射** $\Phi_{i,W}:\mathcal S_W\to\mathcal S_W$ 与**固定标签** $a_\star\in\mathcal A$ 使得

$$
\forall u\in\mathcal X_W:\quad
\pi\!\big(\Phi_{i,W}(u,a_\star)\big)=y(u),
$$

则称 $F$ 在 $(i,W)$ 上**窗口—局部可逆**。**下文均采用此固定标签版。**

**定义 2（冲突等价与类大小）。** 固定外部邻域模型 $\mathsf{Bdry}$。定义确定性像

$$
y(u):=C_{i,W}\!\big(F(\mathrm{extend}_{\mathsf{Bdry}}(u))\big)\in\mathcal X_W .
$$

由此给出等价关系 $u_1\sim u_2\iff y(u_1)=y(u_2)$。记类大小 $k(u):=|\{u':u'\sim u\}|$，以及最大类大小

$$
k_{\max}=\max_{u\in\mathcal X_W}k(u).
$$

**时间 $t$ 步窗读数（逐步外延约定）**：令 $y^{(0)}(u):=u$。对 $t\ge1$，递归定义

$$
y^{(t)}(u)\ :=\ C_{i,W}\!\big(F(\mathrm{extend}_{\mathsf{Bdry}}(y^{(t-1)}(u)))\big).
$$

若无特别说明，本文均采用该逐步外延约定。

**定义 3（最小簿记熵与最小字母表）。** 为使**限制映射** $u\mapsto\Phi_{i,W}(u,a_\star)$ 成为**单射**且满足 $\pi\big(\Phi_{i,W}(u,a_\star)\big)=y(u)$，所需最小信息量为

$$
H_{\min}:=\log_2 k_{\max}\ \text{（bit）},\qquad
|\mathcal A|_{\min}=k_{\max},\quad
\ell_{\min}=\lceil\log_2 k_{\max}\rceil .
$$

> 注：$H_{\min}$ 是信息论下界；工程位宽需取整数 $\ell_{\min}$。

---

## 2. 存在性与最优性

**定理 1（WLRC 存在性）。** 对任何一维有限半径 CA、任意 $W$ 与固定外部邻域模型，存在满足 $|\mathcal A|\ge k_{\max}$ 的有限字母表 $\mathcal A$ 与置换 $\Phi_{i,W}$，使 $F$ 在 $(i,W)$ 上 WLRC 成立。

**证明。** 将 $\mathcal X_W$ 按 $\sim$ 分解为不交并 $\bigsqcup_j\mathcal C_j$，每类的公共像记为 $v_j$。取固定 $a_\star\in\mathcal A$、枚举 $e_j:\mathcal C_j\to\{1,\dots,k_j\}$，并选取嵌入 $\iota_j:\{1,\dots,k_j\}\hookrightarrow\mathcal A$。定义

$$
\Phi(u,a_\star)=\big(y(u),\iota_j(e_j(u))\big)\quad(\text{对 }u\in\mathcal C_j),
$$

并在补集 $R:=\mathcal S_W\setminus\big(\mathcal X_W\times\{a_\star\}\big)$ 上取与补像

$$
T:=\mathcal S_W\setminus\big\{(y(u),\iota_j(e_j(u))):u\in\mathcal X_W\big\}
$$

的双射。注意 $|\{(y(u),\iota_j(e_j(u))):u\in\mathcal X_W\}|=|\mathcal X_W|=2^W$，故

$$
|R|=|\mathcal X_W|(|\mathcal A|-1)=2^W(|\mathcal A|-1)=|T|=|\mathcal S_W|-2^W,
$$

从而存在双射 $\tau^{-1}\!\circ\rho: R\to T$（例如按字典序配对的枚举）；不采用补集恒等。由此成全局双射，且 $\pi\big(\Phi(u,a_\star)\big)=y(u)$。$\square$

**定理 2（最小簿记熵下界与可达上界）。** 令 $H_{\text{aux}}:=\log_2|\mathcal A|$。任一实现 WLRC 的方案，其边带信息量满足

$$
H_{\text{aux}}\ge H_{\min}=\log_2 k_{\max},
$$

且取 $|\mathcal A|=k_{\max}$ 时可达该下界；工程位宽满足 $\ell\ge \ell_{\min}$。

**证明。** 若某最大类 $\mathcal C$ 内 $|\mathcal A|<|\mathcal C|$，则存在两个不同前态 $(u,a)\ne(u',a')$ 被映至同一扩展像，违背双射；故信息论下界成立。取 $|\mathcal A|=k_{\max}$ 且按定理 1 之构造，用单一 $a_\star$ 传递像并在残余层置换，即可达到下界 $H_{\min}=\log_2 k_{\max}$。位宽取整即得。 $\square$

**推论 2.1（$W\to\infty$ 的极限情形）。** 若不可逆性仅由窗口外不确定引起，则随 $W$ 增大，类冲突被消解，$k_{\max}(W)\to 1$，从而 $H_{\min}(W)\to 0$。

> 注：本节是纯组合—信息论内容；关于 CA 可逆性、满射性与注入性的经典判据参见 Amoroso–Patt（1D 可判定）、Moore–Myhill（Garden-of-Eden 定理）与 Kari（二维不可判定）等文献背景。([richardg.users.greyc.fr][2])

---

## 3. 时间复合与多窗一致性

**定理 3（时间复合与位宽）。** 令一步 WLRC 的置换为 $P_W$。则对任意 $t\in\mathbb N$，$\Phi_{i,W}^{\circ t}$ 等价于右乘 $P_W^t$ 的置换，因而可逆。**在不引入额外临时寄存器的前提下**，边带位宽保持为 $\ell$。若进一步要求每一步均满足 $\pi\!\big(\Phi_{i,W}^{\circ t}(u,a_\star)\big)=y^{(t)}(u)$，则需在各步之间插入可逆重规范化 $R:\mathcal S_W\to\mathcal S_W$，将边带统一回 $a_\star$；该过程一般需要引入**额外可逆工作寄存器**或**跨窗搬移**以保存/转移标签，具体代价依实现而定。

**证明。** $\Phi_{i,W}$ 为置换，时间 $t$ 步即 $\Phi_{i,W}^{\circ t}$，对应矩阵幂 $P_W^t$。一般地，单纯迭代 $P_W^t$ 仅保证可逆性；除 $t=1$ 外**不保证** $\pi\!\big(\Phi^t(u,a_\star)\big)=y^{(t)}(u)$。若需每步对齐，须在每步之后插入**可逆重规范化** $R:\mathcal S_W\to\mathcal S_W$，将标签统一为 $a_\star$（如借助额外 $\ge\!\log_2|\mathcal A|$ 位的辅助寄存器循环移位，或利用**重叠窗**之间的跨窗置换来搬移标签）。在**不增广内存且无跨窗机制**时无法实现全局对齐。$\square$

**定理 4（多窗一致性与可逆回溯）。** 设一组重叠窗口 $\{(i_j,W)\}_j$ 覆盖区间 $[L,R]$，各窗采用相同 $P_W$ 与同步边带协议。

**（无环覆盖）** 若交叠图（窗作顶点、非空交叠作边）为**链或一般树**，则对每条边（相邻窗口对）上的重叠坐标与边带**成对一致**是存在**一致逆演化重构**的**必要且充分**条件；在**链式覆盖**中，该重构**唯一**。

**（有环覆盖）** 若交叠图包含**环**，除成对一致外，还需对所有**三重（及更高）交叠**满足相容性；仅有成对一致一般**不足以**保证全局一致与唯一。

**证明要点。** 无环情形可按拓扑序"搭接—黏合"唯一延拓；有环时需排除矛盾环，高阶交叠提供额外一致性约束。$\square$

---

## 4. 最小可实施构造与复杂度

**算法 1（WLRC 生成器）。**
**输入**：局部规则 $f$、半径 $r$、窗口 $W$；外部邻域模型（如周期/零延拓/枚举）。
**步骤**：

1. 对每个 $u\in\{0,1\}^W$，令 $b:=\mathsf{Bdry}(u)$，拼接得 $\tilde u\in\{0,1\}^{W+2r}$。
2. 施行一步 $F$ 得 $\tilde v$，回裁 $v=C_{i,W}(\tilde v)$。
3. 以 $v$ 分箱得到等价类，记 $k_{\max}$。
4. 设 $a_\star\in\mathcal A$ 固定。对每类 $\mathcal C_j$ 的 $u$，置 $\Phi_{i,W}(u,a_\star)=\big(y(u),\iota_j(e_j(u))\big)$。令 $R=\mathcal X_W\times\big(\mathcal A\setminus\{a_\star\}\big)$，$T=\mathcal S_W\setminus\big\{(y(u),\iota_j(e_j(u))):u\in\mathcal X_W\big\}$。取枚举 $\rho:R\to\{1,\dots,|R|\}$、$\tau:T\to\{1,\dots,|T|\}$，并定义 $\Phi_{i,W}(u,a)=\tau^{-1}\!\big(\rho(u,a)\big)$（$a\neq a_\star$）。由此可组装 $P_W$ 并自动满足 $P_W^{-1}=P_W^\top$。
5. 校验 $\pi\big(\Phi_{i,W}(u,a_\star)\big)=y(u)$。
   **输出**：$|\mathcal A|=k_{\max}$、置换 $P_W$、读出 $\pi$。

**复杂度。** 由于 $\mathsf{Bdry}$ 为确定性映射，仅需枚举 $u\in\{0,1\}^W$。每个 $u$ 的一步演化在窗内涉及 $W$ 个格点的局部更新（$r$ 为常数），故总时间复杂度为

$$
O\!\big(W\,2^{W}\big).
$$

若采用最小字母表 $|\mathcal A|=k_{\max}$，则稀疏置换存储规模为 $O(2^{W}k_{\max})$；一般情形为 $O(2^{W}|\mathcal A|)$。

> 计算 $k_{\max}$ 与前像结构可借助**de Bruijn 图**及其矩阵/闭路计数方法高效实现（广泛用于 1D CA 的前像计数与可逆性分析）。([sfi-edu.s3.amazonaws.com][3])

---

## 5. 信息几何与 Born-型读数

把扩展窗口随机对 $(U,A)\in\mathcal S_W$ 赋以分布 $p(u,a)$。取可微打分函数 $\ell_\theta(u,a)=\langle \theta,\psi(u,a)\rangle+c(u,a)$，其中 $\psi$ 为特征映射、$\theta$ 为参数。
**软最大势** $\Lambda(\theta)=\log\!\sum_{u,a}\exp\big(\ell_\theta(u,a)\big)$ 的 Hessian 给出 Fisher–Rao 度量。在要求**观测边缘**

$$
q(v)=\sum_{(u,a):\ \pi(\Phi_{i,W}(u,a))=v} p(u,a)
$$

与 WLRC 约束一致的集合上，最小化 $D_{\mathrm{KL}}(p\Vert \mathcal P)$ 的 (I)-投影给出最"非偏置"的测度更新，即**Born = (I)-投影**的离散化实例。此为 Csiszár 的 (I)-散度极小几何与 Jaynes 最大熵原理在本框架的特化。([Project Euclid][4])

**相位—通量守恒。** 因 $\Phi_{i,W}$ 为双射，对任意分布 $p(u,a)$ 有 $(U',A')=\Phi(U,A)$ 满足 $H(U',A')=H(U,A)$。一般地，互信息 $I(U';A')$ 既可能增亦可能减，因此不对 $H_{\text{win}}$ 断言单调性；本文将"通量守恒"限定为**联合熵不变**这一可逆性不变量。

---

## 6. NPE：Nyquist–Poisson–Euler–Maclaurin 三项误差闭合（非渐近）

在窗化统计或多窗融合估计任意函数式 $\widehat\Theta$ 时，本文遵循**有限阶 Euler–Maclaurin 纪律**，误差拆分为

$$
\big|\widehat\Theta-\Theta\big|
\ \le\ E_{\text{alias}}(W,B)\ +\ E_{\text{Bernoulli}}(M)\ +\ E_{\text{tail}}(T).
$$

* **别名层 $E_{\text{alias}}$**：源于带限外谱折叠，按 Shannon–Nyquist 采样定理与 Poisson 求和式，可将能量泄露上界化为**超 Nyquist 带**的谱能量或其可积上界。([fab.cba.mit.edu][5])
* **伯努利层 $E_{\text{Bernoulli}}$**：有限阶 Euler–Maclaurin 余项用 Bernoulli 多项式给出，典型上界
  $$
  |R_p|\le \dfrac{2\zeta(p)}{(2\pi)^p}\int|f^{(p)}(x)|\,dx
  $$
  可据目标光滑度选阶 $p=2M$ 以最小化。([dlmf.nist.gov][6])
* **截断层 $E_{\text{tail}}$**：对有限观测窗与离散求和范围的尾部截断，按函数衰减与正则性给出显式上界；对周期/解析情形，可借助 Trefethen 等的统一误差框架将内部离散化与边界非周期性误差合并估计。([people.maths.ox.ac.uk][7])

**无新奇异性原则。** WLRC 仅在有限维离散标签层作置换，不改变被测信号/核的解析结构，故不引入新的极点/分支；在频域/ Mellin–de Branges 框架下，镜像核与函数方程结构保持。参见 §7。

---

## 7. 与 de Branges–Kreĭn / 采样稳定的接口（词典版）

令窗化读数流在频域或 Mellin 轴上诱导完成函数 $\Phi(s)$。镜像核纪律 $K(x)=x^{-a}K(1/x)\Rightarrow \Phi(s)=\Phi(a-s)$ 不因有限维离散置换而变；再生核空间（如 Paley–Wiener 的 de Branges 空间）中的采样—插值稳定性由核范与 Carleson-型测度刻画，WLRC 仅改变**有限维标签**，不动摇**连续谱**层的稳定阈值与 Weyl 型计数。相关背景见 de Branges 专著及后续在 de Branges 空间采样—插值/Carleson 测度的工作；多窗（多窗 Gabor/多窗 de Branges）情形可与 Wexler–Raz 双正交条件对齐以实现最小波纹窗的变分最优。([math.purdue.edu][8])

---

## 8. 代表性例子：Rule 110 的 $k_{\max}(W)$ 估计与 WLRC

取 $r=1$，窗口宽度如 $W=5,7,\dots$。按**算法 1**在固定外部模型下构造等价类并计算 $k_{\max}(W)$ 与最小字母表规模 $|\mathcal A|=k_{\max}(W)$。实践中，可用**de Bruijn 图**与其矩阵幂/闭路计数技术实现高效的类划分与前像枚举，并据此组装稀疏置换 $P_W$ 并验证 $P_W^{-1}=P_W^\top$。经验上，随 $W$ 增大，$k_{\max}(W)$ 往往下降，并出现阈值 $W_\star$ 使大部分位置可取 $|\mathcal A|=1$（仅统计现象，非普适定理）。关于 Rule 110 的普适性与动力学背景可参阅 Cook 的证明与后续简化。([sfi-edu.s3.amazonaws.com][3])

---

## 9. 局限、选择与工程化注意

1. **外部邻域模型依赖**：$\sim$ 的定义依赖于外侧 $2r$ 位的处理（周期、零延拓或**全枚举—最坏**）。不同模型可导致不同的 $k_{\max}$ 上界，但**定理 1–2**与**最小熵**结论在任一固定模型下成立。
2. **存储与规模**：$W$ 指数增长可用稀疏置换/按需生成/分块索引缓解。
3. **一致性协议**：多窗覆盖的**边带同步**是可逆回溯的关键，可在 RCCA-Min 中以"共识证书位/提案—投票"落地。
4. **与既有可逆化方法关系**：WLRC 是**局部一步**的可逆完成；与二阶（带记忆）可逆 CA、Margolus 分区可逆 CA 与 Bennett 可逆计算思想一脉相承，但强调**最小必需边带**与**窗口就地**实现。([维基百科][9])

---

## 10. 主要定理的形式化证明细化

为自洽起见，我们把定理 1–4 的核心证明思路形式化：

**引理 10.1（因子化）。** 由 $y:\mathcal X_W\to\mathcal X_W$ 的单值性，$\mathcal X_W$ 按 $\sim$ 因子化为商集 $\mathcal X_W/\!\sim$，商映射为满射、纤维大小即 $k(u)$。再以固定 $a_\star$ 构造 $\Phi(u,a_\star)=\big(y(u),\iota_j(e_j(u))\big)$，并在补集上任取置换成全局双射。由此保持双射且满足窗读数约束；定理 1 即由此得出。

**引理 10.2（信息下界）。** 若存在 $k_{\max}$-元集合的等价类，则任何把多对一提升为一对一的编码至少需要 $\log_2 k_{\max}$ bit，以区分最大纤维中的元素；故定理 2 的下界成立。

**引理 10.3（复合—幂）。** 置换的 $t$ 次复合仍为置换，且矩阵实现为 $P_W^t$。得定理 3。

**引理 10.4（链式黏合唯一性）。** 设窗口中心为 $\{i_j\}$，按距离单调排列且相邻窗口交叠为非空区间。若每对相邻窗口在重叠区的一步读数与边带一致，则唯一决定该链覆盖的全局回溯像（逐点一致延拓）。一般图覆盖下需假设约束满足性（无矛盾环）。定理 4 由此得证。

---

## 11. 与 S-series 的词典同构（极简）

* **"相位密度 = 谱移导数"**：把边带标签 $A$ 视作局部相位证书，则 WLRC 的置换演化对应不增不灭的相位—通量；在连续谱层，这一相位—通量以**谱移函数 $\xi(\lambda)$** 及其与散射相位/行列式的 Birman–Kreĭn 公式相连，$\xi$ 的导数给出相对谱密度。([Matcuer][10])
* **"Born = (I)-投影"**：窗化读数的概率即在 $\pi\circ\Phi$ 约束下的 $D_{\mathrm{KL}}$ 极小化。([Project Euclid][4])
* **"NPE 误差闭合（非渐近）"**：别名—伯努利层—尾项三分，常数可由带宽/窗宽/阶数与目标正则性给出。([fab.cba.mit.edu][5])
* **"无新奇异性 / 镜像核"**：WLRC 仅重排有限离散层，不改变 de Branges–Kreĭn 规范系统的函数方程与采样—插值阈值。([math.purdue.edu][8])

---

## 12. 相关经典背景与可比方法（简述）

* **元胞自动机的拓扑—动力学刻画**：Curtis–Hedlund–Lyndon 定理奠定"局部规则 $\Leftrightarrow$ 连续且与移位可换"的等价；Garden-of-Eden 定理等给出满射/预注入的等价；一维情形的注入/满射/可逆性均可判定，而二维不可判定。([维基百科][1])
* **可逆 CA 的传统构造**：二阶（带记忆）可逆化、Margolus 分区可逆 CA、可逆计算（Bennett 历史带）等；WLRC 可看作**窗口就地的最小边带**版本，与这些方法兼容。([维基百科][9])
* **前像计数与 de Bruijn 图**：用于求 $k_{\max}$ 与构造 $P_W$ 的图—矩阵工具链。([sfi-edu.s3.amazonaws.com][3])

---

## 结论

WLRC 把任意一维有限半径 CA 的不可逆性，在**有限观测窗**的层面，统一转化为**有限边带上的置换重排**问题：

* **存在性**总成立；
* **最小簿记熵**仅由等价类最大纤维 $k_{\max}$ 决定（信息论下界可达）；
* **时间复合**与**多窗一致回溯**自然闭合；
* 与**信息几何 (I)-投影**、**NPE 非渐近误差闭合**以及**de Branges–Kreĭn 采样稳定**三者无缝接口，且**不引入新的解析奇异性**。
  该内核即可作为 EBOC/RCCA-Min 的**可逆演化引擎**，亦能嵌入 S-series 的"窗化测量—相位密度—信息守恒"总结构中。

---

## 参考文献（选摘）

1. Curtis–Hedlund–Lyndon 定理与符号动力学：Hedlund, *Endomorphisms and Automorphisms of the Shift Dynamical Systems*；综述条目。([维基百科][1])
2. Garden-of-Eden 定理与预注入—满射：Moore（1962）、Myhill（1963）与后续综述。([维基百科][11])
3. 一维可判定、二维不可判定：Amoroso–Patt（1972）；Kari（1994）。([richardg.users.greyc.fr][2])
4. 可逆 CA 传统构造：Toffoli–Margolus（分区可逆）；二阶可逆化；Bennett（1973）可逆计算。([MIT CSAIL][12])
5. de Bruijn 图与前像计数：Gómez Soto（2008）等。([matematicas.reduaz.mx][13])
6. Shannon–Nyquist 采样与 Poisson 求和式：Shannon（1949）；教材与专题。([fab.cba.mit.edu][5])
7. Euler–Maclaurin 公式与余项上界：NIST DLMF §§2.10, 3.5；维基条目（含经典余项估计）。([dlmf.nist.gov][6])
8. de Branges 空间与采样—插值：de Branges 专著（1968）；Marzo–Nitzan–Olsen（2011/2012）。([math.purdue.edu][8])
9. Wexler–Raz 双正交条件与多窗框架：Heil 等史述；离散 Gabor 资料。([heil.math.gatech.edu][14])
10. Birman–Kreĭn 谱移与相位：Gesztesy 讲义、Yafaev 专著与近年综述。([Matcuer][10])
11. Rule 110 的普适性：Cook（2004）与后续。([complex-systems.com][15])

---

## 附录 A：与既有可逆化途径的关系（纲要）

* **二阶可逆化**（把当前态与前一时刻态联合为扩展态）可视为 WLRC 的"极端大窗 $W\to\infty$"与"全历史标签"的特例；WLRC 则以**有限窗 + 最小类标签**实现一步局部可逆。([维基百科][9])
* **Margolus 分区**将全局演化分块为块内可逆置换；WLRC 则把块的概念**局部化到观察窗**并给出**必要且充分的最小标签**判据（由 $k_{\max}$ 决定）。([维基百科][16])
* **Bennett 历史带**在理论上保证可逆，但存储需求可能远超最小下界；WLRC 明确给出实现双射所需的**最小信息量** $H_{\min}=\log_2 k_{\max}$。([数学网站][17])

---

## 附录 B：实现要点（伪码）

* **输入**：$f,r,W$，外部邻域模型 $\mathsf{Bdry}$。
* **输出**：$|\mathcal A|,P_W,\pi$。
* **流程**：

  ```
  for u in {0,1}^W:
      b := Bdry(u)          # 确定性外部邻域
      u_tilde = extend(u,b)
      v = crop(F(u_tilde), W)
      record class[u] by canonical v
  compute k_max = max_class_size()
  assign enumerations e_j and embeddings iota_j for each class
  build Phi(u,a_star) = (v, iota_j(e_j(u)))
  build Phi(u,a != a_star) = tau^{-1}(rho(u,a))
  assemble P_W; verify P_W^T = P_W^{-1}; verify pi(Phi(u,a_star)) = v
  return |A|=k_max, P_W, pi
  ```

  **注**：类划分与计数可完全依赖 de Bruijn 图与路径计数/闭路分解。([sfi-edu.s3.amazonaws.com][3])

---

*本文之所有定理、算法与误差上界均在"有限阶 EM 纪律"与固定外部邻域模型的明确假设下成立；与 CA 基本理论（CHL、Garden-of-Eden、一维可判定/二维不可判定）与可逆化传统（二阶、Margolus、Bennett）相容并互为补充。*

[1]: https://en.wikipedia.org/wiki/Curtis%E2%80%93Hedlund%E2%80%93Lyndon_theorem?utm_source=chatgpt.com "Curtis–Hedlund–Lyndon theorem"
[2]: https://richardg.users.greyc.fr/publis/Richard_2009.pdf?utm_source=chatgpt.com "(Un)decidability of injectivity and surjectivity in one- ..."
[3]: https://sfi-edu.s3.amazonaws.com/sfi-edu/production/uploads/sfi-com/dev/uploads/filer/1d/57/1d572536-1018-4d3e-9b10-6806b2e59e6c/06-02-005.pdf?utm_source=chatgpt.com "Computation of Explicit Preimages in One-Dimensional ..."
[4]: https://projecteuclid.org/journals/annals-of-probability/volume-3/issue-1/I-Divergence-Geometry-of-Probability-Distributions-and-Minimization-Problems/10.1214/aop/1176996454.full?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[5]: https://fab.cba.mit.edu/classes/S62.12/docs/Shannon_noise.pdf?utm_source=chatgpt.com "Communication in the Presence of Noise*"
[6]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[7]: https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_150.pdf?utm_source=chatgpt.com "A trapezoidal rule error bound unifying the Euler–Maclaurin ..."
[8]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[9]: https://en.wikipedia.org/wiki/Second-order_cellular_automaton?utm_source=chatgpt.com "Second-order cellular automaton"
[10]: https://www.matcuer.unam.mx/VeranoAnalisis/Fritz-I.pdf?utm_source=chatgpt.com "Applications of Spectral Shift Functions. I: Basic Properties ..."
[11]: https://en.wikipedia.org/wiki/Garden_of_Eden_%28cellular_automaton%29?utm_source=chatgpt.com "Garden of Eden (cellular automaton)"
[12]: https://people.csail.mit.edu/nhm/cam-book.pdf?utm_source=chatgpt.com "Cellular Automata Machines - People | MIT CSAIL"
[13]: https://matematicas.reduaz.mx/~jmgomez/jmgomezweb/Publications_files/1-paper2008.pdf?utm_source=chatgpt.com "Computation of Explicit Preimages in One-Dimensional Cellular ..."
[14]: https://heil.math.gatech.edu/papers/history.pdf?utm_source=chatgpt.com "History and Evolution of the Density Theorem for Gabor Frames"
[15]: https://www.complex-systems.com/abstracts/v15_i01_a01/?utm_source=chatgpt.com "Universality in Elementary Cellular Automata by Matthew ..."
[16]: https://en.wikipedia.org/wiki/Block_cellular_automaton?utm_source=chatgpt.com "Block cellular automaton"
[17]: https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Bennett_Reversibiity.pdf?utm_source=chatgpt.com "Logical Reversibility of Computation*"
