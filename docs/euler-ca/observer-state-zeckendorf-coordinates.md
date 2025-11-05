# 观察者—状态离散流形的 Zeckendorf 坐标化：与 WSIG–EBOC–RCA 的公理化耦合、有限阶 Euler–Maclaurin 误差学与窗化迹稳定性

Version: 2.13

## 摘要

构造一套将"观察者状态"索引空间公理化为离散流形的理论，并以 Zeckendorf 唯一分解提供其对数—稀疏坐标图；再以一般线性递推族与 $\beta$-展开形成多图册与可逆坐标过渡。本文在 WSIG–EBOC–RCA 统一框架下前置"Notation & Axioms / Conventions"，以刻度同一式 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 为母尺，将"窗口/读数/测量"统一为算子—测度—函数分析对象。在"带限+Nyquist+有限阶 Euler–Maclaurin(EM)+Poisson"纪律下，我们建立：其一，离散流形 $\mathcal O$ 的 Zeckendorf 坐标图 $\Phi_{\rm Z}$ 的唯一性、最简性与对数尺度雅可比；其二，多图册过渡的"奇性不增"与"极点=主尺度"；其三，窗化 Toeplitz/Berezin 压缩 $T_{a,w,R}$ 的对数行列式泛函 $\mathscr F_R(a,w;\lambda)$ 对符号与窗口的变分、凹性与强稳定界，且对"位层扰动"呈指数级可积；其四，与 WSIG 三位一体测度坐标一致的换元不变性与非渐近误差闭合。全文为纯理论、公理化文本；有限阶 EM 与 Poisson 的计算模板作为正文内可直接调用的"卡片"给出。

---

## Notation & Axioms / Conventions

1. **母尺与三位一体。** 在绝对连续谱 a.e. 点上给定散射矩阵 $S(E)\in U(N)$、Wigner–Smith 延迟矩阵 $\mathsf Q(E):=-i\,S(E)^\dagger \partial_E S(E)$、半行列式相位 $\varphi(E):=\tfrac12\mathrm{Arg}\det S(E)$、相对态密度 $\rho_{\rm rel}(E)$。统一刻度定为 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)$。

2. **窗口—读数—算子。** 任意读数记作对谱测度的线性泛函 $\mathcal R[f]=\int f\,\mathrm d\mu_{\rm rel}$。窗化压缩以 Toeplitz/Berezin 记号 $T_{a,w,R}$ 或核 $K_{w,R}$ 表示，其中 $a$ 为符号、$w$ 为窗、$R$ 为截断/尺度参数；默认 $w$ 属于带限类或指数衰减类，使得 $T_{a,w,R}$ 至少为 Hilbert–Schmidt，且在适当条件下为迹类。

3. **有限阶误差学。** 全文只使用有限阶 EM 与 Poisson：任何由位层或准格点诱导的和/迹均分解为"Nyquist 主项 + 有限阶 Bernoulli 边界层 + 带外尾项"，并满足"奇性不增/极点=主尺度"的闭合纪律。

4. **观察者—状态离散流形。** 将观察者状态空间 $\mathcal O$ 视为由有限步可逆变换生成的局部有限图 $G(\mathcal O,\mathcal E)$，度量 $d_{\mathcal O}$ 取最短合法步数或带权步长。

5. **位层与 Zeckendorf 约束。** 黄金比 $\phi=(1+\sqrt5)/2$、斐波那契 $F_1=1,F_2=1,F_{k+1}=F_k+F_{k-1}$。位层二元串 $\varepsilon=(\varepsilon_k)_{k\ge2}\in\{0,1\}^{\mathbb N_{\ge2}}$ 受无相邻约束 $\varepsilon_k\varepsilon_{k+1}=0$。

6. **行内数学。** 一切数学表达式均以 $\cdots$ 行内呈现。

7. **谱半径/尺度常数与 $\rho_*$（统一约定）。** 对每个图册 $\Phi^{(\alpha)}$：若来自线性递推 $G_{k+1}=aG_k+bG_{k-1}$（$a,b\in\mathbb N$），令 $\rho_\alpha>1$ 为其特征多项式的主特征根；若来自 $\beta$-展开，则取 $\rho_\alpha:=\beta>1$。**统一约定**：在任一陈述中，记 $\rho_*:=\min_{\alpha\in\mathcal I}\rho_\alpha$，其中 $\mathcal I$ 为该陈述**实际涉及的图册集合**；若仅涉及单一图册 $\alpha$，则 $\rho_*=\rho_\alpha$；在纯 Zeckendorf 图册语境下取 $\rho_*=\rho_{\rm Z}=\phi=\tfrac{1+\sqrt5}{2}$。此约定用于文中一切尾界写作（例如 §1.4、§2.2、§4.3、§5.1 的 $O(\rho_*^{-\eta K_*})$）。

8. **主尺度深度与 $K_*$（统一约定）。** 对任一图册 $\Phi^{(\alpha)}$，记其位层占位比特为 $\varepsilon_k^{(\alpha)}(\omega):=\mathbf 1\{d_k^{(\alpha)}(\omega)\neq 0\}$（见 §3.1 记号补充）。在给定窗 $w$ 与测试/符号 $f$ 的上下文中，定义 $K_\alpha:=\max\Big\{k:\ \exists\,\omega\in\mathcal O\ \text{使}\ \varepsilon_k^{(\alpha)}(\omega)=1\ \text{且}\ w,f\ \text{在层}\ k\ \text{上有支撑}\Big\}$。若一条陈述仅涉及**单一图册** $\alpha$，则令 $K:=K_\alpha$；若涉及**多图册**（如过渡 $\Psi_{\alpha\to\beta}$），则统一取 $K_*:=\min\{K_\alpha,K_\beta,\ldots\}$，即在该陈述**实际涉及的图册集合**上取最坏（最小）主尺度深度。所有出现的尾界均写作 $O(\rho_*^{-\eta K_*})$，其中 $\rho_*$ 依第 7 条统一约定。此约定确保 §2.2、§3.3、§5.1 等处的误差界在单/多图册语境下语义一致且可直接检核。

---

## 1. 离散流形与 Zeckendorf 坐标

### 1.1 定义（离散流形）

令 $\mathcal O$ 为可数集，记 $G(\mathcal O,\mathcal E)$ 为由有限步可逆生成元构成的邻接图，$d_{\mathcal O}$ 为最短合法步数度量或其带权变体。对任意 $\omega\in\mathcal O$，允许定义局域"位层视图"以捕获其在多尺度上的可达性。

### 1.2 定义（Zeckendorf 坐标图）

称映射 $\Phi_{\rm Z}:\mathcal O\to\{0,1\}^{\mathbb N_{\ge2}}$ 为 Zeckendorf 坐标，若在某种与 $\mathbb N$ 的保结构识别下有 $X(\omega)=\sum_{k\ge2}\varepsilon_k(\omega)F_k$ 且 $\varepsilon_k\varepsilon_{k+1}=0$。$X$ 可理解为对数尺度上的稀疏"位层能级"。

### 1.3 定理（唯一性与最简形）

对任意 $n\in\mathbb N$，存在唯一二元串 $(\varepsilon_k)_{k\ge2}$ 使 $n=\sum_k \varepsilon_k F_k$ 且 $\varepsilon_k\varepsilon_{k+1}=0$。因此在相应识别下 $\Phi_{\rm Z}$ 为规范坐标图。

**证明。** 由贪婪算法与无相邻约束给出存在性与唯一性；最简无进位形由斐波那契相邻关系排除冗余表示。■

### 1.4 引理（对数—稀疏雅可比与读数一致化）

设 $J_{\rm Z}(\omega)=C_{\rm Z}\,\phi^{-\sum_k k\,\varepsilon_k(\omega)}$。假设：

(H1) 窗 $w$ 属带限或指数衰减类，且 $w(E)=0$ 于工作域外；测试函数 $f\in C^{m}$（$m\ge2$）并支撑于工作域；

(H2) $E:\mathcal O\to\mathbb R$ 关于位层切换满足两侧 Lipschitz 递减律：存在常数 $0<C_1\le C_2<\infty$ 使对任意层 $k$ 与合法切换 $\omega\mapsto\omega^{(k)}$ 有 $C_1\,\rho_{\rm Z}^{-k}\le|E(\omega)-E(\omega^{(k)})|\le C_2\,\rho_{\rm Z}^{-k}$，**并且另作假设**：层间相互作用具有有限半径（该性质不由无相邻约束推出，而作为模型假定引入）；

(H3) Nyquist 条件：按最深主尺度 $K_*$ 取样时，Poisson 带外能量落入窗的衰减区间。

则取 $C_{\rm Z}$ 使 $\sum_{\omega}J_{\rm Z}(\omega)\,w(\omega)=\int w(E)\,\mathrm d\mu_{\rm rel}(E)$ 后，成立 $\sum_{\omega\in\mathcal O}J_{\rm Z}(\omega)\,w(\omega)\,f\!\big(E(\omega)\big)=\int f(E)\,w(E)\,\mathrm d\mu_{\rm rel}(E)+O\!\big(\rho_*^{-\eta K_*}\big)$，其中常数 $\eta>0$ 仅依赖于 $m$、窗参数与 (H2) 的常数。证明基于有限阶 Euler–Maclaurin 与 Poisson 三分解，并由 (H2) 把层切换的增量等价到对数尺度。■

---

## 2. 有限阶 EM–Poisson 三分解（位层型）

### 2.1 设定

令 $f$ 为位层可分函数 $f(\omega)=\sum_k f_k(\varepsilon_k,k)$，窗 $w$ 属带限或指数类，使 $\sum_{\omega}w(\omega)|f(\omega)|$ 绝对可和。记最深主尺度为 $K:=\max\{k:\exists\,\varepsilon_k(\omega)=1\ \text{且}\ w,f \ \text{在} \ k\ \text{上有支撑}\}$。

**(D$_m$) 离散正则性（至阶 $m$）**：对每个 $\varepsilon\in\{0,1\}$ 与 $\ell=0,1,\dots,m$，记前向差分算子 $\Delta_k g(k):=g(k+1)-g(k)$、$\Delta_k^{\ell}:=\Delta_k\circ\cdots\circ\Delta_k$（$\ell$ 次）。要求 $\sup_{\varepsilon}\sum_{k\ge2}\big|\Delta_k^{\ell} f_k(\varepsilon,k)\big|<\infty$。若 $w$ **显式**依赖位层，则同样要求 $\sup_{\varepsilon}\sum_{k\ge2}\big|\Delta_k^{\ell} w_k(\varepsilon,k)\big|<\infty$；若 $w$ **不显式**依赖位层（即 $w_k$ 与 $k$ 无关），则省略对 $w$ 的差分正则性约束，并在涉及差分算子的公式中**仅对 $\ell\ge1$** 约定 $\Delta_k^{\ell} w_k\equiv 0$（$\ell=0$ 为恒等，不作 0 约定）。记 $|f|_{D_m}:=\max_{0\le \ell\le m}\sup_{\varepsilon}\sum_{k\ge2}\big|\Delta_k^{\ell} f_k(\varepsilon,k)\big|$。当 $w$ 与位层无关时约定 $|w|_{D_m}:=0$（不参与常数估计）。

### 2.2 定理（三分解与指数尾界）

在 2.1 的设定**并满足 (D$_m$)** 下，对任意有限阶 $m\in\mathbb N$ 有
$$\sum_{\omega\in\mathcal O} w(\omega)f(\omega)=\text{Nyquist 主项}+\sum_{j=1}^m\text{Bernoulli 修正}_j+\text{Poisson 带外尾}$$
且存在常数 $C_m,\eta>0$ 使误差项满足 $O(\rho_*^{-\eta K_*})$，其中 $K_*$ 按"Notation 8"定义（单图册情形下 $K_*=K$）。此处 $C_m=C_m\!\big(|f|_{D_m},|w|_{D_m},m,\text{窗带限/指数参数}\big)$，与图规模无关。

**证明要点。** 以位层 $k$ 为准连续变量对层内平滑项施行 EM 展开；无相邻约束将耦合限制为局域二体项；Poisson 校正抑制 alias；窗带限/指数衰减给出尾项指数界，获得 $O(\rho_*^{-\eta K_*})$。证明同前，但 EM 余项与边界层常数由 (D$_m$) 的差分范数控制。■

### 2.3 术语（极点=主尺度；奇性不增）

称由主尺度 $k\le K$ 诱导的非可去奇性为"极点"，其阶由 Nyquist 主项的不可消除项确定。在坐标过渡或局域变形下，极点阶不增加，记为"奇性不增"。

---

## 3. 多图册与坐标过渡

### 3.1 定义（递推族与 $\beta$-展开图）

取线性递推 $G_{k+1}=aG_k+bG_{k-1}$（$a,b\in\mathbb N$）或 $\beta>1$ 的贪婪展开，定义图册映射 $\Phi^{(\alpha)}:\mathcal O\to\mathcal D_\alpha^{\mathbb N}$，其中数字集 $\mathcal D_\alpha\subset\mathbb Z_{\ge0}$ 为有限集合：对 $\beta>1$ 的贪婪展开，取数字集 $\mathcal D_\alpha=\{0,1,\dots,\lceil\beta\rceil-1\}$，当 $\beta\notin\mathbb N$ 时等于 $\{0,1,\dots,\lfloor\beta\rfloor\}$（且当 $1<\beta\le2$ 时退化为 $\{0,1\}$），当 $\beta\in\mathbb N$ 时为 $\{0,1,\dots,\beta-1\}$；对递推族可取与其规范展开相容的有限数字集。约束可为无相邻或有限相邻型，并随图册给定。记图册 $\mathfrak A=\{\Phi^{(\alpha)}\}_\alpha$。

**记号补充。** 记 $d_k^{(\alpha)}(\omega)\in\mathcal D_\alpha$ 为第 $k$ 层数字，定义占位比特 $\varepsilon_k^{(\alpha)}(\omega):=\mathbf 1\{d_k^{(\alpha)}(\omega)\neq 0\}$。除非另述，所有与雅可比/位层权重相关的公式均以 $\varepsilon^{(\alpha)}$ 表示。

### 3.2 定义（过渡映射）

若 $\Phi^{(\alpha)}$、$\Phi^{(\beta)}$ 在子域 $\mathcal U\subset\mathcal O$ 同时有效，定义 $\Psi_{\alpha\to\beta}=\Phi^{(\beta)}\circ(\Phi^{(\alpha)})^{-1}$。

### 3.3 定理（在有限半径过渡下的 EM 控制与奇性不增）

**(H$_{\rm tr}$)**：存在 $L\in\mathbb N$ 使过渡 $\Psi_{\alpha\to\beta}$ 可由记忆长度 $\le L$ 的有限状态进/借位换元器实现（等价地，借/进位传播半径有全局上界）。

在带限/指数窗及有限阶 EM+Poisson 纪律与 (H$_{\rm tr}$) 下，**记** $\mathcal R^{(\gamma)}[f]:=\sum_{\omega\in\mathcal O}J_{\gamma}(\omega)\,w(\omega)\,f\!\big(E(\omega)\big)$（$\gamma\in\{\alpha,\beta\}$，定义与 §5.1 一致）。则过渡 $\Psi_{\alpha\to\beta}$ 对计数/迹泛函的影响满足 $\big|\mathcal R^{(\beta)}[f]-\mathcal R^{(\alpha)}[f]\big|\le C_{\alpha,\beta,m,L}\,\rho_*^{-\eta K_*}$，且若源图主尺度仅出现有限极点，则过渡后不新增主极点，极点阶保持不增。

**证明要点。** 由 (H$_{\rm tr}$) 将过渡等价为半径 $\le L$ 的进/借位卷积；EM 吸收局域扭曲为有限个边界层修正；Poisson 抑制别名；主尺度不可去奇性在有限耦合下保持，且常数对 $L$ 与图册谱半径仅呈多项式依赖。■

---

## 4. 窗化 Toeplitz/Berezin 压缩与对数行列式泛函

### 4.1 定义（算子与泛函）

给定符号 $a$、窗 $w$ 与截断 $R$，压缩 $T_{a,w,R}$ 定义为对 $\mathcal H$ 的窗—局域化 Toeplitz/Berezin 算子。设 $T_{a,w,R}$ 为迹类算子，并取参数 $\lambda\in\mathbb C$ 使 $I+\lambda T_{a,w,R}$ 可逆（**若 $\lambda\ne 0$，等价于** $-1/\lambda\notin\sigma(T_{a,w,R})$）。定义 $\mathscr F_R(a,w;\lambda):=\log\det\!\big(I+\lambda T_{a,w,R}\big)$（Fredholm 行列式），并规定以 $\lambda=0$ 为基点的主支解析延拓：若对所有 $t\in[0,1]$ 有 $\det\!\big(I+t\lambda T_{a,w,R}\big)\neq0$，则定义 $\mathscr F_R(a,w;\lambda)=\mathrm{tr}\,\log\!\big(I+\lambda T_{a,w,R}\big)$。此外，$\mathscr F_R(a,w;0)=0$。

### 4.2 定理（Gateaux/Fréchet 变分与凹性；强凹的充分条件与 Lipschitz 上界）

设 $T:=T_{a,w,R}$ 为迹类且自伴，取**变分方向** $\delta T,\Delta\in\mathcal S_1(\mathcal H)$（故亦属 $\mathcal S_2$），$\lambda\in\mathbb R$ 且 $I+\lambda T\succ0$。则对任意**自伴** $\delta T$，$\delta\mathscr F_R=\mathrm{tr}\!\big((I+\lambda T)^{-1}\lambda\,\delta T\big)$，$\delta^2\mathscr F_R=-\,\lambda^{2}\,\big|(I+\lambda T)^{-1/2}\,\delta T\,(I+\lambda T)^{-1/2}\big|_2^{\,2}\le 0$，因此 $\mathscr F_R$ 在自伴迹类方向上为凹且二阶负半定。若满足 (i) 的谱夹条件，则 $I+\lambda T\succ0$；**在 $\lambda\neq 0$ 时**可得显式强凹模量。进一步：

(i) **谱夹 + $\lambda\neq 0$ $\Rightarrow$ 强凹。** 若存在 $0<\alpha I\preceq I+\lambda T\preceq \beta I$ **且** $\lambda\neq 0$，则对 Hilbert–Schmidt 范数 $\delta^2\mathscr F_R(T)[\delta T,\delta T]\le -\,\frac{\lambda^2}{\beta^2}\,|\delta T|_2^2$，即在该局部区域以模量 $\lambda^2/\beta^2$ 强凹。**（注：当 $\lambda=0$ 时，$\delta^2\mathscr F_R\equiv 0$，仅为凹而非强凹。）**

(ii) **Neumann 区间 $\Rightarrow$ 局部梯度 Lipschitz（对称半径），对任意 $\Delta\in\mathcal S_1$。** 若 $r:=\max\big\{\Vert\lambda T\Vert_{\rm op},\Vert\lambda(T+\Delta)\Vert_{\rm op}\big\}<1$，则有 $\big|\nabla\mathscr F_R(T+\Delta)-\nabla\mathscr F_R(T)\big|_2\le \frac{\lambda^2}{(1-r)^2}\,|\Delta|_2$。（此处 $\nabla\mathscr F_R(T)=\lambda(I+\lambda T)^{-1}$，差分项属于 $\mathcal S_2$，可用 HS 范数度量。）证明用两侧 Resolvent 恒等式与 Neumann 级数，常数对称依赖 $T$ 与 $T+\Delta$，从而刻画真实的"局部"适用域。

**证明。** 由 $\log\det(I+\lambda T)=\mathrm{tr}\,\log(I+\lambda T)$ 与 Fréchet 微分规则；(i) 以 $A:=(I+\lambda T)^{-1}\lambda$ 得 $\delta^2\mathscr F_R=-\,\mathrm{tr}(A\,\delta T\,A\,\delta T)\le -s_{\min}(A)^2\,|\delta T|_2^2\le -(\lambda^2/\beta^2)\,|\delta T|_2^2$；(ii) 以 Neumann 展开与 Schatten 范数收敛判据得梯度 Lipschitz 常数。■

### 4.3 定理（位层扰动的 Lipschitz—强稳定界）

设 $a=\sum_k a_k$、$w=\sum_k w_k$ 为位层分块，且对某 $K$ 有 $\delta a=\sum_{k>K}\delta a_k$、$\delta w=\sum_{k>K}\delta w_k$，并取参数 $\lambda$，**使对所有 $t\in[0,1]$** 有 $\det\!\big(I+t\lambda\,T_{a,w,R}\big)\neq 0$ 且 $\det\!\big(I+t\lambda\,T_{a+\delta a,w+\delta w,R}\big)\neq 0$，从而二者的 $\log\det$ 可在**同一主支**上解析定义。（注：端点 $I+\lambda T$、$I+\lambda(T+\Delta)$ 的可逆性本身**不足以**保证上述沿径条件，故在本定理中将其作为**独立假设**列出。）则存在 $C,\eta>0$ 与窗带限相容的 Banach 范数 $|\cdot|_X,|\cdot|_Y$ 使
$$\big|\mathscr F_R(a+\delta a,w+\delta w;\lambda)-\mathscr F_R(a,w;\lambda)\big|\le C\big(|\delta a|_X+|\delta w|_Y\big)\rho_*^{-\eta K_*}$$
其中 $K_*$ 按"Notation 8"定义（本定理为单图册情形，故 $K_*=K$），且 $C$ 至多多项式依赖 $R$。

**证明要点。** 以位层分块写出 $\delta T=\sum_{k>K}\delta T_k$。令 $\Delta:=T_{a+\delta a,w+\delta w,R}-T_{a,w,R}=\delta T$。用迹范数次可加性与 $\Vert(I+\lambda T)^{-1}\Vert_{\rm op}$ 的有界性得到 Lipschitz 界；有限阶 EM 吸收层差，Poisson 抑制带外 alias，给出 $\rho_*^{-\eta K_*}$ 的指数衰减。常数 $C$ 可取与 $\max\!\big\{\Vert(I+\lambda T)^{-1}\Vert_{\rm op},\Vert(I+\lambda(T+\Delta))^{-1}\Vert_{\rm op}\big\}$ 多项式相关的量，使 resolvent 有界性进入估计。■

---

## 5. 与 WSIG 三位一体刻度的一致性

### 5.1 定理（换元一致性）

在 §3.3 的 (H$_{\rm tr}$)（有限半径进/借位过渡）与 §1.4 的 (H1)–(H3) 的相应假设下（对任一图册以其 $\rho_\alpha>1$ 取代 $\rho_{\rm Z}$），记 $\mathcal R[f]_{\alpha}:=\sum_{\omega\in\mathcal O} J_{\alpha}(\omega)\,w(\omega)\,f\!\big(E(\omega)\big)$，$J_{\alpha}(\omega)=C_{\alpha}\,\rho_{\alpha}^{-\sum_{k}k\,\varepsilon^{(\alpha)}_{k}(\omega)}$，其中 $\varepsilon^{(\alpha)}_{k}(\omega):=\mathbf 1\{d_k^{(\alpha)}(\omega)\neq 0\}$，$C_{\alpha}$ 由归一化 $\sum_{\omega}J_{\alpha}(\omega)\,w(\omega)=\int w(E)\,\mathrm d\mu_{\rm rel}(E)$ 确定。则任意过渡 $\Psi_{\alpha\to\beta}$ 下有 $\mathcal R[f]_{\alpha}=\mathcal R[f]_{\beta}+O\!\big(\rho_*^{-\eta K_*}\big)$，其中误差由过渡雅可比 $J_{\alpha\to\beta}$ 与有限阶 EM 边界层给出，其常数 $C_{\alpha,\beta,m,L}$ 仅依赖于窗的带限/指数参数、正则性阶 $m$、过渡的有限半径常数 $L$ 及图册对 $(\alpha,\beta)$ 的谱半径数据（如 $\rho_\alpha,\rho_\beta$），与图规模无关。

**记号补充（坐标串）。** 对 $\omega\in\mathcal U$，写 $d^{(\gamma)}(\omega):=\Phi^{(\gamma)}(\omega)$（$\gamma\in\{\alpha,\beta\}$）。过渡 $\Psi_{\alpha\to\beta}$ 作用于 $\alpha$-坐标串，满足 $\Psi_{\alpha\to\beta}\!\big(d^{(\alpha)}(\omega)\big)=d^{(\beta)}(\omega)$。

**定义（过渡雅可比）。** $J_{\alpha\to\beta}(\omega):=\frac{J_{\beta}(\omega)}{J_{\alpha}(\omega)}=\frac{C_\beta}{C_\alpha}\,\rho_{\beta}^{-\sum_{k}k\,\varepsilon^{(\beta)}_{k}(\omega)}\,\rho_{\alpha}^{+\sum_{k}k\,\varepsilon^{(\alpha)}_{k}(\omega)}$，其中 $J_{\gamma}(\omega)=C_{\gamma}\,\rho_{\gamma}^{-\sum_{k}k\,\varepsilon^{(\gamma)}_{k}(\omega)}$（见本节开头），且 $d^{(\beta)}(\omega)=\Psi_{\alpha\to\beta}\!\big(d^{(\alpha)}(\omega)\big)$ 仅用于指明两图册坐标的一致对应关系。

**证明要点。** 将读数重写为对 $\mu_{\rm rel}$ 的线性泛函后，坐标变化仅改变计数密度；雅可比修正配合有限阶 EM 校正使差异降为指数小量。■

### 5.2 推论（窗—群延迟比的坐标独立性）

对任意观测三元 $(\mathcal H,w,S)$，其窗—群延迟读数与相位—密度—延迟三位一体的比值类在图册选择下保持不变，误差仅为 $O(\rho_*^{-\eta K_*})$ 的指数级小量。

---

## 6. 复杂度几何与测地

### 6.1 定义（操作复杂度与测地）

在 $G(\mathcal O,\mathcal E)$ 上，以最小合法步数定义从基准态到目标态的操作复杂度 $\mathcal C$，或采用位层带权 $L^1/L^2$/Bregman 代价；相应最小代价路径称为测地。

### 6.2 命题（曲率直觉与坐标弯曲）

若坐标过渡 $\Psi_{\alpha\to\beta}$ 系统性引入长程进/借位并导致描述长度放大，可解释为正曲率效应；有限阶 EM 与 Poisson 给出该弯曲对窗化读数的可积上界，从而复杂度度量在图册间保持准等距。

---

## 7. EBOC 与 RCA 的语义对位

1. **EBOC（永恒静态块·观察—计算）。** 位层坐标是"叶层日志"的规范账本；读数作为对 $\mu_{\rm rel}$ 的泛函只依赖母尺，坐标仅改变计数权，不改变刻度同一式。

2. **RCA（可逆元胞自动机）。** 将"激活 $F_k$ 层"解释为打开第 $k$ 层可逆门；合法加法—进位—回滚构成可逆滑动块，测地对应最小门列；位层受限扰动等价于高层稀疏门的微扰，其对 $\mathscr F_R$ 的影响由 $\rho_*^{-\eta K_*}$ 统御。

3. **WSIG（窗化散射与信息几何）。** 窗—群延迟读数以位层计数实现后与三位一体母尺严格对齐，框架提供非渐近误差预算与坐标独立的稳定性陈述。

---

## 8. 标准化"卡片"（正文内可即取即用）

* **刻度卡。** $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$；任何坐标/图册变换只经由雅可比修正作用于计数密度，不触动母尺。

* **误差卡。** 位层型和/迹遵循"Nyquist 主项 + 有限阶 Bernoulli 边界层 + 带外尾项"，并满足"奇性不增/极点=主尺度"；对最深主尺度 $K_*$ 给出 $O(\rho_*^{-\eta K_*})$ 尾界。

* **稳定卡。** $\big|\Delta \mathscr F_R\big|\le C\big(|\delta a|_X+|\delta w|_Y\big)\rho_*^{-\eta K_*}$，$C$ 至多多项式依赖 $R$ 与窗带限参数。

* **过渡卡。** 在 (H$_{\rm tr}$) 下，任意图册过渡 $\Psi_{\alpha\to\beta}$ 等价于半径 $\le L$ 的卷积型进/借位，从而"奇性不增"，主尺度极点阶保持；若 (H$_{\rm tr}$) 不满足，则不主张上述性质与界。

---

## 9. 主要定理的证明纲要（可扩展为长证）

1. **Zeckendorf 唯一性。** 贪婪选择最大 $F_k$ 并以无相邻约束阻止进位回流，给出唯一最简形；该过程在 $G(\mathcal O,\mathcal E)$ 的局域生成元语义下可视作可逆规范化。

2. **有限阶 EM–Poisson。** 将位层 $k$ 看作准连续变量，对层内平滑项施 EM 至阶 $m$，边界层系数由 Bernoulli 数决定；别名项由 Poisson 求和以窗带限衰减抑制，获得 $O(\rho_*^{-\eta K_*})$。

3. **凹性与强凹。** 由 $f(T)=\log\det(I+\lambda T)$ 的算子凸性—凹性理论及 Fréchet 微分，二阶式为负半定；当 $\Vert\lambda T\Vert_{\rm op}<1$ 时 Neumann 收敛给出显式模量。

4. **奇性不增。** 以 Mellin/拉普拉斯符号化描述主尺度极点来源，过渡仅改变有限层耦合，不产生新的主极点；极点阶由主项的不可去分量决定并在过渡下保持不增。

5. **换元一致性。** 读数重写为对 $\mu_{\rm rel}$ 的线性泛函；图册过渡的雅可比修正与有限阶 EM 校正相抵至指数小量，留存母尺不动点。

---

## 10. 结论要点（形式化摘述）

本文以 Zeckendorf 及其递推/$\beta$-扩展图册为观察者—状态离散流形之对数—稀疏坐标，并在 WSIG–EBOC–RCA 框架与母尺 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 下，给出：$(1)$ 坐标唯一与对数尺度雅可比；$(2)$ 坐标过渡的有限阶 EM 控制与"奇性不增/极点=主尺度"；$(3)$ 窗化对数行列式泛函的凹性与位层扰动的指数稳定；$(4)$ 与三位一体母尺一致的换元不变性与非渐近误差闭合。上述结果为将"坐标选择—窗化读数—散射刻度"粘合为一体的几何—算子—测度三重一致性提供了公理化与可检核的误差预算。
