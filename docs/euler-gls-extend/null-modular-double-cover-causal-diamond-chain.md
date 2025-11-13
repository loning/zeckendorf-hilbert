# Null–Modular 双覆盖与重叠因果钻石链

**——二次型局域化的全序近似桥接、容斥—马尔可夫拼接与分布论散射刻度的奇偶阈值**

Version: 2.11

**MSC**：81T05；81T40；83C57；83C05；46L30；46L60；58J35；81U40；42A38
**Keywords**：Tomita–Takesaki 模理论；零测度边界；因果钻石；半侧模包含；强次可加与马尔可夫性；Petz 恢复；QNEC；JLMS；Wigner–Smith 群延迟；Birman–Kreĭn／Friedel–Lloyd；Toeplitz／Berezin 压缩；Euler–Maclaurin 与 Poisson；GHY 关节项；$\mathbb Z_2$ 取向账本

---

## Abstract

提出以因果钻石零测度边界为载体的**Null–Modular 双覆盖**，在真空二次型意义下将模哈密顿量分解为两层 null 片上的局部能流积分。通过一个**全序近似桥接引理**，把一般钻石规约为同一零测度超平面上的单调半空间族极限，并以二次型闭性与主控收敛确保极限与近似路径无关。建立**重叠因果钻石链**的**模哈密顿量容斥恒等式**与**马尔可夫拼接**；在非全序切割时，引入**马尔可夫缺口线密度**定量刻画失效并给出与层状度的比较不等式。散射侧，在**分布论 Birman–Kreĭn—Friedel–Lloyd—Wigner–Smith** 刻度下引入**窗化读数**，以 Toeplitz／Berezin 压缩、Euler–Maclaurin 与 Poisson 纪律给出**可见常数与门槛不等式**，从而证明**链式 $\mathbb Z_2$ 奇偶阈值稳定**并给出对**弱非幺正扰动**的鲁棒条件。几何侧，以**半侧模包含**构成链式推进的一参数半群；在全息极限下用 **JLMS** 等式将边界容斥—马尔可夫提升为体区纠缠楔的法向模流，并给出次阶 $1/N$ 修正的量纲上界。最后在 $1+1$ 与 $2+1$ 维的最小模型中显算 **GHY 关节项**与平方根粘接类的**$\mathbb Z_2$ 账本一致性**，并提供**可复现实验参数表**与**核查清单**。

---

## 1  Introduction & Historical Context

Tomita–Takesaki 模理论将冯·诺依曼代数—矢量态对 $(\mathcal A,\Omega)$ 赋予模群 $\Delta^{\mathrm i t}$ 与模对合 $J$。劈形区上的 Bisognano–Wichmann 性质把模流几何化为洛伦兹推变。零测度几何方面，半空间及其光滑变形的**局域模哈密顿量**与 QNEC 之真空饱和、光锥／光前上的**真空马尔可夫性**与强次可加饱和已形成稳固基础。代数侧，**半侧模包含**(HSMI) 提供包含—一参数半群—Borchers 交换关系的代数骨架。全息侧，**JLMS** 等式在大 $N$ 领先阶同定边界与体区相对熵。散射侧，**Birman–Kreĭn** 把行列式相位与谱移函数等同，**Friedel–Lloyd** 与 **Wigner–Smith** 将态密度差与群延迟迹统一；**Toeplitz／Berezin** 压缩与 **Szegő／迹公式**提供窗化读数的算子—符号工具；**Euler–Maclaurin** 与 **Poisson** 纪律则给出指数或代数衰减的误差上界。本文在此框架内系统构建 Null–Modular 双覆盖与重叠钻石链的整合理论。

---

## 2  Model & Assumptions

### 2.1 二次型框架与自然域

取闵氏时空 $\mathbb R^{1,d-1}$（$d\ge2$）。令 $\mathcal D_0$ 为真空的能量有界矢量所成稠密域。

**记号与测度约定**：零测度边界分解为两层 $\widetilde E=E^+\sqcup E^-$；以下记号 $\int_{E^\sigma}(\cdots)\,d\lambda\,d^{d-2}x_\perp$ 指在该层上按仿射参数 $\lambda$ 与横向坐标 $x_\perp$ 的标准测度积分。

设对任一区域 $R$ 存在下半界闭二次型

$$
\mathfrak k_R[\psi]
:=\sum_{\sigma=\pm}\int_{E^\sigma} g_\sigma^{(R)}(\lambda,x_\perp)\,
\langle\psi, T_{\sigma\sigma}(\lambda,x_\perp)\psi\rangle\,d\lambda\,d^{d-2}x_\perp,
\quad \psi\in\mathcal D_0,
$$

从而存在自伴算子 $K_R$ 满足 $\langle\psi,K_R\psi\rangle=\mathfrak k_R[\psi]$。CFT 的球形区／劈形与其共形像给出精确几何等式。

设 $\mathfrak k_R$ 下半界为 $a_R\in\mathbb R$，即 $\mathfrak k_R[\psi]\ge a_R|\psi|^2$。取任意 $c_R>-a_R$，定义**移位图范数**

$$|\psi|_{\mathfrak k_R,c_R}^2:=|\psi|^2+\big(\mathfrak k_R[\psi]+c_R|\psi|^2\big),$$

则 $(\mathcal D(\mathfrak k_R),|\cdot|_{\mathfrak k_R,c_R})$ 完备，且与自伴算子 $K_R$ 的一表示定理相容。

### 2.2 零测度局域化与 QNEC

在零测度半空间 $R_V=\{u=0,\ v\ge V(x_\perp)\}$（$V\in C^2$）中，

$$
K_V=2\pi\int d^{d-2}x_\perp\int_{V(x_\perp)}^\infty (v-V)\,T_{vv}(v,x_\perp)\,dv
$$

作为二次型恒等式成立；其二阶变分核为 $2\pi\,T_{vv}$，与 QNEC 真空饱和一致。

### 2.3 双覆盖与粘接、平方根覆盖与账本

零测度边界分解为两层 $\widetilde E=E^+\sqcup E^-$。模对合 $J$ 交换两层并反转取向，模群在可几何化情形沿仿射参数 $\lambda$ 生成可积流。接缝粘接以 $\epsilon_i\in\{\pm1\}$ 记账。散射侧引入"平方根覆盖" $P_{\sqrt S}=\{(E,\sigma):\sigma^2=\det S(E)\}$ 的 $\mathbb Z_2$ 主丛结构；链式闭路的粘接类与关节项取向符号共享同一 $\mathbb Z_2$ 账本。

### 2.4 散射—信息刻度与窗化

幺正散射矩阵 $S(E)$ 分段 $C^{2m}$ 且 $S(E)-\mathbb I$ 在能带内为迹类；定义

$$
Q(E):=-\mathrm i\,S^\dagger\partial_E S,\quad
\varphi(E):=\tfrac12\arg\det S(E),\quad
\rho_{\rm rel}(E):=\tfrac{1}{2\pi}\operatorname{tr}Q(E).
$$

采用窗函数 $h\in\mathcal S(\mathbb R)$（如高斯），**或** $h\in C_c^{2m+1}(\mathbb R)$ 且端点至 $2m$ 阶喷气为零（$m\ge1$）。在此情形有 $\widehat h(\omega)=O(|\omega|^{-(2m+1)})$。若 $h$ 仅为紧支撑的分段 $C^{2m}$（端点允许角点，含 Kaiser–Bessel），则采用**角点尾界**（至少 $O(|\omega|^{-2})$），据此定理 G 的 Poisson 混叠项级数收敛。相应的 Toeplitz／Berezin 压缩与迹公式沿用 §3.5 的误差分解，其中 **端点余项 $R_{\rm EM}$**：对 $C_c^\infty$ 窗取 $O(\ell^{-(m-1)})$；对分段 $C^{2m}$ 的紧支撑窗（含 Kaiser–Bessel）采用**角点版**估计（阶一般降至 $O(\ell^{-1})$），并计入总误差预算 $\mathcal E_h(\gamma)$。

**附加假设（Toeplitz 交换子可积性）**：在任意考察能带 $\mathcal I$ 上，$\partial_E S(E)\in\mathfrak S_2$ 且 $\displaystyle\int_{\mathcal I}|\partial_E S(E)|_2\,dE<\infty$。于是 $R_{\rm T}\le C_{\rm T}\,\ell^{-1/2}\!\int_{\mathcal I}|\partial_E S|_2\,dE$ 有界。

**全局约定（窗与尾项）**：设 $\int_{\mathbb R}h=1$ **且 $h\ge0$**，尺度 $h_\ell(E)=\ell^{-1}h(E/\ell)$。定义

$$\boxed{R_{\rm tail}(\ell,\mathcal I,E_0):=\int_{\mathbb R\setminus\mathcal I(\gamma)} |h_\ell(E-E_0)|\,dE\in[0,1].}$$

*注*：此时 $R_{\rm tail}=1-\int_{\mathcal I(\gamma)}h_\ell(E-E_0)\,dE$。

**符号约定（Poisson 步长）** 记 $\Delta>0$ 为能带分片／频域采样的步长（网格间距）；在 Poisson 重求和估计中取

$$\int_{\mathcal I}|R_{\rm P}|\,dE\ \le\ C_h\sum_{|q|\ge1}\big|\widehat h\left(2\pi q\,\ell/\Delta\right)\big|,$$

与 §3.5 的同名项一致使用此 $\Delta$。

### 2.5 链与交叠、代数假设

链 $\{D_j\}$ 相邻交叠同面；对每个横向点 $x_\perp$ 切割全序为默认假设。代数侧采用 split property 与 strong additivity 的标准假设；HSMI 作为链式推进的代数实现。

---

## 3  Main Results（每条结果后标注"意义／域"）

### 3.1  双层几何分解与全序近似桥接

**定理 A（双层几何分解）**

$$
K_D = 2\pi\sum_{\sigma=\pm}\int_{E^\sigma} g_\sigma(\lambda,x_\perp)\,
T_{\sigma\sigma}(\lambda,x_\perp)\,d\lambda\,d^{d-2}x_\perp,
$$

其中 $T_{++}=T_{vv},\,T_{--}=T_{uu}$。CFT 球形钻石中 $g_\sigma(\lambda)=\lambda(1-\lambda)$。
[**二次型；域：真空，CFT 为精确等式**]

**假设 A′（null 能流一致可积）** 对任意 $\psi\in\mathcal D_0$ 与几何上有界的单调近似族 $\{R_{V_\alpha}^\pm\}$，存在 $H_\sigma\in L^1_{\mathrm{loc}}(E^\sigma\times\mathbb R^{d-2})$ 使

$$
\big|g^{(\alpha)}_\sigma(\lambda,x_\perp)\,\langle\psi,T_{\sigma\sigma}(\lambda,x_\perp)\psi\rangle\big|
\le H_\sigma(\lambda,x_\perp)
$$

几乎处处成立，且 $\sup_\alpha\int_{\mathcal K} H_\sigma<\infty$ 对任意紧集 $\mathcal K\subset E^\sigma\times\mathbb R^{d-2}$。

**引理 A（有序切割近似）**
存在沿 $E^\pm$ 的单调半空间族 $\{R_{V_\alpha}^\pm\}$ 使

$$
\langle\psi,K_D\psi\rangle=\lim_{\alpha\to\infty}
\sum_{\sigma=\pm}2\pi\!\int_{E^\sigma}
g^{(\alpha)}_\sigma\,\langle\psi,T_{\sigma\sigma}\psi\rangle,
\qquad g^{(\alpha)}_\sigma\to g_\sigma\ \text{于}\ L^1_{\mathrm{loc}},
$$

并且极限与选取的有序逼近无关。
[**二次型收敛；域：真空，QNEC 真空饱和**]

**排除说明**：若缺失 BW／HSMI 或边界粗糙到破坏 QNEC 真空饱和，上述分解不保证成立。

**假设 A''（二次型下半界与闭性门槛）** 设所有参与区域 $R$ 的二次型 $\mathfrak k_R$ 存在统一下半界 $a\in\mathbb R$，即 $\mathfrak k_R[\psi]\ge a\,|\psi|^2$。取任意 $c>-a$ 定义移位图范数 $|\psi|_{\mathfrak k_R,c}^2=|\psi|^2+(\mathfrak k_R[\psi]+c|\psi|^2)$，则 $\mathfrak k_R$ 闭且 $\mathcal D(\mathfrak k_R)$ 关于 $|\cdot|_{\mathfrak k_R,c}$ 完备。

**命题 A.1（极限与路径无关的充要条件）** 若满足假设 A′ 与 A''，并且沿任意两族单调近似 $\{R_{V_\alpha}\}$、$\{R_{\widetilde V_\beta}\}$ 都有 $g^{(\alpha)}\to g$、$\widetilde g^{(\beta)}\to g$ 于 $L^1_{\mathrm{loc}}$，则对每个 $\psi\in\mathcal D_0$，极限

$$
\lim_{\alpha\to\infty}\!\sum_{\sigma}\!\int g^{(\alpha)}_\sigma\,\langle\psi,T_{\sigma\sigma}\psi\rangle
=\lim_{\beta\to\infty}\!\sum_{\sigma}\!\int \widetilde g^{(\beta)}_\sigma\,\langle\psi,T_{\sigma\sigma}\psi\rangle .
$$

理由：主控收敛将每条近似的极限与 $g$ 同一；闭性与下半界给出二次型连续性，故与近似路径无关。

### 3.2  容斥与闭性

**定理 B（容斥恒等式）**
同一零测度面上的 $\{R_{V_i}\}_{i=1}^N$ 满足

$$
K_{\cup_i R_{V_i}}
=\sum_{k=1}^N(-1)^{k-1}\!\!\sum_{1\le i_1<\cdots<i_k\le N}\!
K_{R_{V_{i_1}}\cap\cdots\cap R_{V_{i_k}}}.
$$

逐点恒等式 $(v-\min_i V_i)_+ = \sum_{k\ge1}(-1)^{k-1}\sum_{|I|=k}(v-\max_{i\in I}V_i)_+$ 推得。
[**二次型；域：真空，$V_i$ 分段光滑**]

**命题 B（闭性）** 记 $\mathfrak k:=\mathfrak k_{\cup_i R_{V_i}}$ 为容器域的闭二次型，其下半界为 $a\in\mathbb R$。取任意 $c>-a$。若

$$\psi_n,\psi\in \mathcal D(\mathfrak k)\cap\bigcap_{I\ne\emptyset}\mathcal D(\mathfrak k_{R_{V_I}}),
\qquad \psi_n\to\psi\ \text{于移位图范数 }|\cdot|_{\mathfrak k,c}\text{ 下},$$

则容斥恒等式两侧对 $\psi_n$ 的二次型值同收敛至对 $\psi$ 的值；因而该恒等式在上述形式域上闭合。其中

$$|\psi|_{\mathfrak k,c}^2:=|\psi|^2+\big(\mathfrak k[\psi]+c|\psi|^2\big).$$
[**二次型闭性**]

**说明（可操作域）** 上述闭性在共同形式域 $\mathcal D_*:=\mathcal D(\mathfrak k)\cap\bigcap_{I\ne\emptyset}\mathcal D(\mathfrak k_{R_{V_I}})$ 上成立；对链式应用，取 $V_i$ 分段 $C^1$ 且有一致 Lipschitz 常数即可确保 $\mathcal D_*$ 非空且稠密。

### 3.3  马尔可夫拼接、Petz 恢复与非全序缺口

**定理 C（马尔可夫拼接）**
同面全序下，真空满足

$$
I(D_{j-1}:D_{j+1}\mid D_j)=0,\qquad
K_{D_{j-1}\cup D_j}+K_{D_j\cup D_{j+1}}-K_{D_j}-K_{D_{j-1}\cup D_j\cup D_{j+1}}=0 .
$$

[**信息等价；域：真空，split／strong additivity**]

**定理 C′（非全序的马尔可夫缺口）** **定义（层状度）**：令 $V_i^\pm(x_\perp)$ 分别为 $E^\pm$ 上的阈值，定义

$$\boxed{\kappa(x_\perp):=\#\{(a,b):a<b,\ (V_a^+-V_b^+)(V_a^--V_b^-)<0\}.}$$

*注*：全序切割时 $\kappa\equiv 0$。据此得 $\iota$ 对 $\kappa$ 单调非降之比较不等式。

为限定 $\iota(v,x_\perp)$ 的 $v$ 域，记

$$
v_-(x_\perp):=\min_i V_i^+(x_\perp),\qquad v_+(x_\perp):=\max_i V_i^+(x_\perp),
$$

即 $E^+$ 层上该链覆盖的有效支撑区间端点；以下关于 $v$ 的陈述均在 $[v_-(x_\perp),v_+(x_\perp)]$ 内理解。

以相对熵密度核定义的**马尔可夫缺口线密度** $\iota(v,x_\perp)\ge0$ 满足

$$
I(D_{j-1}\!:\!D_{j+1}\mid D_j)=\iint\iota(v,x_\perp)\,dv\,d^{d-2}x_\perp,
\qquad
\iota\ \text{对}\ \kappa\ \text{单调非降}.
$$

特别地，全序时 $\kappa\equiv0$ 且 $I(D_{j-1}\!:\!D_{j+1}\mid D_j)=0$（马尔可夫饱和）。

[**不等式；域：真空**]

**引理 C.1（层状度—缺口比较）** 设 $V_i^\pm$ 分段 $C^1$ 且在每个 $x_\perp$ 上仅有限次交叉。则存在常数 $c_*>0$（依赖于 $\sup|\partial V_i^\pm|$ 与交叉数上界）使在分布意义

$$
\iota(v,x_\perp)\ \ge\ c_*\,\kappa(x_\perp)\,\mathbf 1_{\{v\in[v_-(x_\perp),v_+(x_\perp)]\}} .
$$

与 Fawzi–Renner 下界合用，给出非全序时的缺口定量下界。

**约定（保真度）** 本文统一取 Uhlmann 保真度（未取平方）

$$F(\rho,\sigma):=\big|\sqrt{\rho}\sqrt{\sigma}\big|_1\in[0,1].$$

据此，Fawzi–Renner 不等式写为

$$I(A:C\mid B)\ge -2\ln F,\qquad\text{等价地 }F\ge e^{-I(A:C\mid B)/2}.$$

**定理 D（Petz 恢复与稳定性 — 自洽版）** 记 $A=D_{j-1}$，$B=D_j$，$C=D_{j+1}$。取忘却通道

$$\Phi_{BC\to B}(X_{BC})=\operatorname{Tr}_C[X_{BC}],\qquad \Phi^*(Y_B)=Y_B\otimes \mathbb I_C .$$

以 $\sigma_{BC}=\rho_{BC}$ 为参考态（故 $\sigma_B=\rho_B$），Petz 恢复映射 $\mathcal R_{B\to BC}$ 定义为

$$\boxed{\ \mathcal R_{B\to BC}(X_B)=\sigma_{BC}^{1/2}\big(\sigma_B^{-1/2}X_B\,\sigma_B^{-1/2}\otimes\mathbb I_C\big)\sigma_{BC}^{1/2}\ },$$

其中逆在 $\mathrm{supp}(\sigma_B)$ 上取伪逆。**当且仅当** $I(A:C\mid B)=0$ 时存在完美恢复

$$(\mathrm{id}_A\otimes \mathcal R_{B\to BC})(\rho_{AB})=\rho_{ABC}.$$

一般情形存在**旋转平均 Petz 恢复** $\mathcal R^{\rm rot}_{B\to BC}$ 使

$$I(A:C\mid B)\ \ge\ -2\ln F\left(\rho_{ABC},\ (\mathrm{id}_A\otimes \mathcal R^{\rm rot}_{B\to BC})(\rho_{AB})\right),
\quad\text{等价地 }F\ge e^{-I(A:C\mid B)/2}.$$

上述不等式对未旋转的 $\mathcal R_{B\to BC}$ 一般不保证成立；本文统一采用 $\mathcal R^{\rm rot}_{B\to BC}$ 处理稳定性命题。
[**完全恢复／稳定性；域：马尔可夫饱和**]

### 3.4  半侧模包含与链式推进

**定理 E（HSMI 推进）**
若 $(\mathcal A(D_j)\subset\mathcal A(D_{j+1}),\Omega)$ 为右 HSMI，则存在正能量一参数半群与 $\Delta_{\mathcal A(D_{j+1})}^{\mathrm i t}$ 协变，并把 $\mathcal A(D_j)$ 内禀推进至 $\mathcal A(D_{j+1})$。
[**代数结构；域：HSMI**]

### 3.5  分布论 KFL—WS 刻度与窗化奇偶阈值

**非平滑窗过渡与误差并入**：若窗 $h\in C_c^0$ 且在支撑内分段 $C^{2m}$（端点允许角点），取标准平滑核 $\rho_\delta$ 并定义 $h_{\ell,\delta}:=h_\ell*\rho_\delta$。则对每个固定 $\ell>0$ 有

$$\big|h_{\ell,\delta}-h_\ell\big|_{L^1(\mathbb R)}=O(\delta),$$

且定理 F、Toeplitz／Berezin 压缩与迹公式可先对 $h_{\ell,\delta}$ 应用；由三角不等式可将

$$R_{\rm smooth}(\delta):=\int_{\mathcal I(\gamma)}|h_{\ell,\delta}-h_\ell|\,dE$$

并入总误差预算 $\mathcal E_h(\gamma)$。在定理 G 的门槛条件下，选取 $\delta=\delta(\ell,m)$ 使 $R_{\rm smooth}(\delta)\le \frac12\,\delta_*(\gamma)$，从而保留与 $h_\ell$ 同一的奇偶阈值结论。

**定理 F（分布论刻度同一）** 对 $h\in C_c^\infty(\mathbb R)$（或 $h\in\mathcal S(\mathbb R)$），

$$
\int \partial_E\arg\det S(E)\,h(E)\,dE
=\int \operatorname{tr}Q(E)\,h(E)\,dE
=-2\pi\!\int \xi'(E)\,h(E)\,dE ,
$$

其中 $\xi$ 为谱移函数。（约定：Birman–Kreĭn 取 $\det S(E)=e^{-2\pi \mathrm i\,\xi(E)}$。）能带阈值与嵌入本征态由选择 $\operatorname{supp}h$ 避开；长程势需改用相应的广义 KFL。
[**分布等式；域：$S-\mathbb I\in\mathfrak S_1$，分段光滑**]

**命题 F′（相对／修正口径）** 若 $S_0(E)$ 为在能带内同片解析、无零／极点的参考散射，且

$$
U(E):=S(E)S_0(E)^{-1},\qquad U(E)-\mathbb I\in\mathfrak S_2,\quad \partial_E U\in\mathfrak S_2,\ \int_{\mathcal I}|\partial_E U|_2<\infty,
$$

则 Carleman 行列式满足

$$
\int \partial_E\arg\det_2 U(E)\,h(E)\,dE
=\int \operatorname{tr}\big(Q(E)-Q_0(E)\big)\,h(E)\,dE,
$$

其中 $Q=-\mathrm i\,S^\dagger\partial_E S$，$Q_0=-\mathrm i\,S_0^\dagger\partial_E S_0$。若 $S$ 幺正而 $S_0=\mathbb I$，上式退化为定理 F。此命题给出“非迹类但相对二阶可迹”的窗口下的相位—群延迟—谱移一致性。

**注（π/2 缓冲的来源）** 在奇偶判定中，$(-1)^{\lfloor\Theta/\pi\rfloor}$ 仅当 $\Theta$ 穿越奇数个 $\pi$ 时翻转。将扰动总量收敛至 $<\pi/2$ 保证不会跨越最近的整数倍 $\pi$，因此与无扰动的奇偶一致；取 $\delta_*(\gamma)=\min\{\pi/2,\delta_{\rm gap}(\gamma)\}-\varepsilon$ 即为该缓冲的显式化。

**支路约定（arg 的正则化）** 取 $\arg\det S$ 的连续化分支于能带内除去可数离散集的点后定义；其分布导数 $\partial_E\arg\det S$ 不依赖支路的 $2\pi$ 跳跃选择，因 $h\in C_c^\infty$ 将跳跃消光并由 DOI／Helffer–Sjöstrand 表示与 $\operatorname{tr}Q$ 匹配。

**定理 G（窗化奇偶阈值；带间隙门槛）**
令

$$
\Theta_h(\gamma):=\frac12\int_{\mathcal I(\gamma)}\operatorname{tr}Q(E)\,h_\ell(E-E_0)\,dE,
\qquad \nu_{\rm chain}(\gamma):=(-1)^{\lfloor \Theta_h(\gamma)/\pi\rfloor}.
$$

定义无窗极限

$$
\Theta_{\rm geom}(\gamma):=\frac12\int_{\mathcal I(\gamma)}\operatorname{tr}Q(E)\,dE
=\int_{\mathcal I(\gamma)}\varphi'(E)\,dE
=\varphi(E_2)-\varphi(E_1),
$$

其中 $\mathcal I(\gamma)=[E_1,E_2]$，$\varphi(E)=\tfrac12\arg\det S(E)$。定义间隙

$$
\delta_{\rm gap}(\gamma):=\operatorname{dist}\big(\Theta_{\rm geom}(\gamma),\pi\mathbb Z\big).
$$

在 $\int_{\mathbb R}h=1$、并令

$$
\boxed{\ \mathcal E_h(\gamma)\ :=\ \underbrace{\int_{\mathcal I}|R_{\rm EM}|\,dE}_{\text{EM 端点}}
+\underbrace{\int_{\mathcal I}|R_{\rm P}|\,dE}_{\text{Poisson 混叠}}
+\underbrace{C_{\rm T}\,\ell^{-1/2}\!\int_{\mathcal I}\!|\partial_E S|_2\,dE}_{\text{Toeplitz 交换子}}
+\ \underbrace{R_{\rm tail}(\ell,\mathcal I,E_0)}_{\text{区间外尾部}}\ \le\ \delta_*(\gamma)\ } ,
$$

其中

$$R_{\rm tail}(\ell,\mathcal I,E_0):=\int_{\mathbb R\setminus\mathcal I(\gamma)} |h_\ell(E-E_0)|\,dE\in[0,1].$$

*附注*：若 $h\ge0$ 且 $\int_{\mathbb R} h=1$，则 $R_{\rm tail}=1-\int_{\mathcal I(\gamma)} h_\ell(E-E_0)\,dE$。$\delta_*(\gamma):=\min\big\{\tfrac{\pi}{2},\delta_{\rm gap}(\gamma)\big\}-\varepsilon$。若存在 $\ell>0,\Delta>0,m\in\mathbb N$ 与 $\varepsilon\in(0,\delta_{\rm gap}(\gamma))$ 使上述不等式成立，则对任一满足上述窗质量条件的窗中心 $E_0$，

$$
\nu_{\rm chain}(\gamma)=(-1)^{\lfloor \Theta_h(\gamma)/\pi\rfloor}
=(-1)^{\lfloor \Theta_{\rm geom}(\gamma)/\pi\rfloor}.
$$

这里
$\bullet$ $R_{\rm EM}$ 为 Euler–Maclaurin 端点余项，满足 $\int|R_{\rm EM}|\le C_m\,\ell^{-(m-1)}$；
$\bullet$ $R_{\rm P}$ 为 Poisson 混叠，满足

$$\int_{\mathcal I}|R_{\rm P}|\,dE\ \le\ C_h\sum_{|q|\ge1}\Bigl\lvert\widehat h\left(\tfrac{2\pi q\,\ell}{\Delta}\right)\Bigr\rvert,$$

其中 **$\Delta>0$** 为 Poisson 求和所用的**能量采样步长（能带晶格间距）**；
$\bullet$ $R_{\rm T}$ 为 Toeplitz 交换子项，在 $\partial_E S\in\mathfrak S_2$ 且 $\int_{\mathcal I}|\partial_E S|_2\,dE<\infty$ 的假设下满足 $R_{\rm T}\le C_{\rm T}\,\ell^{-1/2}\!\int_{\mathcal I}|\partial_E S|_2\,dE$；
$\bullet$ **区间外尾项**：

$$R_{\rm tail}(\ell,\mathcal I,E_0):=\int_{\mathbb R\setminus\mathcal I(\gamma)} |h_\ell(E-E_0)|\,dE\in[0,1].$$

*附注*：若 $h\ge0$ 且 $\int_{\mathbb R} h=1$，则 $R_{\rm tail}=1-\int_{\mathcal I(\gamma)} h_\ell(E-E_0)\,dE$。

**注**：对分段光滑紧支撑窗（如 Kaiser），上述 $R_{\rm EM}$ 的 $C_m\,\ell^{-(m-1)}$ 应以角点估计替换（例如 $O(\ell^{-1})$），其余三项 $R_{\rm P},R_{\rm T},R_{\rm tail}$ 不变。由上述衰减阶，$\displaystyle R_{\rm P}\le C_h\sum_{|q|\ge1}\big|\widehat h\left(2\pi q\,\ell/\Delta\right)\big|$ **有限**，并与角点估计保持同阶。
[**窗化分布等式＋显式门槛；域：幺正散射，$h\in C_c^\infty$ 或 $h\in\mathcal S$**]

**引理 T（Toeplitz／Berezin 压缩误差）** 令 $\mathsf T_\ell$ 为能量轴上的窗化压缩算子（核为 $h_\ell(E-E')$ 的卷积），令 $Q(E)=-\mathrm i\,S(E)^\dagger\partial_E S(E)$，且 $\partial_E S\in\mathfrak S_2$ 并满足 $\int_{\mathcal I}|\partial_E S|_2\,dE<\infty$。则存在常数 $C_T>0$ 使

$$
\Big\lvert\operatorname{tr}\big(Q*h_\ell\big)-\int Q(E)\,h_\ell(E-E_0)\,dE\Big\rvert
\le C_T\,\ell^{-1/2}\!\int_{\mathcal I}|\partial_E S|_2\,dE .
$$

证明要点：将压缩误差写成 $[\mathsf T_\ell,\cdot]$ 的交换子，对能量导数做一次平均值估计；用 Hilbert–Schmidt–trace Hölder 与窗扩展尺度 $\int (E-E_0)^2 h_\ell\sim\ell^{-1}$ 得到 $\ell^{-1/2}$ 衰减。

**引理 P（Poisson／EM 的窗条件）** 若 $h\in C_c^{2m+1}$ 且端点 $\le 2m$ 阶喷气为零，则 $\widehat h(\omega)=O(|\omega|^{-(2m+1)})$，故

$$
\sum_{|q|\ge1}\Bigl\lvert\widehat h\!\left(\tfrac{2\pi q\,\ell}{\Delta}\right)\Bigr\rvert<\infty,
\qquad \int|R_{\rm EM}|\le C_m\,\ell^{-(m-1)} .
$$

对分段 $C^{2m}$ 且端点角点的紧支撑窗，用角点估计替代 $R_{\rm EM}$ 的阶，并保持 Poisson 级数收敛。

**引理 G（窗化相位扰动）**
若两组散射 $S,\tilde S$ 在能区 $\mathcal I$ 上满足

$$
\int_{\mathcal I}\!\Big(|S-\tilde S|_2\,|\partial_E S|_2+|\partial_E S-\partial_E\tilde S|_1\Big)\,dE\ \le\ \eta ,
$$

则

$$
\big|\Theta_h[S]-\Theta_h[\tilde S]\big|\ \le\ C_h\,\eta ,
\quad C_h=\sup_E\int |h_\ell(E-E')|\,dE' .
$$

**推论 G（弱非幺正稳定）** 定义 $\Delta_{\rm nonU}(E)=|S^\dagger S-\mathbb I|_1$。令 $\delta_{\rm gap}(\gamma):=\operatorname{dist}\big(\Theta_{\rm geom}(\gamma),\pi\mathbb Z\big)$。若

$$
\int_{\mathcal I(\gamma)} \Delta_{\rm nonU}(E)\,dE\ \le\ \varepsilon,\qquad
\mathcal E_h(\gamma)\ \le\ \delta_*(\gamma):=\min\big\{\tfrac{\pi}{2},\delta_{\rm gap}(\gamma)\big\}-\varepsilon,
$$

其中 $\varepsilon\in(0,\delta_{\rm gap}(\gamma))$，$\mathcal E_h(\gamma):=\int_{\mathcal I(\gamma)} |R_{\rm EM}|\,dE + \int_{\mathcal I(\gamma)} |R_{\rm P}|\,dE + C_{\rm T}\,\ell^{-1/2}\!\int_{\mathcal I(\gamma)}\!|\partial_E S|_2\,dE + R_{\rm tail}(\ell,\mathcal I,E_0)$，则 $\nu_{\rm chain}(\gamma)=(-1)^{\lfloor \Theta_h(\gamma)/\pi\rfloor}$ 不变，且与无窗极限 $(-1)^{\lfloor \Theta_{\rm geom}(\gamma)/\pi\rfloor}$ 一致。

（其中门槛与定理 G 完全对齐。）
[**稳定性；域：弱耗散**]

**引理 N（弱非幺正相位差界）** 写 $S=U(\mathbb I-A)$ 的极分解，$U$ 幺正、$A\ge0$。若 $\int_{\mathcal I}\!|S^\dagger S-\mathbb I|_1\,dE\le\varepsilon$，则存在常数 $C_N$ 使

$$
\Big|\int_{\mathcal I}\!\operatorname{tr}Q(S)\,h_\ell-\int_{\mathcal I}\!\operatorname{tr}Q(U)\,h_\ell\Big|\ \le\ C_N\,\varepsilon .
$$

证明要点：$Q(S)=\!\operatorname{Im}\,\operatorname{tr}(S^{-1}\partial_E S)$，对近幺正的 $S$ 有 $\|S^{-1}\|\le (1-\|A\|)^{-1}$；用 $\|\partial_E S\|_1\le\|\partial_E U\|_1+\|\partial_E A\|_1$ 与 $\|A\|_1\lesssim\|S^\dagger S-\mathbb I\|_1$ 控制差值并积分。

### 3.6  关节项与 $\mathbb Z_2$ 账本

**定理 H（账本一致与规范变换）** 在 null–null 与 null–spacelike 角点，

$$I_{\rm joint}=\frac{\varepsilon_J}{8\pi G}\int\sqrt{\gamma}\,\Xi\,d^{d-2}x,$$

其中

$$\Xi=\ln\frac{|k_1\cdot k_2|}{2}$$
（null–null）或 $\Xi=\ln|n\cdot k|$（null–spacelike）。

对独立缩放 $k_i\to \alpha_i k_i$、$n\to\beta n$ 有

$$\Xi\mapsto \Xi+\ln|\alpha_1\alpha_2|$$

（null–null），

$$\Xi\mapsto \Xi+\ln|\alpha|+\ln|\beta|$$

（null–spacelike）。

仅当法向翻转 $k\to -k$（或 $n\to -n$）时，$\varepsilon_J$ 变号而 $\Xi$ 不变。故单角点的 $I_{\rm joint}$ 非纯符号不变；但沿链闭合并以平方根粘接类 $\epsilon_i$ 记账后，净效应仅依赖 $\prod_i\epsilon_i$ 的奇偶，且与 $\lfloor\Theta_h/\pi\rfloor$ 的奇偶一致。
[**规范变换；域：仿射参数化的 null 边界**]

**引理 H.1（闭合链的角项奇偶对齐）** 设链的每一关节取同一仿射规范并按上式记账。沿闭路的角参数变分之和为 $2\pi$ 的整数倍，其半相位奇偶由穿越 $\Xi=(2k+1)\pi$ 的次数决定。由此 $\sum I_{\rm joint}/(8\pi G)$ 的奇偶与 $\lfloor\Theta_h/\pi\rfloor$ 一致。

**算例（$2+1$ 维）**
两片共线生成的 null 片与一片 spacelike 折面围成角结构；在规范 $k\cdot l=-1$ 下计算外挠曲率号差与角参数，验证符号与 $\epsilon_i$ 一致。

### 3.7  JLMS 提升与次阶估计

**定理 I（全息提升与扰动半径）**
在大 $N$ 领先阶，边界容斥与马尔可夫拼接提升为纠缠楔的法向模流拼接。次阶偏差分解为
$\bullet$ 极值面位移 $\delta X$ 对模流的贡献（规模 $\propto G_N^{-1}|\delta X|^2$ 的无量纲组配）；
$\bullet$ 体区互信息 $I_{\rm bulk}$；
$\bullet$ 体区模哈密顿量涨落 $\mathrm{Var}(K_{\rm bulk})$。
设

$$
\delta_{\rm holo}:=c_1\,|\delta X|^2+c_2\,I_{\rm bulk}+c_3\,\sqrt{\mathrm{Var}(K_{\rm bulk})},
$$

若 $\delta_{\rm holo}\le \tfrac{\pi}{2}-\varepsilon$，则与定理 G 的门槛拼合，奇偶不变。
[**半经典阶；域：AdS/CFT**]

**假设 J（半经典可控窗化）** 取足够平滑的窗 $h$ 与足够大的 $\ell$ 使边界侧的 $R_{\rm EM},R_{\rm P},R_{\rm tail}$ 满足定理 G 的门槛，同时 $\delta X,I_{\rm bulk},\mathrm{Var}(K_{\rm bulk})$ 由 $1/N$ 与耦合窗口的微扰展开统一控制。则边界—体区的二阶误差可与 $\mathcal E_h$ 合并到同一 $\delta_*$ 预算内，实现全息奇偶一致性。

---

## 4  Proofs

本节给出主要结果的证明概要。详细技术细节见附录 A–K。

### 4.1  双层几何分解与全序近似桥接

**引理 A 的证明**：沿每条 null 生成元 $\gamma_{x_\perp}^\pm$ 构造单调函数族 $V_\alpha^\pm(x_\perp)\downarrow V^\pm(x_\perp)$，使对应的半空间近似域 $R_{V_\alpha}^\pm$ 内外逼近因果钻石 $D$。令 $g^{(\alpha)}_\sigma$ 为对应权函数。由假设 A′ 给出的支配函数与单调逼近，结合主控收敛与二次型闭性，极限

$$\lim_{\alpha\to\infty}\sum_{\sigma=\pm}2\pi\!\int g^{(\alpha)}_\sigma\langle\psi,T_{\sigma\sigma}\psi\rangle$$

与有序逼近的选取无关。

**定理 A 的证明**：半空间与球形区（及其共形像）的模哈密顿量分解为已知结果。对一般因果钻石，由引理 A 的全序近似桥接，通过单调半空间族的极限构造完成分解。

### 4.2  容斥恒等式与闭性

**定理 B 的证明**：对固定横向坐标 $x_\perp$，先以 $\mathbf 1_{[a,\infty)}^\eta:=\rho_\eta*\mathbf 1_{[a,\infty)}$ 平滑指示函数并证明

$$\mathbf 1_{[\min_i V_i(x_\perp),\infty)}^\eta(v)=\sum_{k\ge1}(-1)^{k-1}\sum_{|I|=k}\mathbf 1_{[\max_{i\in I}V_i(x_\perp),\infty)}^\eta(v);$$

再对 $v$ 积分得到 $(v-\min_i V_i)_+^\eta=\sum_{k\ge1}(-1)^{k-1}\sum_{|I|=k}(v-\max_{i\in I}V_i)_+^\eta$，

其中 $(x)_+^\eta:=\displaystyle\int_{-\infty}^{x}\mathbf 1_{[0,\infty)}^\eta(t)\,dt$（等价地 $(x)_+^\eta=\rho_\eta*(x)_+$）。令 $\eta\to0^+$，由主控收敛定理与 Fubini–Tonelli 定理交换极限与积分，乘以 $2\pi T_{vv}$ 并积分得到二次型容斥恒等式。

**命题 B 的证明**：取 $c>-a$。设 $\psi_n\to\psi$ 于移位图范数 $|\cdot|_{\mathfrak k,c}$，且 $\psi_n,\psi\in \mathcal D\left(\mathfrak k_{\cup_i R_{V_i}}\right)\cap\bigcap_{I\ne\emptyset}\mathcal D\left(\mathfrak k_{R_{V_I}}\right)$，则容斥恒等式两侧对 $\psi_n$ 的二次型值同收敛至对 $\psi$ 的值。闭性来自**下半界闭二次型的移位图范数完备性**：以

$$|\psi|_{\mathfrak k,c}^2:=|\psi|^2+\big(\mathfrak k[\psi]+c|\psi|^2\big)$$

定义图范数，使形式域完备；配合二次型下半连续性与 Fatou 型论证，容斥恒等式两侧对 $\psi_n\to\psi$ 同收敛，故恒等式在上述形式域上闭合。

### 4.3  马尔可夫拼接与 Petz 恢复

**定理 C 的证明**：在同面全序切割下，容斥恒等式与相对熵恒等式联立，得到三段马尔可夫律

$$I(D_{j-1}:D_{j+1}\mid D_j)=0.$$

**命题 C.2（相对熵的下半连续与数据处理）** 对任意 CPTP 映射 $\Phi$ 与态对 $(\rho,\sigma)$，有

$$S(\rho\Vert\sigma)\ge S(\Phi\rho\Vert\Phi\sigma)\quad\text{且}\quad S\ \text{对弱* 收敛下半连续}.$$

设有单调近似 $R_{V_\alpha}\uparrow R_V$，令 $\Phi_\alpha$ 为对 $R_{V_\alpha}$ 的限制通道，$\Phi$ 为对 $R_V$ 的限制通道；则

$$\liminf_{\alpha\to\infty} I_{\alpha}(A:C\mid B)\ge I(A:C\mid B),$$

其中 $I_\alpha$ 按 $R_{V_\alpha}$ 计算的条件互信息。配合容斥极限与引理 A 可把三段马尔可夫律稳定传递到一般钻石的极限。

对应的模哈密顿量恒等式由容斥与模流几何化直接推得。

**定理 C′ 的证明**：非全序切割时，以相对熵密度核定义马尔可夫缺口线密度 $\iota(v,x_\perp)\ge0$。通过层状度 $\kappa(x_\perp)$ 与 $\iota$ 的单调性比较，得到缺口积分表示与上下界估计。

**定理 D 的证明**：记 $A=D_{j-1}$，$B=D_j$，$C=D_{j+1}$。取忘却通道

$$\Phi_{BC\to B}(X_{BC})=\operatorname{Tr}_C[X_{BC}],\qquad \Phi^*(Y_B)=Y_B\otimes\mathbb I_C,$$

参考态取 $\sigma_{BC}=\rho_{BC}$（$\sigma_B=\rho_B$）。则 Petz 恢复映射

$$\mathcal R_{B\to BC}(X_B)=\sigma_{BC}^{1/2}\big(\sigma_B^{-1/2}X_B\,\sigma_B^{-1/2}\otimes\mathbb I_C\big)\sigma_{BC}^{1/2},$$

逆在 $\mathrm{supp}(\sigma_B)$ 上取伪逆。完美恢复当且仅当 $I(A:C\mid B)=0$ 且

$$(\mathrm{id}_A\otimes\mathcal R_{B\to BC})(\rho_{AB})=\rho_{ABC}.$$

存在旋转平均 $\mathcal R^{\rm rot}_{B\to BC}$ 使

$$I(A:C\mid B)\ \ge\ -2\ln F\left(\rho_{ABC},\ (\mathrm{id}_A\otimes \mathcal R^{\rm rot}_{B\to BC})(\rho_{AB})\right).$$

上述不等式对未旋转的 $\mathcal R_{B\to BC}$ 一般不保证成立；本文统一采用 $\mathcal R^{\rm rot}_{B\to BC}$ 处理稳定性命题。

### 4.4  半侧模包含与链式推进

**定理 E 的证明**：半侧模包含（HSMI）的定义与 Wiesbrock–Borchers 结构定理给出与模群 $\Delta_{\mathcal A(D_{j+1})}^{\mathrm i t}$ 协变的正能量一参数半群，该半群将 $\mathcal A(D_j)$ 内禀推进至 $\mathcal A(D_{j+1})$。

### 4.5  分布论散射刻度与窗化奇偶阈值

**定理 F 的证明**：Birman–Kreĭn 恒等式与 Friedel–Lloyd—Wigner–Smith 等式的分布论版本在测试函数 $h\in C_c^\infty(\mathbb R)$ 下成立：

$$\int \partial_E\arg\det S(E)\,h(E)\,dE = -2\pi\int \xi'(E)\,h(E)\,dE,$$

并与 $\operatorname{tr}Q=\partial_E\arg\det S$ 联立。其中 $\xi$ 为谱移函数。能带阈值与嵌入本征态通过选择 $\operatorname{supp}h$ 回避，或经可去奇点处理。

**定理 G 的证明**：通过 Toeplitz／Berezin 迹公式与交换子半经典估计，将窗化误差 $\mathcal R_h$ 分离为三项：

$$\mathcal R_h = R_{\rm EM} + R_{\rm P} + R_{\rm T}.$$

Euler–Maclaurin 公式给出端点余项 $R_{\rm EM}$ 的 $O(\ell^{-(m-1)})$ 衰减；Poisson 求和公式给出混叠项的普适上界

$$\int_{\mathcal I}|R_{\rm P}|\ \le\ C_h\sum_{|q|\ge1}\big|\widehat h\left(2\pi q\,\ell/\Delta\right)\big| .$$

**若取高斯窗**，由于 $\widehat h$ 的高斯尾，上式呈**指数平方**衰减；**若取 Kaiser–Bessel 或紧支撑 $C^\infty$ 窗**，由其已知傅里叶尾界得到**指数或超多项式**衰减。此与定理 G 及 §6.1 的门槛与参数条件完全一致。Toeplitz 交换子估计给出 $R_{\rm T}$ 的 $O(\ell^{-1/2})$ 界。**对无限支撑窗（如高斯）**，区间外尾部质量

$$R_{\rm tail}(\ell,\mathcal I,E_0):=\int_{\mathbb R\setminus\mathcal I(\gamma)} |h_\ell(E-E_0)|\,dE$$

并入总误差预算；**对紧支撑窗（如 Kaiser–Bessel 或其它 $C^\infty$ 窗）**，若 $\operatorname{supp}h_\ell\subset\mathcal I(\gamma)$ 则 $R_{\rm tail}=0$。若进一步假设 $h\ge0$，则上式与 $1-\int_{\mathcal I(\gamma)}h_\ell(E-E_0)\,dE$ 等价。四项之和满足门槛不等式时，奇偶阈值稳定。

**引理 G 的证明**：利用分解

$$S^\dagger \partial_E S-\tilde S^\dagger \partial_E \tilde S = (S^\dagger-\tilde S^\dagger)\partial_E S+\tilde S^\dagger(\partial_E S-\partial_E\tilde S),$$

取迹范数并在能带上积分，得到相位扰动上界 $|\Theta_h[S]-\Theta_h[\tilde S]|\le C_h\eta$。

**推论 G 的证明**：在增广空间中将非幺正散射 $S$ 幺正化，以非幺正偏差 $\Delta_{\rm nonU}(E)=|S^\dagger S-\mathbb I|_1$ 的能量积分与门槛不等式拼合，得到弱非幺正扰动下的稳定性。

### 4.6  关节项与 $\mathbb Z_2$ 账本一致性

**定理 H 的证明**：GHY 关节项中，对独立缩放 $k_i\to \alpha_i k_i$、$n\to\beta n$，$\Xi$ 变换为 $\Xi+\ln|\alpha_1\alpha_2|$（null–null）或 $\Xi+\ln|\alpha|+\ln|\beta|$（null–spacelike）。仅当法向翻转 $k\to -k$（或 $n\to -n$）时，$\varepsilon_J$ 变号而 $\Xi$ 不变。故单角点的 $I_{\rm joint}$ 非纯符号不变；但沿链闭合并以平方根粘接类 $\epsilon_i$ 记账后，净效应仅依赖 $\prod_i\epsilon_i$ 的奇偶，且与 $\lfloor\Theta_h/\pi\rfloor$ 的奇偶一致。

### 4.7  全息提升与次阶估计

**定理 I 的证明**：由 JLMS 等式，边界容斥与马尔可夫拼接在大 $N$ 领先阶提升为纠缠楔的法向模流拼接。次阶偏差分解为三项：
- 极值面位移 $\delta X$ 对模流的贡献（规模 $\propto G_N^{-1}|\delta X|^2$）；
- 体区互信息 $I_{\rm bulk}$；
- 体区模哈密顿量涨落 $\mathrm{Var}(K_{\rm bulk})$。

通过量纲分析与半经典展开，得到扰动半径 $\delta_{\rm holo}$ 的上界估计。

---

## 5  Model Apply

### 5.1  QNEC 链式加强

二阶响应核与定理 B 的容斥结合，得联合区域能量—熵变分的容斥下界；在全序下该下界取等，等价于马尔可夫饱和。

### 5.2  纠缠楔拼接与角点荷

边界容斥／马尔可夫在体区对应极值面的法向模流拼接与角点荷可加性；在弱回馈与光滑角点条件下，账本一致性维持。

### 5.3  奇偶门槛的工程读数

以窗化 $\rho_{\rm rel}$ 的能带积分估计 $\Theta_h(\gamma)$；当 $\Theta_h$ 跨越 $\pi$ 时输出二值翻转；以可编程接缝设置 $\epsilon_i$ 验证与关节项取向符号一致。

---

## 6  Engineering Proposals（可操作参数）

### 6.1  推荐窗与采样门槛（满足 $\delta_*(\gamma)=\min\{\pi/2,\ \delta_{\rm gap}(\gamma)\}-\varepsilon$）

* **窗族**：高斯窗或 Kaiser 窗（$\beta\ge6$），$h_\ell(E)=\ell^{-1}h(E/\ell)$。

**注**：Kaiser–Bessel 属于紧支撑的分段 $C^{2m}$ 窗，端点为角点；其 Euler–Maclaurin 端点余项按 §3.5 的角点版 $R_{\rm EM}$ 计入总误差预算 $\mathcal E_h(\gamma)$。

* **平滑阶／EM 端点余项**：若 $h\in C_c^\infty$ 或 $h\in\mathcal S$（如高斯），取 $m\ge 6$ 并用 $\int_{\mathcal I}|R_{\rm EM}|\le C_m\,\ell^{-(m-1)}$；若用 **Kaiser** 窗，则按角点估计采用 $\int_{\mathcal I}|R_{\rm EM}|\le C_{\rm KB}\,\ell^{-1}$ 计入误差预算。
* **步长与带宽**：取 $\Delta\le \ell/4$，并使 $2\pi\ell/\Delta$ 足够大。Poisson 混叠采用与正文一致的一般式

  $$R_{\rm P}\ \le\ C_h\sum_{|q|\ge1}\big|\widehat h\left(2\pi q\,\ell/\Delta\right)\big|.$$

  **若取高斯窗**，则上式和 $\widehat h$ 的高斯尾给出**指数平方**衰减的具体界（随 $2\pi\ell/\Delta$ 快速下降）；

  **若取 Kaiser–Bessel 或一般紧支撑 $C^\infty$ 窗**，使用该窗已知的傅里叶尾界给出**指数或超多项式**衰减，不再套用高斯专属的 $e^{-c(2\pi\ell/\Delta)^2}$ 形式。
* **Toeplitz 交换子项**：控制量 $\ell^{-1/2}\int_{\mathcal I}|\partial_E S|_2$。
* **非幺正容限**：若 $\int_{\mathcal I}\Delta_{\rm nonU}\le \varepsilon$，则门槛合格。
* **Gap 预检**：计算 $\delta_{\rm gap}(\gamma)=\operatorname{dist}(\Theta_{\rm geom}(\gamma),\pi\mathbb Z)$。
* **误差预算**：

$$\int|R_{\rm EM}|+\int|R_{\rm P}|+C_{\rm T}\,\ell^{-1/2}\!\int|\partial_E S|_2+R_{\rm tail}\ \le\ \delta_*(\gamma)=\min\big\{\tfrac{\pi}{2},\delta_{\rm gap}(\gamma)\big\}-\varepsilon,$$

其中 $R_{\rm tail}(\ell,\mathcal I,E_0):=\int_{\mathbb R\setminus\mathcal I(\gamma)} |h_\ell(E-E_0)|\,dE$。

（其他数值参数与窗族建议保持不变。）

### 6.2  最小数值与实验管线

* **单道共振**：$\delta(E)=\arctan\frac{\Gamma}{E-E_0}$。估计 $\Theta_h$ 与实际 $\int (2\pi)^{-1}\operatorname{tr}Q$ 的差并标注跨越 $\pi$ 的翻转点。
* **多道近幺正**：$S(E)=U\operatorname{diag}(e^{2i\delta_1(E)},e^{-2i\delta_1(E)})U^\dagger$。考察 $\epsilon_i$ 翻转与链式符号响应。
* **容斥验证**：二维 CFT 三块链，数值评估 $K_{12}+K_{23}-K_2-K_{123}$ 与 $I(1:3|2)$ 的一致性并绘制误差条。

---

## 7  Discussion（边界、反例与扩展）

* **局域化边界**：缺失 QNEC 真空饱和、边界非光滑或曲率过强时，定理 A 的二次型分解可能失效。
* **非全序切割**：层状度 $\kappa$ 非零时产生正的马尔可夫缺口；可采用层状子族分解或沿生成元的排序重组缓解。
* **散射刻度**：长程势与阈值奇点需改用广义 KFL 或平均化谱移；强吸收或大量外耦合则以增广空间幺正化处理并依门槛不等式判定奇偶可控性。
* **全息修正**：次阶 $1/N$ 与 $G_N$ 修正进入 $\delta_{\rm holo}$；当其未跨越 $\pi/2$ 门槛时，奇偶保持。

---

## 8  Conclusion

确立 Null–Modular 双覆盖的二次型局域化与一般钻石的全序近似桥接；在重叠钻石链上给出容斥恒等式与马尔可夫拼接，并以线密度核刻画非全序缺口。采用分布论 KFL—WS 刻度与 Toeplitz／Berezin＋EM／Poisson 误差纪律，得到带常数的窗化奇偶阈值门槛与对弱非幺正的鲁棒性。几何侧以 HSMI 提供代数推进，GHY 关节项与平方根粘接的 $\mathbb Z_2$ 账本一致性在 $1+1$、$2+1$ 维算例中得到印证；全息侧以 JLMS 完成体区提升并给出次阶扰动半径。配套的参数表与核查清单支撑数值与实验复现。

---

## Acknowledgements, Code Availability

全序近似桥接、容斥重建、Petz 拼接与窗化群延迟的脚本可按附录 J 的参数门槛复现；包含窗化卷积、中心差分估计 $\operatorname{tr}Q$、EM 端点修正、Poisson 混叠估计与 Toeplitz 交换子误差评估。

---

## References

Bisognano, Wichmann；Borchers；Wiesbrock；Mund；Faulkner–Leigh–Parrikar–Wang；
Koeller–Leichenauer–Levine–Shahbazi‑Moghaddam；Casini–Testé–Torroba；
Jafferis–Lewkowycz–Maldacena–Suh；Lehner–Myers–Poisson–Sorkin；Jubb–Samuel–Sorkin–Surya；
Wigner；Smith；Birman–Kreĭn；Friedel–Lloyd；
Ma–Marinescu；Schlichenmaier；Borthwick–Paul–Uribe；
Trefethen–Weideman；Javed–Trefethen；Chandrasekaran–Prabhu；Pulakkat。

---

## 附录

### 附录 A：二次型框架与闭性（形式化）

**假设 A（二次型框架）**
存在稠密域 $\mathcal D_0\subset\mathcal H$ 与闭二次型 $\mathfrak k_R$ 使
$\mathfrak k_R[\psi]=\sum_{\sigma=\pm}\!\int g_\sigma^{(R)}\langle\psi,T_{\sigma\sigma}\psi\rangle$
对 $\psi\in\mathcal D_0$ 良定义且下半界；则存在自伴 $K_R$ 满足 $\langle\psi,K_R\psi\rangle=\mathfrak k_R[\psi]$。

**假设 A′（null 能流一致可积）** 对任意 $\psi\in\mathcal D_0$ 与几何上有界的单调近似族 $\{R_{V_\alpha}^\pm\}$，存在 $H_\sigma\in L^1_{\mathrm{loc}}(E^\sigma\times\mathbb R^{d-2})$ 使

$$\big|g^{(\alpha)}_\sigma(\lambda,x_\perp)\,\langle\psi,T_{\sigma\sigma}(\lambda,x_\perp)\psi\rangle\big|
\le H_\sigma(\lambda,x_\perp)$$

几乎处处成立，且 $\sup_\alpha\int_{\mathcal K} H_\sigma<\infty$ 对任意紧集 $\mathcal K\subset E^\sigma\times\mathbb R^{d-2}$。

### 附录 B：有序切割近似（引理 A 证明）

沿每条生成元 $\gamma_{x_\perp}^\pm$ 构造单调函数族 $V_\alpha^\pm(x_\perp)\downarrow V^\pm(x_\perp)$，令 $R_{V_\alpha}^\pm$ 为半空间近似域并取权 $g^{(\alpha)}_\sigma$。二阶响应核 $2\pi\,T_{vv}$ 与主控收敛给出
$\langle\psi,K_{R_{V_\alpha}^\pm}\psi\rangle\to2\pi\!\int g_\sigma\langle\psi,T_{\sigma\sigma}\psi\rangle$。
由闭性与夹逼，极限与近似路径无关。

### 附录 C：容斥的分布式正则化与交换

以指示函数的平滑近似 $\mathbf 1_{[a,\infty)}^\eta:=\rho_\eta*\mathbf 1_{[a,\infty)}$ 证明

$$\mathbf 1_{[\min_i V_i,\infty)}^\eta=\sum_{k\ge1}(-1)^{k-1}\sum_{|I|=k}\mathbf 1_{[\max_{i\in I}V_i,\infty)}^\eta;$$

再对 $v$ 积分得 $(v-\min_i V_i)_+^\eta=\sum_{k\ge1}(-1)^{k-1}\sum_{|I|=k}(v-\max_{i\in I}V_i)_+^\eta$，

其中 $(x)_+^\eta:=\displaystyle\int_{-\infty}^{x}\mathbf 1_{[0,\infty)}^\eta(t)\,dt$（或 $(x)_+^\eta=\rho_\eta*(x)_+$）。令 $\eta\to0^+$ 用主控收敛与 Fubini／Tonelli 完成极限交换并乘 $2\pi T_{vv}$ 积分得二次型容斥。

### 附录 D：Petz 的支撑与稳定性（统一版，自洽）

记 $A=D_{j-1}$，$B=D_j$，$C=D_{j+1}$。令

$$\Phi_{BC\to B}(X_{BC})=\operatorname{Tr}_C[X_{BC}],\qquad \Phi^*(Y_B)=Y_B\otimes\mathbb I_C,$$

参考态取 $\sigma_{BC}=\rho_{BC}$（$\sigma_B=\rho_B$）。则 Petz 恢复映射

$$\mathcal R_{B\to BC}(X_B)=\sigma_{BC}^{1/2}\big(\sigma_B^{-1/2}X_B\,\sigma_B^{-1/2}\otimes\mathbb I_C\big)\sigma_{BC}^{1/2},$$

逆在 $\mathrm{supp}(\sigma_B)$ 上取伪逆。完美恢复当且仅当 $I(A:C\mid B)=0$ 且

$$(\mathrm{id}_A\otimes\mathcal R_{B\to BC})(\rho_{AB})=\rho_{ABC}.$$

存在旋转平均 $\mathcal R^{\rm rot}_{B\to BC}$ 使

$$I(A:C\mid B)\ \ge\ -2\ln F\left(\rho_{ABC},\ (\mathrm{id}_A\otimes \mathcal R^{\rm rot}_{B\to BC})(\rho_{AB})\right).$$

本文后续稳定性命题均以 $\mathcal R^{\rm rot}_{B\to BC}$ 表述，避免与 $AB\to ABC$ 范式混用。

### 附录 E：分布论 KFL—WS 与测试函数空间

给出 $\partial_E\arg\det S=-2\pi \xi'$ 与 $(2\pi)^{-1}\operatorname{tr}Q=-\xi'$ 的分布等式在 $h\in C_c^\infty$（或 $\mathcal S$）下的证明；能带阈值与嵌入本征态通过选择 $\operatorname{supp}h$ 回避或以可去奇点处理；多道情形在能量壳上的有限维通道空间下迹与测试函数配对可交换。

### 附录 F：Toeplitz／Berezin 余项与 EM／Poisson 界

记

$$
\operatorname{tr}Q_h
=h*\operatorname{tr}(-\mathrm i S^\dagger\partial_E S)
+\mathcal R_h,\quad
\mathcal R_h=R_{\rm EM}+R_{\rm P}+R_{\rm T}.
$$

给出 $R_{\rm EM}\le C_m\,\ell^{-(m-1)}$、
$R_{\rm P}\ \le\ C_h\displaystyle\sum_{|q|\ge1}\big|\widehat h\left(2\pi q\,\ell/\Delta\right)\big|$、
$R_{\rm T}\le C_{\rm T}\ell^{-1/2}\int|\partial_E S|_2$ 的推导。

### 附录 G：窗化相位扰动引理（证明）

利用

$$
S^\dagger \partial_E S-\tilde S^\dagger \partial_E \tilde S
=(S^\dagger-\tilde S^\dagger)\partial_E S+\tilde S^\dagger(\partial_E S-\partial_E\tilde S),
$$

取迹范数并在能带上积分，得到
$|\Theta_h[S]-\Theta_h[\tilde S]|\le C_h\eta$。

### 附录 H：GHY 关节项的规范变换与 $2+1$ 维算例

对独立缩放 $k_i\to \alpha_i k_i$、$n\to\beta n$，$\Xi$ 变换为 $\Xi+\ln|\alpha_1\alpha_2|$（null–null）或 $\Xi+\ln|\alpha|+\ln|\beta|$（null–spacelike）。仅当法向翻转 $k\to -k$（或 $n\to -n$）时，$\varepsilon_J$ 变号而 $\Xi$ 不变。沿链闭合并以平方根粘接类 $\epsilon_i$ 记账后，净效应仅依赖 $\prod_i\epsilon_i$ 的奇偶。给出 $2+1$ 维 null–null–spacelike 折面的外挠曲率号差计算并验证与 $\epsilon_i$ 对齐。

### 附录 I：非全序切割的线密度核

以相对熵密度或二次型响应核定义 $\iota(v,x_\perp)$，证明
$\iota\ge0$ 且对 $\kappa$ 单调非降，并给出 $\kappa$ 有界时的上下界。

### 附录 J：可复现实验参数表与核查清单

**参数表**（满足定理 G 门槛；含 $\delta_{\rm gap}$ 预检）：

* 窗：高斯／Kaiser($\beta\ge6$)；$m\ge 6$；$\Delta\le \ell/4$；$2\pi\ell/\Delta\ge 5$。
* **误差预算**：$\int|R_{\rm EM}|+\int|R_{\rm P}|+C_{\rm T}\,\ell^{-1/2}\!\int|\partial_E S|_2+R_{\rm tail}\ \le\ \delta_*(\gamma)$，其中 $R_{\rm tail}(\ell,\mathcal I,E_0):=\int_{\mathbb R\setminus\mathcal I(\gamma)} |h_\ell(E-E_0)|\,dE$。
* 非幺正：$\int \Delta_{\rm nonU}\le \varepsilon$。
* **Gap 预检**：若 $\delta_{\rm gap}(\gamma)<\tfrac{\pi}{2}$，按上式以 $\delta_*(\gamma)$ 为门槛收紧 $\ell,\Delta$ 的取值。


### 附录 K：符号表

$D$：因果钻石；$E^\pm$：零测度两层；$\lambda$：仿射参数；$x_\perp$：横向坐标；
$K_R$：区域模哈密顿量；$\Delta^{\mathrm i t},J$：模群／模对合；
$\mathcal A(R)$：局域代数；$I(\cdot:\cdot\mid\cdot)$：条件互信息；
$S(E)$：散射矩阵；$Q=-\mathrm i S^\dagger\partial_E S$：群延迟；
$\xi$：谱移函数；$\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}Q$；
$\varphi=\tfrac12\arg\det S$（半相位，连续分支）；
$h_\ell$：窗；$\ell$：窗尺度；$\Delta$：采样步长；
$R_{\rm EM}$、$R_{\rm P}$、$R_{\rm T}$：三类误差；
$\epsilon_i$：平方根粘接类；$\varepsilon_J$：关节项取向符号；
$\kappa$：层状度；$\iota$：马尔可夫缺口线密度；
$\Delta_{\rm nonU}$：非幺正偏差；$\delta_{\rm holo}$：全息次阶扰动半径。
