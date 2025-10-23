# EBOC：永恒–静态块 观察-计算 统一理论

**作者**：Auric
**日期**：2025-10-18

---

## 摘要

**目标.** 提出 **EBOC（Eternal-Block Observer-Computing）**：一个无需显式全局时间的几何—信息统一框架，将**永恒图元胞自动机**（EG-CA）的**无时间因果编码**与**静态块宇宙元胞自动机**（SB-CA）的**程序语义与观察-译码**合并于同一形式系统，并给出可验证的信息律与构造算法。本文将静态块 $X_f$ 与永恒图边移位 $(Y_G,\sigma)$ 视为**等价双表述**；以下以 $X_f$ 为主叙述，但每条结论均可在 $(Y_G,\sigma)$ 上通过**图移位（可数状态Markov移位）展示/编码等价**重述；当满足T13的"时间可马尔可夫化"等假设时，可进一步得到sofic/有限型展示。

**三大支柱.**

1. **几何编码（Graph/SFT）**：宇宙作为满足局部规则 $f$ 的**静态块** $X_f\subset\Sigma^{\mathbb{Z}^{d+1}}$；其因果/一致性由**永恒图** $G=(V,E)$ 与 **子移位（SFT）** 并行刻画。
2. **语义涌现（Observation = Decoding）**：**观察=因子译码**。译码器 $\pi:\Sigma^{B}\to\Gamma$ 按**可接受叶分层逐叶读取**静态块（沿 $\tau$ 自层 $c$ 推进到 $c+b$ 的跨叶读取），输出可见语言；"语义塌缩"系从底层配置到可见记录的**信息因子化**。
3. **信息约束（不增律）**：观察不创造信息：
$$
K\big(\pi(x|_W)\big)\ \le\ K(x|_W)+K(\pi)+O(1),
$$
并在**因果厚边界**下给出**条件复杂度**上界与 Brudno 一致的熵极限。

**统一比喻（RPG 游戏）.** 宇宙如**无限剧情的 RPG**：**游戏数据与演化规则**早已写定（$(X_f,f)$），"选择"（表观自由意志）须与**剧情线**一致（决定论）。**逐叶读取**按既定节拍 $b$ 逐章解锁；"选择"是在兼容分支中**选代表**并**排除**不相容分支，本体"ROM"并未增减信息。

**核心对象.**
$$
\mathcal U=(X_f, G, \rho, \Sigma, f, \pi, \mu, \nu),
$$
其中 $X_f$ 为空间-时间 SFT，$G$ 为永恒图，$\rho$ 给出**可接受叶族**（原始整协向量 $\tau^\star$ 的水平集，$\langle\tau^\star,\tau\rangle=b\ge1$），$\pi$ 为译码器，$\mu$ 为移位不变遍历测度，$\nu$ 为通用半测度（仅作典型性权重）。等价地，可用 $G$ 的**边移位** $Y_G$ 及其**路径移位** $(Y_G,\sigma)$ 表达所有结果；观察/信息律对两表述同样成立。

---

## 1. 引言与动机

传统 CA 以全局时间迭代呈现"演化"；块/永恒图视角一次性给定整段时空，"演化"仅是**逐叶读取**得到的路径叙述。动态视角依赖时间背景、难以背景独立；静态视角缺乏观测语义。EBOC 以"**几何编码 × 语义译码 × 信息律**"统一二者：SFT/图结构保证一致性与构造性；因子映射提供可见语言；复杂度/熵刻画守恒与极限。本文在极简公理下建立 T1–T26 定理族，给出细化证明与可复现实验流程。

---

## 2. 符号与先备

### 2.1 空间、字母表与配置

* 空间 $L=\mathbb{Z}^{d}$，时空 $L\times\mathbb{Z}=\mathbb{Z}^{d+1}$；有限字母表 $\Sigma$。
* 时空配置 $x\in \Sigma^{\mathbb{Z}^{d+1}}$。窗口 $W\subset\mathbb{Z}^{d+1}$ 的限制 $x|_W$。
* 约定 $|\cdot|$ 既记字长亦记集合基数（由上下文判别）。

### 2.2 邻域与全局演化

* 有限邻域 $N\subset \mathbb{Z}^{d}$，局部规则 $f:\Sigma^{|N|}\to\Sigma$：
$$
x(\mathbf r+N,t)\coloneqq\big(x(\mathbf r+\mathbf n,t)\big)_{\mathbf n\in N}\in\Sigma^{|N|},\qquad
x(\mathbf r,t)=f\big(x(\mathbf r+N, t-1)\big).
$$
* **全局映射**
$$
F:\Sigma^{\mathbb{Z}^{d}}\to\Sigma^{\mathbb{Z}^{d}},\qquad (F(x))(\mathbf r)=f\big(x(\mathbf r+N)\big).
$$

### 2.3 SFT 与永恒图

* **空间-时间 SFT**
$$
X_f\ :=\ \Big\{x\in\Sigma^{\mathbb{Z}^{d+1}}:\ \forall(\mathbf r,t),\ x(\mathbf r,t)=f\big(x(\mathbf r+N,t-1)\big)\Big\}.
$$
* **永恒图** $G=(V,E)$：顶点 $V$ 编码局部图案（事件），边 $E$ 编码因果/一致关系。
* **边移位**
$$
Y_G=\Big\{(e_t)_{t\in\mathbb{Z}}\in E^{\mathbb{Z}}:\ \forall t,\ \mathrm{tail}(e_{t+1})=\mathrm{head}(e_t)\Big\}.
$$

### 2.4 叶状分解与逐叶读取协议

* **Unimodular 变换**：$U\in \mathrm{GL}_{d+1}(\mathbb{Z})$（整可逆，$\det U=\pm1$），时间方向 $\tau=Ue_{d+1}$。
* **可接受叶**：存在**原始整协向量** $\tau^\star\in(\mathbb{Z}^{d+1})^\vee$ 及常数 $c$，叶为其水平集
$$
\Big\{\ \xi\in\mathbb{Z}^{d+1}:\ \langle\tau^\star,\xi\rangle=c\ \Big\},
$$
并满足
$$
\langle\tau^\star, \tau\rangle=b\ge 1,
$$
以保证**跨叶的单调推进**。
* **逐叶读取**：采用块码 $\pi:\Sigma^B\to\Gamma$，按叶层 $c\mapsto c+b$ 逐叶推进，对相应窗口应用 $\pi$ 产出可见序列。
* **叶计数与时间片长方体族**：对时间片长方体族窗口 $W=R\times[t_0, t_0+T-1]$（$R\subset\mathbb{Z}^d$），定义 $L(W)=T$ 为时间厚度（穿越的叶层数）。在步长 $b$ 的协议下，**观察步数**为 $\lfloor L(W)/b\rfloor$；边界效应 $O(1)$ 对熵/复杂度密度极限无影响。此类窗口族与时间子作用 $\sigma_{\mathrm{time}}$ 的一维Følner理论相容。
* **时间子作用记号**：记 $\sigma_{\mathrm{time}}$ 为 $X_f$ 沿时间坐标的**一维子作用**，$\sigma_\Omega$ 为 $\Omega(F)$ 的时间移位。

### 2.5 复杂度与测度

* 采用**前缀** Kolmogorov 复杂度 $K(\cdot)$ 与条件复杂度 $K(u|v)$。
* $\mu$：对**时间子作用** $\sigma_{\mathrm{time}}$ 不变且遍历（除非另行注明）；$\nu$：通用半测度（算法概率）。
* **窗口描述复杂度**：$K(W)$ 为生成 $W$ 的最短程序长度；Følner 族 $\{W_k\}$ 满足 $|\partial W_k|/|W_k|\to 0$。
* **熵符号约定**：本文区分两类熵：$h_\mu(\sigma_{\mathrm{time}})$（与叶计数 $L(W)$ 归一化相容）与 $h_\mu^{(d+1)}$（与体素数 $|W|$ 归一化相容）。二者一般无固定换算关系；本文各处结论均在各自相容的归一化下陈述与证明，不进行跨归一化换算。进一步地，对任意有限空间截面 $R\subset\mathbb Z^d$，记**时间子作用的观测分割**为
  $$
  \alpha_R\ :=\ \big\{\, [p]_{R\times\{0\}}\ :\ p\in\Sigma^{R}\,\big\},
  $$
  定义相对熵 $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$；并以 Kolmogorov–Sinai 定义
  $$
  h_\mu(\sigma_{\mathrm{time}}):=\sup_{R\text{ 有限}}\ h_\mu(\sigma_{\mathrm{time}},\alpha_R).
  $$
  对观察因子 $\pi$，相应观测分割记作
  $$
  \alpha_R^\pi\ :=\ \big\{\, [q]_{R\times\{0\}}^\pi\ :\ q\in \pi(\Sigma^{B})^{R}\,\big\},
  $$
  其中 $[q]_{R\times\{0\}}^\pi$ 表示在 $R\times\{0\}$ 施加 $\pi$ 的块读取得到可见图案 $q$ 的柱集。

### 2.6 因果厚边界（用于 T4）

* 明确采用 $\infty$-范数：
$$
r\ :=\ \max_{\mathbf n\in N}\ |\mathbf n|_{\infty}.
$$
* 定义
$$
t_-=\min\Big\{t:(\mathbf r,t)\in W\Big\},\quad
t_+=\max\Big\{t:(\mathbf r,t)\in W\Big\},\quad
T=t_+-t_-+1.
$$
* 底层 $\mathrm{base}(W)=\Big\{(\mathbf r,t_-)\in W\Big\}$。
* **底层过去因果输入边界（标准坐标）**
$$
\partial_{\downarrow}^{(r,T)}W^-\ :=\ \Big\{(\mathbf r+\mathbf n,\ t_--1)\ :\ (\mathbf r,t_-)\in\mathrm{base}(W),\ \mathbf n\in[-rT,\,rT]^d\cap\mathbb{Z}^d\Big\}.
$$
约定：本节及后续 T4 中的 $T$ 皆指穿越的时间层数（与 §2.4 的 $L(W)$ 一致）。
非标准叶情形先用 $U^{-1}$ 回到标准坐标后取像。

### 2.7 永恒图的坐标相对化（Anchored Chart）

$G$ 不携带全局坐标。选锚 $v_0$，相对嵌入 $\varphi_{v_0}:\mathrm{Ball}_G(v_0,R_0)\to\mathbb{Z}^{d+1}$ 满足 $\varphi_{v_0}(v_0)=(\mathbf 0,0)$，沿 $\tau$ 的路径层函数单调不减，空间邻接为有限移位。事先固定按"局部图案 $\to$ 顶点"的最小展示半径 $R_0$，以下相关定义与构造一律采用该固定 $R_0$。
层函数
$$
\ell(w):=\langle\tau^\star,\ \varphi_{v_0}(w)\rangle,\qquad
\mathrm{Cone}^+_{\ell}(v):=\Big\{w\in \mathrm{Dom}(\varphi_{v_0})\ :\ \exists\ v\leadsto w\ \text{且 }\ell\ \text{沿途单调不减}\Big\}.
$$
**SBU（静态块展开）**
$$
X_f^{(v,\tau)}:=\Big\{x\in X_f:\ x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R_0))}=\mathrm{pat}(v)\ \text{且}\ x\ \text{在}\ \varphi_{v_0}\!\big(\mathrm{Cone}^+_\ell(v)\big)\ \text{上为该锚的一致扩张}\Big\},
$$
其中"一致扩张"指：在该锥内所有由 $v$ 与局部规则强制得到的单元与 $x$ 匹配。此处"**强制**"指：仅凭锚 $v$ 在所给锥域内经**有限步局部约束闭包**后**唯一决定**的格点取值；SBU 仅要求与这些唯一定值匹配。

### 2.8 永恒图—SFT 的双表述（工作准则）

- 双表示：本文所有以静态块 $X_f$ 叙述的结论，均存在以永恒图边移位 $(Y_G,\sigma)$ 的等价版本；二者通过**图移位（可数状态Markov移位）展示/编码**互相给出；当满足T13的"时间可马尔可夫化"等假设时，可进一步得到sofic/有限型展示。为简洁起见，正文以 $X_f$ 为主，必要处以"（EG）"括注路径版表述。
- 对应关系：窗口 $W$ 与厚边界对应于有限路径段与有限邻接半径；逐叶读取对应于沿路径的时间移位读取；观察因子 $\pi$ 在 $X_f$ 上的定义可在 $Y_G$ 上通过路径块码 $\pi_G$ 等价实现。若为**一般** $X_f$，$Y_G$ 可取**可数状态**图，使窗口依赖以有限邻接半径表达；当满足T13的有限记忆条件时，$Y_G$ 可收束为sofic/SFT。


> 下文仅在**存在该相对嵌入的图域**上讨论 SBU。

**定义·可实现事件.** 设永恒图 $G=(V,E)$。称 $v\in V$ **可实现**，若存在 $x\in X_f$ 与某相对嵌入 $\varphi_{v_0}$ 及半径 $R_0$ 使得 $x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R_0))}$ 与 $v$ 的局部图案一致（按文中"局部图案→顶点"的编码约定）。

---

## 3. 极简公理（A0–A3）

**A0（静态块）** $X_f$ 为局部约束的模型集合。
**A1（因果-局域）** $f$ 邻域有限；读取采用可接受叶。
**A2（观察=因子译码）** 逐叶读取并施加 $\pi$ 得 $\mathcal O_{\pi,\varsigma}(x)$。
**A3（信息不增）** 任意窗口 $W$ 下，$K(\pi(x|_W))\le K(x|_W)+K(\pi)+O(1)$。

---

## 4. 叶-语言与观察等价

固定 $(\pi,\varsigma)$ 与叶族 $\mathcal L$，
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f):=\Big\{\ \mathcal O_{\pi,\varsigma}(x)\in\Gamma^{\mathbb N}:\ x\in X_f,\ \text{按 }\mathcal L\text{ 分层逐叶读取}\ \Big\},
\qquad
x\sim_{\pi,\varsigma}y\iff \mathcal O_{\pi,\varsigma}(x)=\mathcal O_{\pi,\varsigma}(y).
$$

---

## 5. 预备引理

**引理 5.1（可计算变换的复杂度守恒）.** 若 $\Phi$ 可计算，则
$$
K\big(\Phi(u)|v\big)\ \le\ K\big(u|v\big)+K(\Phi)+O(1).
$$
$\square$

**引理 5.2（可描述窗口族）.** 对 $d+1$ 维轴对齐平行多面体或以 $O(\log |W|)$ 个参数描述的规则窗口，有 $K(W)=O(\log|W|)$。$\square$

**引理 5.3（厚边界覆盖性）.** 半径 $r=\max_{\mathbf n\in N}|\mathbf n|_\infty$ 与时间跨度 $T$ 下，计算 $x|_W$ 仅需 $\mathrm{base}(W)$ 的前一层在 $[-rT,\,rT]^d$ 的过去输入；即 $\partial_{\downarrow}^{(r,T)}W^-$ 覆盖所有依赖（**传播半径以 $|\cdot|_\infty$ 计**）。$\square$

**引理 5.4（因子熵不增）.** 若 $\phi:(X,T)\to(Y,S)$ 为因子，则 $h_\mu(T)\ge h_{\phi_\ast\mu}(S)$。$\square$

**引理 5.5（时间子作用版 SMB/Brudno）.** 对**$\sigma_{\mathrm{time}}$-不变且遍历**的 $\mu$ 与**时间片长方体族** $W_k = R \times [t_k, t_k+T_k-1]$，其中 $T_k\to\infty$，且 **$R\subset\mathbb{Z}^d$ 为固定的有限集合**。记 $L(W_k)=T_k$（时间厚度），有
$$
-\frac1{T_k}\log \mu\big([x|_{W_k}]\big)\ \to\ h_\mu(\sigma_{\mathrm{time}},\alpha_R)\quad (\mu\text{-a.e.}),\qquad
\limsup_{k\to\infty}\frac{K(x|_{W_k})}{T_k}\ =\ h_\mu(\sigma_{\mathrm{time}},\alpha_R)\quad (\mu\text{-a.e.}).
$$
此为针对时间子作用 $\sigma_{\mathrm{time}}$ 或等价地 $(\Omega(F),\sigma_\Omega)$ 的一维SMB/Brudno定理。**窗口形状必须为时间片长方体族**（或满足等价"时间均匀切片"条件），以保证柱集 $[x|_{W_k}]$ 由时间子作用的一维生成划分迭代生成，从而归一化与作用匹配。若采用一般 $W_k$，仅能保证以 $|W_k|$ 归一化时极限为 $\mathbb{Z}^{d+1}$ 作用熵 $h_\mu^{(d+1)}$，或在附加均匀切片/密度假设下再得时间熵极限。$\square$
此外，对于固定有限 $R$，上述极限等于 $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$；取 $\sup_R$ 恢复 $h_\mu(\sigma_{\mathrm{time}})$。若改用 $|R_k|\to\infty$ 且生成的截面族（从而对应生成分割），则极限直接等于完整的 $h_\mu(\sigma_{\mathrm{time}})$（此情形为补充说明，不在本引理的固定 $R$ 前提内）。
【注】仅当 $\alpha_R$ 为时间子作用的**生成分割**（例如采用 $R_k\uparrow$ 的生成截面族）时，极限才等于完整的 $h_\mu(\sigma_{\mathrm{time}})$；固定有限 $R$ 时极限为 $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$。

---

## 6. 主定理与详细证明（T1–T26）

### T1（Block–自然扩张共轭）

**命题.** 若 $X_f\neq\varnothing$，则
$$
\boxed{ (X_f,\ \sigma_{\mathrm{time}})\ \cong\ (\Omega(F),\ \sigma_\Omega) },
\quad
\Omega(F)=\Big\{(\ldots,x_{-1},x_0,x_1,\ldots):\ F(x_t)=x_{t+1}\Big\}.
$$

**证明.** 定义 $\Psi:X_f\to\Omega(F)$，$(\Psi(x))_t(\mathbf r)=x(\mathbf r,t)$。由 SFT 约束得 $F((\Psi(x))_t)=(\Psi(x))_{t+1}$。定义逆 $\Phi:\Omega(F)\to X_f$，$\Phi((x_t))(\mathbf r,t)=x_t(\mathbf r)$。显然 $\Phi\circ\Psi=\mathrm{id}$、$\Psi\circ\Phi=\mathrm{id}$，且 $\Psi\circ\sigma_{\mathrm{time}}=\sigma_\Omega\circ\Psi$。连续性与 Borel 可测性由乘积拓扑与柱集结构给出。$\square$

---

### T2（Unimodular 协变性；复杂度密度不变）

**命题.** 对任意移位不变遍历测度 $\mu$ 与两组可接受叶（由 $U_1,U_2\in\mathrm{GL}_{d+1}(\mathbb Z)$ 给出），令 $\tilde W_k=U_2U_1^{-1}(W_k)$。**假设**：（i）$\{W_k\}$ 与 $\{\tilde W_k\}$ 皆为时间片长方体Følner族，且空间截面 $R\subset\mathbb{Z}^d$ 为**固定有限集合**且不随 $k$ 变化；（ii）两组叶族分别由原始整协向量–时间向量对 $(\tau_i^\star,\tau_i)$ 给出，配对常数 $b_i=\langle\tau_i^\star,\tau_i\rangle\ge1$ 为与 $k$ **无关的常数**；（iii）存在由 $(U,\tau_1^\star,\tau_1,\tau_2^\star,\tau_2)$ 决定且与 $k$ 无关的常数 $c_-,c_+>0$，使得 $c_-L(W_k)\le L(\tilde W_k)\le c_+L(W_k)$。则对 $\mu$-a.e. 的 $x$，
$$
\limsup_{k\to\infty}\frac{K(\pi(x|_{W_k}))}{L(W_k)}
= h_{\pi_\ast\mu}\big(\sigma_{\mathrm{time}},\alpha_R^\pi\big),\qquad
\limsup_{k\to\infty}\frac{K(\pi(x|_{\tilde W_k}))}{L(\tilde W_k)}
= h_{\pi_\ast\mu}\big(\sigma_{\mathrm{time}},\tilde\alpha_R^\pi\big).
$$

**证明.** 整同构 $U=U_2U_1^{-1}$ 保持 Følner 性质：$\{W_k\}$ 为 Følner 族则 $\{\tilde W_k\}$ 亦然，且 $|\tilde W_k|=|W_k|$（整行列式 $\pm1$；此处 $\tilde W_k$ 指格点像集 $U(W_k)$，即使形状非轴对齐，格点数仍相等）。由假设（iii），叶计数（时间厚度）按常数倍缩放，该界由线性映射对叶法向量的作用与固定截面 $R$ 的有界几何畸变给出。分别对两窗族将引理 5.5 应用于因子系统，得到相对于各自观察分割的时间熵极限：$h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)$ 与 $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\tilde\alpha_R^\pi)$。若两观察方案由沿时间子作用的**有限记忆可逆块码**互为同构，则两者等价并给出相同熵率；在此条件下坐标选择不改变极限值。$\square$

---

### T3（观察=译码的语义塌缩）

**命题.** $\mathcal O_{\pi,\varsigma}:X_f\to\Gamma^{\mathbb N}$ 为时间子作用的因子映射，诱导等价类 $x\sim_{\pi,\varsigma}y$。一次观察在等价类中选代表，底层 $x$ 不变。$\square$

---

### T4（信息上界：条件复杂度版）

$$
\boxed{ K\Big(\ \pi(x|_{W})\ \Big|\ x\big|_{\partial_{\downarrow}^{(r,T)} W^-}\Big)\ \le\ K(f)+K(W)+K(\pi)+O(\log |W|) }.
$$
其中 $T$ 为穿越的时间层数（与 §2.4 的 $L(W)$ 一致；见 §2.6 约定）。
【前提说明】以下上界在 §2.2 的**单步时间依赖**前提下成立；若规则对过去 $m>1$ 层有依赖，则将过去因果输入边界改为 $\{t_- -1,\dots,t_- -m\}$ 的对应厚边界，并把 $rT$ 替换为 $r\,(T+m-1)$，其余推理不变。

**证明.** 构造通用程序 $\mathsf{Dec}$：

1. **输入**：$f$ 的编码、窗口 $W$ 的编码（含 $(t_-,T)$ 与几何参数）、$\pi$ 的编码，以及条件串 $x|_{\partial_{\downarrow}^{(r,T)}W^-}$。
2. **递推**：自 $t_-$ 层起按时间子作用逐层生成。对任一 $(\mathbf r,s)\in W$，以
$$
x(\mathbf r,s)=f\big(x(\mathbf r+N,s-1)\big)
$$
计算之；所需右端由前一层已生成或来自条件边界（引理 5.3）。**按 $s=t_-,t_-+1,\dots,t_+$ 逐层生成**，避免依赖循环。对每个层 $s$，**先在传播锥内生成 $W$ 的前向闭包所需的全部单元（允许临时产生 $W$ 之外但位于 $[-r(s-t_-)$, $r(s-t_-)]^d \times \{s\}$ 内的值），最终再限制到 $W$**。
3. **译码**：按协议在 $W$ 内应用 $\pi$ 得 $\pi(x|_W)$。

程序体积为常数，输入长度为 $K(f)+K(W)+K(\pi)+O(\log|W|)$（$\log|W|$ 为层深/对齐成本）。由前缀复杂度定义即得上界。$\square$

---

### T5（Brudno 对齐与因子熵）

**命题.** 对**固定有限的空间截面 $R$** 与**时间片长方体族** $\{W_k = R \times [t_k, t_k+T_k-1]\}$（其中 $T_k\to\infty$，且满足引理5.5的窗口前提），以时间厚度 $L(W_k)=T_k$ 归一化：
$$
\limsup_{k\to\infty}\frac{K(x|_{W_k})}{T_k}\ =\ h_\mu(\sigma_{\mathrm{time}},\alpha_R),\qquad
\limsup_{k\to\infty}\frac{K(\pi(x|_{W_k}))}{T_k}\ =\ h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)\ \le\ h_\mu(\sigma_{\mathrm{time}}).
$$
**注**：固定有限 $R$ 情形；仅当 $\alpha_R$ 为**生成分割**（或采用 $|R_k|\to\infty$ 的增长截面族）时，极限等于完整 $h_\mu(\sigma_{\mathrm{time}})$。

**证明.** 由引理 5.5（时间子作用版SMB/Brudno，窗口族形状与归一化匹配），第一条的 limsup 等式成立。对因子像，$\pi$ 为可计算变换且因子熵不增（引理 5.4），故第二条的 limsup 等式成立且不超过 $h_\mu(\sigma_{\mathrm{time}})$。此外，对因子系统 $\big(\pi(X_f),\sigma_{\mathrm{time}},\pi_\ast\mu\big)$ 应用引理 5.5（同一窗口前提），得 $(\pi_\ast\mu)$-a.e. 的 limsup 值为 $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)$；由 $\mu(\pi^{-1}A)=\pi_\ast\mu(A)$ 可知上述 limsup 等式对 $\mu$-a.e. 的 $x$ 亦成立。若选用生成分割（或采用 $|R_k|\to\infty$ 的增长截面族），则右侧可直接写作 $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}})$。$\square$

---

### T6（程序涌现：宏块-强制；SB-CA $\Rightarrow$ TM）

**命题.** （允许经有限高阶块表示/字母扩展）存在宏块-强制嵌入方案 $\mathsf{Emb}(M)$，使得**若**该方案的有限型约束族**非空**（扩展 SFT 非空），**则**存在 $x^{\mathrm{ext}}\in X_f^{\mathrm{ext}}$（若仅采用高阶块而无字母扩展，则写作 $x^{[k]}\in X_f^{[k]}\cong X_f$）可在译码器 $\pi$ 下译读为某一条（预期的）图灵机 $M$ 的运行轨迹。**若进一步假设嵌入约束完备且无伪解**，则得到"若且唯若"。

**证明（构造）.** 取宏块大小 $k$。扩展字母表为 $\Sigma'=\Sigma\times Q\times D\times S$（机状态、带符号、头移动、同步相位）。在宏块尺度上以有限型局部约束实现转移 $(q,a)\mapsto (q',a',\delta)$，并以相位信号实现跨宏块同步。记由上述有限型约束得到的扩展 SFT 为 $X_f^{\mathrm{ext}}$，并记忘却投影 $\rho: \Sigma'\to\Sigma$（如需将扩展配置关联回底层）。译码器 $\pi$ 读取宏块中心行输出带内容。若这些有限型约束族全局相容（扩展 SFT 非空），则由紧致性可取极限得到全局配置 $x^{\mathrm{ext}}$；非空性因此依赖于相容性前提，而非由紧致性自动推出。$\square$

**小结.** 在**相容但未声明无伪解**时，仅有"非空 $\Rightarrow$ 存在某条可译读轨迹"；在**完备且无伪解**时，得到"若且唯若"（与T9的停机见证等价配合）。

---

### T7（程序权重的通用半测度界）

**命题.** 令程序码为前缀无歧义，则对任意可译读程序 $p$，有 $\nu(p)\le C\cdot 2^{-|p|}$。

**证明.** 由 Kraft 不等式 $\sum_p2^{-|p|}\le1$，通用半测度 $\nu$ 作为加权和满足上界，常数 $C$ 仅依赖所选机。$\square$

---

### T8（截面–自然扩张对偶；熵保持）

**命题.** $X_f$ 与 $\Omega(F)$ 互为截面/自然扩张对偶，且时间熵相等。

**证明.** 由 T1 的共轭 $(X_f,\sigma_{\mathrm{time}})\cong (\Omega(F),\sigma_\Omega)$。自然扩张不改熵；共轭保持熵，故结论成立。$\square$

---

### T9（停机见证的静态化）

**命题.** 在 T6 的相容嵌入方案下（即对应扩展 SFT 非空），$M$ 停机当且仅当存在 $x^{\mathrm{ext}}\in X_f^{\mathrm{ext}}$ 与有限窗口 $W$，使得可见图案 $\pi\big(x^{\mathrm{ext}}\big|_W\big)$ 包含"终止标记" $\square$；反之亦然。

**证明.** "若"向：若 $M$ 在步 $\hat t$ 停机，则宏块中央的译码输出出现 $\square$，形成有限可见图案。"唯若"向：若可见层出现 $\square$，由局部一致性回溯至停机转移；构造保证 $\square$ 非他因产生。上述等价均以嵌入方案全局相容（扩展 SFT 非空）为前提。$\square$

---

### T10（Unimodular 协变性的信息稳定）

**命题.** 若窗口族满足 $K(W_k)=O(\log|W_k|)$，则任意整变换 $U\in\mathrm{GL}_{d+1}(\mathbb{Z})$ 下，T4 上界与 T3 语义保持；变换后窗口的窗口描述复杂度差 $O(\log|W_k|)$，不涉及数据复杂度 $K(x|_{W_k})$ 或 $K(\pi(x|_{W_k}))$ 的逐样本上界。

**证明.** 由引理 5.1–5.2，窗口描述复杂度 $K(W)$ 为生成窗口几何参数的最短程序长度。整变换 $U$ 与平移的编码仅增加 $O(1)$ 常数；厚边界 $\partial_{\downarrow}^{(r,T)}W^-$ 在 $U$ 下的有界畸变吸收进 $O(\log|W_k|)$。由 T2 的测度论版本，数据复杂度密度在归一化后与坐标无关。$\square$

---

### T11（模型集合语义）

**命题.**
$$
X_f=\mathcal T_f(\mathsf{Conf})=\Big\{x\in\Sigma^{\mathbb{Z}^{d+1}}:\forall(\mathbf r,t)\ x(\mathbf r,t)=f(x(\mathbf r+N,t-1))\Big\}.
$$
**证明.** 按定义。$\square$

---

### T12（计算模型对应）

**命题.** (i) SB-CA 与 TM 互相模拟；(ii) 若干 CSP/Horn/$\mu$-安全公式 $\Phi$ 可等价嵌入 EG-CA。

**证明.** (i) 由 T6 及标准"TM 模拟 CA"得双向模拟。
(ii) 将每条半径 $\le r$ 的子句转为禁形集 $\mathcal F_\Phi$，得 $X_{f_\Phi}$。解的模型与 $\Phi$ 的模型等价（有限型 + 紧致性）。$\square$

---

### T13（叶-语言的 $\omega$-自动机刻画；sofic 化充分条件）

**命题.** 若（i）采用路径版 $(Y_G,\sigma)$ 或存在 $k$ 使 $X_f$ 在时间子作用上可经高阶块表示 $X_f^{[k]}$ 令跨叶一致性仅依赖相邻 $k$ 层（时间方向可马尔可夫化）；且（ii）译码器 $\pi:\Sigma^B\to\Gamma$ 的核窗 $B$ 具有有限跨叶厚度，则 $\mathsf{Lang}_{\pi,\varsigma}(X_f)$ 为 sofic（因而 $\omega$-正则），可由某 Büchi 自动机 $\mathcal A$ 接受：
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f)=L_\omega(\mathcal A).
$$

**证明（构造）.** 在时间方向有限记忆条件下，取高阶块表示 $X_f^{[k]}$，将有限状态集 $Q$ 编码入扩展字母表并以有限型约束实现转移 $\delta$。跨叶一次读取对应一次自动机步。接受条件以局部安全/正则约束实现（如"无限次访问 $F$"由循环记忆位实现）。于是得到等价 $\omega$-语言。$\square$

---

### T14（任意可实现事件的 SBU 存在）

**命题.** 对可实现 $v$ 与可接受 $\tau$，$\big(X_f^{(v,\tau)},\rho_\tau\big)$ 非空。

**证明.** 取以 $v$ 一致的有限窗口族，按包含构成有向集；有限一致性由"可实现"与局部约束给出。由紧致性（乘积拓扑）与 Kőnig 引理，存在极限配置 $x\in X_f$ 与 $v$ 一致，故非空。$\square$

---

### T15（因果一致扩张与悖论排除）

**命题.** $X_f^{(v,\tau)}$ 仅包含与锚 $v$ 一致之全局解的限制；矛盾事件不共存。

**证明.** 若某 $x\in X_f^{(v,\tau)}$ 同时包含与 $v$ 矛盾之事件，则在 $\varphi_{v_0}(\mathrm{Cone}^+_\ell(v))$ 上既一致又矛盾，违背一致性定义。$\square$

---

### T16（时间=确定性推进（表观选择））

**命题.** 在确定性 $f$ 与厚边界条件下，$\ell$ 的每次最小正增量推进等价于对未来一致扩张族作**确定性推进**；在确定性 CA 下唯一。

**证明.** 由 T4 的构造，给定上一层与厚边界，下一层值由 $f$ 唯一定义；如存在两种不同推进，则某单元下一层取值不等，违背确定性。$\square$

---

### T17（多锚观察者与主观时间率）

**命题.** 有效步长 $b=\langle\tau^\star,\tau\rangle\ge 1$ 反映章节节拍；不同 $b$ 仅改变读取节奏，在时间片长方体Følner族且空间截面固定或一致有界的前提下，以时间厚度 $L(W_k)=T_k$ 归一化的熵率一致。

**证明.** 时间子作用改为 $\sigma_{\mathrm{time}}^{(b)}$ 等效于对 $\mathbb{Z}$ 子作用"抽样"（$\sigma_\Omega^b$）。测度熵满足（相对于所选分割的版本亦成立）
$$
h_\mu(\sigma_\Omega^b)\ =\ b\cdot h_\mu(\sigma_\Omega).
$$
对时间片长方体 $W$，**观察步数**为 $\lfloor L(W)/b\rfloor$（见 §2.4），而归一化采用**时间厚度** $L(W)=T$。因而
$$
\frac{K\big(\pi(x|_W)\big)}{L(W)}\ \sim\ \frac{\lfloor L(W)/b\rfloor}{L(W)}\cdot h_{\pi_\ast\mu}\big(\sigma_{\mathrm{time}}^{b}\big)\ =\ \frac1b\cdot b\,h_{\pi_\ast\mu}(\sigma_{\mathrm{time}})\ =\ h_{\pi_\ast\mu}(\sigma_{\mathrm{time}}),
$$
其中 $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}}^{b})=b\,h_{\pi_\ast\mu}(\sigma_{\mathrm{time}})$。**若使用固定有限截面 $R$，则应写作**
$$
h_{\pi_\ast\mu}(\sigma_{\mathrm{time}}^{b},\alpha_R^\pi)=b\,h_{\pi_\ast\mu}\!\Big(\sigma_{\mathrm{time}},\ \bigvee_{i=0}^{b-1}\sigma_{\mathrm{time}}^{-i}\alpha_R^\pi\Big),
$$
**并且仅当**上述联结分割生成（或存在沿时间的有限记忆可逆块码同构）**时**，才可写作 $b\,h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)$。观察步数计数 $\lfloor L(W)/b\rfloor$ 的 $1/b$ 因子与 $b$ 正好抵消，归一化后熵率不依赖于 $b$ 的选择。由引理 5.5，对 $\mu$-a.e. 的 $x$ 两族密度极限一致。

**补充说明.** 上述抵消在**固定有限截面**并以**时间厚度 $L(W)$**归一化的情形下成立；若改用体素数归一化或非时间片长方体窗族，则对应的是 $h_\mu^{(d+1)}$ 而非时间熵（见 §2.5 与 §7.5 的注释）。$\square$

---

### T18（锚定图的坐标相对化不变性）

**命题.** 两组嵌入 $(\varphi_{v_0},\varphi_{v_1})$ 若源自同一整仿射嵌入 $\Phi$ 的限制，则在交域去除常数半径带后，仅差 $\mathrm{GL}_{d+1}(\mathbb Z)$ 整仿射与有限半径重标定；两组嵌入间观察协议的额外编码/描述开销 $\le O(K(W))$（对可描述窗口族为 $O(\log|W|)$），不涉及对观测序列本身的数据复杂度或熵差给出逐窗口上界。

**证明.** 存在 $U\in\mathrm{GL}_{d+1}(\mathbb Z)$ 与平移 $t$ 使 $\varphi_{v_1}=U\circ\varphi_{v_0}+t$ 于交域成立。有限半径差异对应剔除边界带。窗口在两坐标下的编码仅多出 $U,t$ 的有限描述；这是协议间转换的额外描述成本，被 $O(K(W))$ 吸收（引理 5.1–5.2）。观测序列的数据复杂度由 T2 的测度论版本给出归一化后的坐标无关性。$\square$

---

### T19（$\ell$-后继的确定性与同层排他性）

**命题.** 确定性 $f$、半径 $r$ 下，若 $u$ 的上下文覆盖下一层生成所需信息，则存在唯一 $\mathrm{succ}_\ell(u)$；边 $u\to\mathrm{succ}_\ell(u)$ 对同层备选具排他性。

**证明.** 下一层取值由 $f$ 的局部函数唯一决定；若存在同层两个不同备选均可接续且相互冲突，则在某公共单元产生不一致赋值，矛盾。$\square$

---

### T20（相容原则：表观选择与决定论统一）

**命题.** 逐叶推进在操作层面表现为"代表选择"，而整体静态编码为"唯一一致扩张"；决定论成立，且与 A3/T4 相容。

**证明.** 由 T14 存在全局一致扩张；T15 排斥矛盾分支；T3 表明"观察=在等价类中选代表"；T4/A3 确保选择不增信息。故表观自由与本体决定论一致。$\square$

---

### T21（信息不增律：一般 CA 与观察因子）

**命题.** 设 $F$ 为半径 $r$ 的 $d$ 维 CA，取任意 Følner 窗口族 $\{W_k\}$（轴对齐平行多面体满足 $K(W_k)=O(\log|W_k|)$）。定义空间信息密度（每格）
$$
I(x):=\limsup_{k\to\infty}\frac{K\big(x|_{W_k}\big)}{|W_k|},\qquad
I_\pi(x):=\limsup_{k\to\infty}\frac{K\big(\pi(x|_{W_k})\big)}{|W_k|}.
$$
则对每个固定的 $T\in\mathbb N$ 与配置 $x$，有
$$
I\big(F^T x\big)\ \le\ I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I\big(F^T x\big)\ \le\ I(x).
$$
**注**：此定理针对 $d$ 维空间配置，按**体素数归一化**（用于纯空间配置）。应用于时空SFT的时间子作用时，应改用**时间厚度 $L(W)$ 归一化**（见T5）。

**证明.** 厚边界与传播锥给出依赖域：存在 $W_k^{+rT}$ 使 $\big(F^T x\big)|_{W_k}$ 可由 $x|_{W_k^{+rT}}$ 可计算恢复（见引理 5.3 的 $r,T$ 控制）。由可计算变换的复杂度上界，
$$
K\big((F^T x)|_{W_k}\big)\ \le\ K\big(x|_{W_k^{+rT}}\big)+O(\log|W_k|).
$$
Følner 性给出 $|W_k^{+rT}|/|W_k|\to1$，取 $\limsup$ 得 $I(F^T x)\le I(x)$。因子译码不增信息（A3，或引理 5.1 的可计算变换），得 $I_\pi(F^T x)\le I(F^T x)$。合并即得结论。$\square$

---

### T22（信息守恒律：可逆 CA）

**命题.** 若 $F$ 可逆且 $F^{-1}$ 亦为 CA（可逆元胞自动机），则对每个固定的 $T\in\mathbb N$ 与配置 $x$，空间信息密度（每格）守恒：
$$
I\big(F^T x\big)=I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I(x),
$$
其中等号在 $\pi=\mathrm{id}$ 或与 $F$ 共轭的无损因子下成立。若 $\mu$ 为移位不变遍历测度，应用于时空SFT的时间子作用 $(X_f,\sigma_{\mathrm{time}})$ 时，由 T1 的共轭与可逆性下熵保持可知 $h_\mu(\sigma_{\mathrm{time}})$ 不变；各时刻空间边缘分布 $(\nu_t)$ 满足平稳性 $\nu_{t+1}=F_\ast\nu_t=\nu_t$，该记号与 $h_\mu(\sigma_{\mathrm{time}})$ 的计算无直接混用。故 $\mu$-几乎处处时间方向的信息密度守恒。
**注**：同T21，此处空间信息密度按**体素数归一化**（用于纯空间配置）；用于时空SFT的时间子作用时，应改用**时间厚度 $L(W)$ 归一化**（见T5）。

**证明.** 由 T21 对 $F$ 与 $F^{-1}$ 分别应用得 $I(F^T x)\le I(x)$ 与 $I(x)\le I(F^T x)$，合并即 $I(F^T x)=I(x)$。关于 $\pi$ 的不增由 A3 给出。测度论版本由 $(X_f,\sigma_{\mathrm{time}})\cong(\Omega(F),\sigma_\Omega)$ 的共轭与可逆性下熵保持（T8），配合叶计数归一化的Brudno定理（引理 5.5）得出。$\square$

---

### T23（观测压力函数与信息几何）

【来源映射】对每个可见类目 $j$，令 $a_j$ 为译码后在单位时间片的先验权（或计数权），$\beta_j$ 为对应**逐叶统计特征**（如频率向量/能量代价）的固定向量；当在窗口族 $W_k$ 上取极限时，$\{p_j(\eta)\}$ 即为这些观测统计的指数族重加权。

**定义.** 为避免与 §2 中的叶族记号 $\rho$ 混淆，以下以 $\eta$ 记参数。取一组可见类目（由译码/计数规则给出）索引为 $j=1,\dots,J$（此处取 $J<\infty$），赋权 $a_j>0$ 与向量 $\beta_j\in\mathbb R^n$。定义
$$
Z(\eta)=\sum_{j=1}^{J} a_j\,e^{\,\langle\beta_j,\Re\eta\rangle},\qquad
P(\eta)=\log Z(\eta),\qquad
p_j(\eta)=\frac{a_j e^{\,\langle\beta_j,\Re\eta\rangle}}{Z(\eta)}.
$$
在 $Z(\eta)$ 收敛的域内，且满足局部一致收敛从而允许求和/微分互换的标准条件，有
$$
\nabla_{\eta}P(\eta)=\mathbb E_p[\beta]=\sum_j p_j\,\beta_j,\qquad
\nabla_{\eta}^2 P(\eta)=\mathrm{Cov}_p(\beta)\succeq 0.
$$
因此 $P$ **凸**，其 Hessian 即 Fisher 信息。沿方向 $\eta(s)=\eta_\perp+s\mathbf v$，
$$
\frac{d^2}{ds^2}P\big(\eta(s)\big)=\mathrm{Var}_p\big(\langle\beta,\mathbf v\rangle\big)\ge0.
$$
若再记香农熵 $H(\eta)=-\sum_j p_j\log p_j$，则
$$
H(\eta)=P(\eta)-\sum_j p_j\log a_j-\big\langle\Re\eta,\,\mathbb E_p[\beta]\big\rangle.
$$

**证明要点.** 由 log-sum-exp 的标准求导（在前述局部一致收敛条件下可交换求和与微分），得梯度与 Hessian 表达；方向二阶导即方差。熵恒等式由 $p_j\propto a_j e^{\langle\beta_j,\Re\eta\rangle}$ 代入 $H=-\sum p_j\log p_j$ 展开并整理得到。$\square$

---

### T24（相变/主导切换的判别；有限 J 版）

**命题.** 令幅度 $A_j(\eta):=a_j e^{\langle\beta_j,\eta\rangle}$，并定义
$$
H_{jk}=\Big\{\eta:\ \langle\beta_j-\beta_k,\eta\rangle=\log\frac{a_k}{a_j}\Big\},\qquad
\delta(\eta):=\min_{j<k}\Big|\ \langle\beta_j-\beta_k,\eta\rangle-\log\frac{a_k}{a_j}\ \Big|.
$$
若 $\delta(\eta)>\log(J-1)$，则存在唯一索引 $j_\star$ 使 $A_{j_\star}(\eta)=\max_j A_j(\eta)$ 且
$$
\sum_{k\ne j_\star}A_k(\eta)<A_{j_\star}(\eta),
$$
因而无主导切换；主导切换仅可能发生在 $\{\eta:\ \delta(\eta)\le\log(J-1)\}$ 的薄带内，其骨架为超平面族 $\{H_{jk}\}$。

**证明.** 由 $\delta(\eta)$ 的定义，$\log A_{j_\star}-\log A_k\ge\delta(\eta)$，故 $A_k\le e^{-\delta(\eta)}A_{j_\star}$，再求和得结论。$\square$

---

### T25（方向化极点 = 增长指数；可数无限版）

**命题.** 固定方向 $\mathbf v$ 与分解 $\eta=\eta_\perp+s\mathbf v$。令索引族 $\{(a_j,\beta_j)\}_{j\ge1}$ 为**可数无限**，并假设存在 $\eta_0$ 使得 $\sum_{j\ge1} a_j e^{\langle\beta_j,\Re\eta_0\rangle}<\infty$。设沿 $\mathbf v$ 的带权累积分布
$$
M_{\mathbf v}(t)=\sum_{t_j\le t} w_j,\qquad t_j:=\langle-\beta_j,\mathbf v\rangle,\quad w_j:=a_j e^{\langle\beta_j,\eta_\perp\rangle},
$$
当 $t\to+\infty$ 具有指数–多项式渐近（并假设 $M_{\mathbf v}$ 具界变差与温和增长）
$$
M_{\mathbf v}(t)=\sum_{\ell=0}^{L} Q_\ell(t)\,e^{\gamma_\ell t}+O\!\big(e^{(\gamma_L-\delta)t}\big),\qquad \gamma_0>\cdots>\gamma_L,
$$
且 $M_{\mathbf v}$ 具界变差并满足温和增长。则其拉普拉斯–Stieltjes 变换
$$
\mathcal L_{\mathbf v}(s):=\int_{(-\infty,+\infty)} e^{-s t}\,dM_{\mathbf v}(t)=\sum_j w_j e^{-s t_j}
$$
在 $\Re s>\gamma_0$ 收敛，并可亚纯延拓至 $\Re s>\gamma_L-\delta$，在 $s=\gamma_\ell$ 处至多出现 $\deg Q_\ell+1$ 阶极点。特别地，右端收敛垂线的实部等于最大增长指数 $\gamma_0$。若 $J<\infty$，则上述和式为有限和，不出现极点情形。

**证明要点.** 属于经典的拉普拉斯–Stieltjes Tauberian 词典：对指数–多项式渐近逐段积分并使用分部积分/留数控制，得极点位置与阶；绝对收敛域的临界由 $\gamma_0$ 给出。$\square$

---

### T26（可逆与非可逆：判据与后果）

**命题（判据）.** 全局映射 $F: \Sigma^{\mathbb Z^d}\to\Sigma^{\mathbb Z^d}$ 为 CA 可逆 $\iff$ 它为双射且 $F^{-1}$ 也是 CA（存在有限半径的逆局部规则）。在 $\mathbb Z^d$ 上，Garden-of-Eden 定理给出：$F$ 满射 $\iff$ $F$ 预单射；可逆等价于同时满射与单射。

**命题（后果）.** 若 $F$ 可逆，则：
1) 信息密度守恒：$I(F^T x)=I(x)$（见 T22）；
2) 观察因子下不增：$I_\pi(F^T x)\le I(x)$；
3) 无真吸引子：不存在把开集压入真子集的单向吸引（每点具双向轨道，可能存在周期但无信息耗散到单一固定点的不可逆坍缩）。

**证明.** 判据为标准结论；后果 1–2 由 T21–T22 立即推出；后果 3 由可逆性与双向可达性给出（若存在真吸引子则与双射矛盾）。$\square$

---



## 7. 构造与算法

**7.1 从规则到 SFT**：由 $f$ 的局部一致性导出禁形集 $\mathcal F$，得 $X_f$。

**7.2 从 SFT 到永恒图**：以允许图案为顶点、合法拼接为边构造 $G_f$；用 $\ell$ 的等值面给出叶次序。

**7.3 译码器设计**：选核窗 $B$、块码 $\pi:\Sigma^B\to\Gamma$；定义**按 $\ell$ 分层的逐叶读取**协议 $\varsigma$。

**7.4 宏块-强制程序盒**：自相似平铺嵌入"状态-控制-带"并可译读（见 T6）。

**7.5 压缩-熵实验（可复现）**
$$
y_k=\pi\big(x|_{W_k}\big),\quad
c_k=\mathrm{compress}(y_k),\quad
r_k=\frac{\lvert c_k\rvert}{\lvert W_k\rvert},\quad
\mathrm{plot}(r_k)\ \ (k=1,2,\ldots).
$$
**注**：此处用 $|W_k|$ 归一化便于实验操作；理论上对应时间子作用熵应改用时间厚度 $L(W_k)=T_k$ 归一化（见T5，需采用时间片长方体族）。为与 T5 的时间熵对齐，应保持 $R$ 固定并**同时报告 $|c_k|/T_k$（固定有限 $R$）**；若 $|R_k|$ 变化或采用一般 Følner 窗，则 $r_k$ 反映的是 $h_\mu^{(d+1)}$ 量级而非时间熵。

**7.6 从事件节点构造 SBU（强制域传播）**
**输入**：可实现 $v$、取向 $\tau$、容许误差 $\epsilon$。
**步骤**：以 $v$ 与局部一致性为约束，进行**双向约束传播/一致性检查**，在增大的 $W_k$ 上计算被 $v$**强制**的单元集合，并按 $\ell$ 逐叶扩张至局部稳定。
**输出**：$\big(X_f^{(v,\tau)}\big)$ 在 $W_k$ 上的**强制域近似**与信息密度曲线。

**7.7 锚定图的相对坐标构造**：BFS 分层（按 $\ell$/空间邻接）→ 相对嵌入 $\varphi_{v_0}$ → 半径 $r$ 一致性校验与等价类归并。

**7.8 由 CSP / $\mu$-安全公式到 CA**：给定 CSP 或 Horn/$\mu$-安全公式 $\Phi$，对每条半径 $\le r$ 子句生成禁形 $\mathcal F_\Phi$，定义 $f_\Phi$：
$$
X_{f_\Phi}=\mathcal T_{f_\Phi}(\mathsf{Conf})
=\Big\{x:\ \forall(\mathbf r,t),\ x(\mathbf r,t)=f_\Phi\big(x(\mathbf r+N,t-1)\big)\Big\},
$$
必要时以有限控制层保持同步（不改等价类）。

**7.9 由 $\omega$-自动机到叶-语言**：给定 Büchi 自动机 $\mathcal A=(Q,\Gamma,\delta,q_0,F)$，选择 $(\pi,\varsigma)$ 并构造扩展 SFT $X_{f,\mathcal A}$ 使：

1. $\pi$ 将跨叶观测编码为 $\Gamma$-字；
2. 以有限型同步条件实现 $\delta$：在 $X_f$ 上叠加有限型"控制/同步层"（或等价地先取 $X_f^{[k]}$ 将 $Q$ 编码入字母表并以局部约束模拟转移），得到扩展 SFT $X_{f,\mathcal A}$；
3. 接受条件以安全/正则约束表达。于是
$$
\mathsf{Lang}_{\pi,\varsigma}\big(X_{f,\mathcal A}\big)=L_\omega(\mathcal A).
$$

---

## 8. 典型示例与玩具模型

**Rule-90（线性）**：三视角一致；任意锚的 SBU 由线性关系唯一递推；Følner 归一化后复杂度密度一致；叶-语言为 $\omega$-正则。

**Rule-110（通用）**：宏块-强制嵌入 TM（T6）；停机见证对应局部终止标记（T9）；逐叶推进排除同层备选（T19–T20）。

**二染色 CSP（模型视角）**：图二染色的局部约束 → 禁形；锚定某节点颜色并逐叶展开，构成因果一致事件锥体；叶-语言在适当条件下为 $\omega$-正则。

**2×2 玩具块（锚–SBU–译码–表观选择）**
参数：$\Sigma=\{0,1\}$，$d=1$，$N=\{-1,0,1\}$，$f(a,b,c)=a\oplus b\oplus c$（XOR，周期边界）。锚 $v_0$ 固定 $(t=0,\mathbf r=0)$ 的局部图案。按 T4 的因果厚边界与**逐叶推进**递推 $t=1$ 层，得到唯一一致扩张；与锚矛盾的同层点被排除（T19）。取
$$
B=\Big\{(\mathbf r,t):\ \mathbf r\in\{0,1\},\ t=1\Big\},
$$
$\pi$ 读出二维块为可见二进制串——"下一步"仅读出，不增信息（A3）。

---

## 9. 扩展方向

* **连续扩展（cEBOC）**：以 Markov 符号化/紧致字母 SFT 推广；重述复杂度/熵并阐明离散→连续极限。
* **量子启发**：对同一静态块 $X_f$ 的多个相容 SBU 作同时描述，测量对应**锚定切换与锁定** + 一次 $\pi$-语义塌缩；为基于信息与计算的量子诠释提供构造性基础（非态矢量假设）。
* **范畴/余代数视角**：$(X_f,\mathrm{shift})$ 作余代数；带锚 SBU 为注入初值的余代数子解；叶-语言为自动机余代数同态像。
* **鲁棒性**：小扰动/缺失下的容错译码与鲁棒窗，保证可观察语义稳定。

---

## 10. 观察者、表观选择与时间体验（RPG 比喻）

**层次分离**：**操作层**（观察/译码/逐叶推进/代表选择）与**本体层**（静态几何/唯一一致扩张）。
**相容原则**：把 $X_f$ 视为**RPG 的完整数据与规则**；**逐叶推进**如按**既定章节节拍 $b$** 解锁剧情。玩家"选择"是在同层兼容分支中**选代表**并**排除**其它分支；**剧情本体**（静态块）早已写定，选择不生成新信息（A3），与决定论相容（T20）。
**主观时间率**：有效步长 $b=\langle\tau^\star,\tau\rangle$ 体现"章节节拍"；Følner 归一化后熵率一致（T2/T5/T17）。

---

## 11. 结论

EBOC 在极简公理下统一**无时间几何（永恒图/SFT）**、**静态块一致体**与**逐叶译码的观察-计算语义**，形成从**模型/自动机**到**可见语言**的完整链条。本文给出 T1–T26 的细化证明，确立了**信息不增律**（T4/A3）、**Brudno 对齐**（T5）、**unimodular 协变性**（T2/T10）、**事件锥体/静态块展开**（T14–T16）、**多锚观察者与坐标相对化**（T17–T18）等核心结果，并提供可复现实验与构造流程（§7）。

---

## 附录 A：术语与记号

* **语义塌缩**：$x\mapsto\mathcal O_{\pi,\varsigma}(x)$ 的信息因子化。
* **表观选择**：按 $\ell$ 的最小正增量推进，对同层备选作代表选择；仅改变语义代表，不创造信息。
* **时间片长方体族**：形如 $W_k=R_k\times[t_k, t_k+T_k-1]$ 的窗口族，其中 $R_k\subset\mathbb{Z}^d$ 为空间截面，$T_k\to\infty$ 为时间厚度；与时间子作用 $\sigma_{\mathrm{time}}$ 的一维Følner理论相容。
* **叶计数（时间厚度）**：对时间片长方体 $W=R\times[t_0, t_0+T-1]$，定义 $L(W)=T$ 为穿越的叶层数，对应观察步数。
* **原始整协向量**：$\tau^\star\in(\mathbb{Z}^{d+1})^\vee$，$\gcd(\tau^\star_0,\ldots,\tau^\star_d)=1$；其与实际时间方向 $\tau$ 的配对 $\langle\tau^\star,\tau\rangle=b\ge1$ 定义逐叶推进步长。
* **$\mathrm{GL}_{d+1}(\mathbb{Z})$**：整可逆矩阵群（行列式 $\pm1$）。
* **Følner 族**：$|\partial W_k|/|W_k|\to0$ 的窗口族。
* **柱集**：$[p]_W=\Big\{x\in X_f:\ x|_W=p\Big\}$。
* **熵归一化对应**：$h_\mu(\sigma_{\mathrm{time}})$ 与时间厚度 $L(W)=T$ 归一化相容（时间片长方体族）；$h_\mu^{(d+1)}$ 与体素数 $|W|$ 归一化相容（一般Følner族）。
* **μ-安全公式**（§7.8，T12）：指可表达为有限半径局部约束的一阶逻辑公式子类（如Horn子句、safety属性），其模型可通过有限型禁形集实现为SFT；此处"μ"仅作记号区分，非测度论意义。

---

## 参考文献（指引性）

* A. A. Brudno (1983). *Entropy and the complexity of trajectories*.
* D. Lind & B. Marcus. *Symbolic Dynamics and Coding*.
* E. F. Moore (1962); J. Myhill (1963). *Machine models / Reversible CA*.
* M. Li & P. Vitányi. *An Introduction to Kolmogorov Complexity*.
* R. Berger; J. Kari. *Tilings, Undecidability, SFT*.
* J. R. Büchi; W. Thomas; D. Perrin & J.-E. Pin. *$\omega$-Automata and $\omega$-Languages*.
* D. Ornstein & B. Weiss; E. Lindenstrauss（可加群作用的 SMB / 点态遍历）.
