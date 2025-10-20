# EBOC：永恒–静态块 观察-计算 统一理论

**作者**：Auric
**日期**：2025-10-18

---

## 摘要

**目标.** 提出 **EBOC（Eternal-Block Observer-Computing）**：一个无需显式全局时间的几何—信息统一框架，将**永恒图元胞自动机**（EG-CA）的**无时间因果编码**与**静态块宇宙元胞自动机**（SB-CA）的**程序语义与观察-译码**合并于同一形式系统，并给出可验证的信息律与构造算法。本文将静态块 $X_f$ 与永恒图边移位 $(Y_G,\sigma)$ 视为**等价双表述**；以下以 $X_f$ 为主叙述，但每条结论均可在 $(Y_G,\sigma)$ 上通过有限型展示/编码等价重述。

**三大支柱.**

1. **几何编码（Graph/SFT）**：宇宙作为满足局部规则 $f$ 的**静态块** $X_f\subset\Sigma^{\mathbb{Z}^{d+1}}$；其因果/一致性由**永恒图** $G=(V,E)$ 与 **子移位（SFT）** 并行刻画。
2. **语义涌现（Observation = Decoding）**：**观察=因子译码**。译码器 $\pi:\Sigma^{B}\to\Gamma$ 按**可接受叶分层逐叶读取**静态块（沿 $\tau$ 自层 $c$ 推进到 $c+b$ 的跨叶读取），输出可见语言；"语义塌缩"系从底层配置到可见记录的**信息因子化**。
3. **信息约束（不增律）**：观察不创造信息：
$$
K\big(\pi(x|_W)\big)\ \le\ K(x|_W)+K(\pi)+O(1),
$$
并在**因果厚边界**下给出**条件复杂度**上界与与 Brudno 一致的熵极限。

**统一比喻（RPG 游戏）.** 宇宙如**无限剧情的 RPG**：**游戏数据与演化规则**早已写定（$(X_f,f)$），"选择"（表观自由意志）须与**剧情线**一致（决定论）。**逐叶读取**按既定节拍 $b$ 逐章解锁；"选择"是在兼容分支中**选代表**并**排除**不相容分支，本体"ROM"并未增减信息。

**核心对象.**
$$
\mathcal U=(X_f, G, \rho, \Sigma, f, \pi, \mu, \nu),
$$
其中 $X_f$ 为空间-时间 SFT，$G$ 为永恒图，$\rho$ 给出**可接受叶族**（原始整协向量 $\tau^\star$ 的水平集，$\langle\tau^\star,\tau\rangle=b\ge1$），$\pi$ 为译码器，$\mu$ 为移位不变遍历测度，$\nu$ 为通用半测度（仅作典型性权重）。等价地，可用 $G$ 的**边移位** $Y_G$ 及其**路径移位** $(Y_G,\sigma)$ 表达所有结果；观察/信息律对两表述同样成立。

---

## 1. 引言与动机

传统 CA 以全局时间迭代呈现"演化"；块/永恒图视角一次性给定整段时空，"演化"仅是**逐叶读取**得到的路径叙述。动态视角依赖时间背景、难以背景独立；静态视角缺乏观测语义。EBOC 以"**几何编码 × 语义译码 × 信息律**"统一二者：SFT/图结构保证一致性与构造性；因子映射提供可见语言；复杂度/熵刻画守恒与极限。本文在极简公理下建立 T1–T20 定理族，给出细化证明与可复现实验流程。

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
Y_G=\Big\{(e_t)_{t\in\mathbb{Z}}\in\mathcal E^{\mathbb{Z}}:\ \forall t,\ \mathrm{tail}(e_{t+1})=\mathrm{head}(e_t)\Big\}.
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
* **时间子作用记号**：记 $\sigma_{\mathrm{time}}$ 为 $X_f$ 沿时间坐标的**一维子作用**，$\sigma_\Omega$ 为 $\Omega(F)$ 的时间移位。

### 2.5 复杂度与测度

* 采用**前缀** Kolmogorov 复杂度 $K(\cdot)$ 与条件复杂度 $K(u|v)$。
* $\mu$：移位不变且遍历；$\nu$：通用半测度（算法概率）。
* **窗口描述复杂度**：$K(W)$ 为生成 $W$ 的最短程序长度；Følner 族 $\{W_k\}$ 满足 $|\partial W_k|/|W_k|\to 0$。

### 2.6 因果厚边界（用于 T4）

* 明确采用 $\infty$-范数：
$$
r\ :=\ \max_{\mathbf n\in N}\ |\mathbf n|_{\infty}.
$$
* 定义
$$
t_-=\min\Big\{t:(\mathbf r,t)\in W\Big\},\quad
t_+=\max\Big\{t:(\mathbf r,t)\in W\Big\},\quad
T=t_+-t_-.
$$
* 底层 $\mathrm{base}(W)=\Big\{(\mathbf r,t_-)\in W\Big\}$。
* **底层过去因果输入边界（标准坐标）**
$$
\partial_{\downarrow}^{(r,T)}W^-\ :=\ \Big\{(\mathbf r+\mathbf n,\ t_--1)\ :\ (\mathbf r,t_-)\in\mathrm{base}(W),\ \mathbf n\in[-rT,rT]^d\cap\mathbb{Z}^d\Big\}\setminus W.
$$
非标准叶情形先用 $U^{-1}$ 回到标准坐标后取像。

### 2.7 永恒图的坐标相对化（Anchored Chart）

$G$ 不携带全局坐标。选锚 $v_0$，相对嵌入 $\varphi_{v_0}:\mathrm{Ball}_G(v_0,R)\to\mathbb{Z}^{d+1}$ 满足 $\varphi_{v_0}(v_0)=(\mathbf 0,0)$，沿 $\tau$ 的路径层函数单调不减，空间邻接为有限移位。
层函数
$$
\ell(w):=\langle\tau^\star,\ \varphi_{v_0}(w)\rangle,\qquad
\mathrm{Cone}^+_{\ell}(v):=\Big\{w\in \mathrm{Dom}(\varphi_{v_0})\ :\ \exists\ v\leadsto w\ \text{且 }\ell\ \text{沿途单调不减}\Big\}.
$$
**SBU（静态块展开）**
$$
X_f^{(v,\tau)}:=\Big\{x\in X_f:\ x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R))}=\mathrm{pat}(v)\ \text{且}\ x\ \text{在}\ \varphi_{v_0}\!\big(\mathrm{Cone}^+_\ell(v)\big)\ \text{上为该锚的一致扩张}\Big\},
$$
其中"一致扩张"指：在该锥内所有由 $v$ 与局部规则强制得到的单元与 $x$ 匹配。

### 2.8 永恒图—SFT 的双表述（工作准则）

- 双表示：本文所有以静态块 $X_f$ 叙述的结论，均存在以永恒图边移位 $(Y_G,\sigma)$ 的等价版本；二者通过标准的有限型展示/编码互相给出。为简洁起见，正文以 $X_f$ 为主，必要处以“(EG)”括注路径版表述。
- 对应关系：窗口 $W$ 与厚边界对应于有限路径段与有限邻接半径；逐叶读取对应于沿路径的时间移位读取；观察因子 $\pi$ 在 $X_f$ 上的定义可在 $Y_G$ 上通过路径块码 $\pi_G$ 等价实现。


> 下文仅在**存在该相对嵌入的图域**上讨论 SBU。

**定义·可实现事件.** 设永恒图 $G=(V,E)$。称 $v\in V$ **可实现**，若存在 $x\in X_f$ 与某相对嵌入 $\varphi_{v_0}$ 及半径 $R$ 使得 $x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R))}$ 与 $v$ 的局部图案一致（按文中"局部图案→顶点"的编码约定）。

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

**引理 5.3（厚边界覆盖性）.** 半径 $r=\max_{\mathbf n\in N}|\mathbf n|_\infty$ 与时间跨度 $T$ 下，计算 $x|_W$ 仅需 $\mathrm{base}(W)$ 的前一层在 $[-rT,rT]^d$ 的过去输入；即 $\partial_{\downarrow}^{(r,T)}W^-$ 覆盖所有依赖（**传播半径以 $|\cdot|_\infty$ 计**）。$\square$

**引理 5.4（因子熵不增）.** 若 $\phi:(X,T)\to(Y,S)$ 为因子，则 $h_\mu(T)\ge h_{\phi_\ast\mu}(S)$。$\square$

**引理 5.5（SMB/Brudno 在 $\mathbb{Z}^{d+1}$ 上）.** 对移位不变遍历 $\mu$ 与 Følner 族 $\{W_k\}$，有
$$
-\frac1{|W_k|}\log \mu\big([x|_{W_k}]\big)\ \to\ h_\mu(X_f)\quad (\mu\text{-a.e.}),\qquad
\frac{K(x|_{W_k})}{|W_k|}\ \to\ h_\mu(X_f)\quad (\mu\text{-a.e.}).
$$
$\square$

---

## 6. 主定理与详细证明（T1–T20）

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

**命题.** 对任意移位不变遍历测度 $\mu$ 与两组可接受叶（由 $U_1,U_2\in\mathrm{GL}_{d+1}(\mathbb Z)$ 给出），令 $\tilde W_k=U_2U_1^{-1}(W_k)$。则对 $\mu$-a.e. 的 $x$，
$$
\lim_{k\to\infty}\frac{K(\pi(x|_{W_k}))}{|W_k|}
=
\lim_{k\to\infty}\frac{K(\pi(x|_{\tilde W_k}))}{|\tilde W_k|}
= h_{\pi_\ast\mu}\big(\pi(X_f)\big).
$$

**证明.** 整同构 $U=U_2U_1^{-1}$ 保持 Følner 性质：$\{W_k\}$ 为 Følner 族则 $\{\tilde W_k\}$ 亦然，且 $|\tilde W_k|=|W_k|$（整行列式 $\pm1$）。由引理 5.5（SMB/Brudno），对 $\mu$-a.e. 的 $x$，两族窗口上的归一化复杂度均收敛至 $h_\mu(X_f)$。因子映射 $\pi$ 诱导 $\pi_\ast\mu$，由引理 5.1 与 5.4，归一化后得到因子熵 $h_{\pi_\ast\mu}(\pi(X_f))$，与坐标选择无关。$\square$

---

### T3（观察=译码的语义塌缩）

**命题.** $\mathcal O_{\pi,\varsigma}:X_f\to\Gamma^{\mathbb N}$ 为时间子作用的因子映射，诱导等价类 $x\sim_{\pi,\varsigma}y$。一次观察在等价类中选代表，底层 $x$ 不变。$\square$

---

### T4（信息上界：条件复杂度版）

$$
\boxed{ K\Big(\ \pi(x|_{W})\ \Big|\ x\big|_{\partial_{\downarrow}^{(r,T)} W^-}\Big)\ \le\ K(f)+K(W)+K(\pi)+O(\log |W|) }.
$$

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

**命题.** 对 $\mu$-几乎处处的 $x$ 与任意 Følner 族 $\{W_k\}$：
$$
\frac{K(x|_{W_k})}{|W_k|}\ \to\ h_\mu(X_f),\qquad
\frac{K(\pi(x|_{W_k}))}{|W_k|}\ \to\ h_{\pi_\ast\mu}\big(\pi(X_f)\big)\ \le\ h_\mu(X_f).
$$

**证明.** 由引理 5.5（SMB/Brudno 在可加群作用上），第一极限成立。对因子像，$\pi$ 为可计算变换且因子熵不增（引理 5.4），故第二极限成立且不超过 $h_\mu(X_f)$。$\square$

---

### T6（程序涌现：宏块-强制；SB-CA $\Rightarrow$ TM）

**命题.** 存在宏块-强制嵌入使任意图灵机 $M$ 的运行可在 $X_f$ 中实现并被 $\pi$ 译读。

**证明（构造）.** 取宏块大小 $k$。扩展字母表为 $\Sigma'=\Sigma\times Q\times D\times S$（机状态、带符号、头移动、同步相位）。在宏块尺度上以有限型局部约束实现转移 $(q,a)\mapsto (q',a',\delta)$，并以相位信号实现跨宏块同步。译码器 $\pi$ 读取宏块中心行输出带内容。紧致性与局域性保证非空解存在。$\square$

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

**命题.** 在 T6 的嵌入构造中，$M$ 停机当且仅当 $X_f$ 中存在包含"终止标记" $\square$ 的有限窗口图案。

**证明.** "若"向：若 $M$ 在步 $\hat t$ 停机，则宏块中央出现 $\square$，形成有限柱状图案。
"唯若"向：若出现 $\square$，由局部一致性回溯至停机转移；构造保证 $\square$ 非他因产生。$\square$

---

### T10（Unimodular 协变性的信息稳定）

**命题.** 若 $K(W_k)=O(\log|W_k|)$，则任意整变换 $U$ 下 T4 上界与 T3 语义保持，有限窗口复杂度差 $O(\log|W_k|)$。

**证明.** 由引理 5.1–5.2 与 T2 的同构编码论证；厚边界与传播锥在 $U$ 下仅作有界畸变，吸收进 $O(\log|W_k|)$。$\square$

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

**命题.** 有效步长 $b=\langle\tau^\star,\tau\rangle\ge 1$ 反映章节节拍；不同 $b$ 仅改变读取节奏，在长方体 Følner 族（或等价地：时间厚度 $T_k\to\infty$，且空间/时间尺度比在上下有界）下，归一化熵率一致。

**证明.** 时间子作用改为 $\sigma_{\mathrm{time}}^{(b)}$ 等效于对 $\mathbb{Z}$ 子作用"抽样"（$\sigma_\Omega^b$）。测度熵满足
$$
h(\sigma_\Omega^b)\ =\ b\cdot h(\sigma_\Omega).
$$
对长方体 Følner 族，$|W_k|$ 在"每步跨 $b$"下同样线性按 $b$ 缩放，归一化后抵消，极限一致。对一般 Følner 族，由引理 5.5，对 $\mu$-a.e. 的 $x$ 两族密度极限仍一致，但不宜逐窗口声称线性比例抵消。$\square$

---

### T18（锚定图的坐标相对化不变性）

**命题.** 两组嵌入 $(\varphi_{v_0},\varphi_{v_1})$ 若源自同一整仿射嵌入 $\Phi$ 的限制，则在交域去除常数半径带后，仅差 $\mathrm{GL}_{d+1}(\mathbb Z)$ 整仿射与有限半径重标定；观察语义差 $\le O(K(W))$（可描述窗口族为 $O(\log|W|)$）。

**证明.** 存在 $U\in\mathrm{GL}_{d+1}(\mathbb Z)$ 与平移 $t$ 使 $\varphi_{v_1}=U\circ\varphi_{v_0}+t$ 于交域成立。有限半径差异对应剔除边界带。窗口在两坐标下的编码仅多出 $U,t$ 的有限描述，复杂度差被 $O(K(W))$ 吸收（引理 5.1–5.2）。$\square$

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

**命题.** 设 $F$ 为半径 $r$ 的 $d$ 维 CA，取任意 Følner 窗口族 $\{W_k\}$（轴对齐平行多面体满足 $K(W_k)=O(\log|W_k|)$）。定义信息密度
$$
I(x):=\limsup_{k\to\infty}\frac{K\big(x|_{W_k}\big)}{|W_k|},\qquad
I_\pi(x):=\limsup_{k\to\infty}\frac{K\big(\pi(x|_{W_k})\big)}{|W_k|}.
$$
则对每个固定的 $T\in\mathbb N$ 与配置 $x$，有
$$
I\big(F^T x\big)\ \le\ I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I\big(F^T x\big)\ \le\ I(x).
$$

**证明.** 厚边界与传播锥给出依赖域：存在 $W_k^{+rT}$ 使 $\big(F^T x\big)|_{W_k}$ 可由 $x|_{W_k^{+rT}}$ 可计算恢复（见引理 5.3 的 $r,T$ 控制）。由可计算变换的复杂度上界，
$$
K\big((F^T x)|_{W_k}\big)\ \le\ K\big(x|_{W_k^{+rT}}\big)+O(\log|W_k|).
$$
Følner 性给出 $|W_k^{+rT}|/|W_k|\to1$，取 $\limsup$ 得 $I(F^T x)\le I(x)$。因子译码不增信息（A3，或引理 5.1 的可计算变换），得 $I_\pi(F^T x)\le I(F^T x)$。合并即得结论。$\square$

---

### T22（信息守恒律：可逆 CA）

**命题.** 若 $F$ 可逆且 $F^{-1}$ 亦为 CA（可逆元胞自动机），则对每个固定的 $T\in\mathbb N$ 与配置 $x$，
$$
I\big(F^T x\big)=I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I(x),
$$
其中等号在 $\pi=\mathrm{id}$ 或与 $F$ 共轭的无损因子下成立。若 $\mu$ 为移位不变遍历测度，则 Brudno 极限与熵不变性给出 $h_\mu= h_{F_\ast\mu}$，因而 $\mu$-几乎处处信息密度守恒。

**证明.** 由 T21 对 $F$ 与 $F^{-1}$ 分别应用得 $I(F^T x)\le I(x)$ 与 $I(x)\le I(F^T x)$，合并即 $I(F^T x)=I(x)$。关于 $\pi$ 的不增由 A3 给出。测度论版本由 $(X_f,\sigma_{\mathrm{time}})\cong(\Omega(F),\sigma_\Omega)$ 的共轭与可逆性下熵保持（T8），配合 Brudno（引理 5.5）得出。$\square$

---

### T23（观测压力函数与信息几何）

**定义.** 取一组可见类目（由译码/计数规则给出）索引为 $j=1,\dots,J$，赋权 $a_j>0$ 与向量 $\beta_j\in\mathbb R^n$。定义
$$
Z(\rho)=\sum_{j=1}^{J} a_j\,e^{\,\langle\beta_j,\Re\rho\rangle},\qquad
P(\rho)=\log Z(\rho),\qquad
p_j(\rho)=\frac{a_j e^{\,\langle\beta_j,\Re\rho\rangle}}{Z(\rho)}.
$$
在 $Z(\rho)$ 收敛的域内，且满足局部一致收敛从而允许求和/微分互换的标准条件，有
$$
\nabla_{\rho}P(\rho)=\mathbb E_p[\beta]=\sum_j p_j\,\beta_j,\qquad
\nabla_{\rho}^2 P(\rho)=\mathrm{Cov}_p(\beta)\succeq 0.
$$
因此 $P$ **凸**，其 Hessian 即 Fisher 信息。沿方向 $\rho(s)=\rho_\perp+s\mathbf v$，
$$
\frac{d^2}{ds^2}P\big(\rho(s)\big)=\mathrm{Var}_p\big(\langle\beta,\mathbf v\rangle\big)\ge0.
$$
若再记香农熵 $H(\rho)=-\sum_j p_j\log p_j$，则
$$
H(\rho)=P(\rho)-\sum_j p_j\log a_j-\big\langle\Re\rho,\,\mathbb E_p[\beta]\big\rangle.
$$

**证明要点.** 由 log-sum-exp 的标准求导（在前述局部一致收敛条件下可交换求和与微分），得梯度与 Hessian 表达；方向二阶导即方差。熵恒等式由 $p_j\propto a_j e^{\langle\beta_j,\Re\rho\rangle}$ 代入 $H=-\sum p_j\log p_j$ 展开并整理得到。$\square$

---

### T24（相变/主导切换的判别）

**命题.** 令幅度 $A_j(\rho):=a_j e^{\langle\beta_j,\rho\rangle}$，并定义
$$
H_{jk}=\Big\{\rho:\ \langle\beta_j-\beta_k,\rho\rangle=\log\frac{a_k}{a_j}\Big\},\qquad
\delta(\rho):=\min_{j<k}\Big|\ \langle\beta_j-\beta_k,\rho\rangle-\log\frac{a_k}{a_j}\ \Big|.
$$
若 $\delta(\rho)>\log(J-1)$，则存在唯一索引 $j_\star$ 使 $A_{j_\star}(\rho)=\max_j A_j(\rho)$ 且
$$
\sum_{k\ne j_\star}A_k(\rho)<A_{j_\star}(\rho),
$$
因而无主导切换；主导切换仅可能发生在 $\{\rho:\ \delta(\rho)\le\log(J-1)\}$ 的薄带内，其骨架为超平面族 $\{H_{jk}\}$。

**证明.** 由 $\delta(\rho)$ 的定义，$\log A_{j_\star}-\log A_k\ge\delta(\rho)$，故 $A_k\le e^{-\delta(\rho)}A_{j_\star}$，再求和得结论。$\square$

---

### T25（方向化极点 = 增长指数）

**命题.** 固定方向 $\mathbf v$ 与分解 $\rho=\rho_\perp+s\mathbf v$。设沿 $\mathbf v$ 的带权累积分布
$$
M_{\mathbf v}(t)=\sum_{t_j\le t} w_j,\qquad t_j:=\langle-\beta_j,\mathbf v\rangle,\quad w_j:=a_j e^{\langle\beta_j,\rho_\perp\rangle},
$$
当 $t\to+\infty$ 具有指数–多项式渐近
$$
M_{\mathbf v}(t)=\sum_{\ell=0}^{L} Q_\ell(t)\,e^{\gamma_\ell t}+O\!\big(e^{(\gamma_L-\delta)t}\big),\qquad \gamma_0>\cdots>\gamma_L,
$$
且 $M_{\mathbf v}$ 具界变差并满足温和增长。则其拉普拉斯–Stieltjes 变换
$$
\mathcal L_{\mathbf v}(s):=\int_{(-\infty,+\infty)} e^{-s t}\,dM_{\mathbf v}(t)=\sum_j w_j e^{-s t_j}
$$
在 $\Re s>\gamma_0$ 收敛，并可亚纯延拓至 $\Re s>\gamma_L-\delta$，在 $s=\gamma_\ell$ 处至多出现 $\deg Q_\ell+1$ 阶极点。特别地，右端收敛垂线的实部等于最大增长指数 $\gamma_0$。

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

**7.9 由 $\omega$-自动机到叶-语言**：给定 Büchi 自动机 $\mathcal A=(Q,\Gamma,\delta,q_0,F)$，选择 $(\pi,\varsigma)$ 使：

1. $\pi$ 将跨叶观测编码为 $\Gamma$-字；
2. 以有限型同步条件实现 $\delta$（经 $X_f^{[k]}$ 将 $Q$ 编码入字母表并以局部约束模拟转移）；
3. 接受条件以安全/正则约束表达。于是
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f)=L_\omega(\mathcal A).
$$

---

## 8. 典型示例与玩具模型

**Rule-90（线性）**：三视角一致；任意锚的 SBU 由线性关系唯一递推；Følner 归一化后复杂度密度一致；叶-语言为 $\omega$-正则。

**Rule-110（通用）**：宏块-强制嵌入 TM（T6）；停机见证对应局部终止标记（T9）；逐叶推进排除同层备选（T19–T20）。

**二染色 CSP（模型视角）**：图二染色的局部约束 → 禁形；锚定某节点颜色并逐叶展开，构成因果一致事件锥体；叶-语言在适当条件下为 $\omega$-正则。

**2×2 玩具块（锚–SBU–译码–表观选择）**
$\Sigma=\{0,1\},\ d=1,\ N=\{-1,0,1\},\ f(a,b,c)=a\oplus b\oplus c$（XOR，周期边界）。锚 $v_0$ 固定 $(t=0,\mathbf r=0)$ 的局部图案。按 T4 的因果厚边界与**逐叶推进**递推 $t=1$ 层，得到唯一一致扩张；与锚矛盾的同层点被排除（T19）。取
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

EBOC 在极简公理下统一**无时间几何（永恒图/SFT）**、**静态块一致体**与**逐叶译码的观察-计算语义**，形成从**模型/自动机**到**可见语言**的完整链条。本文给出 T1–T20 的细化证明，确立了**信息不增律**（T4/A3）、**Brudno 对齐**（T5）、**unimodular 协变性**（T2/T10）、**事件锥体/静态块展开**（T14–T16）、**多锚观察者与坐标相对化**（T17–T18）等核心结果，并提供可复现实验与构造流程（§7）。

---

## 附录 A：术语与记号

* **语义塌缩**：$x\mapsto\mathcal O_{\pi,\varsigma}(x)$ 的信息因子化。
* **表观选择**：按 $\ell$ 的最小正增量推进，对同层备选作代表选择；仅改变语义代表，不创造信息。
* **原始整协向量**：$\tau^\star\in(\mathbb{Z}^{d+1})^\vee$，$\gcd(\tau^\star_0,\ldots,\tau^\star_d)=1$；其与实际时间方向 $\tau$ 的配对 $\langle\tau^\star,\tau\rangle=b\ge1$ 定义逐叶推进步长。
* **$\mathrm{GL}_{d+1}(\mathbb{Z})$**：整可逆矩阵群（行列式 $\pm1$）。
* **Følner 族**：$|\partial W_k|/|W_k|\to0$ 的窗口族。
* **柱集**：$[p]_W=\Big\{x\in X_f:\ x|_W=p\Big\}$。

---

## 参考文献（指引性）

* A. A. Brudno (1983). *Entropy and the complexity of trajectories*.
* D. Lind & B. Marcus. *Symbolic Dynamics and Coding*.
* E. F. Moore (1962); J. Myhill (1963). *Machine models / Reversible CA*.
* M. Li & P. Vitányi. *An Introduction to Kolmogorov Complexity*.
* R. Berger; J. Kari. *Tilings, Undecidability, SFT*.
* J. R. Büchi; W. Thomas; D. Perrin & J.-E. Pin. *$\omega$-Automata and $\omega$-Languages*.
* D. Ornstein & B. Weiss; E. Lindenstrauss（可加群作用的 SMB / 点态遍历）.
