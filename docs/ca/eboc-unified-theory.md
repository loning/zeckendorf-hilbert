# EBOC：永恒–静态块 观察-计算 统一理论

**作者**：Auric
**日期**：2025-10-18

---

## 摘要

**目标.** 提出 **EBOC（Eternal-Block Observer-Computing）**：一个无需显式全局时间的几何—信息统一框架，将**永恒图元胞自动机**（EG-CA）的**无时间因果编码**与**静态块宇宙元胞自动机**（SB-CA）的**程序语义与观察-译码**合并于同一形式系统，并给出可验证的信息律与构造算法。

**三大支柱.**

1. **几何编码（Graph/SFT）**：宇宙作为满足局部规则 $f$ 的**静态块** $X_f\subset\Sigma^{\mathbb{Z}^{d+1}}$；其因果/一致性由**永恒图** $G=(V,E)$ 与**子移位（SFT）**并行刻画。
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
其中 $X_f$ 为空间-时间 SFT，$G$ 为永恒图，$\rho$ 给出**可接受叶族**（原始整协向量 $\tau^\star$ 的水平集，$\langle\tau^\star,\tau\rangle=b\ge1$），$\pi$ 为译码器，$\mu$ 为移位不变遍历测度，$\nu$ 为通用半测度（仅作典型性权重）。

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
X_f^{(v,\tau)}:=\Big\{x\in X_f:\ x\big|_{\varphi_{v_0}(\mathrm{Cone}^+_{\ell}(v))}\ \text{与 }v\ \text{一致}\Big\}.
$$

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

### T2（Unimodular 协变性；可描述窗口族）

**命题.** 若 Følner 族 $\{W_k\}$ 满足 $K(W_k)=O(\log|W_k|)$，则任意两组可接受叶所致观察语义复杂度差为 $O(\log|W_k|)$，归一化后趋 0；熵不增保持。

**证明.** 两组叶由 $U_1,U_2\in\mathrm{GL}_{d+1}(\mathbb Z)$ 给出。置 $U=U_2U_1^{-1}$。对每个 $W_k$，$\tilde W_k=U(W_k)$ 可由描述 $\langle U\rangle$ 与 $W_k$ 的编码恢复，故
$$
\big|K(\pi(x|_{\tilde W_k}))-K(\pi(x|_{W_k}))\big|\ \le\ K(\langle U\rangle)+O(\log|W_k|)=O(\log|W_k|),
$$
由引理 5.1–5.2。归一化后极限为 0。熵不增由引理 5.4 给出。$\square$

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

### T13（叶-语言的 $\omega$-自动机刻画）

**命题.** 在"一维子作用 + 有限型/正则安全"下，存在 Büchi/Streett 自动机 $\mathcal A$ 使
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f)=L_\omega(\mathcal A).
$$

**证明（构造）.** 取高阶块表示 $X_f^{[k]}$，将状态集 $Q$ 编码入扩展字母表并以有限型约束实现转移 $\delta$。跨叶一次读取对应一次自动机步。接受条件以局部安全/正则约束实现（如"无限次访问 $F$"由循环记忆位实现）。于是得到等价 $\omega$-语言。$\square$

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

**命题.** 有效步长 $b=\langle\tau^\star,\tau\rangle\ge 1$ 反映章节节拍；不同 $b$ 仅改变读取节奏，Følner 归一化后熵率一致。

**证明.** 时间子作用改为 $\sigma_{\mathrm{time}}^{(b)}$ 等效于对 $\mathbb{Z}$ 子作用"抽样"（$\sigma_\Omega^b$）。测度熵满足
$$
h(\sigma_\Omega^b)\ =\ b\cdot h(\sigma_\Omega).
$$
而 $|W_k|$ 在"每步跨 $b$"下同样线性缩放，归一化后抵消，极限一致。$\square$

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
