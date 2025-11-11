# Gibbons–Hawking–York 边界项的必要性与推广：变分良定性、角点与零类边界，以及到准局域能与热力学的闭合

**Version: 1.6**

**MSC**：83C05；83C57；58A10；49S05

---

## 摘要

在具有（可能非光滑）边界的伪黎曼流形上，爱因斯坦—希尔伯特体作用的变分包含法向导数型边界通量，仅固定诱导度规 $h_{ab}$ 的狄里克雷数据不足以保证良定。本文在 Levi–Civita 联络与外挠曲率框架下，严格证明在非零类边界加入含取向因子 $\varepsilon:=n^\mu n_\mu\in\{\pm 1\}$ 的 Gibbons–Hawking–York（GHY）项后，所有法向导数贡献被抵消，从而对固定 $h_{ab}$ 的变分族建立驻定原理。对分段边界，给出关节（角点）项的统一字典并证明作用的可加性；对零类片段，以膨胀 $\theta$ 与表面引力 $\kappa$ 构造零类边界项，在常数重标度下不变，并阐明非常数重标度与横向超平移分别引入的端点与散度项及其补偿。随后在 ADM/Regge–Teitelboim 正则分解与协变相空间（Iyer–Wald、Wald–Zoupas）中证明：GHY/关节结构使哈密顿量可微，其边界生成元与 Brown–York 准局域应力一致；在同一边界条件类与同一代表下与协变荷相容。对 $f(R)$ 与 Lovelock（含 Gauss–Bonnet）理论，构造与 Dirichlet 数据匹配的边界—角点泛函并给出分段非光滑情况下的可加性命题。最后在欧几里得黑洞几何中，以显式的 $K$ 与参考 $K_0$ 计算，连同必要的关节与（AAdS 情形）反项，得到一致的自由能、能量与熵。附录提供逐步可复算的推导、取向—符号字典与协变相空间的 worked example。

---

## 0 记号、取向与数据类

* **时空与曲率**：$(\mathcal M,g_{\mu\nu})$ 为四维可定向伪黎曼流形，签名 $(-,+,+,+)$。Riemann 张量

$$
R^\rho{}_{\sigma\mu\nu}
=\partial_\mu\Gamma^\rho{}_{\sigma\nu}-\partial_\nu\Gamma^\rho{}_{\sigma\mu}
+\Gamma^\rho{}_{\lambda\mu}\Gamma^\lambda{}_{\sigma\nu}
-\Gamma^\rho{}_{\lambda\nu}\Gamma^\lambda{}_{\sigma\mu},
$$

$R_{\mu\nu}=R^\rho{}_{\mu\rho\nu}$，$R=g^{\mu\nu}R_{\mu\nu}$，$G_{\mu\nu}=R_{\mu\nu}-\tfrac12 R g_{\mu\nu}$。
* **非零类边界几何**：在边界片段 $\mathcal B$ 上取单位法向 $n^\mu$，$\varepsilon:=n^\mu n_\mu\in\{\pm 1\}$。诱导度规与外挠曲率

$$
h_{\mu\nu}=g_{\mu\nu}-\varepsilon\,n_\mu n_\nu,\qquad
K_{\mu\nu}=h_\mu{}^\alpha h_\nu{}^\beta\nabla_\alpha n_\beta,\qquad
K=h^{\mu\nu}K_{\mu\nu}.
$$

* **零类边界几何**：在 $\mathcal N$ 上取零向 $\ell^\mu$ 与辅助向量 $k^\mu$（$\ell\cdot k=-1$）。横截二维度规 $\gamma_{AB}$。形算子与膨胀

$$
W_{AB}:=\gamma_A{}^\mu\gamma_B{}^\nu\nabla_\mu\ell_\nu,\qquad
\theta:=\gamma^{AB}W_{AB},
$$

指标以 $\gamma_{AB}$ 升降；横截协变导数 $\mathcal D_A$ 与 Hájiček 一形式 $\omega_A:=-k_\mu\nabla_A\ell^\mu$ 由 rigging connection 诱导。

**参数与表面引力**：取 $\lambda$ 为沿生成矢量 $\ell$ 的参数，规定

$$
\partial_\lambda:=\ell^\mu\nabla_\mu.
$$

在保持规范 $\ell\cdot k=-1$ 下，表面引力定义为

$$
\boxed{\ \kappa:=-k_\mu\,\ell^\nu\nabla_\nu\ell^\mu\ },
$$

因而有 $\ell^\nu\nabla_\nu\ell^\mu=\kappa\,\ell^\mu$。

该定义与 §4 的重标度律相容：当 $\ell\to e^\alpha\ell$、$k\to e^{-\alpha}k$ 时，

$$
\theta\to e^\alpha\theta\quad\text{且}\quad\kappa\to e^\alpha(\kappa+\partial_\lambda\alpha).
$$

* **分段边界与关节**：$\partial\mathcal M=\bigcup_i\mathcal B_i$，$\mathcal C_{ij}=\mathcal B_i\cap\mathcal B_j$ 允许签名翻转或含零类片段。
* **边界数据（Dirichlet 类）**：非零类片段固定 $h_{ab}$；零类片段固定 Carroll 结构 $(\gamma_{AB},[\ell])$，其中 $[\ell]$ 按常数重标度 $\ell\to e^\alpha\ell$ 取等价类；各关节固定"角"（§3 的 $\eta$ 与 §4 的对数量角 $a$）。
* **测度**：体域 $\sqrt{-g}\,\mathrm d^4x$；非零类边界 $\sqrt{|h|}\,\mathrm d^3x$；零类边界 $\sqrt{\gamma}\,\mathrm d\lambda\,\mathrm d^2x$；关节 $\sqrt{\sigma}\,\mathrm d^2x$。

---

## 1 EH 体作用的变分与边界通量

$$
S_{\mathrm{EH}}=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}\,R\,\mathrm d^4x .
$$

一次变分

$$
\delta(\sqrt{-g}R)=\sqrt{-g}\,G_{\mu\nu}\delta g^{\mu\nu}
+\partial_\mu\left[\sqrt{-g}\left(g^{\alpha\beta}\delta\Gamma^\mu{}_{\alpha\beta}-g^{\mu\alpha}\delta\Gamma^\beta{}_{\alpha\beta}\right)\right],
$$

其中

$$
\delta\Gamma^\rho{}_{\mu\nu}
=\tfrac12 g^{\rho\sigma}\big(\nabla_\mu\delta g_{\sigma\nu}+\nabla_\nu\delta g_{\sigma\mu}-\nabla_\sigma\delta g_{\mu\nu}\big).
$$

边界项在切/法向分解后包含 $n^\mu\nabla_\mu\delta g_{\alpha\beta}$ 的不可约主项，单独 $S_{\mathrm{EH}}$ 在 Dirichlet 数据下不良定。

---

## 2 GHY 抵消与变分良定

$$
\boxed{S_{\mathrm{GHY}}[g]=\frac{\varepsilon}{8\pi G}\int_{\partial\mathcal M}\sqrt{|h|}\,K\,\mathrm d^3x}
$$

**变分设定（固定嵌入、单位法向规范）**：边界几何位置保持不变，仅变度规；因此

$$
\delta(n_\mu n^\mu)=0,\qquad
\boxed{\ \delta n_\mu=\tfrac12\,\varepsilon\,n_\mu\,n^\alpha n^\beta\,\delta g_{\alpha\beta}\ } .
$$

该设定与 Dirichlet 数据（固定 $h_{ab}$）相容，并使 $S_{\mathrm{GHY}}$ 与关节项逐项抵消边界通量。

**定理 2.1（GHY 抵消）**
对固定 $\delta h_{ab}=0$ 的变分类，

$$
\delta\left(S_{\mathrm{EH}}+S_{\mathrm{GHY}}\right)
=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}\,G_{\mu\nu}\,\delta g^{\mu\nu}\,\mathrm d^4x .
$$

证明见附录 B 的逐项配平。
**自检提示**：将附录 A 的主项 $n^\rho h^{\mu\alpha}h^{\nu\beta}\nabla_\rho\delta g_{\alpha\beta}$ 与附录 B 中由
$\delta n_\mu=\tfrac12\varepsilon n_\mu n^\alpha n^\beta\delta g_{\alpha\beta}$ 导致的 $\delta K_{ab}$ 之含 $\nabla\delta g$ 项逐项对齐，可直接复算抵消。

---

## 3 分段边界、签名翻转与角点可加性

**非零—非零关节的分段角字典**：设两片段外法向为单位向量 $n_1,n_2$，其因果型分别由 $\varepsilon_i:=n_i^2\in\{\pm1\}$ 标记。则关节角 $\eta$ 定义为

$$
\eta=
\begin{cases}
\operatorname{arccosh}\big(-n_1\cdot n_2\big), & \varepsilon_1=\varepsilon_2=-1\quad(\text{两片段类空，法向类时}),\\[4pt]
\arccos\big(n_1\cdot n_2\big), & \varepsilon_1=\varepsilon_2=+1\quad(\text{两片段类时，法向类空}),\\[4pt]
\operatorname{arcsinh}\big(n_T\cdot n_S\big), & \varepsilon_1\varepsilon_2=-1\quad(\text{混合因果；}n_T^2=-1,\ n_S^2=+1).
\end{cases}
$$

角点项取

$$
\boxed{S_{\mathrm{corner}}^{(nn)}=\frac{1}{8\pi G}\int_{\mathcal C}\sqrt{\sigma}\,\eta\,\mathrm d^2x},
$$

取向与号差由母公式与取向表统一固定。

**零—非零与零—零关节**：对数量角

$$
a_{(n\ell)}=\ln|-\ell\cdot n|,\qquad
a_{(\ell\ell)}=\ln\Big|-\tfrac12\,\ell_1\cdot\ell_2\Big|,
$$

关节项分别为 $\tfrac{1}{8\pi G}\int_{\mathcal C}\sqrt{\sigma}\,a\,\mathrm d^2x$。

**定理 3.1（可加性与必要性）**
在固定相应角（$\eta$ 或 $a$）的边界数据下，

$$
S_{\mathrm{EH}}+S_{\mathrm{GHY}}+S_{\mathrm{corner/joint}}
$$

的变分良定，并满足可加性

$$
S[\mathcal M_1\cup_{\Sigma}\mathcal M_2]=S[\mathcal M_1]+S[\mathcal M_2] .
$$

关节项在任意 $C^1$ 正则化极限下不变，独立于正则器细节。

---

## 4 零类边界：$\theta+\kappa$ 结构、重标度与端点补偿

$$
\boxed{S_{\mathcal N}=\frac{1}{8\pi G}\int_{\mathcal N}\sqrt{\gamma}\,(\theta+\kappa)\,\mathrm d\lambda\,\mathrm d^2x}
$$

**定理 4.1（零类良定性）**
固定 $(\gamma_{AB},[\ell])$ 时，$\delta(S_{\mathrm{EH}}+S_{\mathcal N})$ 不含法向导数残项。

**纯重标度**（保持 $\ell\cdot k=-1$，不含横向分量）：

$$
\ell\to e^\alpha\ell,\quad k\to e^{-\alpha}k
\ \Rightarrow
W_{AB}\to e^\alpha W_{AB},\quad \theta\to e^\alpha\theta,\quad \kappa\to e^\alpha(\kappa+\partial_\lambda\alpha).
$$

当 $\alpha=\text{const}$ 时，$\int_{\mathcal N}\sqrt{\gamma}(\theta+\kappa)\,\mathrm d\lambda\,\mathrm d^2x$ 与关节项之和不变；当 $\alpha=\alpha(\lambda)$ 时，产生端点全变分，可由对数量角的 counterterm 吸收（见附录 D；路径 B 取 $\ln(\ell_c|\Theta|)$ 并要求 $\Theta$ 保号，若 $\Theta$ 过零则改用路径 A 的端点/关节补偿）。

**横向超平移/截面重参数**：

$$
\ell\to e^\alpha(\ell+v^A e_A)\ \Rightarrow\ \theta\to e^\alpha(\theta+\mathcal D_A v^A),
$$

该项属于截面重定义效应，与上段纯重标度区分处理。**维数注记**：在 $D$ 维时，横截空间维数为 $D-2$，相应散度结构按维数作直推推广。

**零类 Brown–York 应力**：

$$
T^A{}_B\big|_{\mathcal N}=-\frac{1}{8\pi G}\Big(W^A{}_B-\theta\,\delta^A{}_B\Big),
$$

满足以 rigging connection 定义的横截守恒式，并与零类 Wald–Zoupas 荷在同一边界条件类下相容。

---

## 5 正则形式：可微哈密顿量与准局域能

在 $3+1$ 分解下，仅 $S_{\mathrm{EH}}$ 时哈密顿量泛函不可微；加入 $S_{\mathrm{GHY}}$ 与必要关节/零类项后，得

**定理 5.1（可微性与边界生成元）**
在 Dirichlet 数据与本文取向/正则性假设下，若取作用

$$
S=S_{\mathrm{EH}}+S_{\mathrm{GHY}}+S_{\mathrm{joint}}(+S_{\mathcal N})
$$

而**不引入任何仅依赖边界内禀度规 $h_{ab}$ 的本征边界泛函**，则哈密顿量 $H_\xi$ 在相空间 Fréchet 可微，其边界生成元**唯一**由

$$
T^{ab}_{\mathrm{BY}}=\frac{1}{8\pi G}(K^{ab}-Kh^{ab})
$$

给出。

若在同一边界条件类内加入/减去本征项（如第 9 节的 $S_{\mathrm{ct}}$、参考项 $S_{\mathrm{ref}}$），则 $H_\xi$ 仍可微，且边界生成元相应改为

$$
T^{ab}_{\mathrm{BY,ren}}=T^{ab}_{\mathrm{BY}}+T^{ab}_{\mathrm{ct}}-T^{ab}_{\mathrm{ref}},
$$

与第 6 节协变相空间分析及第 9 节重整反项保持一致。

类空截面 $\mathcal S$ 的能量

$$
E_{\mathrm{BY}}=\int_{\mathcal S}\sqrt{\sigma}\,u_a u_b\,T^{ab}_{\mathrm{BY}}\,\mathrm d^2x
$$

在渐近平坦极限下趋于 ADM 质量。

---

## 6 协变相空间与代表无关性

$$
\delta\mathbf L=\mathbf E\cdot\delta\phi+\mathrm d\boldsymbol\Theta(\phi,\delta\phi),\qquad
\mathbf J_\xi=\boldsymbol\Theta(\phi,\mathcal L_\xi\phi)-\xi\cdot\mathbf L=\mathrm d\mathbf Q_\xi .
$$

若 $\mathbf L\to\mathbf L+\mathrm d\mathbf B$，则 $\boldsymbol\Theta\to\boldsymbol\Theta+\delta\mathbf B$、$\mathbf Q_\xi\to\mathbf Q_\xi+\xi\cdot\mathbf B$。在同一边界条件类与同一（或规范等价）代表下，质量、角动量与地平线熵不变；通量边界采用 Wald–Zoupas 修正以保证可积性。

**骨架式（可微性来源定位）**：在 Regge–Teitelboim 框架下，

$$
\delta H_\xi=\int_{\Sigma}(\text{约束}\cdot\delta\phi)\,\mathrm d^3x
+\oint_{\partial\Sigma}\Big(\Pi^{ab}\delta h_{ab}+\cdots\Big)\,\mathrm d^2x .
$$

仅体项时边界变分含 $\Pi^{ab}\delta h_{ab}$ 与法向导数项而不可微；加入 $S_{\mathrm{GHY}}$（及关节/零类项）后，上式边界变分化为 BY 表面生成元，从而 $H_\xi$ 可微。

**Worked Example（代表无关性的算式链）**
取静态黑洞与 Killing 场 $\xi=\partial_t$，在无穷远 $\mathcal I$ 与地平线 $\mathcal H$ 两端：

$$
\delta H_\xi
=\int_{\mathcal S_\infty}\big(\delta\mathbf Q_\xi-\xi\cdot\boldsymbol\Theta\big)
-\int_{\mathcal S_{\mathcal H}}\big(\delta\mathbf Q_\xi-\xi\cdot\boldsymbol\Theta\big).
$$

若 $\mathbf L\mapsto \mathbf L+\mathrm d\mathbf B$，则

$$
\boldsymbol\Theta\mapsto \boldsymbol\Theta+\delta\mathbf B,\qquad
\mathbf Q_\xi\mapsto \mathbf Q_\xi+\xi\cdot\mathbf B,
$$

并且 $\delta(\xi\cdot\mathbf B)=\xi\cdot\delta\mathbf B$，故两端增量分别为零，$\delta H_\xi$ 不变；若存在通量边界，则以 Wald–Zoupas 改正使端点差为零，从而恢复可积性。

**重整后的 BY 表面应力**

$$
T^{ab}_{\mathrm{BY,ren}}
=\frac{2}{\sqrt{|h|}}\frac{\delta\big(S_{\mathrm{GHY}}+S_{\mathrm{joint}}+S_{\mathrm{ct}}-S_{\mathrm{ref}}\big)}{\delta h_{ab}}
= T^{ab}_{\mathrm{BY}} + T^{ab}_{\mathrm{ct}} - T^{ab}_{\mathrm{ref}},
$$

其中\quad
$T^{ab}_{\mathrm{ct}}:=\dfrac{2}{\sqrt{|h|}}\dfrac{\delta S_{\mathrm{ct}}}{\delta h_{ab}},\qquad
T^{ab}_{\mathrm{ref}}:=\dfrac{2}{\sqrt{|h|}}\dfrac{\delta S_{\mathrm{ref}}}{\delta h_{ab}}$。

四维 AAdS 的最小反项见 §9。

---

## 7 $f(R)$ 重力：Dirichlet 兼容边界—关节

以 $\Phi=f'(R)$ 的标量—张量等价

$$
S=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}\,(\Phi R-V(\Phi))\,\mathrm d^4x .
$$

在固定 $(h_{ab},\Phi)$ 的 Dirichlet 数据下，

$$
S^{f(R)}_{\mathrm{bdy}}=\frac{1}{8\pi G}\int_{\partial\mathcal M}\varepsilon\,\sqrt{|h|}\,\Phi\,K\,\mathrm d^3x,\qquad
S^{f(R)}_{\mathrm{joint}}=\frac{1}{8\pi G}\sum_{\mathcal C}\int_{\mathcal C}\sqrt{\sigma}\,\Phi\,(\text{角})\,\mathrm d^2x .
$$

若改为固定 $(h_{ab},n^\mu\nabla_\mu\Phi)$ 等 Robin 型数据，则需在边界加上 $\propto \sqrt{|h|}\,n^\mu\nabla_\mu\Phi$ 的补偿项，并相应加权关节项（附录 G）。

---

## 8 Lovelock（Gauss–Bonnet）重力与分段非光滑可加性

对 $D\ge 5$ 的 Gauss–Bonnet（GB）项，

$$
S_{\mathrm{GB}}=\frac{\alpha}{16\pi G}\int_{\mathcal M}\sqrt{-g}\,\big(R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}-4R_{\mu\nu}R^{\mu\nu}+R^2\big)\,\mathrm d^D x,
$$

其 Dirichlet 兼容的 Myers 型边界项

$$
S^{\mathrm{GB}}_{\mathrm{bdy}}=\frac{\alpha}{8\pi G}\int_{\partial\mathcal M}\varepsilon\,\sqrt{|h|}\,\Big(2\,\widehat G_{ab}K^{ab}+J\Big)\,\mathrm d^{D-1}x,
$$

$\widehat G_{ab}$ 为 $h_{ab}$ 的 Einstein 张量，

$$
J^{ab}=\tfrac13\Big(2KK^{ac}K_c{}^b+K_{cd}K^{cd}K^{ab}-2K^{ac}K_{cd}K^{db}-K^2K^{ab}\Big),\qquad J=h_{ab}J^{ab}.
$$

**命题 8.1（GB 的可加性，分段非光滑）**
取上式边界项并增添相应 GB 关节多项式（由角 $\eta$/对数量角 $a$ 与 $(K,\widehat{\mathcal R})$ 的二次组合构成），则在固定 Dirichlet 数据下

$$
S_{\mathrm{GB}}[\mathcal M_1\cup_\Sigma\mathcal M_2]=S_{\mathrm{GB}}[\mathcal M_1]+S_{\mathrm{GB}}[\mathcal M_2] .
$$

思路：对各分片作分部，关节处出现 $\propto\delta(\text{角})$ 的残项；所选 GB 关节多项式之变分精确抵消该残项。代表见 Deruelle–Merino–Olea（2018）。

---

## 9 非紧边界与 AAdS 反项（四维最小代表）

$$
\boxed{S_{\mathrm{ct}}=\frac{1}{8\pi G}\int_{\partial\mathcal M}\sqrt{|h|}\left(\frac{2}{L}+\frac{L}{2}\,\widehat{\mathcal R}\right)\mathrm d^3x}
$$

其中 $L$ 为 AdS 曲率半径，$\widehat{\mathcal R}$ 为边界内禀 Ricci 标量。该代表与 kounterterms/全息重整化在四维下等价于给出相同的有限应力与保角无关项；高维需加入更高次曲率反项。

---

## 10 分布曲率、薄壳与零测度"边界之边界"

若 $K_{ab}$ 沿某超曲面存在跳跃，体域曲率出现 $\delta$ 型分布；其在作用中的贡献由关节/薄壳项吸收。类时/类空薄壳满足 Israel 条件 $[K_{ab}-Kh_{ab}]=-8\pi G\,S_{ab}$；零类薄壳满足 Barrabès–Israel 条件。本文关节与零类规则与之兼容。

---

## 11 欧几里得黑洞：$K$、$K_0$、自由能与熵

以 Schwarzschild 欧氏几何

$$
\mathrm ds^2=f(r)\,\mathrm d\tau^2+f(r)^{-1}\,\mathrm dr^2+r^2\,\mathrm d\Omega_2^2,\qquad f(r)=1-\frac{2M}{r},
$$

截断于 $r=R$、$\tau\in[0,\beta]$。外向单位法向 $n^\mu=\sqrt{f}\,\delta^\mu_r$ 下，

$$
\boxed{K(R)=\frac{2\sqrt{f(R)}}{R}+\frac{f'(R)}{2\sqrt{f(R)}}},\qquad
\boxed{K_0(R)=\frac{2}{R}}.
$$

总作用

$$
I_E=I_{\mathrm{EH}}+I_{\mathrm{GHY}}[K]+I_{\mathrm{joint}}-I_{\mathrm{ref}}[K_0].
$$

去锥缺陷 $\beta=8\pi M$ 与 $R\to\infty$ 的有限部分给出

$$
F=\frac{I_E}{\beta}=\frac{M}{2},\qquad E=\partial_\beta(\beta F)=M,\qquad S=\beta(E-F)=\frac{\mathcal A}{4G}.
$$

**周期识别不双计**：由于 $\tau\sim\tau+\beta$，侧边 $r=R$ 处 $(R,0)$ 与 $(R,\beta)$ 为等价角点；按区间 $[0,\beta]$ 分部积分得到的两处角项之和等于在周期流形上单角点的贡献，不发生双计。

---

## 12 变分良定与 PDE/Fredholm 之别

本文建立的是作用一次变分在给定边界数据集上的闭合；而 PDE 适定性与 Fredholm 性需函数空间与边值算子分析。紧致边界上纯 Dirichlet/Neumann 映射一般非 Fredholm；自然混合数据（如 $([\gamma],H)$ 或 Bartnik 数据）更合适。本文工作限定于变分良定层面；附录 L 给出说明性示例。

---

# 附录（编号化推导、字典与范例）

> 统一说明：所有积分显式写出测度 $\mathrm d^n x$；集合写法统一为 $\{\pm 1\}$；母公式 $S_{\mathrm{GHY}}=(8\pi G)^{-1}\varepsilon\int\sqrt{|h|}\,K\,\mathrm d^3x$ 与取向表唯一固定号差。

## 附录 A：EH 作用的边界通量（逐项分解）

**A.1** $\delta S_{\mathrm{EH}}=(16\pi G)^{-1}\int_{\mathcal M}\big[\delta(\sqrt{-g})\,R+\sqrt{-g}\,\delta R\big]\mathrm d^4x$，$\delta\sqrt{-g}=-\tfrac12\sqrt{-g}\,g_{\mu\nu}\delta g^{\mu\nu}$。
**A.2** $\delta R=R_{\mu\nu}\delta g^{\mu\nu}+\nabla_\mu\big(g^{\alpha\beta}\delta\Gamma^\mu{}_{\alpha\beta}-g^{\mu\alpha}\delta\Gamma^\beta{}_{\alpha\beta}\big)$。
**A.3** 斯托克斯公式给出边界项 $(16\pi G)^{-1}\int_{\partial\mathcal M}\sqrt{|h|}\,n_\mu(\cdots)\mathrm d^3x$。
**A.4** 投影 $h_\mu{}^\nu=\delta_\mu{}^\nu-\varepsilon n_\mu n^\nu$ 将边界通量写为

$$
\int_{\partial\mathcal M}\sqrt{|h|}\left[\Pi^{ab}\delta h_{ab}
+n^\rho h^{\mu\alpha}h^{\nu\beta}\nabla_\rho\delta g_{\alpha\beta}
+\cdots\right]\mathrm d^3x .
$$

## 附录 B：GHY 的抵消与实例取向表

**B.1** $\delta(\sqrt{|h|}K)=\sqrt{|h|}\big(\delta K+\tfrac12 K\,h^{ab}\delta h_{ab}\big)$，$\delta K=h^{ab}\delta K_{ab}-K^{ab}\delta h_{ab}$，其中

$$
\delta K_{ab}=h_a{}^\mu h_b{}^\nu\big(\nabla_\mu\delta n_\nu+\delta\Gamma^\rho{}_{\mu\nu}n_\rho\big).
$$

**B.2** 代入单位法向规范

$$
\boxed{\ \delta n_\mu=\tfrac12\,\varepsilon\,n_\mu\,n^\alpha n^\beta\,\delta g_{\alpha\beta}\ },
$$

将 $\delta K$ 中的 $\nabla\delta g$ 与附录 A 主项逐项相消，同时 $\Pi^{ab}\delta h_{ab}$ 互消，得定理 2.1。
**B.3 实例取向表**

| 片段 | 因果型 | $n^2=\varepsilon$ | 外法向 | GHY 权重 |
|------|--------|-------------------|--------|----------|
| 初/末空间片 | 类空 | $-1$ | 未来/过去 | $-\int\sqrt{\|h\|}\,K\,\mathrm d^3x$ |
| 侧边 | 类时 | $+1$ | 指向外侧 | $+\int\sqrt{\|h\|}\,K\,\mathrm d^3x$ |
| 欧氏边界 | Riemann | $+1$ | 指向外侧 | $+\int\sqrt{\|h\|}\,K\,\mathrm d^3x$ |

（此表仅为阅读指引；实际计算统一使用母公式。）

## 附录 C：三类关节与可加性（字典与证明提纲）

* 非零—非零：$\eta$ 依因果型分段定义（见 §3）；角点项 $\tfrac{1}{8\pi G}\int\sqrt{\sigma}\,\eta\,\mathrm d^2x$。
* 零—非零：$a=\ln|-\ell\cdot n|$。
* 零—零：$a=\ln|-\tfrac12\ell_1\cdot\ell_2|$。
* 分片 GHY 分部后仅余 $\propto\delta(\text{角})$ 的端点项，由关节项抵消，作用可加；结果独立于关节正则器细节。

## 附录 D：零类重标度、端点补偿与超平移

**D.1 纯重标度** $\ell\to e^{\alpha(\lambda)}\ell,\ k\to e^{-\alpha(\lambda)}k$：$\theta\to e^\alpha\theta$，$\kappa\to e^\alpha(\kappa+\partial_\lambda\alpha)$。常数 $\alpha$ 下不变；非常数产生端点全变分。
**D.2 路径 A（LMPS 端点/关节补偿）**：

$$
S_{\mathrm{end}}=\frac{1}{8\pi G}\sum_{\text{端点}}\int\sqrt{\sigma}\,\alpha\,\mathrm d^2x .
$$

**D.3 路径 B（对数反项）**：

$$
S_{\mathrm{reparam}}=\frac{1}{8\pi G}\int_{\mathcal N}\sqrt{\gamma}\,\Theta\ln\big(\ell_c|\Theta|\big)\,\mathrm d\lambda\,\mathrm d^2x,\qquad \Theta:=\theta .
$$

注：路径 B 需各生成线 $\Theta$ 保持定号；若 $\Theta$ 过零（如在焦点），应将过零点视为关节并按 D.2 的端点/关节补偿处理，或改用路径 A。

**D.4 横向超平移** $\ell\to e^\alpha(\ell+v^A e_A)$ 引入 $\mathcal D_A v^A$，归入截面重定义。

## 附录 E：Regge–Teitelboim 可微性与 BY 生成元

$$
\delta H_\xi=\int_{\Sigma}(N\,\delta\mathcal H+N^i\,\delta\mathcal H_i)\,\mathrm d^3x
+\int_{\partial\Sigma}\sqrt{\sigma}\,\Big(\varepsilon\,\delta N+j_i\,\delta N^i+T^{ab}_{\mathrm{BY}}\delta h_{ab}\Big)\,\mathrm d^2x .
$$

加入 GHY/关节后 $H_\xi$ 可微并生成正确演化；渐近平坦下 $E_{\mathrm{BY}}\to M_{\mathrm{ADM}}$。

## 附录 F：协变相空间——代表自由与 worked example

**F.1 代表自由**：$\mathbf L\to\mathbf L+\mathrm d\mathbf B\Rightarrow \boldsymbol\Theta\to\boldsymbol\Theta+\delta\mathbf B$、$\mathbf Q_\xi\to\mathbf Q_\xi+\xi\cdot\mathbf B$。能荷元 $\bm{k}_\xi:=\delta\mathbf Q_\xi-\xi\cdot\boldsymbol\Theta$ 保持不变。
**F.2 worked example（静态黑洞）**：正文 §6 已给出两端相消链；通量边界以 Wald–Zoupas 改正恢复可积性，由此得第一定律与 $\mathcal S=\mathcal A/(4G)$。

## 附录 G：$f(R)$/Lovelock 的边界—关节对照

**G.1 $f(R)$**：Dirichlet：$S^{f(R)}_{\mathrm{bdy}}=(8\pi G)^{-1}\int\varepsilon\sqrt{|h|}\,\Phi K\,\mathrm d^3x$，关节 $\propto \Phi\,(\eta\ \text{或}\ a)$。Robin：增添 $\propto \sqrt{|h|}\,n^\mu\nabla_\mu\Phi$ 及其关节对偶项。
**G.2 Gauss–Bonnet（$D\ge 5$）**：$S^{\mathrm{GB}}_{\mathrm{bdy}}=(8\pi G)^{-1}\alpha\int\varepsilon\sqrt{|h|}\,(2\widehat G_{ab}K^{ab}+J)\,\mathrm d^{D-1}x$，分段非光滑下的 GB 关节多项式确保命题 8.1 的可加性（系数由 Chern–Weil/transgression 固定；参见 Deruelle–Merino–Olea, 2018）。

## 附录 H：Schwarzschild 欧几里得作用（含 $K$ 与 $K_0$）

$\mathrm ds^2=f\,\mathrm d\tau^2+f^{-1}\mathrm dr^2+r^2\,\mathrm d\Omega_2^2$，$f=1-2M/r$。
$K(R)=\dfrac{2\sqrt{f(R)}}{R}+\dfrac{f'(R)}{2\sqrt{f(R)}}$，$K_0(R)=\dfrac{2}{R}$。
$I_E=I_{\mathrm{EH}}+I_{\mathrm{GHY}}[K]-I_{\mathrm{ref}}[K_0]+I_{\mathrm{joint}}\Rightarrow F=M/2,\ E=M,\ S=\mathcal A/(4G)$。
周期识别不双计说明见正文 §11。

## 附录 I：AAdS 反项与全息/准局域应力一致

四维 AAdS 的最小反项见 §9；该代表与全息应力一致，给出有限的 $T^{ab}_{\mathrm{BY,ren}}$。

## 附录 L：PDE/Fredholm 的说明性示例

紧致边界上纯 Dirichlet/Neumann 的 Einstein 约束映射一般非 Fredholm；自然混合数据（如 $([\gamma],H)$、Bartnik 数据）可得 Fredholm 结构。本文之"变分良定"不蕴含 PDE 适定。

---

## 参考文献（代表性）

* York, J. W., *Phys. Rev. Lett.* 28 (1972) 1082.
* Gibbons, G. W.; Hawking, S. W., *Phys. Rev. D* 15 (1977) 2752.
* Brown, J. D.; York, J. W., *Phys. Rev. D* 47 (1993) 1407.
* Hawking, S. W.; Horowitz, G. T., *Class. Quantum Grav.* 13 (1996) 1487.
* Hayward, G., *Phys. Rev. D* 47 (1993) 3275.
* Jubb, I.; Samuel, J.; Sorkin, R. D.; Surya, S., *Class. Quantum Grav.* 34 (2017) 065006.
* Lehner, L.; Myers, R. C.; Poisson, E.; Sorkin, R. D., *Phys. Rev. D* 94 (2016) 084046.
* Parattu, K.; Chakraborty, S.; Majhi, B. R.; Padmanabhan, T., *Gen. Rel. Grav.* 48 (2016) 94.
* Regge, T.; Teitelboim, C., *Ann. Phys.* 88 (1974) 286–318.
* Iyer, V.; Wald, R. M., *Phys. Rev. D* 50 (1994) 846；Wald, R. M., *Phys. Rev. D* 48 (1993) R3427.
* Wald, R. M.; Zoupas, A., *Phys. Rev. D* 61 (2000) 084027.
* Chandrasekaran, V.; Flanagan, É. É.; Shehzad, I.; Speranza, A. J., *JHEP* 01 (2022) 029.
* Dyer, E.; Hinterbichler, K., *Phys. Rev. D* 79 (2009) 024028.
* Guarnizo, A.; Castañeda, L.; Tejeiro, J. M., *Gen. Rel. Grav.* 42 (2010) 2713–2728.
* Myers, R. C., *Phys. Rev. D* 36 (1987) 392–396.
* Deruelle, N.; Merino, N.; Olea, R., *Phys. Rev. D* 97 (2018) 104009.
* Balasubramanian, V.; Kraus, P., *Commun. Math. Phys.* 208 (1999) 413–428.
* Skenderis, K., *Class. Quantum Grav.* 19 (2002) 5849–5876.
* Israel, W., *Il Nuovo Cimento B* 44 (1966) 1–14；Barrabès, C.; Israel, W., *Phys. Rev. D* 43 (1991) 1129–1142.

---

**说明**：全文统一移除占位符号与非常规标点（包括 `*`、以感叹号控制的负紧空格以及积分被积之间的逗号），所有定义式、投影与变分（含 $\delta\Gamma$、$\delta K_{ab}$ 与主项投影）均使用标准上下标与导数写法，并与"固定嵌入、单位法向规范"的 Dirichlet 数据自洽。
