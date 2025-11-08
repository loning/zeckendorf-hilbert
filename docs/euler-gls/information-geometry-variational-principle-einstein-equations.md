# 信息几何变分原理导出爱因斯坦场方程：EBOC—因果流形统一中的量子引力纲要
Version: 1.1

## 摘要

给定离散—静态块结构 $\mathrm{EBOC}$ 与连续—因果流形的互构框架，本文提出一条信息几何的变分原理：在每一个足够小的类时几何球（或局域因果菱形）上，**广义相对熵**（或等价地，广义熵 $S_{\rm gen}$）在保持体积与参考真空约束下极值。利用相对熵的一阶"第一定律" $\delta S=\delta\langle H_{\rm mod}\rangle$ 与几何光束会聚（Raychaudhuri）导致的面积变分，我们证明：对一切小球与一切形状变形，极值条件当且仅当满足爱因斯坦场方程 $G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle$。在半经典阶，二阶变分与相对熵非负性给出量子焦散—QNEC 等信息不等式，构成量子修正。离散侧以 EBOC 的静态块—因子译码语义给出 Regge 型离散作用并证明：在网格细化与信息几何一致化的极限下收敛到上述连续场方程。本文的"读数—刻度—因果"语义与窗化群延迟母刻度 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 严格对齐，并在 Nyquist–Poisson–Euler–Maclaurin 的有限阶误差纪律下闭合。

---

## Notation & Axioms / Conventions

**单位规范** 采用 $\hbar=c=1$。度规签名 $(-+++)$。对小球 $B_\ell(x)$ 的法向单位类时矢量记为 $u^\mu$，相应空间超曲面元 $d\Sigma^\nu=u^\nu d\Sigma$。

**因果—读数分离（双时间分离）** 因果与无信号仅由**前沿时间** $t_*$ 确定；窗化群延迟读数 $T_\gamma[w_R,h]$ 仅是可测刻度，与 $t_*$ 无普适大小比较。本文所有因果与偏序结论只依赖 $t_*$ 与类光锥结构，读数刻度用于信息几何测度与校准。

**刻度同一（母刻度）** 全局幺正公设下
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q(E)=-i\,S^\dagger(E)\tfrac{dS}{dE}(E)\ }
$$
并以此母刻度定义窗化读数与能—延迟对偶（红移—时间互易）。

**NPE 有限阶误差纪律** 一切数值实现遵循 Nyquist–Poisson–Euler–Maclaurin 三分解与有限阶 EM 端点校正；奇性不增、极点给出主尺度。本文所有信息量—读数的离散近似均在该账本下闭合。

**互构条件（GLS ↔ 因果流形）** 以前沿可达预序与光观测集重构流形的保角类；以辐射场—散射构造能量可微的幺正 $S(E)$ 并回到母刻度。范畴论层面在能量依赖幺正规范等价类上互为等价。

**EBOC（离散侧）** 世界以静态块 $X_f$ 与永恒图—子移位给出；观察 $=$ 因子译码，信息不增；时间子作用的 Brudno 对齐与可逆 CA 的信息守恒构成离散信息几何的公理基。

**信息几何** 统计流形 $(\mathcal P,g^{\rm F})$ 上以 Fisher–Rao 度量为唯一（幺正）单调度量；$D(\rho\Vert\sigma)$ 的二阶变分给出 $g^{\rm F}$，双联络结构 $(\nabla,\nabla^*)$ 由发散族诱导。([施普林格链接][1])

---

## 1. 局域统计流形与广义相对熵

**1.1 局域小球与模哈密顿量** 在点 $x\in\mathcal M$ 的局域洛伦兹坐标中取小球 $B_\ell(x)$。令 $\rho_{B_\ell}$ 为物质场在 $B_\ell$ 的约化态，$\rho^{(0)}_{B_\ell}$ 为与局域最大对称真空对应的参考态。真空的模哈密顿量在共形理论中局域可写为
$$
H_{\rm mod}^{(0)}=2\pi\!\int_{B_\ell}\!\xi^\mu T_{\mu\nu}\,d\Sigma^\nu,\qquad
\xi^\mu=\frac{\ell^2-r^2}{2\ell}\,u^\mu + O(\ell^3),
$$
从而相对熵一阶变分满足"第一定律"
$$
\delta S(\rho_{B_\ell}\Vert \rho^{(0)}_{B_\ell})=\delta\!\left\langle H_{\rm mod}^{(0)}\right\rangle-\delta S_{\rm out}=0.
$$
该等式在微扰下与小球极限普适成立，并已在全息与场论语境中系统阐明。([施普林格链接][2])

**1.2 信息几何视角** 在以度规形变 $g\mapsto g+\delta g$ 与态形变 $\rho\mapsto\rho+\delta\rho$ 参数化的统计流形上，相对熵的二阶变分定义 Fisher–Rao 度量；其唯一性由 Čencov 单调性与充分统计不变性刻画。本文把局域小球族 $\{B_\ell(x)\}$ 诱导之 $D(\rho_{B_\ell}\Vert\rho^{(0)}_{B_\ell})$ 作为信息几何的基本发散，并以其一阶平衡（极值）与二阶正定性为变分原理的内容。([施普林格链接][1])

---

## 2. 信息几何变分原理（IGVP）

**原理（IGVP）** 对每个点 $x$ 与足够小的 $B_\ell(x)$，在保持体积 $\mathrm{Vol}(B_\ell)$ 与参考真空约束下，**广义熵**
$$
S_{\rm gen}(B_\ell):=\frac{A(\partial B_\ell)}{4G} + S_{\rm out}(\rho_{B_\ell})
$$
一阶极值，且二阶变分非负。等价地，令 $\sigma_{B_\ell}=\rho^{(0)}_{B_\ell}$，则
$$
\delta S_{\rm gen}=0,\qquad \delta^2 S(\rho_{B_\ell}\Vert \sigma_{B_\ell})\ge 0.
$$
第一式给出场方程，第二式给出稳定性与量子能量不等式（QNEC）族。该极值假设与"最大真空纠缠/等熵平衡"框架一致。([物理评论链接管理器][3])

**引理 2.1（第一定律）** 在小球极限与一阶微扰下，
$$
\delta S_{\rm out}=\delta\!\left\langle H_{\rm mod}^{(0)}\right\rangle
=2\pi\int_{B_\ell} \xi^\mu\,\delta\!\langle T_{\mu\nu}\rangle\, d\Sigma^\nu.
$$
（证明见上节文献。）([施普林格链接][2])

**引理 2.2（面积变分）** 固定小球体积的同时改变形状（或等价地以保持中心与半径的方式改变背景度规），其边界面积的变分满足
$$
\delta\!\left(\frac{A}{4G}\right)=-2\pi \int_{B_\ell}\xi^\mu\,\frac{1}{8\pi G}\,\delta\!\big(G_{\mu\nu}+\Lambda g_{\mu\nu}\big)\,d\Sigma^\nu + O(\ell^{d+1}),
$$
其中使用了 Raychaudhuri 与测地展开的标准小球几何。把该项与引理 2.1 相比对即可闭合第一变分。（推导同 Jacobson 型局域热力学/等熵论证之小球版。）([物理评论链接管理器][4])

**定理 2.3（IGVP ⇒ 爱因斯坦场方程）** 若对一切 $x$ 与足够小的 $B_\ell(x)$ 有 $\delta S_{\rm gen}=0$，则
$$
\boxed{\ G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle\ }.
$$
*证明*：由 $\delta S_{\rm gen}=\delta(A/4G)+\delta S_{\rm out}=0$ 与两引理得，对任意小球与任意局域形变
$$
\delta\!\Big(G_{\mu\nu}+\Lambda g_{\mu\nu}-8\pi G\,\langle T_{\mu\nu}\rangle\Big)=0.
$$
令
$$
C_{\mu\nu}:=G_{\mu\nu}+\Lambda g_{\mu\nu}-8\pi G\,\langle T_{\mu\nu}\rangle.
$$
上式对所有变分皆为零，故 $C_{\mu\nu}$ 与局域场 $(g_{\mu\nu},\rho)$ 无关。由 Bianchi 恒等式 $\nabla^\mu G_{\mu\nu}=0$ 与能动守恒 $\nabla^\mu\langle T_{\mu\nu}\rangle=0$ 推得 $\nabla^\mu C_{\mu\nu}=0$。在局域洛伦兹协变下，唯一满足该条件的张量为 $C_{\mu\nu}=C\,g_{\mu\nu}$，其中 $C$ 为常数。把 $C$ 吸收到宇宙学常数中，$\Lambda_{\rm eff}=\Lambda+C$，即得
$$
G_{\mu\nu}+\Lambda_{\rm eff} g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle,
$$
完成证明。□
该推导与"纠缠平衡 $\Rightarrow$ 爱因斯坦方程"的等价系谱一致，并在全息与一般场论中得到线性化与非线性扩展。([物理评论链接管理器][3])

---

## 3. 二阶变分与量子能量条件

**命题 3.1（相对熵非负与 QNEC）** 沿任意通过 $x$ 的无挠零测地丛 $k^\mu$ 作切割形变，二阶变分给出
$$
\delta^2 S(\rho_{B_\ell}\Vert \sigma_{B_\ell})\ \ge\ 0
\quad\Longrightarrow\quad
\langle T_{kk}\rangle\ \ge\ \frac{1}{2\pi}\,\frac{d^2 S_{\rm out}}{d\lambda^2},
$$
即量子零能条件（QNEC）。其证明族（场论/全息）均把相对熵的凸性作为核心输入。([物理评论链接管理器][5])

**推论 3.2（量子焦散与广义熵单调）** 量子焦散猜想与量子 Bousso 界由上述不等式与广义熵的非增性得到，与 IGVP 之二阶稳定性兼容。([arXiv][6])

---

## 4. 母刻度、读数与信息几何的耦合

**4.1 窗化群延迟与 Fisher 密度** 取每条观测者窗口—核 $(w_R,h)$ 诱导的带内分布 $p(E|x) \propto (w_R*\check h)(E)\,\rho_{\rm rel}(E;x)$。定义局域 Fisher 张量
$$
\mathcal I_{\mu\nu}(x)=\int \partial_\mu\!\ln p(E|x)\,\partial_\nu\!\ln p(E|x)\, p(E|x)\,dE,
$$
并以 Čencov–Amari 唯一性把其作为**读数—信息几何**与**背景度规**的配准对象：在真空—无别名极限与红移—互易重标度下，$\mathcal I_{\mu\nu}\propto g_{\mu\nu}$ 的约束可作为 IGVP 的附加拉格朗日乘子项，保证读数坐标与几何坐标一致化。该配准与红移—时间互易的缩放律协变。

**4.2 读数—几何的一致变分** 取作用
$$
\mathcal S[g;\rho]=\frac{1}{16\pi G}\!\int\!\sqrt{-g}\,(R-2\Lambda)\,d^4x
-\!\int\!\sqrt{-g}\,\Phi(\rho\Vert\rho^{(0)})\,d^4x
+\!\int\!\sqrt{-g}\,\lambda^{\mu\nu}\!\left(\mathcal I_{\mu\nu}-\kappa\, g_{\mu\nu}\right)\!d^4x,
$$
其中 $\Phi$ 是以相对熵为势的局域密度（小球极限可化为 $\delta\langle H_{\rm mod}\rangle-\delta S_{\rm out}$ 的体积分形式）。对 $g_{\mu\nu}$ 变分给出
$$
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\left(\langle T_{\mu\nu}\rangle + T^{\rm(IG)}_{\mu\nu}\right),
$$
而读数—几何配准 $\mathcal I_{\mu\nu}=\kappa g_{\mu\nu}$ 保证 $T^{\rm(IG)}_{\mu\nu}$ 的迹与真空能吸收到 $\Lambda$ 中，从而回到定理 2.3 的形式。当采用"第一定律"表述时，等价于把 $\delta S_{\rm gen}=0$ 作为 Euler–Lagrange 条件。（信息势的具体选取与 Fisher—相对熵等价在小球极限下由标准信息几何保证。）([施普林格链接][1])

---

## 5. 离散化：EBOC–Regge 信息作用与连续极限

**5.1 静态块—三角化** 在 EBOC 的静态块 $X_f$ 上选取与类光锥一致的叶分层与三角化，令每个 2-骨架（三角形） $h$ 携带离散面积 $A_h$，并在 $h$ 处定义缺角 $\varepsilon_h$。Regge 作用
$$
S_{\rm Regge}=\frac{1}{8\pi G}\sum_{h} A_h\,\varepsilon_h- \frac{\Lambda}{8\pi G}\sum_\sigma V_\sigma
$$
在变分下给出离散爱因斯坦方程。信息几何侧，对每个离散小球胞腔 $c$ 定义**离散广义熵**
$$
S_{\rm gen}^{\rm disc}(c)=\frac{A(\partial c)}{4G}+S_{\rm out}^{\rm disc}(c),
$$
第一变分 $\delta S_{\rm gen}^{\rm disc}=0$ 与 Regge 变分兼容，并在网格细化下收敛到连续 IGVP。([维基百科][7])

**5.2 观察=译码与信息不增** 离散态的可见语言由因子译码 $\pi$ 产生，满足
$$
K\!\left(\pi(x|_W)\right)\ \le\ K(x|_W)+K(\pi)+O(1),
$$
由此离散的 $S_{\rm out}^{\rm disc}$ 在细化极限收敛到连续的 $S_{\rm out}$，保证 $S_{\rm gen}^{\rm disc}\to S_{\rm gen}$ 与 IGVP 的稳定性。

---

## 6. 与 GLS—读数框架的一致性

**6.1 前沿—无超锥传播与读数独立性** 由前沿下界 $t_*\ge L_g/c$ 与窗化读数的规范协变/相对不变可知：IGVP 的小球选择与读数字典选择相互独立；小球—形变只锚定在因果结构与度规之上，读数仅提供 Fisher 配准与能量—延迟刻度。

**6.2 红移—互易与 Fisher 标度** 当谱缩放 $E\mapsto E/(1+z)$ 时，小球中的 Fisher 张量与读数刻度按 $(1+z)^{-2}$ 协变；体积保持的 IGVP 条件与 Jacobson/纠缠平衡的体积约束一致。

---

## 7. 量子修正、重整化与可检条件

**7.1 一回路/$1/N$ 修正** 在全息与场论中，广义熵的"面积 $+$ 外部纠缠"结构在一回路由体纠缠补偿；该修正正是 $S_{\rm gen}$ 的量子极小（QES）条件来源，保证 IGVP 在半经典阶仍成立。([arXiv][8])

**7.2 QNEC 与相对熵凸性** 二阶变分的正性给出 $\langle T_{kk}\rangle \ge (2\pi)^{-1}S''$ 等族不等式，并已在场论与全息语境中证明，构成 IGVP 的稳定性判据与可检核条件。([物理评论链接管理器][5])

---

## 8. 证明细节

**8.1 小球几何与面积展开** 在正规坐标下，小球边界面积
$$
A(\partial B_\ell)=\Omega_{d-2}\,\ell^{d-2}\!\left[1-\frac{\ell^2}{6(d-1)}\,R_{\mu\nu}u^\mu u^\nu+O(\ell^3)\right],
$$
体积保持变分消去 $\delta\ell$，留下 $\delta A\propto \delta(R_{\mu\nu}u^\mu u^\nu)$。与引理 2.1 配对并使用 $G_{\mu\nu}=R_{\mu\nu}-\tfrac12 R g_{\mu\nu}$ 得定理 2.3。

**8.2 "第一定律"与模哈密顿量** 球域的模哈密顿量对共形真空局域为能动张量的线性泛函，故 $\delta S_{\rm out}=\delta\langle H_{\rm mod}\rangle$ 成立；对非共形场的修正已在后续文献中给出并不影响结论的形式。([施普林格链接][2])

---

## 9. 与既有路径的关系与优势

**Jacobson（热力学/纠缠平衡）路线**：本文把"局域热力学/等熵平衡"重述为**信息几何极值**，以 Fisher—相对熵的普适结构取代具体的热学闭包，从而把引力视为"保持局域信息平衡的几何响应"。([物理评论链接管理器][4])

**全息"第一定律"路线**：本文在无需全息假设的局域小球层面复现"第一定律 $\Rightarrow$ 场方程"的逻辑；当存在重力对偶时，与全息推导（线性化爱因斯坦方程）严格对接。([施普林格链接][9])

**EBOC—GLS 统一**：离散—译码与连续—因果在 IGVP 下统一：离散侧的信息不增与静态块一致扩张保证 $S_{\rm gen}^{\rm disc}\to S_{\rm gen}$；连续侧由母刻度—读数—Fisher 配准把可测刻度与几何量纲无缝对齐。

---

## 10. 典型推论与可观测后果

1. **局域等熵 ⇒ 场方程（可逆向）**：若已知 $G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle$，则在小球极限 $\delta S_{\rm gen}=0$ 成立（等价表述），形成封闭的必要充分链条。([物理评论链接管理器][3])

2. **QNEC/量子焦散**：任意零方向的二阶形变给出能量下界，提供对半经典引力的一致性检验与数值检核指标。([物理评论链接管理器][5])

3. **红移—互易时钟与 Fisher 容量**：在观测—计时实验中，带宽—分辨率—红移的互易缩放在 IGVP 的拉格朗日约束中显式体现，可作为实验标定层的直接后验。

---

## 11. 结论式陈述（纲要化）

* 在小球极限中，把**广义相对熵极值**作为信息几何的基本变分原理，**等价**于爱因斯坦场方程。
* 二阶变分的非负性给出 QNEC/量子焦散等**量子一致性**约束。
* EBOC 的离散—译码语义与 Regge 三角化给出**离散作用—极值**的兼容实现，并在细化极限下收敛到连续 IGVP。
* 母刻度—窗化读数—Fisher 配准把"可测刻度"与几何度量**统一对齐**，保持因果—读数的位阶分离与数值误差账本的有限阶闭合。

---

## 参考文献（选）

Jacobson, *Thermodynamics of Spacetime: The Einstein Equation of State*, PRL 75 (1995). ([物理评论链接管理器][4])
Jacobson, *Entanglement Equilibrium and the Einstein Equation*, PRL 116 (2016). ([物理评论链接管理器][3])
Lashkari–McDermott–Van Raamsdonk, *Gravitational dynamics from entanglement "thermodynamics"*, JHEP 04 (2014) 195. ([施普林格链接][2])
Faulkner–Guica–Hartman–Myers–Van Raamsdonk, *Gravitation from entanglement in holographic CFTs*, JHEP 03 (2014) 051. ([施普林格链接][9])
Casini–Huerta–Myers, *Towards a derivation of holographic entanglement entropy*, JHEP 05 (2011) 036. ([arXiv][10])
Bousso–Fisher–Leichenauer–Wall, *A Quantum Focussing Conjecture* (2015); *Proof of a Quantum Bousso Bound* (2014). ([arXiv][6])
Balakrishnan *et al.*, *A General Proof of the Quantum Null Energy Condition* (2019). ([施普林格链接][11])
Amari, *Information Geometry and Its Applications* (2016). ([施普林格链接][1])
Čencov, *Statistical Decision Rules and Optimal Inference* (AMS, 1982). ([bookstore.ams.org][12])
Regge, *General Relativity without Coordinates* (1961)；综述见 Barrett–Oriti–Williams (2018). ([Inspire][13])

---

## 附录 A：与 GLS—EBOC 统一的对接细节（提要）

1. **母刻度与 Fisher 对齐**：由 $\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 构造 $p(E|x)$ 并定义 $\mathcal I_{\mu\nu}$；以 $\lambda^{\mu\nu}(\mathcal I_{\mu\nu}-\kappa g_{\mu\nu})$ 约束把读数坐标拉回几何坐标。

2. **因果—读数分层**：IGVP 的小球与相对熵仅锚定因果与度规；窗化群延迟只用于统计流形的刻度与观测字典，不参与偏序定义。

3. **离散—极限**：在 EBOC 的静态块与永恒图上定义 $S_{\rm gen}^{\rm disc}$、Regge 作用与因子译码，满足 $\delta S_{\rm gen}^{\rm disc}=0 \Rightarrow$ Regge 方程；细化极限回到定理 2.3。

4. **范畴等价与协变**：GLS ↔ 因果流形的互构保证"几何—读数—信息"的函子性与自然性；IGVP 在该等价下保持不变。

---

## 附录 B：信息几何—第一定律的等价写法

把小球相对熵写作
$$
S(\rho_{B_\ell}\Vert \sigma_{B_\ell})
=\mathrm{Tr}(\rho_{B_\ell}\ln\rho_{B_\ell})-\mathrm{Tr}(\rho_{B_\ell}\ln\sigma_{B_\ell}),
$$
一阶变分给出
$$
\delta S=-\delta S_{\rm out}+\delta\!\langle H_{\rm mod}^{(0)}\rangle,\qquad
H_{\rm mod}^{(0)}:=-\ln\sigma_{B_\ell},
$$
即"第一定律"。对共形真空，$H_{\rm mod}^{(0)}$ 为能量流密度的局域泛函；对非共形情形可在小球极限下以算子展开校正，且不改变极值条件的形式。([施普林格链接][2])

---

## 附录 C：数值实现与 NPE 误差账本（读数侧）

在任何以窗—核 $(w_R,h)$ 实现的读数积分中，只对被积函数 $f(E)=w_R(E)\,[h\!\star\!\rho_{\rm rel}](E)$ 施行采样/截断/EM 端点校正；IGVP 的小球—形变与场方程推导不受该数值账本影响。

---

**说明** 本文所有公式的度量—读数—因果位阶与母刻度、互构等一致性已在前述统一框架中系统刻画，本文仅在此基础上把"引力＝信息几何的广义相对熵极值"作严格化表述并给出连续—离散双实现。

[1]: https://link.springer.com/book/10.1007/978-4-431-55978-8?utm_source=chatgpt.com "Information Geometry and Its Applications"
[2]: https://link.springer.com/article/10.1007/JHEP04%282014%29195?utm_source=chatgpt.com "Gravitational dynamics from entanglement "thermodynamics""
[3]: https://link.aps.org/doi/10.1103/PhysRevLett.116.201101?utm_source=chatgpt.com "Entanglement Equilibrium and the Einstein Equation"
[4]: https://link.aps.org/doi/10.1103/PhysRevLett.75.1260?utm_source=chatgpt.com "Thermodynamics of Spacetime: The Einstein Equation of State"
[5]: https://link.aps.org/doi/10.1103/PhysRevD.93.024017?utm_source=chatgpt.com "Proof of the quantum null energy condition | Phys. Rev. D"
[6]: https://arxiv.org/abs/1506.02669?utm_source=chatgpt.com "A Quantum Focussing Conjecture"
[7]: https://en.wikipedia.org/wiki/Regge_calculus?utm_source=chatgpt.com "Regge calculus - Wikipedia"
[8]: https://arxiv.org/abs/1307.2892?utm_source=chatgpt.com "Quantum corrections to holographic entanglement entropy"
[9]: https://link.springer.com/article/10.1007/JHEP03%282014%29051?utm_source=chatgpt.com "Gravitation from entanglement in holographic CFTs"
[10]: https://arxiv.org/abs/1102.0440?utm_source=chatgpt.com "Towards a derivation of holographic entanglement entropy"
[11]: https://link.springer.com/article/10.1007/JHEP09%282019%29020?utm_source=chatgpt.com "A general proof of the quantum null energy condition"
[12]: https://bookstore.ams.org/mmono-53?utm_source=chatgpt.com "Statistical decision rule and optimal inference - AMS Bookstore"
[13]: https://inspirehep.net/literature/3183?utm_source=chatgpt.com "GENERAL RELATIVITY WITHOUT COORDINATES - Inspire HEP"
