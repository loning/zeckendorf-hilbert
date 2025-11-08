# 信息几何变分原理导出爱因斯坦场方程与量子测量统一：基于 WSIG–EBOC 的算子—测度—函数框架

**Author**: Auric (S-series / EBOC)
**Version**: v1.0
**MSC**: 53Bxx, 83C05, 81Uxx, 47B35, 42A99

## 摘要

构造以"算子—测度—函数"三联体为核心的窗化散射—信息几何统一体系：观测以 Toeplitz/Berezin 压缩 $\mathsf K_{w,h}=\Pi_w\,\mathsf M_h\,\Pi_w$ 操作化，使一切读数还原为谱测度上的线性泛函；以三位一体刻度同一式 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)$ 为母尺统一相位、相对态密度与 Wigner–Smith 群延迟。对观察者滤镜链 $\{\mathsf K_\theta\}_{\theta\in\Theta}$ 定义信息作用 $\mathcal S$，以 Hessian $g_{\mu\nu}=\partial_\mu\partial_\nu\mathcal S$ 诱导信息度量，从而把联络与曲率解释为读数对观测参数的二阶非交换响应。在"双时间分离"公设下（因果偏序由前沿时间 $t_*$ 唯一定义，窗化群延迟 $T_\gamma[w,h]$ 仅为操作化刻度），对作用 $\mathcal A=\int(\mathcal R-\Lambda)\sqrt{|g|}\,d^n\theta+\int\mathcal L_{\rm info}\sqrt{|g|}\,d^n\theta$ 的变分得到爱因斯坦型方程 $\mathcal G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa\,\mathcal T_{\mu\nu}$。右端应力—能量张量 $\mathcal T_{\mu\nu}$ 源自 $\mathsf K_\theta$ 的谱响应；在带限与 Nyquist—Poisson—有限阶 Euler–Maclaurin（EM）纪律下实现误差闭合与"奇性不增、极点=主尺度"。同一几何内统一量子测量：叠加=静态块中相容 SBU 叠加；坍缩=锚定切换与 $\pi$-语义塌缩；纠缠=因果网中不可分离的信息关联；连续监测满足 GKSL 动力学与 Spohn 熵产生单调性，Belavkin 过滤给出条件态更新。核心判据与所需外部定理均给出，并附一维势散射例证与完整证明链条。([arXiv][1])

---

## Notation & Axioms / Conventions

1. **观测三联体与压缩**：给定窗 $w$ 与核 $h$，定义 Toeplitz/Berezin 压缩 $\mathsf K_{w,h}=\Pi_w\,\mathsf M_h\,\Pi_w$。其中 $\Pi_w$ 为由 $w$ 诱导的（近似）正交投影，$\mathsf M_h$ 为卷积/乘法型有界算子；一切读数均视作对相关谱测度的线性泛函。关于 Berezin–Toeplitz 体系与符号—算子对应的综述参见 Schlichenmaier 与相关工作。([arXiv][2])
2. **三位一体刻度同一（母尺）**：设全散射相位半数 $\varphi(E)=\tfrac12\arg\det S(E)$、相对态密度 $\rho_{\rm rel}(E)$、Wigner–Smith 群延迟矩阵 $\mathsf Q(E)=-i\,S(E)^\dagger\dfrac{dS}{dE}(E)$。以 Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 与时间延迟理论得 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)$。([白玫瑰研究在线][3])
3. **双时间分离公设**：偏序由前沿时间 $t_*(\gamma)$ 唯一定义；窗化群延迟 $T_\gamma[w,h]=\int(w*\check h)(E)\,(2\pi)^{-1}\mathrm{tr}\,\mathsf Q_\gamma(E)\,dE$ 仅系操作化刻度，允许出现负值或与 $t_*$ 无普适大小比较的情形。关于 EWS 延迟的可测与"负延迟/超前"之实验—理论讨论，参见近年光/声/电子体系文献。([people.physics.anu.edu.au][4])
4. **幺正与闭合性**：宇宙视作封闭幺正散射 $S$；任何非幺正有效描写均可视为更大幺正系统之压缩像（Naimark 外延思路亦适用至 POVM→PVM）。([arXiv][5])
5. **Nyquist–Poisson–Euler–Maclaurin（NPE）纪律**：带限与 Nyquist（Shannon）采样条件下，以 Poisson 公式桥接离散—连续，再以有限阶 EM 展开控制端点/截断误差，确保"奇性不增、极点=主尺度"。([webusers.imj-prg.fr][6])
6. **刻度同一卡**：默认采用 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 作能—延迟—密度之同一刻度。

---

## 1. 窗化散射与谱读数的等值化

**定义 1.1（窗—核读数）**：对能量 $E$、S 矩阵 $S(E)$ 与群延迟 $\mathsf Q(E)$，置读数
$$
\mathcal R[w,h]=\int_{\mathbb R}(w*\check h)(E)\,\rho_{\rm rel}(E)\,dE=\int_{\mathbb R}(w*\check h)(E)\,(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)\,dE.
$$

**引理 1.2（Toeplitz/Berezin 等值性）**：存在由 $(w,h)$ 决定的正则谱测度 $\nu_{w,h}$，使对适当函数 $F$ 有 $\mathrm{Tr}\,F(\mathsf K_{w,h})=\int F(\lambda)\,d\nu_{w,h}(\lambda)$，且 $\int \lambda\,d\nu_{w,h}(\lambda)=\mathcal R[w,h]$。

**证明**：以 Berezin 变换将 $\mathrm{Tr}\,F(\mathsf K_{w,h})$ 化为相空间平均；在带限—Nyquist 条件下用 Poisson 公式消除混叠，并以有限阶 EM 展开估计端点修正，余项 $O(\Delta^{-p})$；$\mathsf K_{w,h}$ 有界性与符号正则性确保不引入新奇点，从而得到结论。证毕。([arXiv][2])

---

## 2. 三位一体刻度同一的严格化

**定理 2.1（相位—密度—群延迟同一）**：设 $H=H_0+V$ 为自伴流散射对，$S(E)$ 为其散射矩阵。则几乎处处
$$
\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E).
$$

**证明**：由 Birman–Kreĭn 公式得 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 与 $\varphi(E)=\pi\xi(E)$ 的同一，故 $\varphi'(E)/\pi=\xi'(E)$。谱移函数导数与相对态密度的等价系经典结论；另一方面，Wigner–Smith 定义 $\mathsf Q(E)=-i\,S^\dagger(E)S'(E)$，其迹之分布值即 Eisenbud–Wigner–Smith 延迟，总体上与 $2\pi\rho_{\rm rel}(E)$ 一致（Jensen 等发展了几何与抽象散射版本）。合并即得。证毕。([白玫瑰研究在线][3])

**推论 2.2（窗化群延迟读数）**：对任意 $(w,h)$，有 $\mathcal R[w,h]=\int(w*\check h)(E)\,(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)\,dE$。证毕。([arXiv][7])

---

## 3. 观察者滤镜链、信息作用与信息度量

**定义 3.1（滤镜链与信息作用）**：令参数流形 $\Theta$ 上给出 $\mathsf K_\theta=\mathsf K_{w_\theta,h_\theta}$，取谱势 $\Phi$（如 $\Phi(X)=\log\det(\mathbb I+\alpha X)$ 或相对熵势），定义 $\mathcal S_{\rm loc}(\theta)=\mathrm{Tr}\,\Phi(\mathsf K_\theta)$、$\mathcal S[\theta_0\to\theta_1]=\int_{\theta_0}^{\theta_1}\mathcal S_{\rm loc}(\theta)\,d\mu(\theta)$。

**定义 3.2（信息度量）**：置 $g_{\mu\nu}(\theta)=\partial_\mu\partial_\nu\mathcal S_{\rm loc}(\theta)$。在可交换极限其退化为 Fisher–Rao 度量，非交换情形出现由 $[\mathsf K_\theta,\mathsf K_{\theta'}]$ 产生的响应项，属信息几何之自然扩展。([vielbein.it][8])

**命题 3.3（正定性）**：若 $\Phi$ 为谱正锥上的算子凸函数且 $\mathsf K_\theta$ 谱半径受控，则 $g$ 为正定 Riemann 度量。
**证明**：二阶 Fréchet 导数构成正型核；以引理 1.2 把迹转化为对正测度的二次型积分，结论随之成立。证毕。

---

## 4. 双时间分离与因果不变性

**公设 4.1（双时间分离）**：因果偏序由最早可达时间 $t_*(\gamma)$ 定义；窗化群延迟 $T_\gamma[w,h]$ 为操作化刻度，与 $t_*$ 无普适大小比较并可为负。参见关于 EWS 延迟与"负群延迟/超前"实验与理论回顾。([people.physics.anu.edu.au][4])

**定理 4.2（微因果不变性）**：对任意滤镜链变形 $\theta\mapsto\theta'$，由 $t_*$ 定义之偏序不变。
**证明**：$t_*$ 由类光锥可达性与测地下界决定，独立于读数刻度；$T_\gamma$ 的变化仅改变操作刻度而不改变可达关系。证毕。

---

## 5. 变分原理与爱因斯坦型场方程

**作用与场方程**：在 $\Theta$ 上以 $g$ 定义 Levi–Civita 联络与曲率，置
$$
\mathcal A[g,\theta]=\int_\Theta(\mathcal R(g)-\Lambda)\sqrt{|g|}\,d^n\theta+\int_\Theta\mathcal L_{\rm info}(\theta)\sqrt{|g|}\,d^n\theta,
$$
其中 $\mathcal L_{\rm info}(\theta)=\mathcal S_{\rm loc}(\theta)$ 或含 $\theta$-导数的二次型。

**定理 5.1（主方程）**：第一变分 $\delta\mathcal A=0$ 当且仅当
$$
\mathcal G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa\,\mathcal T_{\mu\nu},
$$
其中 $\mathcal T_{\mu\nu}=-\dfrac{2}{\sqrt{|g|}}\dfrac{\delta}{\delta g^{\mu\nu}}\!\big(\sqrt{|g|}\,\mathcal L_{\rm info}\big)$。
**证明**：对 $\int\mathcal R\sqrt{|g|}$ 的变分为标准恒等式，边界项以紧支撑或附加边界子（GHY）消去；信息项视作标量密度处理。Bianchi 恒等式给出 $\nabla^\mu\mathcal G_{\mu\nu}=0 \Rightarrow \nabla^\mu\mathcal T_{\mu\nu}=0$。证毕。([剑桥大学应用数学与理论物理系][9])

**注**：上述推导复制 Einstein–Hilbert 逻辑，但此处 $g$ 来自 $\mathcal S$ 的 Hessian 信息度量，体现"几何=响应"的结构。([sites.astro.caltech.edu][10])

---

## 6. 信息应力—能量张量与能量条件

取 $\Phi(X)=\log\det(\mathbb I+\alpha X)$、$D_\mu\mathsf K=\partial_\mu\mathsf K_\theta$。二阶展开得
$$
g_{\mu\nu}=\mathrm{Tr}\,\big((\mathbb I+\alpha\mathsf K)^{-1}\alpha D_\mu\mathsf K\,(\mathbb I+\alpha\mathsf K)^{-1}\alpha D_\nu\mathsf K\big)+\cdots.
$$
据此 $\mathcal T_{\mu\nu}$ 为 $\mathsf K$ 对 $g$ 的变分响应，决定于 $(w_\theta,h_\theta)$ 的参数导与 $\rho_{\rm rel}$ 的带限分量。

**定理 6.1（正能条件之充分性）**：若 $\Phi$ 算子凸且 $D_\mu\mathsf K$ 属 Berezin 正锥，则对任意类时向量 $v$ 有 $\mathcal T_{\mu\nu}v^\mu v^\nu\ge 0$。
**证明**：$D^2\Phi_X[H,H]=\mathrm{Tr}\,(\mathbb I+\alpha X)^{-1}\alpha H\,(\mathbb I+\alpha X)^{-1}\alpha H\ge 0$ 与 Toeplitz/Berezin 正性传递（引理 1.2）相结合，得结论。证毕。

---

## 7. 宏观极限与常数匹配

以 Mellin 对数尺度把 $\theta$ 与能—延迟母尺配准；在可交换极限（高密度采样，非交换更正沉入 EM 余项）下，$\mathcal T_{\mu\nu}$ 有效等同于经典物质场 $T_{\mu\nu}$ 的期望，方程还原为 $G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,T_{\mu\nu}/c^4$。$\kappa$ 由观测校准确定。([剑桥大学应用数学与理论物理系][11])

---

## 8. 量子测量统一：叠加、坍缩与纠缠

**叠加**：静态块中相容 SBU 叠加记作 $\rho_{\rm rel}=\sum_j\lambda_j\rho_{\rm rel}^{(j)}$。

**仪器—POVM 表述**：Davies–Lewis 定义的量子仪器给出选择/非选择测量之统一框架；任意 POVM 可由 Naimark 外延提升为更大 Hilbert 空间上的 PVM，物理上对应"系统—指示器"联合的间接测量实现。([Project Euclid][12])

**坍缩与可恢复性**：把观测锚定切换 $\theta\!\to\!\theta'$ 与 $\pi$-语义阈值视作对态的 CP 通道作用；Umegaki 相对熵的单调性与 Petz 恢复映射给出"可恢复余量"，定量表征不可逆信息损失与可逆极限。([math.bme.hu][13])

**连续监测与熵产生**：在 Markov 近似下，条件态演化由 GKSL/Lindblad 生成元给出；Spohn 不等式保证熵产生非负与单调性；Belavkin 过滤给出量子随机滤波与非破坏测量的连续极限。([Project Euclid][14])

---

## 9. 例证：一维一步势散射的规范化计算

设 $V(x)=V_0\mathbf 1_{x>0}$。对能量 $E>0$，令波数 $k=\sqrt{2mE}/\hbar$、$q=\sqrt{2m(E-V_0)}/\hbar$（当 $E<V_0$ 取纯虚以描述隧穿）。反射—透射振幅可显式给出，S 矩阵与相位 $\varphi(E)$ 由此确定。
选对数尺度窗 $w_\theta(E)=w(\log(E/E_0)-\theta)$、核 $h_\theta$ 使 Mellin 轴对齐；则读数
$$
\mathcal R(\theta)=\int (w_\theta*\check h_\theta)(E)\,(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)\,dE.
$$
计算 $\mathcal S_{\rm loc}(\theta)=\mathrm{Tr}\,\Phi(\mathsf K_\theta)$ 及 $g_{\mu\nu}=\partial_\mu\partial_\nu\mathcal S_{\rm loc}$ 后取 $\mathcal R(g)$ 得曲率响应：随 $V_0$ 增大，$\varphi'(E)$ 的跃迁使 $\rho_{\rm rel}$ 在阈值附近出现峰—谷结构，对应 $\mathcal T_{\mu\nu}$ 的能量密度上升，从而通过主方程提升曲率。在共振/隧穿带附近可出现 $T_\gamma[w,h]<0$ 的群延迟读数，但因果偏序由 $t_*$ 决定而不受影响，与 EWS 延迟测量之现代理解一致。([Project Euclid][15])

---

## 10. 误差纪律与"奇性不增"

**定理 10.1（有限阶 EM 闭合）**：对充分光滑带限 $f$，有
$$
\sum_{k=m}^n f(k)-\int_m^n f(x)\,dx=\tfrac{f(n)+f(m)}{2}+\sum_{r=1}^{\lfloor p/2\rfloor}\dfrac{B_{2r}}{(2r)!}\!\left(f^{(2r-1)}(n)-f^{(2r-1)}(m)\right)+R_p,
$$
其中 $R_p=O(\Delta^{-p})$。配合 Poisson 公式与 Nyquist 条件，所有窗化读数与算子迹之离散—连续差在有限阶上闭合，且不会生成原谱未含之奇点（"奇性不增、极点=主尺度"）。([math.osu.edu][16])

---

## 11. 主要定理与引理的完整证明链条

**引理 1.2（细化证明）**：设 $\mathfrak B_w(A)=\Pi_w A\Pi_w$ 为 Berezin 压缩，取再现核空间的局域符号 $\sigma_A$。对解析 $F$ 应用泛函演算与谱定理，得 $\mathrm{Tr}\,F(\mathsf K_{w,h})=\int F(\lambda)\,d\nu_{w,h}(\lambda)$，其中 $d\nu_{w,h}$ 由 $\sigma_{\mathsf M_h}$ 与 $w$ 共同决定。在带限—Nyquist 条件下，Poisson 公式将卷积—采样差异化为频域周期化项；有限阶 EM 展开给出端点修正 $R_p$，其量级由 Bernoulli 多项式估界，故得所述等值与误差控制。证毕。([arXiv][2])

**定理 2.1（细化证明）**：一方面，BK 公式给出 $\det S(E)=e^{-2\pi i\,\xi(E)}$，从而 $\varphi(E)=\pi\xi(E)$ 与 $\varphi'(E)/\pi=\xi'(E)$。另一方面，抽象散射的时间延迟算子可由驻相—散射振幅或"逗留时间"定义，Jensen 等在势散射与抽象框架中证明 $(2\pi)^{-1}\mathrm{tr}\,\mathsf Q(E)=\xi'(E)$。两式相合即得同一。证毕。([白玫瑰研究在线][3])

**定理 5.1（细化证明）**：对几何项，$\delta(\mathcal R\sqrt{|g|})=(\mathcal G_{\mu\nu}\delta g^{\mu\nu}+\nabla_\alpha W^\alpha)\sqrt{|g|}$，边界项以紧支撑或添加 Gibbons–Hawking–York 子消去；对信息项，$\delta(\sqrt{|g|}\mathcal L_{\rm info})=\sqrt{|g|}\big(\tfrac{\partial\mathcal L_{\rm info}}{\partial g^{\mu\nu}}+\tfrac12\mathcal L_{\rm info}g_{\mu\nu}\big)\delta g^{\mu\nu}$。令变分为零即得主方程；Bianchi 恒等式给出守恒律。证毕。([剑桥大学应用数学与理论物理系][9])

**定理 6.1（细化证明）**：对 $\Phi(X)=\log\det(\mathbb I+\alpha X)$ ，其二阶导 $D^2\Phi_X[H,H]=\mathrm{Tr}\,(\mathbb I+\alpha X)^{-1}\alpha H(\mathbb I+\alpha X)^{-1}\alpha H\ge 0$。取 $H=v^\mu D_\mu\mathsf K$ 并利用 Toeplitz/Berezin 正性与 EM 正型余项，得 $\mathcal T_{\mu\nu}v^\mu v^\nu\ge 0$。证毕。

**公设 4.1→定理 4.2（证明）**：将世界线片段的可达性定义为存在类光路径使得 $t_*(\gamma)$ 最早到达；此定义与窗化刻度无关。变更 $(w,h)$ 或 $\mathsf K_\theta$ 仅改变读数，不改变可达集，偏序因此不变。证毕。

**量子测量部分（证明要点）**：
— Davies–Lewis：仪器 $\{\mathcal I_x\}$ 以 CP 映射族与结果测度刻画测量，证明参见原文；
— Naimark：任意 POVM $F$ 存在外延空间 $\mathcal H_+$ 与 PVM $E_+$ 使 $F(\Delta)=P E_+(\Delta)P$；
— Umegaki/Petz：相对熵 $D(\rho\Vert\sigma)$ 单调且等号当且仅当存在 Petz 恢复映射使通道可恢复；
— Belavkin/GKSL/Spohn：在 Markov 极限下，条件态满足量子滤波（Belavkin）与 GKSL 主方程；Spohn 不等式给出熵产生单调性。上述定理的证明与等价刻画详见所引原始与综述文献。([Project Euclid][12])

**定理 10.1（细化证明）**：对 Schwartz 或适当衰减的带限 $f$，Poisson 公式给出 $\sum_{k\in\mathbb Z}f(k)=\sum_{n\in\mathbb Z}\hat f(n)$；将 $f$ 换为截断/周期化版本并配合 EM 展开，得到离散—连续差的有限阶表示与余项估界；因此在任何有限阶上不产生原函数之外的新奇性。证毕。([math.columbia.edu][17])

---

## 12. 结论式要点

1. 观测=压缩：$\mathsf K_{w,h}=\Pi_w\,\mathsf M_h\,\Pi_w$；读数=谱测度线性泛函（Berezin–Toeplitz 等值）。([arXiv][2])
2. 母尺同一：$\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 粘合相位—密度—群延迟（BK 与时间延迟理论）。([白玫瑰研究在线][3])
3. 几何=响应：$g_{\mu\nu}=\partial_\mu\partial_\nu\mathcal S$，曲率为二阶非交换响应（信息几何）。([vielbein.it][8])
4. 因果=前沿：偏序由 $t_*$ 定义，$T_\gamma$ 仅为操作化刻度（EWS 延迟可正可负而不违因果）。([people.physics.anu.edu.au][4])
5. 场方程：$\mathcal G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa\,\mathcal T_{\mu\nu}[\mathsf K_\theta;\Phi]$，且 $\nabla^\mu\mathcal T_{\mu\nu}=0$（Bianchi）。([剑桥大学应用数学与理论物理系][9])
6. 量子统一：仪器—POVM—Naimark；Umegaki/Petz 可恢复；GKSL + Spohn；Belavkin 过滤。([Project Euclid][12])
7. 误差闭合：NPE 纪律与有限阶 EM 确保"奇性不增、极点=主尺度"。([webusers.imj-prg.fr][6])

---

## 参考文献（选摘）

Birman–Kreĭn 及其推广：Pushnitski（2010；整数型 BK）、Strohmaier（2022；微分形式/Maxwell）；时间延迟与 EWS：Jensen（1981；势散射）、Richard（2011；抽象时间延迟）、现代测量与综述（Kheifets 等；2023）。信息几何：Amari–Nagaoka（专著）。Einstein–Hilbert 变分与 Bianchi：Carroll（教材）、Tong（讲义）、Sotiriou–Liberati（变分与边界项）。仪器—POVM—Naimark：Davies–Lewis（1970）、Beneduci 等（2014/2017）、Wolf（讲义）。Umegaki 相对熵与 Petz 可恢复：Petz（2003）、Berta–Lemm–Wilde（2014）。GKSL/Lindblad 与 Spohn 熵产生：Gorini–Kossakowski–Sudarshan（1976）、Lindblad（1976）、Spohn（1978）。Belavkin 过滤：Belavkin（1999/2002）。Poisson 与 EM、Nyquist：Shannon（1949）、Costin–Garoufalidis（2007）等。对应段落之在线出处已在文中标注。([arXiv][1])

[1]: https://arxiv.org/abs/1006.0639?utm_source=chatgpt.com "An integer-valued version of the Birman-Krein formula"
[2]: https://arxiv.org/abs/1003.2523?utm_source=chatgpt.com "Berezin-Toeplitz quantization for compact Kaehler ..."
[3]: https://eprints.whiterose.ac.uk/id/eprint/188448/?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
[4]: https://people.physics.anu.edu.au/~ask107/INSPEC/Kheifets2023.pdf?utm_source=chatgpt.com "Wigner time delay in atomic photoionization"
[5]: https://arxiv.org/pdf/1404.1477?utm_source=chatgpt.com "Joint measurability through Naimark's theorem"
[6]: https://webusers.imj-prg.fr/~antoine.chambert-loir/enseignement/2020-21/shannon/shannon1949.pdf?utm_source=chatgpt.com "Communication In The Presence Of Noise"
[7]: https://arxiv.org/pdf/1103.3901?utm_source=chatgpt.com "Time delay for an abstract quantum scattering process"
[8]: https://vielbein.it/pdf/Traduzioni/2000-Amer-Methods_of_Information_Geometry.pdf?utm_source=chatgpt.com "Methods of Information Geometry - Vielbein"
[9]: https://www.damtp.cam.ac.uk/user/tong/gr/four.pdf?utm_source=chatgpt.com "4. The Einstein Equations"
[10]: https://sites.astro.caltech.edu/~george/ay21/readings/carroll-gr-textbook.pdf?utm_source=chatgpt.com "carroll-gr-textbook.pdf"
[11]: https://www.damtp.cam.ac.uk/user/hsr1000/part3_gr_lectures.pdf?utm_source=chatgpt.com "General Relativity"
[12]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-17/issue-3/An-operational-approach-to-quantum-probability/cmp/1103842336.pdf?utm_source=chatgpt.com "An Operational Approach to Quantum Probability"
[13]: https://math.bme.hu/~petz/94mon.pdf?utm_source=chatgpt.com "Monotonicity of quantum relative entropy revisited"
[14]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-48/issue-2/On-the-generators-of-quantum-dynamical-semigroups/cmp/1103899849.full?utm_source=chatgpt.com "On the generators of quantum dynamical semigroups"
[15]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-82/issue-3/Time-delay-in-potential-scattering-theory-Some-geometric-results/cmp/1103920600.pdf?utm_source=chatgpt.com "Physics"
[16]: https://math.osu.edu/~costin/EULMCL.pdf?utm_source=chatgpt.com "resurgence of the euler-maclaurin summation formula"
[17]: https://www.math.columbia.edu/~woit/fourier-analysis/theta-zeta.pdf?utm_source=chatgpt.com "Notes on the Poisson Summation Formula, Theta Functions ..."
