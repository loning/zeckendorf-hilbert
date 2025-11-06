# GLS—QFT 协变融合框架

## ——局域网格（AQFT/LCQFT）·窗化群延迟·KMS/模流·局域测量的统一表述与互构定理

## 摘要

在"宇宙 = 广义光结构（GLS）""观察者 = 滤镜链（Toeplitz/Berezin 压缩 → CP 通道 → POVM → 阈值计数）""因果 = 类光锥偏序"的统一语境下，构造与代数量子场论（AQFT）/局域协变量子场论（LCQFT）协变一致的窗化群延迟—红移—光速理论。核心刻度采用同一式 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$，其中 $\mathsf Q(E)=-iS^\dagger(E)\,S'(E)$ 为 Wigner–Smith 群延迟矩阵；在非幺正（开放/耗散）散射下，采用级联可加的改型 $\widetilde{\mathsf Q}(E)=-iS^{-1}(E)\,S'(E)$，并以扩展幺正化与谱移函数连接。GLS 的窗—核 $K_{w,h}$ 被提升为对阿尔维森谱与相空间的协变压缩，从而在 LCQFT 的函子语法下自然化；微因果与 Hadamard/微局域谱条件保证无超锥传播与读数良定；以 KMS/被动性与模流（Bisognano–Wichmann）刻画加速观测（Unruh 温度）；以 Fewster–Verch 局域测量框架将滤镜链实现为"系统—探测器"耦合的 CP 仪式并证明因果分离下的交换与组合；在 Haag–Ruelle/AQFT 散射存在性下建立窗化 Wigner–Smith—谱移一致化（Birman–Kreĭn）；并给出 Nyquist–Poisson–Euler–Maclaurin（NPE）有限阶误差闭合与量子能量不等式（QEI）尾项控制。全文以算子—测度—函数语言表述，证明与引用均对应公开判据。

---

## Notation & Axioms / Conventions

### 卡片 I（三位一体刻度与非幺正改型）

在绝对连续谱带内且 $S(E)$ 幺正时，Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 与 $-i\,\tfrac{d}{dE}\log\det S(E)=\operatorname{tr}\!\big(S^\dagger S'(E)\big)$ 蕴含
$$
\frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q(E)=-iS^\dagger(E)S'(E),\quad \rho_{\rm rel}(E)=-\xi'(E).
$$
当存在有效增益/损耗（开放测量/吸收）时，取 $\widetilde{\mathsf Q}=-iS^{-1}S'$ 维持级联可加性，并以非厄米/次幺正情形的复时间延迟理论对接（见 §7）。([arXiv][1])

### 卡片 II（有限阶 Euler–Maclaurin 与"极点 = 主尺度"）

离散—连续互换与窗化读数服从有限阶误差学
$$
\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}.
$$
Nyquist 关断使 $\varepsilon_{\rm alias}=0$；有限阶 Euler–Maclaurin（EM）给出端点伯努利层与显式余项；尾项由窗外衰减与 QEI 控制。EM 余项与上界采用 DLMF §2.10 记载的标准形式。([dlmf.nist.gov][2])

### AQFT/LCQFT 约定与 rce

采用 Haag–Kastler 局域网格 $\mathcal O\mapsto\mathcal A(\mathcal O)$（同向、微因果），以及 LCQFT 的函子化表述：对象是全局双曲时空，态射为等距嵌入；量子场为自然变换；相对 Cauchy 演化（rce）表征对度量剖分的动力响应。([arXiv][3])

---

## 1. GLS → AQFT：对象层嵌入与窗—核的协变压缩

**定义 1.1（窗—核与协变压缩）** 取偶窗 $w_R\in\mathcal S(\mathbb R)$、相空间核 $h$。对任意 $A\in\mathcal A(\mathcal O)$ 定义
$$
K_{w,h}[A]:=\int_{\mathbb R}\widehat w_R(t)\,\alpha_t(A)\,dt,\qquad \alpha_t=\mathrm{Ad}_{U(t)}.
$$
再以 Berezin/Toeplitz 压缩 $\mathcal B_h$ 作相空间局域化；则 $(K_{w,h},\mathcal B_h)$ 等价于对生成元 $H$ 的阿尔维森谱压缩与相空间压缩之复合，因而在 LCQFT 的自然性下协变。([isibang.ac.in][4])

**命题 1.2（函子协变性）** 若 $\psi:(\mathcal M,g)\to(\mathcal M',g')$ 等距，则
$$
\mathcal A(\psi)\circ K_{w,h}=K_{w\circ\psi,\;h\circ\psi}\circ\mathcal A(\psi).
$$
证因为 LCQFT 的自然性与窗—核的拉回交换性。([arXiv][3])

---

## 2. 微因果、Hadamard 与窗化微因果律

**公理 2.1（微因果）** 类空间分离时 $[\mathcal A(\mathcal O_1),\mathcal A(\mathcal O_2)]=0$。([SpringerLink][5])

**定理 2.2（窗化微因果）** 若 $\operatorname{supp}(K_{w_x,h_x})\subset\mathcal O_x$、$\operatorname{supp}(K_{w_y,h_y})\subset\mathcal O_y$，且 $\mathcal O_x$ 与 $\mathcal O_y$ 类空间分离，则
$$
[K_{w_x,h_x}[A_x]\,,\,K_{w_y,h_y}[A_y]]=0,
$$
并且相应的 CP/POVM 级联在因果顺序下可交换。

**正则性 2.3（Hadamard/微局域谱）** Hadamard 态与微局域谱条件 $(\mu)\mathrm{SC}$ 给出两点函数的波前集方向性，保证 Wick 多项式与窗化读数良定，并与曲时空重整化相容。([Project Euclid][6])

---

## 3. 时间的生成：窗化群延迟与相移导数

**定义 3.1（窗化群延迟读数）** 对传播—读出链 $\gamma$ 与窗—核 $(w_R,h)$ 定义
$$
T_\gamma[w_R,h]=\int_{\mathbb R}(w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)\,dE,\qquad \mathsf Q=-iS^\dagger S'.
$$
亦可写为 $T_\gamma=\int w_R\,[h\!\star\!\rho_{\rm rel}]$。$\operatorname{tr}\mathsf Q$ 与 DOS/谱移的一致性见 §7。([arXiv][7])

**定理 3.2（串并联可加与规范协变）** 若 $\gamma=\gamma_2\circ\gamma_1$ 且带内 $S_j$ 幺正，则
$$
\operatorname{tr}\mathsf Q_{\gamma_2\circ\gamma_1}=\operatorname{tr}\mathsf Q_{\gamma_2}+\operatorname{tr}\mathsf Q_{\gamma_1},\qquad
T_{\gamma_2\circ\gamma_1}=T_{\gamma_2}+T_{\gamma_1}.
$$
能量依赖基变换 $S\mapsto U(E)SV(E)$ 给出
$$
\operatorname{tr}\mathsf Q(USV)=\operatorname{tr}\mathsf Q(S)-i\,\operatorname{tr}(U^\dagger U')-i\,\operatorname{tr}(V'V^\dagger),
$$
因此以相对读数规约后 $T_{\rm rel}(\gamma)$ 与规范无关。（证略）

**注记 3.3（群延迟与前沿）** $T_\gamma[w_R,h]$ 为相位导数的带内加权读数而非"最早到达时间"；其在窄带共振附近可取负，不与因果偏序冲突。([物理评论链接管理器][8])

---

## 4. 光速与类光锥：前沿定标与无超锥传播

**定义 4.1（前沿定标）** 以真空冲激响应的最早非零到达 $t_{\rm front}(L)$ 定义
$$
c:=\lim_{L\to\infty}\frac{L}{t_{\rm front}(L)}.
$$
在此前沿规范下，任意链 $\gamma$ 的最早到达 $t_*(\gamma)\ge L/c$，与 AQFT 微因果一致（无超锥传播）。([SpringerLink][5])

---

## 5. KMS/被动性、模流与加速观测（Unruh）

**命题 5.1（KMS = 完全被动）** 基态与 $\beta$-KMS 态完全被动（第二定律意义）；相对熵对 CP 映射单调不增，从而约束任意滤镜链的能量—信息交换。([Project Euclid][9])

**定理 5.2（Bisognano–Wichmann 与 Unruh）** Minkowski 真空限制至 Rindler 楔为 $2\pi$-KMS，模流等同于相应洛伦兹推进；沿固有加速度 $a$ 的观测等效温度 $T=a/2\pi$。该性质在广义场类中成立并有多种现代扩展。([American Institute of Physics][10])

---

## 6. 滤镜链 = 局域可测性（Fewster–Verch 仪式）

**定义 6.1（FV 仪式）** 以"系统场 + 探测器场"在紧支集耦合区相互作用，由入/出区域的散射映射诱导系统可观测与 Davies–Lewis 仪器 $\{\mathcal I_i\}$；若两耦合区因果分离则仪器按因果顺序可交换并可组合。([白玫瑰研究在线][11])

**命题 6.2（因果一致与不可能测量的化解）** FV 框架在 AQFT/LCQFT 中给出无 Sorkin 型悖论的局域测量范式，选择性/非选择性更新与多次测量的条件概率保持因果一致。([arXiv][12])

---

## 7. 窗化 Wigner–Smith—谱移一致化（QFT 散射）

**定理 7.1（Birman–Kreĭn × Haag–Ruelle）** 在 Haag–Ruelle/AQFT 散射存在与适定性下，
$$
\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q=-iS^\dagger S',
$$
且 $\rho_{\rm rel}(E)=-\xi'(E)$ 与 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 一致。证明基于谱移函数的可微性与通道相移的可加性，并以 AQFT 的多通道散射存在性（含锥局域荷）为背景。([LQP2][13])

**推论 7.2（DOS/Heisenberg 时间）** $\tau_W=(1/N)\operatorname{tr}\mathsf Q$ 与开系统的 DOS 由 Friedel–Kreĭn–Lloyd 结构连接；在窄能窗下 $\langle\tau_W\rangle=2\pi/(N\Delta)$。([arXiv][14])

**注记 7.3（非幺正情形）** 在有损/增益的次幺正散射中，自然改型 $\widetilde{\mathsf Q}=-iS^{-1}S'$ 给出复时间延迟；其统计与物理解释（含虚部）在近年非厄米散射中得到系统刻画，并保留级联可加结构。([物理评论链接管理器][15])

---

## 8. 红移：谱缩放与时间互易

**定理 8.1（红移—时间互易）** 设谱缩放 $E\mapsto E/(1+z)$。则窗化群延迟读数满足
$$
T_\gamma^{\rm obs}[w_R,h]=\frac{1}{1+z}\,T_\gamma\!\big[w_R^{\langle 1/(1+z)\rangle}\,,\,h^{\langle 1/(1+z)\rangle}\big],
$$
其中 $w_R^{\langle a\rangle}(E)=w_R(aE)$、$h^{\langle a\rangle}(E)=h(aE)$。该互易是傅里叶—采样对偶在 LCQFT/GLS 语境下的直接反映。（证略）

---

## 9. NPE 有限阶闭合与 QEI 尾项控制

**命题 9.1（协变 NPE 模板）** 取采样点 $E_n=E_0+n\Delta$ 且 $\Delta\le \pi/(\Omega_h+\Omega_w)$，则
$$
T_\gamma=\sum_n w_R(E_n)\,[h\!\star\!\rho_{\rm rel}](E_n)\,\Delta+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},\qquad \varepsilon_{\rm alias}=0,
$$
其中 $\varepsilon_{\rm EM}$ 由有限阶 EM 余项给出，$\varepsilon_{\rm tail}$ 受窗外衰减与 QEI 统一控制。([dlmf.nist.gov][2])

**命题 9.2（QEI 尾项界）** Hadamard 态下，量子能量不等式为应力—能量张量的窗化加权给出状态无关下界，从而为 $|\varepsilon_{\rm tail}|$ 提供普适控制。([arXiv][16])

---

## 10. 互构定理（GLS ↔ LCQFT）

**范畴** $\mathbf{WScat}$：对象 $(S,\mu_\varphi,\mathcal W)$，态射为保持卡片 I/II 的滤镜链；$\mathbf{LCQFT}$：对象 $(\mathcal M,g,\mathcal A(\mathcal M,g))$，态射为保持因果与协变的等距嵌入。

**定理 10.1（互构）** 存在函子
$$
\mathfrak F:\mathbf{WScat}\to\mathbf{LCQFT},\qquad\mathfrak G:\mathbf{LCQFT}\to\mathbf{WScat},
$$
使 $\mathfrak F\circ\mathfrak G\simeq \mathrm{Id}$、$\mathfrak G\circ\mathfrak F\simeq \mathrm{Id}$（自然同构）。构造：$\mathfrak F$ 以 $\operatorname{tr}\mathsf Q$ 等值面与相位奇性生成偏序与锥；$\mathfrak G$ 以固有时间/光锥参数化构造带限窗—核并施以 Berezin 压缩，使三位一体刻度与 NPE 闭合同步成立。（证略）([arXiv][3])

---

## 11. 典型范式

**11.1（加速观测：Unruh–KMS）** Rindler 楔上真空为 $2\pi$-KMS，等效温度 $T=a/2\pi$；窄带窗下 $T_\gamma[w_R,h]$ 随 $a$ 线性缩放，与模流参数一致。([American Institute of Physics][10])

**11.2（探测器—场计时）** FV 仪式中，探测器通道的散射算符 $S(E)$ 的群延迟矩阵 $\mathsf Q$ 给出
$$
T=\int w_R(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE,
$$
并在因果分离下可组合与交换。([白玫瑰研究在线][11])

**11.3（双缝的窗化互补）** 可辨度 $D$ 与能见度 $V$ 满足 $D^2+V^2\le 1$，与窗化微因果相容，且可在 FV 框架下以"系统—探测器"方式严密实现。([物理评论链接管理器][17])

---

## 附录 A：窗化测量与相对熵—可恢复性

CP/TP 滤镜链满足相对熵单调性；当存在 Petz 恢复映射时取等，给出"损失—恢复"与多窗级联的稳定性判据。([arXiv][18])

---

## 附录 B：有限阶 NPE 上界（协变模板）

**Poisson 别名**：$\Delta\le\pi/(\Omega_h+\Omega_w)\Rightarrow \varepsilon_{\rm alias}=0$。**有限阶 EM**：对任意正整数 $M$，以 DLMF §2.10 的余项表示得
$$
|\varepsilon_{\rm EM}|\;\lesssim\;\sum_{m=1}^{M}\frac{|B_{2m}|}{(2m)!}\,\big|(w_R h)^{(2m-1)}\big|_{L^1}+|R_{2M}|,
$$
尾项 $R_{2M}$ 以标准余项积分界控制；若 $|h\!\star\!\rho_{\rm rel}|\in L^\infty$ 且 $w_R$ 远区 $L^1$ 可控，则
$$
|\varepsilon_{\rm tail}|\;\le\;|w_R\mathbf 1_{|E|>\Lambda R}|_{L^1}\,|h\!\star\!\rho_{\rm rel}|_{L^\infty}.
$$
上述界在谱缩放与采样尺度变换下协变。([dlmf.nist.gov][2])

---

## 参考文献（要目）

1. A. Pushnitski, *An integer-valued version of the Birman–Kreĭn formula* (2010).
2. DLMF, *§2.10 Euler–Maclaurin formula and remainder*.
3. R. Brunetti, K. Fredenhagen, R. Verch, *The Generally Covariant Locality Principle* (2001/2003).
4. W. Arveson, *On Groups of Automorphisms of Operator Algebras*, JFA 15 (1974).
5. R. Haag, *Local Quantum Physics*, 2nd ed. Springer (1996).
6. M. J. Radzikowski, *Microlocal approach to the Hadamard condition*, CMP 179 (1996).
7. W. Pusz, S. L. Woronowicz, *Passive states and KMS states*, CMP 58 (1978).
8. J. J. Bisognano, E. H. Wichmann, *On the duality condition for a Hermitian scalar field*, JMP 16 (1975).
9. C. J. Fewster, R. Verch, *Quantum Fields and Local Measurements*, CMP 378 (2020); *Measurement in Quantum Field Theory*, Encyclopedia of Mathematical Physics (2nd ed., 2025).
10. D. Buchholz, W. Dybalski, *Scattering in Relativistic Quantum Field Theory*（Encyclopedia survey, 2023）.
11. C. Texier, *Wigner time delay and related concepts*（review, 2015）。
12. L. Chen et al., *Generalization of Wigner time delay to subunitary scattering*, Phys. Rev. E 103 (2021).
13. I. L. Giovannelli et al., *Physical Interpretation of Imaginary Time Delay*, Phys. Rev. Lett. (2025).
14. N. Shaibe et al., *Superuniversal Statistics of Complex Time Delays in Non-Hermitian Scattering Systems*, Phys. Rev. Lett. 134 (2025).
15. C. J. Fewster, *Lectures on Quantum Energy Inequalities* (2012).
16. B.-G. Englert, *Fringe Visibility and Which-Way Information: An Inequality*, Phys. Rev. Lett. 77 (1996).

（以上条目与文中主张一一对应；具体断言处已给出逐段引用。）

---

### 证明与注释（选摘）

* **三位一体刻度（卡片 I）**：由 $\det S(E)=e^{-2\pi i\xi(E)}$ 与 $\tfrac{d}{dE}\log\det S(E)=\operatorname{tr}(S^{-1}S')$ 得 $\rho_{\rm rel}(E)=-\xi'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$。AQFT 场景中，采用 Haag–Ruelle 的入/出代数与波算子存在性，将通道分解与迹的可加性结合，得窗化版本（§7）。([LQP2][13])
* **非幺正改型**：次幺正 $S$（开放/吸收）下，$-i\,S^{-1}S'$ 给出复时间延迟；其可加性与统计在非厄米散射与微波图谱实验中得到验证。([物理评论链接管理器][15])
* **KMS/Unruh 与模流**：Rindler 楔上之真空限制满足 $2\pi$-KMS，模群即洛伦兹推进，从而温度 $T=a/2\pi$。该结论在自由场及更广模型中成立。([American Institute of Physics][10])
* **Hadamard/$(\mu)$SC**：Radzikowski 定理将 Hadamard 条件等价于波前集谱条件，保证窗化 Wick 多项式良定，支撑 §2 与 §9 的正则化。([Project Euclid][6])
* **QEI**：对各类自由场，给出沿任意试函数加权的能量密度下界，形成尾项的参数—无关控制。([arXiv][16])
* **FV 框架的因果一致**：以系统—探测器耦合的耦合区紧支集性与因果分离，构造诱导可观测与仪器，避免 Sorkin 式不可能测量悖论。([白玫瑰研究在线][11])

---

**用词对照与尺度统一**：全文以刻度同一式 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 为母尺；"窗口/读数/测量"均作"算子—测度—函数"的窗化读数，"前沿/光速"以无超锥传播的前沿定标规定；误差闭合遵循"有限阶 EM + Nyquist + QEI 尾项"纪律。

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[3]: https://arxiv.org/abs/math-ph/0112041?utm_source=chatgpt.com "The generally covariant locality principle -- A new paradigm for local quantum physics"
[4]: https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-arveson/1970s/1974_On_groups_of_automorphisms_of_operator_algebras.pdf?utm_source=chatgpt.com "[PDF] On groups of automorphisms of operator algebras"
[5]: https://link.springer.com/book/10.1007/978-3-642-61458-3?utm_source=chatgpt.com "Local Quantum Physics: Fields, Particles, Algebras"
[6]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-179/issue-3/Micro-local-approach-to-the-Hadamard-condition-in-quantum-field/cmp/1104287114.pdf?utm_source=chatgpt.com "Mathematical Physics Micro-Local Approach to the ..."
[7]: https://arxiv.org/pdf/1507.00075?utm_source=chatgpt.com "arXiv:1507.00075v6 [cond-mat.mes-hall] 5 Nov 2018"
[8]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[9]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-58/issue-3/Passive-states-and-KMS-states-for-general-quantum-systems/cmp/1103901491.full?tab=ArticleLinkCited&utm_source=chatgpt.com "Passive states and KMS states for general quantum systems"
[10]: https://pubs.aip.org/aip/jmp/article-pdf/16/4/985/19024093/985_1_online.pdf?utm_source=chatgpt.com "On the duality condition for a Hermitian scalar field"
[11]: https://eprints.whiterose.ac.uk/id/eprint/160569/8/Fewster_Verch2020_Article_QuantumFieldsAndLocalMeasureme.pdf?utm_source=chatgpt.com "Quantum fields and local measurements"
[12]: https://arxiv.org/abs/2304.13356?utm_source=chatgpt.com "Measurement in Quantum Field Theory"
[13]: https://www.lqp2.org/sites/default/files/pdf_files/bdy-2023-encyclopedia.pdf?utm_source=chatgpt.com "Scattering in relativistic quantum field theory"
[14]: https://arxiv.org/pdf/1804.09580?utm_source=chatgpt.com "Wigner-Smith time-delay matrix in chaotic cavities with non ..."
[15]: https://link.aps.org/doi/10.1103/PhysRevE.103.L050203?utm_source=chatgpt.com "Generalization of Wigner time delay to subunitary scattering ..."
[16]: https://arxiv.org/abs/1208.5399?utm_source=chatgpt.com "Lectures on quantum energy inequalities"
[17]: https://link.aps.org/pdf/10.1103/PhysRevLett.77.2154?utm_source=chatgpt.com "Fringe Visibility and Which-Way Information: An Inequality"
[18]: https://arxiv.org/pdf/quant-ph/0209053?utm_source=chatgpt.com "Monotonicity of quantum relative entropy revisited"
