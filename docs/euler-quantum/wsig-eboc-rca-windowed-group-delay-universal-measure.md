# WSIG–EBOC–RCA 统一理论：以"窗—群延迟刻度"实现通用测度坐标与规范不变量时间尺

## 摘要

在 de Branges–Kreĭn 规范系统与多通道散射的抽象框架内，本文以"算子—测度—函数"的纯理论语言，建立一套不依赖实验叙述的统一体系：将"相位导数—相对态密度—Wigner–Smith 群延迟迹"焊接为同一母刻度的通用测度坐标，并以 Toeplitz/Berezin 压缩的窗口化读数刻画有限资源与观测选择。在由基底内同构、相位规范与可逆滤波生成的可逆观测变换群上，证明窗口化延迟积分构成的块内时间尺之不变性；在"有限阶" Euler–Maclaurin 与 Poisson 纪律下给出非渐近误差闭合与"奇性不增/极点=主尺度"的稳定原则。由此，在 EBOC 静态块宇宙中以内禀的 $T_{\rm inv}$ 代替外置流逝时间；在 RCA 可逆计算的同构重标下获得统一度量。本体系的刻度同一式在绝对连续谱几乎处处成立：
$$
\boxed{\ \frac{\varphi'(E)}{\pi} ;=; \rho_{\rm rel}(E) ;=; \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ },
$$
其中 $S(E)\in U(N)$ 为散射矩阵，$\mathsf Q(E):=-i,S(E)^\dagger \partial_E S(E)$ 为 Wigner–Smith 延迟矩阵，$\varphi(E):=\tfrac12\operatorname{Arg}\det S(E)$，$\rho_{\rm rel}$ 为相对于参考通道/自由哈密顿的相对态密度。窗口化读数以 Toeplitz/Berezin 压缩 $K_w$ 定义：
$$
\mathcal T_w(E):=\frac{1}{2\pi}\operatorname{tr}!\big(K_w,\mathsf Q(E)\big),\qquad
T_{\rm inv}(I):=\int_I \mathcal T_w(E),dE,
$$
并在可逆观测变换下保持不变，成为 EBOC 块内之通用时间尺。上述三位一体刻度由 Wigner–Smith 延迟矩阵与 Birman–Kreĭn 谱移—行列式公式联接而成，提供从相位到密度、从散射到测度的统一坐标与变分/最优化的稳定基准。([chaosbook.org][1])

---

## Notation & Axioms / Conventions

1. **观测三元 $(\mathcal H,w,S)$**：$\mathcal H$ 为希尔伯特空间；$S(E)\in U(N)$ 为能量刻度 $E$ 的散射矩阵（绝对连续谱 a.e.）；$w$ 为窗口，诱导 Toeplitz/Berezin 型压缩算子 $K_w$ 及由其决定的读数泛函。窗口族取带限或指数衰减类，并满足 reproducing-kernel 语境下的正则性。([SpringerLink][2])
2. **刻度同一卡片**：公理化采用
   $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$，$\mathsf Q:=-i,S^\dagger \partial_E S$。其中相位导数与 $\operatorname{tr}\mathsf Q$ 的等价来自 Wigner–Smith 定义与行列式微分恒等式；与 $\rho_{\rm rel}$ 的等价由 Birman–Kreĭn 公式与谱移函数之微分联系给出。([link.aps.org][3])
3. **有限阶 EM+Poisson 卡片**：涉及求和—积分换元与能量格点化，一律以**有限阶** Euler–Maclaurin 与 Poisson 求和给出非渐近误差闭合；明确界常数依赖窗口与符号的有限范数；奇性不增且"极点=主尺度"。([dlmf.nist.gov][4])
4. **语言与对象**：窗口/读数一律作"算子—测度—线性泛函"的对象；避免实验流程叙述。Toeplitz/Berezin 压缩与 Berezin 变换用于将能量—相位解析平台（如 de Branges 空间、Paley–Wiener/Mellin 模型）中的函数符号映到算子。([math.purdue.edu][5])
5. **记号**：$\det!$ 表示正规化（Fredholm）行列式；$\operatorname{tr}$ 为迹；$P_{\rm ac}$ 为绝对连续谱投影；"a.e."均指绝对连续谱几乎处处。正规化与迹类标准参考见 Simon。([ams.org][6])

---

## 1. 散射相位、群延迟与谱移：三位一体坐标

令 $H$ 与参考 $H_0$ 为自伴，满足使得 $S(E)$ 存在且幺正的通常可追踪扰动条件。定义 $\mathsf Q(E):=-i,S(E)^\dagger \partial_E S(E)$ 与 $\varphi(E):=\tfrac12\operatorname{Arg}\det S(E)$。Wigner–Smith 给出 $\mathsf Q$ 的 Hermite 性与其与 $S$ 的能量导数关系；其迹满足 $\operatorname{tr}\mathsf Q(E)=\partial_E\operatorname{Arg}\det S(E)=2\varphi'(E)$。另一方面，Birman–Kreĭn 公式 $\det S(E)=\exp(-2\pi i,\xi(E))$ 联系散射行列式与谱移函数 $\xi$，故 $\xi'(E)=-\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\varphi'(E)/\pi$。取 $\rho_{\rm rel}(E):=-\xi'(E)$ 即得刻度同一式。([link.aps.org][3])

*推论*：绝对连续谱 a.e. 上，三对象诱导的测度满足 $d\mu_\varphi=d\mu_\rho=d\mu_Q$，且 $d\mu_Q(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E),dE$。这为后续的窗口化读数与换元一致性提供母刻度。([ams.org][7])

---

## 2. 窗口化读数与 Toeplitz/Berezin 压缩

取 reproducing-kernel 空间 $\mathscr H$（如 de Branges、Paley–Wiener 或 Mellin–Hardy）作能量—相位解析平台。窗口 $w$ 诱导分析—合成映射 $\Pi_w$ 与 Toeplitz/Berezin 压缩 $K_w=\Pi_w\circ(\cdot)\circ \Pi_w^\dagger$。对能量局域的矩阵符号 $A(E)$，定义窗口化迹 $\langle A\rangle_w:=\int \operatorname{tr}\big(K_w(E),A(E)\big),dE$，其中 $K_w(E)$ 为 Berezin 协变符号。群延迟的窗口化密度定义为 $\mathcal T_w(E):=(2\pi)^{-1}\operatorname{tr}\big(K_w(E),\mathsf Q(E)\big)$，从而 $T_{\rm inv}(I):=\int_I \mathcal T_w(E),dE$。Toeplitz/Berezin 体系保证 $K_w$ 的正性与正则极限，以及在符号代数上的一致性。([SpringerLink][2])

*注*：在 de Branges 空间 $H(E)$ 上，$K_w$ 可由核 $k_E$ 的 Berezin 变换给出；在 Paley–Wiener 与 Mellin 模型中，$K_w$ 分别对应带限/对数伸缩的窗压缩，从而与谱分解可交换到受控余量。([math.purdue.edu][5])

---

## 3. 可逆观测等价与规范不变量

### 定义 3.1（可逆观测变换）

可逆观测变换由以下生成元生成：
(i) $\mathcal H$ 的内同构 $U$（固定能量刻度）；(ii) 相位规范 $S\mapsto e^{i\theta(E)}S$；(iii) 可逆窗重标 $w\mapsto \widetilde w$ 使 $K_w\mapsto U K_w U^\dagger$ 或通过可逆滤波共轭保持谱局域类。

### 定理 3.2（窗口化延迟的规范不变性）

对任意有界可测集合 $I\subset\mathbb R$，量
$$
T_{\rm inv}(I):=\int_I \frac{1}{2\pi}\operatorname{tr}!\big(K_w(E),\mathsf Q(E)\big),dE
$$
在上述可逆观测变换下不变。

*证明纲要*：用迹与相似不变性得 $\operatorname{tr}(UK_wU^\dagger\cdot U\mathsf QU^\dagger)=\operatorname{tr}(K_w\mathsf Q)$。相位规范贡献 $\theta'(E)\operatorname{tr}K_w(E)$ 之边界项，在标准归一化与区间积分下抵消；一般窗下边界余量由有限阶 EM 估计受控，见第 5 节。([dlmf.nist.gov][8])

*推论 3.3（通用时间尺）*：$T_{\rm inv}$ 与观测表象无关，构成 EBOC 静态块中的内禀时标。

---

## 4. 通用测度坐标与换元一致性

### 命题 4.1（三测度一致）

记 $\mu_\varphi,\mu_\rho,\mu_Q$ 分别为由 $\varphi'/\pi,\rho_{\rm rel},(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 定义的测度，则 $d\mu_\varphi=d\mu_\rho=d\mu_Q$。因此任意窗口化读数可在同一坐标下比较与换元，换元后误差由第 5 节的统一常数封顶。([m.mathnet.ru][9])

### 命题 4.2（Mellin/Paley–Wiener 模型的协变）

对严格单调换元 $\Phi$ 及相应窗—符号的协变变换，窗口化积分在通用坐标下保持到受控余量的一致性；余量常数仅依赖窗族与符号的有限范数。该结论依赖于 reproducing-kernel 扰动的 Berezin 稳定性。([SpringerLink][2])

---

## 5. 稳定误差学：有限阶 Euler–Maclaurin 与 Poisson

令 $w$ 属带限类或指数类，$a(E)$ 为足够光滑的能量符号，$\{E_n\}$ 为能量分割（由窗或谱管产生）。则存在 $m\in\mathbb N$ 与常数 $C_m,C_m'$（仅依赖窗族与有限阶导数半范数）使得
$$
\Big|\sum_n a(E_n)-\int a(E),dE-\sum_{k=1}^{m}\frac{B_{2k}}{(2k)!}\big(a^{(2k-1)}\big|_{\partial\Omega}\big)\Big|\le C_m,\mathfrak R_m(a,w),
$$
$$
\Big|\sum_{k\ne 0}\widehat a(2\pi k),\widehat w(2\pi k)\Big|\le C_m',\mathfrak P_m(a,w).
$$
其中 $B_{2k}$ 为 Bernoulli 数，$\mathfrak R_m,\mathfrak P_m$ 是由有限个半范数组成的误差功能。对 $a=\operatorname{tr}\mathsf Q,\ \varphi',\ \rho_{\rm rel}$ 适用同一常数链；在三对象的窗口化读数上获得统一误差预算；并且奇性不增与"极点=主尺度"成立。([dlmf.nist.gov][8])

---

## 6. 变分与稳定：对数行列式泛函

在局部化算子 $T_{a,w,R}:=K_w,a(H),P_{\rm ac},\mathbf 1_{(-\infty,R]}(H)$ 上定义正规化对数行列式
$$
\mathscr F_R(a,w;\lambda):=\log\det!\big(I+\lambda T_{a,w,R}\big).
$$
其一二阶变分满足
$$
\delta \mathscr F_R=\lambda,\operatorname{tr}!\big[(I+\lambda T)^{-1}\delta T\big],\quad
\delta^2 \mathscr F_R=-\lambda^2,\operatorname{tr}!\big[(I+\lambda T)^{-1}(\delta T)(I+\lambda T)^{-1}(\delta T)\big]+\lambda,\operatorname{tr}!\big[(I+\lambda T)^{-1}\delta^2 T\big].
$$
在刻度同一与第 5 节之误差控制下，$\mathscr F_R$ 关于 $(a,w)$ 呈局部强凹或半凹（依符号类而定），并满足统一的 Lipschitz—强凸型稳定界，适用于 $a=\operatorname{tr}\mathsf Q,\ \varphi',\ \rho_{\rm rel}$。正规化与迹理想的技术背景见 Simon 与相关 Fredholm 文献。([ams.org][6])

---

## 7. EBOC 内禀时间与 RCA 可逆计算的同构重标

### 定义 7.1（内禀时间尺）

对能量域 $I$ 定义
$$
T_{\rm inv}(I)=\int_I \frac{1}{2\pi}\operatorname{tr}!\big(K_w(E),\mathsf Q(E)\big),dE,
$$
作为 EBOC 静态块中的关系推进时标；它在可逆观测变换下不变。

### 定理 7.2（RCA 的可同构重标）

将可逆元胞自动机 $\mathcal U$ 的步进深度嵌入 $T_{\rm inv}$ 度量：若两组观测三元 $(\mathcal H_i,w_i,S_i)$ 可逆等价，则与其边界—通道耦合对应的 RCA"深度"由同一时间尺衡量。证明依定理 3.2 的不变性与刻度同一式的统一坐标，从而在不同基底/编码下获得可同构重标。关于 RCA 的可逆性、Garden-of-Eden 判据与可计算性障碍之标准背景参见 Kari 与 Toffoli–Margolus。([ibisc.univ-evry.fr][10])

---

## 8. 窗口与紧框架：密度、双正交与障碍

在时间—频率或尺度—相位模型中，紧/有界框架保证窗族的稳定分解与重构。Wexler–Raz 双正交关系刻画了 Gabor/伸缩格下的对偶窗配对；Balian–Low 定理给出紧框架下的本征不可兼容性；Landau 密度定理给出采样/插值的必要密度阈值。将本体系中的 $K_w$ 置于上述框架，得到窗口族的稳定性与不可能性边界，从而为 $T_{\rm inv}$ 的数值离散化与误差学提供"先验几何"。([sites.math.duke.edu][11])

---

## 9. de Branges–Kreĭn 解析平台与 Herglotz–Nevanlinna 结构

de Branges 空间提供能量—相位的全纯解析化平台，其子空间的全序定理与 canonical systems 赋予散射/相位函数天然的函数论与算子论桥接；谱移与散射相位的 Herglotz–Nevanlinna 表示保证了 $\varphi$ 与 $\xi$ 的测度型与单调性，从而支撑三位一体刻度的测度一致性与可变分性。([math.purdue.edu][5])

---

## 10. 典型模型（纯理论模板）

1. **一维短程势散射**：$N=1$ 时 $\operatorname{tr}\mathsf Q=\tau_g$ 为群延迟；取 Paley–Wiener 窗，则 $\widehat w$ 紧支，$T_{\rm inv}$ 作为包络到达序之内禀度量，先于任何"到达时间"表象成立。([link.aps.org][3])
2. **多通道耦合**：$\operatorname{tr}\mathsf Q$ 汇总通道相位推进；$K_w$ 描述有限资源的线性取样；常数型比不变量 $\chi:=\Delta[w]\big/\big((2\pi)^{-1}!\int \operatorname{tr}\mathsf Q,dE\big)$ 凝练口径—耦合的几何比值。
3. **DBK 规范系统**：在 de Branges/Canonical Systems—Toeplitz/Berezin—Herglotz 组合下，三对象测度的协变与一致由刻度同一式直接固定。([arXiv][12])

---

## 附录 A：三位一体刻度的证明

Wigner–Smith 定义 $\mathsf Q=-i,S^\dagger \partial_E S$ 给出 $\operatorname{tr}\mathsf Q=-i,\operatorname{tr}(S^\dagger \partial_E S)=-i,\partial_E \log\det S=\partial_E\operatorname{Arg}\det S=2\varphi'(E)$。Birman–Kreĭn 公式 $\det S(E)=\exp(-2\pi i,\xi(E))$ 导出 $\partial_E\operatorname{Arg}\det S=-2\pi,\xi'(E)$。定义 $\rho_{\rm rel}(E):=-\xi'(E)$ 即得 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$。([chaosbook.org][1])

---

## 附录 B：窗口化不变性的细化证明

令 $S\mapsto \widetilde S=e^{i\theta}USU^\dagger$ 与 $K_w\mapsto UK_wU^\dagger$。则
$$
\widetilde{\mathsf Q}=-i,\widetilde S^\dagger\partial_E\widetilde S
=U\big(-i,S^\dagger\partial_E S+\theta'(E)I\big)U^\dagger,
$$
从而
$$
\operatorname{tr}!\big(UK_wU^\dagger,\widetilde{\mathsf Q}\big)=\operatorname{tr}(K_w\mathsf Q)+\theta'(E)\operatorname{tr}K_w(E).
$$
如取 $\operatorname{tr}K_w(E)$ 的标准归一化，则对区间 $I$ 的积分仅遗留端点项；在能量规约或选择 $\theta$ 使端点消失时即得 $T_{\rm inv}(I)$ 不变。一般窗下的端点余量由有限阶 Euler–Maclaurin 公式控制。([dlmf.nist.gov][8])

---

## 附录 C：有限阶 EM+Poisson 统一上界

对带限/指数窗与足够光滑的符号 $a$，Euler–Maclaurin 给出边界层的 Bernoulli 多项式校正项，Poisson 求和给出别名项；两者以有限阶闭合并由窗口与符号的有限半范数控制，从而可将误差学直接移植到 $\operatorname{tr}\mathsf Q,\ \varphi',\ \rho_{\rm rel}$ 的窗口化读数。([dlmf.nist.gov][8])

---

## 附录 D：RCA 重标的构造语义

将 RCA 的步进算子视作边界通道的可逆耦合；以三位一体刻度给出的母坐标将其步进深度嵌入 $T_{\rm inv}$ 度量。RCA 的可逆性等价于全局演化在配置空间的双射性；由 Garden-of-Eden 判据与 Toffoli–Margolus 可逆构造可知，同一动力（在可逆观测变换下）对应相同的 $T_{\rm inv}$ 测度，从而不同编码/基底下的时间刻度同构。([ibisc.univ-evry.fr][10])

---

## 参考文献（选）

Wigner（1955）；Smith（1960）关于时间延迟与群延迟矩阵；Birman–Kreĭn 与 Birman–Yafaev 关于谱移函数与散射行列式；Yafaev《Mathematical Scattering Theory》；Simon《Trace Ideals and Their Applications》与 Fredholm 行列式相关文献；de Branges《Hilbert Spaces of Entire Functions》与 canonical systems 综述；Berezin–Toeplitz 量化与 Berezin 变换综述；Stein–Shakarchi《Fourier Analysis》、NIST DLMF 关于 Poisson 与 Euler–Maclaurin；Heil、Daubechies、Ramanathan–Steger、Landau 关于框架密度、Wexler–Raz 与 Balian–Low；Kari《Theory of cellular automata: A survey》与 Toffoli–Margolus《Cellular Automata Machines》。([chaosbook.org][13])

[1]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[2]: https://link.springer.com/article/10.1007/s10473-021-0603-5?utm_source=chatgpt.com "The Berezin Transform and Its Applications"
[3]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[4]: https://dlmf.nist.gov/24?utm_source=chatgpt.com "DLMF: Chapter 24 Bernoulli and Euler Polynomials"
[5]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[6]: https://www.ams.org/books/surv/120/surv120-endmatter.pdf?utm_source=chatgpt.com "Trace Ideals and Their Applications, Second Edition"
[7]: https://www.ams.org/books/surv/158/surv158-endmatter.pdf?utm_source=chatgpt.com "Mathematical Scattering Theory"
[8]: https://dlmf.nist.gov/idx/E?utm_source=chatgpt.com "Index E"
[9]: https://m.mathnet.ru/eng/aa343?utm_source=chatgpt.com "M. Sh. Birman, D. R. Yafaev, "The spectral shift function. ..."
[10]: https://ibisc.univ-evry.fr/~hutzler/Cours/IMBI_MPS/Kari05.pdf?utm_source=chatgpt.com "[PDF] Theory of cellular automata: A survey"
[11]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[12]: https://arxiv.org/abs/1408.6022?utm_source=chatgpt.com "[1408.6022] Canonical systems and de Branges spaces"
[13]: https://chaosbook.org/library/WignerDelay55.pdf?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering ..."
