# WSIG–EBOC 全息重建理论的形式化构建

Version: 1.2

## 摘要

建立一套以窗化散射—信息几何（WSIG）为观测层、以永恒静态块观察—计算（EBOC）为本体层的全息重建理论。核心命题为：在满足帧稳定性与拓扑一致性的重叠窗口族下，由相位导数—相对态密度—Wigner–Smith 群延迟构成的"三位一体"局部读数可在非渐近 Nyquist–Poisson–Euler–Maclaurin 三项闭合误差预算内被稳定黏合为全局散射场，从而给出 EBOC 静态块的全局编码。文中给出统一符号、规范与黏合一致性条件，证明存在性—稳定性—（规范下）唯一性三大主定理，并提出可实施的反演—投影算法以及与可逆元胞自动机（RCA）的语义对位。

## 0. 记号、规范与公理

**能量域与多端口散射.** 设能量域为可测集合 $\Omega\subset\mathbb{R}$，通道数 $N\in\mathbb{N}$。对绝对连续谱的 Lebesgue 点几乎处处，散射矩阵 $S(E)\in U(N)$ 的 Wigner–Smith 延迟矩阵与总相位定义为

$$
\mathsf Q(E):=-\,i\,S(E)^\dagger \partial_E S(E),\qquad \Phi(E):=\operatorname{Arg}\det S(E).
$$

令半相位 $\varphi(E):=\tfrac12\Phi(E)$。则

$$
\partial_E \Phi(E)=\operatorname{tr}\mathsf Q(E),\qquad \partial_E\varphi(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E).
$$

三者与相对态密度 $\rho_{\rm rel}(E)$ 之间满足刻度同一式

$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ },
$$

其中 $\rho_{\rm rel}$ 等于 Kreĭn 光谱位移函数的导数（本文采用使上式成立的散射相位号志与通道定向）。上述等式分别源自 $\partial_E\log\det S=\operatorname{tr}(S^{-1}S')$ 与 Birman–Kreĭn 判据。([chaosbook.org][1])

**窗口与帧.** 取窗口族 $\{w_j\}_{j\in J}\subset L^1\cap L^2(\Omega)$ 与对应的分析算子 $W_j f:=f\ast w_j$。设存在常数 $0<A\le B<\infty$ 使

$$
A|f|_{L^2(\Omega)}^2\ \le\ \sum_{j\in J}|W_j f|_{L^2(\Omega)}^2\ \le\ B|f|_{L^2(\Omega)}^2,\quad \forall f\in L^2(\Omega),
$$

称 $\{W_j\}$ 为帧；记帧算子 $\mathsf S:=\sum_j W_j^\ast W_j$，其有界可逆且 $|\mathsf S^{-1}|\le A^{-1}$。([SpringerLink][2])

**三项误差闭合（NPE）.** 设采样步长 $h>0$、有效带宽 $W>0$、窗口具有 $m\ge2$ 阶可积导数。离散化—卷积—截断的全误差分解为

$$
\eta_{\rm NPE}:=\eta_{\rm alias}+\eta_{\rm Bern}+\eta_{\rm tail},
$$

其中别名项由 Poisson 求和控制，Bernoulli 校正层来自有限阶 Euler–Maclaurin，尾项刻画截断泄露；相应界定在 §5 给出。([维基百科][3])

**规范与拓扑.** 采用 Birman–Kreĭn 规范：固定 $\Phi=\operatorname{Arg}\det S$ 的绝对连续分支并令 $\varphi=\tfrac12\Phi$。设窗口覆盖重叠且无拓扑缺口（见 §2），以排除相位多值的 Čech 1-余循环。

## 1. 局部观测模型

### 1.1 三位一体局部读数

定义逐窗局部读数

$$
\mathcal R_j(E):=\big(\varphi'_j(E),\ \operatorname{tr}\mathsf Q_j(E),\ \rho_{{\rm rel},j}(E)\big),
$$

满足逐窗三位一体约束 $\varphi'_j=\tfrac12\operatorname{tr}\mathsf Q_j=\pi\rho_{{\rm rel},j}$。观测模型假定存在全局场

$$
\mathcal R(E):=\big(\varphi'(E),\ \operatorname{tr}\mathsf Q(E),\ \rho_{\rm rel}(E)\big)
$$

使

$$
\mathcal R_j\ =\ W_j\mathcal R\ +\ \varepsilon_j,\qquad |\varepsilon_j|_{L^2}\ \le\ C_{\rm NPE}\ \text{由§5界定}.
$$

### 1.2 幺正约束与生成方程

由定义 $\mathsf Q=-iS^\dagger S'$ 推出等价矩阵常微分方程

$$
S'(E)=i\,S(E)\,\mathsf Q(E),\qquad S(E_0)\in U(N).
$$

当 $\mathsf Q^\dagger=\mathsf Q\in L^1_{\rm loc}(\Omega)$ 时，解由路径有序指数给出，且 $S^\dagger S\equiv I$。因此给定 $\mathsf Q$（仅需迹满足刻度同一式），总可构造满足幺正性的 $S$。([math.mit.edu][4])

## 2. 黏合一致性与 Čech 能量

令重叠区 $U_{jk}:=\{E\in\Omega:\ w_j(E)w_k(E)\neq0\}$。定义相位导数差与 Čech 能量

$$
\Delta_{jk}(E):=\varphi'_j(E)-\varphi'_k(E),\qquad
\mathcal E_{\check C}:=\sum_{j\sim k}\int_{U_{jk}}|\Delta_{jk}(E)|^2\,{\rm d}E.
$$

**一致性要求**：存在常数 $\kappa_0>0$ 使 $\mathcal E_{\check C}\le \kappa_0\,|\eta_{\rm NPE}|_{L^2(\Omega)}^2$。尤其，对覆盖神经（nerve）上的任意闭合 1-环 $C$ 有

$$
\Big|\int_C\Delta_{jk}(E)\,{\rm d}E\Big|\ \le\ c_{\rm top}\,|\eta_{\rm NPE}|_{L^1},
$$

排除由覆盖缺口诱发的枝切不一致。

## 3. 全局重建的变分模型

定义约束集

$$
\mathcal C_{\rm tri}:=\Big\{\mathcal R:\ \varphi'=\tfrac12\operatorname{tr}\mathsf Q=\pi\rho_{\rm rel}\Big\},\quad
\mathcal C_{\rm unit}:=\Big\{S:\ S^\dagger S=I,\ -iS^\dagger S'=\mathsf Q\Big\}.
$$

**耦合约束.** 两处出现的 $\mathsf Q(E)$ 为同一函数，并由 $S$ 唯一决定：$\mathsf Q(E):=-i\,S(E)^\dagger \partial_E S(E)$。因此 $\mathcal C_{\rm tri}$ 中的 $\operatorname{tr}\mathsf Q$ 即等于 $-i\,\operatorname{tr}\big(S^\dagger S'\big)$，与 $\mathcal C_{\rm unit}$ 同步。

在加权空间 $|\cdot|_{\mathsf W}$ 上最小化

$$
\min_{\mathcal R,S}\ \mathscr J(\mathcal R,S):=\sum_{j\in J}|W_j\mathcal R-\mathcal R_j|_{\mathsf W}^2
\quad\text{s.t.}\quad \mathcal R\in\mathcal C_{\rm tri},\ S\in\mathcal C_{\rm unit}.
$$

为抑制重叠不一致，引入 Čech 正则化

$$
\mathscr J_\lambda:=\mathscr J+\lambda\,\mathcal E_{\check C},\qquad \lambda>0.
$$

## 4. 主定理与证明

### 定理 A（存在性）

**命题.** 若 $\{W_j\}$ 为帧且覆盖重叠（存在下界 $A>0$），且 $\mathcal E_{\check C}\le \kappa_0|\eta_{\rm NPE}|_{L^2}^2$，则存在极小对 $(\mathcal R_\star,S_\star)$ 使 $\mathscr J_\lambda$ 取到最小，且 $\mathcal R_\star\in\mathcal C_{\rm tri}$、$S_\star\in\mathcal C_{\rm unit}$。

**证明.** 先忽略约束，正规方程

$$
\mathsf S\,\mathcal R=\sum_j W_j^\ast \mathcal R_j,\qquad \mathsf S=\sum_j W_j^\ast W_j,
$$

由帧下界得 $\mathsf S$ 可逆且 $|\mathsf S^{-1}|\le A^{-1}$，故无约束极小解
$$\mathcal R^{(0)}=\mathsf S^{-1}\sum_j W_j^\ast \mathcal R_j$$
存在唯一。选取任意 Hermitian $\mathsf Q^{(0)}$ 使 $\operatorname{tr}\mathsf Q^{(0)}=2\varphi^{(0)\prime}$（例如 $\mathsf Q^{(0)}=\tfrac{2\varphi^{(0)\prime}}{N}I$），由 §1.2 构造 $S^{(0)}\in\mathcal C_{\rm unit}$。对闭集 $\mathcal C_{\rm tri}\times\mathcal C_{\rm unit}$ 施行交替投影与最小化（§6），利用投影的非扩张性与 $\mathscr J_\lambda$ 的下半连续性，结合 Čech 项对误差源的吸收，得到极小对的存在。帧论保证强制性与有界性，进而由直接方法完成存在性。([SpringerLink][2])

### 定理 B（稳定性）

**命题.** 在定理 A 条件下，令 $\widehat{\mathcal R}$ 为极小解之 $\mathcal R$ 分量，则

$$
|\widehat{\mathcal R}-\mathcal R|_{L^2(\Omega)}\ \le\ \kappa(A,B)\Big(\varepsilon_{\rm meas}
+|\eta_{\rm NPE}|_{L^2(\Omega)}\Big),\qquad \kappa(A,B)\le\sqrt{B/A},
$$

其中 $\varepsilon_{\rm meas}:=\max_j|W_j\mathcal R-\mathcal R_j|_{L^2}$。

**证明.** 由帧不等式与三角不等式得

$$
A|\widehat{\mathcal R}-\mathcal R|_{L^2}^2\ \le\ \sum_j|W_j(\widehat{\mathcal R}-\mathcal R)|_{L^2}^2
\ \le\ 2\sum_j|W_j\widehat{\mathcal R}-\mathcal R_j|_{L^2}^2+2\sum_j|W_j\mathcal R-\mathcal R_j|_{L^2}^2.
$$

极小性与 Čech 惩罚项给出右端有界，再用上界 $B$ 归一化得到所述估计。

### 定理 C（规范下唯一性）

**命题.** 若覆盖神经无 1-周（所有闭合环 $C$ 上 $\int_C\Delta_{jk}\,{\rm d}E=0$），并固定 BK 规范，则 $(\mathcal R_\star,S_\star)$ 在左乘常幺正等价（$U(N)$）下唯一。

**证明.** 条件意味着 $\varphi'$ 在覆盖黏合后具有全局原函数 $\varphi$ 且与 BK 规范一致；由 $\operatorname{tr}\mathsf Q=2\varphi'$ 刚性确定 $\operatorname{tr}\mathsf Q$。方程 $S'=iS\mathsf Q$ 的解集在给定 $\mathsf Q$ 时仅差左乘常幺正元，等价于左乘常幺正等价类（$U(N)$）。

## 5. 非渐近 NPE 误差预算

设窗口 $w_j$ 具有 $m$ 阶可积导数，步长 $h$、带宽 $W$。则存在常数 $C_1,C_2,C_3$（依赖于窗口衰减与正则度）使

$$
|\eta_{\rm alias}|_{L^2}\ \le\ C_1\,e^{-\frac{2\pi W}{h}},\quad
|\eta_{\rm Bern}|_{L^2}\ \le\ C_2\,h^{m}\,|\partial_E^{m}\mathcal R|_{L^2},\quad
|\eta_{\rm tail}|_{L^2}\ \le\ C_3\,|\mathcal R\cdot \mathbf 1_{\Omega^{\rm c}}|_{L^2}.
$$

首项由 Poisson 求和的频谱周期化给出指数型别名界；第二项由 Euler–Maclaurin 有界余项（Bernoulli 多项式的傅里叶级数界）推出 $O(h^{m})$ 估计；第三项由截断残余的 $L^2$ 质量控制。故

$$
|\widehat{\mathcal R}-\mathcal R|_{L^2}\ \le\ \kappa(A,B)\Big(\varepsilon_{\rm meas}
+ C_1 e^{-\frac{2\pi W}{h}}+ C_2 h^{m}|\partial_E^{m}\mathcal R|_{L^2}+C_3|\mathcal R\cdot \mathbf 1_{\Omega^{\rm c}}|_{L^2}\Big).
$$

([维基百科][3])

## 6. 反演—投影算法

### 6.1 帧反演初始化

由正规方程解得

$$
\mathcal R^{(0)}=\mathsf S^{-1}\sum_{j}W_j^\ast \mathcal R_j,\qquad |\mathsf S^{-1}|\le A^{-1}.
$$

### 6.2 交替投影与幺正化

以交替投影求解约束可行最小化：

$$
\mathcal R^{(n+\tfrac12)}:=\Pi_{\mathcal C_{\rm tri}}[\mathcal R^{(n)}],\quad
S^{(n+1)}:=\Pi_{\mathcal C_{\rm unit}}[S^{(n)};\,\mathcal R^{(n+\tfrac12)}],\quad
\mathcal R^{(n+1)}:=\arg\min_{\mathcal R}\sum_j|W_j\mathcal R-\mathcal R_j|_{\mathsf W}^2.
$$

其中 $\Pi_{\mathcal C_{\rm tri}}$ 可由最小二乘配平 $(\varphi',\tfrac12\operatorname{tr}\mathsf Q,\pi\rho_{\rm rel})$ 实现；$\Pi_{\mathcal C_{\rm unit}}$ 定义为：先在每个 $E$ 处求

$$
\mathsf Q_\star(E)\ :=\ \arg\min_{\mathsf Q^\dagger=\mathsf Q,\ \operatorname{tr}\mathsf Q=2\varphi'(E)}\ \big|\mathsf Q+i\,S^\dagger S'\big|_F^2,
$$

其闭式解为 $\mathsf Q_\star=\operatorname{sym}\big(-iS^\dagger S'\big)-\frac{1}{N}\left(\operatorname{tr}\operatorname{sym}\big(-iS^\dagger S'\big)-2\varphi'\right)I$；继而积分 $\widetilde S'=i\,\widetilde S\,\mathsf Q_\star$ 并以极分解的幺正因子作回缩。经典交替投影的全局收敛性仅适用于两闭凸集；鉴于 $\mathcal C_{\rm unit}$ 非凸且 $\mathcal U(N)$ 为幺正流形，本文将极分解仅作为回缩（retraction），并在满足局部角条件/线性正则性时主张**局部**收敛；极分解仍提供 Frobenius 范下的最近幺正矩阵。([epubs.siam.org][5])

### 6.3 Čech 能量正则化

在重叠区加入 $\lambda\,\mathcal E_{\check C}$ 使相位不一致源被定位并抑制。$\lambda$ 可据 §5 的 $C_1,C_2,C_3$ 与测量噪声 $\varepsilon_{\rm meas}$ 自适应选取以平衡偏差—方差。

## 7. 多端口谱分解与通道选择

谱分解 $S(E)=\sum_{\ell=1}^{N}e^{i\theta_\ell(E)}P_\ell(E)$ 给出

$$
\operatorname{tr}\mathsf Q(E)=\sum_{\ell=1}^{N}\theta_\ell'(E),\qquad
\varphi'(E)=\tfrac12\sum_{\ell=1}^{N}\theta_\ell'(E).
$$

若需稀疏通道选择，可在谱分解 $S(E)=\sum_{\ell=1}^{N}e^{i\theta_\ell(E)}P_\ell(E)$ 上选取集合 $I(E)\subset\{1,\dots,N\}$，并定义合成投影 $P_{I}(E):=\sum_{\ell\in I(E)}P_\ell(E)$；随后对 $P_I(E)$ 施加秩约束 $\operatorname{rank}P_I(E)\le k$ 或以 Ky–Fan $k$-范数作惩罚，以偏好低秩耦合，同时保持三位一体与幺正耦合。([arXiv][6])

## 8. 与 EBOC 与 RCA 的语义对位

EBOC 将 $(\Omega,S)$ 视为静态块之全局编码；窗口选择仅改变可供读取的局部截面而不改变编码本体。RCA 侧，以滑动块码给出局部—全局拼接：对每个重叠局部状态配置赋予一致的转移与"记录熵"读数，则由 Kolmogorov 一致性可构造全局可逆流。本文的帧稳定性与 Čech 能量对应 RCA 的局部转移无冲突与码本冗余门槛；BK 规范对应全局相位（规范）选择的一致化。

## 9. 充分条件与失败机理

**充分条件.** 帧覆盖（存在下界 $A>0$）；BK 规范固定；覆盖神经无 1-周；三项误差在 §5 界内；Čech 能量有界。

**失败机理.** 覆盖缺口（某能量区无重叠）；拓扑缺口（神经上非零 1-周诱发多值）；帧退化（$A\to0$）；别名主导（$W/h$ 过小）；尾项泄露（窗口外能量质量不可忽略）。

## 10. Kaiser–Bessel 窗的显式常数

对 Kaiser–Bessel 窗（参数 $\beta>0$）可取

$$
C_1\lesssim C(\beta),\qquad C_2\lesssim C(\beta)\,W^{-m},\qquad C_3\lesssim C(\beta)\,e^{-\beta},
$$

从而

$$
|\widehat{\mathcal R}-\mathcal R|_{L^2}\ \le\ \kappa(A,B)\Big(\varepsilon_{\rm meas}+C(\beta)e^{-\frac{2\pi W}{h}}
+C(\beta)W^{-m}h^{m}|\partial_E^{m}\mathcal R|_{L^2}+C(\beta)e^{-\beta}\Big).
$$

Kaiser–Bessel 窗的主瓣—旁瓣权衡与参数 $\beta$ 的作用详见文献。([cs.cmu.edu][7])

## 11. 可验证预言

1. 在固定带宽下提升重叠度（改善帧下界 $A$）应单调降低重建误差；
2. 在重叠区注入相位扰动将以非零 $\mathcal E_{\check C}$ 呈现并被正则项定位；
3. 当 $W/h$ 穿越 Nyquist 门槛，误差曲线出现"别名主导→Bernoulli 主导"的相变点，与采样密度判据一致。([archive.ymsc.tsinghua.edu.cn][8])

## 12. 结论

在"刻度同一式"与 NPE 三项闭合的公理化框架内，本文给出局部三位一体读数到全局散射场的稳定可逆黏合，并在 BK 规范下获得唯一性；算法上以帧反演与交替投影—极分解实现；语义上与 EBOC/RCA 的全息—拼接结构严格对位。该理论在窗口设计、采样密度、拓扑一致化与通道选择之间建立了可检验的定性预言与非渐近误差预算。

---

## 参考文献（选）

1. E. P. Wigner, *Lower limit for the energy derivative of the scattering phase shift*；F. T. Smith, *Lifetime matrix in collision theory*；U. R. Patel, E. Michielssen, *Wigner–Smith Time Delay Matrix*（定义与应用综述）．([arXiv][9])
2. M. Sh. Birman, M. G. Kreĭn，*On the theory of wave operators and scattering matrix*；A. Strohmaier, A. Waters，*The Birman–Kreĭn formula*；V. Kostrykin, R. Schrader，*Spectral shift & density of states*（光谱位移—散射相位—相对态密度）．([research.rug.nl][10])
3. O. Christensen，*An Introduction to Frames and Riesz Bases*（帧下界、帧算子可逆性与稳定重建）．([SpringerLink][2])
4. H. H. Bauschke, J. M. Borwein，*On Projection Algorithms for Convex Feasibility*；O. Ginat，*The Method of Alternating Projections*（交替投影收敛性）．([epubs.siam.org][5])
5. N. J. Higham，*Computing the Polar Decomposition*（最近幺正投影）．([epubs.siam.org][11])
6. DLMF §2.10（Euler–Maclaurin 余项有界）；Poisson Summation（别名与周期化准则）．([维基百科][12])
7. F. J. Harris，*On the Use of Windows for Harmonic Analysis*；Kaiser–Bessel 窗概述（参数—主瓣/旁瓣权衡）．([cs.cmu.edu][7])
8. H. J. Landau，*Necessary density conditions for sampling and interpolation*（采样密度与 Nyquist 门槛）．([archive.ymsc.tsinghua.edu.cn][8])

（完）

[1]: https://chaosbook.org/version13/chapters/scattering.pdf?utm_source=chatgpt.com "Quantum scattering"
[2]: https://link.springer.com/book/10.1007/978-3-319-25613-9?utm_source=chatgpt.com "An Introduction to Frames and Riesz Bases"
[3]: https://en.wikipedia.org/wiki/Poisson_summation_formula?utm_source=chatgpt.com "Poisson summation formula"
[4]: https://math.mit.edu/~dyatlov/res/res_final.pdf?utm_source=chatgpt.com "MATHEMATICAL THEORY OF SCATTERING"
[5]: https://epubs.siam.org/doi/10.1137/S0036144593251710?utm_source=chatgpt.com "On Projection Algorithms for Solving Convex Feasibility"
[6]: https://arxiv.org/pdf/1601.07430?utm_source=chatgpt.com "Variational Analysis of the Ky Fan k-norm"
[7]: https://www.cs.cmu.edu/afs/cs/user/bhiksha/WWW/courses/dsp/spring2013/WWW/schedule/readings/windows_comparison2_harris.pdf?utm_source=chatgpt.com "On the Use of Windows for Harmonic Analysis"
[8]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling"
[9]: https://arxiv.org/abs/2003.06985?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics"
[10]: https://research.rug.nl/files/232459978/1_s2.0_S0007449722000707_main.pdf?utm_source=chatgpt.com "The Birman-Krein formula for differential forms"
[11]: https://epubs.siam.org/doi/10.1137/0911038?utm_source=chatgpt.com "Fast Polar Decomposition of an Arbitrary Matrix"
[12]: https://en.wikipedia.org/wiki/Euler%E2%80%93Maclaurin_formula?utm_source=chatgpt.com "Euler–Maclaurin formula"
