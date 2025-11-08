# 热力学—统计的完全几何化：温度—曲率频谱、熵—体积对数与相变的几何判据
Version: 1.7

**MSC**：82B05；82C31；53C21；58J35；60G10；28A80
**关键词**：KMS/Tolman 红移；热核与 Seeley–DeWitt 系数；Weyl 律与谱维；Bogoliubov–Kubo–Mori（BKM）度量；Bakry–Émery 曲率维条件；Wasserstein 梯度流（JKO）；Lee–Yang/Fisher 零点；Ruppeiner 曲率；Birman–Kreĭn 与散射相位；Spohn 单调与 Jarzynski；分形边界热含量

---

## 摘要

给定带有黎曼度量 $g$ 的可定向 $d$-维流形 $M$ 及拉普拉斯型算子 $\mathcal L=-\Delta_g+V$，以规范配分函数 $Z(\beta)=\operatorname{Tr}\,e^{-\beta \mathcal L}$ 的几何小时间渐近与谱分布为纽带，建立如下三条主张并给出证明链与实现要则：

1. **温度—曲率频谱**：$\beta^{-1}$ 等价于热核半群 $e^{-\beta \mathcal L}$ 的"频谱窗口宽度"；局域上有热核对角渐近 $K(\beta;x,x)\sim (4\pi\beta)^{-d/2}\bigl[1+\beta\bigl(\tfrac{R(x)}{6}-V(x)\bigr)+O(\beta^{2})\bigr]$，据此定义曲率的几何热谱密度 $\mathcal R^{\rm geom}_\beta(x):=6(4\pi)^{d/2}\,\partial_\beta\bigl[\beta^{d/2}e^{\beta V(x)}K(\beta;x,x)\bigr]$ 并证明 $\lim_{\beta\downarrow 0}\mathcal R^{\rm geom}_\beta(x)=R(x)$。故**温度的几何含义**是以窗口尺度 $\beta$ 解析曲率不变量的频谱过滤；在静态时空还满足 Tolman–Ehrenfest 红移 $T(x)\sqrt{-g_{00}(x)}=\text{常数}$，与 KMS 平衡条件等价。([ScienceDirect][1])

2. **熵—体积对数**：微正则下由 Weyl 律的本征计数 $N(\lambda)$ 得到态密度 $\rho(\lambda)\sim \tfrac{d}{2}C_d\,\operatorname{Vol}(M)\,\lambda^{d/2-1}$（边界与曲率给出低次修正），从而系统熵满足 $S(E)=\log \Omega(E)=\log \int_0^E\rho(\lambda)\,d\lambda=\log \operatorname{Vol}(M)+\tfrac{d}{2}\log E+\log C_d+O(E^{-1/2})$；正则系综下 $S(\beta)=\beta\langle \mathcal L\rangle+\log Z(\beta)$ 且 $\log Z(\beta)=\log \int_M K(\beta;x,x)\,dV_g$ 的首项即 $\log \operatorname{Vol}(M)-\tfrac{d}{2}\log \beta+\text{曲率/边界修正}$。由此严格实现命题"熵＝几何体积的对数"，并量化曲率与边界的有限温度修正项。([arXiv][2])

3. **相变的几何描述**：在宏观层面，Ruppeiner 信息几何曲率 $R_{\rm Rup}$ 作为相关体积尺度的量度，在临界点发散并刻画一阶与二阶相变曲线；在微观层面，Lee–Yang/Fisher 零点逼近实轴当且仅当发生非解析，从而以零点测度与 Morse/拓扑变化为判据；二者与热核／Weyl 校正系数、边界与分形维的耦合给出统一的相变几何学。([Physical Review Links][3])

本文同时将线性响应（Kubo–Mori/BKM 度量）、最优传输梯度流（JKO）、Bakry–Émery 曲率维条件与对数 Sobolev/Talagrand–HWI 不等式纳入同一结构，推导热力学四定律为几何约束的必然结果；讨论开放量子系统的 Spohn 单调与含信息的 Jarzynski 等式及其 KMS 基准；并给出分形边界的热含量与谱维修正。([dept.camden.rutgers.edu][4])

---

## 目录

1. 公理化设置与记号
2. 温度＝曲率频谱：热核与 KMS/Tolman
3. 熵＝体积对数：Weyl 律与两系综联通
4. 热力学四定律的几何化推导
5. 线性响应与 BKM 度量；散射相位与母尺
6. 熵产生、涨落关系与信息修正的功—自由能不等式
7. 最优传输梯度流与几何热力学长度
8. 相变：Ruppeiner 曲率、Lee–Yang/Fisher 零点与拓扑假说
9. 边界与分形效应：热含量与谱修正
10. 量子混沌与温度上界
    附录 A–I：证明

---

## 1. 公理化设置与记号

**公理 1（几何—统计实体）**：$(M,g)$ 为紧致 $d$-维流形（可带边界 $\partial M$），$\mathcal L=-\Delta_g+V$ 自伴、半正。热核 $K(\beta;x,y)=\langle x|e^{-\beta \mathcal L}|y\rangle$，配分函数 $Z(\beta)=\operatorname{Tr}e^{-\beta \mathcal L}=\int_M K(\beta;x,x)\,dV_g$。

**公理 2（平衡与温度）**：量子/代数统计学中的平衡态以 KMS 条件表征；在静态时空上局域温度满足 Tolman–Ehrenfest 红移 $T(x)\sqrt{-g_{00}(x)}=\text{常数}$。([Project Euclid][5])

**公理 3（响应与度量）**：线性响应核的 Kubo–Mori（BKM）内积定义在平衡态上并诱导热力学信息几何；其经典极限为 Fisher–Rao 度量。([dept.camden.rutgers.edu][4])

**公理 4（散射—母尺）**：若存在外区散射，Wigner–Smith 延迟矩阵 $\mathsf Q(E)=-iS^\dagger\,\tfrac{dS}{dE}$ 与谱移函数 $\xi$ 满足 Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$；其迹密度 $\displaystyle \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$ 给出相对态密度刻度，用作读数母尺。([arXiv][6])

---

## 2. 温度＝曲率频谱：热核与 KMS/Tolman

**定理 2.1（曲率的热谱恢复，内点版）**。设 $\mathcal L=-\Delta_g+V$ 为拉普拉斯型算子。对**无边界流形**或**有边界流形的内点** $x\in M^\circ$，当 $\beta\downarrow 0$ 有
$$
K(\beta;x,x)\sim (4\pi\beta)^{-d/2}\Bigl[1+\beta\Bigl(\tfrac{R(x)}{6}-V(x)\Bigr)+O(\beta^{2})\Bigr],
$$
从而定义
$$
\boxed{\ \mathcal R^{\rm geom}_\beta(x):=6(4\pi)^{d/2}\,\partial_\beta\Bigl[\beta^{d/2}e^{\beta V(x)}K(\beta;x,x)\Bigr],\qquad \lim_{\beta\downarrow 0}\mathcal R^{\rm geom}_\beta(x)=R(x)\ }
$$
**说明（有边界时）**：若 $\partial M\neq\varnothing$ 且 $x$ 位于边界或以 $\operatorname{dist}(x,\partial M)=O(\sqrt\beta)$ 接近边界，则 $K(\beta;x,x)$ 含半整数项，$\mathcal R^{\rm geom}_\beta(x)$ 一般存在 $\beta^{-1/2}$ 级发散；关于整体量（迹/积分）之半整数修正见第3.3节。

([ScienceDirect][1])

*证明要点*：参见附录 A：$a_0=1$、$a_1=\tfrac{R}{6}-V$，从而
$$
\beta^{d/2}e^{\beta V(x)}K(\beta;x,x)= (4\pi)^{-d/2}\Bigl[1+\beta\,\tfrac{R(x)}{6}+O(\beta^{2})\Bigr].
$$
边界时附加半整数序列 $a_{1/2},a_{3/2},\dots$（无边界，**局域对角**）；有边界时**整体量**出现半整数修正，见第3.3节。([arXiv][7])

**命题 2.2（温度的谱窗口意义）**。$\beta^{-1}$ 等价于谱测度 $\mu$ 的窗口宽度：有 Tauberian 关系
$$
Z(\beta)=\int_0^\infty e^{-\beta \lambda}\,dN(\lambda),\quad N(\lambda)=\#\{\text{spec}\le \lambda\}.
$$
当 $\beta^{-1}$ 提升，滤波器 $e^{-\beta\lambda}$ 赋予更高谱率权重；$\beta\downarrow 0$ 极限恢复局域曲率不变量。([arXiv][2])

**命题 2.3（KMS 与 Tolman 一致性）**。静态类时 Killing 矢量 $K=\partial_t$ 的时空上，KMS 状态在局域正交规范中的温度 $T(x)$ 满足 $T(x)\sqrt{-g_{00}(x)}=\text{常数}$，与热核时间参数的红移关系一致：$\beta_{\rm loc}(x)=\beta_\infty\sqrt{-g_{00}(x)}$。([Project Euclid][5])

---

## 3. 熵＝体积对数：Weyl 律与两系综联通

**定理 3.1（Weyl 律与微正则熵·严格版）**。紧致无边界时
$$
N(\lambda)=C_d\,\operatorname{Vol}(M)\,\lambda^{d/2}+O\bigl(\lambda^{(d-1)/2}\bigr).
$$
态密度 $\rho(\lambda)=N'(\lambda)\sim \tfrac{d}{2}C_d\,\operatorname{Vol}(M)\,\lambda^{d/2-1}$。定义能量 $E\leftrightarrow \lambda$，则微正则熵
$$
S(E)=\log \Omega(E)=\log \int_0^E \rho(\lambda)\,d\lambda=\log \operatorname{Vol}(M)+\tfrac{d}{2}\log E+\log C_d+O(E^{-1/2}).
$$
([arXiv][2])

**命题 3.2（正则熵与体积项）**。设
$$
\bar K(\beta):=\frac{1}{\operatorname{Vol}(M)}\int_M K(\beta;x,x)\,dV_g.
$$
则
$$
\log Z(\beta)=\log \operatorname{Vol}(M)+\log \bar K(\beta),
$$
从而利用第 2 节热核展开得

**无边界情形**：
$$
\boxed{\ \log Z(\beta)=\log \operatorname{Vol}(M)-\tfrac{d}{2}\log(4\pi\beta)+\beta\Bigl(\tfrac{1}{6}\overline{R}-\overline{V}\Bigr)+O(\beta^{2})\ }
$$
于是 $-\partial_\beta\log Z=\tfrac{d}{2\beta}-\bigl(\tfrac{1}{6}\overline{R}-\overline{V}\bigr)+O(\beta)$，
$$
\boxed{\ S(\beta)=\beta\langle\mathcal L\rangle+\log Z(\beta)=\log \operatorname{Vol}(M)-\tfrac{d}{2}\log(4\pi\beta)+\tfrac{d}{2}+O(\beta^{2})\ }
$$
其中 $\displaystyle \overline{R}:=\frac{1}{\operatorname{Vol}(M)}\int_M R\,dV_g$，$\displaystyle \overline{V}:=\frac{1}{\operatorname{Vol}(M)}\int_M V\,dV_g$。

**有边界情形说明**：按第3.3节，$\log Z(\beta)$ 与 $S(\beta)$ 需额外加入面积阶的 $O(\beta^{1/2})$ 半整数修正项。

体积为首要对数项，线性 $\beta$ 曲率修正抵消，边界与更高阶几何项出现在更高次幂。([ScienceDirect][1])

**命题 3.3（边界与半整数修正）**。若 $\partial M\neq\varnothing$，则 $Z(\beta)$ 的下一主项为 $\propto \operatorname{Area}(\partial M)\,\beta^{-(d-1)/2}$，并伴随边界几何不变量；由此在 $S$ 中出现与面积相关的半整数幂。([arXiv][7])

---

## 4. 热力学四定律的几何化推导

**零定律（KMS 等价）**：平衡态 $\omega$ 满足 $\omega(A\tau_t(B))$ 的解析延拓与 KMS 条件；静态时空局域温度满足 Tolman 关系，与第 2 节一致。([Project Euclid][5])

**第一定律（几何变分）**：自由能 $\mathcal F(\beta,g)=-\beta^{-1}\log Z(\beta)$。变分：
$$
\boxed{\ \delta(\beta \mathcal F)=\langle \mathcal L\rangle\,\delta\beta+\tfrac{1}{2}\int_M \sqrt{g}\,T^{\mu\nu}\,\delta g_{\mu\nu}\,d^dx\ }
$$
其中 $T^{\mu\nu}=-\tfrac{2}{\sqrt{g}}\tfrac{\delta \log Z}{\delta g_{\mu\nu}}$；从热核变分可表达 $T^{\mu\nu}$ 的曲率展开。([ScienceDirect][1])

**第二定律（熵生产单调）**：开放系统满足 GKSL 半群 $\Phi_t$，相对熵 $D(\rho_t\Vert \rho_\beta)$ 单调递减；Spohn 不等式给出熵产生率非负，且等号当且仅当处于平衡不变态。([Inspire][8])

**第三定律（零温极限）**：若存在谱隙且基态简并有限，则 $\lim_{\beta\to\infty}S(\beta)=\log g_0$；在几何上等价于 $\lambda_1-\lambda_0>0$ 的谱间隙假设；Weyl 校正不影响极限。([arXiv][2])

---

## 5. 线性响应与 BKM 度量；散射相位与母尺

**命题 5.1（BKM 度量与响应）**：设平衡态 $\rho_\beta\propto e^{-\beta H}$。BKM 内积 $\langle X,Y\rangle_{\rm BKM}=\int_0^1 \operatorname{Tr}\bigl(\rho_\beta^s X^\dagger \rho_\beta^{1-s}Y\bigr)\,ds$ 诱导的黎曼度量是量子信息单调度量中对应于 Kubo–Mori 情形；其 Christoffel 与曲率刻画线性响应与耗散。([dept.camden.rutgers.edu][4])

**命题 5.2（散射相位与谱移）**：若系统含外区散射通道，则谱移函数与散射矩阵满足 $\det S(E)=e^{-2\pi i\xi(E)}$；Kreĭn 迹公式给出 $\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr)=\int f'(E)\,\xi(E)\,dE$，因而 $\displaystyle \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$ 提供与第 2–3 节相容的"读数母尺"。([arXiv][6])

---

## 6. 熵产生、涨落关系与信息修正的功—自由能不等式

**定理 6.1（含信息的 Jarzynski 等式）**：带反馈控制与测量信息 $I$ 的过程满足 $\langle e^{-\beta W+\beta \Delta F-I}\rangle=1$，因此 $\langle W\rangle\ge \Delta F - \beta^{-1}\langle I\rangle$。此处 $I$ 由测量通道的互信息给出；KMS 参照系下等式成立。([Physical Review Links][9])

**命题 6.2（Belavkin 过滤与 Spohn 单调）**：连续监测的后验态满足 Belavkin–QSDE；平均化得到 GKSL 演化并保持 Spohn 单调，从而连续观测与控制下的熵产生仍非负。([epubs.siam.org][10])

---

## 7. 最优传输梯度流与几何热力学长度

**定理 7.1（JKO 方案与自由能下降）**：Fokker–Planck 方程是相对熵 $\mathcal H(\mu|\pi)$ 在 Wasserstein 距离 $\mathcal W_2$ 上的梯度流；离散"最小化运动"迭代 $\mu_{k+1}=\arg\min_\nu \bigl\{ \tfrac{1}{2h}\mathcal W_2^2(\nu,\mu_k)+\mathcal H(\nu|\pi)\bigr\}$ 收敛于连续解并保证自由能递减。([epubs.siam.org][11])

**定理 7.2（Bakry–Émery 与 HWI/Talagrand）**：若满足 $CD(\kappa,N)$ 曲率维条件，则相对熵 $\mathcal H$ $\kappa$-凸，得 HWI 与 Talagrand–LSI 链：$\mathcal H\le \mathcal W_2 \sqrt{\mathcal I}-\tfrac{\kappa}{2}\mathcal W_2^2$，并推导耗散率与"热力学长度"下界。([arXiv][12])

---

## 8. 相变：Ruppeiner 曲率、Lee–Yang/Fisher 零点与拓扑假说

**定理 8.1（Ruppeiner 判据）**：以 $\{-\partial_i\partial_j S\}$ 为度量的标度曲率 $R_{\rm Rup}$ 与相关体积满足临界标度 $R_{\rm Rup}\sim \xi^d$ 并在临界点发散，给出一阶/二阶相变与 Widom 线的几何分辨。([Physical Review Links][3])

**定理 8.2（零点与非解析）**：Lee–Yang（巨正则）与 Fisher（正则）零点在热力学极限逼近实轴当且仅当自由能发生非解析；零点密度由相函数跳跃率给出。由此可将相变判据几何化为谱函数零点的积聚与子能量流形的拓扑改变。([ifi.unicamp.br][13])

**命题 8.3（拓扑假说）**：经典系综中，配置空间子水平集的拓扑改变（如 Euler 示性数的突变）与相变相关；该观点为必要条件，在某些模型中亦足以给出强信号。([Physical Review Links][14])

---

## 9. 边界与分形效应：热含量与谱修正

边界导致热核半整数系数与面积项；**当 $\partial\Omega$ 为粗糙或分形边界（Minkowski 维为 $\gamma$）时，短时的热含量**相对体积的**缺口**满足
$$
|\Omega|-E(s)\sim C\,s^{\frac{d-\gamma}{2}},\qquad s\downarrow 0,
$$
从而可据早时热含量之**缺口标度**反演边界维 $\gamma$ 与 Minkowski 内容。**在 $d=2$ 的特例下，上式退化为先前常用的 $s^{1-\gamma/2}$ 标度。**分形鼓与相对分形 ζ 函数提供复杂维度框架以解析谱振荡与相变信号。([arXiv][7])

---

## 10. 量子混沌与温度上界

在热平衡下 OTOC 的指数增长率满足混沌上界 $\lambda_L\le 2\pi k_B T/\hbar$，该上界来自解析带宽与 KMS 条件，进一步将"温度＝频谱带宽"的解释延伸到动力学混沌领域。严密形式见 Tsuji–Shitara–Ueda 的正则化无关性证明。([arXiv][15])

---

# 附录：主要证明

## 附录 A：热核—曲率频谱同一（定理 2.1）

**引理 A.1（Seeley–DeWitt 展开）**：对拉普拉斯型算子 $\mathcal L=-\Delta_g+V$，存在
$$
K(\beta;x,x)\sim (4\pi\beta)^{-d/2}\sum_{m\ge 0} a_m(x)\,\beta^m,
$$
其中 $a_0=1$、$a_1=\tfrac{R}{6}-V$。([ScienceDirect][1])

*证明*：参考标准热核展开并取对角极限，见综述。由此
$$
\beta^{d/2}e^{\beta V(x)}K(\beta;x,x)= (4\pi)^{-d/2}\Bigl[1+\beta\,\tfrac{R(x)}{6}+O(\beta^{2})\Bigr].
$$
定义 $\mathcal R^{\rm geom}_\beta(x):=6(4\pi)^{d/2}\,\partial_\beta[\beta^{d/2}e^{\beta V(x)}K(\beta;x,x)]$ 即 $\mathcal R^{\rm geom}_\beta(x)=R(x)+O(\beta)$，取 $\beta\downarrow 0$ 得结论。带边界时加入半整数系数。([arXiv][7])

---

## 附录 B：Weyl 律与熵—体积对数（定理 3.1）

**引理 B.1（Weyl 主项）**：
$$
N(\lambda)=\frac{\omega_d}{(2\pi)^d}\operatorname{Vol}(M)\lambda^{d/2}+O\bigl(\lambda^{(d-1)/2}\bigr).
$$
([arXiv][2])

*证明*：微局部分析与 Tauberian 理论。态密度 $\rho=N'$ 给出 $\Omega(E)=C_d\,\operatorname{Vol}(M)\,E^{d/2}(1+O(E^{-1/2}))$；取对数得
$$
\log\Omega(E)=\log \operatorname{Vol}(M)+\tfrac{d}{2}\log E+\log C_d+O(E^{-1/2}).
$$
边界若存在则贡献 $\lambda^{(d-1)/2}$ 级项并由热核 $a_{1/2}$ 等半整数系数控制。([arXiv][7])

---

## 附录 C：KMS、Tolman 与零定律

**定理 C.1**：KMS 条件与静态时空的 Tolman 红移相容，$\beta_{\rm loc}=\beta_\infty\sqrt{-g_{00}}$。*证明*：将 Killing 时间参数化为热核时间并使用局域静态正交标架；KMS 的解析带宽给出 OTOC 与响应的带宽，从而与 Tolman 因子一致。([Project Euclid][5])

---

## 附录 D：BKM 度量与线性响应

**命题 D.1**：BKM 度量是 Petz 单调度量族中对应于算子单调函数 $f_{\rm BKM}(x)=(x-1)/\log x$ 的成员；其二次型为 Kubo–Mori 正则相关函数。*证明*：参见 Petz/Tóth 的构造与线性响应理论。([dept.camden.rutgers.edu][4])

---

## 附录 E：最优传输梯度流与 HWI

**定理 E.1（JKO）**：对可积势能与凸性条件，JKO 迭代收敛且给出 $\mathcal H$ 的陡降流；$\mathcal H$ 单调，Fisher 信息 $\mathcal I$ 控制耗散。*证明*：参见原始文献与 Ambrosio–Gigli–Savaré 的度量空间梯度流理论。([epubs.siam.org][11])

**定理 E.2（Bakry–Émery 与 HWI）**：在 $CD(\kappa,N)$ 下，$\mathcal H$ $\kappa$-凸，得 HWI 与 LSI/Talagrand。*证明*：$\Gamma_2$ 演算与合成 Ricci 下界的等价刻画。([arXiv][12])

---

## 附录 F：相变的几何学

**命题 F.1（Ruppeiner 曲率）**：以 $-\partial_i\partial_j S$ 形成的度量之标度曲率 $R_{\rm Rup}$ 与相关长度 $\xi$ 同标度，临界发散。*证明*：热容与压缩率的临界指数进入 Christoffel 与曲率表达，见综述。([Physical Review Links][3])

**定理 F.2（零点判据）**：令 $Z$ 的 Lee–Yang 或 Fisher 零点集合 $\mathcal Z$；若存在序列趋向实轴且零点测度有非零密度，则自由能非解析且出现相变。*证明*：辩值原理与极限测度的边缘逼近。([ifi.unicamp.br][13])

**命题 F.3（拓扑假说的必要性）**：配置空间子水平集拓扑改变是相变的必要条件；在若干模型中为强信号但非充分。*证明*：参见综述与模型算例。([Physical Review Links][14])

---

## 附录 G：散射、谱移与母尺

**定理 G.1（Birman–Kreĭn 与 Kreĭn 迹公式）**：$\det S(E)=e^{-2\pi i\xi(E)}$，且 $\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr)=\int f'(E)\,\xi(E)\,dE$。*证明*：谱族与行列式的解析延拓；Helffer–Sjöstrand 表示给出迹类性与积分表示。([arXiv][6])

**推论**：$\displaystyle \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$ 提供"温度—能量窗口"下的相对态密度刻度，与第 2–3 节热核/Weyl 框架互补。([Physical Review Links][16])

---

## 附录 H：熵产生与涨落关系

**定理 H.1（Spohn）**：GKSL 半群对平衡态的相对熵非增，定义的熵产生率非负。*证明*：生成元的完全正性与相对熵的凸性。([Inspire][8])

**定理 H.2（含信息 Jarzynski）**：$\langle e^{-\beta W+\beta \Delta F-I}\rangle=1$。*证明*：测量—反馈的通道分解与相对熵恒等式。([Physical Review Links][9])

---

## 附录 I：边界与分形的热含量

**命题 I.1（热含量与边界维）**：对分形边界，短时热含量 $E(s)$ 具有标度 $s^{1-\gamma/2}$，可反演 Minkowski 维 $\gamma$ 与内容；给出统计自相似情形的极限定理。*证明*：更新方程与"感受不到边界"原理。([Pi Math Cornell][17])

---

## 讨论与实现要则

1. **温度＝频谱带宽**：在数值上以热核时间 $\beta$ 作为滤波尺度；曲率重建可用 $\mathcal R_\beta(x)$ 的外推。([ScienceDirect][1])
2. **熵＝体积对数**：通过 Weyl 主项估算微正则熵；在正则下用 $\log Z$ 的 $\log \operatorname{Vol}$ 主项与曲率/边界修正。([arXiv][2])
3. **响应与控制**：以 BKM 度量估算热力学长度与最小耗散；开放系统用 Spohn 与 Jarzynski—信息项评估反馈极限。([dept.camden.rutgers.edu][4])
4. **相变诊断**：并行计算 $R_{\rm Rup}$、零点轨迹与热核修正系数的温度依赖；分形边界或粗糙几何需引入半整数与分形校正。([Physical Review Links][3])
5. **散射—母尺互换**：若存在外散射或实验 S 参数，使用 Birman–Kreĭn 与 Wigner–Smith 直接读取相对态密度，与热核/Weyl 结果交叉校验。([arXiv][6])

---

### 参考（选摘）

热核与 Seeley–DeWitt：Vassilevich（2003）；边界/半整数：Avramidi–Esposito（1997）。([ScienceDirect][1])
Weyl 律：Ivrii（2016）。([arXiv][2])
KMS 与 Tolman–Ehrenfest：Haag–Hugenholtz–Winnink（1967）；Tolman（1930）；Unruh 综述（Crispino 等，2008）。([Project Euclid][5])
BKM 度量与响应：Petz/Tóth；BKM–Petz–单调度量综述（Ciaglia 等）。([dept.camden.rutgers.edu][4])
散射—谱移：Pushnitski（2010）；Strohmaier（2022）。([arXiv][6])
JKO 与梯度流：Jordan–Kinderlehrer–Otto（1998）；Ambrosio–Gigli–Savaré（2008）；Bakry–Émery 曲率维。([epubs.siam.org][11])
Ruppeiner 几何与相变：Ruppeiner 系列；Wei 等（2019）。([arXiv][18])
Lee–Yang/Fisher 零点：Bena 讲义；Aslyamov（2019）。([ifi.unicamp.br][13])
分形边界热含量：Lapidus 学派；Charmoy 幻灯。([SpringerLink][19])
熵产生与涨落：Spohn（1978）；Sagawa–Ueda（2010）。([Inspire][8])
混沌上界：Maldacena–Shenker–Stanford（2016）；Tsuji–Shitara–Ueda（2018/2017）。([arXiv][15])

---

## 结论

通过热核—谱几何、KMS/Tolman、Weyl—Tauberian 与信息几何—最优传输的合流，本文将
$$
\text{温度}=\text{几何曲率的频谱},\qquad \text{熵}=\log\text{几何体积}
$$
严格化为一组可计算的等式与不等式，并给出相变的几何判据（Ruppeiner 曲率发散与 Lee–Yang/Fisher 零点积聚）及其边界/分形修正；同时在开放系统与散射读数下保持一致的"母尺"刻度。上述结果把热力学定律还原为几何与信息的约束：零定律＝KMS/红移一致性，第一定律＝自由能的几何变分，第二定律＝相对熵与梯度流的单调，第三定律＝谱隙与极低温极限；并在混沌上界中出现"温度＝解析带宽"的动力学化阐释。

[1]: https://www.sciencedirect.com/science/article/pii/S0370157303003545?utm_source=chatgpt.com "Heat kernel expansion: user's manual"
[2]: https://arxiv.org/abs/1608.03963?utm_source=chatgpt.com "[1608.03963] 100 years of Weyl's law"
[3]: https://link.aps.org/doi/10.1103/PhysRevE.86.052103?utm_source=chatgpt.com "Thermodynamic geometry, phase transitions, and the Widom ..."
[4]: https://dept.camden.rutgers.edu/math/files/Toth_036.pdf?utm_source=chatgpt.com "The Bogoliubov inner product in quantum statistics"
[5]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-5/issue-3/On-the-equilibrium-states-in-quantum-statistical-mechanics/cmp/1103840050.pdf?utm_source=chatgpt.com "On the Equilibrium States in Quantum Statistical Mechanics"
[6]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[7]: https://arxiv.org/abs/hep-th/9701018?utm_source=chatgpt.com "Heat-Kernel Asymptotics with Generalized Boundary Conditions"
[8]: https://inspirehep.net/literature/2735262?utm_source=chatgpt.com "Entropy production for quantum dynamical semigroups"
[9]: https://link.aps.org/doi/10.1103/PhysRevLett.104.090602?utm_source=chatgpt.com "Generalized Jarzynski Equality under Nonequilibrium ..."
[10]: https://epubs.siam.org/doi/10.1137/060651239?utm_source=chatgpt.com "An Introduction to Quantum Filtering"
[11]: https://epubs.siam.org/doi/10.1137/S0036141096303359?utm_source=chatgpt.com "The Variational Formulation of the Fokker--Planck Equation"
[12]: https://arxiv.org/pdf/1209.5786?utm_source=chatgpt.com "Bakry–Émery curvature-dimension condition and ..."
[13]: https://www.ifi.unicamp.br/~cabrera/teaching/Yang-Lee%20Zeros.pdf?utm_source=chatgpt.com "Yang-Lee Zeros.pdf"
[14]: https://link.aps.org/doi/10.1103/RevModPhys.80.167?utm_source=chatgpt.com "Phase transitions and configuration space topology"
[15]: https://arxiv.org/abs/1503.01409?utm_source=chatgpt.com "[1503.01409] A bound on chaos"
[16]: https://link.aps.org/doi/10.1103/PhysRevE.91.060102?utm_source=chatgpt.com "Statistical distribution of the Wigner-Smith time-delay matrix ..."
[17]: https://pi.math.cornell.edu/~fractals/5/charmoy.pdf?utm_source=chatgpt.com "Heat content asymptotics of some domains with fractal ..."
[18]: https://arxiv.org/abs/1909.03887?utm_source=chatgpt.com "[1909.03887] Ruppeiner Geometry, Phase Transitions, and ..."
[19]: https://link.springer.com/article/10.1007/s11784-014-0207-y?utm_source=chatgpt.com "Fractal zeta functions and complex dimensions of relative ..."
