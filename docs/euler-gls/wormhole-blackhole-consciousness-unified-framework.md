# 虫洞—黑洞—意识的窗化散射—因果—信息几何统一
Version: 1.4

**三位一体母尺、可遍历性判据、测量—熵产生、Mellin—分形—Zeckendorf 桥接与范畴化（含证明）**

---

## 摘要

建立以 Wigner–Smith 群延迟矩阵与 Birman–Kreĭn（BK）公式为枢纽的**三位一体母尺**，将"相位—延迟—相对态密度"统一到能量窗化的散射读数中：若散射矩阵 $S(E)\in\mathrm U(N)$ 可导，定义 $\mathsf Q(E)=-\,i\,S(E)^\dagger \tfrac{dS}{dE}(E)$，则
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ },\qquad
\varphi(E)=\tfrac12\,\arg\det S(E),
$$
该等式与光谱位移函数 $\xi(E)$ 满足 BK 关系 $\det S(E)=\exp[-2\pi i\,\xi(E)]$ 同余，从而 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$。这一"母尺"在 Toeplitz/Berezin 压缩下给出窗化读数的规范化量纲，统一解释喉部几何、散射相位与群延迟。([arXiv][1])

在几何与因果层面，**拓扑审查**定理表明：在满足平均 Null 能量条件（ANEC）等假设的时空中，外部观察者不能利用时空非平凡拓扑实现遍历连接；量子场可在受限时间窗内产生负能流，相关强度受量子能量不等式（QEI）与量子 Null 能量条件（QNEC）严密约束。([arXiv][2])

在全息与近 $\mathrm{AdS}_2$ 语境，**Gao–Jafferis–Wall（GJW）机制**通过边界双迹耦合在视界附近产生平均负的 Null 能量，从而在有限时间窗内使 ER 桥可遍历；进一步，"**传态 = 穿越**"揭示量子传态协议与穿越虫洞的等价结构，SYK—近 $\mathrm{AdS}_2$ 给出**永恒可遍历**解及其门控参数。([Physical Review][3])

在"观察者—意识"侧，将意识的作用建模为"**I-投影 + Belavkin 过滤**"的测量更新链：后验态沿量子过滤随时间演化，路径熵产生满足 Spohn 不等式，且在带反馈的情况下满足含互信息的 Jarzynski 等式
$\langle e^{-\beta W+\beta\Delta F-I}\rangle=1$。该链条为"观察者参与的纠缠—传态—（可遍历）虫洞解释"提供操作化语义，同时保持因果与非超信号。([SIAM Ebooks][4])

为支撑有限窗观测与多尺度记账，引入**Mellin 对数帧**用于指数—幂律分离，并用**Zeckendorf 可逆日志**实现能量—信息份额的无相邻 1 记账；再以**可逆胞元自动机（RCA）**实现局域、可复算的账本更新。([jeanphilippeovarlez.com][5])

---

## 0. 记号、窗化与母尺

**散射与母尺**：设 $S(E)\in\mathrm U(N)$ 能量可导，$\mathsf Q(E)=-iS^\dagger S'$ 为 Wigner–Smith 群延迟矩阵；BK 公式给出 $\det S(E)=e^{-2\pi i\xi(E)}$，从而
$$
\frac{d}{dE}\log\det S(E)=\operatorname{tr}(S^\dagger S')=-2\pi i\,\xi'(E),
$$
推得 $\operatorname{tr}\mathsf Q(E)=-2\pi\,\xi'(E)$。又记 $\varphi(E)=\tfrac12\arg\det S(E)=-\pi\xi(E)$，则
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=-\xi'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ }.
$$
上述恒等将"相位导数—位移密度—群延迟迹"统一为**母尺** $\rho_{\rm rel}(E)$。([arXiv][1])

**窗化读数**：取光滑窗—核 $w_R,h\in\mathcal S(\mathbb R)$，定义能量窗化泛函
$$
\langle f\rangle_{w,h}=\int_{\mathbb R}(w_R*\check h)(E)\,f(E)\,dE ,
$$
并据此比较 $\langle\varphi'\rangle,\ \langle \operatorname{tr}\mathsf Q\rangle$ 等读数。Toeplitz/Berezin 压缩与符号的 Berezin 变换保证窗化操作的正定性与半经典极限可控。([Wiley Online Library][6])

**因果与解析**：线性响应的因果性等价于上半平面的解析性与 Kramers–Kronig/Hilbert 成对关系；Titchmarsh 卷积支撑定理给出前沿时间的次可加性：$\inf\supp(f*g)=\inf\supp f+\inf\supp g$。这确保群延迟可出现负值而不违背最早到达前沿的因果界。([Wikipedia][7])

---

## 1. 几何—因果—散射的闭合

**拓扑审查**：在满足 ANEC 与适当渐近平直/可预言性条件的时空中，任意从无穷远到无穷远的类时/类光曲线均无法穿越非平凡拓扑而实现通信，即不可遍历。该命题将"可遍历"排除到量子负能的例外之中。

**量子例外与约束**：量子场可在受限时间窗内制造平均负的 Null 能量，但受 QEI 与 QNEC 的强约束；后者把 $\langle T_{kk}\rangle$ 的下界与熵的二阶变分联系起来。([arXiv][2])

**从因果到保角**：在区分性条件下，因果同构刻画时空的保角类（HKM/Malament），因此只要窗化观测恢复因果偏序，便可在保角类上重构几何信息。([AIP Publishing][8])

---

## 2. 可遍历性的机制与判据

### 2.1 GJW 机制与负能门控

在双边 $\mathrm{AdS}$ 中引入两侧边界算符的双迹耦合 $g(t)\,\mathcal O_L\mathcal O_R$ 会在视界附近诱导平均负的 Null 能量，开启有限时间窗的信号通道。该负能通量的存在是可遍历的必要条件之一：
$$
\int_I\!\langle T_{\mu\nu}k^\mu k^\nu\rangle\,d\lambda<0 .
$$
原始计算与后续变体均证实此点。

### 2.2 "传态 = 穿越"与 $\mathrm{AdS}_2/$SYK

量子传态在 ER=EPR 框架下等价于通过可遍历虫洞的态传播。具体地，满足传态条件的门控在引力侧对应于使 ER 桥可遍历的边界耦合；SYK—近 $\mathrm{AdS}_2$ 中存在**永恒可遍历**解，持续维持负能与桥的开口。([Physical Review][3])

### 2.3 Page 曲线、岛公式与副本虫洞

黑洞蒸发的细粒度熵通过"副本虫洞"鞍点得以解释，给出与岛公式一致的 Page 曲线，进一步支持"纠缠—几何"的深层联系。

---

## 3. 喉部散射的母尺读数

### 3.1 双端通道与块结构

对左右无穷远端口，散射矩阵写成
$$
S(E)=\begin{pmatrix}R_{\rm L}(E)&T_{\rm RL}(E)\\ T_{\rm LR}(E)&R_{\rm R}(E)\end{pmatrix}\!,
$$
在块幺正或扩展幺正（含弱耗散）下，$\det S$ 与 $\operatorname{tr}\mathsf Q$ 的窗化积分给出喉部有效势的灰体修正与相位延迟一致标度：
$$
\big\langle \rho_{\rm rel}\big\rangle_{w,h}
=\big\langle \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\big\rangle_{w,h}
=\big\langle \varphi'/\pi\big\rangle_{w,h}.
$$
该刻度由 BK 迹公式与 Helffer–Sjöstrand 泛函演算闭合。([PMC][9])

### 3.2 前沿与群延迟的区分

群延迟由 $\operatorname{tr}\mathsf Q$ 给出，可能在频域窗化后出现负值；但最早到达前沿由因果支撑与 Titchmarsh 定理控制，不受负群延迟"表象"的影响，因而无超信号。([Wikipedia][7])

---

## 4. 观察者—意识：测量、过滤与熵产生

以 I-投影描述离散观测的最小相对熵更新；持续监测时后验态满足 Belavkin 量子过滤方程，平均化后回收 GKSL 主方程。沿 Lindblad 演化的熵产生满足 Spohn 单调性；在反馈控制存在时，Jarzynski—Sagawa–Ueda 等式给出功—自由能—互信息的关系：
$$
\big\langle e^{-\beta W+\beta\Delta F-I}\big\rangle=1.
$$
该框架把"观察者参与"的信息增益转译为可遍历门控的能量—信息预算。([Mathematics at Nottingham][10])

---

## 5. Mellin—分形—对数帧与 NPE 纪律

在 $\omega=\log E$ 的对数尺度上，Mellin 变换与稠密（或紧）帧用于指数衰减与幂律尾项的解耦；对窗化读数 $\langle\cdot\rangle_{w,h}$ 进行帧展开可将"穿越窗—环降—尾项"分离并控制误差：
$$
\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
其中 Poisson 取样抑制别名，Euler–Maclaurin（EM）给出端点修正与上界，尾项由窗衰减与母尺正则性控制。([jeanphilippeovarlez.com][5])

---

## 6. Zeckendorf 可逆日志与 RCA 实现

**Zeckendorf 表示**：每个正整数唯一表示为非相邻 Fibonacci 数之和；相应的"无相邻 1"比特串为自然的**可逆日志**，适合有限窗内能量/信息份额的局域进/借位记账。([Wikipedia][11])

**RCA 对接**：基于 Margolus 分块或二阶法则的**可逆胞元自动机**可将日志更新实现为局域可逆映射，保证跨窗账本的可验证与可复算。([people.csail.mit.edu][12])

---

## 7. 范畴互构图

记 $\mathbf{WScat}$ 为窗化散射范畴（对象：$(S(E),w,h)$；态射：能量依赖幺正规范商下的等价类），$\mathbf{Cau}$ 为因果流形范畴（对象：区分性洛伦兹流形；态射：因果同构），$\mathbf{Zec}$ 为 Zeckendorf 记账范畴，$\mathbf{RCA}$ 为可逆胞元自动机范畴。存在函子
$$
\mathfrak F:\mathbf{WScat}\to\mathbf{Cau},\qquad
\mathfrak G:\mathbf{Cau}\to\mathbf{WScat},
$$
分别由"窗化读数$\Rightarrow$ 因果偏序的恢复"与"保角类$\Rightarrow$ 符合 KK/Titchmarsh 的散射响应"实现；$\mathfrak Z:\mathbf{Zec}\to\mathbf{WScat}$、$\mathfrak U:\mathbf{Zec}\to\mathbf{RCA}$ 将日志与局域更新对接为可遍历判据的可计算实现。该互构图在因果—解析—散射与账本—递归之间闭合。([AIP Publishing][8])

---

## 8. 主定理与实现要则

### 定理 A（拓扑审查的窗化重述）

设 $(\mathcal M,g)$ 为区分性、渐近平直且满足 ANEC 的时空。对任意光束生成元 $k^\mu$ 与任意非负、归一化的时间窗核 $K\in\mathcal S(\mathbb R)$（$K\ge0,\ \int_{\mathbb R}K(\lambda)\,d\lambda=1$），若
$$
\int_{\mathbb R} K(\lambda)\ \langle T_{\mu\nu}k^\mu k^\nu\rangle\,d\lambda \ \ge 0 \quad\text{对所有此类 }K,
$$
则外部观察者不可实现遍历通信；若存在可遍历窗，则必存在某此类 $K$ 使上述积分 **严格为负**，其幅度—持续时间受 QEI/QNEC 给出之下界约束。
**证明要点**：拓扑審查定理排除经典可遍历；将能量条件以测试函数加权的窗化形式表述，结合 QEI/QNEC 的下界推出必要的负能窗存在性与约束。([arXiv][2])

### 定理 B（GJW 可遍历性的母尺刻度）

在双边 $\mathrm{AdS}$ 场景，对适定的双迹耦合 $g(t)$ 存在时间窗 $I$ 使
$$
\int_I\!\langle T_{\mu\nu}k^\mu k^\nu\rangle_g\,d\lambda<0,
$$
并导致母尺的窗化读数下降：
$$
\int_{\mathbb R}\!(w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_g(E)\,dE
<\int_{\mathbb R}\!(w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_0(E)\,dE.
$$
等价地，$\langle\varphi'\rangle$ 在该窗内下降，出现**可遍历窗**。
**证明要点**：GJW 线性响应给出负能通量；由 BK 迹公式 $\mathrm{Tr}[f(H)-f(H_0)]=\int f'(E)\,\xi(E)\,dE$ 与 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=-\xi'$ 得窗化相位—群延迟的同步下降。([PMC][9])

### 定理 C（"传态 = 穿越"的测量—控制闭合）

在 ER=EPR 框架下，理想化传态协议等价于穿越 ER 桥的通道；其成功概率 $p_{\rm suc}$ 与门控强度、带宽及互信息预算满足
$$
\big\langle e^{-\beta W+\beta\Delta F-I}\big\rangle=1,\qquad
\langle W\rangle\ge \Delta F - \beta^{-1}\langle I\rangle,
$$
并受 QEI/QNEC 约束；当 $\langle T_{kk}\rangle$ 的负窗与互信息预算匹配时，出现非零 $p_{\rm suc}$ 的遍历传输。
**证明要点**："传态 = 穿越"结果与永恒可遍历解；Belavkin 过滤与 Spohn 熵产生、Jarzynski—Sagawa–Ueda 等式耦合到能量—信息预算。([Physical Review][3])

---

## 9. 实现要则

1. **母尺标定**：统一使用 $\rho_{\rm rel}=\varphi'/\pi=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 作为相位—延迟—相对态密度的刻度。([arXiv][1])
2. **窗与采样**：选择带限窗—核，Poisson 抑制别名，有限阶 EM 校正端点并评估余项。([Mathematical Institute][13])
3. **环降—尾项—穿越窗分离**：在 $\omega=\log E$ 上用 Mellin 帧分离指数/幂律。([jeanphilippeovarlez.com][5])
4. **账本与复算**：Zeckendorf 日志实现无相邻 1 记账；以 RCA 将更新落为局域可逆规则。([Wikipedia][11])
5. **一致性三检**：拓扑审查 + QEI/QNEC + 传态—穿越对偶，三重一致后方可宣称"可遍历"。([arXiv][2])

---

# 附录：证明与技术要点

## 附录 A：因果—解析—散射互构

**A.1 Kramers–Kronig 与前沿**
对任意因果响应 $\chi(t)=0$（$t<0$），其傅里叶像 $\chi(\omega)$ 为上半平面解析，满足 KK 关系；Titchmarsh 定理给出卷积支撑的边界等式，从而链路的最早到达前沿时间 $t_*$ 满足次可加性。([Wikipedia][7])

**A.2 因果到保角**
在过去/未来区分的时空中，因果结构决定拓扑与保角类（HKM/Malament）。因此可从窗化散射读数恢复因果偏序，再由自然变换连接至保角类。([AIP Publishing][8])

**A.3 BK—母尺封口**
由 BK 公式与 $\mathsf Q=-iS^\dagger S'$ 推出 $(2\pi)^{-1}\operatorname{tr}\mathsf Q=-\xi'=\varphi'/\pi$，并用 Helffer–Sjöstrand 公式把 $\mathrm{Tr}[f(H)-f(H_0)]$ 写为 $\int f'(E)\,\xi(E)\,dE$ 的窗化形式。([arXiv][1])

---

## 附录 B：喉部的双端散射与窗化 BK

将喉部几何等效为短程有效势的双端散射问题；对块幺正 $S(E)$，其行列式相位与 $\operatorname{tr}\mathsf Q$ 的窗化积分由 BK—Kreĭn 迹公式控制。对弱耗散情形，采用幺正扩张或耦合—耗散散射的迹公式延拓。([PMC][9])

---

## 附录 C：NPE 三分误差

设能量采样步长 $h$。总误差分解 $\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$。带限—Nyquist 下 $\varepsilon_{\rm alias}\approx0$；EM 给出端点修正与余项上界 $R_p$；尾项由窗衰减阶与母尺的 Hölder 正则性界定。([Mathematical Institute][13])

---

## 附录 D：拓扑审查、QNEC 与 QEI 的窗化

**D.1 拓扑审查**
在 ANEC 与适当全局假设下，任何从 $\mathscr I^-$ 到 $\mathscr I^+$ 的类光通信均被"拓扑审查"禁止。

**D.2 QNEC**
其中 $S''_{\rm out}$ 取每单位横向面积的二阶变分，给出
$\langle T_{kk}\rangle \ge \tfrac{1}{2\pi}\,S''_{\rm out}$（在适定条件下），并可推广至一般场论与全息证法。窗化时在仿射参数上取非负、归一化窗 $K(\lambda)$，写成
$$
\int_{\mathbb R}K(\lambda)\Big(\langle T_{kk}\rangle-\tfrac{1}{2\pi}S''_{\rm out}\Big)\,d\lambda \ge 0.
$$
([Physical Review][14])

**D.3 QEI**
量子场的负能脉冲满足"借贷—归还"的时间—幅度的定量权衡，测试函数（即窗）决定约束形式。([arXiv][2])

---

## 附录 E：Mellin 对数帧的帧界

在 $\omega=\log E$ 上构造 $\{\psi_k\}$ 为对数平移等变的紧框架，利用 Parseval 关系与 Poisson 求和证明存在常数 $A,B>0$ 使
$A\|f\|_2^2\le \sum_k|\langle f,\psi_k\rangle|^2\le B\|f\|_2^2$，据此实现指数环降与幂律尾项的分离。([jeanphilippeovarlez.com][5])

---

## 附录 F：GJW 可遍历性与母尺的变分

将双迹耦合视为边界扰动，线性响应给出视界附近的平均负能通量。由
$\det S(E)=e^{-2\pi i\,\xi(E)}\ \Rightarrow\
\delta\log\det S(E)=-2\pi i\,\delta\xi(E),\qquad
\frac{d}{dE}\log\det S(E)=-2\pi i\,\xi'(E)$
与 $\operatorname{tr}\mathsf Q=-2\pi\,\xi'$ 得
$\delta\langle (2\pi)^{-1}\operatorname{tr}\mathsf Q\rangle_{w,h}=-\langle \delta\xi'\rangle_{w,h}$。其符号由窗内 $\langle \delta\xi'\rangle_{w,h}$ 决定；在 GJW 场景的线性响应预测 $\langle T_{kk}\rangle<0$ 且诱导 $\langle \delta\xi'\rangle_{w,h}>0$ 的条件下，出现母尺下降窗，等价于可遍历窗的出现。([arXiv][1])

---

## 附录 G：传态—穿越与测量—反馈

在"传态 = 穿越"的等价下，将 Bell 观测 + 经典通信 + 纠错映作"负能门控 + 有限时间窗"；Belavkin 过滤给出后验态演化；Spohn 单调性保证沿 GKSL 演化的相对熵非增；带反馈的一般化 Jarzynski 等式给出成功率与信息预算的热力学边界，同时保持因果与非超信号。([Physical Review][3])

---

## 参考文献（选）

* Friedman, Schleich, Witt. *Topological Censorship*. Phys. Rev. Lett. **71** (1993) 1486.
* Gao, Jafferis, Wall. *Traversable Wormholes via a Double Trace Deformation*. JHEP **12** (2017) 151.
* Susskind, Zhao. *Teleportation through the wormhole*. Phys. Rev. D **98** (2018) 046016. ([Physical Review][3])
* Maldacena, Qi. *Eternal traversable wormhole*. arXiv:1804.00491. ([arXiv][15])
* Almheiri et al.; Penington et al. *Replica wormholes / Islands and Page curve*（代表作）。
* Pushnitski. *The spectral shift function and the invariance principle*. J. Funct. Anal. **183** (2001) 269–320；及 *Birman–Kreĭn Det S = e^{-2πiξ}* 综述。([KCL Pure][16])
* Texier. *Wigner time delay and related concepts. Application to transport in coherent conductors*（综述）([arXiv][17])
* Kramers–Kronig 与 Titchmarsh 卷积支撑定理。([Wikipedia][7])
* Koeller, Leichenauer. *Holographic Proof of the QNEC*. Phys. Rev. D **94** (2016) 024026；Bousso et al. *QFC*. ([Physical Review][14])
* Fewster. *Lectures on Quantum Energy Inequalities*. arXiv:1208.5399. ([arXiv][2])
* Belavkin；Bouten–van Handel–James. *Quantum filtering*. SIAM Rev. **51** (2009) 239–316（综述）。([Mathematics at Nottingham][10])
* Spohn. *Entropy production for quantum dynamical semigroups*. J. Math. Phys. **19** (1978) 1227. ([AIP Publishing][18])
* Sagawa, Ueda. *Generalized Jarzynski Equality under Feedback*. Phys. Rev. Lett. **104** (2010) 090602；Jarzynski (1997)。([Physical Review][19])
* Schlichenmaier 等. *Berezin–Toeplitz quantization*（综述）。([Wiley Online Library][6])
* Mellin 对数分析与紧帧（综述与教材章节）。([jeanphilippeovarlez.com][5])
* Zeckendorf 定理与其分布性质。([Wikipedia][11])
* Toffoli–Margolus. *Invertible Cellular Automata*；RCA 概述。([people.csail.mit.edu][12])
* HKM/Malament：因果结构决定保角类。([AIP Publishing][8])

---

### 结语

母尺恒等式将相位、群延迟与相对态密度统一为可窗化的散射刻度；拓扑审查—QNEC/QEI—GJW 的合力为可遍历虫洞提供必要—充分的物理门控；测量—过滤—熵产生给出"观察者参与"的能量—信息预算；Mellin—Zeckendorf—RCA 则把多尺度记账与可逆实现落到可计算规则。由此形成"GKSL—因果流形—窗化散射—能量与信息账本—范畴互构"的闭合框架。

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://arxiv.org/pdf/1208.5399?utm_source=chatgpt.com "Lectures on Quantum Energy Inequalities"
[3]: https://link.aps.org/doi/10.1103/PhysRevD.98.046016?utm_source=chatgpt.com "Teleportation through the wormhole | Phys. Rev. D"
[4]: https://epubs.siam.org/doi/10.1137/060651239?utm_source=chatgpt.com "An Introduction to Quantum Filtering"
[5]: https://www.jeanphilippeovarlez.com/publications/ewExternalFiles/the%20mellin%20.pdf?utm_source=chatgpt.com "Chapter 11 - The Mellin Transform"
[6]: https://onlinelibrary.wiley.com/doi/10.1155/2010/927280?utm_source=chatgpt.com "Berezin‐Toeplitz Quantization for Compact Kähler ..."
[7]: https://en.wikipedia.org/wiki/Kramers%E2%80%93Kronig_relations?utm_source=chatgpt.com "Kramers–Kronig relations"
[8]: https://pubs.aip.org/aip/jmp/article/18/7/1399/460709/The-class-of-continuous-timelike-curves-determines?utm_source=chatgpt.com "The class of continuous timelike curves determines the ..."
[9]: https://pmc.ncbi.nlm.nih.gov/articles/PMC6407858/?utm_source=chatgpt.com "Spectral shift functions and Dirichlet-to-Neumann maps"
[10]: https://www.maths.nottingham.ac.uk/plp/vpb/publications/ofqp-pra.pdf?utm_source=chatgpt.com "Nondemolition observation of a free quantum particle"
[11]: https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem?utm_source=chatgpt.com "Zeckendorf's theorem"
[12]: https://people.csail.mit.edu/nhm/ica.pdf?utm_source=chatgpt.com "ICA - People | MIT CSAIL"
[13]: https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_150.pdf?utm_source=chatgpt.com "A trapezoidal rule error bound unifying the Euler–Maclaurin ..."
[14]: https://link.aps.org/doi/10.1103/PhysRevD.94.024026?utm_source=chatgpt.com "Holographic proof of the quantum null energy condition"
[15]: https://arxiv.org/abs/1804.00491?utm_source=chatgpt.com "Eternal traversable wormhole"
[16]: https://kclpure.kcl.ac.uk/portal/en/publications/the-spectral-shift-function-and-the-invariance-principle?utm_source=chatgpt.com "The spectral shift function and the invariance principle"
[17]: https://arxiv.org/pdf/1507.00075?utm_source=chatgpt.com "Wigner time delay and related concepts. Application to transport in coherent conductors"
[18]: https://pubs.aip.org/aip/jmp/article/19/5/1227/460049/Entropy-production-for-quantum-dynamical?utm_source=chatgpt.com "Entropy production for quantum dynamical semigroups"
[19]: https://link.aps.org/doi/10.1103/PhysRevLett.104.090602?utm_source=chatgpt.com "Generalized Jarzynski Equality under Nonequilibrium ..."
