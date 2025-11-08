# 自由意志的可逆化：可逆元胞自动机的局部可逆边界条件、KL/Bregman 选择算子与可逆账本

Version: 1.10

## 摘要

提出一种把"自由意志"严格实现为**可逆元胞自动机**（reversible cellular automaton, RCA）在有限区域上的**局部可逆边界条件**（reversible local boundary condition, RLBC）的方法学，并将"为何选此不选彼"的**信息保真度**刻画与**选择算子**置于同一可逆账本中。核心做法是：把每一步"抉择"设计为边界带上的**双射更新**，在必要时携带可逆的**证据/随机子寄存器**以保存打平与采样路径，使其与内部 RCA 的一步演化**级联为整体双射**；抉择本身由**最小-KL/I-投影**的**软选择**给出，并在**Γ-极限**下退化为**硬选择**（argmax），其全部信息开销在**Bennett 可逆嵌入**中被精确记账并可逆回收。可逆性与可判性由 CHL 表征定理、Garden-of-Eden 定理、分块/分区可逆元胞自动机结构与线性-边界矩阵判据保障；二维及以上一般邻域的不可判定性通过选取**块置换**或**线性可逆块**的可验证子类加以回避。本文同时将该边界-抉择范式与统一的**窗化读数—相位—相对态密度—群延迟**刻度相衔接，给出端到端的误差与稳定性声明。

---

## Notation & Axioms / Conventions

1. **RCA 与配置空间.** 字母表 $A$ 有限，$d\ge 1$，全空间 $X=A^{\mathbb Z^d}$。时间一步的全局更新 $F:X\to X$ 若在 Cantor 拓扑下连续且与平移等变，则且仅则它由有限视界的局部规则给出（Curtis–Hedlund–Lyndon, CHL）。若 $F$ 为双射，则称为 RCA；在 $\mathbb Z^d$ 全格上，Garden-of-Eden 定理给出 **满射 ⇔ 预单射（无孪生子） ⇔ 无孤儿（无前驱图样）**，并且 **单射 ⇒ 满射**；故双射当且仅当同时单射且满射。([SpringerLink][1])

2. **块/分区可逆与线性可逆.** 采用 Margolus 等分区：若**块内变换为置换**，则全局即可逆；反向演化由逆置换与逆序分区实现。线性元胞自动机在多种边界条件（含"中间边界"）下的可逆性可化为规则矩阵的可逆性与 Kronecker 分解判据。([维基百科][2])

3. **一般性不可判定与可验证子类.** 二维及以上一般邻域 CA 的可逆性问题**不可判定**（Kari）；因此本文聚焦于**分块置换**与**线性-边界矩阵**两类**可验证**子类。([ui.adsabs.harvard.edu][3])

4. **刻度同一（WSIG–EBOC 约定）.** 在窗化散射刻度上，采用同一式
$$
\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi i}\frac{\mathrm d}{\mathrm dE}\log\det S(E)=\frac{1}{2\pi}\operatorname{tr}Q(E)=\frac{1}{2\pi}\,\varphi'(E),
$$
其中 $Q(E)=-i\,S^{\dagger}(E)\,\partial_E S(E)$，$\det S(E)=e^{i\varphi(E)}$。Birman–Kreĭn 公式联系散射相位与谱移函数，作为能量/时间读数与"提交"的公共母刻度。([link.aps.org][4])

5. **信息几何与选择.** "最小-KL 在线性一致性约束下给出指数族/softmax、并满足 Pythagorean 身份与 Fenchel 双性"；"TV–KL"的 Pinsker 界用于温度-扰动-抖动的稳定估计。([pages.stern.nyu.edu][5])

6. **可逆账本.** 仅信息**抹除**耗散（Landauer 下界），**逻辑可逆**即可在极限上**任意低耗散**；随机采样与打平证据通过可逆寄存器记账（Bennett）。([dl.acm.org][6])

---

## 1. 模型：有限区域的局部可逆边界条件（RLBC）

令 $\Lambda\Subset\mathbb Z^d$ 为连通有限区域，取厚度足够的边界带 $\partial\Lambda$。内部一步演化由某个 RCA $F_\Lambda$ 给出。定义**边界层算子**
$$
\mathsf B:\ A^{\partial\Lambda}\times \mathcal E\ \longrightarrow\ A^{\partial\Lambda}\times \mathcal E,
$$
其中 $\mathcal E$ 是**可逆辅助寄存器**（证据/随机子/打平标签等）；本文默认 $\mathcal E$ 的字母表**有限**，并按边界触块局域化配置，以确保整体处于有限字母表 CA 框架（适用 CHL/GOE）。**一轮演化**定义为
$$
\mathcal U \coloneqq F_\Lambda\circ \mathsf B\quad\text{（先边界，后内部）}.
$$
称 $\mathsf B$ 为**局部可逆边界条件**（RLBC），若满足：

* **(R1) 局部性**：$\mathsf B$ 可**读** $\partial\Lambda$ 之外的有限外侧壳层（必要时将观测压入 $\mathcal E$），但**仅写** $\partial\Lambda$ 与 $\mathcal E$，且不触及 $\Lambda^\circ$；
* **(R2) 双射性**：$(b,\epsilon)\mapsto (b',\epsilon')$ 为置换；
* **(R3) 证据可追账**：一切用于抉择的随机子、打平索引、**所选动作索引 $a^\star$（或可重构 $a^\star$ 的最小充分证据）**与观测证据均写入 $\mathcal E$，以便反演恢复（Bennett 嵌入）。([dl.acm.org][6])

在分区实现中，令所有"触边块"各施以块内置换；由**块置换的并行直积=置换**，$\mathsf B$ 自动满足 (R2)。Margolus 分区的反向次序与逆置换给出 $\mathsf B^{-1}$。([维基百科][2])

---

## 2. 级联可逆性与可判性

**命题 2.1（有限域级联为双射）.** 设全局 $F$ 为 RCA，并取其在 $\Lambda$ 上的局部实现 $F_\Lambda$。若 $\mathsf B$ 为 RLBC，**且 $\mathsf B$ 与 $F_\Lambda$ 采用分区两相（如 Margolus）实现，使每一相位中的触边块两两不相交，并按"边界相位→内部相位"的两相日程同步执行**，则
$$
\mathcal U=F_\Lambda\circ\mathsf B
$$
是在状态 $(x|_\Lambda,b,\epsilon)$ 上的**有限域双射**，且 $\mathcal U^{-1}=\mathsf B^{-1}\circ F_\Lambda^{-1}$。将 $\Lambda$ 与 $\mathsf B$ 按上述**分区平铺与两相日程**同步作用于全格时，所得全局演化为 RCA。

*证明.* $\mathcal U$ 为双射，且 $\mathcal U^{-1}=\mathsf B^{-1}\circ F_\Lambda^{-1}$。若将 $\Lambda$ 与 $\mathsf B$ 按分区平铺并同步作用于全格，则由 CHL 可得对应全局映射连续且与平移等变，其逆同理。([SpringerLink][1])∎

**命题 2.2（边界-内部一体的可判性子类）.** 在下列两类实现中，$\mathcal U$ 的可逆性**可判**且可构造反演：

* **分块/分区 RCA**：当且仅当各块规则为置换。([维基百科][2])
* **线性-中间边界**：可逆性化为规则矩阵的可逆及其 Kronecker-分解；可给出多维与中间边界下的高效算法。([aimspress.com][7])

**注（一般性不可判定）.** 二维及以上一般邻域 CA 的可逆性不可判定（Kari），故本文之 RLBC 选取位于可验证子类。([ui.adsabs.harvard.edu][3])

---

## 3. 选择算子：KL/Bregman 保真（软→硬）

设边界可行动作集合 $\mathcal A(b)$。给定基准 $q(\cdot\mid b)$ 与矩约束，引入特征映射 $\phi:\mathcal A(b)\to\mathbb R^m$。

**假设（可行性）**：$b^\star \in \operatorname{conv}\{\phi(a):a\in\mathcal A(b)\}$。

**定义 3.1（软选择 / I-投影）.**
$$
p^\star(\cdot\mid b)\in\arg\min_{p\in\Delta(\mathcal A(b))}\Big\{D_{\mathrm{KL}}(p\|q):\ \sum_{a}p(a\mid b)\phi(a)=b^\star\Big\},
$$
其 KKT 条件给
$$
p^\star(a\mid b)\ \propto\ q(a\mid b)\exp\big(\langle \lambda,\phi(a)\rangle\big),
$$
即指数族/softmax；并满足信息几何的 Pythagorean 身份与 Fenchel-Legendre 对偶。([pages.stern.nyu.edu][5])

**命题 3.2（稳健性与 TV-KL 界）.** 当温度/正则参数改变引入的 KL 误差为 $\delta$ 时，总变差偏移受 Pinsker 界
$$
\|p_1-p_2\|_{\mathrm{TV}}\le \sqrt{\tfrac12 D_{\mathrm{KL}}(p_1\|p_2)}
$$
控制，可作为"温度—抖动"的上界；必要时可用 Bretagnolle–Huber 界改进。([维基百科][8])

**定理 3.3（Γ-极限：软→硬，经熵/KL 正则）.** 设 $q\in\Delta(\mathcal A)$、代价 $c:\mathcal A\to\mathbb R$。对 $\tau>0$，令
$$
p_\tau\in\arg\min_{p\in\Delta(\mathcal A)}\big\{\langle c,p\rangle+\tau D_{\mathrm{KL}}(p\|q)\big\}
$$
则 $p_\tau(a)\propto q(a)\exp(-c_a/\tau)$，且当 $\tau\downarrow 0$ 时 $p_\tau\Rightarrow \delta_{a^\star}$ 其中 $a^\star\in\arg\min_a c_a$；若极小点唯一则收敛唯一。**（带线性矩约束）** 若加入 $\sum_a p(a)\phi(a)=b^\star$，且**可行**（$b^\star\in\operatorname{conv}\phi(\mathcal A)$），则存在对偶变量 $\lambda(\tau)$ 使
$$
p_\tau(a)\propto q(a)\exp\Big(\tfrac{\langle \lambda(\tau),\phi(a)\rangle - c_a}{\tau}\Big).
$$
若可行集中**极小点唯一且为点质量**（存在 $a^\star\in\mathcal A$ 使 $\phi(a^\star)=b^\star$），则当 $\tau\downarrow 0$ 时 $p_\tau\Rightarrow \delta_{a^\star}$。([SpringerLink][9])

*证明略.* 当 $\tau\downarrow 0$ 时，熵/KL 项权重下降，线性目标支配；指数族表达式中的 $-c_a/\tau$ 指数差距放大，使概率质量集中到极小者；Γ-收敛与大偏差原理给出严格极限；矩约束情形通过拉格朗日乘子的尺度分析得到相同结论。唯一性与选择稳定性由 3.2 给出。∎

---

## 4. 可逆实现：Bennett 嵌入与"可逆采样"

**定理 4.1（可逆抉择器）.** 任意有限动作集上的软/硬选择，都存在一个把**随机子、打平证据与抽样路径**写入 $\mathcal E$ 的**可逆扩展**
$$
(b,\epsilon)\ \mapsto\ (b'=\operatorname{Sel}(b;\epsilon),\ \epsilon'),
$$
使该扩展在 $(b,\epsilon)$ 上为置换；反演由 $\epsilon'$ 恢复抽样树与打平秩序，并回擦证据，因而**无不可逆耗散**。

*证明.* 由 Bennett 逻辑可逆性：只要不抹除中间信息即可可逆回擦。将采样实现为**前缀-树/别名法**的受控置换：Knuth–Yao 的 DDG-tree 给出熵-最优的二进制抽样框架；Walker/Vose 别名法在常数均摊时间给出等价的离散采样结构。将树/表索引与抛硬币序列写入 $\mathcal E$ 即得。([dl.acm.org][6])∎

**实现备注（可验证算子族）.** 在 Margolus 分区的**触边块**上，以"选择结果 $\to$ 块内置换"的方式并行施加，即得 $\mathsf B$；其为置换的充分必要性与反演构造由块可逆性直接给出。([维基百科][2])

---

## 5. 形式化定义与主要定理

**定义 5.1（RLBC）.** 在一轮演化中，边界层更新
$$
\mathsf B(b,\epsilon)=\big(b',\epsilon'\big)
$$
满足 (R1)–(R3)，并且在分块实现下为**某一相位的不相交**边界触块置换的直积。

**定理 5.2（RLBC $\otimes$ 局部 RCA ⇒ 有限域双射）.** 若 $F_\Lambda$ 为 RCA、$\mathsf B$ 为 RLBC，则 $\mathcal U=F_\Lambda\circ\mathsf B$ 为有限域双射；$\mathcal U^{-1}=\mathsf B^{-1}\circ F_\Lambda^{-1}$。若对全格的每个平移副本**按分区两相日程**施加同构的 $\mathsf B$ 与对应的 $F_\Lambda$，且在任一相位中触边块**两两不相交**，则得到全局 RCA，逆由相反相位与逆置换回放得到。([SpringerLink][1])

**定理 5.3（选择 = I-投影；软→硬）.** 设 $\sum_a p(a)\phi(a)=b^\star$ 为矩约束，且**可行**（$b^\star\in\operatorname{conv}\phi(\mathcal A)$），则
(i) $p^\star=\arg\min D_{\mathrm{KL}}(p\|q)$ 唯一，且为指数族；
(ii) 对正则化族
$$
p_\tau\in\arg\min_{p\in\Delta(\mathcal A)}\Big\{\langle c,p\rangle+\tau D_{\mathrm{KL}}(p\|q)\ :\ \sum_a p(a)\phi(a)=b^\star\Big\},
$$
**存在**对偶变量 $\lambda(\tau)$；并且**若** $b^\star$ 位于 $\operatorname{conv}\phi(\mathcal A)$ 的**相对内点**（Slater 条件），则 $\{\lambda(\tau)\}$ **有界**（存在聚点）。在一般可行但非内点情形，$\lambda(\tau)$ 可能发散而下式仍成立：
$$
p_\tau(a)\propto q(a)\exp\Big(\tfrac{\langle \lambda(\tau),\phi(a)\rangle - c_a}{\tau}\Big).
$$
**若极小点唯一且为点质量**（存在 $a^\star$ 使 $\phi(a^\star)=b^\star$），则当 $\tau\downarrow 0$ 时 $p_\tau\Rightarrow \delta_{a^\star}$；
(iii) 抖动稳定性受 Pinsker/Bretagnolle–Huber 界控制。([pages.stern.nyu.edu][5])

**定理 5.4（可逆账本化）.** 令 $\operatorname{Sel}$ 为 5.3 的软/硬选择。存在一族边界块-置换 $\{\Pi_{\text{block}}^{(a)}\}_{a\in\mathcal A}$ 与可逆寄存器更新，使
$$
\mathsf B_\theta=\prod_{\text{触边块}}\Pi_{\text{block}}\big(a^\star_\theta\big)
$$
构成 RLBC，并且采样/打平的全部信息被写入 $\mathcal E$ 并在 $\mathsf B_\theta^{-1}$ 中回擦，无 Landauer 成本。([dl.acm.org][6])

**定理 5.5（线性-边界的可逆判据）.** 在线性 CA 与"中间边界"设置下，$\mathcal U$ 的可逆性等价于相应规则矩阵的可逆性；矩阵可经 Kronecker-分解降维判定。([aimspress.com][7])

---

## 6. 与窗化读数—相位—态密度—群延迟刻度的衔接

将边界的"证据汇总/一致性约束"来源于一类窗化谱读数：在绝对连续谱区，以同一刻度
$$
\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi i}\frac{\mathrm d}{\mathrm dE}\log\det S(E)=\frac{1}{2\pi}\operatorname{tr}Q(E)=\frac{1}{2\pi}\,\varphi'(E),
$$
其中 $Q=-i\,S^{\dagger}\,\partial_E S$，$\det S(E)=e^{i\varphi(E)}$，把"读数"表述为相位导数/相对态密度/群延迟迹的积分泛函；Birman–Kreĭn 公式给出谱移与散射相位的等价，从而可把"提交/抉择"的一致性约束 $\sum_a p(a)\phi(a)=b^\star$ 明确地绑定到能量-相位账本。边界-选择的**软→硬**转变对"读数抖动"的灵敏度由 Pinsker-型不等式与线性化响应估计控制。([link.aps.org][4])

---

## 7. 范式构造：Margolus-边界的可逆抉择器

在二维 Margolus 分区上，设外圈全为"触边块"。对每个触边块，给定有限动作集 $\mathcal A\subset \mathfrak S(A^{2\times 2})$（块内置换族）与特征映射 $\phi:\mathcal A\times \partial\Lambda\to\mathbb R^m$。根据 §3 的 I-投影，对温度 $\tau>0$ 定义软选择分布
$$
p^\star_{\tau,\theta}(a\mid b)\ \propto\ q_\theta(a\mid b)\exp\big(\langle \lambda_\theta,\phi(a,b)\rangle/\tau\big),
$$
其硬极限为
$$
a^\star_\theta(b)\in\arg\max_{a\in\mathcal A}\ \langle \lambda_\theta,\phi(a,b)\rangle .
$$
定义
$$
\mathsf B_\theta=\prod_{\text{触边块}}\Pi_{\text{block}}\big(a^\star_\theta(b)\big),
$$
并配合可逆寄存器更新
$$
(b,\epsilon)\ \mapsto\ \Big(b'=\Pi_{\text{block}}\big(a^\star_\theta(b)\big)(b),\ \epsilon'=\epsilon\oplus\operatorname{code}\big(a^\star_\theta(b)\big)\Big),
$$
其中 $\operatorname{code}(\cdot)$ 为动作索引的可逆编码。soft 情形用可逆采样从 $p^\star_{\tau,\theta}(\cdot\mid b)$ 抽取 $a$，将抽样路径与 $\operatorname{code}(a)$ 一并写入 $\mathcal E$ 以保证回放；hard 情形先根据 $b$ 计算 $a^\star_\theta(b)$，写入 $\operatorname{code}\big(a^\star_\theta(b)\big)$ 后再施置换。逆过程中读取编码，施 $\Pi_{\text{block}}(a^\star)^{-1}$ 并回擦编码，从而 $\mathsf B_\theta$ 在 $(b,\epsilon)$ 上为置换。与内部分块 RCA 级联后，$\mathcal U$ 保持可逆；$\epsilon$ 记账保证反演可恢复全部随机/证据路径。([维基百科][2])

---

## 8. 端到端可验证清单（实验-无涉的理论化）

1. **可逆性核查**：分块-置换或线性-边界矩阵法；二维一般邻域的不可判定区不进入实现口径。([维基百科][2])
2. **选择-保真**：求解 I-投影（或其凸对偶），软/硬在温度参数调控下互达；抖动-误差用 Pinsker/Bretagnolle–Huber 界。([pages.stern.nyu.edu][5])
3. **可逆账本**：Knuth–Yao/DDG-tree 或别名法的可逆化；随机子与索引写入 $\mathcal E$；反演回擦。([semanticscholar.org][10])
4. **刻度绑定**：以 $\rho_{\mathrm{rel}}=\tfrac{1}{2\pi}\,\varphi'=\tfrac1{2\pi}\mathrm{tr}\,Q$ 与 Birman–Kreĭn 公式将"读数→约束"嵌入统一能量/相位账本。([link.aps.org][4])

---

## 附录 A：Garden-of-Eden 与 RLBC 的一致性

在欧氏格上，Garden-of-Eden 定理给**局部预单射⇔全局满射**。RLBC 的块置换实现使边界层在其作用域内**局部单射**，内部 RCA 又是全局双射；二者级联保持单射与满射，于是整体仍为 RCA。该论证依 CHL 的连续-等变闭性与 GOE 的 **满射-预单射等价**（并且 **单射⇒满射**）。([维基百科][11])

---

## 附录 B：Γ-极限下的软→硬选择

设可行集为单纯形 $\Delta(\mathcal A)$、代价 $c:\mathcal A\to\mathbb R$、基准分布 $q\in\Delta(\mathcal A)$。定义泛函
$$
\Phi_\tau(p)=\langle c,p\rangle+\tau D_{\mathrm{KL}}(p\|q).
$$
则 $p_\tau\in\operatorname{argmin}\Phi_\tau$ 给出 $p_\tau(a)\propto q(a)\exp(-c_a/\tau)$。当 $\tau\downarrow 0$ 时，KL 项权重趋零，$\Phi_\tau$ **Γ-收敛**到线性泛函 $\Phi_0(p)=\langle c,p\rangle$，其在单纯形顶点（点质量）上极小。若再假设等紧性与极小点 $a^\star\in\arg\min_a c_a$ 唯一，**则极小化器序列** $p_\tau$ **在弱拓扑下收敛**到点质量：$p_\tau \Rightarrow \delta_{a^\star}$。大偏差原理保证指数尺度 $1/\tau$ 下的概率质量集中速率。**矩约束情形（假设可行）**：加入 $\sum_a p(a)\phi(a)=b^\star$（假设 $b^\star\in\operatorname{conv}\phi(\mathcal A)$）后，**存在**对偶变量 $\lambda(\tau)$；**若** $b^\star$ 为相对内点（Slater 条件），$\{\lambda(\tau)\}$ **有界**（存在聚点），否则其范数可能发散而硬极限仍等价于受限线性规划。指数族解为
$$
p_\tau(a)\propto q(a)\exp\Big(\tfrac{\langle \lambda(\tau),\phi(a)\rangle - c_a}{\tau}\Big).
$$
当 $\tau\downarrow 0$ 时，极限问题等价于 $\min\{\langle c,p\rangle:\sum_a p(a)\phi(a)=b^\star\}$；若极小点 $a^\star$ 唯一且为点质量，则 $p_\tau\Rightarrow\delta_{a^\star}$。([SpringerLink][9])

---

## 附录 C：可逆采样器的构造提要

* **DDG-tree（Knuth–Yao）**：以随机比特为源的最优离散抽样；把访问路径（左右分支）与叶编号写入 $\mathcal E$ 即得可逆实现。([semanticscholar.org][10])
* **Alias（Walker/Vose）**：预处理两表后常数时间采样；把表索引与阈值比较结果写入 $\mathcal E$，并在反演中回放。([维基百科][12])
* 两者均与 Bennett 的"保存-回擦"策略相容，因而无不可逆热下界。([dl.acm.org][6])

---

## 参考文献（选）

* Hedlund, **Endomorphisms and Automorphisms of the Shift Dynamical System**（CHL 表征）. ([SpringerLink][1])
* Ceccherini-Silberstein & Coornaert, **Garden of Eden theorem: old and new**；以及 Garden-of-Eden 综述条目. ([arXiv][13])
* Kari, **Reversibility of 2D cellular automata is undecidable**；相关综述. ([ui.adsabs.harvard.edu][3])
* Toffoli & Margolus, **Invertible cellular automata / Margolus 邻域与分区技术**. ([people.csail.mit.edu][14])
* Chang et al., **Reversibility of linear cellular automata with intermediate boundary condition**（矩阵-Kronecker 判据）. ([aimspress.com][7])
* Bennett, **Logical reversibility of computation**（可逆账本与 Landauer）. ([dl.acm.org][6])
* Csiszár, **I-divergence geometry & I-projection**；Cover–Thomas；Wainwright–Jordan（指数族与凸对偶）. ([pages.stern.nyu.edu][5])
* Pinsker 不等式及改进（Bretagnolle–Huber）. ([维基百科][8])
* Knuth–Yao（DDG-tree）；Walker/Vose（Alias）. ([semanticscholar.org][10])
* Wigner（相位导数/时间延迟）；Smith（$\mathsf Q=-i\,S^{\dagger}\,\partial_E S$）；Birman–Kreĭn 公式（谱移-散射）。([link.aps.org][15])

---

[1]: https://link.springer.com/article/10.1007/BF01691062?utm_source=chatgpt.com "Endomorphisms and automorphisms of the shift dynamical ..."
[2]: https://en.wikipedia.org/wiki/Reversible_cellular_automaton?utm_source=chatgpt.com "Reversible cellular automaton"
[3]: https://ui.adsabs.harvard.edu/abs/1990PhyD...45..379K/abstract?utm_source=chatgpt.com "Reversibility of 2D cellular automata is undecidable"
[4]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[5]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[6]: https://dl.acm.org/doi/10.1147/rd.176.0525?utm_source=chatgpt.com "Logical reversibility of computation | IBM Journal of ..."
[7]: https://www.aimspress.com/article/doi/10.3934/math.2024371?viewType=HTML&utm_source=chatgpt.com "Reversibility of linear cellular automata with intermediate ..."
[8]: https://en.wikipedia.org/wiki/Pinsker%27s_inequality?utm_source=chatgpt.com "Pinsker's inequality"
[9]: https://link.springer.com/book/10.1007/978-1-4612-0327-8?utm_source=chatgpt.com "An Introduction to Γ-Convergence"
[10]: https://www.semanticscholar.org/paper/The-complexity-of-nonuniform-random-number-Knuth-Yao/58f10efb7c76b41a6ddc26ff9ff94f7faa1e2e35?utm_source=chatgpt.com "The complexity of nonuniform random number generation"
[11]: https://en.wikipedia.org/wiki/Curtis%E2%80%93Hedlund%E2%80%93Lyndon_theorem?utm_source=chatgpt.com "Curtis–Hedlund–Lyndon theorem"
[12]: https://en.wikipedia.org/wiki/Alias_method?utm_source=chatgpt.com "Alias method"
[13]: https://arxiv.org/abs/1707.08898?utm_source=chatgpt.com "The Garden of Eden theorem: old and new"
[14]: https://people.csail.mit.edu/nhm/ica.pdf?utm_source=chatgpt.com "ICA - People | MIT CSAIL"
[15]: https://link.aps.org/doi/10.1103/PhysRev.98.145?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase ..."
