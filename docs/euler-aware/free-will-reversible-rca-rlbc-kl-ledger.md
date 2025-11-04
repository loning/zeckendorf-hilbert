# 自由意志的可逆化：可逆元胞自动机的局部可逆边界条件、KL/Bregman 选择算子与可逆账本

## 摘要

提出一种把"自由意志"严格实现为**可逆元胞自动机**（reversible cellular automaton, RCA）在有限区域上的**局部可逆边界条件**（reversible local boundary condition, RLBC）的方法学，并将"为何选此不选彼"的**信息保真度**刻画与**选择算子**置于同一可逆账本中。核心做法是：把每一步"抉择"设计为边界带上的**双射更新**，在必要时携带可逆的**证据/随机子寄存器**以保存打平与采样路径，使其与内部 RCA 的一步演化**级联为整体双射**；抉择本身由**最小-KL/I-投影**的**软选择**给出，并在**Γ-极限**下退化为**硬选择**（argmax），其全部信息开销在**Bennett 可逆嵌入**中被精确记账并可逆回收。可逆性与可判性由 CHL 表征定理、Garden-of-Eden 定理、分块/分区可逆元胞自动机结构与线性-边界矩阵判据保障；二维及以上一般邻域的不可判定性通过选取**块置换**或**线性可逆块**的可验证子类加以回避。本文同时将该边界-抉择范式与统一的**窗化读数—相位—相对态密度—群延迟**刻度相衔接，给出端到端的误差与稳定性声明。

---

## Notation & Axioms / Conventions

1. **RCA 与配置空间.** 字母表 $A$ 有限，$d\ge 1$，全空间 $X=A^{\mathbb Z^d}$。时间一步的全局更新 $F:X\to X$ 若在 Cantor 拓扑下连续且与平移等变，则且仅则它由有限视界的局部规则给出（Curtis–Hedlund–Lyndon, CHL）。若 $F$ 为双射，则称为 RCA；在欧氏格上，**单射 ⇔ 满射**与**无前驱 ⇔ 有孤儿/孪生子图样**由 Garden-of-Eden 定理刻画。([SpringerLink][1])

2. **块/分区可逆与线性可逆.** 采用 Margolus 等分区：若**块内变换为置换**，则全局即可逆；反向演化由逆置换与逆序分区实现。线性元胞自动机在多种边界条件（含"中间边界"）下的可逆性可化为规则矩阵的可逆性与 Kronecker 分解判据。([维基百科][2])

3. **一般性不可判定与可验证子类.** 二维及以上一般邻域 CA 的可逆性问题**不可判定**（Kari）；因此本文聚焦于**分块置换**与**线性-边界矩阵**两类**可验证**子类。([ui.adsabs.harvard.edu][3])

4. **刻度同一（WSIG–EBOC 约定）.** 在窗化散射刻度上，采用同一式
$$
\frac{\varphi'(E)}{\pi}=\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\mathsf Q(E)=-,i,S(E)^\dagger ,\partial_E S(E),
$$
并以 Birman–Kreĭn 公式联系散射相位与谱移函数，作为能量/时间读数与"提交"的公共母刻度。([link.aps.org][4])

5. **信息几何与选择.** "最小-KL 在线性一致性约束下给出指数族/softmax、并满足 Pythagorean 身份与 Fenchel 双性"；"TV–KL"的 Pinsker 界用于温度-扰动-抖动的稳定估计。([pages.stern.nyu.edu][5])

6. **可逆账本.** 仅信息**抹除**耗散（Landauer 下界），**逻辑可逆**即可在极限上**任意低耗散**；随机采样与打平证据通过可逆寄存器记账（Bennett）。([dl.acm.org][6])

---

## 1. 模型：有限区域的局部可逆边界条件（RLBC）

令 $\Lambda\Subset\mathbb Z^d$ 为连通有限区域，取厚度足够的边界带 $\partial\Lambda$。内部一步演化由某个 RCA $F_\Lambda$ 给出。定义**边界层算子**
$$
\mathsf B:\ A^{\partial\Lambda}\times \mathcal E\ \longrightarrow\ A^{\partial\Lambda}\times \mathcal E,
$$
其中 $\mathcal E$ 是**可逆辅助寄存器**（证据/随机子/打平标签等）。**一轮演化**定义为
$$
\mathcal U \coloneqq F_\Lambda\circ \mathsf B\quad\text{（先边界，后内部）}.
$$
称 $\mathsf B$ 为**局部可逆边界条件**（RLBC），若满足：

* **(R1) 局部性**：$\mathsf B$ 仅读写 $\partial\Lambda$ 及其有限外侧壳层（或把外侧观测压入 $\mathcal E$），不触及 $\Lambda^\circ$；
* **(R2) 双射性**：$(b,\epsilon)\mapsto (b',\epsilon')$ 为置换；
* **(R3) 证据可追账**：一切用于抉择的随机子、打平索引与观测证据均写入 $\mathcal E$，以便反演恢复（Bennett 嵌入）。([dl.acm.org][6])

在分区实现中，令所有"触边块"各施以块内置换；由**块置换的并行直积=置换**，$\mathsf B$ 自动满足 (R2)。Margolus 分区的反向次序与逆置换给出 $\mathsf B^{-1}$。([维基百科][2])

---

## 2. 级联可逆性与可判性

**命题 2.1（级联可逆）.** 若 $F_\Lambda$ 为 RCA，$\mathsf B$ 为 RLBC，则 $\mathcal U=F_\Lambda\circ\mathsf B$ 为 RCA，且 $\mathcal U^{-1}=\mathsf B^{-1}\circ F_\Lambda^{-1}$。

*证明.* 双射复合仍为双射；局部性与等变性由 CHL 表征保留，从而反向映射亦为局部-等变的 CA 规则。([SpringerLink][1])∎

**命题 2.2（边界-内部一体的可判性子类）.** 在下列两类实现中，$\mathcal U$ 的可逆性**可判**且可构造反演：

* **分块/分区 RCA**：当且仅当各块规则为置换。([维基百科][2])
* **线性-中间边界**：可逆性化为规则矩阵的可逆及其 Kronecker-分解；可给出多维与中间边界下的高效算法。([aimspress.com][7])

**注（一般性不可判定）.** 二维及以上一般邻域 CA 的可逆性不可判定（Kari），故本文之 RLBC 选取位于可验证子类。([ui.adsabs.harvard.edu][3])

---

## 3. 选择算子：KL/Bregman 保真（软→硬）

设边界可行动作集合 $\mathcal A(b)$。给定基准 $q(\cdot\mid b)$ 与线性一致性约束 $Ap=b^\star$。

**定义 3.1（软选择 / I-投影）.**
$$
p^\star(\cdot\mid b)\in\arg\min_{p\in\Delta(\mathcal A(b))}\Big\{D_{\mathrm{KL}}!\big(p|q\big):\ Ap=b^\star\Big\},
$$
其 KKT 条件给
$$
p^\star(a\mid b)\ \propto\ q(a\mid b),e^{\langle\lambda,basis(a)\rangle},
$$
即指数族/softmax；并满足信息几何的 Pythagorean 身份与 Fenchel-Legendre 对偶。([pages.stern.nyu.edu][5])

**命题 3.2（稳健性与 TV-KL 界）.** 当温度/正则参数改变引入的 KL 误差为 $\delta$ 时，总变差偏移受 Pinsker 界
$$
|p_1-p_2|_{\mathrm{TV}}\le \sqrt{\tfrac12 D_{\mathrm{KL}}(p_1|p_2)}
$$
控制，可作为"温度—抖动"的上界；必要时可用 Bretagnolle–Huber 界改进。([维基百科][8])

**定理 3.3（Γ-极限：软→硬）.** 令 $\Phi_\tau(p)=D_{\mathrm{KL}}(p|q)+\tau,R(p)$（$R$ 强凸）；当 $\tau\downarrow 0$ 时，$\Phi_\tau$ 的极小者 $p^\star_\tau$ 在 Γ-意义下收敛到某个极大化线性泛函的点质量 $ \delta_{a^\star}$（硬选择）。([SpringerLink][9])

*证明略.* 利用强凸-Γ-紧性与线性泛函的 Mosco 极限，结合同胚嵌入把极小序列的任何弱极限识别为极值点；唯一性与选择稳定性由 3.2 给出。∎

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
满足 (R1)–(R3)，并且在分块实现下为边界触块置换的直积。

**定理 5.2（RLBC ⊗ RCA ⇒ RCA）.** 若 $F_\Lambda$ 为 RCA、$\mathsf B$ 为 RLBC，则 $\mathcal U=F_\Lambda\circ\mathsf B$ 为 RCA；$\mathcal U^{-1}=\mathsf B^{-1}\circ F_\Lambda^{-1}$。([SpringerLink][1])

**定理 5.3（选择 = I-投影；软→硬）.** 设 $Ap=b^\star$ 为线性一致性约束，则
(i) $p^\star=\arg\min D_{\mathrm{KL}}(p|q)$ 唯一，且为指数族；
(ii) 当温度 $\tau\downarrow 0$ 时，$p^\star\Rightarrow \delta_{a^\star}$；
(iii) 抖动稳定性受 Pinsker/Bretagnolle–Huber 界控制。([pages.stern.nyu.edu][5])

**定理 5.4（可逆账本化）.** 令 $\operatorname{Sel}$ 为 5.3 的软/硬选择。存在一族边界块-置换 $\{\Pi_{\text{block}}^{(a)}\}_{a\in\mathcal A}$ 与可逆寄存器更新，使
$$
\mathsf B_\theta=\prod_{\text{触边块}}\Pi_{\text{block}}^{(a^\star_\theta)}
$$
构成 RLBC，并且采样/打平的全部信息被写入 $\mathcal E$ 并在 $\mathsf B_\theta^{-1}$ 中回擦，无 Landauer 成本。([dl.acm.org][6])

**定理 5.5（线性-边界的可逆判据）.** 在线性 CA 与"中间边界"设置下，$\mathcal U$ 的可逆性等价于相应规则矩阵的可逆性；矩阵可经 Kronecker-分解降维判定。([aimspress.com][7])

---

## 6. 与窗化读数—相位—态密度—群延迟刻度的衔接

将边界的"证据汇总/一致性约束"来源于一类窗化谱读数：在绝对连续谱区，以同一刻度
$$
\frac{\varphi'(E)}{\pi}=\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\quad \mathsf Q=-iS^\dagger S',
$$
把"读数"表述为相位导数/相对态密度/群延迟迹的积分泛函；Birman–Kreĭn 公式给出谱移与散射相位的等价，从而可把"提交/抉择"的一致性约束 $Ap=b^\star$ 明确地绑定到能量-相位账本。边界-选择的**软→硬**转变对"读数抖动"的灵敏度由 Pinsker-型不等式与线性化响应估计控制。([link.aps.org][4])

---

## 7. 范式构造：Margolus-边界的可逆抉择器

在二维 Margolus 分区上，设外圈全为"触边块"。对每个触边块，给定有限动作集 $\mathcal A\subset \mathfrak S(A^{2\times 2})$（块内置换族）。令
$$
a^\star_\theta(\text{局部观测},\epsilon)\in\arg\min_{a\in\mathcal A}\ D_{\mathrm{KL}}!\big(p(\cdot\mid b),|,q_\theta(\cdot\mid b)\big)\ \text{或其软化抽样},
$$
并把平手/抽样标签写入 $\epsilon$。定义
$$
\mathsf B_\theta=\prod_{\text{触边块}}\Pi_{\text{block}}!\big(a^\star_\theta\big),
$$
则 $\mathsf B_\theta$ 为置换；与内部分块 RCA 级联后，$\mathcal U$ 保持可逆；$\epsilon$ 记账保证反演可恢复全部随机/证据路径。([维基百科][2])

---

## 8. 端到端可验证清单（实验-无涉的理论化）

1. **可逆性核查**：分块-置换或线性-边界矩阵法；二维一般邻域的不可判定区不进入实现口径。([维基百科][2])
2. **选择-保真**：求解 I-投影（或其凸对偶），软/硬在温度参数调控下互达；抖动-误差用 Pinsker/Bretagnolle–Huber 界。([pages.stern.nyu.edu][5])
3. **可逆账本**：Knuth–Yao/DDG-tree 或别名法的可逆化；随机子与索引写入 $\mathcal E$；反演回擦。([semanticscholar.org][10])
4. **刻度绑定**：以 $\tfrac{\varphi'}{\pi}=\rho_{\mathrm{rel}}=\tfrac1{2\pi}\mathrm{tr},\mathsf Q$ 与 Birman–Kreĭn 公式将"读数→约束"嵌入统一能量/相位账本。([link.aps.org][4])

---

## 附录 A：Garden-of-Eden 与 RLBC 的一致性

在欧氏格上，Garden-of-Eden 定理给**局部单射⇔全局满射**。RLBC 的块置换实现使边界层在其作用域内**局部单射**，内部 RCA 又是全局双射；二者级联保持单射与满射，于是整体仍为 RCA。该论证依 CHL 的连续-等变闭性与 GOE 的单射-满射等价。([维基百科][11])

---

## 附录 B：Γ-极限下的软→硬选择

设可行集为紧单纯形与线性约束之交。定义 $\Phi_\tau(p)=D_{\mathrm{KL}}(p|q)+\tau R(p)$（$R$ 为强凸、下半连续）。则 $\Phi_\tau\xrightarrow{\Gamma}\Phi_0$（在弱拓扑下），$\operatorname{argmin}\Phi_\tau\to \operatorname{argmin}\Phi_0$。当 $\Phi_0$ 的极小集合为一组面上的极点，对偶问题（线性目标）之解即为硬选择的 argmax；唯一性可通过一般位置与强凸扰动保证。([SpringerLink][9])

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
* Wigner（相位导数/时间延迟）；Smith（$\mathsf Q=-iS^\dagger S'$）；Birman–Kreĭn 公式（谱移-散射）。([link.aps.org][15])

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
