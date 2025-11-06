# 不完备 = 非停机：在逻辑—计算—信息—动力三层统一框架下的等价定理

Version: 1.7

## 摘要

建立一条跨越**逻辑—计算**、**信息—读数**与**可逆动力**三层的严格等价链：在满足"活性（完备停机）约束"的增链流程中，**完备不可达**当且仅当**永不停机**。逻辑层以图灵停机不可判与哥德尔—Rosser不完备构成必要与充分的两端；信息—读数层以窗化散射—信息几何（WSIG）给出有限资源下**别名—伯努利层—尾项**与**KL 模型错配**组成的剩余预算；除非同时满足"带限+Nyquist、无限阶 EM（或处于可精确阶的情形）、无尾截断且 $p=q$"四项理想条件（含退化），该预算在有限阶段于对应非退化条件下**严格大于零**，从而在"降残差=目标"的活性约束下排除停机；动力层以可逆元胞自动机（RCA）的**局部可逆边界补全**（RLBC）刻画"完备"，借助二维 CA 之满射/可逆性不可判与 Garden-of-Eden 判据，由于**不存在统一的、对所有实例都在有限阶段给出"全局双射达成"证毕的程序**，一般情形下边界扩展不保证在有限步终止。三层合并为主等价式"**不完备 = 非停机**"，并给出若干可复现实例与可拓展方向。

**关键词**：停机问题；不完备性；$\Sigma^0_1$-hard；窗化散射；Pinsker 不等式；Birman–Kreĭn 公式；Wigner–Smith 群延迟；可逆元胞自动机；Garden-of-Eden

---

## Notation & Axioms / Conventions

**（卡片 A：刻度同一）** 采用散射统一刻度
$$
\frac{\varphi'(E)}{\pi} = \rho_{\mathrm{rel}}(E) = \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\quad \mathsf Q(E)=-i S(E)^\dagger \partial_E S(E).
$$
并以 Birman–Kreĭn 公式择号约定 $\det S(E)=\exp(2\pi i\xi(E))$，故 $\partial_E\arg\det S(E)=2\pi\xi'(E)=\operatorname{tr}\mathsf Q(E)$。**定义总散射相位**
$$
\boxed{\varphi(E):=\tfrac{1}{2}\arg\det S(E)\ \text{（取连续支）}}
$$
于是 $\varphi'(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)$，与上式刻度 $\rho_{\mathrm{rel}}(E)=(1/2\pi)\operatorname{tr}\mathsf Q(E)$ 自洽。该记号于酉散射下与相对态密度一致。([chaosbook.org][1])

**（卡片 B：有限阶 NPE 纪律）** 任何窗化读数采用 Nyquist–Poisson–Euler–Maclaurin 三分解：在带限与 Nyquist 采样步长下别名项可归零；有限阶 Euler–Maclaurin 仅给出**有界且可控**的伯努利层误差；截断窗的尾项由支撑/正则受控。常数规范以 NIST DLMF 为准。([dlmf.nist.gov][2])

**用词约定**："窗口/测量/读数"统一为算子—测度—函数对象（Toeplitz/Berezin 压缩），不涉实验叙述；"活性（完备停机）约束"定义见 §3.1。

**概率记号与 KL 约定**：记 $p$ 为目标/真实读数的参考概率测度，$q$ 为模型测度；写 $p\ll q$ 表示 $p$ 对 $q$ 绝对连续；本文 $D_{\mathrm{KL}}(p|q)$ 采用**自然对数**刻度。

---

## 1. 引言

在以**追求对问题族 $\mathcal Q$ 的完备裁决**为停止条件的自动增链流程中，"完备不可达"是否必然意味着"流程永不停机"？本文给出肯定答案，并在三层框架中形成对等判据：

1. **逻辑—计算层**：若 $\mathcal Q$ 至少 $\Sigma^0_1$-hard，则一旦停机即可判停机集，悖于图灵；而在一致、递归可枚举且足以表达算术的阶段理论增链中，哥德尔—Rosser确保任一阶段的完备性不可达，因而流程不得停。([cs.virginia.edu][3])

2. **信息—读数层**：WSIG 给出统一刻度与有限资源误差学。除非同时满足"带限+Nyquist、无限阶 EM（或可精确阶）、无尾截断且 $p=q$"四项理想条件，NPE 三分解与 KL–Pinsker 界保证在相应非退化条件下剩余预算 $\mathscr R>0$，从而在"残差 $\mathscr R\downarrow 0$"目标下迫使流程持续。([dlmf.nist.gov][2])

3. **动力层**：将"完备"实现为 RCA 的全局双射补全。由于二维 CA 的满射/可逆性不可判定，**不存在统一的、对所有实例都在有限阶段给出"全局双射达成"证毕的程序**；因此一般情形下无法保证边界扩展在有限步终止。([科学直通车][4])

---

## 2. 预备知识

### 2.1 计算与逻辑

**记号补充（停机集）**：记
$$
K:=\{(M,x)\mid M(x)\downarrow\}
$$
为图灵**停机集**（$M$ 为图灵机、$x$ 为其输入，$M(x)\downarrow$ 表示停机）。经典结论：$K$ 为 $\Sigma^0_1$-完全集。

**停机不可判**：不存在普遍算法判定任意图灵机是否停机。([cs.virginia.edu][3])
**Rice 定理**：程序任一非平凡语义性质不可判。([维基百科][5])
**哥德尔—Rosser**：一致、递归可枚举且足以表达算术的理论必不完备；Rosser 将 $\omega$-一致性要求降至一致性。([homepages.uc.edu][6])
**$\Sigma^0_1$-hard** 与 r.e.：$\Sigma^0_1$ 等同于递归可枚举；多对一（many-one）归约用于刻画"至少同难"。([维基百科][7])

### 2.2 信息几何与 I-投影

**Pinsker 不等式**（自然对数）：$\mathrm{TV}(p,q)\le\sqrt{\tfrac12 D_{\mathrm{KL}}(p|q)}$。
**I-投影**：在凸约束族上的最小 $D_{\mathrm{KL}}$ 投影 $q^\star$ 存在且唯一（适度正则），并在统计与凸优化中等价。([arXiv][8])

### 2.3 相位—密度—延迟刻度与 Birman–Kreĭn

**Wigner–Smith 群延迟**：$\mathsf Q(E)=-iS^\dagger \partial_E S$，$\partial_E\arg\det S(E)=\operatorname{tr}\mathsf Q(E)$。
**Birman–Kreĭn**：$\det S(E)=\exp(2\pi i\xi(E))$，从而 $\xi'(E)=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$，等同于相对态密度。([物理评论链接管理器][9])

### 2.4 NPE 三分解与 Nyquist 条件

若窗 $w$ 与核 $h$ 带限，且采样步长 $\Delta<\pi/(\Omega_w+\Omega_h)$，则**别名项为零**；有限阶 Euler–Maclaurin 给出伯努利层误差上界；有限窗截断导致尾项。常数归一与公式见 DLMF §1.8 与 §2.10。([dlmf.nist.gov][2])

### 2.5 可逆元胞自动机与 Garden-of-Eden

二维 CA 的满射性与可逆性判定不可判；Garden-of-Eden 定理在阿门群背景下给出两条等价：**存在无前像（Garden-of-Eden 配置）⇔ 非满射**，且 **满射 ⇔ 预单射（pre-injective）**，并与可逆性/满射性性质相联。([科学直通车][4])

---

## 3. 模型与设定

### 3.1 问题族与活性（完备停机）约束

令 $\mathcal Q$ 为可计算描述的判定问题族，且至少 $\Sigma^0_1$-hard。流程 $\mathcal A$ 生成一致的、递归可枚举的理论增链
$$
T_0\subset T_1\subset \cdots,\quad T_t\text{ 可用于对 }q\in\mathcal Q\text{ 给出裁决。}
$$
定义**活性（完备停机）约束**：
$$
\boxed{\mathcal A\text{ 停机} \Longleftrightarrow T_t\text{ 已对所有 }q\in\mathcal Q\text{ 完备裁决}}.
$$

### 3.2 资源—窗—核四元组与剩余预算

对任意有限资源**四元组** $\mathsf R=(R,T,\Delta;M)$ **与模型** $q$，定义**剩余预算**
$$
\mathscr R:=\underbrace{\mathcal E_{\mathrm{alias}}(\Delta)}_{\text{Poisson}}
+\underbrace{\mathcal E_{\mathrm{EM}}(M)}_{\text{Euler–Maclaurin（取余项的绝对值/范数上界）}}
+\underbrace{\mathcal E_{\mathrm{tail}}(R,T)}_{\text{截断}}
+\underbrace{c\sqrt{\tfrac12 D_{\mathrm{KL}}(p|q)}}_{\text{模型错配}},
$$
其中三项 NPE-误差均**按非负量**（绝对值或范数上界）计入，末项由 Pinsker 给出从错配到读数差异的根式上界；常数 $c$ 吸收规范差异。

### 3.3 RCA 的局部可逆边界补全（RLBC）

设 $\Lambda_t\subset\mathbb Z^2$ 为递增有限域。RLBC 将"外部解释/建模"抽象为在 $\Lambda_t$ 的**可逆边界双射**，与体内可逆更新级联为全局映射；"完备"指存在 $t^\star$ 使得延拓为**全局双射**并不再需要扩展。

---

## 4. 逻辑—计算层主定理

### 定理 4.1（"停机 ⇒ 可判停机"，故不可停机）

若 $\mathcal Q$ 至少 $\Sigma^0_1$-hard 且 $\mathcal A$ 满足活性约束，则 $\mathcal A$ 不停机。
**证明**：由于 $\Sigma^0_1$-hard，存在多对一归约 $f$ 使对任意图灵机—输入对 $(M,x)$，$(M,x)\in K\iff f(M,x)\in\mathcal Q$。若 $\mathcal A$ 于 $t^\star$ 停机，则 $T_{t^\star}$ 可判定 $\mathcal Q$，从而可判定 $K$，悖于图灵定理。□  ([cs.virginia.edu][3])

### 定理 4.2（"完备不可达 ⇒ 非停机"）

若每个 $T_t$ 一致、递归可枚举并能解释 PA，则对足以表达算术的 $\mathcal Q$，不存在 $t^\star$ 使 $T_{t^\star}$ 完备（哥德尔—Rosser）。由活性约束得 $\mathcal A$ 不停机。□  ([homepages.uc.edu][6])

### 推论 4.3（等价）

在上述条件下，$\text{永远无法完备}\Longleftrightarrow\text{永远不停机}$。

---

## 5. 信息—读数层的强迫非停机

### 定理 5.1（有限资源的非负剩余预算与严格正的充分条件）

对任意有限 $(R,T,\Delta;M)$ 与模型 $q$，有 $\mathscr R\ge 0$。此外，只要下列四项中至少一项与其对应的**非退化**条件同时成立，则 $\mathscr R>0$：  
(i) 带限+Nyquist **不成立**且组合谱在 $[-\pi/\Delta,\pi/\Delta]$ 之外有非零质量；  
(ii) $M<\infty$ 且相关函数的第 $2M$ 阶导数在某区间上不恒为零（则 EM 余项的**上界**严格为正；依 §3.2 的"绝对值/范数上界"计入，可得该项严格为正）；  
(iii) 存在窗截断且被观测对象在窗外域的质量非零；  
(iv) $D_{\mathrm{KL}}(p|q)>0$（当且仅当 $p=q$ 几乎处处时取 $0$；若二者在正 $p$-测度集合上不同或 $p\nll q$，则 $>0$，可为 $+\infty$）。

**证明要点（修订）**：四项均为非负；在各自非退化条件下对应项的**计入量（上界）**严格为正，其余项非负，故和为正。若四项理想条件**同时**成立（含退化情形，如真带限且满足 Nyquist、$M$ 能对所涉函数给出恰当精确度、外域质量为零且 $p=q$），则 $\mathscr R=0$。□  ([dlmf.nist.gov][2])

### 定理 5.2（"$\mathscr R$ 与停机"的正确关系）

**引理（完备裁决的必要条件）**：若在阶段 $t$ 达到活性（完备停机）约束，则对 §3.2 的读数—预算定义必有 $\mathscr R(t)=0$；否则存在不可消除的读数不确定性，使对部分 $q\in\mathcal Q$ 的裁决无法在有限资源下保证一致。

由此，停机仅可能发生于 $\mathscr R=0$ 的阶段。若满足定理 5.1 的任一非退化条件，则对任意有限阶段 $t$ 有 $\mathscr R(t)>0$，故不能在有限步停机；$\mathscr R(t)$ 允许随资源投入而趋近于 $0$，这不影响"完备不可达 ⇒ 非停机"的结论。□

### 讨论 5.3（相位—密度母刻度的可观测像）

在刻度同一式下，理想完备对应 $\xi'(E)=\tfrac1{2\pi}\operatorname{tr}\mathsf Q(E)$ 全域对齐；有限资源下的"随机感"即 $\mathscr R>0$ 的可测投影。([chaosbook.org][1])

---

## 6. 动力层：RLBC 的无尽边界

### 定理 6.1（不存在统一的有限阶段证毕程序）

将"完备"定义为存在 $t^\star$ 使 RLBC 延拓为全局双射。二维 CA 的满射性/可逆性是不可判定的。若存在**对所有实例**都能在有限阶段输出"已达成"或"不可达成"之一结论的统一程序（两侧有限证毕），则可据此构造判定算法，从而可判定满射/可逆，矛盾。仅有单侧（仅"已达成"）的有限证毕最多给出半判定，不足以推出可判定；因此我们断言不存在"两侧"有限证毕的统一程序。于是，一般情形下 RLBC 的边界扩展不保证在有限步出现终点。个别特例（如局部置换型 CA）可在有限阶段证明可逆，不与此结论冲突。□  ([科学直通车][4])

**旁证**：Garden-of-Eden 定理在阿门群条件下给出"满射⇔预单射"，与可逆性刻画相容。([irma.math.unistra.fr][10])

---

## 7. 例与构造

**例 7.1（窗化阈值与 $\Sigma^0_1$ 嵌入）**：构造带限窗—核，使谓词"存在能量区间使窗化相对态密度超过阈值"与某机停机等价；则任一有限 $(R,T,\Delta;M)$ 皆使 $\mathscr R>0$，在"降残差"目标下流程持续。其可行性依赖刻度同一与 Nyquist/EM 误差学。([dlmf.nist.gov][2])

**例 7.2（RCA 的 RLBC 补全）**：以"是否存在 Garden-of-Eden"或"全局可逆"为谓词，逐步扩展可逆边界；若设计一个对**所有**二维 CA 都保证在有限阶段出现的终端证毕机制，将得到一个可判算法，违背不可判结论；对特定可逆/满射 CA 给出有限证毕并不推出普适判定。([科学直通车][4])

---

## 8. 与统一体系的接口

* **刻度桥**：$\partial_E\arg\det S=\operatorname{tr}\mathsf Q=2\pi\xi'(E)$ 统一"相位导数—群延迟—相对态密度"。([物理评论链接管理器][9])
* **NPE-Nyquist 纪律**：$\Delta<\pi/(\Omega_w+\Omega_h)\Rightarrow \mathcal E_{\mathrm{alias}}=0$；有限阶 EM 与尾项提供可控上界。([dlmf.nist.gov][2])
* **I-投影与稳定性**：最小 $D_{\mathrm{KL}}$ 投影给出"最接近可达模型"的读数对齐与稳定链。([pages.stern.nyu.edu][11])

---

## 9. 限制与拓展

1. **关于 $\mathcal Q$**：等价式依赖 $\Sigma^0_1$-hard；对更弱族需个别化。([维基百科][7])
2. **散射场景**：非酉/耗散体系可用广义 BK 与迹公式处理，常数规范依赖具体耦合；详见现代综述。([applied.math.tugraz.at][12])
3. **群上 CA**：非阿门群时 Garden-of-Eden 结论细别，需就群性质校正。([irma.math.unistra.fr][10])

---

## 10. 结论

在活性（完备停机）约束下，**逻辑—计算层**的图灵与哥德尔—Rosser、**信息—读数层**的有限资源剩余预算、以及**动力层**的 RLBC 不可达性，三者严密联锁为
$$
\boxed{\text{永远无法完备} \Longleftrightarrow \text{永远不停机}}.
$$
该等价式把"随机感源自不完备"的直觉落在可检的统一刻度与不可判性判据之上，并为窗口化读数设计与可逆动力语义提供同一结构约束。

---

## 参考文献（选）

1. A. M. Turing, *On Computable Numbers, with an Application to the Entscheidungsproblem*, Proc. Lond. Math. Soc., 1936.
2. H. G. Rice, *Classes of Recursively Enumerable Sets and Their Decision Problems*, Trans. AMS, 1953.
3. K. Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*, 1931；J. B. Rosser, *Extensions of Some Theorems of Gödel and Church*, 1936.
4. P. G. Hinman, *Recursion-Theoretic Hierarchies*, Springer, 1978.
5. I. Csiszár, *I-Divergence Geometry of Probability Distributions and Minimization Problems*, Ann. Probab., 1975；G. L. Gilardoni, *On Pinsker's Type Inequalities*, 2006.
6. E. P. Wigner, *Lower Limit for the Energy Derivative of the Scattering Phase Shift*, Phys. Rev., 1955；F. T. Smith, *Lifetime Matrix in Collision Theory*, Phys. Rev., 1960.
7. J. Behrndt, M. Malamud, H. Neidhardt, *Trace Formulae for Dissipative and Coupled Scattering Systems*, 2008；（及 Birman–Kreĭn 相关综述与教材条目）。
8. NIST DLMF §1.8（Poisson Summation）、§2.10（Euler–Maclaurin）.
9. J. Kari, *Reversibility and Surjectivity Problems of Cellular Automata*, JCSS, 1994；Moore–Myhill（Garden-of-Eden）及其在阿门群上的推广。

[1]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[2]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[3]: https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf?utm_source=chatgpt.com "ON COMPUTABLE NUMBERS, WITH AN APPLICATION ..."
[4]: https://www.sciencedirect.com/science/article/pii/S002200000580025X?utm_source=chatgpt.com "Reversibility and surjectivity problems of cellular automata"
[5]: https://en.wikipedia.org/wiki/Rice%27s_theorem?utm_source=chatgpt.com "Rice's theorem"
[6]: https://homepages.uc.edu/~martinj/History_of_Logic/Godel/Godel%20%E2%80%93%20On%20Formally%20Undecidable%20Propositions%20of%20Principia%20Mathematica%201931.pdf?utm_source=chatgpt.com "On Formally Undecidable Propositions of Principia ..."
[7]: https://en.wikipedia.org/wiki/Arithmetical_hierarchy?utm_source=chatgpt.com "Arithmetical hierarchy"
[8]: https://arxiv.org/abs/cs/0603097?utm_source=chatgpt.com "On Pinsker's Type Inequalities and Csiszar's f-divergences. Part I: Second and Fourth-Order Inequalities"
[9]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[10]: https://irma.math.unistra.fr/~coornaer/IJM598.pdf?utm_source=chatgpt.com "Expansive actions of countable amenable groups, homoclinic ..."
[11]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[12]: https://www.applied.math.tugraz.at/~behrndt/BehrndtMalamudNeidhardt08-3.pdf?utm_source=chatgpt.com "Trace formulae for dissipative and coupled scattering ..."
