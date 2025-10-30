# EBOC–RCA 等价的正式理论

**——二维"静态块宇宙"与一维"可逆元胞自动机"的滑动块码范畴同构**

Version: 1.6  
(2025-10-30, Asia/Dubai)

**作者**：Auric（S-series / EBOC）

**缩写统一**：EBOC = **E**ternal-**B**lock **O**bserver-**C**omputing（永恒静态块·观察—计算）

---

## 摘要

本文把 EBOC 形式化为二维子移位 $X\subset\mathcal A^{\mathbb Z^2}$ 的"静态块宇宙"，将"时间演化"解释为对 $X$ 的**叶/时间片**读取；把 RCA（可逆元胞自动机）形式化为一维子移位 $(Y,\sigma)$ 上的**双射滑动块码** $F:Y\to Y$。我们给出一个**充要判据与范畴同构定理**：当且仅当 EBOC 的叶推进是**局部**且**双射**，且 $X$ 等于该推进的**空间–时间子移位**时，EBOC 与某一 RCA **共轭等价**；反之任意 RCA 的全时空图天然给出一例 EBOC。证明基于 Curtis–Hedlund–Lyndon（CHL）定理（"连续 + 与移位对易"$\Leftrightarrow$ 有限半径局部规则）与"自同态的空间–时间移位"标准构造。并讨论不可逆情形的**分区/二阶/升维**可逆完备化，以及一维可判—高维不可判的算法学边界（Moore–Myhill 之 Garden-of-Eden 与 Kari 不可判定性）。

---

## 1. 预备与记号

**移位与子移位**。字母表 $\mathcal A$ 有限；全移位 $\mathcal A^{\mathbb Z^d}$ 赋以积拓扑与坐标移位 $\sigma$。**SFT** 由有限禁型给出；**sofic** 为 SFT 的滑动块像。**滑动块码**（sliding block code）定义为与移位对易且连续的映射；**CHL 定理**刻画了"滑动块码 $\Leftrightarrow$ 连续且与移位对易"，为 CA 的标准拓扑表述。([SpringerLink][1])

**空间–时间子移位**。对一维自同态/同构 $\Phi$ 的全轨道构成二维系统（"时空图"）；研究 $\Phi$ 的动力学可等价为研究其关联的二维子移位之性质。([arXiv][2])

**Garden-of-Eden（GoE）与可逆性**。在 $\mathbb Z^d$ 及更一般的**可和群（amenable groups）**上，GoE 定理刻画了**满射 $\Leftrightarrow$ 预单射**（无"孪生有限块"），构成可逆/满射/单射关系的基石；**可和群**包含所有阿贝尔群与可解群等。对**非可和群**存在反例（"满射 $\Rightarrow$ 预单射"不再成立）。([arXiv][3])

**可判定性边界**。一维 CA 的注入/满射/可逆性**可判定**（Amoroso–Patt；De Bruijn-图算法等）；但二维及以上的可逆/满射性判定**不可判定**（Kari）。([科学直通车][4])

---

## 2. EBOC 的公理化

**定义 2.1（EBOC 静态块）**。设 $\mathcal A$ 有限。EBOC 宇宙为 $\mathcal U=(X,\sigma_h,\sigma_v)$，其中 $X\subset\mathcal A^{\mathbb Z^2}$ 为二维子移位（通常为 SFT），$\sigma_h,\sigma_v$ 分别为水平/垂直移位。对 $x\in X$、$t\in\mathbb Z$，定义**行叶** $\mathrm{row}_t(x)\in\mathcal A^{\mathbb Z}$。

**定义 2.2（叶-局部性与叶-双射）**。若存在半径 $r\in\mathbb N$ 与局部规则 $\Phi:\mathcal A^{[-r,r]}\!\to!\mathcal A$ 使
$$
x_{t+1,i}=\Phi\big(x_{t,i-r},\ldots,x_{t,i+r}\big)\qquad(\forall\,x\in X,\,t,i\in\mathbb Z),
$$
且诱导的行推进 $F:\mathrm{row}_t\mapsto \mathrm{row}_{t+1}$ 在行迹
$$
Y:=\{\mathrm{row}_0(x):x\in X\}\subset\mathcal A^{\mathbb Z}
$$
上是**双射**，则称 $\mathcal U$ **叶-可逆确定**。

**定义 2.3（时空一致性）**。称 $X$ **时空一致**，若
$$
X=\Bigl\{x\in Y^{\mathbb Z}:\ \mathrm{row}_{t+1}=F(\mathrm{row}_t)\ \ \forall\,t\in\mathbb Z\Bigr\},
$$
即 $X$ 等于 $F$ 的**空间–时间子移位**。([arXiv][2])

---

## 3. 主定理：EBOC–RCA 的充要判据与共轭

**定理 3.1（EBOC–RCA 等价）**

下述两类对象在保持叶的因子–共轭意义下**等价**：

1. 一维子移位 $(Y,\sigma)$ 与其**可逆**滑动块码 $F:Y\to Y$（即 RCA）；
2. 满足定义 2.2–2.3 的二维 EBOC $(X,\sigma_h,\sigma_v)$。

并存在互为准逆的函子
$$
\mathsf{Spacetime}:(Y,F)\mapsto X_F,\qquad
\mathsf{Slice}:(X,\sigma_h,\sigma_v)\mapsto (Y,F),
$$
使 $\mathsf{Slice}\circ\mathsf{Spacetime}\cong \mathrm{Id}$ 与 $\mathsf{Spacetime}\circ\mathsf{Slice}\cong \mathrm{Id}$。

**证明（要点）**

(a) **RCA $\Rightarrow$ EBOC**：设 $F$ 半径 $r$。定义
$$
X_F:=\{x\in\mathcal A^{\mathbb Z^2}:\ x_{t+1,i}=\Phi(x_{t,i-r},\dots,x_{t,i+r})\}.
$$
该集合由有限禁型刻画，故为二维 SFT；$\sigma_v$ 即一次时间推进。由 CHL，局部性来源于"连续 + 与移位对易"，而可逆性给出双向局部规则。于是 $X_F$ 满足时空一致并构成 EBOC。([SpringerLink][1])

(b) **EBOC $\Rightarrow$ RCA**：叶-局部性给出 $F$ 与 $\sigma$ 对易且连续；叶-双射与紧致性蕴含 $F^{-1}$ 连续，从而 $F$ 为**可逆滑动块码**（CHL 的可逆版）；时空一致性保证 $X=X_F$。([SpringerLink][1])

(c) **范畴陈述**：两方向构造在"叶保持的因子–共轭"范畴中给出自然同构（$(Y,\sigma)$ 上的自同态/同构 $\leftrightarrow$ 其二维时空系统的结构）。([arXiv][2])

证毕。

---

## 4. 非可逆情形的可逆完备化（构造性）

**命题 4.1（分区可逆化）**。采用 Toffoli–Margolus 的**分区/块**更新：将格点按固定棋盘式分块，每一步对各块施加**可逆置换**，交替分区更新，即得**分区可逆 CA**（PCA/BCA），且与普通 CA 互相可模拟。([MIT CSAIL][6])

**命题 4.2（成对提升的二阶可逆化——充要条件）**。令局部规则 $G$ 给出"二阶"更新 $x_{t+1}=G(x_t,x_{t-1})$。在扩展字母 $\tilde{\mathcal A}=\mathcal A\times\mathcal A$ 上定义一阶滑动块码
$$
F:(u,v)\longmapsto\big(G(u,v),u\big).
$$
则 $F$ 为**可逆**滑动块码的充要条件是：对每个固定的第一输入配置 $u$，由 $v\mapsto G(u,v)$ 定义的 CA $G_u$ 在**配置空间上为双射**（**充分但非必要的局部判据**：对每个邻域上下文，$G$ 对**第二输入**作用为字母表上的**置换**；一般情形只需 $G_u$ 为**可逆 CA**，并不要求逐点置换，例如移位即给出可逆而非逐点置换的 $G_u$）。在该条件下，逆映射亦为**有限半径**的局部形式（半径**不必**与 $F$ 相同）：
$$
F^{-1}:(u',v')\longmapsto\big(v',H(u',v')\big),
$$
其中 $H(u',v')$ 为满足 $G(v',H)=u'$ 的唯一解。典型充分情形为 Margolus/Toffoli 的"二阶"方案：取 $G(u,v)=\Psi(u)\star v$，其中对每个 $u$ 运算 $\star$ 在 $v$ 上给出置换（如按位异或/块置换），于是条件自动成立。

（依据：二阶 CA 的可逆性等价于"对每个固定 $u$，$G_u$ 为**可逆 CA**"；分区/字母置换是常用**充分**构造，并由 CHL 定理保证逆亦为滑动块码。([MIT CSAIL][6])）

**定理 4.3（升维嵌入 Toffoli）**。任意 $d$ 维 CA **可构造性地嵌入**到 $(d+1)$ 维**可逆** CA 的时空块中：每个"切片"模拟一步，从而在不改原规则下获得可逆实现。([科学直通车][8])

> 注：上式给出一项**通用升维**构造：任意 $d$ 维 CA 可构造性地嵌入到 $(d+1)$ 维**可逆** CA 的时空块中（[8]）。**该构造不主张"最小性"**；在**同维**情形，亦可通过 §4.1 的分区法或 §4.2 的二阶法，在**扩展字母表**下获得可逆完备。

---

## 5. 可判定性与算法学边界

**定理 5.1（一维可判）**。对一维 CA，**满射/单射/可逆性可判定**：Amoroso–Patt 给出注入/满射性的判据；基于 **De Bruijn 图**的**经典判定框架**（Sutner 等）被广泛采用，用以判定注入/满射/可逆性（复杂度依赖于字母表大小与半径，不作统一阶数断言）。([Kari 综述][7])

**定理 5.2（二维不可判）**。维数 $\ge 2$ 时，**可逆性**与**满射性**判定**不可判定**（Kari）。([科学直通车][5])

**命题 5.3（GoE 判据）**。在 $\mathbb Z^d$ 等可和群上，CA 的**满射 $\Leftrightarrow$ 预单射**（Moore–Myhill–Ceccherini-Silberstein–Coornaert 体系）。([arXiv][3])

---

## 6. 对外可检的"等价判据—实施清单"

给定二维 EBOC $(X,\sigma_h,\sigma_v)$：

1. **抽取行迹**：$Y:=\{\mathrm{row}_0(x):x\in X\}\subset\mathcal A^{\mathbb Z}$。
2. **测半径（叶-局部性）**：是否存在统一 $r$ 与 $\Phi$ 使 $x_{t+1,i}=\Phi(x_{t,i-r..i+r})$？（可用高阶块重编码把"需记忆多行"的情形降到有限半径 1）。由 CHL，这等价于 $F$ 是滑动块码。([SpringerLink][1])
3. **检双射（叶-双射）**：判定 $F:Y\to Y$ 之注入/满射：
   – 对满移位/amenable 场景，用 GoE 的"预单射 $\Leftrightarrow$ 满射"。
   – 对一般 sofic，可用 De Bruijn/有限状态覆盖判定框架。([arXiv][3])
4. **时空一致**：验证 $X=\{x\in Y^{\mathbb Z}:\mathrm{row}_{t+1}=F(\mathrm{row}_t)\}$。

若 1)–4) 皆真，则 $(X,\sigma_h,\sigma_v)$ 与 $(Y,F)$**共轭**，等价为 RCA；若 2) 或 3) 失败，可用 §4 的**分区/二阶/升维**作**可逆完备化**以获得"有限扩展下的等价"。([arXiv][2])

---

## 7. 范畴化陈述（总括）

**定理 7.1（范畴同构）**。设 $\mathbf{RCA}$ 的对象为"$(Y,\sigma)$ 上的可逆滑动块码 $F$"与态射为"叶保持共轭"；$\mathbf{EBOC}$ 的对象为"沿行叶-可逆确定且时空一致的二维静态块 $(X,\sigma_h,\sigma_v)$"与态射为"叶保持的局部因子–共轭"。则
$$
\mathsf{Spacetime}:\mathbf{RCA}\rightleftarrows\mathbf{EBOC}:\mathsf{Slice}
$$
给出范畴同构（自然同构到恒等函子），把"一维自同态/同构"的动力学与"二维时空子移位"的结构严格等价。([arXiv][2])

---

## 参考文献（选，统一对应文中 [1]–[9]）

[1] G. A. Hedlund, "Endomorphisms and Automorphisms of the Shift Dynamical System," *Mathematical Systems Theory* 3 (1969), 320–375.（CHL 定理）

[2] V. Cyr, J. Franks, B. Kra, "The Spacetime of a Shift Endomorphism," *Trans. Amer. Math. Soc.* 371 (2019).（时空子移位）

[3] T. Ceccherini-Silberstein, M. Coornaert, "The Garden of Eden Theorem: Old and New," 2018.（GoE 综述）

[4] S. Amoroso, Y. N. Patt, "Decision Procedures for Surjectivity and Injectivity of Parallel Maps for Tessellation Structures," *J. Comput. Syst. Sci.* 6 (1972), 448–464.（一维可判）

[5] J. Kari, "Reversibility of 2D Cellular Automata is Undecidable," *Physica D* 45 (1990), 379–385；以及 "Reversibility and Surjectivity Problems of Cellular Automata," *J. Comput. Syst. Sci.* (1994).（二维不可判）

[6] T. Toffoli, N. Margolus, *Cellular Automata Machines*, MIT Press, 1987.（分区可逆化）

[7] J. Kari, "Theory of Cellular Automata: A Survey," 2005.（综述）

[8] T. Toffoli, "Computation and Construction Universality of Reversible Cellular Automata," *J. Comput. Syst. Sci.* 15 (1977), 213–231.（升维可逆嵌入）

[9] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge Univ. Press, 1995/2021.（符号动力学基础）

---

### 一句话结论

在"叶-局部性 + 叶-双射 + 时空一致"的公理化前提下，**EBOC 与 RCA 是同一类离散动力系统的两种写法**：RCA 的**时空图**就是 EBOC 的**宇宙块**，而 EBOC 的**演化**就是对这块的**逐叶读取**；若不满足双射，可通过分区/二阶/升维取得**可逆完备**并在有限扩展下达到等价。

---

[1]: https://link.springer.com/article/10.1007/BF01691062?utm_source=chatgpt.com "Endomorphisms and automorphisms of the shift dynamical ..."
[2]: https://arxiv.org/abs/1610.07923?utm_source=chatgpt.com "The spacetime of a shift endomorphism"
[3]: https://arxiv.org/pdf/1707.08898?utm_source=chatgpt.com "arXiv:1707.08898v3 [math.DS] 8 Jun 2018"
[4]: https://www.sciencedirect.com/science/article/pii/S0022000072800138?utm_source=chatgpt.com "Decision procedures for surjectivity and injectivity of ..."
[5]: https://www.sciencedirect.com/science/article/pii/016727899090195U?utm_source=chatgpt.com "Reversibility of 2D cellular automata is undecidable"
[6]: https://people.csail.mit.edu/nhm/cam-book.pdf?utm_source=chatgpt.com "Cellular Automata Machines - People | MIT CSAIL"
[7]: https://ibisc.univ-evry.fr/~hutzler/Cours/IMBI_MPS/Kari05.pdf?utm_source=chatgpt.com "Theory of cellular automata: A survey"
[8]: https://www.sciencedirect.com/science/article/pii/S002200007780007X/pdf?md5=2d1b982eeb03c81679a87d9ea21c3447&pid=1-s2.0-S002200007780007X-main.pdf&utm_source=chatgpt.com "Computation and Construction Universality of Reversible ..."
