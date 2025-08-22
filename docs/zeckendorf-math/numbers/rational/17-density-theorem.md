# φ-有理数稠密性定理

## 定义 17.1（φ-有理数在φ-实数中的嵌入）
设 $\mathbb{F}\mathbb{R}$ 为φ-实数集合（将在定理19.1中构造），定义φ-有理数嵌入映射：
$$\iota: \mathbb{F}\mathbb{Q} \to \mathbb{F}\mathbb{R}$$

通过将每个φ-有理数视为常数φ-Cauchy序列实现。

## 引理 17.1（φ-有理数序结构的保持）
嵌入映射 $\iota$ 保持φ-有理数的序关系和域运算：

对 $r_1, r_2 \in \mathbb{F}\mathbb{Q}$：
1. **序保持**：$r_1 \preceq_{\mathbb{F}\mathbb{Q}} r_2 \Leftrightarrow \iota(r_1) \preceq_{\mathbb{F}\mathbb{R}} \iota(r_2)$
2. **运算保持**：$\iota(r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2) = \iota(r_1) \oplus_{\mathbb{F}\mathbb{R}} \iota(r_2)$
3. **乘法保持**：$\iota(r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2) = \iota(r_1) \otimes_{\mathbb{F}\mathbb{R}} \iota(r_2)$

**证明：**
由φ-Cauchy序列的定义和φ-有理数运算的连续性（定理17.10）直接得出。 ∎

## 定理 17.1（φ-有理数的稠密性预备引理）
对任意两个不同的φ-有理数 $r_1, r_2 \in \mathbb{F}\mathbb{Q}$ 且 $r_1 \prec_{\mathbb{F}\mathbb{Q}} r_2$，存在无穷多个φ-有理数位于它们之间。

**证明：**
不失一般性，设 $r_1 \prec_{\mathbb{F}\mathbb{Q}} r_2$。

考虑φ-有理数：
$$r_{mid} = \frac{r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$$

其中 $\mathbf{2}_{\mathbb{F}\mathbb{Q}} = \frac{\mathbf{1}_{\mathbb{F}\mathbb{Z}} \oplus_{\mathbb{F}\mathbb{Z}} \mathbf{1}_{\mathbb{F}\mathbb{Z}}}{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}$。

由序运算的相容性（定理17.7）：
$$r_1 \prec_{\mathbb{F}\mathbb{Q}} r_{mid} \prec_{\mathbb{F}\mathbb{Q}} r_2$$

对区间 $(r_1, r_{mid})$ 和 $(r_{mid}, r_2)$ 递归应用此构造，得到可数无穷个中间φ-有理数。 ∎

## 定义 17.2（φ-区间和φ-邻域）
对φ-有理数 $r_1, r_2 \in \mathbb{F}\mathbb{Q}$ 且 $r_1 \prec_{\mathbb{F}\mathbb{Q}} r_2$，定义：

**φ-开区间**：
$$(r_1, r_2)_{\mathbb{F}\mathbb{Q}} = \{r \in \mathbb{F}\mathbb{Q} : r_1 \prec_{\mathbb{F}\mathbb{Q}} r \prec_{\mathbb{F}\mathbb{Q}} r_2\}$$

**φ-邻域**：
$$U_\varepsilon(r_0) = \{r \in \mathbb{F}\mathbb{Q} : d_{\mathbb{F}\mathbb{Q}}(r, r_0) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon\}$$

其中 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$。

## 定理 17.2（φ-有理数内部稠密性）
φ-有理数在自身的序拓扑中稠密：

对任意φ-开区间 $(r_1, r_2)_{\mathbb{F}\mathbb{Q}}$ 和任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $r \in (r_1, r_2)_{\mathbb{F}\mathbb{Q}}$ 使得 $d_{\mathbb{F}\mathbb{Q}}(r, r_1) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$ 且 $d_{\mathbb{F}\mathbb{Q}}(r, r_2) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$。

**证明：**
由定理18.1，区间 $(r_1, r_2)_{\mathbb{F}\mathbb{Q}}$ 包含无穷多个φ-有理数。

选择充分接近 $r_1$ 和 $r_2$ 的φ-有理数序列，由阿基米德性质（定理15.1），可以找到满足距离条件的φ-有理数。 ∎

## 定理 17.3（φ-有理数在φ-实数中的稠密性）
φ-有理数在φ-实数中稠密：

对任意两个不同的φ-实数 $x, y \in \mathbb{F}\mathbb{R}$ 且 $x \prec_{\mathbb{F}\mathbb{R}} y$，开区间 $(x, y)_{\mathbb{F}\mathbb{R}}$ 包含至少一个φ-有理数。

**证明：**
设 $x, y \in \mathbb{F}\mathbb{R}$ 且 $x \prec_{\mathbb{F}\mathbb{R}} y$。

由φ-实数的构造（通过φ-Cauchy序列），存在φ-有理数序列 $(r_n), (s_n)$ 分别收敛到 $x, y$：
$$\lim_{n \to \infty} r_n = x, \quad \lim_{n \to \infty} s_n = y$$

由于 $x \prec_{\mathbb{F}\mathbb{R}} y$，存在 $N \in \mathbb{F}\mathbb{N}$ 使得对所有 $n \succ_{\mathbb{F}\mathbb{N}} N$：
$$r_n \prec_{\mathbb{F}\mathbb{Q}} s_n$$

由定理18.1，区间 $(r_N, s_N)_{\mathbb{F}\mathbb{Q}}$ 包含φ-有理数 $r_{mid}$。

由φ-有理数序列的收敛性，当 $n$ 足够大时：
$$x \prec_{\mathbb{F}\mathbb{R}} r_{mid} \prec_{\mathbb{F}\mathbb{R}} y$$

因此 $r_{mid} \in (x, y)_{\mathbb{F}\mathbb{R}}$。 ∎

## 引理 17.2（φ-有理数稠密性的度量刻画）
φ-有理数稠密性等价于：

对任意φ-实数 $x \in \mathbb{F}\mathbb{R}$ 和任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在φ-有理数 $r \in \mathbb{F}\mathbb{Q}$ 使得：
$$d_{\mathbb{F}\mathbb{R}}(x, \iota(r)) \prec_{\mathbb{F}\mathbb{R}} \iota(\varepsilon)$$

**证明：**
这是稠密性的标准度量刻画在φ-数系中的对应。
由定理18.3和φ-度量的连续性直接得出。 ∎

## 定理 17.4（φ-有理数的可数稠密性）
φ-有理数在φ-实数中是可数稠密的：

$$\overline{\iota(\mathbb{F}\mathbb{Q})}^{\mathbb{F}\mathbb{R}} = \mathbb{F}\mathbb{R}$$

其中 $\overline{A}^{\mathbb{F}\mathbb{R}}$ 表示集合 $A$ 在φ-实数拓扑中的闭包。

**证明：**
需证明每个φ-实数都是φ-有理数序列的极限。

设 $x \in \mathbb{F}\mathbb{R}$，由φ-实数的构造，$x$ 可表示为φ-有理数Cauchy序列 $(r_n)$ 的等价类。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $N \in \mathbb{F}\mathbb{N}$ 使得：
$$d_{\mathbb{F}\mathbb{R}}(x, \iota(r_n)) \prec_{\mathbb{F}\mathbb{R}} \iota(\varepsilon) \quad \text{对所有 } n \succ_{\mathbb{F}\mathbb{N}} N$$

因此 $x = \lim_{n \to \infty} \iota(r_n)$，即 $x \in \overline{\iota(\mathbb{F}\mathbb{Q})}^{\mathbb{F}\mathbb{R}}$。 ∎

## 定理 17.5（φ-有理数稠密性的等价刻画）
以下条件等价：

1. φ-有理数在φ-实数中稠密
2. 每个非空φ-实数开区间都包含φ-有理数
3. 每个φ-实数都是φ-有理数序列的极限
4. $\mathbb{F}\mathbb{Q}$ 在φ-实数序拓扑中稠密

**证明：**
**(1) ⇒ (2)**：由定理18.3直接得出。

**(2) ⇒ (3)**：设 $x \in \mathbb{F}\mathbb{R}$。对每个 $n \in \mathbb{F}\mathbb{N}$，开区间 $(x \ominus_{\mathbb{F}\mathbb{R}} \frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{n}, x \oplus_{\mathbb{F}\mathbb{R}} \frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{n})_{\mathbb{F}\mathbb{R}}$ 包含φ-有理数 $r_n$。
序列 $(r_n)$ 收敛到 $x$。

**(3) ⇒ (4)**：每个φ-实数都是φ-有理数的极限点，故 $\overline{\mathbb{F}\mathbb{Q}} = \mathbb{F}\mathbb{R}$。

**(4) ⇒ (1)**：稠密性的定义。 ∎

## 推论 17.1（φ-无理数的存在性）
φ-实数中存在φ-无理数，即 $\mathbb{F}\mathbb{R} \setminus \mathbb{F}\mathbb{Q} \neq \emptyset$。

**证明：**
若 $\mathbb{F}\mathbb{R} = \mathbb{F}\mathbb{Q}$，则φ-有理数既是可数集又是完备度量空间。

但由贝尔纲定理，完备度量空间不能是可数集（当空间无孤立点时）。

由定理18.4，φ-实数无孤立点，因此必有 $\mathbb{F}\mathbb{R} \supsetneq \mathbb{F}\mathbb{Q}$。 ∎

## 定理 17.6（φ-有理数稠密性的计算特征）
φ-有理数的稠密性可通过以下算法验证：

**稠密性算法**：
输入：φ-实数 $x \in \mathbb{F}\mathbb{R}$ 和精度 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$
输出：φ-有理数 $r \in \mathbb{F}\mathbb{Q}$ 使得 $d_{\mathbb{F}\mathbb{R}}(x, \iota(r)) \prec_{\mathbb{F}\mathbb{R}} \iota(\varepsilon)$

1. **序列逼近**：取φ-实数 $x$ 的φ-有理数Cauchy序列 $(r_n)$
2. **精度选择**：选择 $N$ 使得序列的Cauchy条件满足精度要求
3. **有理数提取**：返回 $r = r_N$

**证明：**
算法的正确性由φ-实数作为φ-有理数Cauchy序列等价类的构造保证。 ∎

## 定理 17.7（φ-有理数逼近的收敛速度）
对φ-实数 $x \in \mathbb{F}\mathbb{R}$，存在φ-有理数序列 $(r_n)$ 使得：

$$d_{\mathbb{F}\mathbb{R}}(x, \iota(r_n)) \preceq_{\mathbb{F}\mathbb{R}} \iota\left(\frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{n}\right)$$

对所有 $n \in \mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{N}}\}$。

**证明：**
由φ-有理数的阿基米德性质（定理15.1），对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $n \in \mathbb{F}\mathbb{N}$ 使得 $\frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{n} \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$。

结合定理18.6的稠密性算法，可构造满足收敛速度要求的φ-有理数序列。 ∎

## 定理 17.8（φ-有理数的一致稠密性）
φ-有理数在任意有界φ-实数区间中一致稠密：

对任意有界闭区间 $[a, b]_{\mathbb{F}\mathbb{R}} = \{x \in \mathbb{F}\mathbb{R} : a \preceq_{\mathbb{F}\mathbb{R}} x \preceq_{\mathbb{F}\mathbb{R}} b\}$ 和任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在有限φ-有理数集合 $\{r_1, r_2, \ldots, r_k\} \subset \mathbb{F}\mathbb{Q}$ 使得：

$$[a, b]_{\mathbb{F}\mathbb{R}} \subseteq \bigcup_{i=1}^k U_\varepsilon(r_i)$$

**证明：**
由φ-实数区间的紧致性（当构造完成后）和φ-有理数的稠密性，任意有界闭区间都可以用有限个φ-有理数邻域覆盖。

具体构造：选择 $r_i = a \oplus_{\mathbb{F}\mathbb{R}} i \otimes_{\mathbb{F}\mathbb{R}} \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$ 其中 $i$ 取适当的φ-自然数值。 ∎

## 引理 17.3（φ-无理数的构造示例）
存在具体的φ-无理数构造方法：

**φ-平方根构造**：设 $n \in \mathbb{F}\mathbb{N}$ 非完全平方数，则φ-Cauchy序列：
$$r_k = \text{最佳φ-有理数逼近} \sqrt[φ]{n}_k$$

的极限定义了φ-无理数 $\sqrt[φ]{n}$。

**φ-无穷小数构造**：φ-十进制（或φ-进制）无穷小数：
$$x = \sum_{k=\mathbf{0}_{\mathbb{F}\mathbb{Z}}}^{\infty} \frac{a_k}{\mathbf{10}_{\mathbb{F}\mathbb{Q}}^k}$$

其中系数序列 $(a_k)$ 非最终周期，定义φ-无理数。

**证明：**
构造的序列满足φ-Cauchy条件但不收敛到任何φ-有理数，因此定义了φ-无理数。 ∎

## 推论 17.2（φ-有理数稠密性的拓扑后果）
φ-有理数的稠密性导致以下拓扑性质：

1. **分离性**：不同的φ-实数可以用φ-有理数邻域分离
2. **连通性**：φ-实数线是连通的拓扑空间
3. **完备性缺失**：φ-有理数本身不是完备的度量空间
4. **可数基**：φ-有理数开区间构成φ-实数拓扑的可数基

**证明：**
所有性质都是一般拓扑学中稠密可数子空间的标准后果，在φ-数系中的对应。 ∎

## 定理 17.9（φ-有理数稠密性与同构的兼容性）
φ-有理数的稠密性与域同构 $\eta: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 兼容：

标准有理数在标准实数中的稠密性通过扩展同构对应于φ-有理数在φ-实数中的稠密性。

设 $\tilde{\eta}: \mathbb{F}\mathbb{R} \to \mathbb{R}$ 为φ-实数到标准实数的扩展同构，则：
$$\tilde{\eta}(\overline{\iota(\mathbb{F}\mathbb{Q})}^{\mathbb{F}\mathbb{R}}) = \overline{\eta(\mathbb{F}\mathbb{Q})}^{\mathbb{R}} = \mathbb{R}$$

**证明：**
同构映射保持拓扑结构，特别是保持稠密性和闭包运算。
因此φ-有理数的稠密性与标准有理数的稠密性通过同构一一对应。 ∎

## 推论 17.3（φ-数系稠密性理论的完备性）
φ-有理数稠密性理论实现了与标准实分析稠密性理论的完全对应：

1. **稠密性定义**：φ-有理数在φ-实数中的稠密性与标准情形等价
2. **拓扑后果**：所有拓扑性质都通过同构保持
3. **逼近理论**：φ-有理数逼近算法与标准逼近算法等价
4. **分析基础**：为φ-实分析提供了完整的有理数基础

这为构建完整的φ-实数分析理论奠定了稠密性基础。

**证明：**
所有性质由定理18.1-18.9综合得出，特别是同构性（定理18.9）保证了理论的完备性。 ∎