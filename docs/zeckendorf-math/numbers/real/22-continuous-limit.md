# φ-连续性与极限理论

## 定义 22.1（φ-函数极限）
设 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 为函数，$a, L \in \mathbb{F}\mathbb{R}$。称 $f$ 在 $a$ 处的**φ-极限**为 $L$，记作：
$$\lim_{x \to a} f(x) = L$$

当且仅当对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，存在 $\delta \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得：
$$\mathbf{0}_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta \Rightarrow d_{\mathbb{F}\mathbb{R}}(f(x), L) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$$

## 定理 22.1（φ-函数极限的唯一性）
若φ-函数极限存在，则极限唯一。

**证明：**
设 $\lim_{x \to a} f(x) = L_1$ 且 $\lim_{x \to a} f(x) = L_2$。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，取 $\delta_1, \delta_2$ 使得：
- 当 $\mathbf{0}_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta_1$ 时，$d_{\mathbb{F}\mathbb{R}}(f(x), L_1) \prec_{\mathbb{F}\mathbb{R}} \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{R}}}$
- 当 $\mathbf{0}_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta_2$ 时，$d_{\mathbb{F}\mathbb{R}}(f(x), L_2) \prec_{\mathbb{F}\mathbb{R}} \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{R}}}$

取 $\delta = \min_{\mathbb{F}\mathbb{R}}(\delta_1, \delta_2)$，选择 $x$ 满足 $\mathbf{0}_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta$。

由三角不等式：
$$d_{\mathbb{F}\mathbb{R}}(L_1, L_2) \preceq_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(L_1, f(x)) \oplus_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(f(x), L_2) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$$

由 $\varepsilon$ 的任意性，$L_1 = L_2$。 ∎

## 定义 22.2（φ-函数的连续性等价定义）
函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 在点 $a \in \mathbb{F}\mathbb{R}$ **连续**，当且仅当以下等价条件之一成立：

1. **ε-δ定义**：对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，存在 $\delta \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得
   $$d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta \Rightarrow d_{\mathbb{F}\mathbb{R}}(f(x), f(a)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$$

2. **极限定义**：$\lim_{x \to a} f(x) = f(a)$

3. **序列定义**：对任意序列 $(x_n) \to a$，有 $(f(x_n)) \to f(a)$

## 定理 22.2（φ-连续性定义的等价性）
定义22.2中的三个条件等价。

**证明：**
**$(1) \Rightarrow (2)$**：取 $L = f(a)$ 在ε-δ定义中即得极限定义。

**$(2) \Rightarrow (3)$**：设 $(x_n) \to a$ 且 $\lim_{x \to a} f(x) = f(a)$。
对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，由极限定义存在 $\delta$。
由 $(x_n) \to a$，存在 $N$ 使得对 $n \succ_{\mathbb{F}\mathbb{N}} N$：$d_{\mathbb{F}\mathbb{R}}(x_n, a) \prec_{\mathbb{F}\mathbb{R}} \delta$。
故 $d_{\mathbb{F}\mathbb{R}}(f(x_n), f(a)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$，即 $(f(x_n)) \to f(a)$。

**$(3) \Rightarrow (1)$**：反证法。若ε-δ定义不成立，存在 $\varepsilon_0$ 使得对任意 $\delta$，
存在 $x$ 满足 $d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta$ 但 $d_{\mathbb{F}\mathbb{R}}(f(x), f(a)) \succeq_{\mathbb{F}\mathbb{R}} \varepsilon_0$。

构造序列 $(x_n)$ 其中 $d_{\mathbb{F}\mathbb{R}}(x_n, a) \prec_{\mathbb{F}\mathbb{R}} \frac{\mathbf{1}_{\mathbb{F}\mathbb{R}}}{n}$ 但 $d_{\mathbb{F}\mathbb{R}}(f(x_n), f(a)) \succeq_{\mathbb{F}\mathbb{R}} \varepsilon_0$。
则 $(x_n) \to a$ 但 $(f(x_n)) \not\to f(a)$，与条件3矛盾。 ∎

## 定理 22.3（φ-连续函数的运算性质）
设 $f, g: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 在点 $a$ 连续，$c \in \mathbb{F}\mathbb{R}$，则：

1. **线性组合**：$c \odot_{\mathbb{F}\mathbb{R}} f \oplus_{\mathbb{F}\mathbb{R}} g$ 在 $a$ 连续
2. **乘积**：$f \otimes_{\mathbb{F}\mathbb{R}} g$ 在 $a$ 连续
3. **商**：若 $g(a) \neq \mathbf{0}_{\mathbb{F}\mathbb{R}}$，则 $\frac{f}{g}$ 在 $a$ 连续
4. **复合**：若 $g$ 在 $a$ 连续，$f$ 在 $g(a)$ 连续，则 $f \circ g$ 在 $a$ 连续

**证明：**
所有性质都由φ-实数运算的连续性（定理17.10扩展到实数）和极限运算律得出。

**乘积连续性**：设 $(x_n) \to a$，需证明 $(f(x_n) \otimes_{\mathbb{F}\mathbb{R}} g(x_n)) \to f(a) \otimes_{\mathbb{F}\mathbb{R}} g(a)$。

由 $f, g$ 的连续性：$(f(x_n)) \to f(a)$，$(g(x_n)) \to g(a)$。
由φ-实数乘法的连续性：$(f(x_n) \otimes_{\mathbb{F}\mathbb{R}} g(x_n)) \to f(a) \otimes_{\mathbb{F}\mathbb{R}} g(a)$。

其他运算的连续性类似证明。 ∎

## 定义 22.3（φ-一致连续性）
函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 在集合 $S \subseteq \mathbb{F}\mathbb{R}$ 上**一致连续**，当且仅当：

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，存在 $\delta \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得对所有 $x, y \in S$：
$$d_{\mathbb{F}\mathbb{R}}(x, y) \prec_{\mathbb{F}\mathbb{R}} \delta \Rightarrow d_{\mathbb{F}\mathbb{R}}(f(x), f(y)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$$

## 定理 22.4（紧致集上的一致连续性）
在φ-实数的紧致子集上，每个连续函数都一致连续。

**证明：**
设 $K \subseteq \mathbb{F}\mathbb{R}$ 紧致，$f: K \to \mathbb{F}\mathbb{R}$ 连续。

反证法：假设 $f$ 在 $K$ 上不一致连续。
则存在 $\varepsilon_0 \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得对任意 $n \in \mathbb{F}\mathbb{N}$，
存在 $x_n, y_n \in K$ 满足：
$$d_{\mathbb{F}\mathbb{R}}(x_n, y_n) \prec_{\mathbb{F}\mathbb{R}} \frac{\mathbf{1}_{\mathbb{F}\mathbb{R}}}{n} \text{ 但 } d_{\mathbb{F}\mathbb{R}}(f(x_n), f(y_n)) \succeq_{\mathbb{F}\mathbb{R}} \varepsilon_0$$

由 $K$ 的紧致性，序列 $(x_n)$ 有收敛子序列 $(x_{n_k}) \to x_0 \in K$。
由于 $d_{\mathbb{F}\mathbb{R}}(x_{n_k}, y_{n_k}) \to \mathbf{0}_{\mathbb{F}\mathbb{R}}$，有 $(y_{n_k}) \to x_0$。

由 $f$ 在 $x_0$ 的连续性：$(f(x_{n_k})) \to f(x_0)$ 且 $(f(y_{n_k})) \to f(x_0)$。
因此 $d_{\mathbb{F}\mathbb{R}}(f(x_{n_k}), f(y_{n_k})) \to \mathbf{0}_{\mathbb{F}\mathbb{R}}$，与 $d_{\mathbb{F}\mathbb{R}}(f(x_n), f(y_n)) \succeq_{\mathbb{F}\mathbb{R}} \varepsilon_0$ 矛盾。 ∎

## 定义 22.4（φ-Lipschitz连续性）
函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 称为**φ-Lipschitz连续**，当且仅当存在常数 $L \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得：
$$d_{\mathbb{F}\mathbb{R}}(f(x), f(y)) \preceq_{\mathbb{F}\mathbb{R}} L \otimes_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(x, y) \quad \forall x, y \in \mathbb{F}\mathbb{R}$$

常数 $L$ 称为**φ-Lipschitz常数**。

## 定理 22.5（φ-Lipschitz连续性蕴含一致连续性）
φ-Lipschitz连续函数在 $\mathbb{F}\mathbb{R}$ 上一致连续。

**证明：**
设 $f$ 为φ-Lipschitz连续，Lipschitz常数为 $L$。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，取 $\delta = \frac{\varepsilon}{L}$。

对任意 $x, y \in \mathbb{F}\mathbb{R}$ 满足 $d_{\mathbb{F}\mathbb{R}}(x, y) \prec_{\mathbb{F}\mathbb{R}} \delta$：
$$d_{\mathbb{F}\mathbb{R}}(f(x), f(y)) \preceq_{\mathbb{F}\mathbb{R}} L \otimes_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(x, y) \prec_{\mathbb{F}\mathbb{R}} L \otimes_{\mathbb{F}\mathbb{R}} \frac{\varepsilon}{L} = \varepsilon$$

故 $f$ 一致连续。 ∎

## 定义 22.5（φ-序列的函数极限）
对函数序列 $(f_n: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R})_{n \in \mathbb{F}\mathbb{N}}$ 和函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$：

**逐点收敛**：$(f_n) \to f$ 逐点，当且仅当对每个 $x \in \mathbb{F}\mathbb{R}$：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} f_n(x) = f(x)$$

**一致收敛**：$(f_n) \to f$ 一致，当且仅当：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} \sup_{x \in \mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(f_n(x), f(x)) = \mathbf{0}_{\mathbb{F}\mathbb{R}}$$

## 定理 22.6（一致收敛连续函数序列的连续性）
若连续函数序列 $(f_n)$ 一致收敛到 $f$，则 $f$ 连续。

**证明：**
设 $(f_n)$ 为连续函数序列且 $(f_n) \to f$ 一致，需证明 $f$ 在任意点 $a$ 连续。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，取 $\varepsilon_1 = \frac{\varepsilon}{\mathbf{3}_{\mathbb{F}\mathbb{R}}}$。

**步骤1**：由一致收敛性，存在 $N$ 使得对所有 $x \in \mathbb{F}\mathbb{R}$ 和 $n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{R}}(f_n(x), f(x)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon_1$$

**步骤2**：由 $f_N$ 在 $a$ 的连续性，存在 $\delta \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得：
$$d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta \Rightarrow d_{\mathbb{F}\mathbb{R}}(f_N(x), f_N(a)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon_1$$

**步骤3**：对 $d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta$，由三角不等式：
$$d_{\mathbb{F}\mathbb{R}}(f(x), f(a)) \preceq_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(f(x), f_N(x)) \oplus_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(f_N(x), f_N(a)) \oplus_{\mathbb{F}\mathbb{R}} d_{\mathbb{F}\mathbb{R}}(f_N(a), f(a)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$$

故 $f$ 在 $a$ 连续。 ∎

## 定理 22.7（φ-单调函数的连续性刻画）
单调函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 的不连续点构成至多可数集。

**证明：**
设 $f$ 单调非减。对每个不连续点 $a$，定义**跳跃**：
$$\text{jump}(a) = \lim_{x \to a^+} f(x) \ominus_{\mathbb{F}\mathbb{R}} \lim_{x \to a^-} f(x)$$

由单调性，左右极限都存在，且 $\text{jump}(a) \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$。

由于 $f$ 值域有界（在任意有界区间上），不同不连续点的跳跃不相交。
因此不连续点至多可数。 ∎

## 定义 22.6（φ-导数的极限定义）
函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 在点 $a$ 的**φ-导数**定义为：
$$f'(a) = \lim_{h \to \mathbf{0}_{\mathbb{F}\mathbb{R}}} \frac{f(a \oplus_{\mathbb{F}\mathbb{R}} h) \ominus_{\mathbb{F}\mathbb{R}} f(a)}{h}$$

当此极限存在时，称 $f$ 在 $a$ **φ-可导**。

## 定理 22.8（φ-可导性蕴含连续性）
若函数 $f$ 在点 $a$ φ-可导，则 $f$ 在 $a$ 连续。

**证明：**
设 $f'(a)$ 存在。对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，

由导数定义，存在 $\delta_1 \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 使得当 $\mathbf{0}_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} |h|_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} \delta_1$ 时：
$$\left|\frac{f(a \oplus_{\mathbb{F}\mathbb{R}} h) \ominus_{\mathbb{F}\mathbb{R}} f(a)}{h} \ominus_{\mathbb{F}\mathbb{R}} f'(a)\right|_{\mathbb{F}\mathbb{R}} \prec_{\mathbb{F}\mathbb{R}} \mathbf{1}_{\mathbb{F}\mathbb{R}}$$

因此：
$$|f(a \oplus_{\mathbb{F}\mathbb{R}} h) \ominus_{\mathbb{F}\mathbb{R}} f(a)|_{\mathbb{F}\mathbb{R}} \preceq_{\mathbb{F}\mathbb{R}} (|f'(a)|_{\mathbb{F}\mathbb{R}} \oplus_{\mathbb{F}\mathbb{R}} \mathbf{1}_{\mathbb{F}\mathbb{R}}) \otimes_{\mathbb{F}\mathbb{R}} |h|_{\mathbb{F}\mathbb{R}}$$

取 $\delta = \min_{\mathbb{F}\mathbb{R}}\left(\delta_1, \frac{\varepsilon}{|f'(a)|_{\mathbb{F}\mathbb{R}} \oplus_{\mathbb{F}\mathbb{R}} \mathbf{1}_{\mathbb{F}\mathbb{R}}}\right)$，
当 $d_{\mathbb{F}\mathbb{R}}(x, a) \prec_{\mathbb{F}\mathbb{R}} \delta$ 时，$d_{\mathbb{F}\mathbb{R}}(f(x), f(a)) \prec_{\mathbb{F}\mathbb{R}} \varepsilon$。 ∎

## 定理 22.9（φ-Mean Value定理）
设 $f: [a, b]_{\mathbb{F}\mathbb{R}} \to \mathbb{F}\mathbb{R}$ 在 $[a, b]_{\mathbb{F}\mathbb{R}}$ 连续，在 $(a, b)_{\mathbb{F}\mathbb{R}}$ 可导，
则存在 $c \in (a, b)_{\mathbb{F}\mathbb{R}}$ 使得：
$$f'(c) = \frac{f(b) \ominus_{\mathbb{F}\mathbb{R}} f(a)}{b \ominus_{\mathbb{F}\mathbb{R}} a}$$

**证明：**
定义辅助函数：
$$g(x) = f(x) \ominus_{\mathbb{F}\mathbb{R}} f(a) \ominus_{\mathbb{F}\mathbb{R}} \frac{f(b) \ominus_{\mathbb{F}\mathbb{R}} f(a)}{b \ominus_{\mathbb{F}\mathbb{R}} a} \otimes_{\mathbb{F}\mathbb{R}} (x \ominus_{\mathbb{F}\mathbb{R}} a)$$

$g$ 在 $[a, b]_{\mathbb{F}\mathbb{R}}$ 连续，在 $(a, b)_{\mathbb{F}\mathbb{R}}$ 可导，且 $g(a) = g(b) = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。

由Rolle定理（φ-版本），存在 $c \in (a, b)_{\mathbb{F}\mathbb{R}}$ 使得 $g'(c) = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。

计算得：$g'(c) = f'(c) \ominus_{\mathbb{F}\mathbb{R}} \frac{f(b) \ominus_{\mathbb{F}\mathbb{R}} f(a)}{b \ominus_{\mathbb{F}\mathbb{R}} a} = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。

因此结论成立。 ∎

## 定义 22.7（φ-函数的上半连续性和下半连续性）
函数 $f: \mathbb{F}\mathbb{R} \to \mathbb{F}\mathbb{R}$ 在点 $a$ **上半连续**，当且仅当：
$$\limsup_{x \to a} f(x) \preceq_{\mathbb{F}\mathbb{R}} f(a)$$

函数 $f$ 在点 $a$ **下半连续**，当且仅当：
$$\liminf_{x \to a} f(x) \succeq_{\mathbb{F}\mathbb{R}} f(a)$$

## 定理 22.10（φ-半连续性与连续性的关系）
函数 $f$ 在点 $a$ 连续当且仅当它既上半连续又下半连续。

**证明：**
**必要性**：若 $f$ 在 $a$ 连续，则 $\lim_{x \to a} f(x) = f(a)$。
由极限的定义，$\limsup_{x \to a} f(x) = \liminf_{x \to a} f(x) = f(a)$。

**充分性**：若 $f$ 既上半连续又下半连续，则：
$$f(a) \preceq_{\mathbb{F}\mathbb{R}} \liminf_{x \to a} f(x) \preceq_{\mathbb{F}\mathbb{R}} \limsup_{x \to a} f(x) \preceq_{\mathbb{F}\mathbb{R}} f(a)$$

因此 $\liminf_{x \to a} f(x) = \limsup_{x \to a} f(x) = f(a)$，即 $\lim_{x \to a} f(x) = f(a)$。 ∎

## 定理 22.11（φ-极值的存在性）
紧致集 $K \subseteq \mathbb{F}\mathbb{R}$ 上的连续函数 $f: K \to \mathbb{F}\mathbb{R}$ 达到最大值和最小值。

**证明：**
由紧致性，$f(K)$ 为φ-实数中的紧致子集，故有界闭。

由序完备性（定理20.2），$f(K)$ 有上确界和下确界：
$$\sup f(K), \inf f(K) \in \mathbb{F}\mathbb{R}$$

由于 $f(K)$ 闭，$\sup f(K), \inf f(K) \in f(K)$。

因此存在 $x_{\max}, x_{\min} \in K$ 使得：
$$f(x_{\max}) = \sup f(K), \quad f(x_{\min}) = \inf f(K)$$ 
∎

## 定理 22.12（φ-中间值定理的精确表述）
设 $f: [a, b]_{\mathbb{F}\mathbb{R}} \to \mathbb{F}\mathbb{R}$ 连续。若 $f(a) \prec_{\mathbb{F}\mathbb{R}} c \prec_{\mathbb{F}\mathbb{R}} f(b)$，
则存在 $\xi \in (a, b)_{\mathbb{F}\mathbb{R}}$ 使得 $f(\xi) = c$。

**证明：**
定义集合：
$$S = \{x \in [a, b]_{\mathbb{F}\mathbb{R}} : f(x) \preceq_{\mathbb{F}\mathbb{R}} c\}$$

**步骤1**：$S$ 非空（因为 $a \in S$）且有上界（$b$ 为上界）。

**步骤2**：由序完备性，$\xi = \sup S$ 存在。

**步骤3**：证明 $f(\xi) = c$。

若 $f(\xi) \prec_{\mathbb{F}\mathbb{R}} c$，由连续性存在 $\xi$ 的邻域使得 $f$ 在该邻域内 $\prec_{\mathbb{F}\mathbb{R}} c$，
与 $\xi = \sup S$ 矛盾。

若 $f(\xi) \succ_{\mathbb{F}\mathbb{R}} c$，类似可得矛盾。

因此 $f(\xi) = c$。 ∎

## 推论 22.1（φ-连续极限理论的完备性）
φ-连续性和极限理论实现了与标准实分析完全对应的理论体系：

1. **极限存在性**：φ-函数极限的存在性和唯一性
2. **连续性刻画**：多种等价的连续性定义
3. **运算保持性**：连续函数在运算下的封闭性
4. **一致连续性**：紧致集上的一致连续性定理
5. **中间值性质**：连续函数的中间值定理
6. **极值性质**：紧致集上连续函数的最值存在性
7. **微分联系**：可导性与连续性的关系

这为φ-微积分学和φ-函数理论提供了完整的连续性理论基础。

**证明：**
所有性质都由前述定理22.1-22.12综合得出，特别是通过同构 $\Phi: \mathbb{F}\mathbb{R} \to \mathbb{R}$ 与标准实分析的完全对应保证了理论的完备性。 ∎