# Zeckendorf基础理论

## 定义 0.1（Fibonacci序列）
定义Fibonacci序列 $(F_n)_{n \geq 1}$ 为：
$$F_1 = 1, \quad F_2 = 2, \quad F_n = F_{n-1} + F_{n-2} \text{ for } n \geq 3$$

## 定义 0.2（φ-编码）
设 $B = \{0,1\}^*$ 为有限二进制串集合。定义**φ-编码**为满足no-11约束的二进制串：
$$\Phi = \{s \in B : s \text{ 不包含子串 } 11\}$$

## 定义 0.3（Zeckendorf分解）
对于正整数 $n \in \mathbb{N}^+$，其**Zeckendorf分解**为：
$$n = \sum_{i=1}^{k} F_{a_i}$$
其中 $a_1 > a_2 > \cdots > a_k \geq 1$ 且 $a_i - a_{i+1} \geq 2$ 对所有 $i$ 成立。

## 定理 0.1（Zeckendorf唯一性定理）
每个正整数 $n \in \mathbb{N}^+$ 具有唯一的Zeckendorf分解。

**证明：** 
存在性：设 $n$ 为正整数。令 $k$ 为最大的指标使得 $F_k \leq n$。由于 $F_1 = 1$，必有 $k \geq 1$。设 $n_1 = n - F_k$。

若 $n_1 = 0$，则 $n = F_k$ 为所需分解。

若 $n_1 > 0$，令 $\ell$ 为最大指标使得 $F_\ell \leq n_1$。由 $F_k$ 的最大性，有 $\ell < k$。

由Fibonacci递推关系 $F_k = F_{k-1} + F_{k-2}$ (当 $k \geq 3$) 和 $n_1 = n - F_k < F_k$，
若 $\ell = k-1$，则：
- 当 $k = 2$ 时，$F_2 = 2, F_1 = 1$，若选择 $F_1$，余量为 $n_1 - F_1 \geq 0$
- 当 $k \geq 3$ 时，$F_{k-1} \leq n_1 < F_k = F_{k-1} + F_{k-2}$，故 $n_1 - F_{k-1} < F_{k-2}$

为保证非连续性，我们要求 $\ell \leq k-2$，满足 $a_i - a_{i+1} \geq 2$ 的约束。

重复此过程直至余项为0，得到Zeckendorf分解。

唯一性：设存在两个不同分解：
$$n = \sum_{i=1}^{r} F_{a_i} = \sum_{j=1}^{s} F_{b_j}$$
其中 $a_1 > a_2 > \cdots > a_r \geq 1$，$b_1 > b_2 > \cdots > b_s \geq 1$，
且满足非连续性约束。

不失一般性，设 $a_1 \geq b_1$。若 $a_1 > b_1$，则由于非连续性：
$$F_{a_1} \geq F_{b_1+2} > F_{b_1} + F_{b_1+1} \geq \sum_{j=1}^{s} F_{b_j}$$
这与两分解相等矛盾。故 $a_1 = b_1$。

类似地可证明 $a_i = b_i$ 对所有 $i$ 成立，从而 $r = s$ 且两分解相同。 ∎

## 定义 0.4（编码映射）
定义映射 $\text{encode}: \mathbb{N}^+ \to \Phi \setminus \{\varepsilon\}$ 如下：

对于 $n \in \mathbb{N}^+$ 的Zeckendorf分解 $n = \sum_{i=1}^{k} F_{a_i}$，
设 $m = \max\{a_i : i = 1,\ldots,k\}$，定义长度为 $m$ 的二进制串：
$$\text{encode}(n) = b_m b_{m-1} \cdots b_1$$
其中 $b_j = 1$ 当且仅当 $F_j$ 出现在分解中（即存在 $i$ 使得 $a_i = j$）。

## 定义 0.5（解码映射）
定义映射 $\text{decode}: \Phi \to \mathbb{N}$ 如下：

对于 $s = b_k b_{k-1} \cdots b_1 \in \Phi$，定义：
$$\text{decode}(s) = \sum_{i=1}^{k} b_i \cdot F_i$$

特别地，$\text{decode}(\varepsilon) = 0$，其中 $\varepsilon$ 为空串。

## 引理 0.1（编码保持no-11约束）
对于任意 $n \in \mathbb{N}^+$，$\text{encode}(n) \in \Phi$。

**证明：** 
设 $n$ 的Zeckendorf分解为 $n = \sum_{i=1}^{k} F_{a_i}$，其中 $a_1 > a_2 > \cdots > a_k \geq 1$
且 $a_i - a_{i+1} \geq 2$。

在编码 $\text{encode}(n) = b_m \cdots b_1$ 中，$b_j = 1$ 当且仅当 $F_j$ 出现在分解中。

若存在连续的1，即 $b_j = b_{j-1} = 1$，则 $F_j$ 和 $F_{j-1}$ 都出现在分解中。
这意味着存在 $a_i = j$ 和 $a_\ell = j-1$，与非连续性约束 $a_i - a_\ell \geq 2$ 矛盾。

因此 $\text{encode}(n)$ 不包含子串11，即 $\text{encode}(n) \in \Phi$。 ∎

## 定理 0.2（双射定理）
映射 $\text{encode}: \mathbb{N}^+ \to \Phi \setminus \{\varepsilon\}$ 与 $\text{decode}: \Phi \setminus \{\varepsilon\} \to \mathbb{N}^+$ 
构成双射，且互为逆映射。

**证明：** 
首先证明 $\text{decode} \circ \text{encode} = \text{id}_{\mathbb{N}^+}$：

设 $n \in \mathbb{N}^+$ 的Zeckendorf分解为 $n = \sum_{i=1}^{k} F_{a_i}$。
令 $s = \text{encode}(n) = b_m \cdots b_1$，其中 $b_j = 1$ 当且仅当 $F_j$ 出现在分解中。

则：
$$\text{decode}(s) = \sum_{j=1}^{m} b_j \cdot F_j = \sum_{\{j: b_j=1\}} F_j = \sum_{i=1}^{k} F_{a_i} = n$$

接下来证明 $\text{encode} \circ \text{decode} = \text{id}_{\Phi \setminus \{\varepsilon\}}$：

设 $s = b_k b_{k-1} \cdots b_1 \in \Phi \setminus \{\varepsilon\}$。由于 $s \neq \varepsilon$，存在某个 $b_i = 1$。

令 $n = \text{decode}(s) = \sum_{i=1}^{k} b_i \cdot F_i$。

需证明此表示为Zeckendorf分解：设 $I = \{i : b_i = 1\}$，则 $n = \sum_{i \in I} F_i$。

由于 $s \in \Phi$，不存在连续的1，即不存在相邻的 $i, i-1 \in I$，否则 $b_i = b_{i-1} = 1$，与no-11约束矛盾。
因此对任意 $i, j \in I$ 且 $i > j$，有 $i - j \geq 2$。

这表明 $\{i : i \in I\}$ 中的元素满足非连续性约束，故 $n = \sum_{i \in I} F_i$ 为Zeckendorf分解。

设此分解中的指标按降序排列为 $a_1 > a_2 > \cdots > a_r$，其中 $\{a_1, \ldots, a_r\} = I$。

在编码过程中，$\text{encode}(n)$ 的第 $j$ 位为1当且仅当 $F_j$ 出现在分解中，
即当且仅当 $j \in I$，即当且仅当 $b_j = 1$。

因此 $\text{encode}(n) = s$。 ∎

## 推论 0.1（φ-自然数）
定义 **φ-自然数集合** $\mathbb{F}\mathbb{N} = \Phi$，则存在双射：
$$\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$$
其中 $\psi(0) = \varepsilon$ 且 $\psi(n) = \text{encode}(n)$ 对 $n \geq 1$。

## 定理 0.3（Fibonacci计数）
对于每个 $k \geq 0$，长度恰好为 $k$ 的φ-编码串的数量为 $F_{k+1}$。

**证明：** 
设 $a_k$ 为长度为 $k$ 的φ-编码串数量。

对于 $k = 0$：只有空串 $\varepsilon$，故 $a_0 = 1 = F_1$。

对于 $k = 1$：可能的串为 $0, 1$，都满足no-11约束，故 $a_1 = 2 = F_2$。

对于 $k \geq 2$：设 $s$ 为长度为 $k$ 的φ-编码串。

情况1：若 $s$ 以0开头，则 $s = 0s'$，其中 $s'$ 为长度为 $k-1$ 的φ-编码串。
此类串有 $a_{k-1}$ 个。

情况2：若 $s$ 以1开头，则 $s = 1s'$，其中 $s'$ 为长度为 $k-1$ 的φ-编码串且 $s'$ 不以1开头。
等价地，$s' = 0s''$，其中 $s''$ 为长度为 $k-2$ 的φ-编码串。
此类串有 $a_{k-2}$ 个。

由于这两种情况互斥且穷尽所有可能，得到递推关系：
$$a_k = a_{k-1} + a_{k-2}$$

结合初始条件 $a_0 = F_1, a_1 = F_2$ 和递推关系，得到 $a_k = F_{k+1}$。 ∎