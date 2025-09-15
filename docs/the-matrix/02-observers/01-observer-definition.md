# 观察者定义

## 1.1 观察者的数学刻画

**定义 1.1（观察者）**：观察者 $\mathcal{O}$ 是一个三元组 $(I, k, P)$，其中：
- $I \subset \mathbb{N}$ 是其占据的有限行集合
- $k = |I| < \infty$ 是占据的行数
- $P: \mathbb{N} \to I \cup \{\perp\}$ 是预测函数

其中 $P(t)$ 表示对时刻 $t$ 激活位置的预测，$P(t) = \perp$ 表示预测激活在其边界之外。

**定理 1.1（观察者的有限性）**：观察者必须占据有限行数。

*证明*：
1. 若 $k = \infty$，则观察者占据所有行
2. 这违反了观察者的局部性原理
3. 无限观察者无法进行有效预测
4. 因此必须 $k < \infty$

观察者的有限性是其可定义性的前提。$\square$

## 1.2 观察者的基本性质

**定义 1.2（观察者状态）**：观察者 $\mathcal{O}$ 在时刻 $t$ 的状态为：
$$\mathcal{S}_{\mathcal{O}}(t) = \{m_{ij} : i \in I_{\mathcal{O}}, j \leq t\}$$

**定理 1.2（状态的有限性）**：观察者在任意时刻的状态信息有限。

*证明*：
$$|\mathcal{S}_{\mathcal{O}}(t)| = |I_{\mathcal{O}}| \times t = k \times t < \infty$$
因此观察者状态始终有限。$\square$

**定义 1.3（观察者的视野）**：观察者的视野定义为其可观测的矩阵区域：
$$\mathcal{V}_{\mathcal{O}} = \{(i,j) : i \in I_{\mathcal{O}}, j \in \mathbb{N}\}$$

**定理 1.3（视野的局限性）**：观察者只能观测到 The Matrix 的子集。

*证明*：
$$\mathcal{V}_{\mathcal{O}} \subset \mathbb{N} \times \mathbb{N}$$
且由于 $|I_{\mathcal{O}}| = k < \infty$，观察者无法观测到所有行。$\square$

## 1.3 观察者层级

**定义 1.4（观察者层级）**：定义观察者的层级函数：
$$\text{level}(\mathcal{O}) = \log_2(r_k)$$
其中 $r_k$ 是 k-bonacci 递推的特征根。

**定理 1.4（层级的单调性）**：观察者层级随 $k$ 值单调增加。

*证明*：k-bonacci 特征根满足：
- $r_1 = 1$
- $r_2 = \phi = \frac{1+\sqrt{5}}{2} \approx 1.618$
- $r_3 \approx 1.839$
- $\lim_{k \to \infty} r_k = 2$

因此 $\text{level}(\mathcal{O})$ 随 $k$ 单调增加。$\square$

## 1.4 观察者的交互

**定义 1.5（观察者重叠）**：两个观察者 $\mathcal{O}_1, \mathcal{O}_2$ 的重叠度为：
$$\text{overlap}(\mathcal{O}_1, \mathcal{O}_2) = \frac{|I_{\mathcal{O}_1} \cap I_{\mathcal{O}_2}|}{|I_{\mathcal{O}_1} \cup I_{\mathcal{O}_2}|}$$

**定理 1.5（重叠的有界性）**：观察者重叠度在 $[0,1]$ 区间内。

*证明*：
- 当 $I_{\mathcal{O}_1} \cap I_{\mathcal{O}_2} = \emptyset$ 时，$\text{overlap} = 0$
- 当 $I_{\mathcal{O}_1} = I_{\mathcal{O}_2}$ 时，$\text{overlap} = 1$
- 一般情况下，$0 \leq \text{overlap} \leq 1$

$\square$

**定义 1.6（顶层观察者）**：对于行 $i$，定义其顶层观察者为：
$$\mathcal{O}_{\text{top}}(i) = \arg\max_{\mathcal{O}: i \in I_{\mathcal{O}}} \text{level}(\mathcal{O})$$

**定理 1.6（顶层观察者的唯一性）**：每行的顶层观察者在任意时刻唯一确定。

*证明*：
1. 设有两个观察者 $\mathcal{O}_1, \mathcal{O}_2$ 都占据行 $i$
2. 它们的层级要么不同，要么相同
3. 若不同，层级高者为顶层
4. 若相同，系统选择机制确定唯一性

因此顶层观察者唯一。$\square$

## 1.5 观察者的动态性

**定义 1.7（观察者演化）**：观察者可通过以下方式演化：
1. **扩展**：$k \to k + \delta k$，占据新行
2. **收缩**：$k \to k - \delta k$，释放某些行
3. **迁移**：改变占据的行集合，保持 $k$ 不变

**定理 1.7（演化的约束条件）**：观察者演化必须满足：
1. no-k 约束在演化过程中保持
2. 系统总熵不减
3. 激活序列的连续性

*证明*：这些约束确保系统的全局一致性和稳定性。$\square$

**定理 1.8（观察者存在的必要条件）**：观察者存在需要 $k \geq 2$。

*证明*：
- $k = 1$：$r_1 = 1$，无预测复杂度，无法形成有意义的预测
- $k \geq 2$：$r_k > 1$，具有指数增长的预测能力

因此 $k \geq 2$ 是观察者存在的阈值。$\square$