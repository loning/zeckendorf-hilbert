# 子矩阵结构

## 2.1 子矩阵的定义

**定义 2.1（子矩阵）**：观察者 $\mathcal{O}$ 对应的子矩阵为：
$$\mathcal{S}_{\mathcal{O}} = (m_{ij})_{i \in I_{\mathcal{O}}, j \in \mathbb{N}}$$

其中 $I_{\mathcal{O}} = \{i_1, i_2, ..., i_k\}$ 是观察者占据的行集合。

**定理 2.1（子矩阵的继承性）**：子矩阵继承 The Matrix 的所有约束条件。

*证明*：
1. **单点激活约束**：子矩阵中每列最多有一个 1
2. **no-k 约束**：子矩阵不能有连续 k 个激活
3. **熵增约束**：子矩阵的熵贡献系统总熵

子矩阵是 The Matrix 的真子集，自然继承所有性质。$\square$

## 2.2 子矩阵的激活模式

**定义 2.2（子矩阵激活序列）**：对于观察者 $\mathcal{O}$，定义其激活序列：
$$\sigma_{\mathcal{O}}(j) = \begin{cases}
i & \text{若 } m_{ij} = 1 \text{ 且 } i \in I_{\mathcal{O}} \\
\perp & \text{若 } s_j \notin I_{\mathcal{O}}
\end{cases}$$

**定理 2.2（激活序列的稀疏性）**：观察者的激活序列是稀疏的。

*证明*：
1. 由单点激活约束，每时刻最多一个激活
2. 由 no-k 约束，不能有连续 k 个激活在 $I_{\mathcal{O}}$ 内
3. 因此激活密度 $\rho = \lim_{T \to \infty} \frac{|\{j \leq T : \sigma_{\mathcal{O}}(j) \neq \perp\}|}{T} < 1$

激活序列具有天然的稀疏性。$\square$

**定义 2.3（激活频率谱）**：观察者 $\mathcal{O}$ 的激活频率谱为：
$$f_{i_j} = \lim_{T \to \infty} \frac{1}{T} \sum_{t=1}^{T} \mathbb{1}[s_t = i_j], \quad i_j \in I_{\mathcal{O}}$$

**定理 2.3（频率谱的归一化）**：激活频率谱满足：
$$\sum_{i \in I_{\mathcal{O}}} f_i \leq 1$$

*证明*：由于全局激活频率归一化：$\sum_{i=1}^{\infty} f_i = 1$，子集的频率和不超过 1。$\square$

## 2.3 子矩阵的几何性质

**定义 2.4（子矩阵维度）**：子矩阵 $\mathcal{S}_{\mathcal{O}}$ 的维度为 $k \times \infty$。

**定理 2.4（维度的有限性）**：子矩阵在行维度上有限，在列维度上无限。

*证明*：
- 行维度：$k = |I_{\mathcal{O}}| < \infty$
- 列维度：时间无限延伸，$j \in \mathbb{N}$

这创造了"有限×无限"的混合结构。$\square$

**定义 2.5（子矩阵的拓扑）**：定义子矩阵的拓扑结构：
- **行拓扑**：$I_{\mathcal{O}}$ 继承 $\mathbb{N}$ 的离散拓扑
- **列拓扑**：时间轴的自然序拓扑

**定理 2.5（拓扑的可分性）**：子矩阵的拓扑空间是可分的。

*证明*：
1. 行空间有限，自然可分
2. 列空间 $\mathbb{N}$ 可数，因此可分
3. 乘积拓扑保持可分性

子矩阵具有良好的拓扑性质。$\square$

## 2.4 子矩阵的嵌套结构

**定义 2.6（子矩阵包含关系）**：若 $I_{\mathcal{O}_1} \subset I_{\mathcal{O}_2}$，则称 $\mathcal{S}_{\mathcal{O}_1}$ 嵌套在 $\mathcal{S}_{\mathcal{O}_2}$ 中：
$$\mathcal{S}_{\mathcal{O}_1} \subseteq \mathcal{S}_{\mathcal{O}_2}$$

**定理 2.6（嵌套的传递性）**：子矩阵的嵌套关系具有传递性。

*证明*：若 $\mathcal{S}_{\mathcal{O}_1} \subseteq \mathcal{S}_{\mathcal{O}_2}$ 且 $\mathcal{S}_{\mathcal{O}_2} \subseteq \mathcal{S}_{\mathcal{O}_3}$，则：
$$I_{\mathcal{O}_1} \subseteq I_{\mathcal{O}_2} \subseteq I_{\mathcal{O}_3}$$
因此 $\mathcal{S}_{\mathcal{O}_1} \subseteq \mathcal{S}_{\mathcal{O}_3}$。$\square$

**定义 2.7（嵌套层级）**：定义观察者的嵌套层级：
$$\text{nest\_level}(\mathcal{O}) = \max\{n : \exists \mathcal{O}_1, ..., \mathcal{O}_n, \mathcal{S}_{\mathcal{O}} \subseteq \mathcal{S}_{\mathcal{O}_1} \subseteq ... \subseteq \mathcal{S}_{\mathcal{O}_n}\}$$

**定理 2.7（嵌套层级的有界性）**：在给定时刻，嵌套层级有上界。

*证明*：
1. 最大观察者至多占据所有已激活行
2. 已激活行数在任意时刻有限
3. 因此嵌套层级有上界

但随时间演化，上界可以增长。$\square$

## 2.5 子矩阵的信息容量

**定义 2.8（子矩阵信息容量）**：观察者 $\mathcal{O}$ 的信息容量为：
$$C_{\mathcal{O}} = k \log_2(r_k)$$

其中 $k$ 是行数，$r_k$ 是对应的特征根。

**定理 2.8（容量的单调性）**：信息容量随 $k$ 单调增加。

*证明*：
$$\frac{dC}{dk} = \log_2(r_k) + k \frac{d\log_2(r_k)}{dk} > 0$$

因为 $r_k > 1$ 且 $\frac{dr_k}{dk} > 0$。$\square$

**定理 2.9（容量的上界）**：信息容量有理论上界：
$$\lim_{k \to \infty} \frac{C_{\mathcal{O}}}{k} = \log_2(2) = 1$$

*证明*：由于 $\lim_{k \to \infty} r_k = 2$，每行的平均信息容量趋向 1 比特。$\square$

**定理 2.10（子矩阵结构的完备性）**：子矩阵结构完全刻画了观察者的计算能力。

*证明*：
1. 行数 $k$ 决定预测复杂度
2. 激活模式决定信息获取
3. 频率谱决定处理效率
4. 嵌套关系决定层级地位

子矩阵结构是观察者完整的数学表示。$\square$