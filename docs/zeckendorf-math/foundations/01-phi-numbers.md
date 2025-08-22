# φ-数字系统理论

## 定义 2.1（φ-自然数集合）
定义 **φ-自然数集合** $\mathbb{F}\mathbb{N} = \Phi$，其中 $\Phi$ 为所有满足no-11约束的二进制串集合。

## 定义 2.2（φ-自然数值函数）
定义值函数 $\text{val}: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 为：
$$\text{val}(s) = \begin{cases}
0 & \text{若 } s = \varepsilon \\
\sum_{i=1}^{|s|} s_i \cdot F_i & \text{若 } s = s_{|s|} s_{|s|-1} \cdots s_1 \in \Phi \setminus \{\varepsilon\}
\end{cases}$$

其中 $s_i$ 表示串 $s$ 的第 $i$ 个字符（从右向左计数）。

## 定理 2.1（φ-自然数双射性）
值函数 $\text{val}: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 是双射。

**证明：** 
由定理1.2知，存在双射 $\text{encode}: \mathbb{N}^+ \to \Phi \setminus \{\varepsilon\}$ 和 $\text{decode}: \Phi \setminus \{\varepsilon\} \to \mathbb{N}^+$。

注意到 $\text{decode}(s) = \text{val}(s)$ 对所有 $s \in \Phi \setminus \{\varepsilon\}$，
且 $\text{val}(\varepsilon) = 0$，$\text{encode}(0)$ 未定义。

扩展双射为：设 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 定义为
$$\psi(n) = \begin{cases}
\varepsilon & \text{若 } n = 0 \\
\text{encode}(n) & \text{若 } n \geq 1
\end{cases}$$

则 $\text{val} \circ \psi = \text{id}_{\mathbb{N}}$ 且 $\psi \circ \text{val} = \text{id}_{\mathbb{F}\mathbb{N}}$。 ∎

## 定义 2.3（φ-零元和φ-单位元）
定义：
- **φ-零元**：$\mathbf{0}_\phi = \varepsilon$
- **φ-单位元**：$\mathbf{1}_\phi = 1$（对应 $\text{val}(1) = F_1 = 1$）

## 定义 2.4（φ-自然数序关系）
在 $\mathbb{F}\mathbb{N}$ 上定义全序关系 $\preceq_\phi$ 为：
$$s_1 \preceq_\phi s_2 \iff \text{val}(s_1) \leq \text{val}(s_2)$$

## 定理 2.2（φ-序关系的良序性）
$(\mathbb{F}\mathbb{N}, \preceq_\phi)$ 是良序集。

**证明：** 
由于 $\text{val}: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 是双射且 $(\mathbb{N}, \leq)$ 是良序集，
$(\mathbb{F}\mathbb{N}, \preceq_\phi)$ 与 $(\mathbb{N}, \leq)$ 同构，因此也是良序集。 ∎

## 定义 2.5（φ-后继函数）
定义后继函数 $S_\phi: \mathbb{F}\mathbb{N} \to \mathbb{F}\mathbb{N}$ 为：
$$S_\phi(s) = \psi(\text{val}(s) + 1)$$

其中 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 为$\text{val}$的逆映射。

## 定理 2.3（φ-后继函数性质）
后继函数 $S_\phi$ 满足以下性质：
1. **单射性**：$S_\phi(s_1) = S_\phi(s_2) \Rightarrow s_1 = s_2$
2. **无像点为零**：$\nexists s \in \mathbb{F}\mathbb{N}$ 使得 $S_\phi(s) = \mathbf{0}_\phi$
3. **无限性**：$S_\phi$ 的值域为 $\mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}$

**证明：** 
1. 若 $S_\phi(s_1) = S_\phi(s_2)$，则 $\psi(\text{val}(s_1) + 1) = \psi(\text{val}(s_2) + 1)$。
   由于 $\psi$ 是双射，得到 $\text{val}(s_1) + 1 = \text{val}(s_2) + 1$，故 $\text{val}(s_1) = \text{val}(s_2)$。
   由于 $\text{val}$ 是双射，得到 $s_1 = s_2$。

2. 若 $S_\phi(s) = \mathbf{0}_\phi = \varepsilon$，则 $\psi(\text{val}(s) + 1) = \varepsilon = \psi(0)$。
   由 $\psi$ 的双射性，得到 $\text{val}(s) + 1 = 0$，即 $\text{val}(s) = -1$。
   但 $\text{val}(s) \geq 0$ 对所有 $s \in \mathbb{F}\mathbb{N}$，矛盾。

3. 对任意 $t \in \mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}$，有 $\text{val}(t) \geq 1$。
   设 $s = \psi(\text{val}(t) - 1)$，则 $S_\phi(s) = \psi(\text{val}(t) - 1 + 1) = \psi(\text{val}(t)) = t$。 ∎

## 定理 2.4（φ-Peano公理）
$(\mathbb{F}\mathbb{N}, \mathbf{0}_\phi, S_\phi)$ 满足Peano公理的φ-版本：

1. $\mathbf{0}_\phi \in \mathbb{F}\mathbb{N}$
2. 对所有 $s \in \mathbb{F}\mathbb{N}$，$S_\phi(s) \in \mathbb{F}\mathbb{N}$
3. 对所有 $s_1, s_2 \in \mathbb{F}\mathbb{N}$，$S_\phi(s_1) = S_\phi(s_2) \Rightarrow s_1 = s_2$
4. 对所有 $s \in \mathbb{F}\mathbb{N}$，$S_\phi(s) \neq \mathbf{0}_\phi$
5. **φ-归纳公理**：设 $P \subseteq \mathbb{F}\mathbb{N}$ 满足：
   - $\mathbf{0}_\phi \in P$
   - 对所有 $s \in \mathbb{F}\mathbb{N}$，$s \in P \Rightarrow S_\phi(s) \in P$
   
   则 $P = \mathbb{F}\mathbb{N}$。

**证明：** 
前四条直接由定义和定理2.3得出。

对于第5条，设 $P \subseteq \mathbb{F}\mathbb{N}$ 满足给定条件。
定义 $Q = \{\text{val}(s) : s \in P\} \subseteq \mathbb{N}$。

由条件，$\mathbf{0}_\phi \in P$，故 $0 = \text{val}(\mathbf{0}_\phi) \in Q$。

若 $n \in Q$，则存在 $s \in P$ 使得 $\text{val}(s) = n$。
由条件，$S_\phi(s) \in P$，而 $\text{val}(S_\phi(s)) = n + 1$，故 $n + 1 \in Q$。

由数学归纳法，$Q = \mathbb{N}$。

对任意 $t \in \mathbb{F}\mathbb{N}$，有 $\text{val}(t) \in \mathbb{N} = Q$，
故存在 $s \in P$ 使得 $\text{val}(s) = \text{val}(t)$。
由 $\text{val}$ 的双射性，$s = t$，因此 $t \in P$。
故 $P = \mathbb{F}\mathbb{N}$。 ∎

## 推论 2.1（φ-自然数的结构同构）
$(\mathbb{F}\mathbb{N}, \mathbf{0}_\phi, S_\phi) \cong (\mathbb{N}, 0, s)$，其中 $s$ 为标准后继函数。

**证明：** 
双射 $\text{val}: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 保持结构：
- $\text{val}(\mathbf{0}_\phi) = 0$
- $\text{val}(S_\phi(t)) = \text{val}(t) + 1 = s(\text{val}(t))$

因此为结构同构。 ∎