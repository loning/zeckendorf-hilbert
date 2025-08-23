# φ-子群理论的严格构造

## 定义 29.1（φ-子群）
设 $(G_{\mathbb{F}}, \star_{\mathbb{F}})$ 为φ-群，$H_{\mathbb{F}} \subseteq G_{\mathbb{F}}$ 为非空子集。称 $H_{\mathbb{F}}$ 为 $G_{\mathbb{F}}$ 的**φ-子群**，记作 $H_{\mathbb{F}} \leq G_{\mathbb{F}}$，当且仅当：

1. **运算封闭性**：$g, h \in H_{\mathbb{F}} \Rightarrow g \star_{\mathbb{F}} h \in H_{\mathbb{F}}$
2. **逆元封闭性**：$g \in H_{\mathbb{F}} \Rightarrow g^{-1} \in H_{\mathbb{F}}$

## 定理 29.1（φ-子群的等价刻画）
以下条件等价：

1. $H_{\mathbb{F}} \leq G_{\mathbb{F}}$
2. $H_{\mathbb{F}} \neq \emptyset$ 且对所有 $g, h \in H_{\mathbb{F}}$：$g \star_{\mathbb{F}} h^{-1} \in H_{\mathbb{F}}$
3. $(H_{\mathbb{F}}, \star_{\mathbb{F}}|_{H_{\mathbb{F}}})$ 构成φ-群

**证明：**
**$(1) \Rightarrow (2)$**：由φ-子群定义，取 $h = g$ 得单位元 $e_{\mathbb{F}} = g \star_{\mathbb{F}} g^{-1} \in H_{\mathbb{F}}$。
然后 $g \star_{\mathbb{F}} h^{-1} = g \star_{\mathbb{F}} h^{-1} \in H_{\mathbb{F}}$。

**$(2) \Rightarrow (3)$**：需验证φ-群公理。
- **结合律**：继承自 $G_{\mathbb{F}}$
- **单位元**：取任意 $g \in H_{\mathbb{F}}$，则 $e_{\mathbb{F}} = g \star_{\mathbb{F}} g^{-1} \in H_{\mathbb{F}}$
- **逆元**：对 $g \in H_{\mathbb{F}}$，有 $g^{-1} = e_{\mathbb{F}} \star_{\mathbb{F}} g^{-1} \in H_{\mathbb{F}}$

**$(3) \Rightarrow (1)$**：φ-群的运算封闭性和逆元存在性直接给出φ-子群条件。 ∎

## 定义 29.2（φ-子群的生成）
对φ-群 $G_{\mathbb{F}}$ 的子集 $S$，定义 $S$ **生成的φ-子群**：
$$\langle S \rangle_{\mathbb{F}} = \bigcap \{H_{\mathbb{F}} : S \subseteq H_{\mathbb{F}} \leq G_{\mathbb{F}}\}$$

即包含 $S$ 的最小φ-子群。

## 定理 29.2（φ-子群生成的具体刻画）
$$\langle S \rangle_{\mathbb{F}} = \left\{\prod_{i=1}^n s_i^{m_i} : n \in \mathbb{F}\mathbb{N}, s_i \in S, m_i \in \mathbb{F}\mathbb{Z}\right\}$$

即 $S$ 中元素及其逆元的所有有限φ-乘积。

**证明：**
记右边集合为 $T$。

**$T \subseteq \langle S \rangle_{\mathbb{F}}$**：由于 $\langle S \rangle_{\mathbb{F}}$ 包含 $S$ 且在φ-群运算下封闭，
所有 $S$ 中元素的有限乘积都属于 $\langle S \rangle_{\mathbb{F}}$。

**$\langle S \rangle_{\mathbb{F}} \subseteq T$**：需证明 $T$ 为包含 $S$ 的φ-子群。
- **包含 $S$**：对 $s \in S$，取 $n = 1, s_1 = s, m_1 = 1$ 得 $s \in T$
- **运算封闭**：两个有限乘积的乘积仍为有限乘积
- **逆元封闭**：$(s_1^{m_1} \cdots s_n^{m_n})^{-1} = s_n^{-m_n} \cdots s_1^{-m_1} \in T$

因此 $T$ 为包含 $S$ 的φ-子群，故 $\langle S \rangle_{\mathbb{F}} \subseteq T$。 ∎

## 定义 29.3（φ-正规子群）
φ-子群 $N_{\mathbb{F}} \leq G_{\mathbb{F}}$ 称为**φ-正规子群**，记作 $N_{\mathbb{F}} \triangleleft G_{\mathbb{F}}$，当且仅当：

对所有 $g \in G_{\mathbb{F}}, n \in N_{\mathbb{F}}$：
$$g \star_{\mathbb{F}} n \star_{\mathbb{F}} g^{-1} \in N_{\mathbb{F}}$$

## 定理 29.3（φ-正规子群的等价条件）
以下条件等价：

1. $N_{\mathbb{F}} \triangleleft G_{\mathbb{F}}$
2. 对所有 $g \in G_{\mathbb{F}}$：$g \star_{\mathbb{F}} N_{\mathbb{F}} \star_{\mathbb{F}} g^{-1} = N_{\mathbb{F}}$
3. 对所有 $g \in G_{\mathbb{F}}$：$g \star_{\mathbb{F}} N_{\mathbb{F}} = N_{\mathbb{F}} \star_{\mathbb{F}} g$

**证明：**
**$(1) \Rightarrow (2)$**：由正规性定义，$g \star_{\mathbb{F}} N_{\mathbb{F}} \star_{\mathbb{F}} g^{-1} \subseteq N_{\mathbb{F}}$。
反向包含：对 $n \in N_{\mathbb{F}}$，$n = g \star_{\mathbb{F}} (g^{-1} \star_{\mathbb{F}} n \star_{\mathbb{F}} g) \star_{\mathbb{F}} g^{-1} \in g \star_{\mathbb{F}} N_{\mathbb{F}} \star_{\mathbb{F}} g^{-1}$。

**$(2) \Rightarrow (3)$**：$g \star_{\mathbb{F}} N_{\mathbb{F}} = g \star_{\mathbb{F}} N_{\mathbb{F}} \star_{\mathbb{F}} g^{-1} \star_{\mathbb{F}} g = N_{\mathbb{F}} \star_{\mathbb{F}} g$。

**$(3) \Rightarrow (1)$**：对 $n \in N_{\mathbb{F}}$，$g \star_{\mathbb{F}} n \in g \star_{\mathbb{F}} N_{\mathbb{F}} = N_{\mathbb{F}} \star_{\mathbb{F}} g$，
故存在 $n' \in N_{\mathbb{F}}$ 使得 $g \star_{\mathbb{F}} n = n' \star_{\mathbb{F}} g$，
即 $g \star_{\mathbb{F}} n \star_{\mathbb{F}} g^{-1} = n' \in N_{\mathbb{F}}$。 ∎

## 定义 29.4（φ-商群）
设 $N_{\mathbb{F}} \triangleleft G_{\mathbb{F}}$ 为φ-正规子群，定义**φ-商群**：
$$G_{\mathbb{F}}/N_{\mathbb{F}} = \{g \star_{\mathbb{F}} N_{\mathbb{F}} : g \in G_{\mathbb{F}}\}$$

其中 $g \star_{\mathbb{F}} N_{\mathbb{F}} = \{g \star_{\mathbb{F}} n : n \in N_{\mathbb{F}}\}$ 为左陪集。

运算定义为：
$$(g_1 \star_{\mathbb{F}} N_{\mathbb{F}}) \star (g_2 \star_{\mathbb{F}} N_{\mathbb{F}}) = (g_1 \star_{\mathbb{F}} g_2) \star_{\mathbb{F}} N_{\mathbb{F}}$$

## 定理 29.4（φ-商群的良定义性）
φ-商群运算良定义且 $G_{\mathbb{F}}/N_{\mathbb{F}}$ 构成φ-群。

**证明：**
**良定义性**：需证明运算不依赖于陪集代表元的选择。
设 $g_1 \star_{\mathbb{F}} N_{\mathbb{F}} = g_1' \star_{\mathbb{F}} N_{\mathbb{F}}$ 且 $g_2 \star_{\mathbb{F}} N_{\mathbb{F}} = g_2' \star_{\mathbb{F}} N_{\mathbb{F}}$。

则存在 $n_1, n_2 \in N_{\mathbb{F}}$ 使得 $g_1' = g_1 \star_{\mathbb{F}} n_1$，$g_2' = g_2 \star_{\mathbb{F}} n_2$。

$(g_1' \star_{\mathbb{F}} g_2') \star_{\mathbb{F}} N_{\mathbb{F}} = (g_1 \star_{\mathbb{F}} n_1 \star_{\mathbb{F}} g_2 \star_{\mathbb{F}} n_2) \star_{\mathbb{F}} N_{\mathbb{F}}$

由正规性，$n_1 \star_{\mathbb{F}} g_2 = g_2 \star_{\mathbb{F}} n_1'$ 对某个 $n_1' \in N_{\mathbb{F}}$，故：
$(g_1' \star_{\mathbb{F}} g_2') \star_{\mathbb{F}} N_{\mathbb{F}} = (g_1 \star_{\mathbb{F}} g_2) \star_{\mathbb{F}} N_{\mathbb{F}}$

**φ-群性质**：
- **结合律**：继承自 $G_{\mathbb{F}}$
- **单位元**：$e_{\mathbb{F}} \star_{\mathbb{F}} N_{\mathbb{F}} = N_{\mathbb{F}}$
- **逆元**：$(g \star_{\mathbb{F}} N_{\mathbb{F}})^{-1} = g^{-1} \star_{\mathbb{F}} N_{\mathbb{F}}$ ∎

## 定义 29.5（φ-子群的指数）
设 $H_{\mathbb{F}} \leq G_{\mathbb{F}}$ 为φ-子群，定义**φ-指数**：
$$[G_{\mathbb{F}} : H_{\mathbb{F}}]_{\mathbb{F}} = |G_{\mathbb{F}}/H_{\mathbb{F}}|_{\mathbb{F}}$$

即左陪集的个数。

## 定理 29.5（φ-Lagrange定理）
对有限φ-群 $G_{\mathbb{F}}$ 和φ-子群 $H_{\mathbb{F}} \leq G_{\mathbb{F}}$：
$$|G_{\mathbb{F}}|_{\mathbb{F}} = |H_{\mathbb{F}}|_{\mathbb{F}} \otimes_{\mathbb{F}} [G_{\mathbb{F}} : H_{\mathbb{F}}]_{\mathbb{F}}$$

**证明：**
$G_{\mathbb{F}}$ 分解为 $H_{\mathbb{F}}$ 的不相交左陪集：
$$G_{\mathbb{F}} = \bigcup_{i=1}^k (g_i \star_{\mathbb{F}} H_{\mathbb{F}})$$

其中 $k = [G_{\mathbb{F}} : H_{\mathbb{F}}]_{\mathbb{F}}$。

**陪集等势性**：映射 $h \mapsto g_i \star_{\mathbb{F}} h$ 建立双射 $H_{\mathbb{F}} \to g_i \star_{\mathbb{F}} H_{\mathbb{F}}$。
因此 $|g_i \star_{\mathbb{F}} H_{\mathbb{F}}|_{\mathbb{F}} = |H_{\mathbb{F}}|_{\mathbb{F}}$。

**基数计算**：
$$|G_{\mathbb{F}}|_{\mathbb{F}} = \sum_{i=1}^k |g_i \star_{\mathbb{F}} H_{\mathbb{F}}|_{\mathbb{F}} = k \otimes_{\mathbb{F}} |H_{\mathbb{F}}|_{\mathbb{F}} = [G_{\mathbb{F}} : H_{\mathbb{F}}]_{\mathbb{F}} \otimes_{\mathbb{F}} |H_{\mathbb{F}}|_{\mathbb{F}}$$ ∎

## 推论 29.1（φ-群元素阶的整除性）
对有限φ-群 $G_{\mathbb{F}}$ 中的元素 $g$：
$$\text{ord}_{\mathbb{F}}(g) \mid_{\mathbb{F}} |G_{\mathbb{F}}|_{\mathbb{F}}$$

**证明：**
考虑由 $g$ 生成的φ-循环子群 $\langle g \rangle_{\mathbb{F}} \leq G_{\mathbb{F}}$。
由定理29.5，$|\langle g \rangle_{\mathbb{F}}|_{\mathbb{F}} \mid_{\mathbb{F}} |G_{\mathbb{F}}|_{\mathbb{F}}$。
而 $|\langle g \rangle_{\mathbb{F}}|_{\mathbb{F}} = \text{ord}_{\mathbb{F}}(g)$。 ∎

## 定义 29.6（φ-子群格）
φ-群 $G_{\mathbb{F}}$ 的所有φ-子群构成**φ-子群格** $\mathcal{L}(G_{\mathbb{F}})$，其中：

**偏序关系**：$H_1 \preceq_{\mathcal{L}} H_2 \Leftrightarrow H_1 \leq H_2$

**上确界**：$H_1 \vee_{\mathcal{L}} H_2 = \langle H_1 \cup H_2 \rangle_{\mathbb{F}}$

**下确界**：$H_1 \wedge_{\mathcal{L}} H_2 = H_1 \cap H_2$

## 定理 29.6（φ-子群格的格性质）
$(\mathcal{L}(G_{\mathbb{F}}), \preceq_{\mathcal{L}}, \vee_{\mathcal{L}}, \wedge_{\mathcal{L}})$ 构成完备格。

**证明：**
**偏序性质**：包含关系 $\leq$ 为偏序关系。

**上确界存在性**：$\langle H_1 \cup H_2 \rangle_{\mathbb{F}}$ 是包含 $H_1, H_2$ 的最小φ-子群。

**下确界存在性**：$H_1 \cap H_2$ 为φ-子群（运算和逆元在交集中封闭）且为包含于 $H_1, H_2$ 的最大φ-子群。

**完备性**：任意φ-子群族的上确界为其生成的φ-子群，下确界为其交集。 ∎

## 定义 29.7（φ-子群的中心化子和正规化子）
对φ-子群 $H_{\mathbb{F}} \leq G_{\mathbb{F}}$：

**φ-中心化子**：
$$C_{G_{\mathbb{F}}}(H_{\mathbb{F}}) = \{g \in G_{\mathbb{F}} : g \star_{\mathbb{F}} h = h \star_{\mathbb{F}} g, \forall h \in H_{\mathbb{F}}\}$$

**φ-正规化子**：
$$N_{G_{\mathbb{F}}}(H_{\mathbb{F}}) = \{g \in G_{\mathbb{F}} : g \star_{\mathbb{F}} H_{\mathbb{F}} \star_{\mathbb{F}} g^{-1} = H_{\mathbb{F}}\}$$

## 定理 29.7（φ-中心化子和正规化子的性质）
1. $C_{G_{\mathbb{F}}}(H_{\mathbb{F}}) \leq N_{G_{\mathbb{F}}}(H_{\mathbb{F}}) \leq G_{\mathbb{F}}$
2. $H_{\mathbb{F}} \triangleleft N_{G_{\mathbb{F}}}(H_{\mathbb{F}})$
3. $N_{G_{\mathbb{F}}}(H_{\mathbb{F}})$ 是使得 $H_{\mathbb{F}}$ 正规的最大φ-子群

**证明：**
**包含关系1**：若 $g$ 与 $H_{\mathbb{F}}$ 中所有元素交换，则特别地 $g \star_{\mathbb{F}} H_{\mathbb{F}} \star_{\mathbb{F}} g^{-1} = H_{\mathbb{F}}$。

**正规性2**：由φ-正规化子的定义直接得出。

**最大性3**：若 $K \leq G_{\mathbb{F}}$ 且 $H_{\mathbb{F}} \triangleleft K$，则对所有 $k \in K$：
$k \star_{\mathbb{F}} H_{\mathbb{F}} \star_{\mathbb{F}} k^{-1} = H_{\mathbb{F}}$，故 $k \in N_{G_{\mathbb{F}}}(H_{\mathbb{F}})$，即 $K \leq N_{G_{\mathbb{F}}}(H_{\mathbb{F}})$。 ∎

## 定义 29.8（φ-Sylow子群）
设 $G_{\mathbb{F}}$ 为有限φ-群，$p$ 为φ-素数，$|G_{\mathbb{F}}|_{\mathbb{F}} = p^k \otimes_{\mathbb{F}} m$，其中 $\gcd_{\mathbb{F}}(p, m) = \mathbf{1}_{\mathbb{F}}$。

φ-子群 $P \leq G_{\mathbb{F}}$ 称为**φ-Sylow $p$-子群**，当且仅当 $|P|_{\mathbb{F}} = p^k$。

## 定理 29.8（φ-Sylow定理）
设 $G_{\mathbb{F}}$ 为有限φ-群，$p$ 为φ-素数，则：

1. **存在性**：φ-Sylow $p$-子群存在
2. **共轭性**：所有φ-Sylow $p$-子群彼此共轭
3. **个数公式**：φ-Sylow $p$-子群的个数 $n_p$ 满足：
   - $n_p \equiv \mathbf{1}_{\mathbb{F}} \pmod{p}$
   - $n_p \mid_{\mathbb{F}} |G_{\mathbb{F}}|_{\mathbb{F}}$

**证明：**
通过φ-群与标准群的同构（定理27.3），φ-Sylow定理对应标准Sylow定理。

**存在性**：由标准群的Sylow定理和同构的保持性。

**共轭性**：φ-共轭对应标准共轭，同构保持共轭关系。

**个数公式**：通过同构，φ-Sylow子群的个数对应标准Sylow子群的个数，满足相同的同余和整除条件。 ∎

## 定义 29.9（φ-子群系列）
φ-群 $G_{\mathbb{F}}$ 的**φ-子群系列**是φ-子群序列：
$$\{e_{\mathbb{F}}\} = G_0 \leq G_1 \leq \cdots \leq G_n = G_{\mathbb{F}}$$

系列称为**φ-正规系列**，当且仅当每个 $G_i \triangleleft G_{i+1}$。

## 定理 29.9（φ-Jordan-Hölder定理）
每个有限φ-群都有φ-合成系列，且合成因子在同构和重排意义下唯一。

**证明：**
通过φ-群与标准群的同构，φ-Jordan-Hölder定理对应标准Jordan-Hölder定理。

**合成系列存在性**：由有限性和极大性条件，总可构造不能再细分的正规系列。

**唯一性**：合成因子的同构类和重数由群的内在结构唯一确定，
通过同构映射与标准情形保持一一对应。 ∎

## 定理 29.10（φ-子群对应定理）
设 $N_{\mathbb{F}} \triangleleft G_{\mathbb{F}}$ 为φ-正规子群，则存在双射：
$$\{H_{\mathbb{F}} : N_{\mathbb{F}} \leq H_{\mathbb{F}} \leq G_{\mathbb{F}}\} \leftrightarrow \{K : K \leq G_{\mathbb{F}}/N_{\mathbb{F}}\}$$

通过 $H_{\mathbb{F}} \mapsto H_{\mathbb{F}}/N_{\mathbb{F}}$ 和 $K \mapsto \pi^{-1}(K)$ 实现，
其中 $\pi: G_{\mathbb{F}} \to G_{\mathbb{F}}/N_{\mathbb{F}}$ 为自然投影。

**证明：**
**良定义性**：若 $N_{\mathbb{F}} \leq H_{\mathbb{F}} \leq G_{\mathbb{F}}$，则 $H_{\mathbb{F}}/N_{\mathbb{F}} \leq G_{\mathbb{F}}/N_{\mathbb{F}}$。

**双射性**：
- **单射性**：若 $H_1/N_{\mathbb{F}} = H_2/N_{\mathbb{F}}$，则 $H_1 = H_2$
- **满射性**：对任意 $K \leq G_{\mathbb{F}}/N_{\mathbb{F}}$，$H_{\mathbb{F}} = \pi^{-1}(K)$ 满足 $H_{\mathbb{F}}/N_{\mathbb{F}} = K$

**结构保持**：双射保持包含关系、正规性和指数关系。 ∎

## 推论 29.2（φ-子群理论的完备性）
φ-子群理论实现了与标准子群论完全等价的代数结构：

1. **定义等价性**：φ-子群概念与标准子群概念等价
2. **生成理论**：φ-子群生成与标准生成对应
3. **正规性理论**：φ-正规子群与标准正规子群对应
4. **商群理论**：φ-商群构造与标准商群构造等价
5. **格结构理论**：φ-子群格与标准子群格同构
6. **Sylow理论**：φ-Sylow定理与标准Sylow定理对应

这为φ-群分类理论和φ-代数结构分析提供了完整的子群理论基础。

**证明：**
所有性质由定理29.1-29.10综合得出，特别是Lagrange定理（定理29.5）、Sylow定理（定理29.8）和对应定理（定理29.10）确保了φ-子群理论的完备性。 ∎