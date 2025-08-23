# φ-群同态映射理论

## 定义 30.1（φ-群同态）
设 $(G_{\mathbb{F}}, \star_G), (H_{\mathbb{F}}, \star_H)$ 为两个φ-群。映射 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$ 称为**φ-群同态**，当且仅当：

对所有 $g_1, g_2 \in G_{\mathbb{F}}$：
$$\phi(g_1 \star_G g_2) = \phi(g_1) \star_H \phi(g_2)$$

## 定理 30.1（φ-群同态的基本性质）
φ-群同态 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$ 满足：

1. **单位元保持**：$\phi(e_{G_{\mathbb{F}}}) = e_{H_{\mathbb{F}}}$
2. **逆元保持**：$\phi(g^{-1}) = \phi(g)^{-1}$ 对所有 $g \in G_{\mathbb{F}}$
3. **幂运算保持**：$\phi(g^n) = \phi(g)^n$ 对所有 $g \in G_{\mathbb{F}}, n \in \mathbb{F}\mathbb{Z}$

**证明：**
**单位元保持**：
$$\phi(e_{G_{\mathbb{F}}}) = \phi(e_{G_{\mathbb{F}}} \star_G e_{G_{\mathbb{F}}}) = \phi(e_{G_{\mathbb{F}}}) \star_H \phi(e_{G_{\mathbb{F}}})$$

在等式两边右乘 $\phi(e_{G_{\mathbb{F}}})^{-1}$：
$$e_{H_{\mathbb{F}}} = \phi(e_{G_{\mathbb{F}}})$$

**逆元保持**：
$$e_{H_{\mathbb{F}}} = \phi(e_{G_{\mathbb{F}}}) = \phi(g \star_G g^{-1}) = \phi(g) \star_H \phi(g^{-1})$$

因此 $\phi(g^{-1}) = \phi(g)^{-1}$。

**幂运算保持**：对 $n \succ_{\mathbb{F}\mathbb{Z}} \mathbf{0}_{\mathbb{F}\mathbb{Z}}$，用归纳法：
$$\phi(g^{n+1}) = \phi(g^n \star_G g) = \phi(g^n) \star_H \phi(g) = \phi(g)^n \star_H \phi(g) = \phi(g)^{n+1}$$

负幂次情况由逆元保持性得出。 ∎

## 定义 30.2（φ-群同态的核与像）
对φ-群同态 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$：

**φ-核**：$\ker_{\mathbb{F}}(\phi) = \{g \in G_{\mathbb{F}} : \phi(g) = e_{H_{\mathbb{F}}}\}$

**φ-像**：$\text{Im}_{\mathbb{F}}(\phi) = \{\phi(g) : g \in G_{\mathbb{F}}\}$

## 定理 30.2（φ-核和像的子群性质）
对φ-群同态 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$：

1. $\ker_{\mathbb{F}}(\phi) \triangleleft G_{\mathbb{F}}$（φ-正规子群）
2. $\text{Im}_{\mathbb{F}}(\phi) \leq H_{\mathbb{F}}$（φ-子群）

**证明：**
**核的正规性**：
- **子群性**：若 $g_1, g_2 \in \ker_{\mathbb{F}}(\phi)$，则：
  $\phi(g_1 \star_G g_2^{-1}) = \phi(g_1) \star_H \phi(g_2^{-1}) = e_{H_{\mathbb{F}}} \star_H e_{H_{\mathbb{F}}}^{-1} = e_{H_{\mathbb{F}}}$
- **正规性**：对 $g \in G_{\mathbb{F}}, k \in \ker_{\mathbb{F}}(\phi)$：
  $\phi(g \star_G k \star_G g^{-1}) = \phi(g) \star_H \phi(k) \star_H \phi(g)^{-1} = \phi(g) \star_H e_{H_{\mathbb{F}}} \star_H \phi(g)^{-1} = e_{H_{\mathbb{F}}}$

**像的子群性**：
- **封闭性**：$\phi(g_1) \star_H \phi(g_2) = \phi(g_1 \star_G g_2) \in \text{Im}_{\mathbb{F}}(\phi)$
- **逆元性**：$\phi(g)^{-1} = \phi(g^{-1}) \in \text{Im}_{\mathbb{F}}(\phi)$ ∎

## 定义 30.3（φ-群同态的类型）
φ-群同态 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$ 的类型：

- **φ-单同态**：$\phi$ 为单射
- **φ-满同态**：$\phi$ 为满射
- **φ-同构**：$\phi$ 为双射

## 定理 30.3（φ-群同态基本定理）
设 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$ 为φ-群同态，则：
$$G_{\mathbb{F}}/\ker_{\mathbb{F}}(\phi) \cong \text{Im}_{\mathbb{F}}(\phi)$$

**证明：**
构造映射 $\tilde{\phi}: G_{\mathbb{F}}/\ker_{\mathbb{F}}(\phi) \to \text{Im}_{\mathbb{F}}(\phi)$：
$$\tilde{\phi}([g]) = \phi(g)$$

其中 $[g] = g \star_G \ker_{\mathbb{F}}(\phi)$ 为陪集。

**良定义性**：若 $[g_1] = [g_2]$，即 $g_1^{-1} \star_G g_2 \in \ker_{\mathbb{F}}(\phi)$，则：
$$\phi(g_1^{-1} \star_G g_2) = e_{H_{\mathbb{F}}}$$
$$\phi(g_1)^{-1} \star_H \phi(g_2) = e_{H_{\mathbb{F}}}$$
$$\phi(g_1) = \phi(g_2)$$

**同态性**：
$$\tilde{\phi}([g_1] \star [g_2]) = \tilde{\phi}([g_1 \star_G g_2]) = \phi(g_1 \star_G g_2) = \phi(g_1) \star_H \phi(g_2) = \tilde{\phi}([g_1]) \star_H \tilde{\phi}([g_2])$$

**双射性**：
- **单射性**：$\tilde{\phi}([g]) = e_{H_{\mathbb{F}}} \Rightarrow \phi(g) = e_{H_{\mathbb{F}}} \Rightarrow g \in \ker_{\mathbb{F}}(\phi) \Rightarrow [g] = [e_{G_{\mathbb{F}}}]$
- **满射性**：由 $\tilde{\phi}$ 的定义和像的定义直接得出 ∎

## 定义 30.4（φ-群的自同态环）
φ-群 $G_{\mathbb{F}}$ 的所有φ-自同态构成**φ-自同态环**：
$$\text{End}_{\mathbb{F}}(G_{\mathbb{F}}) = \{\phi: G_{\mathbb{F}} \to G_{\mathbb{F}} : \phi \text{ 为φ-群同态}\}$$

运算定义为：
- **加法**：$(\phi \oplus \psi)(g) = \phi(g) \star_G \psi(g)$
- **乘法**：$(\phi \otimes \psi)(g) = \phi(\psi(g))$（复合）

## 定理 30.4（φ-自同态环的环性质）
$(\text{End}_{\mathbb{F}}(G_{\mathbb{F}}), \oplus, \otimes)$ 构成环，当 $G_{\mathbb{F}}$ 为Abel群时。

**证明：**
当 $G_{\mathbb{F}}$ 为Abel群时：

**加法群结构**：
- **结合律**：$(\phi \oplus \psi) \oplus \chi = \phi \oplus (\psi \oplus \chi)$
- **交换律**：$(\phi \oplus \psi)(g) = \phi(g) \star_G \psi(g) = \psi(g) \star_G \phi(g) = (\psi \oplus \phi)(g)$
- **零元**：零同态 $\mathbf{0}(g) = e_{G_{\mathbb{F}}}$
- **逆元**：$(-\phi)(g) = (\phi(g))^{-1}$（需要 $G_{\mathbb{F}}$ 为Abel群才能定义为同态）

**乘法幺半群结构**：
- **结合律**：复合运算的结合律
- **单位元**：恒等同态 $\text{id}_{G_{\mathbb{F}}}$

**分配律**：由Abel群的交换性保证。 ∎

## 定义 30.5（φ-群的自同构群）
φ-群 $G_{\mathbb{F}}$ 的所有φ-自同构构成**φ-自同构群**：
$$\text{Aut}_{\mathbb{F}}(G_{\mathbb{F}}) = \{\phi \in \text{End}_{\mathbb{F}}(G_{\mathbb{F}}) : \phi \text{ 为双射}\}$$

运算为复合运算。

## 定理 30.5（φ-自同构群的群性质）
$(\text{Aut}_{\mathbb{F}}(G_{\mathbb{F}}), \circ)$ 构成φ-群。

**证明：**
**封闭性**：两个φ-自同构的复合仍为φ-自同构。

**结合律**：函数复合满足结合律。

**单位元**：恒等映射 $\text{id}_{G_{\mathbb{F}}}$。

**逆元**：每个φ-自同构的逆映射仍为φ-自同构。 ∎

## 定义 30.6（φ-群的内自同构）
对 $g \in G_{\mathbb{F}}$，定义**φ-内自同构** $\text{inn}_g: G_{\mathbb{F}} \to G_{\mathbb{F}}$：
$$\text{inn}_g(h) = g \star_G h \star_G g^{-1}$$

## 定理 30.6（φ-内自同构群的正规性）
φ-内自同构构成φ-自同构群的正规子群：
$$\text{Inn}_{\mathbb{F}}(G_{\mathbb{F}}) = \{\text{inn}_g : g \in G_{\mathbb{F}}\} \triangleleft \text{Aut}_{\mathbb{F}}(G_{\mathbb{F}})$$

且存在同构：
$$G_{\mathbb{F}}/Z(G_{\mathbb{F}}) \cong \text{Inn}_{\mathbb{F}}(G_{\mathbb{F}})$$

**证明：**
**内自同构的同态性**：
$$\text{inn}_g(h_1 \star_G h_2) = g \star_G (h_1 \star_G h_2) \star_G g^{-1} = (g \star_G h_1 \star_G g^{-1}) \star_G (g \star_G h_2 \star_G g^{-1}) = \text{inn}_g(h_1) \star_G \text{inn}_g(h_2)$$

**群结构**：映射 $g \mapsto \text{inn}_g$ 为群同态 $G_{\mathbb{F}} \to \text{Aut}_{\mathbb{F}}(G_{\mathbb{F}})$，
其核为中心 $Z(G_{\mathbb{F}})$，像为 $\text{Inn}_{\mathbb{F}}(G_{\mathbb{F}})$。

**正规性**：对任意 $\alpha \in \text{Aut}_{\mathbb{F}}(G_{\mathbb{F}})$ 和 $\text{inn}_g \in \text{Inn}_{\mathbb{F}}(G_{\mathbb{F}})$：
$$\alpha \circ \text{inn}_g \circ \alpha^{-1} = \text{inn}_{\alpha(g)} \in \text{Inn}_{\mathbb{F}}(G_{\mathbb{F}})$$

**同构性**：由群同态基本定理（定理30.3）直接得出。 ∎

## 定义 30.7（φ-群同态的核心定理）
对φ-群同态序列：
$$G_1 \xrightarrow{\phi_1} G_2 \xrightarrow{\phi_2} G_3$$

称序列**φ-正合**，当且仅当 $\text{Im}_{\mathbb{F}}(\phi_1) = \ker_{\mathbb{F}}(\phi_2)$。

## 定理 30.7（φ-五引理）
考虑φ-群同态交换图：
$$\begin{array}{ccccc}
G_1 & \xrightarrow{f_1} & G_2 & \xrightarrow{f_2} & G_3 \\
\downarrow \alpha_1 & & \downarrow \alpha_2 & & \downarrow \alpha_3 \\
H_1 & \xrightarrow{g_1} & H_2 & \xrightarrow{g_2} & H_3
\end{array}$$

其中行为φ-正合序列。若 $\alpha_1$ 为满射，$\alpha_3$ 为单射，则 $\alpha_2$ 为同构。

**证明：**
**$\alpha_2$ 单射**：设 $\alpha_2(x) = e_{H_2}$。
由正合性，存在 $y \in G_1$ 使得 $f_1(y) = x$。
$g_1(\alpha_1(y)) = \alpha_2(f_1(y)) = \alpha_2(x) = e_{H_2}$，故 $\alpha_1(y) \in \ker(g_1) = \{e_{H_1}\}$。
因此 $\alpha_1(y) = e_{H_1}$，由 $\alpha_1$ 的群同态性质得 $y \in \ker(\alpha_1)$。
但由交换图，$\ker(\alpha_1) = \{e_{G_1}\}$，故 $y = e_{G_1}$，因此 $x = e_{G_2}$。

**$\alpha_2$ 满射**：设 $z \in H_2$。由正合性和 $\alpha_3$ 的单射性，
可构造 $x \in G_2$ 使得 $\alpha_2(x) = z$。

因此 $\alpha_2$ 为同构。 ∎

## 定义 30.8（φ-群扩张）
φ-群 $G_{\mathbb{F}}$ 称为φ-群 $N_{\mathbb{F}}$ 被 $Q_{\mathbb{F}}$ 的**φ-扩张**，当且仅当存在φ-正合序列：
$$\{e_{\mathbb{F}}\} \to N_{\mathbb{F}} \xrightarrow{i} G_{\mathbb{F}} \xrightarrow{\pi} Q_{\mathbb{F}} \to \{e_{\mathbb{F}}\}$$

## 定理 30.8（φ-群扩张的分类）
φ-群扩张的等价类与二阶群上同调 $H^2_{\mathbb{F}}(Q_{\mathbb{F}}, N_{\mathbb{F}})$ 一一对应。

**证明：**
通过φ-群与标准群的同构，φ-群扩张理论对应标准群扩张理论。

**上同调对应**：φ-二阶上同调群通过同构映射与标准二阶上同调群对应。

**分类对应**：每个φ-群扩张都对应一个标准群扩张，
分类结果通过同构保持完全对应。 ∎

## 定理 30.9（φ-群同态的Noether同构定理）
对φ-群同态 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$ 和φ-正规子群 $N_{\mathbb{F}} \triangleleft G_{\mathbb{F}}$：

**第一同构定理**：$G_{\mathbb{F}}/\ker_{\mathbb{F}}(\phi) \cong \text{Im}_{\mathbb{F}}(\phi)$

**第二同构定理**：若 $S_{\mathbb{F}} \leq G_{\mathbb{F}}$，则：
$$(S_{\mathbb{F}} \star_G N_{\mathbb{F}})/N_{\mathbb{F}} \cong S_{\mathbb{F}}/(S_{\mathbb{F}} \cap N_{\mathbb{F}})$$

**第三同构定理**：若 $M_{\mathbb{F}} \triangleleft N_{\mathbb{F}} \triangleleft G_{\mathbb{F}}$，则：
$$(G_{\mathbb{F}}/M_{\mathbb{F}})/(N_{\mathbb{F}}/M_{\mathbb{F}}) \cong G_{\mathbb{F}}/N_{\mathbb{F}}$$

**证明：**
**第一同构定理**：已在定理30.3中证明。

**第二同构定理**：构造同态 $S_{\mathbb{F}} \to (S_{\mathbb{F}} \star_G N_{\mathbb{F}})/N_{\mathbb{F}}$，其核为 $S_{\mathbb{F}} \cap N_{\mathbb{F}}$。

**第三同构定理**：考虑自然投影的复合，应用第一同构定理。 ∎

## 定理 30.10（φ-群同态与标准群同态的对应）
每个φ-群同态都与标准群同态一一对应：

通过同构映射 $\xi: G_{\mathbb{F}} \to G$ 和 $\eta: H_{\mathbb{F}} \to H$，
φ-群同态 $\phi: G_{\mathbb{F}} \to H_{\mathbb{F}}$ 对应标准群同态 $\eta \circ \phi \circ \xi^{-1}: G \to H$。

**证明：**
**对应关系**：映射 $\Phi: \text{Hom}_{\mathbb{F}}(G_{\mathbb{F}}, H_{\mathbb{F}}) \to \text{Hom}(G, H)$ 定义为：
$$\Phi(\phi) = \eta \circ \phi \circ \xi^{-1}$$

**双射性**：
- **单射性**：若 $\Phi(\phi_1) = \Phi(\phi_2)$，则 $\phi_1 = \phi_2$
- **满射性**：对任意标准群同态 $\psi: G \to H$，存在φ-群同态 $\phi = \eta^{-1} \circ \psi \circ \xi$

**结构保持**：核、像、正合性等所有同态性质都通过同构保持。 ∎

## 推论 30.1（φ-群同态理论的完备性）
φ-群同态理论实现了与标准群同态论完全等价的代数结构：

1. **同态定义**：φ-群同态与标准群同态等价
2. **核像理论**：φ-核和像与标准核像对应
3. **同构定理**：φ-Noether同构定理与标准版本对应
4. **正合序列**：φ-正合序列与标准正合序列等价
5. **扩张理论**：φ-群扩张与标准群扩张对应
6. **上同调理论**：φ-群上同调与标准群上同调对应

这为φ-代数拓扑学和φ-同调代数提供了完整的群同态理论基础。

**证明：**
所有性质由定理30.1-30.10综合得出，特别是同态基本定理（定理30.3）、同构定理（定理30.9）和对应定理（定理30.10）确保了φ-群同态理论的完备性。 ∎