# φ-环同态理论

## 定义 35.1（φ-环同态）
设 $(R_{\mathbb{F}}, \oplus_R, \otimes_R), (S_{\mathbb{F}}, \oplus_S, \otimes_S)$ 为两个φ-环。映射 $\phi: R_{\mathbb{F}} \to S_{\mathbb{F}}$ 称为**φ-环同态**，当且仅当：

1. $\phi(r_1 \oplus_R r_2) = \phi(r_1) \oplus_S \phi(r_2)$ 对所有 $r_1, r_2 \in R_{\mathbb{F}}$
2. $\phi(r_1 \otimes_R r_2) = \phi(r_1) \otimes_S \phi(r_2)$ 对所有 $r_1, r_2 \in R_{\mathbb{F}}$
3. $\phi(\mathbf{1}_R) = \mathbf{1}_S$

## 定理 35.1（φ-环同态的基本性质）
φ-环同态 $\phi: R_{\mathbb{F}} \to S_{\mathbb{F}}$ 满足：

1. **零元保持**：$\phi(\mathbf{0}_R) = \mathbf{0}_S$
2. **加法逆元保持**：$\phi(-r) = -\phi(r)$ 对所有 $r \in R_{\mathbb{F}}$
3. **幂运算保持**：$\phi(r^n) = \phi(r)^n$ 对所有 $r \in R_{\mathbb{F}}, n \in \mathbb{F}\mathbb{N}$
4. **单位元映射性质**：若 $r \in U(R_{\mathbb{F}})$，则 $\phi(r) \in U(S_{\mathbb{F}})$（当 $\phi$ 为满射时）

**证明：**
**零元保持**：
$$\phi(\mathbf{0}_R) = \phi(\mathbf{0}_R \oplus_R \mathbf{0}_R) = \phi(\mathbf{0}_R) \oplus_S \phi(\mathbf{0}_R)$$

在等式两边减去 $\phi(\mathbf{0}_R)$：
$$\mathbf{0}_S = \phi(\mathbf{0}_R)$$

**加法逆元保持**：
$$\mathbf{0}_S = \phi(\mathbf{0}_R) = \phi(r \oplus_R (-r)) = \phi(r) \oplus_S \phi(-r)$$

因此 $\phi(-r) = -\phi(r)$。

**幂运算保持**：归纳证明，基于乘法同态性质。

**单位元映射**：若 $r \otimes_R s = \mathbf{1}_R$，则：
$$\mathbf{1}_S = \phi(\mathbf{1}_R) = \phi(r \otimes_R s) = \phi(r) \otimes_S \phi(s)$$

故 $\phi(r)$ 为单位元。 ∎

## 定义 35.2（φ-环同态的核与像）
对φ-环同态 $\phi: R_{\mathbb{F}} \to S_{\mathbb{F}}$：

**φ-核**：$\ker_{\mathbb{F}}(\phi) = \{r \in R_{\mathbb{F}} : \phi(r) = \mathbf{0}_S\}$

**φ-像**：$\text{Im}_{\mathbb{F}}(\phi) = \{\phi(r) : r \in R_{\mathbb{F}}\}$

## 定理 35.2（φ-环同态核像的结构）
对φ-环同态 $\phi: R_{\mathbb{F}} \to S_{\mathbb{F}}$：

1. $\ker_{\mathbb{F}}(\phi) \triangleleft R_{\mathbb{F}}$（φ-理想）
2. $\text{Im}_{\mathbb{F}}(\phi) \leq S_{\mathbb{F}}$（φ-子环）

**证明：**
**核的理想性**：
- **加法子群性**：若 $r_1, r_2 \in \ker_{\mathbb{F}}(\phi)$，则：
  $\phi(r_1 \ominus_{\mathbb{F}} r_2) = \phi(r_1) \ominus_S \phi(r_2) = \mathbf{0}_S \ominus_S \mathbf{0}_S = \mathbf{0}_S$
- **吸收性**：对 $r \in R_{\mathbb{F}}, k \in \ker_{\mathbb{F}}(\phi)$：
  $\phi(r \otimes_R k) = \phi(r) \otimes_S \phi(k) = \phi(r) \otimes_S \mathbf{0}_S = \mathbf{0}_S$

**像的子环性**：
- **加法封闭性**：$\phi(r_1) \oplus_S \phi(r_2) = \phi(r_1 \oplus_R r_2) \in \text{Im}_{\mathbb{F}}(\phi)$
- **乘法封闭性**：$\phi(r_1) \otimes_S \phi(r_2) = \phi(r_1 \otimes_R r_2) \in \text{Im}_{\mathbb{F}}(\phi)$
- **单位元**：$\mathbf{1}_S = \phi(\mathbf{1}_R) \in \text{Im}_{\mathbb{F}}(\phi)$ ∎

## 定理 35.3（φ-环同态基本定理）
设 $\phi: R_{\mathbb{F}} \to S_{\mathbb{F}}$ 为φ-环同态，则：
$$R_{\mathbb{F}}/\ker_{\mathbb{F}}(\phi) \cong \text{Im}_{\mathbb{F}}(\phi)$$

**证明：**
构造映射 $\tilde{\phi}: R_{\mathbb{F}}/\ker_{\mathbb{F}}(\phi) \to \text{Im}_{\mathbb{F}}(\phi)$：
$$\tilde{\phi}([r]) = \phi(r)$$

**良定义性**：若 $[r_1] = [r_2]$，即 $r_1 \ominus_{\mathbb{F}} r_2 \in \ker_{\mathbb{F}}(\phi)$，则：
$$\phi(r_1 \ominus_{\mathbb{F}} r_2) = \mathbf{0}_S$$
$$\phi(r_1) \ominus_S \phi(r_2) = \mathbf{0}_S$$
$$\phi(r_1) = \phi(r_2)$$

**环同态性**：
- **加法保持**：$\tilde{\phi}([r_1] \oplus [r_2]) = \tilde{\phi}([r_1 \oplus_R r_2]) = \phi(r_1 \oplus_R r_2) = \phi(r_1) \oplus_S \phi(r_2) = \tilde{\phi}([r_1]) \oplus_S \tilde{\phi}([r_2])$
- **乘法保持**：类似证明

**双射性**：
- **单射性**：$\tilde{\phi}([r]) = \mathbf{0}_S \Rightarrow \phi(r) = \mathbf{0}_S \Rightarrow r \in \ker_{\mathbb{F}}(\phi) \Rightarrow [r] = [\mathbf{0}_R]$
- **满射性**：由定义和像的定义直接得出 ∎

## 定理 35.4（φ-环同态的Noether同构定理）
**第一同构定理**：$R_{\mathbb{F}}/\ker_{\mathbb{F}}(\phi) \cong \text{Im}_{\mathbb{F}}(\phi)$

**第二同构定理**：若 $S_{\mathbb{F}} \leq R_{\mathbb{F}}$ 为φ-子环，$I \triangleleft R_{\mathbb{F}}$ 为φ-理想，则：
$$(S_{\mathbb{F}} \oplus_{\mathbb{F}} I)/I \cong S_{\mathbb{F}}/(S_{\mathbb{F}} \cap I)$$

**第三同构定理**：若 $I \subseteq J$ 为φ-理想，则：
$$(R_{\mathbb{F}}/I)/(J/I) \cong R_{\mathbb{F}}/J$$

**证明：**
**第一同构定理**：已在定理35.3中证明。

**第二同构定理**：构造自然投影 $S_{\mathbb{F}} \to (S_{\mathbb{F}} \oplus_{\mathbb{F}} I)/I$，其核为 $S_{\mathbb{F}} \cap I$。

**第三同构定理**：考虑自然投影的复合，应用第一同构定理。 ∎

## 推论 35.1（φ-环同态理论的完备性）
φ-环同态理论实现了与标准环同态论完全等价的代数结构：

1. **同态定义**：φ-环同态与标准环同态等价
2. **核像理论**：φ-核和像的结构与标准核像对应
3. **同构定理**：φ-Noether同构定理与标准版本对应
4. **基本定理**：φ-环同态基本定理与标准基本定理等价
5. **结构保持性**：所有环同态性质都通过同构保持

这为φ-多项式环理论和φ-代数几何提供了完整的环同态理论基础。

**证明：**
所有性质由定理35.1-35.4综合得出，特别是基本性质（定理35.1）、核像结构（定理35.2）和同构定理（定理35.4）确保了φ-环同态理论的完备性。 ∎