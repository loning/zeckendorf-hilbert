# φ-多项式环理论

## 定义 36.1（φ-多项式环）
对φ-环 $R_{\mathbb{F}}$ 和不定元 $X$，定义**φ-多项式环** $R_{\mathbb{F}}[X]$ 为形式多项式：
$$R_{\mathbb{F}}[X] = \left\{\sum_{i=0}^n a_i X^i : n \in \mathbb{F}\mathbb{N}, a_i \in R_{\mathbb{F}}\right\}$$

其中 $a_i$ 称为φ-系数，$X^i$ 为不定元的 $i$ 次幂。

## 定义 36.2（φ-多项式运算）
对 $f(X) = \sum_{i=0}^m a_i X^i, g(X) = \sum_{j=0}^n b_j X^j \in R_{\mathbb{F}}[X]$：

**φ-多项式加法**：
$$f(X) \oplus_{\mathbb{F}} g(X) = \sum_{k=0}^{\max(m,n)} (a_k \oplus_{\mathbb{F}} b_k) X^k$$

其中约定 $a_k = \mathbf{0}_{\mathbb{F}}$ 当 $k > m$，$b_k = \mathbf{0}_{\mathbb{F}}$ 当 $k > n$。

**φ-多项式乘法**：
$$f(X) \otimes_{\mathbb{F}} g(X) = \sum_{k=0}^{m+n} \left(\sum_{i+j=k} a_i \otimes_{\mathbb{F}} b_j\right) X^k$$

## 定理 36.1（φ-多项式环的环性质）
$(R_{\mathbb{F}}[X], \oplus_{\mathbb{F}}, \otimes_{\mathbb{F}})$ 构成φ-环。

**证明：**
**加法Abel群性质**：
- **结合律**：继承自φ-系数环的加法结合律
- **交换律**：继承自φ-系数环的加法交换律  
- **零元**：零多项式 $\mathbf{0}(X) = \mathbf{0}_{\mathbb{F}}$
- **逆元**：$-f(X) = \sum (-a_i) X^i$

**乘法幺半群性质**：
- **结合律**：通过系数重新排列验证
- **单位元**：常数多项式 $\mathbf{1}(X) = \mathbf{1}_{\mathbb{F}}$

**分配律**：通过系数的分配律逐项验证。 ∎

## 定义 36.3（φ-多项式的次数和主系数）
对非零φ-多项式 $f(X) = \sum_{i=0}^n a_i X^i \in R_{\mathbb{F}}[X]$，其中 $a_n \neq \mathbf{0}_{\mathbb{F}}$：

- **φ-次数**：$\deg_{\mathbb{F}}(f) = n$
- **φ-主系数**：$\text{lc}_{\mathbb{F}}(f) = a_n$

约定 $\deg_{\mathbb{F}}(\mathbf{0}) = -\infty$。

## 定理 36.2（φ-多项式次数的性质）
对φ-多项式 $f, g \in R_{\mathbb{F}}[X]$：

1. **加法次数律**：$\deg_{\mathbb{F}}(f \oplus_{\mathbb{F}} g) \leq \max(\deg_{\mathbb{F}}(f), \deg_{\mathbb{F}}(g))$
2. **乘法次数律**：$\deg_{\mathbb{F}}(f \otimes_{\mathbb{F}} g) \leq \deg_{\mathbb{F}}(f) + \deg_{\mathbb{F}}(g)$
3. **整环中的等号**：当 $R_{\mathbb{F}}$ 为φ-整环时，上述不等号为等号

**证明：**
**加法次数律**：显然，因为高次项的系数为 $a_m \oplus_{\mathbb{F}} b_m$，可能为零。

**乘法次数律**：$f \otimes_{\mathbb{F}} g$ 的最高次项系数为 $\text{lc}_{\mathbb{F}}(f) \otimes_{\mathbb{F}} \text{lc}_{\mathbb{F}}(g)$。

**整环中的等号**：当 $R_{\mathbb{F}}$ 为φ-整环时，$\text{lc}_{\mathbb{F}}(f) \otimes_{\mathbb{F}} \text{lc}_{\mathbb{F}}(g) \neq \mathbf{0}_{\mathbb{F}}$，
故最高次项不会被消去。 ∎

## 定义 36.4（φ-多项式的除法算法）
设 $R_{\mathbb{F}}$ 为φ-域，$f, g \in R_{\mathbb{F}}[X]$ 且 $g \neq \mathbf{0}$，则存在唯一的 $q, r \in R_{\mathbb{F}}[X]$ 使得：
$$f = q \otimes_{\mathbb{F}} g \oplus_{\mathbb{F}} r$$

其中 $\deg_{\mathbb{F}}(r) < \deg_{\mathbb{F}}(g)$ 或 $r = \mathbf{0}$。

## 定理 36.3（φ-多项式除法算法的正确性）
当 $R_{\mathbb{F}}$ 为φ-域时，φ-多项式除法算法成立。

**证明：**
**存在性**：通过归纳法构造。设 $\deg_{\mathbb{F}}(f) = m, \deg_{\mathbb{F}}(g) = n$。

若 $m < n$，取 $q = \mathbf{0}, r = f$。

若 $m \geq n$，设 $f = a_m X^m + \text{低次项}, g = b_n X^n + \text{低次项}$。
构造 $f_1 = f \ominus_{\mathbb{F}} (a_m \otimes_{\mathbb{F}} b_n^{-1} X^{m-n}) \otimes_{\mathbb{F}} g$，
则 $\deg_{\mathbb{F}}(f_1) < m$。归纳应用得到结果。

**唯一性**：若 $f = q_1 g + r_1 = q_2 g + r_2$，则 $(q_1 - q_2) g = r_2 - r_1$。
由次数性质，若 $q_1 \neq q_2$，则左边次数至少为 $n$，但右边次数小于 $n$，矛盾。 ∎

## 定义 36.5（φ-多项式的根）
设 $f(X) \in R_{\mathbb{F}}[X]$ 和 $r \in R_{\mathbb{F}}$。称 $r$ 为 $f$ 的**φ-根**，当且仅当：
$$f(r) = \sum_{i=0}^n a_i r^i = \mathbf{0}_{\mathbb{F}}$$

## 定理 36.4（φ-因式定理）
设 $R_{\mathbb{F}}$ 为φ-整环，$f(X) \in R_{\mathbb{F}}[X]$，$r \in R_{\mathbb{F}}$，则：

$r$ 为 $f$ 的φ-根当且仅当 $(X \ominus_{\mathbb{F}} r)$ 整除 $f(X)$。

**证明：**
**必要性**：若 $f(r) = \mathbf{0}_{\mathbb{F}}$，由除法算法：
$$f(X) = q(X) \otimes_{\mathbb{F}} (X \ominus_{\mathbb{F}} r) \oplus_{\mathbb{F}} c$$

其中 $c \in R_{\mathbb{F}}$。代入 $X = r$：
$$\mathbf{0}_{\mathbb{F}} = f(r) = q(r) \otimes_{\mathbb{F}} \mathbf{0}_{\mathbb{F}} \oplus_{\mathbb{F}} c = c$$

故 $f(X) = q(X) \otimes_{\mathbb{F}} (X \ominus_{\mathbb{F}} r)$。

**充分性**：若 $f(X) = q(X) \otimes_{\mathbb{F}} (X \ominus_{\mathbb{F}} r)$，则：
$$f(r) = q(r) \otimes_{\mathbb{F}} (r \ominus_{\mathbb{F}} r) = q(r) \otimes_{\mathbb{F}} \mathbf{0}_{\mathbb{F}} = \mathbf{0}_{\mathbb{F}}$$ ∎

## 定理 36.5（φ-多项式根的重数）
设 $R_{\mathbb{F}}$ 为φ-整环，$f(X) \in R_{\mathbb{F}}[X]$ 非零，$r \in R_{\mathbb{F}}$。
$r$ 的**φ-重数** $\text{mult}_{\mathbb{F}}(r, f)$ 定义为最大的 $k \in \mathbb{F}\mathbb{N}$ 使得 $(X \ominus_{\mathbb{F}} r)^k$ 整除 $f(X)$。

非零 $n$ 次φ-多项式最多有 $n$ 个φ-根（计重数）。

**证明：**
**重数定义的良定义性**：由φ-整环的唯一因数分解性质保证。

**根的个数界限**：归纳证明。设 $f$ 为 $n$ 次φ-多项式，$r$ 为φ-根。
由因式定理，$f(X) = (X \ominus_{\mathbb{F}} r) \otimes_{\mathbb{F}} g(X)$，其中 $\deg_{\mathbb{F}}(g) = n-1$。
归纳假设 $g$ 最多有 $n-1$ 个根，故 $f$ 最多有 $n$ 个根。 ∎

## 定理 36.6（φ-多项式环与标准多项式环的对应）
每个φ-多项式环都与标准多项式环同构：

通过环同构 $\phi: R_{\mathbb{F}} \to R$，可构造同构 $\tilde{\phi}: R_{\mathbb{F}}[X] \to R[X]$：
$$\tilde{\phi}\left(\sum a_i X^i\right) = \sum \phi(a_i) X^i$$

**证明：**
**良定义性**：由φ-多项式表示的唯一性和 $\phi$ 的良定义性。

**环同态性**：
- **加法保持**：$\tilde{\phi}(f + g) = \tilde{\phi}(f) + \tilde{\phi}(g)$
- **乘法保持**：$\tilde{\phi}(f \cdot g) = \tilde{\phi}(f) \cdot \tilde{\phi}(g)$

**双射性**：由 $\phi$ 的双射性逐系数继承。

**结构保持**：次数、根、因式分解等所有性质都通过同构保持。 ∎

## 推论 36.1（φ-多项式环理论的完备性）
φ-多项式环理论实现了与标准多项式环论完全等价的代数结构：

1. **环结构等价性**：φ-多项式环与标准多项式环同构
2. **运算等价性**：φ-多项式运算与标准多项式运算对应
3. **次数理论**：φ-次数概念与标准次数概念等价
4. **除法算法**：φ-多项式除法与标准除法对应
5. **根理论**：φ-多项式根与标准多项式根对应
6. **因式分解**：φ-因式定理与标准因式定理等价

这为φ-代数几何学和φ-域扩张理论提供了完整的多项式理论基础。

**证明：**
所有性质由定理36.1-36.6综合得出，特别是环性质（定理36.1）、次数性质（定理36.2）、除法算法（定理36.3）和对应定理（定理36.6）确保了φ-多项式环理论的完备性。 ∎