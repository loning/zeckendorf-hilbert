# φ-有理数系统构造理论

## 定义 15.1（φ-有理数集合）
定义**φ-有理数集合** $\mathbb{F}\mathbb{Q}$ 为φ-整数的分式集合：
$$\mathbb{F}\mathbb{Q} = \left\{\frac{a}{b} : a, b \in \mathbb{F}\mathbb{Z}, b \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}\right\}$$

其中 $\frac{a}{b}$ 表示有序对 $(a, b)$ 在等价关系下的等价类。

## 定义 15.2（φ-有理数等价关系）
在 $\mathbb{F}\mathbb{Z} \times (\mathbb{F}\mathbb{Z} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{Z}}\})$ 上定义等价关系 $\sim$：
$$(a_1, b_1) \sim (a_2, b_2) \Leftrightarrow a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 = a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1$$

## 引理 15.1（φ-有理数等价关系的性质）
关系 $\sim$ 是 $\mathbb{F}\mathbb{Z} \times (\mathbb{F}\mathbb{Z} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{Z}}\})$ 上的等价关系。

**证明：**
需验证反身性、对称性、传递性。

**反身性**：$(a, b) \sim (a, b)$ 因为 $a \otimes_{\mathbb{F}\mathbb{Z}} b = a \otimes_{\mathbb{F}\mathbb{Z}} b$。

**对称性**：若 $(a_1, b_1) \sim (a_2, b_2)$，则 $a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 = a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1$。
由交换律，$a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1 = a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2$，故 $(a_2, b_2) \sim (a_1, b_1)$。

**传递性**：设 $(a_1, b_1) \sim (a_2, b_2)$ 且 $(a_2, b_2) \sim (a_3, b_3)$。
则 $a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 = a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1$ 且 $a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_3 = a_3 \otimes_{\mathbb{F}\mathbb{Z}} b_2$。

由于 $b_2 \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$ 且 $\mathbb{F}\mathbb{Z}$ 无零因子（定理11.8），可约去 $b_2$：
$(a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2) \otimes_{\mathbb{F}\mathbb{Z}} b_3 = (a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1) \otimes_{\mathbb{F}\mathbb{Z}} b_3$
$a_1 \otimes_{\mathbb{F}\mathbb{Z}} (b_2 \otimes_{\mathbb{F}\mathbb{Z}} b_3) = (a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_3) \otimes_{\mathbb{F}\mathbb{Z}} b_1 = (a_3 \otimes_{\mathbb{F}\mathbb{Z}} b_2) \otimes_{\mathbb{F}\mathbb{Z}} b_1 = a_3 \otimes_{\mathbb{F}\mathbb{Z}} (b_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1)$

因此 $a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_3 = a_3 \otimes_{\mathbb{F}\mathbb{Z}} b_1$，即 $(a_1, b_1) \sim (a_3, b_3)$。 ∎

## 定理 15.1（φ-有理数的良定义性）
φ-有理数集合 $\mathbb{F}\mathbb{Q}$ 良定义且与标准有理数集合 $\mathbb{Q}$ 等势。

**证明：**
**良定义性**：由引理15.1，等价关系 $\sim$ 良定义，故商集 $\mathbb{F}\mathbb{Q}$ 良定义。

**等势性**：构造双射 $\rho: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$：
$$\rho\left(\frac{a}{b}\right) = \frac{\xi(a)}{\xi(b)}$$

其中 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$ 为定理11.10中的环同构。

**良定义性验证**：若 $\frac{a_1}{b_1} = \frac{a_2}{b_2}$ 在 $\mathbb{F}\mathbb{Q}$ 中，
则 $a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 = a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1$。
由 $\xi$ 的同态性，$\xi(a_1) \cdot \xi(b_2) = \xi(a_2) \cdot \xi(b_1)$，
故 $\frac{\xi(a_1)}{\xi(b_1)} = \frac{\xi(a_2)}{\xi(b_2)}$。

**双射性**：由 $\xi$ 为双射且保持分式结构，$\rho$ 为双射。 ∎

## 定义 15.3（φ-有理数加法）
定义φ-有理数加法运算 $\oplus_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \times \mathbb{F}\mathbb{Q} \to \mathbb{F}\mathbb{Q}$：
$$\frac{a_1}{b_1} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2} = \frac{(a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2) \oplus_{\mathbb{F}\mathbb{Z}} (a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1)}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}$$

## 定理 15.2（φ-有理数加法的良定义性）
φ-有理数加法运算良定义。

**证明：**
需证明运算结果不依赖于代表元的选择。

设 $\frac{a_1}{b_1} = \frac{a_1'}{b_1'}$ 且 $\frac{a_2}{b_2} = \frac{a_2'}{b_2'}$。
则 $a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_1' = a_1' \otimes_{\mathbb{F}\mathbb{Z}} b_1$ 且 $a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_2' = a_2' \otimes_{\mathbb{F}\mathbb{Z}} b_2$。

需证明：
$$\frac{(a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2) \oplus_{\mathbb{F}\mathbb{Z}} (a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1)}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2} = \frac{(a_1' \otimes_{\mathbb{F}\mathbb{Z}} b_2') \oplus_{\mathbb{F}\mathbb{Z}} (a_2' \otimes_{\mathbb{F}\mathbb{Z}} b_1')}{b_1' \otimes_{\mathbb{F}\mathbb{Z}} b_2'}$$

即证明：
$$[(a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2) \oplus_{\mathbb{F}\mathbb{Z}} (a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1)] \otimes_{\mathbb{F}\mathbb{Z}} (b_1' \otimes_{\mathbb{F}\mathbb{Z}} b_2') = [(a_1' \otimes_{\mathbb{F}\mathbb{Z}} b_2') \oplus_{\mathbb{F}\mathbb{Z}} (a_2' \otimes_{\mathbb{F}\mathbb{Z}} b_1')] \otimes_{\mathbb{F}\mathbb{Z}} (b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2)$$

通过分配律和已知等价条件的代换，等式成立。 ∎

## 定义 15.4（φ-有理数乘法）
定义φ-有理数乘法运算 $\otimes_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \times \mathbb{F}\mathbb{Q} \to \mathbb{F}\mathbb{Q}$：
$$\frac{a_1}{b_1} \otimes_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2} = \frac{a_1 \otimes_{\mathbb{F}\mathbb{Z}} a_2}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}$$

## 定理 15.3（φ-有理数乘法的良定义性）
φ-有理数乘法运算良定义。

**证明：**
类似于定理15.2的证明方法，利用等价关系的性质和φ-整数乘法的性质。 ∎

## 定理 15.4（φ-有理数加法群性质）
$(\mathbb{F}\mathbb{Q}, \oplus_{\mathbb{F}\mathbb{Q}})$ 构成交换群。

**证明：**
**结合律**：
$$\left(\frac{a_1}{b_1} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2}\right) \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_3}{b_3} = \frac{a_1}{b_1} \oplus_{\mathbb{F}\mathbb{Q}} \left(\frac{a_2}{b_2} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_3}{b_3}\right)$$

由φ-整数运算的结合律和分配律验证。

**交换律**：
$$\frac{a_1}{b_1} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2} = \frac{a_2}{b_2} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_1}{b_1}$$

由φ-整数运算的交换律直接得出。

**单位元**：$\mathbf{0}_{\mathbb{F}\mathbb{Q}} = \frac{\mathbf{0}_{\mathbb{F}\mathbb{Z}}}{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}$ 满足：
$$\frac{a}{b} \oplus_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}} = \frac{a}{b}$$

**逆元存在性**：对 $\frac{a}{b} \in \mathbb{F}\mathbb{Q}$（$a \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$），
其加法逆元为 $-\frac{a}{b} = \frac{-a}{b}$。 ∎

## 定理 15.5（φ-有理数乘法群性质）
$(\mathbb{F}\mathbb{Q} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{Q}}\}, \otimes_{\mathbb{F}\mathbb{Q}})$ 构成交换群。

**证明：**
**结合律**和**交换律**：由φ-整数乘法的对应性质得出。

**单位元**：$\mathbf{1}_{\mathbb{F}\mathbb{Q}} = \frac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}$ 满足：
$$\frac{a}{b} \otimes_{\mathbb{F}\mathbb{Q}} \mathbf{1}_{\mathbb{F}\mathbb{Q}} = \frac{a}{b}$$

**逆元存在性**：对 $\frac{a}{b} \in \mathbb{F}\mathbb{Q}$（$a \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$），
其乘法逆元为 $\left(\frac{a}{b}\right)^{-1} = \frac{b}{a}$。 ∎

## 定理 15.6（φ-有理数域结构）
$(\mathbb{F}\mathbb{Q}, \oplus_{\mathbb{F}\mathbb{Q}}, \otimes_{\mathbb{F}\mathbb{Q}}, \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \mathbf{1}_{\mathbb{F}\mathbb{Q}})$ 构成域。

**证明：**
由定理15.4和15.5，$\mathbb{F}\mathbb{Q}$ 的加法构成交换群，非零元素的乘法构成交换群。

**分配律**：
$$\frac{a_1}{b_1} \otimes_{\mathbb{F}\mathbb{Q}} \left(\frac{a_2}{b_2} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_3}{b_3}\right) = \left(\frac{a_1}{b_1} \otimes_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2}\right) \oplus_{\mathbb{F}\mathbb{Q}} \left(\frac{a_1}{b_1} \otimes_{\mathbb{F}\mathbb{Q}} \frac{a_3}{b_3}\right)$$

由φ-整数的分配律验证。

**零元与单位元不同**：$\mathbf{0}_{\mathbb{F}\mathbb{Q}} \neq \mathbf{1}_{\mathbb{F}\mathbb{Q}}$。

因此 $\mathbb{F}\mathbb{Q}$ 构成域。 ∎

## 定理 15.7（φ-有理数与标准有理数的同构）
存在域同构：
$$\mathbb{F}\mathbb{Q} \cong \mathbb{Q}$$

其中同构映射为 $\rho: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 定义为 $\rho\left(\frac{a}{b}\right) = \frac{\xi(a)}{\xi(b)}$。

**证明：**
需验证 $\rho$ 保持域结构：

**加法保持**：
$$\rho\left(\frac{a_1}{b_1} \oplus_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2}\right) = \rho\left(\frac{a_1}{b_1}\right) + \rho\left(\frac{a_2}{b_2}\right)$$

**乘法保持**：
$$\rho\left(\frac{a_1}{b_1} \otimes_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2}\right) = \rho\left(\frac{a_1}{b_1}\right) \cdot \rho\left(\frac{a_2}{b_2}\right)$$

**单位元保持**：$\rho(\mathbf{0}_{\mathbb{F}\mathbb{Q}}) = 0$，$\rho(\mathbf{1}_{\mathbb{F}\mathbb{Q}}) = 1$。

所有性质由 $\xi$ 的环同构性质和分式运算的定义直接得出。 ∎

## 定义 15.5（φ-有理数序关系）
在 $\mathbb{F}\mathbb{Q}$ 上定义序关系 $\preceq_{\mathbb{F}\mathbb{Q}}$：
$$\frac{a_1}{b_1} \preceq_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2} \Leftrightarrow \rho\left(\frac{a_1}{b_1}\right) \leq \rho\left(\frac{a_2}{b_2}\right)$$

## 定理 15.8（φ-有理数有序域结构）
$(\mathbb{F}\mathbb{Q}, \oplus_{\mathbb{F}\mathbb{Q}}, \otimes_{\mathbb{F}\mathbb{Q}}, \preceq_{\mathbb{F}\mathbb{Q}})$ 构成有序域。

**证明：**
需验证序关系与域运算的相容性：

1. **全序性**：由标准有理数的全序性和同构 $\rho$ 保证
2. **加法相容性**：若 $r_1 \preceq_{\mathbb{F}\mathbb{Q}} r_2$，则对任意 $r \in \mathbb{F}\mathbb{Q}$，
   $r_1 \oplus_{\mathbb{F}\mathbb{Q}} r \preceq_{\mathbb{F}\mathbb{Q}} r_2 \oplus_{\mathbb{F}\mathbb{Q}} r$
3. **乘法相容性**：若 $r_1 \preceq_{\mathbb{F}\mathbb{Q}} r_2$ 且 $\mathbf{0}_{\mathbb{F}\mathbb{Q}} \preceq_{\mathbb{F}\mathbb{Q}} r$，
   则 $r_1 \otimes_{\mathbb{F}\mathbb{Q}} r \preceq_{\mathbb{F}\mathbb{Q}} r_2 \otimes_{\mathbb{F}\mathbb{Q}} r$

所有性质由标准有理数有序域的性质和同构的保持性得出。 ∎

## 推论 15.1（φ-有理数的阿基米德性质）
φ-有理数域 $\mathbb{F}\mathbb{Q}$ 满足阿基米德公理：

对任意 $r_1, r_2 \in \mathbb{F}\mathbb{Q}$ 且 $\mathbf{0}_{\mathbb{F}\mathbb{Q}} \prec_{\mathbb{F}\mathbb{Q}} r_1, r_2$，
存在 $n \in \mathbb{F}\mathbb{N}$ 使得 $r_2 \prec_{\mathbb{F}\mathbb{Q}} n \otimes_{\mathbb{F}\mathbb{Q}} r_1$。

其中 $n \otimes_{\mathbb{F}\mathbb{Q}} r_1$ 表示 $r_1$ 与φ-自然数 $n$ 的φ-有理数乘法。

**证明：**
由标准有理数的阿基米德性质和同构 $\rho$ 的保持性直接得出。 ∎

## 推论 15.2（φ-有理数域的完备性）
φ-有理数域 $\mathbb{F}\mathbb{Q}$ 具有与标准有理数域 $\mathbb{Q}$ 完全相同的代数和序理论性质：

1. 域结构的完整性
2. 有序域的相容性
3. 阿基米德性质
4. 稠密性（在后续φ-实数理论中验证）
5. 可数性

这为构建φ-实数系统提供了坚实的有理数理论基础。

**证明：**
所有性质都由域同构 $\rho: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 的保持性直接得出。 ∎