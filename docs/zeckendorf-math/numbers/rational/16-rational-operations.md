# φ-有理数运算理论

## 定义 16.1（φ-有理数四则运算）
基于φ-有理数域 $(\mathbb{F}\mathbb{Q}, \oplus_{\mathbb{F}\mathbb{Q}}, \otimes_{\mathbb{F}\mathbb{Q}}, \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \mathbf{1}_{\mathbb{F}\mathbb{Q}})$，定义四则运算：

对 $r_1 = \frac{a_1}{b_1}, r_2 = \frac{a_2}{b_2} \in \mathbb{F}\mathbb{Q}$（规范形式）：

**φ-有理数加法**：
$$r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2 = \frac{a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 \oplus_{\mathbb{F}\mathbb{Z}} a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}$$

**φ-有理数乘法**：
$$r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2 = \frac{a_1 \otimes_{\mathbb{F}\mathbb{Z}} a_2}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}$$

其中所有运算结果都约简为规范形式。

## 定理 16.1（φ-有理数减法运算）
定义φ-有理数减法 $\ominus_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \times \mathbb{F}\mathbb{Q} \to \mathbb{F}\mathbb{Q}$：

$$r_1 \ominus_{\mathbb{F}\mathbb{Q}} r_2 = r_1 \oplus_{\mathbb{F}\mathbb{Q}} (-r_2)$$

其中 $-r_2$ 为 $r_2$ 的加法逆元。

**显式计算公式**：
$$r_1 \ominus_{\mathbb{F}\mathbb{Q}} r_2 = \frac{a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 \ominus_{\mathbb{F}\mathbb{Z}} a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}$$

**证明：**
由定理15.4，每个φ-有理数都有唯一的加法逆元。
减法运算的良定义性由φ-整数减法的良定义性（定理13.1）保证。 ∎

## 定理 16.2（φ-有理数除法运算）
定义φ-有理数除法 $\div_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \times (\mathbb{F}\mathbb{Q} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{Q}}\}) \to \mathbb{F}\mathbb{Q}$：

$$r_1 \div_{\mathbb{F}\mathbb{Q}} r_2 = r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2^{-1}$$

其中 $r_2^{-1}$ 为 $r_2$ 的乘法逆元。

**显式计算公式**：
$$\frac{a_1}{b_1} \div_{\mathbb{F}\mathbb{Q}} \frac{a_2}{b_2} = \frac{a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} a_2}$$

其中要求 $a_2 \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$。

**证明：**
由定理15.5，每个非零φ-有理数都有唯一的乘法逆元。
除法运算的良定义性由φ-整数乘法的良定义性保证。 ∎

## 定义 16.2（φ-有理数幂运算）
定义φ-有理数幂运算 $\uparrow_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \times \mathbb{F}\mathbb{Z} \to \mathbb{F}\mathbb{Q}$：

对 $r = \frac{a}{b} \in \mathbb{F}\mathbb{Q}$ 和 $n \in \mathbb{F}\mathbb{Z}$：

$$r \uparrow_{\mathbb{F}\mathbb{Q}} n = \begin{cases}
\frac{a \uparrow_{\mathbb{F}\mathbb{Z}} n}{b \uparrow_{\mathbb{F}\mathbb{Z}} n} & \text{若 } n \succeq_{\mathbb{F}\mathbb{Z}} \mathbf{0}_{\mathbb{F}\mathbb{Z}} \\
\frac{b \uparrow_{\mathbb{F}\mathbb{Z}} |n|_{\mathbb{F}\mathbb{Z}}}{a \uparrow_{\mathbb{F}\mathbb{Z}} |n|_{\mathbb{F}\mathbb{Z}}} & \text{若 } n \prec_{\mathbb{F}\mathbb{Z}} \mathbf{0}_{\mathbb{F}\mathbb{Z}} \text{ 且 } a \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}
\end{cases}$$

## 定理 16.3（φ-有理数幂运算的性质）
φ-有理数幂运算满足：

1. **零指数性质**：$r \uparrow_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Z}} = \mathbf{1}_{\mathbb{F}\mathbb{Q}}$ 对所有 $r \neq \mathbf{0}_{\mathbb{F}\mathbb{Q}}$
2. **单位指数性质**：$r \uparrow_{\mathbb{F}\mathbb{Q}} \mathbf{1}_{\mathbb{F}\mathbb{Z}} = r$ 对所有 $r \in \mathbb{F}\mathbb{Q}$
3. **幂的乘法律**：$r \uparrow_{\mathbb{F}\mathbb{Q}} (m \oplus_{\mathbb{F}\mathbb{Z}} n) = (r \uparrow_{\mathbb{F}\mathbb{Q}} m) \otimes_{\mathbb{F}\mathbb{Q}} (r \uparrow_{\mathbb{F}\mathbb{Q}} n)$
4. **乘积的幂律**：$(r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2) \uparrow_{\mathbb{F}\mathbb{Q}} n = (r_1 \uparrow_{\mathbb{F}\mathbb{Q}} n) \otimes_{\mathbb{F}\mathbb{Q}} (r_2 \uparrow_{\mathbb{F}\mathbb{Q}} n)$
5. **幂的幂律**：$(r \uparrow_{\mathbb{F}\mathbb{Q}} m) \uparrow_{\mathbb{F}\mathbb{Q}} n = r \uparrow_{\mathbb{F}\mathbb{Q}} (m \otimes_{\mathbb{F}\mathbb{Z}} n)$

**证明：**
所有性质都由φ-整数幂运算的对应性质（定理13.3）和分数运算的定义直接得出。 ∎

## 定理 16.4（φ-有理数运算的封闭性）
φ-有理数四则运算在 $\mathbb{F}\mathbb{Q}$ 中封闭：

1. **加法封闭性**：$r_1, r_2 \in \mathbb{F}\mathbb{Q} \Rightarrow r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2 \in \mathbb{F}\mathbb{Q}$
2. **减法封闭性**：$r_1, r_2 \in \mathbb{F}\mathbb{Q} \Rightarrow r_1 \ominus_{\mathbb{F}\mathbb{Q}} r_2 \in \mathbb{F}\mathbb{Q}$
3. **乘法封闭性**：$r_1, r_2 \in \mathbb{F}\mathbb{Q} \Rightarrow r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2 \in \mathbb{F}\mathbb{Q}$
4. **除法封闭性**：$r_1 \in \mathbb{F}\mathbb{Q}, r_2 \in \mathbb{F}\mathbb{Q} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{Q}}\} \Rightarrow r_1 \div_{\mathbb{F}\mathbb{Q}} r_2 \in \mathbb{F}\mathbb{Q}$

**证明：**
所有封闭性都由φ-整数运算的封闭性（定理13.7）和分数运算的定义保证。
结果的规范化不改变其属于 $\mathbb{F}\mathbb{Q}$ 的性质。 ∎

## 定理 16.5（φ-有理数运算与标准有理数运算的等价性）
存在自然的运算保持同构 $\eta: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$，使得：

$$\eta(r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2) = \eta(r_1) + \eta(r_2)$$

$$\eta(r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2) = \eta(r_1) \cdot \eta(r_2)$$

$$\eta(r_1 \ominus_{\mathbb{F}\mathbb{Q}} r_2) = \eta(r_1) - \eta(r_2)$$

$$\eta(r_1 \div_{\mathbb{F}\mathbb{Q}} r_2) = \eta(r_1) / \eta(r_2)$$

**证明：**
构造 $\eta(\frac{a}{b}) = \frac{\xi(a)}{\xi(b)}$，其中 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$ 为定理11.10中的环同构。

**加法等价性**：
$$\eta(r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2) = \eta\left(\frac{a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 \oplus_{\mathbb{F}\mathbb{Z}} a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1}{b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2}\right)$$

$$= \frac{\xi(a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 \oplus_{\mathbb{F}\mathbb{Z}} a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1)}{\xi(b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2)}$$

$$= \frac{\xi(a_1) \cdot \xi(b_2) + \xi(a_2) \cdot \xi(b_1)}{\xi(b_1) \cdot \xi(b_2)} = \frac{\xi(a_1)}{\xi(b_1)} + \frac{\xi(a_2)}{\xi(b_2)} = \eta(r_1) + \eta(r_2)$$

其他运算的等价性类似证明。 ∎

## 定理 16.6（φ-有理数运算的代数性质）
φ-有理数运算满足域的所有代数律：

**加法代数律**：
1. **结合律**：$(r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2) \oplus_{\mathbb{F}\mathbb{Q}} r_3 = r_1 \oplus_{\mathbb{F}\mathbb{Q}} (r_2 \oplus_{\mathbb{F}\mathbb{Q}} r_3)$
2. **交换律**：$r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2 = r_2 \oplus_{\mathbb{F}\mathbb{Q}} r_1$
3. **单位元**：$r \oplus_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}} = r$
4. **逆元性**：$r \oplus_{\mathbb{F}\mathbb{Q}} (-r) = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$

**乘法代数律**：
1. **结合律**：$(r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2) \otimes_{\mathbb{F}\mathbb{Q}} r_3 = r_1 \otimes_{\mathbb{F}\mathbb{Q}} (r_2 \otimes_{\mathbb{F}\mathbb{Q}} r_3)$
2. **交换律**：$r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2 = r_2 \otimes_{\mathbb{F}\mathbb{Q}} r_1$
3. **单位元**：$r \otimes_{\mathbb{F}\mathbb{Q}} \mathbf{1}_{\mathbb{F}\mathbb{Q}} = r$
4. **逆元性**：$r \otimes_{\mathbb{F}\mathbb{Q}} r^{-1} = \mathbf{1}_{\mathbb{F}\mathbb{Q}}$ 对所有 $r \neq \mathbf{0}_{\mathbb{F}\mathbb{Q}}$

**分配律**：
$$r_1 \otimes_{\mathbb{F}\mathbb{Q}} (r_2 \oplus_{\mathbb{F}\mathbb{Q}} r_3) = (r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2) \oplus_{\mathbb{F}\mathbb{Q}} (r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_3)$$

**证明：**
所有性质都由域同构 $\eta: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 和标准有理数域的对应性质保证。 ∎

## 定理 16.7（φ-有理数序关系运算相容性）
φ-有理数的序关系与运算相容：

1. **加法单调性**：若 $r_1 \preceq_{\mathbb{F}\mathbb{Q}} r_2$，则 $r_1 \oplus_{\mathbb{F}\mathbb{Q}} r \preceq_{\mathbb{F}\mathbb{Q}} r_2 \oplus_{\mathbb{F}\mathbb{Q}} r$
2. **乘法保序性**：若 $r_1 \preceq_{\mathbb{F}\mathbb{Q}} r_2$ 且 $r \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，则 $r_1 \otimes_{\mathbb{F}\mathbb{Q}} r \preceq_{\mathbb{F}\mathbb{Q}} r_2 \otimes_{\mathbb{F}\mathbb{Q}} r$
3. **乘法反序性**：若 $r_1 \preceq_{\mathbb{F}\mathbb{Q}} r_2$ 且 $r \prec_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，则 $r_1 \otimes_{\mathbb{F}\mathbb{Q}} r \succeq_{\mathbb{F}\mathbb{Q}} r_2 \otimes_{\mathbb{F}\mathbb{Q}} r$

**证明：**
由定理15.8的序同构性质和标准有理数的序运算相容性直接得出。 ∎

## 定理 16.8（φ-有理数绝对值运算）
定义φ-有理数绝对值函数 $|\cdot|_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \to \mathbb{F}\mathbb{Q}_{\geq 0}$：

$$\left|\frac{a}{b}\right|_{\mathbb{F}\mathbb{Q}} = \frac{|a|_{\mathbb{F}\mathbb{Z}}}{|b|_{\mathbb{F}\mathbb{Z}}}$$

其中 $|\cdot|_{\mathbb{F}\mathbb{Z}}$ 为定理13.4中的φ-整数绝对值。

**性质**：
1. **非负性**：$|r|_{\mathbb{F}\mathbb{Q}} \succeq_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$ 对所有 $r \in \mathbb{F}\mathbb{Q}$
2. **零化性**：$|r|_{\mathbb{F}\mathbb{Q}} = \mathbf{0}_{\mathbb{F}\mathbb{Q}} \Leftrightarrow r = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$
3. **乘法性**：$|r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2|_{\mathbb{F}\mathbb{Q}} = |r_1|_{\mathbb{F}\mathbb{Q}} \otimes_{\mathbb{F}\mathbb{Q}} |r_2|_{\mathbb{F}\mathbb{Q}}$
4. **三角不等式**：$|r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2|_{\mathbb{F}\mathbb{Q}} \preceq_{\mathbb{F}\mathbb{Q}} |r_1|_{\mathbb{F}\mathbb{Q}} \oplus_{\mathbb{F}\mathbb{Q}} |r_2|_{\mathbb{F}\mathbb{Q}}$

**证明：**
所有性质都由φ-整数绝对值的对应性质和分数运算的定义得出。 ∎

## 定理 16.9（φ-有理数距离函数）
定义φ-有理数距离函数 $d_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \times \mathbb{F}\mathbb{Q} \to \mathbb{F}\mathbb{Q}_{\geq 0}$：

$$d_{\mathbb{F}\mathbb{Q}}(r_1, r_2) = |r_1 \ominus_{\mathbb{F}\mathbb{Q}} r_2|_{\mathbb{F}\mathbb{Q}}$$

此距离函数满足度量空间公理：
1. **非负性**：$d_{\mathbb{F}\mathbb{Q}}(r_1, r_2) \succeq_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$
2. **同一性**：$d_{\mathbb{F}\mathbb{Q}}(r_1, r_2) = \mathbf{0}_{\mathbb{F}\mathbb{Q}} \Leftrightarrow r_1 = r_2$
3. **对称性**：$d_{\mathbb{F}\mathbb{Q}}(r_1, r_2) = d_{\mathbb{F}\mathbb{Q}}(r_2, r_1)$
4. **三角不等式**：$d_{\mathbb{F}\mathbb{Q}}(r_1, r_3) \preceq_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(r_1, r_2) \oplus_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(r_2, r_3)$

**证明：**
所有性质都由φ-有理数绝对值的性质（定理17.8）和减法的定义得出。 ∎

## 定理 16.10（φ-有理数运算的连续性）
所有φ-有理数运算在距离度量 $d_{\mathbb{F}\mathbb{Q}}$ 下连续：

对于 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $\delta \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$ 使得：

**加法连续性**：
$$d_{\mathbb{F}\mathbb{Q}}(r_1, r_1') \prec_{\mathbb{F}\mathbb{Q}} \delta \wedge d_{\mathbb{F}\mathbb{Q}}(r_2, r_2') \prec_{\mathbb{F}\mathbb{Q}} \delta$$

$$\Rightarrow d_{\mathbb{F}\mathbb{Q}}(r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2, r_1' \oplus_{\mathbb{F}\mathbb{Q}} r_2') \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

**乘法连续性**：
$$d_{\mathbb{F}\mathbb{Q}}(r_1, r_1') \prec_{\mathbb{F}\mathbb{Q}} \delta \wedge d_{\mathbb{F}\mathbb{Q}}(r_2, r_2') \prec_{\mathbb{F}\mathbb{Q}} \delta$$

$$\Rightarrow d_{\mathbb{F}\mathbb{Q}}(r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2, r_1' \otimes_{\mathbb{F}\mathbb{Q}} r_2') \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

**证明：**
由域同构 $\eta: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 和标准有理数运算的连续性直接得出。 ∎

## 定理 16.11（φ-有理数编码运算）
φ-有理数的编码运算可通过编码直接进行：

设 $r_1, r_2 \in \mathbb{F}\mathbb{Q}$ 的编码分别为：
- $\text{encode}_{\mathbb{F}\mathbb{Q}}(r_1) = (\sigma_1, E_{a_1}, E_{b_1})$
- $\text{encode}_{\mathbb{F}\mathbb{Q}}(r_2) = (\sigma_2, E_{a_2}, E_{b_2})$

则运算结果的编码可通过以下算法计算：

**加法编码算法**：
1. 解码得到 $a_1, b_1, a_2, b_2 \in \mathbb{F}\mathbb{Z}$
2. 计算 $a = a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 \oplus_{\mathbb{F}\mathbb{Z}} a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1$
3. 计算 $b = b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2$
4. 约简 $\frac{a}{b}$ 为规范形式并重新编码

**乘法编码算法**：
1. 解码得到 $a_1, b_1, a_2, b_2 \in \mathbb{F}\mathbb{Z}$
2. 计算 $a = a_1 \otimes_{\mathbb{F}\mathbb{Z}} a_2$，$b = b_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2$
3. 约简 $\frac{a}{b}$ 为规范形式并重新编码

**证明：**
算法的正确性由定理17.1和16.2（编码的双射性）保证。 ∎

## 推论 16.1（φ-有理数运算系统的完备性）
φ-有理数运算系统 $(\mathbb{F}\mathbb{Q}, \oplus_{\mathbb{F}\mathbb{Q}}, \ominus_{\mathbb{F}\mathbb{Q}}, \otimes_{\mathbb{F}\mathbb{Q}}, \div_{\mathbb{F}\mathbb{Q}})$ 构成了与标准有理数运算完全等价的完备域：

1. **域结构**：满足域的所有公理
2. **运算等价性**：与标准有理数运算一一对应
3. **序兼容性**：序关系与运算完全相容
4. **编码可实现性**：所有运算都可通过编码算法实现
5. **度量完备性**：具有完整的距离度量结构

这为构建φ-实数系统提供了完整的有理数理论基础。

**证明：**
所有性质由前述定理17.1-17.11综合得出。特别地：
- 域结构由定理17.6保证
- 运算等价性由定理17.5保证
- 序兼容性由定理17.7保证
- 编码可实现性由定理17.11保证
- 度量完备性由定理17.9-17.10保证 ∎