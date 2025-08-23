# φ-整数运算的扩展理论

## 定义 12.1（φ-整数运算扩展）
基于定义11.4和11.5，φ-整数的四则运算通过双射 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$ 完全定义：

对所有 $z_1, z_2 \in \mathbb{F}\mathbb{Z}$：
$$z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2 = \xi^{-1}(\xi(z_1) + \xi(z_2))$$
$$z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 = \xi^{-1}(\xi(z_1) \cdot \xi(z_2))$$

## 定理 12.1（φ-整数减法运算）
定义φ-整数减法运算 $\ominus_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \times \mathbb{F}\mathbb{Z} \to \mathbb{F}\mathbb{Z}$ 为：
$$z_1 \ominus_{\mathbb{F}\mathbb{Z}} z_2 = z_1 \oplus_{\mathbb{F}\mathbb{Z}} (-z_2)$$

其中 $-z_2$ 为 $z_2$ 的加法逆元。

**证明：**
由定理11.3的逆元存在性，每个 $z \in \mathbb{F}\mathbb{Z}$ 都有唯一的加法逆元 $-z$。
因此减法运算良定义且唯一。

**减法的显式表示**：
$$z_1 \ominus_{\mathbb{F}\mathbb{Z}} z_2 = \xi^{-1}(\xi(z_1) - \xi(z_2))$$

其中右边的 $-$ 为标准整数减法。 ∎

## 定理 12.2（φ-整数除法的完整定义）
扩展定义8.1至φ-整数除法 $\div_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \times (\mathbb{F}\mathbb{Z} \setminus \{\mathbf{0}_{\mathbb{F}\mathbb{Z}}\}) \to \mathbb{F}\mathbb{Z} \times \mathbb{F}\mathbb{Z}$：

对 $z_1, z_2 \in \mathbb{F}\mathbb{Z}$ 且 $z_2 \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$：
$$z_1 \div_{\mathbb{F}\mathbb{Z}} z_2 = (\xi^{-1}(q), \xi^{-1}(r))$$

其中 $q, r \in \mathbb{Z}$ 满足：
$$\xi(z_1) = q \cdot \xi(z_2) + r \quad \text{且} \quad 0 \leq |r| < |\xi(z_2)|$$

**证明：**
标准整数除法的存在性和唯一性保证了对任意 $\xi(z_1), \xi(z_2) \in \mathbb{Z}$ 且 $\xi(z_2) \neq 0$，
存在唯一的 $q, r \in \mathbb{Z}$ 满足上述条件。

由双射 $\xi^{-1}$ 的存在性，φ-整数除法良定义。 ∎

## 定理 12.3（φ-整数幂运算扩展）
定义φ-整数幂运算 $\uparrow_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \times \mathbb{N} \to \mathbb{F}\mathbb{Z}$：

对 $z \in \mathbb{F}\mathbb{Z}$ 和 $n \in \mathbb{N}$：
$$z \uparrow_{\mathbb{F}\mathbb{Z}} n = \xi^{-1}((\xi(z))^n)$$

其中右边的指数运算为标准整数幂运算。

**基本性质**：
1. **零指数**：$z \uparrow_{\mathbb{F}\mathbb{Z}} 0 = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$ 对所有 $z \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$
2. **单位指数**：$z \uparrow_{\mathbb{F}\mathbb{Z}} 1 = z$ 对所有 $z \in \mathbb{F}\mathbb{Z}$
3. **幂的乘积律**：$z \uparrow_{\mathbb{F}\mathbb{Z}} (m+n) = (z \uparrow_{\mathbb{F}\mathbb{Z}} m) \otimes_{\mathbb{F}\mathbb{Z}} (z \uparrow_{\mathbb{F}\mathbb{Z}} n)$

**证明：**
所有性质直接由标准整数幂运算的性质和双射的保持性得出。 ∎

## 引理 12.1（φ-整数符号运算）
对有符号φ-整数的运算，符号规律与标准整数一致：

设 $z_1 = \sigma_1 |z_1|, z_2 = \sigma_2 |z_2|$，其中 $\sigma_1, \sigma_2 \in \{+1, -1\}$，$|z_i|$ 为绝对值：

1. **加法符号**：当 $\sigma_1 = \sigma_2$ 时，$z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2 = \sigma_1 (|z_1| \oplus_\phi |z_2|)$
2. **乘法符号**：$z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 = (\sigma_1 \sigma_2) (|z_1| \otimes_\phi |z_2|)$
3. **除法符号**：$\text{quot}_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = (\sigma_1 \sigma_2) \text{quot}_\phi(|z_1|, |z_2|)$

**证明：**
由双射 $\xi$ 保持符号运算规则，所有性质都由标准整数的符号运算得出。 ∎

## 定理 12.4（φ-整数绝对值运算）
定义φ-整数绝对值函数 $|\cdot|_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \to \mathbb{F}\mathbb{N}$：

$$|z|_{\mathbb{F}\mathbb{Z}} = \begin{cases}
+s & \text{若 } z = +s \\
+s & \text{若 } z = -s \text{ 且 } s \neq \varepsilon \\
+\varepsilon & \text{若 } z = +\varepsilon
\end{cases}$$

**性质**：
1. **非负性**：$|z|_{\mathbb{F}\mathbb{Z}} \in \mathbb{F}\mathbb{N}$ 对所有 $z \in \mathbb{F}\mathbb{Z}$
2. **等价条件**：$|z|_{\mathbb{F}\mathbb{Z}} = \mathbf{0}_{\mathbb{F}\mathbb{Z}} \Leftrightarrow z = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$
3. **乘法性**：$|z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2|_{\mathbb{F}\mathbb{Z}} = |z_1|_{\mathbb{F}\mathbb{Z}} \otimes_\phi |z_2|_{\mathbb{F}\mathbb{Z}}$
4. **三角不等式**：$|z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2|_{\mathbb{F}\mathbb{Z}} \preceq_\phi |z_1|_{\mathbb{F}\mathbb{Z}} \oplus_\phi |z_2|_{\mathbb{F}\mathbb{Z}}$

**证明：**
所有性质都由标准整数绝对值的对应性质和双射的保持性得出。 ∎

## 定理 12.5（φ-整数最大公因数）
扩展定理8.5至φ-整数最大公因数 $\gcd_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \times \mathbb{F}\mathbb{Z} \to \mathbb{F}\mathbb{N}$：

对 $z_1, z_2 \in \mathbb{F}\mathbb{Z}$（不全为零）：
$$\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = \xi^{-1}(\gcd(\xi(z_1), \xi(z_2))) \cap \mathbb{F}\mathbb{N}$$

其中右边的 $\gcd$ 为标准整数最大公因数，$\cap \mathbb{F}\mathbb{N}$ 表示取非负部分。

**性质**：
1. **对称性**：$\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = \gcd_{\mathbb{F}\mathbb{Z}}(z_2, z_1)$
2. **结合性**：$\gcd_{\mathbb{F}\mathbb{Z}}(\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2), z_3) = \gcd_{\mathbb{F}\mathbb{Z}}(z_1, \gcd_{\mathbb{F}\mathbb{Z}}(z_2, z_3))$
3. **整除性**：$\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) \mid_{\mathbb{F}\mathbb{Z}} z_1$ 且 $\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) \mid_{\mathbb{F}\mathbb{Z}} z_2$

**证明：**
由标准整数最大公因数的性质和双射的保持性直接得出。 ∎

## 推论 12.1（φ-整数欧几里得算法）
φ-整数最大公因数可通过扩展欧几里得算法计算：

设 $r_0 = z_1, r_1 = z_2$，定义序列：
$$r_{i+1} = \text{rem}_{\mathbb{F}\mathbb{Z}}(r_{i-1}, r_i) \quad \text{直到} \quad r_k = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$$

则 $\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = |r_{k-1}|_{\mathbb{F}\mathbb{Z}}$。

**证明：**
这是标准欧几里得算法在φ-整数系统中的直接对应。 ∎

## 定理 12.6（φ-整数运算的完全性）
φ-整数运算系统 $(\mathbb{F}\mathbb{Z}, \oplus_{\mathbb{F}\mathbb{Z}}, \otimes_{\mathbb{F}\mathbb{Z}}, \ominus_{\mathbb{F}\mathbb{Z}}, \div_{\mathbb{F}\mathbb{Z}})$ 实现了与标准整数运算的完全等价：

对任意整数运算表达式 $E(n_1, \ldots, n_k)$，存在对应的φ-整数运算表达式 $E_\phi(z_1, \ldots, z_k)$ 使得：
$$\xi(E_\phi(z_1, \ldots, z_k)) = E(\xi(z_1), \ldots, \xi(z_k))$$

**证明：**
由定理13.1-13.5，所有基本运算都保持双射关系。
通过数学归纳法，任意复合运算表达式都保持这一关系。 ∎

## 定理 12.7（φ-整数运算的封闭性）
φ-整数运算在各自定义域内封闭：

1. **加法封闭性**：$z_1, z_2 \in \mathbb{F}\mathbb{Z} \Rightarrow z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2 \in \mathbb{F}\mathbb{Z}$
2. **减法封闭性**：$z_1, z_2 \in \mathbb{F}\mathbb{Z} \Rightarrow z_1 \ominus_{\mathbb{F}\mathbb{Z}} z_2 \in \mathbb{F}\mathbb{Z}$
3. **乘法封闭性**：$z_1, z_2 \in \mathbb{F}\mathbb{Z} \Rightarrow z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 \in \mathbb{F}\mathbb{Z}$
4. **除法定义域**：除法运算在除数非零时良定义

**证明：**
所有封闭性都由双射 $\xi$ 的存在性和标准整数运算的封闭性保证。 ∎

## 推论 12.2（φ-整数运算系统的完备性）
φ-整数运算系统 $(\mathbb{F}\mathbb{Z}, \oplus_{\mathbb{F}\mathbb{Z}}, \ominus_{\mathbb{F}\mathbb{Z}}, \otimes_{\mathbb{F}\mathbb{Z}}, \div_{\mathbb{F}\mathbb{Z}})$ 构成了与标准整数运算完全等价的完备运算系统。

这为后续构建φ-有理数、φ-实数等高层数系提供了坚实的整数理论基础。

**证明：**
由定理13.6和13.7，φ-整数运算具有与标准整数运算相同的完全性和封闭性，
因此构成完备的整数运算系统。 ∎