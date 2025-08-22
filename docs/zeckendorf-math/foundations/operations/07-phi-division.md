# φ-除法运算理论

## 定义 8.1（φ-除法运算）
定义φ-除法运算 $\div_\phi: \mathbb{F}\mathbb{N} \times (\mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}) \to \mathbb{F}\mathbb{N} \times \mathbb{F}\mathbb{N}$ 为：
$$s_1 \div_\phi s_2 = (\psi(q), \psi(r))$$

其中 $q, r \in \mathbb{N}$ 满足：
$$\omega(s_1) = q \cdot \omega(s_2) + r \quad \text{且} \quad 0 \leq r < \omega(s_2)$$

## 定理 8.1（φ-除法的良定义性与唯一性）
对所有 $s_1 \in \mathbb{F}\mathbb{N}$ 和 $s_2 \in \mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}$，φ-除法运算良定义且结果唯一。

**证明：**
设 $n_1 = \omega(s_1), n_2 = \omega(s_2)$。由于 $s_2 \neq \mathbf{0}_\phi$，有 $n_2 > 0$。

由自然数除法的存在性和唯一性，存在唯一的 $q, r \in \mathbb{N}$ 使得：
$$n_1 = q \cdot n_2 + r \quad \text{且} \quad 0 \leq r < n_2$$

由双射 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 的存在性，$\psi(q)$ 和 $\psi(r)$ 唯一确定。

因此 $s_1 \div_\phi s_2 = (\psi(q), \psi(r))$ 良定义且唯一。 ∎

## 定义 8.2（φ-商与φ-余数）
设 $s_1 \div_\phi s_2 = (q_\phi, r_\phi)$，定义：
- **φ-商**：$\text{quot}_\phi(s_1, s_2) = q_\phi$
- **φ-余数**：$\text{rem}_\phi(s_1, s_2) = r_\phi$

## 定理 8.2（φ-除法基本性质）
对所有 $s_1 \in \mathbb{F}\mathbb{N}$ 和 $s_2 \in \mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}$：

1. **除法恒等式**：$s_1 = (\text{quot}_\phi(s_1, s_2) \otimes_\phi s_2) \oplus_\phi \text{rem}_\phi(s_1, s_2)$

2. **余数界限**：$\text{rem}_\phi(s_1, s_2) \prec_\phi s_2$

其中 $\prec_\phi$ 为严格φ-序关系。

**证明：**
1. 设 $(q_\phi, r_\phi) = s_1 \div_\phi s_2$，则：
   $$\begin{align}
   (q_\phi \otimes_\phi s_2) \oplus_\phi r_\phi &= \psi(\omega(q_\phi) \cdot \omega(s_2)) \oplus_\phi r_\phi \\
   &= \psi(q \cdot \omega(s_2) + \omega(r_\phi)) \\
   &= \psi(q \cdot \omega(s_2) + r) \\
   &= \psi(\omega(s_1)) = s_1
   \end{align}$$

2. 由定义，$0 \leq r < \omega(s_2)$，故 $\omega(r_\phi) < \omega(s_2)$，即 $r_\phi \prec_\phi s_2$。 ∎

## 定理 8.3（φ-除法与标准除法的等价性）
φ-除法运算与自然数除法语义等价：
$$\omega(\text{quot}_\phi(s_1, s_2)) = \lfloor \omega(s_1) / \omega(s_2) \rfloor$$
$$\omega(\text{rem}_\phi(s_1, s_2)) = \omega(s_1) \bmod \omega(s_2)$$

**证明：**
直接由定义8.1和双射性质 $\omega \circ \psi = \text{id}_\mathbb{N}$ 得出。 ∎

## 定理 8.4（φ-除法的单调性质）
对所有 $s_1, s_2 \in \mathbb{F}\mathbb{N}$ 和 $d \in \mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}$：

$$s_1 \preceq_\phi s_2 \Rightarrow \text{quot}_\phi(s_1, d) \preceq_\phi \text{quot}_\phi(s_2, d)$$

**证明：**
若 $s_1 \preceq_\phi s_2$，则 $\omega(s_1) \leq \omega(s_2)$。
由除法的单调性，$\lfloor \omega(s_1) / \omega(d) \rfloor \leq \lfloor \omega(s_2) / \omega(d) \rfloor$。
因此 $\omega(\text{quot}_\phi(s_1, d)) \leq \omega(\text{quot}_\phi(s_2, d))$，
即 $\text{quot}_\phi(s_1, d) \preceq_\phi \text{quot}_\phi(s_2, d)$。 ∎

## 引理 8.1（φ-整除性）
定义 $s_1$ **φ-整除** $s_2$（记作 $s_1 \mid_\phi s_2$）当且仅当 $\text{rem}_\phi(s_2, s_1) = \mathbf{0}_\phi$。

等价地，$s_1 \mid_\phi s_2$ 当且仅当存在 $q \in \mathbb{F}\mathbb{N}$ 使得 $s_2 = q \otimes_\phi s_1$。

**证明：**
**必要性**：若 $\text{rem}_\phi(s_2, s_1) = \mathbf{0}_\phi$，则由定理8.2，
$s_2 = (\text{quot}_\phi(s_2, s_1) \otimes_\phi s_1) \oplus_\phi \mathbf{0}_\phi = \text{quot}_\phi(s_2, s_1) \otimes_\phi s_1$。

**充分性**：若 $s_2 = q \otimes_\phi s_1$ 对某个 $q \in \mathbb{F}\mathbb{N}$，则
$\omega(s_2) = \omega(q) \cdot \omega(s_1) + 0$，故 $\text{rem}_\phi(s_2, s_1) = \psi(0) = \mathbf{0}_\phi$。 ∎

## 定理 8.5（φ-最大公因数的存在性）
对任意 $s_1, s_2 \in \mathbb{F}\mathbb{N}$（不全为零），存在唯一的 $\gcd_\phi(s_1, s_2) \in \mathbb{F}\mathbb{N}$ 满足：

1. $\gcd_\phi(s_1, s_2) \mid_\phi s_1$ 且 $\gcd_\phi(s_1, s_2) \mid_\phi s_2$
2. 若 $d \mid_\phi s_1$ 且 $d \mid_\phi s_2$，则 $d \mid_\phi \gcd_\phi(s_1, s_2)$

**证明：**
定义 $\gcd_\phi(s_1, s_2) = \psi(\gcd(\omega(s_1), \omega(s_2)))$，其中右边的$\gcd$为标准最大公因数。

由自然数最大公因数的性质和双射的保持性，所有性质得到满足。

唯一性由标准最大公因数的唯一性和双射的单射性保证。 ∎

## 推论 8.1（φ-欧几里得算法）
φ-最大公因数可通过φ-欧几里得算法计算：

设 $r_0 = s_1, r_1 = s_2$，定义序列：
$$r_{i+1} = \text{rem}_\phi(r_{i-1}, r_i) \quad \text{直到} \quad r_k = \mathbf{0}_\phi$$

则 $\gcd_\phi(s_1, s_2) = r_{k-1}$。

**证明：**
这是标准欧几里得算法在φ-系统中的对应，正确性由双射的保持性保证。 ∎

## 定理 8.6（φ-分数的约分理论）
对 $s_1, s_2 \in \mathbb{F}\mathbb{N}$ 且 $s_2 \neq \mathbf{0}_\phi$，定义**最简φ-分数**：

设 $d = \gcd_\phi(s_1, s_2)$，则最简形式为：
$$\frac{s_1}{s_2} \sim \frac{\text{quot}_\phi(s_1, d)}{\text{quot}_\phi(s_2, d)}$$

**证明：**
由于 $d \mid_\phi s_1$ 和 $d \mid_\phi s_2$，商均良定义。
最简性由φ-最大公因数的性质保证。 ∎

## 定理 8.7（φ-除法的计算特征）
φ-除法运算包含以下计算步骤：

1. **解码**：计算 $\omega(s_1)$ 和 $\omega(s_2)$
2. **标准除法**：计算 $\omega(s_1) \div \omega(s_2) = (q, r)$  
3. **编码**：计算 $\psi(q)$ 和 $\psi(r)$

各步骤均可通过有限步骤完成。

**证明：**
步骤1和3的有限性由定理5.4保证。
步骤2的有限性由自然数除法运算的确定性保证。 ∎

## 定理 8.8（φ-倒数的存在性限制）
在φ-自然数系统中，倒数运算受到限制：

对 $s \in \mathbb{F}\mathbb{N} \setminus \{\mathbf{0}_\phi\}$，定义**φ-倒数存在条件**：
当且仅当 $s = \mathbf{1}_\phi$ 时，存在 $s^{-1}_\phi = s$ 使得 $s \otimes_\phi s^{-1}_\phi = \mathbf{1}_\phi$。

**证明：**
在 $\mathbb{F}\mathbb{N}$ 中，只有单位元1的倒数是自身。
其他元素的倒数需要在φ-有理数扩张中定义。 ∎

## 推论 8.2（半环结构限制）
$(\mathbb{F}\mathbb{N}, \oplus_\phi, \otimes_\phi)$ 构成交换半环结构，但不是环（缺乏加法逆元）。

φ-除法运算为后续φ-有理数系统的构造奠定基础。

**证明：**
半环性由加法和乘法的交换律、结合律、分配律保证。
非环性由$\mathbb{F}\mathbb{N}$中除$\mathbf{0}_\phi$外无元素具有加法逆元得出。 ∎