# φ-乘法运算理论

## 定义 7.1（φ-乘法运算）
定义φ-乘法运算 $\otimes_\phi: \mathbb{F}\mathbb{N} \times \mathbb{F}\mathbb{N} \to \mathbb{F}\mathbb{N}$ 为：
$$s_1 \otimes_\phi s_2 = \psi(\omega(s_1) \cdot \omega(s_2))$$

其中 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 和 $\omega: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 为定理5.1中的双射。

## 定理 7.1（φ-乘法的良定义性）
φ-乘法运算$\otimes_\phi$良定义且唯一。

**证明：**
**存在性**：由定理5.1，双射$\psi$和$\omega$存在，故φ-乘法运算$s_1 \otimes_\phi s_2 = \psi(\omega(s_1) \cdot \omega(s_2))$良定义。

**唯一性**：设存在另一运算$\star$使得$(\mathbb{F}\mathbb{N}, \star)$与$(\mathbb{N}, \cdot)$同构，则必有$s_1 \star s_2 = s_1 \otimes_\phi s_2$。

运算的良定义性直接由双射的存在性得出。唯一性由同构的唯一性保证。 ∎

## 定理 7.2（φ-乘法的结合律）
对所有 $s_1, s_2, s_3 \in \mathbb{F}\mathbb{N}$：
$$(s_1 \otimes_\phi s_2) \otimes_\phi s_3 = s_1 \otimes_\phi (s_2 \otimes_\phi s_3)$$

**证明：**
$$\begin{align}
(s_1 \otimes_\phi s_2) \otimes_\phi s_3 &= \psi(\omega(\psi(\omega(s_1) \cdot \omega(s_2))) \cdot \omega(s_3)) \\
&= \psi((\omega(s_1) \cdot \omega(s_2)) \cdot \omega(s_3)) \\
&= \psi(\omega(s_1) \cdot (\omega(s_2) \cdot \omega(s_3))) \\
&= s_1 \otimes_\phi (s_2 \otimes_\phi s_3)
\end{align}$$

其中第二步使用双射性质 $\omega \circ \psi = \text{id}_\mathbb{N}$，第三步使用自然数乘法结合律。 ∎

## 定理 7.3（φ-乘法的交换律）
对所有 $s_1, s_2 \in \mathbb{F}\mathbb{N}$：
$$s_1 \otimes_\phi s_2 = s_2 \otimes_\phi s_1$$

**证明：**
$$s_1 \otimes_\phi s_2 = \psi(\omega(s_1) \cdot \omega(s_2)) = \psi(\omega(s_2) \cdot \omega(s_1)) = s_2 \otimes_\phi s_1$$

使用自然数乘法交换律。 ∎

## 定理 7.4（φ-乘法的单位元）
$\mathbf{1}_\phi = 1$是φ-乘法的单位元：
$$s \otimes_\phi \mathbf{1}_\phi = \mathbf{1}_\phi \otimes_\phi s = s \quad \text{对所有 } s \in \mathbb{F}\mathbb{N}$$

**证明：**
$$s \otimes_\phi \mathbf{1}_\phi = \psi(\omega(s) \cdot \omega(\mathbf{1}_\phi)) = \psi(\omega(s) \cdot 1) = \psi(\omega(s)) = s$$

使用 $\omega(\mathbf{1}_\phi) = \omega(1) = 1$ 和双射性质 $\psi \circ \omega = \text{id}_{\mathbb{F}\mathbb{N}}$。 ∎

## 定理 7.5（φ-乘法的零化性质）
$\mathbf{0}_\phi = \varepsilon$是φ-乘法的零元：
$$s \otimes_\phi \mathbf{0}_\phi = \mathbf{0}_\phi \otimes_\phi s = \mathbf{0}_\phi \quad \text{对所有 } s \in \mathbb{F}\mathbb{N}$$

**证明：**
$$s \otimes_\phi \mathbf{0}_\phi = \psi(\omega(s) \cdot \omega(\mathbf{0}_\phi)) = \psi(\omega(s) \cdot 0) = \psi(0) = \varepsilon = \mathbf{0}_\phi$$

使用 $\omega(\mathbf{0}_\phi) = \omega(\varepsilon) = 0$。 ∎

## 定理 7.6（φ-乘法对加法的分配律）
对所有 $s_1, s_2, s_3 \in \mathbb{F}\mathbb{N}$：
$$s_1 \otimes_\phi (s_2 \oplus_\phi s_3) = (s_1 \otimes_\phi s_2) \oplus_\phi (s_1 \otimes_\phi s_3)$$

**证明：**
$$\begin{align}
s_1 \otimes_\phi (s_2 \oplus_\phi s_3) &= \psi(\omega(s_1) \cdot \omega(\psi(\omega(s_2) + \omega(s_3)))) \\
&= \psi(\omega(s_1) \cdot (\omega(s_2) + \omega(s_3))) \\
&= \psi(\omega(s_1) \cdot \omega(s_2) + \omega(s_1) \cdot \omega(s_3)) \\
&= \psi(\omega(\psi(\omega(s_1) \cdot \omega(s_2))) + \omega(\psi(\omega(s_1) \cdot \omega(s_3)))) \\
&= (s_1 \otimes_\phi s_2) \oplus_\phi (s_1 \otimes_\phi s_3)
\end{align}$$

其中使用双射性质和自然数乘法对加法的分配律。 ∎

## 定理 7.7（φ-乘法与标准乘法的等价性）
φ-乘法运算与自然数乘法语义等价：
$$\omega(s_1 \otimes_\phi s_2) = \omega(s_1) \cdot \omega(s_2)$$

**证明：**
$$\omega(s_1 \otimes_\phi s_2) = \omega(\psi(\omega(s_1) \cdot \omega(s_2))) = \omega(s_1) \cdot \omega(s_2)$$

使用双射性质 $\omega \circ \psi = \text{id}_\mathbb{N}$。 ∎

## 定理 7.8（φ-乘法的单调性）
对所有 $s_1, s_2, t \in \mathbb{F}\mathbb{N}$，若 $t \neq \mathbf{0}_\phi$：
$$s_1 \preceq_\phi s_2 \Rightarrow s_1 \otimes_\phi t \preceq_\phi s_2 \otimes_\phi t$$

其中 $\preceq_\phi$ 为定义2.4中的φ-序关系。

**证明：**
若 $s_1 \preceq_\phi s_2$，则 $\omega(s_1) \leq \omega(s_2)$。
由于 $t \neq \mathbf{0}_\phi$，有 $\omega(t) \geq 1 > 0$。
因此 $\omega(s_1) \cdot \omega(t) \leq \omega(s_2) \cdot \omega(t)$，
即 $\omega(s_1 \otimes_\phi t) \leq \omega(s_2 \otimes_\phi t)$，
故 $s_1 \otimes_\phi t \preceq_\phi s_2 \otimes_\phi t$。 ∎

## 引理 7.1（Fibonacci乘积的φ-编码性质）
设 $F_i, F_j$ 为Fibonacci数，$i, j \geq 1$，则：
$$\psi(F_i \cdot F_j) \in \mathbb{F}\mathbb{N}$$

**证明：**
由于 $F_i \cdot F_j \in \mathbb{N}$ 且 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 为双射，
$\psi(F_i \cdot F_j)$ 必然存在且唯一属于 $\mathbb{F}\mathbb{N}$。

存在性由定理5.2的构造性质保证。 ∎

## 定理 7.9（φ-乘法的Fibonacci乘积恒等式）
对Fibonacci指标 $i, j \geq 1$：
$$\psi(F_i) \otimes_\phi \psi(F_j) = \psi(F_i \cdot F_j)$$

**证明：**
$$\psi(F_i) \otimes_\phi \psi(F_j) = \psi(\omega(\psi(F_i)) \cdot \omega(\psi(F_j))) = \psi(F_i \cdot F_j)$$

使用双射性质 $\omega \circ \psi = \text{id}_\mathbb{N}$。 ∎

## 推论 7.1（φ-乘法幺半群结构）
$(\mathbb{F}\mathbb{N}, \otimes_\phi, \mathbf{1}_\phi)$ 构成交换幺半群。

**证明：**
由定理7.2（结合律）、定理7.3（交换律）、定理7.4（单位元）得出。 ∎

## 推论 7.2（φ-环结构预备）
$(\mathbb{F}\mathbb{N}, \oplus_\phi, \otimes_\phi, \mathbf{0}_\phi, \mathbf{1}_\phi)$ 构成交换半环。

**证明：**
由推论6.1知 $(\mathbb{F}\mathbb{N}, \oplus_\phi, \mathbf{0}_\phi)$ 构成交换幺半群；
由推论7.1知 $(\mathbb{F}\mathbb{N}, \otimes_\phi, \mathbf{1}_\phi)$ 构成交换幺半群；
由定理7.6知分配律成立；
由定理7.5知零元的零化性质成立。 ∎

## 定理 7.10（φ-乘法的计算特征）
φ-乘法运算的计算过程包含：
1. 解码步骤：计算$\omega(s_1)$和$\omega(s_2)$
2. 标准乘法：计算$\omega(s_1) \cdot \omega(s_2)$
3. 编码步骤：计算$\psi(\omega(s_1) \cdot \omega(s_2))$

所有步骤在理论上均可通过有限步骤完成。

**证明：**
各步骤的有限性由定理5.4的构造性质和乘法运算的确定性保证。 ∎