# φ-加法运算理论

## 定义 6.1（φ-加法运算）
定义φ-加法运算 $\oplus_\phi: \mathbb{F}\mathbb{N} \times \mathbb{F}\mathbb{N} \to \mathbb{F}\mathbb{N}$ 为：
$$s_1 \oplus_\phi s_2 = \psi(\omega(s_1) + \omega(s_2))$$

其中 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 和 $\omega: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 为定理5.1中的双射。

## 定理 6.1（φ-加法的存在性与唯一性）
φ-加法运算$\oplus_\phi$良定义且唯一。

**存在性**：由定理5.1，双射$\psi$和$\omega$存在，故φ-加法运算$s_1 \oplus_\phi s_2 = \psi(\omega(s_1) + \omega(s_2))$良定义。

**唯一性**：设存在另一运算$\star$使得$(\mathbb{F}\mathbb{N}, \star)$与$(\mathbb{N}, +)$同构，则必有$s_1 \star s_2 = s_1 \oplus_\phi s_2$。

**证明：**
运算的良定义性直接由双射的存在性得出。唯一性由同构的唯一性保证。 ∎

## 引理 6.1（φ-加法的No-11保持性）
φ-加法运算保持No-11约束：若 $s_1, s_2 \in \mathbb{F}\mathbb{N}$，则 $s_1 \oplus_\phi s_2 \in \mathbb{F}\mathbb{N}$。

**证明：**
由定义，$s_1 \oplus_\phi s_2 = \psi(\omega(s_1) + \omega(s_2))$。
由于$\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$的定义，其值域恰好是$\mathbb{F}\mathbb{N}$，
故运算结果自动满足No-11约束。 ∎

## 定理 6.2（φ-加法的结合律）
对所有 $s_1, s_2, s_3 \in \mathbb{F}\mathbb{N}$：
$$(s_1 \oplus_\phi s_2) \oplus_\phi s_3 = s_1 \oplus_\phi (s_2 \oplus_\phi s_3)$$

**证明：**
$$\begin{align}
(s_1 \oplus_\phi s_2) \oplus_\phi s_3 &= \psi(\omega(\psi(\omega(s_1) + \omega(s_2))) + \omega(s_3)) \\
&= \psi((\omega(s_1) + \omega(s_2)) + \omega(s_3)) \\
&= \psi(\omega(s_1) + (\omega(s_2) + \omega(s_3))) \\
&= s_1 \oplus_\phi (s_2 \oplus_\phi s_3)
\end{align}$$

其中第二步使用双射性质 $\omega \circ \psi = \text{id}_\mathbb{N}$，第三步使用自然数加法结合律。 ∎

## 定理 6.3（φ-加法的交换律）
对所有 $s_1, s_2 \in \mathbb{F}\mathbb{N}$：
$$s_1 \oplus_\phi s_2 = s_2 \oplus_\phi s_1$$

**证明：**
$$s_1 \oplus_\phi s_2 = \psi(\omega(s_1) + \omega(s_2)) = \psi(\omega(s_2) + \omega(s_1)) = s_2 \oplus_\phi s_1$$

使用自然数加法交换律。 ∎

## 定理 6.4（φ-加法的单位元）
$\varepsilon$（空串）是φ-加法的单位元：
$$s \oplus_\phi \varepsilon = \varepsilon \oplus_\phi s = s \quad \text{对所有 } s \in \mathbb{F}\mathbb{N}$$

**证明：**
$$s \oplus_\phi \varepsilon = \psi(\omega(s) + \omega(\varepsilon)) = \psi(\omega(s) + 0) = \psi(\omega(s)) = s$$

使用 $\omega(\varepsilon) = 0$ 和双射性质 $\psi \circ \omega = \text{id}_{\mathbb{F}\mathbb{N}}$。 ∎

## 定理 6.2'（φ-加法的理论计算性）
φ-加法运算在理论上可通过有限步骤完成。

**证明：**
加法运算的有限性由双射$\psi, \omega$的构造性质（定理5.2）和自然数加法的确定性保证。 ∎

## 定理 6.5（φ-加法与标准加法的等价性）
φ-加法运算与自然数加法语义等价：
$$\omega(s_1 \oplus_\phi s_2) = \omega(s_1) + \omega(s_2)$$

**证明：**
$$\omega(s_1 \oplus_\phi s_2) = \omega(\psi(\omega(s_1) + \omega(s_2))) = \omega(s_1) + \omega(s_2)$$

使用双射性质 $\omega \circ \psi = \text{id}_\mathbb{N}$。 ∎

## 引理 6.2（φ-加法的有限性质）
φ-加法运算保持Zeckendorf表示的有限性特征。

**证明：**
由于φ-编码的有限性和双射$\psi, \omega$的保持性质，运算结果保持有限表示。 ∎

## 定理 6.6（φ-加法的单调性）
对所有 $s_1, s_2, t \in \mathbb{F}\mathbb{N}$：
$$s_1 \preceq_\phi s_2 \Rightarrow s_1 \oplus_\phi t \preceq_\phi s_2 \oplus_\phi t$$

其中 $\preceq_\phi$ 为定义2.4中的φ-序关系。

**证明：**
若 $s_1 \preceq_\phi s_2$，则 $\omega(s_1) \leq \omega(s_2)$。
因此 $\omega(s_1) + \omega(t) \leq \omega(s_2) + \omega(t)$，
即 $\omega(s_1 \oplus_\phi t) \leq \omega(s_2 \oplus_\phi t)$，
故 $s_1 \oplus_\phi t \preceq_\phi s_2 \oplus_\phi t$。 ∎

## 推论 6.1（φ-加法幺半群结构）
$(\mathbb{F}\mathbb{N}, \oplus_\phi, \varepsilon)$ 构成交换幺半群。

**证明：**
由定理6.2（结合律）、定理6.3（交换律）、定理6.4（单位元）得出。 ∎