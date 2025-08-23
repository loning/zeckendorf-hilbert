# φ-整数系统构造理论

## 定义 10.1（φ-整数集合）
定义**φ-整数集合** $\mathbb{F}\mathbb{Z}$ 为φ-自然数的符号扩展：
$$\mathbb{F}\mathbb{Z} = \{+s : s \in \mathbb{F}\mathbb{N}\} \cup \{-s : s \in \mathbb{F}\mathbb{N} \setminus \{\varepsilon\}\}$$

其中：
- $+s$ 表示**正φ-整数**，当 $s \neq \varepsilon$ 时
- $-s$ 表示**负φ-整数**，当 $s \neq \varepsilon$ 时  
- $+\varepsilon = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$ 为**φ-零整数**

## 定义 10.2（φ-整数等价关系）
在 $\mathbb{F}\mathbb{Z}$ 上定义等价关系：
$$+s_1 \sim +s_2 \iff s_1 = s_2$$
$$-s_1 \sim -s_2 \iff s_1 = s_2$$
$$+s \not\sim -t \text{ 对所有 } s, t \in \mathbb{F}\mathbb{N} \setminus \{\varepsilon\}$$

## 定理 10.1（φ-整数良定义性）
集合 $\mathbb{F}\mathbb{Z}$ 在等价关系 $\sim$ 下良定义，且与标准整数集合 $\mathbb{Z}$ 等势。

**证明：**
**良定义性**：等价关系 $\sim$ 满足反身性、对称性、传递性。
- 反身性：$x \sim x$ 对所有 $x \in \mathbb{F}\mathbb{Z}$
- 对称性：$x \sim y \Rightarrow y \sim x$
- 传递性：$x \sim y \wedge y \sim z \Rightarrow x \sim z$

**等势性**：构造双射 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$：
$$\xi(z) = \begin{cases}
0 & \text{若 } z = +\varepsilon \\
+\omega(s) & \text{若 } z = +s, s \neq \varepsilon \\
-\omega(s) & \text{若 } z = -s, s \neq \varepsilon
\end{cases}$$

其中 $\omega: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 为定理5.1中的双射。由于 $\omega$ 为双射，$\xi$ 为双射。 ∎

## 定义 10.3（φ-整数序关系）
在 $\mathbb{F}\mathbb{Z}$ 上定义全序关系 $\preceq_{\mathbb{F}\mathbb{Z}}$：

对 $z_1, z_2 \in \mathbb{F}\mathbb{Z}$，$z_1 \preceq_{\mathbb{F}\mathbb{Z}} z_2$ 当且仅当 $\xi(z_1) \leq \xi(z_2)$。

## 定理 10.2（φ-整数序关系性质）
$(\mathbb{F}\mathbb{Z}, \preceq_{\mathbb{F}\mathbb{Z}})$ 构成全序集，且与 $(\mathbb{Z}, \leq)$ 序同构。

**证明：**
需验证 $\preceq_{\mathbb{F}\mathbb{Z}}$ 的全序性质：

1. **反身性**：$z \preceq_{\mathbb{F}\mathbb{Z}} z$ 因为 $\xi(z) \leq \xi(z)$
2. **反对称性**：若 $z_1 \preceq_{\mathbb{F}\mathbb{Z}} z_2$ 且 $z_2 \preceq_{\mathbb{F}\mathbb{Z}} z_1$，则 $\xi(z_1) = \xi(z_2)$，由 $\xi$ 的单射性得 $z_1 = z_2$
3. **传递性**：若 $z_1 \preceq_{\mathbb{F}\mathbb{Z}} z_2$ 且 $z_2 \preceq_{\mathbb{F}\mathbb{Z}} z_3$，则 $\xi(z_1) \leq \xi(z_2) \leq \xi(z_3)$，故 $z_1 \preceq_{\mathbb{F}\mathbb{Z}} z_3$
4. **全序性**：对任意 $z_1, z_2$，要么 $\xi(z_1) \leq \xi(z_2)$ 要么 $\xi(z_2) \leq \xi(z_1)$

序同构性由双射 $\xi$ 保持序关系得出。 ∎

## 定义 10.4（φ-整数加法）
定义φ-整数加法运算 $\oplus_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \times \mathbb{F}\mathbb{Z} \to \mathbb{F}\mathbb{Z}$：

$$z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2 = \xi^{-1}(\xi(z_1) + \xi(z_2))$$

其中 $+$ 为标准整数加法，$\xi^{-1}$ 为双射 $\xi$ 的逆映射。

## 定理 10.3（φ-整数加法性质）
φ-整数加法具有以下性质：

1. **结合律**：$(z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2) \oplus_{\mathbb{F}\mathbb{Z}} z_3 = z_1 \oplus_{\mathbb{F}\mathbb{Z}} (z_2 \oplus_{\mathbb{F}\mathbb{Z}} z_3)$
2. **交换律**：$z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2 = z_2 \oplus_{\mathbb{F}\mathbb{Z}} z_1$
3. **单位元**：$z \oplus_{\mathbb{F}\mathbb{Z}} \mathbf{0}_{\mathbb{F}\mathbb{Z}} = z$ 对所有 $z \in \mathbb{F}\mathbb{Z}$
4. **逆元存在性**：对每个 $z \in \mathbb{F}\mathbb{Z}$，存在 $z^{-1} \in \mathbb{F}\mathbb{Z}$ 使得 $z \oplus_{\mathbb{F}\mathbb{Z}} z^{-1} = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$

**证明：**
所有性质由标准整数加法的对应性质和双射 $\xi$ 的保持性得出。

**逆元构造**：
- 若 $z = +s$ 且 $s \neq \varepsilon$，则 $z^{-1} = -s$
- 若 $z = -s$ 且 $s \neq \varepsilon$，则 $z^{-1} = +s$  
- 若 $z = +\varepsilon$，则 $z^{-1} = +\varepsilon = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$ ∎

## 定理 10.4（φ-整数加法群结构）
$(\mathbb{F}\mathbb{Z}, \oplus_{\mathbb{F}\mathbb{Z}}, \mathbf{0}_{\mathbb{F}\mathbb{Z}})$ 构成交换群。

**证明：**
由定理11.3，所有群公理得到满足：
- 封闭性：由定义11.4保证
- 结合律：定理11.3第1条
- 单位元：定理11.3第3条  
- 逆元：定理11.3第4条
- 交换律：定理11.3第2条 ∎

## 定义 10.5（φ-整数乘法）
定义φ-整数乘法运算 $\otimes_{\mathbb{F}\mathbb{Z}}: \mathbb{F}\mathbb{Z} \times \mathbb{F}\mathbb{Z} \to \mathbb{F}\mathbb{Z}$：

$$z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 = \xi^{-1}(\xi(z_1) \cdot \xi(z_2))$$

其中 $\cdot$ 为标准整数乘法。

## 定理 10.5（φ-整数乘法性质）
φ-整数乘法具有以下性质：

1. **结合律**：$(z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2) \otimes_{\mathbb{F}\mathbb{Z}} z_3 = z_1 \otimes_{\mathbb{F}\mathbb{Z}} (z_2 \otimes_{\mathbb{F}\mathbb{Z}} z_3)$
2. **交换律**：$z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 = z_2 \otimes_{\mathbb{F}\mathbb{Z}} z_1$
3. **单位元**：$z \otimes_{\mathbb{F}\mathbb{Z}} \mathbf{1}_{\mathbb{F}\mathbb{Z}} = z$ 对所有 $z \in \mathbb{F}\mathbb{Z}$，其中 $\mathbf{1}_{\mathbb{F}\mathbb{Z}} = +1$
4. **零化性质**：$z \otimes_{\mathbb{F}\mathbb{Z}} \mathbf{0}_{\mathbb{F}\mathbb{Z}} = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$ 对所有 $z \in \mathbb{F}\mathbb{Z}$

**证明：**
所有性质由标准整数乘法的对应性质和双射 $\xi$ 的保持性得出。 ∎

## 定理 10.6（φ-整数分配律）
φ-整数乘法对加法满足分配律：
$$z_1 \otimes_{\mathbb{F}\mathbb{Z}} (z_2 \oplus_{\mathbb{F}\mathbb{Z}} z_3) = (z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2) \oplus_{\mathbb{F}\mathbb{Z}} (z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_3)$$

**证明：**
$$\begin{align}
z_1 \otimes_{\mathbb{F}\mathbb{Z}} (z_2 \oplus_{\mathbb{F}\mathbb{Z}} z_3) &= \xi^{-1}(\xi(z_1) \cdot \xi(\xi^{-1}(\xi(z_2) + \xi(z_3)))) \\
&= \xi^{-1}(\xi(z_1) \cdot (\xi(z_2) + \xi(z_3))) \\
&= \xi^{-1}(\xi(z_1) \cdot \xi(z_2) + \xi(z_1) \cdot \xi(z_3)) \\
&= \xi^{-1}(\xi(\xi^{-1}(\xi(z_1) \cdot \xi(z_2))) + \xi(\xi^{-1}(\xi(z_1) \cdot \xi(z_3)))) \\
&= (z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2) \oplus_{\mathbb{F}\mathbb{Z}} (z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_3)
\end{align}$$

使用标准整数分配律和双射性质。 ∎

## 定理 10.7（φ-整数环结构）
$(\mathbb{F}\mathbb{Z}, \oplus_{\mathbb{F}\mathbb{Z}}, \otimes_{\mathbb{F}\mathbb{Z}}, \mathbf{0}_{\mathbb{F}\mathbb{Z}}, \mathbf{1}_{\mathbb{F}\mathbb{Z}})$ 构成交换环。

**证明：**
需验证环公理：
1. **加法群**：由定理11.4
2. **乘法幺半群**：由定理11.5
3. **分配律**：由定理11.6
4. **交换性**：由定理11.5第2条 ∎

## 定理 10.8（φ-整数无零因子性）
φ-整数环 $\mathbb{F}\mathbb{Z}$ 无零因子：若 $z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$，则 $z_1 = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$ 或 $z_2 = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$。

**证明：**
若 $z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$，则：
$$\xi^{-1}(\xi(z_1) \cdot \xi(z_2)) = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$$

因此 $\xi(z_1) \cdot \xi(z_2) = 0$。由于 $\mathbb{Z}$ 无零因子，要么 $\xi(z_1) = 0$ 要么 $\xi(z_2) = 0$，即 $z_1 = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$ 或 $z_2 = \mathbf{0}_{\mathbb{F}\mathbb{Z}}$。 ∎

## 推论 10.1（φ-整环结构）
$\mathbb{F}\mathbb{Z}$ 构成整环（无零因子的交换环）。

**证明：**
由定理11.7和定理11.8直接得出。 ∎

## 定理 10.9（φ-整数扩展的极小性）
$\mathbb{F}\mathbb{Z}$ 是包含 $\mathbb{F}\mathbb{N}$ 的最小整环。

**证明：**
**包含性**：存在环同态 $\iota: \mathbb{F}\mathbb{N} \to \mathbb{F}\mathbb{Z}$ 定义为 $\iota(s) = +s$。

**极小性**：设 $R$ 为任一包含 $\mathbb{F}\mathbb{N}$ 的整环。则 $R$ 必须包含 $\mathbb{F}\mathbb{N}$ 的所有元素及其加法逆元，故 $\mathbb{F}\mathbb{Z} \subseteq R$。 ∎

## 定理 10.10（φ-整数与标准整数的同构）
存在环同构：
$$\mathbb{F}\mathbb{Z} \cong \mathbb{Z}$$

其中同构映射为 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$。

**证明：**
需验证 $\xi$ 保持环结构：
1. **加法保持**：$\xi(z_1 \oplus_{\mathbb{F}\mathbb{Z}} z_2) = \xi(z_1) + \xi(z_2)$
2. **乘法保持**：$\xi(z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2) = \xi(z_1) \cdot \xi(z_2)$
3. **单位元保持**：$\xi(\mathbf{0}_{\mathbb{F}\mathbb{Z}}) = 0$，$\xi(\mathbf{1}_{\mathbb{F}\mathbb{Z}}) = 1$

所有性质由 $\xi$ 的定义直接得出。 ∎

## 推论 10.2（φ-整数的普遍性质）
φ-整数环 $\mathbb{F}\mathbb{Z}$ 满足与标准整数环相同的普遍性质：它是φ-自然数半环的分式环。

**证明：**
由同构定理11.10和分式环的普遍性质得出。 ∎