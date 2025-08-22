# 负数在φ-系统中的编码理论

## 定义 12.1（φ-符号扩展）
定义符号函数 $\sigma: \{+, -\} \to \mathbb{Z}$ 为：
$$\sigma(+) = +1, \quad \sigma(-) = -1$$

对于φ-自然数 $s \in \mathbb{F}\mathbb{N} \setminus \{\varepsilon\}$，定义**有符号φ-数**：
$$\mathbb{F}\mathbb{Z}^* = \{(sign, s) : sign \in \{+, -\}, s \in \mathbb{F}\mathbb{N} \setminus \{\varepsilon\}\} \cup \{(\pm, \varepsilon)\}$$

其中 $(\pm, \varepsilon)$ 表示φ-零，符号任意。

## 定理 12.1（φ-符号编码的良定义性）
φ-符号扩展良定义且与φ-整数 $\mathbb{F}\mathbb{Z}$ 一一对应。

**证明：**
构造映射 $\tau: \mathbb{F}\mathbb{Z}^* \to \mathbb{F}\mathbb{Z}$：
$$\tau((sign, s)) = \begin{cases}
+s & \text{若 } sign = + \\
-s & \text{若 } sign = - \text{ 且 } s \neq \varepsilon \\
+\varepsilon & \text{若 } s = \varepsilon
\end{cases}$$

**单射性**：若 $\tau((sign_1, s_1)) = \tau((sign_2, s_2))$，则由定义11.2的等价关系，必有 $(sign_1, s_1) = (sign_2, s_2)$。

**满射性**：对任意 $z \in \mathbb{F}\mathbb{Z}$，存在相应的 $(sign, s) \in \mathbb{F}\mathbb{Z}^*$ 使得 $\tau((sign, s)) = z$。 ∎

## 定义 12.2（φ-符号运算规则）
定义符号乘法 $\odot: \{+, -\} \times \{+, -\} \to \{+, -\}$：
$$sign_1 \odot sign_2 = \begin{cases}
+ & \text{若 } \sigma(sign_1) \cdot \sigma(sign_2) = +1 \\
- & \text{若 } \sigma(sign_1) \cdot \sigma(sign_2) = -1
\end{cases}$$

## 引理 12.1（φ-符号运算的代数性质）
φ-符号乘法满足：
1. **结合律**：$(sign_1 \odot sign_2) \odot sign_3 = sign_1 \odot (sign_2 \odot sign_3)$
2. **交换律**：$sign_1 \odot sign_2 = sign_2 \odot sign_1$
3. **单位元**：$sign \odot (+) = sign$
4. **逆元性**：$sign \odot sign = (+)$

**证明：**
所有性质直接由标准整数乘法的符号规则和映射 $\sigma$ 的保持性得出。 ∎

## 定义 12.3（φ-负数的Zeckendorf表示）
对负的φ-整数 $-s$（其中 $s \in \mathbb{F}\mathbb{N} \setminus \{\varepsilon\}$），定义其**扩展Zeckendorf表示**：

若 $s$ 的Zeckendorf分解为 $s = \sum_{i \in I} F_i$（其中 $I$ 为有限指标集），则：
$$-s \text{ 的扩展Zeckendorf表示为 } -\sum_{i \in I} F_i$$

## 定理 12.2（扩展Zeckendorf表示的唯一性）
每个φ-整数都有唯一的扩展Zeckendorf表示。

**证明：**
**存在性**：由定理1.2，每个 $s \in \mathbb{F}\mathbb{N}$ 都有唯一的Zeckendorf分解。因此每个φ-整数的扩展表示都存在。

**唯一性**：假设存在 $z \in \mathbb{F}\mathbb{Z}$ 有两个不同的扩展Zeckendorf表示：
$$z = \sigma_1 \sum_{i \in I_1} F_i = \sigma_2 \sum_{i \in I_2} F_i$$

其中 $\sigma_1, \sigma_2 \in \{+1, -1\}$。

若 $\sigma_1 = \sigma_2$，则 $\sum_{i \in I_1} F_i = \sum_{i \in I_2} F_i$，由定理1.2的唯一性，$I_1 = I_2$，矛盾。

若 $\sigma_1 \neq \sigma_2$，则 $\sum_{i \in I_1} F_i = -\sum_{i \in I_2} F_i$，即 $\sum_{i \in I_1} F_i + \sum_{i \in I_2} F_i = 0$。
由于所有 $F_i > 0$，左边为正数，不可能等于0，矛盾。 ∎

## 定义 12.4（φ-符号编码函数）
定义φ-符号编码 $\varepsilon: \mathbb{F}\mathbb{Z} \to \{0, 1\}^* \times \{+, -\}$：

对 $z \in \mathbb{F}\mathbb{Z}$：
$$\varepsilon(z) = \begin{cases}
(\varepsilon, +) & \text{若 } z = \mathbf{0}_{\mathbb{F}\mathbb{Z}} \\
(encode(s), +) & \text{若 } z = +s, s \neq \varepsilon \\
(encode(s), -) & \text{若 } z = -s, s \neq \varepsilon
\end{cases}$$

其中 $encode: \mathbb{F}\mathbb{N} \to \{0, 1\}^*$ 为定理3.2中的No-11编码。

## 定理 12.3（φ-符号编码的双射性）
φ-符号编码 $\varepsilon$ 为双射。

**证明：**
**单射性**：若 $\varepsilon(z_1) = \varepsilon(z_2) = (b, sign)$，则 $z_1, z_2$ 必有相同符号且相同的φ-自然数部分，故 $z_1 = z_2$。

**满射性**：对任意 $(b, sign) \in \{0, 1\}^* \times \{+, -\}$ 满足No-11约束，存在唯一 $s \in \mathbb{F}\mathbb{N}$ 使得 $encode(s) = b$。
则 $z = sign \cdot s$ 满足 $\varepsilon(z) = (b, sign)$。 ∎

## 引理 12.2（φ-符号的序关系）
在有符号φ-数上定义序关系：$(sign_1, s_1) \prec (sign_2, s_2)$ 当且仅当：
1. $sign_1 = - \wedge sign_2 = +$，或
2. $sign_1 = sign_2 = + \wedge s_1 \prec_\phi s_2$，或  
3. $sign_1 = sign_2 = - \wedge s_2 \prec_\phi s_1$

## 定理 12.4（φ-符号序关系与标准序关系的等价性）
φ-符号序关系通过双射 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$ 与标准整数序关系同构。

**证明：**
需验证：$z_1 \preceq_{\mathbb{F}\mathbb{Z}} z_2 \Leftrightarrow \xi(z_1) \leq \xi(z_2)$。

设 $z_1 = \tau((sign_1, s_1)), z_2 = \tau((sign_2, s_2))$，则：
$$\xi(z_1) = \sigma(sign_1) \cdot \omega(s_1), \quad \xi(z_2) = \sigma(sign_2) \cdot \omega(s_2)$$

三种情况的验证直接由整数序关系的定义得出。 ∎

## 定义 12.5（φ-符号运算的编码实现）
对有符号φ-数的运算可通过编码实现：

**φ-符号加法**：
$$(sign_1, s_1) \oplus (sign_2, s_2) = decode(\xi^{-1}(\sigma(sign_1) \cdot \omega(s_1) + \sigma(sign_2) \cdot \omega(s_2)))$$

**φ-符号乘法**：
$$(sign_1, s_1) \otimes (sign_2, s_2) = (sign_1 \odot sign_2, s_1 \otimes_\phi s_2)$$

其中 $decode: \mathbb{Z} \to \mathbb{F}\mathbb{Z}$ 为 $\xi$ 的逆映射。

## 定理 12.5（φ-符号运算的一致性）
φ-符号运算与φ-整数运算完全一致。

**证明：**
需验证对所有 $(sign_1, s_1), (sign_2, s_2) \in \mathbb{F}\mathbb{Z}^*$：
$$\tau((sign_1, s_1) \oplus (sign_2, s_2)) = \tau((sign_1, s_1)) \oplus_{\mathbb{F}\mathbb{Z}} \tau((sign_2, s_2))$$

由定义，两边都等于 $\xi^{-1}(\xi(\tau((sign_1, s_1))) + \xi(\tau((sign_2, s_2))))$，故相等。
乘法运算的一致性类似证明。 ∎

## 推论 12.1（φ-负数编码的计算特征）
φ-负数的编码和运算包含以下步骤：
1. **符号分离**：将φ-整数分解为符号和φ-自然数部分
2. **No-11编码**：将φ-自然数部分编码为满足No-11约束的二进制串  
3. **符号标记**：在编码前添加符号位
4. **运算转换**：通过双射转换为标准整数运算
5. **结果解码**：将运算结果解码回φ-符号表示

## 定理 12.6（φ-负数系统的完备性）
φ-负数编码系统与φ-整数环 $\mathbb{F}\mathbb{Z}$ 等价，实现了负数的完整表示。

**证明：**
由定理12.1、12.3、12.5，φ-符号扩展提供了φ-整数的完整且一致的编码方案。
通过双射 $\tau$ 和编码 $\varepsilon$，所有φ-整数都可以唯一地表示和操作。

因此，φ-负数编码实现了与标准整数系统的完全对应。 ∎

## 推论 12.2（Zeckendorf负数表示的优势）
φ-负数的Zeckendorf表示具有以下理论优势：
1. **唯一性**：每个φ-整数都有唯一的扩展Zeckendorf分解
2. **结构性**：保持了Fibonacci数的加性结构
3. **编码效率**：通过No-11约束实现了紧凑编码
4. **运算一致性**：与φ-自然数运算完全兼容

这为构建完整的φ-数系提供了坚实的负数理论基础。 ∎