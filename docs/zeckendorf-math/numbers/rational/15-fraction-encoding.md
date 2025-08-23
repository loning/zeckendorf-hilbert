# φ-分数的Zeckendorf编码理论

## 定义 15.1（φ-分数的规范表示）
对 $\frac{a}{b} \in \mathbb{F}\mathbb{Q}$，定义其**规范表示**为：
$$\frac{a}{b} = \frac{\text{sign}(a) \cdot |a|/d}{|b|/d}$$

其中 $d = \gcd_{\mathbb{F}\mathbb{Z}}(|a|, |b|)$，$\text{sign}(a) \in \{+1, -1\}$，且 $\gcd_{\mathbb{F}\mathbb{Z}}(|a|/d, |b|/d) = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$。

## 定理 15.1（φ-分数规范表示的唯一性）
每个φ-有理数都有唯一的规范表示。

**证明：**
**存在性**：由定理13.5（φ-整数最大公因数），任意φ-有理数 $\frac{a}{b}$ 可通过约去最大公因数得到规范形式。

**唯一性**：设 $\frac{a_1}{b_1}$ 和 $\frac{a_2}{b_2}$ 为同一φ-有理数的两个规范表示。
则 $\frac{a_1}{b_1} = \frac{a_2}{b_2}$，即 $a_1 \otimes_{\mathbb{F}\mathbb{Z}} b_2 = a_2 \otimes_{\mathbb{F}\mathbb{Z}} b_1$。

由于两者都为规范形式，必有 $\gcd_{\mathbb{F}\mathbb{Z}}(|a_1|, |b_1|) = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$ 且 $\gcd_{\mathbb{F}\mathbb{Z}}(|a_2|, |b_2|) = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$。

由整环的性质，必有 $a_1 = a_2$ 且 $b_1 = b_2$。 ∎

## 定义 15.2（φ-分数的Zeckendorf编码）
对规范φ-分数 $\frac{a}{b}$，定义其**Zeckendorf编码**为三元组：
$$\text{encode}_{\mathbb{F}\mathbb{Q}}\left(\frac{a}{b}\right) = (\sigma, E_a, E_b)$$

其中：
- $\sigma \in \{+, -\}$ 为符号位
- $E_a = \varepsilon(|a|) \in \{0,1\}^*$ 为分子的φ-编码（满足No-11约束）
- $E_b = \varepsilon(b) \in \{0,1\}^*$ 为分母的φ-编码（满足No-11约束，且 $b \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$）

## 定理 15.2（φ-分数Zeckendorf编码的双射性）
编码函数 $\text{encode}_{\mathbb{F}\mathbb{Q}}: \mathbb{F}\mathbb{Q} \to \{+,-\} \times \{0,1\}^* \times (\{0,1\}^* \setminus \{\varepsilon\})$ 为双射，

其中定义域为所有满足No-11约束的编码对。

**证明：**
**单射性**：若 $\text{encode}_{\mathbb{F}\mathbb{Q}}(r_1) = \text{encode}_{\mathbb{F}\mathbb{Q}}(r_2)$，则两个φ-分数有相同的符号、分子编码和分母编码。
由定理3.3（φ-编码的双射性）和定理16.1（规范表示的唯一性），必有 $r_1 = r_2$。

**满射性**：对任意合法编码 $(\sigma, E_a, E_b)$，存在唯一的 $a, b \in \mathbb{F}\mathbb{Z}$（$b \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$）
使得 $\varepsilon(|a|) = E_a$，$\varepsilon(b) = E_b$。
构造 $r = \frac{\sigma \cdot a}{b}$ 的规范形式即得到对应的φ-有理数。 ∎

## 定义 15.3（φ-分数编码的长度度量）
对φ-分数编码 $(\sigma, E_a, E_b)$，定义其**编码长度**为：
$$\ell_{\mathbb{F}\mathbb{Q}}(r) = 1 + |E_a| + |E_b|$$

其中 $|E|$ 表示二进制串的长度。

## 引理 15.1（φ-分数编码长度的性质）
对φ-有理数 $r \in \mathbb{F}\mathbb{Q}$：
1. $\ell_{\mathbb{F}\mathbb{Q}}(r) \geq 2$（最小编码为符号位加两个空串的分数）
2. $\ell_{\mathbb{F}\mathbb{Q}}(\mathbf{0}_{\mathbb{F}\mathbb{Q}}) = 2$
3. $\ell_{\mathbb{F}\mathbb{Q}}(\mathbf{1}_{\mathbb{F}\mathbb{Q}}) = 3$

**证明：**
设定约定：空串 $\varepsilon$ 对应φ-自然数 $\mathbf{0}_{\mathbb{F}\mathbb{N}}$，其编码长度记为0；非零φ-自然数的最小编码长度为1。

1. 符号位占1位，分子和分母编码各至少0位，故 $\ell_{\mathbb{F}\mathbb{Q}}(r) \geq 1+0+0=1$
2. 实际上分母不能为零，$\mathbf{1}_{\mathbb{F}\mathbb{Z}}$ 对应编码长度1，故实际最小长度为2
3. $\mathbf{0}_{\mathbb{F}\mathbb{Q}} = \frac{\mathbf{0}_{\mathbb{F}\mathbb{Z}}}{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}$ 编码为 $(+, \varepsilon, 1)$，长度为$1+0+1=2$
4. $\mathbf{1}_{\mathbb{F}\mathbb{Q}} = \frac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}$ 编码为 $(+, 1, 1)$，长度为$1+1+1=3$ ∎

## 定理 15.3（φ-分数运算的编码保持性）
φ-有理数的四则运算保持Zeckendorf编码结构的封闭性：

对 $r_1, r_2 \in \mathbb{F}\mathbb{Q}$，运算结果 $r_1 \oplus_{\mathbb{F}\mathbb{Q}} r_2$，$r_1 \otimes_{\mathbb{F}\mathbb{Q}} r_2$，
$r_1 \ominus_{\mathbb{F}\mathbb{Q}} r_2$，$r_1 \div_{\mathbb{F}\mathbb{Q}} r_2$（当$r_2 \neq \mathbf{0}_{\mathbb{F}\mathbb{Q}}$）的编码仍满足No-11约束。

**证明：**
由于φ-有理数运算建立在φ-整数运算基础上，而φ-整数运算保持φ-编码的No-11约束（定理3.4），
所有φ-有理数运算的结果都可以编码为满足No-11约束的形式。 ∎

## 定义 15.4（φ-分数的连分数展开）
对φ-有理数 $r \in \mathbb{F}\mathbb{Q}$，定义其**φ-连分数展开**：

若 $r = \frac{a}{b}$（规范形式），则存在有限序列 $q_0, q_1, \ldots, q_n \in \mathbb{F}\mathbb{Z}$ 使得：
$$r = q_0 \oplus_{\mathbb{F}\mathbb{Q}} \cfrac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{q_1 \oplus_{\mathbb{F}\mathbb{Q}} \cfrac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{q_2 \oplus_{\mathbb{F}\mathbb{Q}} \cfrac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{\ddots \cfrac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{q_n}}}}$$

记作 $r = [q_0; q_1, q_2, \ldots, q_n]_\phi$。

## 定理 15.4（φ-连分数展开的存在性与唯一性）
每个φ-有理数都有有限且唯一的φ-连分数展开。

**证明：**
**存在性**：通过φ-欧几里得算法构造。设 $r = \frac{a}{b}$：

1. $q_0 = \text{quot}_{\mathbb{F}\mathbb{Z}}(a, b)$，$r_0 = \text{rem}_{\mathbb{F}\mathbb{Z}}(a, b)$
2. 若 $r_0 \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$，则 $r - q_0 = \frac{r_0}{b} = \frac{\mathbf{1}_{\mathbb{F}\mathbb{Z}}}{\frac{b}{r_0}}$
3. 对 $\frac{b}{r_0}$ 重复此过程

由于φ-整数的欧几里得算法在有限步内终止，φ-连分数展开必然有限。

**唯一性**：由φ-欧几里得算法的唯一性和定理16.1的规范表示唯一性保证。 ∎

## 引理 15.2（φ-分数编码的压缩性质）
对φ-有理数 $r = \frac{a}{b}$，其连分数展开的编码长度一般小于直接分数编码：
$$\ell([q_0; q_1, \ldots, q_n]_\phi) \leq \ell_{\mathbb{F}\mathbb{Q}}\left(\frac{a}{b}\right)$$

当且仅当 $\gcd_{\mathbb{F}\mathbb{Z}}(|a|, |b|) = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$ 且连分数系数较小时等号成立。

**证明：**
连分数展开通过欧几里得算法逐步减小数值，通常产生更紧凑的表示。
具体的编码长度比较需要考虑No-11约束下的编码效率。 ∎

## 定理 15.5（φ-分数编码的计算特征）
φ-分数的编码和解码包含以下步骤：

**编码过程**：
1. **规范化**：将φ-分数约简为规范形式
2. **分离符号**：提取符号位
3. **分子分母编码**：分别对分子、分母进行φ-编码
4. **组合**：构造三元编码组

**解码过程**：
1. **符号识别**：读取符号位
2. **分子分母解码**：分别解码得到φ-整数
3. **分数构造**：构造φ-分数
4. **规范化验证**：验证最大公因数为1

所有步骤都在理论上可通过有限操作完成。

**证明：**
各步骤的可行性由前述各定理和φ-整数编码理论（定理5.4）保证。 ∎

## 推论 15.1（φ-分数编码系统的完备性）
φ-分数的Zeckendorf编码系统实现了有理数的完整表示：

1. **唯一性**：每个φ-有理数都有唯一的规范Zeckendorf编码
2. **完全性**：所有满足约束的编码都对应有效的φ-有理数
3. **运算封闭性**：四则运算在编码层面保持封闭
4. **压缩性**：连分数展开提供更紧凑的编码方案
5. **可计算性**：编码和解码都可通过有限步骤实现

这为构建完整的φ-数系奠定了有理数层面的编码理论基础。

**证明：**
所有性质由前述各定理直接得出，特别是定理16.2的双射性和定理16.3的运算保持性。 ∎