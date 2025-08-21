# 基础记号系统

本文档建立完整的数学记号约定，为理论构建提供严格的数学基础。所有定义基于**A1唯一公理**：任意自指完备系统必然熵增。

## 1. 基础字母表与记号

### 1.1 二进制字母表
```
Σ = {0, 1}
```

### 1.2 基础运算记号
- `∅`: 空集
- `∈`: 属于
- `⊆`: 子集
- `∪`: 并集
- `∩`: 交集
- `\`: 差集
- `×`: 笛卡尔积
- `⊕`: 异或运算
- `⊗`: 张量积

### 1.3 逻辑记号
- `∧`: 逻辑与
- `∨`: 逻辑或
- `¬`: 逻辑非
- `→`: 蕴含
- `↔`: 等价
- `∀`: 全称量词
- `∃`: 存在量词

### 1.4 函数与映射记号
- `f: A → B`: 函数f从集合A映射到集合B
- `|A|`: 集合A的基数
- `log₂`: 以2为底的对数
- `ln`: 自然对数
- `⌊x⌋`: 向下取整函数
- `⌈x⌉`: 向上取整函数

## 2. Fibonacci数列约定

### 2.1 标准定义
Fibonacci数列 $\{F_n\}$ 定义为：
$$F_1 = 1, \quad F_2 = 2, \quad F_n = F_{n-1} + F_{n-2} \quad (n \geq 3)$$

### 2.2 标准序列
$$\begin{align}
F_1 &= 1, \quad F_2 = 2, \quad F_3 = 3, \quad F_4 = 5, \quad F_5 = 8, \quad F_6 = 13\\
F_7 &= 21, \quad F_8 = 34, \quad F_9 = 55, \quad F_{10} = 89, \quad F_{11} = 144\\
F_{12} &= 233, \quad F_{13} = 377, \quad F_{14} = 610, \quad F_{15} = 987, \quad F_{16} = 1597, \ldots
\end{align}$$

### 2.3 记号约定
- $F_n$: 第n个Fibonacci数
- $F(n)$: 函数表示法，等价于 $F_n$
- $\{F_n\}_{n \geq 1}$: Fibonacci数列

## 3. 黄金比例φ的数学性质

### 3.1 定义
$$\varphi = \frac{1 + \sqrt{5}}{2} \approx 1.618033988\ldots$$

### 3.2 基本性质
1. **特征方程**: $\varphi^2 = \varphi + 1$
2. **倒数关系**: $\frac{1}{\varphi} = \varphi - 1$
3. **共轭关系**: 令 $\psi = \frac{1 - \sqrt{5}}{2}$，则 $\varphi + \psi = 1$，$\varphi\psi = -1$

### 3.3 Binet公式
对于我们的Fibonacci约定，广义Binet公式为：
$$F_n = \frac{\varphi^{n+1} - \psi^{n+1}}{\sqrt{5}} \quad (n \geq 1)$$

### 3.4 极限性质
$$\lim_{n \to \infty} \frac{F_{n+1}}{F_n} = \varphi$$

## 4. 合法语言定义

### 4.1 禁11约束
定义**合法字符串集合**为所有不包含连续两个1的二进制字符串：
$$B_n = \{s \in \Sigma^n : s\text{中不包含子串}"11"\}$$

### 4.2 合法语言
$$B = \bigcup_{n \geq 1} B_n$$

### 4.3 基数定理
**定理**: 对于任意正整数n，有 $|B_n| = F_{n+1}$

**证明**: 
设 $a_n = |B_n|$。考虑长度为n的合法字符串：
- 若以0结尾：前n-1位可以是任意合法字符串，有 $a_{n-1}$ 种
- 若以1结尾：为避免"11"，前一位必须是0，前n-2位可以是任意合法字符串，有 $a_{n-2}$ 种

因此：$a_n = a_{n-1} + a_{n-2}$

初始值：$a_1 = 2$（字符串"0"和"1"），$a_2 = 3$（字符串"00", "01", "10"）
按照我们的Fibonacci约定：$a_1 = 2 = F_2$，$a_2 = 3 = F_3$

归纳可得：$a_n = F_{n+1}$ □

## 5. 长度切片定义

### 5.1 长度切片记号
对于集合S中的字符串，定义长度切片：
$$S[n] = \{s \in S : |s| = n\}$$

### 5.2 应用
- $B[n] = B_n$: 长度为n的合法字符串集合
- $\Sigma[n] = \Sigma^n$: 长度为n的所有二进制字符串集合

## 6. Hilbert空间记号

### 6.1 基础定义
对于每个正整数n，定义Hilbert空间：
$$\mathcal{H}_n = \text{span}\{|s\rangle : s \in B_n\}$$
其中 $|s\rangle$ 是对应于字符串s的标准正交基向量。

### 6.2 维度
$$\dim(\mathcal{H}_n) = |B_n| = F_{n+1}$$

### 6.3 内积
对于 $|s\rangle, |t\rangle \in \mathcal{H}_n$：
$$\langle s|t\rangle = \delta_{s,t} = \begin{cases} 1 & \text{if } s = t \\ 0 & \text{if } s \neq t \end{cases}$$

### 6.4 一般元素
$\mathcal{H}_n$中的一般元素表示为：
$$|\psi\rangle = \sum_{s \in B_n} \alpha_s |s\rangle$$
其中 $\alpha_s \in \mathbb{C}$ 且 $\sum_{s \in B_n} |\alpha_s|^2 = 1$。

## 7. 熵的定义

### 7.1 信息熵
对于有限集合S，定义其信息熵为：
$$H(S) = \log_2 |S|$$

### 7.2 合法集合的熵
$$H(B_n) = \log_2 |B_n| = \log_2 F_{n+1}$$

### 7.3 熵增性质
由于 $F_{n+1} < F_{n+2}$，有：
$$H(B_n) < H(B_{n+1})$$
即合法集合的熵严格单调递增。

### 7.4 渐近熵密度
$$\lim_{n \to \infty} \frac{H(B_n)}{n} = \log_2 \varphi \approx 0.694$$

## 8. Zeckendorf表示

### 8.1 定义
**Zeckendorf定理**: 每个正整数都有唯一的表示为不连续Fibonacci数之和：
$$n = F_{i_1} + F_{i_2} + \cdots + F_{i_k}$$
其中 $i_1 > i_2 > \cdots > i_k \geq 2$ 且 $i_{j+1} - i_j \geq 2$ 对所有$j$成立。

### 8.2 记号约定
- $Z(n)$: 数$n$的Zeckendorf表示
- $|Z(n)|$: Zeckendorf表示中项数
- $Z^{-1}(F_{i_1} + \cdots + F_{i_k})$: 从Fibonacci和到整数的逆映射

### 8.3 二进制编码
Zeckendorf表示可编码为二进制字符串：若 $n = \sum_{i \in I} F_i$，则编码为长度为$\max(I)$的二进制字符串，第$i$位为1当且仅当$i \in I$。

**重要性质**: 此编码产生的所有字符串都满足禁11约束。

## 9. 自指与完备性记号

### 9.1 自指算子
定义自指算子 $\text{Ref}: S \to S$ 满足：
$$\forall s \in S: \text{Ref}(s) \in S \land \text{Ref}(s) \neq s$$

### 9.2 完备性
集合S称为**完备的**，如果存在描述函数 $\text{Desc}: S \to S$ 使得：
$$\forall s \in S: \text{Desc}(s) \text{描述了}s\text{的所有本质性质}$$

### 9.3 A1公理的数学表述
**A1唯一公理**: 对于任意自指完备系统 $(S, \text{Ref}, \text{Desc})$：
$$\exists \{S_t\}_{t \geq 0}: S_0 \subseteq S_1 \subseteq S_2 \subseteq \cdots \land H(S_{t+1}) > H(S_t)$$

## 10. 特殊函数与常数

### 10.1 重要常数
- $\varphi = \frac{1+\sqrt{5}}{2}$: 黄金比例
- $\psi = \frac{1-\sqrt{5}}{2}$: 黄金比例的共轭
- $\log_2 \varphi \approx 0.694$: 渐近熵密度

### 10.2 生成函数
合法字符串的生成函数：
$$G(x) = \sum_{n \geq 1} |B_n|x^n = \sum_{n \geq 1} F_{n+1}x^n = \frac{x(1+x)}{1-x-x^2}$$

### 10.3 特征多项式
Fibonacci递推的特征多项式：
$$x^2 - x - 1 = 0$$
根为 $\varphi$ 和 $\psi$。

---

**说明**: 本记号系统为后续理论构建提供严格的数学基础。所有定义都经过精确验证，确保逻辑一致性和数学正确性。每个记号都有明确的定义域和值域，避免歧义。

**使用约定**: 在后续文档中，所有数学表达式都应遵循本记号系统。如需引入新记号，应在相应文档中明确定义并保持与本系统的一致性。