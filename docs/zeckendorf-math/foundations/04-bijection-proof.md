# Zeckendorf双射的构造性证明

## 定义 4.1（扩展的φ-编码映射）
定义映射 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 为：
$$\psi(n) = \begin{cases}
\varepsilon & \text{若 } n = 0 \\
\text{encode}(n) & \text{若 } n \geq 1
\end{cases}$$

其中 $\text{encode}: \mathbb{N}^+ \to \Phi \setminus \{\varepsilon\}$ 如定义1.4所定义。

## 定义 4.2（扩展的解码映射）
定义映射 $\omega: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 为：
$$\omega(s) = \begin{cases}
0 & \text{若 } s = \varepsilon \\
\text{decode}(s) & \text{若 } s \in \Phi \setminus \{\varepsilon\}
\end{cases}$$

其中 $\text{decode}: \Phi \setminus \{\varepsilon\} \to \mathbb{N}^+$ 如定义1.5所定义。

## 定理 4.1（扩展双射定理）
映射 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 与 $\omega: \mathbb{F}\mathbb{N} \to \mathbb{N}$ 构成双射，且互为逆映射。

**证明：**
首先证明 $\omega \circ \psi = \text{id}_{\mathbb{N}}$：

**情况1**：设 $n = 0$，则 $\psi(0) = \varepsilon$，故 $\omega(\psi(0)) = \omega(\varepsilon) = 0 = n$。

**情况2**：设 $n \geq 1$，则 $\psi(n) = \text{encode}(n) \in \Phi \setminus \{\varepsilon\}$。
由定理1.2，$\omega(\psi(n)) = \text{decode}(\text{encode}(n)) = n$。

接下来证明 $\psi \circ \omega = \text{id}_{\mathbb{F}\mathbb{N}}$：

**情况1**：设 $s = \varepsilon$，则 $\omega(\varepsilon) = 0$，故 $\psi(\omega(\varepsilon)) = \psi(0) = \varepsilon = s$。

**情况2**：设 $s \in \Phi \setminus \{\varepsilon\}$，则 $\omega(s) = \text{decode}(s) \geq 1$。
由定理1.2，$\psi(\omega(s)) = \text{encode}(\text{decode}(s)) = s$。

因此 $\psi$ 和 $\omega$ 互为逆映射。 ∎

## 定理 4.2（双射的构造性质）
双射 $\psi$ 和 $\omega$ 具有构造性：存在有限步骤的计算过程实现这两个映射。

**证明：**
$\psi$ 的构造性：对任意 $n \in \mathbb{N}$，若 $n = 0$ 则 $\psi(n) = \varepsilon$；若 $n \geq 1$，则由定理1.1的构造性证明，Zeckendorf分解在有限步骤内完成，从而 $\psi(n) = \text{encode}(n)$ 可构造。

$\omega$ 的构造性：对任意 $s \in \mathbb{F}\mathbb{N}$，若 $s = \varepsilon$ 则 $\omega(s) = 0$；否则 $\omega(s) = \sum_{i=1}^{|s|} s_i \cdot F_i$ 为有限和，可在有限步骤内计算。 ∎

## 定理 4.3（双射的函数方程特征化）
双射 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 是满足以下条件的唯一映射：

1. $\psi(0) = \varepsilon$
2. $\psi(1) = 1$
3. 对所有 $n \geq 1$，$\psi(n+1)$ 为字典序中 $\psi(n)$ 的后继φ-编码串

**证明：**
**存在性**：已知 $\psi$ 满足条件1和2。

对于条件3，需证明 $\psi(n+1)$ 确实是字典序后继。由于 $\psi$ 保持自然数的顺序，且φ-编码串按字典序排列恰好对应其数值顺序，条件3成立。

**唯一性**：假设存在另一映射 $\psi'$ 满足相同条件。
由条件1，$\psi'(0) = \psi(0) = \varepsilon$。
由条件2，$\psi'(1) = \psi(1) = 1$。
由条件3和归纳法，$\psi'(n) = \psi(n)$ 对所有 $n \geq 0$。 ∎

## 推论 4.1（计数性质保持）
双射 $\psi$ 保持计数性质：设 $A_k = \{n \in \mathbb{N} : |\psi(n)| = k\}$，则：
$$|A_k| = F_{k+1}$$

**证明：**
$A_k$ 对应所有长度为 $k$ 的φ-编码串的原像。
由定理1.3，长度为 $k$ 的φ-编码串恰有 $F_{k+1}$ 个，
故 $|A_k| = F_{k+1}$。 ∎

## 定理 4.4（双射的有限性特征）
双射 $\psi$ 和 $\omega$ 的计算过程具有有限性：

1. 对任意 $n \in \mathbb{N}$，$\psi(n)$ 可在有限步骤内确定
2. 对任意 $s \in \mathbb{F}\mathbb{N}$，$\omega(s)$ 可在有限步骤内确定

**证明：**
1. 由定理1.1的构造性证明，Zeckendorf分解过程在有限步骤内终止，故 $\psi(n)$ 可在有限步骤内计算。

2. $\omega(s) = \sum_{i=1}^{|s|} s_i \cdot F_i$ 为有限和，且 $|s|$ 有限，故可在有限步骤内计算。 ∎

## 定义 4.3（双射的逆向构造）
给定φ-编码串 $s \in \Phi$，定义**逆向Zeckendorf分解**为从低位到高位的贪心算法：

设 $s = b_k b_{k-1} \cdots b_1$，则：
$$\text{value}(s) = \sum_{i: b_i=1} F_i$$

## 定理 4.5（逆向构造的等价性）
逆向Zeckendorf分解与标准Zeckendorf分解等价。

**证明：**
设 $s = b_k \cdots b_1 \in \Phi$ 且 $n = \sum_{i: b_i=1} F_i$。

需证明：若 $b_i = b_j = 1$ 且 $i > j$，则 $i - j \geq 2$。

若 $i - j = 1$，则 $b_i = b_{i-1} = 1$，形成"11"模式，与 $s \in \Phi$ 矛盾。
故必有 $i - j \geq 2$，满足Zeckendorf分解的非连续性约束。 ∎

## 推论 4.2（双射的完备性）
双射 $\psi: \mathbb{N} \to \mathbb{F}\mathbb{N}$ 建立了自然数与φ-自然数系统的完全等价性，
使得所有自然数的性质都可在φ-系统中得到对应表述。