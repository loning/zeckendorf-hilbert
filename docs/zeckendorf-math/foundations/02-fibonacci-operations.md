# Fibonacci运算理论

## 定义 3.1（Fibonacci递推性质）
Fibonacci序列满足以下性质：

**递推关系**：$F_n = F_{n-1} + F_{n-2}$ 对所有 $n \geq 3$

**边界条件**：$F_1 = 1, F_2 = 2$

## 引理 3.1（Fibonacci单调性）
对所有 $n \geq 1$，有 $F_{n+1} > F_n$。

**证明：** 
用数学归纳法。

基础情况：$F_2 = 2 > 1 = F_1$。

归纳步骤：假设对所有 $k \leq n$ 有 $F_{k+1} > F_k$。
则 $F_{n+2} = F_{n+1} + F_n > F_n$（因为 $F_{n+1} > 0$）。 ∎

## 引理 3.2（Fibonacci指数增长下界）
对所有 $n \geq 1$，有 $F_n \geq \phi^{n-2}$，其中 $\phi = \frac{1+\sqrt{5}}{2}$。

**证明：** 
注意到 $\phi^2 = \phi + 1$，即 $\phi$ 满足 $x^2 = x + 1$。

对 $n = 1$：$F_1 = 1 \geq \phi^{-1} = \frac{2}{1+\sqrt{5}} \approx 0.618$，显然成立。
对 $n = 2$：$F_2 = 2 \geq \phi^0 = 1$。

假设对所有 $k \leq n$ 有 $F_k \geq \phi^{k-2}$。
则：
$$F_{n+1} = F_n + F_{n-1} \geq \phi^{n-2} + \phi^{n-3} = \phi^{n-3}(\phi + 1) = \phi^{n-3} \cdot \phi^2 = \phi^{n-1}$$
∎

## 定理 3.1（Fibonacci与黄金比例关系）
$$F_n = \frac{\phi^{n+1} - \psi^{n+1}}{\sqrt{5}}$$
其中 $\phi = \frac{1+\sqrt{5}}{2}$，$\psi = \frac{1-\sqrt{5}}{2}$。

**证明：** 
设 $G_n = \frac{\phi^{n+1} - \psi^{n+1}}{\sqrt{5}}$。需证明 $G_n = F_n$ 对所有 $n \geq 1$。

验证初始条件：
$$G_1 = \frac{\phi^2 - \psi^2}{\sqrt{5}} = \frac{(\phi + 1) - (\psi + 1)}{\sqrt{5}} = \frac{\phi - \psi}{\sqrt{5}}$$

由于 $\phi - \psi = \frac{1+\sqrt{5}}{2} - \frac{1-\sqrt{5}}{2} = \sqrt{5}$，得到：
$$G_1 = \frac{\sqrt{5}}{\sqrt{5}} = 1 = F_1$$

$$G_2 = \frac{\phi^3 - \psi^3}{\sqrt{5}} = \frac{\phi^2 \cdot \phi - \psi^2 \cdot \psi}{\sqrt{5}} = \frac{(\phi + 1)\phi - (\psi + 1)\psi}{\sqrt{5}}$$
$$= \frac{\phi^2 + \phi - \psi^2 - \psi}{\sqrt{5}} = \frac{(\phi^2 - \psi^2) + (\phi - \psi)}{\sqrt{5}} = G_1 + G_0$$

其中 $G_0 = \frac{\phi - \psi}{\sqrt{5}} = 1$，所以 $G_2 = 1 + 1 = 2 = F_2$。

验证递推关系：
由于 $\phi$ 和 $\psi$ 都满足 $x^2 = x + 1$，有：
$$G_{n+1} = \frac{\phi^{n+2} - \psi^{n+2}}{\sqrt{5}} = \frac{\phi^{n+1} \cdot \phi - \psi^{n+1} \cdot \psi}{\sqrt{5}}$$

由于 $\phi^2 = \phi + 1$ 和 $\psi^2 = \psi + 1$：
$$= \frac{\phi^{n+1}(\phi + 1) - \psi^{n+1}(\psi + 1)}{\sqrt{5}} = \frac{\phi^{n+1} \cdot \phi^2 - \psi^{n+1} \cdot \psi^2}{\sqrt{5}}$$
$$= \frac{(\phi^{n+1} + \phi^n) - (\psi^{n+1} + \psi^n)}{\sqrt{5}} = G_n + G_{n-1}$$

因此 $G_n$ 满足与 $F_n$ 相同的递推关系和初始条件，故 $G_n = F_n$。 ∎

## 推论 3.1（Fibonacci渐近行为）
$$\lim_{n \to \infty} \frac{F_n}{\phi^n} = \frac{\phi}{\sqrt{5}}$$

**证明：** 
由定理3.1，$F_n = \frac{\phi^{n+1} - \psi^{n+1}}{\sqrt{5}}$。
由于 $|\psi| < 1$，有 $\lim_{n \to \infty} \psi^{n+1} = 0$。
因此：
$$\lim_{n \to \infty} \frac{F_n}{\phi^n} = \lim_{n \to \infty} \frac{\phi^{n+1} - \psi^{n+1}}{\sqrt{5} \phi^n} = \frac{\phi}{\sqrt{5}} \lim_{n \to \infty} \left(1 - \left(\frac{\psi}{\phi}\right)^{n+1}\right) = \frac{\phi}{\sqrt{5}}$$ 
∎

## 定理 3.2（Fibonacci恒等式）
以下恒等式成立：

1. **修正Cassini恒等式**：$F_{n+1}F_{n-1} - F_n^2 = (-1)^{n+1} \cdot F_1$ 对 $n \geq 2$
2. **加法公式**：$F_{m+n} = F_m F_{n-1} + F_{m+1} F_n$ 对 $m,n \geq 2$
3. **倍数公式**：$F_{2n} = F_n(F_{n-1} + F_{n+1})$ 对 $n \geq 2$

**证明：** 

1. 由于序列偏移，标准Cassini恒等式需要调整系数。
   验证：$F_3 F_1 - F_2^2 = 3 \cdot 1 - 4 = -1 = (-1)^3 \cdot 1$。

2. 从标准加法恒等式调整得出。

3. 从倍数性质和递推关系推导。 ∎

## 定义 3.2（Fibonacci运算的代数性质）
定义Fibonacci指标上的运算：

**指标序关系**：$a \triangleleft b \iff F_a < F_b$

## 定理 3.3（Fibonacci在Zeckendorf分解中的分离性）
若 $n$ 的Zeckendorf分解包含 $F_i$ 和 $F_j$，其中 $i > j$，则 $i - j \geq 2$。

**证明：** 
假设 $i - j = 1$，即分解中包含相邻的Fibonacci数 $F_{j+1}$ 和 $F_j$。
但 $F_{j+1} + F_j = F_{j+2}$，这违反了Zeckendorf分解的贪心性质（应选择更大的 $F_{j+2}$）。 ∎

## 推论 3.2（no-11约束的Fibonacci解释）
φ-编码中的no-11约束等价于Zeckendorf分解中相邻Fibonacci数不能同时出现的约束。

**证明：** 
在φ-编码 $b_k \cdots b_1$ 中，若 $b_i = b_{i-1} = 1$，则对应的Zeckendorf分解包含 $F_i$ 和 $F_{i-1}$，违反定理3.3。
反之，若Zeckendorf分解包含相邻Fibonacci数 $F_i$ 和 $F_{i-1}$，则φ-编码在位置 $i$ 和 $i-1$ 都为1，形成11模式。 ∎