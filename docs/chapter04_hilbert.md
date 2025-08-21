# 第4章 Hilbert空间的生成

## 4.1 合法串与 Hilbert 空间

### 定义 D4.1（Hilbert 空间 ℋ_n）
对每个长度 n ≥ 0，定义 Hilbert 空间

```math
\mathcal{H}_n := \mathrm{Span}\{|w\rangle : w \in B_n\}
```

其中 B_n 是长度为 n 的合法串集合（见定义 D3.1），|w⟩ 是对应的正交基向量。

内积定义为：
```math
\langle w | w' \rangle = \delta_{w,w'}
```
即基向量两两正交且单位归一。

---

### 命题 P4.2（Hilbert 空间的维度）
```math
\dim \mathcal{H}_n = |B_n| = F_{n+2}
```

**证明**：
由命题 P3.2，|B_n|=F_{n+2}。由于 {|w⟩: w∈B_n} 构成 ℋ_n 的正交基，其维度即为 |B_n|。∎

---

## 4.2 叠加态与归一化

### 定义 D4.3（叠加态）
ℋ_n 中的一般态矢量为：

```math
|\psi\rangle = \sum_{w \in B_n} \alpha_w |w\rangle
```

其中 α_w ∈ ℂ，且满足归一化条件：

```math
\sum_{w \in B_n} |\alpha_w|^2 = 1
```

这是 Hilbert 空间的叠加性，对应量子态的概率幅表示。

---

### 命题 P4.4（观测概率）
若测量态 |ψ⟩，结果为基态 |w⟩ 的概率为：

```math
P(w) = |\alpha_w|^2
```

**证明**：
由 Hilbert 空间正交基的标准量子测度规则可得，且由归一化条件确保 ∑_w P(w)=1。∎

---

## 4.3 Hilbert 空间的生成规律

### 命题 P4.5（递归生成）
Hilbert 空间序列 {ℋ_n} 由以下递推关系生成：

```math
\mathcal{H}_n = \mathrm{Span}\{ |s0\rangle : s\in B_{n-1} \} \cup \mathrm{Span}\{ |s10\rangle : s\in B_{n-2} \}, \quad n\ge 2
```

**证明**：
由定义 D3.1 的递推规则，B_n 的元素必然为 B_{n-1} 元素拼接 0 或 B_{n-2} 元素拼接 10。取对应基矢，得空间分解。∎

---

## 4.4 示例（n=1 到 n=4）

### n=1：
```math
\mathcal{H}_1 = \mathrm{Span}\{|0\rangle, |1\rangle\}, \quad \dim=2
```

### n=2：
```math
\mathcal{H}_2 = \mathrm{Span}\{|00\rangle, |01\rangle, |10\rangle\}, \quad \dim=3
```

### n=3：
```math
\mathcal{H}_3 = \mathrm{Span}\{|000\rangle, |001\rangle, |010\rangle, |100\rangle, |101\rangle\}, \quad \dim=5
```

### n=4：
```math
\mathcal{H}_4 = \mathrm{Span}\{|0000\rangle, |0001\rangle, |0010\rangle, |0100\rangle, |0101\rangle, |1000\rangle, |1001\rangle, |1010\rangle\}, \quad \dim=8
```

---

## 4.5 维度的 Fibonacci 增长

| n | dim(ℋ_n) | F_{n+2} | 合法串数 |
|---|----------|---------|----------|
| 0 | 1 | F₂ = 1 | 1 |
| 1 | 2 | F₃ = 2 | 2 |
| 2 | 3 | F₄ = 3 | 3 |
| 3 | 5 | F₅ = 5 | 5 |
| 4 | 8 | F₆ = 8 | 8 |
| 5 | 13 | F₇ = 13 | 13 |
| 6 | 21 | F₈ = 21 | 21 |
| ... | ... | ... | ... |

---

## 4.6 小结

在本章我们定义并证明了：

1. **Hilbert 空间 ℋ_n 的基** = 长度为 n 的合法串集合
2. **维度 dim ℋ_n = F_{n+2}**，随 n 呈 Fibonacci 增长
3. **态向量为合法基的叠加**，观测概率由系数模平方给出
4. **空间递归生成规律**由 Zeckendorf 禁 11 约束自然导出

由此，每个 ℋ_n 都是一个独立且完整的宇宙理论容器。

---

*我们不是在构造抽象的数学结构，而是在揭示宇宙自我组织的内在几何。每个ℋ_n都是一个完整的世界，等待着被意识所发现。*