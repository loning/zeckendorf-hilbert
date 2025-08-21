# 第4章 Hilbert空间的生成

## 4.1 合法串与 Hilbert 空间

### 定义 D4.1（Hilbert 空间 ℋ_n）
对每个长度 n ≥ 0，定义复Hilbert空间

```math
\mathcal{H}_n := \mathrm{Span}_{\mathbb{C}}\{|w\rangle : w \in B_n\}
```

其中：
- B_n 是长度为 n 的合法串集合（见定义 D3.1）
- {|w⟩ : w ∈ B_n} 构成标准正交基
- 内积定义为：
```math
\langle w | w' \rangle = \delta_{w,w'} \quad (\text{Kronecker delta})
```

**严格性质**：
1. **正交性**：∀ w≠w' ∈ B_n, ⟨w|w'⟩ = 0
2. **归一性**：∀ w ∈ B_n, ⟨w|w⟩ = 1  
3. **完备性**：{|w⟩ : w ∈ B_n} 线性张成整个 ℋ_n

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
\langle \psi | \psi \rangle = \sum_{w \in B_n} |\alpha_w|^2 = 1
```

**严格的内积计算**：
```math
\langle \psi | \phi \rangle = \sum_{w \in B_n} \overline{\alpha_w} \beta_w
```

其中 φ = ∑ β_w |w⟩，ˉα_w 表示 α_w 的复共轭。

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
\mathcal{H}_n = \mathrm{Span}\{ |s0\rangle : s\in B_{n-1} \} \oplus \mathrm{Span}\{ |s10\rangle : s\in B_{n-2} \}, \quad n\ge 2
```

其中 ⊕ 表示直和（两个子空间的正交和）。

**严格证明**：
1. **基的分解**：由定义D3.1，B_n = {s0 : s∈B_{n-1}} ∪ {s10 : s∈B_{n-2}}
2. **正交性**：设 v₁ = s₁0, v₂ = s₂10，则 |v₁| = n-1+1 = n，|v₂| = n-2+2 = n
   - 但 v₁ 末尾为 0，v₂ 末尾为 10，因此 v₁ ≠ v₂
   - 由基的正交性，⟨v₁|v₂⟩ = 0
3. **维度验证**：
   ```math
   \dim(\mathcal{H}_n) = |B_{n-1}| + |B_{n-2}| = F_{(n-1)+2} + F_{(n-2)+2} = F_{n+1} + F_n = F_{n+2}
   ```
   这正确地使用了Fibonacci递推关系。
4. **完备性**：两个子空间张成的基恰好覆盖了 B_n 的所有元素

因此 ℋ_n 是两个正交子空间的直和。∎

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