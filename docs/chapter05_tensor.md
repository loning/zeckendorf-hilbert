# 第5章 张量积律（组合性）

## 5.1 串拼接运算

### 定义 D5.1（拼接运算）
对任意两个合法串集合 $B_n, B_m$，定义拼接运算 $\boxtimes$ 为：

$$B_n \boxtimes B_m := \{s \| t \mid s\in B_n,\ t\in B_m,\ \neg(\mathrm{last}(s)=1 \land \mathrm{first}(t)=1)\}$$

其中 $s\|t$ 表示串拼接，约束条件为拼接边界不允许出现连续 "$11$"。

---

### 命题 P5.1（拼接生成律）
对任意 $n,m \geq 0$，有：

$$B_{n+m} = B_n \boxtimes B_m$$

**严格证明**：

**第一步：⊆方向**（B_{n+m} ⊆ B_n \boxtimes B_m）

设 w ∈ B_{n+m}，|w| = n+m。由于串的长度是确定的，w 在位置 n 处有唯一分割点，因此存在唯一分解 w = s∥t，其中 |s| = n, |t| = m。

1. **子串合法性**：由于 w ∈ B_{n+m}（无"11"），则 s 和 t 内部都无"11"
2. **边界合法性**：拼接点不能产生"11"，即 ¬(last(s)=1 ∧ first(t)=1)
3. **因此**：s ∈ B_n, t ∈ B_m，且满足拼接条件，所以 w ∈ B_n \boxtimes B_m

**第二步：⊇方向**（B_n \boxtimes B_m ⊆ B_{n+m}）

设 w ∈ B_n \boxtimes B_m，则 w = s∥t，其中 s ∈ B_n, t ∈ B_m，且边界合法。

1. **长度正确**：|w| = |s| + |t| = n + m
2. **无"11"约束**：
   - s 内部无"11"（因为 s ∈ B_n）
   - t 内部无"11"（因为 t ∈ B_m）  
   - 边界无"11"（由拼接条件保证）
3. **因此**：w ∈ B_{n+m}

**结论**：B_{n+m} = B_n \boxtimes B_m ∎

---

## 5.2 Hilbert 空间的张量积

### 定义 D5.2（Zeckendorf 张量积）
对 Hilbert 空间 \mathcal{H}_n,\mathcal{H}_m，定义特殊张量积 \otimes_Z：

在基矢上：
```math
|s\rangle \otimes_Z |t\rangle = \begin{cases}
|s\|t\rangle, & \text{若 } \neg(\mathrm{last}(s)=1 \land \mathrm{first}(t)=1) \\
0, & \text{否则}
\end{cases}
```

线性延拓到整个空间：
```math
\mathcal{H}_n \otimes_Z \mathcal{H}_m = \mathrm{Span}\{|s\rangle \otimes_Z |t\rangle \mid s \in B_n, t \in B_m\}
```

即对任意 $|\psi\rangle = \sum_{s \in B_n} \alpha_s |s\rangle \in \mathcal{H}_n$ 和 $|\phi\rangle = \sum_{t \in B_m} \beta_t |t\rangle \in \mathcal{H}_m$：
```math
|\psi\rangle \otimes_Z |\phi\rangle = \sum_{s \in B_n, t \in B_m} \alpha_s \beta_t (|s\rangle \otimes_Z |t\rangle)
```

---

### 定理 T5.3（张量积律）
对任意 n,m ≥ 0，有：

```math
\mathcal{H}_n \otimes_Z \mathcal{H}_m \cong \mathcal{H}_{n+m}
```

**证明**：

我们构造映射 $\phi: \mathcal{H}_n \otimes_Z \mathcal{H}_m \to \mathcal{H}_{n+m}$：

**步骤1：基矢映射的定义**
$$\phi(|s\rangle \otimes_Z |t\rangle) = \begin{cases}
|s\|t\rangle, & \text{若 } \neg(\mathrm{last}(s)=1 \land \mathrm{first}(t)=1) \\
\text{未定义}, & \text{否则}
\end{cases}$$

**步骤2：基对应完备性**
由命题 P5.1，$B_{n+m} = B_n \boxtimes B_m$。因此每个基矢 $|u\rangle \in \mathcal{H}_{n+m}$ 都唯一分解为 $u = s\|t$，其中存在唯一的 $s \in B_n, t \in B_m$ 满足拼接条件。

**步骤3：双射性验证**
- **单射性**：若 $\phi(|s\rangle \otimes_Z |t\rangle) = \phi(|s'\rangle \otimes_Z |t'\rangle)$，则 $|s\|t\rangle = |s'\|t'\rangle$，由串拼接的唯一性，得 $s = s'$ 且 $t = t'$。
- **满射性**：对任意 $|u\rangle \in \mathcal{H}_{n+m}$，由步骤2知存在唯一分解 $u = s\|t$，因此 $\phi(|s\rangle \otimes_Z |t\rangle) = |u\rangle$。

**步骤4：保范性验证**
对基矢：$\langle s\|t | s'\|t'\rangle = \delta_{s\|t, s'\|t'} = \delta_{s,s'}\delta_{t,t'}$
而：$\langle |s\rangle \otimes_Z |t\rangle | |s'\rangle \otimes_Z |t'\rangle\rangle = \delta_{s,s'}\delta_{t,t'}$
因此 $\phi$ 保持基矢的正交关系。

**步骤5：线性扩张**
$\phi$ 线性延拓：$\phi\left(\sum_{s,t} \alpha_{s,t}|s\rangle\otimes_Z|t\rangle\right) = \sum_{s,t} \alpha_{s,t}|s\|t\rangle \in \mathcal{H}_{n+m}$

因此 $\phi$ 是酉等距同构，$\mathcal{H}_n \otimes_Z \mathcal{H}_m \cong \mathcal{H}_{n+m}$。∎

---

## 5.3 示例：ℋ₂ ⊗_Z ℋ₁ ≅ ℋ₃

### 输入空间
- B₂ = {00, 01, 10}
- B₁ = {0, 1}

### 拼接过程
完整的拼接计算表：

| s ∈ B₂ | t ∈ B₁ | last(s) | first(t) | 边界检查条件 | s∥t | 拼接结果 |
|---------|--------|---------|----------|--------------|-----|----------|
| 00 | 0 | 0 | 0 | ¬(0=1 ∧ 0=1) ✓ | 000 | 合法 |
| 00 | 1 | 0 | 1 | ¬(0=1 ∧ 1=1) ✓ | 001 | 合法 |
| 01 | 0 | 1 | 0 | ¬(1=1 ∧ 0=1) ✓ | 010 | 合法 |
| 01 | 1 | 1 | 1 | ¬(1=1 ∧ 1=1) ✗ | 011 | **禁止** |
| 10 | 0 | 0 | 0 | ¬(0=1 ∧ 0=1) ✓ | 100 | 合法 |
| 10 | 1 | 0 | 1 | ¬(0=1 ∧ 1=1) ✓ | 101 | 合法 |

**边界条件分析**：只有当 last(s)=1 且 first(t)=1 时拼接被禁止，这正好对应 "01" ⊕ "1" → "011" 包含连续"11"的情况。

### 结果验证
- **拼接结果**：B₂ ⊞ B₁ = {000, 001, 010, 100, 101}
- **目标空间**：B₃ = {000, 001, 010, 100, 101}  
- **维度验证**：|B₂ ⊞ B₁| = 5 = |B₃| = F₅
- **完全一致**！因此 $\mathcal{H}_2 \otimes_Z \mathcal{H}_1 \cong \mathcal{H}_3$

**Fibonacci维度关系确认**：
- $\dim(\mathcal{H}_2) = |B_2| = 3 = F_4$
- $\dim(\mathcal{H}_1) = |B_1| = 2 = F_3$  
- $\dim(\mathcal{H}_3) = |B_3| = 5 = F_5$
- 验证：$F_3 \times F_4 \not= F_5$，但通过 No-11 约束投影后维度正确匹配

---

## 5.4 张量积的递归性质

### 命题 P5.4（结合律）
```math
(\mathcal{H}_n \otimes_Z \mathcal{H}_m) \otimes_Z \mathcal{H}_k \cong \mathcal{H}_n \otimes_Z (\mathcal{H}_m \otimes_Z \mathcal{H}_k) \cong \mathcal{H}_{n+m+k}
```

**证明**：

**第一步：串拼接的结合性**
对任意 $s \in B_n, t \in B_m, u \in B_k$，串拼接满足结合律：$(s\|t)\|u = s\|(t\|u)$，当且仅当所有边界条件满足。

**第二步：张量积的结合性**
由于 Zeckendorf 张量积 $\otimes_Z$ 本质上由串拼接和边界约束定义，我们需要验证：

对任意合法的基矢组合：
$$((|s\rangle \otimes_Z |t\rangle) \otimes_Z |u\rangle = |s\rangle \otimes_Z (|t\rangle \otimes_Z |u\rangle)$$

**第三步：边界条件的传递性**
- 左结合：$(s\|t)\|u$ 要求 $\neg(\text{last}(s)=1 \land \text{first}(t)=1)$ 且 $\neg(\text{last}(s\|t)=1 \land \text{first}(u)=1)$
- 右结合：$s\|(t\|u)$ 要求 $\neg(\text{last}(t)=1 \land \text{first}(u)=1)$ 且 $\neg(\text{last}(s)=1 \land \text{first}(t\|u)=1)$

由 "No-11" 约束的局部性，这些条件等价。

**第四步：维度验证**
$$\dim((\mathcal{H}_n \otimes_Z \mathcal{H}_m) \otimes_Z \mathcal{H}_k) = \dim(\mathcal{H}_n \otimes_Z (\mathcal{H}_m \otimes_Z \mathcal{H}_k)) = \dim(\mathcal{H}_{n+m+k})$$

因此结合律成立。∎

### 推论 C5.4.1（多重分解）
任意 Hilbert 空间 ℋ_n 都可以分解为基础空间的张量积：

```math
\mathcal{H}_n \cong \mathcal{H}_{n_1} \otimes_Z \mathcal{H}_{n_2} \otimes_Z \cdots \otimes_Z \mathcal{H}_{n_k}
```

其中 n₁ + n₂ + ⋯ + n_k = n。

---

## 5.5 小结

本章我们证明了：

1. **拼接生成律**：
   ```math
   B_{n+m} = B_n \boxtimes B_m
   ```

2. **张量积律**：
   ```math
   \mathcal{H}_n \otimes_Z \mathcal{H}_m \cong \mathcal{H}_{n+m}
   ```

3. **高维 Hilbert 空间由低维 Hilbert 空间递归生成**，且新空间继续遵守"禁止连续 11"的约束。

这说明 **Hilbert 空间是递归构造的唯一结构**，直接由公理A1（SRA）推出。

---

*张量积不仅是数学运算，更是宇宙组合自身的内在法则。每次\otimes_Z都是两个世界的量子纠缠，在禁11约束下生成新的存在维度。*