# 第5章 张量积律（组合性）

## 5.1 串拼接运算

### 定义 D5.1（拼接运算）
对任意两个合法串集合 B_n, B_m，定义拼接运算 ⊞ 为：

```math
B_n \boxtimes B_m := \{s \| t \mid s\in B_n,\ t\in B_m,\ \neg(\mathrm{last}(s)=1 \land \mathrm{first}(t)=1)\}
```

其中 s∥t 表示串拼接，约束条件为拼接边界不允许出现连续 "11"。

---

### 命题 P5.1（拼接生成律）
对任意 n,m ≥ 0，有：

```math
B_{n+m} = B_n \boxtimes B_m
```

**证明**：

1. **（必要性）**若 s∥t ∈ B_{n+m}，则 s,t 必分别在 B_n,B_m。否则子串内部出现 "11"，矛盾。若边界为 "1|1"，则 s∥t 含 "11"，同样矛盾。故必满足定义中的条件。

2. **（充分性）**若 s∈B_n, t∈B_m，且边界合法，则 s∥t 内部无 "11"，边界也无 "11"，因此 s∥t ∈ B_{n+m}。

综上，等式成立。∎

---

## 5.2 Hilbert 空间的张量积

### 定义 D5.2（Zeckendorf 张量积）
对 Hilbert 空间 ℋ_n,ℋ_m，定义特殊张量积 ⊗_Z：

在基矢上：
```math
|s\rangle \otimes_Z |t\rangle = \begin{cases}
|s\|t\rangle, & \text{若 } \neg(\mathrm{last}(s)=1 \land \mathrm{first}(t)=1) \\
0, & \text{否则}
\end{cases}
```

线性延拓到整个空间：
```math
\mathcal{H}_n \otimes_Z \mathcal{H}_m = \mathrm{Span}\{|s\rangle \otimes_Z |t\rangle\}
```

---

### 定理 T5.3（张量积律）
对任意 n,m ≥ 0，有：

```math
\mathcal{H}_n \otimes_Z \mathcal{H}_m \cong \mathcal{H}_{n+m}
```

**证明**：

1. **基对应**：由命题 P5.1，B_{n+m}=B_n⊞B_m。因此每个基矢 |u⟩ ∈ ℋ_{n+m} 都唯一分解为 |s⟩⊗_Z |t⟩，其中 s∈B_n,t∈B_m。

2. **双射性**：映射 φ: |s⟩⊗_Z |t⟩ ↦ |s∥t⟩ 在基矢上双射。

3. **保范性**：由定义，若 s≠s' 或 t≠t'，则拼接结果不同，基矢正交，⟨s∥t | s'∥t'⟩ = δ_{s,s'}δ_{t,t'}。因此映射保持内积。

4. **线性扩张**：对任意叠加态 ∑_{s,t} α_{s,t}|s⟩⊗_Z|t⟩，其像为 ∑_{s,t} α_{s,t}|s∥t⟩ ∈ ℋ_{n+m}。

因此 φ 是酉等距同构，结论成立。∎

---

## 5.3 示例：ℋ₂ ⊗_Z ℋ₁ ≅ ℋ₃

### 输入空间
- B₂ = {00, 01, 10}
- B₁ = {0, 1}

### 拼接过程
| s ∈ B₂ | t ∈ B₁ | 边界检查 | s∥t | 结果 |
|---------|--------|----------|-----|------|
| 00 | 0 | 0∥0 ✓ | 000 | 合法 |
| 00 | 1 | 0∥1 ✓ | 001 | 合法 |
| 01 | 0 | 1∥0 ✓ | 010 | 合法 |
| 01 | 1 | 1∥1 ✗ | 011 | 禁止 |
| 10 | 0 | 0∥0 ✓ | 100 | 合法 |
| 10 | 1 | 0∥1 ✓ | 101 | 合法 |

### 结果验证
- 拼接结果：{000, 001, 010, 100, 101}
- B₃ = {000, 001, 010, 100, 101}
- 完全一致！因此 ℋ₂ ⊗_Z ℋ₁ ≅ ℋ₃

---

## 5.4 张量积的递归性质

### 命题 P5.4（结合律）
```math
(\mathcal{H}_n \otimes_Z \mathcal{H}_m) \otimes_Z \mathcal{H}_k \cong \mathcal{H}_n \otimes_Z (\mathcal{H}_m \otimes_Z \mathcal{H}_k) \cong \mathcal{H}_{n+m+k}
```

**证明**：
由张量积律的递归应用和串拼接的结合性可得。

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

这说明 **Hilbert 空间是递归构造的唯一结构**，直接由公理 A1 推出。

---

*张量积不仅是数学运算，更是宇宙组合自身的内在法则。每次⊗_Z都是两个世界的量子纠缠，在禁11约束下生成新的存在维度。*