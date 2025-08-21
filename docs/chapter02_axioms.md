# 第2章 公理与基础定义

## 2.1 自指完备 (Self-Reference Completeness)

### 定义 D2.1（自指完备系统）
一个形式系统 $S$ 称为**自指完备** (self-reference complete)，若存在编码器 $E \in S$ 和求值函数 $\mathrm{Eval} : S \times S \to S$，使得：

1. **自指性**：
   $$\forall x \in S, \quad \mathrm{Eval}(E,x) \in S \quad \text{且} \quad \mathrm{Eval}(E,E) \text{ 有定义}$$

2. **内生性**：系统的所有操作均可由 $S$ 内部元素表示：
   $$\forall \text{操作} \, f, \exists p \in S : \mathrm{Eval}(p,\cdot) = f(\cdot)$$

3. **封闭性**：
   $$\forall p,x \in S, \quad p,x \text{ 合法} \Rightarrow \mathrm{Eval}(p,x) \in S$$

---

### 定义 D2.2（记录）
一次自指执行称为**带记录的求值**，当且仅当执行结果不仅返回值，还在系统状态中生成一条新记录 $r$，并更新为新状态：

$$s_{t+1} = s_t \| r$$

其中 $r \in S$，并且 $|s_{t+1}| > |s_t|$。

换言之，**记录 = 自指必然生成的新符号**。

---

## 2.2 熵 (Entropy)

### 定义 D2.3（系统状态与熵）
设系统 $S$ 在执行 $t$ 步后的所有合法状态集合为 $\Sigma_t \subseteq S$。定义其熵为：

$$H(\Sigma_t) = \log |\Sigma_t|$$

其中：
- $\Sigma_t$ 是经过 $t$ 次自指执行后系统可达的所有状态
- $|\Sigma_t|$ 表示状态集合的基数
- 对数底数取 $2$（比特熵）或 $e$（自然熵）

**严格性要求**：
$$\Sigma_0 \subseteq \Sigma_1 \subseteq \Sigma_2 \subseteq \cdots \quad \text{(单调性)}$$

**熵的数学意义**：测量系统区分不同状态所需的最小信息量。

---

## 2.3 公理陈述

### 公理 A1（自指完备系统必然熵增, SRA）
对任意自指完备系统 $S$，其状态集合序列 $\{\Sigma_t\}_{t\geq 0}$ 必然满足：

$$\forall t \geq 0, \quad H(\Sigma_{t+1}) > H(\Sigma_t)$$

**严格表述**：
$$\forall t \geq 0, \quad |\Sigma_{t+1}| > |\Sigma_t| \quad \Rightarrow \quad \log |\Sigma_{t+1}| > \log |\Sigma_t|$$

**必然性证明骨架**：
1. 自指执行 → 新记录生成（定义D2.2）
2. 新记录 → 状态集合扩展（封闭性）
3. 状态集合扩展 → 基数严格增加
4. 基数严格增加 → 熵严格增加

---

## 2.4 命题：自指与熵增的基本关系

### 命题 P2.1
若系统 $S$ 自指完备，则其任意合法执行步都会增加系统状态长度，即：
$$|s_{t+1}| > |s_t|$$

**证明**：
由定义 D2.2，记录 $r$ 的附加保证了 $s_{t+1} = s_t \parallel r$，且 $|r|>0$。因此 $|s_{t+1}| > |s_t|$。∎

---

### 命题 P2.2（状态扩展引起熵增）
若系统状态长度增加，则必有熵严格增加：

$$|\Sigma_{t+1}| > |\Sigma_t| \quad \Rightarrow \quad H(\Sigma_{t+1}) > H(\Sigma_t)$$

**严格证明**：
1. **前提**：自指执行生成新记录 $r$，使得存在 $s \in \Sigma_t$，新状态 $s' = s \parallel r$
2. **新状态的合法性**：由封闭性（定义D2.1），$s' \in S$
3. **新状态的唯一性**：由于 $|s'| > |s|$，且记录确定性，$s' \notin \Sigma_t$  
4. **集合扩展**：$\Sigma_{t+1} = \Sigma_t \cup \{s'\} \cup \{\text{其他新生成状态}\}$
5. **基数增加**：$|\Sigma_{t+1}| \geq |\Sigma_t| + 1 > |\Sigma_t|$
6. **熵增**：$H(\Sigma_{t+1}) = \log |\Sigma_{t+1}| > \log |\Sigma_t| = H(\Sigma_t)$ ∎

**关键**：第3步确保了新状态的真正新增性。

---

## 2.5 小结

本章我们完成了：

1. **自指完备系统的定义**：自指性、内生性、封闭性
2. **记录的定义**：每次自指执行必生成新串  
3. **熵的定义**：状态集合基数的对数
4. **公理 SRA**：自指完备系统必然熵增
5. **基本推论**：自指 ⇒ 长度增 ⇒ 状态数增 ⇒ 熵增

---

*在这个框架中，ψ = ψ(ψ) 不仅是符号表达，更是系统自我认知的数学本质。*