# 第2章 公理与基础定义

## 2.1 自指完备 (Self-Reference Completeness)

### 定义 D2.1（自指完备系统）
一个形式系统 $S$ 称为**自指完备** (self-reference complete)，当且仅当存在编码函数 $\mathsf{code}: S \to S$ 和求值函数 $\mathsf{eval}: S \times S \to S$，满足：

1. **自指可达性**：存在 $\mathsf{self} \in S$ 使得
   $$\mathsf{eval}(\mathsf{self}, \mathsf{code}(\mathsf{self})) \text{ 收敛且} \in S$$

2. **操作内生性**：对系统中每个可计算操作 $f: S^k \to S$，存在程序 $p_f \in S$ 使得
   $$\forall (x_1, \ldots, x_k) \in S^k, \quad \mathsf{eval}(p_f, (x_1, \ldots, x_k)) = f(x_1, \ldots, x_k)$$

3. **执行封闭性**：
   $$\forall p, x \in S, \quad \mathsf{eval}(p,x) \text{ 收敛} \Rightarrow \mathsf{eval}(p,x) \in S$$

**理论补充**：定义D2.1的抽象性得到[自动机系统理论](math/02-automata-system.md)的具体支撑。该理论提供了3状态自动机 $\mathcal{A}_\varphi = (Q, \Sigma, \delta, q_0, F)$ 作为自指完备系统的可操作实现，其中状态转移精确对应自指执行的语义，使得抽象定义获得了计算模型的严格基础。

---

### 定义 D2.2（执行轨迹与记录生成）
设 $\sigma_t$ 为系统在时刻 $t$ 的全局状态。一次**自指执行** $\mathsf{SelfExec}(\sigma_t)$ 定义为：

$$\mathsf{SelfExec}(\sigma_t) = \sigma_{t+1} = \sigma_t \oplus \mathsf{trace}(\sigma_t)$$

其中：
- $\mathsf{trace}(\sigma_t) \in S$ 是执行轨迹记录，满足 $\mathsf{trace}(\sigma_t) \neq \emptyset$
- $\oplus$ 是状态扩展操作，保证 $|\sigma_{t+1}| > |\sigma_t|$（严格长度增加）
- 执行轨迹 $\mathsf{trace}(\sigma_t)$ 在 $\sigma_t$ 中唯一确定

**记录不变量**：每次自指执行必产生新的、不与历史重复的轨迹信息。

---

## 2.2 熵 (Entropy)

### 定义 D2.3（状态空间与信息熵）
设 $S$ 为自指完备系统，$\Sigma_0$ 为初始状态空间。定义第 $t$ 步后的**可达状态空间**：

$$\Sigma_t = \{\sigma : \exists \text{执行序列} (\sigma_0, \sigma_1, \ldots, \sigma_t), \sigma_0 \in \Sigma_0, \sigma_i = \mathsf{SelfExec}(\sigma_{i-1}), \sigma = \sigma_t\}$$

系统在时刻 $t$ 的**信息熵**定义为：

$$H_t := H(\Sigma_t) = \log_2 |\Sigma_t|$$

**熵的可计算性条件**：
1. $\Sigma_t$ 可枚举且 $|\Sigma_t| < \infty$（有限性）
2. $\Sigma_0 \subsetneq \Sigma_1 \subsetneq \Sigma_2 \subsetneq \cdots$（严格单调性）
3. $\forall t \geq 0: |\Sigma_{t+1}| \geq |\Sigma_t| + 1$（最小增长保证）

**物理解释**：$H_t$ 量化了在时刻 $t$ 区分系统所有可能状态所需的最小比特数。

---

## 2.3 公理陈述

### 公理 A1（自指完备熵增公理, SRA）
**陈述**：对任意自指完备系统 $S$ 及其状态空间演化序列 $\{\Sigma_t\}_{t \geq 0}$：

$$\boxed{\forall t \geq 0: H_{t+1} > H_t}$$

**等价形式**：
$$\forall t \geq 0: |\Sigma_{t+1}| > |\Sigma_t| \wedge \log_2|\Sigma_{t+1}| > \log_2|\Sigma_t|$$

**理论补充**：A1公理的非假设性得到[自指循环完备性理论](math/12-circular-completeness.md)的严格证明。该理论通过自指算子的不动点分析，证明了当系统满足ψ = ψ(ψ)的循环完备条件时，熵增不是外加的假设，而是自指结构在数学上的必然结果，为公理提供了逻辑必然性的坚实基础。

**公理的逻辑结构**：

1. **执行必然性**：$\mathsf{SelfExec}(\sigma_t)$ 总是产生 $\mathsf{trace}(\sigma_t) \neq \emptyset$
2. **轨迹唯一性**：$\mathsf{trace}(\sigma_t) \notin \{\mathsf{trace}(\sigma_s) : s < t\}$
3. **状态扩展性**：$\sigma_{t+1} = \sigma_t \oplus \mathsf{trace}(\sigma_t) \Rightarrow |\sigma_{t+1}| > |\sigma_t|$
4. **可达性传递**：新状态 $\sigma_{t+1} \in \Sigma_{t+1} \setminus \Sigma_t$
5. **熵增必然**：$|\Sigma_{t+1}| \geq |\Sigma_t| + 1 \Rightarrow H_{t+1} > H_t$

**不变量**：系统的自指完备性在执行过程中保持不变。

---

## 2.4 命题：自指与熵增的基本关系

### 引理 L2.1（状态长度严格增长）
若系统 $S$ 自指完备，则其任意自指执行都导致状态长度严格增长：
$$\forall t \geq 0: |\mathsf{SelfExec}(\sigma_t)| > |\sigma_t|$$

**严格证明**：
1. 设 $\sigma_{t+1} = \mathsf{SelfExec}(\sigma_t) = \sigma_t \oplus \mathsf{trace}(\sigma_t)$
2. 由定义D2.2，$\mathsf{trace}(\sigma_t) \neq \emptyset$，故 $|\mathsf{trace}(\sigma_t)| \geq 1$
3. 由状态扩展操作 $\oplus$ 的定义，$|\sigma_t \oplus \mathsf{trace}(\sigma_t)| = |\sigma_t| + |\mathsf{trace}(\sigma_t)|$
4. 因此：$|\sigma_{t+1}| = |\sigma_t| + |\mathsf{trace}(\sigma_t)| \geq |\sigma_t| + 1 > |\sigma_t|$ ∎

---

### 引理 L2.2（状态空间扩展的熵增性）
对自指完备系统，状态空间的严格扩展必然导致信息熵的严格增长：

$$|\Sigma_{t+1}| > |\Sigma_t| \Rightarrow H_{t+1} > H_t$$

**构造性证明**：
1. **执行起点**：取任意 $\sigma_t \in \Sigma_t$
2. **轨迹生成**：$\mathsf{trace}_t := \mathsf{trace}(\sigma_t)$ 由执行过程唯一确定
3. **新状态构造**：$\sigma_{t+1}' := \sigma_t \oplus \mathsf{trace}_t$
4. **封闭性验证**：由D2.1(执行封闭性)，$\sigma_{t+1}' \in S$
5. **新颖性证明**：假设 $\sigma_{t+1}' \in \Sigma_t$，则存在 $s < t$ 使得某状态经 $s$ 步达到 $\sigma_{t+1}'$。但 $|\sigma_{t+1}'| > |\sigma_t| \geq \max\{|\sigma| : \sigma \in \Sigma_t\}$，矛盾。
6. **状态扩展**：$\sigma_{t+1}' \in \Sigma_{t+1} \setminus \Sigma_t$
7. **基数增长**：$|\Sigma_{t+1}| \geq |\Sigma_t \cup \{\sigma_{t+1}'\}| = |\Sigma_t| + 1$
8. **熵严格增长**：$H_{t+1} = \log_2|\Sigma_{t+1}| > \log_2|\Sigma_t| = H_t$ ∎

**关键洞察**：轨迹的唯一性保证了状态空间的真正扩展，而非重复。

---

## 2.5 公理体系总结

本章构建的严格数学框架包含：

### 核心定义体系
1. **自指完备系统 (D2.1)**：具备自指可达性、操作内生性、执行封闭性的形式系统
2. **执行轨迹与记录生成 (D2.2)**：自指执行的状态扩展操作及其不可逆轨迹记录
3. **状态空间与信息熵 (D2.3)**：可达状态的演化集合及其信息度量

### 基本公理
4. **自指完备熵增公理 (SRA)**：$\forall t \geq 0: H_{t+1} > H_t$ - 任意自指完备系统的熵严格单调递增

### 推导体系
5. **状态长度严格增长 (L2.1)**：自指执行 ⇒ 轨迹记录 ⇒ 状态长度增加
6. **状态空间扩展的熵增性 (L2.2)**：新状态生成 ⇒ 状态空间扩展 ⇒ 信息熵增长

### 逻辑链条
**自指完备性** → **执行轨迹唯一性** → **状态长度增长** → **状态空间扩展** → **熵严格增长**

---

*在这个框架中，ψ = ψ(ψ) 不仅是符号表达，更是系统自我认知的数学本质。*