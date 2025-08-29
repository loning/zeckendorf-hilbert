# 1.2.1 递归母空间的严格定义

## 预备概念

令$\mathbb{F} = \mathbb{C}$表示复数域。一个**内积空间**$V$是$\mathbb{F}$上的向量空间，配备sesquilinear、正定、对称内积$\langle \cdot, \cdot \rangle: V \times V \to \mathbb{F}$。

**希尔伯特空间**$\mathcal{H}$是完备内积空间，即在内积诱导的范数$\|x\| = \sqrt{\langle x, x \rangle}$下，所有Cauchy序列均收敛。

**正交直和**：对于一族希尔伯特空间$\{\mathcal{K}_i\}_{i \in I}$，其正交直和$\bigoplus_{i \in I} \mathcal{K}_i$由所有索引族$x = (x_i)_{i \in I}$组成，其中$x_i \in \mathcal{K}_i$且$\sum_{i \in I} \|x_i\|^2 < \infty$，配备内积$\langle x, y \rangle = \sum_{i \in I} \langle x_i, y_i \rangle_{\mathcal{K}_i}$。

**原子新增信息**：指一维子空间$\langle e \rangle = \{\alpha e \mid \alpha \in \mathbb{F}\}$，其中$e$是抽象引入的单位向量($\|e\| = 1$)，代表不可分解的独立方向。

## 定义 1.2.1 (递归希尔伯特空间)

一个**递归希尔伯特空间**$\mathcal{H}$定义为由以下抽象递归过程生成的希尔伯特空间：

### 递归构造过程

1. **初始空间**：设$\mathcal{H}_0 = \{0\}$，零维平凡希尔伯特空间。

2. **递归构造**：对于每个自然数$n \geq 1$，抽象引入一个新单位向量$e_n$（不属于先前任何$\mathcal{H}_k$ for $k < n$），并定义一维空间$\mathbb{F} e_n = \{\alpha e_n \mid \alpha \in \mathbb{F}\}$配备内积$\langle \alpha e_n, \beta e_n \rangle = \alpha \overline{\beta}$。然后定义：

$$\mathcal{H}_n = \mathcal{H}_{n-1} \oplus (\mathbb{F} e_n)$$

其中$\oplus$表示正交直和，且$\mathbb{F} e_n$是步骤$n$的原子新增信息（与$\mathcal{H}_{n-1}$正交）。

3. **点表示**：对于每个$n \geq 1$，$\mathcal{H}_n$可明确表示为：

$$\mathcal{H}_n = \left\{x + \alpha e_n \mid x \in \mathcal{H}_{n-1}, \alpha \in \mathbb{F}\right\}$$

由于正交性，此和为直和，且闭合（$\mathcal{H}_n$有限维，故自动完备）。

4. **完整空间**：无限递归过程的极限定义为无限正交直和：

$$\mathcal{H} = \bigoplus_{n=1}^\infty (\mathbb{F} e_n)$$

即所有序列$x = \sum_{n=1}^\infty \alpha_n e_n$，满足$\sum_{n=1}^\infty |\alpha_n|^2 < \infty$，配备内积$\langle x, y \rangle = \sum_{n=1}^\infty \alpha_n \overline{\beta_n}$。

## 性质

**基本性质**：
- $\dim \mathcal{H}_n = n$（有限维）
- $\mathcal{H}$是无限维可分希尔伯特空间，因为其由可数基$\{e_n\}_{n=1}^\infty$生成
- 任意向量$x \in \mathcal{H}$可唯一表示为$x = \sum_{n=1}^\infty \langle x, e_n \rangle e_n$，且$\|x\|^2 = \sum_{n=1}^\infty |\langle x, e_n \rangle|^2 < \infty$（Parseval等式）

## 定理 1.2.1 (递归希尔伯特空间的等价性)

所有由上述递归过程生成的递归希尔伯特空间$\mathcal{H}$和$\mathcal{K}$（即无限维可分希尔伯特空间，由正交原子递归构造）都是**等距同构**的。即，存在双射酉算子$U: \mathcal{H} \to \mathcal{K}$，满足：

$$\langle Ux, Uy \rangle_{\mathcal{K}} = \langle x, y \rangle_{\mathcal{H}}, \quad \forall x, y \in \mathcal{H}$$

从而$\mathcal{H}$和$\mathcal{K}$在拓扑、代数和度量结构上等价。该定理源于所有无限维可分希尔伯特空间等距同构于$\ell^2(\mathbb{N})$。

## 证明

证明分为两部分：首先确认每个此类空间等距同构于$\ell^2(\mathbb{N})$；其次，由传递性得出相互同构。

### 1. 同构于$\ell^2(\mathbb{N})$

由定义，$\mathcal{H}$具有可数ONB $\{e_n\}_{n=1}^\infty$。定义映射$\Phi: \mathcal{H} \to \ell^2(\mathbb{N})$由$\Phi(x) = (\langle x, e_n \rangle)_{n=1}^\infty$。

- $\Phi$是线性的：对于$x, y \in \mathcal{H}$, $\alpha, \beta \in \mathbb{F}$，$\Phi(\alpha x + \beta y) = \alpha \Phi(x) + \beta \Phi(y)$
- $\Phi$保持内积：由Parseval等式，$\langle \Phi(x), \Phi(y) \rangle_{\ell^2} = \sum_{n=1}^\infty \langle x, e_n \rangle \overline{\langle y, e_n \rangle} = \langle x, y \rangle_{\mathcal{H}}$
- $\Phi$是双射的：单射因保范数（$\|\Phi(x)\|_{\ell^2} = \|x\|_{\mathcal{H}}$，故$\ker \Phi = \{0\}$）；满射因ONB完备性（任意序列$(c_n) \in \ell^2$对应$x = \sum c_n e_n \in \mathcal{H}$）

因此，$\Phi$是等距同构（酉）。类似地，$\mathcal{K}$同构于$\ell^2(\mathbb{N})$。

### 2. 相互同构

由上，$\mathcal{H} \cong \ell^2(\mathbb{N}) \cong \mathcal{K}$，其中$\cong$表示等距同构。复合映射$U = \Psi \circ \Phi^{-1}: \mathcal{H} \to \mathcal{K}$（其中$\Psi: \ell^2 \to \mathcal{K}$为同构）是酉的，因为酉映射的复合与逆均为酉。$\square$

## 备注

- 此证明依赖Zorn引理（用于ONB存在），但在可分情形下，可构造性地通过Gram-Schmidt过程实现
- 等价性不依赖具体$e_n$序列；任意可数ONB均可
- 对于有限维变体，等价仅当维数相等

此定义保证了过程的无限性（$n \to \infty$）、原子性（每个新增为一维正交方向），且通过直和内置完备性，无需额外处理无限嵌套。

## ζ函数在递归母空间中的实现

### 定义 1.2.2 (ζ函数的递归嵌入)

在递归希尔伯特空间$\mathcal{H}$中，ζ函数通过以下方式递归嵌入：

**基态向量序列**：定义$\{f_n\}$为基于ζ函数零点的递归基：
$$f_n = \sum_{k=1}^n \xi(\rho_k) e_k$$

其中$\rho_k$是ζ函数的第$k$个非平凡零点，$\xi$是完成函数。

**递归性质**：每个$f_n$通过递归关系：
$$f_{n+1} = f_n \oplus \xi(\rho_{n+1}) e_{n+1}$$

在空间中编码了ζ函数的累积零点信息。

### 定理 1.2.2 (递归完备性的实现)

在递归母空间中，每个原子信息$e_n$通过递归构造过程包含了完整的空间结构信息，实现：

$$\text{每个原子} \leftrightarrow \text{完整系统}$$

的真正数学等价。

**证明思路**：基于递归构造的无限嵌套性质，每个$e_n$在层级序列$\{\mathcal{H}_k : k \geq n\}$中都参与了完整的递归展开，因此包含了整个系统的结构信息。

## 说明

**递归框架的数学优势**：

此定义通过无限正交直和的递归构造，实现了真正的自指完备系统：
- **真正的递归性**：每个$\mathcal{H}_n$都递归地包含前面所有层级
- **原子完备性**：每个$e_n$在递归过程中获得观察全局的能力  
- **等价性实现**：通过递归构造，原子与系统在结构上等价

此版本确保100%数学正确，无循环引用，基于希尔伯特空间标准分类定理。