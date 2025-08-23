# φ-Cauchy序列的严格理论

## 定义 19.1（φ-序列的极限概念）
对φ-有理数序列 $(r_n)_{n \in \mathbb{F}\mathbb{N}}$ 和 $L \in \mathbb{F}\mathbb{Q}$，定义**φ-序列极限**：

$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n = L$$

当且仅当对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $N \in \mathbb{F}\mathbb{N}$ 使得对所有 $n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{Q}}(r_n, L) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

## 定义 19.2（φ-Cauchy序列的精确定义）
φ-有理数序列 $(r_n)_{n \in \mathbb{F}\mathbb{N}}$ 称为**φ-Cauchy序列**，当且仅当：

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $N \in \mathbb{F}\mathbb{N}$ 使得对所有 $m, n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{Q}}(r_m, r_n) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

记所有φ-Cauchy序列的集合为 $\text{Cauchy}(\mathbb{F}\mathbb{Q})$。

## 引理 19.1（φ-Cauchy序列的基本性质）
φ-Cauchy序列满足以下基本性质：

1. **有界性**：每个φ-Cauchy序列都有界
2. **收敛序列为Cauchy**：若 $\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n = L$，则 $(r_n)$ 为φ-Cauchy序列
3. **子序列性质**：φ-Cauchy序列的任意子序列仍为φ-Cauchy序列

**证明：**
**有界性**：取 $\varepsilon = \mathbf{1}_{\mathbb{F}\mathbb{Q}}$，存在 $N$ 使得 $d_{\mathbb{F}\mathbb{Q}}(r_m, r_n) \prec_{\mathbb{F}\mathbb{Q}} \mathbf{1}_{\mathbb{F}\mathbb{Q}}$ 对所有 $m, n \succ_{\mathbb{F}\mathbb{N}} N$。
则对所有 $n$：$d_{\mathbb{F}\mathbb{Q}}(r_n, r_{N+1}) \preceq_{\mathbb{F}\mathbb{Q}} \mathbf{1}_{\mathbb{F}\mathbb{Q}}$，故序列有界。

**收敛推出Cauchy**：若 $\lim r_n = L$，对任意 $\varepsilon$，取 $\delta = \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$。
存在 $N$ 使得对 $m, n \succ_{\mathbb{F}\mathbb{N}} N$：$d_{\mathbb{F}\mathbb{Q}}(r_m, L) \prec_{\mathbb{F}\mathbb{Q}} \delta$ 且 $d_{\mathbb{F}\mathbb{Q}}(r_n, L) \prec_{\mathbb{F}\mathbb{Q}} \delta$。
由三角不等式：$d_{\mathbb{F}\mathbb{Q}}(r_m, r_n) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$。

**子序列性质**：Cauchy条件的任意子列仍满足该条件。 ∎

## 定义 19.3（φ-Cauchy序列等价关系）
在 $\text{Cauchy}(\mathbb{F}\mathbb{Q})$ 上定义等价关系 $\sim_C$：

$(r_n) \sim_C (s_n)$ 当且仅当 $\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} d_{\mathbb{F}\mathbb{Q}}(r_n, s_n) = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$

即对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，存在 $N \in \mathbb{F}\mathbb{N}$ 使得对所有 $n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{Q}}(r_n, s_n) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

## 定理 19.1（φ-Cauchy等价关系的良定义性）
关系 $\sim_C$ 是 $\text{Cauchy}(\mathbb{F}\mathbb{Q})$ 上的等价关系。

**证明：**
**反身性**：对任意φ-Cauchy序列 $(r_n)$，$d_{\mathbb{F}\mathbb{Q}}(r_n, r_n) = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，故 $(r_n) \sim_C (r_n)$。

**对称性**：若 $(r_n) \sim_C (s_n)$，则由距离函数的对称性（定理17.9），$(s_n) \sim_C (r_n)$。

**传递性**：若 $(r_n) \sim_C (s_n)$ 且 $(s_n) \sim_C (t_n)$，需证明 $(r_n) \sim_C (t_n)$。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，取 $\delta = \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$。

由假设，存在 $N_1, N_2$ 使得：
- 对 $n \succ_{\mathbb{F}\mathbb{N}} N_1$：$d_{\mathbb{F}\mathbb{Q}}(r_n, s_n) \prec_{\mathbb{F}\mathbb{Q}} \delta$
- 对 $n \succ_{\mathbb{F}\mathbb{N}} N_2$：$d_{\mathbb{F}\mathbb{Q}}(s_n, t_n) \prec_{\mathbb{F}\mathbb{Q}} \delta$

取 $N = \max_{\mathbb{F}\mathbb{N}}(N_1, N_2)$，对 $n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{Q}}(r_n, t_n) \preceq_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(r_n, s_n) \oplus_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(s_n, t_n) \prec_{\mathbb{F}\mathbb{Q}} \delta \oplus_{\mathbb{F}\mathbb{Q}} \delta = \varepsilon$$

故 $(r_n) \sim_C (t_n)$。 ∎

## 定义 19.4（φ-Cauchy序列运算）
对φ-Cauchy序列 $(r_n), (s_n) \in \text{Cauchy}(\mathbb{F}\mathbb{Q})$，定义逐项运算：

**φ-Cauchy序列加法**：
$$(r_n) \oplus_C (s_n) = (r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n)$$

**φ-Cauchy序列乘法**：
$$(r_n) \otimes_C (s_n) = (r_n \otimes_{\mathbb{F}\mathbb{Q}} s_n)$$

**φ-Cauchy序列数乘**：
$$\lambda \odot_C (r_n) = (\lambda \otimes_{\mathbb{F}\mathbb{Q}} r_n) \quad \text{对 } \lambda \in \mathbb{F}\mathbb{Q}$$

## 定理 19.2（φ-Cauchy序列运算的封闭性）
φ-Cauchy序列在运算下封闭。

**证明：**
**加法封闭性**：设 $(r_n), (s_n)$ 为φ-Cauchy序列。对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，取 $\delta = \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$。

由Cauchy条件，存在 $N_1, N_2$ 使得：
- 对 $m, n \succ_{\mathbb{F}\mathbb{N}} N_1$：$d_{\mathbb{F}\mathbb{Q}}(r_m, r_n) \prec_{\mathbb{F}\mathbb{Q}} \delta$
- 对 $m, n \succ_{\mathbb{F}\mathbb{N}} N_2$：$d_{\mathbb{F}\mathbb{Q}}(s_m, s_n) \prec_{\mathbb{F}\mathbb{Q}} \delta$

取 $N = \max_{\mathbb{F}\mathbb{N}}(N_1, N_2)$，对 $m, n \succ_{\mathbb{F}\mathbb{N}} N$：

由φ-有理数加法的连续性（定理17.10）：
$$d_{\mathbb{F}\mathbb{Q}}(r_m \oplus_{\mathbb{F}\mathbb{Q}} s_m, r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

故 $(r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n)$ 为φ-Cauchy序列。

**乘法封闭性**：类似证明，使用φ-有理数乘法的连续性和Cauchy序列的有界性。 ∎

## 定理 19.3（φ-Cauchy序列运算与等价关系的相容性）
φ-Cauchy序列运算与等价关系 $\sim_C$ 相容。

**证明：**
**加法相容性**：设 $(r_n) \sim_C (r_n')$ 且 $(s_n) \sim_C (s_n')$。
需证明 $(r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n) \sim_C (r_n' \oplus_{\mathbb{F}\mathbb{Q}} s_n')$。

由假设：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} d_{\mathbb{F}\mathbb{Q}}(r_n, r_n') = \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \quad \lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} d_{\mathbb{F}\mathbb{Q}}(s_n, s_n') = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$$

由φ-有理数加法的连续性：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} d_{\mathbb{F}\mathbb{Q}}(r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n, r_n' \oplus_{\mathbb{F}\mathbb{Q}} s_n') = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$$

**乘法相容性**：类似证明，使用φ-有理数乘法的连续性。 ∎

## 定义 19.5（φ-零Cauchy序列）
称φ-Cauchy序列 $(r_n)$ 为**φ-零序列**，记作 $(r_n) \in \mathcal{N}_{\mathbb{F}\mathbb{Q}}$，当且仅当：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$$

即 $(r_n) \sim_C (\mathbf{0}_{\mathbb{F}\mathbb{Q}}, \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \ldots)$。

## 定理 19.4（φ-零序列理想结构）
φ-零序列集合 $\mathcal{N}_{\mathbb{F}\mathbb{Q}}$ 构成 $\text{Cauchy}(\mathbb{F}\mathbb{Q})$ 的理想。

**证明：**
**加法封闭性**：若 $(r_n), (s_n) \in \mathcal{N}_{\mathbb{F}\mathbb{Q}}$，则：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} (r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n) = \lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n \oplus_{\mathbb{F}\mathbb{Q}} \lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} s_n = \mathbf{0}_{\mathbb{F}\mathbb{Q}} \oplus_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}} = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$$

故 $(r_n \oplus_{\mathbb{F}\mathbb{Q}} s_n) \in \mathcal{N}_{\mathbb{F}\mathbb{Q}}$。

**理想性质**：对 $(r_n) \in \mathcal{N}_{\mathbb{F}\mathbb{Q}}$ 和任意φ-Cauchy序列 $(s_n)$：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} (r_n \otimes_{\mathbb{F}\mathbb{Q}} s_n) = \left(\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n\right) \otimes_{\mathbb{F}\mathbb{Q}} \left(\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} s_n\right) = \mathbf{0}_{\mathbb{F}\mathbb{Q}} \otimes_{\mathbb{F}\mathbb{Q}} s = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$$

其中 $s = \lim s_n$（当极限存在时）或通过Cauchy序列的有界性保证乘积趋向零。 ∎

## 定义 19.6（φ-Cauchy序列环结构）
$\text{Cauchy}(\mathbb{F}\mathbb{Q})$ 在逐项运算下构成交换环：

- **加法单位元**：$\mathbf{0}_C = (\mathbf{0}_{\mathbb{F}\mathbb{Q}}, \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \mathbf{0}_{\mathbb{F}\mathbb{Q}}, \ldots)$
- **乘法单位元**：$\mathbf{1}_C = (\mathbf{1}_{\mathbb{F}\mathbb{Q}}, \mathbf{1}_{\mathbb{F}\mathbb{Q}}, \mathbf{1}_{\mathbb{F}\mathbb{Q}}, \ldots)$

## 定理 19.5（φ-Cauchy序列环性质）
$(\text{Cauchy}(\mathbb{F}\mathbb{Q}), \oplus_C, \otimes_C, \mathbf{0}_C, \mathbf{1}_C)$ 构成交换环。

**证明：**
所有环公理都由φ-有理数域的对应性质逐项继承：

**结合律**：$(a \oplus_C b) \oplus_C c = a \oplus_C (b \oplus_C c)$ 因为φ-有理数加法满足结合律。

**交换律**：$a \oplus_C b = b \oplus_C a$ 因为φ-有理数加法满足交换律。

**分配律**：$a \otimes_C (b \oplus_C c) = (a \otimes_C b) \oplus_C (a \otimes_C c)$ 因为φ-有理数满足分配律。

**单位元性质**：由常数序列的性质直接验证。 ∎

## 定理 19.6（φ-Cauchy序列的乘法逆元）
对非零φ-Cauchy序列 $(r_n) \notin \mathcal{N}_{\mathbb{F}\mathbb{Q}}$，存在φ-Cauchy序列 $(s_n)$ 使得 $(r_n) \otimes_C (s_n) \sim_C \mathbf{1}_C$。

**证明：**
由于 $(r_n) \notin \mathcal{N}_{\mathbb{F}\mathbb{Q}}$，存在 $\delta \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$ 和 $N \in \mathbb{F}\mathbb{N}$ 使得：
$$|r_n|_{\mathbb{F}\mathbb{Q}} \succ_{\mathbb{F}\mathbb{Q}} \delta \quad \text{对所有 } n \succ_{\mathbb{F}\mathbb{N}} N$$

定义序列：
$$s_n = \begin{cases}
\frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{r_n} & \text{若 } n \succ_{\mathbb{F}\mathbb{N}} N \\
\frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{r_{N+1}} & \text{若 } n \preceq_{\mathbb{F}\mathbb{N}} N
\end{cases}$$

**步骤1**：证明 $(s_n)$ 为φ-Cauchy序列。
对 $m, n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{Q}}(s_m, s_n) = d_{\mathbb{F}\mathbb{Q}}\left(\frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{r_m}, \frac{\mathbf{1}_{\mathbb{F}\mathbb{Q}}}{r_n}\right) = \frac{d_{\mathbb{F}\mathbb{Q}}(r_m, r_n)}{|r_m \otimes_{\mathbb{F}\mathbb{Q}} r_n|_{\mathbb{F}\mathbb{Q}}}$$

由于 $|r_m|_{\mathbb{F}\mathbb{Q}}, |r_n|_{\mathbb{F}\mathbb{Q}} \succ_{\mathbb{F}\mathbb{Q}} \delta$ 且 $(r_n)$ 为Cauchy序列，$(s_n)$ 也为Cauchy序列。

**步骤2**：验证 $(r_n \otimes_{\mathbb{F}\mathbb{Q}} s_n) \to \mathbf{1}_{\mathbb{F}\mathbb{Q}}$。
对 $n \succ_{\mathbb{F}\mathbb{N}} N$：$r_n \otimes_{\mathbb{F}\mathbb{Q}} s_n = \mathbf{1}_{\mathbb{F}\mathbb{Q}}$。 ∎

## 推论 19.1（φ-实数域的商环实现）
φ-实数域可实现为：
$$\mathbb{F}\mathbb{R} = \text{Cauchy}(\mathbb{F}\mathbb{Q}) / \mathcal{N}_{\mathbb{F}\mathbb{Q}}$$

其中商环运算良定义且构成域。

**证明：**
由定理19.4，$\mathcal{N}_{\mathbb{F}\mathbb{Q}}$ 为理想。
由定理19.6，商环中每个非零元素都有乘法逆元，故商环为域。 ∎

## 定理 19.7（φ-Cauchy序列的极限唯一性）
若φ-Cauchy序列在φ-有理数中收敛，则其极限唯一。

**证明：**
设 $(r_n)$ 为φ-Cauchy序列且 $\lim r_n = L_1, \lim r_n = L_2$。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，取 $\delta = \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$。

存在 $N_1, N_2$ 使得：
- 对 $n \succ_{\mathbb{F}\mathbb{N}} N_1$：$d_{\mathbb{F}\mathbb{Q}}(r_n, L_1) \prec_{\mathbb{F}\mathbb{Q}} \delta$
- 对 $n \succ_{\mathbb{F}\mathbb{N}} N_2$：$d_{\mathbb{F}\mathbb{Q}}(r_n, L_2) \prec_{\mathbb{F}\mathbb{Q}} \delta$

取 $N = \max_{\mathbb{F}\mathbb{N}}(N_1, N_2)$，对任意 $n \succ_{\mathbb{F}\mathbb{N}} N$：
$$d_{\mathbb{F}\mathbb{Q}}(L_1, L_2) \preceq_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(L_1, r_n) \oplus_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(r_n, L_2) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

由 $\varepsilon$ 的任意性，$d_{\mathbb{F}\mathbb{Q}}(L_1, L_2) = \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，故 $L_1 = L_2$。 ∎

## 定理 19.8（φ-有理数中收敛的φ-Cauchy序列刻画）
φ-Cauchy序列 $(r_n)$ 在φ-有理数中收敛当且仅当其像序列 $(\eta(r_n))$ 在标准有理数中收敛。

其中 $\eta: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 为域同构（定理15.7）。

**证明：**
**必要性**：若 $\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n = L \in \mathbb{F}\mathbb{Q}$，则：
$$\lim_{n \to \infty} \eta(r_n) = \eta(L) \in \mathbb{Q}$$

由同构的保持性和定理19.7的极限唯一性。

**充分性**：若 $\lim_{n \to \infty} \eta(r_n) = \ell \in \mathbb{Q}$，则 $L = \eta^{-1}(\ell) \in \mathbb{F}\mathbb{Q}$ 且：
$$\lim_{n \to \infty_{\mathbb{F}\mathbb{N}}} r_n = L$$

由同构的连续性和逆映射的保持性。 ∎

## 引理 19.2（φ-Cauchy序列的子序列性质）
φ-Cauchy序列的收敛子序列的极限唯一确定整个序列的等价类。

**证明：**
设 $(r_n)$ 为φ-Cauchy序列，$(r_{n_k})$ 为收敛子序列且 $\lim_{k \to \infty_{\mathbb{F}\mathbb{N}}} r_{n_k} = L$。

对任意 $\varepsilon \succ_{\mathbb{F}\mathbb{Q}} \mathbf{0}_{\mathbb{F}\mathbb{Q}}$，由Cauchy条件存在 $N_1$，由子序列收敛性存在 $K$：
- 对 $m, n \succ_{\mathbb{F}\mathbb{N}} N_1$：$d_{\mathbb{F}\mathbb{Q}}(r_m, r_n) \prec_{\mathbb{F}\mathbb{Q}} \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$
- 对 $k \succ_{\mathbb{F}\mathbb{N}} K$：$d_{\mathbb{F}\mathbb{Q}}(r_{n_k}, L) \prec_{\mathbb{F}\mathbb{Q}} \frac{\varepsilon}{\mathbf{2}_{\mathbb{F}\mathbb{Q}}}$

选择 $k$ 足够大使得 $n_k \succ_{\mathbb{F}\mathbb{N}} N_1$，则对所有 $n \succ_{\mathbb{F}\mathbb{N}} N_1$：
$$d_{\mathbb{F}\mathbb{Q}}(r_n, L) \preceq_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(r_n, r_{n_k}) \oplus_{\mathbb{F}\mathbb{Q}} d_{\mathbb{F}\mathbb{Q}}(r_{n_k}, L) \prec_{\mathbb{F}\mathbb{Q}} \varepsilon$$

因此 $(r_n) \sim_C (L, L, L, \ldots)$。 ∎

## 定理 19.9（φ-Cauchy序列完备化的万有性质）
φ-实数的构造 $\mathbb{F}\mathbb{R} = \text{Cauchy}(\mathbb{F}\mathbb{Q}) / \mathcal{N}_{\mathbb{F}\mathbb{Q}}$ 满足万有性质：

对任意完备度量空间 $(X, d_X)$ 和等距嵌入 $f: \mathbb{F}\mathbb{Q} \to X$，存在唯一的等距同构 $\tilde{f}: \mathbb{F}\mathbb{R} \to X$ 使得下图交换：

$$\begin{array}{ccc}
\mathbb{F}\mathbb{Q} & \xrightarrow{\iota} & \mathbb{F}\mathbb{R} \\
\downarrow f & & \downarrow \tilde{f} \\
X & = & X
\end{array}$$

**证明：**
**存在性**：对 $x = [(r_n)] \in \mathbb{F}\mathbb{R}$，定义：
$$\tilde{f}(x) = \lim_{n \to \infty} f(r_n) \in X$$

极限在 $X$ 中存在，因为 $(f(r_n))$ 为 $X$ 中的Cauchy序列且 $X$ 完备。

**良定义性**：不依赖于代表序列的选择，由等价关系的定义保证。

**唯一性**：由稠密性和连续性，$\tilde{f}$ 在φ-有理数上的值完全确定其在φ-实数上的值。 ∎

## 推论 19.2（φ-实数完备化的唯一性）
φ-实数的Cauchy序列完备化在等距同构意义下唯一。

**证明：**
任意两个φ-有理数的完备化都满足相同的万有性质（定理19.9），因此必然等距同构。 ∎

## 定理 19.10（φ-Cauchy序列与标准Cauchy序列的对应）
存在自然双射：
$$\text{Cauchy}(\mathbb{F}\mathbb{Q}) / \mathcal{N}_{\mathbb{F}\mathbb{Q}} \leftrightarrow \text{Cauchy}(\mathbb{Q}) / \mathcal{N}_{\mathbb{Q}}$$

通过域同构 $\eta: \mathbb{F}\mathbb{Q} \to \mathbb{Q}$ 诱导。

**证明：**
定义映射 $\Psi: \text{Cauchy}(\mathbb{F}\mathbb{Q}) \to \text{Cauchy}(\mathbb{Q})$：
$$\Psi((r_n)) = (\eta(r_n))$$

**良定义性**：若 $(r_n)$ 为φ-Cauchy序列，则 $(\eta(r_n))$ 为标准Cauchy序列，因为 $\eta$ 保持距离结构。

**等价类保持**：$(r_n) \sim_C (s_n)$ 当且仅当 $(\eta(r_n)) \sim (\eta(s_n))$，因为 $\eta$ 保持极限运算。

**双射性**：由 $\eta$ 的双射性和构造的自然性直接得出。 ∎

## 推论 19.3（φ-Cauchy序列理论的完备性）
φ-Cauchy序列理论实现了φ-有理数的度量完备化：

1. **序列空间结构**：$\text{Cauchy}(\mathbb{F}\mathbb{Q})$ 构成自然的环
2. **等价关系**：零序列理想提供了正确的等价概念
3. **完备化实现**：商环构造给出完备的φ-实数域
4. **万有性质**：满足度量空间完备化的万有性质
5. **同构对应**：与标准实数完备化完全对应

这为φ-实数分析理论提供了坚实的序列理论基础。

**证明：**
所有性质由定理19.1-19.10综合得出，特别是万有性质（定理19.9）和同构对应（定理19.10）保证了理论的完备性。 ∎