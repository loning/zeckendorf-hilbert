# φ-整数代数性质理论

## 定理 14.1（φ-整数环的完整刻画）
φ-整数环 $(\mathbb{F}\mathbb{Z}, \oplus_{\mathbb{F}\mathbb{Z}}, \otimes_{\mathbb{F}\mathbb{Z}}, \mathbf{0}_{\mathbb{F}\mathbb{Z}}, \mathbf{1}_{\mathbb{F}\mathbb{Z}})$ 是主理想整环。

**证明：**
需证明 $\mathbb{F}\mathbb{Z}$ 是整环且每个理想都是主理想。

**整环性**：由定理11.8，$\mathbb{F}\mathbb{Z}$ 无零因子，且由定理11.7是交换环，故为整环。

**主理想性**：由同构 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$，任意理想 $I \triangleleft \mathbb{F}\mathbb{Z}$ 对应 $\xi(I) \triangleleft \mathbb{Z}$。
由于 $\mathbb{Z}$ 是主理想整环，存在 $d \in \mathbb{Z}$ 使得 $\xi(I) = (d)$。
因此 $I = (\xi^{-1}(d))$，即 $\mathbb{F}\mathbb{Z}$ 是主理想整环。 ∎

## 定理 14.2（φ-整数的素元分解）
每个非零非单位的φ-整数都有唯一的素元分解（差一个单位倍数）。

**证明：**
由定理14.1，$\mathbb{F}\mathbb{Z}$ 是主理想整环，因此是唯一因数分解整环。

设 $z \in \mathbb{F}\mathbb{Z}$ 非零非单位，则 $\xi(z) \in \mathbb{Z}$ 非零非单位。
由标准整数的唯一素因数分解：
$$\xi(z) = \pm \prod_{i=1}^k p_i^{e_i}$$

其中 $p_i$ 为不同的正素数，$e_i > 0$。

在φ-整数中对应为：
$$z = \xi^{-1}(\pm 1) \prod_{i=1}^k (\xi^{-1}(p_i))^{e_i}$$

其中 $\xi^{-1}(p_i)$ 为φ-素元，$\xi^{-1}(\pm 1)$ 为φ-单位。 ∎

## 定义 14.1（φ-素元与φ-单位）
- **φ-素元**：$p \in \mathbb{F}\mathbb{Z}$ 称为φ-素元，若 $\xi(p)$ 为素数
- **φ-单位**：$u \in \mathbb{F}\mathbb{Z}$ 称为φ-单位，若 $\xi(u) \in \{+1, -1\}$

## 引理 14.1（φ-单位群结构）
φ-整数的单位群为：
$$U(\mathbb{F}\mathbb{Z}) = \{\mathbf{1}_{\mathbb{F}\mathbb{Z}}, -\mathbf{1}_{\mathbb{F}\mathbb{Z}}\} \cong \mathbb{Z}_2$$

**证明：**
$z \in \mathbb{F}\mathbb{Z}$ 为单位当且仅当存在 $z' \in \mathbb{F}\mathbb{Z}$ 使得 $z \otimes_{\mathbb{F}\mathbb{Z}} z' = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$。

这等价于 $\xi(z) \cdot \xi(z') = 1$，即 $\xi(z) \in U(\mathbb{Z}) = \{+1, -1\}$。

因此 $U(\mathbb{F}\mathbb{Z}) = \{\xi^{-1}(1), \xi^{-1}(-1)\} = \{\mathbf{1}_{\mathbb{F}\mathbb{Z}}, -\mathbf{1}_{\mathbb{F}\mathbb{Z}}\}$。 ∎

## 定理 14.3（φ-整数的欧几里得算法性质）
$\mathbb{F}\mathbb{Z}$ 上的欧几里得算法具有与标准整数相同的收敛性质。

设 $z_1, z_2 \in \mathbb{F}\mathbb{Z}$ 且 $z_2 \neq \mathbf{0}_{\mathbb{F}\mathbb{Z}}$，欧几里得算法序列：
$$r_0 = z_1, r_1 = z_2, \ldots, r_{i+1} = \text{rem}_{\mathbb{F}\mathbb{Z}}(r_{i-1}, r_i)$$

在有限步内终止，且 $\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = r_{k-1}$（最后一个非零余数）。

**证明：**
由同构性质，φ-整数的欧几里得算法与标准整数的欧几里得算法一一对应：
$$r_i = \xi^{-1}(\text{rem}(\xi(z_1), \xi(z_2))_i)$$

因此收敛性和正确性由标准欧几里得算法保证。 ∎

## 定理 14.4（φ-整数的贝祖恒等式）
对任意 $z_1, z_2 \in \mathbb{F}\mathbb{Z}$，存在 $x, y \in \mathbb{F}\mathbb{Z}$ 使得：
$$\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = x \otimes_{\mathbb{F}\mathbb{Z}} z_1 \oplus_{\mathbb{F}\mathbb{Z}} y \otimes_{\mathbb{F}\mathbb{Z}} z_2$$

**证明：**
由标准整数的贝祖恒等式，存在 $a, b \in \mathbb{Z}$ 使得：
$$\gcd(\xi(z_1), \xi(z_2)) = a \cdot \xi(z_1) + b \cdot \xi(z_2)$$

在φ-整数中对应为：
$$\xi^{-1}(\gcd(\xi(z_1), \xi(z_2))) = \xi^{-1}(a) \otimes_{\mathbb{F}\mathbb{Z}} z_1 \oplus_{\mathbb{F}\mathbb{Z}} \xi^{-1}(b) \otimes_{\mathbb{F}\mathbb{Z}} z_2$$

即 $\gcd_{\mathbb{F}\mathbb{Z}}(z_1, z_2) = x \otimes_{\mathbb{F}\mathbb{Z}} z_1 \oplus_{\mathbb{F}\mathbb{Z}} y \otimes_{\mathbb{F}\mathbb{Z}} z_2$，
其中 $x = \xi^{-1}(a), y = \xi^{-1}(b)$。 ∎

## 定理 14.5（φ-整数的中国剩余定理）
设 $z_1, z_2, \ldots, z_k \in \mathbb{F}\mathbb{Z}$ 两两互素，即 $\gcd_{\mathbb{F}\mathbb{Z}}(z_i, z_j) = \mathbf{1}_{\mathbb{F}\mathbb{Z}}$ 对所有 $i \neq j$。

则对任意 $a_1, a_2, \ldots, a_k \in \mathbb{F}\mathbb{Z}$，同余方程组：
$$\begin{cases}
x \equiv a_1 \pmod{z_1} \\
x \equiv a_2 \pmod{z_2} \\
\vdots \\
x \equiv a_k \pmod{z_k}
\end{cases}$$

在模 $z_1 \otimes_{\mathbb{F}\mathbb{Z}} z_2 \otimes_{\mathbb{F}\mathbb{Z}} \cdots \otimes_{\mathbb{F}\mathbb{Z}} z_k$ 下有唯一解。

**证明：**
由同构 $\xi$，φ-整数的同余关系对应标准整数的同余关系。
标准中国剩余定理给出唯一解的存在性，φ-整数情形由同构性质直接得出。 ∎

## 定理 14.6（φ-整数的威尔逊定理）
对φ-素元 $p \in \mathbb{F}\mathbb{Z}$：
$$\prod_{i=1}^{\xi(p)-1} \xi^{-1}(i) \equiv -\mathbf{1}_{\mathbb{F}\mathbb{Z}} \pmod{p}$$

其中乘积在 $\mathbb{F}\mathbb{Z}$ 中进行。

**证明：**
设 $\xi(p) = q$ 为素数。由标准威尔逊定理：
$$(q-1)! \equiv -1 \pmod{q}$$

在φ-整数中对应为：
$$\xi^{-1}((q-1)!) \equiv \xi^{-1}(-1) \pmod{\xi^{-1}(q)}$$

即：
$$\prod_{i=1}^{q-1} \xi^{-1}(i) \equiv -\mathbf{1}_{\mathbb{F}\mathbb{Z}} \pmod{p}$$ 
∎

## 定理 14.7（φ-整数的费马小定理）
设 $p \in \mathbb{F}\mathbb{Z}$ 为φ-素元，$z \in \mathbb{F}\mathbb{Z}$ 且 $p \nmid z$，则：
$$z^{\uparrow_{\mathbb{F}\mathbb{Z}} (\xi(p)-1)} \equiv \mathbf{1}_{\mathbb{F}\mathbb{Z}} \pmod{p}$$

**证明：**
设 $\xi(p) = q, \xi(z) = n$。由标准费马小定理，$n^{q-1} \equiv 1 \pmod{q}$。

在φ-整数中：

$$\xi(z^{\uparrow_{\mathbb{F}\mathbb{Z}} (q-1)}) = \xi(z)^{q-1} = n^{q-1} \equiv 1 \pmod{q}$$

因此：

$$z^{\uparrow_{\mathbb{F}\mathbb{Z}} (q-1)} \equiv \mathbf{1}_{\mathbb{F}\mathbb{Z}} \pmod{p}$$
∎

## 定理 14.8（φ-整数环的理想分类）
$\mathbb{F}\mathbb{Z}$ 中的理想完全由其生成元刻画：

1. **零理想**：$(0) = \{\mathbf{0}_{\mathbb{F}\mathbb{Z}}\}$
2. **单位理想**：$(\mathbf{1}_{\mathbb{F}\mathbb{Z}}) = \mathbb{F}\mathbb{Z}$  
3. **素理想**：$(p)$，其中 $p$ 为φ-素元
4. **合成理想**：$(z)$，其中 $z$ 为非素非单位元素

所有理想形成与 $\mathbb{Z}$ 的理想格同构的格结构。

**证明：**
由定理14.1，$\mathbb{F}\mathbb{Z}$ 是主理想整环，故每个理想都是主理想。
理想的分类直接由同构 $\xi$ 和标准整数理想分类得出。 ∎

## 推论 14.1（φ-整数的模算术）
φ-整数的模算术与标准整数模算术完全等价：

对任意 $m \in \mathbb{F}\mathbb{Z}$，商环 $\mathbb{F}\mathbb{Z}/(m) \cong \mathbb{Z}/(\xi(m))$。

特别地，当 $p$ 为φ-素元时，$\mathbb{F}\mathbb{Z}/(p)$ 是有限域，含 $\xi(p)$ 个元素。

**证明：**
由第一同构定理和双射 $\xi$ 的保持性直接得出。 ∎

## 定理 14.9（φ-整数的二次剩余理论）
设 $p \in \mathbb{F}\mathbb{Z}$ 为奇φ-素元，$z \in \mathbb{F}\mathbb{Z}$ 且 $p \nmid z$。

定义**φ-勒让德符号**：
$$\left(\frac{z}{p}\right)_\phi = \left(\frac{\xi(z)}{\xi(p)}\right)$$

其中右边为标准勒让德符号。

φ-二次互反律和所有二次剩余性质都在φ-整数中保持成立。

**证明：**
由同构性质，φ-整数的二次剩余理论与标准整数二次剩余理论一一对应。 ∎

## 推论 14.2（φ-整数代数结构的完备性）
φ-整数环 $\mathbb{F}\mathbb{Z}$ 具有与标准整数环 $\mathbb{Z}$ 完全相同的代数性质：

1. 主理想整环结构
2. 唯一因数分解性质
3. 欧几里得算法和贝祖恒等式
4. 中国剩余定理和威尔逊定理
5. 费马小定理和二次互反律
6. 完整的模算术理论

这证明了φ-整数系统作为标准整数系统的完全等价替代的可行性。

**证明：**
所有性质都由环同构 $\xi: \mathbb{F}\mathbb{Z} \to \mathbb{Z}$ 的保持性和前述各定理直接得出。 ∎