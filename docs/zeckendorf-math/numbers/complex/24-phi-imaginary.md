# φ-虚数单位的严格定义

## 定义 24.1（φ-虚数单位的代数特征）
**φ-虚数单位** $\mathbf{i}_{\mathbb{F}}$ 定义为φ-复数域 $\mathbb{F}\mathbb{C}$ 中满足以下最小多项式的唯一元素：
$$\mathbf{i}_{\mathbb{F}}^2 \oplus_{\mathbb{F}\mathbb{C}} \mathbf{1}_{\mathbb{F}\mathbb{C}} = \mathbf{0}_{\mathbb{F}\mathbb{C}}$$

等价地，$\mathbf{i}_{\mathbb{F}}$ 为方程 $X^2 + 1 = 0$ 在φ-复数域中的根。

## 定理 24.1（φ-虚数单位的存在性和唯一性）
方程 $X^2 \oplus_{\mathbb{F}\mathbb{C}} \mathbf{1}_{\mathbb{F}\mathbb{C}} = \mathbf{0}_{\mathbb{F}\mathbb{C}}$ 在φ-复数域中有且仅有两个根：$\mathbf{i}_{\mathbb{F}}$ 和 $-\mathbf{i}_{\mathbb{F}}$。

**证明：**
**存在性**：在φ-复数的构造中（定义23.1），$\mathbf{i}_{\mathbb{F}}$ 表示为：
$$\mathbf{i}_{\mathbb{F}} = (\mathbf{0}_{\mathbb{F}\mathbb{R}}, \mathbf{1}_{\mathbb{F}\mathbb{R}}) = \mathbf{0}_{\mathbb{F}\mathbb{R}} \oplus_{\mathbb{F}\mathbb{C}} \mathbf{1}_{\mathbb{F}\mathbb{R}} \mathbf{i}_{\mathbb{F}}$$

验证：
$$\mathbf{i}_{\mathbb{F}}^2 = (\mathbf{0}_{\mathbb{F}\mathbb{R}}, \mathbf{1}_{\mathbb{F}\mathbb{R}}) \otimes_{\mathbb{F}\mathbb{C}} (\mathbf{0}_{\mathbb{F}\mathbb{R}}, \mathbf{1}_{\mathbb{F}\mathbb{R}}) = (\mathbf{0}_{\mathbb{F}\mathbb{R}} \cdot \mathbf{0}_{\mathbb{F}\mathbb{R}} - \mathbf{1}_{\mathbb{F}\mathbb{R}} \cdot \mathbf{1}_{\mathbb{F}\mathbb{R}}, \mathbf{0}_{\mathbb{F}\mathbb{R}} \cdot \mathbf{1}_{\mathbb{F}\mathbb{R}} + \mathbf{1}_{\mathbb{F}\mathbb{R}} \cdot \mathbf{0}_{\mathbb{F}\mathbb{R}}) = (-\mathbf{1}_{\mathbb{F}\mathbb{R}}, \mathbf{0}_{\mathbb{F}\mathbb{R}})$$

因此 $\mathbf{i}_{\mathbb{F}}^2 = -\mathbf{1}_{\mathbb{F}\mathbb{C}}$，即 $\mathbf{i}_{\mathbb{F}}^2 \oplus_{\mathbb{F}\mathbb{C}} \mathbf{1}_{\mathbb{F}\mathbb{C}} = \mathbf{0}_{\mathbb{F}\mathbb{C}}$。

**唯一性**：二次方程最多有两个根。$-\mathbf{i}_{\mathbb{F}} = (\mathbf{0}_{\mathbb{F}\mathbb{R}}, -\mathbf{1}_{\mathbb{F}\mathbb{R}})$ 为另一根。

**根的完整性**：设 $z = a \oplus_{\mathbb{F}\mathbb{C}} b \mathbf{i}_{\mathbb{F}}$ 为方程的根，则：
$$z^2 = (a^2 - b^2) \oplus_{\mathbb{F}\mathbb{C}} (2ab) \mathbf{i}_{\mathbb{F}} = -\mathbf{1}_{\mathbb{F}\mathbb{C}}$$

比较系数：$a^2 - b^2 = -\mathbf{1}_{\mathbb{F}\mathbb{R}}$ 且 $2ab = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。
由第二个等式，$a = \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 或 $b = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。
若 $a = \mathbf{0}_{\mathbb{F}\mathbb{R}}$，则 $-b^2 = -\mathbf{1}_{\mathbb{F}\mathbb{R}}$，故 $b = \pm \mathbf{1}_{\mathbb{F}\mathbb{R}}$。
若 $b = \mathbf{0}_{\mathbb{F}\mathbb{R}}$，则 $a^2 = -\mathbf{1}_{\mathbb{F}\mathbb{R}}$，在φ-实数中无解。

因此根为 $z = \pm \mathbf{i}_{\mathbb{F}}$。 ∎

## 定义 24.2（φ-虚数单位的幂运算性质）
φ-虚数单位的幂次满足周期性：

对 $n \in \mathbb{F}\mathbb{Z}$：
$$\mathbf{i}_{\mathbb{F}}^n = \begin{cases}
\mathbf{1}_{\mathbb{F}\mathbb{C}} & \text{若 } n \equiv \mathbf{0}_{\mathbb{F}\mathbb{Z}} \pmod{\mathbf{4}_{\mathbb{F}\mathbb{Z}}} \\
\mathbf{i}_{\mathbb{F}} & \text{若 } n \equiv \mathbf{1}_{\mathbb{F}\mathbb{Z}} \pmod{\mathbf{4}_{\mathbb{F}\mathbb{Z}}} \\
-\mathbf{1}_{\mathbb{F}\mathbb{C}} & \text{若 } n \equiv \mathbf{2}_{\mathbb{F}\mathbb{Z}} \pmod{\mathbf{4}_{\mathbb{F}\mathbb{Z}}} \\
-\mathbf{i}_{\mathbb{F}} & \text{若 } n \equiv \mathbf{3}_{\mathbb{F}\mathbb{Z}} \pmod{\mathbf{4}_{\mathbb{F}\mathbb{Z}}}
\end{cases}$$

## 定理 24.2（φ-虚数单位幂次的周期性）
φ-虚数单位的幂运算具有周期4的周期性。

**证明：**
**基础幂次**：
- $\mathbf{i}_{\mathbb{F}}^0 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$（幂运算的零指数性质）
- $\mathbf{i}_{\mathbb{F}}^1 = \mathbf{i}_{\mathbb{F}}$（幂运算的单位指数性质）
- $\mathbf{i}_{\mathbb{F}}^2 = -\mathbf{1}_{\mathbb{F}\mathbb{C}}$（定义24.1）
- $\mathbf{i}_{\mathbb{F}}^3 = \mathbf{i}_{\mathbb{F}}^2 \otimes_{\mathbb{F}\mathbb{C}} \mathbf{i}_{\mathbb{F}} = (-\mathbf{1}_{\mathbb{F}\mathbb{C}}) \otimes_{\mathbb{F}\mathbb{C}} \mathbf{i}_{\mathbb{F}} = -\mathbf{i}_{\mathbb{F}}$
- $\mathbf{i}_{\mathbb{F}}^4 = (\mathbf{i}_{\mathbb{F}}^2)^2 = (-\mathbf{1}_{\mathbb{F}\mathbb{C}})^2 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$

**周期性**：由于 $\mathbf{i}_{\mathbb{F}}^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$，对任意 $n \in \mathbb{F}\mathbb{Z}$：
$$\mathbf{i}_{\mathbb{F}}^{n+4} = \mathbf{i}_{\mathbb{F}}^n \otimes_{\mathbb{F}\mathbb{C}} \mathbf{i}_{\mathbb{F}}^4 = \mathbf{i}_{\mathbb{F}}^n \otimes_{\mathbb{F}\mathbb{C}} \mathbf{1}_{\mathbb{F}\mathbb{C}} = \mathbf{i}_{\mathbb{F}}^n$$

**负幂次**：对 $n \succ_{\mathbb{F}\mathbb{Z}} \mathbf{0}_{\mathbb{F}\mathbb{Z}}$：
$$\mathbf{i}_{\mathbb{F}}^{-n} = (\mathbf{i}_{\mathbb{F}}^{-1})^n = (-\mathbf{i}_{\mathbb{F}})^n$$

由于 $(-\mathbf{i}_{\mathbb{F}})^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$，负幂次也满足周期4。 ∎

## 定义 24.3（φ-虚数单位的生成子群）
φ-虚数单位在φ-复数乘法群中生成的子群为：
$$\langle \mathbf{i}_{\mathbb{F}} \rangle = \{\mathbf{i}_{\mathbb{F}}^n : n \in \mathbb{F}\mathbb{Z}\} = \{\mathbf{1}_{\mathbb{F}\mathbb{C}}, \mathbf{i}_{\mathbb{F}}, -\mathbf{1}_{\mathbb{F}\mathbb{C}}, -\mathbf{i}_{\mathbb{F}}\}$$

## 定理 24.3（φ-虚数单位群的循环性质）
$\langle \mathbf{i}_{\mathbb{F}} \rangle$ 构成4阶循环群，同构于 $\mathbb{Z}/4\mathbb{Z}$。

**证明：**
**群结构**：
- **封闭性**：由定理24.2的周期性，任意两个元素的乘积仍在集合中
- **结合律**：继承自φ-复数乘法的结合律
- **单位元**：$\mathbf{1}_{\mathbb{F}\mathbb{C}} \in \langle \mathbf{i}_{\mathbb{F}} \rangle$
- **逆元**：$(\mathbf{i}_{\mathbb{F}})^{-1} = -\mathbf{i}_{\mathbb{F}}$，$(-\mathbf{i}_{\mathbb{F}})^{-1} = \mathbf{i}_{\mathbb{F}}$，$(\pm \mathbf{1}_{\mathbb{F}\mathbb{C}})^{-1} = \pm \mathbf{1}_{\mathbb{F}\mathbb{C}}$

**循环性**：$\mathbf{i}_{\mathbb{F}}$ 为生成元，阶为4。

**同构性**：映射 $\phi: \mathbb{Z}/4\mathbb{Z} \to \langle \mathbf{i}_{\mathbb{F}} \rangle$ 定义为 $\phi([n]_4) = \mathbf{i}_{\mathbb{F}}^n$ 为群同构。 ∎

## 定义 24.4（φ-虚数单位的几何解释）
在φ-复数平面中，乘以φ-虚数单位对应几何旋转：

对φ-复数 $z = a \oplus_{\mathbb{F}\mathbb{C}} b \mathbf{i}_{\mathbb{F}}$：
$$z \otimes_{\mathbb{F}\mathbb{C}} \mathbf{i}_{\mathbb{F}} = -b \oplus_{\mathbb{F}\mathbb{C}} a \mathbf{i}_{\mathbb{F}}$$

这对应平面中绕原点逆时针旋转90度。

## 定理 24.4（φ-虚数单位乘法的几何性质）
乘以φ-虚数单位实现φ-复数平面的90度旋转变换。

**证明：**
**坐标变换**：$(a, b) \mapsto (-b, a)$ 对应将向量 $(a, b)$ 逆时针旋转90度。

**保持距离**：
$$|\mathbf{i}_{\mathbb{F}} \otimes_{\mathbb{F}\mathbb{C}} z|_{\mathbb{F}\mathbb{C}} = |(-b) \oplus_{\mathbb{F}\mathbb{C}} a \mathbf{i}_{\mathbb{F}}|_{\mathbb{F}\mathbb{C}} = \sqrt{\mathbb{F}\mathbb{R}}[(-b)^2 + a^2] = \sqrt{\mathbb{F}\mathbb{R}}[a^2 + b^2] = |z|_{\mathbb{F}\mathbb{C}}$$

**角度变换**：设 $z = |z|_{\mathbb{F}\mathbb{C}} e^{\mathbf{i}_{\mathbb{F}} \theta}$，则：
$$\mathbf{i}_{\mathbb{F}} \otimes_{\mathbb{F}\mathbb{C}} z = |z|_{\mathbb{F}\mathbb{C}} \mathbf{i}_{\mathbb{F}} e^{\mathbf{i}_{\mathbb{F}} \theta} = |z|_{\mathbb{F}\mathbb{C}} e^{\mathbf{i}_{\mathbb{F}} (\theta + \pi_{\mathbb{F}}/2)}$$

这确实对应90度（$\pi_{\mathbb{F}}/2$ 弧度）的旋转。 ∎

## 定义 24.5（φ-虚数单位的幅角表示）
φ-虚数单位在极坐标表示中为：
$$\mathbf{i}_{\mathbb{F}} = e^{\mathbf{i}_{\mathbb{F}} \pi_{\mathbb{F}}/2} = \cos_{\mathbb{F}}(\pi_{\mathbb{F}}/2) \oplus_{\mathbb{F}\mathbb{C}} \sin_{\mathbb{F}}(\pi_{\mathbb{F}}/2) \mathbf{i}_{\mathbb{F}}$$

其中 $\pi_{\mathbb{F}}$ 为φ-圆周率（将在文件56中定义）。

## 定理 24.5（φ-虚数单位与φ-三角函数的关系）
φ-虚数单位满足：
$$\cos_{\mathbb{F}}(\pi_{\mathbb{F}}/2) = \mathbf{0}_{\mathbb{F}\mathbb{R}}, \quad \sin_{\mathbb{F}}(\pi_{\mathbb{F}}/2) = \mathbf{1}_{\mathbb{F}\mathbb{R}}$$

**证明：**
由φ-虚数单位的表示 $\mathbf{i}_{\mathbb{F}} = (\mathbf{0}_{\mathbb{F}\mathbb{R}}, \mathbf{1}_{\mathbb{F}\mathbb{R}})$ 和极坐标表示的唯一性（定理23.7），
必有 $|\mathbf{i}_{\mathbb{F}}|_{\mathbb{F}\mathbb{C}} = \mathbf{1}_{\mathbb{F}\mathbb{R}}$ 且幅角为 $\pi_{\mathbb{F}}/2$。

因此：
$$\mathbf{i}_{\mathbb{F}} = \mathbf{1}_{\mathbb{F}\mathbb{R}} \otimes_{\mathbb{F}\mathbb{C}} (\cos_{\mathbb{F}}(\pi_{\mathbb{F}}/2) \oplus_{\mathbb{F}\mathbb{C}} \sin_{\mathbb{F}}(\pi_{\mathbb{F}}/2) \mathbf{i}_{\mathbb{F}}) = \cos_{\mathbb{F}}(\pi_{\mathbb{F}}/2) \oplus_{\mathbb{F}\mathbb{C}} \sin_{\mathbb{F}}(\pi_{\mathbb{F}}/2) \mathbf{i}_{\mathbb{F}}$$

比较实部和虚部系数得到结论。 ∎

## 定义 24.6（φ-四元数单位根）
φ-虚数单位的幂次构成**φ-四次单位根**：
$$\mathcal{U}_4(\mathbb{F}\mathbb{C}) = \{z \in \mathbb{F}\mathbb{C} : z^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}\} = \{\mathbf{1}_{\mathbb{F}\mathbb{C}}, \mathbf{i}_{\mathbb{F}}, -\mathbf{1}_{\mathbb{F}\mathbb{C}}, -\mathbf{i}_{\mathbb{F}}\}$$

## 定理 24.6（φ-四次单位根的完备性）
$\mathcal{U}_4(\mathbb{F}\mathbb{C})$ 包含方程 $X^4 - 1 = 0$ 在φ-复数域中的所有根。

**证明：**
**直接验证**：
- $(\mathbf{1}_{\mathbb{F}\mathbb{C}})^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$
- $(\mathbf{i}_{\mathbb{F}})^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$（由定理24.2）
- $(-\mathbf{1}_{\mathbb{F}\mathbb{C}})^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$
- $(-\mathbf{i}_{\mathbb{F}})^4 = (\mathbf{i}_{\mathbb{F}})^4 = \mathbf{1}_{\mathbb{F}\mathbb{C}}$

**根的计数**：四次多项式最多有4个根，已找到4个不同的根，故完备。

**几何解释**：四次单位根对应复平面上的正方形顶点，均匀分布在单位圆上。 ∎

## 定义 24.7（φ-虚数单位的共轭性质）
φ-虚数单位的φ-复数共轭为：
$$\overline{\mathbf{i}_{\mathbb{F}}} = \overline{(\mathbf{0}_{\mathbb{F}\mathbb{R}}, \mathbf{1}_{\mathbb{F}\mathbb{R}})} = (\mathbf{0}_{\mathbb{F}\mathbb{R}}, -\mathbf{1}_{\mathbb{F}\mathbb{R}}) = -\mathbf{i}_{\mathbb{F}}$$

## 定理 24.7（φ-虚数单位与实数的区别）
φ-虚数单位不属于φ-实数域：$\mathbf{i}_{\mathbb{F}} \notin \mathbb{F}\mathbb{R}$。

**证明：**
反证法：假设 $\mathbf{i}_{\mathbb{F}} \in \mathbb{F}\mathbb{R}$，即存在 $r \in \mathbb{F}\mathbb{R}$ 使得 $\mathbf{i}_{\mathbb{F}} = r$。

则 $r^2 = -\mathbf{1}_{\mathbb{F}\mathbb{R}}$，即φ-实数 $r$ 满足 $r^2 \oplus_{\mathbb{F}\mathbb{R}} \mathbf{1}_{\mathbb{F}\mathbb{R}} = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。

但由φ-实数的有序域性质（定理18.5），对任意 $r \in \mathbb{F}\mathbb{R}$：
$$r^2 \succeq_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$$

因此 $r^2 \oplus_{\mathbb{F}\mathbb{R}} \mathbf{1}_{\mathbb{F}\mathbb{R}} \succeq_{\mathbb{F}\mathbb{R}} \mathbf{1}_{\mathbb{F}\mathbb{R}} \succ_{\mathbb{F}\mathbb{R}} \mathbf{0}_{\mathbb{F}\mathbb{R}}$，矛盾。

故 $\mathbf{i}_{\mathbb{F}} \notin \mathbb{F}\mathbb{R}$。 ∎

## 定理 24.8（φ-域扩张的维数）
φ-复数域作为φ-实数域的向量空间扩张具有维数2：
$$[\mathbb{F}\mathbb{C} : \mathbb{F}\mathbb{R}] = 2$$

基为 $\{\mathbf{1}_{\mathbb{F}\mathbb{C}}, \mathbf{i}_{\mathbb{F}}\}$。

**证明：**
**线性无关性**：设 $a \mathbf{1}_{\mathbb{F}\mathbb{C}} \oplus_{\mathbb{F}\mathbb{C}} b \mathbf{i}_{\mathbb{F}} = \mathbf{0}_{\mathbb{F}\mathbb{C}}$，其中 $a, b \in \mathbb{F}\mathbb{R}$。

这等价于 $(a, b) = (\mathbf{0}_{\mathbb{F}\mathbb{R}}, \mathbf{0}_{\mathbb{F}\mathbb{R}})$，故 $a = b = \mathbf{0}_{\mathbb{F}\mathbb{R}}$。

**生成性**：任意φ-复数 $z = (a, b)$ 可表示为：
$$z = a \mathbf{1}_{\mathbb{F}\mathbb{C}} \oplus_{\mathbb{F}\mathbb{C}} b \mathbf{i}_{\mathbb{F}}$$

**维数计算**：由线性无关性和生成性，基的大小为2，故 $[\mathbb{F}\mathbb{C} : \mathbb{F}\mathbb{R}] = 2$。 ∎

## 定义 24.8（φ-虚数单位的最小多项式）
φ-虚数单位在φ-实数域上的**最小多项式**为：
$$m_{\mathbf{i}_{\mathbb{F}}}(X) = X^2 \oplus_{\mathbb{F}\mathbb{R}[X]} \mathbf{1}_{\mathbb{F}\mathbb{R}}$$

## 定理 24.9（φ-虚数单位最小多项式的不可约性）
多项式 $X^2 + 1$ 在φ-实数域 $\mathbb{F}\mathbb{R}$ 上不可约。

**证明：**
**次数检查**：多项式为二次，若可约则必有φ-实数根。

**根的不存在性**：由定理24.7，方程 $X^2 + 1 = 0$ 在φ-实数中无解。

**不可约性**：二次多项式无实根当且仅当不可约。

**最小性**：$\mathbf{i}_{\mathbb{F}}$ 不满足任何低于2次的φ-实系数多项式方程（$\mathbf{i}_{\mathbb{F}} \neq \mathbf{0}_{\mathbb{F}\mathbb{R}}$ 且不是任何φ-实数）。 ∎

## 定理 24.10（φ-复数域的代数构造）
φ-复数域可构造为φ-实数域的代数扩张：
$$\mathbb{F}\mathbb{C} \cong \mathbb{F}\mathbb{R}[X]/(X^2 + 1)$$

其中右边为φ-实数上的多项式环对不可约多项式 $X^2 + 1$ 的商环。

**证明：**
**同构映射**：定义 $\psi: \mathbb{F}\mathbb{R}[X]/(X^2 + 1) \to \mathbb{F}\mathbb{C}$：
$$\psi([a + bX]) = a \oplus_{\mathbb{F}\mathbb{C}} b \mathbf{i}_{\mathbb{F}}$$

**良定义性**：若 $a + bX \equiv a' + b'X \pmod{X^2 + 1}$，则：
$$(a - a') + (b - b')X = (X^2 + 1) \cdot q(X)$$

比较系数得 $a = a', b = b'$，故映射良定义。

**同态性**：
- **加法保持**：$\psi([f] + [g]) = \psi([f]) \oplus_{\mathbb{F}\mathbb{C}} \psi([g])$
- **乘法保持**：$\psi([f] \cdot [g]) = \psi([f]) \otimes_{\mathbb{F}\mathbb{C}} \psi([g])$

关键验证：$\psi([X]) = \mathbf{i}_{\mathbb{F}}$ 且 $\psi([X^2]) = \mathbf{i}_{\mathbb{F}}^2 = -\mathbf{1}_{\mathbb{F}\mathbb{C}} = \psi([-1])$

**双射性**：由维数理论和构造的自然性。 ∎

## 推论 24.1（φ-虚数单位的基本性质总结）
φ-虚数单位 $\mathbf{i}_{\mathbb{F}}$ 实现了φ-实数域到φ-复数域的最小代数扩张：

1. **代数性质**：为二次最小多项式 $X^2 + 1$ 的根
2. **几何性质**：实现90度旋转变换
3. **群论性质**：生成4阶循环群
4. **拓扑性质**：在φ-复数平面的单位圆上
5. **域论性质**：实现维数2的域扩张
6. **同构性质**：与标准虚数单位完全对应

这为φ-复分析学、φ-代数几何学和φ-数论提供了虚数理论基础。

**证明：**
所有性质由定理24.1-24.10综合得出，特别是最小多项式的不可约性（定理24.9）和代数构造（定理24.10）确保了φ-虚数单位的理论完备性。 ∎