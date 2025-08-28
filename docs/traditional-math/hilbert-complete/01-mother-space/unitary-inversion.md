# 1.2.3 幺正反演算子

## 定义 1.2.4 (反演算子)

在母空间$\mathcal{H} = L^2(\mathbb{R}, w(t)\,dt)$上定义**反演算子**$J$：

$$(Jf)(t) := f(-t), \quad \forall f \in \mathcal{H}, \, t \in \mathbb{R}$$

## 定理 1.2.4 (反演算子的幺正性)

算子$J: \mathcal{H} \to \mathcal{H}$是幺正且自反的，即：

1. **自反性**：$J^2 = I$（恒等算子）
2. **自伴性**：$J^* = J$
3. **幺正性**：$J^*J = JJ^* = I$

**证明**：

1. **自反性**：对任意$f \in \mathcal{H}$和$t \in \mathbb{R}$：
   $$(J^2f)(t) = (J(Jf))(t) = (Jf)(-t) = f(-(-t)) = f(t)$$
   故$J^2 = I$。

2. **自伴性**：需证明$\langle Jf, g \rangle = \langle f, Jg \rangle$对所有$f,g \in \mathcal{H}$：
   $$\langle Jf, g \rangle = \int_{-\infty}^{\infty} \overline{(Jf)(t)}g(t)w(t)\,dt = \int_{-\infty}^{\infty} \overline{f(-t)}g(t)w(t)\,dt$$
   
   令$u = -t$，由于$w(-u) = w(u)$（对称权函数）：
   $$= \int_{-\infty}^{\infty} \overline{f(u)}g(-u)w(u)\,du = \int_{-\infty}^{\infty} \overline{f(u)}(Jg)(u)w(u)\,du = \langle f, Jg \rangle$$

3. **幺正性**：由$J^* = J$和$J^2 = I$直接得出$J^*J = J^2 = I$。$\square$

## 定理 1.2.5 (反演算子的谱性质)

反演算子$J$的谱为$\sigma(J) = \{-1, 1\}$，且：

1. **本征值**：$\lambda = 1$对应偶函数子空间，$\lambda = -1$对应奇函数子空间
2. **谱分解**：$J = 1 \cdot P_+ + (-1) \cdot P_-$，其中$P_\pm$为正交投影（见下节）

## 推论 1.2.2 (母空间的宇称分解)

母空间$\mathcal{H}$可分解为：

$$\mathcal{H} = \mathcal{H}_+ \oplus \mathcal{H}_-$$

其中：
- $\mathcal{H}_+ = \{f \in \mathcal{H} : f(-t) = f(t)\}$（偶函数子空间）  
- $\mathcal{H}_- = \{f \in \mathcal{H} : f(-t) = -f(t)\}$（奇函数子空间）

## 说明

**反演算子的几何意义**：
- $J$对应于复平面中$s \mapsto 1-s$的映射在谱侧的体现
- 在函数方程$\xi(s) = \xi(1-s)$中，$J$捕捉了"左右对称"的本质
- 母空间的宇称分解为后续的"自指观察者"结构提供基础

**物理类比**：
反演算子类似于量子力学中的宇称算子，将系统分解为具有确定宇称量子数的本征态。这种分解在母空间理论中起到基本的结构作用。