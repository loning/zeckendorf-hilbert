# 一致性工厂：受限主丛—散射—$K^{1}$ 的族级统一与整数唯一性

## 摘要

本文建立一个把**受限几何**（受限酉群与受限 Grassmann 流形）、**散射谱理论**（Birman–Kreĭn 公式、谱移函数、谱流）与**拓扑 $K$ 理论**（$K^{1}$ 的表示空间）在**族（families）层级**无缝拼接的框架。首先以 Hilbert–Schmidt 受限模型赋予 $U_{\mathrm{res}}$ 与 $\mathrm{Gr}_{\mathrm{res}}$ 明确的 Hilbert–Lie 几何结构，证明存在 $H$-空间等价 $U_{\mathrm{res}}\simeq \Omega U$ 并据此得到去圈识别 $BU_{\mathrm{res}}\simeq U$，从而在仿紧基空间上给出 $U_{\mathrm{res}}$-主丛的 $K^{1}$-分类。其次，在"gap 连续 + 相对迹类 + 族 Schatten 连续 + 端点闭合"的最小可检假设下，以**相对 Cayley 变换**将散射族 $(H,H_{0})$ 送入 $K^{1}(X)$，并通过 Pushnitski 不变性、Birman–Kreĭn 公式与"谱移＝谱流＝$K^{1}$ 基本类"的传送带，证明该构造与能量侧稳定酉环路之类一致且与平滑/截断选择无关。最后提出一组极简公理（连续性、函子性/不变性、外直和加性、尺度等变、BK 归一化），在可表性与 Bott 兼容的约束下证明：满足这些公理的任何自然变换均为"乘以整数"的唯一类，经秩一原型归一化得到**整数 $+1$**。作为跨域参照，给出 $\mathbf{FinStat}$ 上相对熵类函子的张量自然变换唯一到非负常数倍。附录提供主丛局部切片与去圈识别、相对 Cayley 的族级 Schatten 控制、尺度等变的显式同伦、能量侧端点闭合与族版不变性、秩一 BK 归一化及"唯一至整数倍"的函子论证明等完整技术细节。

**关键词**：受限酉群；受限 Grassmann 流形；去圈识别；Bott 周期性；主丛分类；相对 Cayley 变换；谱移函数；Birman–Kreĭn 公式；谱流；$K^{1}$ 表示；张量自然变换；相对熵

---

## 1. 引言与历史背景

本文的目标是把下列三条成熟脉络**在族级层面**对齐并闭合为"存在—分类—唯一"的环路：

* **受限几何 $\longleftrightarrow$ $K^{1}$ 表示**：受限 Grassmann 流形 $\mathrm{Gr}_{\mathrm{res}}$ 与受限酉群 $U_{\mathrm{res}}$ 的同伦型与 Bott 周期性匹配，诱导 $BU_{\mathrm{res}}\simeq U$，从而在仿紧 $X$ 上 $\mathrm{Prin}_{U_{\mathrm{res}}}(X)\cong K^{1}(X)$。
* **散射 $\longleftrightarrow$ $K^{1}$**：对自伴算子对 $(H,H_{0})$ 的族，在相对迹类与 gap 连续下经相对 Cayley 变换得到 $K^{1}(X)$ 元；能量侧由稳定酉环路（行列式相位的绕数）给出同一 $K^{1}$ 元；两者对平滑/截断选择同伦不变。
* **唯一性范式**：在极简公理（连续性、加性、尺度等变、BK 归一化）下，散射族 $\to K^{1}$ 的自然变换**唯一到整数倍**；经秩一原型归一化为 $+1$。在 $\mathbf{FinStat}$ 上相对熵类函子**唯一到非负常数倍**作为平行参照。

经典来源包括：Segal–Wilson 与 Pressley–Segal 关于受限 Grassmann/受限群的几何与同伦结构；Kuiper 关于无限维酉群的可收缩性；Bott 周期性与 $K^{1}$ 的表示；Pushnitski 的不变性原理与 Birman–Kreĭn 公式；谱移＝谱流（Azamov–Carey–Dodds–Sukochev）与谱流＝$K^{1}$ 基本类（Phillips）；Baez–Fritz 关于 $\mathbf{FinStat}$ 上相对熵的范畴刻画。本文在这些基底上，系统化族级正则与选择无关性，并把"公理 + 归一化 $\Rightarrow$ 唯一倍数"的思想推广到散射 $\to K^{1}$。

---

## 2. 模型与假设

### 2.1 受限模型与拓扑约定

令 $\mathcal H$ 为可分复 Hilbert 空间，取极化 $\mathcal H=\mathcal H_{+}\oplus \mathcal H_{-}$ 与正投影 $\mathsf P_{+}$。记 Schatten 理想 $\mathfrak S_{p}$（$1\le p\le\infty$），Hilbert–Schmidt 理想 $\mathfrak S_{2}$。

* **受限酉群（Hilbert–Schmidt 受限）**

$$
U_{\mathrm{res}}=\bigl\{U\in U(\mathcal H):[U,\mathsf P_{+}]\in \mathfrak S_{2}\bigr\},
$$

以 $\mathfrak S_{2}$ 模型为切空间赋予 Hilbert–Lie 群结构与相应流形拓扑。

* **受限 Grassmann 流形**

$$
\mathrm{Gr}_{\mathrm{res}}=\bigl\{W\subset\mathcal H\ \text{闭直和子空间}:\ \mathsf P_{+}|_{W}-\mathrm{id}_{W}\in\mathfrak S_{2}\bigr\},
$$

用图像坐标（到 $\mathcal B(\mathcal H_{+},\mathcal H_{-})\cap\mathfrak S_{2}$）赋予 Hilbert 流形结构。$U_{\mathrm{res}}$ 以 $U\cdot W=UW$ 作用其上。

* **稳定酉群与 $K^{1}$ 表示**
  以直和极限 $U=\varinjlim_{n}U(n)$ 为 $H$-空间（外直和乘法）；对仿紧/CW 型拓扑空间 $X$ 有 $[X,U]\cong K^{1}(X)$。

> **记号**：若不致混淆，$H$-空间同伦等价与弱同伦等价均记为 $\simeq$；同构记为 $\cong$。

### 2.2 散射族最小可检假设

设 $X$ 为仿紧可度量空间。对自伴算子族 $\{(H_{x},H_{0,x})\}_{x\in X}\subset\mathcal B(\mathcal H)$ 要求：

* **(S1) gap 连续**：$x\mapsto (H_{x}\pm i)^{-1}$、$(H_{0,x}\pm i)^{-1}$ 在算子范数连续。

* **(S2) 相对迹类与族 $\mathfrak S_{1}$ 连续**：

$$
(H_{x}-H_{0,x})(H_{0,x}-i)^{-1}\in \mathfrak S_{1},\qquad
x\longmapsto |(H_{x}-H_{0,x})(H_{0,x}-i)^{-1}|_{\mathfrak S_{1}}\ \text{连续}.
$$

* **(S3) 散射正则（族版）**：a.e. $\lambda>0$ 有 $S_{x}(\lambda)-\mathbf 1\in \mathfrak S_{1}$，且对任意紧能量区间 $I\subset(0,\infty)$、紧 $K\subset X$，

$$
\sup_{x\in K}\int_{I}|S_{x}(\lambda)-\mathbf 1|_{\mathfrak S_{1}}\,d\lambda<\infty.
$$

* **(S4) 端点闭合**：存在统一的能量重参数与端点静态连接，使 $\lambda\in[0,\infty]\mapsto S_{x}(\lambda)$ 在商 $U^{(1)}:=\{\mathbf 1+\mathfrak S_{1}\}$ 中闭合为环路，且该闭合对选择同伦不变。

> **适用范围备注**：一维短程或相对有限秩/迹类模型满足（S3）；高维情形常见 $S(\lambda)-\mathbf 1\in \mathfrak S_{p}$（$p>1$），可用修正行列式与相位替代，见 §8 讨论。

### 2.3 自然性公理（散射族 $\to K^{1}$）

设候选自然变换 $\Phi$ 将对象 $(H,H_{0})$（或其族）送入 $K^{1}$：

* **(C0) 极限/同伦保持**：对（S1）–（S2）控制下的逼近与 gap 同伦，$\Phi$ 保持极限与同伦类；
* **(C1) 不变性/函子性**：对纤维上连续的酉共轭、平凡稳定化、同构拉回不变；
* **(C2) 外直和加性**：$\Phi((H_{1}\oplus H_{2}),(H_{0,1}\oplus H_{0,2}))=\Phi(H_{1},H_{0,1})+\Phi(H_{2},H_{0,2})$；
* **(C3) 尺度等变**：$\Phi(aH,aH_{0})=\Phi(H,H_{0})$（$a>0$）；
* **(C4) BK 归一化**：在标准秩一原型（§6）上 $\Phi$ 取 $K^{1}(S^{1})\cong\mathbb Z$ 的正生成元。

---

## 3. 主要结果

### 定理 B（受限主丛的 $K^{1}$ 分类）

存在 $H$-空间等价

$$
U_{\mathrm{res}}\ \simeq\ \Omega U,
$$

从而 $BU_{\mathrm{res}}\simeq U$。对仿紧 $X$，自然同构

$$
\mathrm{Prin}_{U_{\mathrm{res}}}(X)\ \cong\ [X,BU_{\mathrm{res}}]\ \cong\ [X,U]\ \cong\ K^{1}(X).
$$

### 定理 A1（相对 Cayley 的族级 $K^{1}$ 构造）

在（S1）–（S2）下，定义

$$
U(H):=(H-i)(H+i)^{-1},\qquad u_{x}:=U(H_{x})U(H_{0,x})^{-1}\in U^{(1)}.
$$

则 $x\mapsto u_{x}$ 范数连续并确定 $K^{1}(X)$ 元 $[u_{\bullet}]$。

### 定理 A2（能量侧与 Cayley 侧的一致性与选择无关）

在（S1）–（S4）下，由 $S_{x}(\lambda)$ 的稳定酉环路构造的 $\Gamma_{x}:S^{1}\to U^{(1)}$ 给出 $K^{1}(X)$ 元 $[\Gamma_{\bullet}]$。有

$$
[\Gamma_{\bullet}]\ =\ [u_{\bullet}]\ \in K^{1}(X),
$$

并且对能量平滑、截断与端点闭合的选择同伦不变。

### 定理 A3（唯一性至整数倍）

设 $\Phi$ 为把散射族送入 $K^{1}$ 的自然变换，满足（C0）–（C4）。则存在唯一整数 $n$ 使得

$$
\Phi\ =\ n\cdot \Phi_{\mathrm{can}},
$$

其中 $\Phi_{\mathrm{can}}(H,H_{0})=[x\mapsto U(H_{x})U(H_{0,x})^{-1}]$ 为定理 A1 的**规范**构造。由（C4）在秩一原型上归一化得 $n=1$。

### 定理 C（$\mathbf{FinStat}$ 上相对熵的张量自然变换唯一）

在有限集概率分布与带右逆 Markov 箭头形成的范畴 $\mathbf{FinStat}$ 上，满足"凸线性、下半连续、数据处理不等式、最优假设处取零"的相对熵型函子均为 Kullback–Leibler 的常数倍。若 $F,G$ 为到 $(\mathbb R_{\ge 0},+)$ 的单体（笛卡尔张量）函子，则任意单体自然变换 $\eta:F\Rightarrow G$ 为某个非负常数 $c$ 的**逐对象标量倍**，且 $c$ 由 $\eta$ 在幺元对象处的值唯一决定。

---

## 4. 证明

### 4.1 定理 B

**步骤 1：主丛与同伦等价**
$U_{\mathrm{res}}$ 通过 $U\cdot W=UW$ 自由、适当地作用于 $\mathrm{Gr}_{\mathrm{res}}$。以图像坐标给出局部切片：对 $W\in\mathrm{Gr}_{\mathrm{res}}$，取小球 $\mathcal U_{W}\subset \mathcal B(\mathcal H_{+},\mathcal H_{-})\cap\mathfrak S_{2}$ 映到 $\mathrm{graph}(T)$。局部平凡性推出投影 $\pi:U_{\mathrm{res}}\to \mathrm{Gr}_{\mathrm{res}}$ 为光滑主丛，稳定子为块对角 $U(\mathcal H_{+})\times U(\mathcal H_{-})$。稳定子在范数拓扑可收缩（Kuiper），且其包含到受限子群为弱等价；纤维同伦平凡推出

$$
U_{\mathrm{res}}\ \simeq\ \mathrm{Gr}_{\mathrm{res}}.
$$

**步骤 2：$\mathrm{Gr}_{\mathrm{res}}$ 的同伦型**
受限 Grassmann 的连通分支由虚维（Fredholm 指数）标号，$\pi_{0}\cong\mathbb Z$。每个分支与 $BU$ 同伦等价，因此

$$
\mathrm{Gr}_{\mathrm{res}}\ \simeq\ \mathbb Z\times BU.
$$

**步骤 3：Bott 与去圈识别**
Bott 周期性 $\Omega U\simeq \mathbb Z\times BU$ 给出 $H$-空间等价

$$
U_{\mathrm{res}}\ \simeq\ \Omega U.
$$

对良点化 $A_{\infty}$ 空间之弱等价 $f:G\to H$，classifying space 函子 $B$ 保弱等价，遂

$$
BU_{\mathrm{res}}\ \simeq\ U.
$$

最后利用 $[X,U]\cong K^{1}(X)$ 得分类陈述。 $\square$

### 4.2 定理 A1

对自伴 $T$，分式预解式恒等式

$$
U(T)=\frac{T-i}{T+i}=I-2i\,(T+i)^{-1}.
$$

于是

$$
U(H_{x})-U(H_{0,x})=2i\,(H_{x}+i)^{-1}(H_{x}-H_{0,x})(H_{0,x}+i)^{-1}.
$$

由（S1）$(H_{x}\pm i)^{-1}$ 范数连续且一致有界；由（S2）$(H_{x}-H_{0,x})(H_{0,x}-i)^{-1}\in\mathfrak S_{1}$ 且族 $\mathfrak S_{1}$ 连续。理想性质给出

$$
|U(H_{x})-U(H_{0,x})|_{\mathfrak S_{1}}
\ \le\ 2\,|(H_{x}-H_{0,x})(H_{0,x}+i)^{-1}|_{\mathfrak S_{1}},
$$

从而 $u_{x}-I\in\mathfrak S_{1}$ 且 $x\mapsto u_{x}$ 范数连续，定义 $K^{1}(X)$ 元 $[u_{\bullet}]$。 $\square$

### 4.3 定理 A2

**（i）能量侧环路与 BK 公式**
在（S3）–（S4）下，选取统一能量重参数 $h:[0,1]\to[0,\infty]$ 与端点静态连接，使 $S_{x}(h(t))$ 在 $U^{(1)}$ 中闭合成环路 $\Gamma_{x}$。Birman–Kreĭn 公式给出

$$
\det S_{x}(\lambda)=\exp\{-2\pi i\, \xi_{x}(\lambda)\},
$$

其微分式为

$$
\frac{1}{2\pi i}\operatorname{tr}\bigl(S_{x}(\lambda)^{-1}\partial_{\lambda}S_{x}(\lambda)\bigr)\,d\lambda
\ =\ d\,\xi_{x}(\lambda).
$$

端点闭合与局部一致可积确保整环路的绕数等于 $\xi_{x}$ 的总变差。

**（ii）不变性与谱流**
Pushnitski 不变性将谱移函数从 $(H_{x},H_{0,x})$ 降至有界演算（如 $\arctan$ 或 Cayley），保持 $\xi_{x}$。谱移 = 谱流把 $\xi_{x}$ 与路径 $\{(H_{x}-\mu)\}_{\mu}$ 的谱流等同。Phillips 识别谱流为 $K^{1}$ 基本类，遂有能量侧 $[\Gamma_{\bullet}]=[u_{\bullet}]$。平滑/截断与端点闭合选择在不变性下同伦不变。 $\square$

### 4.4 定理 A3

**（i）因子化到表示空间**
可表性 $\mathbf{K1}(X)\cong[X,U]$ 使任何自然自同态 $\Phi:K^{1}(-)\Rightarrow K^{1}(-)$ 唯一对应于某个 $H$-空间自映射 $f:U\to U$ 的后合成：$\Phi_{X}([g])=[f\circ g]$。对散射族的自然变换 $\Phi$ 以 $(H,H_{0})\mapsto u$ 的"忘却"函子 $\mathcal U$ 为中介（由 A1 定义）得到 $\Phi=\Phi^{U}\circ \mathcal U$。

**（ii）生成元检测与延拓**
取 $X=S^{1}$，$\widetilde K^{1}(S^{1})\cong\mathbb Z$ 迫使 $\Phi_{S^{1}}$ 为乘 $n$。由外直和加性与 Bott 兼容，乘 $n$ 延拓至任意 $X$；因此 $\Phi=n\cdot \Phi_{\mathrm{can}}$。

**（iii）归一化**
在 §6 的秩一原型上 $\Phi_{\mathrm{can}}$ 取 $+1$；（C4）给出 $n=1$。 $\square$

### 4.5 定理 C（完整证明）

**对象与态射**。$\mathbf{FinStat}$ 的对象为有限集合 $X$ 携带先验 $q\in\Delta(X)$ 与"假设—观测"对 $(f,s)$（$f:X\to Y$ 为 Markov 箭头，$s:Y\to X$ 为右逆 Bayesian 更新，$fs=\mathrm{id}_Y$）。态射为可与右逆配对的 Markov 箭头；张量结构为笛卡尔乘积 $\otimes$，幺元对象为单点 $\mathbf 1$；目标单体范畴取 $(\mathbb R_{\ge0},+,0)$。

**Baez–Fritz 唯一性**。满足"凸线性、下半连续、数据处理不等式、最优假设处取零"的函子 $F:\mathbf{FinStat}\to(\mathbb R_{\ge0},+)$ 必为 $c\cdot D_{\mathrm{KL}}$（$c\ge0$）。

**单体自然变换的唯一性**。设 $F=c\cdot D_{\mathrm{KL}}$、$G=d\cdot D_{\mathrm{KL}}$ 为单体函子，$\eta:F\Rightarrow G$ 为单体自然变换，需证存在唯一 $a\ge0$ 使 $\eta_{X}=a\cdot\mathrm{id}_{F(X)}$（逐对象恒等的标量倍）。

* *（a）逐对象为加法同态*。单体性给

$$
\eta_{X\times Y}\bigl(F(x)\!+\!F(y)\bigr)
=\eta_{X}(F(x))+\eta_{Y}(F(y)).
$$

取 $Y=\mathbf 1$、$F(\mathbf 1)=0$，得 $\eta_{X}$ 为 $(\mathbb R_{\ge0},+)$ 上的加法同态，且由下半连续性可推为线性：$\eta_{X}(t)=a_{X}\,t$（$a_{X}\ge0$）。

* *（b）自然性使比例常数与对象无关*。对任意 Markov 箭头 $f:X\to Y$，自然性给出

$$
a_{Y}\,F(f)=\eta_{Y}\circ F(f)=G(f)\circ \eta_{X}=a_{X}\,F(f).
$$

选取使 $F(f)\neq0$ 的简单二点分布模型（如 Bernoulli），即得 $a_{X}=a_{Y}$。于是 $a_{X}\equiv a$ 与对象无关。

* *（c）幺元处决定系数*。由单体性

$$
\eta_{\mathbf 1}(0)=0,\qquad \eta_{X\times \mathbf 1}=\eta_{X}+\eta_{\mathbf 1}.
$$

归纳得 $\eta$ 完全由 $a=\eta_{\mathbf 1}'$ 决定；又 $a\ge0$。取 $a=d/c$ 则 $\eta$ 与 $F,G$ 匹配。唯一性显然。 $\square$

---

## 5. 模型化应用

### 5.1 一维 Schrödinger 秩一族

取 $\mathcal H=L^{2}(\mathbb R)$，

$$
H_{0}=-\partial_{x}^{2},\qquad H=H_{0}+\alpha\,\langle\cdot,\phi\rangle\phi,
$$

其中 $\alpha>0$、$|\phi|=1$。令参数 $\alpha=\alpha(x)$ 连续变化。该族满足（S1）–（S4），且 $S(\lambda)-\mathbf 1\in\mathfrak S_{1}$（a.e. $\lambda$）。由 A1 得 $[u_{\bullet}]\in K^{1}(X)$，由 A2 得能量侧绕数等于 $[u_{\bullet}]$ 的度。标准相移计算给出 $\frac{1}{2\pi i}\int \operatorname{tr}(S^{-1}dS)=+1$ 的归一单位，匹配 A3 的 $n=1$。

### 5.2 扭转情形与极化不可全局选择

若极化在底空间 $X$ 上扭转，则应以 $PU(\mathcal H)$-主丛与 Dixmier–Douady 类 $\delta\in H^{3}(X,\mathbb Z)$ 表示，输出从 $K^{1}(X)$ 替换为扭转 $K^{1}_{\delta}(X)$。受限几何与散射通道的构造在局部坐标下不变，粘合由束枢纽决定。

---

## 6. 工程化建议（可复现管线）

**输入**：能量网格 $\{\lambda_{k}\}_{k=0}^{N}$、散射矩阵近似 $S(\lambda_{k})$。

**步骤**：

1. **端点静态连接**：在 $\lambda_{0},\lambda_{N}$ 处引入小弧连接确保环路闭合；
2. **平滑**：对 $\lambda\mapsto S(\lambda)$ 施加固定带宽能量平滑以抑制阈值噪声；
3. **行列式相位与绕数**：计算 $\arg\det S(\lambda_{k})$ 并作去跳跃展开，累加差分近似 $\sum \Delta \arg/2\pi$ 得绕数；
4. **稳健性**：随平滑核宽度、网格密度、端点连接长度微调应保持整数不变；
5. **交叉校验**：并行计算相对 Cayley 侧的有限维截断近似 $\operatorname{wind}\det U(H_{n})U(H_{0,n})^{-1}$ 交叉验证。

**误差记分**：由 §4.2 的 $\mathfrak S_{1}$ 上界与（S3）的局部一致可积，网格误差由 $\sup|S-\mathbf 1|_{\mathfrak S_{1}}$ 与步长控制；平滑误差在 Pushnitski 不变性下同伦不变。

---

## 7. 归一化原型与取向核对

以 §5.1 的秩一原型为归一单位：固定相移 $\delta(\lambda)$ 之号记，使

$$
\det S(\lambda)=e^{-2i\delta(\lambda)},\qquad \xi(\lambda)=\frac{\delta(\lambda)}{\pi}.
$$

端点可积与单调性给

$$
\frac{1}{2\pi i}\int_{0}^{\infty}\operatorname{tr}\bigl(S^{-1}(\lambda)\partial_{\lambda}S(\lambda)\bigr)\,d\lambda
=\frac{1}{\pi}\bigl(\delta(0^{+})-\delta(\infty)\bigr)=+1.
$$

尺度 $a>0$ 不改变 $\mathrm{sgn}(H)$ 与 $K^{1}$ 类；Mellin–Hardy 极化下尺度对应于相位乘子，保持极化分解不变（见附录 C）。

---

## 8. 讨论（边界、风险与相关工作）

* **维度与理想阶**：高维短程散射常仅有 $S(\lambda)-\mathbf 1\in \mathfrak S_{p}$（$p>1$）。可改用修正行列式 $\det_{p}$ 与修正相位，沿 A2 之链路获得 $K^{1}$ 类与唯一性，技术细节与本框架兼容。
* **阈值与共振**：零能阈值可通过有限秩/紧扰动将 0 推离本质谱，再由（C0）传回；或引入修正相位。
* **受限模型的等价**：不同受限理想（紧、$\mathfrak S_{2}$、$\mathfrak S_{1}$）在合理比较拓扑下同伦等价并与 Bott 对齐。
* **谱流与非有界 Fredholm**：亦可在非有界 Fredholm 模型下直接实现谱流=$K^{1}$ 的识别。
* **$\mathbf{FinStat}$ 对照**：唯一性范式在统计/信息论侧展示"公理 + 归一化 $\Rightarrow$ 唯一倍数"的同型逻辑。

---

## 9. 结论

受限几何提供 $K^{1}$ 的几何化分类，散射谱理论提供从算子与能量到 $K^{1}$ 的通道，可表性与 Bott 结构则把"自然性 + 归一化"压缩为整数唯一性。三者在族级层面的拼接，给出一个可移植的"**唯一性工厂**"：在最小可检假设下产出存在、对齐与唯一。工程化流程展示了数值上稳健提取 $K^{1}$ 指标的可行性，并为高维/修正相位与扭转情形的推广提供清晰路线。

---

## 参考文献

1. A. Pressley, G. Segal, *Loop Groups*, Oxford University Press, 1986.
2. G. Segal, G. Wilson, "Loop groups and equations of KdV type", *Publications Mathématiques de l'IHÉS* **61** (1985), 5–65.
3. N. Kuiper, "The homotopy type of the unitary group of Hilbert space", *Topology* **3** (1965), 19–30.
4. A. Hatcher, *Vector Bundles and K-Theory*, 2017.
5. A. Beltiță, T. S. Ratiu, A. M. Tumpach, "The restricted Grassmannian, Banach Lie–Poisson spaces and coadjoint orbits", *Journal of Functional Analysis* **247** (2007), 138–168.
6. J. Phillips, "Self-adjoint Fredholm operators and spectral flow", *Canadian Mathematical Bulletin* **39** (1996), 460–467.
7. A. Pushnitski, "The spectral shift function and the invariance principle", *Journal of Functional Analysis* **183** (2001), 269–320.
8. D. R. Yafaev, *Mathematical Scattering Theory: General Theory*, Springer, 1992.
9. N. A. Azamov, A. L. Carey, P. G. Dodds, F. A. Sukochev, "Operator integrals, spectral shift, and spectral flow", *Canadian Journal of Mathematics* **61** (2009), 241–263.
10. V. V. Peller, "Multiple operator integrals in perturbation theory", *Proceedings of the Steklov Institute of Mathematics* **290** (2015), 209–233.
11. D. Potapov, F. Sukochev, "Operator-Lipschitz functions in Schatten–von Neumann classes", *Acta Mathematica* **207** (2011), 375–389.
12. S. Booss-Bavnbek, M. Lesch, J. Phillips, "Unbounded Fredholm operators and spectral flow", *Canadian Journal of Mathematics* **57** (2005), 225–250.
13. J. C. Baez, T. Fritz, "A Bayesian characterization of relative entropy", *Theory and Applications of Categories* **29** (2014), 421–478.
14. L. Fullwood, "On a 2-Relative Entropy", *Entropy* **24** (2022), 74.
15. R. Wurzbacher, "The restricted Grassmannian, Banach Lie–Poisson spaces and coadjoint orbits", 见于 *Analysis, Geometry and Topology of Elliptic Operators*, World Scientific, 2006.

---

# 附录

## 附录 A：受限主丛、局部切片与去圈识别

**A.1 局部切片与主丛**
对 $W\in \mathrm{Gr}_{\mathrm{res}}$ 取邻域

$$
\mathcal U_{W}=\{T\in \mathcal B(\mathcal H_{+},\mathcal H_{-})\cap\mathfrak S_{2}:\ |T|\ \text{小}\},
$$

映射 $T\mapsto \mathrm{graph}(T)$ 给出坐标。联合作用

$$
U_{\mathrm{res}}\times \mathcal U_{W}\to \mathrm{Gr}_{\mathrm{res}},\quad (U,T)\mapsto U\cdot \mathrm{graph}(T)
$$

局部为纤维丛，稳定子为 $U(\mathcal H_+)\times U(\mathcal H_-)$。因 $U_{\mathrm{res}}$ 为 Hilbert–Lie 群，作用自由适当，投影 $\pi:U_{\mathrm{res}}\to \mathrm{Gr}_{\mathrm{res}}$ 为光滑主丛。

**A.2 稳定子收缩与同伦等价**
Kuiper 定理：$U(\mathcal H_{\pm})$ 在范数拓扑可收缩；其包含到子群（由受限拓扑诱导）为弱等价。主丛纤维同伦平凡，故

$$
U_{\mathrm{res}}\ \simeq\ \mathrm{Gr}_{\mathrm{res}}.
$$

**A.3 $\mathrm{Gr}_{\mathrm{res}}\simeq \mathbb Z\times BU$ 与 $U_{\mathrm{res}}\simeq \Omega U$**
受限 Grassmann 的分支按虚维（Fredholm 指数）分解，每一分支同伦等价于 $BU$，得 $\mathrm{Gr}_{\mathrm{res}}\simeq \mathbb Z\times BU$。配合 Bott 周期性 $\Omega U\simeq \mathbb Z\times BU$ 得 $U_{\mathrm{res}}\simeq \Omega U$ 的 $H$-空间等价。

**A.4 去圈识别**
对良点化 $A_{\infty}$ 空间之弱等价 $f:G\to H$，classifying space 函子 $B$ 保弱等价。取 $G=U_{\mathrm{res}},H=\Omega U$ 得

$$
BU_{\mathrm{res}}\ \simeq\ U.
$$

---

## 附录 B：相对 Cayley 的族级 Schatten 控制

**B.1 分式预解式与迹类估计**
对自伴 $T$，

$$
U(T)=I-2i\,(T+i)^{-1}.
$$

于是

$$
U(H)-U(H_{0})=2i\,(H+i)^{-1}(H-H_{0})(H_{0}+i)^{-1}.
$$

若（S1）–（S2）成立，右端为 $\mathfrak S_{1}$，且

$$
|U(H)-U(H_{0})|_{\mathfrak S_{1}}\le 2\,|(H-H_{0})(H_{0}+i)^{-1}|_{\mathfrak S_{1}}.
$$

**B.2 族连续性与一致常数**
在 $K\subset X$ 紧集上，由（S1）$\sup_{x\in K}|(H_{x}\pm i)^{-1}|<\infty$，（S2）给出

$$
\sup_{x\in K}|U(H_{x})-U(H_{0,x})|_{\mathfrak S_{1}}
\ \le\ 2\,\sup_{x\in K}|(H_{x}-H_{0,x})(H_{0,x}+i)^{-1}|_{\mathfrak S_{1}}.
$$

从而 $x\mapsto u_{x}$ 范数连续。

**B.3 MOI/DOI 提升（可选）**
如需推广到更一般的函数演算，取 $f\in B^{1}_{\infty,1}$（Besov），多算子积分给出

$$
|f(H)-f(H_{0})|_{\mathfrak S_{1}}\lesssim |(H-H_{0})(H_{0}-i)^{-1}|_{\mathfrak S_{1}},
$$

并随族连续。

---

## 附录 C：尺度等变的显式同伦

取 $\varphi_{t}(\lambda)=\frac{\lambda-i/t}{\lambda+i/t}$（$t>0$），定义

$$
u_{t}(x)=\varphi_{t}(H_{x})\,\varphi_{t}(H_{0,x})^{-1}.
$$

利用分式预解式，

$$
u_{t}-I=2it\,(H+i/t)^{-1}(H-H_{0})(H_{0}+i/t)^{-1}\,\varphi_{t}(H_{0})^{-1}.
$$

在（S1）–（S2）下 $(x,t)\mapsto u_{t}(x)$ 于 $X\times(0,\infty)$ 范数连续；并且

$$
[u_{1}]=[U(H)U(H_{0})^{-1}],\qquad [u_{1/a}]=[U(aH)U(aH_{0})^{-1}].
$$

若 $0\notin\sigma_{\mathrm{ess}}(H_{x})$ 与 $0\notin\sigma_{\mathrm{ess}}(H_{0,x})$，或经有限秩扰动将 0 推离本质谱，则 $t\downarrow 0$ 时 $u_{t}$ 同伦至相对 $\mathrm{sgn}$ 构造；由（C0）把有限秩修正传回原族。

---

## 附录 D：能量侧端点闭合与族版不变性

**D.1 环路闭合**
取单调 $h:[0,1]\to[0,\infty]$，$h(0)=0,h(1)=\infty$。在端点以常值段连接：$[-\epsilon,0]\mapsto \mathbf 1$、$[1,1+\epsilon]\mapsto \mathbf 1$。由（S3）局部一致可积与（S4）闭合假设，得连续族环路 $\Gamma_{x}$。

**D.2 选择无关**
两种平滑/截断的差产生在 $U^{(1)}$ 中的可收缩环路；Pushnitski 不变性与 BK 公式使行列式相位之总绕数保持不变，因而 $K^{1}$ 类同伦不变。

---

## 附录 E：秩一 BK 归一化

对 §5.1 模型，散射相移 $\delta(\lambda)$ 单调且
$\lim_{\lambda\to\infty}\delta(\lambda)=0$、$\lim_{\lambda\to 0^{+}}\delta(\lambda)=\pi$。故

$$
\frac{1}{2\pi i}\int_{0}^{\infty}\operatorname{tr}\bigl(S^{-1}\partial_{\lambda}S\bigr)\,d\lambda
=\frac{1}{\pi}\bigl(\delta(0^{+})-\delta(\infty)\bigr)=+1,
$$

作为 $K^{1}(S^{1})$ 的正生成元；与定理 A3 的归一化一致。

---

## 附录 F：唯一性至整数倍的函子论证明（细节）

**F.1 因子化到 $U$**
以 A1 定义的"忘却"函子 $\mathcal U:\mathbf{Scatt}\to \mathrm{Top}_{*}$ 将 $(H,H_{0})$ 送到基点映射 $u:X\to U^{(1)}\subset U$。设 $\Phi$ 满足（C0）–（C3）。若 $(H,H_{0})$ 与 $(H',H'_{0})$ 在 $\mathbf{Scatt}$ 中经 $(X\times I)$-族连接（保持（S1）–（S4）的一致性），则由函子性与极限保持有 $\Phi(H,H_{0})=\Phi(H',H'_{0})$。于是 $\Phi$ 只依赖于 $u$ 的同伦类，存在唯一 $H$-空间自映射 $f:U\to U$ 使

$$
\Phi(H,H_{0})=[f\circ u]\in [X,U]\cong K^{1}(X).
$$

**F.2 $H$-映射提升与 Bott 兼容**
由（C2）外直和加性与（C3）尺度等变，$f$ 与 $U$ 的乘法（由块和稳定化诱导）相容，即 $f$ 为 $H$-映射。由定理 B 的去圈识别，存在 $\widetilde f:BU\to BU$ 使 $\Omega\widetilde f\simeq f$。

**F.3 通过 $BU$ 上的特征类确定度数**
$H^{*}(BU;\mathbb Z)=\mathbb Z[c_{1},c_{2},\dots]$。$\widetilde f^{*}$ 为环自同态，且由（C2）–（C3）与 Bott 兼容性，必有

$$
\widetilde f^{*}(c_{1})=n\,c_{1}\quad (n\in\mathbb Z),
$$

进而 $\widetilde f^{*}(c_{j})=n^{j}c_{j}$。由 Hurewicz 与 Bott 周期性知 $f$ 在 $\pi_{2j-1}(U)\cong\mathbb Z$ 上作用为乘 $n^{j}$，在 $\widetilde K^{1}(S^{1})\cong\mathbb Z$ 上为乘 $n$。

**F.4 生成元检测与归一化**
取 $X=S^{1}$ 与秩一散射原型（附录 E），有 $\Phi_{\mathrm{can}}$ 取 $+1$。若 $\Phi=n\cdot\Phi_{\mathrm{can}}$，则 $\Phi_{S^{1}}$ 必为乘 $n$；由（C4）得 $n=1$。由（C2）–（C3）与 Bott，乘 $n$ 延拓到任意 $X$。$\square$

**F.5 排除不稳定运算的备注**
Adams 运算 $\psi^{m}$ 在 $K$-理论的奇次 Chern 分量按 $m^{j}$ 缩放；若要求与（C2）外直和与（C3）尺度等变同时兼容且与散射侧的归一化（C4）一致，则唯一可能是 $m=1$，因此不产生新的自然自同态。本定理的"整数倍"已为最一般形态。

---

（全文完）
