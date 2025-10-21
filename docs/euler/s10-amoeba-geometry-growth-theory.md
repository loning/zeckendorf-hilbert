# S10. Amoeba 几何与增长论

**—— Ronkin 凸性、Phragmén–Lindelöf 指标与镜像—几何—信息的一体化**

## 摘要

建立以有限指数和为核心对象的 **amoeba–Ronkin–增长** 统一框架：在尺度空间的 amoeba 外部，Ronkin 势呈现**近似分段仿射**，其方向增长由 **Newton 支持函数**控制；在"平衡骨架"邻域，二项闭合决定弯折与小值分布；在解析层面，与**有限阶 Euler–Maclaurin**和"**极点 = 主尺度**"原则无缝拼接，若需实现关于中心轴 $a$ 的镜像配平（取 $r(s)=r(a-s)$ 且两侧垂线同阶指数衰减），则需具备完成功能方程；在无功能方程时仅可借 $\Gamma/\pi$ 因子改善单侧垂线增长，通常无法保证镜像配平；在数值层面，Nyquist–Poisson–EM 的三分解与 Pretentious 小球控制给出非渐近、可计算的误差与阈值。全文给出可检条件与严格证明要点。

---

## 0. 记号、对象与前置

* **指数和与参数**。设

$$
F(\theta,\rho)=\sum_{j=1}^J c_j\,e^{i\langle\alpha_j,\theta\rangle}\,e^{\langle\beta_j,\rho\rangle},
\qquad \theta\in\mathbb T^m,\ \rho\in\mathbb R^n,
$$

其中 $\alpha_j\in\mathbb R^m,\ \beta_j\in\mathbb R^n,\ c_j\in\mathbb C\setminus\{0\}$，内积取欧氏标准形。记 **Newton 多面体**

$$
\operatorname{New}(F):=\operatorname{conv}\{\beta_1,\dots,\beta_J\}\subset\mathbb R^n,
$$

其**支持函数**

$$
H_{\operatorname{New}(F)}(\mathbf v):=\max_{1\le j\le J}\langle\beta_j,\mathbf v\rangle,\qquad \mathbf v\in\mathbb S^{n-1}.
$$

* **Amoeba 与 Ronkin 势**。定义 **amoeba**

$$
\mathcal A(F):=\bigl\{\rho\in\mathbb R^n:\ \exists\,\theta\in\mathbb T^m,\ F(\theta,\rho)=0\bigr\},
$$

以及 **Ronkin 型势**

$$
N_F(\rho):=\fint_{\mathbb T^m}\log|F(\theta,\rho)|\,d\theta
=\frac{1}{(2\pi)^m}\int_{\mathbb T^m}\log|F(\theta,\rho)|\,d\theta .
$$

零点的对数奇性在紧致环面上可积。为保证 $N_F(\rho)$ 对任意 $\rho$ 有限，作如下对象假设：
（i）$m\ge 1$（$\theta$ 环面非空）；
（ii）对每个相同 $\alpha$ 的分组先行聚合 $\sum_k c_k e^{\langle\beta_k,\rho\rangle}$，并约定不存在某个 $\rho$ 使所有分组系数同时为 0（否则 $F(\cdot,\rho)\equiv 0$ 导致平均为 $-\infty$）。

* **信息势与软最大**。定义

$$
\Lambda(\rho):=\log\Bigl(\sum_{j=1}^J |c_j|e^{\langle\beta_j,\rho\rangle}\Bigr),\qquad
p_j(\rho):=\frac{|c_j|e^{\langle\beta_j,\rho\rangle}}{e^{\Lambda(\rho)}} .
$$

则 $\Lambda$ 凸，且 $\nabla\Lambda(\rho)=\sum_j p_j(\rho)\beta_j,\
\nabla^2\Lambda(\rho)=\operatorname{Cov}_\rho(\beta)\succeq0$。

* **幅度平衡骨架**。对 $j\neq k$ 定义超平面

$$
H_{jk}:=\Bigl\{\rho\in\mathbb R^n:\ \langle\beta_j-\beta_k,\rho\rangle=\log\frac{|c_k|}{|c_j|}\Bigr\},
$$

并以

$$
\delta(\rho):=\min_{j<k}\Bigl|\langle\beta_j-\beta_k,\rho\rangle-\log\tfrac{|c_k|}{|c_j|}\Bigr|
$$

度量 $\rho$ 与平衡骨架的距离（以自然标度计）。

以下关于命题 10.2 至定理 10.5 的讨论均取 $J\ge 2$。若 $J=1$，则 $\delta$ 无需定义且相关结论平凡成立。

* **解析换序纪律**。一切"求和—积分—微分"互换仅在 S1/S4 的管域内使用**有限阶** Euler–Maclaurin（仅有限伯努利层；余项整/全纯），确保亚纯/整函数性与极点结构不受误差层污染。

---

## 1. Ronkin 上界、凸性与近分段仿射

### 定理 10.1（上包与梯度包含）

对一切 $\rho\in\mathbb R^n$，有

$$
N_F(\rho)\ \le\ \Lambda(\rho),\qquad
\partial N_F(\rho)\ \subseteq\ \operatorname{New}(F).
$$

此外，$\rho\mapsto N_F(\rho)$ 为凸且局部 Lipschitz。

**证明要点**。固定 $\rho$，记 $A_j(\theta,\rho):=c_j e^{i\langle\alpha_j,\theta\rangle}e^{\langle\beta_j,\rho\rangle}$。三角不等式给 $|F(\theta,\rho)|\le\sum_j|A_j|=\sum_j|c_j|e^{\langle\beta_j,\rho\rangle}$，取对数并在 $\theta$ 上平均即得 $N_F\le\Lambda$。先证凸性与局部 Lipschitz：固定方向 $\mathbf v$，令 $G_\theta(z):=F(\theta,\rho+z\mathbf v)$。则 $z\mapsto\log|G_\theta(z)|$ 为次调和，其 Riesz 质量（零点计数测度）非负；由一元 Jensen–Poisson 公式知，$t\mapsto N_F(\rho+t\mathbf v)=\fint_{\mathbb T^m}\log|G_\theta(t)|\,d\theta$ 的**分布二阶导**等于上述非负测度在 $\theta$ 上的平均，故为非负测度，遂 $t\mapsto N_F(\rho+t\mathbf v)$ 凸。沿任意直线皆凸 $\Rightarrow$ $N_F$ 在 $\rho$ 上凸，且由凸函数一般理论得局部 Lipschitz。基于已证凸性（割线斜率单调），对任意单位向量 $\mathbf u$，有链式上界
$$
D^{+}N_F(\rho;\mathbf u)
\ \le\ \limsup_{r\to\infty}\frac{N_F(\rho+r\mathbf u)-N_F(\rho)}{r}
\ \le\ \limsup_{r\to\infty}\frac{\sup_{\theta}\log|F(\theta,\rho+r\mathbf u)|}{r}
\ \le\ H_{\operatorname{New}(F)}(\mathbf u),
$$
其中末步由三角不等式与
$\sup_{\theta}\log|F(\theta,\rho+r\mathbf u)|\le \log\sum_j |c_j|e^{\langle\beta_j,\rho+r\mathbf u\rangle}
\le r\,H_{\operatorname{New}(F)}(\mathbf u)+O(1)$ 得到。由引理 A.1（凸分析：方向导数上界 $\Rightarrow$ 次梯度包含）遂得 $\partial N_F(\rho)\subseteq\operatorname{New}(F)$。关于凸性与局部 Lipschitz：固定方向 $\mathbf v$，令 $G_\theta(z):=F(\theta,\rho+z\mathbf v)$。则 $z\mapsto\log|G_\theta(z)|$ 为次调和，其 Riesz 质量（零点计数测度）非负；由一元 Jensen–Poisson 公式知，$t\mapsto N_F(\rho+t\mathbf v)=\fint_{\mathbb T^m}\log|G_\theta(t)|\,d\theta$ 的**分布二阶导**等于上述非负测度在 $\theta$ 上的平均，故为非负测度，遂 $t\mapsto N_F(\rho+t\mathbf v)$ 凸。沿任意直线皆凸 $\Rightarrow$ $N_F$ 在 $\rho$ 上凸，且由凸函数一般理论得局部 Lipschitz。∎
从而由引理 A.1（凸分析：方向导数上界 $\Rightarrow$ 次梯度包含）得 $\partial N_F(\rho)\subseteq\operatorname{New}(F)$。∎

### 命题 10.2（主导子和区：近分段仿射）

若 $\delta(\rho)\ge D>\log(J-1)$，则存在唯一指标 $j_\star$ 使

$$
\Bigl|\,N_F(\rho)-\bigl(\langle\beta_{j_\star},\rho\rangle+\log|c_{j_\star}|\bigr)\Bigr|
\ \le\ \log\frac{1}{1-(J-1)\,e^{-D}} ,
$$

其中右端仅依赖于 $(J,D)$，与 $\{\alpha_j\}$ 无关。

**证明要点**。单项幅度占优：写 $F=A_{j_\star}(1+R)$ 且 $|R(\theta,\rho)|\le\sum_{j\ne j_\star}\frac{|A_j|}{|A_{j_\star}|}\le(J-1)e^{-D}$，从而 $|(J-1)e^{-D}|<1$。由可积对数的标准不等式
$$
\fint_{\mathbb T^m}\bigl|\log|1+R|\bigr|\,d\theta\ \le\ -\log\bigl(1-(J-1)e^{-D}\bigr)
$$
得到所述绝对误差上界。∎

**几何结论**。在 $\mathbb R^n\setminus\mathcal A(F)$ 的每个"深"连通分量中，$N_F$ 以指数精度近似某个仿射函数 $\langle\beta_{j_\star},\rho\rangle+\log|c_{j_\star}|$；靠近骨架 $H_{jk}$ 时出现两项主导驱动的弯折，决定 amoeba 边界的局部形状。

---

## 2. Phragmén–Lindelöf 指标与支持函数

定义**方向增长指标**

$$
h_F(\mathbf v):=\limsup_{r\to\infty}\frac{1}{r}\ \sup_{\theta\in\mathbb T^m}\log\bigl|F(\theta,\rho_0+r\mathbf v)\bigr|,
\qquad \mathbf v\in\mathbb S^{n-1}.
$$

该定义与基点 $\rho_0$ 无关。

### 定理 10.3（PL 上界 = 支持函数上界）

$$
h_F(\mathbf v)\ \le\ H_{\operatorname{New}(F)}(\mathbf v)=\max_{j}\langle\beta_j,\mathbf v\rangle.
$$

**证明**。$|F|\le\sum_j|c_j|e^{\langle\beta_j,\rho_0+r\mathbf v\rangle}$，取 $\log$、$\sup_\theta$、归一化并令 $r\to\infty$。∎

### 定理 10.4（一般方向取等）

若 $\langle\beta_{j_\star},\mathbf v\rangle>\max_{j\ne j_\star}\langle\beta_j,\mathbf v\rangle$，则

$$
h_F(\mathbf v)=\langle\beta_{j_\star},\mathbf v\rangle.
$$

**证明要点**。在该方向上，幅度唯一主导；由命题 10.2 的近分段仿射与 $\sup_\theta$ 的一致性得到下界，与定理 10.3 的上界吻合。∎

**解析接口**。S5 的方向拉普拉斯–Stieltjes 变换极点位置由主尺度指数率给出；定理 10.3–10.4 因而把**几何支持函数**与**解析极点/增长**严格对齐。

---

## 3. Ronkin–信息势比较与变分极限

### 定理 10.5（信息上包与梯度收敛）

对任意 $\rho$，$\Lambda(\rho)-N_F(\rho)\ge0$。若 $\rho_k=\rho_0+r_k\mathbf v$ 且 $r_k\to\infty$，并且方向 $\mathbf v$ 满足定理 10.4 的唯一性，则

$$
\nabla\Lambda(\rho_k)\ \to\ \beta_{j_\star},\qquad
N_F(\rho_k)-\bigl(\langle\beta_{j_\star},\rho_k\rangle+\log|c_{j_\star}|\bigr)\ \to\ 0 .
$$

**证明要点**。第一式即定理 10.1。第二式由命题 10.2 与 $\nabla\Lambda=\sum_j p_j\beta_j$ 得来：主导子和区 $p_{j_\star}\to1$ 且其余 $p_j\to0$。∎

**解释**。$\Lambda$ 是"信息上包"（软最大），$N_F$ 是"相位平均"的真实势；两者之差度量相位相干引起的减幅：在主导子和区差消失，在平衡骨架邻域差增大。

---

## 4. Amoeba 与竖条亚纯—增长的拼接

* **极点 = 主尺度**。沿方向切片 $\rho=\rho_\perp+s\mathbf v$，使用**有限阶** Euler–Maclaurin 进行离散—连续桥接，伯努利层仅贡献整/全纯项，极点集合不变；极点位置与阶由指数–多项式律确定（主尺度指数率决定位置，阶不超过对应多项式次数加一）。

* **完成函数与垂线增长**。若要实现关于中心轴 $a$ 的镜像配平（取 $r(s)=r(a-s)$ 且使两侧垂线同阶指数衰减），则必须具备相应的完成功能方程。反之，在缺少功能方程时，仍可选取适当 $\Gamma/\pi$ 因子改善**单侧**垂线增长，但一般无法保证镜像对称的"配平"。与定理 10.3 的支持函数上界配合，可在竖条内统一 amoeba 外的增长与中心轴的镜像纪律，并与 $L$-函数显式公式接口一致。

---

## 5. 采样、带限与数值可检

* **Nyquist–Poisson–EM 三分解**。将 $\theta$-平均、截断与端点误差分离，得到 $N_F$ 的非渐近误差常数；在主导子和区，分段仿射性改善反演条件数。

* **谱抽取与方向识别**。Prony/矩法可由方向样本恢复 $\beta_{j_\star}$，并与定理 10.4 的方向指标一致；必要时采用多方向联合以克服平台退化。

---

## 6. 边界族与失效机制（带标注）

* **R10.1（多重平衡）**：$\rho$ 接近多条 $H_{jk}$ 的交线时多项近同幅，近分段仿射失效；需回到二项闭合的局部模型。

* **R10.2（无限伯努利层）**：将 EM 当作无穷级数使用会破坏亚纯/整函数性，导致"极点 = 主尺度"与增长估计失真。

* **R10.3（方向退化）**：若存在 $j\ne k$ 使 $\langle\beta_j-\beta_k,\mathbf v\rangle\equiv0$，则 $h_F(\mathbf v)$ 可能出现平台；应改向或多向联合。

* **R10.4（近零复访）**：有限窗内若相位高度 Pretentious，则 $|F|$ 小球事件更频繁，$N_F$ 数值估计更敏感；需配合小球概率上界与窗函数稳健化。

* **R10.5（正规化误用）**：将 $\Gamma/\pi$ 正规化混入系数 $c_j$ 会破坏 $\Lambda$ 与 $N_F$ 的比较；正规化仅作为全局乘子用于镜像/增长配平。

---

## 7. 统一"可检清单"（最小充分）

1. **几何骨架**：计算 $H_{jk}$ 与 $\delta(\rho)$，判定是否处于主导子和区（$\delta>\log(J-1)$）。
2. **信息上界**：用 $\Lambda,\ \nabla\Lambda,\ \nabla^2\Lambda\succeq0$ 评估上包与方向方差。
3. **Ronkin 比较**：$N_F\le\Lambda$；在主导子和区用命题 10.2 得近仿射及偏差界。
4. **PL 指标**：用定理 10.3–10.4 评估 $h_F(\mathbf v)$，并与方向极点位置核对一致。
5. **亚纯—增长纪律**：离散—连续互换仅用**有限阶** EM；若需镜像配平（$r(s)=r(a-s)$ 与两侧同阶垂线衰减），则需具备完成功能方程；否则仅作单侧增长调节，通常不保证镜像配平。
6. **数值稳健**：按 Nyquist–Poisson–EM 设定步长与窗函数；检测到 Pretentious 行为时以小球/复访上界校正阈值。

---

## 8. 与相关篇章的结构接口

* **零集几何（S2）**：$\mathcal A(F)$ 的尺度投影与 $H_{jk}$ 骨架一致，Ronkin 弯折位置对应二项闭合的横截。
* **自反核与完成函数（S3）**：当对象具备完成功能方程时，$\Gamma/\pi$ 正规化可提供镜像配平与垂线衰减的统一控制。
* **有限阶 EM（S4）**：保证换序合法并落实"极点 = 主尺度"。
* **方向亚纯化（S5）**：方向指标与极点位置/阶一致；主导子和 $\Rightarrow$ 单极点主控。
* **信息刻度（S6）**：$\Lambda$ 的梯度/协方差给出"质心—方差—软最大"的信息几何解释，控制上包与灵敏度。
* **$L$-函数接口（S7）**：显式公式的核窗可对准 amoeba 骨架的尺度带，竖条增长由 PL 指标协同控制。
* **离散一致逼近（S8）**：三分解为 $N_F$ 与方向指标的数值评估提供非渐近误差。
* **Pretentious/指数和（S9）**：Pretentious 区的小值复访与 $\Lambda-N_F$ 的增大相一致。

---

## 结语

以 **amoeba–Ronkin–增长** 为主线，完成了"几何骨架 ($H_{jk}$) — 信息上包 ($\Lambda$) — 解析增长（PL/极点）"的统一缝合：**远离平衡骨架**，$N_F$ 以指数精度近仿射，方向增长等于支持函数；**靠近骨架**，二项闭合决定弯折与小值；**在竖条解析层面**，有限阶 EM 与方向亚纯化保障"极点 = 主尺度"，完成函数提供镜像/增长配平；**数值层面**，Nyquist–Poisson–EM 与 Pretentious 小球控制给出非渐近、可复现实验的误差与阈值。由此，S10 将 S2–S9 的结构成果汇聚为**几何—增长—镜像**的一体化基线。

---

## 附录 A：技术引理（可检版）

### 引理 A.1（凸分析：方向导数上界 $\Rightarrow$ 次梯度包含）

设 $f: \mathbb R^n\to\mathbb R$ 凸，$K\subset\mathbb R^n$ 为非空闭凸集，$H_K$ 为其支持函数。若对点 $x$ 与一切单位向量 $u$ 有
$$
D^{+}f(x;u)\ :=\ \limsup_{t\downarrow0}\frac{f(x+tu)-f(x)}{t}\ \le\ H_K(u),
$$
则 $\partial f(x)\subseteq K$。

（证要）取任一 $g\in\partial f(x)$。由次梯度定义，$D^{+}f(x;u)\ge \langle g,u\rangle$ 对一切单位 $u$ 成立。若 $g\notin K$，则存在 $u$ 使 $\langle g,u\rangle>H_K(u)$（支持函数的分离性质），与 $D^{+}f(x;u)\le H_K(u)$ 矛盾。故必有 $g\in K$。∎
