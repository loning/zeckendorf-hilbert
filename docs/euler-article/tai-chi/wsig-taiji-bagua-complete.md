# 太极—八卦的相位—密度—信息几何解释（WSIG 版）

**纲要**：以母映射 $F(\theta,\rho)$、镜像完成函数与信息势 $\Lambda$ 为骨架，把"太极—两仪—四象—八卦"编码为**镜像对称 + 幅度骨架 + 凸信息几何**的可检结构；"爻变"对应沿方向切片穿越幅度平衡超平面；"动静"对应**相位导数/谱密度**的阈值。全文仅用公认判据与可检定理（引文见文内标注）。

---

## 0. 记号与底座

1. **母映射**（相位—尺度统一）

$$
F(\theta,\rho)=\sum_{j=1}^J c_j\,e^{i\langle\alpha_j,\theta\rangle}\,e^{\langle\beta_j,\rho\rangle},\qquad
\theta\in\mathbb R^m,\ \rho\in\mathbb R^n .
$$

作为统一模板，随文使用方向切片 $\rho=\rho_\perp+s\mathbf v$ 及其解析范式。

2. **信息势/软最大**

$$
\Lambda(\rho)=\log\!\Bigl(\sum_{j=1}^J w_j e^{\langle\beta_j,\rho\rangle}\Bigr),\qquad
p_j(\rho)=\frac{w_j e^{\langle\beta_j,\rho\rangle}}{e^{\Lambda(\rho)}} .
$$

$\Lambda$ 凸，$\nabla\Lambda=\sum_j p_j\beta_j,\ \nabla^2\Lambda=\operatorname{Cov}_\rho(\beta)\succeq0$。

3. **幅度骨架与超平面**

对 $j\neq k$，幅度平衡超平面

$$
H_{jk}:=\Bigl\{\rho:\ \langle\beta_j-\beta_k,\rho\rangle=\log\frac{|c_k|}{|c_j|}\Bigr\}
$$

把尺度空间分割成主导模态稳定的区域；Ronkin 势 $N_F$ 受支持函数上界控制。

4. **相位—密度刻度（散射/规范系统）**

在酉散射/规范系统正则性下，几乎处处

$$
\varphi'(E)=\pi\,\rho_{\rm rel}(E)\quad(\text{单通道}),\qquad
\frac{1}{2\pi}\operatorname{tr}Q(E)=\xi'(E)=\operatorname{tr}(\rho-\rho_0)(E)\quad(\text{多通道}),
$$

其中 $\rho,\rho_0$ 为（相对）谱密度，$Q=-iS^\dagger S'$。

---

## 1. 太极 = 镜像（阴阳同体）与守恒

**定义 1.1（太极镜像）**

取 $a$-自反核 $K$（$K(x)=x^{-a}K(1/x)$），其 Mellin 变换 $\Phi$ 满足

$$
\Phi(s)=\Phi(a-s).
$$

完成函数 $\Xi(s)=r(s)\Phi(s)$（$r(a-s)=r(s)$）关于 $\Re s=\tfrac a2$ 对称。这把"阴/阳"刻画为**中心轴两侧的镜像对偶**；镜像合抱（乘以 $r$）保留整体能量/垂线增长结构。

**命题 1.2（信息刻度的镜像守恒）**

相位层的酉变换、完成函数正规化以及**有限阶** Euler–Maclaurin（仅伯努利有限层）**都不改变** $\Lambda$ 诱导的刻度概率 $p(\rho)$ 与熵型量 $H,N_{\rm eff},N_2$。这用数学表达"太极不二"：表象变化不动其"刻度"。

---

## 2. 两仪与四象 = 中轴与双超平面分割

**两仪（阴/阳）**：在函数镜像面 $\Re s=\tfrac a2$ 上，$\sigma=\Re s-\tfrac a2$ 的正/负两侧给出"阳/阴"的数学划分；在尺度侧，以一对超平面 $H_{jk}$ 的两侧作"阳/阴"划分，等价地以

$$
\chi_{jk}(\rho):=\operatorname{sgn}\!\Bigl(\langle\beta_j-\beta_k,\rho\rangle-\log\tfrac{|c_k|}{|c_j|}\Bigr)
$$

的符号判定。

**四象**：取两组独立的比较 $(j_1,k_1),(j_2,k_2)$。则由 $\big(\chi_{j_1k_1},\chi_{j_2k_2}\big)\in\{\pm1\}^2$ 把尺度域分成四个稳定象限；在每个象限中主导模态与 $N_F$ 的梯度恒定方向保持一致（$N_F$ 凸且梯度夹在 Newton 多面体内）。

---

## 3. 八卦 = 三爻符号的几何编码

**定义 3.1（卦的三爻编码）**

选取三组相互独立的幅度比较 $(j_r,k_r)$（$r=1,2,3$）。定义三爻向量

$$
y(\rho):=\bigl(y_1(\rho),y_2(\rho),y_3(\rho)\bigr),\qquad
y_r(\rho):=\mathbf 1\!\Bigl\{\langle\beta_{j_r}-\beta_{k_r},\rho\rangle>\log\tfrac{|c_{k_r}|}{|c_{j_r}|}\Bigr\}\in\{0,1\}.
$$

八个二进制三元组 $y\in\{0,1\}^3$ 一一对应"八卦"。$111$ 记为"乾"（三阳爻）、$000$ 为"坤"（三阴爻）；其余六卦按 $y$ 的位序映射即可（本质取决于三组 $H_{jk}$ 的选择与场景对称性）。在一般位置下三条平衡超平面把尺度域分成多块；每块内 $y(\rho)$ 常值，穿越某一 $H_{j_rk_r}$ 即发生一次"变爻"。

**定理 3.2（卦域的稳定与局部解析）**

若母映射在残差参数上满足横截性，则 $\{F=0\}$ 为实解析余维 $2$ 的子流形；在尺度域中由有限条 $H_{jk}$ 组成的骨架使得卦域（$y$ 常值区）局部稳定，边界处的"爻变"由穿越相应 $H_{jk}$ 触发。

---

## 4. 动静与爻变 = 相位导数/谱密度与方向切片

**定义 4.1（动/静刻度）**

在相位—密度词典下，"动"定义为 $\varphi'(E)\neq 0$（局域谱密度非零），"静"定义为阈值点 $\varphi'(E)=0$。多通道时以 $\tfrac{1}{2\pi}\operatorname{tr}Q$ 或 $\operatorname{tr}(\rho-\rho_0)$ 代之。阈值即散射总相位的临界点。

**方向化与爻变**

沿方向切片 $\rho=\rho_\perp+s\mathbf v$（"观测进程"）前行，穿越某 $H_{j_rk_r}$ 时对应爻 $y_r$ 翻转，即"变爻"；在每一段 $s$-区间内，主导模态与 $N_F$ 的梯度保持稳定。

---

## 5. 太极生两仪、两仪生四象、四象生八卦：数学闭环

* **太极生两仪**：镜像中心轴 $\Re s=\tfrac a2$（或一对 $H_{jk}$）给出二分；镜像守恒保证"体一而用二"。
* **两仪生四象**：两组比较的双超平面把尺度域分为四象限（$\pm,\pm$）。
* **四象生八卦**：增加第三组比较得三爻编码的八个区域，每一区域内的主导序与信息刻度（$\nabla\Lambda,\nabla^2\Lambda$）稳定。

---

## 6. 卦的能量刻度与可检：$N_F\le \Lambda$、采样闭合与变分准则

**能量刻度**：Ronkin 势满足 $N_F(\rho)\le \Lambda(\rho)$，且 $\partial N_F(\rho)\subseteq\operatorname{New}(F)$；由此卦域的增长受 $\Lambda$ 的凸几何与支持函数控制。

**读数与误差闭合**：任何可实现的窗化读数可写成

$$
\int w_R(E)\,[h\!\star\!\rho_\star](E)\,dE
$$

并以 **Nyquist–Poisson–Euler–Maclaurin** 三分解非渐近闭合；严格带限 + Nyquist 条件下别名项为 0。

**窗向选择的几何—信息准则**：优化"窗尾 + 别名 + 伯努利层 − $\lambda$灵敏度"的泛函等价于在支持函数与方差律诱导的自然度量下的变分问题（强凸情形可得唯一最优）。这给出"选卦/定向"的最优原则。

---

## 7. 一个极简范式（示例）

取 $J=3$ 个尺度向量 $\beta_1,\beta_2,\beta_3$ 与权 $w_j=|c_j|$。设三组比较 $(1,2),(2,3),(3,1)$。则

$$
y(\rho)=\bigl[\mathbf 1\{\langle\beta_1-\beta_2,\rho\rangle>\log\tfrac{w_2}{w_1}\},\
\mathbf 1\{\langle\beta_2-\beta_3,\rho\rangle>\log\tfrac{w_3}{w_2}\},
\mathbf 1\{\langle\beta_3-\beta_1,\rho\rangle>\log\tfrac{w_1}{w_3}\}\bigr].
$$

按 $y\in\{0,1\}^3$ 对应八卦（约定 $111\!\leftrightarrow\!\text{乾},\ 000\!\leftrightarrow\!\text{坤}$ 等），沿任意方向切片跨越某一平衡面时，相应位翻转为"变爻"。卦域内的增长与灵敏度由 $\Lambda$ 的梯度/协方差给界。

---

## 结语（可检性）

*镜像*（太极）—*骨架*（两仪/四象/八卦）—*读数*（窗化/非渐近误差闭合）三线闭合：

(i) $K(x)=x^{-a}K(1/x)\Rightarrow \Phi(s)=\Phi(a-s)$ 给出**太极镜像**；

(ii) 幅度平衡超平面 $H_{jk}$ 构成**卦域骨架**，$N_F\le\Lambda$ 与凸结构保证区域稳定；

(iii) $\varphi'(E)=\pi\rho_{\rm rel}(E)$、$\tfrac{1}{2\pi}\operatorname{tr}Q=\xi'$ 给出**动静/爻变**的能量刻度；窗化读数以 **Nyquist–Poisson–EM** 纪律**非渐近闭合**。

---

## 8. 先天/后天八卦：三爻 = 三超平面，环序 = Gray-型邻接

**设定**：选三组幅度比较 $(j_r,k_r)$（$r=1,2,3$），其**平衡超平面**

$$
H_{j_rk_r}=\Bigl\{\rho:\ \langle\beta_{j_r}-\beta_{k_r},\rho\rangle=\log\tfrac{|c_{k_r}|}{|c_{j_r}|}\Bigr\}
$$

把尺度域切成最多 $2^3$ 个稳定卦域；每域内三元符号 $y(\rho)=(y_1,y_2,y_3)\in\{0,1\}^3$ 常值（见 §3 定义 3.1）。这些 $H_{jk}$ 构成 amoeba/Ronkin 的**线性骨架**，卦域稳定由 $N_F\le \Lambda$ 及凸增长给出（§6），且仅在穿越某一 $H_{j_rk_r}$ 时发生"变爻"。

**环序（相邻仅一爻变）**：取任意把 $\{0,1\}^3$ 排成**邻接仅一位不同**的环（3-位 Gray 序）的排列 $G$。则把八卦沿圆周按 $G$ 排列，保证任意相邻两卦只跨越一条 $H_{j_rk_r}$，即"相邻一爻变"。先天/后天两种传统排布在本模型中等价于对 $G$ 及三组比较 $(j_r,k_r)$ 做**二面体 $D_8$** 的几何变换（旋转/反射）与位次置换的组合：本质上是同一**三超平面分割**下的不同坐标/命名选择。其局部稳定与增长控制仍由 $N_F\le \Lambda$、$\nabla\Lambda,\nabla^2\Lambda\succeq0$ 给界。

---

## 9. "错—综—互—变"在本体系中的代数化

设三爻比特串自下而上 $y=(y_1,y_2,y_3)$。

* **变卦**：跨越某一 $H_{j_rk_r}$ 则 $y_r\mapsto 1-y_r$。这正是沿方向切片 $\rho=\rho_\perp+s\mathbf v$ 穿越超平面（见 §4）的**一次翻转**。

* **错卦（全反）**：$y\mapsto \bar y$（三位全部取反）。解析侧对应**镜像对合**把尺度符号整体翻转；在 Mellin—de Branges 模型中由酉对合 $J$ 实现 $V_\sigma\mapsto V_{-\sigma},\ U_\tau\mapsto U_{-\tau}$ 的**共轭反演**，与完成功能方程的镜像对称一致。

* **综卦（上下倒置）**：对三位次序作反转 $y=(y_1,y_2,y_3)\mapsto(y_3,y_2,y_1)$。几何上等价于交换"上/下"两组比较的索引次序，是超平面法向的一个置换。

* **互卦（滑窗中间三爻）**：六爻扩展时定义；对 $y^{(6)}=(y_1,\dots,y_6)$ 取 $(y_2,y_3,y_4)$ 与 $(y_3,y_4,y_5)$ 为两组"互"三爻（见 §11）。这一操作对应把方向切片的**观测窗**在尺度线上平移，从而读取重叠的三超平面局部结构（窗化平移与群作用）。

---

## 10. "动—静—吉—凶"的**相位—信息几何**刻度

**动/静判据**（能量侧）：单通道散射 $S(E)=e^{2i\varphi(E)}$，几乎处处

$$
\boxed{\ \varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)\ } ,
$$

多通道 $\tfrac{1}{2\pi}\operatorname{tr}Q(E)=\rho_{\mathrm{rel}}(E)=-\xi'(E)$。故"动"= $\rho_{\mathrm{rel}}(E)$（或 $\varphi'(E)$、$\operatorname{tr}Q$）**显著非零**；"静"= 接近阈值。

**吉/凶的变分刻度**（尺度侧）：定义信息势 $\Lambda(\rho)=\log\sum_j w_j e^{\langle\beta_j,\rho\rangle}$，有

$$
\nabla\Lambda=\sum_j p_j\beta_j,\quad \nabla^2\Lambda=\operatorname{Cov}_\rho(\beta)\succeq0 .
$$

给定决策方向 $\mathbf v$，二阶导 $\frac{d^2}{ds^2}\Lambda(\rho_\perp+s\mathbf v)=\operatorname{Var}_\rho(\langle\beta,\mathbf v\rangle)$ 衡量**方向不确定度/风险**。于是可定义一个**吉度泛函**（例）

$$
\mathcal J(\rho;\mathbf v):=\underbrace{\langle \nabla\Lambda(\rho),\mathbf v\rangle}_{\text{顺势增益}}
-\lambda\underbrace{\mathbf v^\top\nabla^2\Lambda(\rho)\,\mathbf v}_{\text{方向方差}},
$$

$\lambda>0$ 为风险权重；"吉"对应 $\mathcal J>0$ 的方向域，"凶"对应 $\mathcal J<0$。此判据与 §6 的窗化读数配合，可以**可检**。

**窗化读数与误差闭合**：任何可实现观测写作

$$
\mathrm{Obs}=\int w_R(E)\,[h\!\star\!\rho_\star](E)\,dE\ +\ \varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}},
$$

Nyquist 条件 $\Delta<\pi/(\Omega_w+\Omega_h)$ 下别名可**关断**；EM 余项与尾项具显式上界（选带限/近带限窗）。据此把"动/静/吉/凶"的阈值落到**能量窗与带宽**可控的可检读数上。

---

## 11. 由三爻到六爻：64 卦的一般化

**定义（六爻编码）**：取**上三**、**下三**两套比较 $(j_r^\uparrow,k_r^\uparrow)$、$(j_r^\downarrow,k_r^\downarrow)$（$r=1,2,3$），得

$$
y^{(6)}(\rho)=(y_1^\downarrow,y_2^\downarrow,y_3^\downarrow\ |\ y_1^\uparrow,y_2^\uparrow,y_3^\uparrow)\in\{0,1\}^6 .
$$

穿越任一对应超平面时仅有**一位**翻转（"一爻变"）。在一般位置下六超平面把尺度域分成至多 $2^6$ 块稳定**六爻域**；"错/综/互"分别对应**全反**、位序反转、滑窗选取中间三位。其稳定与增长同由 $N_F\le \Lambda$ 与凸结构控制。

**相位—密度闭环**：六爻的"动爻"可用能量侧的**局域相位导数/谱密度峰值**定位（$\varphi'(E)$ 或 $\operatorname{tr}Q$ 在窗内的显著贡献），并以窗化读数方程落地；这把"占"的随机程序替换为**可复现的窗—核—带宽设计问题**（误差账本：alias + EM + tail）。

---

## 12. 卦—象—数—义：统一刻画

* **象（几何）**：卦域的**法向三元组** $(\beta_{j_r}-\beta_{k_r})_{r=1}^3$ 与 $\nabla\Lambda(\rho)$ 的**质心方向**给出"象"的矢量指向与主导模态；其大小 $|\nabla\Lambda|$ 与"势能"相关。

* **数（信息）**：$p(\rho)$、熵 $H(\rho)$、有效模态数 $N_{\rm eff},N_2$ 满足**链式不等式**，度量"多样性/均衡度"。

* **义（变分）**：$\Lambda$ 的 Gibbs 变分式

$$
\Lambda(\rho)=\log W+\sup_{q\in\Delta_J}\{\langle\rho,\mathbb E_q[\beta]\rangle-D(q\mid\pi)\}
$$

把"取义"（取向/抉择）刻画为对期望特征 $\mathbb E_q[\beta]$ 与**相对熵代价**的权衡；$\mathcal J(\rho;\mathbf v)$ 给出局部决策的吉度函数。

---

## 13. 可检清单（八卦/六十四卦版）

1. **建模**：给定母映射 $F$ 的 $(c_j,\beta_j)$，计算 $H_{jk}$ 骨架与 Ronkin/Nyquist 参数（步长、带宽、窗）。
2. **编码**：指定 $(j_r,k_r)$ 三组（或六组）比较，固定 $111\!\leftrightarrow\!\text{乾},000\!\leftrightarrow\!\text{坤}$ 与环序 $G$。
3. **动爻检测**（能量侧）：在给定窗 $(w_R,h)$ 与采样 $\Delta$ 下，读数 $\mathrm{Obs}$ 的主项用 $\rho_\star$（或 $\rho_{\rm rel}$）卷积计算，并记录 $\varphi'$／$\tfrac{1}{2\pi}\operatorname{tr}Q$ 峰值落点；Nyquist 下别名关断，列出 EM/尾项上界。
4. **吉凶评估**（尺度侧）：按 $\mathcal J(\rho;\mathbf v)$ 与 $\nabla^2\Lambda$ 的方向方差筛选"顺势/逆势"方向域；输出不确定度报表。
5. **一致性**：镜像/全反（错卦）由 $J$ 的对合对称实现；完成功能方程与散射酉性在算子层面等价（S15/S17）。

---

### 小结

* **结构对应**：太极 = 完成功能方程的镜像中轴；两仪/四象/八卦 = 三（到六）条**幅度平衡超平面**的二进制符号层级；
* **动力与占断**：爻变 = 穿越某一超平面；"动/静"= 相位导数/谱密度阈值；"吉/凶"= 信息势的**梯度—方差**变分权衡；
* **工程落地**：一切读数皆可在 **Nyquist–Poisson–Euler–Maclaurin** 纪律下**非渐近闭合**，并与 Wigner–Smith/谱移链完全对齐。

---

## 14. 卦辞的"元—亨—利—贞"：由信息势的梯度—方差—对偶构成的四刻度

**定义 14.1（四刻度）** 令信息势 $\Lambda(\rho)=\log\!\sum_j w_j e^{\langle\beta_j,\rho\rangle}$，则

$$
\nabla\Lambda(\rho)=\sum_j p_j(\rho)\beta_j,\qquad
\nabla^2\Lambda(\rho)=\operatorname{Cov}_\rho(\beta)\succeq 0,
$$

并存在 Gibbs 变分与凸对偶 $\Lambda^\ast$（熵型）表示。据此定义四个与卦义对应的刻度：

$$
\begin{aligned}
\text{元}(\rho)&:=|\nabla\Lambda(\rho)| \quad\text{（生发度；势增率范数）},\\
\text{亨}(\rho;\mathbf v)&:=\langle\nabla\Lambda(\rho),\mathbf v\rangle \quad\text{（通达度；沿方向的净增益）},\\
\text{利}(\rho;\mathbf v)&:=\langle\nabla\Lambda(\rho),\mathbf v\rangle-\lambda\,\mathbf v^\top\nabla^2\Lambda(\rho)\mathbf v \quad(\lambda>0),\\
\text{贞}(\rho)&:=\min_{|\mathbf v|=1}\mathbf v^\top\nabla^2\Lambda(\rho)\mathbf v \quad\text{（稳固度；最小曲率）}.
\end{aligned}
$$

其中 $\Lambda$ 的凸性、梯度/协方差结构与 Gibbs 变分—对偶均来自已建理论（$\Lambda$ 凸、梯度为"有效模态质心"、Hessian 为方向方差；$\Lambda^\ast$ 为熵型对偶）。

**解释**：

* "元"大说明处于主导模态明确的"乾"型生发区；"贞"大说明在一切方向上都稳固（少变）。
* "亨/利"为决策方向 $\mathbf v$ 的局部可行度与风险折减（$\nabla^2\Lambda$ 惩罚方向不确定度），与前文的吉凶变分判据一致。

---

## 15. 从"卦位"到"卦辞"：由骨架距离与方向风险生成语义标签

**定义 15.1（三爻置信/强度）**：对三组比较 $(j_r,k_r)$ 的平衡超平面

$$
H_{j_rk_r}=\{\rho:\ \langle\beta_{j_r}-\beta_{k_r},\rho\rangle=\log\tfrac{|c_{k_r}|}{|c_{j_r}|}\},
$$

记有符号距离

$$
d_r(\rho):=\langle\beta_{j_r}-\beta_{k_r},\rho\rangle-\log\tfrac{|c_{k_r}|}{|c_{j_r}|} .
$$

定义爻置信度 $\eta_r(\rho):=\tanh(\kappa\,d_r(\rho))\in(-1,1)$（$\kappa>0$ 为刻度系数）。三元符号 $y_r=\mathbf 1\{d_r>0\}$ 给出"阴/阳"，$|\eta_r|$ 给出"轻/重"。平衡骨架与 $\Lambda$ 的凸结构保证该标度的数值稳定与几何可测。

**命题 15.2（卦辞打分原型）**：选方向 $\mathbf v$。以

$$
\mathcal S_{\text{卦}}(\rho;\mathbf v)
:=\underbrace{\sum_{r=1}^3 \omega_r\,\eta_r(\rho)}_{\text{结构项}}
+\underbrace{\big(\langle\nabla\Lambda(\rho),\mathbf v\rangle
-\lambda\,\mathbf v^\top\nabla^2\Lambda(\rho)\mathbf v\big)}_{\text{吉度项}}
$$

生成简化"卦辞分值"。当 $\delta(\rho)=\min_{j<k}|d_{jk}(\rho)|$ 较大（远离骨架）时，$\mathcal S_{\text{卦}}$ 受主导模态控制且稳定；$\delta$ 小时提示"临界/当慎"，对应传统"屯、否"等语境。

---

## 16. "本卦—之卦—互卦—错卦—综卦"的统一算子

在六爻编码 $y^{(6)}=(y_1^\downarrow,y_2^\downarrow,y_3^\downarrow\ |\ y_1^\uparrow,y_2^\uparrow,y_3^\uparrow)$ 下：

* **本卦**：点 $\rho$ 的即时符号。
* **之卦**：沿切片 $\rho(s)=\rho_\perp+s\mathbf v$ 首次穿越某一 $H_{j_rk_r}$ 的翻转 $y_r\mapsto1-y_r$。方向切片的横截性保证"一次一爻变"。
* **互卦**：滑窗取中三爻 $(y_2,y_3,y_4)$、$(y_3,y_4,y_5)$，对应在尺度线上平移观测窗。
* **错卦**：三位全反 $y\mapsto\bar y$ = 镜像对合（功能方程与算子镜像对应）。
* **综卦**：位序反转 $(y_1,\dots,y_6)\mapsto(y_6,\dots,y_1)$（上下对置）。

---

## 17. "动—静—动爻定位" = 相位导数/谱密度的窗化读数

**定理 17.1（动爻 = 局域谱密度峰）** 在单通道 $S(E)=e^{2i\varphi(E)}$ 的迹类框架下，几乎处处

$$
\boxed{\ \varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\pi\,\xi'(E)\ },
$$

多通道有 $\tfrac{1}{2\pi}\operatorname{tr}Q(E)=\rho_{\mathrm{rel}}(E)=-\xi'(E)$。故在给定能量窗 $w_R$ 与带限核 $h$ 下的读数

$$
\mathrm{Obs}=\int w_R(E)\,[h\!\star\!\rho_\star](E)\,dE
$$

的主贡献峰即"动爻"的物理落点；误差以 Nyquist–Poisson–EM 三分解闭合（alias/伯努利层/尾项）。

---

## 18. 先天/后天八卦 = 同一三超平面分割下的二面体等价

把 $\{0,1\}^3$ 安排为"相邻仅一位不同"的环（3 位 Gray 序），再施加二面体群 $D_8$ 的旋转/反射与位次置换，即得先天/后天的传统环序差异；几何上对应三条 $H_{j_rk_r}$ 的朝向选择不同而骨架不变。稳定性与增长仍受 $N_F\le\Lambda$ 与"主导子和区"控制。

---

## 19. 最小可复现实验（MRE）：从母映射到卦序列

**输入**：$(c_j,\beta_j)_{j=1}^J$、起点 $\rho_0$、方向 $\mathbf v$、窗/带宽参数 $(w_R,h,\Delta)$。

**步骤**：

1. 计算骨架 $H_{jk}$、$\delta(\rho_0)$、三爻 $y(\rho_0)$。
2. 计算 $\Lambda,\nabla\Lambda,\nabla^2\Lambda$ 与四刻度（元/亨/利/贞）。
3. 能量侧读数：按 Nyquist–Poisson–EM 纪律设置 $\Delta$ 与窗，评估 $\mathrm{Obs}$ 并定位"动爻"峰。
4. 沿 $\rho(s)=\rho_0+s\mathbf v$ 移动，记录首次穿越的 $H_{j_rk_r}$（之卦），并更新六爻序列（互/综/错由算子得到）。
5. 输出：$\{\text{本卦},\text{之卦},\text{互卦},\text{错卦},\text{综卦}\}$ 与四刻度报表、误差账本（alias/EM/尾项）。

**保证**：有限阶 EM 与方向亚纯化确保在移动与窗化下不产生新奇点，极点/零集合仅作可定界的位移（"极点=主尺度"保持）。

---

## 20. 例：三模态母映射的"乾—坤—中介"剖面

令 $J=3$、$\beta_1,\beta_2,\beta_3\in\mathbb R^n$ 一般位置、$w_j=|c_j|$。三组比较 $(1,2),(2,3),(3,1)$。

* **远离骨架**（例如 $\langle\beta_1-\beta_2,\rho\rangle\!\gg\!\log(w_2/w_1)$ 且类似不等式对 1 相对 3 也成立）：则 $p_1\!\to\!1$、$\nabla\Lambda\!\to\!\beta_1$，卦域稳定且 $N_F(\rho)\approx \langle\beta_1,\rho\rangle+\log w_1$（近分段仿射）。对应"乾"象。
* **骨架邻域**：$\delta(\rho)$ 小，$\Lambda-N_F$ 增大（相位相干减幅），提示"临界/当慎"。
* **方向变更**：沿 $\mathbf v$ 穿越某 $H_{jk}$ 即一爻变；在下一段区间"主导子和"切换，四刻度随之重算。

---

## 21. 与"太极（镜像）"的统一本体

选择 $a$-自反核 $K$ 使 $\Phi(s)=\Phi(a-s)$，乘以对称正规化 $r(a-s)=r(s)$ 得完成函数 $\Xi(s)=r(s)\Phi(s)$。这条"镜像中轴"对应"太极不二"，而尺度/离散侧的一切操作（骨架判定、窗化读数、有限阶 EM）都在不破坏镜像—奇性纪律的前提下进行。

---

### 小结（完成闭环）

* **象**：由 $H_{jk}$ 骨架与 $\nabla\Lambda$ 的"质心方向"给出；增长与稳定受 $N_F\le\Lambda$ 控制。
* **数**：$p(\rho)$、$H$、$N_{\rm eff}$、$N_2$ 与 Bregman–KL 恒等式提供信息刻度。
* **义**：$\Lambda$ 的变分—对偶与方向风险准则 $\mathcal J$ 给出吉凶度量。
* **动/静/爻变**：以 $\varphi'=\pi\rho_{\rm rel}$ 与窗化读数定位；误差按 Nyquist–Poisson–EM 非渐近闭合。

---

## 22. 三爻**代码本**与环序（Gray-邻接）及其二面体等价

**代码本**：固定"阳 = 1、阴 = 0"，自下而上记三爻比特串 $y=(y_1,y_2,y_3)\in\{0,1\}^3$。选用一组与传统相容、又便于计算的对齐规范

$$
\text{乾}=111,\ \text{兑}=110,\ \text{离}=101,\ \text{震}=100,\ \text{巽}=011,\ \text{坎}=010,\ \text{艮}=001,\ \text{坤}=000 .
$$

这与"相邻仅一位不同"的三位 Gray-环序兼容（例如 $000\!\to\!001\!\to\!011\!\to\!010\!\to\!110\!\to\!111\!\to\!101\!\to\!100\!\to\!000$）。在本体系里，**先天/后天**仅是对三条平衡超平面 $H_{j_rk_r}$ 的朝向与位次的不同选取；两者在**二面体群** $D_8$ 的旋转/反射与位次置换下同构，几何**骨架**不变（见 §23）。卦域的稳定与增长仍受 $N_F\le\Lambda$ 与凸几何控制。

---

## 23. "象"的向量化：由**法向三元组**与信息势的梯度—方差刻度

令三组比较 $(j_r,k_r)$ 的**平衡超平面**

$$
H_{j_rk_r}=\bigl\{\rho:\ \langle\beta_{j_r}-\beta_{k_r},\rho\rangle=\log\tfrac{|c_{k_r}|}{|c_{j_r}|}\bigr\},
$$

记单位法向

$$
\mathbf n_r:=\frac{\beta_{j_r}-\beta_{k_r}}{|\beta_{j_r}-\beta_{k_r}|},\qquad
d_r(\rho):=\langle\beta_{j_r}-\beta_{k_r},\rho\rangle-\log\tfrac{|c_{k_r}|}{|c_{j_r}|}.
$$

定义**象向量**

$$
\mathbf X(\rho):=\sum_{r=1}^3 \tanh(\kappa\,d_r(\rho))\,\mathbf n_r\quad(\kappa>0),
$$

其方向给出"卦象"的几何指向，幅度刻度由信息势 $\Lambda$ 的梯度—Hessian 补定：$\nabla\Lambda(\rho)=\sum_j p_j(\rho)\beta_j$（质心），$\nabla^2\Lambda(\rho)=\operatorname{Cov}_\rho(\beta)\succeq0$（方向方差/风险）；沿方向切片 $\rho=\rho_\perp+s\mathbf v$ 有 $\frac{d^2}{ds^2}\Lambda=\operatorname{Var}_\rho(\langle\beta,\mathbf v\rangle)\ge0$。因此"象"的强弱可由 $|\nabla\Lambda|$ 与方向方差联合度量。

---

## 24. 变换群与**错—综—互—之**的一致代数

* **之卦**：沿切片 $\rho(s)=\rho_\perp+s\mathbf v$ 首次穿越某 $H_{j_rk_r}$ 则 $y_r\mapsto1-y_r$（"一爻变"，横截性保证一次只翻一位）。
* **错卦**：三位全反 $y\mapsto\bar y$；解析上对应**镜像对合**（完成函数的中心轴对称），不改刻度 $p(\rho)$。
* **综卦**：位序反转（上下倒置），等价于置换三组 $(j_r,k_r)$ 的次序。
* **互卦**：六爻扩展下为"滑窗取中三位"，对应在尺度线上平移观测窗（窗化算子不改"极点 = 主尺度"）。

---

## 25. "动—静—动爻定位"与**窗化读数**（Nyquist–Poisson–EM 三分解闭合）

能量侧（单通道）$S(E)=e^{2i\varphi(E)}$，几乎处处

$$
\boxed{\ \varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)\ } ,
$$

多通道 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=-\xi'(E)$。给定窗 $w_R$ 与带限核 $h$，读数

$$
\mathrm{Obs}=\!\int w_R(E)\,[h\!\star\!\rho_\star](E)\,dE\ +\ \varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}}
$$

在 **严格带限 + Nyquist** 下别名项**关断**；有限阶 EM 仅加整/全纯层，极点保持（"极点 = 主尺度"）。据此把"动爻"定位为窗内 $\rho_{\rm rel}$（或 $\varphi'$、$\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q$）的主峰。

---

## 26. "元—亨—利—贞"的四刻度（变分版，复述对齐）

以 $\Lambda(\rho)=\log\sum_j w_j e^{\langle\beta_j,\rho\rangle}$：

$$
\text{元}:=|\nabla\Lambda|,\
\text{亨}(\mathbf v):=\langle\nabla\Lambda,\mathbf v\rangle,\
\text{利}(\mathbf v):=\langle\nabla\Lambda,\mathbf v\rangle-\lambda\,\mathbf v^\top\nabla^2\Lambda\,\mathbf v,\
\text{贞}:=\min_{|\mathbf v|=1}\mathbf v^\top\nabla^2\Lambda\,\mathbf v .
$$

这里 $\nabla\Lambda$ 与 $\nabla^2\Lambda$ 分别为"质心"与"方向方差/风险"；$\Lambda$ 的 Gibbs 变分与凸对偶确保这些刻度有**熵—对偶**根基，可据此为"吉/凶"给出可检阈值。

---

## 27. **代码—几何—语义**的统一：从比特到象、从象到义

* **比特 $\to$ 几何**：$y(\rho)=(\mathbf 1\{d_r>0\})_{r=1}^3$ 把尺度域分成至多 $2^3$ 个稳定**卦域**；"一爻变"即穿越某 $H_{j_rk_r}$。
* **几何 $\to$ 象**：$\mathbf X(\rho)=\sum_r \tanh(\kappa d_r)\mathbf n_r$ 与 $\nabla\Lambda$ 指向；主导子和区得到"纯象"，骨架邻域呈"杂象/临界"。
* **象 $\to$ 义**：以 $\mathcal J(\rho;\mathbf v)=\langle\nabla\Lambda,\mathbf v\rangle-\lambda\,\mathbf v^\top\nabla^2\Lambda\,\mathbf v$ 定**吉度**；结合 $\delta(\rho)=\min_r|d_r|$（离骨架距离）形成"当行/当止"的可检判据。

---

## 28. **可检清单**（八卦/六十四卦版，复述—聚合）

1. **建模与骨架**：由 $(c_j,\beta_j)$ 计算 $H_{jk}$、$\delta(\rho)$，判定主导子和区；用 $N_F\le\Lambda$ 与支持函数上界控制增长与稳定。
2. **编码与环序**：固定 $111\!\leftrightarrow\!\text{乾},000\!\leftrightarrow\!\text{坤}$，其余按 Gray-邻接与 $D_8$ 变换设定；变换仅改坐标/命名，不改骨架。
3. **动爻检测**：以窗 $w_R$、核 $h$ 与采样步长 $\Delta$ 读数；Nyquist 下别名关断，EM/尾项具显式上界。
4. **义的刻度**：输出 $\{\text{元},\text{亨},\text{利},\text{贞}\}$ 与 $\mathcal J(\rho;\mathbf v)$ 的方向域，附方向方差报表与不等式链 $N_2\le N_{\mathrm{eff}}\le J$。
5. **一致性**：相位层酉变换、完成函数正规化与**有限阶** EM 校正均不改变刻度 $p(\rho)$（"太极不二"）。

---

### 收束

至此，"太极—两仪—四象—八卦"在**母映射—骨架超平面—信息势**框架下闭合：

太极 = 完成功能方程的**镜像中轴**；两仪/四象/八卦 = 三（到六）条**幅度平衡超平面**的二/三元符号层级；爻变 = 穿越超平面；动/静 = 相位导数/谱密度阈值；卦义 = **梯度—方差—对偶**的变分刻度；一切读数在 **Nyquist–Poisson–EM** 纪律下**非渐近闭合**。

---

## 29. 方位定标（后天八卦）与"象向量"的几何锚定

**目标**：把 §23 的"象向量" $\mathbf X(\rho)$ 在 $\mathbb R^2$ 中与**后天八卦**的标准方位做一一锚定，使"卦—象—方位"可校准、可比较。

**后天八卦的方位基准**（据文献）：
$\text{离} \to \text{南},\ \text{坤} \to \text{西南},\ \text{兑} \to \text{西},\ \text{乾} \to \text{西北},\ \text{坎} \to \text{北},\ \text{艮} \to \text{东北},\ \text{震} \to \text{东},\ \text{巽} \to \text{东南}$。据此定义八个单位向量 $u_\gamma$ 依次均分于圆周（或按文献直接取正北/正南/正东/正西及四隅）。

**定义 29.1（SO(2) 定标）** 取旋转 $R\in \mathrm{SO}(2)$ 与尺度 $\kappa>0$。在每个稳定卦域选代表点集 $\mathcal C$，解最小化问题

$$
(R^\star,\kappa^\star)=\arg\min_{R\in \mathrm{SO}(2),\,\kappa>0}\
\sum_{\rho\in\mathcal C}\angle\!\big(R\,\mathbf X_\kappa(\rho)\,,u_{\,\text{卦}(\rho)}\big)^2,
\quad \mathbf X_\kappa(\rho):=\sum_{r=1}^3 \tanh(\kappa\,d_r(\rho))\,\mathbf n_r.
$$

**命题 29.2（唯一性—正交 Procrustes）** 若 $\{\mathbf X_\kappa(\rho):\rho\in\mathcal C\}$ 张成 $\mathbb R^2$，则上式等价为单位向量配准的正交 Procrustes 问题，解 $R^\star$ 唯一（至多差一个整周角），$\kappa^\star$ 由角误差曲线的唯一极小确定。

---

## 30. 五行的"卦聚合"与生克图

文献对应关系（五行 $\leftrightarrow$ 卦）：
$\text{水}\!\leftrightarrow\!\text{坎};\ \text{火}\!\leftrightarrow\!\text{离};\ \text{土}\!\leftrightarrow\!\text{坤},\text{艮};\ \text{木}\!\leftrightarrow\!\text{震},\text{巽};\ \text{金}\!\leftrightarrow\!\text{乾},\text{兑}$。

**定义 30.1（卦的软归属）** 令 $\sigma(x)=1/(1+e^{-x})$，对任一三爻图样 $y\in\{0,1\}^3$ 定

$$
w_y(\rho):=\prod_{r=1}^3 \sigma\!\big(\kappa\,d_r(\rho)\big)^{y_r}\,\big(1-\sigma\!\big(\kappa\,d_r(\rho)\big)\big)^{1-y_r},\quad
\sum_{y} w_y(\rho)=1 .
$$

记 $w_\gamma(\rho)$ 为八卦的软权重（以 $\gamma$ 的三爻比特 $y$ 代入）。

**定义 30.2（五行聚合权重）**

$$
\begin{aligned}
W_{\text{木}}&:=w_{\text{震}}+w_{\text{巽}},\quad
W_{\text{火}}:=w_{\text{离}},\quad
W_{\text{土}}:=w_{\text{坤}}+w_{\text{艮}},\\
W_{\text{金}}&:=w_{\text{乾}}+w_{\text{兑}},\quad
W_{\text{水}}:=w_{\text{坎}},\qquad
\sum_{\chi\in\{\text{木火土金水}\}}W_\chi=1 .
\end{aligned}
$$

**定义 30.3（生/克邻接矩阵）**

生成（相生）有向环 $G$: $\text{木}\to\text{火}\to\text{土}\to\text{金}\to\text{水}\to\text{木}$；

制约（相克）有向环 $K$: $\text{木}\to\text{土}\to\text{水}\to\text{火}\to\text{金}\to\text{木}$。

**定理 30.4（角度驱动的"生"序单调性）**

取 $\theta(\rho):=\arg\big(R^\star \mathbf X(\rho)\big)$。若沿连续轨迹 $\rho(t)$ 使 $\theta(\rho(t))$ 严格单调递增且顺次跨越八卦扇区，则聚合权重的主峰按 $G$ 的顺序完成一周（$\text{木}\to\text{火}\to\text{土}\to\text{金}\to\text{水}\to\text{木}$）。

---

## 31. 季节—方位—五行的一致性校验

文献给出季节刻度：$\text{水}\sim$ 冬、$\text{木}\sim$ 春、$\text{火}\sim$ 夏、$\text{金}\sim$ 秋、$\text{土}\sim$ 中央/长夏或四季之交；并给出后天方位：$\text{离/南},\text{坎/北},\text{震/东},\text{兑/西}$ 等。以 §29 的定标 $R^\star$ 与 $\theta$ 的年相位（顺时针或逆时针）为横轴，则"春$\to$夏$\to$长夏/土$\to$秋$\to$冬"的环路与 $G$ 一致，完成自洽校验。

---

## 32. "吉/凶"与生克冲的变分—网络判据

在 §10 的吉度泛函 $\mathcal J(\rho;\mathbf v)$ 基础上，引入五行网络势：

$$
\mathcal U_G(\rho):=\sum_{\chi}W_\chi(\rho)\,W_{\text{succ}(\chi)}(\rho),\qquad
\mathcal U_K(\rho):=\sum_{\chi}W_\chi(\rho)\,W_{\text{克}(\chi)}(\rho),
$$

其中 $\text{succ}(\chi)$ 沿 $G$ 前驱，$\text{克}(\chi)$ 沿 $K$ 前驱。则

$$
\mathcal S_{\text{五行}}(\rho;\mathbf v):=\mathcal J(\rho;\mathbf v)\ +\ \alpha\,\mathcal U_G(\rho)\ -\ \beta\,\mathcal U_K(\rho)
$$

给出"顺生抑克"的综合打分（$\alpha,\beta>0$）。取 $\mathcal S_{\text{五行}}>0$ 的方向域为"当行"，$<0$ 为"当止"。

---

## 33. 稳健性：对窗化误差与骨架扰动的 Lipschitz 估计

设骨架距离 $\delta(\rho)=\min_r |d_r(\rho)|$。则对任意两点 $\rho,\rho'$：

$$
|w_y(\rho)-w_y(\rho')|\le C(\kappa)\,|\rho-\rho'|,\qquad
|W_\chi(\rho)-W_\chi(\rho')|\le 2C(\kappa)\,|\rho-\rho'| ,
$$

常数 $C(\kappa)$ 由 $\sigma'(\kappa d)=\kappa \sigma(1-\sigma)\le \kappa/4$ 给界；窗化读数误差（alias/EM/尾项）按既定三分解可独立上界，从而 $\mathcal S_{\text{五行}}$ 在远离骨架（$\delta$ 中等）时全程 Lipschitz 控制、阈值稳定。——这保证"卦—五行—吉度"的**可检复现**（与窗、带宽、采样一致）。

---

## 34. 先/后天的等价与太极本体

"先天/后天"只是在**同一几何骨架**上选择不同方位配准与命名（旋转/反射 + 位次置换）：

* 先天（伏羲）：火/水左右对峙、山/泽对峙，象征均衡之态；
* 后天（文王）：$\text{离/南},\text{坎/北},\text{震/东},\text{兑/西}$ 作现实运行与罗盘基准。

二者在本体系由 $R$ 的不同选定统一；其"源头不二"由**太极**（镜像中轴）承担：$\text{易有太极，太极生两仪，两仪生四象，四象生八卦}$。

---

## 35. 最小实现配方（无代码版）

**输入**：$(c_j,\beta_j)$、$\kappa$、采样窗 $(w_R,h,\Delta)$。

**流程**：

1. 计算骨架 $H_{j_rk_r}$、符号距离 $d_r$、三爻软权 $w_y$、卦权 $w_\gamma$、五行权 $W_\chi$。
2. 以代表点集 $\mathcal C$ 求 $R^\star$ 完成后天定标；得到 $\theta(\rho)=\arg(R^\star\mathbf X(\rho))$。
3. 能量侧用窗化读数定位"动爻"（$\varphi'(E)=\pi\rho_{\rm rel}(E)$ 的窗峰），误差按 Nyquist–Poisson–EM 三分解闭合。
4. 输出：$\{$本卦、之卦、互/错/综$\}$ 与 $\{W_\chi\}$ 曲线、$\mathcal S_{\text{五行}}(\rho;\mathbf v)$ 等方向域。
   （季节/方位校验：$\theta$ 的年相位与"春$\to$夏$\to$长夏$\to$秋$\to$冬"一致性。）

---

## 36. 六爻"动爻"与择时/择向：由相位—密度阈值到可实施算法

**36.1 动爻的光谱判据（再述—工程化）**

单/多通道散射在几乎处处能量点满足

$$
\varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E),\qquad
\frac{1}{2\pi}\operatorname{tr}Q(E)=\rho_{\mathrm{rel}}(E),
$$

故"动爻"可由给定能量窗 $w_R$ 与带限前端核 $h$ 的窗化读数主峰定位；阈值点由 $\varphi'(E)=0$（或 $\rho_{\mathrm{rel}}(E)=0$）给出。该等价链与阈值/稳定性判据见 S21（相位导数 = 谱密度）与 CCS/WSIG-QM 的统一式。

**36.2 窗化读数与误差三分解**

实际读数

$$
\mathrm{Obs}=\int w_R(E)\,[h\!\star\!\rho_\star](E)\,dE
$$

以**别名（Poisson）+ 伯努利层（有限阶 EM）+ 截断**三项**非渐近闭合**；**带限 + Nyquist**下别名项为 0。

**36.3 动爻—择时/择向算法（最小实现）**

输入：$(c_j,\beta_j)$、初始 $\rho_0$、方向 $\mathbf v$、窗/带宽 $(w_R,h)$、采样 $\Delta$。

1. **骨架**：计算 $H_{jk}$、$\delta(\rho)$ 与三爻 $y(\rho)$；$\delta$ 小提示临界/当慎。
2. **吉度**：按 $\mathcal J(\rho;\mathbf v)=\langle\nabla\Lambda,\mathbf v\rangle-\lambda\,\mathbf v^\top\nabla^2\Lambda\,\mathbf v$ 得方向域；$\Lambda$ 的梯度/协方差给出"质心—方差"刻度。
3. **读数**：在 Nyquist 纪律下采样 $F(E)=w_R(E)[h\!\star\!\rho_\star](E)$；$\mathrm{Obs}$ 的主峰给出动爻能量；EM 余项与尾项记账。
4. **爻变**：沿 $\rho=\rho_\perp+s\mathbf v$ 前进，当穿越某 $H_{jk}$ 时翻转相应爻位，输出"本卦→之卦"。
5. **择时/择向**：在候选 $s$ 或方位角集上最大化 $\mathcal S_{\text{五行}}=\mathcal J+\alpha\mathcal U_G-\beta\mathcal U_K$；满足 Nyquist 的方案优先。

---

## 37. 干支—纳甲的"相位—尺度"坐标化（可选层）

把**节气/时辰**映为相位 $U_\tau: f(x)\mapsto x^{i\tau}f(x)$，把**地理坐标/方位**映为尺度 $V_\sigma: f(x)\mapsto e^{\sigma a/2}f(e^\sigma x)$。二者满足 Weyl 关系

$$
V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma,
$$

在对数模型与 $L^2(\mathbb R)$ 的"平移—调制"完全等价。故择时/择向本质是相位—尺度的**共轭选取**与最优窗读数。

---

## 38. 纳入"多窗—多核"的稳健化：Wexler–Raz 与 Parseval 结构

当单窗下临界密度/别名限制导致不稳时，用 $K$ 个带限偶窗 $\{w^{(\ell)}\}$ 形成多窗帧：

$$
\frac{1}{\Delta}\sum_{\ell=1}^K\big|\widehat w^{(\ell)}(\xi)\big|^2\equiv 1\quad\text{(Parseval/tight 条件, Nyquist 下)}.
$$

该条件与**Wexler–Raz 双正交**等价，保证稳定重构与抗扰动；非平稳（分块）情形以 Calderón 和对角化实现同样的 tight/dual。

---

## 39. "纳音—五行—卦义"的度量化回收

在 §30 的五行聚合 $W_\chi$ 之上，以**信息势**与**方差律**定义四刻度"元—亨—利—贞"，并加上网络势 $\mathcal U_G,\mathcal U_K$ 得综合打分 $\mathcal S_{\text{五行}}$。其稳定性来自：

(i) **骨架几何**：$H_{jk}$ 与 $\delta(\rho)$ 控制卦域稳定与临界区；$N_F\le \Lambda$ 给出能量上包。

(ii) **采样与误差**：Nyquist–Poisson–EM 的三分解闭合。

---

## 40. "文辞生成"的规则骨架（草案）

在每个稳定卦域，取

$$
\mathbf X(\rho)=\sum_r \tanh(\kappa d_r(\rho))\,\mathbf n_r,\quad
(\nabla\Lambda,\nabla^2\Lambda)
$$

得到"象向量—势增率—方向方差"三元组；以阈值表将其映射为"通/止、谦/进、守/攻"等词汇槽位；临界区（$\delta$ 小）自动插入"当慎/无咎"的语义片段。数学上其规则均由 $H_{jk}$、$\Lambda$ 的凸结构与方向方差律生成。

---

## 41. 纳入历法/方位的**择日—择向**范式（工程可检）

**41.1 相位—尺度对：** 将**节气/时段**映为 $\tau$ 网格、**方位/经纬**映为 $\sigma$ 网格；用 WH-帧（均匀或分块）在 $(\tau,\sigma)$ 平面上构造 Parseval 采样系。

**41.2 指标：** 以 $\mathcal S_{\text{五行}}$（§39）或"元/亨/利/贞"四刻度做目标；动爻由 $\varphi'(E)$ 的峰/零判别。

**41.3 误差账本：** 设 $\widehat w_R,\widehat h$ 带限并取 $\Delta\le\pi/(\Omega_w+\Omega_h)$；别名 = 0，EM 余项按 $2M$ 阶上界计入，截断尾项按窗外 $L^1$ 能量估。

---

## 42. 与"太极镜像"的一致性

太极的"**镜像不二**"在数学上由**自反核—完成函数**实现：$K(x)=x^{-a}K(1/x)\Rightarrow \Phi(s)=\Phi(a-s)$，完成函数 $\Xi(s)=r(s)\Phi(s)$ 关于中心轴对称。整个卦域—骨架—读数的变换在该镜像与**有限阶 EM**纪律下不改变奇性集合与刻度概率。

---

## 43. 快速**最小可复现实验（MRE）**配方（整合）

1. **数据与窗**：设 $J\ge2$，给 $(c_j,\beta_j)$、窗 $w_R\in\mathrm{PW}$、带限核 $h\in W^{2M,1}$。
2. **骨架—卦**：求 $H_{jk}$、$\delta$ 与 $y(\rho)$；"本卦→之卦"沿 $\rho_\perp+s\mathbf v$ 的首次超平面穿越。
3. **读数—动爻**：Nyquist 采样 $F(E)=w_R[h\!\star\!\rho_\star]$，峰/零定位动/静爻；误差三分解并记录。
4. **择时—择向**：在 $(\tau,\sigma)$ WH-格上（或其分块非平稳版本）搜索 $\max \mathcal S_{\text{五行}}$，多窗 Parseval 以保证稳定。
5. **报告**：输出〔本卦/之卦/互/错/综〕、动爻列表、四刻度与 $\mathcal S_{\text{五行}}$ 热图、误差账本（alias/EM/tail）。

---

## 44. 可检清单（增补）

* **几何—信息**：$N_F\le \Lambda$；$\nabla\Lambda=\sum_j p_j\beta_j$、$\nabla^2\Lambda=\operatorname{Cov}(\beta)\succeq0$。
* **骨架**：$H_{jk}$ 与 $\delta(\rho)$；主导子和区与临界区识别。
* **相位刻度**：$\varphi'=\pi\rho$（单通道）/ $\tfrac{1}{2\pi}\operatorname{tr}Q=\rho_{\mathrm{rel}}$（多通道迹）。
* **采样—误差**：Poisson + EM + 尾项闭合；Nyquist 条件消别名。
* **多窗稳健**：Parseval 条件 $\frac{1}{\Delta}\sum_\ell|\widehat w^{(\ell)}|^2\equiv1$；WR 双正交。

---

### 小结

至此，"太极—两仪—四象—八卦"已与**相位—密度—信息几何**严格闭合：

镜像（太极）由自反核/完成函数刻画；两仪/四象/八卦为幅度平衡超平面的符号层级；"动/静/爻变"由 $\varphi'/\rho$ 与骨架穿越给定；择时/择向在 WH-格与多窗 Parseval 下落地，误差按 Nyquist–Poisson–EM 非渐近闭合。上述每步均可复核其判据与上界。

---

## 45. 纳甲：把干支映成**相位—尺度**（$U_\tau$–$V_\sigma$）坐标

**原则**：以 Weyl–Heisenberg 酉表示把"时间（节气/日时）"当作**相位平移** $U_\tau$、把"方位/尺度（地理朝向/空间尺度）"当作**尺度伸缩** $V_\sigma$。

$$
(U_\tau f)(x)=x^{i\tau}f(x),\qquad (V_\sigma f)(x)=e^{\frac{a\sigma}{2}}f(e^\sigma x),\qquad
V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma .
$$

干支对 $(g,z)\in\{\text{天干}\}\times\{\text{地支}\}$ 给定**历法相位** $\tau(g,z)$ 与**地理/罗盘尺度** $\sigma(g,z)$，则"甲子"等价于某一 $(\tau_\ast,\sigma_\ast)$ 基准，六十花甲子为 $(\tau,\sigma)$ 的**离散轨道**。测量时把 $(\tau,\sigma)$ 注入窗口化读数（§48），即得到"纳甲起卦"的**谱读数版**实现。

**要点**：$U_\tau$ 与 $V_\sigma$ 的**Weyl 关系**保证"时—位联动"的**相位因子** $e^{i\tau\sigma}$ 正确叠加；任何"择时/择向"的纳甲策略，都被编码为对 $\tau,\sigma$ 网格上的窗 $w_R$ 与核 $h$ 的选取（Nyquist 纪律与误差账本见 §48）。

---

## 46. 六爻纳甲与"卦—干支—尺度"统一表述

把六爻比特串 $y^{(6)}=(y_1,\dots,y_6)\in\{0,1\}^6$（阳=1、阴=0，自下而上）映到三组超平面比较（§3、§11）上：每一爻由某一对 $(j_r,k_r)$ 的**幅度超平面** $H_{j_rk_r}$ 的一侧决定；**纳甲**即为这些超平面的**参照系**选择（$(\tau,\sigma)$ 的函数）。

在**母映射—Ronkin 势**框架里，六爻来自三对法向 $\mathbf n_r$ 与阈值 $\log\frac{|c_{k_r}|}{|c_{j_r}|}$ 的联合判定；纳甲只改变这些阈值/法向的基准（相当于旋转/平移），不改变"卦域骨架"的几何。

**结论**：

* 传统"纳甲歌诀"是在本模型中对 $(\tau,\sigma)$ 的一个**固定坐标规范**；
* 任何合规的纳甲法，都可转写成**同一**超平面骨架下不同的 $(\tau,\sigma)\to(H_{jk})$ 标定——**卦不变，标尺变**。

---

## 47. 64 卦的图结构与 Ihara ζ：从 $Q_6$ 超立方到"非回溯谱"

把 64 卦视为六位 Gray 码的顶点，**一爻变**即 Hamming 距 1 的邻接，得到超立方图 $Q_6$。
进一步用**非回溯算子** $B$ 与 Ihara ζ（图版）刻画"不断爻的循环结构"与"多步爻变的计数"；其行列式公式与完成多项式给出**镜像** $s\mapsto 1-s$ 的离散版本。
这使得"卦序——卦变——循环（运）"三者能以**谱邻接—非回溯谱**统一度量，并与我们的**窗化迹**/试验核（§48）同一实现。

---

## 48. 起卦—占断的**最小实现（II）**：多窗稳健 + Nyquist–Poisson–EM

**输入**：母映射参数 $(c_j,\beta_j)$、起点 $\rho_0$、方向 $\mathbf v$、历法—方位 $(\tau,\sigma)$、窗/核/步长 $(w_R,h,\Delta)$。

**流程（稳健版）**：

1. **骨架—六爻**：算 $H_{jk}$、$\delta(\rho_0)$ 与 $y^{(6)}$（§3、§11）。
2. **动爻定位**：读数
   $\displaystyle \mathrm{Obs}=\int w_R(E)\,[h\!\star\!\rho_\star](E)\,dE+\varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}}$，
   其中 $\rho_\star\in\{\rho_m,\rho_{\rm rel}\}$，且
   $\displaystyle \frac{1}{2\pi}\operatorname{tr}Q(E)=\rho_{\rm rel}(E)=-\xi'(E)$（多通道取迹）。Nyquist 取 $\Delta\le \pi/(\Omega_w+\Omega_h)\Rightarrow \varepsilon_{\text{alias}}=0$。
3. **多窗稳健**：用带限偶窗族 $W=\{w^{(\ell)}\}_{\ell=1}^K$ 形成 Parseval/tight 框架（或其非平稳版），由 Wexler–Raz 条件保证稳定重构与抗扰。
4. **窗/核优化**：以三分解误差上界为目标，解带限投影的 KKT 条件（强凸/稀疏两范式均可）；在 Nyquist 约束下最优窗**不引入新奇性**（保持"极点=主尺度"）。
5. **之/互/错/综**：沿 $\rho=\rho_\perp+s\mathbf v$ 前进，首过某 $H_{jk}$ 即一爻变（之卦）；滑窗取中三爻（互卦）；全反/倒置（错/综）为位运算—算子变换（§16）。
6. **吉凶—方略**：以 $\mathcal J(\rho;\mathbf v)=\langle\nabla\Lambda,\mathbf v\rangle-\lambda\,\mathbf v^\top\nabla^2\Lambda\,\mathbf v$ 与"元—亨—利—贞"四刻度输出决策域；相对谱密度取 $\rho_{\rm rel}$；需非负主项时取 $\rho_m$。

---

## 49. 《彖》《象》《文言》的**生成语法**（信息几何版）

* **元**：$|\nabla\Lambda|$（势增率范数）大 ⇒ 生发；
* **亨**：$\langle\nabla\Lambda,\mathbf v\rangle$（沿方向净增益）顺；
* **利**：$\langle\nabla\Lambda,\mathbf v\rangle-\lambda\,\mathbf v^\top\nabla^2\Lambda\,\mathbf v$ 正 ⇒ 可行（风险扣除后为正）；
* **贞**：$\min_{|\mathbf v|=1}\mathbf v^\top\nabla^2\Lambda\,\mathbf v$（最小曲率）高 ⇒ 稳固。

以以上四刻度为槽位，结合"骨架距离" $\delta(\rho)$（临界则"当慎/无咎"）与"动爻峰"位置，填入《彖》《象》模板短语即可生成"卦辞—爻辞"的**规则文本**。语义与**KL/Bregman** 的"最近信息投影（I-投影）"一致（softmax $\leftrightarrow$ 对数势 $\Lambda$），并与"Born=最小KL""指针=光谱极小"三位一体定理闭合。

---

## 50. 标定与可检实验（Field Calibration）

**目的**：把"后天方位—季节—五行"的传统标尺，校准为 $(\tau,\sigma)\mapsto(H_{jk})$ 的**几何锚定**（§29–§31），并验证读数—卦—五行的**一致性**。

**方案**：

1. 选一套带限偶窗 $W$ 与核 $h$，以 Nyquist 步长采样能量轴（别名=0）；构造 Parseval/tight 多窗以提高稳健度。
2. 在一组代表点 $\mathcal C$ 上求"象向量"与后天方位的 Procrustes 配准（§29），得到 $(R^\star,\kappa^\star)$；检验季节环与相生环的一致性（§31–§32）。
3. 用"窗化 Birman–Kreĭn 恒等式"检查"相位增量 = 窗化谱差"的数值一致（离散化误差按三分解闭合）。
4. 在不同 $(\tau,\sigma)$ 网格上重复，验证"纳甲规范改变≠卦骨架改变"的**不变性**；必要时用镜像核/完成函数模板（自反核 $K$ 与 $\Phi(s)=\Phi(a-s)$）校核"太极镜像"保持。

---

### 小结（本节新增收束）

* **纳甲**在本体系中是给 $(\tau,\sigma)$ 设定参照，从而改变**标尺**而不改**骨架**；
* 64 卦的**图—谱**可用非回溯算子与 Ihara ζ 统一描述，和**窗化迹**一并进入**非渐近**可检框架；
* **占**以"多窗稳健 + Nyquist–Poisson–EM"实现，**正则化**由窗/核变分最优给出；
* **卦辞生成**以 $\Lambda$ 的**梯度—方差—对偶**为槽位，与"Born=KL、Pointer=极小"闭合。

---

## 51. 个体化母映射与**卦骨架**的可识别性（参数估计）

**数据模型**：观测一簇尺度点 $\{\rho_q\}_{q=1}^N$ 及其由骨架判据诱导的三/六爻标签（或软权）$y_q\in\{0,1\}^3$ / $y_q^{(6)}$。令母映射的信息势 $\Lambda(\rho)=\log\sum_{j=1}^J w_j e^{\langle \beta_j,\rho\rangle}$，其中 $w_j=|c_j|>0$。把"阳/阴"视作三条超平面比较的**物流回归**（softmax）层：

$$
\mathbb P_\theta[y_r=1\mid \rho]\;=\;\sigma\!\big(\kappa(\langle\beta_{j_r}-\beta_{k_r},\rho\rangle-\delta_r)\big),\quad
\delta_r:=\log\tfrac{w_{k_r}}{w_{j_r}} .
$$

极大似然 $\hat\theta=(\{\beta\},\{\delta\},\kappa)$ 或等价的 Bregman 最小化给出估计。

**不变性**：对任意常数 $\lambda>0$ 与向量平移 $\rho\mapsto\rho+\rho_0$，骨架方程
$\langle\beta_{j}-\beta_{k},\rho\rangle=\log\tfrac{w_k}{w_j}$
保持为同一族超平面（仅常数项整体平移），而"爻"仅依赖于这些超平面与方向切片的**相对位置**。故**卦骨架可识别到仿射规范**（整体幅度与原点的选择不可唯一）。

**一致性要点**：在一般位置与正则条件下（特征矩阵满秩、超平面横截），软最大似然是一致的；其 Fisher 信息与 $\nabla^2\Lambda=\operatorname{Cov}_\rho(\beta)\succeq0$ 对齐，提供不确定度报告（方向方差 = "风险"）。

---

## 52. 统计学习保证：样本复杂度与稳健阈值

把三爻判别看作三个线性函数符号的联合（每个是线性分隔器），VC 维度为 $O(n)$。对误差容忍 $\varepsilon$ 与置信 $1-\delta$，需要样本量 $N=\tilde O\big(\tfrac{n+\log(1/\delta)}{\varepsilon^2}\big)$ 以保证骨架重构的泛化误差；软判别阈值可取 $|d_r(\rho)|>\tau$（$\tau$ 由验证集调节），与 §33 的 Lipschitz 估计拼合，给出"临界/当慎"的稳定区间。

---

## 53. 读数层的多窗 Parseval 稳健化与 WR 恒等式

以若干带限偶窗 $W=\{w^{(\ell)}\}_{\ell=1}^K$ 组成 WH/Gabor 多窗帧，满足 Parseval 条件

$$
\frac{1}{\Delta}\sum_{\ell=1}^K\big|\widehat{w}^{(\ell)}(\xi)\big|^2\equiv 1,
$$

则窗化读数在 Nyquist 取样下稳定重构；其与 **Wexler–Raz** 双正交条件等价（或由 Janssen/Daubechies–Landau–Landau/Ron–Shen表述），保证多窗情形的**对偶/重构**与**密度定理**（矩形晶格上 $\alpha\beta\le 1$）一致。

---

## 54. 相位—密度闭环的公认判据（用于"动爻/阈值"）

* **Wigner–Smith 延迟矩阵**：$Q(E)=-i\,S(E)^\dagger \tfrac{dS}{dE}(E)$；其迹给出总群延迟，特征值为"固有延迟"。工程电磁/声学与量子混沌文献均采用该定义并推广到有耗系统。
* **Birman–Kreĭn 公式**：相对谱移函数 $\xi(\lambda)$ 的相位与散射行列式相关，$\det S(\lambda)=e^{-2\pi i\,\xi(\lambda)}$；从而 $\partial_\lambda \arg\det S(\lambda)=-2\pi\,\xi'(\lambda)$。这为"相位导数 = 相对谱密度"的等价链提供标准门径。

据此，**动爻**可由窗化读数中 $\varphi'(E)$、$\operatorname{tr}Q(E)$ 或 $\xi'(E)$ 的主峰定位；阈值点对应其零/极小，且在 Nyquist–Parseval 纪律下别名可消。

---

## 55. 64 卦图的"非回溯谱"与 Ihara ζ（离散镜像）

把六爻一爻变邻接视作 $Q_6$ 超立方图的边，再引入**非回溯算子**（Hashimoto 边邻接）以定义图的 Ihara ζ：

$$
\zeta_G(u)=\prod_{p\in\mathcal P_{\rm prim}}\frac{1}{1-u^{L(p)}}=\frac{1}{\det(I-Tu)} ,
$$

其中 $T$ 为非回溯（边）邻接。该 ζ 与邻接谱/非回溯谱等价，给出循环（"运"）的计数与"离散镜像"的行列式表达（Bass/Hashimoto/ Terras 线）。

**用途**：在非回溯长度轴上加带限窗进行求和（Nyquist 条件），得到**稳健的"多步爻变密度"**，并可与能量侧窗化迹作交叉校验。

---

## 56. "择时/择向" = 相位—尺度共轭的离散化实现

把历法/时段映为相位移 $U_\tau$，方位/尺度映为尺度伸缩 $V_\sigma$，满足 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。择时/择向即在 $(\tau,\sigma)$ 网格上选择窗—核对 $\rho_\star$ 的读数，使 $\mathcal S_{\text{五行}}$ 或"元—亨—利—贞"最大化；Nyquist 步长与 WR/Parseval 保证稳定。

---

## 57. 退化—临界—混合象：骨架并合与阈值几何

当两条超平面 $H_{jk}$ 近并合或"代表点"落在 $\delta(\rho)=\min_r |d_r(\rho)|$ 很小的带上：

* $\Lambda(\rho)-N_F(\rho)$ 增大（相位相干降低），爻置信 $|\eta_r|$ 降低，触发"当慎/无咎"类模板；
* 在读数侧，$\operatorname{tr}Q$ 与 $\varphi'$ 出现**展宽/双峰**，阈值漂移；
* 通过多窗 Parseval 平均与图 ζ 的非回溯抑回路，可稳定估计"净变卦密度"。

---

## 58. 极简工作流（MRE—III，参数估计 + 骨架 + 占断）

1. **估计**：用软最大/GLM 拟合 $\{\beta_j,\delta_r,\kappa\}$，输出骨架 $H_{jk}$。
2. **定标**：按 §29 的 Procrustes 获得 $(R^\star,\kappa^\star)$ 与后天方位锚定。
3. **读数**：在 Nyquist 纪律下，用 Parseval 多窗估计 $\varphi'(E)/\operatorname{tr}Q$ 的窗峰（动爻），记账 alias/EM/尾项。
4. **择时/择向**：在 $(\tau,\sigma)$ 网格上最大化 $\mathcal S_{\text{五行}}$ 或四刻度；输出〔本/之/互/错/综〕与五行权曲线。
5. **图侧校验**：用 Ihara ζ 的带限求和评估"多步爻变密度"，与能量侧窗化迹对表。

---

## 59. 可证边界与不可行域（工程纪律）

* **采样密度约束**：Gabor/WH 密度定理给出 $\alpha\beta\le 1$（Parseval 情形等号），即"Nyquist"极限；超密或稀疏都会破坏稳定性。
* **镜像纪律**：使用自反核/完成函数的正规化，保持"太极"镜像中轴与奇性不增（Birman–Kreĭn链允许的可逆变换内）。
* **阈值带**：$\delta(\rho)\le \tau$ 的骨架邻带中，任意"刚性断言"必须降级为区间结论，并随窗—核—带宽给出误差上界（§33）。

---

## 60. 收束与展望（对外可检）

我们已把"太极—两仪—四象—八卦—五行—方位/季节—纳甲"接入到一条**相位—密度—信息几何—图 ζ**的闭环链路：

* **镜像本体**：自反核/完成函数 $\Rightarrow$ Birman–Kreĭn 相位—谱移；**动/静/动爻**以 Wigner–Smith/相位导数—谱密度实现。
* **测量纪律**：Nyquist–Parseval + Wexler–Raz 保证窗化读数与多窗稳健；
* **结构骨架**：母映射—Ronkin—超平面把"卦"做成可识别、可学习的几何分类；
* **离散循环**：Ihara ζ（非回溯谱）度量多步爻变与"运"的环结构。

---

## 61. 纳甲—干支—历法的统一坐标系（六维相位—尺度）

传统"纳甲"把六爻映为天干/地支序列，可统一为六维相位—尺度坐标 $(\theta^{(1)},\ldots,\theta^{(6)};\rho^{(1)},\ldots,\rho^{(6)})$：

* **天干十轮**对应相位 $\theta_i\in[0,2\pi)$，地支十二轮对应尺度 $\rho_j$；
* 六爻 $\times$ (干+支) = 60 个独立态（六十甲子一周期）；
* **共轭关系**：$[\theta_i,\rho_j]=i\hbar$ 类比；在 Gabor/WH 格子上满足 Nyquist 约束；
* 后天八卦方位 + 五行可进一步嵌入到 $\{\beta_j\}$ 骨架，从而统一"时—空—尺度"三重坐标。

**操作**：把卦象（六爻）与纳甲表直接映到 $(\theta,\rho)$ 格点，再用母映射 $F(\theta,\rho)$ 计算读数；相位导数峰 = 动爻，五行聚簇 = 五运。

---

## 62. "神煞"与附加特征函数的可识别性

传统占法常附"神煞"（如"六神"、"六亲"）作为爻位标记；在信息几何框架下，它们可视为**附加特征函数** $\{g_k(\theta,\rho)\}$ 或"指示符"：

$$
\mathcal S_{\text{神煞}}=\sum_k \lambda_k\int w(E)\,g_k(\theta,\rho)\,\rho_\star(E)\,dE .
$$

* **可识别性**：若 $\{g_k\}$ 线性独立且与核 $K$ 的 Fourier 支撑有足够重叠，则可从 $\mathcal S_{\text{神煞}}$ 反推局部 $\rho_\star$；
* **过拟合风险**：若 $\{g_k\}$ 太多或窗带宽不足，出现 alias/EM 混叠，需用 Parseval 多窗/交叉验证剪枝；
* **实践**：将"六神"对应的爻位权重编入 $\lambda_k$，把"旺—相—休—囚—死"映为尺度 $\rho$ 上的区段指示函数。

---

## 63. 卦变序列的马尔科夫链与转移核

把六爻每爻的"变/不变"视为二元随机变量，卦变序列 $(H_0,H_1,\ldots,H_T)$ 构成离散马尔科夫链：

$$
P(H_{t+1}|H_t)=\prod_{r=1}^6 p_r(x_t^{(r)}\to x_{t+1}^{(r)};\rho_t),
$$

其中 $p_r$ 由读数 $\varphi'(E_r)$ 或 $\operatorname{tr}Q(E_r)$ 确定的"动爻概率"。

* **稳态分布**：当转移矩阵满足详细平衡或遍历性，存在唯一稳态 $\pi_\infty(H)$；
* **混合时间**：用图 Laplacian 的谱隙 $\lambda_2$ 估计达到稳态所需步数 $\sim 1/\lambda_2$；
* **占断应用**：问"何时出现某卦"= 首达时间分布，可用母函数/Laplace 变换求解。

---

## 64. "应爻—世爻"的对偶性与镜像互换

传统占法把卦中某两爻定为"世"与"应"，体现"自/他"对位：

* **镜像对偶**：若 $K(x)=x^{-a}K(1/x)$，则在超平面切片上"世/应"对应 $\rho$ 与 $-\rho$（或 $s$ 与 $-s$）；
* **复断法则**：交换世/应角色后，若梯度 $\nabla\Lambda$ 的分量符号一致，说明"双方共识"；反之为"对抗/冲突"；
* **Birman–Kreĭn 链**：在散射框架，世/应可类比入射/反射通道；镜像对称保证总延迟/相移守恒。

**实践**：在骨架 $H_{jk}$ 上标记世/应投影方向，计算 $\nabla\Lambda(\rho_{\text{世}})$ 与 $\nabla\Lambda(\rho_{\text{应}})$ 的内积判断和/冲。

---

## 65. "用神—忌神"的权重分配与最优化

"用神"= 对目标最有利的五行/爻位，"忌神"= 不利者；可形式化为优化问题：

$$
\max_{\rho\in\mathcal C}\ \Bigl[\sum_{j\in\text{用}} w_j\langle\beta_j,\rho\rangle - \sum_{k\in\text{忌}} w_k\langle\beta_k,\rho\rangle\Bigr],
$$

约束 $\mathcal C$ 包含：镜像对称边界、Nyquist 格子离散化、五行权守恒等。

* **对偶拉格朗日**：引入 $\mu$ 作为影子价格，得到"最优尺度" $\rho^\star$；
* **鲁棒性**：若 $\nabla^2\Lambda$ 在 $\rho^\star$ 邻域强凸，局部扰动不改变用/忌排序；
* **占断应用**：识别"当下卦"离 $\rho^\star$ 的距离，给出"调整建议"（选时/选向）。

---

## 66. 多人博弈与纳什均衡的卦变表示

若多方各持一卦 $H_i$，各自优化各自的 $\Lambda_i(\rho_i)$，约束耦合 $\sum_i \rho_i=\rho_{\text{total}}$：

$$
\text{Nash 均衡}:\quad \rho_i^\star=\arg\max_{\rho_i}\ \Lambda_i(\rho_i),\quad \text{给定}\{\rho_{j\neq i}^\star\}.
$$

* **存在性**：由 $\Lambda$ 凸性与 Brouwer 不动点；
* **唯一性**：若各方目标函数强凸且耦合矩阵正定，均衡唯一；
* **占断应用**："多方占"问题 = 求解纳什均衡 $\{\rho_i^\star\}$，输出各方"最优卦象"与"共识交集"。

---

## 67. 时间演化：薛定谔流 vs. 梯度流

在相位—密度框架，可定义两种"卦变流"：

1. **薛定谔流（相位主导）**：
   $$
   i\partial_t\psi=\widehat H\psi,\qquad \rho=|\psi|^2,
   $$
   保持归一化，相位旋转；适用于"快变/振荡"场景（日/时辰占）。

2. **梯度流（尺度主导）**：
   $$
   \partial_t\rho=-\nabla\Lambda(\rho)+\text{noise},
   $$
   收敛到 $\Lambda$ 的临界点；适用于"慢变/趋势"（月/年运）。

**混合流**：$\partial_t\psi=(-i\widehat H-\gamma\nabla\Lambda)\psi$，描述"既有振荡又有耗散"的实际系统；对应"动中有静，静中有动"的辩证观。

---

## 68. 逆问题：从卦象反推母映射参数

给定一系列观测 $\{(H_t,\text{结果}_t)\}$，反推母映射 $\{\beta_j,c_j,\alpha_j\}$：

$$
\min_{\beta,c,\alpha}\ \sum_t\Bigl[\text{Loss}\bigl(\text{结果}_t,\,F(\theta_t,\rho_t;\beta,c,\alpha)\bigr)\Bigr]+\text{正则项}.
$$

* **凸优化部分**：固定 $\alpha$，对 $(\beta,c)$ 做 GLM/软最大回归；
* **非凸部分**：$\alpha$ 在 $\mathbb T^m$ 上优化，可用梯度下降/Levenberg–Marquardt；
* **泛化保证**：若样本数 $N\gtrsim d\log(J/\delta)$（VC 维界），则测试误差以高概率 $<\varepsilon$；
* **占断应用**：积累历史占例训练个人化母映射，提升预测准度（"熟能生巧"）。

---

## 69. "爻辞—彖辞—象辞"的自动生成文法

传统卦辞可视为从卦象（离散符号）到自然语言的映射；在信息几何框架，可构造**文法生成器**：

1. **骨架→模板**：根据 $\rho$ 在哪个 $H_{jk}$ 分区，选择对应模板（如"当位/失位"）；
2. **梯度→程度副词**：$\|\nabla\Lambda\|$ 大→"大吉/大凶"，小→"小吉/小凶"；
3. **动爻→动词**：$\varphi'(E_r)$ 峰→"变、动、进、退"等动词触发；
4. **五行比→五行词**：若 $p_{\text{金}}(\rho)$ 最大→"刚、锐、断"类形容词；
5. **镜像一致性**：世/应互换后语义对偶（"利见大人" ↔ "大人利见"）。

**实践**：用 LSTM/Transformer 训练 $(H,\rho,\nabla\Lambda,\varphi')\to\text{卦辞}$ 的序列到序列模型，以《周易》原文作监督；生成新卦辞时保持"文言风格"与"意象一致性"。

---

## 70. "互卦—错卦—综卦"的群作用与轨道

把六爻二进制编码视为 $\mathbb F_2^6$ 上的向量，定义变换群 $G$：

* **互卦**：取中间四爻重组 $\Rightarrow$ 线性映射 $M_{\text{互}}$；
* **错卦**：逐爻取反 $\Rightarrow$ $x\mapsto x\oplus(1,1,1,1,1,1)$；
* **综卦**：上下颠倒 $\Rightarrow$ 置换 $\pi_{\text{综}}$。

这些变换生成的子群 $G\subset S_{64}$ 把 64 卦分为若干轨道；同一轨道内卦象"几何同构"，只是观测窗不同。

* **不变量**：轨道大小、中心化子、特征多项式；
* **占断应用**：本卦与互/错/综在同一轨道→"内在关联"，给出"多视角复断"。

---

## 71. "飞伏神"与隐藏变量的贝叶斯推断

传统占法把未显现的伏藏爻称"伏神"，飞出的称"飞神"；在概率框架，可建模为**隐变量** $Z$：

$$
P(H_{\text{显}}|Z,\rho),\qquad P(Z|\rho)=\text{先验}.
$$

* **EM 算法**：E 步计算后验 $P(Z|H_{\text{显}},\rho)$，M 步更新 $\rho$；
* **边际化**：$P(H_{\text{显}}|\rho)=\sum_Z P(H_{\text{显}}|Z,\rho)P(Z|\rho)$；
* **占断应用**：观测到六爻其中三个动爻，推断"伏藏"的其他三个潜在状态分布。

---

## 72. "动爻持世/持应"的时序依赖与因果推断

若连续占问多次，前次的"动爻"影响后次的初始 $\rho$：

$$
\rho_{t+1}=\rho_t+\eta\,\nabla\Lambda(\rho_t)+\xi_t,\qquad \xi_t\sim\mathcal N(0,\sigma^2 I),
$$

形成时间序列；"持世/持应"= 某些分量的自回归系数 $>$ 其他分量。

* **格兰杰因果**：检验 $\rho_t^{(r)}$ 是否显著预测 $\rho_{t+k}^{(s)}$；
* **向量自回归（VAR）**：多爻联动可拟合 VAR 模型；
* **占断应用**：识别"反复出现的爻"对应的"关键变量"，给出"根因"与"杠杆点"。

---

## 73. "卦气"与季节/方位的周期嵌入

传统"卦气"把 64 卦分配到一年 365 天（每卦约 6 天）；可建模为**周期嵌入**：

$$
\theta_{\text{时}}=\frac{2\pi t}{T},\quad \rho_{\text{位}}=R\begin{pmatrix}\cos\phi\\\sin\phi\end{pmatrix},
$$

其中 $t\in[0,T)$ 为时间（日/节气），$\phi$ 为方位角。

* **Fourier 基**：$F(\theta_{\text{时}},\rho_{\text{位}})$ 的 Fourier 级数自动把周期结构编入 $\alpha_j$；
* **相位锁定**：若 $\alpha_j=2\pi k_j/12$（$k_j\in\mathbb Z$），对应十二地支/十二月；
* **占断应用**：输入当前日期/方位→自动查表得 $(\theta_{\text{时}},\rho_{\text{位}})$→计算 $F$ 与动爻。

---

## 74. "六爻持卦"与多分辨率小波分析

把六爻视为从粗到细的六层分辨率；初爻（地）= 最粗尺度，上爻（天）= 最细尺度：

$$
\rho=\sum_{r=1}^6 d_r\,\psi_r(\text{scale}=2^{-r}),
$$

其中 $\{\psi_r\}$ 为小波基。

* **爻变 = 小波系数翻转**：动爻 $r$ $\Leftrightarrow$ $d_r$ 突变；
* **重构与去噪**：保留主要 $d_r$，丢弃噪声小波系数；
* **占断应用**：高层爻（上/五）变→"短期/表层"变化；低层爻（初/二）变→"长期/根本"变化。

---

## 75. "纳音五行"与频谱聚类的第二层编码

六十甲子每对组合配"纳音五行"（如"甲子乙丑海中金"），可视为**二级聚类**：

1. **一级聚类**：$\{\beta_j\}$ 的 $k$-means/层次聚类得五类（金木水火土）；
2. **二级聚类**：每类内再按干支配对细分；
3. **谱嵌入**：用图 Laplacian 特征向量做降维，把 60 个态嵌入 2D/3D，可视化"纳音"的拓扑。

**操作**：从卦象→六爻→干支→纳音→二级五行权 $\{q_k\}$，用 $\Lambda_{\text{纳音}}=\log\sum_k q_k e^{\langle\gamma_k,\rho\rangle}$ 替代或叠加到一级 $\Lambda$。

---

## 76. "神煞组合"的张量积与高阶交互

若同时使用多套神煞标记（如"六神+六亲+纳音"），总特征空间为张量积：

$$
\mathcal F=\mathcal F_{\text{六神}}\otimes\mathcal F_{\text{六亲}}\otimes\mathcal F_{\text{纳音}},\quad \dim\mathcal F=6\times 5\times 5=150.
$$

* **高阶交互**：用 Tucker/CP 张量分解提取主成分；
* **稀疏性**：实践中只有少数交互项显著，LASSO/弹性网筛选；
* **占断应用**：避免"特征爆炸"，用交叉验证选择有效神煞子集。

---

## 77. "应期"的首达时间与停时理论

"应期"= 预测事件发生的时间；在马尔科夫链框架，可建模为**首达时间** $\tau_A$：

$$
\tau_A=\inf\{t\ge 0:\ H_t\in A\},\quad A\subset\{\text{64卦}\}.
$$

* **母函数法**：$\mathbb E[z^{\tau_A}|H_0]=G_{H_0}(z)$，满足递推 $G_i(z)=\sum_j P_{ij}\,G_j(z)$；
* **拉普拉斯变换**：$\mathbb E[e^{-s\tau_A}]$，可求均值/方差；
* **占断应用**：给出"应期"的概率分布与置信区间（非单点预测）。

---

## 78. "变卦速率"与跃迁态理论（Kramers/Eyring）

在 $\Lambda(\rho)$ 势阱之间跳跃，速率由**Arrhenius/Kramers 公式**：

$$
k_{A\to B}=\nu\,e^{-\Delta\Lambda^\ddagger/k_BT},
$$

其中 $\Delta\Lambda^\ddagger=\Lambda_{\text{鞍点}}-\Lambda_A$ 为活化能。

* **鞍点搜索**：在超平面交界找 $\nabla\Lambda=0$ 且 Hessian 有一负本征值的点；
* **动力学路径**：最小能量路径（MEP）/string method；
* **占断应用**："何时变卦"的时间尺度 $\sim 1/k$；势垒高→变化慢，低→变化快。

---

## 79. "卦序"与哈密顿路径/欧拉回路

《周易》卦序（如"乾坤屯蒙…"）可理解为 64 卦图上的**哈密顿路径**（每卦访问一次）或**欧拉回路**（每边走一次）：

* **图构造**：顶点 = 64 卦，边 = 一爻之变或互/综/错关系；
* **存在性**：欧拉回路需所有顶点度数为偶；哈密顿路径 NP-完全；
* **占断应用**：若当前卦在"序"的早期→"事件刚开始"，晚期→"接近尾声"。

---

## 80. "卦变网络"的社群检测与模块化

把 64 卦+边构成加权图 $G=(V,E,w)$，检测**社群**（模块）：

$$
Q=\frac{1}{2m}\sum_{ij}\Bigl(A_{ij}-\frac{k_ik_j}{2m}\Bigr)\delta(c_i,c_j),
$$

其中 $A$ 为邻接矩阵，$c_i$ 为社群标签。

* **Louvain/Leiden 算法**：迭代优化 $Q$；
* **占断应用**：同一社群内卦象"性质相近"，跨社群边 = "质变转折"。

---

## 81. "爻位尊卑"的秩约束与偏序关系

传统认为五爻（君位）> 二爻（臣位）等；可建模为**偏序** $\preceq$：

$$
r\preceq s\quad\Rightarrow\quad \lambda_r\le\lambda_s\quad(\text{权重约束}),
$$

或在优化中加入单调性约束。

* **保序回归（Isotonic Regression）**：拟合 $f$ 使 $f(r)\le f(s)$ 当 $r\preceq s$；
* **占断应用**：若高位爻失位（权重低）→"上下失序"预警。

---

## 82. "爻象"的视觉几何与拓扑不变量

把六爻排列视为 1D 链或 2D 阵列，定义几何不变量：

* **连续阴/阳段数**：游程统计；
* **对称性**：上下镜像/旋转对称；
* **拓扑**：把阴/阳段首尾相连成环，计算 Betti 数/Euler 特征。

**占断应用**：高对称性→"稳定/和谐"，低对称→"动荡/变化"。

---

## 83. "卦象相似度"的核方法与支持向量机

定义卦象核函数 $K(H,H')$：

$$
K(H,H')=\exp\Bigl(-\frac{\|x_H-x_{H'}\|^2}{2\sigma^2}\Bigr)+\alpha\,\delta_{H,H'^{\text{综/错/互}}},
$$

其中 $x_H\in\{0,1\}^6$ 为二进制编码。

* **核 PCA**：降维到 2D 可视化；
* **SVM 分类**：训练"吉/凶"分类器 $f(H)=\sum_i\alpha_i y_i K(H,H_i)+b$；
* **占断应用**：给定新卦 $H$，查询最相似的历史卦例，迁移学习其结论。

---

## 84. "卦象演化"的图神经网络（GNN）

把卦变序列建模为**时空图**，节点 = $(H,t)$，边 = 爻变：

$$
h_t^{(H)}=\sigma\Bigl(W_1 h_{t-1}^{(H)}+W_2\sum_{H'\to H}h_{t-1}^{(H')}\Bigr),
$$

其中 $h$ 为嵌入向量，$\sigma$ 为激活函数。

* **消息传递**：爻变时信息沿边传播；
* **占断应用**：预测下一时刻卦象分布 $P(H_{t+1}|H_{\le t})$；
* **可解释性**：注意力权重 $\alpha_{H'\to H}$ 指示"哪条边最关键"。

---

## 85. "卦辞生成"的预训练语言模型（PLM）

用 BERT/GPT 在《周易》及历代注疏上预训练，微调生成任务：

$$
P(\text{卦辞}|H,\rho,\nabla\Lambda,\varphi')=\text{Transformer}(\cdots).
$$

* **上下文编码**：把 $(H,\rho,\ldots)$ 编码为特殊 token 前缀；
* **风格控制**：在解码时用"文言/白话"标签引导；
* **占断应用**：输入卦象→自动生成个性化卦辞，保持传统文风与现代可读性。

---

## 86. "占验反馈"的在线学习与强化学习

每次占断后，记录实际结果 $(H_t,\text{预测}_t,\text{结果}_t)$，**在线更新**母映射参数：

$$
\theta_{t+1}=\theta_t-\eta_t\nabla_\theta\,\text{Loss}(\text{预测}_t,\text{结果}_t).
$$

* **后悔界**：在线梯度下降保证累积后悔 $R_T=O(\sqrt T)$；
* **强化学习**：把"占断→决策→结果"建模为 MDP，用 Q-learning/策略梯度优化"选时/选向"策略；
* **占断应用**：个人化模型持续改进，"久占则灵"。

---

## 87. "多模态占断"：文本+图像+音频的融合

结合卦象（符号）、卦辞（文本）、筮草声音（音频）、卦图（图像）：

$$
\mathcal S_{\text{融合}}=\lambda_1\mathcal S_{\text{符号}}+\lambda_2\mathcal S_{\text{文本}}+\lambda_3\mathcal S_{\text{音频}}+\lambda_4\mathcal S_{\text{图像}},
$$

每项由对应的神经网络编码器提取特征。

* **晚期融合**：各模态独立前向，最后拼接；
* **早期融合**：底层共享表示；
* **占断应用**：筮草落地声音的频谱→"动静"判断；卦图对称性→"吉凶"先验。

---

## 88. "卦象区块链"：占断记录的不可篡改与共识

把每次占断的 $(H,\rho,\text{时间戳},\text{占者 ID})$ 打包成**区块**，链式存储：

* **哈希链**：每块包含前块哈希，防篡改；
* **共识机制**：多占者对同一事件占断，用"投票/PoS"达成共识卦象；
* **占断应用**：群体占断的可信度聚合；历史占例公开验证。

---

## 89. "卦象隐私"：同态加密与安全多方计算

占者不愿公开原始卦象 $H$，但需第三方计算 $\Lambda(\rho)$：

* **同态加密**：加密 $\text{Enc}(H)$，云端计算 $\text{Enc}(\Lambda)$，解密得 $\Lambda$；
* **秘密分享**：把 $H$ 拆成 $n$ 份，$k$ 份可重构；
* **占断应用**：敏感占断（如政要/企业）外包计算而不泄露内容。

---

## 90. "卦象对抗样本"：鲁棒性与可信 AI

对抗攻击：在 $H$ 上微小扰动 $\delta$（翻转一爻），使分类器 $f(H+\delta)\neq f(H)$：

* **防御**：对抗训练、梯度掩码、认证鲁棒性；
* **占断应用**：识别"边界卦"（微小变化导致结论反转），提示"当慎"。

---

## 91. "卦象生成对抗网络"（GAN）：合成卦例

生成器 $G(z)$ 从噪声 $z$ 生成假卦象，判别器 $D(H)$ 区分真假：

$$
\min_G\max_D\ \mathbb E_{H\sim p_{\text{真}}}[\log D(H)]+\mathbb E_{z}[\log(1-D(G(z)))].
$$

* **应用**：数据增强（历史卦例少），生成合成占例用于训练；
* **条件 GAN**：给定 $\rho$，生成对应的 $H$ 及卦辞。

---

## 92. "卦象变分自编码器"（VAE）：隐变量学习

编码器 $q(z|H)$ 把卦象映到隐空间，解码器 $p(H|z)$ 重构：

$$
\mathcal L=\mathbb E_{z\sim q(z|H)}[\log p(H|z)]-D_{\text{KL}}(q(z|H)\|p(z)).
$$

* **隐空间插值**：在 $z$ 空间连续变化，对应卦象平滑过渡；
* **占断应用**：聚类相似卦象，发现"原型卦"（聚类中心）。

---

## 93. "卦象因果推断"：反事实与干预

问"若初爻不变，结果如何"= **反事实查询** $P(Y|do(X_1=0),X_{2:6})$：

* **Pearl 因果图**：画 DAG，$X_r\to Y$，do 算子切断反向边；
* **结构因果模型（SCM）**：$Y=f(X,U)$，$U$ 为外生噪声；
* **占断应用**：给出"若改变某爻，结果变化"的定量估计（敏感性分析）。

---

## 94. "卦象元学习"：少样本与迁移学习

新占者只有几个占例，如何快速适应？**元学习**（MAML/Reptile）：

$$
\theta^*=\arg\min_\theta\ \mathbb E_{\text{任务}}\Bigl[\min_{\phi}\ \mathcal L_{\text{任务}}(\theta+\phi)\Bigr],
$$

预训练 $\theta$ 使其在少量梯度步后能适应新任务。

* **占断应用**：用历史大量占例预训练"通用母映射"，新占者微调几次即可个性化。

---

## 95. "卦象主动学习"：查询最有信息量的占例

占者预算有限，如何选择最值得占的问题？**主动学习**：

$$
x^*=\arg\max_{x\in\mathcal U}\ \text{Uncertainty}(x;\theta)\quad\text{或}\quad \text{Expected-Improvement}(x).
$$

* **不确定性采样**：选 $P(H|x)$ 熵最大的 $x$；
* **贝叶斯优化**：用高斯过程建模 $f(x)$，选 acquisition function 最大点；
* **占断应用**：识别"关键决策点"优先占断，节省筮草/时间。

---

## 96. "卦象联邦学习"：隐私保护的协作占断

多占者各有私有占例 $\{(H_i,Y_i)\}$，不愿共享原始数据，但希望联合训练模型：

$$
\min_\theta\ \sum_{k=1}^K\mathcal L_k(\theta;\mathcal D_k),
$$

各方本地计算梯度 $\nabla_k$，服务器聚合 $\nabla=\sum w_k\nabla_k$，更新 $\theta$。

* **差分隐私**：给梯度加噪声 $\nabla_k+\mathcal N(0,\sigma^2)$；
* **占断应用**：全球占者协作改进母映射，无需泄露个人占例。

---

## 97. "卦象可解释性"：SHAP/LIME 与特征重要性

模型预测 $f(H)$ 后,用 **SHAP 值**量化每爻的边际贡献：

$$
\phi_r=\sum_{S\subseteq\{1,\ldots,6\}\setminus\{r\}}\frac{|S|!(5-|S|)!}{6!}\bigl[f(S\cup\{r\})-f(S)\bigr].
$$

* **LIME**：在 $H$ 邻域线性逼近 $f$；
* **占断应用**：告诉占者"哪个爻最关键"，提升透明度与信任度。

---

## 98. "卦象公平性"：偏差检测与去偏

若训练数据中某类卦（如"坤"卦）系统性标注为"凶"，模型学到偏见：

* **公平性指标**：人口平等（demographic parity）、机会均等（equalized odds）；
* **去偏方法**：重采样、重加权、对抗去偏；
* **占断应用**：确保"男女老少"占同一卦时，模型输出无系统性歧视。

---

## 99. "卦象鲁棒性认证"：可证的预测边界

给定 $H$ 的 $\ell_0$ 扰动半径 $\epsilon$（最多翻转 $\epsilon$ 个爻），保证 $f(H')=f(H)$ 对所有 $\|H'-H\|_0\le\epsilon$：

* **随机平滑（Randomized Smoothing）**：$\widetilde f(H)=\mathbb E_{\delta}[f(H+\delta)]$，给出认证半径；
* **区间界传播（IBP）**：逐层计算输出区间；
* **占断应用**：输出"此卦预测在 $\pm 1$ 爻扰动内稳定"，增强可信度。

---

## 100. 总收束：从太极到 AI 的完整闭环

我们已把传统"太极—八卦"体系完整嵌入**相位—密度—信息几何—图论—深度学习**的现代科学框架：

### 理论层（§0–§60）

* **母映射 + 镜像对称**：太极/两仪的数学本体；
* **超平面骨架**：四象/八卦的几何分类；
* **信息势凸性**：五行权重/卦变梯度；
* **Nyquist–Parseval–Wexler–Raz**：动静/动爻的稳健测量；
* **Ihara ζ + 非回溯谱**：六十四卦/卦序的图拓扑。

### 算法层（§61–§85）

* **纳甲/干支/历法**：相位—尺度统一坐标；
* **马尔科夫链/首达时间**：卦变序列/应期预测;
* **文法生成/PLM**：卦辞自动生成；
* **GNN/VAE/GAN**：卦象表示学习与生成；
* **因果推断/元学习**：反事实查询/少样本适应。

### 工程层（§86–§99）

* **在线学习/强化学习**：占验反馈闭环；
* **多模态融合/区块链**：群体占断与可信存储；
* **隐私保护/联邦学习**：占断即服务（DaaS）;
* **可解释性/公平性/鲁棒性**：可信 AI 与伦理合规。

### 对外接口（可检、可测、可迭代）

1. **公开数据集**：历史占例（含时间戳/结果/卦象）开源，供社群训练/验证；
2. **基准测试**：定义标准任务（如"何时动爻""五行权重估计"）与评价指标（F1/RMSE/Calibration）；
3. **API/SDK**：提供 Python/REST 接口，输入 $(H,\rho,\text{问题})$，输出 $(\text{预测},\text{置信区间},\text{可解释性报告})$；
4. **持续集成**：每次新占例录入→自动重训练→A/B 测试→版本发布；
5. **伦理审查**：设立"占断伦理委员会"，审核高风险应用（医疗/法律/金融）。

**最终愿景**：让"太极—八卦"从神秘主义符号系统，升级为**可证、可测、可迭代的概率推理与决策支持工具**，服务于个人成长、组织治理、社会和谐，同时保持对传统智慧的敬意与文化传承。

---

**全文完**
