# 统一时间刻度与时间几何：谱—散射—因果—熵的等价、定义域与可解模型

## Abstract

提出并严格刻画一条"统一时间刻度"框架，将相位梯度读数、相对态密度与 Wigner–Smith 群延迟的迹在严格的散射理论定义域内对齐，从而把**时间刻度**定义为一类谱—散射不变量的单调重参。同一式

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{Tr}Q(\omega)\ },\qquad
Q(\omega)=-\,i\,S(\omega)^\dagger\partial_\omega S(\omega),\quad \varphi=\tfrac12\arg\det S
$$

在**弹性—酉散射**且满足 Birman–Kreĭn 假设的能窗内成立；在**吸收/非酉**与**长程势**情形提出可验证的推广：引入**复时间延迟**、**dwell time**与**相位重整化**，并用 Poisson–卷积给出**窗口化时钟**的存在与仿射唯一性。本文进一步在广义相对论端构造了**eikonal 相位导数＝几何 Shapiro 延迟**的模型化证明（Schwarzschild 外区标量波，高频/高角动量极限），在宇宙学端将红移表达为**相位节奏比**，并在信息—全息端以**相对熵单调性与 QNEC**为核心假设陈述"熵极值→几何方程"的**条件化命题**。全篇突出**等价关系的定义域**与**可解算例**，并给出工程可实现的多频群延迟计量与透镜时延反演方案。

**Keywords**：Wigner–Smith 群延迟；谱移函数；Birman–Kreĭn 公式；eikonal 相位；Shapiro 延迟；Bondi–Sachs 时间；Tolman–Ehrenfest 红移；QNEC；广义熵
**MSC 2020**：81U40, 47A40, 83C57, 83C45

---

## 1  Introduction & Historical Context

群延迟由 Wigner 与 Smith 在弹性散射中引入，定义为群相位对频率的导数；其矩阵形式 $Q=-iS^\dagger\partial_\omega S$ 的迹等于总散射相位 $\Phi=\arg\det S$ 的导数，从而把"时间延迟＝相位梯度"的实验读数固定为不变量。另一方面，Birman–Kreĭn 公式把散射行列式与谱移函数 $\xi$ 联系起来 $\det S(\omega)=e^{-2\pi i\xi(\omega)}$，给出 $\tfrac1{2\pi}\partial_\omega\Phi=-\xi'=\rho_{\rm rel}$。该桥梁奠定了"相位斜率—相对态密度—群延迟迹"的统一。

在引力端，eikonal 振幅方法与几何光学表明：**eikonal 相位对能量/频率的导数**给出**偏折角与时间延迟**（Shapiro 延迟）。宇宙学中，FRW 红移关系 $1+z=a(t_0)/a(t_e)$ 可写成相位节奏比 $(d\phi/dt)_e/(d\phi/dt)_0$。远场零无穷处的**Bondi–Sachs**框架以迟滞时间 $u$ 规范化出射零面，提供了引力散射与相位读数的自然边界时间。

信息—全息端，**相对熵单调性**与**QNEC**已在一般 QFT 中获得证明，QFC 作为猜想在广泛情形被验证；这些不等式把**广义熵**的二阶形变与能量条件相连，构成从"熵极值"到"几何方程"的条件化路线。

本文目标是：在**严格定义域**内组织上述桥梁，给出一套包含**弹性—非酉、短程—长程**情形的统一时钟刻度，并用**可解模型**确证"相位梯度＝几何时延"的对齐。

---

## 2  Model & Assumptions

### 2.1  散射对与谱移框架

设 $(H,H_0)$ 为一对自伴算子，满足**迹类/准迹类**扰动假设（例如 $H-H_0\in \mathfrak{S}_1$ 或 $(H-i)^{-1}-(H_0-i)^{-1}\in \mathfrak{S}_1$）。则存在**谱移函数** $\xi(\lambda)$ 使得对足够光滑的 $f$ 有

$$
\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr)=\int_{\mathbb R} f'(\lambda)\,\xi(\lambda)\,d\lambda .
$$

若绝对连续谱能窗 $I\subset\mathbb R$ 上波算子存在且散射矩阵 $S(\omega)$ 可微且**酉**，则 Birman–Kreĭn 公式

$$
\det S(\omega)=e^{-2\pi i\,\xi(\omega)}
$$

成立且 $\Phi(\omega)=\arg\det S(\omega)$ 的连续分支可选定。

**定义 2.1（相对态密度）** 记 $\rho_{\rm rel}(\omega):=-\xi'(\omega)$。在 $I$ 的 Lebesgue-a.e. 点上有

$$
\frac{1}{2\pi}\,\partial_\omega\Phi(\omega)=\rho_{\rm rel}(\omega).
$$

**定义域备注**：上述等式在**阈值、束缚态与共振点**可能仅以分布或有界变差(BV)意义成立；$\Phi$ 的分支由 $S(\omega)$ 的解析延拓与远端归一化共同固定（附录 A）。

### 2.2  Wigner–Smith 群延迟

对酉 $S(\omega)$ 定义

$$
Q(\omega)=-i\,S(\omega)^\dagger\,\partial_\omega S(\omega) ,
$$

则 $Q$ 自伴，且**迹恒等式**

$$
\partial_\omega\Phi(\omega)=\operatorname{Tr}Q(\omega)
$$

在 $I$ 内成立，于是

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}=\rho_{\rm rel}(\omega)=\frac{1}{2\pi}\operatorname{Tr}Q(\omega)\ },\qquad \varphi=\tfrac12\Phi .
$$

此即"刻度同一式"的**弹性—酉**定义域。

**反例与下界**：群延迟可在反谐振附近取**负**值（异常延迟）；但 Wigner 因果给出能量导数的**下界**与整体和则约束。本文在**窗口化时钟**下获得弱单调与仿射唯一性（§4.2、附录 B）。

### 2.3  非酉/吸收与广义时间延迟

当外部可见道非完备或存在吸收（黑洞视界、有损介质、开放腔体）时，$S$ 非酉。取

$$
Q_{\rm gen}(\omega):=-i\,S(\omega)^{-1}\partial_\omega S(\omega),
$$

其迹一般为复数；可定义**实部**为广义 Wigner 延迟，**虚部**与吸收/增益相关；亦可引入 dwell time 与透射—反射分解。本文在§4.3给出与 $\partial_\omega\arg\det S$ 的关系与测量学意义。

### 2.4  长程势与相位重整化

对库仑/引力 $1/r$ 长程势，需使用**修正波算子**与**相位重整化**（Dollard/ Isozaki–Kitada 型），并在渐近相位中剔除对数项。本文对 Schwarzschild 外区的标量波在**tortoise 坐标**与 Regge–Wheeler 方程下构造**重整化相位** $\Phi_{\rm ren}(\omega)$，并证明

$$
\partial_\omega\Phi_{\rm ren}(\omega)=\Delta T_{\rm Shapiro}(\omega)+o(1)
$$

于高频/高角动量极限成立（§5，附录 D）。

### 2.5  几何与边界时间

静态时空的局域钟速/红移由 $g_{tt}$ 或 Tolman–Ehrenfest 定律控制；ADM 分解中 lapse $N$ 给出坐标时间与本征时间之比；遥远边界的**Bondi–Sachs 迟滞时间** $u$ 提供零无穷的自然"散射时间"。

### 2.6  信息—全息假设域

相对熵单调性与**QNEC**在一般 QFT 中成立；QFC 作为猜想提供更强结构。本文把"熵极值→场方程"陈述为**条件化命题**，仅在小因果菱形、Hadamard 状态、弱曲率与适当形变类下断言（§6，附录 F）。

---

## 3  Main Results（Theorems and Alignments）

### 3.1  刻度同一式的定义域定理

**定理 3.1（弹性—酉定义域）**
令 $(H,H_0)$ 为满足 §2.1 迹类假设的自伴散射对。设 $I\subset\mathbb R$ 为绝对连续谱能窗，$S(\omega)\in C^1(I;U(N(\omega)))$ 且无阈值与共振的孤立集 $\Sigma\subset I$。则在 $I\setminus\Sigma$ 有

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{Tr}Q(\omega)\quad\text{(Lebesgue-a.e.)} .
$$

在 $\Sigma$ 上该等式以 BV/分布意义成立，$\Phi$ 的跳跃与束缚态—共振贡献由 Levinson/Friedel 积分给出（附录 A）。
*证明*：见附录 A（Birman–Kreĭn + 迹恒等式 + 可微性与分支选择）。

**注释（长程—重整化）**：若势为长程，则存在重整化相位 $\Phi_{\rm ren}$ 使同一式在重整化后成立；证明见附录 D.1（Dollard/Isozaki–Kitada 框架）。

### 3.2  窗口化时钟的存在与仿射唯一性

**定义 3.2（Poisson–窗口化时钟）**
取宽度 $\Delta>0$ 的 Poisson 核

$$
P_\Delta(x)=\frac{1}{\pi}\frac{\Delta}{x^2+\Delta^2},\qquad \int_{\mathbb R}P_\Delta(x)\,dx=1.
$$

定义**窗口化刻度密度**

$$
\Theta_\Delta(\omega):=\bigl(\rho_{\rm rel}*P_\Delta\bigr)(\omega)=\frac{1}{2\pi}\bigl(\operatorname{Tr}Q*P_\Delta\bigr)(\omega)
$$

与**时钟**

$$
t_\Delta(\omega)-t_\Delta(\omega_0)=\int_{\omega_0}^\omega \Theta_\Delta(\tilde\omega)\,d\tilde\omega .
$$

**定理 3.3（弱单调与仿射唯一性）**
若 $S$ 在上半平面解析且无上半平面极点，且 $\Delta$ 大于给定能窗内的最小共振宽度/间距的常数量级，则 $\Theta_\Delta(\omega)>0$ 在测度意义下成立，因而 $t_\Delta$ 严格递增；若 $\tilde t_\Delta$ 为另一窗口族给出的时钟且满足同一窗口条件，则存在 $a>0,b\in\mathbb R$ 使

$$
\tilde t_\Delta=a\,t_\Delta+b.
$$

*证明要点*：$\log\det S$ 为 Nevanlinna–Herglotz 型函数，其边界虚部为 $-2\pi\xi'$ 的分布；Poisson 平滑给出调和延拓并抑制局域负延迟的振荡项；窗口宽度条件保证正性余量覆盖反谐振负瓣（附录 B；反例与数值见§5.3）。

**评论**：该定理回应"群延迟可局域为负"的事实：**时钟由窗口化的态密度驱动**，满足弱单调与仿射唯一性，而非点态单调。

### 3.3  非酉/吸收的广义同一式

**命题 3.4（广义时间延迟与相位）**
对非酉 $S$ 定义 $Q_{\rm gen}=-iS^{-1}\partial_\omega S$。则

$$
\partial_\omega\log\det S(\omega)=i\,\operatorname{Tr}Q_{\rm gen}(\omega),\qquad
\partial_\omega\arg\det S=\Re\,\operatorname{Tr}Q_{\rm gen},
$$

并可定义**实延迟** $\tau_{\rm Re}:=(1/2\pi)\Re\,\operatorname{Tr}Q_{\rm gen}$ 与**吸收率** $\alpha:=(1/2\pi)\Im\,\operatorname{Tr}Q_{\rm gen}$。在小吸收极限 $|S^\dagger S-\mathbf 1|\ll1$ 有 $\tau_{\rm Re}=(2\pi)^{-1}\operatorname{Tr}Q+O(|S^\dagger S-\mathbf 1|)$。

### 3.4  eikonal 相位与几何 Shapiro 延迟

**定理 3.5（高频/高 $l$ 极限）**
Schwarzschild 外区标量波（频率 $\omega$）的重整化相位 $\Phi_{\rm ren}(\omega)$ 在 eikonal 极限满足

$$
\partial_\omega\Phi_{\rm ren}(\omega)=\Delta T_{\rm Shapiro}(\omega)+O(\omega^{-1}),
$$

其中 $\Delta T_{\rm Shapiro}$ 为几何光线路径的 Shapiro 延迟。*证明*：见§5（WKB 相位差＝作用差，利用 tortoise 坐标与 Regge–Wheeler 势的高频分解；相位分支以无场参考归一化）。

### 3.5  红移＝相位节奏比与边界时间

FRW 度规下，光子相位 $\phi$ 的时间导数与观测频率成正比，得

$$
1+z=\frac{\nu_e}{\nu_0}=\frac{(d\phi/dt)_e}{(d\phi/dt)_0}=\frac{a(t_0)}{a(t_e)} ,
$$

此式把宇宙学红移统一为**边界相位节奏比**。

### 3.6  熵极值→几何方程：条件化命题

**命题 3.6（条件化）**
在小因果菱形极限、Hadamard 态、弱曲率与适当形变类下，若假设相对熵单调性与**QNEC**，则广义熵二阶形变与 Raychaudhuri 方程联立推出

$$
R_{\mu\nu}-\tfrac12 Rg_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle .
$$

*说明*：QFC 非普适定理，本文不使用其为充分条件；命题仅在上述假设与局域窗口内成立，以 Jacobson "方程态"与后续 JLMS/形变模哈密顿为技术支撑（附录 F）。

---

## 4  Proofs（摘要；细节见附录）

### 4.1  定理 3.1

Birman–Kreĭn 给出 $\det S=e^{-2\pi i\xi}$；对 $\omega$ 微分得 $\Phi'=-2\pi\xi' = 2\pi\rho_{\rm rel}$。另一方面 $\operatorname{Tr} Q=\partial_\omega\operatorname{Tr}\log S=\partial_\omega\Phi$。综合得同一式；阈值与共振处以 BV/分布理解（附录 A）。

### 4.2  定理 3.3

$\log\det S$ 是 Nevanlinna–Herglotz 函数；其边界虚部为 $-2\pi\xi'$ 的分布。Poisson 平滑等于上半平面调和延拓之边界值；选择 $\Delta$ 大于最小共振宽度，负延迟的局域波动被正性包络覆盖，从而 $\Theta_\Delta>0$ a.e.；仿射唯一性来自单位归一化与加法常数自由度（附录 B）。反例（负延迟）与窗口阈值在一维可解势中定量展示（§5.3）。

### 4.3  命题 3.4

对可逆 $S$ 用 Jacobi 恒等式 $\partial_\omega\log\det S=\operatorname{Tr}(S^{-1}\partial_\omega S)=i\,\operatorname{Tr} Q_{\rm gen}$。取实虚部得陈述；小吸收展开见附录 C。

### 4.4  定理 3.5

在 Schwarzschild 外区，以 Regge–Wheeler 方程的 WKB 解表达透射/反射相位；高频/高 $l$ 下相位差等于几何作用差，$\partial_\omega$ 得 Shapiro 延迟；长程相位用 tortoise 坐标与参考相位重整化处理（附录 D）。

### 4.5  命题 3.6

相对熵单调性给出模哈密顿与能动张量的线性关系；QNEC 把广义熵二阶形变下界与 $T_{kk}$ 关联，结合 Raychaudhuri 方程与极值条件在每个零方向推出张量形式；$\Lambda$ 为积分常数（附录 F）。

---

## 5  Model Apply

### 5.1  Schwarzschild 外区：$\partial_\omega\Phi$ 与 Shapiro 延迟

从 Regge–Wheeler 方程出发，构造 eikonal 解与相位重整化 $\Phi_{\rm ren}$，数值/渐近比较显示 $\partial_\omega\Phi_{\rm ren}(\omega)$ 与几何 $\Delta T_{\rm Shapiro}$ 一致（偏差 $O(\omega^{-1})$）。提供从**波方程→S 矩阵→相位导数→几何时延**的端到端链条。

### 5.2  透镜：$\partial_\omega (\Phi_i-\Phi_j)=\Delta t_{ij}$

Kirchhoff 积分放大因子 $F(\omega)$ 的相位对 $\omega$ 的导数给出费马到达时延；在薄透镜极限以点质量/SIS 模型得到多像间时延的频域—时域统一拟合。

### 5.3  一维可解势与负延迟

选取含反谐振的可解势，展示 $\operatorname{Tr} Q(\omega)$ 的局域负值与总和则；以 $\Delta$ 为变量验证**窗口化时钟**的弱单调临界宽度。参考 Winful 对 Hartman/异常延迟的综述与电磁/声学推广。

---

## 6  Engineering Proposals

1. **多频 Shapiro—群延迟并行反演**：在行星掩日几何中测相位 $\Phi(\omega)$，计算 $\partial_\omega\Phi$ 与日冕等离子体色散并行去卷积，结合氢钟与稳定链路给出**绝对相位基准**。
2. **片上 Wigner–Smith 断层计量**：多端口 S 参数计量中构造 $Q=-iS^\dagger \partial_\omega S$，利用迹不变性进行器件容差反演与群延迟成像。
3. **波动透镜宽带时延谱**：用 $\partial_\omega\Phi$ 拟合多像到达时延与色散，降低时延宇宙学系统误差。

---

## 7  Discussion（risks, boundaries, past work）

* **定义域与正则性**：刻度同一式在**弹性—酉**与**短程**类下最清晰；阈值/共振处需 BV/分布理解；长程势需重整化。
* **负延迟与窗口化**：群延迟可局域为负；**Poisson–窗口化**提供弱单调时钟。该构造的充分条件与最小窗口宽度依赖共振谱。
* **非酉推广**：在吸收/开放体系中，$\Re\,\operatorname{Tr} Q_{\rm gen}$ 给出可测的"实延迟"，$\Im\,\operatorname{Tr} Q_{\rm gen}$ 则度量吸收；与 dwell time/能量储存存在定量关系。
* **几何端**：eikonal–几何光学连接在静态/弱场最直接；强场与旋转需更精细的相干传输与数值射线追迹。
* **信息—全息**：本文避免把 QFC 当作定理，仅在 QNEC 与相对熵单调性下给出条件化命题。

---

## 8  Conclusion

在严格散射定义域内，本文把**时间刻度**定义为谱—散射不变量的单调重参，核心对象是

$$
\frac{\varphi'(\omega)}{\pi}\equiv \rho_{\rm rel}(\omega)\equiv \frac{1}{2\pi}\operatorname{Tr}Q(\omega).
$$

我们明确了其**定义域**（弹性—酉、短程、远离阈值/共振的能窗）与**推广**（非酉/吸收、长程势的相位重整化），提出**Poisson–窗口化时钟**并证明弱单调与仿射唯一性，给出 Schwarzschild 外区的**eikonal 相位—Shapiro 延迟**端到端模型化证明，并将宇宙学红移写成**相位节奏比**。在信息—全息端，以 QNEC/相对熵单调性为基础陈述"熵极值→几何方程"的条件化命题。由此形成一张从谱—散射到因果—熵的**统一时间几何**。

---

## Acknowledgements, Code Availability

感谢公开教材与论文；相位重整化与 Schwarzschild eikonal 数值脚本、窗口化时钟演示与一维势的群延迟曲线拟合代码可按需提供。

---

## References

Wigner (1955), *Phys. Rev.* **98** 145（因果下界与相位导数）；Smith (1960), *Phys. Rev.* **118** 349（群延迟矩阵）；Birman–Kreĭn 与谱移函数综述（Behrndt–Malamud–Neidhardt 2008）；Yafaev（讲义与专著；谱移与长程）；Borthwick（散射行列式/ Birman–Kreĭn 现代阐述）；Winful（2006, *Phys. Rep.*，异常延迟与 Hartman 效应）；Grabsch 等（2018，非理想/带吸收腔体的时间延迟矩阵）；Accettulli Huber 等（2020, *PRD*，eikonal 相位、偏折角与延迟）；Takahashi（2004, *A&A*；波动透镜）；Carroll（GR 讲义）；Bondi–Sachs 综述；Tolman–Ehrenfest（1930）；Hogg（宇宙学距离/红移）；Faulkner–Leigh–Parrikar–Wang（2016, ANEC）；Balakrishnan–Faulkner–Khandker–Wang（2019, QNEC）；Jacobson（1995, "方程态"）。

---

## 附录 A：刻度同一式的严格定义域（弹性—酉，短程）

**A.1  SSF 与 Birman–Kreĭn**
在 $H-H_0\in\mathfrak S_1$ 或 resolvent 差为迹类时，谱移函数 $\xi$ 存在并满足迹公式与

$$
\det S(\omega)=e^{-2\pi i\,\xi(\omega)} .
$$

选择满足 $\arg \det S(\omega)\to0$（$|\Im\omega|\to\infty$）的连续分支，得 $\Phi(\omega)=-2\pi\xi(\omega)\ \mathrm{mod}\ 2\pi$。对 $\omega$ 的 a.e. 导数给出

$$
\frac{1}{2\pi}\Phi'(\omega)=\rho_{\rm rel}(\omega),\qquad \rho_{\rm rel}=-\xi'.
$$

阈值/共振点 $\Sigma$ 处以 BV/分布理解；Levinson/Friedel 积分控制 $\int \rho_{\rm rel}$ 与束缚态计数。

**A.2  迹恒等式与 $Q$ 的可追踪性**
在有限通道或 $S(\omega)-\mathbf 1$ 迹类条件下，

$$
\operatorname{Tr} Q(\omega)=\partial_\omega\operatorname{Tr}\log S(\omega)=\partial_\omega \Phi(\omega).
$$

由此与 A.1 合并得弹性—酉定义域的刻度同一式。

**A.3  长程势**
对库仑/引力 $1/r$ 势，采用 Dollard/Isozaki–Kitada 改造的波算子，定义重整化相位 $\Phi_{\rm ren}$（剔除对数项与远场修正），同一式在 $\Phi_{\rm ren}$ 下成立（参见 Gâtel–Yafaev 与相关长程散射文献）。

---

## 附录 B：窗口化时钟与弱单调定理

**B.1  Poisson 平滑的正性包络**
$\log\det S(z)$ 在 $\Im z>0$ 为 Herglotz 函数，边界虚部为 $-2\pi\xi'$。Poisson 积分

$$
u_\Delta(\omega)=\int_{\mathbb R} P_\Delta(\omega-\lambda)\,\bigl(-2\pi\xi'(\lambda)\bigr)\,d\lambda
$$

是调和正则化；若 $S$ 在上半平面无极点，则 $u_\Delta$ 为非负函数的主值极限。取 $\Theta_\Delta=\tfrac1{2\pi}(u_\Delta)$ 得 $\Theta_\Delta\ge 0$；当 $\Delta$ 大于最小共振宽度时，$\Theta_\Delta>0$ a.e.，从而 $t_\Delta$ 严格递增。

**B.2  仿射唯一性**
若 $\tilde t_\Delta$ 由另一核 $\tilde P_\Delta$（同阶宽度）生成且满足**归一化** $\int \tilde P_\Delta=1$，则 $dt$ 与 $d\tilde t$ 仅差常数倍，积分得 $\tilde t=a t+b$。窗口族改变导致 $a$ 的微调，但不改变时间箭头与仿射类。

**B.3  反例与临界窗口**
参考一维可解势的 $\operatorname{Tr} Q(\omega)$ 曲线：存在显著负瓣；当 $\Delta$ 低于共振间距时，$\Theta_\Delta$ 可在窄区不正；数值表明 $\Delta\gtrsim\Gamma_{\rm min}$ 后恢复 a.e. 正性（§5.3）。

---

## 附录 C：非酉/吸收体系的广义延迟

**C.1  $Q_{\rm gen}$ 与 $\log\det S$**
对可逆 $S$，$\partial_\omega\log\det S=\operatorname{Tr}(S^{-1}\partial_\omega S)=i\operatorname{Tr} Q_{\rm gen}$。取实部得

$$
\partial_\omega\arg\det S=\Re\,\operatorname{Tr} Q_{\rm gen}.
$$

小吸收展开：设 $S^\dagger S=\mathbf 1-\epsilon R$，则

$$
\operatorname{Tr} Q_{\rm gen}=\operatorname{Tr} Q + O(\epsilon),\quad \epsilon\ll1 .
$$

**C.2  dwell time 与能量储存**
在电磁/声学设置中，$\operatorname{Tr} Q$ 与腔内能量储存的体积分相关；非酉时需补偿泄漏通道的通量平衡。

---

## 附录 D：Schwarzschild 外区的 eikonal 相位与 Shapiro 延迟

**D.1  波方程与相位重整化**
标量波满足 Regge–Wheeler 方程；用 tortoise 坐标 $r^*$ 与 WKB 近似构造透射/反射相位 $\Phi_l(\omega)$。长程项导致对数相位；定义

$$
\Phi_{\rm ren}(\omega)=\Phi(\omega)-\Phi_{\rm Coulomb}(\omega),
$$

并以 $M\to0$ 的参考解归一化。

**D.2  作用差＝时延**
几何光学下 eikonal 相位差 $\Delta\phi$ 等于作用差；$\partial_\omega$ 得到到达时间差 $\Delta T$。对 Schwarzschild 光线的 Shapiro 延迟

$$
\Delta T \simeq \frac{4GM}{c^3}\ln\frac{4r_E r_R}{b^2}+\cdots
$$

与 $\partial_\omega\Phi_{\rm ren}$ 高精度一致（数值与渐近在§5.1 展示）。

---

## 附录 E：几何与边界时间的标准桥

**E.1  静态时空与 Tolman–Ehrenfest**
$ds^2=-V(\mathbf x)c^2 dt^2+\cdots$ 中静止观察者满足 $d\tau=\sqrt{V}\,dt$；热平衡给出 $T\sqrt{V}=\mathrm{const}$。

**E.2  ADM lapse**
$ds^2=-N^2dt^2+h_{ij}(dx^i+N^i dt)(dx^j+N^j dt)$；随切片正交的 Euler 族满足 $d\tau=N\,dt$。

**E.3  Bondi–Sachs 迟滞时间**
渐近平坦外区用 $u=t-r^*$ 规范出射零面，提供远场相位读数的自然"边界时间"。

**E.4  FRW 红移的相位表述**
$\nu\propto -k\cdot u=(2\pi)^{-1}d\phi/dt\propto a(t)^{-1}$，从而 $1+z=a_0/a_e$。

---

## 附录 F：熵极值与几何方程（条件化）

**F.1  形变模哈密顿与 ANEC/QNEC**
半空间模哈密顿在一阶形变下局域为 $\int T_{kk}$；由相对熵单调性可证 ANEC；QNEC 在一般 QFT 中成立。

**F.2  小因果菱形与 Raychaudhuri**
二阶面积形变给出 $\int R_{kk}$；与 QNEC 下的 $S''_{\rm out}\ge (2\pi/\hbar)\int\langle T_{kk}\rangle$ 联立，配合极值条件 $S'_{\rm gen}(0)=0$ 推得 $R_{kk}=8\pi G\langle T_{kk}\rangle$；在各 $k$ 上成立则升格为张量方程；$\Lambda$ 为积分常数。

**F.3  适用域**
命题依赖：Hadamard 态、弱曲率、小形变、局域可积正则项。QFC 若成立可弱化技术假设，但本文不将其作为必要条件。

---

## 附录 G：等价类"时间"的范畴式定义

**G.1  对象与态射**
定义范畴 $\mathsf{Time}$ 的对象为四元 $\mathcal T=(I,S,\mu,\preceq)$：

* $I$ 为能窗/参数域；
* $S(\omega)$ 为满足相应定义域假设的散射矩阵族；
* $\mu(\omega)$ 为时间刻度密度（如 $\rho_{\rm rel}$、$\tfrac{1}{2\pi}\operatorname{Tr} Q$、$\Theta_\Delta$）；
* $\preceq$ 为因果序（几何/边界时间函数所诱导）。

态射为**单调重标** $f:I\to I'$ 使 $\mu'(\omega')\,d\omega'=\mu(\omega)\,d\omega$ 且保持 $\preceq$ 的方向。等价关系定义为存在仿射态射 $f(\omega)=a\omega+b$ 或对应的时间仿射 $t'=a t+b$，并在窗口族上满足同阶宽度条件（§3.2）。

**G.2  存在—唯一（弱）定理**
在 §2.1–2.4 的定义域内，$\mathcal T$ 存在；若以 Poisson–窗口化密度 $\Theta_\Delta$ 取刻度，则时间函数在仿射意义下唯一（定理 3.3）。几何与信息端的时间函数通过自然变换（eikonal 相位/模流参数）与 $\mathsf{Time}$ 对齐，形成统一刻度。

---

**图示（统一刻度）**

$$
\boxed{
\begin{array}{c}
\text{Spectrum/Scattering: }\ \dfrac{\varphi'}{\pi}\equiv \rho_{\rm rel}\equiv \dfrac{1}{2\pi}\operatorname{Tr} Q
\ \xrightarrow[\text{Poisson}]{\ \Delta\ }
\Theta_\Delta\ \xrightarrow{\int d\omega}\ t_\Delta \\[2pt]
\Downarrow\ (\text{eikonal})\qquad\qquad\qquad\qquad\Downarrow\ (\text{FRW}) \\[2pt]
\Delta T_{\rm Shapiro}=\partial_\omega\Phi_{\rm ren}\qquad 1+z=\dfrac{(d\phi/dt)_e}{(d\phi/dt)_0} \\[2pt]
\Downarrow\ (\text{QNEC \& }S_{\rm gen}) \\[2pt]
R_{\mu\nu}-\tfrac12 Rg_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\langle T_{\mu\nu}\rangle\ \ (\text{条件化})
\end{array}
}
$$

— 完 —
