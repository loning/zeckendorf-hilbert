# S20. 交换算子的信息几何：BN 投影—KL 代价—灵敏度不等式

**—— RKHS/BN 界面下的凸对偶、Bregman 结构与 Nyquist–Poisson–EM 非渐近闭合**

## 摘要（定性）

在再生核 Hilbert 空间（RKHS）与 Beurling–Nyman（BN）混合集/闭凸包的统一框架中，建立由 log-sum-exp 信息势诱导的 Bregman 几何与几何最小范数投影之间的变分对应：在度量校准与 Legendre 条件下，软极小元获得互反参数化，并满足精确毕达哥拉斯恒等式；通过温度极限证明软极小元向硬投影的 Γ-极限收敛。进一步给出"信息—能量—灵敏度"不等式族，刻画几何偏差、相对熵与目标函数缺口的共同控制。数值层面以 Nyquist–Poisson–Euler–Maclaurin（EM）三分解实现离散—连续换序的非渐近闭合，并在解析窗/核与有限阶 EM 的纪律下保持奇性集合（"极点=主尺度"）。所建范式与 S15（Weyl–Heisenberg 酉表示）、S16（de Branges–Krein 规范系统）、S17（散射酉/对称）与 S19（谱图与 Ihara ζ）自然对齐。

---

## 0. 设定与记号

### 0.1 空间、核、镜像

记 $(\mathcal H,\langle\cdot,\cdot\rangle)$ 为可分 Hilbert 空间，$|x|:=\langle x,x\rangle^{1/2}$。再生核 $K$ 给出评估向量 $k_x\in\mathcal H$，使 $f(x)=\langle f,k_x\rangle$。镜像对合 $J:\mathcal H\to\mathcal H$ 为等距自反，$J^2=I$，与完成参数 $a$ 相容：$k_{a-s}=Jk_s$。

### 0.2 BN 原子与混合集/闭凸包

给定测度空间 $(\mathcal J,\nu)$，设原子映射 $\Phi:\mathcal J\to\mathcal H$ **强可测**且 $\int_{\mathcal J}|\Phi(\xi)|^2\,d\nu(\xi)<\infty$。定义

$$
\mathcal C\ :=\ \overline{\operatorname{conv}}\bigl\{\ \Phi(\xi)\ :\ \xi\in\mathcal J\ \bigr\}\ \subset\ \mathcal H,
$$

为 BN **混合集/闭凸包**（范数闭凸集）。置

$$
E:L^2(\nu)\to\mathcal H,\quad Eg:=\int_{\mathcal J}\Phi(\xi)\,g(\xi)\,d\nu(\xi),\qquad
(E^\ast h)(\xi)=\langle h,\Phi(\xi)\rangle .
$$

当且仅当 $\operatorname{ran}E$ **闭**时，Moore–Penrose 广义逆 $(E^\ast E)^\dagger$ 为有界，且

$$
P=E\,(E^\ast E)^\dagger E^\ast
$$

为到 $\overline{\operatorname{ran}E}$ 的正交投影。若 $\operatorname{ran}E$ 非闭，上式不定义为有界算子，投影仅以"到闭凸集的最小范数元"抽象存在唯一。

支撑函数满足 $\sigma_{\overline{\mathcal C}}(\theta)=\operatorname*{ess\,sup}_{\xi}\langle\theta,\Phi(\xi)\rangle$（取 $\nu$-本质上确界），与"原子最大"一致。

### 0.3 信息势、有效域与 Legendre 结构

定义 log-sum-exp 势

$$
\Lambda(\theta):=\log\!\int_{\mathcal J}e^{\langle\theta,\Phi(\xi)\rangle}\,d\nu(\xi),\qquad
\Theta:=\Bigl\{\ \theta\in\mathcal H\ :\ \int e^{\langle\theta,\Phi\rangle}d\nu<\infty\ \Bigr\}.
$$

$\Theta$ 为非空开凸集（例如 $\nu$ 有限且 $\Phi$ 有界时 $\Theta=\mathcal H$）。对 $\theta\in\Theta$，Bochner 意义下

$$
\nabla\Lambda(\theta)=\int \Phi\,p_\theta\,d\nu,\qquad
\nabla^2\Lambda(\theta)=\operatorname{Cov}_{p_\theta}[\Phi]\succeq0,\qquad
p_\theta(\xi)=e^{\langle\theta,\Phi(\xi)\rangle-\Lambda(\theta)}.
$$

假设 $\Lambda$ **本质光滑严格凸**（Legendre 型）[^Rockafellar70]，则
$\nabla\Lambda:\Theta\to\operatorname{ri}(\mathcal C)$ 为双射，且

$$
\operatorname{dom}\Lambda^\ast=\overline{\mathcal C},\qquad \operatorname{ri}\bigl(\operatorname{dom}\Lambda^\ast\bigr)=\operatorname{ri}(\mathcal C),\qquad (\nabla\Lambda)^{-1}=\nabla\Lambda^\ast .
$$

边界 $\partial\mathcal C$ 上 $\Lambda^\ast$ 可取有限值但通常不可微。

### 0.4 窗化与有限阶 EM

选择在工作条带解析的偶窗 $w$ 与试验核 $h$，带限或指数衰减。所有离散—连续换序仅用**有限阶** EM；误差采用"别名 + 伯努利层 + 截断"三分解（§5）。

---

## 1. BN 投影与凸对偶

### 1.1 最小范数投影

对 $F\in\mathcal H$，定义到 $\mathcal C$ 的投影

$$
\Pi_{\mathcal C}(F):=\arg\min_{X\in\mathcal C}\ \tfrac12|X-F|^2.
$$

$\mathcal C$ 闭凸 $\Rightarrow$ 极小元存在唯一；$\Pi_{\mathcal C}$ 为**坚定非扩张**映射（firmly nonexpansive）。由于 $\mathcal C$ 闭凸，$\Pi_{\mathcal C}$ 作为最近点映射存在唯一且坚定非扩张；当 $\operatorname{ran}E$ 非闭时，$E(E^\ast E)^\dagger E^\ast$ 不再给出有界算子表示，但到 $\overline{\operatorname{ran}E}$ 的**正交**投影仍存在（与 $\Pi_{\mathcal C}$ 无需相同）。

### 1.2 Fenchel–Rockafellar 对偶与 KKT

$\iota_{\mathcal C}$ 为 $\mathcal C$ 的指标函数；$\sigma_{\mathcal C}(\theta):=\sup_{X\in\mathcal C}\langle\theta,X\rangle$ 为支撑函数。由二次项处处有限，强对偶成立[^Rockafellar70][^BauschkeCombettes11]：

$$
\min_X\Bigl\{\tfrac12|X-F|^2+\iota_{\mathcal C}(X)\Bigr\}
=\tfrac12|F|^2-\min_\theta\Bigl\{\tfrac12|F-\theta|^2+\sigma_{\mathcal C}(\theta)\Bigr\}
=\tfrac12|F|^2+\max_\theta\Bigl\{-\tfrac12|F-\theta|^2-\sigma_{\mathcal C}(\theta)\Bigr\}.
$$

存在原始解 $X^\ast=\Pi_{\mathcal C}(F)$ 与对偶解 $\theta^\ast$ 满足 KKT 条件

$$
\theta^\ast=F-X^\ast,\qquad \theta^\ast\in N_{\mathcal C}(X^\ast),
$$

其中 $N_{\mathcal C}(X)$ 为法锥。

---

## 2. 软支撑、熵正则化与 Bregman 结构

令

$$
Q(\theta):=\tfrac12|\theta-F|^2+\Lambda(\theta),\qquad
g(X):=\tfrac12|X-F|^2+\Lambda^\ast(X).
$$

### 2.1 软支撑与最小相对熵

$$
\Lambda^\ast(X)=\inf_{\substack{p\in\mathcal P(\nu)\\ \int \Phi\,p=X}}\ \mathrm{KL}(p\,|\,\nu),
\qquad \mathcal P(\nu)=\{p\ge0,\ \int p\,d\nu=1\},
$$

其中**以基准测度 $\nu$ 为参考的相对熵**

$$
\mathrm{KL}(p\,|\,\nu)=\int p\log p\,d\nu
$$

（$p$ 为对 $\nu$ 的密度）。若以同一 $\nu$ 为参考比较两密度 $p,q$，则

$$
\mathrm{KL}(p\,|\,q)=\int p\log\frac{p}{q}\,d\nu .
$$

因此

$$
\min_{\theta}Q(\theta)\ \Longleftrightarrow\ \min_{p\in\mathcal P(\nu)}\Bigl[\tfrac12\bigl|\textstyle\int \Phi\,p-F\bigr|^2+\mathrm{KL}(p\,|\,\nu)\Bigr].
$$

> **注**：若 $\nu$ 非概率，$\mathrm{KL}(p\,|\,\nu)=\int p\log p\,d\nu$ 与以归一化 $\bar\nu$ 为基准的相对熵相差常数；本文仅以差值与最优化为目的，常数项不影响结论。

### 2.2 $Q$ 的 Bregman—欧氏毕达哥拉斯

对任意 $\theta,\vartheta\in\Theta$：

$$
Q(\theta)=Q(\vartheta)+\tfrac12|\theta-\vartheta|^2+D_\Lambda(\theta\mid\vartheta)+\langle\nabla Q(\vartheta),\theta-\vartheta\rangle.
$$

若 $\nabla Q(\theta^\dagger)=0$，则

$$
Q(\theta)-Q(\theta^\dagger)=\tfrac12|\theta-\theta^\dagger|^2+D_\Lambda(\theta\mid\theta^\dagger)\ \ge 0.
$$

---

## 3. "软→硬"：Γ-极限与度量校准

### 3.1 温度极限（Γ-极限）

对 $\beta>0$，置 $\Lambda_\beta(\theta)=\beta^{-1}\log\!\int e^{\beta\langle\theta,\Phi\rangle}d\nu$。则 $\Lambda_\beta$ epi-收敛到 $\sigma_{\mathcal C}$，$\Lambda_\beta^\ast$ epi-收敛到 $\iota_{\mathcal C}$。此处上确界为 $\nu$-本质上确界；由于以闭凸包闭合，支撑函数与原子像集在零测集改动下保持一致。若 $\Phi$ 有界，则

$$
X_\beta:=\arg\min_X\Bigl\{\tfrac12|X-F|^2+\Lambda_\beta^\ast(X)\Bigr\}\ \xrightarrow[\beta\to\infty]{}\ \Pi_{\mathcal C}(F),
$$

且最小值下降至 $\tfrac12|\Pi_{\mathcal C}(F)-F|^2$[^AttouchWets89]。在 $\Phi$ 有界、$\nu$ 有限下，$\Theta\neq\varnothing$，$g_\beta$ 至少 1-强凸（极小元唯一）；若 $\nabla\Lambda_\beta$ 为 $L_\beta$-Lipschitz，则 $g_\beta$ $(1+1/L_\beta)$-强凸。全序列收敛；epi-收敛加唯一解给出 $X_\beta\to\Pi_{\mathcal C}(F)$。

### 3.2 度量校准与内点情形

> **注**：下述校准仅用于理论估计与局部等距，不改变前述投影与 KKT 结论的有效性。

**附加假设**：设存在有界正算子 $C\succ0$ 与参考内积 $\langle\cdot,\cdot\rangle_0$ 使

$$
\nabla^2\Lambda(\theta^\sharp)=C,\qquad \langle x,y\rangle=\langle Cx,y\rangle_0\quad(\text{度量校准}).
$$

在 Legendre 条件下，存在唯一软极小元 $(\theta^\sharp,X^\sharp)$ 使

$$
\boxed{\ X^\sharp=\nabla\Lambda(\theta^\sharp),\qquad \theta^\sharp=F-X^\sharp\ }.
$$

该对偶参数化仅对应**软问题**。**硬投影** $X^\ast=\Pi_{\mathcal C}(F)$ 满足 $F-X^\ast\in N_{\mathcal C}(X^\ast)$；一般 $X^\ast\neq X^\sharp$，但当 $\beta\to\infty$ 时 $X_\beta\to X^\ast$（见 §3.1）。若 $\Pi_{\mathcal C}(F)\in\operatorname{ri}(\mathcal C)$ 则必有 $F=X^\ast$，此时软/硬解一致当且仅当 $\nabla\Lambda(0)=F$。

对任意 $X=\nabla\Lambda(\theta_X)\in\operatorname{ri}(\mathcal C)$，成立

$$
g(X)-g(X^\sharp)=\tfrac12|X-X^\sharp|^2+D_{\Lambda^\ast}(X\mid X^\sharp)\ \ge 0.
$$

若 $\Pi_{\mathcal C}(F)\notin\operatorname{ri}(\mathcal C)$，则对某温度序列 $\beta\to\infty$ 可取 $X_\beta\in\operatorname{ri}(\mathcal C)$ 使 $X_\beta\to \Pi_{\mathcal C}(F)$。

> 说明：群表示的等距/不可约与对称化可**局部**实现 Fisher—Hilbert 的度量校准（至多相差正定因子）[^Amari16]。度量校准的作用定位为局部误差估计与内蕴几何对齐，而非建立软/硬解的点态等同。

---

## 4. 信息—能量—灵敏度不等式

设在最优点邻域

$$
\mu I\ \preceq\ \nabla^2\Lambda(\theta)\ \preceq\ L I,\qquad \operatorname*{ess\,sup}_\xi|\Phi(\xi)|\le R.
$$

### 4.1 强凸/平滑 $\Rightarrow$ $g$-gap 二次下界

由谱界得 $\nabla\Lambda$ 为 $L$-Lipschitz，$\Lambda^\ast$ 为 $(1/L)$-强凸，故

$$
\boxed{\ g(X)-g(X^\sharp)\ \ge\ \tfrac12|X-X^\sharp|^2+\tfrac{1}{2L}|X-X^\sharp|^2\ =\ \tfrac12\bigl(1+\tfrac1L\bigr)|X-X^\sharp|^2\ }.
$$

### 4.2 KL—$g$-gap—灵敏度链

指数族下 $\Lambda$ 为 $\mu$-强凸，且 $\nabla\Lambda$ 的 Lipschitz 常数为 $L$，因此 $|X-X^\sharp|\le L|\theta_X-\theta^\sharp|$。从而

$$
\mathrm{KL}(p_{\theta_X}\,|\,p_{\theta^\sharp})=D_\Lambda(\theta_X\mid\theta^\sharp)\ \ge\ \frac{\mu}{2}|\theta_X-\theta^\sharp|^2\ \ge\ \boxed{\ \frac{\mu}{2L^2}|X-X^\sharp|^2\ }.
$$

由 §4.1 与上式得

$$
\boxed{\ \min\Bigl\{\ \mathrm{KL}(p_{\theta_X}\,|\,p_{\theta^\sharp}),\ g(X)-g(X^\sharp)\ \Bigr\}\ \ge\ \min\Bigl\{\tfrac{\mu}{2L^2},\ \tfrac12\bigl(1+\tfrac1L\bigr)\Bigr\}\,|X-X^\sharp|^2\ }.
$$

另一方面（上界方向），由 $\operatorname*{ess\,sup}|\Phi|\le R$ 与 Csiszár–Pinsker，

$$
|X-X^\sharp|=\Bigl|\int \Phi\,(p_{\theta_X}-p_{\theta^\sharp})\,d\nu\Bigr|
\le R\,|p_{\theta_X}-p_{\theta^\sharp}|_{L^1(\nu)}\ \le\ R\sqrt{2\,\mathrm{KL}(p_{\theta_X}\,|\,p_{\theta^\sharp})}.
$$

### 4.3 稳定性：硬投影与软极小元

**硬投影（与 $\nu$ 无关）**：

$$
|\Pi_{\mathcal C}(\widehat F)-\Pi_{\mathcal C}(F)|\ \le\ |\widehat F-F|\ =\ \varepsilon .
$$

**软极小元（依赖 $\nu$）**：记
$X_\beta^{(\nu)}:=\arg\min_X\{\tfrac12|X-F|^2+\Lambda_{\beta}^{(\nu)\ast}(X)\}$。令 $\bar\nu=\nu/\nu(\mathcal J)$、$\bar{\widehat\nu}=\widehat\nu/\widehat\nu(\mathcal J)$ 为归一化概率测度，若 $\operatorname{TV}(\bar{\widehat\nu},\bar\nu)\le\delta$，Hessian 在最优点邻域一致有界，则

$$
\bigl|X_\beta^{(\widehat\nu)}-X_\beta^{(\nu)}\bigr|\ \le\ C_2\,\delta,\qquad
\Bigl|\min g_{\widehat F}^{(\widehat\nu)}-\min g_{F}^{(\nu)}\Bigr|\ \le\ (1+\kappa_F)\varepsilon+C_3\,\delta,
$$

其中常数 $C_2,C_3$ 与最优点邻域一致的 Hessian 界及 $\operatorname*{ess\,sup}|\Phi|$ 有关，$\kappa_F$ 为 $|\nabla g|$ 的局部 Lipschitz 常数。令 $\beta\to\infty$，由 §3.1 将软极小元逼近到硬投影。

---

## 5. Nyquist–Poisson–EM 三分解与非渐近闭合

约定傅里叶变换 $\widehat g(\omega)=\int_{\mathbb R}g(u)e^{-i\omega u}\,du$。令 $g\in L^1(\mathbb R)\cap C^{2M}(\mathbb R)$ 且导数 $g^{(2j)}\in L^1$。对步长 $\Delta>0$ 与截断 $T>0$：

$$
\left|\int_{\mathbb R} g(u)\,du-\Delta\sum_{|k|\le T/\Delta} g(k\Delta)\right|
\le \underbrace{\sum_{m\neq 0}\bigl|\widehat g(2\pi m/\Delta)\bigr|}_{\text{别名}}
+\underbrace{\sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\,|g^{(2j)}|_{L^1}}_{\text{伯努利层}}
+\underbrace{\int_{|u|>T}|g(u)|\,du}_{\text{截断}}.
$$

满足 **Paley–Wiener 带限假设**（$\widehat g(\omega)=0$ 于 $|\omega|>\Omega$）且采样间隔 $\Delta\le\pi/\Omega$ 时，**别名项为零**（本文取 Shannon 采样条件作保守选取；充要条件为 $2\pi/\Delta>2\Omega$）；指数窗仅得到指数小的别名。将该上界逐项作用于构成 $\widehat F$ 的各积分核，得 $|F-\widehat F|\le \mathfrak E(\Delta,M,T)$ 的显式估计；代入 §4.3 获得投影与最小值的**非渐近**误差闭合。

因窗/核在工作条带解析，且 Euler–Maclaurin 仅取有限阶 $M$，增添层为整/全纯叠加，不引入非解析换序，故"**极点=主尺度**"保持。

---

## 6. 与 S15–S19 的接口

* **S15（Weyl–Heisenberg 酉表示）**：原子族可取 $\Phi_{\tau,\sigma}=U_\tau V_\sigma\Phi_0$。等距与对称化可**局部**实现 Fisher—Hilbert 的度量校准（至多相差正定因子），据此在 $g$ 上得到锐平的几何—信息对应。
* **S16（de Branges–Krein 规范系统）**：取核截面或边界评估为原子，$\operatorname{Cov}_{p_\theta}[\Phi]$ 与传递矩阵通量守恒相容，支撑 Legendre 与校准。
* **S17（散射酉/对称）**：边界振幅的指数族参数 $\theta$ 的最优性与 Herglotz–Nevanlinna 相位导数一致；KL—$g$-gap 给出窗化相位/密度的稳定下界。
* **S18（窗化迹公式）**：$\widehat F$ 的生成受 §5 上界直接控制；带限 + Nyquist 时别名项消失。
* **S19（谱图与 Ihara ζ）**：原子若来自非回溯传播或邻接谱分量，$\mathcal C$ 的投影与 Ihara–Bass 行列式的自倒数镜像兼容；完成函数的镜像对称提供可检基准。

---

## 7. 例与结构模板

1. **Gabor/RKHS 原子**：$\Phi_{\tau,\sigma}=U_\tau V_\sigma g$；Hessian 为协方差算子，群平均实现局部校准。
2. **de Branges 截面**：$\Phi(t)=k_{x(t)}$；$\nabla^2\Lambda$ 等于核 Gram 算子限制，天然正定并与规范系统对齐。
3. **BN–ζ 原型**：$\mathcal H=L^2(0,1)$，$\Phi$ 取 Nyman–Beurling 片段；温度极限 $\beta\to\infty$ 给出到闭凸包的硬投影。

---

## 8. 可检清单（最小充分条件）

1. **空间/原子**：给出 $(\mathcal H,K)$ 与强可测 $\Phi$；$\mathcal C=\overline{\operatorname{conv}}\{\Phi(\xi)\}$ 闭凸，$\operatorname{ri}(\mathcal C)\neq\varnothing$。
2. **信息势**：$\Theta$ 非空开凸；$\Lambda$ Legendre 型；$\nabla\Lambda:\Theta\to\operatorname{ri}(\mathcal C)$ 双射，$\operatorname{dom}\Lambda^\ast=\overline{\mathcal C}$，且 $\operatorname{ri}(\operatorname{dom}\Lambda^\ast)=\operatorname{ri}(\mathcal C)$。
3. **对偶/KKT**：硬投影满足 $\theta^\ast=F-X^\ast$ 与 $\theta^\ast\in N_{\mathcal C}(X^\ast)$；软极小元满足 $\theta^\sharp=F-X^\sharp$ 与 $X^\sharp=\nabla\Lambda(\theta^\sharp)$。
4. **校准/内点**：用度量校准得软极小元 $X^\sharp=\nabla\Lambda(\theta^\sharp)$；通过温度极限 $\beta\to\infty$ 逼近硬投影 $X^\ast=\Pi_{\mathcal C}(F)$。
5. **强凸/平滑**：给出 $(\mu,L)$ 谱界（$\mu I\preceq\nabla^2\Lambda\preceq LI$）与原子有界度 $\operatorname*{ess\,sup}|\Phi|\le R$；验证 §4 的不等式链。
6. **窗化/EM**：解析窗/核，**有限阶** EM；据 §5 给出 $|F-\widehat F|$ 的非渐近上界。
7. **奇性保持**：全流程不引入非解析换序；"极点=主尺度"保持。

---

## 参考文献

[^Rockafellar70]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.

[^BauschkeCombettes11]: H. H. Bauschke, P. L. Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*, Springer, 2011.

[^Amari16]: S. Amari, *Information Geometry and Its Applications*, Springer, 2016.

[^AttouchWets89]: H. Attouch, R. J.-B. Wets, *Quantitative Stability of Variational Systems*, SIAM Journal on Optimization, 1989.

---

## 结语

以 Legendre 信息势为桥梁，本文把 BN 混合集上的几何投影（硬投影）与指数族的最小相对熵（软极小元）统一到目标函数 $g$ 的 Bregman 几何之中：在内点与度量校准下获得互反参数化与精确毕达哥拉斯；在 Γ-极限下实现由软极小元到硬投影的收敛；以强凸/平滑—Pinsker—灵敏度链刻画信息、能量与几何偏差的共同控制；以 Nyquist–Poisson–EM 三分解实现数值层面的非渐近闭合并保持奇性结构。该范式与 S15–S19 的表示—规范—散射—谱图接口一致，为连续谱阈值与奇性稳定的后续研究提供统一的度量与优化语言。
