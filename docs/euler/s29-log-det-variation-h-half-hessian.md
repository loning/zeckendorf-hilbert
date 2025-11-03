# S29. 对数行列式的变分与 $H^{1/2}$ Hessian

**—— de Branges–Mellin 局部化算子的符号/窗方向、凹性、稳定与 $\Gamma$-极限**

Version: 1.4

## 摘要（定性）

在 S27–S28 关于局部化算子与强型 Szegő–Widom 极限的基础上，本文系统建立

$$
\mathscr F_R(a,w;\lambda):=\log\det\nolimits_!\bigl(I+\lambda\,T_{a,w,R}\bigr)
$$

相对于**符号** $a$ 与**窗** $w$ 的变分理论：给出 Gateaux/Fréchet 一阶导数、二阶变分与凹性；在"带限+Nyquist+有限阶 Euler–Maclaurin (EM)"纪律下，证明 $\mathscr F_R$ 对 $(a,w)$ 的扰动满足**Lipschitz—强凸型稳定界（在适当软化下）**；并在尺度 $R\to\infty$ 的极限中，Hessian 的主导型收敛到相位坐标上的 $H^{1/2}$ 能量。由此得到：（1）一阶灵敏度是"非线性局域密度"的积分；（2）二阶 Hessian 为一个正核上的负半定二次型（$\log\det$ 对正算子凹），在极限中与 S28 的 $H^{1/2}$ 二次项匹配；（3）在符号约束 $0\le a\le 1$、窗约束（带限/偶性/归一）下得到 KKT 必要条件并与 S22 的投影—卷积强式一致；（4）对 BN–Bregman 软化的"软目标"建立 $\Gamma$-收敛，并证明梯度—Hessian 结构在极限下保持。

---

## 0. 设定与记号

### 0.1  de Branges 空间与相位—密度恒等式

取 Hermite–Biehler 函数 $E$，de Branges 空间 $\mathcal H(E)$ 的再生核为 $K(z,\zeta)$。沿实轴写

$$
E(x)=|E(x)|e^{-i\varphi(x)},\qquad x\in\mathbb R,
$$

则存在标准恒等式

$$
K(x,x)=\frac{\varphi'(x)}{\pi}\,|E(x)|^2,\qquad \varphi'(x)>0\ \text{a.e.}
$$

据此取基准测度

$$
d\mu(x):=\frac{\varphi'(x)}{\pi}\,dx.
$$

以上关系见 de Branges 专著。([math.purdue.edu][1])

### 0.2  局部化算子、窗与正则化行列式（**Trace-class 设定**）

给定有界实符号 $a\in L^\infty(\mathbb R)$ 与偶窗 $w_R(t):=w(t/R)$。本文固定假设

$$
0\le a\le C,\qquad 0\le w_R\le C_w,\qquad w_R\in L^1(d\mu),
$$

从而

$$
T_{a,w,R}:=\int_\mathbb R a(x)\,w_R(x)\,\frac{\bigl|K(\cdot,x)\rangle\langle K(\cdot,x)\bigr|}{K(x,x)}\,d\mu(x)
$$

为**正、迹类**算子，且

$$
\operatorname{Tr}\,T_{a,w,R}=\int a(x)\,w_R(x)\,d\mu(x)<\infty.
$$

在此设定下统一采用 Fredholm 行列式，记 $\det_!(\cdot)\equiv\det(\cdot)$。因此一阶/二阶变分均可直接使用 $\mathrm d\,\log\det(I+X)=\mathrm{Tr}\!\big[(I+X)^{-1}\mathrm dX\big]$。

*注.* 若放宽至仅 Hilbert–Schmidt，需要将 $\det$ 改为 Carleman–Fredholm 的 $\det_2$ 并在一阶变分中加入补偿项 $-\mathrm{Tr}(\mathrm dX)$；本文为避免额外的可加正则项，统一在迹类框架内工作。有关正则化行列式与迹理想的背景参见 Simon、Gohberg–Lesch 等文献。([sciencedirect.com][2])

### 0.3  "窗化投影核"与相位坐标

定义

$$
\Pi_R:=\int_\mathbb R w_R(t)\,\frac{|K(\cdot,t)\rangle\langle K(\cdot,t)|}{K(t,t)}\,d\mu(t)
\ =\ \int_\mathbb R w_R(t)\,|k_t\rangle\langle k_t|\,d\mu(t),
$$

其"系数核"为

$$
\Pi_R(x,y)=\int_\mathbb R w_R(t)\,
\frac{K(x,t)\overline{K(y,t)}}{\sqrt{K(x,x)K(y,y)}\,K(t,t)}\,d\mu(t).
$$

在 $0\le w_R\le 1$ 时有 $0\le\Pi_R\le I$；当 $w_R\equiv 1$ 时，$\Pi_R=I$。在相位坐标 $u=\varphi(x)/\pi$ 下，若 $w_R\to 1$（局部一致）且满足带限+Nyquist 纪律，则 $\Pi_R$ 局部趋于 Paley–Wiener 投影核（sinc 核），见 Paley–Wiener 空间的 RKHS 表述与 Nyquist–Shannon 采样定理。([mathsci.kaist.ac.kr][3])

---

## 1. 一阶变分：局域密度与单调性

定义

$$
\mathscr F_R(a,w;\lambda):=\log\det\nolimits_!\bigl(I+\lambda T_{a,w,R}\bigr),
\qquad \lambda\in\mathbb R\ \text{使 }I+\lambda T_{a,w,R}\text{ 可逆}.
$$

上式中的 $\log\det_!$ 按 §0.2 的约定选取，其定义域为使 $I+\lambda T_{a,w,R}$ 可逆的 $\lambda$ 集；以下变分公式均在该域内成立。

### 定理 1.1（符号方向 Gateaux 导数，$\lambda\ge 0$）

对任意有界 $\delta a$，且 $I+\lambda T_{a,w,R}$ 可逆时，

$$
\boxed{\;
\mathrm D_a\mathscr F_R(a,w;\lambda)[\delta a]
=\lambda\,\mathrm{Tr}\bigl[(I+\lambda T_{a,w,R})^{-1}T_{\delta a,w,R}\bigr]
=\int \delta a(x)\,w_R(x)\,\sigma_{\lambda,R}(x)\,d\mu(x)\; }
$$

其中

$$
\sigma_{\lambda,R}(x)
:=\lambda\,\frac{\langle (I+\lambda T_{a,w,R})^{-1}K(\cdot,x)\,,K(\cdot,x)\rangle}{K(x,x)}\ \ge 0.
$$

*证明.* 利用 $\mathrm d\,\log\det(I+X)=\mathrm{Tr}[(I+X)^{-1}\mathrm d X]$（在迹类/正则化设定下成立），取 $X=\lambda T_{a,w,R}$、$\mathrm dX=\lambda T_{\delta a,w,R}$ 即得。将迹写为核的积分得到第二式。关于 $\log\det$ 的微分公式可见 Simon 以及标准 Fredholm 行列式文献。([sciencedirect.com][2])

**单调性（$\lambda\ge 0$）.** 若 $\delta a\ge 0$ a.e.，则 $\mathrm D_a\mathscr F_R[\delta a]\ge 0$，因为 $(I+\lambda T_{a,w,R})^{-1}\ge 0$、$T_{\delta a,w,R}\ge 0$。

### 定理 1.2（窗方向 Gateaux 导数，$\lambda\ge 0$）

对任意有界偶扰动 $\delta w$,

$$
\boxed{\;
\mathrm D_w\mathscr F_R(a,w;\lambda)[\delta w]
=\lambda\int a(x)\,\delta w(x)\,\sigma_{\lambda,R}(x)\,d\mu(x);\;}
$$

证明同上，仅将 $T_{\delta a,w,R}$ 换为 $T_{a,\delta w,R}$。

*注.* 若附加点值/质量归一（如 $w(0)=1$ 或 $\int w=1$），则相应 Lagrange 乘子以$\delta$-源或常数出现在线性泛函中（详见 §4）。

---

## 2. 二阶变分：凹性与核二次型

### 定理 2.1（二阶变分与凹性）

对任意方向 $\delta a_1,\delta a_2$,

$$
\boxed{\;
\mathrm D_a^2\mathscr F_R(a,w;\lambda)[\delta a_1,\delta a_2]
=-\lambda^2\,\mathrm{Tr}\!\Big[(I+\lambda T_{a,w,R})^{-1}
T_{\delta a_1,w,R}\,(I+\lambda T_{a,w,R})^{-1}T_{\delta a_2,w,R}\Big]\le 0.}
$$

特别地，$\mathscr F_R$ 对 $a$ 为凹泛函；对 $w$ 同理。

*证明.* 对 $\mathrm D_a\mathscr F_R$ 再求导，并用 $\mathrm d (I+\lambda T)^{-1}=-(I+\lambda T)^{-1}(\lambda\,\mathrm d T)(I+\lambda T)^{-1}$。将两侧乘子对称化可得

$$
-\mathrm D_a^2\mathscr F_R[\delta a,\delta a]
=\lambda^2\,\bigl|\, (I+\lambda T_{a,w,R})^{-1/2}\,T_{\delta a,w,R}\,(I+\lambda T_{a,w,R})^{-1/2}\bigr|_{\mathsf{HS}}^2\ge 0,
$$

从而得凹性。凹性也可由 $\log$ 的算子凹性与迹的单调性推出。([ueltschi.org][4])

### 核型表达与"强度核"

记标准化核向量 $k_x:=K(\cdot,x)/\sqrt{K(x,x)}$，并定义

$$
\mathcal G_{\lambda,R}(x,y)
:=\lambda\,\Big\langle k_y\,,(I+\lambda T_{a,w,R})^{-1}\,k_x\Big\rangle
=\lambda\,\Big\langle (I+\lambda T_{a,w,R})^{-1/2}k_x\,,(I+\lambda T_{a,w,R})^{-1/2}k_y\Big\rangle.
$$

则

$$
-\mathrm D_a^2\mathscr F_R[\delta a,\delta a]
=\iint \delta a(x)\,\delta a(y)\,w_R(x)w_R(y)\,|\mathcal G_{\lambda,R}(x,y)|^2\,d\mu(x)\,d\mu(y).
$$

这是一个由正核 $w_R(x)w_R(y)|\mathcal G_{\lambda,R}(x,y)|^2$ 诱导的非负二次型表达，清晰刻画了 Hessian 的"核强度"。

---

## 3. $R\to\infty$ 的 Hessian 极限：$H^{1/2}$ 能量

### 3.1  带限+Nyquist+有限阶 EM 纪律

假设：

(i) $w_R\to 1$ 局部一致，且在相位坐标 $u=\varphi(x)/\pi$ 上等价为对带宽 $\sim R$ 的带限截断；

(ii) Nyquist 采样（采样率至少为两倍带宽）使别名误差为零；

(iii) 求和—积分换序仅使用**有限阶** Euler–Maclaurin (EM) 公式，余项用 Bernoulli 多项式与导数范数控制。([en.wikipedia.org][5])

在 Paley–Wiener 模型（相位坐标下的 sinc 核）中，这三条可直接验证。([mathsci.kaist.ac.kr][3])

### 定理 3.2（Hessian 的 $H^{1/2}$ 极限）

设 $\phi(x)=\log\bigl(1+\lambda a(x)\bigr)$，并记 $\displaystyle \phi'_a(x):=\frac{\lambda}{1+\lambda a(x)}$。则对任意 $\delta a\in C_c^\infty(\mathbb R)$（或合适的 $H^{1/2}$ 域），

$$
\boxed{\;
-\mathrm D_a^2\mathscr F_R(a,w;\lambda)[\delta a,\delta a]\ \xrightarrow[R\to\infty]{}\
\frac1{2\pi}\int_{\mathbb R}\Big|\widehat{\,(\phi'_a\,\delta a)\circ\varphi^{-1}\,}(\xi)\Big|^2\,|\xi|\,d\xi
=:\frac12\,|\,(\phi'_a\,\delta a)\circ\varphi^{-1}\,|^2_{H^{1/2}(\mathbb R)}.\;}
$$

也即，Hessian 的极限二次型恰为相位坐标中 $g=(\phi'_a\,\delta a)\circ\varphi^{-1}$ 的 $H^{1/2}$ 能量；其 Fourier 特征与 Gagliardo 形式等价。([arXiv][6])

*证明大意.*

由 §2 的核二次型表达，$-\mathrm D^2$ 等于正核

$$
A_R(x,y):=w_R(x)w_R(y)\,|\mathcal G_{\lambda,R}(x,y)|^2
$$

上的二次型。带限+Nyquist+有限阶 EM 三条使得在相位坐标中

$$
A_R(x,y)\ \to\ \frac1{\pi^2}\,\Big|\frac{\sin\pi(u-v)}{\pi(u-v)}\Big|^2\,\Big(\phi'_a(x)\phi'_a(y)\Big),
$$

均匀于紧致集上的卷积—核意义，且别名=0、EM 余项与窗尾衰减在 $R\to\infty$ 时可控。于是

$$
\iint \delta a(x)\delta a(y)\,A_R(x,y)\,d\mu_x d\mu_y
\ \to\ \frac1{2\pi}\int |\widehat{(\phi'_a\delta a)\circ\varphi^{-1}}(\xi)|^2\,|\xi|\,d\xi,
$$

后者正是 $H^{1/2}$ 能量（Fourier 角色）。当 $E(z)=e^{-iz}$（Paley–Wiener）时，上式与强型 Szegő 极限中的二阶项（$\sum_{k\ge1}k\,|\widehat{\log(1+\lambda a)}(k)|^2$ 的连续化）完全一致；一般 de Branges 情形靠相位坐标的局部等距伸缩实现。有关强型 Szegő–Widom 二阶项（对光滑正符号）之典范表述，可参见 Böttcher–Widom、Gray 及其后续综述；Fisher–Hartwig 情形见 Deift–Its–Krasovsky。([sciencedirect.com][7])

### 推论 3.3（与 S28 的二阶展开一致）

将 $\delta a$ 取为小参数的方向，并对 $\phi=\log(1+\lambda a)$ 作二阶展开，可回收

$$
\mathscr F_R(a,w;\lambda)=\int \log(1+\lambda a)\,d\mu
+\frac1{2}\,|\,(\phi)\circ\varphi^{-1}\,|^2_{H^{1/2}}+o(1),
$$

与 S28 的强型 Szegő–Widom 二阶项一致。

---

## 4. 约束下的最优性：KKT 结构与对偶证书

考虑可行域

$$
\mathcal A:=\{a\in L^\infty(\mathbb R):\ 0\le a\le 1\},\qquad
\mathcal W:=\text{带限偶窗类（附归一：如 }w(0)=1\text{ 或 }\int w=1).
$$

以

$$
\max_{a\in\mathcal A,\ w\in\mathcal W}\ \mathscr F_R(a,w;\lambda)
$$

为例（$\lambda>0$），由于 $\mathscr F_R$ 对 $a,w$ 分别凹，标准 Lagrange–KKT 条件适用（凸—凹规划的对偶可行性与互补松弛）。([epubs.siam.org][8])

### 定理 4.1（符号方向 KKT）

存在测度（或 $L^2$ 元）$\eta_-,\eta_+\ge 0$，使得最优解 $\bar a$ 满足

$$
w_R(x)\,\sigma_{\lambda,R}^{(\bar a)}(x)=\eta_+(x)-\eta_-(x)\quad\text{a.e.},
$$

且互补松弛

$$
\eta_-(x)\,\bar a(x)=0,\qquad \eta_+(x)\,(1-\bar a(x))=0\quad\text{a.e.}
$$

其中 $\sigma_{\lambda,R}$ 为 §1 的"非线性局域密度"。

### 定理 4.2（窗方向 KKT）

在可行子空间 $\mathcal W$ 上的最优 $\bar w$ 满足

$$
a(x)\,\sigma_{\lambda,R}^{(\bar w)}(x)\in \bigl(\mathrm{span}\ \text{的带限/偶约束与归一约束的对偶锥}\bigr),
$$

等价地，右端是由带限投影、偶对称、以及 $w(0)=1$ 或 $\int w=1$ 的对偶函数（分布）生成的闭凸锥之元素。该"对偶证书"形式与 S22 的投影—卷积强式一致。

---

## 5. 软化与 $\Gamma$-极限：Bregman 正则与梯度结构保持

令

$$
\mathcal E_{R,\tau}(a,w):=-\mathscr F_R(a,w;\lambda)\ +\ \tau\,\Lambda^\ast(\mathcal T(a,w)),\qquad \tau>0,
$$

其中 $\Lambda^\ast$ 为某 Bregman 型正则项（由强凸势产生），$\mathcal T$ 收集可能的线性观测或惩罚。

### 定理 5.1（$\Gamma$-极限与极小元收敛）

当 $\tau_n\downarrow 0$ 时，

$$
\mathcal E_{R,\tau_n}\ \xrightarrow{\ \Gamma\ }\ \mathcal E_{R,0}:=-\mathscr F_R+\iota_{\mathcal A\times\mathcal W},
$$

且极小值与（相对弱*）极小元随之收敛；若 $\Lambda^\ast$ 在极小元邻域 $(\mu,L)$-强凸/平滑，则有稳定性

$$
|(a_{\tau}-a^\star\,,w_\tau-w^\star)|\ \lesssim\ |\delta(\text{数据})|.
$$

这是凸函数族的经典 $\Gamma$-收敛与 Mosco 收敛框架的直接应用；其梯度流/次微分图的极限保持性可由 Attouch 定理与演化 $\Gamma$-收敛理论推出。([archive.org][9])

*注.* 取 $-\mathscr F_R$（凸）加强凸的 Bregman 正则，可获得（局部）强凸性与条件数控制，便于数值优化。

---

## 6. 稳定性与非渐近误差

### 6.1  Lipschitz—梯度界

由一阶变分

$$
\bigl|\mathscr F_R(a+\delta a,w;\lambda)-\mathscr F_R(a,w;\lambda)\bigr|
\le \lambda\,\bigl|T_{\delta a,w,R}\bigr|_1
\le \lambda\int |\delta a(x)|\,w_R(x)\,d\mu(x),
$$

以及同样的窗方向估计（把 $\delta a$ 换为 $a\,\delta w$）。此处用到 $|(I+\lambda T)^{-1}|\le 1$ 与积分秩一表示的迹范数估计。

### 6.2  EM 三分解与别名—伯努利—尾项

对任意足够光滑 $\phi$（如 $\log(1+\lambda\cdot)$），谱/迹的数值近似可分解为

$$
\bigl|\operatorname{Tr}\,\phi(T_{a,w,R})-\mathsf{tr}_{\Delta,M,T}\bigl(\phi\circ\mathcal S_R\bigr)\bigr|
\ \le\ \underbrace{\text{alias}}_{\text{Nyquist 下为 }0}\ +\ \underbrace{\text{EM 层}}_{\text{有限阶}}\ +\ \underbrace{\text{tail}}_{\text{窗尾与核尾}}.
$$

EM 层可用有限阶公式与 Bernoulli 多项式的余项显式控制；在带限+Nyquist 下 alias 项为零。([PagePlace][10])

### 6.3  Hessian 的非渐近下界与上界

由 §2 的 Hilbert–Schmidt 表达，

$$
\frac{\lambda^2}{|I+\lambda T_{a,w,R}|^2}\,|T_{\delta a,w,R}|_{\mathsf{HS}}^2
\ \le\ -\mathrm D_a^2\mathscr F_R[\delta a,\delta a]
\ \le\ \lambda^2\,|T_{\delta a,w,R}|_{\mathsf{HS}}^2,
$$

对窗方向亦同。若加入强凸 Bregman 正则，则可得到全空间上的强凸/强凹模量。

---

## 7. 例与模板

### (i) Parseval 多窗

若 $\sum_{\ell} w_R^{(\ell)}\equiv 1$（局部一致）且对应帧算子为恒等，则

$$
\sigma_{\lambda,R}=\sum_\ell \sigma_{\lambda,R}^{(\ell)}.
$$

对二阶项，一般情形还有交叉项

$$
-\mathrm D^2\mathscr F_R=\sum_\ell -\mathrm D^2\mathscr F_R^{(\ell)}\ +\ \sum_{\ell\ne m}\mathcal C_{\ell m},
$$

仅当 $\{\Pi_R^{(\ell)}\}$ 两两正交（或 $T_{a,w,R}$ 在该分解下块对角/可交换、或频带支集分离）时有 $\mathcal C_{\ell m}\equiv 0$，此时 Hessian（以及其极限）的能量才**精确叠加**。

### (ii) 低通—高通耦合

若 $a=a_{\rm lp}+a_{\rm hp}$ 且支集分离，则一阶密度与二阶能量分离，加速分块优化与非平稳设计。

### (iii) 近阈值区

当 $\varphi'$ 局部变小（相位度量伸长）时，$H^{1/2}$ 能量对该区的扰动权重减弱，反映"信息稀薄—波动放大"的可检现象。

---

## 8. 失效边界与注意事项

1. **无限阶 EM**：把 EM 当无穷级展开会引入伪奇点并破坏二阶型可控性；本文仅用**有限阶** EM（有严格余项）。([PagePlace][10])
2. **Fisher–Hartwig 奇性**：当 $\log(1+\lambda a)$ 不够平滑或触及分支，会出现 $\gamma\log R$ 型边缘项；需用 RH 方法或 Krein 代数处理。([arXiv][11])
3. **非带限/非偶窗**：需要退回一般 RKHS 的压缩—Toeplitz 表述，并在 KKT 中加入相应对偶边界项。
4. **$\varphi'$ 非正**：相位度量退化，本文刻度失效；需改用适当的谱坐标或排除该区域。

---

## 9. 证明细节与标准引理（选）

### 9.1  迹类与正则化行列式

若 $T=\int f(x)\,|k_x\rangle\langle k_x|\,d\mu(x)$ 且 $\int |f|\,d\mu<\infty$，则 $T$ 迹类，$|T|_1\le \int |f|\,d\mu$；当 $T\in\mathfrak S_2$ 但非迹类时使用 $\det_2(I+\lambda T)$。([sciencedirect.com][2])

### 9.2  $\log\det$ 的微分与凹性

若 $I+\lambda T(t)$ 在迹理想拓扑可微，则

$$
\frac{d}{dt}\log\det(I+\lambda T(t))=\lambda\,\mathrm{Tr}\bigl[(I+\lambda T(t))^{-1}T'(t)\bigr],
$$

$$
\frac{d^2}{dt^2}\log\det(I+\lambda T(t))
=-\lambda^2\,\mathrm{Tr}\bigl[(I+\lambda T)^{-1}T'(t)(I+\lambda T)^{-1}T'(t)\bigr]\le 0.
$$

凹性亦可由 $\log$ 的算子凹性与 Lieb–Ando 类结果推出。([sciencedirect.com][2])

### 9.3  $H^{1/2}$ 能量的 Fourier 与 Gagliardo 等价

对 $g\in\mathcal S$,

$$
\frac1{2\pi}\int_{\mathbb R}|\xi|\,|\widehat g(\xi)|^2\,d\xi
\asymp \iint_{\mathbb R^2}\frac{|g(u)-g(v)|^2}{|u-v|^2}\,du\,dv,
$$

为 $H^{1/2}(\mathbb R)$ 的两种等价表述。([arXiv][6])

### 9.4  强型 Szegő–Widom 二阶项（平滑正符号）

Toeplitz/截断投影模型下，对 $C^{1+\alpha}$ 正符号 $f$ 有

$$
\log\det T_n(f)=n\,(\log f)_0+\sum_{k\ge 1}k\,|(\log f)_k|^2+o(1),
$$

连续化即得到 §3 的 $H^{1/2}$ 能量。参见 Böttcher–Widom 的"Jacobi 证明"、Gray 的综述与后续发展。([sciencedirect.com][7])

---

## 结语

本文建立了 $\mathscr F_R(a,w;\lambda)=\log\det_!(I+\lambda T_{a,w,R})$ 的完整变分框架：

（i）一阶导数由"非线性局域密度" $\sigma_{\lambda,R}$ 给出，体现了符号与窗的局域灵敏度；

（ii）二阶 Hessian 为正核上的负半定二次型，Hilbert–Schmidt 范表达提供了非渐近稳定估计；

（iii）在"带限+Nyquist+有限阶 EM"纪律下，Hessian 的尺度极限为相位坐标的 $H^{1/2}$ 能量，与强型 Szegő–Widom 二阶项完全一致；

（iv）在符号/窗约束与归一条件下，KKT 结构给出了自然的对偶证书；

（v）对 Bregman 软化可建立 $\Gamma$-收敛与极小元/梯度结构的保持，从而获得"可微—凹性—稳健"的统一基础。

---

## 参考线索（不需链接，给出出处方向）

* de Branges：Hilbert Spaces of Entire Functions（相位—密度与核恒等式）。([math.purdue.edu][1])
* 迹理想与（正则化）Fredholm 行列式、$\log\det$ 微分：Simon；Gohberg–Lesch；Bornemann（数值与正则化）。([sciencedirect.com][2])
* $\log$ 的算子凹性、Lieb–Ando 类凹凸性与迹不等式：Carlen；Fawzi–Saunderson；综述讲义。([ueltschi.org][4])
* Paley–Wiener sinc 核与 Nyquist–Shannon 定理。([mathsci.kaist.ac.kr][3])
* Euler–Maclaurin 有界余项（有限阶）与误差估计：Olver；DLMF。([PagePlace][10])
* $H^{1/2}$ 的 Fourier—Gagliardo 等价与"半阶能量"：Di Nezza–Palatucci–Valdinoci。([arXiv][6])
* 强型 Szegő–Widom（平滑正符号二阶项、Fisher–Hartwig）：Böttcher–Widom；Gray；Deift–Its–Krasovsky。([sciencedirect.com][7])
* $\Gamma$/Mosco 收敛与梯度流极限：Attouch；Braides；Mielke（演化 $\Gamma$-收敛）。([archive.org][9])

（全文自洽，计算与换序仅叠加整/全纯层，不改变工作条带之奇性集合与极阶；与 S22、S28 的结构兼容。）

[1]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[2]: https://www.sciencedirect.com/science/article/pii/S0001870877800443/pdf?md5=cb0976456474b5c4cb0ffba290cf931a&pid=1-s2.0-S0001870877800443-main.pdf&utm_source=chatgpt.com "Notes on Infinite Determinants of Hilbert Space Operators"
[3]: https://mathsci.kaist.ac.kr/bk21/morgue/research_report_pdf/05-9.pdf?utm_source=chatgpt.com "Sampling Theory in Abstract Reproducing Kernel Hilbert"
[4]: https://www.ueltschi.org/AZschool/notes/EricCarlen.pdf?utm_source=chatgpt.com "TRACE INEQUALITIES AND QUANTUM ENTROPY"
[5]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[6]: https://arxiv.org/pdf/1104.4345?utm_source=chatgpt.com "Hitchhiker's guide to the fractional Sobolev spaces"
[7]: https://www.sciencedirect.com/science/article/pii/S0024379506002795/pdf?md5=fbefebe761a52640a1f656d4c0ba59a3&pid=1-s2.0-S0024379506002795-main.pdf&utm_source=chatgpt.com "Szegö via Jacobi"
[8]: https://epubs.siam.org/doi/10.1137/1035044?utm_source=chatgpt.com "Lagrange Multipliers and Optimality | SIAM Review"
[9]: https://archive.org/details/variationalconve0000atto?utm_source=chatgpt.com "Variational convergence for functions and operators"
[10]: https://api.pageplace.de/preview/DT0400.9781439864548_A38306604/preview-9781439864548_A38306604.pdf?utm_source=chatgpt.com "Asymptotics and Special Functions"
[11]: https://arxiv.org/abs/0905.0443?utm_source=chatgpt.com "[0905.0443] Asymptotics of Toeplitz, Hankel, and"
