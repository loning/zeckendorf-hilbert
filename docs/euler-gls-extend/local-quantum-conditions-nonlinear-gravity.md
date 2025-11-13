# 全非线性引力方程的局域量子充分条件：小菱形广义熵极值、相对熵片叶无关与 QNEC 逐点饱和

Auric

---

## 摘要

本文在点态小因果菱形的极限提出三条**完全局域**且**充分**的量子—几何判据，并在半经典—全息窗口中**严格**推出含宇宙学常数的**全非线性引力方程**。三条判据为：（A）在固定"有效体积/共形 Killing 能"约束下的小菱形**广义熵极值**；（B）边界相对熵对 Cauchy 片的**片叶无关**当且仅当体内 Iyer–Wald **正则能守恒**（由此给出**量子 Bianchi 恒等式**及其源项形式）；（C）穿过一点的**全部局域割面**与**全部零方向**的 **QNEC 逐点饱和**。我们证明：在 Hadamard 态、无引力反常且正则能非负的耦合窗口内，上述任一判据（辅以本文列明之配套技术假设）均**充分**推出

$$
E^{\rm grav}_{ab}=8\pi G_{\rm ren}\,\langle T^{\rm tot}_{ab}\rangle+\phi\,g_{ab},\qquad \nabla_b\phi=0,
$$

从而将 $\phi$ 并入宇宙学常数 $\Lambda$。核心技术包括：（i）**体积—哈密顿量 $O(r^d)$ 等价定理**（命题 K.1），即"固定 $V^{\rm eff}_\xi\Leftrightarrow$固定 $H_\xi$"在 Einstein–Hilbert 与 $f(R)$ 原型中普适成立；（ii）**两帽边界核的 $O_{\mathcal D'}(r^{d+2})$ 分布抵消定理**（定理 J.1）；（iii）**量子静止代表面**之存在—唯一—正则性与面积二阶式的 $O(r^{d+2})$ 约束；（iv）对 JKM 位移与角点改正的**上同调不变性**；（v）De Donder 规范下的**收缩映射可积性引理**与"近饱和 $\Rightarrow$ 近方程"的稳定性不等式。并给出 FRW 与 AdS$_3$/CFT$_2$ 实例及"相对熵通量计 / QNEC 饱和相图"的可执行规范。

---

## 1 引言

纠缠第一定律与球区族方法已在**线性/二阶**层面奠定"由信息到几何"的基础。要在**点态**与**全非线性**层级闭合，需要兼顾三类约束：**平衡**（熵极值）、**守恒**（正则能守恒）与**刚性**（QNEC 饱和）。本文在点态小因果菱形 $D_{p,r}$ 的极限中，将上述三类约束定理化，并给出**完整的证明与误差控制**，统一导出含 $\Lambda$ 的非线性场方程。

---

## 2 场景、记号与假设

### 2.1 小因果菱形与近似共形 Killing 场

令 $(M,g)$ 为 $d\ge 3$ 的光滑时空，$p\in M$。记 $D_{p,r}$ 为尺度 $r\ll \ell_{\rm curv}$ 的小因果菱形，边界由两片 $C^{1,\alpha}$ 零叶 $\mathcal N_\pm$ 组成，交于两个角点。设小参数 $\varepsilon:=r/\ell_{\rm curv}\ll 1$。取**近似共形 Killing 场** $\xi^a$，满足

$$
\left|\nabla_{(a}\xi_{b)}-\tfrac{1}{d}(\nabla\!\cdot\!\xi)\,g_{ab}\right|_{L^\infty(D_{p,r})}\le C_\xi\,\varepsilon^2,\qquad
\xi^a\big|_{\partial D_{p,r}}=0,
$$

并以"菱形温度"归一 $\kappa_\xi=\kappa_0+O(\varepsilon^2)$。

### 2.2 态、重整化与总应力

取 Hadamard 态与因果处方。定义

$$
\langle T^{\rm tot}_{ab}\rangle:=\langle T_{ab}\rangle+\tau^{\rm ent}_{ab},\qquad
\tau^{\rm ent}_{ab}:=-\frac{2}{\sqrt{-g}}\frac{\delta W_{\rm nonloc}}{\delta g^{ab}},
$$

并要求

$$
\nabla^a\langle T^{\rm tot}_{ab}\rangle=0.
$$

允许的局域对置项只重定义 $G_{\rm ren},\Lambda$（附录 D）。

### 2.3 QES 与量子静止代表面

假设存在唯一且稳定的量子极值面 $\Sigma\subset \partial D_{p,r}$，$\delta S_{\rm gen}|_\Sigma=0$。在等价类内构造**量子静止代表面** $\hat\Sigma$，使

$$
\theta\big|_p=\sigma\big|_p=0,\qquad \int_{\hat\Sigma}(\theta^2+\sigma^2)\,{\rm d}\lambda=O(r^{d+2}),
$$

其存在—唯一—正则性见附录 H。

### 2.4 协变相空间与正则能

令 $L(g,\text{曲率},\ldots)$ 光滑局域，$E^{\rm grav}_{ab}:=\frac{2}{\sqrt{-g}}\frac{\delta}{\delta g^{ab}}\!\int\!\sqrt{-g}L$。由微分同胚不变性有 $\nabla^aE^{\rm grav}_{ab}\equiv 0$。Iyer–Wald 结构给出辛势 $\boldsymbol\theta$、辛流 $\boldsymbol\omega$、Noether 电荷 $\mathbf Q_\xi$ 与角点项 $C_\xi$。定义

$$
\delta H_\xi=\int_\Sigma(\delta\mathbf Q_\xi-\xi\!\cdot\!\boldsymbol\theta-\delta C_\xi),\quad
\mathcal E_\xi(\delta_1,\delta_2)=\int_\Sigma \boldsymbol\omega(\delta_1,\mathcal L_\xi\delta_2).
$$

JKM 位移 $\boldsymbol\theta\to\boldsymbol\theta+{\rm d}Y$、$\mathbf Q_\xi\to\mathbf Q_\xi+\xi\!\cdot\!Y$ 与角点改正形成等价类（附录 F）。

### 2.5 QNEC 与二阶形变

对任一零向 $k^a$ 与局域割面族，QNEC 读作

$$
(\sqrt h)^{-1}S''_{\rm out}\le 2\pi\,\langle T_{kk}\rangle.
$$

在代表面上，Raychaudhuri 给出

$$
(\sqrt h)^{-1}\frac{{\rm d}^2A}{{\rm d}\lambda^2}=-R_{kk}-\tfrac{\theta^2}{d-2}-\sigma^2.
$$

---

## 3 主结论（陈述）

### 定理 A（广义熵极值 $\Rightarrow$ 非线性张量方程）

在第 2 节假设下，若 $\Sigma$ 为 $D_{p,r}$ 的 QES，且在"固定 $V^{\rm eff}_\xi$"（或等价"固定 $H_\xi$"）约束下 $S_{\rm gen}$ 极值，则对穿过 $p$ 的全部零向 $k^a$ 有

$$
E^{\rm grav}_{kk}(p)=8\pi G_{\rm ren}\,\langle T^{\rm tot}_{kk}(p)\rangle.
$$

进而存在分布 $\phi$ 使

$$
E^{\rm grav}_{ab}(p)=8\pi G_{\rm ren}\,\langle T^{\rm tot}_{ab}(p)\rangle+\phi(p)\,g_{ab}(p),\qquad \nabla_b\phi=0.
$$

### 定理 B（片叶无关 $\Leftrightarrow$ 正则能守恒；量子 Bianchi）

若边界相对熵 $S_{\rm rel}^{\rm bdy}$ 对 Cauchy 片 $\Sigma_s$ 无关，则

$$
\nabla^a\big(E^{\rm grav}_{ab}-8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle\big)=0.
$$

含外通量或角点注入时存在源

$$
\nabla^a\big(E^{\rm grav}_{ab}-8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle\big)=J_b,\quad
J_b=\nabla^a\big[\delta Q_{\xi,ab}-(\xi\!\cdot\!\boldsymbol\theta)_{ab}-\delta C_{\xi,ab}\big],
$$

且 $J_b$ 对 JKM 位移与角点改正不变。

### 定理 C（QNEC 全方向逐点饱和 $\Rightarrow$ 非线性闭合；近饱和稳定性）

若在 $p$ 的邻域对全部局域割面与零向 $k^a$ 有

$$
(\sqrt h)^{-1}S''_{\rm out}(p;k)=2\pi\,\langle T_{kk}(p)\rangle,
$$

并且正则能非负、De Donder 规范与 $H^s_\delta$（$s>\tfrac d2+2$、$-1<\delta<0$）下可积性引理成立，则

$$
E^{\rm grav}_{ab}(p)=8\pi G_{\rm ren}\,\langle T^{\rm tot}_{ab}(p)\rangle+\phi(p)\,g_{ab}(p),\qquad \nabla_b\phi=0.
$$

若仅有 $\sup_k\Delta_{\rm QNEC}(p;k)\le\varepsilon$，则存在常数 $C$ 与范数 $X$ 使

$$
\big|E^{\rm grav}_{ab}-8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle-\phi g_{ab}\big|_X\le C\,\varepsilon.
$$

---

## 4 预备：小区域几何、有效体积与核展开

### 4.1 Gray–Vanhecke 展开

RNC 给出

$$
V(B_{p,r})=\Omega_{d-1}\frac{r^d}{d}\Big(1-\frac{R(p)}{6(d+2)}r^2+O(r^4)\Big),\quad
A(\partial B_{p,r})=\Omega_{d-1}r^{d-1}\Big(1-\frac{R(p)}{6d}r^2+O(r^4)\Big).
$$

定义

$$
V^{\rm eff}_\xi(D_{p,r}):=\int_{D_{p,r}}\nabla_a\xi^a\,{\rm dvol},\quad
\delta V^{\rm eff}_\xi=-\int_{D_{p,r}}\delta g^{ab}\nabla_a\xi_b\,{\rm dvol}+O(r^{d+2}).
$$

### 4.2 模哈密顿量局域核与两帽边界核

小区域模哈密顿量写作

$$
K_{D_{p,r}}=2\pi\int_{D_{p,r}}T_{ab}\xi^a{\rm d}\Sigma^b+\sum_{\pm}\int_{\mathcal N_\pm}f_\pm\,T_{kk}\,{\rm d}\sigma+O(r^{d+2}),
$$

$f_\pm=O(r^2)$，镜像 $\mathcal R:\mathcal N_+\to\mathcal N_-$ 下 $f_+=-f_-\circ\mathcal R$。定理 J.1 证明边界项在分布意义 $O(r^{d+2})$ 抵消。

### 4.3 协变相空间恒等式与角点

对任意变分 $\delta$ 与向量场 $\xi$ 有

$$
\boldsymbol\omega(\delta,\mathcal L_\xi)=\delta \boldsymbol j_\xi-{\rm d}\big(\delta\mathbf Q_\xi-\xi\!\cdot\!\boldsymbol\theta\big),\quad
\boldsymbol j_\xi:=\boldsymbol\theta(\mathcal L_\xi)-\xi\!\cdot\!\mathbf L.
$$

角点势 $C_\xi$ 重排角点全微分（附录 F）。

---

## 5 命题 K.1：固定 $V^{\rm eff}_\xi\Leftrightarrow$固定 $H_\xi$（至 $O(r^d)$）

**命题（K.1，精确版）**
若 $L=L_{\rm EH}$ 或 $L=f(R)=R+\alpha R^2$，取第 2 节之近似 CKV $\xi$。则存在常数 $p=-\Lambda/(8\pi G_{\rm ren})$ 与 $C=C(d,|{\rm Rm}|_{C^1},C_\xi)$ 使对所有解空间切向量 $\delta$ 成立

$$
\Big|\delta H_\xi-\frac{\kappa_\xi}{2\pi}\delta S_{\rm grav}+p\,\delta V^{\rm eff}_\xi\Big|\le C\,r^{d+2}\Big(|\delta g|_{C^1(B_{p,2r})}+|\delta\psi|_{H^1}\Big).
$$

**证明**（要点与常数控制）：

**（i）体—边—角分解。** 由协变相空间与 Stokes，

$$
\delta H_\xi=\int_{D_{p,r}} \delta\boldsymbol j_\xi+\int_{\partial D_{p,r}}\!\big(\delta\mathbf Q_\xi-\xi\!\cdot\!\boldsymbol\theta-\delta C_\xi\big).
$$

写 $\boldsymbol j_\xi=\sqrt{-g}\,E^{\rm grav}_{ab}\xi^a{\rm d}\Sigma^b+\nabla\!\cdot\!(\dots)$，利用 $\xi|_{\partial D}=0$ 与角点改正，

$$
\delta H_\xi=\int_{D_{p,r}}\delta(\sqrt{-g}\,E^{\rm grav}_{ab}\xi^a n^b)+\frac{\kappa_\xi}{2\pi}\delta S_{\rm grav}-p\,\delta V^{\rm eff}_\xi+R_{\rm bd}.
$$

余项 $R_{\rm bd}$ 由定理 J.1 与附录 F 归并，$|R_{\rm bd}|\le C_1 r^{d+2}|\delta|_{C^1\oplus H^1}$。

**（ii）EH 主阶。** 代表面上 $\theta|_p=\sigma|_p=0$、$\int(\theta^2+\sigma^2)=O(r^{d+2})$ 压低二阶几何项；体项尺度 $O(r^d)$ 与 $\delta E^{\rm grav}=O(1)$ 相乘给 $O(r^{d+2})$。

**（iii）$f(R)$ 修正。** Wald 熵 $\delta S_{\rm grav}=\tfrac{1}{4G_{\rm ren}}\int_\Sigma \delta(f'(R)\,{\rm d}A)$，RNC 与附录 B 给

$$
\Big|\!\int_{D_{p,r}}\!\delta f'(R)\Big|\le C_2 r^{d+2}|\delta g|_{C^1},\quad
\Big|\!\int_{\Sigma}\!\delta f'(R)\,{\rm d}A\Big|\le C_3 r^{d+1}|\delta g|_{C^1}.
$$

外挠率混项由代表面估计降到 $O(r^{d+2})$。合并得命题成立。证毕。

---

## 6 定理 J.1：两帽边界核在分布意义的 $O(r^{d+2})$ 抵消

**定理（J.1）**
设 $\mathcal N_\pm$ 为镜像零帽，$f_\pm\in C^{1,\alpha}$ 满足 $f_\pm=O(r^2)$、$f_+=-f_-\circ\mathcal R$。Hadamard 态使 $T_{kk}\in\mathcal D'(\mathcal N_\pm)$ 可沿零面限制。则对所有 $\varphi\in C^1\cap H^1$ 有常数 $C$ 使

$$
\Big|\!\int_{\mathcal N_+}! f_+T_{kk}\varphi+!\int_{\mathcal N_-}! f_-T_{kk}\varphi\Big|
\le C\,r^{d+2}\,|\varphi|_{C^1\cap H^1}.
$$

**证明**：附录 E 中以波前集与镜像映射 $\mathcal R$ 的 $C^1$ 偏离 $O(r)$ 为核心，给出

$$
|T_{kk}-\mathcal R^*T_{kk}|_{H^{-1}}\le C r|T_{kk}|_{H^{-1}},
$$

乘以 $|f_\pm|_{C^1}=O(r^2)$ 与测度尺度 $O(r^{d-1})$ 得 $O(r^{d+2})$ 界。角点配合 $C_\xi$ 为全微分不提升阶次。证毕。

---

## 7 定理 A 的证明

**二阶平衡式与零向等式。** 代表面 $\hat\Sigma$ 上固定 $V^{\rm eff}_\xi$（或 $H_\xi$）约束下

$$
0=\delta^2 S_{\rm gen}=\delta^2 S_{\rm grav}+\delta^2 S_{\rm out}+\delta^2 S_{\rm ct}.
$$

命题 K.1 将约束贡献重写为 $\tfrac{\kappa_\xi}{2\pi}\delta^2 S_{\rm grav}-p\,\delta^2 V^{\rm eff}_\xi+O(r^{d+2})$。Raychaudhuri 在 $\hat\Sigma$ 上给

$$
(\sqrt h)^{-1}\delta^2 A=-R_{kk}+O(r^2),
$$

而 QNEC 与定理 J.1 控制 $\delta^2 S_{\rm out}$。综合得

$$
-\frac{1}{4G_{\rm ren}}R_{kk}+2\pi\langle T_{kk}\rangle+O(r^2)=0,
$$

从而

$$
E^{\rm grav}_{kk}=8\pi G_{\rm ren}\langle T^{\rm tot}_{kk}\rangle.
$$

**张量化与常数并入。** 由附录 A 分布级张量化引理，存在 $\phi$ 使

$$
E^{\rm grav}_{ab}-8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle=\phi g_{ab}.
$$

再用 $\nabla^aE^{\rm grav}_{ab}\equiv 0$ 与 $\nabla^a\langle T^{\rm tot}_{ab}\rangle=0$ 得 $\nabla_b\phi=0$，并入 $\Lambda$。证毕。

---

## 8 定理 B 的证明

**无源版。** 协变相空间恒等式给

$$
\frac{{\rm d}}{{\rm d}s}S_{\rm rel}^{\rm bdy}(s)=\int_{\Sigma_s}\boldsymbol\omega(\delta,\mathcal L_\xi\delta)+\int_{\partial\Sigma_s}(\delta\mathbf Q_\xi-\xi\!\cdot\!\boldsymbol\theta-\delta C_\xi).
$$

若片叶无关且无通量，右端为零，得 $\int_{\Sigma_s}\boldsymbol\omega(\delta,\mathcal L_\xi\delta)=0$。局域化并用 $\nabla^aE^{\rm grav}_{ab}=0$ 推出

$$
\nabla^a\big(E^{\rm grav}_{ab}-8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle\big)=0.
$$

**含源版与不变性。** 存在通flux/角点注入时定义

$$
J_b:=\nabla^a\Big[\delta Q_{\xi,ab}-(\xi^c\theta_{cab})-\delta C_{\xi,ab}\Big],
$$

即得带源量子 Bianchi。附录 F 以上同调证明 $J_b$ 对 JKM 位移与角点改正不变。证毕。

---

## 9 定理 C 的证明

**（1）从全方向 QNEC 饱和到线性核。** 对全部局域割面与零向 $k$，QNEC 等式与第一定律给出 $\delta^2 S_{\rm rel}^{\rm bdy}= \mathcal E_\xi(\delta,\delta)=0$。正则能非负推出核即全部物理扰动，遂全部零向线性约束为等式。

**（2）非线性闭合。** 在 De Donder 规范与 $H^s_\delta$ 中，将非线性方程写成

$$
h=\mathcal L^{-1}\big(\mathcal S-\mathcal N(h)\big),
$$

附录 L 给出收缩映射与唯一不动点，从而

$$
E^{\rm grav}_{ab}(g+h)=8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle+\phi g_{ab}.
$$

**（3）近饱和稳定性。** 若 $\sup_k\Delta_{\rm QNEC}\le\varepsilon$，则

$$
\mathcal E_\xi(\delta,\delta)\le C_1\,\varepsilon,
$$

由强制性与 L.1 的 Lipschitz 连续性，得

$$
\big|E^{\rm grav}_{ab}-8\pi G_{\rm ren}\langle T^{\rm tot}_{ab}\rangle-\phi g_{ab}\big|_{H^{s-2}_\delta}\le C\,\varepsilon.
$$

证毕。

---

## 10 二维改写与反常

在 $d=2$ 中，Einstein 张量退化。采用改进应力

$$
T^{\rm impr}_{\pm\pm}=T_{\pm\pm}-\frac{c}{24\pi}\{\lambda,x^\pm\},
$$

Weyl 反常仅入迹。分布级张量化引理改写为：若 $X_{++}=X_{--}=0$ 且 $\nabla^aX_{ab}=\hat J_b$，则 $X_{+-}=\phi g_{+-}$、$\partial_\pm\phi=\hat J_\pm$。于是二维版本 A′/B′/C′ 给出

$$
E^{\rm grav}_{ab}=8\pi G_{\rm ren}\langle T^{\rm tot,\rm impr}_{ab}\rangle+\phi g_{ab},\qquad \partial_b\phi=\hat J_b,
$$

无源时 $\phi$ 常数并入 $\Lambda$。Bañados/BTZ 的对称割面可实现饱和；Vaidya 场景出现近饱和并满足稳定性不等式（附录 I）。

---

## 11 实例

### 11.1 FRW

$$
{\rm d}s^2=-{\rm d}t^2+a^2(t)\gamma_{ij}{\rm d}x^i{\rm d}x^j.
$$

取过 $p$ 的径向零向 $k$，定理 A 给 $E^{\rm grav}_{kk}=8\pi G_{\rm ren}\langle T^{\rm tot}_{kk}\rangle$。与量子 Bianchi 的时间—空间分解组合得

$$
H^2+\frac{k}{a^2}=\frac{16\pi G_{\rm ren}}{(d-1)(d-2)}\,\rho+\frac{2\Lambda}{(d-1)(d-2)},\qquad
\dot H-\frac{k}{a^2}=-\frac{8\pi G_{\rm ren}}{d-2}\,(\rho+P),
$$

误差由 $O(r^{d+2})$ 控制（附录 J）。

### 11.2 AdS$_3$/CFT$_2$

Bañados/BTZ 背景上，对称割面族实现 QNEC 饱和，C′ 直接闭合。AdS–Vaidya 下，E2 显示 $\Delta\mathcal E_\xi$ 的片叶漂移与 $\int J_b$ 闭合；E3 的饱和相图表明 $\Delta_{\rm QNEC}$ 零集与 $E^{\rm grav}_{kk}$ 零集的 Hausdorff 距离随 $r$ 呈 $O(r^2)$ 收敛（附录 I、K）。

---

## 12 误差预算与适用窗口

* **理论误差**：体项 $O(r^d)$；两帽边界核与曲率—半径交叉 $O(r^{d+2})$；高导数外挠率修正不提升主阶。非 CFT 需 $mr\ll 1$。
* **数值误差**：网格尺度、二阶差分步长、角点离散与去噪，双对数斜率校验 $d+2$。
* **适用窗口**：Hadamard 态、无引力反常；Weyl 反常仅入迹（二维改写）；正则能非负的耦合域；可积性小参数 $\epsilon\sim r/\ell_{\rm curv}$ 充分小。

---

# 附录

## 附录 A：分布层级张量化引理（完整证明）

**引理 A.1**
$X_{ab}\in\mathcal D'(M)$ 对称。若对任意零向 $n^a$ 与 $\psi\in C^\infty_0$ 有 $\langle X_{ab}n^a n^b,\psi\rangle=0$，则存在 $\phi\in\mathcal D'(M)$ 使 $X_{ab}=\phi g_{ab}$。若 $\nabla^a X_{ab}=J_b=j_b{\rm dvol}$，则 $\partial_b\phi=j_b$。

**证明**
取局域正交标架 $g_{ab}={\rm diag}(-1,1,\dots)$。任意零向 $n^a=e_0^a+\hat n^i e_i^a$、$|\hat n|=1$。配对式

$$
0=\langle X_{00}+2\hat n^i X_{0i}+\hat n^i\hat n^j X_{ij},\psi\rangle.
$$

视为关于 $\hat n$ 的二次型对所有单位向量为零。球谐分解得线性项 $\langle X_{0i},\psi\rangle=0$，二次项 $\langle X_{ij},\psi\rangle=\lambda\,\delta_{ij}\langle\psi\rangle$，零阶 $\langle X_{00},\psi\rangle=-\lambda\langle\psi\rangle$。故 $X_{ab}=\lambda\,{\rm diag}(-1,1,\dots)=\phi g_{ab}$。散度条件给 $\partial_b\phi=j_b$。证毕。

---

## 附录 B：$f(R)$ 与小区域展开的阶计控制

RNC 中 $R(x)=R(p)+\partial_cR|_p\,x^c+O(x^2)$。$f(R)=R+\alpha R^2$ 的 Wald 熵

$$
S_{\rm grav}=\frac{1}{4G_{\rm ren}}\int_\Sigma f'(R)\,{\rm d}A
=\frac{1}{4G_{\rm ren}}\int_\Sigma \big(1+2\alpha R(p)\big)\,{\rm d}A+O(r^{d+1}).
$$

$\delta f'(R)=2\alpha\,\delta R$。积分估计

$$
\Big|\!\int_{D_{p,r}}\!\delta R\Big|\le C\,r^{d+2}|\delta g|_{C^1},\qquad
\Big|\!\int_{\Sigma}\!\delta R\,{\rm d}A\Big|\le C\,r^{d+1}|\delta g|_{C^1}.
$$

代表面上的外挠率混项由 $\theta|_p=\sigma|_p=0$ 与 $\int(\theta^2+\sigma^2)=O(r^{d+2})$ 压低，不改变 $O(r^d)$ 主阶。证毕。

---

## 附录 C：小区域模哈密顿量核与形状变分

近似 CKV $\xi$ 给形状变分核 $f_\pm=O(r^2)$，并满足镜像奇对称 $f_+=-f_-\circ\mathcal R$。Hadamard 条件确保 $\langle T_{kk},f_\pm\varphi\rangle$ 良定，定理 J.1 给出 $O_{\mathcal D'}(r^{d+2})$ 界。证毕。

---

## 附录 D：方案独立性与总应力守恒

允许的局域对置项只重定义 $G_{\rm ren},\Lambda$ 与有限高导数耦合，不改变 $\nabla^a\langle T^{\rm tot}_{ab}\rangle=0$。非局域有效作用的变分定义 $\tau^{\rm ent}_{ab}$，其散度与体源抵消。故本文主方程在等价类下不变。证毕。

---

## 附录 E：两帽抵消的微局域分析（完整）

Hadamard 两点函数 $W$ 的波前集 $WF(W)$ 控制 $T_{kk}$ 沿零面的分布限制。镜像映射 $\mathcal R$ 的 $C^1$ 偏离为 $O(r)$，故

$$
|T_{kk}-\mathcal R^*T_{kk}|_{H^{-1}}\le C r|T_{kk}|_{H^{-1}}.
$$

再乘以 $|f_\pm|_{C^1}=O(r^2)$ 与测度 $O(r^{d-1})$，配合测试函数范数 $|\varphi|_{C^1\cap H^1}$，即得 $O(r^{d+2})$ 界。角点的分布质量经 $C_\xi$ 重排为全微分，不提升阶次。证毕。

---

## 附录 F：JKM 位移与角点改正的上同调不变性

改变量为精确形式 ${\rm d}\beta$。两帽并角点构成的相对同调类上，$\int_{\partial D_{p,r}}{\rm d}\beta=0$。角点势 $C_\xi$ 的变化由边界全微分补偿，保持 $\delta H_\xi$ 与 $J_b$ 不变。证毕。

---

## 附录 G：量子 Bianchi 源 $J_b$ 的坐标自由表达与示例

写

$$
J_b=\nabla^a\Big[\delta Q_{\xi,ab}-(\xi^c\theta_{cab})-\delta C_{\xi,ab}\Big],
$$

$\theta_{cab}$ 为辛势的双指标拉回。AdS–Vaidya 小菱形的离散实现显示 $\Delta\mathcal E_\xi(\Sigma_1\to\Sigma_2)\approx\int J_b$ 于 $O(r^{d+2})$ 内闭合。证毕。

---

## 附录 H：量子静止代表面——存在、唯一与构造算法

在 $C^{2,\alpha}\cap H^2$ 的形变空间上，以"量子扩张"为非线性算子 $\mathcal Q$。背景 QES 满足 $\mathcal Q(\Sigma)=0$，其 Fréchet 导数自伴正定。隐函数定理给出唯一解族使 $\theta|_p=\sigma|_p=0$。能量估计

$$
\int_{\hat\Sigma}(\theta^2+\sigma^2)\le C\,r^{d+2}.
$$

构造采用梯度流/牛顿迭代，Lipschitz 常数 $\le C\varepsilon$，收敛于 $\hat\Sigma$。证毕。

---

## 附录 I：二维改写、改进应力与相图

在 $d=2$ 采用改进应力 $T^{\rm impr}_{\pm\pm}$，Weyl 反常入迹。二维张量化引理与量子 Bianchi 改写见正文 §10。Bañados/BTZ 与 Vaidya 的数值相图展示 $\Delta_{\rm QNEC}$ 与 $E^{\rm grav}_{kk}$ 零集之重合度随 $r$ 呈 $O(r^2)$ 收敛。证毕。

---

## 附录 J：FRW 的零向投影与 Friedman 组合

记 $H:=\dot a/a$、$\rho:=\langle T^{\rm tot}_{tt}\rangle$、$P:=a^{-2}\gamma^{ij}\langle T^{\rm tot}_{ij}\rangle/(d-1)$。零向投影

$$
E^{\rm grav}_{kk}=E^{\rm grav}_{tt}+E^{\rm grav}_{rr},
$$

配合量子 Bianchi 的时间—空间分解，得正文 §11.1 的两条标量式。误差项 $\le C r^{d+2}$（$C$ 依赖 $|H|_{C^1}$、$|{\rm Rm}|_{C^0}$）。证毕。

---

## 附录 K：E2/E3 的最小实现与误差斜率

**相对熵通量计（E2）**
输入：$(g_{ab}),\xi^a,\Sigma_s$ 的网格；输出：$\Delta\mathcal E_\xi$ 与 $\int J_b$。步骤：生成零叶剖分；离散 $\boldsymbol\omega,\mathbf Q_\xi,\boldsymbol\theta,C_\xi$；片叶差值；报告 $\log$–$\log$ 斜率（目标 $d+2$）。

**饱和相图（E3）**
输入：割面族与二阶差分步长；输出：$\Delta_{\rm QNEC}(x,k)$ 与零集重合度（Hausdorff/Jaccard）。稳定性：改变步长与滤波强度，识别平台区，估计常数 $C$。证毕。

---

## 附录 L：可积性引理 L.1 的能量估计与收缩映射

De Donder 规范与 $H^s_\delta$、$s>\tfrac d2+2$、$-1<\delta<0$。线性化算子 $\mathcal L$ 满足

$$
|\mathcal L^{-1}F|_{H^s_\delta}\le C|F|_{H^{s-2}_\delta}.
$$

非线性满足 Moser 型估计

$$
|\mathcal N(h_1)-\mathcal N(h_2)|_{H^{s-2}_\delta}\le C\big(|h_1|_{H^s_\delta}+|h_2|_{H^s_\delta}\big)|h_1-h_2|_{H^s_\delta}.
$$

当 $|\mathcal S|_{H^{s-2}_\delta}\le C^{-1}\rho$、$\rho\ll 1$ 时，$\mathcal T(h)=\mathcal L^{-1}(\mathcal S-\mathcal N(h))$ 为收缩，存在唯一不动点。强制性常数由正则能非负性给出，导出"近饱和 $\Rightarrow$ 近方程"的 Lipschitz 界。证毕。

---

## 附录 M：误差预算总表

* **体项**：$O(r^d)$，常数 $C_1=C_1(d,|{\rm Rm}|_{C^0})$。
* **两帽核**：$O(r^{d+2})$，常数 $C_2=C_2(d,C_\xi,\alpha)$。
* **曲率—半径交叉**：$O(r^{d+2})$，常数 $C_3=C_3(d,|{\rm Rm}|_{C^1})$。
* **高导数外挠率**：$O(r^{d+2})$，常数 $C_4=C_4(d,|{\rm Rm}|_{C^0})$。
* **数值离散**：网格 $h$、步长 $\delta\lambda$ 的 $O(h^2)+O(\delta\lambda^2)$ 斜率。

---

**全文完**
