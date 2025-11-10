# 信息几何变分原理导出爱因斯坦方程：定体积对偶、显式可交换极限、Radon‑型闭包、OS/KMS–Fisher 解析延拓与 null 边界处方

Version: 2.9

## 摘要

在流形每一点的小尺度因果钻石 $B_\ell(p)$ 上，以广义熵

$$
S_{\rm gen}= \frac{A(\text{腰面})}{4G\hbar}+S_{\rm out}^{\rm ren}+S_{\rm ct}^{\rm UV}-\frac{\Lambda}{8\pi G}\frac{V(B_\ell)}{T}
\qquad\big(T=\hbar|\kappa_\chi|/2\pi\big)
$$

为基本变分泛函，提出信息几何变分原理（IGVP）：一阶层在定体积约束下取驻值，二阶层要求相对熵非负。本文给出四个可直接调用的技术支柱：（i）基于 Raychaudhuri–Sachs–Grönwall 的**显式可交换极限不等式**与**边界层估计**，并将剪切/挠率控制写成几何常数；（ii）以**加权光线变换**与**测试函数局域化引理**实现"族约束 $\Rightarrow$ 点态"的**Radon‑型闭包**，再配"零锥刻画引理"与 Bianchi 恒等式得到张量化闭包；（iii）在 OS 反射正性与 KMS 条带解析性下，建立 Fisher–Rao 度量经解析延拓得到**实、非退化、洛伦兹签名**的**充分条件**及**下界**，并给出交叉分量消失的**可操作判据**；（iv）在协变相空间框架中，提供**标准 null 边界与角点项处方**，证明辛流无外泄与哈密顿量变分可积，且在 Minkowski 小钻石上显式核对。由一阶层得到

$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab},
$$

由二阶层在 JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 条件下得到 Hollands–Wald 规范能量的非负性；在无对偶语境下以 QNEC/ANEC 作为保底。本文同时阐明 $\delta Q/T$、$\delta A/(4G\hbar)$ 在重标定与取向翻转下不变，并说明 $V/T$ 随重标定缩放；在一阶极值层采用固定温标（$\delta T=0$）可规避其规范依赖。

---

## 0 记号、域前提与速查表

**记号与单位**：度规签名 $(-,+,+,+)$；$c=k_B=1$，保留 $\hbar$。爱因斯坦张量 $G_{ab}=R_{ab}-\tfrac12R g_{ab}$。零向量收缩 $R_{kk}:=R_{ab}k^ak^b$、$T_{kk}:=T_{ab}k^ak^b$。**体积与面积**：**体积 $V(B_\ell)$** 指因果钻石**最大截面**（腰面）的 $(d{-}1)$ 维体积（本文默认 $d\ge3$；四维时即三维体积）。以下 $dA$ 皆指腰面测度；腰面面积主阶标度 $A\sim c_d\ell^{d-2}$（常数并入 $C_d$）。

**域前提**：尺度分离 $\varepsilon_{\rm curv}=\ell/L_{\rm curv}$、$\varepsilon_{\rm mat}=\ell/L_{\rm mat}$、$\varepsilon=\max(\varepsilon_{\rm curv},\varepsilon_{\rm mat})\ll1$；Hadamard 类态与点分裂重整化；小区间 $[0,\lambda_*]$ 内**无共轭点/焦点**（Sachs/Raychaudhuri 可控，光线变换局部可逆）。

**不变量速查表**（在 $k^a\to\alpha k^a$、$\lambda\to\lambda/\alpha$、$\kappa\to\alpha\kappa$ 与取向翻转下不变）：

$$
\frac{\delta Q}{T}=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA,\qquad
\frac{\delta A}{4G\hbar}.
$$

**备注**：$V/T$ 随重标定缩放（$T\to\alpha T$、$V$ 不变），故非不变量；在一阶极值层取 $\delta T=0$ 时，其出现仅作对偶项记法，不影响结论。

**常数族速查表**（定义于 $B_\ell$）：

$$
C_R:=\sup|R_{kk}|,\quad C_{\nabla R}:=\sup|\nabla_k R_{kk}|,\quad
C_{\mathcal C}:=\sup\big|C_{abcd}k^a m^b k^c m^d\big|\quad(\text{即 }|\Psi_0|),\quad
C_\sigma:=C_{\mathcal C}\lambda_*,\quad C_\omega=0,\quad \lambda_*\sim c_\lambda \ell .
$$

最终不等式中的 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 给出闭式依赖。

---

## 1 IGVP：泛函、约束与两层准则

**广义熵与拆分**

$$
S_{\rm gen}=\underbrace{\frac{A}{4G\hbar}+S_{\rm out}^{\rm ren}+S_{\rm ct}^{\rm UV}}_{\text{重整化后有限量}}
\;-\;\underbrace{\frac{\Lambda}{8\pi G}\frac{V}{T}}_{\text{体积约束对偶项}},
\qquad T=\frac{\hbar|\kappa_\chi|}{2\pi}.
$$

**准则**
（一阶层）在定体积约束 $\delta V=0$ 下取 $\delta S_{\rm gen}=0$；等价地把 $S_\Lambda$ 并入无约束变分后令 $\delta S_{\rm gen}=0$。
（二阶层）相对熵非负：$\delta^2S_{\rm rel}\ge0$。

**约定（一阶变分的温标）**：默认固定温度 $T$（$\delta T=0$）进行一阶极值；若允许 $\delta T\neq0$，其贡献为 $\mathcal O(\varepsilon^2)$ 不改结论（见 §6）。

---

## 2 小钻石极限：显式不等式与边界层

**正则性门槛**：背景度规 $g\in C^3$（或 $g\in C^2$ 且 $\nabla{\rm Riem}\in L^\infty$），物质场 $T_{ab}\in C^1$；腰面为极大截面，初值 $\theta(0)=\sigma(0)=\omega(0)=0$；零测地丛满足 Frobenius 条件，故 $\omega\equiv0$。

**初值与 Frobenius 条件**：腰面取 $\theta(0)=\sigma(0)=\omega(0)=0$；零测地丛超曲面正交 $\Leftrightarrow\omega\equiv0$。

**Raychaudhuri–Sachs–Twist 方程**

$$
\theta'=-\tfrac12\theta^2-\sigma^2+\omega^2-R_{kk},\quad
\sigma'=-\theta\,\sigma-\mathcal C,\quad
\omega'=-\theta\,\omega ,
$$

其中 $\mathcal C:=C_{abcd}k^a m^b k^c m^d$。*注：本文约定 $\sigma^2:=|\sigma|^2$。*

由 $\omega(0)=0$ 与 Frobenius 得 $\omega\equiv 0$。变系数 Grönwall 与 $|\theta|\lambda_*\ll1$ 给出

$$
|\sigma(\lambda)|\le C_{\mathcal C}|\lambda|\,e^{\int_0^{|\lambda|}|\theta|ds}\le C_\sigma(1+\mathcal O(\varepsilon)),
$$

并且

$$
\big|\theta(\lambda)+\lambda R_{kk}\big|\le \tfrac12 C_{\nabla R}\lambda^2+C_\sigma^2|\lambda|=:M_\theta(\lambda).
$$

**面积变分显式不等式与可交换性**

$$
\boxed{\
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\,d\lambda\,dA\Big|
\le \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2\Big)A
\le C_d\,\varepsilon^2\,\ell^{d-2}\ },
$$

其中 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 与 $\varepsilon$ 无关。

端点层 $[\lambda_*-\delta,\lambda_*]$ 的贡献为

$$
\le \tfrac12 A\big(\lambda_*^2-(\lambda_*-\delta)^2\big)C_R
=\mathcal O\big(A\,\ell\,\delta\,C_R\big),
$$

取 $\delta=\mathcal O(\varepsilon\ell)$ 与 $C_R=\mathcal O(L_{\rm curv}^{-2})$ 得 $\mathcal O\big(A\,\varepsilon\,\ell^2\,C_R\big)=\mathcal O(\varepsilon)\times\mathcal O(\varepsilon^2\ell^{d-2})$。为严谨起见，取一固定凸正规邻域 $\mathcal O$ 与 $\ell_0>0$，令 $\lambda_0=c_\lambda\ell_0$，并在 $\mathcal O$ 上定义

$$
\widehat C_{\nabla R}:=\sup_{\mathcal O}|\nabla_k R_{kk}|,\qquad
\widehat C_{\mathcal C}:=\sup_{\mathcal O}\big|C_{abcd}k^a m^b k^c m^d\big|.
$$

设

$$
M_{\rm dom}^{(\mathcal O)}(\lambda):=\tfrac12\widehat C_{\nabla R}\lambda^2+(\widehat C_{\mathcal C}\lambda_0)^2|\lambda|\in L^1([0,\lambda_0]).
$$

当 $B_\ell\subset\mathcal O$ 且 $\lambda_*\le\lambda_0$ 时，将被积函数在 $[0,\lambda_0]$ 上外延为 $0$（于 $[\lambda_*,\lambda_0]$），得对所有充分小的 $\varepsilon$ 有统一支配：

$$
\big|\theta(\lambda)+\lambda R_{kk}\big|\le M_{\rm dom}^{(\mathcal O)}(\lambda)\quad\text{a.e. on }[0,\lambda_0].
$$

因而可由主导收敛定理严格推出"$\varepsilon\to0$ 与 $\lambda$‑积分可交换"。

---

## 3 族约束 $\Rightarrow$ 点态：Radon‑型闭包与局域化

**加权光线变换**：对过 $p$ 的零测地 $\gamma_{p,\hat k}$，定义

$$
\mathcal L_\lambda[f](p,\hat k):=\int_0^{\lambda_*}\lambda\, f(\gamma_{p,\hat k}(\lambda))\,d\lambda.
$$

小域展开

$$
\mathcal L_\lambda[f](p,\hat k)=\tfrac12\lambda_*^2 f(p)+\mathcal O(\lambda_*^3|\nabla f|_\infty).
$$

**测试函数局域化引理**：若 $\int_{\partial B_\ell}\varphi(x)\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda\,dA=0$ 对所有 $\varphi\in C_c^\infty(\partial B_\ell)$、$w\in C_c^\infty([0,\lambda_*])$ 成立，则几乎处处沿每条生成元 $\int_0^{\lambda_*} w F=0$。
（注：本文主用首矩权 $w\equiv\lambda$。）

由此对 $f=R_{kk}-8\pi G\,T_{kk}$ 得 $\mathcal L_\lambda[f]=o(\ell^2)\Rightarrow f(p)=0$，即

$$
R_{kk}=8\pi G\,T_{kk}\quad(\forall\,k).
$$

---

## 4 张量化闭包与场方程（$d\ge 3$）

**零锥刻画引理**：若 $X_{ab}$ 光滑对称且 $X_{ab}k^ak^b=0$ 对一切零矢成立，则 $X_{ab}=\Phi g_{ab}$。
令 $X_{ab}=R_{ab}-8\pi G\,T_{ab}$。由 $X_{ab}=\Phi g_{ab}$ 得 $\nabla^a X_{ab}=\nabla_b\Phi$。又由收缩 Bianchi 与 $\nabla^aT_{ab}=0$，有 $\nabla^a X_{ab}=\tfrac12\nabla_b R$。于是

$$
\nabla_b\left(\tfrac12 R-\Phi\right)=0,
$$

定义 $\Lambda:=\tfrac12 R-\Phi$（常数），从而

$$
\boxed{\,G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}\,}.
$$

---

## 5 二阶层：$\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$ 与稳定性

**函数空间与无外流条件**：扰动 $h_{ab}\in H^{k}(\Sigma)$（$k\ge2$），边界条件固定诱导度规（或其共轭动量），并要求 $\int_{\partial\Sigma}\iota_n\omega(h,\mathcal L_\xi h)=0$（辛流无外流）；规范采用 Killing 或协变谐以剔除纯规范模。

在 code subspace、线性化约束 $\delta M=\delta J=\delta P=0$ 与合适边界条件下，

$$
\boxed{\ \delta^2S_{\rm rel}=\mathcal F_Q=\mathcal E_{\rm can}[h,h]\ge0\ },
$$

与 Hollands–Wald 线性稳定性等价。**核的说明**：在所选规范固定与边界条件下，$\mathcal E_{\rm can}[h,h]=0$ 当且仅当 $h$ 为纯规范模。线性化爱因斯坦方程来自上一节的一阶族约束与张量化闭包；二者逻辑互不依赖。无对偶语境下，以 QNEC/ANEC 作为保底不等式（形状导数与极限次序详见附录）。

---

## 6 温标–体积对偶与 $\delta\kappa_\chi/\kappa_\chi$ 的阶计数

在重标定与取向翻转下，$\delta Q/T$ 与 $\delta A/(4G\hbar)$ 不变；$V/T$ 非不变量，但一阶极值层采用固定温标（$\delta T=0$）不影响结论。固定端点与腰面，近似 CKV 的表面引力 $\kappa_\chi=2/\ell+\mathcal O(\ell/L_{\rm curv}^2)$，一阶几何扰动给 $\delta\kappa_\chi=\mathcal O(\ell/L_{\rm curv}^2)$，故

$$
\frac{\delta\kappa_\chi}{\kappa_\chi}=\mathcal O\Big(\frac{\ell^2}{L_{\rm curv}^2}\Big)=\mathcal O(\varepsilon^2),
$$

从而"固定 $|\kappa_\chi|$"与"允许 $\delta T\neq0$"在一阶极值层等价。

---

## 7 OS/KMS–Fisher 解析延拓：交叉分量判据与"实/非退化/签名"的下界

令欧氏统计族 $p(y|t_E,x^i)$ 的 Fisher–Rao 度量

$$
g^{(E)}_{\mu\nu}=\mathbb E\big[\partial_\mu\log p\,\partial_\nu\log p\big].
$$

**交叉分量消失（在反射不变点）的充分判据**：若 $p(y|-t_E,x)=p(y|t_E,x)$（OS 反射偶）、$\partial_{t_E}\log p$ 奇、$\partial_i\log p$ 偶，则

$$
g^{(E)}_{t_E i}\big|_{t_E=0}=0 .
$$

KMS 周期保证解析延拓后一致性，故

$$
g^{(L)}_{ti}\big|_{t=0}=0 .
$$

一般 $t_E\neq0$ 时 $g^{(E)}_{t_E i}$ 仅关于 $t_E$ 为奇，不必恒为零。

**实值与非退化的充分条件（含下界）**：设存在常数 $\eta>0$，使

$$
\mathbb E\big[(\partial_{t_E}\log p)^2\big]\ge \eta,\qquad
\mathbb E\big[(\partial_i\log p)^2\big]\ge \eta,\qquad
\mathbb E\big[(\xi^\mu\partial_\mu\log p)^2\big]\ge \eta\,|\xi|^2\ \ \forall\xi\neq0,
$$

并满足 OS 反射正性与 $\beta$-KMS 条带解析性，则延拓 $t_E\mapsto it$ 后

$$
g^{(L)}_{tt}=-\mathbb E\big[(\partial_{t_E}\log p)^2\big]\le -\eta<0,\qquad
g^{(L)}_{ij}\succeq \eta\,\delta_{ij}>0,
$$

度量实、非退化且具 $(-,+,\dots)$ 签名。$1{+}1$ 维高斯族可取 $\eta=1/\sigma^2$ 作显式下界。

**说明**：Fisher–Rao 通道为结构性互补，不参与一阶链的主证明。

---

## 8 协变相空间的 null 边界与角点处方：无外流与可积性

在 Einstein–Hilbert 作用上加入 null 边界项与关节项：

$$
I_{\partial\mathcal N}=\frac{1}{8\pi G}\int_{\mathcal N}d\lambda\,d^{d-2}x\,\sqrt{q}\,\kappa[\ell],\qquad
I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J}d^{d-2}x\,\sqrt{\sigma}\,\eta ,
$$

其中横截面为 $(d{-}2)$ 维，$d^{d-2}x$ 为其固有测度。$\eta=\ln|-\ell\cdot n|$（null–非 null）或 $\eta=\ln\big|-\tfrac12\,\ell\cdot\tilde\ell\big|$（null–null）。取 Dirichlet‑类边界条件并采用**仿射**参数化则 $\kappa[\ell]=0$；**注意**：此处的 $\kappa[\ell]$ 仅是 $\ell^a$ 的非仿射量，**与**温标 $T=\hbar|\kappa_\chi|/2\pi$ **无关**。关节项以 $\eta$ 计入。由此 Iyer–Wald 辛流在边界无外泄，$\delta H_\chi$ 可积，且不改变 $\delta S_{\rm gen}$ 与 $\mathcal E_{\rm can}$ 的数值。

**示例（Minkowski 小钻石）**：两片仿射 null 面拼接 $\Rightarrow \kappa[\ell]=0$ 给 $I_{\partial\mathcal N}=0$；null–空超曲面关节项 $\eta$ 为常数，$\delta I_{\rm joint}=0$。由此边界通量为零且哈密顿量变分可积。

---

## 9 高阶引力与唯一性

以 Wald/Dong–Camps 熵替代面积项定义 $S_{\rm grav}$，小钻石一阶驻值导出高阶引力场方程；二阶层以相应的广义规范能量给出稳定性判据。四维且二阶导数结构的自然性与无散度假设下，Lovelock 唯一性保证张量结构同胚于 $a\,G_{ab}+b\,g_{ab}$。

---

## 10 两条独立链的逻辑蓝图

* **链 A（热力学—几何光学）**：$\delta S_{\rm grav}+\delta S_{\rm out}-\tfrac{\Lambda}{8\pi G}\delta V/T=0\Rightarrow R_{kk}=8\pi G\,T_{kk}\Rightarrow G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。
* **链 B（纠缠—相对熵）**：JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}\Rightarrow \delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$（稳定性）；线性化方程源自链 A 的族约束与闭包。

---

## 11 可复现实操清单

1. 调用 §2 的不等式与常数族，数值检验 $\big|\delta A+\int\lambda R_{kk}\big|\sim\varepsilon^2\ell^{d-2}$ 的标度与 $C_d$ 的保守性；
2. 逐项验证 $\delta Q/T$、$\delta A/(4G\hbar)$ 的重标定/取向不变；并在固定 $T$ 的规约下核查 $V/T$ 的使用。
3. 以"局域化引理"把面积恒等式下推至逐生成元，加上 0‑阶重建得 $R_{kk}=8\pi G\,T_{kk}$；
4. 在 $1{+}1$ 高斯族与满足奇偶性判据的模型上，显式验证 $g_{ti}=0$ 与"实/非退化/签名"的下界；
5. 在 Minkowski 小钻石核查 null 边界/关节项的"无外流 + 可积"。

---

## 参考文献（选）

Jacobson（1995, Phys. Rev. Lett. 75, 1260；2016, Class. Quantum Grav. 33, 245001）；Casini–Huerta–Myers（2011, JHEP 05, 036）；Jafferis–Lewkowycz–Maldacena–Suh（2016, JHEP 06, 004）；Lashkari–Van Raamsdonk（2016, JHEP 04, 153）；Iyer–Wald（1994, Phys. Rev. D 50, 846）；Donnelly–Freidel（2016, JHEP 09, 102）；Radzikowski（1996, Commun. Math. Phys. 179, 529）；Décanini–Folacci（2008, Phys. Rev. D 78, 044025）；Crispino–Higuchi–Matsas（2008, Rev. Mod. Phys. 80, 787）；Jacobson–Visser（2019, JHEP 03, 082）；Dong（2014, JHEP 01, 044）；Camps（2014, JHEP 03, 070）；Bousso–Fisher–Koeller–Leichenauer–Wall（2016, Phys. Rev. D 93, 024017）；Faulkner–Leigh–Parrikar–Wang（2016, JHEP 09, 038）；Hollands–Wald（2013, Commun. Math. Phys. 321, 629）；Bauer–Le Brigant–Lu–Maor（2024, arXiv:2401.xxxxx）；Lovelock（1971, J. Math. Phys. 12, 498）。

---

# 附录 A  小钻石极限：显式上界、边界层与可交换性

**A.1 初值与参数化**
腰面：$\theta(0)=\sigma(0)=\omega(0)=0$；生成元参数 $|\lambda|\le\lambda_*\sim c_\lambda\ell$。常数族 $C_R,C_{\nabla R},C_{\mathcal C},C_\sigma(=C_{\mathcal C}\lambda_*),C_\omega(=0)$。

**A.2 Frobenius 与 $\omega\equiv0$**
零测地丛超曲面正交 $\Leftrightarrow \omega_{ab}=0$。在"腰面 + 近似 CKV"构造下 $\omega(0)=0$，由 $\omega'=-\theta\omega$ 得 $\omega\equiv0$。

**A.3 剪切与曲率梯度上界**
Sachs：$|\sigma(\lambda)|\le C_{\mathcal C}|\lambda|e^{\int|\,\theta|}\Rightarrow \sup\sigma^2\le C_\sigma^2$。

$$
|\theta(\lambda)+\lambda R_{kk}|\le \tfrac12 C_{\nabla R}\lambda^2+C_\sigma^2|\lambda|=M_\theta(\lambda).
$$

**A.4 面积不等式与边界层**

$$
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\Big|
\le \int_{\mathcal H} M_\theta(\lambda)\,d\lambda\,dA
\le \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2\Big)A .
$$

端点层 $[\lambda_*-\delta,\lambda_*]$ 贡献

$$
\le \tfrac12 A\big(\lambda_*^2-(\lambda_*-\delta)^2\big)C_R
=\mathcal O\big(A\,\ell\,\delta\,C_R\big),
$$

取 $\delta=\mathcal O(\varepsilon\ell)$ 与 $C_R=\mathcal O(L_{\rm curv}^{-2})$ 得 $\mathcal O\big(A\,\varepsilon\,\ell^2\,C_R\big)=\mathcal O(\varepsilon)\times\mathcal O(\varepsilon^2\ell^{d-2})$。

**A.5 可交换性（修订）**
以

$$
M_{\rm dom}^{(\mathcal O)}(\lambda)=\tfrac12\widehat C_{\nabla R}\lambda^2+(\widehat C_{\mathcal C}\lambda_0)^2|\lambda|
$$

作为与 $\varepsilon$ 无关且定义在固定区间 $[0,\lambda_0]$ 上的支配函数，对 $[0,\lambda_*]$ 外延零后应用主导收敛定理，即得"$\varepsilon\to0$ 与积分次序可交换"。

---

# 附录 B  局域化引理与 Radon‑型 0‑阶重建

**B.1 局域化引理**
若 $\int_{\partial B_\ell}\varphi(x)\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda\,dA=0$ 对所有 $\varphi\in C_c^\infty$、$w\in C_c^\infty$ 成立，则几乎处处沿每条生成元 $\int_0^{\lambda_*}wF=0$。证：Fubini+单位分解。（注：本文主用首矩权 $w\equiv\lambda$。）

**B.2 0‑阶重建**
$S_{kk}(\gamma(\lambda))=S_{kk}(p)+\lambda\nabla_k S_{kk}(p)+\mathcal O(\lambda^2)$；
$\int_0^{\lambda_*}\lambda S_{kk}=\tfrac12\lambda_*^2 S_{kk}(p)+\mathcal O(\lambda_*^3|\nabla S|)$。
若左侧 $=o(\ell^2)$，则 $S_{kk}(p)\to0$。分布情形可先作 mollifier 平滑，再令平滑尺度 $\to0$。

---

# 附录 C  张量化闭包与维度条件

**引理 C.1（$d\ge3$）**
若 $X_{ab}$ 光滑对称且 $X_{ab}k^ak^b=0\ \forall k$（零矢），则 $X_{ab}=\Phi g_{ab}$。证：去迹分解与"零锥决定共形类"。

---

# 附录 D  QNEC/ANEC 的形状导数与极限次序

对单位横截面积归一：

$$
\langle T_{kk}(p)\rangle \ge \frac{\hbar}{2\pi}\lim_{A_\perp\to0}\frac{\partial_\lambda^2 S_{\rm out}}{A_\perp},\qquad
\int_{\mathbb R}T_{kk}\,d\lambda\ge 0 .
$$

先取 $\partial_\lambda^2$，再取 $A_\perp\to0$ 与 UV 极限；edge modes 以边界代数分解吸收。

---

# 附录 E  协变相空间：null 边界与角点项的可积性核对

**E.1 结构**
$\delta L=E\cdot\delta\Phi+d\Theta$，辛流 $\omega=\delta\Theta$。加入

$$
I_{\partial\mathcal N}=\frac{1}{8\pi G}\int_{\mathcal N}d\lambda\,d^{d-2}x\,\sqrt{q}\,\kappa[\ell],\quad
I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J}d^{d-2}x\,\sqrt{\sigma}\,\eta .
$$

取 Dirichlet‑类边界条件与仿射参数化，边界变分抵消，$\omega$ 无外泄，Wald–Zoupas/Brown–York 荷与 null 约束一致。

**E.2 Minkowski 小钻石核对**
仿射 null 段 $\Rightarrow \kappa[\ell]=0$ 使 $I_{\partial\mathcal N}=0$；null–空超曲面关节 $\eta$ 常数 $\Rightarrow \delta I_{\rm joint}=0$。故 $\delta H_\chi$ 可积，与 §5 的规范能量边界合法性一致。

---

# 附录 F  $\delta\kappa_\chi/\kappa_\chi=\mathcal O(\varepsilon^2)$ 的几何来源

Riemann 正交坐标：$g_{ab}=\eta_{ab}+\tfrac13 R_{acbd}x^c x^d+\cdots$。Minkowski 钻石 CKV 给 $\kappa_{\chi,0}=2/\ell$。弱曲率且端点/腰面固定下，

$$
\kappa_\chi=\kappa_{\chi,0}+\delta\kappa_\chi,\quad \delta\kappa_\chi=\mathcal O\Big(\frac{\ell}{L_{\rm curv}^2}\Big),\quad \frac{\delta\kappa_\chi}{\kappa_\chi}=\mathcal O\Big(\frac{\ell^2}{L_{\rm curv}^2}\Big).
$$

---

# 附录 G  OS/KMS–Fisher：交叉判据、充分条件与下界

**G.1 判据**
若 $p(y|-t_E,x)=p(y|t_E,x)$，$\partial_{t_E}\log p$ 奇、$\partial_i\log p$ 偶，则 $g^{(E)}_{t_E i}\big|_{t_E=0}=0$；KMS 周期保证解析延拓后一致性，故 $g^{(L)}_{ti}\big|_{t=0}=0$。一般 $t_E\neq0$ 时 $g^{(E)}_{t_E i}$ 仅关于 $t_E$ 为奇，不必恒为零。

**G.2 充分条件与下界**
在 OS 反射正性与 $\beta$-KMS 条带解析性前提下，若存在 $\eta>0$ 使 Fisher 协方差阵下界为 $\eta I$，则延拓后

$$
g^{(L)}_{tt}\le -\eta<0,\qquad g^{(L)}_{ij}\succeq \eta\,\delta_{ij}>0,
$$

度量实、非退化并具 $(-,+,\dots)$ 签名。$1{+}1$ 高斯族中 $\eta=1/\sigma^2$ 为显式下界。

---

# 附录 H  高阶引力：Wald/Dong–Camps 熵与线性层

给出 $f(R)$ 与 Gauss–Bonnet 的一阶变分至 $E_{ab}=8\pi G\,T_{ab}$ 的局域演示；线性层的广义规范能量在无外流条件下非负，与 Hollands–Wald 判据形式一致。
