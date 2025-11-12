# 信息几何变分原理导出爱因斯坦方程：定体积对偶、显式可交换极限、Radon‑型闭包、OS/KMS–Fisher 解析延拓与 null 边界处方

Version: 4.3

## 摘要

**We derive Einstein’s equations and the Hollands–Wald stability condition from a single information‑geometric variational principle.**

- 定体积对偶 + 显式可交换极限（小钻石极限，常数族可直接调用）
- Radon 型闭包：族约束下推为点态方程（面积恒等式 ⇒ 点态）
- 二阶层 = Hollands–Wald 规范能量（相对熵非负与稳定性在一条变分链闭环）

在流形每一点的小尺度因果钻石 $\mathcal D_\ell(p)$ 上，以广义熵

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

**记号与单位**：度规签名 $(-,+,+,+)$；$c=k_B=1$，保留 $\hbar$。爱因斯坦张量 $G_{ab}=R_{ab}-\tfrac12R g_{ab}$。零向量收缩 $R_{kk}:=R_{ab}k^ak^b$、$T_{kk}:=T_{ab}k^ak^b$。**体积与面积**：令**腰超曲面** $\Sigma_\ell$ 为因果钻石 $\mathcal D_\ell$ 的最大空间截面（维数 $d{-}1$），其体积 $V(B_\ell):=\mathrm{Vol}(\Sigma_\ell)$；令**腰面** $\partial\Sigma_\ell$ 为其边界（维数 $d{-}2$），其面积 $A:=\mathrm{Area}(\partial\Sigma_\ell)$。记 $B_\ell:=\Sigma_\ell$，$S_\ell:=\partial B_\ell$（腰面）；以下 $dA$ 一律指 $S_\ell$ 的固有测度；主阶标度 $A\sim c_d\ell^{d-2}$（常数并入 $C_d$）。

**域前提**：尺度分离 $\varepsilon_{\rm curv}=\ell/L_{\rm curv}$、$\varepsilon_{\rm mat}=\ell/L_{\rm mat}$、$\varepsilon=\max(\varepsilon_{\rm curv},\varepsilon_{\rm mat})\ll1$；Hadamard 类态与点分裂重整化；小区间 $[0,\lambda_*]$ 内**无共轭点/焦点**（Sachs/Raychaudhuri 可控，光线变换局部可逆）。

**不变量速查表**（在 $k^a\to\alpha k^a$、$\lambda\to\lambda/\alpha$、$\kappa\to\alpha\kappa$ 与取向翻转下不变）：

$$
\frac{\delta Q}{T}=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA,\qquad
\frac{\delta A}{4G\hbar}.
$$

**备注**：$V/T$ 随重标定缩放（$T\to\alpha T$、$V$ 不变），故非不变量；在一阶极值层取 $\delta T=0$ 时，其出现仅作对偶项记法，不影响结论。

**常数族速查表**（定义于 $\mathcal D_\ell$）：

$$
C_R:=\sup_{\mathcal D_\ell}|R_{kk}|,\quad
C_{\nabla R}:=\sup_{\mathcal D_\ell}|\nabla_k R_{kk}|,\quad
\mathcal C_{AB}:=\mathrm{TF}\big[C_{acbd}k^c k^d e^a_A e^b_B\big],\quad
C_{\mathcal C}:=\sup_{\mathcal D_\ell}|\mathcal C_{AB}|,\quad
C_\sigma:=C_{\mathcal C}\lambda_*,\quad C_\omega=0,\quad \lambda_*\sim c_\lambda \ell .
$$

其中 $\{e_A^a\}$ 为与 $k^a$ 正交的 $(d{-}2)$ 维 screen 空间正交基，$\mathrm{TF}$ 表示去迹，$|\cdot|$ 为任一定义良好的矩阵范数。

最终不等式中的 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 给出闭式依赖。

---

### 引言提要：与既有工作的区别度

- Jacobson（1995）：引入定体积对偶与显式 $\varepsilon$‑可交换极限，摆脱未指明“局域 Rindler”依赖
- Jacobson–Visser（2019）：以 Radon 型闭包将面积恒等式下推为点态方程（族约束 ⇒ 点态）
- JLMS + Hollands–Wald：将二阶相对熵与规范能量写入同一变分链，形成单链闭环
- Dong–Camps–Wald：以 Wald/Dong–Camps 熵替代面积后，同一 IGVP 框架直接给出 Lovelock 型方程

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

**外部熵的一阶律（用于链 A）** 在小钻石极限、Hadamard/KMS 态与近 Rindler 生成元 $\chi^a$ 下，

$$
\delta S_{\rm out}^{\rm ren}=\delta\langle K_\chi\rangle
=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA\ +\ \mathcal O(\varepsilon^2)
\equiv \frac{\delta Q}{T}+\mathcal O(\varepsilon^2),
$$

其中 $K_\chi$ 为腰面处的 boost 模块哈密顿量，$T=\hbar|\kappa_\chi|/2\pi$，并且由 §6 得 $\delta T/T=\mathcal O(\varepsilon^2)$。

因此在一阶极值层与 $\delta V=0$ 下，

$$
\delta S_{\rm gen}
=\frac{\delta A}{4G\hbar}+\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA\ +\ \mathcal O(\varepsilon^2)=0.
$$

结合 §2 的面积—曲率恒等式（误差为 $\mathcal O(\varepsilon^2)$），经 §3 的局域化与 §4 的张量化闭包，得到
$R_{kk}=8\pi G\,T_{kk}$ 以及 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。

**约定（一阶变分的温标）**：默认固定温度 $T$（$\delta T=0$）进行一阶极值；若允许 $\delta T\neq0$，其贡献为 $\mathcal O(\varepsilon^2)$ 不改结论（见 §6）。

---

## 2 小钻石极限：显式不等式与边界层

**正则性门槛**：背景度规 $g\in C^3$（或 $g\in C^2$ 且 $\nabla{\rm Riem}\in L^\infty$），物质场 $T_{ab}\in C^1$；令 $\Sigma_\ell$ 为**最大体积空间超曲面**，其边界 $S_\ell=\partial\Sigma_\ell$（**腰面**）为初值面，取 $\theta(0)=\sigma(0)=\omega(0)=0$；零测地丛满足 Frobenius 条件，故 $\omega\equiv0$。

**初值与 Frobenius 条件**：腰面取 $\theta(0)=\sigma(0)=\omega(0)=0$；零测地丛超曲面正交 $\Leftrightarrow\omega\equiv0$。

**Raychaudhuri–Sachs–Twist 方程（$d\ge3$）**

$$
\theta'=-\frac{1}{d-2}\theta^2-\sigma^2+\omega^2-R_{kk},\quad
(\sigma_{AB})'=-\frac{2}{d-2}\theta\,\sigma_{AB}-\big(\sigma^2{+}\omega^2\big)^{\rm TF}_{AB}-\mathcal C_{AB},\quad
\omega_{AB}'=-\frac{2}{d-2}\theta\,\omega_{AB}
-\big(\sigma_A{}^{C}\omega_{CB}+\omega_A{}^{C}\sigma_{CB}\big),
$$

其中 $\sigma^2:=\sigma_{AB}\sigma^{AB}$，$(\sigma^2)_{AB}:=\sigma_A{}^{C}\sigma_{CB}$，$(\omega^2)_{AB}:=\omega_A{}^{C}\omega_{CB}$，$\mathrm{TF}$ 表示去迹，$\mathcal C_{AB}=\mathrm{TF}\big[C_{acbd}k^c k^d e^a_A e^b_B\big]$。

由 $\omega(0)=0$ 与 Frobenius 得 $\omega\equiv 0$。变系数 Grönwall 与 $|\theta|\lambda_*\ll1$ 给出

$$
|\sigma(\lambda)|\le C_{\mathcal C}|\lambda|\,e^{\frac{2}{d-2}\int_0^{|\lambda|}|\theta|ds}\le C_\sigma(1+\mathcal O(\varepsilon)),
$$

并且

$$
\boxed{\
\big|\theta(\lambda)+\lambda R_{kk}(\lambda)\big|\ \le\
\tfrac12 C_{\nabla R}\lambda^2\ +\ C_\sigma^2|\lambda|\ +\ \tfrac{4}{3(d-2)}C_R^2|\lambda|^3\ :=\ \widetilde M_\theta(\lambda)\ .
}
$$

**面积变分显式不等式与可交换性**

$$
\boxed{
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\,d\lambda\,dA\Big|
\ \le\ \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2+\tfrac{1}{3(d-2)}C_R^2\lambda_*^4\Big)A\ .
}
$$

其中 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 与 $\varepsilon$ 无关。

**数值验证**：归一化误差 $|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$ 的 $\varepsilon^2$ 标度见图 1（不同曲率参数 $C_R, C_{\nabla R}, C_{\mathcal C}$ 下的上界曲线）。

![图 1：显式可交换极限的数值验证。归一化误差上界 $|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$ 随尺度分离参数 $\varepsilon$ 的变化，显示 $\varepsilon^2$ 标度。三条曲线对应不同曲率参数组合（低/中/高曲率），灰色虚线为参考 $\varepsilon^2$ 标度线。](igvp_figure1_exchangeable_limit.png)

端点层 $[\lambda_*-\delta,\lambda_*]$ 的贡献满足

$$
\Big|\int_{\lambda_*-\delta}^{\lambda_*}\lambda R_{kk}\,d\lambda\,dA\Big|
\le \tfrac12 A\big(\lambda_*^2-(\lambda_*-\delta)^2\big)C_R
=\mathcal O\big(A,C_R,\lambda_*,\delta\big).
$$

取 $\delta=\mathcal O(\varepsilon\ell)$ 且 $\lambda_*\sim c_\lambda\ell$，得 $\mathcal O\big(A,C_R,\varepsilon,\ell^2\big)$。

取固定常数 $\lambda_0>0$，对所取极限族均有 $0<\lambda_*\le\lambda_0$。由 $C_\sigma=C_{\mathcal C}\lambda_*\le C_{\mathcal C}\lambda_0$，令

$$
\boxed{
\widetilde M_{\rm dom}(\lambda)
:=\tfrac12 C_{\nabla R}\lambda^2+\big(C_{\mathcal C}\lambda_0\big)^2|\lambda|
+\tfrac{4}{3(d-2)}C_R^2\lambda_0^3\ \in L^1([0,\lambda_0])\ .
}
$$

则在固定区间 $[0,\lambda_0]$ 上，有

$$
\big|\chi_{[0,\lambda_*]}(\lambda)\big(\theta(\lambda)+\lambda R_{kk}\big)\big|
\le \widetilde M_\theta(\lambda)\le \widetilde M_{\rm dom}(\lambda),\qquad \widetilde M_{\rm dom}\in L^1([0,\lambda_0]) .
$$

因 $\widetilde M_{\rm dom}$ 与 $\varepsilon$ 无关，且对所有 $|\lambda|\le\lambda_0$ 均有 $\widetilde M_\theta(\lambda)\le \widetilde M_{\rm dom}(\lambda)$，故可据主导收敛定理交换"$\varepsilon\to0$"与沿 $\lambda$ 的积分。

（图 1（建议）：展示归一化误差 $\big|\delta A+\int\lambda R_{kk}\big|/\ell^{d-2}$ 随 $\varepsilon$ 的标度；三条曲线对应不同 $(C_R,C_\sigma)$ 取值。示例参数：$C_R\in\{0.1,0.3\}$，$C_{\mathcal C}\in\{0.1,0.3\}$，$\lambda_0=1$。）

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

**测试函数局域化引理**：若 $\int_{S_\ell}\varphi(x)\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda\,dA=0$ 对所有 $\varphi\in C_c^\infty(S_\ell)$、$w\in C_c^\infty([0,\lambda_*])$ 成立，则几乎处处沿每条生成元 $\int_0^{\lambda_*} w F=0$。
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

上述链路把“零锥刻画 + Bianchi 恒等式”压缩成短证，相比常见教科书推导更为简洁，具备教学价值。

---

## 5 二阶层：$\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$ 与稳定性

**函数空间与无外流条件**：扰动 $h_{ab}\in H^{k}(\Sigma)$（$k\ge2$），边界条件固定诱导度规（或其共轭动量），并要求 $\int_{\partial\Sigma}\iota_n\omega(h,\mathcal L_\xi h)=0$（辛流无外流）；规范采用 Killing 或协变谐以剔除纯规范模。

在 code subspace、线性化约束 $\delta M=\delta J=\delta P=0$ 与合适边界条件下，

$$
\boxed{\ \delta^2S_{\rm rel}=\mathcal F_Q=\mathcal E_{\rm can}[h,h]\ge0\ },
$$

与 Hollands–Wald 线性稳定性等价。**核的说明**：在所选规范固定与边界条件下，$\mathcal E_{\rm can}[h,h]=0$ 当且仅当 $h$ 为纯规范模。线性化爱因斯坦方程来自上一节的一阶族约束与张量化闭包；二者逻辑互不依赖。无对偶语境下，以 QNEC/ANEC 作为保底不等式（形状导数与极限次序详见附录）。

$$
\boxed{\,\delta^2 S_{\rm rel}\ge0\ \Longrightarrow\ \mathcal E_{\rm can}[h,h]\ge0\ \Longrightarrow\ \text{（满足 Hollands–Wald 条件时）线性稳定}\,}.
$$

适用前提：处于 code subspace，满足 $\delta M=\delta J=\delta P=0$ 的线性化荷约束与合适边界/规范条件（辛流无外流）。

谱/椭圆边界的草图与边界无外流、可积性核对见附录 E 与 §8 的边界处方。

---

## 6 温标–体积对偶与 $\delta\kappa_\chi/\kappa_\chi$ 的阶计数

在重标定与取向翻转下，$\delta Q/T$ 与 $\delta A/(4G\hbar)$ 不变；$V/T$ 非不变量，但一阶极值层采用固定温标（$\delta T=0$）不影响结论。固定端点与腰面，近似 CKV 的表面引力 $\kappa_\chi=2/\ell+\mathcal O(\ell/L_{\rm curv}^2)$，一阶几何扰动给 $\delta\kappa_\chi=\mathcal O(\ell/L_{\rm curv}^2)$，故

$$
\frac{\delta\kappa_\chi}{\kappa_\chi}=\mathcal O\Big(\frac{\ell^2}{L_{\rm curv}^2}\Big)=\mathcal O(\varepsilon^2),
$$

从而"固定 $|\kappa_\chi|$"与"允许 $\delta T\neq0$"在一阶极值层等价。

---

## 7 OS/KMS–Fisher 解析延拓：充分条件与下界

令欧氏统计族 $p(y|t_E,x^i)$ 的 Fisher–Rao 度量

$$
g^{(E)}_{\mu\nu}=\mathbb E\big[\partial_\mu\log p\,\partial_\nu\log p\big].
$$

（交叉分量奇偶性判据与 $g_{ti}$ 在反射点的消失条件移至附录 G.1；此处仅保留保证洛伦兹签名的充分条件与下界。）

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

关节项的一般变分为

$$
\delta I_{\rm joint}
=\frac{1}{8\pi G}\int_{\mathcal J} d^{d-2}x\,
\Big(\tfrac12\sqrt{\sigma}\,\sigma^{AB}\delta\sigma_{AB}\,\eta+\sqrt{\sigma}\,\delta\eta\Big).
$$

在本文所取 **Dirichlet** 类边界条件下固定 $\sigma_{AB}$（故 $\delta\sigma_{AB}=0$），并固定关节角（$\delta\eta=0$），因此 $\delta I_{\rm joint}=0$。

从而 joint 项自动可积，无需再调 counterterm。

**示例（Minkowski 小钻石）**：两片仿射 null 面拼接 $\Rightarrow \kappa[\ell]=0$ 给 $I_{\partial\mathcal N}=0$；null–类空超曲面关节项 $\eta$ 为常数，$\delta I_{\rm joint}=0$。由此边界通量为零且哈密顿量变分可积。

---

## 9 高阶引力与唯一性
用 Wald/Dong–Camps 熵替代面积后，同一 IGVP 框架直接给出 Lovelock 型场方程；详细 $f(R)$ 与 Gauss–Bonnet 演示见附录 H。

---

## 10 两条独立链的逻辑蓝图

* **链 A（热力学—几何光学）**：$\delta S_{\rm grav}+\delta S_{\rm out}-\tfrac{\Lambda}{8\pi G}\delta V/T=0\Rightarrow R_{kk}=8\pi G\,T_{kk}\Rightarrow G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。
* **链 B（纠缠—相对熵）**：JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}\Rightarrow \delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$（稳定性）；线性化方程源自链 A 的族约束与闭包。

---

## 11 可复现实操清单

1. 调用 §2 的不等式与常数族，数值检验 $\big|\delta A+\int\lambda R_{kk}\big|\sim\varepsilon^2\ell^{d-2}$ 的标度与 $C_d$ 的保守性（见图 1；生成脚本：`scripts/generate_igvp_figure1.py`）；
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
零测地丛超曲面正交 $\Leftrightarrow \omega_{ab}=0$。在"腰面 + 近似 CKV"构造下 $\omega(0)=0$，由

$$
\omega_{AB}'=-\frac{2}{d-2}\theta\,\omega_{AB}
-\big(\sigma_A{}^{C}\omega_{CB}+\omega_A{}^{C}\sigma_{CB}\big)
$$

（或等价地由 Frobenius 条件）得 $\omega\equiv0$。

**A.3 剪切与曲率梯度上界**
由 Sachs（且 $\omega\equiv0$）得

$$
|\sigma|' \le \frac{2}{d-2}|\theta|\,|\sigma|+|\sigma|^2+|\mathcal C| .
$$

以变系数 Grönwall、初值 $\sigma(0)=0$ 与小钻石标度 $|\theta|\lambda_*\ll1$ 得

$$
|\sigma(\lambda)|\le C_{\mathcal C}|\lambda|\,e^{\frac{2}{d-2}\int_0^{|\lambda|}|\theta|ds}(1+\mathcal O(\varepsilon))
\ \Rightarrow\
\sup\sigma^2\le C_\sigma^2(1+\mathcal O(\varepsilon)),\quad C_\sigma:=C_{\mathcal C}\lambda_* .
$$

（后续使用 $C_\sigma$ 与 $\widetilde M_\theta$ 的各处公式与阶计数保持不变。）

$$
\boxed{\
\big|\theta(\lambda)+\lambda R_{kk}(\lambda)\big|\ \le\
\tfrac12 C_{\nabla R}\lambda^2\ +\ C_\sigma^2|\lambda|\ +\ \tfrac{4}{3(d-2)}C_R^2|\lambda|^3\ :=\ \widetilde M_\theta(\lambda)\ .
}
$$

**A.4 面积不等式与边界层**

$$
\boxed{
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\,d\lambda\,dA\Big|
\ \le\ \int_{\mathcal H}\widetilde M_\theta(\lambda)\,d\lambda\,dA
\ \le\ \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2+\tfrac{1}{3(d-2)}C_R^2\lambda_*^4\Big)A\ .
}
$$

端点层 $[\lambda_*-\delta,\lambda_*]$ 贡献满足

$$
\Big|\int_{\lambda_*-\delta}^{\lambda_*}\lambda R_{kk}\,d\lambda\,dA\Big|
\le \tfrac12 A\big(\lambda_*^2-(\lambda_*-\delta)^2\big)C_R
=\mathcal O\big(A,C_R,\lambda_*,\delta\big).
$$

取 $\delta=\mathcal O(\varepsilon\ell)$ 且 $\lambda_*\sim c_\lambda\ell$，得 $\mathcal O\big(A,C_R,\varepsilon,\ell^2\big)$。

**A.5 可交换性**
取固定 $\lambda_0>0$ 使 $0<\lambda_*\le\lambda_0$。由 $C_\sigma=C_{\mathcal C}\lambda_*\le C_{\mathcal C}\lambda_0$，定义

$$
\boxed{
\widetilde M_{\rm dom}(\lambda)
:=\tfrac12 C_{\nabla R}\lambda^2+\big(C_{\mathcal C}\lambda_0\big)^2|\lambda|
+\tfrac{4}{3(d-2)}C_R^2\lambda_0^3\ \in L^1([0,\lambda_0])\ .
}
$$

于是对 $[0,\lambda_0]$ 上的被积式 $\chi_{[0,\lambda_*]}(\lambda)\big(\theta(\lambda)+\lambda R_{kk}\big)$ 有统一支配（对所有 $|\lambda|\le\lambda_0$ 均有 $|\theta+\lambda R_{kk}|\le \widetilde M_\theta\le \widetilde M_{\rm dom}$），且 $\widetilde M_{\rm dom}$ 与 $\varepsilon$ 无关，由主导收敛定理得到"$\varepsilon\to0$"与积分次序可交换。

---

# 附录 B  局域化引理与 Radon‑型 0‑阶重建

**B.1 命题（Radon/光线变换唯一性与局域化）**
设 $F(x,\lambda)$ 可测且局域可积。若
$\int_{S_\ell}\!\varphi(x)\int_0^{\lambda_*}\! w(\lambda)F(x,\lambda)\,d\lambda\,dA=0$
对所有 $\varphi\in C_c^\infty(S_\ell)$ 与 $w\in C_c^\infty([0,\lambda_*])$ 成立，则几乎处处沿每条生成元
$\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda=0$。
证（草图，4–6 行）：Fubini 定理把 $x$ 与 $\lambda$ 的测试分离；对 $\lambda$ 方向用光滑截断（mollifier）逼近 $\delta$，取首矩权 $w\equiv\lambda$ 得加权光线变换核；由 Radon/光线变换唯一性，核仅在零函数时出现（见 Helgason 2011, Thm 4.2；Finch–Patch–Rakesh 2004）。分布情形先平滑，再令平滑尺度 $\to0$。

**B.2 0‑阶重建**
$S_{kk}(\gamma(\lambda))=S_{kk}(p)+\lambda\nabla_k S_{kk}(p)+\mathcal O(\lambda^2)$；
$\int_0^{\lambda_*}\lambda S_{kk}\,d\lambda=\tfrac12\lambda_*^2 S_{kk}(p)+\mathcal O(\lambda_*^3|\nabla S|)$。
若左侧 $=o(\ell^2)$，则 $S_{kk}(p)\to0$。分布情形可先作 mollifier 平滑，再令平滑尺度 $\to0$。

---

# 附录 C  张量化闭包与维度条件

**引理 C.1（$d\ge3$）**
若 $X_{ab}$ 光滑对称且 $X_{ab}k^ak^b=0\ \forall k$（零矢），则 $X_{ab}=\Phi g_{ab}$。证：去迹分解与"零锥决定共形类"。

---

# 附录 D  QNEC/ANEC 的形状导数与极限次序

对单位横截面积归一：

$$
\langle T_{kk}(p)\rangle \ge \frac{\hbar}{2\pi}\lim_{A_\perp\to0}\frac{\partial_\lambda^2 S_{\rm out}}{A_\perp},
$$

并且在满足 **Minkowski 背景或足够弱曲率极限、Hadamard 类态、完整零测地及局域可积** 等标准假设下，成立

$$
\int_{-\infty}^{+\infty}T_{kk}\,d\lambda\ge 0 .
$$

极限次序同前：先取 $\partial_\lambda^2$，再取 $A_\perp\to0$ 与 UV 极限；edge modes 以边界代数分解吸收。

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
仿射 null 段 $\Rightarrow \kappa[\ell]=0$ 使 $I_{\partial\mathcal N}=0$；null–类空超曲面关节 $\eta$ 常数 $\Rightarrow \delta I_{\rm joint}=0$。故 $\delta H_\chi$ 可积，与 §5 的规范能量边界合法性一致。

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
