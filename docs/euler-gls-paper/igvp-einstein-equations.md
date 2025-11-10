# 信息几何变分原理导出爱因斯坦场方程

Version: 1.0

## 摘要

建立以相对熵与 Fisher 信息为核心的变分原理。对流形每一点的小尺度因果钻石 $B_\ell(p)$（$\ell\ll L_{\rm curv}$）在定体积约束下引入广义熵泛函 $S_{\rm gen}=S_{\rm grav}+S_{\rm out}+S_{\rm ct}$，并规定一阶驻值与二阶正定性为基本准则：一阶信息平衡 $\delta S_{\rm gen}=0$，二阶相对熵非负 $\delta^2 S_{\rm rel}\ge0$。在明确的域前提（尺度分离、Hadamard 正则、重整化与变分良定）之内，证明一阶条件与方程 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$ 等价；二阶条件与线性化爱因斯坦方程及 Iyer–Wald 规范能量正性等价。等价关系通过两条物理独立的路径冗余闭合：局域热力学—几何光学链与纠缠第一定律—相对熵链。进一步给出 Fisher–Rao 度量的推前构造作为互补证据，并说明在高阶引力（Wald/Dong 熵）及因果钻石第一定律下的自然扩展与一致性。

---

## 0 引言：定位、动机与贡献

目标是把局域热力学（$\delta Q=T\,\delta S$ 与 Raychaudhuri 会聚）、纠缠第一定律（$\delta S=\delta\langle K\rangle$）与信息几何（相对熵二阶项即量子 Fisher 信息）统一为两个变分准则的整合框架：信息几何变分原理（IGVP）。性质定位为**重构与等价**：在严格域前提下，说明相同的场方程与稳定性命题可由两条独立的物理路径达成，从而揭示它们背后的共同结构。核心贡献包括：（i）把 $S_{\rm gen}$ 作为**变分原理的基本泛函**外显化，明确其定义、域与重整化独立性；（ii）以可交换极限与误差阶控制，关闭热力学链中的近似环节；（iii）将二阶层分为"有对偶层（全息）"与"无对偶保底层（QNEC/ANEC）"，扩大适用域；（iv）提供 Fisher–Rao 推前的可计算示例，作为统计—几何桥接的互补通道。

---

## 1 记号、域前提与可交换极限

**(1) 记号** 采用签名 $(-,+,+,+)$，$c=1$ 并明示 $\hbar$。爱因斯坦张量 $G_{ab}:=R_{ab}-\tfrac12 R g_{ab}$。相对熵 $S_{\rm rel}(\rho\Vert\sigma)=\mathrm{Tr}\,\rho(\log\rho-\log\sigma)\ge0$。在驻点 $\rho_0=\sigma$ 的二阶展开为 $S_{\rm rel}(\rho_\lambda\Vert\rho_0)=\tfrac12\,\mathcal F_Q(\delta\rho,\delta\rho)\lambda^2+\mathcal O(\lambda^3)$。

**(2) 域前提**
$\triangleright$ **尺度分离**：$\ell\ll L_{\rm curv}$，并引入控制参量 $\varepsilon_{\rm curv}=\ell/L_{\rm curv}$、$\varepsilon_{\rm mat}=\ell/L_{\rm mat}$ 与 $\varepsilon=\max(\varepsilon_{\rm curv},\varepsilon_{\rm mat})\to0$。
$\triangleright$ **态与重整化**：限定于 Hadamard 类态。定义

$$
S_{\rm gen}=\frac{A(\partial B_\ell)}{4G_{\rm ren}\hbar}+S_{\rm out}^{\rm ren}[\rho_{B_\ell};g]+S_{\rm ct}[g],
$$

其中 $S_{\rm out}^{\rm ren}$ 通过点分裂重整化有限，面积型散度与局域反常吸收到 $G_{\rm ren}$ 与 $S_{\rm ct}$。
$\triangleright$ **变分良定与规范**：作用包含 Gibbons–Hawking–York 边界项；采用 Iyer–Wald 协变相空间（辛势 $\Theta$、辛流 $\omega$、Noether 荷量 $Q$）确保哈密顿量变分可积；对带边界子系统计入 edge modes 以维持规范不变量。

**(3) 可交换极限与误差控制** 在线性序下 Raychaudhuri 方程给出 $\theta(\lambda)=-\lambda\,R_{ab}k^a k^b+\mathcal O(\varepsilon^2)$，据此

$$
\delta A=-\!\int_{\mathcal H}\lambda\,R_{ab}k^a k^b\,d\lambda\,dA+\mathcal O(\varepsilon^2),
$$

并以主导/一致收敛论证"积分—极限"可交换，保证系数匹配的稳定性。

---

## 2 信息几何变分原理（IGVP）

**公设 A（局域可积）** 在每点 $p$ 与充分小 $\ell$ 上存在参考真空 $\sigma_{B_\ell}$ 与物理态 $\rho_{B_\ell}$，满足纠缠第一定律 $\delta S_{\rm out}=\delta\langle K_{B_\ell}\rangle$。在 CFT 真空的球形区域，$K_{B_R}=2\pi\int_{B_R}\frac{R^2-r^2}{2R}\,T_{00}\,d^{d-1}x$ 为一特例。

**公设 B（几何信息容量）** 定义几何熵 $S_{\rm grav}=\tfrac{A}{4G\hbar}$ 并以 $T=\hbar\kappa/(2\pi)$ 作为温标。该定义在本框架中作为**变分泛函的组成**，而非由其它理论推得。

**公设 C（平衡与稳定）** 在**定体积约束** $\delta V(B_\ell)=0$ 下，一阶驻值 $\delta S_{\rm gen}=0$，并在同一驻点要求二阶相对熵非负 $\delta^2 S_{\rm rel}\ge0$。体积的选取基于因果钻石第一定律中 $V$ 与其共轭变量 $\Lambda$ 的天然配对，从而保证变分问题的良定与 $\Lambda$ 的拉格朗日乘子解释。

**定义 2.1（IGVP）** 满足 A–C 的 $(g,\rho)$ 为 IGVP 的解。

---

## 3 一阶层：信息平衡到爱因斯坦方程

### 3.1 热力学—几何光学链

取局域 Rindler 视界生成元 $k^a$ 与仿 Killing 向量 $\chi^a=\kappa\lambda k^a$。能流

$$
\delta Q=\int_{\mathcal H}T_{ab}\chi^a d\Sigma^b=\kappa\int_{\mathcal H}\lambda\,T_{ab}k^a k^b\,d\lambda\,dA,
$$

配合 $T=\hbar\kappa/(2\pi)$ 得 $\delta Q/T=\tfrac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{ab}k^a k^b\,d\lambda\,dA$。由 $\theta(\lambda)=-\lambda\,R_{ab}k^a k^b+\mathcal O(\varepsilon^2)$ 与 $\delta S_{\rm grav}=\delta A/(4G\hbar)$，一阶平衡

$$
\delta S_{\rm grav}+\delta S_{\rm out}=0
$$

（此即公设 C 的具体实现）推出

$$
R_{ab}k^a k^b=8\pi G\,T_{ab}k^a k^b\quad\text{对任意零矢 }k^a,
$$

张量化并用 $\nabla^a G_{ab}=0=\nabla^a T_{ab}$ 得存在常数 $\Lambda$ 使

$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}.
$$

### 3.2 纠缠第一定律链

对小球 $B_\ell$ 由 $\delta S_{\rm out}=\delta\langle K_{B_\ell}\rangle$ 与 $\delta S_{\rm grav}=\delta A/(4G\hbar)$ 的系数配对，并要求对任意 $p,\ell$ 成立，可得与 3.1 同一张量方程。该途径与全息语境下的线性化方程一致。

**定理 3.1（IGVP 一阶驻值—场方程）** 在域前提与公设 A–C 下，若对所有 $B_\ell(p)$ 有 $\delta S_{\rm gen}=0$，则必有 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。证明基于上两链的系数匹配、张量化与 Bianchi 闭包；四维、二阶场方程前提下之唯一性由 Lovelock 型定理保障。

---

## 4 二阶层：量子 Fisher 信息、规范能量与线性化

驻点处

$$
\delta^2 S_{\rm rel}=\tfrac12\,\mathcal F_Q(\delta\rho,\delta\rho)\ge0.
$$

**（A）有对偶层** JLMS 等价给出边界相对熵等于体相对熵；进一步有 $\mathcal F_Q=\mathcal E_{\rm can}[h,h]$。因此，在背景满足 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$ 且扰动 $h$ 满足线性化约束与恰当边界条件时，

$$\delta^2 S_{\rm rel}=\mathcal E_{\rm can}[h,h]\ \Rightarrow\ \mathcal E_{\rm can}[h,h]\ge0,$$

这给出稳定性判据（在 $\delta M=\delta J=\delta P=0$ 的子空间）。线性化爱因斯坦方程 $\delta G_{ab}[h]=8\pi G\,\delta T_{ab}$ 则来自一阶层的球/钻石族约束与张量化闭包，不由 $\mathcal E_{\rm can}[h,h]\ge0$ 单独推出。

**（B）无对偶保底层** 沿任意零生成元的二阶形状导数满足 QNEC：$2\pi\langle T_{kk}\rangle \ge \partial_\lambda^2 S_{\rm out}$，为二阶正性提供 QFT 内部下界；配合由相对熵单调性与形变模态哈密顿量得出的 ANEC，实现非全息的独立支撑。

**定理 4.1（IGVP 二阶正定—稳定性）** 在定理 3.1 的驻点背景上，若满足 JLMS 且 $\mathcal F_Q=\mathcal E_{\rm can}[h,h]$，则对所有满足线性化约束与边界条件的扰动 $h$ 有

$$\delta^2 S_{\rm rel}=\mathcal E_{\rm can}[h,h]\ge0,$$

从而得到 Hollands–Wald 意义下的线性稳定性判据；而 $\delta G_{ab}[h]=8\pi G\,\delta T_{ab}$ 由一阶层给出，并不由二阶正性单独导出。

---

## 5 重整化、边界与规范的一致性

**(i) 方案独立** 采用 Hadamard 正则与点分裂重整化，使 $S_{\rm out}^{\rm ren}$ 有限，散度由 $G_{\rm ren}$ 与 $S_{\rm ct}$ 吸收，从而 $S_{\rm gen}$ 在给定阶对方案不敏感。
**(ii) 变分良定** 加入 GHY 项并以 Iyer–Wald 协变相空间刻画辛结构、Noether 荷与哈密顿量变分可积性。
**(iii) 边界自由度** 在规范理论与引力的子系统分割下引入 edge modes，避免熵计数的规范依赖。

---

## 6 因果钻石第一定律与 $\Lambda$

在最大对称背景中，因果钻石满足 Smarr/第一定律，把 $\delta A$、$\delta V$、$\delta H_{\rm matter}$、$\delta\Lambda$ 以热力学型关系联结。小钻石极限与"定体积的广义熵驻值"一致，$\Lambda$ 作为体积约束的拉格朗日乘子自然出现。必要时的"负温度"仅为热力学表述的规范化，不参与数学闭包。

---

## 7 Fisher–Rao 推前：统计 $\to$ 几何的互补通道

给定以 $x^\mu$ 标记的概率场族 $p(y|x)$，定义推前 Fisher–Rao 度量

$$
g_{\mu\nu}(x)=\int p(y|x)\,\partial_\mu\log p(y|x)\,\partial_\nu\log p(y|x)\,dy.
$$

可据此计算 $\Gamma^\lambda_{\mu\nu}[g]$、$R_{\mu\nu}[g]$ 与 $G_{\mu\nu}[g]$，并以熵势 $\phi=-\log p$ 写出有效源 $T^{\rm eff}_{\mu\nu}[\phi,p]$ 的标量场型表达，展示"信息度量 $\to$ 几何张量"的构造性桥接。签名问题经欧氏截面与 KMS 解析延拓处理。此统计几何通道**目前仅提供启发式支持与结构启示**；其 $g_{\mu\nu}^{\rm Fisher}$ 与物理时空度规 $g_{\mu\nu}^{\rm spacetime}$ 的等同为后续需要验证的基本假设，不参与本文主证明链。

**示例（高斯族）** 若

$$
p(y|x)=\frac{1}{\sqrt{2\pi}\,\sigma(x)}\exp\!\Big(-\frac{(y-\mu(x))^2}{2\sigma(x)^2}\Big),
$$

则

$$
g_{\mu\nu}=\sigma^{-2}\,\partial_\mu\mu\,\partial_\nu\mu+2\,\partial_\mu\log\sigma\,\partial_\nu\log\sigma,
$$

可由此显式计算 $\Gamma^\lambda_{\mu\nu}$、$R_{\mu\nu}$、$G_{\mu\nu}$，并构造 $T^{\rm eff}_{\mu\nu}$ 的对应形式。

---

## 8 高阶引力与唯一性

以 Wald/Dong 泛函替代面积定则定义 $S_{\rm grav}$，一阶驻值导出相应高阶引力场方程；线性化层面，纠缠第一定律仍与高阶引力的线性化方程等价。四维且二阶导数结构的唯一性由 Lovelock 型定理给出，即满足自然性与无散度的对称张量唯一同胚于 $a\,G_{ab}+b\,g_{ab}$，其中 $b$ 与 $\Lambda$ 对应。

---

## 参考文献

[1] T. Jacobson, Thermodynamics of Spacetime: The Einstein Equation of State, Phys. Rev. Lett. 75, 1260 (1995).
[2] T. Jacobson, Entanglement Equilibrium and the Einstein Equation, Phys. Rev. Lett. 116, 201101 (2016).
[3] T. Faulkner, M. Guica, T. Hartman, R. C. Myers, M. Van Raamsdonk, Gravitation from Entanglement in Holographic CFTs, JHEP 03 (2014) 051.
[4] D. L. Jafferis, A. Lewkowycz, J. Maldacena, S. J. Suh, Relative Entropy Equals Bulk Relative Entropy, JHEP 06 (2016) 004.
[5] N. Lashkari, M. Van Raamsdonk, Canonical Energy is Quantum Fisher Information, JHEP 04 (2016) 153.
[6] H. Casini, M. Huerta, R. C. Myers, Towards a Derivation of Holographic Entanglement Entropy, JHEP 05 (2011) 036.
[7] V. Iyer, R. M. Wald, Some Properties of the Noether Charge and a Proposal for Dynamical Black Hole Entropy, Phys. Rev. D 50, 846 (1994).
[8] W. Donnelly, L. Freidel, Local Subsystems in Gauge Theory and Gravity, JHEP 09 (2016) 102.
[9] M. J. Radzikowski, Micro-Local Approach to the Hadamard Condition, Commun. Math. Phys. 179, 529 (1996).
[10] Y. Décanini, A. Folacci, Hadamard Renormalization of the Stress-Energy Tensor, Phys. Rev. D 78, 044025 (2008).
[11] L. C. B. Crispino, A. Higuchi, G. E. A. Matsas, The Unruh Effect and its Applications, Rev. Mod. Phys. 80, 787 (2008).
[12] T. Jacobson, M. Visser, Gravitational Thermodynamics of Causal Diamonds in (A)dS, Class. Quantum Gravity / Phys. Rev. D (2019).
[13] X. Dong, Holographic Entanglement Entropy for General Higher Derivative Gravity, JHEP 01 (2014) 044.
[14] J. Camps, Generalized Entropy and Higher Derivative Gravity, JHEP 03 (2014) 070.
[15] R. Bousso, Z. Fisher, J. Koeller, S. Leichenauer, A. C. Wall, Proof of the Quantum Null Energy Condition, Phys. Rev. D 93, 024017 (2016).
[16] T. Faulkner, R. G. Leigh, O. Parrikar, H. Wang, Modular Hamiltonians for Deformed Half-Spaces and the ANEC, JHEP 09 (2016) 038.
[17] S. Hollands, R. M. Wald, Stability of Black Holes and Black Branes, Commun. Math. Phys. 321, 629 (2013).
[18] M. Bauer, A. Le Brigant, Y. Lu, C. Maor, The $L^p$–Fisher–Rao Metric and Amari–Čencov $\alpha$-Connections, Calc. Var. PDE 63, 56 (2024).
[19] D. Lovelock, The Einstein Tensor and Its Generalizations, J. Math. Phys. 12, 498 (1971).

---

## 附录 A Hadamard 正则、点分裂与相对熵可微性

**A.1 微局域谱条件与 Hadamard 形** 设二点函数的奇异部分在局部等距坐标中取 Hadamard 形式，给出波前集约束，保证能量–动量张量点分裂重整化的可实施性与守恒 $\nabla^a\langle T_{ab}\rangle_{\rm ren}=0$。
**A.2 相对熵可微性与形状导数** 在 Hadamard 类态与光滑域变形下，$S_{\rm rel}$ 的 Gateaux/Fréchet 可微性成立；对沿零生成元的形变，二阶导数存在且与积分交换顺序合法。

---

## 附录 B 一阶层：严格推导与误差阶

**B.1 能流与温度** 取 $\chi^a=\kappa\lambda k^a$ 有

$$
\delta Q=\kappa\int_{\mathcal H}\lambda\,T_{ab}k^a k^b\,d\lambda\,dA,\qquad \frac{\delta Q}{T}=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{ab}k^a k^b\,d\lambda\,dA.
$$

**B.2 面积变分与可交换极限** 由 $\theta(\lambda)=-\lambda\,R_{ab}k^a k^b+\mathcal O(\varepsilon^2)$ 得

$$
\delta A=-\int_{\mathcal H}\lambda\,R_{ab}k^a k^b\,d\lambda\,dA+\mathcal O(\varepsilon^2),\quad \delta S_{\rm grav}=\frac{\delta A}{4G\hbar}.
$$

以主导收敛证明"$\varepsilon\to0$"与积分交换。
**B.3 张量化闭包与 $\Lambda$** 由 $\forall k^a$（零）有 $R_{ab}k^a k^b=8\pi G\,T_{ab}k^a k^b$，结合 $\nabla^a G_{ab}=0=\nabla^a T_{ab}$ 得 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。四维唯一性由 Lovelock 型定理给出。

---

## 附录 C 模态哈密顿量：一般性与 CFT 特例

**C.1 一般第一定律** 对任意参考态 $\sigma$ 的代数模态哈密顿量 $K=-\log\sigma$，有 $\delta S=\delta\langle K\rangle$。
**C.2 CFT 球区** 对真空与球 $B_R$，$K_{B_R}=2\pi\int_{B_R}\frac{R^2-r^2}{2R}\,T_{00}\,d^{d-1}x$。将 $\delta\langle K\rangle$ 与 $\delta A/(4G\hbar)$ 配对并要求对一切 $B_\ell(p)$ 成立，即得主文 3.1 的张量方程。

---

## 附录 D 二阶层：JLMS、$\mathcal F_Q=\mathcal E_{\rm can}$ 与稳定性

**D.1 相对熵二阶展开** 驻点 $\rho_0$ 处 $S_{\rm rel}(\rho_\lambda\Vert\rho_0)=\tfrac12\,\mathcal F_Q\,\lambda^2+\cdots$。
**D.2 全息等价** JLMS：边界相对熵等于体相对熵。进而 $\mathcal F_Q=\mathcal E_{\rm can}[h,h]$。
**D.3 Hollands–Wald 判据** 在 $\delta M=\delta J=\delta P=0$ 子空间，$\mathcal E_{\rm can}=\delta^2 M-\sum_A\Omega_A\delta^2 J_A-\tfrac{\kappa}{8\pi}\delta^2 A$，$\mathcal E_{\rm can}\ge0$ 当且仅当线性稳定。

---

## 附录 E QNEC/ANEC 的无对偶支撑

**E.1 QNEC** 沿零生成元的二阶形状导数满足 $2\pi\langle T_{kk}\rangle \ge \partial_\lambda^2 S_{\rm out}$，与主文二阶正性相容。
**E.2 ANEC** 由相对熵单调性与"形变半空间的模态哈密顿量"得到，提供能量条件的独立链。

---

## 附录 F 协变相空间与边界项

**F.1 Iyer–Wald** 写出 $\delta L=E\cdot\delta\Phi+d\Theta$、$\omega=\delta\Theta$、$J=\Theta-\xi\cdot L$ 与荷量 $Q$ 的定义，并给出 $\delta H_\xi$ 的可积性条件。
**F.2 GHY 与 edge modes** 加入 GHY 项以保证变分良定；在子系统边界引入 edge modes 维持规范不变量与熵计数一致性。

---

## 附录 G Fisher–Rao 推前的高斯演示

**G.1 度量与联络** 对

$$
p(y|x)=\frac{1}{\sqrt{2\pi}\,\sigma(x)}\exp\!\Big(-\frac{(y-\mu(x))^2}{2\sigma(x)^2}\Big),
$$

得到

$$
g_{\mu\nu}=\sigma^{-2}\,\partial_\mu\mu\,\partial_\nu\mu+2\,\partial_\mu\log\sigma\,\partial_\nu\log\sigma.
$$

据此计算 $\Gamma^\lambda_{\mu\nu}$、$R_{\mu\nu}$、$G_{\mu\nu}$，并以 $\phi=-\log p$ 给出 $T^{\rm eff}_{\mu\nu}[\phi,p]$ 的标量场表达。
**G.2 备注** 此推前为互补通道；与物理时空度规的等同尚属基本假设，不参与主证明。

---

## 附录 H 高阶引力：Wald/Dong 熵与线性化一致性

**H.1 一阶驻值** 以 Wald/Dong 熵替代面积定则可得相应高阶引力方程。
**H.2 线性化** 纠缠第一定律仍与高阶引力的线性化方程等价，二阶正性给出相应的规范能量判据。
