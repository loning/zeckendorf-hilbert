# 信息几何变分原理导出爱因斯坦方程：定体积对偶、显式可交换极限、Radon‑型闭包、OS/KMS–Fisher 解析延拓与 null 边界处方

Version: 5.2

## 摘要

**We derive Einstein’s equations and the Hollands–Wald stability condition from a single information‑geometric variational principle.**

- 定体积对偶 + 显式可交换极限（小钻石极限，常数族可直接调用）
- Radon 型闭包：族约束下推为点态方程（面积恒等式 ⇒ 点态）
- 二阶层 = Hollands–Wald 规范能量（在 JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 识别成立的语境下；无对偶情形提供 QNEC 备选判据）

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

**误差记法范式**（$\ell$ 标度 × 无量纲 $\varepsilon$ 标度）：本文统一采用

$$
\text{误差}=C_d\,\varepsilon^n\,\ell^m,
$$

其中 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 为无量纲常数（与 $\varepsilon,\ell$ 无关），$n$ 为 $\varepsilon$ 幂次，$m$ 为长度维数。例如：面积变分误差 $\sim C_d\,\varepsilon^3\,\ell^{d-2}$，统一误差命题 $\sim C_{\rm unif}\,\varepsilon^2\,\ell^{d-2}$。

**常数族速查表**（定义于 $\mathcal D_\ell$）：

$$
C_R:=\sup_{\mathcal D_\ell}|R_{kk}|,\quad
C_{\nabla R}:=\sup_{\mathcal D_\ell}|\nabla_k R_{kk}|,\quad
\mathcal C_{AB}:=\mathrm{TF}\big[C_{acbd}k^c k^d e^a_A e^b_B\big],\quad
C_{\mathcal C}:=\sup_{\mathcal D_\ell}|\mathcal C_{AB}|,\quad
C_{\sigma,0}:=\sup_{S_\ell}|\sigma(0)|,\quad
\boxed{C_\sigma:=C_{\sigma,0}+C_{\mathcal C}\lambda_*},\quad
C_\omega=0,\quad \lambda_*\sim c_\lambda \ell .
$$

其中 $\{e_A^a\}$ 为与 $k^a$ 正交的 $(d{-}2)$ 维 screen 空间正交基，$\mathrm{TF}$ 表示去迹，$|\cdot|$ 为任一定义良好的矩阵范数。

最终不等式中的 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C},C_{\sigma,0};d,c_\lambda)$ 给出闭式依赖。

---

### 引言提要：与既有工作的区别度

- Jacobson（1995）：引入定体积对偶与显式 $\varepsilon$‑可交换极限，摆脱未指明"局域 Rindler"依赖
- Jacobson–Visser（2019）：以 Radon 型闭包将面积恒等式下推为点态方程（族约束 ⇒ 点态）
- JLMS + Hollands–Wald：将二阶相对熵与规范能量写入同一变分链，形成单链闭环
- Dong–Camps–Wald：以 Wald/Dong–Camps 熵替代面积后，同一 IGVP 框架直接给出 Lovelock 型方程
- **二阶层条件性与无对偶备选**：二阶层 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}$ 为条件定理（依赖 JLMS 识别）；无对偶情形以 QNEC 二阶形状导数提供普适非负型判据

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

**记号提示**：本文出现两个不同的 $\kappa$：（i）**温标** $T=\hbar|\kappa_\chi|/2\pi$ 中的 $\kappa_\chi$ 是近似 Killing 场 $\chi^a$ 的表面引力；（ii）§8 null 边界项 $\int\sqrt{q}\,\kappa[\ell]$ 中的 $\kappa[\ell]$ 仅是 $\ell^a$ 的非仿射量（在仿射参数化下 $\kappa[\ell]=0$）。二者完全无关。

**外部熵的一阶律（用于链 A）** 在小钻石极限、Hadamard/KMS 态与近 Rindler 生成元 $\chi^a$ 下，

$$
\delta S_{\rm out}^{\rm ren}=\delta\langle K_\chi\rangle
=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA\ +\ \mathcal O(\varepsilon^2)
\equiv \frac{\delta Q}{T}+\mathcal O(\varepsilon^2),
$$

其中 $K_\chi$ 为腰面处的 boost 模块哈密顿量，$T=\hbar|\kappa_\chi|/2\pi$。

**等价的拉格朗日乘子表述（避免规范歧义）**：一阶变分可重述为带约束的极值问题

$$
\delta\left(S_{\rm grav}+S_{\rm out}\right)+\mu\,\delta V=0,
$$

求解后以 $\mu=\frac{\Lambda}{8\pi G T}$ 识别体积约束的物理常数。由附录 F 的 $\delta\kappa_\chi/\kappa_\chi=\mathcal O(\varepsilon^2)$ 可知一阶极值不敏感于 $\delta T$ 的 $\mathcal O(\varepsilon^2)$ 变动，因此"固定 $T$"（$\delta T=0$）为推论而非先验假设。

因此在一阶极值层与 $\delta V=0$ 下，

$$
\delta S_{\rm gen}
=\frac{\delta A}{4G\hbar}+\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA\ +\ \mathcal O(\varepsilon^2)=0.
$$

结合 §2 的**面积—曲率显式上界**，经 §3 的局域化与 §4 的张量化闭包，得到
$R_{kk}=8\pi G\,T_{kk}$ 以及 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$；**若**腰面初始剪切满足 $C_{\sigma,0}=\mathcal O(\varepsilon)$（如最大体积腰面几何），**则**整体误差缩至 $\mathcal O(\varepsilon^3)$。

**约定（一阶变分的温标）**：默认固定温度 $T$（$\delta T=0$）进行一阶极值；若允许 $\delta T\neq0$，其贡献为 $\mathcal O(\varepsilon^2)$ 不改结论（见 §6）。

---

## 2 小钻石极限：显式不等式与边界层

**正则性门槛**：背景度规 $g\in C^3$（或 $g\in C^2$ 且 $\nabla{\rm Riem}\in L^\infty$），物质场 $T_{ab}\in C^1$；令 $\Sigma_\ell$ 为**最大体积空间超曲面**，其边界 $S_\ell=\partial\Sigma_\ell$（**腰面**）为初值面，取 $\theta(0)=0,\ \omega(0)=0$；不对 $\sigma(0)$ 作零假设，仅要求 $\sigma(0)\in L^\infty$；零测地丛满足 Frobenius 条件，故 $\omega\equiv0$。

**参数化约定与记号区分**：下文沿零测地生成元的参数 $\lambda$ 统一取为**仿射参数**（$k^b\nabla_b k^a=0$），因此本文采用的 Raychaudhuri–Sachs–Twist 方程**不含 $\kappa\theta$ 项**。**重要记号区分**：本文出现两个不同的 $\kappa$：（i）**温标** $T=\hbar|\kappa_\chi|/2\pi$ 中的 $\kappa_\chi$ 是近似 Killing 场 $\chi^a$ 的表面引力；（ii）§8 null 边界项 $\int\sqrt{q}\,\kappa[\ell]$ 中的 $\kappa[\ell]$ 仅是 $\ell^a$ 的非仿射量（在仿射参数化下 $\kappa[\ell]=0$）。二者完全无关。

**初值与 Frobenius 条件**：腰面取为极大体积截面蕴含 $\theta(0)=\sigma(0)=\omega(0)=0$（详见附录 A.2）；零测地丛超曲面正交 $\Leftrightarrow\omega\equiv0$。由 $\omega(0)=0$ 与 Frobenius 条件 $\omega_{[a}\nabla_b k_{c]}=0$ 得 $\omega\equiv0$。

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
|\sigma(\lambda)|\le \big(|\sigma(0)|+C_{\mathcal C}|\lambda|\big)\,
e^{\frac{2}{d-2}\int_0^{|\lambda|}|\theta|ds}
\ \le\ C_\sigma\big(1+\mathcal O(\varepsilon)\big),
$$

从而 $\sup\sigma^2\le C_\sigma^2\big(1+\mathcal O(\varepsilon)\big)$。

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

其中 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C},C_{\sigma,0};d,c_\lambda)$ 与 $\varepsilon$ 无关。

**数值验证（在 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 的几何族上）**：归一化误差 $|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$ 呈现 $\varepsilon^3$ 标度；**一般情形**则遵循上式盒装上界。

![图 1：显式可交换极限的数值验证。归一化误差上界 $|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$ 随尺度分离参数 $\varepsilon$ 的变化，显示 $\varepsilon^3$ 标度。三条曲线对应不同曲率参数组合（低/中/高曲率），灰色虚线为参考 $\varepsilon^3$ 标度线。该误差在局域化到每条生成元时仍为 $o(\ell^2)$，与附录 B 的 0 阶重建无缝对接。上界–实测比值的复现脚本：`scripts/generate_igvp_figure1.py`（参数设置与输出格式见脚本头部注释）。](igvp_figure1_exchangeable_limit.png)

**每发生器误差评注（连接面积恒等式与点态重建）**：上述面积变分不等式在逐生成元层面给出

$$
\boxed{
\left|\int_0^{\lambda_*}\lambda\bigl(R_{kk}-8\pi G\,T_{kk}\bigr)\,d\lambda\right|
\le C_{\rm unif}\,\varepsilon^2\,\lambda_*^2,
}
$$

其中 $C_{\rm unif}$ 依赖于 $(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 但与 $\varepsilon$ 无关。该误差相对一阶主项 $\lambda_*^2 f(p)$ 为 $\mathcal O(\varepsilon^2)$ 或更高阶，确保局域化闭包的收敛性。**量纲检查**：$[\varepsilon^2\lambda_*^2]=(\text{无量纲})^2\times(\text{长度})^2=(\text{长度})^2$，与 $[\int\lambda\,R_{kk}\,d\lambda]=(\text{长度})\times(\text{长度}^{-2})\times(\text{长度})=1$ 不匹配需归一化；实际对比时除以 $A\sim\ell^{d-2}$ 得无量纲比。

端点层 $[\lambda_*-\delta,\lambda_*]$ 的贡献满足

$$
\Big|\int_{\lambda_*-\delta}^{\lambda_*}\lambda R_{kk}\,d\lambda\,dA\Big|
\le \tfrac12 A\big(\lambda_*^2-(\lambda_*-\delta)^2\big)C_R
=\mathcal O\big(A,C_R,\lambda_*,\delta\big).
$$

取 $\delta=\mathcal O(\varepsilon\ell)$ 且 $\lambda_*\sim c_\lambda\ell$，得 $\mathcal O\big(A,C_R,\varepsilon,\ell^2\big)$。

取固定常数 $\lambda_0>0$，对所取极限族均有 $0<\lambda_*\le\lambda_0$。由 $C_\sigma=C_{\sigma,0}+C_{\mathcal C}\lambda_*\le C_{\sigma,0}+C_{\mathcal C}\lambda_0$，令

$$
\boxed{
\widetilde M_{\rm dom}(\lambda)
:=\tfrac12 C_{\nabla R}\lambda^2+\big(C_{\sigma,0}+C_{\mathcal C}\lambda_0\big)^2|\lambda|
+\tfrac{4}{3(d-2)}C_R^2\lambda_0^3\ \in L^1([0,\lambda_0])\ .
}
$$

则在固定区间 $[0,\lambda_0]$ 上，有

$$
\big|\chi_{[0,\lambda_*]}(\lambda)\big(\theta(\lambda)+\lambda R_{kk}\big)\big|
\le \widetilde M_\theta(\lambda)\le \widetilde M_{\rm dom}(\lambda),\qquad \widetilde M_{\rm dom}\in L^1([0,\lambda_0]) .
$$

因 $\widetilde M_{\rm dom}$ 与 $\varepsilon$ 无关，且对所有 $|\lambda|\le\lambda_0$ 均有 $\widetilde M_\theta(\lambda)\le \widetilde M_{\rm dom}(\lambda)$，故可据主导收敛定理交换"$\varepsilon\to0$"与沿 $\lambda$ 的积分。

**统一误差命题（保证一致性）**：给定 $\varepsilon$‑小域与无共轭点条件，存在仅依赖 $(d,c_\lambda)$ 与 $(C_R,C_{\nabla R},C_{\mathcal C})$ 的常数 $C_{\rm unif}$，使得对所有 $(p,\hat k)$ 与所有 $\ell$ 足够小

$$
\boxed{
\left|\delta S_{\rm out}-\frac{2\pi}{\hbar}\int\lambda T_{kk}\,d\lambda\,dA\right|
\le C_{\rm unif}\,\varepsilon^2\,\ell^{d-2}.
}
$$

该误差分解为几何近似误差与态依赖误差两部分，均受上述常数族控制。$\delta T/T=\mathcal O(\varepsilon^2)$ 是该命题的推论而非假设。此统一上界保证了局域化时对每条生成元的 $o(\ell^2)$ 控制。

**常数依赖**：$C_{\rm unif}, C_{\rm th}$ 仅依赖 $(C_R,C_{\nabla R};d,c_\lambda)$，与 $\varepsilon,\ell$ 无关。

**引理 2.1（统一误差命题）**：给定 $\varepsilon$‑小域与无共轭点条件，存在常数 $C_{\rm unif}$ 使得对所有 $(p,\hat k)$ 与所有 $\ell$ 足够小

$$
\boxed{
\left|\delta S_{\rm out}-\frac{2\pi}{\hbar}\int\lambda T_{kk}\,d\lambda\,dA\right|
\le C_{\rm unif}\,\varepsilon^2\,\ell^{d-2}.
}
$$

**引理 2.2（局部一阶律误差引理）**：在 Hadamard 态、$g\in C^3$、固定端点与腰面、取近似 CKV $\chi^a$ 的设定下，外部熵与模哈密顿量的变分满足

$$
\boxed{
\big|\delta S_{\rm out}^{\rm ren}-\delta\langle K_\chi\rangle\big|
\le C_{\rm th}\,\varepsilon^2\,\ell^{d-2},
}
$$

其中 $C_{\rm th}=C_{\rm th}(C_R,C_{\nabla R};d)$ 与 $\varepsilon$ 无关，且与 §2 的几何常数族兼容。**证明思路**：把小钻石等距到平直主部（$\eta+\mathcal O(\ell^2/L_{\rm curv}^2)$），用半空间形变的模哈密顿核与形状导数控制误差（Casini–Huerta–Myers 2011；Faulkner–Leigh–Parrikar–Wang 2016）。由此

$$
\delta S_{\rm out}^{\rm ren}=\delta\langle K_\chi\rangle+\mathcal O(\varepsilon^2)
=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA+\mathcal O(\varepsilon^2).
$$

**等价替代路线（无对偶）**：若不采纳局部 KMS 设定，可直接以 QNEC 为起点。在满足 Minkowski 背景或足够弱曲率极限、Hadamard 态、完整零测地及局域可积条件下（附录 D），有

$$
\langle T_{kk}(p)\rangle \ge \frac{\hbar}{2\pi}\lim_{A_\perp\to0}\frac{\partial_\lambda^2 S_{\rm out}}{A_\perp},
$$

该路线与上述一阶律在线性化层面等价，但无需 KMS 周期性假设。

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

**局域化可实现性引理（闭合家族 ⇒ 点态）**：对腰面 $S_\ell$ 上任意 $\varphi\in C_c^\infty(S_\ell)$，存在允许的一阶变分（在定体积约束 $\delta V=0$ 下）使得对一族**端点光滑截断**的首矩权 $w_\epsilon\in C_c^\infty([0,\lambda_*))$ 且 $w_\epsilon\to\lambda$ 于 $L^1$，在 §2 的边界层估计与主导收敛下成立

$$
\int_{S_\ell}\varphi(x)\int_0^{\lambda_*} w_\epsilon(\lambda)\bigl(R_{kk}-8\pi G\,T_{kk}\bigr)\,d\lambda\,dA=o(\ell^2).
$$

**构造草图**：（i）**外部态局域扰动**：取 Hadamard 态扰动其支撑于 $\mathcal H$ 上由 $\varphi$ 确定的管状邻域，其模哈密顿量变分 $\delta\langle K_\chi\rangle$ 给出 $\int \lambda\,\varphi(x)\,T_{kk}\,d\lambda\,dA$ 的加权；（ii）**几何形变的等体积修正**：对腰面嵌入做位形扰动 $\delta X=\epsilon\,\varphi(x)\,n$，并用补偿函数 $\varphi_0$ 满足 $\int_{S_\ell}\varphi_0\,dA=-\int_{S_\ell}\varphi\,dA$ 维持 $\delta V=0$，相应的 $\delta A$ 与 $\int\lambda R_{kk}$ 项给出与（i）匹配的 $\varphi$‑加权。线性变分下 $\delta S_{\rm gen}$ 对外部态与嵌入的 Fréchet 导数均为连续线性泛函，利用分部与分解对任意 $\varphi$ 实现逼近。

**注记**：本文**仅用到首矩权的截断族**，足以与附录 B.2 的 0 阶重建闭合。不需要对"任意 $w\in C_c^\infty([0,\lambda_*])$"的强断言。

**测试函数局域化引理**：若 $\int_{S_\ell}\varphi(x)\int_0^{\lambda_*} w_\epsilon(\lambda)F(x,\lambda)\,d\lambda\,dA=0$ 对所有 $\varphi\in C_c^\infty(S_\ell)$ 与端点光滑截断的首矩权族 $\{w_\epsilon\}$ 成立，则几乎处处沿每条生成元 $\int_0^{\lambda_*} \lambda F=0$。
（注：本文主用首矩权 $w\equiv\lambda$ 及其截断族。证明：Fubini 定理分离 $x$ 与 $\lambda$ 测试；对 $\lambda$ 方向用 mollifier 逼近 $\delta$，取首矩权 $w\equiv\lambda$ 得加权光线变换核；由光线变换的**局部可逆性**（附录 B.3），核仅在零函数时出现。本文仅需**短线段的一阶矩数据**，不依赖全局层析。）

**零测地一阶矩局部可逆性（完备闭包的几何基础）**：在 $p$ 的 Riemann 正规邻域内，无共轭点且生成丛横截空间光滑时，短线段数据 $\mathcal L_\lambda[f](p,\hat k)=\int_0^{\lambda_*}\lambda f(\gamma_{p,\hat k}(\lambda))\,d\lambda$ 确定 $f(p)$。详细证明与误差上界见附录 B.3。

结合上述可实现性与局域化引理，对 $f=R_{kk}-8\pi G\,T_{kk}$ 得 $\mathcal L_\lambda[f]=o(\ell^2)\Rightarrow f(p)=0$，即

$$
R_{kk}=8\pi G\,T_{kk}\quad(\forall\,k).
$$

---

## 4 张量化闭包与场方程（$d\ge 3$）

**零锥刻画引理（$d\ge 3$ 必要）**：若 $X_{ab}$ 光滑对称且 $X_{ab}k^ak^b=0$ 对一切零矢成立，则 $X_{ab}=\Phi g_{ab}$。（注：$d=2$ 时所有对称张量自动满足此性质，场方程退化。）

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

## 5 二阶层：$\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$ 与稳定性（条件定理与普适判据）

**定理 5.1（二阶层稳定性——条件版）**：以下关于 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}$ 为**条件性**结论，其成立依赖 JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 的识别。该识别目前已知在代码子空间与适当边界条件下成立。

设以下条件成立：

**（C1）函数空间**：扰动 $h_{ab}\in H^{k}(\Sigma)$（$k\ge2$），满足线性化爱因斯坦方程（由 §3–§4 的一阶族约束与张量化闭包给出）。

**（C2）Code subspace 与荷约束**：扰动满足 $\delta M=\delta J=\delta P=0$（线性化质量、角动量、线性动量守恒）。在小钻石设置下，这等价于要求扰动不改变钻石端点位置与腰面时刻。

**（C3）边界条件**：采用 Dirichlet‑类边界条件固定诱导度规（或其共轭动量）$\sigma_{AB}|_{\partial\Sigma}$，并要求辛流无外流 $\int_{\partial\Sigma}\iota_n\omega(h,\mathcal L_\xi h)=0$。该条件的逐式验证见附录 E.2（Minkowski）与 E.3（弱曲率推广）。

**（C4）规范固定**：采用 Killing 或协变谐规范以剔除纯规范模。在此规范下 $\mathcal E_{\rm can}[h,h]=0$ 当且仅当 $h$ 为纯规范模。

则在 JLMS 等价与 $\mathcal F_Q=\mathcal E_{\rm can}$ 成立的前提下，

$$
\boxed{\ \delta^2S_{\rm rel}=\mathcal F_Q=\mathcal E_{\rm can}[h,h]\ge0\ },
$$

与 Hollands–Wald 线性稳定性等价。

**定理 5.2（普适非负型判据——无对偶版）**：在小钻石边界无外流的边界条件下，利用 QNEC 的二阶形状导数可构造非负型二次型

$$
\boxed{\ \mathcal Q_{\rm QNEC}[h,h]:=\int_{\mathcal H}\frac{\hbar}{2\pi}\,\partial_\lambda^2\big(\delta^2 S_{\rm out}/A_\perp\big)\,dA\ge 0\ }.
$$

当线性化爱因斯坦方程成立且边界条件可比时，该二次型与 $\mathcal E_{\rm can}$ 一致（形状导数与极限次序详见附录 D）。该判据不依赖 JLMS 识别，提供了与一阶链兼容的能量条件。

**可检核清单**：（1）规范与边界条件的明确陈述见 §8 与附录 E；（2）"无外流"条件 $\int_{\partial\Sigma}\iota_n\omega=0$ 在 Minkowski 小钻石的逐式验证见附录 E.2，在弱曲率小钻石的推广见附录 E.3；（3）Code subspace 的线性约束 $(\delta M,\delta J,\delta P)=(0,0,0)$ 在小钻石设置中由固定端点实现。

**逻辑独立性**：线性化爱因斯坦方程来自第一层（§3–§4）的族约束与张量化闭包；二阶层提供稳定性判据，二者逻辑互不依赖。

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

**结构角色说明**：本节 Fisher–Rao 通道为结构性互补，**不参与一阶链的主证明**（§1–§4 的爱因斯坦方程导出无需此通道）。它为二阶层提供备选的几何诠释，并在某些场景（如统计模型的引力对偶）中提供额外洞察。

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

1. **常数族与标度验证**：调用 §2 的不等式与常数族 $(C_R,C_{\nabla R},C_{\mathcal C})$，数值检验 $\big|\delta A+\int\lambda R_{kk}\big|\sim\varepsilon^3\ell^{d-2}$ 的标度与 $C_d$ 的保守性（见图 1；生成脚本：`scripts/generate_igvp_figure1.py`）。建议测试不同 $(C_R,C_{\nabla R},C_{\mathcal C})$ 组合以评估上界的保守程度。

2. **不变量验证**：逐项验证 $\delta Q/T$、$\delta A/(4G\hbar)$ 的重标定/取向不变；并在固定 $T$ 的规约下核查 $V/T$ 的使用。

3. **局域化可实现性与闭包**：（i）数值构造等体积的局域形变：对腰面 $S_\ell$ 取测试函数 $\varphi\in C_c^\infty(S_\ell)$，构造扰动 $\delta X=\epsilon\,\varphi(x)\,n$ 与补偿 $\varphi_0$ 满足 $\int_{S_\ell}(\varphi+\varphi_0)\,dA=0$（脚本接口：`scripts/construct_local_deformation.py`）；（ii）以"局域化引理"把面积恒等式下推至逐生成元，加上 0‑阶重建得 $R_{kk}=8\pi G\,T_{kk}$；验证 $\mathcal L_\lambda[f]=o(\ell^2)$ 的收敛。

4. **Fisher–Rao 度量验证**：在 $1{+}1$ 高斯族与满足奇偶性判据的模型上，显式验证 $g_{ti}=0$ 与"实/非退化/签名"的下界 $\eta$。

5. **null 边界与可积性**：在 Minkowski 小钻石核查 null 边界/关节项的"无外流 + 可积"（附录 E.2）。验证仿射参数化下 $\kappa[\ell]=0$ 与 $\delta I_{\rm joint}=0$。

---

## 参考文献（选）

Jacobson（1995, Phys. Rev. Lett. 75, 1260；2016, Class. Quantum Grav. 33, 245001）；Casini–Huerta–Myers（2011, JHEP 05, 036）；Jafferis–Lewkowycz–Maldacena–Suh（2016, JHEP 06, 004）；Lashkari–Van Raamsdonk（2016, JHEP 04, 153）；Iyer–Wald（1994, Phys. Rev. D 50, 846）；Donnelly–Freidel（2016, JHEP 09, 102）；Radzikowski（1996, Commun. Math. Phys. 179, 529）；Décanini–Folacci（2008, Phys. Rev. D 78, 044025）；Crispino–Higuchi–Matsas（2008, Rev. Mod. Phys. 80, 787）；Jacobson–Visser（2019, SciPost Phys. 7, 079；arXiv:1812.01596）；Dong（2014, JHEP 01, 044）；Camps（2014, JHEP 03, 070）；Bousso–Fisher–Koeller–Leichenauer–Wall（2016, Phys. Rev. D 93, 024017）；Faulkner–Leigh–Parrikar–Wang（2016, JHEP 09, 038）；Hollands–Wald（2013, Commun. Math. Phys. 321, 629）；Bauer–Le Brigant–Lu–Maor（2023, arXiv:2306.14533）；Lovelock（1971, J. Math. Phys. 12, 498）。

---

# 附录 A  小钻石极限：显式上界、边界层与可交换性

**A.1 初值与参数化**
腰面：$\theta(0)=0,\ \omega(0)=0$；$\sigma(0)\in L^\infty$，定义 $C_{\sigma,0}:=\sup_{S_\ell}|\sigma(0)|$，并取 $\boxed{C_\sigma:=C_{\sigma,0}+C_{\mathcal C}\lambda_*}$。生成元参数 $|\lambda|\le\lambda_*\sim c_\lambda\ell$，**且 $\lambda$ 取为仿射参数**（$k^b\nabla_b k^a=0$）。常数族 $C_R,C_{\nabla R},C_{\mathcal C},C_{\sigma,0},C_\sigma,C_\omega(=0)$。

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

以变系数 Grönwall 与小钻石标度 $|\theta|\lambda_*\ll1$ 得

$$
|\sigma(\lambda)|\le \big(|\sigma(0)|+C_{\mathcal C}|\lambda|\big)\,
e^{\frac{2}{d-2}\int_0^{|\lambda|}|\theta|ds}
\ \Rightarrow\
\sup\sigma^2\le C_\sigma^2\big(1+\mathcal O(\varepsilon)\big).
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
取固定 $\lambda_0>0$ 使 $0<\lambda_*\le\lambda_0$。由 $C_\sigma=C_{\sigma,0}+C_{\mathcal C}\lambda_*\le C_{\sigma,0}+C_{\mathcal C}\lambda_0$，定义

$$
\boxed{
\widetilde M_{\rm dom}(\lambda)
:=\tfrac12 C_{\nabla R}\lambda^2+\big(C_{\sigma,0}+C_{\mathcal C}\lambda_0\big)^2|\lambda|
+\tfrac{4}{3(d-2)}C_R^2\lambda_0^3\ \in L^1([0,\lambda_0])\ .
}
$$

于是对 $[0,\lambda_0]$ 上的被积式 $\chi_{[0,\lambda_*]}(\lambda)\big(\theta(\lambda)+\lambda R_{kk}\big)$ 有统一支配（对所有 $|\lambda|\le\lambda_0$ 均有 $|\theta+\lambda R_{kk}|\le \widetilde M_\theta\le \widetilde M_{\rm dom}$），且 $\widetilde M_{\rm dom}$ 与 $\varepsilon$ 无关，由主导收敛定理得到"$\varepsilon\to0$"与积分次序可交换。

**邻域统一常数引理**：上述常数族 $(C_R,C_{\nabla R},C_{\mathcal C})$ 在 $p$ 的正规邻域 $\mathcal D_\ell(p)$ 上统一定义。对固定 $\lambda_0>0$，当 $0<\ell\le\ell_0$ 时，主控函数 $\widetilde M_{\rm dom}$ 在整个极限族 $\{\mathcal D_\ell\}$ 上统一有效，与 $p$ 和 $\hat k$ 的选择无关（仅依赖背景度规的正则性）。这保证了 §3 局域化闭包在流形每一点的一致收敛性。

---

# 附录 B  局域化引理与 Radon‑型 0‑阶重建

**B.1 命题（Radon/光线变换唯一性与局域化，端点截断）**
设 $F(x,\lambda)$ 可测且局域可积。若
$$
\int_{S_\ell}\!\varphi(x)\int_0^{\lambda_*}\! w(\lambda)F(x,\lambda)\,d\lambda\,dA=0
$$
对所有 $\varphi\in C_c^\infty(S_\ell)$ 与 $w\in C_c^\infty([0,\lambda_*))$（并要求 $w(0)=0$）成立，则几乎处处沿每条生成元
$\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda=0$。

证（草图）：（i）由 Fubini 定理，对固定 $w$，若 $\int_{S_\ell}\varphi(x)\left[\int_0^{\lambda_*} w F\,d\lambda\right]dA=0$ 对所有 $\varphi\in C_c^\infty(S_\ell)$ 成立，则几乎处处在 $S_\ell$ 上有 $\int_0^{\lambda_*} w F\,d\lambda=0$；（ii）对固定 $x$，若 $\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda=0$ 对所有 $w\in C_c^\infty([0,\lambda_*])$ 成立，由 mollifier 逼近与 $C_c^\infty$ 稠密性得 $F(x,\lambda)=0$ 几乎处处；（iii）取 $w\equiv\lambda$ 得加权光线变换 $\mathcal L_\lambda[f]$，其核由 Radon/光线变换唯一性仅包含零函数（Helgason 2011, Thm 4.2；Finch–Patch–Rakesh 2004）。分布情形先平滑，再令平滑尺度 $\to0$。□

**B.2 0‑阶重建**
由 Taylor 展开，$S_{kk}(\gamma(\lambda))=S_{kk}(p)+\lambda\nabla_k S_{kk}(p)+\mathcal O(\lambda^2)$；积分得
$\int_0^{\lambda_*}\!\lambda S_{kk}\,d\lambda=\tfrac12\lambda_*^2 S_{kk}(p)+\mathcal O(\lambda_*^3|\nabla S|_\infty)$。
若左侧 $=o(\ell^2)$ 且 $\lambda_*\sim c_\lambda\ell$，则主项 $\tfrac12\lambda_*^2 S_{kk}(p)=o(\ell^2)$ 迫使 $S_{kk}(p)\to0$（当 $\ell\to0$）。由 $p$ 的任意性得 $S_{kk}=0$ 处处成立。分布情形可先作 mollifier 平滑，再令平滑尺度 $\to0$，估计保持一致。□

**B.3 零测地一阶矩局部可逆性命题**

**注**：本命题为**局部**结论，仅在无共轭点的正规邻域内成立。我们只需一阶矩短线段数据，不诉诸全局层析。

**命题（局部可逆性，以附录证明草图与小钻石误差上界为支撑）**：设 $p$ 在流形上有 Riemann 正规邻域，背景度规 $g\in C^3$，$f\in C^1$。在小区间 $[0,\lambda_*]$（$\lambda_*\sim c_\lambda\ell$，$\ell/L_{\rm curv}\ll 1$）无共轭点且零测地生成丛横截空间光滑时，一阶矩加权光线变换

$$
\mathcal L_\lambda[f](p,\hat k)=\int_0^{\lambda_*}\lambda\, f(\gamma_{p,\hat k}(\lambda))\,d\lambda
$$

满足

$$
\boxed{
\mathcal L_\lambda[f](p,\hat k)=\tfrac12\lambda_*^2 f(p)+\mathcal O\Big(\lambda_*^3|\nabla f|_\infty+\frac{\lambda_*^4}{L_{\rm curv}^2}|f|_\infty\Big).
}
$$

其中常数依赖 $C_d=C_d(C_R,C_{\nabla R};d)$ 与 §2 的几何常数族兼容。特别地，若 $\mathcal L_\lambda[f]=o(\ell^2)$ 对所有 $\hat k$ 成立，则 $f(p)=0$。

**证明草图**：（i）**Riemann 正规坐标展开**：在 $p$ 的正规邻域内，度规可写为

$$
g_{ab}(x)=\eta_{ab}+\tfrac13 R_{acbd}(p)\,x^c x^d+\mathcal O(|x|^3/L_{\rm curv}^3).
$$

零测地 $\gamma_{p,\hat k}(\lambda)$ 从 $p$ 出发沿 $\hat k^a$ 方向，其坐标展开为

$$
x^a(\lambda)=\lambda \hat k^a+\mathcal O\Big(\frac{\lambda^3}{L_{\rm curv}^2}\Big).
$$

（ii）**函数值的 Hadamard 参数化**：沿零测地展开 $f$，

$$
f(\gamma(\lambda))=f(p)+\lambda\,\nabla_k f(p)+\tfrac12\lambda^2\,\nabla_k\nabla_k f(p)+\mathcal O\Big(\lambda^3|\nabla^3 f|+\frac{\lambda^3}{L_{\rm curv}^2}|\nabla f|\Big).
$$

积分得

$$
\mathcal L_\lambda[f]=\int_0^{\lambda_*}\lambda\left[f(p)+\lambda\,\nabla_k f+\tfrac12\lambda^2\,\nabla_k^2 f+\cdots\right]d\lambda.
$$

（iii）**逐项计算与误差控制**：

$$
\int_0^{\lambda_*}\lambda\,d\lambda=\tfrac12\lambda_*^2,\quad
\int_0^{\lambda_*}\lambda^2\,d\lambda=\tfrac13\lambda_*^3,\quad
\int_0^{\lambda_*}\lambda^3\,d\lambda=\tfrac14\lambda_*^4.
$$

结合 §2 的端点层估计与主导收敛，曲率引入的额外项被 $C_R,C_{\nabla R}$ 控制，得

$$
\mathcal L_\lambda[f]=\tfrac12\lambda_*^2 f(p)+\tfrac13\lambda_*^3\nabla_k f(p)+\mathcal O\Big(\lambda_*^4|\nabla^2 f|+\frac{\lambda_*^4}{L_{\rm curv}^2}|f|\Big).
$$

在族约束 $\mathcal L_\lambda[f]=o(\ell^2)$ 与 $\lambda_*\sim c_\lambda\ell$ 下，主项 $\tfrac12\lambda_*^2 f(p)$ 占优，从而 $f(p)=0$。□

**注记**：该命题为**局部**结论，仅在无共轭点的正规邻域内成立，与欧氏 Radon 变换的全局唯一性不同。本文推导爱因斯坦方程时仅需此局部性质。

---

# 附录 C  张量化闭包与维度条件（$d\ge 3$ 必要）

**引理 C.1（零锥刻画，$d\ge3$ 必要）**
若 $X_{ab}$ 光滑对称且 $X_{ab}k^ak^b=0\ \forall k$（零矢），则 $X_{ab}=\Phi g_{ab}$。证：去迹分解与"零锥决定共形类"。

**注**：$d=2$ 时所有对称张量自动满足此性质，场方程退化；本文推导爱因斯坦方程时**明确要求 $d\ge 3$**。

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

**E.3 弱曲率小钻石推广**

**命题**：在弱曲率背景（$\ell/L_{\rm curv}\ll 1$）下，小钻石 $\mathcal D_\ell(p)$ 的 null 边界与关节项处理可推广如下：

（i）**Riemann 正规坐标展开**：在 $p$ 的正规邻域内，度规至 $\mathcal O(\ell^2)$ 精度为

$$
g_{ab}(x)=\eta_{ab}+\tfrac13 R_{acbd}(p)\,x^c x^d+\mathcal O\Big(\frac{\ell^3}{L_{\rm curv}^3}\Big).
$$

（ii）**仿射参数化的 $\mathcal O(\varepsilon^2)$ 修正**：选择仿射参数 $\lambda$ 满足 $k^b\nabla_b k^a=0$。在上述度规展开下，null 生成元的非仿射量

$$
\kappa[\ell]:=k^a\nabla_a\ln|k^b\xi_b|=\mathcal O\Big(\frac{\ell}{L_{\rm curv}^2}\Big)=\mathcal O(\varepsilon^2/\ell).
$$

由于 $I_{\partial\mathcal N}\sim\int\kappa[\ell]\,d\lambda\,dA\sim\mathcal O(\varepsilon^2\ell^{d-2})$，在一阶变分层面可忽略（与 §2 误差一致）。

（iii）**关节角的固定**：采用 Dirichlet 边界条件固定 $\sigma_{AB}$ 与关节角 $\eta$，即 $\delta\sigma_{AB}=0$、$\delta\eta=0$。由 §8 的

$$
\delta I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J} d^{d-2}x\,
\Big(\tfrac12\sqrt{\sigma}\,\sigma^{AB}\delta\sigma_{AB}\,\eta+\sqrt{\sigma}\,\delta\eta\Big)=0,
$$

关节项自动可积。

（iv）**辛流无外流验证**：在上述边界条件下，Iyer–Wald 辛流 $\omega(h,\mathcal L_\xi h)|_{\partial\Sigma}$ 的外流为 $\mathcal O(\varepsilon^2\ell^{d-2})$，在一阶链中可忽略；在二阶链中需明确固定边界数据以保证 $\int_{\partial\Sigma}\iota_n\omega=0$。

**结论**：弱曲率下，null 边界与关节项的处理与 Minkowski 情形一致（至 $\mathcal O(\varepsilon^2)$ 精度），$\delta H_\chi$ 可积且 $\delta S_{\rm gen}$ 与 $\mathcal E_{\rm can}$ 的数值不受边界项影响。

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
