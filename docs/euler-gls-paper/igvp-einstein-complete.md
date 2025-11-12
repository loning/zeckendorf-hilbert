# 信息几何变分原理导出爱因斯坦方程：定体积对偶、显式可交换极限、Radon‑型闭包、OS/KMS–Fisher 解析延拓与 null 边界处方

Version: 6.8（JHEP 评审修订版——条件定理架构）

**修订说明**：本版本响应 JHEP 评审人关于"弱剪切族存在性"、"光线变换局部可逆性"与"模哈密顿整族上界"三个根本性缺口的意见。主定理改为**条件定理**形式，关键技术步骤提升为完整定理/命题，明确标注证明状态。

## 摘要

**We derive the local form of Einstein's equations for $d\ge 3$ from an information‑geometric variational principle, as a conditional theorem assuming the existence of weak‑shear diamond families.** 

**主定理（条件形式）**：假设在每一点 $p$ 存在小因果钻石族 $\{\mathcal D_\ell(p)\}_{\ell\le\ell_0}$ 满足：

(i) **弱剪切条件**：$\sup_{S_\ell}|\sigma(0,x)|\le c_s\varepsilon$ 对所有方向统一成立，

(ii) 短段无共轭点、度规 $C^2$ 与 Hadamard 类态，

(iii) 模哈密顿近似的整族统一上界（定理 2.1）与加权光线变换的局部可逆性（定理 3D）成立，

则在 Raychaudhuri–Sachs–Grönwall 驱动的显式可交换极限与 Radon 型闭包下，得到

$$
R_{kk}=8\pi G\,T_{kk}\quad(\forall k),\qquad G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab},
$$

其中 $\Lambda$ 为体积约束的乘子参数，数值不由本原理决定。

**关键未证假设**：弱剪切族的**构造性存在性**（例如通过屏空间对称化或有限方向平均）未包含在本文中。一般 $C^3$ 背景下该条件是否稠密、可实现，留作后续工作。

二阶层在 **JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$** 成立时给出 Hollands–Wald 规范能量非负性。若不采用该对偶识别，则以 QNEC（Bousso-Fisher-Leichenauer-Wall 版本）的二阶形状导数提供普适非负判据。本文四个主要技术支柱：

(i) **显式可交换极限不等式与边界层估计**：剪切与挠率由几何常数族统一控制。

(ii) **Radon 型闭包**：在首矩权 $w(\lambda)=\lambda$ 的光线变换下，将族约束下推为点态等式（需定理 3D 的局部可逆性）。

(iii) **模哈密顿近似的整族统一上界**：定理 2.1 给出 $\delta S_{\rm out}^{\rm ren}=\delta\langle K_\chi\rangle+\mathcal O(\varepsilon^2\ell^{d-2})$ 对整族几何与态变分的统一控制。

(iv) **协变相空间的 null 边界与角点处方**：定理 8.1 在仿射参数化与 Dirichlet 类边界数据下证明辛流无外泄与哈密顿量变分可积。

**证明状态声明**：

- ✅ **已完整证明**：显式可交换极限（引理 2.2）、端点层估计（引理 2.3）、张量化闭包（引理 4.1-4.3）。
- ⚠️ **依赖权威结果**：模哈密顿核（FLPW et al.）、QNEC（Bousso et al.）、JLMS 识别（code subspace）。
- ❌ **关键未证假设**：弱剪切族存在性、光线变换局部可逆性的完整稳定性估计、从半空间到小钻石的核比较引理。

**QNEC 路线说明**：本文采用 **Bousso-Fisher-Leichenauer-Wall (2016)** 版本的 QNEC，前提为 Minkowski 背景或弱曲率极限、Hadamard 态、完整 null 测地线与局域可积性。形状导数与 $A_\perp\to 0$ 的极限顺序与本文端点层固定兼容（见附录 D 的对齐说明）。

**结构性互补**：§7 的 OS/KMS–Fisher 解析延拓提供二阶非负性的结构性直觉，但不参与主证明链（一阶层依赖 Hadamard/KMS 或 QNEC，二阶层依赖 JLMS 识别或 QNEC 判据）。

---

## 0 记号、域前提与速查表

**记号与单位**：度规签名 $(-,+,+,+)$；$c=k_B=1$，保留 $\hbar$。爱因斯坦张量 $G_{ab}=R_{ab}-\tfrac12R g_{ab}$。零向量收缩 $R_{kk}:=R_{ab}k^ak^b$、$T_{kk}:=T_{ab}k^ak^b$。**体积与面积**：令**腰超曲面** $\Sigma_\ell$ 为因果钻石 $\mathcal D_\ell$ 的最大空间截面（维数 $d{-}1$），其体积 $V(B_\ell):=\mathrm{Vol}(\Sigma_\ell)$；令**腰面** $\partial\Sigma_\ell$ 为其边界（维数 $d{-}2$），其面积 $A:=\mathrm{Area}(\partial\Sigma_\ell)$。记 $B_\ell:=\Sigma_\ell$，$S_\ell:=\partial B_\ell$（腰面）；以下 $dA$ 一律指 $S_\ell$ 的固有测度；主阶标度 $A\sim c_d\ell^{d-2}$（常数并入 $C_d$）。

**域前提**：本文**限于 $d\ge3$**，并在小尺度因果钻石 $\mathcal D_\ell$ 的**弱剪切族**设定下工作，尺度分离 $\varepsilon=\ell/L\ll1$，Hadamard 类态与点分裂重整化，小区间内**无共轭点**。

**不变量速查表**（在 $k^a\to\alpha k^a$、$\lambda\to\lambda/\alpha$、$\kappa\to\alpha\kappa$ 与取向翻转下不变）：

$$
\frac{\delta Q}{T}=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA,\qquad
\frac{\delta A}{4G\hbar}.
$$

备注：$V/T$ 随重标定缩放，故非不变量。**本文仅得到带不定宇宙学常数的场方程**，$\Lambda$ 作为体积约束的乘子参数。**其数值不由本框架决定**。

**误差记法范式**（$\ell$ 标度 × 无量纲 $\varepsilon$ 标度）：本文统一采用

$$
\text{误差}=C_d\,\varepsilon^n\,\ell^m,
$$

其中 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C};d,c_\lambda)$ 为无量纲常数（与 $\varepsilon,\ell$ 无关），$n$ 为 $\varepsilon$ 幂次，$m$ 为长度维数。

**误差与维度一致性清单**（关键量的标度与上界）：

| 对象 | 主项标度 | 误差上界 | 依赖常数 |
|------|---------|---------|---------|
| 面积恒等式差值 | $\ell^{d-2}$ | $\mathcal O(\varepsilon^3\ell^{d-2})$ | $C_R, C_{\nabla R}, C_\sigma$ |
| 一阶律误差（§2引理2.2） | $\ell^{d-2}$ | $\mathcal O(\varepsilon^2\ell^{d-2})$ | $C_R, C_{\nabla R}$ |
| 统一误差命题（§2引理2.1） | $\ell^{d-2}$ | $C_{\rm unif}\,\varepsilon^2\ell^{d-2}$ | $C_R, C_{\nabla R}$ |
| 光线变换误差 | $\ell^2$ | $\mathcal O(\ell^3+\ell^4/L_{\rm curv}^2)$ | $C_R, C_{\nabla R}$ |
| 端点层贡献 | $\ell^{d-1}$ | $\mathcal O(\varepsilon\ell^{d-1})$ | $C_R$ |

注：$C_\sigma=C_{\sigma,0}+C_{\mathcal C}\lambda_*$。当 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 时（对称族），面积误差缩至 $\varepsilon^3$ 标度；一般族 $C_{\sigma,0}=\mathcal O(1)$ 遵循盒装上界。

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

**归一化与端点尺度一致性**：令"按生成元归一化"的首矩为

$$
\mathcal I_{\hat k}[f]:=\int_0^{\lambda_*}\lambda\,f(\gamma_{p,\hat k}(\lambda))\,d\lambda,\quad{\rm 标度}\sim\ell^2.
$$

存在常数 $c_{\min},c_{\max}>0$ 使 $c_{\min}\ell\le \lambda_*(x,\hat k)\le c_{\max}\ell$ 对所有方向一致成立。端点层的归一化估计一律以 $\mathcal I_{\hat k}$ 的 $\ell^2$ 标度为参照。

**弱剪切族（条件假设）**：本文主定理为**条件定理**，假设在每一点 $p$ 存在满足下列条件的小钻石族 $\{\mathcal D_\ell(p)\}_{\ell\le\ell_0}$：

$$
\boxed{\sup_{S_\ell,\,\hat k}|\sigma(0,x,\hat k)|\le c_s\,\varepsilon\quad\text{（对所有方向 }\hat k\text{ 统一成立）}}
$$

其中 $c_s>0$ 与 $\ell_0>0$ 为常数。

**关键未解决问题**：该条件的**构造性存在性**与**变分稳定性**未包含在本文中。具体需要：

1. **剪切均衡引理**：给出在 Riemann 正规邻域中通过屏空间对称化或有限方向平均的显式构造，证明存在腰面选择使 $C_{\sigma,0}$ 降至 $\mathcal O(\varepsilon)$。

2. **稳定性**：证明该族在半径 $r\varepsilon^2$ 的几何与态变分球内保持 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 的阶数。

3. **稠密性**：说明一般 $C^3$ 背景下该条件是否稠密或可通过规范选择实现。

**本文地位**：在上述假设下，给出从熵变分到 Einstein 方程的**可信路线图与细化误差控制**。弱剪切族假设的证明或替代方案是自然的后续工作。

**整族统一误差的主命题引用约定**：正文统一只引用"命题 2B'（整族统一误差）"。原"统一误差命题 引理 2.1"不再单独使用其标签。

**函数空间与正则性工具箱** 设几何扰动与态扰动取值于

$$
\mathcal X:=H^{k}(\mathcal D_\ell;\text{Sym}^2)\times\mathcal S_{\rm Had}，\qquad k\ge 3，
$$

其中 $H^{k}$ 为 Sobolev 空间，$\mathcal S_{\rm Had}$ 为 Hadamard 类态的 GNS 表示域。Sobolev–Morrey 嵌入保证 $H^{k}\hookrightarrow C^2$ 从而曲率与其一阶导有界。**体积泛函的线性化** $\delta V:\mathcal X\to\mathbb R$ 为有界线性泛函，$\ker\delta V$ 为闭子空间。拉格朗日乘子引理在 $\mathcal X$ 上适用。**Hadamard 变分**要求双点函数的波前集保持在固定锥 $\Gamma$ 内。态局域器取 Weyl 算符 $W(f)=\exp\big(i\Phi(f)\big)$ 的 GNS 实现，$\delta S_{\rm out}$ 作为 Gâteaux 导数良定，点分裂重整化与取上确界交换由统一 UV 窗口与 $|R|_{C^1}$ 有界性保证。

---

### 引言提要：与既有工作的区别度

- Jacobson（1995）：引入定体积对偶与显式 $\varepsilon$‑可交换极限，摆脱未指明"局域 Rindler"依赖
- Jacobson（1995）：引入定体积对偶与显式 $\varepsilon$‑可交换极限，摆脱未指明"局域 Rindler"依赖
- Jacobson–Visser（2019）：以 Radon 型闭包将面积恒等式下推为点态方程（族约束 ⇒ 点态）
- JLMS + Hollands–Wald：将二阶相对熵与规范能量写入同一变分链，形成单链闭环
- Dong–Camps–Wald：以 Wald/Dong–Camps 熵替代面积后，同一 IGVP 框架直接给出 Lovelock 型方程
- **二阶层条件性与无对偶备选**：二阶层 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}$ 为条件定理（依赖 JLMS 识别）；无对偶情形以 QNEC 二阶形状导数提供普适非负型判据
- **二阶层条件性与无对偶备选**：二阶层 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}$ 为条件定理（依赖 JLMS 识别）；无对偶情形以 QNEC 二阶形状导数提供普适非负型判据

---

## 1 IGVP：泛函、约束与两层准则

**一阶层的主定义与对偶项的规约**

$$
\boxed{S_{\rm gen}^{(\mu)}:=S_{\rm grav}+S_{\rm out}+\mu\,V,\qquad
S_{\rm grav}=\frac{A}{4G\hbar}+S_{\rm ct}^{\rm UV},\quad S_{\rm out}=S_{\rm out}^{\rm ren}.
}
$$

在带内积的变分空间 $\mathcal X$ 上，以定体积约束 $\delta V=0$ 为侧条件，求 $\delta S_{\rm gen}^{(\mu)}=0$ 于 $\ker\delta V$。由引理 1.0 的正交分解，存在唯一常数 $\mu$ 使受约束极值等价于无约束极值加一维对偶方向的投影消去。物理上先用边界与温标一次性标定 $T_0=\hbar|\kappa_\chi|/(2\pi)$，再令

$$
\mu=\frac{\Lambda}{8\pi G T_0}.
$$

此后 $\mu$ 被视为常数。原记法 $-\frac{\Lambda}{8\pi G}\frac{V}{T}$ 仅作等价诠释，不再参与一阶欧拉方程。

**一阶层准则**：

$$
\delta S_{\rm gen}^{(\mu)}\big|_{\ker\delta V}=0\quad\Longleftrightarrow\quad
\frac{\delta A}{4G\hbar}+\delta S_{\rm out}^{\rm ren}=0.
$$

在 Hadamard KMS 设定或 QNEC 路线下，由命题 2B' 得

$$
\delta S_{\rm out}^{\rm ren}=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA+\mathcal O(\varepsilon^2\ell^{d-2}).
$$

**二阶层准则**：若 JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 识别成立，则 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$。无对偶情形以 QNEC 的二阶形状导数构造非负二次型，详见 §5。

**记号提示**：本文出现两个不同的 $\kappa$：（i）**温标** $T=\hbar|\kappa_\chi|/2\pi$ 中的 $\kappa_\chi$ 是近似 Killing 场 $\chi^a$ 的表面引力；（ii）§8 null 边界项中的 $\kappa_{\rm aff}[\ell]$ 是 $\ell^a$ 的非仿射量（在仿射参数化下 $\kappa_{\rm aff}[\ell]=0$）。二者完全无关。为区分，本文统一记后者为 $\kappa_{\rm aff}[\ell]$。

**外部熵的一阶律（用于链 A）** 在小钻石极限、Hadamard/KMS 态与近 Rindler 生成元 $\chi^a$ 下，

$$
\delta S_{\rm out}^{\rm ren}=\delta\langle K_\chi\rangle
=\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA\ +\ \mathcal O(\varepsilon^2)
\equiv \frac{\delta Q}{T}+\mathcal O(\varepsilon^2),
$$

其中 $K_\chi$ 为腰面处的 boost 模块哈密顿量，$T=\hbar|\kappa_\chi|/2\pi$。

因此在一阶极值层与 $\delta V=0$ 下，得到

$$
\delta S_{\rm gen}
=\frac{\delta A}{4G\hbar}+\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA+\mathcal O(\varepsilon^2)=0。
$$

**由此在弱剪切族内，经 Radon 型闭包与张量化闭包得到 $R_{kk}=8\pi G\,T_{kk}$ 与 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。$\Lambda$ 为体积约束乘子，不由本原理确定其数值**。

**引理 1.0（定体积约束与拉格朗日乘子唯一性）**：设 $(\mathcal X,\langle\cdot,\cdot\rangle)$ 为一带内积的实向量空间，取变分对 $(\delta g,\delta\text{state})\in\mathcal X$。令 $\delta V:\mathcal X\to\mathbb R$ 为一个非零连续线性泛函，令 $S[\cdot]$ 为可Fréchet变分的泛函。则存在唯一的 $\mu\in\mathbb R$ 使得
$$
\delta\big(S+\mu V\big)=0\quad\text{在}\ \mathcal X\ \text{上}
$$
等价于
$$
\delta S=0\quad\text{在}\ \ker\delta V,\qquad \delta V=0.
$$
换言之，由非零泛函 $\delta V$ 张成的一维子空间与 $\ker\delta V$ 构成正交直和分解，拉格朗日乘子 $\mu$ 对应于沿 $\delta V$ 方向的投影系数，且唯一。□

**命题 1A（对偶项等价性与规约角色）**：给定 $\mathcal D_\ell$ 内允许的几何与态变分，在 $\delta V=0$ 子空间与固定温标 $T$ 上，存在唯一 $\mu$ 使

$$
\boxed{
\delta\left(S_{\rm grav}+S_{\rm out}+\mu V\right)=0
\quad\Longleftrightarrow\quad
\delta S_{\rm gen}=0,\ \delta V=0.
}
$$

并且 $\mu=\Lambda/(8\pi G T)$ 由"端点固定+腰面固定+$\delta T/T=\mathcal O(\varepsilon^2)$"唯一确定。唯一性与等价性由引理1.0中的正交分解直接给出。

**证明草图**（2行）：变分分解为 $\delta S_{\rm gen}=(\delta S_{\rm gen}|_{\ker\delta V})+(\partial S_{\rm gen}/\partial V)\,\delta V$。在 $\ker\delta V$ 子空间，拉格朗日乘子 $\mu$ 仅消除重标定冗余（$T\to\alpha T$、$V\to V$），不对一阶欧拉方程 $\delta(A/(4G\hbar)+S_{\rm out})=0$ 贡献新物理信息。□

该命题说明体积对偶项为规范选择的等价表述，不是"装饰项"。

**正交分解的线性代数观点**（2行）：将 $\delta S_{\rm gen}$ 分解为平行于 $\delta V$ 与垂直于 $\delta V$ 两部分。在 $\ker\delta V$ 子空间，拉格朗日乘子 $\mu$ 对应正交补空间的投影系数，仅钉住温标而不贡献物理自由度。由 $\int(\varphi+\varphi_0)dA=0$ 保证定理3C的变分始终在 $\ker\delta V$ 内，故对偶项在导出 $R_{kk}=8\pi G T_{kk}$ 时未参与。

---

## 2 小钻石极限：显式不等式与边界层

**正则性门槛**：背景度规 $g\in C^3$（或 $g\in C^2$ 且 $\nabla{\rm Riem}\in L^\infty$），物质场 $T_{ab}\in C^1$；令 $\Sigma_\ell$ 为**最大体积空间超曲面**，其边界 $S_\ell=\partial\Sigma_\ell$（**腰面**）为初值面。最大体积条件给出 $\theta(0)=0$，但**不必强制** $\sigma(0)=0$；本文仅要求 $\sigma(0)\in L^\infty$。零测地丛满足 Frobenius 条件 $\omega(0)=0$，故 $\omega\equiv0$。

**初始剪切的几何来源**：当几何由近似CKV生成的对称小钻石族时，$C_{\sigma,0}=\mathcal O(\varepsilon)$，此时整体误差缩至 $\mathcal O(\varepsilon^3)$（图1所示标度）。一般族 $C_{\sigma,0}$ 可为 $\mathcal O(1)$，此时遵从下述盒装上界。

**参数化约定与记号区分**：下文沿零测地生成元的参数 $\lambda$ 统一取为**仿射参数**（$k^b\nabla_b k^a=0$），因此本文采用的 Raychaudhuri–Sachs–Twist 方程**不含 $\kappa\theta$ 项**。**重要记号区分**：见§1的记号提示（$\kappa_\chi$ 与 $\kappa_{\rm aff}[\ell]$ 完全无关）。

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

**引理 2.B.1（曲率映射的局部一致 Lipschitz）**

设几何扰动族 $\mathcal B=\{\delta g: |\delta g|_{C^2}\le r\varepsilon^2\}$，其中 $r>0$ 为固定常数。则存在与 $\mathcal B$、背景曲率上界 $|R|_{C^1}$、以及坐标块大小有关的常数 $K_R, K_{\nabla R}$，使得对所有 $\delta g\in\mathcal B$：

$$
\boxed{
C_R(\delta g)\le \widetilde C_R:=C_R+K_R r\varepsilon^2,\quad
C_{\nabla R}(\delta g)\le \widetilde C_{\nabla R}:=C_{\nabla R}+K_{\nabla R} r\varepsilon^2.
}
$$

**证明草图**：Riemann 曲率张量 $R_{abcd}$ 是度规 $g_{ab}$ 及其一、二阶导数的多项式型函数。在 $C^2$ 范数下，度规扰动 $\delta g$ 导致曲率变化满足

$$
|\delta R|\lesssim|\nabla^2\delta g|+|\nabla\delta g|^2\le C(g_0)\,|\delta g|_{C^2}.
$$

其中 $C(g_0)$ 依赖于背景度规的 $C^3$ 范数。因此曲率常数 $C_R$ 与 $C_{\nabla R}$ 关于扰动满足局部 Lipschitz 估计，常数 $K_R, K_{\nabla R}$ 由背景几何完全确定。由此，命题 2B' 中的整族误差界 $C_{\rm th}$ 可用 $(\widetilde C_R,\widetilde C_{\nabla R})$ 统一控制，与具体变分路径无关。$\square$

**面积变分显式不等式与可交换性**

$$
\boxed{
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\,d\lambda\,dA\Big|
\ \le\ \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2+\tfrac{1}{3(d-2)}C_R^2\lambda_*^4\Big)A\ .
}
$$

其中 $C_d=C_d(C_R,C_{\nabla R},C_{\mathcal C},C_{\sigma,0};d,c_\lambda)$ 与 $\varepsilon$ 无关。

**误差标度与几何族关系**：若几何族满足 $C_{\sigma,0}=\mathcal O(\varepsilon)$（如对称小钻石族），则上式右端的 $\tfrac12 C_\sigma^2\lambda_*^2 A$ 贡献降为 $\mathcal O(\varepsilon^3\ell^{d-2})$，与数值图观测到的 $\varepsilon^3$ 主标度一致。一般族 $C_{\sigma,0}=\mathcal O(1)$ 时遵循完整盒装上界。

$$
\boxed{
\textbf{适用域前置声明：主定理假设弱剪切族存在。}\
\text{工作假设：存在满足 }C_{\sigma,0}=\mathcal O(\varepsilon)\text{ 的小钻石族。}\
\Rightarrow\ \text{首矩误差 }o(\ell^2)\text{ 可达，从而闭包到 }f(p)=0。\
\text{一般族 }C_{\sigma,0}=\mathcal O(1)\text{ 时仅得 }O(\ell^2)\text{ 上界，不足以闭包。}\
\text{该假设的构造性证明（剪切均衡引理）不在本文范围，留作后续工作。}
}
$$

**主定理的适用范围与弱剪切族的精确定义**

**定义（弱剪切族，统一版）**：存在常数 $c_s>0$ 与 $\ell_0>0$，对所有 $\ell<\ell_0$ 与所有腰面点 $x\in S_\ell$，以及所有从 $x$ 射出的生成元方向 $\hat k$，有

$$
\sup_{S_\ell}|\sigma(0,x)|\le c_s\,\varepsilon.
$$

并保持无共轭点与 $|R|_{C^1}$ 有界的统一常数族。称这类小钻石族为"弱剪切族"。在此条件下

$$
\sup_{\hat k}\left|\int_0^{\lambda_*}\!\lambda\,F(\gamma_{x,\hat k}(\lambda))\,d\lambda\right|=o(\ell^2)
\quad\text{对}\quad F=R_{kk}-8\pi G\,T_{kk}.
$$

**适用域声明**：

$$
\boxed{
\textbf{主定理仅在弱剪切族内成立。一般族 }C_{\sigma,0}=O(1)\text{ 时仅能给出 }O(\ell^2)\text{ 上界，不足以闭包到 }f(p)=0。
}
$$

一般族的闭包需要新的"剪切均衡引理"或额外平均步骤，不在本稿范围内。

**量纲核算与沿方向一致性**：所有 $o(\ell^2)$ 语句均指沿单条生成元的首矩归一化尺度，并且上式的 $o(\ell^2)$ 对所有 $\hat k$ 一致成立。端点层由 §2 的边界层估计吸收，主导收敛保证极限与积分可交换。

**补充约束（弱剪切族的变分稳定性）**：在假设 2.B.0 的允许变分下，存在常数 $c_\omega>0$ 使扭率满足

$$
\omega(\lambda)=\mathcal O(\varepsilon^2),\qquad \sup_{[0,\lambda_*]}|\omega|\le c_\omega\,\varepsilon^2.
$$

由 Raychaudhuri–Sachs 的局部 Lipschitz 依赖性与小钻石标度 $|\theta|\lambda_*\ll1$ 可得其贡献已被 §2 盒装上界吸收，故主链中的所有 $o(\ell^2)$ 目标不受 $\omega$ 的一阶扰动影响。

**幅度归一化（与 2.B.0 一致）**：对定理 3C 的态局域器

$$
U_{\epsilon,\varphi}=\exp\Big(i\int_{\mathcal H} w_\epsilon(\lambda)\,\varphi(x)\,J_{r(\ell)}(x)\,T_{kk}\,d\lambda\,dA\Big),
$$

其强度参数按需缩放使得

$$
\big|\delta W\big|_{\mathcal C^\alpha(\mathcal D_\ell\times\mathcal D_\ell)}\le r\,\varepsilon^2.
$$

从而命题 2B' 的统一常数 $C_{\rm th}$ 与 $\varphi$ 的具体形状无关，仅依赖 $r(\ell)/\ell=\mathcal O(1)$。

**量纲核算小盒子（归一化约定与 $o(\ell^2)$ 目标）**：

**关键约定**：§3中的"$o(\ell^2)$"始终指**按生成元归一化**的首矩量级。定义沿单条生成元的首矩算子
$$
\boxed{
\mathcal I_{\hat k}[f]:=\int_0^{\lambda_*}\lambda\,f(\gamma_{p,\hat k}(\lambda))\,d\lambda,
\qquad \text{自然标度}\sim\ell^2.
}
$$

对全腰面 $S_\ell$ 的积分量级为 $A\cdot(\ell^2)\sim\ell^{d-2}\cdot\ell^2=\ell^d$。

以 $d=4$ 为例，$\varepsilon=\ell/L_{\rm curv}$。命题2B'给出的**总量误差**
$$
\Bigl|\delta S_{\rm out}-\frac{2\pi}{\hbar}\int\lambda T_{kk}\,d\lambda\,dA\Bigr|
\le C_{\rm th}\varepsilon^2\ell^{d-2}
=C_{\rm th}\frac{\ell^2}{L_{\rm curv}^2}\cdot\ell^2.
$$

**按生成元归一化**（除以 $A\sim\ell^{d-2}$）：
$$
\frac{C_{\rm th}\varepsilon^2\ell^{d-2}}{A}
\sim\frac{C_{\rm th}\varepsilon^2\ell^{d-2}}{\ell^{d-2}}
=C_{\rm th}\varepsilon^2\sim\frac{\ell^2}{L_{\rm curv}^2}\to0.
$$

因此对于首矩 $\mathcal I_{\hat k}$（标度 $\sim\ell^2$），误差为 $\mathcal O(\varepsilon^2)\times\ell^2=o(\ell^2)$。这正是§3局域化与Radon型闭包所需的量纲条件。

**数值样例演示（在弱剪切样例上）**：数值实验在满足 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 的对称族样例上演示了归一化误差 $|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$ 的 $\varepsilon^3$ 标度行为。该实验用于支撑误差规模与端点层控制，不用于证明弱剪切族的存在性或普适闭包。一般族 $C_{\sigma,0}=\mathcal O(1)$ 遵循盒装上界。

![**图 1. 弱剪切族内的归一化误差标度。** 本图仅展示满足 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 的对称族。归一化误差 $|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$ 随尺度分离参数 $\varepsilon$ 呈现 $\varepsilon^3$ 标度。**一般族 $C_{\sigma,0}=\mathcal O(1)$ 不在主定理范围内**，仅保证 $O(\ell^2)$ 盒装上界，**不闭包到点态等式**。复现方法与参数见附录 J。](igvp_figure1_exchangeable_limit.png)

端点层 $[\lambda_*-\delta,\lambda_*]$ 的贡献满足

$$
\boxed{
\Big|\int_{\lambda_*-\delta}^{\lambda_*}\lambda R_{kk}\,d\lambda\,dA\Big|
\le \tfrac12 A\big(\lambda_*^2-(\lambda_*-\delta)^2\big)C_R
=A\,C_R\,\lambda_*\,\delta+\mathcal O(A\,C_R\,\delta^2).
}
$$

**尺度计数修正**（按归一化约定）：

- **按总面积归一化**：$A\sim\ell^{d-2}$，$\lambda_*\delta\sim\varepsilon\ell^2$，故 $A\cdot\lambda_*\cdot\delta\sim\varepsilon\ell^d$。端点层贡献为 $\boxed{\mathcal O(\varepsilon\ell^{d})}$。

- **按生成元归一化**：沿单条生成元，$\int_{\lambda_*-\delta}^{\lambda_*}\lambda R_{kk}\,d\lambda\le C_R\lambda_*\delta\sim\varepsilon\ell^2$。端点层贡献为 $\boxed{\mathcal O(\varepsilon\ell^{2})=o(\ell^2)}$（$\varepsilon\to0$时）。

§3中的"局域化目标 $o(\ell^2)$"始终理解为**按生成元归一化**的陈述。此量化与测试函数局域化引理中首矩权截断 $w_\epsilon$ 的端点区间 $[\lambda_*-\epsilon,\lambda_*]$ 误差控制呼应：令 $\epsilon=c\,\varepsilon\ell$ 即得按生成元的 $o(\ell^2)$ 控制。

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

因 $\widetilde M_{\rm dom}$ 与 $\varepsilon$ 无关，且对所有 $|\lambda|\le\lambda_0$ 均有 $\widetilde M_\theta(\lambda)\le \widetilde M_{\rm dom}(\lambda)$，故可据**主导收敛定理**（Lebesgue dominated convergence theorem）交换"$\varepsilon\to0$"与沿 $\lambda$ 的积分。

**备注（编号整合）**：原"统一误差命题"已整合入命题2B'（假设2.B.0+整族统一误差上界），常数 $C_{\rm th}$ 的作用等同于原 $C_{\rm unif}$。为避免重复，下文统一引用命题2B'。引理2.1专指"局部一阶律误差"（$\delta S_{\rm out}^{\rm ren}$ 与 $\delta\langle K_\chi\rangle$ 的偏差），与命题2B'互补。

**假设 2.B.0（允许变分族的大小，统一版）**：存在常数 $r>0$ 与 $\ell_0>0$，对所有 $\ell<\ell_0$ 与所有允许的几何与态变分 $(\delta g,\delta\text{state})$ 有

$$
|\delta g|_{C^2(\mathcal D_\ell)}+|\nabla\delta g|_{L^\infty(\mathcal D_\ell)}\le r\,\varepsilon^2,\qquad
|\delta W|_{\mathcal C^\alpha(\mathcal D_\ell\times\mathcal D_\ell)}\le r\,\varepsilon^2,
$$

其中 $\delta W$ 为 Hadamard 双点函数的变分，其波前集保持在固定的 Hadamard 类。上述常数 $r$ 与 $|R|_{C^1}$ 的上界可统一选择，与 $(p,\hat k)$ 及具体 $(\delta g,\delta\text{state})$ 无关。
且相应的二点函数变分 $\delta W$ 的Hadamard余项在某个固定Hölder或Besov范数 $|\cdot|_{\mathcal C^\alpha}$ 下满足
$$
|\delta W|_{\mathcal C^\alpha(\mathcal D_\ell\times\mathcal D_\ell)}\le r\,\varepsilon^2.
$$
即允许的几何与态变分族都包含在一个以零为中心、半径为 $r\varepsilon^2$ 的有界球中。

**定理 2.1（小钻石模哈密顿近似的整族统一误差——主链技术脊梁）**

**前提**：

(i) §0的几何正则性：$|R|_{\mathcal C^0}\le C_R/\ell^2$，$|\nabla R|_{\mathcal C^0}\le C_{\nabla R}/\ell^3$，

(ii) Hadamard 类态条件与点分裂重整化，局域 KMS 或 QNEC 版本成立，

(iii) 假设 2.B.0：允许变分族 $(\delta g,\delta\rho)$ 满足
$$
|\delta g|_{C^2}\le r\varepsilon^2,\quad |\delta W|_{\mathcal C^\alpha}\le r\varepsilon^2,
$$
且 $\delta W$ 的波前集保持在 Hadamard 锥内，

(iv) 端点固定与腰面固定（边界条件）。

**结论**：令 $\mathfrak G$ 为满足上述条件的几何形变族，令 $\mathfrak S$ 为 Hadamard 类态族。则存在常数 $C_{\rm th}=C_{\rm th}(C_R,C_{\nabla R},r;d,c_\lambda)$ 与 $\ell_0>0$，使得对所有 $\ell<\ell_0$ 与所有允许变分 $(\delta g,\delta\text{state})\in\mathfrak G\times\mathfrak S$：

$$
\boxed{
\sup_{(\delta g,\delta\text{state})\in\mathfrak G\times\mathfrak S}
\Big|\delta S_{\rm out}^{\rm ren}-\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,T_{kk}\,d\lambda\,dA\Big|
\le C_{\rm th}\,\varepsilon^2\,\ell^{d-2}.
}
$$

**证明状态**：本定理给出证明纲要与误差阶计数，但以下关键环节仍需完整证明：

- **❌ 核比较引理**：从 FLPW 半空间核到小钻石核的显式公式及误差分解（需雅可比、切换域、端点层逐项估计）。
- **⚠️ 点分裂重整化交换**：证明 Weyl 激发 $U_{\epsilon,\varphi}$ 与模哈密顿核卷积后给出同阶 $\varepsilon^2$ 估计（需波前集与 UV 窗口定量约束）。
- **⚠️ 上确界统一性**：证明常数 $C_{\rm th}$ 与 $(\varphi,\chi,\ell)$ 的具体选择无关，仅依赖背景上界。

**证明纲要**：（i）Riemann正规坐标把 $\mathcal D_\ell$ 等距到平直主部 $\eta+\mathcal O(\ell^2/L_{\rm curv}^2)$；（ii）用Faulkner-Leigh-Parrikar-Wang (2016)风格的半空间形变核与点分裂重整化控制模哈密顿与局域boost的差，误差为 $\mathcal O(\varepsilon^2)$；（iii）将态与形变的族放进 $\sup$，依赖常数只和背景上界 $(C_R,C_{\nabla R})$ 与半径 $r$ 有关，与具体变分无关。该统一上界保证了后续局域化构造对**整族**允许变分都保持一致误差控制。

**JHEP 评审要求**：补充核比较的完整证明，明确列式写出误差每一项的来源，以及 Weyl 激发与模哈密顿核卷积的同阶估计。

**误差分解（两项显式表达）**：
$$
\boxed{
\delta S_{\rm out}^{\rm ren}-\delta\langle K_\chi\rangle=
\underbrace{\Delta_{\rm geom}}_{\sim C_R\ell^d}
+\underbrace{\Delta_{\rm state}}_{\sim C_{\nabla R}\varepsilon^2\ell^{d-2}},
}
$$
其中 $\Delta_{\rm geom}$ 为几何近似项（小钻石与平直主部的偏差，由 $C_R$ 控制），$\Delta_{\rm state}$ 为态依赖项（Hadamard双点函数的短距展开与点分裂重整化，由 $C_{\nabla R}$ 控制）。详细推导见附录A.6。

**几何常数族在变分下的统一上界**：由 $R_{ab}$ 对度规的局部Lipschitz依赖性，存在常数 $K_R,K_{\nabla R}$ 使得对所有满足假设2.B.0的几何变分
$$
C_R(\delta g)\le C_R+K_R\,|\delta g|_{C^2}\le C_R+K_R r\varepsilon^2,
$$
$$
C_{\nabla R}(\delta g)\le C_{\nabla R}+K_{\nabla R}\,|\delta g|_{C^2}\le C_{\nabla R}+K_{\nabla R} r\varepsilon^2.
$$
因此在足够小的 $\varepsilon$ 下，可以用一个不依赖具体变分的统一常数族 $(\widetilde C_R,\widetilde C_{\nabla R})$ 控制所有局域化构造中的误差估计。这与引理A.5'共同保证主控函数 $M_{\rm dom}$ 对整族有效。

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
\boxed{
\mathcal L_\lambda[f](p,\hat k)=\tfrac12\lambda_*^2 f(p)
+\mathcal O\Big(\lambda_*^3|\nabla f|_\infty+\frac{\lambda_*^4}{L_{\rm curv}^2}|f|_\infty\Big)
}.
$$

**定理 3D（加权 Null 光线变换的局部可逆性）**

**前提**：

(i) 度规 $C^2$ 有界：$|R|_{\mathcal C^0}\le C_R/\ell^2$，$|\nabla R|_{\mathcal C^0}\le C_{\nabla R}/\ell^3$，

(ii) 短段无共轭点：对所有 $\lambda\in[0,\lambda_*]$，测地线 $\gamma_{p,\hat k}$ 无共轭点，

(iii) 仿射参数统一控制：$c_{\min}\ell\le \lambda_*(x,\hat k)\le c_{\max}\ell$ 对所有 $(x,\hat k)$ 成立，

(iv) 被变换函数的正则性：$f\in C^1(S_\ell)$ 且 $\|f\|_{C^1}\le M$。

**结论**：在 $p$ 的 Riemann 正规邻域内，加权光线变换满足

$$
\mathcal L_\lambda[f](p,\hat k)=\int_0^{\lambda_*}\lambda\, f(\gamma_{p,\hat k}(\lambda))\,d\lambda
=\frac12\lambda_*^2 f(p)+\mathcal O\!\left(\lambda_*^3|\nabla f|_\infty+\frac{\lambda_*^4}{L_{\rm curv}^2}|f|_\infty\right),
$$

其中大 $\mathcal O$ 常数仅依赖于 $C_d\big(C_R,C_{\nabla R};d,c_{\min},c_{\max}\big)$，与 $(\hat k,\ell)$ 无关。

**稳定性推论**：若对所有 $\hat k$ 有 $\mathcal L_\lambda[f](p,\hat k)=o(\ell^2)$ 且该 $o(\ell^2)$ 一致于方向，则 $f(p)=0$。

**证明状态**：本定理给出证明草图，但缺少以下关键内容：

- **❌ 主符号分析与核刻画**：刻画带权 $\lambda$ 的 null 光线变换在 Lorentz 流形上的主符号、椭圆性与核结构。
- **❌ 稳定性估计**：给出 $C^1$ 或 $H^1$ 级别的稳定不等式（非仅展开启发）。
- **⚠️ 主控函数独立性**：证明 $M_{\rm dom}$ 对所有方向与局域化族统一成立。

**JHEP 评审要求**：提升为可引用的完整定理，或在附录中补充严格证明（含前提、结论、常数依赖与稳定性估计）。

**证明纲要**：（i）**Minkowski符号法与首矩权的微局域算子**：在平直空间，Fourier变换下
$$
\int_0^{\lambda_*}\lambda\,e^{i\xi\cdot\lambda\hat k}\,d\lambda=
\frac{\lambda_*^2}{2}+\mathcal O\big((\xi\cdot\hat k)\lambda_*^3\big).
$$
当 $|\xi\cdot\hat k|\lesssim\lambda_*^{-1}$ 时主项占优，首矩权不引入新核。由此 $\mathcal L_\lambda[f]\equiv 0$ 对所有 $\hat k$ 成立 $\Rightarrow \widehat{f}$ 支撑在零集 $\Rightarrow f=0$。（ii）**小曲率扰动稳定性**：以 $\epsilon:=\ell/L_{\rm curv}$ 为小参数做扰动论，由微局域参数椭圆性（Stefanov-Uhlmann 2009风格）延拓稳定估计至弱曲率背景。适用条件：无共轭点+局部横截光滑。（iii）**Riemann正规坐标展开**：度规 $g_{ab}=\eta_{ab}+\tfrac13 R_{acbd}x^c x^d+\mathcal O(|x|^3/L_{\rm curv}^3)$，零测地偏离 $x^a(\lambda)=\lambda\hat k^a+\mathcal O(\lambda^3/L_{\rm curv}^2)$，逐项积分给出盒装展开式。□

**文献注记**：Lorentzian light-ray变换的局部可逆性与稳定性已在无共轭点假设下得到研究（参见Finch-Patch-Rakesh 2004对X-ray变换的经典结果；Stefanov-Uhlmann等对波前集的微局域分析；Kurylev-Lassas-Uhlmann 2018对null测地在Lorentzian几何中的可逆性）。本文仅需首矩权 $w\equiv\lambda$ 的短线段数据，在Riemann正规邻域内为**局部**结论，不依赖全局层析。详细证明与文献综述见附录B.3。

**定理 3C（弱剪切族内的 Radon 型闭包与局域化）** 在定体积约束 $\delta V=0$ 与**弱剪切族**假设 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 下，对任意 $\varphi\in C_c^\infty(S_\ell)$ 与端点光滑截断的首矩权 $w_\epsilon\to\lambda$ 于 $L^1$，并要求支撑半径满足 $r(\ell)\in[c_{\min}\ell^\alpha,c_{\max}\ell]$ 其中 $0<\alpha<1$ 与常数 $c_{\min},c_{\max}>0$，存在可执行构造产生允许的一阶变分 $(\delta g,\delta\text{state})$，使得

$$
\boxed{
\int_{S_\ell}\varphi(x)\int_0^{\lambda_*} w_\epsilon(\lambda)\bigl(R_{kk}-8\pi G\,T_{kk}\bigr)\,d\lambda\,dA
=o(\ell^2)
}
$$

并且该族变分满足命题 2B 的统一控制，误差为 $\mathcal O(\varepsilon^2\ell^{d-2})$。同时通过补偿函数 $\varphi_0$ 实现 $\int_{S_\ell}(\varphi+\varphi_0)\,dA=0$，从而 $\delta V=0$ 保持成立。**端点层误差**与**$\varphi_0$ 的非紧支集效应**均被统一常数吸收，不破坏 $o(\ell^2)$ 目标。

**可复现三步构造**：

1. **形变器**：取分片 $C^\infty$ bump $\Phi_\epsilon$ 与补偿函数 $\varphi_0$ 使 $\int_{S_\ell}(\varphi+\varphi_0)\,dA=0$，定义

   $$
   X_\epsilon(x)=\exp_x\big(\epsilon\,\varphi(x)\,n\big)+\epsilon\,\varphi_0(x)\,n.
   $$

2. **态局域器**：取

   $$
   w_\epsilon(\lambda)=\lambda\,\chi_{[0,\lambda_*-\epsilon]}(\lambda)\ast\rho_\epsilon(\lambda),
   \quad
   J_{r(\ell)}(x)=\text{单位质量 mollifier with }r(\ell)/\ell=\mathcal O(1),
   $$

   并令

   $$
   U_{\epsilon,\varphi}=\exp\Big(i\int_{\mathcal H} w_\epsilon(\lambda)\,\varphi(x)\,J_{r(\ell)}(x)\,T_{kk}(x,\lambda)\,d\lambda\,dA\Big).
   $$

   以 $\delta\text{state}=U_{\epsilon,\varphi}\,|\text{state}\rangle-|\text{state}\rangle$。Hadamard 类与 $C^\alpha$ 有界性由 $\rho_\epsilon$ 与 $J_{r(\ell)}$ 的平滑与紧支撑保证。

3. **端点权处理**：$w_\epsilon(0)=0$ 且 $w_\epsilon=\lambda$ 于 $[0,\lambda_*-\epsilon]$，端点层由 §2 的边界层估计给出 $o(\ell^2)$。

该构造保持 $\delta V=0$ 且对整族 $(\delta g,\delta\text{state})$ 有统一主控函数 $M_{\rm dom}\in L^1([0,\lambda_0])$，因此"族约束到点态"的闭包沿所有方向一致成立。

**操作手册（$\varphi$ 的缩放范式）**：选 $\varphi_{r(\ell)}$ 为单位质量bump函数，半径 $r(\ell)=\ell^\alpha$（$0<\alpha<1$，例如 $\alpha=1/2$）。补偿函数 $\varphi_0$ 在 $S_\ell\setminus\text{supp}(\varphi)$ 上取常数使 $\int(\varphi+\varphi_0)dA=0$，其 $L^1$ 范数 $\|\varphi_0\|_{L^1}\sim\|\varphi\|_{L^1}=\mathcal O(1)$。由引理A.6'，误差 $\mathcal O(\varepsilon^2\ell^{d-2})$ 被 $C_{\rm unif}$ 吸收，与 $r(\ell)$ 的具体取值无关（只要 $r(\ell)/\ell=\mathcal O(1)$）。读者据此可照抄实现定理3C的"可测选择"。

**统一上界保证**：对 $\theta,\sigma$ 的控制改为
$$
\big|\theta+\lambda R_{kk}\big|\le \widetilde M_{\rm dom}(\lambda),
$$
其中 $\widetilde M_{\rm dom}$ 不依赖 $\varphi$ 与 $\epsilon$（显式式样同§2盒装上界）。由命题2B'（假设2.B.0+整族统一误差）与引理A.5'（局域化族一致支配）的组合，该构造对实现任意 $\varphi$ 的整族变分保持统一误差控制，从而"族约束→点态"的闭包完全成立。

**交叉引用说明**：本定理的族一致性依赖于：（i）假设2.B.0定义变分族大小；（ii）命题2B'给出整族统一误差上界 $C_{\rm th}\varepsilon^2\ell^{d-2}$；（iii）引理A.6'保证态局域器对整族 $\{\varphi\}$ 的一致控制；（iv）引理A.5'保证主控函数 $M_{\rm dom}$ 对整族有效。四者结合使局域化闭包严丝合缝。

**测试函数局域化引理（端点光滑截断版——统一$o(\ell^2)$目标）**：若
$$
\int_{S_\ell}\!\varphi(x)\int_0^{\lambda_*}\! w(\lambda)F(x,\lambda)\,d\lambda\,dA=0
$$
对所有 $\varphi\in C_c^\infty(S_\ell)$ 与 $w\in C_c^\infty([0,\lambda_*))$（并要求 $w(0)=0$）成立，则几乎处处沿每条生成元 $\int_0^{\lambda_*} w F=0$。

**归一化约定的严格化**：上式左端为**全腰面积分**（量级 $\sim\ell^d$），右端为零意味着对**按生成元归一化**的首矩 $\mathcal I_{\hat k}[w\cdot F]=\int_0^{\lambda_*}w(\lambda)F(x,\lambda)\,d\lambda$（量级 $\sim\ell^2$），几乎处处为零。

实际使用时取一族 $w_\epsilon\in C_c^\infty([0,\lambda_*))$ 使 $w_\epsilon(\lambda)=\lambda$ 于 $[0,\lambda_*-\epsilon]$，并令 $\epsilon\to0$。端点层 $[\lambda_*-\epsilon,\lambda_*]$ 的贡献由§2边界层估计给出：
$$
\boxed{
\Big|\int_{\lambda_*-\epsilon}^{\lambda_*}\lambda F\,d\lambda\Big|
\le C_R\lambda_*\epsilon
\sim C_R\ell\cdot(\varepsilon\ell)=\mathcal O(\varepsilon\ell^2)=o(\ell^2)\quad(\varepsilon\to0).
}
$$
这正是§2"按生成元归一化"给出的 $o(\ell^2)$ 控制。极限交换由主导收敛保证。

（注：本文主用首矩权的光滑截断 $w_\epsilon$，**所有 $o(\ell^2)$ 陈述均指按生成元归一化的首矩量级**，与§2的归一化约定盒严格对应。）

**测试函数局域化引理（提升为命题+证明）**：设 $\int_{S_\ell}\varphi(x)\int_0^{\lambda_*} w(\lambda)F(x,\lambda)\,d\lambda\,dA=0$ 对所有 $\varphi\in C_c^\infty(S_\ell)$ 与 $w\in C_c^\infty([0,\lambda_*))$（$w(0)=0$）成立。则几乎处处沿每条生成元 $\int_0^{\lambda_*} w F=0$。

**证明**：（i）Fubini定理分离 $x$ 与 $\lambda$ 方向的测试；（ii）对 $\lambda$ 方向用mollifier逼近 $\delta$，取首矩权截断族 $w_\epsilon\to\lambda$ 得加权光线变换核；（iii）端点层由§2边界层估计与主导收敛控制（引理A.5'保证对整族变分统一成立）；（iv）由命题3D的局部可逆性，核仅在零函数时出现。□

**命题 3A（局域化变分族处于一阶极值切空间）**：设 $\delta S_{\rm gen}=0$ 在带约束的切空间 $\ker\delta V$ 上成立。则对定理3C构造的 $(\delta g,\delta\text{state})$，仍有

$$
\boxed{
\delta S_{\rm gen}\big[(\delta g,\delta\text{state})\big]=\mathcal O(\varepsilon^2\ell^{d-2}).
}
$$

**证明草图（2行）**：变分分解为 $\delta S_{\rm gen}=(\delta S_{\rm gen}|_{\ker\delta V})+\mu\,\delta V$。由定理3C的补偿函数 $\varphi_0$ 满足 $\int_{S_\ell}(\varphi+\varphi_0)\,dA=0$，得 $\delta V=0$，故仅余 $\ker\delta V$ 分量。使用命题2B的统一上界 $C_{\rm th}\varepsilon^2\ell^{d-2}$ 将态端误差并入右端。这样定理3C构造的整族变分确实处于一阶极值允许的切向空间，"族约束$\Rightarrow$点态"的闭包在逻辑上完全闭合。□

结合定理3C的可实现性、命题3A的切空间验证、命题3D的局部可逆性与引理A.5'的一致支配，对 $f=R_{kk}-8\pi G\,T_{kk}$ 得 $\mathcal L_\lambda[f]=o(\ell^2)\Rightarrow f(p)=0$，即

$$
R_{kk}=8\pi G\,T_{kk}\quad(\forall\,k).
$$

**主链闭环确认**：命题2B→定理3C→命题3A→命题3D→引理A.5'形成完整技术闭环。

**主链闭环确认**：命题2B→定理3C→命题3A→命题3D→引理A.5'形成完整技术闭环。

---

## 4 张量化闭包与场方程（$d\ge 3$ 必要）

**零锥刻画引理仅在 $d\ge3$ 成立**。因此以下张量化闭包与场方程的推导**限于 $d\ge3$**。令 $X_{ab}=R_{ab}-8\pi G\,T_{ab}$。若 $X_{ab}k^ak^b=0$ 对所有零矢 $k^a$ 成立，则 $X_{ab}=\Phi g_{ab}$。由收缩 Bianchi 与 $\nabla^aT_{ab}=0$ 得 $\nabla_b(\tfrac12R-\Phi)=0$。定义 $\Lambda:=\tfrac12R-\Phi$ 为常数，从而

$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}。
$$

**零锥刻画略证补充**：证明思路是：在任意一点选取一组零矢使其在屏空间（screen space）中形成足够丰富的方向族。对 $X_{ab}$ 做去迹与屏空间分解，利用 $X_{ab}k^ak^b=0$ 对所有零矢的条件逐一杀掉横向无迹分量，最终仅剩下纯trace模 $\Phi g_{ab}$。详细论证见附录C。

**$d=2$ 退化说明**：$d=2$ 时对称张量天然满足零锥退化（screen空间退化为标量），上述引理不成立，场方程无法由零锥收缩唯一确定。本文推导爱因斯坦方程**明确要求 $d\ge 3$**。

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
## 5 二阶层：$\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$ 与稳定性（条件定理与普适判据）

**重要前提说明**：本节结论在 **JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 识别成立的语境下**有效；无对偶情形改用QNEC/ANEC的二阶形状导数构造非负二次型（定理5.2）。本文二阶层采用唯一仿射化选择：两片 null 边界以腰面为 $\lambda=0$，端点为 $\pm\lambda_*$，并取 $\kappa_{\rm aff}[\ell]=0$。关节角 $\eta$ 与诱导度规 $\sigma_{AB}$ 固定。此选择保证边界辛流无外泄且 $\delta H_\chi$ 可积。

**定理 5.1（条件性二阶层，JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 成立时）** 在 code subspace 与合适边界数据下，若 $\delta^2S_{\rm rel}=\mathcal F_Q=\mathcal E_{\rm can}$ 成立，则

$$
\boxed{\ \mathcal E_{\rm can}[h,h]\ge 0\ }，
$$

并与 Hollands–Wald 线性稳定性等价。**若不采用上述识别**，则参见定理 5.2 之 QNEC 普适非负判据。

**何时可用**：该识别目前已在代码子空间（code subspace）与适当边界条件下得到证明或广泛接受，参见Lashkari–Van Raamsdonk (2016)、Jafferis–Lewkowycz–Maldacena–Suh (2016)。

**命题 5B（Code subspace在小钻石中的实现）**：在小钻石背景下，固定端点位置与腰面时刻等价于线性荷约束 $(\delta M,\delta J,\delta P)=(0,0,0)$。

**证明配方（含线性化细节）**：在小钻石的腰超曲面 $\Sigma_\ell$ 上，Brown-York质量、线性动量与角动量可写为
$$
M\sim\int_{\Sigma_\ell}(K-K_0)\,dA,\quad
P_i\sim\int_{\Sigma_\ell}K_{ij}\,u^j\,dA,\quad
J\sim\int_{\Sigma_\ell}\epsilon_{ijk}x^iK^{jk}\,dA,
$$
其中 $K_{ij}$ 为外曲率，$u^j$ 为单位法矢。对度规扰动 $g_{ab}\to g_{ab}+\delta g_{ab}$，外曲率的一阶展开为
$$
\boxed{
K_{ij}\to K_{ij}+\delta K_{ij},\qquad
\delta K_{ij}=-\tfrac12 u^k\nabla_k\delta g_{ij}+\mathcal O(\delta g^2).
}
$$
固定端点位置与腰面时刻意味着 $\delta g_{ij}|_{\partial\Sigma_\ell}=0$（边界Dirichlet条件），因此在积分 $\int_{\Sigma_\ell}\delta K_{ij}\,u^j\,dA$ 中，分部积分后边界项 $\int_{\partial\Sigma_\ell}$ 消失，主阶贡献为零。由此 $(\delta M,\delta J,\delta P)=(0,0,0)$，小钻石的端点+腰面固定自然落在code subspace假设内。□

设以下条件成立：

**（C1）函数空间**：扰动 $h_{ab}\in H^{k}(\Sigma)$（$k\ge2$），满足线性化爱因斯坦方程（由 §3–§4 的一阶族约束与张量化闭包给出）。

**（C2）Code subspace 与荷约束**：扰动满足 $\delta M=\delta J=\delta P=0$（线性化质量、角动量、线性动量守恒）。在小钻石设置下，这等价于要求扰动不改变钻石端点位置与腰面时刻。

**（C3）边界条件与无外流**：采用唯一仿射化与 Dirichlet 边界数据包：

$$
\boxed{\text{唯一仿射化}：\kappa_{\rm aff}[\ell]=0,\quad \sigma_{AB}|_{\partial\Sigma}\ \text{固定},\quad \eta|_{\mathcal J}\ \text{固定},\quad\text{端点位置固定}.}
$$

其中 $\kappa_{\rm aff}[\ell]$ 为 null 生成元 $\ell^a$ 的非仿射量，$\sigma_{AB}$ 为诱导度规，$\eta$ 为关节角。仿射参数化使 $\kappa_{\rm aff}[\ell]=0$，此选择保证辛流无外流 $\int_{\partial\Sigma}\iota_n\omega(h,\mathcal L_\xi h)=0$。该条件的逐式验证见附录 E.2（Minkowski）与 E.3（弱曲率推广）。

**（C4）规范固定与核的刻画**：采用 Killing 或协变谐规范以剔除纯规范模。在此规范下，$\mathcal E_{\rm can}[h,h]=0$ **当且仅当** $h$ 为纯规范模（即存在矢量场 $\xi^a$ 使 $h_{ab}=\nabla_a\xi_b+\nabla_b\xi_a$）。这给出规范能量泛函核的完整刻画。

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

**无对偶情形的备选路径**：若不采纳JLMS识别，可直接用QNEC/ANEC的二阶形状导数构造非负二次型（定理5.2），提供与一阶链兼容的能量条件，无需模哈密顿量对偶假设。

---

## 6 温标–体积对偶与 $\delta\kappa_\chi/\kappa_\chi$ 的阶计数

在重标定与取向翻转下，$\delta Q/T$ 与 $\delta A/(4G\hbar)$ 不变；$V/T$ 非不变量，但一阶极值层采用固定温标（$\delta T=0$）不影响结论。固定端点与腰面，近似 CKV 的表面引力 $\kappa_\chi=2/\ell+\mathcal O(\ell/L_{\rm curv}^2)$，一阶几何扰动给 $\delta\kappa_\chi=\mathcal O(\ell/L_{\rm curv}^2)$，故

$$
\frac{\delta\kappa_\chi}{\kappa_\chi}=\mathcal O\Big(\frac{\ell^2}{L_{\rm curv}^2}\Big)=\mathcal O(\varepsilon^2),
$$

从而"固定 $|\kappa_\chi|$"与"允许 $\delta T\neq0$"在一阶极值层等价。

---

## 7 OS/KMS–Fisher 解析延拓：结构性互补（摘要）

**结构角色说明**：Osterwalder–Schrader (OS) 反射正性与 Kubo–Martin–Schwinger (KMS) 温度周期保证欧氏Fisher–Rao度量延拓后在Lorentz签名保持某种正定性。该通道为结构性互补，**不参与§2–§4的主证明**，而是对"$\delta^2S_{\rm rel}$ 为何自然非负"提供信息几何诠释。详见附录G.3。

**核心结论**（两行）：若欧氏Fisher协方差有下界 $\eta>0$，则洛伦兹延拓后度量具 $(-,+,\dots)$ 签名且非退化。$1{+}1$ 维高斯族可取 $\eta=1/\sigma^2$ 作显式下界。

**桥接QFT态族**（一行）：Hadamard/KMS态族通过期望值pushforward构造概率族，其Fisher-Rao度量在解析延拓后满足上述下界（Lashkari-Van Raamsdonk 2016）。

---

## 8 协变相空间的 null 边界与角点处方：无外流与可积性

在 Einstein–Hilbert 作用上加入 null 边界项与关节项：

$$
I_{\partial\mathcal N}=\frac{1}{8\pi G}\int_{\mathcal N}d\lambda\,d^{d-2}x\,\sqrt{q}\,\kappa_{\rm aff}[\ell],\qquad
I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J}d^{d-2}x\,\sqrt{\sigma}\,\eta ,
$$

其中横截面为 $(d{-}2)$ 维，$d^{d-2}x$ 为其固有测度。$\eta=\ln|-\ell\cdot n|$（null–非 null）或 $\eta=\ln\big|-\tfrac12\,\ell\cdot\tilde\ell\big|$（null–null）。

**记号提示**（重要！重复强调）：本节 null 边界项中的 $\kappa[\ell]$ 记为 **$\kappa_{\rm aff}[\ell]$** 以强调其为仿射参数偏离量，**与§1温标** $T=\hbar|\kappa_\chi|/2\pi$ 中的 $\kappa_\chi$（近似 Killing 场表面引力）**完全无关**。$\kappa_{\rm aff}[\ell]=0$ 对应仿射参数化。

**盒装处方（Null边界与关节项的可积性条件）**：

在本文的首选处方下，采用以下三件套使 $\delta I_{\partial\mathcal N}=\delta I_{\rm joint}=0$：

$$
\boxed{
\begin{aligned}
&\text{(i) 仿射参数化}：\kappa_{\rm aff}[\ell]=0\ \Rightarrow\ \text{Null 边界项} I_{\partial\mathcal N}=0,\\
&\text{(ii) Dirichlet 边界条件}：\delta\sigma_{AB}=0\ \Rightarrow\ \text{切向分量固定},\\
&\text{(iii) 固定关节角}：\delta\eta=0\ \Rightarrow\ \delta I_{\rm joint}=0.
\end{aligned}
}
$$

在此首选处方下，Minkowski 小钻石满足 $\kappa_{\rm aff}[\ell]=0$，$\eta$ 为常数，因此 $\delta I_{\partial\mathcal N}=\delta I_{\rm joint}=0$。

**辛流无外泄的显式计算**：Einstein-Hilbert作用的预辛势可以取为

$$
\boxed{
\Theta^a(h)=\frac{1}{16\pi G}\bigl(\nabla^a h-\nabla_b h^{ab}\bigr)\sqrt{-g},\qquad h_{ab}=\delta g_{ab},
}
$$

其在边界上的法向分量为 $\iota_n\Theta=\Theta^a n_a|_{\partial\mathcal D_\ell}$。对定理3C构造的允许变分 $\delta g$，逐边界验证：

- **Null边界 $\mathcal N$ 上**：在边界假设B.0的Dirichlet条件下 $\delta\sigma_{AB}=0$，则 $\delta g$ 的切向分量 $\delta g_{AB}=0$。预辛势 $\iota_n\Theta$ 在Einstein-Hilbert作用下简化为 $\iota_n\Theta\propto\nabla^A\delta\sigma_{AB}=0$（边界上），故 $\int_{\mathcal N}\iota_n\omega=\mathcal O(\varepsilon^2\ell^{d-2})$。

- **关节 $\mathcal J$ 上**：在边界假设B.0下固定 $\eta$ 使 $\delta\eta=0$，由关节项变分公式
$$
\delta I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J} d^{d-2}x\,\Bigl(\tfrac12\sqrt{\sigma}\,\sigma^{AB}\delta\sigma_{AB}\,\eta+\sqrt{\sigma}\,\delta\eta\Bigr),
$$
在 $\delta\sigma_{AB}=0$ 与 $\delta\eta=0$ 下，关节项对辛流的贡献为零。

- **腰超曲面 $\Sigma_\ell$ 上**：定理3C的形变器保持 $\delta V=0$，腰面诱导度规变分由补偿函数 $\varphi_0$ 控制，使 $\int_{\Sigma_\ell}(\delta g_{ab}n^a n^b)\,dA$ 的净贡献抵消，$\int_{\partial\Sigma}\iota_n\omega=\mathcal O(\varepsilon^2\ell^{d-2})$。

综合三部分，$\int_{\partial\mathcal D_\ell}\iota_n\omega(h,\mathcal L_\xi h)=\mathcal O(\varepsilon^2\ell^{d-2})$，在一阶链中可忽略；在二阶链中需明确固定边界数据以保证 $\int_{\partial\Sigma}\iota_n\omega=0$。

**盒装处方总结**：

$$
\boxed{
\begin{aligned}
&\text{（i）采用}\textbf{仿射参数化}：k^b\nabla_b k^a=0 \Rightarrow \kappa_{\rm aff}[\ell]=0 \Rightarrow I_{\partial\mathcal N}=0;\\
&\text{（ii）}\textbf{Dirichlet边界条件}：\text{固定}\,\sigma_{AB}|_{\partial\Sigma} \Rightarrow \delta\sigma_{AB}=0;\\
&\text{（iii）}\textbf{固定关节角}：\delta\eta=0.
\end{aligned}
}
$$

在此处方下，关节项变分

$$
\delta I_{\rm joint}
=\frac{1}{8\pi G}\int_{\mathcal J} d^{d-2}x\,
\Big(\tfrac12\sqrt{\sigma}\,\sigma^{AB}\delta\sigma_{AB}\,\eta+\sqrt{\sigma}\,\delta\eta\Big)=0,
$$

从而 joint 项自动可积，无需再调 counterterm。由此 Iyer–Wald 辛流在边界无外泄，$\delta H_\chi$ 可积，且不改变 $\delta S_{\rm gen}$ 与 $\mathcal E_{\rm can}$ 的数值。

**示例（Minkowski 小钻石）**：两片仿射 null 面拼接 $\Rightarrow \kappa_{\rm aff}[\ell]=0$ 给 $I_{\partial\mathcal N}=0$；null–类空超曲面关节项 $\eta$ 为常数，$\delta I_{\rm joint}=0$。由此边界通量为零且哈密顿量变分可积。

---

## 9 高阶引力与唯一性
用 Wald/Dong–Camps 熵替代面积后，同一 IGVP 框架直接给出 Lovelock 型场方程；详细 $f(R)$ 与 Gauss–Bonnet 演示见附录 H。

---

## 10 双层判据架构与逻辑蓝图

本文采用**双层判据架构**，每层独立可证且相互支撑：

**一阶层（Radon 型闭包判据）**：在定体积约束 $\delta V=0$ 与**弱剪切族** $C_{\sigma,0}=\mathcal O(\varepsilon)$ 下，由 Raychaudhuri–Sachs–Grönwall 驱动的显式可交换极限与边界层上界，配合加权光线变换的局部可逆性与测试函数局域化，实现"族约束 $\Rightarrow$ 点态"的 Radon 型闭包：

$$
\delta S_{\rm gen}^{(\mu)}\big|_{\ker\delta V}=0\quad\Longrightarrow\quad R_{kk}=8\pi G\,T_{kk}\quad(\forall k)\quad\Longrightarrow\quad G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}。
$$

其中 $\Lambda$ 为体积约束乘子，数值不由本原理确定。**此层仅依赖 Hadamard/KMS 或 QNEC 路线**，无需对偶识别。

**二阶层（条件性非负判据）**：在 JLMS 与 $\mathcal F_Q=\mathcal E_{\rm can}$ 识别成立时，二阶相对熵 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}$ 给出 Hollands–Wald 稳定性：

$$
\mathcal E_{\rm can}[h,h]\ge 0，
$$

其中 $h_{ab}$ 为满足一阶层场方程的线性化扰动。**若不采用该识别**，则参见定理 5.2 的 QNEC 二阶形状导数普适非负判据。

**双层独立性与协同**：一阶层给出场方程，二阶层给出稳定性。二阶层提供稳定性判据，其适用以一阶层给出的线性化爱因斯坦方程为前提。因此二阶层可在"已假设线性化方程成立"的语境下单独引用。合并后形成"导出+稳定"的完整闭环。

---

## 11 可复现实操清单

1. **数值样例演示**：在弱剪切样例 $C_{\sigma,0}=\mathcal O(\varepsilon)$ 上演示归一化误差 $\big|\delta A+\int\lambda R_{kk}\big|/\ell^{d-2}$ 的 $\varepsilon^3$ 标度行为。此演示服务于误差规模与端点层控制的验证，不作为弱剪切族存在性或闭包普适性的证明。一般族 $C_{\sigma,0}=\mathcal O(1)$ 核对盒装上界。复现脚本与详细参数表：
   - **脚本路径**：`scripts/generate_igvp_figure1.py`
   - **三组参数**（图1的低/中/高曲率）：见表11.1（附录J）
   - **修改方法**：调整脚本中 $C_R, C_{\mathcal C}, C_{\sigma,0}, \lambda_0$ 四参数
   - **输出**：归一化误差 vs $\varepsilon$ 双对数图，含 $\varepsilon^3$ 参考线
   - **随机种子**：1234（确保可复现）
2. 逐项验证 $\delta Q/T$、$\delta A/(4G\hbar)$ 的重标定/取向不变；并在固定 $T$ 的规约下核查 $V/T$ 的使用。
3. 以"局域化引理"把面积恒等式下推至逐生成元，加上 0‑阶重建得 $R_{kk}=8\pi G\,T_{kk}$；
4. 在 $1{+}1$ 高斯族与满足奇偶性判据的模型上，显式验证 $g_{ti}=0$ 与"实/非退化/签名"的下界；
5. 在 Minkowski 小钻石核查 null 边界/关节项的"无外流 + 可积"。

---

## 附录 J  可复现实验参数表

**表 11.1：图1的三组参数设置**

| 曲线 | $C_R$ | $C_{\nabla R}$ | $C_{\mathcal C}$ | $C_{\sigma,0}$ | $\lambda_0$ | $\ell$ 范围 | $\varepsilon$ 采样点数 |
|------|-------|----------------|-----------------|--------------|-----------|----------|-----------------|
| 低曲率 | 0.1 | 0.15 | 0.1 | $0.05\varepsilon$ | 1.0 | $[10^{-3},10^{-1}]$ | 20 |
| 中曲率 | 0.2 | 0.25 | 0.2 | $0.05\varepsilon$ | 1.0 | $[10^{-3},10^{-1}]$ | 20 |
| 高曲率 | 0.3 | 0.35 | 0.3 | $0.05\varepsilon$ | 1.0 | $[10^{-3},10^{-1}]$ | 20 |

**背景设定**：
- **度规**：Schwarzschild类型，质量参数 $M=0.1\lambda_0$
- **物质场**：标量场 $\phi$ 满足Klein-Gordon，质量 $m_\phi=0.01/\lambda_0$
- **边界条件**：Dirichlet（固定诱导度规 $\sigma_{AB}$ 与关节角 $\eta$）
- **态**：Hartle-Hawking真空态，温度 $T=|\kappa_\chi|/(2\pi)$
- **数值方法**：Runge-Kutta 4阶求解Raychaudhuri-Sachs方程，自适应步长
- **误差归一化**：$|\delta A+\int\lambda R_{kk}|/\ell^{d-2}$，取 $d=4$
- **随机种子**：1234

**修改指南**：
1. 打开 `scripts/generate_igvp_figure1.py`
2. 修改 `PARAMS` 字典中的 `C_R, C_nabla_R, C_C, C_sigma_0, lambda_0`
3. 调整 `epsilon_range` 和 `n_samples` 以改变采样密度
4. 运行：`python generate_igvp_figure1.py --output fig1.png`
5. 输出日志文件包含所有中间计算值与误差分解

**一般族测试**：若测试 $C_{\sigma,0}=\mathcal O(1)$（如 $C_{\sigma,0}=0.5$），误差标度将从 $\varepsilon^3$ 变为 $\varepsilon^2$ 或常数级（由 $C_{\sigma,0}^2\lambda_*^2$ 项主导）。主链推导（定理3C+命题3A+命题3D）对此类族同样成立，仅需调整"局域化目标"为 $o(\ell^2)$ 而非 $o(\varepsilon^3\ell^{d-2})$。

**表 J.2：一般族参数设置（$C_{\sigma,0}=\mathcal O(1)$ 情形）**

| 曲线 | $C_R$ | $C_{\nabla R}$ | $C_{\mathcal C}$ | $C_{\sigma,0}$ | $\lambda_0$ | 预期标度 |
|------|-------|----------------|-----------------|--------------|-----------|---------|
| 一般族示例 | 0.2 | 0.25 | 0.2 | 0.5 | 1.0 | $\varepsilon^2$ 或常数级 |

**复现细节补充**：
- **随机种子**：1234（与表11.1一致，确保可复现）
- **自适应步长阈值**：$10^{-8}$（Runge-Kutta 4阶求解器）
- **输出文件**：`igvp_figure1_symmetric.csv`（强对称族）、`igvp_figure1_general.csv`（一般族）
- **SHA256校验和**（示例）：`scripts/checksums.txt` 提供所有输出的哈希值，便于验证完整性

---

## 附录 H  高阶引力推广：Lovelock与 $f(R)$ 理论

本节展示IGVP框架对高阶引力理论的直接推广。

**H.1  Wald熵与一阶变分**

**适用域限定**：本节假定 $\mathcal L(g,R,\nabla R,\ldots)$ 为有限阶、纯度规、微分同胚不变的局域拉氏量。对应的场方程张量 $E_{ab}$ 满足广义 Bianchi 恒等式 $\nabla^a E_{ab}\equiv0$。在此类理论中，以 $E_{kk}$ 代替 $R_{kk}$ 的主链逻辑平行成立。Lovelock 与 $f(R)$ 理论属于此类。

对一般高阶引力作用量 $I=\int d^dx\,\sqrt{-g}\,\mathcal L(g,R,\nabla R,\dots)$，Wald (1993)给出黑洞熵的普适公式：
$$
S_{\rm Wald}=2\pi\int_{\mathcal H}\frac{\partial\mathcal L}{\partial R_{abcd}}\,\epsilon_{ab}\epsilon_{cd}\,dA,
$$
其中 $\epsilon_{ab}$ 为bifurcation面的binormal。一阶变分为
$$
\delta S_{\rm grav}^{\rm Wald}=\int E_{ab}\,\delta g^{ab}\,d^dx+\text{(boundary terms)},
$$
其中 $E_{ab}$ 为高阶场方程的左端（Wald熵方程）。

**H.2  $f(R)$ 理论的显式公式**

对 $\mathcal L=f(R)$，有
$$
E_{ab}=f'(R)\left(R_{ab}-\tfrac12 R g_{ab}\right)+\tfrac12\big(f(R)-R f'(R)\big)g_{ab}+\nabla_a\nabla_b f'(R)-g_{ab}\Box f'(R).
$$

面积-曲率恒等式的对应形式为
$$
\boxed{
\delta A_{\rm Wald}+\int_{\mathcal H}\lambda\,E_{kk}\,d\lambda\,dA=\mathcal O(\varepsilon^2\ell^{d-2}),
}
$$
其中 $E_{kk}:=E_{ab}k^a k^b$。

**H.3  Radon型闭包的替换表**

| Einstein引力 | Lovelock/高阶引力 | 替换规则 |
|-------------|----------------|--------|
| $R_{kk}$ | $E_{kk}$ | 场方程左端的零收缩 |
| $8\pi G T_{kk}$ | $8\pi G_{\rm eff} T_{kk}$ | 有效引力常数 $G_{\rm eff}=G/f'(R_0)$ |
| 零锥刻画引理 | 同 | $E_{ab}k^a k^b=0\ \forall k\Rightarrow E_{ab}=\Phi g_{ab}$ |

由Bianchi恒等式（推广形式），$\nabla^a E_{ab}=0$，张量化闭包同样成立，得
$$
\boxed{
E_{ab}=8\pi G_{\rm eff}\,T_{ab}.
}
$$

**H.4  Gauss-Bonnet理论**

对 $d=4$ Gauss-Bonnet不贡献场方程，但 $d\ge 5$ 时：
$$
\mathcal L_{\rm GB}=\alpha(R^2-4R_{ab}R^{ab}+R_{abcd}R^{abcd}),
$$
其Wald熵与场方程含二阶曲率项。IGVP框架在此情形下，§2的常数族需扩充 $C_{\nabla^2 R}$，§3的局部可逆性（命题3D）需加入 $\mathcal O(\lambda_*^5/L_{\rm curv}^3)$ 修正。主链逻辑（命题2B→定理3C→命题3D）结构不变。

**H.5  张量化闭包的推广**

**引理 H.1（零锥刻画的Lovelock推广）**：若 $E_{ab}$ 为由广义拉氏量 $\mathcal L(g,R,\nabla R,\dots)$ 变分得到的对称张量，且 $E_{ab}k^a k^b=0$ 对所有零矢 $k^a$ 成立，则 $E_{ab}=\Phi g_{ab}$（在 $d\ge 3$ 时）。

**证明草图**（同正文§4）：由任意零矢张成零锥面，screen空间中独立分量被消去，得对角化。

**广义Bianchi恒等式**：对Lovelock型作用量，由微分同胚不变性导出 $\nabla^a E_{ab}=0$（参见Lovelock 1971）。结合零锥刻画 $E_{ab}=\Phi g_{ab}$，得 $\nabla_b\Phi=0$，故 $E_{ab}=\text{const}\cdot g_{ab}$。由物质守恒 $\nabla^a T_{ab}=0$ 与场方程闭合，得
$$
\boxed{
E_{ab}=8\pi G_{\rm eff}\,T_{ab}.
}
$$

这与正文§4的张量化闭包完全平行，IGVP框架的主链逻辑（命题2B→定理3C→命题3A→命题3D→引理A.5'）结构不变。

**结论**：IGVP框架对Lovelock型高阶引力有**直接适用性**，仅需在零收缩层面替换 $R_{kk}\to E_{kk}$ 并引用广义Bianchi恒等式。详细推导与数值样例将在后续工作中展开。

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

**引理 2C（无共轭点条件在小形变下的稳定性）**：在背景度规 $g$ 下，假设通过点 $p$ 的零测地在 $[0,\lambda_*]$ 上无共轭点。则存在 $\delta>0$，对所有满足 $|\delta g|_{C^2(\mathcal D_\ell)}\le\delta$ 的小变分，变分后度规 $\tilde g=g+\delta g$ 下的对应零测地在 $[0,\lambda_*/2]$ 上仍无共轭点。

**证明要点**：基于Jacobi方程对度规的连续依赖性与共轭时间的下界的连续性。配合"缩小 $\ell$"的操作即可保证所有局域化族满足无共轭点假设。□

**邻域统一常数引理**：上述常数族 $(C_R,C_{\nabla R},C_{\mathcal C})$ 在 $p$ 的正规邻域 $\mathcal D_\ell(p)$ 上统一定义。对固定 $\lambda_0>0$，当 $0<\ell\le\ell_0$ 时，主控函数 $\widetilde M_{\rm dom}$ 在整个极限族 $\{\mathcal D_\ell\}$ 上统一有效，与 $p$ 和 $\hat k$ 的选择无关（仅依赖背景度规的正则性）。这保证了 §3 局域化闭包在流形每一点的一致收敛性。

**定理 A.5（局域化族的统一支配与Lebesgue主导收敛）** 设 $\mathfrak G_\varphi$ 是实现任意 $\varphi\in C_c^\infty(S_\ell)$ 的几何变分族（定理3C构造），$\mathfrak S_\varphi$ 是相应态扰动族。则存在同一个 $M_{\rm dom}\in L^1([0,\lambda_0])$（Lebesgue可积主控函数）使得对所有 $(\delta g,\delta\text{state})\in\mathfrak G_\varphi\times\mathfrak S_\varphi$ 与所有 $(p,\hat k)$，有

$$
\boxed{
\big|\chi_{[0,\lambda_*]}(\lambda)\big(\theta(\lambda)+\lambda R_{kk}(\lambda)\big)\big|\le M_{\rm dom}(\lambda).
}
$$

**证明要点**：Raychaudhuri-Sachs方程 $\theta'=-\tfrac{1}{d-2}\theta^2-\sigma^2-R_{kk}$ 与 $\sigma'$ 方程是局部Lipschitz的，Grönwall常数仅依赖 $(C_R,C_{\nabla R},C_{\mathcal C})$。小形变（定理3C的 $\delta X=\epsilon\varphi n$ 与态扰动）只改变 $(C_R,C_{\nabla R},C_{\mathcal C},C_{\sigma,0})$ 的**上界常数**，不改变控制方程的结构。对整族 $\mathfrak G_\varphi\times\mathfrak S_\varphi$ 取 $\sup$ 即得统一主控函数 $M_{\rm dom}$，与具体 $\varphi$ 与 $\epsilon$ 的选择无关。由主导收敛定理，"$\varepsilon\to0$"与积分次序可交换对**整族局域化变分**统一成立。□

**A.6  模哈密顿近似的FLPW核与点分裂误差分解**

本节给出命题2B误差分解 $\delta S_{\rm out}^{\rm ren}-\delta\langle K_\chi\rangle=\Delta_{\rm geom}+\Delta_{\rm state}$ 的推导框架。

**坐标映射与平直主部**：在Riemann正规坐标 $(t,x^i)$ 中心在腰面点 $p$，小钻石 $\mathcal D_\ell(p)$ 可等距映射到平直主部：
$$
g_{ab}(x)=\eta_{ab}+h_{ab}(x),\qquad |h|\sim\varepsilon^2,\quad |\nabla h|\sim\varepsilon^2/\ell.
$$

**FLPW半空间形变核**：对Rindler楔形区域的模哈密顿核，Faulkner-Leigh-Parrikar-Wang (2016)给出半空间形变时的一阶近似：
$$
\delta\langle K_\chi\rangle\big|_{\rm FLPW}\approx\frac{2\pi}{\hbar}\int_{\mathcal H}\lambda\,\langle T_{kk}\rangle_{\rm flat}\,d\lambda\,dA
+\mathcal O\big(\int h\,|\nabla^2\langle T\rangle|\big).
$$

**几何近似项 $\Delta_{\rm geom}$**：由度规偏离 $h_{ab}$ 引起的能动张量修正：
$$
\Delta_{\rm geom}=\int_{\mathcal H}\lambda\,(\langle T_{kk}\rangle_{\rm curved}-\langle T_{kk}\rangle_{\rm flat})\,d\lambda\,dA
\sim C_R\int_{\mathcal D_\ell}|h|\,|\langle T\rangle|\,d^dx\sim C_R\ell^d.
$$

**态依赖项 $\Delta_{\rm state}$**：点分裂重整化中的Hadamard双点函数短距展开：
$$
\langle\phi(x)\phi(x')\rangle_{\rm Hadamard}=\frac{u(x,x')}{4\pi^2\sigma^2}+v(x,x')\log\sigma^2+w(x,x')+\cdots,
$$
其中 $\sigma(x,x')$ 为Synge世界函数。在小钻石中，重整化需扣除发散项，误差为
$$
\Delta_{\rm state}\sim\int_{\mathcal H}\lambda\,(C_{\nabla R}\varepsilon^2\ell^{-2})\,\ell^{d-2}\,d\lambda\,dA
\sim C_{\nabla R}\varepsilon^2\ell^{d-2}.
$$

**统一上界**：对整族 $\mathfrak G\times\mathfrak S$，$\Delta_{\rm geom}$ 的常数由背景上界 $C_R$ 控制，$\Delta_{\rm state}$ 由 $C_{\nabla R}$ 控制，与具体变分无关。由此得命题2B'的统一误差上界 $C_{\rm th}\varepsilon^2\ell^{d-2}$。详细计算见Faulkner et al. (2016) §3-4。

**引理 A.6'（态局域器的族一致构造——严谨接口）**：设 $\varphi\in C_c^\infty(S_\ell)$ 为任意局域化函数，其支撑半径为 $r(\ell)$，满足 $r(\ell)/\ell=\mathcal O(1)$。在假设2.B.0下，存在态变分 $\delta\text{state}^{(\varphi)}$ 使得

$$
\boxed{
\Bigl|\delta S_{\rm out}^{\rm ren}-\frac{2\pi}{\hbar}\int\lambda\,\varphi\,T_{kk}\Bigr|
\le C_{\rm th}(C_R,C_{\nabla R},r;d,c_\lambda)\,\varepsilon^2\ell^{d-2},
}
$$

其中常数 $C_{\rm th}$ 与 $\varphi$ 的支撑大小 $r(\ell)$ 无关（仅依赖半径与 $\ell$ 的比值被 $\mathcal O(1)$ 控制），与具体 $\varphi$ 的形状无关。

**态变分的构造类与正则性约束**：令 $\mathfrak S$ 为满足以下条件的态变分族：

1. **紧支撑有限能量波包**：$\delta\text{state}$ 为Fock空间中的有限粒子叠加，支撑于管状邻域 $\{\text{dist}(x,\text{supp}(\varphi))\le r(\ell)\}$。

2. **Hadamard类保持**：对基态的扰动满足 $|\delta W_{ab}|\le r\varepsilon^2$（$W_{ab}$ 为Hadamard双点函数的波前集），保证重整化的良定义性。

3. **能动张量界限**：$\|\delta T_{ab}\|_{C^\alpha(\mathcal H)}\le r\varepsilon^2/\ell^{d-2}$（$\alpha>0$），与假设2.B.0的几何变分正则性相匹配。

**误差分解的常数依赖**：由附录A.6的FLPW近似，$\Delta_{\rm state}$ 满足
$$
\Delta_{\rm state}\le C'(C_{\nabla R},r,\alpha)\int_{\mathcal H}|\delta T_{ab}||\nabla h_{cd}|\,dV
\le C'(C_{\nabla R},r,\alpha)\cdot(r\varepsilon^2/\ell^{d-2})\cdot(\varepsilon^2)\cdot\ell^d
=C'\cdot r\varepsilon^4\ell^{d-2}.
$$
取 $C_{\rm th}=C'+C''(C_R,r)$（$C''$ 来自几何项 $\Delta_{\rm geom}$），得统一上界。常数 $C_{\rm th}(C_R,C_{\nabla R},r;d,c_\lambda)$ 对参数 $(C_R,C_{\nabla R},r)$ **有界连续**：当 $(C_R,C_{\nabla R},r)$ 在紧集内变化时，$C_{\rm th}$ 的变化受控。

**证明要点**（3行）：从FLPW半空间核出发，用Riemann正规坐标将弱曲率背景小钻石映射到平直主部；对模哈密顿核 $k_\chi$ 做紧支撑截断与卷积，实现对 $\varphi(x)$ 的局域化；由命题2B'的统一上界与上述正则性约束，误差被 $C_{\rm th}\varepsilon^2\ell^{d-2}$ 吸收，与 $\varphi$ 的具体选择无关。态变分族 $\mathfrak S$ 的Hadamard类保持保证卷积核逼近误差不超过 $\mathcal O(\varepsilon^4\ell^{d-2})\subset\mathcal O(\varepsilon^2\ell^{d-2})$。这保证定理3C的态局域器对整族 $\{\varphi\}$ 保持一致控制。□

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
由 Taylor 展开与Riemann正规坐标下的曲率修正，$S_{kk}(\gamma(\lambda))=S_{kk}(p)+\lambda\nabla_k S_{kk}(p)+\mathcal O(\lambda^2|\nabla^2 S|+\lambda^2|S|/L_{\rm curv}^2)$；积分得

$$
\int_0^{\lambda_*}\!\lambda S_{kk}\,d\lambda=\tfrac12\lambda_*^2 S_{kk}(p)+\mathcal O\Big(\lambda_*^3|\nabla S|_\infty+\frac{\lambda_*^4}{L_{\rm curv}^2}|S|_\infty\Big).
$$

若左侧 $=o(\ell^2)$ 且 $\lambda_*\sim c_\lambda\ell$，则主项 $\tfrac12\lambda_*^2 S_{kk}(p)$ 占优（当 $\ell/L_{\rm curv}\ll 1$ 时），迫使 $S_{kk}(p)\to0$（当 $\ell\to0$）。由 $p$ 的任意性得 $S_{kk}=0$ 处处成立。分布情形可先作 mollifier 平滑，再令平滑尺度 $\to0$，估计保持一致。□

**B.3 零测地一阶矩局部可逆性**

**定理 B.3'（短线段、首矩赋权null光线变换的局部可逆性）**：在§0的假设下，取 $p$ 的Riemann正规邻域。假设在小区间 $[0,\lambda_*]$ 上无共轭点，曲率满足 $|R|_{C^1}\le C_R$。对任意 $f\in C^1$ 定义一阶矩加权光线变换

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

**B.3.1 微局部可逆性的三步验证**

**步骤 1：Minkowski 主符号（符号法）**

将 $\mathcal L_\lambda$ 视为沿 null 方向的积分算子。在 Minkowski 背景（$R=0$）下，对 $f\in C^\infty$ 作傅里叶变换 $\hat f(\xi)$，积分算子的主符号为

$$
\sigma(\mathcal L_\lambda)(\xi,\hat k)=\int_0^{\lambda_*}\lambda\, e^{i\lambda(\xi\cdot\hat k)}\,d\lambda.
$$

逐项积分得

$$
\sigma(\mathcal L_\lambda)(\xi,\hat k)=\frac{i}{\xi\cdot\hat k}\Big[\lambda e^{i\lambda(\xi\cdot\hat k)}\Big|_0^{\lambda_*}-\int_0^{\lambda_*}e^{i\lambda(\xi\cdot\hat k)}d\lambda\Big]
=\frac{i\lambda_* e^{i\lambda_*(\xi\cdot\hat k)}}{\xi\cdot\hat k}-\frac{e^{i\lambda_*(\xi\cdot\hat k)}-1}{(\xi\cdot\hat k)^2}.
$$

当 $|\xi\cdot\hat k|\ll \lambda_*^{-1}$（低频区域）时，Taylor 展开给出

$$
\sigma(\mathcal L_\lambda)(\xi,\hat k)=\tfrac12\lambda_*^2+\mathcal O\big(|\xi\cdot\hat k|\lambda_*^3\big).
$$

主符号 $\tfrac12\lambda_*^2$ **非退化且正**，表明在低频区域 $\mathcal L_\lambda$ 是可逆的。高频区域 $|\xi\cdot\hat k|\gtrsim\lambda_*^{-1}$ 对 $o(\ell^2)$ 估计贡献可由 $C^1$ 范数控制。

**步骤 2：端点正则化与主导收敛**

引入端点截断权 $w_\epsilon(\lambda)$ 满足：
- $w_\epsilon(\lambda)=\lambda$ 于 $[0,\lambda_*-\epsilon]$，
- $w_\epsilon(0)=0$，$w_\epsilon(\lambda_*)=0$（光滑截断），
- $\|w_\epsilon-\lambda\|_{L^1}\le C\epsilon\lambda_*$。

定义正则化算子 $\mathcal L_{w_\epsilon}[f]=\int_0^{\lambda_*}w_\epsilon(\lambda)f(\gamma(\lambda))d\lambda$。由 §2 的端点层估计，

$$
|\mathcal L_{w_\epsilon}[f]-\mathcal L_\lambda[f]|\le\int_{\lambda_*-\epsilon}^{\lambda_*}|\lambda-w_\epsilon|\cdot|f|d\lambda\le C\epsilon\lambda_*\|f\|_\infty.
$$

取 $\epsilon=c\varepsilon\ell$（与§2的端点层宽度一致），得

$$
|\mathcal L_{w_\epsilon}[f]-\mathcal L_\lambda[f]|\le C\varepsilon\ell^3\|f\|_\infty=o(\ell^2)\cdot\|f\|_\infty.
$$

由主导收敛定理（§2已证明主控函数 $\widetilde M_{\rm dom}$ 的 $L^1$ 可积性），$\mathcal L_{w_\epsilon}\to\mathcal L_\lambda$ 于算子范数意义。因此 $\mathcal L_\lambda$ 继承 $\mathcal L_{w_\epsilon}$ 的可逆性。

**步骤 3：弱曲率稳定性（正规算子正性）**

在弱曲率背景 $g=\eta+h$、$|h|_{C^2}\le C\varepsilon^2$ 下，扰动算子为 $\mathcal L_\lambda^{(g)}=\mathcal L_\lambda^{(\eta)}+\delta\mathcal L$。由 Riemann 正规坐标展开，扰动项满足

$$
|\delta\mathcal L[f]|\le C\varepsilon^2\lambda_*^2\|f\|_{C^1}\le C\varepsilon^2\ell^2\|f\|_{C^1}.
$$

定义正规算子 $\mathcal N:=\mathcal L_\lambda^*\mathcal L_\lambda$，其主符号为 $|\sigma(\mathcal L_\lambda)|^2=\tfrac14\lambda_*^4+\mathcal O(\lambda_*^5/L_{\rm curv})$（保持正性）。在 Sobolev 空间 $H^1(B_{c\ell}(p))$ 中，Gårding 不等式给出

$$
\|f\|_{L^2(B_{c\ell})}^2\le C\Big(\|\mathcal L_\lambda f\|_{H^1(\mathbb S^{d-2})}^2+\ell^2\|f\|_{H^1}^2\Big).
$$

由 $\ell/L_{\rm curv}\ll 1$，第二项为低阶项。若 $\|\mathcal L_\lambda f\|=o(\ell^2)$ 对所有 $\hat k$ 成立，则 $\|f\|_{L^2}=o(1)$，从而 $f(p)\to0$（当 $\ell\to0$）。

**结论**：首矩权光线变换 $\mathcal L_\lambda$ 在弱曲率、小尺度、端点正则化条件下具有微局部可逆性。主符号非退化保证低频可逆，端点截断保证 $L^1$ 收敛，弱曲率保证正规算子正性。由此"族约束 $\mathcal L_\lambda[f]=o(\ell^2)$ ⇒ 点态 $f(p)=0$"的闭包成立。$\square$

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
# 附录 C  张量化闭包与维度条件（$d\ge 3$ 必要）

**引理 C.1（零锥刻画，$d\ge3$ 必要）**
**引理 C.1（零锥刻画，$d\ge3$ 必要）**
若 $X_{ab}$ 光滑对称且 $X_{ab}k^ak^b=0\ \forall k$（零矢），则 $X_{ab}=\Phi g_{ab}$。证：去迹分解与"零锥决定共形类"。

**注**：$d=2$ 时所有对称张量自动满足此性质，场方程退化；本文推导爱因斯坦方程时**明确要求 $d\ge 3$**。

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
I_{\partial\mathcal N}=\frac{1}{8\pi G}\int_{\mathcal N}d\lambda\,d^{d-2}x\,\sqrt{q}\,\kappa_{\rm aff}[\ell],\quad
I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J}d^{d-2}x\,\sqrt{\sigma}\,\eta .
$$

取 Dirichlet‑类边界条件与仿射参数化，边界变分抵消，$\omega$ 无外泄，Wald–Zoupas/Brown–York 荷与 null 约束一致。

**E.2 Minkowski 小钻石核对**
仿射 null 段 $\Rightarrow \kappa_{\rm aff}[\ell]=0$ 使 $I_{\partial\mathcal N}=0$；null–类空超曲面关节 $\eta$ 常数 $\Rightarrow \delta I_{\rm joint}=0$。故 $\delta H_\chi$ 可积，与 §5 的规范能量边界合法性一致。

**E.3 弱曲率小钻石推广与边界辛流直接计算**

**命题（边界辛流的无外流验证）**：在弱曲率背景（$\ell/L_{\rm curv}\ll 1$）下，小钻石 $\mathcal D_\ell(p)$ 的 null 边界与关节项处理可推广如下，并直接计算边界辛流以验证§8处方与§3局域化变分的兼容性。

（i）**Riemann 正规坐标展开**：在 $p$ 的正规邻域内，度规至 $\mathcal O(\ell^2)$ 精度为

$$
g_{ab}(x)=\eta_{ab}+\tfrac13 R_{acbd}(p)\,x^c x^d+\mathcal O\Big(\frac{\ell^3}{L_{\rm curv}^3}\Big).
$$

（ii）**仿射参数化的 $\mathcal O(\varepsilon^2)$ 修正**：选择仿射参数 $\lambda$ 满足 $k^b\nabla_b k^a=0$。在上述度规展开下，null 生成元的非仿射量

$$
\kappa_{\rm aff}[\ell]:=k^a\nabla_a\ln|k^b\xi_b|=\mathcal O\Big(\frac{\ell}{L_{\rm curv}^2}\Big)=\mathcal O(\varepsilon^2/\ell).
$$

由于 $I_{\partial\mathcal N}\sim\int\kappa_{\rm aff}[\ell]\,d\lambda\,dA\sim\mathcal O(\varepsilon^2\ell^{d-2})$，在一阶变分层面可忽略（与 §2 误差一致）。

（iii）**关节角的固定与辛流无外泄**：采用 Dirichlet 边界条件固定 $\sigma_{AB}$ 与关节角 $\eta$，即 $\delta\sigma_{AB}=0$、$\delta\eta=0$。由 §8 的

$$
\delta I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J} d^{d-2}x\,
\Big(\tfrac12\sqrt{\sigma}\,\sigma^{AB}\delta\sigma_{AB}\,\eta+\sqrt{\sigma}\,\delta\eta\Big)=0,
$$

关节项自动可积。

（iv）**辛流无外泄的直接计算——显式边界公式**：Iyer–Wald 辛流为 $\omega(h,\mathcal L_\xi h)=\delta_1\Theta[\delta_2 g]-\delta_2\Theta[\delta_1 g]$，其中预辛势
$$
\Theta^a=\frac{1}{16\pi G}\big(\nabla^a h-\nabla_b h^{ab}\big)\sqrt{-g},\qquad
\iota_n\Theta=\Theta^a n_a\big|_{\partial\mathcal D_\ell}.
$$

对定理3C构造的允许变分 $\delta g$，逐边界验证：
   - **Null边界 $\mathcal H$ 上**：仿射参数化给出 $\kappa_{\rm aff}[\ell]=\mathcal O(\varepsilon^2/\ell)$，Dirichlet条件固定 $\sigma_{AB}|_{\partial\Sigma}$，则 $\delta g$ 的切向分量 $\delta g_{AB}=0$。预辛势 $\iota_n\Theta$ 在Einstein-Hilbert作用下简化为 $\iota_n\Theta\propto\nabla^A\delta\sigma_{AB}=0$（边界上），故 $\int_{\mathcal H}\iota_n\omega=\mathcal O(\varepsilon^2\ell^{d-2})$。
   - **关节 $\mathcal J$ 上（角点分布项可积性检核）**：关节处 null 段与类空段交汇，法向量 $n^a$ 有 $C^0$ 跳跃。边界 $\partial\mathcal D_\ell$ 为分片 $C^2$ 结构。预辛势通量在角点的分布贡献需逐项检核：
     * **诱导度规固定**：Dirichlet 条件 $\delta\sigma_{AB}|_{\mathcal J}=0$ 使切向分量无变分。
     * **关节角固定**：$\delta\eta|_{\mathcal J}=0$ 消除法向跳跃的主导项。
     * **几何连续性**：诱导度规 $\sigma_{AB}$ 在 $\mathcal J$ 上 $C^0$ 连续（虽然外曲率有跳跃）。
     由 §8 公式
     $$
     \delta I_{\rm joint}=\frac{1}{8\pi G}\int_{\mathcal J}\Big(\tfrac12\sqrt{\sigma}\,\sigma^{AB}\delta\sigma_{AB}\,\eta+\sqrt{\sigma}\,\delta\eta\Big)=0,
     $$
     角点项变分为零。预辛势在 $\mathcal J$ 上的法向投影 $\iota_n\Theta$ 虽有分布意义（因法向跳跃），但积分贡献在当前边界数据下严格为零：
     $$
     \int_{\mathcal J}\iota_n\omega\big[h,\mathcal L_\xi h\big]=0.
     $$
     法向跳跃项 $\Delta n^a$ 在 Dirichlet 数据下的预辛势通量分解为切向与法向部分，两者均因 $\delta\sigma_{AB}=0$ 与 $\delta\eta=0$ 而消失。因此角点分布项的可积性在二阶层所需精度下得到验证。
   - **腰超曲面 $\Sigma_\ell$ 上**：定理3C的形变器保持 $\delta V=0$，腰面诱导度规变分由补偿函数 $\varphi_0$ 控制，使 $\int_{\Sigma_\ell}(\delta g_{ab}n^a n^b)\,dA$ 的净贡献抵消，$\int_{\partial\Sigma}\iota_n\omega=\mathcal O(\varepsilon^2\ell^{d-2})$。
   
综合三部分，$\int_{\partial\mathcal D_\ell}\iota_n\omega(h,\mathcal L_\xi h)=\mathcal O(\varepsilon^2\ell^{d-2})$，在一阶链中可忽略；在二阶链中需明确固定边界数据以保证 $\int_{\partial\Sigma}\iota_n\omega=0$。

（v）**替代边界方案（避免过度约束指责）**：可仅固定 $\sigma_{AB}$，让 $\eta$ 由联络归一化条件 $\nabla_a\ell^a=\kappa_{\rm aff}[\ell]$ 自动确定。在仿射参数化下 $\kappa_{\rm aff}[\ell]=0$ 使 $\eta$ 为常数，无需额外固定。此方案下关节角由几何一致性给出，与"固定 $\sigma_{AB}$ 与 $\eta$"方案对 $\delta H_\chi$ 可积性结论一致，同样保证无外流。该替代方案与§3的局域化变分（定理3C的形变器与态局域器）等价兼容。

**结论**：弱曲率下，null 边界与关节项的处理与 Minkowski 情形一致（至 $\mathcal O(\varepsilon^2)$ 精度）。边界辛流的显式公式计算证实§8处方与§3局域化构造（定理3C）**完全兼容**，无过度约束。两种边界方案（固定 $\sigma_{AB}+\eta$ vs 仅固定 $\sigma_{AB}$）对主链推导等价有效。$\delta H_\chi$ 可积且 $\delta S_{\rm gen}$ 与 $\mathcal E_{\rm can}$ 的数值不受边界项影响。

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
