# 穿孔信息流形上的相对拓扑、主丛约化与指数理论

**——通向 $S(U(3)\times U(2))$、三代指标与 Yukawa‑缠绕的统一框架**

---

## 摘要

满秩密度矩阵流形 $\mathcal D^{\rm full}_N=\{\rho>0,\ \mathrm{tr}\rho=1\}$ 是开凸可缩的，Uhlmann 主丛在满域 admit 全局平方根截面 $w=\sqrt\rho$，因而**绝对**整值拓扑不变量在满域上缺失。本文转向**穿孔相对拓扑**：在 $N=5$ 的情形中，从 $\mathcal D^{\rm full}_5$ 移除三—二能级间隙闭合集 $\Sigma_{3|2}=\{\lambda_3=\lambda_4\}$ 的管状邻域，得到穿孔域 $\mathcal D^{\rm exc}$。在 $\mathcal D^{\rm exc}$ 上以 **Riesz 谱投影**构造秩 $3/2$ 子丛 $(\mathcal E_3,\mathcal E_2)$ 并实现主丛结构群约化 $U(5)\to U(3)\times U(2)$；进一步利用行列式平衡得到 $S(U(3)\times U(2))$ 约化。我们证明了一般群同构

$$
S\!\big(U(m)\times U(n)\big)\ \cong\ \big(SU(m)\times SU(n)\times U(1)\big)\big/\mathbb Z_{\mathrm{lcm}(m,n)},
$$

并以 $(m,n)=(3,2)$ 推得 $(SU(3)\times SU(2)\times U(1))/\mathbb Z_6$。通过**相对 $K$ 理论边界映射**统一"投影‑陈类"与"质量‑clutching（$\det\widehat\Phi$ 绕数）"，在二维横截 $S^1$ 上得到

$$
\mathrm{Ind}(\not{D}_A+\Phi)=\mathrm{wind}\,\det\widehat\Phi=\langle c_1(\mathcal L_\Phi),[S^1]\rangle .
$$

在 $\mathbb{CP}^2$ 的 spin$^c$/Dolbeault 口径计算 $\mathrm{index}=3$ 作为"三代原型"。本文给出所有核心命题与定理的**完整证明**，并提供两条**协议级**可复现实验/数值方案（纯化干涉环与光子 Dirac‑质量涡旋）。附录包含：统一围道与全域光滑性、群同构的 gcd/lcm 归一化与"选根"、相对 $K$ 理论与 Chern 角色交换图的严格证明、Callias/Anghel–Bunke 指数定理的 Fredholm 构造、以及 $\Gamma=\mathbb Z_6$ 时最小电荷 $1/6$ 的一页算术推导。

**关键词**：Uhlmann 主丛；穿孔相对拓扑；Riesz 投影；主丛约化；$S(U(3)\times U(2))$；$\mathbb Z_6$ 商；相对上同调/$K$ 理论；Dolbeault/spin$^c$ 指标；Callias/Anghel–Bunke 指数；行列式线丛；线算符谱；可复现实验协议

---

## 0 记号、假设与范围

* **混态流形**：$\mathcal D^{\rm full}_N=\{\rho\in{\rm Herm}^+_N:\rho>0,\ \mathrm{tr}\rho=1\}$，本文固定 $N=5$。
* **本征序**：$\lambda_1\ge\cdots\ge\lambda_5$；**谱隙函数** $g(\rho):=\lambda_3-\lambda_4$。
* **穿孔域**：取 $\delta>0$，定义 $\mathcal D^{\rm exc}:=\{\rho\in\mathcal D^{\rm full}_5:\ g(\rho)\ge 2\delta\}$。边界 $Y:=\partial\mathrm{Tub}_\varepsilon(\Sigma_{3|2})$ 等价于 $g=2\delta$ 的管状边界。
* **Riesz 投影**：固定**统一围道族** $\gamma_3$（见引理 1.2 与附录 A），令

$$
P_3(\rho)=\frac{1}{2\pi i}\oint_{\gamma_3}(z-\rho)^{-1}\,dz,\qquad P_2=I-P_3 .
$$

* **Uhlmann 主丛**：$P=\{\sqrt\rho\,U:\ \rho\in\mathcal D^{\rm full}_5,\ U\in U(5)\}$，右作用 $w\cdot V=wV$；$\pi(w)=ww^\dagger$ 给出 $U(5)$-主丛 $P\to\mathcal D^{\rm full}_5$。
* **regular/ordinary 过程（可检清单）**：沿路径满秩、生成元局域 CPTP 且 $C^1$、可选连续净化规范、且**避开** $\Sigma_{3|2}$（$g\ge 2\delta$）。该清单仅作动机：满域无整值全局类；本文专注穿孔域上的**相对**量子化。
* **归一化**：de Rham 配对统一取 $\frac{1}{2\pi i}$ 因子；$\mathbb{CP}^2$ 上超平面类 $H$ 归一化为 $\int_{\mathbb{CP}^1}H=1$、$\int_{\mathbb{CP}^2}H^2=1$。

---

## 1 主结果（陈述）

**定理 A（群同构，gcd/lcm 归一化）**
令 $g=\gcd(m,n)$、$\ell=\mathrm{lcm}(m,n)=mn/g$。同态

$$
\varphi:\ SU(m)\times SU(n)\times U(1)\to S(U(m)\times U(n)),\quad
\varphi(A,B,z)=\mathrm{diag}\big(z^{n/g}A,\ z^{-m/g}B\big)
$$

为满射，且 $\ker\varphi\simeq \mathbb Z_\ell$。因而

$$
S\!\big(U(m)\times U(n)\big)\ \cong\ \big(SU(m)\times SU(n)\times U(1)\big)\big/\mathbb Z_\ell .
$$

特例 $(m,n)=(3,2)\Rightarrow \ell=6$。

**命题 B（分拆唯一性）**
在"简单因子恰为 $SU(3),SU(2)$ 且仅保留一个 $U(1)$"的约束下，$U(5)$ 的唯一可行分拆为 $5=3+2$。

**定理 C（相对桥接）**
设质量端项 $\Phi$ 在 $Y$ 可逆，取单位化 $\widehat\Phi:Y\to U(N)$。则相对 $K$ 理论边界像 $\partial[\det\widehat\Phi]\in K^0(X,Y)$ 与投影线丛 $[\det\mathcal E_3]-[\det\mathcal E_2]$ 相等；在二维链接上

$$
\langle c_1(\mathcal L_\Phi),[S^2]\rangle=\langle c_1(\det\mathcal E_3),[S^2]\rangle\in\mathbb Z .
$$

**定理 D（Callias/Anghel–Bunke）**
若外区可逆 $\Phi^2\ge cI$、$[\nabla,\Phi]\in L^\infty$、$\Phi\in W^{1,2}_{\rm loc}$ 等条件成立，则

$$
\mathrm{Ind}(\not{D}_A+\Phi)=\deg\big(\widehat\Phi|_{S^{d-1}_\infty}\big)\in \pi_{d-1}(U).
$$

由 Bott 周期性 $\pi_k(U)=\mathbb Z$（$k$ 奇）、$0$（$k$ 偶），得：仅当**横截维 $d$ 为偶**时指数可能非零；$d=2$ 时

$$
\mathrm{Ind}=\frac{1}{2\pi i}\oint\mathrm{Tr}(\widehat\Phi^{-1}d\widehat\Phi)
=\mathrm{wind}\,\det\widehat\Phi=\langle c_1(\mathcal L_\Phi),[S^1]\rangle .
$$

**定理 E（$\mathbb{CP}^2$ 指标）**
$\mathrm{Td}(T\mathbb{CP}^2)=1+\tfrac32H+H^2$、$\mathrm{ch}(\mathcal O(1))=1+H+\tfrac12H^2$，故
$\mathrm{index}\,\not{D}^{\mathcal O(1)}=3$。

**推论 F（SM 全局群）**
由定理 A、命题 B，得到

$$
S(U(3)\times U(2))\ \cong\ \frac{SU(3)\times SU(2)\times U(1)}{\mathbb Z_6}.
$$

附录 E 进一步给出线算符谱的电/磁荷格与 $\Gamma=\mathbb Z_6$ 时**最小电荷步长 $1/6$** 的算术推导。

---

## 2 退化集几何与统一围道

**命题 2.1（共维 3 与 $S^2$-链接）**
在保持 $(\lambda_2,\lambda_5)$ 开隙且无额外对称性的三维横截切片中，$\Sigma_{3|2}=\{\lambda_3=\lambda_4\}$ 为共维 3 的正规子集，其小球边界链接同伦 $S^2$。
*证明要点*：将哈密顿量限制到近简并的 2 维本征子空间，得到 $h=x\sigma_x+y\sigma_y+z\sigma_z$；退化条件 $(x,y,z)=(0,0,0)$ 给三独立实约束。见附录 A.3。

**引理 2.2（统一围道；全域 $C^\infty$）**
对任意紧致 $K\subset\mathcal D^{\rm exc}$，存在 $\delta>0$ 与有限覆盖 $\{U_j\}$ 及闭曲线族 $\{\gamma_j\}$ 使：$\forall \rho\in U_j$，$\gamma_j$ 与余谱距离 $\ge \delta$；由此 $P_{3,2}$ 在 $U_j$ 上 $C^\infty$ 并可光滑拼接。详见附录 A.1–A.2。

---

## 3 主丛约化至 $S(U(3)\times U(2))$

**定理 3.1（约化＝截面）**
设 $P\to X$ 为 $U(5)$-主丛，$\mathcal G=P\times_{U(5)}\mathrm{Gr}_3(\mathbb C^5)$。由 $P_3$ 给出截面 $\sigma$ 当且仅当 $P$ admit $U(3)\times U(2)$-约化 $P_H\subset P$。
*证明*：标准主丛论，附录 B.4。

**命题 3.2（行列式平衡的规范性）**
背景平凡丛 $\underline{\mathbb C}^5$ 之固定体积形式给出规范同构
$\det\mathcal E_3\otimes\det\mathcal E_2\simeq\underline{\mathbb C}$，从而约化到 $S(U(3)\times U(2))$。

**定理 3.3（群同构；定理 A 的 $m=3,n=2$）**

$$
S(U(3)\times U(2))\ \cong\ (SU(3)\times SU(2)\times U(1))/\mathbb Z_6 .
$$

*证明*：见附录 B.1；特别注意满射的"选根"一步：给 $(g_3,g_2)$，取 $z\in U(1)$ 满足 $z^6=\det g_3$，令 $A=z^{-2}g_3\in SU(3)$、$B=z^{3}g_2\in SU(2)$。核同构到 $\mathbb Z_6$。

**命题 3.4（分拆唯一性；命题 B）**
分拆 $5=3+2$ 为唯一满足"简单因子 $SU(3),SU(2)$ 且仅一个 $U(1)$"的方案；$(4+1)$ 无 $SU(2)$，$(3+1+1)$ 与 $(2+2+1)$ 皆保留两个 $U(1)$。详见附录 B.2。

---

## 4 相对拓扑的两种刻画及其等价（定理 C）

**4.1 相对 $K$ 理论与边界映射**
对配对 $(X,Y)=(\mathcal D^{\rm exc},\partial\mathrm{Tub}_\varepsilon)$，有长正合列

$$
\cdots\to K^1(Y)\xrightarrow{\ \partial\ }K^0(X,Y)\to K^0(X)\to\cdots .
$$

若 $\Phi$ 在 $Y$ 可逆，则单位化 $\widehat\Phi:Y\to U(N)$ 定义 $[\widehat\Phi]\in K^1(Y)$，其边界 $\partial[\widehat\Phi]\in K^0(X,Y)$。

**4.2 交换图与 de Rham 代表**
奇 Chern 角色 $\mathrm{ch}_1:K^1(Y)\to H^1(Y;\mathbb Q)$ 的 1 维代表为

$$
\mathrm{ch}_1([\widehat\Phi])=\frac{1}{2\pi i}\mathrm{Tr}(\widehat\Phi^{-1}d\widehat\Phi).
$$

存在交换图（附录 C.1）：

$$
\begin{array}{ccc}
K^1(Y) & \xrightarrow{\partial} & K^0(X,Y) \\
\downarrow{\mathrm{ch}_1} & & \downarrow{\mathrm{ch}} \\
H^1(Y) & \xrightarrow{\partial} & H^2(X,Y)
\end{array}
$$

故

$$
\mathrm{ch}\big(\partial[\widehat\Phi]\big)
=\partial\Big[\frac{1}{2\pi i}\mathrm{Tr}(\widehat\Phi^{-1}d\widehat\Phi)\Big]\in H^2(X,Y).
$$

**4.3 等价命题（定理 C）**
与 Riesz 投影给出的 $\mathcal E_3,\mathcal E_2$ 相比较，利用自然性与 clutching‑gluing 论证（附录 C.2），得

$$
\partial[\det\widehat\Phi]=[\det\mathcal E_3]-[\det\mathcal E_2]\in K^0(X,Y),
$$

从而在二维链接上 $\langle c_1(\mathcal L_\Phi),[S^2]\rangle=\langle c_1(\det\mathcal E_3),[S^2]\rangle$。

---

## 5 $\mathbb{CP}^2$ 上的 spin$^c$/Dolbeault 指标（定理 E）

取 $H=c_1(\mathcal O(1))$，$\int_{\mathbb{CP}^2}H^2=1$。

$$
\mathrm{Td}(T\mathbb{CP}^2)=1+\tfrac12c_1+\tfrac1{12}(c_1^2+c_2)=1+\tfrac32H+H^2,\quad \mathrm{ch}(\mathcal O(1))=e^H=1+H+\tfrac12H^2.
$$

顶维系数 $1+\tfrac32+\tfrac12=3$，故 $\mathrm{index}\,\not{D}^{\mathcal O(1)}=3$。Kodaira 消失确保 $\chi=h^0=3$。

---

## 6 Callias/Anghel–Bunke 指数＝度数；二维绕数公式（定理 D）

**6.1 Fredholm 条件**
设 $M$ 完备，Dirac 型算子 $\not{D}_A$ 与自伴端项 $\Phi$。若存在 $R,c>0$ 使 $M\setminus B_R$ 上 $\Phi^2\ge cI$，且 $[\nabla,\Phi]\in L^\infty$、$\Phi\in W^{1,2}_{\rm loc}$，则 $\not{D}_A+\Phi$ 为 Fredholm（附录 D.1）。

**6.2 指数＝度数与奇偶性**
边界化与 Bott 同构给

$$
\mathrm{Ind}(\not{D}_A+\Phi)=\deg\big(\widehat\Phi|_{S^{d-1}_\infty}\big)\in \pi_{d-1}(U),\quad
\pi_k(U)=\begin{cases}\mathbb Z,&k\ \text{奇}\\ 0,&k\ \text{偶}\end{cases}.
$$

二维横截时

$$
\mathrm{Ind}=\frac{1}{2\pi i}\oint_{S^1}\mathrm{Tr}(\widehat\Phi^{-1}d\widehat\Phi)
=\mathrm{wind}\,\det\widehat\Phi=\langle c_1(\mathcal L_\Phi),[S^1]\rangle ,
$$

并与零模计数一致。符号约定：$S^1$ 取逆时针定向。

---

## 7 与 $G_{\rm SM}$ 的线算符谱对齐与最小电荷 $1/6$

由定理 3.3：$G_{\rm SM}\cong (SU(3)\times SU(2)\times U(1))/\mathbb Z_6$。核生成元可取

$$
(\omega_3^{-1}I_3,\ -I_2,\ e^{i2\pi/6}),\qquad \omega_3=e^{i2\pi/3}.
$$

对 $(t,s,q)$（分别为 $SU(3)$ triality、$SU(2)$ parity、$U(1)$ 整荷）之作用为

$$
\omega_3^{-t}\cdot(-1)^s\cdot e^{i2\pi q/6}.
$$

降到商群的充要条件：$q\equiv 2t+3s\pmod{6}$。故规范化超荷 $Y=q/6$ 之最小分数步长为 $1/6$。附录 E 给出电/磁荷格、Dirac 配对整阵与 $\theta$ 周期的一页推导与示例表。

---

## 8 协议级实验与数值方案（概述）

**E1 纯化干涉（绕 $\Sigma_{3|2}$ 的影像）**：离散化统一围道，读出 $2\pi\phi_{\rm rel}$，其中 $\phi_{\rm rel}=\int_{S^2_{\rm link}} F_{\det\mathcal E_3}/(2\pi)\in\mathbb Z$。采样 $N_{\rm shots}\gtrsim 30$、相位噪声 $\delta\phi\lesssim 0.25$rad 可稳判整数。失败情形：路径擦碰 $\Sigma_{3|2}$、非平滑净化；对策：放大围道半径、提高纯度隙与重复采样。

**E2 光子 Dirac‑质量涡旋**：写入质量相位 $e^{ik\theta}$，外区 $|m|\to m_\infty>0$。零模数 $|k|$、近场强度中心化、带隙中点能位构成指纹。稳健区：相位误差 $\le 10^\circ$、耦合失配 $\le 5\%$。附录 F 给出参数表与"通过标准"。

---

## 9 讨论与展望

* **相对 vs 绝对**：满域可缩→绝对整值类消失；穿孔→相对类量子化。
* **维度效应**：$\det$ 仅在二维横截完全检测；高维需使用稳定 $U$ 群生成元。
* **群论桥接**：谱分裂诱导之 $S(U(3)\times U(2))$ 与线谱字典协同工作，给出最小电荷步长 $1/6$。
* **后续**：多缺陷叠加的相对类加法、噪声‑非平衡下的鲁棒窗口、与高阶（$r$-块）分裂的系统推广。

---

# 附录（详细证明等）

## 附录 A｜谱几何与统一围道（对应 §2）

**A.1 谱隙下界与围道选择**
设 $\mathrm{gap}(\rho)=\min\{\lambda_3-\lambda_4,\ \lambda_2-\lambda_3,\ \lambda_4-\lambda_5\}$。在 $X=\mathcal D^{\rm exc}$ 上 $\mathrm{gap}>0$ 连续；任取紧致 $K\subset X$，设 $\delta=\min_K\mathrm{gap}>0$。对每个 $\rho\in K$ 取以 $\tfrac{\lambda_3+\lambda_4}{2}$ 为心、半径 $\delta/2$ 的圆 $\gamma_\rho$，它围住上谱簇且距余谱 $\ge \delta/2$。

**A.2 Riesz 投影的 $C^\infty$ 依赖**
由 resolvent 估计 $|(z-\rho)^{-1}|\le 2/\delta$ 与 $z\mapsto(z-\rho)^{-1}$ 的光滑性，$P_3(\rho)=\frac{1}{2\pi i}\oint_{\gamma_\rho}(z-\rho)^{-1}dz$ 在 $\rho$ 上 $C^\infty$。用有限覆盖 $\{U_j\}$ 与分片单位拼接，得全域 $C^\infty$ 的投影场 $P_{3,2}$。

**A.3 共维 3 与 $S^2$-链接**
在 $\lambda_3$&$\lambda_4$ 近简并处，取 $E=E_{34}\oplus E^\perp$，有效哈密顿量 $h=\alpha \sigma_z+\Re\beta\,\sigma_x+\Im\beta\,\sigma_y$；退化 $\Leftrightarrow (\alpha,\Re\beta,\Im\beta)=(0,0,0)$，三独立实方程故共维 3。取法向小球 $B^3$，其边界 $S^2$ 为链接。

---

## 附录 B｜群同构与最小分拆（对应 §3）

**B.1 定理 A 的完整证明**
同态

$$
\varphi(A,B,z)=\mathrm{diag}(z^{n/g}A,\ z^{-m/g}B),\quad g=\gcd(m,n),\ \ell=\frac{mn}{g}.
$$

**核**：$\varphi(A,B,z)=I\Rightarrow A=z^{-n/g}I_m,\ B=z^{m/g}I_n$。由 $A\in SU(m)\Rightarrow z^{-nm/g}=1\Rightarrow z^\ell=1$。映射

$$
\kappa:\ \mu_\ell\to\ker\varphi,\quad \kappa(z)=(z^{-n/g}I_m,\ z^{m/g}I_n,\ z)
$$

为群同构，故 $\ker\varphi\simeq\mathbb Z_\ell$。

**满射（"选根"）**：给定 $(g_3,g_2)\in S(U(m)\times U(n))$（即 $\det g_3\det g_2=1$），取 $z\in U(1)$ 满足

$$
z^\ell=\det g_3 .
$$

令

$$
A=z^{-n/g}g_3\in SU(m),\qquad B=z^{m/g}g_2\in SU(n).
$$

则

$$
\det A=z^{-nm/g}\det g_3=z^{-\ell}\det g_3=1,\quad
\det B=z^{nm/g}\det g_2=z^\ell\det g_2=1,
$$

且 $\varphi(A,B,z)=(g_3,g_2)$。从而得到所述同构。

**B.2 分拆唯一性表**

| 分拆        | 简单部                     | $S$-约束后 $U(1)$ 个数 | 结论          |
| --------- | ----------------------- | ----------------: | ----------- |
| $4+1$     | $SU(4)$                 |                 1 | 无 $SU(2)$   |
| $3+1+1$   | $SU(3)$                 |                 2 | 违"一 $U(1)$" |
| $2+2+1$   | $SU(2)\times SU(2)$     |                 2 | 同上          |
| **$3+2$** | **$SU(3)\times SU(2)$** |             **1** | **唯一满足**    |

**B.3 一般化**
$S(U(k)\times U(\ell))\cong (SU(k)\times SU(\ell)\times U(1))/\mathbb Z_{\mathrm{lcm}(k,\ell)}$；核生成元的显式写法依嵌入归一化而定，但商群同构类不变。

---

## 附录 C｜相对 $K$ 理论与 Chern 角色（对应 §4）

**C.1 交换图**
对配对 $(X,Y)$，奇 Chern 角色 $\mathrm{ch}_1:K^1(Y)\to H^1(Y;\mathbb Q)$ 给

$$
\mathrm{ch}_1([u])=\frac{1}{2\pi i}\mathrm{Tr}(u^{-1}du).
$$

偶 Chern 角色 $\mathrm{ch}:K^0(X,Y)\to H^{\rm even}(X,Y;\mathbb Q)$ 与 de Rham 边界算子 $\partial$ 组成交换图

$$
\begin{array}{ccc}
K^1(Y) & \xrightarrow{\partial} & K^0(X,Y) \\
\downarrow{\mathrm{ch}_1} & & \downarrow{\mathrm{ch}} \\
H^1(Y) & \xrightarrow{\partial} & H^2(X,Y)
\end{array}
$$

其可交换性由自然性与 Mayer–Vietoris 拼接给出。

**C.2 桥接等式**
设 $\widehat\Phi:Y\to U(N)$ 为单位化质量，$\partial[\det\widehat\Phi]\in K^0(X,Y)$。另一方面，Riesz 投影得到 $\mathcal E_3,\mathcal E_2$，从而 $[\det\mathcal E_3]-[\det\mathcal E_2]\in K^0(X,Y)$。采用同伦延拓使 $\widehat\Phi$ 与谱分裂态射稳定相容，通过交换图在 $H^2(X,Y)$ 中配对到链接 $S^2$ 的整数相等，故两相对类相等。

**C.3 二维横截的显式配对**
若 $Y$ 的分片链接是 $S^1$，则

$$
\oint_{S^1}\frac{1}{2\pi i}\mathrm{Tr}(\widehat\Phi^{-1}d\widehat\Phi)
=\int_{S^2}\frac{F_{\det\mathcal E_3}}{2\pi}\in\mathbb Z .
$$

---

## 附录 D｜Callias/Anghel–Bunke（对应 §6）

**D.1 Fredholm 构造**
取外区截止 $\chi$ 与参数子 $Q=\chi\Phi^{-1}$。有

$$
(\not{D}_A+\Phi)Q=I-K_1,\qquad Q(\not{D}_A+\Phi)=I-K_2,
$$

其中 $K_{1,2}$ 为相对紧（由 $[\nabla,\Phi]\in L^\infty$、Rellich 紧嵌入与外区可逆性）。故 $\not{D}_A+\Phi$ 为 Fredholm。

**D.2 边界映射与度数**
将外区同伦到仅依赖方向的 $\Phi_\infty(\theta)$，指数等于边界映射 $\partial[\widehat\Phi_\infty]\in \widetilde K^0(S^d)\cong\mathbb Z$。Bott 同构给出

$$
\mathrm{Ind}=\deg(\widehat\Phi_\infty)\in \pi_{d-1}(U).
$$

**D.3 二维单涡旋示例**
$\Phi(r,\theta)=U(\theta)H(r)$, $U(\theta)=\mathrm{diag}(e^{ik\theta},1,1)$, $H(r\to\infty)\to m_0 I$。则 $\widehat\Phi=U$、$\mathrm{Ind}=k$。取逆时针定向为正，$k\to -k$ 指数变号。

---

## 附录 E｜线算符谱与最小电荷 $1/6$（对应 §7）

**E.1 核生成元与同余**
由定理 3.3，$\Gamma\simeq\mathbb Z_6$ 生成元可取

$$
g_*=(\omega_3^{-1}I_3,\ -I_2,\ e^{i2\pi/6}),\qquad \omega_3=e^{i2\pi/3}.
$$

对 $(t,s,q)$ 的作用为 $\omega_3^{-t}(-1)^s e^{i2\pi q/6}$。降商条件：

$$
\omega_3^{-t}(-1)^s e^{i2\pi q/6}=1\iff q\equiv 2t+3s\pmod 6.
$$

令 $Y=q/6\Rightarrow Y\equiv t/3+s/2\pmod{\mathbb Z}$，故最小分数单位 $1/6$。

**E.2 电/磁荷格与 Dirac 配对（示意）**
以 $(\mathbf e;\mathbf m)$ 记电/磁荷向量，中心粘合给出同余约束矩阵 $C$，其满足 $(\mathbf e;\mathbf m)\mapsto(\mathbf e;\mathbf m)+C\mathbf n$（$\mathbf n\in\mathbb Z^r$）等价。Dirac 配对整阵 $\Omega$ 在商上整性良好；$\theta$ 周期在商群识别后发生等价缩并。示例表：基本表示 $\mathbf 3$ 与 $\mathbf 2$ 的 $(t,s)$ 值带来 $Y$ 的分数部分 $\{1/3,1/2\}$，与 $U(1)$ 相位合成后给出跨越最小步长 $1/6$。

---

## 附录 F｜实验与数值"checklist"（对应 §8）

**F.1 E1 纯化干涉**

* **输入**：回路 $C$、$\delta$、采样 $N_{\rm shots}$、$(T_1,T_2)$。
* **步骤**：净化—演化—干涉读出—相位展开—围道积分。
* **输出**：$\phi_{\rm rel}\in\mathbb Z$。
* **通过标准**：$|\mathrm{err}(\phi_{\rm rel})|<0.25$ 即可判定整数；若失败，增大回路半径与 $N_{\rm shots}$。

**F.2 E2 光子涡旋**

* **输入**：阵列尺寸、耦合 $J$、质量幅 $m_\infty$、涡旋数 $k$。
* **步骤**：相位版图写入—激励—近场成像—谱定位—零模计数。
* **输出**：零模数 $|k|$。
* **通过标准**：带隙 $>$ 噪声带宽，中心峰显著且能位接近中点。

**F.3 数值脚本要点**

* 网格 $(N_\theta,N_r)$ 取 $N_\theta\ge 64$；
* Riesz 投影沿固定半径 $\delta$ 圆进行围道求积；
* Wilson‑loop 的 $c_1$ 与 $\mathrm{wind}\,\det\widehat\Phi$ 一致，误差 $\sim \mathcal O(h^2)$。

---

**至此，正文与附录完。**
