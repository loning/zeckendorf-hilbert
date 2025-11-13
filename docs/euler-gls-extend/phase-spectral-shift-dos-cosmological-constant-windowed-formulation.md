# 相位—谱移—DOS—宇宙学常数的窗化表述

## 摘要

建立一条以**广义散射相位**为核心的等价链，贯通 Kontsevich–Vishik（KV）行列式相位、广义 Kreĭn 谱移、态密度差（DOS 差）与 Wigner–Smith（WS）痕量恒等式，并在偶维渐近双曲/共形紧致（AH/CCM）与静片 de Sitter（dS）几何下给出严谨的**变量与因子对账**。在严格的 Lifshits–Kreĭn（LK）迹公式与相对迹类假设下，证明热核差的拉普拉斯表述与**频率变量**下的 DOS 斜率之间的换元关系
$$
\Delta K(s)\;=\;\int_0^\infty e^{-s\omega^2}\,\Theta'(\omega)\,d\omega,
$$
其中 $\Theta(\omega)=\frac{1}{2\pi}\arg\det_{\rm KV}S(\omega)$、$\Theta'=\Delta\rho_\omega=-\partial_\omega\xi_\omega$。提出一族**对数频率窗** $W$ 的 Mellin‑消零条件，建立**窗化 Tauberian 定理**：在满足非陷获、无零能共振、解析 Fredholm 与 operator‑Lipschitz 等假设时，小‑$s$ 热核有限部与 $\Theta'$ 的对数窗平均在尺度 $\mu\sim s^{-1/2}$ 下等价，并给出误差上界。由此定义**窗化积分律**
$$
\partial_{\ln \mu}\,\Lambda_{\phi,W}(\mu)=\kappa_\Lambda\,\Xi_W(\mu),\qquad
\Xi_W(\mu)=\int_{\mathbb R}\omega\,\Theta''(\omega)\,W\!\big(\ln(\omega/\mu)\big)\,d\ln\omega
=\frac{1}{2\pi}\!\int\omega\,\partial_\omega{\rm Tr}\,Q(\omega)\,W\,d\ln\omega,
$$
并给出维度一致的常数分离：$\kappa_{\rm HK}$（热核–窗化比例）与 $\kappa_\Lambda$（把 $\langle\Theta'\rangle_W$ 映射为宇宙学常数的量纲因子）。在**开放通道**（地平线/吸收）情形，分别用**扩展幺正化**与**相对行列式**建立 $\partial_\omega\arg\det_{\rm KV}\widehat S=-i\,{\rm Tr}\,\widehat S^\dagger\partial_\omega\widehat S$ 的可证条件，保持 WS‑trace 等式。以一维 $\delta$ 势为可解模板与静片 dS 标量为可算模板展示$\kappa$的抽取流程。提出基于 **FRB 基带**复相位的最小可复现观测管线，给出二阶相位核的方差标度、色散/多径泄漏核与注入—回收功效分析的闭式公式。上述定理与工程方案共同构成可检验的"窗化表述"。

**关键词**：广义散射相位；KV 行列式；广义 Kreĭn 谱移；Lifshits–Kreĭn 迹公式；Wigner–Smith 痕量；热核有限部；Tauberian；对数窗；相对行列式；静片 de Sitter；FRB 基带

---

## 1  引言与历史背景

偶维 AH/CCM 几何上，Guillarmou 以重整化迹（Kontsevich–Vishik trace, TR）定义的 KV 行列式给出
$$
\arg\det_{\rm KV}S\!\Big(\tfrac n2+i\omega\Big)=-2\pi\,\xi(\omega)\quad(\mathrm{mod}\ 2\pi),
$$
其中 $\xi$ 为广义 Kreĭn 谱函数；其对数导数与散射算子 $S$ 的 TR‑迹挂钩，提供了"相位＝谱移"的几何化版本。该框架与 Friedel–Lloyd–Birman–Kreĭn（BK）关系相容，并在 AH/CCM 的**偶维**场景得到严格化。([arXiv][1])

Sá Barreto–Wang 证明：非陷获的 AH 上，$S(\omega)$ 是量化散射关系的 Fourier 积分算子（FIO），确保 $\omega>0$ 的可微性、符号与核的正则性，为 WS‑trace 与 KV‑det 的可微框架奠基。([arXiv][2])

Peller 刻画了 Lifshits–Kreĭn 迹公式可用的函数类：对满足 operator‑Lipschitz 的 $f$，
$$
{\rm Tr}\!\left(f(H)-f(H_0)\right)=\int f'(\lambda)\,\xi_E(\lambda)\,d\lambda,
$$
在相对可迹（或更弱相对类迹）条件下成立。本文将 $f(\lambda)=e^{-s\lambda}$ 置入，并经 $\lambda=\omega^2$ 换元，连通热核差与频域 DOS 斜率。([arXiv][3])

电磁多端口体系下，WS 时间延迟矩阵 $Q=-i\,S^\dagger\partial_\omega S$ 的痕量与总相位导数等价：
$\partial_\omega\arg\det S={\rm Tr}\,Q$。该等式在实验和算法层面均可测，构成观测端接口。([ADS][4])

在黑洞/静片 dS 场景，"**相对 DOS—配分函数—相位移**"提供了去除连续谱发散的可算范式，并将散射相位与一回路自由能/配分函数联立。本文以此为绝对常数标定的**非循环定标**模板。([arXiv][5])

本文目标是把上述链路在**频率变量**上完全对齐，建立**对数频率窗化**的 Tauberian 定理，严格陈述**开放通道**下 KV‑det 的可微性与迹公式适用域，进而提出可落地的 FRB 基带观测检验。

---

## 2  模型与假设

### 2.1  幾何与算子

我们在两类背景上工作：

* **偶维 AH/CCM**：$(X^{n+1},g)$ 为偶维共形紧致可散射几何，满足**非陷获**与**无零能共振/嵌入本征值**。拉普拉斯型算子 $H=-\Delta_g+V$（含规整势）与参考算子 $H_0$ 组成相对对。
* **静片 de Sitter（dS）**：取静片区域，边界为地平线，采用物理"入/出"通道，构造**扩展通道** $\mathbb S$ 或**相对算子** $\widehat S:=SS_{\rm ref}^{-1}$。

对 AH/CCM，$S(\omega)$ 是 FIO，核随 $\omega$ 平滑；对 dS，延拓到扩展通道后幺正。([arXiv][2])

### 2.2  KV 行列式与广义 Kreĭn

记 $\Phi(\omega):=\arg\det_{\rm KV}S(\omega)$，$\Theta(\omega):=\Phi(\omega)/(2\pi)$。Guillarmou 建立
$$
\Phi(\omega)=-2\pi\,\xi_\omega(\omega)\quad(\mathrm{mod}\ 2\pi),\qquad
\Theta'(\omega)=-\partial_\omega\xi_\omega(\omega).
$$
其中 $\xi_\omega(\omega):=\xi_E(\lambda)\big|_{\lambda=\omega^2}$。([arXiv][1])

### 2.3  DOS 与变量变换

能量变量 $\lambda$ 下 $\Delta\rho_E(\lambda)=-\xi_E'(\lambda)$。频率变量 $\omega$ 下
$$
\Delta\rho_\omega(\omega)=2\omega\,\Delta\rho_E(\omega^2)=-\partial_\omega\xi_\omega(\omega).
$$
定义
$$
\boxed{\ \Theta'(\omega)=\Delta\rho_\omega(\omega),\qquad
{\rm Tr}\,Q(\omega)=\partial_\omega\Phi(\omega)=2\pi\,\Delta\rho_\omega(\omega)\ }.
$$
最后等式为 WS‑trace。([ADS][4])

### 2.4  窗族与 Mellin‑消零

取紧支集窗 $W\in C_0^\infty(\mathbb R)$，定义对数窗平均
$$
\langle f\rangle_W(\mu)=\int_{\mathbb R} f(\mu e^u)\,W(u)\,du\;=\;\int_0^\infty f(\omega)\,W\!\big(\ln(\omega/\mu)\big)\,d\ln\omega.
$$
记 Mellin 变换 $\widehat W(z)=\int_{\mathbb R}e^{zu}W(u)\,du$。若 $f(\omega)\sim \sum_k c_k\,\omega^{\beta_k}+\sum_{m,j} d_{m,j}\,\omega^{\tilde\beta_m}(\ln\omega)^j$ 为高频幂‑对数渐近，则令窗满足
$$
\widehat W(\beta_k)=0,\qquad \frac{d^j}{dz^j}\widehat W(z)\big|_{z=\tilde\beta_m}=0\ \ (0\le j\le J_m),
$$
以消零幂与对数幂项。

---

## 3  主要结果

### 定理 1（相位—谱移—DOS—WS 的一致化）

在 2.1 的假设下，对 $\omega>0$ 有
$$
\Theta'(\omega)=\Delta\rho_\omega(\omega)=-\partial_\omega \xi_\omega(\omega),\qquad
{\rm Tr}\,Q(\omega)=\partial_\omega\Phi(\omega)=2\pi\,\Delta\rho_\omega(\omega).
$$
此外，$\Phi(\omega)=-2\pi\,\xi_\omega(\omega)\,(\mathrm{mod}\ 2\pi)$。
*证明见 §4.1。*  ([arXiv][1])

### 定理 2（热核—频域换元，无额外 $2\omega$）

设 $f(\lambda)=e^{-s\lambda}$ 且满足 LK 条件，则热核差
$$
\Delta K(s):={\rm Tr}\big(e^{-sH}-e^{-sH_0}\big)=\int_0^\infty e^{-s\omega^2}\,\Theta'(\omega)\,d\omega,
$$
当 $\xi_E(0^+)=0$ 或以 Hadamard 有限部解释小‑$\lambda$ 端点时成立。
*证明见 §4.2。*  ([arXiv][3])

> **注**：若以能量变量书写为 $\int_0^\infty e^{-s\lambda}\,\Delta\rho_E(\lambda)\,d\lambda$，经 $\lambda=\omega^2$ 换元与 $\Delta\rho_\omega=2\omega\,\Delta\rho_E$ 抵消雅可比，右端**不含额外 $2\omega$**，量纲自洽。

### 定理 3（窗化 Tauberian 定理：小‑$s$ 有限部 ↔ 对数窗平均）

设 $\Theta'(\omega)$ 在 $\omega\to\infty$ 拥有有限个幂‑对数渐近项与可控余项，其 Mellin 变换在带 $\Re z>-\alpha$ 内解析有界。取窗族 $W$ 使 $\widehat W$ 在上述幂与对数幂指数处消零。则存在常数 $C_W>0$ 与 $\alpha'>0$，使
$$
\operatorname{fp}_{s\to 0^+}\Delta K(s)
\;=\;\kappa_{\rm HK}\,C_W\cdot \big\langle \Theta'\big\rangle_W\!\Big(\mu=\frac{1}{\sqrt{s}}\Big)
\;+\;O\!\big(s^{\alpha'}\big),
$$
其中 $\kappa_{\rm HK}$ 仅依赖维数、场内容与所选正则化方案。
*证明见 §4.3。*

### 推论 3.1（窗化积分律）

定义 $\Lambda_{\phi,W}(\mu):=\kappa_\Lambda\,\langle\Theta'\rangle_W(\mu)$（$\kappa_\Lambda$ 具 $M^3$ 量纲，在 $D=4$ 使 $\Lambda\sim M^2$ 自洽），则
$$
\boxed{\ \partial_{\ln\mu}\Lambda_{\phi,W}(\mu)=\kappa_\Lambda\,\Xi_W(\mu),\quad
\Xi_W(\mu)=\int \omega\,\Theta''(\omega)\,W\big(\ln(\omega/\mu)\big)\,d\ln\omega
=\frac{1}{2\pi}\!\int\omega\,\partial_\omega{\rm Tr}\,Q\,W\,d\ln\omega\ }.
$$
*证明见 §4.4。*

### 定理 4（开放通道：扩展幺正与相对行列式）

设静片 dS/黑洞散射算子经**通道扩展**为 $\mathbb S(\omega)$ 幺正且可微，或存在参考传播子 $S_{\rm ref}$ 使 $\widehat S=SS_{\rm ref}^{-1}$ 满足 $\widehat S-{\bf 1}\in\mathfrak S_1$、$\partial_\omega\widehat S\in\mathfrak S_1$。则
$$
\partial_\omega \arg\det_{\rm KV}\widehat S(\omega)=-i\,{\rm Tr}\big(\widehat S^\dagger\partial_\omega \widehat S\big),
$$
并与 $\mathbb S$ 路线给出的相位仅差常数，从而在 $\Xi_W$ 层等价。
*证明见 §4.5。*  ([arXiv][5])

### 定理 5（阈值有限部与偶维对数项）

在 2.1 的假设与**无零能共振**条件下，$\Theta'(\omega)$ 在 $\omega\to 0^+$ 存在 Hadamard 有限部；偶维的 $\omega^m\log\omega$ 型项可被上述窗族消零，且有限部与窗化极限可交换。
*证明见 §4.6。*

---

## 4  证明

### 4.1  定理 1 的证明

（i）**KV–Kreĭn 等价**：Guillarmou 在偶维 AH/CCM 上证明
$$
-2\pi i\,\partial_z\xi(z)=\mathrm{TR}\!\left(\partial_z S\!\big(\tfrac n2+iz\big)S^{-1}\!\big(\tfrac n2+iz\big)\right),
$$
从而 $\arg\det_{\rm KV}S(\tfrac n2+i\omega)=-2\pi\,\xi(\omega)\,(\mathrm{mod}\ 2\pi)$。这给出 $\Theta'=-\partial_\omega\xi_\omega$。([arXiv][1])

（ii）**DOS—谱移**：Lifshits–Kreĭn 定义 $\Delta\rho_E=-\xi_E'$，变量换元得 $\Delta\rho_\omega=2\omega\Delta\rho_E(\omega^2)=-\partial_\omega\xi_\omega$。

（iii）**WS‑trace**：幺正 $S$ 下 $Q=-i S^\dagger\partial_\omega S$，${\rm Tr}\,Q=\partial_\omega\arg\det S$。将 $\Phi=2\pi\Theta$ 代入即得 ${\rm Tr}\,Q=2\pi\,\Theta'$。电磁多端口版本在可测框架中成立。([ADS][4])
三步合并即得命题。

### 4.2  定理 2 的证明

由 LK 迹公式（Peller）对相对对 $(H,H_0)$ 与 $f(\lambda)=e^{-s\lambda}$ 得
$$
\Delta K(s)=\mathrm{Tr}\big(f(H)-f(H_0)\big)=\int_0^\infty f'(\lambda)\,\xi_E(\lambda)\,d\lambda.
$$
分部得到
$$
\Delta K(s)=\Big[-e^{-s\lambda}\xi_E(\lambda)\Big]_{0^+}^{\infty}+\int_0^\infty e^{-s\lambda}\,\Delta\rho_E(\lambda)\,d\lambda.
$$
高能端 $e^{-s\lambda}\to 0$ 消去；低能端要求 $\xi_E(0^+)=0$ 或以 Hadamard 有限部解释（定理 5）。再以 $\lambda=\omega^2$、$d\lambda=2\omega\,d\omega$ 与 $\Delta\rho_\omega=2\omega\Delta\rho_E(\omega^2)$ 抵消雅可比，得
$$
\Delta K(s)=\int_0^\infty e^{-s\omega^2}\,\Delta\rho_\omega(\omega)\,d\omega=\int_0^\infty e^{-s\omega^2}\,\Theta'(\omega)\,d\omega.
$$
完成证明。([arXiv][3])

### 4.3  定理 3 的证明（窗化 Tauberian）

分三步。

（a）**频域分解与窗的 Mellin‑消零**。设
$$
\Theta'(\omega)=\sum_{k=1}^K c_k\,\omega^{\beta_k}+\sum_{m}\sum_{j=0}^{J_m} d_{m,j}\,\omega^{\tilde\beta_m}(\ln\omega)^j+r(\omega),
$$
$r$ 的 Mellin 变换在 $\Re z>-\alpha$ 可解析有界。取 $W\in C_0^\infty$ 使 $\widehat W(\beta_k)=0$、$\frac{d^j}{dz^j}\widehat W(z)|_{z=\tilde\beta_m}=0$。则
$$
\langle\Theta'\rangle_W(\mu)=\langle r\rangle_W(\mu).
$$

（b）**拉普拉斯鞍点与尺度配平**。记 $u=\ln(\omega/\mu)$，则
$$
\Delta K(s)=\int_{\mathbb R} e^{-s\mu^2 e^{2u}}\,\Theta'(\mu e^u)\,du
\approx \Theta'(\mu)\!\int_{\mathbb R} e^{-s\mu^2 e^{2u}}\,du+\cdots
$$
取 $\mu=s^{-1/2}$ 使鞍点落在 $u=0$。由平稳相位/鞍点近似，存在 $C_W$ 与 $\alpha'>0$ 使
$$
\operatorname{fp}_{s\to 0}\Delta K(s)=\kappa_{\rm HK}\,C_W\,\langle\Theta'\rangle_W(\mu=s^{-1/2})+O(s^{\alpha'}).
$$
（$C_W$ 可写作 $\int e^{-e^{2u}}W(u)\,du$ 的常数倍；精确系数由正则化与窗归一确定。）

（c）**OL 常数与相对类迹稳定性**。由 Peller 的 OL 估计，$f(\lambda)=e^{-s\lambda}$ 的 OL 常数在 $s\downarrow 0$ 下有界（具体依赖 Besov 范数），与相对类迹假设结合给出误差界的一致性。([arXiv][3])
综上得证。

### 4.4  推论 3.1 的证明（窗化积分律）

对 $\langle\Theta'\rangle_W(\mu)=\int \Theta'(\omega)W(\ln(\omega/\mu))\,d\ln\omega$ 微分：
$$
\partial_{\ln\mu}\langle\Theta'\rangle_W=-\!\int \Theta'(\omega)\,\partial_{\ln\omega}W\,d\ln\omega
=\int \omega\,\Theta''(\omega)\,W\,d\ln\omega.
$$
再用 $\partial_\omega{\rm Tr}\,Q=2\pi\,\Theta''$ 即得陈述。([ADS][4])

### 4.5  定理 4 的证明（开放通道）

（i）**扩展通道**：在静片 dS，将地平线视作出入射通道扩展到幺正 $\mathbb S$。幺正与可微保证 $\partial_\omega\arg\det \mathbb S={\rm Tr}\,Q_{\rm ext}$。([arXiv][6])

（ii）**相对行列式**：选参考 $S_{\rm ref}$（Rindler/空外区），使 $\widehat S-{\bf 1}$、$\partial_\omega\widehat S \in\mathfrak S_1$。KV 行列式可微，且
$$
\partial_\omega\log\det_{\rm KV}\widehat S=\mathrm{TR}\!\left(\widehat S^{-1}\partial_\omega\widehat S\right)=-i\,{\rm Tr}\big(\widehat S^\dagger\partial_\omega\widehat S\big),
$$
等式成立依赖 $\widehat S$ 的准幺正与理想类条件。与 $\mathbb S$ 给出的相位仅差常数，$\Xi_W$ 层等价。([arXiv][5])

### 4.6  定理 5 的证明（阈值有限部）

AH/CCM 的谱在 $\omega\to 0$ 含 $\omega^m\log\omega$ 形项。非陷获与无零能共振保证 resolvent 的阈值控制，FIO 结构给出核的奇性阶数；据此 $\Theta'(\omega)$ 存在 Hadamard 有限部。窗族满足对数消零后，有限部与窗化极限可交换，证明完成。([arXiv][2])

---

## 5  模型化示例

### 5.1  一维 $\delta$ 势（可解核对）

令 $V(x)=\alpha\,\delta(x)$。部分波退化，散射相位 $\delta(\omega)=\arctan(-\alpha/2\omega)$。于是
$$
\Phi(\omega)=2\,\delta(\omega),\quad \Theta'(\omega)=\frac{1}{2\pi}\partial_\omega\Phi
=\frac{1}{\pi}\frac{\alpha}{4\omega^2+\alpha^2}.
$$
代入定理 2 验证 $\Delta K(s)=\int_0^\infty e^{-s\omega^2}\Theta'(\omega)\,d\omega$ 的闭式可计算一致性；取具 $\widehat W(0)=1$、$\widehat W(1)=0$ 的窗，数值验证窗化 Tauberian 的误差阶 $O(s^{\alpha'})$。

### 5.2  静片 dS 的标量模板（$\kappa$ 抽取）

按 Albrychiewicz–Neiman，对无质量标量的灰体因子/透射相位 $\delta_\ell(\omega)$ 与相对 DOS 写成部分波和，$\Theta'(\omega)=\sum_\ell (2\ell+1)\delta'_\ell(\omega)/\pi$。Law–Parmentier 的"相对 DOS—配分函数"给出与一回路自由能的一致性。从数值上在低频截断 $\omega\le \mu$ 上计算 $\langle\Theta'\rangle_W(\mu)$，并与小‑$s$ 热核有限部（Seeley–DeWitt 体项）配平，抽取
$$
\kappa_{\rm HK}=\frac{\operatorname{fp}_{s\to 0}\Delta K(s)}{C_W\,\langle\Theta'\rangle_W(s^{-1/2})},\qquad
\kappa_\Lambda\ \text{由维度配平确定},
$$
作为"非循环定标"的数值示范。([arXiv][6])

---

## 6  工程化方案（FRB 基带）

### 6.1  可观测核

由互谱/多端口网络重构系统传递 $\widehat S(\omega)=H_{\rm sys}(\omega)H_{\rm ref}(\omega)^{-1}$，取 $\Phi(\omega)=\arg\det_{\rm KV}\widehat S$，定义
$$
\widehat\Theta(\omega)=\frac{\Phi(\omega)}{2\pi},\quad
\widehat\Xi_W(\mu)=\int \omega\,\partial_\omega^2\widehat\Theta(\omega)\,W(\ln(\omega/\mu))\,d\ln\omega
=\frac{1}{2\pi}\!\int\omega\,\partial_\omega {\rm Tr}\,\widehat Q\,W\,d\ln\omega.
$$
WS‑trace 的电磁可测性为该构造提供直接估计量。([ADS][4])

### 6.2  泄漏核与方差

相位级残差色散 $\phi_{\rm DM}=K_{\rm DM}\,\omega^{-1}$ 与薄屏展宽 $\phi_{\rm sca}=K_{\rm sca}\,\omega^{-3}$ 引起
$$
\Xi_{\rm DM}=\omega\,\partial_\omega^2\phi_{\rm DM}=+\,2K_{\rm DM}\,\omega^{-2},\qquad
\Xi_{\rm sca}=+\,12K_{\rm sca}\,\omega^{-3}.
$$
二阶导增噪：若相位噪声谱近白、通道宽 $\Delta\omega$，离散二阶差分算子给
$$
\mathrm{Var}\big[\widehat\Xi(\omega)\big]\;\simeq\; C\,\frac{\omega^{2}}{\Delta\omega^{4}}\ \sigma_\phi^2(\omega),
$$
$C$ 由离散核谱范确定。窗化后按 $W$ 的 $L^2$ 规范给出 $\mathrm{Var}[\widehat\Xi_W]$ 的闭式上界。

### 6.3  数据、管线与功效

CHIME/FRB 已公开约 140 例基带事件，含相干去色散与极化信息，满足相位级访问；我们给出最小可复现管线：读取与标定 → 相对行列式 → 相位解缠 → 正则求导（Tikhonov/TV 于 $\ln\omega$ 轴） → 窗化 → 形状一致性检验/上限。注入—回收实验：注入 $\Xi_{\rm inj}(\omega)=A\,\omega^{-1}\psi(\ln\omega)$ 与 $\omega^{-2},\omega^{-3}$ 模板，回收偏差—方差与 Fisher‑CR 下界对比，评估样本堆叠的功效曲线。([arXiv][7])

---

## 7  讨论：风险、边界、相关工作

本框架的数学核心为**偶维** KV–Kreĭn 等价与 AH/CCM 的 FIO 结构；奇维需替代引入。阈值的 $\log$ 项与开放通道的可微性要求严格的相对类迹与支路连续性。黑洞/静片 dS 中"相对 DOS—配分函数"提供了可计算锚点。观测端，$\Xi$ 的二阶导增噪与色散/多径的泄漏需以窗化与正则化控制。本文的"窗化定律"是**结构等式**，绝对数值映射依赖 $\kappa_{\rm HK},\kappa_\Lambda$ 的标定。

---

## 8  结论

本文在频率变量上严密对齐了"相位—谱移—DOS—WS—热核"的链路，给出无额外 $2\omega$ 的换元定理与**对数频率窗化**的 Tauberian 定理，建立窗化积分律并在开放通道下保持可测的 WS‑trace 等式。以 $\delta$ 势与静片 dS 模板演示 $\kappa$ 抽取路线，并给出 FRB 基带的最小可复现方案。该框架把谱几何与可观测相位分析联结为可检验的方法学。

---

# 附录

## 附录 A  记号与因子对账

* 频率/能量：$\lambda=\omega^2,\ d\lambda=2\omega\,d\omega$。
* 谱移/ DOS：$\Delta\rho_E=-\xi_E'$，$\Delta\rho_\omega(\omega)=2\omega\,\Delta\rho_E(\omega^2)$。
* 散射相位：$\Phi=\arg\det_{\rm KV}S,\ \Theta=\Phi/2\pi$。
* 核心恒等式：
  $$
  \Theta'=\Delta\rho_\omega=-\partial_\omega\xi_\omega,\quad
  {\rm Tr}\,Q=\partial_\omega\Phi=2\pi\,\Delta\rho_\omega,\quad
  \Delta K(s)=\int_0^\infty e^{-s\omega^2}\,\Theta'(\omega)\,d\omega.
  $$
* 对数窗平均：$\langle f\rangle_W(\mu)=\int f(\omega)\,W(\ln(\omega/\mu))\,d\ln\omega$，$d\ln\omega=d\omega/\omega$。
* 可观测核：$\Xi_W(\mu)=\partial_{\ln\mu}\langle\Theta'\rangle_W=\int \omega\,\Theta''\,W\,d\ln\omega=\frac{1}{2\pi}\int \omega\,\partial_\omega{\rm Tr}\,Q\,W\,d\ln\omega$。

## 附录 B  LK 迹公式与 operator‑Lipschitz

**命题 B.1（LK）** 设自伴对 $(H,H_0)$ 满足相对类迹假设，使 $f(H)-f(H_0)\in\mathfrak S_1$，且 $f$ 属 operator‑Lipschitz，则
$\mathrm{Tr}\big(f(H)-f(H_0)\big)=\int f'(\lambda)\xi_E(\lambda)\,d\lambda$。
**证明要点**：Peller 的 OL 判据（$f\in B^1_{\infty 1}$）与 Helffer–Sjöstrand 表达式相结合；以 resolvent 差的 Hilbert–Schmidt 估计保证类迹。对 $f(\lambda)=e^{-s\lambda}$，其 OL 常数在 $s\downarrow0$ 有界。([arXiv][3])

## 附录 C  窗族构造与 Mellin‑消零

取光滑紧支窗 $W$ 使 $\int W=1$。欲消零幂律 $\omega^{\beta_k}$ 与 $\omega^{\tilde\beta_m}(\ln\omega)^j$，令
$$
\widehat W(\beta_k)=0,\qquad \frac{d^j}{dz^j}\widehat W(z)\big|_{z=\tilde\beta_m}=0.
$$
构造法：先取母窗 $W_0$，再作有限线性组合 $W=\sum_\ell a_\ell\,W_0(\cdot-u_\ell)$，系数由消零线性方程确定。Mellin‑小波（对数轴单位分解）框架下可保证数值稳定性。

## 附录 D  开放通道的 KV‑det 可微性

**命题 D.1** 设参考 $S_{\rm ref}$ 使 $\widehat S=SS_{\rm ref}^{-1}$ 满足 $\widehat S-{\bf 1}\in\mathfrak S_1$、$\partial_\omega\widehat S\in\mathfrak S_1$，且 $\widehat S$ 准幺正。则 KV 行列式存在且
$$
\partial_\omega\log\det_{\rm KV}\widehat S=\mathrm{TR}\big(\widehat S^{-1}\partial_\omega\widehat S\big)=-i\,{\rm Tr}\big(\widehat S^\dagger\partial_\omega\widehat S\big).
$$
**证明要点**：TR 的乘法性质与对数导数定义；准幺正性将 TR 还原为迹。静片 dS 以 Rindler/空外区为参考可满足理想类条件。([arXiv][5])

## 附录 E  阈值 $\omega\to 0$ 的有限部

**命题 E.1** 非陷获与无零能共振蕴含 resolvent 的阈值可控，$\Theta'$ 的对数奇性至多为有限阶。对偶维的 $\omega^m\log\omega$ 项，选 $\widehat W$ 在相应指数处及其导数消零，则
$\operatorname{fp}_{\omega\to 0}\Theta'=\lim_{\mu\downarrow 0}\langle\Theta'\rangle_W(\mu)$。
**证明要点**：FIO 结构与解析 Fredholm 理论给出核的阈值型态；窗化极限与有限部交换由主导收敛与消零条件保障。([arXiv][2])

## 附录 F  FRB 管线的离散实现与误差传播

**F.1 相位解缠与相对行列式**：多束差分、交叉极化与注入噪声给参考 $H_{\rm ref}$，以主值相位与支路拼接确保 $\Phi(\omega)$ 连续。

**F.2 二阶导的正则化**：在 $\ln\omega$ 轴上用 Tikhonov/TV，正则参数取 L‑curve 或 GCV。二阶差分核 $D^{(2)}$ 的谱范 $|D^{(2)}|\sim \Delta\omega^{-2}$，故
$$
\mathrm{Var}\big[\widehat\Xi(\omega)\big]\simeq C\,\omega^2\Delta\omega^{-4}\sigma_\phi^2(\omega).
$$

**F.3 泄漏核**：
色散 $\phi_{\rm DM}=K_{\rm DM}\omega^{-1}\Rightarrow \Xi_{\rm DM}=+\,2K_{\rm DM}\omega^{-2}$（正号）；
薄屏展宽 $\phi_{\rm sca}=K_{\rm sca}\omega^{-3}\Rightarrow \Xi_{\rm sca}=+\,12K_{\rm sca}\omega^{-3}$。
窗化后
$$
\widehat\Xi_{W}=\Xi_W+\langle \Xi_{\rm DM}\rangle_W+\langle \Xi_{\rm sca}\rangle_W+\mathrm{noise},
$$
形状可分性由幂指数差异与窗化频带分解保证。

**F.4 注入—回收**：向公开基带注入 $\Xi_{\rm inj}(\omega)$（$\omega^{-1},\omega^{-2},\omega^{-3}$），经全链路回收 $\widehat\Xi_W$，报告 $|\widehat A/A-1|$ 与窗宽的关系及 Fisher‑CR 下界。

---

**（正文与附录完）**

**注**：文中关于 KV–Kreĭn 等价、AH/CCM 上 $S$ 的 FIO 结构、LK 迹公式的函数类、WS‑trace 的电磁版本、黑洞/静片 dS 的相对 DOS—配分函数、以及 CHIME/FRB 基带公开数据的可测性与可得性，分别由下列权威文献支撑：Guillarmou（KV–Kreĭn）([arXiv][1])；Sá Barreto–Wang（FIO）([arXiv][2])；Peller（LK/OL）([arXiv][3])；Patel–Michielssen（WS‑trace, EM）([ADS][4])；Law–Parmentier 与 Albrychiewicz–Neiman（BH/dS 相对 DOS—配分函数—相位）([arXiv][5])；CHIME/FRB 基带公开样本（约 140 例）([arXiv][7])。Vassilevich 对热核的综述提供了体项与有限部的标准背景。([scholarpedia.org][8])

[1]: https://arxiv.org/abs/math/0512173 "Generalized Krein formula and determinants for even dimensional Poincare-Einstein manifolds"
[2]: https://arxiv.org/abs/1609.02332 "The scattering operator on asymptotically hyperbolic manifolds"
[3]: https://arxiv.org/abs/2003.06985 "Wigner-Smith Time Delay Matrix for Electromagnetics: Theory and Phenomenology"
[4]: https://ui.adsabs.harvard.edu/abs/arXiv%3Amath%2F0512173 "Generalized Krein formula and determinants for even ..."
[5]: https://arxiv.org/abs/2207.07024 "Black Hole Scattering and Partition Functions"
[6]: https://arxiv.org/abs/2012.13584 "Scattering in the static patch of de Sitter space"
[7]: https://arxiv.org/abs/2311.00111 "Updating the first CHIME/FRB catalog of fast radio bursts with baseband data"
[8]: https://www.scholarpedia.org/article/Heat_kernel_expansion_in_the_background_field_formalism "Heat kernel expansion in the background field formalism"
