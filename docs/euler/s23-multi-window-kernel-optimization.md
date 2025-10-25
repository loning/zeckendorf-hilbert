# S23. 多窗/多核协同优化：帧算子、广义 Wexler–Raz 双正交与帕累托前沿

—— 带限偶子空间上的多目标变分、强凸/稀疏两范与"极点 = 主尺度"的多窗保持

## 摘要（定性）

在 Paley–Wiener 带限偶子空间中，建立面向窗化谱读数与窗化迹的多窗/多核协同优化统一框架：以 Nyquist–Poisson–Euler–Maclaurin 的三分解误差为驱动，将单窗 L² 强凸与 L¹ 稀疏问题推广为向量窗与帧算子层面的多目标变分；用加权和与 ε-约束刻画帕累托前沿；给出强凸版的存在唯一性与频域核型—时域高阶常系数方程的必要条件，以及稀疏版的投影式 KKT/证书。结构上，以帧算子与**广义 Wexler–Raz 双正交**刻画最优多窗：线性无关时出现 δ-型双正交，存在冗余时由 Gram 伪逆给出 $GG^\dagger$ 型双正交与在张成子空间内的稳定重构。证明在**有限阶**换序纪律与 Nyquist 约束下，多窗拼接不产生新奇性、极阶不升，从而保持"极点 = 主尺度"，并给出可实施模板、失效边界与复现清单。

---

## 0. 预备与记号

### 0.1 Fourier 规范与带限投影

$$
\widehat f(\xi)=\int_{\mathbb R} f(t)\,e^{-it\xi}\,dt,\qquad
f(t)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{it\xi}\,d\xi .
$$

Paley–Wiener 带限偶子空间

$$
\mathrm{PW}^{\mathrm{even}}_\Omega
=\Big\{w\in L^2(\mathbb R):\ \operatorname{supp}\widehat w\subset[-\Omega,\Omega],\ w(t)=w(-t)\Big\}.
$$

缩放 $w_R(t):=w(t/R)$ 满足 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。为保持带限，缩放后统一取带限投影

$$
P_\Omega w_R:=\mathcal F^{-1}\big(\mathbf 1_{[-\Omega,\Omega]}(\xi)\,\widehat{w_R}(\xi)\big),
$$

并以 $P_\Omega w_R$ 参与一切变分与实现。

### 0.2 向量窗、三分解误差与工作纪律

向量窗 $W=(w^{(1)},\dots,w^{(K)})\in(\mathrm{PW}^{\mathrm{even}}_\Omega)^K$，归一约束

$$
w^{(\ell)}(0)=1\qquad(1\le \ell\le K).
$$

卷积记为 $\star$。在测试核 $h$（$|h|_{\mathfrak H}\le1$）与谱密度 $\rho$ 及参照 $\rho_0$ 下，窗化读数

$$
g^{(\ell)}_{\mathrm{spec}}=(h\cdot P_\Omega w_R^{(\ell)})\star\rho,\qquad
g^{(\ell)}_{0}=(h\cdot P_\Omega w_R^{(\ell)})\star\rho_0 .
$$

误差采用**别名/伯努利层/截断**的三分解

$$
\mathfrak E=\mathfrak E_{\mathrm{alias}}+\mathfrak E_{\mathrm{EM}(M)}+\mathfrak E_{\mathrm{trunc}},
$$

其中 Euler–Maclaurin（EM）仅取固定**有限阶** $M\ge2$。假设：

**假设 A（正则性）**：在固定 $(\Delta,M,T)$ 下，$\mathfrak E$ 对 $w$ 凸、下半连续，并由 $\sum_j|w^{(j)}|_{L^2}$ 与 $|\mathbf 1_{\{|t|>T\}}w|_{L^2}$ 的线性界控制；对卷积与加和稳定。

### 0.3 帧算子、Gram 矩阵与广义 Wexler–Raz 双正交

在 $H=L^2([-\Omega,\Omega],\frac{d\xi}{2\pi})$ 中，记 $\widehat w^{(\ell)}\in H$。分析/合成算子

$$
T_W\phi=\big(\langle \phi,\widehat w^{(1)}\rangle_H,\dots,\langle \phi,\widehat w^{(K)}\rangle_H\big),\quad
T_W^\ast c=\sum_{\ell=1}^K c_\ell\,\widehat w^{(\ell)} .
$$

帧算子 $\mathcal S_W=T_W^\ast T_W$，Gram 矩阵 $G=T_W T_W^\ast\in\mathbb C^{K\times K}$，$G_{\ell q}=\langle \widehat w^{(\ell)},\widehat w^{(q)}\rangle_H$。令 $\mathcal V=\overline{\operatorname{span}}\{\widehat w^{(\ell)}\}$。

**定义 0.1（Parseval on $\mathcal V$）**：若 $\mathcal S_W=P_{\mathcal V}$，称 $W$ 为紧帧（Parseval on $\mathcal V$）。

**注**：本文"紧帧"仅指在张成子空间 $\mathcal V$ 上 Parseval；当 $\mathcal V=H$ 时退化为经典 Parseval 帧。

**命题 0.2（广义双正交与重构）**
设 $\widetilde{\mathbf w}:=(\widehat{\widetilde w}^{(1)},\dots,\widehat{\widetilde w}^{(K)})= \mathbf w\,G^\dagger$（矩阵作用于窗索引），则

$$
\sum_{\ell=1}^K \langle \phi,\widehat{\widetilde w}^{(\ell)}\rangle_H\,\widehat w^{(\ell)}=P_{\mathcal V}\phi \qquad(\phi\in H),
$$

且

$$
\frac{1}{2\pi}\int_{-\Omega}^{\Omega}
\widehat w^{(\ell)}(\xi)\,\overline{\widehat{\widetilde w}^{(q)}(\xi)}\,d\xi
=\big(G\,G^\dagger\big)_{\ell q}.
$$

若 $\{\widehat w^{(\ell)}\}$ 线性无关（$\dim\mathcal V=K$），则 $G$ 可逆，$G G^\dagger=I$，上式退化为 Kronecker δ 正交

$$
\frac{1}{2\pi}\int_{-\Omega}^{\Omega}\widehat w^{(\ell)}\,\overline{\widehat{\widetilde w}^{(q)}}\,d\xi=\delta_{\ell q}.
$$

**说明**：此处 $G^\dagger$ 指 Moore–Penrose 伪逆；由 $F(F^*F)^\dagger F^*=P_{\mathcal V}$（其中 $F=T_W^*$）可得结论。Parseval on $\mathcal V$ 仅保证 $P_{\mathcal V}$ 型重构；只有当窗族线性无关（$\dim\mathcal V=K$）时，才出现 δ-型双正交；存在冗余时为 $G G^\dagger$ 型广义双正交。数值实现建议监控 $\kappa(G)$ 并保持其有界，以确保谱投影与重构稳定。

---

## 1. 多目标与帕累托前沿

对每窗设代价向量

$$
\mathbf J^{(\ell)}(w^{(\ell)})
=\big(\mathfrak E(g^{(\ell)}_{\mathrm{spec}}),\ \mathfrak E(g^{(\ell)}_{0})\big)\in\mathbb R_+^2,
$$

总体代价 $\mathbf J(W)=(\mathbf J^{(1)},\dots,\mathbf J^{(K)})\in\mathbb R_+^{2K}$。称 $W$ 为帕累托优，若不存在 $\widetilde W$ 使所有分量不劣且至少一项严格更好。

**定理 1.1（加权和与帕累托）**
在假设 A 下，任意正权 $(\alpha_\ell,\beta_\ell)_{1\le\ell\le K}$ 的加权和

$$
\mathcal J_\Sigma(W)=\sum_{\ell=1}^K\Big(\alpha_\ell\,\mathfrak E(g^{(\ell)}_{\mathrm{spec}})
+\beta_\ell\,\mathfrak E(g^{(\ell)}_{0})\Big)
$$

的极小元皆为帕累托点。若进一步 $\mathbf J(\mathcal C)$（$\mathcal C$ 为可行集）为凸闭，则每个帕累托点均由某组正权实现。一般非凸像集下，加权和方法仅覆盖支持型帕累托点；非支持点可采用 $\varepsilon$-约束法求解。

---

## 2. L² 强凸多窗：存在唯一与必要条件

### 2.1 强凸模型与工作域

取整数 $M\ge2$、系数 $\gamma_j>0$（$j=0,1,\dots,M-1$）、$\lambda>0$，定义

$$
\mathcal J_{\mathrm{BL}}(W)
=\sum_{\ell=1}^K\Big(\sum_{j=0}^{M-1}\gamma_j| (P_\Omega w_R^{(\ell)})^{(2j)}|_{L^2}^2
+\lambda|\mathbf 1_{\{|t|>T\}}\,P_\Omega w_R^{(\ell)}|_{L^2}^2\Big).
$$

**说明**：加入 $j=0$ 项（即 $\gamma_0|P_\Omega w_R^{(\ell)}|_{L^2}^2$）确保低频控制与整体强凸/胁迫性。

帧惩罚取 Hilbert–Schmidt 型

$$
\Psi(W)=\big|\mathcal S_W-P_{\mathcal V}\big|_{\mathrm{HS}}^2
\quad\text{或}\quad
\Psi(W)=\big|\mathcal S_W-P_{\mathcal V_0}\big|_{\mathrm{HS}}^2,
$$

其中 $\mathcal V_0$ 为预设目标子空间。

**定理 2.1（存在唯一）**
在上述条件与假设 A 下，若 $\Psi$ 弱下半连续（例如 $\Psi$ 凸，或由对 $W$ 弱连续的有界线性算子与凸函数复合而得），则 $\mathcal J_{\mathrm{BL}}+\Psi$ 在可行集 $\mathcal C=\{W\in(\mathrm{PW}^{\mathrm{even}}_\Omega)^K:\ w^{(\ell)}(0)=1\}$ 上存在极小元。若 $\gamma_j>0$（$j=0,\dots,M-1$）、$\lambda>0$，且 $\Psi$ 与 $\mathcal J_{\mathrm{BL}}$ 共同强凸，则极小元唯一。

**注**：上述 Hilbert–Schmidt 型 $\Psi(W)=|\mathcal S_W-P_{\mathcal V}|_{\mathrm{HS}}^2$ 对 $W$ 一般非凸；若采用此类结构正则化，则仅讨论/处理局部极小（不主张全局存在与唯一性）。必要条件（§2.2/2.3）的推导对局部极小同样有效。

**工作域说明**：在必要条件的推导与数值实现中，假设 $\{\widehat w^{(\ell)}\}$ 线性无关且 Gram 矩阵一致可逆，使 $\dim\mathcal V$ 固定，$W\mapsto P_{\mathcal V}$ 在该域内 Fréchet 可微。数值实现中建议监控 $\kappa(G)$ 并保持 $\kappa(G)$ 有界，以免 $P_{\mathcal V}(W)$ 的导数不稳。

### 2.2 频域必要条件（核型形式）

存在常数乘子 $\eta\in\mathbb C^K$（与 $\xi$ 无关）与自伴核 $\Gamma(\xi,\eta)$（来自帧惩罚/约束）使在 $|\xi|\le\Omega$ 上

$$
\Big(\sum_{j=0}^{M-1}\gamma_j\,\xi^{4j}\Big)\,\widehat{\mathbf w}_R(\xi)
+\lambda\big(\widehat{\mathbf 1_{\{|t|>T\}}}\star \widehat{\mathbf w}_R\big)(\xi)
+\int_{-\Omega}^{\Omega}\Gamma(\xi,\eta)\,\widehat{\mathbf w}_R(\eta)\,\frac{d\eta}{2\pi}
=\eta ,
$$

其中 $\widehat{\mathbf w}_R=(\widehat{P_\Omega w_R^{(1)}},\dots,\widehat{P_\Omega w_R^{(K)}})^\top$；$\eta\in\mathbb C^K$ 为与 $\xi$ 无关的常数向量，其时域对应 $\eta_\ell\delta_0$。当惩罚取**点态标量**型时，$\Gamma(\xi,\eta)=\Lambda(\xi)\,2\pi\,\delta(\xi-\eta)$，从而通道解耦并可同时对角化。典型例子：
$\Psi(W)=\int \lambda_0(\xi)\big[\sum_\ell|\widehat w^{(\ell)}(\xi)|^2-c(\xi)\big]^2\frac{d\xi}{2\pi}$；若再加 $\sigma\int\sum_\ell|\widehat w^{(\ell)}(\xi)|^2\frac{d\xi}{2\pi}$ 并**取 $\sigma(\xi)\ge 2\lambda_0(\xi)c(\xi)$（a.e.）**，则 $\Psi+\sigma\int\sum_\ell|\widehat w^{(\ell)}|^2$ 对 $W$ 凸（逐点 integrand 为 $u\mapsto \lambda_0(u-c)^2+\sigma u$，其对 $u\ge0$ 凸且单调不减；由凸函数复合规则知整体凸）；配合 $j=0$ 项得强凸。

### 2.3 时域 Euler–Lagrange 与界面条件

记 $\mathcal L_{\ell q}$ 为帧惩罚导出的零阶耦合算子（时域卷积-零阶）。则在分布意义下

$$
\sum_{j=0}^{M-1}\gamma_j\,\partial_t^{4j}\,P_\Omega w_R^{(\ell)}
+\lambda\,\mathbf 1_{\{|t|>T\}}\,P_\Omega w_R^{(\ell)}
+\sum_{q=1}^K (\mathcal L_{\ell q}\,P_\Omega w_R^{(q)})+\eta_\ell\,\delta_0=0 .
$$

在 $|t|<T$ 内为常系数 ODE（最高阶 $4(M-1)$），外侧附加零阶质量项；在 $t=\pm T$ 处由分部积分得到连续到阶 $4(M-1)-1$ 的**自然匹配条件**。匹配条件来自分部积分消去界面分布项，保证无伪 Dirac 残留。

---

## 3. L¹ 稀疏多窗：投影式 KKT 与证书

考虑

$$
\min_{W\in\mathcal C}\
\sum_{\ell=1}^K\Big(\sum_{j=0}^{M-1}\alpha_j| (P_\Omega w_R^{(\ell)})^{(2j)}|_{L^1}
+\beta |\mathbf 1_{\{|t|>T\}}\,P_\Omega w_R^{(\ell)}|_{L^1}\Big).
$$

取亚梯度
$\mu_j^{(\ell)}\in \operatorname{sign}\big((P_\Omega w_R^{(\ell)})^{(2j)}\big)$，
$\nu^{(\ell)}\in \operatorname{sign}\big(\mathbf 1_{\{|t|>T\}}\,P_\Omega w_R^{(\ell)}\big)$。
设 $\boldsymbol\mu_j=(\mu_j^{(1)},\dots,\mu_j^{(K)})^\top,\ \boldsymbol\nu=(\nu^{(1)},\dots,\nu^{(K)})^\top$。则存在常数 $\eta$ 与帧约束伴随 $\mathcal L^\sharp$ 使

$$
P_{(\mathrm{PW}^{\mathrm{even}}_\Omega)^K}
\Big(\sum_{j=0}^{M-1}\alpha_j\,\partial_t^{2j}\boldsymbol\mu_j
+\beta\,\mathbf 1_{\{|t|>T\}}\boldsymbol\nu
+\mathcal L^\sharp W+\eta\,\delta_0\Big)=0,
$$

且对所有可行微扰 $\Delta W$ 有
$\sum_{\ell,j}\alpha_j\int \mu_j^{(\ell)}(\Delta w_R^{(\ell)})^{(2j)}\,dt
+\beta\sum_\ell\int \nu^{(\ell)}\mathbf 1_{\{|t|>T\}}\,\Delta w_R^{(\ell)}\,dt\ge0$。

**注（Fenchel–Rockafellar 对偶证书）**：上述 KKT 条件等价于 Fenchel–Rockafellar 对偶的鞍点条件；数值实现时可通过监控原始—对偶残差与对偶间隙验证收敛性。$\mathcal L^\sharp$ 的定义域应与 $(\mathrm{PW}^{\mathrm{even}}_\Omega)^K$ 在 $L^2$ 内积下对偶。

---

## 4. BN–Bregman 软化、Γ-极限与稳定

令 $\Phi$ 为 Legendre 型势（下半连续、真、严格可积），$\mathcal T$ 为有界线性映射（逐窗或跨窗），考虑

$$
\min_{W\in\mathcal C}\ \mathcal J_\Sigma(W)+\tau\,\Phi^\ast(\mathcal T W)\qquad (\tau>0),
$$

并以 Bregman 距离 $D_\Phi$ 度量软/硬偏差。

**定理 4.1（Γ-极限）**
假设 $\Phi$ 为下半连续、真、严格可积的 Legendre 型势，$\mathcal T$ 有界线性，$\mathcal J_\Sigma$ 强凸且与 $\Phi^*\circ\mathcal T$ 共同给出等胁迫族。则当 $\tau_n\downarrow 0$ 时，$\mathcal J_\Sigma+\tau_n\Phi^\ast\circ\mathcal T$ 在 $((L^2)^K)$-拓扑下对 $\mathcal J_\Sigma$ Γ-收敛；任一极小序列存在收敛子列趋于硬问题极小元，且目标值收敛。

**定理 4.2（对数据的李普希茨稳定）**
若 $\mathcal J_\Sigma,\widehat{\mathcal J}_\Sigma$ 在可行域上同为 $\mu$-强凸，且梯度 $L$-Lipschitz，则其极小元 $W^\star,\widehat W^\star$ 满足

$$
|W^\star-\widehat W^\star|_{(L^2)^K}
\le \frac{1}{\mu}\,\big|\nabla\mathcal J_\Sigma(W^\star)-\nabla\widehat{\mathcal J}_\Sigma(W^\star)\big|_{(L^2)^K},
$$

右端由 $|\rho-\widehat\rho|+|\rho_0-\widehat\rho_0|+|\mathcal T-\widehat{\mathcal T}|$ 的线性量纲控制。

---

## 5. 结构最优性：紧帧与（广义）Wexler–Raz 双正交

**定理 5.1（双帧结构与最优）**
在 Parseval on $\mathcal V$ 的约束或惩罚下，极小对 $(W^\star,\widetilde W^\star)$ 满足：
(i) 各自满足 §2 的频域核型—时域必要条件；
(ii) 若帧惩罚为点态标量型，则 $\mathcal S_{W^\star}$ 在 $\mathcal V^\star$ 上对角化，$\{\widehat w^{(\ell)}\}$、$\{\widehat{\widetilde w}^{(\ell)}\}$ 同时对角化给出 Parseval 结构；
(iii) 当 $K=1$ 且把截断改为**硬约束**（或其权重趋于无穷），并仅保留带限与时间/能量集中约束时，精确回收 Slepian–Pollak/PSWF 经典变分。

---

## 6. 多窗拼接下"极点 = 主尺度"的保持与阈值稳定

### 6.1 多窗线性算子与奇性保持

令母对象 $\Xi$ 在竖条 $a<\Re z<b$ 内亚纯、极点阶有限。定义多窗拼接

$$
\Xi_W:=\sum_{\ell=1}^K \mathcal T_\ell\big[P_\Omega w_R^{(\ell)};\,\Xi\big],
$$

其中 $\mathcal T_\ell$ 为由窗化、Poisson 求和与**有限阶** EM 换序生成的线性算子。

假设满足以下条件：

**(H1) 整函数指数型窗**：各 $P_\Omega w_R^{(\ell)}$ 为 Paley–Wiener 带限函数，在复平面为指数型整函数。

**(H2) Nyquist 匹配与可交换性**：Nyquist 条件满足，使得别名项不将奇性搬移到新位置；Poisson 求和与有限阶 EM 的换序操作在 $\Xi$ 的解析带内合法且可交换。

**(H3) 通道主部非相消**：对任意极点 $p\in\operatorname{Sing}(\Xi)$，若至少有一窗在对应通道上非零，则各通道极点主系数的线性组合不为 0。

**定理 6.1（奇性不增、极阶不升）**
在条件 (H1)–(H2) 下，

$$
\operatorname{Sing}(\Xi_W)\subseteq\operatorname{Sing}(\Xi),\qquad
\operatorname{ord}_{p}(\Xi_W)\le \operatorname{ord}_{p}(\Xi)\ \ (\forall p\in \operatorname{Sing}(\Xi)).
$$

若再满足 (H3)，则对存在非零通道的极点 $p$ 有 $\operatorname{ord}_{p}(\Xi_W)= \operatorname{ord}_{p}(\Xi)$。

### 6.2 相位—谱密度词典在多窗下的稳定

设 $m$ 为 Weyl–Titchmarsh 函数，$\rho=\frac1\pi\Im m$ 为谱密度，$\varphi$ 为 de Branges 相位（或散射相位 $\delta$ 的等价表示）。在 trace-normalized 规范系统/标准 de Branges 规范下，a.e. 有

$$
\varphi'(x)=\pi\,\rho(x).
$$

**注**：此关系依赖于规范选择。在标准 de Branges 空间中，$\varphi'(x)dx$ 给出自然测度密度；Weyl–Titchmarsh 函数 $m$ 为 Herglotz 函数，满足 $\Im m(x+i0)=\pi\rho(x)$。

定义

$$
\varphi'\!\star\! W:=\sum_{\ell=1}^K \mathcal T_\ell\big[P_\Omega w_R^{(\ell)};\,\varphi'\big],
$$

则在多窗窗化后满足

$$
\big|\varphi'\!\star\! W-\varphi'\big|\ \lesssim\ \mathfrak E_{\mathrm{alias}}
+\mathfrak E_{\mathrm{EM}(M)}+\mathfrak E_{\mathrm{trunc}},
$$

故阈值集合的局部偏移受三分解误差线性控制。

---

## 7. 模板与例

**例 7.1（频带划分的 Parseval-on-span）**
将 $[-\Omega,\Omega]$ 划为 $K$ 个子带，取 $\widehat w^{(\ell)}$ 为各子带指示的平滑化，校准使
$\sum_{\ell}|\widehat w^{(\ell)}(\xi)|^2\approx 2\pi\,\mathbf 1_{[-\Omega,\Omega]}(\xi)$。
帧惩罚取点态标量型，必要条件通道解耦。数值实现中监控 $\kappa(G)$ 并做能量均衡以保持稳定性。

**例 7.2（PSWF 单窗极限）**
$K=1$，将截断改为硬约束（或其权重趋于无穷，等价于 $\lambda\to\infty$ 的软—硬极限），并仅保留带限与时间/能量集中约束，得到 Slepian–Pollak 的 PSWF 变分问题。

**例 7.3（两窗协同：伯努利层 vs. 截断）**
低频窗采用高阶导数罚抑制 EM 伯努利层，高频窗用指数尾抑制截断项；以 BN–Bregman 软化耦合取帕累托前沿点。

---

## 8. 失效边界与工作纪律

1. **有限阶换序**：仅使用固定阶 EM（$M$ 固定），**明示不使用无穷阶 EM**。无限阶会引入伪奇性与非法换序，破坏解析结构。
2. **带限维护**：缩放后统一以 $P_\Omega w_R$ 入模；或仅取 $R\ge1$。
3. **帧退化**：靠近线性相关/秩突变时 $P_{\mathcal V}$ 的导数不稳；需保持 $\kappa(G)$ 受控，或改用固定 $\mathcal V_0$ 的惩罚。
4. **Nyquist 失配**：别名主导误差；需增大带宽/采样或提高窗平滑度。

---

## 9. 复现实验最小清单

1. **可行类**：$W\in(\mathrm{PW}^{\mathrm{even}}_\Omega)^K$，各 $w^{(\ell)}(0)=1$。
2. **带限纪律**：一律以 $P_\Omega w_R$ 进入变分与实现。
3. **三分解参数**：$(\Delta,M,T)$ 与 $|h|_{\mathfrak H}\le1$；显式验证 Nyquist 条件。
4. **强凸版**：给出频域核型 EL 与时域 ODE + 自然匹配条件。
5. **稀疏版**：给出投影式 KKT/证书与亚梯度饱和集合。
6. **帧结构**：计算 $G$、$G^\dagger$，展示 $GG^\dagger$ 型双正交重构；线性无关时验证 δ-型。数值上用 SVD/截断伪逆与阈值策略，控制 $\kappa(G)$ 以保持稳定性。
7. **稳定性**：验证 Γ-极限与解映射 Lipschitz 不等式的数值实例。
8. **奇性保持**：在标准测试族上检验条件 (H1)–(H3) 下的"奇性不增、极阶不升"与阈值偏移上界。

---

## 10. 与既有篇章的接口

* **S15（Weyl–Heisenberg 酉表示）**：多窗族 $\{U_\tau V_\sigma w^{(\ell)}\}$ 在相位—尺度群下的协变性保证帧算子 $\mathcal S_W$ 在群平均下的对角化结构；等距性使多目标 $\mathcal J_\Sigma$ 在群作用下不变。
* **S16（de Branges–Krein 规范系统）**：多窗应用于规范系统评估时，传递矩阵 $M(t,z)$ 的 $J$-酉性与偶对称性保证频域核型方程（2.2）的 Hermite 实化；有限阶 EM 不引入新极点，与 de Branges 相位 $\varphi'$ 的单调性相容。
* **S17（散射算子与功能方程）**：多窗化散射相位 $\delta(x)=-2\varphi(x)+\text{常数}$ 的导数 $\delta'=-2\pi\rho$ 直接进入各通道目标 $g^{(\ell)}_{\mathrm{spec}}$；帧结构保证散射矩阵实轴酉性在多窗拼接下不被破坏。
* **S18（轨道—谱窗化不等式）**：本文多目标 $\mathcal J_\Sigma(W)$ 直接量化 S18 §3.3 的三分解误差；定理 2.1 与 3.1 的极小元给出 S18 "最优多窗/多核"的变分刻画。
* **S19（谱图与 Ihara ζ）**：§7 的离散图模板与 S19 §3 的离散轨道—谱窗化不等式对齐；Ihara ζ 的自倒数性对应离散频域的偶对称约束与多窗 Parseval 结构。
* **S20（BN 投影—KL 代价—灵敏度）**：§4 的 BN–Bregman 软化调用 S20 §3 的 Γ-极限定理；强凸条件下的李普希茨稳定性（定理 4.2）直接继承 S20 §4 的信息—能量链。
* **S21（连续谱阈值与奇性稳定性）**：§6 的"极点 = 主尺度"保持依赖 S21 定理 21.6 的奇性不增原理；阈值邻域稳健性（§6.2）调用 S21 定理 21.9 的 Bregman–KL 灵敏度链。
* **S22（窗/核最优化）**：本文将 S22 的单窗 L²/L¹ 变分推广至向量窗与帧算子层面；频域核型方程（2.2）与 S22 式（2.2）对齐，时域 Euler–Lagrange（§2.3）扩展为多窗耦合的 ODE 系统。

---

## 参考文献（线索）

Paley–Wiener；Slepian–Landau–Pollak（PSWF）；de Branges（整函数 Hilbert 空间）；Titchmarsh（函数论与特征函数展开）；Gröchenig（时频与帧）；Wexler–Raz（离散 Gabor 双帧）；Attouch（变分极限）；Rockafellar–Wets（变分分析）；Bauschke–Combettes（凸分析与单调算子）；Miettinen（多目标优化）。

---

## 附录 A：频域核型必要条件的变分推导（要点）

对 $|(P_\Omega w_R^{(\ell)})^{(2j)}|_{L^2}^2=\int \xi^{4j}\,|\widehat{P_\Omega w_R^{(\ell)}}(\xi)|^2\frac{d\xi}{2\pi}$ 作 Gateaux 变分，产生乘子 $\xi^{4j}$；截断项 $|\mathbf 1_{\{|t|>T\}}P_\Omega w_R^{(\ell)}|_{L^2}^2$ 在频域为与 $\widehat{\mathbf 1_{\{|t|>T\}}}$ 的卷积二次型，一阶变分给出卷积项；帧惩罚 $\Psi(W)$ 的 Frechét 导数为零阶核型算子 $\int \Gamma(\xi,\eta)\,\widehat{\mathbf w}_R(\eta)\,\frac{d\eta}{2\pi}$。归一约束 $w^{(\ell)}(0)=1$ 对应时域 $\eta_\ell\delta_0$（频域常数）。综合即得 §2.2 的核型方程。
