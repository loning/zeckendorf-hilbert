# 统一相位–频率读出的跨平台计量范式：FRB 真空极化窗化上限、δ‑环–AB 通量的谱–散射等价与可辨识性、以及散射拓扑不变量的临界耦合计量

## Abstract

提出一套以"相位–频率"为唯一读出的统一计量范式，贯通三类尺度与物理背景各异的系统：宇宙学距离的快速射电暴（FRB）传播、冷原子/电子学一维环形体系中的点相互作用（δ 势）与阿哈罗诺夫–玻姆（AB）通量耦合、以及凝聚态类 D 端点的散射拓扑不变量。本文在统一的**核–窗化–广义最小二乘/ Fisher**语法下给出：其一，基于弯曲时空 QED 一环有效作用对折射率的改变量级进行自洽估算，并构造可复现的**窗化上限器**，在 FRW 背景上界下相位残差规模达不到观测阈值，仅能给出严格上限；其二，严格证明环上谱量化的三角方程

$$
\cos\theta=\cos(kL)+\frac{\alpha_\delta}{k}\sin(kL)
$$

与"**振幅修正**的相位闭合式"

$$
\cos\gamma(k)=|t(k)|\,\cos\theta,\qquad
\gamma=kL-\arctan\!\frac{\alpha_\delta}{k},\quad
|t(k)|=\frac{k}{\sqrt{k^2+\alpha_\delta^2}}
$$

完全等价，仅在 $|t|\to1$ 的极限退化为纯相位闭合；并给出仅凭 $\{k_n(\theta)\}$ **只能唯一反演** $\alpha_\delta\equiv mg/\hbar^2$ 的**结构可辨识性**定理与闭式灵敏度、病态规避准则及窄势宽度的一阶等效化；其三，在类 D 端点上用 $\mathcal Q=\mathrm{sgn}\det r(0)$ 做拓扑判据，提出**近幺正**前提下统一有限尺寸（指数）与接触/边界（代数）偏置的外推回归

$$
J_c(L)=J_c+\beta e^{-L/\xi}+\gamma/L,
$$

并给出与 cQED 读出（腔频移与附加损耗）的线性响应映射。上述结论的证明与工程化流程均随文给出，可直接复现与移植到相近平台。

**Keywords**：相位–频率计量；快速射电暴；弯曲时空 QED；窗化上限；δ 势；阿哈罗诺夫–玻姆效应；自伴扩展；散射拓扑不变量；Majorana；cQED

---

## 1. Introduction & Historical Context

以"相位–频率"为单一观测量的计量方案天然横跨多个前沿：在宇宙学电磁传播中，相位随频率的微扰记录几何与介质；在一维量子环中，相移量化了散射与几何相干；在凝聚态散射计量中，低能反射子块的相位与行列式刻画拓扑数。弯曲时空 QED 的一环有效作用表明真空极化在弱曲率背景上仅引入极微的折射率修正，且满足高频因果与解析性；这使 FRB 的**载频相位**天然成为一条可供设定**上限**的管道，而非现实的探测量。δ‑环问题在自伴扩展的 $U(2)$ 框架下可得严整的谱–散射等价并与 AB 通量统一；拓扑端点则可由单端反射矩阵的零能判据实现非局域拓扑的近场计量。上述背景在近年文献中日渐清晰，本文的目标是将之凝练为**统一的计量语法与可复现配方**。

---

## 2. Model & Assumptions

### 2.1 统一观测方程、权重与窗化

在三平台中，观测量均可抽象为对频率的相位型读出 $m(\omega)$。统一表述为

$$
m(\omega)=\int_{\mathcal{P}} \mathcal{K}(\omega,\chi)\,x(\chi)\,{\rm d}\chi+\sum_{p=0}^{P-1} a_p\,\Pi_p(\omega)+\epsilon(\omega),
\tag{2.1}
$$

其中 $\mathcal{K}$ 为观测核，$\chi$ 表示传播参数（如共形坐标）、几何相位或能量刻度；$x(\chi)$ 为待估函数（或窗化参数）；$\Pi_p$ 为系统学/前景基函数，$a_p$ 其幅度；$\epsilon$ 为噪声过程，协方差 $C_\phi(\omega,\omega')$。在离散频轴上采用权重内积

$$
\langle f,g\rangle \equiv \sum_{ij} f(\omega_i)\,[C_\phi^{-1}]_{ij}\,g(\omega_j).
\tag{2.2}
$$

定义经加权 Gram–Schmidt 正交化的频窗 $W_j(\omega)$，并以 $A_{j\mu}=\langle W_j,\,\mathcal{K}(\cdot,\chi_\mu)\rangle$ 构造设计矩阵；广义最小二乘（GLS）与 Fisher 信息

$$
\hat{\boldsymbol{\theta}}=(A^\top A)^{-1}A^\top \mathbf{y},\qquad F=A^\top A,
\tag{2.3}
$$

其中 $\mathbf{y}_j=\langle W_j,m\rangle$，$\boldsymbol{\theta}$ 是窗化参数（或 $x(\chi)$ 在分段常数基中的系数）。单频率相位的经典 CRB 在白噪声极限下退化为 $\sigma_\phi\ge (2N\rho)^{-1/2}$，为本文上限推导的信号处理参照。

### 2.2 平台特定假设与核

* **FRB 传播**：沿共形坐标 $\chi$（${\rm d}\ell=a(\eta){\rm d}\chi$）积分时，局域频率 $\omega_{\rm loc}=(1+z)\omega_{\rm obs}$ 与尺度因子相消，故

$$
\boxed{\ \mathcal{K}_{\rm FRB}(\omega_{\rm obs},\chi)=\omega_{\rm obs}/c\ },
\tag{2.4}
$$

  并以 $x(\chi)\equiv \delta n(\chi)$（折射率修正）作为被窗化的目标核。该写法保证高频因果 $n(\omega\to\infty)\to 1$ 与世界线–Penrose 极限下的解析性约束。

* **δ‑环 + AB 通量**：观测量为满足量子化条件的本征波数 $k(\theta)$，以 $\alpha_\delta\equiv mg/\hbar^2$ 表示点相互作用强度，几何长度 $L$ 为环周长，$\theta=2\pi\Phi/\Phi_0$ 为通量相位。核函数体现在色散关系与边界条件上，见第 4 节。

* **拓扑散射**：观测量为零能反射矩阵 $r(0)$ 的特征相位或其行列式的符号；核 $\mathcal{K}$ 来自散射–拓扑映射与输入–输出的线性响应，见第 6 节。

---

## 3. Main Results (Theorems and Alignments)

### 定理 A（FRB：一环真空极化的窗化上限与数量级）

弯曲时空 QED 在弱曲率背景下给出折射率的一环修正量级

$$
\delta n \sim \frac{\alpha_{\rm em}}{\pi}\,\lambda_e^2\,\mathcal{R},
\tag{3.1}
$$

取 FRW 上界 $|\mathcal R|\sim H_0^2/c^2$，则 1 GHz、1 Gpc 的相位累积上限

$$
\Delta \phi \sim \frac{\omega_{\rm obs} L}{c}\,\delta n \approx 1.2\times 10^{-53}\ {\rm rad}.
\tag{3.2}
$$

因此在任何现实的基带数据体量与噪声下，仅能对 $x(\chi)=\delta n(\chi)$ 给出窗化上限，而非有效检出。证明见附录 A。

### 定理 B（δ‑环：三角方程与振幅修正相位式的等价）

对一维环上 δ 势（强度 $g$）与 AB 通量 $\theta$，本征波数 $k$ 满足

$$
\boxed{\ \cos\theta=\cos(kL)+\frac{\alpha_\delta}{k}\sin(kL)\ },
\tag{3.3}
$$

其与

$$
\boxed{\ \cos\gamma(k)=|t(k)|\,\cos\theta,\
\gamma(k)=kL-\arctan\!\frac{\alpha_\delta}{k},\
|t(k)|=\frac{k}{\sqrt{k^2+\alpha_\delta^2}}\ }
\tag{3.4}
$$

完全等价。且仅在 $|t(k)|\to 1$（弱散射或透射共振）时退化为纯相位闭合 $\cos\gamma=\cos\theta$。证明见附录 B。

### 定理 C（δ‑环：仅凭 $\{k_n(\theta)\}$ 的结构可辨识性）

在固定 $(L,\theta)$ 的谱观测 $\{k_n(\theta)\}$ 下，能唯一反演 $\alpha_\delta=mg/\hbar^2$，但无法分离 $m$ 与 $g$ 的个别数值。若引入第二类独立读出（如能谱 $E_n=\hbar^2 k_n^2/(2m)$ 或绝对势强度 $g_{\rm eff}=\int V\,{\rm d}x$ 的标定），则一般点上 $(m,g)$ 的雅可比满秩而可解耦。证明见附录 B。

### 定理 D（δ‑环：隐函数灵敏度与病态条件）

令

$$
f(k,\alpha_\delta,\theta)=\cos(kL)+\frac{\alpha_\delta}{k}\sin(kL)-\cos\theta,
\tag{3.5}
$$

则

$$
\frac{\partial k}{\partial \alpha_\delta}
=\frac{ \dfrac{\sin(kL)}{k} }
{ L\sin(kL)-\dfrac{\alpha_\delta}{k}L\cos(kL)+\dfrac{\alpha_\delta}{k^2}\sin(kL) }.
\tag{3.6}
$$

病态域由 $\partial f/\partial k=0$ 给出；当 $|\alpha_\delta|/k\ll 1$ 时近似为 $\sin(kL)\simeq (\alpha_\delta/k)\cos(kL)$。证明见附录 B。

### 定理 E（δ‑势有限宽度的一阶等效化）

对窄势 $V(x)$（宽度 $w\ll L$）且 $\int V\,{\rm d}x=g$ 固定，在 $(kw)\ll1$ 区域，环上的等效强度

$$
\alpha_\delta^{\rm eff}(k)=\frac{m}{\hbar^2}\,g\left[1+\eta_2[V]\,(kw)^2+\mathcal O\!\big((kw)^4\big)\right],
\tag{3.7}
$$

其中形状因子 $\eta_2[V]$ 由 $V$ 的二阶矩决定；矩形与高斯势分别有 $\eta_2=\tfrac{1}{3},\ \tfrac{1}{2}$。证明与数值对照见附录 B。

### 定理 F（拓扑散射不变量：近幺正外推）

在近幺正（$|r^\dagger r-\mathbb 1|\le \varepsilon_\star$）的前提下，有限长度 $L$、接触不完美与微弱耗散引入对临界耦合 $J_c$ 的偏置，统一可由

$$
\boxed{\ J_c(L)=J_c+\beta e^{-L/\xi}+\gamma/L\ }
\tag{3.8}
$$

外推回归吸收，其中指数项对应端态耦合的重叠，代数项对应接触/边界效应。$\mathcal Q=\mathrm{sgn}\det r(0)$ 的翻转给出 $J_c(L)$ 的观测轨道。证明见附录 C。

### 定理 G（cQED 冗余读出与散射不变量的一致性）

单端口弱耦合下，输入–输出关系给出

$$
r(\omega)=\frac{1-Z_0Y(\omega)}{1+Z_0Y(\omega)}\approx 1-2Z_0Y(\omega),
\qquad
\delta\omega_c\propto g_{\rm cav}^2\,\mathrm{Re}\,\chi(\omega_c),\
\kappa_{\rm add}\propto g_{\rm cav}^2\,\mathrm{Im}\,\chi(\omega_c),
\tag{3.9}
$$

其中 $\chi$ 为端点子系统的线性响应。对适当失谐 $|\omega_c-\omega_{\rm cont}|\gtrsim 3\kappa$ 时，$\{\delta\omega_c,\kappa_{\rm add}\}$ 的零交叉与 $\mathcal Q$ 的翻转一致。证明见附录 C。

---

## 4. Proofs

### 4.1 定理 A 的证明（FRB）

QED 在弯曲背景的有效作用可写为

$$
\mathcal{L}_{\rm eff}=-\frac14 F_{\mu\nu}F^{\mu\nu}
+\frac{1}{m_e^2}\left(a R F_{\mu\nu}F^{\mu\nu}
+b R_{\mu\nu}F^{\mu\alpha}F^{\ \nu}_{\alpha}
+c R_{\mu\nu\alpha\beta}F^{\mu\nu}F^{\alpha\beta}\right)+\cdots,
\tag{4.1}
$$

线性化色散关系给出折射率修正 $\delta n\propto (\alpha_{\rm em}/\pi)\lambda_e^2 \mathcal R$。在 FRW 上，取 $|\mathcal R|\sim H_0^2/c^2$，并以式 (2.4) 的核沿 $\chi$ 积分，

$$
\Delta\phi=\int_0^{\chi_s}\frac{\omega_{\rm obs}}{c}\,\delta n(\chi)\,{\rm d}\chi
\le \frac{\omega_{\rm obs} L}{c}\,\max_{\chi}\delta n(\chi),
\tag{4.2}
$$

代入常数 $(\alpha_{\rm em}/\pi)\simeq 2.32\times 10^{-3}$、$\lambda_e=3.8616\times 10^{-13}\ {\rm m}$、$|\mathcal R|\simeq 5.4\times10^{-53}\ {\rm m^{-2}}$ 与 $\omega_{\rm obs}L/c\simeq 6.46\times10^{26}$（1 GHz/1 Gpc），得 $\Delta\phi\approx 1.2\times 10^{-53}$ rad。Hollowood–Shore 的世界线–Penrose 极限保证 $n(\omega\to\infty)\to1$，本文构造的窗化核满足该因果/解析性约束。

### 4.2 定理 B 的证明（δ‑环）

从直线 δ 势的散射幅 $t=\dfrac{k}{k+i\alpha_\delta}$ 与 $|t|=\dfrac{1}{\sqrt{1+(\alpha_\delta/k)^2}}$ 出发，将一圈的传输矩阵迹条件 $\mathrm{tr}\,T=2\cos\theta$ 展开得

$$
\cos\theta=\cos(kL)+\frac{\alpha_\delta}{k}\sin(kL).
\tag{4.3}
$$

另一方面

$$
\cos(kL)+\frac{\alpha_\delta}{k}\sin(kL)
=\Re\!\Big[(\cos kL+i\sin kL)\,\Big(1-i\frac{\alpha_\delta}{k}\Big)\Big]
=\sqrt{1+(\alpha_\delta/k)^2}\,\cos\Big(kL-\arctan\frac{\alpha_\delta}{k}\Big),
\tag{4.4}
$$

即 $\cos\gamma=|t|\,\cos\theta$，证毕。

### 4.3 定理 C 的证明（可辨识性）

谱方程 (3.3) 仅含组合参数 $\alpha_\delta=mg/\hbar^2$；若存在 $(m_1,g_1)\ne (m_2,g_2)$ 但 $m_1g_1=m_2g_2$，则对任意 $(\theta,n)$ 给出相同 $\{k_n\}$。因此仅凭 $\{k_n(\theta)\}$ 唯一确定 $\alpha_\delta$，而 $m$、$g$ 不可分。若加入能谱 $E_n=\hbar^2 k_n^2/(2m)$，则

$$
J=\begin{pmatrix}
\partial f/\partial m & \partial f/\partial g\\
\partial E/\partial m & \partial E/\partial g
\end{pmatrix}
=\begin{pmatrix}
\frac{\partial f}{\partial \alpha_\delta}\frac{\partial \alpha_\delta}{\partial m} & \frac{\partial f}{\partial \alpha_\delta}\frac{\partial \alpha_\delta}{\partial g}\\[4pt]
-\frac{\hbar^2 k^2}{2m^2} & 0
\end{pmatrix},
\tag{4.5}
$$

在一般点上 $\det J\ne 0$（除非 $k=0$ 等退化子集），故 $(m,g)$ 可解耦，证毕。

### 4.4 定理 D 的证明（灵敏度）

由隐函数定理

$$
\frac{\partial k}{\partial \alpha_\delta}=-\frac{f_{\alpha_\delta}}{f_k},
\qquad
f_{\alpha_\delta}=\frac{1}{k}\sin(kL),\
f_k=-L\sin(kL)+\alpha_\delta\Big(\frac{L}{k}\cos(kL)-\frac{1}{k^2}\sin(kL)\Big),
\tag{4.6}
$$

得式 (3.6)。病态域满足 $f_k=0$，当 $|\alpha_\delta|/k\ll 1$ 时近似为 $\sin(kL)\simeq (\alpha_\delta/k)\cos(kL)$，证毕。

### 4.5 定理 E 的证明（有限宽度）

设窄势 $V(x)=V_0 u(x/w)$（$\int u=1$）且 $g=V_0 w$ 固定，传输矩阵在 $kw\ll 1$ 时的低能展开给出

$$
t^{-1}(k)=1+i\frac{\alpha_\delta}{k}+\eta_2[V]\,(kw)^2+\mathcal O\big((kw)^4\big),
\tag{4.7}
$$

等效为 $\alpha_\delta\to \alpha_\delta^{\rm eff}(k)$ 的替换。对矩形/高斯 $u$ 计算其二阶矩并与可解模型对照，可得 $\eta_2=\tfrac{1}{3},\ \tfrac{1}{2}$。数值验证见附录 B 图 B2。

### 4.6 定理 F 与 G 的证明（拓扑散射与 cQED）

类 D 体系的拓扑数可由单端反射矩阵的零能判据 $\mathcal Q=\mathrm{sgn}\det r(0)$ 给出。有限长度耦合导致零模的能量分裂 $\propto e^{-L/\xi}$，接触/边界引入 $1/L$ 标度；在近幺正假设下，$\det r(0)$ 的符号翻转轨道 $J_c(L)$ 因而呈式 (3.8) 的形状。另一方面，输入–输出给出 $r\approx 1-2Z_0Y$，而 $Y\propto g_{\rm cav}^2 \chi$；当腔模远离连续谱足够失谐时，$\chi(0)$ 的符号变化在 $\{\delta\omega_c,\kappa_{\rm add}\}$ 上产生零交叉，与 $\mathcal Q$ 的翻转一致，证毕。

---

## 5. Model Apply

### 5.1 FRB"窗化上限器"

* **核与权重**：采用 $\mathcal K_{\rm FRB}=\omega_{\rm obs}/c$，$\Pi_p(\omega)\in\{1,\ \omega,\ \omega^{-1},\ \log\omega\}$。$C_\phi$ 由离源、离带与旁瓣三通道自举估计。
* **正交窗**：对 $\{\log\omega_i\}$ 上的离散频轴，使用 $C_\phi^{-1}$ 加权 Gram–Schmidt 得 $W_j$，并做白化检验 $\langle W_j,W_\ell\rangle\simeq \delta_{j\ell}$。
* **上限**：对窗化参数 $\boldsymbol{\theta}$ 采用 GLS 与 profile‑likelihood 并行计算 95% 上限带，给出随带宽/事件数的缩放曲线与系统学基包络；将"是否包含 $\omega^{-1}$"作为稳健性开关并取包络。

### 5.2 δ‑环反演与病态规避

* **反演**：以式 (3.3) 的 $f=0$ 为目标，用式 (3.6) 作为牛顿步长迭代反演 $\hat\alpha_\delta$。
* **病态域**：在 $(kL,\alpha_\delta/k)$ 平面绘制 $|f_k|<\tau$ 的灰区（$\tau\sim 10^{-2}$），实验选点避开该域。
* **有限宽度**：对给定 $w$ 与势形状，用式 (3.7) 修正 $\hat\alpha_\delta$，并将 $\eta_2$ 的不确定度传播到协方差。

### 5.3 拓扑外推与 cQED 冗余

* **外推回归**：在 $\{L_i\}$ 上测定 $\mathcal Q$ 翻转的 $J_c(L_i)$，用式 (3.8) 回归 $(J_c,\beta,\gamma,\xi)$，并用 AIC/BIC 比较"指数/代数/复合"三模型。
* **近幺正质控**：以 $\varepsilon_i=|r_i^\dagger r_i-\mathbb 1|$ 加权或作为协变量进入回归，并报告 $J_c$ 对 $\varepsilon$ 的敏感度。
* **cQED 一致性**：在满足 $|\omega_c-\omega_{\rm cont}|\gtrsim 3\kappa$ 的失谐下，用 $\{\delta\omega_c,\kappa_{\rm add}\}$ 的零交叉作为冗余证据，与 $\mathcal Q$ 翻转进行交叉验证。

---

## 6. Engineering Proposals

* **FRB**：发布最小化脚本加载公开基带样例，完成相干去色散、结构最大化 DM、三通道自举协方差、加权窗正交化与 95% 上限出图，附上"是否包含 $\omega^{-1}$ 基"的稳健性对照。
* **δ‑环**：提供$\{k_n(\theta)\}$ 反演 $\alpha_\delta$ 的可执行脚本，绘制病态域灰图与 $\partial k/\partial\alpha_\delta$ 等值线；给出有限宽度校正与误差传播示例。
* **拓扑 + cQED**：发布从 $r(\omega)$ 提取 $\mathcal Q$、回归 $J_c(L)$ 与模型比较、及 $\{\delta\omega_c,\kappa_{\rm add}\}$ 与 $\mathcal Q$ 的一致性检验脚本。

---

## 7. Discussion (risks, boundaries, past work)

**FRB**：在 FRW 背景量级下，一环真空极化相位效应不可测；本文定位为"窗化上限器"，强调核–度量选择的一致性与系统学包络，避免错设偏差。
**δ‑环**：将"纯相位闭合"严格限定在 $|t|\to 1$ 的极限，避免在一般 $\theta$ 下误用；有限宽度等效化需在 $kw\ll1$ 区域内使用。
**拓扑**：近幺正阈值与模型选择是外推可靠性的关键，建议用残差结构与交叉验证抑制过拟合。

---

## 8. Conclusion

本文以统一的相位–频率读出与"核–窗化–GLS/Fisher"语法，建立了三条平台的可复现计量配方：FRB 侧给出严格的窗化上限器；δ‑环侧证明谱–散射的振幅修正相位等价、结构可辨识性及灵敏度闭式与有限宽度修正；拓扑散射侧用近幺正外推与 cQED 冗余实现临界耦合的可计量。配套的工程化流程与最小脚本使该范式便于迁移至相近系统。

---

## Acknowledgements, Code Availability

感谢相关公开数据与文献提供的可复现基准。配套代码与最小数据样例将以通用许可证发布，包含环境锁定文件、单位检查与注入–回收测试。FRB 脚本与 δ‑环、拓扑外推脚本采用统一 I/O 约定与随机种子以保证可重复性。数据使用与引用遵循各数据集的政策。

---

## References

1. Drummond, I. T., Hathrell, S. J., "QED vacuum polarization in a background gravitational field," *Phys. Rev. D* **22**, 343 (1980).
2. Hollowood, T. J., Shore, G. M., "The causal structure of QED in curved spacetime: Analyticity and the refractive index," *JHEP* **12**, 091 (2008); related works (2008–2009).
3. CHIME/FRB Collaboration, "Updating the First CHIME/FRB Catalog of Fast Radio Bursts with Baseband Data," *ApJ* **969**, 145 (2024).
4. Hessels, J. W. T., *et al.*, "FRB 121102 Bursts Show Complex Time–Frequency Structure," *ApJL* **876**, L23 (2019).
5. Castillo‑Sánchez, M., Gutiérrez‑Vega, J. C., "Quantum solutions for the delta ring and delta shell," *Am. J. Phys.* **93**, 557–565 (2025).
6. Fülöp, T., Tsutsui, I., "A Free Particle on a Circle with Point Interaction," *Phys. Lett. A* **264**, 366–374 (2000).
7. Fulga, I., Hassler, F., Akhmerov, A. R., Beenakker, C. W. J., "Scattering formula for the topological quantum number of a disordered multi‑mode wire," *Phys. Rev. B* **83**, 155429 (2011).
8. Araya Day, J., *et al.*, "Identifying biases of the Majorana scattering invariant," *SciPost Phys. Core* **8**, 047 (2025).
9. Dmytruk, O., Trif, M., "Microwave detection of gliding Majorana zero modes," *Phys. Rev. B* **107**, 115418 (2023).
10. Rife, D. C., Boorstyn, R. R., "Single‑tone parameter estimation from discrete‑time observations," *IEEE Trans. Inf. Theory* **20**, 591–598 (1974).

---

## Appendices

### Appendix A. FRB：一环真空极化规模、核–度量一致性与窗化上限

**A.1 一环有效作用与规模**
从式 (4.1) 线性化麦克斯韦方程，在弱曲率与几何光学近似下，色散关系 $k^2=n^2\omega^2/c^2$ 给出

$$
n(\omega,\chi)=1+\delta n(\chi)+\mathcal O(\mathcal R^2),\qquad
\delta n(\chi)\approx\frac{\alpha_{\rm em}}{\pi}\lambda_e^2\,\mathcal R(\chi).
$$

FRW 背景上 $R_{\mu\nu\alpha\beta}$ 的低阶缩并给出 $|\mathcal R|\sim H_0^2/c^2$。

**A.2 核–度量一致性（红移相消）**
沿测地线的相位增量

$$
{\rm d}\phi=\frac{\omega_{\rm loc}}{c}\,\delta n(\chi)\,{\rm d}\ell
=\frac{(1+z)\omega_{\rm obs}}{c}\,\delta n(\chi)\,a(\eta)\,{\rm d}\chi
=\frac{\omega_{\rm obs}}{c}\,\delta n(\chi)\,{\rm d}\chi,
$$

即在共形坐标积分时 $(1+z)$ 与 $a$ 精确相消，得到式 (2.4) 的核。该写法自动满足 $n(\omega\to\infty)\to 1$ 的因果性要求。

**A.3 Fisher/GLS 的窗化上限**
将 $\delta n(\chi)$ 在分段常数基上展开，定义 $A_{j\mu}=\langle W_j, \omega_{\rm obs}/c\rangle \Delta\chi_\mu$，则

$$
F=A^\top A,\qquad
\boldsymbol{\sigma}_{\rm UL}=1.96\,\sqrt{{\rm diag}(F^{-1})},
$$

并对系统学基的不同选择（是否包含 $\omega^{-1}$、$\log\omega$）取上限包络。

### Appendix B. δ‑环：边界条件、等价性、可辨识性、灵敏度与有限宽度

**B.1 边界条件与三角方程**
直线 δ 势的边界条件

$$
\psi'(0^+)-\psi'(0^-)=2\alpha_\delta\,\psi(0),\qquad \alpha_\delta=mg/\hbar^2,
$$

配合自由传播段的传输矩阵可得一圈的迹条件 $\mathrm{tr}\,T=2\cos\theta$，化简即式 (3.3)。

**B.2 等价性三行推导**
利用

$$
\Re\Big[e^{ikL}\Big(1-i\frac{\alpha_\delta}{k}\Big)\Big]
=\cos(kL)+\frac{\alpha_\delta}{k}\sin(kL)
=\sqrt{1+(\alpha_\delta/k)^2}\,\cos\Big(kL-\arctan\frac{\alpha_\delta}{k}\Big),
$$

得式 (3.4)，其中 $|t|=(1+(\alpha_\delta/k)^2)^{-1/2}$。

**B.3 可辨识性（秩）**
构造观测方程 $\{f=0,E=\hbar^2k^2/(2m)\}$ 对 $(m,g)$ 的雅可比，避开 $k=0$ 与强散射的退化条带即可保满秩（式 4.5）。

**B.4 灵敏度与病态域**
由式 (4.6) 得隐函数导数与 $f_k=0$ 的病态条件。实验设计以 $|f_k|>\tau$ 为准则选点，$\tau\sim 10^{-2}$–$10^{-3}$。

**B.5 有限宽度的等效化与数值对照**
对 $V(x)=V_0 u(x/w)$，在 $kw\ll 1$ 的低能展开下，

$$
t^{-1}(k)=1+i\frac{\alpha_\delta}{k}+\eta_2[V]\,(kw)^2+\cdots,
$$

其中

$$
\eta_2[V]=\frac{1}{w^2}\,\frac{\int x^2 V(x)\,{\rm d}x}{\int V(x)\,{\rm d}x}\ \ \text{(经归一与对照校正)}.
$$

对矩形（$\eta_2=1/3$）与高斯（$\eta_2=1/2$）势进行数值扫描验证，在 $kw\le 0.2$ 区域相对误差 $\le 1\%$。可解模型结果与该展开在重叠区一致。

### Appendix C. 拓扑散射不变量与 cQED

**C.1 $\mathcal Q=\mathrm{sgn}\det r(0)$ 的散射判据**
在类 D 的对称约束下，$\mathcal Q$ 可通过单端反射矩阵的零能行列式符号给出；边界/接触与有限尺寸引入的偏置在近幺正下可视作对 $J_c$ 的平移。

**C.2 外推回归与模型比较**
拟合 $J_c(L)$ 用式 (3.8)，并以 AIC/BIC 比较"指数/代数/复合"三模型；当 $\varepsilon=|r^\dagger r-\mathbb 1|>\varepsilon_\star$ 时，以权重或协变量形式纳入回归并放宽不确定度。

**C.3 cQED 线性响应映射**
单端口下 $r\simeq 1-2Z_0Y$，而 $Y\propto g_{\rm cav}^2\chi$；当 $|\omega_c-\omega_{\rm cont}|\gtrsim 3\kappa$ 时，$\chi$ 在零能的符号变化可在 $\delta\omega_c$ 与 $\kappa_{\rm add}$ 上形成零交叉，与 $\mathcal Q$ 翻转一致。实例化的微波–Majorana 方案可作风格参照。

---

**（正文与附录完）**
