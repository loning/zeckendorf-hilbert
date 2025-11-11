# 自指散射网络：联络矩阵综合、$J$‑幺正稳健性与 Floquet 带缘拓扑

Version 1.7

## 摘要

本文在自指散射网络（Self‑Referential Scattering Networks, SSN）中，给出一套从**设计—实现—读出—证伪**到**定理化保障**的闭环方法学。在**迹类口径**下，将整体半相位（$\sqrt{\det}$ 覆盖）的 holonomy 与谱位移、过 $-1$ 的谱流、判别子横截建立**模二等价**。相较前稿，本版在五个关键环节补齐**可核查细节与可检常数**：（i）第 3 节新增"$\log\det$ 正则化—Birman–Kreĭn—$-1$ 谱流—模二交数"的**桥接引理**与半页级**自足证明**；（ii）第 4 节给出星乘后"**无伪交**"的**定量结构引理**，明确主块最小梯度 $g_{\min}$ 与互耦上界 $r_{\max}$ 的**比较原则**与**设计线**；（iii）第 5 节把**二值化投影＋多数投票**写成**集中不等式**，给出误判率与样本数的显式关系，并附**相关性修正**；（iv）第 6 节用 $J$‑内积归一化的**虚部 Rayleigh 商（Kreĭn 角）**刻画稳健域，构造**极化同伦**并给出阈值函数 $\varepsilon_0(\eta)$ 的可行上界；（v）第 7 节把**相位型 Floquet 指标**的**截断独立**与**规范独立**写成定理，**并在 Hilbert–Schmidt 场景下以 $\det_2$ 完成**正则化一致性**与**失败检测**。工程侧以两端口"耦合器—微环—增益"原型给出可仿真的 Schur‑闭合式，量化群延迟"双峰并合"的平方根标度与阈值选取依据。

**关键词**：闭环散射；Redheffer 星乘；Schur 补；Herglotz/Nevanlinna；判别子；谱位移与谱流；模二 Levinson；$J$‑幺正；Kreĭn 角；Floquet 相位型指标。

---

## 1 口径与基本对象

**频域与变量**：$\omega$ 为角频率（静态 $\omega\in\mathbb{R}$；周期系统 $\omega\in[-\pi/T,\pi/T]$），上半平面口径取 $z=\omega+\mathrm{i}0^+$。必要处与单位圆口径经 Cayley 映射互换，取向保持一致。

**散射与星乘**：端口化节点散射 $S_j(z)$ 经互联（含反馈）由 Redheffer 星乘与 Schur 补得到闭环 $S^{\circlearrowleft}(z)$。

**Cayley 对偶**（统一记号）：

$$
S^{\circlearrowleft}(z)=(I-\mathrm{i}K(z))(I+\mathrm{i}K(z))^{-1},\qquad
K(z)=-\mathrm{i}\bigl(I+S^{\circlearrowleft}(z)\bigr)^{-1}\bigl(I-S^{\circlearrowleft}(z)\bigr).
$$

**迹类与正则化**：凡与谱位移 $\xi$ 和 Birman–Kreĭn 相关的结果，统一假设 $S^{\circlearrowleft}-I\in\mathfrak{S}_1$ 并使用 $\det$。无限维（如 Floquet 侧带）先做有限截断，必要时用 $\det_2$；本文**模二结论与 $\det/\det_2$ 的选择无关**（见附录 F）。

**$J$‑幺正口径**：$J=J^\dagger=J^{-1}$，$S^\sharp=J^{-1}S^\dagger J$、$S^\dagger J S=J$。非厄米稳健性均在此口径下陈述。

---

## 2 判别子、局部模型与横截

在参数流形 $X$ 上定义余维一的分片光滑子流形族 $D=\bigsqcup_b D_b$，其局部模型包括 Jost 零点、阈值开闭、嵌入本征值与 EP 并合。去除后 $X^\circ=X\setminus D$。对闭路 $\gamma\subset X^\circ$，模二交数 $I_2(\gamma,D)$ 为横截点数奇偶。端点/阈值以小半圆切除并入 $D$ 的边界分量。闭环实现层面可用

$$
D=\Bigl\{(\omega,\vartheta):\ \sigma_{\min}\bigl(I-\mathcal{C}(\omega,\vartheta)\,S_{ii}(\omega,\vartheta)\bigr)=0\Bigr\},
$$

在一般位置时与 $\det(I-\mathcal{C}S_{ii})=0$ 等价。

---

## 3 模二半相位—谱位移—谱流—交数：桥接引理与等价定理（迹类）

**定义 3.1（整体半相位）**：

$$
\nu_{\sqrt{\det S^{\circlearrowleft}}}(\gamma)
=\exp\Bigl(\mathrm{i}\oint_{\gamma}\tfrac12\,\mathrm{d}\arg\det S^{\circlearrowleft}\Bigr)\in\{\pm1\}.
$$

**引理 3.2（$\log\det$ 正则化与端点处理）**
若沿闭路 $\gamma$ 几乎处处 $S^{\circlearrowleft}$ 幺正且 $S^{\circlearrowleft}-I\in\mathfrak{S}_1$，则 $\log\det S^{\circlearrowleft}$ 可沿 $\gamma$ 连续延拓并可积；按 §2 的小半圆切除规则处理端点/阈值后，$\oint_\gamma \tfrac12\,\mathrm{d}\arg\det S^{\circlearrowleft}$ 良定（$\bmod\ 2\pi$）。

**引理 3.3（Birman–Kreĭn—$-1$ 谱流桥梁：两步可核查细节）**
记 $\xi(\omega)$ 为谱位移。则
(i) 由 BK 公式 $\det S(\omega)=\exp\{-2\pi\mathrm{i}\,\xi(\omega)\}$，任意分支更换使 $\xi\mapsto\xi+n$（$n\in\mathbb{Z}$），对半相位的贡献为 $\exp\{\mathrm{i}\oint \tfrac12\,\mathrm{d}(2\pi n)\}=1$，故**模二不变**；
(ii) 令 $S(\tau)=V(\tau)\,e^{\mathrm{i}\Phi(\tau)}\,U(\tau)$ 为局部 Schur 形且在 $\tau=\tau_c$ 仅有一一重本征相位 $\phi_j$ 横越 $\pi$（$-1$），则 $\xi$ 的跃迁为 $\pm 1$ 而 $\mathrm{Sf}_{-1}=1$。多重横越分解为有限次单横越叠加，故

$$
\exp\Bigl(-\mathrm{i}\pi\oint_\gamma \mathrm{d}\xi\Bigr)=(-1)^{\mathrm{Sf}_{-1}(S^{\circlearrowleft}\circ\gamma)}.
$$

**命题 3.4（基点与分支独立的模二性）**
对任意基点与连续分支延拓，$\nu_{\sqrt{\det S^{\circlearrowleft}}}(\gamma)$ 不变；允许的端点处理等同于在 $D$ 上添加边界同伦，模二值保持。

**定理 3.5（四重等价）**
若沿 $\gamma$ 几乎处处 $S^{\circlearrowleft}$ 幺正且 $S^{\circlearrowleft}-I\in\mathfrak{S}_1$，则

$$
\nu_{\sqrt{\det S^{\circlearrowleft}}}(\gamma)
=\exp\Bigl(-\mathrm{i}\pi\oint_\gamma \mathrm{d}\xi\Bigr)
=(-1)^{\mathrm{Sf}_{-1}\bigl(S^{\circlearrowleft}\circ\gamma\bigr)}
=(-1)^{I_2(\gamma,D)}.
$$

---

## 4 星乘后的"无伪交"与 $\mathbb{Z}_2$ 组合律（定量版）

**分块记号**：

$$
S^{(k)}=\begin{pmatrix}
S^{(k)}_{ee} & S^{(k)}_{ei}\\[2pt]
S^{(k)}_{ie} & S^{(k)}_{ii}
\end{pmatrix},\quad k=1,2.
$$

**结构引理 4.1（无伪交：定量条件）**
设在邻域 $U\subset X^\circ$ 内满足
(i) Schur 可逆下界：$\sigma_{\min}\bigl(I-S^{(1)}_{ii}S^{(2)}_{ii}\bigr)\ge \delta>0$；
(ii) 互耦小量：$\|S^{(1)}_{ei}\|_2,\|S^{(2)}_{ie}\|_2\le \rho<1$。
定义主判别式 $\Phi_k(\vartheta)=\det\bigl(I-\mathcal{C}S^{(k)}_{ii}\bigr)$ 与主块最小梯度

$$
g_{\min}=\inf_{\vartheta\in U}\min\bigl\{\,|\nabla_\vartheta \Phi_1(\vartheta)|,\ |\nabla_\vartheta \Phi_2(\vartheta)|\,\bigr\}.
$$

则存在互耦残差上界

$$
r_{\max}\ \le\ \frac{\|S^{(1)}_{ei}\|_2\,\|S^{(2)}_{ie}\|_2}{\delta^2},
$$

且当 $r_{\max}<g_{\min}$ 时，网络判别子为子网判别子的横离并：$D_{\mathrm{net}}=D_{(1)}\sqcup D_{(2)}$，并有

$$
I_2(\gamma,D_{\mathrm{net}})=I_2(\gamma,D_{(1)})+I_2(\gamma,D_{(2)})\ \bmod 2.
$$

*证明要点*：将闭环判别式写成主块乘积与互耦 Neumann 余项的乘法分解；由 $\delta$ 控制分母、由 2‑范数控制互耦级数与梯度扰动，比较 $r_{\max}$ 与 $g_{\min}$ 得横离并。

**工程设计线（可检）**
取 $\delta=\inf_{U}\sigma_{\min}(I-S^{(1)}_{ii}S^{(2)}_{ii})$。若

$$
\|S^{(1)}_{ei}\|_2\,\|S^{(2)}_{ie}\|_2\ \le\ \tfrac12\,\delta^2\,g_{\min},
$$

则

$$
r_{\max}\ \le\ \frac{\|S^{(1)}_{ei}\|_2\,\|S^{(2)}_{ie}\|_2}{\delta^2}\ \le\ \tfrac12\,g_{\min}\ <\ g_{\min},
$$

因而满足引理 4.1 的前提 $r_{\max}<g_{\min}$；网络判别子为子网判别子的横离并，横截奇偶由主块决定。

**边界与失败模式 4.2**：当 $\delta\to 0^+$ 或 $\rho\to 1^-$ 时，可能出现近切交与共振‑诱发的"伪交"。应实时监测 $\sigma_{\min}(I-\mathcal{C}S_{ii})$ 的裕度与 $g_{\min}$ 的数值估计，必要时缩小 $U$ 或重配端口。

**定理 4.3（$\mathbb{Z}_2$ 组合律）**
在引理条件下，$\boldsymbol{\nu}_{\mathrm{net}}=\boldsymbol{\nu}_{(1)}\odot\boldsymbol{\nu}_{(2)}$（分量乘，模二加法）。

---

## 5 二值化投影、集中不等式与去混叠

**相位增量与二值化**：

$$
\Delta\phi_{ab}=\frac12\Bigl[\arg\det S\bigl(\gamma_a;\theta_b+\delta\bigr)-\arg\det S\bigl(\gamma_a;\theta_b-\delta\bigr)\Bigr]_{\mathrm{cont}},\qquad
\Pi(\Delta\phi_{ab})=\mathbf{1}_{\{|\Delta\phi_{ab}|\ge \pi/2\}}.
$$

**定义（有效相位窗）** 设实验/仿真使用的测量网格为 $\mathcal{G}=\{(a,b)\}$，并按上式定义 $\Delta\phi_{ab}$ 与二值化规则 $\Pi(\cdot)$。定义

$$
\Delta\phi_{\mathrm{eff}}:=\operatorname*{ess\,inf}_{(a,b)\in\mathcal{G}}\,|\Delta\phi_{ab}|.
$$

当存在有界加性噪声 $\varepsilon$ 且 $|\varepsilon|\le \epsilon$ 时，采用门限条件 $\Delta\phi_{\mathrm{eff}}>\frac{\pi}{2}+2\epsilon$；据此得到定理 5.1 的误判率与样本复杂度估计。

**假设（独立与次高斯）**
测量样本 $\{\widehat{\Delta\phi}_{ab}^{(n)}\}_{n=1}^N$ 独立，$\mathbb{E}\,\widehat{\Delta\phi}_{ab}^{(n)}=\Delta\phi_{ab}$，且为次高斯，代理方差 $\sigma^2$。

**定理 5.1（多数投票的误差界与样本复杂度）**
若有界噪声 $|\varepsilon|\le \epsilon$，有效相位窗满足 $\Delta\phi_{\mathrm{eff}}>\pi/2+2\epsilon$。则对 $N$ 次独立采样与多数投票，

$$
\mathbb{P}(\text{误判})\ \le\ \exp\Bigl(-2N\,\Bigl(\tfrac{\Delta\phi_{\mathrm{eff}}-\pi/2-2\epsilon}{\pi}\Bigr)^2\Bigr),
$$

给定目标误差 $\delta$，取

$$
N\ \ge\ \frac{1}{2}\Bigl(\frac{\pi}{\Delta\phi_{\mathrm{eff}}-\pi/2-2\epsilon}\Bigr)^2\log\frac{1}{\delta}
$$

即可。若存在过采样相关性，以上式中 $N$ 替换为有效样本数 $N_{\mathrm{eff}}$。

**命题 5.2（去混叠与二级证据融合）**
多重穿越或近阈值掩蔽时：
(i) 采用多窗滑动与锚点连续化策略；
(ii) 融合群延迟双峰并合，仅当两指纹同步时确认"有交"；
(iii) 出现串扰时，增添与既有灵敏度近正交的冗余列并重算 Gram 判据直至满秩。

---

## 6 $J$‑幺正稳健性：Kreĭn 角、极化同伦与阈值函数

**Kreĭn 角（$J$‑内积、取虚部口径）**：**假定 $\langle\psi_j(\tau),J\psi_j(\tau)\rangle\neq0$（非中性本征态），否则 $\varkappa_j$ 不定义，且该参数点视为稳健域边界并予以排除。** 对 $(e^{\mathrm{i}\phi_j(\tau)},\psi_j(\tau))$ 定义

$$
\varkappa_j(\tau)=\frac{\operatorname{Im}\,\langle \psi_j(\tau)\,,J\,S^{-1}(\partial_\tau S)\,\psi_j(\tau)\rangle}{\langle \psi_j(\tau)\,,J\,\psi_j(\tau)\rangle},\qquad
\eta=\min_{j:\ \langle\psi_j,J\psi_j\rangle\neq0}\ \inf_\tau |\varkappa_j(\tau)|.
$$

幺正极限 $J=I$ 时 $\varkappa_j=\partial_\tau\phi_j$。近 $J$‑幺正下存在 $c_\pm(\varepsilon)\to1$ 使 $c_{-}\,|\partial_\tau\phi_j|\le |\varkappa_j|\le c_{+}\,|\partial_\tau\phi_j|$。

**小引理 6.1（$(S^\dagger J S-J)$ 到 $(K-K^\sharp)$ 的估计）**
设 $\|S^\dagger J S-J\|\le \varepsilon$ 且 $\beta=\inf_\tau\sigma_{\min}(I+\mathrm{i}K(\tau))>0$。则存在常数 $C=C(\beta,\|S\|,\|S^{-1}\|)$ 使

$$
\|K-K^\sharp\|\ \le\ C\,\varepsilon.
$$

*证要*：用 Cayley 逆映射 $K=-\mathrm{i}(I+S)^{-1}(I-S)$ 的 Fréchet 微分并配合 $J$‑共轭与有界乘子不等式。

**构造 6.2（极化同伦）**
令

$$
K_t=(1-t)\,K+t\,\tfrac12(K+K^\sharp),\qquad
S_t=(I-\mathrm{i}K_t)(I+\mathrm{i}K_t)^{-1},\quad t\in[0,1].
$$

则 $S_0=S$、$S_1$ 为 $J$‑幺正。若 $\|S^\dagger J S-J\|\le \varepsilon$ 与 $\eta>0$，由引理 6.1 与本征相位扰动估计，存在常数 $\alpha>0$（依赖 $\|S\|$、$\|S^{-1}\|$、$\beta$）使当

$$
\varepsilon\ <\ \varepsilon_0(\eta):=\alpha\,\sin^2\!\tfrac{\eta}{2}
$$

时，整条同伦不穿越 $D$。

**定理 6.3（同伦稳健性）**
若存在满足上式的同伦 $\{S_t\}$ 且过程中不与 $D$ 相交，则 $\nu_{\sqrt{\det S^{\circlearrowleft}}}$ 与幺正极限同值。

**平方根渐近（工程指纹）**：主导支化的 $2\times2$ 有效子空间给出

$$
\arg\det S(t)=\arg\det S(t_c)\pm \arctan\bigl(\kappa^{1/2}|t-t_c|^{1/2}\bigr)+O\bigl(|t-t_c|^{3/2}\bigr),
$$

群延迟呈对称双峰并合，峰距 $\Delta\omega=C\sqrt{|t-t_c|}+O\bigl(|t-t_c|^{3/2}\bigr)$。高阶根（EP 阶数 $>2$）在模二上与平方根同类。

---

## 7 Floquet‑SSN：相位型带缘指标、截断与规范独立

**定义 7.1（相位型指标）**：侧带截断至 $|n|\le N$ 得有限维 $S_F^{(N)}(\omega)$，定义

$$
\nu_F^{(N)}=\exp\Bigl(\frac{\mathrm{i}}{2}\int_{-\pi/T}^{\pi/T}\partial_\omega\arg\det S_F^{(N)}(\omega)\,\mathrm{d}\omega\Bigr)\in\{\pm1\}.
$$

等价地，

$$
\nu_F^{(N)}=\exp\Bigl(\frac{\mathrm{i}}{2}\int_{-\pi/T}^{\pi/T}\operatorname{Im}\,\partial_\omega\log\det S_F^{(N)}(\omega)\,\mathrm{d}\omega\Bigr).
$$

**定理 7.2（截断独立：范数/HS 版本）**
若 $S_F^{(N)}\to S_F$ 于算子范数或 Hilbert–Schmidt 拓扑，且端点 $\omega=\pm\pi/T$ 无随 $N$ 迁移的支化，则存在 $N_\ast$ 使 $N\ge N_\ast$ 时 $\nu_F^{(N)}$ 稳定；定义 $\nu_F=\nu_F^{(N_\ast)}$。在 **Hilbert–Schmidt 场景**，用 Koplienko 谱位移与 $\det_2$ 的导数配方替换 $\det$ 的微分，结合附录 F 的模二一致性，得到相同的 $\nu_F$。**仅有强收敛不足以保证 $\det_2$ 与二阶迹公式的良定，因此不纳入本定理的前提。**

**引理 7.3（规范独立性）**
若 $S_F(\omega)\mapsto U_L(\omega)\,S_F(\omega)\,U_R(\omega)$，其中 $U_{L,R}$ 连续、$|\det U_{L,R}|=1$，并满足带缘粘合条件

$$
[\arg\det U_L+\arg\det U_R]_{-\pi/T}^{\pi/T}\in 4\pi\mathbb{Z},
$$

则

$$
\int_{-\pi/T}^{\pi/T}\partial_\omega\arg\det S_F(\omega)\,\mathrm{d}\omega
$$

的模二值不变。

**定理 7.4（带缘等价）**
若端点处满足平方根局部模型且定理 7.2 成立，则

$$
\nu_F=(-1)^{I_2\bigl([-\pi/T,\pi/T],D_F\bigr)}.
$$

**失败模式 7.5（探测与容错阈值）**
截断诱发端点伪支化时，监测

$$
\min_{\omega\in\{\pm\pi/T\}}\sigma_{\min}\!\bigl(I-\mathcal{C}S_{ii}^{(N)}(\omega)\bigr)\ \ge\ \delta_F,
$$

并要求 $\nu_F^{(N)}=\nu_F^{(N+1)}=\nu_F^{(N+2)}$ 连续三阶一致，方判定"稳定"。

---

## 8 原型与 SOP

**8.1 单次穿越的两类等价路径**：
(i) 复参数小环：$\lambda$ 在复平面绕 Jost 零点一次；
(ii) 实参横越 + 频域读出：实参沿横截 $D$ 前后，在频域选取单支并用锚点连续化。两者同伦等价。沿任一由复参数小环或"实参横越 + 回程闭合"得到的**闭合回路**，有

$$
\oint \mathrm{d}\arg\det S=\pm 2\pi,\qquad
\exp\Bigl(\tfrac{\mathrm{i}}{2}\oint \mathrm{d}\arg\det S\Bigr)=-1,
$$

与 §3 的半相位—谱流奇偶完全一致。

**8.2 两端口"耦合器—微环—增益"原型（可仿真）**：
耦合器

$$
C(\kappa)=
\begin{pmatrix}
\sqrt{1-\kappa^2} & \mathrm{i}\kappa\\
\mathrm{i}\kappa & \sqrt{1-\kappa^2}
\end{pmatrix},\qquad
\mathcal{C}(\omega,t)=\rho\,\mathrm{e}^{\mathrm{i}\phi(\omega,t)}.
$$

等效散射（Schur‑闭合）

$$
S^{\circlearrowleft}=S_{ee}+S_{ei}\bigl(I-\mathcal{C}\,S_{ii}\bigr)^{-1}\mathcal{C}\,S_{ie}.
$$

在 $\mathcal{C}\,S_{ii}\to I$ 的临界邻域回落到 §8.1 的平方根模型，可直接重现 $\Delta\varphi=\pi$ 与群延迟双峰并合。

**8.3 SOP 与判据**：端口去嵌→扫反馈跨越 $D$→以 $\Delta\phi_{\mathrm{eff}}>\pi/2+2\epsilon$ 与双峰并合作为通过条件；三重指纹不同步即否决因果链，回到列可控性流程做冗余增列或重选频窗。

---

## 9 读出学与 Wigner–Smith 统一口径

$$
\partial_\omega \log\det S=\mathrm{tr}\bigl(S^{-1}\partial_\omega S\bigr),\qquad
\partial_\omega \arg\det S=\operatorname{Im}\,\mathrm{tr}\bigl(S^{-1}\partial_\omega S\bigr).
$$

幺正情形设 $Q(\omega)=-\mathrm{i}\,S^\dagger\partial_\omega S$，则 $\partial_\omega \arg\det S=\mathrm{tr}\,Q(\omega)$。在 $J$‑幺正情形亦可写为 $\partial_\omega \arg\det S=\operatorname{Im}\,\mathrm{tr}(S^\sharp\partial_\omega S)$。

---

## 10 结论

本文以**桥接引理**严密化"半相位—谱位移—谱流—交数"的四重等价；以**定量结构引理**确保星乘互联的判别子横离并与 $\mathbb{Z}_2$ 组合律；以**集中不等式**保障二值化投影的可复核性；以**Kreĭn 角与极化同伦**刻画近 $J$‑幺正的稳健域与阈值；以**相位型 Floquet 指标**与**截断/规范独立定理**闭合带缘拓扑读出链路。配合最小原型与 SOP，给出"闭环自洽 $\Rightarrow$ 平方根临界 $\Rightarrow$ 双层黎曼面 $\Rightarrow \mathbb{Z}_2$ 半相位"的可编程实现与反事实检验。

---

## 参考文献（择要）

[1] R. Redheffer, "On a Certain Linear Fractional Transformation," *Pacific J. Math.*, **9** (1959) 871–893.
[2] J. Gough, M. R. James, "The Series Product and Its Application to Quantum Feedforward and Feedback Networks," *IEEE TAC*, **54** (2009) 2530–2544.
[3] B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005).
[4] M. Sh. Birman, M. G. Kreĭn, "On the Theory of Wave and Scattering Operators," *Sov. Math. Dokl.*, **3** (1962) 740–744.
[5] L. Koplienko, "Trace Formula for Perturbations of Class $\mathfrak{S}_2$," *Sb. Math.*, **122** (1983) 457–486.
[6] E. P. Wigner, "Lower Limit for the Energy Derivative of the Scattering Phase Shift," *Phys. Rev.*, **98** (1955) 145–147；F. T. Smith, "Lifetime Matrix in Collision Theory," *Phys. Rev.*, **118** (1960) 349–356.
[7] T. Ya. Azizov, I. S. Iokhvidov, *Linear Operators in Spaces with an Indefinite Metric*, Wiley (1989).
[8] D. Z. Arov, H. Dym, *$J$‑Contractive Matrix‑Valued Functions and Related Topics*, CUP (2008).
[9] I. C. Fulga, F. Hassler, A. R. Akhmerov, "Scattering Formula for the Topological Quantum Number," *Phys. Rev. B*, **85** (2012) 165409.
[10] M. S. Rudner, N. H. Lindner, E. Berg, M. Levin, "Anomalous Edge States…," *Phys. Rev. X*, **3** (2013) 031005.

---

## 附录 A  记号与正则化

**记号**：$J$（Kreĭn 度量），$S^\sharp=J^{-1}S^\dagger J$；$\mathfrak{S}_1/\mathfrak{S}_2$（迹类/HS）；$\det_\star$（有限维取 $\det$，HS 取 $\det_2$）；$D,D_F$（判别子/带缘判别子）；$\Lambda$、$\Pi_\tau$、$\eta$、$Q=-\mathrm{i}S^\dagger\partial_\omega S$、$\nu_{\sqrt{\det S^{\circlearrowleft}}}$、$\nu_F$。
**口径**：主文采用 $\mathfrak{S}_1$。HS 情形以 $\det_2$ 稳定化；四重等价与 $\nu_F$ 的模二值与 $\det/\det_2$ 的选择无关（见附录 F）。

---

## 附录 B  覆盖—提升与 $\mathbb{Z}_2$ 约化

平方覆盖 $p:z\mapsto z^2$ 在上同调中对应乘二：存在 $s:X^\circ\to U(1)$ 使 $s^2=\det S^{\circlearrowleft}$ 当且仅当 $[\det S^{\circlearrowleft}]\in 2H^1(X^\circ;\mathbb{Z})$。其 $\mathbb{Z}_2$ 约化即本文整体半相位不变量。

---

## 附录 C  平方根 Puiseux 渐近与误差

对 $2\times2$ 有效子块 $M(t)$ 与 $\Delta(t)\approx \Delta'(t_c)(t-t_c)$，Cayley 映到 $S(t)=(I-\mathrm{i}M)(I+\mathrm{i}M)^{-1}$ 后主导项为

$$
\pm\,\arctan\bigl(\kappa^{1/2}|t-t_c|^{1/2}\bigr)+O\bigl(|t-t_c|^{3/2}\bigr),
$$

群延迟呈对称双峰并合，峰距 $\Delta\omega=C\sqrt{|t-t_c|}+O\bigl(|t-t_c|^{3/2}\bigr)$。代入 §5 的 $\Delta\phi_{\mathrm{eff}}$ 即得样本复杂度估计。

---

## 附录 D  目标—到—器件执行清单与 $\ell$

开环标定与去嵌→选 $W$ 与步长→计算 $\mathcal{S}_{\theta_b}(\omega)=\partial_{\theta_b}\arg\det S(\omega)$ 并积成 $M$→以 $\pi/2\pm\tau$ 得 $\Pi(M)$ 并检秩→解 $\Pi(M)\mathbf{x}=\ell$ 选列→逐列触发并以 $\Delta\varphi=\pi$、双峰并合作停止→反事实复核与归档。
$\ell=(1-\boldsymbol{\nu}^\star)/2\in\{0,1\}^m$（$\nu^\star=+1\mapsto0,\ \nu^\star=-1\mapsto1$）。

---

## 附录 E  $J$‑幺正下的 Kreĭn 角与同伦阈值

设 $S^\dagger J S=J$，记 $X=S^{-1}\dot S$。由微分得 $X^\sharp=-X$（$J$‑斜厄米）。对 $(\lambda_j=\mathrm{e}^{\mathrm{i}\theta_j},v_j)$：

$$
\dot{\theta}_j=\frac{\operatorname{Im}\,\langle v_j\,,JX\,v_j\rangle}{v_j^\dagger J v_j},\qquad
\varkappa_j=\frac{\operatorname{Im}\,\langle v_j\,,JX\,v_j\rangle}{v_j^\dagger J v_j}.
$$

由上两式逐点可得 $\varkappa_j=\dot{\theta}_j$，因而

$$
|\dot{\theta}_1-\dot{\theta}_2|=|\varkappa_1-\varkappa_2|.
$$

以引理 6.1 得 $\|K-K^\sharp\|\le C\,\varepsilon$。取 $K_t=(1-t)K+t(K+K^\sharp)/2$，$S_t=(I-\mathrm{i}K_t)(I+\mathrm{i}K_t)^{-1}$。若 $\|S^\dagger J S-J\|\le \varepsilon$ 且 $\eta>0$，存在常数 $\alpha>0$ 使 $\varepsilon_0(\eta)=\alpha\sin^2(\eta/2)$ 为可行上界。

---

## 附录 F  正则化独立性（统一命题）

**命题 F.1**（$\det/\det_2$ 的模二一致性）
设沿闭路 $\gamma$ 几乎处处 $S^{\circlearrowleft}$ 幺正。若 $S^{\circlearrowleft}-I\in\mathfrak{S}_1$ 则

$$
\exp\Bigl(\mathrm{i}\oint_\gamma \tfrac12\,\partial\log\det S^{\circlearrowleft}\Bigr)
=(-1)^{\mathrm{Sf}_{-1}}=(-1)^{I_2}.
$$

若仅 $S^{\circlearrowleft}-I\in\mathfrak{S}_2$，取 $\mathfrak{S}_1$ 近似族 $S_\epsilon^{\circlearrowleft}\to S^{\circlearrowleft}$ 于 HS 拓扑，并以 $\det_2$ 定义半相位，则

$$
\lim_{\epsilon\to0}\exp\Bigl(\mathrm{i}\oint_\gamma \tfrac12\,\partial\log\det S_\epsilon^{\circlearrowleft}\Bigr)
=\exp\Bigl(\mathrm{i}\oint_\gamma \tfrac12\,\partial\log\det_2 S^{\circlearrowleft}\Bigr),
$$

且两边的模二值与 $\mathrm{Sf}_{-1}$、$I_2$ 一致。

---

## 附录 G  Floquet 截断、收敛与失败模式

将 $S_F$ 侧带截断至 $|m|\le M$ 得 $S_F^{(M)}$。若 $\sum_{|m|>M}\|K_m\|\to0$（**算子范数或 HS 收敛；该条件蕴含算子范数收敛**），且端点不出现随 $M$ 迁移的支化，则 $\sup_\omega \|S_F^{(M+1)}-S_F^{(M)}\|\to 0$，存在 $M_0$ 使 $M\ge M_0$ 时 $\nu_F^{(M)}$ 稳定。检测量：端点奇异值阈值 $\delta_F$ 与"台阶稳定"准则（$\nu_F^{(M)}=\nu_F^{(M+1)}=\nu_F^{(M+2)}$）。出现异常漂移时增大 $M$ 或缩小耦合带宽以规避伪支化。
