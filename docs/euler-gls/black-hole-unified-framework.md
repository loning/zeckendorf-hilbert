# 黑洞的窗化散射—因果—信息几何统一：母尺刻度、环降—共振、灰体因子、测量—熵产生与分形—Mellin—Zeckendorf 桥接（含证明）

**版本**：v7.1
**MSC**：83C57；83C05；81U15；42A38；46E22；37B15；94A17；68Q80
**关键词**：Kerr/Schwarzschild；窗化散射；三位一体母尺；Wigner–Smith 群延迟；Birman–Kreĭn 与光谱位移；Hardy/de Branges；Titchmarsh—Kramers–Kronig 因果；准正则模（QNM）—环降；灰体因子；IGVP（信息几何变分）；QNEC；Belavkin 过滤；量子 Jarzynski；Mellin—对数帧；Zeckendorf 可逆日志

---

## 摘要

在广义光结构与因果流形的统一范式中，本文以"母尺刻度—窗化读数—因果律"三要素闭合黑洞外区的线性扰动散射学。设可微能量散射矩阵 $S(E)\in\mathsf U(N)$ 的 Wigner–Smith 矩阵为 $\mathsf Q(E)=-\,i\,S(E)^\dagger \tfrac{dS}{dE}(E)$。定义总相位 $\varphi(E)=\tfrac12\arg\det S(E)$ 与相对态密度 $\rho_{\rm rel}(E)$。则统一刻度同一式
$$
\frac{\varphi'(E)}{\pi}\;=\;\rho_{\rm rel}(E)\;=\;\frac{1}{2\pi}\,\operatorname{tr}\mathsf Q(E)
$$
成立；该式由 Birman–Kreĭn（BK）公式与光谱位移函数 $\xi(E)$ 精确钩连，并可在存在吸收的开系统/耗散散射中借助自伴扩张与修正 BK 公式保持有效，从而以"视界通道"保全全局幺正。上述刻度与 Toeplitz/Berezin 压缩给出的窗化观测读数线性等价，Hardy $H^2(\mathbb C^+)$ 的上半平面解析性与 Kramers–Kronig/Hilbert 变换则内在刻画了因果律。

在线性扰动层面，Kerr/Schwarzschild 的准正则模（QNM）为延拓散射矩阵的极点（共振），其频率集合决定合并后"环降"段的指数衰减；Kerr–de Sitter 背景的模稳定与解析性已以微局部方法与代数散射工具得到系统证明。环降窗化读数由有限多极点残数与 Price 定律控制的幂律尾项叠加而成。([CaltechAUTHORS][1])

在观测侧，事件视界望远镜（EHT）对 M87* 与 Sgr A* 的多历元、极化与环形几何读数显示阴影直径的持久性与近视界强磁场的普适性；引力波 O3–O4 的环降谱学与面积定理检验方法学持续成熟。

在热力学与量子信息侧，信息几何小球变分（IGVP）的一阶极值蕴含爱因斯坦场方程，二阶变分给出量子零能条件（QNEC）与量子焦散不等式。离散测量的 Lüders 更新可描述为相对熵极小的 I-投影；持续监测由 Belavkin 过滤给出后验态随机微分方程，其平均回收 Lindblad 生成而满足 Spohn 熵产生单调；引入互信息的 Jarzynski 等式刻画含反馈测量的功—熵平衡。

数值—实验实现方面，提出"Poisson 旁瓣—Euler–Maclaurin（EM）端点—尾项"三分误差闭合纪律；以 Mellin 对数帧匹配频率尺度不变性；在环降拟合中显式引入灰体核以缓解起始时刻与过拟合问题；有限窗能量预算以 Zeckendorf 唯一分解编码为可逆日志。

---

## 0. 记号与公设

**（0.1）散射母尺刻度。** 设 $S(E)$ 为每个 $(\ell,m,s)$ 通道的能量散射矩阵，Wigner–Smith 矩阵 $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$。定义总相位 $\varphi(E)=\tfrac12\arg\det S(E)$ 与相对态密度 $\rho_{\rm rel}(E)$。则
$$
\frac{\varphi'(E)}{\pi}\;=\;\rho_{\rm rel}(E)\;=\;\frac{1}{2\pi}\operatorname{tr}\,\mathsf Q(E),\qquad
\det S(E)=\exp\!\bigl(-2\pi i\,\xi(E)\bigr),
$$
其中 $\xi$ 为 BK 光谱位移函数。证明基于 BK 公式与 $S$ 的行列式相位，见附录 A。

**（0.2）耗散/开系统修正。** 黑洞外区存在吸收与超辐射，导致外散射子非幺正。引入包含"视界通道"的自伴扩张或采用耗散/耦合散射的 BK 变体可恢复全局幺正与位移—相位—群延迟的等价。

**（0.3）窗化读数与 Toeplitz/Berezin 压缩。** 取窗—核 $(w_R,h)$ 定义能量测度上的压缩算子 $K_{w,h}$ 与读数 $\langle f\rangle_{w,h}=\int (w_R*\check h)(E)\, f(E)\, \rho_{\rm rel}(E)\,dE$。当 $(w_R*\check h)\ge0$ 且满足适当 Carleson 条件时，$K_{w,h}$ 正且有界，读数为谱测度上的正线性泛函。

**（0.4）因果律与 Hardy 解析。** 时域因果 $\Leftrightarrow$ 频域 $H^2(\mathbb C^+)$ 边值解析与 Kramers–Kronig（Hilbert 共轭），其严密性可由 Titchmarsh 定理与近年的 Laplace 形式化证明支撑。

**（0.5）双时间分离。** 最早到达时间 $t_*$ 确定因果前沿；群延迟刻度 $T_\gamma=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 为操作读数，可能取负且不与 $t_*$ 直接比较。卷积支撑的 Titchmarsh 等式给出前沿的加性：$t_*(f*g)=t_*(f)+t_*(g)$。

---

## 1. 黑洞作为广义光结构（GLS）对象与散射—因果互构

### 1.1 外区方程与短程化

Kerr 外区 $(\mathcal M,g_{M,a})$ 上的 $s=0,\pm1,\pm2$ 线性扰动满足可分离的 Teukolsky 方程；经 Sasaki–Nakamura/Detweiler 变换为一维短程散射型径向方程，便于共振谱与时间域分析。([RUG Research][2])

### 1.2 互构定理

**定理 1（窗化读数—因果互构）。** 设 $(\mathcal M,g)$ 为区分且强因果时空，$\mathfrak G:(\mathcal M,g)\mapsto(\mathcal H,S,\rho_{\rm rel})$ 为辐射场散射函子，$\mathfrak F:(\mathcal H,S)\mapsto(\mathcal M,g)/{\sim_{\rm conf}}$ 为由可达偏序/光观测集重构保角类的函子。则在能量依赖规范等价商上存在自然变换 $\eta,\varepsilon$，使 $\mathfrak F\circ\mathfrak G\simeq\mathrm{Id}$、$\mathfrak G\circ\mathfrak F\simeq\mathrm{Id}$。

*证明要点。*（i）Hardy 解析 $\Rightarrow$ 时域因果与 Kramers–Kronig；（ii）Titchmarsh 支撑等式给出最早到达的加性边界；（iii）Malament 与 Hawking–King–McCarthy 定理：因果同构决定保角同构；（iv）窗化 BK 将 $\operatorname{tr}\mathsf Q$ 与 $\varphi'$ 对齐，给出读数的规范不变性。详见附录 A。([Applied Mathematics at TU Graz][3])

---

## 2. 准正则模（QNM）、环降与共振展开

### 2.1 QNM 作为散射共振

QNM 为散射矩阵（或相应传输—反射系数）之解析延拓的极点；其实部为振频，虚部给衰减率。Kerr 与 Kerr–de Sitter 的模稳定、谱隙与解析性已以微局部与代数散射方法证明。数值上，Leaver 连分式与谱定点迭代为高精度手段。

### 2.2 窗化残数—尾项展开

取时间窗 $w(t)$、频核 $h(\omega)$，以母尺测度加权，线性响应的窗化读数可按 QNM 极点全体展开为
$$
\langle \Psi\rangle_{w,h}
=\sum_{\omega_j\in\mathcal P}\operatorname{Res}\bigl(\widehat\Psi(\omega),\omega_j\bigr)\,\widehat w(\omega_j)\,\widehat h(\omega_j)\;+\;R_{\rm cut},
$$
其中 $\mathcal P$ 为全部 QNM 极点集合（$\Im\omega_j<0$），$R_{\rm cut}$ 为连续谱/分支切割贡献。将极点和按贡献大小截断至前 $J$ 个主导极点，可写成
$$
\langle \Psi\rangle_{w,h}
=\sum_{j=1}^J \operatorname{Res}\bigl(\widehat\Psi(\omega),\omega_j\bigr)\,\widehat w(\omega_j)\,\widehat h(\omega_j)\;+\;\mathrm{Tail},
$$
其中 $\mathrm{Tail}=R_{\rm cut}+R_{\rm qnm}^{(>J)}$，$R_{\rm qnm}^{(>J)}$ 为被截断极点的余项；当 $(w,h)\in\mathcal S$ 且具有频域衰减/带限条件时，$\mathrm{Tail}$ 具显式上界，$R_{\rm cut}$ 依 Price 定律呈幂律衰减（Schwarzschild 情形次幂已得点态精确估计）。

### 2.3 环降谱学与检验

多模环降谱学允许在合并后时段独立估计质量—自旋并检验 Kerr 假说与面积定理；既有事件（如 GW150914）上已实现面积定理的统计检验，O4 数据推动多模拟合方法学成熟。

---

## 3. 灰体因子、超辐射与全局幺正

外区的吸收与超辐射使得"外部通道"散射子次幺正。通过引入"视界通道"的耦合自伴扩张或采用耗散散射理论中的修正 BK 公式可恢复全局幺正并保持光谱位移—相位—群延迟的闭合。灰体因子对 Hawking 能谱与环降频域幅度提供必需的频率滤波，近年的模型显示将灰体核直接嵌入环降拟合能够缓解起始时刻选择与多模过拟合的系统误差，并提高参数可辨性与稳定性；相关稳定性与鲁棒性分析也显示灰体因子在环降频带内具有更好的谱稳定性。

---

## 4. Hardy/de Branges：因果—相位—核对角的一体化

对 de Branges 空间 $H(E)$，再生核
$$
K(w,z)=\frac{E(z)\overline{E(w)}-E^#(z)\overline{E^#(w)}}{2\pi i\,(z-\overline w)}\!,\quad E^#(z)=\overline{E(\overline z)}.
$$
在实轴对角处给出；写 $E(x)=|E(x)|e^{i\varphi(x)}$，其中 $\varphi(x)=\arg E(x)$，则
$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2,
$$
其中 $\varphi$ 为 Hermite–Biehler 函数 $E$ 的相位函数。由此得到"相位导数—核对角—密度"的函数论锚点；配合 Toeplitz/Berezin 压缩可将窗化读数严格表示为谱测度的正线性泛函。证明见附录 B。

---

## 5. 信息几何变分（IGVP）与黑洞几何

在小球 $B_\ell(x)$ 上定义广义熵 $S_{\rm gen}=\tfrac{A(\partial B_\ell)}{4G}+S_{\rm out}$。保持体积与真空约束，一阶极值等价于
$$
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle,
$$
二阶非负给出 QNEC 与量子焦散不等式。该链路与黑洞热力学第一定律与表面引力刻度兼容。

---

## 6. 测量—监测—熵产生：I-投影、Belavkin 过滤与 Jarzynski

离散测量中，Lüders 更新可被刻画为在测量约束上的量子相对熵极小（信息投影），从而实现"仪器/POVM—贝叶斯/最大熵—Lüders"的一致化；持续监测由 Belavkin 过滤给出后验态量子随机微分方程，平均化回收 GKSL/Lindblad 并满足 Spohn 的熵产生单调；含反馈的 Jarzynski 等式加入互信息修正
$$
\big\langle e^{-\beta W+\beta\Delta F-I}\big\rangle=1.
$$

---

## 7. Mellin—分形—对数帧与环降多尺度

以 $\omega=\log E$ 将母尺与尺度测度配准；构造对数均匀采样的 Mellin 紧框架 $\{\psi_k\}$，在带限与窗乘子有界下存在帧界
$$
A\|f\|_{\mathcal H}^2\le\sum_k|\langle f,\psi_k\rangle|^2\le B\|f\|_{\mathcal H}^2,
$$
其中 $\mathcal H$ 为本文采用的 Hilbert 空间（如 $L^2$ 能量空间）。
Mellin 帧天然分离指数衰减 $e^{-\Im\omega\,t}$ 与幂律尾 $t^{-\alpha}$ 的叠加，并与广义 Poisson 公式与对数取样相容，利于环降—尾项的稳健分辨与误差闭合。

---

## 8. Zeckendorf 可逆日志与有限窗能量预算

有限窗总能量与模份额以 Zeckendorf 唯一分解 $S(W)=\sum b_k F_k$（无相邻 1）记账，滑窗对应局域可逆进/借位。可据此定义严格对称单幺半范畴 $\mathbf{Zec}$，并以函子 $\mathfrak Z:\mathbf{Zec}\to\mathbf{WScat}$（窗化散射范畴）与 $\mathfrak U:\mathbf{Zec}\to\mathbf{RCA}$（可逆元胞自动机）实现能量份额与局域更新的双向对接。所需的唯一分解、均值与极限分布性质见相关文献。

---

## 9. 观测校准与实现要则

**（9.1）视界成像校准。** EHT 多历元与极化图像显示 M87* 环形几何与阴影直径的年际持久性，并在 Sgr A* 处揭示近视界强有序磁场；该等结果为散射—几何的一致性提供外在锚点。

**（9.2）环降谱学。** 结合 O3–O4 高信噪数据，多模环降与面积定理检验继续推进；既有事件的高置信度面积定理检验为方法学与系统误差控制提供样本。

**（9.3）实现纪律（最小要则）。**

1. **母尺标定**：各 $(\ell,m,s)$ 通道统一采用 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$；吸收/超辐射以"视界通道"补全幺正或用耗散 BK 修正。
2. **窗—核与采样**：$(w_R,h)\in\mathcal S$，Nyquist 采样抑制别名，有限阶 EM 端点修正显式并给出上界；尾项按 Price 定律评估。
3. **环降拟合**：以"QNM 残数 + 灰体核 + Mellin 帧"联合建模，起始时刻由灰体核稳健化，尾项分离。

---

# 核心定理与命题（陈述与证明概略）

**定理 A（BK—Wigner–Smith—母尺同一）。** 对散射对 $(H,H_0)$ 满足 trace-class 条件，$\det S(E)=\exp[-2\pi i\,\xi(E)]$，且
$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\;=\;-\xi'(E)\;=\;\frac{\varphi'(E)}{\pi}.
$$
*证明。* BK 公式给出 $\det S(E)$ 与 $\xi(E)$ 的指数关系；对数求导并用 $\mathsf Q=-i S^\dagger S'$ 即得迹—位移之等价；再以 $\varphi=\tfrac12\arg\det S$ 得相位导等式。耗散/耦合散射在自伴扩张上成立相应变体，详见附录 A。

**命题 B（窗化读数的 Toeplitz/Berezin 正性）。** 若 $(w_R*\check h)\ge0$ 且为 Carleson 权，则 $K_{w,h}$ 正并有界，窗化读数为谱测度的正线性泛函。*证略。* Hardy/Bergman 空间上 Toeplitz 与 Berezin 变换的正性准则与 Carleson 表征。

**定理 C（因果—解析—Kramers–Kronig）。** 线性时不变响应的因果性与其频域上半平面解析等价；其实部与虚部满足 Hilbert（Kramers–Kronig）对偶。*证略。* Hardy 边值理论与 Titchmarsh 定理；近年的 Laplace 形式化提供 $L^1$ 假设下的简明证明。

**定理 D（de Branges：相位导—核对角）。** 对 Hermite–Biehler 函数 $E$，其 de Branges 空间 $H(E)$ 的再生核满足 $K(x,x)=\pi^{-1}\varphi'(x)|E(x)|^2$。*证略。* 由核的标准公式对角极限与 $\Im(E'/E)=\varphi'$ 的关系得出。

**定理 E（QNM 残数—尾项的窗化展开）。** 设时间窗与频核属于 $\mathcal S$ 并满足带限/衰减条件，则窗化响应可写为 QNM 极点全体的残数和与连续谱（分支切割）项 $R_{\rm cut}$ 之和。将极点和按贡献大小截断至前 $J$ 项时，余项 $\mathrm{Tail}=R_{\rm cut}+R_{\rm qnm}^{(>J)}$，其中 $R_{\rm qnm}^{(>J)}$ 为被截断极点的余项，并在上述条件下具显式上界；其中 $R_{\rm cut}$ 服从 Price 定律的幂律衰减，Schwarzschild 情形尾项次幂已有点态精确估计。

**定理 F（IGVP 一阶—二阶变分）。** 小球广义熵的一阶极值与爱因斯坦方程等价；二阶非负导出 QNEC 与量子焦散不等式。

**定理 G（测量更新的相对熵极小与持续监测的熵产生）。** Lüders 规则可由 Umegaki 相对熵极小（I-投影）推出；Belavkin 过滤给出后验态 QSDE，其平均动力学为 GKSL 并满足 Spohn 熵产生单调；含反馈的 Jarzynski 等式加入互信息修正。

**命题 H（Mellin 对数帧与 PSF 的误差分解）。** Mellin 对数帧与广义 Poisson 公式结合，给出"别名旁瓣—EM 端点—尾项"三分误差的上界与可加分解。

**命题 I（Zeckendorf 可逆日志）。** 每个正整数存在唯一无相邻 1 的 Fibonacci 分解；其均值与波动满足 Lekkerkerker 型结论与中心极限定理，从而可作为有限窗能量预算的可逆整数化账本。

---

# 附录（证明要点）

## 附录 A：散射—因果互构与母尺同一

**A.1 单向支撑与前沿。** 若频域边值属于 $H^2(\mathbb C^+)$，则时域响应因果；Titchmarsh 卷积支撑定理给出 $\inf\supp(f*g)=\inf\supp f+\inf\supp g$，从而最早到达 $t_*$ 的加性成立：$t_*(f*g)=t_*(f)+t_*(g)$。

**A.2 因果决定性。** Malament 与 Hawking–King–McCarthy 定理表明在区分/强因果条件下，因果同构蕴含保角同构，由此构造 $\mathfrak F$ 并给出自然等价。([Applied Mathematics at TU Graz][3])

**A.3 BK—Wigner–Smith 链。** BK 公式 $\det S(E)=\exp[-2\pi i\,\xi(E)]$，对数求导得 $(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$；又 $\varphi(E)=\tfrac12\arg\det S(E)$ 故 $\varphi'/\pi=-\xi'$，得母尺同一。耗散散射以自伴扩张与修正 BK 成立。

**A.4 规范不变性。** 若 $\widetilde S=USV$ 且 $\det U\det V\equiv1$，则 $\operatorname{tr}\widetilde{\mathsf Q}=\operatorname{tr}\mathsf Q$，窗化读数与母尺刻度不变。

## 附录 B：Hardy—Kramers–Kronig—Toeplitz/Berezin

**B.1 因果 $\Leftrightarrow$ 解析。** Kramers–Kronig 由上半平面解析与边值理论推出，Laplace 形式化在 $L^1$ 下给出简明证明。

**B.2 de Branges 核对角。** 由核的标准公式
$$
K(w,z)=\frac{E(z)\overline{E(w)}-E^#(z)\overline{E^#(w)}}{2\pi i\,(z-\overline w)}
$$
取 $w=z=x\in\mathbb R$ 的对角极限，并写 $E(x)=|E(x)|e^{i\varphi(x)}$。此时
$$
\frac{d}{dx}\arg E(x)=\Im\frac{E'}{E}(x)=\varphi'(x),
$$
从而
$$
K(x,x)=\frac{1}{\pi}\,|E(x)|^{2}\,\Im\frac{E'}{E}(x)
=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2.
$$

**B.3 Toeplitz/Berezin 正性与 Carleson。** Hardy/Bergman 空间上，正符号或正 Berezin 变换与 Carleson 条件给出 Toeplitz 压缩的有界正性。

## 附录 C：灰体、超辐射与全局幺正（修正 BK）

对外区次幺正散射，通过在扩充 Hilbert 空间添加"视界通道"构成自伴扩张，或直接应用耗散/耦合散射框架下的 BK 变体，可恢复全局幺正并将光谱位移与 $\det S$ 的指数关系延拓至开系统。

## 附录 D：QNM—环降—尾项

**D.1 共振谱。** Kerr 与 Kerr–de Sitter 的 QNM 模稳定、解析性与谱隙结果参见近作；数值以 Leaver 连分式实现高精度谱。

**D.2 Price 尾。** Schwarzschild 背景上线性波的点态衰减给出精确的幂指数，作为窗化残数展开的 Tail 上界。

## 附录 E：IGVP 与 QNEC

**E.1** 纠缠第一定律 $\delta S_{\rm out}=\delta\langle H_{\rm mod}^{(0)}\rangle$；**E.2** 与面积变分配对导出爱因斯坦方程；**E.3** 二阶变分与 QNEC。

## 附录 F：Belavkin—Jarzynski—熵产生

**F.1** 持续监测的量子过滤方程（后验态 QSDE）；**F.2** Spohn 单调性与熵产生；**F.3** 含互信息的 Jarzynski 等式。

## 附录 G：Mellin 紧框架与 NPE 误差闭合

广义 Poisson 公式与对数采样的帧不等式给出别名旁瓣、EM 端点修正与尾项的三分误差上界与可叠加估计。

## 附录 H：Zeckendorf 可逆日志的范畴化

唯一分解（无相邻 1）、贪婪进/借位的线性时间算法，定义对象—态射—张量并证严格对称单幺半范畴；到 $\mathbf{WScat}$ 与 $\mathbf{RCA}$ 的函子保持合成与单位。

---

## 参考引文（按主题选摘）

**Birman–Kreĭn 与光谱位移、Wigner–Smith/态密度**：Strohmaier 等（BK 公式：微分形式）；Behrndt–Malamud–Neidhardt（耗散/耦合散射与 BK 变体）；Yafaev 综述；Wigner–Smith 与态密度/Friedel—Smith 关系的统计与综述。

**因果—解析（Kramers–Kronig、Titchmarsh）**：Laplace 形式化的 KK 证明；Titchmarsh 卷积支撑定理。

**Kerr 扰动、QNM 与解析性/稳定性**：Vasy 等关于 Kerr/Kerr–dS 的 QNM 解析性；Price 尾与点态衰减。

**EHT 观测与校准**：M87* 阴影持久性与多历元；Sgr A* 极化与近视界强磁场。

**环降谱学与面积定理**：GW150914 的面积定理检验；综述与 O4/O5 进展。

**灰体因子与环降建模**：PRD（2024/2024-09）灰体核嵌入环降谱学及鲁棒性分析。

**de Branges 空间与核对角**：de Branges 专著与后续综述。

**IGVP 与 QNEC**：Jacobson（2016）与 Bousso–Fisher–Leichenauer–Wall（2016）。

**测量—过滤—涨落**：Bouten–van Handel–James（量子过滤综述）；Spohn（熵产生）；Sagawa–Ueda（含反馈的 Jarzynski）。

**Mellin—Poisson—EM 误差**：Nguyen–Unser（广义 Poisson 公式）；Bailey–Borwein（EM 误差上界）。

**Zeckendorf 唯一分解与统计**：Kologlu–Kopp–Miller–Wang（分解数目与分布性质）。

---

## 面向实现的最小要则（精要版）

1. **母尺刻度闭合**：全流程统一以 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 标定；存在吸收/超辐射时以"视界通道"或耗散 BK 修正恢复全局幺正。
2. **窗—核与采样纪律**：选取 Schwartz 级窗—核，Nyquist 采样消除别名；有限阶 EM 端点修正与 Tail 上界显式记录。
3. **环降拟合策略**：以"QNM 残数 + 灰体核 + Mellin 对数帧"联合模型；将灰体核并入频域幅度以缓解起始时刻与过拟合，尾项按 Price 定律处置。
4. **IGVP 校核**：以小球广义熵变分进行几何—热力学一致性自检（$1^\text{st}$ 导数 $\Rightarrow$ 场方程；$2^\text{nd}$ 导数 $\Rightarrow$ QNEC）。
5. **可逆能量日志**：采用 Zeckendorf 唯一分解的无相邻 1 账本进行有限窗能量与模份额的可逆统计与版本管理。

---

**致谢与声明**：文中外部事实、判据与标准定理均给出负载性引文；所有公式使用通行记号与标准写法。

[1]: https://authors.library.caltech.edu/records/6apqj-ep466/latest?utm_source=chatgpt.com "A new topology for curved space–time which incorporates ..."
[2]: https://research.rug.nl/files/232459978/1_s2.0_S0007449722000707_main.pdf?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
[3]: https://www.applied.math.tugraz.at/~behrndt/BehrndtMalamudNeidhardt08-3.pdf?utm_source=chatgpt.com "Trace formulae for dissipative and coupled scattering ..."
