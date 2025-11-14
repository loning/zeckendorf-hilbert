# 时间晶体—Null–Modular $\mathbb Z_2$ 环量统一:从 Floquet 与 Lindblad 到体积分 BF 的相对上同调判据

## Abstract

构建一条把离散/连续时间晶体与 Null–Modular $\mathbb Z_2$ 环量、体积分 $\mathbb Z_2$–BF 选择以及相对上同调不变量统一的理论链路。闭合体系侧,以高频 Floquet–Magnus 与 Lieb–Robinson 约束给出预热离散时间晶体在指数长时间窗口内的刚性与稳定;在强无序下给出 $\pi$ 谱配对与本征态时间晶体序的充要结构。开系侧,对一周期 CPTP 通道的外围谱建立极限环时间晶体的谱判据。准周期驱动侧,以 $\mathbb Z^k$ 时间平移群之有限像构成"时间准晶"的群表示。上述四类现象以一个统一的拓扑—代数骨架对接:$\mathbb Z_2/\mathbb Z_m$ 环量与体积分 $\mathbb Z_2$–BF 顶项的相对上同调类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$;在小因果钻石的门槛下,若满足模块—散射的模二对齐与参数二维循环的可检测与生成,则"几何—能量—拓扑"三者等价,具体为 $[K]=0 \iff$ 允许回路与二维循环上的时间晶体"异常"消失。本文同时给出三类可解家族($\delta$ 势、Aharonov–Bohm、拓扑超导端点)的 $\mathbb Z_2$ 指纹与面向超导量子比特、Rydberg 气体与囚禁离子的工程方案与误差预算。核心 Null–Modular 双覆盖与 BF 相对上同调判据取自作者既有统一原理并在时间晶体语境下重述与证明。

## Keywords

离散时间晶体;预热与多体局域化;开系极限环;时间准晶;拓扑时间晶体;$\pi$ 谱配对;$\mathbb Z_2/\mathbb Z_m$ 环量;体积分 $\mathbb Z_2$–BF;相对上同调;小因果钻石

---

## 1. Introduction & Historical Context

时间平移对称性的自发破缺在平衡体系中受到严谨否定,迫使时间有序相的物理载体转向非平衡驱动与开放动力学。周期驱动多体系统中,离散时间晶体以次谐响应的刚性、长程时间关联与特征谱指纹为标志;随后的本征态有序、预热长寿命、耗散极限环与拓扑(逻辑)时间晶体诸分支,构成跨平台的实验体系。另一方面,我们在几何—信息—散射的统一线上,发展了以平方根行列式分支与模二环量为核心的不变量,并以体积分 $\mathbb Z_2$–BF 的相对上同调语言将其提升为充要判据。本文把这两条脉络严格桥接,证明:时间晶体的"$\pi$/单位根"现象学在统一判据层面即为 $\mathbb Z_2/\mathbb Z_m$ 环量与 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$ 的非平凡性;反之,几何—能量判据(小因果钻石上的一阶与二阶层)在对齐门槛下推出该类不变量的平凡化,从而给出贯通闭合/开放/拓扑/多频的共同结构。

---

## 2. Model & Assumptions

### 2.1 闭合体系(Floquet–MBL/预热)

晶格 $\Lambda$ 上的局域多体体系,周期驱动 $H(t+T)=H(t)$。Floquet 元 $F=\mathcal T \exp(-\mathrm i\int_0^T H\,\mathrm dt)$ 生成离散时间平移。高频极限 $\omega=2\pi/T\gg J$ 下存在准局域有效哈密顿量 $H_\ast$ 与指数小截断误差;强无序情形下 $H_0$ 支持 $l$-bit 结构。

### 2.2 开放体系(周期 Lindblad)

密度矩阵演化 $\dot\rho=\mathcal L_t(\rho)$ 且 $\mathcal L_{t+T}=\mathcal L_t$。一周期量子通道 $\mathcal E=\mathcal T\exp(\int_0^T\mathcal L_t\,\mathrm dt)$ 的外围谱决定长时极限环。

### 2.3 多频准周期

互无理频率族 $\{\omega_i\}_{i=1}^k$ 定义 $\mathbb Z^k$ 的时间平移群;高频预热门槛 $\min_i \omega_i \gg J$ 保障准局域 $H_\star$ 与有限像的群表示。

### 2.4 拓扑时间晶体(逻辑子空间)

稳定子码(表面码)周期工程使 $F_{\rm logical}\simeq \overline X_L \mathrm e^{-\mathrm i H^{\rm top}_\ast T}$,非局域逻辑算符为自然序参量。

### 2.5 Null–Modular 与体积分 BF(相对上同调)

工作空间 $Y=M\times X^\circ$,其中 $M$ 为小因果钻石域或更一般的局域时空片,$X^\circ$ 为参数域去除判别集 $D$。定义

$$
K \;=\; \pi_M^\ast w_2(TM) \;+\; \sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j \;+\; \pi_X^\ast\rho(c_1(\mathcal L_S)) \;\in H^2(Y;\mathbb Z_2),
$$

并在边界平凡化与相对上同调提升下使用 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$。$\mathbb Z_2/\mathbb Z_m$ 环量以平方根行列式分支的模二(或单位根)值计,按"小半圆/折返"规则稳定闭路。

---

## 3. Main Results (Theorems and Alignments)

### 定理 A(预热 DTC 的刚性与指数寿命)

在 $\omega\gg J$ 与分段近 $\pi$"对称踢"的条件下,存在准局域幺正 $U_\ast$ 与对称元 $X^2=\mathbb 1$,使

$$
F \;=\; U_\ast\, \mathrm e^{-\mathrm i H_\ast T}\, X\, U_\ast^\dagger \;+\; \Delta,\qquad |\Delta|\le C\mathrm e^{-c\omega/J}.
$$

任一对 $X$ 奇变换的局域可观测 $O$ 呈 $2T$ 次谐锁定,对 $t\lesssim\tau_\ast\sim \mathrm e^{c\omega/J}$ 不失锁,对小扰动保持 Lipschitz 稳定。

### 定理 B(MBL–DTC 的 $\pi$ 谱配对与本征态序)

强无序链上存在准局域幺正 $U$ 使 $F\simeq \tilde X\, \mathrm e^{-\mathrm i H_{\rm MBL}T}$,谱出现 $\pi$ 配对,诱导态无关的 $2T$ 次谐响应。

### 定理 C(开系极限环的谱判据)

若一周期通道 $\mathcal E$ 的周边谱为 $\{ \mathrm e^{2\pi \mathrm i k/m}\}$ 且余谱半径 $<1$,则几乎所有初态收敛到周期 $mT$ 的极限环吸引子族,构成 $m$ 次谐耗散时间晶体。

### 定理 D(多频"时间准晶"的群表示)

在 $\min_i\omega_i\gg J$ 的预热门槛内,时间平移群 $\mathbb Z^k$ 的有限像产生多条不可通约的次谐峰,形成时间准晶。

### 定理 E(拓扑时间晶体:非局域序与拓扑纠缠)

逻辑子空间中,非局域闭环算符呈刚性的倍周期响应,且与拓扑纠缠熵的非零项一致。

### 定理 F(统一拓扑—同调判据)

在边界平凡化、相对生成性与可检测性的门槛下,以下等价:

$$
[K]=0\ \Longleftrightarrow\ \text{对一切允许回路}\ \gamma:\ \nu_{\sqrt{\det_p S}}(\gamma)=+1\ \text{且对一切允许二维循环}\ \gamma_2:\ \langle \rho(c_1(\mathcal L_S)),[\gamma_2]\rangle=0.
$$

当 $H^2(X^\circ,\partial X^\circ)=0$ 时,上式等价于仅关于回路的模二判据。

### 定理 G(几何—能量 $\Rightarrow$ 拓扑平凡)

在小因果钻石门槛、相对生成—检测、以及模块—散射的模二对齐下,若一阶层给出 $G_{ab}+\Lambda g_{ab}=8\pi G T_{ab}$ 且二阶相对熵 $\delta^2 S_{\rm rel}=\mathcal E_{\rm can}\ge 0$,则上节的统一拓扑—同调判据成立,即推出 $[K]=0$ 与一切 $\mathbb Z_2$ 环量平凡。

---

## 4. Proofs

### 4.1 预热与 $\pi$ 锁定(定理 A/B)

取 Floquet–Magnus 展开 $F=\exp\{-\mathrm iT\sum_{n\ge0}\Omega_n\}$,在最优阶 $n_\ast\sim \omega/J$ 截断定义 $H_\ast$。由 Lieb–Robinson 与局域展开的级数重整得 $|F-\mathrm e^{-\mathrm iH_\ast T}|\le C\mathrm e^{-c\omega/J}$。分段近 $\pi$ 踢 $U_X$ 产生 $X$,在准局域幺正 $U_\ast$ 表象中得到结构分解。强无序下 $UH_0U^\dagger=f(\{\tau_i^z\})$ 与 $\tilde X=UXU^\dagger$ 几乎对易,谱出现 $\pi$ 配对;任意初态在配对子空间展开,得到态无关的 $2T$ 次谐响应。

### 4.2 周边谱与极限环(定理 C)

对 CPTP $\mathcal E$ 作 Jordan–Riesz 分解。若周边谱为 $m$ 个单位根且余谱有隙,则 $\mathcal E^n$ 在各剩余类上指数收敛到周期 $m$ 的循环吸引子;收敛率由 Liouvillian 谱隙控制。

### 4.3 $\mathbb Z_2/\mathbb Z_m$ 环量与相对上同调(定理 F)

以 $\mathbb Z_2$ 系数工作并取相对上同调。体积分 $\mathbb Z_2$–BF 作用

$$
I_{\rm BF}[a,b]=\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile\boldsymbol\delta a\;+\;\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile K\;+\;\mathrm i\pi\!\int_{\partial Y} a\smile b,
$$

在规变与边界项抵消后,对 $[a]\in H^1(Y,\partial Y)$、$[b]\in H^{d-2}(Y,\partial Y)$ 求和,利用有限阿贝尔群特征正交性得到配分函数投影 $Z_{\rm top}\propto \delta([K])$,即 $[K]=0$。由 Poincaré–Lefschetz 对偶,$[K]=0$ 当且仅当对一切允许相对二维循环 $[S]$ 的 Kronecker 配对为零;当 $H^2(X^\circ,\partial X^\circ)=0$ 时,仅余回路模二判据。

### 4.4 几何—能量推出拓扑平凡(定理 G)

在小因果钻石门槛(Hadamard、无共轭点、角点处方、$\nabla^aT_{ab}=0$、固定温标)与加权光线变换的可逆—稳定假设下,由族约束 $\int w(\lambda)(R_{kk}-8\pi G T_{kk})\,\mathrm d\lambda=0$ 与 Radon–型闭包得 $R_{kk}=8\pi G T_{kk}$;零锥刻画与 Bianchi 恒等式升格为张量方程,得到一阶层 $G_{ab}+\Lambda g_{ab}=8\pi G T_{ab}$。角点处方保证协变相空间辛流闭合,$\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge 0$。若存在闭路 $\gamma$ 使 $\nu_{\sqrt{\det_p S}}(\gamma)=-1$,则由模块—散射的模二对齐,在协变相空间构造与环量对应的线性泛函并嵌入二次型核,得到 $\mathcal E_{\rm can}[h,h]<0$ 的矛盾,从而推出一切允许回路的环量平凡,进而由相对生成—检测得到 $[K]=0$。

---

## 5. Model Apply

### 5.1 可解家族的 $\mathbb Z_2$ 指纹

(i)一维 $\delta$ 势:选取围绕复极点的小环,$\oint \tfrac{1}{2\mathrm i} S^{-1}\mathrm dS=\pi\Rightarrow \nu_{\sqrt{\det_p S}}=-1$。
(ii)二维 Aharonov–Bohm:通量穿越半通量 $\alpha=\tfrac12$ 时,$\deg(\det_p S|_\gamma)=1\Rightarrow \nu=-1$。
(iii)拓扑超导端点(Class D/DIII):$\operatorname{sgn}\det_p r(0)$ 或 $\operatorname{sgn}\operatorname{Pf}r(0)$ 翻转与 $\nu_{\sqrt{\det_p r}}$ 同步。三类家族去除判别集后 $H^2(X^\circ,\partial X^\circ)=0$,仅需回路模二判据。

### 5.2 平台映射与观测量

超导量子比特二维阵列:逻辑闭环算符谱中仅在非局域通道出现 $\omega/2$ 峰,并伴随非零拓扑纠缠熵;Rydberg 气体:量子通道周边谱之单位根与荧光自相关的极限环一致;囚禁离子:$\omega$ 提升带来指数寿命增长且频位刚性不漂移;多频驱动:不可通约峰位对应 $\mathbb Z^k$ 的有限像。

---

## 6. Engineering Proposals

### 6.1 预热窗口与脉冲合成

选择 $\omega$ 使 $\mathrm e^{-c\omega/J}\ll \varepsilon$(门噪声幅度),保证 $\tau_\ast\sim \mathrm e^{c\omega/J}$ 覆盖 $10^2\!-\!10^3$ 周期;分段序列在 $\tau_x$ 处实现近 $\pi$ 翻转以放大 $2T$ 锁定。

### 6.2 开系谱隙工程

通过泵浦—退相干比 $G/\kappa$ 构建 Liouvillian 谱隙 $\Delta_{\rm Liouv}$,压制多稳态游移;围绕稳态工作点采样周边特征值与极限环周期。

### 6.3 多频时间准晶

两到三频互无理,避免意外整周期复现;采集频谱并用不可通约峰位识别有限像;以参数闭路重构单位根值。

### 6.4 Wilson–回路的实验化读数

幅—相联合扫描形成闭路;通过 Ramsey/相关函数的离散傅里叶峰区分 $\pm1$;对 $\mathbb Z_m$ 以相位网格拟合单位根。

---

## 7. Discussion (risks, boundaries, past work)

边界与风险包括:高频窗口外吸热致锁定崩解;MBL 在高维与长程作用下的稳性受限;开系的非马尔可夫性导致相位漫游;拓扑时间晶体中非局域读出对漏检与串扰的系统学敏感。统一判据层面,$H^2$ 通道之可检测性需要允许的二维循环生成相对二同调;若平台参数域的二维骨架不足,则只得到必要非充分的判据。与既有工作相比,本文提供的增量在于:以体积分 $\mathbb Z_2$–BF 的相对上同调类 $[K]$ 与模二环量为**单一不变量**,统一刻画闭合/开放/拓扑/多频四类时间晶体,并在小因果钻石的变分门槛下把几何—能量与环量—同调建立为蕴含链。

---

## 8. Conclusion

时间晶体的"$\pi$/单位根"现象学可由 $\mathbb Z_2/\mathbb Z_m$ 环量与体积分 $\mathbb Z_2$–BF 的相对上同调类统一刻画;当相对生成—检测与模块—散射的模二对齐成立时,小因果钻石上的几何—能量判据推出拓扑—同调的平凡化。该结构同时支撑预热 DTC、MBL 本征态序、开系极限环与拓扑时间晶体,并为多频时间准晶提供群表示与实验读出。本文框架为跨平台的时频器件、鲁棒存储与拓扑逻辑操作提供统一的理论—工程通道。

---

## Acknowledgements, Code Availability

感谢公开结果与平台数据所奠定的实验背景。本文不依赖专有代码;相对上同调配对、$\mathbb Z_2/\mathbb Z_m$ 环量重构与周边谱拟合的脚本可据附录中的算法步骤以常规数值工具复现。

---

## References

选取代表性理论与实验工作:时间晶体否定性定理、Floquet–DTC 定义、预热上界、本征态时间晶体序、耗散时间晶体、拓扑时间晶体与时间准晶;以及几何—信息—散射上的 Null–Modular 双覆盖与体积分 $\mathbb Z_2$–BF 统一原理。

---

## 附录(详细证明、技术细节与算法)

### 附录 A  预热上界与指数寿命的严格化

设 $|H(t)|\le J$、$\omega\gg J$。Floquet–Magnus

$$
\Omega_0=\tfrac1T\!\int_0^T\!H,\quad
\Omega_1=\tfrac{1}{2T\mathrm i}\!\iint_{0<t_1<t_2<T}[H(t_2),H(t_1)]\,\mathrm dt_1\mathrm dt_2,\ \ldots
$$

在 $n_\ast\sim \alpha \omega/J$ 截断,取 $H_\ast=\sum_{n\le n_\ast}\Omega_n$。以嵌套对易子的树型重整证明
$|F-\mathrm e^{-\mathrm iH_\ast T}|\le C\mathrm e^{-c\omega/J}$、
$|\tfrac{\mathrm d}{\mathrm dt}\langle H_\ast\rangle|\le C'\mathrm e^{-c\omega/J}$。
分段近 $\pi$ 踢 $U_X$ 使
$F\approx X\,\mathrm e^{-\mathrm iH_\ast T}+\mathcal O(\epsilon)+\mathcal O(\mathrm e^{-c\omega/J})$,从而对 $X$ 奇变换的 $O$ 有
$\langle O(nT)\rangle\approx(-1)^n\langle O(0)\rangle+\mathcal O(\epsilon)+\mathcal O(\mathrm e^{-c\omega/J})$。
频域呈 $\omega/2$ 锁定峰,峰位对参数微扰不漂移(刚性)。

### 附录 B  MBL 的 $\pi$ 配对与本征态序

存在幺正 $U$ 使 $UH_0U^\dagger=f(\{\tau_i^z\})$,近 $\pi$ 踢经 $U$ 变换得准局域 $\tilde X$。若 $F\simeq \tilde X\mathrm e^{-\mathrm iH_{\rm MBL}T}$,则对本征态 $|\psi\rangle$ 有
$F|\psi\rangle=\mathrm e^{-\mathrm iET}\tilde X|\psi\rangle,\quad
F(\tilde X|\psi\rangle)=\mathrm e^{-\mathrm i(ET+\pi)}|\psi\rangle$,谱现 $\pi$ 配对。任意初态在该配对子空间展开给出态无关的 $2T$ 次谐响应。

### 附录 C  CPTP 周边谱与极限环

令 $\sigma(\mathcal E)=\{\lambda_j\}$。若 $|\lambda_j|<1$ 对所有非周边模,且周边模为 $\{ \mathrm e^{2\pi \mathrm i k/m}\}$,则存在互不相交的循环不变子空间,使 $\mathcal E^n$ 将任意初态投影至周期 $m$ 的极限环;收敛速率由 $\Delta_{\rm Liouv}=1-\max_{|\lambda_j|<1}|\lambda_j|$ 控制。

### 附录 D  $\mathbb Z_2/\mathbb Z_m$ 环量:谱流与交数的模二鲁棒

记判别集 $D\subset X^\circ$ 为阈值/嵌入本征值或 $-1$ 特征值子流形。对闭路 $\gamma$ 按"小半圆/折返"规则稳定,定义模二交数 $I_2(\gamma,D)$。修正行列式 $\det_p$ 的改变仅改变量子化相位的整数绕数,其模二投影不变;分波截断 $N\to\infty$ 与相对迹类重整不改变 $\nu_{\sqrt{\det_p S}}=(-1)^{I_2(\gamma,D)}$。

### 附录 E  体积分 $\mathbb Z_2$–BF 的相对上同调推导

在 $(Y,\partial Y)$ 上以 $\mathbb Z_2$ 系数构造

$$
I_{\rm BF}[a,b]=\mathrm i\pi\!\int b\smile\boldsymbol\delta a+\mathrm i\pi\!\int b\smile K+\mathrm i\pi\!\int_{\partial Y} a\smile b.
$$

规变 $a\mapsto a+\boldsymbol\delta\lambda^0$、$b\mapsto b+\boldsymbol\delta\lambda^{d-3}$ 下边界项抵消,作用良定。对 $[a]$ 与 $[b]$ 求和,利用有限阿贝尔群特征正交性得到 $Z_{\rm top}\propto \delta([K])$;Poincaré–Lefschetz 对偶给出 $[K]=0 \iff$ 对一切 $[S]\in H_2(Y,\partial Y;\mathbb Z_2)$ 有 $\langle K,[S]\rangle=0$。

### 附录 F  几何—能量 $\Rightarrow$ 环量平凡:对齐与矛盾法

在角点处方与协变相空间框架下,闭路的模块环量定义有界线性泛函并嵌入二次型核。若存在 $\gamma$ 使 $\nu_{\sqrt{\det_p S}}(\gamma)=-1$,则该泛函在模二投影下给出负方向,构造 $h$ 令 $\mathcal E_{\rm can}[h,h]<0$,与二阶非负性矛盾;故一切允许闭路的环量为 $(+1)$。结合相对生成与检测,推出 $[K]=0$。

### 附录 G  三类可解族的形变收缩与 $H^2=0$

$\delta$ 势、AB 与端点散射的参数域在去除判别集后形变收缩为一维骨架,因而 $H^2(X^\circ,\partial X^\circ)=0$。因此统一判据化为回路上的模二条件;在该情形下,构造横截 $D$ 的参考闭路即可检验 $[K]=0$ 的必要且充分条件。

### 附录 H  实验—算法清单(伪代码层)

1. 数据采集与去趋势:时域序列 $O(t_n)$ 以多项式回归剔除漂移;
2. 峰值与锁定度量:离散傅里叶,拟合峰宽 $\Gamma$ 与锁定比 $\mathcal R$;
3. 单位根读数:参数闭路采样相位,判别 $\pm1$ 或 $m$ 次单位根;
4. 相对上同调测试:选择生成族的回路/二维循环,评估 $\nu_{\sqrt{\det_p S}}$ 与 $\langle \rho(c_1),[\gamma_2]\rangle$ 的表格,验证是否全零以判定 $[K]=0$。
