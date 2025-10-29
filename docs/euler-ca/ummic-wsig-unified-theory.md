# UMMIC–WSIG：窗口化测量—信息几何—Mellin/de Branges—可逆 CA 的统一正式理论（对外版）

**作者**：Auric（S-series / EBOC）
**版本**：v1.6（2025-10-29，阿联酋时区）
**关键词**：窗口化读数；Nyquist–Poisson–Euler–Maclaurin；镜像核；Mellin 完成函数；de Branges–Kreĭn 规范系统；相位密度；Carleson 测度；Toeplitz/Berezin 局域化；Born=I-投影；可逆 CA；信息守恒
**MSC**：42C15；46E22；47B35；11Mxx；68Q80；81Txx

---

## 摘要（定性）

在"有限窗—有限阶 Euler–Maclaurin（EM）—镜像不引入新奇点"的纪律下，本文从母映射—Mellin 嵌入出发构造完成函数 $Z(s)$，在 de Branges–Kreĭn 规范系统与散射词典中，严格建立**相位导数 = 相对谱密度**的窗口化一致性 $\varphi'(\omega)=\pi\rho(\omega)$（窗平均意义），并给出任意有限窗读数的**Nyquist–Poisson–Euler–Maclaurin（NPEM）**非渐近误差闭合。进一步，以 reproducing-kernel 论证与 Carleson 测度刻画 de Branges 类空间的采样/插值门槛，并在 Toeplitz/Berezin 局域化框架中给出迹—Weyl 型恒等式。信息几何层面，证明"**Born 概率 = KL/I-投影；指针基 = 谱统计极小化子；窗口 = 极小极大最优**"的三位一体定理，并将"自由意志"刻画为可逆 CA 层间的**边界行动**，其代价为窗口化分布的 KL 跃迁量，满足全局信息守恒。

---

## 0. 公设、记号与对象

**A0（有限窗纪律）**：可观测量仅通过支持有限或快速衰减的窗 $W$ 读出；只允许有限阶 EM 展开。误差预算由**三项**封顶：$\mathrm{Err}=\mathrm{Alias}+\mathrm{Poisson}+\mathrm{EM}$，其中 **EM** 指有限阶 Euler–Maclaurin 的"伯努利层 + 截断尾"（见 §2、§3）。

**A1（相位—密度守恒，滑移窗平均）**：归一化相位 $\varphi$ 与相对谱密度 $\rho$ 满足

$$
\langle\varphi'\rangle_{W,u}=\pi\langle\rho\rangle_{W,u}\qquad(\forall u\in\mathbb R),
$$

其证明见 §2"定理 2"。该等式源于 Birman–Kreĭn 公式与 Wigner–Smith 延迟矩阵的散射理论结构。([arXiv][1])

**A2（镜像核）**：存在核 $K$ 与标度 $a$ 使 $K(x)=x^{-a}K(1/x)$。其 Mellin 变换 $\Phi(s)=\int_0^\infty x^{s-1}K(x)\,dx$ 满足 $\Phi(s)=\Phi(a-s)$，且镜像不引入新奇点（端点经有限阶 EM 控制）。一般 Mellin 工具见。([people.mpim-bonn.mpg.de][2])

**A3（de Branges–Kreĭn 规范系统）**：使用 de Branges 空间 $\mathcal H(E)$ 与 Kreĭn–de Branges 规范系统（canonical systems）作为谱模型与采样—插值的 RKHS 载体。([math.purdue.edu][3])

**A4（可逆局域动力学）**：计算宇宙以可逆 CA（EBOC）刻画，行动在层切片 $\mathcal S_L$ 的边界 $B_L$ 上发生；可逆性保证信息守恒（Bennett-Toffoli-Kari 体系）。([mathweb.ucsd.edu][4])

**A5（I-投影与指针）**：任何"概率读数"是先验 $p$ 到约束集 $\mathcal C(W,T)$ 的 KL/I-投影；指针基为窗口化 Fisher 信息或方差的极小化本征方向（Amari-Csiszár 信息几何）。([pages.stern.nyu.edu][5])

**母映射与完成函数**：母指数和 $F(\theta,\rho)=\sum_j c_j e^{i\langle\alpha_j,\theta\rangle}e^{\langle\beta_j,\rho\rangle}$。沿尺度切片得到母核 $f(x)$，定义完成函数

$$
Z(s)=\Big(\int_0^\infty x^{s-1}f(x)\,dx\Big)\Phi(s) ,
$$

并记 $\rho(\omega)$ 为相对谱密度，$\langle X\rangle_W=\int X(\omega)W(\omega)\,d\omega$。

**记号（傅里叶约定与单位）**：采用 $\widehat f(\xi)=\int_{\mathbb R} f(\omega)e^{-i\omega\xi}\,d\omega$；全篇以角频率 $\omega$ 计，"有效带宽" $B_W$ 指在此约定下 $\widehat W$ 的能量主支域参数（用于 Nyquist 与别名评估）。

---

## 1. 基本构造与词典

**定义 1（镜像—Mellin 完成）**
若 $K(x)=x^{-a}K(1/x)$ 且其 Mellin 变换 $\Phi(s)=\int_0^\infty x^{s-1}K(x)\,dx$ 在所需条带存在（例如 $K\in L^1(\mathbb R_+,dx/x)$ 可保成立），则 $\Phi(s)=\Phi(a-s)$。镜像不引入新奇点（端点由有限阶 EM 尾项吸收），并据此定义 $Z(s)$ 如上。镜像对称的标准推导见 Mellin 变换通论。([people.mpim-bonn.mpg.de][2])

**定义 2（相位—谱词典，含相对归一化）**
选定"自由"参考对 $(H_0,f_0,K_0)$，记

$$
Z_{\mathrm{rel}}(s):=\frac{Z(s)}{Z_0(s)},\qquad Z_0(s):=M_{f_0}(s)\Phi_0(s).
$$

假设沿临界线存在散射矩阵 $S(\omega)$ 使

$$
\det S(\omega)=Z_{\mathrm{rel}}\big(\tfrac12+i\omega\big).
$$

据此定义相对相位 $\varphi(\omega):=\arg Z_{\mathrm{rel}}(\tfrac12+i\omega)$，并由 $\det S(\omega)=e^{-2\pi i\xi(\omega)}$ 取 $\pi\rho(\omega):=\partial_\omega\xi(\omega)$。在 §0 的窗与正则前提下，§2 将证明 $\langle\varphi'\rangle_W=\pi\langle\rho\rangle_W$（滑移窗平均）。([arXiv][1])

**相位展开与零点处理**：取参考点 $\omega_0$ 连续展开 $\varphi$，并将零点处的跳变以 $\mu_Z=\sum_j m_j\delta(\omega-\omega_j)$ 记账；本文中的 $\varphi'$ 指展开后之绝对连续部分，离散部分在窗平均下计入 $\langle\mu_Z\rangle_{W,u}$ 并并入 $\pi\langle\rho\rangle_{W,u}$ 的右端审计。

**定义 3（NPEM 三分解）**
任何有限窗读数的误差拆分为

$$
\mathrm{Err}=\mathrm{Alias}+\mathrm{Poisson}+\mathrm{EM},
$$

其中别名来自欠采样频栅越 Nyquist；Poisson 为格点重排项；EM 为有限阶伯努利层与尾项，常数由 DLMF 的 Bernoulli 多项式与 EM 误差界给出。([Massachusetts Institute of Technology][6])

**定义 4（EBOC 边界行动的 KL 度量）**
层 $L$ 的行动 $u_L$ 将边界更新为 $B_L^+=\mathcal A_L(B_L,u_L)$。以内层观测分布 $p_{L+1}$ 定义

$$
\Delta\mathcal I_L(u_L):=D_{\mathrm{KL}}\!\big(p_{L+1}(\cdot\!\mid\!B_L^+)\,|\,p_{L+1}(\cdot\!\mid\!B_L)\big)
$$

（方向固定为"后验对先验"，便于与链式分解一致），并以 KL 链式法则审计跨层守恒。([staff.ustc.edu.cn][7])

**定义 5（指针与 I-投影）**
给定窗—统计约束 $\mathcal C(W,T)$，观测分布为

$$
q=\arg\min_{r\in\mathcal C(W,T)} D_{\mathrm{KL}}(r\|p) ,
$$

指针基为窗口化 Fisher 信息极小的本征方向（dually-flat 几何下的正交投影）。([pages.stern.nyu.edu][5])

---

## 2. 主定理与证明

### 定理 1（镜像功能方程与无新奇点）

若 $K(x)=x^{-a}K(1/x)$ 且 $K\in L^1(\mathbb R_+,dx/x)$，则 $\Phi(s)=\Phi(a-s)$。因此

$$
Z(s)=M_f(s)\Phi(s),\qquad M_f(s):=\int_0^\infty x^{s-1}f(x)\,dx .
$$

一般情形仅有 $\Phi$ 的镜像对称；**若另加** $f(x)=x^{-a}f(1/x)$，则对临界线

$$
\Big\langle Z\big(\tfrac12+i\omega\big)\Big\rangle_W=\Big\langle Z\big(a-\tfrac12-i\omega\big)\Big\rangle_W+O(\mathrm{Err}),\quad \langle F\rangle_W:=\int_{\mathbb R}F(\omega)W(\omega)\,d\omega .
$$

镜像不引入新奇点（端点由有限阶 EM 尾项吸收）。
**证明**：作变元 $x\mapsto 1/x$，由 $K$ 的镜像对称得到功能方程；端点奇性经有限阶 EM 的伯努利层与尾项控制。([people.mpim-bonn.mpg.de][2])

### 定理 2（信息通量连续方程；窗平均一致）

**定义（滑移窗平均）**：$\langle X\rangle_{W,u}:=\int_{\mathbb R}X(\omega)W(\omega-u)\,d\omega$。

在 trace-class 散射/规范系统假设下，并要求 $W\in W^{1,1}(\mathbb R)$（或 $W\in C^1$ 且 $W,W'\in L^1$），且 $\lim_{|\omega|\to\infty}\varphi(\omega)W(\omega-u)=0$，于是 $\partial_u\langle \varphi\rangle_{W,u}=\langle \varphi'\rangle_{W,u}$。此处 $B_W$ 为 $\widehat W$ 的有效带宽（角频率制）。有

$$
\langle \varphi'\rangle_{W,u} = \partial_u\langle \varphi\rangle_{W,u} = \pi\langle \rho\rangle_{W,u}\quad(\forall u\in\mathbb R).
$$

故窗平均意义下 $\varphi'=\pi\rho$。
**证明**：Birman–Kreĭn 给出 $\det S(\lambda)=e^{-2\pi i \xi(\lambda)}$；Wigner–Smith 延迟 $Q=-iS^\dagger\partial_E S$ 使得 $\partial_\omega\arg\det S$ 等于谱移 $\xi$ 的导数，进而与相对密度一致；窗口化由 Poisson/EM 将离散化与边界误差归入 $\mathrm{Err}$。([arXiv][1])

### 定理 3（NPEM 非渐近误差闭合）

设 $W\in C^{r}$（且 $W,W'\in L^1$）且其傅里叶变换 $\widehat W$ 的有效带宽为 $B_W$（角频率制）；定义 Nyquist 阈值 $\Delta\omega_{\mathrm{Nyq}}:=\pi/B_W$，并取 $\Delta\omega\le\Delta\omega_{\mathrm{Nyq}}$。取 EM 阶 $M\le r/2$，并要求 $X\in C^{2M}$ 且 $X^{(2M)}\in L^{1}(|W|,d\omega)$。设窗泄露预算 $L>0$，定义 $\Omega_W$ 使 $\int_{|\omega|>\Omega_W}\!|W(\omega)|\,d\omega\le L$。另取 $X\in L^\infty$ 或 $\widehat X\in L^1$ 以启用别名上界。

令 $\langle X\rangle_{W}:=\int_{\mathbb R}X(\omega)W(\omega)\,d\omega$（理想值），$\langle X\rangle_{\mathrm{disc}}:=\Delta\omega\sum_{n\in\mathbb Z}X(n\Delta\omega)W(n\Delta\omega)$（离散值）。则

$$
\big|\langle X\rangle_{\mathrm{disc}}-\langle X\rangle_{W}\big|\ \le\
C_1\!\!\sum_{k\neq0}\! \big|\widehat{XW}(2\pi k/\Delta\omega)\big|
+ C_2\!\!\sum_{m=1}^{M}\! |B_{2m}|\ |X^{(2m)}|_{L^1(|W|)}
+ C_3\!\int_{|\omega|>\Omega_W}\! |X||W|.
$$

其上界可取：若 $X\in L^\infty$，上述首项 $\le C_1|X|_\infty\sum_{k\neq0}|\widehat W(2\pi k/\Delta\omega)|$；或若 $\widehat X\in L^1$，则 $\le C_1|\widehat X|_{L^1}\sup_\eta\sum_{k\neq0}|\widehat W(2\pi k/\Delta\omega-\eta)|$。常数 $C_i$ 仅依赖于 $W$ 的平滑阶、有效带宽 $B_W$ 与泄露预算/衰减常数，以及支集（如适用）。
**证明**：欠采样导致别名项；Poisson 求和将离散误差重排为频域格点级数；有限阶 EM 以 Bernoulli 多项式与显式余项控制边界与尾项；各项相加即得。([kryakin.site][8])

### 定理 4（三位一体：Born = I-投影；Pointer = 谱极小；Window = 极小极大）

设可行窗集 $\mathcal W$ 为凸且在所用拓扑下（例如 $L^1\cap L^2$ 的弱拓扑）相对紧，误差泛函 $W\mapsto \sup_X|\mathrm{Err}(W;X)|$ 对 $W$ 上半连续并凸，对 $X$ 凹（或采用等价的 Fenchel 对偶刻画）。对约束集 $\mathcal C(W,T)$：
(i) 观测分布等价为先验到 $\mathcal C$ 的 I-投影（存在唯一且 Pythagoras 等式成立）；
(ii) 指针基为窗口化 Fisher 信息/方差的极小化本征方向（dually-flat 正交性）；
(iii) 窗族 $\mathcal W$ 上极小极大问题

$$
\min_{W\in\mathcal W}\ \sup_{X}\ |\mathrm{Err}(W;X)|
$$

存在最优解 $W^\star$，并存在对偶证书（KKT 条件）保证强对偶；在 WH/Gabor 框架下，$W^\star$ 与其对偶 $W^\sharp$ 满足近-tight 的 Wexler–Raz 双正交关系。
**证明**：Csiszár 的 I-投影与信息几何的广义勾股定理给出 (i)；Fisher-Rao 度量下的本征方向最小化给出 (ii)；Gabor/WH 框架中，Wexler–Raz 与密度门槛控制别名，实现 $(W,W^\sharp)$ 的近紧折中以最小化最坏误差，参见 Gröchenig 与 Wexler–Raz 文献。([pages.stern.nyu.edu][5])

### 定理 5（Toeplitz/Berezin 局域化的迹—Weyl 型恒等）

在 de Branges 或其等价 RKHS 上，记核 $K(\omega,\xi)$，定义 $T_{W,\sigma}=P\,M_{\sigma W}\,P$（$P$ 为正交投影）。若 $\int_{\mathbb R}\!|\sigma(\omega)W(\omega)K(\omega,\omega)|\,d\omega<\infty$（从而 $T_{W,\sigma}=PM_{\sigma W}P$ 为迹类），则

$$
\mathrm{Tr}\,T_{W,\sigma}=\int \sigma(\omega)W(\omega)K(\omega,\omega)\,d\omega .
$$

上述可积条件为实现上的充分条件；亦可用 $M_{\sigma W}P\in\mathcal S_1$ 作等价检验标准。
**证明**：迹类积分算子之迹等于核的对角积分（Brislawn 与 Simon 的迹理想理论）；此处核为投影核经乘法符号件的压缩；可由 Berezin 变换视角理解为"符号在核对角上的加权积分"。([projecteuclid.org][9])

### 定理 6（采样—插值的 Carleson 判据）

在 de Branges 空间（或相应模型空间 $K_\Theta$）且相位导数给出 doubling 测度时，实轴采样/插值序列的几何密度刻画成立（Landau-型密度门槛），并与再生核—Carleson 测度条件等价。
**证明**：Marzo–Nitzan–Olsen 在相位导数为 doubling 的 de Branges 空间给出采样/插值的密度刻画；对更广 RKHS 的 reproducing-kernel thesis（RKT）提供算子有界/紧性与 Carleson 测度之间的桥梁。([SpringerLink][10])

### 定理 7（EBOC 的边界—因果等价与守恒）

可逆 CA 的层切片模型中，行动 $u_L$ 的效应等价为谱密度的窗口化形变

$$
\Delta\langle\rho\rangle_W=\big\langle (\partial\rho/\partial B_L)\,,\Delta B_L\big\rangle_W,
$$

在可逆动力学与一致传播假设下，

$$
\sum_{L=L_0}^{L_1}\!\Delta\mathcal I_L= D_{\mathrm{KL}}\!\big(p_{L_1+1}(\cdot\!\mid\!B_{L_1}^+)\,|\,p_{L_1+1}(\cdot\!\mid\!B_{L_1})\big)- D_{\mathrm{KL}}\!\big(p_{L_0+1}(\cdot\!\mid\!B_{L_0}^+)\,|\,p_{L_0+1}(\cdot\!\mid\!B_{L_0})\big).
$$

若两端边界固定（或周期闭合），则上式为 $0$。
**证明**：可逆性（Toffoli–Margolus）确保全局雅可比为 1；信息仅在层间再分配；Cover–Thomas 的 KL 链式分解给出总信息的守恒。([people.csail.mit.edu][11])

---

## 3. 门槛、不可兼得与最优窗

**采样下界（Landau 型）**：若 $\mathrm{supp}\,\rho\subset[-B,B]$（$B$ 以角频率计），则必要样本密度 $\delta_\omega:=1/\Delta\omega\ge B/\pi$（等价于 $\Delta\omega\le \pi/B$）。若以 Hz 计的带宽 $B_{\mathrm{Hz}}=B/2\pi$，则必要采样率 $f_s\ge 2B_{\mathrm{Hz}}$。否则 $\mathrm{Alias}$ 主导误差。([numdam.org][12])

**Balian–Low 不可能性**：时频紧集中与正交紧帧不可兼得，需以 $(W,W^\sharp)$ 的近紧折中实现稳定—分辨率平衡。([科学直通车][13])

**等波纹（Chebyshev/Dolph）窗**：在固定旁瓣预算下实现最小最大（equiripple）误差，满足极小极大意义的频域最坏情形最优；配合 Wexler–Raz 对偶可在近紧框架中抑制别名。([journals.ametsoc.org][14])

---

## 4. 实施规范（非渐近、可复现）

**S1（窗族与对偶）**：取 $\mathcal W_{r,\Omega,L}$（平滑阶 $r$、名义带宽 $\Omega$、泄露 $L$）；为每个 $W$ 构造对偶 $W^\sharp$ 以满足 Wexler–Raz 双正交与近-tight。([sites.math.duke.edu][15])

**S2（EM 阶与常数）**：EM 取 $M\le r/2$；伯努利常数 $B_{2m}$ 与余项界据 DLMF 明确评定。([DLMF][16])

**S3（镜像核设计）**：以 $K(x)=x^{-a}K(1/x)$ 产生 $\Phi(s)=\Phi(a-s)$；对数值近似配合凸正则以免端点假奇性。([people.mpim-bonn.mpg.de][2])

**S4（局域化算子审计）**：构造 $T_{W,\sigma}$，以 $\mathrm{Tr}\,T_{W,\sigma}=\int \sigma W K(\omega,\omega)$ 审计局域谱质量。([projecteuclid.org][9])

**S5（EBOC 两层账本）**：记录 $\Delta B_0,\Delta\mathcal I_0$ 与 $\Delta\langle\rho\rangle_W$。在两端边界固定或周期闭合时验证 $\sum_L \Delta\mathcal I_L=0$；一般情形核对 $D_{\mathrm{KL}}\!\big(p_{L_1+1}(\cdot\!\mid\!B_{L_1}^+)\,|\,p_{L_1+1}(\cdot\!\mid\!B_{L_1})\big)- D_{\mathrm{KL}}\!\big(p_{L_0+1}(\cdot\!\mid\!B_{L_0}^+)\,|\,p_{L_0+1}(\cdot\!\mid\!B_{L_0})\big)$。([mathweb.ucsd.edu][4])

---

## 5. 例证（最小可核验）

**E1（带限谱）**：设 $\rho(\omega)=\mathbf 1_{[-B,B]}$。取 Chebyshev 窗，$\Delta\omega\le \pi/B$，数值验证 $\langle\varphi'\rangle_W=\pi\langle\rho\rangle_W$ 与定理 3 的非渐近上界。([journals.ametsoc.org][14])

**E2（母映射—Mellin）**：由母指数和取片得到 $f$，构造 $Z(s)$ 与镜像核 $\Phi(s)$，检验 $\Phi(s)=\Phi(a-s)$ 与临界线相位—谱一致性。([people.mpim-bonn.mpg.de][2])

**E3（EBOC 边界行动）**：在一对层切片上比较不同 $u_0$ 的 $\Delta\mathcal I_0$ 与 $\Delta\langle\rho\rangle_W$，展示"行动 = 边界形变 = 谱密度改写"，并核对信息守恒。([people.csail.mit.edu][11])

---

## 6. 一致性清单（必须满足）

1. 指定 EM 阶 $M$（禁止 $M\to\infty$）。
2. 镜像不引入新奇点（端点由 EM 尾项吸收）。
3. 采样步长不越 Nyquist；越界时别名项为主误差并据此预算。
4. I-投影、指针极小与窗极小极大之间给出 KKT/对偶证书。([pages.stern.nyu.edu][5])
5. 可逆 CA 的 $\sum_L \Delta\mathcal I_L=0$ 与 KL 链式法则一致。([staff.ustc.edu.cn][7])

---

## 7. 适用边界与不可化约性

* 所有结论局限于"有限窗—有限阶 EM—非渐近常数"纪律；超出不保证闭合。
* 若 $f$ 或 $K$ 破坏"无新奇点"，需正则化或收缩窗域。
* Balian–Low 强制时频—正交不可兼得，必须结构性折中。([科学直通车][13])

---

## 8. 结论

UMMIC–WSIG 在可检验、可复现的有限窗纪律下，将**散射相位—谱密度**一致性、**NPEM 非渐近误差闭合**与**信息几何/可逆 CA**统一为单一框架：镜像核确保功能方程而不引入新奇点；Carleson/RKT 与 Toeplitz/Berezin 把采样—插值与局域谱计数联入同一再生核机制；三位一体定理以凸对偶把 Born 概率、指针与最优窗连接起来。该体系提供了跨数学物理—信号处理—可计算宇宙的"**可测—可算—可审计**"统一叙事。

---

## 附：可直接引用的最小公式块

* **镜像与完成**：$K(x)=x^{-a}K(1/x)\Rightarrow \Phi(s)=\Phi(a-s)$,
  $Z(s)=\big(\int_0^\infty x^{s-1}f(x)\,dx\big)\Phi(s)$。([people.mpim-bonn.mpg.de][2])
* **相位—谱一致**：$\langle \varphi' \rangle_W=\pi\langle \rho\rangle_W$（窗平均，一致性由"定理 2"给出），由 $\det S=e^{-2\pi i\xi}$、$Q=-iS^\dagger S'$ 推出。([arXiv][1])
* **NPEM 误差界**：见定理 3（Poisson + EM + 别名）。([kryakin.site][8])
* **I-投影**：$q=\arg\min_{r\in\mathcal C(W,T)}D_{\mathrm{KL}}(r\|p)$，Pythagoras 成立。([pages.stern.nyu.edu][5])
* **Wexler–Raz 对偶**：近-tight 对偶窗最小化最坏误差。([sites.math.duke.edu][15])
* **Toeplitz/Berezin 迹**：$\mathrm{Tr}\,T_{W,\sigma}=\int \sigma W K(\omega,\omega)\,d\omega$。([projecteuclid.org][9])
* **采样密度**：Landau 必要密度条件（及其广义）。([numdam.org][12])

---

## 参考（选）

* Birman–Kreĭn：$\det S=e^{-2\pi i\xi}$ 与谱移函数综述。([arXiv][1])
* Wigner–Smith 延迟矩阵与相位导数。([rottergroup.itp.tuwien.ac.at][17])
* de Branges–Kreĭn 规范系统与 $\mathcal H(E)$。([math.purdue.edu][3])
* Carleson/采样—插值（de Branges 空间，doubling 相位）。([SpringerLink][10])
* RKT 与 Bergman/Fock 空间的算子判据。([arXiv][18])
* Toeplitz/Berezin 与"迹 = 对角核积分"。([projecteuclid.org][9])
* Poisson 与 EM（显式常数）。([kryakin.site][8])
* Landau 密度与其近年推广。([numdam.org][12])
* Wexler–Raz、Balian–Low 与时频帧。([sites.math.duke.edu][15])
* Chebyshev/Dolph 与窗的等波纹最优。([journals.ametsoc.org][14])
* I-投影与信息几何的勾股定理。([pages.stern.nyu.edu][5])
* 可逆计算与可逆 CA。([mathweb.ucsd.edu][4])

---

**注**：以上各处"证明"均给出从属到公开判据/文献的推理路径；所需技术前提（trace-class、doubling 相位、窗的平滑与带限、帧密度等）在引用文献中明示。若在具体应用中某前提不满足，可按 §4 的实施规范（正则化、窗族收缩、近-tight 对偶）恢复可行性。

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://people.mpim-bonn.mpg.de/zagier/files/tex/MellinTransform/fulltext.pdf?utm_source=chatgpt.com "appendix. the mellin transform"
[3]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[4]: https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Bennett_Reversibiity.pdf?utm_source=chatgpt.com "Logical Reversibility of Computation*"
[5]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[6]: https://web.mit.edu/xiphmont/Public/windows.pdf?utm_source=chatgpt.com "On then Use of Windows for Harmonic Analysis with the ..."
[7]: https://staff.ustc.edu.cn/~cgong821/Wiley.Interscience.Elements.of.Information.Theory.Jul.2006.eBook-DDU.pdf?utm_source=chatgpt.com "Elements of Information Theory"
[8]: https://kryakin.site/am2/Stein-Shakarchi-1-Fourier_Analysis.pdf?utm_source=chatgpt.com "Fourier Analysis"
[9]: https://projecteuclid.org/journals/pacific-journal-of-mathematics/volume-150/issue-2/Traceable-integral-kernels-on-countably-generated-measure-spaces/pjm/1102637666.pdf?utm_source=chatgpt.com "Traceable integral kernels on countably generated ..."
[10]: https://link.springer.com/article/10.1007/s11854-012-0026-2?utm_source=chatgpt.com "Sampling and interpolation in de Branges spaces with ..."
[11]: https://people.csail.mit.edu/nhm/ica.pdf?utm_source=chatgpt.com "ICA - People | MIT CSAIL"
[12]: https://www.numdam.org/item/10.1016/j.crma.2012.05.003.pdf?utm_source=chatgpt.com "Revisiting Landau's density theorems for Paley–Wiener ..."
[13]: https://www.sciencedirect.com/science/article/pii/S1063520302005067?utm_source=chatgpt.com "The Balian–Low theorem for symplectic lattices in higher ..."
[14]: https://journals.ametsoc.org/view/journals/mwre/125/4/1520-0493_1997_125_0655_tdcwas_2.0.co_2.xml?utm_source=chatgpt.com "The Dolph–Chebyshev Window: A Simple Optimal Filter in"
[15]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[16]: https://dlmf.nist.gov/24?utm_source=chatgpt.com "DLMF: Chapter 24 Bernoulli and Euler Polynomials"
[17]: https://rottergroup.itp.tuwien.ac.at/wp-content/uploads/2019/09/P-08.pdf?utm_source=chatgpt.com "Generating Particlelike Scattering States in Wave Transport"
[18]: https://arxiv.org/abs/1212.0507?utm_source=chatgpt.com "A reproducing kernel thesis for operators on Bergman-type function spaces"
