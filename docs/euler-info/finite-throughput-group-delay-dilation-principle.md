# 有限吞吐—群延迟膨胀原理：以 WSIG–EBOC–RCA 的"窗—刻度—规范"统一带宽、时延与红移

**Version: 1.5**

## 摘要

建立一套将"有限吞吐—排队时延—表观膨胀（红移）"统一到窗化散射与信息几何（WSIG）刻度体系中的严格理论。在算子—测度—函数的纯理论语言下，以"三位一体"刻度同一式 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=-\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$ 为母尺，定义观察者窗的 Toeplitz/Berezin 压缩 $K_{w,h}$ 及其读数泛函，并以被动性与保因果的散射公理刻画"有限吞吐"的抽象形式。证明三条主定理：（T1）**吞吐—时延膨胀定理**：在被动负载单调性下，任意窗化群延迟读数随负载单调不减；当基准读数 $\Phi_w[\lambda_0]>0$ 时，诱导能标与时间标的 Mellin 伸缩在刻度上等价为红移因子 $1+z_w=\Delta_w\ge1$；（T2）**群延迟—带宽乘积上界**：窗化能谱总读数受"群延迟通量"与"有效带宽常数"之乘积一侧上界，并由 Nyquist–Poisson–Euler–Maclaurin（NPE）三项闭合给出非渐近误差界；（T3）**尺度规范等价**：宇宙学膨胀与内部分辨率提升在刻度上严格等价于 $a(t)=R(t)^{-1}$ 的规范配对，其全部读数保持在同一母尺上不变。进一步在可逆元胞自动机（RCA）动力层给出"前沿斜率—群延迟"对应，从而把排队—吞吐—时延的离散动力学嵌入 EBOC 静态块编码。全程仅使用有限阶 Euler–Maclaurin 与 Poisson 纪律，保持"奇性不增/极点=主尺度"的误差控制；任何数值与实验对接置于附录。

---

## Notation & Axioms / Conventions

1. **刻度同一（Trinity）**：对绝对连续谱 a.e. 成立
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=-\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ },\qquad
\mathsf Q(E)=-\,i\,S(E)^\dagger S'(E),\ S(E)\in U(N),
$$
其中 $\varphi$ 为总散射相位，$\rho_{\rm rel}$ 为相对态密度（Birman–Kreĭn 视角），$\mathsf Q$ 为 Wigner–Smith 群延迟矩阵。由 Birman–Kreĭn 公式 $\det S(E)=\exp(-2\pi i\,\xi(E))$ 与 $-i\,\partial_E\log\det S(E)=\operatorname{tr}\mathsf Q(E)$ 得 $\operatorname{tr}\mathsf Q(E)=-2\pi\,\xi'(E)$，从而上式成立（$\xi$ 为谱位移函数）。([arXiv][1])

2. **观察者窗与压缩**：取非负权窗 $w\in L^1(\mathbb R)\cap L^\infty$ 及平滑器 $h$（逼近单位、Carleson 正则）。定义 Toeplitz/Berezin 压缩 $K_{w,h}$ 作用于能谱符号 $F(E)$ 的窗化读数
$$
\langle F\rangle_{w}:=\int_{\mathbb R} w(E)\,\operatorname{tr}F(E)\,dE,\qquad
\langle F\rangle_{w,h}:=\operatorname{tr}(K_{w,h}F),
$$
二者在 NPE 纪律下仅差有限阶 Poisson+Euler–Maclaurin 误差。关于 Toeplitz/Berezin 与 Carleson 嵌入的刻画参见加权 Bergman/Hardy 体系的近期发展。([SpringerLink][2])

3. **被动性与单调性**：负载由保酉散射族 $S_\lambda(E)\in U(N)$（$\lambda\in[0,1]$）表示。被动性公理写作
$$
\partial_\lambda \mathsf Q_\lambda(E)\succeq 0\ \text{ a.e.}
$$
在本文的全部推导中仅使用该 Loewner 单调性，不再主张与 $\partial_\lambda\rho_{\rm rel}$ 之符号等价。其可由单调耦合的自伴谱对 $(H_\lambda=H_0+\lambda V,\ V\ge0)$ 的谱位移函数 $\xi(E;\lambda)$ 随 $\lambda$ 之单调性支撑。([arXiv][3])

4. **NPE 三项闭合（有限阶）**：离散—连续误差分解
$$
\mathcal E_{\rm total}=\mathcal E_{\rm alias}+\mathcal E_{\rm BL}+\mathcal E_{\rm tail},
$$
其中 $\mathcal E_{\rm alias}$ 由 Poisson 频谱混叠给出，$\mathcal E_{\rm BL}$ 为有限阶 Euler–Maclaurin 边界层项，$\mathcal E_{\rm tail}$ 由窗衰减与目标函数台阶控制。Poisson 与 Euler–Maclaurin（含 Bernoulli 常数）之标准参考见。([kryakin.site][4])

5. **尺度规范（scale gauge）**：外部尺度因子 $a(t)$ 与内部分辨率常数 $R(t)$ 的对偶规范
$$
a(t)=R(t)^{-1},\qquad \kappa(t):=\dot a/a=-\dot R/R,
$$
在能量母尺上实现 Mellin 伸缩，红移满足 $1+z=a(t_0)/a(t_e)=R(t_e)/R(t_0)$。([ned.ipac.caltech.edu][5])

---

## 1. 窗化读数、群延迟通量与有效带宽

定义窗化群延迟通量
$$
\Phi_w:=\frac{1}{2\pi}\int_{\mathbb R} w(E)\,\operatorname{tr}\mathsf Q(E)\,dE
=-\langle \rho_{\rm rel}\rangle_w.
$$
定义窗的有效带宽常数
$$
B_w:=|w|_{L^1}\cdot|\widehat{w}|_{\rm pack},
$$
其中 $\widehat{w}$ 为相应 Fourier–Mellin 变换，$|\cdot|_{\rm pack}$ 由 Nyquist/Landau 密度控制（带限或紧框架窗族时可由上下夹常数给定）。若 $0\preceq F(E)\preceq \alpha(E)\mathbf 1$，则
$$
\langle F\rangle_w\le N\,|\alpha|_{L^\infty(\operatorname{supp}w)}\cdot |w|_{L^1}.
$$
一般情形下 $\mathsf Q$ 非必正，故不可取 $F=(2\pi)^{-1}\mathsf Q$；可用
$$
\boxed{\ \Big|\Big\langle \tfrac{1}{2\pi}\mathsf Q\Big\rangle_w\Big|
\le \frac{N}{2\pi}\,\big|\mathsf Q\big|_{L^\infty(\operatorname{supp}w)}\,|w|_{L^1}\ }
$$
作粗上界。采样/帧密度与带宽打包之必要条件参见 Landau 与后续推广。([archive.ymsc.tsinghua.edu.cn][6])

---

## 2. 吞吐的抽象化：算子—测度—函数范式

设观测三元 $(\mathcal H,w,S)$。记刻度测度 $d\mu_{\mathsf Q}:=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)\,dE$。定义能量读数
$$
\mathscr R_w:=\int w(E)\,\rho_{\rm rel}(E)\,dE
=-\frac{1}{2\pi}\int w(E)\,\operatorname{tr}\mathsf Q(E)\,dE
=-\int w(E)\,d\mu_{\mathsf Q}(E)=-\Phi_w.
$$
"有限吞吐"抽象为 $\mu_{\mathsf Q}$ 的 Carleson 型约束：存在常数 $C_{\rm th}$ 与能域分块 $\{\Omega_k\}$ 使
$$
|\mu_{\mathsf Q}|(\Omega_k)\le C_{\rm th}\,\Lambda(\Omega_k),
$$
其中 $\Lambda$ 为窗族诱导之参考测度（由 Nyquist 密度或帧密度给出）。相应 Toeplitz/Berezin 型嵌入在加权函数空间下可由 Carleson 条件刻画。([SpringerLink][2])

---

## 3. 主定理 I：吞吐—时延膨胀定理

**定理 T1（负载单调与膨胀因子）**
设 $S_\lambda(E)$ 满足被动性公理 $\partial_\lambda \mathsf Q_\lambda(E)\succeq 0$ a.e.，且窗 $w\ge 0$ 有紧支撑或满足帧正则性与 NPE 条件。则对任意 $0\le \lambda_0<\lambda_1\le 1$，有
$$
\Phi_w[\lambda_1]-\Phi_w[\lambda_0]
=\frac{1}{2\pi}\!\int w(E)\,\operatorname{tr}\big(\mathsf Q_{\lambda_1}(E)-\mathsf Q_{\lambda_0}(E)\big)\,dE\ \ge 0.
$$
定义刻度上的"时延膨胀因子"（**在 $\Phi_w[\lambda_0]>0$ 时**）
$$
\Delta_w(\lambda_1,\lambda_0):=\frac{\Phi_w[\lambda_1]}{\Phi_w[\lambda_0]}\ \ge\ 1.
$$
一般情形始终成立的陈述为
$$
\Phi_w[\lambda_1]-\Phi_w[\lambda_0]\ \ge\ 0,
$$
等价于 $\mathscr R_w$ 的非增性（因 $\mathscr R_w=-\Phi_w$）。由 Trinity，$\Delta_w$ 同时刻画相位密度导数与相对态密度之伸长，诱导能标—时标的 Mellin 伸缩，等价于红移因子 $1+z_w=\Delta_w(\lambda_1,\lambda_0)\ge1$。其根基在于谱位移函数 $\xi(E;\lambda)$ 随非负耦合单调，且 $\operatorname{tr}\mathsf Q(E)=-2\pi\,\partial_E\xi(E)$。([arXiv][3])

*证明.* 对每个 $E$ 的 Loewner 序单调与 $w\ge0$ 积分即得非减性。由 Birman–Kreĭn 与 Trinity 线性关系，单调性在 $\varphi'$ 与 $\operatorname{tr}\mathsf Q$ 间等价传递；在 $\rho_{\rm rel}$ 上仅差固定负号（$\rho_{\rm rel}=-\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q$），故以上非减性统一以 $\Phi_w$ 表述。证毕。([arXiv][1])

**推论 1（窗口—带域局域性）**
若 $w$ 支持于带限区 $\Omega$，则 $z_w$ 为该域的局域红移；对互不交叠 $\{\Omega_j\}$ 与分解窗 $\{w_j\}$ 构成紧框架时，有
$$
1+z_{\rm global}=\sum_j \omega_j\,(1+z_{w_j}),\qquad
\omega_j=\frac{\Phi_{w_j}[\lambda_0]}{\sum_k \Phi_{w_k}[\lambda_0]},
$$
给出全局伸缩为局域伸缩的加权组合；若基准态下 $\mu_{\mathsf Q}[\lambda_0]$ 为非负测度（等价于 $\Phi_{w_j}[\lambda_0]\ge0$ 对所有 $j$），则该组合为凸组合。

---

## 4. 主定理 II：群延迟—带宽乘积上界

**定理 T2（有限窗能谱守恒上界）**
在 §2 的 Carleson 型吞吐约束、窗族紧框架与 NPE 有效下，对任意 $S(E)$ 与窗 $w$ 有
$$
\boxed{\ \big|\Phi_w\big|\ \le\ C_{\rm frame}\,C_{\rm th}\,B_w\,\big(1+\big|\varepsilon_{\rm NPE}\big|\big)\ },
$$
其中 $C_{\rm frame}$ 由窗族上下夹常数给定，$B_w$ 为有效带宽常数，$\varepsilon_{\rm NPE}$ 为有限阶误差项，满足
$$
|\varepsilon_{\rm NPE}|\ \le\ C_1\,\mathcal E_{\rm alias}+C_2\,\mathcal E_{\rm BL}^{(m)}+C_3\,\mathcal E_{\rm tail}^{(\beta)}.
$$
证明沿 Berezin 压缩交换不等式与 Carleson 嵌入控制 $\mu_{\mathsf Q}$，以窗族帧上下夹联结局域能谱与全局读数，最后用有限阶 Poisson 去混叠与 Euler–Maclaurin 边界层吸收离散—连续差；奇性不增保证主尺度极点不被放大。([SpringerLink][2])

**推论 2（最优窗的变分趋向）**
在固定 $C_{\rm th}$ 与资源约束 $|w|_{L^1}\,,|\widehat w|_{\rm pack}$ 下，最大化 $\Phi_w$ 的 $w^\star$ 趋向紧框架与近最小不确定性窗；若带限域不变，则 $w^\star$ 于域内近常幅、边界处具有最小边界层代价。其帧/密度条件与 Wexler–Raz 双正交及 Balian–Low 之障碍相容。([SpringerLink][7])

---

## 5. 主定理 III：尺度规范等价与红移=分辨率提升

**定理 T3（规范等价）**
令 $a(t),R(t)$ 满足 $a(t)=R(t)^{-1}$ 与 $\kappa(t)=\dot a/a=-\dot R/R$。在 Trinity 母尺上，对任意窗 $w$ 与能量读数
$$
\mathscr R_w(t)=\int w(E)\,\rho_{\rm rel}(E;t)\,dE=-\frac{1}{2\pi}\int w(E)\,\operatorname{tr}\mathsf Q(E;t)\,dE,
$$
存在 Mellin 伸缩不变性
$$
\mathscr R_w(t_0)=\mathscr R_{(1+z)^{-1}\,w\circ \mathcal D_{1+z}}(t_e),\qquad \mathcal D_{1+z}:E\mapsto \frac{E}{1+z},\quad 1+z=\frac{a(t_0)}{a(t_e)}=\frac{R(t_e)}{R(t_0)}.
$$
因此"膨胀"与"分辨率提升"仅是同一母尺下的规范重述，不改变任何窗化读数的本体含义。([ned.ipac.caltech.edu][5])

**推论 3（红移—时延配对）**
若负载 $\lambda$ 与规范 $a$ 相关，使 $\partial_\lambda \mathsf Q\succeq 0$ 且 $d\lambda$ 诱发 $da/a=d\lambda\cdot \eta(\lambda)$ 的增益，则 T1 的 $\Delta_w$ 与 T3 的 $1+z$ 一致化：$1+z_w=\Delta_w$。

---

## 6. 离散动力学接口：RCA 前沿斜率与群延迟

在 EBOC 静态块编码下，令一维可逆元胞自动机 $\mathcal A$ 的时空图作为二维 SFT。设其前沿斜率 $c_{\rm RCA}$ 为相干缺陷传播的平均速度。WSIG 刻度嵌入给出能轴—格点尺度同构，使
$$
c_{\rm RCA}=\left(\frac{dx}{dt}\right)_{\rm eff}\propto \Big(\tfrac{1}{N}\operatorname{tr}\mathsf Q\Big)^{-1},
$$
即群延迟迹的倒数决定 RCA 的有效推进速率；被动负载使 $\operatorname{tr}\mathsf Q$ 增大，从而 $c_{\rm RCA}$ 降低，表现为离散动力学"减速"与连续刻度"红移"的同构。关于可逆性、信息速度与光锥界的基础性质参见经典 CA 理论综述。([ibisc.univ-evry.fr][8])

---

## 7. 误差学与"奇性不增/极点=主尺度"

**命题（有限阶 NPE 闭合）**
若窗 $w$ 具 $m$ 阶光滑与 $\beta$ 阶衰减，在 Landau 密度条件下，
$$
\big|\mathscr R^{\rm disc}\!*\!w-\mathscr R^{\rm cont}\!*\!w\big|
\le C(m,\beta)\!\left(\!\sum_{\ell\ne 0}\!|\widehat w(\ell f_s)|+\!\sum_{j=1}^m\!\frac{|B_{2j}|}{(2j)!}|\partial^{(2j-1)}w|_{L^1}\!+\!\!\int_{|E|>E_{\max}}\! |w(E)\,\rho_{\rm rel}(E)|\,dE\!\right)\!,
$$
其中 $B_{2j}$ 为 Bernoulli 常数；若 $\rho_{\rm rel}$ 仅含有限极点且窗运算不激发新奇性，则误差项不提升奇性，主尺度由极点决定。([archive.ymsc.tsinghua.edu.cn][6])

---

## 8. 多端口结构与统计刻画

设 $\{\tau_j(E)\}_{j=1}^N$ 为 $\mathsf Q(E)$ 的特征时延（proper delay times），则
$$
\Phi_w=\frac{1}{2\pi}\sum_{j=1}^N \int w(E)\,\tau_j(E)\,dE,\qquad
\partial_\lambda \tau_j(E)\ge 0\ \text{ a.e.}
$$
统计学层面的分布与矩母函数在混沌腔体与非理想耦合下可由随机矩阵理论给出，支撑"总群延迟=特征时延求和"的分解与其极端波动律。([物理评论链接管理器][9])

---

## 9. 与通信容量直觉的对位（纯理论重述）

以 $\mu_{\mathsf Q}$ 的 Carleson 约束代表"有限吞吐"，对应单位资源块内群延迟总量有限。T1 给出"负载 $\uparrow$ $\Rightarrow$ 时延读数 $\uparrow$"；T2 则把总读数上界化为"群延迟通量 $\times$ 有效带宽常数"。若以刻度时间常数 $\mathcal T_w:=\Phi_w/|w|_{L^1}$ 作为表观周期伸长，在 $\Phi_w[\lambda_0]>0$ 时有
$$
\frac{\mathcal T_w[\lambda_1]}{\mathcal T_w[\lambda_0]}\ =\ \Delta_w(\lambda_1,\lambda_0)\ =\ 1+z_w.
$$
一般情形下，仅有 $\ \mathcal T_w[\lambda_1]-\mathcal T_w[\lambda_0]\ \ge\ 0\ $（等价于 $\Phi_w$ 非减）成立，给出"红移 = 等效时延拉伸"的刻度等价，无需概率假设或实验性语汇。

---

## 10. 规范群与不变性

定义能轴上的 Mellin–Heisenberg 规范群 $\mathcal G$ 对窗与读数的作用
$$
g\cdot w(E)=\chi\,w(\chi E),\qquad
g\cdot \rho_{\rm rel}(E)=\rho_{\rm rel}(E/\chi),
$$
则 Trinity 母尺下的窗化读数满足
$$
\langle \rho_{\rm rel}\rangle_{g\cdot w}=\langle g\cdot \rho_{\rm rel}\rangle_{w}.
$$
尺度规范 $a=R^{-1}$ 为 $\mathcal G$ 的一维子群，等价于 T3。([ned.ipac.caltech.edu][5])

---

## 附录 A：定理 T2 的证明提纲

以 Berezin 压缩 $K_{w,h}$ 与自伴符号 $F(E)=(2\pi)^{-1}\mathsf Q(E)$ 开始。Carleson 嵌入给出
$$
\big|\operatorname{tr}(K_{w,h}F)\big|\ \le\ C_{\rm th}\,|K_{w,h}|_{\rm Car}\ \lesssim\ C_{\rm th}\,C_{\rm frame}\,B_w.
$$
其中 $|K_{w,h}|_{\rm Car}$ 受窗族帧密度与 $\widehat w$ 打包度控制；再以有限阶 Poisson 去混叠、Euler–Maclaurin 吸收边界层与尾项，有
$$
\Phi_w=\langle F\rangle_w=\operatorname{tr}(K_{w,h}F)+O(\varepsilon_{\rm NPE}),\qquad
\big|\Phi_w\big|\ \le\ C_{\rm th}\,C_{\rm frame}\,B_w\,\big(1+\big|\varepsilon_{\rm NPE}\big|\big).
$$
当 $w$ 带限且窗族近紧时，$|K_{w,h}|_{\rm Car}$ 上下夹合一，界可成紧。([SpringerLink][2])

---

## 附录 B：RCA 的构造化刻度

在一维可逆 CA 的局域规则与 SFT 编码框架下，引入能轴刻度映射 $\Theta:\mathbb Z^2\to \mathbb R$，使每条特征方向的离散速度与刻度群延迟满足
$$
c_{\rm RCA}(\theta)=\frac{\Delta x}{\Delta t}\ \propto\ \Big(\frac{1}{N}\operatorname{tr}\mathsf Q\big(\Theta(\theta)\big)\Big)^{-1}.
$$
（当且仅当选定统一的空间/时间单位规范时，比例常数可被归一。）被动性使 $\operatorname{tr}\mathsf Q$ 单调上升，故 $c_{\rm RCA}$ 单调下降；此下降与 T1 的 $\Delta_w\ge1$ 同构，给出"非加速—非增"型可逆动力学读数。关于可逆性、信息光锥与速度上界的基础定理见。([ibisc.univ-evry.fr][8])

---

## 附录 C：NPE 误差预算（有限阶配方）

1. **Poisson 去混叠**：选采样率 $f_s$ 满足 Landau 密度条件，控制
$$
\mathcal E_{\rm alias}\le \sum_{\ell\ne 0}\big|\widehat w(\cdot+\ell f_s)\big|.
$$
([archive.ymsc.tsinghua.edu.cn][6])

2. **Euler–Maclaurin 边界层（$m$ 阶）**：取 $m$ 使 $\partial^{(2m)}w$ 与 $\partial^{(2m)}\rho_{\rm rel}$ 可积，误差
$$
\mathcal E_{\rm BL}^{(m)}\ \lesssim\ \sum_{j=1}^m \frac{|B_{2j}|}{(2j)!}\,|\partial^{(2j-1)}w|_{L^1}\,|\partial^{(2j-1)}\rho_{\rm rel}|_{L^\infty(\operatorname{supp}w)}.
$$
([数学函数数字图书馆][10])

3. **尾项**：能域截断 $E_{\max}$ 下，$\mathcal E_{\rm tail}^{(\beta)}\le |w\cdot\mathbf 1_{|E|>E_{\max}}|_{L^1}\,|\rho_{\rm rel}|_{L^\infty}$，由 $w$ 的 $\beta$ 阶衰减控制至所需精度。

---

## 术语卡片（固定）

* **卡片 A（刻度同一）**：$\displaystyle \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=-\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)$；读数一律在母尺上执行。([arXiv][1])
* **卡片 B（有限阶 EM 与"极点=主尺度"）**：仅使用有限阶 Euler–Maclaurin 与 Poisson；误差学遵循"奇性不增/极点=主尺度"。([数学函数数字图书馆][10])

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://link.springer.com/article/10.1007/s10114-023-2396-z?utm_source=chatgpt.com "Toeplitz Operators and Carleson Measures for Weighted ..."
[3]: https://arxiv.org/pdf/math/9909076?utm_source=chatgpt.com "arXiv:math/9909076v1 [math.SP] 14 Sep 1999"
[4]: https://kryakin.site/am2/Stein-Shakarchi-1-Fourier_Analysis.pdf?utm_source=chatgpt.com "Fourier Analysis"
[5]: https://ned.ipac.caltech.edu/level5/March14/Weinberg/Weinberg2.html?utm_source=chatgpt.com "Observational Probes of Cosmic Acceleration"
[6]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[7]: https://link.springer.com/article/10.1007/s00041-001-4018-3?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler-Raz Identity"
[8]: https://ibisc.univ-evry.fr/~hutzler/Cours/IMBI_MPS/Kari05.pdf?utm_source=chatgpt.com "Theory of cellular automata: A survey"
[9]: https://link.aps.org/doi/10.1103/PhysRevLett.78.4737?utm_source=chatgpt.com "Quantum Mechanical Time-Delay Matrix in Chaotic Scattering"
[10]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
