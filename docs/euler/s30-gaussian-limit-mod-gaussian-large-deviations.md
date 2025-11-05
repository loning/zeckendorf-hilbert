# S30. 高斯极限、模高斯与大偏差

**—— de Branges–Mellin 局部化行列式从二阶到全非线性的极限理论**

**Version: 1.2**

## 摘要(定性)

在相位—密度刻度与局部化算子框架中,本文把 S28 的强型 Szegő–Widom 极限与 S29 的变分—Hessian 结构提升为**涨落—偏差**的统一理论:

1. 对**对数行列式** $\mathscr F_R(a,w;\lambda)=\log\det(I+\lambda T_{a,w,R})$,在"带限+Nyquist+有限阶 Euler–Maclaurin (EM)"纪律下,给出**模高斯(mod–Gaussian)收敛**:中心化后其累积母函数以 $H^{1/2}$ 能量为二阶项,三阶及以上累积量在 $R\to\infty$ 时为 $o(M_R)$;
2. 在特例 $0\le a\le1$ 下,以谱值 $\{p_j^{(R)}\}$ 的**Poisson–Binomial**模型刻画"占据统计",建立**中心极限定理(CLT)**、**中偏差(MDP)**与**大偏差原理(LDP)**,速率函数由带窗相位体积平均的勒让德变换给出;
3. 给出**泛函二阶极限/高阶塌缩**:以相位坐标上的测试函数族索引,中心化的线性统计在二阶型上收敛到 $H^{1/2}$ 能量,高阶项统一塌缩;
4. 多窗/非平稳拼接与 BN–Bregman 软化下,极限与稳定性保持;全程仅用**有限阶** EM 与带限投影,**不引入新奇点**,保持"**极点 = 主尺度**"。

---

## 0. 设定与基本对象

**相位—密度与基准测度.** 取 Hermite–Biehler(HB)整函数 $E$ 与 de Branges 空间 $\mathcal H(E)$;写
$$
E(x)=|E(x)|e^{-i\varphi(x)},\qquad \varphi'(x)=\pi\,\rho(x)=\pi\,\frac{K(x,x)}{|E(x)|^2}>0\ \ (\text{a.e.}),
$$
记基准测度 $d\mu(x):=\dfrac{\varphi'(x)}{\pi}\,dx$。

**局部化算子.** 取符号 $a\in L^\infty(\mathbb R)$ 与**偶窗** $w_R(t)=w(t/R)$(带限或指数衰减)。定义
$$
T_{a,w,R}:=\int a(x)\,w_R(x)\ \frac{|K(\cdot,x)\rangle\langle K(\cdot,x)|}{K(x,x)}\,d\mu(x),
$$
以及相位体积 $M_R:=\int w_R\,d\mu$。**窗化积分算子**
$$
\Pi_R(x,y):=\int w_R(t)\,\frac{K(x,t)\overline{K(y,t)}}{\sqrt{K(x,x)K(y,y)}}\,d\mu(t)
$$
是一个自伴的正算子("窗化帧算子"),一般**不是**正交投影;仅当 $w_R$ 为指示函数(或满足 Parseval 紧帧条件)时才退化为投影。由此
$$
\|\Pi_R\|_{HS}^2=\operatorname{Tr}\!\big(\Pi_R^2\big)\ \le\ \|\Pi_R\|_{\infty}\,\operatorname{Tr}\Pi_R\ \le\ C_w\,\operatorname{Tr}\Pi_R\ =\ \mathcal O(M_R),\quad C_w:=\|w\|_\infty.
$$
取
$$
\mathscr F_R(a,w;\lambda):=\log\det\!\big(I+\lambda T_{a,w,R}\big),\qquad \lambda\in\mathbb R\ \text{邻域}.
$$

**平均记号统一.** 记
$$
\langle f\rangle_{w_R}:=\frac{1}{M_R}\int f\,w_R\,d\mu,
$$
若 $\langle f\rangle=\lim_{R\to\infty}\langle f\rangle_{w_R}$ 存在,则以 $\langle f\rangle$ 记之。

**换序与数值纪律.** Lebesgue—求和换序**仅用有限阶** EM;对任意被采样 integrand $g$,数值误差由"别名+伯努利层+截断"的非渐近上界统一控制;在**带限+Nyquist**条件下别名项为 0。

---

## 1. 模高斯极限:从二阶到累积量的塌缩

令
$$
Y_R(\lambda):=\mathscr F_R(a,w;\lambda)
-\int \log\big(1+\lambda a(x)w_R(x)\big)\,d\mu(x)
-\frac12\,\mathcal Q_R\!\big(\log(1+\lambda a)\big),
$$
其中
$$
\mathcal Q_R(h):=\iint \frac{(h(x)-h(y))^2}{2}\,|\Pi_R(x,y)|^2\,d\mu(x)\,d\mu(y).
$$

### 定理 30.1(累积量塌缩/模高斯型)

在固定 $\lambda$ 的紧邻域内,存在 $\epsilon>0$ 使得 $Y_R(\lambda)$ 的高阶累积量(由 $\mathscr F_R(a,w;\lambda)$ 的幂级数系数/多重导数定义)满足:对任意 $k\ge3$,$\kappa_k\big(Y_R(\lambda)\big)=o(M_R)$。且当 $t_R=\theta/\sqrt{M_R}$($\theta$ 有界)时,
$$
\sum_{k\ge3}\frac{\kappa_k\big(Y_R(\lambda)\big)}{k!}\,t_R^k\ \longrightarrow\ 0,\qquad
\kappa_2\big(Y_R(\lambda)\big)\sim M_R\,\sigma^2(\lambda),
$$
其中
$$
\sigma^2(\lambda):=\lim_{R\to\infty}\frac{1}{M_R}\,\mathcal Q_R\!\big(\log(1+\lambda a)\big).
$$
亦即在 $t=t_R$ 处 $Y_R(\lambda)$ 的正规化累积量母函数收敛到 $\frac12\theta^2\sigma^2(\lambda)$。

**证明要点** 由 S28 的二阶展开得主项与二次项;对 $k\ge3$ 阶累积量利用 $\|\Pi_R\|_{HS}^2=\operatorname{Tr}(\Pi_R^2)\le\|\Pi_R\|_{\infty}\,\operatorname{Tr}\Pi_R\le C_w\,\operatorname{Tr}\Pi_R=\mathcal O(M_R)$ 与带限投影的局域性,得 $\kappa_k=o(M_R)$。对 $t_R$ 级别展开即得累积量塌缩。

> **解释** 二次型 $\mathcal Q_R$ 在相位坐标 $u=\varphi(x)/\pi$ 下收敛到 $H^{1/2}$ 能量 $\mathcal Q(h)=\frac{1}{2\pi}\int|\widehat{h\circ\varphi^{-1}}(\xi)|^2|\xi|\,d\xi$。

---

## 2. 占据统计($0\le a\le1$)的 CLT/MDP/LDP

设 $0\le a\le1$。记 $T_R:=T_{a,w,R}$ 的特征值为 $\{p_j^{(R)}\}\subset[0,1]$。定义 Poisson–Binomial 变量
$$
S_R:=\sum_j \xi_j^{(R)},\qquad \xi_j^{(R)}\sim\mathrm{Bernoulli}\big(p_j^{(R)}\big)\ \text{独立},
$$
其母函数为
$$
\log\mathbb E\big[e^{\theta S_R}\big]=\log\det\!\big(I+(e^\theta-1)T_R\big).
$$
令 $\mu_R:=\mathbb E S_R=\operatorname{Tr}T_R$、$\sigma_R^2:=\mathrm{Var}(S_R)=\operatorname{Tr}(T_R(1-T_R))$。

### 定理 30.2(CLT)

若存在常数 $c,C>0$ 使 $\frac{1}{M_R}\mu_R\to m\in(0,\infty)$、$\frac{1}{M_R}\sigma_R^2\to v\in(0,\infty)$,且
$$
\max_j p_j^{(R)}(1-p_j^{(R)})\ =\ o\!\big(\sigma_R^2\big),
$$
则
$$
\frac{S_R-\mu_R}{\sigma_R}\ \xrightarrow{d}\ \mathcal N(0,1).
$$
**说明** 条件保证了"无主导特征值"与"方差线性扩展";这在 $\operatorname{ess\,inf}a>0$ 与 $\operatorname{ess\,sup}a<1$(带内非饱和)且 $w_R\to1$ 的情形下自动满足。

### 定理 30.3(中偏差 MDP)

若 $r_R\to\infty$ 且 $r_R/\sigma_R\to0$,则 $\frac{S_R-\mu_R}{r_R}$ 满足速率函数 $I(x)=x^2/(2v)$ 的 MDP,速率 $r_R^2/\sigma_R^2$。

### 定理 30.4(大偏差 LDP)

$\frac{1}{M_R}\,S_R$ 在速率 $M_R$ 上满足 LDP,其良性速率函数
$$
\mathcal I(s)=\sup_{\theta\in\mathbb R}\Big\{\theta s-\Lambda(\theta)\Big\},
$$
其中
$$
\Lambda(\theta)=\lim_{R\to\infty}\frac1{M_R}\int \log\!\big(1+(e^\theta-1)\,a(x)\,w_R(x)\big)\,d\mu(x).
$$
若进一步有 $w_R\to 1$ 并且带窗平均与 $\mu$-平均一致,则
$$
\Lambda(\theta)=\langle\log\big(1+(e^\theta-1)a\big)\rangle=\lim_{R\to\infty}\langle\log\big(1+(e^\theta-1)a\big)\rangle_{w_R}.
$$
**说明** 由 Gärtner–Ellis 定理:上述 $\Lambda(\theta)$ 为极限累积母函数,其严格凸与 $C^1$ 保证良性。

---

## 3. 线性统计的泛函二阶极限/高阶塌缩($H^{1/2}$ 场)

取 $h\in C^{1,\alpha}\cap L^\infty$,定义中心化线性统计
$$
L_R(h):=\operatorname{Tr}\,h(T_{a,w,R})-\int h\big(a(x)w_R(x)\big)\,d\mu(x).
$$

### 定理 30.5(泛函二阶极限/高阶塌缩)

设 $\{h_\ell\}_{\ell=1}^m\subset C^{1,\alpha}\cap L^\infty$。则
$$
\frac{1}{M_R}\,\mathcal Q_R\!\Big(h_\ell'\!(a)\,a(1-a),\ h_k'\!(a)\,a(1-a)\Big)
\ \longrightarrow\
\mathcal Q\!\Big(h_\ell'\!(a)\,a(1-a),\ h_k'\!(a)\,a(1-a)\Big),
$$
并据此定义极限协方差矩阵
$$
\Sigma_{\ell k}:=\frac12\,\mathcal Q\!\Big(h_\ell'\!(a)\,a(1-a),\ h_k'\!(a)\,a(1-a)\Big),
$$
这里 $\mathcal Q(\cdot,\cdot)$ 为 $H^{1/2}$ 双线性型(相位坐标)。同时,所有 $k\ge3$ 阶多线性累积量均为 $o(M_R)$。

(若采用§2的 Poisson–Binomial 占据随机化解释"随机性",则有
$$
\frac{1}{\sqrt{M_R}}\big(L_R(h_1),\dots,L_R(h_m)\big)\xrightarrow{d}\mathcal N(0,\Sigma).
$$
)

**证明要点** 多维累积量法:二阶项给出 $\Sigma$,高阶累积量统一为 $o(M_R)$。

**窗的进入方式说明** 在协方差矩阵
$$
\Sigma_{\ell k}=\frac12\,\mathcal Q\!\Big(h_\ell'\!(a)\,a(1-a),\ h_k'\!(a)\,a(1-a)\Big)
$$
中,$w_R$ 仅通过 $\Pi_R$ 进入 $\mathcal Q_R$ 并在极限 $\mathcal Q$ 中体现,故 $h'$ 的自变量取 $a$ 而非 $a\,w_R$。

> **注** 对 $h(\cdot)=\log(1+\lambda\,\cdot)$ 回收定理 30.1 的二阶方差;对分段常数 $h$ 得到区段计数的协方差。

---

## 4. 多窗/非平稳与软化的稳定性

**多窗与帧算子.** 若 $\{w_R^{(\ell)}\}_{\ell=1}^K$ 为 Parseval 紧帧拼接($\sum_\ell w_R^{(\ell)}\to1$ 局部一致),则 $\Pi_R=\sum_\ell \Pi_R^{(\ell)}$ 且
$$
\mathcal Q_R(h)=\sum_\ell \mathcal Q_R^{(\ell)}(h)+o(M_R),\qquad
\sigma^2(\lambda)=\lim_{R\to\infty}\frac{1}{M_R}\sum_\ell \mathcal Q_R^{(\ell)}\!\big(\log(1+\lambda a)\big).
$$
因此模高斯、CLT/MDP/LDP 逐窗叠加成立;非 Parseval 情形以帧乘子修正 $a\mapsto a\cdot\mathcal S_W$。

**BN–Bregman 软化.** 以 $\min -\mathscr F_R+\tau\,\Lambda^\ast$ 软化符号/窗的最优化。若 $\Lambda$ 在最优点邻域 $(\mu,L)$-强凸—平滑,则极小元与最小值对数据扰动李普希茨稳定;$\tau\downarrow0$ 的 $\Gamma$-极限回到硬问题,而模高斯与 CLT/MDP/LDP 的极限不变。

---

## 5. 阈值、边界层与 Fisher–Hartwig 型奇性

**阈值区与相位伸长.** 若 $\varphi'$ 在某区间显著变小(S21 的阈值邻域),则相位坐标被拉伸,$H^{1/2}$ 能量弱化,导致方差放大与中/大偏差的速率常数下降;定理 30.1–30.5 仍成立,但协方差与速率函数对阈值几何更敏感。

**符号奇性.** 当 $\log(1+\lambda a)\notin C^{1,\alpha}$(如触及分支或出现跳跃/幂次尖点)时,可能出现 $\gamma\log M_R$ 的边缘项(Fisher–Hartwig 型);本文默认排除此情形(平滑符号)。必要时可将符号分解为"平滑×原子奇性"逐项处理。

---

## 6. 失效边界

1. **无限阶 EM 禁用**:将 EM 当无穷级外推会产生伪奇点并破坏累积量的统一 $o(M_R)$ 控制。
2. **带限/偶性缺失**:需回退到一般 RKHS 的投影—卷积形式并在边界层加入界面条件。
3. **饱和区**:若 $a=0$ 或 $a=1$ 在带内占正测度,方差可退化;CLT 需额外非退化条件或在非饱和区内作限制。
4. **谱主导**:若存在宏观特征值团簇趋近 1,需以"去饱和"正则化或引入 Parseval 近似帧以重新分配能量。

---

## 7. 可检清单(最小充分条件)

1. **相位密度**:$\varphi'(x)=\pi K(x,x)/|E(x)|^2>0$,取 $d\mu=\frac{\varphi'}{\pi}dx$。
2. **窗/换序**:偶窗带限或指数衰减;**有限阶** EM;Nyquist 条件消别名。
3. **二阶量**:$\mathcal Q_R(h)$ 可计算且 $\frac{1}{M_R}\mathcal Q_R(h)\to \mathcal Q(h)$(相位坐标 $H^{1/2}$)。
4. **模高斯**:$Y_R(\lambda)$ 的三阶及以上累积量为 $o(M_R)$;二阶极限为 $\sigma^2(\lambda)=\lim M_R^{-1}\mathcal Q_R(\log(1+\lambda a))$。
5. **占据统计**(若 $0\le a\le1$):验证 $\sigma_R^2=\operatorname{Tr}(T_R(1-T_R))\sim v\,M_R$ 且 $\max_j p_j^{(R)}(1-p_j^{(R)})=o(\sigma_R^2)$,则 CLT/MDP/LDP 成立。
6. **泛函二阶极限**:测试族 $h\in C^{1,\alpha}\cap L^\infty$;协方差由 $\frac12\,\mathcal Q\big(h'(a)a(1-a)\big)$ 给出。
7. **多窗/软化**:Parseval 紧帧下二阶量可加;BN–Bregman 软化保持极限并赋予李普希茨稳定。
8. **奇性保持**:整个流程仅叠加整/全纯层,工作条带内**不增奇性**、极阶不升。

---

## 结语

本文把 S28 的强型 Szegő–Widom 二阶项与 S29 的 $H^{1/2}$ Hessian 结构,系统延展为**涨落—偏差**三层理论:模高斯(二阶主导、三阶塌缩)、CLT/MDP/LDP(占据统计)与泛函二阶极限/高阶塌缩($H^{1/2}$ 场)。在带限—镜像一致与**有限阶** EM 的纪律下,这些极限均以**相位体积**与**$H^{1/2}$ 能量**为核心刻度,并与多窗拼接、软化优化及阈值几何一致,为随后的"边缘奇性(Fisher–Hartwig)—非齐次/变系数—算子级最优设计"的深入研究提供了坚实而可检的基线。
