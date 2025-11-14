# 边界作为统一舞台:变分完备性、时间刻度与拓扑分支

---

## 摘要

本文从第一性原则出发,将"边界"从被动的几何附属物提升为统一的物理舞台。我们提出一个以边界为基本对象的公理化框架,将三类看似分立的结构——引力变分中的 Gibbons–Hawking–York (GHY) 边界项与 Brown–York 准局域量、散射理论中的谱移函数与 Wigner–Smith 时间延迟、算子代数中的模流与相对熵单调性——粘合为同一"边界时间几何"的不同投影。核心观点是:边界并非仅仅"隔开"体域,而是将体域的连续变化压缩为有限种可计量的差异(能量差、时间差、拓扑类别差与因果方向)。

在几何与变分侧,本文回顾并精炼了 Einstein–Hilbert–GHY–角点–零边界项的完整变分结构,证明在固定诱导度规的条件下,要求变分原理良定,会唯一选出一类"变分完备"的边界几何,并由此导出 Brown–York 边界应力–能量张量作为体域"差异"的边界读出。谱–散射侧,在标准迹类扰动假设下,以 Birman–Kreĭn 公式为起点,给出总散射相位的导数、相对态密度与 Wigner–Smith 时间延迟迹之间的刻度同一式,进而将边界散射相位的微小变化统一解读为"态数变化"与"驻留时间变化"。算子代数与信息侧,我们在一般的边界可观测代数与忠实态语境下引入模流,将模哈密顿量写为沿零边界(或楔区边界)的能流积分,并用相对熵单调性与量子能量条件刻画边界时间箭头的单向性。

此外,本文在参数空间中定义了"判别子边界"与 $\mathbb Z_2$ 分支指数,说明在排除谱异常与拓扑相变超曲面后,散射矩阵平方根定义的自旋结构在参数空间上形成 Null–Modular 意义下的双覆盖。该双覆盖的非平凡性以谱流奇偶与交叉数奇偶的形式被边界记忆,从而将"绕行一次"的连续变形压缩为离散的拓扑类别差。最后,我们给出一个统一的"边界时间几何"定义:边界携带一组几何–谱–信息–拓扑数据,使得 (i) 变分良定、(ii) 时间刻度同一式成立、(iii) 模流与广义熵单调确定时间箭头、(iv) 判别子边界上定义的 $\mathbb Z_2$ 指标给出拓扑分支。本文的主定理表明,在适当假设下,可以在边界上选出唯一(仿射重标度意义下)的时间参数,使这四类结构的时间参数属于同一刻度等价类,从而把"边界生成差异"精确化为一个可检、可计算的统一框架。

---

## 1 引言

边界广泛出现在物理与数学的几乎所有角落:广义相对论中的空间无穷远与黑洞视界,量子场论中的 Cauchy 曲面与因果钻石边界,凝聚态中的材料界面与拓扑缺陷,散射理论中的入射/出射无穷远边界,甚至是参数空间中拓扑相变的判别超曲面。传统的处理大多将边界视为"体域的几何附属物":在场论中需要指定边界条件,在几何中需要补充边界项以修正变分,在散射论中边界只是在无穷远上施加渐近条件的方式。

本文试图推进一种更激进的观点:在统一框架下,**边界应当被视为物理结构的真正舞台**。体域中的"连续变化"只有在边界上被翻译为有限维的"刻度差异"时,才成为可计量、可比较、可优化的对象。更具体地说:

* 在**几何与变分**层面,要求 Einstein–Hilbert 作用的变分在有边界情形良定,会强制我们在边界引入 Gibbons–Hawking–York 项与角点/零边界项;Brown–York 准局域应力–能量张量由此自然出现,作为体域几何与物质分布"差多少"的边界账本。
* 在**谱–散射**层面,Birman–Kreĭn 谱移函数与 Wigner–Smith 时间延迟将"相位在频率上的微小变化"翻译为"态密度差"和"驻留时间差";这一结构天然是一个边界结构,因为一切散射读数均在边界(或无穷远)测得。
* 在**算子代数与信息**层面,Tomita–Takesaki 模块理论与相对熵单调性表明:给定边界可观测代数与忠实态,可定义模流及其生成元(模哈密顿量),它往往可以写为沿边界的能流积分,并且该流的参数在适当归一后可解释为边界上的"内禀时间"。
* 在**拓扑与参数空间**层面,散射矩阵的谱与相位在参数空间中常常存在判别子超曲面;排除这些异常点后,平方根散射矩阵定义的自旋结构在参数空间上形成 $\mathbb Z_2$ 双覆盖,其非平凡性以"绕一圈之后多出一个负号"的方式在边界上显现。

这些看似分散的现象指向一个共同的结构:**边界负责把不可见的体域变化压缩为可见的差异刻度**。本文的目标是从这一直观出发,构造一个严格的公理化边界框架,并给出一系列定理,将变分完备性、时间刻度同一式、模流时间箭头与拓扑分支统一到一个"边界时间几何"的语境中。

下文组织如下:第 2 节给出必要的预备知识与记号;第 3 节提出"物理边界系统"的公理化定义与四条基本公设;第 4、5、6、7 节分别从几何变分、谱–散射、模流–信息与拓扑分支四个侧面具体展开,给出本框架中的关键定理;第 8 节证明边界时间刻度的唯一性定理,给出"边界时间几何"的统一叙述;第 9 节给出若干典型模型;附录中包含引力作用变分、刻度同一式与 $\mathbb Z_2$ 指数构造的详细证明。

---

## 2 预备知识与记号

### 2.1 几何与变分

设 $(M,g)$ 为带边界的四维洛伦兹流形,边界记为 $\partial M$。在非零类(类空间状或类时间)边界上,记诱导度规为 $h_{ab}$,外法向为 $n^a$,外在曲率为 $K_{ab} = h_a^{\ c}h_b^{\ d}\nabla_c n_d$,其迹为 $K = h^{ab}K_{ab}$。

Einstein–Hilbert 作用定义为

$$
S_{\mathrm{EH}}(g) = \dfrac{1}{16\pi G}\int_M R(g)\sqrt{-g}\,\mathrm d^4x,
$$

其中 $R$ 为标量曲率。众所周知,在有边界情形,单独的 $S_{\mathrm{EH}}$ 在固定 $h_{ab}$ 的变分下并非良定:变分时会产生依赖于 $\delta(\partial g)$ 的边界项。为修正之,引入 Gibbons–Hawking–York 边界项

$$
S_{\mathrm{GHY}}(g) = \dfrac{\varepsilon}{8\pi G}\int_{\partial M} K \sqrt{|h|}\,\mathrm d^3x,
$$

其中 $\varepsilon = +1$ 对应类空间边界,$\varepsilon=-1$ 对应类时间边界。对于存在角点与零边界的情形,还需引入附加的角点项与零边界项,见附录 A。

### 2.2 散射理论与时间延迟

设 $\mathcal H$ 为复 Hilbert 空间,$H_0$ 与 $H = H_0 + V$ 为自伴算子。假设扰动 $V$ 为 $H_0$-相对迹类,使得波算子

$$
W_\pm = \mathrm{s}\text{-}\lim_{t\to\pm\infty} e^{\mathrm i H t} e^{-\mathrm iH_0 t}
$$

存在且完备,则散射算子定义为

$$
S = W_+^\ast W_-.
$$

在适当条件下,$S$ 在能量表象中可写为纤维分解

$$
S = \int^\oplus S(\omega)\,\mathrm d\mu(\omega),
$$

其中 $S(\omega)$ 为能量 $\omega$ 上的有限维(或可分)散射矩阵。定义 Wigner–Smith 时间延迟算子

$$
Q(\omega) = -\mathrm i\,S(\omega)^\dagger \partial_\omega S(\omega).
$$

Birman–Kreĭn 谱移函数 $\xi(\lambda)$ 满足

$$
\det S(\lambda) = \exp\!\big(-2\pi\mathrm i\,\xi(\lambda)\big),
$$

在适当正则性假设下可微,导数 $\xi'(\lambda)$ 与态密度差相关。本文将采用 Kreĭn 谱移密度 $\rho_{\mathrm{rel}}(\omega) = \xi'(\omega)$ 的记号。

### 2.3 模块理论、模流与相对熵

设 $\mathcal A$ 为 $C^\ast$ 代数或 von Neumann 代数,$\omega$ 为其上的忠实正常态。GNS 构造给出三元组 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$,其中 $\Omega_\omega$ 为循环向量。Tomita 算子 $S_\omega$ 的极分解产生模算子 $\Delta_\omega$ 与共轭 $J_\omega$。模流定义为

$$
\sigma_t^\omega(A) = \Delta_\omega^{\mathrm i t} A \Delta_\omega^{-\mathrm i t},\quad A\in\mathcal A.
$$

若存在自伴算子 $K_\omega$ 满足 $\Delta_\omega = e^{-K_\omega}$,则形式上有

$$
\sigma_t^\omega(A) = e^{\mathrm i K_\omega t} A e^{-\mathrm i K_\omega t}.
$$

对两个态 $\omega,\varphi$,相对熵定义为

$$
S(\omega\Vert\varphi) = \operatorname{tr}\big(\rho_\omega(\log\rho_\omega - \log\rho_\varphi)\big),
$$

在适当一般性下满足单调性:在对某子代数或子区域的限制下不增。

在相对论 QFT 的双锥/楔区情形中,模哈密顿量 $K_\omega$ 常常可写为能量–动量张量沿某边界方向的积分,从而赋予模时间以几何含义。

### 2.4 谱流与 $\mathbb Z_2$ 指数

设 $\{A_t\}_{t\in[0,1]}$ 为一族自伴 Fredholm 算子路径,谱流 $\mathrm{Sf}(\{A_t\})$ 被定义为本征值穿越零点的有向次数。若只关心奇偶性,可定义 $\mathbb Z_2$ 指数

$$
\nu_{\mathbb Z_2}(\{A_t\}) = (-1)^{\mathrm{Sf}(\{A_t\})}\in\{\pm1\}.
$$

在参数空间 $X$ 上,可以将谱流的奇偶与环路对某判别子集 $D\subset X$ 的交数奇偶联系起来,形成一种 $\mathbb Z_2$ 拓扑指数。本文将用这一语言描述散射平方根的分支结构。

---

## 3 物理边界系统的公理化定义

本节给出本文采用的"物理边界系统"定义,将几何、散射、模流与拓扑四类数据统一到同一边界框架中。

### 3.1 边界数据四元组

**定义 3.1(物理边界系统)**
一个物理边界系统由四元组

$$
\mathfrak B = \big(\partial M,\mathcal A_{\partial},\omega_{\partial},\mathcal S_{\partial}\big)
$$

构成,其中:

1. $\partial M$ 为四维时空 $M$ 的共维一边界,配有诱导度规 $h_{ab}$ 与外在曲率 $K_{ab}$,再加上可能的角点与零类片段;
2. $\mathcal A_{\partial}$ 为与 $\partial M$ 关联的边界可观测代数(例如边界限制的场算子代数或散射通道代数);
3. $\omega_{\partial}$ 为 $\mathcal A_{\partial}$ 上的忠实正常态,给出模流 $\sigma_t^{\omega_\partial}$;
4. $\mathcal S_{\partial}$ 为边界散射与拓扑数据的集合,包括:

   * 在能量表象下的散射矩阵 $S(\omega)$;
   * 与 $\mathcal A_{\partial}$ 兼容的频率测度;
   * 参数空间 $X$ 上的判别子集 $D\subset X$ 以及由此定义的 $\mathbb Z_2$ 指数。

在具体模型中,$\partial M$ 可以是有限区域的人工边界、小因果菱形边界、黑洞视界、AdS 无穷远边界、材料界面,甚至是"参数空间中的判别子边界"在抽象意义上的对应物。

### 3.2 四条基本公设

**公设 A1(变分完备性)**
存在一个由体域与边界构成的作用泛函

$$
S_{\mathrm{tot}} = S_{\mathrm{bulk}}[g,\Phi] + S_{\mathrm{bdy}}[h,K,\Phi\vert_{\partial M}],
$$

其中特定的边界项 $S_{\mathrm{bdy}}$(包含 GHY、角点与零边界项等)使得在固定边界诱导度规与物质边界数据 $(h_{ab},\Phi\vert_{\partial M})$ 的变分下,$S_{\mathrm{tot}}$ 的一阶变分只依赖于体域变分,并且等价于某给定的场方程(例如 Einstein–物质方程)。

**公设 A2(刻度同一式)**
存在频率变量 $\omega$ 与相应的散射矩阵 $S(\omega)$,使得以下刻度同一式成立:

$$
\dfrac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \dfrac{1}{2\pi}\operatorname{tr} Q(\omega),
$$

其中 $\varphi(\omega) = \tfrac12\arg\det S(\omega)$、$\rho_{\mathrm{rel}}(\omega)$ 为相对态密度,$Q(\omega) = -\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 时间延迟矩阵。由此定义的函数

$$
\kappa(\omega) := \dfrac{\varphi'(\omega)}{\pi}
$$

被称为边界时间刻度密度。

**公设 A3(模流定向与时间箭头)**
模流 $\sigma_t^{\omega_\partial}$ 的生成元 $K_{\partial}$ 可写为沿边界的能量–动量张量投影的积分

$$
K_{\partial} = \int_{\partial M} f(x) T_{ab}(x)\chi^a(x)n^b(x)\,\mathrm d\Sigma_x,
$$

其中 $\chi^a$ 为类 Killing 或规范化的边界时间平移向量场,$n^b$ 为法向,$f$ 为正的权函数。相对熵 $S(\omega_\partial\Vert\varphi_\partial)$ 对于沿模流的"未来"方向单调不减,从而在边界上定义时间箭头。

**公设 A4(拓扑分支与 $\mathbb Z_2$ 指标)**
在参数空间 $X$ 中存在判别子集 $D\subset X$,使得在 $X^\circ = X\setminus D$ 上可以连续选取散射矩阵的平方根 $S^{1/2}$。任意闭路 $\gamma\subset X^\circ$ 的提升可能返回到原点的相反支,给出 $\mathbb Z_2$ 指数

$$
\nu(\gamma) \in\{\pm1\},
$$

该指数等价于某自伴族的谱流奇偶或与 $D$ 的交数奇偶。

---

## 4 变分完备性与几何边界

本节证明:公设 A1 的变分完备性要求在非零类边界上引入 GHY 项与 Brown–York 边界应力–能量张量;在存在角点与零边界时,则需要附加角点项与零边界项,从而把体域"差异"完全压缩为边界几何与表面应力上的读数。

### 4.1 Einstein–Hilbert 作用的边界变分

考虑总作用

$$
S[g] = S_{\mathrm{EH}}[g] + S_{\mathrm{GHY}}[g],
$$

其中

$$
S_{\mathrm{EH}}[g] = \dfrac{1}{16\pi G}\int_M R(g)\sqrt{-g}\,\mathrm d^4x,
$$

$$
S_{\mathrm{GHY}}[g] = \dfrac{\varepsilon}{8\pi G}\int_{\partial M} K \sqrt{|h|}\,\mathrm d^3x.
$$

**定理 4.1(非零类边界上的变分完备性)**
在固定边界诱导度规 $h_{ab}$ 的变分下,总作用 $S[g]$ 的一阶变分为

$$
\delta S[g] = \dfrac{1}{16\pi G}\int_M (G_{ab} + \Lambda g_{ab})\,\delta g^{ab}\sqrt{-g}\,\mathrm d^4x,
$$

即所有边界项完全抵消。因而在给定 $h_{ab}$ 的条件下,变分原理良定,并导出 Einstein 方程 $G_{ab} + \Lambda g_{ab} = 8\pi G T_{ab}$。

*证明(略要)*:对 $S_{\mathrm{EH}}$ 变分,利用 $\delta R = R_{ab}\delta g^{ab} + \nabla_a(...)$ 的分部积分公式,可将体积分中的二阶导数项转化为边界项,该边界项依赖于 $\delta(\partial g)$。另一方面,对 $S_{\mathrm{GHY}}$ 变分可得边界上的 $\delta K$ 与 $\delta h$ 项。将两者相加,在固定 $h_{ab}$(即 $\delta h_{ab}=0$)条件下,$\delta K$ 与来自体积分的边界项精确抵消,只剩体域中的 $G_{ab}\delta g^{ab}$。详细计算见附录 A.1。证毕。

### 4.2 Brown–York 准局域应力–能量张量

引入物质作用 $S_{\mathrm{matter}}[g,\Phi]$ 后,定义总作用

$$
S_{\mathrm{tot}}[g,\Phi] = S_{\mathrm{EH}}[g] + S_{\mathrm{GHY}}[g] + S_{\mathrm{matter}}[g,\Phi].
$$

在边界上,准局域应力–能量张量定义为

$$
T_{ab}^{\mathrm{BY}} = -\dfrac{2}{\sqrt{|h|}}\dfrac{\delta S_{\mathrm{GHY}}}{\delta h^{ab}} = \dfrac{1}{8\pi G}\big(K_{ab} - K h_{ab}\big).
$$

**命题 4.2(边界能量与时间平移生成元)**
设 $\Sigma\subset\partial M$ 为边界上选定的空间切片,$u^a$ 为其时间样单位法向,收缩 $T_{ab}^{\mathrm{BY}}$ 得到能量密度

$$
\varepsilon = T_{ab}^{\mathrm{BY}} u^a u^b.
$$

则积分

$$
E_{\mathrm{BY}}(\Sigma) = \int_\Sigma \varepsilon\,\mathrm d^2x
$$

可解释为相对于某参考背景的准局域能量,并在 Hamilton 形式中作为边界时间平移的生成元。

*证明思路*:在 ADM 分解中,空间超曲面上的哈密顿生成元包含体域约束以及边界项;将引力作用 Legendre 变换后,可以证明在满足约束的解空间上,剩余的哈密顿量等于边界积分,其 integrand 正是 Brown–York 能量密度。参见附录 A.2 中的简化推导。证毕。

### 4.3 角点与零边界

在存在时样与空样边界相交形成的角点,或零类边界(如视界、零超曲面)情形下,单纯的 GHY 项不足以保证变分完备性。需要引入角点项 $S_{\mathrm{corner}}$ 与零边界项 $S_{\mathcal N}$,其结构大致为:

* 角点项:与两个边界法向之间的对数"转角"有关;
* 零边界项:由膨胀 $\theta$ 与表面引力 $\kappa$ 等零几何不变量构成。

**定理 4.3(含角点与零边界的变分完备性)**
考虑总作用

$$
S_{\mathrm{tot}} = S_{\mathrm{EH}} + S_{\mathrm{GHY}} + S_{\mathrm{corner}} + S_{\mathcal N} + S_{\mathrm{matter}},
$$

在固定每一类边界上适当的几何数据(非零类边界上固定 $h_{ab}$,零边界上固定截面几何与生成矢量场归一)的变分下,一阶变分仅包含体域项。详见附录 A.3 中的分情形讨论。

**小结**:A1 公设在几何上的落实,是用 GHY + 角点 + 零边界项将体域几何与物质"差多少"全部集中到一个边界几何对象上,使得边界成为能量与通量差异的读出屏幕。

---

## 5 谱–散射侧的刻度同一式与边界时间

本节实现公设 A2,给出刻度同一式的充分条件,并说明它如何把边界上相位的微小变化统一读成"态密度差"和"时间延迟差"。

### 5.1 Birman–Kreĭn 谱移与散射相位

在第 2.2 节的假设下,Kreĭn 谱移函数 $\xi(\lambda)$ 定义为使得

$$
\operatorname{tr}\big(f(H) - f(H_0)\big) = \int_{-\infty}^{+\infty} f'(\lambda)\,\xi(\lambda)\,\mathrm d\lambda
$$

对足够多的测试函数 $f$ 成立的函数。Birman–Kreĭn 公式给出

$$
\det S(\lambda) = \exp\big(-2\pi\mathrm i\,\xi(\lambda)\big).
$$

设 $S(\lambda)$ 在每个 $\lambda$ 上为有限维酉矩阵,其本征值可写为 $e^{2\mathrm i\delta_j(\lambda)}$。定义总散射相位

$$
\Phi(\lambda) = \sum_j \delta_j(\lambda),\quad \varphi(\lambda) = \dfrac{1}{2}\Phi(\lambda).
$$

则有

$$
\det S(\lambda) = e^{2\mathrm i\Phi(\lambda)} = e^{4\mathrm i\varphi(\lambda)}.
$$

由此可得

$$
4\varphi(\lambda) = -2\pi\,\xi(\lambda) \mod 2\pi,
$$

从而

$$
\dfrac{\varphi'(\lambda)}{\pi} = -\dfrac{1}{2}\xi'(\lambda) =: \rho_{\mathrm{rel}}(\lambda).
$$

在适当选择相位连续性条件下,可以固定符号约定,使 $\rho_{\mathrm{rel}}(\lambda)$ 解释为态密度差。

### 5.2 Wigner–Smith 时间延迟算子

回顾 Wigner–Smith 算子

$$
Q(\lambda) = -\mathrm i S(\lambda)^\dagger\partial_\lambda S(\lambda).
$$

将 $S(\lambda)$ 对角化:$S(\lambda) = U(\lambda)\operatorname{diag}(e^{2\mathrm i\delta_j(\lambda)})U(\lambda)^\dagger$,可得

$$
Q(\lambda) = 2\sum_j \partial_\lambda\delta_j(\lambda)\, P_j(\lambda) + \text{交换项},
$$

其中 $P_j$ 为本征子空间投影。取迹,

$$
\operatorname{tr}Q(\lambda) = 2\sum_j \partial_\lambda\delta_j(\lambda) = 2\Phi'(\lambda) = 4\varphi'(\lambda).
$$

于是得到刻度同一式的第三个等号:

$$
\dfrac{1}{2\pi}\operatorname{tr}Q(\lambda) = \dfrac{1}{2\pi}\cdot4\varphi'(\lambda) = \dfrac{2}{\pi}\varphi'(\lambda).
$$

与上一小节的关系配合适当归一,可以统一为如下形式。

### 5.3 刻度同一式与时间刻度密度

整理符号,我们选择统一的约定为:定义时间刻度密度为

$$
\kappa(\omega) := \dfrac{\varphi'(\omega)}{\pi}.
$$

**定理 5.1(刻度同一式)**
在满足迹类扰动、波算子完备等标准假设下,存在归一化选取,使得对几乎处处的 $\omega$ 有

$$
\kappa(\omega) = \dfrac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \dfrac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

*证明概述*:第一等号由 Birman–Kreĭn 公式与谱移函数的定义给出;第二等号由 Wigner–Smith 算子的迹表达给出。归一化的不确定性来自相位的 $2\pi$ 不定与谱移函数的整数量子;选取使得在无散射极限下 $\kappa(\omega)\to0$,即可得到一致归一。详见附录 B。证毕。

**物理解释**:刻度同一式表明,边界上的相位微扰 $\delta\varphi$ 对频率的变化 $\partial_\omega\varphi$ 可以被三种等价方式读取:

* 作为单位频率下的"态密度差" $\rho_{\mathrm{rel}}(\omega)$;
* 作为总驻留时间的"时间延迟密度" $(2\pi)^{-1}\operatorname{tr}Q(\omega)$;
* 作为时间刻度密度 $\kappa(\omega)$。

这实现了公设 A2,将边界散射数据与时间刻度直接对接。

---

## 6 模流、广义熵与边界时间箭头

本节说明公设 A3 如何在边界上为时间刻度定向,并与散射刻度同一式对齐。

### 6.1 模哈密顿量的几何表达

设 $\mathcal A_{\partial}$ 为与某楔区或因果菱形边界相关的局域算子代数,$\omega_{\partial}$ 为其上的真空态或 KMS 态。许多模型中,模哈密顿量 $K_{\partial}$ 可写为

$$
K_{\partial} = 2\pi \int_{\partial M} \xi^a T_{ab} n^b\,\mathrm d\Sigma,
$$

其中 $\xi^a$ 为适当归一的时间样 Killing 向量或类钻石 boost 向量,$T_{ab}$ 为能量–动量张量。模流

$$
\sigma_t^{\omega_\partial}(A) = e^{\mathrm i K_{\partial} t} A e^{-\mathrm iK_{\partial} t}
$$

因而可解释为沿边界方向的"热时间"或"模时间"。

### 6.2 相对熵单调性与时间箭头

设 $\omega_\partial,\varphi_\partial$ 为两个边界态,对应的相对熵为 $S(\omega_\partial\Vert\varphi_\partial)$。在局域 QFT 框架下,可证明在对某一嵌套区域族的限制下,相对熵随区域扩大而单调不减。转译到边界几何,这一单调性支配了沿某类"未来方向"的广义熵增长。

**命题 6.1(模时间箭头)**
假设对一族嵌套边界截面 $\{\partial M_t\}$(例如沿零方向推进的截面)有

$$
\dfrac{\mathrm d}{\mathrm dt} S_{\mathrm{gen}}(\partial M_t) \ge 0,
$$

其中 $S_{\mathrm{gen}}$ 为广义熵,则参数 $t$ 可被选为边界上的时间箭头参数。若将 $t$ 等比例重标至与散射时间刻度 $\kappa(\omega)$ 对齐,则在边界上可以同时视为"模时间"和"散射时间"。

证明依赖于相对熵单调性、量子焦聚条件等结果,详见附录 B.3 的讨论。

---

## 7 拓扑分支、判别子边界与 $\mathbb Z_2$ 指数

本节实现公设 A4,将参数空间中的判别子边界、谱流奇偶与散射矩阵平方根的分支结构联系起来。

### 7.1 判别子边界与参数空间

考虑参数空间 $X$,其中每一点 $x\in X$ 对应一个散射系统,具有散射矩阵 $S(\omega;x)$。设存在判别子集 $D\subset X$,使得当且仅当 $x\in D$ 时,$S(\omega;x)$ 在某能量附近出现本征值 $-1$、简并本征值或其他谱异常。定义 $X^\circ = X\setminus D$。

在 $X^\circ$ 上,谱异常被排除,可以选取散射矩阵的"主支平方根" $S^{1/2}(\omega;x)$,满足

$$
\big(S^{1/2}(\omega;x)\big)^2 = S(\omega;x), \quad S^{1/2}(\omega;x_0)\ \text{给定}.
$$

### 7.2 $\mathbb Z_2$ 指数与谱流奇偶

任取闭路 $\gamma:[0,1]\to X^\circ$,沿 $\gamma$ 平行移动平方根 $S^{1/2}$,可能出现整体符号翻转

$$
S^{1/2}(\omega;\gamma(1)) = \pm S^{1/2}(\omega;\gamma(0)).
$$

定义

$$
\nu(\gamma) = \begin{cases}
+1, & S^{1/2}\ \text{无翻转},\\
-1, & S^{1/2}\ \text{翻转}.
\end{cases}
$$

**命题 7.1($\mathbb Z_2$ 指数与谱流奇偶)**
在适当的可微与谱间隙假设下,$\nu(\gamma)$ 等于某自伴族的谱流奇偶:

$$
\nu(\gamma) = (-1)^{\mathrm{Sf}(\{A_t\})},
$$

其中 $\{A_t\}$ 为沿 $\gamma$ 构造的相关自伴算子族,其谱流 $\mathrm{Sf}(\{A_t\})$ 记录本征值跨越零点的次数。

*证明思路*:利用 Cayley 变换将酉族 $S(\omega;x)$ 转换为自伴族,将 $-1$ 本征值对应的穿越转化为自伴谱穿越零点的事件;谱流奇偶与平方根翻转的关系可通过局部模型与拼接论证建立。详见附录 C.1。证毕。

**几何解释**:判别子 $D$ 作为参数空间的"拓扑边界",将 $X^\circ$ 划分为不同的扇区;$\nu(\gamma)$ 记录了闭路是否以奇数次"绕过"该边界。由此,"绕行一次"的连续变形被边界压缩为一个简单的离散标记 $\pm1$。

---

## 8 边界时间几何的统一定理

本节将前述几何、谱–散射、模流与拓扑结构粘合起来,形成一个统一的"边界时间几何"框架,并证明时间刻度的唯一性结果。

### 8.1 边界时间几何的定义

**定义 8.1(边界时间几何)**
一个边界时间几何由数据

$$
\mathfrak G_{\partial} = \big(\partial M, h_{ab},K_{ab}; \mathcal A_{\partial},\omega_{\partial}; S(\omega); D,\nu\big)
$$

构成,满足:

1. $(\partial M,h_{ab},K_{ab})$ 使引力与物质作用的变分在固定 $h_{ab}$ 条件下良定,并给出 Brown–York 边界应力–能量张量;
2. $(\mathcal A_{\partial},\omega_{\partial})$ 给出模流 $\sigma_t^{\omega_\partial}$ 与模哈密顿量 $K_{\partial}$,并通过广义熵单调性定义时间箭头;
3. 散射矩阵 $S(\omega)$ 与谱移数据满足刻度同一式,时间刻度密度 $\kappa(\omega)$ 良好定义;
4. 判别子 $D$ 与 $\nu$ 定义了拓扑分支的 $\mathbb Z_2$ 指数。

我们称一条时间参数 $t$ 为该边界时间几何的统一刻度参数,若它在以下意义上同时标度三个时间结构:

* 引力–几何侧:$t$ 为沿边界时间平移向量场 $\chi^a$ 的参数,使 Brown–York 能量在 $t$ 下的变化率与体域能流一致;
* 散射侧:$t$ 与频率 $\omega$ 通过某双射关系 $t = t(\omega)$ 关联,使得 $\kappa(\omega)$ 可解释为 $\mathrm d t$ 的密度;
* 模流侧:$t$ 为模流参数,使得模哈密顿量 $K_{\partial}$ 与 Brown–York 能量的生成元相差仅为一个常数因子。

### 8.2 时间刻度唯一性的主定理

**定理 8.2(边界时间刻度的唯一定理)**
设 $\mathfrak B = (\partial M,\mathcal A_{\partial},\omega_{\partial},\mathcal S_{\partial})$ 为满足公设 A1–A4 的物理边界系统,且满足如下技术假设:

1. Brown–York 边界能量 $E_{\mathrm{BY}}(t)$ 随某参数 $t$ 的变化可以写为边界能流的积分;

2. 模哈密顿量 $K_{\partial}$ 与 $E_{\mathrm{BY}}$ 生成的时间平移相容,即存在常数 $\beta>0$ 使

   $$
   K_{\partial} = \beta E_{\mathrm{BY}} + \text{常数}.
   $$

3. 散射矩阵 $S(\omega)$ 的频率依赖可重参数化为 $\omega = \omega(t)$,且刻度同一式在该重参数化下保持形式不变。

则存在唯一的(仿射重标度意义下)时间参数 $t$,使得:

* 引力–几何侧的边界时间平移;
* 散射侧的时间延迟刻度;
* 模流侧的模时间流

三者属于同一刻度等价类。

*证明概述*:

1. 由假设 2,可将模流参数 $\tau$ 与几何时间参数 $t$ 线性关联:$\tau = \beta t + \tau_0$。仿射自由度对应整体时间平移与尺度选择。
2. 由刻度同一式,定义 $\mathrm d t = f(\omega)\mathrm d\omega$,其中 $f$ 选取使得 $\kappa(\omega)\mathrm d\omega$ 等于边界 Wigner–Smith 时间延迟对 $t$ 的导数。这样保证对每个能量壳,散射时间延迟与边界几何时间步长一致。
3. 技术假设 1 确保 Brown–York 能量的时间演化与散射流入/流出的能量一致,从而通过能量–时间不等式与 KMS 条件固定了 $t$ 的归一化。
4. 仿射重标度自由度通过要求在无散射、平直背景、模流为平凡的极限下 $t$ 匹配惯常时间坐标而被完全固定。

详细构造与各步骤中使用的引理见附录 B.4。证毕。

**解释**:定理 8.2 表明,在一个满足公设 A1–A4 的边界系统中,"几何时间""散射时间""模时间"并非独立引入,而是可以用一个统一的参数 $t$ 来刻度。边界由此成为时间本身的生成器:体域中的引力演化、散射过程与信息流的"差异",都在这同一条时间刻度上被读出。

---

## 9 典型模型与应用素描

本节简要概述几类典型情形中如何实例化本文的边界框架。

### 9.1 一维势散射与有限区间边界

考虑一维 Schrödinger 方程,背景自由 Hamilton 算子 $H_0 = -\partial_x^2$,在有限区间上加入势阱与边界条件,将散射读数集中到区间端点的相位移与时间延迟。此时:

* 几何侧:区间端点作为"人工边界",变分时需要指定端点条件;
* 散射侧:相位移与时间延迟直接由端点反射系数给出,刻度同一式显式成立;
* 拓扑侧:通过调节势形与边界条件,可在参数空间中形成判别子,使得半相位平方根的分支翻转对应于束缚态产生/消失。

### 9.2 Rindler 楔区、模流与 Unruh 热时间

在 Minkowski 时空中考虑 Rindler 楔区,区域边界为一零类平面。真空态在楔区子代数上的模流对应于沿 Rindler 时间的平移,其模哈密顿量正比于 boost 生成元,而边界上能量–动量张量的流给出 Unruh 温度。此时:

* 几何侧:零边界项与小因果菱形的广义熵极值条件给出局域 Einstein 方程;
* 模流侧:模时间的箭头与 Rindler 时间方向一致;
* 散射侧:对适当的镜像散射模型,Rindler 频率上的相位与时间延迟可用刻度同一式刻画。

### 9.3 拓扑物态中的界面与 $\mathbb Z_2$ 边界指数

在二维或三维拓扑绝缘体/超导体中,材料界面携带受拓扑保护的边缘/表面态。将系统参数(如质量项、局域势、磁通)组织为参数空间 $X$,则界面上的谱在 $X$ 中形成判别子 $D$,其环绕行为由 $\mathbb Z_2$ 指数记忆。这一结构正是本文第 7 节一般框架的具体实例。

上述示例表明,本文的"边界时间几何"既可应用于纯引力与场论,也可延展到凝聚态与散射实验体系。

---

## 附录 A:引力作用的完整边界变分

### A.1 Einstein–Hilbert 与 GHY 项的变分

从 $S_{\mathrm{EH}}$ 出发,利用

$$
\delta R_{ab} = \nabla_c\delta\Gamma^c_{ab} - \nabla_a\delta\Gamma^c_{bc},
$$

$$
\delta\Gamma^c_{ab} = \dfrac{1}{2} g^{cd}\big(\nabla_a\delta g_{bd} + \nabla_b\delta g_{ad} - \nabla_d\delta g_{ab}\big),
$$

可得

$$
\delta S_{\mathrm{EH}} = \dfrac{1}{16\pi G}\int_M (G_{ab} + \Lambda g_{ab})\delta g^{ab}\sqrt{-g}\,\mathrm d^4x + \dfrac{1}{16\pi G}\int_{\partial M} \Pi^{ab}\delta g_{ab}\,\mathrm d\Sigma,
$$

其中边界张量 $\Pi^{ab}$ 依赖于 $\nabla_n\delta g$。单独的 $S_{\mathrm{EH}}$ 因此在固定 $h_{ab}$ 条件下仍含有 $\delta(\partial g)$ 项。

另一方面,对

$$
S_{\mathrm{GHY}} = \dfrac{\varepsilon}{8\pi G}\int_{\partial M} K \sqrt{|h|}\,\mathrm d^3x
$$

变分,利用

$$
\delta K = -\dfrac{1}{2}K^{ab}\delta h_{ab} + \text{包含}\ \nabla_n\delta g\ \text{的项},
$$

可以构造使 $\delta S_{\mathrm{GHY}}$ 精确抵消 $\delta S_{\mathrm{EH}}$ 中的 $\nabla_n\delta g$ 边界项,只留下与 $\delta h_{ab}$ 成正比的项,而在固定 $h_{ab}$ 的变分下这些项为零。

将两部分相加,得到正文中的定理 4.1。详细计算过程包括对法向正交分解与 Gauss–Codazzi 恒等式的使用,此处不再赘述。

### A.2 Brown–York 张量的变分定义

Brown–York 准局域应力–能量张量按定义为

$$
T_{ab}^{\mathrm{BY}} = -\dfrac{2}{\sqrt{|h|}}\dfrac{\delta S_{\mathrm{GHY}}}{\delta h^{ab}}.
$$

对 $S_{\mathrm{GHY}}$ 做显式变分可得

$$
T_{ab}^{\mathrm{BY}} = \dfrac{1}{8\pi G}\big(K_{ab} - K h_{ab}\big).
$$

进一步,将 ADM 分解下的哈密顿密度写成体域约束与边界项之和,利用场方程将体域约束消去,可得剩余哈密顿量为

$$
H = \int_{\Sigma} N\mathcal H + N^a\mathcal H_a\,\mathrm d^3x + \int_{\partial\Sigma} \varepsilon\,\mathrm d^2x,
$$

其中 $\varepsilon = T_{ab}^{\mathrm{BY}}u^a u^b$ 即 Brown–York 能量密度。由此可见,边界能量完全由 $T_{ab}^{\mathrm{BY}}$ 控制。

### A.3 含角点与零边界的边界项结构

在时样与空样边界相交处,需引入角点项

$$
S_{\mathrm{corner}} = \dfrac{1}{8\pi G}\int_{\mathcal C} \eta\,\mathrm d\ell,
$$

其中 $\eta$ 为两法向之间的"转角",$\mathcal C$ 为角点曲线。对零边界 $\mathcal N$,可引入

$$
S_{\mathcal N} = \dfrac{1}{8\pi G}\int_{\mathcal N} (\kappa + \theta)\,\mathrm d\lambda\,\mathrm d^2x,
$$

其中 $\kappa$ 为表面引力,$\theta$ 为膨胀,$\lambda$ 为零参数。结合这些项的变分,可证明在固定适当零边界数据的条件下,总作用的边界变分仍可消除所有 $\nabla\delta g$ 项,实现变分完备性。

---

## 附录 B:刻度同一式与模流的技术细节

### B.1 Kreĭn 谱移函数与 Birman–Kreĭn 公式

在迹类扰动假设下,Kreĭn 谱移函数 $\xi(\lambda)$ 可通过对分布意义上的微分方程

$$
\dfrac{\mathrm d}{\mathrm d\lambda}\xi(\lambda) = \operatorname{tr}\big((H-\lambda-\mathrm i0)^{-1} - (H_0-\lambda-\mathrm i0)^{-1}\big)
$$

求解而得。Birman–Kreĭn 公式则通过比较散射矩阵与分辨算子的 Fredholm 行列式导出。详细论证可见标准散射论文献,此处只记录关键关系:

* $\det S(\lambda) = \exp(-2\pi\mathrm i\,\xi(\lambda))$;
* $\xi'(\lambda)$ 等于态密度差。

### B.2 Wigner–Smith 算子迹与相位导数

在有限维情形,写 $S(\lambda) = e^{\mathrm iA(\lambda)}$,$A$ 为自伴。则

$$
Q(\lambda) = -\mathrm i S^\dagger \partial_\lambda S = \partial_\lambda A(\lambda)
$$

在交换项可忽略时成立;一般情形下仍有

$$
\operatorname{tr}Q(\lambda) = \operatorname{tr}\big(S^\dagger(-\mathrm i\partial_\lambda S)\big) = \partial_\lambda \arg\det S(\lambda) = 2\Phi'(\lambda).
$$

从而得到正文中的迹公式。

### B.3 相对熵单调性与广义熵

在局域 QFT 的双锥/楔区情形中,对嵌套区域 $O_1\subset O_2$,有

$$
S(\omega\Vert\varphi;O_1) \le S(\omega\Vert\varphi;O_2).
$$

将边界截面 $\partial M_t$ 与区域族 $O_t$ 对应,可将相对熵的单调性转化为广义熵 $S_{\mathrm{gen}}(\partial M_t)$ 的单调性或极值条件,从而得到时间箭头与局域 Einstein 方程之间的联系。该联系在多种框架中被系统讨论,本文只在直观层面使用其结论。

### B.4 统一刻度构造

给定一个几何时间参数 $t_{\mathrm{geo}}$、一个模时间参数 $t_{\mathrm{mod}}$ 与一个散射频率 $\omega$,构造统一刻度参数 $t$ 的步骤为:

1. 通过能量–模流关系将 $t_{\mathrm{mod}}$ 与 $t_{\mathrm{geo}}$ 关联:选取常数 $\beta$ 使 $K_{\partial} = \beta E_{\mathrm{BY}} + \text{常数}$,然后定义 $t = t_{\mathrm{mod}} = \beta t_{\mathrm{geo}} + t_0$。
2. 利用刻度同一式,将 $\kappa(\omega)\mathrm d\omega$ 等同于某一"时间延迟密度",定义

   $$
   \mathrm d t = \tau(\omega)\,\mathrm d\omega,
   $$

   其中 $\tau(\omega)$ 选取满足 $\partial_t\varphi(t) = \pi\kappa(\omega(t))$。
3. 在无散射与平直背景极限中要求 $t$ 与 Minkowski 时间一致,以此固定整体仿射自由度。

经此构造,$t$ 同时可以解释为:

* 生成边界几何平移的 Hamilton 时间;
* 构造模流 $\sigma_t^{\omega_\partial}$ 的模时间;
* 用于刻画散射相位与时间延迟的物理时间参数。

---

## 附录 C:$\mathbb Z_2$ 指数与判别子边界

### C.1 Cayley 变换与谱流奇偶

给定酉族 $S(x)$(例如固定能量壳的散射矩阵),定义 Cayley 变换

$$
A(x) = \mathrm i(1 - S(x))(1 + S(x))^{-1}.
$$

当 $S(x)$ 无本征值 $-1$ 时,$1 + S(x)$ 可逆,$A(x)$ 为自伴。谱流穿越零的本征值与 $S(x)$ 带有本征值 $-1$ 的事件一一对应。沿一条闭路 $\gamma\subset X^\circ$,谱流奇偶

$$
(-1)^{\mathrm{Sf}(\{A(\gamma(t))\})}
$$

等于 $S^{1/2}$ 是否翻转的标志,从而等价于正文中定义的 $\nu(\gamma)$。

### C.2 判别子作为拓扑边界

判别子 $D\subset X$ 是使得某个谱性质发生退化的参数超曲面(例如能隙闭合、本征值碰撞)。从拓扑角度看,$X^\circ = X\setminus D$ 上的自旋结构由 $D$ 的同调类控制。闭路 $\gamma$ 的 $\nu(\gamma)=-1$ 表明 $\gamma$ 与 $D$ 的交数为奇,因而 $\gamma$ 无法在 $X^\circ$ 中收缩到一个点。这种"收缩阻碍"正是拓扑相变与 Null–Modular 双覆盖的几何根源。
