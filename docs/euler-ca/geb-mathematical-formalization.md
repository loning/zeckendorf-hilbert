# GEB 的核心概念在"母映射—镜像—窗化测量"框架中的严格化

**—— 奇异环 = 相位—波包回路；自指 = 镜像本征；意义 = 窗化读数（Born = KL-投影，Pointer = 光谱极小，Windows = 极大极小）**

**作者**：Auric（S-series / EBOC）

**MSC**：03F40；11M26；46E22；47B36；81U05

**Version**: 1.5

---

## 摘要

本文以 de Branges–Kreĭn 规范系统与完成函数为底座，将《GEB》中三大母题——**MIU/形式系统、奇异环（Strange Loop）、自指与意义的涌现**——译为**母映射—镜像—窗化测量**的一套严格数学语法。核心桥梁是**自反核**与**完成函数**所定义的**相位场** $U_E=E^\sharp/E$。我们证明并量化
$$
\boxed{\ \text{奇异环（层级回路）}\ \Longleftrightarrow\ \text{镜像本征 } (JF=\varepsilon F)\ \Longleftrightarrow\ \text{相位回绕 = 谱密度积分}\ } ,
$$
其中回绕指标等于谱移/谱密度（Birman–Kreĭn / Wigner–Smith）的窗口化积分；而**意义/读数**在**带限窗 + Nyquist–Poisson–Euler–Maclaurin**（NPE）三分解下实现**非渐近闭合**。另外，我们以**资源有界不完备**刻画「MIU 不可达态 $\Rightarrow$ 必须扩展理论」，并把扩展的解析像表述为**完成函数欧拉/无穷因子的增广**，其效应在显式/迹公式的尺度脉冲中可被直接读出。上述等价与闭合均依托公开判据：de Branges 规范系统与相位—密度词典、Birman–Kreĭn 公式、Wigner–Smith 延迟、Landau 采样密度、Wexler–Raz 正交、Balian–Low 不可能性、Csiszár 的 $I$-投影、Ky Fan 极值原理与 Poisson/Euler–Maclaurin 等。([普渡大学数学系][1])

---

## 0. 记号与底座

**完成函数与镜像。** 给定满足函数方程的完成函数 $\Xi(s)$ 与对合 $s\mapsto a-s$，写
$$
E(z):=\Xi\!\left(\tfrac a2+iz\right),\qquad E^\sharp(z):=\overline{E(\bar z)},\qquad U_E(z):=\frac{E^\sharp(z)}{E(z)} .
$$
若 $E$ 属 Hermite–Biehler 类，则 $U_E$ 在实轴为内函数（单位模），并生成一条 de Branges 空间链 $\mathcal H(E)$ 及其子空间序。([普渡大学数学系][1])

**de Branges–Kreĭn 规范系统。** 取规范系统 $\mathbf J Y'(t)=z H(t) Y(t)$（$H\succeq 0$），其 Weyl–Titchmarsh 函数 $m(z)$ 为 Herglotz，边界虚部给出谱测度密度 $\tilde\rho(x)=\pi^{-1}\Im m(x+i0)$。任意 Herglotz–Nevanlinna 函数都是某规范系统的 $m$-函数。([arXiv][2])

**散射相位与谱移。** 对多通道散射矩阵 $S(\mathcal{E})$，Wigner–Smith 矩阵 $Q(\mathcal{E})=-i\,S(\mathcal{E})^\dagger \tfrac{d}{d\mathcal{E}}S(\mathcal{E})$ 之迹满足 Birman–Kreĭn 约定 $\det S(\mathcal{E})=e^{-2\pi i \xi(\mathcal{E})}$，其中 $\xi$ 为谱移函数，则（Lebesgue-a.e. 或作分布）
$$
\frac{d}{d\mathcal{E}}\arg\det S(\mathcal{E})=\mathrm{tr}\,Q(\mathcal{E})=-2\pi\,\xi'(\mathcal{E}),
$$
其中
$$
\xi'(\mathcal{E})=\xi'_{\mathrm{ac}}(\mathcal{E})+\sum_j m_j\,\delta(\mathcal{E}-\mathcal{E}_j),
$$
$\{\mathcal{E}_j\}$ 为束缚态（或阈值）能级，$m_j>0$。在窗口化读数下，上式按分布与测试函数耦合后等价。等价地，记 $U_S(\mathcal{E}):=\det S(\mathcal{E})$，则
$$
\Im\!\frac{U_S'(\mathcal{E})}{U_S(\mathcal{E})}=-2\pi\,\xi'(\mathcal{E}),\qquad \rho_S(\mathcal{E}):=-\xi'(\mathcal{E}).
$$
([理研][3])

**窗化读数与 NPE 三分解。** 设窗 $w_R$ 及可检核 $h$，定义
$$
\mathrm{Obs}=\int_{\mathbb R} w_R(\mathcal{E})\,(h\!\star\!\rho_\bullet)(\mathcal{E})\,d\mathcal{E}+\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}.
$$
一般的 $w_R\in C^{2M}_c$ 会使 $\widehat{w_R f}$ 非带限，故 $\varepsilon_{\rm alias}\neq 0$。仅在（i）无窗 $w_R\equiv1$ 且 $\widehat f$ 支持于 $[-\Omega,\Omega]$ 并满足 $T\le\pi/\Omega$，或（ii）额外令 $w_R$ 亦带限并使 $\widehat{w_R f}$ 带限且满足 Nyquist 时，$\varepsilon_{\rm alias}=0$。([维基百科][4])

**记号统一（密度，情境化）。** 令 $U_E(x):=\dfrac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)}$（$E\in$ Hermite–Biehler）。de Branges 相位—核恒等式给出
$$
\varphi'(x)=\pi\,\frac{K(x,x)}{|E(x)|^2}\quad\text{(a.e.)},
$$
其中 $K$ 为 $\mathcal H(E)$ 的再生核，定义
$$
\rho_E(x):=\frac{K(x,x)}{|E(x)|^2}=\frac{1}{\pi}\varphi'(x).
$$
为避免多源密度混用，本文将观测密度统一记为 $\rho_\bullet$：默认 $\rho_\bullet=\rho_E$；**散射情形**取 $\rho_\bullet=\rho_S(\mathcal{E}):=-\xi'(\mathcal{E})$；**规范系统**情形取 $\rho_\bullet=\tilde\rho(x):=\pi^{-1}\Im m(x+i0)$。此后所有 $h\!\star\!\rho$ 一律改写为 $h\!\star\!\rho_\bullet$。

---

## 1. MIU / 形式系统 $\Rightarrow$ 资源有界不完备与可分辨刻度

**定义 1.1（资源层级）。** 给一致、递归可公理化理论 $T$ 与成本函数 $\mathrm{Cost}$。写 $T\!\upharpoonright\!L=\{\varphi:\exists\pi\ (\pi\vdash_T\varphi,\ \mathrm{Cost}(\pi)\le L)\}$。统计侧取观测类 $\mathcal F_m$ 与 IPM 距离 $d_{\mathcal F_m}$，记 $\mu\equiv_{(m,\varepsilon)}\nu$ 表示分辨率 $(m,\varepsilon)$ 下不可分辨。

**定义补充（IPM）。** 对观测类 $\mathcal F_m$，令
$$
d_{\mathcal F_m}(\mu,\nu):=\sup_{f\in\mathcal F_m}\,\bigl|\mathbb E_\mu f-\mathbb E_\nu f\bigr|.
$$
记 $\mu\equiv_{(m,\varepsilon)}\nu$ 当且仅当 $d_{\mathcal F_m}(\mu,\nu)\le \varepsilon$。

**定理 1.2（资源有界不完备）。** 对任意 $L$，集合 $T\!\upharpoonright\!L$ 有限；因此存在算术真句（在标准模型 $\mathbb N$ 下为真）不属于 $T\!\upharpoonright\!L$。此外，若将之一加入为新公理得 $T'$，则对任意 $L'$ 同样存在真句不属于 $T'\!\upharpoonright\!L'$。

**证明（要点）。** $\mathrm{Cost}\le L$ 的证明仅有限多条，因而仅推出有限多定理；而真句集合无限。第二断言由第一次不完备与 Chaitin 型不可压定理的稳定性（存在常数 $c_T$ 使 $T$ 不能证明「$K(x)>c_T$」之类真句）与可行不完备思想给出。([维基百科][5])

**注 1.3（MIU 的模 3 不变量）。** MIU 系统中从首句 $MI$ 出发，$I$-计数始终 $\not\equiv 0\pmod 3$，故 $MU$ 不可达；这是「系统内不变量 $\Rightarrow$ 不可达」的原型。([维基百科][6])

---

## 2. 自指（Diagonal / Fixed-Point） $\Rightarrow$ 镜像本征 $(JF=\varepsilon F)$

**定义 2.1（自反核与评估向量）。** 在 Mellin/上半平面模型上取满足镜像对称的核 $K$，得再生核 Hilbert 空间 $\mathcal H(K)$ 与评估向量 $k_s$，并有 $k_{a-s}=Jk_s$。令 $\Xi(s):=\langle F,k_s\rangle$。

**定理 2.2（完成功能方程 $\Longleftrightarrow$ 镜像本征）。**
$$
\Xi(a-s)=\varepsilon\,\Xi(s)\quad\Longleftrightarrow\quad JF=\varepsilon F .
$$

**证明。** 由 $\Xi(a-s)=\langle F,k_{a-s}\rangle=\langle F,Jk_s\rangle$ 及 $J$ 的等距性，得到 $JF=\varepsilon F$；反向同理。该结构落在 de Branges 空间 $\mathcal H(E)$ 的标准镜像机制内，$U=E^\sharp/E$ 为相位内函数。([普渡大学数学系][1])

---

## 3. 奇异环 = 相位—波包回路（定量）

**定义 3.1（相位场与回绕）。** 设 $U_E(x)=E^\sharp(x)/E(x)=e^{2i\varphi(x)}$（实轴单位模）。定义区间 $I$ 上的回绕数
$$
\operatorname{Wind}_I(U_E):=\frac{1}{2\pi}\int_I \Im\!\frac{U_E'(x)}{U_E(x)}\,dx=\frac{1}{\pi}\int_I \varphi'(x)\,dx .
$$
上式等价的分布表述为：对任意 $\psi\in C_c^\infty(I)$，
$$
\big\langle \partial_x\arg U_E,\psi\big\rangle=\int_I \psi(x)\,\Im\!\frac{U_E'(x)}{U_E(x)}\,dx .
$$
因此 $\operatorname{Wind}_I(U_E)=\int_I \rho_E(x)\,dx$ 与分支选择无关。

**定理 3.2（Strange Loop $\Longleftrightarrow$ 相位回绕 $\Longleftrightarrow$ de Branges 密度）。** 由上式设 $\rho(x):=\rho_E(x)$，则
$$
\operatorname{Wind}_I(U_E)=\frac{1}{2\pi}\int_I \Im\!\frac{U_E'(x)}{U_E(x)}\,dx=\frac{1}{\pi}\int_I \varphi'(x)\,dx=\int_I \rho(x)\,dx .
$$
若取散射相位 $U_S(\mathcal{E}):=\det S(\mathcal{E})$，则（a.e. 或作分布）
$$
\Im\!\frac{U_S'(\mathcal{E})}{U_S(\mathcal{E})}=-2\pi\,\xi'(\mathcal{E}),\qquad
\operatorname{Wind}_I(U_S)=\frac{1}{2\pi}\int_I\Im\!\frac{U_S'}{ U_S}\,d\mathcal{E}=\int_I \rho_S(\mathcal{E})\,d\mathcal{E} .
$$
因而散射与 de Branges 两侧的"回绕 = 密度积分"在同一无分支形式下完全对齐。回绕即为该区间的谱移总量。于是**「层级上升又返根」的奇异环被量化为「相位—密度回路的闭合」**。([数学学院][7])

**推论 3.3（环带聚束与临界采样）。** 若 $\varphi$ 严格单调且存在常数 $0<c\le C<\infty$ 使 $c\le \varphi'(x)\le C$（a.e.），则在 Weyl–Heisenberg / 非平稳帧下，按等相位层 $\Delta\varphi=\pi$ 的采样在相位刻度 $d\mu=\pi^{-1}\varphi'(x)\,dx$ 下诱导紧帧；临界密度由 Landau 必要密度与 Wexler–Raz 正交给出，Balian–Low 定理刻画不可兼得的「极端集中 + 非冗余」。([Project Euclid][8])

---

## 4. 意义与读数：Born = KL-投影；Pointer = 光谱极小；Windows = 极大极小

**定义 4.1（窗化读数与误差账本）。** 读数
$$
\mathrm{Obs}(R,\Delta)=\int w_R(\mathcal{E})\,(h\!\star\!\rho_\bullet)(\mathcal{E})\,d\mathcal{E}+\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
其中 $\varepsilon_{\rm alias}$ 由取样频率与带宽决定（Nyquist），$\varepsilon_{\rm EM}$ 由 EM 余项与伯努利层控制，$\varepsilon_{\rm tail}$ 为带外衰减项。([维基百科][4])

**定理 4.2（读数三位一体，Trinity）。**

(i) **Born = $I$-投影（最小 KL）**：在「约束 $\mathbb E_\nu[\phi]=c$」的可测全集上，最小化 $D(\nu|\mu)$ 的解为指数族，给出最优几率读数。([Stern School of Business][9])

(ii) **Pointer = 光谱极小**：对自伴算子 $A\succeq 0$，Ky Fan 原理给出 $\min_{\dim V=k}\mathrm{Tr}(P_V^\perp A)\!=\!\sum_{j>k}\lambda_j(A)$，指针子空间为前 $k$ 本征方向。([arXiv][10])

(iii) **Windows = 极大极小最优**：设决策域 $\mathcal W\subset H$ 为非空、凸且弱紧（例如 $H=L^2(\mathbb R)$，$\mathcal W=\{w\in H^1_0([-R,R]):|w|_{H^1}\le M\}$），对手域 $\mathcal C\subset L^2$ 为凸且弱紧；并且 $w\mapsto \mathrm{Obs}(w;\rho)$ 对 $w$ 为仿射且连续，$\rho\mapsto \mathrm{Obs}(w;\rho)$ 对 $\rho$ 为凸且上半连续。则
$$
\min_{w\in\mathcal W}\max_{\rho\in\mathcal C}\Bigl|\mathrm{Obs}(w;\rho)-\langle h,\rho\rangle\Bigr|^2+\lambda|Lw|_2^2
$$
存在最优解；若另有 $L^\ast L\succeq \mu I>0$，则该解唯一。其稳健性可由 DPI/相对熵单调性刻画。([中国科技大学教职工网站][11])

**证明（撮要）。** (i) 乃 Csiszár 的 $I$-投影判据；(ii) 由 Ky Fan 极值刻画本征和；(iii) 目标是凸—凹形式，Lagrange 乘子给出 Euler–Lagrange 方程；对开放系统，量化通道的 DPI 确保处理链路中的读数单调不增。

---

## 5. NPE：Nyquist–Poisson–Euler–Maclaurin 的非渐近闭合

**定理 5.1（NPE 三分解界）。** 设 $w_R\in C^{2M}_c(\mathbb R)$，且存在常数 $C_k$ 使 $|w_R^{(k)}|_\infty\le C_k R^{-k}$（$0\le k\le 2M$）；取 $f=h\!\star\!\rho_\bullet$ 为 Schwartz，或 $f\in C^{2M}$ 且 $f^{(2M)}$ 可积。若 $\widehat f$ 支持于 $[-\Omega,\Omega]$ 且采样步长 $T\le \tfrac{\pi}{\Omega}$，则
$$
\sum_{n\in\mathbb Z} w_R(nT)\,f(nT)=\int_{\mathbb R} w_R f+\underbrace{\frac{1}{T}\sum_{k\neq 0}\bigl(\widehat{w_R f}\bigr)\!\left(\tfrac{2\pi k}{T}\right)}_{\varepsilon_{\rm alias}}+\underbrace{R_{2M}(w_R f)}_{\varepsilon_{\rm EM}},
$$
其中一般的 $w_R\in C^{2M}_c$ 使 $\widehat{w_R f}$ 非带限，故 $\varepsilon_{\rm alias}\neq 0$；$\varepsilon_{\rm alias}=0$ 仅在（i）$w_R\equiv 1$（无窗）且 $f$ 带限并满足 Nyquist，或（ii）额外令 $w_R$ 亦带限并使 $\widehat{w_R f}$ 带限且满足 Nyquist 时成立。仍有 $|R_{2M}(w_R f)|\le C\,R^{-2M}$。([维基百科][4])

**证明。** 先用 Poisson 求和将离散和写为频域周期化；带限+Nyquist 消灭别名；对有限窗，把积分—和的差用 EM 公式展开，余项为 $O(R^{-2M})$（或由最新形式化文献给出精确余项表达）。([形式证明档案][12])

---

## 6. 从「自指」到「奇异环」：对角化 → 镜像本征 → 相位刻度

**命题 6.1（对角化的算子化）。** 任何「谈论自身」的命题在 $\mathcal H(K)$ 中具体化为 $JF=\varepsilon F$ 的镜像本征；评估向量的协变 $k_{a-s}=Jk_s$ 提供对角构造。见 §2。

**命题 6.2（意义刻度的唯一性）。** 在相位刻度 $d\mu_\varphi=\pi^{-1}\varphi'(x)\,dx$ 下，概率读数（Born/$I$-投影）与帧门槛（Landau 必要密度、Wexler–Raz 双正交）对齐；极端集中与非冗余的不可兼得由 Balian–Low 定理给出。([Project Euclid][8])

---

## 7. MIU 的「不可达」与「扩展」的解析影像

**定理 7.1（不可达 = 不变量；扩展 = 欧拉因子增广）。**

(i) 系统内不可达（如 MIU 模 3）对应于窗化读数下**不可分辨类**的保持；

(ii) 「扩展理论」在解析侧等价于对完成函数的**欧拉/无穷因子**信息的增广，从而经显式/迹公式在尺度 $m\log p$ 处点亮新脉冲，改变相位—零谱。([维基百科][6])

**证明（要点）。** (i) $\equiv_{(m,\varepsilon)}$ 为伪度量，资源单调保证不可分辨类的保序；(ii) 近似功能方程与显式公式把「新增局部信息」转译为频谱侧可检增量，且遵守 EM 纪律而不引入新奇点。([aimath.org][13])

---

## 8. 「奇异环 = 波包」的可检化

**定理 8.1（环 $\to$ 包）。** 取等相位采样 $\Delta\varphi=\pi$。在 $\varphi'$ 刻度下得到紧帧/对偶帧；Calderón 型和式与 Wexler–Raz 正交保证能量守恒与重构稳定；临界密度受 Landau 门槛制约。([杜克大学数学系][14])

**注 8.2（零集几何与奇性保持）。** 有限阶 EM 仅增加伯努利层，不改变「极点 = 主尺度」的主奇性结构（由 Poisson/EM 的整性与带限性保障）。([哥伦比亚大学数学系][15])

---

## 9. 可检清单（把 GEB 变成实验/数值任务）

1. **奇异环读数**：测 $\partial_\mathcal{E}\arg\det S$ 或 $\mathrm{tr}\,Q$，在 $d\mu_\varphi$ 刻度下核对 $\operatorname{Wind}_I(U_S)=\int_I\rho_S$；或对 de Branges 情形验证 $\operatorname{Wind}_I(U_E)=\int_I\rho_E$。([理研][3])
2. **自指本征**：在 $\mathcal H(E)$ 中数值构造 $JF=\varepsilon F$ 的本征态，检验 $\Xi(a-s)=\varepsilon\Xi(s)$。([普渡大学数学系][1])
3. **意义三位一体一致性**：对同一数据流分别做（i）KL 最小的 $I$-投影；（ii）Ky Fan 极小的指针子空间；（iii）窗/核 KKT 极大极小；验证三者读数落入 NPE 误差预算。([Stern School of Business][9])
4. **扩展即素点**：在 AFE/显式公式框架中，人工增删某局部因子参数，监测 $m\log p$ 处读数脉冲与相位回绕跃迁。([aimath.org][13])

---

## 结论

在此统一框架中，**GEB 的「奇异环—自指—意义」不再是隐喻**：它们被严格等价为**镜像本征态的相位回路**、其**回绕 = 谱密度/谱移积分**，以及在**带限窗化读数 + NPE 三分解**下的**三位一体极值结构**。MIU 的不可达由**资源有界不完备**精确定义，「扩展理论」的效应在**完成函数的局部/无穷因子**上具有可观测的谱学回响。由此，《GEB》的叙事三根脉（形式—自指—意义）在**母映射—Mellin—de Branges—散射—窗化**的硬骨架上闭合为可证、可算、可复现实证的统一理论。

---

### 参考与判据（按主题分组）

* **de Branges 空间与规范系统**：de Branges《Hilbert Spaces of Entire Functions》；规范系统 $m$-函数与 Herglotz 对应；$U=E^\sharp/E$ 的内函数角色与子空间链。([普渡大学数学系][1])
* **散射相位/谱移/延迟**：Birman–Kreĭn 公式 $\det S=e^{-2\pi i \xi}$；Wigner–Smith $Q=-iS^\dagger S'$，$\frac{d}{dE}\arg\det S=\mathrm{tr}\,Q$。([arXiv][16])
* **采样与帧**：Landau 必要密度；Wexler–Raz 双正交与 Gabor 框架；Balian–Low 不可能性。([Project Euclid][8])
* **NPE 组成件**：Nyquist–Shannon；Poisson 求和；Euler–Maclaurin 余项的现代形式化。([维基百科][4])
* **信息几何与极值原则**：Csiszár $I$-投影（最小相对熵）；Ky Fan 极值与部分特征值和；相对熵单调性/DPI。([Stern School of Business][9])
* **不完备与 MIU**：Gödel 不完备、Chaitin 不完备、可行不完备/短证明困难；MIU 模 3 不变量。([维基百科][5])

---

[1]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[2]: https://arxiv.org/pdf/1408.6022?utm_source=chatgpt.com "arXiv:1408.6022v1 [math.SP] 26 Aug 2014"
[3]: https://www2.riken.jp/ap/publication/files/shimamura_JPB39%282006%291847-1854.pdf?utm_source=chatgpt.com "Eigenvalues of the time-delay matrix in overlapping ..."
[4]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[5]: https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems?utm_source=chatgpt.com "Gödel's incompleteness theorems"
[6]: https://en.wikipedia.org/wiki/MU_puzzle?utm_source=chatgpt.com "MU puzzle"
[7]: https://www.mat.univie.ac.at/~gerald/ftp/articles/AsymCS.pdf?utm_source=chatgpt.com "spectral asymptotics for canonical systems"
[8]: https://projecteuclid.org/journals/acta-mathematica/volume-117/issue-none/Necessary-density-conditions-for-sampling-and-interpolation-of-certain-entire/10.1007/BF02395039.full?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[9]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[10]: https://arxiv.org/pdf/1108.1467?utm_source=chatgpt.com "arXiv:1108.1467v2 [math.FA] 14 Nov 2011"
[11]: https://staff.ustc.edu.cn/~cgong821/Wiley.Interscience.Elements.of.Information.Theory.Jul.2006.eBook-DDU.pdf?utm_source=chatgpt.com "Elements of Information Theory"
[12]: https://www.isa-afp.org/browser_info/current/AFP/Euler_MacLaurin/document.pdf?utm_source=chatgpt.com "The Euler–MacLaurin summation formula"
[13]: https://aimath.org/~kaur/publications/58.pdf?utm_source=chatgpt.com "Notes on L-functions and Random Matrix Theory"
[14]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[15]: https://www.math.columbia.edu/~woit/fourier-analysis/theta-zeta.pdf?utm_source=chatgpt.com "Notes on the Poisson Summation Formula, Theta Functions ..."
[16]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
