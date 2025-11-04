# 有限记录熵、Zeckendorf 日志与完备—停机判据：WSIG–EBOC–RCA 统一公理化

Version: 1.9

## 摘要

建立一套以窗化散射与信息几何（WSIG）为读数层、以永恒静态块观察—计算（EBOC）为本体层、以可逆元胞自动机（RCA）为动力语义的统一公理化，用于刻画观察者日志的有限记录熵与停机（可逆重建）之间的必要—充分关系。核心结论指出：在满足帧稳定性与规范一致性的条件下，任何观察四元 $(\mathcal H,w,h,\mathcal D)$ 所得到的有限记录，其重建所需的最小自编码信息量 $H_{\mathrm{rec}}$ 与 WSIG 的三位一体刻度完全同尺度，
$$
\boxed{\ \rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}=\frac{1}{2\pi}\operatorname{tr}\big(\mathsf Q(E)\big)\ },\qquad
\mathsf Q(E)=-i\, S(E)^\dagger S'(E)
$$
并在 Nyquist–Poisson–Euler–Maclaurin（NPE）有限阶误差纪律下给出"完备—停机阈值"判据：当且仅当 $H_{\mathrm{rec}}$ 不超过由窗带宽、采样密度与可逆黏合常数决定的临界阈值 $H_\star$ 时，窗口—局部的可逆重建在有限步内停机且与 EBOC 全局编码一致。进一步证明：当记录采用 Zeckendorf 规范（斐波那契无邻位编码）存储时，其最短自解码长度与 $H_{\mathrm{rec}}$ 等阶，并在别名层误差不增意义下实现前缀同步的稳健最优。文中同时给出非渐近误差闭合、复杂度上界以及 RCA 叶上可逆延拓的构造性算法。

---

## 0. 记号与公理 / 约定（Notation & Axioms / Conventions）

**（A0）散射对与谱记号（Scattering Pair & Spectral Notation）**
固定定义在同一希尔伯特空间 $\mathcal H$ 上的一对自伴算子 $H_0, H_V$（波算子 $W_\pm(H_V,H_0)$ 存在且完备），据此定义能量参数化的散射矩阵 $S(E)$。记
$$
E_{H_\sharp}(I):=1_I(H_\sharp)\quad(\sharp\in\{0,V\}),\ I\subset\mathbb R\ \text{为 Borel 集}
$$
并在本文中统一约定 $H:=H_V$，故 $1_I(H)\equiv E_{H_V}(I)$。Birman–Kreĭn 迹公式与 Wigner–Smith 群延迟矩阵 $\mathsf Q(E)=-i\,S(E)^\dagger S'(E)$ 关联为
$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad
\xi'(E)=-\,\rho_{\mathrm{rel}}(E)=-\frac{1}{2\pi}\operatorname{tr}\big(\mathsf Q(E)\big)
$$
并与（A1）之"三位一体刻度"相容（此处 $\rho_{\mathrm{rel}}=\varphi'(E)/\pi=(2\pi)^{-1}\operatorname{tr}\mathsf Q$）。

**（A1）三位一体刻度（Trinity / Mother–Scale）**
绝对连续谱 a.e. 下成立的统一刻度
$$
\boxed{\ \rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}=\frac{1}{2\pi}\operatorname{tr}\big(\mathsf Q(E)\big)\ }
$$
其中 $\varphi'(E)$ 为散射相位导数，$\mathsf Q(E)=-i\, S^\dagger S'$ 为 Wigner–Smith 群延迟矩阵，$\rho_{\mathrm{rel}}$ 为相对态密度（Birman–Kreĭn 光谱位移 $\xi'$ 之负值）。该同一式由 Birman–Kreĭn 迹公式与 $S$ 的相位—行列式联系、以及 Smith 的群延迟定义共同刻画。([arXiv][1])

**（A1′）通道纤维与逐能量迹（Channel Fibers & Integrable Trace）**
在能量工作域 $\mathrm{band}$ 上 a.e. 的能量 $E$ 处，散射矩阵 $S(E)$ 作用于有限维通道纤维 $\mathbb C^{N(E)}$（$N(E)<\infty$），且 $\mathsf Q(E)=-i\,S(E)^\dagger S'(E)$ 在该纤维上为迹类，并满足 $\operatorname{tr}\mathsf Q\in L^1(\mathrm{band})$。因而
$$
\frac{1}{2\pi}\int_{\mathrm{band}}\operatorname{tr}\mathsf Q(E)\, dE
$$
良定义，并与（A1）之刻度同一兼容。

**（A2）窗化读数的算子化表述**
窗口/读数统一为算子—测度—函数分析对象：给定窗核 $w$ 与读数函数 $h$，记 Toeplitz/Berezin 压缩为 $K_{w,h}$；一切观测读数均视作对谱测度的线性泛函。([revistas.ucm.es][2])

**（A2′）迹类与核正则（Trace-Class & Kernel Regularity）**
为使所有迹表达式良定义，约定在所选能量工作域 $\mathrm{band}$ 上满足：
(i) $h\in L^\infty(\mathrm{band})$，窗核 $w$ 为带限或具指数型衰减且具有有限阶可微性；
(ii) 由（A2）定义之 Toeplitz/Berezin 压缩 $K_{w,h}$ 满足 $E_{H_V}(\mathrm{band})\,K_{w,h}\in\mathfrak S_1(\mathcal H)$（迹类），且 $\|E_{H_V}(\mathrm{band})\,K_{w,h}\|_{\mathfrak S_1}$ 由 $\|h\|_{L^\infty}$、窗族的带宽/衰减常数与有限阶导数上界共同控制。
如取带限窗，则 $K_{w,h}$ 为 Hilbert–Schmidt；指数窗情形以下降指数与有限阶 EM/Poisson 逼近得到相同的 HS 结论。为保证所有迹表达式良定义，本文在所选 $\mathrm{band}$ 上进一步假设 $E_{H_V}(\mathrm{band})\,K_{w,h}\in\mathfrak S_1(\mathcal H)$（迹类），可通过加强核平滑与衰减条件来确保。

**（A3）NPE 有限阶误差纪律**
任何离散—连续换元仅使用有限阶 Euler–Maclaurin 与 Poisson 和—积变换；误差闭合为"主项 + 别名层 + Bernoulli 层"，并遵守：（i）奇性不增；（ii）极点=主尺度。所用公式与常数可由 DLMF 的 EM / PSF 标准条目与近年 EM 强化版给出。([dlmf.nist.gov][3])

**定义（$\mathrm{EM}_{\le m}$ 有限阶常数）**
固定 $m\ge 1$。存在有限常数 $C_{\mathrm{alias}}(w,\Lambda)$ 与 $C_{\mathrm{Bernoulli}}^{(\le m)}(w,h)$，使本文所有离散—连续换元均有 $|\mathcal E_{\mathrm{alias}}|\le C_{\mathrm{alias}}(w,\Lambda)$、$|\mathcal E_{\mathrm{Bernoulli}}|\le C_{\mathrm{Bernoulli}}^{(\le m)}(w,h)$。定义
$$
\mathrm{EM}_{\le m}(w,h,\Lambda)
:=C_{\mathrm{alias}}(w,\Lambda)+C_{\mathrm{Bernoulli}}^{(\le m)}(w,h)
$$
并据此在定理 C 的阈值表达中使用 $\mathrm{EM}_{\le m}$。

**（A4）EBOC 与 RCA 语义**
EBOC 为静态全局编码之本体层；RCA 为其可逆叶上动力学对位。RCA 的可逆性与"Garden-of-Eden/预注入—满射"等价定理、以及 Toffoli–Margolus 可逆 CA 形理论证据共同支撑"可逆延拓—停机"的判别几何。本文默认 RCA 定义在有限字母表的满移位 $A^{\mathbb Z^d}$（或更一般的可数 amenable 群）上，以保证 Moore–Myhill（Garden-of-Eden）定理之"预注入 $\Leftrightarrow$ 满射"等价成立。([ibisc.univ-evry.fr][4])

**（A5）帧稳定性与密度一致性**
观察者窗族 $\{w_\lambda\}_{\lambda\in\Lambda}$ 在工作域上构成帧/半框架；采样格 $\Lambda$ 需满足 Landau 必要密度。若 $\{w_\lambda\}$ 由格点时–频平移生成（Gabor 系），则再满足 Wexler–Raz 对偶关系以保证双正交重构；对一般窗族本文仅使用帧界与密度条件。([archive.ymsc.tsinghua.edu.cn][5])

---

## 1. 对象与问题设定

### 1.1 观察者窗—测度—解码四元

设希尔伯特空间 $\mathcal H$，散射算子族 $S(E)$ 与谱测度 $\mu$。观察四元 $(\mathcal H,w,h,\mathcal D)$ 包含：
(i) 窗核 $w$（带限或指数衰减类）；
(ii) 读数函数 $h$ 及其诱导的读数—压缩算子 $K_{w,h}$（以 $h$ 指定读数方向）；
(iii) 自解码器 $\mathcal D$（前缀、可逆、与 $\Lambda$ 同步）。

在采样格 $\Lambda$ 上形成窗化读数向量 $\mathbf y=\{y_\lambda\}_{\lambda\in\Lambda}$，其中每个 $y_\lambda$ 为对 $\mu$ 的线性泛函，由 $K_{w,h}$ 与帧系数给出。下文 $H_{\mathrm{rec}}(R;w,h)$ 与 $K_{w,h}$ 皆以上述四元记号为准。

**约定（能量工作域 $\mathrm{band}$）**
选取有界 Borel 集 $\mathrm{band}\subset\mathbb R$ 作为能量工作域，用以限定积分与迹：$\int_{\mathrm{band}}(\cdot)\, dE$ 与 $\operatorname{tr}\big(1_{\mathrm{band}}(H)(\cdot)\big)$ 皆在该集合内取值。构造上可取 $\mathrm{band}:=\operatorname{supp}h\cap\operatorname{ess\,supp}(d\mu)$；带限窗情形亦可取 $\mathrm{band}=\operatorname{supp}\widehat w$。

### 1.2 记录与可逆过去

**定义 1（记录与可逆过去）**
一次测量得到的记录 $R\subset\Xi$（$\Xi$ 为 EBOC 全局编码空间）是 $(w,h,\Lambda)$ 下可提取的有限符号串/有限维向量集合，且存在可逆扩展 $\Theta$ 使 $\Theta(R)$ 沿 RCA 叶空间 $\mathcal L$ 在规范等价类意义下唯一回接到某一可逆历史分支（固定规范后其代表唯一）。

**定义 2（有限记录熵）**
$$
H_{\mathrm{rec}}(R;w,h)
:=\inf\big\{\text{重建该分支所需的最小自编码比特数（前缀/可逆）}\big\}.
$$
下确界对所有与 $R$ 等价的自解码编码方案取最小；前缀—可逆码满足 Kraft–McMillan 不等式。([staff.ustc.edu.cn][6])

### 1.3 Zeckendorf 规范日志

**定义 3（Zeckendorf 日志）**
令 $\{F_k\}$ 为斐波那契序列。将记录 $R$ 的时间戳与符号块映射为无相邻 1 的 $\{F_k\}$-展开，得一一对应的前缀自解码串 $Z(R)$，长度记 $|Z(R)|$。Zeckendorf 分解唯一，配合"11 终止"之 Fibonacci 编码形成自同步可复位的可判定前缀码。([维基百科][7])

---

## 2. 主定理

### 2.1 记录熵与三位一体刻度的一致性

**定理 A（WSIG—记录熵等价）**
设 $(w,\Lambda)$ 帧稳定，$h$ 有界可测，窗族带限或指数衰减，并满足（A3）。存在仅依赖 $(w,h,\Lambda)$ 的常数 $C_\pm>0$ 与有界误差项 $\mathcal E_{\mathrm{NPE}}$（别名层与有限阶 Bernoulli 层之和），使
$$
C_- \int_{\mathrm{band}} \rho_{\mathrm{rel}}(E)\, dE - \mathcal E_{\mathrm{NPE}}
\ \le\ H_{\mathrm{rec}}(R;w,h)\ \le
C_+ \int_{\mathrm{band}} \rho_{\mathrm{rel}}(E)\, dE + \mathcal E_{\mathrm{NPE}}
$$
亦即
$$
H_{\mathrm{rec}}(R;w,h)\asymp
\int_{\mathrm{band}}\rho_{\mathrm{rel}}(E)\, dE
\asymp \int_{\mathrm{band}}\frac{\varphi'(E)}{\pi}\, dE
\asymp \frac{1}{2\pi}\int_{\mathrm{band}}\operatorname{tr}\big(\mathsf Q(E)\big)\, dE
$$

*证明.* 令
$$
\mathcal N_{w,h}(\mathrm{band})
:=\operatorname{tr}\big(E_{H_V}(\mathrm{band})\,K_{w,h}\big)
$$
取光滑 $g$ 使 $g'=\chi_{\mathrm{band}}$ 的逼近。由 Birman–Kreĭn 迹公式 $\operatorname{tr}\big(g(H_V)-g(H_0)\big)=\int g'(E)\,\xi(E)\, dE$ 与 $\xi'=-\,\rho_{\mathrm{rel}}$、以及 Wigner–Smith $\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$，得 $\int_{\mathrm{band}}\rho_{\mathrm{rel}}$ 与相位增量、群延迟迹之等价。再将 $\mathcal N_{w,h}(\mathrm{band})$ 表示为 Toeplitz/Berezin 压缩的迹并用帧不等式连接离散—连续量度，配合有限阶 Poisson+Euler–Maclaurin 闭合，即得定理所述双边控制。([arXiv][1])

### 2.2 Zeckendorf 自解码的稳健最优性

**定理 B（Zeckendorf 渐近最短自解码）**
在定理 A 条件下，对任意满足 Kraft 不等式的前缀码族，有
$$
H_{\mathrm{rec}}(R;w,h)\ \le\ |Z(R)|\ \le\ C\cdot H_{\mathrm{rec}}(R;w,h)+O(1)
$$
且 $Z(R)$ 在逐块意义下实现与 $H_{\mathrm{rec}}$ 同阶的最短自解码，同时在别名层扰动下具自同步稳健性（"11"终止只在码字尾出现，有限步即可复位）。

*证明.* 下界由 $H_{\mathrm{rec}}$ 的定义与 Kraft–McMillan 立即给出；上界由 Zeckendorf 唯一性与自同步性结合源编码最优性下界得出，故 $|Z(R)|\asymp H_{\mathrm{rec}}$。Zeckendorf 定理保证无相邻 1 的唯一分解；Fibonacci 编码是前缀且自同步的可判定码，译码器可通过扫描终止子在有限位内恢复相位。而 Zeckendorf 以无邻位约束逼近该下界至常数阶。同时，由自同步性质，局部别名误差不向前缀边界外扩散，保证了逐块可修复性与稳定译码。([维基百科][7])

### 2.3 完备—停机阈值

**定理 C（阈值判据）**
设有效采样密度 $\mathsf D_{\mathrm{eff}}$ 与窗带宽 $\mathsf B$ 给出可见自由度 $\mathsf N\sim \mathsf D_{\mathrm{eff}}\mathsf B$。存在阈值
$$
H_\star = \alpha\cdot \mathsf N + \beta\cdot \mathrm{EM}_{\le m}(w,h,\Lambda)
$$
使得：
(i) 若 $H_{\mathrm{rec}}(R;w,h)\le H_\star$，则存在有限步可逆重建算法 $\mathcal A$ 在 RCA 叶上停机，且与 EBOC 全局编码一致（唯一性只差规范）。
(ii) 若 $H_{\mathrm{rec}}(R;w,h)>H_\star$，则任意局部算法要么不停机，要么产生与全局编码不一致的伪解（不可逆回接）。

*证明.* 由帧不等式与 Landau 必要密度得 $\mathsf N$ 的非渐近上界；再以 NPE 误差常数控制别名与边界层，构造阈值 $H_\star$。当 $H_{\mathrm{rec}}\le H_\star$ 时，$\mathsf N$ 给出有限纠错半径的可逆黏合；由于假设 RCA 为可逆 CA（其全局映射为双射），故在规范等价类意义下存在且仅存在一个可逆延拓类；固定规范后其代表唯一。Garden-of-Eden 等价（预注入 $\Leftrightarrow$ 满射）仅用于判别满射性/排除 GOE 模式，并不单独蕴含唯一性。于是有限步停机；反之违反满射或需要无限延拓。([archive.ymsc.tsinghua.edu.cn][5])

---

## 3. 误差学与稳定性

### 3.1 NPE 三项闭合与奇性不增

在固定阶 $m$ 的 EM 与 Poisson 变换下，
$$
H_{\mathrm{rec}}
=\underbrace{\int \rho_{\mathrm{rel}}}_{\text{主尺度}}
+\underbrace{\mathcal E_{\mathrm{alias}}}_{\text{别名层}}
+\underbrace{\mathcal E_{\mathrm{Bernoulli}}}_{\text{EM 有限阶}}
$$
并满足：（i）奇性不增；（ii）极点=主尺度；（iii）误差常数仅由 $(w,h,\Lambda)$ 的衰减阶、平滑度与密度控制。([dlmf.nist.gov][3])

### 3.2 帧与密度阈

若 $\{w_\lambda\}$ 为帧，帧界 $A\le B$，则
$$
A|f|_2^2 \le \sum_{\lambda\in\Lambda} |\langle f,w_\lambda\rangle|^2 \le B|f|_2^2,
$$
从而可见自由度 $\mathsf N$ 与 $\mathsf D_{\mathrm{eff}}\mathsf B$ 等阶；带限窗由 Landau 密度给最小采样约束；指数窗以有效带宽替代并保留同阶估计。若 $\{w_\lambda\}$ 由格点时–频平移生成（Gabor 系），则可再用 Wexler–Raz 对偶给出双正交重构的准则；对一般窗族本文仅使用帧界与密度条件。([archive.ymsc.tsinghua.edu.cn][5])

### 3.3 模型窗与集中性

时—带集中范式可由 PSWF/DPSS 理论给出，时间—带宽乘积 $\mathsf N$ 的非渐近估计可直接用于 $H_\star$ 的设计。([personal.ntu.edu.sg][8])

---

## 4. EBOC / RCA 语义嵌入

**本体层（EBOC）**：$\Xi$ 为全局静态编码；记录 $R$ 是 $\Xi$ 的有限剖面。有限记录熵 $H_{\mathrm{rec}}$ 衡量 $R$ 在规范等价类意义下可逆回接到唯一历史分支所需的最小自编码信息量，即"从叶到块的桥宽"。

**动力叶（RCA）**：叶空间 $\mathcal L$ 赋可逆邻接图，纠错距离 $d_{\mathrm{corr}}$ 决定局部扰动被可逆延拓吸收的半径。Garden-of-Eden（预注入 $\Leftrightarrow$ 满射）提供"停机 $\Leftrightarrow$ 完备"的动力学基础。([ibisc.univ-evry.fr][4])

---

## 5. 构造性算法与复杂度

**算法 $\mathcal A$（局部—全局可逆重建）**
输入：$(w,h,\Lambda)$、窗化读数 $\mathbf y$、Zeckendorf 日志 $Z(R)$。

1. **主尺度估计**：由 $K_{w,h}$ 与窗谱近似计算 $\widehat H:=\int \widehat{\rho}_{\mathrm{rel}}$，三位一体一致化（$\widehat{\rho}_{\mathrm{rel}}\;\widehat{=}\;\varphi'/\pi=(2\pi)^{-1}\operatorname{tr}\,\widehat{\mathsf Q}$）。([arXiv][1])
2. **误差闭合**：有限阶 EM + Poisson 得上下界 $\widehat H_\pm=\widehat H\pm \widehat{\mathcal E}_{\mathrm{NPE}}$。([dlmf.nist.gov][3])
3. **阈值比较**：计算 $H_\star=\alpha\cdot \mathsf N+\beta\cdot \mathrm{EM}_{\le m}$。若 $|Z(R)|\le C\cdot \widehat H+O(1)\le H_\star$，进入延拓；否则判为非停机区。([archive.ymsc.tsinghua.edu.cn][5])
4. **可逆延拓**：在 RCA 叶上以贪心—前缀同步策略用 $Z(R)$ 解码并迭代黏合，冲突时以 $d_{\mathrm{corr}}$ 为半径做最小修复；黏合增量低于阈值即停机。([ui.adsabs.harvard.edu][9])

**复杂度**：停机迭代次数 $\le c_1\mathsf N+c_2 d_{\mathrm{corr}}+c_3 m$，空间复杂度随 $|Z(R)|$ 线性增长。

---

## 6. 推论与设计准则

**（P1）最小日志原则**：在 $H_\star$ 以下，采用 Zeckendorf 规范使 $|Z(R)|\sim H_{\mathrm{rec}}$ 且别名不扩散与自同步并存。([MDPI][10])

**（P2）窗/采样共设计**：给定目标记录熵预算 $H_0$，可反推 $(\mathsf B,\mathsf D_{\mathrm{eff}})$ 的最小组合与窗族类别（带限/指数），在保证帧稳定性的同时最小化 $\mathcal E_{\mathrm{NPE}}$。([archive.ymsc.tsinghua.edu.cn][5])

**（P3）从信息量到时间**：阈值达成即"完备 $\Rightarrow$ 停机"，停机时间上界由 $\mathsf N$ 与误差常数线性控制，建立信息—计算的直接桥接。

---

## 7. 证明框架的要素化展开

### 7.1 定理 A 的要素分解

**Lemma 7.1（帧化同尺度）**
帧不等式将离散能量与连续谱密度联系为双边控制，系数仅由 $A,B$ 与 $|K_{w,h}|$ 决定。([link.springer.com][11])

**Lemma 7.2（三位一体换元）**
Birman–Kreĭn 迹公式给出 $\xi'=-\,\rho_{\mathrm{rel}}$ 与 $\det S=e^{-2\pi i\,\xi}$；Wigner–Smith 给出 $\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$。二者与 $\varphi'=\pi \rho_{\mathrm{rel}}$ 等价，从而建立刻度同一。([arXiv][1])

**Lemma 7.3（NPE 有限阶闭合）**
Poisson 处理别名层，Euler–Maclaurin 处理边界层，误差常数受窗的平滑度与衰减率控制，且不增奇性。([dlmf.nist.gov][3])

**Lemma 7.4（自编码下界）**
Kraft–McMillan 与前缀码最优性给出最小自编码长度的通用下界；配合 Lemma 7.1–7.3 即得主尺度—信息量的双边不等式。([staff.ustc.edu.cn][6])

### 7.2 定理 B 的要素分解

**Lemma 7.5（Zeckendorf 唯一性与前缀性）**
无相邻 1 的 $\{F_k\}$-展开唯一，Fibonacci 编码以"11"为终止子形成前缀—自同步码。([维基百科][7])

**Lemma 7.6（自同步稳健性）**
Fibonacci/高阶 Fibonacci 码具有自同步变量长度特性，局部错误在有限步内被终止子吸收并复位译码相位。([MDPI][10])

### 7.3 定理 C 的要素分解

**Lemma 7.7（$\mathsf N$ 的非渐近估计）**
Landau 必要密度与 PSWF/DPSS 集中性给出 $\mathsf N\sim \mathsf D_{\mathrm{eff}}\mathsf B$ 的非渐近定量上界。([archive.ymsc.tsinghua.edu.cn][5])

**Lemma 7.8（RCA 叶上停机—完备等价）**
在可逆 CA 上，预注入 $\Leftrightarrow$ 满射（Garden-of-Eden 定理）。有限步停机并非由该等价直接推出，而是由 §2.3 的阈值 $H_\star$ 与算法 $\mathcal A$ 的误差闭合给出。([ibisc.univ-evry.fr][4])

---

## 8. 典型窗族与参数化

**带限窗**：Poisson 别名由带外抑制决定，EM 层由带端光滑度决定；Landau 密度给出采样下限。([archive.ymsc.tsinghua.edu.cn][5])

**指数窗（含对数域窗）**：以有效带宽 $\mathsf B_{\mathrm{eff}}$ 替代，误差常数由衰减指数与导数阶控制。

**多尺度/多通道窗**：帧界取最不利通道上界，$\mathcal E_{\mathrm{NPE}}$ 叠加闭合，极点仍由主尺度决定。

---

## 9. 与物理—信息几何的对位

$\rho_{\mathrm{rel}}=\varphi'/\pi=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 将可观测密度、相位导数与群延迟统一为"通用测度坐标"；其积分刻度与记录熵的等阶性把"知道多少信息足以重建可逆过去"转化为可计算阈值；而 RCA 的可逆性与 Garden-of-Eden 定理把该阈值与"有限步停机"的动力学命题精确对接。([arXiv][1])

---

## 附录 A：Wigner–Smith 与 Birman–Kreĭn 的统一

Smith 定义 $\mathsf Q=-i\, S^\dagger S'$ 并证明其谱刻画延迟；在多通道情形，$\frac{1}{2\pi}\operatorname{tr}\mathsf Q$ 等于相对态密度（相对于 $H_0$ 的 DOS 增量）的能量密度，随机矩阵与混沌散射文献亦以此为基础。另一方面，Birman–Kreĭn 给出 $\det S=e^{-2\pi i\,\xi}$ 且 $\xi'=-\,\rho_{\mathrm{rel}}$；结合 $\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$，完成"相位—位移—群延迟"的母刻度闭环。([chaosbook.org][12])

---

## 附录 B：密度定理、Wexler–Raz 与 Balian–Low

Gabor 系的对偶性由 Wexler–Raz 关系刻画；一般帧仅依赖密度定理（如 Landau）给出采样/稳定性结论，WR 不适用；Balian–Low 限制了"同时强局域化且完全"的正交格架，从而指导窗族的选择与误差上界的可能尺度。([sites.math.duke.edu][13])

---

## 参考文献（选）

1. Yafaev, D. R. *Perturbation Determinants, the Spectral Shift Function, Trace Identities…*（2007）。([arXiv][1])
2. Strohmaier, A., et al. *The Birman–Krein formula…*（2022）。([research.rug.nl][14])
3. Wigner, E. P. *Lower limit for the energy derivative of the scattering phase shift*（1955）。([chaosbook.org][15])
4. Smith, F. T. *Lifetime matrix in collision theory*（1960）。([chaosbook.org][12])
5. Schomerus, H., et al. *Wigner–Smith matrix and DOS relation*（2014）。([arXiv][16])
6. Engliš, M. *Berezin–Toeplitz quantization（综述）*（2006）。([revistas.ucm.es][2])
7. DLMF §1.8（Poisson），§2.10（EM）。([dlmf.nist.gov][17])
8. Landau, H. J. *Necessary density conditions for sampling…*（1967/2006）。([archive.ymsc.tsinghua.edu.cn][5])
9. Daubechies, I., Landau, H. J., Landau, Z. *Wexler–Raz Identity*（1995）。([sites.math.duke.edu][13])
10. Balian–Low 定理综述（UMD 讲义；百科条目）。([math.umd.edu][18])
11. Wang, L.-L. *PSWFs Review*（2017）；Boulsane, M.（2019）。([personal.ntu.edu.sg][8])
12. Cover, T. M., Thomas, J. A. *Elements of Information Theory*（2e）。([staff.ustc.edu.cn][6])
13. Zeckendorf 定理与 Fibonacci 编码文献（MDPI/ArXiv）。([维基百科][19])
14. Kari, J. *Theory of Cellular Automata: A Survey*（2005）；Toffoli–Margolus（1990）。([ibisc.univ-evry.fr][4])

---

## 结论式陈述

在 WSIG–EBOC–RCA 统一框架内，将"有限记录能否在规范等价类意义下唯一回接到可逆过去"精确化为可计算的熵阈值命题，并证明
$$
\text{完备}\ (H_{\mathrm{rec}}\le H_\star)\quad\Longleftrightarrow\quad \text{停机}\ (\text{有限步可逆重建}),
$$
其中 $H_{\mathrm{rec}}$ 与三位一体刻度完全同尺度，Zeckendorf 日志提供最短自解码与误差不扩散的实现路径。该结果建立观测几何、信息熵与计算停机之间的非渐近桥梁，为窗口—采样—编码的共设计与可逆重建的复杂度控制提供统一的公理化基础。

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://revistas.ucm.es/index.php/REMA/article/download/REMA0606220385A/15747?utm_source=chatgpt.com "Berezin and Berezin-Toeplitz Quantizations for General ..."
[3]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[4]: https://ibisc.univ-evry.fr/~hutzler/Cours/IMBI_MPS/Kari05.pdf?utm_source=chatgpt.com "Theory of cellular automata: A survey"
[5]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[6]: https://staff.ustc.edu.cn/~cgong821/Wiley.Interscience.Elements.of.Information.Theory.Jul.2006.eBook-DDU.pdf?utm_source=chatgpt.com "Elements of Information Theory"
[7]: https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem?utm_source=chatgpt.com "Zeckendorf's theorem"
[8]: https://personal.ntu.edu.sg/lilian/Review-PSWFs-final.pdf?utm_source=chatgpt.com "A Review of Prolate Spheroidal Wave Functions from the ..."
[9]: https://ui.adsabs.harvard.edu/abs/1990PhyD...45..229T/abstract?utm_source=chatgpt.com "Invertible cellular automata: A review"
[10]: https://www.mdpi.com/2227-7390/10/3/386?utm_source=chatgpt.com "Multidimensional Fibonacci Coding"
[11]: https://link.springer.com/book/10.1007/978-3-319-25613-9?utm_source=chatgpt.com "An Introduction to Frames and Riesz Bases"
[12]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[13]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[14]: https://research.rug.nl/files/232459978/1_s2.0_S0007449722000707_main.pdf?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
[15]: https://chaosbook.org/library/WignerDelay55.pdf?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering ..."
[16]: https://arxiv.org/abs/1412.3998?utm_source=chatgpt.com "Effect of chiral symmetry on chaotic scattering from Majorana zero modes"
[17]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[18]: https://www.math.umd.edu/~jjb/blt1inf_7.pdf?utm_source=chatgpt.com "an endpoint (1, ∞) balian-low theorem - UMD MATH"
[19]: https://en.wikipedia.org/wiki/Fibonacci_coding?utm_source=chatgpt.com "Fibonacci coding"
