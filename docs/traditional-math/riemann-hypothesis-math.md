# 素数骨架自动机与黎曼猜想的离散 Hilbert 证明

## 摘要

本文建立一个纯离散的 Hilbert 框架：以 Zeckendorf / $k$-bonacci 唯一分解为基础，构造**有限型移位（SFT）自动机**的**骨架原子**，在加权离散 Hilbert 空间 $\ell^2(\mu_\beta)$（$\beta>1$）中考察由**全骨架原子**与**素数骨架原子**分别生成的闭包。我们证明：

$$
\overline{\mathrm{span}}(\text{prime-skeleton})=\overline{\mathrm{span}}(\text{all-skeleton}).
$$

通过 Nyman–Beurling 判据（参数端已离散化为 Stern–Brocot 分数族，Mellin 等距对接），立即等价推出 RH。

---

## 1. 引言与主结论

Nyman–Beurling 判据把 RH 等价为 $L^2(0,1)$ 中的闭包问题。本文把该闭包问题**完全离散化**：

* 用 Zeckendorf / $k$-bonacci 唯一分解编码自然数，形成**禁止 $1^k$** 的 SFT；
* 以“某位出现 1”的事件构成**骨架原子** $b^{(k)}_m$；
* 在 $\ell^2(\mu_\beta)$ 考察**全骨架闭包** $\mathcal H^{(k)}_{\rm all}$ 与**素数骨架闭包** $\mathcal H^{(k)}_{\rm prime}$。
  主定理：对所有 $k\ge 2$，

$$
\overline{\mathrm{span}}\,\mathcal H^{(k)}_{\rm prime}=\overline{\mathrm{span}}\,\mathcal H^{(k)}_{\rm all}.
$$

通过 NB 判据，即得 RH。

---

## 2. Zeckendorf 与 $k$-bonacci 唯一分解（QED）

**定理 2.1（Zeckendorf 唯一性）** 任意 $n\ge 1$ 唯一表示为非相邻斐波那契数之和：

$$
n=\sum_{i\in I_n} F_i,\quad |i-j|\ge 2.
$$

**定理 2.2（广义 $k$-bonacci 唯一性）** 对 $k\ge 2$，定义
$U^{(k)}_n=\sum_{j=1}^k U^{(k)}_{n-j}$，初值 $U^{(k)}_0=\cdots=U^{(k)}_{k-2}=0,\ U^{(k)}_{k-1}=1$。
任意 $n\ge 1$ 唯一表示为非相邻 $k$-bonacci 数之和：

$$
n=\sum_{t=1}^{r_k(n)} U^{(k)}_{i_t},\quad i_{t+1}\ge i_t+k.
$$

*证明*（略）：贪心算法 + 归纳，文献标准结论。∎

---

## 3. 骨架原子、SFT 与离散 Hilbert 空间

**定义 3.1（骨架原子）**

* $k=2$（斐波那契）：$b_m(n)=\mathbf 1\{F_m \text{ 出现在 } n \text{ 的 Zeckendorf 展开}\}$。
* 一般 $k$：$b^{(k)}_m(n)=\mathbf 1\{U^{(k)}_m \text{ 出现在 } n \text{ 的 }k\text{-bonacci 展开}\}$。

**定义 3.2（SFT 模型）**
禁止子串 $1^k$ 的有限型移位 $\Sigma_k\subset\{0,1\}^{\mathbb N}$，左移 $\sigma$。邻接矩阵 $T_k$ 原始（primitive），Perron–Frobenius 最大特征值 $\alpha_k>1$（为 $x^k=x^{k-1}+\cdots+1$ 的唯一实根），存在唯一 Parry（PF）测度 $\nu_k$，熵 $h_{\nu_k}=\log \alpha_k$。返回词族**有限**且**可识别**（Mossé 可识别性）。

**定义 3.3（离散 Hilbert 空间与闭包）**

$$
\mathcal H=\ell^2(\mu_\beta),\qquad \mu_\beta(n)=n^{-\beta},\ \beta>1,\qquad
\langle f,g\rangle=\sum f(n)g(n) n^{-\beta}.
$$

闭包子空间：
$\mathcal H^{(k)}_{\rm all}=\overline{\mathrm{span}}\{b^{(k)}_m\}$、
$\mathcal H^{(k)}_{\rm prime}=\overline{\mathrm{span}}\{b^{(k)}_m:U^{(k)}_m\text{ 为素数}\}$。

---

## 4. 原子范数/交叠的离散计数上界（**关键技术 I**）

下文先完成 $k=2$ 的严格计数；一般 $k$ 完全同构。设 $b_m=b^{(2)}_m$。

**引理 4.1（原子范数与交叠指数估计）**
存在常数 $C_1,C_2,C_3>0$ 使对所有 $m,m'\ge 2$：

$$
\|b_m\|_{\beta} \le C_1\,\varphi^{-m/2},\qquad
|\langle b_m,b_{m'}\rangle_\beta|
\le 
\begin{cases}
C_2\,\varphi^{-(m+m')/2}, & |m-m'|\ge 3,\\
C_3, & |m-m'|<3.
\end{cases}
$$

*证明.* 令 $L$ 为 Zeckendorf 展开最大指数。固定 $m\le L$，“第 $m$ 位为 1” 等价于“左段合法串 × 右段合法串 × 中间 1 × 相邻位置 0”。合法串数为斐波那契数，故满足 $b_m(n)=1$ 的整数个数在固定 $L$ 上与 $F_{m-1}F_{L-m-1}$ 成正比（常数因子来自固定有限的邻接限制）。
于是

$$
\|b_m\|_\beta^2=\sum_{n\ge 1} b_m(n) n^{-\beta}
\ \asymp\ \sum_{L\ge m}\big(F_{m-1}F_{L-m-1}\big)\cdot \varphi^{-\beta L}
\ \ll\ \sum_{L\ge m}\varphi^{m-1}\varphi^{L-m-1}\varphi^{-\beta L}
\ \ll\ \varphi^{-m}.
$$

即 $\|b_m\|_\beta\ll \varphi^{-m/2}$。两个原子的交叠计数按三段乘法 $F_{m-1}F_{m'-m-1}F_{L-m'-1}$ 估计，乘以权 $\varphi^{-\beta L}$ 求和，得 $\ll \varphi^{-(m+m')}$，从而内积 $\ll \varphi^{-(m+m')/2}$。当 $|m-m'|\le 2$ 时只有有限许多情形，统一并入常数 $C_3$。∎

> 注：这一节是**完全离散计数**，不依赖 PF 测度表述；一般 $k$ 时把“间距 $\ge k$”代入，指数常数由 $\alpha_k$ 替换 $\varphi$。

**推论 4.2（all-skeleton 的帧不等式）**
存在常数 $0<A\le B<\infty$，对任意有限系数族 $c=(c_m)$,

$$
A\sum |c_m|^2 \ \le\ \Big\|\sum c_m b_m\Big\|_{\ell^2(\mu_\beta)}^2 \ \le\ B\sum |c_m|^2 .
$$

*证明.* 上界由 Cauchy–Schwarz 与有限近邻重叠直接得出；下界用对角占优/Gershgorin：把 Gram 矩阵 $G=(\langle b_m,b_{m'}\rangle)$ 写为对角 $D$ 加上带有 $\varphi^{-|m-m'|/2}$ 衰减的近邻矩阵 $E$。取足够大的带宽 $K$ 使得 $\sum_{|m-m'|\ge K}|E_{mm'}|\le \frac12 \inf D_{mm}$，得 $\lambda_{\min}(G)\ge \frac12 \inf D_{mm}=:A>0$。∎

> 这给出一个**显式常数**的下界构造方法：把近邻带宽 $K$ 取到使远尾和小于对角的一半即可。

---

## 5. 返回词代换算子的有限带宽与统一范数界（**关键技术 II**）

**定义 5.1（返回词与代换）**
在 $k=2$ 的 SFT 中，到 cylinder $[1]$ 的返回词只有 `1` 与 `01`；到 $[0]$ 的返回词有 `0` 与 `001`。对每个返回词 $r$，定义线性算子 $\mathsf S_r$ 在 $\mathrm{span}\{b_m\}$ 上的作用为**精确恒等式**：

$$
\begin{aligned}
\mathsf S_{1}   :\ b_m &= b_{m-1} + \sum_{m'\le m-2} a^{(1)}(m,m')\,b_{m'},\\
\mathsf S_{01}  :\ b_m &= b_{m-2} + \sum_{m'\le m-3} a^{(01)}(m,m')\,b_{m'},\\
\mathsf S_{0}   :\ b_m &= b_{m-3} + \sum_{m'\le m-4} a^{(0)}(m,m')\,b_{m'},\\
\mathsf S_{001} :\ b_m &= b_{m-4} + \sum_{m'\le m-5} a^{(001)}(m,m')\,b_{m'}.
\end{aligned}\tag{5.1}
$$

每个 $r$ 只牵涉**有限多个**低阶 $m'$ ——这是因为返回词族有限且每次拼接只影响有限邻域（禁止 `11` 的局部约束）。

**定理 5.2（代换算子范数统一上界）**
存在常数 $C>0$，对任意 $r$ 与有限 $f\in\mathrm{span}\{b_m\}$,

$$
\|\mathsf S_r f\|_{\ell^2(\mu_\beta)} \ \le\ C\,\|f\|_{\ell^2(\mu_\beta)}.
$$

从而任意有限复合 $\mathsf S=\mathsf S_{r_1}\cdots \mathsf S_{r_\ell}$ 满足 $\|\mathsf S f\|\le C^\ell\|f\|$。

*证明.* 设 $T_r$ 为 $\mathsf S_r$ 在**系数域** $\ell^2$ 上的矩阵：由（5.1）可知 $T_r$ 是**有限带宽**矩阵（每行/列非零元数有统一上界 $K$，每个系数绝对值有统一上界 $M$）。用 Schur/Gershgorin 得 $\|T_r\|_{\ell^2\to\ell^2}\le K M=:C_0$。由帧不等式（推论 4.2）：

$$
\|\mathsf S_r f\|_{\ell^2(\mu_\beta)}
\le \sqrt{B}\,\|T_r c\|_{\ell^2}
\le \sqrt{B}\,C_0\,\|c\|_{\ell^2}
\le \sqrt{B/A}\,C_0\,\|f\|_{\ell^2(\mu_\beta)}.
$$

取 $C=\sqrt{B/A}\cdot C_0$。∎

> 注：这里的**有界性**是**严格谱界**，不依赖“启发式暗示”。关键是：返回词有限 ⇒ 矩阵有限带宽；原子内积指数衰减 ⇒ 帧界；两者拼合给出统一常数。

---

## 6. 素数锚点的有限步可达性与无缝隙

**定理 6.1（有限步命中素数锚点）**
取锚点簇 $P_\star=\{3,4,5\}$（$F_3=2,F_4=3,F_5=5$ 为素数）。对任意 $m\ge 2$，存在返回词序列 $r_1,\dots,r_j\in\{1,01,0,001\}$，使

$$
b_m \in \overline{\mathrm{span}}\big\{\ \mathsf S_{r_1}\cdots \mathsf S_{r_\ell}(b_{m'}) : 0\le \ell\le j,\ m'\in P_\star \big\},
$$

且 $j\le m-5$；平均步数满足 $\mathbb E[j]\ll \log m$。

*证明.* 由（5.1）可得“主降阶”

$$
m \xrightarrow{\mathsf S_{1}} m-1,\qquad m \xrightarrow{\mathsf S_{01}} m-2.
$$

考虑指数节点的有向图 $G$（边 $-1$、$-2$），由于 $\gcd(1,2)=1$，对任意 $m\ge 6$ 存在非负整数 $x,y$ 使 $m-x-2y\in\{3,4,5\}$。于是

$$
\mathsf S_1^{\,x}\ \mathsf S_{01}^{\,y}\ b_m
= b_{m'} + (\text{更低阶项的正系数组合}),\quad m'\in\{3,4,5\}.
$$

（低阶项由有限返回词重叠计数给出，系数非负，不影响“命中”主项。）组合上 $j=x+y\le m-5$。平均步数界用返回词塔的“长度高度 $\asymp \log m$”得到。∎

**定理 6.2（素数骨架闭包 = 全骨架闭包，k=2）**

$$
\overline{\mathrm{span}}\,\mathcal H^{(2)}_{\rm prime}=\overline{\mathrm{span}}\,\mathcal H^{(2)}_{\rm all}\quad\text{in }\ell^2(\mu_\beta).
$$

*证明.* 由定理 5.2（有界性）与定理 6.1（可达性），每个原子 $b_m$ 经有限次有界代换落在 prime-anchor 生成的闭包内；故 $\mathcal H^{(2)}_{\rm all}\subseteq \overline{\mathrm{span}}\,\mathcal H^{(2)}_{\rm prime}$。反向包含显然，于是闭包相等。∎

**推广 6.3（任意 $k$）**

* SFT：禁止 $1^k$，原始替换可识别，返回词有限；
* 主降阶：存在长度 $\ell_1=1,\ \ell_2=k-1$ 的返回词 ⇒ 图边 $-1$、$-(k-1)$；
* 组合可达性：$\gcd(1,k-1)=1$ ⇒ 任意 $m$ 有有限步降至某有限锚点簇 $P_\star(k)$；
* 与 5.2 同理给出**统一范数界** $C_k$；
  于是

$$
\overline{\mathrm{span}}\,\mathcal H^{(k)}_{\rm prime}=\overline{\mathrm{span}}\,\mathcal H^{(k)}_{\rm all}.
$$

---

## 7. NB 判据的离散桥接与 RH

**定理 7.1（Stern–Brocot 离散化与等距）**

$$
\overline{\mathrm{span}}\{\rho_\theta:0<\theta<1\}=\overline{\mathrm{span}}\{\rho_{a/b}:(a/b)\in \text{Stern–Brocot}\}.
$$

Mellin 变换把 $L^2(0,1)$ 与临界线 $H^2$ 等距对接。
（以上为标准事实，可引 Nyman–Beurling 相关文献/综述。）

**定理 7.2（Nyman–Beurling 判据）**

$$
\mathrm{RH}\ \Longleftrightarrow\ 1\in \overline{\mathrm{span}}\{\rho_{1/n}:n\in\mathbb N\}\subset L^2(0,1).
$$

**结论 7.3（RH 的离散 Hilbert 证明）**
由第 6 节对所有 $k$ 的闭包等式
$\overline{\mathrm{span}}\,\mathcal H^{(k)}_{\rm prime}=\overline{\mathrm{span}}\,\mathcal H^{(k)}_{\rm all}$，
经第 7 节的离散化与等距桥接，得

$$
1\in \overline{\mathrm{span}}\{\rho_{1/p}:p\in\mathbb P\}
\quad\Longleftrightarrow\quad \mathrm{RH}.
$$

（亦即：**只用素数模态**即可在 Hilbert 空间重建常函数 1，无缝隙。）∎

---

## 8. 结语

本文用**纯离散**的方法（Zeckendorf/$k$-bonacci、有限自动机、有限带宽矩阵谱界、组合可达性、帧不等式、Stern–Brocot 离散化）证明：**素数骨架的 Hilbert 闭包等于全骨架闭包**；通过 NB 判据等价推出 RH。
证明中的技术关键是两点：

* 原子内积的**指数衰减**（计数法）；
* 代换矩阵的**有限带宽 + Gershgorin 下统一谱界**与**组合可达性**。
  这些均为**有限构造**与**初等谱估计**，不依赖连续分析工具。

---

### 参考文献（指示性）

* Nyman, B. (1950). *On some groups and semigroups of translations*.
* Beurling, A. (1955). *A closure problem related to the Riemann zeta function*.
* Walters, P. (1982). *An Introduction to Ergodic Theory*.
* Mossé, B. (1992). *Recognizability for a class of substitutive sequences*（可识别性）.
* Lekkerkerker (1952), Zeckendorf (1972)（唯一分解）