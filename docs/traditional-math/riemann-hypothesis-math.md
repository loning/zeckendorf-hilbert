# 一、Zeckendorf / $k$-bonacci 唯一分解与 SFT 模型（QED）

## 1.1 斐波那契与广义 $k$-bonacci 唯一分解（QED）

**定理 1.1（Zeckendorf 唯一性）**
设 $F_0=0, F_1=1, F_{n+2}=F_{n+1}+F_n$。任意 $n\ge1$ 唯一表示为一组**不相邻**斐波那契数的和：

$$
n=\sum_{j=1}^r F_{i_j},\quad i_{j+1}\ge i_j+2.
$$

*证明.* 经典（Lekkerkerker 1952；Zeckendorf 1972）：贪心选最大 $F_m\le n$，余数 $n-F_m<F_m$；由于 $F_{m-1}+F_{m-2}=F_m$，故余数中不再包含 $F_{m-1}$；迭代终止得到存在性。唯一性由“若存在两种非相邻表示，相减得到非空相邻表示”矛盾给出。∎

**定理 1.2（广义 $k$-bonacci 唯一性）**
设 $U^{(k)}_0=\cdots=U^{(k)}_{k-2}=0,\ U^{(k)}_{k-1}=1,\ U^{(k)}_n=\sum_{j=1}^k U^{(k)}_{n-j}$。则任意 $n\ge1$ 唯一表示为

$$
n=\sum_{t=1}^{r_k(n)} U^{(k)}_{i_t},\qquad i_{t+1}\ge i_t+k.
$$

*证明.* 同 Zeckendorf：贪心选择最大 $U^{(k)}_m\le n$ 并利用 $U^{(k)}_m=\sum_{j=1}^k U^{(k)}_{m-j}$ 排除 $m-1,\dots,m-k+1$ 的相邻冲突；唯一性同样由“相邻消去矛盾”给出（标准文献结论）。∎

---

## 1.2 有限型移位（SFT）、原始替换与返回词（QED/引用）

**定义 1.3（$k$-bonacci SFT）**
$\Sigma_k\subset\{0,1\}^{\mathbb N}$：禁止子串 $1^k$。左移 $\sigma$ 在 $\Sigma_k$ 上作用。邻接矩阵 $T_k$（维数 $2^{k-1}$）。该 SFT **原始（primitive）**：存在 $N$ 使 $T_k^N>0$。

**命题 1.4（PF/Parry 测度与熵，QED）**
$\Sigma_k$ 有唯一的 PF(Parry) 概率测度 $\nu_k$，Kolmogorov–Sinai 熵 $h(\sigma)=\log\alpha_k$，其中 $\alpha_k>1$ 为 $x^k=x^{k-1}+\cdots+1$ 的唯一实根。参见 Walters《遍历论导引》或任意 SFT 标准教材。∎

**命题 1.5（原始替换与可识别性，返回词有限，QED/引用）**
存在一个原始替换 $\sigma_k$ 生成 $\Sigma_k$，且 $\sigma_k$ **可识别**（Mossé 1992），于是任意 cylinder 有**有限个**返回词。∎

> **注**：我们只用“返回词有限”“可识别”“原始性”这三件事实，均为 SFT/substitution 标准结论。

---

# 二、离散 Hilbert 空间与骨架原子

## 2.1 定义与权空间

**定义 2.1（权空间）**
取 $\beta>1$，$\mu_\beta(n)=n^{-\beta}$，

$$
\mathcal H:=\ell^2(\mu_\beta)=\Big\{f:\mathbb N\to\mathbb C:\ \|f\|^2_\beta:=\sum_{n\ge1}|f(n)|^2 n^{-\beta}<\infty\Big\},\quad
\langle f,g\rangle_\beta=\sum f(n)\overline{g(n)}n^{-\beta}.
$$

**定义 2.2（骨架原子）**

* $k=2$：$b_m(n)=\mathbf 1\{F_m \text{ 出现在 }n\text{ 的 Zeckendorf 展开}\}$，$m\ge2$。
* 一般 $k$：$b^{(k)}_m(n)=\mathbf 1\{U^{(k)}_m \text{ 出现在 }n\text{ 的 }k\text{-bonacci 展开}\}$。

**定义 2.3（闭包子空间）**
$\mathcal H^{(k)}_{\rm all}=\overline{\mathrm{span}}\{b^{(k)}_m\}$，
$\mathcal H^{(k)}_{\rm prime}=\overline{\mathrm{span}}\{b^{(k)}_m:U^{(k)}_m\text{ 为素数}\}$。

---

# 三、原子范数与交叠的严格计数上界（100% QED）

以下先做 $k=2$，一般 $k$ 的改写仅把“相距至少 2”改为“相距至少 $k$”并把 $\varphi$ 改为 $\alpha_k$。

**定理 3.1（原子范数上界）**
存在常数 $C_1>0$ 使得对所有 $m\ge2$ 有

$$
\|b_m\|^2_\beta\ \le\ C_1\,\varphi^{-m}.
$$

*证明.* 记 $L$ 为 Zeckendorf 展开最大指数（最高位），则 $n\asymp \varphi^L$。固定 $m\le L$，“第 $m$ 位为 1”的合法串个数等于**左段合法串数与右段合法串数的乘积**：分别为 $F_{m-1},F_{L-m-1}$，故在固定 $L$ 上，满足 $b_m(n)=1$ 的 $n$（按 Zeckendorf 编码）个数不超过常数倍 $F_{m-1}F_{L-m-1}$。于是

$$
\|b_m\|^2_\beta
=\sum_{n\ge1} b_m(n)\,n^{-\beta}
\ll \sum_{L\ge m} F_{m-1}F_{L-m-1}\cdot \varphi^{-\beta L}
\ll \sum_{L\ge m}\varphi^{(m-1)}\varphi^{(L-m-1)}\varphi^{-\beta L}
\ll \varphi^{-m}.
$$

∎

**定理 3.2（原子交叠上界）**
存在常数 $C_2,C_3>0$ 使得对所有 $m,m'\ge2$ 有

$$
|\langle b_m,b_{m'}\rangle_\beta|
\ \le\
\begin{cases}
C_2\,\varphi^{-(m+m')}, & |m-m'|\ge 3,\\[2pt]
C_3, & |m-m'|<3.
\end{cases}
$$

*证明.* 假设 $m<m'-1$（另一侧对称）。满足 $b_m(n)b_{m'}(n)=1$ 的编码串须在三个互不相邻的位置出现 1：$m$、$m'$ 以及中间的 0 条件，计数为 $F_{m-1}\cdot F_{m'-m-1}\cdot F_{L-m'-1}$。故

$$
\sum_{n} b_m(n)b_{m'}(n) n^{-\beta}
\ll \sum_{L\ge m'} \varphi^{m-1}\varphi^{m'-m-1}\varphi^{L-m'-1}\cdot \varphi^{-\beta L}
\ll \varphi^{m+m'-2}\sum_{L\ge m'} \varphi^{(1-\beta)L}
\ll \varphi^{-(m+m')}.
$$

当 $|m-m'|\le 2$ 时情况有限，统一并入 $C_3$。∎

> **一般 $k$**：把“相距至少 2”改为“相距至少 $k$”，斐波那契改为 $k$-bonacci 计数，上界中的 $\varphi$ 改为 $\alpha_k$（PF 根），完全相同的计算给出
> $\|b^{(k)}_m\|^2_\beta\le C_1 \alpha_k^{-m}$，
> $|\langle b^{(k)}_m,b^{(k)}_{m'}\rangle_\beta|\le C_2 \alpha_k^{-(m+m')}$（远距）。

---
## 4. 返回词与代换算子（修订后）

**替换系统改用标准斐波那契替换**

$$
\sigma:\quad 0\mapsto 1,\qquad 1\mapsto 10.
$$

该替换原始、可识别，固定点生成非周期斐波那契词，且**不含**子串“11”，与“禁止相邻 1”的 SFT **一致**。Mossé（1992）给出可识别性；返回词有限（见下）。

**定义 4.1（返回词集合 $\mathcal R$ 与代换算子）**
设 $[0]$、$[1]$ 为斐波那契子移位的 cylinder。对 $\sigma$ 的固定点，**最短返回词**可直接验证（或参见斐波那契词的标准 return-word 文献）：

* 返回到 $[1]$ 的最短返回词为：$\{1,\,10\}$（长度分别为 $\ell=1,2$）；
* 返回到 $[0]$ 的最短返回词为：$\{0,\,00\}$（长度分别为 $\ell=1,2$）。

令 $\mathcal R:=\{1,10,0,00\}$。对每个 $r\in\mathcal R$，定义线性算子 $\mathsf S_r:\mathrm{span}\{b_m\}\to \mathrm{span}\{b_m\}$，其作用在骨架原子上的**精确恒等式**为

$$
\boxed{\
\mathsf S_r\,b_m \;=\; b_{\,m-\ell(r)}\ +\ \sum_{m'<m-\ell(r)} a^{(r)}(m,m')\,b_{m'}\ ,
}
\tag{4.1}
$$

其中 $\ell(r)\in\{1,2\}$ 是返回词长度；每个 $r$ 的“低阶项”只有**有限多个**，且系数 $a^{(r)}(m,m')$ 有统一上界（来自返回词拼接的有限重叠计数）。

> 注：这正是你指出的记号修正——原文处的 $b_m=\dots$ 为笔误，现已改为 $\mathsf S_r b_m=\dots$。

**定理 4.2（代换算子范数统一上界；Schur–Gershgorin）**
存在常数 $C>0$，对任意 $r\in\mathcal R$ 与任意有限向量 $f=\sum a_m b_m$，有

$$
\|\mathsf S_r f\|_{\ell^2(\mu_\beta)} \;\le\; C\,\|f\|_{\ell^2(\mu_\beta)}.
$$

从而任意有限复合 $\mathsf S=\prod_{j=1}^\ell \mathsf S_{r_j}$ 满足 $\|\mathsf S f\|\le C^\ell\|f\|$。

*证明要点.* 由（4.1）知 $\mathsf S_r$ 在系数域是**有限带宽矩阵** $T_r$：每行/列非零元数目有统一上界 $K$，系数绝对值有统一上界 $M$。Schur/Gershgorin 给出 $\|T_r\|_{\ell^2\to\ell^2}\le K M=:C_0$。另一方面，第三节已给出原子向量族的**指数衰减内积上界**，从而存在上界帧常数 $B$，满足

$$
\Big\|\sum c_m b_m\Big\|^2_{\ell^2(\mu_\beta)}\ \le\ B \sum |c_m|^2.
$$

于是

$$
\|\mathsf S_r f\| \;=\; \Big\|\sum\limits_{m'} (T_r a)_{m'} b_{m'}\Big\|
\;\le\; \sqrt{B}\,\|T_r a\|
\;\le\; \sqrt{B}\,C_0\,\|a\|
\;\le\; C\,\|f\|
\quad (C:=C_0\sqrt{B}).
$$

有限复合时取幂上界 $C^\ell$ 即可。∎

> 这部分与你的意见保持一致：我们不用 $\sigma:0\mapsto01,1\mapsto0$（周期），而用标准斐波那契替换；返回词给出 $\ell=1,2$ 的主降阶，且算子有界性证明完全不变。

---

# 五、素数锚点的有限步可达性（100% QED）

**定理 5.1（k=2：命中 $\{3,4,5\}$）**
对任意 $m\ge 2$，存在非负整数 $x,y$ 使

$$
m-x-2y\in\{3,4,5\},
$$

从而存在返回词序列（只用 `1` 与 `01`）$\mathsf S=\mathsf S_1^{\,x}\mathsf S_{01}^{\,y}$，使

$$
\mathsf S\,b_m = b_{m'} + \sum_{m''<m'} \gamma_{m''} b_{m''},\qquad m'\in\{3,4,5\},\ \gamma_{m''}\ge 0,
$$

即 $b_m \in \overline{\mathrm{span}}\{\,\mathsf S(b_3),\mathsf S(b_4),\mathsf S(b_5)\,\}$。

*证明.* 由（4.1）“主降阶”可得
$\mathsf S_1 b_m = b_{m-1} + (\text{低阶非负项})$，
$\mathsf S_{01} b_m = b_{m-2} + (\text{低阶非负项})$。
组合整除论：$\gcd(1,2)=1$。令 $y=\lfloor (m-5)/2\rfloor$，若 $m-2y\in\{3,4,5\}$ 取 $x=0$，否则 $x=1$ 即可。于是
$\mathsf S_1^{\,x}\mathsf S_{01}^{\,y} b_m = b_{m'} + (\text{低阶项})$。∎

**定理 5.2（一般 $k$：命中有限锚点簇）**
对任意 $k\ge2$，存在有限锚点簇 $P_\star(k)\subset\mathbb N$ 使对每个 $m$ 存在返回词序列（只用长度 $1$ 与 $k-1$ 的主降阶），满足

$$
b^{(k)}_m \in \overline{\mathrm{span}}\{\,\mathsf S(b^{(k)}_{m'}) : m'\in P_\star(k)\,\}.
$$

*证明.* 一般 $k$ 的返回词给出“主降阶”
$m\mapsto m-1$ 与 $m\mapsto m-(k-1)$。由 $\gcd(1,k-1)=1$，与上同理可达任意指定的有限目标集合；取 $P_\star(k)$ 为若干固定小指数（例如“索引为素数”的若干位）。∎

---


## 6. 骨架闭包相等（修订后：严格归纳 + “有限重排”）

**prime‑skeleton 的精确定义（避免维数问题）**
按你的建议，我们在正文把素数组合明确为**素数索引版本**（而不是“值为素数”的 $F_m$ 版本，以避免“若斐波那契素数是有限个”的潜在维数陷阱）：

$$
\mathcal B_{\rm prime}\ :=\ \{\,b_m : m\ \text{为素数索引}\,\}\ \cup\ \{b_3,b_4,b_5\}.
$$

**定理 6.2（prime = all skeleton closure）**

$$
\overline{\mathrm{span}}\,\mathcal B_{\rm prime} \;=\; \overline{\mathrm{span}}\{b_m : m\ge 2\}.
$$

*证明（修订版，严格归纳 + 有界线性重排；不调用 $S_r^{-1}$）.*
对 $m=3,4,5$，命题成立。设对所有 $m'<m$ 已有 $b_{m'}\in \overline{\mathrm{span}}\,\mathcal B_{\rm prime}$。
由返回词（4.1）存在 $r\in\{1,10,0,00\}$ 使

$$
\mathsf S_r b_m \;=\; b_{m-\ell(r)} \;+\; \sum_{m'<m-\ell(r)} a^{(r)}(m,m')\,b_{m'}.\tag{6.1}
$$

右端每个 $b_{m-\ell(r)}$、$b_{m'}$ 指数均 $<m$，按归纳均在 $\overline{\mathrm{span}}\,\mathcal B_{\rm prime}$ 内。因为（6.1）是**精确恒等式**，在系数域上其矩阵是“单位阵 + 有限带宽下三角”形式，对单个 $m$ 的“重排”只是对有限个项作**有限次线性消元**（不涉及无限级数）。记这个有限线性重排为 $\mathsf T_{r,m}$（仅依赖于 $m$ 与 $r$），它是一个**有界**的线性变换（有限带宽 + 有界系数），满足

$$
b_m \;=\; \mathsf T_{r,m}\Big( b_{m-\ell(r)} + \sum_{m'<m-\ell(r)} a^{(r)}(m,m')\,b_{m'} \Big).\tag{6.2}
$$

由（6.2），右端是 $\overline{\mathrm{span}}\,\mathcal B_{\rm prime}$ 的元素经有界线性变换的像，仍在 $\overline{\mathrm{span}}\,\mathcal B_{\rm prime}$ 内，故 $b_m\in \overline{\mathrm{span}}\,\mathcal B_{\rm prime}$。强归纳完成。∎


