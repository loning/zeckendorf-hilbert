# 册 B｜法典（大众）

## 第一门｜见之门（星窗印・一秤诀・玄砂漏・静相铃）

> 体例：每条含**法条**（简述）、**数学推理**（判据/证明要点）、**可检步骤**（最小可复演），并统一使用记号与公设（见册 A）。

---

### 1. 星窗印（凡测必窗）

**法条**
任何一次"看见"，都是某个窗 $W$ 对真实 $f$ 的加权读数：$\displaystyle \langle f\rangle_W=\int f(E)\,W(E)\,dE$；$W\ge0$，$\int W=1$。

**数学推理**
(1) 线性与稳定：若 $|W|_1=1$，则

$$
|\langle f\rangle_W-\langle g\rangle_W|\le \int |f-g|\,W \le |f-g|_\infty .
$$

(2) 换窗敏感度（窗误差上界）：

$$
|\langle f\rangle_{W_1}-\langle f\rangle_{W_2}|\le |f|_\infty \,|W_1-W_2|_1 .
$$

(3) 不可辨域（核非空）：有限窗族 $\{W_i\}_{i=1}^m$ 定义 $\mathcal A:f\mapsto(\langle f\rangle_{W_i})_{i=1}^m$。当信号空间维数 $>m$（如 $L^2$ 无限维），由秩—核定理

$$
\dim \ker \mathcal A=\infty,\quad \exists\,h\ne0:\ \langle h\rangle_{W_i}=0\ \forall i .
$$

(4) 三分误差预算（NPE）：任何窗化估计的非渐近误差

$$
\mathrm{Err}\le \underbrace{\mathrm{Alias}(W)}_{\text{带外混叠}}
+\underbrace{\mathrm{Bernoulli}(k,W)}_{\text{有限阶 EM 修正}}
+\underbrace{\mathrm{Tail}(k)}_{\text{截断尾项}} .
$$

**可检步骤**
以同一问题，实施"三窗试验"：更换信息来源/时段/人群三种 $W$，若结论显著分歧，则处于不可辨域；延时与加修正后再判。

---

### 2. 一秤诀（换单位不换事实）

**法条**
换单位/刻度不改变事实读数；变量代换 $E'=aE+b$ 下保持

$$
\langle f\rangle_W=\langle f'\rangle_{W'},\quad
W'(E')=\frac{1}{|a|}\,W\!\left(\frac{E'-b}{a}\right),\
f'(E')=f\!\left(\frac{E'-b}{a}\right).
$$

**数学推理**
(1) 守读数（代换证明）：由 $E=(E'-b)/a$，$dE=dE'/a$

$$
\int f(E)W(E)\,dE=\int f\!\Big(\tfrac{E'-b}{a}\Big)\,\frac{1}{|a|}W\!\Big(\tfrac{E'-b}{a}\Big)\,dE'
=\int f'(E')W'(E')\,dE'.
$$

(2) 刻度群与不变性：尺度 $a>0$、平移 $b\in\mathbb R$ 组成仿射群 $G$；读数是 $G$-不变泛函。
(3) 影子刻度（拉格朗日乘子）：在"价值—预算"泛函

$$
\mathcal L=\mathbb E[U]-\lambda B ,
$$

$\lambda=\partial \mathcal L/\partial B$ 为**影子价**；等价于在秤变动下的边际补偿率。
(4) 同秤可谈：若两方各用 $(a_1,b_1)$、$(a_2,b_2)$ 标度，先作 $(a,b)$ 归一（例如 $a_2/a_1$ 与 $b$-校正），再比较 $\langle f\rangle$ 方可避免"秤差偏置"。

**可检步骤**
任何对比先写明 $(a,b)$；用同一 $(a,b)$ 复算旧数据。若结论反转，先修秤，不急下断。

---

### 3. 玄砂漏（分辨—时间的下界）

**法条**
想分得更清，必须付出更多时间：$\Delta t\,\Delta\omega\ge \tfrac12$。

**数学推理**
(1) 定义方差：对窗函数 $g\in L^2(\mathbb R)$（作分析窗，$|g|_2=1$），设

$$
\Delta t^2=\int (t-\mu_t)^2 |g(t)|^2 dt,\quad
\Delta \omega^2=\int (\omega-\mu_\omega)^2 |\widehat g(\omega)|^2 d\omega,
$$

其中 $\mu_t=\int t|g|^2$，$\mu_\omega=\int \omega |\widehat g|^2$。
(2) Heisenberg 不等式（证明要点）：由

$$
| (t-\mu_t)g|_2\, | (\omega-\mu_\omega)\widehat g|_2
\ge \tfrac12 |g|_2^2=\tfrac12,
$$

得 $\Delta t\,\Delta\omega\ge \tfrac12$。等号当且仅当 $g$ 为高斯。
(3) 窗化估计的代价函数：若要求频率分辨 $\Delta\omega\le \epsilon$，最短等待窗满足 $\Delta t\ge \frac{1}{2\epsilon}$。
(4) 与 NPE 耦合：拉长时间窗（增 $k$ 与减带外能量）会同时降低 $\mathrm{Alias}(W)$ 与 $\mathrm{Tail}(k)$，但增加观测成本——形成优化折中：

$$
\min_{\Delta t,k}\ \mathrm{Err}(\Delta t,k)+\lambda\,\Delta t .
$$

**可检步骤**
对重要判决设最小等待窗 $T_{\min}=\frac{1}{2\epsilon}$（$\epsilon$ 由期望分辨率定），并记录 NPE 三项在等待前后之变化；未达阈值不结论。

---

### 4. 静相铃（方向＝相位导数，多少＝密度）

**法条**
"往哪儿去"的方向由相位决定，"带多少"由密度决定；它们共享同一把秤：

$$
\varphi'(E)=\pi\,\rho(E).
$$

**数学推理**
(1) 谱词典：设 $H$ 为一维自伴算子，其谱测度 $\rho(E)$ 与散射相位 $\varphi(E)$ 关联。令 $S(E)$ 为散射矩阵，谱移函数 $\xi(E)$ 满足

$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad \partial_E\arg \det S(E)=-2\pi\,\xi'(E).
$$

(2) 相位—密度同秤：在 Weyl–Titchmarsh 词典中，$\rho(E)=\frac{1}{\pi}\Im M(E+i0)$（$M$ 为 m-函数），而总相位 $\varphi(E)$ 的导数与 $\Im M$ 成正比，得

$$
\varphi'(E)=\pi\,\rho(E).
$$

(3) 窗化读数的一致性：对任何非负窗 $W$，

$$
\int \varphi'(E)\,W(E)\,dE
=\pi\int \rho(E)\,W(E)\,dE,
$$

即"方向变化率的窗化平均"等于"密度的窗化平均"（同秤等价）。
(4) 相对谱密度表述：若以参照 $H_0$ 定义相对谱移 $\xi$，则

$$
\partial_E \arg\det S(E)=-2\pi\,\xi'(E),\quad
\rho_{\text{rel}}(E)=\xi'(E),
$$

故方向变化的判据与"多少"的相对度量一致。

**可检步骤**
为任一目标先给出"方向词"（$\varphi$ 的趋势）与"配重表"（$\rho$ 的资源比例）。以相同窗 $W$ 计算两侧的窗化平均；若

$$
\Big|\int \varphi'(E)W-\pi\int \rho(E)W\Big|>\varepsilon,
$$

则为"伪愿"或"错配重"，需重配资源或修正方向。

---

## 小结（见之门）

1. **星窗印**确立读数的窗结构与不可辨域；
2. **一秤诀**保证变量代换下事实不变与"影子刻度"的边际意义；
3. **玄砂漏**给出"分辨—时间"的硬下界并嵌入 NPE 误差优化；
4. **静相铃**用 $\varphi'(E)=\pi\rho(E)$ 把"方向"与"数量"统一到同一秤上，供配重校验。
