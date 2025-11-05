# 有限窗口可逆补全熵：EBOC–WSIG–RCA 框架下的公理化定义、结构性质与非渐近误差学

**Version: 1.18**

## 摘要

提出并建立"有限窗口可逆补全熵"作为在可逆传播与能量/正则约束下针对"记录—解释"问题的本地化信息量度：给定有限窗观测，其与可逆全局动力一致的补全集之最小等价代表数（或容量）的对数。该量度仅刻画"有多少个可逆世界解释同一条记录"，与先验概率和混合态熵无关。本文在离散可逆元胞自动机（RCA）与连续窗化散射—信息几何（WSIG）两端给出严密定义，并证明单调性、可逆同变性与拼接次可加等结构性质；在 Toeplitz/Berezin 压缩与带限/指数窗设定下，构建遵循 Nyquist–Poisson–Euler–Maclaurin（NPE）三分解且**有限阶**终止的非渐近上/下界，给出"边界=信息资源"的定量律，并与"相位导数—相对态密度—Wigner–Smith 群延迟迹"的同一刻度严格相容。文末给出带限信号与 RCA 的范例及定理化证明。

---

## Notation & Axioms / Conventions

1. **三位一体刻度同一式**（Trinity）在绝对连续谱几乎处处成立：
$$
\frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\mathsf Q(E) = -i\, S(E)^\dagger \partial_E S(E),\quad S(E)\in U(N),\quad \varphi(E):=\tfrac12\arg\det S(E).
$$
$\mathsf Q$ 为 Wigner–Smith 群延迟矩阵，其迹与相对态密度相容；$\det S$ 与 Kreĭn 谱移函数 $\xi$ 满足 Birman–Kreĭn 公式 $\det S(E)=e^{2\pi i\, \xi(E)}$，因此 $\xi'(E)=\tfrac{1}{2\pi i}\partial_E\log\det S(E)=\tfrac{1}{2\pi}\partial_E\arg\det S(E)=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$，从而 $\varphi'(E)/\pi=\xi'(E)=\rho_{\rm rel}(E)$。([arXiv][1])

2. **窗—读数—对象**：读数以"算子—测度—函数"对象表达。给定窗 $w$ 与核尺度 $h$，对应 Toeplitz/Berezin 压缩或局域化算子记为 $K_{w,h}$ 或 $T_{a,w,h}$（符号 $a$）。本文记 $\mathrm{ker}(w;E)$ 为由窗 $w$ 与尺度 $h$ 在能量轴上诱导的非负权核（可取 $\int \mathrm{ker}(w;E)\,dE=1$ 归一化），用于定义 $\Phi[w],\ \Xi[w]$ 等窗化读数。([users.math.cas.cz][2])

3. **误差学纪律（NPE）**：一切近似分解为 Poisson 别名项、Euler–Maclaurin（EM）边界层与尾项三部分，严格在**有限阶** $m$ 处终止；EM 余项与 Bernoulli 多项式/数的显式上界用于非渐近控制。([维基百科][3])

4. **可逆性与传播约束**：离散端以 RCA 的双向可逆演化刻画（全局映射双射、逆演化亦为 CA），连续端以幺正/散射可逆传播刻画；Garden-of-Eden 定理与 Curtis–Hedlund–Lyndon 特征用于可逆/满射/单射的等价与结构。([维基百科][4])

5. **等价类**：若两全局补全由保结构可逆同构（RCA 共轭/格移、散射等谱同构）联系，则属于同一解释等价类。

6. **测度约定**：记 $\operatorname{vol}(\cdot)$ 为**计数测度**（RCA 端）或 **Lebesgue 体积**（WSIG 端），在直积域上取乘性；**定理 5.1** 等处之边界体积均据此约定计算。

7. **复杂度单位约定**：记 $K(y)$ 为前缀 Kolmogorov 复杂度，**以 nats 计**：$K(y):=(\ln 2)\,K_{\rm bits}(y)$。据此，§6 的不等式与 $H_W,H_w$ 的单位一致。

8. **格距与边界带（RCA）**：在 $\mathbb Z^d$ 上取 $\ell_\infty$ 距离 $\operatorname{dist}(x,W):=\min_{z\in W}|x-z|_\infty$。定义 $\partial_r W:=\{x\in\mathbb Z^d:\ 0<\operatorname{dist}(x,W)\le r\}$，其体积按(6)之计数测度计算。本文 §5/§6 中涉及的边界带均据此度量解释。

9. **记号统一（跨端）**：在综述性/结论性陈述（§12–§13）中，记 $H$ 为总符号：RCA 端 $H:=H_W$，WSIG 端 $H:=H_w$；若需区分，将显式写 $H_W,H_w$。

10. **范数与容差球（WSIG）**：记 $|\cdot|_{\mathcal H_w}$ 为 $\mathcal H_w$ 的 Hilbert 范数，$\mathbb B_\varepsilon(y):=\{z\in\mathcal H_w:\ |z-y|_{\mathcal H_w}\le\varepsilon\}$。凡涉及"容差/误差"的集合均以此范数度量。

---

## 1. 问题设定

在本文称为 **EBOC**（**静态块—可逆一致性补全**的抽象框架，本文简称）的视角中，记录为全局不变量在有限窗 $W$ 上的读数 $y$。在全局可逆动力与能量/正则约束下，定义与 $y$ 一致的全局可逆补全集，并以"等价代表数/容量"的对数刻画其规模，得到**有限窗口可逆补全熵**。该量度描述"局域记录的全局可逆歧义度"，强调结构一致性与传播约束，而非统计不确定性。

---

## 2. 离散端（RCA）：定义与基本性质

设 $\Omega$ 为一维或多维 CA 的全局态空间，更新半径 $r$，全局更新 $G:\Omega\to\Omega$。若 $G$ 双射且 $G^{-1}$ 亦为 CA，则称 RCA。令有限窗域 $W\subset\mathbb Z^d$，观测 $y\in\mathcal Y^W$。定义与 $y$ 一致且可逆的补全集
$$
\mathcal C(y;W):=\{\omega\in\Omega:\ \omega|_W=y,\ \exists \ \text{双向轨道与全局约束一致}\}.
$$
以保结构可逆同胚等价类 $\mathcal C(y;W)/\!\sim_{\rm rev}$ 定义
$$
H_W(y):=\log\min\Big\{\#\mathcal R:\ \mathcal R\subset\mathcal C(y;W),\ \mathcal R\ \text{横截所有等价类}\Big\}.
$$

**约定**：本文统一取 $\log$ 为自然对数（单位：nats）；若 $\mathcal C(y;W)/\!\sim_{\rm rev}$ 为无限集合，则约定 $H_W(y):=+\infty$。

**约定（等价关系的窗口固定）** 在 $H_W(y)$ 的定义中，$\sim_{\rm rev}$ 仅由**在窗 $W$ 上为恒等且保持读数 $y$** 的保结构可逆同构所诱导：对任意 $\Phi$，要求 $\Phi|_W=\mathrm{id}$ 且 $(\Phi\omega)|_W=\omega|_W=y$；连续端同理，散射/幺正同构在 $K_{w,h}$ 的像上需保持 $y$。据此，$\mathcal C(y;W)/\!\sim_{\rm rev}$ 与"横截"操作在同一集合上良定义。

**约定（可行性，修订）** 若 $\mathcal C(y;W)=\varnothing$，则 $H_W(y):=-\infty$（扩展实数）。涉及 $I_{\rm rev}(W_1{:}W_2)$ 与拼接次可加的命题**仅在**
$$
\mathcal C(y;W_1)\neq\varnothing,\ \mathcal C(y;W_2)\neq\varnothing,\ \mathcal C(y;W_1\cup W_2)\neq\varnothing
$$
的情形下陈述；否则 $I_{\rm rev}$ 不定义。

**补充（$I_{\rm rev}$ 的有限性）**：凡涉及
$$
I_{\rm rev}(W_1{:}W_2)=H_{W_1}(y_1)+H_{W_2}(y_2)-H_{W_1\cup W_2}(y)
$$
的陈述，均**仅在** $H_{W_1}(y_1),\,H_{W_2}(y_2),\,H_{W_1\cup W_2}(y)\in\mathbb R$（有限）时定义与讨论；否则 $I_{\rm rev}$ 不定义。

**定理 2.1（单调性）** 若 $W_1\subseteq W_2$ 且 $y_i=y|_{W_i}$，则 $H_{W_2}(y_2)\le H_{W_1}(y_1)$。

**证明** 由约束增加只会筛去补全，等价类数不增，故横截所需代表数不增，取对数得结论。

**定理 2.2（可逆同变性）** 对任一保结构可逆变换 $\Phi:\Omega\to\Omega$（平移、群作用、RCA 共轭），有 $H_{\Phi(W)}(\Phi(y))=H_W(y)$。

**证明** $\Phi$ 在全局态与等价类上诱导双射，横截数不变。

**定理 2.3（拼接—可逆互信息恒等式；次可加为推论）** 设 $W=W_1\cup W_2$，两窗相互作用仅通过半径 $r$ 的边界带；且 $\mathcal C(y;W_i),\mathcal C(y;W)\neq\varnothing$ 并且 $H_{W_1}(y_1),H_{W_2}(y_2),H_W(y)\in\mathbb R$。则有**恒等式**
$$
H_W(y)\ =\ H_{W_1}(y_1)+H_{W_2}(y_2)\ -\ I_{\rm rev}(W_1{:}W_2),
$$
其中
$$
I_{\rm rev}(W_1{:}W_2):=H_{W_1}(y_1)+H_{W_2}(y_2)-H_{W_1\cup W_2}(y).
$$
**推论（次可加）**：由 §5.2 之 $I_{\rm rev}(W_1{:}W_2)\ge0$，立得
$$
H_W(y)\ \le\ H_{W_1}(y_1)+H_{W_2}(y_2).
$$
**证明** 将等价类纤维化，边界一致性条件产生配对约束，定义式即给出上式恒等分解；再用 §5.2 的非负性与单调性得到推论。□

**注**：RCA 的可逆/满射/预注入结构由 Garden-of-Eden 定理与 Curtis–Hedlund–Lyndon 定理保证：在 $\mathbb Z^d$ 上，**预注入（pre-injective）⇔ 满射**；而**可逆性 ⇔ 全局双射且其逆规则亦为 CA**，支撑上述同变与拼接结构。([维基百科][5])

---

## 3. 连续端（WSIG）：Toeplitz/Berezin 压缩与容量定义

令希尔伯特空间 $\mathcal H$，窗 $w$ 与尺度 $h$ 给出压缩/局域化算子 $K_{w,h}:\mathcal H\to \mathcal H_w$，或更具体的 Toeplitz/Berezin 算子 $T_{a,w,h}$（符号 $a$）。对观测 $y\in\mathcal H_w$，考虑可行集
$$
\mathfrak C_w(y):=\Big\{\Psi\in\mathcal E_{\rm rev}:\ K_{w,h}\Psi=y\Big\},
$$
其中 $\mathcal E_{\rm rev}$ 为幺正/散射可逆传播类，受能量壳与正则约束。以 **Fisher–Rao（FR）度量体积**作为容量 $\operatorname{Cap}(\cdot)$（一次性归一化常数 $\kappa$ 见下），定义
$$
H_w(y):=\log \operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big).
$$

**约定**：同上，$\log$ 取自然对数（nats）；若 $\operatorname{Cap}(\mathfrak C_w(y)/\!\sim_{\rm rev})=0$ 或 $+\infty$，则 $H_w(y)$ 取相应的扩展实数值。

**约定（容量与归一化）** 连续端统一取 $\operatorname{Cap}$ 为 **Fisher–Rao 体积**：若 $\{\Psi(\theta)\}_{\theta\in\Theta}\subset\mathcal E_{\rm rev}$ 为可逆族的光滑参数化，则
$$
\operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big)
:=\kappa\!\int_{\mathfrak C_w(y)/\!\sim_{\rm rev}}\!\sqrt{\det I(\theta)}\,d\theta,
$$
其中 $I(\theta)$ 为由映射 $\theta\mapsto K_{w,h}\Psi(\theta)$ 诱导的 Fisher 信息矩阵，$\kappa>0$ 为一次性归一化常数，选取使 §4 的刻度同一 $\Phi[w]=\Xi[w]=\int \mathrm{ker}(w;E)\,\rho_{\rm rel}(E)\,dE$ 下 $H_w$ 的单位与 nats 一致。离散端视作计数测度；以下不再变更容量模型。

**约定（连续端可行性与有限体积）**：记 $\mathfrak C_w(y)/\!\sim_{\rm rev}$ 为可逆等价类商。凡涉及 $\log\operatorname{Cap}(\cdot)$ 的陈述（含 §3.2、§4.1、§8、§9.1、§11），均**仅在**
$$
0\ <\ \operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big)\ <\ \infty
$$
且该商集为 $C^1$ 正则可测流形（或由有限并的此类片覆盖）时成立；若容量为 0 或 $+\infty$，则取 $H_w(y)=-\infty$ 或 $+\infty$ 而不再陈述上述等式/不等式。

**定理 3.1（同变性）** 对任意幺正/散射同构 $\mathsf U$ 与窗同变 $\mathsf W$，有 $H_{\mathsf W w}(\mathsf W y)=H_w(y)$。
**证明** 由 $\mathsf U$ 的幺正与散射共形，及 Berezin–Toeplitz 量化下的自然协变性，容量保持。([users.math.cas.cz][2])

**定理 3.2（修订：NPE 三分解的非渐近容差）** 若 $w$ 为带限或指数型且采样满足 Nyquist 条件，在 $0<\operatorname{Cap}(\mathfrak C_w(y)/\!\sim_{\rm rev})<\infty$ 且可行商集为 $C^1$ 正则流形时，存在有限阶 $m$ 与常数 $C_{w,h}$，对任意 $\varepsilon>0$ 有
$$
\Big|\log \operatorname{Cap}\Big(\big\{\Psi:\ |K_{w,h}\Psi-y|_{\mathcal H_w}\le \varepsilon\big\}/\!\sim_{\rm rev}\Big)
-\log \operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big)\Big|
\ \le\ C_{w,h}\,\varepsilon\ +\ \Delta_{\rm NPE}^{(\le m)}.
$$
其中 $\Delta_{\rm NPE}^{(\le m)}=\Delta_{\rm alias}+\Delta_{\rm Bernoulli}^{(\le m)}+\Delta_{\rm tail}$。该表述与 §8 的 Toeplitz/Berezin 压缩结果保持一致。([维基百科][3])

---

## 4. 与三位一体刻度的一致性

定义窗化读数量
$$
\Phi[w]:=\int \mathrm{ker}(w;E)\,\frac{\varphi'(E)}{\pi}\,dE,\qquad
\Xi[w]:=\int \mathrm{ker}(w;E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE,
$$
以及 $\int \mathrm{ker}(w;E)\,\rho_{\rm rel}(E)\,dE$。由三位一体同一式得 $\Phi[w]=\Xi[w]=\int \mathrm{ker}(w;E)\,\rho_{\rm rel}(E)\,dE$。据此得到：

**定理 4.1（刻度相容与局域稳定）** 若容量归一化与上述刻度一致，则对窗的平滑形变 $\delta w$ 与符号扰动 $\delta a$ 存在常数 $C$ 使
$$
|\delta H_w(y)|\le C\big(|\delta w|_{W^{1,1}}+|\delta a|_{W^{1,1}}\big)+O\!\left(\Delta_{\rm NPE}^{(\le m)}\right).
$$
**证明** Gateaux 变分由窗化迹的一级响应控制；刻度同一将 $\varphi'(E)/\pi$、$\rho_{\rm rel}(E)$ 与 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 统一归一；NPE 有限阶终止给出残差的非渐近上界。([arXiv][1])

---

## 5. 边界=信息资源：传播半径与互信息

RCA 的有限传播半径 $r$ 或连续系统的有限群延迟/微支集传播界，意味着窗外自由度作用经厚度 $r$ 的边界带传入。

**定义 5.0（RCA 端的边界补丁计数 $\operatorname{Comp}$）** 设
$$
\partial_r W:=\{x\in\mathbb Z^d:\ 0<\operatorname{dist}(x,W)\le r\},
$$
其中 $\operatorname{dist}$ 与体积 $\operatorname{vol}$ 依 Notation(8)/(6) 取值。定义
$$
\operatorname{Comp}(y;\partial_r W):=\min\Big\{\#\mathcal B:\ \mathcal B\subset\mathcal S(\partial_r W),\ \forall\,\omega\in\mathcal C(y;W)\ \exists\,b\in\mathcal B\ \text{s.t.}\ \omega|_{\partial_r W}=b\Big\},
$$
其中 $\mathcal S(\partial_r W)$ **仅指 RCA 字母表配置空间**。

**定义 5.1a（边界可分辨性，BD）**
对任意 $\omega,\omega'\in\mathcal C(y;W)$，若 $\omega\not\sim_{\rm rev}\omega'$，则有
$$
\omega|_{\partial_r W}\ \ne\ \omega'|_{\partial_r W}.
$$
换言之，**不同等价类必对应不同的边界补丁**。

**定理 5.1（RCA 端的边界主导上界；统一版）**
**存在常数** $c>0$（仅依赖传播半径 $r$、维度与局部规则/字母表规模）使
$$
\log \operatorname{Comp}(y;\partial_r W)\ \le\ c\cdot \operatorname{vol}(\partial_r W).
$$
**若进一步满足边界可分辨性（定义 5.1a），则**
$$
H_W(y)\ \le\ \log \operatorname{Comp}(y;\partial_r W)\ \le\ c\cdot \operatorname{vol}(\partial_r W).
$$
其中 $\operatorname{vol}$ 依"测度约定(6)"取计数测度。**本定理不涉及 WSIG 端**；连续端的对应上界与尺度控制见 §9 与 §4。

（此统一版与 §10.1 的一维情形一致。）

**定理 5.2（可逆互信息的非负性）** 令
$$
I_{\rm rev}(W_1{:}W_2):=H_{W_1}(y_1)+H_{W_2}(y_2)-H_{W_1\cup W_2}(y)\ \ge 0,
$$
且随边界一致性约束增强单调不减；在边界完全闭合时取极值。
**证明** 由等价类纤维化与匹配数的子模性，结合可逆一致性，得到非负性与单调性。

---

## 6. 复杂度下界与随机稳健性

记 $K(y)$ 为柯尔莫哥洛夫复杂度的可计算上界代理。

**定义（边界长度预算）**：设 $\partial_r W$ 与常数 $c$ 如 **定理 5.1**，定义
$$
\mathrm{bdry}(W):=c\cdot \operatorname{vol}(\partial_r W).
$$

**定义（模型容量）**：沿用 **定理 5.1** 之常数 $c$ 与"测度约定(6)"，定义
$$
\mathrm{ModelCap}(W):=c\cdot \operatorname{vol}(\partial_r W).
$$
则弱依赖与有限传播场景下，有
$$
H_W(y)\ \gtrsim\ \big[\,K(y)-\mathrm{bdry}(W)\,\big]_+,\qquad
H_W(y)\ \lesssim\ \mathrm{ModelCap}(W)=c\cdot \operatorname{vol}(\partial_r W),
$$
其中 $[x]_+:=\max\{x,0\}$，两端常数与 **定理 5.1** 的刻度一致。高度不可压缩的 $y$ 需要更大的解释族，因而提升 $H_W$ 的下界。([维基百科][6])

---

## 7. 与香农/冯诺依曼熵的关系

$H_w$ 度量"结构一致的可逆解释族规模"，而香农/冯诺依曼熵度量分布或密度矩阵不确定性。在独立同分布与窗尺度趋大极限下，单位体密度的 $H_w$ 可与熵率耦合；但在强可逆约束与边界主导的几何场景中二者分离：$H_w$ 对"可逆一致性"和"传播半径"更敏感。

---

## 8. Toeplitz/Berezin 压缩的非渐近界

设 $T_{a,w,h}$ 为符号 $a$ 与窗 $w$ 的 Toeplitz/Berezin 压缩；记容差球 $\mathbb B_\varepsilon(y)$。存在常数 $C_{w,a,h}$ 与有限阶 $m$ 使
$$
\Big|\log \operatorname{Cap}\Big(\big\{\Psi\in\mathcal E_{\rm rev}:\ |T_{a,w,h}\Psi-y|_{\mathcal H_w}\le \varepsilon\big\}/\!\sim_{\rm rev}\Big)
-\log \operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big)\Big|
\le C_{w,a,h}\,\varepsilon+\Delta_{\rm NPE}^{(\le m)}.
$$
其中 $\Delta_{\rm NPE}^{(\le m)}$ 由 Poisson 别名、EM 有限阶边界层和尾项共同控制；若 $a$ 为带限/解析符号、$w$ 指数衰减且满足帧密度条件，则常数由带宽与 Bernoulli 常数统一界定。([users.math.cas.cz][2])

---

## 9. 带限信号的 Nyquist 范例

设一维带限信号，带宽 $B$，采样率 $f_s\ge 2B$，窗 $w$ 为紧支或指数窗，能量壳 $|\Psi|_{\mathcal H}\le E$。

**定理 9.1（Nyquist 条件下的边界主导）**
$$
H_w(y)\ =\ \log \operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big),
$$
$$
\Bigg|\,\log \operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big)
-\log \operatorname{Cap}\big(\text{边界相位/幅度自由度}/\!\sim_{\rm rev}\big)\,\Bigg|
\le \Delta_{\rm NPE}^{(\le m)}.
$$
当窗尺度 $R\to\infty$ 而 $B,E$ 固定时，单位长度 $H_w/R\to 0$。
**证明** 由 Paley–Wiener 空间的 Landau 密度必要条件与 Poisson 求和控制别名误差，EM 有限阶收敛控制边界层；边界主导由有限传播/核衰减与帧稳定性给出。([numdam.org][7])

**注（帧与不确定性）** 窗族取紧框架可优化误差常数；Balian–Low 禁止在临界密度下同时实现优良双局域，提示容量下界不可过度压缩。([维基百科][8])

---

## 10. RCA 范例与定理

考虑一维 RCA，半径 $r$，窗长 $R$。

**定理 10.1（有限半径传播的容量上界）** 若长度 $2r$ 的边界补丁唯一决定外延，则
$$
H_R(y)\ \le\ \log \#\{\text{边界补丁}\}\ \le\ c\cdot r,
$$
且当 $R\to\infty$、$r$ 固定时，单位长度 $H_R/R\to 0$。
**证明** 由马尔可夫型传播限制与边界决定性，横截数受边界补丁数界定。

**定理 10.2（拼接与可逆互信息）** 对相邻窗 $W_1,W_2$ 与公共边界带，
$$
I_{\rm rev}(W_1{:}W_2)\ \text{随边界一致性约束增强而单调不减，并在闭合时极大}.
$$
**证明** 与定理 2.3 同理；RCA 可逆性与 Garden-of-Eden/CHL 结构确保配对的可逆一致性与非负性。([维基百科][5])

---

## 11. 变分与二阶结构

记 $\mathscr F(a,w):=\log\operatorname{Cap}\big(\mathfrak C_w(y)/\!\sim_{\rm rev}\big)$。在符号/窗的正则类（带限/解析/指数窗）内，有
$$
\delta \mathscr F=\langle \mathcal G_a,\delta a\rangle+\langle \mathcal G_w,\delta w\rangle+O\!\left(\Delta_{\rm NPE}^{(\le m)}\right),
$$
其中灵敏度泛函 $\mathcal G_a,\mathcal G_w$ 由窗化迹与三位一体刻度导出；其二阶对称部分建立 $H^{1/2}$-型稳定 Hessian 下界，反映容量函数在可行域上的强凸/凹互补结构（取决于容量模型与归一化）。

---

## 12. 公理化总结

* **A1 可逆一致性**：仅计与观测一致且可逆的补全；
* **A2 同变性**：对保结构可逆变换不变；
* **A3 单调性**：随窗扩张不增；
* **A4 次可加**：拼接时以可逆互信息修正；
* **A5 NPE–EM 非渐近闭合**：一切误差在**有限阶**终止并可显式上界；
* **A6 奇性不增/极点=主尺度**：窗化不引入更强奇性，极点决定主尺度；
* **A7 刻度同一相容**：与 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 严格一致。

---

## 13. 结论性定理

**定理 13.1（良定性与稳健性）** 在上述公理与正则条件下，有限窗口可逆补全熵 $H$（RCA 端为 $H_W$，WSIG 端为 $H_w$）良定、与可逆同构不变、对窗/符号扰动 Lipschitz 稳定，并在 NPE–EM 纪律下获得非渐近上下界与变分估计；其规模受边界带与传播半径主导，体现"边界=信息资源"的定量律；且与三位一体刻度严格相容。
**证明** 由 3.1、3.2、4.1、5.1、5.2 及 NPE–EM 有限阶控制综合得证。([维基百科][3])

**定理 13.2（局域信息律）** 在 RCA 半径有限或连续传播有界的系统中，随窗尺度增大，单位体密度的 $H$（RCA 端 $H_W$，WSIG 端 $H_w$）衰减至零；对带限/指数窗，$H/R$ 的衰减速率由带宽、窗衰减与 EM 阶数的常数集合统一控制。
**证明** 由 5.1 的边界主导上界与 9.1 的 Nyquist 框架、结合 EM 有限阶终止，得单位尺度衰减。

---

## 附录 A：NPE 三分解的显式常数

* **Poisson 别名项**：令频域带宽 $B$ 与采样间隔 $\Delta$ 满足 $1/\Delta\ge 2B$（Nyquist），则别名误差按高频泄露的窗谱衰减估计；Poisson 求和给出离散—连续差的主项。([维基百科][3])
* **EM 边界层**：对 $p\le m$ 阶终止，余项由 periodized Bernoulli 函数 $P_p$ 的 $L^\infty$ 界与 $\zeta(p)$ 常数给出 $\big|R_p\big|\le \tfrac{2\zeta(p)}{(2\pi)^p}\!\int |f^{(p)}|$。([维基百科][9])
* **尾项**：由窗的指数/次指数衰减与能量壳正则性（有限阶导数有界）给出几何级或幂级收敛。

---

## 附录 B：帧密度与不确定性障碍

Gabor/多窗框架下，Wexler–Raz 双正交与 Janssen 表示保证帧稳定与密度判据；Landau 密度定理给出 Paley–Wiener 空间的采样必要密度；Balian–Low 定理提供临界密度下的双局域障碍与定量强化版本，限制容量的进一步压缩。([sites.math.duke.edu][10])

---

## 参考文献（选）

1. Wigner, Smith：群延迟与时间延迟矩阵；Brouwer–Frahm–Beenakker：$\mathsf Q$ 谱的随机矩阵理论分布。([arXiv][1])
2. Birman–Kreĭn 公式与谱移函数综述与推广（Pushnitski；Hanisch 等）。([arXiv][11])
3. Berezin–Toeplitz 量化与局域化算子（Engliš；相关 Toeplitz-局域化文献）。([users.math.cas.cz][2])
4. Poisson 求和、Euler–Maclaurin 公式与 Bernoulli 常数的显式余项估计。([维基百科][3])
5. Garden-of-Eden 定理、Curtis–Hedlund–Lyndon 定理与 RCA 可逆性综述（Kari）。([维基百科][5])
6. Landau 密度必要条件及新近推广；Wexler–Raz、Janssen 与 Gabor 框架的双正交理论；Balian–Low 定理及其定量版本。([numdam.org][7])
7. 柯尔莫哥洛夫复杂度、MDL/MML 与编码定理（Li–Vitányi；Grünwald 教程）。([维基百科][6])

---

[1]: https://arxiv.org/pdf/2005.03211?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics"
[2]: https://users.math.cas.cz/~englis/81.pdf?utm_source=chatgpt.com "An excursion into Berezin-Toeplitz quantization and related ..."
[3]: https://en.wikipedia.org/wiki/Poisson_summation_formula?utm_source=chatgpt.com "Poisson summation formula"
[4]: https://en.wikipedia.org/wiki/Reversible_cellular_automaton?utm_source=chatgpt.com "Reversible cellular automaton"
[5]: https://en.wikipedia.org/wiki/Garden_of_Eden_%28cellular_automaton%29?utm_source=chatgpt.com "Garden of Eden (cellular automaton)"
[6]: https://en.wikipedia.org/wiki/Kolmogorov_complexity?utm_source=chatgpt.com "Kolmogorov complexity"
[7]: https://www.numdam.org/item/10.1016/j.crma.2012.05.003.pdf?utm_source=chatgpt.com "Revisiting Landau's density theorems for Paley–Wiener ..."
[8]: https://en.wikipedia.org/wiki/Balian%E2%80%93Low_theorem?utm_source=chatgpt.com "Balian–Low theorem"
[9]: https://en.wikipedia.org/wiki/Euler%E2%80%93Maclaurin_formula?utm_source=chatgpt.com "Euler–Maclaurin formula"
[10]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[11]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
