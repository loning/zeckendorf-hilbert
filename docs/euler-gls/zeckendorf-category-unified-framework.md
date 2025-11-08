# GLS—因果流形—EBOC—RCA 统一中的 Zeckendorf 范畴：反射结构、强张量性质、窗化散射信息的函子化桥接及其到几何变分—爱因斯坦场方程的闭合推导

Version: 1.8

## 摘要

在以广义光结构刻画因果几何、以 EBOC 表达观察—计算的全局幺正与可逆性的统一语境下，构造 Zeckendorf 结构的范畴化体系 $\mathbf{Zec}$，在对象级定义归一化投影 $N$，并以"值加法后归一化"的张量给出对象级结合/交换与张量相容。由可逆局域"进/借位"规则与 Curtis–Hedlund–Lyndon 型定理建立与 RCA 的桥接；在 Nyquist—Poisson—有限阶 EM 纪律下定义 $\mathbf{WScat}\xrightarrow{\ \mathsf M\ }\mathbf{Fib}\xrightarrow{\ N\ }\mathbf{Zec}$ 的量化—归一化链 $L=N\circ\mathsf M$，给出非渐近误差闭合与"奇性不增"。几何侧以"双时间分离原理"保证因果偏序仅由因果前沿时间 $t_*$ 决定，而 Zeckendorf 日志仅定位于操作化刻度 $T_\gamma$ 侧。最后在统一公理背景下，以窗化相对熵—几何作用的变分严格导出含宇宙学常数的爱因斯坦场方程的极值条件。

**MSC**：83C05；81U15；37B15；37N20；42A38；94A17。
**关键词**：GLS；EBOC；RCA；Zeckendorf 分解；归一化投影；张量相容；窗化群延迟；有限阶 Euler–Maclaurin；Poisson 连接；双时间分离；信息几何变分；爱因斯坦—希尔伯特作用。

---

## Notation & Axioms / Conventions

1. **散射母尺与幺正性**。能变量 $E\in\mathbb R$。幺正散射矩阵 $S(E)\in\mathsf U(N)$ 可微。Wigner–Smith 群延迟 $\mathsf Q(E)=-\,i\,S(E)^\dagger \frac{dS}{dE}(E)$。总相位 $\varphi(E)=\tfrac12\arg\det S(E)$。相对态密度 $\rho_{\rm rel}(E)$。核心母刻度同一
   $$
   \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E).
   $$
2. **窗化压缩与读数**。取平滑快速衰减窗核 $w_R$ 与分析核 $h$，记 $\check h(E)=h(-E)$、卷积 $(h*f)(E)=\int h(E-\xi)f(\xi)\,d\xi$。Toeplitz/Berezin 压缩乘子 $K_{w,h}[f](E)=(w_R*\check h)(E)f(E)$。沿观测路径 $\gamma$ 的窗化群延迟读数
   $$
   T_\gamma[w_R,h]=\int (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)\,dE.
   $$
3. **双时间分离**。因果前沿时间 $t_*(\gamma)$ 决定偏序与无信号；$T_\gamma[w_R,h]$ 为操作化刻度。二者无普适大小比较，允许 $T_\gamma<0$。
4. **NPE 纪律**。在带限与 Nyquist 条件下，仅使用有限阶 EM 与 Poisson 求和进行误差预算；坚持"奇性不增"，即归一化与量化操作不引入主尺度之外的新极点或本征奇性。
5. **Fibonacci 与 Zeckendorf**。设 $F_1=1, F_2=1, F_{k+1}=F_k+F_{k-1}$。Zeckendorf 展开采用 $k\ge 2$ 计位，合法码字 $\mathbf b=(b_2,b_3,\dots)$ 满足 $b_k\in\{0,1\}$ 且 $b_kb_{k+1}=0$。

---

## 1. 数字流、正规形与能函数终止性

**定义 1.1（数字流与估值）**。给定有限窗口 $I=[a,b]\subset\mathbb Z$，定义数字流空间
$$
X_{\rm Fib}^I=\{\mathbf a=(a_k)_{k\in I}: a_k\in\mathbb N,\ \text{仅有限个非零}\},
$$
估值 $V_I(\mathbf a)=\sum_{k\in I}a_kF_k$。

**定义 1.2（黄金均值子移位与正规形）**。黄金均值子移位
$$
X_{\rm GM}^I=\{\mathbf b\in\{0,1\}^I: b_kb_{k+1}=0\}.
$$
给定 $n\in\mathbb N$，称 $\mathbf b\in X_{\rm GM}^I$ 为 $n$ 的**正规形**，若 $V_I(\mathbf b)=n$；对每个 $n$，该 $\mathbf b$ 在值等价类 $\{\mathbf a\in X_{\rm Fib}^I:V_I(\mathbf a)=n\}$ 中唯一，等价于 Zeckendorf 唯一展开。

**定理 1.3（Zeckendorf 存在与唯一）**。任意 $n\in\mathbb N$ 存在唯一 $\mathbf b\in X_{\rm GM}^{[2,K]}$ 使 $n=\sum_{k=2}^K b_kF_k$ 且 $b_kb_{k+1}=0$。
**证明**。存在性：贪婪选 $k^*$ 使 $F_{k^*}\le n<F_{k^*+1}$，置 $b_{k^*}=1$，余量 $n_1=n-F_{k^*}$。由
$$
\sum_{j<k^*}F_j=F_{k^*+1}-1
$$
得 $n_1<F_{k^*-1}$，故强制 $b_{k^*-1}=0$。递归至零。唯一性同原。证毕。

**定义 1.4（重写关系与正规形）**。在 $X_{\rm Fib}^I$ 上生成重写关系 $\Rightarrow$，其基本步为
$$
F_{k+1}\leftrightarrow F_k+F_{k-1},
$$
以及相应的进/借位。称 $\mathbf b\in X_{\rm Fib}^I$ **不可约**（或为**正规形**），若 $\mathbf b\in X_{\rm GM}^I$（即 $b_k b_{k+1}=0$）且对 $\Rightarrow$ 不再可化。关于任意 $\mathbf a$ 的正规形**存在且唯一**、并与 $V_I$ 的 Zeckendorf 唯一展开一致，见定理 1.5 与附录 B。

**定义（正规度与势函数）**。对 $\mathbf a=(a_k)_{k\in I}$，置
$$
\mathrm{Reg}(\mathbf a)=\sum_{k\in I}\mathbf 1\{a_k>0\ \&\ a_{k+1}>0\},\qquad
\Phi(\mathbf a)=\sum_{k\in I}a_k\alpha^k\ \ (\alpha>2).
$$

**定理 1.5（终止与唯一极限）**。按文中"归约循环"（一次最高可行位拆分 $F_{k+1}\to F_k+F_{k-1}$ 加随后全部强制合并至 $\mathrm{Reg}=0$）执行，每一轮有
$$
\Delta_{\mathrm{split}}=\alpha^{k+1}-(\alpha^{k}+\alpha^{k-1})=\alpha^{k-1}(\alpha^2-\alpha-1),
$$
$$
\Delta_{\mathrm{merge}}\le \frac{\alpha^{k-1}(\alpha^2-\alpha-1)}{\alpha-1},
\qquad\Rightarrow\qquad
\Delta_{\mathrm{cycle}}=\Delta_{\mathrm{merge}}-\Delta_{\mathrm{split}}<0\ \ (\alpha>2),
$$
故 $\Phi$ 按轮严格下降，归一化在有限轮终止；极限唯一由 Zeckendorf 唯一性给出。

---

## 2. 范畴 $\mathbf{Fib}$、$\mathbf{Zec}$ 与反射结构

**定义 2.1（范畴 $\mathbf{Fib}$）**。对象为各 $X_{\rm Fib}^I$。态射为值保持的滑块编码 $f:X_{\rm Fib}^I\to X_{\rm Fib}^J$，具有限半径局域性且 $V_J(f(\mathbf a))=V_I(\mathbf a)$。本文称"滑块编码"为（当 $I=\mathbb Z$ 时）**与移位算子 $\sigma$ 交换**的有限半径局域映射。

**例 2.2（半径一进/借位算子）**。若 $a_{k+1}\ge 1$，可设
$$
a_{k+1}\mapsto a_{k+1}-1,\ a_k\mapsto a_k+1,\ a_{k-1}\mapsto a_{k-1}+1;
$$
逆操作对称。该滑块编码保持 $V$。

**定义 2.3（范畴 $\mathbf{Zec}$ 与包含）**。对象为 $X_{\rm GM}^I\subset X_{\rm Fib}^I$，态射取自 $\mathbf{Fib}$ 中将正规形映为正规形且值保持的滑块编码。包含函子 $I:\mathbf{Zec}\hookrightarrow\mathbf{Fib}$。

**定理 2.4（归一化的对象级投影族）**。在对象上定义 $N_I:X_{\rm Fib}^I\to X_{\rm GM}^I$ 为逐点归一化。记对象级指派
$$
\eta_X:\ X\ \mapsto\ I(NX)
$$
表示"先归一化、再包含"的对象级对应；$\eta$ 不是自然变换。并且 $N\circ I=\mathrm{Id}_{\mathbf{Zec}}$（对象级）。

**命题 2.5（对象级幂等）**。对任意窗口 $I$，$N_I$ 幂等且对 $\mathbf b\in X_{\rm GM}^I$ 有 $N_I(\mathbf b)=\mathbf b$。

---

## 3. 张量结构与对象级张量相容

**定义 3.1（$\mathbf{Fib}$ 的点和张量）**。对同窗口 $I$，定义 $\oplus:X_{\rm Fib}^I\times X_{\rm Fib}^I\to X_{\rm Fib}^I$ 为分量相加 $(\mathbf a\oplus\mathbf c)_k=a_k+c_k$。则 $V_I(\mathbf a\oplus\mathbf c)=V_I(\mathbf a)+V_I(\mathbf c)$。按窗口直和推广为范畴层的对称单体结构。

**边界假设／扩窗规则**：对固定窗口 $I=[2,K_{\max}]$，若 $V_I(\mathbf b)+V_I(\mathbf c)\ge F_{K_{\max}+1}$，则采用**动态扩窗**到最小 $I'=[2,K']$（使 $F_{K'}>V_I(\mathbf b)+V_I(\mathbf c)$），再在 $I'$ 上定义 $\oplus,\ N,\ \otimes$。在此约定下，以下结论均以 $I$ 代表当前工作窗口。

**定义 3.2（$\mathbf{Zec}$ 的归一化张量）**。对 $\mathbf b,\mathbf c\in X_{\rm GM}^I$，置
$$
\mathbf b\otimes\mathbf c:=N_I(\mathbf b\oplus\mathbf c).
$$
则 $V_I(\mathbf b\otimes\mathbf c)=V_I(\mathbf b)+V_I(\mathbf c)$。

**定理 3.3（结合与交换）**。在上述边界假设／扩窗规则下，对任意 $\mathbf b,\mathbf c,\mathbf d\in X_{\rm GM}^I$，有
$$
(\mathbf b\otimes\mathbf c)\otimes\mathbf d=\mathbf b\otimes(\mathbf c\otimes\mathbf d),\qquad \mathbf b\otimes\mathbf c=\mathbf c\otimes\mathbf b,
$$
幺元为全零码字。
**证明**。三者估值均为 $V_I(\mathbf b)+V_I(\mathbf c)+V_I(\mathbf d)$。正规形唯一性使对应码字相同。交换性同理。证毕。

**定理 3.4（对象级强张量相容）**。对任意对象 $X,Y$，存在**对象级的典范同构**
$$
N(X\oplus Y)\ \cong\ NX\otimes NY,
$$
其中 $\otimes$ 由"值加法后归一化"定义。该同构仅指对象级的识别，**不主张自然性**，亦不涉及态射层的函子性。

**证明**。由估值 $V$ 的可加性与正规形唯一性，对于任意 $\mathbf b\in NX$、$\mathbf c\in NY$，有
$$
N(\mathbf b\oplus\mathbf c)=\mathbf b\otimes\mathbf c.
$$
因而在**对象级**可逐码字将 $N(X\oplus Y)$ 与 $NX\otimes NY$ 进行一一对应识别。该识别不依赖于态射结构，故不主张其为自然同构。证毕。

---

## 4. 与可逆元胞自动机（RCA）的桥接

**定义 4.1（守恒型 RCA 规则）**。在格点 $I=\mathbb Z$ 上，令**与移位 $\sigma$ 交换**的有限半径可逆局域规则 $U$ 作用于 $X_{\rm Fib}^{\mathbb Z}$。若对一切配置 $\mathbf a$ 有 $V_I(U\mathbf a)=V_I(\mathbf a)$，称 $U$ 值守恒。

**定理 4.2（双射与无 Garden-of-Eden）**。若 $U$ 可逆且局域，则 $U:X_{\rm Fib}^I\to X_{\rm Fib}^I$ 为双射且无无前像配置；若进一步值守恒，则 $V_I$ 为一阶守恒量。
**证明**。可逆局域性蕴含 Curtis–Hedlund–Lyndon 型表征，给出双射与无 Garden-of-Eden。值守恒为定义直接结论。证毕。

**命题 4.3（到 $\mathbf{Zec}$ 的对象级压缩）**。定义 $\widehat U:=N\circ U|_{X_{\rm GM}^I}$。则 $\widehat U:X_{\rm GM}^I\to X_{\rm GM}^I$ 为对象级映射且保持 $V_I$；一般情形下 $\widehat U$ **不**必为滑块编码，故不视为 $\mathbf{Zec}$ 的态射。
**证明**。$U$ 不改 $V_I$，$N$ 仅作局域正规化且不改估值，故像仍为正规形并值保持。但 $N$ 一般不是滑块编码，复合 $\widehat U$ 亦未必与移位交换。证毕。

---

## 5. 从窗化散射到 $\mathbf{Fib}\to\mathbf{Zec}$ 的函子化

**定义 5.1（窗化载荷与量化）**。对能区 $W$，窗化载荷
$$
S(W)=\int \chi_W(E)\,(w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE\in\mathbb R.
$$
取量纲 $\epsilon>0$，量化算子
$$
\boxed{\ \kappa(S)=\Bigl\lfloor \frac{(S)_+}{\epsilon}\Bigr\rceil\in\mathbb N,\qquad (S)_+=\max\{S,0\}\ }.
$$

**定义 5.2（分辨—Fibonacci 配码）**。选定 $K_{\max}$ 与 $I=[2,K_{\max}]$。定义 $\mathsf M:\mathbf{WScat}\to\mathbf{Fib}$ 为
$$
\mathsf M(W)=\mathbf a^{(m)},\qquad m=\kappa(S(W)),
$$
其中 $\mathbf a^{(m)}$ 在 $I$ 上唯一取 $a_2=m$、其余 $a_k=0$，从而 $V_I(\mathsf M(W))=m$。取 $K_{\max}$ 使 $F_{K_{\max}}>\kappa(S(W))$ 对所有考虑的 $W$ 成立；若不成立，则先动态扩窗至 $I'=[2,K']$ 后再施行 $L=N\circ\mathsf M$。再置 $L:=N\circ \mathsf M:\mathbf{WScat}\to\mathbf{Zec}$。

**定理 5.3（张量一致—与量化一致的版本）**。设 $W_1,W_2$ 不重叠或满足 Nyquist 条件的等效并窗，且 **$S(W_1)\ge0,\ S(W_2)\ge0$**。令
$$
\boxed{\ \delta:=\kappa\bigl(S(W_1\sqcup W_2)\bigr)-\kappa\bigl(S(W_1)\bigr)-\kappa\bigl(S(W_2)\bigr)\in\{-1,0,1\}\ }.
$$
则
$$
L(W_1\sqcup W_2)=L(W_1)\otimes L(W_2)\quad\Longleftrightarrow\quad \delta=0,
$$
且一般地
$$
V_I\bigl(L(W_1\sqcup W_2)\bigr)=V_I\bigl(L(W_1)\bigr)+V_I\bigl(L(W_2)\bigr)+\delta.
$$
**证明（要点）**。在 $S(W_i)\ge0$ 下，$\kappa$ 与最近整数一致（无阈值截断），故 $\delta$ 由舍入误差差分给出并落在 $\{-1,0,1\}$；张量一致当且仅当舍入误差可加，等价于 $\delta=0$。证毕。

**定理 5.4（非渐近误差闭合与奇性不增）**。取步长 $h\asymp L^{-1}$，则
$$
\bigl|(S(W))_+-\epsilon\,V_I(\mathsf M(W))\bigr|\ \le\ C_mL^{-m}+\epsilon\,c(K_{\max}),
$$
从 $\mathsf M$ 至 $L$ 的正规化不引入新奇性。

**证明**。有限阶 Euler–Maclaurin 给出积分—求和偏差 $O(L^{-m})$，Poisson 求和在 Nyquist 条件下抑制别名。最近整数量化满足
$$
\bigl|(S(W))_+-\epsilon\,\kappa(S(W))\bigr|<\tfrac{\epsilon}{2},
$$
且 $V_I(\mathsf M(W))=\kappa(S(W))$，合并即得所述上界；正规化仅施行 $F_{k+1}=F_k+F_{k-1}$ 的局域替换，不引入新奇性。证毕。

---

## 6. 双时间分离与因果一致性

**定理 6.1（位阶分离）**。$t_*$ 决定因果偏序与无信号；$\mathsf M$ 与 $L$ 仅依赖能域窗化读数与量化，不改变 $t_*$。
**证明**。$\mathsf M$、$L$ 皆为对谱测度的函数—量化后处理，属 $T_\gamma$ 侧的操作化刻度；GLS 的类光锥几何与最早到达 $t_*$ 由传播方程与支撑锥决定，与后处理独立。证毕。

---

## 7. 信息几何变分与爱因斯坦方程

**定义 7.1（窗化相对熵—几何作用）**。设参考参数 $\theta_0$，谱密度 $d\mu_\theta(E)=\rho_{\rm rel}(E;\theta)\,dE$。定义
$$
\mathcal I[w_R,h;\theta\mid\theta_0]=\int (w_R*\check h)(E)\,\rho_{\rm rel}(E;\theta)\,\log\frac{\rho_{\rm rel}(E;\theta)}{\rho_{\rm rel}(E;\theta_0)}\,dE.
$$
总作用
$$
\mathscr S[w_R,h;g,\psi]=\alpha\int_{\mathcal M}R(g)\sqrt{|g|}\,d^4x+\beta\,\mathcal I[w_R,h;\theta(g,\psi)\mid\theta_0]+\int_{\mathcal M}\mathcal L_{\rm m}(g,\psi)\sqrt{|g|}\,d^4x.
$$

**引理 7.2（一阶变分）**。在交换变分与积分的常规条件下，
$$
\delta\mathcal I=\int (w_R*\check h)(E)\,\Bigl[1+\log\frac{\rho_{\rm rel}(E;\theta)}{\rho_{\rm rel}(E;\theta_0)}\Bigr]\,(\partial_i\log\rho_{\rm rel})(E;\theta)\,\delta\theta^i\,d\mu_\theta(E).
$$
**证明**。将 $\mathcal I$ 写作 $\int (w_R*\check h)\,\rho_{\rm rel}\,\log\frac{\rho_{\rm rel}}{\rho_{\rm rel}(\cdot;\theta_0)}\,dE$，对 $\rho_{\rm rel}$ 的变分得 Fréchet 导数 $(w_R*\check h)\bigl(1+\log\frac{\rho_{\rm rel}}{\rho_0}\bigr)$，链式法则引入 $(\partial_i\log\rho_{\rm rel})\,\delta\theta^i$。测度变化与被积变化合并为所述表达式。证毕。

**命题 7.3（场方程原型）**。对度规变分得到
$$
\alpha\,G_{\mu\nu}+\frac{\beta}{2}\,H_{\mu\nu}[w_R,h;\theta]=\frac{1}{2}\,T_{\mu\nu},
$$
其中
$$
H_{\mu\nu}=\frac{2}{\sqrt{|g|}}\frac{\delta}{\delta g^{\mu\nu}}\mathcal I[w_R,h;\theta(g,\psi)\mid\theta_0].
$$
**证明**。爱因斯坦—希尔伯特项的变分给出 $\alpha G_{\mu\nu}$，物质项给出 $\tfrac{1}{2}T_{\mu\nu}$。相对熵项对 $g$ 的依赖来自 $\theta(g,\psi)$ 与测度 $d\mu_\theta$，按引理 7.2 与链式法则得到 $H_{\mu\nu}$。证毕。

**定理 7.4（极小耦合极限与宇宙学常数）**。若存在窗族与 NPE 规模使
$$
\lim_{\mathrm{NPE}}H_{\mu\nu}[w_R,h;\theta]=0,
$$
则极值方程还原为 $\alpha\,G_{\mu\nu}=\tfrac12 T_{\mu\nu}$。若 $\mathcal I$ 具有常量偏移 $\Delta\mathcal I=\Lambda\int \sqrt{|g|}\,d^4x$，则得到 $\alpha\,G_{\mu\nu}+\Lambda g_{\mu\nu}=\tfrac12 T_{\mu\nu}$。
**证明**。由第 5 节的非渐近闭合，选取带限并满足 Nyquist 条件的窗组使 EM 余项与别名误差同时受控并趋零，从而 $H_{\mu\nu}\to 0$。若 $\mathcal I$ 的参数平移只引入体积项常量，吸收为 $\Lambda$。证毕。

---

## 8. 与 GLS—因果流形的互构与交换图

**定义 8.1（范畴族）**。$\mathbf{WScat}$：对象 $(\mathcal H,S,\rho_{\rm rel},K_{w,h})$，态射为保持母尺与窗化读数的 CPTP 映射。$\mathbf{Cau}$：对象 $(\mathcal M,g)$，态射为保因果锥的映射。$\mathbf{RCA}$：对象为可逆局域更新系统。$\mathbf{EBOC}$：对象为全局幺正的散射三元。

**定义 8.2（互构函子）**。$\mathfrak F:\mathbf{WScat}\to\mathbf{Cau}$ 由几何散射与李乌维尔推送构造；$\mathfrak G:\mathbf{Cau}\to\mathbf{WScat}$ 由类光测地流的 Poincaré 返流—散射相位构造。存在自然变换 $\eta:\mathfrak G\circ\mathfrak F\simeq\mathrm{Id}_{\mathbf{WScat}}$、$\epsilon:\mathfrak F\circ\mathfrak G\simeq\mathrm{Id}_{\mathbf{Cau}}$。

**定理 8.3（与 $\mathbf{Zec}$ 的对象级交换图）**。存在对象级交换图
$$
\mathbf{RCA}\xrightarrow{\ \mathfrak S\ }\mathbf{Fib}\xrightarrow{\ N\ }\mathbf{Zec}\xleftarrow{\ L=N\circ\mathsf M\ }\mathbf{WScat}\ \underset{\mathfrak G}{\overset{\mathfrak F}{\rightleftarrows}}\ \mathbf{Cau},
$$
其中 $\mathfrak S$ 将可逆更新规则表为值守恒滑块编码。
**证明**。第 4 节赋予 $\mathfrak S$ 的存在性与值守恒，**第 5 节赋予 $L$ 的有条件张量一致（当且仅当 $\delta=0$）**。第 6 节的双时间分离确保因果层与量化—归一化层的独立性。按块验证**对象级**交换性成立。证毕。

---

## 9. 范畴结构与后果

**命题 9.1（有限极限与等化子片段）**。在固定窗口族上，$\mathbf{Fib}$ 保留有限积与等化子；$\mathbf{Zec}$ 在对象级作为子空间按包含继承相应结果（此处不援引反射性）。
**证明**。数字流为有限维非负整向量的子集，乘积与等化子逐分量定义且与值保持态射相容；$\mathbf{Zec}$ 的对象级继承由包含关系直接给出。证毕。

**命题 9.2（单体闭合的否定结果）**。在上述张量下，$\mathbf{Zec}$ 一般不单体闭合。
**证明**。若内部 Hom 存在，则 $\mathrm{Hom}_{\mathbf{Zec}}(\cdot,\cdot)$ 应由值加法与正规化生成的态射族稠密逼近任意"评估态射"。但正规形唯一与局域性共同限制了可实现映射的谱，致使柯里化公设与评估—余评估的同构失败。可于有限窗口上构造反例：对两非等值对象，任何非平凡映射均破坏相邻禁止或估值守恒。证毕。

---

## 10. 算法与复杂度

**定理 10.1（贪婪编码复杂度）**。对 $n\in\mathbb N$，Zeckendorf 编码在 $O(\log_\phi n)$ 步内完成。
**证明**。最高位索引 $k_{\max}\sim\log_\phi n$。每步选择最大 $F_k$ 至少覆盖一位，步数与 $k_{\max}$ 同阶。证毕。

**定理 10.2（窗口平移的归一化传播界）**。若净变化 $\Delta S$ 对应的 Fibonacci 展开最高位指数为 $k^*$，则一次窗口平移引起的归一化传播半径 $O(k^*)=O(\log(|\Delta S|+1))$。
**证明**。归一化影响至多传播至覆盖 $|\Delta S|$ 所需的最高位。证毕。

---

## 附录 A：有限阶 Euler–Maclaurin 与 Poisson 的统一

设区段 $[a,b]$、步长 $h$。有限阶 EM 展开
$$
\int_a^b f(x)\,dx=h\sum_{j=0}^{N}f(x_j)+\sum_{r=1}^{m}\frac{B_{2r}}{(2r)!}h^{2r}\bigl(f^{(2r-1)}(b)-f^{(2r-1)}(a)\bigr)+R_{2m},
$$
$$
|R_{2m}|\le C_m h^{2m}.
$$
在带限与 Nyquist 条件下，Poisson 求和抑制非零谐波别名。EM 与 Poisson 共同构成 NPE 的非渐近误差预算；归一化仅由 $F_{k+1}=F_k+F_{k-1}$ 的局域重写实现，奇性不增。

---

## 附录 B：归一化重写系统的终止与合流（修订）

允许规则与主文相同，并采用主文"定向规则"。取势函数 $\Phi$（$\alpha>2$）。

**终止性**。取 $\alpha>2$。按主文定义的归约循环计量势函数变化：在拆分位 $k+1$ 有
$$
\Delta_{\mathrm{split}}=\alpha^{k-1}(\alpha^2-\alpha-1),
$$
合并阶段满足
$$
\Delta_{\mathrm{merge}}\le \alpha^{k-1}(\alpha^2-\alpha-1)/(\alpha-1),
$$
故每轮 $\Delta_{\mathrm{cycle}}<0$，终止性成立。

**合流性**：对所有局域临界对用 Knuth–Bendix 检查其后继经有限步归一化后合一；结合终止性得全局合流，因而正规形唯一并与定理 1.3 的 Zeckendorf 唯一展开一致。证毕。

---

## 附录 C：RCA 的范畴化表述与守恒

RCA 对象记为 $(X,\sigma,U)$，其中 $X$ 为配置空间，$\sigma$ 为移位，$U$ 为有限半径可逆局域更新。Curtis–Hedlund–Lyndon 表征给出 $U$ 与滑块编码的等价。值守恒 $V_I(U\mathbf a)=V_I(\mathbf a)$ 使 $V_I$ 成为一阶守恒量并诱导 $\mathfrak S:\mathbf{RCA}\to\mathbf{Fib}$。压缩 $N$ 将 $\mathfrak S$ 的像落于 $\mathbf{Zec}$。

---

## 附录 D：窗化相对熵变分与 $H_{\mu\nu}$ 的构型

写
$$
\mathcal I=\int \omega(E;\theta)\,\rho_{\rm rel}(E;\theta)\,\log\frac{\rho_{\rm rel}(E;\theta)}{\rho_{\rm rel}(E;\theta_0)}\,dE,
$$
其中 $\omega=w_R*\check h$。对 $\theta$ 的变分
$$
\delta\mathcal I=\int \omega\,\delta\rho_{\rm rel}\,\Bigl[1+\log\frac{\rho_{\rm rel}}{\rho_0}\Bigr]\,dE.
$$
再由 $\delta\rho_{\rm rel}=(\partial_i\rho_{\rm rel})\,\delta\theta^i$ 得引理 7.2。度规变分经 $\theta=\theta(g,\psi)$ 与光学长度标度进入，链式得到
$$
H_{\mu\nu}=2\int \omega(E;\theta)\,\left[\Bigl(1+\log\frac{\rho_{\rm rel}}{\rho_0}\Bigr)\,(\partial_i\log\rho_{\rm rel})(E;\theta)\,\frac{\delta\theta^i}{\delta g^{\mu\nu}}+\frac{1}{2}\Bigl(1+\log\frac{\rho_{\rm rel}}{\rho_0}\Bigr)\,\frac{\delta\log\sqrt{|g|}}{\delta g^{\mu\nu}}\right]\,d\mu_\theta(E).
$$
在满足 NPE 纪律且 $\theta$ 的几何依赖为慢变—带限时，$H_{\mu\nu}$ 的窗平均可被任意压小。

---

## 附录 E：宇宙学常数的由来

若参考选择使 $\log\frac{\rho_{\rm rel}(E;\theta)}{\rho_{\rm rel}(E;\theta_0)}=\mathrm{const}$ 于工作频带上，则
$$
\mathcal I=\Lambda\int \omega(E)\,d\mu_\theta(E)=\Lambda\int_{\mathcal M}\sqrt{|g|}\,d^4x,
$$
常量 $\Lambda$ 只与标定有关，故在场方程中表现为宇宙学常数项。

---

## 附录 F：双时间分离原理的技术阐释

$t_*$ 由传播方程的最早非零响应定义，取决于支撑锥与几何。$T_\gamma$ 为窗化的积分读数，系对谱测度的线性泛函，不改变传播支撑。对任意两条时样路径 $\gamma_1,\gamma_2$，若 $t_*(\gamma_1)<t_*(\gamma_2)$，则无论 $\omega=w_R*\check h$ 如何选取，保持 $t_*$ 的偏序。故 Zeckendorf 日志仅改变操作化刻度而不改变微因果。

---

## 附录 G：误差闭合与"奇性不增"的细化

设被积函数具有有限个主尺度极点或尖点，其余为带限平滑部分。EM 尾项按 $O(h^{2m})$ 估计，Poisson 非零谐波按带限与 Nyquist 约束衰减。量化 $\kappa$ 的最近整数误差 $<\tfrac12$，在位权 $F_k$ 的指数增长下可被更高位吸收而不引入新奇点。归一化仅施行 $F_{k+1}=F_k+F_{k-1}$ 的代数恒等替换，故不生成谱侧的新奇性，保持"极点=主尺度"。

---

## 参考文献（选）

Zeckendorf A., *Représentation des nombres naturels par une somme de nombres de Fibonacci sans répétition*, Bulletin de la Société Royale des Sciences de Liège (1962)。
Lekkerkerker C. G., *Representation of natural numbers as a sum of Fibonacci numbers*, Simon Stevin (1952)。
Hedlund G. A., *Endomorphisms and automorphisms of the shift dynamical system*, Math. Systems Theory (1969)。
Moore E. F., *Machine models of self-reproduction*（Garden-of-Eden 思想源流）；Myhill J., *Garden of Eden Theorems*, Proc. AMS (1963)。
Wigner E. P., Smith F. T., 群延迟经典文献。
Birman M. Š., Kreĭn M. G., *On the theory of wave operators and scattering matrices*, Sov. Math. Dokl. (1962)。
Euler—Maclaurin 与 Poisson 求和的经典教科书陈述（Hardy；Titchmarsh）。
Umegaki H., *Conditional expectation in an operator algebra*；Petz D., *Sufficient subalgebras and relative entropy*，关于相对熵与信息几何。
Einstein A., Hilbert D., 经典场方程与作用原理之原始论文与标准教材阐释。
