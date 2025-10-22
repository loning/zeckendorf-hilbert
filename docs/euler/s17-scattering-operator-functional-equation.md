# S17. 散射算子与完成功能方程的算子化等价

—— 由规范系统与镜像对合导出的酉/对称结构

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在带权 Mellin–Hilbert 空间的镜像结构、Weyl–Heisenberg 酉表示与 de Branges–Krein 规范系统的统一框架下，完成功能方程

$$
\Xi(a-s)=\varepsilon\,\Xi(s)\qquad(|\varepsilon|=1)
$$

被等价刻画为二端口散射矩阵在实频上的**酉性/对称性**与**通道特征值恒等**。以一阶辛型规范系统

$$
\mathbf J\,Y'(t)=z\,H(t)\,Y(t),\qquad
\mathbf J=\begin{pmatrix}0&-1\\[1pt]1&0\end{pmatrix},\quad H(t)=H(t)^{\top}\succeq0
$$

刻画通量并构造传递矩阵 $M(t,z)$；在实轴上按 Kreĭn 符号将边界分解为入/出子空间，得到二端口散射矩阵 $S(z)\in\mathrm U(2)$。对由完成函数 $E(z):=\Xi(\tfrac a2+iz)$ 生成的一维评估通道，完成功能方程与"该通道的散射特征值在实轴上恒等于根数 $\varepsilon$"互为等价。相位以 de Branges 的**内函数**

$$
U(z):=\frac{E^\sharp(z)}{E(z)},\qquad E^\sharp(z):=\overline{E(\bar z)}
$$

定义（HB/有界型情形），Herglotz–Nevanlinna 理论给出相位导数与 Weyl–Titchmarsh 函数虚部的等价。窗化与离散在**有限阶** Euler–Maclaurin 与 **Nyquist–Poisson–EM** 三分解的纪律下不改变奇性集合且不升阶，从而保持"**极点 = 主尺度**"。

---

## 0. 设定与基本判据

### 0.1 完成函数、镜像与现实性

取

$$
\Xi(s)=Q^{s/2}\,r(s)\,L(s),\qquad r(a-s)=r(s),\qquad \Xi(a-s)=\varepsilon\,\Xi(s),\quad |\varepsilon|=1.
$$

定义

$$
E(z):=\Xi\left(\tfrac a2+iz\right),\qquad E^\sharp(z):=\overline{E(\bar z)}.
$$

若进一步满足**现实性**（Schwarz 反射）

$$
\Xi(\overline s)=\overline{\Xi(s)},
$$

则 $E^\sharp(z)=E(-z)$；在未假定现实性时仅使用 $E^\sharp$ 记号。必要时作**根数规范化**：若 $\varepsilon=e^{i\theta}$ 且**假定同时满足功能方程与现实性**（从而 $E^\sharp(z)=E(-z)$ 与 $E(-z)=\varepsilon E(z)$），取 $\widetilde E(z):=e^{i\theta/2}E(z)$ 则有

$$
\frac{\widetilde E^\sharp(z)}{\widetilde E(z)}\equiv1,
\qquad\text{且}\qquad
\widetilde E^\sharp(z)=e^{-i\theta}\widetilde E(-z).
$$

若只假定现实性而**不**假定功能方程，则一般仅有 $\widetilde E^\sharp(z)=e^{-i\theta}\widetilde E(-z)$，并**不能**保证 $\widetilde E^\sharp/\widetilde E\equiv1$。**如需保留原根数**则不作此规范化。

### 0.2 规范系统、传递矩阵与通量

令 $H:[0,T)\to\mathbb R^{2\times2}$ 局部可积、对称非负，研究

$$
\mathbf J\,Y'(t)=z\,H(t)\,Y(t),\qquad Y(0,z)=I.
$$

其传递矩阵 $M(t,z)$ 满足对任意 $z\in\mathbb C$ 的积分恒等式

$$
\boxed{\ M(t,\bar z)^\ast\mathbf J M(t,z)
=\mathbf J+(z-\bar z)\int_0^t M(s,\bar z)^\ast H(s)M(s,z)\,ds\ }.
$$

因此**仅当 $z\in\mathbb R$** 时 $M(t,z)^\ast\mathbf J M(t,z)=\mathbf J$（$\mathbf J$-等距/幺正）。又因 $\operatorname{tr}(\mathbf J^{-1}H)=0$，有

$$
\det M(t,z)\equiv1\qquad(z\in\mathbb C).
$$

设通量型 $[u,v]_{\mathbf J}:=u^\ast(i\mathbf J)v$。当 $z\in\mathbb R$ 时，对任意两解 $Y_1(t;z),Y_2(t;z)$，通量 $[Y_1(t;z),Y_2(t;z)]_{\mathbf J}$ 与 $t$ 无关。

---

## 1. 二端口散射构造（实频）

取

$$
e_+:=\tfrac1{\sqrt2}\binom{1}{\,i},\qquad e_-:=\tfrac1{\sqrt2}\binom{1}{-i},\qquad (i\mathbf J)e_\pm=\pm e_\pm.
$$

对**实** $z$，任意解在端点 $0,T$ 的边界振幅分解为

$$
Y(0;z)=a_0^-e_-+a_0^+e_+,\qquad
Y(T;z)=a_T^-e_-+a_T^+e_+.
$$

在基 $\{e_-,e_+\}$ 下的传递矩阵 $R(M)=\begin{pmatrix}\alpha&\beta\\ \gamma&\delta\end{pmatrix}$ 满足

$$
R(M)^\ast\,\Sigma\,R(M)=\Sigma,\qquad \Sigma=\mathrm{diag}(-1,1),
$$

即 $R(M)\in\mathrm U(1,1)$。

在 $\delta$ 可逆的点，定义二端口散射矩阵

$$
\binom{a_0^+}{a_T^-}=S_T(z)\binom{a_0^-}{a_T^+},\qquad
S_T(z)=
\begin{pmatrix}
-\delta^{-1}\gamma & \delta^{-1}\\
\alpha-\beta\delta^{-1}\gamma & \beta\delta^{-1}
\end{pmatrix}.
$$

若 $\delta=0$ 则改用 $\alpha$ 块或 Redheffer 星积的互补分式线性公式（对实 $z$，不可逆点在典型情形下构成离散集合）。由能流守恒得

$$
\boxed{\ S_T(x)^\ast S_T(x)=I_2\qquad(x\in\mathbb R)\ },
$$

且在 $\delta$ 不可逆的离散点改用互补块/星积公式时，酉性在极限意义下保持。

默认**单边入射规约**（如取 $a_T^+=0$）以将"系统特性"与"驱动选择"分离。当 $T\to\infty$ 且在适当紧性条件下 $S_T(z)$ 收敛时，记极限 $S(z)\in\mathrm U(2)$。

---

## 2. 评估通道与功能方程的散射等价

### 2.1 评估通道与振幅比

取**固定**边界点（下文均取 $t=T$），存在线性映射 $\eta$ 使

$$
E_F(z):=\langle F,k_{a/2+iz}\rangle
=Y_F^{(1)}(T;z)-i\,Y_F^{(2)}(T;z)
=\sqrt2\,\langle e_+,\,Y_F(T;z)\rangle,\qquad
Y_F(t;z)=M(t,z)\,\eta(F).
$$

记投影 $\Pi_\pm v:=\langle e_\pm,v\rangle e_\pm$。在满足 $\Pi_-(Y_F(T;x))\neq0$ 的 Lebesgue-a.e. 集上定义

$$
s_F(x):=\frac{\Pi_+\big(Y_F(T;x)\big)}{\Pi_-\big(Y_F(T;x)\big)}\in\mathbb T
\qquad\text{（由 (2.1) 与 }U=E^\sharp/E\text{ 的内函数性得出）},
$$

若该分量为零，则改用互补块/星积表达（与 §1 的不可逆块处理保持一致）。由 $2\times2$ 的 $J$-酉分式线性结构（Potapov–Kreĭn/Arov–Dym）可得存在与通道归一选择有关的**常相位** $\phi_F\in\mathbb R$（仅由 $\eta(F)$ 边界归一决定，与 $x$ 无关）使

$$
\boxed{\ \frac{\Pi_+\big(Y_F(T;x)\big)}{\Pi_-\big(Y_F(T;x)\big)}
= e^{i\phi_F}\,\frac{E^\sharp(x)}{E(x)}\qquad(\text{a.e. }x\in\mathbb R).\ }
\tag{2.1}
$$

### 2.2 单通道散射等价

**定理 2.1（功能方程 $\Longleftrightarrow$ 通道特征值恒等）**
设 $E$ 为 de Branges（HB）函数，使 $U(z):=E^\sharp(z)/E(z)$ 为内函数。以下两者互相等价：

$$
\text{\rm(1)}\quad E^\sharp(z)=\varepsilon\,E(z)\ \ (\forall z\in\mathbb C)
\ \ \bigl(\text{若有现实性，则等价于 }E(-z)=\varepsilon E(z)\bigr);
$$

$$
\text{\rm(2)}\quad s_F(x)=e^{i\phi_F}\,\varepsilon\qquad(\text{a.e. }x\in\mathbb R),
$$

其中 $\phi_F\in\mathbb R$ 为与 $\eta(F)$ 的边界归一有关的**常相位**。

*证明*：
(1)$\Rightarrow$(2)：由 (2.1) 立得 $s_F(x)=e^{i\phi_F}\,U(x)=e^{i\phi_F}\,\varepsilon$。
(2)$\Rightarrow$(1)：由 (2.1) 与 (2) 得 $U(x)\equiv\varepsilon$（a.e.）。因 $U$ 为内函数，边界值常等式蕴含 $U(z)\equiv\varepsilon$ 于 $\mathbb C_+$；再由反射原理得 $E^\sharp=\varepsilon E$。∎

---

## 3. 内函数相位与 Herglotz–Nevanlinna

令 $m(z)$ 为规范系统的 Weyl–Titchmarsh 函数（$\Im m(z)\ge0$ 于 $\Im z>0$）。以内函数

$$
U(z)=\frac{E^\sharp(z)}{E(z)}
$$

的实轴**非切向**边界值定义相位 $\varphi(x)$（a.e. $x$ 上 $U(x)=e^{2i\varphi(x)}$）。记 $\mu$ 为对应谱测度，$\mu'_{\mathrm{ac}}$ 为其绝对连续密度。

**定理 3.1（$\varphi'=\Im m$ 与 $\mu'_{\mathrm{ac}}=\frac{1}{\pi}\Im m$）**
取**非切向**边界值，在 Lebesgue-a.e. 的 $x\in\mathbb R$ 上，

$$
\boxed{\ \varphi'(x)=\Im m(x+i0),\qquad
\mu'_{\mathrm{ac}}(x)=\frac{1}{\pi}\Im m(x+i0),\qquad
\varphi'(x)=\pi\,\mu'_{\mathrm{ac}}(x)\ }.
$$

*证明*：de Branges 相位 $\varphi(x)$ 由 $E(x)=|E(x)|e^{-i\varphi(x)}$ 定义，且 $U(x)=e^{2i\varphi(x)}$。核对公式给出

$$
\varphi'(x)=\pi\,\frac{K(x,x)}{|E(x)|^2}=\pi\,\mu'_{\mathrm{ac}}(x).
$$

标准化 Herglotz 表示 $m(z)=a+b z+\int_\mathbb R\bigl(\frac{1}{t-z}-\frac{t}{1+t^2}\bigr)\,d\mu(t)$ 之边界值满足 $\mu'_{\mathrm{ac}}(x)=\frac{1}{\pi}\Im m(x+i0)$，从而 $\varphi'(x)=\Im m(x+i0)$。∎

> 注：Cayley 变换 $\Theta=(m-i)/(m+i)$ 为 Schur 函数；在绝对连续谱上 $|\Theta(x)|<1$，不宜直接用其定义相位。

---

## 4. 解析纪律与误差三分解

### 4.1 窗化与奇性

取偶窗 $\psi$（紧支或指数衰减），设 $\Xi_\psi(s):=\langle F\ast\psi,\,k_s\rangle$。在满足方向亚纯化的竖条/半平面内、$\psi$ 为偶窗且为紧支或指数衰减、且窗 $\psi$ 的拉普拉斯/傅里叶像在该域内无极点时，

$$
\boxed{\ \operatorname{Sing}(\Xi_\psi)=\operatorname{Sing}(\Xi),\ \text{且奇性阶不升；若 }\psi\text{ 在奇点处非零，则阶同。}\ }
$$

理由：有限阶 Euler–Maclaurin 仅引入整函数校正；在方向亚纯化的竖条/半平面内，卷积/窗化不改变主尺度奇性集合。若窗 $\psi$ 在奇点处为零，则可能**降低**阶，但不**升**阶。

### 4.2 Nyquist–Poisson–EM 三分解

对光滑带限或指数衰减的 $g$，步长 $\Delta$、EM 阶 $M$、截断半径 $T$，记 $\widehat g(\omega):=\int_{\mathbb R}e^{-i\omega u}g(u)\,du$，有

$$
\Bigl|\int_{-T}^{T}g(u)\,du-\Delta\sum_{|k|\le \lfloor T/\Delta\rfloor}g(k\Delta)\Bigr|
\le
\underbrace{\sum_{m\neq0}\big|\widehat g(2\pi m/\Delta)\big|}_{\text{别名}}
+\underbrace{\sum_{j=1}^{M-1}c_{2j}\,\Delta^{2j}\,|g^{(2j)}|_{L^1([-T,T])}}_{\text{伯努利层（有限阶 EM 系数，含 }B_{2j}\text{）}}
+\underbrace{\int_{|u|>T}|g(u)|\,du}_{\text{截断尾项}}.
$$

若 $\operatorname{supp}\widehat g\subset[-\Omega,\Omega]$ 且 $\Delta\le\pi/\Omega$，则别名项为零。

---

## 5. 例示

* **Riemann $\xi$**：$a=1,\ \varepsilon=+1$。评估通道的散射特征值在实轴恒为 $+1$；相位导数由定理 3.1 以 $\Im m$ 读出；谱密度为 $\tfrac{1}{\pi}\Im m$。

* **Dirichlet $L(\chi,\cdot)$**：$a=1,\ |\varepsilon|=1$。同理，通道特征值恒为 $\varepsilon$；实特征给 $\varepsilon=\pm1$。

---

## 6. 稳健性与边界情形

* **块奇异点与互补公式**：当传递到散射的 $\delta$ 块不可逆时，改用 $\alpha$ 块或 Redheffer 星积，二端口散射仍良定并在实频保持酉性。在 $\mathbb R$ 上该退化频率为离散集，与正文 §1 的分式线性构造自洽。

* **反辛对称与镜像**：若存在 $\mathbf S$ 使

$$
\mathbf S^\top\mathbf J\mathbf S=-\mathbf J,\qquad \mathbf S^\top H(t)\,\mathbf S=H(t)\ \text{(a.e.)},
$$

则有

$$
M(t,-z)=\mathbf S\,M(t,z)\,\mathbf S^{-1},\qquad
S(-z)=\mathbf C\,S(z)\,\mathbf C^{-1},
$$

其中 $\mathbf C$ 由边界分解 $\{e_-,e_+\}$ 的互换诱导，与通道特征值恒等一致。

* **窗/采样稳定性**：带限或指数窗结合 Nyquist 条件可抑制别名项；有限阶 EM 仅引入可控伯努利层常数，确保非渐近估计稳健。

---

## 7. 可检清单

1. **规范系统**：给出 $H\succeq0$ 与 $M(t,z)$，核查

$$
M(t,\bar z)^\ast\mathbf J M(t,z)
=\mathbf J+(z-\bar z)\int_0^t M(s,\bar z)^\ast H(s)M(s,z)\,ds,\quad
\det M\equiv1.
$$

2. **二端口散射（实频）**：构造 $S_T(x)$ 并验证 $S_T(x)^\ast S_T(x)=I_2$（$x\in\mathbb R$）；对不可逆块采用互补公式/星积。
3. **评估通道**：建立 $E_F(z)=Y_F^{(1)}-iY_F^{(2)}$ 与振幅比关系式 (2.1)。
4. **功能方程等价**：以内函数 $U=E^\sharp/E$ 与定理 2.1 检验"$E^\sharp=\varepsilon E$"$\Longleftrightarrow$"$s_F\equiv e^{i\phi_F}\varepsilon$"；有现实性时等价于"$E(-z)=\varepsilon E(z)$"。
5. **相位—谱密度**：用定理 3.1 以 $\varphi'(x)=\Im m(x+i0)$ 与 $\mu'_{\mathrm{ac}}(x)=\frac{1}{\pi}\Im m(x+i0)$ 连接窗化积分与谱密度。
6. **解析—误差纪律**：仅用**有限阶** EM；方向亚纯化确保"极点 = 主尺度"；窗在奇点处非零时阶同（否则可能下降但不升）。

---

## 8. 与既有篇章的接口

* **↔ S14（RKHS/BN 界面）**：评估向量 $k_s$ 与内积评估为散射通道的振幅提供 Hilbert 语义；BN 投影的窗选择在散射侧体现为入—出模态的能量分配。
* **↔ S15（Weyl–Heisenberg 酉表示）**：$U_\tau,V_\sigma$ 的群作用在散射侧对应"频移—时移"的 affine 变换；镜像算子 $J$ 与反辛对称 $\mathbf S$ 在边界分解下保持散射的对称性。
* **↔ S16（de Branges–Krein 规范系统）**：传递矩阵 $M(t,z)$ 与哈密顿量 $H(t)$ 直接生成二端口散射；功能方程 $E^\sharp=\varepsilon E$ 与镜像本征 $JF=\varepsilon F$ 在散射侧对应通道特征值恒等（定理 2.1）。
* **↔ S4/S5（EM/方向亚纯化）**：窗化与离散仅用有限阶 EM，保证散射矩阵的奇性集合与阶的稳健性（§4.1）。
* **↔ S8（Nyquist–Poisson–EM）**：三分解误差控制在散射侧确保数值实现的非渐近可检性（§4.2）。
* **↔ S13（谱半径阈值）**：散射的能量守恒与通道特征值可与共振器的谱半径对齐，用于大值存在性的阈值判据。

---

## 结语

通量守恒的一阶辛型规范系统与二端口散射结构，为完成功能方程的镜像对称提供了精确的算子化表达：在实频上散射矩阵酉且受反辛对称约束；对评估的一维通道，其特征值在实轴恒等于根数 $\varepsilon$。以内函数 $U=E^\sharp/E$ 定义的相位把散射与谱密度通过 Herglotz–Nevanlinna 理论紧密耦合；配合**有限阶** Euler–Maclaurin 与 **Nyquist–Poisson–EM** 三分解的误差控制，保证奇性集合与阶的稳健性，从而将"镜像—核—Hilbert 子空间""群表示—Weyl 关系"与"散射—边界—通量"三条脉络统一于可检的算子框架之中，并为后续的**轨道—谱窗化不等式**（S18）提供直接可用的入—出算子骨架。
