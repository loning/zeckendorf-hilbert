# S19. 谱图与 Ihara ζ：非回溯算子、行列式公式与完成对称

**—— 有限图上的轨道—谱合奏、镜像 $s\mapsto 1-s$ 与窗化不等式**

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在有限无向连通图的有向边空间上构造非回溯算子 $B$，以内循环位移等价（不并入反向）的**原始非回溯回路**定义 Ihara ζ 函数，建立其与 $\det(I-uB)$ 的行列式恒等以及 Bass 公式；在 $(q+1)$-正则图情形，通过谱多项式的自倒数性给出完成函数 $\Xi_G(s)$ 的镜像对称 $\Xi_G(s)=\Xi_G(1-s)$。进一步，在偶窗/偶核、仅使用**有限阶** Euler–Maclaurin（EM）换序的纪律下，建立离散图版的"轨道—谱窗化不等式"，其误差由"别名 + 伯努利层 + 截断"三项非渐近上界统一控制；带限 + Nyquist 条件下别名为零。该框架与 Weyl–Heisenberg 酉系统（S15）、de Branges–Krein 规范系统（S16）、散射算子与完成功能方程的算子等价（S17）、窗化迹不等式（S18）逐项对齐，形成离散几何—谱图—解析函数的统一算子范式。

---

## 0. 设定与记号

令 $G=(V,E)$ 为有限、无向、连通、无自环与多重边的图。记顶点数 $n=|V|$、边数 $m=|E|$。设有向边集

$$
\vec E=\{\,e=(v\to w): \{v,w\}\in E\,\},\qquad N:=|\vec E|=2m,
$$

对 $e=(v\to w)$ 记反向 $\bar e=(w\to v)$。邻接矩阵 $A\in\mathbb R^{n\times n}$、度矩阵 $D=\mathrm{diag}(\deg v)$、统一记

$$
Q:=D-I.
$$

**非回溯算子（Hashimoto）** 定义为

$$
B_{e,f}=
\begin{cases}
1,& \mathrm{tail}(f)=\mathrm{head}(e)\ \text{且}\ f\neq \bar e,\\
0,& \text{否则}.
\end{cases}
$$

其 $k$-次迹 $\operatorname{Tr}B^{k}$ 计数长度为 $k$ 的闭非回溯走步（计起点与方向）。

**原始回路与重排式（方向区分）** 设 $[C]$ 为**原始**非回溯回路的等价类，等价仅按**循环位移**（不将反向并为同类），长度记 $\ell(C)$。记 $\pi_d$ 为长度 $d$ 的此类等价类数，则存在重排恒等式

$$
N_k:=\operatorname{Tr}B^k=\sum_{d\mid k} d\,\pi_d,
$$

其与行列式展开一致。

**窗/核与有限阶换序** 取偶核 $h$ 与偶窗 $w$（带限或指数衰减），尺度 $R>0$ 时 $w_R(t):=w(t/R)$。所有离散—连续换序仅取**有限阶** EM，伯努利层与端点余项对外参（如 $s$、$R$）整/全纯，从而保持"极点 = 主尺度"。

---

## 1. Ihara ζ 的行列式表达与 Bass 公式

### 定义 1.1（Ihara ζ）

$$
Z_G(u):=\prod_{[C]}\bigl(1-u^{\ell(C)}\bigr)^{-1},\qquad |u|\ \text{充分小},
$$

其中 $[C]$ 按循环位移等价（不识别反向）遍历原始非回溯回路。本稿约定原始回路仅按循环位移并类，**不**按反向并类；相应重排式 $N_k=\sum_{d\mid k}d\,\pi_d$ 与行列式展开一致。若改为并入反向（部分文献采用），则 $\pi_d$ 改记为 $\tilde\pi_d$ 且重排式变为 $N_k=\sum_{d\mid k}d\,(2\tilde\pi_d)$（除去回文异常的零测情形），等价地 $Z_G(u)$ 仅差一个幂次的规范化，Bass 公式与后续结论不受影响。

### 定理 1.2（行列式表达）

$$
Z_G(u)^{-1}=\det(I-uB)\qquad(|u|\ \text{充分小}).
$$

**证明.** 由

$$
-\log\det(I-uB)=\sum_{k\ge 1}\frac{\operatorname{Tr}B^{k}}{k}\,u^{k},
$$

并用 $N_k=\sum_{d\mid k}d\,\pi_d$ 重排，逐长整合为原始回路的几何级数，即得定义 1.1 的 Euler 乘积。解析延拓见下述 Bass 公式。 $\square$

### 定理 1.3（Bass 公式）

$$
\boxed{\,Z_G(u)^{-1}=(1-u^2)^{m-n}\,\det\!\bigl(I-uA+u^2 Q\bigr)\,.}
$$

**证明.** 取入射矩阵 $H$、出射矩阵 $O$（$O$ 为字母 'O'）

$$
(H)_{e,v}=\mathbf 1_{\{v=\mathrm{head}(e)\}},\qquad
(O)_{e,v}=\mathbf 1_{\{v=\mathrm{tail}(e)\}},
$$

与反向置换矩阵 $R$（$R_{e,f}=\mathbf 1_{\{f=\bar e\}}$，故 $R^2=I$）。由定义

$$
B=HO^{\top}-R,\qquad HO^{\top}=B+R.
$$

于是

$$
\begin{aligned}
\det(I-uB)
&=\det\!\bigl(I-u(HO^{\top}-R)\bigr)
=\det(I+uR-uHO^{\top})\\
&=\det(I+uR)\cdot \det\!\Bigl(I-u\,(I+uR)^{-1}HO^{\top}\Bigr).
\end{aligned}
$$

利用 $R^2=I\Rightarrow (I+uR)^{-1}=(1-u^2)^{-1}(I-uR)$（因此 $u=\pm1$ 处由多项式恒等延拓）以及

$$
O^{\top}H=A,\qquad O^{\top}RH=O^{\top}O=D,
$$

得

$$
O^{\top}(I+uR)^{-1}H=(1-u^2)^{-1}(A-uD).
$$

上述等式先在 $u\notin\{\pm1\}$ 成立，结论由多项式恒等作解析延拓至全复平面。

由 $\det(I+uR)=(1-u^2)^m$ 与 **Sylvester 行列式恒等式** $\det(I-XY)=\det(I-YX)$ 得

$$
\begin{aligned}
\det(I-uB)
&=(1-u^2)^m\cdot \det\!\Bigl(I-\tfrac{u}{1-u^2}A+\tfrac{u^2}{1-u^2}D\Bigr)\\
&=(1-u^2)^{m-n}\det\!\bigl(I-uA+u^2(D-I)\bigr),
\end{aligned}
$$

即所求。 $\square$

### 推论 1.4（$(q+1)$-正则图）

若 $G$ 为 $(q+1)$-正则，则 $Q=qI$，

$$
Z_G(u)^{-1}=(1-u^2)^{m-n}\,P_G(u),\qquad
P_G(u):=\det\!\bigl(I-uA+q u^2 I\bigr)=\prod_{j=1}^{n}\bigl(1-\lambda_j u+q u^2\bigr),
$$

其中 $\{\lambda_j\}$ 为 $A$ 的特征值。由上式读出 $B$ 的谱：每个 $\lambda_j$ 诱导

$$
\mu_{\pm}=\tfrac12\bigl(\lambda_j\pm\sqrt{\lambda_j^2-4q}\bigr),
$$

并另外出现

$$
(+1)\ \text{与}\ (-1)\ \text{各重数 }\,m-n,
$$

从而总维度闭合 $2n+2(m-n)=2m=N$；在 $(q+1)$-正则图上 $m-n=\tfrac{(q-1)n}{2}$。

---

## 2. 完成多项式与镜像对称（$(q+1)$-正则图）

**假设.** 本节全程设 $G$ 为 $(q+1)$-正则图，故 $Q=qI$ 且 $P_G(u)=\det(I-uA+qu^2I)=\prod_{j=1}^{n}(1-\lambda_j u+qu^2)$。

### 定理 2.1（谱多项式的自倒数性）

$$
\boxed{\,P_G(u)=(q u^{2})^{n}\,P_G\!\left(\tfrac{1}{q u}\right)\,.}
$$

**证明.** 由 $P_G(u)=\prod_{j}(1-\lambda_j u+qu^2)$，直接得
$$
(qu^2)^nP_G\!\left(\tfrac{1}{qu}\right)=\prod_{j}(qu^2-\lambda_j u+1)=P_G(u).
$$
$\square$

### 定义 2.2（完成函数）

置 $u=q^{-s}$，定义（$s\in\mathbb C$）

$$
\boxed{\,\Xi_G(s):=q^{\,n\left(s-\tfrac12\right)}\,P_G\!\bigl(q^{-s}\bigr)\,.}
$$

### 命题 2.3（功能方程）

$$
\boxed{\,\Xi_G(s)=\Xi_G(1-s)\,.}
$$

**证明.** 由定理 2.1 得 $P_G(q^{-(1-s)})=q^{\,n(2s-1)}P_G(q^{-s})$，代回定义即得。功能方程在全复平面按代数恒等成立。 $\square$

### 备注 2.4（Ramanujan 判据）

对 $(q+1)$-正则图，**除去平凡因子 $(1-u^2)^{m-n}$** 与平凡特征值 $+(q+1)$（若 $G$ 为二部，还包含 $-(q+1)$）后，Ihara ζ 的**非平凡**极点全部落在 $|u|=q^{-1/2}$ **当且仅当** 所有**非平凡**邻接特征值满足 $|\lambda_j|\le 2\sqrt q$（即图为 Ramanujan）。

### 备注 2.5（代数恒等式与非自倒数性）

任意 $N\times N$ 矩阵 $B$ 与标量 $u$ 满足

$$
u^{N}\,\det\!\bigl(I-(1/u)B\bigr)=\det(uI-B),
$$

该式为纯代数恒等；一般**不**蕴含 $\det(I-uB)$ 的自倒数性。镜像结构统一由 $P_G(u)$ 或 $\Xi_G(s)$ 承担。

---

## 3. 轨道—谱的窗化不等式（离散图版）

**假设.** 本节起至定理 3.1，全程假设 $G$ 为 $(q+1)$-正则图（故 $Q=qI$）。

取偶核 $h\in W^{2M,1}(\mathbb R)$（$M\ge2$）与偶窗 $w$，并**假设 $\widehat h,\widehat w$ 均带限（紧支集）**，从而 $\widehat h*\widehat w_R$ 亦带限，轨道侧求和为**有限和**，保证绝对收敛。尺度 $R>0$ 时 $w_R(t):=w(t/R)$。

**谱侧**

$$
\mathcal S_{\mathrm{spec}}(h;R):=\sum_{j=1}^{n} h(\lambda_j)\,w_R(\lambda_j).
$$

**轨道侧（并入偶长显式项）**

$$
\boxed{\
\mathcal S_{\mathrm{orb}}^{\star}(h;R)
:=\sum_{k\ge 1}\frac{N_k}{k}\,(\widehat h*\widehat w_R)(k)
\;+\;(m-n)\sum_{k\ge 1}\frac{1}{k}\,(\widehat h*\widehat w_R)(2k)\ }.
$$

第二项来自 Bass 公式中 $(1-u^2)^{m-n}$ 的对数展开：
$$
(n-m)\log(1-u^2)=-(n-m)\sum_{k\ge1}\frac{u^{2k}}{k}=(m-n)\sum_{k\ge1}\frac{u^{2k}}{k},
$$
故偶长项系数确为 $+(m-n)/k$。

### 定理 3.1（窗化迹公式的三分解误差上界）

存在常数 $C=C(M,h,w)$ 与数值参数 $(\Delta,T)$（采样步长、截断阈值），使

$$
\bigl|\,\mathcal S_{\mathrm{spec}}(h;R)-\mathcal S_{\mathrm{orb}}^{\star}(h;R)\,\bigr|
\ \le\ C\sum_{X\in\{\mathrm{spec},\mathrm{orb}\}}\Bigl(\mathrm{alias}_{X}+\mathrm{EM\text{-}layer}_{X}+\mathrm{tail}_{X}\Bigr),
$$

其中分别对谱侧定义 $g_{\mathrm{spec}}:=h\cdot w_R$、对轨道侧定义 $g_{\mathrm{orb}}:=\widehat h*\widehat w_R$，各侧误差项定义为（$X\in\{\mathrm{spec},\mathrm{orb}\}$）

$$
\begin{aligned}
&\mathrm{alias}_{X}:=\sum_{r\neq 0}\bigl|\widehat{g_X}(2\pi r/\Delta)\bigr|,\\
&\mathrm{EM\text{-}layer}_{X}:=\sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\,\bigl|g_X^{(2j)}\bigr|_{L^1},\\
&\mathrm{tail}_{X}:=\int_{|t|>T}\!|g_X(t)|\,dt.
\end{aligned}
$$

当 $g_X$ 带限且 $\Delta\le \pi/\Omega$（Nyquist 步长）时 $\mathrm{alias}_X=0$。

**变换约定.** 本文傅里叶变换取 $\widehat g(\omega)=\int_{\mathbb R}g(t)e^{-i\omega t}\,dt$（角频率制），故别名频谱复制间隔为 $2\pi/\Delta$，带限 $\Omega$ 时 Nyquist 步长为 $\Delta\le\pi/\Omega$。在本约定下
$$
\widehat{h\cdot w_R}=\tfrac{1}{2\pi}(\widehat h*\widehat w_R);
$$
该常数因子 $1/(2\pi)$ 已吸收入误差常数 $C$ 中，不再逐处显式书写。

**说明（偶窗/偶核与端点）** 取偶窗与偶核可使有限阶 EM 的端点项互消/简化，且伯努利层与截断尾项对外参（如 $s,R$）整/全纯，故不引入新奇性，从而保持"极点 = 主尺度"。

---

## 4. 例示

### 4.1 Ramanujan 图

若所有**非平凡** $\lambda_j$ 满足 $|\lambda_j|\le 2\sqrt q$，则 $P_G$ 的零全部位于 $|u|=q^{-1/2}$ 的反演对称环上；由定义 2.2，$\Xi_G(s)$ 的零关于 $s=\tfrac12$ 成对。带限窗与 Nyquist 采样时，定理 3.1 的误差仅来自 EM 层与截断项，具有非渐近可计算性。

### 4.2 循环图 $C_L$

本例为 2-正则图（$q=1$）。此时 $A$ 的谱为 $2\cos(2\pi j/L)$（$0\le j<L$），

$$
P_G(u)=\prod_{j=0}^{L-1}\bigl(1-2u\cos(2\pi j/L)+u^2\bigr),
$$

可用 Chebyshev 多项式闭式化简；非回溯回路计数由长度整除结构给出显式，窗化恒等式可直接核验。

---

## 5. 与"镜像—规范—散射—窗化"框架的接口

* **镜像/功能方程（S17）**：$\Xi_G(s)=\Xi_G(1-s)$ 为离散图的代数镜像；与"$\Xi(a-s)=\varepsilon\Xi(s)\iff JF=\varepsilon F$"之算子等价同构（$u=q^{-s}$ 为尺度映射，$s\mapsto 1-s$ 对应 $u\mapsto 1/(q u)$ 的乘法镜像）。
* **规范系统（S16）**：有限维纯点谱可视作 Herglotz—谱测度框架的离散极限；相位—能量度量与窗化估计相容。
* **散射/二端口（S17）**：非回溯传输可理解为"无回头通道"的离散传递；$\det(I-uA+u^2 Q)$ 的结构与通道特征值恒等在代数层面平行。
* **窗化迹不等式（S18）**：将 Lebesgue 积分替换为长度/频率采样，即得离散版三分解误差上界。
* **Weyl–Heisenberg（S15）**：相位移与尺度变换的带限—采样纪律直接转译到谱图变量（$\lambda$、$k$）的窗化—采样上。

---

## 6. 边界与扩展

* **有限阶 EM**：坚持有限阶以避免伪奇性与非法换序，确保"极点 = 主尺度"。
* **窗衰减与收敛性**：本文采用 $\widehat h,\widehat w$ 双带限的假设以确保轨道侧求和为有限和。若改用非带限窗，则需要（i）$\widehat h*\widehat w_R$ 的衰减足以压制 $N_k\sim q^k$ 的增长，或（ii）在轨道侧引入 $q^{-k/2}$ 归一化以确保级数绝对收敛。当 $\widehat w\notin L^1$ 或衰减不足时，别名与尾项可能主导；宜选带限窗 + Nyquist，或指数窗 + 充分截断。
* **自环/多重边**：若允许自环与多重边，则需按标准方式修正 $B$ 与原始回路定义，同时在 Bass 公式中以带权度矩阵替代 $Q=D-I$。

---

## 附录 A：有限阶 Euler–Maclaurin（用于窗化换序）

若 $g\in C^{2M}([a,b])$ 且 $g^{(2M)}\in L^1([a,b])$，则

$$
\sum_{n=a}^{b} g(n)
=\int_{a}^{b} g(t)\,dt+\frac{g(a)+g(b)}{2}
+\sum_{j=1}^{M-1}\frac{B_{2j}}{(2j)!}\bigl(g^{(2j-1)}(b)-g^{(2j-1)}(a)\bigr)+R_M,
$$

其中 $B_{2j}$ 为伯努利数，$B_{2M}(\{t\})$ 为周期伯努利多项式（其上界可由伯努利数控制），

$$
R_M=\frac{1}{(2M)!}\int_{a}^{b} B_{2M}(\{t\})\,g^{(2M)}(t)\,dt,\qquad
|R_M|\le \frac{|B_{2M}|}{(2M)!}\,|g^{(2M)}|_{L^1}.
$$

在偶窗/偶核下端点项简化；积分—求和换序始终限制于有限阶层内，保证余项对外参整/全纯。

---

## 参考文献

* Y. Ihara, *On discrete subgroups of the two by two projective linear group over $p$-adic fields*, J. Math. Soc. Japan 18 (1966), 219–235.
* K. Hashimoto, *Zeta functions of finite graphs and representations of $p$-adic groups*, Adv. Stud. Pure Math. 15 (1989), 211–280.
* H. Bass, *The Ihara–Selberg zeta function of a graph*, Int. J. Math. 3 (1992), 717–797.
* H. M. Stark and A. A. Terras, *Zeta functions of finite graphs and coverings*, Adv. Math. 121 (1996), 124–165.
* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge Univ. Press, 2011.
* M. Kotani and T. Sunada, *Zeta functions of finite graphs*, J. Math. Sci. Univ. Tokyo 7 (2000), 7–25.

---

## 结语

Ihara–Hashimoto–Bass 三恒等在有限图上给出了非回溯算子、邻接谱与回路几何的紧耦合；$(q+1)$-正则情形的谱多项式自倒数性导出完成函数 $\Xi_G(s)$ 的镜像对称。将 S18 的窗化思想移植至离散图，并显式并入偶长项后，得到仅依赖有限阶 EM 的非渐近三分解上界；带限 + Nyquist 下可达"别名 = 0"。由此，离散几何的轨道—谱合奏与解析函数的完成—镜像在统一算子视角中闭环。
