# Null–Modular 双覆盖统一原理：在因果钻石上对齐信息几何变分与散射半相位的 $\mathbb{Z}_2$ holonomy

## Abstract

在每一点小因果钻石 $B_\ell(p)$ 上提出一条把信息几何变分的一阶—二阶判据与定能散射半相位的平方根双覆盖耦合的统一路线。方法论核心是在乘积底空间 $Y:=M\times X^\circ$ 上以**体积分版本**的离散 $\mathbb Z_2$–BF 机制选择"物理可实现扇区"：令 $\dim Y=d$，取上链场 $a\in C^{d-3}(Y;\mathbb Z_2)$、$b\in C^{d-2}(Y;\mathbb Z_2)$ 与

$$
I_{\rm BF}[a,b;g,S]
=\mathrm i\pi\!\int_Y a\smile\delta b
+\mathrm i\pi\!\int_Y b\smile K(g,S),\qquad
K\in Z^2(Y;\mathbb Z_2),
$$

其中 $K$ 的 Künneth 分解同时包含**几何自旋障碍** $\pi_M^\ast w_2(TM)$、**散射线丛的 $H^2$ 通道** $\pi_X^\ast\rho\!\big(c_1(\mathcal L_S)\big)$（扭挠情形）与**平方根双覆盖的 $H^1$ 通道**的交叉项 $\sum_j\pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j$（$\mu_j\in H^1(M;\mathbb Z_2)$、$\mathfrak w_j\in H^1(X^\circ;\mathbb Z_2)$）。对上同调类求和后，配分函数在上同调意义上投影到 $[K]=0$，从而在一切物理回路上强制半相位 holonomy $\nu_{\sqrt{\det S}}(\gamma)\equiv 1$。几何侧：一阶层 $\delta S_{\rm gen}=0\Rightarrow G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$，二阶层 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$。散射侧：在迹类/相对迹类与（修正）行列式门槛下由 Birman–Kreĭn、谱流与模二交数得到 $\nu_{\sqrt{\det S}}=(-1)^{\mathrm{Sf}}=(-1)^{I_2(\gamma,D)}$ 的稳健表述。提出"模组—散射对齐"的**充分条件**并给出**可解示例**；给出含边界时的相对上同调版本与边界对偶项。以一维 $\delta$ 势、二维 Aharonov–Bohm 与拓扑超导端点散射做指纹化应用。两条技术链分别对齐信息几何变分与自指散射的技术底稿。

## Keywords

广义熵；相对熵；规范能量；小因果钻石；模组 Berry 联络；Birman–Kreĭn；谱流；模二交数；$\mathbb Z_2$–BF 顶项；$H^1/H^2$ 不变量；Künneth 分解；$\mathrm{spin}^c$；拓扑超导端点散射

---

## Introduction & Historical Context

在 $B_\ell(p)$ 上以重整化后的广义熵

$$
S_{\rm gen}
=\frac{A(\partial B_\ell)}{4G\hbar}
+S_{\rm out}^{\rm ren}+S_{\rm ct}^{\rm UV}
-\frac{\Lambda}{8\pi G}\,V(B_\ell)
$$

为泛函：一阶层 $\delta S_{\rm gen}=0$ 得 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$；二阶层 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$ 与 Hollands–Wald 规范能量非负等价。论证基于 Raychaudhuri–Sachs–Grönwall 显式不等式与边界层估计、加权光线变换的 Radon‑型闭包、OS/KMS–Fisher 解析延拓的度量判据与协变相空间的 null 边界/角点处方。

散射侧在去除鉴别子 $D\subset X$ 后的参数空间 $X^\circ$ 上，以

$$
\alpha=\frac{1}{2\mathrm i}(\det S)^{-1}\mathrm d(\det S),\qquad
\nu_{\sqrt{\det S}}(\gamma)=\exp\!\Bigl(\mathrm i\oint_\gamma \alpha\Bigr)\in{\pm1},
$$

刻画平方根双覆盖；在行列式与谱位移良定义的门槛下，$\nu_{\sqrt{\det S}}=(-1)^{\mathrm{Sf}}=(-1)^{I_2(\gamma,D)}$。
本文在 $Y=M\times X^\circ$ 上通过 $\mathbb Z_2$–BF 机制把**方程—稳定**与**holonomy 平凡化**统一到**变分—holonomy**的单一语言，并把 $\mathbb Z_2$ 不变量的 $H^1/H^2$ 两条来源显式并行化。

---

## Symbols, Units, Conventions

度规签名 $(-+++)$；单位 $c=k_B=1$，保留 $\hbar$。微分与虚数单位统一为 $\mathrm d$、$\mathrm i$。运算符与群记号统一为 $\operatorname{tr}$、$\operatorname{Pf}$、$\operatorname{sgn}$、$\det_p$、$\mathrm{Sf}$、$U(1)$、$\mathbb Z_2$。
**物理回路** $\gamma\subset X^\circ$：可由外参绝热实现的闭路；若绕过 $D$，以小半圆切除或折返保持绝热并用 $I_2(\gamma,D)$ 记录奇偶。**物理二维循环**允许两类乘积：$\Sigma_2\times{\mathrm{pt}}\subset M\times X^\circ$ 与 $\Sigma_1\times\gamma_1\subset M\times X^\circ$（$\Sigma_k$ 为 $M$ 中闭 $k$‑链，$\gamma_1\subset X^\circ$ 为闭 1‑链）。

---

## Conceptual Bridge: Künneth 分解与 $H^1/H^2$ 两条散射不变量

Künneth 给出

$$
H^2(Y;\mathbb Z_2)\cong
H^2(M)\ \oplus\ \big(H^1(M)\otimes H^1(X^\circ)\big)\ \oplus\ H^2(X^\circ)\ \oplus\ \mathrm{Tor}.
$$

散射平方根的全局障碍有两条并行来源：
**$H^1$ 路线**：主 $\mathbb Z_2$‑丛类 $\mathfrak w\in H^1(X^\circ;\mathbb Z_2)$ 控制
$\nu_{\sqrt{\det S}}(\gamma)=(-1)^{\langle\mathfrak w,[\gamma]\rangle}$；在 $\Sigma_1\times\gamma_1$ 上以交叉项
$\pi_M^\ast\mu\smile \pi_X^\ast\mathfrak w$（$\mu\in H^1(M;\mathbb Z_2)$ 为与 $\Sigma_1$ 对偶的类）配对。
**$H^2$ 路线**：平直线丛 $\mathcal L_S$ 的 $c_1(\mathcal L_S)\in H^2(X^\circ;\mathbb Z)$（扭挠）经模二约化 $\rho\!\big(c_1\big)$；在 $\Sigma_2\times{\mathrm{pt}}$ 上直接配对。
后文 BF 顶项统一把三部分累加到同一 $K$ 中并以 $[K]=0$ 作为"可实现扇区"的充要判据。

---

## Model & Assumptions

**几何与态**：$(M,g)$ 为定向四维流形，$g\in C^3$、$T_{ab}\in C^1$；小钻石腰面为极大截面，$\theta(0)=\sigma(0)=\omega(0)=0$，零测地族超曲面正交；Hadamard 类态与点分裂重整化；$[0,\lambda_*]$ 内无共轭点。
**散射与正则性**：$S-\mathbf 1\in\mathfrak S_1$ 或满足相对迹类并采用修正行列式 $\det_p$；闭路数据分段 $C^1$；阈值/嵌入本征值以小半圆切除或折返，并以 $I_2(\gamma,D)$ 稳定。
**单位与温标**：体积项取 $-\tfrac{\Lambda}{8\pi G}V$；一阶极值在固定温标/加速度框架下进行（$\delta T=0$），不把 $T$ 作为变分变量。

---

## Main Results (Theorems and Alignments)

### 定理 1（Null 链：两层判据）

在上述几何正则性与协变相空间边界/角点处方下，

$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab},\qquad \delta^2 S_{\rm rel}=\mathcal E_{\rm can}[h,h]\ge 0 .
$$

首式由"族约束 $\Rightarrow$ 点态"的 Radon‑型闭包与零锥刻画得到；次式与 Hollands–Wald 规范能量非负等价。

### 定理 2（Modular 链：模二等价；在迹类/相对迹类 + $\det_p$ + 阈值/嵌入本征值以 $I_2$ 稳定 的门槛下）

对任意闭路 $\gamma\subset X^\circ$，

$$
\nu_{\sqrt{\det S}}(\gamma)
=\exp\!\Bigl(-\mathrm i\pi\oint_\gamma \mathrm d\xi\Bigr)
=(-1)^{\mathrm{Sf}(\gamma)}
=(-1)^{I_2(\gamma,D)} .
$$

其中 $\xi$ 为谱位移，$\mathrm{Sf}$ 为谱流。

### 定理 3（$\mathbb Z_2$–BF 扇区选择：体积分、一般维度、相对上同调）

令 $d=\dim Y$，取

$$
a\in C^{d-3}(Y;\mathbb Z_2),\quad b\in C^{d-2}(Y;\mathbb Z_2),\quad
K:=\pi_M^\ast w_2(TM)\ +\ \underbrace{\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j}_{H^1\!\times H^1\ \text{通道}}\ +\ \underbrace{\pi_X^\ast\rho\!\big(c_1(\mathcal L_S)\big)}_{H^2\ \text{通道}} .
$$

取

$$
I_{\rm BF}[a,b]=\mathrm i\pi\!\int_Y a\smile\delta b+\mathrm i\pi\!\int_Y b\smile K .
$$

在闭流形上，欧拉—拉格朗日方程给 $\delta b=0,\ \delta a=K$。对上同调类求和后

$$
\boxed{\,Z_{\rm top}\propto \delta\big([K]\big)\quad\Longleftrightarrow\quad [K]=0\in H^2(Y;\mathbb Z_2)\,},
$$

从而对一切允许的二维循环 $S\subset Y$ 有 $\langle K,[S]\rangle=0$。若 $Y$ 含边界，加入边界对偶项或施加相对边界条件，结论为 $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$ 的充要条件（相对上同调）。

### 定理 4（模组—散射对齐：充分条件与适用域）

若编码子空间的模组 Berry 曲率等于体辛形式，且存在线性响应嵌入使

$$
\oint_{\gamma}\frac{1}{2\mathrm i}\operatorname{tr}\!\big(S^{-1}\mathrm dS\big)=\oint_{\gamma}\mathcal A_{\rm mod},
$$

则 $\nu_{\sqrt{\det S}}(\gamma)=\exp(\mathrm i\oint_\gamma \mathcal A_{\rm mod})$ 与二阶稳定性同阶，对齐为**充分**条件。**失效/谨慎域**：非平衡驱动、强非局域响应核、HRRT 几何非光滑、参数族断裂等情形上式的实数环量可能不等，但其 $\mathbb Z_2$ 投影仍可一致。

### 定理 5（统一原理：分解陈述）

**E‑(a)（充分）** 在定理 1–4 的门槛与对齐假设下，以下命题等价：
(i) 小钻石上一阶极值与二阶非负；
(ii) $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$；
(iii) 一切物理回路上 $\nu_{\sqrt{\det S}}(\gamma)\equiv 1$。
**E‑(b)（模型域内必要）** 在一维 $\delta$ 势、二维 Aharonov–Bohm 与端点散射（Class D/DIII）的可解族中，若 (iii) 成立，则 (ii) 成立（相对上同调意义）。

---

## Proofs

### 定理 1

由 Sachs 与变系数 Grönwall 得

$$
\big|\theta(\lambda)+\lambda R_{kk}\big|\le \tfrac12 C_{\nabla R}\lambda^2+C_\sigma^2|\lambda|.
$$

以与 $\varepsilon$ 无关的支配函数建立"极限—积分可交换"，配合加权光线变换与局域化引理将族约束下推为 $R_{kk}=8\pi G\,T_{kk}$。零锥刻画与 Bianchi 恒等式给出 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。协变相空间的 null 边界与角点处方保证辛流无外泄与 $\delta H_\chi$ 可积，故 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$。

### 定理 2

在门槛下 $\det S=\mathrm e^{-2\pi\mathrm i\,\xi}$；沿闭路 $\gamma$ 有

$$
\deg(\det S|_\gamma)=-\oint_\gamma \mathrm d\xi=\mathrm{Sf}(\gamma)\in\mathbb Z,\qquad
\nu_{\sqrt{\det S}}(\gamma)=\exp\!\Bigl(-\mathrm i\pi\oint_\gamma \mathrm d\xi\Bigr).
$$

阈值/嵌入本征值以 $I_2(\gamma,D)$ 稳定。

### 定理 3（体积分、一般维度、相对上同调）

$a\in C^{d-3}$、$b\in C^{d-2}$ 使 $\deg(a\smile\delta b)=\deg(b\smile K)=d$。闭流形上变分给 $\delta b=0,\ \delta a=K$。若 $[K]\neq 0$，$\delta a=K$ 无全球解；对 $[a]$ 求和把配分函数投影到 $[K]=0$。含边界时以相对上同调 $H^\bullet(Y,\partial Y;\mathbb Z_2)$ 替代，并加入边界对偶项 $\mathrm i\pi\int_{\partial Y}a\smile b$ 保证离散 Stokes 与变分无缺口；结论即 $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$ 的充要条件。

### 定理 4

在半空间编码中边界平移 $U(\lambda)=\mathrm e^{-\mathrm iP\lambda}$ 生成 $\mathcal A_{\rm mod}=\langle P\rangle\mathrm d\lambda$；移动镜反射给 $S=e^{2\mathrm i k\lambda}$，$\tfrac{1}{2\mathrm i}\operatorname{tr}(S^{-1}\mathrm dS)=k\,\mathrm d\lambda$。两侧环量一致；非局域核可使实数环量不同，但模二投影稳定。

### 定理 5

E‑(a) 由定理 3 得 (ii)$\Rightarrow$(iii)，由定理 1 与 4 得 (i)$\Rightarrow$(iii)；以检测子回路生成相对二同调得 (iii)$\Rightarrow$(ii)。E‑(b) 在可解族中与 $D$ 横截的回路构造完成。

---

## Model Apply

### 一维 $\delta$ 势（$\hbar=2m=1$）

偶宇称通道

$$
S(k)=\frac{2k-\mathrm i\lambda}{2k+\mathrm i\lambda}=e^{2\mathrm i\delta(k)},\qquad f(k)=1+\frac{\mathrm i\lambda}{2k}.
$$

**复参数小环（真奇点）**：取 $E(t)=E_0$、$\lambda(t)=-2\mathrm i\sqrt{E_0}+\rho\,\mathrm e^{\mathrm i t}$，则

$$
\oint_{\gamma}\frac{1}{2\mathrm i}S^{-1}\mathrm dS=\pi,\qquad \nu_{\sqrt{\det S}}=-1 .
$$

**实参数折返**：在 $(E,\lambda)$ 平面折返横截 $D$ 并以小半圆切除，$I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt{\det S}}=-1$。

### 二维 Aharonov–Bohm

通量 $\alpha\mapsto\alpha+1$ 穿越 $\alpha=\tfrac12$ 时 $\deg(\det S|_\gamma)=1\Rightarrow\nu_{\sqrt{\det S}}=-1$。分波无穷以分波截断或 $\det_2$ 正则化，模二结果不变。

### 拓扑超导端点散射

Class D：$Q=\operatorname{sgn}\det r(0)$；Class DIII：$Q=\operatorname{sgn}\operatorname{Pf}r(0)$。两者等价于 $\sqrt{\det r(0)}$ 的分支号符；隙闭合（属 $D$）横跨一次触发 $Q$ 翻转并与 $\nu_{\sqrt{\det r}}$ 同步。

---

## Engineering Proposals（参数窗与误差估计）

**AB 干涉环**：有效面积 $A\sim 1~\mu\mathrm m^2$，半通量 $B_{1/2}\simeq\Phi_0/(2A)\sim \mathrm{mT}$。需 $L_\phi\gtrsim$ 周长且 $|\delta B|\ll \Phi_0/(4A)$ 以解析 $\pi$ 跃迁。
**冷原子 $\delta$ 势环路**：以 Feshbach 调谐 $\lambda$ 绕极点闭路，绝热标度 $\tau_{\rm drive}\gg \hbar/\Delta$ 抑制非绝热误差；Ramsey/MZ 干涉读出 $\arg S$。
**拓扑纳米线（D/DIII）**：$k_BT\ll\Delta$、接触展宽 $\Gamma/\Delta\ll1$；$\operatorname{sgn}\det r(0)$/$\operatorname{sgn}\operatorname{Pf}r(0)$ 的翻转与量化导通峰协变。

---

## Discussion

**选择原则的充要化**：对一切允许二维循环 $S\subset Y$ 有

$$
\big\langle\,K\,,\,[S]\big\rangle
=\Big\langle \pi_M^\ast w_2(TM)+\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j+\pi_X^\ast\rho\!\big(c_1(\mathcal L_S)\big),[S]\Big\rangle=0
$$

为"物理可实现扇区"的充要条件；若 $[K]\neq0$，存在回路使 $\nu_{\sqrt{\det S}}=-1$。
**充分 vs 必要**：模组—散射对齐提供充分而非必要条件；在非平衡/非局域情形实数环量可能不等，但 $\mathbb Z_2$ 投影常稳定。
**OS/KMS–Fisher**：反射正性与条带解析性给出延拓后 $g^{(L)}_{tt}<0$、$g^{(L)}_{ij}\succ0$ 与 $g^{(L)}_{ti}|_{t=0}=0$ 的充分判据，作为几何侧结构性互补。

---

## Conclusion

通过在 $Y=M\times X^\circ$ 上以**体积分版本**的 $\mathbb Z_2$–BF 机制实现 $H^2$ 与 $H^1\!\times H^1$ 两条散射不变量与几何自旋障碍的同调对齐，获得"$[K]=0$"这一**扇区选择原则**；在"模组—散射对齐"的充分门槛下，将小因果钻石的一阶—二阶判据与半相位 holonomy 平凡化对齐。配合模二 Levinson 与鉴别子交数的稳健刻画，建立把**方程—稳定—拓扑**统一到**变分—holonomy**的工作框架，并在 $\delta$ 势、AB 散射与拓扑端点散射上给出可计算与可检的指纹。

---

## Acknowledgements, Code Availability

未使用外部代码；所有推导与计算可依正文与附录复现。

---

## References

Jacobson, *Phys. Rev. Lett.* **75** (1995) 1260；Hollands & Wald, *Commun. Math. Phys.* **321** (2013) 629；Jafferis–Lewkowycz–Maldacena–Suh, *JHEP* **06** (2016) 004；Faulkner–Leigh–Parrikar–Wang, *JHEP* **09** (2016) 038；Bousso *et al.*, *Phys. Rev. D* **93** (2016) 024017；Czech *et al.*, *Phys. Rev. Lett.* **120** (2018) 091601；*Phys. Rev. D* **108** (2023) 066003；Pushnitski, *J. Funct. Anal.* **183** (2001) 269；Fulga–Hassler–Akhmerov–Beenakker, *Phys. Rev. B* **83** (2011) 155429；Akhmerov *et al.*, *Phys. Rev. Lett.* **106** (2011) 057001；Witten, *Rev. Mod. Phys.* **88** (2016) 035001。
（两份技术底稿为信息几何变分与自指散射之内部支点。）

---

## 附录 I  体积分版本 $\mathbb Z_2$–BF：次数—积分域—相对上同调

令 $d=\dim Y$。取 $a\in C^{d-3}(Y;\mathbb Z_2)$、$b\in C^{d-2}(Y;\mathbb Z_2)$、$K\in Z^2(Y;\mathbb Z_2)$，则
$\deg(a\smile\delta b)=\deg(b\smile K)=d$。闭流形上

$$
I_{\rm BF}=\mathrm i\pi\!\int_Y a\smile\delta b+\mathrm i\pi\!\int_Y b\smile K,\qquad
\delta b=0,\ \ \delta a=K,
$$

规范变换 $a\mapsto a+\delta\lambda^{d-4}$、$b\mapsto b+\delta\lambda^{d-3}$ 不改相位。对 $[a],[b]$ 求和，配分函数投影到 $[K]=0\in H^2(Y;\mathbb Z_2)$。有边界时以相对上同调 $H^\bullet(Y,\partial Y;\mathbb Z_2)$ 处理，并加入边界对偶项 $\mathrm i\pi\int_{\partial Y}a\smile b$。

## 附录 II  Künneth 分解与 $H^1/H^2$ 的等价操控

由

$$
H^2(Y)\cong H^2(M)\oplus\big(H^1(M)\otimes H^1(X^\circ)\big)\oplus H^2(X^\circ)\oplus\mathrm{Tor}
$$

可作

$$
K=\pi_M^\ast w_2(TM)+\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j+\pi_X^\ast\rho\!\big(c_1(\mathcal L_S)\big).
$$

对物理二维循环的两类乘积：

$$
\begin{aligned}
&\text{(A)}\ \ \Sigma_2\times{\mathrm{pt}}:\ \ \langle K,[S]\rangle=\langle w_2(TM),[\Sigma_2]\rangle,\\
&\text{(B)}\ \ \Sigma_1\times\gamma_1:\ \ \langle K,[S]\rangle=\sum_j\langle \mu_j,[\Sigma_1]\rangle\,\langle \mathfrak w_j,[\gamma_1]\rangle
\ +\ \langle \rho(c_1),[{\mathrm{pt}}\times\gamma_1]\rangle .
\end{aligned}
$$

由此 $H^1$ 与 $H^2$ 两通道在二维循环上统一进入同一配对。

## 附录 III  IGVP 的显式不等式与二阶层

给出

$$
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\,\mathrm d\lambda\,\mathrm dA\Big|
\le \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2\Big)A,
$$

与零锥刻画引理，完成 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$；在 null 边界与角点处方下 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$。

## 附录 IV  Birman–Kreĭn、谱流与模二 Levinson 的"工具箱"

（i）$\det S=\mathrm e^{-2\pi \mathrm i\,\xi}$；（ii）$\mathrm{Sf}(\gamma)=-\oint_\gamma \mathrm d\xi$；（iii）阈值/嵌入本征值以 $I_2(\gamma,D)$ 稳定；（iv）多通道/分波用 $\det_p$ 与截断余项估计保证模二鲁棒。

## 附录 V  模组—散射对齐的最小可解示例

半空间编码：边界平移 $U(\lambda)=\mathrm e^{-\mathrm iP\lambda}\Rightarrow \mathcal A_{\rm mod}=\langle P\rangle \mathrm d\lambda$；移动镜反射 $S=e^{2\mathrm i k\lambda}\Rightarrow \tfrac{1}{2\mathrm i}\operatorname{tr}(S^{-1}\mathrm dS)=k\,\mathrm d\lambda$；两侧环量与其 $\mathbb Z_2$ 投影一致。

## 附录 VI  $\delta$ 势与 AB 的显式绕数

复 $\lambda$‑环 $\lambda(t)=-2\mathrm i\sqrt{E_0}+\rho\,\mathrm e^{\mathrm i t}$ 给
$\oint (1/2\mathrm i)S^{-1}\mathrm dS=\pi\Rightarrow \nu_{\sqrt{\det S}}=-1$；AB 圈穿越 $\alpha=\tfrac12$ 时 $\deg(\det S|_\gamma)=1\Rightarrow\nu=-1$。

---

**排版与符号一致性说明**：全文统一使用 $\mathbb Z_2$、$\mathrm d$、$\mathrm i$ 与 $(-,+,+,+)$；积分记号不加前缀；多通道统一采用 $\sqrt{\det S}$ 表述。
