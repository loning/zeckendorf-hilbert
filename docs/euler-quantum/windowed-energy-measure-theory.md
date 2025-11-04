# 能量的窗化谱测度理论（WEM：Windowed Energy as Measure）

Version: 1.4

## 摘要

建立以窗化相对谱密度的一阶矩刻画能量的自洽框架。核心刻度链在绝对连续谱几乎处处成立：

$$
\boxed{\ \frac{\varphi'(E)}{\pi}\;=\;\rho_{\mathrm{rel}}(E)\;=\;\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ },
$$

其中 $\varphi(E)=\tfrac12\operatorname{Arg}\det S(E)$，$\mathsf Q(E)=-i\,S(E)^\dagger\partial_E S(E)$ 为 Wigner–Smith 群延迟矩阵，$\rho_{\mathrm{rel}}$ 为相对谱密度。以窗 $w$ 对 $\rho_{\mathrm{rel}}$ 加权定义能量泛函

$$
\mathcal E[w]=\int_{\mathbb R}E\,w(E)\,\rho_{\mathrm{rel}}(E)\,dE.
$$

本文给出：能量重参数—窗推前的协变不变性与通道加性；基于 Birman–Kreĭn 迹—相位公式的 $\log\det$ 表征及在 Hilbert–Schmidt 相对扰动下的 $\det_2$/Koplienko 正则化；有限阶 Euler–Maclaurin（EM）纪律下的非渐近误差闭合；以及在 EBOC（静态块·观察—计算）与 RCA（可逆元胞自动机）中的语义嵌入与 Koopman 谱对应。所用事实基础包括群延迟矩阵的定义与多物理场推广、谱移函数与相对迹、以及 EM 误差学。([chaosbook.org][1])

---

## Notation & Axioms / Conventions

**Card-1（刻度同一式）**：在绝对连续谱 a.e. 成立

$$
\frac{\varphi'(E)}{\pi}=\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\mathsf Q(E)=-i\,S^\dagger(E)\,\partial_E S(E).
$$

单/多通道情形与原始"寿命矩阵"定义一致，并已在电磁、声学等系统中建立计算与实验路径。([chaosbook.org][1])

**Card-2（有限阶 EM—NPE 纪律）**：一切离散近似仅采用**有限阶** Euler–Maclaurin 展开；误差分解为"别名 + Bernoulli 校正 + 尾项"，常数仅依赖端点导数与有限阶光滑度。([维基百科][2])

**散射—谱移规范**：在迹类散射框架

$$
\det S(E)=\exp\!\big(-2\pi i\,\xi(E)\big),\qquad (\log\det S)'(E)=i\,\operatorname{tr}\mathsf Q(E),
$$

故 $\rho_{\mathrm{rel}}(E)=-\xi'(E)$；在 Hilbert–Schmidt 相对扰动下以 Koplienko 谱移 $\eta$ 与 $\det_2$ 取代之。([arXiv][3])

**窗与窗化测度**：窗 $w\in L^1(\mathbb R)\cap C^1$，$w\ge0$、$\int w=1$、$\int |E|w(E)\,dE<\infty$；窗化相对谱测度 $d\mu_w(E)=w(E)\rho_{\mathrm{rel}}(E)\,dE$。

---

## 1. 框架与基本对象

设可分希尔伯特空间 $(\mathcal H,\langle\cdot,\cdot\rangle)$，自伴算子对 $(H_0,H)$ 的波算子存在且完备；绝对连续谱上存在可微散射矩阵 $E\mapsto S(E)\in U(N(E))$。定义

$$
\mathsf Q(E)=-i\,S^\dagger(E)\partial_E S(E),\qquad
\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),
$$

并以

$$
\boxed{\ \mathcal E[w]=\int_{\mathbb R}E\,w(E)\,\rho_{\mathrm{rel}}(E)\,dE\ }
$$

作为"能量"的窗化谱定义。单通道 $S(E)=e^{2i\delta(E)}$ 时 $\operatorname{tr}\mathsf Q(E)=2\delta'(E)$，与态密度差之 Friedel 型关系相容（图网络存在局域态修正）。([chaosbook.org][1])

---

## 2. 公理与基本性质

**A1（可观测性）** $\mathcal E[w]$ 仅依赖窗化相对谱测度 $d\mu_w$。

**A2（重参数协变）** 设 $\phi:\mathbb R\to\mathbb R$ 严格单调且 $C^1$。定义窗化相对谱测度

$$
d\mu_w(E):=w(E)\,\rho_{\mathrm{rel}}(E)\,dE,
$$

及其推前 $d\mu_w^\phi:=\phi_* d\mu_w$。则**协变等价式**为

$$
\boxed{\ \mathcal E_S^{(\phi)}[w]:=\int_{\mathbb R}\phi(E)\,d\mu_w(E)
=\int_{\mathbb R}E\,d\mu_w^\phi(E)\ } .
$$

若以密度形式展开（$\phi$ 递增），则

$$
d\mu_w^\phi(E)
=w(\phi^{-1}(E))\,\rho_{\mathrm{rel}}(\phi^{-1}(E))\,(\phi^{-1})'(E)\,dE .
$$

（注：如需与 $S^\phi(E):=S(\phi(E))$ 的记号并行使用，可保持 $S^\phi$ 仅作参数重标，而协变等价式始终经由测度推前给出。）

**A3（通道加性）** $S=S_1\oplus S_2\Rightarrow \rho_{\mathrm{rel}}=\rho_{\mathrm{rel},1}+\rho_{\mathrm{rel},2}\Rightarrow \mathcal E_S[w]=\mathcal E_{S_1}[w]+\mathcal E_{S_2}[w]$。

**A4（正则化延拓）** 若 $S-I\in\mathfrak S_2$，以 Koplienko 谱移函数 $\eta$ 与 $\det_2$ 维持 $\mathcal E[w]$ 的结构与表征。([Department of Mathematics][4])

**A5（空真）** $S\equiv I\Rightarrow \rho_{\mathrm{rel}}\equiv 0 \Rightarrow \mathcal E[w]=0$。

---

## 3. $\log\det$/$\det_2$ 表征与相对迹

**定理 3.1（迹类情形）** 若 $S-I\in\mathfrak S_1$，则

$$
\mathcal E[w]=\frac{1}{2\pi i}\int_{\mathbb R}E\,w(E)\,(\log\det S)'(E)\,dE
= -\int_{\mathbb R}E\,w(E)\,\xi'(E)\,dE .
$$

*证明要点*：由 $(\log\det S)'=\operatorname{tr}(S^{-1}S')=i\,\operatorname{tr}\mathsf Q$ 与 Card-1 直接推出；$\det S=\exp(-2\pi i\,\xi)$ 导出谱移版本。([arXiv][3])

**定理 3.2'（Hilbert–Schmidt 情形，安全表述）** 设 $S(E)-I\in \mathfrak S_2$。则存在 Koplienko 谱移函数 $\eta\in L^1_{\mathrm{loc}}(\mathbb R)$，使对任意 $f\in C_c^2(\mathbb R)$ 有

$$
\mathrm{tr}\!\big(f(H)-f(H_0)-f'(H_0)(H-H_0)\big)=\int_{\mathbb R} f''(E)\,\eta(E)\,dE .
$$

在此框架下，能量泛函仍定义为 $\mathcal E[w]=\int_{\mathbb R}E\,w(E)\,\rho_{\mathrm{rel}}(E)\,dE$。

若进一步满足**附加正则性假设**（例如 $\det_{2}S(E)$ 存在非切边界值且 a.e. 可微），则可定义

$$
\Xi_{2}(E):=\frac{1}{2\pi i}\,\partial_E\log\det_{2}S(E),
$$

并得到与迹类情形结构一致的表达

$$
\boxed{\ \mathcal E[w]=\int_{\mathbb R}E\,w(E)\,\Xi_{2}(E)\,dE\ } .
$$

（说明：上述分层陈述与 BK 型关系在迹类情形保持一致；在 Hilbert–Schmidt 情形则以 Koplienko 迹公式为主，并仅在额外正则性下使用 $\det_2$ 版本。([arxiv.org][10])）

---

## 4. 变分结构与尺度窗族

在约束 $\int w=1$ 下，Gateaux 导数

$$
D\mathcal E[w]\!\cdot\!\delta w=\int_{\mathbb R}E\,\rho_{\mathrm{rel}}(E)\,\delta w(E)\,dE,
$$

驻点满足 $E\,\rho_{\mathrm{rel}}(E)=\lambda$ 于 $w$ 的支集上。尺度窗族

$$
w_\lambda(E)=\lambda^{-1}w\!\left(\tfrac{E}{\lambda}\right),
$$

其方向导数为

$$
\boxed{\ \frac{d}{d\lambda}\mathcal E[w_\lambda]\Big|_{\lambda=1}
=-\int_{\mathbb R}E\,\rho_{\mathrm{rel}}(E)\,\bigl(w(E)+E\,\partial_E w(E)\bigr)\,dE\ }.
$$

---

## 5. 有限阶 Euler–Maclaurin（EM）非渐近误差闭合

对均匀网格 $E_n=E_0+n\Delta$ 的离散近似

$$
\widehat{\mathcal E}=\sum_{n=-R}^{R}E_n\,w(E_n)\,\rho_{\mathrm{rel}}(E_n)\,\Delta ,
$$

令 $f(E)=E\,w(E)\,\rho_{\mathrm{rel}}(E)\in C^p$，均匀网格 $E_n=E_0+n\Delta$ 且 $[a,b]$ 覆盖有效支集，则

$$
\boxed{\
\mathcal E
=\widehat{\mathcal E}
-\frac{\Delta}{2}\bigl(f(a)+f(b)\bigr)
-\frac{B_2}{2!}\Delta^2\bigl(f'(b)-f'(a)\bigr)
-\frac{B_4}{4!}\Delta^4\bigl(f^{(3)}(b)-f^{(3)}(a)\bigr)-\cdots
}
$$

因而，未做端点修正时误差首项为 $O(\Delta)$；当 $f(a)=f(b)=0$（如窗在端点消失）或改用**梯形/中点**等对称规则时，主误差提升为 $O(\Delta^2)$。上述分解仍记作

$$
\Delta_{\mathrm{NPE}}=\Delta_{\mathrm{alias}}+\Delta_{\mathrm{Bernoulli}}+\Delta_{\mathrm{tail}},
$$

该纪律体现"窗越平滑误差越优"的原则，并给出端点主导项的可计算界。([维基百科][2])

---

## 6. 统计与混沌散射刻画

在混沌腔体、量子点与电磁/声学散射中，$\mathsf Q$ 本征值（proper delay times）与 $\operatorname{tr}\mathsf Q$ 的矩与分布可由随机矩阵方法建立，从而为 $\mathcal E[w]$ 提供统计界与置信区间构造准则；含损耗与色散的推广亦已给出。([arXiv][5])

---

## 7. EBOC 嵌入：全观察者集成不变量

EBOC 将读数视为对谱测度的线性泛函。由 Card-1 得

$$
d\mu_w(E)=w(E)\,\rho_{\mathrm{rel}}(E)\,dE
=\frac{w(E)}{\pi}\,\varphi'(E)\,dE
=\frac{w(E)}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE,
$$

能量读数为 $\mathcal E[w]=\int E\,d\mu_w(E)$。对可逆观察变换族 $\Omega$ 定义全局量

$$
\mathcal E_{\mathrm{glob}}:=\int_{\Omega}\mathcal E[w]\,d\Omega(w),
$$

其在能量重参数与窗推前下协变不变，刻画静态块中的"能量—相位—延迟"一致刻度。

---

## 8. RCA 嵌入与 Koopman 谱对应

考虑可逆元胞自动机 $(X,\sigma,T)$ 及其不变测度 $\mu$。Koopman 算子 $U_Tg=g\circ T$ 的谱测度 $\nu_g$ 满足

$$
\langle U_T^n g,g\rangle=\int_{-\pi}^{\pi}e^{in\omega}\,d\nu_g(\omega).
$$

对局部可加"能量密度"观测 $g$，定义离散相位域上的窗化能量

$$
\boxed{\ \mathcal E_{\mathrm{RCA}}[w]=\int_{-\pi}^{\pi}\omega\,w(\omega)\,d\nu_g(\omega)\ }.
$$

Curtis–Hedlund–Lyndon 定理将可逆 CA 刻画为滑动块共轭的连续—移位等变映射；现代 Koopman 理论提供从非线性到线性算子表述的谱工具。存在离散—连续谱变换 $\omega\leftrightarrow E$ 与 Poincaré 截面动力学的可测嵌入时，有 $\mathcal E_{\mathrm{RCA}}[w]\equiv\mathcal E[w]$。([维基百科][6])

---

## 9. 典型情形与实例

1. **单通道相移**：$\mathcal E[w]=\pi^{-1}\int E\,w(E)\,\delta'(E)\,dE$，与 Friedel 求和一致；图网络存在未耦合局域态时需修正局域态密度项。([lptms.universite-paris-saclay.fr][7])

2. **多通道与有耗介质**：$\operatorname{tr}\mathsf Q=\sum_j2\delta'_j(E)$；在色散/损耗体系内可引入校正项并解耦损耗与延迟，由此保持群延迟刻度与能量窗读数的可解释性。([arXiv][8])

3. **电磁/声学实现**：$\mathsf Q$ 可通过 S 参数的频率导数或面/体积分公式稳定估计，并用于模式综合与延迟整形。([arXiv][9])

---

## 10. 主要定理（摘选）

**定理 10.1（重参数协变的一致性）**

对任意严格单调 $C^1$ 的 $\phi$ 均有

$$
\mathcal E_S^{(\phi)}[w]=\int_{\mathbb R}\phi(E)\,d\mu_w(E)
=\int_{\mathbb R}E\,d(\phi_* d\mu_w)(E).
$$

*证：* 推前测度的定义给出 $\int g(E)\,d(\phi_* \mu)(E)=\int g(\phi(E))\,d\mu(E)$。取 $g(E)=E$ 立即得到结论。

**定理 10.2（$\log\det/\det_2$ 表征）**

在 $S-I\in\mathfrak S_1$ 时成立定理 3.1；在 $S-I\in\mathfrak S_2$ 时成立定理 3.2'，且两者在迹类极限上一致。([arXiv][3])

**定理 10.3（有限阶 EM 稳定界——统一表述）**

设 $f(E)=E\,w(E)\,\rho_{\mathrm{rel}}(E)\in C^{p}([a,b])$，均匀网格 $E_n=E_0+n\Delta$ 覆盖有效支集，离散近似取

$$
\widehat{\mathcal E}=\sum_{n=-R}^{R}E_n\,w(E_n)\,\rho_{\mathrm{rel}}(E_n)\,\Delta .
$$

则存在常数 $C_1,\,C_{2k}$（依赖端点导数至阶 $2k-1$），使

$$
\boxed{\ |\mathcal E-\widehat{\mathcal E}|
\;\le\; \tfrac{\Delta}{2}\bigl(|f(a)|+|f(b)|\bigr)
\;+\;\sum_{k=1}^{\lfloor p/2\rfloor} C_{2k}\,\Delta^{2k}\ }.
$$

进一步地，若满足下列任一条件，则首项 $O(\Delta)$ 消失而主阶提升为 $O(\Delta^{2})$：

(i) $f(a)=f(b)=0$（例如窗在端点至少一阶消失）；或

(ii) 采用**梯形/中点**等对称求和规则。

若再有 $f^{(2j-1)}(a)=f^{(2j-1)}(b)=0$ 对 $1\le j\le m$，则主阶提升为 $O(\Delta^{2(m+1)})$。([维基百科][2])

**命题 10.4（WEM–RCA 谱对应）**

当存在 $\omega\leftrightarrow E$ 的谱变换与可测嵌入时，$\mathcal E_{\mathrm{RCA}}[w]\equiv\mathcal E[w]$；其不变性由滑动块共轭与 Koopman 谱测度的自然性保证。([维基百科][6])

---

## 11. 实施细则：估计与误差控制

**群延迟途径**：$\mathsf Q(E_n)\approx -i\,S^\dagger(E_n)\frac{S(E_{n+1})-S(E_{n-1})}{2\Delta}$，$\rho_{\mathrm{rel}}(E_n)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E_n)$。

**$\log\det$ 途径**：直接估计 $(\log\det S)'(E_n)$ 或 $(\log\det_2 S)'(E_n)$ 并积分，常较差分更稳健。

**NPE 闭合**：加入二阶/四阶 Bernoulli 端点校正并估计尾项；在统计场景下结合 $\mathsf Q$ 的矩界给出置信区间。([维基百科][2])

---

## 12. 适用范围与边界

当 $S(E)$ 正则性不足或奇点密集时，应提高窗平滑度并采用 $\log\det$/$\det_2$ 交叉验证；在量子图与缺陷体系中需显式补偿未耦合局域态密度项；在非酉或亚酉散射的广义延时情形下，可通过极点—零点结构与广义群延迟的延拓维持测度—函数结构。上述处理与已知的 Friedel 失效情形相容。([lptms.universite-paris-saclay.fr][7])

---

## 参考要点（主题指引）

Wigner–Smith 群延迟矩阵的原始/多物理场表述与计算；Birman–Kreĭn 公式与谱移函数（含 $\mathfrak S_2$ 正则化）；Euler–Maclaurin 有限阶误差学；量子图情形的 Friedel 规则与失效；Curtis–Hedlund–Lyndon 定理与可逆 CA；Koopman 算子与数据驱动谱方法。([chaosbook.org][1])

[1]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[2]: https://en.wikipedia.org/wiki/Euler%E2%80%93Maclaurin_formula?utm_source=chatgpt.com "Euler–Maclaurin formula"
[3]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[4]: https://web.ma.utexas.edu/mp_arc/c/07/07-127.pdf?utm_source=chatgpt.com "on the koplienko spectral shift function, i. basics"
[5]: https://arxiv.org/abs/2205.07347?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Acoustic Scattering: Theory and Phenomenology"
[6]: https://en.wikipedia.org/wiki/Curtis%E2%80%93Hedlund%E2%80%93Lyndon_theorem?utm_source=chatgpt.com "Curtis–Hedlund–Lyndon theorem"
[7]: https://www.lptms.universite-paris-saclay.fr/ressources/publis/2003/Local%20Friedel%20sum%20rule%20on%20graphs.pdf?utm_source=chatgpt.com "Local Friedel sum rule on graphs"
[8]: https://arxiv.org/pdf/2206.01403?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics"
[9]: https://arxiv.org/abs/2005.03211?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics: Computational Aspects for Radiation and Scattering Analysis"
[10]: https://arxiv.org/pdf/math/9911182?utm_source=chatgpt.com "The spectral shift function and the invariance principle"
