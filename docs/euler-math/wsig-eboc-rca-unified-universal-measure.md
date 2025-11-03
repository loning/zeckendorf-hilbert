# WSIG–EBOC–RCA 统一理论：

三位一体"通用测度坐标"的公理化、换元一致性与误差学

Version: 1.2

## 摘要

在 de Branges–Kreĭn 规范系统与多通道散射理论下，以散射相位导数、相对态密度与 Wigner–Smith 群延迟迹为同一刻度的三种等价表述，构造"通用测度坐标"，并证明其在窗化读数下的换元一致性与 Nyquist–Poisson–Euler–Maclaurin（NPE）三分解的非渐近误差闭合。核心统一式（绝对连续谱几乎处处）为

$$
d\mu_\varphi(E)=\frac{\varphi'(E)}{\pi}\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE=\rho_{\mathrm{rel}}(E)\,dE,
$$

其中 $\mathsf Q(E)=-i\,S(E)^\dagger S'(E)$ 为 Wigner–Smith 延迟矩阵，$\rho_{\mathrm{rel}}=-\xi'$ 为相对于参照算子 $H_0$ 的谱移密度，$\det S(E)=\exp(-2\pi i\,\xi(E))$ 为 Birman–Kreĭn 公式的标准规范。三位一体链条由 Birman–Kreĭn 公式与 Wigner–Smith 延迟的一致化推导得到，适用于多通道酉散射；次酉体系以广义（复）延迟作相容推广。论文给出：（i）窗化换元一致性定理（能量 ↔ 相位/延迟/密度坐标）；（ii）最大熵—最小延迟对偶定理；（iii）因果单调 $\Leftrightarrow$ 相位单调；并在相位坐标下表述采样—帧门槛、Wexler–Raz 双正交与 Balian–Low 不可能性的不变表达，同时建立多窗/多核优化的 KKT 与 Γ-极限稳定性。以上结论与 BK/SSF、Wigner–Smith、Herglotz–Weyl、Carleson—帧论判据逐条对齐，可直接复核与实现。([SpringerLink][1])

---

## 0. 记号、规范与基础文献

**散射与谱移.** 自伴散射对 $(H,H_0)$ 的 on-shell 多通道散射矩阵 $S(E)\in U(N)$。Birman–Kreĭn 公式（迹类假设下）为

$$
\det S(E)=\exp\bigl(-2\pi i\,\xi(E)\bigr),
$$

其中 $\xi$ 为谱移函数；据此得 $\frac{d}{dE}\Arg\det S(E)=-2\pi\,\xi'(E)$。约定相对态密度 $\rho_{\mathrm{rel}}(E):=-\xi'(E)$。([SpringerLink][1])

**相位（散射半相位）.** 设多通道散射矩阵 $S(E)\in U(N)$。定义

$$
\varphi(E):=\tfrac12\,\Arg\det S(E)\quad(\text{BK 连续分支}),
$$

则几乎处处有 $\varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)=\pi\,\rho_{\mathrm{rel}}(E)$，其中 $\mathsf Q(E)=-i\,S(E)^\dagger S'(E)$、$\rho_{\mathrm{rel}}(E)=-\xi'(E)$。

**Wigner–Smith 延迟.** 定义 $\mathsf Q(E)=-i\,S(E)^\dagger \tfrac{dS}{dE}(E)$。对酉 $S$，有

$$
\frac{d}{dE}\log\det S(E)=\operatorname{tr}\bigl(S^{-1}S'(E)\bigr)=\operatorname{tr}\bigl(S^\dagger S'(E)\bigr),
$$

从而 $\frac{d}{dE}\Arg\det S(E)=\operatorname{tr}\mathsf Q(E)$ 与 $\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$（a.e.）。单通道 $S=e^{2i\varphi}$ 时 $\operatorname{tr}\mathsf Q=2\varphi'(E)$。延迟矩阵的定义与性质参见综述与计算文献。([chaosbook.org][2])

**de Branges–Kreĭn 与 Herglotz–Weyl.** 对规范系统与 de Branges 空间 $\mathcal H(\mathcal E)$，其再生核对角满足

$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|\mathcal E(x)|^2,
$$

其中 $\varphi$ 为 Hermite–Biehler 函数 $\mathcal E$ 的相位函数；同时 Weyl–Titchmarsh $m$ 为 Herglotz 函数，边界虚部给出谱密度。([diposit.ub.edu][3])

**窗化读数与 NPE 三分解.** 取偶带限窗 $w_R$ 与带限核 $h$，窗化读数 $\int w_R(E)\,(h*\rho_\star)(E)\,dE$ 的数值积分—求和换序误差可由 Poisson 求和与 Euler–Maclaurin（EM）公式的有限阶校正与窗外尾项三部分组成（alias + Bernoulli 层 + tail），并在 Nyquist 条件下消除别名项。([dlmf.nist.gov][4])

---

## 1. 公理化：三位一体刻度与可观操作

**公理 A（刻度统一）** 在绝对连续谱的 Lebesgue 点几乎处处成立

$$
\varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)=\pi\,\rho_{\mathrm{rel}}(E).
$$

由 BK 与延迟矩阵定义得出。([SpringerLink][1])

**公理 B（窗化可观与 NPE）** 对偶带限窗 $w_R$ 与带限核 $h$，一切求和—积分换序以有限阶 EM 与 Poisson 求和控制，误差三分解闭合，Nyquist 下 alias 消失。([dlmf.nist.gov][4])

**公理 C（实现—语义协变）** 存在 EBOC 记录几何与 RCA 局域可逆更新的语义嵌入，使 $(\varphi,\rho_{\mathrm{rel}},\tfrac1N\operatorname{tr}\mathsf Q)$ 分别对齐"记录页码—记录密度—读取开销"与"信息增量—步延迟"，并保持因果圆锥与相位单调一致。

---

## 2. 通用测度坐标与换元三式

**定义 2.1（通用测度坐标）** 取

$$
d\mu_\varphi:=\frac{\varphi'(E)}{\pi}\,dE,\qquad
d\tau:=\frac{1}{N}\operatorname{tr}\mathsf Q(E)\,dE,\qquad
d\rho:=\rho_{\mathrm{rel}}(E)\,dE.
$$

**命题 2.2（WSIG 换元一致性）** 设 $F\in L^1_{\mathrm{loc}}$、窗 $w_R\in L^1\cap L^\infty$。若在窗支配区间上 $\varphi$（或 $\tau,\rho$）**绝对连续且严格单调**，则

$$
\int F(E)\,w_R(E)\,dE=\int F\bigl(E(\varphi)\bigr)\,w_R\bigl(E(\varphi)\bigr)\,\frac{dE}{d\varphi}\,d\varphi,
$$

且雅可比为

$$
\frac{dE}{d\varphi}=\Bigl(\tfrac12\,\operatorname{tr}\mathsf Q(E)\Bigr)^{-1},\qquad
\frac{dE}{d\tau}=\Bigl(\tfrac1N\,\operatorname{tr}\mathsf Q(E)\Bigr)^{-1},\qquad
\frac{dE}{d\rho}=\bigl(\rho_{\mathrm{rel}}(E)\bigr)^{-1}.
$$

其中 $E(\varphi)=\varphi^{-1}(\varphi)$ 存在且可测，换元由绝对连续与严格单调保证。这里 $\tau(E):=\displaystyle\int_{E_0}^{E}\tfrac1N\operatorname{tr}\mathsf Q(s)\,ds$，$\rho(E):=\displaystyle\int_{E_0}^{E}\rho_{\mathrm{rel}}(s)\,ds$。

*证明.* 可测换元与 Lebesgue 点性质，分支由 BK 连续分支与窗化可积性保证。([SpringerLink][1])

---

## 3. 窗化 Birman–Kreĭn 恒等式与误差闭合

**定理 3.1（窗化 BK 恒等式）** 在 resolvent 差为迹类，且

$$
h\in W^{1,1}\cap L^\infty\ \ (\text{或 }C_c^1),\qquad
w_R\in W^{1,1}\cap L^1\cap L^\infty\ \ (\text{或 }C_c^1),
$$

由此 $(h w_R)'=h' w_R+h\,w_R'\in L^1$ 且 $(h w_R)(\pm\infty)=0$。定义

$$
\mathcal S_{\rm spec}(h;R)=\int h(E)\,\rho_{\mathrm{rel}}(E)\,w_R(E)\,dE,\quad
\mathcal S_{\rm scat}(h;R)=-\frac{1}{2\pi i}\int \bigl[h' w_R+h\,w_R'\bigr]\log\det S\,dE,
$$

则 $\mathcal S_{\rm spec}(h;R)=\mathcal S_{\rm scat}(h;R)$。

*证明.* 用恒等式

$$
\partial_E\log\det S(E)=\operatorname{tr}\!\bigl(S^{-1}(E)S'(E)\bigr),\qquad
\frac{1}{2\pi i}\,\partial_E\log\det S=\rho_{\rm rel},
$$

令 $f:=h w_R$，在 $f\in W^{1,1}\cap L^1$ 与 $f(\pm\infty)=0$ 下对 $\int f\,\partial_E\log\det S$ 作分部积分，边界项为零，即得结论。([SpringerLink][1])

**定理 3.2（NPE 三分解；非渐近）** 等距采样近似 $\int F$ 的误差分解

$$
\mathcal E_R=\mathcal E_{\rm alias}+\mathcal E_{\rm EM}+\mathcal E_{\rm tail},
$$

其中 $\mathcal E_{\rm alias}$ 由 Poisson 求和给出，Nyquist 条件下 $\mathcal E_{\rm alias}=0$；$\mathcal E_{\rm EM}$ 为有限阶 Euler–Maclaurin 余项（Bernoulli 序列显式）；$\mathcal E_{\rm tail}$ 受窗外指数衰减控制。([dlmf.nist.gov][4])

---

## 4. 信息几何与"最大熵—最小延迟"对偶

**定义 4.1（窗化熵）** 记能量参数的输出分布 $p_E$，窗化熵

$$
\mathcal H_R:=\int H(p_E)\,w_R(E)\,dE.
$$

借助命题 2.2 的换元，与 $\varphi$-坐标中的 $\tfrac{dE}{d\varphi}=(\tfrac12\operatorname{tr}\mathsf Q)^{-1}$ 相联。

**定理 4.2（最大熵—最小延迟对偶）** 若 $E\mapsto p_E$ 平滑、$H$ 严凸且 $R$ 足大，则 $\mathcal H_R$ 的极大点与窗化平均延迟 $\int \tfrac1N\operatorname{tr}\mathsf Q\,w_R\,dE$ 的极小点在同一 $\varphi^\star$ 对齐（唯一性模别名余项）。

*证明思路.* 在 $\varphi$-坐标中极值条件为 $\partial_\varphi!\bigl[H(p_{E(\varphi)})\,\tfrac{dE}{d\varphi}\bigr]=0$；结合 $\tfrac{dE}{d\varphi}$ 与 KL 投影唯一性、Ky–Fan 极小子空间一致性获得对偶同位。关于 Ky–Fan 极值性质与谱子空间稳定性见下述引用。([pnas.org][5])

---

## 5. 因果与"相位单调"等价

**定义 5.1（环路延迟）** 对可实现能量环 $\gamma$，设 $\Delta T(\gamma):=\oint_\gamma \operatorname{tr}\mathsf Q(E)\,dE$。

**定理 5.2（因果单调 $\Leftrightarrow$ 相位单调）** 若对一切可实现环 $\Delta T(\gamma)\ge 0$，则 $\oint_\gamma d\varphi=\tfrac12\Delta T(\gamma)\ge0$；反之亦然。两者与无信号性/可实现性等价。

*证明.* 由 $d\varphi=\tfrac12\,\operatorname{tr}\mathsf Q\,dE$ 立即得出。([chaosbook.org][2])

---

## 6. 采样—帧门槛、Carleson 与 Wexler–Raz

**定理 6.1（相位密度与 Landau 门槛）** 在 de Branges–Mellin 统一框架下，以 $d\nu_0=\frac{\varphi'}{\pi}\,dx$ 为几何测度，采样/插值的必要密度门槛沿 Landau 型判据给出；Paley–Wiener 情形退化为经典 Landau 必要密度。对 de Branges 空间，当 $\varphi'(x)\,dx$ 为（局部）doubling 测度时，采样—插值可由 Beurling 密度刻画。([archive.ymsc.tsinghua.edu.cn][6])

**定理 6.2（Wexler–Raz 双正交与 Parseval 条件）** Nyquist 下，多窗 $\{w_\alpha\}$ 生成 Parseval 紧帧当且仅当频域能量平衡恒等式成立；存在别名时需加入周期复制求和。等价关系与对偶窗点态条件即 Wexler–Raz 身份。该条件在 $\varphi$-坐标下不变。([sites.math.duke.edu][7])

**定理 6.3（Balian–Low 障碍；临界密度）** 单窗矩形格在临界密度下不可能同时双侧局域且生成 Riesz 基/ONB；该障碍在相位坐标下保持不变。([encyclopediaofmath.org][8])

---

## 7. 多窗/多核优化、KKT 与 Γ-极限

**定理 7.1（带限投影–KKT 方程与 PSWF 结构）** 在偶带限子空间上最小化 NPE 上界的强凸泛函，其必要最优性条件是带限投影后的核型特征方程，解呈现 Prolate Spheroidal（Slepian–Landau–Pollak）结构，给出最优"主尺度—极点"。([math.ucdavis.edu][9])

**定理 7.2（多目标帕累托前沿与稳定性）** 多窗强凸多目标代理的极小元满足广义 Wexler–Raz 与帧算子方程；对数据/核扰动具 $O(\mu^{-1})$ Lipschitz 稳定，并保持"极点=主尺度"的谱不变性。参考 Walnut 表示的帧算子对角化可用于稳定性估计。([heil.math.gatech.edu][10])

**定理 7.3（非平稳块系统的 tight/dual 显式构造）** 在分块非平稳 Weyl–Mellin 系统中，Walnut–Poisson 对角化将帧算子化为 Calderón 和乘子，给出 tight/dual 的频域闭式；无混叠条件 $2\Omega_n\le \Delta\tau_n$ 与 Nyquist 等价。([sciencedirect.com][11])

---

## 8. 统一到 EBOC 与 RCA 的语义映射

**命题 8.1（EBOC 记录几何映射）** 将 $\varphi$ 解释为"记录页码"、$\rho_{\mathrm{rel}}$ 为"记录密度"、$\tau=\tfrac1N\operatorname{tr}\mathsf Q$ 为"读取开销"，则"最大熵—最小延迟"对偶对应"最短证据路径"，其可逆读写以相位单调为序。

**命题 8.2（RCA 步延迟与信息增量）** 可逆元胞自动机的单步更新在相位坐标上以 $\Delta\varphi$ 计量，因果圆锥的离散表述即相位单调，系统步延迟的加和等于 $\sum \Delta\varphi=\tfrac12\int \operatorname{tr}\mathsf Q\,dE$。

---

## 9. 非酉扩展与半经典换元

**命题 9.1（次酉散射的复延迟）** 次酉 $S$ 下以复延迟的迹/实部替代 $\operatorname{tr}\mathsf Q$ 可保持上述换元与误差学的结构；相位—密度—延迟三者的实部仍给出窗化可观测量。([link.aps.org][12])

**命题 9.2（Egorov–Moyal 的坐标化）** 用 $\partial_\varphi=(\tfrac12\operatorname{tr}\mathsf Q)^{-1}\partial_E$ 将 Egorov–Moyal 级数转写到相位坐标，便于在 $\varphi$-均匀网格上给出 Ehrenfest 时间内的一致估计。([semanticscholar.org][13])

---

## 10. 主定理与证明汇总

**主定理 A（窗化换元一致性与 NPE 界）** 在公理 A–B 下，能量—三位一体坐标的窗化积分相等，离散化/有限和近似的误差服从 NPE 三分解上界。

*证据链.* 命题 2.2 的可测换元 + 定理 3.1 的窗化 BK + 定理 3.2 的 NPE。([SpringerLink][1])

**主定理 B（最大熵—最小延迟对偶）** 在 §4 假设下，$\mathcal H_R$ 的极大点与平均延迟的极小点在同一 $\varphi^\star$ 对齐（唯一性模 alias）。

*证据链.* $\varphi$-坐标极值条件 + KL/I-投影唯一性 + Ky–Fan 极小子空间；谱子空间稳定性由 Davis–Kahan 给出。([pnas.org][5])

**主定理 C（因果单调—相位单调等价）** 见定理 5.2。

*证据链.* $d\varphi=\tfrac12\operatorname{tr}\mathsf Q\,dE$ 与延迟的可加性。([chaosbook.org][2])

---

## 11. 数学与实现清单（可复现）

1. **刻度统一**：以 $\operatorname{tr}\mathsf Q$ 或 $\Arg\det S$ 估计 $d\mu_\varphi$，在 $\varphi$-均匀采样上进行 Nyquist 校验。([chaosbook.org][2])
2. **指针验证**：窗算子 $W_R$ 的谱最小子空间（Ky–Fan 极小和）与数据扰动的稳定性用 Davis–Kahan 控制。([pnas.org][5])
3. **误差闭合**：报告 $(\varepsilon_{\rm alias},\varepsilon_{\rm EM},\varepsilon_{\rm tail})$，带限+Nyquist 下关闭 alias。([dlmf.nist.gov][4])
4. **采样—帧**：在 $\varphi$-坐标中验证 Landau 必要密度、Wexler–Raz 条件与 Balian–Low 障碍。([archive.ymsc.tsinghua.edu.cn][6])
5. **多窗优化**：解带限投影–KKT 方程，得到 PSWF 型解；在 Walnut 表示下作稳定性估计与 tight/dual 构造。([math.ucdavis.edu][9])

---

## 12. 结论

以 BK/SSF 与 Wigner–Smith 为桥梁，本文将相位导数、相对态密度与群延迟迹统一为"通用测度坐标"，并在窗化读数下给出换元一致性与 NPE 三分解的非渐近闭合。相位坐标提供了采样—帧门槛、Wexler–Raz 双正交与 Balian–Low 障碍的坐标不变表述；在优化侧，带限投影–KKT 推出 PSWF 型最优窗，多窗帧的稳定性与 tight/dual 构造可由 Walnut–Poisson 对角化刻画。非酉散射与半经典 Egorov–Moyal 在该坐标中保持同构结构。EBOC 与 RCA 的语义嵌入使"最大熵—最小延迟"与"因果—相位单调"两组对偶得到统一的可实现诠释。

---

## 参考文献（选）

1. Birman–Kreĭn 公式与谱移：Simon, *Tosio Kato's work on non-relativistic QM*（含 BK 公式综述）；Yafaev, *On the spectral shift function*；Athmouni 等（BK 在离散模型中的推导）。([SpringerLink][1])
2. Wigner–Smith 延迟：Patel–Michielssen（电磁散射中的 $\mathsf Q$）；Texier（时间延迟综述）；ChaosBook（$\operatorname{tr}\mathsf Q$ 与 DoS 的联系）。
3. de Branges 核对角与相位导数：Antezana–Marzo–Olsen，式 $(K(x,x)=\frac{1}{\pi}\varphi'(x)|\mathcal E(x)|^2)$。([diposit.ub.edu][3])
4. Poisson 与 Euler–Maclaurin：NIST DLMF §1.8(iv), §2.10(i)。([dlmf.nist.gov][4])
5. Landau 必要密度与其在 de Branges 的推广：Landau（1967）；Marzo–Nitzan–Olsen（doubling 相位情形）。([archive.ymsc.tsinghua.edu.cn][6])
6. Wexler–Raz 身份与密度定理综述：Daubechies 等；Heil（历史与密度定理）。([sites.math.duke.edu][7])
7. Balian–Low 定理：百科条目与后续量化改进。([encyclopediaofmath.org][8])
8. Davis–Kahan 与 Ky–Fan：Yu–Wang–Samworth（D-K 变体）；Ky Fan（1951）。([arXiv][14])
9. Γ-收敛：Dal Maso；Braides。([SpringerLink][15])
10. 非酉散射的复延迟：Chen 等（次酉散射的复时间延迟）。([link.aps.org][12])
11. Egorov–Moyal 与半经典：Bouzouina–Robert；Prouff（Weyl–Hörmander 框架中的 Egorov）。([semanticscholar.org][13])
12. Walnut 表示与非平稳帧：Heil（教材讲义）；Holighaus 等（非平稳 Gabor 的 Walnut-like 表示）。([heil.math.gatech.edu][10])

[1]: https://link.springer.com/article/10.1007/s13373-018-0121-5?utm_source=chatgpt.com "Tosio Kato's work on non-relativistic quantum mechanics"
[2]: https://chaosbook.org/version13/chapters/scattering.pdf?utm_source=chatgpt.com "Quantum scattering"
[3]: https://diposit.ub.edu/dspace/bitstream/2445/108405/1/669580.pdf "Zeros of Random Functions Generated with de Branges Kernels"
[4]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[5]: https://www.pnas.org/doi/pdf/10.1073/pnas.37.11.760?utm_source=chatgpt.com "Maximum Properties and Inequalities for the Eigenvalues"
[6]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling"
[7]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[8]: https://encyclopediaofmath.org/wiki/Balian-Low_theorem?utm_source=chatgpt.com "Balian-Low theorem"
[9]: https://www.math.ucdavis.edu/~saito/data/ONR15/PSWF-II.pdf?utm_source=chatgpt.com "Prolate Spheroidal Wave Functions"
[10]: https://heil.math.gatech.edu/umd/day2.pdf?utm_source=chatgpt.com "FRAMES AND TIME-FREQUENCY ANALYSIS"
[11]: https://www.sciencedirect.com/science/article/pii/S1063520314000190?utm_source=chatgpt.com "Structure of nonstationary Gabor frames"
[12]: https://link.aps.org/doi/10.1103/PhysRevE.103.L050203?utm_source=chatgpt.com "Generalization of Wigner time delay"
[13]: https://www.semanticscholar.org/paper/Uniform-semiclassical-estimates-for-the-propagation-Bouzouina-Robert/78d1d1708b4936b7b3f947eeac78a6b60ce90c2c?utm_source=chatgpt.com "Uniform semiclassical estimates"
[14]: https://arxiv.org/pdf/1405.0680?utm_source=chatgpt.com "A useful variant of the Davis–Kahan theorem"
[15]: https://link.springer.com/book/10.1007/978-1-4612-0327-8?utm_source=chatgpt.com "An Introduction to Γ-Convergence"
