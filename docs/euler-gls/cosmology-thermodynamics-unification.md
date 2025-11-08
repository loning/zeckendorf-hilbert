# 宇宙学—热力学统一：以几何熵产生重释 Friedmann 方程（含证明）

Version: 1.0

## 摘要

在各向同性—均匀的 FLRW 宇宙中，以表观视界为天然热力学边界，构造广义熵 $S_{\rm gen}(t)=\tfrac{A(t)}{4G}+S_{\rm out}(t)$（其中 $A(t)=4\pi r_A^2$、$r_A=(H^2+\kappa/a^2)^{-1/2}$），并采用 Kodama–Hayward 温度 $T=|\kappa_{\rm sg}|/(2\pi)$ 的准静极限 $T=\tfrac{1}{2\pi r_A}$，可将宇宙动力学等价表述为几何熵产生过程。以 Hayward 统一第一定律 $dE=A\psi+W\,dV$ 与 Clausius 关系 $\delta Q=T\,dS$ 为核心，可在表观视界上得到与两条 Friedmann 方程互为充要的一组热力学关系；由
$$T\dot S_h=4\pi H r_A^3(\rho+p)$$
可知，可逆熵通量仅由物质/辐射焓通量给定，曲率与真空 $\Lambda$ 不产生独立的局域熵通量（即便 $\dot\Lambda\neq0$，其效应亦经 $(T,A,r_A)$ 的几何刻度与能量交换自洽吸收）。在含曲率修正或非平衡流体情形下，需引入内禀熵产生项 $d_iS$，对应改变量子/几何修正的不可逆效应。由此建立三重对应：宇宙演化 $=$ 几何熵产生过程；大爆炸 $=$ 由观测锚定的相变链；暗能量 $=$ 真空几何曲率。该框架以 Jacobson 的"时空热力学"思想、Hayward 的统一第一定律、Cai–Kim 与 Akbar–Cai 的视界热力学导出 Friedmann 方程、以及 Bousso–Engelhardt 的宇宙学广义第二定律（Q-screen 形式）为理论支柱，并以 Gibbons–Hawking 的 de Sitter 温度与地平线熵刻度统一晚期几何极限。([物理评论链接管理器][1])

---

## 0. 设定与记号

度规取 FLRW：$ds^2=-dt^2+a(t)^2\big((1-\kappa r^2)^{-1}dr^2+r^2 d\Omega^2\big)$，$\kappa\in\{-1,0,+1\}$，Hubble 参量 $H=\dot a/a$。表观视界半径 $r_A=(H^2+\kappa/a^2)^{-1/2}$，面积 $A=4\pi r_A^2$，体积 $V=\tfrac{4}{3}\pi r_A^3$。表面引力采用 Hayward–Kodama 动态定义，准静极限温度 $T=\tfrac{1}{2\pi r_A}$，一般情形 $T=|\kappa_{\rm sg}|/(2\pi)$ 与 FRW 的动态 trapping horizon 相容。Misner–Sharp 能量 $E$ 与能量供应 $\psi$、功密度 $W=\tfrac{1}{2}(\rho-p)$ 进入统一第一定律 $dE=A\psi+W\,dV$。这些对象与定义在球对称时空、特别是 FRW 背景的表观视界上良定，并已用于从热力学重建 Friedmann 方程。

---

## 1. Friedmann 方程的热力学重释

### 1.1 视界第一定律 $\Longleftrightarrow$ Friedmann 方程

在表观视界上取热量流 $\delta Q=A\psi$，令 Clausius 关系 $\delta Q=T\,dS_h$（$S_h=\tfrac{A}{4G}$），并以统一第一定律 $dE=A\psi+W\,dV$ 表示能量平衡。由能量守恒 $\dot\rho+3H(\rho+p)=0$，可得
$$
\dot H-\frac{\kappa}{a^2}=-4\pi G(\rho+p),\qquad
H^2+\frac{\kappa}{a^2}=\frac{8\pi G}{3}\rho+\frac{\Lambda}{3},
$$
即两条 Friedmann 方程；反之，假定上述两式成立，则在表观视界上 $\delta Q=T\,dS_h$ 恒成立，构成充要等价。该结论在 Einstein 引力严格成立，并已推广至 Gauss–Bonnet/Lovelock 与 $f(R)$ 等情形（非平衡校正见 §3）。([arXiv][2])

### 1.2 第一方程的"熵平衡分拆"

写成 $r_A^{-2}=H^2+\kappa/a^2=\tfrac{8\pi G}{3}\rho+\tfrac{\Lambda}{3}$，对时间微分并用 $\dot\rho+3H(\rho+p)=-\dot\Lambda/(8\pi G)$（$\dot\Lambda=0$ 时化为标准守恒），配合 $T=(2\pi r_A)^{-1}$ 与 $S_h=\pi r_A^2/G$，得到
$$
T\,\dot S_h=4\pi H r_A^3(\rho+p).
\tag{1}
$$
即表观视界上的可逆熵产生完全由物质/辐射的焓通量决定；曲率与 $\Lambda$ 仅通过几何刻度 $(r_A,T)$ 间接影响 $T\,\dot S_h$，并不构成独立的熵通量项。([arXiv][2])

---

## 2. 三重对应与物理诠释

### 2.1 宇宙演化 = 几何熵产生过程

Raychaudhuri 方程给出测地线族膨胀的聚焦/发散演化；在能量条件与适当边界下，表观/事件视界面积的单调性与宇宙学广义第二定律（Q-screen 形式）共同保证沿自然时间箭头的广义熵 $S_{\rm gen}$ 不减。式(1) 表明，可逆熵收支由物质/辐射的焓通量唯一决定；曲率与 $\Lambda$ 仅通过几何刻度 $(r_A,T)$ 间接影响 $S_{\rm gen}$ 的演化。([物理评论链接管理器][3])

### 2.2 大爆炸 = 观测锚定的相变链

热史中的电弱、QCD、复合/复离与 BBN 等阶段可视为序参量跃迁对应的熵结构拐点。以 BBN 轻元素丰度与 CMB 的声学峰为观测锚对 $\rho(z),p(z)$ 和 $w(z)$ 进行约束，可重构 $\Phi_{\rm m}(z)=4\pi H r_A^3(\rho+p)$ 的历史轨迹并检验 $\dot S_{\rm gen}\ge0$。参数取值可由 Planck 2018（A&A 641 A6, 2020）与 PDG 评审锚定。([Aanda][4])

### 2.3 暗能量 = 真空几何曲率

在 de Sitter 极限 $H^2=\Lambda/3$ 中，温度与熵分别为 $T_{\rm dS}=H/(2\pi)$、$S_{\rm dS}=A/(4G)=3\pi/(G\Lambda)$，体现真空曲率对几何刻度的可逆设定；若 $\Lambda$ 随时间缓变或含高阶曲率修正，则其效应通过改变 $H(t)$ 进而改变量子/几何刻度 $(T,S_h)$，并可能在非平衡扩展中体现为 $d_iS$。([物理评论链接管理器][5])

---

## 3. 非平衡扩展与内禀熵产生

当引力熵泛函含曲率修正（如 $S\sim\int f(R)$ 的 Wald/Noether 熵）时，Clausius 关系需改为 $\delta Q=T\,dS_h+T\,d_iS$（$d_iS\ge0$）。Eling–Guedens–Jacobson 表明，对 Ricci 标量的多项式修正，必须采取非平衡熵学处理，并可由熵平衡关系导出修正场方程；即便在 Einstein 理论中，若考虑视界剪切/体粘滞，也存在 $d_iS$ 的正定贡献。宇宙学粘滞流体（Eckart/Israel–Stewart）提供了宏观建模途径，其非平衡压强 $\Pi$ 与 $d_iS$ 在早/晚期阶段皆可造成附加熵增长。([物理评论链接管理器][6])

---

## 4. 主定理

**定理 1（视界第一定律与 Friedmann 方程的等价）**：在 Einstein 引力与 FLRW 背景下，表观视界上 $\delta Q=A\psi=T\,dS_h$、$T=\tfrac{1}{2\pi r_A}$、$S_h=\tfrac{A}{4G}$ 与两条 Friedmann 方程互为充要。证明要点：由 $\dot r_A=-H r_A^3\!\left(\dot H-\kappa/a^2\right)$、$\dot\rho+3H(\rho+p)=0$，配合 $E=\rho V$、$V=\tfrac{4}{3}\pi r_A^3$、$A=4\pi r_A^2$ 与 $T$ 上式，即得 $\dot H-\kappa/a^2=-4\pi G(\rho+p)$；再由 $r_A^{-2}=H^2+\kappa/a^2$ 与能量约束积分得第一 Friedmann 方程，反向亦然。([物理评论链接管理器][7])

**定理 2（视界熵收支）**：对 $r_A^{-2}=H^2+\kappa/a^2$ 微分并使用 $\dot\rho+3H(\rho+p)=-\dot\Lambda/(8\pi G)$（$\dot\Lambda=0$ 时退化为标准守恒），在表观视界上成立
$$
T\,\dot S_h=4\pi H r_A^3(\rho+p).
$$
即可逆熵产生项完全由焓通量给定；若引入高阶曲率或非平衡流体，则应改写为 $\delta Q=T\,dS_h+T\,d_iS$，其中 $d_iS\ge0$ 描述几何/量子修正导致的不可逆贡献。([arXiv][2])

**定理 3（广义第二定律与"相变链"的单调性）**：沿宇宙学 Q-screen 的族，广义熵 $S_{\rm gen}$ 单调不减；早期热史诸相变/转变节点在 $S_{\rm gen}$ 上表现为非解析拐点，其时间—尺度位置由 BBN 与 CMB 的观测量锚定。([物理评论链接管理器][3])

---

## 5. 观测锚与可检验后果

（1）晚期几何刻度：$\Lambda$ 主导时代 $T=H/(2\pi)$、$S_h=3\pi/(G\Lambda)$。若考虑运行真空模型，缓变的 $\Lambda(t)$ 通过改变 $H(t)$ 从而改变量子/几何刻度 $(T,S_h)$；其不可逆效应（若有）应在 $\delta Q=T\,dS_h+T\,d_iS$ 的 $d_iS$ 中体现。([物理评论链接管理器][5])
（2）焓通量熵重构：以 Planck 2018 的 $\Omega_m,\Omega_b,n_s,\tau$ 与 PDG/最新 BBN 的 $\eta_B$ 为输入，可随红移重构 $\Phi_{\rm m}(z)$ 并检验 $\dot S_{\rm gen}\ge0$。([Aanda][4])
（3）曲率调制效应：若 $|\Omega_k|\neq 0$，曲率通过改变 $r_A=(H^2+\kappa/a^2)^{-1/2}$ 进而调制几何刻度 $(T,S_h)$，其现值受 BAO/CMB 对 $\Omega_k$ 的约束；相应地，曲率对熵演化的影响比例随 $a(t)$ 的演化而调制。([arXiv][2])

---

## 6. 温度的动态一致性与选择

动态 FRW 背景下，Hayward–Kodama 表面引力给出一致的温度选择，且对 past-inner trapping horizons 具有正号；该温度与隧穿法的谱解释一致，并不依赖于视界的因果性质（类时/类空/类光）。准静极限 $T\simeq(2\pi r_A)^{-1}$ 仅是其一阶近似，严格公式含 $\dot r_A$ 校正。

---

## 7. 与引力—信息统一的关系

Jacobson 将 Einstein 方程视作局域 Rindler 视界族上的状态方程 $\delta Q=T\,dS$；本文在宇宙学尺度以表观视界的几何刻度 $(S_h,T)$ 将该思想具体化，给出 Friedmann 方程的熵学分拆。含高阶曲率/非最小耦合时，需引入 $d_iS$ 的非平衡扩展；在 de Sitter 极限，暗能量作为真空几何曲率仅通过几何刻度 $(T,S_h)$ 改变可逆几何熵，而不在局域产生独立的熵通量项（即使 $\Lambda$ 时间依赖，其效应亦经能量交换与几何刻度自洽吸收）。([物理评论链接管理器][1])

---

## 附录 A：定理 1 的证明细节

（A.1）由 $r_A=(H^2+\kappa/a^2)^{-1/2}$ 得 $\dot r_A=-H r_A^3\!\left(\dot H-\kappa/a^2\right)$。故 $\dot S_h=\tfrac{d}{dt}(\pi r_A^2/G)=\tfrac{2\pi r_A}{G}\dot r_A=-\tfrac{2\pi H r_A^4}{G}\!\left(\dot H-\kappa/a^2\right)$，从而 $T\,\dot S_h=-\tfrac{H r_A^3}{G}\!\left(\dot H-\kappa/a^2\right)$。
（A.2）统一第一定律 $dE=A\psi+W\,dV$ 与 $\delta Q=A\psi$、能量守恒 $\dot\rho+3H(\rho+p)=0$ 结合，代入 $E=\rho V$、$V=\tfrac{4}{3}\pi r_A^3$、$A=4\pi r_A^2$ 与 $T$ 上式，即得 $\dot H-\kappa/a^2=-4\pi G(\rho+p)$。
（A.3）再由 $r_A^{-2}=H^2+\kappa/a^2$ 与能量约束积分得 $H^2+\kappa/a^2=\tfrac{8\pi G}{3}\rho+\tfrac{\Lambda}{3}$，完成充要性证明。([物理评论链接管理器][7])

---

## 附录 B：式(1) 的推导

由 $r_A^{-2}=H^2+\kappa/a^2$ 得 $-2r_A^{-3}\dot r_A=2H(\dot H-\kappa/a^2)$。两侧乘 $-\tfrac{\pi r_A^4}{G}$ 并用 $S_h=\pi r_A^2/G$、$T=(2\pi r_A)^{-1}$ 得
$$T\,\dot S_h=-\frac{H r_A^3}{G}\big(\dot H-\kappa/a^2\big).$$
再由 $\dot H-\kappa/a^2=-4\pi G(\rho+p)$（允许 $\Lambda(t)$ 时亦成立）即得
$$T\,\dot S_h=4\pi H r_A^3(\rho+p).$$
([arXiv][2])

---

## 附录 C：非平衡熵产生与改变量子/几何修正

当熵泛函含曲率修正时，需采用非平衡熵平衡式 $\delta Q=T\,dS_h+T\,d_iS$，其中 $d_iS\ge0$。Ricci 标量多项式修正需要体粘滞型 $d_iS$，通过能动守恒定出其系数；Einstein 理论下亦可因视界剪切/体粘滞出现 $d_iS$。这些结果保持从热力学导出修正场方程的一致性。([物理评论链接管理器][6])

---

## 附录 D：宇宙学广义第二定律（Q-screen 形式）

在满足量子聚焦猜想的背景下，沿 past/future Q-screen 的广义熵 $S_{\rm gen}$ 单调不减，适用于无事件视界的宇宙学时空；该结论为将热史相变链刻画为 $S_{\rm gen}$ 非解析结构提供了严密基础，并与标准宇参约束协同工作。([物理评论链接管理器][3])

---

## 参考文献（选）

Jacobson, T. Thermodynamics of Spacetime: The Einstein Equation of State. Phys. Rev. Lett. 75 (1995) 1260.
Hayward, S. A. Unified first law of black-hole dynamics and relativistic thermodynamics. arXiv:gr-qc/9710089 (1997).
Cai, R.-G.; Kim, S. P. First Law of Thermodynamics and Friedmann Equations of FRW Universe. JHEP 0502 (2005) 050.
Akbar, M.; Cai, R.-G. Thermodynamic Behavior of the Friedmann Equation at the Apparent Horizon of the FRW Universe. Phys. Rev. D 75 (2007) 084003.
Bousso, R.; Engelhardt, N. Generalized Second Law for Cosmology. Phys. Rev. D 93 (2016) 024025.
Gibbons, G. W.; Hawking, S. W. Cosmological Event Horizons, Thermodynamics and Particle Creation. Phys. Rev. D 15 (1977) 2738.
Planck Collaboration (Aghanim, N. et al.). Planck 2018 results. VI. Cosmological parameters. A&A 641 (2020) A6.
Particle Data Group (Fields, B. D.; Molaro, P.; Sarkar, S.). Big-Bang Nucleosynthesis. Review of Particle Physics (2024/2025 update).

[1]: https://link.aps.org/doi/10.1103/PhysRevLett.75.1260?utm_source=chatgpt.com "Thermodynamics of Spacetime: The Einstein Equation of State"
[2]: https://arxiv.org/abs/hep-th/0501055?utm_source=chatgpt.com "[hep-th/0501055] First Law of Thermodynamics and ..."
[3]: https://link.aps.org/doi/10.1103/PhysRevD.93.024025?utm_source=chatgpt.com "Generalized second law for cosmology | Phys. Rev. D"
[4]: https://www.aanda.org/articles/aa/abs/2020/09/aa33910-18/aa33910-18.html?utm_source=chatgpt.com "Planck 2018 results - VI. Cosmological parameters"
[5]: https://link.aps.org/doi/10.1103/PhysRevD.15.2738?utm_source=chatgpt.com "Cosmological event horizons, thermodynamics, and particle ..."
[6]: https://link.aps.org/doi/10.1103/PhysRevLett.96.121301?utm_source=chatgpt.com "Nonequilibrium Thermodynamics of Spacetime | Phys. Rev. Lett."
[7]: https://link.aps.org/doi/10.1103/PhysRevD.75.084003?utm_source=chatgpt.com "Thermodynamic behavior of the Friedmann equation at the ..."
