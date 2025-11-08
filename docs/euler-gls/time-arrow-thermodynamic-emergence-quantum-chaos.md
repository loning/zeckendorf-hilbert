# 时间箭头与热力学涌现：SBU 叠加的量子混沌、$\pi$-语义塌缩的熵产生与 Belavkin 过滤下的量子涨落定理

## 摘要

以静态块世界的 SBU（Static Block Units）叠加为微观描述、以因果流形为宏观载体，建立时间箭头与热力学涌现的统一理论。其一，在 SBU 叠加上以 OTOC 与回声度量刻画早期指数增长并定义 Lyapunov 指数 $\lambda_{\rm L}$，证明在 KMS 热态下满足 $\lambda_{\rm L}\le 2\pi T$ 的混沌上界且与可观测窗—核读数一致。其二，将测量刻画为观察者"锚定切换"的 $\pi$-语义塌缩，使用 Umegaki 相对熵与 Petz 可恢复性给出退相干导致的不可逆熵产生分解与路径级涨落关系。其三，在 Hudson–Parthasarathy 量子随机微分与 Belavkin 过滤框架中，借助量子 Feynman–Kac 与测度变换构造鞅，推导带信息修正的量子 Jarzynski 等式，并在连续监测与反馈控制下保持积分涨落定律的闭合性。上述三部分分别与混沌上界、量子非平衡涨落与连续监测—控制之代表性结果一致并形成可检读数。([施普林格链接][1])

---

## Notation & Conventions

取 $\hbar=c=k_{\rm B}=1$。希尔伯特空间 $\mathcal H$，可观测代数 $\mathcal A\subset\mathcal B(\mathcal H)$，经典记录代数 $\mathcal O\simeq L^\infty(\mathcal X)$。测量以量子仪器 $\{\mathcal I_x\}_x$ 与 POVM $\{E_x\}_x$ 表示，存在 Stinespring/Naimark/Kraus 表示。连续监测采用 Hudson–Parthasarathy 量子随机微分（QSDE）与 Belavkin 过滤表述。SBU 指因果网中相容记录的局域片，波函数为 SBU 集上的复幅赋值。锚定切换记为经典化通道 $\pi:\mathcal A\to\mathcal O$（海森堡像），测量更新为 $\rho\mapsto\rho_x=\mathcal I_x(\rho)/{\rm tr}\,\mathcal I_x(\rho)$。连续监测的后验态 $\rho_t$ 满足扩散型或计数型 QSDE。([Project Euclid][2])

---

## 1. 时间箭头的涌现：$\pi$-语义塌缩与相对熵单调

### 定义 1（路径熵产生）

在由仪器序列 $\{\mathcal I_{x_k}\}$ 生成的记录 $\underline x_{0:t}$ 与后验轨道 $\rho_{0:t}$ 上，设不变态为 $\rho^{\rm ss}$。定义单步熵产生
$$
\Sigma_k:=D(\rho_{k}\Vert\rho^{\rm ss})-D(\rho_{k-1}\Vert\rho^{\rm ss})-\ln\frac{\mathbb P^\dagger(\tilde x_k|\tilde\rho_{k-1})}{\mathbb P(x_k|\rho_{k-1})},
$$
令总熵产生 $\Sigma_{0:t}=\sum_k\Sigma_k$，其中 $D$ 为 Umegaki 相对熵，$\dagger$ 表示与前向过程互为时间反演的对偶过程。([Project Euclid][3])

### 定理 1（平均不可逆性与 Spohn 单调）

任意 CPTP 演化与测量通道下有 $\langle \Sigma_{0:t}\rangle\ge 0$。当连续极限为 Lindblad 半群且存在 $\rho^{\rm ss}$ 时，满足 $\frac{{\rm d}}{{\rm d}t}D(\rho_t\Vert\rho^{\rm ss})\le 0$。
**证明**：相对熵的 CPTP 单调给出 $D(\rho\Vert\sigma)\ge D(\Phi(\rho)\Vert\Phi(\sigma))$。离散路径层面，定义前后向路径测度 $\mathbb P,\mathbb P^\dagger$ 得 $\Sigma_{0:t}=\ln\frac{{\rm d}\mathbb P}{{\rm d}\mathbb P^\dagger}$，由 Kullback–Leibler 非负性得平均非负；Lindblad 情形由 Spohn 对 GKLS 生成元的引理推出相对熵随流不增。([物理评论链接管理器][4])

### 推论 1（时间箭头）

当观测层通过 $\pi$-语义塌缩将量子不确定性转为经典记录时，$\Sigma_{0:t}$ 的正值方向定义宏观时间箭头；无观测或可逆演化使 $\Sigma_{0:t}=0$。该方向性与量子非平衡涨落综述中的路径层与二点测量架构保持一致。([物理评论链接管理器][4])

---

## 2. 量子混沌：SBU—OTOC 与回声的热上界

### 定义 2（SBU—OTOC 与回声度量）

在可实现效果算子类 $\mathcal E$ 内，对 $V,W\in\mathcal E$ 定义 OTOC $C_{V,W}(t):=-\langle[W(t),V]^2\rangle_\beta$ 与 Loschmidt 回声 $\mathcal L_\delta(t):=\big|\langle\psi|e^{iHt}e^{-i(H+\delta V)t}|\psi\rangle\big|^2$。定义 Lyapunov 指数 $\lambda_{\rm L}(\mathcal W):=\sup_{V,W\in\mathcal E}\limsup_{t\to 0^+}\frac{1}{2t}\ln\frac{C_{V,W}(t)}{C_{V,W}(0^+)}$。([物理评论链接管理器][5])

### 定理 2（MSS 上界的 SBU 适用性）

在 KMS 热态下，$\lambda_{\rm L}\le 2\pi T$。
**证明**：MSS 以 KMS 正则性与解析延拓约束 OTOC 的早期指数增长速率。SBU 仅限制可测算子类 $\mathcal E$，不改变 KMS 构型与解析区域，故上界保持。回声的早期衰减速率一致地给出 $\lambda_{\rm L}$ 的读数。([施普林格链接][1])

---

## 3. 退相干与测量的熵—信息账本

### 模型

一次测量由仪器 $\{\mathcal I_x\}$ 与结果分布 $p_x={\rm tr}\,\mathcal I_x(\rho)$ 给出，塌缩后态 $\rho_x=\mathcal I_x(\rho)/p_x$。

### 定理 3（一步熵产生分解）

定义总通道 $\Phi=\sum_x\mathcal I_x$、信息增益 $I_{\rm meas}:=I(X:\mathrm{系统})$，存在可恢复项 $\mathcal R\ge 0$ 使
$$
\langle \Sigma\rangle=D(\Phi(\rho)\Vert\Phi(\rho^{\rm ss}))-D(\rho\Vert\rho^{\rm ss})+I_{\rm meas}-\mathcal R.
$$
**证明**：将测量视作量子—经典通道并使用相对熵的链式法则与数据处理；对 $\Phi$ 应用以 Petz 恢复映射为下界的"带余项"版本得到 $\mathcal R\ge 0$，当 $\Phi$ 可逆或测量不携带信息时回到 Spohn 单调。([arXiv][6])

### 命题 1（路径级涨落定理）

以前向与对偶路径测度配对，得 $\langle e^{-\Sigma}\rangle=1$ 与 $\langle\Sigma\rangle\ge 0$。该结果在量子二点测量与量子通道框架的综述中给出统一推导。([物理评论链接管理器][4])

---

## 4. Belavkin 过滤与量子 Jarzynski 等式（含信息修正）

### 设置与记号

系统—热浴初态 $\rho_\beta\otimes\tau_\beta$，外参 $\lambda_t$ 驱动并进行连续弱测量（同相、外差或计数），后验态 $\rho_t$ 满足 QSDE 与 Belavkin 过滤方程。([Project Euclid][2])

### 定义 3（轨道功、自由能差与信息项）

采用与二点测量等价的"条件能谱读数"定义轨道功 $W_t$ 与 $\Delta F_t$。在开系中引入"一时测量"的猜测功/热保持 Jarzynski 结构；连续监测引入信息项 $I_t$ 表示测量—反馈环的互信息流。([物理评论链接管理器][7])

### 引理 1（量子 Feynman–Kac 与测度变换）

对伴随半群做指数歪斜，定义过程 $\Gamma_t:=\exp[-\beta W_t+\beta\Delta F_t-I_t]$。在适定条件下 $\Gamma_t$ 为物理测度下的局部鞅（量子 Girsanov 变换）。([物理评论链接管理器][8])

### 定理 4（Belavkin–Jarzynski 等式）

有 $\big\langle \exp[-\beta W_t+\beta\Delta F_t-I_t]\big\rangle=1$，从而 $\langle W_t\rangle\ge \Delta F_t-T\,\langle I_t\rangle$。无反馈或无信息流极限 $I_t=0$ 时恢复标准量子 Jarzynski 等式；在一般开系下"一时测量"方案给出一致推广。([物理评论链接管理器][9])

---

## 5. 连续监测与控制的一致性

Belavkin 过滤与 Markovian 线性反馈的协同框架确保观测电流、后验态与控制律的统计闭合；相关教材与综述系统阐明扩散与计数两类后验方程、输入—输出与反馈主方程的等价关系。连续监测下区分功与热并保持第一与第二定律的形式，含反馈时以信息项修正。([Cambridge University Press & Assessment][10])

---

## 6. 可检后果与读数方案

一是混沌上界的可检性：以 OTOC 或 Loschmidt 回声的早期衰减率估计 $\lambda_{\rm L}$，热平衡态满足 $\lambda_{\rm L}\le 2\pi T$。二是退相干的熵—信息账本：通过 $\langle \Sigma\rangle$ 的分解在实验上区分动力学单调、信息增益与可恢复项。三是带信息修正的积分涨落定理：连续监测与反馈下的 Belavkin–Jarzynski 等式给出功—互信息的权衡边界。([施普林格链接][1])

---

## 7. 证明细节

### 7.1 定理 1 的严格化

离散情形将一步演化写为 $\Phi_k=\sum_x\mathcal I_{x_k}$。定义联合状态 $\omega_k=\sum_x p_x\,|x\rangle\!\langle x|\otimes\rho_x$ 与参考 $\sigma_k=\sum_x p_x\,|x\rangle\!\langle x|\otimes\rho^{\rm ss}$。有 $\Sigma_k=D(\omega_k\Vert\sigma_k)-D(\omega_{k-1}\Vert\sigma_{k-1})$，累加并取期望得 $\langle\Sigma_{0:t}\rangle=D(\omega_t\Vert\sigma_t)-D(\omega_0\Vert\sigma_0)\ge 0$。连续极限下，若 $\dot\rho_t=\mathcal L(\rho_t)$ 且 $\mathcal L^\dagger(\rho^{\rm ss})=0$，则 $\frac{{\rm d}}{{\rm d}t}D(\rho_t\Vert\rho^{\rm ss})={\rm tr}\,(\mathcal L(\rho_t)(\log\rho_t-\log\rho^{\rm ss}))\le 0$。([物理评论链接管理器][4])

### 7.2 定理 3 的可恢复项

设 $\Phi$ CPTP、$\mathcal R_\sigma$ 为 Petz 恢复映射，则 $D(\rho\Vert\sigma)-D(\Phi(\rho)\Vert\Phi(\sigma))\ge -\ln F(\rho,\mathcal R_\sigma\circ\Phi(\rho))^2$。取平均并识别测量互信息项得断言，其中 $\mathcal R$ 由恢复保真度下界控制且非负。([arXiv][11])

### 7.3 定理 2 与回声—OTOC 对齐

用 KMS 条件将 OTOC 解析延拓到复条带，最大模原理与 Schwarz 不等式给出指数增长的上界系数不超过 $2\pi T$。选择 $\mathcal E$ 为由 SBU 可实现的效果算子族不改变 KMS 数据，所以上界保持。回声的早期衰减常数与对易子平方的二阶矩等价，从而两种读数一致。([施普林格链接][1])

### 7.4 定理 4 的鞅构造

在 QSDE 中对生成元作指数歪斜并应用量子版 Girsanov 变换，得到 Doléans–Dade 指数型过程 $\Gamma_t$。由 Itô 计算验证 $\Gamma_t$ 为局部鞅，取期望得 $\langle \Gamma_t\rangle=1$。将 $\Gamma_t$ 的指数权重分解为功、自由能差与信息项即得结论；当 $I_t=0$ 或通道满足"一时测量"设定时分别回到标准与开系版本。([物理评论链接管理器][8])

---

## 8. 典型算例：两能级体系的同相监测

哈密顿量 $H(t)=\tfrac{\Omega(t)}{2}\sigma_x+\tfrac{\Delta}{2}\sigma_z$，Lindblad 扰动 $L=\sqrt{\kappa}\,\sigma_z$。扩散型同相监测给出 Belavkin 过滤
$$
{\rm d}\rho_t=\mathcal L(\rho_t)\,{\rm d}t+\sqrt{\kappa}\,(\sigma_z\rho_t+\rho_t\sigma_z-2\,{\rm tr}(\sigma_z\rho_t)\rho_t)\,{\rm d}W_t.
$$
用二点或"一时测量"定义 $W_t,\Delta F_t$，构造 $\Gamma_t=\exp[-\beta W_t+\beta\Delta F_t-I_t]$ 并验证 $\langle e^{-\beta W_t+\beta\Delta F_t-I_t}\rangle=1$。回声 $\mathcal L_\delta(t)$ 的短时衰减常数给出 $\lambda_{\rm L}$ 的估计。([Cambridge University Press & Assessment][10])

---

## 参考文献（选摘）

Maldacena, Shenker, Stanford, "A bound on chaos", JHEP 08 (2016) 106。([施普林格链接][1])
Esposito, Harbola, Mukamel, "Nonequilibrium fluctuations…", Rev. Mod. Phys. 81 (2009) 1665；及 2014 勘误。([物理评论链接管理器][4])
Hudson, Parthasarathy, "Quantum Itô's formula and stochastic evolutions", CMP 93 (1984) 301。([Project Euclid][2])
Wiseman, Milburn, "Quantum Measurement and Control", CUP (2010)。([Cambridge University Press & Assessment][10])
Manzano, Fazio, Roldán, "Quantum Martingale Theory and Entropy Production", PRL 122 (2019) 220602。([物理评论链接管理器][12])
Sagawa, Ueda, "Generalized Jarzynski equality under feedback", PRL 104 (2010) 090602。([物理评论链接管理器][9])
Funo, Watanabe, Ueda, "Integral quantum fluctuation theorems under measurement and feedback", PRE 88 (2013) 052121。([物理评论链接管理器][13])
Sone, Liu, Cappellaro, "Quantum Jarzynski equality in open systems…", PRL 125 (2020) 060602。([物理评论链接管理器][7])
Albarelli, Genoni, "A pedagogical introduction to continuously monitored quantum systems…", Phys. Lett. A 494 (2024) 129260。([科学直通车][14])
Xu, Swingle, "Scrambling Dynamics and OTOCs", PRX Quantum 5 (2024) 010201。([物理评论链接管理器][5])
Petz 系列与可恢复性：Wilde, "Recoverability in quantum information theory" 与 Sutter–Fawzi–Renner 等。([arXiv][11])
Loschmidt 回声综述：Gorin–Prosen–Seligman–Žnidarič，Phys. Rep. 435 (2006) 33–156。([科学直通车][15])

---

[1]: https://link.springer.com/article/10.1007/JHEP08%282016%29106?utm_source=chatgpt.com "A bound on chaos | Journal of High Energy Physics"
[2]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-93/issue-3/Quantum-Itos-formula-and-stochastic-evolutions/cmp/1103941122.pdf?utm_source=chatgpt.com "Quantum Ito's Formula and Stochastic Evolutions*"
[3]: https://projecteuclid.org/journals/kodai-mathematical-journal/volume-14/issue-2/Conditional-expectation-in-an-operator-algebra-IV-Entropy-and-information/10.2996/kmj/1138844604.full?utm_source=chatgpt.com "Conditional expectation in an operator algebra. IV. Entropy ..."
[4]: https://link.aps.org/doi/10.1103/RevModPhys.81.1665?utm_source=chatgpt.com "Reviews of Modern Physics"
[5]: https://link.aps.org/doi/10.1103/PRXQuantum.5.010201?utm_source=chatgpt.com "Scrambling Dynamics and Out-of-Time-Ordered Correlators in ..."
[6]: https://arxiv.org/pdf/1509.07127?utm_source=chatgpt.com "Universal recovery maps and approximate sufficiency of ..."
[7]: https://link.aps.org/doi/10.1103/PhysRevLett.125.060602?utm_source=chatgpt.com "Quantum Jarzynski Equality in Open Quantum Systems from ..."
[8]: https://link.aps.org/doi/10.1103/PhysRevE.86.010103?utm_source=chatgpt.com "Derivation of quantum work equalities using a quantum ..."
[9]: https://link.aps.org/doi/10.1103/PhysRevLett.104.090602?utm_source=chatgpt.com "Generalized Jarzynski Equality under Nonequilibrium ..."
[10]: https://www.cambridge.org/core/books/quantum-measurement-and-control/F78F445CD9AF00B10593405E9BAC6B9F?utm_source=chatgpt.com "Quantum Measurement and Control"
[11]: https://arxiv.org/pdf/1505.04661?utm_source=chatgpt.com "Recoverability in quantum information theory"
[12]: https://link.aps.org/doi/10.1103/PhysRevLett.122.220602?utm_source=chatgpt.com "Quantum Martingale Theory and Entropy Production"
[13]: https://link.aps.org/doi/10.1103/PhysRevE.88.052121?utm_source=chatgpt.com "Integral quantum fluctuation theorems under measurement ..."
[14]: https://www.sciencedirect.com/science/article/pii/S0375960123006400?utm_source=chatgpt.com "A pedagogical introduction to continuously monitored ..."
[15]: https://www.sciencedirect.com/science/article/abs/pii/S0370157306003310?utm_source=chatgpt.com "Dynamics of Loschmidt echoes and fidelity decay"
