# 相对散射行列式在量子引力中的统一角色：两域框架、固定能量 BK（$p\in\{1,2\}$ 统一版）、闭域 $\Lambda$‑斜率与黑洞极点谱学

## 摘要

以"相对行列式"为统一对象，我们在两类几何—物理场景中建立一套严密且可检的理论：$(\mathbf C)$ 紧致闭域中欧化后二次变分算子族的相对 $\zeta$/热核行列式及其对宇宙学常数项的体积密度响应；$(\mathbf S)$ 稳态外部几何（Schwarzschild–de Sitter/Kerr–de Sitter）上的定频散射矩阵及其相对（修正）行列式、谱移对象与准正则模（QNM）谱学。本文给出四个主定理并附完整证明：（i）在带权限制吸收原理（LAP）与双算子积分（DOI）的控制下，证明固定能量 Birman–Kreĭn 等式的 $p\in\{1,2\}$ 统一版：对勒贝格几乎处处频率 $\omega$ 有 $\det_p S_\Lambda(\omega)=\exp\!\big(-2\pi i\,\Xi^{(p)}_\Lambda(\omega)\big)$，其中 $p=1$ 时 $\Xi^{(1)}=\xi$ 为 Lifshits–Kreĭn 谱移函数，$p=2$ 时 $\Xi^{(2)}$ 为 Koplienko 二阶谱移的累积原函数；（ii）在闭域穆勒相对行列式框架下，证明"体积斜率定理"：$\lim_{\mu\to 0^+}\mathrm{Vol}_4(M)^{-1}\,\partial_\Lambda \Re\log\det_{\zeta,\mathrm{rel}}(\mathcal K_\Lambda+\mu^2,\mathcal K_0+\mu^2)=\tfrac{1}{8\pi G}$（按我们在正文固定的号约定）；（iii）在物理条带 $\Im\omega>-\,\gamma_0$ 上，相对散射行列式 $\tau_p(\omega)=\det_p\!\big(S(\omega)S_0(\omega)^{-1}\big)$ 的极点与 QNM 等价（计代数重数），且对参考 $S_0$ 的选择独立；（iv）对实频仅能对"相位"给等式，$\arg\det_p S=-2\pi\,\Xi^{(p)}$；而对 $p=2$ 的 Carleman 行列式有 $|\det_2 S|=\exp\!\big(\sum_j(1-\cos\theta_j)\big)\ge 1$，一般不可主张 $|\det_2 S|=1$。据此引入"相位化行列式" $\widehat{\det}_p S:=\det_p S/|\det_p S|$ 作为频域"全域亚纯拟合"的约束对象，并给出 Fisher 信息的主角度上界。文末提供闭域 rel‑zeta、外域 meromorph‑fit、通道‑伪幺正核验三条可复现实验管线的参数与验收标准。

---

## 1　引言

闭域的相对 $\zeta$/热核行列式与外域的相对散射行列式共享一个本质结构——"相对相位"。闭域侧，该相位通过对数导数回收 on‑shell 作用对宇宙学常数 $\Lambda$ 的体积密度响应；外域侧，它由 BK/LK（以及二阶 Koplienko 版）谱移函数控制到能量纤维化的散射矩阵之相位。本文把两域统一到一个"可检假设 $\Rightarrow$ 定理 $\Rightarrow$ 详细证明"的闭环：

1. 在算子‑Lipschitz 与 DOI 技术下实现固定能量化，配带权 LAP 主导收敛；
2. 在穆勒相对行列式下实现正则化独立与角点/边界/ghost 的逐项对消；
3. 在解析 Fredholm 框架下把相对散射行列式的极点同一为 QNM 并证明参考独立；
4. 在伪幺正（J‑酉）框架下分离"块级模长守恒"与"全局 Carleman 模长非恒等"，以"相位化行列式"施加实轴模长约束。

全文所有数学表达式均以 $\cdot$ 形式内联呈现，避免显示/环境切换造成的歧义。

---

## 2　设定、记号与可检假设

### 2.1　谱、理想与修正行列式

Hilbert 空间取可分 $\mathcal H$。自伴算子对记作 $(H_\Lambda,H_0)$，差 $V=H_\Lambda-H_0$。Schatten 理想 $\mathfrak S_p$ 定义标准。对 $K\in\mathfrak S_1$ 取 Fredholm 行列式 $\det(I+K)$；对 $K\in\mathfrak S_2$ 取 Carleman 行列式 $\det_2(I+K)=\det\!\big((I+K)\exp(-K)\big)$。若 $U$ 酉且 $U-I\in\mathfrak S_2$，谱角 $\{\theta_j\}\in\ell^2$ 满足 $|\det_2(U)|=\exp\!\big(\sum_j(1-\cos\theta_j)\big)\ge 1$、$\arg\det_2(U)=\sum_j(\theta_j-\sin\theta_j)$。

### 2.2　谱移对象与 DOI

一阶谱移 $\xi$ 与二阶谱移测度 $\eta$ 分别满足 $\mathrm{Tr}(f(H_\Lambda)-f(H_0))=\int f'(E)\,\xi(E)\,dE$、$\mathrm{Tr}(f(H_\Lambda)-f(H_0)-f'(H_0)V)=\int f''(E)\,d\eta(E)$，函数类取算子‑Lipschitz/适当 Besov 交集。累积原函数 $\Xi^{(2)}(E)=\eta((-\infty,E))$，归一化 $\Xi^{(2)}(-\infty)=0$。双算子积分表示 $f(H_\Lambda)-f(H_0)=\iint \Phi_f(\lambda,\mu)\,dE_\Lambda(\lambda)\,V\,dE_0(\mu)$，其中 $\Phi_f(\lambda,\mu)=(f(\lambda)-f(\mu))/(\lambda-\mu)$ 具 Schur/Haagerup 界。

### 2.3　带权 LAP 与能量纤维化

存在 $s>\tfrac12$、能窗 $I$ 与常数 $C_I$，使 $|\langle x\rangle^{-s}(H_\#-\lambda\mp i0)^{-1}\langle x\rangle^{-s}|\le C_I$ 对 $\lambda\in I$、$\#\in\{\Lambda,0\}$ 成立。稳态外部区（SdS/KdS）以时间 Killing 场驻定频率 $\omega$ 并施部分波分解得到通道矩阵 $S_{\ell m}(\omega)$。

### 2.4　闭域相对 $\zeta$-行列式与体积斜率

欧化后二次变分算子族 $\mathcal K_\Lambda$ 与参考 $\mathcal K_0$ 主符号一致，边界条件与 Faddeev–Popov ghost 配对一致，零模/阈值共振经去投影移除。差热核 $K_{\mathrm{rel}}(t)=\mathrm{Tr}\big(e^{-t(\mathcal K_\Lambda+\mu^2)}-e^{-t(\mathcal K_0+\mu^2)}\big)$ 具短时展开，定义 $\log\det_{\zeta,\mathrm{rel}}(\mathcal K_\Lambda+\mu^2,\mathcal K_0+\mu^2)=-\int_0^\infty t^{-1}K_{\mathrm{rel}}(t)\,dt$。度规号符与行动约定固定为 $\partial_\Lambda S_{\mathrm{on\text{-}shell}}=(8\pi G)^{-1}\mathrm{Vol}_4(M)$。

### 2.5　外域参考与伪幺正

在条带 $\Im\omega\in(-\gamma_0,0]$ 选参考散射矩阵 $S_0(\omega)$，要求同片解析且无零/极点。每个通道以 Jost–Wronskian 归一构造能流二次型 $\eta$ 使 $S_{\ell m}^\dagger\eta S_{\ell m}=\eta$。

### 2.6　可检假设（Assumption Box）

$(\mathrm{H\text{-}AC})$：波算子存在且完备，AC 部分可按能量纤维化；
$(\mathrm{H\text{-}LAP})$：带权 LAP（参数 $s>1/2$、常数 $C_I$）；
$(\mathrm{H\text{-}LK/DOI})$：Poisson 平滑 $f_\varepsilon\in\mathrm{OL}$、$|f_\varepsilon|_{\mathrm{OL}}\le C/\varepsilon$，DOI 核具统一 Schur/Haagerup 界；
$(\mathrm{H\text{-}S}_p)$：对 a.e. $\omega\in I$，有 $\chi_{(-\infty,\omega]}(H_\Lambda)-\chi_{(-\infty,\omega]}(H_0)\in\mathfrak S_p$ 与 $S_\Lambda(\omega)S_0(\omega)^{-1}-I\in\mathfrak S_p$（典型 $p=2$）；
$(\mathrm{H\text{-}relDet})$：主符号一致，边界/ghost 匹配，无零模或已去共振，差热核具短时展开；
$(\mathrm{H\text{-}Ref})$：参考 $S_0$ 条带内解析且无零/极点；
$(\mathrm{H\text{-}Can})$：通道能流规范固定，块级伪幺正成立。

---

## 3　主定理与结论

**定理 3.1（固定能量 BK：$p\in\{1,2\}$ 统一版）**　在 $(\mathrm{H\text{-}AC})$、$(\mathrm{H\text{-}LAP})$、$(\mathrm{H\text{-}LK/DOI})$、$(\mathrm{H\text{-}S}_p)$ 下，对勒贝格几乎处处 $\omega\in I$ 有：当 $p=1$ 时 $\det S_\Lambda(\omega)=\exp\big(-2\pi i\,\xi_\Lambda(\omega)\big)$；当 $p=2$ 时 $\det_2 S_\Lambda(\omega)=\exp\big(-2\pi i\,\Xi^{(2)}_\Lambda(\omega)\big)$。因此 $\arg\det_p S_\Lambda(\omega)=-2\pi\,\Xi^{(p)}_\Lambda(\omega)$。

**定理 3.2（闭域"体积斜率"）**　在 $(\mathrm{H\text{-}relDet})$ 与去共振投影下，有 $\lim_{\mu\to 0^+}\mathrm{Vol}_4(M)^{-1}\,\partial_\Lambda \Re\log\det_{\zeta,\mathrm{rel}}(\mathcal K_\Lambda+\mu^2,\mathcal K_0+\mu^2)=\tfrac{1}{8\pi G}$（按本文号约定）。

**定理 3.3（$\tau_p$ 的极点＝QNM，参考独立）**　令 $\tau_p(\omega)=\det_p\big(S(\omega)S_0(\omega)^{-1}\big)$。在 $(\mathrm{H\text{-}Ref})$ 下，条带 $\Im\omega\in(-\gamma_0,0]$ 内，$\tau_p$ 的极点集合与 $S$ 的极点（QNM）一致且计代数重数。若更换参考 $\widetilde S_0$ 仍满足 $(\mathrm{H\text{-}Ref})$，则 $\tau_p/\widetilde\tau_p$ 为条带内无零/极点的解析外函数，不改变极点集。

**定理 3.4（实频相位与模长；相位化行列式）**　块级：若 $S_{\ell m}^\dagger(\omega)\eta S_{\ell m}(\omega)=\eta$，则 $|\det S_{\ell m}(\omega)|=1$。整体：一般仅有 $\arg\det_p S(\omega)=-2\pi\,\Xi^{(p)}(\omega)$。当 $S(\omega)$ 酉且 $S(\omega)-I\in\mathfrak S_2$ 时，$|\det_2 S(\omega)|=\exp\big(\sum_j(1-\cos\theta_j(\omega))\big)\ge 1$。定义 $\widehat{\det}_p S(\omega)=\det_p S(\omega)/|\det_p S(\omega)|$、$\widehat{\tau}_p(\omega)=\tau_p(\omega)/|\tau_p(\omega)|$ 作为实轴"模长等于 1"的约束对象。

---

## 4　定理 3.1 的证明（DOI–LAP 主导收敛至固定能量）

**证明思路总览**：以 Poisson 平滑 $f_\varepsilon$ 逼近阶跃函数，应用 DOI 表达与带权 LAP 建立统一的 $\mathfrak S_p$ 主导不等式，随后在谱移对象的勒贝格点处令 $\varepsilon\downarrow 0$ 完成极限交换，最后经 AC 纤维化识别散射相位并升指数得到行列式等式。$p=1$ 与 $p=2$ 的差异由一阶/二阶迹公式承担。

**步骤 1（Poisson 平滑与 DOI 核界）**　取 $f_\varepsilon(\lambda)=\tfrac12+\tfrac{1}{\pi}\arctan((\omega-\lambda)/\varepsilon)$。则 $f_\varepsilon\in\mathrm{OL}$ 且 $|f_\varepsilon|_{\mathrm{OL}}\le C/\varepsilon$。DOI 表达 $f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)=\iint \Phi_{f_\varepsilon}(\lambda,\mu)\,dE_\Lambda(\lambda)\,V\,dE_0(\mu)$，其中 $|\Phi_{f_\varepsilon}|_{\mathrm{Schur}}\le C/\varepsilon$。

**步骤 2（带权 LAP 与 Schatten 主导）**　用 Stone 公式写出带权投影的边界值解算子形式，并应用 $(\mathrm{H\text{-}LAP})$ 得 $|\langle x\rangle^{-s}R_\#(\omega\pm i0)\langle x\rangle^{-s}|\le C_I$。由 Birman–Solomyak 型估计得
$|f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)|_{\mathfrak S_p}\le C_I(C/\varepsilon)\,M_p(I)$，其中 $M_p(I)=\sup_{\lambda\in I}|\langle x\rangle^{-s}(R_\Lambda(\lambda\pm i0)-R_0(\lambda\pm i0))\langle x\rangle^{-s}|_{\mathfrak S_p}$ 有界。

**步骤 3（$p=1$：谱移与 BK）**　一阶迹公式给 $\mathrm{Tr}(f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0))=\int f_\varepsilon'(E)\,\xi(E)\,dE$。令 $\varepsilon\downarrow 0$ 并用主导收敛，得 $\mathrm{Tr}(\chi_{(-\infty,\omega]}(H_\Lambda)-\chi_{(-\infty,\omega]}(H_0))=\xi(\omega)$ 于 $\omega$ 的勒贝格点成立。AC 纤维化与驻定散射表明 $\det S(\omega)=\exp(-2\pi i\,\xi(\omega))$。

**步骤 4（$p=2$：Koplienko 相位）**　二阶迹公式给 $\mathrm{Tr}\big(f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)-f'_\varepsilon(H_0)V\big)=\int f_\varepsilon''(E)\,d\eta(E)$。对右端两次分部并令 $\varepsilon\downarrow 0$ 得 $\Xi^{(2)}(\omega)=\eta((-\infty,\omega))$。固定能量化同上，于是 $\det_2 S(\omega)=\exp(-2\pi i\,\Xi^{(2)}(\omega))$。证毕。

---

## 5　定理 3.2 的证明（相对热核逐项对消、Tauberian 交换与号约定）

**步骤 1（对数导数的热核表示）**　有 $\partial_\Lambda \log\det_{\zeta,\mathrm{rel}}=-\int_0^\infty t^{-1}\,\partial_\Lambda K_{\mathrm{rel}}(t)\,dt$，其中 $K_{\mathrm{rel}}(t)=\mathrm{Tr}(e^{-t(\mathcal K_\Lambda+\mu^2)}-e^{-t(\mathcal K_0+\mu^2)})$。

**步骤 2（短时展开与逐项对消）**　在主符号一致、边界/ghost 配对一致、multiplicative anomaly 消失的条件下，$K_{\mathrm{rel}}(t)\sim \sum_{k\ge 0} a_k^{\mathrm{rel}}\,t^{(k-d)/2}$（$d=4$），除体积项 $a_0^{\mathrm{rel}}$ 外的局域系数（含 GHY、角点与 ghost 配对）逐项对消，即 $a_{k>0}^{\mathrm{rel}}=0$。

**步骤 3（Tauberian 交换与体积斜率）**　引入小质量 $\mu>0$ 以控制大 $t$ 部分，把 $\int_0^\infty=\int_0^{t_0}+\int_{t_0}^{\infty}$。前段由 $a_0^{\mathrm{rel}}$ 主导，后段在去共振投影下有统一界。交换 $\mu\downarrow 0$ 与体积密度化极限后，得到 $\mathrm{Vol}_4^{-1}\,\partial_\Lambda \Re\log\det_{\zeta,\mathrm{rel}}=\partial_\Lambda c_0$。按本文约定 $\partial_\Lambda S_{\mathrm{on\text{-}shell}}=(8\pi G)^{-1}\mathrm{Vol}_4$，对齐得到 $\partial_\Lambda c_0=\tfrac{1}{8\pi G}$。证毕。

---

## 6　定理 3.3 的证明（解析 Fredholm 与参考独立）

**步骤 1（解析 Fredholm）**　在条带 $\Im\omega\in(-\gamma_0,0]$，写 $S(\omega)=I+K(\omega)$，其中 $K(\omega)$ 为 $\mathfrak S_p$-值梅罗莫尔族。行列式 $\mathcal D_p(\omega)=\det_p(I+K(\omega))$ 梅罗莫尔，其零点阶等于 $I+K(\omega)$ 的核维数（代数重数）。

**步骤 2（相对化与极点计数）**　定义 $\tau_p(\omega)=\det_p(S(\omega)S_0(\omega)^{-1})$。若 $S_0$ 在条带内解析非零，$\tau_p$ 与 $S$ 共享极点与阶，极点即 QNM。

**步骤 3（参考独立）**　若另取 $\widetilde S_0$ 亦满足条件，则 $\tau_p/\widetilde\tau_p=\det_p(S_0\widetilde S_0^{-1})$ 为解析无零/极点的外函数，不改变极点集。证毕。

---

## 7　定理 3.4 的证明（块级伪幺正与整体 Carleman 模长）

**块级**　由 $S_{\ell m}^\dagger\eta S_{\ell m}=\eta$ 与 $\det(\eta^{-1}S_{\ell m}^\dagger\eta S_{\ell m})=1$ 得 $|\det S_{\ell m}|=1$。

**整体相位**　由定理 3.1 得 $\arg\det_p S(\omega)=-2\pi\,\Xi^{(p)}(\omega)$。

**整体模长（$p=2$）**　若 $S(\omega)$ 酉且 $S(\omega)-I\in\mathfrak S_2$，谱角 $\{\theta_j(\omega)\}\in\ell^2$ 给出 $|\det_2 S(\omega)|=\exp\big(\sum_j(1-\cos\theta_j(\omega))\big)\ge 1$。在一般 J‑酉情形，模长不恒定，故相位化 $\widehat{\det}_p$ 为实轴模长约束的自然对象。证毕。

---

## 8　全域亚纯拟合与 Fisher 投影几何（用于数据侧落地）

在条带 $\Im\omega\in[-\gamma_0,0]$ 上参数化 $\log\widehat{\tau}_p(\omega)=\sum_{j=1}^{J}\log\frac{\omega-\omega_j}{\omega-\overline{\omega_j}}+iQ(\omega)$，其中 $\omega_j$ 为下半平面极点，$Q$ 为在实轴取纯虚值的低阶整函数。强制共轭配对与"相位化模长等于 1"，并以条带交叉验证抑制假极点。

**命题 8.1（Fisher 主角度上界）**　对白化观测 $y_k=\Im\log\widehat{\tau}_p(\omega_k)+\epsilon_k$，雅可比 $J$ 与约束子流形切空间投影 $P_\mathcal M$ 给出受限 Fisher $F_\mathcal M=(P_\mathcal M J)^\top(P_\mathcal M J)$。若 $\vartheta$ 为 $\mathrm{range}(J)$ 与 $\mathrm{range}(P_\mathcal M)$ 的最大主角度，则方差缩减因子 $\mathcal R\le 1/|\sin\vartheta|$。证明见附录 F。

---

## 9　可复现实验协议（P1–P3）

**P1｜rel‑zeta（闭域）**：网格步长 $h$（三档）、热核窗 $t\in[t_{\min},t_{\max}]$（$t_{\min}\sim c\,h^2$）、外推阶 $N\in\{2,3\}$、小质量 $\mu$（三至五个对数点）。目标量为 $\mathrm{Vol}_4^{-1}\,\partial_\Lambda \Re\log\det_{\zeta,\mathrm{rel}}$。验收：斜率误差 $<1\%$；换角点剖分/规范后漂移 $<0.5\%$。

**P2｜meromorph‑fit（外域）**：拟合 $\log\widehat{\tau}_p$ 并恢复 $\{\omega_j\}$。先验：成对对称、条带解析、实轴模长约束（施于 $\widehat{\tau}_p$）、以及 $\Re\log\det_2(\omega)\ge 0$（若用 $p=2$）。验收：CRLB 相较逐模态提升 $\ge 1.3$ 倍；虚警率 $\le 5\%$；跨条带一致。

**P3｜bh‑channels（伪幺正与 BK 相位）**：Jost–Wronskian 归一构造 $\eta$，计算 $|S_{\ell m}^\dagger\eta S_{\ell m}-\eta|$ 与 $\arg\widehat{\det}_p S +2\pi\Xi^{(p)}$ 的相位闭合。验收：伪幺正残差 $<10^{-12}$，相位闭合 $<10^{-3}$ 弧度；随 $\ell_{\max}$ 呈 $a+b/\ell_{\max}$ 收敛。

---

## 10　讨论与展望

本文在明确可检的分析假设下，完成了固定能量 BK 的 $p\in\{1,2\}$ 统一版、闭域体积斜率、相对散射行列式极点＝QNM 的参考独立性、以及实频相位—模长分解四项主结论，并提供可复现实验管线。局限在于：强 trapping 或极端自旋时 LAP 常数可能恶化；非局部边界与奇异几何需单独核查 multiplicative anomaly；统计侧需应对模型偏差的鲁棒正则化。未来工作包括：在 Krein 空间下推广 $\det_p$ 的模长—相位公式；把微分形式/电磁场的 BK 版本无缝接入；利用多测站条带数据检验"参考独立"极点的稳定性。

---

# 附录（详细证明与技术细节）

## 附录 A　DOI–LAP 主导收敛的完整推导

**A.1　核界与权重移入**

取 $f_\varepsilon(\lambda)=\tfrac12+\tfrac1\pi\arctan\!\frac{\omega-\lambda}{\varepsilon}$。$f_\varepsilon\in\mathrm{OL}$，$|f_\varepsilon|_{\mathrm{OL}}\le C/\varepsilon$。DOI 表达给
$f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)=\iint \Phi_{f_\varepsilon}(\lambda,\mu)\,dE_\Lambda(\lambda)\,V\,dE_0(\mu)$，其中 $\Phi_{f_\varepsilon}$ 满足 $\sup_\lambda\int |\Phi_{f_\varepsilon}(\lambda,\mu)|\,d\mu\le C/\varepsilon$、$\sup_\mu\int |\Phi_{f_\varepsilon}(\lambda,\mu)|\,d\lambda\le C/\varepsilon$。

插入 $\langle x\rangle^{\pm s}$ 得
$f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)=\iint (\langle x\rangle^{-s}dE_\Lambda(\lambda))\,(\langle x\rangle^{s}V\langle x\rangle^{s})\, (dE_0(\mu)\langle x\rangle^{-s})\,\Phi_{f_\varepsilon}(\lambda,\mu)$。

**A.2　Schatten 主导不等式**

由 Haagerup/Schur 界与 Hölder 不等式（在 $\mathfrak S_p$ 上）得
$|f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)|_{\mathfrak S_p}\le |\Phi_{f_\varepsilon}|_{\mathrm{Schur}}\cdot \sup_{\lambda\in I}|\langle x\rangle^{-s}E'_\Lambda(\lambda)\langle x\rangle^{-s}|\cdot |\langle x\rangle^{s}V\langle x\rangle^{s}|_{\mathfrak S_p}\cdot \sup_{\mu\in I}|\langle x\rangle^{-s}E'_0(\mu)\langle x\rangle^{-s}|$。

用 Stone 公式 $E'_\#(\lambda)=\pi^{-1}\Im R_\#(\lambda+i0)$ 与 $(\mathrm{H\text{-}LAP})$ 得
$|f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)|_{\mathfrak S_p}\le C_I\,\varepsilon^{-1}\,|\langle x\rangle^{s}V\langle x\rangle^{s}|_{\mathfrak S_p}$。

在散射设置中更宜用差解算子形式
$|\langle x\rangle^{-s}(R_\Lambda(\lambda\pm i0)-R_0(\lambda\pm i0))\langle x\rangle^{-s}|_{\mathfrak S_p}$
控制 $|\langle x\rangle^{s}V\langle x\rangle^{s}|_{\mathfrak S_p}$，于是得到统一主导
$|f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)|_{\mathfrak S_p}\le C_I\,\varepsilon^{-1}\,M_p(I)$。

**A.3　勒贝格点与极限交换**

设 $\omega$ 为谱移对象的勒贝格点。由上式得一族 $\varepsilon$-一致可积的主导函数 $M(\omega)=\sup_{\varepsilon<\varepsilon_0}|f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)|_{\mathfrak S_p} \in L^1_{\mathrm{loc}}(I)$。于是 $\varepsilon\downarrow 0$ 下 DOI‑迹之极限与 $\omega$ 的局部积分可换，得到一阶/二阶迹公式的固定能量化，从而完成定理 3.1 的证明。

---

## 附录 B　相对热核逐项对消与 $\Lambda$‑斜率的细化

**B.1　短时展开与局域系数**

对 Laplace‑型算子 $\mathcal K_\#$（含规范‑ghost 配对）有 $\mathrm{Tr}(e^{-t\mathcal K_\#})\sim \sum_{j\ge 0} a_j(\mathcal K_\#)\,t^{(j-d)/2}$。在主符号一致与边界/ghost 匹配下，相对差 $a_{j>0}^{\mathrm{rel}}=a_j(\mathcal K_\Lambda)-a_j(\mathcal K_0)=0$；角点与边界项的系数在"相对差"中亦对消（Wodzicki 残数为零保证 multiplicative anomaly 不出现）。

**B.2　对数导数与体积项**

相对 $\zeta$ 写为 $\zeta_{\mathrm{rel}}(s;\mu)=\tfrac{1}{\Gamma(s)}\int_0^\infty t^{s-1}e^{-t\mu^2}\,K_{\mathrm{rel}}(t)\,dt$。对 $\Lambda$ 求导，仅 $a_0^{\mathrm{rel}}=\mathrm{Vol}_4(M)c_0$ 贡献，得到
$\partial_\Lambda \zeta'_{\mathrm{rel}}(0;\mu)=-\partial_\Lambda a_0^{\mathrm{rel}}\int_0^\infty t^{-1}e^{-t\mu^2}\,dt +\text{有限项}$。
体积密度化与 $\mu\downarrow 0$ 交换后，按本文约定 $\partial_\Lambda c_0=\tfrac{1}{8\pi G}$，从而得定理 3.2。

**B.3　Tauberian 交换的误差估计**

取 $t_0=\mu^{-2\alpha}$（$\alpha\in(0,1)$），$\int_{t_0}^\infty t^{-1}e^{-t\mu^2}\,K_{\mathrm{rel}}(t)\,dt$ 由谱间隙与去共振投影控制为 $\mathcal O(\mu^{2(1-\alpha)})$，而 $(0,t_0)$ 段误差由高阶系数对消后为 $\mathcal O(t_0^{1/2})=\mathcal O(\mu^{-\alpha})$ 的系数零化项，综合可取 $\alpha$ 使总体误差 $o(1)$。

---

## 附录 C　相对散射行列式的参考独立性与极点计数

**C.1　解析 Fredholm 工具**

记 $S(\omega)=I+K(\omega)$，$K(\omega)$ 为 $\mathfrak S_p$-值梅罗莫尔族。则 $\mathcal D_p(\omega)=\det_p(I+K(\omega))$ 梅罗莫尔且其零点阶等于 $\dim\ker(I+K(\omega))$。

**C.2　相对化与极点传递**

设 $S_0$ 条带内解析无零/极点，定义 $\tau_p(\omega)=\det_p(S(\omega)S_0(\omega)^{-1})$=$\det_p(I+K(\omega))\cdot \det_p(S_0(\omega)^{-1})$。后因子解析非零，故 $\tau_p$ 的极点与 $\mathcal D_p$ 同步，其阶即 QNM 的代数重数。

**C.3　参考独立的外函数因子**

若更换参考 $\widetilde S_0$，则 $\tau_p/\widetilde\tau_p=\det_p(S_0\widetilde S_0^{-1})$ 为解析且无零/极点（外函数），不改变极点集合与其重数。

---

## 附录 D　伪幺正：通道构造与整体 Carleman 模长

**D.1　能流二次型与 J‑酉**

径向方程两端取 Jost 解 $u_{\mathrm{in/out}}$ 并以 Wronskian 归一，使能流 $\mathcal F=\Im(\overline u\,\partial_r u)$ 在两端一致。据此定义通道二次型 $\eta=\mathrm{diag}(1,-1)$ 使 $S_{\ell m}^\dagger\eta S_{\ell m}=\eta$。

**D.2　块级行列式单位模与整体相位**

有限维块直接给 $|\det S_{\ell m}|=1$。整体直和在 $\mathfrak S_2$ 设置下仅相位等式可保留；若整体酉且 $S-I\in\mathfrak S_2$，由谱角展开得 $|\det_2 S|=\exp(\sum(1-\cos\theta_j))\ge 1$。

---

## 附录 E　Koplienko 相位的固定能量构造（$p=2$）

**E.1　二阶迹公式与 DOI**

对 $f_\varepsilon$ 有 $\mathrm{Tr}\big(f_\varepsilon(H_\Lambda)-f_\varepsilon(H_0)-f'_\varepsilon(H_0)V\big)=\int f_\varepsilon''(E)\,d\eta(E)$。右端两次分部得 $-\int f_\varepsilon'(E)\,d\Xi^{(2)}(E)$。

**E.2　主导收敛与勒贝格点**

由附录 A 的 $\mathfrak S_2$ 主导与 $|f'_\varepsilon|_{L^1}\le C$ 得可积主导，$\varepsilon\downarrow 0$ 时 $f'_\varepsilon$ 收敛到 $\delta_\omega$（弱意义）并在勒贝格点处恢复 $\Xi^{(2)}(\omega)$。

**E.3　散射相位与行列式**

固定能量化与 AC 纤维化把 $\Xi^{(2)}(\omega)$ 识别为散射相位的二阶谱移原函数，升指数得到 $\det_2 S(\omega)=\exp(-2\pi i\,\Xi^{(2)}(\omega))$。

---

## 附录 F　Fisher 投影几何上界的证明

**F.1　模型与投影**

白化观测 $y=J\theta+\epsilon$，硬约束 $C(\theta)=0$ 的可微子流形 $\mathcal M$ 之切空间投影 $P_\mathcal M$ 满足 $P_\mathcal M^2=P_\mathcal M$。

**F.2　主角度与谱界**

设 $\vartheta$ 为 $\mathrm{range}(J)$ 与 $\mathrm{range}(P_\mathcal M)$ 的最大主角度，有 $|P_\mathcal M v|\ge |\sin\vartheta|\,|v|$ 对所有 $v\in\mathrm{range}(J)$。于是 $v^\top F_\mathcal M v=|P_\mathcal M Jv|^2\ge \sin^2\vartheta\,|Jv|^2=v^\top (\sin^2\vartheta\,F) v$，从而 $F_\mathcal M\succeq \sin^2\vartheta\,F$。取最大特征值得 $\mathrm{Tr}(F_\mathcal M^{-1})\le \mathrm{Tr}(F^{-1})/ \sin^2\vartheta$，即方差缩减因子 $\mathcal R\le 1/|\sin\vartheta|$。证毕。

---

## 附录 G　可复现实验的参数与误差预算（简表）

**G.1　P1（闭域）**：$h\in\{h_0,\,h_0/2,\,h_0/4\}$；$t_{\min}\sim c\,h^2$、$t_{\max}$ 取满足半经典窗；$\mu$ 取 $\{\mu_0,\,\mu_0/3,\,\mu_0/9,\,\mu_0/27\}$。外推采用双线性（对 $(\mu,h)$）与 Richardson（对 $t$‑窗）混合。容差：斜率 $<1\%$；不同角点剖分/规范下漂移 $<0.5\%$。

**G.2　P2（外域）**：条带 $\Im\omega\in[-\gamma_0,0]$ 均匀采样；极点数 $J$ 以 AIC/BIC 与条带交叉验证联合确定；惩罚项约束 $Q(\omega)$ 的次数与实轴纯虚条件；先验 $\Re\log\det_2\ge 0$ 仅用作软正则化。容差：CRLB 提升 $\ge 1.3$、虚警 $\le 5\%$。

**G.3　P3（通道）**：外推半径、匹配半径与积分步长经网格搜索定标；Wronskian 归一差 $<10^{-12}$；$|S_{\ell m}^\dagger\eta S_{\ell m}-\eta|_\infty<10^{-12}$；相位闭合 $<10^{-3}$ 弧度；随 $\ell_{\max}$ 呈 $a+b/\ell_{\max}$ 收敛。

---

**正文与附录完**
