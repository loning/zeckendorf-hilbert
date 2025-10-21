# S2. 加法镜像与零集几何

**—— 二项闭合、余维 2、横截（残差）与基于幅度"平衡超平面"的局部化**

## 摘要（定性）

在母映射框架下系统刻画有限项指数和的**加法镜像**结构与**零集几何**。在统一的管域与换序/收敛前提下，给出：二项闭合的**充要条件**与显式零集参数化；有限和在**残差**参数集上零集为**实解析余维 2**子流形的横截性定理（在任意固定紧致子域上为**开且稠密**）；零集在尺度侧受若干幅度"平衡超平面"的**定量必要局部化**；并列出退化族与反例。记号、Γ/π 正规化与方向切片约定与 S0/S1 保持一致，摘要仅作定性描述。

---

## 0. 记号与前置（与 S0/S1 对齐）

* **相位—尺度母映射**

$$
\mathcal M[\mu](\theta,\rho)
=\int e^{\,i\langle\omega,\theta\rangle}\,e^{\,\langle\gamma,\rho\rangle}\,\mathrm d\mu(\omega,\gamma),
\qquad \theta\in\mathbb R^{m},\ \rho\in\mathbb R^{n}.
$$

离散谱时

$$
\mathcal M(\theta,\rho)
=\sum_{j=1}^J c_j\,e^{\,i\langle\alpha_j,\theta\rangle}\,e^{\,\langle\beta_j,\rho\rangle},
\quad
c_j\in\mathbb C,\ \alpha_j\in\mathbb R^m,\ \beta_j\in\mathbb R^n.
$$

* **预处理约定（C1′）**：先**删除所有 $c_j=0$ 的项**，并对**具有相同 $(\alpha_j,\beta_j)$** 的项进行**合并**（系数相加）。在此约定下，对所有参与求和的索引 $j$ 有 $c_j\neq0$，从而 $H_{jk}$ 与 $\delta(\rho)$ **定义良好**。
* **域契约（C0）**：一切计算在 S1 给定的管域/条带内进行，保证换序、逐项微分与 Poisson/Euler–Maclaurin 的合法互换。
* **方向切片（向量乘法）**

$$
\boxed{\ \rho=\rho_\perp+s\,\mathbf v,\qquad \mathbf v\in\mathbb S^{n-1},\ s\in\mathbb R\ }.
$$

* **幅度与相位**

$$
A_j(\rho):=|c_j|\,e^{\langle\beta_j,\rho\rangle},\qquad
\phi_j(\theta):=\arg c_j+\langle\alpha_j,\theta\rangle.
$$

* **幅度平衡超平面（尺度侧）**

$$
H_{jk}:=\Big\{\rho\in\mathbb R^n:\ \langle\beta_j-\beta_k,\rho\rangle=\log\frac{|c_k|}{|c_j|}\Big\},\qquad j\ne k,
$$

并约定：若 $\beta_j=\beta_k$ 且 $|c_j|\ne|c_k|$，则 $H_{jk}:=\varnothing$；若 $\beta_j=\beta_k$ 且 $|c_j|=|c_k|$，则 $H_{jk}:=\mathbb R^n$（对应纯相位等幅分支）。
* **可检纪律**：D1（测度/权重）、D2（Γ/π 正规化）、D3（有限阶 EM）、D4（方向化前置）。

---

## 1. 二项闭合与显式零集（加法镜像原型）

### 定理 T2.1（二项闭合的充要条件与零集参数化）

设

$$
F(\theta,\rho)=c_1 e^{\,i\langle\alpha_1,\theta\rangle}e^{\,\langle\beta_1,\rho\rangle}
+c_2 e^{\,i\langle\alpha_2,\theta\rangle}e^{\,\langle\beta_2,\rho\rangle},
\qquad c_1c_2\ne0,
$$

记 $\Delta\alpha:=\alpha_1-\alpha_2,\ \Delta\beta:=\beta_1-\beta_2$。在 C0 前提下：

1. **非退化**（$\Delta\alpha\ne0,\ \Delta\beta\ne0$）

$$
F=0\iff
\begin{cases}
\langle \Delta\beta,\rho\rangle = -\log\big|\tfrac{c_1}{c_2}\big|,\\[2mm]
\langle \Delta\alpha,\theta\rangle \equiv \pi-\arg\big(\tfrac{c_1}{c_2}\big)\ \ (\mathrm{mod}\ 2\pi).
\end{cases}
$$

零集为**实解析余维 2**的可数并列（尺度侧一条超平面与相位侧平行超平面族之积）。
2. **退化 I（纯相位）**（$\Delta\beta=0,\ \Delta\alpha\ne0$）
$|c_1|=|c_2|$ 时零集为相位侧平行超平面族；否则无零点。
3. **退化 II（纯尺度）**（$\Delta\alpha=0,\ \Delta\beta\ne0$）
$\tfrac{c_1}{c_2}\in(-\infty,0)$ 且 $\langle \Delta\beta,\rho\rangle=-\log\big|\tfrac{c_1}{c_2}\big|$ 时零集为尺度侧超平面；否则无零点。
4. **退化 III（同频同尺度）**（$\Delta\alpha=\Delta\beta=0$）
当且仅当 $c_1+c_2=0$ 时恒为零，否则无零点。

---

## 2. 有限项指数和的零集为余维 2（局部横截几何）

设

$$
F(\theta,\rho)=\sum_{j=1}^J c_j\,e^{\,\langle\beta_j,\rho\rangle}e^{\,i\langle\alpha_j,\theta\rangle},\qquad J\ge2,
$$

并记 $G=(\Re F,\Im F):\Omega\subset\mathbb R^{m+n}\to\mathbb R^2$。

### 引理 2.1（雅可比结构）

$$
\partial_{\theta_k}F=i\sum_{j=1}^J \alpha_{j,k}\,c_j e^{\,\langle\beta_j,\rho\rangle}e^{\,i\langle\alpha_j,\theta\rangle},\quad
\partial_{\rho_\ell}F=\sum_{j=1}^J \beta_{j,\ell}\,c_j e^{\,\langle\beta_j,\rho\rangle}e^{\,i\langle\alpha_j,\theta\rangle}.
$$

### 定理 T2.2（零集的局部结构：实解析余维 2）

若 $x_0=(\theta_0,\rho_0)\in\Omega$ 满足 $F(x_0)=0$ 且 $\mathrm{rank}\,\mathrm D G(x_0)=2$，则存在邻域 $U\ni x_0$ 使

$$
Z\cap U=\{x\in U:\ G(x)=0\}
$$

为 $\mathbb R^{m+n}$ 中的**实解析子流形**，且**余维 2**；该性质对 $\{c_j\}$ 与 $\{(\alpha_j,\beta_j)\}$ 的小扰动稳定。

---

## 3. 横截性为残差（在紧域上开且稠密）

### 定理 T2.3（参数横截性）

设参数空间

$$
\mathcal P=\Big\{(c_1,\ldots,c_J,\alpha_1,\ldots,\alpha_J,\beta_1,\ldots,\beta_J)\Big\}
$$

具自然拓扑。则在 $\mathcal P$ 的**残差**子集上，$G$ 与 $0\in\mathbb R^2$**横截**；并且对任意固定的紧致子域 $K\Subset\Omega$，该性质在 $\mathcal P$ 上为**开且稠密**。

*思路.* 令增广映射 $\mathscr G(\mathbf p,x)=G_{\mathbf p}(x)$。参数横截性（Baire 类）给出残差性；限制于固定 $K$ 时横截性为开条件且由 Sard–Thom 原理稠密。

---

## 4. 幅度"平衡超平面"的**定量必要局部化**

### 命题 2.4（必要局部化：定量版）

定义

$$
\delta(\rho):=\min_{j<k}\Big|\ \langle\beta_j-\beta_k,\rho\rangle-\log\frac{|c_k|}{|c_j|}\ \Big|.
$$

若 $\delta(\rho)>\log(J-1)$，则对任意 $\theta$ 有 $F(\theta,\rho)\ne0$。因此零集在尺度投影上仅可能出现在

$$
\{\rho:\ \delta(\rho)\le \log(J-1)\}
$$

这一族"有界厚度邻域"内；当 $J=2$ 时该厚度阈值为 $0$，零点仅可出现在 $H_{12}$ 上。

*证明要点.* 令 $j_\star$ 使 $A_{j_\star}(\rho)=\max_j A_j(\rho)$。由 $\delta(\rho)$ 的定义，对任意 $k\ne j_\star$ 有
$\log A_{j_\star}(\rho)-\log A_k(\rho)\ge \delta(\rho)$，故 $A_k(\rho)\le e^{-\delta(\rho)}A_{j_\star}(\rho)$，从而

$$
\sum_{k\ne j_\star}A_k(\rho)\le (J-1)e^{-\delta(\rho)}A_{j_\star}(\rho)
< A_{j_\star}(\rho).
$$

三角不等式给出 $|F(\theta,\rho)|\ge A_{j_\star}-\sum_{k\ne j_\star}A_k>0$。

---

## 5. 方向切片上的横截与亚纯化接口

取 $\rho=\rho_\perp+s\,\mathbf v$ 并固定 $\theta$，定义

$$
f_{\theta,\rho_\perp,\mathbf v}(s)
=\sum_{j=1}^J \big(c_j e^{\,\langle\beta_j,\rho_\perp\rangle}e^{\,i\langle\alpha_j,\theta\rangle}\big)\,e^{\,\langle\beta_j,\mathbf v\rangle s}.
$$

若存在 $j\ne k$ 使 $\langle\beta_j-\beta_k,\mathbf v\rangle\ne0$，则沿 $s$ 的零点在一般位置参数上为**简单零**（方向意义下的余维 1），其局部由两项主导的二项闭合控制；该方向性结构与 S5 的"沿方向亚纯化"自然对接。

---

## 6. 反例与边界族

* **R2.1（同频同尺度合并）**：$\alpha_1=\alpha_2,\ \beta_1=\beta_2,\ c_1+c_2\ne0$。无零点（同项合并）。
* **R2.2（纯相位不等幅）**：$\beta_1=\beta_2,\ |c_1|\ne|c_2|$。无零点（等式不可达）。
* **R2.3（纯尺度非负比）**：$\alpha_1=\alpha_2,\ \tfrac{c_1}{c_2}\notin(-\infty,0)$。无零点（相位不可对径）。
* **R2.4（多项和的共线梯度）**：存在非平凡实向量 $u=(u_1,\dots,u_J),\ v=(v_1,\dots,v_J)\in\mathbb R^J$ 使 $\sum_{j=1}^J u_j\alpha_j=0,\ \sum_{j=1}^J v_j\beta_j=0$，并在零点处致 $\mathrm D G$ 两行共线。出现**非横截**零（可能余维 1 或粘连）。
* **R2.5（域外切片）**：尺度超平面与 C0 域不相交，参数方程无解；属域边界而非几何失效。

---

## 7. 与后续篇章的接口

* **S3（自反核与函数镜像）**：T2.1–T2.3 提供"幅度平衡 + 相位对径"的零集模板，可直接用于 Mellin 自反核下完成函数零点对称的局部模型；核之选取宜保 $\Delta\alpha\ne0,\ \Delta\beta\ne0$ 以维持镜像横截。
* **S4（有限阶 EM 延拓）**：命题 2.4 的定量界给出端点—主尺度分离的可检阈值；EM 余项以整函数方式进入，不改变"余维 2 主体几何"。
* **S5（方向亚纯化）**：沿方向切片的二项闭合结构（简单零与极点阶的方向模板）嵌入"极点=主尺度"的定位叙述。
* **S10（amoeba/Ronkin）**：$H_{jk}$ 为 amoeba 边界的线性骨架；零集的尺度投影受其支配，本篇给出必要性与定量局部化，凸性与定量增长留待 S10 完备。

---

## 8. 统一"可检清单"（最小充分条件汇总）

* **C0（域）**：工作点与邻域操作均处于 S1 的管域/条带内。
* **C1（参数非退化）**：关注二项子和满足 $\Delta\alpha\ne0,\ \Delta\beta\ne0$，或遵循 T2.1 的相应幅度/相位条件。
* **C2（横截性）**：候选零点处核对 $\mathrm{rank}\,\mathrm D G=2$；多项和避免诱发 $\nabla F$ 共线的代数关系。
* **C3（尺度局部化）**：仅在 $\{\rho:\ \delta(\rho)\le \log(J-1)\}$ 内搜索；若存在单项绝对占优或 $\delta(\rho)>\log(J-1)$，立判无零。
* **C4（方向化）**：沿 $\mathbf v$ 切片上确保 $\langle\beta_j-\beta_k,\mathbf v\rangle\ne0$ 以获得简单零（一般位置）。
* **C5（稳定性）**：对小扰动参数保持 T2.2 的满秩与 T2.3 的横截性（紧域上开且稠密，整体为残差）。

---

## 9. 参考公式与微分算子（实作速记）

* 梯度与雅可比

$$
\nabla_{\theta}F=i\sum_j \alpha_j\,\varphi_j,\qquad
\nabla_{\rho}F=\sum_j \beta_j\,\varphi_j,\qquad
\varphi_j:=c_j e^{\,\langle\beta_j,\rho\rangle}e^{\,i\langle\alpha_j,\theta\rangle}.
$$

* 满秩判据（等价、可检）

$$
\boxed{\ \mathrm{rank}\,\mathrm D G=2\ \Longleftrightarrow
\Re\nabla F\ \text{与}\ \Im\nabla F\ \text{在}\ \mathbb R^{m+n}\ \text{线性无关}\ }.
$$

等价地，存在 $u,v\in\mathbb R^{m+n}$ 使

$$
\det\begin{pmatrix}
\Re\langle u,\nabla F\rangle & \Re\langle v,\nabla F\rangle\\[2pt]
\Im\langle u,\nabla F\rangle & \Im\langle v,\nabla F\rangle
\end{pmatrix}\neq 0.
$$

* 二项闭合判据（速记）

$$
\boxed{\ \langle \Delta\beta,\rho\rangle=-\log|c_1/c_2|,\quad
\langle \Delta\alpha,\theta\rangle\equiv \pi-\arg(c_1/c_2)\ (\mathrm{mod}\ 2\pi)\ }.
$$

---

## 结语

加法镜像将"指数和为零"的问题剖分为**幅度平衡**与**相位对径**两条独立实方程；在一般位置下两者横截，零集呈现**实解析余维 2**的稳定几何。由此产生的二项闭合模板、参数横截性（残差/紧域开且稠密）与尺度侧的**定量必要局部化**，构成后续函数镜像、有限阶延拓与方向亚纯化的统一几何—分析基线。
