# S25. 非平稳 Weyl–Heisenberg 框架（对数/Mellin 模型）：带限—镜像一致下的 tight/dual 构造与稳定性

**—— Paley–Wiener 偶子空间上的分块调制—伸缩系统、Calderón 和与规范系统采样**

## 摘要（定性）

在对数模型下的 Weyl–Heisenberg 酉表示中，构造一类**分块（非平稳）调制—伸缩**的窗族，作用于 Paley–Wiener 偶子空间。以单块**"无混叠（painless）"**条件为核心，在频域得到**Walnut–Poisson**型能量恒等式，从而将多块系统的分析—合成算子**严格对角化**为**Calderón 和**的乘子；据此给出**tight/dual** 的显式频域构造与帧界判据。进一步，证明**步长与窗**的有界扰动在帧界上仅引入**$L^\infty$-级**的夹逼误差；轻微非均匀步长在 Schur 测试下保持帧性。频域的对角化允许直接调用**Wiener 型引理**得到对偶窗在同类函数空间中的正则性。最后，在 de Branges–Kreĭn 规范系统侧，利用**相位导数 = 谱密度**的同一式，采用**按相位等间隔**的非均匀采样，构造与空间链相容的非平稳 tight 系列，并与 Fourier 侧的 Calderón–tight 条件严格对齐。全程所有求和—积分换序仅依赖**有限阶** Euler–Maclaurin 及 Poisson 公式的带限情形，保证奇性与主尺度保持不变。参照文献包括非平稳 Gabor 帧之"painless"对角化与对偶构造、Wiener–Gabor 型谱不变性、de Branges 再生核与相位导数公式，以及 EM/Poisson 的带余项估计。

---

## 0. 设定与约定

### 0.1 Fourier 规范与缩放

采用

$$
\widehat f(\xi)=\int_{\mathbb R} f(t)\,e^{-it\xi}\,dt,\qquad
f(t)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{it\xi}\,d\xi .
$$

尺度变换 $w_R(t):=w(t/R)$ 满足 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。

Paley–Wiener 偶子空间

$$
\mathsf{PW}_\Omega^{\mathrm{even}}
=\bigl\{w\in L^2(\mathbb R):\ \operatorname{supp}\widehat w\subset[-\Omega,\Omega],\ w(t)=w(-t)\bigr\}.
$$

### 0.2 Weyl–Heisenberg 酉表示（对数/Mellin 模型）

在对数模型 $\mathcal H=L^2(\mathbb R)$（由 Mellin—对数变换与 $L^2(\mathbb R_+,x^{a-1}dx)$ 酉等价）上，取

$$
U_\tau g(t)=e^{i\tau t}g(t),\qquad V_\sigma g(t)=g(t+\sigma),
$$

满足 Weyl 关系 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。这是 **Weyl–Heisenberg 群**的标准酉表示（Stone–von Neumann 唯一性），与通常 $L^2(\mathbb R)$ Schrödinger 表示同构，为时—频平移的算子论背景。[^1] 本文所用"**Weyl–Heisenberg（对数/Mellin 模型）**"与文中其他地方可能出现的"Weyl–Mellin"术语等价（均指此表示）。

[^1]: 对数/Mellin 变换将乘性群上的伸缩映为加性平移，但酉表示保持 Heisenberg 代数结构不变。

### 0.3 Poisson 与 Euler–Maclaurin（有限阶）纪律

Poisson 求和在**带限**与适当可积性下等式成立；有限阶 Euler–Maclaurin（EM）给出端点导数与 Bernoulli 层的余项控制。本文所有换序仅用有限阶 EM 与带限 Poisson 情形，避免渐近展开的不可控尾项。

---

## 1. 分块非平稳系统与 Walnut–Poisson 结构

### 1.1 分块原子与"无混叠（painless）"条件

以块指标 $n\in\mathbb Z$ 计，选偶窗 $\psi_n\in\mathsf{PW}_{\Omega_n}^{\mathrm{even}}$，块内调制步长 $\Delta\tau_n>0$ 与平移 $\sigma_n\in\mathbb R$，原子

$$
\psi_{n,k}:=U_{k\Delta\tau_n}V_{\sigma_n}\psi_n,\qquad k\in\mathbb Z .
$$

记 $\widehat\psi_n$ 支持于区间 $I_n\subset\mathbb R$，长度 $|I_n|=2\Omega_n$。**单块无混叠条件**取为

$$
\boxed{\quad |I_n|\le \Delta\tau_n\quad\text{（即 }2\Omega_n\le \Delta\tau_n\text{）}\quad}
$$

它确保频域平移族 $\{\widehat{\psi_n}(\cdot-k\Delta\tau_n)\}_{k\in\mathbb Z}$ **互不重叠**，从而后述能量分解无混叠（"painless"）。该条件与非平稳 Gabor 框架的对角化定理一致。

为避免端点别名，除非另行声明，以下均假定 $2\Omega_n<\Delta\tau_n$；若取极限情形 $2\Omega_n=\Delta\tau_n$，则约定 $\{\xi:\widehat\psi_n(\xi)\neq0\}$ 与其 $\Delta\tau_n$-移位仅在零测集合上接触，因而不影响 (1.1) 与 (1.2) 的等式成立。

> **注**：$\Delta\tau_n\ge 2\Omega_n$ 是**调制采样**的无混叠条件；不同于**时域 Nyquist**（对时间采样带限信号 $h\le \pi/\Omega$），两者作用变量不同，勿混。本文频率变量为**弧频**（$e^{i\tau t}$），故与以 Hz 计的工程文献相比，所有 Nyquist/步长条件与 $2\pi$ 因子存在一一换算关系。

### 1.2 单块 Walnut–Poisson 能量恒等式

令 $f\in L^2(\mathbb R)$。在"无混叠"下，利用

$$
\mathcal F\{U_{k\Delta\tau}V_\sigma \psi\}(\xi)=e^{i\sigma(\xi-k\Delta\tau)}\,\widehat\psi(\xi-k\Delta\tau),
$$

与 Poisson/Parseval，可得**单块能量恒等式**

$$
\sum_{k\in\mathbb Z}\bigl|\langle f,\psi_{n,k}\rangle\bigr|^2
=\frac{2\pi}{\Delta\tau_n}\int_{\mathbb R}\bigl|\widehat f(\xi)\bigr|^2\,\bigl|\widehat{\psi_n}(\xi)\bigr|^2\,d\xi .
\tag{1.1}
$$

这正是非平稳 Gabor "painless"情形下帧算子的对角化（Walnut–Poisson 结构），参见定理化表述于 Balazs–Dörfler–Jaillet–Holighaus–Velasco（"NSGF"）的 Theorem 1 与其 Fourier 侧 Corollary 2。**常数按 §0.1 规范固定；与 DGM/NSGF 的 $2\pi$/步长因子一致地转换**。

### 1.3 多块 Gram 汇总与 Calderón 和

对多块求和得

$$
\sum_{n\in\mathbb Z}\sum_{k\in\mathbb Z}\bigl|\langle f,\psi_{n,k}\rangle\bigr|^2
=\int_{\mathbb R}\underbrace{\Bigl(\sum_{n}\frac{2\pi}{\Delta\tau_n}\,\bigl|\widehat{\psi_n}(\xi)\bigr|^2\Bigr)}_{=:\ \mathcal C(\xi)}\,\bigl|\widehat f(\xi)\bigr|^2\,d\xi ,
\tag{1.2}
$$

称 $\mathcal C$ 为（非平稳）**Calderón 和**。式 (1.2) 与 NSGF 结果完全一致（乘子为 $\sum_n b_n^{-1}|h_n|^2$）。**常数因子已按 §0.1 的 Fourier 规范 $\widehat f(\xi)=\int f(t)e^{-it\xi}dt$ 固定**。

---

## 2. 框架判据与 tight 构造

### 定理 2.1（Calderón–帧界判据）

设每块满足 $2\Omega_n\le \Delta\tau_n$，且存在 $0<A\le B<\infty$ 使

$$
A\le \mathcal C(\xi)=\sum_n \frac{2\pi}{\Delta\tau_n}\,|\widehat{\psi_n}(\xi)|^2\le B \quad\text{a.e. }\xi .
$$

则 $\{\psi_{n,k}\}_{n,k}$ 是 $\overline{\operatorname{span}}\{\psi_{n,k}\}$ 上的帧，且

$$
A\|f\|_2^2\le \sum_{n,k}|\langle f,\psi_{n,k}\rangle|^2\le B\|f\|_2^2,\qquad \forall f\in \overline{\operatorname{span}}\{\psi_{n,k}\} .
$$

**证明**：由 (1.2) 立即得到（帧算子为乘子 $\mathcal C$）。"无混叠"与对角化见 NSGF。∎

### 定理 2.2（tight 条件与 $\varepsilon$-tight）

若在**工作带** $\bigcup_n I_n$ 上 $\mathcal C(\xi)\equiv 1$（a.e.），则 $\{\psi_{n,k}\}$ 在 $\mathcal H_{\rm work}:=\overline{\operatorname{span}}\{\psi_{n,k}\}$ 上为 tight，且

$$
\sum_{n,k}|\langle f,\psi_{n,k}\rangle|^2=\|f\|_2^2,\qquad
f=\sum_{n,k}\langle f,\psi_{n,k}\rangle\,\psi_{n,k}\quad(L^2,\ \forall f\in\mathcal H_{\rm work}).
$$

若 $|\mathcal C-1|_{L^\infty}\le \varepsilon<1$，则帧界可取 $(1-\varepsilon,1+\varepsilon)$。

**证明**：由 (1.2) 代入并取上下夹。∎

> **频域构造**：可在带限与偶性约束下最小化
>
> $$
> \int_{\mathbb R}\Bigl|\sum_n\frac{2\pi}{\Delta\tau_n}|\widehat{\psi_n}(\xi)|^2-1\Bigr|^2d\xi,
> $$
>
> 并以 Bregman 型软约束实现数值稳健；$\Gamma$-收敛保证软—硬问题的极小序列与极小值一致极限。

---

## 3. 对偶窗的显式频域公式与正则性

### 定理 3.1（canonical dual）

在定理 2.1 条件下，设

$$
\widehat{\gamma_n}(\xi):=\frac{\overline{\widehat{\psi_n}(\xi)}}{\mathcal C(\xi)}\quad(\text{取 }\mathcal C(\xi)>0\ \text{处};\text{ 在 }\{\mathcal C=0\}\text{ 的零测集上取 }\widehat{\gamma_n}:=0).
$$

令 $\gamma_{n,k}:=U_{k\Delta\tau_n}V_{\sigma_n}\gamma_n$。则对任意 $f\in\overline{\operatorname{span}}\{\psi_{n,k}\}$ 有

$$
f=\sum_{n,k}\langle f,\psi_{n,k}\rangle\,\gamma_{n,k}
=\sum_{n,k}\langle f,\gamma_{n,k}\rangle\,\psi_{n,k}\quad(L^2\text{ 收敛}).
$$

**证明**：频域分析—合成乘子为 $\sum_n \tfrac{2\pi}{\Delta\tau_n}\widehat{\psi_n}\overline{\widehat{\gamma_n}}=\mathcal C\cdot\mathcal C^{-1}\equiv 1$。这正是非平稳"painless"情形对偶窗的标准公式。∎

**正则性（点乘代数情形）**：在 (1.2) 的对角化情形，帧算子为乘子 $\mathcal C$。若 $\mathcal C\in L^\infty$ 且 $\operatorname*{ess\,inf}_\xi\mathcal C(\xi)>0$，则 $1/\mathcal C\in L^\infty$，并且当 $\mathcal C$ 具有 $C^r$ 或 $W^{s,\infty}$ 正则性时，$1/\mathcal C$ 继承相同阶的正则性。于是

$$
\widehat{\gamma_n}=\frac{\overline{\widehat{\psi_n}}}{\mathcal C}\in \text{与 }\widehat{\psi_n}\text{ 同类的函数空间}.
$$

> **备注**：对于一般（非对角化）Gabor 框架，需要更强的 Wiener–Gabor 谱不变性（如 Gröchenig–Leinert 的扭卷积 Wiener 引理）；在本文"无混叠"情形下，上述点乘代数足够。

---

## 4. 稳定性

### 定理 4.1（Calderón 和扰动）

设基准系统之 Calderón 和 $\mathcal C$ 夹于 $[A,B]$。若扰动后 $\widetilde{\mathcal C}$ 满足

$$
|\widetilde{\mathcal C}-\mathcal C|_{L^\infty}\le \delta,\qquad \operatorname*{ess\,inf}_\xi\widetilde{\mathcal C}(\xi)>0,
$$

且各块仍满足 $2\Omega_n\le \Delta\tau_n$，则扰动后的系统仍为帧，帧界夹于 $[A-\delta,B+\delta]$（若 $A>\delta$）。

**证明**：帧算子为乘子 $\mathcal C$ 与 $\widetilde{\mathcal C}$，故能量由 (1.2) 直接夹逼。∎

### 定理 4.2（步长轻微非均匀化）

令步长列 $\{\Delta\tau_{n,k}\}_{k\in\mathbb Z}$ 有界且正，**以递推**

$$
\tau_{n,0}:=0,\qquad \tau_{n,k+1}-\tau_{n,k}=\Delta\tau_{n,k+1}\quad(\forall\,k\in\mathbb Z),
$$

从而

$$
\tau_{n,k}=\sum_{j=1}^{k}\Delta\tau_{n,j}\ (k>0),\qquad
\tau_{n,k}=-\sum_{j=k+1}^{0}\Delta\tau_{n,j}\ (k<0).
$$

仍取 $\psi_{n,k}:=U_{\tau_{n,k}}V_{\sigma_n}\psi_n$。假设存在全局分离常数 $d_n>0$ 使

$$
\inf_{k\neq\ell}|\tau_{n,k}-\tau_{n,\ell}|\ge d_n\ge 2\Omega_n .
$$

等价地，可写成**扰动型均匀格**：$\tau_{n,k}=k\Delta\tau_n+\delta_{n,k}$，且 $\sup_k|\delta_{n,k}-\delta_{n,k-1}|\le\varepsilon_n$ 与 $\Delta\tau_n-2\Omega_n>\varepsilon_n$。

在此分离假设下，Walnut 展开只剩小的"近对角"带，Gram 矩阵相对基准为小扰动；以 Schur 测试控制，得帧界偏移为 $\mathcal O(\sum_n \varepsilon_n)$（该估计在 $\sum_n \varepsilon_n\,|\widehat{\psi_n}|_{L^\infty}^2<\infty$ 或 $\sup_n\varepsilon_n\le\varepsilon$ 且仅有限多块非零等可检情形下有意义；见 §8‑4）。

**证明要点**：分离条件保证频域移位的全局最小间距，从而 Walnut 展开给出"几乎对角"结构，非均匀性仅进入对角外行列；以 Schur 测试/有界扰动法则控制。参见帧扰动一般理论。∎

> **软化与灵敏度**：以 Bregman 软目标在频域拟合 $\mathcal C\approx 1$，其最优解对数据与窗的扰动具 Lipschitz 连续依赖；$\tau\downarrow 0$ 时由 $\Gamma$-收敛回到硬约束问题。

---

## 5. 规范系统侧的非平稳 tight 采样

设 $E$ 为 de Branges 生成函数，$\mathcal H(E)$ 其 Hilbert 空间。写 $E(x)=|E(x)|e^{-i\varphi(x)}$，则再生核满足

$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2 \qquad(x\in\mathbb R),
$$

故 $\varphi'(x)=\pi\,\frac{K(x,x)}{|E(x)|^2}$。该恒等式乃 de Branges 论的基本结论（参见 Antezana–Marzo–Olsen, IMRN 2016）。另一方面，Weyl–Titchmarsh $m$ 函数为 Herglotz 函数，其边界虚部通过 Stieltjes 反演给出谱测度绝对连续部分的密度：

$$
\frac{d\mu_{\mathrm{ac}}}{dx}(x)=\frac{1}{\pi}\,\Im m(x+i0)\quad\text{(a.e.)}.
$$

**在采用与 $m$ 的 Herglotz 表示一致的规范化时**，当 $m$ 来自与 $E$ 相同的规范系统，两侧密度是一致刻度的，从而有 $\rho(x):=\frac{1}{\pi}\Im m(x+i0)=\frac{1}{\pi}\varphi'(x)$（核对角与 Stieltjes 反演一致）。若采用不同的相位/谱归一化，需在常数上做相应换元。

### 定理 5.1（相位等间隔的采样帧与 $\varepsilon$-tight 归一）

设 $E$ 的相位测度 $\varphi'(x)\,dx$ 为 **doubling**。取一族频带互不重叠的 $I_n$ 与窗 $\psi_n\in\mathsf{PW}_{\Omega_n}^{\mathrm{even}}$ 使

$$
\frac{2\pi}{\Delta\tau_n}\,|\widehat{\psi_n}(\xi)|^2=\mathbf{1}_{I_n}(\xi)\quad\text{a.e.},
$$

于是 $\mathcal C\equiv 1$（tight）。在规范系统侧，选取采样点列 $\{x_{n,k}\}$ 使

$$
\varphi(x_{n,k+1})-\varphi(x_{n,k})=\pi\quad(\text{每块内等间隔于相位}),
$$

等价于局部步长 $\Delta x\approx \pi/\varphi'(x)=1/\rho(x)$。则 $\{K(\cdot,x_{n,k})\}_{n,k}$ 在 $\mathcal H(E)$ 中**构成稳定采样帧**；当相位严格等间隔 $\Delta\varphi=\pi$（除至多一个相位偏移）时，归一核序列 $\kappa_x:=K(\cdot,x)/\sqrt{K(x,x)}$ 构成**正交基**（因此 tight）。在相位网格**准均匀**（doubling 条件）时形成**稳定帧**，可达 **$\varepsilon$-tight**（帧界 $1\pm\varepsilon$），其能量通过 $\varphi'=\pi\rho$ 与 Fourier 侧的 tight 条件严格匹配。

**证明概略**：频域 tight 使 Fourier 侧帧算子为恒等；规范侧用再生核与相位导数的核对角公式将能量归一化到单位密度刻度，取相位等间距即得采样帧；加权归一后在准均匀网格下可达 $\varepsilon$-tight 逼近；两侧借标准词典对齐。∎

> **说明**：相位等间隔与采样/插值密度的判据在 de Branges 文献中系统展开，含"相位导数给出自然密度/度量"的观点；密度/帧判据见 Marzo–Nitzan–Olsen (2011) 关于"doubling phase"的采样—插值研究。

---

## 6. "极点 = 主尺度" 与有限阶换序

### 定理 6.1（分析—合成不引入新奇性）

**技术假设**：对相关参数 $s$ 的条带 $\mathcal S$，被积函数与 $k$-求和项在 $t,\xi$ 上受一个 $s$-一致可积的主函数控制，且有限阶 EM 余项在 $\mathcal S$ 内一致有界；Poisson 求和仅在**带限**情形使用。于是所有换序与微分—求和交换均由主导收敛或 Fubini–Tonelli 支撑。

取偶带限或指数衰减窗，所有连续—离散换序仅用**有限阶** EM；假定窗与被测函数对参数 $s$ 的依赖在工作条带内解析/全纯。则对任意参数族 $h(\cdot;s)$ 的分析/合成泛函，在工作条带内的奇性位置与阶数与未窗化时相同；若窗在奇点处非零，则极阶保持。

**证明要点**：单块 Poisson 的混叠在"无混叠"下消失；有限阶 EM 的 Bernoulli 层与余项为整/全纯函数；分析—合成只叠加整/全纯层，故不改变原有奇性集合与阶。∎

---

## 7. 离散图并行的直觉类比（展望）

在 $(q+1)$-正则图的 Ihara ζ 场景中，频域由谱多项式的自倒数性支配；按回路长度分块采样的 tight 条件与 Bass–Ihara 行列式恒等存在**直觉上的平行结构**，可视作离散谱域的 Calderón 和。该类比尚需严格化，此处仅作为未来研究方向的提示。

---

## 8. 可检清单（最小充分条件）

1. **无混叠（painless）**：每块 $\psi_n\in\mathsf{PW}_{\Omega_n}^{\mathrm{even}}$，且

$$
2\Omega_n\le \Delta\tau_n
\quad(\text{频域移位互不重叠}).
$$

这是将 Walnut 结构对角化的几何充分条件。

2. **Calderón 和**：

$$
\mathcal C(\xi)=\sum_n \frac{2\pi}{\Delta\tau_n}|\widehat{\psi_n}(\xi)|^2,
$$

在工作带上夹于 $[A,B]$；tight 取 $\mathcal C\equiv 1$。

3. **对偶窗**：

$$
\widehat{\gamma_n}=\frac{\overline{\widehat{\psi_n}}}{\mathcal C};
$$

检验 $\operatorname*{ess\,inf}_\xi\mathcal C(\xi)>0$，并用 Wiener–型谱不变性得同类正则性。

4. **扰动半径**：若 $|\widetilde{\mathcal C}-\mathcal C|_{L^\infty}<A$ 则仍为帧；块内轻微非均匀步长满足 $\inf_k\Delta\tau_{n,k}\ge 2\Omega_n$ 且 $\sum_n\varepsilon_n|\widehat{\psi_n}|_{L^\infty}^2$ 小。

5. **Bregman 软化与 $\Gamma$**：软目标（如 $L^2$-罚）下的解与目标对扰动具稳定性；$\tau\downarrow0$ 的极限为硬约束问题。

6. **EM/Poisson 纪律**：仅用**有限阶** EM；记录阶数与端点导数阶；带限处 Poisson 去别名成立。

7. **规范系统 tight**：以 $\varphi'=\pi\rho$ 决定相位密度，按 $\Delta\varphi=\pi$ 取样再生核并与 Fourier 侧 tight 条件匹配。

---

## 9. 与前序理论的接口

### 9.1 S15：Weyl–Heisenberg 协变与窗函数诱导的内积

- S25 的分块非平稳系统由 Weyl–Heisenberg 酉表示 $(U_\tau,V_\sigma)$ 生成，直接推广 S15 的均匀格点情形；
- S15 的 RKHS 内积与 S25 的单块 Walnut–Poisson 恒等式（式 1.1）共享同一 Parseval 结构；
- S25 的 Calderón 和 $\mathcal C(\xi)$ 在均匀情形下退化为 S15 的标量帧算子乘子。

### 9.2 S16：de Branges 规范系统与辛结构

- S25 第 5 节的相位—密度恒等式 $K(x,x)=\pi^{-1}\varphi'(x)|E(x)|^2$ 是 S16 中 de Branges 规范系统再生核公式的核心；
- 相位等间隔采样 $\Delta\varphi=\pi$ 对应 S16 中辛流沿相位坐标的自然参数化；
- S25 的非平稳 tight 框架在规范系统侧保持辛结构，与 S16 的 Hamiltonian 流保持极点一致。

### 9.3 S17：散射—酉性与相位—行列式公式

- S25 定理 5.1 中的谱密度 $\rho(x)=\pi^{-1}\Im m(x+i0)$ 与 S17 的散射相位导数 $\delta'(E)=-2\pi\rho_{\mathrm{rel}}(E)$**（相对于参照算子）**联结；de Branges **$\varphi$** 与散射相位 **$\delta$** 的归一不同：若 $\delta=-2\varphi$（常见于 $\det S(E)=e^{-2\pi i\xi(E)}$ 与 $\xi'=\rho_{\mathrm{rel}}$ 的规范），则两式相容；
- 非平稳采样的局部步长 $\Delta x\approx 1/\rho(x)$ 对应 S17 中散射延迟时间的自然尺度；
- S25 的 tight 条件 $\mathcal C\equiv 1$ 类似于 S17 的散射酉性 $S^\dagger S=I$。

### 9.4 S18：窗不等式与半范数测度化

- S25 的"无混叠"条件 $2\Omega_n\le\Delta\tau_n$ 对应 S18 中频域 Nyquist 条件的非平稳推广；
- 定理 2.1 的帧界 $[A,B]$ 判据即 S18 的窗加权半范数等价常数在非平稳情形的推广；
- S25 的 Calderón 和扰动界（定理 4.1）与 S18 的窗扰动稳定性分析平行。

### 9.5 S19：光谱图与非回溯—邻接关系

- S25 第 7 节的离散图 tight 框架与 S19 的 Ihara ζ 函数通过 Bass–Ihara 行列式联结；
- 分块 Calderón 和在离散图上对应 S19 中非回溯算子谱的周期分解；
- 相位等间隔采样在图论侧对应按路径长度的均匀采样。

### 9.6 S20：BN 投影、KL 代价与 Bregman 敏感度

- S25 的频域 tight 构造（定理 2.2 注记）直接调用 S20 的 BN–Bregman 软目标框架；
- Calderón 和的 $\Gamma$-收敛（$\tau\downarrow 0$ 时软约束→硬约束）与 S20 的 Bregman 几何一致；
- 对偶窗的扰动界（定理 3.1）对应 S20 的信息—能量—敏感度不等式链。

### 9.7 S21：连续谱阈值与奇性稳定性

- S25 定理 6.1 的"极点 = 主尺度"保持即 S21 的奇性非增定理在非平稳框架下的推广；
- 有限阶 EM 的端点层（整/全纯）不引入新奇点，与 S21 的 Bregman–KL 敏感度链在阈值邻域的稳定性一致；
- 相位等间隔采样在奇点邻域的局部细化对应 S21 的阈值稳定半径。

### 9.8 S22：窗/核最优化与变分原理

- S25 的频域 tight 构造最小化 $\int|\mathcal C(\xi)-1|^2d\xi$，与 S22 的带限偶窗变分原理平行；
- 定理 2.2 的 $\varepsilon$-tight 判据对应 S22 的 L² 强凸变分问题的近似解；
- 非平稳步长的选择 $\Delta\tau_n\ge 2\Omega_n$ 对应 S22 的频域核型 Euler–Lagrange 方程的可行域约束。

### 9.9 S23：多窗协同优化与 Pareto 前沿

- S25 的分块系统 $\{\psi_n\}_{n\in\mathbb Z}$ 可视为 S23 的多窗族在频域的非重叠分块；
- Calderón 和 $\mathcal C(\xi)$ 对应 S23 的帧算子 Gram 矩阵对角元的加权和；
- S25 的对偶窗显式公式（定理 3.1）推广 S23 的 Wexler–Raz 双正交关系到非平稳情形。

### 9.10 S24：紧框架与对偶窗

- S25 的非平稳 tight/dual 构造推广 S24 的均匀移位紧框架到分块情形；
- 定理 2.1 的 Calderón–帧界判据对应 S24 定理 24.1 的纤维 Gram 表征在非重叠情形的简化；
- S25 的"无混叠"条件使 S24 的纤维 Gram 矩阵严格对角化为标量 Calderón 和；
- 定理 3.1 的对偶窗公式 $\widehat{\gamma_n}=\frac{\overline{\widehat{\psi_n}}}{\mathcal C}$ 推广 S24 定理 24.4 的 Nyquist 版正则对偶到非平稳分块；
- Wiener 型正则性引理对应 S24 第 5 节的 BN–Bregman 稳定性分析在函数空间的推广。

---

## 10. 与常见"Nyquist 条件"的术语对齐

- 本文**频域无混叠**用于调制步长 $\Delta\tau$，要求 $\Delta\tau\ge 2\Omega$（窗的频域支撑宽度不超过步长）。这是**使 Walnut 对角化成立的几何充分条件**，在 Gabor/NSGF 文献的"painless"情形下为核心假设。
- **时域 Nyquist**针对**时间采样**带限信号，步长 $h\le \pi/\Omega$。两者对象不同，条件方向相反，需区分。
- **单位与换算**：本文频率变量为**弧频**（$e^{i\tau t}$），故与以 Hz 计的工程文献相比，所有 Nyquist/步长条件与 $2\pi$ 因子存在一一换算关系。式 (1.1) 的常数因子 $2\pi/\Delta\tau_n$ 与 NSGF "painless" 对角化中的 $a_k^{-1}$ 乘子（工程单位酉傅里叶）互相匹配。

---

## 参考文献（荐读）

* **非平稳 Gabor 与 painless 对角化**：P. Balazs, M. Dörfler, F. Jaillet, N. Holighaus, G. Velasco, *Theory, implementation and applications of nonstationary Gabor frames*, J. Comput. Appl. Math., 2011（含 Theorem 1 & Corollary 2 的对角化与对偶公式）。
* **Painless non-orthogonal expansions**：I. Daubechies, A. Grossmann, Y. Meyer, *Painless nonorthogonal expansions*, J. Math. Phys., 1986（"painless"思想源头）。
* **Wiener–Gabor 谱不变性**：K. Gröchenig, M. Leinert, *Wiener's lemma for twisted convolution and Gabor frames*, J. Amer. Math. Soc., 2004。
* **Poisson 与 Euler–Maclaurin**：NIST DLMF（Bernoulli/EM 条目）、及 Poisson 公式讲义/教材。
* **帧稳定性**：见 Christensen 等关于帧的扰动定理综述。
* **de Branges 空间**：J. Antezana, J. Marzo, J.-F. Olsen, *Zeros of Random Functions Generated with de Branges Kernels*, IMRN, 2016（$K(x,x)=\pi^{-1}\varphi'(x)|E(x)|^2$）。
* **Weyl–Titchmarsh $m$ 与谱密度**：Stieltjes 反演给出 $d\mu_{\mathrm{ac}}=\pi^{-1}\Im m(x+i0)\,dx$。
* **采样—插值的相位密度观点**：J. Marzo, S. Nitzan, J.-F. Olsen, *Sampling and interpolation in de Branges spaces with doubling phase*, arXiv:1103.0566。
* **Ihara ζ 与 Bass–Ihara 行列式**：A. Terras 等综述与教材；维基条目概览。

---

**结语**

在"无混叠—Calderón 和—Wiener 引理"的三段论下，分块非平稳 Weyl–Mellin 系统可在 Paley–Wiener 偶子空间中实现 tight/dual 的显式构造与稳定控制；其规范系统对偶叙事则以相位导数提供自然的非均匀 tight 采样刻度，两侧通过再生核与乘子恒等式严密对齐。上述论证依赖的各环（NSGF 对角化、de Branges 核公式、EM/Poisson 纪律与帧扰动理论）均有现成标准文献支撑。该框架与 S15–S24（Weyl–Heisenberg、de Branges 规范系统、散射—酉性、窗不等式、光谱图、BN 投影、连续谱阈值、窗/核最优、多窗协同与紧框架）接口一致，将均匀框架推广至非平稳分块情形，并通过 Calderón 和的对角化实现频域—规范系统双侧的 tight/dual 统一构造。
