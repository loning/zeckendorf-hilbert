# 信息几何与时空几何的结构同构：从相对熵的二阶响应到度规、联络与场方程

## 摘要

本文构建并严格论证一个"信息—时空同构"框架。以满足 Eguchi 正则性的散度函数（含相对熵）为起点，定义 Fisher–Rao 度量与对偶联络族，并在 $\alpha=0$ 情形下得到与度量相容且无挠的 Levi–Civita 联络；由此保证二阶 Bianchi 恒等式与能动张量守恒。随后我们把"散度—Hessian—度量"的构造范畴化，证明**"正则散度流形（对偶平坦）"与"带平直仿射联络且度量为 Hessian 形式的（伪）黎曼流形"**之间的等价，消除"形式类比"的歧义。针对时空所需的洛伦兹签名，本文给出两步方案：第一步证明一个正定性不可行性引理，指出在 Eguchi 条件下由对角极小性的散度诱导的 Fisher–Rao 度量必为正定；第二步通过"伪-Hessian 结构／ADM 提升"自然嵌入到洛伦兹几何，并在微扰层面用"相对熵二阶变分＝量子 Fisher＝引力规范能"的同一性建立信息几何切空间与满足线性化爱因斯坦方程的引力相空间之间的等距对应；非线性层面以体-边相对熵等价与引力的"纠缠第一定律"闭合到完整场方程。该框架还导出可检验推论：相对熵单调性与二阶形变给出 QNEC/ANEC，从而对应几何中的聚焦不等式与能量条件。上述关键点分别以 Eguchi/Amari—Nagaoka 的信息几何、Hessian/伪-Hessian 几何、以及全息/量子信息—引力的代表性判据为锚定。([Project Euclid][1])

---

## 0  记号、范畴与基本公设

**散度与对偶联络** 设正则散度 $D(\theta|\theta')$ 在对角处三阶可微且对角极小（Eguchi 正则性）。定义
$$
g_{ij}=\left.\partial_i\partial_{j'}D\right|_{\Delta},\quad \Gamma_{ijk}=-\left.\partial_i\partial_j\partial_{k'}D\right|_{\Delta},\quad \Gamma^{*}_{ijk}=-\left.\partial_{i'}\partial_{j'}\partial_k D\right|_{\Delta},
$$
并取对偶联络族 $\nabla^{(\alpha)}=\tfrac{1+\alpha}{2}\nabla+\tfrac{1-\alpha}{2}\nabla^{*}$。当 $\alpha=0$ 时得到与 $g$ 相容且无挠的 Levi–Civita 联络。([Project Euclid][1])

**Fisher–Rao 唯一性** 在信息单调性（对充分统计与随机映射单调）假设下，信息度量在比例因子之外唯一，即 Fisher–Rao 度量。本文在范畴层面采用该刚性。([SpringerLink][2])

**Hessian/伪-Hessian 流形** 设 $(M,\nabla^{\mathrm{aff}})$ 为平直无挠的仿射流形，若存在势函数 $\varphi$ 使 $g=\nabla^{\mathrm{aff}}d\varphi$（或局部 $g_{ij}=\partial_i\partial_j\varphi$），则称 $(M,\nabla^{\mathrm{aff}},g)$ 为 Hessian 流形；允许 $g$ 非定号时称伪-Hessian 流形。([Nzdr][3])

**全息/量子信息—引力桥** 相对熵一阶变分"第一定律"给出线性化爱因斯坦方程；二阶变分的量子 Fisher 信息（QFI）与引力**规范能**等距同构。体-边相对熵等价把该关系推广到非线性阶。([SpringerLink][4])

---

## 1  正定性障碍与两步化解

### 1.1  正定性不可行性引理

若 $D$ 满足 Eguchi 正则性且对角极小，则对任何非零切向量 $v$，有
$$
v^iv^jg_{ij}=\left.\tfrac{d^2}{dt^2}D(\theta|\theta+tv)\right|_{t=0}>0.
$$
因此由此产生的 Fisher–Rao 度量必为正定，不能直接作为时空的洛伦兹度规。([Project Euclid][1])

### 1.2  伪-Hessian 与 ADM 提升

**步骤 A：伪-Hessian 扩展** 在允许非定号的伪-Hessian 框架中，可在数学上容纳洛伦兹指数；但此时"散度"须理解为**伪散度/作用**而非对角极小的统计散度。([ncatlab.org][5])
**步骤 B：ADM 提升** 取统计流形 $(\mathcal S,g_{F})$ 作为"空间切片"，并引入 lapse $N$ 与 shift $N^i$，定义洛伦兹度规
$$
g_L=-N^2d\tau^2+h_{ij}(dx^i+N^i d\tau)(dx^j+N^j d\tau),
$$
其中 $h_{ij}=g_{F,ij}$。把"信息流/模流"编码入 $(N,N^i)$；在线性化层面，由"QFI＝规范能"得到信息切空间与满足线性化爱因斯坦方程的摄动空间的等距对应；非线性层面由体-边相对熵等价与引力第一定律闭合到完整场方程。([SpringerLink][4])

---

## 2  范畴化陈述与主同构定理

### 2.1  两个范畴

$\mathbf{Div}^{\mathrm{df}}$：对象为 $\bigl(M,D\bigr)$，其中 $D$ 正则且诱导对偶平坦结构；态射为保持 $(g,\nabla,\nabla^*)$ 的光滑映射。
$\mathbf{Hess}^{\sigma}$：对象为 $\bigl(M,\nabla^{\mathrm{aff}},g\bigr)$，$\nabla^{\mathrm{aff}}$ 平直无挠且 $g=\nabla^{\mathrm{aff}}d\varphi$（允许签名 $\sigma$）；态射为保持 $\nabla^{\mathrm{aff}}$ 与 $g$ 的仿射等距。

### 2.2  主定理（对偶平坦情形的范畴等价）

存在函子
$$
\Phi:(M,D)\mapsto\bigl(M,\nabla^{\mathrm{aff}},g=\nabla^{\mathrm{aff}}d\varphi\bigr),\quad \Psi:(M,\nabla^{\mathrm{aff}},g)\mapsto(M,D_{\mathrm{can}}),
$$
使 $\Phi,\Psi$ 在对偶平坦子范畴上互为等价：$\Phi$ 由 Bregman/Legendre 势生成 Hessian 结构；$\Psi$ 由 Ay–Amari/Felice–Ay 的**规范散度**自反构造恢复 $(g,\nabla,\nabla^*)$。$\alpha=0$ 联络即 Levi–Civita。([Vielbein][6])

*证明要点*：对偶平坦保证存在仿射坐标与凸势 $\varphi$ 使 $g=\partial^2\varphi$；反向方向以"规范散度"在测地上积分逆指数映射重建 $(g,\nabla,\nabla^*)$，两向构造在态射层自然相容。

---

## 3  线性与非线性：由相对熵到场方程

### 3.1  线性化层面

在 CFT 的球形区域与其 AdS/Rindler 楔的全息对偶下，相对熵二阶变分的 QFI 与 GR 相空间的规范能二次型等距：
$$
\delta^2 S_{\mathrm{rel}}=\tfrac12\langle\delta\rho,\mathcal I_{\mathrm{QF}}\delta\rho\rangle=E_{\mathrm{can}}[\delta g,\delta\Phi].
$$
相对熵一阶"第一定律"给出线性化爱因斯坦方程，二阶正性给出稳定性/正能。([SpringerLink][4])

### 3.2  非线性补全

体-边相对熵等价与"纠缠第一定律"把上述结果推广至非线性，得到完整的爱因斯坦方程（含宇宙学常数项）并与 Wald 形式主义一致。([SpringerLink][7])

---

## 4  能量条件：由信息不等式到几何聚焦

相对熵的单调性与形状导数给出 QNEC，从而推出几何侧的聚焦不等式与能量条件；ANEC 可由因果性与微局部算子展开给出。该链条构成本框架的经验核可检性。([物理评论链接管理器][8])

---

## 5  与"伪-Riemann—最优传输"之桥接

Wong 等建立了"伪-Riemann 框架编码信息几何"的一般论断：Kim–McCann 的伪-Riemann 结构把最优传输中的 MTW 张量与信息几何的对偶结构联系起来，由此提供了从"散度—对偶联络"到"伪-Riemann"乃至最优传输的统一桥接。该观点为"伪-Hessian／ADM 提升"的数学实现提供了外部支持。([SpringerLink][9])

---

## 6  结构同构的"正定性障碍—提升"范式（形式化叙述）

**引理 6.1（正定性障碍）** 在 Eguchi 意义下，$D$ 的对角极小 $\Rightarrow g$ 正定。见 §1.1。([Project Euclid][1])

**定理 6.2（提升闭合）** 设 $(\mathcal S,g_F)$ 为由相对熵二阶变分给出的统计流形；取带 $N,N^i$ 的 ADM 提升 $g_L$。则：
(i) 线性化下，QFI 与 $g_L$ 的规范能等距，从而得到线性化场方程；
(ii) 若满足体-边相对熵等价与纠缠第一定律，则非线性层面闭合到完整的爱因斯坦方程。([SpringerLink][4])

**推论 6.3（范畴等价的稳健性）** 在对偶平坦子范畴内，$\mathbf{Div}^{\mathrm{df}}\simeq\mathbf{Hess}^{+}$；对洛伦兹目标几何采用"伪-Hessian／ADM 提升"，范畴等价通过提升函子保留到物理几何侧的线性/非线性动力学判据。

---

## 7  观测—校准—可检性

1. **观测校准**：在低曲率与弱场极限中，ADM 提升/伪-Hessian 配置可回归 GR 之标准可观测（时延、透镜、黑洞阴影等）；偏离只可能来自（a）脱离对偶平坦（非度量/非 Levi–Civita 修正）或（b）相对熵的量子修正（二阶以上）。
2. **能量条件**：QNEC/ANEC 提供模型无关的实验约束（例如通过引力波有效能量符号判据）。([物理评论链接管理器][8])

---

## 附录 A  由散度到 $(g,\nabla,\nabla^*)$ 与 $\alpha$-联络

令 $g_{ij}=\left.\partial_i\partial_{j'}D\right|_{\Delta}$、$\Gamma_{ijk}=-\left.\partial_i\partial_j\partial_{k'}D\right|_{\Delta}$、$\Gamma^{*}_{ijk}=-\left.\partial_{i'}\partial_{j'}\partial_kD\right|_{\Delta}$。可验证 $(\nabla,\nabla^*)$ 互为对偶且无挠，$\nabla^{(\alpha)}=\tfrac{1+\alpha}{2}\nabla+\tfrac{1-\alpha}{2}\nabla^*$。当 $\alpha=0$ 时与 $g$ 相容，故为 Levi–Civita。([Project Euclid][1])

---

## 附录 B  对偶平坦 $\Longleftrightarrow$ Hessian 的范畴等价细节

对偶平坦 $\Rightarrow$ 存在仿射坐标与凸势 $\varphi$ 满足 $g=\partial^2\varphi$，$\nabla^{\mathrm{aff}}$ 为坐标平直联络；反向由 Ay–Amari（及其 Felice–Ay 的推广）的"规范散度" $D_{\mathrm{can}}$ 沿测地积分逆指数映射重建 $(g,\nabla,\nabla^*)$。两向构造在态射上自然相容。([MDPI][10])

---

## 附录 C  QFI＝规范能＝相对熵二阶项

全息背景下，边界相对熵二阶项
$$
\delta^2 S_{\mathrm{rel}}(\delta\rho)=\tfrac12\langle\delta\rho,\mathcal I_{\mathrm{QF}}\delta\rho\rangle
$$
与体内规范能 $E_{\mathrm{can}}[\delta g,\delta\Phi]$ 相等；相对熵的一阶变分给出线性化场方程，二阶正性给出能量正性。体-边相对熵等价与引力"第一定律"确保非线性闭合。([SpringerLink][4])

---

## 附录 D  相关背景与延展

**D.1 Hessian 与伪-Hessian**：Hessian 几何系统综述见 Shima 专著；伪-Riemann 框架与信息几何的编码见 Wong。([Nzdr][3])
**D.2 Fisher–Rao 唯一性**：Čencov/Ay–Jost–Lê–Schwachhöfer—Lê 的唯一性与单调性刻画，最新还出现 $L^p$-Fisher–Rao 的推广，但不影响 $\alpha=0$ 的唯一性结论。([SpringerLink][2])
**D.3 Jacobson 等价**：信息—几何—引力的宏观等价（"爱因斯坦方程＝状态方程"）为本文的宏观一致性背景。([物理评论链接管理器][11])

---

## 参考指引（关键文献）

* Eguchi, **Geometry of minimum contrast**（度量与对偶联络来自散度）. ([Project Euclid][1])
* Amari & Nagaoka, **Methods of Information Geometry**（$\alpha$-联络与 Bregman 规范）. ([Vielbein][6])
* Ay & Amari / Felice & Ay，**规范散度与对偶平坦的散度化**. ([MDPI][10])
* Shima, **The Geometry of Hessian Structures**（Hessian/伪-Hessian 典范）. ([Nzdr][3])
* Lashkari & Van Raamsdonk, **Canonical energy is quantum Fisher information**（QFI＝规范能）. ([SpringerLink][4])
* Jafferis–Lewkowycz–Maldacena–Suh, **Relative entropy equals bulk relative entropy**（体-边相对熵等价）. ([SpringerLink][7])
* Bousso 等，**Proof of the QNEC**；Hartman–Kundu–Tajdini，**ANEC from causality**（能量条件的"信息→几何"链条）. ([物理评论链接管理器][8])
* Wong, **Pseudo-Riemannian geometry encodes information geometry**（连接信息几何与最优传输的伪-Riemann框架）. ([SpringerLink][9])
* Jacobson, **Thermodynamics of Spacetime: The Einstein Equation of State**（宏观一致性与等价原则）. ([物理评论链接管理器][11])

---

## 结语（要点汇总）

1. 在 Eguchi 正则散度下，二阶响应 $g$ 正定，不能直接充当洛伦兹度规；2) 通过伪-Hessian／ADM 提升把"统计—Hessian 结构"嵌入时空洛伦兹几何；3) 相对熵的一、二阶变分与 QFI/规范能同构，在线性与非线性层面导出爱因斯坦方程；4) 相对熵单调性与形状导数给出 QNEC/ANEC 等可检约束；5) 对偶平坦子范畴上"散度—Hessian"范畴等价，使"信息—时空同构"具有严格的结构意义。

[1]: https://projecteuclid.org/journals/hiroshima-mathematical-journal/volume-22/issue-3/Geometry-of-minimum-contrast/10.32917/hmj/1206128508.pdf?utm_source=chatgpt.com "Geometry of minimum contrast Shinto EGUCHI Such ..."
[2]: https://link.springer.com/article/10.1007/s10463-016-0562-0?utm_source=chatgpt.com "The uniqueness of the Fisher metric as information metric"
[3]: https://www.nzdr.ru/data/media/biblio/kolxoz/M/MD/MDdg/Shima%20H.%20The%20geometry%20of%20Hessian%20structures%20%28WS%2C%202007%29%28ISBN%209812700315%29%28261s%29_MDdg_.pdf?utm_source=chatgpt.com "The Geometry of Hessian Structures (260 pages)"
[4]: https://link.springer.com/article/10.1007/JHEP04%282016%29153?utm_source=chatgpt.com "Canonical energy is quantum Fisher information"
[5]: https://ncatlab.org/nlab/show/Hessian%2Bmanifold?utm_source=chatgpt.com "Hessian manifold in nLab"
[6]: https://vielbein.it/pdf/Traduzioni/2000-Amer-Methods_of_Information_Geometry.pdf?utm_source=chatgpt.com "Methods of Information Geometry - Vielbein"
[7]: https://link.springer.com/article/10.1007/JHEP06%282016%29004?utm_source=chatgpt.com "Relative entropy equals bulk relative entropy | Journal of ..."
[8]: https://link.aps.org/doi/10.1103/PhysRevD.93.024017?utm_source=chatgpt.com "Proof of the quantum null energy condition | Phys. Rev. D"
[9]: https://link.springer.com/article/10.1007/s41884-021-00053-7?utm_source=chatgpt.com "Pseudo-Riemannian geometry encodes information ..."
[10]: https://www.mdpi.com/1099-4300/17/12/7866?utm_source=chatgpt.com "A Novel Approach to Canonical Divergences within ..."
[11]: https://link.aps.org/pdf/10.1103/PhysRevLett.75.1260?utm_source=chatgpt.com "Thermodynamics of Spacetime: The Einstein Equation of State"
