# 统一计算宇宙终对象

离散复杂性几何、信息几何、多观察者因果网与能力–风险结构

---

## 摘要

本文在此前"计算宇宙"系列工作的基础上,构造一个具有明确范畴意义的**统一计算宇宙终对象**。前文已经将计算宇宙公理化为四元组

$$
U_{\mathrm{comp}}
=
(X,\mathsf T,\mathsf C,\mathsf I),
$$

并在其上建立了:离散复杂性几何(复杂性距离、体积增长与离散 Ricci 曲率)、离散信息几何(任务信息流形 $(\mathcal S_Q,g_Q)$ 与嵌入 $\Phi_Q$)、统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 与时间–信息–复杂性联合变分原理、多观察者共识几何与因果网、拓扑复杂性与不可判定性,以及普适灾难安全性与能力–风险前沿的理论。

本文的目标是将这些离散与连续、几何与逻辑、单观察者与多观察者、能力与风险的结构统一为一个单一的范畴对象

$$
\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
$$

——称为**统一计算宇宙终对象**(terminal computational universe object)。具体地,我们执行如下步骤:

1. 定义带统一时间刻度的计算宇宙范畴 $\mathbf{CompUniv}_\kappa$:对象是满足公理的计算宇宙 $U_{\mathrm{comp}}$,态射是同时保持复杂性几何、信息几何与灾难规范的"安全模拟映射"。

2. 在该范畴上构造一个 2–层结构:一层为离散配置–事件–因果小钻石层;一层为连续控制–信息几何层,并在上面安置多观察者网络、知识图谱族与能力–风险前沿。

3. 证明存在一个对象

$$
\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
=
\big(
\mathfrak X,\,
\mathfrak G_{\mathrm{comp}},\,
\mathfrak G_{\mathrm{info}},\,
\mathfrak E_{\mathrm{obs}},\,
\mathfrak S_{\mathrm{cat}},\,
\mathfrak F_{\mathrm{CR}}
\big),
$$

以及对每个 $U_{\mathrm{comp}} \in \mathbf{CompUniv}_\kappa$ 的"收缩"态射

$$
F_{U} : U_{\mathrm{comp}} \to \mathfrak U_{\mathrm{comp}}^{\mathrm{term}},
$$

使得:

* $F_U$ 在离散层面为配置–事件–小钻石的嵌入,在连续层面为控制–信息–观察者状态的嵌入;
* $F_U$ 保持复杂性距离与统一时间刻度(至多线性重标度);
* $F_U$ 使得所有任务信息几何与多观察者共识几何成为 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 上某类"子流形–子网";
* $F_U$ 将灾难规范与能力–风险前沿映射为 $\mathfrak S_{\mathrm{cat}}$ 与 $\mathfrak F_{\mathrm{CR}}$ 的子结构。

4. 证明在自然的 2–范畴意义下(态射之间允许自然变换),$\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 满足"终对象"性质:对任意两个这样的统一对象之间的态射存在唯一(在自然同构意义下)因子分解。

5. 最后利用此前已建立的物理宇宙–计算宇宙范畴等价,构造统一物理宇宙终对象 $\mathfrak U_{\mathrm{phys}}^{\mathrm{term}}$ 与 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 的对应,并说明两者在统一时间刻度、边界小钻石、观察者网络与能力–风险结构下是等价的终对象。

本文从而给出一个在纯离散、公理化框架下的"宇宙作为计算"的终极统一描述:所有具体的有限或局部计算宇宙都通过安全–几何–信息兼容的态射收缩到同一个统一计算宇宙终对象,后者在范畴论、几何与逻辑层面同时扮演终对象的角色。

---

## 2 统一时间刻度下的计算宇宙 2–范畴

本节将此前零散的结构整理为一个带 2–态射的 2–范畴框架。

### 2.1 带统一时间刻度的计算宇宙对象

**定义 2.1(带统一时间刻度的计算宇宙)**

一个带统一时间刻度的计算宇宙对象是七元组

$$
\widehat U_{\mathrm{comp}}
=
(X,\mathsf T,\mathsf C,\mathsf I;\,
\mathcal M,G;\,
\mathcal S_Q,g_Q),
$$

其中:

1. $(X,\mathsf T,\mathsf C,\mathsf I)$ 为满足此前公理的计算宇宙:

   * $X$ 可数;
   * $\mathsf T \subset X\times X$ 局域有限度;
   * $\mathsf C$ 单步代价正且路径加性;
   * $\mathsf I$ 为任务信息质量基准。

2. $(\mathcal M,G)$ 为由统一时间刻度散射母尺构造出的控制流形与复杂性度量,满足离散复杂性距离 $d_{\mathrm{comp}}$ 的 Riemann 极限性质:对每个局域可达区域存在细化族 $\{X^{(h)}\}$ 与映射 $\Phi_h:X^{(h)}\to\mathcal M$,使得

$$
d_{\mathrm{comp}}^{(h)}(x,y)
\to
d_G\big(\Phi_h(x),\Phi_h(y)\big).
$$

3. $(\mathcal S_Q,g_Q)$ 为任务 $Q$ 的信息流形与 Fisher 信息度量,存在嵌入

$$
\Phi_Q:X\to\mathcal S_Q,
$$

使得离散 Jensen–Shannon 信息距离 $d_{\mathrm{JS},Q}(x,y)$ 在局部上与 $d_{\mathcal S_Q}\big(\Phi_Q(x),\Phi_Q(y)\big)$ 一致。

我们称这类对象构成的范畴为 $\mathbf{CompUniv}_\kappa$ 的"0–层对象"。

### 2.2 安全–几何–信息兼容的 1–态射

**定义 2.2(安全–几何–信息兼容的模拟态射)**

给定两个带统一时间刻度的计算宇宙

$$
\widehat U_{\mathrm{comp}}
=
(X,\mathsf T,\mathsf C,\mathsf I;\mathcal M,G;\mathcal S_Q,g_Q),
$$

$$
\widehat U_{\mathrm{comp}}'
=
(X',\mathsf T',\mathsf C',\mathsf I';\mathcal M',G';\mathcal S'_Q,g'_Q),
$$

一个 1–态射

$$
F:\widehat U_{\mathrm{comp}} \to \widehat U_{\mathrm{comp}}'
$$

由以下数据组成:

1. 配置映射 $f_X:X\to X'$,为此前定义的模拟映射(保持步进结构、代价控制与信息质量单调),存在常数 $\alpha_X,\beta_X>0$ 与单调函数 $\Psi$ 使得
   $$
   (x,y)\in\mathsf T \Rightarrow (f_X(x),f_X(y))\in\mathsf T',
   $$
   $$
   d_{\mathrm{comp}}'(f_X(x),f_X(y)) \le \alpha_X d_{\mathrm{comp}}(x,y)+\beta_X,
   $$
   $$
   \mathsf I(x) \le \Psi\big(\mathsf I'(f_X(x))\big).
   $$

2. 控制流形映射 $f_{\mathcal M}:\mathcal M\to\mathcal M'$,对度量 $G,G'$ 满足 Lipschitz–双侧控制:存在 $\alpha_{\mathcal M},\beta_{\mathcal M}>0$ 使得
   $$
   \alpha_{\mathcal M} G_\theta(v,v)
   \le
   G'_{f_{\mathcal M}(\theta)}\big( \mathrm d f_{\mathcal M} v,\mathrm d f_{\mathcal M} v \big)
   \le
   \beta_{\mathcal M} G_\theta(v,v).
   $$

3. 信息流形映射 $f_{\mathcal S}:\mathcal S_Q\to\mathcal S'_Q$,对 Fisher 度量满足类似的 Lipschitz–双侧控制,并与 $f_X$ 兼容,即存在自然变换 $\eta_X$ 使得
   $$
   f_{\mathcal S}\circ \Phi_Q
   \simeq
   \Phi'_Q\circ f_X.
   $$

4. 安全规范兼容性:若在 $\widehat U_{\mathrm{comp}}$ 上存在灾难集合 $C_{\mathrm{cat}} \subset X$,则其像 $C_{\mathrm{cat}}' = f_X(C_{\mathrm{cat}}) \subset X'$ 仍为灾难集合,且 $F$ 不将安全点映入灾难点,即可见的安全–灾难分区在映射下保持或"向安全一侧变钝"。

这样的 1–态射同时保持离散–连续几何与灾难规范。所有对象与 1–态射构成范畴 $\mathbf{CompUniv}_\kappa$。

### 2.3 2–态射与自然变换

在控制与信息流形层,两个 1–态射之间可能存在"连续形变",对应到范畴论即为 2–态射——自然变换。

**定义 2.3(自然变换作为 2–态射)**

给定两个 1–态射

$$
F,G : \widehat U_{\mathrm{comp}}\to \widehat U_{\mathrm{comp}}',
$$

一个 2–态射

$$
\Xi: F \Rightarrow G
$$

包含:

1. 一个配置侧自然变换 $\Xi_X$,通常是 $X'$ 上的一族局域可逆映射,使得 $G_X \simeq \Xi_X \circ F_X$;
2. 控制与信息侧的自然变换 $\Xi_{\mathcal M},\Xi_{\mathcal S}$,给予在度量兼容意义下 $G_{\mathcal M} \simeq \Xi_{\mathcal M}\circ F_{\mathcal M}$、$G_{\mathcal S} \simeq \Xi_{\mathcal S}\circ F_{\mathcal S}$;
3. 安全结构上不破坏灾难集合与能力–风险前沿的粗粒结构。

如此,$\mathbf{CompUniv}_\kappa$ 具有 2–范畴结构。

---

## 3 统一计算宇宙终对象的结构数据

本节给出统一计算宇宙终对象

$$
\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
$$

的具体组成:从离散配置–事件–小钻石到连续控制–信息–观察者–能力–风险。

### 3.1 离散层:极大配置宇宙与事件–小钻石结构

**定义 3.1(极大配置宇宙)**

令 $\mathfrak X$ 为在某个大基数控制下的"所有可数配置集及其有限表示的归并",形式上可通过 Grothendieck 宇宙 $\mathcal U$ 与集合论构造为

$$
\mathfrak X
=
\bigcup_{U_{\mathrm{comp}}\in\mathbf{CompUniv}_\kappa}
\iota_U(X),
$$

其中 $\iota_U$ 为将各个 $X$ 嵌入一个公共超集的嵌入。对 $\mathfrak X$ 定义统一的转移关系

$$
\mathsf T_\infty
=
\bigcup_{U_{\mathrm{comp}}} \iota_U(\mathsf T_U),
$$

代价函数

$$
\mathsf C_\infty
=
\bigcup_{U_{\mathrm{comp}}} \iota_U(\mathsf C_U),
$$

在矛盾处通过等价类识别(即将不同宇宙中几何等价的更新规则合并为单一对象)。从而得到一个包含所有局部计算结构的"极大全局复杂性图"

$$
\mathfrak G_{\mathrm{comp}}^{(1)}
=
(\mathfrak X,\mathsf T_\infty,\mathsf C_\infty).
$$

在事件层

$$
\mathfrak E
=
\mathfrak X\times\mathbb N,
$$

可以定义统一的因果偏序与复杂性光锥;由此任意有限预算因果小钻石 $\Diamond$ 都可视为 $\mathfrak G_{\mathrm{comp}}^{(1)}$ 的子图。

### 3.2 连续层:统一控制流形与信息流形的终对象

在控制与信息几何层,前文已经构造了对每个 $\widehat U_{\mathrm{comp}}$ 的控制流形 $(\mathcal M_U,G_U)$ 与信息流形 $(\mathcal S_{Q,U},g_{Q,U})$。

**定义 3.2(统一控制流形终对象)**

令

$$
\mathfrak M
=
\coprod_{U_{\mathrm{comp}}}
\mathcal M_U \Big/ \sim,
$$

其中 $\sim$ 为"时间刻度–复杂性等距等价":若存在控制–散射实现的等距嵌入,则将相应点识别。通过这一归并得到一个大流形或堆栈式对象 $\mathfrak M$,带统一度量 $\mathfrak G$,在局部上与各 $G_U$ 一致。

**定义 3.3(统一信息流形终对象)**

类似地对所有任务 $Q$ 与宇宙 $U_{\mathrm{comp}}$,构造信息流形族 $\mathcal S_{Q,U}$ 并做类似归并,得到统一信息流形

$$
\mathfrak S
=
\coprod_{Q,U}
\mathcal S_{Q,U} \Big/ \sim,
$$

携带分段 Fisher 度量 $\mathfrak g$。

这样,任何具体计算宇宙的控制–信息几何都可以嵌入 $(\mathfrak M,\mathfrak G)$ 与 $(\mathfrak S,\mathfrak g)$ 中作为子流形;在统一时间刻度母尺与散射结构下,这些嵌入保持测地结构与信息结构。

### 3.3 多观察者网络层

以单观察者对象

$$
O = (M_{\mathrm{int}},\Sigma_{\mathrm{obs}},\Sigma_{\mathrm{act}},\mathcal P,\mathcal U)
$$

为基本单元,将所有可数观察者族在统一计算宇宙中视为点 $(\theta,\phi,m,\mathcal G,A)$ 的集合。

**定义 3.4(统一观察者状态空间)**

定义

$$
\mathfrak E_{\mathrm{obs}}
=
\bigcup_{U_{\mathrm{comp}},\mathcal O}
\Big(
\prod_{i\in I} \mathcal E_Q^{(i)}
\times
M_{\mathrm{int}}^{(i)}
\times
\mathfrak G^{(i)}
\times
\mathfrak A^{(i)}
\Big) \Big/ \sim,
$$

其中 $\mathcal E_Q^{(i)} = \mathcal M_U^{(i)}\times\mathcal S_{Q,U}^{(i)}$,$\mathfrak G^{(i)}$ 为知识图谱空间,$\mathfrak A^{(i)}$ 为注意力配置空间,$\sim$ 为将几何等价与策略等价的状态识别。

联合度量由各 $G_U,g_{Q,U}$ 的和与知识图谱谱距离构成。

### 3.4 灾难规范与能力–风险前沿层

对所有计算宇宙中定义的灾难规范与能力–风险结构进行类似的归并。

**定义 3.5(统一灾难规范层)**

定义灾难规范族

$$
\mathfrak S_{\mathrm{cat}}
=
\bigcup_{U_{\mathrm{comp}}}
\{(X_{0,U},C_{\mathrm{cat},U})\}
\Big/ \sim,
$$

其中等价关系将在统一嵌入下等价的初态集合与灾难集合识别。

**定义 3.6(统一能力–风险前沿层)**

对每个 $(U_{\mathrm{comp}},Q)$,能力–风险前沿为 $\mathcal F_{\mathrm{CR}}^{(U,Q)}\subset\mathbb R\times[0,1]$。将所有这些前沿作为参数化族嵌入统一策略空间上,得到整体结构

$$
\mathfrak F_{\mathrm{CR}}
=
\bigcup_{U,Q} \mathcal F_{\mathrm{CR}}^{(U,Q)} \times \{(U,Q)\} \Big/ \sim.
$$

在统一控制–观察者策略空间上,$\mathfrak F_{\mathrm{CR}}$ 是一个分片帕累托边界集合,描述在所有可能计算宇宙中的能力–风险极限曲线。

---

## 4 统一计算宇宙终对象与终对象性质

本节将上述所有层合并,给出统一计算宇宙终对象的定义,并证明其在 2–范畴意义下的终对象性质。

### 4.1 终对象的定义

**定义 4.1(统一计算宇宙终对象)**

统一计算宇宙终对象定义为十元组

$$
\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
=
\big(
\mathfrak X,\,
\mathsf T_\infty,\,
\mathsf C_\infty,\,
\mathsf I_\infty;\,
\mathfrak M,\mathfrak G;\,
\mathfrak S,\mathfrak g;\,
\mathfrak E_{\mathrm{obs}};\,
\mathfrak S_{\mathrm{cat}};\,
\mathfrak F_{\mathrm{CR}}
\big),
$$

其中各部分定义如 3.1–3.6。

直观上,$\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 同时包含:

* 所有局部可实现的配置与更新;
* 在统一时间刻度下所有控制路径的复杂性几何极限;
* 所有任务信息几何与观察者网络;
* 所有灾难规范与能力–风险前沿。

### 4.2 统一收缩函子

**定义 4.2(收缩 1–态射)**

对每个 $\widehat U_{\mathrm{comp}} \in \mathbf{CompUniv}_\kappa$,定义

$$
F_U : \widehat U_{\mathrm{comp}} \to \mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
$$

如下:

1. 配置嵌入

$$
f_X = \iota_U : X \hookrightarrow \mathfrak X.
$$

2. 控制流形嵌入

$$
f_{\mathcal M} : \mathcal M_U \hookrightarrow \mathfrak M,
$$

保持度量结构(至多常数重标度)。

3. 信息流形嵌入

$$
f_{\mathcal S} : \mathcal S_{Q,U} \hookrightarrow \mathfrak S,
$$

保持 Fisher 信息度量。

4. 观察者与知识图谱嵌入

$$
f_{\mathrm{obs}} : \text{ObsStates}(U_{\mathrm{comp}}) \hookrightarrow \mathfrak E_{\mathrm{obs}}.
$$

5. 灾难规范与能力–风险前沿嵌入

$$
f_{\mathrm{cat}} : (X_0,C_{\mathrm{cat}}) \mapsto \mathfrak S_{\mathrm{cat}},
\quad
f_{\mathrm{CR}} : \mathcal F_{\mathrm{CR}}^{(U,Q)} \mapsto \mathfrak F_{\mathrm{CR}}.
$$

组合起来 $F_U$ 即为一个安全–几何–信息兼容的 1–态射。

### 4.3 终对象性质

**定理 4.3(统一计算宇宙终对象的 2–终对象性)**

在 2–范畴 $\mathbf{CompUniv}_\kappa$ 中,$\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 是一个 2–终对象:

对每个对象 $\widehat U_{\mathrm{comp}}$,存在一个 1–态射

$$
F_U : \widehat U_{\mathrm{comp}} \to \mathfrak U_{\mathrm{comp}}^{\mathrm{term}},
$$

并且对任意另一个 1–态射

$$
G_U : \widehat U_{\mathrm{comp}} \to \mathfrak U_{\mathrm{comp}}^{\mathrm{term}},
$$

存在唯一(在 2–态射意义下)自然变换

$$
\Xi_U : G_U \Rightarrow F_U.
$$

**证明(概要)**

1. **存在性**:由 4.2 的构造,对每个 $\widehat U_{\mathrm{comp}}$ 可以显式定义 $F_U$ 为嵌入。

2. **唯一性(至自然变换)**:任何其它 1–态射 $G_U$ 必须将 $X$ 映射到 $\mathfrak X$ 的某个子集,并在控制–信息–观察者–能力–风险层保持结构。由于 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 按照"极大全局等价类"构造,对任何这样的 $G_U$ 都存在一个"等距–等价类"自然变换 $\Xi_U$ 将其拉回到规范嵌入 $F_U$:在每一层,都可以通过内部等距或局域酉变换消去多余自由度,使映射与 $F_U$ 同构。

3. **自然性**:对态射 $H:\widehat U_{\mathrm{comp}}\to\widehat V_{\mathrm{comp}}$,两侧合成 $F_V\circ H$ 与 $F_U$ 之间的自然变换由统一构造给出——这是 Grothendieck 宇宙中"包含–等距"结构的常规特性。

严格的 2–范畴证明需要在每一层检查兼容性,见附录 C。

---

## 5 与统一物理宇宙终对象的等价

前文已经构造物理宇宙范畴 $\mathbf{PhysUniv}^{\mathrm{QCA}}$ 与计算宇宙范畴 $\mathbf{CompUniv}^{\mathrm{phys}}$,并通过函子

$$
F : \mathbf{PhysUniv}^{\mathrm{QCA}} \to \mathbf{CompUniv}^{\mathrm{phys}},
\quad
G : \mathbf{CompUniv}^{\mathrm{phys}} \to \mathbf{PhysUniv}^{\mathrm{QCA}}
$$

证明两者范畴等价。在物理层,统一物理宇宙终对象 $\mathfrak U_{\mathrm{phys}}^{\mathrm{term}}$ 已通过散射时间刻度、边界时间几何与 Dirac–QCA 连续极限构造。

在当前场景下,由 $\mathbf{CompUniv}^{\mathrm{phys}} \hookrightarrow \mathbf{CompUniv}_\kappa$ 的包含与范畴等价,可以提升终对象关系:

**命题 5.1(终对象之间的等价)**

在统一时间刻度的约束下,统一物理宇宙终对象 $\mathfrak U_{\mathrm{phys}}^{\mathrm{term}}$ 与统一计算宇宙终对象 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 在 2–范畴意义下等价。

即存在一对 1–态射

$$
\mathcal F : \mathfrak U_{\mathrm{phys}}^{\mathrm{term}}
\to
\mathfrak U_{\mathrm{comp}}^{\mathrm{term}},
\quad
\mathcal G : \mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
\to
\mathfrak U_{\mathrm{phys}}^{\mathrm{term}},
$$

以及自然同构 2–态射

$$
\mathcal G\circ\mathcal F \simeq \mathrm{Id}_{\mathfrak U_{\mathrm{phys}}^{\mathrm{term}}},
\quad
\mathcal F\circ\mathcal G \simeq \mathrm{Id}_{\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}}.
$$

证明依赖于前文的范畴等价定理和终对象性质,见附录 D。

这意味着:"宇宙作为计算"的统一终对象与"宇宙作为统一时间–边界几何"的终对象是同一个 2–终对象在不同范畴中的呈现:一个以离散计算结构为主,一个以连续几何结构为主。

---

## 附录 A:统一配置–事件–小钻石层的技术细节

### A.1 极大配置宇宙的集合论构造

为避免大小悖论,我们在某个 Grothendieck 宇宙 $\mathcal U$ 内操作,令

$$
\mathcal X_0
=
\{X_U : U\in\mathbf{CompUniv}_\kappa\},
\quad
\mathcal T_0
=
\{\mathsf T_U,\mathsf C_U,\mathsf I_U\}.
$$

定义

$$
\mathfrak X
=
\bigsqcup_{U} (X_U\times\{U\}),
$$

再通过等距–等价关系 $\sim$ 识别"几何完全相同"的点对,得到商集

$$
\mathfrak X
=
\Big(
\bigsqcup_{U} X_U
\Big) \Big/ \sim.
$$

统一转移关系 $\mathsf T_\infty$ 与代价 $\mathsf C_\infty$ 通过类似的商构造得到。这一过程确保:

* 每个具体 $X_U$ 被嵌入 $\mathfrak X$;
* 在等距等价类中,不会重复计数相同的更新结构;
* 统一复杂性距离 $d_{\mathrm{comp},\infty}$ 在各子集上限制为原始距离。

### A.2 统一事件层与小钻石

事件层

$$
\mathfrak E = \mathfrak X\times\mathbb N
$$

上,统一更新关系

$$
\mathsf T_{\mathfrak E}
=
\{((x,k),(y,k+1)) : (x,y)\in\mathsf T_\infty\}
$$

与代价函数诱导复杂性光锥与小钻石定义与单一宇宙情形完全类同。

---

## 附录 B:统一控制与信息流形终对象的构造

### B.1 控制流形终对象的局域构造

对每个 $U_{\mathrm{comp}}$,控制流形 $\mathcal M_U$ 在局部与某个 Riemann 流形 $(\mathbb R^{d_U},G_U)$ 同构。我们对所有这样的局部片进行 disjoint union,再按"时间刻度–散射–控制结构等距"关系归并,得到统一控制流形 $\mathfrak M$。

在技术上,可定义等价关系:

$$
(\theta,U) \sim (\theta',U')
\iff
\exists\ \text{等距同构}\ \varphi:
\mathcal M_U\supset U \to U'\subset\mathcal M_{U'}
\ \text{使}\ \varphi(\theta)=\theta'.
$$

度量 $\mathfrak G$ 在等价类代表上由 $G_U$ 定义,等距等价保证一致性。

### B.2 信息流形终对象的构造

对所有 $Q,U$,信息流形 $(\mathcal S_{Q,U},g_{Q,U})$ 可通过相对熵二阶结构确定。与控制流形相同,通过 disjoint union 与 Fisher–等距等价关系归并得到 $(\mathfrak S,\mathfrak g)$。

---

## 附录 C:终对象 2–性质的形式证明纲要

### C.1 1–态射唯一性(至自然变换)

给定 $\widehat U_{\mathrm{comp}}$ 与两个 1–态射

$$
F_U,G_U : \widehat U_{\mathrm{comp}} \to \mathfrak U_{\mathrm{comp}}^{\mathrm{term}},
$$

比较其在各层的映射:

* 在配置层,由 $\mathfrak X$ 的等距–等价构造,$F_U$ 与 $G_U$ 的像必落在同一个等价类,故存在某个局域双射 $\Xi_X$ 使得 $G_X = \Xi_X\circ F_X$;
* 在控制与信息层,由 $\mathfrak M,\mathfrak S$ 的等距–等价构造,$F_{\mathcal M},G_{\mathcal M}$ 与 $F_{\mathcal S},G_{\mathcal S}$ 之间存在等距自然变换 $\Xi_{\mathcal M},\Xi_{\mathcal S}$;
* 在观察者与能力–风险层,类似的归并保证存在相应的自然变换。

将这些自然变换组合为 2–态射 $\Xi_U$ 即完成。

### C.2 2–终对象性

若存在另外一个候选终对象 $\mathfrak U'_{\mathrm{comp}}$,则从 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 出发的 1–态射 $H:\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}\to\mathfrak U'_{\mathrm{comp}}$ 与从 $\mathfrak U'_{\mathrm{comp}}$ 到 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 的 1–态射 $K$ 组合必须在 2–态射意义下成为恒等,因两者均具有"包含–归并–等距"结构。此即 2–终对象的标准论证。

---

## 附录 D:统一物理宇宙终对象与统一计算宇宙终对象的等价

在物理层,统一物理宇宙终对象

$$
\mathfrak U_{\mathrm{phys}}^{\mathrm{term}}
=
(M_\infty,g_\infty;\,
\mathcal F_\infty;\,
\kappa_\infty;\,
\mathsf S_\infty;\,
\cdots)
$$

通过类似的 Grothendieck 归并在物理宇宙范畴 $\mathbf{PhysUniv}^{\mathrm{QCA}}$ 中构造。此前已给出范畴等价

$$
F : \mathbf{PhysUniv}^{\mathrm{QCA}} \to \mathbf{CompUniv}^{\mathrm{phys}},
\quad
G : \mathbf{CompUniv}^{\mathrm{phys}} \to \mathbf{PhysUniv}^{\mathrm{QCA}}.
$$

通过将这些函子扩展到终对象层,可以构造

$$
\mathcal F : \mathfrak U_{\mathrm{phys}}^{\mathrm{term}}
\to
\mathfrak U_{\mathrm{comp}}^{\mathrm{term}},
\quad
\mathcal G : \mathfrak U_{\mathrm{comp}}^{\mathrm{term}}
\to
\mathfrak U_{\mathrm{phys}}^{\mathrm{term}},
$$

并利用终对象性质与等价性,得到自然同构

$$
\mathcal G\circ\mathcal F \simeq \mathrm{Id}_{\mathfrak U_{\mathrm{phys}}^{\mathrm{term}}},
\quad
\mathcal F\circ\mathcal G \simeq \mathrm{Id}_{\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}}.
$$

这从根本上说明:

* 把宇宙视为"统一时间刻度下的散射–边界几何终对象"与
* 把宇宙视为"统一时间刻度下的计算宇宙终对象"

是同一个数学对象在两个等价范畴中的双重呈现。
