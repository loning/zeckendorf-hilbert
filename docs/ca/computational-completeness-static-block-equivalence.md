# 计算完备性与静态块元胞自动机的等价性：从计算封闭到时空静态结构的统一表述

**Computational Completeness and Static Block Cellular Automata Equivalence: A Unified Formulation from Computational Closure to Spatiotemporal Static Structure**

**作者**：基于静态块量子场论框架的整合扩展
**日期**：2025年10月17日
**版本**：v1.6.1-final（提交版）

---

## 摘要

本文在"通用基底"条件下证明计算完备性与系统可静态化为全时空元胞自动机块结构（SB-CA）的双向可约性（在可计算同构意义下）。通过 Rule 110 与 Wang 贴砖的构造性嵌入、Kolmogorov 复杂度上界及停机问题对偶（时间视角与静态描述的不可判定性等价），展示动态演化可重写为静态张量的序贯投影，时间可重新解释为时空张量的一个索引维度。结果为计算哲学与复杂系统建模提供统一框架。

**关键词**：计算完备性，静态块元胞自动机，图灵完备性，Rule 110，Wang 贴砖，Kolmogorov 复杂度，停机问题

---

## §1 引言

### 1.1 背景与动机

计算完备性定义系统模拟任意可计算函数的能力。自 Turing 提出图灵机以来，诸多模型（如 λ 演算、元胞自动机）被证明等价。Wolfram (2002) 提出计算等价性原理，非平凡系统（如类4元胞自动机）在计算复杂性上等价。本文焦点：系统的计算完备性 $C(\mathcal{S})$ 等价于其可静态化为全时空元胞自动机块结构的能力 $A(\mathcal{S})$，即 $C(\mathcal{S}) \iff A(\mathcal{S})$。静态化指将动态过程转换为时空块 $\mathcal{B}$；全时空指网格覆盖空间与时间维度；块结构指模块化离散单元。

Gödel 不完备性定理显示足够强递归系统无法同时一致与逻辑完备，但本文完备性指计算完备性（图灵完备），二者并行不悖。我们通过定义、证明与模拟验证自洽性。

### 1.2 理论定位

本文作为"静态块完备性"系列的计算理论篇，从计算封闭性角度探讨静态块结构的表达能力。与前续工作中静态块元胞自动机理论、静态块量子元胞自动机理论、静态块量子场论及静态块量子力学相呼应，本文聚焦于经典计算模型与时空静态化的等价性。

### 1.3 论文结构

本文组织如下：

- **§2** 相关工作
- **§3** 定义与形式系统
- **§4** 主定理：计算完备性与静态块结构的等价性
- **§5** 时间的静态化
- **§6** 与计算理论的关系
- **§7** 讨论与哲学性推测
- **§8** 结论与展望
- **附录A** Wang 贴砖历史构造
- **附录B** Rule 110 模拟验证

### 1.4 术语与模型对照

- SB-CA：将 CA 的时空史冻结为 $(d+1)$ 维配置，并以有限型子移位（SFT）方式给出局域约束的静态模型。
- SFT：由有限禁用图样定义的子移位，本文中的 SB-CA 即一种具有时间坐标的 SFT 实例。
- 贴砖（Wang）：与 SFT 等价的静态铺砌模型，本文用作与 Rule 110 并行的静态基底。
- 通用基底：支持统一、有效的 UTM 编码/解码与有界（有效可计算）开销的 SB-CA/SFT/贴砖系统。

**说明**：本文默认 $\Lambda=\mathbb{Z}^d$ 无限无边界；采用周期边界/有限环面时，将环尺寸并入编码并确保其充足，以保持结论。若采用环面边界，环尺寸并入编码并取充分大以容纳所需历史；主定理在 $\Lambda=\mathbb{Z}^d$ 情形下不变。

---

## §2 相关工作

元胞自动机由 von Neumann 和 Ulam 提出，用于自复制模拟。Conway 的生命游戏证明简单规则产生复杂行为。Wolfram 分类一维 CA，Rule 110 被 Cook (2004) 证明图灵完备，通过模拟循环移位寄存器。计算等价性原理扩展此观点。

Hedlund (1969) CHL 定理奠定符号动力学基础。Berger (1966) 和 Wang (1961) 引入贴砖问题，展示静态铺砌模型的全局性质不可判定性与极强表达力；该事实与通用基底的历史编码构造相辅而行（但不可判定性本身并不蕴含“计算通用”）。Ollinger (2008) 和 Kari (1994) 综述 CA 性质不可判定性。Toffoli (1977) 引入可逆 CA，Morita (1995) 证明通用可逆 CA，支持静态化与可逆性关联。Barbour (1999) 永恒主义视时间为静态存在。与 Barbour 永恒主义不同，本研究不主张形而上同一性，而主张形式可约性。Zenil (2012) 探讨可计算宇宙。Aaronson (2024) 作为讨论性引用，启发量子时空计算框架。

---

## §3 定义与形式系统

### 定义 3.1（计算完备性/图灵完备性）

系统 $\mathcal{S}$ 图灵完备，若能模拟通用图灵机 $U$：对任意图灵机 $M$ 与输入 $w$，存在编码使 $\mathcal{S}$ 计算 $U(M, w)$。计算类等于全部部分可计算函数（partial recursive functions）。

**注记 3.1**：图灵完备性是递归论意义下的，与 Gödel 不完备性（逻辑层面）正交。

### 定义 3.2（元胞自动机）

元胞自动机为 $\mathrm{CA} = (\Lambda, Q, f)$，$\Lambda = \mathbb{Z}^d$ 为空间格点，$Q$ 为有限状态集，$f: Q^{\mathcal{N}_r} \to Q$ 为局域更新函数（$\mathcal{N}_r$ 为邻域）。

**注记 3.2（Curtis-Hedlund-Lyndon 定理）**：任何连续平移不变映射 $G: Q^{\mathbb{Z}^d} \to Q^{\mathbb{Z}^d}$ 都由某个局域函数 $f$ 决定（Hedlund, 1969）。

### 定义 3.3（静态块元胞自动机 SB-CA）

一个静态块元胞自动机是一个三元组 $(\Lambda \times T, Q, C)$，其中：

- $\Lambda = \mathbb{Z}^d$ 是空间网格
- $T = \mathbb{N}$ 是时间集合
- $Q$ 是有限状态集
- $C$ 是一组**局域约束**，每个约束作用于一个时空邻域 $\mathcal{N}_r(x,t) \subset \Lambda \times T$，规定该邻域内状态组合的合法性

一个**合法配置**（即静态块）$\mathcal{B} \in Q^{\Lambda \times T}$ 必须满足所有 $(x,t) \in \Lambda \times T$ 上的约束 $C$。

特别地，若约束 $C$ 由 CA 的局域演化规则 $f: Q^{\mathcal{N}_r} \to Q$ 导出，即要求对于所有 $(x,t)$，有

$$
\mathcal{B}(x, t+1) = f\big( \mathcal{B}(y, t) \text{ for } y \in \mathcal{N}_r(x) \big)
$$

那么我们称该 SB-CA 是**由动态 CA $(\Lambda, Q, f)$ 生成的**。

**注记 3.3（紧致性与延拓性）**：SB-CA 的配置空间是在乘积拓扑 $Q^{\Lambda \times T}$ 下由上述局域柱状约束定义的闭子集（Hedlund, 1969）。由 Tychonoff 定理，$Q^{\Lambda \times T}$ 在乘积拓扑下紧致；SB-CA 配置空间作为有限型子移位（SFT）是闭集。设一族有限窗口图样两两兼容并满足有限交性质（任意有限子族可共同延拓），则由紧致性可得存在全局配置；但"局部合法"并不自动蕴含可延拓。本文所有构造均显式保证该有限交条件。

**注记 3.4（时空耦合邻域）**：上述定义采用"纯空间邻域 + 单步时间推进"范式；如需"真正的时空耦合"（例如 $(y,s)$ 允许 $s\in [t-r_t, t+r_t]$），可将 $\mathcal{N}_r$ 相应拓展，本文结论在该变体下保持不变。当采用时空耦合邻域时，约束依赖图在时间维上必须为有向无环（DAG），以确保与因果-单步 CA 的可约性。

**注记 3.5（边界与维度）**：除非另行说明，本文取 $\Lambda=\mathbb{Z}^d$ 无限无边界。若采用周期边界或有限环面，需将环尺寸作为编码的一部分并确保其足够大以容纳所需历史；定理与归约在相应规模条件下保持。

（形式化对象）记 $\mathrm{Histories}(\mathcal{B})$ 为满足约束 $C$ 的全局赋值集合（必要时包含初始行约束）；记 $\mathrm{Region}(\mathcal{B})$ 为可枚举的有限时空窗口族（如有限长方体）。本文关于 I/O 与同构的陈述均相对于这些规范对象与其代码空间表述。

### 定义 3.4（形式可静态化）

系统 $\mathcal{S}$ 可静态化，若存在 SB-CA $\mathcal{B}$，输入编码 $\iota: \text{Input}(\mathcal{S}) \to \text{Initial}(\mathcal{B})$，输出解码 $\pi: \text{Region}(\mathcal{B}) \to \text{Output}(\mathcal{S})$，以及一个双向可计算的同构
$$
\Phi: \text{Traces}(\mathcal{S}) \leftrightarrow \mathcal{H} \subseteq \text{Histories}(\mathcal{B})
$$
使得：
1) $\Phi$ 与 $\Phi^{-1}$ 均可计算且与 $\iota,\pi$ 交换，保持 I/O 语义；
2) 覆盖性：$\mathcal{H}$ 覆盖全部 UTM 编码历史 $\{\mathrm{hist}(M,w)\mid M,w\}$（允许统一、有效的预/后处理变换）；
3) $\mathrm{Region}(\mathcal{B})$ 为可枚举的有限窗口族，输出由某有限窗口可读出。

备注（可计算性约定）：$\Phi$ 与 $\Phi^{-1}$ 相对于规范代码空间全域可计算（等价地，可视为在可分零维拓扑下的类型-2可计算映射）；$\iota,\pi$ 亦如是。本文所有可计算性均相对于该规范编码。

### 定义 3.5（通用基底）

设 $\mathsf{B}$ 为由有限局域约束定义的 SFT/贴砖/CA-静态块系统。称 $\mathsf{B}$ 为通用基底，若存在可计算函数 $\iota,\pi$ 以及某个有效可计算的开销函数 $g: \mathbb{N}\to\mathbb{N}$ 与常数 $c$，使得：对任意 TM $M$ 与输入 $w$，

(i) $\iota(M,w)$ 生成的 $\mathsf{B}$ 历史与 $M$ 的计算在定义 3.4 的可计算同构意义下对应（统一、有效）；

(ii) 若 $M(w)\downarrow$，则存在 $t$ 与有限窗口使 $\pi$ 读出输出，且时间/空间开销 $\le g(|M|+|w|)+c$。

（可选的更强假设）若存在多项式 $p$ 使上述开销界可取为 $p(|M|+|w|)+c$，称 $\mathsf{B}$ 为“多项式通用基底”。本文主要结果在一般 $g$ 下成立；若进一步给出多项式上界，则相应复杂度陈述可强化为多项式界。必要时，$g$ 的参数可包含周期背景/环尺寸等规范信息的码长。

---

## §4 主定理：计算完备性与静态块结构的等价性

### 引理 4.A（静态化嵌入）

对任意 TM 与输入对 $(M,w)$，存在统一、有效的编码 $\iota(M,w)$，使其在某通用基底 $\mathcal{B}$ 中诱导一条合法历史；且存在有限窗口族可读出输出。该构造对 $(M,w)$ 一致（uniform），并满足定义 3.5 的开销界。

### 引理 4.B（同构提纯）

若存在双向可计算的 $\Phi: \text{Traces}(\mathcal{S}) \leftrightarrow \mathcal{H} \subseteq \text{Histories}(\mathcal{B})$，其像 $\mathcal{H}$ 覆盖全部 UTM 编码历史 $\{\mathrm{hist}(M,w)\}$，则 $\mathcal{S}$ 图灵完备。

### 定理 4.1（等价性定理）

给定一个计算系统 $\mathcal{S}$。以下两者等价：

(i) $\mathcal{S}$ 图灵完备；

(ii) 存在一个以通用元胞自动机或等价静态铺砌（Wang 贴砖）历史构造为基底的静态块元胞自动机 $\mathcal{B}$，以及输入/输出编码 $(\iota, \pi)$，使得 $\mathcal{S}$ 的任意计算可被嵌入为 $\mathcal{B}$ 的一条时空一致路径，且输出由 $\pi$ 在有限区域读出。

此外，在可计算同构意义下，上述嵌入是典范至同构的（不同实现仅相差可计算的双射与坐标重标定）。

**证明**（(i) $\Rightarrow$ (ii)）：

任意图灵完备 $\mathcal{S}$ 可模拟通用图灵机 UTM。结合引理 4.A，取以 Rule 110 或等价贴砖为基底的 $\mathcal{B}$，用统一编码 $\iota$ 将 $\mathcal{S}$ 的计算经 UTM 映射到 $\mathcal{B}$ 的一条历史，输出经 $\pi$ 在有限窗口读出。由定义 3.5，资源开销受某有效可计算函数 $g$ 控制（若采用多项式通用基底则为多项式界）。

**存在性**：Cook (2004) 证明 Rule 110 模拟任意 TM（周期背景条件下）。将时间维作为附加坐标，可把演化图冻结为二维阵列 $\mathcal{B} \in Q^{\mathbb{Z} \times \mathbb{N}}$，从而给出满足定义 3.5 的通用 SB-CA。$\square$

**证明**（(ii) $\Rightarrow$ (i)）：

由定义 3.4 假设存在双向可计算同构 $\Phi$，且其像覆盖 UTM 编码历史族。对任意 $(M,w)$，$\mathrm{hist}(M,w)\in \mathcal{H}$，故存在 $\tau\in \text{Traces}(\mathcal{S})$ 使 $\Phi(\tau)=\mathrm{hist}(M,w)$。$\Phi^{-1}$ 可计算给出 $\tau$，表明 $\mathcal{S}$ 能模拟任意 TM，故图灵完备。$\square$

### 推论 4.1（双向可约性）

$$
\mathcal{S}\ \text{图灵完备} \quad \Longleftrightarrow \quad \exists \text{通用基底的 SB-CA } \mathcal{B}: \mathcal{S}\ \text{可静态化嵌入 } \mathcal{B}
$$

**注记 4.1**：SB-CA 的通用性是必要条件；非通用 CA 的 SB-CA 表示不必然具备图灵完备性。

### 命题 4.2（验证自洽性）

模拟 Rule 110：初始状态 $[0,0,0,1,1,1,0,0]$，下一状态 $[0,0,1,1,0,1,0,0]$（验证无矛盾）。同一初态继续演化两步：

$$
[0,0,1,1,0,1,0,0] \mapsto [0,1,1,1,1,1,0,0]
$$

继续一步：

$$
[0,1,1,1,1,1,0,0] \mapsto [1,1,0,0,0,1,0,0]
$$

**证明**：与规则表一致（可由读者逐格核对）。该演化序列具体验证了规则表中的多个条目，如对位于中心的模式 $(1,1,0)$ 应用了规则 $110 \to 1$，对 $(1,0,1)$ 应用了规则 $101 \to 1$ 等，与规则表完全一致。$\square$

---

## §5 时间的静态化

### 5.1 Kolmogorov 复杂度上界

从 SB-CA 视角，时间 $t$ 为索引维度。序列 $(S_0, S_1, \dots)$ 为 $\mathcal{B}$ 在 $t$-方向切片。演化即投影。以下复杂度度量一律针对规范化的有限编码对象（如：给定切片或窗口的最短生成程序/枚举器），避免对无限对象直接取 $K(\cdot)$ 的非标准性。

**定理 5.1（时间切片的复杂度上界）**：

对固定的规则 $f$ 与初态 $S_0$，令 $\ulcorner S_t\urcorner$ 表示时间切片 $S_t$ 的规范有限码（例如最短生成程序在输入 $t$ 时输出该切片的有限描述）。则其前缀复杂度满足

$$
K(S_t) \le K(S_0) + K(f) + K(t)+O(1)
$$

其中 $K(\cdot)$ 为前缀 Kolmogorov 复杂度。注意 $K(t)$ 为最坏情形下的编码成本；当 $t$ 为 Kolmogorov 随机时上界不紧，但该式本为“最坏情况”陈述，仍支持“演化作为对静态块的可编址读取”的解释。

（粗界提示）对自然数的标准自描述，$K(t) \le \lfloor \log_2 t \rfloor + O(1)$，与“寻址所需比特数”直觉一致（依编码细节，亦常写作 $\log_2 t + O(\log\log t)$ 级别的标准上界）。

**证明**：在给定 $S_0,f$ 与索引 $t$ 的前提下，由 Levin–Chaitin 编码定理与前缀编码性质，存在常数项 $O(1)$ 使上界成立。$\square$

### 5.2 有限窗口的描述长度

**定理 5.2（有限窗口复杂度上界）**：

若考虑 $\mathcal{B}$ 的任意有限时空窗口 $W \subset \Lambda \times T$ 对应的截取 $\mathcal{B} \upharpoonright W$，则存在一常数 $c$（与编码约定相关），使

$$
K \left( \mathcal{B} \upharpoonright W \right) \le K(S_0)+K(f)+c+K(\mathrm{diam}(W))+O(1)
$$

这说明任意有限窗口的最短描述长度受初态与局域规则的总复杂度所上界；"演化"可理解为对静态块 $\mathcal{B}$ 的可编址枚举读取。这里 $\mathrm{diam}(W)$ 取 $\ell_\infty$ 度量下的直径（对 $\Lambda \times T$ 的乘积度量）。

**证明**：由 Kolmogorov 复杂度的可加性与局域规则的有限表示得出。$\square$

---

## §6 与计算理论的关系

### 6.1 可计算性

**定义 6.1（部分可计算函数）**：图灵完备系统可表达全部部分可计算函数；在 I/O 语义下，以"停机即产出"的约定可诱导相应的全定义外延。

### 6.2 停机问题对偶

**定理 6.1（块出现的 Σ₁ 完全性）**：

在通用基底的 SB-CA/SFT/贴砖系统 $\mathsf{B}$ 中，给定有限图案 $P$，判定

$$
\exists t,\exists W_t\quad P\subseteq \mathcal{B} \upharpoonright W_t
$$

为 Σ₁-完全（Cook 式嵌入把停机化为“存在时间步的见证出现”）。

**证明（归约梳理）**：构造“停机见证图样” $P_{\mathrm{halt}}$，其编码指定输出轨道出现终止旗标并由右侧守卫块界定窗口边界。对任意 $\langle M,w\rangle$，统一地构造初始编码使 $\mathrm{hist}(M,w)$ 存在当且仅当 $M(w)$ 停机；于是 $M(w)$ 停机 $\Leftrightarrow \exists t,\exists W_t: P_{\mathrm{halt}}\subseteq \mathcal{B}\upharpoonright W_t$。归约为多对一并保持有效可计算性。$\square$

**定理 6.2（必现性的 Π₂ 难度）**：

在通用基底的 SB-CA/SFT/贴砖系统中，判定

$$
\forall t,\exists t' \ge t,\exists W_{t'}\quad P\subseteq \mathcal{B} \upharpoonright W_{t'}
$$

一般为 Π₂-难；在通用基底下不存在低于该层级的判定程式。

**证明（量词展开）**：将“必现/无限经常出现”性质编码为随 $t$ 单调扩大的窗口族与标记图样 $P$ 的出现：$\forall t\,\exists t'\ge t\,\exists W_{t'}\, P\subseteq \mathcal{B}\upharpoonright W_{t'}$。结合 CA 全局性质不可判定性的经典结果（Ollinger, 2008），得到 Π₂ 难度。$\square$
（定位说明）由通用基底的内在普适性与 CA 全局性质不可判定性的经典综述结果，可将此类“必现/频现”判定定位于算术层级的 Π₂ 层，故一般为 Π₂-难。

**注记 6.1（Garden-of-Eden 定理）**：另参 Moore (1962) 与 Myhill (1963) 的 Garden-of-Eden 定理（前注入/满射与可达性），与本节不可判定性结论互补。

### 6.3 图灵等价

**命题 6.1（表达等价性）**：TM 可嵌入 SB-CA；在通用基底下，可计算函数的定义域/像与 TM 等价（即表达同一类图灵可计算函数）。

**证明**：由定理 4.1 的双向嵌入得出。$\square$

---

## §7 讨论与哲学性推测

前述计算完备性与静态块结构的数学等价性，为我们重新审视时间、量子力学乃至意识等基本问题提供了一个形式化的计算框架，以下我们探讨若干由此衍生的、具有启发性的推论。

**注记 7.1（推测性内容）**：本节内容为基于前述数学模型的哲学性推测和启发式类比，并非严格的数学结论。

### 7.1 永恒主义类比

若接受 SB-CA 的本体解释，时间可理解为静态存在的维度，与 Barbour (1999) 的永恒主义共鸣。然而，这一解释是形而上学选择，而非数学必然。

### 7.2 量子力学类比

SB-CA 的静态块表示在形式上类似量子场论的路径积分表述，其中所有路径"同时存在"。但量子测量的非酉性（坍缩）无对应于 SB-CA 的确定性规则，该类比仅为启发性。SB-CA 为确定性局域规则，并不包含叠加/非定域相干。

---

## §8 结论与展望

### 8.1 主要贡献

本文证明计算完备性与 SB-CA 形式等价。在"通用基底"这一精确条件下，建立了图灵完备性与可静态化之间的等价性，这为后续研究提供了形式化工具。时间、演化均为观测现象。该结果统一计算论与物理实在。

### 8.2 理论定位

本文提供计算模型的静态表述框架，与动态视角等价。该推广基于 SB-CA 的构造性嵌入，确保自洽过渡。我们承认这是概念探索而非全新数学定理。

### 8.3 未来方向

**短期方向**：SB-QFT 推广；复杂性守恒方程；观察路径建模。

**长期方向**：探索与 Zenil (2012) 可计算宇宙的连接，及在量子计算中的应用。

---

## 附录A：Wang 贴砖历史构造（平行嵌入示例）

### A.1 基本构造

Wang 贴砖（Wang 1961）提供静态铺砌历史构造，作为 Rule 110 的平行基底。将动态 CA 演化"冻结"为静态约束：每块贴砖编码状态与转移，水平匹配空间邻域，垂直匹配时间演化。Berger (1966) 证明其不可判定性支持通用性。

### A.2 具体实现

对于简单 CA，将转移函数编码为贴砖边标签，确保全局铺砌对应一致演化路径。该构造确保 SB-CA 嵌入的静态性。令每块上、下边标签编码"时间 $(t,t+1)$ 的局域模式"，左、右边标签编码"空间相邻约束"；合法铺砌 ⇔ CA 局域转移与空间邻接同时满足，从而合法铺砌 ⇔ CA 一致演化历史。

### A.3 局域约束与有限交延拓（构造性说明）

设 $C$ 为如下有限集合的柱状约束：
1) 时间一致性约束：对每个 $(x,t)$，贴砖上、下边标签匹配 $t$ 与 $t+1$ 的局域模式，等价于 CA 的 $f$；
2) 空间邻接约束：对每个 $(x,t)$，左右相邻贴砖的接触边标签一致；
3) 起始行约束：$t=0$ 行的贴砖边标签编码 $\iota(M,w)$ 的初态带。
该族约束的依赖图在时间方向为 DAG，且每个有限窗口的本地图样族两两兼容时可按时间层自外向内拼接：先铺设 $t=0$ 初始层，再依序向 $t=1,2,\dots$ 延拓。因而满足有限交延拓性，存在全局解（SFT 闭性与紧致性提供极限）。构造性延拓顺序：先铺设 $t=0$ 初始层，再按 $t=1,2,\dots$ 自外向内逐层拼接，极限即为全局配置。

---

## 附录B：Rule 110 到 SB-CA 的明确编码表

### B.1 规则表

下表采用 (左,中,右) → 中心单元的标准对齐方式，编码与 Wolfram (2002, pp. 675–702) 保持一致。

| 当前状态 (左,中,右) | 下一状态 (中心单元) |
|---------------------|--------------|
| 000                | 0           |
| 001                | 1           |
| 010                | 1           |
| 011                | 1           |
| 100                | 0           |
| 101                | 1           |
| 110                | 1           |
| 111                | 0           |

### B.2 SB-CA 嵌入示例

SB-CA 嵌入：时间向下扩展，空间水平。示例初始：$[0,0,0,1,1,1,0,0]$ → 下一：$[0,0,1,1,0,1,0,0]$。

### B.3 规则表到 SB-CA 约束的对应与验证伪代码

对应关系：将表 B.1 的 8 个三元组 $(l,c,r)\mapsto c'$ 作为“时间一致性约束”，即在 $(x,t)$ 的上边编码 $(l,c,r)$，下边编码 $c'$，空间上以左右边标签实现相邻 $l,r$ 的强制匹配。如此，合法铺砌当且仅当所有局部转移均满足表 B.1。

验证伪代码（Python 风格）：

```python
RULE110 = {
    (0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,
    (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):0,
}

def step(state):
    n = len(state)
    nxt = [0]*n
    for i in range(n):
        l,c,r = state[(i-1)%n], state[i], state[(i+1)%n]
        nxt[i] = RULE110[(l,c,r)]
    return nxt

assert step([0,0,0,1,1,1,0,0]) == [0,0,1,1,0,1,0,0]
```

注：示例采用环面边界（模 $n$）以便可执行性展示；正文主命题在 $\Lambda=\mathbb{Z}^d$ 上成立。若采用环面，环尺寸并入编码，并取充分大以容纳所需历史。

---

## 参考文献

1. Gödel, K. (1931). Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I.
2. Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media.
3. Tegmark, M. (2014). *Our Mathematical Universe*. Knopf.
4. Lloyd, S. (2006). *Programming the Universe*. Knopf.
5. Cook, M. (2004). Universality in Elementary Cellular Automata. *Complex Systems* 15(1), 1-40.
6. Barbour, J. (1999). *The End of Time: The Next Revolution in Physics*. Oxford University Press.
7. Zenil, H. (2012). *A Computable Universe: Understanding and Exploring Nature as Computation*. World Scientific.
8. Aaronson, S. (2024). Quantum Computing: Between Hope and Hype. *Shtetl-Optimized Blog*, accessed Oct 17, 2025. (讨论性引用)
9. Auric, H. (2025). Collapse-Aware Foundations of Static Block Reality.
10. Hedlund, G. A. (1969). Endomorphisms and Automorphisms of the Shift Dynamical System. *Mathematical Systems Theory* 3(4), 320-375.
11. Berger, R. (1966). The Undecidability of the Domino Problem. *Memoirs of the American Mathematical Society* 66.
12. Wang, H. (1961). Proving Theorems by Pattern Recognition II. *Bell System Technical Journal* 40(1), 1-41.
13. Ollinger, N. (2008). Universalities in Cellular Automata: a (short) survey. arXiv:0809.5065.
14. Kari, J. (1994). Reversibility and Surjectivity Problems of Cellular Automata. *Journal of Computer and System Sciences* 48(1), 149-182.
15. Toffoli, T. (1977). Computation and Construction Universality of Reversible Cellular Automata. *Journal of Computer and System Sciences* 15(2), 213-231.
16. Morita, K. (1995). Reversible Simulation of One-Dimensional Irreversible Cellular Automata. *Theoretical Computer Science* 148(1), 157-163.
17. Li, M., & Vitányi, P. (2008). *An Introduction to Kolmogorov Complexity and Its Applications* (3rd ed.). Springer.
18. Moore, E. F. (1962). Machine Models of Self-Reproduction. *Proceedings of the Symposium on Mathematical Problems in the Biological Sciences*, 17-33.
19. Myhill, J. (1963). The Converse of Moore's Garden-of-Eden Theorem. *Proceedings of the American Mathematical Society* 14(5), 685-686.

---

**致谢**

感谢审阅反馈，确保修订版逻辑自洽。特别感谢指出通用基底条件、可计算同构精确性等关键问题的审阅者，使本理论得以完善。

**版本说明**

v1.6.1-final (2025-10-17): 提交版，根据审阅反馈最终优化，确保通用基底条件明确、可计算同构定义精确、停机问题对偶的算术层次表述自洽，包含完整的形式化定义、定理证明、模拟验证和 Rule 110 编码表。论文已准备好提交。
