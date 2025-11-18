# 03. 结构参数详解：时空的离散图纸

## 引言：搭积木的第一步——图纸

在第02篇中，我们建立了参数向量的三重分解 $\Theta = (\Theta_{\text{str}}, \Theta_{\text{dyn}}, \Theta_{\text{ini}})$。现在深入第一类参数：**结构参数** $\Theta_{\text{str}}$。

### 通俗比喻：建筑图纸决定房子的骨架

想象你要用乐高积木搭建一座城堡。开始之前，你需要一张**建筑图纸**回答以下问题：

**基础问题**：
1. 有多少块积木？（格点数 $N_{\text{cell}}$）
2. 每块积木是什么类型？（元胞Hilbert空间 $\mathcal{H}_{\text{cell}}$）
3. 积木如何连接？（图结构、邻居关系）
4. 是搭在平面上还是圆形底座上？（拓扑与边界条件）

**进阶问题**：
5. 积木有特殊对称性吗？（如镜像对称、旋转不变）
6. 有些位置不能放积木吗？（缺陷、非均匀结构）

**宇宙的情况完全类似**：

结构参数 $\Theta_{\text{str}}$ 就是宇宙的"乐高图纸"，它回答：
- 有多少个"时空格点"？→ 格点集合 $\Lambda$
- 每个格点有什么"内部结构"？→ 元胞Hilbert空间 $\mathcal{H}_x$
- 格点如何"连接"？→ 图结构 $(  \Lambda, E)$
- 宇宙是"开放"还是"封闭"？→ 边界条件
- 有什么对称性？→ 对称群 $G$

本篇将详细解释这些内容。

## 第一部分：格点集合 $\Lambda$ 的构造

### 最简单情况：规则矩形格

**定义3.1**（$d$维矩形格）：

$$
\Lambda = \prod_{i=1}^d \{0, 1, \ldots, L_i - 1\} = \mathbb{Z}_{L_1} \times \cdots \times \mathbb{Z}_{L_d}
$$

**参数**：
- 维度 $d \in \{1, 2, 3, 4, \ldots\}$
- 各方向格长 $L_1, \ldots, L_d \in \mathbb{N}$

**总格点数**：
$$
N_{\text{cell}} = \prod_{i=1}^d L_i
$$

**例子1**（一维链）：
$$
\Lambda = \{0, 1, \ldots, 99\} = \mathbb{Z}_{100}
$$
- $d=1$，$L_1 = 100$
- 总格点数：$N_{\text{cell}} = 100$

**例子2**（二维方格）：
$$
\Lambda = \{0, \ldots, 999\} \times \{0, \ldots, 999\}
$$
- $d=2$，$L_1 = L_2 = 1000$
- 总格点数：$N_{\text{cell}} = 10^6$

**例子3**（三维立方体）：
$$
\Lambda = \{0, \ldots, L-1\}^3
$$
- $d=3$，$L_1 = L_2 = L_3 = L$
- 总格点数：$N_{\text{cell}} = L^3$

**宇宙学尺度**（以普朗克长度 $\ell_p \sim 10^{-35}\,\text{m}$ 为单位）：
- 可观测宇宙半径：$R_{\text{uni}} \sim 10^{26}\,\text{m} = 10^{61} \ell_p$
- 若三维立方格：$L \sim 10^{61}$
- 总格点数：$N_{\text{cell}} \sim (10^{61})^3 = 10^{183}$

（但这超过 $I_{\max} \sim 10^{123}$！后面会讨论如何调和）

### 编码格点集合

**编码内容**（$\Theta_{\text{str}}$ 的一部分）：

1. **维度** $d$：
   - 用 $\lceil \log_2 d_{\max} \rceil$ 比特
   - 若限制 $d \leq 16$（足够物理），需要 4 比特

2. **各方向格长** $L_1, \ldots, L_d$：
   - 若每个 $L_i \leq 2^{64}$，每个需要 64 比特
   - 总共：$64d$ 比特

**比特计数**：
$$
I_{\Lambda} = 4 + 64d
$$

**例子**（$d=3$）：
$$
I_{\Lambda} = 4 + 64 \times 3 = 196 \text{ bits}
$$

### 图结构与邻居关系

格点集合 $\Lambda$ 本身只是点的集合。要定义"哪些格点相邻"，需要**图结构**。

**定义3.2**（格点图）：

$$
\mathcal{G}_{\Lambda} = (\Lambda, E)
$$

其中 $E \subset \Lambda \times \Lambda$ 是边集合，$(x, y) \in E$ 表示 $x, y$ 相邻。

**标准选择**（矩形格）：

**(1) 最近邻图**（nearest-neighbor）：

$$
(x, y) \in E \quad \Leftrightarrow \quad \sum_{i=1}^d |x_i - y_i| = 1
$$

（曼哈顿距离为1）

**例子**（二维方格）：
- 点 $(5, 7)$ 的最近邻：$(4,7), (6,7), (5,6), (5,8)$（4个邻居）

**(2) 次近邻图**（next-nearest-neighbor）：

$$
(x, y) \in E \quad \Leftrightarrow \quad 1 \leq \sum_{i=1}^d |x_i - y_i| \leq 2
$$

**例子**（二维方格）：
- 点 $(5, 7)$ 的次近邻：除了4个最近邻，还有对角线方向的4个（共8个）

**(3) 切比雪夫图**（Chebyshev）：

$$
(x, y) \in E \quad \Leftrightarrow \quad \max_{i=1}^d |x_i - y_i| = 1
$$

**度数**（degree）：

每个格点的邻居数（度数 $\deg(x)$）：
- 一维最近邻：$\deg = 2$（内部点），$\deg=1$（边界点）
- 二维方格最近邻：$\deg = 4$（内部），$\deg \in \{2,3\}$（边界）
- 三维立方最近邻：$\deg = 6$（内部）

**编码图结构**：

对标准规则格，图结构由**邻居类型**唯一确定：
- "最近邻" → 1 比特编码选项
- "次近邻" → 另1 比特
- 总共：2-3 比特

对非规则图，需要编码邻接矩阵（开销大，通常避免）。

### 物理含义：格点 = 时空事件的"像素"

**经典连续时空**：
- 事件：$(t, x, y, z) \in \mathbb{R}^4$（连续）
- 不可数无穷多点

**离散QCA时空**：
- 事件：$x \in \Lambda \subset \mathbb{Z}^d$（离散）
- 有限格点数 $N_{\text{cell}}$

**格距** $a$（lattice spacing）：

$$
a = \frac{L_{\text{physical}}}{L_{\text{lattice}}}
$$

**例子**：
- 物理长度：$L_{\text{physical}} = 1\,\text{m}$
- 格点数：$L_{\text{lattice}} = 10^{35}$（以普朗克长度为单位）
- 格距：$a = 10^{-35}\,\text{m} = \ell_p$

**通俗比喻**：
- 连续时空 = 无限分辨率的照片
- QCA格点 = 数字照片的像素
- 格距 $a$ = 每个像素代表的物理尺寸

## 第二部分：元胞Hilbert空间 $\mathcal{H}_{\text{cell}}$

### 单元胞的内部自由度

每个格点 $x \in \Lambda$ 携带一个**有限维Hilbert空间** $\mathcal{H}_x$。

**定义3.3**（元胞Hilbert空间）：

$$
\mathcal{H}_x \cong \mathbb{C}^{d_{\text{cell}}}
$$

其中 $d_{\text{cell}} \in \mathbb{N}$ 是元胞维数。

**物理意义**：
- $d_{\text{cell}}$：每个格点有多少个"内部量子态"
- 类比：每个像素有多少个颜色通道（RGB = 3通道）

### 元胞维数的物理来源

在真实物理中，$\mathcal{H}_{\text{cell}}$ 通常分解为多个子系统的张量积：

$$
\boxed{\mathcal{H}_{\text{cell}} = \mathcal{H}_{\text{fermion}} \otimes \mathcal{H}_{\text{gauge}} \otimes \mathcal{H}_{\text{aux}}}
$$

#### (1) 费米子自由度 $\mathcal{H}_{\text{fermion}}$

**最简单**（Dirac-QCA）：
$$
\mathcal{H}_{\text{fermion}} = \mathbb{C}^2
$$
- 基矢：$\{|\uparrow\rangle, |\downarrow\rangle\}$（自旋上/下）
- 维数：$\dim \mathcal{H}_{\text{fermion}} = 2$

**标准模型**（3代轻子+夸克）：
- 轻子：电子、缪子、陶子（各有中微子）→ 6种
- 夸克：上、下、奇、粲、底、顶 → 6种
- 自旋：上/下 → 2种
- 粒子/反粒子 → 2种
- 总计：$(6+6) \times 2 \times 2 = 48$

但考虑色荷（夸克有3色）：
$$
\dim \mathcal{H}_{\text{fermion}} \sim 3 \times 6 \times 2 \times 2 = 72
$$

（实际需要更精细的Fock空间构造）

#### (2) 规范场自由度 $\mathcal{H}_{\text{gauge}}$

**电磁场**（U(1)）：
- 光子：2个偏振态
- 维数：$\dim \mathcal{H}_{\text{gauge}}^{\text{EM}} = 2$

**非阿贝尔规范场**（SU(N)）：
- 胶子（SU(3)色规范）：8个胶子 × 2偏振 = 16态
- 弱规范玻色子（SU(2)）：3个玻色子（W⁺, W⁻, Z） × 2偏振 = 6态

**联合**（标准模型 SU(3)×SU(2)×U(1)）：
$$
\dim \mathcal{H}_{\text{gauge}} \sim 16 + 6 + 2 = 24
$$

#### (3) 辅助比特 $\mathcal{H}_{\text{aux}}$

**为何需要**：保证QCA演化的**可逆性**。

**原理**（Bennett垃圾比特）：
经典可逆计算需要"垃圾寄存器"存储中间结果，量子QCA类似。

**维数估计**：
若主要自由度有 $d_{\text{main}}$ 个态，辅助比特通常需要 $d_{\text{aux}} \sim \log_2 d_{\text{main}}$。

**标准模型QCA**：
- 主要自由度：$d_{\text{main}} \sim 72 \times 24 \sim 1700$
- 辅助比特：$d_{\text{aux}} \sim \log_2 1700 \sim 11$ → $2^{11} = 2048$

**总元胞维数**：
$$
d_{\text{cell}} = d_{\text{fermion}} \times d_{\text{gauge}} \times d_{\text{aux}} \sim 72 \times 24 \times 2048 \sim 3.5 \times 10^6
$$

（这是**单个格点**的Hilbert空间维数！）

### 编码元胞Hilbert空间

**方法1**（直接编码维数）：
- 存储 $d_{\text{cell}}$
- 需要 $\lceil \log_2 d_{\text{cell}} \rceil$ 比特
- 例：$d_{\text{cell}} = 3.5 \times 10^6$ → $\log_2(3.5 \times 10^6) \approx 22$ 比特

**方法2**（分解编码）：
- 分别存储 $d_{\text{fermion}}, d_{\text{gauge}}, d_{\text{aux}}$
- 总比特数：$\log_2 d_{\text{fermion}} + \log_2 d_{\text{gauge}} + \log_2 d_{\text{aux}}$
- 例：$\log_2 72 + \log_2 24 + \log_2 2048 = 7 + 5 + 11 = 23$ 比特

**方法3**（指定物理模型）：
- 编码"标准模型"（字符串）
- 维数隐含在模型中
- 需要：$\sim 50$ 比特（编码模型名称+参数）

**通常选择**：方法3（物理模型编码）

**比特计数**：
$$
I_{\mathcal{H}} \sim 50 \text{ bits}
$$

### 全局Hilbert空间的张量积

**定义3.4**（全局Hilbert空间）：

$$
\boxed{\mathcal{H}_{\Lambda} = \bigotimes_{x \in \Lambda} \mathcal{H}_x}
$$

**维数**：
$$
\dim \mathcal{H}_{\Lambda} = \prod_{x \in \Lambda} d_{\text{cell}}(x) = d_{\text{cell}}^{N_{\text{cell}}}
$$

（假设各格点元胞维数相同）

**数值例子**（宇宙学尺度）：
- $d_{\text{cell}} = 10^6$
- $N_{\text{cell}} = 10^{90}$（以普朗克单位的可观测宇宙）
- $\dim \mathcal{H}_{\Lambda} = (10^6)^{10^{90}} = 10^{6 \times 10^{90}}$

这是一个**双重指数**大的数！

**最大熵**（信息容量）：
$$
S_{\max} = \log_2 \dim \mathcal{H}_{\Lambda} = N_{\text{cell}} \log_2 d_{\text{cell}}
$$

**例子**：
- $N_{\text{cell}} = 10^{90}$，$d_{\text{cell}} = 10^6$
- $S_{\max} = 10^{90} \times \log_2(10^6) = 10^{90} \times 20 = 2 \times 10^{91}$ 比特

（远超 $I_{\max} \sim 10^{123}$，这意味着宇宙不能"填满"整个Hilbert空间！）

## 第三部分：边界条件与拓扑

### 为什么需要边界条件？

格点集合 $\Lambda$ 是有限的，必然有"边界"。边界的处理方式影响物理性质。

**经典类比**：
- 开放系统：能量可以流入/流出（开边界）
- 封闭系统：能量守恒（周期边界）

### 开边界条件（Open Boundary）

**定义3.5**（开边界）：

边界格点只有部分邻居（内部格点的邻居数正常）。

**一维例子**：
$$
\Lambda = \{0, 1, 2, \ldots, L-1\}
$$
- 边界：$x=0, x=L-1$
- 内部：$x \in \{1, \ldots, L-2\}$

**邻居结构**：
- $x=0$：只有右邻居 $x=1$
- $x=L-1$：只有左邻居 $x=L-2$
- $x \in \{1, \ldots, L-2\}$：左右邻居都有

**物理意义**：
- 边界是"真实的"（如容器壁）
- 量子态可以在边界反射或吸收
- **边界效应**显著（当 $L$ 不够大时）

**编码**：
- 对每个方向指定"open" → 1比特/方向
- 总共：$d$ 比特

### 周期边界条件（Periodic Boundary）

**定义3.6**（周期边界）：

边界格点通过"环绕"与对侧连接。

**一维例子**：
$$
\Lambda = \mathbb{Z}_L = \{0, 1, \ldots, L-1\}
$$

**邻居结构**（最近邻）：
- $x=0$：左邻居是 $x=L-1$，右邻居是 $x=1$
- $x=L-1$：左邻居是 $x=L-2$，右邻居是 $x=0$
- （形成一个"环"）

**拓扑**：
- 一维周期：圆 $S^1$
- 二维周期：环面 $\mathbb{T}^2 = S^1 \times S^1$
- 三维周期：三维环面 $\mathbb{T}^3$

**物理意义**：
- 消除边界效应
- 平移对称性保持
- 模拟"无限大"系统（当 $L$ 足够大时）

**编码**：
- 对每个方向指定"periodic" → 1比特/方向
- 总共：$d$ 比特

**通俗比喻**：
- **开边界**：在平面地图上行走，走到边缘就停止
- **周期边界**：在游戏《贪吃蛇》中，蛇从屏幕右边出去，从左边重新进来

### 扭曲边界条件（Twisted Boundary）

**定义3.7**（扭曲边界）：

环绕时施加一个相位或对称变换。

**一维例子**（反周期）：
$$
\psi(L) = -\psi(0)
$$

（波函数在环绕时改变符号）

**物理意义**：
- 费米子：通常用反周期边界（泡利不相容原理）
- 玻色子：用周期边界
- 拓扑相：需要扭曲边界检测拓扑不变量

**编码**：
- 指定扭曲类型（无、反周期、U(1)相位）→ 2比特/方向
- 总共：$2d$ 比特

### 非平凡拓扑

**例子1**（三维球面 $S^3$）：
- 闭合、无边界
- 需要特殊格点粘合

**例子2**（RP³、流形）：
- 复杂拓扑不变量
- 需要额外编码粘合映射

**编码开销**：
- 简单拓扑（$\mathbb{R}^d$、$\mathbb{T}^d$、$S^d$）：$\sim 10$ 比特
- 复杂拓扑（任意流形）：$\sim 100$ 比特（Morse理论、CW复形）

**宇宙学应用**：
- 可观测宇宙拓扑未知（可能是 $\mathbb{R}^3$、$\mathbb{T}^3$、双曲空间……）
- $\Theta_{\text{str}}$ 需要编码拓扑类型

### 边界条件的比特计数

$$
I_{\text{boundary}} \sim 2d \text{ bits}
$$

（假设标准或扭曲周期边界）

**例子**（$d=3$）：
$$
I_{\text{boundary}} = 6 \text{ bits}
$$

## 第四部分：对称性与守恒律

### 为什么对称性重要？

物理定律通常具有对称性：
- **时间平移对称** → 能量守恒
- **空间平移对称** → 动量守恒
- **转动对称** → 角动量守恒
- **规范对称** → 荷守恒

在QCA框架，对称性编码在 $\Theta_{\text{str}}$ 中，影响 $\mathcal{H}_{\text{cell}}$ 的表示论结构。

### 全局对称群 $G_{\text{global}}$

**定义3.8**（全局对称）：

一个幺正表示 $\rho: G \to U(\mathcal{H}_{\text{cell}})$ 使得动力学保持不变。

**例子1**（U(1)对称）：
- 粒子数守恒
- 群：$G = U(1) = \{e^{i\theta} : \theta \in [0, 2\pi)\}$
- 表示：$\rho(e^{i\theta}) = e^{i\theta \hat{N}}$（$\hat{N}$ 为粒子数算符）

**例子2**（SU(2)自旋对称）：
- 转动不变性
- 群：$G = SU(2)$
- 表示：自旋-1/2、自旋-1等表示

**例子3**（Z₂对称）：
- 宇称对称（$x \to -x$）
- 群：$G = \mathbb{Z}_2 = \{+1, -1\}$
- 表示：$\rho(-1) = P$（宇称算符）

### 局域规范对称 $G_{\text{local}}$

**定义3.9**（规范对称）：

在每个格点独立地作用的对称变换，物理态在规范变换下等价。

**标准模型**：
$$
G_{\text{local}} = SU(3)_{\text{color}} \times SU(2)_{\text{weak}} \times U(1)_Y
$$

- SU(3)：色规范对称（强相互作用）
- SU(2)：弱同位旋对称
- U(1)：超荷对称

**物理Hilbert空间**：
需要满足**Gauss定律**（规范约束）的态。

**例子**（格规范理论）：
- 在每条边上放置规范场变量 $U_e \in SU(N)$
- 物理态满足：$\prod_{e \text{ 出于 } x} U_e = \mathbb{1}$（每个格点）

### 对称性的编码

**编码内容**：

1. **对称群类型**：
   - "U(1)"、"SU(2)"、"SU(3)"、……
   - 用字符串或枚举类型 → $\sim 20$ 比特

2. **表示选择**：
   - 基本表示、伴随表示、自旋-$j$ 表示……
   - 每个表示 $\sim 10$ 比特

3. **如何作用在 $\mathcal{H}_{\text{cell}}$ 上**：
   - 指定生成元在基矢上的矩阵表示
   - 对标准群（U(1)、SU(2)、SU(3)），可以预设
   - 额外编码 $\sim 10$ 比特

**总比特数**：
$$
I_{\text{symmetry}} \sim 20 + 10 + 10 = 40 \text{ bits}
$$

（对单个对称群）

**标准模型**（SU(3)×SU(2)×U(1)）：
$$
I_{\text{symmetry}} \sim 3 \times 40 = 120 \text{ bits}
$$

### 对称性与信息压缩

**关键洞察**：对称性可以**极大压缩**参数信息！

**例子**（平移不变性）：

**无对称性**：
- 每个格点的哈密顿量参数独立 → $N_{\text{cell}}$ 组参数
- 信息量：$\sim N_{\text{cell}} \times I_{\text{local}}$

**有平移对称性**：
- 所有格点哈密顿量相同 → 只需1组参数
- 信息量：$\sim I_{\text{local}}$

**压缩比**：$N_{\text{cell}}$（天文数字！）

**物理必然性**：
若宇宙没有对称性，需要的参数信息将超过 $I_{\max}$ → 矛盾

因此：**对称性不是巧合，而是有限信息公理的必然后果！**

## 第五部分：缺陷与非均匀结构

### 拓扑缺陷

**定义3.10**（拓扑缺陷）：

空间中某些位置，场配置或几何具有奇异性，不能通过连续变形消除。

**例子1**（宇宙弦）：
- 一维缺陷（三维空间中的"弦"）
- 场配置在绕弦一周时获得非平凡相位
- 产生圆锥几何（亏损角）

**例子2**（磁单极）：
- 零维缺陷（"点"）
- 规范场在远处类似磁单极场
- Dirac量子化条件

**例子3**（畴壁）：
- 二维缺陷（三维空间中的"壁"）
- 两侧真空态不同（自发对称性破缺）

### QCA中的缺陷编码

**方法1**（位置列表）：
- 缺陷位置：$(x_1, y_1, z_1), (x_2, y_2, z_2), \ldots$
- 每个坐标 $\sim 3 \times \log_2 L$ 比特
- $k$ 个缺陷：$\sim k \times 3 \log_2 L$ 比特

**方法2**（场配置编码）：
- 在缺陷附近，场配置特殊
- 编码缺陷类型（字符串、单极、畴壁）+ 取向
- 每个缺陷 $\sim 50$ 比特

**宇宙学**（暴涨后遗迹）：
- 暴涨理论预言：宇宙中可能有 $\sim 0$ 个大尺度缺陷（暴涨稀释）
- 或 $\sim 10$ 个缺陷（相变时形成）

**编码开销**：
$$
I_{\text{defect}} \sim k_{\text{defect}} \times 50 \text{ bits}
$$

**例子**（$k_{\text{defect}} = 0$）：
$$
I_{\text{defect}} = 0 \text{ bits}
$$

（均匀宇宙，无缺陷）

### 非均匀格长（Refinement）

**动机**：某些区域需要更高分辨率。

**例子**（天文学）：
- 星系团附近：高分辨率（$a \sim 10^{-10} \ell_p$）
- 星际空间：低分辨率（$a \sim 10^{-5} \ell_p$）

**实现**（自适应网格）：
- 将某些粗格点"细分"为 $2^d$ 个子格点
- 递归细分

**编码**：
- 细分树结构（类似四叉树/八叉树）
- 每个细分决策 $\sim 1$ 比特
- 若细分 $k_{\text{refine}}$ 次：$\sim k_{\text{refine}}$ 比特

**宇宙学应用**：
- 观测表明宇宙**大尺度均匀**（CMB涨落 $\sim 10^{-5}$）
- 非均匀结构主要在小尺度（星系、恒星）
- 若用粗粒化（coarse-graining），小尺度涌现
- $\Theta_{\text{str}}$ 可以只编码大尺度均匀格

**典型值**：
$$
I_{\text{refine}} \sim 0 \text{ bits}
$$

（均匀格足够）

## 第六部分：结构参数的总比特计数

综合以上各部分：

$$
\boxed{|\Theta_{\text{str}}| = I_{\Lambda} + I_{\mathcal{H}} + I_{\text{boundary}} + I_{\text{symmetry}} + I_{\text{defect}} + I_{\text{refine}}}
$$

**数值表**（标准宇宙QCA）：

| 项目 | 内容 | 比特数 |
|------|------|--------|
| $I_{\Lambda}$ | 维度 + 格长 | $4 + 64 \times 3 = 196$ |
| $I_{\mathcal{H}}$ | 元胞Hilbert空间 | 50 |
| $I_{\text{boundary}}$ | 边界条件 | $2 \times 3 = 6$ |
| $I_{\text{symmetry}}$ | 对称群 | 120 |
| $I_{\text{defect}}$ | 拓扑缺陷 | 0 |
| $I_{\text{refine}}$ | 非均匀细分 | 0 |
| **总计** | | **372** |

**关键观察**：
$$
|\Theta_{\text{str}}| \sim 400 \text{ bits} \ll I_{\max} \sim 10^{123} \text{ bits}
$$

结构参数信息量**极小**！

## 第七部分：准局域 $C^*$ 代数的构造

### 从格点到代数

有了格点集合 $\Lambda$ 和元胞Hilbert空间 $\mathcal{H}_x$，可以构造**准局域算子代数**。

**定义3.11**（局域代数）：

对有限子集 $F \subset \Lambda$，定义：

$$
\mathcal{H}_F = \bigotimes_{x \in F} \mathcal{H}_x
$$

$$
\mathcal{A}_F = \mathcal{B}(\mathcal{H}_F)
$$

（$\mathcal{H}_F$ 上所有有界算子）

**嵌入**：

若 $F \subset F'$，则 $\mathcal{A}_F \subset \mathcal{A}_{F'}$ 通过：

$$
\iota_{F \subset F'}(A_F) = A_F \otimes \mathbb{1}_{F' \setminus F}
$$

（在 $F$ 外作用为恒等）

**定义3.12**（准局域 $C^*$ 代数）：

$$
\boxed{\mathcal{A}(\Lambda) = \overline{\bigcup_{F \Subset \Lambda} \mathcal{A}_F}^{\|\cdot\|}}
$$

（所有局域算子的闭包，以算符范数计）

**物理意义**：
- $\mathcal{A}(\Lambda)$：所有"局域可观测量"
- 可观测量作用在有限区域，但可以任意大

### 态空间

**定义3.13**（态）：

态是 $\mathcal{A}(\Lambda)$ 上的正、归一线性泛函：

$$
\omega: \mathcal{A}(\Lambda) \to \mathbb{C}
$$

满足：
- 正性：$\omega(A^\dagger A) \geq 0$
- 归一性：$\omega(\mathbb{1}) = 1$

**纯态与混态**：
- 纯态：$\omega(A) = \langle \psi | A | \psi \rangle$（某个矢量态）
- 混态：$\omega(A) = \text{tr}(\rho A)$（密度矩阵）

**态空间维数**：
$$
\dim(\text{纯态流形}) = 2 \dim \mathcal{H}_{\Lambda} - 2 = 2 d_{\text{cell}}^{N_{\text{cell}}} - 2
$$

（复射影空间 $\mathbb{CP}^{d-1}$ 的实维数）

这是**双重指数**大！

### $C^*$ 代数与有限信息的关系

**关键定理**：

在有限维 $\mathcal{H}_{\Lambda}$ 上，$\mathcal{A}(\Lambda) = \mathcal{B}(\mathcal{H}_{\Lambda})$ 也是有限维的：

$$
\dim_{\mathbb{C}} \mathcal{A}(\Lambda) = (\dim \mathcal{H}_{\Lambda})^2 = d_{\text{cell}}^{2N_{\text{cell}}}
$$

**信息量**：
$$
\log_2 \dim \mathcal{A}(\Lambda) = 2 N_{\text{cell}} \log_2 d_{\text{cell}} = 2 S_{\max}
$$

但**物理可观测算子数量**远小于 $\dim \mathcal{A}$，因为：
- 对称性约束（规范不变、平移不变）
- 局域性（实验只能测量局域算符）

**有效信息**：
$$
I_{\text{eff}}^{\text{obs}} \ll 2 S_{\max}
$$

（通常 $\sim S_{\max}$ 或更少）

## 本篇核心要点总结

### 结构参数的五大组成

$$
\Theta_{\text{str}} = (\Lambda, \mathcal{H}_{\text{cell}}, \text{boundary}, G_{\text{symm}}, \text{defects})
$$

| 组成部分 | 物理含义 | 典型比特数 |
|---------|---------|-----------|
| $\Lambda$ | 格点集合（维度+格长+图） | 200 |
| $\mathcal{H}_{\text{cell}}$ | 元胞内部自由度 | 50 |
| 边界条件 | 开/周期/扭曲 | 6 |
| 对称群 | 全局/规范对称 | 120 |
| 缺陷 | 拓扑缺陷、非均匀 | 0 |
| **总计** | | **~400** |

### 全局Hilbert空间

$$
\mathcal{H}_{\Lambda} = \bigotimes_{x \in \Lambda} \mathcal{H}_x, \quad \dim \mathcal{H}_{\Lambda} = d_{\text{cell}}^{N_{\text{cell}}}
$$

**最大熵**：
$$
S_{\max} = N_{\text{cell}} \log_2 d_{\text{cell}}
$$

**数值例子**（宇宙学）：
- $N_{\text{cell}} \sim 10^{90}$，$d_{\text{cell}} \sim 10^6$
- $S_{\max} \sim 2 \times 10^{91}$ bits

### 准局域 $C^*$ 代数

$$
\mathcal{A}(\Lambda) = \overline{\bigcup_{F \Subset \Lambda} \mathcal{B}(\mathcal{H}_F)}^{\|\cdot\|}
$$

**物理意义**：所有局域可观测量的集合。

### 核心洞察

1. **结构参数微小**：$|\Theta_{\text{str}}| \sim 400 \ll I_{\max} \sim 10^{123}$
2. **状态空间巨大**：$S_{\max} \sim 10^{91}$ 主导信息容量
3. **对称性必然**：无对称性 → 参数爆炸 → 超过 $I_{\max}$
4. **有限信息强制离散**：连续时空需要无限信息 → 必须离散化
5. **格距 $a$ 与物理尺度**：$a \sim \ell_p$（普朗克长度）是自然单位

### 与连续场论的关系

| 连续场论 | QCA离散实现 |
|---------|-----------|
| 时空流形 $M$ | 格点集合 $\Lambda$ |
| 点 $x \in M$ | 格点 $x \in \Lambda$ |
| 场 $\phi(x)$ | 元胞态 $\psi_x \in \mathcal{H}_x$ |
| 场算符 $\hat{\phi}(x)$ | 元胞算符 $A_x \in \mathcal{B}(\mathcal{H}_x)$ |
| 无限自由度 | 有限 $N_{\text{cell}}$ 个格点 |
| 连续对称性 | 离散对称性（有限精度） |

**连续极限**（第07篇详述）：
$$
a, \Delta t \to 0 \Rightarrow \text{QCA} \to \text{场论}
$$

---

**下一篇预告**：**04. 动力学参数详解：物理定律的源代码**
- QCA自同构 $\alpha_{\Theta}$ 的构造
- 有限深度局域幺正线路
- 门集 $\mathcal{G}$ 与通用性
- 离散角参数 $\theta \to 2\pi n/2^m$
- Lieb-Robinson界与光锥
- 从离散门到连续哈密顿量
