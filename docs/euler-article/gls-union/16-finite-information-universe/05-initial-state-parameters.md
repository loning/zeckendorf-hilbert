# 05. 初始态参数详解：宇宙的出厂设置

## 引言：大爆炸时刻的量子态

在前面的篇章中，我们建立了：
- **第03篇**：宇宙的空间结构 $\Theta_{\text{str}}$（舞台）
- **第04篇**：宇宙的演化规则 $\Theta_{\text{dyn}}$（剧本）

但还缺少一个关键要素：**起点**。

**核心问题**：
- 宇宙在 $t=0$（大爆炸时刻）处于什么量子态？
- 如何用有限比特串编码这个初始态？
- 初始态如何影响整个宇宙历史？

答案在**初始态参数** $\Theta_{\text{ini}}$ 中。

### 通俗比喻：工厂的出厂设置

继续我们的建筑/工厂类比：

**已有**：
- $\Theta_{\text{str}}$：工厂的图纸（有多少机器，如何布局）
- $\Theta_{\text{dyn}}$：生产流程（如何操作机器）

**缺少**：
- $\Theta_{\text{ini}}$：机器的初始状态（开关位置、温度、库存……）

**为什么重要**？

想象两台完全相同的咖啡机（相同 $\Theta_{\text{str}}$ 和 $\Theta_{\text{dyn}}$）：
- 机器A：豆仓满、水箱满、预热完成 → 立即出咖啡
- 机器B：豆仓空、水箱空、未预热 → 需要准备

**相同的结构和规则，不同的初态 → 不同的演化历史！**

宇宙也是如此：

| 咖啡机类比 | 宇宙QCA | 数学对象 |
|-----------|---------|---------|
| 机器出厂设置 | 初始态参数 $\Theta_{\text{ini}}$ | 参数比特串 |
| 开关/温度/库存 | 初始量子态 $\omega_0$ | 态泛函 |
| 设置手册 | 态制备线路 $V$ | 幺正算符 |
| 参考状态（全关闭） | 参考积态 $\|0_\Lambda\rangle$ | 简单积态 |
| 出厂流程 | 从 $\|0\rangle$ 到 $\|\Psi_0\rangle$ | 有限深度线路 |

本篇将详细解释如何用约**500比特**编码整个宇宙的初始量子态。

## 第一部分：初始态的物理意义

### 宇宙学的初始条件问题

**经典宇宙学**（Friedmann-Lemaître-Robertson-Walker模型）：

初始条件需要指定：
- 初始物质密度 $\rho_0$
- 初始哈勃常数 $H_0$
- 初始曲率 $k$
- 初始温度 $T_0$
- 初始涨落谱 $\Delta\rho(\mathbf{k})$
- ……

**问题**：这些都是**实数**，需要无限精度 → 无限信息！

**量子宇宙学**（Hartle-Hawking, Vilenkin等）：

试图从"无边界"或"隧穿"等原理导出初态，但仍需要：
- 波函数 $\Psi[\text{三几何}]$（在超空间上的泛函）
- 连续、无限维 → 仍需无限信息

**QCA框架的解决**：

初态是**有限维Hilbert空间中的一个态**：

$$
|\Psi_0\rangle \in \mathcal{H}_\Lambda = \bigotimes_{x \in \Lambda} \mathcal{H}_x
$$

**维数**：
$$
\dim \mathcal{H}_\Lambda = d_{\text{cell}}^{N_{\text{cell}}} \sim 10^{6 \times 10^{90}}
$$

虽然维数巨大，但**有限**！

### 初态的三种表述

**表述1**（量子态矢量）：

$$
|\Psi_0^{\Theta}\rangle \in \mathcal{H}_\Lambda
$$

一个归一化的量子态。

**表述2**（密度矩阵）：

$$
\rho_0^{\Theta} = |\Psi_0^{\Theta}\rangle\langle\Psi_0^{\Theta}|
$$

纯态的密度算符。

**表述3**（态泛函）：

$$
\omega_0^{\Theta}(A) = \langle\Psi_0^{\Theta}|A|\Psi_0^{\Theta}\rangle, \quad A \in \mathcal{A}(\Lambda)
$$

准局域代数上的正归一泛函。

**三者等价**（在纯态情况下）。本篇主要使用表述1和3。

### 初态决定宇宙历史

给定初态 $\omega_0$ 和演化 $\alpha$，整个宇宙历史被唯一确定：

$$
\boxed{\omega_n = \omega_0 \circ \alpha^{-n}}
$$

即：

$$
\omega_n(A) = \omega_0(\alpha^{-n}(A)) = \langle\Psi_0|U^{\dagger n} A U^n|\Psi_0\rangle
$$

**物理意义**：
- $\omega_0$："第零帧"（大爆炸时刻）
- $\alpha$："逐帧演化规则"（来自 $\Theta_{\text{dyn}}$）
- $\omega_n$："第n帧"（时间 $t = n\Delta t$）

**通俗比喻**：
- 初态 = 电影的第一帧
- 演化规则 = 每一帧如何变换到下一帧
- 整部电影 = 从第一帧开始，逐帧生成

**哲学意涵**：
宇宙历史是**确定性的**（在幺正演化下）：
$$
\text{初态} + \text{演化规则} \Rightarrow \text{整个历史}
$$

## 第二部分：参考积态 $|0_\Lambda\rangle$

### 最简单的态：真空态

直接编码一个任意量子态 $|\Psi_0\rangle \in \mathcal{H}_\Lambda$ 需要多少信息？

**朴素计数**：
- $\mathcal{H}_\Lambda \cong \mathbb{C}^D$，其中 $D = d_{\text{cell}}^{N_{\text{cell}}}$
- 量子态：$|\Psi\rangle = \sum_{i=1}^D c_i |i\rangle$
- 系数 $c_i \in \mathbb{C}$，满足 $\sum_i |c_i|^2 = 1$
- 自由度：$2(D-1)$ 个实数（除去归一化和整体相位）

**信息量**（若每个实数需要 $m$ 比特精度）：
$$
I \sim 2D \times m \sim 2 \times 10^{10^{91}} \times m
$$

这是**双重指数**！远远超过 $I_{\max} \sim 10^{123}$！

**解决方案**：不直接编码态矢量，而是**从简单态生成**。

### 定义参考积态

**定义5.1**（参考积态）：

选择每个元胞的一个固定"真空态" $|0_{\text{cell}}\rangle \in \mathcal{H}_{\text{cell}}$，定义：

$$
\boxed{|0_\Lambda\rangle = \bigotimes_{x \in \Lambda} |0_{\text{cell}}\rangle_x}
$$

**性质**：
1. **积态**（product state）：无纠缠
2. **平移不变**：每个格点相同
3. **简单**：完全由 $|0_{\text{cell}}\rangle$ 决定

**例子1**（自旋链）：

若 $\mathcal{H}_{\text{cell}} = \mathbb{C}^2$，基矢 $\{|\uparrow\rangle, |\downarrow\rangle\}$：

$$
|0_{\text{cell}}\rangle = |\downarrow\rangle
$$

则：

$$
|0_\Lambda\rangle = |\downarrow\downarrow\downarrow\cdots\downarrow\rangle
$$

（所有自旋向下）

**例子2**（费米子QCA）：

若 $\mathcal{H}_{\text{cell}}$ 包含费米子湮灭/产生算符 $\hat{a}, \hat{a}^\dagger$：

$$
|0_{\text{cell}}\rangle = |\text{vac}\rangle
$$

（费米子真空态，无粒子）

**编码开销**：

参考积态由 $|0_{\text{cell}}\rangle$ 完全确定，而 $|0_{\text{cell}}\rangle$ 在 $\Theta_{\text{str}}$ 中已指定（作为Hilbert空间的一部分）。

因此：**无需额外编码！**

### 物理解释

**宇宙的"绝对零度"**：

$|0_\Lambda\rangle$ 类似物理的"基态"或"真空态"：
- 无粒子
- 无纠缠
- 无激发
- 熵为零（纯态）

**通俗比喻**：
- 参考积态 = 全新出厂的白纸
- 初始态 = 白纸上画好的图画
- 态制备线路 = 从白纸到图画的"绘画过程"

## 第三部分：态制备线路 $V_{\Theta_{\text{ini}}}$

### 从参考态生成初态

**核心思想**：用**有限深度幺正线路**从 $|0_\Lambda\rangle$ 生成 $|\Psi_0\rangle$。

**定义5.2**（态制备线路）：

存在有限深度幺正算符 $V_{\Theta_{\text{ini}}}$，由门集 $\mathcal{G}$ 组成：

$$
V_{\Theta_{\text{ini}}} = V_{D_{\text{ini}}} V_{D_{\text{ini}}-1} \cdots V_2 V_1
$$

使得：

$$
\boxed{|\Psi_0^{\Theta}\rangle = V_{\Theta_{\text{ini}}} |0_\Lambda\rangle}
$$

**结构**（与第04篇动力学线路完全类似）：
- 深度：$D_{\text{ini}} \in \mathbb{N}$
- 每层 $V_\ell$：若干个局域门 $G_k \in \mathcal{G}$ 的并行组合
- 门参数：离散角 $\theta = 2\pi n / 2^m$

**区别**：
- 动力学线路 $U_{\Theta_{\text{dyn}}}$：定义时间演化（反复施加）
- 态制备线路 $V_{\Theta_{\text{ini}}}$：生成初态（只施加一次）

**通俗比喻**：
- $U$：工厂的生产流程（每天重复）
- $V$：机器的安装调试流程（只做一次）

### 线路深度与纠缠结构

**有限深度的后果**（Lieb-Robinson界）：

若线路深度为 $D_{\text{ini}}$，Lieb-Robinson速度为 $v_{\text{LR}}$，则：

**定理5.3**（纠缠范围限制）：

距离 $d(x, y) > v_{\text{LR}} D_{\text{ini}}$ 的两个区域 $A, B$ 的互信息满足：

$$
I(A:B) \lesssim e^{-c(d - v_{\text{LR}} D_{\text{ini}})}
$$

（指数衰减）

**物理意义**：
- 短深度线路 $\Rightarrow$ **短程纠缠态**
- 长程纠缠需要深度 $D \sim N_{\text{cell}}$ $\Rightarrow$ 参数爆炸

**宇宙学应用**：

观测表明宇宙微波背景（CMB）的相关长度有限：
- 声地平线：$\sim 10^5$ 光年
- 可观测宇宙：$\sim 10^{10}$ 光年
- 比值：$\sim 10^{-5}$

**推论**：初始纠缠是**局域的**，深度 $D_{\text{ini}} \sim \log N_{\text{cell}}$ 足够。

### 态制备线路的例子

**例子1**（Hadamard层）：

对自旋链，施加Hadamard门：

$$
V = \bigotimes_{x \in \Lambda} H_x
$$

其中 $H = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$。

**初态**：

$$
|\Psi_0\rangle = V |\downarrow\downarrow\cdots\downarrow\rangle = \frac{1}{2^{N_{\text{cell}}/2}} \sum_{\{s_x\}} |s_1 s_2 \cdots s_{N_{\text{cell}}}\rangle
$$

（所有自旋配置的等权叠加）

**性质**：
- 最大纠缠（在某种意义下）
- 深度 $D=1$（极浅）
- 熵 $S = N_{\text{cell}} \log 2$（最大熵）

**例子2**（GHZ态生成）：

对3个格点生成GHZ态：

$$
|\text{GHZ}\rangle = \frac{1}{\sqrt{2}}(|\downarrow\downarrow\downarrow\rangle + |\uparrow\uparrow\uparrow\rangle)
$$

**线路**（深度3）：
1. 第1格点施加Hadamard：$H_1$
2. CNOT门：1控制2，2控制3
3. 结果：$|\text{GHZ}\rangle$

**例子3**（热态近似）：

通过随机局域幺正构造"热化"态：

$$
V = \prod_{\ell=1}^D \prod_x R_x^{(\ell)}(\theta_{\ell,x})
$$

其中 $R(\theta)$ 为随机旋转，角度从分布中采样（离散化）。

**深度**：$D \sim \log N_{\text{cell}}$ 可达到接近热态。

## 第四部分：$\Theta_{\text{ini}}$ 的编码

### 编码结构

类似 $\Theta_{\text{dyn}}$（第04篇），$\Theta_{\text{ini}}$ 编码态制备线路 $V$：

$$
\Theta_{\text{ini}} = (D_{\text{ini}}, \{k_\ell\}, \{R_\ell\}, \{\theta_{\ell,j}\})
$$

**组成**：
1. **深度** $D_{\text{ini}}$
2. **每层门类型** $k_\ell \in \{1, \ldots, K\}$
3. **作用区域** $R_\ell \subset \Lambda$
4. **角参数** $\theta_{\ell,j} = 2\pi n_{\ell,j} / 2^m$

### 比特计数

$$
|\Theta_{\text{ini}}| = \lceil\log_2 D_{\text{ini}}\rceil + D_{\text{ini}} \times (I_{\text{gate}} + I_{\text{region}} + I_{\text{angles}})
$$

**平移不变情况**（典型）：

- $D_{\text{ini}} = 5$（短程纠缠足够）
- 门类型：$\log_2 K = 4$ 比特/层
- 作用区域：1 比特/层（奇偶性）
- 角参数：$2 \times 50 = 100$ 比特/层（2个角，精度50）

**总计**：
$$
|\Theta_{\text{ini}}| = \lceil\log_2 5\rceil + 5 \times (4 + 1 + 100) = 3 + 525 = 528 \text{ 比特}
$$

$$
\boxed{|\Theta_{\text{ini}}| \sim 500 \text{ 比特}}
$$

**关键观察**：
$$
|\Theta_{\text{ini}}| \sim 500 \ll I_{\max} \sim 10^{123}
$$

初始态参数信息量**微不足道**！

## 第五部分：对称性对初态的约束

### 平移不变初态

最简单的对称性：平移不变。

**定义5.4**（平移不变初态）：

$$
V_{\Theta_{\text{ini}}} = \left( \bigotimes_{x \in \Lambda} V_{\text{local}} \right)
$$

每个格点施加相同的局域幺正 $V_{\text{local}}$。

**例子**：

$$
V_{\text{local}} = R_y(\theta) = \exp(-i\theta \sigma_y / 2)
$$

施加到所有格点：

$$
|\Psi_0\rangle = \bigotimes_x R_y(\theta) |\downarrow\rangle_x
$$

**编码开销**：
- 只需编码 $V_{\text{local}}$（与 $N_{\text{cell}}$ 无关！）
- 例：单个旋转门 + 1个角参数 = 约50比特

**信息压缩**：
- 无对称性：$\sim N_{\text{cell}} \times I_{\text{local}}$ 比特
- 平移不变：$\sim I_{\text{local}}$ 比特
- **压缩比**：$N_{\text{cell}} \sim 10^{90}$（天文数字！）

### 基态与热态

**基态初态**：

若初态是某个有效哈密顿量 $H_{\text{eff}}$ 的基态：

$$
|\Psi_0\rangle = |\text{GS}(H_{\text{eff}})\rangle
$$

**编码**：
- 只需编码 $H_{\text{eff}}$（通常由 $\Theta_{\text{dyn}}$ 隐含）
- 额外信息：$\sim 0$ 比特（如果约定"初态=基态"）

**热态初态**（密度矩阵）：

$$
\rho_0 = \frac{e^{-\beta H_{\text{eff}}}}{Z}
$$

**编码**：
- 哈密顿量 $H_{\text{eff}}$（已在 $\Theta_{\text{dyn}}$ 中）
- 温度 $\beta = 1/k_B T$（需要离散化，约50比特）

**总计**：$\sim 50$ 比特

### 对称性破缺与相变

**自发对称性破缺**：

若理论有对称性，但初态破缺对称性：

**例子**（铁磁态）：
- 哈密顿量：$H = -J\sum_{\langle i,j\rangle} \sigma_i^z \sigma_j^z$（$Z_2$ 对称）
- 基态：两个简并态 $|\uparrow\uparrow\cdots\uparrow\rangle$ 和 $|\downarrow\downarrow\cdots\downarrow\rangle$
- 初态：选择其中一个（破缺 $Z_2$ 对称）

**编码**：
- 哈密顿量（对称）：在 $\Theta_{\text{dyn}}$ 中
- 选择哪个基态：1 比特（$\uparrow$ 或 $\downarrow$）

**宇宙学应用**（暴涨与真空选择）：
- 暴涨后宇宙可能落入不同"真空"
- 每个真空对应不同的物理常数
- $\Theta_{\text{ini}}$ 编码"选择了哪个真空"

## 第六部分：初始熵与信息

### 初态的von Neumann熵

**定义5.5**（von Neumann熵）：

对纯态：

$$
S(\omega_0) = -\text{tr}(\rho_0 \log \rho_0) = 0
$$

（纯态熵为零）

对混态：

$$
S(\rho_0) = -\text{tr}(\rho_0 \log \rho_0) > 0
$$

**物理意义**：
- 纯态：完全确定的量子态，无经典不确定性
- 混态：部分不确定性（热涨落、粗粒化等）

### 初始熵与宇宙演化

**定理5.6**（幺正演化保持熵）：

若演化是幺正的（$\alpha$由幺正算符实现），则：

$$
S(\omega_n) = S(\omega_0), \quad \forall n
$$

**推论**：
- 若 $\omega_0$ 是纯态（$S=0$），则 $\omega_n$ 永远是纯态（$S=0$）
- 幺正演化**不增加熵**

**问题**：宇宙为何有热力学第二定律（熵增）？

**解答**：
- 全局量子态：纯态，熵=0（守恒）
- 局域子系统：纠缠导致约化态是混态，熵>0
- **纠缠熵增长** = 表观的"热力学熵增"

**通俗比喻**：
- 两个色子：初始都是确定态（如都是6）
- 操作：把两个色子纠缠起来（量子门）
- 看单个色子：变成混态（似乎是随机的）
- 但两个一起看：仍是纯态（完全确定的纠缠态）

**宇宙学应用**：
- 初始态：极低熵（接近纯态）
- 演化：产生大量纠缠
- 局域观测者看到的：熵增（但全局仍是纯态）

### 初态复杂度

**定义5.7**（态复杂度）：

生成态 $|\Psi\rangle$ 所需的最小线路深度：

$$
C(|\Psi\rangle) = \min\{D : \exists V \text{ 深度 } D, \, V|0\rangle = |\Psi\rangle\}
$$

**性质**：
- 简单态（如积态）：$C = O(1)$
- 高度纠缠态（如随机态）：$C = O(N_{\text{cell}})$

**有限信息约束**：

由于 $|\Theta_{\text{ini}}| < I_{\max}$，复杂度不能太高：

$$
C(|\Psi_0\rangle) \lesssim I_{\max} / I_{\text{per-gate}}
$$

**数值例子**：
- $I_{\max} = 10^{123}$ 比特
- 每个门编码 $\sim 100$ 比特
- 最大复杂度：$C \lesssim 10^{121}$ 层

（虽然仍是天文数字，但比 $N_{\text{cell}} \sim 10^{90}$ 大得多）

## 第七部分：Hartle-Hawking无边界态的QCA版本

### 经典Hartle-Hawking提案

**量子宇宙学**（Hartle-Hawking, 1983）：

宇宙波函数由路径积分定义：

$$
\Psi[h_{ij}, \phi] = \int_{\text{compact}} \mathcal{D}[g, \phi] \, e^{iS[g, \phi]/\hbar}
$$

其中积分在"无边界"紧致四几何上。

**物理意义**：
- 宇宙"自发涌现"，无需初始奇点
- 时间在极早期变成"虚时间"（欧氏几何）
- 类似：量子隧穿

**问题**：
- 路径积分在连续几何上发散
- 需要引入截断或正规化
- 波函数定义在无限维超空间上

### QCA版本：最小深度原理

在QCA框架，可以类似定义：

**QCA无边界原理**：

初态 $|\Psi_0\rangle$ 由以下条件选择：

$$
\boxed{|\Psi_0\rangle = \arg\min_{V} \left\{ D(V) : V|0_\Lambda\rangle \text{ 满足某些对称性约束} \right\}}
$$

其中 $D(V)$ 为线路 $V$ 的深度。

**物理意义**：
- 宇宙选择"最简单"（深度最小）的与对称性兼容的初态
- 类似：最小作用量原理
- "奥卡姆剃刀"：无需额外假设的最简单解释

**例子**（平移不变 + 低能）：

约束：
1. 平移不变性
2. 能量低于某阈值 $E < E_0$

**结果**：
- 唯一解（在对称性类中）：基态 $|\text{GS}\rangle$
- 深度：$D = 0$（如果基态=参考态）或 $D = O(1)$

**与IGVP的联系**：

在GLS理论中，IGVP（信息几何变分原理）从熵变分导出爱因斯坦方程。类似地：

$$
\delta S_{\text{complexity}} = 0 \Rightarrow \text{选择最小深度初态}
$$

**推测**（未严格证明）：
- 最小复杂度 $\Leftrightarrow$ 最大对称性
- 最大对称性 $\Rightarrow$ 暴涨宇宙的近均匀初态
- 这或许解释了为何宇宙初态如此"特殊"（低熵）

## 第八部分：初态参数的测量与观测

### 我们如何知道初态？

**问题**：我们处在时刻 $n \sim 10^{60}$（宇宙年龄），如何推断 $t=0$ 的初态？

**答案**：从当前观测**反向推演**。

**宇宙微波背景（CMB）**：
- 观测：温度涨落 $\Delta T / T \sim 10^{-5}$（各向异性）
- 功率谱：$C_\ell$ 作为 $\ell$ 的函数
- 推断：初始密度涨落谱 $P(k)$

**暴涨理论预言**：
- 近标度不变谱：$P(k) \propto k^{n_s}$，$n_s \approx 0.96$
- 高斯分布（极小非高斯性）
- 绝热涨落（非等曲率）

**QCA语言翻译**：
- 近标度不变 $\Rightarrow$ 初态在动量空间近似平移不变
- 高斯 $\Rightarrow$ 纠缠结构简单（接近积态）
- 绝热 $\Rightarrow$ 某种对称性（如超对称在早期）

### 初态参数的"考古学"

**类比**：考古学家从遗迹推断古代文明。

| 考古学 | 宇宙学 |
|--------|--------|
| 遗迹（陶器、建筑） | CMB、大尺度结构 |
| 地层年代 | 红移 $z$ |
| 推断古人生活 | 推断初态 $\omega_0$ |
| 考古报告 | 参数 $\Theta_{\text{ini}}$ |

**当前测量精度**：
- CMB温度涨落：$\sim 10^{-6}$ K（Planck卫星）
- 大尺度结构：星系巡天（SDSS, DES, LSST）
- 原初引力波：尚未探测（目标：$r \sim 10^{-3}$）

**约束 $\Theta_{\text{ini}}$**：
- 谱指数 $n_s$：约束某些角参数
- 张标比 $r$：约束暴涨势的形状
- 非高斯性 $f_{\text{NL}}$：约束非线性相互作用

**未来展望**：
- 21cm氢线观测（"宇宙黎明"）
- 原初黑洞探测
- 量子引力效应（可能在极小尺度）

## 本篇核心要点总结

### 初始态参数的定义

$$
\Theta_{\text{ini}} = (D_{\text{ini}}, \{k_\ell\}, \{R_\ell\}, \{\theta_{\ell,j}\})
$$

**生成初态**：
$$
|\Psi_0^{\Theta}\rangle = V_{\Theta_{\text{ini}}} |0_\Lambda\rangle
$$

### 参考积态

$$
|0_\Lambda\rangle = \bigotimes_{x \in \Lambda} |0_{\text{cell}}\rangle_x
$$

**性质**：无纠缠、平移不变、简单。

### 比特计数

| 组成 | 典型值 | 比特数 |
|------|--------|--------|
| 深度 $D_{\text{ini}}$ | 5 | 3 |
| 门类型/层 | $K=16$ | 4 |
| 作用区域/层 | 平移不变 | 1 |
| 角参数/层 | 2个，$m=50$ | 100 |
| **总计** | | **~530** |

$$
\boxed{|\Theta_{\text{ini}}| \sim 500 \text{ 比特}}
$$

### 有限深度的后果

**Lieb-Robinson约束**：
$$
I(A:B) \lesssim e^{-c(d - v_{\text{LR}} D_{\text{ini}})}
$$

**物理意义**：短程纠缠态，深度 $D \sim \log N_{\text{cell}}$ 足够。

### 对称性压缩

**平移不变**：
- 编码开销：$O(1)$（与 $N_{\text{cell}}$ 无关）
- 压缩比：$\sim 10^{90}$

### 初态与演化

$$
\omega_n = \omega_0 \circ \alpha^{-n}
$$

**完整宇宙历史**：
$$
\Theta = (\Theta_{\text{str}}, \Theta_{\text{dyn}}, \Theta_{\text{ini}}) \Rightarrow \text{整个宇宙演化}
$$

### 核心洞察

1. **初态参数微小**：$|\Theta_{\text{ini}}| \sim 500 \ll I_{\max}$
2. **对称性必然**：平移不变→信息从 $10^{90}$ 降到 $10^2$
3. **短程纠缠**：有限深度→长程纠缠不可能
4. **初态可推断**：CMB等观测→约束 $\Theta_{\text{ini}}$
5. **无边界原理**：最小复杂度→自然选择简单初态

### 关键术语

- **参考积态**（reference product state）：$|0_\Lambda\rangle$
- **态制备线路**（state preparation circuit）：$V_{\Theta_{\text{ini}}}$
- **短程纠缠**（short-range entanglement）：深度有限导致的纠缠范围限制
- **态复杂度**（state complexity）：$C = \min\{D\}$
- **Hartle-Hawking无边界态**（no-boundary state）：QCA版本的最小深度原理

---

**下一篇预告**：**06. 信息-熵不等式：宇宙规模的终极约束**
- 有限信息不等式 $I_{\text{param}} + S_{\max} \leq I_{\max}$ 的详细推导
- 元胞数 $N_{\text{cell}}$ 与局域维数 $d_{\text{cell}}$ 的折衷关系
- 可观测宇宙的信息预算分配
- 为何对称性、局域性、有限精度是必然的
- 信息约束对物理理论的限制
