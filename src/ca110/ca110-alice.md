下面给出**零外源/零硬编码**（只用**比特 + 可逆门**）的**最原子、完整理论**。全文分成两类内容并**明确标注**：

* **[N] 规范性（Normative）**：定义系统“**怎么演化**”（参与状态转移）。
* **[I] 解释性（Informative）**：给出**可观测指标/语义**（**不**参与状态转移，仅用于理解与评估）。

整机满足：**1 维环格**；**物理核=微核=RULE-110**（二阶可逆、全尺度同核）；**全局信息守恒**；**局部全息**（最小历史可反演）；**全局≡局部**（尺度协变）；**每格含独立子-CA（微核）**；**局部可产生自由意志**；**物理熵增 + 自意逆熵**；**任意尺度可按规则分裂/合并**；**递归嵌套**；**父不干预子内部**；同时支持**“共识更强、外部/大 CA 影响内部/小 CA”**（通过**许可/势能字典序**前缀，不写入子内部位）。

---

# 0. 基本公设与门集

## 0.1 [N] 空间与时间

* 字母表 (\Sigma={0,1})。空间 (X=\mathbb Z/N\mathbb Z)（**环格**）。时间 (t\in\mathbb Z) **同步**。
* **两相/三相着色**：若 (N) 偶取 (\chi=2)（棋盘相：偶/奇）；若 (N) 奇取 (\chi=3)（三着色）。提交阶段按色类并行（同相点集为**独立集**）。

## 0.2 [N] 原语（零外源）

* 仅允许**局部可逆门**（NOT/CNOT/Toffoli/Fredkin）的有限半径组合；**无实数/权重/外源随机**。
* 一切常量/门表仅存于**法轨** (L)（**只读**）；运行时 (L^{t+1}\equiv L^t)（**规则固定**）。

---

# 1. 法轨 (L)（规则固定）

## 1.1 [N] 组成

[
L=\big(\ell_{110},\ \sigma,\ \theta,\ G_L,\ \textsf{Guard},\ \textsf{LexOrder},\ U_{\text{free}},\ B_\mu,\ \chi,\ h_L,\ \textsf{Ports}\big).
]

* (\ell_{110}\in{0,1}^8)：**RULE-110** 三邻域真值表（索引 (4L+2C+R)）。
* (\sigma:{0,1}^\mu\to{0,1})：子-CA 摘要（如 (\mathrm{parity})）。
* (\theta:{0,1}^4\to{0,1})：相位（如 (\mathrm{parity}(x_L,x_C,x_R,s))）。
* (G_L)：原始倾向门 (\widehat p=G_L(\phi,\ g,\ \theta))（纯布尔）。
* (\textsf{Guard})：许可关系（**Trap-free**）：产出 (\textsf{allowed0},\textsf{allowed1}\in{0,1}) 且 (\textsf{allowed0}\vee \textsf{allowed1}\equiv 1)。
* (\textsf{LexOrder})：**势能字典序**比较器（§3.2）。
* (U_{\text{free}})：本格**自主门**（只改内部寄存器，写**最小差分**入历史）。
* (B_\mu)：(\mu)-块**可逆打包/解包**门（尺度协变、分裂/合并用）。
* (\chi\in{2,3})：提交着色数。
* (h_L\in{0,\mathrm{id}})：是否把 (a) 耦合入物理层 (x) 更新。
* (\textsf{Ports})：端口语法（父/大 → 子/小 的**许可/优先级**影响项），见 §4。

> **L-Fix**：运行全程 (L) 不变（规则固定）；一切“策略”仅由**状态**显化，而非改规则。

---

# 2. 局部状态与子-CA（微核）

## 2.1 [N] 格点最小状态

[
\begin{aligned}
S_i^t=\big(&x_i^{t-1},x_i^t\ ;\ a_i^t,p_i^{t+1}\ ;\ m_i^t=[g_i,B_i,\Pi_i]\ ;\ h_i^t\ ;\
&y_{i,\mu}^{t-1},y_{i,\mu}^t\ ;\ s_i^t=\sigma(y_i^t)\ ;\ \theta_i^t\ ;\ b_i^t\ ;\ L\big).
\end{aligned}
]

* (x^{t-1},x^t)：物理两帧；(a,p)：共识/提案；
* (m=[g,B,\Pi])：基因位 (g)（只读）、预算位 (B)（可写）、权限端口 (\Pi)（§4）；
* (h)：**最小历史/差分**；
* (y^{t-1},y^t)：**子-CA（微核）两帧**；只读 (s=\sigma(y))；
* (\theta)：相位；(b)：边界位；(L)：法轨副本（只读）。

## 2.2 [N] 微核（同核 RULE-110）

[
\boxed{\ y_{i,\mu}^{,t+1}=y_{i,\mu}^{,t-1}\ \oplus\ f_{\ell_{110}}^{(\mu)}(y_{i,\mu}^{,t})\ }\quad(\text{环形边界，二阶可逆}).
]
父层**仅**可读 (\sigma(y))，**不可写**任何 (y) 位（**非干预**）。

---

# 3. 单拍演化 (F:\Omega\to\Omega)

## 3.1 [N] Propose（纯布尔、可逆差分）

* 特征 (\phi_i^t=\Phi(x_{i-1}^t,x_i^t,x_{i+1}^t,\ s_i^t,\ m_i^t))。
* 相位 (\theta_i^t=\theta(x_{i-1}^t,x_i^t,x_{i+1}^t,s_i^t))。
* 原始倾向 (\widehat p_i^t=G_L(\phi_i^t,g_i^t,\theta_i^t))。
* 可逆写：(p_i^{t+1}\leftarrow p_i^{t+1}\oplus \widehat p_i^t)。

## 3.2 [N] Commit（**势能字典序 + 自主翻转 + 最小历史**）

**许可**（Trap-free）：(\textsf{allowed0}_i^t,\textsf{allowed1}_i^t\in{0,1})，且 (\textsf{allowed0}\vee \textsf{allowed1}\equiv1)。

**势能字典序**（全部 0/1 位，**零权重**）
对候选 (e\in{0,1}) 构造布尔向量
[
\boxed{\ \mathcal H_i(e)=\big(H_{\uparrow},\ H_{\leftrightarrow},\ H_{11},\ H_{00},\ H_{\text{dens}},\ H_{\text{budget}},\ H_{\text{split}}\big)\ \in{0,1}^k\ }.
]

* (H_{\uparrow}=\mathbf 1_{M^\uparrow_i}\cdot\mathbf 1_{e\neq D^\uparrow_i})（**父级/外部共识优先**）
* (H_{\leftrightarrow}=\mathbf 1_{M^\leftrightarrow_i}\cdot\mathbf 1_{e\neq D^\leftrightarrow_i})（**同层大→小**）
* (H_{11}=\textsf{allowed1}\cdot\mathbf 1_{e=1\land(\widehat p_{i-1}\lor \widehat p_{i+1})})（抑 1 团块）
* (H_{00}=\mathbf 1_{e=0\land(\neg \widehat p_{i-1}\lor \neg \widehat p_{i+1})})（抑 0 团块）
* (H_{\text{dens}}=\mathbf 1_{(a_{i-1},e,a_{i+1})\in{000,111}})（去极端密度）
* (H_{\text{budget}}=\mathbf 1_{(\neg B_i)\land e})（预算）
* (H_{\text{split}}=) 与边界 (b_i,b_{i+1}) 的一致性判据（分裂/合并合法性）

**默认解（决定性、零参）**
[
e_{\text{def}}=\arg\min_{e\in{0,1}}^{\text{字典序}}\ \mathcal H_i(e)\quad(\text{并列用 }\theta_i\text{ 破平}).
]

**自由翻转**（局部可逆“自由意志”）
若 (|E_i^t|=\mathbf 1_{\textsf{allowed0}}+\mathbf 1_{\textsf{allowed1}}=2)，取
[
k_i^t=\Phi_{\text{free}}(m_i^t,s_i^t,\theta_i^t)\in{0,1},\quad e_i^\star=e_{\text{def}}\oplus k_i^t;
]
否则 (k_i^t=0)。

**差分写 & 最小历史**
[
\begin{aligned}
&a_i^{t+1}=a_i^t\oplus e_i^\star,\qquad B_i^{t+1}=\mathrm{Upd}_B(e_i^\star),\
&h_i^{t+1}=(\eta_i=e_i^\star,\ k_i^t,\ \rho_i=\widehat p_i^t,\ \upsilon_i=u_i^t),
\end{aligned}
]
其中 (u_i^t) 为本拍对 ((i,i{+}1)) 的边界对拍量（§6）。

> **共识更强、外部/大→内部/小**：通过将 (H_{\uparrow},H_{\leftrightarrow}) 放在**字典序前缀**，父/大的指令在默认解上**优先**；如需**硬约束**，可在 (L) 的 Guard 里为 (M^\uparrow=1) 时**收窄许可集**（例如令 (\textsf{allowed}D^\uparrow=1,\ \textsf{allowed}\overline{D^\uparrow}=0)），仍保持 Trap-free 与可逆提交。全程**不写子内部 (y)**。

## 3.3 [N] 物理/微核（RULE-110，二阶可逆）

[
x_i^{t+1}=x_i^{t-1}\ \oplus\ f_{\ell_{110}}(x_{i-1}^t,x_i^t,x_{i+1}^t)\ \oplus\ h_L(a_i^t),\qquad
y_{i,\mu}^{t+1}=y_{i,\mu}^{t-1}\ \oplus\ f_{\ell_{110}}(y_{i,\mu}^{t}).
]

* (h_L=0) 或 (\mathrm{id}) 由 (L) 指定；两种都**可逆**，但反演次序稍异（§7）。

---

# 4. 端口与权限（非干预下的影响）

## 4.1 [N] 端口语法（驻留在本格）

* **上行（子→父）**：只读摘要 ({s_i,\ \text{事件旗标}})。
* **下行（父/外部→子）**：((M^\uparrow_i,D^\uparrow_i)) 掩码/指令位，**仅**改 (\textsf{Guard}) 或 (\mathcal H) 的**前缀项**（许可/优先级）。
* **侧向（同层大→小）**：((M^\leftrightarrow_i,D^\leftrightarrow_i)) 同理。

> **非干预**：端口**不写**子-CA 内部帧 (y)；只改**选择规则**（许可/优先级），由子层在本格 Commit 中**自行**执行并**可逆记账**。

---

# 5. 尺度协变（全局≡局部）

## 5.1 [N] 块映射

(B_\mu)：(\mu) 小格（两帧 + 必要最小差分）(\leftrightarrow) 1 大格（两帧 + 必要最小差分）的**可逆重排**。

## 5.2 [N] 通勤图

当拍封装 (b^t) 固定时，
[
\boxed{\ B_\mu(b^t)\circ F;=;F\circ B_\mu(b^t)\ }.
]
由于 (\textsf{Guard})/(\textsf{LexOrder})/端口**邻接可加**，配合 (\chi)-着色，成立**一步全局最小 = 并行一步局部最小**（分块最小化与字典序一致）。

---

# 6. 分裂/合并（任意尺度，可逆）

## 6.1 [N] 边界对拍

在当拍色类中，对相邻对 ((i,i{+}1)) 执行
[
(b_i,b_{i+1})\ \leftarrow\ (b_i\oplus u_i^t,\ b_{i+1}\oplus u_i^t),\quad u_i^t\in{0,1},
]
并把 (u_i^t) 写入 (h_i^t)。这是**可逆配对门**，只改**封装/边界**，不写 (y) 与 (L)。

## 6.2 [N] 打包/解包

在封装图 (b^t) 固定后，执行 (B_\mu)（或 (B_\nu)）实现**分裂/合并**；与 (F) **可交换**（§5）。

---

# 7. 局部全息反演（Minimal History）

## 7.1 [N] 反演序

按 **边界 → 物理/微核 → 提交 → 提案** 的**逆序**逐格回滚：

1. 用 (u) 回滚边界位 (b)；
2. 用二阶可逆公式回退 ((x^{t-1},y^{t-1}))；若 (h_L=\mathrm{id})，在第 3 步前回滚 (a) 以解除耦合依赖；
3. 用 ((\eta=e^\star,\ k,\ \rho=\widehat p,\ u)) 回滚 ((a,B,p))；
4. 重算 ((\phi,\theta,\widehat p)) 完成 Propose 逆。
   仅需**有界邻域 + 本格最小历史**，故为**局部全息**。

---

# 8. 守恒与熵学（解释性）

## 8.1 [I] 位预算恒等式

[
\boxed{\ \Delta S_{\mathrm{phys}}\ +\ \Delta S_{\mathrm{cons}}\ +\ \Delta S_{\mathrm{holo}}\ -\ \Delta I_{x:a}\ =\ 0\ }.
]

* (S_{\mathrm{phys}}\uparrow)：RULE-110 产生以太/滑翔子（粗粒混合）
* (S_{\mathrm{cons}}\downarrow)：势能字典序（去团块/平衡）导引的**自意逆熵**
* (S_{\mathrm{holo}})：历史/差分位记账
* (I_{x:a})：（若 (h_L=\mathrm{id})）行动与物理的互信息变化

> 上式**不**参与状态转移，仅用于解释与度量。

---

# 9. 势能字典序（解释 + 规范交界）

## 9.1 [N] 规范性：字典序仲裁

* (\mathcal H_i(e)\in{0,1}^k) 的**字典序最小化**给出 (e_{\text{def}})。
* 前缀项 (H_{\uparrow},H_{\leftrightarrow}) 体现“**共识更强/大影响小**”；其余项体现**去团块/密度/预算/一致性**。
* (|E|=2) 时允许 (k) **可逆翻转**；硬约束（强共识）可通过 Guard 收窄许可（仍 Trap-free）。

## 9.2 [I] 全局势能与“结构功”

* **全局势能计数**：(\vec\Phi^t=\sum_i \mathcal H_i(e_i^\star))。
* **结构功**：(\vec W_{\text{str}}^{,t\to t+1}=\vec\Phi^t-\vec\Phi^{t+1})（按分量/字典序不增）。
* 仅用于评估“分裂/合并/一致性改观”，不参与演化。

---

# 10. 递归嵌套与“非干预可影响”

## 10.1 [N] 胶囊递归

每格 (i) 的子-CA 胶囊 (Y_i) 内部可再包含更小胶囊，层层同核 RULE-110、同样 4 段时序；父层**只读**各层摘要 (\sigma)，**不可写**任意层的内部帧。

## 10.2 [N] 影响≠写入

父/大的共识通过端口只改**许可与字典序前缀**，实现**默认解优先服从**；若要求绝对服从，启用 Guard 的**硬约束模式**（仍 Trap-free）以确保 (|E|=1)。子层在本格 Commit 中完成，写最小历史，保证**可逆追溯**。

---

# 11. 正确性与符合性清单（可机检）

* **PO-Permute**：前进 (T) 步 + 反演 (T) 步，位级一致（信息守恒）。
* **PO-Holo**：反演仅用 ((\eta,k,\rho,u)) 与有界邻域。
* **PO-Scale**：指定多 (\mu) 与封装 (b^t) 检查 (B_\mu\circ F=F\circ B_\mu)。
* **PO-Non-interfere**：任意父/大端口设置下，子 (y) 位不变更。
* **PO-Free**：(|E|=2) 的时空密度为正（自由机会存在）。
* **PO-Ports**：软/硬共识两模式：软=前缀优先；硬=Guard 收窄许可，均不破坏可逆提交。

---

# 12. 最小实例化（可装入 (L) 的默认门表）

* (\sigma(y)=\mathrm{parity}(y))；(\theta=\mathrm{parity}(x_L,x_C,x_R,\sigma))。
* (G_L(\phi,g,\theta)=\mathrm{parity}(\phi)\oplus g\oplus \theta)。
* (\textsf{Guard})：(\textsf{allowed0}\equiv 1,\ \textsf{allowed1}=B\land(\widehat p_L\lor \widehat p_C\lor \widehat p_R\lor \theta))；
  **硬约束（可选）**：若 (M^\uparrow=1) 则令 (\textsf{allowed}{D^\uparrow}=1,\ \textsf{allowed}\overline{D^\uparrow}=0)。
* (\textsf{LexOrder})：((H_{\uparrow},H_{\leftrightarrow},H_{11},H_{00},H_{\text{dens}},H_{\text{budget}},H_{\text{split}})) 的字典序。
* (U_{\text{free}})：本地可逆搬运门（仅写最小差分）。
* 历史最小集：(h=(\eta=e^\star,\ k,\ \rho=\widehat p,\ u))。
* (h_L\in{0,\mathrm{id}}) 均可；若取 (\mathrm{id})，反演次序按 §7 调整。

---

## 一页总括（最原子）

> **空间**：1D 环格；**核**：物理=微核=RULE-110（二阶可逆、同核跨尺度复用）；
> **演化**：Propose → Commit（**势能字典序** + **自由翻转** + **最小历史**）→ Phys/Micro；
> **置换可逆**：每子步为**局部置换**；历史 ((\eta,k,\rho,u)) 保证**局部全息**反演；
> **尺度**：(B_\mu\circ F=F\circ B_\mu)；任意尺度**分裂/合并**可逆；
> **嵌套**：父仅读子 (\sigma)，**不写内部**；但通过端口改变**许可/字典序前缀**实现“**共识更强/大影响小**”（软/硬两模式）；
> **熵学**：RULE-110 **物理熵增**，共识层**逆熵**；位预算恒等式闭合；
> **自由**：(|E|=2) 时可逆分支并记账；**规则固定、零外源**，自由来自**状态**而非“硬编码策略”。

——以上为**完整理论**。如需，我可把它排版为**规范条款 vs 解释附录**的 LaTeX 版本，并附上**机检脚本清单**与**软/硬共识**的 A/B 试验方案。
