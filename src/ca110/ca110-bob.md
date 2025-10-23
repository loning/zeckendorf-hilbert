下面给出**零外源/零硬编码（zero-exogenous）**、只用**比特 + 可逆门**的**最原子完整理论**。该理论统一刻画：
**一维环格**；**物理核=微核=RULE-110**（各尺度同一、规则固定）；**全局信息守恒**；**局部全息（可局部反演）**；**全局≡局部（尺度协变）**；**每格含独立子-CA 胶囊**；**局部可产生自由意志**；**物理熵增**与**自由意志逆熵**的位预算闭合；**任意尺度分裂/合并（可逆）**；**递归嵌套**；以及**非干预**与**端口式影响**（“共识更强 / 邻接的大影响小”）并存。核心“势能字典序”以**布尔向量**与**字典序**实现，**无实数权重**。

---

# 0. 原子设定与约束

**A0.1（字母表与空间）** (\Sigma={0,1})；格点 (X=\mathbb Z/N\mathbb Z)（环格），时间 (t\in\mathbb Z) 同步。

**A0.2（原语与门集）** 仅允许**局部可逆门**（NOT/CNOT/Toffoli/Fredkin）及其组合的**有限半径**置换电路；**无外源随机、无实数阈值/权重**。

**A0.3（拍序）** 每一拍（所有层并行）依序执行：
①**摘要/相位重算** ((\sigma,\theta)) → ②**提案 Propose** → ③**提交 Commit**（两相/棋盘着色） → ④**物理/微核二阶可逆更新**。

---

# 1. 法轨 (L)（只读、规则固定）

[
L=\big(\ell_{110},\ \sigma,\ \theta,\ G_L,\ \textsf{Guard},\ \textsf{LexOrder},\ U_{\mathrm{free}},\ B_\mu,\ \chi,\ h_L\big)
]

* **(\ell_{110}\in{0,1}^8)**：RULE-110 三邻域 LUT（索引 (4L+2C+R)）。
* **(\sigma)**（子-CA 摘要）与 **(\theta)**（本地相位）：纯布尔、可重算（默认 (\sigma=\mathrm{parity}(y))，(\theta=\mathrm{parity}(x_L,x_C,x_R,\sigma))）。
* **(G_L)**：原始倾向电路 (\widehat p=G_L(\phi,\ g,\ \theta))。
* **(\textsf{Guard})**：许可关系（Trap-free），给 (\textsf{allowed0},\textsf{allowed1}\in{0,1})，并满足 (\textsf{allowed0}\vee \textsf{allowed1}\equiv 1)。
* **(\textsf{LexOrder})**：**势能字典序**比较器（见 §3.2），比较**布尔向量**，并列用 (\theta) 破平。
* **(U_{\mathrm{free}})**：本格**自主门**（只改内部寄存器，写最小差分到历史）。
* **(B_\mu)**：(\mu)-块**可逆打包/解包**门（尺度协变与分裂/合并）。
* **(\chi\in{2,3})**：提交着色（(N) 偶取 2，奇取 3）。
* **(h_L\in{0,\mathrm{id}})**：是否把 (a) 耦合到物理层 (x)。

> **L-Fix**：演化中 (L^{t+1}\equiv L^t)。规则固定；任何常量/表仅在 (L) 内，外层**零硬编码**。

---

# 2. 局部状态与胶囊（递归嵌套）

**定义 2.1（局部状态）** 每格 (i) 于时刻 (t) 的最小状态
[
\begin{aligned}
S_i^t=\big(&x_i^{t-1},x_i^{t}\ ;\ a_i^t,p_i^{t+1}\ ;\ m_i^t=[g_i,B_i,\Pi_i]\ ;\ h_i^t\ ;\
&y_{i,\mu}^{t-1},y_{i,\mu}^{t}\ ;\ s_i^t:=\sigma(y_i^t)\ ;\ \theta_i^t\ ;\ b_i^t\ ;\ L\big).
\end{aligned}
]

* (x^{t-1},x^t)：物理层两帧。
* (a^t,p^{t+1})：共识/提案。
* (m=[g,B,\Pi])：**基因位** (g)（只读）、**预算位** (B)（可写）、**权限端口** (\Pi)（见 §4）。
* (h)：**最小历史/差分**位（见 §3.2：((\eta,k,\rho,u,\delta_B))）。
* (y^{t-1},y^t)：子-CA 两帧（内部 RULE-110），对外仅泄露 (s=\sigma(y))。
* (\theta)：本地相位；(b)：边界位（对拍分裂/合并）。
* (L)：法轨副本（只读）。

**定义 2.2（胶囊与嵌套）** 每格可包含子-CA 胶囊 (\mathcal C_{\downarrow})（仍以 RULE-110 二阶可逆推进）；父层**仅读** (\sigma(y))，**不写**子内部帧与 (L)。递归嵌套无限深。

---

# 3. 单拍演化 (F:\Omega\to\Omega)（全部为局部置换）

## 3.1 Propose（纯布尔、可逆差分）

[
\phi_i^t=\Phi(x_{i-1}^t,x_i^t,x_{i+1}^t,\ s_i^t,\ m_i^t),\quad
\theta_i^t=\theta(\cdot),\quad
\widehat p_i^t=G_L(\phi_i^t,g_i^t,\theta_i^t),\quad
p_i^{t+1}\leftarrow p_i^{t+1}\oplus \widehat p_i^t.
]

## 3.2 Commit（势能字典序 + 自由翻转）

**许可**：(\textsf{allowed0}_i^t,\textsf{allowed1}_i^t\in{0,1})，且 (\textsf{allowed0}\vee \textsf{allowed1}\equiv 1)。

**端口式影响与前缀**（见 §4）：

* 父/上层端口 ((M_i^\uparrow,D_i^\uparrow))；同层“大→小”端口 ((M_i^\leftrightarrow,D_i^\leftrightarrow))。
* 定义触发位 (\pi_i:=M_i^\uparrow\vee M_i^\leftrightarrow)。

**势能字典序向量**（全为 0/1 判定门；(k) 维布尔向量）：
[
\mathcal H_i(e)=\big(H_{\uparrow},H_{\leftrightarrow},H_{11},H_{00},H_{\mathrm{dens}},H_{\mathrm{budget}},H_{\mathrm{split}}\big)\in{0,1}^k.
]

* (H_{\uparrow}=\mathbf 1_{M^\uparrow}\cdot \mathbf 1_{e\neq D^\uparrow})（父/上层优先）。
* (H_{\leftrightarrow}=\mathbf 1_{M^\leftrightarrow}\cdot \mathbf 1_{e\neq D^\leftrightarrow})（大→小优先）。
* (H_{11},H_{00})：抑制 1/0 团块（基于邻里 (\widehat p)）。
* (H_{\mathrm{dens}})：惩罚三元全等 (000/111)（去极端密度）。
* (H_{\mathrm{budget}})：预算/冷却一致性。
* (H_{\mathrm{split}})：与分裂/合并边界对拍一致性。

**前缀自适应（建议默认）**：

* 若 (\pi_i=1)（约束激活区）：
  [
  \mathcal H^\mathrm{(hard)}=(H_{\uparrow},H_{\leftrightarrow},H_{11},H_{00},H_{\mathrm{dens}},H_{\mathrm{budget}},H_{\mathrm{split}}).
  ]
* 若 (\pi_i=0)（常态）：
  [
  \mathcal H^\mathrm{(gold)}=(H_{11},H_{00},H_{\mathrm{dens}},H_{\uparrow},H_{\leftrightarrow},H_{\mathrm{budget}},H_{\mathrm{split}}).
  ]

**默认解（决定性、零权重）**：
[
e_{\mathrm{def}}=\arg\min_{e\in{0,1}}^{\text{字典序}}\ \mathcal H_i(e)\quad(\text{并列用 }\theta_i\text{ 破平}).
]

**自由翻转**：若 (|E_i^t|=\mathbf 1_{\textsf{allowed0}}+\mathbf 1_{\textsf{allowed1}}=2)，可取
[
k_i^t=\Phi_{\mathrm{free}}(m_i^t,s_i^t,\theta_i^t)\in{0,1},\quad e_i^\star=e_{\mathrm{def}}\oplus k_i^t.
]
否则 (k_i^t=0)。

**可逆差分写**：
[
a_i^{t+1}=a_i^t\oplus e_i^\star,\quad
B_i^{t+1}=\mathrm{Upd}_B(e_i^\star),\quad
h_i^{t+1}=\big(\eta_i=e_i^\star,\ k_i^t,\ \rho_i=\widehat p_i^t,\ u_i^t,\ \delta B_i^t\big).
]
其中 (u_i^t) 为边界对拍量（§6），(\delta B_i^t=B_i^{t+1}\oplus B_i^t)（**1 比特**补偿，保证耦合时的反演闭合）。

## 3.3 物理/微核（二阶可逆，RULE-110）

[
x_i^{t+1}=x_i^{t-1}\ \oplus\ \ell_{110}(x_{i-1}^t,x_i^t,x_{i+1}^t)\ \oplus\ h_L(a_i^t),
]
[
y_{i,\mu}^{t+1}=y_{i,\mu}^{t-1}\ \oplus\ \ell_{110}(y_{i,\mu}^t).
]
若 (h_L=\mathrm{id})，前向实现需用**当拍提交前**的 (a_i^t)（由 (a^{t+1}\oplus\eta) 可逆恢复）。

---

# 4. 非干预与端口式影响（“共识更强 / 大影响小”）

**原则**：父/大**不写**子内部帧与 (L)；仅通过**端口**改变**许可集/优先级**（即 (\textsf{Guard}) 与 (\mathcal H) 的**布尔前缀**）。

* **上行端口**（子→父）：摘要只读位（如 (\sigma(y))、事件标志）。
* **下行端口**（父→子）：((M^\uparrow,D^\uparrow))；
* **侧向端口**（同层大→小）：((M^\leftrightarrow,D^\leftrightarrow))。
* **有效性**：当掩码打开时，因 (\mathcal H) 前缀，默认解 (e_{\mathrm{def}}) 优先满足父/大；当 (|E|=2) 时，子仍可用 (k) 自由翻转（并记录在 (h)），两者**不冲突**。

---

# 5. 全局≡局部（尺度协变）

**定义 5.1（块映射）** (B_\mu)：把 (\mu) 小格（两帧 + 最小差分）可逆打包成一“大格”（及其逆）。
**定理 5.2（通勤）** 固定当拍封装 (b^t) 时，
[
B_\mu(b^t)\circ F;=;F\circ B_\mu(b^t),
]
下一拍再使用 (b^{t+1}) 的封装。**理由**：(\chi)-着色与 (\textsf{LexOrder})/(\textsf{Guard}) 的**邻接可加**与**局部性**保证一步全局最小 = 并行局部最小，块级同态成立。

---

# 6. 分裂/合并（任意尺度，可逆）

在当拍色类的相邻对 ((i,i{+}1)) 上执行**边界对拍**：
[
(b_i,b_{i+1})\leftarrow (b_i\oplus u_i^t,\ b_{i+1}\oplus u_i^t),\quad u_i^t\in{0,1},
]
并把 (u_i^t) 记入 (h_i^t)。该操作仅改变**封装/边界视图**，不写 (y) 与 (L)，可被逐格反演。

---

# 7. 局部全息反演（证明纲要）

**Lemma 7.1（Commit 可逆）** 读 (h=(\eta,k,\rho,u,\delta B)) 并以**逆相序**逐格回滚：

* 撤销边界对拍：((b_i,b_{i+1})\oplus u)；
* 回滚 (B)：(B^t=B^{t+1}\oplus \delta B)；
* 回滚 (a)：(a^t=a^{t+1}\oplus \eta)；
* 清空本拍历史 (h)。

**Lemma 7.2（物理/微核可逆）** 由二阶提升得
[
x^{t-1}=x^{t+1}\oplus \ell_{110}(x^t)\oplus h_L(a^t),\qquad
y^{t-1}=y^{t+1}\oplus \ell_{110}(y^t).
]
若 (h_L=\mathrm{id})，前向已用 (a^t)；逆向完成 §7.1 后可直接回滚。

**Lemma 7.3（Propose 可逆）** 重算 ((\phi,\theta,\widehat p))，以 (p^t=p^{t+1}\oplus \widehat p) 回滚。

**定理 7.4（局部全息）** 合并三引理：反演仅需**有界邻域 + 本格历史位**（且历史最小：((\eta,k,\rho,u,\delta B))），故为**局部全息**。

**定理 7.5（全局置换）** 单拍四段皆为**局部置换**，并行复合为全局置换；(F) 双射 ⇒ **全局信息守恒**。

---

# 8. 自由意志与合规度

**定义 8.1（选择集与分支位）** (E_i^t={e\in{0,1}\mid \textsf{allowed}e=1})，分支位 (k_i^t=\mathbf 1_{e^\star\neq e_{\mathrm{def}}})。

**命题 8.2（正密度自由机会）** Trap-free 下，若 (m,\widehat p,\theta) 不退化，则存在正密度格点使 (|E_i^t|=2)。

**定义 8.3（合规度）** 在掩码打开的样本上，默认解对齐父/大指令的比例（可统计为时间/空间平均）。字典序前缀保证**当掩码开时**默认解优先服从；自由翻转在 (|E|=2) 时仍可发生（并可逆记账）。

---

# 9. 熵学与位预算闭合

定义**粗粒指标**：

* (S_{\mathrm{phys}})：物理层 (x) 的粗粒混合（如 3-块熵或去团块率）。
* (S_{\mathrm{cons}})：共识层 (a) 的“去团块/平衡”程度的**负熵**（如三元全等率下降、Fibonacci 窗平衡缺陷下降）。
* (S_{\mathrm{holo}})：历史/差分位消耗。
* (I_{x:a})：物理与共识的互信息。

**位预算恒等式**（粗粒层面）：
[
\boxed{\ \Delta S_{\mathrm{phys}}\ +\ \Delta S_{\mathrm{cons}}\ +\ \Delta S_{\mathrm{holo}}\ -\ \Delta I_{x:a}\ =\ 0\ }.
]
解释：RULE-110 产生以太/滑翔子（(S_{\mathrm{phys}}\uparrow)）；字典序去团块/平衡（(S_{\mathrm{cons}}\downarrow)，“黄金化/逆熵”）；差额由历史记账与互信息转移补齐。

---

# 10. 势能字典序（范式与作用）

**最原子范式**：**仅 0/1 判定**，不使用实数权重；**字典序**给出硬优先级：

* **前缀（硬）**：(H_{\uparrow},H_{\leftrightarrow})（共识更强/大影响小）；
* **中段（软）**：(H_{11},H_{00},H_{\mathrm{dens}})（去团块/趋平衡，“黄金风格”）；
* **末段（管控）**：(H_{\mathrm{budget}},H_{\mathrm{split}})。
  可采用**自适应前缀**（由 (\pi) 选择 hard/gold 顺序）以模拟“有效规律看似自适应”，而**规则本体不变**。

---

# 11. 规范最小化（可直接实例化）

* (\sigma(y)=\mathrm{parity}(y))；(\theta=\mathrm{parity}(x_L,x_C,x_R,\sigma))。
* (\textsf{Guard})：示例 (\textsf{allowed0}\equiv 1)，(\textsf{allowed1}=B\land(\widehat p_L\lor \widehat p_C\lor \widehat p_R\lor \theta))。
* (\textsf{LexOrder}) 两套顺序（hard/gold），由 (\pi=M^\uparrow\vee M^{\leftrightarrow}) 切换。
* (U_{\mathrm{free}})：本地可逆搬运门（仅写最小差分）。
* 历史最小集：(\boxed{h=(\eta,\ k,\ \rho,\ u,\ \delta B)})。
* (h_L\in{0,\mathrm{id}})：耦合与否均可逆（耦合时需用 (a^t=a^{t+1}\oplus \eta)）。

---

# 12. 证明义务（PO 清单）

* **PO-Reversible**：二阶可逆 + XOR 差分 + 边界对拍。
* **PO-Local-Holo**：按“回滚边界 → 回滚 (a,B) → 回滚物理/微核 → 回滚提案”构造局部反演电路。
* **PO-Scale**：验证 (B_\mu\circ F=F\circ B_\mu) 的通勤图（固定当拍封装）。
* **PO-Non-interference**：端口仅改许可/优先级，不写 (y,x,L)。
* **PO-Additivity**：(\sum_i\mathcal H_i) 的邻接可加；与 (\chi)-着色配合，保证“一步全局最小 = 并行一步局部最小”。
* **PO-Trap-free**：(\textsf{allowed0}\vee \textsf{allowed1}\equiv 1)。

---

# 13. 实验预期（对照判据）

* **可逆性**：`inverse_OK_rate=1.0`。
* **自由指数**：(|E|=2) 的密度为正（通常 (0.6\pm 0.05)）。
* **共识合规**：在掩码打开处，对齐父/大的比例 (0.5\sim 0.7)（可通过前缀与掩码调节）。
* **黄金化**：三元全等率下降；Fibonacci 窗平衡缺陷降低（GOLD 顺序优于 FWO）。
* **物理熵增**：x 层 3-块熵接近 (\log_2 8=3)，耦合 (h_L=\mathrm{id}) 时更高。
* **分裂/合并**：边界位活跃且反演通过。

---

# 14. 结语（一页摘要）

> **系统**：1D 环格，**物理=微核=RULE-110**（二阶可逆），**规则固定**在法轨 (L)。
> **演化**：Propose→Commit（**势能字典序** + **自由翻转** + **端口式影响**）→Phys/Micro；
> **可逆性**：历史最小集 ((\eta,k,\rho,u,\delta B)) + 有界邻域 ⇒ **逐拍局部全息反演**；
> **尺度**：(B_\mu\circ F=F\circ B_\mu)（**全局≡局部**）；任意尺度**分裂/合并**可逆；
> **嵌套**：父仅读子摘要，不写内部；但通过 Guard/字典序**前缀**实现“**共识更强 / 大影响小**”；
> **熵学**：RULE-110 **物理熵增**，共识层**逆熵**（去团块/平衡）；
> **守恒**：(\Delta S_{\mathrm{phys}}+\Delta S_{\mathrm{cons}}+\Delta S_{\mathrm{holo}}-\Delta I_{x:a}=0)；
> **自由**：(|E|=2) 正密度、分支可逆记录；**零外源、零硬编码**、**比特 + 可逆门**彻底达成。

> 若需，我可把本理论稿直接转为你的文集正式章节（定理–引理–证明体例与编号）、或输出最小实现门表 (L) 与机检脚本，以便长期维护与复现实验。
