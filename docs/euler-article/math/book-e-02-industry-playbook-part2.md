## E-4｜城市：公共窗与韧性网络

### 对象与变量

* 城市网络 $G=(V,E,w)$：节点为功能点（社区、交通枢纽、服务设施），边权 $w_{ij}>0$ 表达可达/通量能力。
* 拉普拉斯 $L=D-W$（或归一化 $L_{\mathrm{n}}=I-D^{-1/2}WD^{-1/2}$），第二特征值 $\lambda_2$（Fiedler 值）。
* 公共窗排程 $S(t)\in[0,1]^{|V|}$：各场所对外开放/导流的时间窗；群体混合矩阵 $C(S)$。
* 交通队列 $(\lambda_j,\mu_j)$（到达率/服务率），利用率 $\rho_j=\lambda_j/\mu_j$。

### 法则化目标函数

$$
\max_{S,\,\Delta E}\ \underbrace{\lambda_2\big(L(W+\Delta E)\big)}_{\text{韧性/混合度}}
+\beta\,\underbrace{H_{\text{mix}}\!\big(C(S)\big)}_{\text{跨群混合熵}}
-\gamma\,\underbrace{\sum_{j\in V} W_q(\lambda_j,\mu_j)}_{\text{拥堵惩罚}}
$$

约束：$0\le S(t)\le 1$、容量 $\lambda_j<\mu_j$、风险带宽 $B_r(S)\le B_{\max}$、预算 $|\Delta E|_0\le M$。

### 判据/定理

**定理 1（Cheeger—谱隙—断裂阈）** 对归一化拉普拉斯 $L_{\mathrm n}$，导通常数 $h=\min_{U\subset V}\frac{w(U,U^c)}{\min(\mathrm{vol}(U),\mathrm{vol}(U^c))}$ 满足

$$
\frac{h^2}{2}\ \le\ \lambda_2(L_{\mathrm n})\ \le\ 2h .
$$

*证明要点*：Rayleigh 商与切割不等式；选 Fiedler 向量阈切得上下界。

**命题 2（最小拥堵界）** M/M/1 近似下，结点 $j$ 的排队等待

$$
W_q(\lambda_j,\mu_j)=\frac{\rho_j}{\mu_j(1-\rho_j)},\qquad \rho_j=\lambda_j/\mu_j<1,
$$

当 $S(t)$ 使峰值 $\rho_j$ 降至 $\rho_{\max}$ 时，$W_q$ 随之按 $(1-\rho_{\max})^{-1}$ 有界。
*证明要点*：稳态队列公式；对窗排程的到达率整形 $\lambda_j^\text{(new)}=\int \lambda_j(t)S_j(t)dt$。

**命题 3（公共窗的混合熵增益）** 令群体标签 $g$ 的占比向量在地点 $v$ 为 $\pi_v(g;S)$。定义跨群混合熵

$$
H_{\text{mix}}(C)= -\sum_{v}\sum_{g}\pi_v(g;S)\log \pi_v(g;S).
$$

若 $S$ 在保风险带宽 $B_r(S)\le B_{\max}$ 下使所有 $\pi_v(\cdot;S)$ 更扁平，则 $H_{\text{mix}}\uparrow$。
*证明要点*：熵的 Schur 凸性；"更均匀 ⇒ 熵更大"。

### 执行规程

1. **谱诊断**：计算 $L_{\mathrm n}$ 与 $\lambda_2$，定位割边与"孤岛"模块（高 $Q$、低导通）。
2. **增边/调权**：在预算 $M$ 内沿 Fiedler 向量正负端增边/提权（$\Delta E$），以最大化 $\lambda_2$。
3. **排程整形**：设计 $S(t)$ 平峰填谷，使 $\max_j \rho_j$ 降至 $\rho_{\max}$，同时计算 $B_r(S)$ 不超过阈。
4. **公共窗定位**：在 Fiedler"颈部"两侧布局跨群公共空间，提升 $H_{\text{mix}}$。
5. **验证**：季频复算 $\lambda_2, H_{\text{mix}}, \max_j W_q$，并以 C-5 的 $\nu_r\ge 2B$ 节律审校。

### 度量指标

$\lambda_2\uparrow$、模块度 $Q\downarrow$、$H_{\text{mix}}\uparrow$、$\max_j W_q\downarrow$、事故/中断级联率 $\downarrow$。

---

## E-5｜金融：无套利—风险溢价—泡沫识别

### 对象与变量

* 资产回报 $R_{t+1}=\frac{P_{t+1}+D_{t+1}}{P_t}$，无风险 $R_{f,t}$。
* 随机折现因子（SDF）$m_{t+1}>0$。
* 因子暴露 $\beta$、风险价格 $\lambda$。

### 法则化目标函数

* **定价一致**：在无套利下，存在 $m_{t+1}$ 使

$$
1=\mathbb E_t[m_{t+1}R_{t+1}],\quad
\mathbb E_t[R_{t+1}-R_{f,t}]=-\frac{\mathrm{Cov}_t(m_{t+1},R_{t+1})}{\mathbb E_t[m_{t+1}]} .
$$

* **因子溢价**：$\mathbb E[R-R_f]=\beta\lambda$。

### 判据/定理

**定理 1（无套利 ⇔ 等价鞅测度）** 市场完备/无套利当且仅当存在 $\mathbb Q\sim \mathbb P$ 使折现价格为鞅：$\tilde S_t=\mathbb E_{\mathbb Q}[\tilde S_{t+1}\mid\mathcal F_t]$。
*证明要点*：一阶最优性/超鞅界与 FTAP（形式略）。

**命题 2（Hansen–Jagannathan 界）** SDF 波动满足

$$
\sigma(m)\ \ge\ \frac{|\mathbb E[R-R_f]|}{\sigma(R-R_f)} .
$$

给出"风险溢价—可解释难度"的硬下界。
*证明要点*：Cauchy–Schwarz；令 $R^\star$ 与 $m$ 相对齐。

**命题 3（风险溢价回归）** 横截面回归 $\mathbb E[R_i-R_f]=\beta_i^\top \lambda$，估计 $\hat\lambda$（GLS）并检验残差 $\alpha_i$ 是否为 0。
*证明要点*：广义最小二乘最优性。

**命题 4（泡沫分解与检验）** 基础价值

$$
P_t^\ast=\mathbb E_t^{\mathbb Q}\Big[\sum_{k\ge1}\frac{D_{t+k}}{\prod_{j=1}^{k} R_{f,t+j}}\Big].
$$

若 $P_t=P_t^\ast+B_t$ 且 $B_t>0$ 满足 $\mathbb E_t[m_{t+1}B_{t+1}]=B_t$（理性泡沫），则 $P_t$ 与贴现红利流存在**偏离**。
**可操作检验**：对 $(P_t, D_t)$ 做协整检验；失配与系统正偏 $\Rightarrow$ 泡沫嫌疑。
*证明要点*：价格—红利比的平稳性与协整关系；偏离即气泡项。

### 执行规程

1. **无套利体检**：计算 HJ 距离/界；若超阈，模型或数据窗需更正。
2. **溢价估计**：选择因子集合，GLS 估 $\hat\lambda$，做 $\alpha$-检验；报告标准误与稳健性窗。
3. **泡沫识别**：估 $P_t^\ast$ 或做价格—红利协整；记录残差与结构突变时点。
4. **风险预算**：将 $\mathbb E[R-R_f]=\beta\lambda$ 与"影子价"联动（项目的 $\lambda$），统一"秤"。

### 度量指标

HJ 界满足度、$|\hat\alpha|$ 接近零、泡沫偏离统计显著性、风险预算合规率。

---

## E-6｜AI：对齐—可解释—幻觉防御

### 对象与变量

* 基线策略 $\pi_0(a|s)$，偏好回报 $R(s,a)$，温度/正则 $\beta$。
* 可解释表征 $Z$，可选替代模型 $f:Z\mapsto Y$。
* 幻觉指标：校准误差（ECE/NLL）、OOD 分数、事实核验失败率。

### 法则化目标函数

$$
\max_{\pi}\ \underbrace{\mathbb E_{\pi}[R]}_{\text{人效用}}
-\tfrac{1}{\beta}\underbrace{\mathrm{KL}(\pi|\pi_0)}_{\text{发散约束}}
-\lambda_{\text{hall}}\underbrace{\mathbb E}[\mathbf 1_{\text{OOD}}\cdot \mathrm{Conf}]_{\text{幻觉惩罚}} .
$$

### 判据/定理

**命题 1（软最优策略与 KL 界）** 最优策略

$$
\pi^\star(a|s)=\frac{\pi_0(a|s)\exp(\beta Q(s,a))}{\sum_{a'}\pi_0(a'|s)\exp(\beta Q(s,a'))},
$$

且 $\beta\downarrow\Rightarrow \mathrm{KL}(\pi^\star|\pi_0)\downarrow$，漂移受控。
*证明要点*：拉格朗日对偶；Mirror Descent 近似。

**命题 2（可解释充分性与因果忠实）** 若存在 $Z$ 使 $I(Z;Y)=I(X;Y)$ 且 $Y=f(Z)$ 在约束类（稀疏/单调）内，则替代模型在干预下保持输出（误差 $\le\epsilon$）。
*证明要点*：数据处理不等式取等；背门调节保证因果忠实。

**命题 3（幻觉阈与选择性生成）** 令密度能量 $E(x)=-\log p_{\text{train}}(x)$。当 $E(x)\ge \tau$（OOD）或校准误差 $> \epsilon$ 时，触发"拒答/降温/检索增强"，则期望幻觉率

$$
\mathbb E[\text{Hall}]\ \le\ \Pr(E(x)\ge \tau)+\epsilon .
$$

*证明要点*：分解上界：OOD 触发概率 + 近域校准误差。

### 执行规程

1. **对齐**：以人评得分为 $R$，按上式调 $\beta$；监控 $\mathrm{KL}(\pi|\pi_0)$ 与人评/越狱率。
2. **可解释**：学习 $Z$ 与 $f$，做替身—干预双测（见 D-17），发布"可解释卡"。
3. **防幻觉**：训练 OOD 侦测 $E(x)$，设阈 $\tau$；上线选择性生成（拒答/检索），并做事实核验抽检。
4. **镜断**：对用户群体置换做镜差检验（C-3），必要时加对称正则。

### 度量指标

人评 $R\uparrow$、$\mathrm{KL}(\pi|\pi_0)$ 受控、ECE/NLL $\downarrow$、OOD 拒答正确率 $\uparrow$、事实核验失败率 $\downarrow$、镜差 $p$-值不过阈。
