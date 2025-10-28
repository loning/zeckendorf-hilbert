# 册 A｜总纲（五法锚与元律）

## 0. 记号与公设

**测度舞台**

* 观察/测量一律写作**窗加权读数**：$\displaystyle \langle f\rangle_W=\int_{\mathbb R} f(E)\,W(E)\,dE$，其中 $W\ge 0$ 且 $\int W=1$。
* **单位变换**与**刻度校准**：若用 $E'=aE$ 重标，则 $W'(E')=a^{-1}W(E'/a)$、$f'(E')=f(E'/a)$，并且 $\langle f\rangle_W=\langle f'\rangle_{W'}$。
* **动力学与记账**：连续方程（或离散守恒）

$$
\partial_t \rho+\nabla\!\cdot J=0\quad\text{或}\quad \rho_{t+1}-\rho_t+\nabla\!\cdot J_t=0 .
$$

* **相位—密度同秤**：在一维散射/谱模型下

$$
\varphi'(E)=\pi\,\rho(E),\qquad \det S(E)=e^{-2\pi i\,\xi(E)},\quad \partial_E\arg\det S(E)=-2\pi\,\xi'(E).
$$

* **分辨—时间下界**：任意窗 $W(t)$ 与其频域 $\widehat W(\omega)$ 满足 $\Delta t\,\Delta\omega\ge \tfrac12$。
* **非渐近误差三分（NPE）**：

$$
\mathrm{Err}\le \underbrace{\mathrm{Alias}(W)}_{\text{混叠}}+\underbrace{\mathrm{Bernoulli}(k,W)}_{\text{有限阶修正}}+\underbrace{\mathrm{Tail}(k)}_{\text{截断尾项}} .
$$

* **KL/I-投影与小步更正**：在约束 $\mathcal C$ 下，最小代价更新

$$
q^\star=\arg\min_{q\in\mathcal C}\mathrm{KL}(q|p),\qquad
\text{并有 Bregman–Pythagoras： } \mathrm{KL}(r|p)=\mathrm{KL}(r|q^\star)+\mathrm{KL}(q^\star|p).
$$

---

## 1. 五法锚（窗·秤·镜·路·账）

### 1.1 窗（Window：可见性的法则）

**定义** 任何读数皆为 $\langle f\rangle_W$。
**推论 1（线性—稳定）** 若 $W\in L^1\cap L^2$ 且 $|W|_1=1$，则 $|\langle f\rangle_W-\langle g\rangle_W|\le |f-g|_\infty$。
**推论 2（不可辨域）** 有限窗族 $\{W_i\}_{i=1}^m$ 定义测量算子 $\mathcal A:f\mapsto(\langle f\rangle_{W_i})_{i=1}^m$。若信号空间维数 $>m$，则 $\ker\mathcal A\neq\{0\}$，存在 $h\ne0$ 使 $\langle h\rangle_{W_i}=0\ \forall i$。

### 1.2 秤（Scale：刻度与单位的法则）

**定义** 刻度改写 $E\mapsto E'=aE$ 守读数：$\langle f\rangle_W=\langle f'\rangle_{W'}$。
**命题（影子价）** 在拉格朗日 $\mathcal L=\mathbb E[U]-\lambda B$ 中，$\lambda=\partial \mathcal L/\partial B$ 为**影子刻度**：衡量预算 $B$ 的边际价值。

### 1.3 镜（Mirror：互换/对偶的法则）

**定义（镜像核）** 若核 $K$ 满足 $K(x)=x^{-a}K(1/x)$，其 Mellin 变换 $\Phi(s)$ 满足完成对称 $\Phi(s)=\Phi(a-s)$。
**判据（公平）** 决策规则 $D$ 在角色互换群 $G$ 下不变：$D(g\cdot \text{data})=D(\text{data})\ \forall g\in G$，则"镜中复断"一致，称**镜像公平**。

### 1.4 路（Path：因果与可复演的法则）

**定义** 可复演路为序列 $x_{t+1}=F(x_t,u_t)$ 在同窗同秤复作下给出稳定读数的策略族 $\{u_t\}$。
**判据（因果可检）** 若存在控制 $u_t$ 使 $x_{t+1}-\hat x_{t+1}$ 在 $t$ 次重复中方差 $\downarrow O(t^{-1})$，则称该路**因果可复演**。

### 1.5 账（Account：守恒与记账的法则）

**定义** 一切出入以连续方程记账：$\partial_t\rho+\nabla\!\cdot J=0$。
**推论（最小补偿）** 若扰动源项 $\sigma$ 使守恒破坏：$\partial_t\rho+\nabla\!\cdot J=\sigma$，则最小控制 $u$ 使闭合的代价

$$
\inf_u |u|\quad\text{s.t.}\quad \partial_t\rho+\nabla\!\cdot(J+u)=0
$$

定义"最小补偿量"。

---

## 2. 元律八条（根因命题与推理要点）

### 元律一｜有限窗不完备（谦卑之根）

**断语** 凡窗皆漏，盲区由结构决定。
**命题（核非空）** 令 $\mathcal W=\mathrm{span}\{W_i\}_{i=1}^m$。若 $f$ 属于高维/无限维函数类（如 $L^2$），则 $\ker \mathcal A\neq\{0\}$。
**证明要点** 线性算子 $\mathcal A: L^2\to\mathbb R^m$ 秩 $\le m$，由秩—核定理得 $\dim\ker\mathcal A=\infty$。
**推论（实践）** 重大断言须"换三窗"（来源/时段/人群），否则处在不可辨域。

### 元律二｜镜像不变 ⇒ 公平（互换判据）

**断语** 能在镜中互换而不失真的，才叫公。
**定理（镜像核—完成对称）** 若 $K(x)=x^{-a}K(1/x)$，则 $\Phi(s)=\int_0^\infty K(x)\,x^{s-1}dx$ 满足 $\Phi(s)=\Phi(a-s)$。
**证明要点** 代入 $x\mapsto 1/x$，得 $\Phi(s)=\int K(1/x)\,x^{-s-1}\,dx=\int x^{a}K(x)\,x^{-s-1}\,dx=\Phi(a-s)$。
**推论（制度）** 决策器 $D$ 对角色置换群 $G$ 不变 ⇔"镜中复断"一致，故公平可检。

### 元律三｜相位导数等密度（意义可计）

**断语** 方向（相位）与厚度（密度）是同一秤两面。
**定理（相位—密度）** 在一维散射/谱框架，$\varphi'(E)=\pi\,\rho(E)$；同时 $\det S(E)=e^{-2\pi i\,\xi(E)}\Rightarrow \partial_E\arg\det S=-2\pi\,\xi'(E)$。
**证明要点** 由 Birman–Kreĭn 公式与谱移 $\xi$ 的导数即相对谱密度，结合相位—散射关系。
**推论（配重判据）** 给定目标"方向词"，其资源配比表若与 $\rho$ 不一致，则为"伪愿"。

### 元律四｜分辨—时间下界（代价之根）

**断语** 分得更清，必付更多时。
**定理（Heisenberg-型）** 设 $\mu_t,\mu_\omega$ 为 $W$ 与 $\widehat W$ 的方差，则 $\Delta t\,\Delta\omega\ge \tfrac12$。
**证明要点** Cauchy–Schwarz 及傅里叶变换的不等式。
**推论（流程）** 重要决策配置最小等待窗 $T_{\min}$，违规急断记入"越界账"。

### 元律五｜KL-仁慈（最小代价更正）

**断语** 真正的宽恕是最小代价对齐，而非重置。
**定理（I-投影最优）** 在凸约束 $\mathcal C$ 下，$q^\star=\arg\min_{q\in\mathcal C}\mathrm{KL}(q|p)$ 最小化信息代价且给出 Bregman–Pythagoras 分解。
**证明要点** KL 为 Bregman 散度；I-投影为最近点；Mirror Descent 累积遗憾 $O(\sqrt T)$。
**推论（组织）** 推行"KL 小步改错"可控反弹与后悔。

### 元律六｜NPE 三分（迷惑之源）

**断语** 多数谬误源自结构性误差：混叠、少修、尾项。
**命题（非渐近上界）** 存在 $k,W$ 使 $\mathrm{Err}\le \mathrm{Alias}(W)+\mathrm{Bernoulli}(k,W)+\mathrm{Tail}(k)$。
**证明要点** Nyquist 频段外别名项；有限阶 Euler–Maclaurin 的伯努利修正；截断尾项以绝对可和界。
**推论（执行）** "三修"达阈前不扩散。

### 元律七｜指针基与谱隙（神圣/权威之源）

**断语** 常被读且抗扰者，自然上升为"圣"。
**定理（收敛与鲁棒）** 设马尔可夫/观测核 $T$ 的主特征值 $\lambda_1$ 与次特征值 $\lambda_2$，谱隙 $\Delta=\lambda_1-\lambda_2>0$ 则 $T^n x/|T^n x|\to v_1$，扰动界 $|v_1-\tilde v_1|\le C|T-\tilde T|/\Delta$。
**证明要点** Perron–Frobenius 与 Davis–Kahan 夹角不等式。
**推论（制度）** 以谱隙阈值选"权威/规范流程"。

### 元律八｜共识采样下限（防混叠频率）

**断语** 校准过慢，必生混叠。
**定理（采样阈）** 议题有效带宽 $B$ 时，校准频率 $\nu_r\ge 2B$ 方能防混叠。
**证明要点** 采样定理：频谱折叠导致伪稳态。
**推论（治理）** 周/月会频率按带宽设下限，降频须评估混叠风险。

---

## 3. 术语与符号（统一口径）

* **窗**：$W$；**同窗**＝同来源/时段/带宽。
* **秤**：单位/刻度/代价函数；影子刻度 $\lambda$。
* **镜**：角色互换群 $G$；镜像核 $K$、完成函数 $\Phi$。
* **路**：可复演序列 $x_{t+1}=F(x_t,u_t)$。
* **账**：$\partial_t\rho+\nabla\!\cdot J=0$ 与最小补偿 $\inf_u|u|$。
* **相位—密度**：$\varphi'(E)=\pi\rho(E)$；谱移 $\xi$。
* **NPE**：$\mathrm{Err}\le \mathrm{Alias}+\mathrm{Bernoulli}+\mathrm{Tail}$。
* **KL 小步**：$q^\star=\arg\min_{q\in\mathcal C}\mathrm{KL}(q|p)$；Mirror Descent 遗憾 $O(\sqrt T)$。
* **谱隙**：$\Delta=\lambda_1-\lambda_2$；指针基 $v_1$。
* **采样阈**：$\nu_r\ge 2B$。

---

## 4. 本册小结（形式化要点）

1. **看见之前先写窗**：$\langle f\rangle_W$ 与不可辨域由 $\ker\mathcal A$ 确定。
2. **判断之前先校秤**：变量代换守读数，影子刻度 $\lambda$ 定边际代价。
3. **公平可被证明**：镜像核 $K$ 与完成对称 $\Phi(s)=\Phi(a-s)$ 给出互换不变性。
4. **意义可被计量**：$\varphi'(E)=\pi\rho(E)$；谈方向必配密度。
5. **清明有代价**：$\Delta t\,\Delta\omega\ge \tfrac12$。
6. **更正有最优**：KL-I 投影与 Bregman–Pythagoras。
7. **谬误有结构**：NPE 三分闭合误差账。
8. **神圣有判据**：谱隙 $\Delta>0$ 选指针基。
9. **共识有频率**：$\nu_r\ge 2B$ 防混叠。
