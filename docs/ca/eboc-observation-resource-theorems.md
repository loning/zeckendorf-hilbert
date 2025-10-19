# EBOC 观察–资源理论：不完备、不可分辨与面积律

（在 EBOC 框架中抽离的四条核心定理）

**作者**：Auric
**日期**：2025-10-19

---

## 摘要

本文在 EBOC（永恒–静态块 观察-计算）统一框架下，独立陈述并证明四条与“资源化不完备、统计不可分辨、因果厚边界与观测熵单调性”相关的核心结果：（O1）EBOC 观察理论的资源有界不完备；（O2）有限样本下的因子观察者统计不可分辨（以素数密度序列为显式构造）；（O3）厚边界互信息的“面积律”；（O4）观测熵对粗粒化的不增。本文给出自洽的定义、前提与证明要点，并指出其与资源有界不完备性理论（RBIT）及 EBOC 主体定理族的接口。

**关键词**：元胞自动机；SFT；因子映射；Kolmogorov 复杂度；样本复杂度；互信息；熵；RBIT。

---

## 0. 记号与依赖

- 采用 EBOC 文献中的记号：$X_f$ 为空间-时间 SFT；$F$ 为半径 $r$ 的 $d$ 维 CA 全局映射；$\pi$ 为因子译码；厚边界与传播锥如 EBOC 引理 5.3；Følner 窗口族满足 $|\partial W_k|/|W_k|\to 0$；前缀 Kolmogorov 复杂度记为 $K(\cdot)$。
- 统计不可分辨采用积分概率度量在检验族 $\mathcal F_m$ 上的界与资源三元组 $(m,N,\varepsilon)$（见 RBIT）。
- RBIT（docs/zeta-publish/resource-bounded-incompleteness-theory.md）提供两项外部支撑：长度门槛版不完备（定理 4.1）与相对误差样本复杂度下界（定理 4.4）。
 - 概率量（如 $\alpha,N$ 等）均在固定的概率空间上计算，例如：对长度为 $K$ 的窗口作等权随机抽取，或在 CA 的移位不变遍历测度 $\mu$ 下取随机样本。

---

## 1. 主定理

### O1（资源有界不完备：EBOC 观察理论版）

**定理.** 令 $T_{\mathrm{EBOC}}$ 为包含 SFT/CA 语义、厚边界（传播锥）、因子映射、Kolmogorov 复杂度与基础算术的公理化系统，且递归可枚举并一致。对每个 $L\in\mathbb N$，存在 $\Delta_0$ 句子 $G_L$ 使：

1) 若 $T_{\mathrm{EBOC}}$ 一致，则 $\mathbb N\models G_L$；

2) $T_{\mathrm{EBOC}}$ 无长度 $\le L$ 的 $G_L$ 的证明；

3) $G_L$ 等价于“长度 $\le L$ 的证明串中无 $G_L$ 的证明”。

**证明要点.** 由 RBIT 的长度门槛不完备（定理 4.1）对 $T_{\mathrm{EBOC}}$ 应用哥德尔对角化，且 $\mathrm{Proof}_{T_{\mathrm{EBOC}}}(x,y)$ 在标准编码下为 $\Delta_0$ 可定义，立即得到结论。$\square$

---

### O2（统计不可分辨：有限样本下的因子观察者）

**定理.**（前提，二选一其一）

 (a) 令 $M$ 充分大，并在所取区间上采用局部密度近似：$\mathbb P\{s+id\ \text{为素}\}=p:=\tfrac{d}{\varphi(d)}\cdot\tfrac{1}{\ln M}$；或

 (b) 令 $p$ 为该区间的经验密度：$p=\tfrac1K\sum_{i=0}^{K-1}\mathbf1\{s+id\ \text{为素}\}$，以下检验以此 $p$ 为基准。

取步长 $d\in\{2, q\}$（$q$ 为素数）与起点 $s$，在 CA 中通过宏块-强制嵌入序列

$$
b_i=\mathbf1\{s+i d\ \text{为素}\},\qquad i=0,\dots,K-1,
$$

并令目标密度 $p=\tfrac{d}{\varphi(d)}\cdot\tfrac{1}{\ln M}$。若区间满足 $Kd\le (\eta/2)\,M\ln M$ 且因子观察者仅使用检验族 $\mathcal F_m$（频率、一阶自相关、窗口 $\le m$ 的 runs），则当

$$
N\ <\ \frac{3}{\eta^2 p}\,\ln\frac{2}{\alpha}
$$

时，该因子观察者在资源 $(m,N,\varepsilon=\eta p)$ 下无法将该序列与 i.i.d. Bernoulli$(p)$ 区分（不可分辨）。

**证明要点.** 频率检验由 RBIT 样本复杂度下界（定理 4.4）直接给出；由上述前提得密度偏差 $\le \eta p/2$；素数间隔的短程相关在该样本规模下的偏差 $\le \eta p/2$，合并得总体误差 $\le \eta p$。$\square$

---

### O3（厚边界互信息“面积律”，固定 $T$）

**定理.** 在移位不变遍历测度 $\mu$ 下，设 $F$ 为半径 $r$ 的 CA，$W\subset\mathbb Z^d$ 为有限窗口，记 $X_t:=x|_{W\times\{t\}}$，$Y_{t+T}:=x|_{W\times\{t+T\}}$。存在常数 $C=C(\Sigma)$ 使

$$
I\big(X_t;Y_{t+T}\big)\ \le\ C\,r\,T\,\big|\partial W\big|.
$$

因此对任意 Følner 族 $\{W_k\}$ 与固定的 $T$，$I(X_t;Y_{t+T})/|W_k|\to0$（归一化互信息消失）。

**证明要点.** 厚边界与传播锥给出：$Y_{t+T}$ 由 $X_t$ 的 $rT$-膨胀 $W^{+rT}$ 决定，依赖集中在边界带；由数据处理与次可加性，互信息受边界自由度线性上界，得不等式。$\square$

---

### O4（观测熵的粗粒化不增）

**命题.** 在移位不变遍历测度 $\mu$ 下，令观测类目的细分分布为 $p_j(\rho)$，对任意满射分组 $\pi:\{j\}\twoheadrightarrow\{g\}$ 定义粗粒化分布 $p_g(\rho)=\sum_{j\in g}p_j(\rho)$。则对一切 $\rho$，

$$
H_{\mathrm{group}}(\rho):= -\sum_g p_g\log p_g\ \le\ H_{\mathrm{fine}}(\rho):= -\sum_j p_j\log p_j.
$$

**证明.** 熵的链式法则：$H_{\mathrm{fine}}=H_{\mathrm{group}}+\mathbb E[H(\text{组内条件分布})]\ge H_{\mathrm{group}}$，等号当且仅当组内分布退化。$\square$

---

## 2. 接口与应用

- 与 EBOC：O1–O4 分别对应“观测–计算语义的资源不完备”、“因子观察者的统计分辨边界”、“厚边界的可通信信息上界”与“因子粗化的熵单调性”，为 EBOC 主体定理（信息不增、可逆守恒、厚边界传播）提供可检补充。
- 与 RBIT：O1 与 O2 直接依赖 RBIT（资源有界不完备与样本复杂度）；O3 与 O4 则是 EBOC 框架下的纯信息论结论。
- 实证路线：用宏块-强制在 CA 中嵌入素数密度序列；选择 $M,\eta,K$ 满足 O2 的区间与样本约束，即得“不可分辨”演示；互信息边界可通过压缩率与经验互信息估计做数值验证。

---

## 参考文献（指引性）

1. docs/ca/eboc-unified-theory.md（EBOC 主文档：SFT/CA、厚边界、因子映射与复杂度基线）
2. docs/zeta-publish/resource-bounded-incompleteness-theory.md（RBIT：资源有界不完备与样本复杂度定理）
3. D. Lind & B. Marcus, Symbolic Dynamics and Coding（SFT 与因子理论基础）
4. W. Li & P. Vitányi, An Introduction to Kolmogorov Complexity（复杂度与信息论基础）
