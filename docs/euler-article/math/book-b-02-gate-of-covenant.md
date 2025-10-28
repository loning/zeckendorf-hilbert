## 第二门｜约之门（圣域篆・长愿灯・清账符・共识印）

> 体例同前：每条含**法条**（简述）、**数学推理**（判据/证明要点）、**可检步骤**（最小可复演），统一使用册 A 的记号与公设。

---

### 5. 圣域篆（"圣"＝稳定指针基）

**法条**
凡经反复读而不乱、遇扰不偏者，称"圣"。其数理像即"指针基"与谱隙：稳定方向 $v_1$ 与谱隙 $\Delta=\lambda_1-\lambda_2>0$。

**数学推理**
(1) 设行为/流程的更新核为 $T$（马尔可夫或线性正算子），主特征值为 $\lambda_1$（规范化为 $1$），次特征值为 $\lambda_2$。则反复观测有 $T^n x/|T^n x|\to v_1$，收敛速率受谱隙控制：$|T^n-\mathbf{1}v_1^\top|\le C\,|\lambda_2|^n=C\,e^{-n\Delta'}$（其中 $\Delta'=-\log|\lambda_2|$，等价于谱隙）。
(2) 抗扰性由 Davis–Kahan 夹角不等式界定：若扰动 $\tilde T$ 满足 $|T-\tilde T|\le \varepsilon$，则指针方向偏移 $\sin\angle(v_1,\tilde v_1)\le \varepsilon/\Delta$。谱隙越大，越"圣"。
(3) "圣度指标"可取 $S=\Delta/\varepsilon_{\text{env}}$，其中 $\varepsilon_{\text{env}}$ 为环境典型扰动尺度；当 $S\ge S_0$（阈值）时，流程可晋升"圣规"。

**可检步骤**
（i）由 30 天日志估计 $T$；（ii）求 $\lambda_1,\lambda_2$ 得谱隙 $\Delta$；（iii）做"小扰动压力测评"估 $\varepsilon_{\text{env}}$；（iv）计算 $S=\Delta/\varepsilon_{\text{env}}$。若 $S\ge S_0$ 且复演误差 $\downarrow O(n^{-1})$，列入"圣规清单"。

---

### 6. 长愿灯（祈＝权重重排＋延长时间窗）

**法条**
祈愿是把优先级写入权重并"拉长时间窗"。最优的重排满足一个"软最大化"，日更以"KL 小步"。

**数学推理**
(1) 在预算 $\sum_i w_i=1$，$w_i\ge 0$ 下，最大化"效用－惩罚"

$$
\max_{w}\ \sum_i w_i u_i-\tau\,\mathrm{KL}(w|w_0) .
$$

一阶条件给出软最优权重 $w_i^\star=\dfrac{w_{0,i}\,e^{u_i/\tau}}{\sum_j w_{0,j}\,e^{u_j/\tau}}$。这就是"把愿望写进秤"的闭式式子。
(2) 日常更新用 Mirror Descent 的指数权重法（KL 小步）：$w_i^{+}\propto w_i\,\exp(\eta\,\hat g_i)$，其中 $\hat g_i$ 是当日梯度估计（收益或进展信号），并归一化；其累积遗憾为 $O(\sqrt{T})$。
(3) 延长时间窗降低波动：若日序列自相关系数为 $\rho\in[0,1)$，长度为 $T$ 的移动平均方差近似 $\mathrm{Var}(\overline X_T)\approx \sigma^2\,\dfrac{1+\rho}{1-\rho}\cdot \dfrac{1}{T}$。定义有效样本数 $T_{\mathrm{eff}}=T\cdot \dfrac{1-\rho}{1+\rho}$。拉长窗即增大 $T_{\mathrm{eff}}$，故"愿"需配"久"。

**可检步骤**
选三类投入 $i=1,2,3$（如时间、练习、联络），估计 $u_i$ 与初始 $w_{0,i}$，按 $w^\star$ 设每日"一分钟动作"，用 $w^{+}\propto w\exp(\eta\hat g)$ 更新；每 7 天计算 $\overline X_T$ 的方差是否 $\downarrow$ 且目标相关事件频率是否 $\uparrow$。

---

### 7. 清账符（罪＝破坏守恒；赦＝最小补偿＋复路）

**法条**
"罪"是对公共账本的破坏；"赦"是以最小代价重闭守恒并恢复可复演路径。

**数学推理**
(1) 守恒破坏写作 $\partial_t \rho+\nabla\!\cdot J=\sigma$。令控制通量为 $u$，最小能量补偿问题

$$
\min_{u}\ \int_0^T\!\!\int |u|^2\quad \text{s.t.}\quad \partial_t \rho+\nabla\!\cdot(J+u)=0 .
$$

拉格朗日乘子法给欧拉–拉格朗日方程：最优 $u^\star=-\nabla \phi$，势函数 $\phi$ 解泊松型方程 $-\Delta \phi=\sigma$。最小能量为 $\int |\nabla \phi|^2=\langle \sigma,\phi\rangle$，下界为 $|\sigma|_{\mathcal H^{-1}}^2$。
(2) 离散图网络上，图拉普拉斯 $L\phi=\sigma$，最小代价 $\phi^\top L \phi$。这给出"补偿账"的可计算度量。
(3) **赦后复路**需要策略分布的"KL 小步"回可行域：在约束 $\mathcal C$ 下令 $q^\star=\arg\min_{q\in\mathcal C}\mathrm{KL}(q|p)$。由 Bregman–毕达哥拉斯，任意后续目标分布 $r$ 满足 $\mathrm{KL}(r|p)=\mathrm{KL}(r|q^\star)+\mathrm{KL}(q^\star|p)$，即"先复账，再上路"减少后悔。

**可检步骤**
识别源项 $\sigma$（何处破坏守恒），解 $-\Delta\phi=\sigma$（或 $L\phi=\sigma$）估算最小补偿；执行"最小闭环补偿"并用 $q^\star$ 重设策略；30 天后复查：守恒误差是否 $\downarrow$，复路流程的复演误差是否 $\downarrow O(n^{-1})$。

---

### 8. 共识印（仪式＝定期校窗校秤；采样频率有下限）

**法条**
仪式的本质是"同窗同秤"的定期校准；其频率必须不低于议题带宽的两倍，方可防混叠与伪稳态。

**数学推理**
(1) 设议题状态 $y(t)$ 的有效带宽为 $B$。若校准频率 $\nu_r<2B$，则离散采样的频谱折叠产生混叠，群体读数进入伪稳态；故需 $\nu_r\ge 2B$。
(2) 群体共识迭代写作 $x_{t+1}=W x_t$，其中 $W$ 为行和为 $1$ 的权重矩阵。若 $W$ 原始且非负，则 $x_t\to \bar x\mathbf{1}$（$\bar x$ 为均值），收敛速率由谱半径 $\rho\big(W-\tfrac{1}{n}\mathbf{1}\mathbf{1}^\top\big)=\lambda_2(W)$ 控制，谱隙 $1-\lambda_2(W)$ 越大，共识越快。
(3) 当议题随时间变动 $y(t)$ 时，若会期间隔为 $\Delta t$，则"共识误差"含两项：传播误差 $\propto \lambda_2(W)^{k}$ 与跟踪误差 $\propto |y(t)-y(t-\Delta t)|$。选 $\Delta t$ 与 $W$ 使二者总和最小，且守住 $\nu_r=1/\Delta t\ge 2B$。

**可检步骤**
为每类议题估计带宽 $B$（近 4–8 周的频谱或变化率），设置会频 $\nu_r\ge 2B$。会议程序：先对"窗/秤"记名表决（统一来源/时段/单位），再执行"误差先报"（不确定与假设），最后发"最小闭环单"。每季评估 $\lambda_2(W)$ 与争议率下降幅度，必要时重构 $W$（增加跨组连接，扩大谱隙）。

---

## 小结（约之门）

5. **圣域篆**以谱隙 $\Delta$ 给出"圣"的量化判据与抗扰边界；
6. **长愿灯**把"愿"落到软最大化与 KL 小步，说明"延长时间窗"如何实降方差；
7. **清账符**用 $-\Delta \phi=\sigma$ 与 $\mathcal H^{-1}$ 范数刻画"最小补偿"，并以 I-投影恢复复路；
8. **共识印**把仪式的必要性落实为 $\nu_r\ge 2B$ 与共识谱隙的双重条件，使群体读数免于混叠与伪稳态。
