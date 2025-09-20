# 附录：核心符号与定义

| 符号 | 类型 | 说明 | 引用位置 |
|------|------|------|----------|
| $k$ | 整数 | 观察者占用的行数（$k \ge 2$），对应递归算法数量 | 01-foundations/1.2, 02-observer-theory/2.1 |
| $r_k$ | 实数 | k-bonacci 特征根，满足 $r^k = r^{k-1} + \cdots + r + 1$，决定增长率与熵率 | 01-foundations/1.4 |
| $I_{\mathcal{O}}$ | 集合 | 观察者占据的行索引集合 | 02-observer-theory/2.1 |
| $s_t$ | 序列 | 时刻 $t$ 的实际激活行索引 | 01-foundations/1.2 |
| $P(t)$ | 序列 | 观察者对时刻 $t$ 激活位置的预测 | 02-observer-theory/2.1 |
| $p_i(t)$ | 概率 | 行 $i$ 在时刻 $t$ 被激活的概率，$\sum_i p_i(t)=1$ | 03-dynamics/3.4 |
| $w_{\mathcal{O}}(t)$ | 概率 | 观察者的激活权重，$\sum_{\mathcal{O}} w_{\mathcal{O}}(t)=1$ | 03-dynamics/3.2, 03-dynamics/3.4, 04-emergence/4.4 |
| $\mathcal{I}(t)$ | 信息量 | 加权信息强度，$\sum_{\mathcal{O}} w_{\mathcal{O}}(t) \log_2(r_{k_{\mathcal{O}}})$ | 01-foundations/1.7 |
| $\eta(t)$ | 归一化因子 | 保证“信息=计算=1”的归一化常数，$\eta(t)=1/\mathcal{I}(t)$ | 01-foundations/1.7 |
| $\tau_{\mathcal{O}}$ | 频率 | 观察者的主观时间速率，三类频率之和 | 04-emergence/4.1 |
| $f_{i}^{understood}$ | 频率 | 行 $i$ 被成功预测/理解的激活频率 | 04-emergence/4.1 |
| $f_{i}^{observed}$ | 频率 | 行 $i$ 激活但预测失败（仍处观察者行内）的频率 | 04-emergence/4.1 |
| $f_{i}^{unpredicted}$ | 频率 | 行 $i$ 激活且预测为 $\perp$ 的频率 | 04-emergence/4.1 |
| $\vec{h}_j$ | 向量 | 观察者的历史状态向量 $(s_{j-1},\ldots,s_{j-k})$ | 04-emergence/4.3 |
| $\vec{p}_j$ | 向量 | 预测向量 $(P(j-1),\ldots,P(j-k))$ | 04-emergence/4.3 |
| $L_{\text{direct}}$ | 整数 | 即时历史窗口长度，等于 $k$ | 04-emergence/4.3 |
| $n_{\text{active}}$ | 整数 | 当前仍在运行的调度层数（递推轮数） | 04-emergence/4.3 |
| $L_{\text{effective}}$ | 整数 | 可重构历史长度，$k + \alpha n_{\text{active}}$ | 04-emergence/4.3 |
| $\alpha$ | 实数 | 调度效率参数，$0 < \alpha \le 1$ | 04-emergence/4.3 |
| $\lambda_{\text{step}}$ | 实数 | 单步遗忘/退纠缠率，$\lambda_{\text{step}} = \frac{\log r_k}{k}$ | 04-emergence/4.3, 03-dynamics/3.3 |
| $C_{\text{local}}$ | 信息量 | 观察者局部可重构容量，$L_{\text{effective}} \log_2(r_k)$ | 04-emergence/4.3 |
| $\gamma$ | 实数 | 纠缠生成率 | 03-dynamics/3.3 |
| $p_{share}(t)$ | 概率 | 时刻 $t$ 的共享激活概率 | 03-dynamics/3.3 |
| $C(t)$ | 实数 | 纠缠度随时间的演化 | 03-dynamics/3.3 |
| $S_{red}$ | 信息量 | 子系统的约化 von Neumann 熵，量化纠缠强度 | 03-dynamics/3.3, 05-philosophical-unity/5.2 |

> 本表列出常用符号及其含义；补充定义请参考对应章节。
