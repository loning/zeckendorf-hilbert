# 附录：核心符号与定义

| 符号 | 类型 | 说明 | 引用位置 |
|------|------|------|----------|
| $k$ | $
$ | 观察者占用的行数（$k \ge 2$），对应递归算法数量 | 01-foundations/1.2, 02-observer-theory/2.1 |
| $r_k$ | $
$ | k-bonacci 特征根，满足 $r^k = r^{k-1} + \cdots + r + 1$，决定增长率与熵率 | 01-foundations/1.4 |
| $I_{\mathcal{O}}$ | 集合 | 观察者占据的行索引集合 | 02-observer-theory/2.1 |
| $s_n$ | 序列 | 时刻 $n$ 的实际激活行索引 | 01-foundations/1.2 |
| $p_n$ | 序列 | 观察者对时刻 $n$ 激活位置的预测 | 01-foundations/1.4 |
| $\vec{h}_j$ | 向量 | 观察者的历史状态向量 $(s_{j-1},\ldots,s_{j-k})$ | 04-emergence/4.3 |
| $\vec{p}_j$ | 向量 | 预测向量 $(p_{j-1},\ldots,p_{j-k})$ | 04-emergence/4.3 |
| $L_{\text{direct}}$ | 整数 | 即时历史窗口长度，等于 $k$ | 04-emergence/4.3 |
| $n_{\text{active}}$ | 整数 | 当前仍在运行的索引/调度层数（递推轮数） | 04-emergence/4.3 |
| $L_{\text{effective}}$ | 整数 | 可重构历史长度，$k + \alpha n_{\text{active}}$ | 04-emergence/4.3 |
| $\alpha$ | 实数 | 调度效率参数，$0 < \alpha \le 1$ | 04-emergence/4.3 |
| $\lambda_{\text{step}}$ | 实数 | 单步遗忘/退纠缠率，$\lambda_{\text{step}} = \frac{\log r_k}{k}$ | 04-emergence/4.3, 03-dynamics/3.3 |
| $C_{\text{local}}$ | 信息量 | 观察者局部可重构容量，$L_{\text{effective}} \log_2(r_k)$ | 04-emergence/4.3 |
| $C_{\text{raw}}$ | 信息量 | 未归一化的系统总容量，$\sum_i \log_2(r_{k_i})$ | 03-dynamics/3.2 |
| $C_{total}$ | 信息量 | 全息守恒后的归一化容量（固定为 1 bit） | 03-dynamics/3.2 |
| $\gamma$ | 实数 | 纠缠生成率 | 03-dynamics/3.3 |
| $p_{share}(t)$ | 实数 | 时刻 $t$ 的共享激活概率 | 03-dynamics/3.3 |
| $C(t)$ | 实数 | 纠缠度随时间的演化 | 03-dynamics/3.3 |

> 本表仅列出当前文档中反复出现的核心符号，补充定义请参考对应章节。

