# 12 时间域与可解模型:从边界数据重构时间

## 核心思想

在前面的章节中,我们构建了时间的理论框架:

- **时间被诠释为熵的最优路径**(第8节)
- **力可被视为时间几何的投影**(第9节)
- **时间结构可能由拓扑不变量决定**(第10节)
- **时间可能定义在边界上**(第11节)

现在我们面临最后一个关键问题:**在什么条件下,我们能在理论上从边界数据重构出时间?**

GLS理论提出:**定义域**(Domain)可能决定一切。就像数学函数需要定义域才有意义,时间刻度也需要明确的**定义域条件**才能从边界数据唯一确定。

---

## 日常类比:电影的放映

想象你要从胶片重构电影:

```mermaid
graph TB
    subgraph "问题:胶片上有什么信息?"
        Film["🎞️ 电影胶片<br/>(边界数据)"]

        Film -->|"每一帧"| Frame["静止图像"]
        Film -->|"帧间距"| Spacing["△t 时间间隔"]

        Frame -.->|"不足以"| Question["❓ 能重构出<br/>连续的电影吗?"]
        Spacing -.-> Question
    end

    subgraph "答案:需要定义域条件"
        Condition["✓ 定义域条件"]

        Condition --> C1["帧率已知<br/>(24 fps)"]
        Condition --> C2["播放顺序固定<br/>(因果性)"]
        Condition --> C3["没有缺失帧<br/>(完备性)"]

        C1 -.->|"满足"| Reconstruct["✓ 能唯一重构<br/>连续电影"]
        C2 -.-> Reconstruct
        C3 -.-> Reconstruct
    end

    style Film fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px
    style Frame fill:#4ecdc4,stroke:#0b7285
    style Spacing fill:#4ecdc4,stroke:#0b7285
    style Question fill:#e9ecef,stroke:#495057,stroke-dasharray: 5 5
    style Condition fill:#ffe66d,stroke:#f59f00,stroke-width:4px
    style C1 fill:#a9e34b,stroke:#5c940d
    style C2 fill:#a9e34b,stroke:#5c940d
    style C3 fill:#a9e34b,stroke:#5c940d
    style Reconstruct fill:#4ecdc4,stroke:#0b7285,stroke-width:4px
```

**理论洞察**:

- 胶片(边界数据)本身不够
- 需要**定义域条件**(帧率、顺序、完备性)
- 满足条件→理论上唯一重构电影(时间)

---

## 刻度同一式的定义域

回到第8节的核心公式,现在我们明确其**定义域**:

```mermaid
graph TB
    Identity["核心同一式:<br/>κ(ω) = φ'(ω)/π = ρ_rel(ω) = tr Q(ω)/2π"]

    Identity -->|"问"| Domain["在什么定义域成立?"]

    Domain --> D1["弹性-酉域<br/>(标准情况)"]
    Domain --> D2["非酉-吸收域<br/>(推广情况)"]
    Domain --> D3["长程势域<br/>(需要重整化)"]

    D1 -->|"精确条件"| C1["· S(ω)酉<br/>· 短程散射<br/>· 远离阈值/共振<br/>· trace类扰动"]

    D2 -->|"修正条件"| C2["· S非酉(吸收)<br/>· 使用 Q_gen = -iS⁻¹∂_ωS<br/>· Re tr Q_gen = 实延迟"]

    D3 -->|"重整化条件"| C3["· 库仑/引力势<br/>· Dollard修正波算子<br/>· 相位重整化 Φ_ren"]

    style Identity fill:#ff6b6b,stroke:#c92a2a,stroke-width:4px
    style Domain fill:#ffe66d,stroke:#f59f00,stroke-width:3px
    style D1 fill:#4ecdc4,stroke:#0b7285,stroke-width:3px
    style D2 fill:#4ecdc4,stroke:#0b7285
    style D3 fill:#4ecdc4,stroke:#0b7285
    style C1 fill:#a9e34b,stroke:#5c940d
    style C2 fill:#a9e34b,stroke:#5c940d
    style C3 fill:#a9e34b,stroke:#5c940d
```

### 域1:弹性-酉域(理想情况)

**定义域条件**:

$$
\begin{cases}
S(\omega) \in C^1(I; U(N)) & \text{(酉性)} \\
H - H_0 \in \mathfrak{S}_1 & \text{(trace类)} \\
\omega \in I \setminus \Sigma & \text{(远离阈值/共振)}
\end{cases}
$$

**同一式**:在此域内,刻度同一式**在数学上精确成立**:

$$
\frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\mathrm{tr}\,Q(\omega) \quad \text{(Lebesgue-a.e.)}
$$

---

### 域2:非酉-吸收域(推广情况)

想象一个**有损耗的微波腔**:

```mermaid
graph LR
    In["⚡ 入射波<br/>能量 E_in"]

    Cavity["📦 腔体<br/>(吸收能量)"]

    Out1["⚡ 透射波<br/>E_trans"]
    Out2["💨 吸收<br/>E_abs"]

    In --> Cavity
    Cavity --> Out1
    Cavity -.->|"散失"| Out2

    Conservation["能量守恒:<br/>E_in = E_trans + E_abs"]

    Out1 --> Conservation
    Out2 --> Conservation

    NonUnitary["S非酉:<br/>S†S ≠ 1"]

    Conservation --> NonUnitary

    style In fill:#4ecdc4,stroke:#0b7285
    style Cavity fill:#ffe66d,stroke:#f59f00,stroke-width:3px
    style Out1 fill:#a9e34b,stroke:#5c940d
    style Out2 fill:#ff6b6b,stroke:#c92a2a
    style Conservation fill:#e9ecef,stroke:#495057
    style NonUnitary fill:#fff,stroke:#868e96,stroke-width:3px
```

**修正定义**:

广义群延迟:
$$
Q_{\mathrm{gen}}(\omega) = -iS(\omega)^{-1}\partial_\omega S(\omega)
$$

相位关系:
$$
\partial_\omega \arg\det S = \Re\,\mathrm{tr}\,Q_{\mathrm{gen}}
$$

**物理意义**:

- $\Re\,\mathrm{tr}\,Q_{\mathrm{gen}}$ = 实际时间延迟
- $\Im\,\mathrm{tr}\,Q_{\mathrm{gen}}$ = 吸收率

小吸收极限:
$$
\mathrm{tr}\,Q_{\mathrm{gen}} = \mathrm{tr}\,Q + O(|S^\dagger S - 1|)
$$

---

### 域3:长程势域(重整化情况)

**问题**:库仑/引力势 $V \sim 1/r$

```mermaid
graph TB
    Problem["问题:长程势<br/>V(r) ~ 1/r"]

    Problem -->|"导致"| Issue1["相位发散<br/>φ ~ ln r"]
    Problem -->|"导致"| Issue2["波算子不收敛"]

    Solution["解决:相位重整化"]

    Issue1 --> Solution
    Issue2 --> Solution

    Solution --> S1["修正波算子<br/>(Dollard变换)"]
    Solution --> S2["定义重整化相位<br/>Φ_ren = Φ - Φ_Coulomb"]

    S1 -.->|"结果"| Result["重整化同一式:<br/>∂_ωΦ_ren = ρ_rel"]
    S2 -.-> Result

    style Problem fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px
    style Issue1 fill:#ffe66d,stroke:#f59f00
    style Issue2 fill:#ffe66d,stroke:#f59f00
    style Solution fill:#4ecdc4,stroke:#0b7285,stroke-width:4px
    style S1 fill:#a9e34b,stroke:#5c940d
    style S2 fill:#a9e34b,stroke:#5c940d
    style Result fill:#e9ecef,stroke:#495057,stroke-width:3px
```

---

## 窗口化时钟:解决负延迟问题

### 问题:群延迟可以为负

**异常延迟现象**:

```mermaid
graph TB
    Frequency["频率 ω"]

    Frequency -->|"共振附近"| Resonance["谐振峰"]
    Frequency -->|"反共振附近"| AntiRes["反谐振谷"]

    Resonance -->|"群延迟"| Pos["tr Q > 0<br/>正延迟"]
    AntiRes -->|"群延迟"| Neg["tr Q < 0<br/>负延迟!"]

    Neg -.->|"问题"| Question["时间倒流?"]

    style Frequency fill:#e9ecef,stroke:#495057
    style Resonance fill:#a9e34b,stroke:#5c940d
    style AntiRes fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px
    style Pos fill:#4ecdc4,stroke:#0b7285
    style Neg fill:#ffe66d,stroke:#f59f00,stroke-width:4px
    style Question fill:#fff,stroke:#868e96,stroke-dasharray: 5 5
```

**经典例子**:Hartman效应——量子隧穿中的超光速群速度

---

### 解决:Poisson窗口化

**思路**:不要在单个频率点定义时间,而是用**窗口平均**

```mermaid
graph TB
    Raw["原始群延迟 tr Q(ω)<br/>(可能有负值)"]

    Window["Poisson窗口 P_Δ(x)<br/>P_Δ(x) = (1/π) Δ/(x²+Δ²)"]

    Raw -->|"卷积"| Smooth["窗口化刻度密度<br/>Θ_Δ(ω) = (tr Q * P_Δ)(ω)"]

    Window --> Smooth

    Smooth -->|"积分"| Clock["窗口化时钟<br/>t_Δ(ω) = ∫ Θ_Δ dω"]

    Property["性质:<br/>Δ > 临界宽度 Γ_min<br/>⟹ Θ_Δ(ω) > 0<br/>⟹ t_Δ 严格递增"]

    Clock --> Property

    style Raw fill:#ff6b6b,stroke:#c92a2a
    style Window fill:#4ecdc4,stroke:#0b7285,stroke-width:3px
    style Smooth fill:#ffe66d,stroke:#f59f00
    style Clock fill:#a9e34b,stroke:#5c940d,stroke-width:4px
    style Property fill:#e9ecef,stroke:#495057
```

**数学定义**:

Poisson核:
$$
P_\Delta(x) = \frac{1}{\pi}\frac{\Delta}{x^2 + \Delta^2}
$$

窗口化刻度密度:
$$
\Theta_\Delta(\omega) = (\rho_{\mathrm{rel}} * P_\Delta)(\omega) = \frac{1}{2\pi}(\mathrm{tr}\,Q * P_\Delta)(\omega)
$$

窗口化时钟:
$$
t_\Delta(\omega) = \int_{\omega_0}^\omega \Theta_\Delta(\tilde{\omega})\,\mathrm{d}\tilde{\omega}
$$

**核心命题**:

若 $\Delta > \Gamma_{\min}$ (最小共振宽度),则:

1. **弱单调性**: $\Theta_\Delta(\omega) > 0$ 几乎处处
2. **仿射唯一性**: 任何满足条件的窗口化时钟都仅相差仿射变换 $\tilde{t}_\Delta = at_\Delta + b$

---

## 可解模型:Schwarzschild黑洞

### 问题:相位导数 = 几何时延?

在Schwarzschild黑洞外区,我们能验证**散射时间 = 几何时间**吗?

```mermaid
graph TB
    BH["⚫ Schwarzschild黑洞<br/>质量 M"]

    Wave["🌊 标量波<br/>频率 ω, 角动量 l"]

    BH -->|"散射"| Scatter["散射矩阵 S_l(ω)"]

    Scatter -->|"计算"| Phase["散射相位 Φ_l(ω)"]

    Phase -->|"导数"| Derivative["∂_ωΦ(ω) = ?"]

    Geometric["🌍 几何光学<br/>Shapiro延迟"]

    Geometric -->|"预言"| ShapiroDelay["ΔT_Shapiro ~ (4GM/c³)ln(r)"]

    Compare["对比"]

    Derivative --> Compare
    ShapiroDelay --> Compare

    Compare -.->|"高频极限"| Result["✓ ∂_ωΦ_ren = ΔT_Shapiro<br/>+ O(ω⁻¹)"]

    style BH fill:#ff6b6b,stroke:#c92a2a,stroke-width:4px
    style Wave fill:#4ecdc4,stroke:#0b7285
    style Scatter fill:#ffe66d,stroke:#f59f00
    style Phase fill:#a9e34b,stroke:#5c940d
    style Derivative fill:#e9ecef,stroke:#495057
    style Geometric fill:#4ecdc4,stroke:#0b7285
    style ShapiroDelay fill:#ffe66d,stroke:#f59f00
    style Compare fill:#fff,stroke:#868e96
    style Result fill:#a9e34b,stroke:#5c940d,stroke-width:4px
```

### Regge-Wheeler方程

Schwarzschild外区的标量波满足:

$$
\frac{\mathrm{d}^2 u}{\mathrm{d}r_*^2} + \left[\omega^2 - V_{\mathrm{eff}}(r)\right]u = 0
$$

其中:
- $r_* = r + 2M\ln(r/2M - 1)$ (tortoise坐标)
- $V_{\mathrm{eff}} = \left(1 - \frac{2M}{r}\right)\left(\frac{l(l+1)}{r^2} + \frac{2M}{r^3}\right)$ (有效势)

### Eikonal近似

高频/高角动量极限 $(ω \gg M^{-1}, l \gg 1)$:

WKB相位:
$$
\phi_{\mathrm{WKB}} = \int \sqrt{\omega^2 - V_{\mathrm{eff}}(r)}\,\mathrm{d}r_*
$$

相位导数:
$$
\partial_\omega\phi_{\mathrm{WKB}} = \int \frac{\omega}{\sqrt{\omega^2 - V_{\mathrm{eff}}}}\,\mathrm{d}r_*
$$

**几何对应**:

$$
\partial_\omega\phi_{\mathrm{WKB}} \approx \Delta T_{\mathrm{Shapiro}} = \frac{4GM}{c^3}\ln\frac{4r_E r_R}{b^2} + O(\omega^{-1})
$$

其中 $b$ 是冲击参数,$r_E, r_R$ 是发射/接收半径。

---

## 可解模型:引力透镜

### 多像时间延迟

```mermaid
graph LR
    Source["🌟 源<br/>t=0发光"]

    Lens["🌍 透镜<br/>(点质量M)"]

    Image1["📷 像1<br/>到达 t₁"]
    Image2["📷 像2<br/>到达 t₂"]

    Source -->|"光路1"| Lens
    Source -->|"光路2"| Lens

    Lens -->|"偏折"| Image1
    Lens -->|"偏折"| Image2

    Delay["时间延迟<br/>Δt = t₂ - t₁"]

    Image1 --> Delay
    Image2 --> Delay

    style Source fill:#ffe66d,stroke:#f59f00,stroke-width:3px
    style Lens fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px
    style Image1 fill:#4ecdc4,stroke:#0b7285
    style Image2 fill:#4ecdc4,stroke:#0b7285
    style Delay fill:#a9e34b,stroke:#5c940d,stroke-width:4px
```

**Fermat原理**: 光沿时间极值路径传播

时间延迟:
$$
\Delta t_{ij} = \frac{1+z_d}{c}\frac{D_d D_s}{D_{ds}}\left[\frac{(\boldsymbol{\theta}_i - \boldsymbol{\beta})^2}{2} - \psi(\boldsymbol{\theta}_i)\right] - \text{(像j)}
$$

其中:
- $\boldsymbol{\theta}_i$ = 像i的角位置
- $\boldsymbol{\beta}$ = 源的真实位置
- $\psi$ = 透镜势
- $D_{d,s,ds}$ = 角直径距离

**边界语言表述**:

频域放大因子 $F(\omega)$ 的相位:
$$
\partial_\omega[\Phi_i(\omega) - \Phi_j(\omega)] = \Delta t_{ij}
$$

时间延迟 = 相位差的频率导数(理论推论)!

---

## 可解模型:宇宙学红移

### 红移 = 相位节奏比

FRW宇宙中,光子相位:

$$
\phi = \int \omega\,\mathrm{d}t
$$

相位节奏:
$$
\frac{\mathrm{d}\phi}{\mathrm{d}t} = \omega = \omega_0 a(t_0)/a(t)
$$

红移:
$$
1 + z = \frac{\omega_e}{\omega_0} = \frac{(d\phi/dt)_e}{(d\phi/dt)_0} = \frac{a(t_0)}{a(t_e)}
$$

```mermaid
graph LR
    Emission["发射时刻 t_e<br/>尺度因子 a(t_e)"]

    Observation["观测时刻 t_0<br/>尺度因子 a(t_0)"]

    Emission -->|"光子传播"| Observation

    PhaseE["相位节奏<br/>(dφ/dt)_e"]
    PhaseO["相位节奏<br/>(dφ/dt)_0"]

    Emission --> PhaseE
    Observation --> PhaseO

    Redshift["红移<br/>1+z = (dφ/dt)_e/(dφ/dt)_0<br/>= a(t_0)/a(t_e)"]

    PhaseE --> Redshift
    PhaseO --> Redshift

    style Emission fill:#ff6b6b,stroke:#c92a2a
    style Observation fill:#4ecdc4,stroke:#0b7285
    style PhaseE fill:#ffe66d,stroke:#f59f00
    style PhaseO fill:#ffe66d,stroke:#f59f00
    style Redshift fill:#a9e34b,stroke:#5c940d,stroke-width:4px
```

**边界语言解读**:

- 宇宙学红移不是"多普勒效应"
- 而是**边界相位节奏的比值**
- 理论上完全由边界数据(相位演化)决定!

---

## 实验验证方案

### 方案1:多频Shapiro延迟测量

```mermaid
graph TB
    Sun["☀️ 太阳<br/>引力源"]

    Spacecraft["🛰️ 航天器<br/>信号发射"]

    Earth["🌍 地球<br/>接收站"]

    Sun -.->|"引力场"| Path["信号路径<br/>(经过太阳附近)"]

    Spacecraft -->|"多频信号<br/>ω₁, ω₂, ω₃..."| Path
    Path --> Earth

    Measure["测量相位 Φ(ω)"]

    Earth --> Measure

    Derivative["计算 ∂_ωΦ"]

    Measure --> Derivative

    Compare["对比:<br/>∂_ωΦ vs ΔT_Shapiro^(geo)"]

    Derivative --> Compare

    style Sun fill:#ffe66d,stroke:#f59f00,stroke-width:4px
    style Spacecraft fill:#4ecdc4,stroke:#0b7285
    style Earth fill:#a9e34b,stroke:#5c940d
    style Path fill:#ff6b6b,stroke:#c92a2a,stroke-dasharray: 5 5
    style Measure fill:#e9ecef,stroke:#495057
    style Derivative fill:#ffe66d,stroke:#f59f00
    style Compare fill:#fff,stroke:#868e96,stroke-width:3px
```

**关键**:

- 在多个频率测量相位 $\Phi(\omega)$
- 数值求导得到 $\partial_\omega\Phi$
- 与几何预言的Shapiro延迟对比
- 验证刻度同一式!

---

### 方案2:微波网络S参数测量

```mermaid
graph LR
    Network["📡 微波散射网络<br/>(多端口器件)"]

    VNA["矢量网络分析仪<br/>(VNA)"]

    Network -->|"扫频测量"| VNA

    VNA -->|"提取"| SMatrix["S矩阵 S(ω)"]

    SMatrix -->|"计算"| Q["Wigner-Smith矩阵<br/>Q = -iS†∂_ωS"]

    Q -->|"取迹"| Trace["tr Q(ω)"]

    Trace -->|"对比"| DOS["态密度 ρ_rel(ω)<br/>(从谱计算)"]

    Check["验证:<br/>tr Q/2π = ρ_rel"]

    Trace --> Check
    DOS --> Check

    style Network fill:#e9ecef,stroke:#495057
    style VNA fill:#4ecdc4,stroke:#0b7285
    style SMatrix fill:#ffe66d,stroke:#f59f00
    style Q fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px
    style Trace fill:#a9e34b,stroke:#5c940d
    style DOS fill:#a9e34b,stroke:#5c940d
    style Check fill:#fff,stroke:#868e96,stroke-width:3px
```

---

### 方案3:引力透镜时延宇宙学

```mermaid
graph TB
    QSO["类星体<br/>(时变源)"]

    Lens["前景星系<br/>(引力透镜)"]

    Images["多个像<br/>到达时间不同"]

    QSO -->|"光"| Lens
    Lens --> Images

    Measure["测量多频信号<br/>提取相位 Φ_i(ω)"]

    Images --> Measure

    Phase["计算相位差<br/>∂_ω[Φ_i - Φ_j]"]

    Measure --> Phase

    Delay["对比时间延迟<br/>Δt_ij (从光变曲线)"]

    Phase -.->|"应相等"| Delay

    Cosmology["宇宙学参数<br/>H₀, Ω_m..."]

    Delay --> Cosmology

    style QSO fill:#ffe66d,stroke:#f59f00,stroke-width:3px
    style Lens fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px
    style Images fill:#4ecdc4,stroke:#0b7285
    style Measure fill:#e9ecef,stroke:#495057
    style Phase fill:#a9e34b,stroke:#5c940d,stroke-width:3px
    style Delay fill:#a9e34b,stroke:#5c940d
    style Cosmology fill:#fff,stroke:#868e96,stroke-width:3px
```

**H0LiCOW项目**:利用透镜时延测量哈勃常数

---

## 定义域的哲学意义

```mermaid
graph TB
    Math["数学函数 f(x)"]

    Math --> Need1["需要定义域 D"]
    Math --> Need2["需要值域 R"]

    Need1 -.->|"类比"| Time["时间刻度 κ(ω)"]

    Time --> Domain["定义域条件"]
    Time --> Range["时间的值"]

    Domain --> D1["弹性-酉"]
    Domain --> D2["非酉-吸收"]
    Domain --> D3["长程势"]

    Range --> R1["窗口化时钟 t_Δ"]

    Insight["💡 深层启示"]

    D1 --> Insight
    D2 --> Insight
    D3 --> Insight
    R1 --> Insight

    Insight --> I1["时间不是绝对的<br/>取决于定义域"]
    Insight --> I2["不同域<br/>需要不同'语言'"]
    Insight --> I3["统一性在仿射等价类<br/>而非点态一致"]

    style Math fill:#e9ecef,stroke:#495057
    style Need1 fill:#ffe66d,stroke:#f59f00
    style Need2 fill:#ffe66d,stroke:#f59f00
    style Time fill:#ff6b6b,stroke:#c92a2a,stroke-width:4px
    style Domain fill:#4ecdc4,stroke:#0b7285,stroke-width:3px
    style Range fill:#a9e34b,stroke:#5c940d
    style D1 fill:#e9ecef,stroke:#495057
    style D2 fill:#e9ecef,stroke:#495057
    style D3 fill:#e9ecef,stroke:#495057
    style R1 fill:#e9ecef,stroke:#495057
    style Insight fill:#ffe66d,stroke:#f59f00,stroke-width:4px
    style I1 fill:#fff,stroke:#868e96
    style I2 fill:#fff,stroke:#868e96
    style I3 fill:#fff,stroke:#868e96
```

**深层启示**:

1. **时间像数学函数**:必须指定定义域才有意义
2. **不同物理情境 = 不同定义域**:弹性散射、吸收腔体、引力场各有其域
3. **统一性在等价类层面**:不同域的时间刻度通过仿射变换统一
4. **可解模型是桥梁**:连接抽象理论与具体实验

---

## 本章小结

**核心观点**:

> **GLS理论认为,时间刻度的重构需要明确的定义域条件。在弹性-酉域,刻度同一式精确成立;在非酉/长程域,需要修正或重整化。窗口化时钟解决负延迟问题,提供弱单调与仿射唯一性。可解模型(Schwarzschild、透镜、宇宙学)验证了散射时间=几何时间。**

**关键公式**:

刻度同一式(弹性-酉域):
$$
\frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\mathrm{tr}\,Q(\omega) \quad (\omega \in I \setminus \Sigma)
$$

窗口化时钟:
$$
\Theta_\Delta(\omega) = (\rho_{\mathrm{rel}} * P_\Delta)(\omega), \quad t_\Delta(\omega) = \int_{\omega_0}^\omega \Theta_\Delta\,\mathrm{d}\omega
$$

eikonal对应:
$$
\partial_\omega\Phi_{\mathrm{ren}}(\omega) = \Delta T_{\mathrm{Shapiro}} + O(\omega^{-1})
$$

红移-相位关系:
$$
1 + z = \frac{(d\phi/dt)_e}{(d\phi/dt)_0} = \frac{a(t_0)}{a(t_e)}
$$

**三大定义域**:

| 定义域 | 条件 | 刻度公式 |
|--------|------|----------|
| 弹性-酉 | $S$酉,短程,trace类 | 标准同一式 |
| 非酉-吸收 | $S$非酉,吸收 | $\Re\,\mathrm{tr}\,Q_{\mathrm{gen}}$ |
| 长程势 | 库仑/引力势 | $\partial_\omega\Phi_{\mathrm{ren}}$ |

**可解模型验证**:

1. **Schwarzschild**: $\partial_\omega\Phi \approx \Delta T_{\mathrm{Shapiro}}$ (高频极限)
2. **引力透镜**: $\partial_\omega(\Phi_i - \Phi_j) = \Delta t_{ij}$
3. **宇宙学**: $1+z = (d\phi/dt)_e / (d\phi/dt)_0$

**实验可验证**:

- 多频Shapiro延迟(行星掩日)
- 微波网络S参数(片上器件)
- 引力透镜时延(H0LiCOW)

**哲学意义**:

时间的重构不是自动的,而是**条件化的**:

- 必须指定定义域(物理情境)
- 必须选择窗口(测量分辨率)
- 统一性在仿射等价类,而非点态值

这构成了GLS统一时间理论的**重要一环**:从边界数据到时间重构的严格条件。

---

## 与其他章节的联系

```mermaid
graph TB
    Current["📍 本章:<br/>时间域与可解模型"]

    Prev1["← 08 时间作为熵<br/>最优路径"]
    Prev2["← 09 时间-几何统一<br/>无基本力"]
    Prev3["← 10 拓扑不变量<br/>时间的DNA"]
    Prev4["← 11 边界语言<br/>时间在哪说话"]

    Next1["→ 06 边界优先<br/>BTG完整框架"]
    Next2["→ 07 因果结构<br/>时间箭头"]

    Prev1 -->|"最优路径<br/>现在知道定义域"| Current
    Prev2 -->|"几何统一<br/>现在能可解验证"| Current
    Prev3 -->|"拓扑不变量<br/>现在有定义域约束"| Current
    Prev4 -->|"边界数据<br/>现在能重构时间"| Current

    Current -->|"定义域条件<br/>完整BTG假设"| Next1
    Current -->|"因果偏序<br/>从窗口化单调得出"| Next2

    Summary["✓ Phase 1完成<br/>05-unified-time章节<br/>8个文件完整"]

    Current --> Summary

    style Current fill:#ff6b6b,stroke:#c92a2a,stroke-width:4px
    style Prev1 fill:#4ecdc4,stroke:#0b7285
    style Prev2 fill:#4ecdc4,stroke:#0b7285
    style Prev3 fill:#4ecdc4,stroke:#0b7285
    style Prev4 fill:#4ecdc4,stroke:#0b7285
    style Next1 fill:#ffe66d,stroke:#f59f00
    style Next2 fill:#ffe66d,stroke:#f59f00
    style Summary fill:#a9e34b,stroke:#5c940d,stroke-width:4px
```

---

## 延伸阅读

**源理论文献**:
- `docs/euler-gls-paper-time/unified-time-scale-geometry-domains-solvable-models.md` - 时间刻度、定义域与可解模型的完整推导

**相关章节**:
- [03 散射相位与时间刻度](../02-scattering-time/03-scattering-phase-time-scale.md) - 散射理论基础
- [08 时间作为广义熵最优路径](./08-time-as-entropy.md) - 变分原理
- [09 时间–几何–相互作用统一](./09-time-geometry-interaction.md) - 几何实现
- [10 拓扑不变量与时间](./10-topological-invariants-time.md) - 拓扑约束
- [11 边界语言](./11-boundary-language.md) - 边界框架
- [06 边界优先与时间涌现](../06-boundary-theory/01-boundary-priority.md) - BTG完整理论

---

*至此,我们完成了统一时间理论的全部基础章节。下一步将探索边界理论、因果结构与矩阵宇宙的应用。*
