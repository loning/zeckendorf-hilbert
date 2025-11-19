# 物理基础：几何与信息

本书旨在建立基于离散信息本体的物理理论框架。

## 书籍结构

### 第一卷：离散本体论 —— 信息的物理基础

#### 第一编：有限信息公理与状态空间几何

##### 第一章：全息原理与有限性公理

- [1.1 贝肯斯坦界限（Bekenstein Bound）的严格推导与普朗克信息密度](volume01-discrete-ontology/part01-finite-information-axioms/chapter01-holographic-principle/01-01-bekenstein-bound.md)
- [1.2 有限信息公理：物理实在的希尔伯特空间维数有限性证明](volume01-discrete-ontology/part01-finite-information-axioms/chapter01-holographic-principle/01-02-finite-information-axiom.md)
- [1.3 连续统假设的失效：紫外发散的物理起源与自然截断](volume01-discrete-ontology/part01-finite-information-axioms/chapter01-holographic-principle/01-03-continuum-hypothesis-failure.md)
- [1.4 惠勒（Wheeler）的"It from Bit"与量子信息的本体论地位](volume01-discrete-ontology/part01-finite-information-axioms/chapter01-holographic-principle/01-04-wheeler-it-from-bit.md)

##### 第二章：参数化宇宙与信息几何

- [2.1 状态空间的黎曼结构：量子费希尔信息度量（QFIM）的构造](volume01-discrete-ontology/part01-finite-information-axioms/chapter02-parameterized-universe/02-01-riemannian-structure-qfim.md)
- [2.2 距离即由可区分性定义：Fubini-Study 度量的物理意义](volume01-discrete-ontology/part01-finite-information-axioms/chapter02-parameterized-universe/02-02-fubini-study-physical-meaning.md)
- [2.3 贝里曲率（Berry Curvature）与几何相位：规范场的几何起源](volume01-discrete-ontology/part01-finite-information-axioms/chapter02-parameterized-universe/02-03-berry-curvature-geometric-phase.md)
- [2.4 射影希尔伯特空间 $\mathbb{C}P^{N-1}$ 上的动力学流与辛几何结构](volume01-discrete-ontology/part01-finite-information-axioms/chapter02-parameterized-universe/02-04-dynamical-flow-symplectic-structure.md)

#### 第二编：离散动力学与因果结构

##### 第三章：量子元胞自动机 (QCA) 公理体系

- [3.1 六元组定义：离散背景 $\Lambda$、局域代数 $\mathcal{A}$ 与更新算符 $U$](volume01-discrete-ontology/part02-discrete-dynamics/chapter03-quantum-cellular-automata/03-01-qca-six-tuple-definition.md)
- [3.2 因果局域性定理：从有限传播半径推导严格光锥结构](volume01-discrete-ontology/part02-discrete-dynamics/chapter03-quantum-cellular-automata/03-02-causal-locality-theorem.md)
- [3.3 离散诺特（Noether）定理：对称性、守恒流与格点上的幺正性](volume01-discrete-ontology/part02-discrete-dynamics/chapter03-quantum-cellular-automata/03-03-discrete-noether-theorem.md)
- [3.4 计算普遍性：物理动力学与通用量子图灵机的范畴学等价性证明](volume01-discrete-ontology/part02-discrete-dynamics/chapter03-quantum-cellular-automata/03-04-computational-universality.md)

##### 第四章：从离散到连续的场论涌现

- [4.1 路径积分离散化：费曼核的格点求和表示与连续极限](volume01-discrete-ontology/part02-discrete-dynamics/chapter04-continuum-emergence/04-01-path-integral-discretization.md)
- [4.2 狄拉克方程的推导：量子行走（Quantum Walk）的长波极限与自旋的涌现](volume01-discrete-ontology/part02-discrete-dynamics/chapter04-continuum-emergence/04-02-dirac-equation-derivation.md)
- [4.3 规范场作为连接变量：格点上的威尔逊线（Wilson Line）与曲率](volume01-discrete-ontology/part02-discrete-dynamics/chapter04-continuum-emergence/04-03-gauge-fields-wilson-lines.md)
- [4.4 洛伦兹对称性的破缺与恢复：重整化群流（RG Flow）的不动点分析](volume01-discrete-ontology/part02-discrete-dynamics/chapter04-continuum-emergence/04-04-lorentz-symmetry-rg-flow.md)

#### 第三编：数学基础与误差控制

##### 第五章：离散-连续对偶的数学工具

- [5.1 物理采样定理：泊松求和公式在带限物理场中的应用](volume01-discrete-ontology/part03-mathematical-foundations/chapter05-discrete-continuous-duality/05-01-physical-sampling-theorem.md)
- [5.2 离散-连续误差控制 (DCEC)：欧拉-麦克劳林展开与边界项的精确控制](volume01-discrete-ontology/part03-mathematical-foundations/chapter05-discrete-continuous-duality/05-02-dcec-euler-maclaurin.md)
- [5.3 长球波函数 (PSWF)：有限观测窗口下的最优基底与信息截断](volume01-discrete-ontology/part03-mathematical-foundations/chapter05-discrete-continuous-duality/05-03-pswf-optimal-basis.md)
- [5.4 哥德尔不完备性在物理预测视界中的体现：不可判定性边界](volume01-discrete-ontology/part03-mathematical-foundations/chapter05-discrete-continuous-duality/05-04-godel-incompleteness-prediction-horizon.md)

## 目录结构

```
book-foundation-of-phys-in-geo-and-info/
├── index.md
└── volume01-discrete-ontology/
    ├── part01-finite-information-axioms/
    │   ├── chapter01-holographic-principle/
    │   │   ├── 01-01-bekenstein-bound.md
    │   │   ├── 01-02-finite-information-axiom.md
    │   │   ├── 01-03-continuum-hypothesis-failure.md
    │   │   └── 01-04-wheeler-it-from-bit.md
    │   └── chapter02-parameterized-universe/
    │       ├── 02-01-riemannian-structure-qfim.md
    │       ├── 02-02-fubini-study-physical-meaning.md
    │       ├── 02-03-berry-curvature-geometric-phase.md
    │       └── 02-04-dynamical-flow-symplectic-structure.md
    ├── part02-discrete-dynamics/
    │   ├── chapter03-quantum-cellular-automata/
    │   │   ├── 03-01-qca-six-tuple-definition.md
    │   │   ├── 03-02-causal-locality-theorem.md
    │   │   ├── 03-03-discrete-noether-theorem.md
    │   │   └── 03-04-computational-universality.md
    │   └── chapter04-continuum-emergence/
    │       ├── 04-01-path-integral-discretization.md
    │       ├── 04-02-dirac-equation-derivation.md
    │       ├── 04-03-gauge-fields-wilson-lines.md
    │       └── 04-04-lorentz-symmetry-rg-flow.md
    └── part03-mathematical-foundations/
        └── chapter05-discrete-continuous-duality/
            ├── 05-01-physical-sampling-theorem.md
            ├── 05-02-dcec-euler-maclaurin.md
            ├── 05-03-pswf-optimal-basis.md
            └── 05-04-godel-incompleteness-prediction-horizon.md
```

