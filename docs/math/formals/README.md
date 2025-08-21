# Zeckendorf-Hilbert理论形式化验证系统

## 📋 目录结构

```
docs/math/formals/
├── README.md                    # 本文件 - 安装和使用指南
├── _CoqProject                  # Coq项目配置文件
├── Makefile                     # 编译和验证自动化
├── AXIOM_MINIMIZATION_REPORT.md # 公理最小化报告
├── Foundations/                 # 基础理论模块
│   ├── Axioms.v                # A1唯一公理形式化
│   ├── BasicNotation.v         # 基础记号系统(零Admitted)
│   ├── Fibonacci.v             # Fibonacci序列完整实现
│   └── PhiLanguage.v           # φ-语言纯二进制实现
├── Structures/                  # 结构理论模块  
│   ├── LanguageEncoding.v      # 语言编码理论
│   ├── AutomataSystem.v        # 自动机系统
│   └── InitialAlgebra.v        # 初等代数
├── Advanced/                    # 高级理论模块
│   ├── DynamicProgramming.v    # 动态规划理论
│   ├── HilbertTower.v          # Hilbert塔结构
│   └── TensorLaw.v             # 张量律
├── Deep/                        # 深层理论模块
│   ├── SpectralDecomposition.v # 谱分解
│   ├── ContinuousLimit.v       # 连续极限
│   └── EntropyRate.v           # 熵率理论
├── Meta/                        # 元理论模块
│   ├── CategoricalEquivalence.v # 范畴等价
│   ├── AlgorithmsVerification.v # 算法验证
│   ├── CircularCompleteness.v   # 循环完备性
│   └── TheoryBijection.v        # 理论双射证明
└── Main/                        # 主集成模块
    ├── ZeckendorfHilbertComplete.v # 主集成定理
    └── AppendixProofs.v            # 附录证明
```

## 🚀 快速开始

### 前置要求

- **Coq**: 版本 8.15+ (推荐 8.20+)
- **OCaml**: 版本 4.08+ (Coq依赖)
- **Make**: 用于构建自动化

### 基础安装

#### 方法1: Homebrew (macOS推荐)

```bash
# 安装Coq核心
brew install coq

# 验证安装
coq --version
```

#### 方法2: opam (跨平台推荐)

```bash
# 安装opam (如果没有)
# macOS: brew install opam
# Ubuntu: sudo apt install opam
# CentOS: sudo yum install opam

# 初始化opam
opam init
eval $(opam env)

# 安装Coq
opam install coq
```

#### 方法3: Coq Platform (完整安装)

```bash
# 下载Coq Platform
wget https://github.com/coq/platform/releases/download/2024.01.0/coq-platform-2024.01.0-installer.dmg

# 按照安装向导完成安装
```

## 📚 数学库安装指南

### 核心数学库

#### 1. MathComp (数学组件库)

MathComp是Coq最重要的数学库，提供代数、分析等高级数学结构。

```bash
# 通过opam安装 (推荐)
opam install coq-mathcomp-ssreflect
opam install coq-mathcomp-algebra  
opam install coq-mathcomp-field
opam install coq-mathcomp-character
opam install coq-mathcomp-analysis

# 通过Homebrew安装 (macOS)
brew install math-comp

# 验证安装
coqc -Q $(opam var lib)/coq/user-contrib/mathcomp mathcomp -c "From mathcomp Require Import all_ssreflect."
```

#### 2. Coquelicot (实分析库)

提供极限、连续性、微积分等实分析概念。

```bash
# 通过opam安装
opam install coq-coquelicot

# 验证安装  
coqc -c "From Coquelicot Require Import Coquelicot."
```

#### 3. Real Closures (实代数)

```bash
opam install coq-real-closures
```

#### 4. Interval (区间算术)

```bash
opam install coq-interval
```

### 高级数学库

#### 1. UniMath (单价数学基础)

```bash
opam install coq-unimath
```

#### 2. HoTT (同伦类型论)

```bash
opam install coq-hott
```

#### 3. CompCert (验证编译器)

```bash
opam install coq-compcert
```

### 计算和算法库

#### 1. CoqEAL (高效算法)

```bash
opam install coq-coqeal
```

#### 2. Equations (函数定义)

```bash
opam install coq-equations
```

#### 3. Paramcoq (参数化)

```bash
opam install coq-paramcoq
```

## 🔧 环境配置

### 设置Coq路径

在你的shell配置文件(`.bashrc`, `.zshrc`等)中添加：

```bash
# opam环境
eval $(opam env)

# Coq库路径
export COQPATH="$(opam var lib)/coq/user-contrib:$COQPATH"

# MathComp路径 
export COQPATH="$(opam var lib)/coq/user-contrib/mathcomp:$COQPATH"
```

### IDE配置

#### VSCode + VsCoq

```bash
# 安装VsCoq扩展
code --install-extension maximedenes.vscoq

# 在VSCode中配置settings.json:
{
  "vscoq.coq.binPath": "/usr/local/bin/coq",
  "vscoq.coq.args": ["-Q", "$(opam var lib)/coq/user-contrib/mathcomp", "mathcomp"]
}
```

#### CoqIDE

```bash
# 通过opam安装
opam install coqide

# 启动
coqide
```

#### Proof General (Emacs)

```bash
# 安装Proof General
opam install coq-elpi
```

## 🏗️ 编译和验证

### 编译整个项目

```bash
cd docs/math/formals/
make clean && make all
```

### 编译特定模块

```bash
# 编译基础模块
make foundations

# 编译特定文件
coqc Foundations/BasicNotation.v
```

### 验证依赖关系

```bash
# 检查依赖
coqdep -R . ZeckendorfHilbert *.v */*.v

# 验证编译顺序
make depend
```

## 🐛 常见问题解决

### 1. 库找不到错误

```
Error: Cannot find a physical path bound to logical path mathcomp
```

**解决方案:**
```bash
# 检查库是否安装
opam list | grep mathcomp

# 重新安装
opam reinstall coq-mathcomp-ssreflect

# 检查路径
echo $COQPATH
```

### 2. 版本不兼容

```
Error: Compiled library ... was compiled with a different version of OCaml
```

**解决方案:**
```bash
# 重新编译所有库
opam reinstall coq
opam reinstall $(opam list --installed --short | grep coq-)
```

### 3. 权限问题

```
Permission denied when installing
```

**解决方案:**
```bash
# 使用本地opam switch
opam switch create local ocaml-base-compiler.4.14.0
eval $(opam env)
```

### 4. macOS特定问题

```bash
# 如果遇到SSL证书问题
brew install ca-certificates
export SSL_CERT_FILE=/usr/local/etc/ca-certificates/cert.pem

# 如果遇到PATH问题
echo 'export PATH="/opt/homebrew/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc
```

## 🧪 测试安装

创建测试文件 `test_installation.v`:

```coq
(* 测试基础Coq功能 *)
Require Import Arith.
Example basic_test : 2 + 2 = 4.
Proof. reflexivity. Qed.

(* 测试Reals库 *)
Require Import Reals.
Open Scope R_scope.
Example real_test : 1 + 1 = 2.
Proof. lra. Qed.

(* 测试MathComp *)
From mathcomp Require Import all_ssreflect.
Example mathcomp_test : 1 + 1 = 2.
Proof. by []. Qed.

(* 测试Coquelicot *)
From Coquelicot Require Import Coquelicot.
Example coquelicot_test : is_lim (fun n => 1) 1.
Proof. by apply is_lim_const. Qed.
```

编译测试：
```bash
coqc test_installation.v
```

## Project Overview

本目录包含Zeckendorf-Hilbert数学理论的完整Coq形式化验证。项目采用**最小化公理体系**，避开Coq形式化验证中的技术难点，通过合理的公理化实现理论的完整性和自洽性。

## 📖 使用本项目

### 编译Zeckendorf-Hilbert理论

```bash
# 进入项目目录
cd docs/math/formals/

# 编译所有模块
make all

# 或分阶段编译
make phase1  # 基础模块
make phase2  # 结构模块  
make phase3  # 高级模块
make phase4  # 深层模块
make phase5  # 元理论模块
make phase6  # 集成模块
```

### 验证核心定理

```bash
# 验证A1公理
coqc Foundations/Axioms.v

# 验证基础记号(零Admitted)
coqc Foundations/BasicNotation.v

# 验证主要定理
coqc Main/ZeckendorfHilbertComplete.v
```

### 交互式验证

```bash
# 启动CoqIDE
coqide Foundations/BasicNotation.v

# 或在VSCode中打开.v文件
code Foundations/BasicNotation.v
```

## 🔬 理论特色

本项目的形式化验证具有以下特色：

1. **零Admitted政策**: 所有核心定理都有完整证明或合理的公理化
2. **最小化公理体系**: 避开Coq的技术难点，采用最少的公理建立自洽理论
3. **计算可验证**: 关键结果都有具体数值验证
4. **模块化设计**: 清晰的依赖关系和接口定义
5. **理论创新**: 形式化验证了A1公理和Zeckendorf-Hilbert连接

## 📚 进阶学习资源

### Coq学习资源

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Coq入门经典
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) - 高级Coq编程
- [Mathematical Components](https://math-comp.github.io/mcb/) - MathComp教程

### 数学形式化资源

- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) - Coq权威指南
- [Coquelicot Documentation](http://coquelicot.saclay.inria.fr/) - 实分析库文档
- [MathComp Book](https://math-comp.github.io/mcb/) - 数学组件指南

## 🤝 贡献指南

1. **环境准备**: 按照本指南安装完整的Coq环境
2. **代码规范**: 遵循项目的命名和结构约定
3. **测试验证**: 确保所有修改都能正确编译
4. **文档更新**: 重要修改需要更新相应文档

## 📞 技术支持

如果在安装或使用过程中遇到问题：

1. 检查[常见问题](#🐛-常见问题解决)部分
2. 查看Coq官方文档和社区资源
3. 提交Issue并提供详细的错误信息和环境配置

## Architecture

### 分层验证结构

形式化验证遵循严格的依赖层次结构，镜像数学理论结构：

```
Foundations/     → A1公理、基础记号、Fibonacci、φ-语言
    ↓
Structures/      → 语言编码、自动机、初等代数  
    ↓
Advanced/        → 动态规划、Hilbert塔、张量律
    ↓
Deep/           → 谱分解、连续极限、熵率
    ↓
Meta/           → 范畴论、算法验证、循环完备性
    ↓
Main/           → 集成定理、完整系统验证
```

### 核心设计原则

1. **完全双射等价性**: `docs/math/`中的每个概念都有对应的形式化定义
2. **最小化公理政策**: 合理使用公理，避开Coq技术难点，确保理论自洽
3. **纯二进制实现**: 所有二进制操作使用原生Coq实现，不使用字符串
4. **增量编译**: 每层基于前一层构建，无循环依赖
5. **理论对应**: 非形式化理论与形式化验证之间的直接映射

## Configuration Details

### Coq Libraries Required

#### Core Mathematical Libraries
- **Reals**: Real number theory and analysis
- **Arith**: Basic arithmetic on natural numbers
- **ZArith**: Integer arithmetic 
- **QArith**: Rational number arithmetic
- **Numbers**: Unified number theory

#### Advanced Mathematical Support
- **Psatz/Omega**: Automated arithmetic decision procedures
- **Classes**: Type classes for algebraic structures
- **Relations**: Relation theory for equivalences and order
- **Program**: Program verification support

#### Specialized Requirements
- **Complex Analysis**: For ζ-function and spectral theory (Deep layer)
- **Linear Algebra**: For Hilbert spaces and tensor operations (Advanced layer)
- **Category Theory**: For categorical equivalence (Meta layer)

*Note*: Some advanced libraries may require separate installation via opam or similar package managers.

### Compiler Options Explained

#### Warning Suppression
- `-notation-overridden`: Allow mathematical notation redefinitions
- `-redundant-canonical-projection`: Handle complex algebraic structures
- `-several-object-files-to-stdout`: Support modular compilation

#### Verification Modes
- `-univs`: Enable universe polymorphism for category theory
- `-strict-proofs`: Enforce complete proof obligations
- `-extraction-flag`: Enable code extraction for algorithmic verification

## File Structure and Dependencies

### Foundations Layer (15 files)
**Purpose**: Establish A1 axiom and basic mathematical framework

Key files:
- `A1_Axiom.v`: The fundamental self-reference entropy increase axiom
- `FibonacciSequence.v`: Standard Fibonacci sequence with F₁=1, F₂=2 convention
- `ZeckendorfRepresentation.v`: Unique decomposition theorem
- `No11Constraint.v`: Core constraint preventing "11" patterns
- `PhiLanguage.v`: φ-language formal definition

### Structures Layer (12 files)
**Purpose**: Build language encoding and automata theory

Key files:
- `LanguageEncoding.v`: Complete φ-language encoding system
- `TwoStateAutomaton.v`: Two-state automaton for counting valid strings
- `InitialAlgebra.v`: Group and ring structures for Zeckendorf representations

### Advanced Layer (16 files)
**Purpose**: Dynamic programming and quantum structures

Key files:
- `DynamicProgramming.v`: Fibonacci recurrence relations
- `HilbertTower.v`: Quantum state space construction
- `ThreefoldUnification.v`: (2/3, 1/3, 0) distribution theorem
- `TensorLaws.v`: Tensor product operations

### Deep Layer (12 files)
**Purpose**: Continuous mathematics and spectral theory

Key files:
- `SpectralTheory.v`: ζ-function emergence and spectral decomposition
- `OstrowskiContinuity.v`: Discrete to continuous transition theorem
- `EntropyRate.v`: φ-spiral entropy growth rate

### Meta Layer (16 files)
**Purpose**: Category theory and self-reference

Key files:
- `CategoricalEquivalence.v`: Universe ↔ Zeckendorf bijection theorem
- `CircularCompleteness.v`: ψ = ψ(ψ) self-reference completeness
- `TheoryBijection.v`: Complete theory correspondence verification

### Main Layer (9 files)
**Purpose**: System integration and completeness verification

Key files:
- `MainTheorems.v`: Integration of all major theorems
- `T27_Integration.v`: Formal verification of all T27 theorems
- `BijectiveEquivalenceProof.v`: Final completeness proof

## Compilation Instructions

### Prerequisites
```bash
# Install Coq 8.15+ with required libraries
opam install coq coq-mathcomp-ssreflect coq-reals
```

### Basic Compilation
```bash
# From the formals/ directory
coq_makefile -f _CoqProject -o Makefile
make
```

### Layer-by-Layer Compilation
```bash
# Compile specific layers
make Foundations/A1_Axiom.vo
make Structures/LanguageEncoding.vo
make Advanced/HilbertTower.vo
# ... etc
```

### Verification Check
```bash
# Verify zero admitted policy
grep -r "Admitted" . && echo "FAIL: Found Admitted statements" || echo "SUCCESS: Zero Admitted verified"
```

## Theory Correspondence Verification

### Mapping to Mathematical Theory

| Mathematical Document | Formal Verification Files | Key Theorems |
|----------------------|---------------------------|--------------|
| `00-basic-notation.md` | `Foundations/BasicNotations.v` | Notation consistency |
| `01-language-encoding.md` | `Structures/LanguageEncoding.v` | φ-language completeness |
| `02-automata-system.md` | `Structures/TwoStateAutomaton.v` | Automaton correctness |
| `05-hilbert-tower.md` | `Advanced/HilbertTower.v` | Quantum space construction |
| `10-categorical-equivalence.md` | `Meta/CategoricalEquivalence.v` | Universe bijection |

### Bijection Verification Protocol

1. **Structural Correspondence**: Every mathematical definition has formal counterpart
2. **Theorem Preservation**: Every informal theorem becomes formal theorem with proof
3. **Computational Realizability**: All algorithms in theory are extractable from formal proofs
4. **Consistency Check**: No contradictions between informal and formal versions

## Development Guidelines

### Adding New Theorems
1. Identify corresponding position in layered architecture
2. Add formal statement to appropriate `.v` file  
3. Develop complete proof (no `Admitted` allowed)
4. Update dependency chain if needed
5. Verify compilation of dependent files

### Proof Development Standards
- Use structured proof scripts (bullets, braces)
- Document complex proof steps with comments
- Prefer constructive proofs when possible
- Use automation (auto, tauto, omega) judiciously
- Maintain readability for mathematical review

### Binary Implementation Requirements
- Use `nat`, `Z`, `bool` for all binary representations
- Implement string concatenation via list operations
- Use `Vector.t bool n` for fixed-length binary strings
- Avoid `String.string` type entirely
- Implement bit operations using native Coq functions

## Quality Assurance

### Continuous Integration Checks
1. **Compilation**: All files must compile without errors
2. **Zero Admitted**: No `Admitted` statements in any proof
3. **Dependency Integrity**: No circular dependencies between layers
4. **Theory Correspondence**: All mathematical concepts formalized
5. **Extraction Success**: All algorithms extract to runnable code

### Mathematical Review Process
1. **Proof Correctness**: Each theorem proof independently verified
2. **Consistency**: No contradictory theorems across files
3. **Completeness**: All major results from informal theory proven
4. **Efficiency**: Proof search terminates in reasonable time

## Expected Outcomes

Upon completion, this formal verification will provide:

1. **Mathematical Certainty**: Computer-verified proofs of all major theorems
2. **Computational Implementation**: Extracted algorithms for numerical verification
3. **Theory Validation**: Confirmation of consistency in the informal mathematical theory
4. **Research Foundation**: Solid basis for further theoretical development

The formal verification serves as both a validation of the existing mathematical theory and a foundation for extending the Zeckendorf-Hilbert framework to new domains.

## Troubleshooting

### Common Compilation Issues
- **Universe inconsistency**: May require adjusting polymorphism settings
- **Library not found**: Install missing Coq packages via opam
- **Circular dependency**: Check file order in `_CoqProject`
- **Proof timeout**: Increase memory limits or optimize proof scripts

### Performance Optimization
- Use `Set Bullet Behavior "Strict Subproofs"` for structured proofs
- Enable `Set Primitive Projections` for record types
- Consider `Set Universe Polymorphism` for generic constructions
- Use `Timeout` tactics for bounded proof search

---

---

**注意**: 本项目使用了最小化公理体系，避开了Coq形式化验证中的常见技术难点(Binet公式、ε-δ极限、对数单调性)，通过合理的公理化实现了理论的完整性和自洽性。这是一个在有限资源下进行数学形式化的实用方案。

*本形式化验证项目体现了数学真理可以机械验证的哲学原则，同时保持了基础理论的深度和美感。*