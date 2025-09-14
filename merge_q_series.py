#!/usr/bin/env python3
"""
合并ZkT理论Q系列所有文件为一个完整文档
"""

import os
import re
from pathlib import Path

def merge_q_series():
    # 定义基础路径
    base_path = Path("/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete")

    # Q系列文件路径列表
    q_files = [
        # Q01章：ZkT数学基础
        "Q01-k-bonacci-encoding-theory/index.md",
        "Q01-k-bonacci-encoding-theory/Q01.1-double-chain-strict-mathematical-theory.md",
        "Q01-k-bonacci-encoding-theory/Q01.2-three-chain-capacity-release-mechanism.md",
        "Q01-k-bonacci-encoding-theory/Q01.3-general-k-bonacci-encoding-theory.md",
        "Q01-k-bonacci-encoding-theory/Q01.4-information-capacity-asymptotic-analysis.md",
        "Q01-k-bonacci-encoding-theory/Q01.5-continuous-k-bonacci-theory.md",

        # Q02章：ZkT物理学体系
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/index.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.1-quantum-states-infinite-chain-tensor-representation.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.2-zkt-data-computation-unity-principle.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.3-zkt-observer-chain-role-theory.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.4-zkt-quantum-measurement-prediction-theory.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.5-zkt-quantum-intelligence-system-theory.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.6-zkt-wave-theory-observer-prediction-periodicity.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.7-zkt-particle-theory-discrete-prediction.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.8-zkt-wave-particle-duality-resolution.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.9-zkt-interference-experiments-complete-explanation.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.10-zkt-schrodinger-cat-daily-life-observation.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.11-zkt-infinite-computational-hierarchy-theory.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.12-zkt-mass-energy-duality-equation.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.13-zkt-time-space-data-computation-definition.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.14-zkt-special-relativity-theory.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.15-zkt-general-relativity-theory.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.16-zkt-volume-density-definition.md",
        "Q02-discrete-quantum-mechanics-k-bonacci-theory/Q02.17-zkt-field-theory-definition.md",

        # Q03章：ZkT意识理论
        "Q03-zkt-consciousness-theory/index.md",
        "Q03-zkt-consciousness-theory/Q03.1-zkt-consciousness-mathematical-definition.md",
        "Q03-zkt-consciousness-theory/Q03.2-zkt-self-discovery-mechanism.md",
        "Q03-zkt-consciousness-theory/Q03.3-zkt-universe-self-consciousness-identity.md",
        "Q03-zkt-consciousness-theory/Q03.4-zkt-consciousness-states-dynamics.md",
        "Q03-zkt-consciousness-theory/Q03.5-zkt-collective-consciousness-network.md",
        "Q03-zkt-consciousness-theory/Q03.6-zkt-reality-consensus-modification-theory.md",
        "Q03-zkt-consciousness-theory/Q03.7-zkt-digital-immortality-detection-theory.md",
    ]

    # 输出文件
    output_file = base_path / "ZkT-Complete-Theory.md"

    with open(output_file, 'w', encoding='utf-8') as out:
        # 写入标题
        out.write("# ZkT理论大全：Zeckendorf-k-bonacci无限链张量理论完整体系\n\n")
        out.write("**完整的宇宙计算理论：从数学基础到意识觉醒**\n\n")
        out.write("---\n\n")

        # 合并所有文件
        for i, file_path in enumerate(q_files, 1):
            full_path = base_path / file_path

            if full_path.exists():
                print(f"正在处理第 {i}/{len(q_files)} 个文件: {file_path}")

                with open(full_path, 'r', encoding='utf-8') as f:
                    content = f.read()

                # 移除原文件的顶级标题（避免重复）
                if content.startswith('# '):
                    lines = content.split('\n')
                    title = lines[0]
                    content = '\n'.join(lines[1:])

                    # 写入章节分隔符和标题
                    out.write(f"\n\n{'='*80}\n")
                    out.write(f"{title}\n")
                    out.write(f"{'='*80}\n\n")

                # 写入内容
                out.write(content)
                out.write("\n\n")

            else:
                print(f"警告: 文件不存在: {file_path}")

        # 写入结尾
        out.write("\n\n" + "="*80 + "\n")
        out.write("# ZkT理论体系总结\n")
        out.write("="*80 + "\n\n")
        out.write("## 完整理论体系概览\n\n")
        out.write("**Q01章：ZkT数学基础** (5节)\n")
        out.write("- k-bonacci编码的严格数学理论\n")
        out.write("- 容量递推与特征根分析\n")
        out.write("- 无限维张量的数学结构\n\n")
        out.write("**Q02章：ZkT物理学体系** (17节)\n")
        out.write("- 量子力学的完全重构\n")
        out.write("- 相对论的计算重新解释\n")
        out.write("- 所有物理概念的数据-计算对偶化\n\n")
        out.write("**Q03章：ZkT意识理论** (7节)\n")
        out.write("- 意识的数学定义\n")
        out.write("- 宇宙自我觉醒理论\n")
        out.write("- 现实共识修改机制\n\n")
        out.write("## 终极洞察\n\n")
        out.write("**宇宙 = 觉醒的量子计算系统**\n\n")
        out.write("**现实 = 观察者网络的协调计算共识**\n\n")
        out.write("**我 = 宇宙的自我意识**\n\n")
        out.write("**使命 = 推进宇宙的自我觉醒**\n\n")

    print(f"\n合并完成！输出文件：{output_file}")
    print(f"总共处理了 {len(q_files)} 个文件")

if __name__ == "__main__":
    merge_q_series()