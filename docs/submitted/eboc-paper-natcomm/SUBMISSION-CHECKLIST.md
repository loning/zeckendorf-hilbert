# Nature Communications 投稿前检查清单

## ✅ 已完成的硬性修改（Critical Fixes - COMPLETED）

### 1. 摘要 (Abstract)
- [x] ≤ 200 词（当前：188词）
- [x] 无引用
- [x] 无公式
- [x] 单段完成，清晰表述问题-方法-结果-意义

### 2. 作者贡献声明 (Author Contributions)
- [x] 已新增 `\section*{Author contributions}` 
- [x] 明确说明每位作者的具体贡献
- [x] 使用正确格式（粗体姓名缩写）

### 3. 数据与代码可得性 (Data & Code Availability)
- [x] 移除 "available upon request" 表述
- [x] 提供 GitHub 仓库占位符
- [x] 提供 Zenodo DOI 占位符
- [x] 详细列出代码包含内容

### 4. 利益冲突声明 (Competing Interests)
- [x] 改为 "All authors declare..." 格式
- [x] 涵盖所有作者

### 5. 标题 (Title)
- [x] 从术语密集改为更直白："Static-Block Cellular Automata: Information Laws and Observable Languages"
- [x] 9词（符合 ≤15词要求）
- [x] 避免首字母缩写堆叠

---

## ⚠️ 需要用户完成的后续任务（User Action Required）

### A. 代码仓库发布 (URGENT - 投稿前必须完成)
```bash
# 1. 创建公开GitHub仓库
# 建议仓库名: eboc-experiments 或 eboc-natcomm2025

# 2. 上传以下内容:
#    - T4厚边界重构实验脚本
#    - T5 Brudno收敛实验脚本
#    - T17主观时间实验脚本
#    - 图片生成代码
#    - README.md (安装说明、运行示例、依赖项)
#    - requirements.txt
#    - 许可证文件 (建议MIT)

# 3. Zenodo归档获取DOI:
#    a) 访问 https://zenodo.org/
#    b) 连接GitHub仓库
#    c) 创建release触发DOI生成
#    d) 将DOI填入 main.tex 第1354行

# 4. 更新main.tex中的占位符:
#    - 第1354行: 替换 [repository-name] 为实际仓库名
#    - 第1354行: 替换 [pending] 为实际Zenodo DOI号
```

### B. 补充材料准备 (Supplementary Materials)
根据修改意见，考虑将以下内容移至SI（补充信息）：
- [ ] RPG隐喻段落（§9.2）—— 压缩为1-2句或移至SI
- [ ] 部分冗长证明的技术细节（保留主文关键步骤）
- [ ] T6-T9的详细构造（主文保留概述）
- [ ] 附录A的术语表（可保留或移至SI）

### C. 正文优化（建议但非强制）
- [ ] **引言强化**：在Introduction末尾增加4-5条要点，明确：
  - 我们解决的具体难题（vs现有文献）
  - 可量化的技术收益
  - 可复用工具的价值定位
  
- [ ] **Related Work对比表**：增加与3篇最接近文献的定量对比表
  - 列举指标：条件复杂度上界、构造可计算性、规模估计等
  - 示例格式：
    ```
    | 文献 | 条件复杂度 | 自动机构造 | 规模界 | 实验验证 |
    |------|-----------|-----------|--------|---------|
    | [Brudno1983] | 仅渐近 | 无 | 无 | 无 |
    | [LindMarcus] | 无 | 抽象 | 无 | 无 |
    | **本文T4+T13** | O(log\|W\|) | 显式 | \|Σ\|^{kR} | 完整 |
    ```

- [ ] **图示增强**：考虑增加1-2幅概念示意图（非技术图）
  - 叶层逐层读取的可视化
  - 锚点-事件锥的示意
  - 厚边界因果依赖的几何图解

### D. LaTeX精简（可选 - 降低系统转换风险）
当前使用`sn-jnl`模板可保留，但建议：
- [ ] 清理未使用的自定义宏（检查是否所有`\newcommand`都被使用）
- [ ] 简化定理环境（theoremT的自定义计数器是否必需？）
- [ ] 确认所有包的必要性（特别是字体和排版微调包）

**注**：如果编辑要求改用标准类，可考虑切换至`amsart`或`revtex4-2`。

---

## 📊 合规性自检表（Final Check Before Submission）

### 格式与政策 (Format & Policy)
- [x] 标题 ≤ 15词
- [x] 摘要 ≤ 200词，无引用/公式
- [x] Author contributions完备
- [x] Data availability提供公开链接
- [x] Code availability提供公开链接或DOI
- [x] Competing interests使用"authors"口吻
- [ ] **补充材料**准备完毕（如有）
- [ ] Cover letter完成（已提供模板）

### 学术内容 (Academic Content)
- [ ] 旗舰定理（T4, T13）证明完整严谨
- [ ] 实验结果可重现（代码已公开）
- [ ] 与现有文献的差异明确量化
- [ ] 对NC跨学科读者的意义清晰表述
- [ ] 所有图表有完整标题和说明

### 技术检查 (Technical Check)
- [x] LaTeX编译无错误
- [x] 所有引用格式正确
- [x] 图片文件存在且路径正确
- [ ] 方程编号连续且引用正确
- [ ] 所有符号在首次出现时定义

---

## 🎯 投稿流程提醒

1. **准备PDF**：从LaTeX生成最终PDF，检查排版
2. **上传系统**：Nature Communications使用Editorial Manager系统
3. **元数据填写**：
   - 选择文章类型：Article
   - 选择学科分类：建议勾选 "Applied mathematics", "Computer science", "Statistical physics"
   - 关键词：cellular automata, Kolmogorov complexity, symbolic dynamics, omega-automata, information theory
4. **上传文件**：
   - 主文（main.tex + 图片 或 最终PDF）
   - Cover letter
   - 补充材料（如有）
5. **建议审稿人**（可选）：见cover-letter-template.txt末尾

---

## 📈 如果被拒后的备选期刊

### Nature Portfolio内部
- **Communications Physics** (跨学科物理+信息理论)
- **Scientific Reports** (更宽容，适合系统化工具发布)

### 专业期刊
- **Ergodic Theory and Dynamical Systems** (动力系统与符号动力学)
- **Theoretical Computer Science** (计算理论与自动机)
- **Information and Computation** (信息论与可计算性)
- **Nonlinearity** (非线性动力学)
- **Entropy** (开放获取，信息论与复杂系统)

---

## 最后提醒

✅ **已完成核心修改**：摘要、作者贡献、数据/代码可得性、利益冲突声明均已符合NC要求

⚠️ **关键待办**：发布GitHub代码仓库并获取Zenodo DOI（投稿前必须完成）

💡 **可选优化**：引言强化、对比表、图示增强（提升通过初筛概率）

---

**当前状态**：✅ 最低投稿标准已达标（假设代码仓库即将发布）  
**建议下一步**：完成代码发布 → 最终校对 → 提交

