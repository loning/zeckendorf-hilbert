# Nature Communications 投稿修改文件说明

本目录包含针对Nature Communications投稿要求的修改文件和辅助文档。

## 📁 文件清单

### 主文件（已修改）
- **`main.tex`** - 主投稿文件，已完成以下关键修改：
  - ✅ 摘要重写（188词，无公式，无引用）
  - ✅ 标题优化（9词，更直白）
  - ✅ 新增 Author contributions
  - ✅ 修正 Data/Code availability声明
  - ✅ 修正 Competing interests声明

### 辅助文档（新创建）
1. **`MODIFICATION-SUMMARY.md`** ⭐ 【先读这个】
   - 完整修改总结
   - 已完成事项 vs 待办事项
   - 操作步骤与时间预估
   - 投稿前自检清单

2. **`SUBMISSION-CHECKLIST.md`**
   - 投稿前逐项检查表
   - 合规性自检（格式+政策）
   - 代码发布详细步骤
   - 备选期刊列表

3. **`cover-letter-template.txt`**
   - 投稿信模板（8点核心贡献）
   - 学术意义论述
   - 建议审稿人模板

4. **`INTRODUCTION-ENHANCEMENT-SUGGESTIONS.md`**
   - 引言优化建议（可选但强烈推荐）
   - "Core Problems Addressed"段落（可直接复制到main.tex）
   - 定量对比表格LaTeX代码
   - "大白话导引"段落示例

5. **`README-MODIFICATIONS.md`** （本文件）
   - 文件导航与使用说明

## 🚀 快速开始

### 如果你只有30分钟
1. 阅读 `MODIFICATION-SUMMARY.md` 前半部分（已完成的修改）
2. 检查 `main.tex` 编译是否正常
3. 记下"关键待办"：需要发布代码仓库

### 如果你有2-4小时
1. 完成代码仓库发布（GitHub + Zenodo）
2. 更新 `main.tex` 第1354行的占位符链接
3. 使用 `cover-letter-template.txt` 准备投稿信
4. 完成 `SUBMISSION-CHECKLIST.md` 的自检

### 如果你有1-2天
1. 完成上述所有步骤
2. 实施 `INTRODUCTION-ENHANCEMENT-SUGGESTIONS.md` 中的建议
   - 插入"Core Problems"段落
   - 制作定量对比表
3. 压缩主文（移RPG隐喻等至SI）
4. 最终校对

## ⚠️ 关键待办（投稿前必须完成）

### 代码仓库发布
**当前状态**：`main.tex` 使用占位符  
**必须操作**：
```bash
# 1. 创建GitHub仓库（公开）
# 2. 上传实验脚本（T4/T5/T17验证代码）
# 3. Zenodo归档获取DOI
# 4. 更新main.tex第1354行
```

**不完成后果**：❌ 不符合NC政策，直接拒稿

详细步骤见 `MODIFICATION-SUMMARY.md` 第II部分。

## 📋 主要修改对照表

| 修改项 | 原状态 | 现状态 | 位置 |
|--------|--------|--------|------|
| 摘要 | 400词+公式 | 188词纯文本 | main.tex:79-81 |
| 标题 | EBOC: Eternal-Block... | Static-Block Cellular Automata... | main.tex:65 |
| Author contributions | ❌ 缺失 | ✅ 已添加 | main.tex:1347-1348 |
| Code availability | "upon request" | GitHub+Zenodo链接 | main.tex:1353-1354 |
| Competing interests | "author" | "All authors" | main.tex:1356-1357 |

## 🎯 投稿时间线建议

```
Day 0（今天）：
├─ ✅ 核心修改已完成（AI已处理）
└─ ⚠️ 启动代码仓库整理

Day 1-2：
├─ 代码上传GitHub
├─ Zenodo归档
└─ 更新main.tex链接

Day 3-4（可选优化）：
├─ 引言增强
├─ 正文压缩
└─ Cover letter定制

Day 5（提交日）：
├─ 最终编译检查
├─ 上传NC系统
└─ 元数据填写
```

## 📚 推荐阅读顺序

```
第1步：MODIFICATION-SUMMARY.md（全面了解）
  ↓
第2步：SUBMISSION-CHECKLIST.md（逐项确认）
  ↓
第3步：实施代码发布（关键待办）
  ↓
第4步（可选）：INTRODUCTION-ENHANCEMENT-SUGGESTIONS.md（提升竞争力）
  ↓
第5步：cover-letter-template.txt（准备投稿信）
```

## 🔗 相关资源

- **Nature Communications投稿指南**：https://www.nature.com/ncomms/submit
- **Zenodo使用教程**：https://zenodo.org/
- **GitHub公开仓库设置**：Settings → Manage access → Set to Public

## ❓ 常见问题

**Q: 是否必须使用sn-jnl模板？**  
A: 不是硬性要求，但当前模板兼容NC。如果编辑要求改用标准类，可联系获取article.cls移植版。

**Q: Zenodo DOI需要多久生成？**  
A: 创建GitHub release后即时生成（<5分钟），但首次配置Zenodo-GitHub连接需10-15分钟。

**Q: 引言增强是否必须？**  
A: 非强制，但强烈建议。当前形式已达最低标准，引言增强可显著提升初筛通过率。

**Q: 正文是否太长？**  
A: 当前约11000词（含Methods），建议压缩至8000词左右（移部分内容至SI）。

## 📞 进一步支持

如需以下帮助，请在对话中提出：
- [ ] 将main.tex转为article.cls版本
- [ ] 生成补充材料LaTeX模板
- [ ] 制作GitHub仓库README模板
- [ ] 优化特定定理的证明表述

---

**修改完成日期**：2025-11-17  
**修改者**：AI Assistant  
**符合标准**：Nature Communications 投稿要求 v2025

**关键提醒**：当前修改已解决所有硬性合规问题（除代码发布需用户操作），可立即进入投稿准备阶段！

