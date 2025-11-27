# 🚀 Zenodo 自动翻译上传工作流

## 📋 快速使用

将文件夹拖入 Cursor，并说：

```
@[你的文件夹] @tools

请处理此文件夹：翻译 MD 为英文 LaTeX，编译 PDF，并按规定格式上传到 Zenodo。
```

## 🎯 工作流程

### 1️⃣ AI 翻译 (MD → LaTeX)
AI 将读取中文 Markdown，使用 `tools/latex_template.tex` 模板翻译为英文 LaTeX (`_en.tex`)。
- **要求**：保留数学公式，准确翻译术语，去除笔名。

### 2️⃣ 编译 (LaTeX → PDF)
```powershell
python tools/compile_latex.py "docs/你的文件夹"
```
- 自动编译目录下的所有 `_en.tex`
- 自动清理辅助文件 (.aux, .log 等)

### 3️⃣ 上传 (Zenodo)
```powershell
python tools/batch_upload_zenodo.py "docs/你的文件夹"
```
- 为每个论文创建 Zenodo Record
- 上传 **MD + LaTeX + PDF** 三个文件
- 自动填写元数据 (Title, Abstract, Authors, Keywords)
- **智能跳过**：已成功上传（含PDF）的文件会自动跳过，支持断点续传

---

## 📁 核心文件说明

1.  **`zenodo_config.json`**
    - 配置 API Token、作者信息 (Name, ORCID)、默认关键词等。
2.  **`latex_template.tex`**
    - LaTeX 论文模板，控制文档格式。
3.  **`compile_latex.py`**
    - 批量编译脚本，调用 `pdflatex`。
4.  **`batch_upload_zenodo.py`**
    - 批量上传脚本，处理元数据提取和文件上传。
5.  **`zenodo_upload_records.json`**
    - 自动记录上传成功的 Deposition ID 和链接，防止重复上传。

---

## ✅ 检查清单

- [ ] 所有 `_en.tex` 文件已生成
- [ ] 所有 `_en.pdf` 文件已编译成功
- [ ] `zenodo_upload_records.json` 中包含所有文件的上传记录
- [ ] 登录 Zenodo 检查 Drafts，确认无误后点击 **Publish**
