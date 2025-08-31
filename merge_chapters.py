#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Merge all chapters 01-15 into a single comprehensive document
递归希尔伯特理论完整版生成器
"""

import os
import glob
import re
from pathlib import Path

def get_chapter_order():
    """定义章节顺序和名称"""
    return [
        ("01-mother-space", "第一章：递归母空间理论"),
        ("02-coordinates-projection", "第二章：坐标系与投影理论"), 
        ("03-recursive-dynamics", "第三章：递归动力学理论"),
        ("04-recursive-spectral-theory", "第四章：递归谱理论"),
        ("05-recursive-stability", "第五章：递归稳定性理论"),
        ("06-relative-incompatibility", "第六章：相对论不相容理论"),
        ("07-holographic-applications", "第七章：全息应用理论"),
        ("08-zeckendorf-hilbert-theory", "第八章：Zeckendorf-Hilbert理论"),
        ("09-recursive-topology", "第九章：递归拓扑理论"),
        ("10-recursive-measure-probability", "第十章：递归测度概率理论"),
        ("11-recursive-category-theory", "第十一章：递归范畴论"),
        ("12-recursive-algebraic-geometry", "第十二章：递归代数几何"),
        ("13-recursive-logic-foundations", "第十三章：递归数理逻辑基础"),
        ("14-recursive-algebraic-topology", "第十四章：递归代数拓扑"),
        ("15-recursive-number-theory", "第十五章：递归数论"),
        ("16-recursive-holographic-universe", "第十六章：递归全息宇宙论"),
        ("P17-recursive-quantum-mechanics", "P17章：递归量子力学"),
        ("P18-recursive-relativity-spacetime", "P18章：递归相对论与时空几何"),
        ("P19-recursive-cosmology-unification", "P19章：递归宇宙学与统一理论"),
        ("P20-recursive-observer-physics", "P20章：递归观察者物理学"),
    ]

def find_markdown_files(chapter_dir):
    """找到章节目录下的所有markdown文件，按数字顺序排序"""
    chapter_path = Path("docs/traditional-math/hilbert-complete") / chapter_dir
    
    if not chapter_path.exists():
        print(f"警告：章节目录不存在 {chapter_path}")
        return []
    
    # 查找所有.md文件，排除README.md
    md_files = []
    for md_file in chapter_path.glob("*.md"):
        if md_file.name != "README.md":
            md_files.append(md_file)
    
    # 按文件名中的数字排序
    def extract_section_number(filepath):
        filename = filepath.name
        # 匹配类似 "1.2.3-xxx.md" 的模式
        match = re.match(r'(\d+)\.(\d+)\.?(\d+)?', filename)
        if match:
            major = int(match.group(1))
            minor = int(match.group(2))
            sub = int(match.group(3)) if match.group(3) else 0
            return (major, minor, sub)
        # 匹配类似 "1.2-xxx.md" 的模式  
        match = re.match(r'(\d+)\.(\d+)', filename)
        if match:
            major = int(match.group(1))
            minor = int(match.group(2))
            return (major, minor, 0)
        return (0, 0, 0)
    
    md_files.sort(key=extract_section_number)
    return md_files

def clean_content(content):
    """清理内容，移除多余的空行"""
    lines = content.split('\n')
    cleaned_lines = []
    prev_empty = False
    
    for line in lines:
        if line.strip() == '':
            if not prev_empty:
                cleaned_lines.append('')
                prev_empty = True
        else:
            cleaned_lines.append(line)
            prev_empty = False
    
    return '\n'.join(cleaned_lines)

def generate_toc():
    """生成目录"""
    toc = ["# 递归希尔伯特理论完整版", ""]
    toc.append("## 理论概述")
    toc.append("")
    toc.append("本文档是递归希尔伯特理论的完整版，包含从第1章到第15章的所有内容。这是一个完整的数学理论体系，基于递归自相似希尔伯特空间，统一了现代数学的各个分支。")
    toc.append("")
    toc.append("## 目录")
    toc.append("")
    
    chapter_order = get_chapter_order()
    for i, (folder, title) in enumerate(chapter_order, 1):
        toc.append(f"- [{title}](#{i:02d}-{folder.replace('-', '')})")
    
    toc.append("")
    toc.append("---")
    toc.append("")
    
    return '\n'.join(toc)

def merge_chapters():
    """合并所有章节"""
    output_file = "docs/COMPLETE_RECURSIVE_HILBERT_THEORY.md"
    chapter_order = get_chapter_order()
    
    with open(output_file, 'w', encoding='utf-8') as outfile:
        # 写入目录
        outfile.write(generate_toc())
        
        # 处理每一章
        for chapter_num, (chapter_folder, chapter_title) in enumerate(chapter_order, 1):
            print(f"正在处理 {chapter_title}...")
            
            # 写入章节标题
            outfile.write(f"# {chapter_title}\n\n")
            
            # 查找章节中的所有markdown文件
            md_files = find_markdown_files(chapter_folder)
            
            if not md_files:
                outfile.write(f"*{chapter_title} 内容暂无*\n\n")
                continue
            
            # 处理每个文件
            for md_file in md_files:
                print(f"  - 添加文件：{md_file.name}")
                
                try:
                    with open(md_file, 'r', encoding='utf-8') as infile:
                        content = infile.read()
                        
                        # 清理内容
                        content = clean_content(content)
                        
                        # 如果文件有自己的一级标题，将其转换为二级标题
                        lines = content.split('\n')
                        processed_lines = []
                        
                        for line in lines:
                            # 调整标题级别：# -> ##, ## -> ###, etc.
                            if line.startswith('#'):
                                line = '#' + line
                            processed_lines.append(line)
                        
                        content = '\n'.join(processed_lines)
                        
                        outfile.write(content)
                        outfile.write('\n\n')
                        
                except Exception as e:
                    print(f"    错误：读取文件 {md_file} 失败：{e}")
                    outfile.write(f"*读取 {md_file.name} 失败*\n\n")
            
            # 章节分隔线
            outfile.write("---\n\n")
    
    print(f"\n✅ 合并完成！输出文件：{output_file}")
    
    # 统计信息
    with open(output_file, 'r', encoding='utf-8') as f:
        content = f.read()
        lines = len(content.split('\n'))
        words = len(content.split())
        chars = len(content)
    
    print(f"📊 统计信息：")
    print(f"   - 总行数：{lines:,}")
    print(f"   - 总字数：{words:,}")
    print(f"   - 总字符：{chars:,}")

if __name__ == "__main__":
    print("🚀 开始合并递归希尔伯特理论各章节...")
    merge_chapters()