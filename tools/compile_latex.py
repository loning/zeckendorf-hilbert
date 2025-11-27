#!/usr/bin/env python3
"""
LaTeX → PDF 批量编译工具
用法: python tools/compile_latex.py
"""

import sys
from pathlib import Path

import subprocess
import shutil
import os

# 检测 pdflatex 路径
PDFLATEX_PATH = None
if os.path.exists(r"C:\Users\zwl62\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe"):
    PDFLATEX_PATH = r"C:\Users\zwl62\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe"
elif shutil.which('pdflatex'):
    PDFLATEX_PATH = 'pdflatex'

def check_pdflatex():
    """检查 pdflatex 是否可用"""
    if PDFLATEX_PATH is None:
        print("✗ 错误: 未检测到 pdflatex")
        print("\n请安装: winget install MiKTeX.MiKTeX")
        print("安装后重启终端")
        return False
    
    try:
        result = subprocess.run([PDFLATEX_PATH, '--version'], 
                              capture_output=True, text=True, timeout=5)
        version = result.stdout.split('\n')[0]
        print(f"✓ 已检测到 LaTeX: {version}")
        return True
    except Exception as e:
        print(f"✗ 检测 LaTeX 版本时出错: {e}")
        return False

def compile_latex(tex_file: Path):
    """编译单个 LaTeX 文件"""
    if not tex_file.exists():
        print(f"  ✗ 文件不存在: {tex_file}")
        return False
    
    try:
        # 使用系统 pdflatex
        cmd = [
            PDFLATEX_PATH,
            '-interaction=nonstopmode',
            '-output-directory=' + str(tex_file.parent),
            '-halt-on-error',
            str(tex_file)
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True, 
                              timeout=60, cwd=tex_file.parent)
        
        if result.returncode == 0:
            pdf_file = tex_file.with_suffix('.pdf')
            if pdf_file.exists():
                size_kb = pdf_file.stat().st_size / 1024
                print(f"  ✓ 成功 → {size_kb:.1f} KB")
                return True
        
        print("  ✗ 编译失败")
        log_file = tex_file.with_suffix('.log')
        if log_file.exists():
            print(f"    查看日志: {log_file}")
        return False
    
    except subprocess.TimeoutExpired:
        print("  ✗ 编译超时（>60秒）")
        return False
    except Exception as e:
        print(f"  ✗ 错误: {e}")
        return False

def main():
    print("=" * 50)
    print("  LaTeX → PDF 批量编译")
    print("=" * 50)
    print()
    
    # 检查 pdflatex
    if not check_pdflatex():
        sys.exit(1)
    
    print()
    
    # 获取目标文件夹
    base_dir = Path(__file__).parent.parent
    
    if len(sys.argv) > 1:
        # 使用命令行参数指定的文件夹
        target_dir = Path(sys.argv[1])
        if not target_dir.is_absolute():
            target_dir = base_dir / target_dir
    else:
        # 默认扫描整个 docs 目录
        target_dir = base_dir / "docs"
    
    # 查找所有 _en.tex 文件
    latex_files = sorted(target_dir.rglob("*_en.tex"))
    
    if not latex_files:
        print(f"✗ 未找到任何 _en.tex 文件在: {target_dir}")
        sys.exit(1)
    
    print(f"找到 {len(latex_files)} 个 LaTeX 文件:")
    for f in latex_files:
        print(f"  - {f.relative_to(base_dir)}")
    print()
    
    success_count = 0
    fail_count = 0
    
    # 编译每个文件
    for i, tex_file in enumerate(latex_files, 1):
        print(f"[{i}/{len(latex_files)}] 编译: {tex_file.name}")
        if compile_latex(tex_file):
            success_count += 1
        else:
            fail_count += 1
        print()
    
    # 总结
    print("=" * 50)
    print("  编译完成")
    print("=" * 50)
    print()
    print(f"成功: {success_count} / {len(latex_files)}")
    if fail_count > 0:
        print(f"失败: {fail_count} / {len(latex_files)}")
    print()
    
    # 自动清理辅助文件
    print("清理辅助文件...")
    cleaned_count = 0
    
    # 获取所有包含 _en.tex 的目录
    dirs = set(f.parent for f in latex_files)
    
    for output_dir in dirs:
        for ext in ['.aux', '.log', '.out', '.toc']:
            for file in output_dir.glob(f'*{ext}'):
                file.unlink()
                cleaned_count += 1
    
    print(f"✓ 清理完成 (删除 {cleaned_count} 个辅助文件)")
    print()

if __name__ == '__main__':
    main()

