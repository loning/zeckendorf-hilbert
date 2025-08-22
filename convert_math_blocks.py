#!/usr/bin/env python3

import re
import glob

def convert_math_blocks(file_path):
    """将 ```math 块转换为 $$ 块"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 使用正则表达式替换 ```math...``` 为 $$...$$
    pattern = r'```math\n(.*?)\n```'
    replacement = r'$$\n\1\n$$'
    
    new_content = re.sub(pattern, replacement, content, flags=re.DOTALL)
    
    # 检查是否有修改
    if new_content != content:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return True
    return False

def main():
    print("Converting ```math blocks to $$ blocks...")
    
    # 查找所有 .md 文件
    md_files = glob.glob('docs/**/*.md', recursive=True)
    
    converted_count = 0
    for file_path in md_files:
        if convert_math_blocks(file_path):
            print(f"Converted: {file_path}")
            converted_count += 1
        else:
            print(f"No changes: {file_path}")
    
    print(f"\nConversion completed! {converted_count} files modified.")

if __name__ == "__main__":
    main()