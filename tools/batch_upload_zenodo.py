#!/usr/bin/env python3
"""
批量上传 Zenodo - 支持 MD + LaTeX + PDF

用法:
    python tools/batch_upload_zenodo.py <folder_path>

示例:
    python tools/batch_upload_zenodo.py docs/euler-physics
"""
import sys
import requests
import json
import re
from pathlib import Path
from datetime import datetime

def extract_abstract_from_latex(tex_file):
    """从 LaTeX 文件中提取摘要"""
    with open(tex_file, 'r', encoding='utf-8') as f:
        tex_content = f.read()
    
    abstract_match = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', tex_content, re.DOTALL)
    if abstract_match:
        abstract = abstract_match.group(1).strip()
        # 清理 LaTeX 命令
        abstract_plain = re.sub(r'\\textbf\{([^}]+)\}', r'\1', abstract)
        abstract_plain = re.sub(r'\\[a-zA-Z]+\{([^}]+)\}', r'\1', abstract_plain)
        abstract_plain = re.sub(r'\$([^$]+)\$', r'\1', abstract_plain)
        abstract_plain = re.sub(r'\s+', ' ', abstract_plain)
        return abstract_plain
    return None

def extract_title_from_latex(tex_file):
    """从 LaTeX 文件中提取标题"""
    with open(tex_file, 'r', encoding='utf-8') as f:
        tex_content = f.read()
    
    title_match = re.search(r'\\title\{([^}]+)\}', tex_content)
    if title_match:
        title = title_match.group(1)
        # 清理 LaTeX 数学符号
        title = re.sub(r'\$([^$]+)\$', r'\1', title)
        return title.strip()
    return "Untitled"

def upload_to_zenodo(md_file, tex_file, pdf_file, config_file='tools/zenodo_config.json'):
    """
    上传英文 PDF 到 Zenodo (仅上传 PDF 文件)
    
    Args:
        md_file: Markdown 文件路径 (用于生成元数据)
        tex_file: LaTeX 文件路径 (用于提取标题和摘要)
        pdf_file: PDF 文件路径 (实际上传的文件)
        config_file: Zenodo 配置文件路径
    
    Returns:
        dict: 上传记录
    """
    # 加载配置
    with open(config_file, 'r', encoding='utf-8') as f:
        config = json.load(f)
    
    TOKEN = config['zenodo_token']
    API_URL = config['zenodo_endpoint']
    
    md_path = Path(md_file)
    tex_path = Path(tex_file)
    pdf_path = Path(pdf_file)
    
    print(f"=" * 80)
    print(f"Zenodo Upload: {md_path.stem}")
    print(f"=" * 80)
    print(f"\n📁 Files (Uploading PDF only):")
    print(f"  PDF: {pdf_path.name} ({pdf_path.stat().st_size/1024:.1f} KB)")
    print(f"  (Using MD/TeX for metadata extraction only)")
    
    # 提取摘要和标题
    print(f"\n📄 Extracting metadata...")
    title = extract_title_from_latex(tex_path)
    abstract = extract_abstract_from_latex(tex_path)
    if not abstract:
        abstract = "English LaTeX translation of theoretical physics paper."
    print(f"✓ Title: {title[:60]}...")
    print(f"✓ Abstract: {len(abstract)} chars")
    
    # 创建 deposition
    print(f"\n[1/4] Creating deposition...")
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {TOKEN}"
    }
    
    r = requests.post(f"{API_URL}/deposit/depositions", json={}, headers=headers)
    if r.status_code != 201:
        print(f"✗ Error: {r.status_code}")
        print(r.text)
        return None
    
    deposition = r.json()
    deposition_id = deposition['id']
    bucket_url = deposition['links']['bucket']
    print(f"✓ Deposition ID: {deposition_id}")
    
    # 上传文件 (仅上传 PDF)
    print(f"\n[2/4] Uploading PDF file...")
    
    uploaded_files = []
    if not pdf_path.exists():
        print(f"  ✗ PDF file not found: {pdf_path.name}")
    else:
        print(f"  Uploading {pdf_path.name}...")
        with open(pdf_path, 'rb') as f:
            r = requests.put(
                f"{bucket_url}/{pdf_path.name}",
                data=f,
                headers={"Authorization": f"Bearer {TOKEN}"}
            )
        
        if r.status_code not in [200, 201]:
            print(f"  ✗ Error uploading PDF: {r.status_code}")
            print(f"  {r.text}")
        else:
            print(f"  ✓ PDF uploaded")
            uploaded_files.append(pdf_path.name)
    
    if len(uploaded_files) == 0:
        print(f"✗ No files uploaded successfully")
        return None
    
    # 更新元数据 - 使用 legacy 格式
    print(f"\n[3/4] Updating metadata...")
    
    # 准备 creators (legacy format: "LastName, FirstName")
    creators = []
    for creator in config['default_metadata']['creators']:
        creator_entry = {
            "name": creator['name'],
            "affiliation": creator['affiliation']
        }
        
        if 'orcid' in creator and creator['orcid']:
            creator_entry['orcid'] = creator['orcid']
        
        creators.append(creator_entry)
    
    metadata = {
        "metadata": {
            "title": title,
            "upload_type": "publication",
            "publication_type": "article",
            "description": abstract,
            "creators": creators,
            "access_right": "open",
            "license": "cc-by-4.0",
            "keywords": config['default_metadata'].get('keywords', []),
            "prereserve_doi": True
        }
    }
    
    r = requests.put(
        f"{API_URL}/deposit/depositions/{deposition_id}",
        json=metadata,
        headers=headers
    )
    
    if r.status_code != 200:
        print(f"✗ Error updating metadata: {r.status_code}")
        print(r.text)
        return None
    
    print(f"✓ Metadata updated")
    
    # 保存记录
    print(f"\n[4/4] Saving record...")
    records_file = Path('tools/zenodo_upload_records.json')
    if records_file.exists():
        with open(records_file, 'r', encoding='utf-8') as f:
            records = json.load(f)
    else:
        records = []
    
    record = {
        "source_md": str(md_path),
        "output_tex": str(tex_path),
        "output_pdf": str(pdf_path),
        "deposition_id": deposition_id,
        "doi": None,
        "doi_url": None,
        "url": f"https://zenodo.org/deposit/{deposition_id}",
        "status": "draft",
        "files_uploaded": uploaded_files,
        "upload_time": datetime.now().isoformat()
    }
    
    records.append(record)
    with open(records_file, 'w', encoding='utf-8') as f:
        json.dump(records, f, ensure_ascii=False, indent=2)
    
    print(f"✓ Record saved")
    
    print("\n" + "=" * 80)
    print("✅ UPLOAD SUCCESSFUL")
    print("=" * 80)
    print(f"\n📋 Summary:")
    print(f"  Deposition ID: {deposition_id}")
    print(f"  Files: {', '.join(uploaded_files)}")
    print(f"  Status: Draft")
    print(f"\n🔗 View: https://zenodo.org/deposit/{deposition_id}")
    print("\n" + "=" * 80 + "\n")
    
    return record

def batch_upload_folder(folder_path):
    """批量上传文件夹中的所有文件"""
    folder = Path(folder_path)
    
    # 查找所有 MD 文件
    md_files = list(folder.glob("*.md"))
    
    # 过滤掉已翻译的文件（*_en.md）
    md_files = [f for f in md_files if not f.stem.endswith('_en')]
    
    print(f"=" * 80)
    print(f"批量上传到 Zenodo")
    print(f"=" * 80)
    print(f"\n📂 文件夹: {folder}")
    print(f"📄 找到 {len(md_files)} 个 MD 文件\n")
    
    # Load existing records to check for duplicates/completions
    records_file = Path('tools/zenodo_upload_records.json')
    existing_records = {}
    if records_file.exists():
        try:
            with open(records_file, 'r', encoding='utf-8') as f:
                loaded_records = json.load(f)
                for rec in loaded_records:
                    # Use source_md as key, normalize path separators
                    key = str(Path(rec['source_md'])).replace('\\', '/')
                    existing_records[key] = rec
        except Exception as e:
            print(f"Warning: Could not load existing records: {e}")

    results = []
    for i, md_file in enumerate(md_files, 1):
        # Check if already fully uploaded
        md_key = str(md_file).replace('\\', '/')
        if md_key in existing_records:
            rec = existing_records[md_key]
            # Check if PDF was uploaded (assuming PDF name is derived from MD stem)
            pdf_name = f"{md_file.stem}_en.pdf"
            if 'files_uploaded' in rec and any(f.endswith('.pdf') for f in rec['files_uploaded']):
                print(f"\n[{i}/{len(md_files)}] Skipping {md_file.stem} (Already uploaded)")
                results.append({
                    "file": md_file.stem,
                    "status": "skipped",
                    "url": rec.get('url', '')
                })
                continue
        
        tex_file = folder / f"{md_file.stem}_en.tex"
        pdf_file = folder / f"{md_file.stem}_en.pdf"
        
        print(f"\n[{i}/{len(md_files)}] Processing: {md_file.stem}")
        print("-" * 80)
        
        # 检查文件是否存在
        if not tex_file.exists():
            print(f"  ⚠ LaTeX file not found: {tex_file.name}")
            continue
        
        if not pdf_file.exists():
            print(f"  ⚠ PDF file not found: {pdf_file.name}")
            continue
        
        # 上传
        try:
            record = upload_to_zenodo(md_file, tex_file, pdf_file)
            if record:
                results.append({
                    "file": md_file.stem,
                    "status": "success",
                    "deposition_id": record['deposition_id'],
                    "url": record['url']
                })
            else:
                results.append({
                    "file": md_file.stem,
                    "status": "failed"
                })
        except Exception as e:
            print(f"✗ Error: {e}")
            results.append({
                "file": md_file.stem,
                "status": "error",
                "error": str(e)
            })
    
    # 总结
    print("\n" + "=" * 80)
    print("批量上传完成")
    print("=" * 80)
    print(f"\n总计: {len(md_files)} 个文件")
    success_count = sum(1 for r in results if r['status'] == 'success')
    print(f"成功: {success_count}")
    print(f"失败: {len(results) - success_count}")
    
    print("\n📋 上传记录:")
    for r in results:
        if r['status'] == 'success':
            print(f"  ✓ {r['file']}")
            print(f"    → {r['url']}")
        else:
            print(f"  ✗ {r['file']}: {r['status']}")
    
    print("\n" + "=" * 80)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        # 使用命令行参数指定的文件夹
        folder_path = sys.argv[1]
    else:
        # 默认使用 docs 目录下的所有子文件夹
        print("用法: python tools/batch_upload_zenodo.py <folder_path>")
        print("示例: python tools/batch_upload_zenodo.py docs/euler-physics")
        sys.exit(1)
    
    batch_upload_folder(folder_path)

