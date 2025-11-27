#!/usr/bin/env python3
"""
批量上传 PDF 到 Zenodo (仅上传 PDF 文件)

用法:
    python tools/upload_pdf_only_zenodo.py <folder_path>

示例:
    python tools/upload_pdf_only_zenodo.py docs/euler-gls-paper-bondary
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
        abstract = re.sub(r'\\textbf\{([^}]+)\}', r'\1', abstract)
        abstract = re.sub(r'\\[a-zA-Z]+\{([^}]+)\}', r'\1', abstract)
        abstract = re.sub(r'\$\$[^$]+\$\$', '', abstract)  # 移除显示公式
        abstract = re.sub(r'\$([^$]+)\$', r'\1', abstract)  # 保留内联公式内容
        abstract = re.sub(r'\s+', ' ', abstract)
        return abstract[:500]  # 限制长度
    return "English translation of theoretical physics paper."

def extract_title_from_latex(tex_file):
    """从 LaTeX 文件中提取标题"""
    with open(tex_file, 'r', encoding='utf-8') as f:
        tex_content = f.read()
    
    title_match = re.search(r'\\title\{([^}]+)\}', tex_content, re.MULTILINE | re.DOTALL)
    if title_match:
        title = title_match.group(1)
        # 清理换行和多余空格
        title = re.sub(r'\\\\', ' ', title)  # 移除换行命令
        title = re.sub(r'\s+', ' ', title)
        # 清理 LaTeX 数学符号
        title = re.sub(r'\$([^$]+)\$', r'\1', title)
        return title.strip()
    return "Untitled"

def upload_pdf_to_zenodo(pdf_file, tex_file, config_file='tools/zenodo_config.json'):
    """
    上传英文 PDF 到 Zenodo (仅上传 PDF 文件)
    
    Args:
        pdf_file: PDF 文件路径 (实际上传的文件)
        tex_file: LaTeX 文件路径 (用于提取标题和摘要)
        config_file: Zenodo 配置文件路径
    
    Returns:
        dict: 上传记录
    """
    # 加载配置
    with open(config_file, 'r', encoding='utf-8') as f:
        config = json.load(f)
    
    TOKEN = config['zenodo_token']
    API_URL = config['zenodo_endpoint']
    
    tex_path = Path(tex_file)
    pdf_path = Path(pdf_file)
    
    print(f"=" * 80)
    print(f"Zenodo Upload: {pdf_path.stem}")
    print(f"=" * 80)
    print(f"\n📁 File (PDF only):")
    print(f"  {pdf_path.name} ({pdf_path.stat().st_size/1024:.1f} KB)")
    
    # 提取摘要和标题
    print(f"\n📄 Extracting metadata from LaTeX...")
    title = extract_title_from_latex(tex_path)
    abstract = extract_abstract_from_latex(tex_path)
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
    
    # 上传 PDF 文件
    print(f"\n[2/4] Uploading PDF...")
    if not pdf_path.exists():
        print(f"  ✗ PDF file not found: {pdf_path}")
        return None
    
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
        return None
    
    print(f"  ✓ PDF uploaded")
    
    # 更新元数据
    print(f"\n[3/4] Updating metadata...")
    
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
        "output_pdf": str(pdf_path),
        "source_tex": str(tex_path),
        "deposition_id": deposition_id,
        "doi": None,
        "doi_url": None,
        "url": f"https://zenodo.org/deposit/{deposition_id}",
        "status": "draft",
        "files_uploaded": [pdf_path.name],
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
    print(f"  File: {pdf_path.name}")
    print(f"  Status: Draft")
    print(f"\n🔗 View: https://zenodo.org/deposit/{deposition_id}")
    print("\n" + "=" * 80 + "\n")
    
    return record

def batch_upload_folder(folder_path):
    """批量上传文件夹中所有 PDF 文件"""
    folder = Path(folder_path)
    
    # 查找所有 _en.pdf 文件
    pdf_files = sorted(folder.glob("*_en.pdf"))
    
    print(f"=" * 80)
    print(f"批量上传 PDF 到 Zenodo")
    print(f"=" * 80)
    print(f"\n📂 文件夹: {folder}")
    print(f"📄 找到 {len(pdf_files)} 个 PDF 文件\n")
    
    # Load existing records to check for duplicates
    records_file = Path('tools/zenodo_upload_records.json')
    existing_records = {}
    if records_file.exists():
        try:
            with open(records_file, 'r', encoding='utf-8') as f:
                loaded_records = json.load(f)
                for rec in loaded_records:
                    if 'output_pdf' in rec:
                        key = str(Path(rec['output_pdf'])).replace('\\', '/')
                        existing_records[key] = rec
        except Exception as e:
            print(f"Warning: Could not load existing records: {e}")
    
    results = []
    for i, pdf_file in enumerate(pdf_files, 1):
        # Check if already uploaded
        pdf_key = str(pdf_file).replace('\\', '/')
        if pdf_key in existing_records:
            rec = existing_records[pdf_key]
            print(f"\n[{i}/{len(pdf_files)}] Skipping {pdf_file.stem} (Already uploaded)")
            results.append({
                "file": pdf_file.stem,
                "status": "skipped",
                "url": rec.get('url', '')
            })
            continue
        
        # 找到对应的 TeX 文件
        tex_file = pdf_file.with_suffix('.tex')
        
        print(f"\n[{i}/{len(pdf_files)}] Processing: {pdf_file.stem}")
        print("-" * 80)
        
        if not tex_file.exists():
            print(f"  ⚠ LaTeX file not found: {tex_file.name}")
            results.append({
                "file": pdf_file.stem,
                "status": "failed",
                "error": "LaTeX file not found"
            })
            continue
        
        # 上传
        try:
            record = upload_pdf_to_zenodo(pdf_file, tex_file)
            if record:
                results.append({
                    "file": pdf_file.stem,
                    "status": "success",
                    "deposition_id": record['deposition_id'],
                    "url": record['url']
                })
            else:
                results.append({
                    "file": pdf_file.stem,
                    "status": "failed"
                })
        except Exception as e:
            print(f"✗ Error: {e}")
            results.append({
                "file": pdf_file.stem,
                "status": "error",
                "error": str(e)
            })
    
    # 总结
    print("\n" + "=" * 80)
    print("批量上传完成")
    print("=" * 80)
    print(f"\n总计: {len(pdf_files)} 个文件")
    success_count = sum(1 for r in results if r['status'] == 'success')
    skipped_count = sum(1 for r in results if r['status'] == 'skipped')
    failed_count = len(results) - success_count - skipped_count
    print(f"成功: {success_count}")
    print(f"跳过: {skipped_count}")
    if failed_count > 0:
        print(f"失败: {failed_count}")
    
    print("\n📋 上传记录:")
    for r in results:
        if r['status'] == 'success':
            print(f"  ✓ {r['file']}")
            print(f"    → {r['url']}")
        elif r['status'] == 'skipped':
            print(f"  - {r['file']} (已跳过)")
        else:
            print(f"  ✗ {r['file']}: {r.get('error', r['status'])}")
    
    print("\n" + "=" * 80)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        folder_path = sys.argv[1]
    else:
        print("用法: python tools/upload_pdf_only_zenodo.py <folder_path>")
        print("示例: python tools/upload_pdf_only_zenodo.py docs/euler-gls-paper-bondary")
        sys.exit(1)
    
    batch_upload_folder(folder_path)

