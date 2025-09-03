import os
import shutil
import subprocess
from datetime import datetime

def get_git_commit_id():
    """현재 git commit id (짧은 7자리) 가져오기"""
    try:
        commit_id = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], stderr=subprocess.DEVNULL
        ).decode().strip()
        return commit_id[:7]
    except Exception:
        return "nogit"

def backup_directory(src_dir, dst_parent="."):
    now = datetime.now().strftime("%Y%m%d_%H%M%S")
    commit_id = get_git_commit_id()
    backup_dir = os.path.join(dst_parent, f"backup_{now}_{commit_id}")

    for root, dirs, files in os.walk(src_dir):
        rel_path = os.path.relpath(root, src_dir)
        dst_root = os.path.join(backup_dir, rel_path)
        os.makedirs(dst_root, exist_ok=True)

        for f in files:
            src_path = os.path.join(root, f)
            dst_path = os.path.join(dst_root, f)
            shutil.copy2(src_path, dst_path)
            print(f"{src_path} → {dst_path}")

    print(f"\nBackup complete: {backup_dir}")

if __name__ == "__main__":
    source_directory = "result/dilemma"   # 원하는 디렉토리 경로
    backup_directory(source_directory, dst_parent=".")
    summary_directory = "summary"
    backup_directory(summary_directory, dst_parent=".")