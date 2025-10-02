#!/usr/bin/env python3
"""Generate plots summarizing critical-line experiments."""

import os
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", str(Path(__file__).resolve().parent / ".." / "data" / "mpl-cache"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import pandas as pd

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data" / "critical_line_limit"
IMAGE_DIR = ROOT / "docs" / "zeta-publish" / "images"
UNIFORM_PATH = DATA_DIR / "critical_line_uniform_samples.csv"
ZERO_PATH = DATA_DIR / "critical_line_zero_samples.csv"

def load_uniform() -> pd.DataFrame:
    return pd.read_csv(UNIFORM_PATH)

def load_zero() -> pd.DataFrame:
    return pd.read_csv(ZERO_PATH)

def ensure_dirs() -> None:
    IMAGE_DIR.mkdir(parents=True, exist_ok=True)

def plot_uniform(df: pd.DataFrame) -> None:
    fig, ax = plt.subplots(figsize=(10, 5))
    t = df["t"]
    ax.plot(t, df["i_plus"], label=r"$i_+$", color="#d55e00", alpha=0.5)
    ax.plot(t, df["i_zero"], label=r"$i_0$", color="#0072b2", alpha=0.5)
    ax.plot(t, df["i_minus"], label=r"$i_-$", color="#009e73", alpha=0.5)
    ax.plot(t, df["avg_i_plus"], label=r"$\langle i_+ \rangle$", color="#d55e00", linewidth=2)
    ax.plot(t, df["avg_i_zero"], label=r"$\langle i_0 \rangle$", color="#0072b2", linewidth=2)
    ax.plot(t, df["avg_i_minus"], label=r"$\langle i_- \rangle$", color="#009e73", linewidth=2)
    ax.axhline(0.403, color="#d55e00", linestyle="--", linewidth=1, alpha=0.6)
    ax.axhline(0.194, color="#0072b2", linestyle="--", linewidth=1, alpha=0.6)
    ax.set_xlabel("t")
    ax.set_ylabel("Information components")
    ax.set_title("Uniform sampling on the critical line")
    ax.legend(loc="best")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(IMAGE_DIR / "critical_line_uniform_components.png", dpi=200)
    plt.close(fig)

def plot_zero(df: pd.DataFrame, tail_size: int = 400) -> None:
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.plot(df["t"], df["i_plus"], label=r"$i_+$", color="#d55e00", alpha=0.35)
    ax.plot(df["t"], df["i_zero"], label=r"$i_0$", color="#0072b2", alpha=0.35)
    ax.plot(df["t"], df["i_minus"], label=r"$i_-$", color="#009e73", alpha=0.35)
    tail = df.tail(tail_size)
    ax.scatter(tail["t"], tail["i_plus"], color="#d55e00", s=10, label=f"Tail $i_+$ (last {tail_size})")
    ax.scatter(tail["t"], tail["i_zero"], color="#0072b2", s=10, label=f"Tail $i_0$ (last {tail_size})")
    ax.scatter(tail["t"], tail["i_minus"], color="#009e73", s=10, label=f"Tail $i_-$ (last {tail_size})")
    ax.axhline(0.403, color="#d55e00", linestyle="--", linewidth=1, alpha=0.6)
    ax.axhline(0.194, color="#0072b2", linestyle="--", linewidth=1, alpha=0.6)
    ax.set_xlabel("t (zeros)")
    ax.set_ylabel("Information components")
    ax.set_title("Zero-based sampling with local smoothing")
    ax.legend(loc="best")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(IMAGE_DIR / "critical_line_zero_components.png", dpi=200)
    plt.close(fig)

def plot_tail_stats(df: pd.DataFrame, windows=(100, 200, 400, 600)) -> None:
    rows = []
    for w in windows:
        tail = df.tail(w)
        rows.append({
            "window": w,
            "i_plus": tail["i_plus"].mean(),
            "i_zero": tail["i_zero"].mean(),
            "i_minus": tail["i_minus"].mean(),
        })
    stats_df = pd.DataFrame(rows)
    fig, ax = plt.subplots(figsize=(8, 4))
    ax.plot(stats_df["window"], stats_df["i_plus"], marker="o", label=r"$\overline{i_+}$", color="#d55e00")
    ax.plot(stats_df["window"], stats_df["i_zero"], marker="o", label=r"$\overline{i_0}$", color="#0072b2")
    ax.plot(stats_df["window"], stats_df["i_minus"], marker="o", label=r"$\overline{i_-}$", color="#009e73")
    ax.axhline(0.403, color="#d55e00", linestyle="--", linewidth=1, alpha=0.6)
    ax.axhline(0.194, color="#0072b2", linestyle="--", linewidth=1, alpha=0.6)
    ax.set_xlabel("Tail window size")
    ax.set_ylabel("Mean value")
    ax.set_title("Tail averages for zero-based sampling")
    ax.legend(loc="best")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(IMAGE_DIR / "critical_line_zero_tail_means.png", dpi=200)
    plt.close(fig)

def main() -> None:
    ensure_dirs()
    uniform_df = load_uniform()
    zero_df = load_zero()
    plot_uniform(uniform_df)
    plot_zero(zero_df)
    plot_tail_stats(zero_df)

if __name__ == "__main__":
    main()
