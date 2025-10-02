#!/usr/bin/env python3
"""Empirically verify the critical-line limit theorem (Theorem 4.2).

This version supports incremental execution: rerun with --resume and optional
chunk sizes to extend existing datasets without recomputing prior samples.
"""

from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verify_unified_info_definitions import UnifiedInfoDefinitions  # type: ignore

THEORETICAL_LIMITS = {
    "i_plus": 0.403,
    "i_zero": 0.194,
    "i_minus": 0.403,
}

def parse_recompute_arg(value: Optional[str]) -> Optional[int]:
    if value is None:
        return None
    cleaned = value.strip().lower()
    if cleaned in {"all", "*", "inf"}:
        return -1
    try:
        parsed = int(cleaned)
    except ValueError:
        raise SystemExit(f"Invalid recompute argument: {value}")
    return parsed


def parse_weight_modes(value: Optional[str]) -> List[str]:
    if value is None or value.strip() == "":
        return ["delta"]
    modes = []
    for raw in value.split(','):
        mode = raw.strip().lower()
        if not mode:
            continue
        if mode not in {"delta", "log", "delta_log"}:
            raise SystemExit(f"Unsupported zero weight mode: {raw}")
        modes.append(mode)
    return modes or ["delta"]



@dataclass
class Sample:
    t: float
    i_plus: float
    i_zero: float
    i_minus: float

    def as_row(self) -> List[float]:
        return [self.t, self.i_plus, self.i_zero, self.i_minus]


@dataclass
class ZeroSample:
    index: int
    t: float
    i_plus: float
    i_zero: float
    i_minus: float

    def as_row(self) -> List[float]:
        return [self.index, self.t, self.i_plus, self.i_zero, self.i_minus]


@dataclass
class DatasetStats:
    overall: dict[str, float]
    tail: dict[str, float]


def compute_samples(model: UnifiedInfoDefinitions, t_values: Iterable[float]) -> List[Sample]:
    samples: List[Sample] = []
    for t in t_values:
        if abs(t) < 1e-16:
            continue
        s = mp.mpf("0.5") + 1j * mp.mpf(t)
        i_plus, i_zero, i_minus = model.normalized_info_components(s)
        samples.append(
            Sample(
                t=float(t),
                i_plus=float(i_plus),
                i_zero=float(i_zero),
                i_minus=float(i_minus),
            )
        )
    return samples


def running_averages(values: Sequence[float]) -> List[float]:
    totals: List[float] = []
    cumulative = 0.0
    for idx, value in enumerate(values, 1):
        cumulative += value
        totals.append(cumulative / idx)
    return totals


def make_uniform_grid(max_t: float, num_points: int) -> np.ndarray:
    lower = 5.0 if max_t > 5 else 1.0
    if num_points <= 1 or max_t <= lower:
        return np.array([max_t], dtype=float)
    ratio = max_t / lower
    if ratio >= 10:
        return np.geomspace(lower, max_t, num_points)
    return np.linspace(lower, max_t, num_points)


def load_precomputed_zeros(path: Path, count: int) -> List[float]:
    loaded: List[float] = []
    try:
        with path.open() as fh:
            for line in fh:
                value = line.strip()
                if not value:
                    continue
                loaded.append(float(value))
                if len(loaded) == count:
                    break
    except OSError:
        return []
    return loaded


def acquire_zero_imag_parts(count: int, zero_data_path: Optional[Path]) -> List[float]:
    precomputed: List[float] = []
    if zero_data_path is not None and zero_data_path.is_file():
        precomputed = load_precomputed_zeros(zero_data_path, count)
        if precomputed:
            print(f"Loaded {len(precomputed)} precomputed zeros from {zero_data_path}")
    if len(precomputed) >= count:
        return precomputed[:count]

    imag_parts = precomputed[:]
    start_index = len(precomputed) + 1
    missing = count - len(precomputed)
    if missing > 0 and precomputed:
        print(f"Computing remaining {missing} zeros via mpmath (continuing from index {start_index})")
    elif missing > 0:
        print(f"Computing {missing} zeros via mpmath")
    for n in range(start_index, count + 1):
        zero = mp.zetazero(n)
        imag_parts.append(float(mp.im(zero)))
    return imag_parts


def load_uniform_samples(path: Path) -> List[Sample]:
    if not path.exists():
        return []
    with path.open() as fh:
        reader = csv.DictReader(fh)
        samples = [
            Sample(
                t=float(row["t"]),
                i_plus=float(row["i_plus"]),
                i_zero=float(row["i_zero"]),
                i_minus=float(row["i_minus"]),
            )
            for row in reader
        ]
    return samples


def load_zero_samples(path: Path) -> List[ZeroSample]:
    if not path.exists():
        return []
    with path.open() as fh:
        reader = csv.DictReader(fh)
        samples = [
            ZeroSample(
                index=int(float(row["index"])),
                t=float(row["t"]),
                i_plus=float(row["i_plus"]),
                i_zero=float(row["i_zero"]),
                i_minus=float(row["i_minus"]),
            )
            for row in reader
        ]
    return samples


def write_uniform_csv(samples: Sequence[Sample], path: Path) -> None:
    avg_plus = running_averages([s.i_plus for s in samples])
    avg_zero = running_averages([s.i_zero for s in samples])
    avg_minus = running_averages([s.i_minus for s in samples])

    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow([
            "t",
            "i_plus",
            "i_zero",
            "i_minus",
            "avg_i_plus",
            "avg_i_zero",
            "avg_i_minus",
        ])
        for sample, m_plus, m_zero, m_minus in zip(samples, avg_plus, avg_zero, avg_minus):
            writer.writerow(
                [
                    sample.t,
                    sample.i_plus,
                    sample.i_zero,
                    sample.i_minus,
                    m_plus,
                    m_zero,
                    m_minus,
                ]
            )


def write_zero_csv(samples: Sequence[ZeroSample], path: Path) -> None:
    avg_plus = running_averages([s.i_plus for s in samples])
    avg_zero = running_averages([s.i_zero for s in samples])
    avg_minus = running_averages([s.i_minus for s in samples])

    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow([
            "index",
            "t",
            "i_plus",
            "i_zero",
            "i_minus",
            "avg_i_plus",
            "avg_i_zero",
            "avg_i_minus",
        ])
        for sample, m_plus, m_zero, m_minus in zip(samples, avg_plus, avg_zero, avg_minus):
            writer.writerow(
                [
                    sample.index,
                    sample.t,
                    sample.i_plus,
                    sample.i_zero,
                    sample.i_minus,
                    m_plus,
                    m_zero,
                    m_minus,
                ]
            )


def compute_stats(
    samples: Sequence[Sample],
    tail_min: int = 25,
    tail_ratio: float = 0.2,
    weights: Optional[Sequence[float]] = None,
) -> DatasetStats:
    if not samples:
        empty = {key: float("nan") for key in THEORETICAL_LIMITS}
        return DatasetStats(empty, empty)

    def avg(values: np.ndarray, w: Optional[np.ndarray]) -> float:
        if w is None:
            return float(np.mean(values))
        total = float(np.sum(w))
        if total == 0:
            return float("nan")
        return float(np.dot(values, w) / total)

    values_plus = np.array([s.i_plus for s in samples], dtype=float)
    values_zero = np.array([s.i_zero for s in samples], dtype=float)
    values_minus = np.array([s.i_minus for s in samples], dtype=float)
    weight_array = np.array(weights, dtype=float) if weights is not None else None

    overall = {
        "i_plus": avg(values_plus, weight_array),
        "i_zero": avg(values_zero, weight_array),
        "i_minus": avg(values_minus, weight_array),
    }

    tail_len = min(len(samples), max(tail_min, int(len(samples) * tail_ratio)))
    tail_slice = slice(len(samples) - tail_len, len(samples))
    tail_weights = weight_array[tail_slice] if weight_array is not None else None
    tail = {
        "i_plus": avg(values_plus[tail_slice], tail_weights),
        "i_zero": avg(values_zero[tail_slice], tail_weights),
        "i_minus": avg(values_minus[tail_slice], tail_weights),
    }

    return DatasetStats(overall=overall, tail=tail)


def zero_sample_weights(samples: Sequence[ZeroSample], mode: str) -> List[float]:
    if not samples:
        return []

    def delta_weights() -> List[float]:
        weights: List[float] = []
        for idx, current in enumerate(samples):
            if idx < len(samples) - 1:
                dt = samples[idx + 1].t - current.t
            elif len(samples) > 1:
                dt = current.t - samples[idx - 1].t
            else:
                dt = 1.0
            weights.append(float(abs(dt)))
        return weights

    def log_weights() -> List[float]:
        weights: List[float] = []
        for entry in samples:
            t_abs = abs(entry.t)
            if t_abs <= 0:
                weight = 0.0
            else:
                t_scaled = max(t_abs, float(np.e))
                weight = 1.0 / np.log(t_scaled)
            weights.append(float(weight))
        return weights

    mode = mode.lower()
    if mode == "delta":
        return delta_weights()
    if mode == "log":
        return log_weights()
    if mode == "delta_log":
        delta = np.array(delta_weights(), dtype=float)
        log = np.array(log_weights(), dtype=float)
        return list((delta * log).astype(float))
    raise ValueError(f"Unsupported zero weight mode: {mode}")


def report_stats(title: str, stats: DatasetStats) -> None:
    print(f"{title} (overall):")
    for key, expected in THEORETICAL_LIMITS.items():
        observed = stats.overall[key]
        delta = observed - expected
        print(f"{key:<7} observed={observed:.6f} expected={expected:.3f} delta={delta:+.6f}")
    print(f"\n{title} (tail window):")
    for key, expected in THEORETICAL_LIMITS.items():
        observed = stats.tail[key]
        delta = observed - expected
        print(f"{key:<7} observed={observed:.6f} expected={expected:.3f} delta={delta:+.6f}")


def build_uniform_dataset(
    model: UnifiedInfoDefinitions,
    max_t: float,
    num_points: int,
    output_dir: Path,
    resume: bool,
    chunk_size: Optional[int],
    recompute: Optional[int],
) -> tuple[List[Sample], int, int]:
    path = output_dir / "critical_line_uniform_samples.csv"
    existing = load_uniform_samples(path) if resume else []

    grid = make_uniform_grid(max_t, num_points)
    total_target = min(num_points, len(grid))
    existing = existing[:total_target]
    already = len(existing)

    # Optional recomputation of existing uniform samples
    recomputed = 0
    if recompute and existing:
        if recompute < 0 or recompute >= len(existing):
            indices = list(range(len(existing)))
        else:
            indices = list(range(len(existing) - recompute, len(existing)))
        if indices:
            print(f"Recomputing {len(indices)} uniform samples (indices {indices[0]}..{indices[-1]})")
            t_values = [existing[i].t for i in indices]
            updated = compute_samples(model, t_values)
            for offset, sample in zip(indices, updated):
                existing[offset] = Sample(sample.t, sample.i_plus, sample.i_zero, sample.i_minus)
            recomputed = len(indices)

    already = len(existing)
    remaining = total_target - already
    compute_count = remaining if chunk_size is None else min(remaining, max(chunk_size, 0))
    if compute_count > 0:
        start = already
        end = start + compute_count
        print(f"Computing {compute_count} new uniform samples (indices {start}..{end-1})")
        new_samples = compute_samples(model, grid[start:end])
        combined = existing + new_samples
    else:
        combined = existing

    write_uniform_csv(combined, path)
    stats = compute_stats(combined)
    report_stats("Uniform sampling", stats)
    print(f"Uniform samples stored: {len(combined)} / {total_target}")
    if len(combined) < total_target:
        print("Uniform dataset incomplete; rerun with --resume to continue.")
    return combined, compute_count, total_target


def local_average_samples(
    model: UnifiedInfoDefinitions,
    center: float,
    radius: float,
    count: int,
) -> Sample:
    if count <= 1:
        return compute_samples(model, [center])[0]
    t_values = np.linspace(center - radius, center + radius, count)
    samples = compute_samples(model, t_values)
    avg_plus = float(np.mean([s.i_plus for s in samples]))
    avg_zero = float(np.mean([s.i_zero for s in samples]))
    avg_minus = float(np.mean([s.i_minus for s in samples]))
    return Sample(t=center, i_plus=avg_plus, i_zero=avg_zero, i_minus=avg_minus)


def build_zero_dataset(
    model: UnifiedInfoDefinitions,
    num_zeros: int,
    output_dir: Path,
    zero_data_path: Optional[Path],
    resume: bool,
    chunk_size: Optional[int],
    recompute: Optional[int],
    weight_modes: Sequence[str],
    local_radius: float,
    local_scale: float,
    local_count: int,
) -> tuple[List[ZeroSample], int, int]:
    path = output_dir / "critical_line_zero_samples.csv"
    existing = load_zero_samples(path) if resume else []

    total_target = num_zeros
    zeros_all = acquire_zero_imag_parts(total_target, zero_data_path) if total_target > 0 else []
    existing = existing[:total_target]
    already = len(existing)

    def effective_radius(global_idx: int) -> float:
        radius = max(local_radius, 0.0)
        if local_scale > 0 and zeros_all:
            left_gap = zeros_all[global_idx] - zeros_all[global_idx - 1] if global_idx > 0 else 0.0
            right_gap = zeros_all[global_idx + 1] - zeros_all[global_idx] if global_idx < len(zeros_all) - 1 else 0.0
            gaps = [gap for gap in (left_gap, right_gap) if gap > 0]
            if gaps:
                spacing = sum(gaps) / len(gaps)
                radius += local_scale * spacing
        return radius

    # Optional recomputation of existing zero samples
    recomputed = 0
    if recompute and existing:
        if recompute < 0 or recompute >= len(existing):
            indices = list(range(len(existing)))
        else:
            indices = list(range(len(existing) - recompute, len(existing)))
        if indices:
            start_idx = existing[indices[0]].index
            end_idx = existing[indices[-1]].index
            print(f"Recomputing {len(indices)} zero samples (indices {start_idx}..{end_idx})")
            t_values = [existing[i].t for i in indices]
            updated = compute_samples(model, t_values)
            for offset, sample in zip(indices, updated):
                entry = existing[offset]
                global_idx = entry.index - 1
                radius_eff = effective_radius(global_idx)
                if local_count > 1 and radius_eff > 0:
                    smoothed = local_average_samples(model, sample.t, radius_eff, local_count)
                    existing[offset] = ZeroSample(entry.index, sample.t, smoothed.i_plus, smoothed.i_zero, smoothed.i_minus)
                else:
                    existing[offset] = ZeroSample(entry.index, sample.t, sample.i_plus, sample.i_zero, sample.i_minus)
            recomputed = len(indices)

    already = len(existing)
    remaining = total_target - already
    compute_count = remaining if chunk_size is None else min(remaining, max(chunk_size, 0))

    if compute_count > 0:
        start = already
        end = start + compute_count
        new_t_values = zeros_all[start:end]
        print(f"Computing {compute_count} zero-based samples (indices {start+1}..{end})")
        base_samples = compute_samples(model, new_t_values)
        zero_samples: List[ZeroSample] = []
        smoothing_possible = local_count > 1 and (local_radius > 0 or local_scale > 0)
        announced = False
        for idx, sample in enumerate(base_samples):
            index = already + idx + 1
            t_center = sample.t
            radius_eff = effective_radius(index - 1)
            if smoothing_possible and radius_eff > 0:
                if not announced:
                    print(f"Applying local averaging (base_radius={local_radius}, scale={local_scale}, count={local_count}) around each zero")
                    announced = True
                smoothed = local_average_samples(model, t_center, radius_eff, local_count)
                zero_samples.append(
                    ZeroSample(index=index, t=t_center, i_plus=smoothed.i_plus, i_zero=smoothed.i_zero, i_minus=smoothed.i_minus)
                )
            else:
                zero_samples.append(
                    ZeroSample(index=index, t=t_center, i_plus=sample.i_plus, i_zero=sample.i_zero, i_minus=sample.i_minus)
                )
        combined = existing + zero_samples
    else:
        combined = existing

    write_zero_csv(combined, path)
    simple_samples = [Sample(s.t, s.i_plus, s.i_zero, s.i_minus) for s in combined]
    stats = compute_stats(simple_samples)
    report_stats("Zero-based sampling", stats)

    for mode in weight_modes:
        try:
            weights = zero_sample_weights(combined, mode) if combined else []
        except ValueError as exc:
            print(f"Skipping weight mode '{mode}': {exc}")
            continue
        if not weights:
            continue
        label = {
            "delta": "Zero-based sampling [Δt]",
            "log": "Zero-based sampling [1/log t]",
            "delta_log": "Zero-based sampling [Δt/log t]",
        }.get(mode, f"Zero-based sampling [{mode}]")
        weighted_stats = compute_stats(simple_samples, weights=weights)
        report_stats(label, weighted_stats)

    print(f"Zero samples stored: {len(combined)} / {total_target}")
    if len(combined) < total_target:
        print("Zero dataset incomplete; rerun with --resume to extend.")
    return combined, compute_count, total_target


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=70, help="mpmath precision (decimal places)")
    parser.add_argument("--max-t", type=float, default=800.0, help="maximum |t| value for uniform sampling")
    parser.add_argument("--num-uniform", type=int, default=300, help="target number of uniform samples")
    parser.add_argument("--uniform-chunk", type=int, default=None, help="number of new uniform samples to compute this run")
    parser.add_argument("--num-zeros", type=int, default=200, help="target number of zero-based samples")
    parser.add_argument("--zero-chunk", type=int, default=None, help="number of new zero-based samples to compute this run")
    parser.add_argument(
        "--zero-data-path",
        type=Path,
        default=ROOT / "zero.data",
        help="path to precomputed zero imaginary parts (leave unset to compute with mpmath)",
    )
    parser.add_argument(
        "--uniform-recompute",
        type=str,
        default=None,
        help="recompute this many tail uniform samples (use 'all' for full dataset)",
    )
    parser.add_argument(
        "--zero-recompute",
        type=str,
        default=None,
        help="recompute this many tail zero samples (use 'all' for full dataset)",
    )
    parser.add_argument(
        "--zero-weight-modes",
        type=str,
        default="delta",
        help="comma-separated zero weighting modes (delta, log, delta_log)",
    )
    parser.add_argument(
        "--zero-local-radius",
        type=float,
        default=0.0,
        help="micro-grid radius around each zero (0 disables smoothing)",
    )
    parser.add_argument(
        "--zero-local-scale",
        type=float,
        default=0.0,
        help="additional radius multiplier relative to local zero spacing",
    )
    parser.add_argument(
        "--zero-local-count",
        type=int,
        default=1,
        help="number of samples per zero when smoothing (>1 enables)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("data/critical_line_limit"),
        help="directory where CSV results will be written",
    )
    parser.add_argument("--resume", action="store_true", help="append to existing datasets instead of recomputing from scratch")

    args = parser.parse_args()

    uniform_recompute = parse_recompute_arg(args.uniform_recompute)
    zero_recompute = parse_recompute_arg(args.zero_recompute)
    zero_weight_modes = parse_weight_modes(args.zero_weight_modes)
    zero_local_scale = args.zero_local_scale

    mp.mp.dps = args.precision
    model = UnifiedInfoDefinitions(args.precision)

    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    build_uniform_dataset(
        model,
        args.max_t,
        args.num_uniform,
        output_dir,
        resume=args.resume,
        chunk_size=args.uniform_chunk,
        recompute=uniform_recompute,
    )

    print()

    build_zero_dataset(
        model,
        args.num_zeros,
        output_dir,
        args.zero_data_path,
        resume=args.resume,
        chunk_size=args.zero_chunk,
        recompute=zero_recompute,
        weight_modes=zero_weight_modes,
        local_radius=args.zero_local_radius,
        local_scale=zero_local_scale,
        local_count=args.zero_local_count,
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
