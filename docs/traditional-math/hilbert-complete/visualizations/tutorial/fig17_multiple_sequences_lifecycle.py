#!/usr/bin/env python3
"""
Figure 17: Multiple Observer Sequences Parallel Lifecycle
Show how multiple finite sequences exist simultaneously in mother space
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Rectangle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 10

def generate_figure_17():
    """Generate single figure: Multiple Sequences Lifecycle"""
    
    fig = plt.figure(figsize=(16, 10))
    ax = fig.add_subplot(111)
    
    # Universal timeline
    timeline_length = 60
    ax.set_xlim(0, timeline_length)
    ax.set_ylim(0, 12)
    
    # Central core timeline (always present)
    ax.barh(0.5, timeline_length, height=1, color='gold', alpha=0.6, 
           edgecolor='black', linewidth=2, label='Eternal Core')
    ax.text(timeline_length/2, 1, 'INVARIANT CORE (Always Present)', 
           ha='center', va='center', fontsize=12, weight='bold')
    
    # Multiple observer sequences with realistic parameters
    observer_sequences = [
        {'start': 5, 'length': 18, 'y_pos': 3, 'color': 'red', 'name': 'Observer A (φ-dominant)', 'mode_mix': [0.6, 0.3, 0.1]},
        {'start': 0, 'length': 25, 'y_pos': 4.5, 'color': 'green', 'name': 'Observer B (e-dominant)', 'mode_mix': [0.2, 0.7, 0.1]},
        {'start': 12, 'length': 15, 'y_pos': 6, 'color': 'purple', 'name': 'Observer C (π-dominant)', 'mode_mix': [0.1, 0.2, 0.7]},
        {'start': 20, 'length': 22, 'y_pos': 7.5, 'color': 'orange', 'name': 'Observer D (mixed)', 'mode_mix': [0.4, 0.3, 0.3]},
        {'start': 8, 'length': 12, 'y_pos': 9, 'color': 'cyan', 'name': 'Observer E (φ-e mix)', 'mode_mix': [0.5, 0.5, 0.0]},
        {'start': 35, 'length': 20, 'y_pos': 10.5, 'color': 'magenta', 'name': 'Observer F (e-π mix)', 'mode_mix': [0.0, 0.6, 0.4]}
    ]
    
    for seq in observer_sequences:
        start = seq['start']
        length = seq['length']
        end = start + length
        y_pos = seq['y_pos']
        color = seq['color']
        
        # Main sequence bar
        ax.barh(y_pos, length, left=start, height=0.8, color=color, alpha=0.7,
               edgecolor='black', linewidth=1)
        
        # Show mode composition within sequence
        phi_portion = length * seq['mode_mix'][0]
        e_portion = length * seq['mode_mix'][1]
        pi_portion = length * seq['mode_mix'][2]
        
        # φ portion
        if phi_portion > 0:
            ax.barh(y_pos, phi_portion, left=start, height=0.8, color='gold', alpha=0.8)
        
        # e portion  
        if e_portion > 0:
            ax.barh(y_pos, e_portion, left=start + phi_portion, height=0.8, 
                   color='lightgreen', alpha=0.8)
        
        # π portion
        if pi_portion > 0:
            ax.barh(y_pos, pi_portion, left=start + phi_portion + e_portion, 
                   height=0.8, color='lavender', alpha=0.8)
        
        # Birth marker
        ax.plot(start, y_pos, 'o', color=color, markersize=12, 
               markeredgecolor='green', markeredgewidth=2)
        
        # Death marker
        ax.plot(end, y_pos, 'X', color=color, markersize=15,
               markeredgecolor='red', markeredgewidth=3)
        
        # Sequence label
        ax.text(end + 1, y_pos, seq['name'], ha='left', va='center',
               fontsize=9, weight='bold', color=color)
        
        # Length annotation
        ax.text(start + length/2, y_pos - 0.5, f'{length}', ha='center', va='center',
               fontsize=9, weight='bold')
    
    # Mark overlapping periods
    overlap_regions = [
        (12, 23),  # Multiple sequences active
        (20, 27),  # Peak overlap period
        (35, 42)   # Later overlap
    ]
    
    for start_overlap, end_overlap in overlap_regions:
        overlap_rect = Rectangle((start_overlap, 2.5), end_overlap - start_overlap, 6.5,
                               fill=True, color='yellow', alpha=0.2, linewidth=2,
                               edgecolor='orange')
        ax.add_patch(overlap_rect)
    
    # Timeline markers
    for t in [0, 15, 30, 45, 60]:
        ax.axvline(x=t, color='gray', linestyle=':', alpha=0.5)
        ax.text(t, 11.5, f'T={t}', ha='center', va='center', fontsize=9)
    
    ax.set_xlabel('Universal Time')
    ax.set_ylabel('Observer Sequences') 
    ax.set_title('Multiple Observer Sequences: Parallel Finite Lifespans in Infinite Timeline\nOverlap periods show simultaneous active sequences',
                fontsize=14, weight='bold', pad=20)
    ax.grid(axis='x', alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig17_multiple_sequences_lifecycle.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 17 generated successfully")

if __name__ == "__main__":
    generate_figure_17()