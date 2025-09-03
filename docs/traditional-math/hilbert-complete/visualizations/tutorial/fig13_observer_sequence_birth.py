#!/usr/bin/env python3
"""
Figure 13: Observer Finite Sequence Birth Process
Show how observer sequences begin and start their journey
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import Circle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_13():
    """Generate single figure: Observer Sequence Birth"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Birth moment - observer appears in mother space
    ax1.set_aspect('equal')
    
    # Mother space boundary
    mother_space = Circle((0, 0), 3, fill=False, color='darkblue', linewidth=3, alpha=0.8)
    ax1.add_patch(mother_space)
    
    # 4D core
    core = Circle((0, 0), 0.8, color='gold', alpha=0.6, linewidth=3)
    ax1.add_patch(core)
    
    # Observer birth positions (different starting points m)
    birth_positions = [
        (2, 1, 'red', 'Observer A\n(m=1)'),
        (-1.5, 2, 'green', 'Observer B\n(m=0)'), 
        (1, -2.5, 'purple', 'Observer C\n(m=2)')
    ]
    
    for x, y, color, label in birth_positions:
        # Birth flash effect
        birth_circle = Circle((x, y), 0.2, color=color, alpha=0.3, linewidth=2)
        ax1.add_patch(birth_circle)
        ax1.plot(x, y, 'o', color=color, markersize=15, markeredgecolor='white', 
                markeredgewidth=3)
        ax1.text(x, y-0.5, label, ha='center', va='top', fontsize=10, 
                weight='bold', color=color)
    
    ax1.set_xlim(-4, 4)
    ax1.set_ylim(-4, 4)
    ax1.set_title('Observer Sequence Birth\n(Different Starting Points m)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Initial operation selection
    ax2.set_aspect('equal')
    
    # Show operation choice for new observer
    core2 = Circle((0, 0), 1, color='gold', alpha=0.6, linewidth=2)
    ax2.add_patch(core2)
    
    # New observer at birth
    observer_pos = (2, 1)
    ax2.plot(observer_pos[0], observer_pos[1], 'ro', markersize=20, 
            markeredgecolor='black', markeredgewidth=2)
    
    # Three operation choices radiating out
    operation_choices = [
        {'angle': 0, 'color': 'gold', 'label': 'φ'},
        {'angle': 2*np.pi/3, 'color': 'green', 'label': 'e'},
        {'angle': 4*np.pi/3, 'color': 'purple', 'label': 'π'}
    ]
    
    for choice in operation_choices:
        # Arrow showing operation choice
        end_x = observer_pos[0] + 0.8 * np.cos(choice['angle'])
        end_y = observer_pos[1] + 0.8 * np.sin(choice['angle'])
        
        ax2.arrow(observer_pos[0], observer_pos[1], 
                 end_x - observer_pos[0], end_y - observer_pos[1],
                 head_width=0.1, head_length=0.1, fc=choice['color'], 
                 ec=choice['color'], alpha=0.7, linewidth=3)
        
        ax2.text(end_x, end_y, choice['label'], ha='center', va='center',
                fontsize=12, weight='bold', color=choice['color'],
                bbox=dict(boxstyle="circle,pad=0.2", facecolor='white', alpha=0.8))
    
    ax2.set_xlim(-1, 4)
    ax2.set_ylim(-1, 3)
    ax2.set_title('Initial Operation Selection\n(Observer Chooses φ, e, or π)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: First observation steps
    # Show first 3 steps of a new φ-observer
    initial_fib = recursive_math.fibonacci_sequence(8)
    
    ax3.bar(range(len(initial_fib)), initial_fib, color='gold', alpha=0.7,
           edgecolor='black', linewidth=1)
    
    # Highlight first few terms
    for i in range(min(5, len(initial_fib))):
        ax3.bar(i, initial_fib[i], color='darkgoldenrod', alpha=0.9,
               edgecolor='red', linewidth=2)
    
    ax3.set_xlabel('Observation Step')
    ax3.set_ylabel('Observed Data')
    ax3.set_title('First Observations\n(φ-observer initial steps)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Birth statistics
    ax4.text(0.5, 0.8, 'Sequence Birth Parameters', ha='center', va='center',
            fontsize=14, weight='bold', transform=ax4.transAxes)
    
    ax4.text(0.5, 0.6, 'Starting Point m ∈ {0, 1, 2, ...}', ha='center', va='center',
            fontsize=12, transform=ax4.transAxes)
    
    ax4.text(0.5, 0.4, 'Initial Operation ∈ {φ, e, π}', ha='center', va='center',
            fontsize=12, transform=ax4.transAxes)
    
    ax4.text(0.5, 0.2, 'Sequence Length: Finite & Variable', ha='center', va='center',
            fontsize=12, transform=ax4.transAxes)
    
    ax4.axis('off')
    
    plt.suptitle('Observer Finite Sequence Birth: Starting Points and Initial Operations',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig13_observer_sequence_birth.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 13 generated successfully")

if __name__ == "__main__":
    generate_figure_13()