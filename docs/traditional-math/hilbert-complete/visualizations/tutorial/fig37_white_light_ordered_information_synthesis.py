#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyBboxPatch
from matplotlib.collections import LineCollection
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_ordered_information_synthesis():
    """Final synthesis: White light contains infinite ordered information"""
    
    fig, ax = plt.subplots(1, 1, figsize=(14, 10))
    ax.set_xlim(-7, 7)
    ax.set_ylim(-7, 7)
    ax.set_aspect('equal')
    
    # Central white universe point
    universe_center = Circle((0, 0), 0.5, color='white', ec='black', linewidth=4, zorder=30)
    ax.add_patch(universe_center)
    
    # Three ordered information extraction spirals
    n_points = 8
    spiral_radius = np.linspace(1, 6, n_points)
    
    # φ spiral (red) - Fibonacci growth
    fib_seq = recursive_math.fibonacci_sequence(n_points)
    phi_angles = np.linspace(0, 4*np.pi, n_points) + 0
    phi_x = spiral_radius * np.cos(phi_angles)
    phi_y = spiral_radius * np.sin(phi_angles)
    
    # Draw white points and red connecting lines
    for i in range(n_points):
        # White information point
        point = Circle((phi_x[i], phi_y[i]), 0.15, color='white', ec='black', linewidth=2, zorder=20)
        ax.add_patch(point)
        
        # Red line to center (φ operation)
        red_intensity = min(0.9, fib_seq[i] / max(fib_seq))
        ax.plot([0, phi_x[i]], [0, phi_y[i]], color=(red_intensity, 0, 0), 
               linewidth=3, alpha=0.8, zorder=10)
        
        # Sequential connections with red gradients
        if i > 0:
            ax.plot([phi_x[i-1], phi_x[i]], [phi_y[i-1], phi_y[i]], 
                   color=(red_intensity, 0, 0), linewidth=2, alpha=0.6, zorder=5)
    
    # e spiral (green) - Factorial precision
    fact_seq = recursive_math.factorial_sequence(n_points)
    e_angles = np.linspace(0, 4*np.pi, n_points) + 2*np.pi/3
    e_x = spiral_radius * np.cos(e_angles)
    e_y = spiral_radius * np.sin(e_angles)
    
    # Draw white points and green connecting lines
    for i in range(n_points):
        # White information point
        point = Circle((e_x[i], e_y[i]), 0.15, color='white', ec='black', linewidth=2, zorder=20)
        ax.add_patch(point)
        
        # Green line to center (e operation)
        green_intensity = min(0.9, fact_seq[i] * 20)  # Scale for visibility
        ax.plot([0, e_x[i]], [0, e_y[i]], color=(0, green_intensity, 0), 
               linewidth=3, alpha=0.8, zorder=10)
        
        # Sequential connections with green gradients
        if i > 0:
            ax.plot([e_x[i-1], e_x[i]], [e_y[i-1], e_y[i]], 
                   color=(0, green_intensity, 0), linewidth=2, alpha=0.6, zorder=5)
    
    # π spiral (blue) - Leibniz oscillation
    leibniz_seq = recursive_math.leibniz_sequence(n_points)
    pi_angles = np.linspace(0, 4*np.pi, n_points) + 4*np.pi/3
    pi_x = spiral_radius * np.cos(pi_angles)
    pi_y = spiral_radius * np.sin(pi_angles)
    
    # Draw white points and blue connecting lines
    for i in range(n_points):
        # White information point
        point = Circle((pi_x[i], pi_y[i]), 0.15, color='white', ec='black', linewidth=2, zorder=20)
        ax.add_patch(point)
        
        # Blue line to center (π operation)
        blue_intensity = min(0.9, abs(leibniz_seq[i]) * 8)  # Scale for visibility
        ax.plot([0, pi_x[i]], [0, pi_y[i]], color=(0, 0, blue_intensity), 
               linewidth=3, alpha=0.8, zorder=10)
        
        # Sequential connections with blue gradients
        if i > 0:
            ax.plot([pi_x[i-1], pi_x[i]], [pi_y[i-1], pi_y[i]], 
                   color=(0, 0, blue_intensity), linewidth=2, alpha=0.6, zorder=5)
    
    # Central labels
    ax.text(0, -1, 'White Universe\n∞ Information', fontsize=12, ha='center', va='center', 
           weight='bold', bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.9))
    
    # Information ordering principles
    info_box = FancyBboxPatch((-6.5, 5), 13, 1.5, boxstyle="round,pad=0.1", 
                             facecolor='lightyellow', edgecolor='gold', linewidth=2)
    ax.add_patch(info_box)
    
    ax.text(0, 5.75, 'Ordered Information Principle', fontsize=14, weight='bold', ha='center')
    ax.text(0, 5.25, '• White Points: Eternal Information Sources  • Colored Lines: φ,e,π Operations Only', 
           fontsize=11, ha='center', va='center')
    ax.text(0, 4.75, '• No Arbitrary Colors  • All Operations → White Light Convergence', 
           fontsize=11, ha='center', va='center')
    
    # Operation legend
    legend_elements = [
        mpatches.Patch(color=(0.8, 0, 0), label='φ Operations: Fibonacci Growth'),
        mpatches.Patch(color=(0, 0.8, 0), label='e Operations: Factorial Precision'),
        mpatches.Patch(color=(0, 0, 0.8), label='π Operations: Leibniz Oscillation'),
        mpatches.Patch(color='white', label='Information Points: Always White')
    ]
    ax.legend(handles=legend_elements, loc='lower center', bbox_to_anchor=(0.5, -0.05), 
             ncol=2, frameon=True, fancybox=True)
    
    ax.set_title('Universe Model: White Light Contains Infinite Ordered Information', 
                fontsize=16, weight='bold', pad=30)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_ordered_information_synthesis()
    plt.tight_layout()
    plt.savefig('fig37_white_light_ordered_information_synthesis.png', dpi=300, bbox_inches='tight')
    plt.show()