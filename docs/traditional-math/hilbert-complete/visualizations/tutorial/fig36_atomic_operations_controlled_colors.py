#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_atomic_operations_control():
    """Demonstrate atomic π,e,φ operations preventing arbitrary color changes"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Panel 1: φ operation (Fibonacci growth) - Red spectrum only
    ax1.set_xlim(-1, 6)
    ax1.set_ylim(-1, 4)
    ax1.set_aspect('equal')
    
    # White starting point
    start_point = plt.Circle((0, 2), 0.2, color='white', ec='black', linewidth=2)
    ax1.add_patch(start_point)
    
    # φ operation sequence
    fib_seq = recursive_math.fibonacci_sequence(5)
    x_positions = np.linspace(1, 5, 5)
    
    for i, (x, fib) in enumerate(zip(x_positions, fib_seq)):
        # End point (still white)
        end_point = plt.Circle((x, 2), 0.15, color='white', ec='black', linewidth=2)
        ax1.add_patch(end_point)
        
        # Red line segment (φ operation)
        red_intensity = min(0.9, fib / max(fib_seq))
        prev_x = x_positions[i-1] if i > 0 else 0
        ax1.plot([prev_x, x], [2, 2], color=(red_intensity, 0, 0), linewidth=4)
        
        # Operation label
        ax1.text(x-0.5, 2.5, f'φ{i+1}', fontsize=10, ha='center', va='center',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='pink', alpha=0.7))
    
    ax1.set_title('φ Operations: Only Red Spectrum Allowed', fontsize=12, weight='bold')
    ax1.text(2.5, 0.5, 'Fibonacci: [0,1,1,2,3,5] → Red Gradient', ha='center', va='center')
    ax1.axis('off')
    
    # Panel 2: e operation (Factorial decay) - Green spectrum only  
    ax2.set_xlim(-1, 6)
    ax2.set_ylim(-1, 4)
    ax2.set_aspect('equal')
    
    # White starting point
    start_point = plt.Circle((0, 2), 0.2, color='white', ec='black', linewidth=2)
    ax2.add_patch(start_point)
    
    # e operation sequence
    fact_seq = recursive_math.factorial_sequence(5)
    
    for i, (x, fact) in enumerate(zip(x_positions, fact_seq)):
        # End point (still white)
        end_point = plt.Circle((x, 2), 0.15, color='white', ec='black', linewidth=2)
        ax2.add_patch(end_point)
        
        # Green line segment (e operation)
        green_intensity = min(0.9, fact * 10)  # Scale for visibility
        prev_x = x_positions[i-1] if i > 0 else 0
        ax2.plot([prev_x, x], [2, 2], color=(0, green_intensity, 0), linewidth=4)
        
        # Operation label
        ax2.text(x-0.5, 2.5, f'e{i+1}', fontsize=10, ha='center', va='center',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='lightgreen', alpha=0.7))
    
    ax2.set_title('e Operations: Only Green Spectrum Allowed', fontsize=12, weight='bold')
    ax2.text(2.5, 0.5, 'Factorial: [1,1,1/2,1/6,1/24] → Green Gradient', ha='center', va='center')
    ax2.axis('off')
    
    # Panel 3: π operation (Leibniz oscillation) - Blue spectrum only
    ax3.set_xlim(-1, 6)
    ax3.set_ylim(-1, 4)
    ax3.set_aspect('equal')
    
    # White starting point
    start_point = plt.Circle((0, 2), 0.2, color='white', ec='black', linewidth=2)
    ax3.add_patch(start_point)
    
    # π operation sequence
    leibniz_seq = recursive_math.leibniz_sequence(5)
    
    for i, (x, leibniz) in enumerate(zip(x_positions, leibniz_seq)):
        # End point (still white)
        end_point = plt.Circle((x, 2), 0.15, color='white', ec='black', linewidth=2)
        ax3.add_patch(end_point)
        
        # Blue line segment (π operation)
        blue_intensity = min(0.9, abs(leibniz) * 5)  # Scale for visibility
        prev_x = x_positions[i-1] if i > 0 else 0
        ax3.plot([prev_x, x], [2, 2], color=(0, 0, blue_intensity), linewidth=4)
        
        # Operation label
        ax3.text(x-0.5, 2.5, f'π{i+1}', fontsize=10, ha='center', va='center',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='lightblue', alpha=0.7))
    
    ax3.set_title('π Operations: Only Blue Spectrum Allowed', fontsize=12, weight='bold')
    ax3.text(2.5, 0.5, 'Leibniz: [1,-1/3,1/5,-1/7,1/9] → Blue Gradient', ha='center', va='center')
    ax3.axis('off')
    
    # Panel 4: Forbidden arbitrary color changes
    ax4.set_xlim(-1, 6)
    ax4.set_ylim(-1, 4)
    ax4.set_aspect('equal')
    
    # White starting point
    start_point = plt.Circle((0, 2), 0.2, color='white', ec='black', linewidth=2)
    ax4.add_patch(start_point)
    
    # Show forbidden arbitrary color transition
    forbidden_x = [1, 2, 3, 4]
    forbidden_colors = [(1, 0.5, 0), (0.5, 1, 0.5), (0.8, 0.2, 0.9), (0.2, 0.8, 0.6)]
    
    for i, (x, color) in enumerate(zip(forbidden_x, forbidden_colors)):
        # Forbidden colored line (with X mark)
        if i > 0:
            prev_x = forbidden_x[i-1]
            ax4.plot([prev_x, x], [2, 2], color=color, linewidth=4, alpha=0.3)
            
            # Red X mark indicating forbidden
            mid_x = (prev_x + x) / 2
            ax4.plot([mid_x-0.2, mid_x+0.2], [1.8, 2.2], 'red', linewidth=3)
            ax4.plot([mid_x-0.2, mid_x+0.2], [2.2, 1.8], 'red', linewidth=3)
        
        # Points remain white
        point = plt.Circle((x, 2), 0.15, color='white', ec='black', linewidth=2)
        ax4.add_patch(point)
    
    ax4.set_title('Forbidden: Arbitrary Color Changes', fontsize=12, weight='bold', color='red')
    ax4.text(2.5, 0.5, 'Only φ,e,π Operations Allowed\nNo Random Colors', 
            ha='center', va='center', color='red', weight='bold')
    ax4.axis('off')
    
    plt.suptitle('Atomic Operations: φ,e,π Control All Color Changes', 
                fontsize=16, weight='bold', y=0.95)
    
    return fig

if __name__ == "__main__":
    fig = create_atomic_operations_control()
    plt.tight_layout()
    plt.savefig('fig36_atomic_operations_controlled_colors.png', dpi=300, bbox_inches='tight')
    plt.show()