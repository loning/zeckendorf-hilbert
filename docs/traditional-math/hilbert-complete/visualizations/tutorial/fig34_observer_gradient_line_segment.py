#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_observer_gradient_line():
    """Observer as colored gradient line segment with unique perspective"""
    
    fig, ax = plt.subplots(1, 1, figsize=(12, 8))
    ax.set_xlim(-1, 11)
    ax.set_ylim(-1, 6)
    ax.set_aspect('equal')
    
    # Generate observer path with 10 white points
    n_points = 10
    observer_x = np.linspace(0, 10, n_points)
    observer_y = 2 + 0.8 * np.sin(observer_x * 0.6)
    
    # Draw white points (information sources)
    for i in range(n_points):
        circle = plt.Circle((observer_x[i], observer_y[i]), 0.15, 
                          color='white', ec='black', linewidth=2, zorder=10)
        ax.add_patch(circle)
    
    # Create colored gradient line segments between points
    phi_seq = recursive_math.fibonacci_sequence(n_points-1)
    e_seq = recursive_math.factorial_sequence(n_points-1)  
    pi_seq = recursive_math.leibniz_sequence(n_points-1)
    
    # Normalize sequences for color mapping
    phi_norm = np.array(phi_seq) / max(phi_seq)
    e_norm = np.array(e_seq) / max(e_seq) if max(e_seq) > 0 else np.array(e_seq)
    pi_norm = np.array(pi_seq) / max(abs(np.array(pi_seq)))
    
    # Draw gradient line segments
    for i in range(n_points-1):
        # Line segment from point i to point i+1
        x_segment = [observer_x[i], observer_x[i+1]]
        y_segment = [observer_y[i], observer_y[i+1]]
        
        # Color based on φ,e,π operations
        red_intensity = phi_norm[i] * 0.8
        green_intensity = e_norm[i] * 0.8  
        blue_intensity = abs(pi_norm[i]) * 0.8
        
        # Create gradient effect along line
        gradient_points = 50
        x_grad = np.linspace(x_segment[0], x_segment[1], gradient_points)
        y_grad = np.linspace(y_segment[0], y_segment[1], gradient_points)
        
        # Color gradient along segment
        colors = []
        for j in range(gradient_points-1):
            t = j / (gradient_points-1)
            r = red_intensity * (1-t) + red_intensity * t
            g = green_intensity * (1-t) + green_intensity * t  
            b = blue_intensity * (1-t) + blue_intensity * t
            colors.append((r, g, b, 0.8))
        
        # Draw gradient line
        points = np.array([x_grad[:-1], y_grad[:-1]]).T.reshape(-1, 1, 2)
        segments = np.concatenate([points[:-1], points[1:]], axis=1)
        lc = LineCollection(segments, colors=colors, linewidths=3)
        ax.add_collection(lc)
        
        # Operation label
        operation_labels = ['φ', 'e', 'π'] * ((n_points-1)//3 + 1)
        mid_x = (x_segment[0] + x_segment[1]) / 2
        mid_y = (y_segment[0] + y_segment[1]) / 2 + 0.3
        ax.text(mid_x, mid_y, operation_labels[i], fontsize=10, 
               ha='center', va='center', weight='bold',
               bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8))
    
    # Observer label
    ax.text(5, 4.5, 'Observer: Colored Gradient Line Segment', 
           fontsize=14, ha='center', va='center', weight='bold')
    ax.text(5, 4, 'White Points: Information Sources\nColored Lines: φ,e,π Operations', 
           fontsize=12, ha='center', va='center')
    
    # Legend for operations
    legend_elements = [
        mpatches.Patch(color=(0.8, 0, 0), label='φ operations (red)'),
        mpatches.Patch(color=(0, 0.8, 0), label='e operations (green)'),
        mpatches.Patch(color=(0, 0, 0.8), label='π operations (blue)')
    ]
    ax.legend(handles=legend_elements, loc='lower right')
    
    ax.set_title('Observer as Gradient Line: Unique Information Extraction Perspective', 
                fontsize=14, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_observer_gradient_line()
    plt.tight_layout()
    plt.savefig('fig34_observer_gradient_line_segment.png', dpi=300, bbox_inches='tight')
    plt.show()