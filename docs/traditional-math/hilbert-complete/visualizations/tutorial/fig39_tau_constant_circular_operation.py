#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_tau_circular_operation():
    """τ constant circular geometric operation visualization"""
    
    fig, ax = plt.subplots(1, 1, figsize=(12, 10))
    ax.set_xlim(-7, 7)
    ax.set_ylim(-7, 7)
    ax.set_aspect('equal')
    
    # Central white universe point
    center = plt.Circle((0, 0), 0.3, color='white', ec='black', linewidth=3, zorder=20)
    ax.add_patch(center)
    
    # τ = 2π circular path
    n_points = 12
    radius = 5
    angles = np.linspace(0, 2*np.pi, n_points, endpoint=False)
    
    # Create circular observer path with white points
    circle_x = radius * np.cos(angles)
    circle_y = radius * np.sin(angles)
    
    # Draw the circular path
    circle_path = plt.Circle((0, 0), radius, fill=False, color='orange', 
                            linewidth=3, alpha=0.6, zorder=5)
    ax.add_patch(circle_path)
    
    # Place white information points along the circle
    for i in range(n_points):
        white_point = plt.Circle((circle_x[i], circle_y[i]), 0.2, 
                               color='white', ec='black', linewidth=2, zorder=15)
        ax.add_patch(white_point)
        
        # Connect to center with orange τ lines
        ax.plot([0, circle_x[i]], [0, circle_y[i]], 
               color='orange', linewidth=2, alpha=0.7, zorder=10)
        
        # Point labels
        label_angle = angles[i]
        label_x = (radius + 0.8) * np.cos(label_angle)
        label_y = (radius + 0.8) * np.sin(label_angle)
        ax.text(label_x, label_y, f'P{i+1}', fontsize=10, ha='center', va='center',
               bbox=dict(boxstyle='circle,pad=0.1', facecolor='orange', alpha=0.7))
    
    # Draw τ operation segments between adjacent points
    for i in range(n_points):
        next_i = (i + 1) % n_points
        
        # τ operation line between adjacent points
        tau_intensity = 0.8
        ax.plot([circle_x[i], circle_x[next_i]], [circle_y[i], circle_y[next_i]], 
               color=(1.0, 0.5, 0.0, tau_intensity), linewidth=3, zorder=12)
        
        # τ operation label
        mid_x = (circle_x[i] + circle_x[next_i]) / 2
        mid_y = (circle_y[i] + circle_y[next_i]) / 2
        ax.text(mid_x, mid_y, 'τ', fontsize=12, weight='bold', 
               ha='center', va='center', color='darkorange')
    
    # Mathematical annotation
    ax.text(0, 6.5, 'τ = 2π Operation', fontsize=16, weight='bold', ha='center', va='center')
    ax.text(0, -6.5, 'Complete Circular Geometry\nCyclic Information Encoding', 
           fontsize=12, ha='center', va='center')
    
    # Geometric properties text box
    props_text = 'τ Properties:\n• Complete circle = τ radians\n• Cyclic symmetry\n• Periodic encoding'
    ax.text(-6.5, 5, props_text, fontsize=10, ha='left', va='top',
           bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow', alpha=0.9))
    
    # Mathematical formula
    ax.text(6, -5, 'τ = 2π ≈ 6.283\nCircular Information\nGeometric Encoding', 
           fontsize=11, ha='center', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='orange', alpha=0.3))
    
    ax.set_title('τ Constant: Circular Geometric Operation for Complete Cycle Encoding', 
                fontsize=14, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_tau_circular_operation()
    plt.tight_layout()
    plt.savefig('fig39_tau_constant_circular_operation.png', dpi=300, bbox_inches='tight')
    plt.show()