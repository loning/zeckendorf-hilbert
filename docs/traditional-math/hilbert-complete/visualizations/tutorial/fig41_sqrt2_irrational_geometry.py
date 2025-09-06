#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

def create_sqrt2_irrational_geometry():
    """√2 constant irrational number geometric structure visualization"""
    
    fig, ax = plt.subplots(1, 1, figsize=(12, 10))
    ax.set_xlim(-7, 7)
    ax.set_ylim(-7, 7)
    ax.set_aspect('equal')
    
    # Central white universe point
    center = plt.Circle((0, 0), 0.3, color='white', ec='black', linewidth=3, zorder=20)
    ax.add_patch(center)
    
    # √2 geometric path: diagonal progression
    sqrt2 = np.sqrt(2)
    n_points = 10
    
    # Create diagonal pattern based on √2 ratio
    distances = [sqrt2**i for i in range(n_points)]
    angles = [i * 45 for i in range(n_points)]  # 45-degree increments (√2 related)
    
    # Convert to coordinates, scaling to fit
    max_distance = 6
    scale_factor = max_distance / max(distances)
    
    obs_x = [scale_factor * distances[i] * np.cos(np.radians(angles[i])) for i in range(n_points)]
    obs_y = [scale_factor * distances[i] * np.sin(np.radians(angles[i])) for i in range(n_points)]
    
    # Draw white information points
    for i in range(n_points):
        white_point = plt.Circle((obs_x[i], obs_y[i]), 0.15, 
                               color='white', ec='black', linewidth=2, zorder=15)
        ax.add_patch(white_point)
    
    # Draw √2 operation lines between consecutive points
    for i in range(n_points-1):
        # Pink √2 line segment with intensity based on √2 power
        intensity = min(0.9, 0.3 + 0.1 * i)
        ax.plot([obs_x[i], obs_x[i+1]], [obs_y[i], obs_y[i+1]], 
               color=(1.0, 0.0, intensity), linewidth=3, alpha=0.8, zorder=10)
        
        # √2 operation label
        mid_x = (obs_x[i] + obs_x[i+1]) / 2
        mid_y = (obs_y[i] + obs_y[i+1]) / 2
        ax.text(mid_x, mid_y, '√2', fontsize=9, weight='bold', 
               ha='center', va='center', color='darkmagenta',
               bbox=dict(boxstyle='circle,pad=0.1', facecolor='pink', alpha=0.7))
    
    # Connect points to center with light pink lines
    for i in range(n_points):
        ax.plot([0, obs_x[i]], [0, obs_y[i]], 
               color='pink', linewidth=1, alpha=0.4, zorder=5)
    
    # Draw reference squares to show √2 diagonal relationship
    square_sizes = [1.5, 3.0, 4.5]
    for size in square_sizes:
        # Square outline
        square = plt.Rectangle((-size/2, -size/2), size, size, 
                             fill=False, ec='gray', linewidth=1, alpha=0.4)
        ax.add_patch(square)
        
        # Diagonal line
        ax.plot([-size/2, size/2], [-size/2, size/2], 
               '--', color='gray', alpha=0.4, linewidth=1)
    
    # Mathematical properties annotation
    ax.text(-6.5, 5.5, '√2 ≈ 1.4142135624', fontsize=14, weight='bold')
    ax.text(-6.5, 4.8, 'Algebraic Irrational', fontsize=12)
    
    # Mathematical definition
    definition_text = '√2 = diag/side\nof unit square\n\nIrrational:\nNon-repeating\nNon-terminating'
    ax.text(-6.5, 3.5, definition_text, fontsize=11, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='mistyrose', alpha=0.8))
    
    # Geometric sequence properties
    sequence_text = 'Geometric Sequence:\nr_n = r₀ × (√2)ⁿ\n\nDiagonal Scaling:\nEach step × √2'
    ax.text(4.5, -5, sequence_text, fontsize=10, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='lavenderblush', alpha=0.8))
    
    # Central mathematical relationship
    ax.text(0, -6.5, 'Diagonal Geometry: Square Root 2 Operations', 
           fontsize=14, weight='bold', ha='center', va='center')
    
    ax.set_title('√2 Constant: Irrational Geometric Sequence Operations', 
                fontsize=14, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_sqrt2_irrational_geometry()
    plt.tight_layout()
    plt.savefig('fig41_sqrt2_irrational_geometry.png', dpi=300, bbox_inches='tight')
    plt.show()