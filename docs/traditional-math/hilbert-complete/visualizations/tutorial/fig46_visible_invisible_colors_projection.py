#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, ConnectionPatch
import sys
import os

def create_visible_invisible_projection():
    """Visible and invisible colors projection essence visualization"""
    
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(18, 8))
    
    # Left panel: Infinite dimensional color space (invisible)
    ax1.set_xlim(-5, 5)
    ax1.set_ylim(-5, 5)
    ax1.set_aspect('equal')
    
    # Central white point in infinite space
    infinite_center = plt.Circle((0, 0), 0.3, color='white', ec='black', linewidth=3, zorder=20)
    ax1.add_patch(infinite_center)
    
    # Show infinite "invisible" operations with abstract colors
    n_invisible = 24
    invisible_operations = []
    
    for i in range(n_invisible):
        angle = 2 * np.pi * i / n_invisible
        radius = 3.5 + 0.8 * np.sin(3 * angle)  # Variable radius
        
        # Create "invisible" colors (grayscale gradients, representing unseen spectrum)
        if i < 8:
            color = (0.8, 0.8, 0.8)  # Light gray - "infrared" analogy
        elif i < 16:
            color = (0.5, 0.5, 0.5)  # Medium gray - "X-ray" analogy  
        else:
            color = (0.3, 0.3, 0.3)  # Dark gray - "gamma ray" analogy
        
        end_x = radius * np.cos(angle)
        end_y = radius * np.sin(angle)
        
        # Draw invisible operation line
        ax1.plot([0, end_x], [0, end_y], color=color, linewidth=2, alpha=0.6, zorder=10)
        
        # Invisible operation point
        invisible_point = plt.Circle((end_x, end_y), 0.1, color=color, ec='black', 
                                   linewidth=1, alpha=0.7, zorder=15)
        ax1.add_patch(invisible_point)
        
        invisible_operations.append({'x': end_x, 'y': end_y, 'color': color})
    
    ax1.set_title('Infinite Dimensional\nColor Space', fontsize=14, weight='bold')
    ax1.text(0, -4.5, '∞ Invisible Operations\n(Beyond Human Perception)', 
            fontsize=12, ha='center', va='center', 
            bbox=dict(boxstyle='round,pad=0.3', facecolor='lightgray', alpha=0.8))
    ax1.axis('off')
    
    # Middle panel: Projection operator P
    ax2.set_xlim(-2, 2)
    ax2.set_ylim(-3, 3)
    ax2.set_aspect('equal')
    
    # Projection operator visualization
    proj_box = FancyBboxPatch((-1.5, -1), 3, 2, boxstyle="round,pad=0.1", 
                             facecolor='yellow', edgecolor='black', linewidth=2, alpha=0.8)
    ax2.add_patch(proj_box)
    
    ax2.text(0, 0, 'P\n\nProjection\nOperator', fontsize=16, weight='bold', 
            ha='center', va='center')
    
    # Mathematical formula
    ax2.text(0, -2.5, 'P: ℋ^(∞) → ℋ^(finite)\n\nObserver Limitation\nCognitive Boundary', 
            fontsize=10, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='lightyellow', alpha=0.9))
    
    ax2.set_title('Observer Projection\nOperator', fontsize=14, weight='bold')
    ax2.axis('off')
    
    # Right panel: Visible color space (projected)
    ax3.set_xlim(-5, 5)
    ax3.set_ylim(-5, 5)
    ax3.set_aspect('equal')
    
    # Central white point in visible space
    visible_center = plt.Circle((0, 0), 0.3, color='white', ec='black', linewidth=3, zorder=20)
    ax3.add_patch(visible_center)
    
    # Visible operations (what we can perceive)
    visible_ops = [
        {'name': 'φ', 'color': (1.0, 0.0, 0.0), 'angle': 0},
        {'name': 'e', 'color': (0.0, 1.0, 0.0), 'angle': 60},
        {'name': 'π', 'color': (0.0, 0.0, 1.0), 'angle': 120},
        {'name': 'ζ', 'color': (0.5, 0.0, 1.0), 'angle': 180},
        {'name': 'τ', 'color': (1.0, 0.5, 0.0), 'angle': 240},
        {'name': 'γ', 'color': (0.0, 1.0, 1.0), 'angle': 300}
    ]
    
    for op in visible_ops:
        angle_rad = np.radians(op['angle'])
        end_x = 3.5 * np.cos(angle_rad)
        end_y = 3.5 * np.sin(angle_rad)
        
        # Visible operation line (bright and clear)
        ax3.plot([0, end_x], [0, end_y], color=op['color'], linewidth=3, alpha=0.9, zorder=10)
        
        # Visible operation point
        visible_point = plt.Circle((end_x, end_y), 0.15, color=op['color'], 
                                 ec='black', linewidth=2, alpha=0.9, zorder=15)
        ax3.add_patch(visible_point)
        
        # Operation label
        label_x = 4.2 * np.cos(angle_rad)
        label_y = 4.2 * np.sin(angle_rad)
        ax3.text(label_x, label_y, op['name'], fontsize=12, weight='bold', 
                ha='center', va='center', color='white',
                bbox=dict(boxstyle='round,pad=0.2', facecolor=op['color'], alpha=0.9))
    
    ax3.set_title('Visible Color Space\n(Human Perception)', fontsize=14, weight='bold')
    ax3.text(0, -4.5, 'Limited Visible Operations\n(Projected Subset)', 
            fontsize=12, ha='center', va='center',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='lightblue', alpha=0.8))
    ax3.axis('off')
    
    # Draw projection arrows
    arrow1 = ConnectionPatch((2, 0), (-2, 0), "data", "data", 
                            axesA=ax1, axesB=ax2, color="red", linewidth=3, 
                            arrowstyle="->", alpha=0.7)
    fig.add_artist(arrow1)
    
    arrow2 = ConnectionPatch((2, 0), (-2, 0), "data", "data", 
                            axesA=ax2, axesB=ax3, color="red", linewidth=3, 
                            arrowstyle="->", alpha=0.7)
    fig.add_artist(arrow2)
    
    # Overall title and explanation
    fig.suptitle('Color Projection: From Infinite to Finite Dimensions', 
                fontsize=18, weight='bold', y=0.95)
    
    # Bottom explanation
    explanation = ('Projection Reality: Our perceived colors (φ,e,π,ζ,τ,γ...) are only the visible subset of infinite mathematical operations.\n'
                  'The complete color universe contains unlimited "invisible" operations beyond human perception,\n'
                  'but each visible color holographically encodes the complete infinite information.')
    fig.text(0.5, 0.02, explanation, ha='center', va='bottom', fontsize=12,
            bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow', alpha=0.9))
    
    plt.tight_layout()
    plt.subplots_adjust(bottom=0.15, top=0.85)
    
    return fig

if __name__ == "__main__":
    fig = create_visible_invisible_projection()
    plt.tight_layout()
    plt.savefig('fig46_visible_invisible_colors_projection.png', dpi=300, bbox_inches='tight')
    plt.show()