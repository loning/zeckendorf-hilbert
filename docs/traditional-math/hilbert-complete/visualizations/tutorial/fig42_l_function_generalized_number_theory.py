#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

def create_l_function_number_theory():
    """L-function generalized number theory encoding visualization"""
    
    fig, ax = plt.subplots(1, 1, figsize=(14, 10))
    ax.set_xlim(-8, 8)
    ax.set_ylim(-8, 8)
    ax.set_aspect('equal')
    
    # Central white universe point
    center = plt.Circle((0, 0), 0.4, color='white', ec='black', linewidth=4, zorder=20)
    ax.add_patch(center)
    
    # Different L-functions with different character functions χ
    l_functions = [
        {'name': 'L(s,χ₁)', 'color': (0.8, 0.2, 0.8), 'start_angle': 0, 'spiral_rate': 0.3},
        {'name': 'L(s,χ₂)', 'color': (0.2, 0.8, 0.8), 'start_angle': 72, 'spiral_rate': 0.35},
        {'name': 'L(s,χ₃)', 'color': (0.8, 0.8, 0.2), 'start_angle': 144, 'spiral_rate': 0.4},
        {'name': 'L(s,χ₄)', 'color': (0.8, 0.4, 0.2), 'start_angle': 216, 'spiral_rate': 0.25},
        {'name': 'L(s,χ₅)', 'color': (0.4, 0.8, 0.4), 'start_angle': 288, 'spiral_rate': 0.45}
    ]
    
    # Draw L-function spirals
    for l_func in l_functions:
        n_points = 8
        t = np.linspace(0.5, 3, n_points)
        
        # Create spiral path for this L-function
        radius = 0.8 + l_func['spiral_rate'] * t
        angles = np.radians(l_func['start_angle']) + t * 1.5
        
        spiral_x = radius * np.cos(angles)
        spiral_y = radius * np.sin(angles)
        
        # Draw white points along the spiral
        for i in range(n_points):
            white_point = plt.Circle((spiral_x[i], spiral_y[i]), 0.12, 
                                   color='white', ec='black', linewidth=1.5, zorder=15)
            ax.add_patch(white_point)
        
        # Draw L-function operation lines between points
        for i in range(n_points-1):
            # Color intensity based on L-function character
            intensity = 0.7 + 0.2 * np.sin(i * np.pi / 4)
            color_with_alpha = (*l_func['color'], intensity)
            
            ax.plot([spiral_x[i], spiral_x[i+1]], [spiral_y[i], spiral_y[i+1]], 
                   color=l_func['color'], linewidth=2.5, alpha=intensity, zorder=10)
            
            # L operation label
            mid_x = (spiral_x[i] + spiral_x[i+1]) / 2
            mid_y = (spiral_y[i] + spiral_y[i+1]) / 2
            ax.text(mid_x, mid_y, 'L', fontsize=8, weight='bold', 
                   ha='center', va='center', color='darkviolet')
        
        # Connect spiral start to center
        ax.plot([0, spiral_x[0]], [0, spiral_y[0]], 
               color=l_func['color'], linewidth=2, alpha=0.6, zorder=8)
        
        # Function label at the outer end
        outer_x = 7 * np.cos(np.radians(l_func['start_angle']))
        outer_y = 7 * np.sin(np.radians(l_func['start_angle']))
        ax.text(outer_x, outer_y, l_func['name'], fontsize=10, weight='bold',
               ha='center', va='center',
               bbox=dict(boxstyle='round,pad=0.3', facecolor=l_func['color'], alpha=0.7))
    
    # Mathematical properties annotation
    ax.text(-7.5, 6, 'Dirichlet L-Functions', fontsize=16, weight='bold')
    ax.text(-7.5, 5.3, 'L(s,χ) = Σ χ(n)/n^s', fontsize=12)
    
    # Properties explanation
    properties_text = 'L-Function Properties:\n• Character function χ\n• Arithmetic modulation\n• Generalized zeta\n• Number theory encoding'
    ax.text(-7.5, 3.5, properties_text, fontsize=10, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='lightcyan', alpha=0.8))
    
    # Encoding explanation
    encoding_text = 'Encoding Features:\n• Multiple characters χ\n• Spiral path diversity\n• Arithmetic function coding\n• Extended prime structure'
    ax.text(5, 6, encoding_text, fontsize=10, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='lavender', alpha=0.8))
    
    # Central label
    ax.text(0, -7, 'Generalized Number Theory: L-Function Encoding Network', 
           fontsize=14, weight='bold', ha='center', va='center')
    
    # Create legend
    legend_elements = []
    for l_func in l_functions:
        legend_elements.append(mpatches.Patch(color=l_func['color'], label=l_func['name']))
    ax.legend(handles=legend_elements, loc='lower right', fontsize=9)
    
    ax.set_title('L-Functions: Generalized Number Theory Encoding Operations', 
                fontsize=14, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_l_function_number_theory()
    plt.tight_layout()
    plt.savefig('fig42_l_function_generalized_number_theory.png', dpi=300, bbox_inches='tight')
    plt.show()