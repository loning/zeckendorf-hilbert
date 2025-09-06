#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_extended_color_space():
    """Extended self-similar operations showing multi-dimensional color space beyond RGB"""
    
    fig, ax = plt.subplots(1, 1, figsize=(14, 10))
    ax.set_xlim(-8, 8)
    ax.set_ylim(-8, 8)
    ax.set_aspect('equal')
    
    # Central white universe point
    universe_center = plt.Circle((0, 0), 0.4, color='white', ec='black', linewidth=4, zorder=20)
    ax.add_patch(universe_center)
    
    # Extended mathematical constants and their color mappings
    constants = {
        'φ': {'color': (1.0, 0.0, 0.0), 'angle': 0, 'name': 'Golden Ratio'},        # Red
        'e': {'color': (0.0, 1.0, 0.0), 'angle': 60, 'name': 'Natural Constant'},   # Green  
        'π': {'color': (0.0, 0.0, 1.0), 'angle': 120, 'name': 'Pi Constant'},      # Blue
        'ζ': {'color': (0.5, 0.0, 1.0), 'angle': 180, 'name': 'Zeta Function'},    # Purple
        'τ': {'color': (1.0, 0.5, 0.0), 'angle': 240, 'name': 'Tau Constant'},     # Orange
        'γ': {'color': (0.0, 1.0, 1.0), 'angle': 300, 'name': 'Euler-Mascheroni'}, # Cyan
        '√2': {'color': (1.0, 0.0, 0.5), 'angle': 45, 'name': 'Square Root 2'}     # Pink
    }
    
    # Draw extended operation lines
    for const, props in constants.items():
        angle_rad = np.radians(props['angle'])
        
        # End point for the line
        end_x = 6.5 * np.cos(angle_rad)
        end_y = 6.5 * np.sin(angle_rad)
        
        # Draw the operation line
        ax.plot([0, end_x], [0, end_y], color=props['color'], linewidth=4, alpha=0.8, zorder=10)
        
        # Draw white information point at the end
        end_point = plt.Circle((end_x, end_y), 0.25, color='white', ec='black', linewidth=2, zorder=15)
        ax.add_patch(end_point)
        
        # Label the operation
        label_x = 7.5 * np.cos(angle_rad)
        label_y = 7.5 * np.sin(angle_rad)
        ax.text(label_x, label_y, f'{const}', fontsize=14, weight='bold', 
               ha='center', va='center',
               bbox=dict(boxstyle='round,pad=0.3', facecolor=props['color'], alpha=0.7))
        
        # Add mathematical property text
        prop_x = 5.5 * np.cos(angle_rad)
        prop_y = 5.5 * np.sin(angle_rad)
        ax.text(prop_x, prop_y, props['name'], fontsize=10, ha='center', va='center',
               rotation=props['angle'] if -90 <= props['angle'] <= 90 else props['angle']-180,
               bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8))
    
    # Mathematical sequences for visualization
    n_points = 8
    
    # Show extended operation sequences along some lines
    # φ sequence (red line)
    phi_seq = recursive_math.fibonacci_sequence(n_points)
    phi_x = np.linspace(0.5, 6, n_points)
    phi_y = np.zeros(n_points)
    
    for i, fib in enumerate(phi_seq):
        intensity = min(0.9, fib / max(phi_seq))
        point = plt.Circle((phi_x[i], phi_y[i]), 0.1, 
                         color=(intensity, 0, 0), ec='black', linewidth=1, zorder=12)
        ax.add_patch(point)
    
    # e sequence (green line) 
    e_seq = recursive_math.factorial_sequence(n_points)
    e_angle = np.radians(60)
    e_x = np.linspace(0.5, 6, n_points) * np.cos(e_angle)
    e_y = np.linspace(0.5, 6, n_points) * np.sin(e_angle)
    
    for i, fact in enumerate(e_seq):
        intensity = min(0.9, fact * 20)
        point = plt.Circle((e_x[i], e_y[i]), 0.1, 
                         color=(0, intensity, 0), ec='black', linewidth=1, zorder=12)
        ax.add_patch(point)
    
    # Concentric circles showing dimensional expansion
    for radius in [2, 4, 6]:
        circle = plt.Circle((0, 0), radius, fill=False, ec='gray', 
                          linewidth=1, alpha=0.3, linestyle='--', zorder=5)
        ax.add_patch(circle)
    
    # Central label
    ax.text(0, -6.5, 'Multi-Dimensional\nColor Space', fontsize=14, weight='bold', 
           ha='center', va='center')
    ax.text(0, -7.5, 'φ,e,π,ζ,τ,γ,√2,...', fontsize=12, ha='center', va='center')
    
    # Legend for extended operations
    legend_elements = [
        mpatches.Patch(color=(1.0, 0.0, 0.0), label='φ (Golden Ratio)'),
        mpatches.Patch(color=(0.0, 1.0, 0.0), label='e (Natural Constant)'),
        mpatches.Patch(color=(0.0, 0.0, 1.0), label='π (Pi Constant)'),
        mpatches.Patch(color=(0.5, 0.0, 1.0), label='ζ (Zeta Function)'),
        mpatches.Patch(color=(1.0, 0.5, 0.0), label='τ (Tau Constant)'),
        mpatches.Patch(color=(0.0, 1.0, 1.0), label='γ (Euler-Mascheroni)'),
        mpatches.Patch(color=(1.0, 0.0, 0.5), label='√2 (Square Root 2)')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=10)
    
    ax.set_title('Extended Self-Similar Operations: Beyond RGB to Infinite Dimensions', 
                fontsize=16, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_extended_color_space()
    plt.tight_layout()
    plt.savefig('fig38_extended_multidimensional_color_space.png', dpi=300, bbox_inches='tight')
    plt.show()