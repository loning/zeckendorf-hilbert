#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

def create_observer_free_choice():
    """Observer free choice in infinite dimensional network visualization"""
    
    fig, ax = plt.subplots(1, 1, figsize=(16, 12))
    ax.set_xlim(-10, 10)
    ax.set_ylim(-10, 10)
    ax.set_aspect('equal')
    
    # Create a network of white information points
    np.random.seed(42)  # For reproducible layout
    n_points = 20
    
    # Generate points in a roughly circular pattern with some randomness
    base_angles = np.linspace(0, 2*np.pi, n_points, endpoint=False)
    base_radius = 6 + 2 * np.random.rand(n_points) - 1  # Vary radius slightly
    
    points_x = base_radius * np.cos(base_angles) + 0.5 * (np.random.rand(n_points) - 0.5)
    points_y = base_radius * np.sin(base_angles) + 0.5 * (np.random.rand(n_points) - 0.5)
    
    # Add central point
    points_x = np.insert(points_x, 0, 0)
    points_y = np.insert(points_y, 0, 0)
    
    # Draw all white information points
    for i in range(len(points_x)):
        size = 0.4 if i == 0 else 0.2  # Central point larger
        white_point = plt.Circle((points_x[i], points_y[i]), size, 
                               color='white', ec='black', linewidth=2, zorder=20)
        ax.add_patch(white_point)
        
        # Label points
        if i > 0:
            ax.text(points_x[i], points_y[i]-0.6, f'P{i}', fontsize=8, 
                   ha='center', va='center', weight='bold')
    
    # Define multiple operation types with colors
    operations = [
        {'name': 'φ', 'color': (1.0, 0.0, 0.0), 'symbol': 'φ'},
        {'name': 'e', 'color': (0.0, 1.0, 0.0), 'symbol': 'e'},
        {'name': 'π', 'color': (0.0, 0.0, 1.0), 'symbol': 'π'},
        {'name': 'ζ', 'color': (0.5, 0.0, 1.0), 'symbol': 'ζ'},
        {'name': 'τ', 'color': (1.0, 0.5, 0.0), 'symbol': 'τ'},
        {'name': 'γ', 'color': (0.0, 1.0, 1.0), 'symbol': 'γ'},
        {'name': '√2', 'color': (1.0, 0.0, 0.5), 'symbol': '√'},
        {'name': 'L', 'color': (0.8, 0.8, 0.2), 'symbol': 'L'}
    ]
    
    # Create several example observer paths showing free choice
    example_paths = [
        {'start': 0, 'sequence': [5, 12, 8, 15], 'ops': ['φ', 'π', 'ζ', 'τ']},
        {'start': 3, 'sequence': [7, 11, 16], 'ops': ['e', 'γ', '√2']},
        {'start': 9, 'sequence': [2, 14, 6], 'ops': ['L', 'φ', 'π']},
    ]
    
    # Draw example observer paths
    for path_idx, path in enumerate(example_paths):
        current_points = [path['start']] + path['sequence']
        
        for i in range(len(current_points)-1):
            start_idx = current_points[i]
            end_idx = current_points[i+1]
            
            # Get operation color
            op_name = path['ops'][i]
            op_color = next(op['color'] for op in operations if op['name'] == op_name)
            
            # Draw operation line
            ax.plot([points_x[start_idx], points_x[end_idx]], 
                   [points_y[start_idx], points_y[end_idx]], 
                   color=op_color, linewidth=3, alpha=0.8, zorder=15)
            
            # Add operation symbol
            mid_x = (points_x[start_idx] + points_x[end_idx]) / 2
            mid_y = (points_y[start_idx] + points_y[end_idx]) / 2
            ax.text(mid_x, mid_y, op_name, fontsize=10, weight='bold', 
                   ha='center', va='center', color='white',
                   bbox=dict(boxstyle='circle,pad=0.1', facecolor=op_color, alpha=0.9))
            
            # Add arrow to show direction
            dx = points_x[end_idx] - points_x[start_idx]
            dy = points_y[end_idx] - points_y[start_idx]
            length = np.sqrt(dx**2 + dy**2)
            arrow_start_x = points_x[start_idx] + 0.7 * dx
            arrow_start_y = points_y[start_idx] + 0.7 * dy
            ax.arrow(arrow_start_x, arrow_start_y, 0.1*dx/length, 0.1*dy/length,
                    head_width=0.15, head_length=0.2, fc=op_color, ec=op_color, alpha=0.8)
        
        # Label the path
        start_x, start_y = points_x[path['start']], points_y[path['start']]
        path_label = f"Path {path_idx+1}"
        ax.text(start_x-1, start_y+1, path_label, fontsize=10, weight='bold',
               bbox=dict(boxstyle='round,pad=0.3', facecolor='yellow', alpha=0.7))
    
    # Show some unused connections in light gray to indicate infinite possibilities
    n_gray_connections = 15
    for _ in range(n_gray_connections):
        i, j = np.random.choice(len(points_x), 2, replace=False)
        ax.plot([points_x[i], points_x[j]], [points_y[i], points_y[j]], 
               color='lightgray', linewidth=1, alpha=0.3, zorder=5)
    
    # Create operation legend
    legend_elements = []
    for op in operations:
        legend_elements.append(mpatches.Patch(color=op['color'], label=f"{op['symbol']} operation"))
    ax.legend(handles=legend_elements, loc='upper left', fontsize=10, 
             title="Available Operations", title_fontsize=12)
    
    # Free choice explanation
    choice_text = 'Observer Freedom:\n• Choose any starting point\n• Select any operation sequence\n• Create unique colored paths\n• Infinite combinations possible'
    ax.text(-9.5, -6, choice_text, fontsize=12, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.5', facecolor='lightgreen', alpha=0.9))
    
    # Mathematical freedom explanation
    math_text = 'Mathematical Basis:\n• m ≥ 2 (starting point freedom)\n• η^(R)(k;m) (relative indicators)\n• R_multi nesting (operation combining)\n• Infinite dimensional color space'
    ax.text(6, -6, math_text, fontsize=12, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.5', facecolor='lightblue', alpha=0.9))
    
    # Central principle
    ax.text(0, 9, 'Observer Freedom in Infinite Mathematical Operations', 
           fontsize=18, weight='bold', ha='center', va='center')
    
    ax.text(0, -9, 'Complete Freedom: Any Path Through Any Mathematical Constants', 
           fontsize=14, weight='bold', ha='center', va='center')
    
    ax.set_title('Ultimate Observer Freedom: Infinite Choice in Mathematical Universe', 
                fontsize=16, weight='bold', pad=30)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_observer_free_choice()
    plt.tight_layout()
    plt.savefig('fig44_observer_free_choice_infinite_network.png', dpi=300, bbox_inches='tight')
    plt.show()