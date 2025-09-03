#!/usr/bin/env python3
"""
Figure 31: Observer Random Colored Path in 4D Hypercube
Show observer with 10-point line segment, each point from random φ,e,π operation
Line color changes continuously based on operation sequence
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from recursive_math_functions import recursive_math
import random

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_31():
    """Generate single figure: Observer Random Colored Path"""
    
    fig = plt.figure(figsize=(16, 12))
    ax = fig.add_subplot(111, projection='3d')
    
    # Generate 4D hypercube structure
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    vertices_3d = recursive_math.project_4d_to_3d(vertices_4d) * 2
    
    # Draw light hypercube frame
    for v1_idx, v2_idx in edges:
        v1, v2 = vertices_3d[[v1_idx, v2_idx]]
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
               'lightgray', linewidth=1, alpha=0.3)
    
    # Draw vertices
    ax.scatter(vertices_3d[:, 0], vertices_3d[:, 1], vertices_3d[:, 2],
              c='lightgray', s=20, alpha=0.4)
    
    # Central white light core
    ax.scatter([0], [0], [0], s=400, c='white', marker='*',
              edgecolor='gold', linewidth=3, alpha=1.0)
    
    # Four axes
    axis_length = 3
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=3, alpha=0.6)     # φ-axis
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=3, alpha=0.6)   # e-axis  
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=3, alpha=0.6)    # π-axis
    
    # T-axis (time)
    time_end = np.array([axis_length*0.7, axis_length*0.7, axis_length*0.7])
    ax.plot([0, time_end[0]], [0, time_end[1]], [0, time_end[2]], 
           'purple', linewidth=4, alpha=0.8)
    ax.text(time_end[0], time_end[1], time_end[2]+0.3, 'T', 
           fontsize=14, weight='bold', color='purple', ha='center')
    
    # Generate random operation sequence for observer
    operations = ['φ', 'e', 'π']
    random.seed(42)  # Reproducible randomness
    random_sequence = [random.choice(operations) for _ in range(10)]
    
    # Calculate observer path with 10 points based on operations
    observer_path_x = []
    observer_path_y = []  
    observer_path_z = []
    line_colors = []
    
    # Starting position
    start_pos = [1.5, 1, 0.5]
    current_pos = start_pos.copy()
    
    # Track cumulative operation effects
    phi_cumulative = 0
    e_cumulative = 0  
    pi_cumulative = 0
    
    for i, operation in enumerate(random_sequence):
        # Update cumulative values based on operation
        if operation == 'φ':
            phi_cumulative += 1
            step_direction = np.array([0.3, 0.1, 0.1])  # Toward φ-axis
        elif operation == 'e':
            e_cumulative += 1
            step_direction = np.array([0.1, 0.3, 0.1])  # Toward e-axis
        else:  # π operation
            pi_cumulative += 1  
            step_direction = np.array([0.1, 0.1, 0.3])  # Toward π-axis
        
        # Update position
        current_pos = [current_pos[j] + step_direction[j] * (1 + i*0.1) for j in range(3)]
        
        observer_path_x.append(current_pos[0])
        observer_path_y.append(current_pos[1])
        observer_path_z.append(current_pos[2])
        
        # Calculate line color based on operation ratios
        total_ops = i + 1
        phi_ratio = phi_cumulative / total_ops
        e_ratio = e_cumulative / total_ops
        pi_ratio = pi_cumulative / total_ops
        
        # Color = ratio of operations used so far
        line_color = [phi_ratio, e_ratio, pi_ratio]
        line_colors.append(line_color)
    
    # Draw observer path with changing colors
    for i in range(len(observer_path_x)-1):
        # Current segment color
        segment_color = line_colors[i]
        
        # Draw segment with thickness indicating time progression
        thickness = 2 + i * 0.5  # Getting thicker over time
        
        ax.plot([observer_path_x[i], observer_path_x[i+1]], 
               [observer_path_y[i], observer_path_y[i+1]], 
               [observer_path_z[i], observer_path_z[i+1]],
               color=segment_color, linewidth=thickness, alpha=0.9)
    
    # Draw the 10 operation points with colors and operation labels
    for i, (x, y, z, color, op) in enumerate(zip(observer_path_x, observer_path_y, observer_path_z, 
                                                 line_colors, random_sequence)):
        # Point marker
        ax.scatter([x], [y], [z], c=[color], s=120, alpha=0.9,
                  edgecolor='black', linewidth=1)
        
        # Operation label
        ax.text(x, y, z+0.2, f'{i+1}:{op}', ha='center', va='bottom',
               fontsize=9, weight='bold', color='black',
               bbox=dict(boxstyle="round,pad=0.2", facecolor='white', alpha=0.8))
    
    # Mark starting point
    ax.scatter([start_pos[0]], [start_pos[1]], [start_pos[2]], 
              s=200, c='white', marker='o', edgecolor='black', linewidth=3)
    ax.text(start_pos[0], start_pos[1], start_pos[2]-0.3, 'START', 
           ha='center', va='top', fontsize=12, weight='bold')
    
    # Mark ending point  
    ax.scatter([observer_path_x[-1]], [observer_path_y[-1]], [observer_path_z[-1]],
              s=200, c=line_colors[-1], marker='s', edgecolor='black', linewidth=3)
    ax.text(observer_path_x[-1], observer_path_y[-1], observer_path_z[-1]+0.3, 'END',
           ha='center', va='bottom', fontsize=12, weight='bold')
    
    # Show operation sequence at bottom
    sequence_text = f"Random Operation Sequence: {' → '.join(random_sequence)}"
    ax.text2D(0.5, 0.02, sequence_text, transform=ax.transAxes, ha='center', va='bottom',
             fontsize=12, weight='bold',
             bbox=dict(boxstyle="round,pad=0.3", facecolor='lightyellow', alpha=0.9))
    
    # Color evolution legend
    legend_text = "Line Color Evolution:\nRed intensity = φ operation ratio\nGreen intensity = e operation ratio\nBlue intensity = π operation ratio"
    ax.text2D(0.02, 0.98, legend_text, transform=ax.transAxes, ha='left', va='top',
             fontsize=10, bbox=dict(boxstyle="round,pad=0.3", facecolor='lightcyan', alpha=0.9))
    
    ax.set_xlabel('φ-dimension (Red intensity)')
    ax.set_ylabel('e-dimension (Green intensity)')  
    ax.set_zlabel('π-dimension (Blue intensity)')
    ax.set_title('Observer Random Colored Path in 4D Hypercube\n10 Random Operations → Continuously Changing Line Color',
                fontsize=14, weight='bold', pad=20)
    
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig31_observer_random_colored_path.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 31 generated successfully")
    print(f"Random sequence used: {random_sequence}")

if __name__ == "__main__":
    generate_figure_31()