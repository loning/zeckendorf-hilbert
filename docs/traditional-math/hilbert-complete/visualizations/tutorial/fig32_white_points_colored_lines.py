#!/usr/bin/env python3
"""
Figure 32: White Points, Colored Lines - The True Structure
Show that points are always white (information sources) 
Only the lines (operations) have colors
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from recursive_math_functions import recursive_math
import random

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_32():
    """Generate single figure: White Points, Colored Lines"""
    
    fig = plt.figure(figsize=(16, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Generate observer path with 10 points
    n_points = 10
    operations = ['φ', 'e', 'π']
    random.seed(123)  # Different seed for variety
    operation_sequence = [random.choice(operations) for _ in range(n_points-1)]  # 9 operations for 10 points
    
    # Generate path points
    path_points = []
    start_point = [1, 1, 1]  # Starting position
    current_point = start_point.copy()
    path_points.append(current_point.copy())
    
    for i, operation in enumerate(operation_sequence):
        # Each operation moves observer to next white point
        if operation == 'φ':
            # Fibonacci-like movement
            movement = [0.3, 0.1, 0.2]
        elif operation == 'e':
            # Factorial-like movement  
            movement = [0.1, 0.3, 0.1]
        else:  # π operation
            # Leibniz-like movement
            movement = [0.2, 0.1, 0.3]
        
        # Apply movement with some randomness
        for j in range(3):
            current_point[j] += movement[j] * (1 + i*0.1) * (0.8 + 0.4*random.random())
        
        path_points.append(current_point.copy())
    
    # ALL POINTS ARE WHITE (information sources)
    for i, point in enumerate(path_points):
        x, y, z = point
        
        # Every point is WHITE - they are all information source points
        ax.scatter([x], [y], [z], s=200, c='white', marker='o',
                  edgecolor='black', linewidth=2, alpha=1.0)
        
        # Label each point
        ax.text(x, y, z+0.2, f'P{i+1}', ha='center', va='bottom',
               fontsize=10, weight='bold', color='black',
               bbox=dict(boxstyle="circle,pad=0.2", facecolor='white', 
                        edgecolor='black', alpha=0.9))
    
    # ONLY LINES HAVE COLORS (operations have colors)
    operation_colors = {'φ': 'red', 'e': 'green', 'π': 'blue'}
    
    for i in range(len(path_points)-1):
        operation = operation_sequence[i]
        color = operation_colors[operation]
        
        p1 = path_points[i]
        p2 = path_points[i+1]
        
        # Draw colored line segment (thick to emphasize)
        ax.plot([p1[0], p2[0]], [p1[1], p2[1]], [p1[2], p2[2]], 
               color=color, linewidth=6, alpha=0.9)
        
        # Operation label on line
        mid_x = (p1[0] + p2[0]) / 2
        mid_y = (p1[1] + p2[1]) / 2  
        mid_z = (p1[2] + p2[2]) / 2
        
        ax.text(mid_x, mid_y, mid_z, operation, ha='center', va='center',
               fontsize=12, weight='bold', color='white',
               bbox=dict(boxstyle="round,pad=0.2", facecolor=color, alpha=0.8))
    
    # Central white light source
    ax.scatter([0], [0], [0], s=500, c='white', marker='*',
              edgecolor='gold', linewidth=4, alpha=1.0)
    ax.text(0, 0, -0.5, 'WHITE\nSOURCE', ha='center', va='top',
           fontsize=12, weight='bold', color='gold')
    
    # Show that all points connect back to white source
    for point in path_points[::2]:  # Every other point for clarity
        x, y, z = point
        ax.plot([0, x], [0, y], [0, z], 'gold', linestyle=':', 
               alpha=0.3, linewidth=1)
    
    # Three information axes
    axis_length = 5
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=2, alpha=0.4)
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=2, alpha=0.4)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=2, alpha=0.4)
    
    ax.set_xlabel('φ-space')
    ax.set_ylabel('e-space')
    ax.set_zlabel('π-space')
    ax.set_title('TRUE STRUCTURE: White Points (Information Sources) + Colored Lines (Operations)\nPoints Never Change Color - Only Operations Have Color',
                fontsize=14, weight='bold', pad=20)
    
    # Key insight box
    insight_text = f"""OPERATION SEQUENCE: {' → '.join(operation_sequence)}

KEY INSIGHT:
• All points are WHITE (information sources)
• Only LINES have colors (operations)  
• Color = Operation type, not point property
• Information flows through colored operations
• Points remain pure information sources"""
    
    ax.text2D(0.02, 0.98, insight_text, transform=ax.transAxes, ha='left', va='top',
             fontsize=10, bbox=dict(boxstyle="round,pad=0.4", 
             facecolor='lightyellow', alpha=0.95))
    
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig32_white_points_colored_lines.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 32 generated successfully")
    print(f"Operation sequence: {operation_sequence}")

if __name__ == "__main__":
    generate_figure_32()