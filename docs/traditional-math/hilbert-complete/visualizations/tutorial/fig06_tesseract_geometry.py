#!/usr/bin/env python3
"""
Figure 06: Complete 4D Hypercube (Tesseract) Geometry
Precise mathematical structure of the invariant core
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_06():
    """Generate single figure: Complete Tesseract Geometry"""
    
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Generate exact 4D hypercube vertices using strict math
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    
    # Project to 3D with sophisticated perspective
    vertices_3d = recursive_math.project_4d_to_3d(vertices_4d, w_distance=4.0)
    
    # Scale and center for better visualization
    vertices_3d = vertices_3d * 2
    
    # Draw edges with dimension-based coloring
    edge_colors = ['red', 'green', 'blue', 'purple']
    
    for edge_idx, (v1_idx, v2_idx) in enumerate(edges):
        v1_4d = vertices_4d[v1_idx]
        v2_4d = vertices_4d[v2_idx]
        
        # Determine which dimension this edge spans
        diff = v2_4d - v1_4d
        dimension = np.argmax(np.abs(diff))
        
        v1_3d = vertices_3d[v1_idx]
        v2_3d = vertices_3d[v2_idx]
        
        # Color based on dimension
        color = edge_colors[dimension]
        
        # Alpha based on 4th dimension position
        w_avg = (v1_4d[3] + v2_4d[3]) / 2
        alpha = 0.4 + 0.6 * w_avg
        
        # Line thickness based on distance from center
        distance = np.linalg.norm((v1_3d + v2_3d) / 2)
        linewidth = 1 + 3 * np.exp(-distance)
        
        ax.plot([v1_3d[0], v2_3d[0]], [v1_3d[1], v2_3d[1]], [v1_3d[2], v2_3d[2]],
               color=color, linewidth=linewidth, alpha=alpha)
    
    # Draw vertices with 4D coordinate encoding
    vertex_colors = []
    vertex_sizes = []
    
    for v4d in vertices_4d:
        # RGB from XYZ coordinates, size from W coordinate
        r, g, b, w = v4d
        vertex_colors.append([r, g, b])
        vertex_sizes.append(50 + w * 100)
    
    ax.scatter(vertices_3d[:, 0], vertices_3d[:, 1], vertices_3d[:, 2],
              c=vertex_colors, s=vertex_sizes, alpha=0.9, 
              edgecolor='black', linewidth=1)
    
    # Central invariant core marker
    ax.scatter([0], [0], [0], s=400, c='gold', marker='*', 
              edgecolor='black', linewidth=3, alpha=1.0)
    
    # Add coordinate system axes including TIME axis
    axis_length = 3
    ax.plot([0, axis_length], [0, 0], [0, 0], 'r-', linewidth=4, alpha=0.9)
    ax.plot([0, 0], [0, axis_length], [0, 0], 'g-', linewidth=4, alpha=0.9)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'b-', linewidth=4, alpha=0.9)
    
    # Special TIME axis (4th dimension) - shown as diagonal projection
    time_axis_end = np.array([axis_length*0.6, axis_length*0.6, axis_length*0.6])
    ax.plot([0, time_axis_end[0]], [0, time_axis_end[1]], [0, time_axis_end[2]], 
           'purple', linewidth=5, alpha=1.0)
    
    # Axis labels
    ax.text(axis_length, 0, 0, 'X', fontsize=16, weight='bold', color='red')
    ax.text(0, axis_length, 0, 'Y', fontsize=16, weight='bold', color='green')
    ax.text(0, 0, axis_length, 'Z', fontsize=16, weight='bold', color='blue')
    ax.text(time_axis_end[0], time_axis_end[1], time_axis_end[2], 'T\n(TIME)', 
           fontsize=16, weight='bold', color='purple', ha='center', va='center')
    
    ax.set_xlabel('X Dimension (Recursion Level)')
    ax.set_ylabel('Y Dimension (Starting Point)')
    ax.set_zlabel('Z Dimension (Tag Coefficient)')
    ax.set_title('4D Hypercube (Tesseract) with TIME Dimension\n16 Vertices, 32 Edges, T-axis = 4th Dimension', 
                fontsize=14, weight='bold', pad=20)
    
    # Perfect aspect ratio for 4D visualization
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig06_tesseract_geometry.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 06 generated successfully")

if __name__ == "__main__":
    generate_figure_06()