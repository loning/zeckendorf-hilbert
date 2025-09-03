#!/usr/bin/env python3
"""
Figure 08: Different Projection Views of 4D Hypercube
Show how 4D tesseract appears from different viewing angles
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 10

def generate_figure_08():
    """Generate single figure: Tesseract Different Projections"""
    
    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(18, 12))
    
    # Generate tesseract vertices and edges
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    
    # Different projection parameters for 6 different views
    projection_params = [
        {'w_distance': 3.0, 'rotation': (0, 0), 'title': 'Standard View\n(W-distance=3.0)'},
        {'w_distance': 2.0, 'rotation': (0, 0), 'title': 'Close View\n(W-distance=2.0)'}, 
        {'w_distance': 5.0, 'rotation': (0, 0), 'title': 'Far View\n(W-distance=5.0)'},
        {'w_distance': 3.0, 'rotation': (30, 0), 'title': 'Rotated View X\n(30° rotation)'},
        {'w_distance': 3.0, 'rotation': (0, 45), 'title': 'Rotated View Y\n(45° rotation)'},
        {'w_distance': 2.5, 'rotation': (20, 30), 'title': 'Combined Rotation\n(20°,30°)'}
    ]
    
    axes_3d = []
    for i in range(6):
        ax = fig.add_subplot(2, 3, i+1, projection='3d')
        axes_3d.append(ax)
    
    for ax, params in zip(axes_3d, projection_params):
        
        # Apply rotation to 4D vertices before projection
        vertices_4d_rotated = vertices_4d.copy()
        
        # Simple 4D rotation (rotation in XY and XZ planes)
        rot_xy = np.radians(params['rotation'][0])
        rot_xz = np.radians(params['rotation'][1])
        
        if rot_xy != 0 or rot_xz != 0:
            for j, v in enumerate(vertices_4d):
                x, y, z, w = v
                
                # Rotation in XY plane
                if rot_xy != 0:
                    x_new = x * np.cos(rot_xy) - y * np.sin(rot_xy)
                    y_new = x * np.sin(rot_xy) + y * np.cos(rot_xy)
                    x, y = x_new, y_new
                
                # Rotation in XZ plane  
                if rot_xz != 0:
                    x_new = x * np.cos(rot_xz) - z * np.sin(rot_xz)
                    z_new = x * np.sin(rot_xz) + z * np.cos(rot_xz)
                    x, z = x_new, z_new
                
                vertices_4d_rotated[j] = [x, y, z, w]
        
        # Project to 3D with specified parameters
        vertices_3d = recursive_math.project_4d_to_3d(vertices_4d_rotated, params['w_distance'])
        vertices_3d = vertices_3d * 2  # Scale for visibility
        
        # Draw edges with dimension-based coloring
        edge_colors = ['red', 'green', 'blue', 'purple']
        
        for v1_idx, v2_idx in edges:
            # Determine edge dimension
            diff = vertices_4d_rotated[v2_idx] - vertices_4d_rotated[v1_idx]
            dimension = np.argmax(np.abs(diff))
            
            v1_3d = vertices_3d[v1_idx]
            v2_3d = vertices_3d[v2_idx]
            
            # Alpha based on W coordinate for depth perception
            w_avg = (vertices_4d_rotated[v1_idx][3] + vertices_4d_rotated[v2_idx][3]) / 2
            alpha = 0.3 + 0.7 * w_avg
            
            ax.plot([v1_3d[0], v2_3d[0]], [v1_3d[1], v2_3d[1]], [v1_3d[2], v2_3d[2]],
                   color=edge_colors[dimension], linewidth=2, alpha=alpha)
        
        # Draw vertices with simple coloring
        w_coords = vertices_4d_rotated[:, 3]  # Extract W coordinates
        vertex_colors = w_coords  # Use W coordinate for color mapping
        vertex_sizes = 40 + w_coords * 40  # Size based on W coordinate
        
        scatter = ax.scatter(vertices_3d[:, 0], vertices_3d[:, 1], vertices_3d[:, 2],
                           c=vertex_colors, s=vertex_sizes, cmap='plasma', 
                           alpha=0.8, edgecolor='black', linewidth=0.5)
        
        # Central core
        ax.scatter([0], [0], [0], s=200, c='gold', marker='*', 
                  edgecolor='black', linewidth=2, alpha=1.0)
        
        # TIME axis for each projection
        time_end = np.array([2, 2, 2])
        ax.plot([0, time_end[0]], [0, time_end[1]], [0, time_end[2]], 
               'purple', linewidth=4, alpha=0.8)
        ax.text(time_end[0], time_end[1], time_end[2]+0.3, 'T', 
               fontsize=12, weight='bold', color='purple', ha='center')
        
        ax.set_title(params['title'], fontsize=11, weight='bold')
        ax.set_box_aspect([1,1,1])
        ax.grid(True, alpha=0.2)
        ax.set_xlim(-3, 3)
        ax.set_ylim(-3, 3)
        ax.set_zlim(-3, 3)
    
    plt.suptitle('4D Hypercube from Different Viewing Angles\nT-axis (Time Dimension) Visible in All Projections',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig08_tesseract_projections.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 08 generated successfully")

if __name__ == "__main__":
    generate_figure_08()