#!/usr/bin/env python3
"""
Figure 28: 4D Color-Time Hypercube System
Three color axes (φ,e,π) + Time axis (T) = Complete 4D information structure
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from information_extraction_mathematics import info_math
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 10

def generate_figure_28():
    """Generate single figure: 4D Color-Time Hypercube"""
    
    fig = plt.figure(figsize=(16, 12))
    ax = fig.add_subplot(111, projection='3d')
    
    # Generate 4D hypercube with color-time structure
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    
    # Project 4D to 3D for visualization
    vertices_3d = recursive_math.project_4d_to_3d(vertices_4d) * 2
    
    # Draw hypercube edges with gradient colors based on endpoint RGB values
    for v1_idx, v2_idx in edges:
        v1_4d = vertices_4d[v1_idx]
        v2_4d = vertices_4d[v2_idx]
        v1_3d = vertices_3d[v1_idx]
        v2_3d = vertices_3d[v2_idx]
        
        # Calculate RGB colors for both endpoints
        v1_color = [v1_4d[0], v1_4d[1], v1_4d[2]]  # φ,e,π coordinates as RGB
        v2_color = [v2_4d[0], v2_4d[1], v2_4d[2]]
        
        # Create gradient line by drawing multiple segments
        n_segments = 20
        for seg in range(n_segments):
            t1 = seg / n_segments
            t2 = (seg + 1) / n_segments
            
            # Interpolate positions
            x1 = v1_3d[0] + t1 * (v2_3d[0] - v1_3d[0])
            y1 = v1_3d[1] + t1 * (v2_3d[1] - v1_3d[1])
            z1 = v1_3d[2] + t1 * (v2_3d[2] - v1_3d[2])
            
            x2 = v1_3d[0] + t2 * (v2_3d[0] - v1_3d[0])
            y2 = v1_3d[1] + t2 * (v2_3d[1] - v1_3d[1])
            z2 = v1_3d[2] + t2 * (v2_3d[2] - v1_3d[2])
            
            # Interpolate color
            seg_color = [
                v1_color[0] + t1 * (v2_color[0] - v1_color[0]),
                v1_color[1] + t1 * (v2_color[1] - v1_color[1]),
                v1_color[2] + t1 * (v2_color[2] - v1_color[2])
            ]
            
            # Ensure color values are in valid range
            seg_color = [max(0, min(1, c)) for c in seg_color]
            
            # Draw colored segment
            ax.plot([x1, x2], [y1, y2], [z1, z2], color=seg_color, 
                   linewidth=2, alpha=0.8)
    
    # Draw vertices with RGB+T color encoding
    for i, (v4d, v3d) in enumerate(zip(vertices_4d, vertices_3d)):
        phi_coord, e_coord, pi_coord, t_coord = v4d
        
        # RGB color based on φ,e,π coordinates
        rgb_color = [phi_coord, e_coord, pi_coord]
        
        # Size based on T coordinate
        size = 80 + t_coord * 120
        
        # Alpha based on T coordinate for time depth
        alpha = 0.5 + t_coord * 0.5
        
        ax.scatter([v3d[0]], [v3d[1]], [v3d[2]], c=[rgb_color], s=size,
                  alpha=alpha, edgecolor='black', linewidth=1)
    
    # Central white light origin
    ax.scatter([0], [0], [0], s=600, c='white', marker='*',
              edgecolor='gold', linewidth=4, alpha=1.0)
    
    # Four dimensional axes clearly labeled
    axis_length = 3
    
    # φ-axis (Red/X)
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=5, alpha=0.9)
    ax.text(axis_length, 0, 0, 'φ-axis\n(Red)', fontsize=12, weight='bold', 
           color='red', ha='left', va='center')
    
    # e-axis (Green/Y)  
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=5, alpha=0.9)
    ax.text(0, axis_length, 0, 'e-axis\n(Green)', fontsize=12, weight='bold',
           color='green', ha='center', va='bottom')
    
    # π-axis (Blue/Z)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=5, alpha=0.9)
    ax.text(0, 0, axis_length, 'π-axis\n(Blue)', fontsize=12, weight='bold',
           color='blue', ha='center', va='bottom')
    
    # T-axis (Time/Purple) - diagonal projection of 4th dimension
    time_end = np.array([axis_length*0.6, axis_length*0.6, axis_length*0.6])
    ax.plot([0, time_end[0]], [0, time_end[1]], [0, time_end[2]],
           'purple', linewidth=6, alpha=1.0)
    ax.text(time_end[0], time_end[1], time_end[2]+0.3, 'T-axis\n(TIME)', 
           fontsize=14, weight='bold', color='purple', ha='center', va='center')
    
    # Show observer trajectories in 4D color-time space
    observer_trajectories = [
        {
            'sequence': ['φ']*5 + ['e']*3 + ['π']*2,
            'start_color': [1, 0.2, 0.1],
            'path_color': 'red'
        },
        {
            'sequence': ['e']*6 + ['π']*4, 
            'start_color': [0.1, 1, 0.3],
            'path_color': 'green'
        },
        {
            'sequence': ['π']*4 + ['φ']*3 + ['e']*3,
            'start_color': [0.2, 0.3, 1],
            'path_color': 'blue'
        }
    ]
    
    for traj in observer_trajectories:
        sequence = traj['sequence']
        path_color = traj['path_color']
        
        # Calculate trajectory points in color-time space
        traj_x = []
        traj_y = []
        traj_z = []
        
        phi_cumulative = 0
        e_cumulative = 0
        pi_cumulative = 0
        
        for i, operation in enumerate(sequence):
            # Accumulate along respective axes
            if operation == 'φ':
                phi_cumulative += 0.2
            elif operation == 'e':
                e_cumulative += 0.2
            else:  # π
                pi_cumulative += 0.2
            
            # Position in 3D projection (T mapped to diagonal)
            t_factor = i / len(sequence)
            x = phi_cumulative + t_factor * 0.5
            y = e_cumulative + t_factor * 0.5
            z = pi_cumulative + t_factor * 0.5
            
            traj_x.append(x)
            traj_y.append(y)
            traj_z.append(z)
        
        # Plot trajectory
        for i in range(len(traj_x)-1):
            alpha = 0.4 + 0.6 * i / len(traj_x)
            ax.plot([traj_x[i], traj_x[i+1]], [traj_y[i], traj_y[i+1]], 
                   [traj_z[i], traj_z[i+1]], color=path_color, 
                   linewidth=3, alpha=alpha)
        
        # Mark start and end points
        ax.scatter([traj_x[0]], [traj_y[0]], [traj_z[0]], 
                  c='white', s=100, edgecolor=path_color, linewidth=2, marker='o')
        ax.scatter([traj_x[-1]], [traj_y[-1]], [traj_z[-1]],
                  c='black', s=100, edgecolor=path_color, linewidth=2, marker='s')
    
    ax.set_xlabel('φ-dimension (Red/Fibonacci)')
    ax.set_ylabel('e-dimension (Green/Factorial)')
    ax.set_zlabel('π-dimension (Blue/Leibniz)')
    ax.set_title('4D Hypercube: Three Color Axes + Time Axis\nWhite Origin Contains All Information',
                fontsize=14, weight='bold', pad=20)
    
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig28_4d_color_time_hypercube.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 28 generated successfully")

if __name__ == "__main__":
    generate_figure_28()