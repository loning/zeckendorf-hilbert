#!/usr/bin/env python3
"""
Figure 25: Observer Hierarchy Recursive Structure (Final Figure)
Show different observer levels and their recursive capabilities
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import Circle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 10

def generate_figure_25():
    """Generate single figure: Observer Hierarchy Levels"""
    
    fig = plt.figure(figsize=(16, 12))
    ax = fig.add_subplot(111, projection='3d')
    
    # Central hypercube core
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    vertices_3d = recursive_math.project_4d_to_3d(vertices_4d) * 1
    
    # Draw core structure (light)
    for v1_idx, v2_idx in edges:
        v1, v2 = vertices_3d[[v1_idx, v2_idx]]
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
               'gold', linewidth=1, alpha=0.4)
    
    ax.scatter(vertices_3d[:, 0], vertices_3d[:, 1], vertices_3d[:, 2],
              c='gold', s=20, alpha=0.5)
    
    # Different observer hierarchy levels
    observer_levels = [
        {
            'level': 1, 
            'radius': 2,
            'n_observers': 8,
            'color': 'red',
            'capability': 'Basic observation',
            'sequence_length': 10
        },
        {
            'level': 2,
            'radius': 3,
            'n_observers': 6, 
            'color': 'green',
            'capability': 'Multi-mode observation',
            'sequence_length': 20
        },
        {
            'level': 3,
            'radius': 4,
            'n_observers': 4,
            'color': 'blue',
            'capability': 'Coordinate transformation',
            'sequence_length': 35
        },
        {
            'level': 4,
            'radius': 5,
            'n_observers': 2,
            'color': 'purple', 
            'capability': 'Meta-observation',
            'sequence_length': 50
        }
    ]
    
    for level_data in observer_levels:
        level = level_data['level']
        radius = level_data['radius']
        n_obs = level_data['n_observers']
        color = level_data['color']
        seq_length = level_data['sequence_length']
        
        # Observer positions in this level
        angles = np.linspace(0, 2*np.pi, n_obs, endpoint=False)
        
        for angle in angles:
            # Observer position
            x = radius * np.cos(angle)
            y = radius * np.sin(angle)
            z = (level - 2.5) * 1.5  # Vertical separation by level
            
            ax.scatter([x], [y], [z], c=color, s=100, alpha=0.8,
                      edgecolor='black', linewidth=1)
            
            # Observer capability trajectory (towards core)
            n_steps = seq_length // 5  # Simplified for visualization
            traj_x = []
            traj_y = []
            traj_z = []
            
            for step in range(n_steps):
                # Trajectory spirals toward core with level-specific complexity
                t = step * 2*np.pi / n_steps
                r = radius * (1 - step/(n_steps * 1.2))  # Approach core
                
                traj_x.append(r * np.cos(angle + t/level))
                traj_y.append(r * np.sin(angle + t/level))  
                traj_z.append(z + (step/n_steps - 0.5) * 0.5)
            
            # Plot capability trajectory
            for i in range(len(traj_x)-1):
                alpha = 0.3 + 0.7 * i / len(traj_x)
                ax.plot([traj_x[i], traj_x[i+1]], [traj_y[i], traj_y[i+1]], 
                       [traj_z[i], traj_z[i+1]], color=color, linewidth=2, alpha=alpha)
    
    # Level boundaries (spherical shells)
    for level_data in observer_levels:
        radius = level_data['radius'] 
        level = level_data['level']
        
        # Draw level boundary circle in XY plane
        theta_boundary = np.linspace(0, 2*np.pi, 50)
        boundary_x = radius * np.cos(theta_boundary)
        boundary_y = radius * np.sin(theta_boundary)
        boundary_z = np.ones_like(theta_boundary) * ((level - 2.5) * 1.5)
        
        ax.plot(boundary_x, boundary_y, boundary_z, color='gray', 
               linewidth=1, alpha=0.3)
    
    # Central core marker
    ax.scatter([0], [0], [0], s=300, c='gold', marker='*',
              edgecolor='black', linewidth=3, alpha=1.0)
    
    # Coordinate axes
    axis_length = 6
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=2, alpha=0.6)
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=2, alpha=0.6)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=2, alpha=0.6)
    
    # TIME axis
    time_end = np.array([4, 4, 4])
    ax.plot([0, time_end[0]], [0, time_end[1]], [0, time_end[2]],
           'purple', linewidth=4, alpha=0.9)
    ax.text(time_end[0], time_end[1], time_end[2]+0.5, 'T', 
           fontsize=14, weight='bold', color='purple', ha='center')
    
    ax.set_xlabel('Observation Scope X')
    ax.set_ylabel('Observation Depth Y')
    ax.set_zlabel('Observer Level Z')
    ax.set_title('Observer Hierarchy Recursive Structure\nHigher Levels → Greater Observation Capability → Longer Sequences',
                fontsize=14, weight='bold', pad=20)
    
    ax.set_box_aspect([1,1,0.6])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig25_observer_hierarchy_levels.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 25 generated successfully")

if __name__ == "__main__":
    generate_figure_25()