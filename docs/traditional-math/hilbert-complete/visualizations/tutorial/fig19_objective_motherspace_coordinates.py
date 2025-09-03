#!/usr/bin/env python3
"""
Figure 19: Objective Mother Space Coordinate Structure
Show the objective coordinate system of recursive mother space
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import Circle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_19():
    """Generate single figure: Objective Mother Space Coordinates"""
    
    fig = plt.figure(figsize=(16, 12))
    
    # Main 3D view of objective coordinate system
    ax = fig.add_subplot(111, projection='3d')
    
    # Draw objective coordinate grid
    grid_range = 4
    grid_spacing = 0.5
    
    # Grid lines in each plane
    for i in np.arange(-grid_range, grid_range + grid_spacing, grid_spacing):
        # XY plane grid
        ax.plot([-grid_range, grid_range], [i, i], [0, 0], 'gray', alpha=0.2, linewidth=0.5)
        ax.plot([i, i], [-grid_range, grid_range], [0, 0], 'gray', alpha=0.2, linewidth=0.5)
        
        # XZ plane grid
        ax.plot([-grid_range, grid_range], [0, 0], [i, i], 'gray', alpha=0.2, linewidth=0.5)
        ax.plot([i, i], [0, 0], [-grid_range, grid_range], 'gray', alpha=0.2, linewidth=0.5)
        
        # YZ plane grid
        ax.plot([0, 0], [-grid_range, grid_range], [i, i], 'gray', alpha=0.2, linewidth=0.5)
        ax.plot([0, 0], [i, i], [-grid_range, grid_range], 'gray', alpha=0.2, linewidth=0.5)
    
    # Main coordinate axes
    axis_length = 5
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=4, alpha=0.9)
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=4, alpha=0.9)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=4, alpha=0.9)
    
    # TIME dimension axis (4th dimension)
    time_axis_end = np.array([axis_length*0.7, axis_length*0.7, axis_length*0.7])
    ax.plot([0, time_axis_end[0]], [0, time_axis_end[1]], [0, time_axis_end[2]],
           'purple', linewidth=6, alpha=1.0)
    
    # Central invariant hypercube core
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    vertices_3d = recursive_math.project_4d_to_3d(vertices_4d) * 1.5
    
    # Draw hypercube edges
    for v1_idx, v2_idx in edges:
        v1, v2 = vertices_3d[[v1_idx, v2_idx]]
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
               'gold', linewidth=2, alpha=0.8)
    
    # Draw hypercube vertices
    ax.scatter(vertices_3d[:, 0], vertices_3d[:, 1], vertices_3d[:, 2],
              c='gold', s=60, alpha=0.9, edgecolor='black', linewidth=1)
    
    # Multiple observer sequences in objective space
    observer_data = [
        {'start': np.array([2, 1, -1]), 'color': 'red', 'mode': 'phi'},
        {'start': np.array([-1.5, 2, 0.5]), 'color': 'green', 'mode': 'e'},
        {'start': np.array([1, -2, 1.5]), 'color': 'purple', 'mode': 'pi'}
    ]
    
    for obs in observer_data:
        start_pos = obs['start']
        color = obs['color']
        mode = obs['mode']
        
        # Generate objective trajectory based on mode
        n_steps = 15
        trajectory_x = [start_pos[0]]
        trajectory_y = [start_pos[1]]
        trajectory_z = [start_pos[2]]
        
        if mode == 'phi':
            fib_seq = recursive_math.fibonacci_sequence(n_steps)
            for i, fib_val in enumerate(fib_seq[1:]):
                factor = fib_val / max(fib_seq) * 0.3
                trajectory_x.append(trajectory_x[-1] + factor * np.cos(i * 0.5))
                trajectory_y.append(trajectory_y[-1] + factor * np.sin(i * 0.5))
                trajectory_z.append(trajectory_z[-1] + factor * 0.2)
                
        elif mode == 'e':
            fact_seq = recursive_math.factorial_sequence(n_steps)
            for i, fact_val in enumerate(fact_seq[1:]):
                factor = fact_val * 2
                trajectory_x.append(trajectory_x[-1] + factor * np.cos(i * 0.4))
                trajectory_y.append(trajectory_y[-1] + factor * np.sin(i * 0.4))
                trajectory_z.append(trajectory_z[-1] - factor * 0.1)
                
        else:  # pi mode
            leibniz_seq = recursive_math.leibniz_sequence(n_steps)
            for i, leibniz_val in enumerate(leibniz_seq[1:]):
                factor = abs(leibniz_val) * 3
                sign = 1 if leibniz_val > 0 else -1
                trajectory_x.append(trajectory_x[-1] + factor * np.cos(i * 0.6) * sign)
                trajectory_y.append(trajectory_y[-1] + factor * np.sin(i * 0.6))
                trajectory_z.append(trajectory_z[-1] + factor * 0.1 * sign)
        
        # Plot observer trajectory in objective space
        for i in range(len(trajectory_x)-1):
            alpha = 0.4 + 0.6 * i / len(trajectory_x)
            ax.plot([trajectory_x[i], trajectory_x[i+1]],
                   [trajectory_y[i], trajectory_y[i+1]], 
                   [trajectory_z[i], trajectory_z[i+1]],
                   color=color, linewidth=3, alpha=alpha)
        
        # Mark start and end
        ax.scatter([trajectory_x[0]], [trajectory_y[0]], [trajectory_z[0]],
                  c='white', s=100, edgecolor=color, linewidth=2, marker='o')
        ax.scatter([trajectory_x[-1]], [trajectory_y[-1]], [trajectory_z[-1]],
                  c='black', s=100, edgecolor=color, linewidth=2, marker='s')
    
    # Axis labels
    ax.text(axis_length, 0, 0, 'X (n)', fontsize=14, weight='bold', color='red')
    ax.text(0, axis_length, 0, 'Y (m)', fontsize=14, weight='bold', color='green')
    ax.text(0, 0, axis_length, 'Z', fontsize=14, weight='bold', color='blue')
    ax.text(time_axis_end[0], time_axis_end[1], time_axis_end[2]+0.5, 'T', 
           fontsize=16, weight='bold', color='purple', ha='center')
    
    ax.set_xlabel('Recursion Level n')
    ax.set_ylabel('Starting Point m')
    ax.set_zlabel('Tag Coefficient')
    ax.set_title('Objective Mother Space Coordinates\nAll Observer Sequences in Universal Framework',
                fontsize=14, weight='bold', pad=20)
    
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig19_objective_motherspace_coordinates.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 19 generated successfully")

if __name__ == "__main__":
    generate_figure_19()