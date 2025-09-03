#!/usr/bin/env python3
"""
Figure 07: Proof that 4D Hypercube Contains Time Dimension
Show how observer trajectories exist within the 4D structure
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_07():
    """Generate single figure: Time Dimension Containment Proof"""
    
    fig = plt.figure(figsize=(16, 12))
    ax = fig.add_subplot(111, projection='3d')
    
    # Generate tesseract structure
    vertices_4d = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    vertices_3d = recursive_math.project_4d_to_3d(vertices_4d) * 3
    
    # Draw hypercube structure (light gray for background)
    for v1_idx, v2_idx in edges:
        v1, v2 = vertices_3d[[v1_idx, v2_idx]]
        ax.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
               'gray', linewidth=1, alpha=0.3)
    
    # Draw vertices
    ax.scatter(vertices_3d[:, 0], vertices_3d[:, 1], vertices_3d[:, 2],
              c='lightgray', s=30, alpha=0.5)
    
    # Central core
    ax.scatter([0], [0], [0], s=300, c='gold', marker='*', 
              edgecolor='black', linewidth=2, alpha=1.0)
    
    # Show three observer time trajectories INSIDE the hypercube
    
    # Observer A: φ-mode trajectory (Exact Fibonacci sequence)
    n_phi_steps = 12
    fib_seq = recursive_math.fibonacci_sequence(n_phi_steps)
    phi_traj_x = []
    phi_traj_y = []
    phi_traj_z = []
    
    for i, fib_val in enumerate(fib_seq):
        # Use exact Fibonacci ratios for φ-mode
        if i > 0:
            phi_ratio = fib_seq[i] / fib_seq[i-1]  # Converges to φ ≈ 1.618
        else:
            phi_ratio = 1
        
        # Trajectory based on exact φ convergence
        angle = i * 2 * np.pi / len(fib_seq)
        radius = min(phi_ratio / 2, 1.5)  # Keep within hypercube bounds
        
        x = radius * np.cos(angle)
        y = radius * np.sin(angle)
        z = (i / (len(fib_seq) - 1) - 0.5) * 3  # T-axis: time progression
        
        phi_traj_x.append(x)
        phi_traj_y.append(y)
        phi_traj_z.append(z)
    
    # Plot φ-trajectory
    ax.plot(phi_traj_x, phi_traj_y, phi_traj_z, 'red', linewidth=4, alpha=0.9, 
           label='φ-Observer Time Path')
    ax.scatter(phi_traj_x, phi_traj_y, phi_traj_z, c='red', s=50, alpha=0.8)
    
    # Observer B: e-mode trajectory (Exact factorial sequence)
    n_e_steps = 10
    fact_seq = recursive_math.factorial_sequence(n_e_steps)
    e_traj_x = []
    e_traj_y = []
    e_traj_z = []
    
    for i, fact_val in enumerate(fact_seq):
        # Use exact factorial values for e-mode
        angle = i * 2 * np.pi / len(fact_seq) + np.pi/3  # Offset for visibility
        
        # Factorial decay pattern: large at start, rapidly decreasing
        radius = fact_val * 3  # Scale up small factorial values
        radius = min(radius, 1.5)  # Keep within bounds
        
        x = radius * np.cos(angle)
        y = radius * np.sin(angle)
        z = (i / (len(fact_seq) - 1) - 0.5) * 3  # T-axis: time progression
        
        e_traj_x.append(x)
        e_traj_y.append(y)
        e_traj_z.append(z)
    
    # Plot e-trajectory
    ax.plot(e_traj_x, e_traj_y, e_traj_z, 'green', linewidth=4, alpha=0.9,
           label='e-Observer Time Path')
    ax.scatter(e_traj_x, e_traj_y, e_traj_z, c='green', s=50, alpha=0.8)
    
    # Observer C: π-mode trajectory (Exact Leibniz sequence)
    n_pi_steps = 14
    leibniz_seq = recursive_math.leibniz_sequence(n_pi_steps)
    pi_traj_x = []
    pi_traj_y = []
    pi_traj_z = []
    
    for i, leibniz_val in enumerate(leibniz_seq):
        # Use exact Leibniz alternating series for π-mode
        angle = i * 2 * np.pi / len(leibniz_seq) + 2*np.pi/3  # Offset for visibility
        
        # Leibniz oscillating pattern: positive/negative alternation
        radius = abs(leibniz_val) * 8  # Scale up small Leibniz values
        radius = min(radius, 1.5)  # Keep within bounds
        
        # Include sign information in the trajectory shape
        sign_factor = 1 if leibniz_val > 0 else -0.5
        
        x = radius * np.cos(angle) + sign_factor * 0.2
        y = radius * np.sin(angle) + sign_factor * 0.2
        z = (i / (len(leibniz_seq) - 1) - 0.5) * 3  # T-axis: time progression
        
        pi_traj_x.append(x)
        pi_traj_y.append(y)
        pi_traj_z.append(z)
    
    # Plot π-trajectory
    ax.plot(pi_traj_x, pi_traj_y, pi_traj_z, 'purple', linewidth=4, alpha=0.9,
           label='π-Observer Time Path')
    ax.scatter(pi_traj_x, pi_traj_y, pi_traj_z, c='purple', s=50, alpha=0.8)
    
    # Coordinate system axes with TIME axis highlighted
    axis_length = 4
    
    # X, Y, Z axes
    ax.plot([0, axis_length], [0, 0], [0, 0], 'r-', linewidth=3, alpha=0.7)
    ax.plot([0, 0], [0, axis_length], [0, 0], 'g-', linewidth=3, alpha=0.7)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'b-', linewidth=3, alpha=0.7)
    
    # TIME axis (4th dimension) - prominent display
    time_end = np.array([axis_length*0.7, axis_length*0.7, axis_length*0.7])
    ax.plot([0, time_end[0]], [0, time_end[1]], [0, time_end[2]], 
           'purple', linewidth=6, alpha=1.0)
    
    # Axis labels
    ax.text(axis_length, 0, 0, 'X', fontsize=14, weight='bold', color='red')
    ax.text(0, axis_length, 0, 'Y', fontsize=14, weight='bold', color='green')
    ax.text(0, 0, axis_length, 'Z', fontsize=14, weight='bold', color='blue')
    ax.text(time_end[0], time_end[1], time_end[2]+0.5, 'T (TIME)', 
           fontsize=16, weight='bold', color='purple', ha='center', va='center')
    
    # Mark trajectory start/end points
    for traj_x, traj_y, traj_z, color in [
        (phi_traj_x, phi_traj_y, phi_traj_z, 'red'),
        (e_traj_x, e_traj_y, e_traj_z, 'green'),
        (pi_traj_x, pi_traj_y, pi_traj_z, 'purple')
    ]:
        ax.scatter([traj_x[0]], [traj_y[0]], [traj_z[0]], 
                  c='white', s=100, edgecolor=color, linewidth=3, marker='o')
        ax.scatter([traj_x[-1]], [traj_y[-1]], [traj_z[-1]], 
                  c='black', s=100, edgecolor=color, linewidth=3, marker='s')
    
    ax.set_xlabel('X: Recursion Level')
    ax.set_ylabel('Y: Starting Point') 
    ax.set_zlabel('Z: Tag Coefficient')
    ax.set_title('4D Hypercube Contains All Observer Time Trajectories\nT-axis = 4th Dimension = Time Dimension', 
                fontsize=14, weight='bold', pad=20)
    
    ax.legend(loc='upper left')
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig07_time_dimension_proof.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 07 generated successfully")

if __name__ == "__main__":
    generate_figure_07()