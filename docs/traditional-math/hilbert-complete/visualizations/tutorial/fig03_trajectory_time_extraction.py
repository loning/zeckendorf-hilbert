#!/usr/bin/env python3
"""
Figure 03: Trajectory Time Extraction
Show how the trajectory itself becomes the time dimension data
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default') 
plt.rcParams['font.size'] = 12

def generate_figure_03():
    """Generate single figure: Trajectory Time Extraction"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Generate trajectory using exact Fibonacci modulation
    lat, lon = np.pi/4, np.pi/3
    n_steps = 25
    fib_sequence = recursive_math.fibonacci_sequence(n_steps)
    
    # Create complex trajectory
    trajectory_data = []
    cumulative_angle = 0
    
    for i, fib_val in enumerate(fib_sequence):
        # Complex rotation pattern
        angle_increment = fib_val / 500 + 0.2  # Fibonacci + base rotation
        cumulative_angle += angle_increment
        
        # Add complexity: wobble and scaling
        wobble = 0.05 * np.sin(cumulative_angle * 3)
        scale = 1 + 0.1 * np.sin(cumulative_angle * 0.8)
        
        # Calculate position
        effective_lat = lat + wobble
        x = scale * np.cos(effective_lat) * np.cos(lon + cumulative_angle)
        y = scale * np.cos(effective_lat) * np.sin(lon + cumulative_angle)
        z = scale * np.sin(effective_lat)
        
        trajectory_data.append([x, y, z, fib_val, scale])
    
    trajectory_data = np.array(trajectory_data)
    
    # Top left: Spatial trajectory
    ax1.set_aspect('equal')
    ax1.plot(trajectory_data[:, 0], trajectory_data[:, 1], 'b-', linewidth=3, alpha=0.8)
    ax1.scatter(trajectory_data[:, 0], trajectory_data[:, 1], 
               c=range(len(trajectory_data)), cmap='plasma', s=60, alpha=0.9,
               edgecolors='black', linewidths=0.5)
    
    # Mark sequence
    ax1.plot(trajectory_data[0, 0], trajectory_data[0, 1], 'go', markersize=15,
            markeredgecolor='black', markeredgewidth=2, label='Start')
    ax1.plot(trajectory_data[-1, 0], trajectory_data[-1, 1], 'ro', markersize=15,
            markeredgecolor='black', markeredgewidth=2, label='End')
    
    ax1.set_xlabel('X Spatial Coordinate')
    ax1.set_ylabel('Y Spatial Coordinate')
    ax1.set_title('Spatial Trajectory\n(Observer Path in Space)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Top right: Time dimension extracted - X component
    time_indices = range(len(trajectory_data))
    ax2.plot(time_indices, trajectory_data[:, 0], 'r-', linewidth=3, 
            marker='o', markersize=5, alpha=0.8, label='X(time)')
    ax2.fill_between(time_indices, trajectory_data[:, 0], alpha=0.3, color='red')
    
    ax2.set_xlabel('Time Index (Sequence Position)')
    ax2.set_ylabel('X Coordinate Value')
    ax2.set_title('Time Dimension: X Component\n(Trajectory AS Time)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Time dimension extracted - Y component  
    ax3.plot(time_indices, trajectory_data[:, 1], 'g-', linewidth=3,
            marker='s', markersize=5, alpha=0.8, label='Y(time)')
    ax3.fill_between(time_indices, trajectory_data[:, 1], alpha=0.3, color='green')
    
    ax3.set_xlabel('Time Index (Sequence Position)')
    ax3.set_ylabel('Y Coordinate Value')
    ax3.set_title('Time Dimension: Y Component\n(Trajectory AS Time)')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Combined time dimension data
    ax4.plot(time_indices, trajectory_data[:, 0], 'r-', linewidth=2, 
            marker='o', markersize=4, alpha=0.8, label='X(t)')
    ax4.plot(time_indices, trajectory_data[:, 1], 'g-', linewidth=2,
            marker='s', markersize=4, alpha=0.8, label='Y(t)')
    ax4.plot(time_indices, trajectory_data[:, 2], 'b-', linewidth=2,
            marker='^', markersize=4, alpha=0.8, label='Z(t)')
    ax4.plot(time_indices, trajectory_data[:, 4], 'm--', linewidth=2,
            marker='D', markersize=4, alpha=0.8, label='Scale(t)')
    
    ax4.set_xlabel('Time Index')
    ax4.set_ylabel('Data Value')
    ax4.set_title('Complete Time Dimension Data\n(All Components)')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Trajectory Extraction: How Spatial Path Becomes Time Dimension Data',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig03_trajectory_time_extraction.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 03 generated successfully")

if __name__ == "__main__":
    generate_figure_03()