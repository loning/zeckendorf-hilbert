#!/usr/bin/env python3
"""
Figure 02: Earth Scaling Effects
Show how Earth can be scaled up/down but geometry stays the same
Observer point relationship to Earth never changes
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 12

def generate_figure_02():
    """Generate single figure: Earth Scaling Effects"""
    
    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(18, 12))
    
    # INVARIANT observer position (relative to Earth)
    lat = np.pi/4  # Always 45°N
    lon = np.pi/3  # Always 60°E
    
    # Different Earth scales
    earth_scales = [0.6, 0.8, 1.0, 1.2, 1.4, 1.6]
    axes = [ax1, ax2, ax3, ax4, ax5, ax6]
    colors = ['lightblue', 'blue', 'darkblue', 'navy', 'purple', 'darkviolet']
    
    trajectories = []
    
    for i, (ax, scale, color) in enumerate(zip(axes, earth_scales, colors)):
        ax.set_aspect('equal')
        
        # Earth at different scales (but same geometry)
        earth_circle = Circle((0, 0), scale, fill=False, color=color, linewidth=3)
        ax.add_patch(earth_circle)
        
        # Observer point (SAME relative position on Earth)
        point_x = scale * np.cos(lat) * np.cos(lon)
        point_y = scale * np.cos(lat) * np.sin(lon)
        
        ax.plot(point_x, point_y, 'ro', markersize=12, markeredgecolor='black', 
               markeredgewidth=2)
        
        # Generate trajectory for this scale using Fibonacci modulation
        n_rotation_steps = 20
        fib_sequence = recursive_math.fibonacci_sequence(n_rotation_steps)
        
        trajectory_x = []
        trajectory_y = []
        cumulative_angle = 0
        
        for j, fib_val in enumerate(fib_sequence):
            # Fibonacci-modulated rotation (same pattern, different scale)
            angle_increment = fib_val / 1000  # Fibonacci modulation
            cumulative_angle += angle_increment
            
            traj_x = scale * np.cos(lat) * np.cos(lon + cumulative_angle)
            traj_y = scale * np.cos(lat) * np.sin(lon + cumulative_angle)
            
            trajectory_x.append(traj_x)
            trajectory_y.append(traj_y)
        
        # Plot trajectory
        ax.plot(trajectory_x, trajectory_y, 'red', linewidth=2, alpha=0.8)
        
        # Store for comparison
        trajectories.append({
            'x': trajectory_x,
            'y': trajectory_y, 
            'scale': scale,
            'color': color
        })
        
        # Labels
        ax.set_title(f'Earth Scale: {scale:.1f}\n(Same Geometry)')
        ax.set_xlim(-2, 2)
        ax.set_ylim(-2, 2)
        ax.grid(True, alpha=0.3)
        
        # Add scale annotation
        ax.text(-1.8, 1.8, f'Scale {scale:.1f}', fontsize=11, weight='bold', 
               bbox=dict(boxstyle="round,pad=0.2", facecolor=color, alpha=0.3))
    
    plt.suptitle('Earth Scaling: Same Geometry + Same Observer → Different Trajectory Data\n(Earth geometry invariant, observer relationship invariant, only scale changes)', 
                fontsize=16, weight='bold', y=0.98)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig02_earth_scaling_effects.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 02 generated successfully")

if __name__ == "__main__":
    generate_figure_02()