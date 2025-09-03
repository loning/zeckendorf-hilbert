#!/usr/bin/env python3
"""
Figure 04: Dimension Transition from 3D Earth to 4D Hypercube
Show how Earth analogy transitions to 4D hypercube concept
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import Circle, Rectangle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 12

def generate_figure_04():
    """Generate single figure: 3D to 4D Transition"""
    
    fig = plt.figure(figsize=(20, 5))
    
    # Step 1: 1D Line (1D "universe")
    ax1 = fig.add_subplot(141)
    
    # 1D line with observer point
    line_x = np.linspace(-1, 1, 100)
    ax1.plot(line_x, np.zeros_like(line_x), 'b-', linewidth=4)
    
    # Observer point on line
    observer_1d = 0.3
    ax1.plot(observer_1d, 0, 'ro', markersize=12, markeredgecolor='black', markeredgewidth=2)
    ax1.text(observer_1d, 0.1, 'Observer', ha='center', va='bottom', fontsize=10, weight='bold')
    
    # 1D "rotation" = left/right movement
    positions_1d = [observer_1d + 0.2*np.sin(i*0.5) for i in range(10)]
    ax1.plot(positions_1d, [0.05]*len(positions_1d), 'r--', alpha=0.6, linewidth=2)
    
    ax1.set_xlim(-1.2, 1.2)
    ax1.set_ylim(-0.2, 0.2)
    ax1.set_xlabel('X Dimension')
    ax1.set_title('1D Universe:\nLine + Point')
    ax1.grid(True, alpha=0.3)
    
    # Step 2: 2D Circle (2D "Earth")
    ax2 = fig.add_subplot(142)
    ax2.set_aspect('equal')
    
    # 2D circle
    circle_2d = Circle((0, 0), 1, fill=False, color='blue', linewidth=4)
    ax2.add_patch(circle_2d)
    
    # Observer point on circle
    angle_2d = np.pi/3
    observer_2d_x = np.cos(angle_2d)
    observer_2d_y = np.sin(angle_2d)
    ax2.plot(observer_2d_x, observer_2d_y, 'ro', markersize=12, 
            markeredgecolor='black', markeredgewidth=2)
    
    # 2D rotation trajectory
    angles_2d = np.linspace(angle_2d, angle_2d + 2*np.pi, 20)
    traj_2d_x = np.cos(angles_2d)
    traj_2d_y = np.sin(angles_2d)
    ax2.plot(traj_2d_x, traj_2d_y, 'r--', alpha=0.7, linewidth=2)
    
    ax2.set_xlim(-1.3, 1.3)
    ax2.set_ylim(-1.3, 1.3)
    ax2.set_xlabel('X Dimension')
    ax2.set_ylabel('Y Dimension')
    ax2.set_title('2D Universe:\nCircle + Point')
    ax2.grid(True, alpha=0.3)
    
    # Step 3: 3D Sphere (3D Earth)
    ax3 = fig.add_subplot(143, projection='3d')
    
    # 3D sphere
    u = np.linspace(0, 2*np.pi, 20)
    v = np.linspace(0, np.pi, 15)
    sphere_x = np.outer(np.cos(u), np.sin(v))
    sphere_y = np.outer(np.sin(u), np.sin(v))
    sphere_z = np.outer(np.ones(np.size(u)), np.cos(v))
    
    ax3.plot_surface(sphere_x, sphere_y, sphere_z, alpha=0.6, color='lightblue')
    
    # Observer point on sphere
    lat, lon = np.pi/4, np.pi/3
    observer_3d_x = np.cos(lat) * np.cos(lon)
    observer_3d_y = np.cos(lat) * np.sin(lon)
    observer_3d_z = np.sin(lat)
    
    ax3.scatter([observer_3d_x], [observer_3d_y], [observer_3d_z], 
               c='red', s=150, edgecolor='black', linewidth=2)
    
    # 3D rotation trajectory
    rotation_angles = np.linspace(0, 2*np.pi, 20)
    traj_3d_x = np.cos(lat) * np.cos(lon + rotation_angles)
    traj_3d_y = np.cos(lat) * np.sin(lon + rotation_angles)
    traj_3d_z = np.sin(lat) * np.ones_like(rotation_angles)
    
    ax3.plot(traj_3d_x, traj_3d_y, traj_3d_z, 'r--', alpha=0.8, linewidth=3)
    
    ax3.set_xlabel('X')
    ax3.set_ylabel('Y')
    ax3.set_zlabel('Z')
    ax3.set_title('3D Universe:\nSphere + Point\n(Earth Analogy)')
    ax3.set_box_aspect([1,1,1])
    
    # Step 4: 4D Hypercube conceptual
    ax4 = fig.add_subplot(144)
    
    # 4D hypercube visualization concept
    ax4.text(0.5, 0.9, '4D HYPERCUBE', ha='center', va='center',
            fontsize=16, weight='bold', transform=ax4.transAxes)
    
    # Draw conceptual 4D structure
    # Inner cube (3D projection of one "face")
    inner_square = Rectangle((0.2, 0.2), 0.3, 0.3, fill=False, color='blue', linewidth=2)
    ax4.add_patch(inner_square)
    
    # Outer cube (3D projection of opposite "face")
    outer_square = Rectangle((0.4, 0.4), 0.3, 0.3, fill=False, color='darkblue', linewidth=2)
    ax4.add_patch(outer_square)
    
    # Connect corresponding vertices (4th dimension)
    connections = [
        [(0.2, 0.2), (0.4, 0.4)],  # Bottom-left
        [(0.5, 0.2), (0.7, 0.4)],  # Bottom-right
        [(0.5, 0.5), (0.7, 0.7)],  # Top-right
        [(0.2, 0.5), (0.4, 0.7)]   # Top-left
    ]
    
    for start, end in connections:
        ax4.plot([start[0], end[0]], [start[1], end[1]], 'purple', 
                linewidth=2, alpha=0.7)
    
    # Observer point in 4D
    ax4.plot(0.55, 0.55, 'ro', markersize=15, markeredgecolor='black', markeredgewidth=2)
    ax4.text(0.55, 0.45, 'Observer', ha='center', va='top', fontsize=11, weight='bold')
    
    ax4.text(0.5, 0.15, 'CONTAINS TIME DIMENSION', ha='center', va='center',
            fontsize=12, weight='bold', color='purple', transform=ax4.transAxes)
    
    ax4.set_xlim(0, 1)
    ax4.set_ylim(0, 1)
    ax4.set_title('4D Universe:\nHypercube + Point\n(Time Included)')
    ax4.axis('off')
    
    plt.suptitle('Dimensional Progression: 1D → 2D → 3D → 4D\n(Each dimension adds more complex time patterns)',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig04_dimension_transition.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 04 generated successfully")

if __name__ == "__main__":
    generate_figure_04()