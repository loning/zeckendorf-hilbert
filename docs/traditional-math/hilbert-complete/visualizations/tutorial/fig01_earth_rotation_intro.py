#!/usr/bin/env python3
"""
Figure 01: Earth Rotation Analogy Introduction
The perfect metaphor for understanding recursive mother space
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

plt.style.use('default')
plt.rcParams['font.size'] = 13

def generate_figure_01():
    """Generate single figure: Earth Rotation Introduction"""
    
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Create Earth sphere with precise geometry
    u = np.linspace(0, 2 * np.pi, 40)
    v = np.linspace(0, np.pi, 30)
    earth_x = np.outer(np.cos(u), np.sin(v))
    earth_y = np.outer(np.sin(u), np.sin(v))
    earth_z = np.outer(np.ones(np.size(u)), np.cos(v))
    
    # Plot Earth with beautiful surface
    ax.plot_surface(earth_x, earth_y, earth_z, alpha=0.7, color='lightblue', 
                   edgecolor='none', shade=True)
    
    # Observer point on Earth (INVARIANT position)
    lat = np.pi/4  # 45° North latitude
    lon = np.pi/3  # 60° East longitude
    
    point_x = np.cos(lat) * np.cos(lon)
    point_y = np.cos(lat) * np.sin(lon)
    point_z = np.sin(lat)
    
    # Mark the observer point
    ax.scatter([point_x], [point_y], [point_z], c='red', s=200, 
              edgecolor='black', linewidth=2, alpha=1.0)
    
    # Earth's rotation axis
    axis_z = np.linspace(-1.3, 1.3, 20)
    axis_x = np.zeros_like(axis_z)
    axis_y = np.zeros_like(axis_z)
    ax.plot(axis_x, axis_y, axis_z, 'k-', linewidth=4, alpha=0.8)
    
    # Rotation arrow
    arrow_angles = np.linspace(0, 1.5*np.pi, 30)
    arrow_radius = 1.2
    arrow_x = arrow_radius * np.cos(arrow_angles)
    arrow_y = arrow_radius * np.sin(arrow_angles)
    arrow_z = np.ones_like(arrow_angles) * 0.8
    
    ax.plot(arrow_x, arrow_y, arrow_z, 'orange', linewidth=4, alpha=0.9)
    
    # Arrow head
    ax.scatter([arrow_x[-1]], [arrow_y[-1]], [arrow_z[-1]], 
              c='orange', s=300, marker='>', alpha=1.0)
    
    # Labels and annotations
    ax.text(0, 0, 1.6, 'Rotation', ha='center', va='center', 
           fontsize=16, weight='bold', color='orange')
    ax.text(point_x*1.4, point_y*1.4, point_z*1.4, 'Observer\nPoint', 
           ha='center', va='center', fontsize=14, weight='bold', color='red')
    ax.text(0, 0, -1.6, 'EARTH\n(Invariant Core)', ha='center', va='center', 
           fontsize=14, weight='bold', color='blue')
    
    ax.set_xlabel('X Axis')
    ax.set_ylabel('Y Axis')
    ax.set_zlabel('Z Axis')
    ax.set_title('Earth Rotation Analogy:\nFoundation for Recursive Mother Space', 
                fontsize=16, weight='bold', pad=30)
    
    # Perfect cube aspect ratio
    ax.set_box_aspect([1,1,1])
    ax.grid(True, alpha=0.2)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig01_earth_rotation_intro.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 01 generated: Earth Rotation Introduction")

if __name__ == "__main__":
    generate_figure_01()