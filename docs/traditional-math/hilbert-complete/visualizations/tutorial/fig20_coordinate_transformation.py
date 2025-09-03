#!/usr/bin/env python3
"""
Figure 20: Coordinate System Transformation Mathematics
Show the mathematical relationship between subjective and objective coordinates
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_20():
    """Generate single figure: Coordinate Transformation"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Subjective coordinate system
    ax1.set_aspect('equal')
    
    # Observer's personal time curve (φ-mode)
    fib_seq = recursive_math.fibonacci_sequence(10)
    time_curve_x = []
    time_curve_y = []
    
    for i, fib_val in enumerate(fib_seq):
        angle = i * np.pi / 4
        radius = 0.5 + fib_val / max(fib_seq) * 0.8
        x = radius * np.cos(angle)
        y = radius * np.sin(angle)
        time_curve_x.append(x)
        time_curve_y.append(y)
    
    # Plot personal time axis
    ax1.plot(time_curve_x, time_curve_y, 'red', linewidth=4, alpha=0.8)
    ax1.scatter(time_curve_x, time_curve_y, c=range(len(time_curve_x)), 
               cmap='Reds', s=50, alpha=0.8, edgecolor='black', linewidths=0.5)
    
    # Personal coordinate grid
    for i in range(0, len(time_curve_x), 2):
        if i < len(time_curve_x)-1:
            # Perpendicular lines
            dx = time_curve_x[i+1] - time_curve_x[i]
            dy = time_curve_y[i+1] - time_curve_y[i]
            length = np.sqrt(dx**2 + dy**2)
            if length > 0:
                perp_x = -dy / length * 0.8
                perp_y = dx / length * 0.8
                ax1.plot([time_curve_x[i] - perp_x, time_curve_x[i] + perp_x],
                        [time_curve_y[i] - perp_y, time_curve_y[i] + perp_y],
                        'red', alpha=0.4, linewidth=1)
    
    ax1.set_xlim(-2, 2)
    ax1.set_ylim(-2, 2)
    ax1.set_title('Subjective Coordinate System\n(Observer\'s Personal Framework)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Objective coordinate system
    ax2.set_aspect('equal')
    
    # Objective grid
    for i in np.arange(-2, 2.5, 0.5):
        ax2.axhline(y=i, color='blue', alpha=0.3, linewidth=1)
        ax2.axvline(x=i, color='blue', alpha=0.3, linewidth=1)
    
    # Objective axes
    ax2.arrow(0, 0, 2, 0, head_width=0.1, head_length=0.1, fc='blue', ec='blue', linewidth=3)
    ax2.arrow(0, 0, 0, 2, head_width=0.1, head_length=0.1, fc='blue', ec='blue', linewidth=3)
    
    # Same observer trajectory in objective coordinates
    objective_x = [2 + i*0.1*np.cos(i*0.3) for i in range(len(time_curve_x))]
    objective_y = [1 + i*0.1*np.sin(i*0.3) for i in range(len(time_curve_y))]
    
    ax2.plot(objective_x, objective_y, 'red', linewidth=3, alpha=0.8)
    ax2.scatter(objective_x, objective_y, c=range(len(objective_x)),
               cmap='Reds', s=50, alpha=0.8, edgecolor='black', linewidths=0.5)
    
    ax2.set_xlim(-2, 4)
    ax2.set_ylim(-2, 3)
    ax2.set_title('Objective Coordinate System\n(Mother Space Framework)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Transformation visualization
    ax3.set_aspect('equal')
    
    # Show transformation arrows between coordinate systems
    # Subjective points
    subj_points = [(time_curve_x[i], time_curve_y[i]) for i in range(0, len(time_curve_x), 3)]
    # Objective points  
    obj_points = [(objective_x[i], objective_y[i]) for i in range(0, len(objective_x), 3)]
    
    # Plot both coordinate representations
    for i, (subj_pt, obj_pt) in enumerate(zip(subj_points[:4], obj_points[:4])):
        # Subjective point
        ax3.plot(subj_pt[0]-3, subj_pt[1], 'ro', markersize=8, alpha=0.8)
        
        # Objective point
        ax3.plot(obj_pt[0], obj_pt[1], 'bo', markersize=8, alpha=0.8)
        
        # Transformation arrow
        arrow = FancyArrowPatch((subj_pt[0]-3, subj_pt[1]), (obj_pt[0], obj_pt[1]),
                              arrowstyle='->', mutation_scale=20, color='green', 
                              linewidth=2, alpha=0.7)
        ax3.add_patch(arrow)
    
    # Labels
    ax3.text(-3, 2.5, 'Subjective\nCoordinates', ha='center', va='center',
            fontsize=12, weight='bold', color='red')
    ax3.text(2, 2.5, 'Objective\nCoordinates', ha='center', va='center',
            fontsize=12, weight='bold', color='blue')
    
    ax3.set_xlim(-5, 5)
    ax3.set_ylim(-2, 3)
    ax3.set_title('Coordinate Transformation\n(Subjective ↔ Objective)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Transformation mathematics
    # Show transformation matrix concept
    transform_angles = np.linspace(0, 2*np.pi, 8)
    
    # Original vectors
    for angle in transform_angles:
        x_orig = np.cos(angle)
        y_orig = np.sin(angle)
        ax4.arrow(0, 0, x_orig, y_orig, head_width=0.05, head_length=0.05,
                 fc='blue', ec='blue', alpha=0.6, linewidth=1)
    
    # Transformed vectors (rotation + scaling)
    transform_matrix = np.array([[1.2, 0.3], [-0.2, 1.1]])  # Example transformation
    
    for angle in transform_angles:
        orig_vec = np.array([np.cos(angle), np.sin(angle)])
        transformed_vec = transform_matrix @ orig_vec
        
        ax4.arrow(0, 0, transformed_vec[0], transformed_vec[1], 
                 head_width=0.05, head_length=0.05, fc='red', ec='red', 
                 alpha=0.8, linewidth=2)
    
    ax4.set_xlim(-2, 2)
    ax4.set_ylim(-2, 2)
    ax4.set_title('Linear Transformation\n(Mathematical Framework)')
    ax4.grid(True, alpha=0.3)
    ax4.set_aspect('equal')
    
    plt.suptitle('Coordinate System Transformations: Subjective ↔ Objective Mathematical Relations',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig20_coordinate_transformation.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 20 generated successfully")

if __name__ == "__main__":
    generate_figure_20()