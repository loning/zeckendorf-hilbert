#!/usr/bin/env python3
"""
Figure 18: Subjective Time Coordinate Construction Details
Show how observers build their personal time coordinate systems
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_18():
    """Generate single figure: Subjective Coordinate Construction"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Observer constructs their time axis
    ax1.set_aspect('equal')
    
    # Holographic core
    core = Circle((0, 0), 1, color='gold', alpha=0.6, linewidth=2)
    ax1.add_patch(core)
    
    # Observer starting position
    observer_start = (2, 1)
    ax1.plot(observer_start[0], observer_start[1], 'ro', markersize=15,
            markeredgecolor='black', markeredgewidth=2)
    
    # Observer constructs their time curve using φ-mode
    fib_seq = recursive_math.fibonacci_sequence(12)
    time_curve_x = []
    time_curve_y = []
    
    cumulative_angle = 0
    for i, fib_val in enumerate(fib_seq):
        angle_increment = fib_val / 500
        cumulative_angle += angle_increment
        
        x = observer_start[0] + (i * 0.15) * np.cos(cumulative_angle)
        y = observer_start[1] + (i * 0.15) * np.sin(cumulative_angle)
        
        time_curve_x.append(x)
        time_curve_y.append(y)
    
    # Plot time curve construction
    ax1.plot(time_curve_x, time_curve_y, 'red', linewidth=3, alpha=0.8)
    ax1.scatter(time_curve_x, time_curve_y, c=range(len(time_curve_x)), 
               cmap='Reds', s=40, alpha=0.8, edgecolor='black', linewidths=0.5)
    
    # Show perpendicular lines (coordinate grid)
    for i in range(0, len(time_curve_x), 3):
        if i < len(time_curve_x)-1:
            # Calculate perpendicular direction
            dx = time_curve_x[i+1] - time_curve_x[i]
            dy = time_curve_y[i+1] - time_curve_y[i]
            length = np.sqrt(dx**2 + dy**2)
            if length > 0:
                perp_x = -dy / length * 0.5
                perp_y = dx / length * 0.5
                
                ax1.plot([time_curve_x[i] - perp_x, time_curve_x[i] + perp_x],
                        [time_curve_y[i] - perp_y, time_curve_y[i] + perp_y],
                        'red', alpha=0.4, linewidth=1)
    
    ax1.set_xlim(-1, 4)
    ax1.set_ylim(-1, 3)
    ax1.set_title('Observer Constructs Personal Time Axis\n(φ-mode curve)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Core sampling along time curve
    ax2.set_aspect('equal')
    
    # Same core
    core2 = Circle((0, 0), 1, color='gold', alpha=0.6, linewidth=2)
    ax2.add_patch(core2)
    
    # Observer's sampling points along their curve
    sampling_points = [(time_curve_x[i], time_curve_y[i]) for i in range(0, len(time_curve_x), 2)]
    
    # Sample holographic core data
    sampled_data = recursive_math.sample_holographic_core(sampling_points)
    
    # Show sampling lines to core
    for i, (sx, sy) in enumerate(sampling_points):
        # Line to core center
        ax2.plot([sx, 0], [sy, 0], 'gray', linestyle=':', alpha=0.6)
        
        # Sampling point
        ax2.plot(sx, sy, 'o', color='red', markersize=8, markeredgecolor='black')
        
        # Data value indicator (size represents value)
        data_size = min(abs(sampled_data[i]) * 20, 100)
        ax2.scatter([sx], [sy], s=data_size, c='blue', alpha=0.5)
    
    ax2.set_xlim(-2, 4)
    ax2.set_ylim(-2, 3)
    ax2.set_title('Sampling Core Along Time Curve\n(Data extraction process)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Extracted time series data
    time_indices = range(len(sampled_data))
    
    ax3.plot(time_indices, sampled_data, 'o-', color='red', linewidth=2,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5)
    ax3.fill_between(time_indices, sampled_data, alpha=0.3, color='red')
    
    ax3.set_xlabel('Personal Time Index')
    ax3.set_ylabel('Extracted Data Value')
    ax3.set_title('Personal Time Series\n(Observer\'s Reality Data)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Personal coordinate system established
    ax4.set_aspect('equal')
    
    # Observer's coordinate axes
    # X-axis = their time curve
    ax4.plot(time_curve_x, time_curve_y, 'red', linewidth=4, alpha=0.8)
    
    # Y-axis = perpendicular to time curve at current position
    current_pos = len(time_curve_x) // 2
    if current_pos < len(time_curve_x) - 1:
        dx = time_curve_x[current_pos+1] - time_curve_x[current_pos]
        dy = time_curve_y[current_pos+1] - time_curve_y[current_pos]
        length = np.sqrt(dx**2 + dy**2)
        if length > 0:
            perp_x = -dy / length * 1.5
            perp_y = dx / length * 1.5
            
            # Y-axis of personal coordinate system
            ax4.arrow(time_curve_x[current_pos], time_curve_y[current_pos],
                     perp_x, perp_y, head_width=0.1, head_length=0.1, 
                     fc='blue', ec='blue', linewidth=3, alpha=0.8)
    
    # Mark coordinate origin
    ax4.plot(time_curve_x[current_pos], time_curve_y[current_pos], 's', 
            color='black', markersize=12, markeredgecolor='white', markeredgewidth=2)
    
    # Core in this coordinate system
    core3 = Circle((0, 0), 1, color='gold', alpha=0.3, linewidth=1)
    ax4.add_patch(core3)
    
    ax4.set_xlim(-1, 4)
    ax4.set_ylim(-1, 3)
    ax4.set_title('Personal Coordinate System\n(Red=Time axis, Blue=Data axis)')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Subjective Coordinate System Construction: How Observers Build Personal Reality Framework',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig18_subjective_coordinate_construction.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 18 generated successfully")

if __name__ == "__main__":
    generate_figure_18()