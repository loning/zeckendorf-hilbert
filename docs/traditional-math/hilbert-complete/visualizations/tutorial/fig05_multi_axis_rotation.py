#!/usr/bin/env python3
"""
Figure 05: Multi-Axis Earth Rotation with Scaling
Same Earth + Same Observer Point → Different Time Trajectories
Due to different rotation axes and scaling patterns
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def rotate_point_around_axis(point, axis, angle):
    """Rotate 3D point around arbitrary axis by given angle"""
    # Rodrigues' rotation formula
    axis = axis / np.linalg.norm(axis)  # Normalize axis
    cos_angle = np.cos(angle)
    sin_angle = np.sin(angle)
    
    # Rotation matrix using Rodrigues' formula
    cross_matrix = np.array([
        [0, -axis[2], axis[1]],
        [axis[2], 0, -axis[0]], 
        [-axis[1], axis[0], 0]
    ])
    
    rotation_matrix = (cos_angle * np.eye(3) + 
                      sin_angle * cross_matrix +
                      (1 - cos_angle) * np.outer(axis, axis))
    
    return rotation_matrix @ point

def generate_figure_05():
    """Generate single figure: Multi-axis rotation effects"""
    
    fig = plt.figure(figsize=(20, 16))
    
    # INVARIANT: Observer point position on Earth (relative coordinates)
    lat = np.pi/4  # 45°N latitude (NEVER changes)
    lon = np.pi/3  # 60°E longitude (NEVER changes)
    
    # Initial observer point in Cartesian coordinates
    observer_point = np.array([
        np.cos(lat) * np.cos(lon),
        np.cos(lat) * np.sin(lon),
        np.sin(lat)
    ])
    
    # Define different rotation scenarios with unique colors and accurate math
    rotation_scenarios = [
        {
            'title': 'Standard Z-axis\n(Normal rotation)',
            'axis': np.array([0, 0, 1]),
            'color': 'royalblue',
            'modulation': 'standard',
            'subplot': 331
        },
        {
            'title': 'Standard X-axis\n(Tumbling)',
            'axis': np.array([1, 0, 0]),
            'color': 'crimson', 
            'modulation': 'standard',
            'subplot': 332
        },
        {
            'title': 'Standard Y-axis\n(Rolling)',
            'axis': np.array([0, 1, 0]), 
            'color': 'forestgreen',
            'modulation': 'standard',
            'subplot': 333
        },
        {
            'title': 'Diagonal axis\n(Complex tumbling)',
            'axis': np.array([1, 1, 1]),
            'color': 'darkorange',
            'modulation': 'standard',
            'subplot': 334
        },
        {
            'title': 'φ-modulated Z-axis\n(Fibonacci pattern)',
            'axis': np.array([0, 0, 1]),
            'color': 'gold',
            'modulation': 'fibonacci',
            'subplot': 335
        },
        {
            'title': 'e-modulated X-axis\n(Factorial pattern)',
            'axis': np.array([1, 0, 0]),
            'color': 'mediumseagreen',
            'modulation': 'factorial',
            'subplot': 336
        },
        {
            'title': 'π-modulated Y-axis\n(Leibniz pattern)', 
            'axis': np.array([0, 1, 0]),
            'color': 'mediumpurple',
            'modulation': 'leibniz',
            'subplot': 337
        },
        {
            'title': 'Combined modulation\n(Multi-mode)',
            'axis': np.array([1, 0.5, 0.8]),
            'color': 'darkslategray',
            'modulation': 'combined',
            'subplot': 338
        }
    ]
    
    # Generate trajectories for each scenario
    n_steps = 40
    
    for scenario in rotation_scenarios:
        ax = fig.add_subplot(scenario['subplot'], projection='3d')
        
        # Draw Earth sphere (INVARIANT)
        u = np.linspace(0, 2*np.pi, 15)
        v = np.linspace(0, np.pi, 10) 
        earth_x = np.outer(np.cos(u), np.sin(v))
        earth_y = np.outer(np.sin(u), np.sin(v))
        earth_z = np.outer(np.ones(np.size(u)), np.cos(v))
        
        ax.plot_surface(earth_x, earth_y, earth_z, alpha=0.4, color='lightblue')
        
        # Generate trajectory for this rotation scenario
        trajectory_x = []
        trajectory_y = []
        trajectory_z = []
        scales = []
        
        for i in range(n_steps):
            # Calculate rotation angle and scale for this step
            # Use accurate mathematical sequences based on modulation type
            if scenario['modulation'] == 'fibonacci':
                fib_seq = recursive_math.fibonacci_sequence(min(n_steps, 20))
                if i < len(fib_seq):
                    modulation_factor = fib_seq[i] / max(fib_seq)
                else:
                    modulation_factor = 1
                angle = i * 2*np.pi/n_steps * (1 + modulation_factor * 0.5)
                scale = 1 + 0.2 * modulation_factor
                
            elif scenario['modulation'] == 'factorial':
                fact_seq = recursive_math.factorial_sequence(min(n_steps, 15))
                if i < len(fact_seq):
                    modulation_factor = fact_seq[i] * 50  # Scale up small factorials
                else:
                    modulation_factor = fact_seq[-1] * 50
                angle = i * 2*np.pi/n_steps * (1 + modulation_factor)
                scale = 1 + 0.3 * min(modulation_factor, 1)  # Cap scaling
                
            elif scenario['modulation'] == 'leibniz':
                leibniz_seq = recursive_math.leibniz_sequence(min(n_steps, 25))
                if i < len(leibniz_seq):
                    modulation_factor = leibniz_seq[i]
                else:
                    modulation_factor = 0
                angle = i * 2*np.pi/n_steps * (1 + modulation_factor * 2)
                scale = 1 + 0.15 * abs(modulation_factor) * 3
                
            elif scenario['modulation'] == 'combined':
                # Accurate combination of all three
                if i < 10:
                    fib_seq = recursive_math.fibonacci_sequence(10)
                    modulation_factor = fib_seq[i] / max(fib_seq) if i < len(fib_seq) else 0
                elif i < 20:
                    fact_seq = recursive_math.factorial_sequence(10)
                    idx = i - 10
                    modulation_factor = fact_seq[idx] * 20 if idx < len(fact_seq) else 0
                else:
                    leibniz_seq = recursive_math.leibniz_sequence(10)
                    idx = i - 20
                    modulation_factor = leibniz_seq[idx] if idx < len(leibniz_seq) else 0
                
                angle = i * 2*np.pi/n_steps * (1 + abs(modulation_factor))
                scale = 1 + 0.2 * abs(modulation_factor)
                
            else:  # standard
                angle = i * 2*np.pi/n_steps
                scale = 1 + 0.1 * np.sin(i * 0.3)  # Gentle scaling
            
            # Apply rotation around specified axis
            rotated_point = rotate_point_around_axis(observer_point, scenario['axis'], angle)
            
            # Apply scaling
            final_point = rotated_point * scale
            
            trajectory_x.append(final_point[0])
            trajectory_y.append(final_point[1]) 
            trajectory_z.append(final_point[2])
            scales.append(scale)
        
        # Plot trajectory with color gradient
        for i in range(len(trajectory_x)-1):
            alpha = 0.4 + 0.6 * i / len(trajectory_x)
            ax.plot([trajectory_x[i], trajectory_x[i+1]],
                   [trajectory_y[i], trajectory_y[i+1]], 
                   [trajectory_z[i], trajectory_z[i+1]],
                   color=scenario['color'], linewidth=3, alpha=alpha)
        
        # Mark start and end
        ax.scatter([trajectory_x[0]], [trajectory_y[0]], [trajectory_z[0]], 
                  c='green', s=100, edgecolor='black', linewidth=1)
        ax.scatter([trajectory_x[-1]], [trajectory_y[-1]], [trajectory_z[-1]],
                  c='red', s=100, edgecolor='black', linewidth=1)
        
        # Mark INVARIANT observer point on Earth surface
        ax.scatter([observer_point[0]], [observer_point[1]], [observer_point[2]],
                  c='yellow', s=150, marker='*', edgecolor='black', linewidth=2)
        
        ax.set_title(scenario['title'], fontsize=10, weight='bold')
        ax.set_box_aspect([1,1,1])
        ax.grid(True, alpha=0.2)
        
        # Set equal limits for comparison
        ax.set_xlim(-1.5, 1.5)
        ax.set_ylim(-1.5, 1.5)
        ax.set_zlim(-1.5, 1.5)
    
    # Summary subplot - minimal text
    ax9 = fig.add_subplot(339)
    
    ax9.text(0.5, 0.7, 'Same Earth + Same Point', ha='center', va='center',
            fontsize=14, weight='bold', transform=ax9.transAxes)
    ax9.text(0.5, 0.5, '↓', ha='center', va='center',
            fontsize=20, weight='bold', transform=ax9.transAxes)
    ax9.text(0.5, 0.3, '8 Different Time Trajectories', ha='center', va='center',
            fontsize=14, weight='bold', transform=ax9.transAxes)
    ax9.axis('off')
    
    plt.suptitle('Same Earth + Same Observer Point → 8 Different Time Trajectories\n(Due to Different Rotation Axes and Scaling Patterns)',
                fontsize=16, weight='bold', y=0.98)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig05_multi_axis_rotation.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 05 generated successfully")

if __name__ == "__main__":
    generate_figure_05()