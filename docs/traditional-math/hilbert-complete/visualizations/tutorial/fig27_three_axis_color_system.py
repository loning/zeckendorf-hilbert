#!/usr/bin/env python3
"""
Figure 27: Three-Axis Color System (φ, e, π as Color Axes)
This is not analogy - this IS the mathematical structure of information
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from spectrum_math_functions import spectrum_math
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_27():
    """Generate single figure: Three-Axis Color System"""
    
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Define the three information axes as color axes
    axis_length = 5
    
    # φ-axis (Red axis) - Fibonacci operation axis
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=6, alpha=0.9)
    ax.text(axis_length, 0, 0, 'φ-axis\n(Fibonacci Operation)', 
           fontsize=12, weight='bold', color='red', ha='left', va='center')
    
    # e-axis (Green axis) - Factorial operation axis
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=6, alpha=0.9)
    ax.text(0, axis_length, 0, 'e-axis\n(Factorial Operation)', 
           fontsize=12, weight='bold', color='green', ha='center', va='bottom')
    
    # π-axis (Blue axis) - Leibniz operation axis
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=6, alpha=0.9)
    ax.text(0, 0, axis_length, 'π-axis\n(Leibniz Operation)', 
           fontsize=12, weight='bold', color='blue', ha='center', va='bottom')
    
    # WHITE LIGHT ORIGIN - where all three axes converge to infinity
    ax.scatter([0], [0], [0], s=800, c='white', marker='*', 
              edgecolor='gold', linewidth=4, alpha=1.0)
    ax.text(0, 0, -0.5, 'WHITE LIGHT ORIGIN\n(Information Source)', 
           ha='center', va='top', fontsize=12, weight='bold', color='gold')
    
    # Show information extraction along each axis
    n_points = 20
    
    # φ-axis information points
    fib_seq = recursive_math.fibonacci_sequence(n_points)
    for i, fib_val in enumerate(fib_seq[1:8]):  # Show first 7
        position = (i+1) * 0.4
        intensity = fib_val / max(fib_seq)
        ax.scatter([position], [0], [0], s=intensity*200, c='red', 
                  alpha=0.7, edgecolor='darkred', linewidth=1)
    
    # e-axis information points
    fact_seq = recursive_math.factorial_sequence(n_points)
    for i, fact_val in enumerate(fact_seq[1:8]):
        position = (i+1) * 0.4
        intensity = fact_val * 50  # Scale up small values
        ax.scatter([0], [position], [0], s=min(intensity*200, 400), c='green',
                  alpha=0.7, edgecolor='darkgreen', linewidth=1)
    
    # π-axis information points  
    leibniz_seq = recursive_math.leibniz_sequence(n_points)
    for i, leibniz_val in enumerate(leibniz_seq[1:8]):
        position = (i+1) * 0.4
        intensity = abs(leibniz_val) * 100
        ax.scatter([0], [0], [position], s=intensity*200, c='blue',
                  alpha=0.7, edgecolor='darkblue', linewidth=1)
    
    # Information vectors in 3D color space
    # Show how different observers exist in this color space
    observers_in_color_space = [
        {'pos': [3, 1, 0.5], 'color': [1, 0.3, 0.1], 'name': 'φ-dominant'},
        {'pos': [0.8, 4, 0.3], 'color': [0.2, 1, 0.1], 'name': 'e-dominant'},
        {'pos': [0.5, 1, 3.5], 'color': [0.1, 0.3, 1], 'name': 'π-dominant'},
        {'pos': [2, 2, 2], 'color': [0.8, 0.8, 0.8], 'name': 'Balanced'},
        {'pos': [1, 3, 2], 'color': [0.3, 0.9, 0.6], 'name': 'e-π mix'},
        {'pos': [3, 0.5, 1.5], 'color': [0.9, 0.2, 0.5], 'name': 'φ-π mix'}
    ]
    
    for obs in observers_in_color_space:
        x, y, z = obs['pos']
        color = obs['color']
        
        ax.scatter([x], [y], [z], s=120, c=[color], alpha=0.9,
                  edgecolor='black', linewidth=1)
        
        # Line from origin to observer (their information vector)
        ax.plot([0, x], [0, y], [0, z], color=color, linewidth=2, alpha=0.6)
    
    # Color mixing demonstration planes
    # φ-e plane (Red-Green mixing → Yellow)
    xx, yy = np.meshgrid(np.linspace(0, 3, 10), np.linspace(0, 3, 10))
    zz = np.zeros_like(xx) + 0.1
    colors_phi_e = np.zeros((10, 10, 3))
    for i in range(10):
        for j in range(10):
            phi_intensity = xx[i,j] / 3
            e_intensity = yy[i,j] / 3
            colors_phi_e[i,j] = [phi_intensity, e_intensity, 0]
    
    ax.plot_surface(xx, yy, zz, facecolors=colors_phi_e, alpha=0.3)
    
    ax.set_xlabel('φ-axis (Fibonacci/Red)')
    ax.set_ylabel('e-axis (Factorial/Green)')
    ax.set_zlabel('π-axis (Leibniz/Blue)')
    ax.set_title('Three-Axis Information Color Space\nWhite Origin → All Information Through φ,e,π Operations',
                fontsize=14, weight='bold', pad=20)
    
    ax.set_box_aspect([1,1,1])
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig27_three_axis_color_system.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 27 generated successfully")

if __name__ == "__main__":
    generate_figure_27()