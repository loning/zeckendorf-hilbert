#!/usr/bin/env python3
"""
Figure 21: Data Slicing Mathematical Principle
Show how observers slice holographic core data with their time curves
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_21():
    """Generate single figure: Data Slicing Principle"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Holographic core with rich data structure
    ax1.set_aspect('equal')
    
    # Create holographic data visualization
    theta = np.linspace(0, 2*np.pi, 100)
    r = np.linspace(0, 2, 50)
    THETA, R = np.meshgrid(theta, r)
    
    # Rich holographic data pattern
    Z = (3 + 2*np.sin(THETA*3) + np.cos(THETA*5) + 0.8*np.sin(THETA*7) + 
         0.5*np.cos(R*4) + 0.3*np.sin(R*6))
    
    # Plot as contour to show data richness
    contour = ax1.contour(R*np.cos(THETA), R*np.sin(THETA), Z, levels=15, 
                         colors='gold', alpha=0.6, linewidths=1)
    ax1.contourf(R*np.cos(THETA), R*np.sin(THETA), Z, levels=15, 
                cmap='YlOrBr', alpha=0.3)
    
    # Core boundary
    core_boundary = Circle((0, 0), 2, fill=False, color='black', linewidth=3)
    ax1.add_patch(core_boundary)
    
    ax1.set_xlim(-2.5, 2.5)
    ax1.set_ylim(-2.5, 2.5)
    ax1.set_title('Holographic Core Data\n(Contains ALL possible information)')
    
    # Top right: Observer's slicing curve
    ax2.set_aspect('equal')
    
    # Same core
    core2 = Circle((0, 0), 2, fill=False, color='gold', linewidth=2, alpha=0.8)
    ax2.add_patch(core2)
    
    # Observer's time curve (φ-mode)
    fib_seq = recursive_math.fibonacci_sequence(8)
    slice_curve_x = []
    slice_curve_y = []
    
    for i, fib_val in enumerate(fib_seq):
        angle = i * np.pi / 3
        radius = 0.5 + fib_val / max(fib_seq) * 1.3
        x = radius * np.cos(angle)
        y = radius * np.sin(angle)
        slice_curve_x.append(x)
        slice_curve_y.append(y)
    
    # Plot slicing curve
    ax2.plot(slice_curve_x, slice_curve_y, 'red', linewidth=4, alpha=0.9)
    
    # Show slicing points
    for i, (x, y) in enumerate(zip(slice_curve_x, slice_curve_y)):
        ax2.plot(x, y, 'ro', markersize=10, markeredgecolor='black', markeredgewidth=1)
        
        # Slicing line to core center
        ax2.plot([x, 0], [y, 0], 'red', linestyle=':', alpha=0.6, linewidth=2)
    
    ax2.set_xlim(-2.5, 2.5) 
    ax2.set_ylim(-2.5, 2.5)
    ax2.set_title('Observer Slicing Curve\n(φ-mode time coordinate)')
    
    # Bottom left: Extracted data from slicing
    # Sample the holographic core at slicing points
    sampling_points = list(zip(slice_curve_x, slice_curve_y))
    extracted_data = recursive_math.sample_holographic_core(sampling_points)
    
    ax3.plot(range(len(extracted_data)), extracted_data, 'o-', color='red', 
            linewidth=3, markersize=6, markeredgecolor='black', markeredgewidth=0.5)
    ax3.fill_between(range(len(extracted_data)), extracted_data, alpha=0.3, color='red')
    
    ax3.set_xlabel('Slicing Point Index (Time)')
    ax3.set_ylabel('Extracted Data Value')
    ax3.set_title('Sliced Data Results\n(Observer\'s extracted reality)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Different slicing patterns
    ax4.set_aspect('equal')
    
    # Same core
    core4 = Circle((0, 0), 1.5, fill=False, color='gold', linewidth=2)
    ax4.add_patch(core4)
    
    # Three different slicing patterns
    slicing_patterns = [
        {'angles': np.linspace(0, 2*np.pi, 8), 'color': 'red', 'label': 'φ-pattern'},
        {'angles': np.linspace(0, np.pi, 6), 'color': 'green', 'label': 'e-pattern'},
        {'angles': np.linspace(0, 4*np.pi/3, 7), 'color': 'purple', 'label': 'π-pattern'}
    ]
    
    for pattern in slicing_patterns:
        for angle in pattern['angles']:
            x_end = 1.5 * np.cos(angle)
            y_end = 1.5 * np.sin(angle) 
            ax4.plot([0, x_end], [0, y_end], color=pattern['color'], 
                    alpha=0.7, linewidth=2)
            ax4.plot(x_end, y_end, 'o', color=pattern['color'], markersize=6,
                    markeredgecolor='black', markeredgewidth=0.5)
    
    ax4.set_xlim(-2, 2)
    ax4.set_ylim(-2, 2)
    ax4.set_title('Different Slicing Patterns\n(Different observer modes)')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Data Slicing Principle: How Time Curves Extract Different Reality Data from Same Core',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig21_data_slicing_principle.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 21 generated successfully")

if __name__ == "__main__":
    generate_figure_21()