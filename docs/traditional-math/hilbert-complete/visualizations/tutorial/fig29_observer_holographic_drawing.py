#!/usr/bin/env python3
"""
Figure 29: Observer Holographic Drawing Process
Observer uses three operations simultaneously to draw colored lines
The line color changes reflect information decomposition via holographic principle
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from information_extraction_mathematics import info_math
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_29():
    """Generate single figure: Observer Holographic Drawing"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Observer simultaneously uses all three operations
    n_steps = 30
    
    # Generate three operation sequences
    fib_seq = recursive_math.fibonacci_sequence(n_steps)
    fact_seq = recursive_math.factorial_sequence(n_steps)  
    leibniz_seq = recursive_math.leibniz_sequence(n_steps)
    
    # Observer draws line using all three operations simultaneously
    drawing_x = []
    drawing_y = []
    line_colors = []
    
    for i in range(n_steps):
        # Position calculated using all three operations
        phi_component = fib_seq[i] if i < len(fib_seq) else fib_seq[-1]
        e_component = fact_seq[i] if i < len(fact_seq) else fact_seq[-1]
        pi_component = abs(leibniz_seq[i]) if i < len(leibniz_seq) else 0
        
        # Combine three operations for position
        x = 3 * np.cos(i * 0.3) * (phi_component / max(fib_seq))
        y = 3 * np.sin(i * 0.3) * (e_component * 100)  # Scale up factorial
        
        drawing_x.append(x)
        drawing_y.append(y)
        
        # Line color reflects three-axis information at this point
        # Normalize to RGB
        total_info = phi_component + e_component*100 + pi_component*50
        if total_info > 0:
            r = (phi_component / max(fib_seq))  # φ contribution → Red
            g = (e_component * 100) / max([e*100 for e in fact_seq])  # e contribution → Green  
            b = (pi_component * 50) / 50 if pi_component > 0 else 0  # π contribution → Blue
            
            # Ensure valid color range
            color = [max(0, min(1, r)), max(0, min(1, g)), max(0, min(1, b))]
        else:
            color = [0.5, 0.5, 0.5]  # Gray fallback
        
        line_colors.append(color)
    
    # Top left: Observer drawing process (colored line)
    ax1.set_aspect('equal')
    
    # Draw the colored line segment by segment
    for i in range(len(drawing_x)-1):
        ax1.plot([drawing_x[i], drawing_x[i+1]], [drawing_y[i], drawing_y[i+1]], 
                color=line_colors[i], linewidth=4, alpha=0.8)
    
    # Mark observer position (follows the line)
    ax1.scatter(drawing_x, drawing_y, c=line_colors, s=40, alpha=0.9,
               edgecolor='black', linewidths=0.5)
    
    # Starting and ending points
    ax1.plot(drawing_x[0], drawing_y[0], 'go', markersize=12, 
            markeredgecolor='black', markeredgewidth=2)
    ax1.plot(drawing_x[-1], drawing_y[-1], 'ro', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    
    ax1.set_xlim(-4, 4)
    ax1.set_ylim(-0.5, 0.5)
    ax1.set_xlabel('Combined φ-e Operation')
    ax1.set_ylabel('Combined Operation Result')
    ax1.set_title('Observer Draws Colored Line\n(Three operations simultaneously)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Holographic decomposition of the line
    # Extract three-axis components from the colored line
    
    # φ-axis extraction (Red component)
    phi_extracted = [color[0] for color in line_colors]
    ax2.plot(range(len(phi_extracted)), phi_extracted, 'red', linewidth=3, 
            alpha=0.8, label='φ-axis extraction')
    ax2.fill_between(range(len(phi_extracted)), phi_extracted, alpha=0.3, color='red')
    
    # e-axis extraction (Green component)  
    e_extracted = [color[1] for color in line_colors]
    ax2.plot(range(len(e_extracted)), e_extracted, 'green', linewidth=3,
            alpha=0.8, label='e-axis extraction')
    
    # π-axis extraction (Blue component)
    pi_extracted = [color[2] for color in line_colors] 
    ax2.plot(range(len(pi_extracted)), pi_extracted, 'blue', linewidth=3,
            alpha=0.8, label='π-axis extraction')
    
    ax2.set_xlabel('Time Step')
    ax2.set_ylabel('Extracted Information Intensity')
    ax2.set_title('Holographic Decomposition\n(Extract three-axis info from colored line)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Information reconstruction
    # Verify that three components can reconstruct original
    
    reconstructed_colors = []
    for i in range(len(line_colors)):
        # Reconstruct RGB from extracted components
        reconstructed = [phi_extracted[i], e_extracted[i], pi_extracted[i]]
        reconstructed_colors.append(reconstructed)
    
    # Plot original vs reconstructed
    ax3.scatter(range(len(line_colors)), [0.8]*len(line_colors), 
               c=line_colors, s=80, alpha=0.9, label='Original colors')
    ax3.scatter(range(len(reconstructed_colors)), [0.2]*len(reconstructed_colors),
               c=reconstructed_colors, s=80, alpha=0.9, label='Reconstructed colors')
    
    ax3.set_xlim(0, len(line_colors))
    ax3.set_ylim(0, 1)
    ax3.set_xlabel('Position on Line')
    ax3.set_title('Information Reconstruction\n(Holographic principle verification)')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Time-color relationship
    # Show how time progression relates to color change
    
    # Calculate color change rate
    color_changes = []
    for i in range(1, len(line_colors)):
        prev_color = np.array(line_colors[i-1])
        curr_color = np.array(line_colors[i])
        change = np.linalg.norm(curr_color - prev_color)
        color_changes.append(change)
    
    ax4.plot(range(len(color_changes)), color_changes, 'purple', linewidth=3,
            alpha=0.8, marker='o', markersize=4)
    ax4.fill_between(range(len(color_changes)), color_changes, alpha=0.3, color='purple')
    
    ax4.set_xlabel('Time Step')
    ax4.set_ylabel('Color Change Rate')
    ax4.set_title('Time-Color Relationship\n(Information change over time)')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Observer Holographic Drawing: Three Operations → Colored Line → Information Decomposition',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig29_observer_holographic_drawing.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 29 generated successfully")

if __name__ == "__main__":
    generate_figure_29()