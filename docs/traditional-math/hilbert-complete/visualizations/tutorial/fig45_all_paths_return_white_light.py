#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

def create_all_paths_return_white():
    """All paths return to white light ultimate unity visualization"""
    
    fig, ax = plt.subplots(1, 1, figsize=(16, 12))
    ax.set_xlim(-10, 10)
    ax.set_ylim(-10, 10)
    ax.set_aspect('equal')
    
    # Central white universe point (larger for ultimate unity)
    center = plt.Circle((0, 0), 0.6, color='white', ec='black', linewidth=5, zorder=30)
    ax.add_patch(center)
    
    # Define operation colors
    operation_colors = [
        (1.0, 0.0, 0.0),  # φ red
        (0.0, 1.0, 0.0),  # e green  
        (0.0, 0.0, 1.0),  # π blue
        (0.5, 0.0, 1.0),  # ζ purple
        (1.0, 0.5, 0.0),  # τ orange
        (0.0, 1.0, 1.0),  # γ cyan
        (1.0, 0.0, 0.5),  # √2 pink
        (0.8, 0.8, 0.2),  # L yellow
        (0.8, 0.2, 0.8),  # Extended 1
        (0.2, 0.8, 0.8),  # Extended 2
        (0.6, 0.6, 0.6),  # Extended 3
        (0.9, 0.4, 0.7),  # Extended 4
    ]
    
    # Create multiple observer paths that all return to center
    n_paths = 12
    
    for path_idx in range(n_paths):
        # Create a complex path that eventually returns to center
        n_segments = 5 + np.random.randint(3)  # 5-7 segments per path
        
        # Start from outer edge
        start_angle = 2 * np.pi * path_idx / n_paths
        start_radius = 8 + np.random.rand() * 1.5
        current_x = start_radius * np.cos(start_angle)
        current_y = start_radius * np.sin(start_angle)
        
        # Create path coordinates that spiral inward
        path_x = [current_x]
        path_y = [current_y]
        
        for seg in range(n_segments):
            # Gradually move toward center with some randomness
            progress = (seg + 1) / n_segments
            target_radius = start_radius * (1 - progress) + 0.8
            angle_offset = np.random.rand() * np.pi/3 - np.pi/6  # Random angle variation
            target_angle = start_angle + angle_offset + progress * np.pi/2
            
            next_x = target_radius * np.cos(target_angle)
            next_y = target_radius * np.sin(target_angle)
            
            path_x.append(next_x)
            path_y.append(next_y)
        
        # Final segment always goes to center
        path_x.append(0)
        path_y.append(0)
        
        # Draw the complete path with varying colors
        for i in range(len(path_x)-1):
            # Choose operation color
            color_idx = (path_idx * 3 + i) % len(operation_colors)
            segment_color = operation_colors[color_idx]
            
            # Add some transparency variation
            alpha = 0.6 + 0.3 * np.sin(i * np.pi / 4)
            
            # Draw segment
            ax.plot([path_x[i], path_x[i+1]], [path_y[i], path_y[i+1]], 
                   color=segment_color, linewidth=2.5, alpha=alpha, zorder=10)
            
            # Draw white points at junctions
            if i < len(path_x)-2:  # Don't draw point at center (already exists)
                white_point = plt.Circle((path_x[i+1], path_y[i+1]), 0.08, 
                                       color='white', ec='black', linewidth=1, zorder=15)
                ax.add_patch(white_point)
    
    # Draw arrows pointing toward center to emphasize convergence
    arrow_angles = np.linspace(0, 2*np.pi, 24, endpoint=False)
    for angle in arrow_angles:
        start_radius = 9.5
        end_radius = 7.5
        start_x = start_radius * np.cos(angle)
        start_y = start_radius * np.sin(angle)
        end_x = end_radius * np.cos(angle)
        end_y = end_radius * np.sin(angle)
        
        ax.arrow(start_x, start_y, end_x-start_x, end_y-start_y,
                head_width=0.2, head_length=0.3, fc='gray', ec='gray', alpha=0.4)
    
    # Concentric circles showing convergence layers
    for radius in [3, 6, 9]:
        circle = plt.Circle((0, 0), radius, fill=False, ec='silver', 
                          linewidth=1, alpha=0.3, linestyle=':', zorder=5)
        ax.add_patch(circle)
    
    # Unity principles
    unity_text = 'Unity Principles:\n• All paths lead home\n• Infinite diversity\n• Ultimate convergence\n• Mathematical harmony\n• Complete freedom\n• Perfect unity'
    ax.text(-9.5, 7, unity_text, fontsize=12, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow', alpha=0.9))
    
    # Convergence explanation
    convergence_text = 'Convergence Mathematics:\n• η^(R)(∞;m) → unity\n• All operations → white\n• Infinite → finite\n• Complex → simple\n• Many → one'
    ax.text(6.5, 7, convergence_text, fontsize=12, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.5', facecolor='lightcyan', alpha=0.9))
    
    # Central labels
    ax.text(0, -0.8, 'White Light\nUnity', fontsize=12, weight='bold', ha='center', va='center')
    ax.text(0, 0.8, '∞ → 1', fontsize=14, weight='bold', ha='center', va='center')
    
    ax.set_title('Ultimate Unity: All Mathematical Operations Return to White Light', 
                fontsize=16, weight='bold', pad=30)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_all_paths_return_white()
    plt.tight_layout()
    plt.savefig('fig45_all_paths_return_white_light.png', dpi=300, bbox_inches='tight')
    plt.show()