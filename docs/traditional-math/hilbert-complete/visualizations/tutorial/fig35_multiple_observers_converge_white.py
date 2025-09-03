#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_multiple_observers_convergence():
    """Multiple observers' colored perspectives converging back to white light"""
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))
    
    # Left panel: Individual observers with their colored perspectives
    ax1.set_xlim(-3, 3)
    ax1.set_ylim(-3, 3)
    ax1.set_aspect('equal')
    
    # Central white universe point
    universe_center = (0, 0)
    universe_circle = plt.Circle(universe_center, 0.2, color='white', 
                               ec='black', linewidth=3, zorder=20)
    ax1.add_patch(universe_circle)
    
    # Create 6 different observers around the center
    n_observers = 6
    observer_angles = np.linspace(0, 2*np.pi, n_observers, endpoint=False)
    observer_radius = 2.5
    
    observer_colors = []
    
    for i, angle in enumerate(observer_angles):
        # Observer position
        obs_x = observer_radius * np.cos(angle)
        obs_y = observer_radius * np.sin(angle)
        
        # Each observer uses different combinations of φ,e,π operations
        phi_weight = (i + 1) / n_observers
        e_weight = ((i + 2) % n_observers) / n_observers
        pi_weight = ((i + 3) % n_observers) / n_observers
        
        # Normalize weights
        total = phi_weight + e_weight + pi_weight
        phi_weight /= total
        e_weight /= total
        pi_weight /= total
        
        # Observer color based on operation weights
        obs_color = [phi_weight, e_weight, pi_weight]
        observer_colors.append(obs_color)
        
        # Draw observer as colored circle
        observer_circle = plt.Circle((obs_x, obs_y), 0.15, 
                                   color=obs_color, ec='black', linewidth=2, zorder=15)
        ax1.add_patch(observer_circle)
        
        # Draw observation line to center
        ax1.plot([obs_x, universe_center[0]], [obs_y, universe_center[1]], 
                color=obs_color, linewidth=2, alpha=0.7, zorder=5)
        
        # Observer label
        ax1.text(obs_x*1.15, obs_y*1.15, f'O{i+1}', fontsize=10, 
               ha='center', va='center', weight='bold')
    
    ax1.set_title('Individual Observers: Unique Colored Perspectives', 
                 fontsize=14, weight='bold')
    ax1.text(0, -2.7, 'White Universe Point\n∞ Information Source', 
            ha='center', va='center', fontsize=10, weight='bold')
    ax1.axis('off')
    
    # Right panel: Color convergence back to white
    ax2.set_xlim(-1, 5)
    ax2.set_ylim(-1, 3)
    ax2.set_aspect('equal')
    
    # Show color mixing process
    # Individual colors on the left
    for i, color in enumerate(observer_colors):
        y_pos = 2.5 - i * 0.4
        color_rect = plt.Rectangle((0, y_pos-0.15), 0.8, 0.3, 
                                 color=color, ec='black', linewidth=1)
        ax2.add_patch(color_rect)
        ax2.text(-0.2, y_pos, f'O{i+1}', ha='center', va='center', fontsize=10)
    
    # Mixing process arrows
    for i in range(len(observer_colors)):
        y_start = 2.5 - i * 0.4
        ax2.arrow(0.8, y_start, 0.8, 0.5 - y_start, 
                 head_width=0.05, head_length=0.1, fc='gray', ec='gray', alpha=0.6)
    
    # Combined white light on the right
    white_result = plt.Circle((2.5, 1), 0.3, color='white', 
                            ec='black', linewidth=3, zorder=10)
    ax2.add_patch(white_result)
    
    # Mathematical representation
    ax2.text(2.5, 0.4, '∑ Observers\n= White Light', 
            ha='center', va='center', fontsize=12, weight='bold')
    
    # Color addition formula
    ax2.text(1.5, 2.7, 'Color Addition:\nAll φ,e,π → White', 
            ha='center', va='center', fontsize=11)
    
    ax2.set_title('Convergence: All Colors Return to White Light', 
                 fontsize=14, weight='bold')
    ax2.axis('off')
    
    plt.tight_layout()
    return fig

if __name__ == "__main__":
    fig = create_multiple_observers_convergence()
    plt.tight_layout()
    plt.savefig('fig35_multiple_observers_converge_white.png', dpi=300, bbox_inches='tight')
    plt.show()