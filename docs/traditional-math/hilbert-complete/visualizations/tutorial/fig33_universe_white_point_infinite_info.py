#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import matplotlib.patches as mpatches

def create_universe_white_point():
    """Universe as single white point containing infinite ordered information"""
    
    fig, ax = plt.subplots(1, 1, figsize=(10, 8))
    ax.set_xlim(-2, 2)
    ax.set_ylim(-2, 2)
    ax.set_aspect('equal')
    
    # Central white point - the universe
    universe_point = Circle((0, 0), 0.3, color='white', ec='black', linewidth=3)
    ax.add_patch(universe_point)
    
    # Information density visualization - concentric transparent circles
    for radius in [0.5, 0.8, 1.1, 1.4, 1.7]:
        info_circle = Circle((0, 0), radius, fill=False, ec='lightgray', 
                           linewidth=1, alpha=0.4, linestyle='--')
        ax.add_patch(info_circle)
    
    # Information potential field - radiating from center
    theta = np.linspace(0, 2*np.pi, 12, endpoint=False)
    for i, angle in enumerate(theta):
        # Different information "rays" with varying intensity
        length = 1.8
        x_end = length * np.cos(angle)
        y_end = length * np.sin(angle)
        
        # Draw information ray
        ax.arrow(0, 0, x_end*0.8, y_end*0.8, 
                head_width=0.05, head_length=0.1, 
                fc='lightgray', ec='gray', alpha=0.3, linewidth=0.8)
    
    # Mathematical symbols representing infinite information
    info_symbols = ['φ', 'π', 'e', 'ζ', '∞', '⊕', '⊗', '∮', '∇', '∂', 'Ψ', '∫']
    angles = np.linspace(0, 2*np.pi, len(info_symbols), endpoint=False)
    
    for i, (symbol, angle) in enumerate(zip(info_symbols, angles)):
        radius = 1.5
        x = radius * np.cos(angle)
        y = radius * np.sin(angle)
        ax.text(x, y, symbol, fontsize=14, ha='center', va='center',
               bbox=dict(boxstyle='circle,pad=0.1', facecolor='white', 
                        edgecolor='gray', alpha=0.7))
    
    # Central label
    ax.text(0, -0.6, 'Universe\n∞ Information', 
           fontsize=12, ha='center', va='center', weight='bold')
    
    ax.set_title('Universe as White Point: Infinite Ordered Information Source', 
                fontsize=14, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_universe_white_point()
    plt.tight_layout()
    plt.savefig('fig33_universe_white_point_infinite_info.png', dpi=300, bbox_inches='tight')
    plt.show()