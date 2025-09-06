#!/usr/bin/env python3

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import sys
import os

# Import math functions
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from recursive_math_functions import recursive_math

def create_gamma_logarithmic_growth():
    """γ (Euler-Mascheroni) constant logarithmic growth pattern visualization"""
    
    fig, ax = plt.subplots(1, 1, figsize=(12, 10))
    ax.set_xlim(-8, 8)
    ax.set_ylim(-6, 6)
    ax.set_aspect('equal')
    
    # Central white universe point
    center = plt.Circle((0, 0), 0.3, color='white', ec='black', linewidth=3, zorder=20)
    ax.add_patch(center)
    
    # Generate logarithmic spiral path for γ constant
    n_points = 15
    t = np.linspace(0.5, 3.5, n_points)  # Parameter for spiral
    
    # Logarithmic spiral: r = a * e^(bt)
    a = 0.5
    b = 0.4
    r = a * np.exp(b * t)
    
    # Convert to Cartesian coordinates
    angles = t * np.pi  # Angle increases with t
    obs_x = r * np.cos(angles)
    obs_y = r * np.sin(angles)
    
    # Ensure points stay within bounds
    max_radius = 6
    for i in range(len(obs_x)):
        if np.sqrt(obs_x[i]**2 + obs_y[i]**2) > max_radius:
            scale = max_radius / np.sqrt(obs_x[i]**2 + obs_y[i]**2)
            obs_x[i] *= scale
            obs_y[i] *= scale
    
    # Draw white information points
    for i in range(n_points):
        white_point = plt.Circle((obs_x[i], obs_y[i]), 0.18, 
                               color='white', ec='black', linewidth=2, zorder=15)
        ax.add_patch(white_point)
    
    # Draw γ operation lines between points
    for i in range(n_points-1):
        # Calculate γ-related intensity based on harmonic series difference
        k = i + 1
        harmonic_partial = sum(1/j for j in range(1, k+1))
        gamma_approx = harmonic_partial - np.log(k) if k > 1 else 0.5772
        intensity = min(0.9, abs(gamma_approx))
        
        # Cyan γ line segment
        ax.plot([obs_x[i], obs_x[i+1]], [obs_y[i], obs_y[i+1]], 
               color=(0.0, intensity, intensity), linewidth=3, alpha=0.8, zorder=10)
        
        # γ operation label
        mid_x = (obs_x[i] + obs_x[i+1]) / 2
        mid_y = (obs_y[i] + obs_y[i+1]) / 2
        ax.text(mid_x, mid_y, 'γ', fontsize=10, weight='bold', 
               ha='center', va='center', color='darkcyan',
               bbox=dict(boxstyle='circle,pad=0.1', facecolor='cyan', alpha=0.7))
    
    # Connect all points to center with lighter γ lines
    for i in range(n_points):
        ax.plot([0, obs_x[i]], [0, obs_y[i]], 
               color='cyan', linewidth=1, alpha=0.4, zorder=5)
    
    # Mathematical properties annotation
    ax.text(-7, 4.5, 'γ ≈ 0.5772156649', fontsize=14, weight='bold', 
           ha='left', va='center')
    ax.text(-7, 3.8, 'Euler-Mascheroni Constant', fontsize=12, 
           ha='left', va='center')
    
    # Mathematical definition
    definition_text = 'γ = lim(H_n - ln n)\nn→∞\n\nH_n = Σ(1/k)\nk=1 to n'
    ax.text(-7, 2.5, definition_text, fontsize=11, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='lightcyan', alpha=0.8))
    
    # Logarithmic growth explanation
    growth_text = 'Logarithmic Growth:\n• Harmonic series\n• Natural logarithm\n• Asymptotic difference'
    ax.text(5, 4, growth_text, fontsize=10, ha='left', va='center',
           bbox=dict(boxstyle='round,pad=0.4', facecolor='lightblue', alpha=0.8))
    
    # Draw logarithmic reference curves
    x_ref = np.linspace(0.1, 6, 100)
    y_log = np.log(x_ref)
    y_harmonic = np.array([sum(1/k for k in range(1, int(x)+1)) for x in x_ref])
    
    # Logarithmic curve (reference)
    ax.plot(x_ref, y_log-2, '--', color='gray', alpha=0.5, linewidth=1, label='ln(x)')
    ax.plot(x_ref, y_harmonic-2, '--', color='lightgray', alpha=0.5, linewidth=1, label='H_x')
    
    # Central label
    ax.text(0, -5.5, 'γ Constant: Logarithmic Growth Information Encoding', 
           fontsize=14, weight='bold', ha='center', va='center')
    
    ax.set_title('γ (Euler-Mascheroni) Constant: Asymptotic Growth Rate Encoding', 
                fontsize=14, weight='bold', pad=20)
    ax.axis('off')
    
    return fig

if __name__ == "__main__":
    fig = create_gamma_logarithmic_growth()
    plt.tight_layout()
    plt.savefig('fig40_gamma_constant_logarithmic_growth.png', dpi=300, bbox_inches='tight')
    plt.show()