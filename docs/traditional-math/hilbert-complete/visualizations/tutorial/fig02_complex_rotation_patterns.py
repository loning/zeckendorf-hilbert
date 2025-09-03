#!/usr/bin/env python3
"""
Figure 02: Complex Rotation Patterns
Show how different rotation patterns create different time data
while Earth and observer point remain invariant
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 12

def generate_figure_02():
    """Generate single figure: Complex Rotation Patterns"""
    
    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(18, 12))
    
    # INVARIANT parameters
    lat = np.pi/4  # Observer latitude (NEVER changes)
    lon = np.pi/3  # Observer longitude (NEVER changes)
    
    # φ-mode rotation: Fibonacci-modulated
    n_steps_phi = 30
    fib_sequence = recursive_math.fibonacci_sequence(n_steps_phi)
    
    phi_trajectory_x = []
    phi_trajectory_y = []
    cumulative_rotation = 0
    
    for i, fib_val in enumerate(fib_sequence):
        # Use Fibonacci values to modulate rotation speed
        rotation_increment = fib_val / 100  # Normalize Fibonacci values
        cumulative_rotation += rotation_increment
        
        # Earth scaling based on Fibonacci (but Earth geometry unchanged)
        earth_scale = 1 + 0.1 * (fib_val / max(fib_sequence))
        
        # Observer point trajectory (relative position on Earth unchanged)
        x = earth_scale * np.cos(lat) * np.cos(lon + cumulative_rotation)
        y = earth_scale * np.cos(lat) * np.sin(lon + cumulative_rotation)
        
        phi_trajectory_x.append(x)
        phi_trajectory_y.append(y)
    
    # Plot φ-mode
    ax1.set_aspect('equal')
    ax1.plot(phi_trajectory_x, phi_trajectory_y, 'gold', linewidth=3, alpha=0.8)
    ax1.scatter(phi_trajectory_x, phi_trajectory_y, c=range(len(phi_trajectory_x)), 
               cmap='plasma', s=40, alpha=0.8, edgecolors='black', linewidths=0.5)
    
    # Show start and end
    ax1.plot(phi_trajectory_x[0], phi_trajectory_y[0], 'go', markersize=12, 
            markeredgecolor='black', markeredgewidth=2)
    ax1.plot(phi_trajectory_x[-1], phi_trajectory_y[-1], 'ro', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    
    ax1.set_title('φ-mode: Fibonacci-Modulated\nRotation Pattern')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    
    # e-mode rotation: Factorial-modulated
    n_steps_e = 25
    factorial_sequence = recursive_math.factorial_sequence(n_steps_e)
    
    e_trajectory_x = []
    e_trajectory_y = []
    cumulative_rotation = 0
    
    for i, fact_val in enumerate(factorial_sequence):
        # Use factorial values to modulate rotation
        rotation_increment = (1 + fact_val) * 0.3
        cumulative_rotation += rotation_increment
        
        # Earth scaling based on factorial
        earth_scale = 1 + 0.2 * fact_val
        
        x = earth_scale * np.cos(lat) * np.cos(lon + cumulative_rotation)
        y = earth_scale * np.cos(lat) * np.sin(lon + cumulative_rotation)
        
        e_trajectory_x.append(x)
        e_trajectory_y.append(y)
    
    # Plot e-mode
    ax2.set_aspect('equal')
    ax2.plot(e_trajectory_x, e_trajectory_y, 'green', linewidth=3, alpha=0.8)
    ax2.scatter(e_trajectory_x, e_trajectory_y, c=range(len(e_trajectory_x)),
               cmap='viridis', s=40, alpha=0.8, edgecolors='black', linewidths=0.5)
    
    ax2.plot(e_trajectory_x[0], e_trajectory_y[0], 'go', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    ax2.plot(e_trajectory_x[-1], e_trajectory_y[-1], 'ro', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    
    ax2.set_title('e-mode: Factorial-Modulated\nRotation Pattern')
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(-1.5, 1.5)
    ax2.set_ylim(-1.5, 1.5)
    
    # π-mode rotation: Leibniz-modulated
    n_steps_pi = 20
    leibniz_sequence = recursive_math.leibniz_sequence(n_steps_pi)
    
    pi_trajectory_x = []
    pi_trajectory_y = []
    cumulative_rotation = 0
    
    for i, leibniz_val in enumerate(leibniz_sequence):
        # Use Leibniz values to modulate rotation (handle oscillation)
        rotation_increment = 0.4 + leibniz_val * 0.2
        cumulative_rotation += rotation_increment
        
        # Earth scaling based on Leibniz oscillation
        earth_scale = 1 + 0.1 * abs(leibniz_val)
        
        x = earth_scale * np.cos(lat) * np.cos(lon + cumulative_rotation)
        y = earth_scale * np.cos(lat) * np.sin(lon + cumulative_rotation)
        
        pi_trajectory_x.append(x)
        pi_trajectory_y.append(y)
    
    # Plot π-mode
    ax3.set_aspect('equal')
    ax3.plot(pi_trajectory_x, pi_trajectory_y, 'purple', linewidth=3, alpha=0.8)
    ax3.scatter(pi_trajectory_x, pi_trajectory_y, c=range(len(pi_trajectory_x)),
               cmap='cool', s=40, alpha=0.8, edgecolors='black', linewidths=0.5)
    
    ax3.plot(pi_trajectory_x[0], pi_trajectory_y[0], 'go', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    ax3.plot(pi_trajectory_x[-1], pi_trajectory_y[-1], 'ro', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    
    ax3.set_title('π-mode: Leibniz-Modulated\nRotation Pattern')
    ax3.grid(True, alpha=0.3)
    ax3.set_xlim(-1.5, 1.5)
    ax3.set_ylim(-1.5, 1.5)
    
    # Bottom row: Time dimension data extracted from trajectories
    
    # φ-mode time data
    ax4.plot(range(len(phi_trajectory_x)), phi_trajectory_x, 'gold', linewidth=2, 
            marker='o', markersize=4, alpha=0.8, label='φ-mode X(t)')
    ax4.plot(range(len(phi_trajectory_y)), phi_trajectory_y, 'orange', linewidth=2,
            marker='s', markersize=4, alpha=0.8, label='φ-mode Y(t)')
    
    ax4.set_xlabel('Time Step')
    ax4.set_ylabel('Coordinate Value') 
    ax4.set_title('φ-mode Time Dimension Data\n(Growth Pattern)')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    # e-mode time data
    ax5.plot(range(len(e_trajectory_x)), e_trajectory_x, 'green', linewidth=2,
            marker='o', markersize=4, alpha=0.8, label='e-mode X(t)')
    ax5.plot(range(len(e_trajectory_y)), e_trajectory_y, 'darkgreen', linewidth=2,
            marker='s', markersize=4, alpha=0.8, label='e-mode Y(t)')
    
    ax5.set_xlabel('Time Step')
    ax5.set_ylabel('Coordinate Value')
    ax5.set_title('e-mode Time Dimension Data\n(Rational Pattern)')
    ax5.legend()
    ax5.grid(True, alpha=0.3)
    
    # π-mode time data
    ax6.plot(range(len(pi_trajectory_x)), pi_trajectory_x, 'purple', linewidth=2,
            marker='o', markersize=4, alpha=0.8, label='π-mode X(t)')
    ax6.plot(range(len(pi_trajectory_y)), pi_trajectory_y, 'magenta', linewidth=2,
            marker='s', markersize=4, alpha=0.8, label='π-mode Y(t)')
    ax6.axhline(y=0, color='black', linestyle='-', alpha=0.3)
    
    ax6.set_xlabel('Time Step')
    ax6.set_ylabel('Coordinate Value')
    ax6.set_title('π-mode Time Dimension Data\n(Dialectical Pattern)')
    ax6.legend()
    ax6.grid(True, alpha=0.3)
    
    plt.suptitle('Same Earth + Same Observer Point → Different Time Dimension Data\n(Based on Different Rotation Observation Modes)', 
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig01_earth_rotation_intro.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 01 generated successfully")

if __name__ == "__main__":
    generate_figure_01()