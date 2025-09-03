#!/usr/bin/env python3
"""
Figure 11: π-mode Leibniz Series Calculation
Precise mathematical process of Leibniz alternating series and π convergence
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_11():
    """Generate single figure: π-mode Leibniz Calculation"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Generate exact Leibniz sequence
    n_terms = 25
    leibniz_sequence = recursive_math.leibniz_sequence(n_terms)
    
    # Top left: Leibniz alternating terms
    colors = ['purple' if term > 0 else 'orange' for term in leibniz_sequence]
    
    bars = ax1.bar(range(len(leibniz_sequence)), leibniz_sequence, color=colors, 
                  alpha=0.7, edgecolor='black', linewidth=1)
    
    # Zero line for reference
    ax1.axhline(y=0, color='black', linewidth=2, alpha=0.8)
    
    # Mark positive and negative terms
    for i, (bar, term) in enumerate(zip(bars[:10], leibniz_sequence[:10])):  # First 10
        sign = '+' if term > 0 else '-'
        ax1.text(i, term + 0.02*np.sign(term), sign, ha='center', 
                va='bottom' if term > 0 else 'top', fontsize=12, weight='bold')
    
    ax1.set_xlabel('Term Index k')
    ax1.set_ylabel('Leibniz Term (-1)^(k-1)/(2k-1)')
    ax1.set_title('Leibniz Alternating Series\na_k = (-1)^(k-1)/(2k-1)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: π convergence
    partial_sums, final_sum = recursive_math.pi_mode_convergence(n_terms)
    pi_target = recursive_math.pi
    
    ax2.plot(range(len(partial_sums)), partial_sums, 'o-', color='purple', 
            linewidth=3, markersize=6, markeredgecolor='black', markeredgewidth=0.5,
            label='4 × Partial Sum')
    
    # Target π line
    ax2.axhline(y=pi_target, color='red', linestyle='--', linewidth=3, alpha=0.8,
               label=f'π = {pi_target:.6f}')
    
    # Show oscillating convergence
    ax2.fill_between(range(len(partial_sums)), partial_sums, pi_target,
                    alpha=0.3, color='purple')
    
    ax2.set_xlabel('Partial Sum Index')
    ax2.set_ylabel('π Approximation')
    ax2.set_title('π-mode Oscillating Convergence\n4×Σ((-1)^(k-1)/(2k-1)) → π')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Oscillation pattern analysis
    oscillations = [partial_sums[i] - pi_target for i in range(len(partial_sums))]
    
    ax3.plot(range(len(oscillations)), oscillations, 'o-', color='darkorchid', 
            linewidth=2, markersize=4, markeredgecolor='black', markeredgewidth=0.5)
    ax3.axhline(y=0, color='black', linestyle='-', alpha=0.8)
    
    # Show decreasing oscillation amplitude
    upper_envelope = [abs(osc) for osc in oscillations]
    lower_envelope = [-abs(osc) for osc in oscillations]
    ax3.plot(range(len(upper_envelope)), upper_envelope, '--', color='red', 
            alpha=0.6, linewidth=1)
    ax3.plot(range(len(lower_envelope)), lower_envelope, '--', color='red',
            alpha=0.6, linewidth=1)
    
    ax3.set_xlabel('Oscillation Index')
    ax3.set_ylabel('Deviation from π')
    ax3.set_title('π-mode Oscillation Pattern\n(Decreasing Amplitude)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Unit circle visualization
    theta = np.linspace(0, 2*np.pi, 100)
    unit_circle_x = np.cos(theta)
    unit_circle_y = np.sin(theta)
    
    ax4.plot(unit_circle_x, unit_circle_y, 'purple', linewidth=3, alpha=0.8)
    ax4.set_aspect('equal')
    
    # Mark special points where Leibniz series relates to circle
    special_angles = [0, np.pi/4, np.pi/2, 3*np.pi/4, np.pi, 5*np.pi/4, 3*np.pi/2, 7*np.pi/4]
    for angle in special_angles:
        x, y = np.cos(angle), np.sin(angle)
        ax4.plot(x, y, 'o', markersize=8, color='darkorchid', 
                markeredgecolor='black', markeredgewidth=1)
    
    ax4.set_xlim(-1.2, 1.2)
    ax4.set_ylim(-1.2, 1.2)
    ax4.set_xlabel('cos(θ)')
    ax4.set_ylabel('sin(θ)')
    ax4.set_title('Unit Circle Geometry\n(π-mode Foundation)')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('π-mode: Precise Leibniz Alternating Series and Pi Convergence',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig11_pi_leibniz_calculation.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 11 generated successfully")

if __name__ == "__main__":
    generate_figure_11()