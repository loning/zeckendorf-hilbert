#!/usr/bin/env python3
"""
Figure 22: Phase Transition Critical Points Mathematical Features
Based on P21.1 recursive quantum statistical mechanics theory
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_22():
    """Generate single figure: Phase Transition Critical Points"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Order parameter discontinuity
    control_param = np.linspace(-2, 2, 300)
    order_param = recursive_math.phase_transition_order_parameter(control_param)
    
    ax1.plot(control_param, order_param, 'blue', linewidth=3, alpha=0.8)
    ax1.axvline(x=0, color='red', linestyle='--', linewidth=3, alpha=0.8)
    ax1.fill_between(control_param, order_param, alpha=0.3, color='blue')
    
    # Mark phases
    ax1.text(-1.5, 0.7, 'Phase A', fontsize=12, ha='center', weight='bold',
            bbox=dict(boxstyle="round,pad=0.2", facecolor='lightblue', alpha=0.8))
    ax1.text(1.5, 0.7, 'Phase B', fontsize=12, ha='center', weight='bold',
            bbox=dict(boxstyle="round,pad=0.2", facecolor='lightcoral', alpha=0.8))
    
    ax1.set_xlabel('Control Parameter')
    ax1.set_ylabel('Order Parameter')
    ax1.set_title('Order Parameter Discontinuity\n(Critical point at origin)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Entropy behavior near critical point
    entropy_vals = recursive_math.critical_entropy_behavior(control_param)
    
    ax2.plot(control_param, entropy_vals, 'green', linewidth=3, alpha=0.8)
    ax2.axvline(x=0, color='red', linestyle='--', linewidth=3, alpha=0.8)
    
    # Mark entropy maximum
    max_idx = np.argmax(entropy_vals)
    ax2.plot(control_param[max_idx], entropy_vals[max_idx], 'ro', markersize=12,
            markeredgecolor='black', markeredgewidth=2)
    
    ax2.set_xlabel('Control Parameter')
    ax2.set_ylabel('Recursive Entropy')
    ax2.set_title('Entropy Maximum at Critical Point\n(Based on recursive theory)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Critical scaling behavior
    distance_from_critical = np.abs(control_param)
    susceptibility = 1 / (distance_from_critical + 0.05)  # Divergence at critical point
    
    ax3.semilogy(control_param, susceptibility, 'orange', linewidth=3, alpha=0.8)
    ax3.axvline(x=0, color='red', linestyle='--', linewidth=3, alpha=0.8)
    
    ax3.set_xlabel('Control Parameter')
    ax3.set_ylabel('Susceptibility (log scale)')
    ax3.set_title('Critical Scaling Behavior\n(Divergence at critical point)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Critical fluctuations
    # Show how fluctuations increase near critical point
    fluctuation_amplitude = np.exp(-distance_from_critical * 3) + 0.1
    
    # Generate fluctuation pattern
    np.random.seed(42)  # Reproducible randomness
    fluctuations = np.array([amp * np.random.normal(0, 1) for amp in fluctuation_amplitude])
    
    ax4.plot(control_param, fluctuations, 'purple', linewidth=2, alpha=0.8)
    ax4.fill_between(control_param, fluctuations, alpha=0.3, color='purple')
    ax4.axvline(x=0, color='red', linestyle='--', linewidth=3, alpha=0.8)
    ax4.axhline(y=0, color='black', linestyle='-', alpha=0.5)
    
    ax4.set_xlabel('Control Parameter')
    ax4.set_ylabel('System Fluctuations')
    ax4.set_title('Enhanced Fluctuations\n(Near critical point)')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Phase Transition Critical Point Mathematical Characteristics (Based on Recursive Theory)',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig22_phase_transition_critical_points.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 22 generated successfully")

if __name__ == "__main__":
    generate_figure_22()