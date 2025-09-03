#!/usr/bin/env python3
"""
Figure 12: Three Mode Convergence Comparison
Compare convergence characteristics of φ, e, π modes
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_12():
    """Generate single figure: Mode Convergence Comparison"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Compare all three convergences on same scale
    n_terms = 15
    
    # φ-mode convergence
    phi_ratios, phi_final = recursive_math.phi_mode_convergence(n_terms)
    phi_errors = [abs(ratio - recursive_math.phi) for ratio in phi_ratios]
    
    # e-mode convergence  
    e_sums, e_final = recursive_math.e_mode_convergence(n_terms)
    e_errors = [abs(sum_val - recursive_math.e) for sum_val in e_sums]
    
    # π-mode convergence
    pi_sums, pi_final = recursive_math.pi_mode_convergence(n_terms)
    pi_errors = [abs(sum_val - recursive_math.pi) for sum_val in pi_sums]
    
    # Top left: Convergence values comparison
    ax1.plot(range(len(phi_ratios)), phi_ratios, 'o-', color='gold', linewidth=2, 
            markersize=5, label=f'φ-mode → {recursive_math.phi:.4f}')
    ax1.plot(range(len(e_sums)), e_sums, 's-', color='green', linewidth=2,
            markersize=5, label=f'e-mode → {recursive_math.e:.4f}') 
    ax1.plot(range(len(pi_sums)), pi_sums, '^-', color='purple', linewidth=2,
            markersize=5, label=f'π-mode → {recursive_math.pi:.4f}')
    
    # Target lines
    ax1.axhline(y=recursive_math.phi, color='gold', linestyle=':', alpha=0.7)
    ax1.axhline(y=recursive_math.e, color='green', linestyle=':', alpha=0.7)
    ax1.axhline(y=recursive_math.pi, color='purple', linestyle=':', alpha=0.7)
    
    ax1.set_xlabel('Term Index')
    ax1.set_ylabel('Convergence Value')
    ax1.set_title('Three Mode Convergence Patterns')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Top right: Convergence error comparison (log scale)
    ax2.semilogy(range(len(phi_errors)), phi_errors, 'o-', color='gold', 
                linewidth=2, markersize=4, label='φ-mode error')
    ax2.semilogy(range(len(e_errors)), e_errors, 's-', color='green',
                linewidth=2, markersize=4, label='e-mode error')
    ax2.semilogy(range(len(pi_errors)), pi_errors, '^-', color='purple',
                linewidth=2, markersize=4, label='π-mode error')
    
    ax2.set_xlabel('Term Index')
    ax2.set_ylabel('Convergence Error (log scale)')
    ax2.set_title('Convergence Speed Comparison')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Convergence rate analysis
    # Calculate convergence rates (how fast error decreases)
    
    phi_rates = []
    e_rates = []
    pi_rates = []
    
    for i in range(1, min(len(phi_errors), len(e_errors), len(pi_errors))):
        if phi_errors[i] > 0 and phi_errors[i-1] > 0:
            phi_rates.append(phi_errors[i] / phi_errors[i-1])
        if e_errors[i] > 0 and e_errors[i-1] > 0:
            e_rates.append(e_errors[i] / e_errors[i-1])  
        if pi_errors[i] > 0 and pi_errors[i-1] > 0:
            pi_rates.append(pi_errors[i] / pi_errors[i-1])
    
    min_length = min(len(phi_rates), len(e_rates), len(pi_rates))
    
    ax3.plot(range(min_length), phi_rates[:min_length], 'o-', color='gold',
            linewidth=2, markersize=4, label='φ-mode rate')
    ax3.plot(range(min_length), e_rates[:min_length], 's-', color='green', 
            linewidth=2, markersize=4, label='e-mode rate')
    ax3.plot(range(min_length), pi_rates[:min_length], '^-', color='purple',
            linewidth=2, markersize=4, label='π-mode rate')
    
    ax3.set_xlabel('Rate Index')
    ax3.set_ylabel('Error Reduction Ratio')
    ax3.set_title('Convergence Rate Analysis')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Final accuracy comparison
    final_errors = [
        abs(phi_final - recursive_math.phi),
        abs(e_final - recursive_math.e), 
        abs(pi_final - recursive_math.pi)
    ]
    
    mode_names = ['φ-mode', 'e-mode', 'π-mode']
    colors = ['gold', 'green', 'purple']
    
    bars = ax4.bar(mode_names, final_errors, color=colors, alpha=0.7,
                  edgecolor='black', linewidth=2)
    
    # Add accuracy labels on bars
    for bar, error in zip(bars, final_errors):
        height = bar.get_height()
        ax4.text(bar.get_x() + bar.get_width()/2., height * 1.1,
                f'{error:.2e}', ha='center', va='bottom', fontsize=10, weight='bold')
    
    ax4.set_ylabel('Final Convergence Error')
    ax4.set_title('Final Accuracy Comparison')
    ax4.set_yscale('log')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Three Mathematical Mode Convergence Characteristics Comparison',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig12_mode_convergence_comparison.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 12 generated successfully")

if __name__ == "__main__":
    generate_figure_12()