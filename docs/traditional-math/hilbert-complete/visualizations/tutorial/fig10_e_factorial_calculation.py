#!/usr/bin/env python3
"""
Figure 10: e-mode Factorial Series Calculation  
Precise mathematical process of factorial series and e convergence
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math
import math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_10():
    """Generate single figure: e-mode Factorial Calculation"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Generate exact factorial sequence
    n_terms = 12
    fact_sequence = recursive_math.factorial_sequence(n_terms)
    
    # Top left: Factorial terms visualization
    ax1.bar(range(len(fact_sequence)), fact_sequence, color='green', alpha=0.7,
           edgecolor='black', linewidth=1)
    
    # Show factorial values on logarithmic scale for clarity
    ax1.set_yscale('log')
    
    # Add factorial notation above bars
    for i, val in enumerate(fact_sequence[:8]):  # Show first 8 only
        factorial_val = math.factorial(i)
        ax1.text(i, val * 2, f'1/{factorial_val}!', ha='center', va='bottom', 
                fontsize=8, rotation=45)
    
    ax1.set_xlabel('Term Index k')
    ax1.set_ylabel('Factorial Term 1/k!')
    ax1.set_title('Factorial Series Terms\na_k = 1/k!')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Cumulative sum converging to e
    partial_sums, final_sum = recursive_math.e_mode_convergence(n_terms)
    e_target = recursive_math.e
    
    ax2.plot(range(len(partial_sums)), partial_sums, 'o-', color='green', 
            linewidth=3, markersize=6, markeredgecolor='black', markeredgewidth=0.5,
            label='Partial Sum')
    
    # Target e line
    ax2.axhline(y=e_target, color='red', linestyle='--', linewidth=3, alpha=0.8,
               label=f'e = {e_target:.6f}')
    
    # Fill convergence area
    ax2.fill_between(range(len(partial_sums)), partial_sums, e_target, 
                    alpha=0.3, color='green')
    
    ax2.set_xlabel('Partial Sum Index')
    ax2.set_ylabel('Cumulative Sum Value')
    ax2.set_title('e-mode Convergence to Natural Constant\nΣ(1/k!) → e ≈ 2.718282')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Convergence rate analysis  
    convergence_errors = [abs(sum_val - e_target) for sum_val in partial_sums]
    
    ax3.semilogy(range(len(convergence_errors)), convergence_errors, 'o-', 
                color='darkgreen', linewidth=2, markersize=5,
                markeredgecolor='black', markeredgewidth=0.5)
    
    ax3.set_xlabel('Term Index')
    ax3.set_ylabel('Convergence Error (log scale)')
    ax3.set_title('e-mode Convergence Speed\n(Exponential Error Decrease)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Exponential function visualization
    x = np.linspace(0, 2, 100)
    y = np.exp(x)
    
    ax4.plot(x, y, 'green', linewidth=3, alpha=0.8)
    
    # Mark e point
    ax4.plot(1, e_target, 'ro', markersize=12, markeredgecolor='black', 
            markeredgewidth=2)
    
    # Show tangent line at x=1 (derivative = e)
    tangent_x = np.linspace(0.5, 1.5, 50)
    tangent_y = e_target * (tangent_x - 1) + e_target
    ax4.plot(tangent_x, tangent_y, 'r--', alpha=0.7, linewidth=2)
    
    ax4.set_xlabel('x')
    ax4.set_ylabel('exp(x)')
    ax4.set_title('Exponential Function\ne^x with e-point marked')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('e-mode: Precise Factorial Series and Natural Constant Convergence',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig10_e_factorial_calculation.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 10 generated successfully")

if __name__ == "__main__":
    generate_figure_10()