#!/usr/bin/env python3
"""
Figure 09: φ-mode Fibonacci Recursive Calculation
Precise mathematical process of Fibonacci sequence and φ convergence
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_09():
    """Generate single figure: φ-mode Fibonacci Calculation"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Generate exact Fibonacci sequence
    n_terms = 20
    fib_sequence = recursive_math.fibonacci_sequence(n_terms)
    
    # Top left: Fibonacci sequence values
    ax1.bar(range(len(fib_sequence)), fib_sequence, color='gold', alpha=0.7, 
           edgecolor='black', linewidth=1)
    
    # Add recursive arrows showing F_k = F_(k-1) + F_(k-2)
    for i in range(2, min(8, len(fib_sequence))):
        # Arrow from F_(k-1)
        ax1.annotate('', xy=(i, fib_sequence[i]), xytext=(i-1, fib_sequence[i-1]),
                    arrowprops=dict(arrowstyle='->', color='red', lw=2))
        # Arrow from F_(k-2)  
        ax1.annotate('', xy=(i, fib_sequence[i]), xytext=(i-2, fib_sequence[i-2]),
                    arrowprops=dict(arrowstyle='->', color='blue', lw=2))
    
    ax1.set_xlabel('Sequence Index k')
    ax1.set_ylabel('Fibonacci Value F_k')
    ax1.set_title('Fibonacci Recursive Generation\nF_k = F_(k-1) + F_(k-2)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Fibonacci ratios converging to φ
    ratios, final_ratio = recursive_math.phi_mode_convergence(n_terms)
    phi_target = recursive_math.phi
    
    ax2.plot(range(1, len(ratios)+1), ratios, 'o-', color='gold', linewidth=3, 
            markersize=6, markeredgecolor='black', markeredgewidth=0.5,
            label=f'F_k/F_(k-1)')
    
    # Target φ line
    ax2.axhline(y=phi_target, color='red', linestyle='--', linewidth=3, alpha=0.8,
               label=f'φ = {phi_target:.6f}')
    
    # Show convergence error
    errors = [abs(ratio - phi_target) for ratio in ratios]
    ax2_twin = ax2.twinx()
    ax2_twin.semilogy(range(1, len(errors)+1), errors, 's--', color='darkred', 
                     alpha=0.7, label='Convergence Error')
    
    ax2.set_xlabel('Ratio Index k')
    ax2.set_ylabel('Ratio Value')
    ax2_twin.set_ylabel('Convergence Error (log scale)', color='darkred')
    ax2.set_title('φ-mode Convergence to Golden Ratio\nF_(k+1)/F_k → φ ≈ 1.618034')
    ax2.legend(loc='center right')
    ax2_twin.legend(loc='upper right')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Growth rate analysis
    growth_rates = [fib_sequence[i+1]/fib_sequence[i] if fib_sequence[i] > 0 else 1 
                   for i in range(len(fib_sequence)-1)]
    
    ax3.plot(range(len(growth_rates)), growth_rates, 'o-', color='darkgoldenrod', 
            linewidth=2, markersize=5, markeredgecolor='black', markeredgewidth=0.5)
    ax3.axhline(y=phi_target, color='red', linestyle=':', linewidth=2, alpha=0.8)
    
    # Highlight convergence region
    convergence_start = max(0, len(growth_rates) - 5)
    ax3.fill_between(range(convergence_start, len(growth_rates)), 
                    [growth_rates[i] for i in range(convergence_start, len(growth_rates))],
                    alpha=0.3, color='gold')
    
    ax3.set_xlabel('Growth Rate Index')
    ax3.set_ylabel('Growth Rate F_(k+1)/F_k')
    ax3.set_title('φ-mode Growth Rate Convergence\nStabilizes at Golden Ratio')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Clean convergence visualization
    # Show the golden ratio spiral pattern
    theta = np.linspace(0, 4*np.pi, 100)
    r = phi_target ** (theta / (2*np.pi))  # Golden spiral
    x_spiral = r * np.cos(theta)
    y_spiral = r * np.sin(theta)
    
    ax4.plot(x_spiral, y_spiral, 'gold', linewidth=3, alpha=0.8)
    ax4.set_aspect('equal')
    ax4.set_xlim(-5, 5)
    ax4.set_ylim(-5, 5)
    ax4.grid(True, alpha=0.3)
    ax4.set_title('Golden Spiral Pattern\n(φ-mode Geometry)')
    
    plt.suptitle('φ-mode: Precise Fibonacci Recursive Calculation and Golden Ratio Convergence',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig09_phi_fibonacci_calculation.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 09 generated successfully")

if __name__ == "__main__":
    generate_figure_09()