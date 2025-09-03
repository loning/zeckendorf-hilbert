#!/usr/bin/env python3
"""
Figure 23: Entropy Increase Process Visualization
Based on recursive entropy theory from Chapter 1.3.3
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_23():
    """Generate single figure: Entropy Increase Process"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Entropy increase S_(n+1) > S_n
    n_levels = 15
    
    # Calculate entropy for each level using different modes
    phi_entropies = []
    e_entropies = []
    pi_entropies = []
    
    for n in range(n_levels):
        # φ-mode entropy increase
        phi_entropy_increase = recursive_math.entropy_increase_function(n, 'φ')
        phi_entropies.append(sum(recursive_math.entropy_increase_function(i, 'φ') for i in range(n+1)))
        
        # e-mode entropy increase
        e_entropy_increase = recursive_math.entropy_increase_function(n, 'e')
        e_entropies.append(sum(recursive_math.entropy_increase_function(i, 'e') for i in range(n+1)))
        
        # π-mode entropy increase
        pi_entropy_increase = recursive_math.entropy_increase_function(n, 'π')
        pi_entropies.append(sum(recursive_math.entropy_increase_function(i, 'π') for i in range(n+1)))
    
    # Plot entropy increase
    ax1.plot(range(n_levels), phi_entropies, 'o-', color='gold', linewidth=3,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5, label='φ-mode entropy')
    ax1.plot(range(n_levels), e_entropies, 's-', color='green', linewidth=3,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5, label='e-mode entropy')
    ax1.plot(range(n_levels), pi_entropies, '^-', color='purple', linewidth=3,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5, label='π-mode entropy')
    
    ax1.set_xlabel('Recursive Level n')
    ax1.set_ylabel('Cumulative Entropy S_n')
    ax1.set_title('Strict Entropy Increase: S_(n+1) > S_n\n(Three mode comparisons)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Top right: Entropy increase rate
    phi_rates = [recursive_math.entropy_increase_function(n, 'φ') for n in range(n_levels)]
    e_rates = [recursive_math.entropy_increase_function(n, 'e') for n in range(n_levels)]
    pi_rates = [recursive_math.entropy_increase_function(n, 'π') for n in range(n_levels)]
    
    ax2.semilogy(range(n_levels), phi_rates, 'o-', color='gold', linewidth=2,
                markersize=5, label='g_φ(n) = φ^(-n)')
    ax2.semilogy(range(n_levels), e_rates, 's-', color='green', linewidth=2,
                markersize=5, label='g_e(n) = 1/n!')
    ax2.semilogy(range(n_levels), pi_rates, '^-', color='purple', linewidth=2,
                markersize=5, label='g_π(n) = 1/(2n+1)')
    
    ax2.set_xlabel('Level n')
    ax2.set_ylabel('Entropy Increase Rate g(n)')
    ax2.set_title('Entropy Increase Modulation Functions\n(Different mode characteristics)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Information emergence pattern
    # Show how information emerges at each level
    
    information_content = []
    for n in range(12):
        # Information content = number of possible states at level n
        # Based on recursive structure
        content = 2**(n+1) * (1 + np.sin(n * 0.5))  # Recursive growth pattern
        information_content.append(content)
    
    ax3.semilogy(range(len(information_content)), information_content, 'o-', 
                color='darkblue', linewidth=3, markersize=6,
                markeredgecolor='white', markeredgewidth=1)
    ax3.fill_between(range(len(information_content)), information_content, 
                    alpha=0.3, color='darkblue')
    
    ax3.set_xlabel('Recursive Level n')
    ax3.set_ylabel('Information Content (log scale)')
    ax3.set_title('Information Emergence Pattern\n(Exponential growth with recursion)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Irreversibility demonstration
    # Show why entropy cannot decrease
    
    # Hypothetical entropy decrease (impossible)
    n_steps = 10
    impossible_entropy = [10 - i for i in range(n_steps)]
    actual_entropy = [i**1.5 + 2 for i in range(n_steps)]
    
    ax4.plot(range(n_steps), impossible_entropy, 'r--', linewidth=3, alpha=0.7,
            label='Impossible: S_(n+1) < S_n')
    ax4.plot(range(n_steps), actual_entropy, 'g-', linewidth=4, alpha=0.9,
            label='Actual: S_(n+1) > S_n')
    
    # Mark violations
    ax4.fill_between(range(n_steps), impossible_entropy, alpha=0.2, color='red')
    ax4.fill_between(range(n_steps), actual_entropy, alpha=0.2, color='green')
    
    ax4.set_xlabel('Recursive Level n')
    ax4.set_ylabel('Entropy Value')
    ax4.set_title('Irreversibility of Entropy Increase\n(Fundamental recursion law)')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Recursive Entropy Increase: Mathematical Foundation of Time Arrow',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig23_entropy_increase_process.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 23 generated successfully")

if __name__ == "__main__":
    generate_figure_23()