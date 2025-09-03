#!/usr/bin/env python3
"""
Figure 14: Observer Sequence Growth Stages
Show how observer sequences develop through different life stages
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_14():
    """Generate single figure: Sequence Growth Stages"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Observer life stages with different operation preferences
    life_stages = {
        'Youth': {'length': 8, 'operations': ['φ'] * 8, 'color': 'red'},
        'Adulthood': {'length': 12, 'operations': ['e'] * 12, 'color': 'green'}, 
        'Maturity': {'length': 6, 'operations': ['π'] * 6, 'color': 'purple'},
        'Integration': {'length': 4, 'operations': ['φ', 'e', 'π', 'φ'], 'color': 'orange'}
    }
    
    # Top left: Youth stage (φ-dominant)
    youth_ops = life_stages['Youth']['operations']
    youth_data = recursive_math.fibonacci_sequence(len(youth_ops))
    
    ax1.plot(range(len(youth_data)), youth_data, 'o-', color='red', linewidth=3,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5)
    ax1.fill_between(range(len(youth_data)), youth_data, alpha=0.3, color='red')
    
    ax1.set_xlabel('Age Step')
    ax1.set_ylabel('Growth Data')
    ax1.set_title('Youth Stage: φ-mode Dominant\n(Growth & Exploration)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Adulthood stage (e-dominant)
    adult_ops = life_stages['Adulthood']['operations'] 
    adult_data = recursive_math.factorial_sequence(len(adult_ops))
    adult_data = [val * 100 for val in adult_data]  # Scale up for visibility
    
    ax2.plot(range(len(adult_data)), adult_data, 's-', color='green', linewidth=3,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5)
    ax2.fill_between(range(len(adult_data)), adult_data, alpha=0.3, color='green')
    ax2.set_yscale('log')
    
    ax2.set_xlabel('Age Step') 
    ax2.set_ylabel('Stability Data (log scale)')
    ax2.set_title('Adulthood Stage: e-mode Dominant\n(Stability & Rationality)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Maturity stage (π-dominant)
    mature_ops = life_stages['Maturity']['operations']
    mature_data = recursive_math.leibniz_sequence(len(mature_ops))
    mature_data = [val * 10 for val in mature_data]  # Scale up for visibility
    
    ax3.plot(range(len(mature_data)), mature_data, '^-', color='purple', linewidth=3,
            markersize=6, markeredgecolor='black', markeredgewidth=0.5)
    ax3.axhline(y=0, color='black', linewidth=1, alpha=0.5)
    ax3.fill_between(range(len(mature_data)), mature_data, alpha=0.3, color='purple')
    
    ax3.set_xlabel('Age Step')
    ax3.set_ylabel('Balance Data')
    ax3.set_title('Maturity Stage: π-mode Dominant\n(Balance & Wisdom)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Complete life sequence
    total_length = sum(stage['length'] for stage in life_stages.values())
    complete_sequence = []
    stage_boundaries = [0]
    current_pos = 0
    
    for stage_name, stage_data in life_stages.items():
        if stage_name == 'Youth':
            stage_values = recursive_math.fibonacci_sequence(stage_data['length'])
            stage_values = [val/10 for val in stage_values]  # Normalize
        elif stage_name == 'Adulthood':
            stage_values = recursive_math.factorial_sequence(stage_data['length'])
            stage_values = [val*50 for val in stage_values]  # Scale
        elif stage_name == 'Maturity':
            stage_values = recursive_math.leibniz_sequence(stage_data['length'])
            stage_values = [abs(val)*20 for val in stage_values]  # Absolute & scale
        else:  # Integration
            fib_val = recursive_math.fibonacci_sequence(4)[1]  # F_1
            fact_val = recursive_math.factorial_sequence(4)[1]  # 1/1!
            leibniz_val = recursive_math.leibniz_sequence(4)[1]  # -1/3
            mixed_val = recursive_math.fibonacci_sequence(4)[2]  # F_2
            stage_values = [fib_val/10, fact_val*50, abs(leibniz_val)*20, mixed_val/10]
        
        complete_sequence.extend(stage_values)
        current_pos += stage_data['length']
        stage_boundaries.append(current_pos)
    
    # Plot complete sequence with stage coloring
    ax4.plot(range(len(complete_sequence)), complete_sequence, 'k-', linewidth=2, alpha=0.8)
    
    # Color different stages
    current_idx = 0
    for stage_name, stage_data in life_stages.items():
        length = stage_data['length']
        indices = range(current_idx, current_idx + length)
        values = complete_sequence[current_idx:current_idx + length]
        
        ax4.fill_between(indices, values, alpha=0.4, color=stage_data['color'],
                        label=stage_name)
        current_idx += length
    
    # Mark stage boundaries
    for boundary in stage_boundaries[1:-1]:
        ax4.axvline(x=boundary, color='black', linestyle=':', alpha=0.7)
    
    ax4.set_xlabel('Complete Life Sequence')
    ax4.set_ylabel('Sequence Data')
    ax4.set_title('Complete Observer Lifecycle\n(Four Distinct Stages)')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Observer Finite Sequence: Birth and Life Stage Development',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig14_sequence_growth_stages.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 14 generated successfully")

if __name__ == "__main__":
    generate_figure_14()