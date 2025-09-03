#!/usr/bin/env python3
"""
Figure 24: Different Systems Phase Transition Comparison
Compare phase transitions across physical, biological, social, cognitive systems
"""

import numpy as np
import matplotlib.pyplot as plt
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 10

def generate_figure_24():
    """Generate single figure: System Phase Transitions Comparison"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # System parameters
    control_range = np.linspace(-3, 3, 200)
    
    # Top left: Physical systems (sharp transitions)
    physical_order = np.tanh(control_range * 4)  # Sharp transition
    physical_entropy = 2 + 2 * np.exp(-(control_range**2) * 6)
    
    ax1.plot(control_range, physical_order, 'blue', linewidth=3, alpha=0.8, label='Order Parameter')
    ax1_twin = ax1.twinx()
    ax1_twin.plot(control_range, physical_entropy, 'red', linewidth=2, alpha=0.7, label='Entropy')
    
    ax1.axvline(x=0, color='black', linestyle='--', alpha=0.8)
    ax1.set_xlabel('Temperature / Energy')
    ax1.set_ylabel('Order Parameter', color='blue')
    ax1_twin.set_ylabel('Entropy', color='red')
    ax1.set_title('Physical Systems\n(Ice-water, magnetic transitions)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Biological systems (gradual transitions)
    biological_order = 1 / (1 + np.exp(-control_range * 2))  # Sigmoid
    biological_entropy = 1.5 + 1.2 * np.exp(-(control_range**2) * 2)
    
    ax2.plot(control_range, biological_order, 'green', linewidth=3, alpha=0.8)
    ax2_twin = ax2.twinx()
    ax2_twin.plot(control_range, biological_entropy, 'orange', linewidth=2, alpha=0.7)
    
    ax2.axvline(x=0, color='black', linestyle='--', alpha=0.8)
    ax2.set_xlabel('Environmental Pressure')
    ax2.set_ylabel('Adaptation Level', color='green')
    ax2_twin.set_ylabel('Genetic Diversity', color='orange')
    ax2.set_title('Biological Systems\n(Evolution, ecosystem changes)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Social systems (complex transitions)
    social_order = np.tanh(control_range * 1.5) + 0.3 * np.sin(control_range * 3)
    social_entropy = 1.8 + 1.5 * np.exp(-(control_range**2) * 3) + 0.2 * np.cos(control_range * 4)
    
    ax3.plot(control_range, social_order, 'purple', linewidth=3, alpha=0.8)
    ax3_twin = ax3.twinx()
    ax3_twin.plot(control_range, social_entropy, 'brown', linewidth=2, alpha=0.7)
    
    ax3.axvline(x=0, color='black', linestyle='--', alpha=0.8)
    ax3.set_xlabel('Social Pressure / Technology')
    ax3.set_ylabel('Social Order', color='purple')
    ax3_twin.set_ylabel('Cultural Diversity', color='brown')
    ax3.set_title('Social Systems\n(Revolutions, cultural shifts)')
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Cognitive systems (recursive transitions)
    cognitive_order = np.tanh(control_range * 2.5) * (1 + 0.2 * np.sin(control_range * 5))
    cognitive_entropy = 2.2 + 1.8 * np.exp(-(control_range**2) * 4)
    
    ax4.plot(control_range, cognitive_order, 'darkred', linewidth=3, alpha=0.8)
    ax4_twin = ax4.twinx()
    ax4_twin.plot(control_range, cognitive_entropy, 'navy', linewidth=2, alpha=0.7)
    
    ax4.axvline(x=0, color='black', linestyle='--', alpha=0.8)
    ax4.set_xlabel('Knowledge / Experience')
    ax4.set_ylabel('Understanding Level', color='darkred')
    ax4_twin.set_ylabel('Cognitive Complexity', color='navy')
    ax4.set_title('Cognitive Systems\n(Learning breakthroughs, insights)')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('Universal Phase Transition Pattern Across Different System Types',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig24_system_phase_transitions.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 24 generated successfully")

if __name__ == "__main__":
    generate_figure_24()