#!/usr/bin/env python3
"""
Figure 16: Observer Sequence Termination and Death
Show how finite sequences end and what happens at termination
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_16():
    """Generate single figure: Sequence Termination"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: Approaching termination
    # Generate complete sequence approaching end
    sequence_length = 20
    complete_sequence = recursive_math.fibonacci_sequence(sequence_length)
    
    # Show the approach to termination
    ax1.plot(range(len(complete_sequence)), complete_sequence, 'b-', linewidth=2, alpha=0.8)
    
    # Highlight final steps
    final_steps = 5
    final_range = range(len(complete_sequence) - final_steps, len(complete_sequence))
    final_values = complete_sequence[-final_steps:]
    
    ax1.plot(final_range, final_values, 'ro-', linewidth=3, markersize=8,
            markeredgecolor='black', markeredgewidth=1)
    
    # Mark termination point
    ax1.plot(len(complete_sequence)-1, complete_sequence[-1], 'X', 
            color='red', markersize=20, markeredgecolor='black', markeredgewidth=3)
    
    ax1.set_xlabel('Sequence Step')
    ax1.set_ylabel('Sequence Value')
    ax1.set_title('Approaching Sequence Termination\n(Final steps highlighted)')
    ax1.grid(True, alpha=0.3)
    
    # Top right: Death moment in space
    ax2.set_aspect('equal')
    
    # Mother space
    mother_boundary = Circle((0, 0), 3, fill=False, color='darkblue', linewidth=3, alpha=0.8)
    ax2.add_patch(mother_boundary)
    
    # Core
    core = Circle((0, 0), 0.8, color='gold', alpha=0.6, linewidth=2)
    ax2.add_patch(core)
    
    # Observer trajectory ending
    trajectory_x = [2 + 0.1*i*np.cos(i*0.3) for i in range(20)]
    trajectory_y = [1 + 0.1*i*np.sin(i*0.3) for i in range(20)]
    
    # Plot trajectory with fading alpha
    for i in range(len(trajectory_x)-1):
        alpha = 0.3 + 0.7 * i / len(trajectory_x)
        ax2.plot([trajectory_x[i], trajectory_x[i+1]], [trajectory_y[i], trajectory_y[i+1]],
                'red', linewidth=2, alpha=alpha)
    
    # Mark death point
    ax2.plot(trajectory_x[-1], trajectory_y[-1], 'X', color='red', markersize=25,
            markeredgecolor='black', markeredgewidth=4)
    
    # Expanding circles showing "data preservation"
    for radius in [0.3, 0.6, 0.9]:
        death_echo = Circle((trajectory_x[-1], trajectory_y[-1]), radius, 
                          fill=False, color='red', linewidth=1, alpha=0.4)
        ax2.add_patch(death_echo)
    
    ax2.set_xlim(-4, 4)
    ax2.set_ylim(-4, 4)
    ax2.set_title('Sequence Termination in Space\n(Data preserved in mother space)')
    ax2.grid(True, alpha=0.3)
    
    # Bottom left: Data preservation after death
    # Show how terminated sequence data remains
    
    # Original sequence
    ax3.bar(range(len(complete_sequence)), complete_sequence, color='blue', 
           alpha=0.5, edgecolor='black', linewidth=1, label='Original sequence')
    
    # "Preserved" sequence (same data, different visualization)
    ax3.bar(range(len(complete_sequence)), complete_sequence, color='gray', 
           alpha=0.8, edgecolor='red', linewidth=2, 
           label='Preserved in mother space')
    
    ax3.set_xlabel('Sequence Index')
    ax3.set_ylabel('Data Value')
    ax3.set_title('Data Preservation After Termination\n(Sequence becomes mother space data)')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Multiple sequence lifespans
    # Show different sequence lengths
    
    sequences_info = [
        {'length': 15, 'color': 'red', 'y_pos': 1, 'name': 'Sequence A'},
        {'length': 25, 'color': 'green', 'y_pos': 2, 'name': 'Sequence B'},
        {'length': 10, 'color': 'purple', 'y_pos': 3, 'name': 'Sequence C'},
        {'length': 30, 'color': 'orange', 'y_pos': 4, 'name': 'Sequence D'}
    ]
    
    for seq in sequences_info:
        # Lifespan bar
        ax4.barh(seq['y_pos'], seq['length'], height=0.6, color=seq['color'], 
                alpha=0.7, edgecolor='black', linewidth=1)
        
        # Birth mark
        ax4.plot(0, seq['y_pos'], 'o', color=seq['color'], markersize=10,
                markeredgecolor='green', markeredgewidth=2)
        
        # Death mark
        ax4.plot(seq['length'], seq['y_pos'], 'X', color=seq['color'], 
                markersize=15, markeredgecolor='red', markeredgewidth=3)
        
        # Length label
        ax4.text(seq['length']/2, seq['y_pos'], f"{seq['length']} steps", 
                ha='center', va='center', fontsize=10, weight='bold', color='white')
    
    ax4.set_xlabel('Sequence Length (Steps)')
    ax4.set_ylabel('Different Observer Sequences')
    ax4.set_title('Variable Sequence Lifespans\n(Different observers, different lengths)')
    ax4.grid(axis='x', alpha=0.3)
    
    plt.suptitle('Observer Sequence Termination: Death and Data Preservation',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig16_sequence_termination.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 16 generated successfully")

if __name__ == "__main__":
    generate_figure_16()