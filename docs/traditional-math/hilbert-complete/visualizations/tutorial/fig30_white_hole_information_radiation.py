#!/usr/bin/env python3
"""
Figure 30: White Hole Information Radiation Model (Final Figure)
The complete model: White hole radiates all information, observers extract colored spectra
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from information_extraction_mathematics import info_math
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_30():
    """Generate single figure: White Hole Information Radiation"""
    
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Central white hole (information source)
    ax.scatter([0], [0], [0], s=1000, c='white', marker='*',
              edgecolor='gold', linewidth=5, alpha=1.0)
    ax.text(0, 0, -1, 'WHITE HOLE\nInformation Source', ha='center', va='top',
           fontsize=14, weight='bold', color='gold')
    
    # Information radiation in all directions
    n_radiation_beams = 24
    radiation_angles = np.linspace(0, 2*np.pi, n_radiation_beams, endpoint=False)
    beam_length = 5
    
    for angle in radiation_angles:
        # Each beam carries all three types of information
        for radius in np.linspace(0.5, beam_length, 15):
            # Position along beam
            x = radius * np.cos(angle)
            y = radius * np.sin(angle)
            z = 0  # Primary radiation plane
            
            # Information intensity decreases with distance (1/r² law)
            intensity = 1 / (radius**2 + 0.1)
            
            # Each point contains RGB information
            # Intensity modulates but color ratios stay constant
            intensity_clamped = max(0.1, min(1.0, intensity))  # Clamp intensity
            
            ax.scatter([x], [y], [z], c='white', s=intensity_clamped*30, 
                      alpha=intensity_clamped*0.7, edgecolor='gold', linewidth=0.5)
    
    # Multiple observers at different distances extracting different spectra
    observers = [
        {
            'position': [3, 1, 1], 
            'extraction_mode': 'φ',
            'color': 'red',
            'extracted_spectrum': 'Red spectrum'
        },
        {
            'position': [-2, 3, 0.5],
            'extraction_mode': 'e', 
            'color': 'green',
            'extracted_spectrum': 'Green spectrum'
        },
        {
            'position': [1, -2.5, 1.5],
            'extraction_mode': 'π',
            'color': 'blue', 
            'extracted_spectrum': 'Blue spectrum'
        },
        {
            'position': [-3, -2, -1],
            'extraction_mode': 'mixed',
            'color': 'magenta',
            'extracted_spectrum': 'Mixed spectrum'
        },
        {
            'position': [2, 2.5, -1.5],
            'extraction_mode': 'white',
            'color': 'white',
            'extracted_spectrum': 'Full spectrum'
        }
    ]
    
    for obs in observers:
        x, y, z = obs['position']
        color = obs['color']
        mode = obs['extraction_mode']
        
        # Observer position
        ax.scatter([x], [y], [z], s=200, c=color, edgecolor='black', 
                  linewidth=2, alpha=0.9)
        
        # Information beam from white hole to observer
        beam_segments = 20
        for i in range(beam_segments):
            t = i / beam_segments
            beam_x = t * x
            beam_y = t * y
            beam_z = t * z
            
            # Beam color depends on observer's extraction capability
            if mode == 'φ':
                beam_color = [1-t, t*0.5, t*0.3]  # Red gradient
            elif mode == 'e':
                beam_color = [t*0.3, 1-t, t*0.5]  # Green gradient
            elif mode == 'π':
                beam_color = [t*0.5, t*0.3, 1-t]  # Blue gradient
            elif mode == 'mixed':
                beam_color = [0.8, 0.2, 0.8]      # Purple
            else:  # white
                beam_color = [1-t*0.2, 1-t*0.2, 1-t*0.2]  # White gradient
            
            # Draw beam segment
            if i < beam_segments - 1:
                next_t = (i+1) / beam_segments
                next_x, next_y, next_z = next_t * x, next_t * y, next_t * z
                
                ax.plot([beam_x, next_x], [beam_y, next_y], [beam_z, next_z],
                       color=beam_color, linewidth=2, alpha=0.7)
        
        # Extracted information visualization around observer
        extraction_radius = 0.5
        extraction_angles = np.linspace(0, 2*np.pi, 8, endpoint=False)
        
        for extract_angle in extraction_angles:
            extract_x = x + extraction_radius * np.cos(extract_angle)
            extract_y = y + extraction_radius * np.sin(extract_angle)  
            extract_z = z + extraction_radius * 0.3 * np.sin(extract_angle)
            
            ax.scatter([extract_x], [extract_y], [extract_z], 
                      c=color, s=30, alpha=0.6)
    
    # Three primary axes emanating from white hole
    axis_length = 6
    
    # φ-axis (Red)
    ax.plot([0, axis_length], [0, 0], [0, 0], 'red', linewidth=4, alpha=0.8)
    ax.text(axis_length, 0, 0, 'φ-axis', fontsize=12, weight='bold', color='red')
    
    # e-axis (Green)
    ax.plot([0, 0], [0, axis_length], [0, 0], 'green', linewidth=4, alpha=0.8)
    ax.text(0, axis_length, 0, 'e-axis', fontsize=12, weight='bold', color='green')
    
    # π-axis (Blue)
    ax.plot([0, 0], [0, 0], [0, axis_length], 'blue', linewidth=4, alpha=0.8)
    ax.text(0, 0, axis_length, 'π-axis', fontsize=12, weight='bold', color='blue')
    
    # Time flow direction (affects all observations)
    time_flow = np.array([4, 4, 4])
    ax.plot([0, time_flow[0]], [0, time_flow[1]], [0, time_flow[2]],
           'purple', linewidth=5, alpha=0.9)
    ax.text(time_flow[0], time_flow[1], time_flow[2]+0.5, 'T-flow', 
           fontsize=12, weight='bold', color='purple', ha='center')
    
    ax.set_xlabel('φ-dimension (Information Extraction)')
    ax.set_ylabel('e-dimension (Information Processing)')
    ax.set_zlabel('π-dimension (Information Integration)')
    ax.set_title('White Hole Information Radiation Model\nComplete Information → Observers Extract Specific Spectra',
                fontsize=14, weight='bold', pad=20)
    
    ax.set_box_aspect([1,1,1])
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig30_white_hole_information_radiation.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 30 generated successfully - TUTORIAL COMPLETE!")

if __name__ == "__main__":
    generate_figure_30()