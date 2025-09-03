#!/usr/bin/env python3
"""
Figure 26: White Light Decomposition into φ, e, π Spectra
The perfect analogy: White light = Hilbert core, Colors = Observation modes
"""

import numpy as np
import matplotlib.pyplot as plt
from spectrum_math_functions import spectrum_math
from recursive_math_functions import recursive_math

plt.style.use('default')
plt.rcParams['font.size'] = 11

def generate_figure_26():
    """Generate single figure: White Light Decomposition"""
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    # Top left: White light source (white hole)
    ax1.set_aspect('equal')
    
    # White hole as brilliant white source
    theta_circle = np.linspace(0, 2*np.pi, 100)
    white_hole_x = np.cos(theta_circle)
    white_hole_y = np.sin(theta_circle)
    
    # Multiple concentric circles for brilliance effect
    for radius in [0.3, 0.6, 0.9, 1.2]:
        ax1.plot(radius * white_hole_x, radius * white_hole_y, 'white', 
                linewidth=3, alpha=0.8)
        ax1.fill(radius * white_hole_x, radius * white_hole_y, 'yellow', 
                alpha=0.2)
    
    # Central white core
    ax1.scatter([0], [0], s=500, c='white', edgecolor='gold', linewidth=4, alpha=1.0)
    
    # Radiating white light beams
    beam_angles = np.linspace(0, 2*np.pi, 12)
    for angle in beam_angles:
        beam_x = [0, 2.5 * np.cos(angle)]
        beam_y = [0, 2.5 * np.sin(angle)]
        ax1.plot(beam_x, beam_y, 'yellow', linewidth=2, alpha=0.7)
    
    ax1.set_xlim(-3, 3)
    ax1.set_ylim(-3, 3)
    ax1.set_title('White Hole: Source of All Information\n(Hilbert Recursive Mother Space Core)')
    ax1.set_facecolor('black')
    
    # Top right: Prism decomposition
    ax2.set_aspect('equal')
    
    # Incident white light beam
    ax2.arrow(-2, 0, 1.5, 0, head_width=0.1, head_length=0.1, 
             fc='white', ec='white', linewidth=4, alpha=0.9)
    
    # Prism (triangle)
    prism_x = [0, 0.5, 0, 0]
    prism_y = [-0.5, 0, 0.5, -0.5]
    ax2.plot(prism_x, prism_y, 'gray', linewidth=3)
    ax2.fill(prism_x, prism_y, 'lightgray', alpha=0.8)
    
    # Decomposed light beams (φ, e, π modes)
    # φ-mode: Red light (upper beam)
    ax2.arrow(0.5, 0, 2, 0.8, head_width=0.08, head_length=0.1,
             fc='red', ec='red', linewidth=3, alpha=0.9)
    
    # e-mode: Green light (middle beam)
    ax2.arrow(0.5, 0, 2, 0, head_width=0.08, head_length=0.1,
             fc='green', ec='green', linewidth=3, alpha=0.9)
    
    # π-mode: Blue light (lower beam)
    ax2.arrow(0.5, 0, 2, -0.8, head_width=0.08, head_length=0.1,
             fc='blue', ec='blue', linewidth=3, alpha=0.9)
    
    ax2.set_xlim(-3, 3)
    ax2.set_ylim(-1.5, 1.5)
    ax2.set_title('Prism Decomposition\n(φ=Red, e=Green, π=Blue)')
    ax2.set_facecolor('black')
    
    # Bottom left: Spectral analysis
    # Generate white hole data
    n_points = 30
    white_data = spectrum_math.generate_white_hole_data(n_points)
    
    # Decompose into three spectra
    phi_spectrum = spectrum_math.white_light_decomposition(white_data, 'φ')
    e_spectrum = spectrum_math.white_light_decomposition(white_data, 'e')
    pi_spectrum = spectrum_math.white_light_decomposition(white_data, 'π')
    
    # Plot original white light
    ax3.plot(range(len(white_data)), white_data, 'gray', linewidth=4, 
            alpha=0.9, label='White Light (All Information)')
    
    # Plot decomposed spectra
    ax3.plot(range(len(phi_spectrum)), phi_spectrum, 'red', linewidth=2,
            alpha=0.8, label='φ-spectrum (Growth patterns)')
    ax3.plot(range(len(e_spectrum)), e_spectrum, 'green', linewidth=2,
            alpha=0.8, label='e-spectrum (Stability patterns)')
    ax3.plot(range(len(pi_spectrum)), pi_spectrum, 'blue', linewidth=2,
            alpha=0.8, label='π-spectrum (Balance patterns)')
    
    ax3.set_xlabel('Information Index')
    ax3.set_ylabel('Spectral Intensity')
    ax3.set_title('Spectral Decomposition Analysis\n(Same source → Different spectra)')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Bottom right: Wavelength distribution
    wavelengths = np.linspace(400, 750, 100)  # Visible spectrum
    
    # Calculate spectral distributions
    phi_wavelengths, phi_intensity = spectrum_math.spectral_intensity_distribution(phi_spectrum, 'φ')
    e_wavelengths, e_intensity = spectrum_math.spectral_intensity_distribution(e_spectrum, 'e')
    pi_wavelengths, pi_intensity = spectrum_math.spectral_intensity_distribution(pi_spectrum, 'π')
    
    # Plot spectral distributions
    ax4.fill_between(phi_wavelengths, phi_intensity, alpha=0.6, color='red', label='φ-mode (700nm)')
    ax4.fill_between(e_wavelengths, e_intensity, alpha=0.6, color='green', label='e-mode (550nm)')
    ax4.fill_between(pi_wavelengths, pi_intensity, alpha=0.6, color='blue', label='π-mode (450nm)')
    
    # Mark specific wavelengths
    for mode, wl in spectrum_math.wavelengths.items():
        color = {'φ': 'red', 'e': 'green', 'π': 'blue'}[mode]
        ax4.axvline(x=wl, color=color, linestyle='--', linewidth=2, alpha=0.8)
    
    ax4.set_xlabel('Wavelength (nm)')
    ax4.set_ylabel('Spectral Intensity')
    ax4.set_title('Wavelength Distribution\n(Mode-specific frequencies)')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('White Light = Hilbert Core: Complete Information Decomposed by Observer Modes',
                fontsize=16, weight='bold', y=0.95)
    
    plt.tight_layout()
    plt.savefig('/Users/cookie/zeckendorf-hilbert/docs/traditional-math/hilbert-complete/visualizations/tutorial/fig26_white_light_decomposition.png',
                dpi=300, bbox_inches='tight')
    plt.close()
    
    print("✓ Figure 26 generated successfully")

if __name__ == "__main__":
    generate_figure_26()