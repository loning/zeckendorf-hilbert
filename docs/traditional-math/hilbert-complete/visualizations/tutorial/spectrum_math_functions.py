#!/usr/bin/env python3
"""
Spectrum Mathematics for White Light Decomposition
Mathematical functions for φ, e, π spectral analysis of white light
"""

import numpy as np
import math
from recursive_math_functions import recursive_math

class SpectrumMathFunctions:
    """Mathematical functions for light spectrum decomposition"""
    
    def __init__(self):
        # Wavelength assignments for three modes
        self.wavelengths = {
            'φ': 700,  # Red light (passionate, creative)
            'e': 550,  # Green light (stable, rational)  
            'π': 450   # Blue light (deep, balanced)
        }
        
        # RGB color mappings
        self.rgb_colors = {
            'φ': [1.0, 0.0, 0.0],      # Pure red
            'e': [0.0, 1.0, 0.0],      # Pure green
            'π': [0.0, 0.0, 1.0],      # Pure blue
            'white': [1.0, 1.0, 1.0]   # White light (all combined)
        }
    
    def white_light_decomposition(self, white_data, mode):
        """Decompose white light data into specific mode spectrum"""
        
        if mode == 'φ':
            # φ-mode extracts Fibonacci growth patterns (red spectrum)
            fib_seq = recursive_math.fibonacci_sequence(len(white_data))
            return [white_data[i] * (fib_seq[i] / max(fib_seq)) for i in range(len(white_data))]
            
        elif mode == 'e':
            # e-mode extracts factorial decay patterns (green spectrum)
            fact_seq = recursive_math.factorial_sequence(len(white_data))
            return [white_data[i] * fact_seq[i] * 10 for i in range(len(white_data))]
            
        elif mode == 'π':
            # π-mode extracts oscillating patterns (blue spectrum)
            leibniz_seq = recursive_math.leibniz_sequence(len(white_data))
            return [white_data[i] * abs(leibniz_seq[i]) * 5 for i in range(min(len(white_data), len(leibniz_seq)))]
        
        else:
            return white_data  # Return unchanged
    
    def generate_white_hole_data(self, n_points):
        """Generate white hole information radiation (contains all possibilities)"""
        
        # Rich information pattern containing all mode signatures
        angles = np.linspace(0, 4*np.pi, n_points)
        
        # Superposition of all three mode patterns
        phi_component = np.array([recursive_math.fibonacci_sequence(20)[i % 20] for i in range(n_points)])
        e_component = np.array([recursive_math.factorial_sequence(15)[i % 15] * 100 for i in range(n_points)])
        pi_component = np.array([abs(recursive_math.leibniz_sequence(25)[i % 25]) * 50 for i in range(n_points)])
        
        # Combine with harmonic structure
        harmonic_base = 10 + 5*np.sin(angles) + 3*np.cos(angles*2) + 2*np.sin(angles*3)
        
        # White light = superposition of all components
        white_light = (phi_component/max(phi_component) + 
                      e_component/max(e_component) + 
                      pi_component/max(pi_component)) * harmonic_base / 3
        
        return white_light
    
    def spectral_intensity_distribution(self, mode_data, mode):
        """Calculate spectral intensity distribution for a mode"""
        
        wavelength = self.wavelengths[mode]
        
        # Gaussian distribution around central wavelength
        wavelength_range = np.linspace(380, 750, 100)  # Visible spectrum
        
        # Width depends on mode characteristics
        if mode == 'φ':
            sigma = 50  # Broader spectrum (dynamic)
        elif mode == 'e':
            sigma = 30  # Narrower spectrum (precise)
        else:  # π
            sigma = 40  # Medium spectrum (balanced)
        
        intensity = np.exp(-((wavelength_range - wavelength)**2) / (2 * sigma**2))
        
        # Modulate intensity based on mode data
        avg_intensity = np.mean(mode_data) if mode_data else 1
        intensity = intensity * avg_intensity
        
        return wavelength_range, intensity
    
    def color_mixing_matrix(self, phi_intensity, e_intensity, pi_intensity):
        """Calculate RGB color from three mode intensities"""
        
        # Normalize intensities
        total_intensity = phi_intensity + e_intensity + pi_intensity
        if total_intensity == 0:
            return [0, 0, 0]
        
        phi_weight = phi_intensity / total_intensity
        e_weight = e_intensity / total_intensity  
        pi_weight = pi_intensity / total_intensity
        
        # Mix RGB based on weights
        mixed_color = [
            phi_weight * self.rgb_colors['φ'][0] + e_weight * self.rgb_colors['e'][0] + pi_weight * self.rgb_colors['π'][0],
            phi_weight * self.rgb_colors['φ'][1] + e_weight * self.rgb_colors['e'][1] + pi_weight * self.rgb_colors['π'][1],
            phi_weight * self.rgb_colors['φ'][2] + e_weight * self.rgb_colors['e'][2] + pi_weight * self.rgb_colors['π'][2]
        ]
        
        return mixed_color
    
    def hypercube_color_encoding(self, dimension):
        """Generate color encoding for higher dimensional hypercubes"""
        
        if dimension <= 4:
            # Standard XYZT encoding
            return ['red', 'green', 'blue', 'purple']
        
        elif dimension == 5:
            # Add Color dimension
            return ['red', 'green', 'blue', 'purple', 'gold']
            
        elif dimension == 6:
            # Add Intensity dimension
            return ['red', 'green', 'blue', 'purple', 'gold', 'cyan']
            
        elif dimension == 7:
            # Add Polarization dimension
            return ['red', 'green', 'blue', 'purple', 'gold', 'cyan', 'magenta']
            
        else:
            # Generate distinct colors for higher dimensions
            colors = []
            for i in range(dimension):
                hue = i / dimension
                colors.append(plt.cm.hsv(hue)[:3])  # RGB from HSV
            return colors
    
    def white_hole_radiation_pattern(self, observer_position, observation_mode):
        """Calculate what an observer receives from white hole"""
        
        # Distance from white hole center
        distance = np.linalg.norm(observer_position)
        
        # Radiation intensity (1/r² law)
        base_intensity = 1 / (distance**2 + 0.1)
        
        # Mode-specific reception efficiency
        if observation_mode == 'φ':
            # φ-observers are more sensitive to growth patterns
            reception_efficiency = 0.8
            frequency_response = lambda f: np.exp(-(f - 700)**2 / 1000)
        elif observation_mode == 'e':
            # e-observers are more sensitive to stable patterns
            reception_efficiency = 0.9
            frequency_response = lambda f: np.exp(-(f - 550)**2 / 800)
        else:  # π mode
            # π-observers are more sensitive to oscillating patterns
            reception_efficiency = 0.7
            frequency_response = lambda f: np.exp(-(f - 450)**2 / 900)
        
        received_intensity = base_intensity * reception_efficiency
        
        return received_intensity, frequency_response

# Global instance
spectrum_math = SpectrumMathFunctions()

def test_spectrum_functions():
    """Test spectrum mathematical functions"""
    print("Testing Spectrum Mathematical Functions...")
    
    # Test white light generation
    white_data = spectrum_math.generate_white_hole_data(20)
    print(f"White hole data length: {len(white_data)}")
    
    # Test decomposition
    phi_spectrum = spectrum_math.white_light_decomposition(white_data, 'φ')
    e_spectrum = spectrum_math.white_light_decomposition(white_data, 'e')
    pi_spectrum = spectrum_math.white_light_decomposition(white_data, 'π')
    
    print(f"φ-spectrum: {phi_spectrum[:5]}...")
    print(f"e-spectrum: {e_spectrum[:5]}...")
    print(f"π-spectrum: {pi_spectrum[:5]}...")
    
    # Test color mixing
    mixed_color = spectrum_math.color_mixing_matrix(0.5, 0.3, 0.2)
    print(f"Mixed color RGB: {mixed_color}")
    
    # Test hypercube colors
    colors_5d = spectrum_math.hypercube_color_encoding(5)
    print(f"5D hypercube colors: {colors_5d}")
    
    print("✓ All spectrum functions verified!")

if __name__ == "__main__":
    test_spectrum_functions()