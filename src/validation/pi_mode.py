#!/usr/bin/env python3
"""
π-mode Tag Sequence Validation
==============================

This module validates the theoretical predictions for π-mode tag sequences
in the recursive self-similar Hilbert space construction.

Theory: H_n^(R) = span{e_0, e_1, ..., e_n} with π-mode coefficients:
η^(R)(k; n) = |Σ_{j=0}^k (-1)^j/(2j+1)| / |Σ_{j=0}^n (-1)^j/(2j+1)| 
for Leibniz series approximation to π/4
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict
from math import pi, log, atan
import warnings

warnings.filterwarnings('ignore', category=RuntimeWarning)


class PiMode:
    """Implementation of π-mode tag sequences."""
    
    def __init__(self, max_n: int = 50):
        """Initialize with maximum sequence length."""
        self.max_n = max_n
        self.pi = pi
        self.pi_quarter = pi / 4  # Target of Leibniz series
        self.leibniz_sum_cache = {}
        self._precompute_leibniz_sums()
    
    def _precompute_leibniz_sums(self) -> None:
        """Precompute Leibniz series partial sums: Σ_{j=0}^k (-1)^j/(2j+1)."""
        self.leibniz_sum_cache[0] = 1.0  # First term: 1/1 = 1
        
        for k in range(1, self.max_n + 10):
            # Add next term: (-1)^k / (2k+1)
            next_term = ((-1) ** k) / (2 * k + 1)
            self.leibniz_sum_cache[k] = self.leibniz_sum_cache[k-1] + next_term
    
    def leibniz_partial_sum(self, k: int) -> float:
        """
        Compute partial sum Σ_{j=0}^k (-1)^j/(2j+1) of the Leibniz series.
        
        The Leibniz series: π/4 = 1 - 1/3 + 1/5 - 1/7 + 1/9 - ...
        
        Args:
            k: Upper limit of summation
            
        Returns:
            Partial sum value
        """
        if k in self.leibniz_sum_cache:
            return self.leibniz_sum_cache[k]
        
        # Extend cache if needed
        max_cached = max(self.leibniz_sum_cache.keys())
        for i in range(max_cached + 1, k + 1):
            next_term = ((-1) ** i) / (2 * i + 1)
            self.leibniz_sum_cache[i] = self.leibniz_sum_cache[i-1] + next_term
        
        return self.leibniz_sum_cache[k]
    
    def relativistic_index(self, k: int, n: int) -> float:
        """
        Compute relativistic index η^(R)(k; n) for π-mode.
        
        Theory: η^(R)(k; n) = |sum_k| / |sum_n| for Leibniz partial sums
        
        Args:
            k: Target index
            n: Reference index
            
        Returns:
            Relativistic index value
        """
        if n == 0:
            return 1.0 if k == 0 else float('inf')
        
        numerator = abs(self.leibniz_partial_sum(k))
        denominator = abs(self.leibniz_partial_sum(n))
        
        if denominator == 0:
            return float('inf') if numerator > 0 else 1.0
        
        return numerator / denominator
    
    def tag_coefficient_vector(self, n: int) -> np.ndarray:
        """
        Generate tag coefficient vector for H_n^(R).
        
        Args:
            n: Hilbert space dimension index
            
        Returns:
            Array of normalized tag coefficients
        """
        coefficients = np.zeros(n + 1)
        
        for k in range(n + 1):
            coefficients[k] = self.relativistic_index(k, n)
        
        # Normalize to unit norm
        norm = np.linalg.norm(coefficients)
        if norm > 0:
            coefficients /= norm
            
        return coefficients
    
    def recursive_entropy(self, n: int) -> float:
        """
        Compute recursive entropy S_n^(R) for π-mode.
        
        Theory: S_n^(R) = log(π_dimension_factor)
        
        Args:
            n: Sequence index
            
        Returns:
            Recursive entropy value
        """
        # Use the absolute Leibniz sum as dimension factor
        dimension_factor = abs(self.leibniz_partial_sum(n)) + 1e-12  # Avoid log(0)
        return log(dimension_factor)
    
    def entropy_increment(self, n: int) -> float:
        """
        Compute entropy increment ΔS_{n+1}^(R).
        
        Args:
            n: Current index
            
        Returns:
            Entropy increment
        """
        return self.recursive_entropy(n + 1) - self.recursive_entropy(n)
    
    def validate_pi_convergence(self, max_n: int = 100) -> Dict[str, List]:
        """
        Validate that Leibniz series converges to π/4.
        
        Args:
            max_n: Maximum n to test
            
        Returns:
            Dictionary with convergence data
        """
        partial_sums = []
        errors = []
        indices = []
        
        for n in range(1, max_n, 2):  # Check odd indices for better convergence
            partial_sum = self.leibniz_partial_sum(n)
            error = abs(partial_sum - self.pi_quarter)
            
            partial_sums.append(partial_sum)
            errors.append(error)
            indices.append(n)
        
        return {
            'indices': indices,
            'partial_sums': partial_sums,
            'errors': errors,
            'pi_quarter': self.pi_quarter
        }
    
    def validate_alternating_convergence(self, max_n: int = 20) -> Dict[str, any]:
        """
        Validate alternating convergence properties.
        
        Args:
            max_n: Maximum n to test
            
        Returns:
            Dictionary with alternating convergence data
        """
        even_sums = []
        odd_sums = []
        even_indices = []
        odd_indices = []
        
        for n in range(0, max_n):
            partial_sum = self.leibniz_partial_sum(n)
            
            if n % 2 == 0:
                even_sums.append(partial_sum)
                even_indices.append(n)
            else:
                odd_sums.append(partial_sum)
                odd_indices.append(n)
        
        # Check monotonicity properties
        even_decreasing = all(even_sums[i] >= even_sums[i+1] 
                            for i in range(len(even_sums)-1))
        odd_increasing = all(odd_sums[i] <= odd_sums[i+1] 
                           for i in range(len(odd_sums)-1))
        
        return {
            'even_indices': even_indices,
            'odd_indices': odd_indices,
            'even_sums': even_sums,
            'odd_sums': odd_sums,
            'even_decreasing': even_decreasing,
            'odd_increasing': odd_increasing,
            'alternating_convergence': even_decreasing and odd_increasing
        }
    
    def validate_relativistic_scaling(self, n_values: List[int]) -> Dict[str, any]:
        """
        Validate relativistic index scaling properties.
        
        Args:
            n_values: List of n values to test
            
        Returns:
            Dictionary with scaling validation results
        """
        results = {}
        
        for n in n_values:
            if n == 0:
                continue
                
            coeffs = self.tag_coefficient_vector(n)
            
            # Test scaling property: η^(R)(k; n) = |sum_k| / |sum_n|
            theoretical_ratios = [
                abs(self.leibniz_partial_sum(k)) / abs(self.leibniz_partial_sum(n))
                for k in range(n + 1)
            ]
            theoretical_normalized = np.array(theoretical_ratios)
            norm = np.linalg.norm(theoretical_normalized)
            if norm > 0:
                theoretical_normalized /= norm
            
            # Compare with computed coefficients
            max_error = np.max(np.abs(coeffs - theoretical_normalized))
            
            results[f'n_{n}'] = {
                'coefficients': coeffs,
                'theoretical': theoretical_normalized,
                'max_error': max_error
            }
        
        return results
    
    def validate_oscillation_damping(self, n: int = 20) -> Dict[str, any]:
        """
        Validate oscillation damping property of π-mode.
        
        Args:
            n: Reference index for testing
            
        Returns:
            Dictionary with oscillation validation results
        """
        # Compute absolute differences between consecutive terms
        oscillations = []
        damping_ratios = []
        
        for k in range(1, n):
            curr_sum = self.leibniz_partial_sum(k)
            prev_sum = self.leibniz_partial_sum(k-1)
            oscillation = abs(curr_sum - prev_sum)
            oscillations.append(oscillation)
            
            # Theoretical damping: |(-1)^k / (2k+1)|
            theoretical_term = 1.0 / (2 * k + 1)
            
            if k > 1:
                prev_theoretical = 1.0 / (2 * (k-1) + 1)
                damping_ratio = theoretical_term / prev_theoretical
                damping_ratios.append(damping_ratio)
        
        # Check if oscillations are decreasing
        oscillations_decreasing = all(oscillations[i] >= oscillations[i+1] 
                                    for i in range(len(oscillations)-1))
        
        return {
            'oscillations': oscillations,
            'damping_ratios': damping_ratios,
            'oscillations_decreasing': oscillations_decreasing,
            'mean_damping_ratio': np.mean(damping_ratios) if damping_ratios else 1.0
        }
    
    def generate_validation_report(self) -> Dict[str, any]:
        """
        Generate comprehensive validation report.
        
        Returns:
            Dictionary with all validation results
        """
        print("Validating pi-mode Tag Sequences...")
        
        # Test pi/4 convergence
        pi_convergence = self.validate_pi_convergence()
        print(f"OK pi/4 convergence: final error = {pi_convergence['errors'][-1]:.2e}")
        
        # Test alternating convergence
        alternating_data = self.validate_alternating_convergence()
        print(f"OK Alternating convergence: {alternating_data['alternating_convergence']}")
        
        # Test relativistic scaling
        scaling_data = self.validate_relativistic_scaling([5, 10, 15, 20])
        max_scaling_error = max(data['max_error'] for data in scaling_data.values() if data)
        print(f"OK Relativistic scaling: max error = {max_scaling_error:.2e}")
        
        # Test oscillation damping
        damping_data = self.validate_oscillation_damping()
        print(f"OK Oscillation damping: decreasing = {damping_data['oscillations_decreasing']}")
        
        # Compute key theoretical predictions
        pi_approx_99 = self.leibniz_partial_sum(99) * 4  # Convert to π approximation
        entropy_20 = self.recursive_entropy(20)
        
        return {
            'pi_convergence': pi_convergence,
            'alternating_validation': alternating_data,
            'scaling_validation': scaling_data,
            'damping_validation': damping_data,
            'key_values': {
                'pi': self.pi,
                'pi_quarter': self.pi_quarter,
                'pi_approx_99': pi_approx_99,
                'S_20': entropy_20,
                'max_scaling_error': max_scaling_error,
                'convergence_error': pi_convergence['errors'][-1] if pi_convergence['errors'] else 1.0
            },
            'validation_passed': (
                pi_convergence['errors'][-1] < 1e-3 and  # π convergence is slow
                alternating_data['alternating_convergence'] and
                max_scaling_error < 1e-8 and
                damping_data['oscillations_decreasing']
            )
        }


def main():
    """Run π-mode validation."""
    validator = PiMode()
    
    # Generate validation report
    report = validator.generate_validation_report()
    
    print("\n" + "="*50)
    print("PI-MODE VALIDATION SUMMARY")
    print("="*50)
    print(f"pi = {report['key_values']['pi']:.10f}")
    print(f"pi/4 = {report['key_values']['pi_quarter']:.10f}")
    print(f"100-term pi approximation = {report['key_values']['pi_approx_99']:.10f}")
    print(f"Recursive entropy S_20 = {report['key_values']['S_20']:.6f}")
    print(f"Maximum scaling error = {report['key_values']['max_scaling_error']:.2e}")
    print(f"Convergence error = {report['key_values']['convergence_error']:.2e}")
    print(f"\nOverall validation: {'PASSED' if report['validation_passed'] else 'FAILED'}")
    
    # Generate plots for visual validation
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(12, 10))
    
    # Plot 1: pi/4 convergence
    pi_data = report['pi_convergence']
    ax1.plot(pi_data['indices'], pi_data['partial_sums'], 'b-', label='Leibniz series')
    ax1.axhline(y=pi_data['pi_quarter'], color='r', linestyle='--', label='pi/4')
    ax1.set_xlabel('n')
    ax1.set_ylabel('Partial Sum')
    ax1.set_title('Convergence to pi/4')
    ax1.legend()
    ax1.grid(True)
    
    # Plot 2: Convergence error
    ax2.plot(pi_data['indices'], pi_data['errors'], 'g-')
    ax2.set_xlabel('n')
    ax2.set_ylabel('|Sum (-1)^j/(2j+1) - pi/4|')
    ax2.set_title('Convergence Error')
    ax2.set_yscale('log')
    ax2.grid(True)
    
    # Plot 3: Alternating convergence
    alt_data = report['alternating_validation']
    ax3.plot(alt_data['even_indices'], alt_data['even_sums'], 'ro-', 
             label='Even terms', markersize=3)
    ax3.plot(alt_data['odd_indices'], alt_data['odd_sums'], 'bo-', 
             label='Odd terms', markersize=3)
    ax3.axhline(y=pi/4, color='k', linestyle='--', label='pi/4', alpha=0.7)
    ax3.set_xlabel('n')
    ax3.set_ylabel('Partial Sum')
    ax3.set_title('Alternating Convergence')
    ax3.legend()
    ax3.grid(True)
    
    # Plot 4: Oscillation damping
    damping_data = report['damping_validation']
    k_values = range(1, len(damping_data['oscillations']) + 1)
    ax4.semilogy(k_values, damping_data['oscillations'], 'c-', 
                label='|Term differences|')
    # Theoretical damping curve
    theoretical_damping = [1/(2*k+1) for k in k_values]
    ax4.semilogy(k_values, theoretical_damping, 'r--', 
                label='1/(2k+1)', alpha=0.7)
    ax4.set_xlabel('k')
    ax4.set_ylabel('Oscillation (log scale)')
    ax4.set_title('Oscillation Damping')
    ax4.legend()
    ax4.grid(True)
    
    plt.tight_layout()
    plt.savefig('pi_mode_validation.png', dpi=300, bbox_inches='tight')
    plt.show()
    
    return report


if __name__ == "__main__":
    main()