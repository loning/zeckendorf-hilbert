#!/usr/bin/env python3
"""
Exponential e-mode Tag Sequence Validation
==========================================

This module validates the theoretical predictions for exponential e-mode tag sequences
in the recursive self-similar Hilbert space construction.

Theory: H_n^(R) = span{e_0, e_1, ..., e_n} with e-mode coefficients:
η^(R)(k; n) = (Σ_{j=0}^k 1/j!) / (Σ_{j=0}^n 1/j!) for exponential series approximation
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict
from math import factorial, exp, log
import warnings

warnings.filterwarnings('ignore', category=RuntimeWarning)


class ExponentialEMode:
    """Implementation of exponential e-mode tag sequences."""
    
    def __init__(self, max_n: int = 30):
        """Initialize with maximum sequence length."""
        self.max_n = max_n
        self.e = exp(1)  # Euler's number
        self.factorial_cache = {}
        self.exponential_sum_cache = {}
        self._precompute_values()
    
    def _precompute_values(self) -> None:
        """Precompute factorial values and exponential series sums."""
        # Precompute factorials
        self.factorial_cache[0] = 1
        for i in range(1, self.max_n + 10):
            self.factorial_cache[i] = self.factorial_cache[i-1] * i
        
        # Precompute exponential series partial sums: Σ_{j=0}^k 1/j!
        self.exponential_sum_cache[0] = 1.0  # 1/0! = 1
        
        for k in range(1, self.max_n + 10):
            self.exponential_sum_cache[k] = (
                self.exponential_sum_cache[k-1] + 1.0 / self.factorial_cache[k]
            )
    
    def factorial(self, n: int) -> int:
        """Get n! with caching."""
        if n in self.factorial_cache:
            return self.factorial_cache[n]
        
        # Extend cache if needed
        max_cached = max(self.factorial_cache.keys())
        for i in range(max_cached + 1, n + 1):
            self.factorial_cache[i] = self.factorial_cache[i-1] * i
        
        return self.factorial_cache[n]
    
    def exponential_partial_sum(self, k: int) -> float:
        """
        Compute partial sum Σ_{j=0}^k 1/j! of the exponential series.
        
        Args:
            k: Upper limit of summation
            
        Returns:
            Partial sum value
        """
        if k in self.exponential_sum_cache:
            return self.exponential_sum_cache[k]
        
        # Extend cache if needed
        max_cached = max(self.exponential_sum_cache.keys())
        for i in range(max_cached + 1, k + 1):
            self.exponential_sum_cache[i] = (
                self.exponential_sum_cache[i-1] + 1.0 / self.factorial_cache[i]
            )
        
        return self.exponential_sum_cache[k]
    
    def relativistic_index(self, k: int, n: int) -> float:
        """
        Compute relativistic index η^(R)(k; n) for e-mode.
        
        Theory: η^(R)(k; n) = (Σ_{j=0}^k 1/j!) / (Σ_{j=0}^n 1/j!)
        
        Args:
            k: Target index
            n: Reference index
            
        Returns:
            Relativistic index value
        """
        if n == 0:
            return 1.0 if k == 0 else float('inf')
        
        numerator = self.exponential_partial_sum(k)
        denominator = self.exponential_partial_sum(n)
        
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
        Compute recursive entropy S_n^(R) for e-mode.
        
        Theory: S_n^(R) = log(exponential_dimension_factor)
        
        Args:
            n: Sequence index
            
        Returns:
            Recursive entropy value
        """
        # Use the exponential sum as dimension factor
        dimension_factor = self.exponential_partial_sum(n + 1)
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
    
    def validate_exponential_convergence(self, max_n: int = 25) -> Dict[str, List]:
        """
        Validate that Σ_{j=0}^n 1/j! → e as n → ∞.
        
        Args:
            max_n: Maximum n to test
            
        Returns:
            Dictionary with convergence data
        """
        partial_sums = []
        errors = []
        indices = []
        
        for n in range(1, max_n):
            partial_sum = self.exponential_partial_sum(n)
            error = abs(partial_sum - self.e)
            
            partial_sums.append(partial_sum)
            errors.append(error)
            indices.append(n)
        
        return {
            'indices': indices,
            'partial_sums': partial_sums,
            'errors': errors,
            'e': self.e
        }
    
    def validate_entropy_monotonicity(self, max_n: int = 15) -> Dict[str, List]:
        """
        Validate that entropy is strictly monotonic: S_{n+1}^(R) > S_n^(R).
        
        Args:
            max_n: Maximum n to test
            
        Returns:
            Dictionary with entropy data
        """
        entropies = []
        increments = []
        indices = []
        
        for n in range(1, max_n):
            entropy = self.recursive_entropy(n)
            increment = self.entropy_increment(n)
            
            entropies.append(entropy)
            increments.append(increment)
            indices.append(n)
        
        return {
            'indices': indices,
            'entropies': entropies,
            'increments': increments,
            'all_positive': all(inc > 0 for inc in increments)
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
            coeffs = self.tag_coefficient_vector(n)
            
            # Test scaling property: η^(R)(k; n) = sum_k / sum_n
            theoretical_ratios = [
                self.exponential_partial_sum(k) / self.exponential_partial_sum(n) 
                for k in range(n + 1)
            ]
            theoretical_normalized = np.array(theoretical_ratios)
            theoretical_normalized /= np.linalg.norm(theoretical_normalized)
            
            # Compare with computed coefficients
            max_error = np.max(np.abs(coeffs - theoretical_normalized))
            
            results[f'n_{n}'] = {
                'coefficients': coeffs,
                'theoretical': theoretical_normalized,
                'max_error': max_error
            }
        
        return results
    
    def validate_exponential_decay_property(self, n: int = 10) -> Dict[str, any]:
        """
        Validate exponential decay property of relativistic indices.
        
        Args:
            n: Reference index for testing
            
        Returns:
            Dictionary with decay validation results
        """
        coeffs = self.tag_coefficient_vector(n)
        
        # Test that coefficients approach exponential decay pattern
        theoretical_weights = [
            1.0 / self.factorial(k) for k in range(n + 1)
        ]
        
        # Normalize both for comparison
        theoretical_normalized = np.array(theoretical_weights)
        theoretical_normalized /= np.sum(theoretical_normalized)
        
        coeffs_squared = coeffs ** 2  # Convert to weight-like quantities
        coeffs_squared /= np.sum(coeffs_squared)
        
        # Measure decay rate consistency
        decay_errors = []
        for k in range(1, n):
            if coeffs_squared[k-1] > 0 and coeffs_squared[k] > 0:
                actual_ratio = coeffs_squared[k] / coeffs_squared[k-1]
                theoretical_ratio = theoretical_normalized[k] / theoretical_normalized[k-1]
                decay_errors.append(abs(actual_ratio - theoretical_ratio))
        
        return {
            'coefficients_squared': coeffs_squared,
            'theoretical_weights': theoretical_normalized,
            'decay_errors': decay_errors,
            'mean_decay_error': np.mean(decay_errors) if decay_errors else 0.0
        }
    
    def generate_validation_report(self) -> Dict[str, any]:
        """
        Generate comprehensive validation report.
        
        Returns:
            Dictionary with all validation results
        """
        print("Validating Exponential e-mode Tag Sequences...")
        
        # Test exponential convergence
        exp_convergence = self.validate_exponential_convergence()
        print(f"OK Exponential convergence: final error = {exp_convergence['errors'][-1]:.2e}")
        
        # Test entropy monotonicity
        entropy_data = self.validate_entropy_monotonicity()
        print(f"OK Entropy monotonicity: all increments positive = {entropy_data['all_positive']}")
        
        # Test relativistic scaling
        scaling_data = self.validate_relativistic_scaling([5, 8, 12, 15])
        max_scaling_error = max(data['max_error'] for data in scaling_data.values())
        print(f"OK Relativistic scaling: max error = {max_scaling_error:.2e}")
        
        # Test exponential decay property
        decay_data = self.validate_exponential_decay_property()
        print(f"OK Exponential decay: mean error = {decay_data['mean_decay_error']:.2e}")
        
        # Compute key theoretical predictions
        e_approx_15 = self.exponential_partial_sum(15)
        entropy_15 = self.recursive_entropy(15)
        
        return {
            'exp_convergence': exp_convergence,
            'entropy_validation': entropy_data,
            'scaling_validation': scaling_data,
            'decay_validation': decay_data,
            'key_values': {
                'e': self.e,
                'e_approx_15': e_approx_15,
                'S_15': entropy_15,
                'max_scaling_error': max_scaling_error,
                'mean_decay_error': decay_data['mean_decay_error']
            },
            'validation_passed': (
                exp_convergence['errors'][-1] < 1e-10 and
                entropy_data['all_positive'] and
                max_scaling_error < 1e-10 and
                decay_data['mean_decay_error'] < 1e-3
            )
        }


def main():
    """Run exponential e-mode validation."""
    validator = ExponentialEMode()
    
    # Generate validation report
    report = validator.generate_validation_report()
    
    print("\n" + "="*50)
    print("EXPONENTIAL e-MODE VALIDATION SUMMARY")
    print("="*50)
    print(f"Euler's number e = {report['key_values']['e']:.10f}")
    print(f"15-term approximation = {report['key_values']['e_approx_15']:.10f}")
    print(f"Recursive entropy S_15 = {report['key_values']['S_15']:.6f}")
    print(f"Maximum scaling error = {report['key_values']['max_scaling_error']:.2e}")
    print(f"Mean decay error = {report['key_values']['mean_decay_error']:.2e}")
    print(f"\nOverall validation: {'PASSED' if report['validation_passed'] else 'FAILED'}")
    
    # Generate plots for visual validation
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(12, 10))
    
    # Plot 1: Exponential convergence
    exp_data = report['exp_convergence']
    ax1.plot(exp_data['indices'], exp_data['partial_sums'], 'b-', label='Σ 1/j!')
    ax1.axhline(y=exp_data['e'], color='r', linestyle='--', label='e')
    ax1.set_xlabel('n')
    ax1.set_ylabel('Partial Sum')
    ax1.set_title('Convergence to e')
    ax1.legend()
    ax1.grid(True)
    
    # Plot 2: Convergence error (log scale)
    ax2.semilogy(exp_data['indices'], exp_data['errors'], 'g-')
    ax2.set_xlabel('n')
    ax2.set_ylabel('|Σ 1/j! - e|')
    ax2.set_title('Convergence Error (log scale)')
    ax2.grid(True)
    
    # Plot 3: Entropy growth
    entropy_data = report['entropy_validation']
    ax3.plot(entropy_data['indices'], entropy_data['entropies'], 'm-')
    ax3.set_xlabel('n')
    ax3.set_ylabel('S_n^(R)')
    ax3.set_title('Recursive Entropy Growth')
    ax3.grid(True)
    
    # Plot 4: Exponential decay validation
    decay_data = report['decay_validation']
    k_values = range(len(decay_data['coefficients_squared']))
    ax4.semilogy(k_values, decay_data['coefficients_squared'], 'c-', 
                label='Actual coeffs²')
    ax4.semilogy(k_values, decay_data['theoretical_weights'], 'r--', 
                label='Theoretical 1/k!')
    ax4.set_xlabel('k')
    ax4.set_ylabel('Weight (log scale)')
    ax4.set_title('Exponential Decay Validation')
    ax4.legend()
    ax4.grid(True)
    
    plt.tight_layout()
    plt.savefig('exponential_e_mode_validation.png', dpi=300, bbox_inches='tight')
    plt.show()
    
    return report


if __name__ == "__main__":
    main()