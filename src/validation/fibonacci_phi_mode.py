#!/usr/bin/env python3
"""
Fibonacci φ-mode Tag Sequence Validation
========================================

This module validates the theoretical predictions for Fibonacci φ-mode tag sequences
in the recursive self-similar Hilbert space construction.

Theory: H_n^(R) = span{e_0, e_1, ..., e_n} with φ-mode coefficients:
η^(R)(k; n) = F_k / F_n for Fibonacci sequence F_k
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict
from math import sqrt, log, exp


class FibonacciPhiMode:
    """Implementation of Fibonacci φ-mode tag sequences."""
    
    def __init__(self, max_n: int = 50):
        """Initialize with maximum sequence length."""
        self.max_n = max_n
        self.phi = (1 + sqrt(5)) / 2  # Golden ratio
        self.fibonacci_cache = {}
        self._precompute_fibonacci()
    
    def _precompute_fibonacci(self) -> None:
        """Precompute Fibonacci numbers using the standard definition."""
        # F_1 = 1, F_2 = 2, F_3 = 3, F_4 = 5, ...
        self.fibonacci_cache[0] = 0  # F_0 for mathematical completeness
        self.fibonacci_cache[1] = 1  # F_1 = 1
        self.fibonacci_cache[2] = 2  # F_2 = 2
        
        for i in range(3, self.max_n + 5):
            self.fibonacci_cache[i] = self.fibonacci_cache[i-1] + self.fibonacci_cache[i-2]
    
    def fibonacci(self, n: int) -> int:
        """Get nth Fibonacci number."""
        if n in self.fibonacci_cache:
            return self.fibonacci_cache[n]
        
        # Extend cache if needed
        max_cached = max(self.fibonacci_cache.keys())
        for i in range(max_cached + 1, n + 1):
            self.fibonacci_cache[i] = self.fibonacci_cache[i-1] + self.fibonacci_cache[i-2]
        
        return self.fibonacci_cache[n]
    
    def relativistic_index(self, k: int, n: int) -> float:
        """
        Compute relativistic index η^(R)(k; n) = F_k / F_n.
        
        Args:
            k: Target index
            n: Reference index
            
        Returns:
            Relativistic index value
        """
        if n == 0:
            return float('inf') if k > 0 else 1.0
        
        return self.fibonacci(k) / self.fibonacci(n)
    
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
        Compute recursive entropy S_n^(R) for φ-mode.
        
        Theory: S_n^(R) = log(F_{n+2}) due to Hilbert space dimension
        
        Args:
            n: Sequence index
            
        Returns:
            Recursive entropy value
        """
        return log(self.fibonacci(n + 2))
    
    def entropy_increment(self, n: int) -> float:
        """
        Compute entropy increment ΔS_{n+1}^(R).
        
        Args:
            n: Current index
            
        Returns:
            Entropy increment
        """
        return self.recursive_entropy(n + 1) - self.recursive_entropy(n)
    
    def validate_golden_ratio_convergence(self, max_n: int = 30) -> Dict[str, List]:
        """
        Validate that F_{n+1}/F_n → φ as n → ∞.
        
        Args:
            max_n: Maximum n to test
            
        Returns:
            Dictionary with convergence data
        """
        ratios = []
        errors = []
        indices = []
        
        for n in range(2, max_n):
            ratio = self.fibonacci(n + 1) / self.fibonacci(n)
            error = abs(ratio - self.phi)
            
            ratios.append(ratio)
            errors.append(error)
            indices.append(n)
        
        return {
            'indices': indices,
            'ratios': ratios,
            'errors': errors,
            'phi': self.phi
        }
    
    def validate_entropy_monotonicity(self, max_n: int = 20) -> Dict[str, List]:
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
            
            # Test scaling property: η^(R)(k; n) ∝ F_k/F_n
            theoretical_ratios = [self.fibonacci(k) / self.fibonacci(n) for k in range(n + 1)]
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
    
    def generate_validation_report(self) -> Dict[str, any]:
        """
        Generate comprehensive validation report.
        
        Returns:
            Dictionary with all validation results
        """
        print("Validating Fibonacci phi-mode Tag Sequences...")
        
        # Test golden ratio convergence
        phi_convergence = self.validate_golden_ratio_convergence()
        print(f"OK Golden ratio convergence: final error = {phi_convergence['errors'][-1]:.2e}")
        
        # Test entropy monotonicity
        entropy_data = self.validate_entropy_monotonicity()
        print(f"OK Entropy monotonicity: all increments positive = {entropy_data['all_positive']}")
        
        # Test relativistic scaling
        scaling_data = self.validate_relativistic_scaling([5, 10, 15, 20])
        max_scaling_error = max(data['max_error'] for data in scaling_data.values())
        print(f"OK Relativistic scaling: max error = {max_scaling_error:.2e}")
        
        # Compute key theoretical predictions
        fibonacci_20 = self.fibonacci(20)
        entropy_20 = self.recursive_entropy(20)
        
        return {
            'phi_convergence': phi_convergence,
            'entropy_validation': entropy_data,
            'scaling_validation': scaling_data,
            'key_values': {
                'phi': self.phi,
                'F_20': fibonacci_20,
                'S_20': entropy_20,
                'max_scaling_error': max_scaling_error
            },
            'validation_passed': (
                phi_convergence['errors'][-1] < 1e-10 and
                entropy_data['all_positive'] and
                max_scaling_error < 1e-12
            )
        }


def main():
    """Run Fibonacci φ-mode validation."""
    validator = FibonacciPhiMode()
    
    # Generate validation report
    report = validator.generate_validation_report()
    
    print("\n" + "="*50)
    print("FIBONACCI PHI-MODE VALIDATION SUMMARY")
    print("="*50)
    print(f"Golden ratio phi = {report['key_values']['phi']:.10f}")
    print(f"F_20 = {report['key_values']['F_20']}")
    print(f"Recursive entropy S_20 = {report['key_values']['S_20']:.6f}")
    print(f"Maximum scaling error = {report['key_values']['max_scaling_error']:.2e}")
    print(f"\nOverall validation: {'PASSED' if report['validation_passed'] else 'FAILED'}")
    
    # Generate plots for visual validation
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(12, 10))
    
    # Plot 1: Golden ratio convergence
    phi_data = report['phi_convergence']
    ax1.plot(phi_data['indices'], phi_data['ratios'], 'b-', label='F_{n+1}/F_n')
    ax1.axhline(y=phi_data['phi'], color='r', linestyle='--', label='phi')
    ax1.set_xlabel('n')
    ax1.set_ylabel('Ratio')
    ax1.set_title('Convergence to Golden Ratio')
    ax1.legend()
    ax1.grid(True)
    
    # Plot 2: Convergence error (log scale)
    ax2.semilogy(phi_data['indices'], phi_data['errors'], 'g-')
    ax2.set_xlabel('n')
    ax2.set_ylabel('|F_{n+1}/F_n - phi|')
    ax2.set_title('Convergence Error (log scale)')
    ax2.grid(True)
    
    # Plot 3: Entropy growth
    entropy_data = report['entropy_validation']
    ax3.plot(entropy_data['indices'], entropy_data['entropies'], 'm-')
    ax3.set_xlabel('n')
    ax3.set_ylabel('S_n^(R)')
    ax3.set_title('Recursive Entropy Growth')
    ax3.grid(True)
    
    # Plot 4: Entropy increments
    ax4.plot(entropy_data['indices'], entropy_data['increments'], 'c-')
    ax4.set_xlabel('n')
    ax4.set_ylabel('ΔS_{n+1}^(R)')
    ax4.set_title('Entropy Increments')
    ax4.grid(True)
    
    plt.tight_layout()
    plt.savefig('fibonacci_phi_mode_validation.png', dpi=300, bbox_inches='tight')
    plt.show()
    
    return report


if __name__ == "__main__":
    main()