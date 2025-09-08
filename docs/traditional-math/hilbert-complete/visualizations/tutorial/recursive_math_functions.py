#!/usr/bin/env python3
"""
Strict Mathematical Functions for Recursive Hilbert Theory Visualization
All calculations based on exact recursive theory definitions
"""

import numpy as np
import math
from typing import List, Tuple, Dict

class RecursiveMathFunctions:
    """Mathematical functions strictly based on recursive Hilbert theory"""
    
    def __init__(self):
        self.phi = (1 + np.sqrt(5)) / 2  # Golden ratio
        self.e = math.e
        self.pi = math.pi
    
    # ============ BASIC RECURSIVE FUNCTIONS ============
    
    def fibonacci_sequence(self, n_terms: int) -> List[int]:
        """Generate standard Fibonacci sequence: F0=0, F1=1, F2=1, F3=2, F4=3, F5=5, ..."""
        if n_terms <= 0:
            return []
        elif n_terms == 1:
            return [0]
        elif n_terms == 2:
            return [0, 1]
        elif n_terms == 3:
            return [0, 1, 1]
        
        fib = [0, 1, 1]
        for i in range(2, n_terms):
            fib.append(fib[i-1] + fib[i-2])
        return fib
    
    def factorial_sequence(self, n_terms: int) -> List[float]:
        """Generate exact factorial sequence: a_k = 1/k!"""
        return [1/math.factorial(k) for k in range(n_terms)]
    
    def leibniz_sequence(self, n_terms: int) -> List[float]:
        """Generate exact Leibniz sequence: a_k = (-1)^(k-1)/(2k-1)"""
        return [(-1)**(k-1) / (2*k-1) for k in range(1, n_terms+1)]
    
    # ============ CONVERGENCE CALCULATIONS ============
    
    def phi_mode_convergence(self, n_terms: int) -> Tuple[List[float], float]:
        """Calculate φ-mode convergence: F_ratio → φ"""
        fib = self.fibonacci_sequence(n_terms)
        if len(fib) < 2:
            return [], 0
        
        ratios = [fib[i+1]/fib[i] for i in range(len(fib)-1)]
        final_value = ratios[-1] if ratios else 0
        return ratios, final_value
    
    def e_mode_convergence(self, n_terms: int) -> Tuple[List[float], float]:
        """Calculate e-mode convergence: F_sum → e"""
        factorial_terms = self.factorial_sequence(n_terms)
        partial_sums = [sum(factorial_terms[:i+1]) for i in range(len(factorial_terms))]
        final_value = partial_sums[-1] if partial_sums else 0
        return partial_sums, final_value
    
    def pi_mode_convergence(self, n_terms: int) -> Tuple[List[float], float]:
        """Calculate π-mode convergence: F_weighted → π"""
        leibniz_terms = self.leibniz_sequence(n_terms)
        partial_sums = [4 * sum(leibniz_terms[:i+1]) for i in range(len(leibniz_terms))]
        final_value = partial_sums[-1] if partial_sums else 0
        return partial_sums, final_value
    
    # ============ 4D HYPERCUBE GEOMETRY ============
    
    def generate_tesseract_vertices(self) -> np.ndarray:
        """Generate all 16 vertices of 4D hypercube (tesseract)"""
        vertices = []
        for i in range(16):  # 2^4 = 16 vertices
            vertex = [(i >> j) & 1 for j in range(4)]  # Binary representation
            vertices.append(vertex)
        return np.array(vertices, dtype=float)
    
    def tesseract_edges(self) -> List[Tuple[int, int]]:
        """Generate all edges of tesseract (vertices differing by 1 bit)"""
        edges = []
        for i in range(16):
            for j in range(i+1, 16):
                if bin(i ^ j).count('1') == 1:  # Adjacent vertices in 4D
                    edges.append((i, j))
        return edges
    
    def project_4d_to_3d(self, vertices_4d: np.ndarray, w_distance: float = 3.0) -> np.ndarray:
        """Project 4D tesseract to 3D using perspective projection"""
        vertices_3d = []
        for v in vertices_4d:
            x, y, z, w = v
            # Perspective projection formula
            scale = w_distance / (w_distance + w)
            projected = [(x - 0.5) * scale, (y - 0.5) * scale, (z - 0.5) * scale]
            vertices_3d.append(projected)
        return np.array(vertices_3d)
    
    # ============ OBSERVER SEQUENCES ============
    
    def generate_finite_observer_sequence(self, start_point: Tuple[float, float], 
                                        sequence_length: int, 
                                        operation_schedule: List[str]) -> Dict:
        """Generate finite observer sequence with operation schedule"""
        
        if len(operation_schedule) != sequence_length:
            raise ValueError("Operation schedule length must match sequence length")
        
        sequence_data = []
        trajectory_x = [start_point[0]]
        trajectory_y = [start_point[1]]
        
        for step, operation in enumerate(operation_schedule):
            if operation == 'φ':
                # Fibonacci-like growth
                if step < 2:
                    data_value = 1
                else:
                    data_value = sequence_data[step-1] + sequence_data[step-2]
                
                # Trajectory grows outward
                angle = step * 0.3
                radius = 0.5 + step * 0.1
                next_x = trajectory_x[-1] + radius * np.cos(angle) * 0.1
                next_y = trajectory_y[-1] + radius * np.sin(angle) * 0.1
                
            elif operation == 'e':
                # Factorial-like decay
                data_value = 10 / math.factorial(min(step, 6) + 1)
                
                # Trajectory converges inward
                angle = step * 0.4
                radius = max(0.1, 1 - step * 0.05)
                next_x = trajectory_x[-1] + radius * np.cos(angle) * 0.05
                next_y = trajectory_y[-1] + radius * np.sin(angle) * 0.05
                
            else:  # π operation
                # Leibniz-like oscillation
                data_value = 5 * (-1)**step / (2*step + 1)
                
                # Trajectory oscillates
                angle = step * 0.5 + np.pi * step
                radius = 0.8 + 0.3 * np.sin(step)
                next_x = trajectory_x[-1] + radius * np.cos(angle) * 0.08
                next_y = trajectory_y[-1] + radius * np.sin(angle) * 0.08
            
            sequence_data.append(data_value)
            trajectory_x.append(next_x)
            trajectory_y.append(next_y)
        
        return {
            'data': sequence_data,
            'trajectory_x': trajectory_x[1:],  # Remove initial point
            'trajectory_y': trajectory_y[1:],
            'operations': operation_schedule,
            'start': start_point,
            'length': sequence_length
        }
    
    # ============ RELATIVISTIC INDEX CALCULATIONS ============
    
    def relativistic_index(self, k: int, m: int, mode: str) -> float:
        """Calculate relativistic index η(k;m) for different modes"""
        
        if mode == 'φ':
            # φ-mode: F_finite(k)/F_finite(m) for Fibonacci
            if m == 0:
                m = 1  # Avoid division by zero
            fib_k = self.fibonacci_sequence(k+1)[-1] if k >= 0 else 1
            fib_m = self.fibonacci_sequence(m+1)[-1] if m >= 0 else 1
            return fib_k / fib_m
            
        elif mode == 'e':
            # e-mode: factorial ratio
            if m < 0 or k < 0:
                return 1
            return math.factorial(m) / math.factorial(k) if k <= m else math.factorial(k) / math.factorial(m)
            
        else:  # π-mode
            # π-mode: alternating series ratio
            if m <= 0:
                m = 1
            if k <= 0:
                k = 1
            leibniz_k = abs((-1)**(k-1) / (2*k-1))
            leibniz_m = abs((-1)**(m-1) / (2*m-1))
            return leibniz_k / leibniz_m
    
    # ============ ENTROPY CALCULATIONS ============ 
    
    def recursive_entropy(self, probability_distribution: List[float]) -> float:
        """Calculate recursive von Neumann entropy: S = -Σ p_k log p_k"""
        entropy = 0
        for p in probability_distribution:
            if p > 0:  # Avoid log(0)
                entropy -= p * np.log(p)
        return entropy
    
    def entropy_increase_function(self, n: int, mode: str) -> float:
        """Calculate entropy increase g(η(n+1;n)) > 0"""
        
        eta = self.relativistic_index(n+1, n, mode)
        
        if mode == 'φ':
            return self.phi ** (-n) if n >= 0 else 1
        elif mode == 'e':
            return 1 / math.factorial(n+1) if n >= 0 else 1
        else:  # π-mode
            return 1 / (2*n + 1) if n >= 0 else 1
    
    # ============ PHASE TRANSITION CALCULATIONS ============
    
    def phase_transition_order_parameter(self, control_param: float, critical_point: float = 0) -> float:
        """Calculate order parameter with phase transition at critical point"""
        shifted_param = control_param - critical_point
        return np.tanh(shifted_param * 3)  # Sharp transition at critical point
    
    def critical_entropy_behavior(self, control_param: float, critical_point: float = 0) -> float:
        """Calculate entropy behavior near critical point (maximum at critical point)"""
        shifted_param = control_param - critical_point
        return 2 + 1.5 * np.exp(-(shifted_param**2) * 4)
    
    # ============ COORDINATE SYSTEM TRANSFORMATIONS ============
    
    def subjective_coordinate_transform(self, objective_coords: Tuple[float, float],
                                      observer_sequence: Dict) -> Tuple[float, float]:
        """Transform objective coordinates to observer's subjective coordinates"""
        
        obj_x, obj_y = objective_coords
        
        # Observer's time axis is their trajectory
        traj_x = observer_sequence['trajectory_x']
        traj_y = observer_sequence['trajectory_y']
        
        if len(traj_x) == 0:
            return obj_x, obj_y
        
        # Find closest point on observer's trajectory (subjective time coordinate)
        distances = [(obj_x - tx)**2 + (obj_y - ty)**2 for tx, ty in zip(traj_x, traj_y)]
        min_idx = distances.index(min(distances))
        
        # Subjective coordinates
        subjective_time = min_idx  # Time coordinate along observer's sequence
        subjective_data = observer_sequence['data'][min_idx] if min_idx < len(observer_sequence['data']) else 0
        
        return subjective_time, subjective_data
    
    # ============ HOLOGRAPHIC CORE SAMPLING ============
    
    def sample_holographic_core(self, sampling_curve: List[Tuple[float, float]]) -> List[float]:
        """Sample holographic core data using observer's sampling curve"""
        
        # Holographic core function (contains all possible information)
        def core_function(x: float, y: float) -> float:
            """Complete holographic data function"""
            r = np.sqrt(x**2 + y**2)
            theta = np.arctan2(y, x)
            
            # Rich holographic structure with multiple harmonics
            value = (3 + 
                    2 * np.sin(theta * 3) + 
                    np.cos(theta * 5) + 
                    0.8 * np.sin(theta * 7) +
                    0.5 * np.cos(r * 4) +
                    0.3 * np.sin(r * 6))
            
            return value
        
        # Sample the core at each point of the observer's curve
        sampled_data = []
        for x, y in sampling_curve:
            sampled_data.append(core_function(x, y))
        
        return sampled_data

# Global instance for easy import
recursive_math = RecursiveMathFunctions()

def test_mathematical_functions():
    """Test all mathematical functions to ensure correctness"""
    print("Testing Recursive Mathematical Functions...")
    
    # Test Fibonacci
    fib = recursive_math.fibonacci_sequence(10)
    print(f"Fibonacci(10): {fib}")
    assert fib == [1, 1, 2, 3, 5, 8, 13, 21, 34, 55], "Fibonacci calculation error"
    
    # Test factorial
    fact = recursive_math.factorial_sequence(5)
    expected_fact = [1, 1, 1/2, 1/6, 1/24]
    print(f"Factorial sequence(5): {fact}")
    assert all(abs(a-b) < 1e-10 for a, b in zip(fact, expected_fact)), "Factorial calculation error"
    
    # Test Leibniz
    leibniz = recursive_math.leibniz_sequence(5)
    expected_leibniz = [1, -1/3, 1/5, -1/7, 1/9]
    print(f"Leibniz sequence(5): {leibniz}")
    assert all(abs(a-b) < 1e-10 for a, b in zip(leibniz, expected_leibniz)), "Leibniz calculation error"
    
    # Test convergence
    phi_ratios, phi_final = recursive_math.phi_mode_convergence(15)
    print(f"φ-mode final convergence: {phi_final:.6f}, target φ: {recursive_math.phi:.6f}")
    
    e_sums, e_final = recursive_math.e_mode_convergence(10)
    print(f"e-mode final convergence: {e_final:.6f}, target e: {recursive_math.e:.6f}")
    
    pi_sums, pi_final = recursive_math.pi_mode_convergence(50)
    print(f"π-mode final convergence: {pi_final:.6f}, target π: {recursive_math.pi:.6f}")
    
    # Test tesseract
    vertices = recursive_math.generate_tesseract_vertices()
    edges = recursive_math.tesseract_edges()
    print(f"Tesseract: {len(vertices)} vertices, {len(edges)} edges")
    assert len(vertices) == 16, "Tesseract vertex count error"
    assert len(edges) == 32, "Tesseract edge count error"
    
    print("✓ All mathematical functions verified!")

if __name__ == "__main__":
    test_mathematical_functions()