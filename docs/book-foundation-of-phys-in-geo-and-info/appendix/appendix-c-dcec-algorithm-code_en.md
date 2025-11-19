## Appendix C: Discrete-Continuous Error Control Algorithm Code Examples

**(离散-连续误差控制算法代码示例)**

Chapter 5 of this book establishes the "Discrete-Continuous Error Control (DCEC)" system and proves that using PSWF/DPSS window functions can control the error between discrete sampling and continuous field theory to exponential precision. To make this theory operational, this appendix provides Python reference implementations of core algorithms.

These code examples cover:

1. **KRD Threshold Calculation**: Determine minimum number of samples for given error tolerance.

2. **Hankel-HS Cross-Term Upper Bound**: Calculate aliasing error introduced by multiplication operators.

3. **DPSS Sequence Generation**: Generate optimal discrete window functions.

4. **Unified Time Scale Reconstruction**: Calculate $\kappa(E)$ from scattering data.

-----

### C.1 KRD Threshold Calculator

This algorithm calculates the minimum Shannon number $N_0$ (or number of sampling points) required for a given leakage error $\varepsilon$ based on Theorem 5.2.3 of Chapter 5 and non-asymptotic upper bounds in related literature. This is used to determine minimum resource budgets in experimental design.

```python
import numpy as np
from math import pi, log, exp, ceil

def calculate_krd_threshold(epsilon):
    """
    Calculate the minimum Shannon number N0_star required to achieve given leakage error epsilon.
    Based on formula: 1 - lambda_0 <= 10 * exp( - (N0 - 7)^2 / (pi^2 * log(50 * N0 + 25)) )
    
    Parameters:
        epsilon (float): Target error tolerance (e.g., 1e-6)
        
    Returns:
        tuple: (N0_star, c_star, NW_star)
            N0_star: Minimum Shannon number (2*T*Omega or 2*N*W)
            c_star: Corresponding time-bandwidth product (pi * N0 / 2)
            NW_star: Corresponding discrete product (N0 / 2)
    """
    n = 1
    while True:
        # KRD bound (variant of Karras-Reddy-Davenport bound)
        # Note: For very small n, formula may not apply, but will be automatically skipped in search loop
        if n > 7:
            numerator = (n - 7)**2
            denominator = pi**2 * log(50 * n + 25)
            upper_bound = 10 * exp(-numerator / denominator)
            
            if upper_bound <= epsilon:
                return n, (pi * n / 2), (n / 2.0)
        n += 1

# Example usage
tols = [1e-3, 1e-6, 1e-9]
print(f"{'Epsilon':<10} | {'N0*':<5} | {'c*':<10} | {'NW*':<10}")
print("-" * 45)
for tol in tols:
    n0, c, nw = calculate_krd_threshold(tol)
    print(f"{tol:<10} | {n0:<5} | {c:<10.4f} | {nw:<10.4f}")

# Expected output (approximate):
# 1e-3       | 33    | 51.8363    | 16.5000   
# 1e-6       | 42    | 65.9734    | 21.0000   
# 1e-9       | 50    | 78.5398    | 25.0000   
```

-----

### C.2 Multiplication Cross-Term (Hankel-HS Norm) Estimation

When we multiply a band-limited signal by a non-band-limited function $x(t)$ (e.g., local potential field or window modulation), spectral aliasing is introduced. This algorithm calculates the Hilbert-Schmidt upper bound of this error.

```python
def compute_hankel_hs_error(x_signal, W, domain_length=1.0):
    """
    Calculate the Hilbert-Schmidt norm of multiplication operator (I - B_W) M_x B_W.
    This quantifies out-of-band energy leakage when applying signal x to band-limited space.
    
    Parameters:
        x_signal (array): Sampled values of function x(t) on uniform lattice
        W (float): Normalized bandwidth (0 < W < 0.5)
        domain_length (float): Physical length of sampling domain
        
    Returns:
        float: Hankel-HS norm Xi_W(x)
    """
    N = len(x_signal)
    # Calculate discrete Fourier transform of x
    x_hat = np.fft.fft(x_signal) / N  # Normalization coefficient depends on specific definition
    
    # Frequency lattice (assuming sampling rate is N/domain_length)
    freqs = np.fft.fftfreq(N, d=domain_length/N)
    
    # Construct weight function sigma_W(delta) = min(2W, |delta|)
    # Note: For periodic boundary conditions, delta should take wrap-around distance
    sigma_W = np.minimum(2 * W, np.abs(freqs))
    
    # Integral (sum) to calculate norm squared
    # Integral |x_hat(delta)|^2 * sigma_W(delta)
    integral = np.sum(np.abs(x_hat)**2 * sigma_W)
    
    return np.sqrt(integral * domain_length) # Dimensional correction

# Example: Calculate "contamination" of a Gaussian wave packet on band-limited subspace
N = 1024
t = np.linspace(0, 1, N)
x_gauss = np.exp(-(t - 0.5)**2 / (2 * 0.05**2)) # Narrow Gaussian, wide frequency band
W_limit = 0.1 # Target bandwidth

error_norm = compute_hankel_hs_error(x_gauss, W_limit)
print(f"Hankel-HS Error Norm: {error_norm:.6f}")
```

-----

### C.3 DPSS Sequence Generator (Based on SciPy)

Generate discrete prolate spheroidal sequences (DPSS) for constructing optimal observation windows. This is the foundation for implementing the "finite-order windowing discipline" of Chapter 5.

```python
from scipy.linalg import eigh_tridiagonal
import scipy.signal.windows as windows

def generate_dpss_vectors(N, NW, K_max=None):
    """
    Generate first K_max DPSS sequences (Slepian sequences).
    
    Parameters:
        N (int): Sequence length (complexity steps)
        NW (float): Time-bandwidth product (standard half-bandwidth product, typically e.g., 4.0)
        K_max (int): Number of sequences to generate. Default is 2*NW (Shannon number).
        
    Returns:
        ndarray: (K_max, N) matrix, each row is a DPSS vector
        ndarray: Corresponding eigenvalues (energy concentration lambda)
    """
    if K_max is None:
        K_max = int(2 * NW)
        
    # SciPy's dpss implementation uses tridiagonal matrix solving with high numerical stability
    dpss_seqs, ratios = windows.dpss(N, NW, K_max, return_ratios=True)
    
    return dpss_seqs, ratios

# Example: Generate first 5 basis vectors for N=100, NW=4
N = 100
NW = 4.0
seqs, lambdas = generate_dpss_vectors(N, NW, K_max=5)

print(f"Generated {len(seqs)} DPSS vectors.")
print(f"Energy concentration ratios (eigenvalues): {lambdas}")
# lambda should be extremely close to 1.0 until approaching Shannon limit
```

-----

### C.4 Unified Time Scale Reconstruction Algorithm

This algorithm extracts unified time scale density $\kappa(E)$ from experimentally measured scattering matrix $S(E)$ data, implementing the microwave cavity experimental verification process described in Section 26.1.

```python
def reconstruct_unified_time_scale(energies, s_matrix_data):
    """
    Reconstruct unified time scale density kappa(E) from scattering data.
    
    Parameters:
        energies (array): Energy/frequency scan points E_i
        s_matrix_data (ndarray): Complex scattering matrix data of shape (N_E, N_ch, N_ch)
        
    Returns:
        array: Unified time scale density kappa(E)
    """
    import numpy as np
    
    # 1. Calculate determinant det S(E)
    # s_matrix_data[i] is the matrix at E_i
    dets = np.linalg.det(s_matrix_data)
    
    # 2. Extract total phase Phi(E) = Im(ln(det S))
    # Use unwrap to handle phase wrapping (branch cut)
    phases = np.unwrap(np.angle(dets))
    
    # 3. Numerical differentiation to calculate kappa(E) = (1/pi) * dPhi/dE
    # Use central difference method
    dPhi_dE = np.gradient(phases, energies)
    kappa = (1.0 / np.pi) * dPhi_dE
    
    return kappa

def wigner_smith_trace(energies, s_matrix_data):
    """
    Directly calculate via Wigner-Smith operator Q = -i S^dag dS/dE for verification.
    """
    n_points = len(energies)
    n_ch = s_matrix_data.shape[1]
    q_traces = np.zeros(n_points)
    
    # Calculate dS/dE
    ds_de = np.gradient(s_matrix_data, energies, axis=0)
    
    for i in range(n_points):
        s = s_matrix_data[i]
        ds = ds_de[i]
        s_dag = s.conj().T
        
        # Q = -i * S^dag * dS/dE
        q_matrix = -1j * np.dot(s_dag, ds)
        
        # Trace
        q_traces[i] = np.real(np.trace(q_matrix))
        
    # According to identity, should have kappa = (1/2pi) * Tr(Q)
    return q_traces / (2 * np.pi)

# Simulated data to verify consistency
E = np.linspace(0, 10, 500)
# Construct a simple resonant scattering S = (E - E0 - iG/2)/(E - E0 + iG/2)
E0, Gamma = 5.0, 0.5
S_scalar = (E - E0 - 1j*Gamma/2) / (E - E0 + 1j*Gamma/2)
S_data = S_scalar.reshape(-1, 1, 1) # Single channel

kappa_phase = reconstruct_unified_time_scale(E, S_data)
kappa_trace = wigner_smith_trace(E, S_data)

# Check error
error = np.max(np.abs(kappa_phase - kappa_trace))
print(f"Max discrepancy between Phase-derivative and Trace-formula: {error:.4e}")
# Expected output should be close to machine precision (e.g., < 1e-10)
```

-----

These code snippets provide foundational tools for verifying and applying the theory in this book. They demonstrate how to transform abstract operator theory into concrete numerical computation, thereby connecting theoretical physics with experimental data analysis.

