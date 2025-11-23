# Appendix B: QCA Simulation Guide

**Appendix B: Guide to Simulating QCA Universes**

Physics is not just for deriving formulas; it is also for **running**. The "unitary computational universe" constructed in this book exists not only in abstract Hilbert space, but can also be fully simulated on classical digital computers (though with efficiency limitations).

This appendix aims to provide a practical programming guide for readers who wish to "create universes" with their own hands. We will demonstrate how to build a simple one-dimensional Dirac-QCA model satisfying Axiom $\Omega$ using Python, and observe the emergence of mass, wave packet diffusion, and Zitterbewegung phenomena.

This is not only verification of the theory, but also a preliminary attempt at transformation from "observer" to "builder."

-----

## B.1 Basic Architecture of the Simulator

A QCA simulator mainly consists of three core modules:

1. **State Register**: Stores the current global wave function $|\Psi(t)\rangle$.

2. **Evolution Engine**: Executes local unitary operators $\hat{U}$.

3. **Measurement Module**: Computes observables (such as position probability distribution, momentum spectrum).

### B.1.1 Data Structure

In a one-dimensional QCA, we have a ring containing $L$ lattice points (periodic boundary conditions). Each lattice point has two components (left-handed $L$ and right-handed $R$).

Therefore, the wave function can be represented by a complex array of size $(L, 2)$.

```python
import numpy as np
import matplotlib.pyplot as plt

class QCAUniverse:
    def __init__(self, L, mass_theta):
        """
        Initialize QCA universe
        L: Number of lattice points (spatial size)
        mass_theta: Mass parameter θ (corresponding to m*c^2*dt/hbar)
        """
        self.L = L
        self.theta = mass_theta
        
        # Wave function psi[x, 0] = psi_L, psi[x, 1] = psi_R
        self.psi = np.zeros((L, 2), dtype=np.complex128)
        
        # Construct local rotation matrix (Coin Operator)
        c, s = np.cos(self.theta), np.sin(self.theta)
        self.coin_op = np.array([[c, -1j*s], 
                                 [-1j*s, c]])
```

## B.2 Evolution Algorithm: Split Operator Method

According to the Dirac-QCA model (see Chapter 5 of the main text), the single-step evolution operator decomposes as:

$$\hat{U} = \hat{S} \cdot \hat{C}(\theta)$$

where $\hat{C}$ is local rotation (mixing left and right chirality), and $\hat{S}$ is conditional translation.

### B.2.1 Code Implementation

```python
    def step(self):
        """Execute one time evolution step: U = S * C"""
        
        # 1. Coin Step (local rotation)
        # Matrix multiplication for each lattice point: psi(x) = C . psi(x)
        # Use einsum for acceleration: 'ij,xj->xi' (i,j are spin components, x is spatial)
        self.psi = np.einsum('ij,xj->xi', self.coin_op, self.psi)
        
        # 2. Shift Step (conditional translation)
        # L component (index 0) moves left (x -> x-1) -> np.roll shift=-1
        # R component (index 1) moves right (x -> x+1) -> np.roll shift=+1
        # Note: Directions may be opposite depending on definition, here using standard QW convention
        psi_L = np.roll(self.psi[:, 0], -1)
        psi_R = np.roll(self.psi[:, 1], 1)
        
        self.psi[:, 0] = psi_L
        self.psi[:, 1] = psi_R
```

## B.3 Initial Conditions and Observation

To simulate a particle, we need to initialize a Gaussian wave packet.

```python
    def initialize_wavepacket(self, x0, k0, sigma):
        """
        Initialize Gaussian wave packet
        x0: Center position
        k0: Initial momentum
        sigma: Wave packet width
        """
        x = np.arange(self.L)
        # Gaussian envelope * plane wave
        envelope = np.exp(-(x - x0)**2 / (4 * sigma**2))
        plane_wave = np.exp(1j * k0 * x)
        
        psi_init = envelope * plane_wave
        
        # Assign to L and R components (here simply set equal, corresponding to spin pointing in x direction)
        self.psi[:, 0] = psi_init / np.sqrt(2)
        self.psi[:, 1] = psi_init / np.sqrt(2)
        
        # Normalize
        norm = np.sqrt(np.sum(np.abs(self.psi)**2))
        self.psi /= norm

    def measure_probability(self):
        """Return position probability distribution P(x)"""
        return np.sum(np.abs(self.psi)**2, axis=1)
    
    def measure_expectation_x(self):
        """Calculate position expectation value <x>"""
        P = self.measure_probability()
        x = np.arange(self.L)
        # Careful handling of centroid under periodic boundary conditions, here assuming wave packet far from boundaries
        return np.sum(x * P)
```

## B.4 Experimental Script: Verifying Zitterbewegung

Now, let's run this universe and verify the core prediction of Chapter 5: **Massive particles tremble microscopically.**

```python
def run_zitterbewegung_experiment():
    L = 2000
    theta = 0.1  # Small mass parameter
    steps = 500
    
    universe = QCAUniverse(L, theta)
    # Initialize particle with momentum 0
    universe.initialize_wavepacket(x0=L//2, k0=0, sigma=20)
    
    trajectory = []
    
    for t in range(steps):
        universe.step()
        x_avg = universe.measure_expectation_x()
        trajectory.append(x_avg)
        
    # Plotting
    t_axis = np.arange(steps)
    plt.plot(t_axis, trajectory)
    plt.title("Zitterbewegung Simulation (QCA)")
    plt.xlabel("Time Step")
    plt.ylabel("Expectation Position <x>")
    plt.show()

if __name__ == "__main__":
    run_zitterbewegung_experiment()
```

**Expected Results**:

Running the above code, you will see that `<x>` is not a straight line (stationary), but exhibits **high-frequency, small-amplitude sinusoidal oscillation** near the initial position.

* Oscillation frequency $\omega \approx 2\theta$.

* This is the precise discrete reproduction of the Zitterbewegung phenomenon in the Dirac equation.

* If `theta` is set to 0 (photon), oscillation disappears, and the wave packet will split and fly toward both ends at speed $c$ (or remain stationary if not mixed).

## B.5 Advanced Challenge: Curved Spacetime Simulation

To simulate gravity in QCA (Chapter 4 content), we need to introduce **non-uniform refractive index**.

This can be achieved by making the mass parameter $\theta$ or translation operator $\hat{S}$ depend on position $x$.

**Modification Idea**:

In the `step` function, instead of using a uniform `self.theta`, use an array `self.theta_field[x]`.

* Near a "black hole," set `theta[x]` very large (close to $\pi/2$), which will cause $v_{int} \to c$, $v_{ext} \to 0$.

* Running the simulation, you will find that wave packets entering this region will drastically slow down, wavelengths compress, exhibiting characteristics of gravitational redshift and spacetime curvature.

In this way, you are not just learning physics; you are **coding physics**. Every logic gate is a natural law of this toy universe.

