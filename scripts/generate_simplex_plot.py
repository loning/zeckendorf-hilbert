#!/usr/bin/env python3
"""
Generate simplex plot for ζ-information triadic balance theory
Shows the triangular simplex with norm contours and critical line prediction
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib.colors import LinearSegmentedColormap

def barycentric_to_cartesian(a, b, c):
    """Convert barycentric coordinates to Cartesian"""
    x = 0.5 * (2*b + c)
    y = (np.sqrt(3)/2) * c
    return x, y

def cartesian_to_barycentric(x, y):
    """Convert Cartesian coordinates to barycentric"""
    c = (2/np.sqrt(3)) * y
    b = x - c/2
    a = 1 - b - c
    return a, b, c

def norm_function(a, b, c):
    """Calculate the Euclidean norm of the vector (a,b,c)"""
    return np.sqrt(a**2 + b**2 + c**2)

def generate_simplex_plot():
    """Generate the simplex plot with norm contours"""

    # Create figure
    fig, ax = plt.subplots(figsize=(12, 10))

    # Define simplex vertices
    vertices = np.array([[0, 0], [1, 0], [0.5, np.sqrt(3)/2]])

    # Plot simplex triangle
    triangle = Polygon(vertices, fill=False, edgecolor='black', linewidth=2)
    ax.add_patch(triangle)

    # Add vertex labels
    ax.text(-0.05, -0.05, '(1,0,0)\n$i_+ = 1$', fontsize=12, ha='right')
    ax.text(1.05, -0.05, '(0,1,0)\n$i_0 = 1$', fontsize=12, ha='left')
    ax.text(0.5, np.sqrt(3)/2 + 0.05, '(0,0,1)\n$i_- = 1$', fontsize=12, ha='center')

    # Generate grid points inside simplex
    n_points = 200
    x_vals = np.linspace(0, 1, n_points)
    y_vals = np.linspace(0, np.sqrt(3)/2, n_points)
    X, Y = np.meshgrid(x_vals, y_vals)

    # Convert to barycentric and filter points inside simplex
    A = np.zeros_like(X)
    B = np.zeros_like(X)
    C = np.zeros_like(X)

    for i in range(n_points):
        for j in range(n_points):
            a, b, c = cartesian_to_barycentric(X[i,j], Y[i,j])
            if a >= 0 and b >= 0 and c >= 0 and abs(a + b + c - 1) < 1e-10:
                A[i,j] = a
                B[i,j] = b
                C[i,j] = c
            else:
                A[i,j] = np.nan
                B[i,j] = c = np.nan
                C[i,j] = np.nan

    # Calculate norm
    Z = norm_function(A, B, C)

    # Create custom colormap (blue for low entropy, red for high entropy)
    colors = [(0, 'darkblue'), (0.5, 'cyan'), (1, 'red')]
    cmap = LinearSegmentedColormap.from_list('entropy_cmap', colors)

    # Plot norm contours
    cs = ax.contourf(X, Y, Z, levels=np.linspace(1/np.sqrt(3), 1, 20),
                     cmap=cmap, alpha=0.7)

    # Add contour lines
    contour_levels = [1/np.sqrt(3), 0.8, 0.9, 1.0]
    cs_lines = ax.contour(X, Y, Z, levels=contour_levels, colors='black', linewidths=1)

    # Label contour lines
    ax.clabel(cs_lines, inline=True, fontsize=10, fmt='%.3f')

    # Mark special points
    # Center point (maximum entropy)
    center_x, center_y = barycentric_to_cartesian(1/3, 1/3, 1/3)
    ax.plot(center_x, center_y, 'ko', markersize=10, markerfacecolor='white')
    ax.text(center_x, center_y - 0.05, '$(\\frac{1}{3},\\frac{1}{3},\\frac{1}{3})$\n$|\\vec{i}| = 1/\\sqrt{3}$\nMax Entropy', fontsize=10, ha='center')

    # Critical line prediction point
    crit_x, crit_y = barycentric_to_cartesian(0.5, 0, 0.5)
    ax.plot(crit_x, crit_y, 'r*', markersize=15, markerfacecolor='red')
    ax.text(crit_x, crit_y + 0.03, '$(0.5, 0, 0.5)$\n$|\\vec{i}| = 1/\\sqrt{2} \\approx 0.707$\nCritical Line\nPrediction', fontsize=10, ha='center', color='red')

    # Add colorbar
    cbar = plt.colorbar(cs, ax=ax, shrink=0.8)
    cbar.set_label('$|\\vec{i}|$ (Vector Norm)', fontsize=12)

    # Set axis properties
    ax.set_xlim(-0.1, 1.1)
    ax.set_ylim(-0.1, np.sqrt(3)/2 + 0.1)
    ax.set_aspect('equal')
    ax.axis('off')

    # Title
    ax.set_title('ζ-Information Triadic Balance: Simplex Geometry\n' +
                'Scalar Conservation ($|\\vec{i}|_1 = 1$) vs Geometric Structure ($|\\vec{i}|_2$)',
                fontsize=14, pad=20)

    # Add explanation text
    explanation = """
    Vector $\\vec{i} = (i_+, i_0, i_-)$ represents information distribution in ζ-function framework:
    • $i_+$: Constructive information (particles, discrete spectra)
    • $i_0$: Wave information (interference, superposition)
    • $i_-$: Compensatory information (vacuum energy, Casimir effect)

    Norm contours show entropy levels (higher norm = lower entropy).
    Critical line prediction: $\\lim_{T\\to\\infty} \\mathbb{E}[|\\vec{i}(T)|] = 1/\\sqrt{2}$
    """

    ax.text(0.02, 0.02, explanation, transform=ax.transAxes,
            fontsize=9, verticalalignment='bottom',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='lightgray', alpha=0.8))

    plt.tight_layout()
    return fig, ax

def save_plot(filename='zeta_simplex_plot.png', dpi=300):
    """Save the plot to file"""
    fig, ax = generate_simplex_plot()
    plt.savefig(filename, dpi=dpi, bbox_inches='tight')
    print(f"Plot saved as {filename}")
    plt.close()

if __name__ == '__main__':
    save_plot()
    print("ζ-simplex visualization generated successfully!")
