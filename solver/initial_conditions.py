# =============================================================================
#  initial_conditions.py — Taylor-Green, Perturbed TG, ABC/Beltrami
# =============================================================================

import jax.numpy as jnp
from jax.numpy.fft import fftn


def taylor_green_ic(solver, amplitude=2.0):
    """
    Standard Taylor-Green vortex on T^3.

    v = ( A sin(x) cos(y) cos(z),
         -A cos(x) sin(y) cos(z),
          0 )
    """
    X, Y, Z = solver.X, solver.Y, solver.Z
    A = amplitude

    u0 = A * jnp.sin(X) * jnp.cos(Y) * jnp.cos(Z)
    v0 = -A * jnp.cos(X) * jnp.sin(Y) * jnp.cos(Z)
    w0 = jnp.zeros_like(X)

    return fftn(u0), fftn(v0), fftn(w0)


def perturbed_taylor_green_ic(solver, amplitude=2.0, pert_frac=0.3,
                               k_range=(2, 6)):
    """
    Taylor-Green + high-wavenumber perturbations at k = k_range[0] .. k_range[1]-1.
    """
    X, Y, Z = solver.X, solver.Y, solver.Z
    A = amplitude
    p = pert_frac * A

    u0 = A * jnp.sin(X) * jnp.cos(Y) * jnp.cos(Z)
    v0 = -A * jnp.cos(X) * jnp.sin(Y) * jnp.cos(Z)
    w0 = jnp.zeros_like(X)

    for k in range(k_range[0], k_range[1]):
        u0 += (p / k) * jnp.sin(k * X) * jnp.cos(k * Y) * jnp.cos(k * Z)
        v0 += -(p / k) * jnp.cos(k * X) * jnp.sin(k * Y) * jnp.cos(k * Z)

    return fftn(u0), fftn(v0), fftn(w0)


def abc_ic(solver, A_coeff=1.0, B_coeff=1.0, C_coeff=1.0):
    """
    Arnold-Beltrami-Childress (ABC) flow.

    v = ( A sin(z) + C cos(y),
          B sin(x) + A cos(z),
          C sin(y) + B cos(x) )

    This is a Beltrami field: curl v = v (with eigenvalue lambda=1).
    """
    X, Y, Z = solver.X, solver.Y, solver.Z

    u0 = A_coeff * jnp.sin(Z) + C_coeff * jnp.cos(Y)
    v0 = B_coeff * jnp.sin(X) + A_coeff * jnp.cos(Z)
    w0 = C_coeff * jnp.sin(Y) + B_coeff * jnp.cos(X)

    return fftn(u0), fftn(v0), fftn(w0)


def rescale_to_energy(solver, u_hat, v_hat, w_hat, target_E):
    """
    Rescale velocity field so that kinetic energy = target_E.

    E = (1/2) <|v|^2>
    """
    from jax.numpy.fft import ifftn
    u = ifftn(u_hat).real
    v = ifftn(v_hat).real
    w = ifftn(w_hat).real
    E_current = 0.5 * jnp.mean(u**2 + v**2 + w**2)
    scale = jnp.sqrt(target_E / (E_current + 1e-30))
    return u_hat * scale, v_hat * scale, w_hat * scale
