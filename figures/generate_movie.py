#!/usr/bin/env python3
"""
generate_movie.py — Supplementary Movie 1

Animated R(k,t) shell-resolved budget for the low-viscosity
Taylor-Green case (nu=0.005, T=6.0).

Shows the cascade front k_f(t) advancing, saturating and receding
against the k^4 dissipative barrier.

Usage:
  python figures/generate_movie.py

Output:
  figures/movie1_shell_dynamics.mp4
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm
import matplotlib.animation as animation

# --- Load data ---
d = np.load('data/fig4_shell_lowvis.npz')
times = d['times']
ks = d['k_shells']
Rk = d['shell_Rk']
Rs_global = d['Rs']
Omegas = d['Omegas']

# --- Trim to useful range ---
k_max_plot = 45
k_mask = ks <= k_max_plot
ks_plot = ks[k_mask]
Rk_plot = Rk[:, k_mask]

# --- Precompute cascade front ---
kf = []
for i in range(len(times)):
    above = np.where((Rk[i, k_mask] > 1.0) & (ks_plot > 0))[0]
    kf.append(float(ks_plot[above[-1]]) if len(above) > 0 else 0.0)
kf = np.array(kf)

# --- JFM style ---
plt.rcParams.update({
    'font.family': 'serif',
    'font.size': 11,
    'axes.labelsize': 12,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'lines.linewidth': 1.5,
})

# --- Setup figure ---
fig = plt.figure(figsize=(10, 6))
gs = fig.add_gridspec(2, 2, height_ratios=[3, 1.2], width_ratios=[3, 1],
                      hspace=0.25, wspace=0.3)

ax_bar = fig.add_subplot(gs[0, 0])      # R(k) bar/line at current t
ax_heatmap = fig.add_subplot(gs[0, 1])  # mini R(k,t) heatmap with time marker
ax_R = fig.add_subplot(gs[1, 0])        # global R(t)
ax_Om = fig.add_subplot(gs[1, 1])       # Omega(t)

# --- Static elements ---

# Mini heatmap (right top)
norm_hm = TwoSlopeNorm(vmin=0, vcenter=1.0, vmax=min(Rk_plot.max(), 15.0))
ax_heatmap.pcolormesh(times, ks_plot, Rk_plot.T,
                      cmap='RdBu_r', norm=norm_hm, shading='auto', rasterized=True)
try:
    ax_heatmap.contour(times, ks_plot, Rk_plot.T, levels=[1.0],
                       colors='k', linewidths=0.5)
except:
    pass
ax_heatmap.set_ylabel(r'$k$')
ax_heatmap.set_xlabel(r'$t$')
ax_heatmap.set_ylim(0, k_max_plot)
ax_heatmap.set_title(r'$R(k,t)$ map', fontsize=10)
time_line_hm = ax_heatmap.axvline(0, color='lime', lw=1.5, ls='-')

# Global R(t) (bottom left)
ax_R.plot(times, Rs_global, 'k-', lw=0.8)
ax_R.axhline(1.0, color='grey', ls='--', lw=0.6)
ax_R.set_xlabel(r'$t$')
ax_R.set_ylabel(r'$R(t)$')
ax_R.set_xlim(0, times[-1])
ax_R.set_ylim(0, max(Rs_global) * 1.1)
dot_R = ax_R.plot([], [], 'ro', ms=6, zorder=5)[0]

# Omega(t) (bottom right)
ax_Om.plot(times, Omegas, 'k-', lw=0.8)
ax_Om.set_xlabel(r'$t$')
ax_Om.set_ylabel(r'$\Omega(t)$')
ax_Om.set_xlim(0, times[-1])
ax_Om.set_ylim(0, max(Omegas) * 1.1)
dot_Om = ax_Om.plot([], [], 'ro', ms=6, zorder=5)[0]

# R(k) snapshot (left top) — initialized empty
Rk_max_global = min(Rk_plot.max(), 15.0)
ax_bar.set_xlim(0, k_max_plot)
ax_bar.set_ylim(0, Rk_max_global * 1.1)
ax_bar.axhline(1.0, color='grey', ls='--', lw=0.8, label=r'$R=1$')
ax_bar.set_xlabel(r'$k$')
ax_bar.set_ylabel(r'$R(k,t)$')

# colored fill above/below R=1
line_Rk, = ax_bar.plot([], [], 'k-', lw=1.2)
fill_above = None
fill_below = None

# cascade front marker
kf_marker = ax_bar.axvline(0, color='red', ls=':', lw=1.0, alpha=0)

# title and time label
title_text = ax_bar.set_title('', fontsize=12)

# --- Animation function ---
def animate(frame):
    global fill_above, fill_below

    t_now = times[frame]
    Rk_now = Rk_plot[frame]

    # Update R(k) snapshot
    line_Rk.set_data(ks_plot, Rk_now)

    # Remove old fills
    if fill_above is not None:
        fill_above.remove()
    if fill_below is not None:
        fill_below.remove()

    # Fill above R=1 (red) and below (blue)
    fill_above = ax_bar.fill_between(
        ks_plot, 1.0, Rk_now, where=(Rk_now > 1.0),
        color='firebrick', alpha=0.3, interpolate=True)
    fill_below = ax_bar.fill_between(
        ks_plot, Rk_now, 1.0, where=(Rk_now < 1.0),
        color='steelblue', alpha=0.3, interpolate=True)

    # Cascade front
    kf_now = kf[frame]
    if kf_now > 0:
        kf_marker.set_xdata([kf_now, kf_now])
        kf_marker.set_alpha(1.0)
    else:
        kf_marker.set_alpha(0.0)

    # Update title
    status = 'PRODUCTION' if Rs_global[frame] > 1 else 'DISSIPATION'
    color = 'firebrick' if Rs_global[frame] > 1 else 'steelblue'
    title_text.set_text(
        f'$t = {t_now:.2f}$    '
        f'$R = {Rs_global[frame]:.2f}$    '
        f'$\\Omega = {Omegas[frame]:.2f}$    '
        f'[{status}]')
    title_text.set_color(color)

    # Update time marker on heatmap
    time_line_hm.set_xdata([t_now, t_now])

    # Update dots on global plots
    dot_R.set_data([t_now], [Rs_global[frame]])
    dot_Om.set_data([t_now], [Omegas[frame]])

    return (line_Rk, fill_above, fill_below, kf_marker,
            title_text, time_line_hm, dot_R, dot_Om)


# --- Create animation ---
n_frames = len(times)
print(f"  Generating movie: {n_frames} frames ...")

ani = animation.FuncAnimation(
    fig, animate, frames=n_frames,
    interval=80,   # ms per frame (~12.5 fps)
    blit=False,
    repeat=False)

# --- Save ---
outpath = 'figures/movie1_shell_dynamics.mp4'
writer = animation.FFMpegWriter(fps=12, bitrate=2000,
                                extra_args=['-vcodec', 'libx264',
                                            '-pix_fmt', 'yuv420p'])
ani.save(outpath, writer=writer)
plt.close(fig)

print(f"  Movie saved: {outpath}")
print(f"  Frames: {n_frames}, Duration: {n_frames/12:.1f}s")
print(f"\n  This movie shows the time evolution of the shell-resolved")
print(f"  stretching-to-dissipation ratio R(k,t) for the low-viscosity")
print(f"  Taylor-Green case (nu=0.005, T=6.0).")
print(f"  Red regions: R(k)>1 (production-dominated)")
print(f"  Blue regions: R(k)<1 (dissipation-dominated)")
print(f"  Red dashed line: cascade front k_f(t)")
