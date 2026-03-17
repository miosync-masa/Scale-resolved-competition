#!/usr/bin/env python3
"""
generate_all_figures.py — Produce all 6 main figures for JFM submission.

Reads .npz files from data/ and outputs vector PDFs to figures/

  Fig.1  Baseline global budget: Omega, P, D, R
  Fig.2  Viscosity dependence: R(t), Omega(t)
  Fig.3  Baseline R(k,t) heatmap + k_f(t)
  Fig.4  Low-nu long-time R(k,t) heatmap + k_f(t)
  Fig.5  Matched-energy: TG vs perturbed TG
  Fig.6  TG vs ABC/Beltrami geometry effect

Usage:
  python figures/generate_all_figures.py
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm
import os

# --- JFM style ---
plt.rcParams.update({
    'font.family': 'serif',
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 11,
    'legend.fontsize': 9,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'lines.linewidth': 1.2,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
    'text.usetex': False,  # set True if LaTeX available
})

OUTDIR = 'figures'
os.makedirs(OUTDIR, exist_ok=True)


# =========================================================================
#  Fig. 1: Baseline global budget
# =========================================================================
def fig1_baseline():
    d = np.load('data/fig1_baseline.npz')
    t = d['times']; Om = d['Omegas']; P = d['Ps']; D = d['Ds']; R = d['Rs']

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(5.5, 5.5),
                                    sharex=True, gridspec_kw={'hspace': 0.08})

    # upper: Omega, P, D
    ax1.plot(t, Om, 'k-', label=r'$\Omega(t)$')
    ax1.plot(t, P,  'r-', label=r'$P(t)$')
    ax1.plot(t, D,  'b-', label=r'$D(t)$')
    ax1.set_ylabel(r'Enstrophy budget terms')
    ax1.legend(loc='upper right', frameon=False)
    ax1.set_xlim(0, t[-1])
    ax1.text(0.02, 0.92, '(a)', transform=ax1.transAxes, fontweight='bold')

    # lower: R(t)
    ax2.plot(t, R, 'k-')
    ax2.axhline(1.0, color='grey', ls='--', lw=0.8)
    ax2.set_xlabel(r'$t$')
    ax2.set_ylabel(r'$R(t) = P/D$')
    ax2.set_xlim(0, t[-1])

    # mark peaks
    i_R = R.argmax()
    i_Om = Om.argmax()
    ax2.plot(t[i_R], R[i_R], 'ro', ms=5, zorder=5)
    ax2.annotate(f'$R_{{\\max}}={R[i_R]:.2f}$\n$t={t[i_R]:.2f}$',
                 xy=(t[i_R], R[i_R]), xytext=(t[i_R]+0.5, R[i_R]-0.5),
                 fontsize=8, arrowprops=dict(arrowstyle='->', color='r'))
    ax1.axvline(t[i_Om], color='grey', ls=':', lw=0.6, alpha=0.5)
    ax2.axvline(t[i_R],  color='grey', ls=':', lw=0.6, alpha=0.5)
    ax2.text(0.02, 0.92, '(b)', transform=ax2.transAxes, fontweight='bold')

    fig.savefig(f'{OUTDIR}/fig1_baseline_budget.pdf')
    plt.close(fig)
    print("  Fig.1 saved.")


# =========================================================================
#  Fig. 2: Viscosity dependence
# =========================================================================
def fig2_viscosity():
    d = np.load('data/fig2_viscosity.npz')

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(5.5, 5.5),
                                    sharex=True, gridspec_kw={'hspace': 0.08})

    styles = {
        'nu0.02_T4.0':  ('C0', '-',  r'$\nu=0.02$'),
        'nu0.01_T4.0':  ('C1', '-',  r'$\nu=0.01$'),
        'nu0.005_T4.0': ('C2', '-',  r'$\nu=0.005$'),
        'nu0.005_T6.0': ('C2', '--', r'$\nu=0.005$ (ext.)'),
    }

    for key, (color, ls, label) in styles.items():
        t = d[f'{key}_times']
        R = d[f'{key}_Rs']
        Om = d[f'{key}_Omegas']
        ax1.plot(t, R, color=color, ls=ls, label=label)
        ax2.plot(t, Om, color=color, ls=ls, label=label)

    ax1.axhline(1.0, color='grey', ls='--', lw=0.8)
    ax1.set_ylabel(r'$R(t) = P/D$')
    ax1.legend(loc='upper right', frameon=False)
    ax1.set_xlim(0, 6)
    ax1.text(0.02, 0.92, '(a)', transform=ax1.transAxes, fontweight='bold')

    ax2.set_xlabel(r'$t$')
    ax2.set_ylabel(r'$\Omega(t)$')
    ax2.legend(loc='upper right', frameon=False)
    ax2.set_xlim(0, 6)
    ax2.text(0.02, 0.92, '(b)', transform=ax2.transAxes, fontweight='bold')

    fig.savefig(f'{OUTDIR}/fig2_viscosity.pdf')
    plt.close(fig)
    print("  Fig.2 saved.")


# =========================================================================
#  Fig. 3: Shell-resolved R(k,t) baseline
# =========================================================================
def fig3_shell_baseline():
    d = np.load('data/fig3_shell_baseline.npz')
    t = d['times']; ks = d['k_shells']; Rk = d['shell_Rk']

    # trim to useful range
    k_max_plot = 45
    k_mask = ks <= k_max_plot
    Rk_plot = Rk[:, k_mask]
    ks_plot = ks[k_mask]

    fig, ax = plt.subplots(figsize=(6, 4))

    # heatmap with diverging colormap centered at R=1
    norm = TwoSlopeNorm(vmin=0, vcenter=1.0, vmax=min(Rk_plot.max(), 8.0))
    im = ax.pcolormesh(t, ks_plot, Rk_plot.T,
                       cmap='RdBu_r', norm=norm, shading='auto', rasterized=True)

    # R=1 contour
    try:
        ax.contour(t, ks_plot, Rk_plot.T, levels=[1.0],
                   colors='k', linewidths=1.0)
    except:
        pass

    # cascade front k_f(t)
    kf = []
    for i in range(len(t)):
        above = np.where((Rk[i, k_mask] > 1.0) & (ks_plot > 0))[0]
        kf.append(ks_plot[above[-1]] if len(above) > 0 else 0)
    kf = np.array(kf)
    valid = kf > 0
    ax.plot(t[valid], kf[valid], 'w--', lw=1.5, label=r'$k_f(t)$')

    ax.set_xlabel(r'$t$')
    ax.set_ylabel(r'$k$')
    ax.set_xlim(0, t[-1])
    ax.set_ylim(0, k_max_plot)
    ax.legend(loc='upper right', frameon=False,
              labelcolor='white')

    cb = fig.colorbar(im, ax=ax, label=r'$R(k,t)$', shrink=0.9)

    fig.savefig(f'{OUTDIR}/fig3_shell_baseline.pdf')
    plt.close(fig)
    print("  Fig.3 saved.")


# =========================================================================
#  Fig. 4: Shell-resolved R(k,t) low-viscosity long-time
# =========================================================================
def fig4_shell_lowvis():
    d = np.load('data/fig4_shell_lowvis.npz')
    t = d['times']; ks = d['k_shells']; Rk = d['shell_Rk']
    Rs_global = d['Rs']

    k_max_plot = 45
    k_mask = ks <= k_max_plot
    Rk_plot = Rk[:, k_mask]
    ks_plot = ks[k_mask]

    fig, (ax_main, ax_R) = plt.subplots(
        2, 1, figsize=(6, 5.5), sharex=True,
        gridspec_kw={'height_ratios': [3, 1], 'hspace': 0.08})

    # heatmap
    norm = TwoSlopeNorm(vmin=0, vcenter=1.0, vmax=min(Rk_plot.max(), 15.0))
    im = ax_main.pcolormesh(t, ks_plot, Rk_plot.T,
                            cmap='RdBu_r', norm=norm, shading='auto',
                            rasterized=True)

    try:
        ax_main.contour(t, ks_plot, Rk_plot.T, levels=[1.0],
                        colors='k', linewidths=1.0)
    except:
        pass

    # cascade front
    kf = []
    for i in range(len(t)):
        above = np.where((Rk[i, k_mask] > 1.0) & (ks_plot > 0))[0]
        kf.append(ks_plot[above[-1]] if len(above) > 0 else 0)
    kf = np.array(kf)
    valid = kf > 0
    ax_main.plot(t[valid], kf[valid], 'w--', lw=1.5, label=r'$k_f(t)$')

    ax_main.set_ylabel(r'$k$')
    ax_main.set_ylim(0, k_max_plot)
    ax_main.legend(loc='upper right', frameon=False, labelcolor='white')
    ax_main.text(0.02, 0.92, '(a)', transform=ax_main.transAxes,
                 fontweight='bold', color='white')

    cb = fig.colorbar(im, ax=ax_main, label=r'$R(k,t)$', shrink=0.9)

    # lower panel: global R(t)
    ax_R.plot(t, Rs_global, 'k-')
    ax_R.axhline(1.0, color='grey', ls='--', lw=0.8)
    ax_R.set_xlabel(r'$t$')
    ax_R.set_ylabel(r'$R(t)$')
    ax_R.set_xlim(0, t[-1])
    ax_R.text(0.02, 0.85, '(b)', transform=ax_R.transAxes, fontweight='bold')

    fig.savefig(f'{OUTDIR}/fig4_shell_lowvis.pdf')
    plt.close(fig)
    print("  Fig.4 saved.")


# =========================================================================
#  Fig. 5: Matched-energy TG vs perturbed TG
# =========================================================================
def fig5_matched_energy():
    d = np.load('data/fig5_matched_energy.npz')

    fig, axes = plt.subplots(1, 3, figsize=(12, 3.5))
    ax_ek, ax_R, ax_bar = axes

    # (a) Initial energy spectrum
    ks = d['k_shells']
    k_plot = ks[1:60]
    ax_ek.semilogy(k_plot, d['pure_Ek'][1:60], 'k-', label='Pure TG')
    ax_ek.semilogy(k_plot, d['pert_Ek'][1:60], 'r-', label='Perturbed TG')
    ax_ek.set_xlabel(r'$k$')
    ax_ek.set_ylabel(r'$E(k)$')
    ax_ek.legend(frameon=False)
    ax_ek.set_xlim(0, 60)
    ax_ek.text(0.05, 0.92, '(a)', transform=ax_ek.transAxes, fontweight='bold')

    # (b) R(t) comparison
    ax_R.plot(d['pure_times'], d['pure_Rs'], 'k-', label='Pure TG')
    ax_R.plot(d['pert_times'], d['pert_Rs'], 'r-', label='Perturbed TG')
    ax_R.axhline(1.0, color='grey', ls='--', lw=0.8)
    ax_R.set_xlabel(r'$t$')
    ax_R.set_ylabel(r'$R(t)$')
    ax_R.legend(frameon=False)
    ax_R.text(0.05, 0.92, '(b)', transform=ax_R.transAxes, fontweight='bold')

    # (c) D0 and R_max bar comparison
    labels = ['Pure TG', 'Pert. TG']
    D0_vals = [float(d['pure_D0']), float(d['pert_D0'])]
    Rmax_vals = [d['pure_Rs'].max(), d['pert_Rs'].max()]

    x = np.arange(2)
    w = 0.35
    bars1 = ax_bar.bar(x - w/2, D0_vals, w, label=r'$D_0$', color='steelblue')
    ax_bar.set_ylabel(r'$D_0$', color='steelblue')
    ax_bar.set_xticks(x)
    ax_bar.set_xticklabels(labels)

    ax_bar2 = ax_bar.twinx()
    bars2 = ax_bar2.bar(x + w/2, Rmax_vals, w, label=r'$R_{\max}$', color='firebrick')
    ax_bar2.set_ylabel(r'$R_{\max}$', color='firebrick')

    ax_bar.text(0.05, 0.92, '(c)', transform=ax_bar.transAxes, fontweight='bold')

    fig.tight_layout()
    fig.savefig(f'{OUTDIR}/fig5_matched_energy.pdf')
    plt.close(fig)
    print("  Fig.5 saved.")


# =========================================================================
#  Fig. 6: TG vs ABC geometry effect
# =========================================================================
def fig6_abc():
    d = np.load('data/fig6_abc.npz')

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9, 3.5))

    # (a) R(t)
    ax1.plot(d['tg_times'],  d['tg_Rs'],  'k-',  label='Taylor--Green')
    ax1.plot(d['abc_times'], d['abc_Rs'], 'b-', label='ABC/Beltrami')
    ax1.axhline(1.0, color='grey', ls='--', lw=0.8)
    ax1.set_xlabel(r'$t$')
    ax1.set_ylabel(r'$R(t) = P/D$')
    ax1.legend(frameon=False)
    ax1.text(0.05, 0.92, '(a)', transform=ax1.transAxes, fontweight='bold')

    # (b) Omega(t)
    ax2.plot(d['tg_times'],  d['tg_Omegas'],  'k-',  label='Taylor--Green')
    ax2.plot(d['abc_times'], d['abc_Omegas'], 'b-', label='ABC/Beltrami')
    ax2.set_xlabel(r'$t$')
    ax2.set_ylabel(r'$\Omega(t)$')
    ax2.legend(frameon=False)
    ax2.text(0.05, 0.92, '(b)', transform=ax2.transAxes, fontweight='bold')

    fig.tight_layout()
    fig.savefig(f'{OUTDIR}/fig6_abc_geometry.pdf')
    plt.close(fig)
    print("  Fig.6 saved.")


# =========================================================================
#  Main
# =========================================================================
if __name__ == '__main__':
    print("=" * 60)
    print("  Generating all figures for JFM submission")
    print("=" * 60)

    fig1_baseline()
    fig2_viscosity()
    fig3_shell_baseline()
    fig4_shell_lowvis()
    fig5_matched_energy()
    fig6_abc()

    print("\n  All 6 figures saved to figures/")
    print("  Format: vector PDF (JFM recommended)")
