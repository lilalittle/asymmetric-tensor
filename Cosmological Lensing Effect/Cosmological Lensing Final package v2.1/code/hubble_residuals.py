import csv
import numpy as np
import matplotlib.pyplot as plt
import os
import re

# --- CONFIGURATION ---
INPUT_FILE = 'produced/refined_actual_data_1701.csv'
PARAM_FILE = 'produced/appendix_B_fit_parameters.txt'
OUTPUT_PLOT = 'plots/hubble_residuals_bridge.png'
C_LIGHT = 299792.458

def load_k_exp(default_k=4200.36):
    if os.path.exists(PARAM_FILE):
        with open(PARAM_FILE, 'r') as f:
            content = f.read()
            m_exp = re.search(r"Exponential.*?K = ([\d\.]+)", content, re.S)
            if m_exp:
                return float(m_exp.group(1))
    return default_k

def get_mu_refractive_exact(z_vals, K):
    # Exact analytic integral of n(r) = 1 / (1 - v0(r)^2 / c^2)
    z_safe = np.maximum(z_vals, 1e-9)
    r_opt_vals = K * (0.5 * z_safe + 0.25 * np.log(2.0 * z_safe + 1.0))
    dL_vals = r_opt_vals * (1.0 + z_safe)
    return 5.0 * np.log10(dL_vals) + 25.0

def main():
    print("Generating Bridge Plot...")
    if not os.path.exists(INPUT_FILE):
        print(f"Error: {INPUT_FILE} not found. Run data generation first.")
        return

    z_list, mu_list = [], []
    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            z_val = float(row['z_clean'])
            if z_val > 0.001:
                z_list.append(z_val)
                mu_list.append(float(row['mu_obs']))

    z_data = np.array(z_list)
    mu_data = np.array(mu_list)

    K_EXP = load_k_exp()
    print(f"Loaded converged K_EXP = {K_EXP:.2f} Mpc from pipeline.")

    H0_REF = C_LIGHT / K_EXP
    mu_linear = 5.0 * np.log10(C_LIGHT * z_data / H0_REF) + 25.0
    
    signal_data = mu_data - mu_linear

    z_smooth = np.logspace(np.log10(0.001), np.log10(np.max(z_data)), 200)
    mu_linear_smooth = 5.0 * np.log10(C_LIGHT * z_smooth / H0_REF) + 25.0
    mu_refractive_smooth = get_mu_refractive_exact(z_smooth, K_EXP)
    signal_theory = mu_refractive_smooth - mu_linear_smooth

    mu_refractive_data = get_mu_refractive_exact(z_data, K_EXP)
    residuals_corrected = mu_data - mu_refractive_data

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 10), sharex=True)
    plt.subplots_adjust(hspace=0.05)
    
    ax1.scatter(z_data, signal_data, s=15, color='gray', alpha=0.3, label='Standard Residuals')
    ax1.plot(z_smooth, signal_theory, color='blue', linewidth=3, label=f'Refractive Prediction (K={K_EXP:.0f} Mpc)')
    ax1.set_ylabel(r'$\mu_{obs} - \mu_{linear}$ (mag)', fontsize=14)
    ax1.legend(loc='upper left')
    ax1.grid(True, alpha=0.3)
    ax1.axhline(0, color='k', lw=1, linestyle=':')

    ax2.scatter(z_data, residuals_corrected, s=15, color='royalblue', alpha=0.3, label='Corrected Residuals')
    ax2.axhline(0, color='k', linewidth=2, linestyle='-')
    ax2.set_xlabel('Redshift $z$', fontsize=14)
    ax2.set_ylabel(r'Residuals (mag)', fontsize=14)
    ax2.set_xscale('log')
    ax2.legend(loc='lower left')
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim(-0.5, 0.5)
    
    os.makedirs('plots', exist_ok=True)
    plt.savefig(OUTPUT_PLOT, dpi=300, bbox_inches='tight')
    print(f"Saved {OUTPUT_PLOT}")

if __name__ == '__main__':
    main()
