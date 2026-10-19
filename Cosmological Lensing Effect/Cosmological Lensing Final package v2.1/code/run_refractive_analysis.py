import csv
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from scipy.optimize import minimize
from scipy.integrate import cumulative_trapezoid
from scipy.interpolate import interp1d
import re
import os

# --- CONSTANTS ---
C_KM_S = 299792.458
Z_STAR_MASS = 0.0

# --- 1. LOAD DATA & PARAMS ---
print("Loading data and parameters...")

raw_path = Path('data') / 'Pantheon+SH0ES.dat'
refined_path = Path('produced/refined_actual_data_1701.csv')

if not raw_path.exists():
    print(f"Error: {raw_path} not found.")
    exit(1)
if not refined_path.exists():
    print(f"Error: {refined_path} not found. Run data generation first.")
    exit(1)

z_obs_list, mu_obs_list, mu_err_list = [], [], []
with open(raw_path, 'r', encoding='utf-8') as f:
    header = None
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        if header is None:
            header = parts
            idx_z = header.index('zHD')
            idx_mu = header.index('MU_SH0ES')
            idx_err = header.index('MU_SH0ES_ERR_DIAG') if 'MU_SH0ES_ERR_DIAG' in header else None
            continue
        try:
            z_val = float(parts[idx_z])
            mu_val = float(parts[idx_mu])
            err_val = float(parts[idx_err]) if idx_err is not None else 1.0
            if not (np.isnan(z_val) or np.isnan(mu_val)) and z_val > 0.001:
                z_obs_list.append(z_val)
                mu_obs_list.append(mu_val)
                mu_err_list.append(err_val)
        except ValueError:
            continue

z_obs_raw = np.array(z_obs_list)
z_fit = (1.0 + z_obs_raw) / (1.0 + Z_STAR_MASS) - 1.0
mu_fit = np.array(mu_obs_list)
mu_err_fit = np.array(mu_err_list)
N_fit = len(z_fit)

param_path = Path('produced/appendix_B_fit_parameters.txt')
K_EXP_INV = 4200.36
K_HILL_INV = 3028.63
ETA_HILL_INV = 1.18

if param_path.exists():
    with open(param_path, 'r') as f:
        content = f.read()
        m_exp = re.search(r"Exponential.*?K = ([\d\.]+)", content, re.S)
        if m_exp: K_EXP_INV = float(m_exp.group(1))
        
        m_hill = re.search(r"Sigmoidal.*?K = ([\d\.]+).*?eta = ([\d\.]+)", content, re.S)
        if m_hill: 
            K_HILL_INV = float(m_hill.group(1))
            ETA_HILL_INV = float(m_hill.group(2))

print(f"Inverse Parameters Loaded: Exp K={K_EXP_INV:.2f}, Hill K={K_HILL_INV:.2f}, eta={ETA_HILL_INV:.4f}")

# --- 2. PHYSICS MODELS ---

def get_mu_vectorized(z_vals, v_func, args):
    if len(args) == 1:
        # Exact closed-form integral of n = 1 / (1 - v0^2/c^2) for v_exp
        K = args[0]
        r_opt_vals = K * (0.5 * z_vals + 0.25 * np.log(2.0 * z_vals + 1.0))
    else:
        # Numerical integral of exact n = 1 / (1 - v0^2/c^2) for v_hill(r, K, eta)
        r_max = 20000 
        r_grid = np.linspace(0, r_max, 2000)
        v_grid = v_func(r_grid, *args)
        beta2 = np.minimum((v_grid / C_KM_S)**2, 1.0 - 1e-12)
        n_grid = 1.0 / (1.0 - beta2)
        d_opt_grid = cumulative_trapezoid(n_grid, r_grid, initial=0.0)
        z_grid = (v_grid / C_KM_S) / np.maximum(1.0 - v_grid / C_KM_S, 1e-12)
        d_opt_interp = interp1d(z_grid, d_opt_grid, kind='linear', fill_value='extrapolate')
        r_opt_vals = d_opt_interp(z_vals)
    dL_vals = r_opt_vals * (1.0 + z_vals)
    return 5.0 * np.log10(np.maximum(dL_vals, 1e-9)) + 25.0

def v_exp(r, K):
    return C_KM_S * (1.0 - np.exp(-r/K))

def v_hill(r, K, eta):
    return C_KM_S * ( (r/K)**eta / (1.0 + (r/K)**eta) )

def get_mu_lcdm(z_vals, H0, Om):
    z_grid = np.linspace(0, np.max(z_vals)*1.05, 2000)
    E_inv = 1.0 / np.sqrt(Om * (1.0 + z_grid)**3 + (1.0 - Om))
    dc_grid = (C_KM_S / H0) * cumulative_trapezoid(E_inv, z_grid, initial=0.0)
    dc_interp = interp1d(z_grid, dc_grid, kind='cubic')
    dL_vals = dc_interp(z_vals) * (1.0 + z_vals)
    return 5.0 * np.log10(np.maximum(dL_vals, 1e-9)) + 25.0

# --- 3. FORWARD FITTING & BENCHMARKS ---

def fit_forward(model_type='exp'):
    print(f"Fitting {model_type} forward...")
    def loss(params):
        if model_type == 'exp':
            K = params[0]
            if K < 1000: return 1e9
            pred = get_mu_vectorized(z_fit, v_exp, [K])
        else:
            K, eta = params
            if K < 1000 or eta < 0.1: return 1e9
            pred = get_mu_vectorized(z_fit, v_hill, [K, eta])
        return np.sum( ((mu_fit - pred)/mu_err_fit)**2 )

    if model_type == 'exp':
        res = minimize(loss, [4400.0], method='Nelder-Mead')
    else:
        res = minimize(loss, [3300.0, 1.1], method='Nelder-Mead')
    return res.x, res.fun

params_exp_fwd, chi2_exp_fwd = fit_forward('exp')
K_EXP_FWD = params_exp_fwd[0]
chi2_exp_inv = float(np.sum(((mu_fit - get_mu_vectorized(z_fit, v_exp, [K_EXP_INV]))/mu_err_fit)**2))

params_hill_fwd, chi2_hill_fwd = fit_forward('hill')
K_HILL_FWD, ETA_HILL_FWD = params_hill_fwd

res_lcdm_1p = minimize(lambda p: np.sum(((mu_fit - get_mu_lcdm(z_fit, p[0], 0.315))/mu_err_fit)**2), [73.0], method='Nelder-Mead')
H0_lcdm_1p, chi2_lcdm_1p = res_lcdm_1p.x[0], res_lcdm_1p.fun

res_lcdm_2p = minimize(
    lambda p: np.sum(((mu_fit - get_mu_lcdm(z_fit, p[0], p[1]))/mu_err_fit)**2) if (0.01 < p[1] < 0.99 and 50 < p[0] < 90) else 1e9,
    [73.0, 0.3], method='Nelder-Mead'
)
H0_lcdm_2p, Om_lcdm_2p = res_lcdm_2p.x
chi2_lcdm_2p = res_lcdm_2p.fun

res_lin = minimize(lambda p: np.sum(((mu_fit - (5.0*np.log10(C_KM_S * z_fit / p[0]) + 25.0))/mu_err_fit)**2), [70.0], method='Nelder-Mead')
H0_lin, chi2_lin = res_lin.x[0], res_lin.fun

lnN = np.log(N_fit)
delta_exp_pct = abs(K_EXP_INV - K_EXP_FWD) / K_EXP_INV * 100.0

summary_text = f"""--- APPENDIX C: ROBUSTNESS & CHI-SQUARED COMPARISON (N = {N_fit}) ---
1. Refractive Exponential (Inverse Fit, Exact n, k=1):
   K = {K_EXP_INV:.2f} Mpc (H0 = {C_KM_S/K_EXP_INV:.2f} km/s/Mpc)
   Chi2 = {chi2_exp_inv:.2f} | Chi2/dof = {chi2_exp_inv/(N_fit-1):.4f} | BIC = {chi2_exp_inv + 1*lnN:.2f}

2. Refractive Exponential (Forward Fit, Exact n, k=1):
   K = {K_EXP_FWD:.2f} Mpc (H0 = {C_KM_S/K_EXP_FWD:.2f} km/s/Mpc) | Agreement = {delta_exp_pct:.2f}%
   Chi2 = {chi2_exp_fwd:.2f} | Chi2/dof = {chi2_exp_fwd/(N_fit-1):.4f} | BIC = {chi2_exp_fwd + 1*lnN:.2f}

3. Refractive Sigmoidal (Forward Fit, Exact n, k=2):
   K = {K_HILL_FWD:.2f} Mpc, eta = {ETA_HILL_FWD:.4f}
   Chi2 = {chi2_hill_fwd:.2f} | Chi2/dof = {chi2_hill_fwd/(N_fit-2):.4f} | BIC = {chi2_hill_fwd + 2*lnN:.2f}

4. Flat LambdaCDM (Planck Om=0.315 fixed, k=1):
   H0 = {H0_lcdm_1p:.2f} km/s/Mpc
   Chi2 = {chi2_lcdm_1p:.2f} | Chi2/dof = {chi2_lcdm_1p/(N_fit-1):.4f} | BIC = {chi2_lcdm_1p + 1*lnN:.2f}

5. Flat LambdaCDM (2-Parameter Free, k=2):
   H0 = {H0_lcdm_2p:.2f} km/s/Mpc, Om = {Om_lcdm_2p:.4f}
   Chi2 = {chi2_lcdm_2p:.2f} | Chi2/dof = {chi2_lcdm_2p/(N_fit-2):.4f} | BIC = {chi2_lcdm_2p + 2*lnN:.2f}

6. Un-lensed Linear Hubble Law (k=1):
   H0 = {H0_lin:.2f} km/s/Mpc
   Chi2 = {chi2_lin:.2f} | Chi2/dof = {chi2_lin/(N_fit-1):.4f} | BIC = {chi2_lin + 1*lnN:.2f}
"""

print(summary_text)
os.makedirs('produced', exist_ok=True)
with open('produced/appendix_C_chi2_comparison.txt', 'w') as f:
    f.write(summary_text)
print("Saved chi-squared report to produced/appendix_C_chi2_comparison.txt")

# --- 4. PLOTTING ---
print("Generating Robustness Plot...")
os.makedirs('plots', exist_ok=True)
out_path = Path('plots') / 'robustness_comparison_final.png'

r_cloud_list, v_cloud_list = [], []
with open(refined_path, 'r', encoding='utf-8') as f:
    reader = csv.DictReader(f)
    for row in reader:
        r_cloud_list.append(float(row['r_true_Mpc']))
        v_cloud_list.append(float(row['v0_derived_km_s']))

r_cloud = np.array(r_cloud_list)
v_cloud = np.array(v_cloud_list)

r_line = np.linspace(0, r_cloud.max()*1.1, 1000)
v_exp_inv_line = v_exp(r_line, K_EXP_INV)
v_exp_fwd_line = v_exp(r_line, K_EXP_FWD)
v_hill_inv_line = v_hill(r_line, K_HILL_INV, ETA_HILL_INV)
v_hill_fwd_line = v_hill(r_line, K_HILL_FWD, ETA_HILL_FWD)

fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 12))

# Panel A: Exponential
ax1.scatter(r_cloud, v_cloud, s=10, c='k', alpha=0.1, label='Rectified Data')
ax1.plot(r_line, v_exp_inv_line, 'b-', lw=3, label=f'Inverse Fit (K={K_EXP_INV:.0f})')
ax1.plot(r_line, v_exp_fwd_line, 'c--', lw=3, label=f'Forward Fit (K={K_EXP_FWD:.0f})')
ax1.set_title('Panel A: Exponential Model Robustness')
ax1.set_ylabel('Escape Velocity $v_0$ (km/s)')
ax1.legend()
ax1.grid(alpha=0.3)

# Panel B: Sigmoidal
ax2.scatter(r_cloud, v_cloud, s=10, c='k', alpha=0.1, label='Rectified Data')
ax2.plot(r_line, v_hill_inv_line, 'r-', lw=3, label=rf'Inverse Fit (K={K_HILL_INV:.0f}, $\eta$={ETA_HILL_INV:.2f})')
ax2.plot(r_line, v_hill_fwd_line, 'orange', linestyle='--', lw=3, label=rf'Forward Fit (K={K_HILL_FWD:.0f}, $\eta$={ETA_HILL_FWD:.2f})')
ax2.set_title('Panel B: Sigmoidal (Hill) Model Robustness')
ax2.set_xlabel('True Coordinate Distance (Mpc)')
ax2.set_ylabel('Escape Velocity $v_0$ (km/s)')
ax2.legend()
ax2.grid(alpha=0.3)

plt.tight_layout()
plt.savefig(out_path, dpi=300)
print(f"Saved {out_path}")
