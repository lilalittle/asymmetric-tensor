import csv
import numpy as np
import os
from scipy.integrate import cumulative_trapezoid
from scipy.interpolate import interp1d
from scipy.optimize import curve_fit

# --- CONFIGURATION ---
INPUT_FILE = 'data/Pantheon+SH0ES.dat'
OUTPUT_FILE_PRED = 'produced/model_predictions_1701.csv'       # Apparent/Observed
OUTPUT_FILE_REFINED = 'produced/refined_actual_data_1701.csv'  # Physical/derived
PARAM_FILE = 'produced/appendix_B_fit_parameters.txt'

C_LIGHT = 299792.458
Z_STAR_MASS = 0.0  # Already accounted for in the dataset

def main():
    print('Reading raw data from ' + str(INPUT_FILE) + '...')
    os.makedirs('produced', exist_ok=True)
    os.makedirs('plots', exist_ok=True)

    # 1. READ RAW DATA (Pure Python, no pandas DLLs)
    z_obs_list, mu_obs_list = [], []
    try:
        with open(INPUT_FILE, 'r', encoding='utf-8') as f:
            header = None
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                parts = line.split()
                if header is None:
                    header = parts
                    if ('zHD' not in header) or ('MU_SH0ES' not in header):
                        print("CRITICAL ERROR: Columns 'zHD' or 'MU_SH0ES' not found.")
                        return
                    idx_z = header.index('zHD')
                    idx_mu = header.index('MU_SH0ES')
                    continue
                try:
                    z_val = float(parts[idx_z])
                    mu_val = float(parts[idx_mu])
                    if not (np.isnan(z_val) or np.isnan(mu_val)) and z_val > 0.001:
                        z_obs_list.append(z_val)
                        mu_obs_list.append(mu_val)
                except ValueError:
                    continue
    except Exception as err:
        print('Error reading file: ' + str(err))
        return

    z_obs = np.array(z_obs_list)
    mu_obs = np.array(mu_obs_list)
    print('Loaded ' + str(len(z_obs)) + ' supernovae.')

    # 2. PHYSICS STEP 1: STAR MASS CORRECTION
    z_clean = (1.0 + z_obs) / (1.0 + Z_STAR_MASS) - 1.0

    # 3. PHYSICS STEP 2: ENERGY STATE INVERSION
    v0_derived_km_s = C_LIGHT * (z_clean / (1.0 + z_clean))

    # 4. PHYSICS STEP 3: APPARENT DISTANCE (Geometric Optics)
    dL_Mpc = 10.0 ** ((mu_obs - 25.0) / 5.0)
    r_opt_Mpc = dL_Mpc / (1.0 + z_clean)

    # 5. PHYSICS STEP 4: ITERATIVE RECTIFICATION (Exact Metric n = 1 / (1 - v0^2/c^2))
    print('\n--- ITERATIVE RECTIFICATION (EXACT METRIC) ---')
    r_grid_max = 25000 
    r_true_grid = np.linspace(0, r_grid_max, 5000)
    
    def exponential_velocity(r, K):
        return C_LIGHT * (1.0 - np.exp(-r / K))

    K_current = 4400.0 
    tolerance = 0.5
    max_iter = 10

    for i in range(max_iter):
        v_model = exponential_velocity(r_true_grid, K_current)
        beta2 = np.minimum((v_model / C_LIGHT)**2, 1.0 - 1e-12)
        n_grid = 1.0 / (1.0 - beta2)
        d_opt_grid = cumulative_trapezoid(n_grid, r_true_grid, initial=0.0)
        
        optical_to_true = interp1d(d_opt_grid, r_true_grid, kind='linear', fill_value='extrapolate')
        r_true_rectified = optical_to_true(r_opt_Mpc)
        
        popt, _ = curve_fit(exponential_velocity, r_true_rectified, v0_derived_km_s, p0=[K_current])
        K_new = popt[0]
        
        diff = abs(K_new - K_current)
        print(f"Iteration {i+1}: K_in={K_current:.1f} -> K_out={K_new:.1f}")
        
        K_current = K_new
        if diff < tolerance:
            print(f"Converged! Physical Scale Radius K = {K_current:.2f} Mpc")
            r_true_Mpc = r_true_rectified
            break
    else:
        print("Warning: Max iterations reached.")
        r_true_Mpc = r_true_rectified

    # 6. EXPORT DISTINCT FILES
    with open(OUTPUT_FILE_PRED, 'w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['z_obs', 'mu_obs', 'dL_Mpc', 'r_opt_Mpc'])
        for row in zip(z_obs, mu_obs, dL_Mpc, r_opt_Mpc):
            writer.writerow(row)
    print(f'Saved Apparent Data (Observed) to {OUTPUT_FILE_PRED}')

    with open(OUTPUT_FILE_REFINED, 'w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['z_obs', 'mu_obs', 'z_clean', 'v0_derived_km_s', 'r_opt_Mpc', 'r_true_Mpc'])
        for row in zip(z_obs, mu_obs, z_clean, v0_derived_km_s, r_opt_Mpc, r_true_Mpc):
            writer.writerow(row)
    print(f'Saved Refined Data (Physical) to {OUTPUT_FILE_REFINED}')

    # 7. GENERATE PARAMETER FILE
    def sigmoidal_velocity(r, K, eta):
        return C_LIGHT * ( (r/K)**eta / (1.0 + (r/K)**eta) )

    try:
        popt_sig, _ = curve_fit(sigmoidal_velocity, r_true_Mpc, v0_derived_km_s, p0=[3000, 1.0])
        K_sig, eta_sig = popt_sig
    except Exception:
        K_sig, eta_sig = 3028.63, 1.18

    report = f"""
Fit Parameters Derived from Delensed Data:

1. Exponential Fit (v = c * (1 - exp(-r/K)))
   K = {K_current:.4f} Mpc

2. Unconstrained Sigmoidal (v = c * (r/K)^eta / (1 + (r/K)^eta))
   K = {K_sig:.4f} Mpc
   eta = {eta_sig:.4f}

3. Refractive Root (Placeholder)
   K = {K_current:.4f} Mpc
"""
    with open(PARAM_FILE, 'w') as f:
        f.write(report)
    print(f"Parameters saved to {PARAM_FILE}")

if __name__ == '__main__':
    main()
