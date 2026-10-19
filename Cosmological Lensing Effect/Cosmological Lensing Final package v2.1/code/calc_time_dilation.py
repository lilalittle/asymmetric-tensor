import numpy as np
from scipy.integrate import quad
import os
import re

# --- CONSTANTS ---
C_LIGHT = 299792.458
MPC_TO_KM = 3.08567758e19
SEC_TO_GYR = 1.0 / (365.25 * 24 * 3600 * 1e9)
SEC_TO_MYR = 1.0 / (365.25 * 24 * 3600 * 1e6)

PARAM_FILE = 'produced/appendix_B_fit_parameters.txt'
Z_START = 20.0
Z_END = 14.0
CONV_MULTS = [10.0, 100.0, 1000.0]

def load_fitted_params():
    k_exp, k_sig, eta_sig = 4200.3645, 3028.6277, 1.1775
    if os.path.exists(PARAM_FILE):
        with open(PARAM_FILE, 'r') as f:
            content = f.read()
            m_exp = re.search(r"Exponential.*?K = ([\d\.]+)", content, re.S)
            if m_exp:
                k_exp = float(m_exp.group(1))
            m_hill = re.search(r"Sigmoidal.*?K = ([\d\.]+).*?eta = ([\d\.]+)", content, re.S)
            if m_hill:
                k_sig = float(m_hill.group(1))
                eta_sig = float(m_hill.group(2))
    return k_exp, k_sig, eta_sig

K_EXP, K_SIG, ETA_SIG = load_fitted_params()

def v0_exp(r_mpc):
    return C_LIGHT * (1.0 - np.exp(-r_mpc / K_EXP))

def v0_sigmoid(r_mpc):
    term = (r_mpc / K_SIG) ** ETA_SIG
    return C_LIGHT * (term / (1.0 + term))

def n_from_v(v):
    # Exact metric refractive index n(r) = 1 / (1 - (v0/c)^2)
    beta2 = np.minimum((v / C_LIGHT)**2, 1.0 - 1e-12)
    return 1.0 / (1.0 - beta2)

def r_from_z(z, key):
    if key == 'exp':
        return K_EXP * np.log(1.0 + z)
    elif key == 'sigmoid':
        return K_SIG * (z ** (1.0 / ETA_SIG))
    return 0.0

def integrand_proper_time(r, key):
    # Compound relativistic time-dilation factor d(tau)/dt_0 = 1 - v0(r)/c (Eq. 22)
    if key == 'exp':
        return np.exp(-r / K_EXP) / C_LIGHT
    else:
        return 1.0 / (C_LIGHT * (1.0 + (r / K_SIG) ** ETA_SIG))

def integrand_optical_path(r, v_func):
    v = v_func(r)
    return n_from_v(v)

def integrate_quad_time(func, r0, r1):
    if np.isinf(r1) and r0 > 0:
        # Substitution r = r0 / u^4 regularizes algebraic tails at infinity without quad warnings
        res, _ = quad(lambda u: func(r0 / (u**4)) * (4.0 * r0 / (u**5)), 0.0, 1.0, epsabs=1e-8, epsrel=1e-6)
    else:
        res, _ = quad(func, r0, r1, epsabs=1e-8, epsrel=1e-6)
    return res * MPC_TO_KM

def main():
    os.makedirs('produced', exist_ok=True)
    out_file = 'produced/appendix_D_time_dilation.txt'
    
    report = []
    def log(s):
        print(s)
        report.append(s)

    log('--- REFRACTIVE COSMOLOGY TIME DILATION (Appendix D) ---')
    log(f'Parameters Loaded: K_EXP={K_EXP:.2f} Mpc, K_SIG={K_SIG:.2f} Mpc, ETA_SIG={ETA_SIG:.4f}')
    
    models = [('Exponential', 'exp', v0_exp), ('Sigmoidal (Hill)', 'sigmoid', v0_sigmoid)]

    for name, key, func in models:
        r_start = r_from_z(Z_START, key)
        r_end = r_from_z(Z_END, key)
        
        sec_window = integrate_quad_time(lambda r: integrand_proper_time(r, key), r_end, r_start)
        myr_window = sec_window * SEC_TO_MYR
        
        sec_age_z14 = integrate_quad_time(lambda r: integrand_proper_time(r, key), r_end, np.inf)
        myr_age_z14 = sec_age_z14 * SEC_TO_MYR

        sec_age_z20 = integrate_quad_time(lambda r: integrand_proper_time(r, key), r_start, np.inf)
        myr_age_z20 = sec_age_z20 * SEC_TO_MYR

        sec_lookback_z14 = integrate_quad_time(lambda r: integrand_proper_time(r, key), 0.0, r_end)
        gyr_lookback_z14 = sec_lookback_z14 * SEC_TO_GYR
        gyr_total_age = gyr_lookback_z14 + (sec_age_z14 * SEC_TO_GYR)

        r_opt_z14, _ = quad(lambda r: integrand_optical_path(r, func), 0.0, r_end, epsabs=1e-8, epsrel=1e-6)
        
        log(f'\n[Model: {name}]')
        log(f' r_true(z=20): {r_start:.1f} Mpc')
        log(f' r_true(z=14): {r_end:.1f} Mpc | Optical Path r_opt(z=14): {r_opt_z14:.1f} Mpc')
        log(f' Chronological Lookback Time to z=14: {gyr_lookback_z14:.2f} Gyr (Sum Rule tau_0 = {gyr_total_age:.2f} Gyr)')
        log(f' Proper Metric Age at z=20: {myr_age_z20:.1f} Myr')
        log(f' Proper Metric Age at z=14: {myr_age_z14:.1f} Myr')
        log(f' Proper evolutionary window z=20 -> 14: {myr_window:.1f} Myr')
        
        for mult in CONV_MULTS:
            r_far = r_end + mult * (K_EXP if key == 'exp' else K_SIG)
            sec_tail = integrate_quad_time(lambda r: integrand_proper_time(r, key), r_end, r_far)
            gyr_tail = sec_tail * SEC_TO_GYR
            log(f'  Cumulative Proper Age to +{int(mult)}K: {gyr_tail:.4f} Gyr')

    with open(out_file, 'w') as f:
        f.write('\n'.join(report))
    print(f"\nReport saved to {out_file}")

if __name__ == '__main__':
    main()
