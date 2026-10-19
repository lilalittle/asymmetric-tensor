import csv
import numpy as np
import matplotlib.pyplot as plt
import os
from scipy.optimize import curve_fit

# --- CONFIGURATION ---
INPUT_FILE = 'produced/refined_actual_data_1701.csv'
OUTPUT_PLOT = 'plots/velocity_potential_fit.png'
C_LIGHT = 299792.458

def exponential_velocity(r, K):
    return C_LIGHT * (1.0 - np.exp(-r / K))

def main():
    print("Generating Velocity Potential Plot...")
    if not os.path.exists(INPUT_FILE):
        print(f"Error: {INPUT_FILE} not found.")
        return

    r_true_list, v0_list = [], []
    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            r_true_list.append(float(row['r_true_Mpc']))
            v0_list.append(float(row['v0_derived_km_s']))

    r_true_Mpc = np.array(r_true_list)
    v0_derived_km_s = np.array(v0_list)
    
    popt, _ = curve_fit(exponential_velocity, r_true_Mpc, v0_derived_km_s, p0=[4200])
    K_final = popt[0]

    plt.figure(figsize=(10, 7))
    plt.scatter(r_true_Mpc, v0_derived_km_s, s=5, c='black', alpha=0.15, label='Delensed Data')
    
    r_plot = np.linspace(0, r_true_Mpc.max()*1.1, 1000)
    v_exp = exponential_velocity(r_plot, K_final)
    plt.plot(r_plot, v_exp, 'b-', lw=2.5, label=f'Exponential Fit (K={K_final:.0f})')
    
    v_h73 = 73.0 * r_plot
    mask_h73 = v_h73 < C_LIGHT * 1.5
    plt.plot(r_plot[mask_h73], v_h73[mask_h73], color='green', linestyle=':', linewidth=2, label='$H_0 = 73$ km/s/Mpc')
    
    plt.axhline(C_LIGHT, color='gray', linestyle='-', alpha=0.5, label='$c$')
    plt.xlabel('True Coordinate Distance $r_{true}$ (Mpc)')
    plt.ylabel('Escape Velocity $v_0$ (km/s)')
    plt.title('Velocity Potential Fit')
    plt.legend()
    plt.ylim(0, 350000)
    plt.grid(True, alpha=0.3)
    
    os.makedirs('plots', exist_ok=True)
    plt.savefig(OUTPUT_PLOT, dpi=300)
    print(f"Saved {OUTPUT_PLOT}")

if __name__ == '__main__':
    main()
