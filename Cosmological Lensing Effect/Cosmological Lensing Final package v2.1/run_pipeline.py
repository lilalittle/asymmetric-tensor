import os
import sys
import subprocess

# 1. Lock the working directory to the folder containing this script
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
os.chdir(BASE_DIR)

# Ensure 'code' directory is in path
sys.path.append(os.path.join(BASE_DIR, 'code'))

# 2. Ensure output directories exist before sub-scripts try to save to them
os.makedirs(os.path.join(BASE_DIR, 'produced'), exist_ok=True)
os.makedirs(os.path.join(BASE_DIR, 'plots'), exist_ok=True)

def run_step(script_name, description):
    print('')
    print('=' * 60)
    print(f'STEP: {description}')
    print(f'RUNNING: {script_name}')
    print('=' * 60)

    # Check locations: Try root first, then 'code' subdirectory
    if os.path.exists(script_name):
        script_path = script_name
    elif os.path.exists(os.path.join('code', script_name)):
        script_path = os.path.join('code', script_name)
    else:
        print(f'ERROR: Could not find {script_name} in {BASE_DIR} or code/ directory.')
        input('\nPress Enter to exit...')
        sys.exit(1)
    
    try:
        subprocess.run([sys.executable, script_path], check=True, cwd=BASE_DIR)
        print(f'SUCCESS: {script_name} completed.')
    except subprocess.CalledProcessError:
        print(f'ERROR: Failed to run {script_name}')
        input('\nPress Enter to exit...')
        sys.exit(1)

if __name__ == '__main__':
    print('--- REFRACTIVE COSMOLOGY PIPELINE (v2.1) ---')

    # 1. Data Generation & Rectification
    run_step('generate_clean_v0_data.py', 'Data Generation: Rectification & K-Convergence')

    # 2. Primary Results Plotting
    run_step('plot_results.py', 'Plotting: Velocity Potential & Saturation')

    # 3. Statistical Robustness
    run_step('run_refractive_analysis.py', 'Analysis: Statistical Robustness Check')

    # 4. Time Dilation
    run_step('calc_time_dilation.py', 'Physics: Time Dilation & Horizon Topology')

    # 5. The Bridge Plot
    run_step('hubble_residuals.py', 'Plotting: Origin of the Dark Energy Signal')

    print('')
    print('=' * 60)
    print('--- PIPELINE COMPLETE ---')
    print("Data artifacts: produced/")
    print("Figure artifacts: plots/")
    print('=' * 60)
    input('\nPress Enter to close this window...')
