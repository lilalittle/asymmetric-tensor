# Refractive Cosmology Reproduction Package (v2.0 - Final Manuscript)

This package contains the source code and data required to reproduce the results presented in the manuscript **The Cosmological Lensing Effect**. It includes the full analytic pipeline, from the raw data rectification to the statistical robustness verification.

## Directory Structure
- `data/` contains the raw Pantheon+ dataset `Pantheon+SH0ES.dat`
- `code/` source code for the analysis pipeline
- `produced/` stores reconstructed velocity potential CSV outputs
- `plots/` stores generated figures (Figures 1, 2, and Appendix figures)

## Reproducibility Guide

| Manuscript Section | Source Code Script | Description |
| :--- | :--- | :--- |
| **Data Pipeline** | `generate_clean_v0_data.py` | **Core Physics Engine**: Performs star mass correction, analytic inversion, and the iterative de-lensing loop to derive the physical coordinates $(r_{true}, v_0)$. |
| **Figure 1** | `plot_results.py` | **Velocity Fit**: Generates the Velocity Potential plot (Figure 1) and fits the Exponential saturation curve with the $H_0=73$ reference line. |
| **Appendix C** | `run_refractive_analysis.py` | **Robustness**: Performs the Forward vs. Inverse statistical check to confirm the stability of the potential ($K \approx 4224$). |
| **Appendix D** | `calc_time_dilation.py` | **Time Dilation**: Calculates the proper time window for high-z galaxy formation ($z=20 \to 14$). |
| **Appendix E** | `hubble_residuals.py` | **Bridge Plot**: Generates the residuals plot showing the resolution of the "Dark Energy" signal via refractive correction. |
| **Orchestrator** | `run_pipeline.py` | **Master Driver**: Runs all scripts in the correct sequence to generate the full manuscript artifact set. |

## Pipeline Manifest

### 1. `code/generate_clean_v0_data.py`
**Iterative Rectification Pipeline**
* **Input:** `data/Pantheon+SH0ES.dat`
* **Operation:** 1. Applies Stellar Mass Correction ($z_{star} \approx 0.0003$).
  2. Performs point-by-point analytic inversion to $v_0$.
  3. Iteratively solves the optical path integral ($r_{opt} = \int n dr$) to recover physical distances $r_{true}$.
* **Output:** `refined_actual_data_1701.csv` (The clean physical dataset).

### 2. `code/plot_results.py`
**Velocity Potential Fit (Figure 1)**
* **Input:** `refined_actual_data_1701.csv`
* **Operation:** Fits the Exponential Saturation model to the de-lensed data and plots the result against the local Hubble expansion line ($H_0 = 73$).
* **Output:** `velocity_potential_fit.png`.

### 3. `code/run_refractive_analysis.py`
**Statistical Robustness Check**
* **Input:** Raw Pantheon+ Data + `refined_actual_data_1701.csv`.
* **Operation:** Compares the parameters derived from the **Inverse Method** (rectification) against a blind **Forward Method** (minimizing $\chi^2$ in magnitude space).
* **Result:** Confirms convergence to $<0.8\%$ agreement. Generates `robustness_comparison_final.png`.

### 4. `code/calc_time_dilation.py`
**Relativistic Integration**
* **Input:** Converged Exponential Parameter ($K \approx 4224$ Mpc).
* **Operation:** Numerically integrates the proper time element $d\tau = n(r) dr / (c \gamma)$ along the lookback path.
* **Result:** Outputs the "Impossible Galaxy" evolutionary window ($z=20 \to 14$) proving the existence of $>6$ Gyr of proper time.

### 5. `code/hubble_residuals.py`
**Signal Resolution**
* **Input:** `refined_actual_data_1701.csv`.
* **Operation:** Calculates the theoretical refractive anomaly $\Delta \mu = 5 \log(r_{opt}/r_{true})$ and subtracts it from the observed Hubble residuals.
* **Result:** Generates `hubble_residuals_bridge.png`, demonstrating that the "Dark Energy" signal vanishes.

## Key Parameters (v2.0)

| Parameter | Exponential Fit (Preferred) | Sigmoidal (Hill) Fit |
| :--- | :--- | :--- |
| **Scale Radius ($K$)** | **~4224 Mpc** | ~3232 Mpc |
| **Shape Parameter ($\eta$)** | **1.0 (Fixed)** | ~1.12 |
| **$H_{local}$ Prediction** | $c/K \approx \mathbf{71.0}$ | $c/K \approx 92.8$ |

## How to Run

1. **Install dependencies**
```bash
pip install -r requirements.txt

2. **Run the full pipeline**
python run_pipeline.py