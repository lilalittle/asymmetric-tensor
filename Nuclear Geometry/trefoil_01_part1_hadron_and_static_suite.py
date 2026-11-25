"""
trefoil_01_part1_hadron_and_static_suite.py  [PART I MASTER VERIFICATION SUITE]
===============================================================================
Companion Code (Module 1 of 4) to:
  B. T. Bair-Mosheh, "Continuum Mechanics and Dynamic Geometry of (2,3) Trefoil
  Nucleons" (V3.3 Unified Monograph, Part I: Sections 1--13, November 2026)
  ORCID: 0000-0003-4329-7740 | Reference Anchor: doi:10.5281/zenodo.20466167

Reproduces all Part I single-nucleon and static contact benchmarks (Flake8-clean):
  1. Five Universal Constants Only: HBAR_C, ALPHA, M_P, M_N, M_E (zero empirical
     hadronic length inputs). Derives De=1 horizon r_e = 2.8179 fm, spherical
     Neumann Bessel shells R_1..3 = (0.9437, 1.6225, 2.2901) fm < r_e < R_4, and
     De=3 Hookean pion scale U_Hooke(r_e/3) = 137.150 MeV (r_pi = 1.43877 fm).
  2. Divergence-Conserved Inverse-Cube Relaxed Proton: V_tau(p)/V_tau(n) = M_P/M_N
     and V_rc * V_tau^3 = const => jammed 90-deg n0 (L_n = 8.1083 fm) and relaxed
     109.47-deg p+ (L_p = 8.1195 fm, +13.42% open throat clearance).
  3. 540x540 Regularized Kelvin Elastostatic BEM, 1080-Panel Exterior Laplace BEM,
     Curvature-Binormal Surface Vorticity, Unified Gordon-Sachs Form Factors
     (G_E, G_M, r_E, r_M), and Cottingham Electromagnetic Self-Energy dU_EM.
  4. Part I Static Baseline (g_S, g_M, g_B, c_FB): 21 synchronous two-body contact
     modes, Degree-1 relays, flat-T pure-2N CG baseline (A=2,3,4), exact-contact
     C_2v 4He disphenoid, 8Be..16O alpha blocks, and 55-pair 11Li cluster ledger.
"""
import time
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eig_banded, eigh
from scipy.optimize import brentq, minimize, minimize_scalar
from scipy.special import spherical_jn

_TRAPZ = getattr(np, "trapezoid", getattr(np, "trapz", None))

# ======================================================================
# UNIVERSAL CONSTANTS & DERIVED De=1 / De=3 CONTINUUM SCALES (ZERO FITS)
# ======================================================================
HBAR_C = 197.3269804
ALPHA = 1.0 / 137.035999084
M_P, M_N, M_E = 938.272088, 939.565420, 0.51099895
M_0 = 0.5 * (M_P + M_N)
MU_NP = (M_P * M_N) / (M_P + M_N)
HB2_2M0 = (HBAR_C ** 2) / (2.0 * M_0)
HB2_2MU_NP = (HBAR_C ** 2) / (2.0 * MU_NP)
HB2_2MU_NN = (HBAR_C ** 2) / M_N

R_C0 = HBAR_C / M_0
R_T0 = R_C0 / np.sqrt(3.0)
NU_ELAST = (1.0 - 2.0 * ALPHA) / (2.0 * (1.0 - ALPHA))

# Derived viscoelastic relaxation horizon r_e (De=1) & Hookean rupture (De=3)
R_E = ALPHA * HBAR_C / M_E
KAP_HOOKE = ALPHA * (M_N ** 3) / (HBAR_C ** 2)
U_HOOKE_DE3 = KAP_HOOKE * ((R_E / 3.0) ** 2)
R_PI = HBAR_C / U_HOOKE_DE3
R_2PI = 0.5 * R_PI

R0_U, A_U = 3.0 / 5.0, 2.0 / 5.0
B_U_P, B_U_N = np.sqrt(2.0) / 6.0, np.sqrt(2.0) / 3.0

D111 = np.array([1.0, 1.0, 1.0]) / np.sqrt(3.0)
U0 = np.array([2.0, -1.0, -1.0]) / np.sqrt(6.0)
V0 = np.array([0.0, 1.0, -1.0]) / np.sqrt(2.0)


# ======================================================================
# UNIVERSAL SO(3), 1D ARC-LENGTH, & PAIRWISE STERIC CONTACT HELPERS
# ======================================================================
def rot_x(ang):
    c, s = np.cos(ang), np.sin(ang)
    return np.array([[1.0, 0.0, 0.0], [0.0, c, -s], [0.0, s, c]])


def rot_y(ang):
    c, s = np.cos(ang), np.sin(ang)
    return np.array([[c, 0.0, s], [0.0, 1.0, 0.0], [-s, 0.0, c]])


def rot_z(ang):
    c, s = np.cos(ang), np.sin(ang)
    return np.array([[c, -s, 0.0], [s, c, 0.0], [0.0, 0.0, 1.0]])


def euler_zyz(alpha, beta, gamma):
    """Exact SO(3) parameterization R = R_z(alpha) @ R_y(beta) @ R_z(gamma)."""
    return rot_z(alpha) @ rot_y(beta) @ rot_z(gamma)


def frame_from_z_and_ref(s_hat, ref_e2, gam=0.0):
    """Right-handed SO(3) matrix R = [e2 x e3, e2, e3] @ rot_z(gam)."""
    e3 = s_hat / np.linalg.norm(s_hat)
    e2 = ref_e2 - np.dot(ref_e2, e3) * e3
    if np.linalg.norm(e2) < 1e-9:
        alt = (np.array([1.0, 0.0, 0.0]) if abs(e3[0]) < 0.8
               else np.array([0.0, 1.0, 0.0]))
        e2 = alt - np.dot(alt, e3) * e3
    e2 /= np.linalg.norm(e2)
    e1 = np.cross(e2, e3)
    return np.column_stack([e1, e2, e3]) @ rot_z(gam)


def exact_steric_contact_scale(u_vecs, r_loc_tau, iu, ju, r_sum_pairs):
    """
    Exact closed-form outer contact scale xi_touch where pairwise distance hits
    r_sum_pairs[p] = r_t,i + r_t,j across all (tau, p, s_1, s_2).
    """
    r_cut = np.asarray(r_sum_pairs, dtype=float)
    if r_cut.ndim == 0:
        r_cut = np.full(len(iu), float(r_cut))
    du = u_vecs[iu] - u_vecs[ju]
    a_coef = np.sum(du ** 2, axis=-1)
    w_vec = r_loc_tau[:, iu, :, None, :] - r_loc_tau[:, ju, None, :, :]
    b_coef = np.einsum("pk,tpijk->tpij", du, w_vec)
    c_coef = np.sum(w_vec ** 2, axis=-1) - (r_cut[None, :, None, None] ** 2)
    disc = (b_coef ** 2) - a_coef[None, :, None, None] * c_coef
    mask = disc > 0.0
    if not np.any(mask):
        return 0.0
    xi_p = (-b_coef + np.sqrt(np.maximum(disc, 0.0))) / a_coef[None, :, None, None]
    return float(np.max(np.where(mask, np.maximum(0.0, xi_p), 0.0)))


def build_local_arclength_tube(b_u, l_phys, n_s=96):
    """Canonical spin +z trefoil resampled onto uniform s in [0, l_phys)."""
    n_f = max(3840, 32 * n_s)
    phi = np.linspace(0.0, 2.0 * np.pi, n_f, endpoint=False)
    dphi = 2.0 * np.pi / n_f
    er = np.column_stack([np.sin(2.0 * phi), -np.cos(2.0 * phi), np.zeros(n_f)])
    ep = np.column_stack([np.cos(2.0 * phi), np.sin(2.0 * phi), np.zeros(n_f)])
    ez = np.array([[0.0, 0.0, 1.0]])

    rho = R0_U + A_U * np.cos(3.0 * phi)
    w = b_u * np.sin(3.0 * phi)
    r_u = rho[:, None] * er + w[:, None] * ez
    r1_u = ((-3.0 * A_U * np.sin(3.0 * phi))[:, None] * er
            + (2.0 * rho)[:, None] * ep
            + (3.0 * b_u * np.cos(3.0 * phi))[:, None] * ez)

    js = np.linalg.norm(r1_u, axis=1)
    lam = l_phys / float(np.sum(js * dphi))
    s_cum = np.concatenate([[0.0], np.cumsum(lam * js * dphi)])
    phi_p = np.concatenate([phi, [2.0 * np.pi]])
    r_fm = np.vstack([lam * r_u, lam * r_u[0:1]])
    t_u = r1_u / js[:, None]
    t_p = np.vstack([t_u, t_u[0:1]])

    s_g = np.linspace(0.0, l_phys, n_s, endpoint=False)
    ph_deg = np.rad2deg(np.interp(s_g, s_cum, phi_p))
    r_s = np.column_stack([np.interp(s_g, s_cum, r_fm[:, c]) for c in (0, 1, 2)])
    t_s = np.column_stack([np.interp(s_g, s_cum, t_p[:, c]) for c in (0, 1, 2)])
    t_s /= np.linalg.norm(t_s, axis=1, keepdims=True)
    return s_g, ph_deg, r_s, t_s, lam


def build_trefoil_discrete_z(b_u, l_phys, n_phi=36):
    """Discrete +z trefoil with universal V3.2 lobe phase flux Phi_0 (eta=1)."""
    phi = np.linspace(0.0, 2.0 * np.pi, n_phi, endpoint=False)
    dphi = 2.0 * np.pi / n_phi
    er = np.column_stack([np.sin(2.0 * phi), -np.cos(2.0 * phi), np.zeros(n_phi)])
    ep = np.column_stack([np.cos(2.0 * phi), np.sin(2.0 * phi), np.zeros(n_phi)])
    ez = np.array([[0.0, 0.0, 1.0]])
    rho, w = R0_U + A_U * np.cos(3.0 * phi), b_u * np.sin(3.0 * phi)
    r0 = rho[:, None] * er + w[:, None] * ez
    dr0 = ((-3.0 * A_U * np.sin(3.0 * phi))[:, None] * er
           + (2.0 * rho)[:, None] * ep
           + (3.0 * b_u * np.cos(3.0 * phi))[:, None] * ez)
    ds0 = np.linalg.norm(dr0, axis=1) * dphi
    sc = l_phys / float(np.sum(ds0))
    return sc * r0, sc * dr0 * dphi, sc * ds0


# ======================================================================
# SECTION 1: INVERSE-CUBE RELAXED PROTON, De=3 RUPTURE, & 2-LOBE MESON
# ======================================================================
def trefoil_point_and_tangent_u(phi_scalar, b_u, ell_u):
    rc = np.sin(2.0 * phi_scalar) * U0 - np.cos(2.0 * phi_scalar) * V0
    pc = np.cos(2.0 * phi_scalar) * U0 + np.sin(2.0 * phi_scalar) * V0
    rho = R0_U + A_U * np.cos(3.0 * phi_scalar)
    w = b_u * np.sin(3.0 * phi_scalar)
    r_pt = (rho * rc + w * D111) / ell_u
    r1_pt = ((-3.0 * A_U * np.sin(3.0 * phi_scalar)) * rc
             + (2.0 * rho) * pc
             + (3.0 * b_u * np.cos(3.0 * phi_scalar)) * D111)
    return r_pt, r1_pt / np.linalg.norm(r1_pt)


def build_unit_radius_state(b_u, n_phi=1440):
    phi = np.linspace(0.0, 2.0 * np.pi, n_phi, endpoint=False)
    dphi = 2.0 * np.pi / n_phi
    rc = np.sin(2.0 * phi)[:, None] * U0 - np.cos(2.0 * phi)[:, None] * V0
    pc = np.cos(2.0 * phi)[:, None] * U0 + np.sin(2.0 * phi)[:, None] * V0
    rho, w = R0_U + A_U * np.cos(3.0 * phi), b_u * np.sin(3.0 * phi)
    r = rho[:, None] * rc + w[:, None] * D111

    r1 = ((-3.0 * A_U * np.sin(3.0 * phi))[:, None] * rc
          + (2.0 * rho)[:, None] * pc
          + (3.0 * b_u * np.cos(3.0 * phi))[:, None] * D111)
    r2 = (-(4.0 * R0_U + 13.0 * A_U * np.cos(3.0 * phi))[:, None] * rc
          - (12.0 * A_U * np.sin(3.0 * phi))[:, None] * pc
          - (9.0 * b_u * np.sin(3.0 * phi))[:, None] * D111)
    r3 = ((63.0 * A_U * np.sin(3.0 * phi))[:, None] * rc
          - (8.0 * R0_U + 62.0 * A_U * np.cos(3.0 * phi))[:, None] * pc
          - (27.0 * b_u * np.cos(3.0 * phi))[:, None] * D111)

    js = np.linalg.norm(r1, axis=1)
    ds = js * dphi
    ell_u = float(np.sum(ds))
    c12 = np.cross(r1, r2)
    c12_n = np.linalg.norm(c12, axis=1)
    tang, bino = r1 / js[:, None], c12 / c12_n[:, None]
    norm = np.cross(bino, tang)
    kap = c12_n / (js ** 3)
    tau = np.sum(c12 * r3, axis=1) / (c12_n ** 2)

    j_vec = np.cross(r, r1)
    j_perp_num = j_vec - (j_vec @ D111)[:, None] * D111[None, :]
    j_perp_ex = ((-2.0 * rho * w)[:, None] * rc
                 - (3.0 * b_u * (A_U + R0_U * np.cos(3.0 * phi)))[:, None] * pc)
    err_jperp = float(np.max(np.abs(j_perp_num - j_perp_ex)))
    return {
        "b_u": b_u, "phi": phi, "dphi": dphi, "r": r, "r1": r1, "js": js,
        "ds": ds, "ell": ell_u, "T": tang, "N": norm, "B": bino,
        "kap": kap, "tau": tau, "t_d": tang @ D111, "err_jperp": err_jperp,
    }


def gonzalez_maddocks_exact_thickness(st):
    phi_sub = st["phi"][::2]
    r_u = st["r"][::2] / st["ell"]
    t_u = st["T"][::2]
    n_p = len(r_u)
    diff = r_u[None, :, :] - r_u[:, None, :]
    d2 = np.sum(diff ** 2, axis=-1)
    d2[np.arange(n_p), np.arange(n_p)] = 1e9
    cr_n = np.linalg.norm(np.cross(diff, t_u[:, None, :]), axis=-1)
    rad_mat = d2 / (2.0 * np.maximum(cr_n, 1e-18))
    i0, j0 = np.unravel_index(int(np.argmin(rad_mat)), rad_mat.shape)

    def gm_pair_radius(angles):
        p1, p2 = angles
        r1, t1 = trefoil_point_and_tangent_u(p1, st["b_u"], st["ell"])
        r2, _ = trefoil_point_and_tangent_u(p2, st["b_u"], st["ell"])
        df = r2 - r1
        dd2 = float(np.dot(df, df))
        if dd2 < 1e-12:
            return 1e9
        cn = float(np.linalg.norm(np.cross(df, t1)))
        return dd2 / (2.0 * max(cn, 1e-18))

    res = minimize(
        gm_pair_radius, [phi_sub[i0], phi_sub[j0]],
        method="Nelder-Mead", options={"xatol": 1e-13, "fatol": 1e-15}
    )
    r_global = float(res.fun)
    r_focal = 1.0 / float(np.max(st["kap"] * st["ell"]))
    return min(r_global, r_focal), r_focal


def compute_v32_relaxed_scales(st_p, st_n, rst_p, rst_n):
    """
    Divergence-conserved V3.2 scales (Boxes 16, 19, & 34):
      - Strain volume V_tau(p)/V_tau(n) = M_P/M_N = 0.998623 (proton less strained)
      - Cavity volume V_rc * V_tau^3 = const => V_tube(p)/V_tube(n) = (M_N/M_P)^3
      - Tighter 90-deg neutron jammed at GM self-contact: L_n = r_tn / rst_n
      - Relaxed 109.5-deg proton uncoils to L_p = (M_N/M_P)*L_n > L_n with +13.4%
        un-jammed throat clearance and universal lobe flux Phi_0 (eta_p=eta_n=1).
    """
    r_tn = HBAR_C / (np.sqrt(3.0) * M_N)
    r_tp = HBAR_C / (np.sqrt(3.0) * M_P)
    l_n = r_tn / rst_n
    l_p = (M_N / M_P) * l_n
    rmax_n = l_n / st_n["ell"]
    rmax_p = l_p / st_p["ell"]
    return {
        "l_p": l_p, "l_n": l_n, "r_tp": r_tp, "r_tn": r_tn,
        "rmax_p": rmax_p, "rmax_n": rmax_n, "eta_p": 1.0, "eta_n": 1.0,
        "rst_p_jam": rst_p, "rst_p_act": r_tp / l_p, "rst_n": rst_n,
    }


def gauss_writhe_curve(r_pts, dr_pts):
    diff = r_pts[:, None, :] - r_pts[None, :, :]
    dist = np.linalg.norm(diff, axis=-1)
    np.fill_diagonal(dist, 1.0)
    integ = np.sum(np.cross(dr_pts[:, None, :], dr_pts[None, :, :]) * diff,
                   axis=-1) / (dist ** 3)
    np.fill_diagonal(integ, 0.0)
    return float(np.sum(integ) / (4.0 * np.pi))


def knot_alexander_determinant(r_pts):
    """Alexander determinant |Delta_K(-1)| under exact SO(3) projection."""
    r_so3 = rot_x(1.0 / 7.0) @ rot_y(1.0 / 5.0)
    p = r_pts @ r_so3.T
    n_p = len(p)
    crossings = []
    for i in range(n_p):
        i2 = (i + 1) % n_p
        a_pt, b_pt = p[i, :2], p[i2, :2]
        for j in range(i + 2, n_p):
            if i == 0 and j == n_p - 1:
                continue
            j2 = (j + 1) % n_p
            c_pt, d_pt = p[j, :2], p[j2, :2]
            mat_m = np.column_stack([b_pt - a_pt, -(d_pt - c_pt)])
            if abs(np.linalg.det(mat_m)) < 1e-12:
                continue
            u, v = np.linalg.solve(mat_m, c_pt - a_pt)
            if 0.0 <= u < 1.0 and 0.0 <= v < 1.0:
                z1 = p[i, 2] + u * (p[i2, 2] - p[i, 2])
                z2 = p[j, 2] + v * (p[j2, 2] - p[j, 2])
                crossings.append((i + u, j + v, z1 > z2))
    under = sorted([(s2 if ab_ov else s1, kc)
                    for kc, (s1, s2, ab_ov) in enumerate(crossings)])
    nc = len(under)
    if nc <= 2:
        return 1
    mat = np.zeros((nc, nc))
    for row, (_, kc) in enumerate(under):
        s1, s2, ab_ov = crossings[kc]
        s_ov = s1 if ab_ov else s2
        arc_ov = next((iu for iu in range(nc) if s_ov < under[iu][0]), 0)
        mat[row, arc_ov] += 2.0
        mat[row, row] -= 1.0
        mat[row, (row + 1) % nc] -= 1.0
    return int(round(abs(np.linalg.det(mat[:-1, :-1]))))


def run_sec1_geometry_and_meson(st_p, st_n, sc, rfoc_n, wr_p, wr_n):
    rp, rn = st_p["r"], st_n["r"]
    phi, dphi = st_p["phi"], st_p["dphi"]
    c_face = 1.0 / np.sqrt(2.0)
    max_xn = float(np.max(np.abs(rn))) / c_face
    max_xp = float(np.max(np.abs(rp))) / c_face
    max_rhomb = float(np.max(np.abs(rp + (rp @ D111)[:, None] * D111))) / c_face

    alp0 = np.arctan2(-3.0 * np.sqrt(7.0) / 8.0, -1.0 / 8.0)
    n_f = [-D111]
    for k in range(3):
        ang = alp0 + 4.0 * np.pi * k / 3.0
        u_d = np.cos(ang) * U0 + np.sin(ang) * V0
        n_f.append((1.0 / 3.0) * D111 + (2.0 * np.sqrt(2.0) / 3.0) * u_d)
    d_b = np.array([np.sqrt(2.0) / 6.0] + [np.sqrt(14.0) / 4.0] * 3)
    tet_pos_err = float(np.max((rp @ np.array(n_f).T) - d_b[None, :]))

    n_tot = len(phi)
    t_tet = np.vstack([-D111, st_p["T"][[0, n_tot // 3, (2 * n_tot) // 3]]])
    tet_ang_err = float(np.max(np.abs(
        (t_tet @ t_tet.T)[~np.eye(4, dtype=bool)] + 1.0 / 3.0
    )))

    bu0, dpsi = 0.30, 0.35
    rho_u = R0_U + A_U * np.cos(3.0 * phi)
    w_s = bu0 * np.sin(3.0 * phi + dpsi)
    wp_s = 3.0 * bu0 * np.cos(3.0 * phi + dpsi)
    lhs_lag = 0.2 * float(np.sum(w_s * wp_s / rho_u)) * dphi
    rhs_lag = 0.3 * np.pi * (7.0 * np.sqrt(5.0) - 15.0) * (bu0 ** 2) * np.sin(2.0 * dpsi)

    twf_p = float(np.sum(st_p["tau"] * st_p["ds"]) / (2.0 * np.pi))
    twf_n = float(np.sum(st_n["tau"] * st_n["ds"]) / (2.0 * np.pi))
    det_31 = knot_alexander_determinant(rn[::6])

    # Exact spherical Neumann Bessel roots j_0'(x_n) = 0 <=> tan(x_n) = x_n
    r_cn = HBAR_C / M_N
    x_neu = [
        float(brentq(lambda x: np.tan(x) - x, (k + 0.01) * np.pi, (k + 0.499) * np.pi))
        for k in (1, 2, 3, 4)
    ]
    r_sh = [xn * r_cn for xn in x_neu]
    re_bessel_p = float(np.sqrt(1.0 / 3.0 - 1.0 / (6.0 * (x_neu[0] ** 2))) * R_PI)

    t_m = np.linspace(0.0, 2.0 * np.pi, 360, endpoint=False)
    dt_m = 2.0 * np.pi / 360
    r_mes = np.column_stack([np.sin(t_m), 0.5 * np.sin(2.0 * t_m), 0.25 * np.cos(3.0 * t_m)])
    dr_mes = np.column_stack([np.cos(t_m), np.cos(2.0 * t_m), -0.75 * np.sin(3.0 * t_m)]) * dt_m
    det_mes = knot_alexander_determinant(r_mes)
    wr_mes = gauss_writhe_curve(r_mes, dr_mes)
    dl_mes = np.cross(r_mes, dr_mes)
    lz_r, lz_l = float(np.sum(dl_mes[:180, 2])), float(np.sum(dl_mes[180:, 2]))
    l_tot_mes = float(np.linalg.norm(np.sum(dl_mes, axis=0)))
    gap_pct = 100.0 * (sc["rst_p_jam"] / sc["rst_p_act"] - 1.0)

    print("=== 1. V3.2 INVERSE-CUBE RELAXED PROTON, De=3 RUPTURE, & 2-LOBE MESON ===",
          flush=True)
    print(f"  Unit Contact  : |r_n(0)|={np.linalg.norm(rn[0]):.6f}, "
          f"|r_p(0)|={np.linalg.norm(rp[0]):.6f} | "
          f"ell_u(n,p)=({st_n['ell']:.6f},{st_p['ell']:.6f})")
    print(f"  Relaxed p+    : L_p={sc['l_p']:.4f} fm > L_n={sc['l_n']:.4f} fm | "
          f"R_max(p,n)=({sc['rmax_p']:.4f},{sc['rmax_n']:.4f}) fm "
          f"(+{100*(sc['rmax_p']/sc['rmax_n']-1):.2f}%)")
    print(f"  Strain vs Cav : V_tau(p/n)={M_P/M_N:.6f} (p+ less strained) | "
          f"V_rc(p/n)={(M_N/M_P)**3:.6f} | p+ throat gap=+{gap_pct:.2f}% (< focal {rfoc_n:.4f})")
    print(f"  De=1 & De=3   : L_crit=r_e={R_E:.4f} fm (De=1) | r_break=r_e/3={R_E/3:.4f} fm "
          f"(De=3: U_Hooke={U_HOOKE_DE3:.3f} MeV => r_pi={R_PI:.5f} fm)")
    print(f"  Neumann Shells: R_1..4=({r_sh[0]:.4f}, {r_sh[1]:.4f}, {r_sh[2]:.4f} < r_e < "
          f"{r_sh[3]:.4f}) fm | dR_12={r_sh[1]-r_sh[0]:.4f} vs L_n/12={sc['l_n']/12:.4f} fm "
          f"| r_E(Bessel)={re_bessel_p:.4f} fm")
    print(f"  Polyhedra     : max|X_n|/c={max_xn:.6f}, max|X_p|/c={max_xp:.6f}, "
          f"Rhomb={max_rhomb:.6f}, Tet_err={tet_pos_err:+.2e}, S^2_err={tet_ang_err:.2e}")
    print(f"  3_1 Baryon    : |Delta(-1)|={det_31} (B=1), "
          f"Lk_F(n,p)=({wr_n+twf_n:+.4f},{wr_p+twf_p:+.4f}) | "
          f"j_perp_err={st_p['err_jperp']:.2e}, lag_err={abs(lhs_lag-rhs_lag):.2e}")
    print(f"  2-Lobe Meson  : |Delta(-1)|={det_mes} (B=0), "
          f"Lz_lobes=({lz_r:+.4f},{lz_l:+.4f}) -> "
          f"|L_tot|={l_tot_mes:.2e}, Wr={wr_mes:+.2e}", flush=True)

# ======================================================================
# SECTION 2 & 3: KELVIN BEM, EXTERIOR LAPLACE F_1(Q^2), & GORDON-SACHS
# ======================================================================
def solve_kelvin_bem_and_check_eq23(st, a_bead, m_beads=180):
    s_cum = np.concatenate([[0.0], np.cumsum(st["ds"]) / st["ell"]])
    s_u = np.linspace(0.0, 1.0, m_beads, endpoint=False)

    def interp_per(arr):
        ap = np.vstack([arr, arr[0:1]])
        return np.column_stack([np.interp(s_u, s_cum, ap[:, c]) for c in (0, 1, 2)])

    r = interp_per(st["r"] / st["ell"])
    tang, norm, bino = interp_per(st["T"]), interp_per(st["N"]), interp_per(st["B"])
    tang /= np.linalg.norm(tang, axis=1, keepdims=True)
    norm /= np.linalg.norm(norm, axis=1, keepdims=True)
    bino /= np.linalg.norm(bino, axis=1, keepdims=True)

    nu = NU_ELAST
    c_pre = 1.0 / (16.0 * np.pi * (1.0 - nu))
    diff = r[:, None, :] - r[None, :, :]
    re = np.sqrt(np.sum(diff ** 2, axis=-1) + (a_bead ** 2))
    eye3 = np.eye(3)[None, None, :, :]
    g_4d = c_pre * (
        ((3.0 - 4.0 * nu) / re + (a_bead ** 2) / (re ** 3))[:, :, None, None] * eye3
        + (1.0 / (re ** 3))[:, :, None, None] * (diff[:, :, :, None] * diff[:, :, None, :])
    )
    g_mat = g_4d.transpose(0, 2, 1, 3).reshape(3 * m_beads, 3 * m_beads)
    rhs = np.column_stack([tang.ravel(), bino.ravel(), norm.ravel()])
    sol = np.linalg.solve(g_mat, rhs)
    f_t, f_b, f_n = (sol[:, k].reshape(m_beads, 3) for k in (0, 1, 2))

    def mults(fv):
        d0 = float(np.sum(r * fv))
        d_ij = fv.T @ r
        s_ij = 0.5 * (d_ij + d_ij.T) - (d0 / 3.0) * np.eye(3)
        return (float(np.sum(fv @ D111)), float(np.sum(np.cross(r, fv) @ D111)),
                d0, float(D111 @ s_ij @ D111), s_ij)

    mt, mb, mn = mults(f_t), mults(f_b), mults(f_n)
    chi_f = -np.arctan2(mt[0], mb[0])
    mff = mults(np.cos(chi_f) * f_t + np.sin(chi_f) * f_b)

    f_n0 = f_n - np.mean(f_n, axis=0, keepdims=True)
    _, _, d0_n, _, s_mat_n = mults(f_n0)
    x_test = 150.0 * np.array([0.8, 0.7, 0.5]) / np.linalg.norm([0.8, 0.7, 0.5])
    dx = x_test[None, :] - r
    rx = np.linalg.norm(dx, axis=1)
    u_exact = c_pre * np.sum(
        ((3.0 - 4.0 * nu) / rx)[:, None] * f_n0
        + (np.sum(dx * f_n0, axis=1) / (rx ** 3))[:, None] * dx,
        axis=0
    )
    r_far = float(np.linalg.norm(x_test))
    r_hat = x_test / r_far
    u_eq23 = (
        ((1.0 - 2.0 * nu) * d0_n / (24.0 * np.pi * (1.0 - nu) * (r_far ** 2))) * r_hat
        + (2.0 * (1.0 - 2.0 * nu) * (s_mat_n @ r_hat)
           + 3.0 * float(r_hat @ s_mat_n @ r_hat) * r_hat)
        / (16.0 * np.pi * (1.0 - nu) * (r_far ** 2))
    )
    rel_err23 = float(np.linalg.norm(u_exact - u_eq23) / np.linalg.norm(u_exact))
    return mt[:4], mb[:4], (np.rad2deg(chi_f),) + mff[:4], mn[:4], rel_err23


def solve_exterior_metric_induced_charge(st, l_phys, r_t, n_s=90, n_th=12):
    """1080-panel exterior Laplace BEM on 2D torus boundary dT_p."""
    stride = len(st["phi"]) // n_s
    idx = np.arange(0, len(st["phi"]), stride)[:n_s]
    sc = l_phys / st["ell"]
    r_c = sc * st["r"][idx]
    ds_i = sc * st["ds"][idx] * stride
    norm, bino = st["N"][idx], st["B"][idx]
    kap = st["kap"][idx] / sc

    vth = np.linspace(0.0, 2.0 * np.pi, n_th, endpoint=False)
    dth = 2.0 * np.pi / n_th
    cos_t, sin_t = np.cos(vth), np.sin(vth)
    x_pan = r_c[:, None, :] + r_t * (
        cos_t[None, :, None] * norm[:, None, :] + sin_t[None, :, None] * bino[:, None, :]
    )
    len_s = np.repeat(ds_i[:, None], n_th, axis=1)
    len_th = r_t * (1.0 - r_t * kap[:, None] * cos_t[None, :]) * dth

    pts = x_pan.reshape(-1, 3)
    a_s, b_t = len_s.ravel(), len_th.ravel()
    area = a_s * b_t
    dist = np.linalg.norm(pts[:, None, :] - pts[None, :, :], axis=-1)
    np.fill_diagonal(dist, 1.0)
    g_mat = 1.0 / (4.0 * np.pi * dist)
    diag_self = (
        a_s * np.log((b_t + np.sqrt(a_s ** 2 + b_t ** 2)) / a_s)
        + b_t * np.log((a_s + np.sqrt(a_s ** 2 + b_t ** 2)) / b_t)
    ) / (2.0 * np.pi * area)
    np.fill_diagonal(g_mat, diag_self)

    q_pan = np.linalg.solve(g_mat, np.ones(len(pts)))
    w_ind = q_pan / float(np.sum(q_pan))
    x2_ind = float(np.sum(w_ind * np.sum(pts ** 2, axis=-1)))
    q_ring = w_ind.reshape(n_s, n_th).sum(axis=1) / ds_i
    return pts, w_ind, x2_ind, float(q_ring[0] / q_ring[n_s // 6])


def build_gordon_sachs_evaluator(st, l_phys, r_t_spec, m_spec, q_ch, sgn_pol, ind_pack=None):
    """Unified Gordon-Sachs evaluator integrating exterior Laplace w_ind in F_1(Q^2)."""
    rc_spec = HBAR_C / m_spec
    idx = np.arange(0, len(st["phi"]), 4)
    sc = l_phys / st["ell"]
    r_c = sc * st["r"][idx]
    ds = sc * st["ds"][idx] * 4.0
    norm, bino = st["N"][idx], st["B"][idx]
    kap = st["kap"][idx] / sc

    vth = np.linspace(0.0, 2.0 * np.pi, 16, endpoint=False)
    x_surf = r_c[:, None, :] + r_t_spec * (
        np.cos(vth)[None, :, None] * norm[:, None, :]
        + np.sin(vth)[None, :, None] * bino[:, None, :]
    )
    x_mag_u = np.linalg.norm(x_surf, axis=-1)
    x2_unif = float(np.sum((ds / l_phys) * np.mean(x_mag_u ** 2, axis=1)))

    if ind_pack is not None and q_ch != 0.0:
        pts_ind, w_ind, x2_active = ind_pack
        x_ind_mag = np.linalg.norm(pts_ind, axis=1)
    else:
        w_ind, x_ind_mag, x2_active = None, None, x2_unif

    rho1_ds = q_ch * (ds / l_phys)
    m_vec = sgn_pol * (r_t_spec / (4.0 * rc_spec)) * (kap[:, None] * bino)
    m111_ds = (m_vec @ D111) * ds
    r_mag_c = np.linalg.norm(r_c, axis=1)
    r_hat_c = r_c / r_mag_c[:, None]
    m_quad_ds = 0.5 * (
        (m_vec @ D111) - 3.0 * np.sum(m_vec * r_hat_c, axis=1) * (r_hat_c @ D111)
    ) * ds

    kap_anom = float(np.sum(m111_ds))
    mu_tot = float(q_ch + kap_anom)
    im0 = float(np.sum(m111_ds * (r_mag_c ** 2)))
    im2 = float(np.sum(m_quad_ds * (r_mag_c ** 2)))

    re2_bare = q_ch * x2_active + 1.5 * (rc_spec ** 2) * kap_anom
    re2_dres = q_ch * (x2_active + 6.0 * (r_t_spec ** 2)) + 1.5 * (rc_spec ** 2) * mu_tot
    re2_u_br = q_ch * x2_unif + 1.5 * (rc_spec ** 2) * kap_anom
    re2_u_dr = q_ch * (x2_unif + 6.0 * (r_t_spec ** 2)) + 1.5 * (rc_spec ** 2) * mu_tot
    rm2_bare = (q_ch * x2_active + im0 - 0.4 * im2) / mu_tot
    rm2_dres = (
        q_ch * (x2_active + 6.0 * (r_t_spec ** 2) + 1.5 * (rc_spec ** 2))
        + im0 - 0.4 * im2 + kap_anom * (6.0 * (r_t_spec ** 2) + 3.0 * (rc_spec ** 2))
    ) / mu_tot

    def eval_sachs(q2_gev2, dressed=True):
        q_mev = 1000.0 * np.sqrt(q2_gev2)
        k_q = q_mev / HBAR_C
        tau_b = (q_mev ** 2) / (4.0 * (m_spec ** 2))
        if k_q < 1e-10:
            return float(q_ch), mu_tot, tau_b
        k_int = k_q / (1.0 + tau_b) if dressed else k_q
        if w_ind is not None:
            f1_raw = float(q_ch * np.sum(w_ind * spherical_jn(0, k_int * x_ind_mag)))
        else:
            f1_raw = float(np.sum(rho1_ds * np.mean(spherical_jn(0, k_int * x_mag_u), axis=1)))
        xs_c = k_int * r_mag_c
        f2_raw = float(np.sum(
            m111_ds * spherical_jn(0, xs_c) + m_quad_ds * spherical_jn(2, xs_c)
        ))
        if dressed:
            prop = 1.0 / (1.0 + (r_t_spec * k_q) ** 2)
            f1 = f1_raw * prop / (1.0 + tau_b)
            f2 = f2_raw * prop / ((1.0 + tau_b) ** 2)
        else:
            f1, f2 = f1_raw, f2_raw
        return f1 - tau_b * f2, f1 + f2, tau_b

    moments_0 = (mu_tot, re2_dres, re2_bare, rm2_dres, rm2_bare, re2_u_dr, re2_u_br)
    return eval_sachs, moments_0


def run_sec3_single_nucleon_ledger(st_p, st_n, sc):
    pts_i, w_i, x2_i, ratio_ap_th = solve_exterior_metric_induced_charge(
        st_p, sc["l_p"], sc["r_tp"]
    )
    eval_p, mom_p = build_gordon_sachs_evaluator(
        st_p, sc["l_p"], sc["r_tp"], M_P, 1.0, +1.0, (pts_i, w_i, x2_i)
    )
    eval_n, mom_n = build_gordon_sachs_evaluator(
        st_n, sc["l_n"], sc["r_tn"], M_N, 0.0, -1.0, None
    )
    mu_p, re2_p_dr, re2_p_br, rm2_p_dr, rm2_p_br, re2_u_dr, re2_u_br = mom_p
    mu_n, re2_n_dr, _, rm2_n_dr, rm2_n_br, _, _ = mom_n
    re_p_dr, re_p_br = float(np.sqrt(re2_p_dr)), float(np.sqrt(re2_p_br))
    re_u_dr, re_u_br = float(np.sqrt(re2_u_dr)), float(np.sqrt(re2_u_br))
    rm_p_dr, rm_p_br = float(np.sqrt(rm2_p_dr)), float(np.sqrt(rm2_p_br))
    rm_n_dr, rm_n_br = float(np.sqrt(rm2_n_dr)), float(np.sqrt(rm2_n_br))

    q2_chk = 1e-6
    kq2_chk = ((1000.0 * np.sqrt(q2_chk)) / HBAR_C) ** 2
    gep_c, gmp_c, _ = eval_p(q2_chk, True)
    gen_c, gmn_c, _ = eval_n(q2_chk, True)
    slope_err = max(
        abs(re2_p_dr - (-6.0 * (gep_c - 1.0) / kq2_chk)),
        abs(re2_n_dr - (-6.0 * gen_c / kq2_chk)),
        abs(rm2_p_dr - (-6.0 * (gmp_c / mu_p - 1.0) / kq2_chk)),
        abs(rm2_n_dr - (-6.0 * (gmn_c / mu_n - 1.0) / kq2_chk)),
    )

    r_ce = HBAR_C / M_E
    mu_e_over_p = (M_P / M_E) * (1.0 + ALPHA / (2.0 * np.pi)) / mu_p
    r_null_f0 = r_ce * ((2.0 * mu_e_over_p) ** (-1.0 / 3.0))
    z_null_f1 = r_ce * (mu_e_over_p ** (-1.0 / 3.0))

    kq_g = np.linspace(1e-3, 35.0, 450)
    dkq = kq_g[1] - kq_g[0]
    q2_g = ((kq_g * HBAR_C) / 1000.0) ** 2
    gep_a, gmp_a, tb_a = zip(*[eval_p(q2, True) for q2 in q2_g])
    gen_a, gmn_a, _ = zip(*[eval_n(q2, True) for q2 in q2_g])
    gep_a, gmp_a = np.array(gep_a), np.array(gmp_a)
    gen_a, gmn_a, tb_a = np.array(gen_a), np.array(gmn_a), np.array(tb_a)
    du_em = (
        (ALPHA * HBAR_C / np.pi) * float(np.sum(gen_a ** 2 - gep_a ** 2) * dkq)
        + (2.0 * ALPHA * HBAR_C / (3.0 * np.pi))
        * float(np.sum(tb_a * (gmn_a ** 2 - gmp_a ** 2)) * dkq)
    )

    w_pn = np.sqrt((st_p["ds"] / st_p["ell"]) * (st_n["ds"] / st_n["ell"]))
    o_np = float(np.sum(w_pn * np.sum(st_p["T"] * st_n["T"], axis=1)))
    tp_perp = st_p["T"] - st_p["t_d"][:, None] * D111[None, :]
    tn_perp = st_n["T"] - st_n["t_d"][:, None] * D111[None, :]
    m_perp = float(np.sum(w_pn * np.sum(tp_perp * tn_perp, axis=1)))

    print("\n=== 3. ANALYTIC GORDON-SACHS SINGLE-NUCLEON LEDGER (A=1, 0 FREE PARAMS) ===",
          flush=True)
    print(f"  Scales: L_p={sc['l_p']:.4f} > L_n={sc['l_n']:.4f} fm | "
          f"r_t(p,n)=({sc['r_tp']:.5f},{sc['r_tn']:.5f}) fm | err={slope_err:.2e}")
    print("  Observable                   | Computed          | Exp_Ref           | Residual / Note")
    print(f"  Proton mu_p [u_N]            | {mu_p:+17.4f} | +2.792847         | "
          f"{100*(mu_p/2.792847-1):+6.2f}%")
    print(f"  Neutron mu_n [u_N]           | {mu_n:+17.4f} | -1.913043         | "
          f"{100*(mu_n/-1.913043-1):+6.2f}%")
    print(f"  Isovector mu_p - mu_n [u_N]  | {mu_p-mu_n:+17.4f} | +4.705890         | "
          f"{100*((mu_p-mu_n)/4.70589-1):+6.2f}%")
    print(f"  p+ r_E Metric-Ind (Br / Dr)  | {re_p_br:7.4f} / {re_p_dr:7.4f} | "
          f"0.84075 fm        | {100*(re_p_br/0.84075-1):+6.2f}% (apex/th={ratio_ap_th:.1f}x)")
    print(f"  p+ r_E Uniform (Dres / Bare) | {re_u_dr:7.4f} / {re_u_br:7.4f} | "
          f"0.84075 fm        | {100*(re_u_dr/0.84075-1):+6.2f}% (rho_1=Q/L_p)")
    print(f"  Neutron <r_E^2>_n (Foldy)    | {re2_n_dr:+17.5f} | -0.1155 fm^2      | "
          f"{100*(re2_n_dr/-0.1155-1):+6.2f}% (Phi_n=0 exact)")
    print(f"  Proton r_M (Dressed / Bare)  | {rm_p_dr:7.4f} / {rm_p_br:7.4f} | "
          f"0.776(34) fm      | {100*(rm_p_dr/0.776-1):+6.2f}% (w_ind in F_1)")
    print(f"  Neutron r_M (Dressed / Bare) | {rm_n_dr:7.4f} / {rm_n_br:7.4f} | "
          f"0.780 fm          | {100*(rm_n_dr/0.780-1):+6.2f}%")
    print(f"  Cottingham dU_EM(n-p) [MeV]  | {du_em:+17.4f} | -1.00(16) MeV     | "
          f"dU_mech={M_N-M_P-du_em:+.3f}")
    print(f"  1D Overlaps O_np / M_perp    | {o_np:7.5f} / {m_perp:7.5f} | "
          f"g_A/g_V=1.2754    | Pure 1-tube (0 SU6 mult)")
    print(f"  H 21cm Nulls (F=0 / F=1)     | R={r_null_f0:.2f}, z=+-{z_null_f1:.2f} fm | "
          "Spheromak / ring", flush=True)
    return mu_p, mu_n, re_p_br, re2_n_dr, (pts_i, w_i, x2_i)


# ======================================================================
# SECTION 4: DETERMINISTIC SOG & CG FEW-BODY SOLVER (WITH De(r) CUTOFF)
# ======================================================================
def build_two_body_channels(d_grid, sc):
    rp, drp, dsp = build_trefoil_discrete_z(B_U_P, sc["l_p"], 36)
    rn, drn, dsn = build_trefoil_discrete_z(B_U_N, sc["l_n"], 36)
    rtp, rtn = sc["r_tp"], sc["r_tn"]

    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, 3, endpoint=False)
    mu_pts, mu_wts = leggauss(8)
    p2_vals = 0.5 * (3.0 * (mu_pts ** 2) - 1.0)
    u_dirs = np.column_stack([np.zeros_like(mu_pts), np.sqrt(1.0 - mu_pts ** 2), mu_pts])
    w_r = 0.5 * mu_wts
    ey, ez = np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])

    def sphere_mults(ra0, dra0, dsa, rb0, drb0, dsb, sig2_ab, anti):
        ra_s, dra_s, rb_s, drb_s = [], [], [], []
        for t in taus:
            ra_m = frame_from_z_and_ref(+ez, +ey, -t if anti else +t)
            rb_m = (frame_from_z_and_ref(-ez, -ey, +t + np.pi / 3.0) if anti
                    else frame_from_z_and_ref(+ez, +ey, +t + np.pi / 3.0))
            ra_s.append(ra0 @ ra_m.T)
            dra_s.append(dra0 @ ra_m.T)
            rb_s.append(rb0 @ rb_m.T)
            drb_s.append(drb0 @ rb_m.T)
        ra_s, dra_s, rb_s, drb_s = map(np.array, (ra_s, dra_s, rb_s, drb_s))
        dot_dr = np.einsum("tik,tjk->tij", dra_s, drb_s)[None, ...]
        ds_mat = (dsa[:, None] * dsb[None, :])[None, None, :, :]
        fac = 1.0 / (4.0 * np.pi * len(taus))

        m0, m2, s0, b0 = (np.zeros(len(d_grid)) for _ in range(4))
        for idx, d in enumerate(d_grid):
            sh = (d * u_dirs)[:, None, None, None, :] + rb_s[None, :, None, :, :]
            diff = ra_s[None, :, :, None, :] - sh
            d2 = np.sum(diff ** 2, axis=-1) + sig2_ab
            d12 = np.sqrt(d2)
            e1 = np.exp(-d12 / R_PI)
            g_de = (R_E ** 2) / (d2 + (R_E ** 2))
            m_ray = np.sum(dot_dr * g_de * e1 / d12, axis=(1, 2, 3)) * fac
            s_ray = np.sum(ds_mat * g_de * (e1 * e1) / d12, axis=(1, 2, 3)) * fac
            b_ray = np.sum(ds_mat / (d2 ** 2), axis=(1, 2, 3)) * fac
            m0[idx] = float(np.sum(w_r * m_ray))
            m2[idx] = float(np.sum(w_r * p2_vals * m_ray))
            s0[idx] = float(np.sum(w_r * s_ray))
            b0[idx] = float(np.sum(w_r * b_ray))
        return m0, m2, s0, b0

    s2_pn, s2_nn, s2_pp = rtp ** 2 + rtn ** 2, 2.0 * (rtn ** 2), 2.0 * (rtp ** 2)
    return {
        "pn1": sphere_mults(rp, drp, dsp, rn, drn, dsn, s2_pn, False),
        "pn0": sphere_mults(rp, drp, dsp, rn, drn, dsn, s2_pn, True),
        "nn1": sphere_mults(rn, drn, dsn, rn, drn, dsn, s2_nn, False),
        "nn0": sphere_mults(rn, drn, dsn, rn, drn, dsn, s2_nn, True),
        "pp1": sphere_mults(rp, drp, dsp, rp, drp, dsp, s2_pp, False),
        "pp0": sphere_mults(rp, drp, dsp, rp, drp, dsp, s2_pp, True),
    }


def safe_root(func, lo, hi, n_scan=60, pole_cut=3.0):
    xs = np.linspace(lo, hi, n_scan)
    fs = np.array([func(x) for x in xs])
    for i in range(n_scan - 1):
        if np.isfinite(fs[i]) and np.isfinite(fs[i + 1]) and fs[i] * fs[i + 1] <= 0.0:
            if abs(fs[i]) < pole_cut and abs(fs[i + 1]) < pole_cut:
                return float(brentq(func, xs[i], xs[i + 1]))
    return float(xs[np.nanargmin(np.abs(fs))])


def solve_deuteron_banded(rf, vc_i, vt_i, r2_ep, r2_en, mu_p, mu_n, only_e=False):
    dr = rf[1] - rf[0]
    n_p = len(rf)
    k_dr2 = HB2_2MU_NP / (dr ** 2)
    ab = np.zeros((3, 2 * n_p))
    ab[0, 0::2] = 2.0 * k_dr2 + vc_i
    ab[0, 1::2] = 2.0 * k_dr2 + vc_i - 2.0 * vt_i + 6.0 * HB2_2MU_NP / (rf ** 2)
    ab[1, 0::2] = np.sqrt(8.0) * vt_i
    ab[2, 0:-2:2] = -k_dr2
    ab[2, 1:-2:2] = -k_dr2
    if only_e:
        ev0 = eig_banded(ab, lower=True, eigvals_only=True, select="i", select_range=(0, 0))
        return float(ev0[0])

    ev, vec = eig_banded(ab, lower=True, select="i", select_range=(0, 0))
    u, w = vec[0::2, 0], vec[1::2, 0]
    if u[6] < 0.0:
        u, w = -u, -w
    nm = _TRAPZ(u ** 2 + w ** 2, rf)
    u, w = u / np.sqrt(nm), w / np.sqrt(nm)
    pd = 100.0 * float(_TRAPZ(w ** 2, rf))
    r_d = float(np.sqrt(_TRAPZ(((0.5 * rf) ** 2) * (u ** 2 + w ** 2), rf) + r2_ep + r2_en))
    q_d = 0.05 * float(_TRAPZ((rf ** 2) * w * (np.sqrt(8.0) * u - w), rf))
    mu_d = (mu_p + mu_n) - 1.5 * (mu_p + mu_n - 0.5) * (pd / 100.0)

    gam = np.sqrt(max(1e-8, -ev[0]) / HB2_2MU_NP)
    mask = rf < 13.0
    xr = gam * rf[mask]
    f0 = np.sinh(xr)
    f2 = (1.0 + 3.0 / (xr ** 2)) * np.sinh(xr) - (3.0 / xr) * np.cosh(xr)
    s_u = vc_i[mask] * u[mask] + np.sqrt(8.0) * vt_i[mask] * w[mask]
    s_w = np.sqrt(8.0) * vt_i[mask] * u[mask] + (vc_i[mask] - 2.0 * vt_i[mask]) * w[mask]
    eta_ds = float(_TRAPZ(f2 * s_w, rf[mask]) / _TRAPZ(f0 * s_u, rf[mask]))
    return float(ev[0]), r_d, q_d, pd, eta_ds, mu_d


def scatt_obs(r_g, v_g, hb2_2mu):
    dr = r_g[1] - r_g[0]
    u = np.zeros(len(r_g))
    u[0], u[1] = r_g[0], r_g[1]
    k2 = np.maximum(-v_g / hb2_2mu, -6.0 / (dr ** 2))
    for i in range(1, len(r_g) - 1):
        c0 = 1.0 + (dr ** 2) * k2[i - 1] / 12.0
        c1 = 2.0 * (1.0 - 5.0 * (dr ** 2) * k2[i] / 12.0)
        c2 = 1.0 + (dr ** 2) * k2[i + 1] / 12.0
        u[i + 1] = (c1 * u[i] - c0 * u[i - 1]) / c2
    du = (u[-1] - u[-3]) / (2.0 * dr)
    a_s = r_g[-2] - u[-2] / du
    u_n = u / (-a_s * du)
    phi0 = 1.0 - r_g / a_s
    r_eff = 2.0 * float(_TRAPZ(phi0[:-1] ** 2 - u_n[:-1] ** 2, r_g[:-1]))
    return float(a_s), r_eff


class SOGPotentialBank:
    """Uniformly fitted Sum-of-Gaussians expansion (zero hand-chosen peaks)."""

    def __init__(self, d_grid, v_dict, zero_at_origin=()):
        self.betas = 1.0 / (np.geomspace(0.12, 10.0, 28) ** 2)
        r_fit = np.linspace(0.0, 14.5, 580)
        g_m = np.exp(-(r_fit[:, None] ** 2) * self.betas[None, :])
        gtg = g_m.T @ g_m
        reg = 1e-13 * np.trace(gtg) / len(self.betas)
        self.coeffs = {}
        self.max_rms_err = 0.0
        for key, v_arr in v_dict.items():
            left_v = 0.0 if key in zero_at_origin else v_arr[0]
            v_f = np.interp(r_fit, d_grid, v_arr, left=left_v, right=0.0)
            if key in zero_at_origin:
                w_0 = np.ones_like(r_fit)
                w_0[0] = 1e6
                gtg_0 = g_m.T @ (w_0[:, None] * g_m)
                c_k = np.linalg.solve(gtg_0 + reg * np.eye(len(self.betas)), g_m.T @ (w_0 * v_f))
            else:
                c_k = np.linalg.solve(gtg + reg * np.eye(len(self.betas)), g_m.T @ v_f)
            self.coeffs[key] = c_k
            rms = float(np.sqrt(np.mean((g_m @ c_k - v_f) ** 2)))
            self.max_rms_err = max(self.max_rms_err, rms)

    def moments(self, key, gam):
        c = self.coeffs[key]
        mu = 1.0 / (1.0 + 2.0 * gam[..., None] * self.betas)
        m15 = mu * np.sqrt(mu)
        return (np.sum(c * m15, axis=-1),
                3.0 * gam * np.sum(c * m15 * mu, axis=-1),
                15.0 * (gam ** 2) * np.sum(c * m15 * (mu ** 2), axis=-1))


def eval_kron(pauli_c, p_idx, n_part, id2):
    op = np.array([[1.0]], dtype=np.complex128)
    for k in range(n_part):
        op = np.kron(op, pauli_c if k == p_idx else id2)
    return op


def build_spin_algebra(n_part):
    id2 = np.eye(2, dtype=np.complex128)
    paulis = [
        np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128),
        np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=np.complex128),
        np.array([[1.0, 0.0], [0.0, -1.0]], dtype=np.complex128),
    ]
    return [[eval_kron(paulis[c], p, n_part, id2) for c in range(3)] for p in range(n_part)]


def pair_spin_ops(sigs, i, j):
    dim = sigs[0][0].shape[0]
    id_n = np.eye(dim, dtype=np.complex128)
    s_dot = sum(sigs[i][c] @ sigs[j][c] for c in range(3))
    p1, p0 = 0.25 * (3.0 * id_n + s_dot), 0.25 * (id_n - s_dot)
    sig = np.zeros((3, 3, dim, dim), dtype=np.complex128)
    for a in range(3):
        for b in range(3):
            ab = sigs[i][a] @ sigs[j][b] + sigs[i][b] @ sigs[j][a]
            sig[a, b] = 1.5 * ab - (1.0 if a == b else 0.0) * s_dot
    return p1, p0, sig


def qubit_swap(n_part, p1, p2):
    dim = 1 << n_part
    u_sw = np.zeros((dim, dim), dtype=np.complex128)
    for s in range(dim):
        bits = [(s >> (n_part - 1 - k)) & 1 for k in range(n_part)]
        bits[p1], bits[p2] = bits[p2], bits[p1]
        u_sw[sum(b << (n_part - 1 - k) for k, b in enumerate(bits)), s] = 1.0
    return u_sw


def solve_cg_pure_2b(n_jac, kappa_kin, basis, perms, edges, quad_ops, sog_bank):
    idx_s = [i for i, b in enumerate(basis) if b["L"] == 0]
    idx_d = [i for i, b in enumerate(basis) if b["L"] == 2]
    b_ord = [basis[i] for i in idx_s] + [basis[i] for i in idx_d]
    ns, nd = len(idx_s), len(idx_d)
    m_tot, n_perm = ns + nd, len(perms)

    s_mat, t_mat, v2_mat = (np.zeros((m_tot, m_tot)) for _ in range(3))
    q_mats = [np.zeros((m_tot, m_tot)) for _ in quad_ops]

    a_all = np.array([b["A"] for b in b_ord])
    as_m = a_all[:ns]
    ad_m = a_all[ns:] if nd > 0 else np.zeros((0, n_jac, n_jac))
    ad_v = np.array([b_ord[ns + i]["a"] for i in range(nd)]) if nd > 0 else np.zeros((0, n_jac))
    chis = np.array([b_ord[i]["chi"] for i in range(ns)]) if ns > 0 else None
    xid = np.array([b_ord[ns + i]["Xi"] for i in range(nd)]) if nd > 0 else None

    for sgn, p_j, u_s in perms:
        wt_p = sgn / float(n_perm)
        if ns > 0:
            bs_m = np.einsum("ba,jbc,cd->jad", p_j, as_m, p_j)
            chis_p = (u_s @ chis.T).T
            c_ss = as_m[:, None, :, :] + bs_m[None, :, :, :]
            _, ld = np.linalg.slogdet(c_ss)
            i0_ss = (((2.0 * np.pi) ** n_jac) / np.exp(ld)) ** 1.5
            cinv_ss = np.linalg.inv(c_ss)
            sp_ov = np.real(np.conj(chis) @ chis_p.T)
            s_mat[:ns, :ns] += wt_p * sp_ov * i0_ss

            acinvb = np.einsum("ikm,ijmn,jnl->ijkl", as_m, cinv_ss, bs_m)
            tr_ss = np.trace(acinvb, axis1=2, axis2=3)
            t_mat[:ns, :ns] += wt_p * kappa_kin * 3.0 * tr_ss * sp_ov * i0_ss
            for k_q, q_op in enumerate(quad_ops):
                q_mats[k_q][:ns, :ns] += (
                    wt_p * 3.0 * np.einsum("mn,ijmn->ij", q_op, cinv_ss) * sp_ov * i0_ss
                )

            for w_e, k1, k0, _, p1_op, p0_op, _ in edges:
                gam = np.einsum("m,ijmn,n->ij", w_e, cinv_ss, w_e)
                j0_1, _, _ = sog_bank.moments(k1, gam)
                v_e = np.real(np.conj(chis) @ (p1_op @ chis_p.T)) * j0_1
                if k0 is not None:
                    j0_0, _, _ = sog_bank.moments(k0, gam)
                    v_e = v_e + np.real(np.conj(chis) @ (p0_op @ chis_p.T)) * j0_0
                v2_mat[:ns, :ns] += wt_p * v_e * i0_ss

        if ns > 0 and nd > 0:
            bd_m = np.einsum("ba,jbc,cd->jad", p_j, ad_m, p_j)
            bd_p = (p_j.T @ ad_v.T).T
            xid_p = np.einsum("st,jabt->jabs", u_s, xid)
            c_sd = as_m[:, None, :, :] + bd_m[None, :, :, :]
            _, ld_sd = np.linalg.slogdet(c_sd)
            i0_sd = (((2.0 * np.pi) ** n_jac) / np.exp(ld_sd)) ** 1.5
            cinv_sd = np.linalg.inv(c_sd)
            block_sd = np.zeros((ns, nd))
            for w_e, _, _, kt, _, _, sig_ef in edges:
                if kt is None:
                    continue
                gam = np.einsum("m,ijmn,n->ij", w_e, cinv_sd, w_e)
                lam_b = np.einsum("jm,ijmn,n->ij", bd_p, cinv_sd, w_e) / gam
                sig_chi = np.einsum("abst,it->iabs", sig_ef, chis)
                m_sd = np.real(np.einsum("iabs,jabs->ij", np.conj(sig_chi), xid_p))
                _, j1_t, _ = sog_bank.moments(kt, gam)
                block_sd += (2.0 / 15.0) * (lam_b ** 2) * m_sd * j1_t * i0_sd
            v2_mat[:ns, ns:] += wt_p * block_sd
            v2_mat[ns:, :ns] += wt_p * block_sd.T

        if nd > 0:
            bd_m = np.einsum("ba,jbc,cd->jad", p_j, ad_m, p_j)
            bd_p = (p_j.T @ ad_v.T).T
            xid_p = np.einsum("st,jabt->jabs", u_s, xid)
            c_dd = ad_m[:, None, :, :] + bd_m[None, :, :, :]
            _, ld_dd = np.linalg.slogdet(c_dd)
            i0_dd = (((2.0 * np.pi) ** n_jac) / np.exp(ld_dd)) ** 1.5
            cinv_dd = np.linalg.inv(c_dd)

            q_ab = np.einsum("im,ijmn,jn->ij", ad_v, cinv_dd, bd_p)
            m_dd = np.real(np.einsum("iabs,jabs->ij", np.conj(xid), xid_p))
            s_mat[ns:, ns:] += wt_p * 2.0 * (q_ab ** 2) * m_dd * i0_dd

            acinvb_dd = np.einsum("ikm,ijmn,jnl->ijkl", ad_m, cinv_dd, bd_m)
            tr_dd = np.trace(acinvb_dd, axis1=2, axis2=3)
            v_left = np.einsum("im,ijmn->ijn", ad_v, cinv_dd)
            v_right = np.einsum("ijmn,jn->ijm", cinv_dd, bd_p)
            ba_prod = np.einsum("jmk,ikl->ijml", bd_m, ad_m)
            quad_ba = np.einsum("ijm,ijml,ijl->ij", v_left, ba_prod, v_right)
            t_mat[ns:, ns:] += (
                wt_p * kappa_kin * (6.0 * tr_dd * (q_ab ** 2) + 8.0 * q_ab * quad_ba)
                * m_dd * i0_dd
            )

            for k_q, q_op in enumerate(quad_ops):
                tr_q = np.einsum("mn,ijmn->ij", q_op, cinv_dd)
                quad_q = np.einsum("ijm,ml,ijl->ij", v_left, q_op, v_right)
                q_mats[k_q][ns:, ns:] += (
                    wt_p * (6.0 * tr_q * (q_ab ** 2) + 8.0 * q_ab * quad_q) * m_dd * i0_dd
                )

            for w_e, k1, k0, kt, p1_op, p0_op, sig_ef in edges:
                gam = np.einsum("m,ijmn,n->ij", w_e, cinv_dd, w_e)
                q_ae = np.einsum("im,ijmn,n->ij", ad_v, cinv_dd, w_e)
                q_be = np.einsum("jm,ijmn,n->ij", bd_p, cinv_dd, w_e)
                la, lb, qt = q_ae / gam, q_be / gam, q_ab - (q_ae * q_be) / gam

                p1_xi = np.einsum("st,jabt->jabs", p1_op, xid_p)
                m_p1 = np.real(np.einsum("iabs,jabs->ij", np.conj(xid), p1_xi))
                j0_1, j1_1, j2_1 = sog_bank.moments(k1, gam)
                v2_mat[ns:, ns:] += wt_p * (
                    2.0 * (qt ** 2) * j0_1
                    + (4.0 / 3.0) * la * lb * qt * j1_1
                    + (2.0 / 15.0) * (la ** 2) * (lb ** 2) * j2_1
                ) * m_p1 * i0_dd

                if k0 is not None:
                    p0_xi = np.einsum("st,jabt->jabs", p0_op, xid_p)
                    m_p0 = np.real(np.einsum("iabs,jabs->ij", np.conj(xid), p0_xi))
                    j0_0, j1_0, j2_0 = sog_bank.moments(k0, gam)
                    v2_mat[ns:, ns:] += wt_p * (
                        2.0 * (qt ** 2) * j0_0
                        + (4.0 / 3.0) * la * lb * qt * j1_0
                        + (2.0 / 15.0) * (la ** 2) * (lb ** 2) * j2_0
                    ) * m_p0 * i0_dd

                if kt is not None:
                    sg_xi = np.einsum("bcst,jcat->jbas", sig_ef, xid_p)
                    m3 = np.real(np.einsum("iabs,jbas->ij", np.conj(xid), sg_xi))
                    _, jt_1, jt_2 = sog_bank.moments(kt, gam)
                    v2_mat[ns:, ns:] += wt_p * (
                        (8.0 / 15.0) * la * lb * qt * jt_1
                        + (8.0 / 105.0) * (la ** 2) * (lb ** 2) * jt_2
                    ) * m3 * i0_dd

    s_mat = 0.5 * (s_mat + s_mat.T)
    h2 = 0.5 * ((t_mat + v2_mat) + (t_mat + v2_mat).T)
    diag_s = np.diag(s_mat)
    idx_v = np.where(diag_s > 1e-24)[0]
    d_inv = 1.0 / np.sqrt(diag_s[idx_v])
    scale_m = np.outer(d_inv, d_inv)

    s_ev, s_vec = eigh(s_mat[np.ix_(idx_v, idx_v)] * scale_m)
    keep = s_ev > 1e-8
    x_norm = s_vec[:, keep] / np.sqrt(s_ev[keep])[None, :]
    evals, evecs_x = eigh(x_norm.T @ (h2[np.ix_(idx_v, idx_v)] * scale_m) @ x_norm)

    c_full = np.zeros(m_tot)
    c_full[idx_v] = (x_norm @ evecs_x[:, 0]) * d_inv
    c_full /= np.sqrt(c_full @ s_mat @ c_full)
    cd = c_full[ns:]
    pd = 100.0 * float(cd @ s_mat[ns:, ns:] @ cd) if nd > 0 else 0.0
    q_evs = [float(c_full @ (0.5 * (qm + qm.T)) @ c_full) for qm in q_mats]
    return float(evals[0]), pd, q_evs


def run_deuteron_cg_check(sog_bank, r2_ep, r2_en):
    sigs2 = build_spin_algebra(2)
    p1_op, p0_op, sig = pair_spin_ops(sigs2, 0, 1)
    chi1 = np.array([1.0, 0.0, 0.0, 0.0], dtype=np.complex128)
    xi1 = np.einsum("abst,t->abs", sig, chi1)
    w01 = np.array([np.sqrt(2.0)])
    mw = np.outer(w01, w01)
    basis = [{"L": 0, "A": mw / (r0 ** 2), "chi": chi1} for r0 in np.geomspace(0.20, 15.0, 22)]
    basis += [{"L": 2, "A": mw / (r0 ** 2), "a": w01, "Xi": xi1}
              for r0 in np.geomspace(0.28, 11.0, 18)]
    perms = [(+1.0, np.eye(1), np.eye(4, dtype=np.complex128))]
    edges = [(w01, "VC_pn", "V0_pn", "VT_pn", p1_op, p0_op, sig)]
    e0, pd, q_evs = solve_cg_pure_2b(
        1, 0.5 * HB2_2MU_NP, basis, perms, edges, [np.array([[0.5]])], sog_bank
    )
    return e0, float(np.sqrt(q_evs[0] + r2_ep + r2_en)), pd


def run_a3_pure_2b(z_ch, sog_bank, r2_ep, r2_en):
    sigs3 = build_spin_algebra(3)
    up, dn = np.array([1.0, 0.0]), np.array([0.0, 1.0])

    def st3(a, b, c):
        return np.kron(np.kron(a, b), c).astype(np.complex128)

    chi_rho = (st3(up, dn, up) - st3(dn, up, up)) / np.sqrt(2.0)
    chi_lam = (2.0 * st3(up, up, dn) - st3(up, dn, up) - st3(dn, up, up)) / np.sqrt(6.0)

    w01 = np.array([np.sqrt(2.0), 0.0])
    w02 = np.array([1.0 / np.sqrt(2.0), np.sqrt(1.5)])
    w12 = np.array([-1.0 / np.sqrt(2.0), np.sqrt(1.5)])
    q_cm = np.diag([0.0, 2.0 / 3.0]) if z_ch == 1 else np.diag([0.5, 1.0 / 6.0])

    p1_01, p0_01, sig_01 = pair_spin_ops(sigs3, 0, 1)
    p1_02, p0_02, sig_02 = pair_spin_ops(sigs3, 0, 2)
    p1_12, p0_12, sig_12 = pair_spin_ops(sigs3, 1, 2)
    xi_02 = np.einsum("abst,t->abs", sig_02, chi_rho)
    xi_lam = np.einsum("abst,t->abs", sig_02, chi_lam)
    m01, m02, m12 = np.outer(w01, w01), np.outer(w02, w02), np.outer(w12, w12)

    def make_a(r_id, r_a, r_b):
        return m01 / (r_id ** 2) + m02 / (r_a ** 2) + m12 / (r_b ** 2)

    basis = []
    for r_env in np.geomspace(1.00, 9.50, 6):
        basis.append({"L": 0, "A": make_a(r_env, r_env, r_env), "chi": chi_rho})
        for r_h in np.geomspace(0.36, 1.20, 3):
            basis += [
                {"L": 0, "A": make_a(r_h, r_env, r_env), "chi": chi_rho},
                {"L": 0, "A": make_a(r_env, r_h, r_env), "chi": chi_rho},
                {"L": 0, "A": make_a(r_env, r_h, r_env), "chi": chi_lam},
                {"L": 0, "A": make_a(r_h, r_h, r_env), "chi": chi_rho},
                {"L": 0, "A": make_a(r_h, r_h, r_env), "chi": chi_lam},
                {"L": 0, "A": make_a(r_env, r_h, r_h), "chi": chi_rho},
            ]
    for r_t in np.geomspace(0.45, 3.20, 5):
        for r_o in np.geomspace(1.10, 6.00, 4):
            basis.append({"L": 2, "A": make_a(r_o, r_t, r_o), "a": w02, "Xi": xi_02})
        for r_o in np.geomspace(1.50, 4.00, 2):
            basis.append({"L": 2, "A": make_a(r_o, r_t, r_o), "a": w02, "Xi": xi_lam})

    perms = [(+1.0, np.eye(2), np.eye(8, dtype=np.complex128)),
             (-1.0, np.diag([-1.0, 1.0]), qubit_swap(3, 0, 1))]
    k1_id = "V1_nn" if z_ch == 1 else "V1_pp"
    k0_id = "V0_nn" if z_ch == 1 else "V0_pp"
    edges = [
        (w01, k1_id, k0_id, None, p1_01, p0_01, sig_01),
        (w02, "VC_pn", "V0_pn", "VT_pn", p1_02, p0_02, sig_02),
        (w12, "VC_pn", "V0_pn", "VT_pn", p1_12, p0_12, sig_12),
    ]
    e0, pd, q_evs = solve_cg_pure_2b(2, HB2_2M0, basis, perms, edges, [q_cm], sog_bank)
    r_en_wt = 2.0 * r2_en if z_ch == 1 else 0.5 * r2_en
    return e0, float(np.sqrt(max(0.0, q_evs[0] + r2_ep + r_en_wt))), pd


def run_a4_pure_2b(sog_bank, r2_ep, r2_en):
    sigs4 = build_spin_algebra(4)
    s0 = np.array([0.0, 1.0, -1.0, 0.0], dtype=np.complex128) / np.sqrt(2.0)
    t_p = np.array([1.0, 0.0, 0.0, 0.0], dtype=np.complex128)
    t_0 = np.array([0.0, 1.0, 1.0, 0.0], dtype=np.complex128) / np.sqrt(2.0)
    t_m = np.array([0.0, 0.0, 0.0, 1.0], dtype=np.complex128)
    chi00 = np.kron(s0, s0)
    chi11 = (np.kron(t_p, t_m) - np.kron(t_0, t_0) + np.kron(t_m, t_p)) / np.sqrt(3.0)

    w01, w23 = np.array([np.sqrt(2.0), 0.0, 0.0]), np.array([0.0, np.sqrt(2.0), 0.0])
    w02 = np.array([+1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0), 1.0])
    w03 = np.array([+1.0 / np.sqrt(2.0), +1.0 / np.sqrt(2.0), 1.0])
    w12 = np.array([-1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0), 1.0])
    w13 = np.array([-1.0 / np.sqrt(2.0), +1.0 / np.sqrt(2.0), 1.0])
    a_swirl = np.array([1.0, 1.0, 0.0])

    q_cm = np.diag([0.5, 0.0, 0.25])
    q_pp = np.diag([2.0, 0.0, 0.0])
    q_nn = np.diag([0.0, 2.0, 0.0])
    q_pn = np.diag([0.5, 0.5, 1.0])

    p1_01, p0_01, s_01 = pair_spin_ops(sigs4, 0, 1)
    p1_23, p0_23, s_23 = pair_spin_ops(sigs4, 2, 3)
    p1_02, p0_02, s_02 = pair_spin_ops(sigs4, 0, 2)
    p1_03, p0_03, s_03 = pair_spin_ops(sigs4, 0, 3)
    p1_12, p0_12, s_12 = pair_spin_ops(sigs4, 1, 2)
    p1_13, p0_13, s_13 = pair_spin_ops(sigs4, 1, 3)
    xi_02 = np.einsum("abst,t->abs", s_02, chi00)
    xi_11 = np.einsum("abst,t->abs", s_02, chi11)
    mats_w = [np.outer(w, w) for w in [w01, w23, w02, w03, w12, w13]]

    def make_a6(rs):
        return sum(mw / (r ** 2) for r, mw in zip(rs, mats_w))

    basis = []
    for r_pn in np.geomspace(0.95, 6.20, 6):
        basis += [
            {"L": 0, "chi": chi00, "A": make_a6([r_pn] * 6)},
            {"L": 0, "chi": chi00, "A": make_a6([1.15*r_pn, 0.90*r_pn, r_pn, r_pn, r_pn, r_pn])},
            {"L": 0, "chi": chi00, "A": make_a6([0.90*r_pn, 1.15*r_pn, r_pn, r_pn, r_pn, r_pn])},
        ]
    key_orbits = [(1, 0, 0, 0, 0, 0), (0, 1, 0, 0, 0, 0), (0, 0, 1, 0, 0, 0),
                  (1, 1, 0, 0, 0, 0), (0, 0, 1, 1, 0, 0), (0, 0, 1, 0, 0, 1),
                  (1, 0, 1, 0, 0, 0), (0, 1, 1, 0, 0, 0), (1, 1, 1, 1, 1, 1)]
    for r_env in np.geomspace(1.45, 3.60, 3):
        for r_h in np.geomspace(0.42, 0.78, 2):
            for flags in key_orbits:
                basis.append({"L": 0, "chi": chi00, "A": make_a6([r_h if f else r_env for f in flags])})
    for r_sh in np.geomspace(0.55, 1.85, 3):
        for r_cr in np.geomspace(1.60, 5.00, 3):
            rs_dd = [r_cr, r_cr, r_sh, r_cr, r_cr, r_sh]
            basis += [
                {"L": 0, "chi": chi00, "A": make_a6(rs_dd)},
                {"L": 0, "chi": chi11, "A": make_a6(rs_dd)},
                {"L": 0, "chi": chi00, "A": make_a6([r_cr, r_sh, r_cr, r_cr, r_sh, r_sh])},
                {"L": 0, "chi": chi00, "A": make_a6([r_sh, r_cr, r_cr, r_sh, r_cr, r_sh])},
            ]
    for r_id in np.geomspace(0.80, 3.60, 4):
        for r_pn in np.geomspace(0.90, 3.90, 4):
            basis.append({"L": 2, "a": a_swirl, "Xi": xi_02,
                          "A": make_a6([r_id, r_id, r_pn, r_pn, r_pn, r_pn])})
    for r_t in np.geomspace(0.48, 2.40, 4):
        for r_bg in np.geomspace(1.45, 4.20, 3):
            basis.append({"L": 2, "a": w02, "Xi": xi_02,
                          "A": make_a6([r_bg, r_bg, r_t, r_bg, r_bg, r_bg])})
        for r_sh2 in np.geomspace(0.95, 1.85, 2):
            rs_2 = [2.0, 2.0, r_t, 2.0, 2.0, r_sh2]
            basis += [{"L": 2, "a": w02, "Xi": xi_02, "A": make_a6(rs_2)},
                      {"L": 2, "a": w02, "Xi": xi_11, "A": make_a6(rs_2)}]

    u01, u23 = qubit_swap(4, 0, 1), qubit_swap(4, 2, 3)
    perms = [(+1.0, np.eye(3), np.eye(16, dtype=np.complex128)),
             (-1.0, np.diag([-1.0, +1.0, +1.0]), u01),
             (-1.0, np.diag([+1.0, -1.0, +1.0]), u23),
             (+1.0, np.diag([-1.0, -1.0, +1.0]), u01 @ u23)]
    edges = [(w01, "V1_pp", "V0_pp", None, p1_01, p0_01, s_01),
             (w23, "V1_nn", "V0_nn", None, p1_23, p0_23, s_23),
             (w02, "VC_pn", "V0_pn", "VT_pn", p1_02, p0_02, s_02),
             (w03, "VC_pn", "V0_pn", "VT_pn", p1_03, p0_03, s_03),
             (w12, "VC_pn", "V0_pn", "VT_pn", p1_12, p0_12, s_12),
             (w13, "VC_pn", "V0_pn", "VT_pn", p1_13, p0_13, s_13)]
    q_list = [q_cm, q_pp, q_nn, q_pn]
    e0, pd, q_evs = solve_cg_pure_2b(3, HB2_2M0, basis, perms, edges, q_list, sog_bank)
    return (e0, float(np.sqrt(max(0.0, q_evs[0] + r2_ep + r2_en))), pd,
            float(np.sqrt(q_evs[1])), float(np.sqrt(q_evs[3])), float(np.sqrt(q_evs[2])))


def calibrate_a2_and_run_quantum_cg(sc, mu_p, mu_n, r2_ep, re2_n):
    d_grid = np.concatenate([np.linspace(0.04, 3.20, 44), np.linspace(3.40, 12.50, 16)])
    ch = build_two_body_channels(d_grid, sc)
    m0_pn1, m2_pn1, s0_pn1, b0_pn1 = ch["pn1"]

    rf_cal = np.linspace(0.03, 16.0, 320)
    s0_rf = np.interp(rf_cal, d_grid, s0_pn1, right=0.0)
    m0_rf = np.interp(rf_cal, d_grid, m0_pn1, right=0.0)
    b0_rf = np.interp(rf_cal, d_grid, b0_pn1, right=0.0)
    m2_rf = np.interp(rf_cal, d_grid, m2_pn1, left=0.0, right=0.0)

    def eval_deut_fast(lam, xi, c_b, only_e=False):
        gs, gm = (1.0 - xi) * lam, xi * lam
        gb = c_b * lam * (R_C0 ** 3)
        return solve_deuteron_banded(
            rf_cal, -gs * s0_rf - gm * m0_rf + gb * b0_rf,
            -2.5 * gm * m2_rf, r2_ep, re2_n, mu_p, mu_n, only_e=only_e
        )

    def fit_lam_fast(xi, c_b):
        lo, hi = 15.0, 350.0
        while eval_deut_fast(hi, xi, c_b, True) > -2.22457 and hi < 2e5:
            lo, hi = hi, hi * 2.5
        return float(brentq(
            lambda lm: eval_deut_fast(lm, xi, c_b, True) + 2.22457, lo, hi, xtol=1e-3
        ))

    def fit_xi_fast(c_b):
        def q_res(x):
            return eval_deut_fast(fit_lam_fast(x, c_b), x, c_b, False)[2] - 0.2859

        xs = np.linspace(0.12, 0.94, 9)
        fs = [q_res(x) for x in xs]
        for i in range(len(xs) - 1):
            if fs[i] * fs[i + 1] <= 0.0:
                return float(brentq(q_res, xs[i], xs[i + 1], xtol=1e-3))
        return float(xs[int(np.argmin(np.abs(fs)))])

    cb_pts = np.geomspace(0.35, 5.00, 7)
    rd_res = [eval_deut_fast(fit_lam_fast(fit_xi_fast(c), c), fit_xi_fast(c), c, False)[1]
              - 2.1280 for c in cb_pts]
    cb_cal = float(cb_pts[int(np.argmin(np.abs(rd_res)))])
    for i in range(len(cb_pts) - 1):
        if rd_res[i] * rd_res[i + 1] <= 0.0:
            cb_cal = float(brentq(
                lambda c: eval_deut_fast(
                    fit_lam_fast(fit_xi_fast(c), c), fit_xi_fast(c), c, False
                )[1] - 2.1280,
                cb_pts[i], cb_pts[i + 1], xtol=1e-2
            ))
            break

    xi_cal = fit_xi_fast(cb_cal)
    lam_cal = fit_lam_fast(xi_cal, cb_cal)
    g_s = (1.0 - xi_cal) * lam_cal
    g_m = xi_cal * lam_cal
    g_b = cb_cal * lam_cal * (R_C0 ** 3)
    ed_fd, rd_fd, qd_fd, pd_fd, eta_fd, mud_mod = eval_deut_fast(
        lam_cal, xi_cal, cb_cal, False
    )
    mu_isos_emp = 2.792847 - 1.913043
    mud_emp = mu_isos_emp - 1.5 * (mu_isos_emp - 0.5) * (pd_fd / 100.0)

    m0_pn0, _, s0_pn0, b0_pn0 = ch["pn0"]
    m0_nn0, _, s0_nn0, b0_nn0 = ch["nn0"]
    m0_pp0, _, s0_pp0, b0_pp0 = ch["pp0"]
    m0_nn1, _, s0_nn1, b0_nn1 = ch["nn1"]
    m0_pp1, _, s0_pp1, b0_pp1 = ch["pp1"]

    r_sc = np.linspace(0.04, 16.0, 700)

    def inv_anp_res(c_val):
        v_interp = np.interp(r_sc, d_grid, (-g_s + c_val) * s0_pn0 - g_m * m0_pn0 + g_b * b0_pn0)
        return 1.0 / scatt_obs(r_sc, v_interp, HB2_2MU_NP)[0] + 1.0 / 23.74

    cfb = safe_root(inv_anp_res, -25.0, 75.0, n_scan=70, pole_cut=2.5)

    v_coul = ALPHA * HBAR_C / np.sqrt(d_grid ** 2 + r2_ep)
    v0_pn = (-g_s + cfb) * s0_pn0 - g_m * m0_pn0 + g_b * b0_pn0
    v0_nn = (-g_s + cfb) * s0_nn0 - g_m * m0_nn0 + g_b * b0_nn0
    v0_pp = (-g_s + cfb) * s0_pp0 - g_m * m0_pp0 + g_b * b0_pp0
    _, r0_np = scatt_obs(r_sc, np.interp(r_sc, d_grid, v0_pn), HB2_2MU_NP)
    a_nn, _ = scatt_obs(r_sc, np.interp(r_sc, d_grid, v0_nn), HB2_2MU_NN)
    a_pp, _ = scatt_obs(r_sc, np.interp(r_sc, d_grid, v0_pp), HB2_2MU_NN)

    bank = SOGPotentialBank(d_grid, {
        "VC_pn": -g_s * s0_pn1 - g_m * m0_pn1 + g_b * b0_pn1,
        "VT_pn": -2.5 * g_m * m2_pn1, "V0_pn": v0_pn,
        "V0_nn": v0_nn, "V0_pp": v0_pp + v_coul,
        "V1_nn": -g_s * s0_nn1 - g_m * m0_nn1 + g_b * b0_nn1,
        "V1_pp": -g_s * s0_pp1 - g_m * m0_pp1 + g_b * b0_pp1 + v_coul,
    }, zero_at_origin=("VT_pn",))
    ed_cg, _, _ = run_deuteron_cg_check(bank, r2_ep, re2_n)
    e3h, r3h, _ = run_a3_pure_2b(1, bank, r2_ep, re2_n)
    e3he, r3he, _ = run_a3_pure_2b(2, bank, r2_ep, re2_n)
    e4, r4, pd4, dpp, dpn, dnn = run_a4_pure_2b(bank, r2_ep, re2_n)

    print("\n=== 4. PURE TWO-BODY A=2,3,4 QUANTUM LEDGER (De=3 r_pi & G'(r) CUTOFF) ===",
          flush=True)
    print(f"  Couplings: g_S={g_s:.2f}, g_M={g_m:.2f} MeV/fm, "
          f"g_B={g_b:.2f} MeV*fm^2, c_FB={cfb:+.2f} MeV/fm")
    print(f"  Unweighted 28-Gaussian SOG Fit Worst-Case RMS Residual = {bank.max_rms_err:.4f} MeV")
    print("  Observable                   | Computed          | Exp_Ref           | Status")
    print(f"  2H  E_d (1D / 3D CG) [MeV]   | {ed_fd:+7.3f} / {ed_cg:+7.3f} | "
          "-2.22457          | Calibrated A=2")
    print(f"  2H  Q_d [fm^2] & r_d [fm]    | {qd_fd:+7.4f} / {rd_fd:7.3f} | "
          "+0.2859 / 2.128   | Calibrated A=2")
    print(f"  2H  eta_D/S & P_D [%]        | {eta_fd:+7.4f} / {pd_fd:6.2f}% | "
          "+0.0256(4) / ~5%  | Untuned prediction")
    print(f"  2H  mu_d (mod / emp u_p,n)   | {mud_mod:+7.4f} / {mud_emp:+7.4f} | "
          "+0.85744 u_N      | Untuned D-wave check")
    print(f"  1S0 a_pp(strong) & r_0s [fm] | {a_pp:+7.1f} / {r0_np:7.2f} | "
          "-17.3 / 2.75      | De(r) G' range check")
    print(f"  1S0 a_np (cal) & a_nn [fm]   |  -23.74 / {a_nn:+7.1f} | "
          "-23.74 / -18.9    | Universal Phi_0 check")
    print(f"  3H  Triton E [MeV] (r_E)     | {e3h:+7.3f} ({r3h:5.3f})   | "
          "-8.482 (1.759)    | Pure 2N (3N open)")
    print(f"  3He Helion E [MeV] (r_E)     | {e3he:+7.3f} ({r3he:5.3f})   | "
          f"-7.718 (1.966)    | Split={e3he-e3h:+.3f} MeV")
    print(f"  4He Alpha  E [MeV] (r_E)     | {e4:+7.3f} ({r4:5.3f})   | "
          f"-28.296 (1.676)   | Pure 2N, PD={pd4:.1f}%")
    print(f"  4He RMS Pair (d_pp,d_nn,d_pn)| ({dpp:.3f},{dnn:.3f},{dpn:.3f}) | "
          "d_pp > d_nn > d_pn| Unbiased CG basis", flush=True)
    return g_s, g_m, g_b, cfb

# === END OF PART 1 OF 2 (Paste Part 2 directly below this line) ===

# ======================================================================
# trefoil_nuclear_master_suite.py  [PART 2 OF 2 — V3.2 UNIFIED EDITION]
# Sections 2 & 5-10: 4-Mode Kelvin BEM, Two-Body Contact Spectrum,
# Degree-1 Relays, Exact-Contact A=3..16O & 11Li, & Continuum Checks
# ======================================================================

N_S_MULTI = 36
N_TAU_MULTI = 6


def run_sec2_kelvin_bem(st_p, st_n, sc):
    mt_n, mb_n, mff_n, mn_n, err23_n = solve_kelvin_bem_and_check_eq23(
        st_n, sc["rst_n"], 180
    )
    mt_p, mb_p, mff_p, mn_p, err23_p = solve_kelvin_bem_and_check_eq23(
        st_p, sc["rst_p_act"], 180
    )
    s111_ratio = mn_p[3] / mn_n[3]
    d3_leak = max(
        abs(mt_n[2]), abs(mt_n[3]), abs(mb_n[2]), abs(mb_n[3]),
        abs(mn_n[0]), abs(mn_n[1]), abs(mn_p[0]), abs(mn_p[1]),
    )
    throt_err = abs((1.0 - 2.0 * NU_ELAST) / (1.0 - NU_ELAST) - 2.0 * ALPHA)
    anapole_np = ((sc["rmax_n"] / sc["rmax_p"]) ** 3) * (B_U_N / B_U_P)

    print("\n=== 2. KELVIN 1/r^2 BEM MULTIPOLES (ALL 4 MODES) & FAR-FIELD CHECK ===",
          flush=True)
    print(f"  Mode 1 Tangential (T) : p+(F={mt_p[0]:+.3f}, T={mt_p[1]:+.3f}) | "
          f"n0(F={mt_n[0]:+.3f}, T={mt_n[1]:+.3f})")
    print(f"  Mode 2 Binormal   (B) : p+(F={mb_p[0]:+.3f}, T={mb_p[1]:+.3f}) | "
          f"n0(F={mb_n[0]:+.3f}, T={mb_n[1]:+.3f})")
    print(f"  Mode 3 Force-Free (FF): p+(chi={mff_p[0]:+6.2f} deg, T_FF={mff_p[2]:+.4f}) | "
          f"n0(chi={mff_n[0]:+6.2f} deg, T_FF={mff_n[2]:+.4f})")
    print(f"  Mode 4 Cavitation (N) : p+(D_0={mn_p[2]:+.4f}, S_111={mn_p[3]:+.4f}) | "
          f"n0(D_0={mn_n[2]:+.4f}, S_111={mn_n[3]:+.4f}) [p/n={s111_ratio:.2f}x]")
    print(f"  Exact Identities      : Eq.(23) err(n,p)=({err23_n:.2e},{err23_p:.2e}), "
          f"D_3 leak={d3_leak:.2e}, |throt-2a|={throt_err:.2e}, "
          f"Anapole(n/p)={anapole_np:.4f}x", flush=True)


# ======================================================================
# SECTION 5: ALIGNED 1D-TO-3D TUBE COORDINATE PROFILES (s_a in [0, L_a))
# ======================================================================
def print_two_tube_1d_strip(title, ip1, ip2, c1, c2, rm1, rm2, sc, n_s=360):
    b1, l1, rt1 = (
        (B_U_P, sc["l_p"], sc["r_tp"]) if ip1 else (B_U_N, sc["l_n"], sc["r_tn"])
    )
    b2, l2, rt2 = (
        (B_U_P, sc["l_p"], sc["r_tp"]) if ip2 else (B_U_N, sc["l_n"], sc["r_tn"])
    )
    s1, ph1, r1_0, t1_0, _ = build_local_arclength_tube(b1, l1, n_s)
    s2, ph2, r2_0, t2_0, _ = build_local_arclength_tube(b2, l2, n_s)
    r1, t1 = c1[None, :] + (r1_0 @ rm1.T), t1_0 @ rm1.T
    r2, t2 = c2[None, :] + (r2_0 @ rm2.T), t2_0 @ rm2.T

    d_mat = np.linalg.norm(r1[:, None, :] - r2[None, :, :], axis=-1)
    d2_reg = (d_mat ** 2) + (rt1 ** 2) + (rt2 ** 2)
    d12_reg = np.sqrt(d2_reg)
    g_de = (R_E ** 2) / (d2_reg + (R_E ** 2))
    td_mat = t1 @ t2.T
    ds1, ds2 = l1 / n_s, l2 / n_s
    m1_line = np.sum(
        td_mat * g_de * np.exp(-d12_reg / R_PI) / d12_reg, axis=1
    ) * ds2 / (4.0 * np.pi)
    m1_tot = float(np.sum(m1_line) * ds1)

    i0, j0 = np.unravel_index(int(np.argmin(d_mat)), d_mat.shape)
    print(f"\n  --- {title} (M_1pi={m1_tot:+.4f} fm, "
          f"d_min={d_mat[i0, j0]:.4f} >= {rt1+rt2:.4f} fm) ---")
    print("  s1[fm] phi1  | Tube-1 3D (x,y,z) [fm]   | "
          "Closest T2: s2(phi2)  d_min  T1.T2 | d_max | M1pi(s1)")
    step = n_s // 12
    for k in range(0, n_s, step):
        jl, jh = int(np.argmin(d_mat[k])), int(np.argmax(d_mat[k]))
        x1, y1, z1 = r1[k]
        print(f"  {s1[k]:5.3f} {ph1[k]:5.1f} | ({x1:+5.2f},{y1:+5.2f},{z1:+5.2f}) | "
              f" {s2[jl]:5.2f}({ph2[jl]:5.1f}) {d_mat[k, jl]:5.3f} {td_mat[k, jl]:+6.3f} | "
              f"{d_mat[k, jh]:5.3f} | {m1_line[k]:+6.3f}")


def run_sec5_aligned_1d_strips(sc, d_cat, del_cat):
    ey, ez = np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])
    d_pn = d_cat["coax_s1"]["pn"]
    dl_pn = del_cat["coax_s1"]["pn"]
    d_pp = d_cat["eq_s0"]["pp"]
    dl_pp = del_cat["eq_s0"]["pp"]
    dl_nn = del_cat["eq_s0"]["nn"]

    print("\n=== 5. ALIGNED 1D-TO-3D TUBE COORDINATE PROFILES (s_a in [0, L_a)) ===",
          flush=True)
    print_two_tube_1d_strip(
        f"5A. Coaxial C3 Triplet p-n at d*={d_pn:.3f} fm, dphi={np.rad2deg(dl_pn):.1f} deg",
        True, False, np.array([0., 0., -0.5 * d_pn]), np.array([0., 0., +0.5 * d_pn]),
        frame_from_z_and_ref(+ez, ey, 0.0), frame_from_z_and_ref(+ez, ey, dl_pn), sc
    )
    print_two_tube_1d_strip(
        f"5B. Equatorial Singlet p-p at d*={d_pp:.3f} fm, dphi={np.rad2deg(dl_pp):.1f} deg",
        True, True, np.array([0., -0.5 * d_pp, 0.]), np.array([0., +0.5 * d_pp, 0.]),
        frame_from_z_and_ref(+ez, -ey, 0.0), frame_from_z_and_ref(-ez, +ey, dl_pp), sc
    )
    print_two_tube_1d_strip(
        f"5C. Equatorial Singlet n-n at Same d={d_pp:.3f} fm, dphi={np.rad2deg(dl_nn):.1f} deg",
        False, False, np.array([0., -0.5 * d_pp, 0.]), np.array([0., +0.5 * d_pp, 0.]),
        frame_from_z_and_ref(+ez, -ey, 0.0), frame_from_z_and_ref(-ez, +ey, dl_nn), sc
    )


# ======================================================================
# SECTION 6: SYNCHRONOUS TWO-BODY CONTACT SPECTRUM (21 DEGREE-0 MODES)
# ======================================================================
def run_sec6_contact_spectrum(sc, couplings):
    """Solves all 21 synchronous Degree-0 modes with De(r) G' storage cutoff."""
    g_s, g_m, g_b, cfb, r2_ep = couplings
    _, _, rp0, tp0, _ = build_local_arclength_tube(B_U_P, sc["l_p"], N_S_MULTI)
    _, _, rn0, tn0, _ = build_local_arclength_tube(B_U_N, sc["l_n"], N_S_MULTI)
    dsp_seg, dsn_seg = sc["l_p"] / N_S_MULTI, sc["l_n"] / N_S_MULTI

    ex, ey, ez = np.eye(3)
    ax_p = np.array([-1.0, +1.0, 0.0]) / np.sqrt(2.0)
    ax_n = np.array([+1.0, +1.0, 0.0]) / np.sqrt(2.0)
    bp_in = np.array([-1.0, -1.0, 0.0]) / np.sqrt(2.0)
    bn_in = np.array([-1.0, +1.0, 0.0]) / np.sqrt(2.0)
    u_disp = np.array([0.0, -1.0, -1.0]) / np.sqrt(2.0)
    s_tet2 = np.array([2.0 * np.sqrt(2.0) / 3.0, 0.0, -1.0 / 3.0])
    u_tet = np.array([np.sqrt(2.0 / 3.0), 0.0, np.sqrt(1.0 / 3.0)])

    orientations = [
        ("coax_s1", "1. Coaxial C3 Triplet (S=1)", ez,   ey,    ez,     ey,    ez,     1.0, "2 axial polar"),
        ("coax_s0", "2. Coaxial Singlet    (S=0)", ez,   ey,   -ez,     ey,    ez,     0.0, "2 axial polar"),
        ("eq_s0",   "3. Equatorial Singlet (S=0)", ez,  -ey,   -ez,     ey,    ey,     0.0, "6 equatorial "),
        ("eq_s1",   "4. Equatorial Triplet (S=1)", ez,  -ey,    ez,     ey,    ey,     1.0, "6 equatorial "),
        ("bev_90",  "5. Orthogonal Skew-Bevel   ", ax_p, bp_in, ax_n,   bn_in, u_disp, 0.5, "4 skew 90-deg"),
        ("pol_eq",  "6. Polar-Equatorial Ortho. ", ez,   ex,    ex,    -ez,    ez,     0.5, "6 ortho 90   "),
        ("tet_109", "7. Tetrahedral 109.5 Cpl.  ", ez,   ex,    s_tet2, ey,    u_tet,  1/3, "4 skew 109.5 "),
    ]

    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, N_TAU_MULTI, endpoint=False)
    del_grid = np.linspace(0.0, 2.0 * np.pi / 3.0, 12, endpoint=False)
    iu_2, ju_2 = np.array([0]), np.array([1])
    d_opt_catalog, del_opt_catalog = {}, {}

    print("\n=== 6. SYNCHRONOUS TWO-BODY CONTACT SPECTRUM (21 DEGREE-0 MODES) ===",
          flush=True)
    print("  Symmetry Sites: 2 Axial Polar + 6 Equatorial (3 Apices + 3 Troughs) + 4 Skew = 12")
    print("  Coupling Mode               | Symmetry Zone | Pair | P_S1 | "
          "d_touch  d*(sync)  d_min(d*) | M_1pi(d*) | V_sync[MeV]")
    print("  " + "-" * 110)

    for key, oname, s1, rf1, s2, rf2, ub, p_s1, zone in orientations:
        d_opt_catalog[key], del_opt_catalog[key] = {}, {}
        s_dot = float(np.dot(s1 / np.linalg.norm(s1), s2 / np.linalg.norm(s2)))
        ub_u = ub / np.linalg.norm(ub)
        u_pair = np.array([[0.0, 0.0, 0.0], ub_u])

        for p_lbl, (ip1, ip2) in [("pn", (True, False)), ("nn", (False, False)), ("pp", (True, True))]:
            r1_0, t1_0, ds1, rt1 = (
                (rp0, tp0, dsp_seg, sc["r_tp"]) if ip1 else (rn0, tn0, dsn_seg, sc["r_tn"])
            )
            r2_0, t2_0, ds2, rt2 = (
                (rp0, tp0, dsp_seg, sc["r_tp"]) if ip2 else (rn0, tn0, dsn_seg, sc["r_tn"])
            )
            r_cut = rt1 + rt2
            sig2_ij = (rt1 ** 2) + (rt2 ** 2)
            fac = (ds1 * ds2) / (4.0 * np.pi * N_TAU_MULTI)

            ra_t = np.array([r1_0 @ frame_from_z_and_ref(s1, rf1, t).T for t in taus])
            ta_t = np.array([t1_0 @ frame_from_z_and_ref(s1, rf1, t).T for t in taus])

            def min_v_for_delta(dl_val):
                rb_t = np.array([r2_0 @ frame_from_z_and_ref(s2, rf2, t + dl_val).T for t in taus])
                tb_t = np.array([t2_0 @ frame_from_z_and_ref(s2, rf2, t + dl_val).T for t in taus])
                r_loc = np.stack([ra_t, rb_t], axis=1)
                dt_ex = exact_steric_contact_scale(u_pair, r_loc, iu_2, ju_2, r_cut) * (1.0 + 1e-12)
                tdot = np.einsum("tik,tjk->tij", ta_t, tb_t)

                def v_of_d(dv):
                    df = ra_t[:, :, None, :] - (dv * ub_u[None, None, None, :] + rb_t[:, None, :, :])
                    raw_d2 = np.sum(df ** 2, axis=-1)
                    d_min_v = float(np.sqrt(np.min(raw_d2)))
                    d2 = raw_d2 + sig2_ij
                    d12 = np.sqrt(d2)
                    g_de = (R_E ** 2) / (d2 + (R_E ** 2))
                    s2v = float(np.sum(g_de * np.exp(-d12 / R_2PI) / d12)) * fac
                    m1v = float(np.sum(tdot * g_de * np.exp(-d12 / R_PI) / d12)) * fac
                    b4v = float(np.sum(1.0 / (d2 ** 2))) * fac
                    vc = (ALPHA * HBAR_C / np.sqrt(dv ** 2 + r2_ep)) if (ip1 and ip2) else 0.0
                    v_tot = (-g_s + cfb * max(0.0, -s_dot)) * s2v - g_m * m1v + g_b * b4v + vc
                    return v_tot, m1v, d_min_v

                res_d = minimize_scalar(lambda d: v_of_d(d)[0], bounds=(dt_ex, 4.50), method="bounded")
                v_int, m_int, dm_int = v_of_d(float(res_d.x))
                v_bnd, m_bnd, dm_bnd = v_of_d(dt_ex)
                if v_bnd <= v_int:
                    return v_bnd, dt_ex, dt_ex, m_bnd, dm_bnd
                return v_int, float(res_d.x), dt_ex, m_int, dm_int

            cand = [min_v_for_delta(dl)[0] for dl in del_grid]
            dl0 = del_grid[int(np.argmin(cand))]
            step_dl = 2.0 * np.pi / (3.0 * len(del_grid))
            res_dl = minimize_scalar(
                lambda dl: min_v_for_delta(dl)[0],
                bounds=(dl0 - step_dl, dl0 + step_dl), method="bounded"
            )
            best_dl = float(np.mod(res_dl.x, 2.0 * np.pi / 3.0))

            v_sync, d_sync, d_touch, m1_sync, dmin_sync = min_v_for_delta(best_dl)
            d_opt_catalog[key][p_lbl] = d_sync
            del_opt_catalog[key][p_lbl] = best_dl

            p_disp = f"{p_lbl[0]}-{p_lbl[1]}"
            print(f"  {oname} | {zone} | {p_disp}  | {p_s1:4.2f} | "
                  f" {d_touch:5.3f}    {d_sync:5.3f}     {dmin_sync:6.4f}  | "
                  f" {m1_sync:+7.4f}  |   {v_sync:+7.2f}")
    return d_opt_catalog, del_opt_catalog


# ======================================================================
# SECTION 7: DEGREE-1 SEPARATED RELAY COUPLINGS (A --- {C} --- B)
# ======================================================================
def eval_cycle_pair_3d(ip1, c1, rf1, s1, g1, ip2, c2, rf2, s2, g2,
                       p_base, n_base, sc, couplings, n_tau=N_TAU_MULTI):
    g_s, g_m, g_b, cfb, r2_ep = couplings
    r1_0, t1_0, l1, rt1 = (
        (p_base[2], p_base[3], sc["l_p"], sc["r_tp"]) if ip1
        else (n_base[2], n_base[3], sc["l_n"], sc["r_tn"])
    )
    r2_0, t2_0, l2, rt2 = (
        (p_base[2], p_base[3], sc["l_p"], sc["r_tp"]) if ip2
        else (n_base[2], n_base[3], sc["l_n"], sc["r_tn"])
    )

    n_s = len(r1_0)
    ds1, ds2 = l1 / n_s, l2 / n_s
    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, n_tau, endpoint=False)

    d_cm = float(np.linalg.norm(c2 - c1))
    s_dot = float(np.dot(s1 / np.linalg.norm(s1), s2 / np.linalg.norm(s2)))
    sig2_ij = (rt1 ** 2) + (rt2 ** 2)
    v_coul = (ALPHA * HBAR_C / np.sqrt(d_cm ** 2 + r2_ep)) if (ip1 and ip2) else 0.0

    ra_t = np.array([c1[None, :] + (r1_0 @ frame_from_z_and_ref(s1, rf1, g1 + t).T) for t in taus])
    ta_t = np.array([t1_0 @ frame_from_z_and_ref(s1, rf1, g1 + t).T for t in taus])
    rb_t = np.array([c2[None, :] + (r2_0 @ frame_from_z_and_ref(s2, rf2, g2 + t).T) for t in taus])
    tb_t = np.array([t2_0 @ frame_from_z_and_ref(s2, rf2, g2 + t).T for t in taus])

    diff = ra_t[:, :, None, :] - rb_t[:, None, :, :]
    raw_d2 = np.sum(diff ** 2, axis=-1)
    d_min_cyc = float(np.sqrt(np.min(raw_d2)))
    d2 = raw_d2 + sig2_ij
    d12 = np.sqrt(d2)
    g_de = (R_E ** 2) / (d2 + (R_E ** 2))
    tdot = np.einsum("tik,tjk->tij", ta_t, tb_t)

    s_ker = g_de * np.exp(-d12 / R_2PI) / (4.0 * np.pi * d12)
    m_ker = tdot * g_de * np.exp(-d12 / R_PI) / (4.0 * np.pi * d12)
    k_s = -g_s * s_ker
    k_m = -g_m * m_ker
    k_b = g_b / (4.0 * np.pi * (d2 ** 2))
    k_cfb = cfb * max(0.0, -s_dot) * s_ker
    k_tot = k_s + k_m + k_b + k_cfb + (v_coul / (l1 * l2))

    eps1 = np.sum(k_tot, axis=(0, 2)) * (ds2 / n_tau)
    eps2 = np.sum(k_tot, axis=(0, 1)) * (ds1 / n_tau)

    fac = (ds1 * ds2) / n_tau
    m1_v = float(np.sum(m_ker)) * fac
    vs_v = float(np.sum(k_s)) * fac
    vm_v = float(np.sum(k_m)) * fac
    vb_v = float(np.sum(k_b)) * fac
    vcfb_v = float(np.sum(k_cfb)) * fac
    v_raw = vs_v + vm_v + vb_v + vcfb_v + v_coul
    return (d_cm, d_min_cyc, m1_v, vs_v, vm_v, vb_v, vcfb_v + v_coul,
            v_raw, eps1, eps2, rt1 + rt2)


def run_sec7_degree1_relays(sc, couplings, d_cat, del_cat):
    p_b = build_local_arclength_tube(B_U_P, sc["l_p"], N_S_MULTI)
    n_b = build_local_arclength_tube(B_U_N, sc["l_n"], N_S_MULTI)
    ey, ez = np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])

    bridges = [
        ("n-{p}-n", False, True,  False), ("p-{n}-p", True,  False, True),
        ("p-{n}-n", True,  False, False), ("n-{p}-p", False, True,  True),
        ("n-{n}-n", False, False, False), ("p-{p}-p", True,  True,  True),
    ]

    def bkey(ia, ib):
        return "pn" if (ia != ib) else ("pp" if ia else "nn")

    dl_coax = 2.0 * del_cat["coax_s1"]["pn"]
    dl_eq = del_cat["eq_s0"]["pn"]
    modes_180 = [
        ("7A. Colinear Axial Relay      (A^ {C^} B^, S_AB=1)", ez, d_cat["coax_s1"], +ez, +ez, dl_coax),
        ("7B. Colinear Equatorial Relay (A^ {Cv} B^, S_AB=1)", ey, d_cat["eq_s0"],   +ez, +ez, 0.0),
        ("7C. Polar-Equatorial Relay    (A^ {C>} Bv, S_AB=0)", ey, d_cat["pol_eq"],  +ez, -ez, dl_eq),
    ]

    print("\n=== 7. DEGREE-1 (A --- {C} --- B, {C} REMOVED) CONTINUUM RELAY SPECTRUM ===",
          flush=True)
    for m_lbl, u_ax, d_tab, s_a, s_b, g_b in modes_180:
        print(f"\n  --- {m_lbl} ---")
        print("  Bridge  | D_AB[fm]  d_min(cyc) |   M_1pi  |  V_S2pi   V_M1pi  V_B4+C | V_sync[MeV]")
        for bl, ip_a, ip_c, ip_b in bridges:
            d1, d2 = d_tab[bkey(ip_a, ip_c)], d_tab[bkey(ip_c, ip_b)]
            res = eval_cycle_pair_3d(ip_a, -d1 * u_ax, ey, s_a, 0.0,
                                     ip_b, +d2 * u_ax, ey, s_b, g_b,
                                     p_b, n_b, sc, couplings)
            print(f"  {bl} |  {res[0]:6.3f}     {res[1]:6.3f}   | {res[2]:+7.4f}  | "
                  f"{res[3]:+7.2f}  {res[4]:+7.2f} {res[5]+res[6]:+7.2f} |   {res[7]:+7.2f}")

    d_pol, d_wst = d_cat["coax_s1"]["pn"], d_cat["eq_s0"]["pn"]
    print("\n  --- 7D. Oblique Polar-Equatorial Hinge (S_AB=0, {C} Removed): n-{p}-n vs p-{n}-p ---")
    print("  Theta[deg] | D_AB[fm] | n-{p}-n: d_min   M_1pi   V_sync  Status  | "
          "p-{n}-p: d_min   M_1pi   V_sync  Status")
    for th_d in [180.0, 150.0, 120.0, 109.47, 90.0, 75.0]:
        th = np.deg2rad(th_d)
        ca = np.array([0.0, 0.0, -d_pol])
        cb = np.array([0.0, d_wst * np.sin(th), -d_wst * np.cos(th)])
        rn = eval_cycle_pair_3d(False, ca, ey, +ez, 0.0, False, cb, ey, -ez, dl_eq,
                                p_b, n_b, sc, couplings)
        rp = eval_cycle_pair_3d(True,  ca, ey, +ez, 0.0, True,  cb, ey, -ez, dl_eq,
                                p_b, n_b, sc, couplings)
        sn = "overlap" if rn[1] < rn[10] else "clear  "
        sp = "overlap" if rp[1] < rp[10] else "clear  "
        print(f"    {th_d:6.2f}   |  {rn[0]:6.3f}  |         {rn[1]:5.3f}  {rn[2]:+7.4f}  "
              f"{rn[7]:+7.2f}  {sn} |         {rp[1]:5.3f}  {rp[2]:+7.4f}  {rp[7]:+7.2f}  {sp}")


# ======================================================================
# SECTION 8: EXACT-CONTACT A=3 (3H, 3He) & A=4 (4He, 4n) DECOMPOSITIONS
# ======================================================================
def eval_exact_contact_single_cluster(spec_list, u_xi, p_b, n_b, sc, couplings):
    n_c = len(spec_list)
    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, N_TAU_MULTI, endpoint=False)
    u_vecs = np.array([sp[2] for sp in spec_list], dtype=float)
    u_vecs -= np.mean(u_vecs, axis=0, keepdims=True)
    rt_arr = np.array([sc["r_tp"] if sp[1] else sc["r_tn"] for sp in spec_list])

    r_loc_tau = np.zeros((N_TAU_MULTI, n_c, N_S_MULTI, 3))
    for a, (_, ip_a, _, rf_a, sx_a, gm_a) in enumerate(spec_list):
        r0 = p_b[2] if ip_a else n_b[2]
        for it, tau in enumerate(taus):
            rm = frame_from_z_and_ref(sx_a, rf_a, gm_a + tau)
            r_loc_tau[it, a] = r0 @ rm.T

    iu, ju = np.triu_indices(n_c, k=1)
    r_cuts = rt_arr[iu] + rt_arr[ju]
    xi_touch = exact_steric_contact_scale(u_vecs, r_loc_tau, iu, ju, r_cuts) * (1.0 + 1e-12)
    xi = xi_touch + (u_xi ** 2)

    nodes = [
        (nm, ip, xi * u_vecs[a], rf, sx, gm)
        for a, (nm, ip, _, rf, sx, gm) in enumerate(spec_list)
    ]
    eps = np.zeros((n_c, n_c, N_S_MULTI))
    ledger = {}
    min_clr_fm, min_ratio = 1e9, 1e9
    v_raw_sum = 0.0
    for i in range(n_c):
        ni, ip1, c1, rf1, s1, g1 = nodes[i]
        for j in range(i + 1, n_c):
            nj, ip2, c2, rf2, s2, g2 = nodes[j]
            r = eval_cycle_pair_3d(ip1, c1, rf1, s1, g1, ip2, c2, rf2, s2, g2,
                                   p_b, n_b, sc, couplings)
            min_clr_fm = min(min_clr_fm, r[1])
            min_ratio = min(min_ratio, r[1] / r[10])
            v_raw_sum += r[7]
            eps[i, j], eps[j, i] = r[8], r[9]
            ledger[f"{ni}-{nj}"] = r[:8] + (r[10],)
    return v_raw_sum, min_clr_fm, min_ratio, nodes, ledger, eps


def run_sec8_a3_a4_decompositions(sc, couplings, del_cat):
    p_b = build_local_arclength_tube(B_U_P, sc["l_p"], N_S_MULTI)
    n_b = build_local_arclength_tube(B_U_N, sc["l_n"], N_S_MULTI)
    ey, ez = np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])

    def spec_a3_m1(par, is_triton=True):
        u_y, z_rat, g_a, g_b, u_xi = par
        y_rat = 0.5 + np.exp(np.clip(u_y, -3.0, 3.0))
        ip_o, ip_i = (True, False) if is_triton else (False, True)
        no, na, nb = ("p1", "n1", "n2") if is_triton else ("n1", "p1", "p2")
        specs = [
            (no, ip_o, np.array([0.0, 0.0, -0.5]),   ey, +ez, 0.0),
            (na, ip_i, np.array([0.0, 0.0, +0.5]),   ey, +ez, g_a),
            (nb, ip_i, np.array([0.0, y_rat, z_rat]), ey, -ez, g_b),
        ]
        return specs, u_xi

    x0_a3 = [np.log(1.65), 0.0, del_cat["coax_s1"]["pn"], del_cat["eq_s0"]["pn"], 0.0]
    opt_h3 = minimize(
        lambda x: eval_exact_contact_single_cluster(*spec_a3_m1(x, True), p_b, n_b, sc, couplings)[0],
        x0_a3, method="Nelder-Mead", options={"maxiter": 220}
    )
    opt_he3 = minimize(
        lambda x: eval_exact_contact_single_cluster(*spec_a3_m1(x, False), p_b, n_b, sc, couplings)[0],
        x0_a3, method="Nelder-Mead", options={"maxiter": 220}
    )
    vr_h3, clr_h3, rat_h3, nds_h3, _, _ = eval_exact_contact_single_cluster(
        *spec_a3_m1(opt_h3.x, True), p_b, n_b, sc, couplings
    )
    vr_he3, clr_he3, rat_he3, _, _, _ = eval_exact_contact_single_cluster(
        *spec_a3_m1(opt_he3.x, False), p_b, n_b, sc, couplings
    )

    sp_p = np.array([-1.0, +1.0, 0.0]) / np.sqrt(2.0)
    sp_n = np.array([+1.0, +1.0, 0.0]) / np.sqrt(2.0)
    bp_in = np.array([-1.0, -1.0, 0.0]) / np.sqrt(2.0)
    bn_in = np.array([-1.0, +1.0, 0.0]) / np.sqrt(2.0)

    def spec_disphenoid(par, has_protons=True):
        u_xn, u_z, dl, u_xi = par
        eta_xn = np.exp(np.clip(u_xn, -2.5, 2.5))
        eta_z = np.exp(np.clip(u_z, -2.5, 2.5))
        ip_top = bool(has_protons)
        n_t1, n_t2 = ("p1", "p2") if has_protons else ("n1", "n2")
        n_b1, n_b2 = ("n1", "n2") if has_protons else ("n3", "n4")
        dl_top = del_cat["eq_s0"]["pp" if has_protons else "nn"]
        dl_bot = del_cat["eq_s0"]["nn"]
        specs = [
            (n_t1, ip_top, np.array([+1.0, +1.0, +eta_z]),       +bp_in, +sp_p, 0.0),
            (n_t2, ip_top, np.array([-1.0, -1.0, +eta_z]),       -bp_in, -sp_p, dl_top),
            (n_b1, False,  np.array([+eta_xn, -eta_xn, -eta_z]), +bn_in, +sp_n, dl),
            (n_b2, False,  np.array([-eta_xn, +eta_xn, -eta_z]), -bn_in, -sp_n, dl + dl_bot),
        ]
        return specs, u_xi

    x0_4 = [0.0, np.log(0.65), del_cat["bev_90"]["pn"], 0.0]
    opt_he4 = minimize(
        lambda x: eval_exact_contact_single_cluster(
            *spec_disphenoid(x, True), p_b, n_b, sc, couplings
        )[0],
        x0_4, method="Nelder-Mead", options={"maxiter": 240}
    )
    opt_4n = minimize(
        lambda x: eval_exact_contact_single_cluster(
            *spec_disphenoid(x, False), p_b, n_b, sc, couplings
        )[0],
        x0_4, method="Nelder-Mead", options={"maxiter": 240}
    )
    vr_4, clr_4, rat_4, nds_he4, led_4, eps_4 = eval_exact_contact_single_cluster(
        *spec_disphenoid(opt_he4.x, True), p_b, n_b, sc, couplings
    )
    vr_4n, clr_4n, _, nds_4n, _, _ = eval_exact_contact_single_cluster(
        *spec_disphenoid(opt_4n.x, False), p_b, n_b, sc, couplings
    )

    sp_grid, sn_grid = p_b[0], n_b[0]
    ds_nodes = [sc["l_p"] / N_S_MULTI if nd[1] else sc["l_n"] / N_S_MULTI for nd in nds_he4]
    e_half_4 = [0.5 * np.sum(eps_4[a], axis=0) for a in range(4)]
    sum_4tubes = sum(float(np.sum(e_half_4[a]) * ds_nodes[a]) for a in range(4))

    print("\n=== 8. EXACT-CONTACT A=3 & A=4 STATIC PAIR LEDGERS & 4-TUBE 1D MAP ===",
          flush=True)
    print(f"  3H  Polar-Eq. Triangle : V_2N={vr_h3:+.2f} MeV, min_d12={clr_h3:.4f} fm "
          f"(d/(r_i+r_j)={rat_h3:.4f})")
    print(f"  3He Polar-Eq. Triangle : V_2N={vr_he3:+.2f} MeV, min_d12={clr_he3:.4f} fm "
          f"(d/(r_i+r_j)={rat_he3:.4f}) | 4n-Disph: {vr_4n:+.2f} MeV ({clr_4n:.4f} fm)")
    print(f"\n  --- 4He C_2v Disphenoid 6-Pair Ledger (V_2N={vr_4:+.2f} MeV, "
          f"min d/(r_i+r_j)={rat_4:.4f}) ---")
    print("  Pair  | d_cm  d_min  r_i+r_j |  V_S2pi   V_M1pi    V_B4  V_cFB+C |  V_pair   Share")
    for pk, v in led_4.items():
        print(f"  {pk:5s} | {v[0]:4.2f}  {v[1]:6.4f}  {v[8]:6.4f} | {v[3]:+7.2f}  {v[4]:+7.2f} "
              f"{v[5]:+7.2f}  {v[6]:+6.2f} | {v[7]:+7.2f}  {100.0 * v[7] / vr_4:5.1f}%")
    print(f"  4-Tube <-> 6-Pair Identity: Sum_4_tubes={sum_4tubes:+.4f} MeV vs {vr_4:+.4f} MeV "
          f"(diff={abs(sum_4tubes - vr_4):.2e})")

    print("\n  --- Proton-1 (L_p) & Neutron-1 (L_n) 1D Line-Density Profiles in 4He [MeV/fm] ---")
    print("  s_p/s_n[fm] | p1: eps(p2) eps(n1) eps(n2) -> E_p1(s) | "
          "n1: eps(p1) eps(p2) eps(n2) -> E_n1(s)")
    for k in range(0, N_S_MULTI, 3):
        print(f"  {sp_grid[k]:4.2f}/{sn_grid[k]:4.2f}   |    "
              f"{eps_4[0,1,k]:+7.2f} {eps_4[0,2,k]:+7.2f} {eps_4[0,3,k]:+7.2f}   "
              f"{e_half_4[0][k]:+7.2f} |    "
              f"{eps_4[2,0,k]:+7.2f} {eps_4[2,1,k]:+7.2f} {eps_4[2,3,k]:+7.2f}   "
              f"{e_half_4[2][k]:+7.2f}")
    return nds_h3, nds_he4, nds_4n


# ======================================================================
# SECTION 9: DEDUCTIVE ALPHA CLUSTERS (8Be..16O) & 55-PAIR 11Li LEDGER
# ======================================================================
def run_sec9_macroblocks_and_11li(sc, couplings, d_cat, del_cat, blocks_8):
    g_s, g_m, g_b, cfb, r2_ep = couplings
    nds_h3, nds_he4, nds_4n = blocks_8
    _, _, rp0, tp0, _ = build_local_arclength_tube(B_U_P, sc["l_p"], N_S_MULTI)
    _, _, rn0, tn0, _ = build_local_arclength_tube(B_U_N, sc["l_n"], N_S_MULTI)
    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, N_TAU_MULTI, endpoint=False)
    ex, ey, ez = np.eye(3)

    d_2n_eq = d_cat["eq_s0"]["nn"]
    dl_2n_eq = del_cat["eq_s0"]["nn"]

    def instantiate_block(tag, u_ray, template_nodes, rot_blk=np.eye(3)):
        return [
            (f"{nm}_{tag}", ip, tag, u_ray, pos @ rot_blk.T,
             rf @ rot_blk.T, sx @ rot_blk.T, gm)
            for nm, ip, pos, rf, sx, gm in template_nodes
        ]

    def instantiate_2n(tag, u_ray, ax_sep, s_ax):
        us = ax_sep / np.linalg.norm(ax_sep)
        su = s_ax / np.linalg.norm(s_ax)
        return [
            (f"n1_{tag}", False, tag, u_ray, -0.5 * d_2n_eq * us, -us, +su, 0.0),
            (f"n2_{tag}", False, tag, u_ray, +0.5 * d_2n_eq * us, +us, -su, dl_2n_eq),
        ]

    def eval_exact_contact_assembly(blk_nucs, u_xi, inter_only=True):
        n_tot = len(blk_nucs)
        is_p = np.array([n[1] for n in blk_nucs], dtype=bool)
        tags = [n[2] for n in blk_nucs]
        u_rays = np.array([n[3] for n in blk_nucs], dtype=float)
        dr_blk = np.array([n[4] for n in blk_nucs], dtype=float)
        s_vecs = np.array([n[6] / np.linalg.norm(n[6]) for n in blk_nucs])

        ds_arr = np.where(is_p, sc["l_p"] / N_S_MULTI, sc["l_n"] / N_S_MULTI)
        rt_arr = np.where(is_p, sc["r_tp"], sc["r_tn"])

        r_loc_tau = np.zeros((N_TAU_MULTI, n_tot, N_S_MULTI, 3))
        t_all = np.zeros((N_TAU_MULTI, n_tot, N_S_MULTI, 3))
        for k, (_, ip, _, _, p_loc, rfk, sxk, gmk) in enumerate(blk_nucs):
            r0, t0 = (rp0, tp0) if ip else (rn0, tn0)
            for it, tau in enumerate(taus):
                rm = frame_from_z_and_ref(sxk, rfk, gmk + tau)
                r_loc_tau[it, k] = p_loc + (r0 @ rm.T)
                t_all[it, k] = t0 @ rm.T

        inter_pairs = [
            (i, j) for i in range(n_tot) for j in range(i + 1, n_tot) if tags[i] != tags[j]
        ]
        iu_in = np.array([p[0] for p in inter_pairs])
        ju_in = np.array([p[1] for p in inter_pairs])
        rcut_in = rt_arr[iu_in] + rt_arr[ju_in]
        xi_touch = exact_steric_contact_scale(u_rays, r_loc_tau, iu_in, ju_in, rcut_in) * (1.0 + 1e-12)
        xi = xi_touch + (u_xi ** 2)

        centers = xi * u_rays + dr_blk
        r_all = (xi * u_rays)[None, :, None, :] + r_loc_tau
        iu, ju = (iu_in, ju_in) if inter_only else np.triu_indices(n_tot, k=1)

        diff = r_all[:, iu, :, None, :] - r_all[:, ju, None, :, :]
        raw_d2 = np.sum(diff ** 2, axis=-1)
        d12_min_p = np.sqrt(np.min(raw_d2, axis=(0, 2, 3)))
        rcut_p = rt_arr[iu] + rt_arr[ju]
        sig2_p = (rt_arr[iu] ** 2) + (rt_arr[ju] ** 2)
        d2 = raw_d2 + sig2_p[None, :, None, None]
        d12 = np.sqrt(d2)
        g_de = (R_E ** 2) / (d2 + (R_E ** 2))
        tdot = np.einsum("tpik,tpjk->tpij", t_all[:, iu], t_all[:, ju])

        fac_p = (ds_arr[iu] * ds_arr[ju]) / (4.0 * np.pi * N_TAU_MULTI)
        s2_p = np.sum(g_de * np.exp(-d12 / R_2PI) / d12, axis=(0, 2, 3)) * fac_p
        m1_p = np.sum(tdot * g_de * np.exp(-d12 / R_PI) / d12, axis=(0, 2, 3)) * fac_p
        b4_p = np.sum(1.0 / (d2 ** 2), axis=(0, 2, 3)) * fac_p
        sdot_p = np.sum(s_vecs[iu] * s_vecs[ju], axis=-1)
        dcm_p = np.linalg.norm(centers[iu] - centers[ju], axis=-1)
        vc_p = np.where(is_p[iu] & is_p[ju], ALPHA * HBAR_C / np.sqrt(dcm_p ** 2 + r2_ep), 0.0)
        vp_p = (-g_s + cfb * np.maximum(0.0, -sdot_p)) * s2_p - g_m * m1_p + g_b * b4_p + vc_p
        min_rat = float(np.min(d12_min_p / rcut_p))
        return (float(np.sum(vp_p)), xi, float(np.min(d12_min_p)), min_rat,
                centers, (iu, ju, vp_p, dcm_p, d12_min_p, sdot_p))

    seeds_8 = ([0.0, 0.0, 0.0, 0.1], [0.5 * np.pi, np.pi, 0.0, 0.1], [0.5 * np.pi, 0.0, 0.0, 0.1])
    opt_8be = min(
        [minimize(
            lambda x: eval_exact_contact_assembly(
                instantiate_block("a1", np.array([0., 0., -0.5]), nds_he4)
                + instantiate_block("a2", np.array([0., 0., +0.5]), nds_he4, euler_zyz(*x[:3])),
                x[3], True
            )[0],
            x0, method="Nelder-Mead", options={"maxiter": 140}
        ) for x0 in seeds_8],
        key=lambda r: r.fun
    )
    e8, r8, clr8, rat8, _, _ = eval_exact_contact_assembly(
        instantiate_block("a1", np.array([0., 0., -0.5]), nds_he4)
        + instantiate_block("a2", np.array([0., 0., +0.5]), nds_he4, euler_zyz(*opt_8be.x[:3])),
        opt_8be.x[3], True
    )

    def build_9be_free(x):
        u_xm, z_m, psi2, th_s, ph_s, gm_m = x[:6]
        s_m = np.array([np.sin(th_s) * np.cos(ph_s), np.sin(th_s) * np.sin(ph_s), np.cos(th_s)])
        u_m = np.array([np.exp(np.clip(u_xm, -2.5, 2.0)), 0.0, z_m])
        return (instantiate_block("a1", np.array([0., 0., -0.5]), nds_he4)
                + instantiate_block("a2", np.array([0., 0., +0.5]), nds_he4, rot_z(psi2))
                + [("n_med", False, "med", u_m, np.zeros(3), ex, s_m, gm_m)])

    opt_9be = minimize(
        lambda x: eval_exact_contact_assembly(build_9be_free(x), x[6], True)[0],
        [np.log(0.35), 0.0, 0.5 * np.pi, 0.5 * np.pi, 0.5 * np.pi, 0.0, 0.0],
        method="Nelder-Mead", options={"maxiter": 200}
    )
    e9, r9, clr9, rat9, _, _ = eval_exact_contact_assembly(
        build_9be_free(opt_9be.x), opt_9be.x[6], True
    )

    def build_12c_ring(x):
        return sum([
            instantiate_block(
                f"a{k}", (1.0 / np.sqrt(3.0)) * np.array([np.cos(a), np.sin(a), 0.]),
                nds_he4, rot_z(a) @ euler_zyz(x[0], x[1], x[2])
            ) for k, a in enumerate((0.0, 2 * np.pi / 3, 4 * np.pi / 3))
        ], [])

    opt_12c = minimize(
        lambda x: eval_exact_contact_assembly(build_12c_ring(x), x[3], True)[0],
        [0.0, 0.5 * np.pi, 0.0, 0.0], method="Nelder-Mead", options={"maxiter": 160}
    )
    e12, r12, clr12, rat12, _, _ = eval_exact_contact_assembly(
        build_12c_ring(opt_12c.x), opt_12c.x[3], True
    )

    evs_tet = np.array([[1, 1, 1], [-1, -1, 1], [1, -1, -1], [-1, 1, -1]], float) / np.sqrt(3.0)
    v4_grp = [np.eye(3), np.diag([-1., -1., 1.]), np.diag([1., -1., -1.]), np.diag([-1., 1., -1.])]

    def r0_protons_in(gam):
        return frame_from_z_and_ref(-D111, U0, gam)

    def r0_neutrons_in(gam):
        return frame_from_z_and_ref(+D111, U0, gam)

    def solve_16o_v4_orbit(r0_fn):
        opt = min(
            [minimize(
                lambda x: eval_exact_contact_assembly(sum([
                    instantiate_block(f"a{k}", np.sqrt(3.0 / 8.0) * evs_tet[k],
                                      nds_he4, v4_grp[k] @ r0_fn(x[0]))
                    for k in range(4)
                ], []), x[1], True)[0],
                [g0, 0.0], method="Nelder-Mead", options={"maxiter": 100}
            ) for g0 in (0.0, np.pi / 3.0, 2.0 * np.pi / 3.0)],
            key=lambda r: r.fun
        )
        return eval_exact_contact_assembly(sum([
            instantiate_block(f"a{k}", np.sqrt(3.0 / 8.0) * evs_tet[k],
                              nds_he4, v4_grp[k] @ r0_fn(opt.x[0]))
            for k in range(4)
        ], []), opt.x[1], True)[:4]

    e16_ax, r16_ax, c16_ax, rt16_ax = solve_16o_v4_orbit(rot_z)
    e16_pi, r16_pi, c16_pi, rt16_pi = solve_16o_v4_orbit(r0_protons_in)
    e16_ni, r16_ni, c16_ni, rt16_ni = solve_16o_v4_orbit(r0_neutrons_in)

    print("\n=== 9A. DEDUCTIVE ALPHA-CLUSTER EQUILIBRIA & V_4 CONTROL TEST ===", flush=True)
    print("   Cluster Architecture          | R_aa*[fm]  min_d12[fm]  d/(r_i+r_j) | "
          "Static V_inter [MeV]")
    for lbl, r_v, c_v, rt_v, e_v in [
        ("8Be = 2a (SO(3)-relaxed)     ", r8,     clr8,   rat8,    e8),
        ("9Be = a + n + a (free n-med) ", r9,     clr9,   rat9,    e9),
        ("12C = 3a (C_3 Euler-relaxed) ", r12,    clr12,  rat12,   e12),
        ("16O = 4a V_4 Axis-Parallel   ", r16_ax, c16_ax, rt16_ax, e16_ax),
        ("16O = 4a V_4 Protons-Inward  ", r16_pi, c16_pi, rt16_pi, e16_pi),
        ("16O = 4a V_4 Neutrons-Inward ", r16_ni, c16_ni, rt16_ni, e16_ni),
    ]:
        print(f"  {lbl} |   {r_v:5.2f}      {c_v:6.4f}       {rt_v:6.4f}    |      {e_v:+8.2f}")

    def arch_1a(x):
        yaw, tilt, uz, gm_p = x[:4]
        ez_c = np.exp(np.clip(uz, -2.5, 2.5))
        ns = sum([instantiate_block(
            f"t{k+1}", np.array([np.cos(2 * np.pi * k / 3), np.sin(2 * np.pi * k / 3), 0.]),
            nds_h3, rot_z(2 * np.pi * k / 3 + yaw) @ rot_x(tilt)
        ) for k in range(3)], [])
        return ns + [
            ("n_p1", False, "p_up", np.array([0., 0., +ez_c]), np.zeros(3), ey, +ex, gm_p),
            ("n_p2", False, "p_dn", np.array([0., 0., -ez_c]), np.zeros(3), ey, -ex, gm_p + dl_2n_eq),
        ]

    def arch_1b(x):
        yaw, tilt, ur, zh = x[:4]
        er_h = np.exp(np.clip(ur, -2.5, 2.5))
        uc = np.array([0.5, 0.5 * np.sqrt(3.0), 0.])
        ut = np.array([-0.5 * np.sqrt(3.0), 0.5, 0.])
        ns = sum([instantiate_block(
            f"t{k+1}", np.array([np.cos(2 * np.pi * k / 3), np.sin(2 * np.pi * k / 3), 0.]),
            nds_h3, rot_z(2 * np.pi * k / 3 + yaw) @ rot_x(tilt)
        ) for k in range(3)], [])
        return ns + instantiate_2n("2n_h", er_h * uc + np.array([0., 0., zh]), ut, ez)

    def arch_2(x):
        psi_t, ux1, z1, ux2, z2 = x[:5]
        rx180 = np.diag([1.0, -1.0, -1.0])
        u1 = np.array([+np.exp(np.clip(ux1, -2.5, 2.5)), 0.0, z1])
        u2 = np.array([-np.exp(np.clip(ux2, -2.5, 2.5)), 0.0, z2])
        return (instantiate_block("a", np.array([0., 0., -3.0 / 7.0]), nds_he4)
                + instantiate_block("t", np.array([0., 0., +4.0 / 7.0]), nds_h3, rot_z(psi_t) @ rx180)
                + instantiate_2n("w1", u1, ey, ez)
                + instantiate_2n("w2", u2, ey, ez))

    def arch_3(x):
        ya, y4, yt, t4 = x[:4]
        angs = (0.0, 2 * np.pi / 3, 4 * np.pi / 3)
        return (
            instantiate_block("a", np.array([np.cos(angs[0]), np.sin(angs[0]), 0.]), nds_he4, rot_z(ya))
            + instantiate_block("4n", np.array([np.cos(angs[1]), np.sin(angs[1]), 0.]),
                                nds_4n, rot_z(y4) @ rot_x(t4))
            + instantiate_block("t", np.array([np.cos(angs[2]), np.sin(angs[2]), 0.]), nds_h3, rot_z(yt))
        )

    specs_11 = [
        ("1A. 3x(1p+2n) + Central 2n Bridge", arch_1a, [0.8, 0.25, np.log(0.90), 0.0, 0.0]),
        ("1B. 3x(1p+2n) + Outer Eq. (2n)   ", arch_1b, [0.8, 0.20, np.log(1.35), 0.0, 0.0]),
        ("2.  4He + 3H + Two Eq. (2n)      ", arch_2,  [0.0, np.log(0.75), 0.05, np.log(0.80), 0.05, 0.0]),
        ("3.  4He + 4n-Disph + 3H Tri      ", arch_3,  [0.0, 0.5, 0.5, 0.2, 0.0]),
    ]

    print("\n=== 9B. COMPARATIVE 55-PAIR 11-TUBE 11Li (3p + 8n) CLUSTER LEDGER ===", flush=True)
    print("  Architecture                      | Static V_55 |  V_pp    V_pn     V_nn  | "
          "d/(r_i+r_j) | S1_nn  R_cm")
    best_res = None
    for title, fn_a, x0 in specs_11:
        opt = minimize(
            lambda x: eval_exact_contact_assembly(fn_a(x), x[-1], True)[0],
            x0, method="Nelder-Mead", options={"maxiter": 180}
        )
        b_nucs = fn_a(opt.x)
        vt, _, _, mrat, cms, (iu, ju, vp_p, dcm_p, d12_p, sdot_p) = eval_exact_contact_assembly(
            b_nucs, opt.x[-1], False
        )
        is_p = np.array([n[1] for n in b_nucs], dtype=bool)
        pp_m, nn_m = is_p[iu] & is_p[ju], (~is_p[iu]) & (~is_p[ju])
        pn_m = ~(pp_m | nn_m)
        s1_nn = float(np.sum(0.5 * (1.0 + sdot_p[nn_m])))
        r_cm = float(np.sqrt(np.mean(np.sum((cms - np.mean(cms, axis=0)) ** 2, axis=-1))))
        print(f"  {title} |   {vt:+8.1f}  | {np.sum(vp_p[pp_m]):+6.1f} {np.sum(vp_p[pn_m]):+7.1f} "
              f"{np.sum(vp_p[nn_m]):+7.1f} |    {mrat:6.4f}   | {s1_nn:4.1f}   {r_cm:4.2f}")
        if best_res is None or vt < best_res[0]:
            best_res = (vt, title, b_nucs, cms, iu, ju, vp_p, dcm_p, d12_p)

    _, b_title, b_nucs, cms, iu, ju, vp_p, dcm_p, d12_p = best_res
    v_mat = np.zeros((11, 11))
    v_mat[iu, ju] = v_mat[ju, iu] = vp_p
    cm0 = np.mean(cms, axis=0)
    is_p = np.array([n[1] for n in b_nucs], dtype=bool)

    print(f"\n  --- 11-Tube Spatial & Load Ledger for Optimal State: {b_title.strip()} ---")
    print("  Tube      Blk  | Center (x, y, z) [fm]  | Spin (sx,sy,sz)   | "
          "V_w/p   V_w/n  1/2-Share | Top-2 Partners")
    for a in range(11):
        nm, _, bk, _, _, _, sxa, _ = b_nucs[a]
        rc, su = cms[a] - cm0, sxa / np.linalg.norm(sxa)
        vp_a, vn_a = float(np.sum(v_mat[a, is_p])), float(np.sum(v_mat[a, ~is_p]))
        ord_b = [b for b in np.argsort(v_mat[a]) if b != a]
        b1, b2 = ord_b[0], ord_b[1]
        p_str = f"{b_nucs[b1][0]}({v_mat[a,b1]:+6.1f}), {b_nucs[b2][0]}({v_mat[a,b2]:+6.1f})"
        print(f"  {nm:9s} {bk:4s} | ({rc[0]:+5.2f},{rc[1]:+5.2f},{rc[2]:+5.2f}) | "
              f"({su[0]:+4.2f},{su[1]:+4.2f},{su[2]:+4.2f}) | {vp_a:+6.1f}  {vn_a:+6.1f}  "
              f"{0.5 * (vp_a + vn_a):+7.2f}  | {p_str}")

    inter_b = sorted(
        [(vp_p[k], b_nucs[iu[k]][0], b_nucs[iu[k]][2],
          b_nucs[ju[k]][0], b_nucs[ju[k]][2], dcm_p[k], d12_p[k])
         for k in range(len(iu)) if b_nucs[iu[k]][2] != b_nucs[ju[k]][2]],
        key=lambda z: z[0]
    )
    print("\n  --- Top 8 Inter-Cluster Bridging Bonds (All Steric-Clear >= r_i + r_j) ---")
    print("  Rank | Pair (BlkA <-> BlkB)              | d_cm[fm] d_min[fm] | Static V_pair [MeV]")
    for rk, (vp, n1, b1, n2, b2, dcm, dmn) in enumerate(inter_b[:8], 1):
        print(f"   {rk:2d}  | {n1:9s}({b1:4s}) <-> {n2:9s}({b2:4s}) | "
              f"  {dcm:4.2f}    {dmn:6.4f}   |      {vp:+7.2f}")


# ======================================================================
# SECTION 10: UNIT-RADIUS 1D ATLAS, HIGH-Q^2 SACHS, & C_2v DISPHENOID
# ======================================================================
def kelly_empirical_sachs(q2_gev2):
    tau_p = (q2_gev2 * 1e6) / (4.0 * (M_P ** 2))
    tau_n = (q2_gev2 * 1e6) / (4.0 * (M_N ** 2))
    ge_p = (1.0 - 0.24 * tau_p) / (
        1.0 + 10.98 * tau_p + 12.82 * (tau_p ** 2) + 21.97 * (tau_p ** 3)
    )
    gm_p_mu = (1.0 + 0.12 * tau_p) / (
        1.0 + 10.97 * tau_p + 18.86 * (tau_p ** 2) + 6.55 * (tau_p ** 3)
    )
    dip = (1.0 + q2_gev2 / 0.71) ** (-2)
    ge_n = (1.70 * tau_n / (1.0 + 3.30 * tau_n)) * dip
    return ge_p, gm_p_mu, ge_n


def wall_normalized_spin_wake_volume(nucs_list, sc, n_grid=24):
    """Wall-normalized 3D Biot-Savart spin-wake saturation integral."""
    _, _, rp0, tp0, _ = build_local_arclength_tube(B_U_P, sc["l_p"], N_S_MULTI)
    _, _, rn0, tn0, _ = build_local_arclength_tube(B_U_N, sc["l_n"], N_S_MULTI)
    dsp_seg, dsn_seg = sc["l_p"] / N_S_MULTI, sc["l_n"] / N_S_MULTI
    rtp, rtn = sc["r_tp"], sc["r_tn"]

    drn0 = tn0 * dsn_seg
    pts_w = rn0 + rtn * np.array([[0.0, 0.0, 1.0]])
    df_w = pts_w[:, None, :] - rn0[None, :, :]
    d2_w = np.sum(df_w ** 2, axis=-1) + (rtn ** 2)
    d1_w = np.sqrt(d2_w)
    kw = (1.0 + d1_w / R_PI) * np.exp(-d1_w / R_PI) / (d2_w * d1_w)
    vw = np.sum(np.cross(drn0[None, :, :], df_w) * kw[:, :, None], axis=1)
    v_wall_norm = float(np.sqrt(np.mean(np.sum(vw ** 2, axis=-1))))

    ax = np.linspace(-3.4, 3.4, n_grid)
    dv = (ax[1] - ax[0]) ** 3
    xg, yg, zg = np.meshgrid(ax, ax, ax, indexing="ij")
    pts = np.stack([xg.ravel(), yg.ravel(), zg.ravel()], axis=-1)

    v_tot = np.zeros_like(pts)
    for _, ip, center_a, rf_a, sx_a, gm_a in nucs_list:
        r0, t0, dsa, rta = (
            (rp0, tp0, dsp_seg, rtp) if ip else (rn0, tn0, dsn_seg, rtn)
        )
        rm = frame_from_z_and_ref(sx_a, rf_a, gm_a)
        r_s = center_a[None, :] + (r0 @ rm.T)
        dr_s = (t0 @ rm.T) * dsa
        diff = pts[:, None, :] - r_s[None, :, :]
        d2 = np.sum(diff ** 2, axis=-1) + (rta ** 2)
        d1 = np.sqrt(d2)
        kern = (1.0 + d1 / R_PI) * np.exp(-d1 / R_PI) / (d2 * d1)
        v_tot += (1.0 / v_wall_norm) * np.sum(
            np.cross(dr_s[None, :, :], diff) * kern[:, :, None], axis=1
        )
    return float(np.sum(np.minimum(1.0, np.sum(v_tot ** 2, axis=-1))) * dv)


def run_sec10_supplemental_checks(st_p, st_n, sc, wr_p, wr_n, mu_p, ind_pack,
                                  couplings, del_cat, blocks_8):
    _, nds_he4, _ = blocks_8
    n_tot = len(st_p["phi"])

    print("\n=== 10A. UNIT-CONTACT (R_max=1) 1D FLUID-LINE ATLAS & FRENET INVARIANTS ===",
          flush=True)
    print("  Phi[deg] St | |r_u|   J_s,u  |   (T_rho, T_phi, T_d)    |  "
          "kap_u    tau_u  |   B_d   1+r.kN")
    for deg, idx in [(0, 0), (30, n_tot // 12), (60, n_tot // 6), (90, n_tot // 4)]:
        ph = st_p["phi"][idx]
        er = np.sin(2.0 * ph) * U0 - np.cos(2.0 * ph) * V0
        ep = np.cos(2.0 * ph) * U0 + np.sin(2.0 * ph) * V0
        for lbl, st in [("p+", st_p), ("n0", st_n)]:
            ru_m = float(np.linalg.norm(st["r"][idx]))
            js_u = float(st["js"][idx])
            tr = float(st["T"][idx] @ er)
            tp = float(st["T"][idx] @ ep)
            td = float(st["T"][idx] @ D111)
            kp_u, ta_u = float(st["kap"][idx]), float(st["tau"][idx])
            bd_v = float(st["B"][idx] @ D111)
            vir = 1.0 + float(np.dot(st["r"][idx], st["kap"][idx] * st["N"][idx]))
            print(f"    {deg:3d}    {lbl} | {ru_m:6.4f}  {js_u:6.4f} | "
                  f"({tr:+6.3f},{tp:+6.3f},{td:+6.3f}) |  {kp_u:6.4f}  {ta_u:+7.4f} | "
                  f"{bd_v:+6.4f}  {vir:+6.4f}")

    r_pi_111 = 2.0 * np.outer(D111, D111) - np.eye(3)
    rp_rd = st_p["r"] @ r_pi_111.T
    rd_u_ratio = max(
        float(np.max(np.abs(rp_rd[:, i] + sgn * rp_rd[:, j]))) / np.sqrt(2.0)
        for (i, j) in ((0, 1), (1, 2), (2, 0)) for sgn in (-1.0, 1.0)
    )

    twf_n = float(np.sum(st_n["tau"] * st_n["ds"]) / (2.0 * np.pi))
    twf_p = float(np.sum(st_p["tau"] * st_p["ds"]) / (2.0 * np.pi))
    wk_n = float(np.sum(st_n["kap"] * st_n["ds"]) / (2.0 * np.pi))
    wk_p = float(np.sum(st_p["kap"] * st_p["ds"]) / (2.0 * np.pi))
    wb_n = float(np.sum(st_n["kap"] * (st_n["B"] @ D111) * st_n["ds"]) / (2.0 * np.pi))
    wb_p = float(np.sum(st_p["kap"] * (st_p["B"] @ D111) * st_p["ds"]) / (2.0 * np.pi))
    a111_n = (0.5 * float(np.sum(np.cross(st_n["r"], st_n["r1"]) @ D111) * st_n["dphi"])
              / (st_n["ell"] ** 2))
    a111_p = (0.5 * float(np.sum(np.cross(st_p["r"], st_p["r1"]) @ D111) * st_p["dphi"])
              / (st_p["ell"] ** 2))

    def e2_bu(bu):
        st = build_unit_radius_state(bu, 720)
        return st["ell"] * float(np.sum((st["kap"] ** 2) * st["ds"]))

    def e4_bu(bu):
        st = build_unit_radius_state(bu, 720)
        return (st["ell"] ** 3) * float(np.sum((st["kap"] ** 4) * st["ds"]))

    def s0_bu(bu):
        st = build_unit_radius_state(bu, 720)
        return float(np.sum((st["t_d"] ** 2) * st["ds"]) / st["ell"]) - (1.0 / 3.0)

    def oblate_bu(bu):
        st = build_unit_radius_state(bu, 720)
        w_d = st["r"] @ D111
        rho2 = np.sum(st["r"] ** 2, axis=1) - (w_d ** 2)
        return float(np.sum((rho2 - 2.0 * (w_d ** 2)) * st["ds"]))

    def rope_bu(bu):
        st = build_unit_radius_state(bu, 720)
        r_u, t_u = st["r"][::2] / st["ell"], st["T"][::2]
        df = r_u[None, :, :] - r_u[:, None, :]
        d2 = np.sum(df ** 2, axis=-1)
        np.fill_diagonal(d2, 1e9)
        cn = np.linalg.norm(np.cross(df, t_u[:, None, :]), axis=-1)
        return 1.0 / float(np.min(d2 / (2.0 * np.maximum(cn, 1e-18))))

    bu_e2 = float(minimize_scalar(e2_bu, bounds=(0.24, 0.50), method="bounded").x)
    bu_e4 = float(minimize_scalar(e4_bu, bounds=(0.24, 0.50), method="bounded").x)
    bu_s0 = float(brentq(s0_bu, 0.35, 0.65))
    bu_iso = float(brentq(oblate_bu, 0.55, 0.90))
    res_rope = minimize_scalar(rope_bu, bounds=(0.12, 0.28), method="bounded")

    phi, dphi = st_n["phi"], st_n["dphi"]
    dbus, dbuc = 0.05, 0.03
    rc_u = np.sin(2.0 * phi)[:, None] * U0 - np.cos(2.0 * phi)[:, None] * V0
    pc_u = np.cos(2.0 * phi)[:, None] * U0 + np.sin(2.0 * phi)[:, None] * V0
    rho_u = R0_U + A_U * np.cos(3.0 * phi)
    w_1p = B_U_N * np.sin(3.0 * phi) + dbus * np.sin(phi) + dbuc * np.cos(phi)
    wp_1p = 3.0 * B_U_N * np.cos(3.0 * phi) + dbus * np.cos(phi) - dbuc * np.sin(phi)
    r_1p = rho_u[:, None] * rc_u + w_1p[:, None] * D111
    rp_1p = ((-3.0 * A_U * np.sin(3.0 * phi))[:, None] * rc_u
             + (2.0 * rho_u)[:, None] * pc_u + wp_1p[:, None] * D111)
    j_tot = np.sum(np.cross(r_1p, rp_1p), axis=0) * dphi
    j_par = float(np.dot(j_tot, D111))
    tan_num = float(np.linalg.norm(j_tot - j_par * D111) / j_par)
    tan_ex = (5.0 / 22.0) * np.sqrt(dbus ** 2 + dbuc ** 2)
    u_pipe_c = HBAR_C / (4.0 * M_N * a111_n * sc["l_n"])

    print(f"  RD_u Tangency   : max(|x+-y|)/sqrt(2) on 180-deg p+ = {rd_u_ratio:.6f} "
          "(exact 1.000000)")
    print(f"  Frenet & Darboux: Wr(n,p)=({wr_n:+.5f},{wr_p:+.5f}), "
          f"Tw_F(n,p)=({twf_n:+.5f},{twf_p:+.5f}) -> Lk_F=({wr_n+twf_n:+.4f},{wr_p+twf_p:+.4f})")
    print(f"                    W_kap(n,p)=({wk_n:.5f},{wk_p:.5f}), "
          f"W_B(n,p)=({wb_n:.5f},{wb_p:.5f}), A_111/L^2(n,p)=({a111_n:.6f},{a111_p:.6f})")
    print(f"  Unit Landmarks  : b_u: p+={B_U_P:.4f}, n0={B_U_N:.4f}, "
          f"rope={res_rope.x:.4f}(L/r_t={res_rope.fun:.2f}), E2={bu_e2:.4f}, "
          f"E4={bu_e4:.4f}, S0=0:{bu_s0:.4f}, iso={bu_iso:.4f}")
    print(f"  Added-Mass Gyro : 1*phi tilt err={abs(tan_num-tan_ex):.2e} | "
          f"hollow-pipe u/c={u_pipe_c:.4f} > v_s/c={np.sqrt(ALPHA):.5f} "
          "(M_a = exterior added mass)", flush=True)

    eval_p, _ = build_gordon_sachs_evaluator(
        st_p, sc["l_p"], sc["r_tp"], M_P, 1.0, +1.0, ind_pack
    )
    eval_n, _ = build_gordon_sachs_evaluator(
        st_n, sc["l_n"], sc["r_tn"], M_N, 0.0, -1.0, None
    )
    print("\n=== 10B. HIGH-Q^2 GORDON-SACHS FORM FACTORS (LAPLACE w_ind IN F_1) ===",
          flush=True)
    print("  Q^2[GeV^2] |  G_E^p (Model / Kelly)  | G_M^p/mu_p (Mod / Kel) | "
          " G_E^n (Model / Kelly)  | Q^4*G_M^p/mu_p (M / K)")
    for q2 in [0.05, 0.25, 0.50, 1.00, 2.00, 4.00, 6.00]:
        gep, gmp, _ = eval_p(q2, True)
        gen, _, _ = eval_n(q2, True)
        gep_k, gmp_k, gen_k = kelly_empirical_sachs(q2)
        gmp_u = gmp / mu_p
        print(f"    {q2:5.2f}    | {gep:+8.4f} / {gep_k:+8.4f}   | "
              f"{gmp_u:+8.4f} / {gmp_k:+8.4f}  | {gen:+8.4f} / {gen_k:+8.4f}   | "
              f"  {(q2**2)*gmp_u:+6.3f} / {(q2**2)*gmp_k:+6.3f}")

    idx_ap = [0, n_tot // 3, (2 * n_tot) // 3]
    tp_ap, tn_ap = st_p["T"][idx_ap], st_n["T"][idx_ap]
    v4_m = [np.eye(3), np.diag([1., -1., -1.]), np.diag([-1., 1., -1.]), np.diag([-1., -1., 1.])]
    v4_sum = tp_ap @ v4_m[0].T + tp_ap @ v4_m[1].T + tn_ap @ v4_m[2].T + tn_ap @ v4_m[3].T
    v4_leak = float(np.linalg.norm(np.sum(v4_sum, axis=0)))
    v4_exact = 2.0 * (np.sqrt(3.0) - 1.0) / np.sqrt(3.0)

    mt_n, _, _, _, _ = solve_kelvin_bem_and_check_eq23(st_n, sc["rst_n"], 180)
    mt_p, _, _, _, _ = solve_kelvin_bem_and_check_eq23(st_p, sc["rst_p_act"], 180)
    c2v_s = np.array([n[4] / np.linalg.norm(n[4]) for n in nds_he4])
    f111_vec = np.array([mt_p[0] if n[1] else mt_n[0] for n in nds_he4])[:, None] * c2v_s
    c2v_f_leak = float(np.linalg.norm(np.sum(f111_vec, axis=0)))

    p_b = build_local_arclength_tube(B_U_P, sc["l_p"], N_S_MULTI)
    n_b = build_local_arclength_tube(B_U_N, sc["l_n"], N_S_MULTI)
    d_ref = 1.75
    s_tet = d_ref / (2.0 * np.sqrt(2.0))
    ex, ey, ez = np.eye(3)
    sp_p = np.array([-1.0, +1.0, 0.0]) / np.sqrt(2.0)
    sp_n = np.array([+1.0, +1.0, 0.0]) / np.sqrt(2.0)
    bp_in = np.array([-1.0, -1.0, 0.0]) / np.sqrt(2.0)
    bn_in = np.array([-1.0, +1.0, 0.0]) / np.sqrt(2.0)
    dl_pp = del_cat["eq_s0"]["pp"]
    dl_nn = del_cat["eq_s0"]["nn"]
    dl_bv = del_cat["bev_90"]["pn"]
    dl_cx = del_cat["coax_s1"]["pn"]
    dl_ws = del_cat["eq_s0"]["pn"]

    tet_pts = [
        np.array([+s_tet, +s_tet, +s_tet]), np.array([-s_tet, -s_tet, +s_tet]),
        np.array([+s_tet, -s_tet, -s_tet]), np.array([-s_tet, +s_tet, -s_tet]),
    ]
    v4_dirs = [p / np.linalg.norm(p) for p in [
        np.array([1., 1., 1.]), np.array([1., -1., -1.]),
        np.array([-1., 1., -1.]), np.array([-1., -1., 1.]),
    ]]

    modes_a4 = [
        ("1. 3D C_2v Disphenoid Swirl (0+)", [
            (True,  tet_pts[0], +bp_in, +sp_p, 0.0),
            (True,  tet_pts[1], -bp_in, -sp_p, dl_pp),
            (False, tet_pts[2], +bn_in, +sp_n, dl_bv),
            (False, tet_pts[3], -bn_in, -sp_n, dl_bv + dl_nn),
        ]),
        ("2. 2x2 Planar Singlet Sq.   (0+)", [
            (True,  np.array([-0.5 * d_ref, -0.5 * d_ref, 0.]), +ex, +ez, 0.0),
            (True,  np.array([+0.5 * d_ref, +0.5 * d_ref, 0.]), -ex, +ez, 0.0),
            (False, np.array([+0.5 * d_ref, -0.5 * d_ref, 0.]), -ey, -ez, dl_ws),
            (False, np.array([-0.5 * d_ref, +0.5 * d_ref, 0.]), +ey, -ez, dl_ws),
        ]),
        ("3. 2x2 Planar Antiparallel  (0+)", [
            (True,  np.array([-0.5 * d_ref, 0., -0.5 * d_ref]), +ex, +ez, 0.0),
            (False, np.array([-0.5 * d_ref, 0., +0.5 * d_ref]), +ex, +ez, dl_cx),
            (True,  np.array([+0.5 * d_ref, 0., +0.5 * d_ref]), -ex, -ez, dl_ws),
            (False, np.array([+0.5 * d_ref, 0., -0.5 * d_ref]), -ex, -ez, dl_ws + dl_cx),
        ]),
        ("4. 3D V_4 Sub-Lattice Node  (0+)", [
            (True,  tet_pts[0], U0, v4_dirs[0], 0.0),
            (True,  tet_pts[1], U0, v4_dirs[1], 0.0),
            (False, tet_pts[2], U0, v4_dirs[2], 0.0),
            (False, tet_pts[3], U0, v4_dirs[3], 0.0),
        ]),
        ("5. 1x4 Coaxial Linear Chain (2+)", [
            (True,  np.array([0., 0., -1.5 * d_ref]), ey, +ez, 0.0),
            (False, np.array([0., 0., -0.5 * d_ref]), ey, +ez, dl_cx),
            (True,  np.array([0., 0., +0.5 * d_ref]), ey, +ez, 2.0 * dl_cx),
            (False, np.array([0., 0., +1.5 * d_ref]), ey, +ez, 3.0 * dl_cx),
        ]),
        ("6. 3D Radial Hedgehog       (0+)", [
            (True,  tet_pts[0], ez, tet_pts[0] / np.linalg.norm(tet_pts[0]), 0.0),
            (True,  tet_pts[1], ez, tet_pts[1] / np.linalg.norm(tet_pts[1]), 0.0),
            (False, tet_pts[2], ez, tet_pts[2] / np.linalg.norm(tet_pts[2]), 0.0),
            (False, tet_pts[3], ez, tet_pts[3] / np.linalg.norm(tet_pts[3]), 0.0),
        ]),
    ]

    n_origin = [("n0", False, np.zeros(3), ey, ez, 0.0)]
    vcav_1n = wall_normalized_spin_wake_volume(n_origin, sc)
    vcav_4he = wall_normalized_spin_wake_volume(nds_he4, sc)
    vcav_5he = wall_normalized_spin_wake_volume(nds_he4 + n_origin, sc)
    cav_block_pct = 100.0 * (1.0 - (vcav_5he - vcav_4he) / vcav_1n)

    print("\n=== 10C. UNFORCED C_2v DISPHENOID VS 6-MODE EQUAL-SPACING (1.75 fm) A=4 ATLAS ===",
          flush=True)
    print(f"  Symmetry Nulls  : Single-cube V_4 tangent leak = {v4_leak:.6f} "
          f"(exact {v4_exact:.6f}) vs C_2v thrust leak = {c2v_f_leak:.2e}")
    print(f"  5He Spin-Wake   : V_wake(1n)={vcav_1n:.3f}, V_wake(4He)={vcav_4he:.3f}, "
          f"V_wake(5He)={vcav_5he:.3f} fm^3 -> {cav_block_pct:.1f}% central saturation")
    print("  4-Nucleon Architecture (d_NN = 1.75 fm) | min_d12[fm] | Static V_2N [MeV]")
    for m_name, m_nodes in modes_a4:
        v_sum = 0.0
        d_min_m = 1e9
        for i in range(4):
            ip1, c1, rf1, s1, g1 = m_nodes[i]
            for j in range(i + 1, 4):
                ip2, c2, rf2, s2, g2 = m_nodes[j]
                res = eval_cycle_pair_3d(ip1, c1, rf1, s1, g1, ip2, c2, rf2, s2, g2,
                                         p_b, n_b, sc, couplings)
                v_sum += res[7]
                d_min_m = min(d_min_m, res[1])
        print(f"  {m_name:39s} |   {d_min_m:6.4f}    |     {v_sum:+8.2f}", flush=True)


# ======================================================================
# MASTER ENTRY POINT
# ======================================================================
def main():
    t0 = time.time()
    st_p = build_unit_radius_state(B_U_P, 1440)
    st_n = build_unit_radius_state(B_U_N, 1440)
    rst_n, rfoc_n = gonzalez_maddocks_exact_thickness(st_n)
    rst_p, _ = gonzalez_maddocks_exact_thickness(st_p)
    sc = compute_v32_relaxed_scales(st_p, st_n, rst_p, rst_n)

    wr_p = gauss_writhe_curve(st_p["r"][::2], st_p["r1"][::2] * (2.0 * st_p["dphi"]))
    wr_n = gauss_writhe_curve(st_n["r"][::2], st_n["r1"][::2] * (2.0 * st_n["dphi"]))

    run_sec1_geometry_and_meson(st_p, st_n, sc, rfoc_n, wr_p, wr_n)
    run_sec2_kelvin_bem(st_p, st_n, sc)
    mu_p, mu_n, re_p_br, re2_n, ind_pack = run_sec3_single_nucleon_ledger(st_p, st_n, sc)
    r2_ep = re_p_br ** 2

    g_s, g_m, g_b, cfb = calibrate_a2_and_run_quantum_cg(sc, mu_p, mu_n, r2_ep, re2_n)
    couplings = (g_s, g_m, g_b, cfb, r2_ep)

    d_opt_cat, del_opt_cat = run_sec6_contact_spectrum(sc, couplings)
    run_sec5_aligned_1d_strips(sc, d_opt_cat, del_opt_cat)
    run_sec7_degree1_relays(sc, couplings, d_opt_cat, del_opt_cat)
    blocks_8 = run_sec8_a3_a4_decompositions(sc, couplings, del_opt_cat)
    run_sec9_macroblocks_and_11li(sc, couplings, d_opt_cat, del_opt_cat, blocks_8)
    run_sec10_supplemental_checks(
        st_p, st_n, sc, wr_p, wr_n, mu_p, ind_pack, couplings, del_opt_cat, blocks_8
    )

    print(f"\n=== V3.2 UNIFIED CONTINUUM SUITE COMPLETE (Elapsed: {time.time() - t0:.2f} s) ===",
          flush=True)


if __name__ == "__main__":
    main()