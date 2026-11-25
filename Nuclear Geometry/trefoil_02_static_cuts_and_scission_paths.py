"""
trefoil_part2a_structural_tournaments.py  [SECTIONS 11-13 MEMORY ARCHIVE]
=========================================================================
Post-Part-1 3D Structural Tournament, Exhaustive Weakest-Link Min-Cut, &
Continuous Decay/Scission Rearrangement Memory Module (extending V3.2).

  - Sec 11: Z=3 Lithium Ring Discovery (6Li 1+/0+/3+, 7Li, mirror 7Be,
            11Li polar vs outer 2n) & 12C (Closed 3a vs Hoyle vs 6d).
  - Sec 12: Z=4..7 Ring-to-Alpha Crossover (9Be 5 modes, 10B 7 modes) &
            14C(0+) -> 14N*(trans) -> 14N(1+ cis) within-family audit.
  - Sec 13: Continuous 3D Rearrangement & Scission Tracers:
              Path 1: 14C -> 14N meridional rim-climb barrier V(theta),
              Path 2: 10B(2a+d) + n_th -> [11B*] -> 4He + 7Li* unfolding,
              Path 3: 9Be - n_b -> 8Be(2a) scission across r_e = 2.82 fm.
  - Exports all optimized geometries & cuts to `trefoil_part2a_memory.json`.
"""

import json
import time
import numpy as np
from scipy.linalg import eigh
from scipy.optimize import brentq, minimize, minimize_scalar

# ======================================================================
# FROZEN V3.2 CONSTANTS & PART-1 CALIBRATED COUPLINGS (ZERO NEW FITS)
# ======================================================================
HBAR_C = 197.3269804
ALPHA = 1.0 / 137.035999084
M_P, M_N, M_E = 938.272088, 939.565420, 0.51099895

R_E = ALPHA * HBAR_C / M_E
KAP_HOOKE = ALPHA * (M_N ** 3) / (HBAR_C ** 2)
R_PI = HBAR_C / (KAP_HOOKE * ((R_E / 3.0) ** 2))
R_2PI = 0.5 * R_PI

R0_U, A_U = 3.0 / 5.0, 2.0 / 5.0
B_U_P, B_U_N = np.sqrt(2.0) / 6.0, np.sqrt(2.0) / 3.0
RST_N = 0.014954337

R_TN = HBAR_C / (np.sqrt(3.0) * M_N)
R_TP = HBAR_C / (np.sqrt(3.0) * M_P)
L_N = R_TN / RST_N
L_P = (M_N / M_P) * L_N

G_S, G_M, G_B, C_FB = 265.97, 506.16, 21.82, +37.92
R2_EP_V32 = 0.8195 ** 2

N_S = 18
N_TAU = 3


# ======================================================================
# SHARED 3D FRAMES, PATCHED STERIC CONTACT, & SEED BLOCK BUILDERS
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


def euler_zyz(a, b, g):
    return rot_z(a) @ rot_y(b) @ rot_z(g)


def frame_from_z_and_ref(s_hat, ref_e2, gam=0.0):
    e3 = s_hat / np.linalg.norm(s_hat)
    e2 = ref_e2 - np.dot(ref_e2, e3) * e3
    if np.linalg.norm(e2) < 1e-9:
        alt = (np.array([1.0, 0.0, 0.0]) if abs(e3[0]) < 0.8
               else np.array([0.0, 1.0, 0.0]))
        e2 = alt - np.dot(alt, e3) * e3
    e2 /= np.linalg.norm(e2)
    return np.column_stack([np.cross(e2, e3), e2, e3]) @ rot_z(gam)


def exact_steric_contact_scale(u_vecs, r_loc_tau, iu, ju, r_sum_pairs):
    """Patched Part-1 contact solver: guards safe_a > 1e-18 for co-ray nodes."""
    r_cut = np.asarray(r_sum_pairs, dtype=float)
    du = u_vecs[iu] - u_vecs[ju]
    a_coef = np.sum(du ** 2, axis=-1)
    safe_a = np.where(a_coef > 1e-18, a_coef, 1.0)
    w_vec = r_loc_tau[:, iu, :, None, :] - r_loc_tau[:, ju, None, :, :]
    b_coef = np.einsum("pk,tpijk->tpij", du, w_vec)
    c_coef = np.sum(w_vec ** 2, axis=-1) - (r_cut[None, :, None, None] ** 2)
    disc = (b_coef ** 2) - a_coef[None, :, None, None] * c_coef
    mask = (disc > 0.0) & (a_coef[None, :, None, None] > 1e-18)
    if not np.any(mask):
        return 0.0
    xi_p = (-b_coef + np.sqrt(np.maximum(disc, 0.0))) / safe_a[None, :, None, None]
    return float(np.max(np.where(mask, np.maximum(0.0, xi_p), 0.0)))


def exact_probe_ray_contact(u_hat, r_probe_tau, r_core_tau, rt_probe, rt_core):
    """Exact minimum radius rho >= 0 along ray u_hat keeping probe clear."""
    w_vec = r_probe_tau[:, None, :, None, :] - r_core_tau[:, :, None, :, :]
    b_coef = np.einsum("k,tcijk->tcij", u_hat, w_vec)
    r_cut2 = ((rt_probe + rt_core)[None, :, None, None]) ** 2
    c_coef = np.sum(w_vec ** 2, axis=-1) - r_cut2
    disc = (b_coef ** 2) - c_coef
    mask = disc > 0.0
    if not np.any(mask):
        return 0.0
    rho_p = -b_coef + np.sqrt(np.maximum(disc, 0.0))
    return float(np.max(np.where(mask, np.maximum(0.0, rho_p), 0.0)))


def build_arclength_tube(b_u, l_phys, n_s=N_S):
    n_f = 1800
    phi = np.linspace(0.0, 2.0 * np.pi, n_f, endpoint=False)
    dphi = 2.0 * np.pi / n_f
    er = np.column_stack([np.sin(2.0 * phi), -np.cos(2.0 * phi), np.zeros(n_f)])
    ep = np.column_stack([np.cos(2.0 * phi), np.sin(2.0 * phi), np.zeros(n_f)])
    ez = np.array([[0.0, 0.0, 1.0]])
    rho, w = R0_U + A_U * np.cos(3.0 * phi), b_u * np.sin(3.0 * phi)
    r_u = rho[:, None] * er + w[:, None] * ez
    r1_u = ((-3.0 * A_U * np.sin(3.0 * phi))[:, None] * er
            + (2.0 * rho)[:, None] * ep
            + (3.0 * b_u * np.cos(3.0 * phi))[:, None] * ez)
    js = np.linalg.norm(r1_u, axis=1)
    lam = l_phys / float(np.sum(js * dphi))
    s_cum = np.concatenate([[0.0], np.cumsum(lam * js * dphi)])
    r_fm = np.vstack([lam * r_u, lam * r_u[0:1]])
    t_p = np.vstack([r1_u / js[:, None], (r1_u / js[:, None])[0:1]])
    s_g = np.linspace(0.0, l_phys, n_s, endpoint=False)
    r_s = np.column_stack([np.interp(s_g, s_cum, r_fm[:, c]) for c in (0, 1, 2)])
    t_s = np.column_stack([np.interp(s_g, s_cum, t_p[:, c]) for c in (0, 1, 2)])
    t_s /= np.linalg.norm(t_s, axis=1, keepdims=True)
    return r_s, t_s


def build_seed_blocks(rp0, tp0, rn0, tn0):
    """Builds steric-clear 1s (p, n), 2s (d, d_mir, nn0), 3s (3H, 3He), & 4s (4He)."""
    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, N_TAU, endpoint=False)
    ey, ez = np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])

    def eval_blk(specs, u_xi):
        nc = len(specs)
        u_v = np.array([s[2] for s in specs], float)
        u_v -= np.mean(u_v, axis=0, keepdims=True)
        is_p = np.array([s[1] for s in specs], bool)
        rt_a = np.where(is_p, R_TP, R_TN)
        ds_a = np.where(is_p, L_P / N_S, L_N / N_S)
        s_v = np.array([s[4] / np.linalg.norm(s[4]) for s in specs])
        rloc = np.zeros((N_TAU, nc, N_S, 3))
        tall = np.zeros((N_TAU, nc, N_S, 3))
        for a, (_, ip, _, rf, sx, gm) in enumerate(specs):
            r0, t0 = (rp0, tp0) if ip else (rn0, tn0)
            for it, t in enumerate(taus):
                rm = frame_from_z_and_ref(sx, rf, gm + t)
                rloc[it, a], tall[it, a] = r0 @ rm.T, t0 @ rm.T
        iu, ju = np.triu_indices(nc, k=1)
        xit = exact_steric_contact_scale(u_v, rloc, iu, ju, rt_a[iu] + rt_a[ju]) * (1.0 + 1e-12)
        xi = xit + (u_xi ** 2)
        cms = xi * u_v
        r_all = cms[None, :, None, :] + rloc
        df = r_all[:, iu, :, None, :] - r_all[:, ju, None, :, :]
        d2 = np.sum(df ** 2, axis=-1) + ((rt_a[iu] ** 2) + (rt_a[ju] ** 2))[None, :, None, None]
        d12 = np.sqrt(d2)
        g_de = (R_E ** 2) / (d2 + (R_E ** 2))
        tdot = np.einsum("tpik,tpjk->tpij", tall[:, iu], tall[:, ju])
        fac = (ds_a[iu] * ds_a[ju]) / (4.0 * np.pi * N_TAU)
        s2p = np.sum(g_de * np.exp(-d12 / R_2PI) / d12, axis=(0, 2, 3)) * fac
        m1p = np.sum(tdot * g_de * np.exp(-d12 / R_PI) / d12, axis=(0, 2, 3)) * fac
        b4p = np.sum(1.0 / (d2 ** 2), axis=(0, 2, 3)) * fac
        sdot = np.sum(s_v[iu] * s_v[ju], axis=-1)
        dcm = np.linalg.norm(cms[iu] - cms[ju], axis=-1)
        vcp = np.where(is_p[iu] & is_p[ju], ALPHA * HBAR_C / np.sqrt(dcm**2 + R2_EP_V32), 0.0)
        vp = (-G_S + C_FB * np.maximum(0.0, -sdot)) * s2p - G_M * m1p + G_B * b4p + vcp
        nodes = [(specs[a][0], specs[a][1], cms[a], specs[a][3], specs[a][4], specs[a][5])
                 for a in range(nc)]
        return float(np.sum(vp)), nodes, float(xi)

    def opt_dimer(ip1, ip2, coax_s1):
        def v_dl(dl):
            sp = ([("a", ip1, np.array([0., 0., -0.5]), ey, +ez, 0.0),
                   ("b", ip2, np.array([0., 0., +0.5]), ey, +ez, dl)] if coax_s1
                  else [("a", ip1, np.array([0., -0.5, 0.]), -ey, +ez, 0.0),
                        ("b", ip2, np.array([0., +0.5, 0.]), +ey, -ez, dl)])
            res = minimize_scalar(lambda ux: eval_blk(sp, ux)[0], bounds=(0.0, 1.4),
                                  method="bounded")
            return eval_blk(sp, float(res.x)) + (float(dl),)

        dls = np.linspace(0.0, 2.0 * np.pi / 3.0, 8, endpoint=False)
        b_dl = dls[int(np.argmin([v_dl(d)[0] for d in dls]))]
        r_dl = minimize_scalar(lambda d: v_dl(d)[0], bounds=(b_dl - 0.25, b_dl + 0.25),
                               method="bounded")
        return v_dl(float(np.mod(r_dl.x, 2.0 * np.pi / 3.0)))

    v_d, nds_d, d_deut, dl_deut = opt_dimer(True, False, True)
    _, nds_dmir, _, _ = opt_dimer(False, True, True)
    _, nds_nn0, _, _ = opt_dimer(False, False, False)

    def sp_a3(par, triton=True):
        uy, zr, ga, gb, uxi = par
        yr = 0.5 + np.exp(np.clip(uy, -3.0, 3.0))
        ipo, ipi = (True, False) if triton else (False, True)
        return [
            ("o1", ipo, np.array([0., 0., -0.5]), ey, +ez, 0.0),
            ("i1", ipi, np.array([0., 0., +0.5]), ey, +ez, ga),
            ("i2", ipi, np.array([0., yr, zr]),   ey, -ez, gb),
        ], uxi

    o_3h = minimize(lambda x: eval_blk(*sp_a3(x, True))[0],
                    [0.5, 0.0, 0.84, 1.05, 0.0], method="Nelder-Mead", options={"maxiter": 110})
    o_3he = minimize(lambda x: eval_blk(*sp_a3(x, False))[0],
                     [0.5, 0.0, 0.84, 1.05, 0.0], method="Nelder-Mead", options={"maxiter": 110})
    v_3h, nds_3h, _ = eval_blk(*sp_a3(o_3h.x, True))
    v_3he, nds_3he, _ = eval_blk(*sp_a3(o_3he.x, False))

    sp_p = np.array([-1., +1., 0.]) / np.sqrt(2.0)
    sp_n = np.array([+1., +1., 0.]) / np.sqrt(2.0)
    bp_in = np.array([-1., -1., 0.]) / np.sqrt(2.0)
    bn_in = np.array([-1., +1., 0.]) / np.sqrt(2.0)

    def sp_4he(par):
        uxn, uz, dl, uxi = par
        exn, ezv = np.exp(np.clip(uxn, -2.5, 2.5)), np.exp(np.clip(uz, -2.5, 2.5))
        return [
            ("p1", True,  np.array([+1.0, +1.0, +ezv]), +bp_in, +sp_p, 0.0),
            ("p2", True,  np.array([-1.0, -1.0, +ezv]), -bp_in, -sp_p, np.pi / 3.0),
            ("n1", False, np.array([+exn, -exn, -ezv]), +bn_in, +sp_n, dl),
            ("n2", False, np.array([-exn, +exn, -ezv]), -bn_in, -sp_n, dl + np.pi / 3.0),
        ], uxi

    o_4he = minimize(lambda x: eval_blk(*sp_4he(x))[0],
                     [0.0, -0.4, 0.5, 0.0], method="Nelder-Mead", options={"maxiter": 120})
    v_4he, nds_4he, _ = eval_blk(*sp_4he(o_4he.x))
    blks = {
        "p": [("p", True, np.zeros(3), ey, +ez, 0.0)],
        "n": [("n", False, np.zeros(3), ey, +ez, 0.0)],
        "d": nds_d, "d_mir": nds_dmir, "nn0": nds_nn0,
        "3H": nds_3h, "3He": nds_3he, "4He": nds_4he,
    }
    seed_meta = {"V_d": v_d, "d_deut_fm": d_deut, "dl_deut_rad": dl_deut,
                 "V_3H": v_3h, "V_3He": v_3he, "V_4He": v_4he}
    return blks, seed_meta


def inst(tag, u_ray, tmpl, r_m=np.eye(3)):
    return [(f"{nm}_{tag}", ip, tag, u_ray, pos @ r_m.T,
             rf @ r_m.T, sx @ r_m.T, gm) for nm, ip, pos, rf, sx, gm in tmpl]


def eval_assembly(blk_nucs, u_xi, rp0, tp0, rn0, tn0, full_audit=False):
    """Evaluates static V_tot + L1_min + exhaustive 2^(A-1)-1 W_cut + Fiedler lam2."""
    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, N_TAU, endpoint=False)
    n_tot = len(blk_nucs)
    is_p = np.array([n[1] for n in blk_nucs], bool)
    tags = [n[2] for n in blk_nucs]
    u_rays = np.array([n[3] for n in blk_nucs], float)
    u_rays -= np.mean(u_rays, axis=0, keepdims=True)
    dr_blk = np.array([n[4] for n in blk_nucs], float)
    s_vecs = np.array([n[6] / np.linalg.norm(n[6]) for n in blk_nucs])

    ds_arr = np.where(is_p, L_P / N_S, L_N / N_S)
    rt_arr = np.where(is_p, R_TP, R_TN)

    rloc = np.zeros((N_TAU, n_tot, N_S, 3))
    tall = np.zeros((N_TAU, n_tot, N_S, 3))
    for k, (_, ip, _, _, ploc, rfk, sxk, gmk) in enumerate(blk_nucs):
        r0, t0 = (rp0, tp0) if ip else (rn0, tn0)
        for it, tau in enumerate(taus):
            rm = frame_from_z_and_ref(sxk, rfk, gmk + tau)
            rloc[it, k], tall[it, k] = ploc + (r0 @ rm.T), t0 @ rm.T

    inter_p = [(i, j) for i in range(n_tot) for j in range(i + 1, n_tot) if tags[i] != tags[j]]
    iu_in, ju_in = np.array([p[0] for p in inter_p]), np.array([p[1] for p in inter_p])
    xit = exact_steric_contact_scale(
        u_rays, rloc, iu_in, ju_in, rt_arr[iu_in] + rt_arr[ju_in]
    ) * (1.0 + 1e-12)
    xi = xit + (u_xi ** 2)

    cms = xi * u_rays + dr_blk
    r_all = (xi * u_rays)[None, :, None, :] + rloc
    iu, ju = np.triu_indices(n_tot, k=1)

    df = r_all[:, iu, :, None, :] - r_all[:, ju, None, :, :]
    raw_d2 = np.sum(df ** 2, axis=-1)
    d2 = raw_d2 + ((rt_arr[iu] ** 2) + (rt_arr[ju] ** 2))[None, :, None, None]
    d12 = np.sqrt(d2)
    g_de = (R_E ** 2) / (d2 + (R_E ** 2))
    tdot = np.einsum("tpik,tpjk->tpij", tall[:, iu], tall[:, ju])

    fac_p = (ds_arr[iu] * ds_arr[ju]) / (4.0 * np.pi * N_TAU)
    s2p = np.sum(g_de * np.exp(-d12 / R_2PI) / d12, axis=(0, 2, 3)) * fac_p
    m1p = np.sum(tdot * g_de * np.exp(-d12 / R_PI) / d12, axis=(0, 2, 3)) * fac_p
    b4p = np.sum(1.0 / (d2 ** 2), axis=(0, 2, 3)) * fac_p
    sdot = np.sum(s_vecs[iu] * s_vecs[ju], axis=-1)
    dcm = np.linalg.norm(cms[iu] - cms[ju], axis=-1)
    vcp = np.where(is_p[iu] & is_p[ju], ALPHA * HBAR_C / np.sqrt(dcm**2 + R2_EP_V32), 0.0)
    vp = (-G_S + C_FB * np.maximum(0.0, -sdot)) * s2p - G_M * m1p + G_B * b4p + vcp
    v_tot = float(np.sum(vp))

    if not full_audit:
        return v_tot

    v_mat = np.zeros((n_tot, n_tot))
    v_mat[iu, ju] = v_mat[ju, iu] = vp

    holds_1 = -np.sum(v_mat, axis=1)
    i_weak1 = int(np.argmin(holds_1))
    l1_min = float(holds_1[i_weak1])
    sp_tag = "p" if is_p[i_weak1] else "n"
    weak1_str = f"{sp_tag}({tags[i_weak1]})"

    masks = np.arange(1, 1 << (n_tot - 1), dtype=np.int32)
    bits = ((masks[:, None] >> np.arange(n_tot)[None, :]) & 1)
    sizes = np.sum(bits, axis=1)
    valid = (sizes >= 2) & (sizes <= n_tot - 2)
    b_val = bits[valid].astype(float)
    w_cuts = np.sum((b_val @ (-v_mat)) * (1.0 - b_val), axis=1)
    idx_min = int(np.argmin(w_cuts))
    w_cut_min = float(w_cuts[idx_min])
    win_mask = b_val[idx_min] > 0.5
    if int(np.sum(win_mask)) > n_tot // 2:
        win_mask = ~win_mask
    zp_s, nn_s = int(np.sum(is_p[win_mask])), int(np.sum(~is_p[win_mask]))
    cut_str = f"({zp_s}p+{nn_s}n)|rest"

    w_pos = np.maximum(0.0, -v_mat)
    lap = np.diag(np.sum(w_pos, axis=1)) - w_pos
    lam_2 = float(eigh(lap, eigvals_only=True)[1])

    min_rat = float(np.min(np.sqrt(np.min(raw_d2, axis=(0, 2, 3))) / (rt_arr[iu] + rt_arr[ju])))
    r_cm = float(np.sqrt(np.mean(np.sum((cms - np.mean(cms, axis=0)) ** 2, axis=-1))))
    s_net = float(np.linalg.norm(np.sum(s_vecs, axis=0)))
    return (v_tot, l1_min, weak1_str, w_cut_min, cut_str,
            lam_2, r_cm, s_net, min_rat, cms, r_all, tall, s_vecs, is_p)


def run_opt(fn_spec, seeds, rp0, tp0, rn0, tn0, maxit=45):
    best = min(
        [minimize(
            lambda z: eval_assembly(*fn_spec(z), rp0, tp0, rn0, tn0, False),
            x0, method="Nelder-Mead", options={"maxiter": maxit}
        ) for x0 in seeds],
        key=lambda r: r.fun
    )
    return eval_assembly(*fn_spec(best.x), rp0, tp0, rn0, tn0, True), best.x


# ======================================================================
# SECTION 11: Z=3 LITHIUM RING DISCOVERY (6Li, 7Li, 7Be, 11Li) & 12C
# ======================================================================
def run_sec11_lithium_rings_and_12c(blks, rp0, tp0, rn0, tn0, registry):
    rx_pi = np.diag([1.0, -1.0, -1.0])
    angs3 = (0.0, 2.0 * np.pi / 3.0, 4.0 * np.pi / 3.0)
    th_tet = np.arccos(1.0 / 3.0)

    def li6_alpha_d(x):
        psi_a, bd, gd, uxi = x
        return (inst("a", np.array([0., 0., -0.5]), blks["4He"], rot_z(psi_a))
                + inst("d", np.array([0., 0., +0.5]), blks["d"], euler_zyz(0., bd, gd))), uxi

    def li6_bi_trimer(x):
        bt, gt, ps2, uxi = x
        rt = euler_zyz(0., bt, gt)
        return (inst("t", np.array([0., -0.5, 0.]), blks["3H"], rt)
                + inst("he", np.array([0., +0.5, 0.]), blks["3He"], rt @ rot_z(ps2))), uxi

    def li6_3d_tet_s1(x):
        yaw, roll, uxi = x
        return sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["d"],
                         rot_z(a + yaw) @ rot_y(th_tet) @ rot_z(roll))
                    for k, a in enumerate(angs3)], []), uxi

    def li6_3d_vortex_s0(x):
        yaw, roll, uxi = x
        return sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["d"],
                         rot_z(a + yaw) @ rot_x(0.5 * np.pi) @ rot_z(roll))
                    for k, a in enumerate(angs3)], []), uxi

    def li6_3d_axial_s3(x):
        r1, r2, r3, uxi = x
        rs = (r1, r2, r3)
        return sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["d"], rot_z(rs[k]))
                    for k, a in enumerate(angs3)], []), uxi

    def a7_alpha_trimer(x, is_be7=False):
        psi_a, bt, gt, uxi = x
        tri = blks["3He"] if is_be7 else blks["3H"]
        return (inst("a", np.array([0., 0., -0.5]), blks["4He"], rot_z(psi_a))
                + inst("tr", np.array([0., 0., +0.5]), tri, euler_zyz(0., bt, gt))), uxi

    def a7_tet_wheel(x, is_be7=False):
        yaw, roll, zn, uxi = x
        d_blk = blks["d_mir"] if is_be7 else blks["d"]
        hub = blks["p"] if is_be7 else blks["n"]
        ns = sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), d_blk,
                       rot_z(a + yaw) @ rot_y(th_tet) @ rot_z(roll))
                  for k, a in enumerate(angs3)], [])
        return ns + inst("hub", np.array([0., 0., zn]), hub, rx_pi), uxi

    def li7_open_chain(x):
        r1, r2, r3, uxi = x
        return (inst("d0", np.array([0., 0., -1.2]), blks["d"], rot_z(r1))
                + inst("d1", np.zeros(3), blks["d"], rot_z(r2) @ rx_pi)
                + inst("d2", np.array([0., 0., +1.2]), blks["d"], rot_z(r3))
                + inst("nh", np.array([0., 0., +2.2]), blks["n"], rx_pi)), uxi

    def li11_3t_polar_2n(x):
        yaw, tilt, uz, thn, uxi = x
        zn = 0.45 + np.exp(np.clip(uz, -2.0, 1.0))
        rn_m = rot_y(thn)
        ns = sum([inst(f"t{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["3H"],
                       rot_z(a + yaw) @ rot_x(tilt))
                  for k, a in enumerate(angs3)], [])
        return (ns + inst("nN", np.array([0., 0., +zn]), blks["n"], rn_m)
                + inst("nS", np.array([0., 0., -zn]), blks["n"], rn_m @ rx_pi)), uxi

    def li11_3t_outer_2n(x):
        yaw, tilt, ur, gn, uxi = x
        ro = 1.25 + np.exp(np.clip(ur, -1.5, 1.0))
        ns = sum([inst(f"t{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["3H"],
                       rot_z(a + yaw) @ rot_x(tilt))
                  for k, a in enumerate(angs3)], [])
        return ns + inst("2n", np.array([-ro, 0., 0.]), blks["nn0"], rot_z(gn)), uxi

    def c12_closed_3a(x):
        a1, b1, g1, uxi = x
        return sum([inst(f"a{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["4He"],
                         rot_z(a) @ euler_zyz(a1, b1, g1))
                    for k, a in enumerate(angs3)], []), uxi

    def c12_hoyle_hinge(x):
        p1, p2, th_h, uxi = x
        th = 2.09 + 0.55 * np.tanh(th_h)
        return (inst("a0", np.zeros(3), blks["4He"])
                + inst("a1", np.array([-1.0, 0.0, 0.0]), blks["4He"], rot_z(p1))
                + inst("a2", np.array([-np.cos(th), np.sin(th), 0.0]),
                       blks["4He"], rot_z(p2))), uxi

    def c12_6d_hex(x):
        tilt, roll, uxi = x
        ns = []
        for k in range(6):
            ang = 2.0 * np.pi * k / 6.0
            rb = rot_z(ang) @ rot_x(tilt) @ rot_z(roll)
            ns += inst(f"d{k}", np.array([np.cos(ang), np.sin(ang), 0.]), blks["d"],
                       (rb @ rx_pi) if (k % 2 == 1) else rb)
        return ns, uxi

    print("=== 11. WEAKEST-LINK TOURNAMENTS: Z=3 RINGS (6Li, 7Li, 7Be, 11Li) & 12C ===",
          flush=True)
    print("  [Nuclide] Architecture                  |  Static V   | Weakest 1N (Who) | "
          "Weakest Cut     |  lam2  |S|")
    print("  " + "-" * 102)
    rows = [
        ("6Li", "6Li(1+) [4+2]   Textbook a + d          ", li6_alpha_d,
         [[0., 0., 0., 0.], [0.5*np.pi, 0.5*np.pi, 0., 0.]]),
        ("6Li", "6Li(1+) [3+3]   Parallel 3H^ + 3He^     ", li6_bi_trimer,
         [[0., 0., 0.4, 0.], [0.5*np.pi, 0., 0.5, 0.]]),
        ("6Li", "6Li(1+) [2+2+2] Tet-Cone 3d Ring        ", li6_3d_tet_s1,
         [[0.5, 0.3, 0.], [0., 0., 0.]]),
        ("6Li*", "6Li(0+) [2+2+2] Chiral Vortex 3d (3563k)", li6_3d_vortex_s0,
         [[0., 0., 0.], [0.5, 0.3, 0.]]),
        ("6Li*", "6Li(3+) [2+2+2] Axial Parallel 3d(2186k)", li6_3d_axial_s3,
         [[0., 0.4, 0.8, 0.], [0.2, 0.7, 1.2, 0.]]),
        ("7Li", "7Li(3/2-) [4+3] Textbook a + 3H         ", lambda z: a7_alpha_trimer(z, False),
         [[0., 0., 0., 0.], [0.5*np.pi, 0.5*np.pi, 0., 0.]]),
        ("7Li", "7Li(3/2-) [3d+n] Tet-Cone 3d + n(hub)   ", lambda z: a7_tet_wheel(z, False),
         [[0.5, 0.3, -0.7, 0.], [0., 0., -0.5, 0.]]),
        ("7Li", "7Li(Chain) Open d---d---d---n Chain     ", li7_open_chain,
         [[0., 0.4, 0.8, 0.]]),
        ("7Be", "7Be(3/2-) [4+3] Textbook a + 3He        ", lambda z: a7_alpha_trimer(z, True),
         [[0., 0., 0., 0.], [0.5*np.pi, 0.5*np.pi, 0., 0.]]),
        ("7Be", "7Be(3/2-) [3d+p] Mirror Tet-Cone 3d + p ", lambda z: a7_tet_wheel(z, True),
         [[0.5, 0.3, -0.7, 0.], [0., 0., -0.5, 0.]]),
        ("11Li", "11Li(3/2-) [3t+2n] 3x 3H Ring + Polar 2n", li11_3t_polar_2n,
         [[0.8, 0.25, -0.1, 0.5*np.pi, 0.]]),
        ("11Li", "11Li(3/2-) [3t+2n] 3x 3H Ring + Outer 2n", li11_3t_outer_2n,
         [[0.8, 0.25, 0.0, 0.0, 0.]]),
        ("12C", "12C(0+_1) Closed C3 3a Disphenoid Ring  ", c12_closed_3a,
         [[0., 0.5*np.pi, 0., 0.], [0.4, 0.5*np.pi, 0.4, 0.]]),
        ("12C*", "12C(0+_2) Hoyle Open Bent-Arm 3a Hinge ", c12_hoyle_hinge,
         [[0.5*np.pi, 0.5*np.pi, 0.0, 0.0]]),
        ("12C", "12C(0+)   [2x6] 6d Hexagonal Ring       ", c12_6d_hex,
         [[0., 0., 0.], [0.5*np.pi, 0.3, 0.]]),
    ]
    for key_iso, title, fn, sds in rows:
        (vt, l1, w1, wc, cs, lm2, rcm, snet, *_), x_opt = run_opt(fn, sds, rp0, tp0, rn0, tn0)
        print(f"  {title} |   {vt:+9.2f} | {l1:6.1f} {w1:8s} | "
              f"{wc:6.1f} {cs:9s} | {lm2:5.1f} {snet:4.1f}", flush=True)
        registry["tournaments"].setdefault(key_iso, []).append({
            "arch": title.strip(), "V_static_MeV": vt, "L1_min_MeV": l1, "weakest_1N": w1,
            "W_cut_MeV": wc, "cut": cs, "lam2": lm2, "R_cm_fm": rcm, "x_opt": x_opt.tolist(),
        })


# ======================================================================
# SECTION 12: Z=4..7 CROSSOVER (9Be, 10B, 14C -> 14N BETA LOCK)
# ======================================================================
def run_sec12_be9_b10_c14_tournaments(blks, rp0, tp0, rn0, tn0, registry):
    rx_pi = np.diag([1.0, -1.0, -1.0])
    angs3 = (0.0, 2.0 * np.pi / 3.0, 4.0 * np.pi / 3.0)
    angs4 = (0.0, 0.5 * np.pi, np.pi, 1.5 * np.pi)
    th_tet = np.arccos(1.0 / 3.0)

    def be9_2a_n_waist(x):
        ux, zn, psi2, ths, gn, uxi = x
        xm = 0.25 + np.exp(np.clip(ux, -2.5, 1.0))
        return (inst("a1", np.array([0., 0., -0.5]), blks["4He"])
                + inst("a2", np.array([0., 0., +0.5]), blks["4He"], rot_z(psi2))
                + inst("nb", np.array([xm, 0., 0.3 * np.tanh(zn)]), blks["n"],
                       rot_y(ths) @ rot_z(gn))), uxi

    def be9_a_t_d_tri(x):
        pa, bt, gt, ps_d, sy, uxi = x
        scy = np.exp(np.clip(sy, -0.6, 0.6))
        rt = euler_zyz(0.0, bt, gt)
        return (inst("a", np.array([0., -0.6*scy, 0.]), blks["4He"], rot_z(pa))
                + inst("t", np.array([-0.85, +0.6*scy, 0.]), blks["3H"], rt)
                + inst("d", np.array([+0.85, +0.6*scy, 0.]), blks["d"],
                       rt @ rot_z(ps_d) @ rx_pi)), uxi

    def be9_3trimer_ring(x):
        bt, gt, p2, p3, sy, uxi = x
        scy = np.exp(np.clip(sy, -0.6, 0.6))
        r1 = euler_zyz(0.0, bt, gt)
        return (inst("t1", np.array([-0.866, -0.5*scy, 0.]), blks["3H"], r1)
                + inst("t2", np.array([+0.866, -0.5*scy, 0.]), blks["3H"], r1 @ rot_z(p2) @ rx_pi)
                + inst("he", np.array([0.0, +scy, 0.]), blks["3He"], r1 @ rot_z(p3))), uxi

    def be9_4d_wheel_n(x):
        roll, yaw, zn, thn, uxi = x
        ns = sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["d"],
                       rot_z(a + yaw) @ rot_x(0.5*np.pi) @ rot_z(roll))
                  for k, a in enumerate(angs4)], [])
        return ns + inst("nb", np.array([0., 0., 0.7 * np.tanh(zn)]), blks["n"], rot_y(thn)), uxi

    def be9_2a_n_chain(x):
        psi2, ths, gn, uxi = x
        return (inst("a1", np.array([0., 0., -1.0]), blks["4He"])
                + inst("a2", np.zeros(3), blks["4He"], rot_z(psi2))
                + inst("ne", np.array([0., 0., +1.1]), blks["n"], rot_y(ths) @ rot_z(gn))), uxi

    def b10_2a_d_s1(x):
        ux, psi2, bd, gd, uxi = x
        xm = 0.25 + np.exp(np.clip(ux, -2.5, 1.0))
        return (inst("a1", np.array([0., 0., -0.6]), blks["4He"])
                + inst("a2", np.array([0., 0., +0.6]), blks["4He"], rot_z(psi2))
                + inst("d", np.array([xm, 0., 0.]), blks["d"], euler_zyz(0., bd, gd))), uxi

    def b10_a_t_he3(x, anti_s0=False):
        pa, bt, gt, ps2, sy, uxi = x
        scy = np.exp(np.clip(sy, -0.6, 0.6))
        rt = euler_zyz(0., bt, gt)
        rh = (rt @ rot_z(ps2) @ rx_pi) if anti_s0 else (rt @ rot_z(ps2))
        return (inst("a", np.array([0., -0.6*scy, 0.]), blks["4He"], rot_z(pa))
                + inst("t", np.array([-0.85, +0.6*scy, 0.]), blks["3H"], rt)
                + inst("he", np.array([+0.85, +0.6*scy, 0.]), blks["3He"], rh)), uxi

    def b10_5d_s3(x):
        r1, r2, r3, uz, gp, uxi = x
        zd = 0.45 + np.exp(np.clip(uz, -2.0, 1.0))
        return (inst("d0", np.array([1., 0., 0.]), blks["d"], rot_z(r1))
                + inst("d1", np.array([-0.5, +0.866, 0.]), blks["d"], rot_z(r2))
                + inst("d2", np.array([-0.5, -0.866, 0.]), blks["d"], rot_z(r3))
                + inst("dN", np.array([0., 0., +zd]), blks["d"], rot_z(gp))
                + inst("dS", np.array([0., 0., -zd]), blks["d"], rot_z(gp + 0.5) @ rx_pi)), uxi

    def b10_5d_s1(x, vortex_s0=False):
        yaw, roll, uz, bp, gp, uxi = x
        zd = 0.45 + np.exp(np.clip(uz, -2.0, 1.0))
        rp_m = euler_zyz(0., bp, gp)
        ns = sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["d"],
                       rot_z(a + yaw) @ (rot_x(0.5*np.pi) if vortex_s0 else rot_y(th_tet))
                       @ rot_z(roll))
                  for k, a in enumerate(angs3)], [])
        return (ns + inst("dN", np.array([0., 0., +zd]), blks["d"], rp_m)
                + inst("dS", np.array([0., 0., -zd]), blks["d"], rp_m @ rx_pi)), uxi

    def c14_3a_polar_2n(x):
        a1, b1, g1, uz, thn, uxi = x
        zn = 0.42 + np.exp(np.clip(uz, -2.0, 1.0))
        rn_m = rot_y(thn)
        ns = sum([inst(f"a{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["4He"],
                       rot_z(a) @ euler_zyz(a1, b1, g1))
                  for k, a in enumerate(angs3)], [])
        return (ns + inst("nN", np.array([0., 0., +zn]), blks["n"], rn_m)
                + inst("nS", np.array([0., 0., -zn]), blks["n"], rn_m @ rx_pi)), uxi

    def c14_3a_outer_2n(x):
        a1, b1, g1, ur, gn, uxi = x
        rn_o = 1.25 + np.exp(np.clip(ur, -1.5, 1.0))
        ns = sum([inst(f"a{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["4He"],
                       rot_z(a) @ euler_zyz(a1, b1, g1))
                  for k, a in enumerate(angs3)], [])
        return ns + inst("2n", np.array([-rn_o, 0., 0.]), blks["nn0"], rot_z(gn)), uxi

    def c14_6d_polar_2n(x):
        tilt, roll, uz, thn, uxi = x
        zn = 0.42 + np.exp(np.clip(uz, -2.0, 1.0))
        rn_m = rot_y(thn)
        ns = []
        for k in range(6):
            ang = 2.0 * np.pi * k / 6.0
            rb = rot_z(ang) @ rot_x(tilt) @ rot_z(roll)
            ns += inst(f"d{k}", np.array([np.cos(ang), np.sin(ang), 0.]), blks["d"],
                       (rb @ rx_pi) if (k % 2 == 1) else rb)
        return (ns + inst("nN", np.array([0., 0., +zn]), blks["n"], rn_m)
                + inst("nS", np.array([0., 0., -zn]), blks["n"], rn_m @ rx_pi)), uxi

    def n14_trans_unrearranged(x):
        a1, b1, g1, uz, ths, uxi = x
        zn = 0.42 + np.exp(np.clip(uz, -2.0, 1.0))
        rs = rot_y(ths)
        ns = sum([inst(f"a{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["4He"],
                       rot_z(a) @ euler_zyz(a1, b1, g1))
                  for k, a in enumerate(angs3)], [])
        return (ns + inst("nN", np.array([0., 0., +zn]), blks["n"], rs)
                + inst("pS", np.array([0., 0., -zn]), blks["p"], rs)), uxi

    def n14_3a_coax_d(x):
        a1, b1, g1, ur, uz, bd, uxi = x
        rd_x, zd = 0.45 * np.tanh(ur), 0.85 * np.tanh(uz)
        ns = sum([inst(f"a{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["4He"],
                       rot_z(a) @ euler_zyz(a1, b1, g1))
                  for k, a in enumerate(angs3)], [])
        return ns + inst("dH", np.array([rd_x, 0., zd]), blks["d"], rot_y(bd)), uxi

    def n14_7d_wheel(x):
        tilt, roll, zd, bd, uxi = x
        ns = []
        for k in range(6):
            ang = 2.0 * np.pi * k / 6.0
            rb = rot_z(ang) @ rot_x(tilt) @ rot_z(roll)
            ns += inst(f"d{k}", np.array([np.cos(ang), np.sin(ang), 0.]), blks["d"],
                       (rb @ rx_pi) if (k % 2 == 1) else rb)
        return ns + inst("dH", np.array([0., 0., 0.6 * np.tanh(zd)]), blks["d"], rot_y(bd)), uxi

    print("\n=== 12. Z=4..7 RING-TO-ALPHA CROSSOVER (9Be, 10B) & 14C->14N LOCK ===",
          flush=True)
    print("  [Nuclide] Architecture                  |  Static V   | Weakest 1N (Who) | "
          "Weakest Cut     |  lam2  |S|")
    print("  " + "-" * 102)
    rows12 = [
        ("9Be", "9Be  [4+4+1] 2x 4He + Waist Bridge n    ", be9_2a_n_waist,
         [[0., 0., 0.5*np.pi, 0.5*np.pi, 0., 0.], [-0.5, 0., 0., 0., 0.4, 0.]]),
        ("9Be", "9Be  [4+3+2] 4He + 3H^ + dv Triangle    ", be9_a_t_d_tri,
         [[0., 0., 0., 0.5, 0., 0.], [0.5*np.pi, 0.5*np.pi, 0., 0.4, 0.1, 0.]]),
        ("9Be", "9Be  [3+3+3] 3He^ + 3H^ + 3Hv Trimer Rng", be9_3trimer_ring,
         [[0., 0., 0.5, 0.3, 0., 0.], [0.5*np.pi, 0., 0.5, 0.4, 0.1, 0.]]),
        ("9Be", "9Be  [2x4+1] 4x d Chiral Ring + Hub n   ", be9_4d_wheel_n,
         [[0., 0., 0., 0., 0.], [0.6, 0.4, 0.8, 0.5*np.pi, 0.]]),
        ("9Be", "9Be  [Chain] Open a --- a --- n Chain   ", be9_2a_n_chain,
         [[0.5*np.pi, 0., 0., 0.]]),
        ("10B", "10B(3+/1+) [4+4+2] 2x 4He + d(1+) Bridge", b10_2a_d_s1,
         [[0., 0.5*np.pi, 0., 0., 0.], [-0.4, 0., 0.5*np.pi, 0., 0.]]),
        ("10B", "10B(1+) [4+3+3] 4He + 3H^ + 3He^ Triang.", lambda z: b10_a_t_he3(z, False),
         [[0., 0., 0., 0.5, 0., 0.]]),
        ("10B*", "10B(0+) [4+3+3] 4He + 3H^ + 3Hev(1740k) ", lambda z: b10_a_t_he3(z, True),
         [[0., 0., 0., 0.5, 0., 0.]]),
        ("10B", "10B(3+) [2x5]   5x d Bipyramid (|S|=6)  ", b10_5d_s3,
         [[0., 0.4, 0.8, -0.2, 0., 0.]]),
        ("10B", "10B(1+) [2x5]   5x d Tet-Cone Bipyramid ", lambda z: b10_5d_s1(z, False),
         [[0., 0., -0.2, 0., 0., 0.], [0.5, 0.3, 0.2, 0.5*np.pi, 0., 0.]]),
        ("10B*", "10B(0+) [2x5]   5x d Vortex Bipyramid   ", lambda z: b10_5d_s1(z, True),
         [[0., 0., -0.2, 0., 0., 0.]]),
        ("14C", "14C(0+) [3a+2n] 3a Ring + Polar +-z 2n  ", c14_3a_polar_2n,
         [[0., 0.5*np.pi, 0., -0.2, 0.5*np.pi, 0.], [0.4, 0.5*np.pi, 0.4, 0.1, 0., 0.]]),
        ("14C", "14C(0+) [3a+2n] 3a Ring + Outer Eq 2n   ", c14_3a_outer_2n,
         [[0., 0.5*np.pi, 0., 0., 0., 0.]]),
        ("14C_6d", "14C(0+) [6d+2n] 6d Hex Ring + Polar 2n  ", c14_6d_polar_2n,
         [[0., 0., -0.2, 0.5*np.pi, 0.], [0.5*np.pi, 0.3, 0.1, 0., 0.]]),
        ("14N_tr", "14N*(1+) [Trans] Un-Rearranged nN^+pS^  ", n14_trans_unrearranged,
         [[0., 0.5*np.pi, 0., -0.2, 0.5*np.pi, 0.], [0.4, 0.5*np.pi, 0.4, 0.1, 0., 0.]]),
        ("14N_3a", "14N(1+)  [Cis]   Rearranged 3a+Coax d   ", n14_3a_coax_d,
         [[0., 0.5*np.pi, 0., 0., 0., 0., 0.], [0.4, 0.5*np.pi, 0.4, 0., 0.5, 0.5*np.pi, 0.]]),
        ("14N_7d", "14N(1+)  [7d]    6d Hex Ring + d(1+) Hub", n14_7d_wheel,
         [[0., 0., 0., 0., 0.], [0.5*np.pi, 0.3, 0.2, 0.5*np.pi, 0.]]),
    ]
    v_map = {}
    for key_iso, title, fn, sds in rows12:
        (vt, l1, w1, wc, cs, lm2, rcm, snet, *_), x_opt = run_opt(fn, sds, rp0, tp0, rn0, tn0)
        print(f"  {title} |   {vt:+9.2f} | {l1:6.1f} {w1:8s} | "
              f"{wc:6.1f} {cs:9s} | {lm2:5.1f} {snet:4.1f}", flush=True)
        registry["tournaments"].setdefault(key_iso, []).append({
            "arch": title.strip(), "V_static_MeV": vt, "L1_min_MeV": l1, "weakest_1N": w1,
            "W_cut_MeV": wc, "cut": cs, "lam2": lm2, "R_cm_fm": rcm, "x_opt": x_opt.tolist(),
        })
        v_map[key_iso] = min(v_map.get(key_iso, 1e9), vt)

    print(f"  >> Fixed Within-3a-Family Audit: 14C({v_map['14C']:+.1f}) -> "
          f"14N*_trans({v_map['14N_tr']:+.1f}) -> 14N_cis({v_map['14N_3a']:+.1f} MeV) "
          f"[Cis Gain = {v_map['14N_3a'] - v_map['14N_tr']:+.2f} MeV; "
          f"6d->7d = {v_map['14N_7d'] - v_map['14C_6d']:+.2f} MeV]")


# ======================================================================
# SECTION 13: CONTINUOUS 3D DECAY & SCISSION TRACERS (PATHS 1, 2, 3)
# ======================================================================
def run_sec13_rearrangement_tracers(blks, seed_meta, rp0, tp0, rn0, tn0, registry):
    taus = np.linspace(0.0, 2.0 * np.pi / 3.0, N_TAU, endpoint=False)
    angs3 = (0.0, 2.0 * np.pi / 3.0, 4.0 * np.pi / 3.0)
    ey, ez = np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])
    rx_pi = np.diag([1.0, -1.0, -1.0])
    th_tet = np.arccos(1.0 / 3.0)
    v_4he = seed_meta["V_4He"]

    # Path 1: 14C -> 14N*(trans) -> 14N(cis) 7-angle meridional rim climb V(theta)
    def core13_spec(x):
        a1, b1, g1, uz = x
        zn = 0.42 + np.exp(np.clip(uz, -2.0, 0.8))
        ns = sum([inst(f"a{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["4He"],
                       rot_z(a) @ euler_zyz(a1, b1, g1))
                  for k, a in enumerate(angs3)], [])
        return ns + inst("nN", np.array([0., 0., +zn]), blks["n"], np.eye(3)), 0.0

    opt13 = minimize(lambda z: eval_assembly(*core13_spec(z), rp0, tp0, rn0, tn0, False),
                     [0.0, 0.5*np.pi, 0.0, -0.2], method="Nelder-Mead", options={"maxiter": 55})
    res13 = eval_assembly(*core13_spec(opt13.x), rp0, tp0, rn0, tn0, True)
    v_core13, cms13, rall13, tall13, svecs13, isp13 = (
        res13[0], res13[9], res13[10], res13[11], res13[12], res13[13]
    )
    cm_3a = np.mean(cms13[:12], axis=0)
    cms13, rall13 = cms13 - cm_3a[None, :], rall13 - cm_3a[None, None, None, :]
    rt13 = np.where(isp13, R_TP, R_TN)
    ds13 = np.where(isp13, L_P / N_S, L_N / N_S)

    phi_notch = np.deg2rad(60.0)
    curve = []
    for th_d in (180.0, 150.0, 120.0, 90.0, 60.0, 30.0, 0.0):
        th = np.deg2rad(th_d)
        u_hat = np.array([np.sin(th) * np.cos(phi_notch),
                          np.sin(th) * np.sin(phi_notch), np.cos(th)])

        def v_probe(par):
            gp, u_dr = par
            rp_t = np.array([rp0 @ frame_from_z_and_ref(+ez, ey, gp + t).T for t in taus])
            tp_t = np.array([tp0 @ frame_from_z_and_ref(+ez, ey, gp + t).T for t in taus])
            rho_t = exact_probe_ray_contact(u_hat, rp_t, rall13, R_TP, rt13) * (1.0 + 1e-12)
            rho = rho_t + (u_dr ** 2)
            cm_p = rho * u_hat
            r_p = cm_p[None, None, :] + rp_t
            df = r_p[:, None, :, None, :] - rall13[:, :, None, :, :]
            d2 = np.sum(df ** 2, axis=-1) + ((R_TP ** 2) + (rt13 ** 2))[None, :, None, None]
            d12 = np.sqrt(d2)
            g_de = (R_E ** 2) / (d2 + (R_E ** 2))
            tdot = np.einsum("tik,tcjk->tcij", tp_t, tall13)
            fac = ((L_P / N_S) * ds13) / (4.0 * np.pi * N_TAU)
            s2c = np.sum(g_de * np.exp(-d12 / R_2PI) / d12, axis=(0, 2, 3)) * fac
            m1c = np.sum(tdot * g_de * np.exp(-d12 / R_PI) / d12, axis=(0, 2, 3)) * fac
            b4c = np.sum(1.0 / (d2 ** 2), axis=(0, 2, 3)) * fac
            dcm_c = np.linalg.norm(cm_p[None, :] - cms13, axis=-1)
            v_c = np.where(isp13, ALPHA * HBAR_C / np.sqrt(dcm_c**2 + R2_EP_V32), 0.0)
            v_int = float(np.sum(
                (-G_S + C_FB * np.maximum(0.0, -svecs13[:, 2])) * s2c
                - G_M * m1c + G_B * b4c + v_c
            ))
            return v_core13 + v_int

        bp = min([minimize(v_probe, [g0, 0.0], method="Nelder-Mead", options={"maxiter": 32})
                  for g0 in (0.0, 0.7, 1.4)], key=lambda r: r.fun)
        curve.append((th_d, float(bp.fun)))

    dv_mig = max(c[1] for c in curve) - curve[0][1]
    dv_notch = curve[3][1] - curve[0][1]
    dv_cis = curve[-1][1] - curve[0][1]

    # Path 2: 10B(2a+d) + n_th -> [11B*] -> 4He + [a+d+n] -> 4He + 7Li*[3d+n]
    def b11_dock(x):
        ux_d, ux_n, psi2, bd, gd, uxi = x
        xd = 0.25 + np.exp(np.clip(ux_d, -2.0, 0.8))
        xn = 0.25 + np.exp(np.clip(ux_n, -2.0, 0.8))
        rd = euler_zyz(0.0, bd, gd)
        return (inst("a1", np.array([0., 0., -0.75]), blks["4He"])
                + inst("a2", np.array([0., 0., +0.65]), blks["4He"], rot_z(psi2))
                + inst("d", np.array([xd, 0., +0.35]), blks["d"], rd)
                + inst("nc", np.array([-xn, 0., +0.55]), blks["n"], rd @ rx_pi)), uxi

    o11 = minimize(lambda z: eval_assembly(*b11_dock(z), rp0, tp0, rn0, tn0, False),
                   [-0.2, -0.2, 0.5*np.pi, 0., 0., 0.], method="Nelder-Mead",
                   options={"maxiter": 55})
    r11 = eval_assembly(*b11_dock(o11.x), rp0, tp0, rn0, tn0, True)

    def li7_adn(x):
        bs, gs, pa, uxi = x
        rd = euler_zyz(0., bs, gs)
        return (inst("a", np.array([0., -0.6, 0.]), blks["4He"], rot_z(pa))
                + inst("d", np.array([-0.85, +0.6, 0.]), blks["d"], rd)
                + inst("n", np.array([+0.85, +0.6, 0.]), blks["n"], rd @ rx_pi)), uxi

    def li7_whl(x):
        yaw, roll, zn, uxi = x
        ns = sum([inst(f"d{k}", np.array([np.cos(a), np.sin(a), 0.]), blks["d"],
                       rot_z(a + yaw) @ rot_y(th_tet) @ rot_z(roll))
                  for k, a in enumerate(angs3)], [])
        return ns + inst("nb", np.array([0., 0., zn]), blks["n"], rx_pi), uxi

    v_nas = float(minimize(lambda z: eval_assembly(*li7_adn(z), rp0, tp0, rn0, tn0, False),
                           [0., 0., 0., 0.], method="Nelder-Mead", options={"maxiter": 50}).fun)
    v_whl = float(minimize(lambda z: eval_assembly(*li7_whl(z), rp0, tp0, rn0, tn0, False),
                           [0.5, 0.3, -0.7, 0.], method="Nelder-Mead",
                           options={"maxiter": 50}).fun)

    # Path 3: 9Be - n_bridge -> 8Be(2a) scission curve across r_e = 2.82 fm
    nucs8 = (inst("a1", np.array([0., 0., -0.5]), blks["4He"])
             + inst("a2", np.array([0., 0., +0.5]), blks["4He"], rot_z(0.5 * np.pi)))
    isp8 = np.array([n[1] for n in nucs8], bool)
    ur8 = np.array([n[3] for n in nucs8], float)
    dr8 = np.array([n[4] for n in nucs8], float)
    sv8 = np.array([n[6] / np.linalg.norm(n[6]) for n in nucs8])
    ds8 = np.where(isp8, L_P / N_S, L_N / N_S)
    rt8 = np.where(isp8, R_TP, R_TN)
    rloc8 = np.zeros((N_TAU, 8, N_S, 3))
    tall8 = np.zeros((N_TAU, 8, N_S, 3))
    for k, (_, ip, _, _, ploc, rfk, sxk, gmk) in enumerate(nucs8):
        r0, t0 = (rp0, tp0) if ip else (rn0, tn0)
        for it, tau in enumerate(taus):
            rm = frame_from_z_and_ref(sxk, rfk, gmk + tau)
            rloc8[it, k], tall8[it, k] = ploc + (r0 @ rm.T), t0 @ rm.T
    ip_idx = [(i, j) for i in range(4) for j in range(4, 8)]
    iu8, ju8 = np.array([p[0] for p in ip_idx]), np.array([p[1] for p in ip_idx])
    fac8 = (ds8[iu8] * ds8[ju8]) / (4.0 * np.pi * N_TAU)
    sdot8 = np.sum(sv8[iu8] * sv8[ju8], axis=-1)

    def v_inter_8be(r_aa):
        cms = r_aa * ur8 + dr8
        r_all = (r_aa * ur8)[None, :, None, :] + rloc8
        df = r_all[:, iu8, :, None, :] - r_all[:, ju8, None, :, :]
        d2 = np.sum(df ** 2, axis=-1) + ((rt8[iu8]**2) + (rt8[ju8]**2))[None, :, None, None]
        d12 = np.sqrt(d2)
        g_de = (R_E ** 2) / (d2 + (R_E ** 2))
        tdot = np.einsum("tpik,tpjk->tpij", tall8[:, iu8], tall8[:, ju8])
        s2p = np.sum(g_de * np.exp(-d12 / R_2PI) / d12, axis=(0, 2, 3)) * fac8
        m1p = np.sum(tdot * g_de * np.exp(-d12 / R_PI) / d12, axis=(0, 2, 3)) * fac8
        b4p = np.sum(1.0 / (d2 ** 2), axis=(0, 2, 3)) * fac8
        dcm = np.linalg.norm(cms[iu8] - cms[ju8], axis=-1)
        vc = np.sum(np.where(isp8[iu8] & isp8[ju8],
                             ALPHA * HBAR_C / np.sqrt(dcm**2 + R2_EP_V32), 0.0))
        vb = np.sum((-G_S + C_FB * np.maximum(0.0, -sdot8)) * s2p - G_M * m1p + G_B * b4p)
        return float(vb + vc)

    r_turn_8be = float(brentq(v_inter_8be, 2.8, 4.8))

    print("\n=== 13. 3D DECAY & SCISSION REARRANGEMENT TRACERS (PATHS 1-3) ===", flush=True)
    print(f"  Path 1 (14C->14N Rim Climb) : Saddle dV_mig^‡ = {dv_mig:+.1f} MeV | "
          f"90-deg Notch = {dv_notch:+.1f} MeV | Cis Gain = {dv_cis:+.1f} MeV")
    print(f"  Path 2 (10B+n -> a + 7Li*)  : [11B*] min-cut = {r11[3]:.1f} MeV {r11[4]} | "
          f"Cleaved 4He+[a+d+n]={v_4he+v_nas:+.1f} -> Unfold [3d+n] Gain={v_whl-v_nas:+.1f} MeV")
    print(f"  Path 3 (9Be-n -> 8Be->2a)   : V_inter(r_e={R_E:.2f} fm) = "
          f"{v_inter_8be(R_E):+.2f} MeV -> Scission Turnover R_aa = {r_turn_8be:.2f} fm")
    registry["rearrangement_paths"] = {
        "14N_theta_curve_MeV": curve, "14C_barrier_MeV": dv_mig,
        "14N_90deg_notch_MeV": dv_notch, "14N_cis_gain_MeV": dv_cis,
        "11B_weakest_cut_MeV": r11[3], "11B_cut_partition": r11[4],
        "7Li_unfolding_gain_MeV": v_whl - v_nas,
        "8Be_V_at_re_MeV": v_inter_8be(R_E), "8Be_scission_turnover_fm": r_turn_8be,
    }


def main():
    t0 = time.time()
    rp0, tp0 = build_arclength_tube(B_U_P, L_P, N_S)
    rn0, tn0 = build_arclength_tube(B_U_N, L_N, N_S)
    blks, seed_meta = build_seed_blocks(rp0, tp0, rn0, tn0)

    registry = {"seed_blocks": seed_meta, "tournaments": {}, "rearrangement_paths": {}}
    run_sec11_lithium_rings_and_12c(blks, rp0, tp0, rn0, tn0, registry)
    run_sec12_be9_b10_c14_tournaments(blks, rp0, tp0, rn0, tn0, registry)
    run_sec13_rearrangement_tracers(blks, seed_meta, rp0, tp0, rn0, tn0, registry)

    with open("trefoil_part2a_memory.json", "w", encoding="utf-8") as fh:
        json.dump(registry, fh, indent=2)
    print(f"\n=== PART 2A ARCHIVE SAVED (`trefoil_part2a_memory.json`, "
          f"Elapsed: {time.time() - t0:.2f} s) ===", flush=True)


if __name__ == "__main__":
    main()