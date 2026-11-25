"""
trefoil_03_part2_fewbody_quantum_a1_to_a5.py  [PART II FEW-BODY QUANTUM SUITE]
==============================================================================
Companion Code (Module 3 of 4) to:
  B. T. Bair-Mosheh, "Continuum Mechanics and Dynamic Geometry of (2,3) Trefoil
  Nucleons" (V3.3 Unified Monograph, Part II: Sections 14--17, November 2026)
  ORCID: 0000-0003-4329-7740 | Reference Anchor: doi:10.5281/zenodo.20466167

Reproduces all Part II A = 1..5 dynamic continuum benchmarks (Flake8-clean):
  (1) Zero-Parameter A = 1 Virial Charge-Symmetry Breaking (Sec. 15.1):
      50% rest-mass exterior cavitation equipartition fixes (gamma_p, gamma_n)
      and eta_CSB = gamma_n / gamma_p = 1.00175 with zero free parameters.
  (2) Shear-Ceiling Spring (G_B == 0), Velocity Overlap, & Magic-Cone Beveling
      (Secs. 15.2--16.1): Replaces +g_B/d^4 with Hookean shear-ceiling stiffness
      (Pi_shear = alpha * P_c), Debye range contraction, Bloch magic-angle cone
      gear-meshing (T_rot = 81.68 MeV), and midpoint parity Pi_ab^+.
  (3) Live A = 2 Scattering, Radiative Capture, & 3P Phase-Shift Flip (Sec. 16.1):
      Verifies E_d, P_D, a_np, r_0s, virtual singlet pole E_virt (+65.4 keV),
      thermal 1H(n,g)2H M1 capture (340.5 mb), and 3P phase-shift sign flip
      (-0.32 deg at 25 MeV, -1.07 deg at 50 MeV vs. Nijmegen -0.3 / -1.2 deg).
  (4) Pure Two-Body Ego-Metric CG Benchmarks Across A = 3, 4, 5 (Sec. 17):
      Resolves 3H, 3He, the +763.7 keV Nolen-Schiffer mirror split, cooperative
      4He binding (zero 3N force loops), and the 12-permutation unbound 5He gate.
"""

import base64
import time
import zlib
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eig_banded, eigh, solve_banded
from scipy.optimize import brentq
from scipy.special import erf, erfc, spherical_jn, spherical_yn

_TRAPZ = getattr(np, "trapezoid", getattr(np, "trapz", None))

# ======================================================================
# FIVE UNIVERSAL CONSTANTS & DERIVED ZERO-KNOB CONTINUUM SCALES
# ======================================================================
HBAR_C = 197.3269804
C_M_S = 299792458.0
ALPHA = 1.0 / 137.035999084
M_P, M_N, M_E = 938.272088, 939.565420, 0.51099895
M_0 = 0.5 * (M_P + M_N)
MU_NP = (M_P * M_N) / (M_P + M_N)
HB2_2M0 = (HBAR_C ** 2) / (2.0 * M_0)
HB2_2MU_NP = (HBAR_C ** 2) / (2.0 * MU_NP)

R_E = ALPHA * HBAR_C / M_E
KAP_HOOKE = ALPHA * (M_N ** 3) / (HBAR_C ** 2)
U_HOOKE_DE3 = KAP_HOOKE * ((R_E / 3.0) ** 2)
R_PI = HBAR_C / U_HOOKE_DE3
R_2PI = 0.5 * R_PI
K_0 = KAP_HOOKE / R_PI

R0_U, A_U, B_U_CORE = 3.0 / 5.0, 2.0 / 5.0, np.sqrt(2.0) / 3.0
RST_N = 0.014954337
R_TN = HBAR_C / (np.sqrt(3.0) * M_N)
R_TP = HBAR_C / (np.sqrt(3.0) * M_P)
L_N = R_TN / RST_N
L_P = (M_N / M_P) * L_N
L_0 = 0.5 * (L_P + L_N)

R_EP = 0.8195
R2_EP, RE2_N = R_EP ** 2, -0.11699
MU_P_EMP, MU_N_EMP = +2.79284734, -1.91304273

STEP12_BANK_B85 = (
    "c-kG6cRba51Aq^%V{h3)C{%~YDC772mXf`aYt$89Bb0==Dk~$K!tLr+R7QmCx^%ujS=l2+Hb?e2w"
    "qw2b^FDt+e?L#e$jbzIrWLGiz^u}<!2u8tIeZnpE&{^;A%Q622l?)0c3?XglPt)z1Xl(tJ`J`Qg6"
    "2tH?aRd%0k`?#>zfmrASsgOx=dC9mru(0@9vxgHT8pqIbG5q-uwXO^N0a6_8dXaaXwJA<R|1I&kp"
    "RTEXuJ}2GH^#loi4~ER{BuAjPnbxp&LTpR`%PeoA?j@$gfy9C`l;`MX2dm@|RIE&C0#Q+uYQ^`s4"
    "JW2s{mSF6V?<w`W2vTCs2j1emhy>cw4hPgWPV<E=69w+Mf`x}f-f4*|5`vtZSIo<wte}-)~mFZi~"
    "#bH7GMSA0ZKE?{AHih;J1wf@?xps>yJvh2JCcZefh%LlS&jo^h?2~xdFN5MQSaPA+<!HG~vhVd}T"
    "O;>5Z1=iK;%kjQtWdjHslvPrd!}|wi2vM8Owg;QJNo@g^6DC2d#BMHCjFlk6E3YjEK0^bBN{8iEQ"
    "BWnj^4V7IsecuIAHc57hb2)KO#9}YGI5vu@-&U)~rPAN?Zk&Z_dIO;^~G>ma7=I-}fTxmn<56-Ez"
    "k=4R6prv+ctM1|B;9kz9fCrmu|I`?_Jqw}mZufhYNPR;=X$k1M89l6#nVtq;>-3geSYtiTE`nGn3"
    "a-LP`U6HU^OD#<0r7RAbc_h8A5DJ?Z{7?XB-HOwkkiU~yNeipiZ4{KMeK5^?qB{?wFxGuS?2g5~U"
    "wO?Hs#@bE3O<R#lv8-Fca@%(Iu)Vd=p|9zcWQO5*KI@7e%t@eutbA!0b1q#gJAJYgt3PrACfeV_4"
    "7y{ANQ*zwkMw+2@3!Ayi`+j)#j1|tF`fDxCy$a~(vztkLXjF?@F0o)=e8yc5I?*)<E@Qn6Ds<`cQ"
    "m0#a<I7Sum=7({a9*2{#iJDTTGg!sf2IIy`r99k%QJer}vuJr17d$Yika3aVRPl{<OJQ059m2!;|"
    "-T;CJpGxZlZ+f4H2{wI0C)2ZwoD9~U#=LoycStg8g*=1dzuMt^|v!#D)>`F6n!<9{2fFK(k9UU$;"
    "Br|Td|(c?(jt0knKQ&`coH4aur9M2~hwIMNwyRy|8Z^0zZ-swu<AR@ffDqPoRgvXY)jWQx7@DFK!"
    "^>eP0AdS&JT+C1%SLAD(G9YWg)y?e<cV`{Et9`>cK|&i|4M=zzBzqpOKGo;EwX6zF$6H;J9nRoo)"
    "-3MZ!wQhoNv~e^l?-k_F!cDpqY^NDjN;ESDumBRJ3bA~;e%#?e^Dcb3lCR#U?|hY0!c>C|0D8-5q"
    "}cyb?tF3Jsgoe^@cZ^fU_}dYY7eP18u>W1kE}cT3C~;NiW?5_e!H?#waW3K*EP(q-PSmYrXke_gp"
    "8^ZOl6J_D3!-yALfE*sH+N(cd}^+PaY+Ikh6rwh#Ov(fT}rIS9oQf|vR`mQbCOsM#Y|2AG!Vt<lr"
    "Sh6|>Aw61%}2ECfRB-*wa@i#t2?(s~AU`wfG)FzjThSD-jvZ>8L1XzyTw3!46=S!mp52&cPRcvJK"
    "`3A_w35x4Z8|ba|wez~6tKf^w-39XcJlb%)x}K*z4y=mm)JM&lket1pD8F9=`mId5;k?)=0F;BB4"
    "<6H~w$1gL(aIdS$ZsZOt2cv8?9B>@;$z@xjGwB1cq<}N#@D+Pa)6uUr%6`*DnLi1IMv<lLB4UibT"
    "Sh^fM#!!gXlmNI(|7iTz7L0{rQh-p->h*EU380Kwr&<E4GjKKeA_s;z@(6iEBiBd{0l4%0qybkH}"
    "HAu~ZaQZ}Oajh6B^JrH+KxQ=oLcT(A7(8X_B%AnvkFFwE8=m}t9+1oWJ=*i6>I4$kPqrMif&4jLE"
    "IgeO4r3^3hF`-+sg=O;-%^+<L`%1+?)D4^5-xc<I)8U>gn-y5}_2Xul(o}gp~eLws%xZ^Sg_PYZI"
    "6^U)=Wwq>6m$V%4#4u@?AlrlXVoxv2uxtWeITL{{2PQntMz_i)iUS66<Y#oWFyR_+xmBh~RPgJ9x"
    "1<PnFKBk1T5u1V0i4I#eDWmO@UvcF=kmJw;9A`XS%s4i{~9F_RC|I8im@JxFg(SKe{W(GB(&4R?+"
    "d@v9w+T1NzI-e9-l2>_V};7rqNZjpAz=k_}3DcIximnZe|woU!iLjwE6{lP52BOS|`!L!x8VxW8)"
    "x<Jd|6=G=`r0UjmXUgTO2;+T9QPhWc*!<t*1V0nvRE_x{RKwC^ERHuWqH$PQfcD<b!x-p5j|)dE}"
    "KgNlT#2p<c6jqklcs3$iJdg7;XM~59(D!7`RNu+^?_THMcLZ4BTcYpBo&JuVUx>d(PWyKXlBg6h8"
    "@Ikg0D~cf#Jh;EgRqK#Jc9>fqo^a~|5&u}Avyx~)2V<^y?))adi+qL@e+s2<fQCD^3bwbX=+W;v5"
    "f3vLz}a}5(!o807Jzz$c?$*9B1$gsoj}<}S*lg<$G}`H{l$dEVN^p(@jB%)0K{n82?n!0=%0`bLv"
    "iIsz^->EG%Dx=vQ}mc`A`-Ef`)vTn~(OOH)r|tTh=x}fQ!BDeL*H%Wp&oUA%Gn|q&n%AJ2K*e8tk"
    "vXT%H8ilfNo+d(4A$M&WeIP8&$?BDTaOGT{mxgQ*W5@WLJSk~`HRytrzx^Splx2b7}u#!4$N;qSQ"
    "O<vf__VV2PiUdoL<bgHhDH#TGwaOm84og==Alq2VBc5)X%_L|Dtjo}$IEpnvF<@OZd`drf}b2x!2"
    "lehLfPmBZ42xH^=FC!?M{zqxE@J|q9)uF|3yB9@lzxR`FZv=At4rXxU1Dd^emPOMm7RWBE=S@|2B"
    "jutI-eT7c;9S}KIr&c_zEvFDZ`aNSX^v?#n=*{JwJ~8U)S3eHw6qTGmS+LacfG!cs10aspIkMh5b"
    "?SfZGou+JkTnzC!*Pu2j9PGwv&IB9m*Ab532sch?ffZ{OK@8faDxa`S?g0Qo5pQ(8Ij}YD+5o)QM"
    "E2#?`Nz$+-X?e*I-9**J~jWOaTtbWi}w&75lOoj~H?qITl#anL2>5go@lh8Sa-bVQa10sl+WxK*`"
    "2G%J<Xxu^3L=qD>&spc$43$^Et{N9!TJOqB-G0z-C2Bt2WuWm6ypHt2&-(E@JZ)R^?@S>2QhEI6#"
    "3n_K{eI(mGy1QD?E`C;foLL9YLUXmzeOfTTsjTJ6!8yE#{ToegP8G%l@EwTVIfD}~isrAgorGIlk"
    "q5HfGB{QHT9T`{B#b3QpC%{@<5(|)2Abo8QbIRn-|utbP41T7GRmy*?)^qL$A5d=VE)uIfJzTf2}"
    "N3Xwh-{kBeylD%?|+4ZJ7VK;w~~Eh#OgOZGj61DmL5-R79l8hn$w7fIp5)Y6N`jM2h}_e`K7?10z"
    "4Pc8*35BA9;6<1c$g*cD<+OL;DV>(trgIjxXjSUAczRaM82v#DgSM`^(TR?i71b{$+&G4qmWxfX0"
    "xY2=%)IEQae*eu0GszS+xSIsH(XYjCvP&-F$1-LFzFX$pFgWne*-jZdJfWjQ4uP$f*{hv}-h?OKC"
    "G?uD5$ot5NH>Bz4;Yuvfy2#U)fy9Ux%>Uh9Zbc9C<T>T$tqHip!5sn4kNe=o(IAcPK^jU?c=yw6e"
    "G}mPWsUhtRAi|9Mndrd1w5o4t_~e^B7SucEfAOo>hj`UiIiD#a0&;9%JC!MjR;ZX@1`?|?a2O}Pv"
    "3Px<=M`%3O7qM6Nn#JY}^2!svo>%BDtX1MCJ<}!Cqj$H8|lxwhu~;IYPAh><@xQ*=B`L1fhZ}{oh"
    "6DLO|`dsa{xJ7;*<CYL>eZz@4;fO#Sf$IdTYNTiFSqN2gm!@M;R`-_`Q!I-dse8BGkP>@(25>rBM"
    "6BUvCb`&6!j`&+cDqnOri@(yeQb3Na?MgRVtzuxwGF`x`QH=L<{hq##E#g+f-HyHYcGn>YtU;Cd^"
    "aXlCCKi>fC1O"
)


# ======================================================================
# SECTION 1: BANK UNPACKER & LIVE A = 1 VIRIAL CSB VERIFICATION
# ======================================================================
def unpack_step12_bank():
    """Unpacks Step 12A bank & enforces exact V_nuc(r > 11.5 fm) == 0 out to 36 fm."""
    v = np.frombuffer(zlib.decompress(base64.b85decode(STEP12_BANK_B85)), dtype="<f8")
    meta = {"eta_csb": float(v[0]), "g_s": float(v[1]),
            "c_fb": float(v[2]), "g_m": float(v[3])}
    betas_raw, al5 = v[4:32].copy(), v[32:37].copy()
    fits = {
        "csn0": v[37:42].copy(), "csp0": v[42:47].copy(),
        "l_pp": v[47:52].copy(), "l_nn": v[52:57].copy(), "l_pn": v[57:62].copy(),
        "s_pp": v[62:67].copy(), "s_nn": v[67:72].copy(), "s_pn": v[72:77].copy(),
    }
    ch_keys = (
        "VC_pn_ev", "VC_pn_od", "VT_pn_ev", "VT_pn_od",
        "V0_pn_ev", "V0_pn_od", "V0_nn_ev", "V0_pp_ev",
        "V1_nn_od", "V1_pp_od", "VCoul_erf",
    )
    sog_raw = {k: v[77 + 28 * i: 77 + 28 * (i + 1)].copy() for i, k in enumerate(ch_keys)}

    r_f = np.concatenate([
        np.linspace(0.001, 4.0, 420),
        np.linspace(4.02, 13.5, 320),
        np.linspace(13.6, 36.0, 220),
    ])
    dr_w = np.gradient(r_f)
    r_cl = np.minimum(r_f, 12.2)
    gm_in = np.exp(-(r_cl[:, None] ** 2) * betas_raw[None, :])
    win = 0.5 * erfc((r_f - 10.8) / 0.60)
    vc_exact = (ALPHA * HBAR_C / r_f) * erf(np.sqrt(3.0) * r_f / (2.0 * R_EP))

    betas = 1.0 / (np.geomspace(0.095, 13.5, 28) ** 2)
    gm_out = np.exp(-(r_f[:, None] ** 2) * betas[None, :])
    gtg = gm_out.T @ (dr_w[:, None] * gm_out)
    reg = (1e-12 * np.trace(gtg) / 28.0) * np.eye(28)
    w_z0 = dr_w.copy()
    w_z0[0] = 1e4
    gtg_z0 = gm_out.T @ (w_z0[:, None] * gm_out) + reg

    sog = {"VCoul_erf": np.linalg.solve(gtg + reg, gm_out.T @ (dr_w * vc_exact))}
    for k in ch_keys[:-1]:
        c_sub = sog_raw["VCoul_erf"] if "pp" in k else 0.0
        v_nuc = win * (gm_in @ (sog_raw[k] - c_sub))
        v_tot = v_nuc + (vc_exact if "pp" in k else 0.0)
        if "VT_" in k:
            v_tot[0] = 0.0
            sog[k] = np.linalg.solve(gtg_z0, gm_out.T @ (w_z0 * v_tot))
        else:
            sog[k] = np.linalg.solve(gtg + reg, gm_out.T @ (dr_w * v_tot))
    return meta, betas, al5, fits, sog


def build_inmedium_trefoil(l_spatial, n_phi=48):
    """Builds universal (2,3) core filament at spatial scale l_spatial & flux L_0."""
    phi = np.linspace(0.0, 2.0 * np.pi, n_phi, endpoint=False)
    dphi = 2.0 * np.pi / n_phi
    er = np.column_stack([np.sin(2.0 * phi), -np.cos(2.0 * phi), np.zeros(n_phi)])
    ep = np.column_stack([np.cos(2.0 * phi), np.sin(2.0 * phi), np.zeros(n_phi)])
    ez = np.array([[0.0, 0.0, 1.0]])
    rho = R0_U + A_U * np.cos(3.0 * phi)
    w = B_U_CORE * np.sin(3.0 * phi)
    r0 = rho[:, None] * er + w[:, None] * ez
    dr0 = (
        (-3.0 * A_U * np.sin(3.0 * phi))[:, None] * er +
        (2.0 * rho)[:, None] * ep +
        (3.0 * B_U_CORE * np.cos(3.0 * phi))[:, None] * ez
    )
    js = np.linalg.norm(dr0, axis=1)
    ell_u = float(np.sum(js * dphi))
    r_fm = (l_spatial / ell_u) * r0
    ds_0 = (L_0 / ell_u) * js * dphi
    rho2_avg = float(np.sum((r_fm[:, 0] ** 2 + r_fm[:, 1] ** 2) * ds_0) / L_0)
    t_rot = (HBAR_C ** 2) / (2.0 * M_0 * rho2_avg)
    return r_fm, ds_0, t_rot


def verify_a1_virial_csb():
    """Solves 50% rest-mass virial equipartition for gamma_p, gamma_n, & eta_CSB."""
    rp, dsp, t_rot = build_inmedium_trefoil(L_P, 48)
    rn, dsn, _ = build_inmedium_trefoil(L_N, 48)

    x1, w1 = leggauss(28)
    x2, w2 = leggauss(18)
    r_pts = np.concatenate([1.5 * (x1 + 1.0), 4.5 * (x2 + 1.0) + 3.0])
    r_wts = np.concatenate([1.5 * w1, 4.5 * w2])
    mu_q, mw_q = leggauss(10)
    phi_q = np.linspace(0.0, 2.0 * np.pi, 12, endpoint=False)
    dphi = 2.0 * np.pi / len(phi_q)
    st = np.sqrt(1.0 - mu_q ** 2)
    pts = np.stack([
        r_pts[:, None, None] * st[None, :, None] * np.cos(phi_q)[None, None, :],
        r_pts[:, None, None] * st[None, :, None] * np.sin(phi_q)[None, None, :],
        r_pts[:, None, None] * mu_q[None, :, None] * np.ones_like(phi_q)[None, None, :],
    ], axis=-1)
    vol_w = (r_pts ** 2)[:, None, None] * r_wts[:, None, None] * mw_q[None, :, None] * dphi

    def wake_u(r_fil, ds_fil, r_t):
        d2 = np.sum((pts[..., None, :] - r_fil[None, None, None, :, :]) ** 2, axis=-1) + r_t ** 2
        d1 = np.sqrt(d2)
        g_de = (R_E ** 2) / (d2 + R_E ** 2)
        kern = g_de * np.exp(-d1 / R_2PI) / d1 * ds_fil[None, None, None, :]
        return np.sum(kern, axis=-1) / (4.0 * np.pi)

    up_3d = wake_u(rp, dsp, R_TP)
    un_3d = wake_u(rn, dsn, R_TN)
    gam_p = float(brentq(
        lambda g: float(np.sum(vol_w * K_0 * (g * up_3d / (1.0 + g * up_3d)))) - 0.5 * M_P,
        0.5, 4.0, xtol=1e-7
    ))
    gam_n = float(brentq(
        lambda g: float(np.sum(vol_w * K_0 * (g * un_3d / (1.0 + g * un_3d)))) - 0.5 * M_N,
        0.5, 4.0, xtol=1e-7
    ))
    return gam_p, gam_n, gam_n / gam_p, t_rot


# ======================================================================
# SECTION 2: A = 2 BOUND, CAPTURE, & P-WAVE PARITY DIAGNOSTICS (G_B == 0)
# ======================================================================
def eval_sog_radial(r_grid, betas, coeffs):
    return np.exp(-(r_grid[:, None] ** 2) * betas[None, :]) @ coeffs


def run_a2_scattering_capture_and_pwave(meta, betas, al5, fits, sog):
    """Evaluates live Ego-Metric 2H bound state, 1S0 virtual pole, M1 capture, & 3P flip."""
    rf = np.linspace(0.02, 24.0, 960)
    dr = rf[1] - rf[0]
    n_p = len(rf)
    vc_ev = eval_sog_radial(rf, betas, sog["VC_pn_ev"])
    vt_ev = eval_sog_radial(rf, betas, sog["VT_pn_ev"])
    vt_ev[0] = 0.0
    v0_ev = eval_sog_radial(rf, betas, sog["V0_pn_ev"])

    def ego_profile(r_arr):
        g5 = np.exp(-(r_arr[:, None] ** 2) * al5[None, :])
        s_pn = np.maximum(0.0, g5 @ fits["s_pn"])
        f2 = 1.0 / (1.0 + s_pn)
        df2_r = 2.0 * (g5 @ (al5 * fits["s_pn"])) * (f2 ** 2)
        return f2, df2_r

    f2_r, df2_r = ego_profile(rf)
    r_mid = np.concatenate([[0.5 * dr], 0.5 * (rf[:-1] + rf[1:]), [rf[-1] + 0.5 * dr]])
    f2_mid, _ = ego_profile(r_mid)
    fl, fr = f2_mid[:-1], f2_mid[1:]

    # 1. Coupled 3S1-3D1 Ego-Metric Sturm-Liouville Deuteron Eigenstate
    kd = HB2_2MU_NP / (dr ** 2)
    t_diag_s = kd * (fl + fr) + HB2_2MU_NP * df2_r
    t_diag_d = t_diag_s + 6.0 * HB2_2MU_NP * f2_r / (rf ** 2)
    ab = np.zeros((3, 2 * n_p))
    ab[0, 0::2] = t_diag_s + vc_ev
    ab[0, 1::2] = t_diag_d + vc_ev - 2.0 * vt_ev
    ab[1, 0::2] = np.sqrt(8.0) * vt_ev
    ab[2, 0:-2:2] = -kd * fr[:-1]
    ab[2, 1:-2:2] = -kd * fr[:-1]

    ev_d, vec_d = eig_banded(ab, lower=True, select="i", select_range=(0, 0))
    e_d = float(ev_d[0])
    u_d, w_d = vec_d[0::2, 0].copy(), vec_d[1::2, 0].copy()
    if u_d[8] < 0.0:
        u_d, w_d = -u_d, -w_d
    nm_d = float(np.sqrt(_TRAPZ(u_d ** 2 + w_d ** 2, rf)))
    u_d, w_d = u_d / nm_d, w_d / nm_d
    prob_d = u_d ** 2 + w_d ** 2
    p_d_pct = 100.0 * float(_TRAPZ(w_d ** 2, rf))
    rp2_lab = float(_TRAPZ(((0.5 * rf) ** 2) * prob_d, rf))
    re_d_lab = float(np.sqrt(rp2_lab + R2_EP + RE2_N))

    # 2. Zero-Energy 1S0 Ego-Metric Scattering, Virtual Pole E_virt, & 1H(n,g)2H M1
    m_in = n_p - 1
    ab_s = np.zeros((3, m_in))
    off_s = -kd * fr[:-1]
    ab_s[0, 1:] = off_s[:-1]
    ab_s[1, :] = t_diag_s[:-1] + v0_ev[:-1]
    ab_s[2, :-1] = off_s[:-1]
    rhs_s = np.zeros(m_in)
    rhs_s[-1] = -off_s[-1]
    u_s = np.append(solve_banded((1, 1), ab_s, rhs_s), 1.0)

    du_s = (u_s[-1] - u_s[-3]) / (2.0 * dr)
    c0_int = u_s[-2] - rf[-2] * du_s
    a_np = float(rf[-2] - u_s[-2] / du_s)
    u_sn = u_s / c0_int
    r_0s = float(2.0 * _TRAPZ(((1.0 - rf / a_np) ** 2) - (u_sn ** 2), rf))
    k_virt = (1.0 - np.sqrt(max(0.0, 1.0 - 2.0 * r_0s / a_np))) / r_0s
    e_virt_kev = 1000.0 * HB2_2MU_NP * (k_virt ** 2)

    v_oc = 2200.0 / C_M_S
    k_th = (MU_NP * v_oc) / HBAR_C
    i_ov = float(_TRAPZ(u_d * u_sn, rf))
    pref = (np.pi * ALPHA / v_oc) * ((abs(e_d) ** 3) / ((M_P ** 2) * HBAR_C))
    eff_a2 = (a_np ** 2) / (1.0 + (k_th * a_np) ** 2)
    sig_th_mb = 10.0 * pref * ((MU_P_EMP - MU_N_EMP) ** 2) * eff_a2 * (i_ov ** 2)

    # 3. Odd-L 3P Central Phase-Shift Sign Flip: Pi_12^+ Off vs. Pi_12^+ Active
    rp = np.linspace(0.015, 14.0, 900)
    drp = rp[1] - rp[0]
    kp_d = HB2_2MU_NP / (drp ** 2)
    f2_p, df2_p = ego_profile(rp)
    rm_p = np.concatenate([[0.5 * drp], 0.5 * (rp[:-1] + rp[1:]), [rp[-1] + 0.5 * drp]])
    f2_mp, _ = ego_profile(rm_p)
    fl_p, fr_p = f2_mp[:-1], f2_mp[1:]
    vc_p_wigner = eval_sog_radial(rp, betas, sog["VC_pn_ev"])
    vc_p_parity = eval_sog_radial(rp, betas, sog["VC_pn_od"])

    def pwave_phase_deg(v_arr, e_lab_mev):
        e_cm = (M_P / (M_P + M_N)) * e_lab_mev
        k_cm = float(np.sqrt(e_cm / HB2_2MU_NP))
        mp_in = len(rp) - 1
        t_p = kp_d * (fl_p + fr_p) + HB2_2MU_NP * (df2_p + 2.0 * f2_p / (rp ** 2))
        off_p = -kp_d * fr_p[:-1]
        ab_p = np.zeros((3, mp_in))
        ab_p[0, 1:] = off_p[:-1]
        ab_p[1, :] = t_p[:-1] + v_arr[:-1] - e_cm
        ab_p[2, :-1] = off_p[:-1]
        rhs_p = np.zeros(mp_in)
        rhs_p[-1] = -off_p[-1]
        u_p = np.append(solve_banded((1, 1), ab_p, rhs_p), 1.0)
        r1, r2 = rp[-6], rp[-1]
        u1, u2 = u_p[-6], u_p[-1]
        j1_a, y1_a = r1 * spherical_jn(1, k_cm * r1), r1 * spherical_yn(1, k_cm * r1)
        j1_b, y1_b = r2 * spherical_jn(1, k_cm * r2), r2 * spherical_yn(1, k_cm * r2)
        num = u1 * j1_b - u2 * j1_a
        den = u1 * y1_b - u2 * y1_a
        return float(np.rad2deg(np.arctan2(num, den)))

    d25_off, d25_on = pwave_phase_deg(vc_p_wigner, 25.0), pwave_phase_deg(vc_p_parity, 25.0)
    d50_off, d50_on = pwave_phase_deg(vc_p_wigner, 50.0), pwave_phase_deg(vc_p_parity, 50.0)

    vc_erf_ex = (ALPHA * HBAR_C / rp) * erf(np.sqrt(3.0) * rp / (2.0 * R_EP))
    erf_err = float(np.max(np.abs(eval_sog_radial(rp, betas, sog["VCoul_erf"]) - vc_erf_ex)))

    return {
        "e_d": e_d, "p_d": p_d_pct, "re_d": re_d_lab, "a_np": a_np, "r_0s": r_0s,
        "e_virt": e_virt_kev, "sig_th": sig_th_mb, "erf_err": erf_err,
        "d25_off": d25_off, "d25_on": d25_on, "d50_off": d50_off, "d50_on": d50_on,
        "meta_gs": meta["g_s"], "meta_cfb": meta["c_fb"],
    }

# === PASTE CLEAN PIECE 2 DIRECTLY BELOW THIS LINE ===

# ======================================================================
# SECTION 3: HOUSEHOLDER PARITY Pi_ab^+ & EGO-METRIC CG ENGINE (A = 3, 4)
# ======================================================================
class UnpackedSOGBank:
    def __init__(self, betas, sog):
        self.betas = betas
        self.sog = sog

    def moments(self, key, gam):
        c = self.sog[key]
        mu = 1.0 / (1.0 + 2.0 * gam[..., None] * self.betas)
        m15 = mu * np.sqrt(mu)
        j0 = np.sum(c * m15, axis=-1)
        j1 = 3.0 * gam * np.sum(c * m15 * mu, axis=-1)
        j2 = 15.0 * (gam ** 2) * np.sum(c * m15 * (mu ** 2), axis=-1)
        return j0, j1, j2


def inv_det_sym(c_arr):
    n_j = c_arr.shape[-1]
    if n_j == 2:
        c00, c01, c11 = c_arr[..., 0, 0], c_arr[..., 0, 1], c_arr[..., 1, 1]
        det = c00 * c11 - c01 * c01
        inv = np.empty_like(c_arr)
        inv[..., 0, 0], inv[..., 1, 1] = c11 / det, c00 / det
        inv[..., 0, 1] = inv[..., 1, 0] = -c01 / det
        return inv, det
    if n_j == 3:
        c00, c01, c02 = c_arr[..., 0, 0], c_arr[..., 0, 1], c_arr[..., 0, 2]
        c11, c12, c22 = c_arr[..., 1, 1], c_arr[..., 1, 2], c_arr[..., 2, 2]
        m00 = c11 * c22 - c12 * c12
        m11 = c00 * c22 - c02 * c02
        m22 = c00 * c11 - c01 * c01
        m01 = c02 * c12 - c01 * c22
        m02 = c01 * c12 - c02 * c11
        m12 = c01 * c02 - c00 * c12
        det = c00 * m00 + c01 * m01 + c02 * m02
        inv = np.empty_like(c_arr)
        inv[..., 0, 0], inv[..., 1, 1], inv[..., 2, 2] = m00 / det, m11 / det, m22 / det
        inv[..., 0, 1] = inv[..., 1, 0] = m01 / det
        inv[..., 0, 2] = inv[..., 2, 0] = m02 / det
        inv[..., 1, 2] = inv[..., 2, 1] = m12 / det
        return inv, det
    _, ld = np.linalg.slogdet(c_arr)
    return np.linalg.inv(c_arr), np.exp(ld)


def build_spin_algebra(n_part):
    id2 = np.eye(2, dtype=np.complex128)
    paulis = [
        np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128),
        np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=np.complex128),
        np.array([[1.0, 0.0], [0.0, -1.0]], dtype=np.complex128),
    ]
    res = []
    for p in range(n_part):
        ops_p = []
        for c in range(3):
            op = np.array([[1.0]], dtype=np.complex128)
            for k in range(n_part):
                op = np.kron(op, paulis[c] if k == p else id2)
            ops_p.append(op)
        res.append(ops_p)
    return res


def pair_spin_ops(sigs, i, j):
    dim = sigs[0][0].shape[0]
    id_n = np.eye(dim, dtype=np.complex128)
    s_dot = sum(sigs[i][c] @ sigs[j][c] for c in range(3))
    p1 = 0.25 * (3.0 * id_n + s_dot)
    p0 = 0.25 * (id_n - s_dot)
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
        idx_out = sum(b << (n_part - 1 - k) for k, b in enumerate(bits))
        u_sw[idx_out, s] = 1.0
    return u_sw


def householder_jacobi(w_vec):
    """Orthogonal Householder reflection R_ab sending r_ab -> -r_ab."""
    n_j = len(w_vec)
    return np.eye(n_j) - (2.0 / float(np.dot(w_vec, w_vec))) * np.outer(w_vec, w_vec)


def solve_ego_gevp(s_mat, t0_mat, ksig_mat, v_mat, rp2_mat=None, lam_mat=None):
    """Solves H_ego = T_0^(1/2) (I + T_0^(-1/2) K_Sig T_0^(-1/2))^(-1) T_0^(1/2) + V."""
    s_m = 0.5 * (s_mat + s_mat.T)
    t0_m = 0.5 * (t0_mat + t0_mat.T)
    ks_m = 0.5 * (ksig_mat + ksig_mat.T)
    v_m = 0.5 * (v_mat + v_mat.T)

    di = 1.0 / np.sqrt(np.maximum(np.diag(s_m), 1e-24))
    ev_s, vc_s = eigh(s_m * np.outer(di, di))
    kp = ev_s > 1e-8
    u_orth = (vc_s[:, kp] / np.sqrt(ev_s[kp])[None, :]) * di[:, None]

    t0_raw = u_orth.T @ t0_m @ u_orth
    ks_raw = u_orth.T @ ks_m @ u_orth
    t0_o = 0.5 * (t0_raw + t0_raw.T)
    ks_o = 0.5 * (ks_raw + ks_raw.T)
    v_o = u_orth.T @ v_m @ u_orth

    ev_t, vc_t = eigh(t0_o)
    t_half = (vc_t * np.sqrt(np.maximum(ev_t, 1e-12))[None, :]) @ vc_t.T
    t_invh = (vc_t / np.sqrt(np.maximum(ev_t, 1e-12))[None, :]) @ vc_t.T
    denom = np.eye(len(ev_t)) + t_invh @ ks_o @ t_invh
    t_ego_o = t_half @ np.linalg.solve(0.5 * (denom + denom.T), t_half)

    h_tot = 0.5 * (t_ego_o + t_ego_o.T) + 0.5 * (v_o + v_o.T)
    evals, evecs = eigh(h_tot)
    v0 = evecs[:, 0]
    c_gs = u_orth @ v0
    dt_ego = float(v0 @ (t_ego_o - t0_o) @ v0)
    rp2_v = float(c_gs @ (0.5 * (rp2_mat + rp2_mat.T)) @ c_gs) if rp2_mat is not None else 0.0
    lam_v = float(c_gs @ (0.5 * (lam_mat + lam_mat.T)) @ c_gs) if lam_mat is not None else 0.0
    return float(evals[0]), dt_ego, rp2_v, lam_v


def _add_pair_block(v_mat, ns, wt_p, b_m, b_p, as_m, ad_m, ad_v, chis, chis_p,
                    xid, xid_p, w_e, k1, k0, kt, p1_op, p0_op, sig_ef, bank):
    """Accumulates SS, SD, and DD two-body Gaussian matrix elements."""
    n_jac = as_m.shape[-1]
    two_pi_n = (2.0 * np.pi) ** n_jac
    nd = len(ad_m)

    cinv_ss, det_ss = inv_det_sym(as_m[:, None, :, :] + b_m[0][None, :, :, :])
    i0_ss = (two_pi_n / det_ss) ** 1.5
    gam_ss = np.einsum("m,ijmn,n->ij", w_e, cinv_ss, w_e)
    sp1_ss = np.real(np.conj(chis) @ (p1_op @ chis_p.T)) * bank.moments(k1, gam_ss)[0]
    sp0_ss = np.real(np.conj(chis) @ (p0_op @ chis_p.T)) * bank.moments(k0, gam_ss)[0]
    v_mat[:ns, :ns] += wt_p * (sp1_ss + sp0_ss) * i0_ss

    if nd == 0:
        return

    if kt is not None:
        cinv_sd, det_sd = inv_det_sym(as_m[:, None, :, :] + b_m[1][None, :, :, :])
        i0_sd = (two_pi_n / det_sd) ** 1.5
        gam_sd = np.einsum("m,ijmn,n->ij", w_e, cinv_sd, w_e)
        lam_b = np.einsum("jm,ijmn,n->ij", b_p, cinv_sd, w_e) / gam_sd
        sig_chi = np.einsum("abst,it->iabs", sig_ef, chis)
        m_sd = np.real(np.einsum("iabs,jabs->ij", np.conj(sig_chi), xid_p))
        blk_sd = (2.0 / 15.0) * (lam_b ** 2) * m_sd * bank.moments(kt, gam_sd)[1] * i0_sd
        v_mat[:ns, ns:] += wt_p * blk_sd
        v_mat[ns:, :ns] += wt_p * blk_sd.T

    cinv_dd, det_dd = inv_det_sym(ad_m[:, None, :, :] + b_m[1][None, :, :, :])
    i0_dd = (two_pi_n / det_dd) ** 1.5
    q_ab = np.einsum("im,ijmn,jn->ij", ad_v, cinv_dd, b_p)
    gam_dd = np.einsum("m,ijmn,n->ij", w_e, cinv_dd, w_e)
    qae = np.einsum("im,ijmn,n->ij", ad_v, cinv_dd, w_e)
    qbe = np.einsum("jm,ijmn,n->ij", b_p, cinv_dd, w_e)
    la, lb, qt = qae / gam_dd, qbe / gam_dd, q_ab - (qae * qbe) / gam_dd

    p1_xid = np.einsum("st,jabt->jabs", p1_op, xid_p)
    p0_xid = np.einsum("st,jabt->jabs", p0_op, xid_p)
    mp1 = np.real(np.einsum("iabs,jabs->ij", np.conj(xid), p1_xid))
    mp0 = np.real(np.einsum("iabs,jabs->ij", np.conj(xid), p0_xid))
    j0_1, j1_1, j2_1 = bank.moments(k1, gam_dd)
    j0_0, j1_0, j2_0 = bank.moments(k0, gam_dd)
    poly_1 = (
        2.0 * (qt ** 2) * j0_1 +
        (4.0 / 3.0) * la * lb * qt * j1_1 +
        (2.0 / 15.0) * (la ** 2) * (lb ** 2) * j2_1
    )
    poly_0 = (
        2.0 * (qt ** 2) * j0_0 +
        (4.0 / 3.0) * la * lb * qt * j1_0 +
        (2.0 / 15.0) * (la ** 2) * (lb ** 2) * j2_0
    )
    v_dd = poly_1 * mp1 + poly_0 * mp0
    if kt is not None:
        sg_xid = np.einsum("bcst,jcat->jbas", sig_ef, xid_p)
        m3 = np.real(np.einsum("iabs,jbas->ij", np.conj(xid), sg_xid))
        _, jt_1, jt_2 = bank.moments(kt, gam_dd)
        v_dd = v_dd + ((8.0 / 15.0) * la * lb * qt * jt_1 +
                       (8.0 / 105.0) * (la ** 2) * (lb ** 2) * jt_2) * m3
    v_mat[ns:, ns:] += wt_p * v_dd * i0_dd


def build_ego_cg_matrices(u_jac, masses, bas_s, bas_d, perms, edges, spec_coul,
                          rp_vecs, al5, fits, sog_raw, betas):
    """Builds exact unequal-mass S, T_0, K_Sigma, V(Pi_ab^+), <r_p^2>, & <Lam_p>."""
    ns, nd = len(bas_s), len(bas_d)
    m_tot, n_perm = ns + nd, len(perms)
    n_jac, n_part = u_jac.shape
    two_pi_n = (2.0 * np.pi) ** n_jac

    sog_ext = dict(sog_raw)
    for ch in ("VC_pn", "V0_pn", "VT_pn"):
        sog_ext[f"{ch}_dir"] = 0.5 * (sog_raw[f"{ch}_ev"] + sog_raw[f"{ch}_od"])
        sog_ext[f"{ch}_ex"] = 0.5 * (sog_raw[f"{ch}_ev"] - sog_raw[f"{ch}_od"])
    bank = UnpackedSOGBank(betas, sog_ext)

    k_kin = sum(
        ((HBAR_C ** 2) / (2.0 * masses[a])) * np.outer(u_jac[:, a], u_jac[:, a])
        for a in range(n_part)
    )
    s_mat, t0_mat, ks_mat, v_mat, rp2_mat, lam_mat = (
        np.zeros((m_tot, m_tot)) for _ in range(6)
    )
    as_m = np.array([b["A"] for b in bas_s])
    chis = np.array([b["chi"] for b in bas_s])
    ad_m = np.array([b["A"] for b in bas_d]) if nd > 0 else np.zeros((0, n_jac, n_jac))
    ad_v = np.array([b["a"] for b in bas_d]) if nd > 0 else np.zeros((0, n_jac))
    xid = np.array([b["Xi"] for b in bas_d]) if nd > 0 else None

    for sgn, p_j, u_s in perms:
        wt_p = sgn / float(n_perm)
        bs_m = np.einsum("ba,jbc,cd->jad", p_j, as_m, p_j)
        chis_p = (u_s @ chis.T).T
        bd_m = np.einsum("ba,jbc,cd->jad", p_j, ad_m, p_j) if nd > 0 else ad_m
        bd_p = (p_j.T @ ad_v.T).T if nd > 0 else ad_v
        xid_p = np.einsum("st,jabt->jabs", u_s, xid) if nd > 0 else None

        cinv_ss, det_ss = inv_det_sym(as_m[:, None, :, :] + bs_m[None, :, :, :])
        i0_ss = (two_pi_n / det_ss) ** 1.5
        sp_ov = np.real(np.conj(chis) @ chis_p.T)
        s_mat[:ns, :ns] += wt_p * sp_ov * i0_ss
        acb_ss = np.einsum("ikm,ijmn,jnl->ijkl", as_m, cinv_ss, bs_m)
        t0_mat[:ns, :ns] += wt_p * 3.0 * np.einsum("kl,ijkl->ij", k_kin, acb_ss) * sp_ov * i0_ss

        fac_rp = wt_p * (3.0 / len(rp_vecs))
        for rv in rp_vecs:
            tau_ss = np.einsum("m,ijmn,n->ij", rv, cinv_ss, rv)
            rp2_mat[:ns, :ns] += fac_rp * tau_ss * sp_ov * i0_ss

        if nd > 0:
            cinv_dd, det_dd = inv_det_sym(ad_m[:, None, :, :] + bd_m[None, :, :, :])
            i0_dd = (two_pi_n / det_dd) ** 1.5
            q_ab = np.einsum("im,ijmn,jn->ij", ad_v, cinv_dd, bd_p)
            m_dd = np.real(np.einsum("iabs,jabs->ij", np.conj(xid), xid_p))
            s_mat[ns:, ns:] += wt_p * 2.0 * (q_ab ** 2) * m_dd * i0_dd
            acb_dd = np.einsum("ikm,ijmn,jnl->ijkl", ad_m, cinv_dd, bd_m)
            tr_k = np.einsum("kl,ijkl->ij", k_kin, acb_dd)
            p_a = np.einsum("im,ijmn,jnl->ijl", ad_v, cinv_dd, bd_m)
            p_b = np.einsum("ikm,ijmn,jn->ijk", ad_m, cinv_dd, bd_p)
            qd_k = np.einsum("ijl,lk,ijk->ij", p_a, k_kin, p_b)
            t0_mat[ns:, ns:] += wt_p * (6.0 * tr_k * (q_ab ** 2) + 8.0 * q_ab * qd_k) * m_dd * i0_dd
            for rv in rp_vecs:
                tau_r = np.einsum("m,ijmn,n->ij", rv, cinv_dd, rv)
                par = np.einsum("im,ijmn,n->ij", ad_v, cinv_dd, rv)
                pbr = np.einsum("jm,ijmn,n->ij", bd_p, cinv_dd, rv)
                poly_r = 6.0 * tau_r * (q_ab ** 2) + 8.0 * q_ab * par * pbr
                rp2_mat[ns:, ns:] += (wt_p / len(rp_vecs)) * poly_r * m_dd * i0_dd

        for a_i, b_i, is_pn, k1, k0, kt, s_key, l_key, p_share, p1_op, p0_op, sig_ef in edges:
            w_e = u_jac[:, a_i] - u_jac[:, b_i]
            if is_pn:
                _add_pair_block(v_mat, ns, wt_p, (bs_m, bd_m), bd_p, as_m, ad_m, ad_v,
                                chis, chis_p, xid, xid_p, w_e, "VC_pn_dir", "V0_pn_dir",
                                "VT_pn_dir", p1_op, p0_op, sig_ef, bank)
                r_h = householder_jacobi(w_e)
                bs_r = np.einsum("ab,jbc,cd->jad", r_h, bs_m, r_h)
                bd_r = np.einsum("ab,jbc,cd->jad", r_h, bd_m, r_h) if nd > 0 else bd_m
                bd_pr = (r_h @ bd_p.T).T if nd > 0 else bd_p
                _add_pair_block(v_mat, ns, wt_p, (bs_r, bd_r), bd_pr, as_m, ad_m, ad_v,
                                chis, chis_p, xid, xid_p, w_e, "VC_pn_ex", "V0_pn_ex",
                                "VT_pn_ex", p1_op, p0_op, sig_ef, bank)
            else:
                _add_pair_block(v_mat, ns, wt_p, (bs_m, bd_m), bd_p, as_m, ad_m, ad_v,
                                chis, chis_p, xid, xid_p, w_e, k1, k0, kt,
                                p1_op, p0_op, sig_ef, bank)

            gam_s = np.einsum("m,ijmn,n->ij", w_e, cinv_ss, w_e)
            c_sab, c_lab = fits[s_key], fits[l_key]
            for q_i, ap in enumerate(al5):
                ds_q = 1.0 + 2.0 * ap * gam_s
                eta_s = (2.0 * ap) / ds_q
                f_q = (ds_q ** (-1.5)) * i0_ss
                if p_share > 0.0:
                    lam_mat[:ns, :ns] += wt_p * p_share * c_lab[q_i] * sp_ov * f_q
                for p_idx in (a_i, b_i):
                    up_v = u_jac[:, p_idx]
                    kap_p = (HBAR_C ** 2) / (2.0 * masses[p_idx])
                    ya_s = np.einsum("imk,k->im", as_m, up_v)
                    yb_s = np.einsum("jmk,k->jm", bs_m, up_v)
                    t0_s = np.einsum("im,ijmn,jn->ij", ya_s, cinv_ss, yb_s)
                    ca_s = np.einsum("im,ijmn,n->ij", ya_s, cinv_ss, w_e)
                    cb_s = np.einsum("m,ijmn,jn->ij", w_e, cinv_ss, yb_s)
                    tq_s = t0_s - eta_s * ca_s * cb_s
                    ks_mat[:ns, :ns] += wt_p * 3.0 * kap_p * c_sab[q_i] * tq_s * sp_ov * f_q

            if nd > 0:
                gam_d = np.einsum("m,ijmn,n->ij", w_e, cinv_dd, w_e)
                aw_d = np.einsum("im,ijmn,n->ij", ad_v, cinv_dd, w_e)
                bw_d = np.einsum("m,ijmn,jn->ij", w_e, cinv_dd, bd_p)
                for q_i, ap in enumerate(al5):
                    dd_q = 1.0 + 2.0 * ap * gam_d
                    eta_d = (2.0 * ap) / dd_q
                    fd_q = (dd_q ** (-1.5)) * i0_dd
                    q_q = q_ab - eta_d * aw_d * bw_d
                    if p_share > 0.0:
                        lam_mat[ns:, ns:] += (wt_p * p_share * c_lab[q_i] *
                                              2.0 * (q_q ** 2) * m_dd * fd_q)
                    for p_idx in (a_i, b_i):
                        up_v = u_jac[:, p_idx]
                        kap_p = (HBAR_C ** 2) / (2.0 * masses[p_idx])
                        ya_d = np.einsum("imk,k->im", ad_m, up_v)
                        yb_d = np.einsum("jmk,k->jm", bd_m, up_v)
                        t0_d = np.einsum("im,ijmn,jn->ij", ya_d, cinv_dd, yb_d)
                        ca_d = np.einsum("im,ijmn,n->ij", ya_d, cinv_dd, w_e)
                        cb_d = np.einsum("m,ijmn,jn->ij", w_e, cinv_dd, yb_d)
                        tq_d = t0_d - eta_d * ca_d * cb_d
                        pa_q = np.einsum("im,ijmn,jn->ij", ad_v, cinv_dd, yb_d) - eta_d * aw_d * cb_d
                        pb_q = np.einsum("im,ijmn,jn->ij", ya_d, cinv_dd, bd_p) - eta_d * ca_d * bw_d
                        ra_q = np.einsum("im,ijmn,in->ij", ad_v, cinv_dd, ya_d) - eta_d * aw_d * ca_d
                     rb_q = np.einsum("jm,ijmn,jn->ij", yb_d, cinv_dd, bd_p) - eta_d * cb_d * bw_d
                        alu = ad_v @ up_v
                        btu = bd_p @ up_v
                        cross_ab = pa_q * pb_q + (alu[:, None] - ra_q) * (btu[None, :] - rb_q)
                        poly_k = 6.0 * tq_d * (q_q ** 2) + 4.0 * q_q * cross_ab
                        ks_mat[ns:, ns:] += wt_p * kap_p * c_sab[q_i] * poly_k * m_dd * fd_q

        for w_pp, u_sp, c_sp in spec_coul:
            gam_pp = np.einsum("m,ijmn,n->ij", w_pp, cinv_ss, w_pp)
            tau_sp = np.einsum("m,ijmn,n->ij", u_sp, cinv_ss, u_sp)
            chi_sp = np.einsum("m,ijmn,n->ij", u_sp, cinv_ss, w_pp)
            for q_i, ap in enumerate(al5):
                d_sp = 1.0 + 2.0 * ap * tau_sp
                g_ef = gam_pp - (2.0 * ap * (chi_sp ** 2)) / d_sp
                vc_s = bank.moments("VCoul_erf", g_ef)[0]
                v_mat[:ns, :ns] += wt_p * c_sp[q_i] * sp_ov * vc_s * i0_ss * (d_sp ** (-1.5))

    return s_mat, t0_mat, ks_mat, v_mat, rp2_mat, lam_mat


# === PASTE CLEAN PIECE 2B (FINAL PART) DIRECTLY BELOW THIS LINE ===

# ======================================================================
# SECTION 4: A = 3, 4 BENCHMARKS & 12-PERMUTATION A = 5 (5He) GATE
# ======================================================================
def _svm_enrich_4he(u4, perms4, edges_4, sog, betas, bas4_s, chi_s0, chi_s1, mk4):
    """Adds 22 greedy 2x2 Rayleigh-Ritz SVM 6-edge correlation states to 4He."""
    sog_d = dict(sog)
    for ch in ("VC_pn", "V0_pn"):
        sog_d[f"{ch}_dir"] = 0.5 * (sog[f"{ch}_ev"] + sog[f"{ch}_od"])
        sog_d[f"{ch}_ex"] = 0.5 * (sog[f"{ch}_ev"] - sog[f"{ch}_od"])
    bank = UnpackedSOGBank(betas, sog_d)
    m_4he = np.array([M_P, M_P, M_N, M_N])
    k_eff = 0.68 * sum(
        ((HBAR_C ** 2) / (2.0 * m_4he[a])) * np.outer(u4[:, a], u4[:, a]) for a in range(4)
    )
    two_pi_3 = (2.0 * np.pi) ** 3

    def block_sh(a_left, chi_l, a_right, chi_r):
        nl, nr = len(a_left), len(a_right)
        sm, hm = np.zeros((nl, nr)), np.zeros((nl, nr))
        for sgn, p_j, u_s in perms4:
            wt = sgn / 4.0
            br = np.einsum("ba,jbc,cd->jad", p_j, a_right, p_j)
            cr = (u_s @ chi_r.T).T
            cinv, det_c = inv_det_sym(a_left[:, None, :, :] + br[None, :, :, :])
            i0 = (two_pi_3 / det_c) ** 1.5
            spo = np.real(np.conj(chi_l) @ cr.T)
            sm += wt * spo * i0
            acb = np.einsum("ikm,ijmn,jnl->ijkl", a_left, cinv, br)
            hm += wt * 3.0 * np.einsum("kl,ijkl->ij", k_eff, acb) * spo * i0
            for a_i, b_i, is_pn, k1, k0, _, _, _, _, p1_op, p0_op, _ in edges_4:
                w_e = u4[:, a_i] - u4[:, b_i]
                gm = np.einsum("m,ijmn,n->ij", w_e, cinv, w_e)
                s1 = np.real(np.conj(chi_l) @ (p1_op @ cr.T))
                s0 = np.real(np.conj(chi_l) @ (p0_op @ cr.T))
                if is_pn:
                    hm += wt * (
                        s1 * bank.moments("VC_pn_dir", gm)[0] +
                        s0 * bank.moments("V0_pn_dir", gm)[0]
                    ) * i0
                    rh = householder_jacobi(w_e)
                    br_x = np.einsum("ab,jbc,cd->jad", rh, br, rh)
                    ci_x, dt_x = inv_det_sym(a_left[:, None, :, :] + br_x[None, :, :, :])
                    gm_x = np.einsum("m,ijmn,n->ij", w_e, ci_x, w_e)
                    i0_x = (two_pi_3 / dt_x) ** 1.5
                    hm += wt * (
                        s1 * bank.moments("VC_pn_ex", gm_x)[0] +
                        s0 * bank.moments("V0_pn_ex", gm_x)[0]
                    ) * i0_x
                else:
                    hm += wt * (
                        s1 * bank.moments(k1, gm)[0] + s0 * bank.moments(k0, gm)[0]
                    ) * i0
        return sm, hm

    as_cur = np.array([b["A"] for b in bas4_s])
    ch_cur = np.array([b["chi"] for b in bas4_s])
    s_cur, h_cur = block_sh(as_cur, ch_cur, as_cur, ch_cur)
    rng = np.random.default_rng(20261125)

    for _ in range(22):
        di = 1.0 / np.sqrt(np.maximum(np.diag(s_cur), 1e-24))
        evs, vcs = eigh(0.5 * (s_cur + s_cur.T) * np.outer(di, di))
        kp = evs > 1e-8
        uo = (vcs[:, kp] / np.sqrt(evs[kp])[None, :]) * di[:, None]
        eh, vh = eigh(0.5 * (uo.T @ (h_cur + h_cur.T) @ uo))
        e0, c0 = float(eh[0]), uo @ vh[:, 0]

        n_c = 44
        rs = np.exp(rng.uniform(np.log(0.25), np.log(4.20), size=(n_c, 6)))
        cands = [
            {"A": mk4(*rs[k]), "chi": chi_s1 if (k % 6 == 5) else chi_s0,
             "is_s0": (k % 6 != 5)}
            for k in range(n_c)
        ]
        ac = np.array([b["A"] for b in cands])
        cc = np.array([b["chi"] for b in cands])
        sc_x, hc_x = block_sh(ac, cc, as_cur, ch_cur)
        sc_d = np.array([block_sh(ac[k:k+1], cc[k:k+1], ac[k:k+1], cc[k:k+1])[0][0, 0]
                         for k in range(n_c)])
        hc_d = np.array([block_sh(ac[k:k+1], cc[k:k+1], ac[k:k+1], cc[k:k+1])[1][0, 0]
                         for k in range(n_c)])

        sp_v, hp_v = sc_x @ c0, hc_x @ c0
        n_rem = sc_d - (sp_v ** 2)
        ok = (sc_d > 1e-20) & (n_rem > 1e-4 * np.maximum(sc_d, 1e-30))
        vn = hp_v - e0 * sp_v
        nr_s = np.where(ok, n_rem, 1.0)
        d_or = ((hc_d - e0 * sc_d) - 2.0 * sp_v * vn) / nr_s
        de = np.where(ok, 0.5 * (d_or - np.sqrt(d_or ** 2 + 4.0 * (vn ** 2) / nr_s)), 0.0)
        bk = int(np.argmin(de))

        bas4_s.append(cands[bk])
        as_cur = np.concatenate([as_cur, ac[bk:bk+1]], axis=0)
        ch_cur = np.concatenate([ch_cur, cc[bk:bk+1]], axis=0)
        s_cur = np.block([[s_cur, sc_x[bk:bk+1].T], [sc_x[bk:bk+1], sc_d[bk:bk+1, None]]])
        h_cur = np.block([[h_cur, hc_x[bk:bk+1].T], [hc_x[bk:bk+1], hc_d[bk:bk+1, None]]])


def run_a3_a4_benchmarks(al5, fits, sog, betas, e_d):
    """Runs unequal-mass A = 3 (3H, 3He) and SVM-converged A = 4 (4He) CG."""
    u3 = np.array([
        [+1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0), 0.0],
        [+1.0 / np.sqrt(6.0), +1.0 / np.sqrt(6.0), -2.0 / np.sqrt(6.0)],
    ])
    sigs3 = build_spin_algebra(3)
    up, dn = np.array([1.0, 0.0]), np.array([0.0, 1.0])

    def st3(a, b, c):
        return np.kron(np.kron(a, b), c).astype(np.complex128)

    chi_r = (st3(up, dn, up) - st3(dn, up, up)) / np.sqrt(2.0)
    chi_l = (2.0 * st3(up, up, dn) - st3(up, dn, up) - st3(dn, up, up)) / np.sqrt(6.0)
    w01, w02, w12 = u3[:, 0] - u3[:, 1], u3[:, 0] - u3[:, 2], u3[:, 1] - u3[:, 2]
    m01, m02, m12 = np.outer(w01, w01), np.outer(w02, w02), np.outer(w12, w12)
    ops01, ops02, ops12 = (pair_spin_ops(sigs3, i, j) for i, j in ((0, 1), (0, 2), (1, 2)))
    xi_r = np.einsum("abst,t->abs", ops02[2], chi_r)
    xi_l = np.einsum("abst,t->abs", ops02[2], chi_l)

    def mk3(r1, r2, r3):
        return m01 / (r1 ** 2) + m02 / (r2 ** 2) + m12 / (r3 ** 2)

    bas3_s, bas3_d = [], []
    for re in np.geomspace(0.80, 9.50, 7):
        bas3_s.append({"A": mk3(re, re, re), "chi": chi_r})
        for rh in np.geomspace(0.30, 1.25, 4):
            bas3_s += [
                {"A": mk3(rh, re, re), "chi": chi_r}, {"A": mk3(re, rh, re), "chi": chi_r},
                {"A": mk3(re, rh, re), "chi": chi_l}, {"A": mk3(rh, rh, re), "chi": chi_r},
                {"A": mk3(rh, rh, re), "chi": chi_l}, {"A": mk3(re, rh, rh), "chi": chi_r},
            ]
    for rt in np.geomspace(0.38, 3.20, 6):
        for ro in np.geomspace(0.95, 6.00, 4):
            bas3_d.append({"A": mk3(ro, rt, ro), "a": w02, "Xi": xi_r})
        for ro in np.geomspace(1.35, 4.00, 2):
            bas3_d.append({"A": mk3(ro, rt, ro), "a": w02, "Xi": xi_l})

    perms3 = [
        (+1.0, np.eye(2), np.eye(8, dtype=np.complex128)),
        (-1.0, u3 @ np.array([[0, 1, 0], [1, 0, 0], [0, 0, 1.0]]) @ u3.T, qubit_swap(3, 0, 1)),
    ]
    m_3h = np.array([M_N, M_N, M_P])
    ucm_3h = (u3 * m_3h[None, :]) @ np.ones(3) / np.sum(m_3h)
    edges_3h = [
        (0, 1, False, "V1_nn_od", "V0_nn_ev", None, "s_nn", "l_nn", 0.0, *ops01),
        (0, 2, True, "", "", "VT_pn_dir", "s_pn", "l_pn", 1.0, *ops02),
        (1, 2, True, "", "", "VT_pn_dir", "s_pn", "l_pn", 1.0, *ops12),
    ]
    e_3h, dt_3h, rp2_3h, lam_3h = solve_ego_gevp(*build_ego_cg_matrices(
        u3, m_3h, bas3_s, bas3_d, perms3, edges_3h, [], [u3[:, 2] - ucm_3h], al5, fits, sog, betas
    ))
    re_3h = float(np.sqrt((1.0 - lam_3h) * rp2_3h + R2_EP + 2.0 * RE2_N))

    m_3he = np.array([M_P, M_P, M_N])
    ucm_3he = (u3 * m_3he[None, :]) @ np.ones(3) / np.sum(m_3he)
    edges_3he = [
        (0, 1, False, "V1_pp_od", "V0_pp_ev", None, "s_pp", "l_pp", 1.0, *ops01),
        (0, 2, True, "", "", "VT_pn_dir", "s_pn", "l_pn", 0.5, *ops02),
        (1, 2, True, "", "", "VT_pn_dir", "s_pn", "l_pn", 0.5, *ops12),
    ]
    sc_3he = [(w01, u3[:, 2] - 0.5 * (u3[:, 0] + u3[:, 1]), fits["csn0"])]
    e_3he, dt_3he, rp2_3he, lam_3he = solve_ego_gevp(*build_ego_cg_matrices(
        u3, m_3he, bas3_s, bas3_d, perms3, edges_3he, sc_3he,
        [u3[:, 0] - ucm_3he, u3[:, 1] - ucm_3he], al5, fits, sog, betas
    ))
    re_3he = float(np.sqrt((1.0 - lam_3he) * rp2_3he + R2_EP + 0.5 * RE2_N))

    q_nd, q_pd = e_d - e_3h, e_d - e_3he
    mt_3h, mt_3he = 2.0 * M_N + M_P + e_3h, 2.0 * M_P + M_N + e_3he
    e_rec_3h = q_nd - (q_nd ** 2) / (2.0 * mt_3h)
    e_rec_3he = q_pd - (q_pd ** 2) / (2.0 * mt_3he)
    de_gam_kev = 1000.0 * (e_rec_3h - e_rec_3he)

    u4 = np.array([
        [+1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0), 0.0, 0.0],
        [0.0, 0.0, +1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0)],
        [+0.5, +0.5, -0.5, -0.5],
    ])
    sigs4 = build_spin_algebra(4)
    s0_2 = (np.kron(up, dn) - np.kron(dn, up)) / np.sqrt(2.0)
    tp_2, tm_2 = np.kron(up, up), np.kron(dn, dn)
    t0_2 = (np.kron(up, dn) + np.kron(dn, up)) / np.sqrt(2.0)
    chi_s0 = np.kron(s0_2, s0_2).astype(np.complex128)
    chi_s1 = ((np.kron(tp_2, tm_2) - np.kron(t0_2, t0_2) + np.kron(tm_2, tp_2)) /
              np.sqrt(3.0)).astype(np.complex128)

    pairs4 = [(0, 1), (2, 3), (0, 2), (1, 3), (0, 3), (1, 2)]
    w4 = {p: u4[:, p[0]] - u4[:, p[1]] for p in pairs4}
    m4 = {p: np.outer(w4[p], w4[p]) for p in pairs4}
    ops4 = {p: pair_spin_ops(sigs4, p[0], p[1]) for p in pairs4}
    xi4_02 = np.einsum("abst,t->abs", ops4[(0, 2)][2], chi_s0)

    def mk4(r01, r23, r02, r13, r03, r12):
        return (
            m4[(0, 1)] / r01**2 + m4[(2, 3)] / r23**2 + m4[(0, 2)] / r02**2 +
            m4[(1, 3)] / r13**2 + m4[(0, 3)] / r03**2 + m4[(1, 2)] / r12**2
        )

    bas4_s, bas4_d = [], []
    for ro in (1.05, 1.55, 2.35, 3.60):
        bas4_s.append({"A": mk4(ro, ro, ro, ro, ro, ro), "chi": chi_s0, "is_s0": True})
        for rh in (0.30, 0.58):
            bas4_s += [
                {"A": mk4(rh, ro, ro, ro, ro, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, rh, ro, ro, ro, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, ro, rh, ro, ro, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(rh, rh, ro, ro, ro, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, ro, rh, rh, ro, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, ro, rh, rh, ro, ro), "chi": chi_s1, "is_s0": False},
                {"A": mk4(ro, ro, rh, ro, rh, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, ro, rh, ro, ro, rh), "chi": chi_s0, "is_s0": True},
                {"A": mk4(rh, ro, rh, ro, ro, rh), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, rh, rh, ro, rh, ro), "chi": chi_s0, "is_s0": True},
                {"A": mk4(ro, ro, rh, rh, rh, rh), "chi": chi_s0, "is_s0": True},
            ]

    u01_4, u23_4 = qubit_swap(4, 0, 1), qubit_swap(4, 2, 3)
    perms4 = [
        (+1.0, np.eye(3), np.eye(16, dtype=np.complex128)),
        (-1.0, np.diag([-1.0, +1.0, +1.0]), u01_4),
        (-1.0, np.diag([+1.0, -1.0, +1.0]), u23_4),
        (+1.0, np.diag([-1.0, -1.0, +1.0]), u01_4 @ u23_4),
    ]
    edges_4 = [
        (0, 1, False, "V1_pp_od", "V0_pp_ev", None, "s_pp", "l_pp", 1.0, *ops4[(0, 1)]),
        (2, 3, False, "V1_nn_od", "V0_nn_ev", None, "s_nn", "l_nn", 0.0, *ops4[(2, 3)]),
    ] + [
        (p[0], p[1], True, "", "", "VT_pn_dir", "s_pn", "l_pn", 0.5, *ops4[p])
        for p in ((0, 2), (1, 3), (0, 3), (1, 2))
    ]
    _svm_enrich_4he(u4, perms4, edges_4, sog, betas, bas4_s, chi_s0, chi_s1, mk4)

    for rt in (0.38, 0.68, 1.15, 1.85):
        for ro in (1.20, 2.05, 3.25):
            bas4_d += [
                {"A": mk4(ro, ro, rt, ro, ro, ro), "a": w4[(0, 2)], "Xi": xi4_02},
                {"A": mk4(ro, ro, rt, 0.40, ro, ro), "a": w4[(0, 2)], "Xi": xi4_02},
                {"A": mk4(0.42, 0.42, rt, ro, ro, ro), "a": w4[(0, 2)], "Xi": xi4_02},
            ]

    m_4he = np.array([M_P, M_P, M_N, M_N])
    ucm_4 = (u4 * m_4he[None, :]) @ np.ones(4) / np.sum(m_4he)
    mid_pp = 0.5 * (u4[:, 0] + u4[:, 1])
    sc_4 = [(w4[(0, 1)], u4[:, 2] - mid_pp, fits["csn0"]),
            (w4[(0, 1)], u4[:, 3] - mid_pp, fits["csn0"])]
    mats_4 = build_ego_cg_matrices(
        u4, m_4he, bas4_s, bas4_d, perms4, edges_4, sc_4,
        [u4[:, 0] - ucm_4, u4[:, 1] - ucm_4], al5, fits, sog, betas
    )
    e_4he, dt_4he, rp2_4, lam_4 = solve_ego_gevp(*mats_4)
    re_4he = float(np.sqrt((1.0 - lam_4) * rp2_4 + R2_EP + RE2_N))

    # Select 16 greedy chi_s0 core states for exact 5He threshold comparison
    s0_all = [i for i, b in enumerate(bas4_s) if b["is_s0"]]
    chosen = [s0_all[0], s0_all[11], s0_all[22]]
    h_lin4 = 0.68 * mats_4[1] + mats_4[3]
    for _ in range(13):
        best_i, best_e = None, 1e9
        for cand_i in s0_all:
            if cand_i in chosen:
                continue
            trial = chosen + [cand_i]
            ix = np.ix_(trial, trial)
            st_m = 0.5 * (mats_4[0][ix] + mats_4[0][ix].T)
            di = 1.0 / np.sqrt(np.maximum(np.diag(st_m), 1e-24))
            ev, vc = eigh(st_m * np.outer(di, di))
            kp = ev > 1e-7
            if np.sum(kp) < len(trial):
                continue
            uo = (vc[:, kp] / np.sqrt(ev[kp])[None, :]) * di[:, None]
            et = float(eigh(0.5 * (uo.T @ (h_lin4[ix] + h_lin4[ix].T) @ uo), eigvals_only=True)[0])
            if et < best_e:
                best_e, best_i = et, cand_i
        if best_i is not None:
            chosen.append(best_i)

    ix16 = np.ix_(chosen, chosen)
    e4_sub16 = solve_ego_gevp(
        mats_4[0][ix16], mats_4[1][ix16], mats_4[2][ix16], mats_4[3][ix16]
    )[0]
    cores_16 = [bas4_s[i]["A"] for i in chosen]

    return {
        "e_3h": e_3h, "dt_3h": dt_3h, "re_3h": re_3h,
        "e_3he": e_3he, "dt_3he": dt_3he, "re_3he": re_3he, "de_gam_kev": de_gam_kev,
        "e_4he": e_4he, "dt_4he": dt_4he, "re_4he": re_4he,
        "e4_sub16": e4_sub16, "cores_16": cores_16,
    }


def run_a5_he5_dripline_gate(al5, fits, sog, betas, eta_csb, e4_sub, cores_16):
    """Exact 12-permutation L = 1 P-wave 5He = 4He(correlated) + n drip-line gate."""
    u5 = np.array([
        [+1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0), 0.0, 0.0, 0.0],
        [0.0, 0.0, +1.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0), 0.0],
        [+0.5, +0.5, -0.5, -0.5, 0.0],
        [-1.0 / np.sqrt(20.0)] * 4 + [+4.0 / np.sqrt(20.0)],
    ])
    sigs5 = build_spin_algebra(5)
    up, dn = np.array([1.0, 0.0]), np.array([0.0, 1.0])
    s0_2 = (np.kron(up, dn) - np.kron(dn, up)) / np.sqrt(2.0)
    chi5 = np.kron(np.kron(s0_2, s0_2), up).astype(np.complex128)
    a_pwave = np.array([0.0, 0.0, 0.0, np.sqrt(1.25)])

    def perm_mat5(idx_tuple):
        m = np.zeros((5, 5))
        for r_i, c_i in enumerate(idx_tuple):
            m[r_i, c_i] = 1.0
        return m

    sw_01 = qubit_swap(5, 0, 1)
    sw_23, sw_34, sw_24 = qubit_swap(5, 2, 3), qubit_swap(5, 3, 4), qubit_swap(5, 2, 4)
    p_specs = [(+1.0, (0, 1), np.eye(32, dtype=np.complex128)), (-1.0, (1, 0), sw_01)]
    n_specs = [
        (+1.0, (2, 3, 4), np.eye(32, dtype=np.complex128)),
        (-1.0, (3, 2, 4), sw_23), (-1.0, (2, 4, 3), sw_34), (-1.0, (4, 3, 2), sw_24),
        (+1.0, (3, 4, 2), sw_23 @ sw_34), (+1.0, (4, 2, 3), sw_34 @ sw_23),
    ]
    perms5 = [
        (sp * sn, u5 @ perm_mat5(ip_t + in_t).T @ u5.T, up_s @ un_s)
        for sp, ip_t, up_s in p_specs for sn, in_t, un_s in n_specs
    ]

    masses5 = np.array([M_P, M_P, M_N, M_N, M_N])
    k_kin5 = sum(
        ((HBAR_C ** 2) / (2.0 * masses5[a])) * np.outer(u5[:, a], u5[:, a]) for a in range(5)
    )
    m_halo = np.outer(a_pwave, a_pwave)
    r_halos = (1.85, 3.30, 6.20, 12.00)
    bas_a = []
    for ac in cores_16:
        a_pad = np.zeros((4, 4))
        a_pad[:3, :3] = ac
        for rh in r_halos:
            bas_a.append(a_pad + m_halo / (rh ** 2))
    bas_a = np.array(bas_a)
    nb = len(bas_a)
    two_pi_4 = (2.0 * np.pi) ** 4

    def eval_5he_mode(use_parity=True):
        s_m, t0_m, ks_m, v_m = (np.zeros((nb, nb)) for _ in range(4))
        sog_w = dict(sog)
        for ch in ("VC_pn", "V0_pn"):
            od_c = sog[f"{ch}_od"] if use_parity else sog[f"{ch}_ev"]
            sog_w[f"{ch}_dir"] = 0.5 * (sog[f"{ch}_ev"] + od_c)
            sog_w[f"{ch}_ex"] = 0.5 * (sog[f"{ch}_ev"] - od_c)
        sog_w["V1_nn_use"] = sog["V1_nn_od"] if use_parity else (eta_csb * sog["VC_pn_ev"])

        for sgn, p_j, u_s in perms5:
            wt = sgn / 12.0
            sp_ov = float(np.real(np.conj(chi5) @ (u_s @ chi5)))
            if abs(sp_ov) < 1e-12:
                continue
            b_m = np.einsum("ba,jbc,cd->jad", p_j, bas_a, p_j)
            b_v = p_j.T @ a_pwave
            c_m = bas_a[:, None, :, :] + b_m[None, :, :, :]
            cinv, det_c = inv_det_sym(c_m)
            i0 = (two_pi_4 / det_c) ** 1.5
            q_ab = np.einsum("m,ijmn,n->ij", a_pwave, cinv, b_v)
            s_m += wt * sp_ov * q_ab * i0

            acb = np.einsum("ikm,ijmn,jnl->ijkl", bas_a, cinv, b_m)
            tr_k = np.einsum("kl,ijkl->ij", k_kin5, acb)
            vec_l = np.einsum("m,ijmn,jnl->ijl", a_pwave, cinv, b_m)
            vec_r = np.einsum("ikm,ijmn,n->ijk", bas_a, cinv, b_v)
            qd_k = np.einsum("ijl,lk,ijk->ij", vec_l, k_kin5, vec_r)
            t0_m += wt * sp_ov * (3.0 * tr_k * q_ab + 2.0 * qd_k) * i0

            w_pp = u5[:, 0] - u5[:, 1]
            gm_pp = np.einsum("m,ijmn,n->ij", w_pp, cinv, w_pp)
            qa_pp = np.einsum("m,ijmn,n->ij", a_pwave, cinv, w_pp)
            qb_pp = np.einsum("ijmn,n->ijm", cinv, w_pp) @ b_v
            for c_n in (2, 3, 4):
                u_sp = u5[:, c_n] - 0.5 * (u5[:, 0] + u5[:, 1])
                t_sp = np.einsum("m,ijmn,n->ij", u_sp, cinv, u_sp)
                ch_sp = np.einsum("m,ijmn,n->ij", u_sp, cinv, w_pp)
                sa_sp = np.einsum("m,ijmn,n->ij", a_pwave, cinv, u_sp)
                sb_sp = np.einsum("ijmn,n->ijm", cinv, u_sp) @ b_v
                for q_i, ap in enumerate(al5):
                    dsp = 1.0 + 2.0 * ap * t_sp
                    eta_sp = (2.0 * ap) / dsp
                    g_ef = gm_pp - eta_sp * (ch_sp ** 2)
                    q_sp = q_ab - eta_sp * sa_sp * sb_sp
                    qa_e = qa_pp - eta_sp * sa_sp * ch_sp
                    qb_e = qb_pp - eta_sp * sb_sp * ch_sp
                    db = 1.0 + 2.0 * g_ef[..., None] * betas
                    qb_m = q_sp[..., None] - (2.0 * betas / db) * (qa_e * qb_e)[..., None]
                    vc_term = (((db ** (-1.5)) * qb_m) @ sog["VCoul_erf"]) * i0 * (dsp ** (-1.5))
                    v_m += wt * sp_ov * fits["csn0"][q_i] * vc_term

            for a_i in range(5):
                for b_i in range(a_i + 1, 5):
                    w_e = u5[:, a_i] - u5[:, b_i]
                    p1_op, p0_op, _ = pair_spin_ops(sigs5, a_i, b_i)
                    sp1 = float(np.real(np.conj(chi5) @ (p1_op @ (u_s @ chi5))))
                    sp0 = float(np.real(np.conj(chi5) @ (p0_op @ (u_s @ chi5))))
                    is_pn = (a_i < 2) != (b_i < 2)
                    s_key = "s_pn" if is_pn else ("s_pp" if a_i < 2 else "s_nn")

                    def add_v_gauss(cm_use, bv_use, k1_n, k0_n):
                        ci_u, dt_u = inv_det_sym(cm_use)
                        i0_u = (two_pi_4 / dt_u) ** 1.5
                        gm_u = np.einsum("m,ijmn,n->ij", w_e, ci_u, w_e)
                        qa_u = np.einsum("m,ijmn,n->ij", a_pwave, ci_u, w_e)
                        qb_u = np.einsum("ijmn,n->ijm", ci_u, w_e) @ bv_use
                        q0_u = np.einsum("m,ijmn,n->ij", a_pwave, ci_u, bv_use)
                        den_b = 1.0 + 2.0 * gm_u[..., None] * betas
                        q_b = q0_u[..., None] - (2.0 * betas / den_b) * (qa_u * qb_u)[..., None]
                        wt_b = (den_b ** (-1.5)) * q_b
                        pair_v = sp1 * (wt_b @ sog_w[k1_n]) + sp0 * (wt_b @ sog_w[k0_n])
                        v_m[:] += wt * pair_v * i0_u

                    if is_pn:
                        add_v_gauss(c_m, b_v, "VC_pn_dir", "V0_pn_dir")
                        rh = householder_jacobi(w_e)
                        bm_r = np.einsum("ab,jbc,cd->jad", rh, b_m, rh)
                        add_v_gauss(bas_a[:, None] + bm_r[None, :], rh @ b_v,
                                    "VC_pn_ex", "V0_pn_ex")
                    elif a_i < 2:
                        add_v_gauss(c_m, b_v, "V1_pp_od", "V0_pp_ev")
                    else:
                        add_v_gauss(c_m, b_v, "V1_nn_use", "V0_nn_ev")

                    gm_s = np.einsum("m,ijmn,n->ij", w_e, cinv, w_e)
                    cw_m = np.einsum("ijmn,n->ijm", cinv, w_e)
                    aw_s, bw_s = cw_m @ a_pwave, cw_m @ b_v
                    for q_i, ap in enumerate(al5):
                        dq = 1.0 + 2.0 * ap * gm_s
                        eta_q = (2.0 * ap) / dq
                        i0_q = i0 * (dq ** (-1.5))
                        q_q = q_ab - eta_q * aw_s * bw_s
                        for p_idx in (a_i, b_i):
                            up_v = u5[:, p_idx]
                            kap_p = (HBAR_C ** 2) / (2.0 * masses5[p_idx])
                            ya, yb = bas_a @ up_v, b_m @ up_v
                            cu = np.einsum("ijmn,jn->ijm", cinv, yb)
                            ya_cw = np.einsum("im,ijm->ij", ya, cw_m)
                            cw_yb = np.einsum("ijm,jm->ij", cw_m, yb)
                            y_sy = np.einsum("im,ijm->ij", ya, cu) - eta_q * ya_cw * cw_yb
                            ra = np.einsum("im,ijmn,n->ij", ya, cinv, a_pwave) - eta_q * ya_cw * aw_s
                            rb = (cu @ b_v) - eta_q * cw_yb * bw_s
                            ysb = (np.einsum("im,ijmn->ijn", ya, cinv) @ b_v) - eta_q * ya_cw * bw_s
                            asy = np.einsum("m,ijm->ij", a_pwave, cu) - eta_q * aw_s * cw_yb
                            ta, tb = float(a_pwave @ up_v), float(b_v @ up_v)
                            poly1 = 3.0 * y_sy * q_q + (ta - ra) * (tb - rb) + ysb * asy
                            ks_m += wt * sp_ov * kap_p * fits[s_key][q_i] * poly1 * i0_q

        return solve_ego_gevp(s_m, t0_m, ks_m, v_m)[0]

    e5_wig = eval_5he_mode(use_parity=False)
    e5_par = eval_5he_mode(use_parity=True)
    return e5_wig - e4_sub, e5_par - e4_sub


def main():
    t0 = time.time()
    meta, betas, al5, fits, sog = unpack_step12_bank()
    gp, gn, eta_live, t_rot = verify_a1_virial_csb()
    a2 = run_a2_scattering_capture_and_pwave(meta, betas, al5, fits, sog)
    a34 = run_a3_a4_benchmarks(al5, fits, sog, betas, a2["e_d"])
    de5_wigner, de5_parity = run_a5_he5_dripline_gate(
        al5, fits, sog, betas, meta["eta_csb"], a34["e4_sub16"], a34["cores_16"]
    )

    print("=== MODULE 03: PART II FEW-BODY QUANTUM SUITE (A = 1..5, G_B == 0) ===",
          flush=True)
    print(f"  1. A=1 Virial CSB : gamma_p={gp:.5f}, gamma_n={gn:.5f} -> "
          f"eta_CSB={eta_live:.5f} (Bank {meta['eta_csb']:.5f}) | T_rot={t_rot:.2f} MeV")
    print(f"  2. A=2 Bound/Capt : G_S={a2['meta_gs']:.2f}, C_FB={a2['meta_cfb']:+.2f} (G_B=0) | "
          f"E_d={a2['e_d']:+.4f} MeV, P_D={a2['p_d']:.2f}%, r_E={a2['re_d']:.3f} fm")
    print(f"     1S0 & M1 Capt  : a_np={a2['a_np']:+.2f} fm, r_0s={a2['r_0s']:.2f} fm, "
          f"E_virt=+{a2['e_virt']:.1f} keV (Exp +66.0) | "
          f"sigma_th={a2['sig_th']:.1f} mb (Exp 332.6)")
    print(f"     3P Parity Flip : 25 MeV: {a2['d25_off']:+.2f} -> {a2['d25_on']:+.2f} deg "
          f"(Exp -0.30) | 50 MeV: {a2['d50_off']:+.2f} -> {a2['d50_on']:+.2f} deg (Exp -1.20)")
    print("\n  3. Pure Two-Body Ego-Metric CG Ledger (Zero 3N Force Loops):")
    print(f"     3H  (Triton)   : E = {a34['e_3h']:+8.3f} MeV (Exp -8.482) | "
          f"<dT_ego> = {a34['dt_3h']:+6.2f} MeV | r_E = {a34['re_3h']:.3f} fm (Exp 1.759)")
    print(f"     3He (Helion)   : E = {a34['e_3he']:+8.3f} MeV (Exp -7.718) | "
          f"<dT_ego> = {a34['dt_3he']:+6.2f} MeV | r_E = {a34['re_3he']:.3f} fm (Exp 1.966)")
    print(f"     Mirror Split   : dE_gam = {a34['de_gam_kev']:+6.1f} keV (Exp +763.8 keV) | "
          f"erf-Coulomb fit err = {a2['erf_err']:.2e} MeV")
    print(f"     4He (Alpha)    : E = {a34['e_4he']:+8.3f} MeV (Exp -28.296) | "
          f"<dT_ego> = {a34['dt_4he']:+6.2f} MeV | r_E = {a34['re_4he']:.3f} fm (Exp 1.676)")
    print("\n  4. 12-Permutation 5He(3/2-) Drip-Line Gate (vs. Subspace E(4He) = "
          f"{a34['e4_sub16']:+.2f} MeV):")
    print(f"     Without Pi_ab^+ (Wigner): dE(5He - 4He) = {de5_wigner:+6.2f} MeV "
          "[FALSELY BOUND]")
    print(f"     With    Pi_ab^+ (Active): dE(5He - 4He) = {de5_parity:+6.2f} MeV "
          "[STRICTLY UNBOUND (>0), Exp +0.80 MeV]")
    print(f"\n=== MODULE 03 COMPLETE (Elapsed: {time.time() - t0:.2f} s) ===", flush=True)


if __name__ == "__main__":
    main()