# Check the MuJoCo model of the nominal arm (no friction, no rotor inertia, no payload) against the
# library's formulas: inertia matrix, bias force C(theta, theta_dot) theta_dot + N(theta), tool
# point, and the Christoffel table against central differences of M. Random configurations and
# rates, fixed seed. Prints the largest absolute and relative deviations.
import sys

import mujoco
import numpy as np

import arm

n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
rng = np.random.default_rng(20261105)
th = rng.uniform(-np.pi, np.pi, (n, 3))
thd = rng.uniform(-3, 3, (n, 3))

m = mujoco.MjModel.from_xml_string(arm.mjcf(arm.load_scene(), contact=False))
d = mujoco.MjData(m)
site = m.site("tool").id


def mj(q, v):
    d.qpos[:], d.qvel[:] = q, v
    mujoco.mj_forward(m, d)
    M = np.zeros((3, 3))
    mujoco.mj_fullM(m, d, M)
    return M, d.qfrc_bias.copy(), d.site_xpos[site].copy()


# MuJoCo is called once per sample (its API has no batch form for these quantities); the library
# side is evaluated on the whole batch at once
res = [mj(q, v) for q, v in zip(th, thd)]
Mmj = np.array([r[0] for r in res])
bmj = np.array([r[1] for r in res])
pmj = np.array([r[2] for r in res])

Mlib, blib, plib = arm.mass(th), arm.bias(th, thd), arm.tool(th)
print("samples", n)
print("max |M_mujoco - M_library|", np.abs(Mmj - Mlib).max(), "relative to max |M|", np.abs(Mmj - Mlib).max() / np.abs(Mlib).max())
print("max |bias_mujoco - bias_library|", np.abs(bmj - blib).max(), "relative to max |bias|", np.abs(bmj - blib).max() / np.abs(blib).max())
print("max |tool_mujoco - tool_library| (m)", np.abs(pmj - plib).max())

# gravity alone (zero rates) and the Christoffel table against central differences of M
b0 = np.array([mj(q, 0 * q)[1] for q in th])
print("max |gravity_mujoco - N_library|", np.abs(b0 - arm.gravity(th)).max())
h = 1e-6
E = np.eye(3)
dM = np.stack([(arm.mass(th + h * E[k]) - arm.mass(th - h * E[k])) / (2 * h) for k in range(3)], 1)
# symbol dM i j k = (dM_k[i, j] + dM_j[i, k] - dM_i[k, j]) / 2 with dM indexed (sample, k, i, j)
G = (np.einsum("nkij->nijk", dM) + np.einsum("njik->nijk", dM) - np.einsum("nikj->nijk", dM)) / 2
print("max |Gamma_table - Gamma_from_dM|", np.abs(G - arm.christoffel(th)).max())
M = arm.mass(th)
print("min eigenvalue of M over the samples", np.linalg.eigvalsh(M).min())
