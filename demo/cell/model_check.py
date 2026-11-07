# Check the controller's nominal model (model.py) against MuJoCo on the rigid plant with the rotor
# inertia J as every joint's armature and a point mass m_hat at the tool point: M_hat(theta) against
# mj_fullM and C_hat theta' + N_hat against qfrc_bias, with J, m_hat, the configuration and the
# rates drawn at random per sample (fixed seed); the payload term Jt^T Jt against MuJoCo's Jacobian
# of the tool site. The payload body first has the smallest inertia the harness uses (1e-12 kg m^2,
# a point mass up to round-off), then the inertia of the 35 mm sphere the plant's part has, which the
# point-mass model leaves out. Prints the largest absolute and relative differences.
# Usage: uv run python model_check.py [samples]
import sys

import mujoco
import numpy as np

import arm
import model

n = int(sys.argv[1]) if len(sys.argv) > 1 else 500
rng = np.random.default_rng(20261107)
th = rng.uniform(-np.pi, np.pi, (n, 3))
thd = rng.uniform(-6, 6, (n, 3))
J = rng.uniform(0, 2, n)
mh = rng.uniform(0, 5, n)

m = mujoco.MjModel.from_xml_string(arm.mjcf(arm.load_scene(), contact=False))
d = mujoco.MjData(m)
pay, site = m.body("payload").id, m.site("tool").id


def mj(q, v, rotor, mass, inertia):
    m.dof_armature[:] = rotor
    m.body_mass[pay] = mass
    m.body_inertia[pay] = inertia
    d.qpos[:], d.qvel[:] = q, v
    mujoco.mj_forward(m, d)
    M = np.zeros((3, 3))
    mujoco.mj_fullM(m, d, M)
    jp = np.zeros((3, 3))
    mujoco.mj_jacSite(m, d, jp, None, site)
    return M, d.qfrc_bias.copy(), jp


def compare(label, radius):
    # MuJoCo is called once per sample (its API has no batch form); the model on the whole batch
    res = [mj(q, v, a, b, 0.4 * b * radius**2 + 1e-12) for q, v, a, b in zip(th, thd, J, mh)]
    Mmj = np.array([r[0] for r in res])
    bmj = np.array([r[1] for r in res])
    Mh, bh = model.mass(th, J[:, None], mh), model.bias(th, thd, mh)
    print(label, "max |M_mujoco - M_hat|", np.abs(Mmj - Mh).max(), "relative to max |M_hat|", np.abs(Mmj - Mh).max() / np.abs(Mh).max())
    print(label, "max |bias_mujoco - (C_hat v + N_hat)|", np.abs(bmj - bh).max(), "relative to max |bias|", np.abs(bmj - bh).max() / np.abs(bh).max())
    return np.array([r[2] for r in res])


print("samples", n, "J in [0, 2] kg m^2, m_hat in [0, 5] kg, rates in [-6, 6] rad/s")
jp = compare("point mass:", 0.0)
print("max |Jt^T Jt (MuJoCo site Jacobian) - tool_inertia|", np.abs(np.einsum("nki,nkj->nij", jp, jp) - model.tool_inertia(th)).max())
compare("35 mm sphere:", 0.035)
