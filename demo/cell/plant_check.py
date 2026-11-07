# Checks of the plant's elastic joints, actuator lag, encoder noise and timing jitter, each on one run
# of the ablation's cycle at (omega, delta) = (80, 0.03), against quantities recomputed independently
# from the trace: the link and rotor equations of the elastic plant, the lag's output against a
# first-order filter of the commanded torque, the applied torque against the jitter drawn, and the
# counts sent to the program against the true angles and the noise drawn.
# Usage: uv run python plant_check.py
import numpy as np
from scipy.signal import lfilter

import arm
import jobs
import sim

scene = jobs.scene
w, delta = 80.0, 0.03
base = dict(sim.nominal, omega=w, delta=delta, **sim.tolerances(w, delta))


def go(cfg):
    sup = sim.supervisor()
    o = sim.run(scene, cfg, jobs.ablation_plan, sup)
    sup.close()
    if "unstable_t" in o:
        print("unstable: the integration diverged at t", o["unstable_t"])
    print("run: sim s", round(o["trace"]["t"][-1], 2), "outcomes", [(mv["outcome"], mv["k_end"] - mv["k0"] if mv["k_end"] else None) for mv in o["moves"]])
    return o, sim.analyse(scene, cfg, o), sup.transcript


def boundary_counts(transcript):
    rows = [ln.split() for ln, _ in transcript if ln.startswith("boundary ")]
    return np.array([int(r[1]) for r in rows]), np.array([[int(x) for x in r[2:5]] for r in rows])


# ------------------------------------------------------------------
# elastic joints on the nominal links (no payload, friction or model error) with the encoders, filter
# and delay of the realistic plant: the springs must pass K (qm - q) + D (vm - v), the links obey
# M(q) q'' + C q' + N = spring torque, the rotors J qm'' = applied torque - spring torque, and the
# disturbance d of the analysis must contain the torque the springs did not pass on
cfg = dict(base, armature=[0.1] * 3, counts=2**18, cutoff=100.0, delay=True, **jobs.elastic(1e5))
o, recs, tr_ = go(cfg)
tr = o["trace"]
M = arm.mass(tr["q"])
link = np.einsum("nij,nj->ni", M, tr["qacc"]) + arm.bias(tr["q"], tr["v"]) - tr["spring"]
rotor = (0.1 + 1e-9) * tr["qacc_m"] - (tr["tau"] - tr["spring"])
K, D = cfg["stiffness"][0], cfg["joint_damping"][0]
spring = K * (tr["qm"] - tr["q"]) + D * (tr["vm"] - tr["v"])
print("elastic K", K, "D", round(D, 4), "samples", len(tr["t"]))
print("link equation max |M q'' + C q' + N - spring| N m", np.abs(link).max())
print("rotor equation max |J qm'' - (tau - spring)| N m", np.abs(rotor).max())
print("spring torque max |spring - (K (qm - q) + D (vm - v))| N m", np.abs(tr["spring"] - spring).max(), "of max |spring|", np.abs(tr["spring"]).max())
print("initial link acceleration max |q''| over the first ms rad/s^2", np.abs(tr["qacc"][:4]).max())
gap = tr["spring"] - tr["tau"]
minv_gap = np.linalg.solve(M, gap[..., None])[..., 0]
print("torque the springs did not pass on: max |spring - tau| N m", np.abs(gap).max(), "max |M^-1 (spring - tau)| / (w^2 delta)",
      np.abs(minv_gap).max() / (w**2 * delta))
print("deflection max |qm - q| rad", np.abs(tr["qm"] - tr["q"]).max())
print("analysis: max minvd_over_w2delta", max(r["minvd_over_w2delta"] for r in recs), "max d_plant", max(r["d_plant"] for r in recs))
dpl = np.einsum("nij,nj->ni", M, tr["qacc"]) + arm.bias(tr["q"], tr["v"]) - tr["tau"]
print("plant disturbance minus the springs' gap max |d_plant - (spring - tau)| N m", np.abs(dpl - gap).max())

# the same with the encoders on the motors: the counts sent are those of the rotor angles
cfg = dict(cfg, **jobs.elastic(1e6, sense="motor"))
o, recs, tr_ = go(cfg)
tr = o["trace"]
k, c = boundary_counts(tr_)
n = k * round(cfg["h"] / cfg["ctrl"]) * round(cfg["ctrl"] / cfg["dt"])
k, c, n = k[n < len(tr["t"])], c[n < len(tr["t"])], n[n < len(tr["t"])]
step = 2 * np.pi / 2**18
print("motor sensing: counts - round(qm / step) at the boundaries, max abs", np.abs(c - np.round(tr["qm"][n] / step)).max(),
      "max |q_s - q| rad", max(r["meas_q_max"] for r in recs), "max |qm - q| rad at the boundaries", np.abs(tr["qm"][n] - tr["q"][n]).max())

# ------------------------------------------------------------------
# actuator lag on the reference plant without saturation: the applied torque against the
# first-order filter, run independently on the delayed commands held over each period
ref = dict(base, **jobs.middle, counts=2**18, cutoff=100.0, delay=True)
lag = 0.002
o, recs, _ = go(dict(ref, lag=lag))
tr = o["trace"]
u = np.vstack([tr["ctl_tau"][:1], tr["ctl_tau"][:-1]])
u = np.clip(np.repeat(u, 4, axis=0), -150.0, 150.0)
a = np.exp(-ref["dt"] / lag)
y = lfilter([1 - a], [1, -a], u - u[0], axis=0) + u[0]
print("lag", lag, "max |applied - filtered command| N m", np.abs(tr["tau"] - y).max(), "max |applied - command| N m", np.abs(tr["tau"] - u).max())

# ------------------------------------------------------------------
# timing jitter: in each period the new torque from substep jit on, the last applied one before
nj = 4
o, recs, _ = go(dict(ref, jitter=nj))
tr = o["trace"]
jit = tr["jitter"]
cmd = np.vstack([tr["ctl_tau"][:1], tr["ctl_tau"][:-1]])
P = len(jit)
ok = jit < 4
last = np.maximum.accumulate(np.where(ok, np.arange(P), -1))
prev = np.concatenate([[-1], last[:-1]])
held = np.where(prev[:, None] >= 0, cmd[np.maximum(prev, 0)], cmd)
j = np.arange(4)
exp = np.where((j[None, :] >= jit[:, None])[..., None], cmd[:, None, :], held[:, None, :]).reshape(-1, 3)
print("jitter", nj, "periods", P, "draws per value 0..4", np.bincount(jit, minlength=nj + 1).tolist(),
      "max |applied - expected| N m", np.abs(tr["tau"] - np.clip(exp, -150, 150)).max())

# ------------------------------------------------------------------
# encoder noise: the counts sent to the program minus the counts of the true angle are the noise drawn
nn = 4
o, recs, tr_ = go(dict(ref, enc_noise=nn))
tr = o["trace"]
k, c = boundary_counts(tr_)
step = 2 * np.pi / 2**18
n = k * round(ref["h"] / ref["ctrl"]) * round(ref["ctrl"] / ref["dt"])
k, c, n = k[n < len(tr["t"])], c[n < len(tr["t"])], n[n < len(tr["t"])]
nz = tr["noise"][k * round(ref["h"] / ref["ctrl"])]
print("noise", nn, "draws per value -4..4", np.bincount(tr["noise"].ravel() + nn, minlength=2 * nn + 1).tolist(),
      "boundaries", len(k), "max |counts - round(q / step) - noise|", np.abs(c - np.round(tr["q"][n] / step) - nz).max(),
      "max |q_s - q| rad", max(r["meas_q_max"] for r in recs), "bound (n + 1/2) step", (nn + 0.5) * step)
