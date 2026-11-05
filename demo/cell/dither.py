# Torque dither at standstill. (1) From the kept campaign traces of each (gain, tube radius) pair:
# during the rest move (the first 2 s, reference constant at home) the standard deviation and the
# peak-to-peak of the commanded torque per joint, the rms of its change between control periods, and
# the true joint motion in encoder counts. (2) Isolation runs of the rest move alone on the middle
# plant at each gain, with one sensing or timing effect removed at a time, to find the cause.
# Usage: uv run python dither.py <outdir>   (writes <outdir>/dither.json)
import json
import sys
from pathlib import Path

import numpy as np

import arm
import jobs
import sim
from bounds import candidates

out = Path(sys.argv[1])
count = 2 * np.pi / 2**18


def stats(t, tau, q, t1=2.0):
    """Dither of the commanded torque and motion of the true joint angle on 0.2 s <= t < t1 (the
    first 0.2 s are left out as the start transient)."""
    tc = np.arange(len(tau)) * 0.001
    s = (tc >= 0.2) & (tc < t1)
    qs = q[(t >= 0.2) & (t < t1)]
    return dict(tau_std=tau[s].std(0).round(3).tolist(), tau_ptp=np.ptp(tau[s], 0).round(3).tolist(),
                tau_mean=tau[s].mean(0).round(3).tolist(), tau_step_rms=np.sqrt((np.diff(tau[s], axis=0)**2).mean(0)).round(3).tolist(),
                q_ptp_counts=(np.ptp(qs, 0) / count).round(2).tolist(), q_std_counts=(qs.std(0) / count).round(2).tolist())


S = {"campaign_rest_move": {}, "isolation": {}}
for w, d in candidates:
    rows = []
    for s in range(3):
        p = out / "traces" / f"c{w}-{d}-{s:04d}.npz"
        if p.exists():
            z = np.load(p)
            rows.append(stats(z["t"], z["ctl_tau"], z["q"]))
    if rows:
        S["campaign_rest_move"][f"{w}-{d}"] = {k: np.max([r[k] for r in rows], 0).round(3).tolist() if k != "tau_mean" else rows[0][k]
                                               for k in rows[0]}

# isolation: the rest move only (an empty plan; the run ends one second after it), middle plant
base = dict(sim.nominal, **jobs.fixed, **jobs.middle, tail=1.0)
variants = {
    "realistic": {},
    "exact position (no quantization)": dict(counts=0),
    "exact velocity (no differencing or filter)": dict(cutoff=0.0),
    "no delay": dict(delay=False),
    "exact position and velocity": dict(counts=0, cutoff=0.0),
}
for w in sorted({float(c[0]) for c in candidates}):
    for name, v in variants.items():
        cfg = dict(base, omega=w, delta=0.03, **v)
        sup = sim.supervisor()
        o = sim.run(jobs.scene, cfg, [], sup)
        sup.close()
        tr = o["trace"]
        S["isolation"][f"omega {int(w)}: {name}"] = stats(tr["t"], tr["ctl_tau"], tr["q"])
json.dump(S, open(out / "dither.json", "w"), indent=1)
print(json.dumps(S, indent=1))
