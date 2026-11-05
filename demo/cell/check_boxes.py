# Smallest capsule-to-obstacle distance over each certified cell inflated by the scene's inflation,
# sampled on a grid of 41 values per joint, next to the certified clearance. A sampled minimum is an
# upper bound on the true minimum over the box; the certificate is the proof.
import numpy as np

import arm

scene = arm.load_scene()
infl = scene["cell_inflation_rad"]
obs = [o["name"] for o in scene["obstacles"]]
print("certified clearance (m)", scene["clearance"], "inflation (rad)", infl)
for c in scene["cells"]:
    lo = np.radians(np.array(c["lo_deg"], float)) - infl
    hi = np.radians(np.array(c["hi_deg"], float)) + infl
    g = np.stack(np.meshgrid(*[np.linspace(lo[i], hi[i], 41) for i in range(3)], indexing="ij"), -1).reshape(-1, 3)
    # chunks keep the sampled segments within memory
    d = np.concatenate([arm.capsule_distance(x, scene).min(1) for x in np.array_split(g, 20)])
    m = d.min(0)
    print(c["name"], " ".join(f"{o} {round(float(v), 4)}" for o, v in zip(obs, m)), "smallest", round(float(m.min()), 4), obs[int(m.argmin())])
