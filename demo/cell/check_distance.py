# Check MuJoCo's capsule-to-obstacle distances against an independent computation: the link
# segments from the library's shoulder, elbow and tool points, sampled densely, with exact
# point-to-box and point-to-half-space distances, minus the link radius. Random configurations in
# the scene's joint envelope widened by 15 degrees, fixed seed.
import mujoco
import numpy as np

import arm

scene = arm.load_scene()
rng = np.random.default_rng(7)
lo = np.radians(scene["joint_envelope"]["lo_deg"]) - np.radians(15)
hi = np.radians(scene["joint_envelope"]["hi_deg"]) + np.radians(15)
th = rng.uniform(lo, hi, (3000, 3))

m = mujoco.MjModel.from_xml_string(arm.mjcf(scene))
d = mujoco.MjData(m)
caps = [m.geom("cap1").id, m.geom("cap2").id]
oid = [m.geom(o["name"]).id for o in scene["obstacles"]]


def mj(q):
    d.qpos[:] = q
    mujoco.mj_kinematics(m, d)
    return [[mujoco.mj_geomDistance(m, d, c, o, 1.0, None) for o in oid] for c in caps]


# MuJoCo is queried once per configuration; the reference side is computed on the whole batch
D = np.array([mj(q) for q in th])

P = arm.points(th)
s = np.linspace(0, 1, 2001)[:, None]
segs = [P[:, None, 0] + s * (P[:, None, 1] - P[:, None, 0]), P[:, None, 1] + s * (P[:, None, 2] - P[:, None, 1])]
ref = []
for seg in segs:
    row = []
    for o in scene["obstacles"]:
        if o["kind"] == "box":
            blo, bhi = np.array(o["lo"]), np.array(o["hi"])
            out = np.linalg.norm(np.maximum(np.maximum(blo - seg, seg - bhi), 0), axis=-1)
            pen = np.minimum(seg - blo, bhi - seg).min(-1)
            dist = np.where(out > 0, out, -pen)
        else:
            n = np.array(o["n"], float)
            dist = (seg @ n - o["beta"]) / np.linalg.norm(n)
        row.append(dist.min(1) - arm.rho)
    ref.append(row)
ref = np.minimum(np.transpose(np.array(ref), (2, 0, 1)), 1.0)
err = np.abs(D - ref)
print("configurations", len(th), "max |mujoco - reference| (m)", err.max(), "at", np.unravel_index(err.argmax(), err.shape))
print("fraction of (configuration, link, obstacle) with distance < 1", (ref < 1).mean(), "with negative distance", (ref < 0).mean())
