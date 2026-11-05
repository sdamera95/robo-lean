# The three-link elbow arm of the pick-and-place cell: parameters, the nominal rigid-body model
# (the inertia matrix, Christoffel symbols and gravity term of MLS Example 4.3, pp. 172-175, as
# formalized in the library), the tool map, and the MuJoCo model of the plant.
#
# Conventions (the library's): joint vector (base yaw, shoulder, elbow) in radians; at theta = 0
# the arm lies along +y at height l0; joints 1 and 2 turn about -x, so a negative shoulder angle
# raises the arm; gravity along -z; the table is the plane z = 0. Every function of the nominal
# model takes arrays with the joint index last and broadcasts over leading axes.
import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np

here = Path(__file__).resolve().parent

# arm parameters in SI units, exact as stated in the cell specification
P = dict(
    l0=F(2, 5), l1=F(17, 40), l2=F(49, 125),
    m1=F(37, 10), m2=F(8393, 1000), m3=F(49, 10),
    r0=F(1, 5), r1=F(17, 80), r2=F(3, 10),
    I1=(F(103, 10000), F(103, 10000), F(67, 10000)),
    I2=(F(67, 500), F(3, 200), F(67, 500)),
    I3=(F(39, 500), F(9, 1000), F(39, 500)),
    g=F(981, 100), rho=F(3, 50),
)
l0, l1, l2 = float(P["l0"]), float(P["l1"]), float(P["l2"])
m1, m2, m3 = float(P["m1"]), float(P["m2"]), float(P["m3"])
r0, r1, r2 = float(P["r0"]), float(P["r1"]), float(P["r2"])
I1, I2, I3 = (np.array([float(x) for x in P[k]]) for k in ("I1", "I2", "I3"))
g, rho = float(P["g"]), float(P["rho"])


def trig(th):
    c1, s1 = np.cos(th[..., 1]), np.sin(th[..., 1])
    c2, s2 = np.cos(th[..., 2]), np.sin(th[..., 2])
    c12, s12 = np.cos(th[..., 1] + th[..., 2]), np.sin(th[..., 1] + th[..., 2])
    return c1, s1, c2, s2, c12, s12


def mass(th):
    """Inertia matrix M(theta) of MLS p. 173 (the library's threeLinkArm_massMatrix)."""
    c1, s1, c2, s2, c12, s12 = trig(th)
    M = np.zeros(th.shape[:-1] + (3, 3))
    M[..., 0, 0] = (I2[1] * s1**2 + I3[1] * s12**2 + I1[2] + I2[2] * c1**2 + I3[2] * c12**2
                    + m2 * r1**2 * c1**2 + m3 * (l1 * c1 + r2 * c12)**2)
    M[..., 1, 1] = I2[0] + I3[0] + m3 * l1**2 + m2 * r1**2 + m3 * r2**2 + 2 * m3 * l1 * r2 * c2
    M[..., 1, 2] = M[..., 2, 1] = I3[0] + m3 * r2**2 + m3 * l1 * r2 * c2
    M[..., 2, 2] = I3[0] + m3 * r2**2
    return M


def christoffel(th):
    """Christoffel symbols Gamma[i, j, k] of MLS p. 174 (the library's threeLinkArmChristoffel)."""
    c1, s1, c2, s2, c12, s12 = trig(th)
    a = l1 * c1 + r2 * c12
    G112 = (I2[1] - I2[2] - m2 * r1**2) * c1 * s1 + (I3[1] - I3[2]) * c12 * s12 - m3 * a * (l1 * s1 + r2 * s12)
    G113 = (I3[1] - I3[2]) * c12 * s12 - m3 * r2 * s12 * a
    G = np.zeros(th.shape[:-1] + (3, 3, 3))
    G[..., 0, 0, 1] = G[..., 0, 1, 0] = G112
    G[..., 0, 0, 2] = G[..., 0, 2, 0] = G113
    G[..., 1, 0, 0] = -G112
    G[..., 1, 1, 2] = G[..., 1, 2, 1] = G[..., 1, 2, 2] = -l1 * m3 * r2 * s2
    G[..., 2, 0, 0] = -G113
    G[..., 2, 1, 1] = l1 * m3 * r2 * s2
    return G


def coriolis(th, thd):
    """Coriolis matrix C(theta, theta_dot) with C_ij = sum_k Gamma_ijk theta_dot_k (MLS eq. (4.23))."""
    return np.einsum("...ijk,...k->...ij", christoffel(th), thd)


def gravity(th):
    """Gravity term N(theta) of MLS eq. (4.25) (the library's threeLinkArm_gravityTerm), up = +z."""
    c1, s1, c2, s2, c12, s12 = trig(th)
    N = np.zeros(th.shape)
    N[..., 1] = -(m2 * g * r1 + m3 * g * l1) * c1 - m3 * g * r2 * c12
    N[..., 2] = -m3 * g * r2 * c12
    return N


def bias(th, thd):
    """C(theta, theta_dot) theta_dot + N(theta)."""
    return np.einsum("...ij,...j->...i", coriolis(th, thd), thd) + gravity(th)


def points(th):
    """Shoulder, elbow and tool points (metres), stacked on the second-to-last axis."""
    c0, s0 = np.cos(th[..., 0]), np.sin(th[..., 0])
    c1, s1, c2, s2, c12, s12 = trig(th)
    sh = np.stack([0 * c0, 0 * c0, l0 + 0 * c0], -1)
    el = np.stack([-s0 * l1 * c1, c0 * l1 * c1, l0 - l1 * s1], -1)
    reach = l1 * c1 + l2 * c12
    tl = np.stack([-s0 * reach, c0 * reach, l0 - l1 * s1 - l2 * s12], -1)
    return np.stack([sh, el, tl], -2)


def tool(th):
    return points(th)[..., 2, :]


def computed_torque(w, r, rd, rdd, th, thd):
    """Computed torque M (r'' - Kv (theta' - r') - Kp (theta - r)) + C theta' + N with Kp = w^2 I,
    Kv = 2 w I (the library's computedTorqueAlong), on the nominal model."""
    a = rdd - 2 * w * (thd - rd) - w**2 * (th - r)
    return np.einsum("...ij,...j->...i", mass(th), a) + bias(th, thd)


# ------------------------------------------------------------------
# the move reference: the clamped quintic of the specification

def quintic(s):
    s = np.clip(s, 0, 1)
    return 10 * s**3 - 15 * s**4 + 6 * s**5, 30 * s**2 - 60 * s**3 + 30 * s**4, 60 * s - 180 * s**2 + 120 * s**3


def reference(a, b, t0, T, t):
    """r(t) = a + sigma((t - t0)/T)(b - a) with its first two time derivatives; t broadcasts."""
    t = np.asarray(t, float)[..., None]
    s, sd, sdd = quintic((t - t0) / T)
    inside = ((t > t0) & (t < t0 + T)).astype(float)
    return a + s * (b - a), inside * sd / T * (b - a), inside * sdd / T**2 * (b - a)


# ------------------------------------------------------------------
# the scene

def load_scene(path=here / "scene.json"):
    return json.load(open(path))


def frac(x):
    return F(str(x))


def waypoints(scene):
    """Waypoints by name: exact degrees (Fractions) and radians."""
    return {w["name"]: dict(exact=tuple(frac(x) for x in w["deg"]), role=w["role"],
                            rad=np.radians([float(frac(x)) for x in w["deg"]])) for w in scene["waypoints"]}


def cells(scene):
    return [(tuple(frac(x) for x in c["lo_deg"]), tuple(frac(x) for x in c["hi_deg"])) for c in scene["cells"]]


# ------------------------------------------------------------------
# the MuJoCo model of the plant

def mjcf(scene, armature=0.0, damping=0.0, frictionloss=0.0, dt=0.00025, limit=150.0, contact=True):
    """MJCF of the plant: the nominal arm (body frames at the joints, inertial frames at the mass
    centres with the base orientation at theta = 0, diagonal inertias as in MLS p. 172), capsules of
    radius rho around the two link segments, a payload body at the tool point (mass set at run
    time), torque motors with the limit, joint friction and rotor inertia, and the obstacles."""
    f = lambda v: " ".join(repr(float(x)) for x in v)
    ct = 'contype="1" conaffinity="0"' if contact else 'contype="0" conaffinity="0"'
    obs = []
    for o in scene["obstacles"]:
        if o["kind"] == "box":
            lo, hi = np.array(o["lo"], float), np.array(o["hi"], float)
            obs.append(f'<geom name="{o["name"]}" type="box" pos="{f((lo + hi) / 2)}" size="{f((hi - lo) / 2)}" '
                       f'contype="0" conaffinity="1" rgba="0.6 0.6 0.65 0.5"/>')
        else:
            # half-space {p : n . p <= beta}: a plane geom whose normal +n points out of the obstacle
            n = np.array(o["n"], float) / np.linalg.norm(o["n"])
            p = n * float(o["beta"]) / np.linalg.norm(o["n"])
            obs.append(f'<geom name="{o["name"]}" type="plane" pos="{f(p)}" zaxis="{f(n)}" size="2 2 0.01" '
                       f'contype="0" conaffinity="1" rgba="0.8 0.8 0.8 0.3"/>')
    joint = f'armature="{armature}" damping="{damping}" frictionloss="{frictionloss}"'
    return f"""
<mujoco model="cell">
  <compiler angle="radian" autolimits="true"/>
  <option timestep="{dt}" integrator="implicitfast" gravity="0 0 {-g}"/>
  <worldbody>
    <light pos="0 0 3"/>
    {chr(10).join(obs)}
    <body name="link1">
      <joint name="j0" type="hinge" axis="0 0 1" {joint}/>
      <inertial pos="0 0 {r0}" mass="{m1}" diaginertia="{f(I1)}"/>
      <geom name="column" type="cylinder" fromto="0 0 0 0 0 {l0}" size="0.05" contype="0" conaffinity="0" rgba="0.3 0.3 0.3 1"/>
      <body name="link2" pos="0 0 {l0}">
        <joint name="j1" type="hinge" axis="-1 0 0" {joint}/>
        <inertial pos="0 {r1} 0" mass="{m2}" diaginertia="{f(I2)}"/>
        <geom name="cap1" type="capsule" fromto="0 0 0 0 {l1} 0" size="{rho}" {ct} rgba="0.0 0.45 0.7 1"/>
        <body name="link3" pos="0 {l1} 0">
          <joint name="j2" type="hinge" axis="-1 0 0" {joint}/>
          <inertial pos="0 {r2} 0" mass="{m3}" diaginertia="{f(I3)}"/>
          <geom name="cap2" type="capsule" fromto="0 0 0 0 {l2} 0" size="{rho}" {ct} rgba="0.0 0.62 0.45 1"/>
          <site name="tool" pos="0 {l2} 0"/>
          <body name="payload" pos="0 {l2} 0">
            <inertial pos="0 0 0" mass="1e-9" diaginertia="1e-12 1e-12 1e-12"/>
            <geom name="load" type="sphere" size="0.035" contype="0" conaffinity="0" rgba="0.9 0.6 0.0 0"/>
          </body>
        </body>
      </body>
    </body>
  </worldbody>
  <actuator>
    <motor joint="j0" ctrlrange="{-limit} {limit}"/>
    <motor joint="j1" ctrlrange="{-limit} {limit}"/>
    <motor joint="j2" ctrlrange="{-limit} {limit}"/>
  </actuator>
</mujoco>
"""


def capsule_distance(th, scene, n=101):
    """Signed distance from each link capsule to each obstacle, shape (..., 2, obstacles): the
    link segments sampled at n points, exact point-to-box and point-to-half-space distances, minus
    rho. Sampling overestimates a positive distance by at most half the sample spacing."""
    P = points(th)
    s = np.linspace(0, 1, n)[:, None]
    segs = [P[..., None, 0, :] + s * (P[..., None, 1, :] - P[..., None, 0, :]),
            P[..., None, 1, :] + s * (P[..., None, 2, :] - P[..., None, 1, :])]
    out = []
    for seg in segs:
        row = []
        for o in scene["obstacles"]:
            if o["kind"] == "box":
                lo, hi = np.array(o["lo"], float), np.array(o["hi"], float)
                ext = np.linalg.norm(np.maximum(np.maximum(lo - seg, seg - hi), 0), axis=-1)
                dist = np.where(ext > 0, ext, -np.minimum(seg - lo, hi - seg).min(-1))
            else:
                nv = np.array(o["n"], float)
                dist = (seg @ nv - o["beta"]) / np.linalg.norm(nv)
            row.append(dist.min(-1) - rho)
        out.append(np.stack(row, -1))
    return np.stack(out, -2)
