# The controller's nominal model of the cell arm: the unloaded arm of arm.py plus a known rotor
# inertia J on every joint (a diagonal added to the inertia matrix) and, while the part is held, a
# nominal point mass m_hat at the tool point. With the payload terms per unit mass written from the
# library's toolInertia, toolCoriolis and toolGravity:
#   M_hat(theta) = M(theta) + J I + m_hat Jt^T Jt,
#   C_hat theta' = C theta' + m_hat toolCoriolis(theta, theta'),
#   N_hat = N + m_hat toolGravity(theta),
# with Jt the Jacobian of the tool point. Joint order and conventions as in arm.py (base yaw,
# shoulder, elbow; radians, seconds, kg, kg m^2, N m); every function takes arrays with the joint
# index last and broadcasts over leading axes.
import numpy as np

import arm


def reach(th):
    """The tool's horizontal reach R = l1 cos th1 + l2 cos(th1 + th2) and its drop below the
    shoulder Z = l1 sin th1 + l2 sin(th1 + th2) (m)."""
    c1, s1, c2, s2, c12, s12 = arm.trig(th)
    return arm.l1 * c1 + arm.l2 * c12, arm.l1 * s1 + arm.l2 * s12


def tool_inertia(th):
    """The payload's inertia per unit mass, Jt^T Jt for the Jacobian Jt of the tool point (m^2)."""
    c1, s1, c2, s2, c12, s12 = arm.trig(th)
    R, Z = reach(th)
    A = np.zeros(th.shape[:-1] + (3, 3))
    A[..., 0, 0] = R**2
    A[..., 1, 1] = arm.l1**2 + arm.l2**2 + 2 * arm.l1 * arm.l2 * c2
    A[..., 1, 2] = A[..., 2, 1] = arm.l2**2 + arm.l1 * arm.l2 * c2
    A[..., 2, 2] = arm.l2**2
    return A


def tool_coriolis(th, thd):
    """The payload's Coriolis and centrifugal term per unit mass (m^2/s^2)."""
    c1, s1, c2, s2, c12, s12 = arm.trig(th)
    R, Z = reach(th)
    v0, v1, v2 = thd[..., 0], thd[..., 1], thd[..., 2]
    k = arm.l1 * arm.l2 * s2
    return np.stack([-2 * R * v0 * (Z * v1 + arm.l2 * s12 * v2),
                     R * Z * v0**2 - k * (2 * v1 * v2 + v2**2),
                     arm.l2 * s12 * R * v0**2 + k * v1**2], -1)


def tool_gravity(th):
    """The payload's gravity term per unit mass, g times the gradient of the tool's height
    (m^2/s^2)."""
    c1, s1, c2, s2, c12, s12 = arm.trig(th)
    R, Z = reach(th)
    return np.stack([0 * R, -arm.g * R, -arm.g * arm.l2 * c12], -1)


def mass(th, rotor=0.0, payload=0.0):
    """M_hat(theta) = M(theta) + J I + m_hat Jt^T Jt; `rotor` (kg m^2) a number or one per joint
    (joint index last), `payload` (kg) a number or one per sample (both broadcast over the leading
    axes)."""
    M = arm.mass(th) + (np.zeros(3) + rotor)[..., None] * np.eye(3)
    return M + np.asarray(payload, float)[..., None, None] * tool_inertia(th)


def bias(th, thd, payload=0.0):
    """C_hat(theta, theta') theta' + N_hat(theta) = C theta' + N + m_hat (toolCoriolis + toolGravity)."""
    return arm.bias(th, thd) + np.asarray(payload, float)[..., None] * (tool_coriolis(th, thd) + tool_gravity(th))


def computed_torque(w, r, rd, rdd, th, thd, rotor=0.0, payload=0.0):
    """Computed torque M_hat (r'' - 2 w (theta' - r') - w^2 (theta - r)) + C_hat theta' + N_hat on the
    nominal model; with no rotor inertia and no payload it is arm.computed_torque, computed by it."""
    if not np.any(rotor) and not np.any(payload):
        return arm.computed_torque(w, r, rd, rdd, th, thd)
    a = rdd - 2 * w * (thd - rd) - w**2 * (th - r)
    return np.einsum("...ij,...j->...i", mass(th, rotor, payload), a) + bias(th, thd, payload)
