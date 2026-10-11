import RoboLean.Geometry.RotationExp
import RoboLean.Geometry.Rodrigues
import RoboLean.Geometry.RotationAxis
import RoboLean.Geometry.RotationPlane
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Axis-angle existence for proper rotations

MLS Proposition 2.5 and Theorem 2.6, printed pp. 29–31. The fixed-axis
construction and the planar angle are independent of division by `sin θ`.
In particular, identity and half-turn cases remain in the domain.

The action of `exp ω θ` split along a unit axis (`exp_act_eq`) and the invariance of the axial
component (`inner_exp_act_axis`) moved here from `RoboLean.Kinematics.PadenKahan` on
2026-10-11.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Rotation

/-- A point on the unit circle has a real angle, including `(1,0)` and `(-1,0)`.
The complex argument chooses an angle in `(-π,π]`. -/
theorem exists_angle_of_sq_add_sq_eq_one (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ t : ℝ, -Real.pi < t ∧ t ≤ Real.pi ∧ Real.cos t = c ∧ Real.sin t = s := by
  let z : ℂ := ⟨c, s⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    change Real.sqrt (c * c + s * s) = 1
    rw [show c * c + s * s = 1 by simpa only [pow_two] using hcs, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  refine ⟨z.arg, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z, ?_, ?_⟩
  · simpa only [hn, div_one] using Complex.cos_arg hz
  · simpa only [hn, div_one] using Complex.sin_arg z

/-- A unit axis is fixed by its actual matrix exponential at every angle. -/
theorem exp_act_unit_axis (ω : Vec3) (hω : ‖ω‖ = 1) (t : ℝ) :
    (exp ω t).act ω = ω := by
  have hsq : Vec3.hat ω ^ 2 *ᵥ WithLp.ofLp ω = 0 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, Vec3.hat_mulVec_self, Matrix.mulVec_zero]
  apply WithLp.ofLp_injective
  change NormedSpace.exp (t • Vec3.hat ω) *ᵥ WithLp.ofLp ω = WithLp.ofLp ω
  rw [Vec3.exp_hat_of_norm_eq_one ω hω t]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Vec3.hat_mulVec_self, hsq, smul_zero, add_zero]

/-- On the plane perpendicular to a unit axis, actual Rodrigues action is the
cosine/sine combination of a vector and its right-handed quarter-turn. -/
theorem exp_act_of_inner_eq_zero (ω u : Vec3) (hω : ‖ω‖ = 1)
    (hperp : inner ℝ ω u = 0) (t : ℝ) :
    (exp ω t).act u = Real.cos t • u + Real.sin t • Vec3.cross ω u := by
  have hdot : WithLp.ofLp ω ⬝ᵥ WithLp.ofLp u = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm] using hperp
  have ho : Vec3.outer ω ω *ᵥ WithLp.ofLp u = 0 := by
    rw [Vec3.outer, Matrix.vecMulVec_mulVec, hdot]
    simp
  apply WithLp.ofLp_injective
  change NormedSpace.exp (t • Vec3.hat ω) *ᵥ WithLp.ofLp u =
    Real.cos t • WithLp.ofLp u + Real.sin t • WithLp.ofLp (Vec3.cross ω u)
  rw [Vec3.exp_hat_of_norm_eq_one ω hω t, Vec3.hat_sq_of_norm_eq_one ω hω]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.sub_mulVec, ho, Vec3.hat_mulVec]
  module

/-- **Rodrigues' formula on vectors, split along a unit axis** (MLS eq. (2.14), p. 28, applied
to `u = (ωᵀu) ω + u′`): `e^{ω̂θ} u = (ωᵀu) ω + cos θ u′ + sin θ (ω × u′)`. -/
theorem exp_act_eq {ω : Vec3} (hω : ‖ω‖ = 1) (θ : ℝ) (u : Vec3) :
    (Rotation.exp ω θ).act u =
      inner ℝ ω u • ω + Real.cos θ • Vec3.perp ω u +
        Real.sin θ • Vec3.cross ω (Vec3.perp ω u) := by
  have hu : u = inner ℝ ω u • ω + Vec3.perp ω u := by simp [Vec3.perp]
  have hp : inner ℝ ω (Vec3.perp ω u) = 0 := by
    simp [Vec3.perp, inner_sub_right, inner_smul_right, hω]
  conv_lhs => rw [hu]
  rw [map_add, map_smul, exp_act_unit_axis ω hω, exp_act_of_inner_eq_zero ω _ hω hp, add_assoc]

/-- A rotation about a unit axis `ω` preserves the component along `ω`: `ωᵀ(e^{ω̂θ} x) = ωᵀx`
(used for eq. (3.23), p. 101, and eq. (3.19), p. 100). -/
theorem inner_exp_act_axis {ω : Vec3} (hω : ‖ω‖ = 1) (θ : ℝ) (x : Vec3) :
    inner ℝ ω ((Rotation.exp ω θ).act x) = inner ℝ ω x := by
  calc inner ℝ ω ((Rotation.exp ω θ).act x)
      = inner ℝ ((Rotation.exp ω θ).act ω) ((Rotation.exp ω θ).act x) := by
        rw [exp_act_unit_axis ω hω θ]
    _ = inner ℝ ω x := inner_act _ ω x

/-- A fixed unit axis admits an angle in `(-π,π]` giving the whole rotation.
Cross-product covariance fixes the action on the third adapted basis vector;
no division by the sine of the angle is used. -/
theorem exists_angle_exp_eq_of_fixed_axis (R : Rotation) (ω : Vec3)
    (hω : ‖ω‖ = 1) (hfix : R.act ω = ω) :
    ∃ t : ℝ, -Real.pi < t ∧ t ≤ Real.pi ∧ exp ω t = R := by
  obtain ⟨u, hu, hperp⟩ := Vec3.exists_unit_orthogonal ω hω
  let b := Vec3.adaptedBasis ω u hω hu hperp
  let c := inner ℝ u (R.act u)
  let s := inner ℝ (Vec3.cross ω u) (R.act u)
  have horth : inner ℝ ω (R.act u) = 0 := by
    calc
      inner ℝ ω (R.act u) = inner ℝ (R.act ω) (R.act u) := by rw [hfix]
      _ = inner ℝ ω u := R.inner_act ω u
      _ = 0 := hperp
  have hdec : R.act u = c • u + s • Vec3.cross ω u := by
    have h := b.sum_repr' (R.act u)
    simpa [b, c, s, Fin.sum_univ_succ, horth] using h.symm
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have h := b.sum_sq_norm_inner_right (R.act u)
    simpa [b, c, s, Fin.sum_univ_succ, horth, hu, Real.norm_eq_abs] using h
  obtain ⟨t, htlo, hthi, hcos, hsin⟩ := exists_angle_of_sq_add_sq_eq_one c s hcs
  have hu_exp : (exp ω t).act u = R.act u := by
    rw [exp_act_of_inner_eq_zero ω u hω hperp t, hcos, hsin]
    exact hdec.symm
  have hω_exp : (exp ω t).act ω = R.act ω := by
    rw [exp_act_unit_axis ω hω t, hfix]
  have hcross_exp : (exp ω t).act (Vec3.cross ω u) = R.act (Vec3.cross ω u) := by
    rw [act_cross, act_cross, hω_exp, hu_exp]
  refine ⟨t, htlo, hthi, ?_⟩
  apply Subtype.ext
  apply Matrix.toEuclideanLin.injective
  change (exp ω t).act = R.act
  apply b.toBasis.ext
  intro i
  fin_cases i
  · simpa [b] using hω_exp
  · simpa [b] using hu_exp
  · simpa [b] using hcross_exp

/-- MLS Proposition 2.5, with a principal nonnegative angle. Every proper
rotation is the actual exponential of a unit axis with angle in `[0,π]`.
The identity and half-turns are included without a separate denominator formula. -/
theorem exists_unit_axis_angle_le_pi (R : Rotation) :
    ∃ ω : Vec3, ‖ω‖ = 1 ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ Real.pi ∧ exp ω t = R := by
  obtain ⟨ω, hω, hfix⟩ := R.exists_unit_axis
  obtain ⟨t, htlo, hthi, heq⟩ := exists_angle_exp_eq_of_fixed_axis R ω hω hfix
  by_cases ht : 0 ≤ t
  · exact ⟨ω, hω, t, ht, hthi, heq⟩
  · refine ⟨-ω, by simpa using hω, -t, by linarith, by linarith, ?_⟩
    have hscale : exp (-ω) (-t) = exp ω t := by
      simpa using exp_smul (-1 : ℝ) ω (-t)
    exact hscale.trans heq

/-- MLS Theorem 2.6: a unit axis and angle in `[0,2π)` represent every
proper rotation. This is existence, without a uniqueness or smooth-selection claim. -/
theorem exists_unit_axis_angle (R : Rotation) :
    ∃ ω : Vec3, ‖ω‖ = 1 ∧ ∃ t : ℝ,
      0 ≤ t ∧ t < 2 * Real.pi ∧ exp ω t = R := by
  obtain ⟨ω, hω, t, ht0, htπ, heq⟩ := exists_unit_axis_angle_le_pi R
  exact ⟨ω, hω, t, ht0, by linarith [Real.pi_pos], heq⟩

/-- The exponential map from unit axes and real angles is onto `Rotation`. -/
theorem exists_unit_exp (R : Rotation) :
    ∃ ω : Vec3, ‖ω‖ = 1 ∧ ∃ t : ℝ, exp ω t = R := by
  obtain ⟨ω, hω, t, _, _, heq⟩ := exists_unit_axis_angle R
  exact ⟨ω, hω, t, heq⟩

end Rotation
end RoboLean
