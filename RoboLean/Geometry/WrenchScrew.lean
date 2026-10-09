import RoboLean.Geometry.Wrench
import RoboLean.Geometry.TwistScrew
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Screw coordinates and Poinsot decomposition of wrenches

MLS printed pp. 64–66, equations (2.68)–(2.71) and Theorem 2.17 (ledger
X53–X57). Wrenches are ordered `(f, τ)`. The explicit algebraic swap to twist
coordinates is `(τ, f)`, so the nonzero angular branch of twist reconstruction
becomes the nonzero force branch here.

All coordinates concern one common frame, with moment measured about its
origin. Unit directions and nonnegative magnitudes are supplied by the
normalized reconstruction theorems. The zero wrench has a separate stationary
pitch tag and no axis; nonzero pure couples have infinite pitch. This extends
the source's zero-omitting convention explicitly. Affine axes below are genuine
one-dimensional subspaces with an offset; their directed signs are carried by
`forceDirection` and `coupleDirection`, not by the unoriented affine sets.

No common physical norm on force/moment coordinates, contact feasibility,
calibration, or uniqueness of a screw representation is asserted.
-/

noncomputable section

namespace RoboLean
namespace Wrench

/-- Algebraic coordinate swap `(f, τ) ↦ (τ, f)` used to reuse twist screw algebra. -/
def toTwist : Wrench ≃ₗ[ℝ] Twist := LinearEquiv.prodComm ℝ Vec3 Vec3

@[simp] theorem toTwist_linear (F : Wrench) : (toTwist F).linear = F.torque := rfl
@[simp] theorem toTwist_angular (F : Wrench) : (toTwist F).angular = F.force := rfl

theorem toTwist_eq_zero_iff (F : Wrench) : toTwist F = 0 ↔ F = 0 := by
  constructor
  · intro h
    apply toTwist.injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero toTwist

/-- MLS (2.68), finite pitch. Geometric use requires a unit direction separately. -/
def fromScrew (ω q : Vec3) (pitch magnitude : ℝ) : Wrench :=
  magnitude • (ω, -Vec3.cross ω q + pitch • ω)

/-- MLS (2.68), infinite pitch: a pure couple about the supplied direction. -/
def pureCouple (ω : Vec3) (magnitude : ℝ) : Wrench := (0, magnitude • ω)

@[simp] theorem fromScrew_force (ω q : Vec3) (h M : ℝ) :
    (fromScrew ω q h M).force = M • ω := rfl

@[simp] theorem fromScrew_torque (ω q : Vec3) (h M : ℝ) :
    (fromScrew ω q h M).torque = M • (-Vec3.cross ω q + h • ω) := rfl

@[simp] theorem pureCouple_force (ω : Vec3) (M : ℝ) :
    (pureCouple ω M).force = 0 := rfl

@[simp] theorem pureCouple_torque (ω : Vec3) (M : ℝ) :
    (pureCouple ω M).torque = M • ω := rfl

/-- The swap of the source wrench constructor is exactly the twist constructor. -/
theorem toTwist_fromScrew (ω q : Vec3) (h M : ℝ) :
    toTwist (fromScrew ω q h M) = M • Twist.fromScrew ω q h := rfl

/-- Shifting the chosen point along the axis does not change the wrench. -/
theorem fromScrew_axis_shift (ω q : Vec3) (h M r : ℝ) :
    fromScrew ω (q + r • ω) h M = fromScrew ω q h M := by
  apply toTwist.injective
  rw [toTwist_fromScrew, toTwist_fromScrew, Twist.fromScrew_axis_shift]

/-- MLS (2.69), defined only on the nonzero-force branch. -/
def finitePitch (F : Wrench) (hf : F.force ≠ 0) : ℝ :=
  Twist.finitePitch (toTwist F) hf

theorem finitePitch_eq (F : Wrench) (hf : F.force ≠ 0) :
    finitePitch F hf = inner ℝ F.force F.torque / ‖F.force‖ ^ 2 := rfl

/-- MLS (2.70): the perpendicular representative point on a finite wrench axis. -/
def axisPoint (F : Wrench) (hf : F.force ≠ 0) : Vec3 :=
  Twist.axisPoint (toTwist F) hf

theorem axisPoint_eq (F : Wrench) (hf : F.force ≠ 0) :
    axisPoint F hf = (‖F.force‖ ^ 2)⁻¹ • Vec3.cross F.force F.torque := rfl

theorem axisPoint_orthogonal (F : Wrench) (hf : F.force ≠ 0) :
    inner ℝ F.force (axisPoint F hf) = 0 :=
  Twist.axisPoint_orthogonal (toTwist F) hf

/-- Actual moment reconstruction includes the origin-dependent axis offset. -/
theorem finite_reconstruction (F : Wrench) (hf : F.force ≠ 0) :
    F.torque = Vec3.cross (axisPoint F hf) F.force + finitePitch F hf • F.force := by
  have h := Twist.finite_reconstruction (toTwist F) hf
  change F.torque = -Vec3.cross F.force (axisPoint F hf) + finitePitch F hf • F.force at h
  rw [Vec3.cross_anticomm F.force (axisPoint F hf), neg_neg] at h
  exact h

private theorem norm_normalized (v : Vec3) (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

private theorem norm_smul_normalized (v : Vec3) (hv : v ≠ 0) :
    ‖v‖ • (‖v‖⁻¹ • v) = v := by
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

/-- Unit direction carrying the signed force direction in the finite branch. -/
def forceDirection (F : Wrench) (_hf : F.force ≠ 0) : Vec3 := ‖F.force‖⁻¹ • F.force

theorem norm_forceDirection (F : Wrench) (hf : F.force ≠ 0) :
    ‖forceDirection F hf‖ = 1 := norm_normalized F.force hf

/-- Finite-pitch reconstruction with unit direction and positive force magnitude. -/
theorem fromScrew_reconstruction (F : Wrench) (hf : F.force ≠ 0) :
    fromScrew (forceDirection F hf) (axisPoint F hf) (finitePitch F hf) ‖F.force‖ = F := by
  apply toTwist.injective
  rw [toTwist_fromScrew, Twist.fromScrew_smul]
  have hn : ‖F.force‖ • forceDirection F hf = F.force := norm_smul_normalized _ hf
  rw [hn]
  exact Twist.fromScrew_reconstruction (toTwist F) hf

/-- Unit direction of a nonzero pure couple. -/
def coupleDirection (F : Wrench) (_hτ : F.torque ≠ 0) : Vec3 := ‖F.torque‖⁻¹ • F.torque

theorem norm_coupleDirection (F : Wrench) (hτ : F.torque ≠ 0) :
    ‖coupleDirection F hτ‖ = 1 := norm_normalized F.torque hτ

/-- A force-free nonzero wrench reconstructs as a normalized pure couple. -/
theorem pureCouple_reconstruction (F : Wrench) (hf : F.force = 0) (hτ : F.torque ≠ 0) :
    pureCouple (coupleDirection F hτ) ‖F.torque‖ = F := by
  apply Prod.ext
  · exact hf.symm
  · exact norm_smul_normalized _ hτ

/-- Poinsot's algebraic representation, with all three degeneracy branches explicit.
The nonzero branches have unit directions and strictly positive magnitudes. -/
theorem poinsot (F : Wrench) :
    F = 0 ∨
      (F.force = 0 ∧ ∃ ω M, ‖ω‖ = 1 ∧ 0 < M ∧ pureCouple ω M = F) ∨
      (F.force ≠ 0 ∧ ∃ ω q h M, ‖ω‖ = 1 ∧ 0 < M ∧ fromScrew ω q h M = F) := by
  by_cases hf : F.force = 0
  · by_cases hτ : F.torque = 0
    · exact Or.inl (Prod.ext hf hτ)
    · exact Or.inr (Or.inl ⟨hf, coupleDirection F hτ, ‖F.torque‖,
        norm_coupleDirection F hτ, norm_pos_iff.mpr hτ, pureCouple_reconstruction F hf hτ⟩)
  · exact Or.inr (Or.inr ⟨hf, forceDirection F hf, axisPoint F hf, finitePitch F hf,
      ‖F.force‖, norm_forceDirection F hf, norm_pos_iff.mpr hf, fromScrew_reconstruction F hf⟩)

/-- Finite, pure-couple infinite, or zero-wrench stationary pitch. -/
def screwPitch (F : Wrench) : ScrewPitch := Twist.screwPitch (toTwist F)

@[simp] theorem screwPitch_of_force_ne_zero (F : Wrench) (hf : F.force ≠ 0) :
    screwPitch F = .finite (finitePitch F hf) :=
  Twist.screwPitch_of_angular_ne_zero (toTwist F) hf

@[simp] theorem screwPitch_zero : screwPitch (0 : Wrench) = .stationary := by
  simp [screwPitch]

theorem screwPitch_eq_stationary_iff (F : Wrench) :
    screwPitch F = .stationary ↔ F = 0 := by
  rw [screwPitch, Twist.screwPitch_eq_stationary_iff, toTwist_eq_zero_iff]

theorem screwPitch_eq_infinite_iff (F : Wrench) :
    screwPitch F = .infinite ↔ F.force = 0 ∧ F.torque ≠ 0 :=
  Twist.screwPitch_eq_infinite_iff (toTwist F)

theorem screwPitch_smul (F : Wrench) (c : ℝ) (hc : c ≠ 0) :
    screwPitch (c • F) = screwPitch F := by
  unfold screwPitch
  rw [map_smul, Twist.screwPitch_smul _ c hc]

/-- The genuine finite affine axis through the perpendicular point, in force direction. -/
def finiteAxis (F : Wrench) (hf : F.force ≠ 0) : AffineSubspace ℝ Vec3 :=
  AffineSubspace.mk' (axisPoint F hf) (Submodule.span ℝ {F.force})

theorem mem_finiteAxis (F : Wrench) (hf : F.force ≠ 0) (x : Vec3) :
    x ∈ finiteAxis F hf ↔ ∃ r : ℝ, x = axisPoint F hf + r • F.force := by
  rw [finiteAxis, AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  change (∃ r : ℝ, r • F.force = x - axisPoint F hf) ↔ _
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, by simpa only [add_comm] using (sub_eq_iff_eq_add.mp hr.symm)⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩

theorem finiteAxis_direction_finrank (F : Wrench) (hf : F.force ≠ 0) :
    Module.finrank ℝ (finiteAxis F hf).direction = 1 := by
  rw [finiteAxis, AffineSubspace.direction_mk']
  exact finrank_span_singleton hf

/-- Source pure-couple axis convention: the line through the origin in moment direction. -/
def coupleAxis (F : Wrench) (_hf : F.force = 0) (_hτ : F.torque ≠ 0) :
    AffineSubspace ℝ Vec3 := AffineSubspace.mk' 0 (Submodule.span ℝ {F.torque})

theorem mem_coupleAxis (F : Wrench) (hf : F.force = 0) (hτ : F.torque ≠ 0) (x : Vec3) :
    x ∈ coupleAxis F hf hτ ↔ ∃ r : ℝ, x = r • F.torque := by
  simp [coupleAxis, AffineSubspace.mem_mk', Submodule.mem_span_singleton, eq_comm]

theorem coupleAxis_direction_finrank (F : Wrench) (hf : F.force = 0) (hτ : F.torque ≠ 0) :
    Module.finrank ℝ (coupleAxis F hf hτ).direction = 1 := by
  rw [coupleAxis, AffineSubspace.direction_mk']
  exact finrank_span_singleton hτ

/-- MLS axis branches with an explicit absent axis for the zero wrench. -/
def screwAxis (F : Wrench) : Option (AffineSubspace ℝ Vec3) := by
  classical
  exact if hf : F.force = 0 then
    if hτ : F.torque = 0 then none else some (coupleAxis F hf hτ)
  else some (finiteAxis F hf)

@[simp] theorem screwAxis_of_force_ne_zero (F : Wrench) (hf : F.force ≠ 0) :
    screwAxis F = some (finiteAxis F hf) := by
  simp [screwAxis, hf]

@[simp] theorem screwAxis_of_pureCouple (F : Wrench) (hf : F.force = 0) (hτ : F.torque ≠ 0) :
    screwAxis F = some (coupleAxis F hf hτ) := by
  simp [screwAxis, hf, hτ]

@[simp] theorem screwAxis_zero : screwAxis (0 : Wrench) = none := by
  simp [screwAxis, force, torque]

theorem screwAxis_eq_none_iff (F : Wrench) : screwAxis F = none ↔ F = 0 := by
  classical
  rcases F with ⟨f, τ⟩
  by_cases hf : f = 0 <;> by_cases hτ : τ = 0 <;>
    simp [screwAxis, force, torque, hf, hτ]

/-- MLS (2.71), a branch-dependent nonnegative magnitude rather than a mixed-unit norm. -/
def screwMagnitude (F : Wrench) : ℝ := Twist.screwMagnitude (toTwist F)

@[simp] theorem screwMagnitude_of_force_eq_zero (F : Wrench) (hf : F.force = 0) :
    screwMagnitude F = ‖F.torque‖ :=
  Twist.screwMagnitude_of_angular_eq_zero (toTwist F) hf

@[simp] theorem screwMagnitude_of_force_ne_zero (F : Wrench) (hf : F.force ≠ 0) :
    screwMagnitude F = ‖F.force‖ :=
  Twist.screwMagnitude_of_angular_ne_zero (toTwist F) hf

@[simp] theorem screwMagnitude_zero : screwMagnitude (0 : Wrench) = 0 := by
  simp [screwMagnitude]

theorem screwMagnitude_nonneg (F : Wrench) : 0 ≤ screwMagnitude F :=
  Twist.screwMagnitude_nonneg (toTwist F)

theorem screwMagnitude_eq_zero_iff (F : Wrench) : screwMagnitude F = 0 ↔ F = 0 := by
  rw [screwMagnitude, Twist.screwMagnitude_eq_zero_iff, toTwist_eq_zero_iff]

theorem screwMagnitude_smul (F : Wrench) (c : ℝ) :
    screwMagnitude (c • F) = |c| * screwMagnitude F := by
  unfold screwMagnitude
  rw [map_smul, Twist.screwMagnitude_smul]

end Wrench
end RoboLean
