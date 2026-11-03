import RoboLean.Grasp.SpatialAntipodal
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Spatial antipodal grasps: the "only if" direction of Theorem 5.7 restated

MLS Chapter 5, §4.2, printed p. 233: "**Theorem 5.7. Spatial antipodal grasps** [82]. A spatial
grasp with two soft-finger contacts is force-closure if and only if the line connecting the
contact point lies inside both friction cones." No proof is printed. The "if" direction is
`spatial_softFinger_isForceClosure_of_lineInsideCones`; the "only if" direction as printed is
false in the library's soft-finger model (`Examples.softAntipodal_onlyIf_counterexample`).

This file states what does hold for the "only if" direction, in the same model (soft-finger
contacts of eq. (5.4), p. 217, with `μ > 0` and torsional coefficient `γ > 0`, contact frames
`g_{ocᵢ} = (pᵢ, Rᵢ)` with the contact `z`-axis the inward normal, pp. 214–215):

* the torsional form: a force-closure grasp carries opposite forces `F` and `-F`, strictly inside
  the two Coulomb cones, and torsions `t₀, t₁` strictly inside their bounds `|tᵢ| < γ fᵢ₃` with
  `(p₁ - p₀) × F = t₀ n₀ + t₁ n₁`: the moment of the pair of forces about the line is balanced by
  the torsions, which is how a force-closure grasp can have the line outside a cone;
* the coplanar form: when the two inward normals `n₀ = R₀ e_z`, `n₁ = R₁ e_z` and the line
  `p₁ - p₀` lie in one plane (a nonzero vector orthogonal to all three exists) and the first
  normal does not point away from the second contact, force-closure implies that the line lies
  inside both open friction cones, for every `γ > 0`; with the "if" direction this is the printed
  equivalence under these two hypotheses, which the book does not state.

Derivation of the coplanar form: with `m` orthogonal to `n₀`, `n₁` and `d = p₁ - p₀`, the
balance gives `m · (d × F) = 0`, and the expansion of `F` in `m`, `d`, `m × d` gives
`|d|² (n · F) = (d · F)(n · d)` for `n = n₀, n₁`; Cauchy–Schwarz then moves the strict Coulomb
inequality from `F` to `d`.

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

open Matrix

namespace RoboLean.Grasp

/-- The inward normal `nᵢ = Rᵢ e_z` of contact `i` of a two-contact spatial grasp, in object
coordinates: the third column of `Rᵢ`, with `g_{ocᵢ} = (pᵢ, Rᵢ)` and the contact `z`-axis along the
inward normal (MLS printed pp. 214–215; Theorem 5.7, p. 233). -/
def spatialContactNormal (frame : Fin 2 → RigidTransform) (i : Fin 2) : Fin 3 → ℝ :=
  fun k => (frame i).rotation.val k 2

/-- The line connecting the two contacts of a spatial grasp, `d = p₁ - p₀` in object coordinates
(MLS Theorem 5.7, printed p. 233, "the line connecting the contact point"). -/
def contactLine (frame : Fin 2 → RigidTransform) : Fin 3 → ℝ :=
  WithLp.ofLp ((frame 1).translation - (frame 0).translation)

private theorem graspMap_softFinger_coords {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (frame : Fin 2 → RigidTransform) (c : Fin 2 → Fin 4 → ℝ) :
    WithLp.ofLp ((ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
        frame).toGrasp.map c).force =
      (frame 0).rotation.val *ᵥ ![c 0 0, c 0 1, c 0 2] +
        (frame 1).rotation.val *ᵥ ![c 1 0, c 1 1, c 1 2] ∧
    WithLp.ofLp ((ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
        frame).toGrasp.map c).torque =
      WithLp.ofLp (frame 0).translation ⨯₃ ((frame 0).rotation.val *ᵥ ![c 0 0, c 0 1, c 0 2]) +
        c 0 3 • spatialContactNormal frame 0 +
      (WithLp.ofLp (frame 1).translation ⨯₃ ((frame 1).rotation.val *ᵥ ![c 1 0, c 1 1, c 1 2]) +
        c 1 3 • spatialContactNormal frame 1) := by
  rw [ContactGrasp.toGrasp_map, ContactGrasp.graspMap_apply, Fin.sum_univ_two,
    ContactGrasp.spatial_contactMap_apply, ContactGrasp.spatial_contactMap_apply,
    ContactModel.softFinger_wrench, ContactModel.softFinger_wrench]
  constructor
  · ext k
    fin_cases k <;> simp [Wrench.transform, Rotation.act_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, spatialContactNormal]
    fin_cases k <;> simp [Wrench.transform, Rotation.act_apply, Vec3.cross_coordinates,
      crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private theorem dotProduct_rot_mulVec (R : Rotation) (u v : Fin 3 → ℝ) :
    (R.val *ᵥ u) ⬝ᵥ (R.val *ᵥ v) = u ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, Rotation.transpose_mul, one_mulVec]

private theorem dotProduct_rotT_mulVec (R : Rotation) (u v : Fin 3 → ℝ) :
    (R.valᵀ *ᵥ u) ⬝ᵥ (R.valᵀ *ᵥ v) = u ⬝ᵥ v := by
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, Rotation.mul_transpose, one_mulVec]

private theorem spatialContactNormal_eq (frame : Fin 2 → RigidTransform) (i : Fin 2) :
    spatialContactNormal frame i = (frame i).rotation.val *ᵥ ![0, 0, 1] := by
  ext k
  simp [spatialContactNormal, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem cross_expansion (m d F u : Fin 3 → ℝ) :
    ((m ⬝ᵥ m) * (d ⬝ᵥ d) - (m ⬝ᵥ d) ^ 2) * (F ⬝ᵥ u) =
      ((d ⬝ᵥ d) * (F ⬝ᵥ m) - (m ⬝ᵥ d) * (F ⬝ᵥ d)) * (m ⬝ᵥ u) +
        ((m ⬝ᵥ m) * (F ⬝ᵥ d) - (m ⬝ᵥ d) * (F ⬝ᵥ m)) * (d ⬝ᵥ u) +
        (m ⬝ᵥ (d ⨯₃ F)) * ((m ⨯₃ d) ⬝ᵥ u) := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply]
  simp
  ring

private theorem sq_dotProduct_le (F d : Fin 3 → ℝ) : (F ⬝ᵥ d) ^ 2 ≤ (F ⬝ᵥ F) * (d ⬝ᵥ d) := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (F 0 * d 1 - F 1 * d 0), sq_nonneg (F 1 * d 2 - F 2 * d 1),
    sq_nonneg (F 0 * d 2 - F 2 * d 0)]

private theorem cone_transfer {μ N S D A e x₀ x₁ y₀ y₁ : ℝ} (hμ : 0 < μ)
    (hx : √(x₀ ^ 2 + x₁ ^ 2) < μ * N) (hS : S = x₀ ^ 2 + x₁ ^ 2 + N ^ 2) (hD : 0 < D)
    (hCS : A ^ 2 ≤ S * D) (hDN : D * N = A * e) (he : 0 < e) (hy : y₀ ^ 2 + y₁ ^ 2 + e ^ 2 = D) :
    √(y₀ ^ 2 + y₁ ^ 2) < μ * e := by
  have hN : 0 < N := by
    have := Real.sqrt_nonneg (x₀ ^ 2 + x₁ ^ 2)
    by_contra h
    nlinarith
  have hq := (Real.sqrt_lt' (by positivity)).1 hx
  have hA : 0 < A := by
    by_contra h
    nlinarith [mul_pos hD hN]
  rw [Real.sqrt_lt' (by positivity)]
  have h1 : A ^ 2 * (y₀ ^ 2 + y₁ ^ 2) = A ^ 2 * D - (D * N) ^ 2 := by
    rw [hDN, ← hy]
    ring
  have key : A ^ 2 * (y₀ ^ 2 + y₁ ^ 2) < A ^ 2 * (μ * e) ^ 2 := by
    rw [h1]
    have h2 : A ^ 2 * D ≤ S * D ^ 2 := by nlinarith
    have h3 : D ^ 2 * (x₀ ^ 2 + x₁ ^ 2) < D ^ 2 * (μ * N) ^ 2 :=
      mul_lt_mul_of_pos_left hq (by positivity)
    have h4 : A ^ 2 * (μ * e) ^ 2 = D ^ 2 * (μ * N) ^ 2 := by
      have : (μ * (A * e)) ^ 2 = (μ * (D * N)) ^ 2 := by rw [hDN]
      nlinarith
    rw [h4]
    nlinarith
  exact lt_of_mul_lt_mul_left key (sq_nonneg A)

/-- An interior point of the soft-finger friction cone of MLS eq. (5.4), printed p. 217, meets
the strict inequalities `√(f₁² + f₂²) < μ f₃` and `|f₄| < γ f₃` (for `μ > 0`, `γ > 0`; `int(FC)`
of p. 223). -/
theorem lt_of_mem_interior_softFingerCone {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) {f : Fin 4 → ℝ}
    (hf : f ∈ interior (softFingerCone μ γ : Set (Fin 4 → ℝ))) :
    √(f 0 ^ 2 + f 1 ^ 2) < μ * f 2 ∧ |f 3| < γ * f 2 := by
  have hcont : Continuous fun t : ℝ => f + t • (![0, 0, -1, 0] : Fin 4 → ℝ) := by fun_prop
  have h0 : f + (0 : ℝ) • (![0, 0, -1, 0] : Fin 4 → ℝ) ∈
      interior (softFingerCone μ γ : Set (Fin 4 → ℝ)) := by simpa using hf
  have hev := hcont.continuousAt.eventually_mem (isOpen_interior.mem_nhds h0)
  obtain ⟨t, ht, htpos⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hmem := interior_subset ht
  simp only [SetLike.mem_coe, mem_softFingerCone, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hmem
  simp at hmem htpos
  obtain ⟨h1, h2, h3⟩ := hmem
  exact ⟨by nlinarith, by nlinarith⟩

/-- **MLS Theorem 5.7, "only if", torsional form**, printed p. 233: a force-closure spatial grasp
of two soft-finger contacts (eq. (5.4), p. 217, `μ > 0`, `γ > 0`) carries contact-frame forces
`x₀`, `x₁` strictly inside the Coulomb cones and torsions `t₀`, `t₁` strictly inside their bounds,
with opposite object-frame forces `R₀ x₀ + R₁ x₁ = 0` and the balance
`(p₁ - p₀) × (R₀ x₀) = t₀ n₀ + t₁ n₁`. When the torsions vanish, `R₀ x₀` is along the line and the
printed conclusion follows; in general the torsions balance the moment of the two forces about
the line. Finite-force caveat (MLS p. 214). -/
theorem spatial_softFinger_exists_balance_of_isForceClosure {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (frame : Fin 2 → RigidTransform)
    (h : (ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
      frame).toGrasp.IsForceClosure) :
    ∃ (x₀ x₁ : Fin 3 → ℝ) (t₀ t₁ : ℝ),
      √(x₀ 0 ^ 2 + x₀ 1 ^ 2) < μ * x₀ 2 ∧ |t₀| < γ * x₀ 2 ∧
      √(x₁ 0 ^ 2 + x₁ 1 ^ 2) < μ * x₁ 2 ∧ |t₁| < γ * x₁ 2 ∧
      (frame 0).rotation.val *ᵥ x₀ + (frame 1).rotation.val *ᵥ x₁ = 0 ∧
      contactLine frame ⨯₃ ((frame 0).rotation.val *ᵥ x₀) =
        t₀ • spatialContactNormal frame 0 + t₁ • spatialContactNormal frame 1 := by
  obtain ⟨-, c, hGc, hint⟩ := (Grasp.isForceClosure_iff _).1 h
  rw [ContactGrasp.toGrasp_cone, ContactGrasp.mem_interior_cone] at hint
  have h0 := lt_of_mem_interior_softFingerCone hμ hγ (hint 0)
  have h1 := lt_of_mem_interior_softFingerCone hμ hγ (hint 1)
  obtain ⟨hF, hT⟩ := graspMap_softFinger_coords hμ hγ frame c
  rw [hGc] at hF hT
  simp only [Wrench.zero_force, Wrench.zero_torque, WithLp.ofLp_zero] at hF hT
  refine ⟨![c 0 0, c 0 1, c 0 2], ![c 1 0, c 1 1, c 1 2], c 0 3, c 1 3, h0.1, h0.2, h1.1, h1.2,
    hF.symm, ?_⟩
  have hG := eq_neg_of_add_eq_zero_right hF.symm
  rw [hG, map_neg] at hT
  rw [contactLine, WithLp.ofLp_sub, map_sub, LinearMap.sub_apply]
  linear_combination (norm := module) hT

/-- **MLS Theorem 5.7, "only if", for coplanar normals**, printed p. 233: if the two inward
normals and the connecting line lie in one plane (a nonzero `m` orthogonal to `n₀`, `n₁` and
`p₁ - p₀`) and the first normal does not point away from the second contact
(`n₀ · (p₁ - p₀) ≥ 0`), then a force-closure grasp of two soft-finger contacts (eq. (5.4),
p. 217, `μ > 0`, `γ > 0`) has the line inside both open friction cones (`√(x₁² + x₂²) < μ x₃` for
the direction `x` to the other contact in each contact frame), for every torsional coefficient.
Both hypotheses are added to the printed statement. Finite-force caveat (MLS p. 214). -/
theorem spatial_softFinger_lineInsideCones_of_isForceClosure {μ γ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (frame : Fin 2 → RigidTransform) (m : Fin 3 → ℝ) (hm : m ≠ 0)
    (hm₀ : m ⬝ᵥ spatialContactNormal frame 0 = 0) (hm₁ : m ⬝ᵥ spatialContactNormal frame 1 = 0)
    (hmd : m ⬝ᵥ contactLine frame = 0) (hface : 0 ≤ contactDirection frame 0 1 2)
    (h : (ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
      frame).toGrasp.IsForceClosure) :
    √(contactDirection frame 0 1 0 ^ 2 + contactDirection frame 0 1 1 ^ 2) <
        μ * contactDirection frame 0 1 2 ∧
      √(contactDirection frame 1 0 0 ^ 2 + contactDirection frame 1 0 1 ^ 2) <
        μ * contactDirection frame 1 0 2 := by
  have hmm : 0 < m ⬝ᵥ m := by
    refine lt_of_le_of_ne ?_ (fun h0 => hm (dotProduct_self_eq_zero.1 h0.symm))
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [mul_self_nonneg (m 0), mul_self_nonneg (m 1), mul_self_nonneg (m 2)]
  -- the contacts are distinct: otherwise the wrench `(0, m)` is not reached
  have hD : 0 < contactLine frame ⬝ᵥ contactLine frame := by
    refine lt_of_le_of_ne ?_ (fun h0 => ?_)
    · simp only [dotProduct, Fin.sum_univ_three]
      nlinarith [mul_self_nonneg (contactLine frame 0), mul_self_nonneg (contactLine frame 1),
        mul_self_nonneg (contactLine frame 2)]
    have hd := dotProduct_self_eq_zero.1 h0.symm
    obtain ⟨c', hc'⟩ := ((Grasp.isForceClosure_iff _).1 h).1 ⟨0, WithLp.toLp 2 m⟩
    obtain ⟨hF', hT'⟩ := graspMap_softFinger_coords hμ hγ frame c'
    rw [hc'] at hF' hT'
    simp only [WithLp.ofLp_zero] at hF' hT'
    have hG' := eq_neg_of_add_eq_zero_right hF'.symm
    have hp : WithLp.ofLp (frame 1).translation = WithLp.ofLp (frame 0).translation := by
      rw [← sub_eq_zero, ← WithLp.ofLp_sub]
      exact hd
    have key : m = c' 0 3 • spatialContactNormal frame 0 + c' 1 3 • spatialContactNormal frame 1 := by
      rw [hT', hp, hG', map_neg]
      abel
    have : m ⬝ᵥ m = 0 := by
      nth_rewrite 2 [key]
      simp [dotProduct_add, dotProduct_smul, hm₀, hm₁]
    exact hmm.ne' this
  obtain ⟨x₀, x₁, t₀, t₁, hc₀, -, hc₁, -, hsum, hbal⟩ :=
    spatial_softFinger_exists_balance_of_isForceClosure hμ hγ frame h
  have hG := eq_neg_of_add_eq_zero_right hsum
  have hmF : m ⬝ᵥ (contactLine frame ⨯₃ ((frame 0).rotation.val *ᵥ x₀)) = 0 := by
    rw [hbal, dotProduct_add, dotProduct_smul, dotProduct_smul, hm₀, hm₁]
    simp
  -- `|d|² (n · F) = (d · F)(n · d)` for both normals
  have hsplit : ∀ u : Fin 3 → ℝ, m ⬝ᵥ u = 0 →
      (contactLine frame ⬝ᵥ contactLine frame) * (((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ u) =
        (((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ contactLine frame) * (contactLine frame ⬝ᵥ u) := by
    intro u hu
    have e := cross_expansion m (contactLine frame) ((frame 0).rotation.val *ᵥ x₀) u
    rw [hmd, hu, hmF] at e
    have : (m ⬝ᵥ m) * ((contactLine frame ⬝ᵥ contactLine frame) *
        (((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ u) - (((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ
          contactLine frame) * (contactLine frame ⬝ᵥ u)) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hmm.ne'
    · linarith
  have hN₀ : ((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ spatialContactNormal frame 0 = x₀ 2 := by
    rw [spatialContactNormal_eq, dotProduct_rot_mulVec]
    simp [dotProduct, Fin.sum_univ_three]
  have hN₁ : ((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ spatialContactNormal frame 1 = -x₁ 2 := by
    rw [← neg_neg ((frame 0).rotation.val *ᵥ x₀), ← hG, neg_dotProduct, spatialContactNormal_eq,
      dotProduct_rot_mulVec]
    simp [dotProduct, Fin.sum_univ_three]
  have hS₀ : ((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ ((frame 0).rotation.val *ᵥ x₀) =
      x₀ 0 ^ 2 + x₀ 1 ^ 2 + x₀ 2 ^ 2 := by
    rw [dotProduct_rot_mulVec]
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  have hS₁ : ((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ ((frame 0).rotation.val *ᵥ x₀) =
      x₁ 0 ^ 2 + x₁ 1 ^ 2 + x₁ 2 ^ 2 := by
    rw [← neg_neg ((frame 0).rotation.val *ᵥ x₀), ← hG, neg_dotProduct, dotProduct_neg, neg_neg,
      dotProduct_rot_mulVec]
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  have he₀ : contactLine frame ⬝ᵥ spatialContactNormal frame 0 = contactDirection frame 0 1 2 := by
    simp [contactDirection, contactLine, spatialContactNormal, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.transpose_apply]
    ring
  have he₁ : contactLine frame ⬝ᵥ spatialContactNormal frame 1 = -contactDirection frame 1 0 2 := by
    simp [contactDirection, contactLine, spatialContactNormal, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.transpose_apply]
    ring
  have hy₀ : contactDirection frame 0 1 0 ^ 2 + contactDirection frame 0 1 1 ^ 2 +
      contactDirection frame 0 1 2 ^ 2 = contactLine frame ⬝ᵥ contactLine frame := by
    rw [← dotProduct_rotT_mulVec (frame 0).rotation]
    simp only [contactDirection, contactLine, dotProduct, Fin.sum_univ_three]
    ring
  have hy₁ : contactDirection frame 1 0 0 ^ 2 + contactDirection frame 1 0 1 ^ 2 +
      contactDirection frame 1 0 2 ^ 2 = contactLine frame ⬝ᵥ contactLine frame := by
    have hd1 : WithLp.ofLp ((frame 0).translation - (frame 1).translation) = -contactLine frame := by
      rw [contactLine, ← WithLp.ofLp_neg, neg_sub]
    calc contactDirection frame 1 0 0 ^ 2 + contactDirection frame 1 0 1 ^ 2 +
          contactDirection frame 1 0 2 ^ 2 =
          ((frame 1).rotation.valᵀ *ᵥ WithLp.ofLp ((frame 0).translation - (frame 1).translation)) ⬝ᵥ
            ((frame 1).rotation.valᵀ *ᵥ
              WithLp.ofLp ((frame 0).translation - (frame 1).translation)) := by
          simp only [contactDirection, dotProduct, Fin.sum_univ_three]
          ring
      _ = contactLine frame ⬝ᵥ contactLine frame := by
          rw [dotProduct_rotT_mulVec, hd1, neg_dotProduct, dotProduct_neg, neg_neg]
  have hCS := sq_dotProduct_le ((frame 0).rotation.val *ᵥ x₀) (contactLine frame)
  have hDN₀ := hsplit _ hm₀
  have hDN₁ := hsplit _ hm₁
  rw [hN₀, he₀] at hDN₀
  rw [hN₁, he₁] at hDN₁
  have hx₀ : 0 < x₀ 2 := by
    have := Real.sqrt_nonneg (x₀ 0 ^ 2 + x₀ 1 ^ 2)
    by_contra h0
    nlinarith
  have hx₁ : 0 < x₁ 2 := by
    have := Real.sqrt_nonneg (x₁ 0 ^ 2 + x₁ 1 ^ 2)
    by_contra h0
    nlinarith
  have he0 : 0 < contactDirection frame 0 1 2 := by
    rcases hface.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      rw [← h0, mul_zero] at hDN₀
      exact (mul_pos hD hx₀).ne' hDN₀
  have hA : 0 < ((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ contactLine frame :=
    (pos_iff_pos_of_mul_pos (hDN₀ ▸ mul_pos hD hx₀)).2 he0
  have hDN₁' : contactLine frame ⬝ᵥ contactLine frame * x₁ 2 =
      ((frame 0).rotation.val *ᵥ x₀) ⬝ᵥ contactLine frame * contactDirection frame 1 0 2 := by
    linear_combination -hDN₁
  have he1 : 0 < contactDirection frame 1 0 2 :=
    (pos_iff_pos_of_mul_pos (hDN₁' ▸ mul_pos hD hx₁)).1 hA
  exact ⟨cone_transfer hμ hc₀ hS₀ hD hCS hDN₀ he0 hy₀,
    cone_transfer hμ hc₁ hS₁ hD hCS hDN₁' he1 hy₁⟩

/-- **MLS Theorem 5.7 for coplanar normals**, printed p. 233: when the two inward normals and the
connecting line lie in one plane and the first normal does not point away from the second
contact, a spatial grasp of two soft-finger contacts (eq. (5.4), p. 217, `μ > 0`, `γ > 0`) is
force-closure if and only if the line lies inside both open friction cones. The two hypotheses
are added to the printed statement; without them the "only if" fails
(`Examples.softAntipodal_onlyIf_counterexample`). Finite-force caveat (MLS p. 214). -/
theorem spatial_softFinger_isForceClosure_iff_of_coplanar {μ γ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (frame : Fin 2 → RigidTransform) (m : Fin 3 → ℝ) (hm : m ≠ 0)
    (hm₀ : m ⬝ᵥ spatialContactNormal frame 0 = 0) (hm₁ : m ⬝ᵥ spatialContactNormal frame 1 = 0)
    (hmd : m ⬝ᵥ contactLine frame = 0) (hface : 0 ≤ contactDirection frame 0 1 2) :
    (ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
      frame).toGrasp.IsForceClosure ↔
      √(contactDirection frame 0 1 0 ^ 2 + contactDirection frame 0 1 1 ^ 2) <
          μ * contactDirection frame 0 1 2 ∧
        √(contactDirection frame 1 0 0 ^ 2 + contactDirection frame 1 0 1 ^ 2) <
          μ * contactDirection frame 1 0 2 :=
  ⟨spatial_softFinger_lineInsideCones_of_isForceClosure hμ hγ frame m hm hm₀ hm₁ hmd hface,
    fun h => spatial_softFinger_isForceClosure_of_lineInsideCones hμ hγ frame h.1 h.2⟩

end RoboLean.Grasp
