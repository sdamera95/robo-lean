import RoboLean.Geometry.TwistExpClosedForm

/-!
# Left invariant constraints on `SE(3)` and Proposition A.7 as printed

MLS Appendix A, Examples A.24–A.25 and Proposition A.7, printed pp. 428–429. A holonomic constraint
on `SE(3)` is `f(g) = 0` with `f : SE(3) → ℝ` smooth; differentiating gives `df(g)ġ = 0`, translated
to the identity as `⟨L_g^*df(g), ξ̂⟩ = 0` with `ξ̂ = g⁻¹ġ` (p. 428). "A constraint is said to be left
invariant if `L_g^*df(g) = df(e)`" (p. 429). Proposition A.7 (Loncaric): "a constraint `f(g) = 0` is
left (or right) invariant if and only if `f⁻¹(0)` is a subgroup of `SE(3)`" (p. 429, no proof
printed).

Reading. Group elements are the library's rigid transforms and `exp` is the twist exponential, so
the curve `t ↦ g exp(tξ̂)` has velocity `T_eL_g ξ̂` at `t = 0` and `(L_g^*df(g))(ξ) =
d/dt f(g exp(tξ̂))|_{t=0}` (`leftPulledDifferential`, defined with Mathlib's `deriv`, which is this
derivative for every smooth `f`, in particular for the polynomial functions used below). Left
invariance is the printed equality of covectors for every `g` (`IsLeftInvariantConstraint`).

Statements. With these definitions Proposition A.7 fails in both directions: the zero set of
`f(g) = ‖p‖²` is the subgroup of rotations about the origin while `f` is not left invariant (at
`g = (e₁, I)` and `ξ = (e₁, 0)` the pulled-back differential is `2`, at the identity `0`), and a
nonzero constant is left invariant with an empty zero set. The first function has the critical value
`0`, and the second is not a constraint with solutions, so the printed statement needs hypotheses it
does not state; the intended notion of left invariance is presumably that of the constraint's
subspace (the span of the `L_g^*df_i(g)`), see the ledger note.
-/

noncomputable section

namespace RoboLean

namespace LieGroup

/-- The unit vector `e₁`. -/
private def e1 : Vec3 := WithLp.toLp 2 ![1, 0, 0]

private theorem norm_e1 : ‖e1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [e1, Fin.sum_univ_three]

/-- **The differential of a constraint pulled back to the identity**, `(L_g^*df(g))(ξ) =
d/dt f(g exp(tξ̂))|_{t=0}` (MLS Example A.24, p. 428, with `ξ̂ = g⁻¹ġ`), for `f : SE(3) → ℝ`, a rigid
transform `g` and a twist `ξ = (v, ω)`. -/
def leftPulledDifferential (f : RigidTransform → ℝ) (g : RigidTransform) (ξ : Twist) : ℝ :=
  deriv (fun t : ℝ => f (g * Twist.exp ξ t)) 0

/-- **A left invariant constraint** (MLS Example A.25, p. 429): `L_g^*df(g) = df(e)` for every
`g ∈ SE(3)`, as covectors on twists. -/
def IsLeftInvariantConstraint (f : RigidTransform → ℝ) : Prop :=
  ∀ (g : RigidTransform) (ξ : Twist), leftPulledDifferential f g ξ = leftPulledDifferential f 1 ξ

/-- The zero set `f⁻¹(0)` of a constraint is a subgroup of `SE(3)` (MLS Proposition A.7, p. 429). -/
def IsSubgroupZeroSet (f : RigidTransform → ℝ) : Prop :=
  ∃ H : Subgroup RigidTransform, (H : Set RigidTransform) = {g | f g = 0}

/-- MLS Proposition A.7, p. 429: the zero set of `f(g) = ‖p‖²` is a subgroup of `SE(3)` (the
rotations about the origin). -/
theorem isSubgroupZeroSet_translation_sq :
    IsSubgroupZeroSet fun g : RigidTransform => ‖g.translation‖ ^ 2 := by
  refine ⟨{ carrier := {g | g.translation = 0}
            mul_mem' := ?_
            one_mem' := RigidTransform.one_translation
            inv_mem' := ?_ }, ?_⟩
  · intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [RigidTransform.mul_translation, ha, hb]
    simp
  · intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [RigidTransform.inv_translation, ha]
    simp
  · ext g
    simp

/-- MLS Example A.25, p. 429: `f(g) = ‖p‖²` is not a left invariant constraint. -/
theorem not_isLeftInvariantConstraint_translation_sq :
    ¬ IsLeftInvariantConstraint fun g : RigidTransform => ‖g.translation‖ ^ 2 := by
  intro h
  have hg := h ⟨1, e1⟩ ⟨e1, 0⟩
  unfold leftPulledDifferential at hg
  have h1 : (fun t : ℝ => ‖((⟨1, e1⟩ : RigidTransform) * Twist.exp ⟨e1, 0⟩ t).translation‖ ^ 2) =
      fun t => (t + 1) ^ 2 := by
    funext t
    rw [Twist.exp_pure_translation, RigidTransform.mul_translation, Rotation.act_one,
      show t • e1 + e1 = (t + 1) • e1 by rw [add_smul, one_smul], norm_smul, norm_e1, mul_one,
      Real.norm_eq_abs, sq_abs]
  have h2 : (fun t : ℝ => ‖((1 : RigidTransform) * Twist.exp ⟨e1, 0⟩ t).translation‖ ^ 2) =
      fun t => t ^ 2 := by
    funext t
    rw [one_mul, Twist.exp_pure_translation, norm_smul, norm_e1, mul_one, Real.norm_eq_abs, sq_abs]
  rw [h1, h2] at hg
  have d1 : deriv (fun t : ℝ => (t + 1) ^ 2) 0 = 2 := by
    have := ((hasDerivAt_id (0 : ℝ)).add_const 1).pow 2
    rw [show (fun t : ℝ => (t + 1) ^ 2) = (fun x => id x + 1) ^ 2 from rfl, this.deriv]
    norm_num
  have d2 : deriv (fun t : ℝ => t ^ 2) 0 = 0 := by
    have := (hasDerivAt_id (0 : ℝ)).pow 2
    rw [show (fun t : ℝ => t ^ 2) = id ^ 2 from rfl, this.deriv]
    norm_num
  rw [d1, d2] at hg
  norm_num at hg

/-- MLS Example A.25, p. 429: a constant function is a left invariant constraint (its differential
vanishes). -/
theorem isLeftInvariantConstraint_const (c : ℝ) :
    IsLeftInvariantConstraint fun _ : RigidTransform => c := by
  intro g ξ
  simp [leftPulledDifferential]

/-- MLS Proposition A.7, p. 429: the zero set of a nonzero constant is empty, not a subgroup. -/
theorem not_isSubgroupZeroSet_const (c : ℝ) (hc : c ≠ 0) :
    ¬ IsSubgroupZeroSet fun _ : RigidTransform => c := by
  rintro ⟨H, hH⟩
  have h1 : (1 : RigidTransform) ∈ (H : Set RigidTransform) := H.one_mem
  rw [hH] at h1
  exact hc h1

/-- **MLS Proposition A.7, p. 429, as printed, fails in both directions** with the printed definition
of left invariance: some constraint has a subgroup as zero set without being left invariant, and
some left invariant constraint has a zero set that is not a subgroup. -/
theorem propositionA7_counterexamples :
    (∃ f : RigidTransform → ℝ, IsSubgroupZeroSet f ∧ ¬ IsLeftInvariantConstraint f) ∧
      ∃ f : RigidTransform → ℝ, IsLeftInvariantConstraint f ∧ ¬ IsSubgroupZeroSet f :=
  ⟨⟨_, isSubgroupZeroSet_translation_sq, not_isLeftInvariantConstraint_translation_sq⟩,
    ⟨_, isLeftInvariantConstraint_const 1, not_isSubgroupZeroSet_const 1 one_ne_zero⟩⟩

end LieGroup

end RoboLean
