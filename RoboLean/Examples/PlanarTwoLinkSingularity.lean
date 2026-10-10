import RoboLean.Kinematics.Singularity
import RoboLean.Examples.PlanarTwoLinkWorkspace

/-!
# Singular configurations of the planar two-link arm

Two different Jacobians of the planar two-revolute chain `planarTwoLink` are compared here.

* The **position Jacobian** `∂p/∂θ` of the tool-position map `p : θ ↦ (x, y)`, in the sense
  of MLS eq. (3.64), printed p. 131 (printed there for a three-link planar arm in the book's
  own coordinates; specialized here to two links with the zero configuration along `+y`).
  It is a `2 × 2` matrix, read off from the time derivative of K09
  (`hasDerivAt_planarTwoLink_translation`). Its determinant is `a b sin θ₂`, so for nonzero
  link lengths it is singular exactly at the folded and stretched configurations
  `sin θ₂ = 0`, `θ₂ ∈ πℤ`, where the tool lies on one of the two boundary circles
  `‖p‖ = a + b` or `‖p‖ = |a - b|` of the annulus. These statements about the position map go
  beyond the definition of p. 123.
* The **spatial twist Jacobian** `Jˢ(θ) ∈ ℝ^{6×2}` of MLS eq. (3.54), p. 116, whose rank
  drop is the definition of a singular configuration on MLS p. 123
  (`SerialChain.IsSingular`). Its two columns have angular part `+z` and linear parts `0`
  and `a (cos θ₁, sin θ₁, 0)`, so it has full rank `2` at every configuration as soon as
  `a ≠ 0`: in the p. 123 sense the planar arm has no singular configuration.

So the folded configurations `sin θ₂ = 0` are singular for the tool-position map but not
for the spatial twist Jacobian of p. 123.

Conventions as in `PlanarTwoLink`: Lean joint `0` is the book's joint `1`, so `q 0 = θ₁` and
`q 1 = θ₂`; twists are in the order `(v, ω)`; the zero configuration has both links along
`+y`; the link lengths `a, b` are arbitrary reals unless a hypothesis says otherwise. These
are statements about the coordinate model, not about a physical arm.
-/

noncomputable section

namespace RoboLean.Examples

/-- **Position Jacobian of the planar two-link arm** (in the sense of MLS eq. (3.64),
printed p. 131, specialized to two links). The matrix `∂p/∂θ` of the tool-position map
`θ ↦ (x, y)` of `planarTwoLink`: rows are the `x` and `y` coordinates of the tool position,
columns the joints `θ₁ = q 0` and `θ₂ = q 1`. It is derived from the time derivative of K09
(`hasDerivAt_planarTwoLink_translation`, see
`hasDerivAt_planarTwoLink_translation_eq_positionJacobian`). The zero configuration points
along `+y`, so the entries differ from the printed eq. (3.64), whose zero configuration
points along `+x`. This is not the twist Jacobian whose rank defines singularity on
p. 123. -/
def planarTwoLinkPositionJacobian (a b : ℝ) (q : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-a * Real.cos (q 0) - b * Real.cos (q 0 + q 1), -b * Real.cos (q 0 + q 1);
    -a * Real.sin (q 0) - b * Real.sin (q 0 + q 1), -b * Real.sin (q 0 + q 1)]

/-- The derivative of K09 (MLS p. 115) in matrix form: along a joint trajectory with rates
`θ̇ = q'` at time `t`, the planar part `(ẋ, ẏ)` of the tool velocity of `planarTwoLink` is
`(∂p/∂θ) θ̇` with the position Jacobian `planarTwoLinkPositionJacobian` (MLS eq. (3.64),
p. 131, specialized), and the third coordinate has derivative `0`. Conventions:
`q 0 = θ₁`, `q 1 = θ₂`, zero configuration along `+y`. -/
theorem hasDerivAt_planarTwoLink_translation_eq_positionJacobian (a b : ℝ)
    {q : ℝ → Fin 2 → ℝ} {q' : Fin 2 → ℝ} {t : ℝ}
    (hq : ∀ i, HasDerivAt (fun s => q s i) (q' i) t) :
    HasDerivAt (fun s => ((planarTwoLink a b).fk (q s)).translation)
      (vec ((planarTwoLinkPositionJacobian a b (q t)).mulVec q' 0)
        ((planarTwoLinkPositionJacobian a b (q t)).mulVec q' 1) 0) t := by
  convert hasDerivAt_planarTwoLink_translation a b hq using 2
  · simp [planarTwoLinkPositionJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [planarTwoLinkPositionJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The determinant of the position Jacobian of the planar two-link arm (MLS eq. (3.64),
p. 131, specialized) is `a b sin θ₂`, with `θ₂ = q 1`; it does not depend on `θ₁`. This is a
statement about the tool-position map, beyond the definition of p. 123. Holds for all real
`a, b`. -/
theorem det_planarTwoLinkPositionJacobian (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLinkPositionJacobian a b q).det = a * b * Real.sin (q 1) := by
  rw [planarTwoLinkPositionJacobian, Matrix.det_fin_two_of, Real.sin_add, Real.cos_add]
  linear_combination a * b * Real.sin (q 1) * Real.sin_sq_add_cos_sq (q 0)

/-- For nonzero link lengths, the position Jacobian of the planar two-link arm (MLS
eq. (3.64), p. 131, specialized) is singular exactly when `sin θ₂ = 0`, `θ₂ = q 1`: the
second link is stretched out along or folded back onto the first. A statement about the
tool-position map, beyond p. 123. -/
theorem det_planarTwoLinkPositionJacobian_eq_zero_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (q : Fin 2 → ℝ) :
    (planarTwoLinkPositionJacobian a b q).det = 0 ↔ Real.sin (q 1) = 0 := by
  rw [det_planarTwoLinkPositionJacobian, mul_eq_zero, mul_eq_zero,
    or_iff_right (not_or.2 ⟨ha, hb⟩)]

/-- For nonzero link lengths there is a nonzero joint rate `θ̇` with `(∂p/∂θ) θ̇ = 0` (the
tool position does not move to first order) exactly when `sin θ₂ = 0`, `θ₂ = q 1`. Position
Jacobian of MLS eq. (3.64), p. 131, specialized; a statement about the tool-position map,
beyond p. 123. -/
theorem exists_planarTwoLink_null_rate_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (q : Fin 2 → ℝ) :
    (∃ q' : Fin 2 → ℝ, q' ≠ 0 ∧ (planarTwoLinkPositionJacobian a b q).mulVec q' = 0) ↔
      Real.sin (q 1) = 0 := by
  rw [← det_planarTwoLinkPositionJacobian_eq_zero_iff ha hb, ← Matrix.exists_mulVec_eq_zero_iff]

/-- For nonzero link lengths, the position Jacobian of the planar two-link arm (MLS
eq. (3.64), p. 131, specialized) is singular exactly when `θ₂ = q 1` is an integer multiple
of `π`. A statement about the tool-position map, beyond p. 123. -/
theorem det_planarTwoLinkPositionJacobian_eq_zero_iff_exists_int {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) (q : Fin 2 → ℝ) :
    (planarTwoLinkPositionJacobian a b q).det = 0 ↔ ∃ k : ℤ, q 1 = k * Real.pi := by
  rw [det_planarTwoLinkPositionJacobian_eq_zero_iff ha hb, Real.sin_eq_zero_iff]
  exact exists_congr fun _ => eq_comm

/-- For positive link lengths, the position Jacobian of the planar two-link arm (MLS
eq. (3.64), p. 131, specialized) is singular exactly when the tool lies on one of the two
boundary circles of the annulus `|a - b| ≤ ‖p‖ ≤ a + b`: the outer circle (arm stretched out,
`cos θ₂ = 1`) or the inner circle (arm folded, `cos θ₂ = -1`). The tool position is MLS
eq. (3.4), p. 89, specialized (`planarTwoLinkPosition`). A statement about the tool-position
map, beyond p. 123. -/
theorem det_planarTwoLinkPositionJacobian_eq_zero_iff_norm {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (q : Fin 2 → ℝ) :
    (planarTwoLinkPositionJacobian a b q).det = 0 ↔
      ‖planarTwoLinkPosition a b q‖ = a + b ∨ ‖planarTwoLinkPosition a b q‖ = |a - b| := by
  have hsq := planarTwoLinkPosition_norm_sq a b q
  have hab : 0 < a * b := mul_pos ha hb
  have hn := norm_nonneg (planarTwoLinkPosition a b q)
  rw [det_planarTwoLinkPositionJacobian_eq_zero_iff ha.ne' hb.ne', Real.sin_eq_zero_iff_cos_eq,
    ← sq_eq_sq₀ hn (by linarith), ← sq_eq_sq₀ hn (abs_nonneg _), sq_abs, hsq]
  constructor
  · rintro (h | h) <;> rw [h]
    · left; ring
    · right; ring
  · rintro (h | h)
    · left
      have : a * b * (Real.cos (q 1) - 1) = 0 := by linear_combination h / 2
      simpa [hab.ne', sub_eq_zero] using this
    · right
      have : a * b * (Real.cos (q 1) + 1) = 0 := by linear_combination h / 2
      simpa [hab.ne', add_eq_zero_iff_eq_neg] using this

/-- **Connection to ledger C07.** For equal nonzero link lengths `a = b`, a configuration
that puts the tool at the base origin (`cos θ₂ = -1`, `planarTwoLinkPosition_eq_zero_iff`) is
a singular configuration of the position Jacobian (MLS eq. (3.64), p. 131, specialized),
since there `sin θ₂ = 0`. A statement about the tool-position map, beyond p. 123. -/
theorem det_planarTwoLinkPositionJacobian_eq_zero_of_position_eq_zero {a : ℝ} (ha : a ≠ 0)
    (q : Fin 2 → ℝ) (h : planarTwoLinkPosition a a q = 0) :
    (planarTwoLinkPositionJacobian a a q).det = 0 := by
  rw [det_planarTwoLinkPositionJacobian_eq_zero_iff ha ha, Real.sin_eq_zero_iff_cos_eq]
  exact Or.inr ((planarTwoLinkPosition_eq_zero_iff ha q).1 h)

/-- The spatial Jacobian of `planarTwoLink` (MLS eq. (3.54), p. 116; Example 3.8, p. 118) as
a whole: the columns `ξ₁ = (0, 0, 0, 0, 0, 1)` and
`ξ₂' = (l₁ cos θ₁, l₁ sin θ₁, 0, 0, 0, 1)` with `l₁ = a`, `θ₁ = q 0`. Twist order `(v, ω)`. -/
theorem planarTwoLink_spatialJacobian_eq (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).spatialJacobian q =
      ![⟨vec 0 0 0, vec 0 0 1⟩,
        ⟨vec (a * Real.cos (q 0)) (a * Real.sin (q 0)) 0, vec 0 0 1⟩] := by
  funext i
  fin_cases i
  · exact planarTwoLink_spatialJacobian_zero a b q
  · exact planarTwoLink_spatialJacobian_one a b q

/-- **MLS p. 123 for the planar two-link arm.** In the book's sense of a singular
configuration (the spatial twist Jacobian `Jˢ(θ) ∈ ℝ^{6×2}` drops rank, i.e. its two columns
become linearly dependent; `SerialChain.IsSingular`), `planarTwoLink a b` is singular at a
configuration exactly when the first link length `a` is zero; the second length `b` and the
configuration play no role. For `a = 0` the two columns coincide. In particular the folded
configurations `sin θ₂ = 0`, which are singular for the position Jacobian
(`det_planarTwoLinkPositionJacobian_eq_zero_iff`), are not singular in the p. 123 sense when
`a ≠ 0`. Twist order `(v, ω)`; `q 0 = θ₁`, `q 1 = θ₂`. -/
theorem planarTwoLink_isSingular_iff (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).IsSingular q ↔ a = 0 := by
  rw [SerialChain.isSingular_iff_not_linearIndependent _ _ (by norm_num),
    planarTwoLink_spatialJacobian_eq, LinearIndependent.pair_iff]
  constructor
  · intro h
    by_contra ha
    apply h
    intro s t hst
    have h0 := congrArg (fun ξ : Twist => ξ.linear 0) hst
    have h1 := congrArg (fun ξ : Twist => ξ.linear 1) hst
    have h2 := congrArg (fun ξ : Twist => ξ.angular 2) hst
    simp only [vec, Twist.add_linear, Twist.add_angular, Twist.smul_linear, Twist.smul_angular,
      Twist.zero_linear, Twist.zero_angular, PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, smul_eq_mul] at h0 h1 h2
    have hta : (t * a) ^ 2 = 0 := by
      linear_combination (t * a) * (Real.cos (q 0) * h0 + Real.sin (q 0) * h1) -
        (t * a) ^ 2 * Real.sin_sq_add_cos_sq (q 0)
    have ht : t = 0 := by simpa [ha] using hta
    exact ⟨by linarith, ht⟩
  · rintro rfl h
    have := h 1 (-1) (by
      apply Twist.ext <;> ext i <;> fin_cases i <;> simp [vec])
    norm_num at this

/-- **MLS p. 123 for the planar two-link arm, nonzero first link.** If the first link length
`a` is nonzero, no configuration of `planarTwoLink a b` is singular in the book's p. 123 sense
(`SerialChain.IsSingular`): the spatial twist Jacobian `Jˢ(θ) ∈ ℝ^{6×2}` (eq. (3.54), p. 116)
has full rank `2` everywhere, also at the folded configurations `sin θ₂ = 0` where the
position Jacobian drops rank. Twist order `(v, ω)`; `q 0 = θ₁`, `q 1 = θ₂`; `b` arbitrary. -/
theorem planarTwoLink_not_isSingular {a : ℝ} (ha : a ≠ 0) (b : ℝ) (q : Fin 2 → ℝ) :
    ¬ (planarTwoLink a b).IsSingular q :=
  fun h => ha ((planarTwoLink_isSingular_iff a b q).1 h)

end RoboLean.Examples
