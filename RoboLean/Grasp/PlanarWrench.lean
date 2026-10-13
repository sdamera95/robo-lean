import RoboLean.Grasp.GraspMap

/-!
# The 2-D cross product, `n^⊥`, planar contact frames and planar point-contact grasp maps

MLS Chapter 5, printed p. 232 (§4.2, Theorem 5.6 and the inequalities A–D): "Given a unit vector
`n`, define `n^⊥` to be the unit vector perpendicular to `n` which satisfies `n ⊗ n^⊥ = +1`,
where `⊗` is the 2-D cross product: `a ⊗ b = det[a b]`, `a, b ∈ ℝ²`." With the planar rule of
Example 5.3 (printed p. 222) these give the wrenches of planar point contacts.

Conventions.
* `cross2 a b = a_x b_y - a_y b_x = det[a b]`, the matrix with columns `a`, `b`
  (`cross2_eq_det`). Lean `a 0, a 1` are `a_x, a_y`.
* `perp2 n = (-n_y, n_x)`, the counterclockwise quarter turn; for a unit `n` it is the unique
  vector with `n · m = 0` and `n ⊗ m = 1` (`perp2_unique`), the printed `n^⊥`.
* A planar contact frame is `(R, p)` with `R ∈ SO(2)` (Mathlib's
  `specialOrthogonalGroup (Fin 2) ℝ`), as in `ContactGrasp.planar`. Its contact `x`-axis is
  `contactTangent R = R e_x` (first column) and its contact `y`-axis, the inward normal of the
  planar convention of p. 222, is `contactNormal R = R e_y` (second column). Since `det R = 1`,
  the printed `n^⊥` of the inward normal is `-t` (`perp2_contactNormal`).
* `planarWrench p F = (F_x, F_y, p ⊗ F)` is the planar wrench `(f_x, f_y, τ)` (p. 222) of a force
  `F` applied at the point `p`, both in object coordinates.

The frame is data: nothing checks that `contactNormal R` is an inward normal of an object.
-/

noncomputable section

open Matrix

namespace RoboLean.Grasp

/-- The 2-D cross product of MLS printed p. 232, `a ⊗ b = det[a b] = a_x b_y - a_y b_x` for
`a, b ∈ ℝ²` (Lean `a 0, a 1` are `a_x, a_y`). -/
def cross2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

/-- MLS printed p. 232: `a ⊗ b = det[a b]`, the determinant of the `2 × 2` matrix with columns
`a` and `b` (the transpose of the matrix with rows `a`, `b`). -/
theorem cross2_eq_det (a b : Fin 2 → ℝ) : cross2 a b = (Matrix.of ![a, b])ᵀ.det := by
  rw [Matrix.det_fin_two]
  simp [cross2, mul_comm]

/-- The 2-D cross product of MLS printed p. 232 is antisymmetric: `a ⊗ b = -(b ⊗ a)`. -/
theorem cross2_comm (a b : Fin 2 → ℝ) : cross2 a b = -cross2 b a := by
  simp only [cross2]
  ring

/-- `a ⊗ a = 0` for the 2-D cross product of MLS printed p. 232. -/
@[simp] theorem cross2_self (a : Fin 2 → ℝ) : cross2 a a = 0 := by
  simp only [cross2]
  ring

/-- The 2-D cross product of MLS printed p. 232 is additive in its first argument. -/
theorem cross2_add_left (a b c : Fin 2 → ℝ) : cross2 (a + b) c = cross2 a c + cross2 b c := by
  simp only [cross2, Pi.add_apply]
  ring

/-- The 2-D cross product of MLS printed p. 232 is additive in its second argument. -/
theorem cross2_add_right (a b c : Fin 2 → ℝ) : cross2 a (b + c) = cross2 a b + cross2 a c := by
  simp only [cross2, Pi.add_apply]
  ring

/-- The 2-D cross product of MLS printed p. 232 is subtractive in its first argument. -/
theorem cross2_sub_left (a b c : Fin 2 → ℝ) : cross2 (a - b) c = cross2 a c - cross2 b c := by
  simp only [cross2, Pi.sub_apply]
  ring

/-- The 2-D cross product of MLS printed p. 232 is subtractive in its second argument. -/
theorem cross2_sub_right (a b c : Fin 2 → ℝ) : cross2 a (b - c) = cross2 a b - cross2 a c := by
  simp only [cross2, Pi.sub_apply]
  ring

/-- The 2-D cross product of MLS printed p. 232 is homogeneous in its first argument. -/
theorem cross2_smul_left (s : ℝ) (a b : Fin 2 → ℝ) : cross2 (s • a) b = s * cross2 a b := by
  simp only [cross2, Pi.smul_apply, smul_eq_mul]
  ring

/-- The 2-D cross product of MLS printed p. 232 is homogeneous in its second argument. -/
theorem cross2_smul_right (s : ℝ) (a b : Fin 2 → ℝ) : cross2 a (s • b) = s * cross2 a b := by
  simp only [cross2, Pi.smul_apply, smul_eq_mul]
  ring

/-- Negating the first argument negates the 2-D cross product of MLS printed p. 232. -/
theorem cross2_neg_left (a b : Fin 2 → ℝ) : cross2 (-a) b = -cross2 a b := by
  simp only [cross2, Pi.neg_apply]
  ring

/-- Negating the second argument negates the 2-D cross product of MLS printed p. 232. -/
theorem cross2_neg_right (a b : Fin 2 → ℝ) : cross2 a (-b) = -cross2 a b := by
  simp only [cross2, Pi.neg_apply]
  ring

/-- The vector `n^⊥ = (-n_y, n_x)` of MLS printed p. 232, the counterclockwise quarter turn of
`n`. For a unit vector `n` it is the printed "unit vector perpendicular to `n` which satisfies
`n ⊗ n^⊥ = +1`" (`perp2_unique`); the definition applies to every `n ∈ ℝ²`. -/
def perp2 (n : Fin 2 → ℝ) : Fin 2 → ℝ := ![-n 1, n 0]

/-- `n^⊥` (MLS printed p. 232) is perpendicular to `n`. -/
theorem dotProduct_perp2 (n : Fin 2 → ℝ) : n ⬝ᵥ perp2 n = 0 := by
  simp only [perp2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- `n ⊗ n^⊥ = n_x² + n_y²` (MLS printed p. 232); it is `+1` for a unit vector `n`. -/
theorem cross2_perp2 (n : Fin 2 → ℝ) : cross2 n (perp2 n) = n 0 ^ 2 + n 1 ^ 2 := by
  simp only [cross2, perp2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- `n^⊥` (MLS printed p. 232) has the length of `n`: `(n^⊥)_x² + (n^⊥)_y² = n_x² + n_y²`. -/
theorem perp2_sq_add_sq (n : Fin 2 → ℝ) : perp2 n 0 ^ 2 + perp2 n 1 ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
  simp only [perp2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The printed definition of `n^⊥`, MLS printed p. 232**: for a unit vector `n`, a vector `m`
perpendicular to `n` with `n ⊗ m = +1` is `perp2 n`. With `perp2_sq_add_sq` and
`cross2_perp2`, `perp2 n` is the unique unit vector of the printed definition. -/
theorem perp2_unique {n m : Fin 2 → ℝ} (hn : n 0 ^ 2 + n 1 ^ 2 = 1) (hdot : n ⬝ᵥ m = 0)
    (hcross : cross2 n m = 1) : m = perp2 n := by
  simp only [dotProduct, Fin.sum_univ_two] at hdot
  simp only [cross2] at hcross
  funext i
  fin_cases i
  · simp only [perp2, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linear_combination n 0 * hdot - n 1 * hcross - m 0 * hn
  · simp only [perp2, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination n 1 * hdot + n 0 * hcross - m 1 * hn

/-- The contact `x`-axis `t = R e_x` (first column of `R`) of a planar contact frame `R ∈ SO(2)`,
in object coordinates (MLS Example 5.3, printed p. 222). -/
def contactTangent (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) : Fin 2 → ℝ :=
  fun i => (R : Matrix (Fin 2) (Fin 2) ℝ) i 0

/-- The contact `y`-axis `n = R e_y` (second column of `R`) of a planar contact frame
`R ∈ SO(2)`, in object coordinates: the inward normal in the planar convention of MLS
Example 5.3, printed p. 222 (the `n_i` of p. 232 for contact frames built this way). -/
def contactNormal (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) : Fin 2 → ℝ :=
  fun i => (R : Matrix (Fin 2) (Fin 2) ℝ) i 1

/-- Entries of a planar rotation (supporting lemma for MLS printed pp. 222 and 232):
`R = [[a, -c], [c, a]]` with `a² + c² = 1` (Mathlib
`Matrix.mem_specialOrthogonalGroup_fin_two_iff`). -/
theorem so2_entries (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    (R : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
      (R : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ∧
      (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.2
  refine ⟨h1.symm, h2, ?_⟩
  rw [h2] at h3
  linarith

/-- The inward normal of a planar contact frame is a unit vector (MLS printed pp. 222, 232). -/
theorem contactNormal_sq_add_sq (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    contactNormal R 0 ^ 2 + contactNormal R 1 ^ 2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := so2_entries R
  simp only [contactNormal, h1, h2]
  linarith

/-- **`n^⊥ = -t`** for a planar contact frame `R ∈ SO(2)` (MLS printed p. 232, with the frame
convention of p. 222): the printed `n^⊥` of the inward normal `n = R e_y` is minus the contact
`x`-axis `t = R e_x`. -/
theorem perp2_contactNormal (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    perp2 (contactNormal R) = -contactTangent R := by
  obtain ⟨h1, h2, -⟩ := so2_entries R
  funext i
  fin_cases i <;> simp [perp2, contactNormal, contactTangent, h1, h2]

/-- `t ⊗ n = det R = 1` for a planar contact frame `R ∈ SO(2)` (MLS printed pp. 222, 232). -/
theorem cross2_contactTangent_contactNormal (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    cross2 (contactTangent R) (contactNormal R) = 1 := by
  obtain ⟨h1, h2, h3⟩ := so2_entries R
  simp only [cross2, contactTangent, contactNormal, h1, h2]
  linarith

/-- `n · d = (Rᵀ d)_y`: the normal coordinate of `d` in the contact frame `R` (MLS printed
pp. 222, 232). -/
theorem contactNormal_dotProduct (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) : contactNormal R ⬝ᵥ d = ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 1 := by
  simp [contactNormal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `t · d = (Rᵀ d)_x`: the tangential coordinate of `d` in the contact frame `R` (MLS printed
pp. 222, 232). -/
theorem contactTangent_dotProduct (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) : contactTangent R ⬝ᵥ d = ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 0 := by
  simp [contactTangent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `R Rᵀ d = d` for a planar rotation (supporting lemma for MLS printed pp. 222, 232). -/
theorem so2_mulVec_transpose_mulVec (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) :
    (R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) = d := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- `Rᵀ R f = f` for a planar rotation (supporting lemma for MLS printed pp. 222, 232). -/
theorem so2_transpose_mulVec_mulVec (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (f : Fin 2 → ℝ) :
    (R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ((R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f) = f := by
  have h := (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- The planar wrench `(f_x, f_y, τ)` of a force `F` applied at the point `p`, both in object
coordinates: `τ = p ⊗ F = p_x F_y - p_y F_x`, the moment of MLS Example 5.3, printed p. 222
(`Planar.wrenchTransform_mulVec` with zero contact moment), written with the 2-D cross product of
p. 232. -/
def planarWrench (p F : Fin 2 → ℝ) : Fin 3 → ℝ := ![F 0, F 1, cross2 p F]

/-- The planar wrench of MLS printed p. 222 is additive in the force. -/
theorem planarWrench_add (p F F' : Fin 2 → ℝ) :
    planarWrench p (F + F') = planarWrench p F + planarWrench p F' := by
  funext i
  fin_cases i <;> simp [planarWrench, cross2_add_right]

/-- The planar wrench of MLS printed p. 222 is homogeneous in the force. -/
theorem planarWrench_smul (p F : Fin 2 → ℝ) (s : ℝ) :
    planarWrench p (s • F) = s • planarWrench p F := by
  funext i
  fin_cases i <;> simp [planarWrench, cross2_smul_right]

/-- The planar wrench of MLS printed p. 222 of a negated force is negated. -/
theorem planarWrench_neg (p F : Fin 2 → ℝ) : planarWrench p (-F) = -planarWrench p F := by
  funext i
  fin_cases i <;> simp [planarWrench, cross2_neg_right]

/-- The planar wrench of MLS printed p. 222 is additive in the point of application:
`(F, (p + q) ⊗ F) = (F, p ⊗ F) + (0, 0, q ⊗ F)`. -/
theorem planarWrench_add_point (p q F : Fin 2 → ℝ) :
    planarWrench (p + q) F = planarWrench p F + ![0, 0, cross2 q F] := by
  funext i
  fin_cases i <;> simp [planarWrench, cross2_add_left]

/-- **The contact map of a planar point contact with friction**, MLS Example 5.3, printed p. 222:
contact `i` with frame `(Rᵢ, pᵢ)` applies to the object the planar wrench of the force
`Rᵢ fᵢ` (the contact force rotated into object coordinates) at the point `pᵢ`. -/
theorem planar_planarPointContact_contactMap {ι : Type*} [Fintype ι] (μ : ℝ) (hμ : 0 < μ)
    (R : ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : ι → Fin 2 → ℝ) (i : ι)
    (f : Fin 2 → ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).contactMap i f =
      planarWrench (p i) ((R i : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f) := by
  rw [ContactGrasp.planar_contactMap_apply, ContactModel.planarPointContact_wrench,
    Planar.wrenchTransform_mulVec]
  funext j
  fin_cases j <;> simp [planarWrench, cross2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The grasp map of planar point contacts with friction**, MLS eq. (5.6) with Example 5.3,
printed pp. 219, 222: `G f_c = ∑ᵢ (Rᵢ fᵢ, pᵢ ⊗ Rᵢ fᵢ)`, the sum of the planar wrenches of the
contact forces rotated into object coordinates. -/
theorem planar_planarPointContact_graspMap {ι : Type*} [Fintype ι] (μ : ℝ) (hμ : 0 < μ)
    (R : ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : ι → Fin 2 → ℝ)
    (f : ι → Fin 2 → ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).graspMap f =
      ∑ i, planarWrench (p i) ((R i : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f i) := by
  rw [ContactGrasp.graspMap_apply]
  exact Finset.sum_congr rfl fun i _ => planar_planarPointContact_contactMap μ hμ R p i (f i)

end RoboLean.Grasp
