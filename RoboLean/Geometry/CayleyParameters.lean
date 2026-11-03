import RoboLean.Geometry.Hat

/-!
# Cayley parameters of `SO(3)`

MLS Exercise 5, p. 73: for `a ∈ ℝ³` with skew-symmetric matrix `â`, the Cayley parameterization
`R_a = (I - â)⁻¹ (I + â)` is a rotation, its entries are the printed rational functions of
`a = (a₁, a₂, a₃)` with denominator `1 + ‖a‖²`, and the parameters can be recovered from the
rotation.

Conventions: `â` is `Vec3.hat a`, rows `(0, -a₃, a₂)`, `(a₃, 0, -a₁)`, `(-a₂, a₁, 0)` (MLS p. 26),
with the book's indices `1, 2, 3` read as Lean's `0, 1, 2`; `‖a‖` is the Euclidean norm. Part (c)
of the exercise prints no hypothesis; the recovery `â = (R - I)(R + I)⁻¹` needs `R + I`
invertible, which excludes the rotations by `π` (they are not of the form `R_a`), and the
hypothesis is stated.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- The Cayley parameterization `R_a = (I - â)⁻¹ (I + â)` of MLS Exercise 5, p. 73, with `â` the
hat matrix of p. 26 and Mathlib's matrix inverse. -/
def cayley (a : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - Vec3.hat a)⁻¹ * (1 + Vec3.hat a)

/-- The determinant of `I - â` is `1 + ‖a‖² > 0`, so the inverse in the Cayley parameterization
of MLS Exercise 5, p. 73, exists for every `a`. Euclidean norm. -/
theorem det_one_sub_hat (a : Vec3) : (1 - Vec3.hat a).det = 1 + ‖a‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Matrix.det_fin_three]
  simp [Vec3.hat]
  ring

/-- Supporting lemma: `1 + ‖a‖² ≠ 0`, the denominator of MLS Exercise 5(b), p. 73. -/
private theorem one_add_norm_sq_ne_zero (a : Vec3) : 1 + ‖a‖ ^ 2 ≠ 0 := by positivity

/-- Supporting lemma: `det(I - â)` is a unit, so `(I - â)⁻¹` is a two-sided inverse (MLS
Exercise 5, p. 73). -/
private theorem isUnit_det_one_sub_hat (a : Vec3) : IsUnit (1 - Vec3.hat a).det := by
  rw [det_one_sub_hat]; exact (one_add_norm_sq_ne_zero a).isUnit

/-- MLS Exercise 5(b), p. 73: the entries of the Cayley parameterization,
`R_a = (1 / (1 + ‖a‖²)) [[1 + a₁² - a₂² - a₃², 2(a₁a₂ - a₃), 2(a₁a₃ + a₂)],
[2(a₁a₂ + a₃), 1 - a₁² + a₂² - a₃², 2(a₂a₃ - a₁)], [2(a₁a₃ - a₂), 2(a₂a₃ + a₁),
1 - a₁² - a₂² + a₃²]]`, with indices `1, 2, 3` read as `0, 1, 2`. -/
theorem cayley_eq (a : Vec3) :
    cayley a = (1 / (1 + ‖a‖ ^ 2)) •
      !![1 + a 0 ^ 2 - a 1 ^ 2 - a 2 ^ 2, 2 * (a 0 * a 1 - a 2), 2 * (a 0 * a 2 + a 1);
         2 * (a 0 * a 1 + a 2), 1 - a 0 ^ 2 + a 1 ^ 2 - a 2 ^ 2, 2 * (a 1 * a 2 - a 0);
         2 * (a 0 * a 2 - a 1), 2 * (a 1 * a 2 + a 0), 1 - a 0 ^ 2 - a 1 ^ 2 + a 2 ^ 2] := by
  set N : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1 + a 0 ^ 2 - a 1 ^ 2 - a 2 ^ 2, 2 * (a 0 * a 1 - a 2), 2 * (a 0 * a 2 + a 1);
       2 * (a 0 * a 1 + a 2), 1 - a 0 ^ 2 + a 1 ^ 2 - a 2 ^ 2, 2 * (a 1 * a 2 - a 0);
       2 * (a 0 * a 2 - a 1), 2 * (a 1 * a 2 + a 0), 1 - a 0 ^ 2 - a 1 ^ 2 + a 2 ^ 2]
  have hd : 1 + ‖a‖ ^ 2 = 1 + a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; ring
  have hd0 : 1 + a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 ≠ 0 := by positivity
  have key : (1 - Vec3.hat a) * ((1 / (1 + ‖a‖ ^ 2)) • N) = 1 + Vec3.hat a := by
    rw [hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [N, Vec3.hat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> field_simp <;> ring
  rw [cayley, ← key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_one_sub_hat a),
    Matrix.one_mul]

/-- MLS Exercise 5(a), p. 73: the Cayley parameterization `R_a = (I - â)⁻¹ (I + â)` lies in
`SO(3)` for every `a ∈ ℝ³`. -/
theorem cayley_mem_specialOrthogonalGroup (a : Vec3) :
    cayley a ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hd : 1 + ‖a‖ ^ 2 = 1 + a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; ring
  have hd0 : 1 + a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 ≠ 0 := by positivity
  rw [cayley_eq, hd]
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring
  · rw [Matrix.det_smul, Matrix.det_fin_three]
    simp
    field_simp
    ring

/-- The Cayley parameterization of MLS Exercise 5, p. 73, as a map `ℝ³ → SO(3)`. -/
def cayleyRotation (a : Vec3) : Rotation :=
  ⟨cayley a, cayley_mem_specialOrthogonalGroup a⟩

/-- The matrix `R_a + I` is invertible for every Cayley rotation of MLS Exercise 5, p. 73: the
Cayley parameterization never reaches a rotation with `det(R + I) = 0` (a rotation by `π`). -/
theorem det_cayley_add_one_ne_zero (a : Vec3) : (cayley a + 1).det ≠ 0 := by
  have hu := isUnit_det_one_sub_hat a
  have h : cayley a + 1 = (1 - Vec3.hat a)⁻¹ * ((2 : ℝ) • 1) := by
    have e : (1 - Vec3.hat a)⁻¹ * ((2 : ℝ) • 1) = (1 - Vec3.hat a)⁻¹ * (1 + Vec3.hat a) +
        (1 - Vec3.hat a)⁻¹ * (1 - Vec3.hat a) := by
      rw [← Matrix.mul_add]; congr 1; module
    rw [e, Matrix.nonsing_inv_mul _ hu, cayley]
  rw [h, Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Matrix.det_nonsing_inv]
  have := hu.ne_zero
  simp [Ring.inverse_eq_inv', this]

/-- The Cayley parameters of a matrix `R`, `a = ((R - I)(R + I)⁻¹)^∨`, the answer to MLS
Exercise 5(c), p. 73; the vee map reads the skew entries as on p. 26. -/
def cayleyParameters (R : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  Vec3.vee ((R - 1) * (R + 1)⁻¹)

/-- MLS Exercise 5(c), p. 73: a rotation `R ∈ SO(3)` with `R + I` invertible is the Cayley
rotation of its Cayley parameters, `R = (I - â)⁻¹ (I + â)` for `â = (R - I)(R + I)⁻¹`. The
invertibility of `R + I` is a hypothesis the book does not print; without it the statement fails
(`det_cayley_add_one_ne_zero`). -/
theorem cayley_cayleyParameters (R : Rotation) (hR : (R.val + 1).det ≠ 0) :
    cayley (cayleyParameters R.val) = R.val := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := R.val
  set B : Matrix (Fin 3) (Fin 3) ℝ := M + 1
  have hB : IsUnit B.det := hR.isUnit
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hB
  have hBB' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hB
  have hMt : Mᵀ * M = 1 := R.transpose_mul
  have h1 : M * B = B * M := by simp [B, Matrix.mul_add, Matrix.add_mul]
  have hcomm : B⁻¹ * M = M * B⁻¹ := by
    calc B⁻¹ * M = B⁻¹ * M * (B * B⁻¹) := by rw [hBB, Matrix.mul_one]
      _ = B⁻¹ * (M * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * M) * B⁻¹ := by rw [h1]
      _ = (B⁻¹ * B) * M * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M * B⁻¹ := by rw [hBB', Matrix.one_mul]
  set S : Matrix (Fin 3) (Fin 3) ℝ := (M - 1) * B⁻¹
  have hskew : Sᵀ = -S := by
    set C : Matrix (Fin 3) (Fin 3) ℝ := Bᵀ
    have hC : IsUnit C.det := by rw [Matrix.det_transpose]; exact hB
    have hCC' : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
    have hid : (Mᵀ - 1) * B = -(C * (M - 1)) := by
      simp only [C, B, Matrix.transpose_add, Matrix.transpose_one, Matrix.sub_mul,
        Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, hMt, Matrix.mul_one, Matrix.one_mul]
      abel
    have hSt : Sᵀ = C⁻¹ * (Mᵀ - 1) := by
      simp only [S, C, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
        Matrix.transpose_one]
    rw [hSt]
    calc C⁻¹ * (Mᵀ - 1) = C⁻¹ * ((Mᵀ - 1) * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = -((C⁻¹ * C) * (M - 1) * B⁻¹) := by
          rw [hid, Matrix.mul_neg, Matrix.neg_mul]; simp only [Matrix.mul_assoc]
      _ = -S := by rw [hCC', Matrix.one_mul]
  have hhat : Vec3.hat (cayleyParameters M) = S := Vec3.hat_vee S hskew
  have h2 : B - (M - 1) = (2 : ℝ) • 1 := by simp only [B]; module
  have h1S : 1 - S = (2 : ℝ) • B⁻¹ := by
    calc 1 - S = B * B⁻¹ - (M - 1) * B⁻¹ := by rw [hBB]
      _ = (B - (M - 1)) * B⁻¹ := (Matrix.sub_mul _ _ _).symm
      _ = (2 : ℝ) • B⁻¹ := by rw [h2, Matrix.smul_mul, Matrix.one_mul]
  have h1S' : 1 + S = (2 : ℝ) • (M * B⁻¹) := by
    calc 1 + S = B * B⁻¹ + (M - 1) * B⁻¹ := by rw [hBB]
      _ = (B + (M - 1)) * B⁻¹ := (Matrix.add_mul _ _ _).symm
      _ = ((2 : ℝ) • M) * B⁻¹ := by congr 1; simp only [B]; module
      _ = (2 : ℝ) • (M * B⁻¹) := by rw [Matrix.smul_mul]
  have hinv : (1 - S)⁻¹ = (1 / 2 : ℝ) • B := by
    apply Matrix.inv_eq_right_inv
    rw [h1S, Matrix.smul_mul, Matrix.mul_smul, hBB', smul_smul]
    norm_num
  rw [cayley, hhat, hinv, h1S', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc,
    ← h1, Matrix.mul_assoc, hBB, Matrix.mul_one]
  norm_num

/-- MLS Exercise 5(c), p. 73: the Cayley parameters of the Cayley rotation `R_a` are `a`, so the
parameterization is injective on `ℝ³`. -/
theorem cayleyParameters_cayley (a : Vec3) : cayleyParameters (cayley a) = a := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := 1 - Vec3.hat a
  set P : Matrix (Fin 3) (Fin 3) ℝ := 1 + Vec3.hat a
  have hu := isUnit_det_one_sub_hat a
  have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hu
  have hPA : A⁻¹ * P * A = P := by
    have : P * A = A * P := by
      simp only [A, P, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul]
      abel
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hinv : (cayley a + 1)⁻¹ = (1 / 2 : ℝ) • A := by
    apply Matrix.inv_eq_right_inv
    rw [cayley, Matrix.mul_smul, Matrix.add_mul, hPA, Matrix.one_mul]
    simp only [A, P]
    module
  unfold cayleyParameters
  rw [hinv, Matrix.mul_smul, Matrix.sub_mul, cayley, hPA, Matrix.one_mul]
  have : (1 / 2 : ℝ) • (P - A) = Vec3.hat a := by simp only [A, P]; module
  rw [this, Vec3.vee_hat]

end RoboLean
