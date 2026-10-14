import RoboLean.Grasp.FrictionCone
import RoboLean.Geometry.WrenchWork
import RoboLean.Geometry.ElementaryRotations
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Contact models: wrench bases, friction cones and the planar wrench rule

MLS Chapter 5, §2.1, printed pp. 214–219, and Example 5.3, printed p. 222.

Frames (p. 214–215). The object frame `O` is at the object's center of mass; the contact frame
`Cᵢ` sits at the contact point with its `z`-axis along the *inward* surface normal (p. 214–215;
in the planar Example 5.3 the `y`-axis is the inward normal, p. 222); `g_{ocᵢ} = (p_{ocᵢ}, R_{ocᵢ})`
takes contact coordinates to object coordinates. The contact location is fixed on the object
(p. 214). A contact applies a wrench `F_{cᵢ}` at the origin of `Cᵢ`, written in `Cᵢ`. MLS's
section 6 (p. 246, footnote 2) uses the outward normal instead; that convention is not used
here. The frame is data: no type enforces that the `z`-axis is the inward normal.

A contact model (p. 218) is a wrench basis `B_c ∈ ℝ^{p×m}` and a friction cone `FC_c ⊂ ℝ^m`;
the contact wrench is `F_c = B_c f_c` with `f_c ∈ FC_c` (eq. (5.5)). `ContactModel W m` stores the
`m` columns of `B_c` as elements of the wrench space `W` (`Wrench` for spatial contacts, `p = 6`;
`Fin 3 → ℝ` with coordinates `(f_x, f_y, τ)` for planar contacts, `p = 3`, p. 222) and the
friction cone of `FrictionCone`. Wrench order is force then moment, as in the library's
`Wrench` (MLS p. 61).

The planar rule of p. 222, `[f_o; τ_o] = [[R, 0], [[-p_y, p_x] R, 1]] [f_c; τ_c]`, is
`Planar.wrenchTransform`; `Planar.transform_embedWrench` proves it is the spatial rule (2.66)
(`Wrench.transform`) for a frame change about the `z`-axis acting on wrenches with force in the
`xy`-plane and moment along `z`.

Rigid bodies, rigid links and accurate models are standing assumptions (MLS p. 214); nothing
here claims that a physical contact behaves as modeled.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- A contact model, MLS printed p. 218: a wrench basis `B_c ∈ ℝ^{p×m}`, stored as its `m` columns
in the wrench space `W` (the wrenches of unit contact force coefficients, written in the contact
frame), and a friction cone `FC_c ⊂ ℝ^m` satisfying the two properties required on p. 218
(`FrictionCone`). The contact wrench is `F_c = B_c f_c`, `f_c ∈ FC_c` (eq. (5.5)). -/
structure ContactModel (W : Type*) [AddCommGroup W] [Module ℝ W] (m : ℕ) where
  /-- The columns of the wrench basis `B_c`, MLS printed p. 218. -/
  basis : Fin m → W
  /-- The friction cone `FC_c`, MLS printed p. 218. -/
  cone : FrictionCone (Fin m → ℝ)

namespace ContactModel

variable {W : Type*} [AddCommGroup W] [Module ℝ W] {m : ℕ}

/-- The contact wrench `F_c = B_c f_c` of contact force coefficients `f_c`, MLS eq. (5.5),
printed p. 218, written in the contact frame; a real linear map `ℝ^m → W`. -/
def wrench (c : ContactModel W m) : (Fin m → ℝ) →ₗ[ℝ] W :=
  Fintype.linearCombination ℝ c.basis

/-- `B_c f_c = ∑ⱼ f_{c,j} Bⱼ`, the column form of MLS eq. (5.5), printed p. 218. -/
theorem wrench_apply (c : ContactModel W m) (f : Fin m → ℝ) :
    c.wrench f = ∑ j, f j • c.basis j :=
  Fintype.linearCombination_apply ℝ c.basis f

/-- A unit coefficient selects a column of the wrench basis (MLS eq. (5.5), printed p. 218). -/
theorem wrench_single (c : ContactModel W m) (j : Fin m) :
    c.wrench (Pi.single j 1) = c.basis j := by
  rw [wrench_apply]
  simp [Pi.single_apply]

/-- The set of wrenches a contact can apply, `{B_c f_c : f_c ∈ FC_c}`, MLS eq. (5.5), printed
p. 218: the image of the friction cone under the wrench basis (written in the contact frame). -/
def wrenchCone (c : ContactModel W m) : ConvexCone ℝ W :=
  c.cone.toConvexCone.map c.wrench

/-- A wrench can be applied by the contact exactly when it is `B_c f_c` for some `f_c ∈ FC_c`
(MLS eq. (5.5), printed p. 218). -/
theorem mem_wrenchCone (c : ContactModel W m) {F : W} :
    F ∈ c.wrenchCone ↔ ∃ f ∈ c.cone, c.wrench f = F :=
  ConvexCone.mem_map

/-! ### The spatial contact models of Table 5.2 -/

/-- The frictionless point contact, MLS eq. (5.1), printed p. 215, and Table 5.2, p. 219: wrench
basis `(0, 0, 1, 0, 0, 0)ᵀ` (unit force along the contact `z`-axis, the inward normal) and
friction cone `f₁ ≥ 0`. -/
def frictionless : ContactModel Wrench 1 where
  basis := ![⟨Rotation.zAxis, 0⟩]
  cone := FrictionCone.frictionless

/-- The point contact with friction, MLS eq. (5.3), printed p. 217, and Table 5.2, p. 219: wrench
basis `[e₁ e₂ e₃] ∈ ℝ^{6×3}` (unit forces along the contact axes) and the Coulomb cone
`√(f₁² + f₂²) ≤ μ f₃, f₃ ≥ 0`, for a coefficient of friction `μ > 0`. -/
def pointContact (μ : ℝ) (hμ : 0 < μ) : ContactModel Wrench 3 where
  basis := ![⟨Rotation.xAxis, 0⟩, ⟨Rotation.yAxis, 0⟩, ⟨Rotation.zAxis, 0⟩]
  cone := FrictionCone.pointContact μ hμ

/-- The soft-finger contact, MLS eq. (5.4), printed p. 217, and Table 5.2, p. 219: wrench basis
`[e₁ e₂ e₃ e₆] ∈ ℝ^{6×4}` (unit forces along the contact axes and unit moment about the contact
normal) and the cone `√(f₁² + f₂²) ≤ μ f₃, f₃ ≥ 0, |f₄| ≤ γ f₃`, for `μ > 0` and a torsional
friction coefficient `γ > 0`. -/
def softFinger (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) : ContactModel Wrench 4 where
  basis := ![⟨Rotation.xAxis, 0⟩, ⟨Rotation.yAxis, 0⟩, ⟨Rotation.zAxis, 0⟩, ⟨0, Rotation.zAxis⟩]
  cone := FrictionCone.softFinger μ γ hμ hγ

/-- MLS eq. (5.1), printed p. 215: a frictionless point contact applies the wrench
`F_c = (0, 0, f, 0, 0, 0)`, a force of magnitude `f` along the contact normal and no moment. -/
theorem frictionless_wrench (f : Fin 1 → ℝ) :
    frictionless.wrench f = ⟨WithLp.toLp 2 ![0, 0, f 0], 0⟩ := by
  rw [wrench_apply]
  apply Wrench.ext
  · ext i
    fin_cases i <;> simp [frictionless, Rotation.zAxis]
  · simp [frictionless]

/-- MLS eq. (5.3), printed p. 217: a point contact with friction applies the wrench
`F_c = (f₁, f₂, f₃, 0, 0, 0)`, a force with no moment about the contact point. -/
theorem pointContact_wrench (μ : ℝ) (hμ : 0 < μ) (f : Fin 3 → ℝ) :
    (pointContact μ hμ).wrench f = ⟨WithLp.toLp 2 ![f 0, f 1, f 2], 0⟩ := by
  rw [wrench_apply]
  apply Wrench.ext
  · ext i
    fin_cases i <;> simp [pointContact, Fin.sum_univ_succ, Rotation.xAxis, Rotation.yAxis,
      Rotation.zAxis]
  · simp [pointContact, Fin.sum_univ_succ]

/-- MLS eq. (5.4), printed p. 217: a soft-finger contact applies the wrench
`F_c = (f₁, f₂, f₃, 0, 0, f₄)`, a force and a moment `f₄` about the contact normal. -/
theorem softFinger_wrench (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (f : Fin 4 → ℝ) :
    (softFinger μ γ hμ hγ).wrench f =
      ⟨WithLp.toLp 2 ![f 0, f 1, f 2], WithLp.toLp 2 ![0, 0, f 3]⟩ := by
  rw [wrench_apply]
  apply Wrench.ext
  · ext i
    fin_cases i <;> simp [softFinger, Fin.sum_univ_succ, Rotation.xAxis, Rotation.yAxis,
      Rotation.zAxis]
  · ext i
    fin_cases i <;> simp [softFinger, Fin.sum_univ_succ, Rotation.zAxis]

/-- The wrench basis as the real `6 × m` matrix of MLS printed p. 218 (`B_c ∈ ℝ^{p×m}`): column `j`
holds the six coordinates `Wrench.coordinates` (force rows `Sum.inl`, moment rows `Sum.inr`) of
basis column `j`. -/
def basisMatrix (c : ContactModel Wrench m) : Matrix (Fin 3 ⊕ Fin 3) (Fin m) ℝ :=
  Matrix.of fun r j => (c.basis j).coordinates r

/-- The matrix of the wrench basis acts on coefficients as `F_c = B_c f_c` in six coordinates,
MLS eq. (5.5), printed p. 218. -/
theorem basisMatrix_mulVec (c : ContactModel Wrench m) (f : Fin m → ℝ) :
    c.basisMatrix *ᵥ f = (c.wrench f).coordinates := by
  rw [wrench_apply, ← Wrench.coordinatesEquiv_apply, map_sum]
  funext r
  simp [basisMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- The frictionless wrench basis is the printed column `(0, 0, 1, 0, 0, 0)ᵀ` of Table 5.2, MLS
printed p. 219 (force rows on top, moment rows below). -/
theorem frictionless_basisMatrix :
    frictionless.basisMatrix = Matrix.fromRows !![0; 0; 1] !![0; 0; 0] := by
  ext r j
  fin_cases j
  rcases r with i | i <;> fin_cases i <;>
    simp [basisMatrix, frictionless, Wrench.coordinates, Rotation.zAxis]

/-- The point-contact wrench basis is the printed `6 × 3` matrix `[e₁ e₂ e₃]` of Table 5.2, MLS
printed p. 219. -/
theorem pointContact_basisMatrix (μ : ℝ) (hμ : 0 < μ) :
    (pointContact μ hμ).basisMatrix =
      Matrix.fromRows !![1, 0, 0; 0, 1, 0; 0, 0, 1] !![0, 0, 0; 0, 0, 0; 0, 0, 0] := by
  ext r j
  rcases r with i | i <;> fin_cases i <;> fin_cases j <;>
    simp [basisMatrix, pointContact, Wrench.coordinates, Rotation.xAxis, Rotation.yAxis,
      Rotation.zAxis]

/-- The soft-finger wrench basis is the printed `6 × 4` matrix `[e₁ e₂ e₃ e₆]` of Table 5.2, MLS
printed p. 219. -/
theorem softFinger_basisMatrix (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (softFinger μ γ hμ hγ).basisMatrix =
      Matrix.fromRows !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]
        !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1] := by
  ext r j
  rcases r with i | i <;> fin_cases i <;> fin_cases j <;>
    simp [basisMatrix, softFinger, Wrench.coordinates, Rotation.xAxis, Rotation.yAxis,
      Rotation.zAxis]

/-! ### The constraint `B_cᵀ` on twists (MLS eq. (5.9), printed p. 235) -/

/-- The transpose `B_cᵀ` of a spatial wrench basis acting on twists, MLS eq. (5.9), printed
p. 235: coefficient `j` of `B_cᵀ V` is the pairing `f · v + τ · ω` (MLS printed p. 61) of basis
column `j` with the twist `V`. For the relative velocity `V = V^b_{fc}` of the contact frame with
respect to the fingertip, `B_cᵀ V = 0` is the contact constraint (5.9). Wrench order `(f, τ)`,
twist order `(v, ω)`. -/
def constraint (c : ContactModel Wrench m) : Twist →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi fun j => Wrench.pairing (c.basis j)

/-- Coefficient `j` of `B_cᵀ V` is the pairing of basis column `j` with `V` (MLS eq. (5.9),
printed p. 235; pairing of MLS p. 61). -/
theorem constraint_apply (c : ContactModel Wrench m) (V : Twist) (j : Fin m) :
    c.constraint V j = Wrench.pair (c.basis j) V := rfl

/-- `B_cᵀ` is onto `ℝ^m` when the `m` columns of the wrench basis are linearly independent (MLS
printed p. 218: `m` "indicates the number of independent forces that can be applied by the
contact"; the constraint is eq. (5.9), p. 235). Proof: a nonzero linear form `φ` on `ℝ^m` vanishing
on the range of `B_cᵀ` has coefficients `f` with `(B_c f) · V = φ(B_cᵀ V) = 0` for every twist `V`,
so `B_c f = 0` (`Wrench.ext_pair`) and `f = 0` by independence. Wrench order `(f, τ)`, twist order
`(v, ω)`. -/
theorem constraint_surjective_of_linearIndependent (c : ContactModel Wrench m)
    (hc : LinearIndependent ℝ c.basis) : Function.Surjective c.constraint := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ :=
    (LinearMap.range c.constraint).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  set f : Fin m → ℝ := fun j => φ (Pi.single j 1) with hf_def
  have hφ : ∀ y : Fin m → ℝ, φ y = ∑ j, y j * f j := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf_def, ← smul_eq_mul, ← map_smul]
    congr 1
    ext k
    simp [Pi.single_apply]
  have hw : c.wrench f = 0 := by
    refine Wrench.ext_pair fun V => ?_
    have h0 : φ (c.constraint V) = 0 := hle ⟨V, rfl⟩
    rw [hφ] at h0
    rw [Wrench.pair_zero_left, wrench_apply, Wrench.pair_sum_left, ← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Wrench.pair_smul_left, constraint_apply, mul_comm]
  have hf : f = 0 := funext (Fintype.linearIndependent_iff.mp hc f (by rwa [wrench_apply] at hw))
  exact hφ0 (LinearMap.ext fun y => by rw [hφ, hf]; simp)

/-- The frictionless constraint map `B_cᵀ` is onto `ℝ¹` (its basis column is nonzero; MLS
eq. (5.1), printed p. 215, and eq. (5.9), p. 235). -/
theorem frictionless_constraint_surjective : Function.Surjective frictionless.constraint := by
  refine constraint_surjective_of_linearIndependent _ (Fintype.linearIndependent_iff.mpr ?_)
  intro g hg
  rw [← wrench_apply, frictionless_wrench] at hg
  simp [Wrench.ext_iff] at hg
  intro i
  fin_cases i
  simp_all

/-- The point-contact constraint map `B_cᵀ` of MLS eq. (5.3) (printed p. 217) is onto `ℝ³`: its
three basis columns are the unit forces along the contact axes (MLS eq. (5.9), p. 235). -/
theorem pointContact_constraint_surjective (μ : ℝ) (hμ : 0 < μ) :
    Function.Surjective (pointContact μ hμ).constraint := by
  refine constraint_surjective_of_linearIndependent _ (Fintype.linearIndependent_iff.mpr ?_)
  intro g hg
  rw [← wrench_apply, pointContact_wrench] at hg
  simp [Wrench.ext_iff] at hg
  intro i
  fin_cases i <;> simp_all

/-- The soft-finger constraint map `B_cᵀ` of MLS eq. (5.4) (printed p. 217) is onto `ℝ⁴`: its
basis columns are the three unit forces and the unit moment about the contact normal (MLS
eq. (5.9), p. 235). -/
theorem softFinger_constraint_surjective (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    Function.Surjective (softFinger μ γ hμ hγ).constraint := by
  refine constraint_surjective_of_linearIndependent _ (Fintype.linearIndependent_iff.mpr ?_)
  intro g hg
  rw [← wrench_apply, softFinger_wrench] at hg
  simp [Wrench.ext_iff] at hg
  intro i
  fin_cases i <;> simp_all

/-- `B_cᵀ` is the transpose of `B_c`: `(B_cᵀ V) · f = (B_c f) · V`, the dot product of
coefficients on one side and the twist–wrench pairing (MLS printed p. 61) on the other
(MLS eqs. (5.5), (5.9), printed pp. 218, 235). -/
theorem sum_constraint_mul (c : ContactModel Wrench m) (V : Twist) (f : Fin m → ℝ) :
    ∑ j, c.constraint V j * f j = Wrench.pair (c.wrench f) V := by
  rw [wrench_apply, Wrench.pair_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Wrench.pair_smul_left, constraint_apply, mul_comm]

/-- In six coordinates `B_cᵀ` is the transpose of the `6 × m` basis matrix: `B_cᵀ V` is
`basisMatrixᵀ` applied to the twist coordinates (MLS eq. (5.9), printed p. 235; wrench rows
`(f, τ)` against twist rows `(v, ω)`). -/
theorem basisMatrix_transpose_mulVec (c : ContactModel Wrench m) (V : Twist) :
    c.basisMatrixᵀ *ᵥ V.coordinates = c.constraint V := by
  funext j
  have hpair : Wrench.pair (c.basis j) V = (c.basis j).coordinates ⬝ᵥ V.coordinates := by
    simp only [Wrench.pair, Wrench.coordinates, Twist.coordinates, dotProduct,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [constraint_apply, hpair]
  simp [basisMatrix, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- The frictionless contact constraint of MLS printed p. 235: `[0 0 1 0 0 0] V = 0` constrains
only the linear velocity along the contact `z`-axis (the inward normal); `B_cᵀ V` is that one
coordinate. -/
theorem frictionless_constraint (V : Twist) :
    frictionless.constraint V = ![V.coordinates (Sum.inl 2)] := by
  funext j
  fin_cases j
  simp [constraint_apply, frictionless, Wrench.pair, Rotation.zAxis, Twist.coordinates,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-! ### The planar point contact of Example 5.3 -/

/-- The planar point contact with friction, MLS Example 5.3, printed p. 222: in planar wrench
coordinates `(f_x, f_y, τ)` the wrench basis is `B_c = [[1, 0], [0, 1], [0, 0]]` (unit forces along
the contact `x`- and `y`-axes; the `y`-axis is the inward normal) and the friction cone is
`|f₁| ≤ μ f₂, f₂ ≥ 0`, for `μ > 0`. -/
def planarPointContact (μ : ℝ) (hμ : 0 < μ) : ContactModel (Fin 3 → ℝ) 2 where
  basis := ![![1, 0, 0], ![0, 1, 0]]
  cone := FrictionCone.planarPointContact μ hμ

/-- The planar contact wrench of MLS Example 5.3, printed p. 222: `B_c f = (f₁, f₂, 0)`. -/
theorem planarPointContact_wrench (μ : ℝ) (hμ : 0 < μ) (f : Fin 2 → ℝ) :
    (planarPointContact μ hμ).wrench f = ![f 0, f 1, 0] := by
  rw [wrench_apply]
  funext i
  fin_cases i <;> simp [planarPointContact, Fin.sum_univ_succ]

end ContactModel

namespace Planar

/-- The planar wrench transformation of MLS Example 5.3, printed p. 222: for a contact frame with
orientation `R ∈ SO(2)` and position `p = (p_x, p_y)` relative to the object frame,
`[f_o; τ_o] = [[R, 0], [[-p_y, p_x] R, 1]] [f_c; τ_c]`, a `3 × 3` matrix on planar wrench
coordinates `(f_x, f_y, τ)`. Lean `p 0, p 1` are `p_x, p_y`. The rule is defined for any matrix
`R`; `transform_embedWrench` identifies it with the spatial rule (2.66) for `R ∈ SO(2)`. -/
def wrenchTransform (R : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![R 0 0, R 0 1, 0;
    R 1 0, R 1 1, 0;
    -p 1 * R 0 0 + p 0 * R 1 0, -p 1 * R 0 1 + p 0 * R 1 1, 1]

/-- The planar rule of MLS printed p. 222 in components: `f_o = R f_c` and
`τ_o = p_x (R f_c)_y - p_y (R f_c)_x + τ_c`, the planar moment of the transferred force about the
object origin plus the contact moment. -/
theorem wrenchTransform_mulVec (R : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    wrenchTransform R p *ᵥ w =
      ![R 0 0 * w 0 + R 0 1 * w 1, R 1 0 * w 0 + R 1 1 * w 1,
        p 0 * (R 1 0 * w 0 + R 1 1 * w 1) - p 1 * (R 0 0 * w 0 + R 0 1 * w 1) + w 2] := by
  funext i
  fin_cases i <;> simp [wrenchTransform, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- A planar rotation `R ∈ SO(2)` as the rotation `[[R, 0], [0, 1]] ∈ SO(3)` about the `z`-axis
(supporting declaration for identifying the planar wrench rule of MLS printed p. 222 with the
spatial rule (2.66)). -/
def rotation (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) : Rotation :=
  ⟨!![(R : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (R : Matrix (Fin 2) (Fin 2) ℝ) 0 1, 0;
      (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (R : Matrix (Fin 2) (Fin 2) ℝ) 1 1, 0;
      0, 0, 1], by
    obtain ⟨hO, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp R.2
    have hRR := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp hO
    set A : Matrix (Fin 2) (Fin 2) ℝ := (R : Matrix (Fin 2) (Fin 2) ℝ)
    have h00 : A 0 0 * A 0 0 + A 0 1 * A 0 1 = 1 := by
      have := congrFun (congrFun hRR 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h01 : A 0 0 * A 1 0 + A 0 1 * A 1 1 = 0 := by
      have := congrFun (congrFun hRR 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h11 : A 1 0 * A 1 0 + A 1 1 * A 1 1 = 1 := by
      have := congrFun (congrFun hRR 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact hdet
    refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first
          | linear_combination h00
          | linear_combination h01
          | linear_combination h11
    · rw [Matrix.det_fin_three]
      simp
      linear_combination hd⟩

/-- A planar frame `(R, p)` with `R ∈ SO(2)` as the rigid transformation `([[R, 0], [0, 1]],
(p_x, p_y, 0))` of `SE(3)` (supporting declaration for MLS printed p. 222). -/
def rigidTransform (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → ℝ) :
    RigidTransform :=
  ⟨rotation R, WithLp.toLp 2 ![p 0, p 1, 0]⟩

/-- A planar wrench `(f_x, f_y, τ)` as the spatial wrench with force `(f_x, f_y, 0)` and moment
`(0, 0, τ)` about the `z`-axis (MLS printed p. 222: `τ` is the torque about the normal to the
plane). -/
def embedWrench : (Fin 3 → ℝ) →ₗ[ℝ] Wrench where
  toFun w := ⟨WithLp.toLp 2 ![w 0, w 1, 0], WithLp.toLp 2 ![0, 0, w 2]⟩
  map_add' v w := by
    apply Wrench.ext <;> ext i <;> fin_cases i <;> simp
  map_smul' c w := by
    apply Wrench.ext <;> ext i <;> fin_cases i <;> simp

/-- The embedding of planar wrenches into spatial wrenches is injective (supporting lemma for MLS
printed p. 222). -/
theorem embedWrench_injective : Function.Injective embedWrench := by
  intro v w h
  have hf := congrArg (fun F : Wrench => F.force) h
  have ht := congrArg (fun F : Wrench => F.torque) h
  funext i
  fin_cases i
  · simpa [embedWrench] using congrFun (congrArg WithLp.ofLp hf) 0
  · simpa [embedWrench] using congrFun (congrArg WithLp.ofLp hf) 1
  · simpa [embedWrench] using congrFun (congrArg WithLp.ofLp ht) 2

/-- **The planar wrench rule of MLS Example 5.3 (printed p. 222) is the spatial rule (2.66).**
For a planar frame `(R, p)`, `R ∈ SO(2)`, the spatial transfer `Wrench.transform` (MLS
eqs. (2.65)–(2.66), p. 62: `F_A = Ad_{g_AB⁻¹}ᵀ F_B`) of the embedded planar wrench is the
embedding of `[[R, 0], [[-p_y, p_x] R, 1]] [f; τ]`. -/
theorem transform_embedWrench (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → ℝ)
    (w : Fin 3 → ℝ) :
    Wrench.transform (rigidTransform R p) (embedWrench w) =
      embedWrench (wrenchTransform R p *ᵥ w) := by
  rw [wrenchTransform_mulVec]
  apply Wrench.ext
  · ext i
    fin_cases i <;>
      simp [embedWrench, rigidTransform, rotation, Rotation.act_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;>
      simp [embedWrench, rigidTransform, rotation, Rotation.act_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, Vec3.cross_coordinates, crossProduct]

end Planar

end RoboLean
