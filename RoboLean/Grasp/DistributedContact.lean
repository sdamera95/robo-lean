import RoboLean.Grasp.Contact

/-!
# Line and plane contacts (MLS Chapter 5, Exercise 4)

MLS Chapter 5, Exercise 4, printed pp. 259–260, "Additional contact models": "Derive the wrench
basis and friction cone for the contact models shown below. Assume the coefficient of sliding
friction is `μ > 0`." The figure (p. 260, read as a rendered image) shows (a) a line contact, an
edge of a box against a plane, and (b) a plane contact, a face of a box against a plane. The book
prints no answer.

Model. A contact made of a segment or a planar region is modeled by Coulomb point contacts with
friction (eq. (5.3), p. 217, `μ > 0`) at finitely many points `qᵢ` of the contact frame (here the
endpoints of the segment and the corners of a rectangle; contact `z`-axis the inward normal,
pp. 214–215). `ContactModel.multiPoint μ hμ q` is the library's `ContactModel` with
`3k` coefficients, coefficient `(i, j)` (index `finProdFinEquiv (i, j)`) the `j`-th contact-frame
component of the force at `qᵢ`; the friction cone is the product of `k` Coulomb cones. Derived:

* its wrenches are exactly the sums of Coulomb point forces at the `qᵢ`;
* a Coulomb force applied at any convex combination of the `qᵢ` is one of its wrenches, so the
  segment's endpoints (resp. the rectangle's corners) carry every Coulomb force distributed
  over the segment (resp. the rectangle) as a finite sum;
* the line contact of half-length `l > 0` along the contact `x`-axis transmits exactly the
  wrenches with zero moment about the line (a five-dimensional wrench space: three forces and the
  moments about the two axes normal to the line);
* the rectangular plane contact with half-sides `a, b > 0` transmits every wrench.

The point-contact reading of a distributed contact (pressure and friction acting only where the
figure shows contact, Coulomb's law pointwise) is a modeling choice made here; nothing claims
that a physical edge or face contact behaves this way.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Grasp

/-- The forces of a multi-point contact, MLS Exercise 4, printed p. 260: the contact-frame force
`(f_{i,0}, f_{i,1}, f_{i,2})` at the `i`-th point is the block of coefficients
`finProdFinEquiv (i, j)`, `j < 3`. -/
def pointBlock {k : ℕ} (f : Fin (k * 3) → ℝ) (i : Fin k) : Fin 3 → ℝ :=
  fun j => f (finProdFinEquiv (i, j))

/-- The friction cone of a contact of `k` Coulomb point contacts, MLS Exercise 4, printed p. 260,
with the point-contact cone of eq. (5.3), p. 217: every force block in the Coulomb cone. -/
def multiPointCone (k : ℕ) (μ : ℝ) : ConvexCone ℝ (Fin (k * 3) → ℝ) where
  carrier := {f | ∀ i, pointBlock f i ∈ pointContactCone μ}
  smul_mem' := fun _ hc _ hf i => (pointContactCone μ).smul_mem hc (hf i)
  add_mem' := fun _ hf _ hg i => (pointContactCone μ).add_mem (hf i) (hg i)

/-- Membership in the multi-point friction cone of MLS Exercise 4, printed p. 260 (Coulomb cone
(5.3), p. 217, at every point). -/
theorem mem_multiPointCone {k : ℕ} {μ : ℝ} {f : Fin (k * 3) → ℝ} :
    f ∈ multiPointCone k μ ↔ ∀ i, pointBlock f i ∈ pointContactCone μ := Iff.rfl

end Grasp

namespace FrictionCone

/-- The multi-point friction cone of MLS Exercise 4, printed p. 260, is a friction cone in the
sense of Definition 5.1, p. 220 (closed, nonempty interior, a convex cone), for `μ > 0`. -/
def multiPoint (k : ℕ) (μ : ℝ) (hμ : 0 < μ) : FrictionCone (Fin (k * 3) → ℝ) where
  toConvexCone := Grasp.multiPointCone k μ
  isClosed := by
    change IsClosed {f : Fin (k * 3) → ℝ | ∀ i, Grasp.pointBlock f i ∈ Grasp.pointContactCone μ}
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => (Grasp.isClosed_pointContactCone μ).preimage
      (continuous_pi fun j => continuous_apply _)
  interior_nonempty := by
    refine ⟨fun n => if (finProdFinEquiv.symm n).2 = 2 then 1 else 0, ?_⟩
    have hU : IsOpen {f : Fin (k * 3) → ℝ |
        ∀ i, Grasp.pointBlock f i ∈ interior (Grasp.pointContactCone μ : Set (Fin 3 → ℝ))} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_interior.preimage
        (continuous_pi fun j => continuous_apply _)
    refine interior_maximal (fun f hf => ?_) hU ?_
    · have hf' : ∀ i, Grasp.pointBlock f i ∈ interior (Grasp.pointContactCone μ : Set (Fin 3 → ℝ)) :=
        hf
      exact Grasp.mem_multiPointCone.2 fun i => interior_subset (hf' i)
    · show ∀ i, _
      intro i
      apply Grasp.mem_interior_pointContactCone <;> simp [Grasp.pointBlock, hμ]

end FrictionCone

namespace ContactModel

/-- The contact of `k` Coulomb point contacts at the points `q : Fin k → Vec3` of the contact
frame, MLS Exercise 4, printed p. 260 (with eq. (5.3), p. 217, `μ > 0`): column `(i, j)` of the
wrench basis is the wrench `(e_j, qᵢ × e_j)` of a unit force along the `j`-th contact axis at
`qᵢ` (wrench at the contact origin, in the contact frame, p. 218). -/
def multiPoint (μ : ℝ) (hμ : 0 < μ) {k : ℕ} (q : Fin k → Vec3) : ContactModel Wrench (k * 3) where
  basis n := Wrench.pointForce (q (finProdFinEquiv.symm n).1)
    (![Rotation.xAxis, Rotation.yAxis, Rotation.zAxis] (finProdFinEquiv.symm n).2)
  cone := FrictionCone.multiPoint k μ hμ

/-- The wrench of a multi-point contact, MLS Exercise 4, printed p. 260: `B_c f = ∑ᵢ (Fᵢ, qᵢ × Fᵢ)`
with `Fᵢ` the force block at `qᵢ`. -/
theorem multiPoint_wrench (μ : ℝ) (hμ : 0 < μ) {k : ℕ} (q : Fin k → Vec3) (f : Fin (k * 3) → ℝ) :
    (multiPoint μ hμ q).wrench f =
      ∑ i, Wrench.pointForce (q i) (WithLp.toLp 2 (Grasp.pointBlock f i)) := by
  rw [wrench_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [multiPoint, Equiv.symm_apply_apply, Fin.sum_univ_three]
  apply Wrench.ext
  · apply WithLp.ofLp_injective
    ext j
    fin_cases j <;> simp [Grasp.pointBlock, Rotation.xAxis, Rotation.yAxis, Rotation.zAxis]
  · apply WithLp.ofLp_injective
    ext j
    fin_cases j <;> simp [Grasp.pointBlock, Rotation.xAxis, Rotation.yAxis, Rotation.zAxis,
      Vec3.cross_coordinates, crossProduct] <;> ring

/-- Coefficients built from force blocks `F i` have those blocks (MLS Exercise 4, p. 260). -/
private theorem pointBlock_ofBlocks {k : ℕ} (F : Fin k → Fin 3 → ℝ) (i : Fin k) :
    Grasp.pointBlock (fun n => F (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2) i =
      F i := by
  ext j
  simp [Grasp.pointBlock]

/-- Forces add under finite sums of wrenches (MLS printed p. 63). -/
private theorem sum_force {ι : Type*} (s : Finset ι) (W : ι → Wrench) :
    (∑ i ∈ s, W i).force = ∑ i ∈ s, (W i).force :=
  map_sum (AddMonoidHom.mk' Wrench.force Wrench.add_force) W s

/-- Moments add under finite sums of wrenches (MLS printed p. 63). -/
private theorem sum_torque {ι : Type*} (s : Finset ι) (W : ι → Wrench) :
    (∑ i ∈ s, W i).torque = ∑ i ∈ s, (W i).torque :=
  map_sum (AddMonoidHom.mk' Wrench.torque Wrench.add_torque) W s

/-- **The friction cone of a multi-point contact**, MLS Exercise 4, printed p. 260: the wrenches
the contact can apply (eq. (5.5), p. 218) are exactly the sums `∑ᵢ (Fᵢ, qᵢ × Fᵢ)` of Coulomb
forces (eq. (5.3), p. 217) at the points `qᵢ`. -/
theorem mem_multiPoint_wrenchCone_iff (μ : ℝ) (hμ : 0 < μ) {k : ℕ} (q : Fin k → Vec3)
    {W : Wrench} :
    W ∈ (multiPoint μ hμ q).wrenchCone ↔
      ∃ F : Fin k → Vec3, (∀ i, WithLp.ofLp (F i) ∈ Grasp.pointContactCone μ) ∧
        W = ∑ i, Wrench.pointForce (q i) (F i) := by
  rw [mem_wrenchCone]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i => WithLp.toLp 2 (Grasp.pointBlock f i), fun i => Grasp.mem_multiPointCone.1 hf i,
      multiPoint_wrench μ hμ q f⟩
  · rintro ⟨F, hF, rfl⟩
    refine ⟨fun n => WithLp.ofLp (F (finProdFinEquiv.symm n).1) (finProdFinEquiv.symm n).2,
      Grasp.mem_multiPointCone.2 fun i => ?_, ?_⟩
    · rw [pointBlock_ofBlocks (fun i => WithLp.ofLp (F i))]
      exact hF i
    · rw [multiPoint_wrench]
      simp only [pointBlock_ofBlocks (fun i => WithLp.ofLp (F i)), WithLp.toLp_ofLp]

/-- **Distributed forces**, MLS Exercise 4, printed p. 260: a Coulomb force (eq. (5.3), p. 217)
applied at a convex combination `∑ᵢ wᵢ qᵢ` of the contact points is a wrench of the multi-point
contact: it is the sum of the forces `wᵢ F` at the `qᵢ`. -/
theorem pointForce_mem_multiPoint_wrenchCone (μ : ℝ) (hμ : 0 < μ) {k : ℕ} (q : Fin k → Vec3)
    {w : Fin k → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) {F : Vec3}
    (hF : WithLp.ofLp F ∈ Grasp.pointContactCone μ) :
    Wrench.pointForce (∑ i, w i • q i) F ∈ (multiPoint μ hμ q).wrenchCone := by
  rw [mem_multiPoint_wrenchCone_iff]
  refine ⟨fun i => w i • F, fun i => ?_, ?_⟩
  · show WithLp.ofLp (w i • F) ∈ Grasp.pointContactCone μ
    rcases (hw i).lt_or_eq with h | h
    · rw [WithLp.ofLp_smul]
      exact (Grasp.pointContactCone μ).smul_mem h hF
    · rw [← h, zero_smul, WithLp.ofLp_zero]
      simp
  · apply Wrench.ext
    · rw [sum_force]
      simp [← Finset.sum_smul, hsum]
    · rw [sum_torque]
      apply WithLp.ofLp_injective
      simp only [Wrench.pointForce_torque, Vec3.cross_coordinates, WithLp.ofLp_sum,
        WithLp.ofLp_smul, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- The endpoints `(∓l, 0, 0)` of a line contact of half-length `l` along the contact `x`-axis,
MLS Exercise 4(a), printed p. 260 (contact frame at the midpoint, `z`-axis the inward normal). -/
def lineContactPoints (l : ℝ) : Fin 2 → Vec3 :=
  ![WithLp.toLp 2 ![-l, 0, 0], WithLp.toLp 2 ![l, 0, 0]]

/-- **The line contact**, MLS Exercise 4(a), printed p. 260: Coulomb point contacts with friction
(eq. (5.3), p. 217, `μ > 0`) at the two endpoints of a segment of half-length `l` along the
contact `x`-axis; six coefficients, friction cone the product of two Coulomb cones. -/
def lineContact (μ : ℝ) (hμ : 0 < μ) (l : ℝ) : ContactModel Wrench (2 * 3) :=
  multiPoint μ hμ (lineContactPoints l)

/-- MLS Exercise 4(a), printed p. 260: a Coulomb force (eq. (5.3), p. 217) applied at any point
`(s, 0, 0)`, `|s| ≤ l`, of the segment is a wrench of the line contact (`l > 0`). -/
theorem lineContact_pointForce_mem (μ : ℝ) (hμ : 0 < μ) {l : ℝ} (hl : 0 < l) {s : ℝ}
    (hs : |s| ≤ l) {F : Vec3} (hF : WithLp.ofLp F ∈ Grasp.pointContactCone μ) :
    Wrench.pointForce (WithLp.toLp 2 ![s, 0, 0]) F ∈ (lineContact μ hμ l).wrenchCone := by
  obtain ⟨h1, h2⟩ := abs_le.1 hs
  have hpt : (WithLp.toLp 2 ![s, 0, 0] : Vec3) =
      ∑ i, (![(l - s) / (2 * l), (l + s) / (2 * l)] i) • lineContactPoints l i := by
    apply WithLp.ofLp_injective
    ext j
    fin_cases j <;> simp [lineContactPoints, Fin.sum_univ_two]
    field_simp
    ring
  rw [hpt]
  apply pointForce_mem_multiPoint_wrenchCone μ hμ _ _ _ hF
  · intro i
    fin_cases i <;> simp <;> apply div_nonneg <;> linarith
  · simp [Fin.sum_univ_two]
    field_simp
    ring

/-- **The wrench basis of the line contact**, MLS Exercise 4(a), printed p. 260: for `l > 0` the
line contact transmits exactly the wrenches with zero moment about the line (the contact
`x`-axis): three forces and the moments about the `y`- and `z`-axes. -/
theorem lineContact_exists_wrench_iff (μ : ℝ) (hμ : 0 < μ) {l : ℝ} (hl : 0 < l) (W : Wrench) :
    (∃ f, (lineContact μ hμ l).wrench f = W) ↔ W.torque 0 = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    rw [lineContact, multiPoint_wrench, sum_torque]
    simp [Fin.sum_univ_two, lineContactPoints, Vec3.cross_coordinates, crossProduct]
  · intro hW
    refine ⟨fun n => (![![W.force 0 / 2, W.force 1 / 2 - W.torque 2 / (2 * l),
        W.force 2 / 2 + W.torque 1 / (2 * l)], ![W.force 0 / 2,
        W.force 1 / 2 + W.torque 2 / (2 * l), W.force 2 / 2 - W.torque 1 / (2 * l)]]
          (finProdFinEquiv.symm n).1) (finProdFinEquiv.symm n).2, ?_⟩
    rw [lineContact, multiPoint_wrench]
    simp only [pointBlock_ofBlocks]
    apply Wrench.ext
    · rw [sum_force]
      apply WithLp.ofLp_injective
      ext j
      fin_cases j <;> simp [Fin.sum_univ_two]
    · rw [sum_torque]
      apply WithLp.ofLp_injective
      ext j
      fin_cases j <;> simp [Fin.sum_univ_two, lineContactPoints, Vec3.cross_coordinates,
        crossProduct]
      · exact hW.symm
      · field_simp
        ring
      · field_simp
        ring

/-- The corners `(±a, ±b, 0)` of a rectangular plane contact with half-sides `a`, `b` along the
contact `x`- and `y`-axes, MLS Exercise 4(b), printed p. 260 (contact frame at the center,
`z`-axis the inward normal). -/
def planeContactPoints (a b : ℝ) : Fin 4 → Vec3 :=
  ![WithLp.toLp 2 ![-a, -b, 0], WithLp.toLp 2 ![a, -b, 0], WithLp.toLp 2 ![-a, b, 0],
    WithLp.toLp 2 ![a, b, 0]]

/-- **The plane contact**, MLS Exercise 4(b), printed p. 260: Coulomb point contacts with friction
(eq. (5.3), p. 217, `μ > 0`) at the four corners of a rectangle with half-sides `a`, `b`; twelve
coefficients, friction cone the product of four Coulomb cones. -/
def planeContact (μ : ℝ) (hμ : 0 < μ) (a b : ℝ) : ContactModel Wrench (4 * 3) :=
  multiPoint μ hμ (planeContactPoints a b)

/-- MLS Exercise 4(b), printed p. 260: a Coulomb force (eq. (5.3), p. 217) applied at any point
`(x, y, 0)`, `|x| ≤ a`, `|y| ≤ b`, of the rectangle is a wrench of the plane contact
(`a, b > 0`). -/
theorem planeContact_pointForce_mem (μ : ℝ) (hμ : 0 < μ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x y : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) {F : Vec3} (hF : WithLp.ofLp F ∈ Grasp.pointContactCone μ) :
    Wrench.pointForce (WithLp.toLp 2 ![x, y, 0]) F ∈ (planeContact μ hμ a b).wrenchCone := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  obtain ⟨h3, h4⟩ := abs_le.1 hy
  have hpt : (WithLp.toLp 2 ![x, y, 0] : Vec3) =
      ∑ i, (![(a - x) * (b - y) / (4 * a * b), (a + x) * (b - y) / (4 * a * b),
        (a - x) * (b + y) / (4 * a * b), (a + x) * (b + y) / (4 * a * b)] i) •
          planeContactPoints a b i := by
    apply WithLp.ofLp_injective
    ext j
    fin_cases j <;> simp [planeContactPoints, Fin.sum_univ_four]
    · field_simp
      ring
    · field_simp
      ring
  rw [hpt]
  apply pointForce_mem_multiPoint_wrenchCone μ hμ _ _ _ hF
  · intro i
    fin_cases i <;> simp <;> apply div_nonneg <;> nlinarith
  · simp [Fin.sum_univ_four]
    field_simp
    ring

/-- **The wrench basis of the plane contact**, MLS Exercise 4(b), printed p. 260: for `a, b > 0`
the rectangular plane contact transmits every wrench (its wrench basis spans all six
dimensions). -/
theorem planeContact_exists_wrench (μ : ℝ) (hμ : 0 < μ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (W : Wrench) : ∃ f, (planeContact μ hμ a b).wrench f = W := by
  obtain ⟨u₁, hu₁⟩ : ∃ u, u = W.torque 2 / (2 * a) := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u, u = (W.torque 0 / (2 * b) - W.torque 1 / (2 * a)) / 2 := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, v = (W.torque 0 / (2 * b) + W.torque 1 / (2 * a)) / 2 := ⟨_, rfl⟩
  refine ⟨fun n => (![![W.force 0 / 4, W.force 1 / 4 - u₁, W.force 2 / 4 - u₂],
      ![W.force 0 / 4, W.force 1 / 4, W.force 2 / 4 - v₂],
      ![W.force 0 / 4, W.force 1 / 4, W.force 2 / 4 + v₂],
      ![W.force 0 / 4, W.force 1 / 4 + u₁, W.force 2 / 4 + u₂]]
        (finProdFinEquiv.symm n).1) (finProdFinEquiv.symm n).2, ?_⟩
  rw [planeContact, multiPoint_wrench]
  simp only [pointBlock_ofBlocks]
  apply Wrench.ext
  · rw [sum_force]
    apply WithLp.ofLp_injective
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four] <;> ring
  · rw [sum_torque]
    apply WithLp.ofLp_injective
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four, planeContactPoints, Vec3.cross_coordinates,
      crossProduct]
    · rw [hu₂, hv₂]
      field_simp
      ring
    · rw [hu₂, hv₂]
      field_simp
      ring
    · rw [hu₁]
      field_simp
      ring

end ContactModel

end RoboLean
