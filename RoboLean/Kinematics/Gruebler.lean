import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith

/-!
# Gruebler's formula as a count of independent velocity constraints

MLS Chapter 3, §5.2, printed p. 133, eq. (3.66): "Let `N` be the number of links in the mechanism,
`g` the number of joints, and `fᵢ` the number of degrees of freedom for the `i`th joint. ... If all
of the joints define independent constraints, the number of degrees of freedom for the mechanism
is `F = 6N - ∑ᵢ (6 - fᵢ) = 6(N - g) + ∑ᵢ fᵢ`. ... For planar motions, Gruebler's formula holds
with 6 replaced by 3." The four-bar linkage (p. 136) has `N = 3` links (the ground is not
counted), `g = 4` joints and `fᵢ = 1`: `F = 3(3 - 4) + 4 = 1` in the plane and `6(3 - 4) + 4 = -2`
in space, "an apparent paradox" left as an exercise.

Convention (an instantaneous reading; the book does not fix one): degrees of freedom are counted
at the velocity level. Each of the `N` moving links has a velocity in a real vector space `E` of
dimension `d` (twists, `d = 6`; planar twists, `d = 3`); the ground has velocity `0`. Joint `j`
connects two bodies (`none` is the ground) and lets their relative velocity range over a subspace
`Sⱼ` of dimension `fⱼ`, its freedom. The admissible link velocities are those whose relative
velocity across every joint lies in that joint's freedom; this is the kernel of the constraint map
sending link velocities to the relative velocities modulo the freedoms, a map into a space of
dimension `∑ⱼ (d - fⱼ)`. "The joints define independent constraints" is read as: the constraint
map is onto. Then:

* the dimension of the admissible velocities is always at least `dN - ∑ⱼ (d - fⱼ)`
  (`grueblerCount_le_finrank_velocities`);
* it equals Gruebler's count exactly when the constraints are independent
  (`finrank_velocities_eq_grueblerCount_iff`), eq. (3.66);
* the two printed forms of the count agree (`grueblerCount_eq`).

The configuration space and its dimension as a manifold are not formalized; the printed four-bar
numbers are checked as arithmetic. These are statements about the linear model only.
-/

noncomputable section

namespace RoboLean

/-- **Gruebler's count, MLS eq. (3.66), p. 133:** `F = d N - ∑ⱼ (d - fⱼ)` as an integer, with `d`
the dimension of a link's velocity space (`6` spatial, `3` planar), `N` the number of moving links
and `fⱼ` the degrees of freedom of joint `j`. -/
def grueblerCount {g : ℕ} (d N : ℕ) (f : Fin g → ℕ) : ℤ :=
  d * N - ∑ j, ((d : ℤ) - f j)

/-- **MLS eq. (3.66), p. 133: the two forms of Gruebler's formula agree**,
`d N - ∑ᵢ (d - fᵢ) = d (N - g) + ∑ᵢ fᵢ` (integer arithmetic). -/
theorem grueblerCount_eq {g : ℕ} (d N : ℕ) (f : Fin g → ℕ) :
    grueblerCount d N f = d * ((N : ℤ) - g) + ∑ j, (f j : ℤ) := by
  simp only [grueblerCount, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **MLS p. 136: the four-bar linkage in the plane**, `N = 3`, `g = 4`, `fᵢ = 1`:
`F = 3(3 - 4) + 4 = 1`. -/
theorem grueblerCount_fourBar_planar : grueblerCount 3 3 (fun _ : Fin 4 => 1) = 1 := by
  norm_num [grueblerCount, Fin.sum_univ_four]

/-- **MLS p. 136: the four-bar linkage counted in space**, `F = 6(3 - 4) + 4 = -2` (the book's
"apparent paradox"). -/
theorem grueblerCount_fourBar_spatial : grueblerCount 6 3 (fun _ : Fin 4 => 1) = -2 := by
  norm_num [grueblerCount, Fin.sum_univ_four]

/-- The velocity-level model of a mechanism for Gruebler's formula (MLS p. 133): `N` moving links
with velocities in `E`, and `g` joints, joint `j` connecting the bodies `proximal j` and
`distal j` (`none` is the ground, whose velocity is zero) and letting their relative velocity
range over the subspace `freedom j`. -/
structure LinkageModel (E : Type*) [AddCommGroup E] [Module ℝ E] (N g : ℕ) where
  /-- The body on the base side of joint `j` (`none`: the ground). -/
  proximal : Fin g → Option (Fin N)
  /-- The body on the far side of joint `j` (`none`: the ground). -/
  distal : Fin g → Option (Fin N)
  /-- The relative velocities joint `j` permits; its dimension is the joint's freedom `fⱼ`. -/
  freedom : Fin g → Submodule ℝ E

namespace LinkageModel

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {N g : ℕ}

/-- The velocity of a body: the link velocity `V l` for a moving link, zero for the ground
(MLS p. 133, the ground has no degrees of freedom). -/
def bodyVelocity (V : Fin N → E) : Option (Fin N) → E
  | none => 0
  | some l => V l

/-- The relative velocity across joint `j`: distal body minus proximal body (MLS p. 133). -/
def relativeVelocity (L : LinkageModel E N g) (V : Fin N → E) (j : Fin g) : E :=
  bodyVelocity V (L.distal j) - bodyVelocity V (L.proximal j)

/-- The constraint map of MLS p. 133: link velocities to the relative velocity across each joint
modulo that joint's freedom, a linear map into `∏ⱼ E ⧸ Sⱼ`. -/
def constraintMap (L : LinkageModel E N g) : (Fin N → E) →ₗ[ℝ] ((j : Fin g) → E ⧸ L.freedom j) where
  toFun V j := Submodule.Quotient.mk (L.relativeVelocity V j)
  map_add' := by
    intro V W
    funext j
    simp only [relativeVelocity, Pi.add_apply]
    rw [← Submodule.Quotient.mk_add]
    congr 1
    cases L.distal j <;> cases L.proximal j <;> simp [bodyVelocity] <;> abel
  map_smul' := by
    intro a V
    funext j
    simp only [relativeVelocity, RingHom.id_apply, Pi.smul_apply]
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    cases L.distal j <;> cases L.proximal j <;> simp [bodyVelocity, smul_sub]

/-- The admissible link velocities (MLS p. 133): the kernel of the constraint map. -/
def velocities (L : LinkageModel E N g) : Submodule ℝ (Fin N → E) :=
  LinearMap.ker L.constraintMap

/-- Link velocities are admissible exactly when every joint's relative velocity lies in its
freedom (MLS p. 133). -/
theorem mem_velocities_iff (L : LinkageModel E N g) (V : Fin N → E) :
    V ∈ L.velocities ↔ ∀ j, L.relativeVelocity V j ∈ L.freedom j := by
  simp only [velocities, LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  exact forall_congr' fun j => Submodule.Quotient.mk_eq_zero _

/-- **MLS p. 133: "all of the joints define independent constraints"**, read as: the constraint
map is onto `∏ⱼ E ⧸ Sⱼ`, so the `∑ⱼ (d - fⱼ)` scalar constraints are linearly independent. -/
def IndependentConstraints (L : LinkageModel E N g) : Prop :=
  Function.Surjective L.constraintMap

/-- Rank–nullity for the constraint map in Gruebler's terms: the admissible velocities have
dimension Gruebler's count plus the codimension of the range of the constraint map. -/
private theorem finrank_velocities_eq [FiniteDimensional ℝ E] (L : LinkageModel E N g)
    {d : ℕ} (hd : Module.finrank ℝ E = d) {f : Fin g → ℕ}
    (hf : ∀ j, Module.finrank ℝ (L.freedom j) = f j) :
    (Module.finrank ℝ L.velocities : ℤ) = grueblerCount d N f +
      ((Module.finrank ℝ ((j : Fin g) → E ⧸ L.freedom j) : ℤ) -
        Module.finrank ℝ (LinearMap.range L.constraintMap)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker L.constraintMap
  have hdom : Module.finrank ℝ (Fin N → E) = N * d := by
    rw [Module.finrank_pi_fintype, hd]
    simp
  have hcod : (Module.finrank ℝ ((j : Fin g) → E ⧸ L.freedom j) : ℤ) =
      ∑ j, ((d : ℤ) - f j) := by
    rw [Module.finrank_pi_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hq := Submodule.finrank_quotient_add_finrank (L.freedom j)
    rw [hf j, hd] at hq
    omega
  rw [hdom] at hrn
  rw [hcod, velocities, grueblerCount]
  linarith

/-- **Gruebler's count is a lower bound (MLS eq. (3.66), p. 133).** If `E` has dimension `d` and
joint `j` has `fⱼ` degrees of freedom, the admissible link velocities have dimension at least
`d N - ∑ⱼ (d - fⱼ)`, whether or not the constraints are independent. -/
theorem grueblerCount_le_finrank_velocities [FiniteDimensional ℝ E] (L : LinkageModel E N g)
    {d : ℕ} (hd : Module.finrank ℝ E = d) {f : Fin g → ℕ}
    (hf : ∀ j, Module.finrank ℝ (L.freedom j) = f j) :
    grueblerCount d N f ≤ Module.finrank ℝ L.velocities := by
  have h := L.finrank_velocities_eq hd hf
  have hle := Submodule.finrank_le (LinearMap.range L.constraintMap)
  have hle' : (Module.finrank ℝ (LinearMap.range L.constraintMap) : ℤ) ≤
      Module.finrank ℝ ((j : Fin g) → E ⧸ L.freedom j) := by exact_mod_cast hle
  linarith

/-- **MLS eq. (3.66), p. 133: Gruebler's formula.** If `E` has dimension `d` and joint `j` has
`fⱼ` degrees of freedom, the admissible link velocities have dimension exactly
`d N - ∑ⱼ (d - fⱼ) = d(N - g) + ∑ⱼ fⱼ` if and only if the joints define independent
constraints. -/
theorem finrank_velocities_eq_grueblerCount_iff [FiniteDimensional ℝ E] (L : LinkageModel E N g)
    {d : ℕ} (hd : Module.finrank ℝ E = d) {f : Fin g → ℕ}
    (hf : ∀ j, Module.finrank ℝ (L.freedom j) = f j) :
    (Module.finrank ℝ L.velocities : ℤ) = grueblerCount d N f ↔ L.IndependentConstraints := by
  have h := L.finrank_velocities_eq hd hf
  rw [IndependentConstraints, ← LinearMap.range_eq_top]
  constructor
  · intro hk
    apply Submodule.eq_top_of_finrank_eq
    have : (Module.finrank ℝ (LinearMap.range L.constraintMap) : ℤ) =
        Module.finrank ℝ ((j : Fin g) → E ⧸ L.freedom j) := by linarith
    exact_mod_cast this
  · intro htop
    have : Module.finrank ℝ (LinearMap.range L.constraintMap) =
        Module.finrank ℝ ((j : Fin g) → E ⧸ L.freedom j) := by
      rw [htop, finrank_top]
    rw [h, this]
    ring

end LinkageModel
end RoboLean
