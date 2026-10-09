import RoboLean.Geometry.Reciprocal
import RoboLean.Examples.RigidTransform

/-!
# Independent reciprocal-pair and reciprocal-space witnesses

MLS printed pp66–69 defines coordinate reciprocity by zero instantaneous
power and reciprocal systems as annihilators. In the cancellation witness,
the force contribution is `1` and the moment contribution `-1`; changing one moment coordinate gives
power `6`. The reciprocal space of every pure translation is exactly the
pure couples, and conversely; both actual subspaces have dimension three.
These are algebraic statements in one common frame, not contact feasibility
or a conclusion about possible finite motion.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix

/-- The nonzero force and moment contributions cancel across the two components. -/
theorem reciprocal_pair_cancellation :
    Wrench.pair (vec 1 0 0, vec 1 (-1) 0) (vec 1 2 3, vec 4 5 6) = 0 := by
  simp only [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  norm_num [dotProduct, Fin.sum_univ_succ, vec]

/-- Adding one unit of z moment changes the pairing from zero to six. -/
theorem reciprocal_pair_perturbed :
    Wrench.pair (vec 1 0 0, vec 1 (-1) 1) (vec 1 2 3, vec 4 5 6) = 6 := by
  simp only [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  norm_num [dotProduct, Fin.sum_univ_succ, vec]

/-- The reciprocal product can be negative on a nonzero vector paired with itself. -/
theorem reciprocal_product_negative_self :
    Twist.reciprocalProduct (vec 1 0 0, vec (-1) 0 0) (vec 1 0 0, vec (-1) 0 0) = -2 := by
  rw [Twist.reciprocalProduct_eq]
  simp only [Twist.linear, Twist.angular, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  norm_num [dotProduct, Fin.sum_univ_succ, vec]

/-- All pure translations as an actual range submodule, including zero. -/
def translationTwists : Submodule ℝ Twist := (LinearMap.inl ℝ Vec3 Vec3).range

/-- All pure couples as an actual range submodule, including zero. -/
def coupleWrenches : Submodule ℝ Wrench := (LinearMap.inr ℝ Vec3 Vec3).range

theorem mem_translationTwists (ξ : Twist) : ξ ∈ translationTwists ↔ ξ.angular = 0 := by
  change (∃ v : Vec3, (v, 0) = ξ) ↔ ξ.angular = 0
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro h
    exact ⟨ξ.linear, Prod.ext rfl h.symm⟩

theorem mem_coupleWrenches (F : Wrench) : F ∈ coupleWrenches ↔ F.force = 0 := by
  change (∃ τ : Vec3, (0, τ) = F) ↔ F.force = 0
  constructor
  · rintro ⟨τ, rfl⟩
    rfl
  · intro h
    exact ⟨F.torque, Prod.ext h.symm rfl⟩

/-- A wrench pairs to zero with every pure translation exactly when its force is zero. -/
theorem reciprocal_translationTwists : Reciprocal.wrenches translationTwists = coupleWrenches := by
  ext F
  rw [Reciprocal.mem_wrenches, mem_coupleWrenches]
  constructor
  · intro h
    apply ext_inner_right ℝ
    intro v
    have hv := h (v, 0) ((mem_translationTwists _).mpr rfl)
    simpa [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular] using hv
  · intro hf ξ hξ
    have hω := (mem_translationTwists ξ).mp hξ
    simp [Wrench.pair, hf, hω]

/-- A twist pairs to zero with every pure couple exactly when its angular part is zero. -/
theorem reciprocal_coupleWrenches : Reciprocal.twists coupleWrenches = translationTwists := by
  ext ξ
  rw [Reciprocal.mem_twists, mem_translationTwists]
  constructor
  · intro h
    apply ext_inner_left ℝ
    intro ω
    have hω := h (0, ω) ((mem_coupleWrenches _).mpr rfl)
    simpa [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular] using hω
  · intro hω F hF
    have hf := (mem_coupleWrenches F).mp hF
    simp [Wrench.pair, hf, hω]

/-- The range of the injective translation-coordinate map has dimension three. -/
theorem translationTwists_finrank : Module.finrank ℝ translationTwists = 3 := by
  have h : Function.Injective (LinearMap.inl ℝ Vec3 Vec3) := by
    intro v w hvw
    exact congrArg Prod.fst hvw
  calc
    _ = Module.finrank ℝ Vec3 := by exact LinearMap.finrank_range_of_inj h
    _ = 3 := by simp [Vec3]

/-- The range of the injective moment-coordinate map independently has dimension three. -/
theorem coupleWrenches_finrank : Module.finrank ℝ coupleWrenches = 3 := by
  have h : Function.Injective (LinearMap.inr ℝ Vec3 Vec3) := by
    intro v w hvw
    exact congrArg Prod.snd hvw
  calc
    _ = Module.finrank ℝ Vec3 := by exact LinearMap.finrank_range_of_inj h
    _ = 3 := by simp [Vec3]

/-- The actual reciprocal wrench space has dimension three, agreeing with the dimension law. -/
theorem translation_reciprocal_finrank :
    Module.finrank ℝ (Reciprocal.wrenches translationTwists) = 3 := by
  rw [reciprocal_translationTwists, coupleWrenches_finrank]

/-- The reverse reciprocal twist space also has dimension three. -/
theorem couple_reciprocal_finrank :
    Module.finrank ℝ (Reciprocal.twists coupleWrenches) = 3 := by
  rw [reciprocal_coupleWrenches, translationTwists_finrank]

end RoboLean.Examples
