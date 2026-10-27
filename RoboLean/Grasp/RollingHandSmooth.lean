import RoboLean.Kinematics.SerialChainSmooth
import RoboLean.Grasp.RollingHand

/-!
# Smooth dependence of the contact coordinates on the joint angles (MLS eq. (5.41))

MLS Chapter 5, §6.3, printed pp. 254–255. After Proposition 5.12 (p. 254, a smooth local bijection
between `η` and `g_of` in the contact set) the book writes: "Since `ηᵢ` is a smooth function of
`g_of = g_{po}⁻¹ g_{pfᵢ}` and `g_{pfᵢ}` is a smooth function of `θ`, we can write this constraint
as `J_h(θ, x_o) θ̇ = Gᵀ(θ, x_o) V^b_{po}` (5.41), where `x_o := g_{po}`" (p. 255).

**Formalized.** A pose is read in `ℝ^{3×3} × ℝ³` through its rotation matrix and its translation
(`Rolling.poseCoords`, the coordinates of Proposition 5.12 in the library), and smoothness classes
are Mathlib's `C^k`, `k : WithTop ℕ∞` (`k = ∞` is `C^∞`).

* A family of poses is `C^k` in these coordinates exactly when its homogeneous matrix is
  (`Rolling.contDiff_poseCoords_iff`); hence `t ↦ e^{ξ̂t}` (`Twist.contDiff_poseCoords_exp`), the
  product of exponentials and the forward kinematics `θ ↦ g_st(θ)` of every serial chain
  (`SerialChain.contDiff_poseCoords_poe`, `SerialChain.contDiff_poseCoords_fk`) are `C^k` in
  pose coordinates.
* The relative pose `g_{ofᵢ} = g_{po}⁻¹ g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` of finger `i` of a rolling hand is
  `C^k` in `(θᵢ, x_o)` along every `C^k` family of joint angles and object poses
  (`RollingHand.contDiff_poseCoords_fingerPose_comp`), and in `θᵢ` at a fixed object pose
  (`RollingHand.contDiff_poseCoords_fingerPose`): "`g_{pfᵢ}` is a smooth function of `θ`".
* (5.41) with the smoothness of `θ ↦ ηᵢ`: under the hypotheses of the library's (5.41), the readouts
  `Ψᵢ` of Proposition 5.12 can be chosen so that, besides the equivalence of the first line of
  (5.40) with (5.41), at every joint vector that puts finger `i` at the contact pose `g_of(η₀ᵢ)`
  the contact coordinates read from the finger, `θᵢ ↦ Ψᵢ(g_{ofᵢ}(θᵢ, x_o))`, take the value `η₀ᵢ`
  and are `C¹`, and where every finger is at its contact pose the map `θ ↦ η(θ, x_o)` of all
  fingers is `C¹` (`RollingHand.exists_graspingConstraint_iff_graspingConstraintOfPose_contDiffAt`).
  The order is `C¹` because the charts are `C²` (`IsOrthogonalChartOn`); along a `C¹` family of
  joint angles and object poses through such a point the readout is `C¹` by composition with the
  family lemma above.

Nothing here concerns forces, the persistence of contact or the global contact set of two bodies.
-/

noncomputable section

open Filter Topology

namespace RoboLean

namespace Rolling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

/-- **Pose coordinates and homogeneous coordinates give the same smoothness (MLS p. 35, `g = (p,
R)`, and pp. 36–37, eq. (2.23), `ḡ = [R p; 0 1]`).** A family of poses is `C^k` in the coordinates
`(R, p) ∈ ℝ^{3×3} × ℝ³` exactly when every entry of its homogeneous matrix is `C^k`. -/
theorem contDiff_poseCoords_iff {g : E → RigidTransform} :
    ContDiff ℝ k (fun x => poseCoords (g x)) ↔
      ∀ i j, ContDiff ℝ k fun x => (g x).toHomogeneous i j := by
  rw [RigidTransform.contDiff_toHomogeneous_iff, contDiff_prod_iff]
  simp only [poseCoords]
  constructor
  · rintro ⟨hR, hp⟩
    exact ⟨fun i j => contDiff_pi.mp (contDiff_pi.mp hR i) j, hp⟩
  · rintro ⟨hR, hp⟩
    exact ⟨contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => hR i j, hp⟩

end Rolling

open Rolling

namespace Twist

variable {k : WithTop ℕ∞}

/-- **The twist exponential is smooth in pose coordinates (MLS p. 40 and Proposition 2.8, pp.
41–42).** For every twist `ξ`, `t ↦ e^{ξ̂t}` is `C^k` as a map into `ℝ^{3×3} × ℝ³`, for every
order `k`. -/
theorem contDiff_poseCoords_exp (ξ : Twist) :
    ContDiff ℝ k fun t : ℝ => poseCoords (exp ξ t) :=
  contDiff_poseCoords_iff.mpr fun i j => contDiff_exp_toHomogeneous_apply ξ i j

end Twist

namespace SerialChain

variable {n : ℕ} {k : WithTop ℕ∞}

/-- **The product of exponentials is smooth in pose coordinates (MLS eq. (3.3), p. 87).** For
every chain, `θ ↦ exp(ξ₁θ₁) ⋯ exp(ξₙθₙ)` is `C^k` as a map `ℝⁿ → ℝ^{3×3} × ℝ³`, for every order
`k`. -/
theorem contDiff_poseCoords_poe (c : SerialChain n) :
    ContDiff ℝ k fun θ : Fin n → ℝ => poseCoords (c.poe θ) :=
  contDiff_poseCoords_iff.mpr fun i j => c.contDiff_poe_toHomogeneous i j

/-- **The forward kinematics is smooth in pose coordinates (MLS eq. (3.3), p. 87; p. 255,
"`g_{pfᵢ}` is a smooth function of `θ`").** For every chain, `θ ↦ g_st(θ)` is `C^k` as a map
`ℝⁿ → ℝ^{3×3} × ℝ³`, for every order `k`. -/
theorem contDiff_poseCoords_fk (c : SerialChain n) :
    ContDiff ℝ k fun θ : Fin n → ℝ => poseCoords (c.fk θ) :=
  contDiff_poseCoords_iff.mpr fun i j => c.contDiff_fk_toHomogeneous i j

end SerialChain

namespace RollingHand

open Surface

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

/-- **The relative pose of a finger is smooth in the joint angles and the object pose (MLS p. 255,
`g_{ofᵢ} = g_{po}⁻¹ g_{pfᵢ}` with `g_{pfᵢ}` "a smooth function of `θ`").** Along every family of
joint angles `θᵢ(x)` and object poses `x_o(x)` that are `C^k` (the object pose in pose
coordinates), the relative pose `g_{ofᵢ} = x_o⁻¹ g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` of finger `i` is `C^k` in
pose coordinates. -/
theorem contDiff_poseCoords_fingerPose_comp (h : RollingHand ι m n) (i : ι)
    {θ : E → Fin (n i) → ℝ} {xo : E → RigidTransform} (hθ : ContDiff ℝ k θ)
    (hxo : ContDiff ℝ k fun x => poseCoords (xo x)) :
    ContDiff ℝ k fun x => poseCoords (h.fingerPose i (θ x) (xo x)) := by
  rw [contDiff_poseCoords_iff] at hxo ⊢
  simp only [fingerPose]
  refine RigidTransform.contDiff_toHomogeneous_mul
    (RigidTransform.contDiff_toHomogeneous_inv hxo) ?_
  refine RigidTransform.contDiff_toHomogeneous_mul (fun _ _ => contDiff_const) ?_
  exact fun a b => ((h.finger i).contDiff_fk_toHomogeneous a b).comp hθ

/-- **The relative pose of a finger is a smooth function of its joint angles (MLS p. 255,
"`g_{pfᵢ}` is a smooth function of `θ`").** At every fixed object pose `x_o`, the map
`θᵢ ↦ g_{ofᵢ}(θᵢ, x_o) = x_o⁻¹ g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` is `C^k` in pose coordinates, for every order
`k`. -/
theorem contDiff_poseCoords_fingerPose (h : RollingHand ι m n) (i : ι) (xo : RigidTransform) :
    ContDiff ℝ k fun θi : Fin (n i) → ℝ => poseCoords (h.fingerPose i θi xo) :=
  h.contDiff_poseCoords_fingerPose_comp i contDiff_id contDiff_const

/-- **MLS eq. (5.41), p. 255, with the smoothness of `θ ↦ ηᵢ(θ, x_o)`:** at contact coordinates
`η₀` in the domains of orthogonal charts with every relative curvature form invertible, there are
neighbourhoods `Nᵢ` of `η₀ᵢ` and readouts `Ψᵢ`, `C¹` at the contact poses `g_of(η₀ᵢ)`
(Proposition 5.12, p. 254), such that

* whenever the contact coordinates `η` lie in the `Nᵢ` and every finger is at its contact pose
  (`g_{ofᵢ} = g_of(ηᵢ)`), the first line of (5.40) at `η` is (5.41) at `(θ, x_o)` with the contact
  coordinates read as `Ψᵢ(g_{ofᵢ})`;
* at every joint vector `θᵢ` and object pose `x_o` that put finger `i` at its contact pose
  `g_of(η₀ᵢ)`, the contact coordinates read from the finger, `θᵢ' ↦ Ψᵢ(g_{ofᵢ}(θᵢ', x_o))`, equal
  `η₀ᵢ` at `θᵢ` and are `C¹` there: "`ηᵢ` is a smooth function of `g_of` and `g_{pfᵢ}` is a smooth
  function of `θ`", with `C¹` for the book's "smooth" because the charts are `C²`;
* at every joint vector `θ₀` and object pose `x_o` that put every finger at its contact pose, the
  map `θ ↦ η(θ, x_o) = (Ψᵢ(g_{ofᵢ}(θᵢ, x_o)))ᵢ` of (5.41) equals `η₀` at `θ₀` and is `C¹` there. -/
theorem exists_graspingConstraint_iff_graspingConstraintOfPose_contDiffAt (h : RollingHand ι m n)
    {Uf Uo : ι → Set (Fin 2 → ℝ)} (hf : ∀ i, IsOrthogonalChartOn (h.fingerChart i) (Uf i))
    (ho : ∀ i, IsOrthogonalChartOn (h.objectChart i) (Uo i)) {η₀ : ι → ContactCoords}
    (hηf : ∀ i, (η₀ i).1 ∈ Uf i) (hηo : ∀ i, (η₀ i).2.1 ∈ Uo i)
    (hX : ∀ i, IsUnit (relativeCurvature (curvatureTensor (h.fingerChart i) (η₀ i).1)
      (curvatureTensor (h.objectChart i) (η₀ i).2.1) (η₀ i).2.2).det) :
    ∃ N : ι → Set ContactCoords, ∃ Ψ : ι → PoseCoords → ContactCoords,
      (∀ i, N i ∈ 𝓝 (η₀ i)) ∧
      (∀ i, ContDiffAt ℝ 1 (Ψ i)
        (poseCoords (relativePoseMap (h.fingerChart i) (h.objectChart i) (η₀ i)))) ∧
      (∀ (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (η : ι → ContactCoords),
        (∀ i, η i ∈ N i) →
        (∀ i, h.fingerPose i (θ i) xo =
          relativePoseMap (h.fingerChart i) (h.objectChart i) (η i)) →
        ∀ (θ' : (i : ι) → Fin (n i) → ℝ) (V : Twist),
          h.GraspingConstraint θ xo η θ' V ↔
            h.GraspingConstraintOfPose (fun i g => Ψ i (poseCoords g)) θ xo θ' V) ∧
      (∀ (i : ι) (θi : Fin (n i) → ℝ) (xo : RigidTransform),
        h.fingerPose i θi xo = relativePoseMap (h.fingerChart i) (h.objectChart i) (η₀ i) →
        Ψ i (poseCoords (h.fingerPose i θi xo)) = η₀ i ∧
          ContDiffAt ℝ 1 (fun θi' : Fin (n i) → ℝ => Ψ i (poseCoords (h.fingerPose i θi' xo)))
            θi) ∧
      ∀ (θ₀ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform),
        (∀ i, h.fingerPose i (θ₀ i) xo =
          relativePoseMap (h.fingerChart i) (h.objectChart i) (η₀ i)) →
        (fun i => Ψ i (poseCoords (h.fingerPose i (θ₀ i) xo))) = η₀ ∧
          ContDiffAt ℝ 1 (fun θ : (i : ι) → Fin (n i) → ℝ =>
            fun i => Ψ i (poseCoords (h.fingerPose i (θ i) xo))) θ₀ := by
  have H := fun i => exists_local_inverse_relativePoseMap_of_isOrthogonalChartOn (hf i) (ho i)
    (hηf i) (hηo i) (hX i)
  choose N hN Ψ hΨ _ _ hinv using H
  have hfin : ∀ (i : ι) (θi : Fin (n i) → ℝ) (xo : RigidTransform),
      h.fingerPose i θi xo = relativePoseMap (h.fingerChart i) (h.objectChart i) (η₀ i) →
      Ψ i (poseCoords (h.fingerPose i θi xo)) = η₀ i ∧
        ContDiffAt ℝ 1 (fun θi' : Fin (n i) → ℝ => Ψ i (poseCoords (h.fingerPose i θi' xo)))
          θi := by
    intro i θi xo hpose
    refine ⟨by rw [hpose, hinv i (η₀ i) (mem_of_mem_nhds (hN i))], ?_⟩
    have hΨi := hΨ i
    rw [← hpose] at hΨi
    exact hΨi.comp θi (h.contDiff_poseCoords_fingerPose i xo).contDiffAt
  refine ⟨N, Ψ, hN, hΨ, ?_, hfin, ?_⟩
  · intro θ xo η hηN hpose θ' V
    have hη : (fun i => Ψ i (poseCoords (h.fingerPose i (θ i) xo))) = η := by
      funext i
      rw [hpose i, hinv i (η i) (hηN i)]
    rw [GraspingConstraintOfPose, hη]
  · intro θ₀ xo hpose
    refine ⟨funext fun i => (hfin i (θ₀ i) xo (hpose i)).1, contDiffAt_pi.mpr fun i => ?_⟩
    exact ContDiffAt.comp (g := fun θi' => Ψ i (poseCoords (h.fingerPose i θi' xo)))
      (f := fun θ : (i : ι) → Fin (n i) → ℝ => θ i) θ₀ (hfin i (θ₀ i) xo (hpose i)).2
      (contDiff_pi.mp contDiff_id i).contDiffAt

end RollingHand

end RoboLean
