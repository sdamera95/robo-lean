import RoboLean.Grasp.RollingContact
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth dependence of the contact coordinates on the relative pose (MLS Proposition 5.12)

MLS Chapter 5, §6.3, printed p. 254, with the contact set of p. 249.

**What MLS states.** "Let `W ⊂ SE(3)` be the set of all configurations `g_of` for which the two
objects are in contact. **Proposition 5.12. Smooth dependence of `η` on `g_of`.** There is a smooth
local bijection between `η ∈ ℝ⁵` and `g_of ∈ W ⊂ SE(3)` if the matrix `K_f + R_ψ K_o R_ψᵀ` is full
rank. The proof of this proposition requires application of the implicit function theorem to the
mapping `η ↦ g_of ∈ W` and can be found in [77]" (p. 254). On p. 249, "`W` is the set of all
relative positions and orientations for which the two objects are in contact".

**Formalized.** The contact coordinates are `η = (α_f, α_o, ψ) ∈ ℝ² × ℝ² × ℝ` (`ContactCoords`) and
the mapping is `η ↦ g_of(η)` (`relativePoseMap`, the relative pose of `RoboLean.Rolling`). A pose is
read in `ℝ^{3×3} × ℝ³` through its rotation matrix and its translation (`poseCoords`, injective), so
that smoothness on `SE(3)` is smoothness of a map defined near the pose in this ambient space. The
book does not define `W` beyond the sentence of p. 249; for two chart patches it is taken here as
the set of relative poses that bring a point of the finger patch onto a point of the object patch
with opposed Gauss normals (`contactSet`), and it is exactly the image of `η ↦ g_of(η)` over the
chart domains (`relativePoseMap_mem_contactSet`, `exists_relativePoseMap_eq_of_mem_contactSet`).

For orthogonal charts of class `C^{n+1}` (`n ≥ 1`) and a contact `η₀` in the chart domains:

* `η ↦ g_of(η)` is `C^n` near `η₀` (`contDiffAt_relativePoseMap`);
* its derivative at `η₀` is injective exactly when `K_f + R_ψ K_o R_ψᵀ` is invertible
  (`injective_fderiv_relativePoseMap_iff`; "full rank" for a `2 × 2` matrix);
* **Proposition 5.12:** if `K_f + R_ψ K_o R_ψᵀ` is invertible at `η₀`, there are a neighbourhood
  `N` of `η₀` and a map `Ψ`, `C^n` at `g_of(η₀)`, such that `η ↦ g_of(η)` maps `N` injectively into
  the contact set and `Ψ(g_of(η)) = η` on `N` (`exists_local_inverse_relativePoseMap`): `η` depends
  smoothly on `g_of` over the contact configurations `g_of(N)`.

The proof applies the inverse function theorem (Mathlib's `ContDiffAt.localInverse`) to
`(η, w) ↦ g_of(η) + w` on `ℝ⁵ × C`, with `C` a complement of the range of the derivative; the
injectivity of the derivative comes from the derivative-level core of the proposition along the
straight motions `s ↦ η₀ + s h` (`rates_eq_zero_of_bodyVelocity_eq_zero`).

What is not claimed: that `g_of(N)` is all of `W` near `g_of(η₀)`. The book's `W` collects every
contact of the two bodies; two surfaces can touch at several points at once, and then `W` near
`g_of(η₀)` contains configurations with contact coordinates far from `η₀`. The statement here is
the local one that the implicit function theorem gives.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Rolling

open Surface

/-- **The contact coordinates `η = (α_f, α_o, ψ)` (MLS p. 249) as a point of `ℝ² × ℝ² × ℝ`**, the
book's `η ∈ ℝ⁵` (p. 254): the finger chart coordinates, the object chart coordinates and the contact
angle. -/
abbrev ContactCoords : Type := (Fin 2 → ℝ) × (Fin 2 → ℝ) × ℝ

/-- **The mapping `η ↦ g_of` of MLS Proposition 5.12, p. 254:** the relative pose
`g_of(η) = g_{o c_o}(α_o) (0, diag(R_ψ, −1)) g_{f c_f}(α_f)⁻¹` of `RoboLean.Rolling`. -/
def relativePoseMap (cf co : (Fin 2 → ℝ) → Vec3) (η : ContactCoords) : RigidTransform :=
  relativePose cf co η.1 η.2.1 η.2.2

/-- **The ambient coordinates of a pose (MLS p. 35, `g = (p, R) ∈ SE(3)`):** the `3 × 3` rotation
matrix, read as `Fin 3 → Fin 3 → ℝ`, and the translation. -/
abbrev PoseCoords : Type := (Fin 3 → Fin 3 → ℝ) × Vec3

/-- **The pose `g = (p, R)` in the coordinates `(R, p) ∈ ℝ^{3×3} × ℝ³` (MLS p. 35).** -/
def poseCoords (g : RigidTransform) : PoseCoords := (fun i j => g.rotation.val i j, g.translation)

/-- **A pose is determined by its rotation matrix and translation (MLS p. 35).** -/
theorem poseCoords_injective : Function.Injective poseCoords := by
  intro g h e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  refine RigidTransform.ext (Subtype.ext ?_) e2
  ext i j
  exact congrFun (congrFun e1 i) j

/-- **The contact set of two chart patches (MLS p. 249: "the set of all relative positions and
orientations for which the two objects are in contact"; p. 254):** the relative poses `g` that take
a point `c_f(α_f)` of the finger patch to a point `c_o(α_o)` of the object patch and the finger's
Gauss normal there to the opposite of the object's (the surfaces touch with opposed normals). -/
def contactSet (cf co : (Fin 2 → ℝ) → Vec3) (Uf Uo : Set (Fin 2 → ℝ)) : Set RigidTransform :=
  {g | ∃ αf ∈ Uf, ∃ αo ∈ Uo,
    g.applyPoint (cf αf) = co αo ∧ g.applyVector (gaussNormal cf αf) = -gaussNormal co αo}

variable {cf co : (Fin 2 → ℝ) → Vec3} {Uf Uo : Set (Fin 2 → ℝ)}

/-- **`g_of(η)` is a contact configuration (MLS p. 249):** for orthogonal charts and contact
coordinates in the chart domains, `g_of(η)` lies in the contact set. -/
theorem relativePoseMap_mem_contactSet (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) {η : ContactCoords} (hηf : η.1 ∈ Uf) (hηo : η.2.1 ∈ Uo) :
    relativePoseMap cf co η ∈ contactSet cf co Uf Uo :=
  ⟨η.1, hηf, η.2.1, hηo, relativePose_applyPoint cf co η.1 η.2.1 η.2.2,
    relativePose_applyVector_gaussNormal (hf.orthogonal _ hηf) (hf.partialU_ne_zero hηf)
      (hf.partialV_ne_zero hηf) (ho.orthogonal _ hηo) (ho.partialU_ne_zero hηo)
      (ho.partialV_ne_zero hηo) η.2.2⟩

/-- A point of the unit circle has an angle (supporting lemma for MLS eq. (5.34), p. 251: the
contact rotation `diag(R_ψ, −1)` is read off a rotation fixing the normal line). -/
private theorem exists_angle_of_sq_add_sq_eq_one (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ t : ℝ, Real.cos t = c ∧ Real.sin t = s := by
  let z : ℂ := ⟨c, s⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    change Real.sqrt (c * c + s * s) = 1
    rw [show c * c + s * s = 1 by simpa only [pow_two] using hcs, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  refine ⟨z.arg, ?_, ?_⟩
  · simpa only [hn, div_one] using Complex.cos_arg hz
  · simpa only [hn, div_one] using Complex.sin_arg z

/-- **Every contact configuration of the two patches is a relative pose `g_of(η)` (MLS p. 249):**
for orthogonal charts, a pose in the contact set equals `g_of(η)` for contact coordinates `η` in the
chart domains, the angle `ψ` being read from the rotation between the two Gauss frames. So the
contact set is the image of `η ↦ g_of(η)` over the chart domains. -/
theorem exists_relativePoseMap_eq_of_mem_contactSet (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) {g : RigidTransform} (hg : g ∈ contactSet cf co Uf Uo) :
    ∃ η : ContactCoords, η.1 ∈ Uf ∧ η.2.1 ∈ Uo ∧ relativePoseMap cf co η = g := by
  obtain ⟨αf, hαf, αo, hαo, hp, hn⟩ := hg
  set A := contactFrame co αo
  set B := contactFrame cf αf
  set h := A⁻¹ * g * B with hh
  have ht : h.translation = 0 := by
    have e : h.applyPoint 0 = 0 := by
      rw [hh, RigidTransform.mul_applyPoint, RigidTransform.mul_applyPoint]
      have hB : B.applyPoint 0 = cf αf := by simp [B, RigidTransform.applyPoint]
      have hA : co αo = A.applyPoint 0 := by simp [A, RigidTransform.applyPoint]
      rw [hB, hp, hA, RigidTransform.inv_applyPoint_applyPoint]
    simpa [RigidTransform.applyPoint] using e
  have hz : h.rotation.act (WithLp.toLp 2 ![0, 0, 1]) = -WithLp.toLp 2 ![0, 0, 1] := by
    change h.applyVector _ = _
    rw [hh, RigidTransform.mul_applyVector, RigidTransform.mul_applyVector]
    have hB : B.applyVector (WithLp.toLp 2 ![0, 0, 1]) = gaussNormal cf αf :=
      gaussFrame_act_axisZ (hf.orthogonal _ hαf) (hf.partialU_ne_zero hαf)
        (hf.partialV_ne_zero hαf)
    have hA : gaussNormal co αo = A.applyVector (WithLp.toLp 2 ![0, 0, 1]) :=
      (gaussFrame_act_axisZ (ho.orthogonal _ hαo) (ho.partialU_ne_zero hαo)
        (ho.partialV_ne_zero hαo)).symm
    rw [hB, hn, hA]
    simp [RigidTransform.applyVector, map_neg]
  set Q := h.rotation.val with hQ
  have hcol : ∀ i, Q i 2 = -(![0, 0, 1] : Fin 3 → ℝ) i := by
    intro i
    have := congrArg (fun v : Vec3 => v i) hz
    simpa [Rotation.act_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Q] using this
  have h02 : Q 0 2 = 0 := by simpa using hcol 0
  have h12 : Q 1 2 = 0 := by simpa using hcol 1
  have h22 : Q 2 2 = -1 := by simpa using hcol 2
  have hO1 := h.rotation.mul_transpose
  have hO2 := h.rotation.transpose_mul
  have hdet := h.rotation.det_eq_one
  rw [← hQ] at hO1 hO2 hdet
  have r22 := congrFun (congrFun hO1 2) 2
  have c00 := congrFun (congrFun hO2 0) 0
  have c01 := congrFun (congrFun hO2 0) 1
  have c11 := congrFun (congrFun hO2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_succ, h22] at r22 c00 c01 c11
  rw [Matrix.det_fin_three, h02, h12, h22] at hdet
  have h20 : Q 2 0 = 0 := by nlinarith [sq_nonneg (Q 2 0), sq_nonneg (Q 2 1)]
  have h21 : Q 2 1 = 0 := by nlinarith [sq_nonneg (Q 2 0), sq_nonneg (Q 2 1)]
  rw [h20] at c00
  rw [h20, h21] at c01
  rw [h21] at c11
  have hsq : (Q 0 0 + Q 1 1) ^ 2 + (Q 0 1 - Q 1 0) ^ 2 = 0 := by
    linear_combination c00 + c11 - 2 * hdet
  obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hsq
  have had : Q 1 1 = -Q 0 0 := by linarith [(pow_eq_zero_iff two_ne_zero).mp e1]
  have hbc : Q 1 0 = Q 0 1 := by linarith [(pow_eq_zero_iff two_ne_zero).mp e2]
  obtain ⟨ψ, hcos, hsin⟩ := exists_angle_of_sq_add_sq_eq_one (Q 0 0) (-Q 0 1)
    (by rw [hbc] at c00; linear_combination c00)
  have hoff : h = contactOffset ψ := by
    refine RigidTransform.ext (Subtype.ext ?_) ht
    change Q = contactRotationMatrix ψ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [contactRotationMatrix, hcos, hsin, h02, h12, h22, h20, h21, had, hbc]
  refine ⟨(αf, αo, ψ), hαf, hαo, ?_⟩
  have hg : g = A * h * B⁻¹ := by rw [hh]; group
  rw [hg, hoff]
  rfl

/-- The cross product of MLS p. 26 as a bilinear map (supporting definition for the smoothness of
the Gauss normal, MLS eq. (5.19), p. 245). -/
private def crossBilin : Vec3 →ₗ[ℝ] Vec3 →ₗ[ℝ] Vec3 :=
  LinearMap.mk₂ ℝ Vec3.cross (fun u v w => Vec3.add_cross u v w)
    (fun a u v => Vec3.smul_cross u v a) (fun u v w => Vec3.cross_add u v w)
    (fun a u v => Vec3.cross_smul u v a)

/-- The cross product of MLS p. 26 as a continuous bilinear map (supporting definition for MLS eq.
(5.19), p. 245). -/
private def crossCLM : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ crossBilin)

/-- The cross product of `C^n` vector fields is `C^n` (supporting lemma for MLS eq. (5.19),
p. 245). -/
private theorem contDiffAt_cross {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f g : E → Vec3} {x : E} (hf : ContDiffAt ℝ n f x)
    (hg : ContDiffAt ℝ n g x) : ContDiffAt ℝ n (fun y => Vec3.cross (f y) (g y)) x :=
  (crossCLM.contDiff.contDiffAt.comp x hf).clm_apply hg

/-- The axes of the normalized Gauss frame are `C^n` for a `C^{n+1}` chart (supporting lemma for
MLS eqs. (5.19) and (5.22), p. 245). -/
private theorem contDiffAt_frame {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ} {n : WithTop ℕ∞}
    (hc : ContDiffAt ℝ (n + 1) c α) (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) :
    ContDiffAt ℝ n (frameX c) α ∧ ContDiffAt ℝ n (frameY c) α ∧
      ContDiffAt ℝ n (gaussNormal c) α := by
  have hD : ContDiffAt ℝ n (fderiv ℝ c) α := hc.fderiv_right_succ
  have hU : ContDiffAt ℝ n (partialU c) α := hD.clm_apply contDiffAt_const
  have hV : ContDiffAt ℝ n (partialV c) α := hD.clm_apply contDiffAt_const
  have hX := contDiffAt_cross hU hV
  have h0 := cross_partial_ne_zero h hu hv
  exact ⟨((hU.norm ℝ hu).inv (norm_ne_zero_iff.mpr hu)).smul hU,
    ((hV.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul hV,
    ((hX.norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)).smul hX⟩

/-- The entries of the normalized Gauss frame are `C^n` on the domain of a `C^{n+1}` orthogonal
chart (supporting lemma for MLS eq. (5.22), p. 245). -/
private theorem contDiffAt_gaussFrame_apply {c : (Fin 2 → ℝ) → Vec3} {U : Set (Fin 2 → ℝ)}
    {α : Fin 2 → ℝ} {n : WithTop ℕ∞} (hc : IsOrthogonalChartOn c U)
    (hcn : ContDiffOn ℝ (n + 1) c U) (hα : α ∈ U) (i j : Fin 3) :
    ContDiffAt ℝ n (fun β => (gaussFrame c β).val i j) α := by
  have hev : (fun β => gaussFrameMatrix c β i j) =ᶠ[𝓝 α] fun β => (gaussFrame c β).val i j :=
    Filter.eventually_of_mem (hc.isOpen.mem_nhds hα) fun β hβ => by
      show gaussFrameMatrix c β i j = (gaussFrame c β).val i j
      rw [gaussFrame_val (hc.orthogonal β hβ) (hc.partialU_ne_zero hβ) (hc.partialV_ne_zero hβ)]
  obtain ⟨hx, hy, hn⟩ := contDiffAt_frame (hcn.contDiffAt (hc.isOpen.mem_nhds hα))
    (hc.orthogonal α hα) (hc.partialU_ne_zero hα) (hc.partialV_ne_zero hα)
  have hp : ∀ {v : (Fin 2 → ℝ) → Vec3}, ContDiffAt ℝ n v α →
      ContDiffAt ℝ n (fun β => v β i) α := fun hv =>
    (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).contDiff.contDiffAt.comp α hv
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev.symm
  fin_cases j
  · simpa [gaussFrameMatrix] using hp hx
  · simpa [gaussFrameMatrix] using hp hy
  · simpa [gaussFrameMatrix] using hp hn

/-- The entries of `R_{o f}(η)` (supporting lemma for MLS Proposition 5.12, p. 254). -/
private theorem relativePoseMap_rotation_apply (η : ContactCoords) (i j : Fin 3) :
    (relativePoseMap cf co η).rotation.val i j = ∑ l, (∑ k, (gaussFrame co η.2.1).val i k *
      contactRotationMatrix η.2.2 k l) * (gaussFrame cf η.1).val j l := by
  simp [relativePoseMap, relativePose, Matrix.mul_apply, contactOffset, contactRotation]

/-- The translation of `g_of(η)`: `p_of = c_o(α_o) − R_of c_f(α_f)` (supporting lemma for MLS
Proposition 5.12, p. 254, from the coincidence of the contact points, p. 248). -/
private theorem relativePoseMap_translation (η : ContactCoords) :
    (relativePoseMap cf co η).translation =
      co η.2.1 - (relativePoseMap cf co η).rotation.act (cf η.1) := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact relativePose_applyPoint cf co η.1 η.2.1 η.2.2

/-- **`η ↦ g_of(η)` is `C^n` (MLS Proposition 5.12, p. 254, "smooth"):** for orthogonal charts of
class `C^{n+1}` on their domains and contact coordinates `η` in the domains, the map
`η ↦ (R_of(η), p_of(η))` is `C^n` at `η`. -/
theorem contDiffAt_relativePoseMap {n : WithTop ℕ∞} (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) (hfn : ContDiffOn ℝ (n + 1) cf Uf)
    (hon : ContDiffOn ℝ (n + 1) co Uo) {η : ContactCoords} (hηf : η.1 ∈ Uf) (hηo : η.2.1 ∈ Uo) :
    ContDiffAt ℝ n (fun η => poseCoords (relativePoseMap cf co η)) η := by
  have pf : ContDiffAt ℝ n (fun η : ContactCoords => η.1) η := by fun_prop
  have po : ContDiffAt ℝ n (fun η : ContactCoords => η.2.1) η := by fun_prop
  have pψ : ContDiffAt ℝ n (fun η : ContactCoords => η.2.2) η := by fun_prop
  have hrot : ∀ i j, ContDiffAt ℝ n (fun η => (relativePoseMap cf co η).rotation.val i j) η := by
    intro i j
    simp only [relativePoseMap_rotation_apply]
    refine ContDiffAt.sum fun l _ => ContDiffAt.mul (ContDiffAt.sum fun k _ => ?_) ?_
    · have hA : ContDiffAt ℝ n (fun η : ContactCoords => (gaussFrame co η.2.1).val i k) η :=
        ContDiffAt.comp (g := fun β => (gaussFrame co β).val i k) η
          (contDiffAt_gaussFrame_apply ho hon hηo i k) po
      have hk : ContDiff ℝ n (fun ψ => contactRotationMatrix ψ k l) := by
        fin_cases k <;> fin_cases l <;> simp [contactRotationMatrix] <;> fun_prop
      have hB : ContDiffAt ℝ n (fun η : ContactCoords => contactRotationMatrix η.2.2 k l) η :=
        hk.contDiffAt.comp η pψ
      exact hA.mul hB
    · have hC : ContDiffAt ℝ n (fun η : ContactCoords => (gaussFrame cf η.1).val j l) η :=
        (contDiffAt_gaussFrame_apply hf hfn hηf j l).comp η pf
      exact hC
  have hcf : ContDiffAt ℝ n cf η.1 :=
    (hfn.contDiffAt (hf.isOpen.mem_nhds hηf)).of_le (by simp)
  have hco : ContDiffAt ℝ n co η.2.1 :=
    (hon.contDiffAt (ho.isOpen.mem_nhds hηo)).of_le (by simp)
  have hp : ∀ {v : ContactCoords → Vec3}, ContDiffAt ℝ n v η → ∀ i : Fin 3,
      ContDiffAt ℝ n (fun η => v η i) η := fun hv i =>
    (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).contDiff.contDiffAt.comp η hv
  have htr : ContDiffAt ℝ n (fun η => WithLp.ofLp (relativePoseMap cf co η).translation) η := by
    refine contDiffAt_pi.mpr fun i => ?_
    simp only [relativePoseMap_translation, PiLp.sub_apply, Rotation.act_apply, Matrix.mulVec,
      dotProduct]
    have h1 : ContDiffAt ℝ n (fun η : ContactCoords => co η.2.1) η := hco.comp η po
    have h2 : ContDiffAt ℝ n (fun η : ContactCoords => cf η.1) η := hcf.comp η pf
    exact (hp h1 i).sub (ContDiffAt.sum fun j _ => (hrot i j).mul (hp h2 j))
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => hrot i j) ?_
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.contDiffAt.comp η htr

/-- The pose map is differentiable at contact coordinates in the chart domains (supporting lemma
for MLS Proposition 5.12, p. 254; the charts of an orthogonal chart are `C²`). -/
private theorem differentiableAt_relativePoseMap (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) {η : ContactCoords} (hηf : η.1 ∈ Uf) (hηo : η.2.1 ∈ Uo) :
    DifferentiableAt ℝ (fun η => poseCoords (relativePoseMap cf co η)) η := by
  have h2f : ContDiffOn ℝ (1 + 1) cf Uf := by rw [one_add_one_eq_two]; exact hf.contDiffOn
  have h2o : ContDiffOn ℝ (1 + 1) co Uo := by rw [one_add_one_eq_two]; exact ho.contDiffOn
  exact (contDiffAt_relativePoseMap hf ho h2f h2o hηf hηo).differentiableAt one_ne_zero

/-- The homogeneous derivative of `s ↦ g_of(η + s h)` at `0`, built from the derivative of the
pose map applied to `h` (supporting lemma for MLS Proposition 5.12, p. 254). -/
private def lineDerivative (w : PoseCoords) : HomogeneousMatrix :=
  Matrix.fromBlocks (Matrix.of w.1) (Matrix.of fun i _ => w.2 i) 0 0

/-- Along the straight motion `s ↦ η + s h`, the pose `g_of` has the homogeneous derivative built
from `D(η ↦ g_of(η))(η) h` (supporting lemma for MLS Proposition 5.12, p. 254). -/
private theorem hasDerivAt_line (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) {η : ContactCoords} (hηf : η.1 ∈ Uf) (hηo : η.2.1 ∈ Uo)
    (h : ContactCoords) :
    HasDerivAt (fun s : ℝ => (relativePoseMap cf co (η + s • h)).toHomogeneous)
      (lineDerivative (fderiv ℝ (fun η => poseCoords (relativePoseMap cf co η)) η h)) 0 := by
  have hd := differentiableAt_relativePoseMap hf ho hηf hηo
  have hline : HasDerivAt (fun s : ℝ => η + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add η
  have hF : HasFDerivAt (fun η => poseCoords (relativePoseMap cf co η))
      (fderiv ℝ (fun η => poseCoords (relativePoseMap cf co η)) η) (η + (0 : ℝ) • h) := by
    simpa using hd.hasFDerivAt
  have hc := hF.comp_hasDerivAt (0 : ℝ) hline
  have hR := (ContinuousLinearMap.fst ℝ (Fin 3 → Fin 3 → ℝ) Vec3).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hc
  have hp := (ContinuousLinearMap.snd ℝ (Fin 3 → Fin 3 → ℝ) Vec3).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hc
  exact Surface.hasDerivAt_toHomogeneous_of hR hp

/-- A pose curve with the homogeneous derivative `lineDerivative w` has zero body velocity exactly
when `w = 0` (supporting lemma for MLS Proposition 5.12, p. 254, with MLS eq. (2.60), p. 55). -/
private theorem bodyVelocity_eq_zero_iff {g : ℝ → RigidTransform} {w : PoseCoords}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) (lineDerivative w) 0) :
    RigidTransform.bodyVelocity g (lineDerivative w) 0 hD = 0 ↔ w = 0 := by
  have hb := RigidTransform.hat_bodyVelocity hD
  rw [← RigidTransform.toHomogeneous_inv] at hb
  constructor
  · intro hV
    rw [hV, Twist.hat_zero] at hb
    have hD0 : lineDerivative w = 0 := by
      have := congrArg ((g 0).toHomogeneous * ·) hb
      rw [Matrix.mul_zero, ← Matrix.mul_assoc, RigidTransform.toHomogeneous_mul_inv,
        Matrix.one_mul] at this
      exact this.symm
    refine Prod.ext ?_ ?_
    · funext i j
      have := congrFun (congrFun hD0 (Sum.inl i)) (Sum.inl j)
      rwa [lineDerivative, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, Matrix.of_apply] at this
    · ext i
      have := congrFun (congrFun hD0 (Sum.inl i)) (Sum.inr 0)
      rwa [lineDerivative, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.of_apply] at this
  · intro hw
    apply Twist.hat_injective
    rw [hb, Twist.hat_zero]
    have hD0 : lineDerivative w = 0 := by
      subst hw
      rw [lineDerivative]
      ext (i | i) (j | j)
      · rw [Matrix.fromBlocks_apply₁₁]; rfl
      · rw [Matrix.fromBlocks_apply₁₂]; rfl
      · rw [Matrix.fromBlocks_apply₂₁]; rfl
      · rw [Matrix.fromBlocks_apply₂₂]; rfl
    rw [hD0, Matrix.mul_zero]

/-- **The derivative of `η ↦ g_of(η)` is injective exactly under the rank condition of MLS
Proposition 5.12, p. 254:** for orthogonal charts and contact coordinates `η` in the chart domains,
`D(η ↦ g_of(η))(η)` is injective if and only if `K_f + R_ψ K_o R_ψᵀ` is invertible at `η`. -/
theorem injective_fderiv_relativePoseMap_iff (hf : IsOrthogonalChartOn cf Uf)
    (ho : IsOrthogonalChartOn co Uo) {η : ContactCoords} (hηf : η.1 ∈ Uf) (hηo : η.2.1 ∈ Uo) :
    Function.Injective (fderiv ℝ (fun η => poseCoords (relativePoseMap cf co η)) η) ↔
      IsUnit (relativeCurvature (curvatureTensor cf η.1) (curvatureTensor co η.2.1) η.2.2).det := by
  set L := fderiv ℝ (fun η => poseCoords (relativePoseMap cf co η)) η with hL
  have hαf : ∀ h : ContactCoords, HasDerivAt (fun s : ℝ => (η + s • h).1) h.1 0 := fun h => by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add η.1
  have hαo : ∀ h : ContactCoords, HasDerivAt (fun s : ℝ => (η + s • h).2.1) h.2.1 0 := fun h => by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.2.1).const_add η.2.1
  have hψ : ∀ h : ContactCoords, HasDerivAt (fun s : ℝ => (η + s • h).2.2) h.2.2 0 := fun h => by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.2.2).const_add η.2.2
  have hft : ∀ h : ContactCoords, (η + (0 : ℝ) • h).1 ∈ Uf := fun h => by simpa using hηf
  have hot : ∀ h : ContactCoords, (η + (0 : ℝ) • h).2.1 ∈ Uo := fun h => by simpa using hηo
  have hg : ∀ h : ContactCoords, ∀ᶠ s in 𝓝 (0 : ℝ), relativePoseMap cf co (η + s • h) =
      relativePose cf co (η + s • h).1 (η + s • h).2.1 (η + s • h).2.2 := fun h =>
    Filter.Eventually.of_forall fun _ => rfl
  constructor
  · intro hinj
    by_contra hX
    have hz := (contactEquations_zero_injective_iff (Mf := metricTensor cf η.1)
      (Kf := curvatureTensor cf η.1) (Mo := metricTensor co η.2.1)
      (Ko := curvatureTensor co η.2.1) (Tf := torsionForm cf η.1) (To := torsionForm co η.2.1)
      (ψ := η.2.2) (isUnit_det_metricTensor (hf.partialU_ne_zero hηf) (hf.partialV_ne_zero hηf))
      (isUnit_det_metricTensor (ho.partialU_ne_zero hηo) (ho.partialV_ne_zero hηo))).not.mpr hX
    push Not at hz
    obtain ⟨af, ao, b, h0, hne⟩ := hz
    set h : ContactCoords := (af, ao, b)
    have hD := hasDerivAt_line hf ho hηf hηo h
    have hce := contactEquations_of_hasDerivAt hf ho (hαf h) (hαo h) (hψ h) (hft h) (hot h)
      (hg h) hD
    simp only [zero_smul, add_zero] at hce
    set V := Twist.adjoint (contactFrame cf η.1)⁻¹
      (RigidTransform.bodyVelocity (fun s => relativePoseMap cf co (η + s • h)) _ 0 hD) with hV
    have hV0 : V = 0 := by
      have e1 : ![V.linear 0, V.linear 1] = ![(0 : Twist).linear 0, (0 : Twist).linear 1] :=
        add_left_cancel (hce.linear_tangent.trans h0.linear_tangent.symm)
      have e2 : ![V.angular 1, -V.angular 0] = ![(0 : Twist).angular 1, -(0 : Twist).angular 0] :=
        add_left_cancel (hce.angular_tangent.trans h0.angular_tangent.symm)
      have e3 : V.angular 2 = (0 : Twist).angular 2 :=
        add_left_cancel (hce.angular_normal.trans h0.angular_normal.symm)
      have l0 := congrFun e1 0
      have l1 := congrFun e1 1
      have a1 := congrFun e2 0
      have a0 := congrFun e2 1
      simp at l0 l1 a0 a1 e3
      apply Twist.ext
      · ext i
        fin_cases i
        · simpa using l0
        · simpa using l1
        · simpa using hce.linear_normal
      · ext i
        fin_cases i
        · simpa using a0
        · simpa using a1
        · simpa using e3
    have hB := Twist.adjoint_adjoint_inv (contactFrame cf η.1)
      (RigidTransform.bodyVelocity (fun s => relativePoseMap cf co (η + s • h)) _ 0 hD)
    rw [← hV, hV0, Twist.adjoint_zero] at hB
    have hw := (bodyVelocity_eq_zero_iff hD).mp hB.symm
    have hh0 : h = 0 := hinj (by rw [hw, map_zero])
    exact hne (congrArg Prod.fst hh0) (congrArg (fun x => x.2.1) hh0)
      (congrArg (fun x => x.2.2) hh0)
  · intro hX
    refine (injective_iff_map_eq_zero L).mpr fun h hh => ?_
    have hD := hasDerivAt_line hf ho hηf hηo h
    rw [← hL, hh] at hD
    have hV := (bodyVelocity_eq_zero_iff hD).mpr rfl
    obtain ⟨e1, e2, e3⟩ := rates_eq_zero_of_bodyVelocity_eq_zero hf ho (hαf h) (hαo h) (hψ h)
      (hft h) (hot h) (by simpa using hX) (hg h) hD hV
    exact Prod.ext e1 (Prod.ext e2 e3)

/-- **The local inverse of `η ↦ g_of(η)` (MLS Proposition 5.12, p. 254, by the implicit function
theorem):** for orthogonal charts of class `C^{n+1}` (`n ≥ 1`), contact coordinates `η₀` in the
chart domains and `K_f + R_ψ K_o R_ψᵀ` invertible at `η₀`, there is a map `Ψ` from pose coordinates
to contact coordinates, `C^n` at `g_of(η₀)`, with `Ψ(g_of(η)) = η` for every `η` near `η₀`. -/
theorem exists_contDiffAt_leftInverse_relativePoseMap {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hf : IsOrthogonalChartOn cf Uf) (ho : IsOrthogonalChartOn co Uo)
    (hfn : ContDiffOn ℝ (n + 1) cf Uf) (hon : ContDiffOn ℝ (n + 1) co Uo) {η₀ : ContactCoords}
    (hηf : η₀.1 ∈ Uf) (hηo : η₀.2.1 ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf η₀.1) (curvatureTensor co η₀.2.1)
      η₀.2.2).det) :
    ∃ Ψ : PoseCoords → ContactCoords, ContDiffAt ℝ n Ψ (poseCoords (relativePoseMap cf co η₀)) ∧
      ∀ᶠ η in 𝓝 η₀, Ψ (poseCoords (relativePoseMap cf co η)) = η := by
  set F := fun η => poseCoords (relativePoseMap cf co η) with hF
  have hFn : ContDiffAt ℝ n F η₀ := contDiffAt_relativePoseMap hf ho hfn hon hηf hηo
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  set L := fderiv ℝ F η₀ with hLdef
  have hL : Function.Injective L := (injective_fderiv_relativePoseMap_iff hf ho hηf hηo).mpr hX
  have hFd : HasFDerivAt F L η₀ := (hFn.differentiableAt hn0).hasFDerivAt
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range (L : ContactCoords →ₗ[ℝ] PoseCoords))
  let G : ContactCoords × C → PoseCoords := fun p => F p.1 + (p.2 : PoseCoords)
  let L' : ContactCoords × C →L[ℝ] PoseCoords :=
    L.comp (ContinuousLinearMap.fst ℝ ContactCoords C) +
      C.subtypeL.comp (ContinuousLinearMap.snd ℝ ContactCoords C)
  have hG' : HasFDerivAt G L' (η₀, 0) := by
    have h1 : HasFDerivAt (fun p : ContactCoords × C => F p.1)
        (L.comp (ContinuousLinearMap.fst ℝ ContactCoords C)) (η₀, 0) :=
      HasFDerivAt.comp (f := Prod.fst) ((η₀, 0) : ContactCoords × C) hFd hasFDerivAt_fst
    have h2 : HasFDerivAt (fun p : ContactCoords × C => (p.2 : PoseCoords))
        (C.subtypeL.comp (ContinuousLinearMap.snd ℝ ContactCoords C)) (η₀, 0) :=
      (C.subtypeL.comp (ContinuousLinearMap.snd ℝ ContactCoords C)).hasFDerivAt
    exact h1.add h2
  have hinj : Function.Injective L' := by
    refine (injective_iff_map_eq_zero L').mpr fun p hp => ?_
    have hp' : L p.1 + (p.2 : PoseCoords) = 0 := hp
    have hmem : L p.1 ∈ C := by
      rw [eq_neg_of_add_eq_zero_left hp']
      exact C.neg_mem p.2.2
    have h0 : L p.1 = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ ⟨p.1, rfl⟩ hmem
    have h1 : p.1 = 0 := hL (by rw [h0, map_zero])
    have h2 : (p.2 : PoseCoords) = 0 := by rw [h0, zero_add] at hp'; exact hp'
    exact Prod.ext h1 (Subtype.ext h2)
  have hsurj : Function.Surjective L' := by
    intro y
    have hy : y ∈ LinearMap.range (L : ContactCoords →ₗ[ℝ] PoseCoords) ⊔ C := by
      rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ⟨x, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    exact ⟨(x, ⟨b, hb⟩), hab⟩
  let e := (LinearEquiv.ofBijective (L' : ContactCoords × C →ₗ[ℝ] PoseCoords)
    ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he : (e : ContactCoords × C →L[ℝ] PoseCoords) = L' := ContinuousLinearMap.ext fun _ => rfl
  have hG'' : HasFDerivAt G (e : ContactCoords × C →L[ℝ] PoseCoords) (η₀, 0) := by
    rw [he]; exact hG'
  have hGn : ContDiffAt ℝ n G (η₀, 0) :=
    (ContDiffAt.comp (f := Prod.fst) ((η₀, 0) : ContactCoords × C) hFn contDiffAt_fst).add
      (C.subtypeL.contDiff.comp contDiff_snd).contDiffAt
  have : CompleteSpace (ContactCoords × C) := FiniteDimensional.complete ℝ _
  have hG0 : ∀ η, G (η, 0) = F η := fun η => by simp [G]
  refine ⟨fun y => (hGn.localInverse hG'' hn0 y).1, ?_, ?_⟩
  · have hΦ := hGn.to_localInverse hG'' hn0
    rw [hG0] at hΦ
    exact contDiffAt_fst.comp _ hΦ
  · have hev := (hGn.hasStrictFDerivAt' hG'' hn0).eventually_left_inverse
    have ht : Tendsto (fun η : ContactCoords => ((η, 0) : ContactCoords × C)) (𝓝 η₀)
        (𝓝 (η₀, 0)) := (continuous_id.prodMk continuous_const).tendsto η₀
    filter_upwards [ht.eventually hev] with η hη
    rw [hG0] at hη
    exact congrArg Prod.fst hη

/-- **MLS Proposition 5.12, printed p. 254: smooth dependence of `η` on `g_of`.** For orthogonal
charts of class `C^{n+1}` (`n ≥ 1`; `n = ∞` for smooth charts, `n = ω` for analytic ones),
contact coordinates `η₀` in the chart domains and `K_f + R_ψ K_o R_ψᵀ` invertible ("full rank") at
`η₀`, there are a neighbourhood `N` of `η₀` and a map `Ψ` on pose coordinates, `C^n` at
`g_of(η₀)`, such that `η ↦ g_of(η)` maps `N` into the contact set, is injective on `N`, and
`Ψ(g_of(η)) = η` for every `η ∈ N`: a local bijection between `N` and the contact configurations
`g_of(N)` whose inverse is the restriction of `Ψ`. -/
theorem exists_local_inverse_relativePoseMap {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hf : IsOrthogonalChartOn cf Uf) (ho : IsOrthogonalChartOn co Uo)
    (hfn : ContDiffOn ℝ (n + 1) cf Uf) (hon : ContDiffOn ℝ (n + 1) co Uo) {η₀ : ContactCoords}
    (hηf : η₀.1 ∈ Uf) (hηo : η₀.2.1 ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf η₀.1) (curvatureTensor co η₀.2.1)
      η₀.2.2).det) :
    ∃ N ∈ 𝓝 η₀, ∃ Ψ : PoseCoords → ContactCoords,
      ContDiffAt ℝ n Ψ (poseCoords (relativePoseMap cf co η₀)) ∧
      Set.MapsTo (relativePoseMap cf co) N (contactSet cf co Uf Uo) ∧
      Set.InjOn (relativePoseMap cf co) N ∧
      ∀ η ∈ N, Ψ (poseCoords (relativePoseMap cf co η)) = η := by
  obtain ⟨Ψ, hΨ, hev⟩ := exists_contDiffAt_leftInverse_relativePoseMap hn hf ho hfn hon hηf hηo hX
  have hU : {η : ContactCoords | η.1 ∈ Uf ∧ η.2.1 ∈ Uo} ∈ 𝓝 η₀ :=
    ((hf.isOpen.preimage continuous_fst).inter
      (ho.isOpen.preimage (continuous_fst.comp continuous_snd))).mem_nhds ⟨hηf, hηo⟩
  refine ⟨{η | Ψ (poseCoords (relativePoseMap cf co η)) = η} ∩
    {η | η.1 ∈ Uf ∧ η.2.1 ∈ Uo}, Filter.inter_mem hev hU, Ψ, hΨ, ?_, ?_, ?_⟩
  · intro η hη
    exact relativePoseMap_mem_contactSet hf ho hη.2.1 hη.2.2
  · intro x hx y hy hxy
    rw [← hx.1, ← hy.1, hxy]
  · intro η hη
    exact hη.1

/-- **MLS Proposition 5.12, p. 254, for charts of class `C²`:** the conclusion of
`exists_local_inverse_relativePoseMap` with a `C¹` inverse, under the hypotheses of an orthogonal
chart alone. -/
theorem exists_local_inverse_relativePoseMap_of_isOrthogonalChartOn
    (hf : IsOrthogonalChartOn cf Uf) (ho : IsOrthogonalChartOn co Uo) {η₀ : ContactCoords}
    (hηf : η₀.1 ∈ Uf) (hηo : η₀.2.1 ∈ Uo)
    (hX : IsUnit (relativeCurvature (curvatureTensor cf η₀.1) (curvatureTensor co η₀.2.1)
      η₀.2.2).det) :
    ∃ N ∈ 𝓝 η₀, ∃ Ψ : PoseCoords → ContactCoords,
      ContDiffAt ℝ 1 Ψ (poseCoords (relativePoseMap cf co η₀)) ∧
      Set.MapsTo (relativePoseMap cf co) N (contactSet cf co Uf Uo) ∧
      Set.InjOn (relativePoseMap cf co) N ∧
      ∀ η ∈ N, Ψ (poseCoords (relativePoseMap cf co η)) = η := by
  have h2f : ContDiffOn ℝ (1 + 1) cf Uf := by rw [one_add_one_eq_two]; exact hf.contDiffOn
  have h2o : ContDiffOn ℝ (1 + 1) co Uo := by rw [one_add_one_eq_two]; exact ho.contDiffOn
  exact exists_local_inverse_relativePoseMap le_rfl hf ho h2f h2o hηf hηo hX

end Rolling
end RoboLean
