import RoboLean.Dynamics.PseudoInverse
import RoboLean.Kinematics.MapJacobian
import RoboLean.Grasp.Frictionless
import RoboLean.Grasp.PositiveSpanBounds
import RoboLean.Grasp.Steinitz

/-!
# Kinematics and statics of tendon actuation (MLS Chapter 6, §4, eqs. (6.34)–(6.35))

MLS Chapter 6, §4, printed pp. 293–300 (renders inspected this session).

**Setting (MLS pp. 294–295).** A finger with joint angles `θ ∈ ℝⁿ` is driven by `p` tendons. The
routing of tendon `i` is an extension function `hᵢ : ℝⁿ → ℝ` (`h : ℝⁿ → ℝᵖ`); the coupling matrix is
`P(θ) = (∂h/∂θ)ᵀ ∈ ℝ^{n×p}` (`couplingMatrix`, with `∂h/∂θ = MapJacobian.jac h θ`), so that
`ė = Pᵀ(θ) θ̇` along a motion (`hasDerivAt_extension`). "Since the work done by the tendons must
equal that done by the fingers ... we can use conservation of energy to conclude `τ = P(θ) f`" (p.
295): as for (5.16) in E028, the energy argument is a premise of the model and is not derived; only
the power identity `(P f) ⬝ θ̇ = f ⬝ (Pᵀ θ̇)` (`dotProduct_tendonTorque`) and its uniqueness step
(`eq_mulVec_of_forall_dotProduct`) are formalized.

**Elastic tendons (p. 297).** `f = K (e + h(0) − h(θ))` (`elasticForce`), the stiffness
`S(θ) = P K (h(θ) − h(0))` (`tendonStiffness`) and the coupling `Q = P K`; the dynamics
`M θ̈ + C θ̇ + N = P f` become `M θ̈ + C θ̇ + N + S(θ) = Q e` (`elastic_dynamics_iff`; p. 297 prints
`M(θ) + C θ̇ + …` without the `θ̈`).

**Force-closure (6.34), p. 299.** `IsTendonForceClosure P`: every `τ` is `P f` with all `fᵢ > 0`. It
is positive spanning by the columns of `P` (p. 225; "analogous to grasping using frictionless point
contacts", p. 299), and it holds exactly when `P` is onto and some `f_N` with all `f_{N,i} > 0` has
`P f_N = 0` (`isTendonForceClosure_iff`, the orthant-cone case of Proposition 5.2, G09). The counts:
at least `n + 1` tendons (`IsTendonForceClosure.succ_le_card`, Theorem 5.4, G28) and a force-closure
subnetwork of at most `2n` tendons (`IsTendonForceClosure.exists_card_le`, Steinitz's theorem, G38),
both for `n ≥ 1` (the hypothesis G28 and G38 add). The tensions `f = P⁺ τ + f_N`
(`P⁺ = Pᵀ (P Pᵀ)⁻¹`, `rightPinv`) are positive for a suitable `f_N ∈ N(P)`
(`IsTendonForceClosure.exists_rightPinv_add`), and the position-controlled case (6.35) is solved by
`e = (P K)⁺ τ + c e_N` for large `c` (`IsTendonForceClosure.exists_extension`), for a diagonal
stiffness matrix with positive entries (p. 297; the printed reason "since `K` is invertible" does
not suffice, see the E037 source observations).

Nothing here models friction, tendon or actuator dynamics, slack tendons or limits on the forces.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Composite

variable {n p : ℕ}

/-! ### Extension functions and the coupling matrix (MLS pp. 294–295) -/

/-- **The coupling matrix `P(θ) = (∂h/∂θ)ᵀ(θ) ∈ ℝ^{n×p}` of a tendon network (MLS printed p. 295)**
for the extension functions `h = (h₁, …, h_p) : ℝⁿ → ℝᵖ` (p. 294); `∂h/∂θ` is `MapJacobian.jac h θ`
(column `j` is the derivative along `θⱼ`). Column `i` of `P` holds the joint torques produced by a
unit tension in tendon `i`. -/
def couplingMatrix (h : (Fin n → ℝ) → Fin p → ℝ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  (MapJacobian.jac h θ)ᵀ

/-- **MLS printed p. 295: `ė = (∂h/∂θ)(θ) θ̇ = Pᵀ(θ) θ̇`.** Along a motion `θ` with velocity `θ'` at
`t`, with `h` differentiable at `θ(t)`, the tendon extensions `e = h(θ)` have the rate
`Pᵀ(θ(t)) θ'`. -/
theorem hasDerivAt_extension {h : (Fin n → ℝ) → Fin p → ℝ} {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hh : DifferentiableAt ℝ h (θ t)) (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => h (θ s)) ((couplingMatrix h (θ t))ᵀ *ᵥ θ') t := by
  rw [couplingMatrix, Matrix.transpose_transpose]
  exact MapJacobian.hasDerivAt_comp hh hθ

/-- **Pulley networks (MLS printed p. 294): for linear extension functions
`hᵢ(θ) = lᵢ ± rᵢ₁ θ₁ ± ⋯ ± rᵢₙ θₙ`**, written `h(θ) = l + R θ` with the signed radii `R ∈ ℝ^{p×n}`,
the coupling matrix is the constant `Rᵀ`. -/
theorem couplingMatrix_affine (l : Fin p → ℝ) (R : Matrix (Fin p) (Fin n) ℝ) (θ : Fin n → ℝ) :
    couplingMatrix (fun q => l + R *ᵥ q) θ = Rᵀ := by
  have h : MapJacobian.jac (fun q => l + R *ᵥ q) θ = MapJacobian.jac (fun q => R *ᵥ q) θ := by
    ext i j
    simp only [MapJacobian.jac, Matrix.of_apply, fderiv_const_add]
  rw [couplingMatrix, h, MapJacobian.jac_linear]

/-- **The power identity behind `τ = P(θ) f` (MLS printed p. 295, "the work done by the tendons must
equal that done by the fingers"):** the joint power of `τ = P f` equals the tendon power `f ⬝ ė`
with `ė = Pᵀ θ̇`. The book's conservation-of-energy argument is a premise and is not derived. -/
theorem dotProduct_tendonTorque (P : Matrix (Fin n) (Fin p) ℝ) (f : Fin p → ℝ)
    (θ' : Fin n → ℝ) : (P *ᵥ f) ⬝ᵥ θ' = f ⬝ᵥ (Pᵀ *ᵥ θ') := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- **Uniqueness in "`τ = P(θ) f`" (MLS printed p. 295):** if the joint power `τ ⬝ θ̇` equals the
tendon power `f ⬝ (Pᵀ θ̇)` for every joint velocity `θ̇`, then `τ = P f`. -/
theorem eq_mulVec_of_forall_dotProduct {P : Matrix (Fin n) (Fin p) ℝ} {τ : Fin n → ℝ}
    {f : Fin p → ℝ} (h : ∀ θ' : Fin n → ℝ, τ ⬝ᵥ θ' = f ⬝ᵥ (Pᵀ *ᵥ θ')) : τ = P *ᵥ f := by
  funext i
  have hi := h (Pi.single i 1)
  rw [← dotProduct_tendonTorque, dotProduct_single, dotProduct_single] at hi
  simpa using hi

/-! ### Elastic tendons (MLS p. 297) -/

/-- **The tendon forces of an elastic network (MLS printed p. 297):** `f = K (e + h(0) − h(θ))`,
with `K` the matrix of tendon stiffnesses (diagonal in the book), `e` the commanded extensions and
`h(θ)` the extensions due to the mechanism ("when `θ = 0` and `eᵢ = 0` the tendon is under zero
tension"). -/
def elasticForce (K : Matrix (Fin p) (Fin p) ℝ) (h : (Fin n → ℝ) → Fin p → ℝ) (e : Fin p → ℝ)
    (θ : Fin n → ℝ) : Fin p → ℝ :=
  K *ᵥ (e + h 0 - h θ)

/-- **The stiffness of an elastic tendon network (MLS printed p. 297):**
`S(θ) := P K (h(θ) − h(0))`, for the coupling matrix `P` at `θ`. -/
def tendonStiffness (P : Matrix (Fin n) (Fin p) ℝ) (K : Matrix (Fin p) (Fin p) ℝ)
    (h : (Fin n → ℝ) → Fin p → ℝ) (θ : Fin n → ℝ) : Fin n → ℝ :=
  (P * K) *ᵥ (h θ - h 0)

/-- **MLS printed p. 297: the dynamics with elastic tendons.** At a configuration `θ` with coupling
matrix `P`, `M θ̈ + C θ̇ + N = P f` with the elastic forces `f = K (e + h(0) − h(θ))` holds exactly
when `M θ̈ + C θ̇ + N + S(θ) = Q e`, `S(θ) = P K (h(θ) − h(0))`, `Q = P K` (the book prints
`M(θ) + C θ̇ + …`, without `θ̈`). -/
theorem elastic_dynamics_iff (M C : Matrix (Fin n) (Fin n) ℝ) (N θ' θ'' : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin p) ℝ) (K : Matrix (Fin p) (Fin p) ℝ) (h : (Fin n → ℝ) → Fin p → ℝ)
    (e : Fin p → ℝ) (θ : Fin n → ℝ) :
    M *ᵥ θ'' + C *ᵥ θ' + N = P *ᵥ elasticForce K h e θ ↔
      M *ᵥ θ'' + C *ᵥ θ' + N + tendonStiffness P K h θ = (P * K) *ᵥ e := by
  have h1 : P *ᵥ elasticForce K h e θ = (P * K) *ᵥ e - tendonStiffness P K h θ := by
    rw [elasticForce, tendonStiffness, Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]
    congr 1
    abel
  rw [h1, eq_sub_iff_add_eq]

/-! ### Force-closure of a tendon network, eq. (6.34) (MLS p. 299) -/

/-- **Force-closure of a tendon network, MLS eq. (6.34), printed p. 299:** for every joint torque
`τ ∈ ℝⁿ` there are tendon forces `f` with `P f = τ` and every tension `fᵢ > 0` (strictly, as
printed). The tendons are indexed by a finite type `ι` (the book's `1, …, p`). -/
def IsTendonForceClosure {ι : Type*} [Fintype ι] (P : Matrix (Fin n) ι ℝ) : Prop :=
  ∀ τ : Fin n → ℝ, ∃ f : ι → ℝ, P *ᵥ f = τ ∧ ∀ i, 0 < f i

/-- `P f` is the combination `∑ fᵢ Pᵢ` of the columns of `P`. -/
private theorem mulVec_eq_sum_col {ι : Type*} [Fintype ι] (P : Matrix (Fin n) ι ℝ) (f : ι → ℝ) :
    P *ᵥ f = ∑ i, f i • P.col i := by
  funext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **MLS printed p. 299: "This is analogous to grasping using frictionless point contacts".** A
tendon network is force-closure (6.34) exactly when the columns of `P` positively span `ℝⁿ` in the
sense of MLS p. 225 (strictly positive coefficients). -/
theorem isTendonForceClosure_iff_positivelySpans {ι : Type*} [Fintype ι]
    (P : Matrix (Fin n) ι ℝ) : IsTendonForceClosure P ↔ Grasp.PositivelySpans P.col := by
  simp only [IsTendonForceClosure, Grasp.PositivelySpans, mulVec_eq_sum_col]
  exact forall_congr' fun τ => exists_congr fun f => and_comm

/-- For `g` and a strictly positive `w`, `gᵢ + c wᵢ > 0` for every `i` once `c` is large. -/
private theorem exists_forall_pos_add_mul {ι : Type*} [Fintype ι] (g : ι → ℝ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) : ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → ∀ i, 0 < g i + c * w i := by
  refine ⟨∑ j, (|g j| + 1) / w j, fun c hc i => ?_⟩
  have h1 : (|g i| + 1) / w i ≤ ∑ j, (|g j| + 1) / w j :=
    Finset.single_le_sum (f := fun j => (|g j| + 1) / w j)
      (fun j _ => div_nonneg (by positivity) (hw j).le) (Finset.mem_univ i)
  have h2 : w i * ((|g i| + 1) / w i) = |g i| + 1 := mul_div_cancel₀ _ (hw i).ne'
  have h3 : w i * ((|g i| + 1) / w i) ≤ w i * c :=
    mul_le_mul_of_nonneg_left (h1.trans hc) (hw i).le
  have h4 := neg_abs_le (g i)
  nlinarith

/-- **MLS printed p. 299: "a necessary and sufficient condition for a tendon network to be
force-closure is that `P(θ)` be surjective and there exist a strictly positive vector of internal
forces `f_N`, `f_{N,i} > 0` such that `P(θ) f_N = 0`"** (Proposition 5.2, G09, for the orthant
cone). -/
theorem isTendonForceClosure_iff {ι : Type*} [Fintype ι] (P : Matrix (Fin n) ι ℝ) :
    IsTendonForceClosure P ↔
      Function.Surjective P.mulVec ∧ ∃ fN : ι → ℝ, (∀ i, 0 < fN i) ∧ P *ᵥ fN = 0 := by
  constructor
  · intro h
    refine ⟨fun τ => ?_, ?_⟩
    · obtain ⟨f, hf, -⟩ := h τ
      exact ⟨f, hf⟩
    · obtain ⟨f, hf, hpos⟩ := h 0
      exact ⟨f, hpos, hf⟩
  · rintro ⟨hsurj, fN, hpos, hN⟩ τ
    obtain ⟨f₀, hf₀⟩ := hsurj τ
    obtain ⟨c₀, hc⟩ := exists_forall_pos_add_mul f₀ hpos
    refine ⟨f₀ + c₀ • fN, ?_, fun i => ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hN, smul_zero, add_zero]
      exact hf₀
    · simpa using hc c₀ le_rfl i

/-- **MLS printed p. 299, Carathéodory's count (Theorem 5.4, G28): "for a robot with `n` links, at
least `n + 1` tendons are required to actuate it"**, for `n ≥ 1` (the hypothesis G28 adds; with
`n = 0` a network without tendons is force-closure). -/
theorem IsTendonForceClosure.succ_le_card {ι : Type*} [Fintype ι] {P : Matrix (Fin n) ι ℝ}
    (h : IsTendonForceClosure P) (hn : 1 ≤ n) : n + 1 ≤ Fintype.card ι := by
  have hs := (isTendonForceClosure_iff_positivelySpans P).mp h
  simpa using hs.finrank_succ_le_card (by rw [Module.finrank_fin_fun]; omega)

/-- **MLS printed p. 299, Steinitz's count (Theorem 5.5, G38): "any more than `2n` tendons are
redundant"**: for `n ≥ 1`, a force-closure tendon network has a force-closure subnetwork of at most
`2n` of its tendons (the columns of `P` indexed by `s`). -/
theorem IsTendonForceClosure.exists_card_le {ι : Type*} [Fintype ι] {P : Matrix (Fin n) ι ℝ}
    (h : IsTendonForceClosure P) (hn : 1 ≤ n) :
    ∃ s : Finset ι, s.card ≤ 2 * n ∧ IsTendonForceClosure (P.submatrix id ((↑) : s → ι)) := by
  classical
  have hs := (isTendonForceClosure_iff_positivelySpans P).mp h
  have hne : Nonempty ι := by
    have hc := h.succ_le_card hn
    exact Fintype.card_pos_iff.mp (by omega)
  have h0 : (0 : Fin n → ℝ) ∈ interior (convexHull ℝ (Set.range P.col)) :=
    mem_interior_iff_mem_nhds.mpr ((Grasp.positivelySpans_iff_convexHull_mem_nhds _).mp hs)
  obtain ⟨X, hXS, hXcard, hX0⟩ :=
    Grasp.exists_finset_mem_interior_convexHull_card_le_two_mul_fin h0 hn
  have hpre : ∀ x ∈ X, ∃ i, P.col i = x := fun x hx => hXS hx
  choose g hg using hpre
  refine ⟨X.attach.image fun x => g x.1 x.2, ?_, ?_⟩
  · exact Finset.card_image_le.trans (Finset.card_attach.le.trans hXcard)
  have hrange : Set.range (P.submatrix id ((↑) : (X.attach.image fun x => g x.1 x.2) → ι)).col =
      (X : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hi
      change P.col (g x.1 x.2) ∈ (X : Set (Fin n → ℝ))
      rw [hg]
      exact x.2
    · intro hy
      exact ⟨⟨g y hy, Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩⟩, hg y hy⟩
  have hXne : (X.attach.image fun x => g x.1 x.2).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.image_eq_empty, Finset.attach_eq_empty_iff]
      at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty, interior_empty] at hX0
    exact hX0
  have : Nonempty (X.attach.image fun x => g x.1 x.2) := hXne.to_subtype
  rw [isTendonForceClosure_iff_positivelySpans, Grasp.positivelySpans_iff_convexHull_mem_nhds,
    hrange]
  exact mem_interior_iff_mem_nhds.mp hX0

/-- **MLS printed p. 299: "the tendon forces chosen to exert a given vector of joint torques have
the form `f = P⁺(θ) τ + f_N`, where ... `f_N ∈ N(P)` ... is an internal force that insures that all
tendon tensions are positive"**: for a force-closure network and every `τ` there is `f_N` with
`P f_N = 0` and `f_N > 0` such that `f = P⁺ τ + f_N` has every `fᵢ > 0` and `P f = τ`. -/
theorem IsTendonForceClosure.exists_rightPinv_add {P : Matrix (Fin n) (Fin p) ℝ}
    (h : IsTendonForceClosure P) (τ : Fin n → ℝ) :
    ∃ fN : Fin p → ℝ, P *ᵥ fN = 0 ∧ (∀ i, 0 < fN i) ∧
      (∀ i, 0 < (rightPinv P *ᵥ τ + fN) i) ∧ P *ᵥ (rightPinv P *ᵥ τ + fN) = τ := by
  obtain ⟨hsurj, fN, hpos, hN⟩ := (isTendonForceClosure_iff P).mp h
  obtain ⟨c₀, hc⟩ := exists_forall_pos_add_mul (rightPinv P *ᵥ τ) hpos
  have hc1 : 0 < max c₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max c₀ 1 • fN, ?_, fun i => ?_, fun i => ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hN, smul_zero]
  · simpa using mul_pos hc1 (hpos i)
  · simpa using hc (max c₀ 1) (le_max_left _ _) i
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hN, smul_zero, add_zero,
      mulVec_rightPinv_mulVec hsurj]

/-- Scaling the tendons by a positive diagonal stiffness keeps force-closure: `P K` is force-closure
when `P` is and `K = diag(k)` with every `kᵢ > 0`. -/
private theorem isTendonForceClosure_mul_diagonal {P : Matrix (Fin n) (Fin p) ℝ}
    (h : IsTendonForceClosure P) {k : Fin p → ℝ} (hk : ∀ i, 0 < k i) :
    IsTendonForceClosure (P * Matrix.diagonal k) := by
  intro τ
  obtain ⟨f, hf, hpos⟩ := h τ
  refine ⟨fun i => f i / k i, ?_, fun i => div_pos (hpos i) (hk i)⟩
  have hd : Matrix.diagonal k *ᵥ (fun i => f i / k i) = f := by
    funext i
    rw [Matrix.mulVec_diagonal]
    exact mul_div_cancel₀ _ (hk i).ne'
  rw [← Matrix.mulVec_mulVec, hd, hf]

/-- **MLS eq. (6.35), printed p. 299, the internal extensions:** for a force-closure network and the
diagonal stiffness matrix `K = diag(k)` with every `kᵢ > 0` (p. 297), there is `e_N` with every
`e_{N,i} > 0` and `P K e_N = 0`. -/
theorem IsTendonForceClosure.exists_extension_null {P : Matrix (Fin n) (Fin p) ℝ}
    (h : IsTendonForceClosure P) {k : Fin p → ℝ} (hk : ∀ i, 0 < k i) :
    ∃ eN : Fin p → ℝ, (∀ i, 0 < eN i) ∧ (P * Matrix.diagonal k) *ᵥ eN = 0 := by
  obtain ⟨-, eN, hpos, hN⟩ :=
    (isTendonForceClosure_iff _).mp (isTendonForceClosure_mul_diagonal h hk)
  exact ⟨eN, hpos, hN⟩

/-- **MLS eq. (6.35), printed pp. 299–300: "By choosing `e = (P K)⁺ τ + e_N` with `e_N` sufficiently
large in magnitude, we can insure that the constraints in equation (6.35) are satisfied."** For a
force-closure network, the diagonal stiffness `K = diag(k)` with every `kᵢ > 0`, every `τ` and every
offset vector `d` (the book's `h(0) − h(θ)`), there are `e_N > 0` with `P K e_N = 0` and `c₀` such
that for every `c ≥ c₀`, `e = (P K)⁺ τ + c e_N` solves `P K e = τ` and `eᵢ + dᵢ > 0` for every `i`.
-/
theorem IsTendonForceClosure.exists_extension {P : Matrix (Fin n) (Fin p) ℝ}
    (h : IsTendonForceClosure P) {k : Fin p → ℝ} (hk : ∀ i, 0 < k i) (τ : Fin n → ℝ)
    (d : Fin p → ℝ) :
    ∃ eN : Fin p → ℝ, (∀ i, 0 < eN i) ∧ (P * Matrix.diagonal k) *ᵥ eN = 0 ∧
      ∃ c₀ : ℝ, ∀ c, c₀ ≤ c →
        (P * Matrix.diagonal k) *ᵥ (rightPinv (P * Matrix.diagonal k) *ᵥ τ + c • eN) = τ ∧
          ∀ i, 0 < (rightPinv (P * Matrix.diagonal k) *ᵥ τ + c • eN) i + d i := by
  obtain ⟨hsurj, eN, hpos, hN⟩ :=
    (isTendonForceClosure_iff _).mp (isTendonForceClosure_mul_diagonal h hk)
  obtain ⟨c₀, hc⟩ := exists_forall_pos_add_mul (rightPinv (P * Matrix.diagonal k) *ᵥ τ + d) hpos
  refine ⟨eN, hpos, hN, c₀, fun c hcc => ⟨?_, fun i => ?_⟩⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hN, smul_zero, add_zero,
      mulVec_rightPinv_mulVec hsurj]
  · have hi := hc c hcc i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linarith

end Composite
end RoboLean
