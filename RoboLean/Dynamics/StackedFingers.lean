import RoboLean.Dynamics.CompositeDynamics

/-!
# Stacked finger dynamics, eq. (6.16) (MLS Chapter 6, §2.1)

MLS Chapter 6, §2.1, printed p. 276, eq. (6.16).

**What MLS states.** "the finger dynamics have the form
`M_f(θ) θ̈ + C_f(θ, θ̇) θ̇ + N_f(θ, θ̇) = τ`, where `θ = (θ_{f₁}, …, θ_{f_k}) ∈ ℝⁿ` is the vector of
joint angles for all of the fingers in the hand and `τ ∈ ℝⁿ` is the corresponding vector of joint
torques. `M_f`, `C_f`, and `N_f` are formed by appropriately stacking the quantities obtained for
the individual fingers": `M_f` and `C_f` block diagonal, `N_f` stacked.

**Formalized.** Fingers are indexed by a finite type `ι`, finger `i` has `n i` joints, and the
stacked joint vector is `θ ∈ ℝᴺ` with the relabeling `e : (Σ i, Fin (n i)) ≃ Fin N` (the carrier of
`CompositeDynamics`; `θ_{fᵢ} = fingerCoords e θ i`).

* `stackMat` (block diagonal, `Matrix.blockDiagonal'`) and `stackVec`; (6.16) for the stacked
  quantities holds exactly when every finger's equation holds (`stacked_dynamics_iff`).
* The structural properties: the stacked inertia is symmetric, positive definite when every block is
  (`stackMat_isSymm`, `stackMat_posDef`), and `Ṁ_f − 2C_f` is skew when every finger's is
  (`skew_stackMat_sub_two`; along a motion `skew_deriv_stackField_sub_two`).
* The Christoffel matrix (MLS eq. (4.23)) of the stacked inertia field
  `θ ↦ blockdiag(M_{fᵢ}(θ_{fᵢ}))` is the block diagonal of the fingers' Christoffel matrices
  (`coriolisMatrix_stackPartials`, with the stacked Fréchet data of `hasFDerivAt_stackField`), and
  Lagrange's equations of the hand's mechanical Lagrangian are the stacked finger equations (6.16)
  (`lagrangeEquationsAt_stack_iff`): the hand's `C_f` is "formed by appropriately stacking" the
  fingers' `C_{fᵢ}`.

Hypotheses as in `Dynamics/Lagrangian`: symmetric inertia fields with Fréchet derivative data at the
configuration, actual velocity and acceleration of the motion. Nothing here models couplings between
fingers other than through the object (none in (6.16)).
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Composite

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {N : ℕ}

/-- **The joint angles `θ_{fᵢ}` of finger `i` in the stacked vector `θ = (θ_{f₁}, …, θ_{f_k})` (MLS
printed p. 276)**, with the stacked coordinates relabeled by `e`. -/
def fingerCoords (e : (Σ i, Fin (n i)) ≃ Fin N) (θ : Fin N → ℝ) (i : ι) : Fin (n i) → ℝ :=
  fun a => θ (e ⟨i, a⟩)

/-- **The projection `θ ↦ θ_{fᵢ}` as a continuous linear map (MLS p. 276).** -/
def fingerProj (e : (Σ i, Fin (n i)) ≃ Fin N) (i : ι) : (Fin N → ℝ) →L[ℝ] (Fin (n i) → ℝ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (e ⟨i, a⟩)

omit [Fintype ι] [DecidableEq ι] in
/-- `fingerProj e i θ = θ_{fᵢ}` (MLS p. 276). -/
@[simp] theorem fingerProj_apply (e : (Σ i, Fin (n i)) ≃ Fin N) (i : ι) (θ : Fin N → ℝ) :
    fingerProj e i θ = fingerCoords e θ i :=
  rfl

/-- **Stacking per-finger vectors (MLS printed p. 276, `N_f = (N_{f₁}, …, N_{f_k})`).** -/
def stackVec (e : (Σ i, Fin (n i)) ≃ Fin N) (v : (i : ι) → Fin (n i) → ℝ) : Fin N → ℝ :=
  fun j => v (e.symm j).1 (e.symm j).2

/-- **Block-diagonal stacking of per-finger matrices (MLS printed p. 276,
`M_f = diag(M_{f₁}, …, M_{f_k})`, `C_f = diag(C_{f₁}, …, C_{f_k})`).** -/
def stackMat (e : (Σ i, Fin (n i)) ≃ Fin N) (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (Matrix.blockDiagonal' A).submatrix e.symm e.symm

omit [Fintype ι] [DecidableEq ι] in
/-- The stacked vector at the relabeled joint `e (i, a)` is finger `i`'s entry `a` (MLS p. 276). -/
private theorem stackVec_apply_e (e : (Σ i, Fin (n i)) ≃ Fin N) (v : (i : ι) → Fin (n i) → ℝ)
    (p : Σ i, Fin (n i)) : stackVec e v (e p) = v p.1 p.2 :=
  congrArg (fun r : (Σ i, Fin (n i)) => v r.1 r.2) (e.symm_apply_apply p)

omit [Fintype ι] [DecidableEq ι] in
/-- The fingers' parts of a stacked vector are the stacked parts (MLS p. 276). -/
@[simp] theorem fingerCoords_stackVec (e : (Σ i, Fin (n i)) ≃ Fin N)
    (v : (i : ι) → Fin (n i) → ℝ) (i : ι) : fingerCoords e (stackVec e v) i = v i := by
  funext a
  exact stackVec_apply_e e v ⟨i, a⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A vector is the stack of its fingers' parts (MLS p. 276, `θ = (θ_{f₁}, …, θ_{f_k})`). -/
theorem stackVec_fingerCoords (e : (Σ i, Fin (n i)) ≃ Fin N) (θ : Fin N → ℝ) :
    stackVec e (fingerCoords e θ) = θ := by
  funext j
  simp [stackVec, fingerCoords]

/-- A block-diagonal matrix over the stacked index acts block by block (MLS p. 276). -/
private theorem blockDiagonal'_mulVec_apply (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ)
    (w : (Σ i, Fin (n i)) → ℝ) (i : ι) (a : Fin (n i)) :
    (Matrix.blockDiagonal' A *ᵥ w) ⟨i, a⟩ = (A i *ᵥ fun b => w ⟨i, b⟩) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c _ hc
    exact Finset.sum_eq_zero fun b _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hc), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **A block-diagonal matrix acts finger by finger (MLS p. 276).** -/
theorem stackMat_mulVec (e : (Σ i, Fin (n i)) ≃ Fin N)
    (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) (v : Fin N → ℝ) :
    stackMat e A *ᵥ v = stackVec e fun i => A i *ᵥ fingerCoords e v i := by
  funext j
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  rw [stackVec_apply_e, stackMat, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm]
  rw [blockDiagonal'_mulVec_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A stacked vector equals `τ` exactly when every finger's part equals `τ_{fᵢ}` (MLS p. 276). -/
private theorem stackVec_eq_iff (e : (Σ i, Fin (n i)) ≃ Fin N) (F : (i : ι) → Fin (n i) → ℝ)
    (τ : Fin N → ℝ) : stackVec e F = τ ↔ ∀ i, F i = fingerCoords e τ i := by
  constructor
  · rintro rfl i
    rw [fingerCoords_stackVec]
  · intro h
    rw [← stackVec_fingerCoords e τ]
    congr 1
    funext i
    exact h i

/-- **MLS eq. (6.16), printed p. 276: the stacked finger dynamics.** With `M_f = diag(M_{fᵢ})`,
`C_f = diag(C_{fᵢ})` and `N_f = (N_{fᵢ})`, the hand equation `M_f θ̈ + C_f θ̇ + N_f = τ` holds
exactly when every finger's equation `M_{fᵢ} θ̈_{fᵢ} + C_{fᵢ} θ̇_{fᵢ} + N_{fᵢ} = τ_{fᵢ}` holds. -/
theorem stacked_dynamics_iff (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M C : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) (Nf : (i : ι) → Fin (n i) → ℝ)
    (θ' θ'' τ : Fin N → ℝ) :
    stackMat e M *ᵥ θ'' + stackMat e C *ᵥ θ' + stackVec e Nf = τ ↔
      ∀ i, M i *ᵥ fingerCoords e θ'' i + C i *ᵥ fingerCoords e θ' i + Nf i =
        fingerCoords e τ i := by
  rw [stackMat_mulVec, stackMat_mulVec]
  exact stackVec_eq_iff e
    (fun i => M i *ᵥ fingerCoords e θ'' i + C i *ᵥ fingerCoords e θ' i + Nf i) τ

omit [Fintype ι] in
/-- The transpose of a stacked matrix is the stack of the transposes (MLS p. 276). -/
private theorem stackMat_transpose (e : (Σ i, Fin (n i)) ≃ Fin N)
    (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) :
    (stackMat e A)ᵀ = stackMat e fun i => (A i)ᵀ := by
  rw [stackMat, stackMat, Matrix.transpose_submatrix, Matrix.blockDiagonal'_transpose]

omit [Fintype ι] in
/-- **The stacked inertia is symmetric when every finger's is (MLS p. 276 with Lemma 4.2(1)).** -/
theorem stackMat_isSymm (e : (Σ i, Fin (n i)) ≃ Fin N)
    {A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ} (h : ∀ i, (A i).IsSymm) :
    (stackMat e A).IsSymm := by
  rw [Matrix.IsSymm, stackMat_transpose]
  congr 1
  funext i
  exact h i

omit [DecidableEq ι] in
/-- The dot product with a stacked vector is the sum over the fingers (MLS p. 276). -/
private theorem dotProduct_stackVec (e : (Σ i, Fin (n i)) ≃ Fin N) (x : Fin N → ℝ)
    (F : (i : ι) → Fin (n i) → ℝ) :
    x ⬝ᵥ stackVec e F = ∑ i, fingerCoords e x i ⬝ᵥ F i := by
  simp only [dotProduct]
  conv_lhs => rw [← Equiv.sum_comp e, Fintype.sum_sigma]
  simp only [stackVec_apply_e, fingerCoords]

/-- **The stacked inertia is positive definite when every finger's is (MLS p. 276 with Lemma 4.2(1),
p. 171).** -/
theorem stackMat_posDef (e : (Σ i, Fin (n i)) ≃ Fin N)
    {A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ} (h : ∀ i, (A i).PosDef) :
    (stackMat e A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr
      (stackMat_isSymm e fun i => Matrix.isHermitian_iff_isSymm.mp (h i).isHermitian))
    fun x hx => ?_
  rw [star_trivial, stackMat_mulVec, dotProduct_stackVec]
  have hpos : ∀ i, fingerCoords e x i ≠ 0 →
      0 < fingerCoords e x i ⬝ᵥ (A i *ᵥ fingerCoords e x i) := fun i hi => by
    simpa only [star_trivial] using (h i).dotProduct_mulVec_pos hi
  have hne : ∃ i, fingerCoords e x i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hx
    rw [← stackVec_fingerCoords e x]
    funext j
    simp [stackVec, hcon]
  obtain ⟨i, hi⟩ := hne
  refine Finset.sum_pos' (fun c _ => ?_) ⟨i, Finset.mem_univ i, hpos i hi⟩
  by_cases hc : fingerCoords e x c = 0
  · simp [hc]
  · exact (hpos c hc).le

omit [Fintype ι] in
/-- Stacking commutes with `A − c B` (MLS p. 276). -/
private theorem stackMat_sub_smul (e : (Σ i, Fin (n i)) ≃ Fin N)
    (A B : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) (c : ℝ) :
    stackMat e A - c • stackMat e B = stackMat e fun i => A i - c • B i := by
  change _ = (Matrix.blockDiagonal' (A - c • B)).submatrix e.symm e.symm
  rw [Matrix.blockDiagonal'_sub, Matrix.blockDiagonal'_smul]
  rfl

omit [Fintype ι] in
/-- Stacking commutes with negation (MLS p. 276). -/
private theorem stackMat_neg (e : (Σ i, Fin (n i)) ≃ Fin N)
    (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) :
    -stackMat e A = stackMat e fun i => -A i := by
  change _ = (Matrix.blockDiagonal' (-A)).submatrix e.symm e.symm
  rw [Matrix.blockDiagonal'_neg]
  rfl

omit [Fintype ι] in
/-- **`Ṁ_f − 2C_f` is skew when every finger's `Ṁ_{fᵢ} − 2C_{fᵢ}` is (MLS p. 276 with Lemma 4.2(2),
p. 171; the "usual structural properties" of the fingers, p. 283).** -/
theorem skew_stackMat_sub_two (e : (Σ i, Fin (n i)) ≃ Fin N)
    {Md C : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ}
    (h : ∀ i, (Md i - (2 : ℝ) • C i)ᵀ = -(Md i - (2 : ℝ) • C i)) :
    (stackMat e Md - (2 : ℝ) • stackMat e C)ᵀ = -(stackMat e Md - (2 : ℝ) • stackMat e C) := by
  rw [stackMat_sub_smul, stackMat_transpose, stackMat_neg]
  congr 1
  funext i
  exact h i

/-! ### The stacked inertia field and its Christoffel matrix -/

/-- **The hand's inertia field `M_f(θ) = diag(M_{f₁}(θ_{f₁}), …, M_{f_k}(θ_{f_k}))` (MLS printed p.
276)**, each finger's inertia depending only on its own joints. -/
def stackField (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M : (i : ι) → (Fin (n i) → ℝ) → Matrix (Fin (n i)) (Fin (n i)) ℝ) :
    (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ :=
  fun θ => stackMat e fun i => M i (fingerCoords e θ i)

/-- **The Fréchet derivative data of the stacked inertia field (MLS p. 276 with p. 170):** entry
`(j, l)` in the block of finger `i` is the finger's derivative composed with `θ ↦ θ_{fᵢ}`; entries
outside the diagonal blocks are `0`. -/
def stackPartials (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ)) :
    Fin N → Fin N → ((Fin N → ℝ) →L[ℝ] ℝ) :=
  fun j l => (Matrix.blockDiagonal' fun i => Matrix.of fun a b => (M' i a b).comp (fingerProj e i))
    (e.symm j) (e.symm l)

omit [Fintype ι] in
/-- **The stacked inertia field has the stacked Fréchet data (MLS p. 276)** at `θ`, when every
finger's inertia field has the data `M'ᵢ` at `θ_{fᵢ}`. -/
theorem hasFDerivAt_stackField (e : (Σ i, Fin (n i)) ≃ Fin N)
    {M : (i : ι) → (Fin (n i) → ℝ) → Matrix (Fin (n i)) (Fin (n i)) ℝ}
    {M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ)} {θ : Fin N → ℝ}
    (hM : ∀ i a b, HasFDerivAt (fun y => M i y a b) (M' i a b) (fingerCoords e θ i))
    (j l : Fin N) :
    HasFDerivAt (fun y => stackField e M y j l) (stackPartials e M' j l) θ := by
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective l
  simp only [stackField, stackPartials, stackMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases eq_or_ne i k with rfl | hik
  · simp only [Matrix.blockDiagonal'_apply_eq, Matrix.of_apply]
    exact (hM i a b).comp θ (fingerProj e i).hasFDerivAt
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hik]
    exact hasFDerivAt_const 0 θ

omit [Fintype ι] [DecidableEq ι] in
/-- The finger-`i` part of the unit vector of joint `(i, a)` is the unit vector of `a` (MLS p. 276).
-/
private theorem fingerProj_single_self (e : (Σ i, Fin (n i)) ≃ Fin N) (i : ι) (a : Fin (n i)) :
    fingerProj e i (Pi.single (e ⟨i, a⟩) 1) = Pi.single a 1 := by
  funext b
  simp [fingerCoords, Pi.single_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- The finger-`i` part of the unit vector of a joint of another finger is zero (MLS p. 276). -/
private theorem fingerProj_single_ne (e : (Σ i, Fin (n i)) ≃ Fin N) {i c : ι} (h : c ≠ i)
    (d : Fin (n c)) : fingerProj e i (Pi.single (e ⟨c, d⟩) 1) = 0 := by
  funext b
  simp [fingerCoords, Ne.symm h]

omit [Fintype ι] in
/-- The stacked partial `∂M_{pq}/∂θ_r` vanishes unless `p`, `q`, `r` lie in one finger (MLS p. 276
with eq. (4.22), p. 170). -/
private theorem partials_stackPartials_eq_zero (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ))
    {p q r : Σ i, Fin (n i)} (h : p.1 ≠ q.1 ∨ r.1 ≠ p.1) :
    Christoffel.partials (stackPartials e M') (e r) (e p) (e q) = 0 := by
  obtain ⟨i, a⟩ := p
  obtain ⟨k, b⟩ := q
  obtain ⟨c, d⟩ := r
  simp only [Christoffel.partials, stackPartials, Matrix.of_apply, Equiv.symm_apply_apply]
  rcases eq_or_ne i k with rfl | hik
  · have hc : c ≠ i := h.resolve_left fun h' => h' rfl
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.of_apply, ContinuousLinearMap.comp_apply,
      fingerProj_single_ne e hc, map_zero]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hik, _root_.zero_apply]

omit [Fintype ι] in
/-- Within one finger the stacked Christoffel symbols are the finger's (MLS eq. (4.22), p. 170). -/
private theorem symbol_stackPartials_same (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ)) (i : ι)
    (a b d : Fin (n i)) :
    Christoffel.symbol (Christoffel.partials (stackPartials e M')) (e ⟨i, a⟩) (e ⟨i, b⟩)
        (e ⟨i, d⟩) = Christoffel.symbol (Christoffel.partials (M' i)) a b d := by
  simp only [Christoffel.symbol, Christoffel.partials, stackPartials, Matrix.of_apply,
    Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq, ContinuousLinearMap.comp_apply,
    fingerProj_single_self]

omit [Fintype ι] in
/-- A stacked Christoffel symbol with indices in two fingers vanishes (MLS eq. (4.22), p. 170). -/
private theorem symbol_stackPartials_eq_zero (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ))
    {p q r : Σ i, Fin (n i)} (h : p.1 ≠ q.1 ∨ r.1 ≠ p.1) :
    Christoffel.symbol (Christoffel.partials (stackPartials e M')) (e p) (e q) (e r) = 0 := by
  rw [Christoffel.symbol]
  rcases h with h | h
  · have h3 : r.1 ≠ q.1 ∨ p.1 ≠ r.1 := by
      by_cases hrq : r.1 = q.1
      · exact Or.inr fun hpr => h (hpr.trans hrq)
      · exact Or.inl hrq
    rw [partials_stackPartials_eq_zero e M' (Or.inl h),
      partials_stackPartials_eq_zero e M' (Or.inr (Ne.symm h)),
      partials_stackPartials_eq_zero e M' h3]
    simp
  · rw [partials_stackPartials_eq_zero e M' (Or.inr h),
      partials_stackPartials_eq_zero e M' (Or.inl (Ne.symm h)),
      partials_stackPartials_eq_zero e M' (Or.inr (Ne.symm h))]
    simp

/-- **MLS p. 276: "`C_f` ... formed by appropriately stacking the quantities obtained for the
individual fingers".** The Christoffel Coriolis matrix (MLS eq. (4.23)) of the stacked inertia field
is the block diagonal of the fingers' Christoffel matrices at their own joint rates. -/
theorem coriolisMatrix_stackPartials (e : (Σ i, Fin (n i)) ≃ Fin N)
    (M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ)) (v : Fin N → ℝ) :
    Christoffel.coriolisMatrix (Christoffel.partials (stackPartials e M')) v =
      stackMat e fun i => Christoffel.coriolisMatrix (Christoffel.partials (M' i))
        (fingerCoords e v i) := by
  ext j l
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective l
  simp only [Christoffel.coriolisMatrix, Matrix.of_apply, stackMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp e]
  rcases eq_or_ne i k with rfl | hik
  · rw [Matrix.blockDiagonal'_apply_eq, Fintype.sum_sigma, Finset.sum_eq_single i]
    · simp only [Matrix.of_apply, symbol_stackPartials_same, fingerCoords]
    · intro c _ hc
      exact Finset.sum_eq_zero fun d _ => by
        rw [symbol_stackPartials_eq_zero e M' (Or.inr hc), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hik]
    exact Finset.sum_eq_zero fun r _ => by
      rw [symbol_stackPartials_eq_zero e M' (Or.inl hik), zero_mul]

/-- **The hand's potential `V(θ) = ∑ᵢ V_{fᵢ}(θ_{fᵢ})` (MLS p. 276, `N_f` stacked).** -/
def stackPotential (e : (Σ i, Fin (n i)) ≃ Fin N) (V : (i : ι) → (Fin (n i) → ℝ) → ℝ) :
    (Fin N → ℝ) → ℝ :=
  fun θ => ∑ i, V i (fingerCoords e θ i)

/-- **The derivative of the hand's potential (MLS p. 276):** `∑ᵢ V'ᵢ ∘ (θ ↦ θ_{fᵢ})`. -/
def stackPotentialDeriv (e : (Σ i, Fin (n i)) ≃ Fin N)
    (V' : (i : ι) → (Fin (n i) → ℝ) →L[ℝ] ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i, (V' i).comp (fingerProj e i)

omit [DecidableEq ι] in
/-- The hand's potential has the stacked derivative (MLS p. 276). -/
theorem hasFDerivAt_stackPotential (e : (Σ i, Fin (n i)) ≃ Fin N)
    {V : (i : ι) → (Fin (n i) → ℝ) → ℝ} {V' : (i : ι) → (Fin (n i) → ℝ) →L[ℝ] ℝ}
    {θ : Fin N → ℝ} (hV : ∀ i, HasFDerivAt (V i) (V' i) (fingerCoords e θ i)) :
    HasFDerivAt (stackPotential e V) (stackPotentialDeriv e V') θ := by
  exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hV i).comp θ (fingerProj e i).hasFDerivAt

omit [DecidableEq ι] in
/-- **The gradient of the hand's potential is the stack of the fingers' gradients (MLS p. 276, `N_f`
stacked).** -/
theorem gradient_stackPotentialDeriv (e : (Σ i, Fin (n i)) ≃ Fin N)
    (V' : (i : ι) → (Fin (n i) → ℝ) →L[ℝ] ℝ) :
    Lagrangian.gradient (stackPotentialDeriv e V') =
      stackVec e fun i => Lagrangian.gradient (V' i) := by
  funext j
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  rw [stackVec_apply_e]
  simp only [Lagrangian.gradient, stackPotentialDeriv, _root_.sum_apply,
    ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single i]
  · rw [fingerProj_single_self]
  · intro c _ hc
    rw [fingerProj_single_ne e (Ne.symm hc), map_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **MLS eq. (6.16), p. 276, from Lagrange's equations of the hand (Theorem 4.1, p. 158).** For
symmetric finger inertia fields and potentials with Fréchet data at `θ_{fᵢ}(t)`, along a motion with
velocity `θ'` near `t` and acceleration `θ''` at `t`, the mechanical Lagrangian of the stacked
inertia and potential satisfies Lagrange's equations with the force `τ` exactly when every finger
satisfies `M_{fᵢ} θ̈_{fᵢ} + C_{fᵢ} θ̇_{fᵢ} + ∂V_{fᵢ}/∂θ_{fᵢ} = τ_{fᵢ}`, with the fingers'
Christoffel matrices. -/
theorem lagrangeEquationsAt_stack_iff (e : (Σ i, Fin (n i)) ≃ Fin N)
    {M : (i : ι) → (Fin (n i) → ℝ) → Matrix (Fin (n i)) (Fin (n i)) ℝ}
    {M' : (i : ι) → Fin (n i) → Fin (n i) → ((Fin (n i) → ℝ) →L[ℝ] ℝ)}
    {V : (i : ι) → (Fin (n i) → ℝ) → ℝ} {V' : (i : ι) → (Fin (n i) → ℝ) →L[ℝ] ℝ}
    {θ θ' : ℝ → Fin N → ℝ} {θ'' : Fin N → ℝ} {t : ℝ} (hsymm : ∀ i y, (M i y).IsSymm)
    (hM : ∀ i a b, HasFDerivAt (fun y => M i y a b) (M' i a b) (fingerCoords e (θ t) i))
    (hV : ∀ i, HasFDerivAt (V i) (V' i) (fingerCoords e (θ t) i))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (τ : Fin N → ℝ) :
    Lagrangian.LagrangeEquationsAt (Lagrangian.mechanical (stackField e M) (stackPotential e V)) θ
        τ t ↔
      ∀ i, M i (fingerCoords e (θ t) i) *ᵥ fingerCoords e θ'' i +
          Christoffel.coriolisMatrix (Christoffel.partials (M' i)) (fingerCoords e (θ' t) i) *ᵥ
            fingerCoords e (θ' t) i + Lagrangian.gradient (V' i) = fingerCoords e τ i := by
  rw [Lagrangian.lagrangeEquationsAt_mechanical_iff (M := stackField e M)
    (M' := stackPartials e M') (V := stackPotential e V) (V' := stackPotentialDeriv e V')
    (fun q => stackMat_isSymm e fun i => hsymm i _) (hasFDerivAt_stackField e hM)
    (hasFDerivAt_stackPotential e hV) hθ hθ' τ, coriolisMatrix_stackPartials,
    gradient_stackPotentialDeriv]
  exact stacked_dynamics_iff e (fun i => M i (fingerCoords e (θ t) i)) _ _ _ _ _

omit [Fintype ι] in
/-- **The hand's `Ṁ_f − 2C_f` is skew along a motion when every finger's is (MLS p. 276 with Lemma
4.2(2)).** If the entries of `s ↦ M_{fᵢ}(θ_{fᵢ}(s))` have the derivatives `Ṁᵢ` at `t` and every
`Ṁᵢ − 2Cᵢ` is skew, then every actual derivative of `s ↦ M_f(θ(s))` at `t` minus `2 diag(Cᵢ)` is
skew. -/
theorem skew_deriv_stackField_sub_two (e : (Σ i, Fin (n i)) ≃ Fin N)
    {M : (i : ι) → (Fin (n i) → ℝ) → Matrix (Fin (n i)) (Fin (n i)) ℝ} {θ : ℝ → Fin N → ℝ}
    {t : ℝ} {Md C : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ}
    (hMd : ∀ i a b, HasDerivAt (fun s => M i (fingerCoords e (θ s) i) a b) (Md i a b) t)
    (hs : ∀ i, (Md i - (2 : ℝ) • C i)ᵀ = -(Md i - (2 : ℝ) • C i))
    {Mtd : Matrix (Fin N) (Fin N) ℝ}
    (hMt : ∀ j l, HasDerivAt (fun s => stackField e M (θ s) j l) (Mtd j l) t) :
    (Mtd - (2 : ℝ) • stackMat e C)ᵀ = -(Mtd - (2 : ℝ) • stackMat e C) := by
  have hMtd : Mtd = stackMat e Md := by
    ext j l
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
    obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective l
    refine (hMt _ _).unique ?_
    simp only [stackField, stackMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases eq_or_ne i k with rfl | hik
    · simp only [Matrix.blockDiagonal'_apply_eq]
      exact hMd i a b
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hik]
      exact hasDerivAt_const t 0
  rw [hMtd]
  exact skew_stackMat_sub_two e hs

end Composite
end RoboLean
