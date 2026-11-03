import RoboLean.Geometry.Reciprocal
import RoboLean.Geometry.TwistScrew

/-!
# Reciprocal screw systems of zero-pitch and infinite-pitch screws

MLS Exercise 2.17(c)–(e), printed p. 78, with the reciprocal product `ξ ⊙ η = v₁ · ω₂ + v₂ · ω₁`
of printed p. 67 (`Twist.reciprocalProduct`) and the zero-pitch twist `(-ω × q, ω)` about the line
through `q` with direction `ω` (`Twist.fromScrew ω q 0`, MLS equation (2.43) with `h = 0`).
Coordinates `(v, ω)`, linear part first.

* (c) A twist is reciprocal to the zero-pitch screw through `q` with direction `ω` exactly when it
  is the sum of a zero-pitch screw through `q` (any direction `w`) and a pure translation `u`
  perpendicular to `ω`: geometrically, the zero-pitch screws whose axes meet the given axis at `q`
  and the infinite-pitch screws perpendicular to it. In the frame with `q = 0` and `ω = e₃` (the
  book's hint) the five twists `(e₁, 0), (e₂, 0), (0, e₁), (0, e₂), (0, e₃)` are a basis.
* (d) A twist is reciprocal to the infinite-pitch screw `(v, 0)` exactly when its angular part is
  perpendicular to `v`: every pure translation, and every twist whose rotation axis is perpendicular
  to `v`.
* (e) Three parallel coplanar zero-pitch screws are linearly dependent: four linearly independent
  screws reciprocal to each of them are exhibited (two translations perpendicular to the common
  direction and two zero-pitch screws along lines of the plane), and Proposition 2.19 (printed
  p. 69) bounds the dimension of their span by `6 - 4 = 2`.
-/

noncomputable section

namespace RoboLean

namespace Twist

/-- The scalar triple product changes sign when the outer factors are exchanged,
`(a × b) · c = -(c × b) · a` (MLS p. 26, right-handed cross product). Supporting lemma. -/
private theorem inner_cross_swap (a b c : Vec3) :
    inner ℝ (Vec3.cross a b) c = -inner ℝ (Vec3.cross c b) a := by
  simp only [Vec3.cross, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    cross_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

private theorem inner_cross_left_self (a b : Vec3) : inner ℝ (Vec3.cross a b) a = 0 := by
  have := inner_cross_swap a b a
  linarith

private theorem inner_cross_right_self (a b : Vec3) : inner ℝ (Vec3.cross a b) b = 0 := by
  simp only [Vec3.cross, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    cross_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- Lagrange's identity `‖a × b‖² = ‖a‖² ‖b‖² - (a · b)²` in inner products (MLS p. 26). -/
private theorem inner_cross_cross_self (a b : Vec3) :
    inner ℝ (Vec3.cross a b) (Vec3.cross a b) =
      inner ℝ a a * inner ℝ b b - inner ℝ a b ^ 2 := by
  simp only [Vec3.cross, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    cross_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- MLS Exercise 2.17(c), printed p. 78: a twist `η` is reciprocal to the zero-pitch screw through
`q` with direction `ω`, `(-ω × q, ω) ⊙ η = 0`, exactly when `η = (-w × q + u, w)` with `u · ω = 0`:
a zero-pitch screw through `q` with direction `w` plus a translation perpendicular to `ω`.
No normalization of `ω` is assumed. -/
theorem reciprocalProduct_fromScrew_zero_eq_zero_iff (ω q : Vec3) (η : Twist) :
    reciprocalProduct (fromScrew ω q 0) η = 0 ↔
      ∃ w u : Vec3, inner ℝ u ω = 0 ∧ η = ⟨-Vec3.cross w q + u, w⟩ := by
  rw [reciprocalProduct_eq]
  simp only [fromScrew, zero_smul, add_zero, inner_neg_left]
  constructor
  · intro h
    refine ⟨η.angular, η.linear + Vec3.cross η.angular q, ?_, ?_⟩
    · rw [inner_add_left, inner_cross_swap η.angular q ω]
      linarith
    · apply Twist.ext
      · simp only
        abel
      · rfl
  · rintro ⟨w, u, hu, rfl⟩
    simp only
    rw [inner_add_left, hu, inner_neg_left, inner_cross_swap ω q w]
    ring

/-- MLS Exercise 2.17(c), printed p. 78, in the frame of the book's hint (`q = 0`, `ω = e₃`): the
five twists `(e₁, 0), (e₂, 0), (0, e₁), (0, e₂), (0, e₃)` are linearly independent. Indices
`0, 1, 2` for the book's `1, 2, 3`. -/
theorem linearIndependent_reciprocal_basis_e3 :
    LinearIndependent ℝ ![(⟨EuclideanSpace.single 0 1, 0⟩ : Twist),
      ⟨EuclideanSpace.single 1 1, 0⟩, ⟨0, EuclideanSpace.single 0 1⟩,
      ⟨0, EuclideanSpace.single 1 1⟩, ⟨0, EuclideanSpace.single 2 1⟩] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hl (k : Fin 3) := congrArg (fun ξ : Twist => ξ.linear k) hg
  have ha (k : Fin 3) := congrArg (fun ξ : Twist => ξ.angular k) hg
  simp only [Fin.sum_univ_five] at hl ha
  simp at hl ha
  intro i
  fin_cases i
  · simpa using hl 0
  · simpa using hl 1
  · simpa using ha 0
  · simpa using ha 1
  · simpa using ha 2

/-- MLS Exercise 2.17(c), printed p. 78, in the frame of the book's hint: the twists reciprocal to
the zero-pitch screw `(0, e₃)` through the origin are exactly the span of
`(e₁, 0), (e₂, 0), (0, e₁), (0, e₂), (0, e₃)`. -/
theorem reciprocal_e3_eq_span (η : Twist) :
    reciprocalProduct ⟨0, EuclideanSpace.single 2 1⟩ η = 0 ↔
      η ∈ Submodule.span ℝ (Set.range ![(⟨EuclideanSpace.single 0 1, 0⟩ : Twist),
        ⟨EuclideanSpace.single 1 1, 0⟩, ⟨0, EuclideanSpace.single 0 1⟩,
        ⟨0, EuclideanSpace.single 1 1⟩, ⟨0, EuclideanSpace.single 2 1⟩]) := by
  rw [Submodule.mem_span_range_iff_exists_fun, reciprocalProduct_eq]
  constructor
  · intro h
    simp [EuclideanSpace.inner_single_right] at h
    refine ⟨![η.linear 0, η.linear 1, η.angular 0, η.angular 1, η.angular 2], ?_⟩
    apply Twist.ext <;> ext k <;> fin_cases k <;> simp [Fin.sum_univ_five, h]
  · rintro ⟨c, rfl⟩
    simp [Fin.sum_univ_five, EuclideanSpace.inner_single_right]

/-- MLS Exercise 2.17(d), printed p. 78: a twist `η` is reciprocal to the infinite-pitch screw
`(v, 0)` exactly when its angular part is perpendicular to `v`. -/
theorem reciprocalProduct_translation_eq_zero_iff (v : Vec3) (η : Twist) :
    reciprocalProduct ⟨v, 0⟩ η = 0 ↔ inner ℝ v η.angular = 0 := by
  rw [reciprocalProduct_eq]
  simp

/-- MLS Exercise 2.17(e), printed p. 78, the reciprocal screws: for three zero-pitch screws
`(-ω × qᵢ, ω)` with a common direction `ω` and axes in the plane through `q₁` with normal `n`
(`n · ω = 0`, `n · (qᵢ - q₁) = 0`), each of the four screws `(n, 0)`, `(ω × n, 0)`,
`(-ω × q₁, ω)` and `(-(ω × n) × q₁, ω × n)` is reciprocal to each of the three. -/
theorem reciprocalProduct_coplanar_eq_zero (ω n : Vec3) (q : Fin 3 → Vec3)
    (hnω : inner ℝ n ω = 0) (hq : ∀ i, inner ℝ n (q i - q 0) = 0) (i : Fin 3) (j : Fin 4) :
    reciprocalProduct (![⟨n, 0⟩, ⟨Vec3.cross ω n, 0⟩, fromScrew ω (q 0) 0,
      fromScrew (Vec3.cross ω n) (q 0) 0] j) (fromScrew ω (q i) 0) = 0 := by
  have hωn : inner ℝ ω n = 0 := by rw [real_inner_comm]; exact hnω
  fin_cases j
  · simp [reciprocalProduct_eq, fromScrew, hnω]
  · simp [reciprocalProduct_eq, fromScrew, inner_cross_left_self]
  · simp [reciprocalProduct_eq, fromScrew, inner_neg_left, inner_cross_left_self]
  · have key : reciprocalProduct (fromScrew (Vec3.cross ω n) (q 0) 0) (fromScrew ω (q i) 0) =
        inner ℝ ω n * inner ℝ ω (q i - q 0) - inner ℝ ω ω * inner ℝ n (q i - q 0) := by
      simp only [reciprocalProduct_eq, fromScrew, zero_smul, add_zero]
      simp only [Vec3.cross, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_three, cross_apply, WithLp.ofLp_toLp, PiLp.neg_apply, PiLp.sub_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring
    simpa [hωn, hq i] using key

/-- MLS Exercise 2.17(e), printed p. 78: the four reciprocal screws of
`reciprocalProduct_coplanar_eq_zero` are linearly independent when `ω ≠ 0`, `n ≠ 0` and
`n · ω = 0`. -/
theorem linearIndependent_coplanar_reciprocal (ω n p : Vec3) (hω : ω ≠ 0) (hn : n ≠ 0)
    (hnω : inner ℝ n ω = 0) :
    LinearIndependent ℝ ![(⟨n, 0⟩ : Twist), ⟨Vec3.cross ω n, 0⟩, fromScrew ω p 0,
      fromScrew (Vec3.cross ω n) p 0] := by
  have hωω : 0 < inner ℝ ω ω := real_inner_self_pos.mpr hω
  have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
  have hωn : inner ℝ ω n = 0 := by rw [real_inner_comm]; exact hnω
  have hmm : 0 < inner ℝ (Vec3.cross ω n) (Vec3.cross ω n) := by
    rw [inner_cross_cross_self, hωn]
    nlinarith
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four] at hg
  have hang := congrArg Twist.angular hg
  have hlin := congrArg Twist.linear hg
  simp [fromScrew] at hang hlin
  -- angular parts: `g₂ ω + g₃ (ω × n) = 0`
  have h2 : g 2 = 0 := by
    have := congrArg (fun x => inner ℝ x ω) hang
    simp only [inner_add_left, inner_smul_left, conj_trivial, inner_zero_left,
      inner_cross_left_self, mul_zero, add_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hωω.ne'
  have h3 : g 3 = 0 := by
    have := congrArg (fun x => inner ℝ x (Vec3.cross ω n)) hang
    simp only [inner_add_left, inner_smul_left, conj_trivial, inner_zero_left, h2,
      zero_mul, zero_add] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hmm.ne'
  simp only [h2, h3, zero_smul, add_zero, neg_zero] at hlin
  have h0 : g 0 = 0 := by
    have := congrArg (fun x => inner ℝ x n) hlin
    simp only [inner_add_left, inner_smul_left, conj_trivial, inner_zero_left,
      inner_cross_right_self, mul_zero, add_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hnn.ne'
  have h1 : g 1 = 0 := by
    have := congrArg (fun x => inner ℝ x (Vec3.cross ω n)) hlin
    simp only [inner_add_left, inner_smul_left, conj_trivial, inner_zero_left, h0,
      zero_mul, zero_add] at this
    rw [real_inner_comm] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hmm.ne'
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- MLS Exercise 2.17(e), printed p. 78: three parallel coplanar zero-pitch screws are linearly
dependent. The screws are `(-ω × qᵢ, ω)` with a common direction `ω ≠ 0` and axes in a plane with
normal `n ≠ 0` (`n · ω = 0`, `n · (qᵢ - q₁) = 0`); the proof counts dimensions with the four
reciprocal screws and Proposition 2.19 (printed p. 69). -/
theorem not_linearIndependent_coplanar (ω n : Vec3) (q : Fin 3 → Vec3) (hω : ω ≠ 0) (hn : n ≠ 0)
    (hnω : inner ℝ n ω = 0) (hq : ∀ i, inner ℝ n (q i - q 0) = 0) :
    ¬ LinearIndependent ℝ fun i => fromScrew ω (q i) 0 := by
  intro hind
  set S := Submodule.span ℝ (Set.range fun i => fromScrew ω (q i) 0)
  set η := ![(⟨n, 0⟩ : Twist), ⟨Vec3.cross ω n, 0⟩, fromScrew ω (q 0) 0,
    fromScrew (Vec3.cross ω n) (q 0) 0]
  have hS : Module.finrank ℝ S = 3 := by
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hind' : LinearIndependent ℝ (fun j => swapWrench (η j)) :=
    (linearIndependent_coplanar_reciprocal ω n (q 0) hω hn hnω).map' swapWrench.toLinearMap
      (LinearEquiv.ker _)
  have hle : Submodule.span ℝ (Set.range fun j => swapWrench (η j)) ≤ Reciprocal.wrenches S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Reciprocal.mem_wrenches_span]
    rintro _ ⟨i, rfl⟩
    exact reciprocalProduct_coplanar_eq_zero ω n q hnω hq i j
  have h4 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hind', Fintype.card_fin] at h4
  have := Reciprocal.finrank_add_finrank_wrenches S
  omega

end Twist

end RoboLean
