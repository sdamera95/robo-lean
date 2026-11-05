import RoboLean.Examples.ElbowExerciseIsotropy

/-!
# Point sets of the three-link arm and clearance from separating planes

The arm is the elbow arm without a wrist (MLS Example 3.2, pp. 89–91; the same kinematics as the
three-link arm of MLS Example 4.3, pp. 172–174): base yaw `θ 0`, shoulder `θ 1`, elbow `θ 2`, in
radians. At `θ = 0` the arm lies along `+y` at the shoulder height `l₀`; negative `θ 1` raises the
arm. The tool point is `elbowArmPosition l₀ l₁ l₂ θ`, the elbow point is the same map with `l₂ = 0`,
and the shoulder is `(0, 0, l₀)`. The two links are the segments shoulder–elbow and elbow–tool.

Points of space are coordinate functions `Fin 3 → ℝ` in metres. Distances are Euclidean: the
distance between `p` and `q` is `dist (toLp 2 p) (toLp 2 q)` in `EuclideanSpace ℝ (Fin 3)`, which
equals `√(∑ i, (p i - q i) ^ 2)` (`euclidDist_eq`). (The default norm on `Fin 3 → ℝ` is the sup
norm, so it is not used for distances here.)

A separating plane `(n, β)` with `n ⬝ᵥ n ≤ 1` certifies clearance `r` between a point `q` and a set
`O`: if `O` lies in `{p | n ⬝ᵥ p ≤ β}` and `β + r ≤ n ⬝ᵥ q`, every point of `O` is at Euclidean
distance at least `r` from `q`, by the Cauchy–Schwarz inequality. A half-space `{p | r ≤ n ⬝ᵥ p}`
that contains the endpoints of a segment contains the segment, so checking the shoulder, the elbow
and the tool point certifies both links. These are design statements, not from MLS.
-/

noncomputable section

open Real

namespace RoboLean.Cell

open RoboLean.Examples

/-- The Euclidean distance between two points of space given as coordinate functions, in metres:
the distance of `EuclideanSpace ℝ (Fin 3)` (a design definition, not from MLS). -/
def euclidDist (p q : Fin 3 → ℝ) : ℝ :=
  dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 q)

/-- The Euclidean distance in coordinates: `√(∑ i, (p i - q i) ^ 2)` (a design statement, not from
MLS). -/
theorem euclidDist_eq (p q : Fin 3 → ℝ) : euclidDist p q = √(∑ i, (p i - q i) ^ 2) := by
  simp [euclidDist, EuclideanSpace.dist_eq, Real.dist_eq, sq_abs]

/-- A point set `A` keeps Euclidean clearance at least `r` from a set `O`: every point of `A` is at
Euclidean distance at least `r` from every point of `O` (a design definition, not from MLS; metres).
-/
def KeepsClearance (A O : Set (Fin 3 → ℝ)) (r : ℝ) : Prop :=
  ∀ q ∈ A, ∀ p ∈ O, r ≤ euclidDist q p

/-- The closed neighbourhood of radius `ρ` of a point set `A` in the Euclidean distance; for a link
segment `A` it is the capsule of radius `ρ` around the link (a design definition, not from MLS). -/
def capsule (A : Set (Fin 3 → ℝ)) (ρ : ℝ) : Set (Fin 3 → ℝ) :=
  {x | ∃ q ∈ A, euclidDist x q ≤ ρ}

/-- The shoulder point `(0, 0, l₀)` of the three-link arm, on the base yaw axis (MLS Example 3.2,
pp. 89–90: the shoulder joint axis passes through `(0, 0, l₀)`; metres). -/
def shoulderPoint (l₀ : ℝ) : Fin 3 → ℝ := ![0, 0, l₀]

/-- The elbow point of the three-link arm: the tool map `elbowArmPosition` of MLS Example 3.2
(pp. 90–91) with forearm length `0`, that is `(−sin θ₀ l₁ cos θ₁, cos θ₀ l₁ cos θ₁, l₀ − l₁ sin θ₁)`
(radians, metres). -/
def elbowPoint (l₀ l₁ : ℝ) (θ : Fin 3 → ℝ) : Fin 3 → ℝ := elbowArmPosition l₀ l₁ 0 θ

/-- The two links of the three-link arm at the configuration `θ` as point sets: the segment from the
shoulder to the elbow point and the segment from the elbow point to the tool point
`elbowArmPosition l₀ l₁ l₂ θ` (MLS Example 3.2, pp. 89–91, links idealized as segments; a design
definition). -/
def armLinks (l₀ l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  segment ℝ (shoulderPoint l₀) (elbowPoint l₀ l₁ θ) ∪
    segment ℝ (elbowPoint l₀ l₁ θ) (elbowArmPosition l₀ l₁ l₂ θ)

/-- A half-space `{q | r ≤ n ⬝ᵥ q}` that contains both endpoints of a segment contains the whole
segment (convexity of a half-space; a design statement, not from MLS). -/
theorem le_dotProduct_of_mem_segment {n x y q : Fin 3 → ℝ} {r : ℝ} (hx : r ≤ n ⬝ᵥ x)
    (hy : r ≤ n ⬝ᵥ y) (hq : q ∈ segment ℝ x y) : r ≤ n ⬝ᵥ q := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have h3 : r = a * r + b * r := by rw [← add_mul, hab, one_mul]
  linarith

/-- Clearance from a separating plane: if `n ⬝ᵥ n ≤ 1`, `n ⬝ᵥ p ≤ β` and `β + r ≤ n ⬝ᵥ q`, then the
Euclidean distance from `q` to `p` is at least `r` (Cauchy–Schwarz; a design statement, not from
MLS). -/
theorem le_euclidDist_of_separating {n p q : Fin 3 → ℝ} {β r : ℝ} (hn : n ⬝ᵥ n ≤ 1)
    (hp : n ⬝ᵥ p ≤ β) (hq : β + r ≤ n ⬝ᵥ q) : r ≤ euclidDist q p := by
  rw [euclidDist_eq]
  simp only [dotProduct, Fin.sum_univ_three] at hn hp hq ⊢
  rcases le_or_gt r 0 with hr | hr
  · exact hr.trans (Real.sqrt_nonneg _)
  apply Real.le_sqrt_of_sq_le
  set a := n 0 * (q 0 - p 0) + n 1 * (q 1 - p 1) + n 2 * (q 2 - p 2) with ha
  have h1 : r ≤ a := by rw [ha]; linarith
  have h2 : r ^ 2 ≤ a ^ 2 := by nlinarith
  have h3 : a ^ 2 ≤ (n 0 * n 0 + n 1 * n 1 + n 2 * n 2) *
      ((q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 + (q 2 - p 2) ^ 2) := by
    rw [ha]
    nlinarith [sq_nonneg (n 0 * (q 1 - p 1) - n 1 * (q 0 - p 0)),
      sq_nonneg (n 0 * (q 2 - p 2) - n 2 * (q 0 - p 0)),
      sq_nonneg (n 1 * (q 2 - p 2) - n 2 * (q 1 - p 1))]
  have h4 : (n 0 * n 0 + n 1 * n 1 + n 2 * n 2) *
      ((q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 + (q 2 - p 2) ^ 2) ≤
      (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 + (q 2 - p 2) ^ 2 :=
    mul_le_of_le_one_left (by positivity) hn
  linarith

/-- The plane `(n, β)` is a clearance certificate of margin `r` for the arm over the configuration
set `S` against the obstacle `O`: `n ⬝ᵥ n ≤ 1`, the obstacle lies in `{p | n ⬝ᵥ p ≤ β}`, and
`β + r ≤ n ⬝ᵥ p` holds at the shoulder, and at the elbow and tool points of every `θ ∈ S` (a design
definition, not from MLS; the arm of MLS Example 3.2, metres and radians). -/
def IsArmPlaneCert (l₀ l₁ l₂ : ℝ) (O S : Set (Fin 3 → ℝ)) (r : ℝ) (n : Fin 3 → ℝ) (β : ℝ) :
    Prop :=
  n ⬝ᵥ n ≤ 1 ∧ (∀ p ∈ O, n ⬝ᵥ p ≤ β) ∧ β + r ≤ n ⬝ᵥ shoulderPoint l₀ ∧
    ∀ θ ∈ S, β + r ≤ n ⬝ᵥ elbowPoint l₀ l₁ θ ∧ β + r ≤ n ⬝ᵥ elbowArmPosition l₀ l₁ l₂ θ

/-- A plane certificate gives clearance of both links: at every `θ ∈ S` every point of the two link
segments is at Euclidean distance at least `r` from every point of the obstacle (a design
statement, not from MLS). -/
theorem IsArmPlaneCert.keepsClearance {l₀ l₁ l₂ r β : ℝ} {O S : Set (Fin 3 → ℝ)}
    {n : Fin 3 → ℝ} (h : IsArmPlaneCert l₀ l₁ l₂ O S r n β) :
    ∀ θ ∈ S, KeepsClearance (armLinks l₀ l₁ l₂ θ) O r := by
  obtain ⟨hn, hO, hs, hS⟩ := h
  intro θ hθ q hq p hp
  obtain ⟨he, ht⟩ := hS θ hθ
  have hq' : β + r ≤ n ⬝ᵥ q := by
    rcases hq with hq | hq
    · exact le_dotProduct_of_mem_segment hs he hq
    · exact le_dotProduct_of_mem_segment he ht hq
  exact le_euclidDist_of_separating hn (hO p hp) hq'

/-- Clearance `ρ + c` of a point set gives clearance `c` of its capsule of radius `ρ`, by the
triangle inequality (a design statement, not from MLS; metres). -/
theorem KeepsClearance.capsule {A O : Set (Fin 3 → ℝ)} {ρ c : ℝ}
    (h : KeepsClearance A O (ρ + c)) : KeepsClearance (capsule A ρ) O c := by
  rintro x ⟨q, hq, hxq⟩ p hp
  have h1 := h q hq p hp
  have h2 : euclidDist q p ≤ euclidDist q x + euclidDist x p := dist_triangle _ _ _
  have h3 : euclidDist q x = euclidDist x q := dist_comm _ _
  linarith

end RoboLean.Cell
