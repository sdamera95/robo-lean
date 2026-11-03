import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.BigOperators.Fin
import RoboLean.Examples.NonholonomicGrowth

/-!
# Chapter 7, Exercise 6: the car with `N` trailers (MLS pp. 349–350)

MLS Chapter 7, Exercise 6, printed pp. 349–350: "We attach the hitch of each trailer to the center
of the rear axle of the previous trailer. The wheels of the individual trailers are aligned with the
body of the trailer. The constraints are again based on allowing the wheels only to roll and spin,
but not slip. … Show that the control equation for the system has the form `ẋ = cos θ₀ u₁`,
`ẏ = sin θ₀ u₁`, `φ̇ = u₂`, `θ̇₀ = (1/l) tan φ u₁`,
`θ̇ᵢ = (1/dᵢ) (∏_{j=1}^{i−1} cos(θ_{j−1} − θⱼ)) sin(θ_{i−1} − θᵢ) u₁`."

**Recorded reading.** `P₀ = (x, y)` is the centre of the car's rear axle, `θ₀` the car's heading;
the centre of trailer `i`'s axle is `Pᵢ = P_{i−1} − dᵢ(cos θᵢ, sin θᵢ)` with `dᵢ ≠ 0` the distance
from the hitch (the previous axle centre) to that axle; the no-slip constraint of trailer `i` says
that `Ṗᵢ` has no component across the trailer, `−Ṗᵢ,ₓ sin θᵢ + Ṗᵢ,ᵧ cos θᵢ = 0`. The car's equations
(`ẋ`, `ẏ`, `θ̇₀`, `φ̇`) are those of the car of §7.2 and are taken as given: `Ṗ₀ = u₁(cos θ₀, sin θ₀)`.

**What is formalized.** Under these constraints, at a time `t` where all the quantities are
differentiable, the trailer angles move as printed, and the axle of trailer `i` moves along its
heading with speed `u₁ ∏_{j=1}^{i} cos(θ_{j−1} − θⱼ)` (`nTrailer_rates`). Indices: the printed
`θᵢ` for `i ≥ 1` is `θ (i)` and its rate is `trailerRate … (i − 1)`.

**Exercise 15 at `N = 0` (p. 353).** Exercise 15 asks to show that the system of Exercise 6 "is
controllable, with degree of nonholonomy `N + 2` and relative growth vector `(2, 1, …, 1)`". For
`N = 0` the system is the car (7.14) of §7.3 (with the coordinates `φ` and `θ₀` exchanged), whose
degree of nonholonomy is `3` at every point with `cos φ ≠ 0` (the library's
`car_isDegreeOfNonholonomy`): so the printed `N + 2` fails at `N = 0` (`exercise15_car_degree`),
while `N + 3`, which is also the length `N + 3` of a relative growth vector `(2, 1, …, 1)` summing to
the dimension `N + 4`, holds there. The general `N` is not formalized.

**Conventions.** Points of the plane are `Fin 2 → ℝ`; products over `j = 1, …, i − 1` are written
over `Finset.range (i − 1)` with `j ↦ cos(θ j − θ (j + 1))`.
-/

noncomputable section

open Real
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Chapter 7, Exercise 6, p. 350: the printed rate of trailer `i + 1`,**
`(1/d_{i+1}) (∏_{j=0}^{i−1} cos(θⱼ − θ_{j+1})) sin(θᵢ − θ_{i+1}) u₁`. -/
def trailerRate (θ : ℕ → ℝ) (d : ℕ → ℝ) (u₁ : ℝ) (i : ℕ) : ℝ :=
  (1 / d (i + 1)) * (∏ j ∈ Finset.range i, cos (θ j - θ (j + 1))) * sin (θ i - θ (i + 1)) * u₁

/-- **MLS Chapter 7, Exercise 6, pp. 349–350: the control equations of the trailers.** If the axle
centres satisfy `P_{i+1} = Pᵢ − d_{i+1}(cos θ_{i+1}, sin θ_{i+1})` with `d_{i+1} ≠ 0`, the car's axle
moves as `Ṗ₀ = u₁(cos θ₀, sin θ₀)`, and every trailer axle satisfies the no-slip constraint, then
at `t` every trailer angle moves with the printed rate `θ̇_{i+1} = trailerRate θ d u₁ i`, and the
axle of trailer `i` moves along its heading with speed `u₁ ∏_{j<i} cos(θⱼ − θ_{j+1})`. -/
theorem nTrailer_rates {P : ℕ → ℝ → Fin 2 → ℝ} {θ : ℕ → ℝ → ℝ} {θ' : ℕ → ℝ} {V : ℕ → Fin 2 → ℝ}
    {d : ℕ → ℝ} {t u₁ : ℝ} (hd : ∀ i, d (i + 1) ≠ 0)
    (hP : ∀ i s, P (i + 1) s = P i s - d (i + 1) • ![cos (θ (i + 1) s), sin (θ (i + 1) s)])
    (hθ : ∀ i, HasDerivAt (θ i) (θ' i) t) (hV : ∀ i, HasDerivAt (P i) (V i) t)
    (hV0 : V 0 = u₁ • ![cos (θ 0 t), sin (θ 0 t)])
    (hns : ∀ i, -V (i + 1) 0 * sin (θ (i + 1) t) + V (i + 1) 1 * cos (θ (i + 1) t) = 0) :
    ∀ i, θ' (i + 1) = trailerRate (fun j => θ j t) d u₁ i ∧
      V i = (u₁ * ∏ j ∈ Finset.range i, cos (θ j t - θ (j + 1) t)) •
        ![cos (θ i t), sin (θ i t)] := by
  -- the velocity of each trailer axle from the hitch relation
  have hrel : ∀ i, V (i + 1) = V i - d (i + 1) •
      ![-sin (θ (i + 1) t) * θ' (i + 1), cos (θ (i + 1) t) * θ' (i + 1)] := by
    intro i
    have hc : HasDerivAt (fun s => (![cos (θ (i + 1) s), sin (θ (i + 1) s)] : Fin 2 → ℝ))
        ![-sin (θ (i + 1) t) * θ' (i + 1), cos (θ (i + 1) t) * θ' (i + 1)] t := by
      refine hasDerivAt_pi.2 fun k => ?_
      fin_cases k
      · simpa using (hθ (i + 1)).cos
      · simpa using (hθ (i + 1)).sin
    have h := (hV i).sub (hc.const_smul (d (i + 1)))
    have hfun : P (i + 1) = P i - d (i + 1) • fun s => ![cos (θ (i + 1) s), sin (θ (i + 1) s)] :=
      funext fun s => by rw [hP i s]; rfl
    rw [← hfun] at h
    exact (hV (i + 1)).unique h
  -- the speed along the heading, by induction
  have hspeed : ∀ i, V i = (u₁ * ∏ j ∈ Finset.range i, cos (θ j t - θ (j + 1) t)) •
      ![cos (θ i t), sin (θ i t)] ∧ (∀ k, k + 1 ≤ i → θ' (k + 1) = trailerRate (fun j => θ j t) d u₁ k) := by
    intro i
    induction i with
    | zero => exact ⟨by simpa using hV0, fun k hk => by omega⟩
    | succ i ih =>
      obtain ⟨hVi, hrates⟩ := ih
      set c := u₁ * ∏ j ∈ Finset.range i, cos (θ j t - θ (j + 1) t) with hcdef
      have hn := hns i
      rw [hrel i, hVi] at hn
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at hn
      -- the rate of trailer `i + 1`
      have hrate : θ' (i + 1) = (1 / d (i + 1)) * c * sin (θ i t - θ (i + 1) t) := by
        have hs := sin_sq_add_cos_sq (θ (i + 1) t)
        rw [sin_sub]
        field_simp [hd i]
        linear_combination (-1 : ℝ) * hn - d (i + 1) * θ' (i + 1) * hs
      refine ⟨?_, fun k hk => ?_⟩
      · rw [hrel i, hVi, hrate, Finset.prod_range_succ,
          show u₁ * ((∏ x ∈ Finset.range i, cos (θ x t - θ (x + 1) t)) * cos (θ i t - θ (i + 1) t)) =
            c * cos (θ i t - θ (i + 1) t) by rw [hcdef]; ring]
        have hs := sin_sq_add_cos_sq (θ (i + 1) t)
        funext k
        fin_cases k
        · simp only [Fin.zero_eta, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
          rw [cos_sub, sin_sub]
          field_simp [hd i]
          linear_combination (-(c * cos (θ i t))) * hs
        · simp only [Fin.mk_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          rw [cos_sub, sin_sub]
          field_simp [hd i]
          linear_combination (-(c * sin (θ i t))) * hs
      · rcases Nat.lt_or_ge k i with hki | hki
        · exact hrates k (by omega)
        · have : k = i := by omega
          subst this
          rw [hrate, trailerRate, hcdef]
          ring
  exact fun i => ⟨(hspeed (i + 1)).2 i le_rfl, (hspeed i).1⟩

/-- **MLS Chapter 7, Exercise 15, p. 353, at `N = 0`: the degree of nonholonomy is `N + 3`, not the
printed `N + 2`.** The car (7.14) (Exercise 6 with no trailer, in the library's coordinates
`(x, y, θ, φ)`) has degree of nonholonomy `3` at every point with `cos φ ≠ 0`, and not `2`. -/
theorem exercise15_car_degree {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : q ∈ carDomain) :
    IsDegreeOfNonholonomy (carFields l) q (0 + 3) ∧ ¬ IsDegreeOfNonholonomy (carFields l) q (0 + 2) :=
  ⟨car_isDegreeOfNonholonomy hl hq, fun h => by
    have := h.unique (car_isDegreeOfNonholonomy hl hq)
    omega⟩

end Examples
end RoboLean
