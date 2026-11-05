import RoboLean.Demo.ArrivalConstants
import RoboLean.Control.RegulationRate
import RoboLean.Examples.PlanarTwoLinkRate

/-!
# Sharper arrival constants for the planar arm demo

The demo's arm (the demo report's parameters; MLS prints none for this arm): link lengths
`l₁ = 1`, `l₂ = 1/2`, unit masses, mass centres at mid-link (`r₁ = 1/2`, `r₂ = 1/4`), moments
`I_{z1} = 1/12`, `I_{z2} = 1/48` about the joint axes, under the PD law (4.51) of MLS p. 193 with
compensation of `N` and `K_p = K_v = I`. Its inertia matrix (MLS eq. (4.10), p. 165) is
`M(θ) = [[17/12 + c₂/2, 1/12 + c₂/4], [1/12 + c₂/4, 1/12]]`, `c₂ = cos θ₂`, and `β = m₂l₁r₂ = 1/4`.

**Constants.** The skewed energy `V = ½ ėᵀMė + ½|e|² + ε eᵀMė` of the proof of Proposition 4.10
(p. 194) decays at the rate `V̇ ≤ −kV` wherever the position error satisfies `|e₂| ≤ r`: the only
term of `V̇` that is not quadratic in the state is `−ε β (s₂e₂) ė₁(ė₁ + ė₂)`
(`Examples/PlanarTwoLinkRate`), and with `s₂e₂` frozen in `[−r, r]` and `c₂` in `[−1, 1]` the
inequality is one between quadratic forms whose coefficients are affine in `c₂` and in `s₂e₂`; it
is proved by an exact sum-of-squares identity at the four corners of that box
(`demoArm_rate_le_eight`, `demoArm_rate_le_four`). The energy `½ ėᵀMė + ½|e|²` of Proposition 4.9
does not increase along solutions and is at most `(7/3)ρ²` on the sup-norm ball of radius `ρ`, so
`e₂² ≤ (14/3)ρ²` at all later times. With these:

* for initial state errors below `ρ = 8`: `ε = 1/10`, `k = 1/6`, `r = 35/2`, the exponential bound
  with `C = 19` and `α = 1/12` (`demoArm_exponentialBoundOn_sharp`), the arrival time for the
  demo's tolerance at most `116` s (`demo_arrivalTime_sharp_le`) and the age bound `232` half-second
  periods (`demo_planarDist_le_at_bound_of_run_sharp`);
* for initial state errors below `ρ = 4`: `ε = 1/7`, `k = 1/4`, `r = 35/4`, `C = 19`, `α = 1/8`
  (`demoArm_exponentialBoundOn_sharp_four`), arrival time at most `72` s
  (`demo_arrivalTime_sharp_four_le`) and the age bound `144` periods
  (`demo_planarDist_le_at_bound_of_run_sharp_four`).

The constants are conservative bounds from one Lyapunov function; they are not a statement about
the arm's actual convergence time.

Conventions: the state `(θ, θ̇)` with Mathlib's sup norms on `Fin 2 → ℝ` and on products for the
exponential bound, Euclidean squares written out inside the inequalities; the book's frame of
Figure 4.4 (p. 164); the demo report's conventions for runs, targets and the Euclidean tolerance.
Statements about the ideal continuous model with exact model cancellation and a fixed target per
command; not the sampled loop, the floating-point simulation or a physical arm.
-/

noncomputable section

namespace RoboLean.Demo

open Matrix RoboLean.Examples RoboLean.Stability

/-- **The decay of the skewed energy on the box for `ρ = 8` (MLS p. 195, with eqs. (4.10)–(4.11),
p. 165, and the demo report's parameters).** For `ε = 1/10`, `k = 1/6`, `|c| ≤ 1` (the cosine
`c₂`) and `|p| ≤ 35/2` (the product `s₂e₂`): the derivative
`−|ė|² + ε ėᵀMė − ε|e|² − ε eᵀė − (ε/4) p ė₁(ė₁ + ė₂)` is at most `−k` times
`½ ėᵀMė + ½|e|² + ε eᵀMė`, with `M = [[17/12 + c/2, 1/12 + c/4], [1/12 + c/4, 1/12]]`. -/
theorem demoArm_rate_le_eight (e₀ e₁ w₀ w₁ c p : ℝ) (hc : |c| ≤ 1) (hp : |p| ≤ 35 / 2) :
    -(w₀ ^ 2 + w₁ ^ 2) +
        1 / 10 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) + (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) +
          1 / 12 * (w₁ * w₁)) -
        1 / 10 * (e₀ ^ 2 + e₁ ^ 2) - 1 / 10 * (e₀ * w₀ + e₁ * w₁) -
        1 / 10 * (1 / 4) * p * (w₀ * (w₀ + w₁)) ≤
      -(1 / 6 * (1 / 2 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) +
          (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) + 1 / 12 * (w₁ * w₁)) +
        1 / 2 * (e₀ ^ 2 + e₁ ^ 2) +
        1 / 10 * ((17 / 12 + 1 / 2 * c) * (e₀ * w₀) + (1 / 12 + 1 / 4 * c) * (e₀ * w₁ + e₁ * w₀) +
          1 / 12 * (e₁ * w₁)))) := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  have h11 : 0 ≤ (1 + c) * (35 / 2 + p) := mul_nonneg (by linarith) (by linarith)
  have h12 : 0 ≤ (1 + c) * (35 / 2 - p) := mul_nonneg (by linarith) (by linarith)
  have h21 : 0 ≤ (1 - c) * (35 / 2 + p) := mul_nonneg (by linarith) (by linarith)
  have h22 : 0 ≤ (1 - c) * (35 / 2 - p) := mul_nonneg (by linarith) (by linarith)
  linear_combination (1/4200) * mul_nonneg h11 (sq_nonneg (e₀ + (49/24) * w₀ + (-1/6) * w₁)) +
      (1/4200) * mul_nonneg h11 (sq_nonneg (e₁ + (-1/6) * w₀ + (71/24) * w₁)) +
      (5017/345600) * mul_nonneg h11 (sq_nonneg (w₀ + (5928/35119) * w₁)) +
      (982431841/84959884800) * mul_nonneg h11 (sq_nonneg (w₁)) +
      (1/4200) * mul_nonneg h12 (sq_nonneg (e₀ + (49/24) * w₀ + (-1/6) * w₁)) +
      (1/4200) * mul_nonneg h12 (sq_nonneg (e₁ + (-1/6) * w₀ + (71/24) * w₁)) +
      (697/345600) * mul_nonneg h12 (sq_nonneg (w₀ + (-9192/4879) * w₁)) +
      (56876161/11803276800) * mul_nonneg h12 (sq_nonneg (w₁)) +
      (1/4200) * mul_nonneg h21 (sq_nonneg (e₀ + (61/24) * w₀ + (1/12) * w₁)) +
      (1/4200) * mul_nonneg h21 (sq_nonneg (e₁ + (1/12) * w₀ + (71/24) * w₁)) +
      (40147/2419200) * mul_nonneg h21 (sq_nonneg (w₀ + (8352/40147) * w₁)) +
      (218797037/19424724480) * mul_nonneg h21 (sq_nonneg (w₁)) +
      (1/4200) * mul_nonneg h22 (sq_nonneg (e₀ + (61/24) * w₀ + (1/12) * w₁)) +
      (1/4200) * mul_nonneg h22 (sq_nonneg (e₁ + (1/12) * w₀ + (71/24) * w₁)) +
      (9907/2419200) * mul_nonneg h22 (sq_nonneg (w₀ + (-6768/9907) * w₁)) +
      (48273677/4793402880) * mul_nonneg h22 (sq_nonneg (w₁))

/-- **The decay of the skewed energy on the box for `ρ = 4` (MLS p. 195, with eqs. (4.10)–(4.11),
p. 165, and the demo report's parameters).** For `ε = 1/7`, `k = 1/4`, `|c| ≤ 1` and
`|p| ≤ 35/4`, the inequality of `demoArm_rate_le_eight` with these constants. -/
theorem demoArm_rate_le_four (e₀ e₁ w₀ w₁ c p : ℝ) (hc : |c| ≤ 1) (hp : |p| ≤ 35 / 4) :
    -(w₀ ^ 2 + w₁ ^ 2) +
        1 / 7 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) + (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) +
          1 / 12 * (w₁ * w₁)) -
        1 / 7 * (e₀ ^ 2 + e₁ ^ 2) - 1 / 7 * (e₀ * w₀ + e₁ * w₁) -
        1 / 7 * (1 / 4) * p * (w₀ * (w₀ + w₁)) ≤
      -(1 / 4 * (1 / 2 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) +
          (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) + 1 / 12 * (w₁ * w₁)) +
        1 / 2 * (e₀ ^ 2 + e₁ ^ 2) +
        1 / 7 * ((17 / 12 + 1 / 2 * c) * (e₀ * w₀) + (1 / 12 + 1 / 4 * c) * (e₀ * w₁ + e₁ * w₀) +
          1 / 12 * (e₁ * w₁)))) := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  have h11 : 0 ≤ (1 + c) * (35 / 4 + p) := mul_nonneg (by linarith) (by linarith)
  have h12 : 0 ≤ (1 + c) * (35 / 4 - p) := mul_nonneg (by linarith) (by linarith)
  have h21 : 0 ≤ (1 - c) * (35 / 4 + p) := mul_nonneg (by linarith) (by linarith)
  have h22 : 0 ≤ (1 - c) * (35 / 4 - p) := mul_nonneg (by linarith) (by linarith)
  linear_combination (1/1960) * mul_nonneg h11 (sq_nonneg (e₀ + (25/12) * w₀ + (-1/3) * w₁)) +
      (1/1960) * mul_nonneg h11 (sq_nonneg (e₁ + (-1/3) * w₀ + (47/12) * w₁)) +
      (829/40320) * mul_nonneg h11 (sq_nonneg (w₀ + (828/5803) * w₁)) +
      (32153593/1637838720) * mul_nonneg h11 (sq_nonneg (w₁)) +
      (1/1960) * mul_nonneg h12 (sq_nonneg (e₀ + (25/12) * w₀ + (-1/3) * w₁)) +
      (1/1960) * mul_nonneg h12 (sq_nonneg (e₁ + (-1/3) * w₀ + (47/12) * w₁)) +
      (109/40320) * mul_nonneg h12 (sq_nonneg (w₀ + (-1692/763) * w₁)) +
      (1454953/215349120) * mul_nonneg h12 (sq_nonneg (w₁)) +
      (1/1960) * mul_nonneg h21 (sq_nonneg (e₀ + (37/12) * w₀ + (1/6) * w₁)) +
      (1/1960) * mul_nonneg h21 (sq_nonneg (e₁ + (1/6) * w₀ + (47/12) * w₁)) +
      (1033/40320) * mul_nonneg h21 (sq_nonneg (w₀ + (1452/7231) * w₁)) +
      (38898697/2040877440) * mul_nonneg h21 (sq_nonneg (w₁)) +
      (1/1960) * mul_nonneg h22 (sq_nonneg (e₀ + (37/12) * w₀ + (1/6) * w₁)) +
      (1/1960) * mul_nonneg h22 (sq_nonneg (e₁ + (1/6) * w₀ + (47/12) * w₁)) +
      (313/40320) * mul_nonneg h22 (sq_nonneg (w₀ + (-1068/2191) * w₁)) +
      (11284537/618387840) * mul_nonneg h22 (sq_nonneg (w₁))

/-- **Bounds on the skewed energy for `ε = 1/10` (MLS p. 195, "positive definite for `ε`
sufficiently small", with eq. (4.10), p. 165, and the demo report's parameters).** For `|c| ≤ 1`:
`(3/250)(e₁² + e₂² + ė₁² + ė₂²) ≤ ½ ėᵀMė + ½|e|² + (1/10) eᵀMė` and the same quantity is at most
`(101/100)(e₁² + e₂² + ė₁² + ė₂²)`. -/
theorem demoArm_energy_bounds_eight (e₀ e₁ w₀ w₁ c : ℝ) (hc : |c| ≤ 1) :
    3 / 250 * (e₀ ^ 2 + e₁ ^ 2 + w₀ ^ 2 + w₁ ^ 2) ≤
        1 / 2 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) + (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) +
          1 / 12 * (w₁ * w₁)) + 1 / 2 * (e₀ ^ 2 + e₁ ^ 2) +
        1 / 10 * ((17 / 12 + 1 / 2 * c) * (e₀ * w₀) + (1 / 12 + 1 / 4 * c) * (e₀ * w₁ + e₁ * w₀) +
          1 / 12 * (e₁ * w₁)) ∧
      1 / 2 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) + (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) +
          1 / 12 * (w₁ * w₁)) + 1 / 2 * (e₀ ^ 2 + e₁ ^ 2) +
        1 / 10 * ((17 / 12 + 1 / 2 * c) * (e₀ * w₀) + (1 / 12 + 1 / 4 * c) * (e₀ * w₁ + e₁ * w₀) +
          1 / 12 * (e₁ * w₁)) ≤ 101 / 100 * (e₀ ^ 2 + e₁ ^ 2 + w₀ ^ 2 + w₁ ^ 2) := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  have hc1 : 0 ≤ 1 + c := by linarith
  have hc2 : 0 ≤ 1 - c := by linarith
  constructor
  · linear_combination (61/250) * mul_nonneg hc1 (sq_nonneg (e₀ + (575/2928) * w₀ +
      (25/732) * w₁)) +
      (61/250) * mul_nonneg hc1 (sq_nonneg (e₁ + (25/732) * w₀ + (25/2928) * w₁)) +
      (16284559/35136000) * mul_nonneg hc1 (sq_nonneg (w₀ + (2868000/16284559) * w₁)) +
      (88804158481/572174265024000) * mul_nonneg hc1 (sq_nonneg (w₁)) +
      (61/250) * mul_nonneg hc2 (sq_nonneg (e₀ + (275/2928) * w₀ + (-25/1464) * w₁)) +
      (61/250) * mul_nonneg hc2 (sq_nonneg (e₁ + (-25/1464) * w₀ + (25/2928) * w₁)) +
      (7763059/35136000) * mul_nonneg hc2 (sq_nonneg (w₀ + (-1449000/7763059) * w₁)) +
      (1922121582481/272762841024000) * mul_nonneg hc2 (sq_nonneg (w₁))
  · linear_combination (51/200) * mul_nonneg hc1 (sq_nonneg (e₀ + (-115/612) * w₀ +
      (-5/153) * w₁)) +
      (51/200) * mul_nonneg hc1 (sq_nonneg (e₁ + (-5/153) * w₀ + (-5/612) * w₁)) +
      (24319/1468800) * mul_nonneg hc1 (sq_nonneg (w₀ + (-124800/24319) * w₁)) +
      (1708935361/35719747200) * mul_nonneg hc1 (sq_nonneg (w₁)) +
      (51/200) * mul_nonneg hc2 (sq_nonneg (e₀ + (-55/612) * w₀ + (5/306) * w₁)) +
      (51/200) * mul_nonneg hc2 (sq_nonneg (e₁ + (5/306) * w₀ + (-5/612) * w₁)) +
      (402019/1468800) * mul_nonneg hc2 (sq_nonneg (w₀ + (61800/402019) * w₁)) +
      (282023907361/590485507200) * mul_nonneg hc2 (sq_nonneg (w₁))

/-- **Bounds on the skewed energy for `ε = 1/7` (MLS p. 195, with eq. (4.10), p. 165, and the
demo report's parameters).** For `|c| ≤ 1`:
`(3/250)(e₁² + e₂² + ė₁² + ė₂²) ≤ ½ ėᵀMė + ½|e|² + (1/7) eᵀMė ≤ (26/25)(e₁² + e₂² + ė₁² + ė₂²)`. -/
theorem demoArm_energy_bounds_four (e₀ e₁ w₀ w₁ c : ℝ) (hc : |c| ≤ 1) :
    3 / 250 * (e₀ ^ 2 + e₁ ^ 2 + w₀ ^ 2 + w₁ ^ 2) ≤
        1 / 2 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) + (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) +
          1 / 12 * (w₁ * w₁)) + 1 / 2 * (e₀ ^ 2 + e₁ ^ 2) +
        1 / 7 * ((17 / 12 + 1 / 2 * c) * (e₀ * w₀) + (1 / 12 + 1 / 4 * c) * (e₀ * w₁ + e₁ * w₀) +
          1 / 12 * (e₁ * w₁)) ∧
      1 / 2 * ((17 / 12 + 1 / 2 * c) * (w₀ * w₀) + (1 / 12 + 1 / 4 * c) * (w₀ * w₁ + w₁ * w₀) +
          1 / 12 * (w₁ * w₁)) + 1 / 2 * (e₀ ^ 2 + e₁ ^ 2) +
        1 / 7 * ((17 / 12 + 1 / 2 * c) * (e₀ * w₀) + (1 / 12 + 1 / 4 * c) * (e₀ * w₁ + e₁ * w₀) +
          1 / 12 * (e₁ * w₁)) ≤ 26 / 25 * (e₀ ^ 2 + e₁ ^ 2 + w₀ ^ 2 + w₁ ^ 2) := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  have hc1 : 0 ≤ 1 + c := by linarith
  have hc2 : 0 ≤ 1 - c := by linarith
  constructor
  · linear_combination (61/250) * mul_nonneg hc1 (sq_nonneg (e₀ + (2875/10248) * w₀ +
      (125/2562) * w₁)) + (61/250) * mul_nonneg hc1 (sq_nonneg (e₁ + (125/2562) * w₀ +
      (125/10248) * w₁)) + (195142879/430416000) * mul_nonneg hc1 (sq_nonneg (w₀ +
      (34368000/195142879) * w₁)) +
      (263188577809/1714135049136000) * mul_nonneg hc1 (sq_nonneg (w₁)) +
      (61/250) * mul_nonneg hc2 (sq_nonneg (e₀ + (1375/10248) * w₀ + (-125/5124) * w₁)) +
      (61/250) * mul_nonneg hc2 (sq_nonneg (e₁ + (-125/5124) * w₀ + (125/10248) * w₁)) +
      (94101379/430416000) * mul_nonneg hc2 (sq_nonneg (w₀ + (-17559000/94101379) * w₁)) +
      (5818785293809/826586513136000) * mul_nonneg hc2 (sq_nonneg (w₁))
  · linear_combination (27/100) * mul_nonneg hc1 (sq_nonneg (e₀ + (-575/2268) * w₀ +
      (-25/567) * w₁)) + (27/100) * mul_nonneg hc1 (sq_nonneg (e₁ + (-25/567) * w₀ +
      (-25/2268) * w₁)) + (437299/19051200) * mul_nonneg hc1 (sq_nonneg (w₀ +
      (-1647600/437299) * w₁)) + (29374708849/170021851200) * mul_nonneg hc1 (sq_nonneg (w₁)) +
      (27/100) * mul_nonneg hc2 (sq_nonneg (e₀ + (-275/2268) * w₀ + (25/1134) * w₁)) +
      (27/100) * mul_nonneg hc2 (sq_nonneg (e₁ + (25/1134) * w₀ + (-25/2268) * w₁)) +
      (5462599/19051200) * mul_nonneg hc2 (sq_nonneg (w₀ + (808800/5462599) * w₁)) +
      (1046460831649/2123858491200) * mul_nonneg hc2 (sq_nonneg (w₁))

/-- Each coordinate squared is at most the square of the sup norm on `ℝ²`. -/
private theorem sq_apply_le_sq_norm (v : Fin 2 → ℝ) (i : Fin 2) : v i ^ 2 ≤ ‖v‖ ^ 2 := by
  have h : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- The square of the sup norm on `ℝ²` is at most the sum of the squares of the coordinates. -/
private theorem sq_norm_le_sum_sq (v : Fin 2 → ℝ) : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
  have h : ‖v‖ ≤ √(v 0 ^ 2 + v 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr ?_
    rw [Fin.forall_fin_two, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨Real.abs_le_sqrt (by nlinarith [sq_nonneg (v 1)]),
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (v 0)])⟩
  calc ‖v‖ ^ 2 ≤ (√(v 0 ^ 2 + v 1 ^ 2)) ^ 2 := by gcongr
    _ = v 0 ^ 2 + v 1 ^ 2 := Real.sq_sqrt (by positivity)

/-- The square of the sup norm of a state `(e, ė)` is at most the sum of the four squares. -/
private theorem sq_norm_pair_le (e w : Fin 2 → ℝ) :
    ‖(e, w)‖ ^ 2 ≤ e 0 ^ 2 + e 1 ^ 2 + w 0 ^ 2 + w 1 ^ 2 := by
  have h := Control.sq_norm_prod_le (e, w)
  have he := sq_norm_le_sum_sq e
  have hw := sq_norm_le_sum_sq w
  simp only at h
  linarith

/-- The sum of the four squares of a state `(e, ė)` is at most four times its sup norm squared. -/
private theorem sum_sq_le_four_sq_norm_pair (e w : Fin 2 → ℝ) :
    e 0 ^ 2 + e 1 ^ 2 + w 0 ^ 2 + w 1 ^ 2 ≤ 4 * ‖(e, w)‖ ^ 2 := by
  have he : ‖e‖ ^ 2 ≤ ‖(e, w)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (e, w)) 2
  have hw : ‖w‖ ^ 2 ≤ ‖(e, w)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (e, w)) 2
  linarith [sq_apply_le_sq_norm e 0, sq_apply_le_sq_norm e 1, sq_apply_le_sq_norm w 0,
    sq_apply_le_sq_norm w 1]

/-- **The energy of Proposition 4.9 on a sup-norm ball (MLS p. 193, with eq. (4.10), p. 165, and
the demo report's parameters).** For the demo arm with `K_p = I`, at every set point `θ_d`, the
energy `½ ėᵀM(θ_d + e)ė + ½|e|²` (`augmentedEnergy` with `ε = 0`) is at most `(7/3)‖(e, ė)‖²`
(sup norm), from `ėᵀMė ≤ (8/3)‖ė‖²` (`demoArm_massMatrix_upper`). -/
theorem demoArm_energy_le {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48)
    (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (θd e w : Fin 2 → ℝ) :
    (planarTwoLinkModel 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne).augmentedEnergy 1 0 (θd + e) e w ≤
      7 / 3 * ‖(e, w)‖ ^ 2 := by
  rw [planarTwoLinkModel_augmentedEnergy_one]
  have hMu := demoArm_massMatrix_upper hI₁ hI₂ (θd + e) w w
  have h1 := (le_abs_self _).trans hMu
  have he : ‖e‖ ^ 2 ≤ ‖(e, w)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (e, w)) 2
  have hw : ‖w‖ ^ 2 ≤ ‖(e, w)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (e, w)) 2
  have h0 := sq_apply_le_sq_norm e 0
  have h2 := sq_apply_le_sq_norm e 1
  nlinarith

/-- **The energy of Proposition 4.9 bounds the second joint's position error (MLS p. 193, with
eq. (4.10), p. 165, and the demo report's parameters).** For the demo arm with `K_p = I`:
`e₂² ≤ 2 (½ ėᵀM(q)ė + ½|e|²)` at every configuration `q` (`e₂ = e 1`), since `M(q)` is positive
semidefinite (`demoArm_massMatrix_lower`). -/
theorem demoArm_sq_le_energy {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48)
    (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (q e w : Fin 2 → ℝ) :
    e 1 ^ 2 ≤
      2 * (planarTwoLinkModel 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne).augmentedEnergy 1 0 q e w := by
  rw [planarTwoLinkModel_augmentedEnergy_one]
  have hl := demoArm_massMatrix_lower hI₁ hI₂ q w
  nlinarith [sq_nonneg (e 0), sq_nonneg ‖w‖]

/-- **Sharper exponential constants for the demo's closed loop on initial errors below `8` (MLS
Proposition 4.10, p. 194, at a constant set point; Theorem 4.5, pp. 183–184; Definition 4.3,
p. 180; the demo report's parameters).** For every set point `θ_d`, the demo arm under the PD law
with compensation of `N` and `K_p = K_v = I` has the exponential bound with constants `C = 19` and
`α = 1/12` at `(θ_d, 0)` on the initial state errors smaller than `8` (sup norm on `(θ, θ̇)`), for
any gravity data, joint forces and moments about the other axes. -/
theorem demoArm_exponentialBoundOn_sharp {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12)
    (hI₂ : I₂ 2 = 1 / 48) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (θd : Fin 2 → ℝ) :
    ExponentialBoundOn (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne θd) (θd, 0) 19 (1 / 12)
      8 := by
  set P := planarTwoLinkModel 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne with hP
  have hMeq : ∀ q, P.M q = (planarTwoLinkArm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂).massMatrix q :=
    fun q => by rw [hP, planarTwoLinkModel_M]
  have hsymm : ∀ k, (P.chain.linkInertia k).IsSymm :=
    planarTwoLinkArm_linkInertia_isSymm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂
  have hM : ∀ q, (P.M q).PosDef := by
    intro q
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hMeq, planarTwoLinkArm_massMatrix]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
    · have hl := demoArm_massMatrix_lower hI₁ hI₂ q x
      rw [← hMeq] at hl
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [star_trivial]
      nlinarith
  have hKv : ∀ w : Fin 2 → ℝ, 0 ≤ w ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) := by
    intro w
    rw [Matrix.one_mulVec]
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have key := P.exponentialBoundOn_pdCompensatedTorque_of_sublevel hsymm hM Matrix.isSymm_one hKv
    θd (ε := 1 / 10) (k := 1 / 6) (a₁ := 3 / 250) (a₂ := 101 / 25) (E₀ := 448 / 3) (ρ := 8)
    (C := 19)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun e w h => by
      have h1 := demoArm_energy_le hI₁ hI₂ g up Ne θd e w
      have h2 : ‖(e, w)‖ ^ 2 ≤ 8 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h.le 2
      linarith)
    (fun e w _ => by
      rw [planarTwoLinkModel_augmentedEnergy_one, planarTwoLinkArm_dotProduct_massMatrix_mulVec,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec, hI₁, hI₂]
      have h1 := (demoArm_energy_bounds_eight (e 0) (e 1) (w 0) (w 1) (Real.cos ((θd + e) 1))
        (Real.abs_cos_le_one _)).1
      linear_combination h1 + 3 / 250 * sq_norm_pair_le e w)
    (fun e w _ => by
      rw [planarTwoLinkModel_augmentedEnergy_one, planarTwoLinkArm_dotProduct_massMatrix_mulVec,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec, hI₁, hI₂]
      have h1 := (demoArm_energy_bounds_eight (e 0) (e 1) (w 0) (w 1) (Real.cos ((θd + e) 1))
        (Real.abs_cos_le_one _)).2
      linear_combination h1 + 101 / 25 / 4 * sum_sq_le_four_sq_norm_pair e w)
    (fun e w hE => by
      have hs := demoArm_sq_le_energy hI₁ hI₂ g up Ne (θd + e) e w
      have he : |e 1| ≤ 35 / 2 := by
        have h1 : e 1 ^ 2 ≤ (35 / 2) ^ 2 := by nlinarith
        have h2 := sq_le_sq.mp h1
        rwa [abs_of_pos (by norm_num : (0 : ℝ) < 35 / 2)] at h2
      have hp : |Real.sin ((θd + e) 1) * e 1| ≤ 35 / 2 := by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans he
      rw [planarTwoLinkModel_augmentedEnergyRate_one_one, planarTwoLinkModel_augmentedEnergy_one,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec, hI₁, hI₂]
      linear_combination demoArm_rate_le_eight (e 0) (e 1) (w 0) (w 1) (Real.cos ((θd + e) 1))
        (Real.sin ((θd + e) 1) * e 1) (Real.abs_cos_le_one _) hp)
  rwa [show (1 / 6 : ℝ) / 2 = 1 / 12 by norm_num] at key

/-- **Sharper exponential constants for the demo's closed loop on initial errors below `4` (MLS
Proposition 4.10, p. 194, at a constant set point; Theorem 4.5, pp. 183–184; Definition 4.3,
p. 180; the demo report's parameters).** As `demoArm_exponentialBoundOn_sharp`, with `C = 19` and
`α = 1/8` on the initial state errors smaller than `4` (sup norm). -/
theorem demoArm_exponentialBoundOn_sharp_four {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12)
    (hI₂ : I₂ 2 = 1 / 48) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (θd : Fin 2 → ℝ) :
    ExponentialBoundOn (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne θd) (θd, 0) 19 (1 / 8)
      4 := by
  set P := planarTwoLinkModel 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne with hP
  have hMeq : ∀ q, P.M q = (planarTwoLinkArm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂).massMatrix q :=
    fun q => by rw [hP, planarTwoLinkModel_M]
  have hsymm : ∀ k, (P.chain.linkInertia k).IsSymm :=
    planarTwoLinkArm_linkInertia_isSymm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂
  have hM : ∀ q, (P.M q).PosDef := by
    intro q
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hMeq, planarTwoLinkArm_massMatrix]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
    · have hl := demoArm_massMatrix_lower hI₁ hI₂ q x
      rw [← hMeq] at hl
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [star_trivial]
      nlinarith
  have hKv : ∀ w : Fin 2 → ℝ, 0 ≤ w ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) := by
    intro w
    rw [Matrix.one_mulVec]
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have key := P.exponentialBoundOn_pdCompensatedTorque_of_sublevel hsymm hM Matrix.isSymm_one hKv
    θd (ε := 1 / 7) (k := 1 / 4) (a₁ := 3 / 250) (a₂ := 104 / 25) (E₀ := 112 / 3) (ρ := 4)
    (C := 19)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun e w h => by
      have h1 := demoArm_energy_le hI₁ hI₂ g up Ne θd e w
      have h2 : ‖(e, w)‖ ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h.le 2
      linarith)
    (fun e w _ => by
      rw [planarTwoLinkModel_augmentedEnergy_one, planarTwoLinkArm_dotProduct_massMatrix_mulVec,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec, hI₁, hI₂]
      have h1 := (demoArm_energy_bounds_four (e 0) (e 1) (w 0) (w 1) (Real.cos ((θd + e) 1))
        (Real.abs_cos_le_one _)).1
      linear_combination h1 + 3 / 250 * sq_norm_pair_le e w)
    (fun e w _ => by
      rw [planarTwoLinkModel_augmentedEnergy_one, planarTwoLinkArm_dotProduct_massMatrix_mulVec,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec, hI₁, hI₂]
      have h1 := (demoArm_energy_bounds_four (e 0) (e 1) (w 0) (w 1) (Real.cos ((θd + e) 1))
        (Real.abs_cos_le_one _)).2
      linear_combination h1 + 104 / 25 / 4 * sum_sq_le_four_sq_norm_pair e w)
    (fun e w hE => by
      have hs := demoArm_sq_le_energy hI₁ hI₂ g up Ne (θd + e) e w
      have he : |e 1| ≤ 35 / 4 := by
        have h1 : e 1 ^ 2 ≤ (35 / 4) ^ 2 := by nlinarith
        have h2 := sq_le_sq.mp h1
        rwa [abs_of_pos (by norm_num : (0 : ℝ) < 35 / 4)] at h2
      have hp : |Real.sin ((θd + e) 1) * e 1| ≤ 35 / 4 := by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans he
      rw [planarTwoLinkModel_augmentedEnergyRate_one_one, planarTwoLinkModel_augmentedEnergy_one,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec,
        planarTwoLinkArm_dotProduct_massMatrix_mulVec, hI₁, hI₂]
      linear_combination demoArm_rate_le_four (e 0) (e 1) (w 0) (w 1) (Real.cos ((θd + e) 1))
        (Real.sin ((θd + e) 1) * e 1) (Real.abs_cos_le_one _) hp)
  rwa [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at key

/-- **The sharper arrival time for the demo's tolerance is at most `116` s (MLS Definition 4.3,
p. 180; the demo report's parameters).** For initial state errors below `ρ = 8` and the tolerance
`0.02` (so `ε / (a + 2b) = 1/100`), `arrivalTime 19 (1/12) 8 (1/100) = 12 log 15 200 ≤ 116`, from
`15 200³ ≤ e²⁹`. -/
theorem demo_arrivalTime_sharp_le : arrivalTime 19 (1 / 12) 8 (1 / 100) ≤ 116 := by
  have hlog : Real.log (19 * 8 / (1 / 100)) ≤ 29 / 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : ((19 : ℝ) * 8 / (1 / 100)) ^ 3 ≤ Real.exp (29 / 3) ^ 3 := by
      rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * (29 / 3) = ((29 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_nat_mul]
      calc ((19 : ℝ) * 8 / (1 / 100)) ^ 3 ≤ 2.7182818283 ^ 29 := by norm_num
        _ ≤ Real.exp 1 ^ 29 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 29
    exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num)).mp h1
  refine max_le (by norm_num) ?_
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **The sharper arrival time for initial errors below `4` is at most `72` s (MLS Definition 4.3,
p. 180; the demo report's parameters).** `arrivalTime 19 (1/8) 4 (1/100) = 8 log 7 600 ≤ 72`, from
`7 600 ≤ e⁹`. -/
theorem demo_arrivalTime_sharp_four_le : arrivalTime 19 (1 / 8) 4 (1 / 100) ≤ 72 := by
  have hlog : Real.log (19 * 4 / (1 / 100)) ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    calc (19 : ℝ) * 4 / (1 / 100) ≤ 2.7182818283 ^ 9 := by norm_num
      _ ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 9
  refine max_le (by norm_num) ?_
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **Design statement with the sharper constants (MLS eq. (3.16), p. 98, Proposition 4.10, p. 194;
the demo report's parameters and conventions).** For the demo's link lengths, period `h = 1/2`,
tolerance `1/50`, initial state errors below `8` and an age bound of at least `232` periods
(`116` s), the end effector is within `1/50` of every commanded target at the sample
`t₀ + bound · h` at which the age reaches the bound, for every run, commanded target and solution
of the demo's closed loop at its set point from `t₀ ≥ 0`. -/
theorem demo_planarDist_le_at_bound_of_run_sharp {p : Params} (hpa : p.a = 1) (hpb : p.b = 1 / 2)
    (hN : 232 ≤ p.bound) {acts : List Action} {s : State}
    (hrun : run p State.init acts = some s) {tgt : Target} (htgt : tgt ∈ s.commanded)
    {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hx : IsSolution (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne (setPoint p tgt)) t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < 8) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + p.bound * (1 / 2))).1)
      ![(tgt.1 : ℝ), tgt.2] ≤ 1 / 50 := by
  have ha : 0 < p.a := by rw [hpa]; norm_num
  have hb : 0 < p.b := by rw [hpb]; norm_num
  have hab : p.a ≠ p.b := by rw [hpa, hpb]; norm_num
  have hL : ((p.a : ℝ) + 2 * p.b) = 2 := by rw [hpa, hpb]; norm_num
  refine planarDist_le_at_sample_of_run ha hb hab hrun htgt
    (demoArm_exponentialBoundOn_sharp hI₁ hI₂ g up Ne (setPoint p tgt)) ht₀ hx hx₀
    (by norm_num : (0 : ℝ) < 1 / 50) ?_
  rw [hL]
  have hN' : (232 : ℝ) ≤ p.bound := by exact_mod_cast hN
  calc arrivalTime 19 _ 8 (1 / 50 / 2) = arrivalTime 19 _ 8 (1 / 100) := by norm_num
    _ ≤ 116 := demo_arrivalTime_sharp_le
    _ ≤ p.bound * (1 / 2) := by linarith

/-- **Design statement with the sharper constants for initial errors below `4` (MLS eq. (3.16),
p. 98, Proposition 4.10, p. 194; the demo report's parameters and conventions).** As
`demo_planarDist_le_at_bound_of_run_sharp`, for initial state errors below `4` and an age bound of
at least `144` periods (`72` s). -/
theorem demo_planarDist_le_at_bound_of_run_sharp_four {p : Params} (hpa : p.a = 1)
    (hpb : p.b = 1 / 2) (hN : 144 ≤ p.bound) {acts : List Action} {s : State}
    (hrun : run p State.init acts = some s) {tgt : Target} (htgt : tgt ∈ s.commanded)
    {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hx : IsSolution (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne (setPoint p tgt)) t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < 4) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + p.bound * (1 / 2))).1)
      ![(tgt.1 : ℝ), tgt.2] ≤ 1 / 50 := by
  have ha : 0 < p.a := by rw [hpa]; norm_num
  have hb : 0 < p.b := by rw [hpb]; norm_num
  have hab : p.a ≠ p.b := by rw [hpa, hpb]; norm_num
  have hL : ((p.a : ℝ) + 2 * p.b) = 2 := by rw [hpa, hpb]; norm_num
  refine planarDist_le_at_sample_of_run ha hb hab hrun htgt
    (demoArm_exponentialBoundOn_sharp_four hI₁ hI₂ g up Ne (setPoint p tgt)) ht₀ hx hx₀
    (by norm_num : (0 : ℝ) < 1 / 50) ?_
  rw [hL]
  have hN' : (144 : ℝ) ≤ p.bound := by exact_mod_cast hN
  calc arrivalTime 19 _ 4 (1 / 50 / 2) = arrivalTime 19 _ 4 (1 / 100) := by norm_num
    _ ≤ 72 := demo_arrivalTime_sharp_four_le
    _ ≤ p.bound * (1 / 2) := by linarith

end RoboLean.Demo
