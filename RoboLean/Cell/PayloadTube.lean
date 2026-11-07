import RoboLean.Cell.AssuredTorque

/-!
# The full tracking tube as the first-exit band, and the tube bounds along a linked move

`tube_invariant_on_accel_right_of_near` requires the acceleration bound on the disturbance only
while every joint is within `η > δ` of the reference. Here the band is the full tube
`InTube ω η`: the bound is required only while `|eᵢ| ≤ η` and `|zᵢ| ≤ ω η` for every joint, with
`e = x − r` and `z = ẋ − ṙ + ω e`. Inside that tube both the configuration and the velocity of
the arm are known up to `η`, which is what a bound on a configuration- and velocity-dependent
disturbance (a payload, friction) needs.

At the gain `ω = 80` rad/s and the tube radius `η = 301/10000` rad, along the quintic reference of
duration `T = 2` s between two waypoints linked by the supervisor's link test, every state in the
tube keeps the forearm's mass centre at horizontal distance at least `29/80` m from the base axis,
the commanded acceleration `r̈ − 2ω (θ̇ − ṙ) − ω² (θ − r)` is at most `583` rad/s² on the base and
`580` rad/s² on the shoulder and the elbow, and the joint speed is at most `15/2` rad/s on the base
and `29/5` rad/s on the shoulder and the elbow. The numbers come from `|eᵢ| ≤ η`,
`|zᵢ| ≤ ω η`, the joint envelope of the cells (`162°` of base travel, `57°` for the shoulder and
the elbow) and the speed and acceleration bounds of the quintic reference.

**Formalized.**

* `tube_invariant_on_accel_right_of_inTube`: the tube with right derivatives, the acceleration
  bound required only while the motion is in the tube of radius `η > δ` (first exit).
* `Loop.payload_tube_bounds`: the reach, the commanded acceleration and the joint speeds inside
  the tube of radius `301/10000` rad around a linked move at the design gain.

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); speeds in rad/s, accelerations in rad/s², time in seconds. The computed torque law is
MLS eq. (4.49), p. 191; the scene, the reference and the bounds are design statements, not from
MLS. Nothing here concerns a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- **Tube invariance with right derivatives and the acceleration bound required only inside a
wider tube (a design statement, not from MLS; the law is MLS eq. (4.49), p. 191, along a motion
as on p. 301).** The statement of `tube_invariant_on_accel_right` with `δ < η`, where the bound
`|wᵢ| ≤ ω² δ` for every `w` with `M(s) w = d(s)` (rad/s²) is required only at the instants
`s ∈ (t₀, t₁]` where the motion is in the tube `InTube ω η` around the reference: for every
joint, `|xᵢ(s) − rᵢ(s)| ≤ η` (rad) and `|ẋᵢ(s) − ṙᵢ(s) + ω (xᵢ(s) − rᵢ(s))| ≤ ω η` (rad/s). The
proof is a first-exit argument: up to and including the first time some joint reaches the
boundary of the `η`-tube the bound holds, so the tube of radius `δ < η` holds, which keeps the
motion strictly inside the `η`-tube. -/
theorem tube_invariant_on_accel_right_of_inTube {n : ℕ} {ω δ η t₀ t₁ : ℝ} (hω : 0 < ω)
    (hδη : δ < η) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x (x' s) (Ici s) s)
    (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x' (x'' s) (Ici s) s)
    (hw : ∀ s ∈ Ioc t₀ t₁, InTube ω η (x s) (x' s) (r s) (r' s) →
      ∀ w, Mt s *ᵥ w = d s → ∀ i, |w i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) ∧
      ∀ i, |x' t i - r' t i| ≤ 2 * ω * δ := by
  have hxc : ContinuousOn x (Icc t₀ t₁) := continuous_fst.comp_continuousOn hc
  have hxc' : ContinuousOn x' (Icc t₀ t₁) := continuous_snd.comp_continuousOn hc
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hrc' : Continuous r' := continuous_iff_continuousAt.mpr fun t => (hr' t).continuousAt
  -- the error `e` and the filtered error `z` as one map, continuous on `[t₀, t₁]`
  set F : ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun s => (x s - r s, x' s - r' s + ω • (x s - r s)) with hF
  have hFc : ContinuousOn F (Icc t₀ t₁) :=
    (hxc.sub hrc.continuousOn).prodMk ((hxc'.sub hrc'.continuousOn).add
      ((hxc.sub hrc.continuousOn).const_smul ω))
  have hF1 : ∀ s i, (F s).1 i = x s i - r s i := fun _ _ => rfl
  have hF2 : ∀ s i, (F s).2 i = x' s i - r' s i + ω * (x s i - r s i) := fun _ _ => rfl
  -- inside the tube of radius `δ` no joint is at the boundary of the tube of radius `η`
  have hωδη : ω * δ < ω * η := mul_lt_mul_of_pos_left hδη hω
  have hinner : ∀ s, InTube ω δ (x s) (x' s) (r s) (r' s) → ∀ j,
      ¬(η ≤ |x s j - r s j| ∨ ω * η ≤ |x' s j - r' s j + ω * (x s j - r s j)|) := by
    intro s hs j hj
    rcases hj with hj | hj
    · linarith [(hs j).1]
    · linarith [(hs j).2]
  -- the closed set of times in `[t₀, t₁]` where the motion is in the tube of radius `η`
  set K : Set ℝ := Icc t₀ t₁ ∩
    F ⁻¹' (⋂ i, ({p | |p.1 i| ≤ η} ∩ {p | |p.2 i| ≤ ω * η})) with hK
  have hKmem : ∀ s, s ∈ K ↔ s ∈ Icc t₀ t₁ ∧ InTube ω η (x s) (x' s) (r s) (r' s) := by
    intro s
    simp only [hK, mem_inter_iff, mem_preimage, mem_iInter, mem_ofPred_eq, hF1, hF2, InTube]
  have hKc : IsClosed K := hFc.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_iInter fun i =>
      (isClosed_le ((continuous_apply i).comp continuous_fst).abs continuous_const).inter
        (isClosed_le ((continuous_apply i).comp continuous_snd).abs continuous_const))
  -- first exit: the motion stays in the tube of radius `η` on `[t₀, t₁]`
  have hband : ∀ s ∈ Icc t₀ t₁, InTube ω η (x s) (x' s) (r s) (r' s) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₁, hs₁, hn⟩ := hcon
    -- the closed set of times in `[t₀, t₁]` where some joint is at or beyond the boundary
    set S : Set ℝ := Icc t₀ t₁ ∩
      F ⁻¹' (⋃ i, ({p | η ≤ |p.1 i|} ∪ {p | ω * η ≤ |p.2 i|})) with hS
    have hmem : ∀ s, s ∈ S ↔ s ∈ Icc t₀ t₁ ∧
        ∃ i, η ≤ |x s i - r s i| ∨ ω * η ≤ |x' s i - r' s i + ω * (x s i - r s i)| := by
      intro s
      simp only [hS, mem_inter_iff, mem_preimage, mem_iUnion, mem_union, mem_ofPred_eq, hF1, hF2]
    have hSc : IsClosed S := hFc.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_iUnion_of_finite fun i =>
        (isClosed_le continuous_const ((continuous_apply i).comp continuous_fst).abs).union
          (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd).abs))
    have hnotS : ∀ s ∈ Icc t₀ t₁, s ∉ S → InTube ω η (x s) (x' s) (r s) (r' s) := by
      intro s hs hnS
      rw [hmem] at hnS
      push Not at hnS
      exact fun i => ⟨(hnS hs i).1.le, (hnS hs i).2.le⟩
    have hne : S.Nonempty := ⟨s₁, by_contra fun h => hn (hnotS s₁ hs₁ h)⟩
    have hbdd : BddBelow S := ⟨t₀, fun s hs => ((hmem s).1 hs).1.1⟩
    obtain ⟨hτI, j, hj⟩ := (hmem _).1 (hSc.csInf_mem hne hbdd)
    -- `t₀` is before the first exit: at `t₀` the motion is in the tube of radius `δ < η`
    have hlt : t₀ < sInf S := by
      rcases hτI.1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hj
        exact hinner t₀ h₀ j hj
    -- before the first exit the motion is in the tube of radius `η`
    have hbefore : Ico t₀ (sInf S) ⊆ K := by
      intro s hs
      have hsI : s ∈ Icc t₀ t₁ := ⟨hs.1, hs.2.le.trans hτI.2⟩
      exact (hKmem s).2 ⟨hsI, hnotS s hsI (notMem_of_lt_csInf hs.2 hbdd)⟩
    -- at the first exit it is still in that tube (closure of `[t₀, τ)`)
    have hτK : sInf S ∈ K := by
      have hcl : closure (Ico t₀ (sInf S)) ⊆ K := closure_minimal hbefore hKc
      rw [closure_Ico hlt.ne] at hcl
      exact hcl ⟨hlt.le, le_rfl⟩
    have hsub : ∀ s ∈ Ioc t₀ (sInf S), s ∈ Ioc t₀ t₁ := fun s hs => ⟨hs.1, hs.2.trans hτI.2⟩
    have hnear : ∀ s ∈ Ioc t₀ (sInf S), InTube ω η (x s) (x' s) (r s) (r' s) := by
      intro s hs
      rcases hs.2.lt_or_eq with h | h
      · exact ((hKmem s).1 (hbefore ⟨hs.1.le, h⟩)).2
      · rw [h]
        exact ((hKmem _).1 hτK).2
    have htube := tube_invariant_on_accel_right hω hr hr'
      (hc.mono (Icc_subset_Icc_right hτI.2)) (fun s hs => hx s (hsub s hs))
      (fun s hs => hx' s (hsub s hs)) (fun s hs => hw s (hsub s hs) (hnear s hs))
      (fun s hs => hE s (hsub s hs)) h₀ (sInf S) ⟨hlt.le, le_rfl⟩
    exact hinner _ htube.1 j hj
  exact tube_invariant_on_accel_right hω hr hr' hc hx hx'
    (fun s hs => hw s hs (hband s (Ioc_subset_Icc_self hs))) hE h₀

/-- If the shoulder and the forearm are both within `π/3` of the horizontal,
`|θ₁| ≤ π/3` and `|θ₁ + θ₂| ≤ π/3` (radians), the forearm's mass centre is at horizontal
distance at least `29/80` m from the base axis. -/
private theorem reach_of_abs_le_pi_div_three {θ : Fin 3 → ℝ}
    (h₁ : |θ 1| ≤ Real.pi / 3) (h₁₂ : |θ 1 + θ 2| ≤ Real.pi / 3) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  have hc : ∀ y : ℝ, |y| ≤ Real.pi / 3 → 1 / 2 ≤ Real.cos y := fun y hy => by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hy
  linarith [hc _ h₁, hc _ h₁₂]

end Cell

namespace Cell.Loop

open Set Supervisor

/-- Every configuration within `1/10` rad (each joint) of a point of the segment between two
waypoints linked by the supervisor's link test keeps the forearm's mass centre at horizontal
distance at least `29/80` m from the base axis: such a configuration lies in a cell inflated by
`1/10`, hence in the joint envelope (shoulder at most `51°` in magnitude, shoulder plus elbow at
most `57°` in magnitude). -/
private theorem reach_linked {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) {p : Fin 3 → ℝ}
    (hp : p ∈ segment ℝ (DegPoint.toRad a) (DegPoint.toRad g)) {θ : Fin 3 → ℝ}
    (hθ : ∀ i, |θ i - p i| ≤ 1 / 10) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  obtain ⟨B, hB, ha, hb⟩ := sceneLinked_of_linked_eq_true hag
  have hpB : p ∈ B.radSet 0 :=
    (B.convex_radSet 0).segment_subset (DegBox.toRad_mem_radSet ha) (DegBox.toRad_mem_radSet hb) hp
  have hθE := radSet_subset_jointEnvelope B hB (DegBox.mem_radSet_of_abs_sub_le hpB hθ)
  have hπ := Real.pi_pos
  obtain ⟨h11, h12⟩ := hθE 1
  obtain ⟨h21, h22⟩ := hθE 2
  simp [DegPoint.toRad, degToRad, jointEnvelope] at h11 h12 h21 h22
  apply reach_of_abs_le_pi_div_three
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- The travel of a linked move in each joint: two waypoints linked by the supervisor's link test
lie in one cell, hence in the joint envelope, so they differ by at most `162°` (`9π/10` rad) on
the base and `57°` (`19π/60` rad) on the shoulder and the elbow. -/
private theorem abs_toRad_sub_le_of_linked {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) (i : Fin 3) :
    |DegPoint.toRad g i - DegPoint.toRad a i| ≤ ![9 / 10, 19 / 60, 19 / 60] i * Real.pi := by
  obtain ⟨B, hB, ha, hb⟩ := sceneLinked_of_linked_eq_true hag
  have hE : ∀ w : Waypoint, B.Contains w → DegPoint.toRad w ∈ jointEnvelope.radSet 0 :=
    fun w hw => radSet_subset_jointEnvelope B hB
      (B.radSet_mono (by norm_num) (DegBox.toRad_mem_radSet hw))
  have hπ := Real.pi_pos
  obtain ⟨h1, h2⟩ := hE a ha i
  obtain ⟨h3, h4⟩ := hE g hb i
  rw [abs_le]
  fin_cases i <;> simp [DegPoint.toRad, degToRad, jointEnvelope] at h1 h2 h3 h4 ⊢ <;>
    constructor <;> linarith

/-- **The tube bounds along a linked move at the design gain (a design statement, not from MLS;
the commanded acceleration is that of the computed torque law, MLS eq. (4.49), p. 191, with
`K_p = ω² I` and `K_v = 2ω I`).** Let `a, g` be waypoints linked by the supervisor's link test
for the loop data `openCellParams h T δa va`, `r` the quintic reference from `a` to `g` admitted
at `t₀` with duration `2` s, and `(θ, θ̇)` (rad, rad/s) in the tube `InTube 80 (301/10000)`
around `(r(s), ṙ(s))` at some time `s`. Then the forearm's mass centre is at horizontal distance
at least `29/80` m from the base axis; the commanded acceleration
`r̈ᵢ(s) − 160 (θ̇ᵢ − ṙᵢ(s)) − 6400 (θᵢ − rᵢ(s))` is at most `583` rad/s² in magnitude on the base
and `580` rad/s² on the shoulder and the elbow; and the joint speed `|θ̇ᵢ|` is at most `15/2`
rad/s on the base and `29/5` rad/s on the shoulder and the elbow. -/
theorem payload_tube_bounds {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) {t₀ s : ℝ} {θ θ' : Fin 3 → ℝ}
    (hin : Cell.InTube 80 (301 / 10000) θ θ'
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) ∧
    (∀ i, |moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s i -
        2 * 80 * (θ' i - moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s i) -
        80 ^ 2 * (θ i - moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s i)| ≤
      ![583, 580, 580] i) ∧
    ∀ i, |θ' i| ≤ ![15 / 2, 29 / 5, 29 / 5] i := by
  have hπ := Real.pi_pos
  have hπ' := Real.pi_lt_d4
  refine ⟨reach_linked hag (moveRef_mem_segment _ _ _ _ _)
    (fun i => (hin i).1.trans (by norm_num)), fun i => ?_, fun i => ?_⟩
  · have h2 := abs_moveRefDeriv2_apply_le (a := DegPoint.toRad a) (b := DegPoint.toRad g)
      (t₀ := t₀) (by norm_num : (0 : ℝ) < 2) s i
    have hg := abs_toRad_sub_le_of_linked hag i
    have hk : 6 * (![9 / 10, 19 / 60, 19 / 60] i * Real.pi) / 2 ^ 2 + 19200 * (301 / 10000) ≤
        ![583, 580, 580] i := by
      fin_cases i <;> norm_num <;> linarith
    obtain ⟨he, hz⟩ := hin i
    rw [abs_le] at he hz h2 ⊢
    constructor <;> linarith
  · have h1 := abs_moveRefDeriv_apply_le (a := DegPoint.toRad a) (b := DegPoint.toRad g)
      (t₀ := t₀) (by norm_num : (0 : ℝ) < 2) s i
    have hg := abs_toRad_sub_le_of_linked hag i
    have hk : 15 / 8 * (![9 / 10, 19 / 60, 19 / 60] i * Real.pi) / 2 + 160 * (301 / 10000) ≤
        ![15 / 2, 29 / 5, 29 / 5] i := by
      fin_cases i <;> norm_num <;> linarith
    obtain ⟨he, hz⟩ := hin i
    rw [abs_le] at he hz h1 ⊢
    constructor <;> linarith

end Cell.Loop
end RoboLean
