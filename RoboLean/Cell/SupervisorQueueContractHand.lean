import Mathlib.Data.List.Chain
import RoboLean.Cell.SupervisorQueue

/-!
# The queue supervisor's contract, proved by hand

This file proves the contract `RoboLean.Cell.SupervisorQueue.Contract p` of the queue supervisor
for every parameter value `p` by a hand-written inductive invariant `QueueInv` on the program's
state. The queue is the list `requested` itself, so no design relation is needed: the invariant
holds at the initial state (`QueueInv.init`), every accepted step preserves it (`QueueInv.step`),
so every state reached from the initial state satisfies it (`QueueInv.run`), and its first six
clauses are the six clauses of the contract (`contract_of_queue_invariant`).

The invariant strengthens the contract with four clauses about the queue: the head of the queue is
linked to the waypoint the arm is at while the supervisor is idle, the head is linked to every
commanded waypoint, every adjacent pair of the queue is linked, and a busy supervisor has a
commanded list of exactly one waypoint. The last clause is an addition that shortens the proof:
it gives the commanded waypoint as `front` of a busy state.

A design statement, not from MLS. Waypoints are rational degrees; the age counts ticks.
-/

namespace RoboLean.Cell.SupervisorQueue

open RoboLean.Cell.Supervisor (Waypoint State linked)

/-- **The queue invariant.** For the parameters `p`, a state `s` of the queue supervisor satisfies
the six clauses of `Contract` and four clauses about the queue `s.requested` (head first): the
head is linked to `s.current` while the supervisor is idle; the head is linked to every commanded
waypoint; every adjacent pair of the queue is linked, stated as `List.IsChain` of the link test,
which says that each element is linked to the next one; and a busy supervisor has exactly one
commanded waypoint as a list. A design statement, not from MLS; waypoints are rational degrees
and the age counts ticks. -/
structure QueueInv (p : Params) (s : State) : Prop where
  /-- A busy supervisor has exactly one commanded waypoint, linked to the waypoint the arm is
  at. -/
  busy_commanded :
    s.busy = true → ∃ w, linked p.cells s.current w = true ∧ ∀ u, u ∈ s.commanded ↔ u = w
  /-- An idle supervisor has no commanded waypoint. -/
  idle_uncommanded : s.busy = false → ∀ u, u ∉ s.commanded
  /-- The age is at most the bound. -/
  age_le : s.age ≤ p.bound
  /-- An idle supervisor has age zero. -/
  idle_age : s.busy = false → s.age = 0
  /-- A faulted supervisor is idle. -/
  faulted_idle : s.faulted = true → s.busy = false
  /-- Every commanded waypoint is linked to the waypoint the arm is at. -/
  commanded_linked : ∀ u ∈ s.commanded, linked p.cells s.current u = true
  /-- The head of the queue is linked to the waypoint the arm is at while the supervisor is
  idle. -/
  head_linked_idle :
    ∀ h, s.requested.head? = some h → s.busy = false → linked p.cells s.current h = true
  /-- The head of the queue is linked to every commanded waypoint. -/
  head_linked_busy :
    ∀ h, s.requested.head? = some h → ∀ c ∈ s.commanded, linked p.cells c h = true
  /-- Every waypoint of the queue is linked to the next one. -/
  next_linked : s.requested.IsChain (fun a b => linked p.cells a b = true)
  /-- A busy supervisor's commanded list is a single waypoint. -/
  busy_single : s.busy = true → ∃ w, s.commanded = [w]

/-- The queue invariant holds at the initial state at `p.home`: no request, no command, idle, not
faulted, age zero. A design statement, not from MLS. -/
theorem QueueInv.init (p : Params) :
    QueueInv p (RoboLean.Cell.Supervisor.State.init p.home) where
  busy_commanded h := Bool.noConfusion h
  idle_uncommanded _ _ h := List.not_mem_nil h
  age_le := Nat.zero_le _
  idle_age _ := rfl
  faulted_idle h := Bool.noConfusion h
  commanded_linked _ h := absurd h List.not_mem_nil
  head_linked_idle _ h := by simp [RoboLean.Cell.Supervisor.State.init] at h
  head_linked_busy _ h := by simp [RoboLean.Cell.Supervisor.State.init] at h
  next_linked := List.IsChain.nil
  busy_single h := Bool.noConfusion h

/-- A waypoint `x` linked to `front s` is linked to the waypoint the arm is at when the supervisor
is idle, and to every commanded waypoint, in a state that satisfies the queue invariant. A design
statement, not from MLS. -/
theorem QueueInv.of_front {p : Params} {s : State} {x : Waypoint} (hs : QueueInv p s)
    (hx : linked p.cells (front s) x = true) :
    (s.busy = false → linked p.cells s.current x = true) ∧
      ∀ c ∈ s.commanded, linked p.cells c x = true := by
  cases hb : s.busy
  · have hf : front s = s.current := by simp [front, hb]
    exact ⟨fun _ => hf ▸ hx, fun c hc => absurd hc (hs.idle_uncommanded hb c)⟩
  · obtain ⟨w, hw⟩ := hs.busy_single hb
    have hf : front s = w := by simp [front, hb, hw]
    refine ⟨fun h => Bool.noConfusion h, fun c hc => ?_⟩
    rw [hw, List.mem_singleton] at hc
    exact hc ▸ hf ▸ hx

/-- An accepted step has no failing guard and leads to the effect of its action. A design
statement, not from MLS. -/
theorem blocker_eq_none_of_step {p : Params} {s s' : State} {act : Action}
    (h : SupervisorQueue.step p s act = some s') :
    act.blocker p s = none ∧ effect p s act = s' := by
  unfold SupervisorQueue.step at h
  split at h
  · simp at h
  · exact ⟨‹_›, Option.some.inj h⟩

/-- **Every accepted step preserves the queue invariant.** If a state `s` satisfies `QueueInv p`
and `step` accepts an action from `s` with the result `s'`, then `s'` satisfies `QueueInv p`. A
queued request uses the head and commanded-head clauses through `QueueInv.of_front` and extends
the chain; `admit` uses the idle-head clause for the commanded waypoint's link and the chain for
the new head; `finish` uses the commanded-head clause for the idle-head clause. A design statement,
not from MLS. -/
theorem QueueInv.step {p : Params} {s s' : State} {act : Action} (hs : QueueInv p s)
    (h : SupervisorQueue.step p s act = some s') : QueueInv p s' := by
  obtain ⟨hg, rfl⟩ := blocker_eq_none_of_step h
  cases act with
  | request w prio =>
    simp only [effect]
    split
    · rename_i hq
      cases prio with
      | normal =>
        simp only [queueable, Bool.and_eq_true, decide_eq_true_eq] at hq
        obtain ⟨⟨hl, -⟩, -⟩ := hq
        have hhead : ∀ h, (s.requested ++ [w]).head? = some h →
            (s.busy = false → linked p.cells s.current h = true) ∧
              ∀ c ∈ s.commanded, linked p.cells c h = true := by
          intro h hh
          cases hr : s.requested with
          | nil =>
            rw [hr] at hh
            simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hh
            subst hh
            have hp : pred s = front s := by simp [pred, hr]
            exact hs.of_front (hp ▸ hl)
          | cons a t =>
            rw [hr] at hh
            simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
            subst hh
            exact ⟨hs.head_linked_idle a (by simp [hr]), hs.head_linked_busy a (by simp [hr])⟩
        exact
          { busy_commanded := hs.busy_commanded
            idle_uncommanded := hs.idle_uncommanded
            age_le := hs.age_le
            idle_age := hs.idle_age
            faulted_idle := hs.faulted_idle
            commanded_linked := hs.commanded_linked
            head_linked_idle := fun h hh => (hhead h hh).1
            head_linked_busy := fun h hh => (hhead h hh).2
            next_linked := hs.next_linked.append (List.IsChain.singleton w) (by
              intro x hx y hy
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
              subst hy
              have hp : pred s = x := by simp [pred, Option.mem_def.mp hx]
              exact hp ▸ hl)
            busy_single := hs.busy_single }
      | urgent =>
        simp only [queueable, Bool.and_eq_true, decide_eq_true_eq] at hq
        obtain ⟨⟨⟨hl, hall⟩, -⟩, -⟩ := hq
        have hhead := hs.of_front hl
        exact
          { busy_commanded := hs.busy_commanded
            idle_uncommanded := hs.idle_uncommanded
            age_le := hs.age_le
            idle_age := hs.idle_age
            faulted_idle := hs.faulted_idle
            commanded_linked := hs.commanded_linked
            head_linked_idle := fun h hh => by
              simp only [List.head?_cons, Option.some.injEq] at hh
              exact hh ▸ hhead.1
            head_linked_busy := fun h hh => by
              simp only [List.head?_cons, Option.some.injEq] at hh
              exact hh ▸ hhead.2
            next_linked := hs.next_linked.cons (by
              intro y hy
              rw [Option.mem_def] at hy
              rw [hy] at hall
              simpa using hall)
            busy_single := hs.busy_single }
    · exact
        { busy_commanded := hs.busy_commanded
          idle_uncommanded := hs.idle_uncommanded
          age_le := hs.age_le
          idle_age := hs.idle_age
          faulted_idle := hs.faulted_idle
          commanded_linked := hs.commanded_linked
          head_linked_idle := hs.head_linked_idle
          head_linked_busy := hs.head_linked_busy
          next_linked := hs.next_linked
          busy_single := hs.busy_single }
  | admit =>
    simp only [Action.blocker] at hg
    cases hr : s.requested with
    | nil => simp [hr] at hg
    | cons a t =>
      have hb : s.busy = false := by
        cases hb : s.busy <;> simp_all
      have hf : s.faulted = false := by
        cases hf : s.faulted <;> simp_all
      have ha : linked p.cells s.current a = true := hs.head_linked_idle a (by simp [hr]) hb
      have hc : (a :: t).IsChain (fun a b => linked p.cells a b = true) := hr ▸ hs.next_linked
      simp only [effect, hr]
      exact
        { busy_commanded := fun _ => ⟨a, ha, fun u => List.mem_singleton⟩
          idle_uncommanded := fun h => Bool.noConfusion h
          age_le := Nat.zero_le _
          idle_age := fun h => Bool.noConfusion h
          faulted_idle := fun h => absurd (hf ▸ h) Bool.false_ne_true
          commanded_linked := fun u hu => (List.mem_singleton.mp hu) ▸ ha
          head_linked_idle := fun _ _ h => Bool.noConfusion h
          head_linked_busy := fun h hh c hcm => by
            rw [List.mem_singleton] at hcm
            subst hcm
            exact List.isChain_cons.mp hc |>.1 h hh
          next_linked := hc.tail
          busy_single := fun _ => ⟨a, rfl⟩ }
  | finish =>
    have hb : s.busy = true := by
      simp only [Action.blocker] at hg
      cases hb : s.busy <;> simp_all
    obtain ⟨w, hw⟩ := hs.busy_single hb
    simp only [effect, hw, List.headD_cons]
    exact
      { busy_commanded := fun h => Bool.noConfusion h
        idle_uncommanded := fun _ _ h => List.not_mem_nil h
        age_le := Nat.zero_le _
        idle_age := fun _ => rfl
        faulted_idle := fun _ => rfl
        commanded_linked := fun _ h => absurd h List.not_mem_nil
        head_linked_idle := fun h hh _ => hs.head_linked_busy h hh w (by simp [hw])
        head_linked_busy := fun _ _ _ h => absurd h List.not_mem_nil
        next_linked := hs.next_linked
        busy_single := fun h => Bool.noConfusion h }
  | tick =>
    simp only [Action.blocker] at hg
    have hb : s.busy = true := by
      cases hb : s.busy <;> simp_all
    have hlt : s.age < p.bound := by
      rw [hb] at hg
      by_contra hn
      simp [hn] at hg
    simp only [effect]
    exact
      { busy_commanded := hs.busy_commanded
        idle_uncommanded := hs.idle_uncommanded
        age_le := hlt
        idle_age := fun h => by simp [hb] at h
        faulted_idle := hs.faulted_idle
        commanded_linked := hs.commanded_linked
        head_linked_idle := hs.head_linked_idle
        head_linked_busy := hs.head_linked_busy
        next_linked := hs.next_linked
        busy_single := hs.busy_single }
  | timeout =>
    simp only [effect]
    exact
      { busy_commanded := fun h => Bool.noConfusion h
        idle_uncommanded := fun _ _ h => List.not_mem_nil h
        age_le := Nat.zero_le _
        idle_age := fun _ => rfl
        faulted_idle := fun _ => rfl
        commanded_linked := fun _ h => absurd h List.not_mem_nil
        head_linked_idle := fun _ h => by simp at h
        head_linked_busy := fun _ h => by simp at h
        next_linked := List.IsChain.nil
        busy_single := fun h => Bool.noConfusion h }

/-- Every state that the queue supervisor reaches by a list of accepted actions from a state that
satisfies the queue invariant satisfies it too. A design statement, not from MLS. -/
theorem QueueInv.run_from {p : Params} :
    ∀ (acts : List Action) {s₀ s : State}, QueueInv p s₀ →
      SupervisorQueue.run p s₀ acts = some s → QueueInv p s
  | [], _, _, h₀, h => by
    simp only [SupervisorQueue.run, Option.some.injEq] at h
    exact h ▸ h₀
  | act :: acts, s₀, _, h₀, h => by
    simp only [SupervisorQueue.run] at h
    split at h
    · simp at h
    · rename_i s' hstep
      exact QueueInv.run_from acts (h₀.step hstep) h

/-- **Every reachable state satisfies the queue invariant.** For the parameters `p`, every state
that the queue supervisor reaches from its initial state at `p.home` by a list of accepted actions
satisfies `QueueInv p`. A design statement, not from MLS. -/
theorem QueueInv.run {p : Params} {acts : List Action} {s : State}
    (h : SupervisorQueue.run p (RoboLean.Cell.Supervisor.State.init p.home) acts = some s) :
    QueueInv p s :=
  QueueInv.run_from acts (QueueInv.init p) h

/-- **The queue supervisor's contract, by a hand-written invariant.** For every parameter value
`p`, every state that the queue supervisor reaches from its initial state at `p.home` meets the six
clauses of `Contract p`: they are the first six clauses of the queue invariant, which every
reachable state satisfies (`QueueInv.run`). A design statement, not from MLS; waypoints are
rational degrees and the age counts ticks. -/
theorem contract_of_queue_invariant (p : Params) : Contract p := by
  intro acts s h
  have hs := QueueInv.run h
  exact ⟨hs.busy_commanded, hs.idle_uncommanded, hs.age_le, hs.idle_age, hs.faulted_idle,
    hs.commanded_linked⟩

end RoboLean.Cell.SupervisorQueue
