/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.VectorClock.Clocks

/-!
# Crown-execution clock-dimension lower-bound step for unicast executions

This module proves a self-contained crown-execution dimension lower-bound step over finite unicast
message-passing executions `Execution P` toward #7203 (after [CharronBost1991], whose primary
journal text was not inspected, so this module does not claim its cited endpoint): characterizing
`Execution.HappensBeforeLe` across `Execution P` via coordinatewise order-embeddings into
`Fin d → α` (for any `LinearOrder α`) requires dimension `Fintype.card P ≤ d`.

### Construction and proof outline

For `n ≥ 2` processes `Fin n` with cyclic derangement `crownShift hn p = (p + 1) % n`,
`crownFin n hn` constructs an explicit causally well-formed execution in four blocks of total
length `2 * n + 2 * (n * n)`:

1. **Phase 1 initial events (`crownPhase1 hn p`):** one internal event `a_p` on each process `p`.
2. **Phase 1 point-to-point sends:** for each pair `(p, q)` with `q ≠ p` and `q ≠ crownShift hn p`,
   process `p` sends a message to `q` (using an internal step on `p` for excluded pairs so block
   offsets stay uniform).
3. **Message deliveries:** each process `q` receives those `n - 2` messages sent to it in Block 2.
4. **Phase 2 terminal events (`crownPhase2 hn q`):** one internal event `b_q` on each process `q`.

Because no `send` step ever occurs at or after any `recv` step, causal paths cross at most one
message hop, giving the exact crown characterization (`crownFin_happensBeforeLe_iff`):
`a_p ≼ b_q ↔ q ≠ crownShift hn p`.

Any order-embedding `f : E.Event → (Fin d → α)` into a `d`-fold product of a `LinearOrder α` must
separate each incomparable pair `(a_p, b_{crownShift p})` at some coordinate `coord p : Fin d`
where `f (b_{crownShift p}) (coord p) < f (a_p) (coord p)`. If `coord p₁ = coord p₂ = i` for
`p₁ ≠ p₂`, then `crownShift p₂ ≠ crownShift p₁` yields `a_{p₁} ≼ b_{crownShift p₂}` and
`a_{p₂} ≼ b_{crownShift p₁}`, producing the strict cycle
`f (a_{p₁}) i ≤ f (b_{crownShift p₂}) i < f (a_{p₂}) i ≤ f (b_{crownShift p₁}) i < f (a_{p₁}) i`.
Hence `coord : Fin n → Fin d` is injective, proving `n ≤ d`.

For arbitrary finite `P`, `exists_unicast_execution_dim_lower_bound` and
`unicast_clock_dim_lower_bound` handle `Fintype.card P = 0` (`Execution.empty`, `0 ≤ d`) and
`Fintype.card P = 1` (two sequential internal events on the unique process forcing `1 ≤ d`)
directly, and transport `crownFin` along `Fin (Fintype.card P) ≃ P` when `2 ≤ Fintype.card P`.
Combining with Mattern vector clocks (`Execution.vc`, [Mattern1989]) yields
`exists_unicast_orderEmbedding_clock_iff`: every unicast execution on `P` admits a `d`-coordinate
`ℕ`-vector clock iff `Fintype.card P ≤ d`.

## Main definitions

* `Cslib.Distributed.VectorClock.crownShift`: cyclic fixed-point-free permutation on `Fin n` for
  `2 ≤ n`.
* `Cslib.Distributed.VectorClock.crownStep`, `Cslib.Distributed.VectorClock.crownFin`:
  explicit 4-block crown execution on `Fin n` for `2 ≤ n`.
* `Cslib.Distributed.VectorClock.crownPhase1`, `Cslib.Distributed.VectorClock.crownPhase2`: Phase-1
  events `a_p` and Phase-2 events `b_q` of `crownFin`.

## Main results

* `Cslib.Distributed.VectorClock.crownFin_happensBeforeLe_iff`: exact crown causality
  `a_p ≼ b_q ↔ q ≠ crownShift hn p` in `crownFin`.
* `Cslib.Distributed.VectorClock.crownFin_dim_lower_bound`: any order-embedding of `crownFin n hn`
  into `Fin d → α` forces `n ≤ d`.
* `Cslib.Distributed.VectorClock.exists_unicast_execution_dim_lower_bound`: crown-execution step
  constructing a single `Execution P` that forces `Fintype.card P ≤ d` for any product
  order-embedding into `Fin d → α`.
* `Cslib.Distributed.VectorClock.unicast_clock_dim_lower_bound`: crown-execution step proving
  `Fintype.card P ≤ d` for `Fin d → α` logical clocks across `Execution P`.
* `Cslib.Distributed.VectorClock.exists_unicast_orderEmbedding_clock_iff`: sharp
  `Fintype.card P ≤ d` characterization for `Fin d → ℕ` vector clocks across `Execution P`.

## References

* [B. Charron-Bost, *Concerning the size of logical clocks in distributed systems*][CharronBost1991]
* [F. Mattern, *Virtual Time and Global States of Distributed Systems*][Mattern1989]
-/

public section

namespace Cslib.Distributed.VectorClock

universe u v

/-! ### Cyclic derangement and explicit crown execution on `Fin n` (`2 ≤ n`) -/

/-- Cyclic shift `(p + 1) mod n` on `Fin n` (`2 ≤ n`), used as the fixed-point-free bijection in
the crown execution `crownFin`. -/
@[expose] def crownShift {n : ℕ} (hn : 2 ≤ n) (p : Fin n) : Fin n :=
  ⟨(p.val + 1) % n, Nat.mod_lt _ (by omega)⟩

/-- `crownShift hn` has no fixed points when `2 ≤ n`. -/
theorem crownShift_ne_self {n : ℕ} (hn : 2 ≤ n) (p : Fin n) : crownShift hn p ≠ p := by
  intro heq
  have hval : (p.val + 1) % n = p.val := congrArg Fin.val heq
  by_cases hlt : p.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hval
    omega
  · have hp : p.val + 1 = n := by omega
    rw [hp, Nat.mod_self] at hval
    omega

/-- `crownShift hn` is injective on `Fin n`. -/
theorem crownShift_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (crownShift hn) := by
  intro p₁ p₂ heq
  have hval : (p₁.val + 1) % n = (p₂.val + 1) % n := congrArg Fin.val heq
  ext
  by_cases h₁ : p₁.val + 1 < n <;> by_cases h₂ : p₂.val + 1 < n
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hval
    omega
  · have hp₂ : p₂.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h₁, hp₂, Nat.mod_self] at hval
    omega
  · have hp₁ : p₁.val + 1 = n := by omega
    rw [hp₁, Nat.mod_self, Nat.mod_eq_of_lt h₂] at hval
    omega
  · omega

/-- Step `i` (`0 ≤ i < 2 * n + 2 * (n * n)`) of the 4-block crown execution `crownFin` on `Fin n`:
* `[0, n)`: Phase-1 initial internal step `a_p` on each `p`,
* `[n, n + n²)`: send from `p = (i - n) / n` to `q = (i - n) % n` if `q ∉ {p, crownShift p}`,
  else internal step on `p`,
* `[n + n², n + 2n²)`: matching receive at `q` of step `i - n²` if `q ∉ {p, crownShift p}`,
  else internal step on `q`,
* `[n + 2n², 2n + 2n²)`: Phase-2 terminal internal step `b_q` on each `q`. -/
@[expose] def crownStep (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 2 * (n * n))) : Step (Fin n) :=
  have hn_pos : 0 < n := by omega
  if hi₀ : i.val < n then
    .internal ⟨i.val, hi₀⟩
  else if hi₁ : i.val < n + n * n then
    let m := i.val - n
    let p : Fin n := ⟨m / n, (Nat.div_lt_iff_lt_mul hn_pos).mpr (by omega)⟩
    let q : Fin n := ⟨m % n, Nat.mod_lt m hn_pos⟩
    if q ≠ p ∧ q ≠ crownShift hn p then .send p q else .internal p
  else if hi₂ : i.val < n + 2 * (n * n) then
    let m := i.val - (n + n * n)
    let p : Fin n := ⟨m / n, (Nat.div_lt_iff_lt_mul hn_pos).mpr (by omega)⟩
    let q : Fin n := ⟨m % n, Nat.mod_lt m hn_pos⟩
    if q ≠ p ∧ q ≠ crownShift hn p then .recv q (n + m) else .internal q
  else
    .internal ⟨i.val - (n + 2 * (n * n)), by have := i.isLt; omega⟩

private theorem crownStep_eq_recv {n : ℕ} {hn : 2 ≤ n} {i : ℕ}
    {hi : i < 2 * n + 2 * (n * n)} {r : Fin n} {sIdx : ℕ}
    (h : crownStep n hn ⟨i, hi⟩ = .recv r sIdx) :
    ∃ (hge : n + n * n ≤ i) (hlt : i < n + 2 * (n * n)),
      sIdx = n + (i - (n + n * n)) ∧
      have hn_pos : 0 < n := by omega
      have hm_lt : i - (n + n * n) < n * n := by omega
      let m := i - (n + n * n)
      let p : Fin n := ⟨m / n, (Nat.div_lt_iff_lt_mul hn_pos).mpr hm_lt⟩
      let q : Fin n := ⟨m % n, Nat.mod_lt m hn_pos⟩
      (q ≠ p ∧ q ≠ crownShift hn p) ∧ r = q := by
  dsimp only [crownStep] at h
  split_ifs at h
  cases h
  exact ⟨by omega, by omega, rfl, ‹_›, rfl⟩

private theorem crownStep_send_at {n : ℕ} (hn : 2 ≤ n) {m : ℕ} (hm : m < n * n)
    (hcond :
      let p : Fin n := ⟨m / n, (Nat.div_lt_iff_lt_mul (by omega)).mpr hm⟩
      let q : Fin n := ⟨m % n, Nat.mod_lt m (by omega)⟩
      q ≠ p ∧ q ≠ crownShift hn p) :
    crownStep n hn ⟨n + m, by omega⟩ =
      .send ⟨m / n, (Nat.div_lt_iff_lt_mul (by omega)).mpr hm⟩
        ⟨m % n, Nat.mod_lt m (by omega)⟩ := by
  have hs₀ : ¬ n + m < n := by omega
  have hs₁ : n + m < n + n * n := by omega
  have hsub : n + m - n = m := by omega
  dsimp only [crownStep]
  simp only [hs₀, hs₁, ↓reduceDIte, hsub]
  dsimp only at hcond
  simp only [eq_true hcond, ↓reduceIte]

/-- Explicit 4-block unicast crown execution on `Fin n` (`2 ≤ n`), containing
`2 * n + 2 * (n * n)` events (a crown-poset step after [CharronBost1991] toward #7203). -/
@[expose] def crownFin (n : ℕ) (hn : 2 ≤ n) : Execution (Fin n) where
  steps := List.ofFn (crownStep n hn)
  recv_valid := by
    intro ⟨i, hi⟩ r sIdx hstep
    have hi' : i < 2 * n + 2 * (n * n) := by simpa only [List.length_ofFn] using hi
    change (List.ofFn (crownStep n hn))[i] = .recv r sIdx at hstep
    rw [List.getElem_ofFn] at hstep
    obtain ⟨hge, hlt, hsIdx, hcond, hr⟩ := crownStep_eq_recv hstep
    have hm_lt : i - (n + n * n) < n * n := by omega
    have hs_lt : sIdx < i := by omega
    refine ⟨hs_lt, ⟨(i - (n + n * n)) / n, (Nat.div_lt_iff_lt_mul (by omega)).mpr hm_lt⟩, ?_⟩
    rw [List.getElem_ofFn, hr]
    have hidx_eq : (⟨sIdx, hs_lt.trans hi'⟩ : Fin (2 * n + 2 * (n * n))) =
        ⟨n + (i - (n + n * n)), by omega⟩ := Fin.ext hsIdx
    rw [hidx_eq]
    exact crownStep_send_at hn hm_lt hcond
  recv_injective := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ r₁ r₂ sIdx hi_eq hj_eq
    change (List.ofFn (crownStep n hn))[i] = .recv r₁ sIdx at hi_eq
    change (List.ofFn (crownStep n hn))[j] = .recv r₂ sIdx at hj_eq
    rw [List.getElem_ofFn] at hi_eq hj_eq
    obtain ⟨hge_i, _, hs_i, _, _⟩ := crownStep_eq_recv hi_eq
    obtain ⟨hge_j, _, hs_j, _, _⟩ := crownStep_eq_recv hj_eq
    have hij : i = j := by omega
    exact Fin.ext hij

private theorem crownEvent_step_eq {n : ℕ} (hn : 2 ≤ n) (e : (crownFin n hn).Event) :
    e.step = crownStep n hn ⟨e.idx.val,
      by simpa only [crownFin, List.length_ofFn] using e.idx.isLt⟩ := by
  change (List.ofFn (crownStep n hn))[e.idx.val] = _
  exact List.getElem_ofFn _

/-- Phase-1 event `a_p` on process `p` in `crownFin n hn` (at trace index `p.val`). -/
@[expose] def crownPhase1 {n : ℕ} (hn : 2 ≤ n) (p : Fin n) : (crownFin n hn).Event :=
  ⟨⟨p.val, by simp only [crownFin, List.length_ofFn]; have := p.isLt; omega⟩⟩

/-- Phase-2 event `b_q` on process `q` in `crownFin n hn` (at trace index `n + 2n² + q.val`). -/
@[expose] def crownPhase2 {n : ℕ} (hn : 2 ≤ n) (q : Fin n) : (crownFin n hn).Event :=
  ⟨⟨n + 2 * (n * n) + q.val, by simp only [crownFin, List.length_ofFn]; have := q.isLt; omega⟩⟩

private theorem crownStep_actor_phase1 {n : ℕ} (hn : 2 ≤ n) (p : Fin n) :
    (crownPhase1 hn p).actor = p := by
  unfold Execution.Event.actor
  rw [crownEvent_step_eq]
  simp only [crownPhase1, crownStep, p.isLt, ↓reduceDIte, Step.actor_internal]

private theorem crownStep_actor_phase2 {n : ℕ} (hn : 2 ≤ n) (q : Fin n) :
    (crownPhase2 hn q).actor = q := by
  have h₀ : ¬ n + 2 * (n * n) + q.val < n := by omega
  have h₁ : ¬ n + 2 * (n * n) + q.val < n + n * n := by omega
  have h₂ : ¬ n + 2 * (n * n) + q.val < n + 2 * (n * n) := by omega
  have hsub : n + 2 * (n * n) + q.val - (n + 2 * (n * n)) = q.val := by omega
  unfold Execution.Event.actor
  rw [crownEvent_step_eq]
  simp only [crownPhase2, crownStep, h₀, h₁, h₂, ↓reduceDIte, Step.actor_internal]
  ext
  exact hsub

/-- Reachability invariant from `crownPhase1 hn p`: in Phase 1 (`idx < n + n²`) only process `p`
is reached, and in Phase 2 (`idx ≥ n + n²`) process `crownShift hn p` is never reached. -/
private def CrownAllowed {n : ℕ} (hn : 2 ≤ n) (p : Fin n)
    (x : (crownFin n hn).Event) : Prop :=
  if x.idx.val < n + n * n then x.actor = p else x.actor ≠ crownShift hn p

private theorem crownAllowed_preserved {n : ℕ} {hn : 2 ≤ n} {p : Fin n}
    {x y : (crownFin n hn).Event} (hx : CrownAllowed hn p x)
    (hstep : (crownFin n hn).CausalStep x y) : CrownAllowed hn p y := by
  unfold CrownAllowed at hx ⊢
  rcases hstep with ⟨hact, hlt⟩ | hmsg
  · split_ifs at hx ⊢ with hy_ph hx_ph hx_ph₂
    · exact hact.symm.trans hx
    · omega
    · rw [← hact, hx]
      exact (crownShift_ne_self hn p).symm
    · exact hact ▸ hx
  · have hy_step : y.step = .recv y.actor x.idx.val := hmsg
    rw [crownEvent_step_eq] at hy_step
    obtain ⟨hge, hlt, hx_idx, hcond, hy_act⟩ := crownStep_eq_recv hy_step
    have hm_lt : y.idx.val - (n + n * n) < n * n := by omega
    have hx_ph : x.idx.val < n + n * n := by omega
    simp only [hx_ph, ↓reduceIte] at hx
    have hy_not_ph : ¬ y.idx.val < n + n * n := by omega
    simp only [hy_not_ph, ↓reduceIte]
    have hx_step : x.step =
        .send ⟨(y.idx.val - (n + n * n)) / n,
          (Nat.div_lt_iff_lt_mul (by omega)).mpr hm_lt⟩
          ⟨(y.idx.val - (n + n * n)) % n, Nat.mod_lt _ (by omega)⟩ := by
      rw [crownEvent_step_eq]
      have hx_fin : (⟨x.idx.val, by simpa only [crownFin, List.length_ofFn] using x.idx.isLt⟩ :
          Fin (2 * n + 2 * (n * n))) = ⟨n + (y.idx.val - (n + n * n)), by omega⟩ :=
        Fin.ext hx_idx
      rw [hx_fin]
      exact crownStep_send_at hn hm_lt hcond
    have hp_eq : (⟨(y.idx.val - (n + n * n)) / n,
        (Nat.div_lt_iff_lt_mul (by omega)).mpr hm_lt⟩ : Fin n) = p := by
      rw [← hx, Execution.Event.actor, hx_step, Step.actor_send]
    rw [hy_act, ← hp_eq]
    exact hcond.2

/-- Crown-poset causality step in `crownFin` (toward #7203, after [CharronBost1991], not the
uninspected paper endpoint): Phase-1 event `a_p` causally precedes or equals Phase-2 event `b_q`
iff `q ≠ crownShift hn p`. -/
theorem crownFin_happensBeforeLe_iff {n : ℕ} (hn : 2 ≤ n) (p q : Fin n) :
    (crownFin n hn).HappensBeforeLe (crownPhase1 hn p) (crownPhase2 hn q) ↔
      q ≠ crownShift hn p := by
  constructor
  · intro hle hq
    have hinit : CrownAllowed hn p (crownPhase1 hn p) := by
      have hlt : (crownPhase1 hn p).idx.val < n + n * n := by simp only [crownPhase1]; omega
      simp only [CrownAllowed, hlt, ↓reduceIte, crownStep_actor_phase1]
    have hend : CrownAllowed hn p (crownPhase2 hn q) := by
      generalize crownPhase2 hn q = y at hle ⊢
      induction hle with
      | refl => exact hinit
      | tail _ hcs ih => exact crownAllowed_preserved ih hcs
    have hnot_lt : ¬ (crownPhase2 hn q).idx.val < n + n * n := by simp only [crownPhase2]; omega
    simp only [CrownAllowed, hnot_lt, ↓reduceIte, crownStep_actor_phase2] at hend
    exact hend hq
  · intro hq_ne
    by_cases hqp : q = p
    · subst hqp
      refine (crownFin n hn).programOrder_happensBeforeLe ?_ ?_
      · rw [crownStep_actor_phase1, crownStep_actor_phase2]
      · simp only [crownPhase1, crownPhase2, Fin.le_def]; omega
    · let m := p.val * n + q.val
      have hm_lt : m < n * n := by
        calc p.val * n + q.val
          _ < p.val * n + n := Nat.add_lt_add_left q.isLt _
          _ = (p.val + 1) * n := (Nat.succ_mul p.val n).symm
          _ ≤ n * n := Nat.mul_le_mul_right n p.isLt
      have hm_div : m / n = p.val := by
        dsimp only [m]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt q.isLt,
          Nat.zero_add]
      have hm_mod : m % n = q.val := by
        dsimp only [m]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt q.isLt]
      have hp_fin : (⟨m / n, (Nat.div_lt_iff_lt_mul (by omega)).mpr hm_lt⟩ : Fin n) = p :=
        Fin.ext hm_div
      have hq_fin : (⟨m % n, Nat.mod_lt m (by omega)⟩ : Fin n) = q :=
        Fin.ext hm_mod
      have hcond_m :
          let p' : Fin n := ⟨m / n, (Nat.div_lt_iff_lt_mul (by omega)).mpr hm_lt⟩
          let q' : Fin n := ⟨m % n, Nat.mod_lt m (by omega)⟩
          q' ≠ p' ∧ q' ≠ crownShift hn p' := by
        dsimp only
        rw [hp_fin, hq_fin]
        exact ⟨hqp, hq_ne⟩
      have hlen_eq : (crownFin n hn).steps.length = 2 * n + 2 * (n * n) := by
        simp only [crownFin, List.length_ofFn]
      let eSend : (crownFin n hn).Event := ⟨⟨n + m, by rw [hlen_eq]; omega⟩⟩
      let eRecv : (crownFin n hn).Event := ⟨⟨n + n * n + m, by rw [hlen_eq]; omega⟩⟩
      have hsend_step : eSend.step = .send p q := by
        rw [crownEvent_step_eq]
        simp only [eSend]
        rw [crownStep_send_at hn hm_lt hcond_m, hp_fin, hq_fin]
      have hrecv_step : eRecv.step = .recv q eSend.idx.val := by
        rw [crownEvent_step_eq]
        dsimp only [eRecv, eSend, crownStep]
        simp only [show ¬ n + n * n + m < n by omega, show ¬ n + n * n + m < n + n * n by omega,
          show n + n * n + m < n + 2 * (n * n) by omega, ↓reduceDIte,
          show n + n * n + m - (n + n * n) = m by omega, hp_fin, hq_fin,
          eq_true (⟨hqp, hq_ne⟩ : q ≠ p ∧ q ≠ crownShift hn p), ↓reduceIte]
      have h1 : (crownFin n hn).HappensBefore (crownPhase1 hn p) eSend :=
        (crownFin n hn).programOrder_happensBefore
          (by rw [crownStep_actor_phase1, Execution.Event.actor, hsend_step, Step.actor_send])
          (by simp only [crownPhase1, eSend, Fin.lt_def]; have := p.isLt; omega)
      have h2 : (crownFin n hn).HappensBefore eSend eRecv :=
        (crownFin n hn).messageOrder_happensBefore
          ((crownFin n hn).messageOrder_of_recv hrecv_step)
      have h3 : (crownFin n hn).HappensBefore eRecv (crownPhase2 hn q) :=
        (crownFin n hn).programOrder_happensBefore
          (by rw [crownStep_actor_phase2, Execution.Event.actor, hrecv_step, Step.actor_recv])
          (by simp only [eRecv, crownPhase2, Fin.lt_def]; omega)
      exact ((h1.trans h2).trans h3).happensBeforeLe

/-! ### Dimension lower bound and sharp characterization -/

/-- Crown-execution dimension step on `Fin n` (toward #7203, after [CharronBost1991], not the
uninspected paper endpoint): any coordinatewise order-embedding of `crownFin n hn` into
`Fin d → α` (for any `LinearOrder α`) satisfies `n ≤ d`. -/
theorem crownFin_dim_lower_bound {n : ℕ} (hn : 2 ≤ n) {α : Type v} [LinearOrder α] {d : ℕ}
    (f : (crownFin n hn).Event → (Fin d → α))
    (hf : ∀ e₁ e₂, (crownFin n hn).HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂) :
    n ≤ d := by
  have hex : ∀ p : Fin n, ∃ i : Fin d,
      f (crownPhase2 hn (crownShift hn p)) i < f (crownPhase1 hn p) i := fun p => by
    simpa [Pi.le_def] using mt (hf _ _).mpr (mt (crownFin_happensBeforeLe_iff hn _ _).mp (· rfl))
  choose coord hcoord using hex
  have hinj : Function.Injective coord := by
    intro p₁ p₂ heq
    by_contra hp_ne
    have hσ : crownShift hn p₂ ≠ crownShift hn p₁ :=
      fun h => hp_ne (crownShift_injective hn h.symm)
    have hle₁₂ := (hf _ _).mp ((crownFin_happensBeforeLe_iff hn p₁ _).mpr hσ) (coord p₁)
    have hle₂₁ := (hf _ _).mp ((crownFin_happensBeforeLe_iff hn p₂ _).mpr hσ.symm) (coord p₁)
    exact lt_irrefl _ ((hle₁₂.trans_lt (heq ▸ hcoord p₂)).trans (hle₂₁.trans_lt (hcoord p₁)))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective coord hinj

/-- Single-execution dimension lower-bound step over finite unicast traces `Execution P` (toward
#7203, after [CharronBost1991], whose primary text was not inspected; not the cited endpoint):
for every finite `P`, there exists `E : Execution P` such that any order-embedding of `E.Event`
into `Fin d → α` (for any `LinearOrder α`) forces `Fintype.card P ≤ d` (via `Execution.empty` at
`|P| = 0`, two sequential internal events at `|P| = 1`, and `crownFin` for `2 ≤ |P|`). -/
theorem exists_unicast_execution_dim_lower_bound (P : Type u) [Fintype P] :
    ∃ E : Execution P, ∀ {α : Type v} [LinearOrder α] {d : ℕ}
      (f : E.Event → (Fin d → α)),
      (∀ e₁ e₂ : E.Event, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂) →
      Fintype.card P ≤ d := by
  rcases hcard : Fintype.card P with _ | _ | k
  · exact ⟨Execution.empty, fun _ _ => Nat.zero_le _⟩
  · obtain ⟨p₀, _⟩ := Fintype.card_eq_one_iff.mp hcard
    let E : Execution P := Execution.ofInternal [p₀, p₀]
    refine ⟨E, fun {α} _ {d} f hf => ?_⟩
    let e₀ : E.Event := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
    let e₁ : E.Event := ⟨⟨1, Nat.lt_succ_self 1⟩⟩
    have hnot : ¬ E.HappensBeforeLe e₁ e₀ := by
      intro hle
      have hidx : e₁.idx.val ≤ e₀.idx.val := E.happensBeforeLe_idx_le hle
      exact Nat.not_succ_le_zero 0 hidx
    have hnot_le : ¬ f e₁ ≤ f e₀ := mt (hf e₁ e₀).mpr hnot
    rw [Pi.le_def] at hnot_le
    push Not at hnot_le
    obtain ⟨i, _⟩ := hnot_le
    have hi := i.isLt
    omega
  · have hn : 2 ≤ k + 2 := by omega
    let equiv : Fin (k + 2) ≃ P := (Fintype.equivOfCardEq (by simp [hcard])).symm
    let E : Execution P := (crownFin (k + 2) hn).map equiv
    refine ⟨E, fun {α} _ {d} f hf => ?_⟩
    refine crownFin_dim_lower_bound hn (fun e => f ((crownFin (k + 2) hn).mapEvent equiv e)) ?_
    intro e₁ e₂
    rw [← hf, Execution.map_happensBeforeLe_iff equiv.injective]

/-- Clock-dimension lower-bound step over finite unicast executions `Execution P` (toward #7203,
after [CharronBost1991], whose primary text was not inspected; not the cited endpoint): if every
`E : Execution P` admits an order-embedding into `Fin d → α` (for a `LinearOrder α`) characterizing
`HappensBeforeLe`, then `Fintype.card P ≤ d`. -/
theorem unicast_clock_dim_lower_bound {P : Type u} [Fintype P] {α : Type v} [LinearOrder α]
    {d : ℕ} (h : ∀ E : Execution P, ∃ f : E.Event → (Fin d → α),
      ∀ e₁ e₂ : E.Event, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂) :
    Fintype.card P ≤ d := by
  obtain ⟨E, hE⟩ := exists_unicast_execution_dim_lower_bound P
  obtain ⟨f, hf⟩ := h E
  exact hE f hf

/-- Sharp `Fin d → ℕ` clock-dimension step over finite unicast executions `Execution P` (toward
#7203, combining `unicast_clock_dim_lower_bound` after [CharronBost1991] with Mattern's
`Execution.vc` [Mattern1989]; not claiming [CharronBost1991]'s uninspected endpoint): every
`E : Execution P` admits an order-embedding into `Fin d → ℕ` iff `Fintype.card P ≤ d`. -/
theorem exists_unicast_orderEmbedding_clock_iff {P : Type u} [Fintype P] {d : ℕ} :
    (∀ E : Execution P, ∃ f : E.Event → (Fin d → ℕ),
      ∀ e₁ e₂ : E.Event, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂) ↔
      Fintype.card P ≤ d := by
  constructor
  · exact unicast_clock_dim_lower_bound
  · intro hd E
    let _ : DecidableEq P := Classical.decEq P
    let equiv : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
    refine ⟨fun e i => if hi : i.val < Fintype.card P then
        E.vc e (equiv.symm ⟨i.val, hi⟩) else 0, fun e₁ e₂ => ?_⟩
    rw [E.happensBeforeLe_iff_vc_le]
    constructor
    · intro hle i
      dsimp only
      split_ifs with hi
      · exact hle _
      · exact le_rfl
    · intro hle p
      let j : Fin d := ⟨(equiv p).val, (equiv p).isLt.trans_le hd⟩
      have hj : j.val < Fintype.card P := (equiv p).isLt
      have hval := hle j
      dsimp only at hval
      simp only [hj, ↓reduceDIte] at hval
      have hjp : equiv.symm ⟨j.val, hj⟩ = p := equiv.symm_apply_apply p
      rwa [hjp] at hval

end Cslib.Distributed.VectorClock
