/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Paging.LRU
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.List.FinRange

/-!
# First-in, first-out (FIFO) paging and LIFO non-competitiveness

This file formalizes two companion deterministic paging results from Section 4 ("Paging"),
pp. 207–208, of [Sleator and Tarjan, *Amortized Efficiency of List Update and Paging
Rules*][SleatorTarjan1985] in the equal-capacity (`n_A = n_MIN = k`) demand-paging model of
`CslibFrontier.DataStructure.Paging.Basic`:

1. **FIFO `k`-competitiveness (`fifoStrategy_isCompetitive`, `fifoStrategy_isCompetitiveAnyInit`):**
   First-in, first-out (FIFO) replaces the page that has resided in fast memory longest (p. 207),
   leaving arrival order unchanged on a cache hit (`fifoNext k q p = q` when `p ∈ q`) and matching
   `lruNext` on every cache miss (`(p :: q).take k` when `p ∉ q`). Consequently, `lruPotential` from
   `CslibFrontier.DataStructure.Paging.LRU` is directly an `Amortized` potential certificate for
   FIFO (`fifoPotential_step`, `fifoAmortized`, p. 208), giving `(k, 0)`-competitiveness from any
   common initial cache and `(k, k)`-competitiveness across arbitrary initial caches.
2. **LIFO non-competitiveness (`lifo_not_isCompetitiveFrom_empty`, `lifo_not_isCompetitive`):**
   Last-in, first-out (LIFO) replaces the page most recently moved into fast memory (p. 207). For
   `k = 1`, LIFO coincides with FIFO and is `(1, 0)`-competitive (`lifoStrategy_one_isCompetitive`).
   For every capacity `k ≥ 2` over at least `k + 1` distinct pages, Sleator and Tarjan's sequence of
   `k - 1` distinct warmup accesses followed by repeated alternating accesses to two further pages
   (p. 208) forces LIFO to fault at every step while an offline cache of size `k` faults only
   `k + 1` times in total, refuting `(c, b)`-competitiveness for all `c, b : Nat`.

Resource augmentation with unequal fast-memory capacities (`n_MIN < n_FIFO`) and the LFU
counterexample are not formalized here.

## Main definitions

* `Cslib.DataStructure.Paging.fifoNext`, `fifoStep`, `fifoRun`, `fifoFaults`, `fifoStrategy`:
  computable arrival-ordered FIFO transitions, fault counter, and `Online.DetStrategy`.
* `Cslib.DataStructure.Paging.lifoNext`, `lifoRun`, `lifoFaults`, `lifoStrategy`:
  computable LIFO transitions, fault counter, and `Online.DetStrategy`.
* `Cslib.DataStructure.Paging.lifoCounterexample`: Sleator–Tarjan alternating witness against LIFO.

## Main results

* `fifoPotential_step`, `fifoAmortized`, `fifoFaults_amortized_bound`: `Amortized` potential
  certificate for FIFO reusing `lruPotential`.
* `fifoStrategy_isCompetitive`, `fifoStrategy_isCompetitiveAnyInit`: FIFO is `(k, 0)`-competitive
  from a shared initial cache and `(k, k)`-competitive across arbitrary initial caches.
* `lifoStrategy_one_isCompetitive`: at `k = 1`, LIFO is `(1, 0)`-competitive.
* `lifo_not_isCompetitiveFrom_empty`, `lifo_not_isCompetitive`, `lifo_not_isCompetitiveAnyInit`,
  `fin_lifo_not_isCompetitiveFrom_empty`: for `2 ≤ k` over `≥ k + 1` pages, LIFO is not
  `(c, b)`-competitive for any `c, b : Nat`.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985], Section 4 ("Paging"), pp. 207–208.
-/

public section

namespace Cslib.DataStructure.Paging

open Cslib.DataStructure Cslib.DataStructure.Online

variable {α : Type} [DecidableEq α]

/-! ### First-in, first-out (FIFO) paging and `k`-competitiveness -/

/-- Advance the arrival-ordered FIFO queue (most recently inserted first, longest-resident last) of
capacity `k` on page `p`: hits leave the queue unchanged, while misses prepend `p` and truncate to
length `k`. -/
@[expose]
def fifoNext (k : Nat) (q : List α) (p : α) : List α :=
  if p ∈ q then q else (p :: q).take k

/-- Single-step FIFO update returning the new queue and whether a page fault occurred. -/
@[expose]
def fifoStep (k : Nat) (q : List α) (p : α) : List α × Bool :=
  (fifoNext k q p, decide (p ∉ q))

/-- Run `fifoNext k` across a request list from initial arrival queue `q`. -/
@[expose]
def fifoRun (k : Nat) (q : List α) : List α → List α
  | [] => q
  | p :: ps => fifoRun k (fifoNext k q p) ps

/-- Count total page faults incurred by computable queue-based FIFO from `q` on `reqs`. -/
@[expose]
def fifoFaults (k : Nat) (q : List α) : List α → Nat
  | [] => 0
  | p :: ps => (if p ∈ q then 0 else 1) + fifoFaults k (fifoNext k q p) ps

@[simp]
theorem fifoRun_nil (k : Nat) (q : List α) : fifoRun k q [] = q := rfl

@[simp]
theorem fifoRun_cons (k : Nat) (q : List α) (p : α) (ps : List α) :
    fifoRun k q (p :: ps) = fifoRun k (fifoNext k q p) ps := rfl

@[simp]
theorem fifoFaults_nil (k : Nat) (q : List α) : fifoFaults k q [] = 0 := rfl

@[simp]
theorem fifoFaults_cons (k : Nat) (q : List α) (p : α) (ps : List α) :
    fifoFaults k q (p :: ps) = (if p ∈ q then 0 else 1) + fifoFaults k (fifoNext k q p) ps := rfl

/-- On every cache miss `p ∉ q`, `fifoNext` coincides with `lruNext`. -/
theorem fifoNext_eq_lruNext_of_notMem {k : Nat} {q : List α} {p : α} (hp : p ∉ q) :
    fifoNext k q p = lruNext k q p := by
  simp only [fifoNext, lruNext, hp, ↓reduceIte]

/-- `fifoNext` preserves `List.Nodup`. -/
theorem nodup_fifoNext {k : Nat} {q : List α} (hq : q.Nodup) (p : α) :
    (fifoNext k q p).Nodup := by
  by_cases hp : p ∈ q
  · simp only [fifoNext, hp, ↓reduceIte]
    exact hq
  · rw [fifoNext_eq_lruNext_of_notMem hp]
    exact nodup_lruNext hq p

/-- `fifoNext k` preserves `length ≤ k`. -/
theorem length_fifoNext_le {k : Nat} {q : List α} (hq : q.length ≤ k) (p : α) :
    (fifoNext k q p).length ≤ k := by
  by_cases hp : p ∈ q
  · simp only [fifoNext, hp, ↓reduceIte]
    exact hq
  · rw [fifoNext_eq_lruNext_of_notMem hp]
    exact length_lruNext_le hq p

/-- For `0 < k`, `fifoNext` induces a valid demand-paging transition on `q.toFinset`. -/
theorem validStep_fifoNext {k : Nat} (hk : 0 < k) {q : List α} (hlen : q.length ≤ k) (p : α) :
    ValidStep k q.toFinset p (fifoNext k q p).toFinset := by
  by_cases hp : p ∈ q
  · simp only [fifoNext, hp, ↓reduceIte]
    exact validStep_hit ((List.toFinset_card_le q).trans hlen) (List.mem_toFinset.mpr hp)
  · rw [fifoNext_eq_lruNext_of_notMem hp]
    exact validStep_lruNext hk hlen p

/-- Deterministic online strategy realizing FIFO for demand paging with positive capacity `k`.

Marked `noncomputable` solely because `init s₀ := s₀.toList` chooses an initial arrival order on
pre-loaded cache elements from `s₀ : Finset α` (`[]` when `s₀ = ∅`, witnessed by
`fifoStrategy_cost_empty`). -/
noncomputable abbrev fifoStrategy (k : Nat) (hk : 0 < k) : DetStrategy (problem α k) where
  Mem := List α
  ValidMem q := q.Nodup ∧ q.length ≤ k
  project q := q.toFinset
  init s₀ := s₀.toList
  step q p := fifoNext k q p
  valid_init hs₀ := by
    refine ⟨⟨Finset.nodup_toList _, ?_⟩, Finset.toList_toFinset _⟩
    rw [Finset.length_toList]
    exact hs₀
  valid_step {q} p hq :=
    ⟨⟨nodup_fifoNext hq.1 p, length_fifoNext_le hq.2 p⟩, validStep_fifoNext hk hq.2 p⟩

/-- `fifoStrategy.runMem` agrees with computable `fifoRun`. -/
theorem fifoStrategy_runMem_eq (k : Nat) (hk : 0 < k) (q : List α) (reqs : List α) :
    (fifoStrategy (α := α) k hk).runMem q reqs = fifoRun k q reqs := by
  induction reqs generalizing q with
  | nil => rfl
  | cons p ps ih => exact ih (fifoNext k q p)

/-- `fifoStrategy.costFrom` agrees with computable `fifoFaults`. -/
theorem fifoStrategy_costFrom_eq (k : Nat) (hk : 0 < k) (q : List α) (reqs : List α) :
    (fifoStrategy (α := α) k hk).costFrom q reqs = fifoFaults k q reqs := by
  induction reqs generalizing q with
  | nil => rfl
  | cons p ps ih =>
    change stepCost q.toFinset p (fifoNext k q p).toFinset +
        (fifoStrategy (α := α) k hk).costFrom (fifoNext k q p) ps = _
    simp only [stepCost, List.mem_toFinset, ih (fifoNext k q p), fifoFaults_cons]

/-- From an empty cache `∅`, `fifoStrategy.cost` equals computable `fifoFaults k [] reqs`. -/
theorem fifoStrategy_cost_empty (k : Nat) (hk : 0 < k) (reqs : List α) :
    (fifoStrategy (α := α) k hk).cost ∅ reqs = fifoFaults k [] reqs := by
  rw [(fifoStrategy (α := α) k hk).cost_eq_costFrom (validCache_empty k), fifoStrategy_costFrom_eq]
  simp only [Finset.toList_empty]

/-- Single-step competitive potential inequality for FIFO (`0 < k`), reusing `lruPotential`:
hits keep `fifoNext k q p = q` unchanged while misses delegate to `lruPotential_step`. -/
theorem fifoPotential_step {k : Nat} (hk : 0 < k) {s s' : Finset α} {q : List α} {p : α}
    (hq : q.Nodup ∧ q.length ≤ k) (hv : ValidStep k s p s') :
    stepCost q.toFinset p (fifoNext k q p).toFinset + lruPotential k s' (fifoNext k q p) ≤
      k * stepCost s p s' + lruPotential k s q := by
  by_cases hpq : p ∈ q
  · have hpqs : p ∈ q.toFinset := List.mem_toFinset.mpr hpq
    simp only [fifoNext, hpq, ↓reduceIte, stepCost_of_mem hpqs, Nat.zero_add]
    by_cases hps : p ∈ s
    · rw [validStep_hit_eq hv hps, stepCost_of_mem hps, Nat.mul_zero, Nat.zero_add]
    · rw [stepCost_of_notMem hps, Nat.mul_one]
      exact (lruPotential_le hv.2.1 q).trans (Nat.le_add_right k _)
  · rw [fifoNext_eq_lruNext_of_notMem hpq]
    exact lruPotential_step hk hq hv

/-- Native `Cslib.DataStructure.Amortized` potential certificate for `fifoStrategy k hk` against `k`
times the offline demand-paging step cost. -/
theorem fifoAmortized (k : Nat) (hk : 0 < k) :
    Amortized (fifoStrategy (α := α) k hk).impl id (lruPotential k)
      (fun s o => k * stepCost s o.1 o.2) :=
  Amortized.ofFn fun {_ _ _ _ _ _} hrep hv hexec => by
    rcases hexec with ⟨rfl, rfl⟩
    simpa only [id_eq, fifoStrategy, problem, Problem.offlineSpec] using
      fifoPotential_step hk hrep hv

/-- Computable-list telescoping bound for FIFO: for any valid arrival queue `q` and valid offline
schedule `(s_off, reqs, offStates)`, `fifoFaults k q reqs` plus final potential is at most `k` times
offline faults plus initial potential. -/
theorem fifoFaults_amortized_bound {k : Nat} (hk : 0 < k) {s_off : Finset α} {q : List α}
    {reqs : List α} {offStates : List (Finset α)}
    (hq : q.Nodup ∧ q.length ≤ k) (hv : (problem α k).ValidSchedule s_off reqs offStates) :
    fifoFaults k q reqs +
        lruPotential k ((problem α k).finalState s_off offStates) (fifoRun k q reqs) ≤
      k * (problem α k).scheduleCost s_off reqs offStates + lruPotential k s_off q := by
  have h := (fifoStrategy (α := α) k hk).amortized_bound (fifoAmortized k hk) hq hv
  simpa only [fifoStrategy_costFrom_eq, fifoStrategy_runMem_eq] using h

/-- **FIFO `k`-competitiveness from a common initial cache** ([SleatorTarjan1985], Section 4, p. 208
at `n_FIFO = n_MIN = k` with identical initial caches): when online and offline algorithms start
from the same valid cache `s₀` (including `∅`), `fifoStrategy k hk` incurs at most `k` times the
faults of any valid offline schedule, with zero additive constant. -/
theorem fifoStrategy_isCompetitive (k : Nat) (hk : 0 < k) :
    (fifoStrategy (α := α) k hk).IsCompetitive k 0 := by
  apply (fifoStrategy (α := α) k hk).competitive_of_amortized (fifoAmortized k hk)
  intro s₀ _
  simp only [lruPotential_eq_zero_of_toFinset_eq k (Finset.toList_toFinset s₀), le_refl]

/-- **FIFO `k`-competitiveness across arbitrary initial caches** ([SleatorTarjan1985], Section 4,
p. 208 at `n_FIFO = n_MIN = k`): for any valid initial caches `s₀` and `s_off` of size at most `k`,
`fifoStrategy k hk` incurs at most `k * optCost + k` faults. -/
theorem fifoStrategy_isCompetitiveAnyInit (k : Nat) (hk : 0 < k) :
    (fifoStrategy (α := α) k hk).IsCompetitiveAnyInit k k := by
  apply (fifoStrategy (α := α) k hk).competitiveAnyInit_of_amortized (fifoAmortized k hk)
  intro s₀ s_off _ hs_off
  exact lruPotential_le hs_off s₀.toList

/-! ### Last-in, first-out (LIFO) paging and Sleator–Tarjan's counterexample (`2 ≤ k`) -/

/-- Advance the LIFO stack (most recently inserted page at the head) of capacity `k` on page `p`:
hits leave the stack unchanged, misses into a non-full cache push `p`, and misses into a full cache
replace the head (the page most recently moved into fast memory) with `p`. -/
@[expose]
def lifoNext (k : Nat) (q : List α) (p : α) : List α :=
  if p ∈ q then q
  else if q.length < k then p :: q
  else (p :: q.drop 1).take k

/-- Run `lifoNext k` across a request list from initial LIFO stack `q`. -/
@[expose]
def lifoRun (k : Nat) (q : List α) : List α → List α
  | [] => q
  | p :: ps => lifoRun k (lifoNext k q p) ps

/-- Count total page faults incurred by computable LIFO from `q` on `reqs`. -/
@[expose]
def lifoFaults (k : Nat) (q : List α) : List α → Nat
  | [] => 0
  | p :: ps => (if p ∈ q then 0 else 1) + lifoFaults k (lifoNext k q p) ps

@[simp]
theorem lifoRun_nil (k : Nat) (q : List α) : lifoRun k q [] = q := rfl

@[simp]
theorem lifoRun_cons (k : Nat) (q : List α) (p : α) (ps : List α) :
    lifoRun k q (p :: ps) = lifoRun k (lifoNext k q p) ps := rfl

@[simp]
theorem lifoFaults_nil (k : Nat) (q : List α) : lifoFaults k q [] = 0 := rfl

@[simp]
theorem lifoFaults_cons (k : Nat) (q : List α) (p : α) (ps : List α) :
    lifoFaults k q (p :: ps) = (if p ∈ q then 0 else 1) + lifoFaults k (lifoNext k q p) ps := rfl

@[simp]
theorem lifoFaults_append (k : Nat) (q : List α) (rs₁ rs₂ : List α) :
    lifoFaults k q (rs₁ ++ rs₂) = lifoFaults k q rs₁ + lifoFaults k (lifoRun k q rs₁) rs₂ := by
  induction rs₁ generalizing q with
  | nil => simp only [List.nil_append, lifoFaults_nil, lifoRun_nil, Nat.zero_add]
  | cons p ps ih => simp only [List.cons_append, lifoFaults_cons, lifoRun_cons, ih, Nat.add_assoc]

/-- `lifoNext` preserves `List.Nodup`. -/
theorem nodup_lifoNext {k : Nat} {q : List α} (hq : q.Nodup) (p : α) :
    (lifoNext k q p).Nodup := by
  unfold lifoNext
  split
  · exact hq
  · next hp =>
    split
    · exact List.nodup_cons.mpr ⟨hp, hq⟩
    · have hp_drop : p ∉ q.drop 1 := fun h => hp ((List.drop_sublist 1 q).subset h)
      exact (List.nodup_cons.mpr ⟨hp_drop, hq.sublist (List.drop_sublist 1 q)⟩).take

/-- `lifoNext k` preserves `length ≤ k`. -/
theorem length_lifoNext_le {k : Nat} {q : List α} (hq : q.length ≤ k) (p : α) :
    (lifoNext k q p).length ≤ k := by
  unfold lifoNext
  split
  · exact hq
  · split
    · next hlt =>
      rw [List.length_cons]
      omega
    · exact List.length_take_le k _

/-- For `0 < k`, `lifoNext` induces a valid demand-paging transition on `q.toFinset`. -/
theorem validStep_lifoNext {k : Nat} (hk : 0 < k) {q : List α} (hnodup : q.Nodup)
    (hlen : q.length ≤ k) (p : α) :
    ValidStep k q.toFinset p (lifoNext k q p).toFinset := by
  by_cases hp : p ∈ q
  · simp only [lifoNext, hp, ↓reduceIte]
    exact validStep_hit ((List.toFinset_card_le q).trans hlen) (List.mem_toFinset.mpr hp)
  · have hps : p ∉ q.toFinset := by simpa only [List.mem_toFinset] using hp
    by_cases hlt : q.length < k
    · simp only [lifoNext, hp, hlt, ↓reduceIte, List.toFinset_cons]
      exact validStep_insert ((List.toFinset_card_le q).trans_lt hlt) hps
    · have hqeq : q.length = k := by omega
      have hqpos : 0 < q.length := by omega
      cases q with
      | nil =>
        simp only [List.length_nil] at hqpos
        omega
      | cons e rest =>
        simp only [List.length_cons] at hqeq
        rcases List.nodup_cons.mp hnodup with ⟨herest, _⟩
        have hstep : lifoNext k (e :: rest) p = p :: rest := by
          simp only [lifoNext, hp, hlt, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
          exact List.take_of_length_le (by simp only [List.length_cons]; omega)
        rw [hstep]
        have herase : ((e :: rest).toFinset).erase e = rest.toFinset := by
          rw [List.toFinset_cons,
            Finset.erase_insert (by simpa only [List.mem_toFinset] using herest)]
        rw [List.toFinset_cons (a := p), ← herase]
        exact validStep_replace ((List.toFinset_card_le _).trans hlen) hps
          (List.mem_toFinset.mpr List.mem_cons_self)

/-- Deterministic online strategy realizing LIFO for demand paging with positive capacity `k`. -/
noncomputable abbrev lifoStrategy (k : Nat) (hk : 0 < k) : DetStrategy (problem α k) where
  Mem := List α
  ValidMem q := q.Nodup ∧ q.length ≤ k
  project q := q.toFinset
  init s₀ := s₀.toList
  step q p := lifoNext k q p
  valid_init hs₀ := by
    refine ⟨⟨Finset.nodup_toList _, ?_⟩, Finset.toList_toFinset _⟩
    rw [Finset.length_toList]
    exact hs₀
  valid_step {q} p hq :=
    ⟨⟨nodup_lifoNext hq.1 p, length_lifoNext_le hq.2 p⟩, validStep_lifoNext hk hq.1 hq.2 p⟩

/-- `lifoStrategy.costFrom` agrees with computable `lifoFaults`. -/
theorem lifoStrategy_costFrom_eq (k : Nat) (hk : 0 < k) (q : List α) (reqs : List α) :
    (lifoStrategy (α := α) k hk).costFrom q reqs = lifoFaults k q reqs := by
  induction reqs generalizing q with
  | nil => rfl
  | cons p ps ih =>
    change stepCost q.toFinset p (lifoNext k q p).toFinset +
        (lifoStrategy (α := α) k hk).costFrom (lifoNext k q p) ps = _
    simp only [stepCost, List.mem_toFinset, ih (lifoNext k q p), lifoFaults_cons]

/-- From `∅`, `lifoStrategy.cost` equals computable `lifoFaults k [] reqs`. -/
theorem lifoStrategy_cost_empty (k : Nat) (hk : 0 < k) (reqs : List α) :
    (lifoStrategy (α := α) k hk).cost ∅ reqs = lifoFaults k [] reqs := by
  rw [(lifoStrategy (α := α) k hk).cost_eq_costFrom (validCache_empty k), lifoStrategy_costFrom_eq]
  simp only [Finset.toList_empty]

/-- At capacity `k = 1`, `lifoNext 1` equals `fifoNext 1`, so LIFO is `(1, 0)`-competitive; the
hypothesis `2 ≤ k` in `lifo_not_isCompetitiveFrom_empty` is therefore sharp. -/
theorem lifoStrategy_one_isCompetitive :
    (lifoStrategy (α := α) 1 (by omega)).IsCompetitive 1 0 := by
  have hnext : ∀ (q : List α) (p : α), q.length ≤ 1 → lifoNext 1 q p = fifoNext 1 q p := by
    intro q p hq
    by_cases hp : p ∈ q
    · simp only [lifoNext, fifoNext, hp, ↓reduceIte]
    · cases q with
      | nil =>
        simp only [lifoNext, fifoNext, hp, ↓reduceIte, List.length_nil, Nat.zero_lt_one,
          List.take_succ_cons, List.take_zero]
      | cons e rest =>
        simp only [List.length_cons] at hq
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        simp only [lifoNext, fifoNext, hp, ↓reduceIte, List.length_singleton, Nat.lt_irrefl,
          List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
  intro s₀ hs₀ reqs offStates hv
  have hcost : ∀ (q : List α) (rs : List α), q.length ≤ 1 →
      lifoFaults 1 q rs = fifoFaults 1 q rs := by
    intro q rs hq
    induction rs generalizing q with
    | nil => rfl
    | cons p ps ih =>
      rw [lifoFaults_cons, fifoFaults_cons, hnext q p hq]
      exact congrArg _ (ih (fifoNext 1 q p) (length_fifoNext_le hq p))
  rw [(lifoStrategy (α := α) 1 (by omega)).cost_eq_costFrom hs₀, lifoStrategy_costFrom_eq,
    hcost s₀.toList reqs (by rw [Finset.length_toList]; exact hs₀),
    ← fifoStrategy_costFrom_eq 1 (by omega),
    ← (fifoStrategy (α := α) 1 (by omega)).cost_eq_costFrom hs₀]
  exact fifoStrategy_isCompetitive 1 (by omega) s₀ hs₀ reqs offStates hv

/-- Sleator–Tarjan LIFO counterexample ([SleatorTarjan1985], p. 208): `init` (`k - 1` distinct
pages) followed by `t + 1` alternating pairs `[a, b]` of two further distinct pages. -/
@[expose]
def lifoCounterexample (init : List α) (a b : α) (t : Nat) : List α :=
  init ++ (List.replicate (t + 1) [a, b]).flatten

private theorem lifoRun_warmup {k : Nat} :
    ∀ (xs q : List α), (xs.reverse ++ q).Nodup → xs.length + q.length ≤ k →
      lifoRun k q xs = xs.reverse ++ q ∧ lifoFaults k q xs = xs.length
  | [], q, _, _ => ⟨rfl, rfl⟩
  | x :: xs, q, hnodup, hlen => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hnodup
    have hxq : x ∉ q := (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
    have hlt : q.length < k := by
      simp only [List.length_cons] at hlen
      omega
    have hstep : lifoNext k q x = x :: q := by simp only [lifoNext, hxq, hlt, ↓reduceIte]
    have hlen' : xs.length + (x :: q).length ≤ k := by
      simp only [List.length_cons] at hlen ⊢
      omega
    obtain ⟨hrun, hfault⟩ := lifoRun_warmup xs (x :: q) hnodup hlen'
    refine ⟨?_, ?_⟩
    · rw [lifoRun_cons, hstep, hrun, List.reverse_cons, List.append_assoc, List.singleton_append]
    · simp only [lifoFaults_cons, hxq, ↓reduceIte, hstep, hfault, List.length_cons]
      omega

private theorem lifoFaults_alternating {k : Nat} {base : List α} {a b : α}
    (hlen : base.length = k - 1) (hk : 1 ≤ k) (ha : a ∉ base) (hb : b ∉ base) (hab : a ≠ b) :
    ∀ t : Nat,
      lifoRun k (b :: base) ((List.replicate t [a, b]).flatten) = b :: base ∧
        lifoFaults k (b :: base) ((List.replicate t [a, b]).flatten) = 2 * t
  | 0 => ⟨rfl, rfl⟩
  | t + 1 => by
    have hab_not : a ∉ b :: base := by
      simp only [List.mem_cons, hab, ha, or_self, not_false_eq_true]
    have hba_not : b ∉ a :: base := by
      simp only [List.mem_cons, hab.symm, hb, or_self, not_false_eq_true]
    have hnotlt_b : ¬ (b :: base).length < k := by simp only [List.length_cons, hlen]; omega
    have hnotlt_a : ¬ (a :: base).length < k := by simp only [List.length_cons, hlen]; omega
    have hstep_a : lifoNext k (b :: base) a = a :: base := by
      simp only [lifoNext, hab_not, hnotlt_b, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
      exact List.take_of_length_le (by simp only [List.length_cons, hlen]; omega)
    have hstep_b : lifoNext k (a :: base) b = b :: base := by
      simp only [lifoNext, hba_not, hnotlt_a, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
      exact List.take_of_length_le (by simp only [List.length_cons, hlen]; omega)
    obtain ⟨hrun, hfault⟩ := lifoFaults_alternating hlen hk ha hb hab t
    simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
      lifoRun_cons, lifoFaults_cons, hab_not, hba_not, ↓reduceIte, hstep_a, hstep_b, hrun, hfault]
    exact ⟨trivial, by omega⟩

omit [DecidableEq α] in
private theorem nodup_append_pair {init : List α} {a b : α}
    (hnodup : (init ++ [a, b]).Nodup) :
    init.Nodup ∧ a ≠ b ∧ a ∉ init ∧ b ∉ init :=
  ⟨(List.nodup_append.mp hnodup).1,
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1 ∘ List.mem_singleton.mpr,
    fun ha => (List.nodup_append.mp hnodup).2.2 a ha a (by simp) rfl,
    fun hb => (List.nodup_append.mp hnodup).2.2 b hb b (by simp) rfl⟩

/-- On `lifoCounterexample init a b t` (`init.length = k - 1`, `(init ++ [a, b]).Nodup`, `1 ≤ k`),
LIFO from `[]` faults on every single request (`(k - 1) + 2 * (t + 1)` faults). -/
theorem lifoFaults_lifoCounterexample {k : Nat} (hk : 1 ≤ k) {init : List α} {a b : α}
    (hinit : init.length = k - 1) (hnodup : (init ++ [a, b]).Nodup) (t : Nat) :
    lifoFaults k [] (lifoCounterexample init a b t) = (k - 1) + 2 * (t + 1) := by
  obtain ⟨hnodup_init, hab, ha_init, hb_init⟩ := nodup_append_pair hnodup
  obtain ⟨hrun_w, hfault_w⟩ := lifoRun_warmup (k := k) init []
    (by simpa only [List.append_nil, List.nodup_reverse] using hnodup_init)
    (by simp only [List.length_nil, hinit]; omega)
  rw [List.append_nil] at hrun_w
  have ha_rev : a ∉ init.reverse := by simpa only [List.mem_reverse] using ha_init
  have hb_rev : b ∉ init.reverse := by simpa only [List.mem_reverse] using hb_init
  have hrev_len : init.reverse.length = k - 1 := by simp only [List.length_reverse, hinit]
  have hlt_rev : init.reverse.length < k := by omega
  have hstep1 : lifoNext k init.reverse a = a :: init.reverse := by
    simp only [lifoNext, ha_rev, hlt_rev, ↓reduceIte]
  have hba_not : b ∉ a :: init.reverse := by
    simp only [List.mem_cons, hab.symm, hb_rev, or_self, not_false_eq_true]
  have hnotlt_a : ¬ (a :: init.reverse).length < k := by
    simp only [List.length_cons, hrev_len]; omega
  have hstep2 : lifoNext k (a :: init.reverse) b = b :: init.reverse := by
    simp only [lifoNext, hba_not, hnotlt_a, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
    exact List.take_of_length_le (by simp only [List.length_cons, hrev_len]; omega)
  obtain ⟨_, hfault_alt⟩ := lifoFaults_alternating hrev_len hk ha_rev hb_rev hab t
  simp only [lifoCounterexample, lifoFaults_append, hrun_w, hfault_w, hinit,
    List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
    lifoFaults_cons, ha_rev, hba_not, ↓reduceIte, hstep1, hstep2, hfault_alt]
  omega

private theorem exists_validSchedule_insertAll {k : Nat} :
    ∀ (xs : List α) (s : Finset α),
      (∀ x ∈ xs, x ∉ s) → xs.Nodup → s.card + xs.length ≤ k →
      ∃ states, (problem α k).ValidSchedule s xs states ∧
        (problem α k).finalState s states = s ∪ xs.toFinset ∧
        (problem α k).scheduleCost s xs states = xs.length
  | [], s, _, _, _ => ⟨[], trivial, by simp only [List.toFinset_nil, Finset.union_empty]; rfl, rfl⟩
  | x :: xs, s, hdisj, hnodup, hcard => by
    rcases List.nodup_cons.mp hnodup with ⟨hxxs, hnodup'⟩
    have hxs : x ∉ s := hdisj x List.mem_cons_self
    have hlt : s.card < k := by simp only [List.length_cons] at hcard; omega
    have hstep : ValidStep k s x (insert x s) := validStep_insert hlt hxs
    have hdisj' : ∀ y ∈ xs, y ∉ insert x s := by
      intro y hy hmem
      rcases Finset.mem_insert.mp hmem with rfl | hys
      · exact hxxs hy
      · exact hdisj y (List.mem_cons_of_mem x hy) hys
    have hcard' : (insert x s).card + xs.length ≤ k := by
      rw [Finset.card_insert_of_notMem hxs]
      simp only [List.length_cons] at hcard
      omega
    obtain ⟨ss, hv, hfin, hcost⟩ := exists_validSchedule_insertAll xs (insert x s) hdisj' hnodup'
      hcard'
    refine ⟨insert x s :: ss, ⟨hstep, hv⟩, ?_, ?_⟩
    · change (problem α k).finalState (insert x s) ss = _
      rw [hfin]
      finset_card [List.toFinset_cons]
    · change stepCost s x (insert x s) + (problem α k).scheduleCost (insert x s) xs ss =
        (x :: xs).length
      rw [stepCost_of_notMem hxs, hcost, List.length_cons, Nat.add_comm]

/-- For `2 ≤ k`, an offline schedule of capacity `k` serves `lifoCounterexample init a b t` from `∅`
with at most `k + 1` faults by retaining `{a, b}` in fast memory across all alternating pairs. -/
theorem exists_offline_lifoCounterexample {k : Nat} (hk2 : 2 ≤ k) {init : List α} {a b : α}
    (hinit : init.length = k - 1) (hnodup : (init ++ [a, b]).Nodup) (t : Nat) :
    ∃ offStates,
      (problem α k).ValidSchedule ∅ (lifoCounterexample init a b t) offStates ∧
        (problem α k).scheduleCost ∅ (lifoCounterexample init a b t) offStates = k + 1 := by
  obtain ⟨hnodup_init, hab, ha_init, hb_init⟩ := nodup_append_pair hnodup
  obtain ⟨ss₀, hv₀, hfin₀, hcost₀⟩ := exists_validSchedule_insertAll (k := k) init ∅
    (fun _ _ h => Finset.notMem_empty _ h) hnodup_init
    (by simp only [Finset.card_empty, hinit]; omega)
  rw [Finset.empty_union] at hfin₀
  have hcard_init : init.toFinset.card = k - 1 := by
    rw [List.toFinset_card_of_nodup hnodup_init, hinit]
  have ha_not : a ∉ init.toFinset := by simpa only [List.mem_toFinset] using ha_init
  have hstep_a : ValidStep k init.toFinset a (insert a init.toFinset) :=
    validStep_insert (by omega) ha_not
  obtain ⟨e₀, he₀_mem⟩ : ∃ e₀, e₀ ∈ init.toFinset :=
    Finset.card_pos.mp (by omega)
  have he₀_in : e₀ ∈ insert a init.toFinset := Finset.mem_insert_of_mem he₀_mem
  have hb_not_a : b ∉ insert a init.toFinset := by
    simp only [Finset.mem_insert, hab.symm, List.mem_toFinset, hb_init, or_self, not_false_eq_true]
  have hcard_ins : (insert a init.toFinset).card ≤ k := by finset_card
  set s_pair := insert b ((insert a init.toFinset).erase e₀)
  have hstep_b : ValidStep k (insert a init.toFinset) b s_pair :=
    validStep_replace hcard_ins hb_not_a he₀_in
  have hcard_pair : s_pair.card ≤ k := hstep_b.2.1
  have he₀_ne_a : e₀ ≠ a := fun h => ha_not (h ▸ he₀_mem)
  have ha_pair : a ∈ s_pair :=
    Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he₀_ne_a.symm, Finset.mem_insert_self a _⟩)
  have hb_pair : b ∈ s_pair := Finset.mem_insert_self b _
  set tailReqs := (List.replicate t [a, b]).flatten
  have hmem_tail : ∀ p ∈ tailReqs, p ∈ s_pair := by
    intro p hp
    rcases List.mem_flatten.mp hp with ⟨l, hl, hpl⟩
    rw [List.mem_replicate.mp hl |>.2] at hpl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpl
    rcases hpl with rfl | rfl
    · exact ha_pair
    · exact hb_pair
  have hv_tail := validSchedule_replicate_of_forall_mem hcard_pair hmem_tail
  have hcost_tail := scheduleCost_replicate_of_forall_mem (k := k) hmem_tail
  set afterInitReqs := a :: b :: tailReqs
  set afterInitStates := insert a init.toFinset :: s_pair :: List.replicate tailReqs.length s_pair
  have hv_after : (problem α k).ValidSchedule init.toFinset afterInitReqs afterInitStates :=
    ⟨hstep_a, hstep_b, hv_tail⟩
  have hcost_after :
      (problem α k).scheduleCost init.toFinset afterInitReqs afterInitStates = 2 := by
    change stepCost init.toFinset a (insert a init.toFinset) +
      (stepCost (insert a init.toFinset) b s_pair +
        (problem α k).scheduleCost s_pair tailReqs (List.replicate tailReqs.length s_pair)) = 2
    rw [stepCost_of_notMem ha_not, stepCost_of_notMem hb_not_a, hcost_tail]
  have hreq_eq : lifoCounterexample init a b t = init ++ afterInitReqs := by
    simp only [lifoCounterexample, afterInitReqs, tailReqs, List.replicate_succ, List.flatten_cons,
      List.cons_append, List.nil_append]
  rw [hreq_eq]
  refine ⟨ss₀ ++ afterInitStates, ?_, ?_⟩
  · apply (problem α k).validSchedule_append hv₀
    rwa [hfin₀]
  · rw [(problem α k).scheduleCost_append hv₀.length_eq, hfin₀, hcost₀, hcost_after, hinit]
    omega

/-- **LIFO is not competitive for `2 ≤ k`** ([SleatorTarjan1985], Section 4, p. 208): over any
`k + 1` distinct pages (`pages.Nodup`, `pages.length = k + 1`), `lifoStrategy` from `∅` fails
`(c, b)`-competitiveness for every `c, b : Nat`. -/
theorem lifo_not_isCompetitiveFrom_empty {k : Nat} (hk2 : 2 ≤ k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1) (c b : Nat) :
    ¬ (lifoStrategy (α := α) k (by omega)).IsCompetitiveFrom ∅ c b := by
  have hsplit : pages.take (k - 1) ++ pages.drop (k - 1) = pages := List.take_append_drop _ _
  have hdrop_len : (pages.drop (k - 1)).length = 2 := by
    simp only [List.length_drop, hlen]; omega
  obtain ⟨a, b_pg, hdrop⟩ : ∃ a b_pg, pages.drop (k - 1) = [a, b_pg] := by
    cases h1 : pages.drop (k - 1) with
    | nil => simp only [h1, List.length_nil] at hdrop_len; omega
    | cons a rest =>
      cases rest with
      | nil => simp only [h1, List.length_singleton] at hdrop_len; omega
      | cons b_pg rest' =>
        simp only [h1, List.length_cons] at hdrop_len
        exact ⟨a, b_pg, congrArg (fun l => a :: b_pg :: l)
          (List.eq_nil_of_length_eq_zero (by omega))⟩
  set init := pages.take (k - 1)
  have hinit_len : init.length = k - 1 := by
    simp only [init, List.length_take, hlen]; omega
  have hnodup' : (init ++ [a, b_pg]).Nodup := by
    rwa [← hdrop, hsplit]
  set t := c * (k + 1) + b
  obtain ⟨offStates, hv, hoff⟩ := exists_offline_lifoCounterexample hk2 hinit_len hnodup' t
  have hlifo := lifoFaults_lifoCounterexample (k := k) (by omega) hinit_len hnodup' t
  intro hcomp
  have hbound := hcomp (lifoCounterexample init a b_pg t) offStates hv
  rw [lifoStrategy_cost_empty k (by omega), hlifo, hoff] at hbound
  omega

/-- Over `≥ k + 1` pages with `2 ≤ k`, `lifoStrategy` is not `(c, b)`-competitive. -/
theorem lifo_not_isCompetitive {k : Nat} (hk2 : 2 ≤ k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1) (c b : Nat) :
    ¬ (lifoStrategy (α := α) k (by omega)).IsCompetitive c b :=
  fun h => lifo_not_isCompetitiveFrom_empty hk2 hnodup hlen c b (h ∅ (validCache_empty k))

/-- Over `≥ k + 1` pages with `2 ≤ k`, `lifoStrategy` is not `(c, b)`-competitive across arbitrary
initial caches. -/
theorem lifo_not_isCompetitiveAnyInit {k : Nat} (hk2 : 2 ≤ k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1) (c b : Nat) :
    ¬ (lifoStrategy (α := α) k (by omega)).IsCompetitiveAnyInit c b :=
  fun h => lifo_not_isCompetitive hk2 hnodup hlen c b h.toIsCompetitive

/-- Canonical LIFO impossibility on `Fin (k + 1)` (`2 ≤ k`): LIFO from `∅` is not
`(c, b)`-competitive for any `c, b : Nat`. -/
theorem fin_lifo_not_isCompetitiveFrom_empty {k : Nat} (hk2 : 2 ≤ k) (c b : Nat) :
    ¬ (lifoStrategy (α := Fin (k + 1)) k (by omega)).IsCompetitiveFrom ∅ c b :=
  lifo_not_isCompetitiveFrom_empty hk2 (List.nodup_finRange (k + 1)) (List.length_finRange) c b

end Cslib.DataStructure.Paging
