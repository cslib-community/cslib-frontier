/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Moser
public import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# The entropy-compression argument for Moser's algorithm

A run of Moser's algorithm (`CslibFrontier.Logics.Propositional.CNF.Moser`) is recorded by an
*execution log*. Each move contributes one bit, which separates a pass of `Solve` over a satisfied
clause from a call of `Fix` by `Solve`, or a returning `Fix` call from a recursive one. A recursive
call is followed by the position of its clause among the clauses sharing a variable with the
caller, in `L` bits, where `2 ^ L` exceeds every clause degree. The log of a run with a budget of
`t` resamplings has at most `m + t (L + 2)` bits (`length_log_le`).

Replaying the log recomputes the resampled clauses. A resampled clause was violated just before
its resampling, which determines the old values of its variables, so rewinding the final
assignment recovers every tape bit the run read (`decode_run`). A tape of length `n + t k` whose
run uses up the budget is therefore determined by its final assignment (`n` bits) and its log, and
there are fewer than `2 ^ (n + m + 1 + t (L + 2))` such tapes (`card_exhausts_lt`).

If every clause shares a variable with fewer than `2 ^ (k - 3)` other clauses, take `L = k - 3`.
Then fewer than a `2 ^ (m + 1 - t)` fraction of the tapes of length `n + t k` use up `t`
resamplings (`card_exhausts_mul_two_pow_lt`). For `t = m + 1` some tape does not, so the formula is
satisfiable (`satisfiable_of_degree_lt`). This is the entropy-compression argument as presented
by Fortnow [Fortnow2009], with the bound `r < 2 ^ (k - 3)` that Fortnow reports from Moser's STOC
2009 talk. The paper [Moser2009] analyses its algorithm differently, by counting witness trees,
under the stronger hypothesis that each clause shares a variable with at most `2 ^ (k - 5)`
clauses, itself included (its Theorem 1.2); neither that argument nor that bound is formalized
here. Fortnow encodes each `Fix` call made by `Solve` in `log m` bits; here the scan of `Solve`
costs one bit per clause.

## Main definitions

* `Cslib.Logic.PL.Moser.log`: the execution log.
* `Cslib.Logic.PL.Moser.decode`: the tape recovered from a final assignment and a log.

## Main results

* `Cslib.Logic.PL.Moser.length_log_le`: the log has at most `m + t (L + 2)` bits.
* `Cslib.Logic.PL.Moser.decode_run`: **recoverability** of the tape.
* `Cslib.Logic.PL.Moser.card_exhausts_lt`, `Cslib.Logic.PL.Moser.card_exhausts_mul_two_pow_lt`:
  the counting bounds.
* `Cslib.Logic.PL.Moser.satisfiable_of_degree_lt`: the Local Lemma for `k`-SAT, constructively.

## References

* [R. A. Moser, *A constructive proof of the Lovász Local Lemma*][Moser2009]
* [L. Fortnow, *A Kolmogorov Complexity Proof of the Lovász Local Lemma*][Fortnow2009]
-/

public section

namespace Cslib.Logic.PL.Moser

open Finset

variable {n : ℕ} (φ : CNF (Fin n))

/-! ### The log and the decoder -/

/-- The execution log of a move: one bit for the kind of move, followed by the `L`-bit position of
the clause of a recursive call. -/
@[expose] def bits (L : ℕ) : Move φ.length → List Bool
  | .skip | .pop => [false]
  | .root _ => [true]
  | .child pos _ => true :: BitString.lowBits L pos
  | .stop => []

/-- The execution log of the first `N` steps. -/
@[expose] def log (k t L : ℕ) (x : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | N + 1 => log k t L x N ++ bits φ L (move φ t (run φ k t x N))

/-- Replay an execution log, recomputing the control state. -/
@[expose] def replay (L : ℕ) : Control φ.length → List Bool → Control φ.length
  | c, [] => c
  | ⟨[], ptr, trace⟩, false :: w => replay L ⟨[], ptr + 1, trace⟩ w
  | ⟨[], ptr, trace⟩, true :: w =>
    if h : ptr < φ.length then replay L ⟨[⟨ptr, h⟩], ptr + 1, ⟨ptr, h⟩ :: trace⟩ w
    else ⟨[], ptr, trace⟩
  | ⟨_ :: st, ptr, trace⟩, false :: w => replay L ⟨st, ptr, trace⟩ w
  | ⟨e :: st, ptr, trace⟩, true :: w =>
    match (neighbors φ e)[BitString.lsbValue (w.take L)]? with
    | some d => replay L ⟨d :: e :: st, ptr, d :: trace⟩ (w.drop L)
    | none => ⟨e :: st, ptr, trace⟩
termination_by _ w => w.length

/-- Recover the tape from an assignment and the resampled clauses (latest first): the bits read by
the latest resampling are the current values of the variables of its clause, and the earlier bits
are recovered after undoing it. -/
@[expose] def recoverTape (k : ℕ) : List (Fin φ.length) → (Fin n → Bool) → ℕ → Bool
  | [], σ, i => if h : i < n then σ ⟨i, h⟩ else false
  | c :: tr, σ, i =>
    if n + tr.length * k ≤ i then
      match (vbl φ[c])[i - (n + tr.length * k)]? with
      | some v => σ v
      | none => false
    else recoverTape k tr (unresample φ[c] σ) i

/-- The decoder: the tape recovered from a final assignment and an execution log. -/
@[expose] def decode (k L : ℕ) (σ : Fin n → Bool) (w : List Bool) : ℕ → Bool :=
  recoverTape φ k (replay φ L ⟨[], 0, []⟩ w).trace σ

variable {φ}

/-! ### Recovering the tape -/

variable (φ) in
/-- The recovery invariant: the tape bits read so far are recovered from the current assignment and
the resampled clauses. -/
def Recovers (k : ℕ) (x : ℕ → Bool) (s : State n φ.length) : Prop :=
  ∀ i < n + s.trace.length * k, recoverTape φ k s.trace s.assignment i = x i

theorem recovers_init (k : ℕ) (x : ℕ → Bool) : Recovers φ k x (init φ x) := by
  intro i hi
  have hi' : i < n := by simpa [init] using hi
  simp [recoverTape, init, hi']

theorem recovers_resample {k : ℕ} (hφ : φ.IsExactDistinct k) {x : ℕ → Bool} {σ : Fin n → Bool}
    {tr : List (Fin φ.length)} (hs : ∀ i < n + tr.length * k, recoverTape φ k tr σ i = x i)
    {c : Fin φ.length} (hc : φ[c].eval σ = false) :
    ∀ i < n + (tr.length + 1) * k,
      recoverTape φ k (c :: tr) (resample φ[c] x (n + tr.length * k) σ) i = x i := by
  intro i hi
  obtain ⟨hlen, hnd⟩ := hφ _ (getElem_mem_fin c)
  rw [add_mul, one_mul] at hi
  simp only [recoverTape]
  split_ifs with ho
  · have hlt : i - (n + tr.length * k) < (vbl φ[c]).length := by
      rw [List.length_map, hlen]
      omega
    simp only [List.getElem?_eq_getElem hlt]
    rw [resample_getElem hnd]
    congr 1
    omega
  · rw [unresample_resample hc]
    exact hs i (by omega)

theorem recovers_step {k : ℕ} (hφ : φ.IsExactDistinct k) (t : ℕ) (x : ℕ → Bool)
    {s : State n φ.length} (hs : Recovers φ k x s) : Recovers φ k x (step φ k t x s) := by
  rcases move_cases t s with ⟨hm, -⟩ | ⟨c, hm, -, -, hev, -⟩ | ⟨e, st, d, hm, -, -, hev, -⟩ |
    ⟨e, st, hm, -⟩ | ⟨hm, -⟩ <;> simp only [Recovers, step, hm, apply, List.length_cons]
  exacts [hs, recovers_resample hφ hs hev, recovers_resample hφ hs hev, hs, hs]

theorem recovers_run {k : ℕ} (hφ : φ.IsExactDistinct k) (t : ℕ) (x : ℕ → Bool) (N : ℕ) :
    Recovers φ k x (run φ k t x N) := by
  induction N with
  | zero => exact recovers_init k x
  | succ N ih => exact recovers_step hφ t x ih

/-! ### The length of the log -/

theorem ptr_run_le (k t : ℕ) (x : ℕ → Bool) (N : ℕ) : (run φ k t x N).ptr ≤ φ.length := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [run_succ]
    rcases move_cases t (run φ k t x N) with ⟨hm, -, hp, -⟩ | ⟨c, hm, -, hc, -⟩ |
      ⟨_, _, _, hm, -⟩ | ⟨_, _, hm, -⟩ | ⟨hm, -⟩ <;> simp only [step, hm, apply]
    · omega
    · exact hc ▸ c.2
    · exact ih
    · exact ih
    · exact ih

theorem length_log_add_le (k t L : ℕ) (x : ℕ → Bool) (N : ℕ) :
    (log φ k t L x N).length + (run φ k t x N).stack.length ≤
      (run φ k t x N).ptr + (run φ k t x N).trace.length * (L + 2) := by
  induction N with
  | zero => simp [log, run, init]
  | succ N ih =>
    rw [log, run_succ]
    rcases move_cases t (run φ k t x N) with ⟨hm, -⟩ | ⟨_, hm, hst, -⟩ | ⟨_, _, _, hm, -⟩ |
      ⟨_, _, hm, hst, -⟩ | ⟨hm, -⟩ <;>
      simp_all only [step, apply, bits, List.length_append, List.length_cons, List.length_nil,
        List.tail_cons, BitString.length_lowBits, add_mul, one_mul] <;> omega

/-- **Log length.** The execution log of a run with a budget of `t` resamplings has at most
`m + t (L + 2)` bits. -/
theorem length_log_le (k t L : ℕ) (x : ℕ → Bool) (N : ℕ) :
    (log φ k t L x N).length ≤ φ.length + t * (L + 2) := by
  have h1 := length_log_add_le (φ := φ) k t L x N
  have h2 := ptr_run_le (φ := φ) k t x N
  have h3 := Nat.mul_le_mul_right (L + 2) (length_trace_run_le (φ := φ) k t x N)
  omega

/-! ### Replaying the log -/

theorem replay_nil (L : ℕ) (c : Control φ.length) : replay φ L c [] = c := by
  simp only [replay]

theorem replay_step {L : ℕ} (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) (k t : ℕ)
    (x : ℕ → Bool) (s : State n φ.length) (w : List Bool) :
    replay φ L s.toControl (bits φ L (move φ t s) ++ w) =
      replay φ L (step φ k t x s).toControl w := by
  obtain ⟨⟨stack, ptr, trace⟩, σ⟩ := s
  rcases move_cases t ⟨⟨stack, ptr, trace⟩, σ⟩ with ⟨hm, hst, -⟩ | ⟨⟨c, hcm⟩, hm, hst, hc, -⟩ |
    ⟨e, st, d, hm, hst, hd, -⟩ | ⟨e, st, hm, hst, -⟩ | ⟨hm, -⟩
  · cases hst
    simp [hm, bits, step, apply, replay]
  · cases hst
    cases hc
    simp [hm, bits, step, apply, replay, hcm]
  · cases hst
    have hpos : (neighbors φ e).idxOf d < 2 ^ L :=
      (List.idxOf_lt_length_of_mem hd).trans_le ((length_neighbors_le e).trans (hL e))
    simp [hm, bits, step, apply, replay, BitString.length_lowBits,
      BitString.lsbValue_lowBits hpos, List.getElem?_idxOf hd]
  · cases hst
    simp [hm, bits, step, apply, replay]
  · simp [hm, bits, step, apply]

theorem replay_log {L : ℕ} (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) (k t : ℕ)
    (x : ℕ → Bool) (N : ℕ) (w : List Bool) :
    replay φ L ⟨[], 0, []⟩ (log φ k t L x N ++ w) = replay φ L (run φ k t x N).toControl w := by
  induction N generalizing w with
  | zero => rfl
  | succ N ih => rw [log, List.append_assoc, ih, replay_step hL k t x, run_succ]

/-- **Recoverability.** If every clause shares a variable with fewer than `2 ^ L` other clauses,
then after any number of steps the decoder recovers every tape bit read so far from the current
assignment and the execution log. -/
theorem decode_run {k L : ℕ} (hφ : φ.IsExactDistinct k)
    (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) (t : ℕ) (x : ℕ → Bool) (N : ℕ) :
    ∀ i < n + (run φ k t x N).trace.length * k,
      decode φ k L (run φ k t x N).assignment (log φ k t L x N) i = x i := by
  have h := replay_log hL k t x N []
  rw [List.append_nil, replay_nil] at h
  intro i hi
  rw [decode, h]
  exact recovers_run hφ t x N i hi

/-! ### Counting -/

/-- **Counting.** If every clause shares a variable with fewer than `2 ^ L` other clauses, fewer
than `2 ^ (n + m + 1 + t (L + 2))` tapes of length `n + t k` (padded with `false`) use up a budget
of `t` resamplings. -/
theorem card_exhausts_lt {k L : ℕ} (hφ : φ.IsExactDistinct k)
    (hL : ∀ c : Fin φ.length, degree φ c < 2 ^ L) (t : ℕ) :
    #{y : Fin (n + t * k) → Bool | Exhausts φ k t (Function.extend Fin.val y fun _ => false)} <
      2 ^ (n + φ.length + 1 + t * (L + 2)) := by
  classical
  let ext (y : Fin (n + t * k) → Bool) : ℕ → Bool := Function.extend Fin.val y fun _ => false
  calc #{y : Fin (n + t * k) → Bool | Exhausts φ k t (ext y)}
      ≤ #((univ : Finset (Fin n → Bool)) ×ˢ BitString.shortWords (φ.length + t * (L + 2))) := by
        refine card_le_card_of_injOn
          (fun y => ((final φ k t (ext y)).assignment, log φ k t L (ext y) (fuel φ t)))
          (fun _ _ => by simp [BitString.mem_shortWords, length_log_le])
          fun y hy y' hy' h => funext fun i => ?_
        have h1 := decode_run hφ hL t (ext y) (fuel φ t) i
          (by rw [← final, length_trace_final_eq (mem_filter.mp hy).2]; exact i.2)
        have h2 := decode_run hφ hL t (ext y') (fuel φ t) i
          (by rw [← final, length_trace_final_eq (mem_filter.mp hy').2]; exact i.2)
        rw [← final] at h1 h2
        simpa only [ext, (Prod.mk.inj h).1, (Prod.mk.inj h).2, h2,
          Fin.val_injective.extend_apply] using h1.symm
    _ = 2 ^ n * #(BitString.shortWords (φ.length + t * (L + 2))) := by simp
    _ < 2 ^ n * 2 ^ (φ.length + t * (L + 2) + 1) :=
        Nat.mul_lt_mul_of_pos_left (BitString.card_shortWords_lt _) (Nat.two_pow_pos n)
    _ = 2 ^ (n + φ.length + 1 + t * (L + 2)) := by
        rw [← pow_add]
        congr 1
        omega

/-- **Moser's counting bound.** If every clause of an exact `k`-CNF shares a variable with fewer
than `2 ^ (k - 3)` other clauses, fewer than a `2 ^ (m + 1 - t)` fraction of the tapes of length
`n + t k` use up a budget of `t` resamplings. -/
theorem card_exhausts_mul_two_pow_lt {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) (t : ℕ) :
    #{y : Fin (n + t * k) → Bool | Exhausts φ k t (Function.extend Fin.val y fun _ => false)} *
      2 ^ t < 2 ^ (n + t * k) * 2 ^ (φ.length + 1) := by
  have h := card_exhausts_lt (L := k - 3) hφ hdeg t
  have hk' : t * (k - 3 + 2) + t = t * k := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  calc _ < 2 ^ (n + φ.length + 1 + t * (k - 3 + 2)) * 2 ^ t :=
        Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos t)
    _ = 2 ^ (n + t * k) * 2 ^ (φ.length + 1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega

/-- **The Local Lemma for `k`-SAT, constructively.** If every clause of an exact `k`-CNF shares a
variable with fewer than `2 ^ (k - 3)` other clauses, the formula is satisfiable: on some tape of
length `n + (m + 1) k` the algorithm stops with a satisfying assignment. -/
theorem satisfiable_of_degree_lt {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) : φ.Satisfiable := by
  classical
  have h := card_exhausts_mul_two_pow_lt hk hφ hdeg (φ.length + 1)
  have hlt := Nat.lt_of_mul_lt_mul_right h
  by_contra hns
  have hall (y : Fin (n + (φ.length + 1) * k) → Bool) :
      Exhausts φ k (φ.length + 1) (Function.extend Fin.val y fun _ => false) := by
    by_contra hy
    exact hns ⟨_, eval_final_of_not_exhausts (hφ.ne_nil (by omega)) hy⟩
  rw [filter_true_of_mem (fun y _ => hall y), card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hlt
  exact lt_irrefl _ hlt

end Cslib.Logic.PL.Moser
