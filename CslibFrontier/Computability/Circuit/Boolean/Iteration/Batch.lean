/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.InputTime
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.SharedDictionary
public import CslibFrontier.Computability.Circuit.Replication
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Batched fixed powers with one shared dictionary

A circuit with `r * n` inputs and outputs applies `f^[T]` to each of `r` independent `n`-bit
states (`blockMap`). All members share one checkpoint table: the orbit prefixes of all members
are looked up in one batched dictionary, and each member finishes on its own. For `r ≤ 2 ^ n` and
`0 < L` this costs at most `100000 * batchBudget n s (2 ^ n) r L` gates
(`batched_fixed_power`), where
`batchBudget n s M r L = r * L * s + (n + 1) ^ 3 * (r * L + M / L + 1)`;
the storage term `M / L` is paid once rather than `r` times. Balancing `L` gives
`200000 * (r * A + √((n + 1) ^ 3 * 2 ^ n * r * A))` with `A = s + (n + 1) ^ 3`
(`batched_fixed_power_optimized`).

If each trajectory's first `L` states lie in a finite set `S`, the same construction pays
`S.card / L` for the shared checkpoint table (`batched_fixed_power_on_prefixes`). The trajectories
may leave `S` later. In particular, an invariant set gives the tradeoff
`100000 * batchBudget n s S.card r L` (`batched_fixed_power_on`) and its balanced form
(`batched_fixed_power_on_optimized`). No correctness is required outside the stated input domain.

With a separate `m`-bit time for each member, binary powering with the batched powers costs
`m * (100000 * batchBudget n s (2 ^ n) r L + 4 * r * n)` (`batched_variable_time`), and
`m * (200000 * optimizedBatchBudget n s (2 ^ n) r + 4 * r * n)` balanced
(`batched_variable_time_optimized`). These input-time circuits specialize the shared
binary-powering rule in `Iteration.InputTime` to the batched fixed-power circuits proved here.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. The checkpoints are chosen nonconstructively, so the
circuits exist for each parameter choice; nothing here bounds the time to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.batchBudget`: the batched size tradeoff.
* `Cslib.Circuits.Boolean.Iteration.optimizedBatchBudget`: its balanced square-root form.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_batched_power`: the shared-dictionary construction.
* `Cslib.Circuits.Boolean.Iteration.batched_fixed_power`,
  `Cslib.Circuits.Boolean.Iteration.batched_fixed_power_optimized`: batched fixed powers.
* `Cslib.Circuits.Boolean.Iteration.batched_fixed_power_on_prefixes`: batched powers when the
  first `L` states of each trajectory lie in a finite set.
* `Cslib.Circuits.Boolean.Iteration.batched_fixed_power_on`,
  `Cslib.Circuits.Boolean.Iteration.batched_fixed_power_on_optimized`: invariant-set batches.
* `Cslib.Circuits.Boolean.Iteration.synthesis_batched_binary_powering`: binary powering of
  batches, with one time per member.
* `Cslib.Circuits.Boolean.Iteration.batched_variable_time`,
  `Cslib.Circuits.Boolean.Iteration.batched_variable_time_optimized`: batched input times.

## References

* Adapted from lean/Proofs/{BatchPowers,BatchVariableTime}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n m r a M : ℕ}

/-- The batched tradeoff `r * L * s + (n + 1) ^ 3 * (r * L + M / L + 1)` for `r` trajectories of
`n`-bit states, a transition circuit of size `s`, `M` relevant states and parameter `L`. -/
def batchBudget (n s M r L : ℕ) : ℕ :=
  r * L * s + (n + 1) ^ 3 * (r * L + M / L + 1)

/-- A single trajectory has the fixed-power tradeoff. -/
theorem batchBudget_one (n s M L : ℕ) : batchBudget n s M 1 L = powerBudget n s M L := by
  simp only [batchBudget, powerBudget, Nat.one_mul]

/-- A synthesis of every member's output block gives a circuit for the block map. -/
private theorem exists_circuit_blockMap {k : ℕ} {g : BitString n → BitString k} {C : ℕ}
    (h : Synthesis interpretation (inputs (r * n))
      (⋃ member, wires fun x => g (BitString.block x member)) C) :
    ∃ out : Circuit signature (r * n) (r * k),
      out.Computes interpretation (blockMap g r) ∧ out.size ≤ C := by
  refine (h.mono Set.Subset.rfl ?_ le_rfl).exists_circuit_outputs
  rintro _ ⟨i, rfl⟩
  exact Set.mem_iUnion.mpr ⟨(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2, rfl⟩

/-! ### Batched fixed powers -/

/-- The shared construction is synthesized on all inputs, but its correctness only needs
checkpoint coverage for the states in `S`. -/
private theorem synthesis_batched_power_on (c : Circuit signature n n)
    (s : Set (BooleanFunction a))
    (init : BitString a → Fin r → BitString n)
    (hi : ∀ member bit, (fun x => init x member bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s)
    (T L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hT : 2 * L ≤ T)
    (cp : Fin M → BitString n) (hcp : Function.Injective cp) (S : Set (BitString n))
    (hcover : ∀ x ∈ S, FunctionalGraph.Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j) :
    ∃ result : Fin r → BitString a → BitString n,
      (∀ member x, init x member ∈ S →
        result member x = (c.eval interpretation)^[T] (init x member)) ∧
      Synthesis interpretation s (⋃ member, wires (result member))
      (r * (2 * L * c.size) +
        48 * (r * (2 * L + 1) + M + 1) * (Nat.clog 2 (r * (2 * L + 1) + M) + 1) ^ 2 *
          (n + (n + 1) + 1) +
        r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * c.size +
          200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n c.size 0 L +
          4 * n)) := by
  let f := c.eval interpretation
  let K := 2 * L
  let orbit := fun member => Synthesis.stages (fun j => wires fun x => f^[j] (init x member)) K
  have hall : Synthesis interpretation s (⋃ member, orbit member) (r * (K * c.size)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      Synthesis.iUnion orbit (fun _ => K * c.size)
        fun member => Synthesis.orbit c (fun x => init x member) (hi member) K
  let s1 := s ∪ ⋃ member, orbit member
  let queries : BitString a → Fin (r * (K + 1)) → BitString n := fun x q =>
    f^[(finProdFinEquiv.symm q).2.val] (init x (finProdFinEquiv.symm q).1)
  have hquery (x : BitString a) (member : Fin r) (j : Fin (K + 1)) :
      queries x (finProdFinEquiv (member, j)) = f^[j.val] (init x member) := by
    simp only [queries, Equiv.symm_apply_apply]
  let stored : Fin M → BitString (n + 1) := fun j => Fin.cons true (f^[T - K] (cp j))
  have hdict := synthesis_lookupOr s1 cp stored queries fun q bit =>
    Or.inr (Set.mem_iUnion.mpr ⟨(finProdFinEquiv.symm q).1, Synthesis.subset_stages _
      (Nat.le_of_lt_succ (finProdFinEquiv.symm q).2.isLt) ⟨bit, rfl⟩⟩)
  let s2 := s1 ∪ ⋃ q, wires fun x => lookupOr cp stored (queries x q)
  have hresult (member : Fin r) (j : Fin (K + 1)) (bit : Fin (n + 1)) :
      (fun x => lookupOr cp stored (f^[j.val] (init x member)) bit) ∈ s2 :=
    Or.inr <| Set.mem_iUnion.mpr ⟨finProdFinEquiv (member, j), bit,
      funext fun x => congrArg (lookupOr cp stored · bit) (hquery x member j)⟩
  obtain ⟨fallback, hfall, hfs⟩ := exists_repeat_power c T L hL hLN hT
  let flags := fun member x (j : Fin (K + 1)) =>
    lookupOr cp stored (f^[j.val] (init x member)) 0
  let payloads := fun member x (j : Fin (K + 1)) (bit : Fin n) =>
    lookupOr cp stored (f^[j.val] (init x member)) bit.succ
  let finished := fun member x => finishHit (w := n + 2) f K (flags member x)
    (payloads member x) (fallback.eval interpretation (init x member))
  have hfinish (member : Fin r) : Synthesis interpretation s2 (wires (finished member))
      ((K + 1) * (4 * ((n + 2) + n + 1)) + K * c.size + 200 * (K + 1) * (n + (n + 2) + 1) ^ 2 +
        fallback.size + 4 * n) :=
    synthesis_finishHit c s2 K (flags member) (payloads member) _
      (fun j => hresult member j 0) (fun j bit => hresult member j bit.succ)
      (fun b => Or.inl (Or.inl (hc b)))
      (Synthesis.circuit (I := interpretation) (s := s2) fallback (fun i x => init x member i)
        fun i => Or.inl (Or.inl (hi member i)))
  have hcorrect (member : Fin r) (x : BitString a) (hx : init x member ∈ S) :
      finished member x = f^[T] (init x member) := by
    have hfit : K < 2 ^ (n + 2) := by simp only [K, Nat.pow_succ]; omega
    apply finishHit_correct f T K _ _ _ _ hfit hT
    · intro j hj
      obtain ⟨h, hh, -⟩ := (decide_eq_true_iff.mp hj : ∃ h, cp h = _ ∧ stored h 0 = true)
      funext bit
      simp only [payloads, lookupOr_of_eq stored hcp hh, stored, Fin.cons_succ, hh]
    · intro hnone
      refine (hcover (init x member) hx).elim (hfall _) fun ⟨t, ht, h, hh⟩ => ?_
      have hj := hnone ⟨t, by omega⟩
      simp only [flags, lookupOr, decide_eq_false_iff_not] at hj
      exact absurd ⟨h, hh.symm, rfl⟩ hj
  have hfam := Synthesis.iUnion (fun member => wires (finished member)) _ hfinish
  refine ⟨finished, hcorrect,
    (hall.trans (hdict.trans hfam)).mono Set.Subset.rfl Set.Subset.rfl ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, K, ← add_assoc]
  gcongr

/-- **Shared-dictionary powers.** Let `cp` be injective checkpoints such that every orbit repeats
among its first `L` states or reaches a checkpoint in fewer than `2 L` steps, and let
`2 L ≤ T`. Then `f^[T]` of `r` available states costs one orbit prefix of `2 L` steps per member,
one shared lookup of all prefix states against the `M` checkpoints, and one finishing step and
one checkpoint-free fixed-power circuit per member. -/
theorem synthesis_batched_power (c : Circuit signature n n) (s : Set (BooleanFunction a))
    (init : BitString a → Fin r → BitString n)
    (hi : ∀ member bit, (fun x => init x member bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s)
    (T L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hT : 2 * L ≤ T)
    (cp : Fin M → BitString n) (hcp : Function.Injective cp)
    (hcover : ∀ x, FunctionalGraph.Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j) :
    Synthesis interpretation s
      (⋃ member, wires fun x => (c.eval interpretation)^[T] (init x member))
      (r * (2 * L * c.size) +
        48 * (r * (2 * L + 1) + M + 1) * (Nat.clog 2 (r * (2 * L + 1) + M) + 1) ^ 2 *
          (n + (n + 1) + 1) +
        r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * c.size +
          200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n c.size 0 L +
          4 * n)) := by
  obtain ⟨result, hresult, hs⟩ := synthesis_batched_power_on c s init hi hc T L hL hLN hT
    cp hcp Set.univ (fun x _ => hcover x)
  refine hs.mono Set.Subset.rfl (fun _ hg => ?_) le_rfl
  obtain ⟨member, bit, rfl⟩ := Set.mem_iUnion.mp hg
  exact Set.mem_iUnion.mpr
    ⟨member, bit, funext fun x => congrFun (hresult member x (Set.mem_univ _)) bit⟩

/-- The construction cost is within `100000` times the batched tradeoff. -/
private theorem batch_construction_cost (n s M N r L : ℕ) (hN : N ≤ 2 ^ n)
    (hrN : r ≤ 2 ^ n) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hM : M ≤ N / L) :
    2 + (r * (2 * L * s) +
        48 * (r * (2 * L + 1) + M + 1) * (Nat.clog 2 (r * (2 * L + 1) + M) + 1) ^ 2 *
          (n + (n + 1) + 1) +
        r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * s +
          200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n s 0 L + 4 * n)) ≤
      100000 * batchBudget n s N r L := by
  set U := 2 ^ n with hUdef
  set d := Nat.clog 2 (r * (2 * L + 1) + M)
  set P := (n + 1) ^ 3
  have hU : 1 ≤ U := Nat.one_le_two_pow
  have hMU : M ≤ U := (hM.trans (Nat.div_le_self _ _)).trans hN
  have hd : d ≤ 2 * n + 2 := by
    apply Nat.clog_le_of_le_pow
    have he : 2 ^ (2 * n + 2) = 4 * (U * U) := by
      rw [pow_add, mul_comm 2 n, pow_mul, ← hUdef]
      ring
    have hp := Nat.mul_le_mul hrN hLN
    have hU2 := Nat.le_mul_of_pos_right U hU
    rw [he, mul_add, mul_one, mul_left_comm]
    omega
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hn1 : n + 1 ≤ P := Nat.le_self_pow (by decide) _
  have hn2 : (n + 1) ^ 2 ≤ P := Nat.pow_le_pow_right (by omega) (by decide)
  -- the shared dictionary
  have hwidth : (d + 1) ^ 2 * (n + (n + 1) + 1) ≤ 18 * P := by
    have h1 : (d + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 :=
      (Nat.pow_le_pow_left (by omega : d + 1 ≤ 3 * (n + 1)) 2).trans_eq (by ring)
    calc (d + 1) ^ 2 * (n + (n + 1) + 1) ≤ 9 * (n + 1) ^ 2 * (2 * (n + 1)) := by
          gcongr; omega
      _ = 18 * P := by simp only [P]; ring
  have hrecords : r * (2 * L + 1) + M + 1 ≤ 3 * (r * L) + N / L + 1 := by
    have hrL := Nat.mul_le_mul_left r hL
    rw [mul_add, mul_left_comm]
    omega
  have hdict : 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (n + 1) + 1) ≤
      864 * P * (3 * (r * L) + N / L + 1) := by
    calc 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (n + 1) + 1)
        = 48 * (r * (2 * L + 1) + M + 1) * ((d + 1) ^ 2 * (n + (n + 1) + 1)) := by ring
      _ ≤ 48 * (3 * (r * L) + N / L + 1) * (18 * P) := by gcongr
      _ = _ := by ring
  -- one member
  have hmember : (2 * L + 1) * (4 * ((n + 2) + n + 1)) +
      200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * (P * (L + 0 + 1)) + 4 * n ≤
        85440 * (L * P) := by
    have h1 : (2 * L + 1) * (4 * ((n + 2) + n + 1)) ≤ 36 * (L * P) :=
      (Nat.mul_le_mul (by omega : 2 * L + 1 ≤ 3 * L) (by omega : _ ≤ 12 * P)).trans_eq (by ring)
    have h2 : 200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤ 5400 * (L * P) := by
      have hs : (n + (n + 2) + 1) ^ 2 ≤ 9 * P := by
        calc (n + (n + 2) + 1) ^ 2 ≤ (3 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ ≤ 9 * P := by rw [mul_pow]; exact Nat.mul_le_mul_left _ hn2
      calc 200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤ 200 * (3 * L) * (9 * P) := by gcongr; omega
        _ = 5400 * (L * P) := by ring
    have h3 : 40000 * (P * (L + 0 + 1)) ≤ 80000 * (L * P) := by
      linarith [Nat.le_mul_of_pos_left P hL]
    have h4 : 4 * n ≤ 4 * (L * P) :=
      Nat.mul_le_mul_left 4 ((Nat.le_succ n).trans (hn1.trans (Nat.le_mul_of_pos_left P hL)))
    omega
  have hmem_full : (2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * s +
      200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n s 0 L + 4 * n ≤
        40002 * (L * s) + 85440 * (L * P) := by
    have hpb : powerBudget n s 0 L = L * s + P * (L + 0 + 1) := by rw [powerBudget, Nat.zero_div]
    rw [mul_assoc 2 L s, hpb, Nat.mul_add 40000]
    omega
  unfold batchBudget
  change 2 + (r * (2 * L * s) + 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 *
    (n + (n + 1) + 1) + r * _) ≤ 100000 * (r * L * s + P * (r * L + N / L + 1))
  calc 2 + (r * (2 * L * s) + 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 *
          (n + (n + 1) + 1) + r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * s +
            200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n s 0 L + 4 * n))
      ≤ 2 + (r * (2 * L * s) + 864 * P * (3 * (r * L) + N / L + 1) +
          r * (40002 * (L * s) + 85440 * (L * P))) := by gcongr
    _ = 2 + 40004 * (r * L * s) + 88032 * (P * (r * L)) + 864 * (P * (N / L)) + 864 * P := by ring
    _ ≤ 100000 * (r * L * s + P * (r * L + N / L + 1)) := by
        simp only [mul_add, mul_one]
        omega

/-- **Batched powers on promised prefixes.** If the first `L` states of each input trajectory
lie in `S`, one shared checkpoint table costs `S.card / L` in the batched tradeoff. The set need
not be invariant: later states may leave it. The circuit is only required to be correct on the
displayed input domain. All gates are charged; the time to construct the circuit is not bounded. -/
theorem batched_fixed_power_on_prefixes (c : Circuit signature n n)
    (S : Finset (BitString n)) (r T L : ℕ) (hrN : r ≤ 2 ^ n) (hL : 0 < L) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.ComputesOn interpretation
        {x | ∀ member : Fin r, ∀ i : Fin L,
          (c.eval interpretation)^[i.val] (BitString.block x member) ∈ S}
        (blockMap (c.eval interpretation)^[T] r) ∧
      out.size ≤ 100000 * batchBudget n c.size S.card r L := by
  classical
  have hrep (x : BitString (r * n)) : ((c.iterate T).replicate r).eval interpretation x =
      blockMap (c.eval interpretation)^[T] r x := by
    ext i
    simp [Circuit.eval_replicate, blockMap, Circuit.eval_iterate]
  wlog hLN : L ≤ 2 ^ n generalizing L
  · -- A longer prefix only strengthens the promise, and for a nonempty batch the budget at
    -- `L = 2 ^ n` is at most the budget at `L`.
    have hNL : 2 ^ n < L := not_le.1 hLN
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨(c.iterate T).replicate 0, fun x _ => hrep x,
        by rw [Circuit.size_replicate, Nat.zero_mul]; exact Nat.zero_le _⟩
    obtain ⟨out, hout, hs⟩ := this (2 ^ n) (Nat.two_pow_pos n) le_rfl
    refine ⟨out, fun x hx => hout fun member i => hx member ⟨i, i.isLt.trans hNL⟩, hs.trans ?_⟩
    have hcard : S.card ≤ 2 ^ n := by simpa using Finset.card_le_univ S
    have hdiv : S.card / 2 ^ n ≤ 1 := Nat.div_le_of_le_mul (by omega)
    have hrL : r * (2 ^ n + 1) ≤ r * L := Nat.mul_le_mul_left r hNL
    rw [Nat.mul_add_one] at hrL
    have h1 : r * 2 ^ n * c.size ≤ r * L * c.size :=
      Nat.mul_le_mul_right c.size (Nat.mul_le_mul_left r hNL.le)
    have h2 : (n + 1) ^ 3 * (r * 2 ^ n + S.card / 2 ^ n + 1) ≤
        (n + 1) ^ 3 * (r * L + S.card / L + 1) :=
      Nat.mul_le_mul_left _ (by have := Nat.zero_le (S.card / L); omega)
    unfold batchBudget
    exact Nat.mul_le_mul_left 100000 (Nat.add_le_add h1 h2)
  let f := c.eval interpretation
  by_cases hT : T < 2 * L
  · refine ⟨(c.iterate T).replicate r, fun x _ => hrep x, ?_⟩
    rw [Circuit.size_replicate, Circuit.size_iterate]
    have h1 : r * (T * c.size) ≤ 2 * (r * L * c.size) :=
      (by gcongr : r * (T * c.size) ≤ r * (2 * L * c.size)).trans_eq (by ring)
    unfold batchBudget
    omega
  obtain ⟨H, _, hcard, hcover⟩ := FunctionalGraph.exists_checkpoints_on f S hL
  let cp : Fin H.card → BitString n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := fun i j h => H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : BitString n) (hx : ∀ i : Fin L, f^[i.val] x ∈ S) :
      FunctionalGraph.Repeats f x L ∨ ∃ t < 2 * L, ∃ j, f^[t] x = cp j :=
    (hcover x hx).imp_right fun ⟨t, ht, hmem⟩ => ⟨t, ht, H.equivFin ⟨_, hmem⟩, by simp [cp]⟩
  let constants : Set (BooleanFunction (r * n)) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs (r * n)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  obtain ⟨result, hresult, hs⟩ := synthesis_batched_power_on c (inputs (r * n) ∪ constants)
    (fun x member => BitString.block x member) (fun _ _ => Or.inl ⟨_, rfl⟩)
    (fun b => Or.inr (by cases b <;> simp [constants])) T L hL hLN (by omega) cp hcp
    {x | ∀ i : Fin L, f^[i.val] x ∈ S} hcov
  obtain ⟨out, hout, hsize⟩ := ((hconst.trans hs).mono Set.Subset.rfl
    (Set.range_subset_iff.mpr fun i => Set.mem_iUnion.mpr
      ⟨(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2, rfl⟩)
    le_rfl).exists_circuit_outputs
  refine ⟨out, fun x hx => (hout x).trans
    (funext fun i => congrFun (hresult _ x (hx _)) _), hsize.trans ?_⟩
  exact batch_construction_cost n c.size H.card S.card r L
    (by simpa using Finset.card_le_univ S) hrN hL hLN ((Nat.le_div_iff_mul_le hL).mpr hcard)

/-- **Batched powers on an invariant set.** The checkpoint storage term `S.card / L` is shared
by all `r` trajectories. The batch may have more members than `S` has states. -/
theorem batched_fixed_power_on (c : Circuit signature n n) (S : Finset (BitString n))
    (r T L : ℕ) (hS : ∀ x ∈ S, c.eval interpretation x ∈ S)
    (hrN : r ≤ 2 ^ n) (hL : 0 < L) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.ComputesOn interpretation
        {x | ∀ member : Fin r, BitString.block x member ∈ S}
        (blockMap (c.eval interpretation)^[T] r) ∧
      out.size ≤ 100000 * batchBudget n c.size S.card r L := by
  obtain ⟨out, hout, hs⟩ := batched_fixed_power_on_prefixes c S r T L hrN hL
  refine ⟨out, fun x hx => hout fun member i => ?_, hs⟩
  induction i.val with
  | zero => exact hx member
  | succ t ih => simpa only [Function.iterate_succ_apply'] using hS _ ih

/-- **Batched fixed powers.** For `r ≤ 2 ^ n` and `0 < L`, some circuit of size at most
`100000 * batchBudget n c.size (2 ^ n) r L` applies `T` steps of `c` to each of `r` independent
states. -/
theorem batched_fixed_power (c : Circuit signature n n) (r T L : ℕ) (hrN : r ≤ 2 ^ n)
    (hL : 0 < L) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.Computes interpretation (blockMap (c.eval interpretation)^[T] r) ∧
      out.size ≤ 100000 * batchBudget n c.size (2 ^ n) r L := by
  classical
  obtain ⟨out, hout, hs⟩ := batched_fixed_power_on c Finset.univ r T L
    (fun _ _ => Finset.mem_univ _) hrN hL
  refine ⟨out, fun x => hout (fun _ => Finset.mem_univ _), ?_⟩
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hs

/-- The balanced batched budget `r * A + √((n + 1) ^ 3 * M * r * A)` with `A = s + (n + 1) ^ 3`. -/
noncomputable def optimizedBatchBudget (n s M r : ℕ) : ℝ :=
  (r * (s + (n + 1) ^ 3) : ℕ) + Real.sqrt ((n + 1 : ℝ) ^ 3 * M * (r * (s + (n + 1) ^ 3) : ℕ))

/-- A single trajectory has the balanced fixed-power budget. -/
theorem optimizedBatchBudget_one (n s M : ℕ) :
    optimizedBatchBudget n s M 1 = optimizedBudget n s M := by
  simp only [optimizedBatchBudget, optimizedBudget, Nat.one_mul]

private theorem exists_batchBudget_le_optimizedBatchBudget (n s M r : ℕ) (hr : 0 < r)
    (hM : M ≤ 2 ^ n) :
    ∃ L : ℕ, 0 < L ∧ (batchBudget n s M r L : ℝ) ≤ 2 * optimizedBatchBudget n s M r := by
  have hb : (n + 1) ^ 3 ≤ r * (s + (n + 1) ^ 3) :=
    (Nat.le_add_left _ s).trans (Nat.le_mul_of_pos_left _ hr)
  obtain ⟨L, hL, -, h⟩ := exists_le_add_add_two_mul_sqrt (r * (s + (n + 1) ^ 3)) ((n + 1) ^ 3)
    M (2 ^ n) (by positivity) hb hM (by positivity)
  have he : batchBudget n s M r L = r * (s + (n + 1) ^ 3) * L + (n + 1) ^ 3 * (M / L + 1) := by
    dsimp only [batchBudget]; ring
  have hb' : (((n + 1) ^ 3 : ℕ) : ℝ) ≤ (r * (s + (n + 1) ^ 3) : ℕ) := Nat.cast_le.2 hb
  refine ⟨L, hL, ?_⟩
  simp only [he, optimizedBatchBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    at h hb' ⊢
  linarith only [h, hb']

/-- **Square-root batched powers on an invariant set.** The balanced shared-storage bound uses
`S.card` rather than the size of the ambient state space. -/
theorem batched_fixed_power_on_optimized (c : Circuit signature n n)
    (S : Finset (BitString n)) (r T : ℕ) (hS : ∀ x ∈ S, c.eval interpretation x ∈ S)
    (hr : 0 < r) (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.ComputesOn interpretation
        {x | ∀ member : Fin r, BitString.block x member ∈ S}
        (blockMap (c.eval interpretation)^[T] r) ∧
      (out.size : ℝ) ≤ 200000 * optimizedBatchBudget n c.size S.card r := by
  obtain ⟨L, hL, hopt⟩ := exists_batchBudget_le_optimizedBatchBudget n c.size S.card r hr
    (by simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
      Finset.card_le_univ S)
  obtain ⟨out, hout, hs⟩ := batched_fixed_power_on c S r T L hS hrN hL
  exact ⟨out, hout, by cast_linarith only [hopt, hs]⟩

/-- **Square-root batched fixed powers.** -/
theorem batched_fixed_power_optimized (c : Circuit signature n n) (r T : ℕ) (hr : 0 < r)
    (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.Computes interpretation (blockMap (c.eval interpretation)^[T] r) ∧
      (out.size : ℝ) ≤ 200000 * optimizedBatchBudget n c.size (2 ^ n) r := by
  obtain ⟨L, hL, hopt⟩ := exists_batchBudget_le_optimizedBatchBudget n c.size (2 ^ n) r hr
    le_rfl
  obtain ⟨out, hout, hs⟩ := batched_fixed_power c r T L hrN hL
  exact ⟨out, hout, by cast_linarith only [hopt, hs]⟩

/-! ### Batched input times -/

/-- **Batched input times.** For `r ≤ 2 ^ n` and `0 < L`, some circuit of size at most
`m * (100000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n))` iterates `c` on each of `r`
independent states for that member's own number of steps, given by `m` input bits. -/
theorem batched_variable_time (c : Circuit signature n n) (r m L : ℕ) (hrN : r ≤ 2 ^ n)
    (hL : 0 < L) :
    ∃ out : Circuit signature (r * (n + m)) (r * n),
      out.Computes interpretation (blockMap (inputTimeIterate (c.eval interpretation) m) r) ∧
      out.size ≤ m * (100000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n)) :=
  exists_circuit_blockMap (synthesis_batched_binary_powering (c.eval interpretation) _
    (fun j _ => batched_fixed_power c r (2 ^ j) L hrN hL) (inputs (r * (n + m)))
    (fun x member i => BitString.block x member (Fin.castAdd m i))
    (fun x member j => BitString.block x member (Fin.natAdd n j))
    (fun _ _ => ⟨_, rfl⟩) fun _ _ => ⟨_, rfl⟩)

/-- **Square-root batched input times.** -/
theorem batched_variable_time_optimized (c : Circuit signature n n) (r m : ℕ) (hr : 0 < r)
    (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * (n + m)) (r * n),
      out.Computes interpretation (blockMap (inputTimeIterate (c.eval interpretation) m) r) ∧
      (out.size : ℝ) ≤ m * (200000 * optimizedBatchBudget n c.size (2 ^ n) r + 4 * (r * n)) := by
  obtain ⟨L, hL, hopt⟩ := exists_batchBudget_le_optimizedBatchBudget n c.size (2 ^ n) r hr
    le_rfl
  obtain ⟨out, hout, hs⟩ := batched_variable_time c r m L hrN hL
  refine ⟨out, hout, ((Nat.cast_le (α := ℝ)).2 hs).trans ?_⟩
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith only [hopt]) m.cast_nonneg

end Cslib.Circuits.Boolean.Iteration
