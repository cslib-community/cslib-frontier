/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CollisionResistant.BruteForce
import CslibFrontier.Foundations.Data.BitString.List.LowBits

/-!
# Tests for the brute-force collision finder

Checks for `CslibFrontier/Crypto/Computational/CollisionResistant/BruteForce.lean` as a `module`
client with ordinary imports:

* Concrete evaluation (`decide`) of `collidingPair?` on `2 ^ 2 + 1 = 5` three-bit messages under a
  `2`-bit hash: the first four digests are distinct and the fifth collides with the first.
* Sharpness of `D.card < s`: `s = 2 ^ ℓ` evaluations do not suffice for any `ℓ : ℕ`, witnessed by
  the identity map on the `2 ^ ℓ` binary words of length `ℓ`.
* Pigeonhole (`isSome_collidingPair?_of_card_lt`), soundness (`bruteForceFinder_sound`), and
  deterministic run characterization (`eval_run_bruteForceFinder`), including a non-bit-string
  domain and a multi-query digest.
* The edge case `ℓ = 0` (`2 ^ 0 + 1 = 2` evaluations on a `0`-bit hash).
* The explicit example of [BonehShoup2023], §8.3, printed p. 294: `ℓ = 16` requires at most
  `2 ^ 16 + 1 = 65537` hash evaluations and finds a collision with probability `1` for every
  `16`-bit hash.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BruteForceCollision

open Cslib Cslib.Crypto

/-! ## Concrete search and sharpness on `ℓ = 2` -/

/-- For `ℓ = 2`, the first `2 ^ 2 = 4` three-bit words have distinct `2`-bit prefixes, so `4`
evaluations do not find a collision. -/
example :
    collidingPair? (fun i : Fin 4 => BitString.lowBits 3 i)
      (fun i : Fin 4 => (BitString.lowBits 3 i).take 2) = none := by decide

/-- Adding a fifth three-bit word (`2 ^ 2 + 1 = 5` evaluations) forces a collision between
`[false, false, false]` (`i = 0`) and `[false, false, true]` (`i = 4`) at digest
`[false, false]`. -/
example :
    collidingPair? (fun i : Fin 5 => BitString.lowBits 3 i)
      (fun i : Fin 5 => (BitString.lowBits 3 i).take 2) =
        some ([false, false, false], [false, false, true], [false, false]) := by decide

/-! ## Sharpness of `D.card < s` for every digest length `ℓ` -/

/-- `s = 2 ^ ℓ` evaluations do not suffice for any `ℓ : ℕ`: the `2 ^ ℓ` distinct `ℓ`-bit words
`BitString.lowBits ℓ` have distinct `ℓ`-bit digests under `id`, so `collidingPair?` returns `none`
and `bruteForceFinder` succeeds with probability `0`. -/
example (ℓ : ℕ) :
    let ms : Fin (2 ^ ℓ) → List Bool := fun i => BitString.lowBits ℓ i
    Function.Injective ms ∧
      (∀ i, (id (ms i)).length = ℓ) ∧
      collidingPair? ms (fun i => id (ms i)) = none ∧
      (ProbComp.eval ((bruteForceFinder
        (spec := fun _ : List Bool => List Bool) ProbOracleComp.query ms).run
          fun m => pure (id m))).toOuterMeasure (collisionOutputs id) = 0 := by
  intro ms
  have hinj : Function.Injective ms := fun i j hij =>
    Fin.ext (BitString.lowBits_injective_of_lt i.isLt j.isLt hij)
  have hnone : collidingPair? ms (fun i => id (ms i)) = none := by
    rw [← Option.not_isSome_iff_eq_none, isSome_collidingPair?_iff]
    rintro ⟨i, j, hij, hne⟩
    exact hne hij
  refine ⟨hinj, fun i => BitString.length_lowBits ℓ i, hnone, ?_⟩
  rw [eval_run_bruteForceFinder id id (fun i => ProbOracleComp.run_query (ms i) _), hnone,
    PMF.toOuterMeasure_pure_apply, ite_eq_right]
  rintro ⟨m, m', -, -, ⟨⟩⟩

/-! ## General domain (`Fin n`), soundness, and multi-query digests -/

/-- General pigeonhole (`isSome_collidingPair?_of_card_lt` and `bruteForceFinder_success`) on
`n + 1` natural numbers mapped into `Fin n`. -/
example {n : ℕ} (f : ℕ → Fin n) :
    (collidingPair? (s := n + 1) Fin.val (fun i => f i.val)).isSome ∧
      (ProbComp.eval ((bruteForceFinder
        (spec := fun _ : ℕ => Fin n) ProbOracleComp.query (s := n + 1) Fin.val).run
          fun x => pure (f x))).toOuterMeasure (collisionOutputs f) = 1 :=
  ⟨isSome_collidingPair?_of_card_lt Fin.val_injective (fun _ => Finset.mem_univ _)
      (by simp),
    bruteForceFinder_success f f Fin.val_injective (fun _ => ProbOracleComp.run_query _ _)
      Finset.univ (fun _ => Finset.mem_univ _) (by simp)⟩

/-- Soundness (`bruteForceFinder_sound`) and run characterization (`eval_run_bruteForceFinder`):
every pair returned by `bruteForceHashFinder ℓ` consists of two distinct `(ℓ + 1)`-bit messages
with the reported digest. -/
example (ℓ : ℕ) (H : List Bool → List Bool) {m m' d : List Bool}
    (ho : some (m, m', d) ∈
      (ProbComp.eval ((bruteForceHashFinder ℓ).run fun x => pure (H x))).support) :
    m ≠ m' ∧ m.length = ℓ + 1 ∧ m'.length = ℓ + 1 ∧ H m = d ∧ H m' = d := by
  have hc := bruteForceFinder_sound H H (fun _ => ProbOracleComp.run_query _ _) ho (by simp)
  rw [bruteForceHashFinder,
    eval_run_bruteForceFinder H H (fun _ => ProbOracleComp.run_query _ _),
    PMF.mem_support_pure_iff] at ho
  obtain ⟨hne, i, j, rfl, rfl, rfl, hd⟩ := collidingPair?_eq_some ho.symm
  simp only [collisionOutputs, Set.mem_ofPred_eq] at hc
  exact ⟨hne, BitString.length_lowBits _ _, BitString.length_lowBits _ _, rfl, hd⟩

/-- Multi-call digest (`c = 2`): hashing twice per message (`H ∘ H`) costs at most
`(2 ^ ℓ + 1) * 2` oracle calls and finds a collision of `H ∘ H` with probability `1`. -/
example (ℓ : ℕ) (H : List Bool → List Bool) (hlen : ∀ m, (H m).length = ℓ) :
    let doubleDigest : List Bool → ProbOracleComp (fun _ : List Bool => List Bool) (List Bool) :=
      fun m => do
        let d ← ProbOracleComp.query m
        ProbOracleComp.query d
    let ms : Fin (2 ^ ℓ + 1) → List Bool := fun i => BitString.lowBits (ℓ + 1) i
    ProbOracleComp.IsQueryBounded (bruteForceFinder doubleDigest ms) ((2 ^ ℓ + 1) * 2) ∧
      (ProbComp.eval ((bruteForceFinder doubleDigest ms).run fun x => pure (H x))).toOuterMeasure
        (collisionOutputs fun m => H (H m)) = 1 := by
  intro doubleDigest ms
  have hle : 2 ^ ℓ + 1 ≤ 2 ^ (ℓ + 1) := by
    rw [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := ℓ)
    omega
  have hinj : Function.Injective ms := fun i j hij =>
    Fin.ext (BitString.lowBits_injective_of_lt (i.isLt.trans_le hle) (j.isLt.trans_le hle) hij)
  refine ⟨isQueryBounded_bruteForceFinder fun i =>
      (ProbOracleComp.IsQueryBounded.query (ms i)).bind (m := 1) fun d =>
        ProbOracleComp.IsQueryBounded.query d,
    bruteForceFinder_two_pow_succ_success H (fun m => H (H m)) hinj ?_ fun _ => hlen _⟩
  intro i
  simp only [doubleDigest, ProbOracleComp.run_bind, ProbOracleComp.run_query, pure_bind]

/-! ## Edge case `ℓ = 0` and Boneh–Shoup's `ℓ = 16` example (`2 ^ 16 + 1 = 65537`) -/

/-- Edge case `ℓ = 0`: `bruteForceHashFinder 0` makes at most `2 ^ 0 + 1 = 2` hash evaluations and
finds a collision with probability `1` for every `0`-bit hash on `1`-bit words. -/
example (H : List Bool → List Bool) (hlen : ∀ m, m.length = 1 → (H m).length = 0) :
    ProbOracleComp.IsQueryBounded (bruteForceHashFinder 0) 2 ∧
      (ProbComp.eval ((bruteForceHashFinder 0).run fun m => pure (H m))).toOuterMeasure
        (collisionOutputs H) = 1 :=
  ⟨isQueryBounded_bruteForceHashFinder 0, bruteForceHashFinder_success 0 H hlen⟩

/-- Concrete `ℓ = 0` run: the unique `0`-bit digest `[]` collides on `[false]` and `[true]`. -/
example :
    collidingPair? (fun i : Fin (2 ^ 0 + 1) => BitString.lowBits 1 i)
      (fun _ : Fin (2 ^ 0 + 1) => ([] : List Bool)) =
        some ([false], [true], []) := by decide

/-- **[BonehShoup2023], §8.3, printed p. 294**: for `16`-bit digests, `bruteForceHashFinder 16`
uses at most `2 ^ 16 + 1 = 65537` hash evaluations and finds a collision with probability `1` for
every hash `H : List Bool → List Bool` outputting `16`-bit digests. -/
example (H : List Bool → List Bool) (hlen : ∀ m, (H m).length = 16) :
    ProbOracleComp.IsQueryBounded (bruteForceHashFinder 16) 65537 ∧
      (ProbComp.eval ((bruteForceHashFinder 16).run fun m => pure (H m))).toOuterMeasure
        (collisionOutputs H) = 1 :=
  ⟨isQueryBounded_bruteForceHashFinder 16, bruteForceHashFinder_success 16 H fun m _ => hlen m⟩

end CslibFrontierTests.BruteForceCollision
