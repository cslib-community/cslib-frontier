/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Nondeterministic.Functions
public import CslibFrontier.Computability.Streaming.Distinctness
public import CslibFrontier.Computability.Streaming.MultiPass
public import CslibFrontier.Computability.Streaming.Nondeterministic

/-!
# Unit tests for multi-pass and nondeterministic streaming algorithms

Verifies non-vacuity and concrete behavior of:
1. the multi-pass model: a two-pass counter, and one pass of a one-pass algorithm;
2. `Cslib.Streaming.MultiPass.ecomplexityFun_le_of_spaceLE`: a deterministic `p`-pass algorithm
   deciding whether at most $2n$ items of `Fin n` are distinct needs $n \le (2p-1)b$, the
   multi-pass form of `Cslib.Streaming.Algorithm.le_of_run_eq_decide_nodup`;
3. `Cslib.Streaming.Nondeterministic.Algorithm.ecomplexityFun_le_of_spaceLE`: so does a
   nondeterministic one, from $N^1(\mathrm{DISJ}_n) = n$, with no extra bit; and an algorithm
   with one memory state has a `1`-cover by one rectangle.
-/

public section

namespace CslibFrontierTests.StreamingMultiPass

open Cslib Cslib.Communication Cslib.Streaming

/-! ## 1. The multi-pass model -/

/-- Counts the items in every pass. -/
def counter : MultiPass ℕ (Fin 3) ℕ where
  init := 0
  update q _ := q + 1
  output := id
  endPass := id

example : counter.run 2 [0, 1, 2] = 6 := by decide

example : counter.run 0 [0, 1, 2] = 0 := by decide

/-- The one-pass counter. -/
def counter₁ : Algorithm ℕ (Fin 3) ℕ where
  init := 0
  update q _ := q + 1
  output := id

example : counter₁.toMultiPass.run 1 [0, 1, 2] = counter₁.run [0, 1, 2] := by simp

/-! ## 2. Deterministic multi-pass distinctness -/

/-- A deterministic `p`-pass algorithm deciding whether at most $2n$ items of `Fin n` are
distinct, with `b` bits of memory, has $n \le (2p-1)b$. -/
theorem le_of_run_eq_decide_nodup {σ : Type*} {n p b : ℕ} (hp : 0 < p)
    (A : MultiPass σ (Fin n) Bool)
    (hA : ∀ s : List (Fin n), s.length ≤ 2 * n → A.run p s = decide s.Nodup)
    (hspace : A.SpaceLE p (2 * n) b) : n ≤ (2 * p - 1) * b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hlen : ∀ x y : BitString n,
      (BitString.positions x ++ BitString.positions y).length ≤ 2 * n := fun x y => by
    rw [List.length_append]
    have := BitString.length_positions_le x
    have := BitString.length_positions_le y
    omega
  have h := A.ecomplexityFun_le_of_spaceLE hp hspace BitString.positions BitString.positions hlen
    id disjointness fun x y => by
      rw [id, hA _ (hlen x y), Bool.eq_iff_iff, decide_eq_true_iff, nodup_positions_append]
  unfold Protocol.ecomplexityFun at h
  rw [ecomplexity_disjointness hn] at h
  have : n + 1 ≤ (2 * p - 1) * b + 1 := by exact_mod_cast h
  omega

/-! ## 3. Nondeterministic multi-pass algorithms -/

/-- A nondeterministic `p`-pass algorithm that accepts exactly the streams of at most `2 n`
distinct items of `Fin n`, with `b` bits of memory, has $n \le (2p-1)b$. -/
theorem le_of_answers_nodup {σ : Type*} {n p b : ℕ} (hp : 0 < p)
    (A : Nondeterministic.Algorithm σ (Fin n) Bool)
    (hA : ∀ s : List (Fin n), s.length ≤ 2 * n → (s.Nodup ↔ true ∈ A.answers p s))
    (hspace : A.SpaceLE p (2 * n) b) : n ≤ (2 * p - 1) * b := by
  have hlen : ∀ x y : BitString n,
      (BitString.positions x ++ BitString.positions y).length ≤ 2 * n := fun x y => by
    rw [List.length_append]
    have := BitString.length_positions_le x
    have := BitString.length_positions_le y
    omega
  have h := A.ecomplexityFun_le_of_spaceLE hp hspace BitString.positions BitString.positions hlen
    id true disjointness fun x y => by
      simp only [id, exists_eq_right, ← hA _ (hlen x y), nodup_positions_append]
  rw [Nondeterministic.ecomplexityFun_disjointness] at h
  exact_mod_cast h

/-- The nondeterministic algorithm with one memory state, which accepts everything. -/
def acceptAll : Nondeterministic.Algorithm Unit (Fin 3) Bool where
  init := ()
  update _ _ := Set.univ
  endPass _ := Set.univ
  output _ := true

/-- It uses no memory, so the constant function `true` has a `1`-cover by one rectangle. -/
example : Nondeterministic.ecomplexityFun true (fun (_ _ : Unit) => true) Set.univ Set.univ ≤
    ((2 * 1 - 1) * 0 : ℕ) := by
  refine acceptAll.ecomplexityFun_le_of_spaceLE (m := 0) one_pos
    ⟨fun _ => Fin.elim0, fun _ _ _ _ _ => rfl⟩ (fun _ => []) (fun _ => []) (fun _ _ => le_rfl) id
    true _ fun _ _ => ?_
  simp only [id, true_iff]
  exact ⟨true, ⟨(), acceptAll.mem_passes_succ.2 ⟨(), rfl, acceptAll.mem_pass.2 ⟨(), rfl, trivial⟩⟩,
    rfl⟩, rfl⟩

end CslibFrontierTests.StreamingMultiPass
