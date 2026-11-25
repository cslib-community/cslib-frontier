/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Partition
public import CslibFrontier.Computability.Communication.Protocol
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Communication.Announce

/-!
# Monochromatic tilings give protocols: the Aho–Ullman–Yannakakis bound

If the matrix of `f : X → Y → Z` is partitioned into `t` monochromatic rectangles, then `f` has a
deterministic protocol with `O(log² t)` bits. Hence `C(f) = O(log² χ(f))`, where `χ(f)` is the
minimum size of a monochromatic tiling ([AroraBarak07], Chapter 12, Exercise 7, attributed there
to Aho, Ullman and Yannakakis).

The players search for the piece of the partition that contains their input pair. They keep a set
`S` of candidate pieces that still contains it. Two distinct pieces of a partition cannot share
both a row and a column, so the piece `k` containing the input meets at most `|S| + 1` members
of `S` in rows and in columns together (itself counted twice). Hence `k` meets at most `⌈|S| / 2⌉`
members of `S` in rows, or at most `⌈|S| / 2⌉` in columns. In each phase Alice announces a piece
containing her row with this property, if there is one, and otherwise Bob announces one
containing his column. The candidates shrink to the pieces sharing a row (or a column) with the
announced one, which still contain `k`. After `⌈log₂ t⌉` phases one candidate is left and
its label is the output. Each phase costs two announcements of a piece or "none", that is
`2 ⌈log₂ (t + 1)⌉` bits.

## Main results

* `Cslib.Communication.RectanglePartition.ecomplexityFun_run_le`: a tiling with `t` pieces gives
  a protocol with at most `2 ⌈log₂ t⌉ ⌈log₂ (t + 1)⌉` bits.
* `Cslib.Communication.ecomplexityFun_le_eight_mul_log_tilingNumber_sq`:
  `C(f) ≤ 8 ⌊log₂ χ(f)⌋²` for finite input types.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Chapter 12, Exercise 7 (printed p. 232 / PDF p. 248).
-/

public section

namespace Cslib.Communication

namespace RectanglePartition

open Finset

variable {X Y Z : Type*} (p : RectanglePartition X Y Z)

open Classical in
/-- The candidate pieces in `S` sharing a row with piece `i`. -/
private noncomputable def rowMeets (S : Finset (Fin p.size)) (i : Fin p.size) :
    Finset (Fin p.size) :=
  S.filter fun j => (p.alice i ∩ p.alice j).Nonempty

open Classical in
/-- The candidate pieces in `S` sharing a column with piece `i`. -/
private noncomputable def colMeets (S : Finset (Fin p.size)) (i : Fin p.size) :
    Finset (Fin p.size) :=
  S.filter fun j => (p.bob i ∩ p.bob j).Nonempty

/-- A piece sharing a row and a column with the piece `k` is `k`. -/
private theorem eq_of_mem_rowMeets_colMeets {S : Finset (Fin p.size)} {k j : Fin p.size}
    (hr : j ∈ p.rowMeets S k) (hc : j ∈ p.colMeets S k) : j = k := by
  classical
  simp only [rowMeets, colMeets, mem_filter] at hr hc
  obtain ⟨x, hxk, hxj⟩ := hr.2
  obtain ⟨y, hyk, hyj⟩ := hc.2
  exact (p.partition x y).unique ⟨hxj, hyj⟩ ⟨hxk, hyk⟩

/-- The piece `k` meets at most `|S| + 1` candidates in rows and columns together. -/
private theorem card_rowMeets_add_card_colMeets_le {S : Finset (Fin p.size)} (k : Fin p.size) :
    #(p.rowMeets S k) + #(p.colMeets S k) ≤ #S + 1 := by
  classical
  have hinter : p.rowMeets S k ∩ p.colMeets S k ⊆ {k} := fun _ hj =>
    mem_singleton.mpr (p.eq_of_mem_rowMeets_colMeets (mem_inter.mp hj).1 (mem_inter.mp hj).2)
  have hunion : p.rowMeets S k ∪ p.colMeets S k ⊆ S :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have := card_union_add_card_inter (p.rowMeets S k) (p.colMeets S k)
  have := card_le_card hinter
  have := card_le_card hunion
  rw [card_singleton] at *
  omega

/-- Without communication: a set of at most one candidate fixes the output. -/
private theorem exists_protocol_of_card_le_one [Nonempty Z] {S : Finset (Fin p.size)}
    (hS : #S ≤ 1) : ∃ q : Protocol X Y Z, q.depth = 0 ∧
      ∀ x y, p.part x y ∈ S → q.run x y = p.run x y := by
  classical
  refine ⟨.output (if h : S.Nonempty then p.output h.choose else Classical.arbitrary Z),
    rfl, fun x y hk => ?_⟩
  have hne : S.Nonempty := ⟨_, hk⟩
  rw [Protocol.run_output, dite_eq_left hne, run_eq_output_part,
    card_le_one.mp hS _ hne.choose_spec _ hk]

/-- `r` phases of the halving protocol, each of `2 ⌈log₂ (t + 1)⌉` bits, find the piece
containing the input among at most `2 ^ r` candidates. -/
private theorem exists_protocol_of_card_le_two_pow [Nonempty Z] (r : ℕ) (S : Finset (Fin p.size)) :
    ∃ q : Protocol X Y Z, q.depth ≤ r * (2 * Nat.clog 2 (p.size + 1)) ∧
      (#S ≤ 2 ^ r → ∀ x y, p.part x y ∈ S → q.run x y = p.run x y) := by
  classical
  induction r generalizing S with
  | zero =>
    by_cases hS : #S ≤ 1
    · obtain ⟨q, hq, hrun⟩ := p.exists_protocol_of_card_le_one hS
      exact ⟨q, by omega, fun _ => hrun⟩
    · exact ⟨.output (Classical.arbitrary Z), by simp, fun h => absurd (by simpa using h) hS⟩
  | succ r ih =>
    choose! next hnext hnext_run using ih
    -- A piece is a good announcement for Alice (rows) or Bob (columns).
    let goodA (x : X) (i : Fin p.size) : Prop :=
      i ∈ S ∧ x ∈ p.alice i ∧ 2 * #(p.rowMeets S i) ≤ #S + 1
    let goodB (y : Y) (i : Fin p.size) : Prop :=
      i ∈ S ∧ y ∈ p.bob i ∧ 2 * #(p.colMeets S i) ≤ #S + 1
    let choiceA (x : X) : Option (Fin p.size) :=
      if h : ∃ i, goodA x i then some h.choose else none
    let choiceB (y : Y) : Option (Fin p.size) :=
      if h : ∃ i, goodB y i then some h.choose else none
    have hcard : Fintype.card (Option (Fin p.size)) = p.size + 1 := by simp
    obtain ⟨qa, hqa, hqa_run⟩ := Protocol.exists_run_eq_left (Y := Y) choiceA
    obtain ⟨qb, hqb, hqb_run⟩ := Protocol.exists_run_eq_right (X := X) choiceB
    rw [hcard] at hqa hqb
    let afterB : Option (Fin p.size) → Protocol X Y Z
      | some j => next (p.colMeets S j)
      | none => .output (Classical.arbitrary Z)
    let afterA : Option (Fin p.size) → Protocol X Y Z
      | some i => next (p.rowMeets S i)
      | none => qb.bind afterB
    refine ⟨qa.bind afterA, ?_, fun hS x y hk => ?_⟩
    · set c := Nat.clog 2 (p.size + 1)
      have hB : ∀ o, (afterB o).depth ≤ r * (2 * c) := by
        rintro (_ | j)
        · simp [afterB]
        · exact hnext _
      have hA : ∀ o, (afterA o).depth ≤ c + r * (2 * c) := by
        rintro (_ | i)
        · exact (Protocol.depth_bind_le hB).trans (by omega)
        · exact (hnext _).trans (by omega)
      have hmul : (r + 1) * (2 * c) = r * (2 * c) + 2 * c := by ring
      refine (Protocol.depth_bind_le hA).trans ?_
      omega
    -- A good announcement keeps the containing piece and halves the candidates.
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
    set k := p.part x y
    obtain ⟨hxk, hyk⟩ := p.part_mem x y
    rw [Protocol.run_bind, hqa_run]
    by_cases hA : ∃ i, goodA x i
    · have hi := hA.choose_spec
      simp only [choiceA, dite_eq_left hA, afterA]
      refine hnext_run _ (by omega) x y ?_
      simp only [rowMeets, mem_filter]
      exact ⟨hk, x, hi.2.1, hxk⟩
    by_cases hB : ∃ j, goodB y j
    · have hj := hB.choose_spec
      simp only [choiceA, dite_eq_right hA, afterA, Protocol.run_bind, hqb_run, choiceB,
        dite_eq_left hB, afterB]
      refine hnext_run _ (by omega) x y ?_
      simp only [colMeets, mem_filter]
      exact ⟨hk, y, hj.2.1, hyk⟩
    · have hsum := p.card_rowMeets_add_card_colMeets_le (S := S) k
      have hA' : ¬ 2 * #(p.rowMeets S k) ≤ #S + 1 := fun h => hA ⟨k, hk, hxk, h⟩
      have hB' : ¬ 2 * #(p.colMeets S k) ≤ #S + 1 := fun h => hB ⟨k, hk, hyk, h⟩
      omega

/-- **Aho–Ullman–Yannakakis, explicit form.** The function computed by a rectangle partition with
`t` pieces has a deterministic protocol with at most `2 ⌈log₂ t⌉ ⌈log₂ (t + 1)⌉` bits: in each of
`⌈log₂ t⌉` phases, Alice or Bob names a piece that shares a row or a column with at most
`⌈|S| / 2⌉` of the `|S|` remaining candidates, and these candidates still include the piece
containing the input. The output type must be
nonempty, since there is no protocol at all with an empty output type. -/
theorem ecomplexityFun_run_le [Nonempty Z] :
    Protocol.ecomplexityFun p.run ≤
      (2 * Nat.clog 2 p.size * Nat.clog 2 (p.size + 1) : ℕ) := by
  obtain ⟨q, hq, hrun⟩ := p.exists_protocol_of_card_le_two_pow (Nat.clog 2 p.size) univ
  refine Protocol.ecomplexityFun_le_iff.mpr ⟨q, funext₂ fun x y => ?_, ?_⟩
  · exact hrun (by simpa using Nat.le_pow_clog one_lt_two _) x y (mem_univ _)
  · exact hq.trans_eq (by ring)

end RectanglePartition

/-- **Aho–Ullman–Yannakakis** ([AroraBarak07], Chapter 12, Exercise 7): `C(f) = O(log² χ(f))`.
For finite input types, every `f` with nonempty output type satisfies
`C(f) ≤ 8 ⌊log₂ χ(f)⌋²`, where `χ(f)` is the minimum size of a monochromatic tiling
(`tilingNumber`, finite here) and `C(f)` is deterministic communication complexity. The draft
states it for Boolean `f` on `{0,1}ⁿ × {0,1}ⁿ`. -/
theorem ecomplexityFun_le_eight_mul_log_tilingNumber_sq {X Y Z : Type*} [Finite X] [Finite Y]
    [Nonempty Z] (f : X → Y → Z) :
    Protocol.ecomplexityFun f ≤ (8 * Nat.log 2 (tilingNumber f).toNat ^ 2 : ℕ) := by
  obtain ⟨p, rfl, hp⟩ := exists_minimal_tiling f
  rw [← hp, ENat.toNat_natCast]
  refine p.ecomplexityFun_run_le.trans (Nat.cast_le.mpr ?_)
  set t := p.size
  rcases Nat.lt_or_ge t 2 with ht | ht
  · simp [Nat.clog_of_right_le_one (by omega : t ≤ 1)]
  have hL : 1 ≤ Nat.log 2 t := Nat.log_pos one_lt_two ht
  have hlt := Nat.lt_pow_succ_log_self one_lt_two t
  have h1 : Nat.clog 2 (t + 1) ≤ Nat.log 2 t + 1 := Nat.clog_le_of_le_pow hlt
  have h0 : Nat.clog 2 t ≤ Nat.log 2 t + 1 := Nat.clog_le_of_le_pow hlt.le
  calc 2 * Nat.clog 2 t * Nat.clog 2 (t + 1)
      ≤ 2 * (Nat.log 2 t + 1) * (Nat.log 2 t + 1) := by gcongr
    _ ≤ 2 * (2 * Nat.log 2 t) * (2 * Nat.log 2 t) := by gcongr <;> omega
    _ = 8 * Nat.log 2 t ^ 2 := by ring

end Cslib.Communication
