/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.OneHole
import CslibFrontier.Foundations.Data.List.Extract

/-! # Hole derivations

A hole derivation builds a sequence of transitions from three kinds of blocks, keeping track of
the open holes as chains of pending pushes: a well-nested block, a new hole made of atomic hole
segments `↓ws ↓ws ⋯` of one stack (each a push followed by a well-nested sequence), and a pop that
matches the newest push of the last open hole of its stack. These are the steps of the search of
Algorithm 1 of [AkshayGastinKrishnaRoychowdhury2020] (`AddHole`, `AddPop` and the well-nested
continuations through `WR`).

Every sequence built with at most `K` open holes is `K`-hole-bounded
(`MPDA.HoleDerivation.holeBounded`): at each position, the first pending pushes of open holes in
the sense of Definition 1 map injectively to the open chains.

## Main definitions

- `MPDA.HoleBlock`: a block of atomic hole segments of one stack.
- `MPDA.HoleDerivation`: hole derivations with at most `K` open chains.

## Main results

- `MPDA.HoleDerivation.holeBounded`: sequences built by hole derivations are `K`-hole-bounded.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α : Type*}

/-! ## Pending pushes -/

section Pending

variable {w v : List (α × Op n Γ)} {p q x y : ℕ}

/-- Whether a push is pending at a position only depends on the sequence up to that position. -/
theorem pendingAt_append_iff (hx : x < w.length) : PendingAt (w ++ v) p x ↔ PendingAt w p x := by
  unfold PendingAt
  have hext : (w ++ v).extract (p + 1) (x + 1) = w.extract (p + 1) (x + 1) :=
    List.extract_append_right _ _ (by omega)
  constructor
  · rintro ⟨hpx, -, i, ⟨a, γ, hp⟩, hk⟩
    refine ⟨hpx, hx, i, ⟨a, γ, ?_⟩, fun k => hext ▸ hk k⟩
    rwa [List.getElem?_append_left (by omega)] at hp
  · rintro ⟨hpx, -, i, ⟨a, γ, hp⟩, hk⟩
    refine ⟨hpx, by simp; omega, i, ⟨a, γ, ?_⟩, fun k => hext.symm ▸ hk k⟩
    rwa [List.getElem?_append_left (by omega)]

/-- A push pending at a position is pending at every earlier position from the push on. -/
theorem PendingAt.anti (h : PendingAt w p x) (hpy : p ≤ y) (hyx : y ≤ x) : PendingAt w p y := by
  obtain ⟨hpx, hx, i, hp, hk⟩ := h
  refine ⟨hpy, by omega, i, hp, fun k => ?_⟩
  rw [← w.take_extract (show p + 1 ≤ y + 1 by omega) (show y + 1 ≤ x + 1 by omega),
    List.take_take]
  exact hk _

/-- A push pending at `x` stays pending at `y ≥ x` if no prefix of the factor after `x` pops below
its initial height on any stack. -/
theorem PendingAt.extend (h : PendingAt w p x) (hxy : x ≤ y) (hy : y < w.length)
    (hk : ∀ (i : Fin n) k, 0 ≤ net i ((w.extract (x + 1) (y + 1)).take k)) : PendingAt w p y := by
  obtain ⟨hpx, -, i, hp, hk'⟩ := h
  refine ⟨by omega, hy, i, hp, fun k => ?_⟩
  rw [← w.extract_append_extract (show p + 1 ≤ x + 1 by omega) (show x + 1 ≤ y + 1 by omega),
    List.take_append, net_append]
  have h₁ := hk' k
  have h₂ := hk i (k - (w.extract (p + 1) (x + 1)).length)
  by_cases hkl : k ≤ (w.extract (p + 1) (x + 1)).length
  · rw [show k - (w.extract (p + 1) (x + 1)).length = 0 by omega]
    simp only [List.take_zero, net_nil, add_zero]
    exact h₁
  · rw [List.take_of_length_le (by omega)] at h₁ ⊢
    have := hk' (w.extract (p + 1) (x + 1)).length
    rw [List.take_length] at this
    omega

/-- A push matched at `m` is no longer pending from `m` on. -/
theorem not_pendingAt_of_matches {m : ℕ} (h : Matches w q m) (hmx : m ≤ x) :
    ¬PendingAt w q x := by
  obtain ⟨hqm, i, hq, ⟨b, γ, hm⟩, -, hnet⟩ := h
  rintro ⟨-, hx, j, hq', hk⟩
  obtain rfl : j = i := by
    obtain ⟨a, γ', hq⟩ := hq
    obtain ⟨a', γ'', hq'⟩ := hq'
    rw [hq] at hq'
    simp only [Option.some.injEq, Prod.mk.injEq, Op.push.injEq] at hq'
    exact hq'.2.1.symm
  have := hk (m + 1 - (q + 1))
  have hneg := net_neg_of_pop (w := w) (a := q + 1) (m' := x + 1) (by omega) (by omega) hm hnet
  omega

/-- A push inside a well-nested factor is closed by a well-nested continuation inside that
factor. -/
theorem exists_matches_of_wellNested {a b : ℕ} {i : Fin n} (hwn : WellNested (w.extract a b))
    (hb : b ≤ w.length) (haq : a ≤ q) (hqb : q < b) (hq : IsPushOn w i q) :
    ∃ m, Matches w q m ∧ m < b ∧ WellMatched w q := by
  have hsplit : w.take a ++ w.extract a b ++ w.drop b = w := by
    rw [List.extract_eq_take_drop, ← List.take_add, show a + (b - a) = b by omega,
      List.take_append_drop]
  have hpush : IsPushOn (w.extract a b) i (q - a) := by
    obtain ⟨c, γ, hq⟩ := hq
    refine ⟨c, γ, ?_⟩
    rw [List.extract_eq_take_drop, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_cancel' haq, hq]
  obtain ⟨m, hm, hmwn⟩ := hwn.exists_wellMatched hpush
  have hmlen := hm.lt_length
  have hlen : (w.extract a b).length = b - a := by
    rw [List.extract_eq_take_drop, List.length_take, List.length_drop]
    omega
  have hwm := (show WellMatched (w.extract a b) (q - a) from ⟨m, hm, hmwn⟩).append
    (w.take a) (w.drop b)
  rw [hsplit, List.length_take, min_eq_left (by omega), Nat.add_sub_cancel' haq] at hwm
  have hM := (matches_append_left (w.take a) (w.extract a b ++ w.drop b) (q - a) m).mpr
    (hm.append_right _)
  rw [← List.append_assoc, hsplit, List.length_take, min_eq_left (by omega),
    Nat.add_sub_cancel' haq] at hM
  exact ⟨a + m, hM, by omega, hwm⟩

end Pending

/-! ## Chains of pending pushes -/

/-- An open hole as a chain of pushes on one stack: their positions and pushed symbols, newest
first. -/
structure HoleChain (n : ℕ) (Γ : Type*) where
  /-- The stack of the hole. -/
  stack : Fin n
  /-- The positions and symbols of the pushes, newest first. -/
  pushes : List (ℕ × Γ)

/-- Consecutive pushes of a chain are separated by a well-nested factor, newest first. -/
@[expose] def Chained (w : List (α × Op n Γ)) (ps : List (ℕ × Γ)) : Prop :=
  ps.IsChain fun e e' => e'.1 < e.1 ∧ WellNested (w.extract (e'.1 + 1) e.1)

/-- A snapshot of the open holes at position `x` of `w`: at most `K` chains of pending pushes,
consecutive pushes of a chain separated by well-nested factors, and every other push pending at
`x` inside a well-nested factor of `w`. -/
@[expose] def Snapshot (K : ℕ) (w : List (α × Op n Γ)) (x : ℕ) (C : List (HoleChain n Γ)) :
    Prop :=
  C.length ≤ K ∧
  (∀ c ∈ C, ∀ e ∈ c.pushes, (∃ a, w[e.1]? = some (a, .push c.stack e.2)) ∧ PendingAt w e.1 x) ∧
  (∀ c ∈ C, Chained w c.pushes) ∧
  ∀ q, PendingAt w q x → (∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q) ∨
    ∃ a b, a ≤ q ∧ q < b ∧ b ≤ w.length ∧ WellNested (w.extract a b)

section Counting

variable {w : List (α × Op n Γ)} {x : ℕ} {K : ℕ} {C : List (HoleChain n Γ)}

private theorem chained_pairwise {ps : List (ℕ × Γ)} (h : Chained w ps) :
    ps.Pairwise fun e e' => e'.1 < e.1 := by
  have : IsTrans (ℕ × Γ) (fun e e' => e'.1 < e.1) := ⟨fun _ _ _ h h' => h'.trans h⟩
  exact (h.imp fun _ _ h => h.1).pairwise

/-- In a chain, a push older than another one has a direct older neighbour of the newer one, at or
after it, separated from the newer one by a well-nested factor. -/
private theorem exists_older_neighbour {ps : List (ℕ × Γ)} (h : Chained w ps) {e e' : ℕ × Γ}
    (he : e ∈ ps) (he' : e' ∈ ps) (hlt : e.1 < e'.1) :
    ∃ f ∈ ps, e.1 ≤ f.1 ∧ f.1 < e'.1 ∧ WellNested (w.extract (f.1 + 1) e'.1) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp he'
  have hpw := chained_pairwise h
  rw [List.pairwise_append, List.pairwise_cons] at hpw
  -- `e` comes after `e'`.
  have hel₂ : e ∈ l₂ := by
    rcases List.mem_append.mp he with hl | hl
    · have := hpw.2.2 e hl e' List.mem_cons_self
      omega
    · rcases List.mem_cons.mp hl with rfl | hl
      · omega
      · exact hl
  obtain ⟨f, l₃, rfl⟩ : ∃ f l₃, l₂ = f :: l₃ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hel₂)
  have hchain : (e' :: f :: l₃).IsChain fun e e' => e'.1 < e.1 ∧
      WellNested (w.extract (e'.1 + 1) e.1) := (List.IsChain.right_of_append h)
  obtain ⟨hfe', hwn⟩ := (List.isChain_cons_cons.mp hchain).1
  refine ⟨f, by simp, ?_, hfe', hwn⟩
  rcases List.mem_cons.mp hel₂ with rfl | hl
  · exact le_rfl
  · exact ((List.pairwise_cons.mp hpw.2.1.2).1 e hl).le

/-- **Counting holes**: the open holes at `x`, in the sense of Definition 1, are at most the
chains of a snapshot at `x`. -/
theorem Snapshot.openHoles_le (h : Snapshot K w x C) : openHoles w x ≤ C.length := by
  obtain ⟨-, hpend, hchain, hcover⟩ := h
  classical
  set S := {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q}
  -- Each counted push lies in a chain.
  have hin : ∀ q ∈ S, ∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q := by
    rintro q ⟨⟨⟨⟨i, hpush⟩, hnot⟩, hq⟩, -⟩
    rcases hcover q hq with h | ⟨a, b, haq, hqb, hb, hwn⟩
    · exact h
    · obtain ⟨-, -, -, hwm⟩ := exists_matches_of_wellNested hwn hb haq hqb hpush
      exact absurd hwm hnot
  let f : ℕ → ℕ := fun q => C.findIdx fun c => c.pushes.any (·.1 == q)
  have hf : ∀ q ∈ S, ∃ hlt : f q < C.length, ∃ e ∈ (C[f q]'hlt).pushes, e.1 = q := by
    intro q hq
    obtain ⟨c, hc, e, he, rfl⟩ := hin q hq
    have hlt : f e.1 < C.length :=
      List.findIdx_lt_length_of_exists ⟨c, hc, List.any_eq_true.mpr ⟨e, he, by simp⟩⟩
    have := List.findIdx_getElem (w := hlt)
    simp only [List.any_eq_true, beq_iff_eq] at this
    exact ⟨hlt, this⟩
  -- Two counted pushes in the same chain are equal.
  have hinj : Set.InjOn f S := by
    intro q hq q' hq' hqq'
    obtain ⟨hlt, e, he, rfl⟩ := hf q hq
    obtain ⟨hlt', e', he', rfl⟩ := hf q' hq'
    have he2 : e ∈ (C[f e'.1]'hlt').pushes := by simpa only [hqq'] using he
    set c := C[f e'.1]'hlt'
    have hc : c ∈ C := List.getElem_mem _
    replace he := he2
    by_contra hne
    -- Order the two pushes; the newer one is not the first pending push of its hole.
    suffices key : ∀ {e e' : ℕ × Γ}, e ∈ c.pushes → e' ∈ c.pushes → e.1 < e'.1 → e'.1 ∈ S →
        False by
      rcases lt_or_gt_of_ne hne with h | h
      · exact key he he' h hq'
      · exact key he' he h hq
    intro e e' he he' hlt hS
    obtain ⟨⟨⟨⟨i, hpush'⟩, hnot'⟩, hq'x⟩, hfirst⟩ := hS
    obtain ⟨g, hg, heg, hge', hwn⟩ := exists_older_neighbour (hchain c hc) he he' hlt
    obtain ⟨⟨a, hga⟩, hgx⟩ := hpend c hc g hg
    obtain ⟨⟨a', hea'⟩, -⟩ := hpend c hc e' he'
    have hgpush : IsPushOn w c.stack g.1 := ⟨a, g.2, hga⟩
    -- The older neighbour is a hole push: otherwise it would enclose the newer one.
    have hghole : HolePush w g.1 := by
      refine ⟨⟨c.stack, hgpush⟩, fun ⟨m, hm, hmwn⟩ => hnot' ?_⟩
      have hmx : x < m := by
        by_contra hmx
        exact not_pendingAt_of_matches hm (by omega) hgx
      obtain ⟨-, -, -, hwm⟩ := exists_matches_of_wellNested hmwn
        (by have := hm.lt_length; omega) (by omega) (by have := hq'x.1; omega) ⟨a', e'.2, hea'⟩
      exact hwm
    exact hfirst ⟨g.1, hge', ⟨hghole, hgx⟩, ⟨⟨⟨c.stack, ⟨a', e'.2, hea'⟩⟩, hnot'⟩, hq'x⟩,
      ⟨c.stack, hgpush, a', e'.2, hea'⟩, hwn⟩
  calc openHoles w x = S.ncard := rfl
    _ ≤ ((Finset.range C.length : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun q hq => by
          obtain ⟨hlt, -⟩ := hf q hq
          simpa using hlt) hinj (Finset.finite_toSet _)
    _ = C.length := by rw [Set.ncard_coe_finset, Finset.card_range]

end Counting

end Cslib.Automata.MPDA
