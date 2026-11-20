/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.EmptinessSound
import CslibFrontier.Foundations.Data.List.Extract
import Mathlib.Data.List.Forall2

/-! # Completeness of the emptiness procedure

If an MPDA has a `K`-hole-bounded accepting run, the repaired search of Algorithm 1 of
[AkshayGastinKrishnaRoychowdhury2020] (`MPDA.isEmpty`) answers `false`.

The run is cut at its events: the positions after a maximal well-nested factor, where the next
transition is a pop or a push that is not closed by a well-nested continuation (`MPDA.wnEnd`). A
hole push opens a chain, which extends greedily by the least later hole push of the same stack
behind a well-nested factor; the chain is one `AddHole` step. A pop matches the newest push of the
last chain of its stack and is one `AddPop` step. When a chain opens, Definition 1 counts at least
one more open hole than there are open chains, so a `K`-hole-bounded run never needs more than `K`
of them.

## Main results

- `MPDA.isEmpty_eq_false_of_mem_boundedLanguage`: if some word has a `K`-hole-bounded accepting
  run, the search answers `false`.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α : Type*}

/-! ## The next event -/

section Events

variable (w : List (α × Op n Γ))

open Classical in
/-- The end of the longest well-nested factor of `w` starting at `p`. -/
noncomputable def wnEnd (p : ℕ) : ℕ :=
  Nat.findGreatest (fun r => p ≤ r ∧ WellNested (w.extract p r)) w.length

variable {w} {p r : ℕ}

theorem wnEnd_spec (hp : p ≤ w.length) :
    p ≤ wnEnd w p ∧ wnEnd w p ≤ w.length ∧ WellNested (w.extract p (wnEnd w p)) := by
  classical
  have hP : p ≤ p ∧ WellNested (w.extract p p) := ⟨le_rfl, by
    rw [List.extract_eq_take_drop, Nat.sub_self, List.take_zero]
    exact .nil⟩
  have := Nat.findGreatest_spec (P := fun r => p ≤ r ∧ WellNested (w.extract p r)) hp hP
  exact ⟨this.1, Nat.findGreatest_le _, this.2⟩

theorem le_wnEnd (hr : r ≤ w.length) (hpr : p ≤ r) (hwn : WellNested (w.extract p r)) :
    r ≤ wnEnd w p := by
  classical
  exact Nat.le_findGreatest (P := fun r => p ≤ r ∧ WellNested (w.extract p r)) hr ⟨hpr, hwn⟩

/-- After the longest well-nested factor comes an event: not a `nop`, and not a push closed by a
well-nested continuation. -/
theorem wnEnd_event (hp : p ≤ w.length) (hlt : wnEnd w p < w.length) :
    (¬∃ a, w[wnEnd w p]? = some (a, .nop)) ∧ ¬WellMatched w (wnEnd w p) := by
  obtain ⟨hpe, -, hwn⟩ := wnEnd_spec hp
  constructor
  · rintro ⟨a, ha⟩
    have hext : WellNested (w.extract p (wnEnd w p + 1)) := by
      rw [← w.extract_append_extract hpe (Nat.le_succ _), List.extract_eq_singleton ha]
      exact hwn.append (.nop .nil)
    have := le_wnEnd (show wnEnd w p + 1 ≤ w.length by omega) (by omega) hext
    omega
  · rintro ⟨m, hm, hmwn⟩
    have hmlen := hm.lt_length
    have hext : WellNested (w.extract p (m + 1)) := by
      rw [← w.extract_append_extract hpe (show wnEnd w p ≤ m + 1 by have := hm.1; omega)]
      exact hwn.append hmwn
    have := le_wnEnd (show m + 1 ≤ w.length by omega) (by have := hm.1; omega) hext
    have := hm.1
    omega

end Events

/-! ## Greedy chains -/

section Chains

open Classical

variable {w : List (α × Op n Γ)}

/-- A push on stack `i` that is not closed by a well-nested continuation. -/
@[expose] def IsHolePushOn (w : List (α × Op n Γ)) (i : Fin n) (r : ℕ) : Prop :=
  IsPushOn w i r ∧ ¬WellMatched w r

/-- The hole push at `r` extends a chain ending in the push at `q`: same stack, separated by a
well-nested factor. -/
@[expose] def Ext (w : List (α × Op n Γ)) (i : Fin n) (q r : ℕ) : Prop :=
  q < r ∧ IsHolePushOn w i r ∧ WellNested (w.extract (q + 1) r)

theorem IsPushOn.lt_length {i : Fin n} {r : ℕ} (h : IsPushOn w i r) : r < w.length := by
  obtain ⟨a, γ, h⟩ := h
  exact (List.getElem?_eq_some_iff.mp h).1

/-- Only the least extension of a push is an extension: a later one would enclose it in a
well-nested factor. -/
theorem Ext.eq_of_le {i : Fin n} {q r r' : ℕ} (h : Ext w i q r) (h' : Ext w i q r')
    (hle : r ≤ r') : r = r' := by
  by_contra hne
  obtain ⟨hqr, ⟨hpush, hnot⟩, -⟩ := h
  obtain ⟨hqr', ⟨hpush', -⟩, hwn'⟩ := h'
  obtain ⟨-, -, -, hwm⟩ := exists_matches_of_wellNested hwn'
    (by have := hpush'.lt_length; omega) (show q + 1 ≤ r by omega)
    (by omega) hpush
  exact hnot hwm

/-- The greedy chain from position `q`, oldest first: `q`, then the least extension, and so on. -/
noncomputable def chainFrom (w : List (α × Op n Γ)) (i : Fin n) (q : ℕ) : List ℕ :=
  if h : ∃ r, Ext w i q r then q :: chainFrom w i (Nat.find h) else [q]
termination_by w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

theorem chainFrom_eq {i : Fin n} {q : ℕ} : chainFrom w i q =
    if h : ∃ r, Ext w i q r then q :: chainFrom w i (Nat.find h) else [q] := by
  rw [chainFrom]

theorem mem_chainFrom_self {i : Fin n} {q : ℕ} : q ∈ chainFrom w i q := by
  rw [chainFrom_eq]
  split_ifs <;> simp

/-- Every element of the greedy chain after `q` is a hole push of stack `i`, and the elements
increase. -/
theorem chainFrom_spec {i : Fin n} :
    ∀ q, ∀ r ∈ chainFrom w i q, q ≤ r ∧ (r ≠ q → IsHolePushOn w i r)
  | q, r, hr => by
    rw [chainFrom_eq] at hr
    split_ifs at hr with h
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨le_rfl, fun h' => absurd rfl h'⟩
      · have hspec := Nat.find_spec h
        obtain ⟨hle, hhole⟩ := chainFrom_spec (Nat.find h) r hr
        refine ⟨by have := hspec.1; omega, fun _ => ?_⟩
        by_cases hrf : r = Nat.find h
        · rw [hrf]
          exact hspec.2.1
        · exact hhole hrf
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨le_rfl, fun h' => absurd rfl h'⟩
termination_by q => w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

/-- **Greedy chains are closed under extension**: an extension of an element of the chain is in
the chain. -/
theorem mem_chainFrom_of_ext {i : Fin n} : ∀ q, ∀ p ∈ chainFrom w i q, ∀ r, Ext w i p r →
    r ∈ chainFrom w i q
  | q, p, hp, r, hr => by
    rw [chainFrom_eq] at hp ⊢
    split_ifs at hp ⊢ with h
    · rcases List.mem_cons.mp hp with rfl | hp
      · -- The least extension is the only one.
        have hmin := Nat.find_min' h hr
        obtain rfl := (Nat.find_spec h).eq_of_le hr hmin
        exact List.mem_cons_of_mem _ mem_chainFrom_self
      · exact List.mem_cons_of_mem _ (mem_chainFrom_of_ext (Nat.find h) p hp r hr)
    · obtain rfl := List.mem_singleton.mp hp
      exact absurd ⟨r, hr⟩ h
termination_by q => w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

end Chains

/-! ## The counting guard -/

section Guard

variable {w : List (α × Op n Γ)}

theorem pendingAt_self {i : Fin n} {t : ℕ} (h : IsPushOn w i t) : PendingAt w t t :=
  ⟨le_rfl, h.lt_length, i, h, fun k => by
    rw [List.extract_eq_take_drop, Nat.sub_self, List.take_zero, List.take_nil]
    simp⟩

theorem IsPushOn.stack_eq {i j : Fin n} {t : ℕ} (hi : IsPushOn w i t) (hj : IsPushOn w j t) :
    i = j := by
  obtain ⟨a, γ, ha⟩ := hi
  obtain ⟨b, δ, hb⟩ := hj
  rw [ha] at hb
  simp only [Option.some.injEq, Prod.mk.injEq, Op.push.injEq] at hb
  exact hb.2.1

/-- Pushes of different chains are at different positions. -/
theorem chains_ne {C : List (HoleChain n Γ)}
    (horder : C.Pairwise fun c c' => ∀ e ∈ c.pushes, ∀ e' ∈ c'.pushes, e.1 < e'.1)
    {c c' : HoleChain n Γ} (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c') :
    ∀ e ∈ c.pushes, ∀ e' ∈ c'.pushes, e.1 ≠ e'.1 := by
  induction C with
  | nil => simp at hc
  | cons d C ih =>
    rw [List.pairwise_cons] at horder
    rcases List.mem_cons.mp hc with rfl | hc₁ <;> rcases List.mem_cons.mp hc' with rfl | hc₁'
    · exact absurd rfl hne
    · exact fun e he e' he' => (horder.1 c' hc₁' e he e' he').ne
    · exact fun e he e' he' => (horder.1 c hc₁ e' he' e he).ne'
    · exact ih horder.2 hc₁ hc₁'

/-- **The counting guard**: a new hole push at `t` comes with at least one more open hole, in the
sense of Definition 1, than there are open chains. -/
theorem card_add_one_le_openHoles {C : List (HoleChain n Γ)} {t : ℕ} {i : Fin n}
    (ht : IsHolePushOn w i t)
    (hne : ∀ c ∈ C, c.pushes ≠ [])
    (helem : ∀ c ∈ C, ∀ e ∈ c.pushes,
      IsHolePushOn w c.stack e.1 ∧ PendingAt w e.1 t ∧ e.1 < t)
    (hcover : ∀ q < t, PendingAt w q t → ∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q)
    (horder : C.Pairwise fun c c' => ∀ e ∈ c.pushes, ∀ e' ∈ c'.pushes, e.1 < e'.1)
    (hchain : ∀ c ∈ C, c.pushes.Pairwise fun e e' => e'.1 < e.1)
    (hclosed : ∀ c ∈ C, ∀ e ∈ c.pushes, ∀ r, Ext w c.stack e.1 r →
      r < t ∧ (PendingAt w r t → ∃ e' ∈ c.pushes, e'.1 = r)) :
    C.length + 1 ≤ openHoles w t := by
  classical
  -- The oldest push of each chain.
  let old : HoleChain n Γ → ℕ := fun c => (c.pushes.getLast?.map Prod.fst).getD 0
  have hold : ∀ c ∈ C, ∃ e ∈ c.pushes, e.1 = old c ∧ ∀ e' ∈ c.pushes, e.1 ≤ e'.1 := by
    intro c hc
    obtain ⟨e, he⟩ := List.getLast?_isSome.mpr (hne c hc) |> Option.isSome_iff_exists.mp
    refine ⟨e, List.mem_of_getLast? he, by simp [old, he], fun e' he' => ?_⟩
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp he
    have hpw := hchain c hc
    rw [hl] at he' hpw
    rcases List.mem_append.mp he' with he' | he'
    · exact ((List.pairwise_append.mp hpw).2.2 e' he' e (by simp)).le
    · simp at he'
      rw [he']
  -- If two pending pushes are joined like one hole, they lie in the same chain, the older first.
  have hsame : ∀ p q, p < q → q < t → PendingAt w p t → PendingAt w q t →
      (∃ j, IsPushOn w j p ∧ IsPushOn w j q) → (∃ j, IsHolePushOn w j q) →
      WellNested (w.extract (p + 1) q) →
      ∃ c ∈ C, (∃ e ∈ c.pushes, e.1 = p) ∧ ∃ e ∈ c.pushes, e.1 = q := by
    intro p q hpq hqt hp hq ⟨j, hpj, hqj⟩ ⟨j', hqhole⟩ hwn
    obtain ⟨c, hc, e, he, rfl⟩ := hcover p (by omega) hp
    have hjc : c.stack = j := (helem c hc e he).1.1.stack_eq hpj
    have hext : Ext w c.stack e.1 q := ⟨hpq, by
      rw [hjc, hqj.stack_eq hqhole.1]
      exact hqhole, hwn⟩
    exact ⟨c, hc, ⟨e, he, rfl⟩, (hclosed c hc e he q hext).2 hq⟩
  -- The counted pushes.
  set S := {q | OpenHolePush w t q ∧ ¬∃ p, SameHole w t p q}
  have hT : ((insert t ((C.map old).toFinset) : Finset ℕ) : Set ℕ) ⊆ S := by
    intro q hq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, List.mem_toFinset,
      List.mem_map] at hq
    rcases hq with hq | ⟨c, hc, rfl⟩
    · rw [hq]
      refine ⟨⟨⟨⟨i, ht.1⟩, ht.2⟩, pendingAt_self ht.1⟩, ?_⟩
      rintro ⟨p, hpt, ⟨-, hp⟩, -, hstk, hwn⟩
      obtain ⟨c, hc, e, he, rfl⟩ := hcover p hpt hp
      obtain ⟨j, hpj, htj⟩ := hstk
      have hjc : c.stack = j := (helem c hc e he).1.1.stack_eq hpj
      have hext : Ext w c.stack e.1 t := ⟨hpt, by rw [hjc, htj.stack_eq ht.1]; exact ht, hwn⟩
      exact absurd (hclosed c hc e he t hext).1 (lt_irrefl _)
    · obtain ⟨e, he, hev, hmin⟩ := hold c hc
      obtain ⟨hhole, hpend, het⟩ := helem c hc e he
      rw [← hev]
      refine ⟨⟨⟨⟨c.stack, hhole.1⟩, hhole.2⟩, hpend⟩, ?_⟩
      rintro ⟨p, hpe, ⟨-, hp⟩, -, hstk, hwn⟩
      obtain ⟨c', hc', ⟨f, hf, rfl⟩, ⟨g, hg, hge⟩⟩ :=
        hsame p e.1 hpe het hp hpend hstk ⟨c.stack, hhole⟩ hwn
      -- `e` lies in `c'`, so `c' = c` by the order of chains, and `f` is older than `e`.
      have hcc : c' = c := by
        by_contra hcc
        exact chains_ne horder hc hc' (Ne.symm hcc) e he g hg hge.symm
      subst hcc
      have := hmin f hf
      omega
  have hfin : S.Finite := (Set.finite_le_nat t).subset fun q hq => hq.1.2.1
  have hcard : (insert t ((C.map old).toFinset)).card = C.length + 1 := by
    rw [Finset.card_insert_of_notMem, List.toFinset_card_of_nodup]
    · simp
    · -- The oldest pushes of distinct chains differ.
      rw [List.nodup_map_iff_inj_on]
      · intro c hc c' hc' hcc'
        by_contra hne'
        obtain ⟨e, he, hev, -⟩ := hold c hc
        obtain ⟨e', he', hev', -⟩ := hold c' hc'
        exact chains_ne horder hc hc' hne' e he e' he' (by omega)
      · exact horder.imp_of_mem fun hc _ h heq => by
          subst heq
          obtain ⟨e, he, -, -⟩ := hold _ hc
          exact lt_irrefl _ (h e he e he)
    · simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
      intro c hc hct
      obtain ⟨e, he, hev, -⟩ := hold c hc
      have := (helem c hc e he).2.2
      omega
  calc C.length + 1 = (insert t ((C.map old).toFinset)).card := hcard.symm
    _ = ((insert t ((C.map old).toFinset) : Finset ℕ) : Set ℕ).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hT hfin

end Guard

end Cslib.Automata.MPDA
