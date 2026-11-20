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

/-! ## Helper lemmas -/

section Helpers

theorem splitLastHole_eq_none {State : Type*} {i : Fin n} :
    ∀ {l : List (HoleTriple n State)}, (∀ h ∈ l, h.1 ≠ i) → splitLastHole i l = none
  | [], _ => rfl
  | h :: t, hl => by
    unfold splitLastHole
    rw [splitLastHole_eq_none fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')]
    simp [hl h List.mem_cons_self]

/-- The converse of `splitLastHole_eq_some`. -/
theorem splitLastHole_eq_some_of {State : Type*} {i : Fin n} {post : List (HoleTriple n State)}
    {x : State × State} (hpost : ∀ h ∈ post, h.1 ≠ i) :
    ∀ pre : List (HoleTriple n State), splitLastHole i (pre ++ (i, x) :: post) = some (pre, x, post)
  | [] => by
    simp only [List.nil_append]
    unfold splitLastHole
    rw [splitLastHole_eq_none hpost]
    simp
  | h :: pre => by
    simp only [List.cons_append]
    unfold splitLastHole
    rw [splitLastHole_eq_some_of hpost pre]

/-- The top of a stack holding open chains is the newest push of the last chain of that stack. -/
theorem stacksOf_eq_cons {C : List (HoleChain n Γ)} (hne : ∀ c ∈ C, c.pushes ≠ []) {i : Fin n}
    {γ : Γ} {rest : List Γ} (h : stacksOf C i = γ :: rest) :
    ∃ pre post p ps, C = pre ++ ⟨i, (p, γ) :: ps⟩ :: post ∧ ∀ d ∈ post, d.stack ≠ i := by
  induction C using List.reverseRecOn generalizing rest with
  | nil => simp [stacksOf] at h
  | append_singleton C d ih =>
    rw [stacksOf_append_singleton] at h
    by_cases hd : d.stack = i
    · subst hd
      rw [Function.update_self] at h
      obtain ⟨⟨p, γ'⟩, ps, hps⟩ := List.exists_cons_of_ne_nil (hne d (by simp))
      rw [hps] at h
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨C, [], p, ps, ?_, by simp⟩
      obtain ⟨stk, pushes⟩ := d
      simp only at hps ⊢
      rw [hps]
    · rw [Function.update_of_ne (Ne.symm hd)] at h
      obtain ⟨pre, post, p, ps, rfl, hpost⟩ :=
        ih (fun c hc => hne c (by simp [hc])) h
      refine ⟨pre, post ++ [d], p, ps, by simp, fun d' hd' => ?_⟩
      rcases List.mem_append.mp hd' with hd' | hd'
      · exact hpost d' hd'
      · obtain rfl := List.mem_singleton.mp hd'
        exact hd

/-- Prepend an atomic hole segment to a hole block. -/
theorem HoleBlock.prepend {i : Fin n} {L : ℕ} {v ws : List (α × Op n Γ)} {ps : List (ℕ × Γ)}
    {a : α} {γ : Γ} (hb : HoleBlock i (L + 1 + ws.length) v ps) (hws : WellNested ws) :
    HoleBlock i L ((a, .push i γ) :: ws ++ v) (ps ++ [(L, γ)]) := by
  induction hb with
  | nil => simpa using HoleBlock.snoc (v := []) (L := L) (a := a) (γ := γ) .nil hws
  | @snoc v ws' ps' a' γ' _ hws' ih =>
    have := HoleBlock.snoc (a := a') (γ := γ') ih hws'
    have e₁ : (a, Op.push i γ) :: ws ++ (v ++ (a', Op.push i γ') :: ws') =
        (a, Op.push i γ) :: ws ++ v ++ (a', Op.push i γ') :: ws' := by simp
    have e₂ : (L + 1 + ws.length + v.length, γ') :: ps' ++ [(L, γ)] =
        (L + ((a, Op.push i γ) :: ws ++ v).length, γ') :: (ps' ++ [(L, γ)]) := by
      simp only [List.cons_append, List.length_cons, List.length_append, List.cons.injEq,
        Prod.mk.injEq, and_true]
      omega
    rw [e₁, e₂]
    exact this

end Helpers

/-! ## Blocks of greedy chains along a run -/

section Block

open Classical

/-- The end of the hole block of the greedy chain from `q`: after its last push, the longest
well-nested factor. -/
noncomputable def blockEnd (w : List (α × Op n Γ)) (i : Fin n) (q : ℕ) : ℕ :=
  if h : ∃ r, Ext w i q r then blockEnd w i (Nat.find h) else wnEnd w (q + 1)
termination_by w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

variable {State Symbol : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]

/-- Prepend an atomic hole segment to a realization. -/
theorem Realizes.prepend {i : Fin n} {s s₁ t : State} {γ : Γ} {r : List (Γ × State)}
    (hγ : (s, γ, s₁) ∈ M.atomicHoles i) (hr : M.Realizes i s₁ t r) :
    M.Realizes i s t (r ++ [(γ, s₁)]) := by
  induction hr with
  | nil => exact .cons .nil hγ
  | cons _ hγ' ih => exact .cons ih hγ'

/-- **The block of a greedy chain along a run**: from a push at `q`, the greedy chain is a hole
block, the run through it realizes the hole triple from the state at `q` to the state at the end of
the block, and pushes the chain's symbols on stack `i`. -/
theorem exists_block_run {w : List (Symbol × Op n Γ)} {i : Fin n} :
    ∀ q, IsPushOn w i q → ∀ (c cf : Config n State Γ), M.configLTS.MTr c (w.drop q) cf →
      ∃ (c' : Config n State Γ) (r : List (Γ × State)) (ps : List (ℕ × Γ)),
        HoleBlock i q (w.extract q (blockEnd w i q)) ps ∧
        ps.map Prod.fst = (chainFrom w i q).reverse ∧ ps.map Prod.snd = r.map Prod.fst ∧
        M.Realizes i c.state c'.state r ∧
        c'.contents = Function.update c.contents i (r.map Prod.fst ++ c.contents i) ∧
        M.configLTS.MTr c' (w.drop (blockEnd w i q)) cf ∧
        q < blockEnd w i q ∧ blockEnd w i q ≤ w.length
  | q, hq, c, cf, hrun => by
    obtain ⟨a, γ, hqa⟩ := hq
    have hqlen : q < w.length := (List.getElem?_eq_some_iff.mp hqa).1
    -- The push at `q`.
    have hdrop : w.drop q = (a, Op.push i γ) :: w.drop (q + 1) := by
      rw [List.drop_eq_getElem_cons hqlen]
      congr 1
      exact (List.getElem?_eq_some_iff.mp hqa).2
    rw [hdrop] at hrun
    obtain ⟨c₁, hpush, hrest⟩ := LTS.MTr.cons_iff.mp hrun
    obtain ⟨hpushT, hpushA⟩ := configLTS_tr.mp hpush
    -- The segment `↓ws` ending at `e`, then the rest of the run from `e`.
    have hseg : ∀ e, q + 1 ≤ e → e ≤ w.length → WellNested (w.extract (q + 1) e) →
        ∃ c₂ : Config n State Γ, (c.state, γ, c₂.state) ∈ M.atomicHoles i ∧
          c₂.contents = Function.update c.contents i (γ :: c.contents i) ∧
          M.configLTS.MTr c₂ (w.drop e) cf := by
      intro e he₁ he₂ hwn
      have hsplit : w.drop (q + 1) = w.extract (q + 1) e ++ w.drop e := by
        rw [List.extract_eq_take_drop, show w.drop e = (w.drop (q + 1)).drop (e - (q + 1)) by
          rw [List.drop_drop]; congr 1; omega, List.take_append_drop]
      rw [hsplit] at hrest
      obtain ⟨c₂, hws, hrest'⟩ := LTS.MTr.split hrest
      obtain ⟨hwsc, hcont⟩ := (hwn.configLTS_mTr_iff).mp hws
      refine ⟨c₂, (mem_atomicHoles M).mpr ⟨a, c₁.state, hpushT,
        wellNestedReach_iff.mpr ⟨_, hwn, hwsc⟩⟩, ?_, hrest'⟩
      rw [hcont]
      exact Op.apply_push.mp hpushA
    rw [chainFrom_eq, blockEnd]
    split_ifs with h
    · -- The chain extends to the least extension `q₂`.
      have hspec := Nat.find_spec h
      set q₂ := Nat.find h
      obtain ⟨c₂, hγ, hc₂, hrun₂⟩ := hseg q₂ (by have := hspec.1; omega)
        (by have := hspec.2.1.1.lt_length; omega) hspec.2.2
      obtain ⟨c', r, ps, hb, hpsf, hpss, hr, hc', hrun', hlt, hle⟩ :=
        exists_block_run q₂ hspec.2.1.1 c₂ cf hrun₂
      refine ⟨c', r ++ [(γ, c₂.state)], ps ++ [(q, γ)], ?_, by simp [hpsf], by simp [hpss],
        hr.prepend hγ, ?_, hrun', by have := hspec.1; omega, hle⟩
      · have hlen : q + 1 + (w.extract (q + 1) q₂).length = q₂ := by
          rw [List.extract_eq_take_drop, List.length_take, List.length_drop]
          have := hspec.1
          have := hspec.2.1.1.lt_length
          omega
        have hb₂ : HoleBlock i (q + 1 + (w.extract (q + 1) q₂).length)
            (w.extract q₂ (blockEnd w i q₂)) ps := by
          rw [hlen]
          exact hb
        have hb' := hb₂.prepend (a := a) (γ := γ) hspec.2.2
        convert hb' using 1
        rw [← w.extract_append_extract (show q ≤ q₂ by have := hspec.1; omega)
          (show q₂ ≤ blockEnd w i q₂ by omega),
          ← w.extract_append_extract (show q ≤ q + 1 by omega) (show q + 1 ≤ q₂ by
            have := hspec.1; omega), List.extract_eq_singleton hqa]
        simp
      · rw [hc', hc₂]
        simp
    · -- The chain stops: one segment, then the longest well-nested factor.
      obtain ⟨hle₁, hle₂, hwn⟩ := wnEnd_spec (w := w) (p := q + 1) (by omega)
      obtain ⟨c₂, hγ, hc₂, hrun₂⟩ := hseg _ hle₁ hle₂ hwn
      refine ⟨c₂, [(γ, c₂.state)], [(q, γ)], ?_, by simp, by simp, .cons .nil hγ, ?_, hrun₂,
        by omega, hle₂⟩
      · have := HoleBlock.snoc (v := []) (L := q) (a := a) (γ := γ) (i := i) .nil hwn
        convert this using 1
        rw [← w.extract_append_extract (show q ≤ q + 1 by omega) hle₁,
          List.extract_eq_singleton hqa]
        simp
      · rw [hc₂]
        simp
termination_by q => w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

end Block

/-! ## The completeness invariant -/

section Invariant

open Classical

theorem chainFrom_lt_blockEnd {w : List (α × Op n Γ)} {i : Fin n} :
    ∀ q, q < w.length → ∀ r ∈ chainFrom w i q, r < blockEnd w i q
  | q, hq, r, hr => by
    rw [chainFrom_eq] at hr
    rw [blockEnd]
    split_ifs at hr ⊢ with h
    · have hspec := Nat.find_spec h
      have hq₂ := hspec.2.1.1.lt_length
      rcases List.mem_cons.mp hr with rfl | hr
      · have := chainFrom_lt_blockEnd (i := i) (Nat.find h) hq₂ _ mem_chainFrom_self
        have := hspec.1
        omega
      · exact chainFrom_lt_blockEnd (Nat.find h) hq₂ r hr
    · obtain rfl := List.mem_singleton.mp hr
      have := (wnEnd_spec (w := w) (p := r + 1) (by omega)).1
      omega
termination_by q => w.length - q
decreasing_by
  all_goals
    have hspec := Nat.find_spec h
    have := hspec.2.1.1.lt_length
    have := hspec.1
    omega

theorem blockEnd_event {w : List (α × Op n Γ)} {i : Fin n} :
    ∀ q, q < w.length → blockEnd w i q < w.length →
      (¬∃ a, w[blockEnd w i q]? = some (a, .nop)) ∧ ¬WellMatched w (blockEnd w i q)
  | q, hq, hlt => by
    rw [blockEnd] at hlt ⊢
    split_ifs at hlt ⊢ with h
    · exact blockEnd_event (Nat.find h) (Nat.find_spec h).2.1.1.lt_length hlt
    · exact wnEnd_event (by omega) hlt
termination_by q => w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

theorem eq_nil_of_stacksOf_eq_empty {C : List (HoleChain n Γ)} (hne : ∀ c ∈ C, c.pushes ≠ [])
    (h : stacksOf C = Stacks.empty) : C = [] := by
  induction C using List.reverseRecOn with
  | nil => rfl
  | append_singleton C d _ =>
    exfalso
    have := congrFun h d.stack
    rw [stacksOf_append_singleton, Function.update_self] at this
    obtain ⟨e, ps, hps⟩ := List.exists_cons_of_ne_nil (hne d (by simp))
    simp [hps, Stacks.empty] at this

theorem update_cons_injective {σ σ' : Stacks n Γ} {i : Fin n} {γ : Γ}
    (h : Function.update σ i (γ :: σ i) = Function.update σ' i (γ :: σ' i)) : σ = σ' := by
  funext j
  by_cases hj : j = i
  · subst hj
    have := congrFun h j
    simp only [Function.update_self, List.cons.injEq, true_and] at this
    exact this
  · have := congrFun h j
    rwa [Function.update_of_ne hj, Function.update_of_ne hj] at this

theorem reverse_take_eq_cons {β : Type*} {L : List β} {m : ℕ} (hm₁ : 1 ≤ m)
    (hm₂ : m ≤ L.length) :
    (L.take m).reverse = L[m - 1] :: (L.take (m - 1)).reverse := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [List.take_succ_eq_append_getElem (by omega), List.reverse_append]
  simp

variable {State Symbol : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  [DecidableEq Γ] (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- The completeness invariant at an event `t` of a run reaching `f` with empty stacks: a reachable
list of the search, a hole derivation of the run up to `t`, and the rest of the run, whose stacks
hold the pushes of the chains; chains, hole triples and their realizations agree; and each chain
is a prefix of a greedy chain whose other pushes are no longer pending. -/
def CInv (K : ℕ) (w : List (Symbol × Op n Γ)) (f : State) (t : ℕ) : Prop :=
  ∃ (μ : HoleList n State) (C : List (HoleChain n Γ)) (rs : List (List (Γ × State)))
    (c : Config n State Γ),
    M.Reachable K M.initialLists μ ∧ HoleDerivation K C (w.take t) ∧
    M.configLTS.MTr c (w.drop t) ⟨f, Stacks.empty⟩ ∧ c.state = μ.last ∧
    c.contents = stacksOf C ∧
    List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.1) C μ.holes ∧
    List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.1 h.2.1 h.2.2 r) rs μ.holes ∧
    List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd = r.map Prod.fst) C rs ∧
    (∀ c ∈ C, c.pushes ≠ []) ∧ (∀ c ∈ C, ∀ e ∈ c.pushes, IsHolePushOn w c.stack e.1) ∧
    ∀ c ∈ C, ∃ q₀ m, c.pushes.map Prod.fst = ((chainFrom w c.stack q₀).take m).reverse ∧
      (∀ r ∈ chainFrom w c.stack q₀, r < t) ∧
      ∀ r ∈ (chainFrom w c.stack q₀).drop m, ¬PendingAt w r (t - 1)

variable {M}

/-- The invariant holds at the first event. -/
theorem cinv_init {K : ℕ} {w : List (Symbol × Op n Γ)} {s₀ f : State} (hs₀ : s₀ ∈ M.start)
    (hrun : M.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨f, Stacks.empty⟩) :
    M.CInv K w f (wnEnd w 0) := by
  obtain ⟨-, hle, hwn⟩ := wnEnd_spec (w := w) (p := 0) (Nat.zero_le _)
  have hsplit : w = w.extract 0 (wnEnd w 0) ++ w.drop (wnEnd w 0) := by
    rw [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, List.take_append_drop]
  rw [hsplit] at hrun
  obtain ⟨c, hpre, hrest⟩ := LTS.MTr.split hrun
  obtain ⟨hctl, hcont⟩ := hwn.configLTS_mTr_iff.mp hpre
  have hμ : (⟨[], c.state⟩ : HoleList n State) ∈ M.initialLists :=
    mem_initialLists.mpr ⟨rfl, s₀, hs₀, (mem_wellNestedPairs M).mpr
      (wellNestedReach_iff.mpr ⟨_, hwn, hctl⟩)⟩
  have htake : w.take (wnEnd w 0) = [] ++ w.extract 0 (wnEnd w 0) := by
    rw [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, List.nil_append]
  refine ⟨⟨[], c.state⟩, [], [], c, .init hμ, htake ▸ .wellNested .nil hwn, hrest, rfl,
    by rw [hcont, stacksOf_nil], .nil, .nil, .nil, by simp, by simp, by simp⟩

/-- At the end of the run, the invariant gives an accepting list. -/
theorem isEmpty_eq_false_of_cinv [DecidablePred (· ∈ M.accept)] {K : ℕ}
    {w : List (Symbol × Op n Γ)} {f : State} (hf : f ∈ M.accept)
    (h : M.CInv K w f w.length) : M.isEmpty K = false := by
  obtain ⟨μ, C, rs, c, hμ, -, hrun, hst, hcont, hstk, -, -, hne, -, -⟩ := h
  rw [List.drop_length] at hrun
  obtain rfl := LTS.MTr.nil_eq _ hrun
  obtain rfl := eq_nil_of_stacksOf_eq_empty hne hcont.symm
  have hholes : μ.holes = [] := List.forall₂_nil_left_iff.mp hstk
  unfold isEmpty isEmptyFrom
  rw [decide_eq_false_iff_not, not_not]
  refine ⟨μ, (mem_explore fun ν hν => (mem_initialLists.mp hν).1).mpr hμ, hholes, f,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, ?_⟩
  rw [← hst]
  exact (mem_wellNestedPairs M).mpr (.refl _)

end Invariant

end Cslib.Automata.MPDA
