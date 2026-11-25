/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.EmptinessSound
import CslibFrontier.Foundations.Data.List.Extract
import CslibFrontier.Foundations.Data.List.Forall2

/-! # Completeness of the emptiness procedure

If an MPDA has a `K`-hole-bounded accepting run, repaired Algorithm 1 of
[AkshayGastinKrishnaRoychowdhury2020] (`MPDA.isEmpty`) answers `false`. With soundness, this is
Theorem 1 for repaired Algorithm 1 (`MPDA.isEmpty_iff`), for every `K`; the source states
Theorem 1 for positive `K`. Starting the search from the initial state alone, as printed, is not
complete (`CslibFrontierTests.MPDA.Emptiness`).

The run is cut at its events: the positions after a maximal well-nested factor, where the next
transition is a pop or a push that is not closed by a well-nested continuation (`MPDA.wnEnd`). A
hole push opens a chain, which extends greedily by the least later hole push of the same stack
behind a well-nested factor; the chain is one `AddHole` step. A pop matches the newest push of the
last chain of its stack and is one `AddPop` step. When a chain opens, Definition 1 counts at least
one more open hole than there are open chains, so a `K`-hole-bounded run never needs more than `K`
of them.

## Main results

- `MPDA.isEmpty_eq_false_of_mem_boundedLanguage`: if some word has a `K`-hole-bounded accepting
  run, repaired Algorithm 1 answers `false`.
- `MPDA.isEmpty_iff`: Theorem 1 for repaired Algorithm 1.

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
    have hext : WellNested (w.extract p (m + 1)) := by
      rw [← w.extract_append_extract hpe (by have := hm.1; omega)]
      exact hwn.append hmwn
    have := le_wnEnd hm.lt_length (by have := hm.1; omega) hext
    have := hm.1
    omega

end Events

/-! ## Greedy chains -/

section Chains

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

open Classical in
private theorem Ext.find_sub_lt {i : Fin n} {q : ℕ} (h : ∃ r, Ext w i q r) :
    w.length - Nat.find h < w.length - q := by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

open Classical in
/-- The greedy chain from position `q`, oldest first: `q`, then the least extension, and so on. -/
noncomputable def chainFrom (w : List (α × Op n Γ)) (i : Fin n) (q : ℕ) : List ℕ :=
  if h : ∃ r, Ext w i q r then q :: chainFrom w i (Nat.find h) else [q]
termination_by w.length - q
decreasing_by exact Ext.find_sub_lt h

open Classical in
theorem chainFrom_eq {i : Fin n} {q : ℕ} : chainFrom w i q =
    if h : ∃ r, Ext w i q r then q :: chainFrom w i (Nat.find h) else [q] := by
  rw [chainFrom]

open Classical in
theorem mem_chainFrom_self {i : Fin n} {q : ℕ} : q ∈ chainFrom w i q := by
  rw [chainFrom_eq]
  split_ifs <;> simp

open Classical in
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
        rcases eq_or_ne r (Nat.find h) with rfl | hrf
        exacts [hspec.2.1, hhole hrf]
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨le_rfl, fun h' => absurd rfl h'⟩
termination_by q => w.length - q
decreasing_by exact Ext.find_sub_lt h

open Classical in
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
decreasing_by exact Ext.find_sub_lt h

end Chains

/-! ## The counting guard -/

section Guard

variable {w : List (α × Op n Γ)}

theorem pendingAt_self {i : Fin n} {t : ℕ} (h : IsPushOn w i t) : PendingAt w t t :=
  ⟨le_rfl, h.lt_length, i, h, fun k => by
    rw [List.extract_eq_take_drop, Nat.sub_self, List.take_zero, List.take_nil]
    simp⟩

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
    simp only [hl, List.pairwise_append, List.mem_append, List.mem_singleton] at he' hpw
    rcases he' with he' | rfl
    exacts [(hpw.2.2 e' he' e rfl).le, le_rfl]
  -- A pending push joined to a later hole push `q` lies in a chain closed up to `q`.
  have hext_of_same : ∀ {p q j'}, p < q → q ≤ t → PendingAt w p t →
      (∃ j, IsPushOn w j p ∧ IsPushOn w j q) → IsHolePushOn w j' q →
      WellNested (w.extract (p + 1) q) →
      ∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = p ∧ Ext w c.stack e.1 q := by
    intro p q j' hpq hqt hp ⟨j, hpj, hqj⟩ hqhole hwn
    obtain ⟨c, hc, e, he, rfl⟩ := hcover p (by omega) hp
    have hjc : c.stack = j := (helem c hc e he).1.1.unique hpj
    exact ⟨c, hc, e, he, rfl, hpq, by rw [hjc, hqj.unique hqhole.1]; exact hqhole, hwn⟩
  -- The counted pushes.
  set S := {q | OpenHolePush w t q ∧ ¬∃ p, SameHole w t p q}
  have hT : ((insert t ((C.map old).toFinset) : Finset ℕ) : Set ℕ) ⊆ S := by
    intro q hq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, List.mem_toFinset,
      List.mem_map] at hq
    rcases hq with rfl | ⟨c, hc, rfl⟩
    · refine ⟨⟨⟨⟨i, ht.1⟩, ht.2⟩, pendingAt_self ht.1⟩, ?_⟩
      rintro ⟨p, hpt, ⟨-, hp⟩, -, hstk, hwn⟩
      obtain ⟨c, hc, e, he, -, hext⟩ := hext_of_same hpt le_rfl hp hstk ht hwn
      exact absurd (hclosed c hc e he q hext).1 (lt_irrefl _)
    · obtain ⟨e, he, hev, hmin⟩ := hold c hc
      obtain ⟨hhole, hpend, het⟩ := helem c hc e he
      rw [← hev]
      refine ⟨⟨⟨⟨c.stack, hhole.1⟩, hhole.2⟩, hpend⟩, ?_⟩
      rintro ⟨p, hpe, ⟨-, hp⟩, -, hstk, hwn⟩
      obtain ⟨c', hc', f, hf, rfl, hext⟩ := hext_of_same hpe het.le hp hstk hhole hwn
      obtain ⟨g, hg, hge⟩ := (hclosed c' hc' f hf e.1 hext).2 hpend
      obtain rfl : c' = c := by
        by_contra hcc
        exact chains_ne horder hc hc' (Ne.symm hcc) e he g hg hge.symm
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
    ∀ {l : List (HoleTriple n State)}, (∀ h ∈ l, h.stack ≠ i) → splitLastHole i l = none
  | [], _ => rfl
  | h :: t, hl => by
    unfold splitLastHole
    rw [splitLastHole_eq_none fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')]
    simp [hl h List.mem_cons_self]

/-- The converse of `splitLastHole_eq_some`. -/
theorem splitLastHole_eq_some_of {State : Type*} {i : Fin n} {post : List (HoleTriple n State)}
    {s s' : State} (hpost : ∀ h ∈ post, h.stack ≠ i) :
    ∀ pre : List (HoleTriple n State),
      splitLastHole i (pre ++ ⟨i, s, s'⟩ :: post) = some (pre, (s, s'), post)
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
      · exact (List.mem_singleton.mp hd').symm ▸ hd

/-- Prepend an atomic hole segment to a hole block. -/
theorem HoleBlock.prepend {i : Fin n} {L : ℕ} {v ws : List (α × Op n Γ)} {ps : List (ℕ × Γ)}
    {a : α} {γ : Γ} (hb : HoleBlock i (L + 1 + ws.length) v ps) (hws : WellNested ws) :
    HoleBlock i L ((a, .push i γ) :: ws ++ v) (ps ++ [(L, γ)]) := by
  induction hb with
  | nil => simpa using HoleBlock.snoc (v := []) (L := L) (a := a) (γ := γ) .nil hws
  | @snoc v ws' ps' a' γ' _ hws' ih =>
    convert HoleBlock.snoc (a := a') (γ := γ') ih hws' using 1
    · simp [List.cons_append, List.append_assoc]
    · simp only [List.cons_append, List.length_cons, List.length_append, List.cons.injEq,
        Prod.mk.injEq, and_true]
      omega

end Helpers

/-! ## Blocks of greedy chains along a run -/

section Block

open Classical in
/-- The end of the hole block of the greedy chain from `q`: after its last push, the longest
well-nested factor. -/
noncomputable def blockEnd (w : List (α × Op n Γ)) (i : Fin n) (q : ℕ) : ℕ :=
  if h : ∃ r, Ext w i q r then blockEnd w i (Nat.find h) else wnEnd w (q + 1)
termination_by w.length - q
decreasing_by exact Ext.find_sub_lt h

variable {State Symbol : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]

/-- Prepend an atomic hole segment to a realization. -/
theorem Realizes.prepend {i : Fin n} {s s₁ t : State} {γ : Γ} {r : List (Γ × State)}
    (hγ : ⟨s, γ, s₁⟩ ∈ M.atomicHoles i) (hr : M.Realizes i s₁ t r) :
    M.Realizes i s t (r ++ [(γ, s₁)]) := by
  induction hr with
  | nil => exact .cons .nil hγ
  | cons _ hγ' ih => exact .cons ih hγ'

open Classical in
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
      rw [List.drop_eq_getElem_cons hqlen, (List.getElem?_eq_some_iff.mp hqa).2]
    rw [hdrop] at hrun
    obtain ⟨c₁, hpush, hrest⟩ := LTS.MTr.cons_iff.mp hrun
    obtain ⟨hpushT, hpushA⟩ := configLTS_tr.mp hpush
    -- The segment `↓ws` ending at `e`, then the rest of the run from `e`.
    have hseg : ∀ e, q + 1 ≤ e → e ≤ w.length → WellNested (w.extract (q + 1) e) →
        ∃ c₂ : Config n State Γ, ⟨c.state, γ, c₂.state⟩ ∈ M.atomicHoles i ∧
          c₂.contents = Function.update c.contents i (γ :: c.contents i) ∧
          M.configLTS.MTr c₂ (w.drop e) cf := by
      intro e he₁ he₂ hwn
      rw [w.drop_eq_extract_append_drop he₁] at hrest
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
        have hb' : HoleBlock i (q + 1 + (w.extract (q + 1) q₂).length)
            (w.extract q₂ (blockEnd w i q₂)) ps := by rw [hlen]; exact hb
        convert hb'.prepend (a := a) (γ := γ) hspec.2.2 using 1
        rw [← w.extract_append_extract (show q ≤ q₂ by have := hspec.1; omega)
          (show q₂ ≤ blockEnd w i q₂ by omega),
          ← w.extract_append_extract (by omega) (show q + 1 ≤ q₂ by have := hspec.1; omega),
          List.extract_eq_singleton hqa]
        simp
      · rw [hc', hc₂]; simp
    · -- The chain stops: one segment, then the longest well-nested factor.
      obtain ⟨hle₁, hle₂, hwn⟩ := wnEnd_spec (w := w) (p := q + 1) (by omega)
      obtain ⟨c₂, hγ, hc₂, hrun₂⟩ := hseg _ hle₁ hle₂ hwn
      refine ⟨c₂, [(γ, c₂.state)], [(q, γ)], ?_, by simp, by simp, .cons .nil hγ,
        by rw [hc₂]; simp, hrun₂, by omega, hle₂⟩
      convert HoleBlock.snoc (v := []) (L := q) (a := a) (γ := γ) (i := i) .nil hwn using 1
      rw [← w.extract_append_extract (by omega) hle₁, List.extract_eq_singleton hqa]
      simp
termination_by q => w.length - q
decreasing_by exact Ext.find_sub_lt h

end Block

/-! ## The completeness invariant -/

section Invariant

open Classical in
theorem chainFrom_lt_blockEnd {w : List (α × Op n Γ)} {i : Fin n} :
    ∀ q, q < w.length → ∀ r ∈ chainFrom w i q, r < blockEnd w i q
  | q, hq, r, hr => by
    rw [chainFrom_eq] at hr
    rw [blockEnd]
    split_ifs at hr ⊢ with h
    · have hspec := Nat.find_spec h
      have hq₂ := hspec.2.1.1.lt_length
      rcases List.mem_cons.mp hr with hqr | hr
      · rw [hqr]
        have := chainFrom_lt_blockEnd (i := i) (Nat.find h) hq₂ _ mem_chainFrom_self
        have := hspec.1
        omega
      · exact chainFrom_lt_blockEnd (Nat.find h) hq₂ r hr
    · obtain rfl := List.mem_singleton.mp hr
      have := (wnEnd_spec (w := w) (p := r + 1) (by omega)).1
      omega
termination_by q => w.length - q
decreasing_by all_goals exact Ext.find_sub_lt h

open Classical in
theorem blockEnd_event {w : List (α × Op n Γ)} {i : Fin n} :
    ∀ q, q < w.length → blockEnd w i q < w.length →
      (¬∃ a, w[blockEnd w i q]? = some (a, .nop)) ∧ ¬WellMatched w (blockEnd w i q)
  | q, hq, hlt => by
    rw [blockEnd] at hlt ⊢
    split_ifs at hlt ⊢ with h
    · exact blockEnd_event (Nat.find h) (Nat.find_spec h).2.1.1.lt_length hlt
    · exact wnEnd_event (by omega) hlt
termination_by q => w.length - q
decreasing_by exact Ext.find_sub_lt h

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
  have hj' := congrFun h j
  by_cases hj : j = i
  · subst hj
    simpa only [Function.update_self, List.cons.injEq, true_and] using hj'
  · rwa [Function.update_of_ne hj, Function.update_of_ne hj] at hj'

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
private def CInv (K : ℕ) (w : List (Symbol × Op n Γ)) (f : State) (t : ℕ) : Prop :=
  ∃ (μ : HoleList n State) (C : List (HoleChain n Γ)) (rs : List (List (Γ × State)))
    (c : Config n State Γ),
    M.Reachable K M.initialLists μ ∧ HoleDerivation K C (w.take t) ∧
    M.configLTS.MTr c (w.drop t) ⟨f, Stacks.empty⟩ ∧ c.state = μ.last ∧
    c.contents = stacksOf C ∧
    List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) C μ.holes ∧
    List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r) rs μ.holes ∧
    List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd = r.map Prod.fst) C rs ∧
    (∀ c ∈ C, c.pushes ≠ []) ∧ (∀ c ∈ C, ∀ e ∈ c.pushes, IsHolePushOn w c.stack e.1) ∧
    ∀ c ∈ C, ∃ q₀ m, c.pushes.map Prod.fst = ((chainFrom w c.stack q₀).take m).reverse ∧
      (∀ r ∈ chainFrom w c.stack q₀, r < t) ∧
      ∀ r ∈ (chainFrom w c.stack q₀).drop m, ¬PendingAt w r (t - 1)

variable {M}

/-- The invariant holds at the first event. -/
private theorem cinv_init {K : ℕ} {w : List (Symbol × Op n Γ)} {s₀ f : State}
    (hs₀ : s₀ ∈ M.start) (hrun : M.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨f, Stacks.empty⟩) :
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
private theorem isEmpty_eq_false_of_cinv [DecidablePred (· ∈ M.accept)] {K : ℕ}
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

/-! ## The pop step -/

section PopStep

private theorem CInv.chain_mono {t t' : ℕ} (htt' : t ≤ t') {w : List (α × Op n Γ)}
    {c : HoleChain n Γ}
    (h : ∃ q₀ m, c.pushes.map Prod.fst = ((chainFrom w c.stack q₀).take m).reverse ∧
      (∀ r ∈ chainFrom w c.stack q₀, r < t) ∧
      ∀ r ∈ (chainFrom w c.stack q₀).drop m, ¬PendingAt w r (t - 1)) :
    ∃ q₀ m, c.pushes.map Prod.fst = ((chainFrom w c.stack q₀).take m).reverse ∧
      (∀ r ∈ chainFrom w c.stack q₀, r < t') ∧
      ∀ r ∈ (chainFrom w c.stack q₀).drop m, ¬PendingAt w r (t' - 1) := by
  obtain ⟨q₀, m, hm, hlt, hpend⟩ := h
  exact ⟨q₀, m, hm, fun r hr => (hlt r hr).trans_le htt', fun r hr hr' =>
    hpend r hr (hr'.anti (by have := hlt r (List.mem_of_mem_drop hr); omega) (by omega))⟩

private theorem chainFrom_drop_pred_not_pendingAt {w : List (α × Op n Γ)} {i : Fin n}
    {q₀ m₀ t t' : ℕ} {p : ℕ} {ps : List (ℕ × Γ)} {γ : Γ} (htt' : t < t')
    (hm : ((p, γ) :: ps).map Prod.fst = ((chainFrom w i q₀).take m₀).reverse)
    (hlt₀ : ∀ r ∈ chainFrom w i q₀, r < t)
    (hpend₀ : ∀ r ∈ (chainFrom w i q₀).drop m₀, ¬PendingAt w r (t - 1))
    (hpnot : ¬PendingAt w p t) :
    ∃ m, ps.map Prod.fst = ((chainFrom w i q₀).take m).reverse ∧
      (∀ r ∈ chainFrom w i q₀, r < t') ∧
      ∀ r ∈ (chainFrom w i q₀).drop m, ¬PendingAt w r (t' - 1) := by
  set L := chainFrom w i q₀
  set m := min m₀ L.length with hmdef
  have htake : L.take m = L.take m₀ := by
    rcases le_total m₀ L.length with h | h <;> simp [m, h, List.take_of_length_le]
  replace hpend₀ : ∀ r ∈ L.drop m, ¬PendingAt w r (t - 1) := by
    intro r hr
    rcases le_total m₀ L.length with h | h
    · rw [hmdef, min_eq_left h] at hr; exact hpend₀ r hr
    · simp [hmdef, min_eq_right h] at hr
  rw [← htake] at hm
  have hm₂ : m ≤ L.length := min_le_right _ _
  have hm₁ : 1 ≤ m := by
    have := congrArg List.length hm
    simp only [List.length_map, List.length_cons, List.length_reverse, List.length_take] at this
    omega
  rw [reverse_take_eq_cons hm₁ hm₂] at hm
  simp only [List.map_cons, List.cons.injEq] at hm
  refine ⟨m - 1, hm.2, fun r hr => (hlt₀ r hr).trans htt', fun r hr hr' => ?_⟩
  rw [List.drop_eq_getElem_cons (by omega), show m - 1 + 1 = m by omega] at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [← hm.1] at hr'
    have := hlt₀ _ (List.getElem_mem (show m - 1 < L.length by omega))
    exact hpnot (hr'.anti (by rw [← hm.1] at this; omega) (by omega))
  · have := hlt₀ r (List.mem_of_mem_drop hr)
    exact hpend₀ r hr (hr'.anti (by omega) (by omega))

variable {State Symbol : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  [DecidableEq Γ] {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- **The pop step**: at a pop, the invariant moves to the next event. -/
private theorem cinv_pop {K : ℕ} {w : List (Symbol × Op n Γ)} {f : State} {t : ℕ}
    {b : Symbol} {i : Fin n} {γ : Γ} (hwt : w[t]? = some (b, .pop i γ)) (h : M.CInv K w f t) :
    t < wnEnd w (t + 1) ∧ M.CInv K w f (wnEnd w (t + 1)) := by
  have htlen : t < w.length := (List.getElem?_eq_some_iff.mp hwt).1
  obtain ⟨μ, C, rs, c, hμ, hd, hrun, hst, hcont, hstk, hreal, hsym, hne, hhole, hcons⟩ := h
  set t' := wnEnd w (t + 1) with ht'
  obtain ⟨ht1, ht'len, hwn⟩ := wnEnd_spec (w := w) (p := t + 1) (by omega)
  -- The run: the pop, then a well-nested factor up to the next event.
  have hdrop : w.drop t = (b, Op.pop i γ) :: w.drop (t + 1) := by
    rw [List.drop_eq_getElem_cons htlen, (List.getElem?_eq_some_iff.mp hwt).2]
  rw [hdrop, w.drop_eq_extract_append_drop ht1] at hrun
  obtain ⟨c₁, hpopT, hrest⟩ := LTS.MTr.cons_iff.mp hrun
  obtain ⟨c₂, hwnrun, hrest⟩ := LTS.MTr.split hrest
  obtain ⟨hTr, hApply⟩ := configLTS_tr.mp hpopT
  obtain ⟨hwnctl, hc₂⟩ := hwn.configLTS_mTr_iff.mp hwnrun
  have hApply' := Op.apply_pop.mp hApply
  -- The last chain of stack `i` and its newest push.
  have htop : stacksOf C i = γ :: c₁.contents i := by
    rw [← hcont, hApply', Function.update_self]
  obtain ⟨pre, post, p, ps, rfl, hpost⟩ := stacksOf_eq_cons hne htop
  have hc₁ : c₁.contents = stacksOf (pre ++ ⟨i, ps⟩ :: post) := by
    apply update_cons_injective (i := i) (γ := γ)
    rw [← stacksOf_pop hpost, ← hcont, hApply']
  -- Align the chains with the hole triples and the realizations.
  obtain ⟨hpre, ⟨i₀, s₁, s₃⟩, hpost', hμh, hlen, hstkpre, hh₀, hstkpost⟩ :=
    List.Forall₂.split_left_cons hstk
  obtain ⟨rpre, r₀, rpost, rfl, hrlen, hsympre, hsym₀, hsympost⟩ := hsym.split_left_cons
  rw [hμh] at hreal
  obtain ⟨hrealpre, hrealrest⟩ := List.Forall₂.split_of_length_eq (hrlen.trans hlen.symm) hreal
  cases hrealrest with
  | cons hreal₀ hrealpost =>
  simp only at hh₀ hreal₀
  subst hh₀
  have hpost'' : ∀ h ∈ hpost', h.stack ≠ i := fun h hh => by
    obtain ⟨d, hd', hdh⟩ := List.Forall₂.exists_mem_of_mem hstkpost.flip hh
    exact hdh ▸ hpost d hd'
  have hsplitLast := splitLastHole_eq_some_of (s := s₁) (s' := s₃) hpost'' hpre
  cases hreal₀ with
  | nil => simp at hsym₀
  | @cons s₂ _ γ' r hr hγ' =>
  simp only [List.map_cons, List.cons.injEq] at hsym₀
  obtain ⟨rfl, hpsr⟩ := hsym₀
  have hHS : (s₁, s₂) ∈ M.holeSegments i := mem_holeSegments_iff_realizes.mpr ⟨r, hr⟩
  have hWR : (c₁.state, c₂.state) ∈ M.wellNestedPairs :=
    (mem_wellNestedPairs M).mpr (wellNestedReach_iff.mpr ⟨_, hwn, hwnctl⟩)
  have hd₁ : HoleDerivation K (pre ++ ⟨i, ps⟩ :: post) (w.take (t + 1)) := by
    rw [List.take_add_one, hwt, Option.toList_some]; exact hd.pop hpost
  -- Positions of the other chains, relative to `p`.
  obtain ⟨hB, -⟩ := hd.invariant
  obtain ⟨-, -, hB₃, -, hB₅⟩ := hB
  rw [List.pairwise_append, List.pairwise_cons] at hB₅
  have hp_mem : (p, γ) ∈ (⟨i, (p, γ) :: ps⟩ : HoleChain n Γ).pushes := List.mem_cons_self
  have hlt_ps : ∀ e ∈ ps, e.1 < p := fun e he =>
    (List.pairwise_cons.mp (Chained.pairwise (hB₃ ⟨i, (p, γ) :: ps⟩ (by simp)))).1 e he
  -- `p` is no longer pending after the pop.
  have hpnot : ¬PendingAt w p t := by
    intro hp
    obtain ⟨hB', -⟩ := hd₁.invariant
    have hlen₁ : (w.take (t + 1)).length = t + 1 := by simp; omega
    obtain ⟨d, hd', e, he, hep⟩ := hB'.2.2.2.1 p (by
      rw [hlen₁, show t + 1 - 1 = t by omega]
      exact (pendingAt_append_iff (v := w.drop (t + 1)) (by omega)).mp
        (by rwa [List.take_append_drop]))
    rcases List.mem_append.mp hd' with hd' | hd'
    · have := hB₅.2.2 d hd' _ (by simp) e he _ hp_mem; omega
    · rcases List.mem_cons.mp hd' with rfl | hd'
      · have := hlt_ps e he; omega
      · have := hB₅.2.1.1 d hd' _ hp_mem e he; omega
  obtain ⟨q₀, m₀, hm, hlt₀, hpend₀⟩ := hcons ⟨i, (p, γ) :: ps⟩ (by simp)
  have hcons_ps := chainFrom_drop_pred_not_pendingAt (by omega : t < t') hm hlt₀ hpend₀ hpnot
  have hpopnext : ∀ ν, ν ∈ M.addPop i μ → M.Reachable K M.initialLists ν := fun ν hν =>
    .step hμ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hν⟩))
  have hok : (s₁, s₂) ∈ M.holeSegments i ∧ ⟨s₂, γ, s₃⟩ ∈ M.atomicHoles i ∧
      (∃ b', M.Tr μ.last (b', .pop i γ) c₁.state) ∧ (c₁.state, c₂.state) ∈ M.wellNestedPairs :=
    ⟨hHS, hγ', ⟨b, hst ▸ hTr⟩, hWR⟩
  have htake' : w.take t' = w.take (t + 1) ++ w.extract (t + 1) t' :=
    w.take_eq_take_append_extract ht1
  have hmem_old : ∀ {d}, d ∈ pre ++ post → d ∈ pre ++ ⟨i, (p, γ) :: ps⟩ :: post := fun {d} hd' => by
    rcases List.mem_append.mp hd' with hd' | hd' <;> simp [hd']
  refine ⟨by omega, ?_⟩
  rcases eq_or_ne ps [] with rfl | hpsne
  · obtain rfl : r = [] := by simpa using hpsr.symm
    cases hr
    refine ⟨⟨hpre ++ hpost', c₂.state⟩, pre ++ post, rpre ++ rpost, c₂, hpopnext _ ?_,
      htake' ▸ hd₁.close.wellNested hwn, hrest, rfl, by rw [hc₂, hc₁, stacksOf_close],
      List.rel_append hstkpre hstkpost, List.rel_append hrealpre hrealpost,
      List.rel_append hsympre hsympost, fun d hd' => hne d (hmem_old hd'),
      fun d hd' => hhole d (hmem_old hd'),
      fun d hd' => CInv.chain_mono (by omega) (hcons d (hmem_old hd'))⟩
    unfold addPop
    rw [hμh, hsplitLast]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(s₁, γ, c₁.state, c₂.state),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hok, rfl⟩, rfl⟩)
  · have hsh : ∀ {P : HoleChain n Γ → Prop},
        (∀ d ∈ pre ++ ⟨i, (p, γ) :: ps⟩ :: post, P d) → P ⟨i, ps⟩ →
        ∀ d ∈ pre ++ ⟨i, ps⟩ :: post, P d := fun hC hnew d hd' => by
      simp only [List.mem_append, List.mem_cons] at hd'
      rcases hd' with hd' | rfl | hd'
      exacts [hC d (by simp [hd']), hnew, hC d (by simp [hd'])]
    refine ⟨⟨hpre ++ ⟨i, s₁, s₂⟩ :: hpost', c₂.state⟩, pre ++ ⟨i, ps⟩ :: post,
      rpre ++ r :: rpost, c₂, hpopnext _ ?_, htake' ▸ hd₁.wellNested hwn, hrest, rfl,
      by rw [hc₂, hc₁], List.rel_append hstkpre (.cons rfl hstkpost),
      List.rel_append hrealpre (.cons hr hrealpost), List.rel_append hsympre (.cons hpsr hsympost),
      hsh hne hpsne,
      hsh hhole fun e he => hhole ⟨i, (p, γ) :: ps⟩ (by simp) e (List.mem_cons_of_mem _ he),
      hsh (fun d hd' => CInv.chain_mono (by omega) (hcons d hd')) ⟨q₀, hcons_ps⟩⟩
    unfold addPop
    rw [hμh, hsplitLast]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(s₂, γ, c₁.state, c₂.state),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hok⟩, rfl⟩)

end PopStep

/-! ## The hole step -/

section HoleStep

/-- A push pending before a push stays pending across it. -/
theorem pendingAt_of_push {w : List (α × Op n Γ)} {p t : ℕ} {a : α} {i : Fin n} {γ : Γ}
    (h : PendingAt w p (t - 1)) (hpt : p < t) (hwt : w[t]? = some (a, .push i γ)) :
    PendingAt w p t := by
  have htlen : t < w.length := (List.getElem?_eq_some_iff.mp hwt).1
  refine h.extend (by omega) htlen fun j _ k => ?_
  rw [show t - 1 + 1 = t by omega, List.extract_eq_singleton hwt]
  rcases k with _ | k
  · simp
  · simp only [List.take_succ_cons, List.take_nil, net_cons, net_nil, add_zero,
      Op.net, Op.kind, OpKind.net]
    split_ifs <;> simp

variable {State Symbol : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  [DecidableEq Γ] {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- **The hole step**: at a hole push, the invariant moves to the end of the block of its greedy
chain. The counting guard keeps the number of chains below `K`. -/
private theorem cinv_hole {K : ℕ} {w : List (Symbol × Op n Γ)} {f : State} {t : ℕ}
    {a : Symbol} {i : Fin n} {γ : Γ} (hK : HoleBounded K w)
    (hwt : w[t]? = some (a, .push i γ)) (hev : ¬WellMatched w t) (h : M.CInv K w f t) :
    t < blockEnd w i t ∧ M.CInv K w f (blockEnd w i t) := by
  have htlen : t < w.length := (List.getElem?_eq_some_iff.mp hwt).1
  obtain ⟨μ, C, rs, c, hμ, hd, hrun, hst, hcont, hstk, hreal, hsym, hne, hhole, hcons⟩ := h
  have hpush : IsPushOn w i t := ⟨a, γ, hwt⟩
  have ht : IsHolePushOn w i t := ⟨hpush, hev⟩
  have htake_len : (w.take t).length = t := by simp; omega
  obtain ⟨hB, -⟩ := hd.invariant
  obtain ⟨-, hB₂, hB₃, hB₄, hB₅⟩ := hB
  rw [htake_len] at hB₂ hB₄
  -- The old pushes, seen in `w`.
  have hold : ∀ d ∈ C, ∀ e ∈ d.pushes, e.1 < t ∧ PendingAt w e.1 (t - 1) := by
    intro d hd' e he
    obtain ⟨⟨b, hb⟩, hpend⟩ := hB₂ d hd' e he
    have hlt : e.1 < t := htake_len ▸ (List.getElem?_eq_some_iff.mp hb).1
    refine ⟨hlt, ?_⟩
    simpa using (pendingAt_append_iff (v := w.drop t) (by omega)).mpr hpend
  -- The counting guard.
  have hguard : C.length + 1 ≤ openHoles w t := by
    refine card_add_one_le_openHoles ht hne (fun d hd' e he => ⟨hhole d hd' e he,
      pendingAt_of_push (hold d hd' e he).2 (hold d hd' e he).1 hwt, (hold d hd' e he).1⟩)
      (fun q hq hpq => hB₄ q ?_) hB₅ (fun d hd' => (hB₃ d hd').pairwise) ?_
    · rw [← pendingAt_append_iff (v := w.drop t) (show t - 1 < (w.take t).length by omega),
        List.take_append_drop]
      exact hpq.anti (show q ≤ t - 1 by omega) (by omega)
    · intro d hd' e he r hr
      obtain ⟨q₀, m, hm, hlt, hpend⟩ := hcons d hd'
      have heL : e.1 ∈ chainFrom w d.stack q₀ :=
        List.mem_of_mem_take (List.mem_reverse.mp (hm ▸ List.mem_map_of_mem he))
      have hrL := mem_chainFrom_of_ext q₀ e.1 heL r hr
      have hrt := hlt r hrL
      refine ⟨hrt, fun hpr => ?_⟩
      rw [← List.take_append_drop m (chainFrom w d.stack q₀), List.mem_append] at hrL
      rcases hrL with hrL | hrL
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp (hm ▸ List.mem_reverse.mpr hrL)
        exact ⟨e', he', rfl⟩
      · exact absurd (hpr.anti (by omega) (by omega)) (hpend r hrL)
  have hClt : C.length < K := by have := hK t htlen; omega
  -- The block of the greedy chain from `t`.
  obtain ⟨c', r, ps, hblock, hpsfst, hpssnd, hr, hc', hrun', htlt, -⟩ :=
    exists_block_run (M := M) t hpush c _ hrun
  have hd' : HoleDerivation K (C ++ [⟨i, ps⟩]) (w.take (blockEnd w i t)) := by
    rw [w.take_eq_take_append_extract htlt.le]
    exact hd.hole hClt (by rw [htake_len]; exact hblock)
  -- The step of the search.
  have hHS : (μ.last, c'.state) ∈ M.holeSegments i :=
    hst ▸ mem_holeSegments_iff_realizes.mpr ⟨r, hr⟩
  have hif : μ.holes.length < K := hstk.length_eq.symm ▸ hClt
  have hnext : M.Reachable K M.initialLists ⟨μ.holes ++ [⟨i, μ.last, c'.state⟩], c'.state⟩ :=
    .step hμ (by
      simp only [successors, hif, ↓reduceIte]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨(μ.last, c'.state), Finset.mem_filter.mpr ⟨hHS, rfl⟩, rfl⟩⟩))
  refine ⟨htlt, ⟨μ.holes ++ [⟨i, μ.last, c'.state⟩], c'.state⟩, C ++ [⟨i, ps⟩], rs ++ [r], c',
    hnext, hd', hrun', rfl, ?_, List.rel_append hstk (.cons rfl .nil),
    List.rel_append hreal (.cons (by rw [← hst]; exact hr) .nil),
    List.rel_append hsym (.cons hpssnd .nil), ?_, ?_, ?_⟩
  · rw [hc', hcont, stacksOf_append_singleton, hpssnd]
  · refine List.forall_mem_append.mpr ⟨hne, List.forall_mem_singleton.mpr fun hps => ?_⟩
    have h₂ : t ∈ (chainFrom w i t).reverse := List.mem_reverse.mpr mem_chainFrom_self
    dsimp at hps
    simp [← hpsfst, hps] at h₂
  · refine List.forall_mem_append.mpr ⟨hhole, List.forall_mem_singleton.mpr fun e he => ?_⟩
    have : e.1 ∈ chainFrom w i t := List.mem_reverse.mp (hpsfst ▸ List.mem_map_of_mem he)
    by_cases het : e.1 = t
    · exact het ▸ ht
    · exact (chainFrom_spec t e.1 this).2 het
  · exact List.forall_mem_append.mpr ⟨fun d hd' => CInv.chain_mono htlt.le (hcons d hd'),
      List.forall_mem_singleton.mpr ⟨t, (chainFrom w i t).length,
        by rw [List.take_length]; exact hpsfst, chainFrom_lt_blockEnd t htlen, by simp⟩⟩

end HoleStep

/-! ## Completeness -/

section Complete

open Classical in
theorem blockEnd_le_length {w : List (α × Op n Γ)} {i : Fin n} :
    ∀ q, q < w.length → blockEnd w i q ≤ w.length
  | q, hq => by
    rw [blockEnd]
    split_ifs with h
    · exact blockEnd_le_length (Nat.find h) (Nat.find_spec h).2.1.1.lt_length
    · exact (wnEnd_spec (by omega)).2.1
termination_by q => w.length - q
decreasing_by exact Ext.find_sub_lt h

variable {State Symbol : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  [DecidableEq Γ] {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- From an event, or the end, the invariant reaches the end of the run. -/
private theorem cinv_length {K : ℕ} {w : List (Symbol × Op n Γ)} {f : State}
    (hK : HoleBounded K w) :
    ∀ t, t ≤ w.length →
      (t < w.length → (¬∃ a, w[t]? = some (a, .nop)) ∧ ¬WellMatched w t) →
      M.CInv K w f t → M.CInv K w f w.length
  | t, hle, hev, h => by
    rcases lt_or_eq_of_le hle with hlt | rfl
    · obtain ⟨hnop, hwm⟩ := hev hlt
      obtain ⟨⟨a, op⟩, hwt⟩ : ∃ x, w[t]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
      cases op with
      | nop => exact absurd ⟨a, hwt⟩ hnop
      | push i γ =>
        obtain ⟨ht', h'⟩ := cinv_hole hK hwt hwm h
        have hle' := blockEnd_le_length (i := i) t hlt
        exact cinv_length hK _ hle' (blockEnd_event t hlt) h'
      | pop i γ =>
        obtain ⟨ht', h'⟩ := cinv_pop hwt h
        have hle' := (wnEnd_spec (w := w) (p := t + 1) (by omega)).2.1
        exact cinv_length hK _ hle' (wnEnd_event (by omega)) h'
    · exact h
termination_by t => w.length - t

/-- **Completeness of repaired Algorithm 1** of [AkshayGastinKrishnaRoychowdhury2020]: if some
word has a `K`-hole-bounded accepting run, the search answers `false`. -/
theorem isEmpty_eq_false_of_mem_boundedLanguage [DecidablePred (· ∈ M.accept)] {K : ℕ}
    {x : List Symbol} (hx : x ∈ M.boundedLanguage (HoleBounded K)) : M.isEmpty K = false := by
  obtain ⟨s₀, hs₀, f, hf, w, -, hrun, hK⟩ := hx
  obtain ⟨-, hle, -⟩ := wnEnd_spec (w := w) (p := 0) (Nat.zero_le _)
  exact isEmpty_eq_false_of_cinv hf
    (cinv_length hK _ hle (wnEnd_event (Nat.zero_le _)) (cinv_init (K := K) hs₀ hrun))

/-- **Theorem 1** of [AkshayGastinKrishnaRoychowdhury2020], for repaired Algorithm 1: the search
answers `true` exactly when no word has a `K`-hole-bounded accepting run. It holds for every `K`,
including `K = 0`; the source states Theorem 1 for positive `K`. -/
theorem isEmpty_iff [DecidablePred (· ∈ M.accept)] {K : ℕ} :
    M.isEmpty K = true ↔ M.boundedLanguage (HoleBounded K) = 0 := by
  refine ⟨fun h => Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
      Bool.false_ne_true (isEmpty_eq_false_of_mem_boundedLanguage hx ▸ h),
    fun h => Bool.eq_true_of_not_eq_false fun h' => ?_⟩
  obtain ⟨x, hx⟩ := exists_mem_boundedLanguage_of_isEmpty_eq_false h'
  exact cast (congrArg (x ∈ ·) h) hx

end Complete

end Cslib.Automata.MPDA
