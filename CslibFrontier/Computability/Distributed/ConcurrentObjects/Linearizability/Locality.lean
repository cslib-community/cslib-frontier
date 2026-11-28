/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Basic
import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.CallIndex
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
# Interval-order cycle collapse and Herlihy–Wing Theorem 1 (Locality)

Algebraic interval-order acyclicity (`acyclic_sup_of_isIntervalOrder`), finite topological sort,
per-object operation lifting (`liftOp`), and **Herlihy–Wing Theorem 1**
(`isLinearizable_iff_forall_obj`, compositionality / locality of linearizability across typed
concurrent objects; [HerlihyWing1990], §3.1, Theorem 1, pp. 470–471; [SelaHerlihyPetrank2021],
§5.2, Theorem 5.1, pp. 7–9).

## Main results

* `Cslib.Distributed.ConcurrentObjects.History.prec_append_resp_iff`: appending response events does
  not alter real-time precedence `<_H` on operations completed in `H ++ R`.
* `Cslib.Distributed.ConcurrentObjects.acyclic_sup_of_isIntervalOrder`: algebraic interval-order
  cycle-collapse theorem showing the union of per-object strict orders with a compatible interval
  order is `Relation.Acyclic`.
* `Cslib.Distributed.ConcurrentObjects.IsLinearizable.objSubhistory`,
  `Cslib.Distributed.ConcurrentObjects.isLinearizable_iff_forall_obj`: **Herlihy–Wing Theorem 1
  (Locality)** — a well-formed history `H` is linearizable if and only if for every object `x`, its
  object subhistory `History.objSubhistory H x` is linearizable.

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

open Relation

/-- Appending response events does not alter `<_H` on operations completed in `H ++ R`. -/
theorem History.prec_append_resp_iff {P Obj : Type*} {Op Resp : Obj → Type*} [DecidableEq P]
    {H R : History P Op Resp} (hwf : History.WellFormed H) (hresp : History.IsRespList R)
    (hwf_ext : History.WellFormed (H ++ R)) {e₀ e₁ : OpId P}
    (hc₁ : History.IsCompletedOp (H ++ R) e₁) :
    History.prec (H ++ R) e₀ e₁ ↔ History.prec H e₀ e₁ := by
  have hresp_p : ∀ p, History.IsRespList (History.procSubhistory R p) :=
    fun p e hm => hresp e (List.mem_filter.mp hm).1
  have hinv_in_H : 2 * e₁.idx < (History.procSubhistory H e₁.proc).length := by
    have hlen : 2 * e₁.idx + 1 < (History.procSubhistory (H ++ R) e₁.proc).length :=
      (History.isCompletedOp_iff_lt_length _ _).mp hc₁
    rw [History.procSubhistory_append, List.length_append] at hlen
    have hseq_ext := hwf_ext e₁.proc
    rw [History.procSubhistory_append] at hseq_ext
    rcases History.isRespList_le_one_of_isSequential (hwf e₁.proc) (hresp_p e₁.proc) hseq_ext with
      hnil | ⟨_, _, _, _, _, _, hR⟩
    · rw [hnil, List.length_nil] at hlen; omega
    · rw [hR, List.length_singleton] at hlen; omega
  have hinv_eq : History.invPos (H ++ R) e₁ = History.invPos H e₁ :=
    History.nthProcPos_append_left R hinv_in_H
  constructor
  · rintro ⟨r, i, hr, hi, hri⟩
    rw [hinv_eq] at hi
    obtain ⟨hi_lt, _⟩ := History.nthProcPos_lt_length hi
    exact ⟨r, i, History.nthProcPos_of_append_lt hr (by omega), hi, hri⟩
  · rintro ⟨r, i, hr, hi, hri⟩
    have hr_in : 2 * e₀.idx + 1 < (History.procSubhistory H e₀.proc).length :=
      (History.nthProcPos_isSome_iff e₀.proc H (2 * e₀.idx + 1)).mp
        (by rw [← History.respPos, hr]; rfl)
    refine ⟨r, i, ?_, ?_, hri⟩
    · rw [History.respPos, History.nthProcPos_append_left R hr_in]; exact hr
    · rw [hinv_eq]; exact hi

/-! ### Interval-order acyclicity and finite topological sort -/

/-- **Algebraic interval-order cycle collapse** (core of [HerlihyWing1990], §3.1, Theorem 1,
p. 471): if `rt` is a `Relation.IsIntervalOrder` on `α`, `loc` only relates elements of the same
object (`obj a = obj b`), `loc` is a strict order (irreflexive and transitive), and `rt` restricted
to same-object pairs is contained in `loc`, then `loc ⊔ rt` is `Relation.Acyclic`. -/
theorem acyclic_sup_of_isIntervalOrder {α Obj : Type*} (obj : α → Obj)
    (loc rt : α → α → Prop)
    (hrt : IsIntervalOrder rt)
    (hloc_irrefl : ∀ a, ¬ loc a a)
    (hloc_trans : ∀ {a b c}, loc a b → loc b c → loc a c)
    (hloc_obj : ∀ {a b}, loc a b → obj a = obj b)
    (hrt_sub_loc : ∀ {a b}, obj a = obj b → rt a b → loc a b) :
    Acyclic (loc ⊔ rt) := by
  have hmid : ∀ {a b c d}, rt a b → loc b c → rt c d → rt a d := by
    intro a b c d hab hbc hcd
    rcases hrt.2 a b c d ⟨hab, hcd⟩ with had | hcb
    · exact had
    · exact False.elim (hloc_irrefl b (hloc_trans hbc (hrt_sub_loc (hloc_obj hbc).symm hcb)))
  have hrefl_trans : ∀ {a b c}, ReflGen loc a b → ReflGen loc b c → ReflGen loc a c := by
    intro a b c h₁ h₂
    cases h₁ with
    | refl => exact h₂
    | single h₁ =>
      cases h₂ with
      | refl => exact ReflGen.single h₁
      | single h₂ => exact ReflGen.single (hloc_trans h₁ h₂)
  have hcollapse : ∀ {x y}, TransGen (loc ⊔ rt) x y →
      loc x y ∨ ∃ u v, ReflGen loc x u ∧ rt u v ∧ ReflGen loc v y := by
    intro x y hxy
    induction hxy with
    | single hstep =>
      rcases hstep with hl | hr
      · exact Or.inl hl
      · exact Or.inr ⟨x, _, ReflGen.refl, hr, ReflGen.refl⟩
    | tail _ hstep ih =>
      rcases ih with hl | ⟨u, v, hxu, huv, hvy⟩
      · rcases hstep with hl₂ | hr₂
        · exact Or.inl (hloc_trans hl hl₂)
        · exact Or.inr ⟨_, _, ReflGen.single hl, hr₂, ReflGen.refl⟩
      · rcases hstep with hl₂ | hr₂
        · exact Or.inr ⟨u, v, hxu, huv, hrefl_trans hvy (ReflGen.single hl₂)⟩
        · cases hvy with
          | refl => exact Or.inr ⟨u, _, hxu, hrt.1.trans _ _ _ huv hr₂, ReflGen.refl⟩
          | single hv => exact Or.inr ⟨u, _, hxu, hmid huv hv hr₂, ReflGen.refl⟩
  refine ⟨fun x hxx => ?_⟩
  rcases hcollapse hxx with hl | ⟨u, v, hxu, huv, hvx⟩
  · exact hloc_irrefl x hl
  · cases hrefl_trans hvx hxu with
    | refl => exact hrt.1.irrefl u huv
    | single hvu => exact hloc_irrefl v (hloc_trans hvu (hrt_sub_loc (hloc_obj hvu).symm huv))

private theorem exists_minimal_of_acyclic {α : Type*} (R : α → α → Prop) (hacyc : Acyclic R)
    {elems : List α} (hne : elems ≠ []) :
    ∃ m ∈ elems, ∀ x ∈ elems, ¬ TransGen R x m := by
  classical
  have go : ∀ (k : ℕ) (pool : List α) (y : α), pool.length ≤ k →
      y ∈ pool → pool ⊆ elems → (∀ z ∈ elems, TransGen R z y → z ∈ pool) →
      ∃ m ∈ elems, ∀ x ∈ elems, ¬ TransGen R x m := by
    intro k
    induction k with
    | zero =>
      intro pool y hlen hy _ _
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hy
      exact False.elim (List.not_mem_nil hy)
    | succ k ih =>
      intro pool y hlen hy hsub hclosed
      by_cases hmin : ∀ x ∈ pool.erase y, ¬ TransGen R x y
      · refine ⟨y, hsub hy, fun x hx hxy => ?_⟩
        have hne_xy : x ≠ y := fun h => hacyc.irrefl y (h ▸ hxy)
        exact hmin x ((List.mem_erase_of_ne hne_xy).mpr (hclosed x hx hxy)) hxy
      · push Not at hmin
        obtain ⟨x, hx_er, hxy⟩ := hmin
        have hlen' : (pool.erase y).length < pool.length := by
          rw [List.length_erase_of_mem hy]
          exact Nat.sub_lt (List.length_pos_of_mem hy) Nat.one_pos
        refine ih (pool.erase y) x (by omega) hx_er (fun _ hw => hsub (List.mem_of_mem_erase hw))
          fun z hz hzx => ?_
        have hzy : TransGen R z y := hzx.trans hxy
        have hne_zy : z ≠ y := fun h => hacyc.irrefl y (h ▸ hzy)
        exact (List.mem_erase_of_ne hne_zy).mpr (hclosed z hz hzy)
  obtain ⟨y₀, hy₀⟩ := List.exists_mem_of_ne_nil elems hne
  exact go elems.length elems y₀ (Nat.le_refl _) hy₀ (fun _ h => h) (fun _ hz _ => hz)

/-- Finite topological sort: every duplicate-free list `elems` over an acyclic relation `R` admits a
permutation `order` in which every `R`-edge points strictly forward. -/
private theorem exists_topoSort_of_acyclic {α : Type*} {R : α → α → Prop}
    (hacyc : Acyclic R) {elems : List α} (hnodup : elems.Nodup) :
    ∃ order : List α, order.Perm elems ∧ order.Nodup ∧
      ∀ i j (hi : i < order.length) (hj : j < order.length),
        TransGen R order[i] order[j] → i < j := by
  classical
  have go : ∀ n (l : List α), l.length = n → l.Nodup →
      ∃ order : List α, order.Perm l ∧ order.Nodup ∧
        ∀ i j (hi : i < order.length) (hj : j < order.length),
          TransGen R order[i] order[j] → i < j := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      rw [List.length_eq_zero_iff.mp hl]
      exact ⟨[], List.Perm.nil, List.nodup_nil,
        fun _ _ hi => by simp only [List.length_nil] at hi; omega⟩
    | succ n ih =>
      intro l hl hnd
      have hne : l ≠ [] := fun h => by rw [h, List.length_nil] at hl; omega
      obtain ⟨m, hm, hmin⟩ := exists_minimal_of_acyclic R hacyc hne
      have hlen' : (l.erase m).length = n := by rw [List.length_erase_of_mem hm, hl]; omega
      obtain ⟨order', hperm', hnd', hord'⟩ := ih (l.erase m) hlen' (hnd.erase m)
      have hm_not : m ∉ order' := fun hmem => hnd.not_mem_erase (hperm'.subset hmem)
      have hperm : (m :: order').Perm l := (hperm'.cons m).trans (List.perm_cons_erase hm).symm
      refine ⟨m :: order', hperm, List.nodup_cons.mpr ⟨hm_not, hnd'⟩, ?_⟩
      intro i j hi hj hrel
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero] at hrel
        exact False.elim (hmin _ (hperm.subset (List.getElem_mem hi)) hrel)
      | succ j' =>
        cases i with
        | zero => omega
        | succ i' =>
          simp only [List.length_cons] at hi hj
          simp only [List.getElem_cons_succ] at hrel
          have := hord' i' j' (by omega) (by omega) hrel
          omega
  exact go elems.length elems rfl hnodup

/-! ### Per-object operation lifting -/

section LocalityInfrastructure

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- Position in `L` of the `n`-th event whose object is `x`. -/
private def nthObjPos [DecidableEq Obj] (x : Obj) (L : History P Op Resp) (n : ℕ) : Option ℕ :=
  List.nthFilterPos (fun e => decide (e.obj = x)) L n

private theorem nthObjPos_nil [DecidableEq Obj] (x : Obj) (n : ℕ) :
    nthObjPos x ([] : History P Op Resp) n = none :=
  rfl

private theorem nthObjPos_cons_zero [DecidableEq Obj] (x : Obj) (e : Event P Op Resp)
    (rest : History P Op Resp) :
    nthObjPos x (e :: rest) 0 =
      if e.obj = x then some 0 else (nthObjPos x rest 0).map (· + 1) := by
  dsimp only [nthObjPos]
  by_cases h : e.obj = x
  · simp only [h, ↓reduceIte]
    exact List.nthFilterPos_cons_zero_of_true (pred := fun a => decide (a.obj = x)) (a := e) rest
      (decide_eq_true h)
  · simp only [h, ↓reduceIte]
    exact List.nthFilterPos_cons_of_false (pred := fun a => decide (a.obj = x)) (a := e) rest 0
      (decide_eq_false h)

private theorem nthObjPos_cons_succ [DecidableEq Obj] (x : Obj) (e : Event P Op Resp)
    (rest : History P Op Resp) (n : ℕ) :
    nthObjPos x (e :: rest) (n + 1) =
      if e.obj = x then (nthObjPos x rest n).map (· + 1)
      else (nthObjPos x rest (n + 1)).map (· + 1) := by
  dsimp only [nthObjPos]
  by_cases h : e.obj = x
  · simp only [h, ↓reduceIte]
    exact List.nthFilterPos_cons_succ_of_true (pred := fun a => decide (a.obj = x)) (a := e) rest n
      (decide_eq_true h)
  · simp only [h, ↓reduceIte]
    exact List.nthFilterPos_cons_of_false (pred := fun a => decide (a.obj = x)) (a := e) rest
      (n + 1) (decide_eq_false h)

private theorem nthObjPos_cons_ne [DecidableEq Obj] (x : Obj) (e : Event P Op Resp)
    (rest : History P Op Resp) (n : ℕ) (h : e.obj ≠ x) :
    nthObjPos x (e :: rest) n = (nthObjPos x rest n).map (· + 1) := by
  cases n <;> simp only [nthObjPos_cons_zero, nthObjPos_cons_succ, h, ↓reduceIte]

/-- Number of events on object `x` strictly preceding index `pos` in `M`. -/
private def objProjPos [DecidableEq Obj] (x : Obj) : History P Op Resp → ℕ → ℕ
  | [], _ => 0
  | _, 0 => 0
  | e :: rest, pos + 1 =>
    if e.obj = x then objProjPos x rest pos + 1 else objProjPos x rest pos

private theorem objProjPos_lt_iff [DecidableEq Obj] (x : Obj) :
    ∀ {M : History P Op Resp} {pos₁ pos₂ : ℕ},
      pos₁ < M.length → pos₂ < M.length → M[pos₁]?.map Event.obj = some x →
      (objProjPos x M pos₁ < objProjPos x M pos₂ ↔ pos₁ < pos₂)
  | [], _, _, h₁, _, _ => by simp only [List.length_nil] at h₁; omega
  | _ :: _, 0, 0, _, _, _ => by dsimp only [objProjPos]; simp only [Nat.lt_irrefl]
  | e :: rest, 0, p₂ + 1, _, _, hobj => by
    simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hobj
    dsimp only [objProjPos]
    simp only [hobj, ↓reduceIte]
    omega
  | _ :: _, _ + 1, 0, _, _, _ => by dsimp only [objProjPos]; omega
  | e :: rest, p₁ + 1, p₂ + 1, h₁, h₂, hobj => by
    simp only [List.length_cons] at h₁ h₂
    simp only [List.getElem?_cons_succ] at hobj
    have ih := objProjPos_lt_iff x (pos₁ := p₁) (pos₂ := p₂) (by omega) (by omega) hobj
    dsimp only [objProjPos]
    by_cases hex : e.obj = x <;> simp only [hex, ↓reduceIte] <;> omega

private theorem nthObjPos_isSome_iff [DecidableEq Obj] (x : Obj) (L : History P Op Resp) (n : ℕ) :
    (nthObjPos x L n).isSome = true ↔ n < (History.objSubhistory L x).length :=
  List.nthFilterPos_isSome_iff (fun e : Event P Op Resp => decide (e.obj = x)) L n

private theorem nthObjPos_lt_length [DecidableEq Obj] {x : Obj} {L : History P Op Resp}
    {n m : ℕ} (h : nthObjPos x L n = some m) : m < L.length ∧ L[m]?.map Event.obj = some x := by
  obtain ⟨hlt, _, hpr⟩ := List.nthFilterPos_lt_length h
  refine ⟨hlt, ?_⟩
  cases hget : L[m]? with
  | none =>
    rw [hget] at hpr
    simp only [Option.map_none, reduceCtorEq] at hpr
  | some a =>
    rw [hget] at hpr
    simpa only [Option.map_some, Option.some.injEq, decide_eq_true_eq] using hpr

private theorem nthObjPos_pair_of_isSequential [DecidableEq Obj] {x : Obj}
    {L : History P Op Resp} (hseq : History.IsSequential L) {k_x m : ℕ}
    (h : nthObjPos x L (2 * k_x + 1) = some m) :
    ∃ k : ℕ, m = 2 * k + 1 ∧ nthObjPos x L (2 * k_x) = some (2 * k) := by
  match L with
  | [] => simp only [nthObjPos_nil, reduceCtorEq] at h
  | [.inv p y op] =>
    by_cases hyx : y = x <;>
      simp only [nthObjPos_cons_succ, Event.obj_inv, hyx, ↓reduceIte, nthObjPos_nil,
        Option.map_none, reduceCtorEq] at h
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    by_cases hxx : x₁ = x
    · cases k_x with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add, nthObjPos_cons_succ, nthObjPos_cons_zero,
          Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte, Option.map_some, Option.some.injEq] at h
        refine ⟨0, h.symm, ?_⟩
        simp only [Nat.mul_zero, nthObjPos_cons_zero, Event.obj_inv, hxx, ↓reduceIte]
      | succ k_x' =>
        have hstep₁ : 2 * (k_x' + 1) + 1 = (2 * k_x' + 1) + 1 + 1 := by omega
        have hstep₀ : 2 * (k_x' + 1) = (2 * k_x') + 1 + 1 := by omega
        simp only [hstep₁, nthObjPos_cons_succ, Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte,
          Option.map_eq_some_iff] at h
        obtain ⟨_, ⟨m', hm', rfl⟩, rfl⟩ := h
        obtain ⟨k', rfl, hk₀⟩ := nthObjPos_pair_of_isSequential hrest hm'
        refine ⟨k' + 1, by omega, ?_⟩
        simp only [hstep₀, nthObjPos_cons_succ, Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte, hk₀,
          Option.map_some]
        exact congrArg some (by omega)
    · simp only [nthObjPos_cons_ne x (.inv p₁ x₁ op) _ _ hxx,
        nthObjPos_cons_ne x (.resp p₁ x₁ res) _ _ hxx, Option.map_eq_some_iff] at h
      obtain ⟨_, ⟨m', hm', rfl⟩, rfl⟩ := h
      obtain ⟨k', rfl, hk₀⟩ := nthObjPos_pair_of_isSequential hrest hm'
      refine ⟨k' + 1, by omega, ?_⟩
      simp only [nthObjPos_cons_ne x (.inv p₁ x₁ op) _ _ hxx,
        nthObjPos_cons_ne x (.resp p₁ x₁ res) _ _ hxx, hk₀, Option.map_some]
      exact congrArg some (by omega)

private theorem nthObjPos_complete_eq [DecidableEq P] [DecidableEq Obj] {x : Obj}
    {L : History P Op Resp} (hseq : History.IsSequential L) {n m : ℕ}
    (h : nthObjPos x (History.complete L) n = some m) :
    nthObjPos x L n = some m := by
  match L with
  | [] => exact h
  | [.inv p y op] =>
    simp only [History.complete, List.any_nil, Bool.false_eq_true, ↓reduceIte, nthObjPos_nil,
      reduceCtorEq] at h
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    simp only [History.complete, List.any_cons, Event.proc_resp, decide_true, Bool.true_or,
      ↓reduceIte] at h
    by_cases hxx : x₁ = x
    · rcases n with _ | _ | n₂
      · simp only [nthObjPos_cons_zero, Event.obj_inv, hxx, ↓reduceIte] at h ⊢
        exact h
      · simp only [nthObjPos_cons_succ, nthObjPos_cons_zero, Event.obj_inv, Event.obj_resp, hxx,
          ↓reduceIte] at h ⊢
        exact h
      · simp only [nthObjPos_cons_succ, Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte,
          Option.map_eq_some_iff] at h ⊢
        obtain ⟨_, ⟨m₂, hm₂, rfl⟩, rfl⟩ := h
        exact ⟨m₂ + 1, ⟨m₂, nthObjPos_complete_eq hrest hm₂, rfl⟩, rfl⟩
    · simp only [nthObjPos_cons_ne x (.inv p₁ x₁ op) _ _ hxx,
        nthObjPos_cons_ne x (.resp p₁ x₁ res) _ _ hxx, Option.map_eq_some_iff] at h ⊢
      obtain ⟨_, ⟨m₂, hm₂, rfl⟩, rfl⟩ := h
      exact ⟨m₂ + 1, ⟨m₂, nthObjPos_complete_eq hrest hm₂, rfl⟩, rfl⟩

private theorem nthObjPos_eq_complete_of_odd [DecidableEq P] [DecidableEq Obj] {x : Obj}
    {L : History P Op Resp} (hseq : History.IsSequential L) {k_x : ℕ} :
    nthObjPos x L (2 * k_x + 1) = nthObjPos x (History.complete L) (2 * k_x + 1) ∧
      (∀ m, nthObjPos x L (2 * k_x + 1) = some m →
        nthObjPos x L (2 * k_x) = nthObjPos x (History.complete L) (2 * k_x)) := by
  match L with
  | [] =>
    exact ⟨rfl, fun _ hm => by simp only [nthObjPos_nil, reduceCtorEq] at hm⟩
  | [.inv p y op] =>
    by_cases hyx : y = x <;>
      exact ⟨by simp only [History.complete, List.any_nil, Bool.false_eq_true, ↓reduceIte,
          nthObjPos_cons_succ, Event.obj_inv, hyx, nthObjPos_nil, Option.map_none],
        fun _ hm => by simp only [nthObjPos_cons_succ, Event.obj_inv, hyx, ↓reduceIte,
          nthObjPos_nil, Option.map_none, reduceCtorEq] at hm⟩
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    simp only [History.complete, List.any_cons, Event.proc_resp, decide_true, Bool.true_or,
      ↓reduceIte]
    by_cases hxx : x₁ = x
    · cases k_x with
      | zero =>
        refine ⟨?_, fun _ _ => ?_⟩
        · simp only [Nat.mul_zero, Nat.zero_add, nthObjPos_cons_succ, nthObjPos_cons_zero,
            Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte]
        · simp only [Nat.mul_zero, nthObjPos_cons_zero, Event.obj_inv, hxx, ↓reduceIte]
      | succ k_x' =>
        obtain ⟨ih₁, ih₀⟩ := nthObjPos_eq_complete_of_odd (x := x) hrest (k_x := k_x')
        have hstep₁ : 2 * (k_x' + 1) + 1 = (2 * k_x' + 1) + 1 + 1 := by omega
        have hstep₀ : 2 * (k_x' + 1) = (2 * k_x') + 1 + 1 := by omega
        rw [hstep₁, hstep₀]
        refine ⟨?_, fun m hm => ?_⟩
        · simp only [nthObjPos_cons_succ, Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte, ih₁]
        · simp only [nthObjPos_cons_succ, Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte,
            Option.map_eq_some_iff] at hm
          obtain ⟨_, ⟨m₂, hm₂, rfl⟩, rfl⟩ := hm
          simp only [nthObjPos_cons_succ, Event.obj_inv, Event.obj_resp, hxx, ↓reduceIte,
            ih₀ m₂ hm₂]
    · obtain ⟨ih₁, ih₀⟩ := nthObjPos_eq_complete_of_odd (x := x) hrest (k_x := k_x)
      simp only [nthObjPos_cons_ne x (.inv p₁ x₁ op) _ _ hxx,
        nthObjPos_cons_ne x (.resp p₁ x₁ res) _ _ hxx, ih₁, Option.map_eq_some_iff, true_and]
      rintro _ ⟨_, ⟨m₂, hm₂, rfl⟩, rfl⟩
      rw [ih₀ m₂ (ih₁.trans hm₂)]

private theorem nthProcPos_cons_of_ne [DecidableEq P] {p : P} {e : Event P Op Resp}
    (rest : History P Op Resp) (n : ℕ) (h : e.proc ≠ p) :
    History.nthProcPos p (e :: rest) n = (History.nthProcPos p rest n).map (· + 1) :=
  List.nthFilterPos_cons_of_false rest n (decide_eq_false h)

private theorem nthProcPos_objSubhistory_eq [DecidableEq P] [DecidableEq Obj]
    {p : P} {x : Obj} :
    ∀ {M : History P Op Resp} {n_x n pos : ℕ},
      nthObjPos x (History.procSubhistory M p) n_x = some n →
      History.nthProcPos p M n = some pos →
      M[pos]?.map Event.obj = some x ∧
        History.nthProcPos p (History.objSubhistory M x) n_x = some (objProjPos x M pos)
  | [], _, _, _, hobj, _ => by
    simp only [History.procSubhistory_nil, nthObjPos_nil, reduceCtorEq] at hobj
  | e :: rest, n_x, n, pos, hobj, hproc => by
    by_cases hep : e.proc = p
    · simp only [History.procSubhistory_cons, hep, ↓reduceIte] at hobj
      by_cases hex : e.obj = x
      · cases n_x with
        | zero =>
          simp only [nthObjPos_cons_zero, hex, ↓reduceIte, Option.some.injEq] at hobj
          subst hobj
          simp only [History.nthProcPos, List.nthFilterPos, hep, decide_true, ↓reduceIte,
            Option.some.injEq] at hproc
          subst hproc
          dsimp only [objProjPos]
          simp only [List.getElem?_cons_zero, Option.map_some, hex, History.objSubhistory_cons,
            ↓reduceIte, History.nthProcPos, List.nthFilterPos, hep, decide_true, and_self]
        | succ n_x' =>
          simp only [nthObjPos_cons_succ, hex, ↓reduceIte, Option.map_eq_some_iff] at hobj
          obtain ⟨n', hn', rfl⟩ := hobj
          simp only [History.nthProcPos, List.nthFilterPos, hep, decide_true, ↓reduceIte,
            Option.map_eq_some_iff] at hproc
          obtain ⟨pos', hpos', rfl⟩ := hproc
          obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hn' hpos'
          rw [History.nthProcPos] at hm_pos
          dsimp only [objProjPos]
          simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
            History.nthProcPos, List.nthFilterPos, hep, decide_true, hm_pos, Option.map_some,
            and_self]
      · rw [nthObjPos_cons_ne x e _ n_x hex, Option.map_eq_some_iff] at hobj
        obtain ⟨n', hn', rfl⟩ := hobj
        simp only [History.nthProcPos, List.nthFilterPos, hep, decide_true, ↓reduceIte,
          Option.map_eq_some_iff] at hproc
        obtain ⟨pos', hpos', rfl⟩ := hproc
        obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hn' hpos'
        dsimp only [objProjPos]
        simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
          hm_pos, and_self]
    · simp only [History.procSubhistory_cons, hep, ↓reduceIte] at hobj
      rw [nthProcPos_cons_of_ne rest n hep, Option.map_eq_some_iff] at hproc
      obtain ⟨pos', hpos', rfl⟩ := hproc
      obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hobj hpos'
      dsimp only [objProjPos]
      by_cases hex : e.obj = x
      · simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
          nthProcPos_cons_of_ne _ n_x hep, hm_pos, Option.map_some, and_self]
      · simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
          hm_pos, and_self]

/-- Lift a local operation identifier `e_x` of `M | x` to its global `OpId P` in `M`, computed from
`complete (M | e_x.proc)` so equivalent completions induce the identical lift. -/
private def liftOp [DecidableEq P] [DecidableEq Obj] (M : History P Op Resp) (x : Obj)
    (e_x : OpId P) : OpId P :=
  match nthObjPos x (History.complete (History.procSubhistory M e_x.proc)) (2 * e_x.idx) with
  | some n => ⟨e_x.proc, n / 2⟩
  | none => e_x

private theorem liftOp_eq_of_equivalent_complete [DecidableEq P] [DecidableEq Obj]
    {M₁ M₂ : History P Op Resp} (heq : History.Equivalent (History.complete M₁) M₂)
    (hseq₂ : History.IsSequential M₂) (hwf₁ : History.WellFormed M₁) (x : Obj) (e_x : OpId P) :
    liftOp M₁ x e_x = liftOp M₂ x e_x := by
  have hev₂ := History.even_length_of_equivalent_complete hwf₁ hseq₂ heq
  have hcomp_M₂ : History.complete (History.procSubhistory M₂ e_x.proc) =
      History.procSubhistory M₂ e_x.proc := by
    rw [← History.procSubhistory_complete,
      History.complete_eq_self_of_isSequential_even hseq₂ hev₂]
  have hp := heq e_x.proc
  rw [History.procSubhistory_complete] at hp
  dsimp only [liftOp]
  rw [hcomp_M₂, hp]

private theorem liftOp_spec [DecidableEq P] [DecidableEq Obj] {M : History P Op Resp}
    (hwf : History.WellFormed M) {x : Obj} {e_x : OpId P}
    (hc : History.IsCompletedOp (History.objSubhistory M x) e_x) :
    History.IsCompletedOp M (liftOp M x e_x) ∧
      (liftOp M x e_x).proc = e_x.proc ∧
      (∃ i, History.invPos M (liftOp M x e_x) = some i ∧ M[i]?.map Event.obj = some x ∧
        History.invPos (History.objSubhistory M x) e_x = some (objProjPos x M i)) ∧
      (∃ r, History.respPos M (liftOp M x e_x) = some r ∧ M[r]?.map Event.obj = some x ∧
        History.respPos (History.objSubhistory M x) e_x = some (objProjPos x M r)) := by
  have hlen_x : 2 * e_x.idx + 1 <
      (History.objSubhistory (History.procSubhistory M e_x.proc) x).length := by
    rw [← History.procSubhistory_objSubhistory_comm]
    exact (History.isCompletedOp_iff_lt_length _ _).mp hc
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp ((nthObjPos_isSome_iff x _ _).mpr hlen_x)
  obtain ⟨k, rfl, hk₀⟩ := nthObjPos_pair_of_isSequential (hwf e_x.proc) hm
  obtain ⟨_, heq_even_fn⟩ := nthObjPos_eq_complete_of_odd (x := x) (hwf e_x.proc) (k_x := e_x.idx)
  have hk₀_comp :
      nthObjPos x (History.complete (History.procSubhistory M e_x.proc)) (2 * e_x.idx) =
        some (2 * k) := by
    rw [← heq_even_fn (2 * k + 1) hm]; exact hk₀
  have hlift : liftOp M x e_x = ⟨e_x.proc, k⟩ := by
    dsimp only [liftOp]
    rw [hk₀_comp]
    ext
    · rfl
    · dsimp only; omega
  rw [hlift]
  obtain ⟨hm_lt, _⟩ := nthObjPos_lt_length hm
  have hc_M : History.IsCompletedOp M ⟨e_x.proc, k⟩ :=
    (History.isCompletedOp_iff_lt_length M ⟨e_x.proc, k⟩).mpr hm_lt
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hc_M
  obtain ⟨i, hi, _⟩ := History.invPos_of_respPos hr
  obtain ⟨hi_obj, hi_proj⟩ := nthProcPos_objSubhistory_eq hk₀ hi
  obtain ⟨hr_obj, hr_proj⟩ := nthProcPos_objSubhistory_eq hm hr
  exact ⟨hc_M, rfl, ⟨i, hi, hi_obj, hi_proj⟩, ⟨r, hr, hr_obj, hr_proj⟩⟩

private theorem liftOp_inj_of_isCompletedOp [DecidableEq P] [DecidableEq Obj]
    {M : History P Op Resp} (hwf : History.WellFormed M) {x : Obj} {u₁ u₂ : OpId P}
    (hc₁ : History.IsCompletedOp (History.objSubhistory M x) u₁)
    (hc₂ : History.IsCompletedOp (History.objSubhistory M x) u₂)
    (heq : liftOp M x u₁ = liftOp M x u₂) : u₁ = u₂ := by
  obtain ⟨_, hp₁, ⟨i₁, hi₁, _, hproj₁⟩, _⟩ := liftOp_spec hwf hc₁
  obtain ⟨_, hp₂, ⟨i₂, hi₂, _, hproj₂⟩, _⟩ := liftOp_spec hwf hc₂
  have hp_eq : u₁.proc = u₂.proc := hp₁.symm.trans ((congrArg OpId.proc heq).trans hp₂)
  rw [heq, hi₂] at hi₁
  injection hi₁ with hi_eq
  subst hi_eq
  dsimp only [History.invPos, History.nthProcPos] at hproj₁ hproj₂
  rw [hp_eq] at hproj₁
  have h2eq := List.nthFilterPos_inj hproj₁ hproj₂
  ext
  · exact hp_eq
  · omega

private theorem prec_objSubhistory_iff [DecidableEq P] [DecidableEq Obj] {M : History P Op Resp}
    (hwf : History.WellFormed M) {x : Obj} {e₀ e₁ : OpId P}
    (hc₀ : History.IsCompletedOp (History.objSubhistory M x) e₀)
    (hc₁ : History.IsCompletedOp (History.objSubhistory M x) e₁) :
    History.prec (History.objSubhistory M x) e₀ e₁ ↔
      History.prec M (liftOp M x e₀) (liftOp M x e₁) := by
  obtain ⟨_, _, _, ⟨r, hr, hr_obj, hr_proj⟩⟩ := liftOp_spec hwf hc₀
  obtain ⟨_, _, ⟨i, hi, _, hi_proj⟩, _⟩ := liftOp_spec hwf hc₁
  obtain ⟨hr_lt, _⟩ := History.nthProcPos_lt_length hr
  obtain ⟨hi_lt, _⟩ := History.nthProcPos_lt_length hi
  have hlt_iff := objProjPos_lt_iff x hr_lt hi_lt hr_obj
  constructor
  · rintro ⟨rx, ix, hrx, hix, hlt⟩
    rw [hr_proj] at hrx; rw [hi_proj] at hix
    injection hrx with hrx'; injection hix with hix'
    subst hrx' hix'
    exact ⟨r, i, hr, hi, hlt_iff.mp hlt⟩
  · rintro ⟨r', i', hr', hi', hlt⟩
    rw [hr] at hr'; rw [hi] at hi'
    injection hr' with hr''; injection hi' with hi''
    subst hr'' hi''
    exact ⟨objProjPos x M r, objProjPos x M i, hr_proj, hi_proj, hlt_iff.mpr hlt⟩

private def countObjCalls [DecidableEq Obj] (x : Obj) (calls : List (OpCall P Op Resp)) : ℕ :=
  (calls.filter fun c => decide (c.obj = x)).length

private theorem nthObjPos_flatMap_toEvents [DecidableEq Obj] (calls : List (OpCall P Op Resp))
    (k : ℕ) (hk : k < calls.length) :
    nthObjPos calls[k].obj (calls.flatMap OpCall.toEvents)
        (2 * countObjCalls calls[k].obj (calls.take k)) = some (2 * k) ∧
      nthObjPos calls[k].obj (calls.flatMap OpCall.toEvents)
        (2 * countObjCalls calls[k].obj (calls.take k) + 1) = some (2 * k + 1) :=
  nthFilterPos_flatMap_toEvents
    (fun c => decide (c.obj = calls[k].obj))
    (fun e => decide (e.obj = calls[k].obj))
    (fun _ => rfl) (fun _ => rfl) calls k hk (decide_eq_true rfl)

private theorem objSubhistory_flatMap_of_nodup [DecidableEq Obj] {l : List Obj} (hnd : l.Nodup)
    (f : Obj → History P Op Resp) (hobj : ∀ y ∈ l, ∀ e ∈ f y, e.obj = y) (x : Obj) :
    History.objSubhistory (l.flatMap f) x = if x ∈ l then f x else [] := by
  induction l with
  | nil => simp only [List.flatMap_nil, History.objSubhistory_nil, List.not_mem_nil, ↓reduceIte]
  | cons y rest ih =>
    obtain ⟨hynot, hnd_rest⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, History.objSubhistory_append, List.mem_cons]
    have ih' := ih hnd_rest (fun z hz => hobj z (List.mem_cons_of_mem _ hz))
    by_cases hxy : x = y
    · subst hxy
      simp only [true_or, ↓reduceIte, ih', hynot, List.append_nil]
      exact History.objSubhistory_eq_self_of_forall_obj (hobj x List.mem_cons_self)
    · have hfy : History.objSubhistory (f y) x = [] :=
        History.objSubhistory_eq_nil_of_forall_ne fun e he => by
          rw [hobj y List.mem_cons_self e he]; exact Ne.symm hxy
      simp only [hxy, false_or, hfy, List.nil_append, ih']

private theorem procSubhistory_flatMap_eq_single [DecidableEq P] [DecidableEq Obj]
    {l : List Obj} (hnd : l.Nodup) (f : Obj → History P Op Resp) (p : P) (x₀ : Obj)
    (hother : ∀ y ∈ l, y ≠ x₀ → History.procSubhistory (f y) p = []) :
    History.procSubhistory (l.flatMap f) p =
      if x₀ ∈ l then History.procSubhistory (f x₀) p else [] := by
  induction l with
  | nil => simp only [List.flatMap_nil, History.procSubhistory_nil, List.not_mem_nil, ↓reduceIte]
  | cons y rest ih =>
    obtain ⟨hynot, hnd_rest⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, History.procSubhistory_append, List.mem_cons]
    have ih' := ih hnd_rest (fun z hz => hother z (List.mem_cons_of_mem _ hz))
    by_cases hxy : x₀ = y
    · subst hxy
      simp only [true_or, ↓reduceIte, ih', hynot, List.append_nil]
    · rw [hother y List.mem_cons_self (Ne.symm hxy), List.nil_append, ih']
      simp only [hxy, false_or]

end LocalityInfrastructure

/-! ### Herlihy–Wing Theorem 1 (Locality) -/

/-- Restricting a linearizable history `H` to any single object `x` preserves linearizability
("only if" direction of [HerlihyWing1990], §3.1, Theorem 1, p. 470; [SelaHerlihyPetrank2021], §5.2,
Theorem 5.1, p. 7). -/
theorem IsLinearizable.objSubhistory {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {spec : ∀ x, SeqSpec P Op Resp x}
    {H : History P Op Resp} (hlin : IsLinearizable spec H) (x : Obj) :
    IsLinearizable spec (History.objSubhistory H x) := by
  obtain ⟨H', ⟨R, hresp, rfl, hwf'⟩, S, hseqS, hlegS, heqS, hprecS⟩ := hlin
  have hwfH : History.WellFormed H := fun p => by
    have hp := hwf' p
    rw [History.procSubhistory_append] at hp
    exact History.isSequential_append_left hp
  let R_x := History.objSubhistory R x
  have hresp_x : History.IsRespList R_x := fun e hm => hresp e (List.mem_filter.mp hm).1
  have hwf'_x : History.WellFormed (History.objSubhistory H x ++ R_x) := by
    rw [← History.objSubhistory_append]
    exact hwf'.objSubhistory x
  refine ⟨History.objSubhistory H x ++ R_x, ⟨R_x, hresp_x, rfl, hwf'_x⟩,
    History.objSubhistory S x, History.isSequential_objSubhistory hseqS x, ?_, ?_, ?_⟩
  · intro y
    by_cases hxy : x = y
    · subst hxy
      rw [History.objSubhistory_idem]
      exact hlegS x
    · rw [History.objSubhistory_of_ne S hxy]
      exact (spec y).nil_mem
  · rw [← History.objSubhistory_append, History.complete_objSubhistory hwf' x]
    exact heqS.objSubhistory x
  · intro e₀ e₁ hc₀ hc₁ hprec_x
    rw [← History.objSubhistory_append] at hc₀ hc₁
    have h₁ : History.prec (History.objSubhistory (H ++ R) x) e₀ e₁ := by
      rw [History.objSubhistory_append] at hc₁ ⊢
      exact (History.prec_append_resp_iff (hwfH.objSubhistory x) hresp_x hwf'_x hc₁).mpr hprec_x
    have h₂ : History.prec (H ++ R) (liftOp (H ++ R) x e₀) (liftOp (H ++ R) x e₁) :=
      (prec_objSubhistory_iff hwf' hc₀ hc₁).mp h₁
    obtain ⟨hc₀_HR, _⟩ := liftOp_spec hwf' hc₀
    obtain ⟨hc₁_HR, _⟩ := liftOp_spec hwf' hc₁
    have h₄ : History.prec S (liftOp (H ++ R) x e₀) (liftOp (H ++ R) x e₁) :=
      hprecS _ _ hc₀_HR hc₁_HR
        ((History.prec_append_resp_iff hwfH hresp hwf' hc₁_HR).mp h₂)
    rw [liftOp_eq_of_equivalent_complete heqS hseqS hwf' x e₀,
      liftOp_eq_of_equivalent_complete heqS hseqS hwf' x e₁] at h₄
    have h_eq_x : History.Equivalent
        (History.complete (History.objSubhistory (H ++ R) x)) (History.objSubhistory S x) := by
      rw [History.complete_objSubhistory hwf' x]
      exact heqS.objSubhistory x
    have hc_Sx : ∀ e, History.IsCompletedOp (History.objSubhistory (H ++ R) x) e →
        History.IsCompletedOp (History.objSubhistory S x) e := fun e hc =>
      (h_eq_x.isCompletedOp_iff e).mp
        ((History.isCompletedOp_complete_iff (hwf'.objSubhistory x) e).mpr hc)
    have hwfS : History.WellFormed S := by
      obtain ⟨cs, rfl⟩ := History.exists_calls_of_isSequential_even hseqS
        (History.even_length_of_equivalent_complete hwf' hseqS heqS)
      exact History.wellFormed_flatMap_toEvents cs
    exact (prec_objSubhistory_iff hwfS (hc_Sx e₀ hc₀) (hc_Sx e₁ hc₁)).mpr h₄

private theorem exists_normalized_obj_linearization {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {spec : ∀ x, SeqSpec P Op Resp x}
    {H : History P Op Resp} (hwf : History.WellFormed H)
    (hall : ∀ x, IsLinearizable spec (History.objSubhistory H x)) (x : Obj) :
    ∃ (Rx Sx : History P Op Resp),
      History.IsRespList Rx ∧
      (∀ e ∈ Rx, e.obj = x) ∧
      (x ∉ H.map Event.obj → Rx = []) ∧
      History.WellFormed (History.objSubhistory H x ++ Rx) ∧
      History.IsSequential Sx ∧
      Sx ∈ (spec x).allowed ∧
      History.Equivalent (History.complete (History.objSubhistory H x ++ Rx)) Sx ∧
      (∀ e₀ e₁, History.IsCompletedOp (History.objSubhistory H x ++ Rx) e₀ →
        History.IsCompletedOp (History.objSubhistory H x ++ Rx) e₁ →
        History.prec (History.objSubhistory H x) e₀ e₁ → History.prec Sx e₀ e₁) := by
  by_cases hx_mem : x ∈ H.map Event.obj
  · obtain ⟨H'_x, ⟨Rx, hresp_x, rfl, hwf'_x⟩, Sx, hseq_x, hleg_x, heq_x, hprec_x⟩ := hall x
    have hRx_obj : ∀ e ∈ Rx, e.obj = x := by
      intro e he
      have hp_mem : e ∈ History.procSubhistory Rx e.proc :=
        List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩
      have hseq_ext := hwf'_x e.proc
      rw [History.procSubhistory_append] at hseq_ext
      have hresp_p : History.IsRespList (History.procSubhistory Rx e.proc) :=
        fun a ha => hresp_x a (List.mem_filter.mp ha).1
      rcases History.isRespList_le_one_of_isSequential ((hwf.objSubhistory x) e.proc) hresp_p
        hseq_ext with hnil | ⟨_, q, y, op, _, hL, hR⟩
      · rw [hnil] at hp_mem; exact False.elim (List.not_mem_nil hp_mem)
      · rw [hR, List.mem_singleton] at hp_mem
        have hmem_p :
            Event.inv q y op ∈ History.procSubhistory (History.objSubhistory H x) e.proc := by
          rw [hL]; exact List.mem_append_right _ List.mem_cons_self
        have hyx : y = x :=
          of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp hmem_p).1).2
        rw [hp_mem, Event.obj_resp, hyx]
    have hSx_obj : ∀ e ∈ Sx, e.obj = x := by
      intro e he
      have hp_mem : e ∈ History.procSubhistory Sx e.proc :=
        List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩
      rw [← heq_x e.proc] at hp_mem
      rcases List.mem_append.mp (History.mem_of_mem_complete (List.mem_filter.mp hp_mem).1) with
        hH | hR
      · exact of_decide_eq_true (List.mem_filter.mp hH).2
      · exact hRx_obj e hR
    have hSx_allowed : Sx ∈ (spec x).allowed := by
      have h := hleg_x x
      rwa [History.objSubhistory_eq_self_of_forall_obj hSx_obj] at h
    exact ⟨Rx, Sx, hresp_x, hRx_obj, fun hnot => absurd hx_mem hnot,
      hwf'_x, hseq_x, hSx_allowed, heq_x, hprec_x⟩
  · have hHx_nil : History.objSubhistory H x = [] :=
      History.objSubhistory_eq_nil_of_forall_ne fun e he h =>
        hx_mem (List.mem_map.mpr ⟨e, he, h⟩)
    refine ⟨[], [], fun _ hm => False.elim (List.not_mem_nil hm),
      fun _ hm => False.elim (List.not_mem_nil hm), fun _ => rfl, ?_, trivial,
      (spec x).nil_mem, ?_, ?_⟩
    · rw [hHx_nil, List.nil_append]; exact History.wellFormed_nil
    · rw [hHx_nil, List.nil_append, History.complete_nil]; exact History.Equivalent.refl []
    · intro e₀ _ hc₀ _ _
      rw [hHx_nil, List.nil_append, History.isCompletedOp_iff_lt_length,
        History.procSubhistory_nil, List.length_nil] at hc₀
      omega

private theorem wellFormed_append_flatMap_resp {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {H : History P Op Resp} (hwf : History.WellFormed H)
    {objs : List Obj} (hobjs_nd : objs.Nodup) (Rx : Obj → History P Op Resp)
    (hRx_resp : ∀ x, History.IsRespList (Rx x))
    (hRx_obj : ∀ x, ∀ e ∈ Rx x, e.obj = x)
    (hwf_x : ∀ x, History.WellFormed (History.objSubhistory H x ++ Rx x)) :
    History.WellFormed (H ++ objs.flatMap Rx) := by
  intro p
  rw [History.procSubhistory_append]
  have hp_seq := hwf p
  have hRx_even_nil : ∀ y, (History.objSubhistory (History.procSubhistory H p) y).length % 2 = 0 →
      History.procSubhistory (Rx y) p = [] := by
    intro y hev_y
    have hev_hy : (History.procSubhistory (History.objSubhistory H y) p).length % 2 = 0 := by
      rwa [History.procSubhistory_objSubhistory_comm]
    have hseq_ext := hwf_x y p
    rw [History.procSubhistory_append] at hseq_ext
    have hresp_py : History.IsRespList (History.procSubhistory (Rx y) p) :=
      fun e hm => hRx_resp y e (List.mem_filter.mp hm).1
    exact History.isRespList_eq_nil_of_isSequential_even ((hwf.objSubhistory y) p) hev_hy
      hresp_py hseq_ext
  rcases History.isSequential_decomp hp_seq with ⟨cs, hcs⟩ | ⟨cs, q, x₀, op, hcs⟩
  · have hall_y : ∀ y, History.procSubhistory (Rx y) p = [] := fun y =>
      hRx_even_nil y (by
        rw [hcs, History.objSubhistory_flatMap_toEvents, History.length_flatMap_toEvents]; omega)
    have hflat_nil : ∀ l : List Obj, History.procSubhistory (l.flatMap Rx) p = [] := by
      intro l
      induction l with
      | nil => exact History.procSubhistory_nil p
      | cons y ys ih =>
        rw [List.flatMap_cons, History.procSubhistory_append, hall_y y, List.nil_append, ih]
    rw [hflat_nil objs, List.append_nil]
    exact hp_seq
  · have hqp : q = p := by
      have hmem : Event.inv q x₀ op ∈ History.procSubhistory H p := by
        rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
      exact of_decide_eq_true (List.mem_filter.mp hmem).2
    subst hqp
    have hother : ∀ y ∈ objs, y ≠ x₀ → History.procSubhistory (Rx y) q = [] := by
      intro y _ hyx₀
      apply hRx_even_nil y
      rw [hcs, History.objSubhistory_append, History.objSubhistory_flatMap_toEvents,
        History.objSubhistory_cons, Event.obj_inv]
      simp only [Ne.symm hyx₀, ↓reduceIte, History.objSubhistory_nil, List.append_nil,
        History.length_flatMap_toEvents]
      omega
    rw [procSubhistory_flatMap_eq_single hobjs_nd Rx q x₀ hother]
    by_cases hx₀ : x₀ ∈ objs
    · simp only [hx₀, ↓reduceIte]
      have hseq_ext := hwf_x x₀ q
      rw [History.procSubhistory_append] at hseq_ext
      have hresp_px₀ : History.IsRespList (History.procSubhistory (Rx x₀) q) :=
        fun e hm => hRx_resp x₀ e (List.mem_filter.mp hm).1
      rcases History.isRespList_le_one_of_isSequential ((hwf.objSubhistory x₀) q)
        hresp_px₀ hseq_ext with hnil | ⟨_, q', y', _, res, _, hR_eq⟩
      · rw [hnil, List.append_nil]; exact hp_seq
      · have hmem_p : Event.resp q' y' res ∈ History.procSubhistory (Rx x₀) q := by
          rw [hR_eq]; exact List.mem_cons_self
        have hq' : q' = q := of_decide_eq_true (List.mem_filter.mp hmem_p).2
        have hy' : y' = x₀ := hRx_obj x₀ _ (List.mem_filter.mp hmem_p).1
        subst hq' hy'
        rw [hR_eq, hcs]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          History.isSequential_append_pair (History.isSequential_flatMap_toEvents cs)
            (by rw [History.length_flatMap_toEvents]; omega) q' y' op res
    · simp only [hx₀, ↓reduceIte, List.append_nil]; exact hp_seq

private theorem procSubhistory_getElem?_even_of_complete {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {M : History P Op Resp} {p : P}
    (hseq : History.IsSequential (M.procSubhistory p)) {cs : List (OpCall P Op Resp)}
    (hcomp : History.complete (M.procSubhistory p) = cs.flatMap OpCall.toEvents) {k : ℕ}
    (hk : k < cs.length) :
    (M.procSubhistory p)[2 * k]? = some (.inv cs[k].proc cs[k].obj cs[k].op) := by
  rcases History.isSequential_decomp hseq with ⟨cs', hcs'⟩ | ⟨cs', q, y, op, hcs'⟩
  · have hcomp' : History.complete (M.procSubhistory p) = cs'.flatMap OpCall.toEvents := by
      rw [hcs']
      exact History.complete_eq_self_of_isSequential_even (hcs' ▸ hseq)
        (by rw [History.length_flatMap_toEvents]; omega)
    have hcs_eq := flatMap_toEvents_injective (hcomp'.symm.trans hcomp)
    subst hcs_eq
    rw [hcs', flatMap_toEvents_getElem?_even cs' k hk]
  · have hcomp' : History.complete (M.procSubhistory p) = cs'.flatMap OpCall.toEvents := by
      rw [hcs', History.complete_flatMap_append_inv]
    have hcs_eq := flatMap_toEvents_injective (hcomp'.symm.trans hcomp)
    subst hcs_eq
    rw [hcs', List.getElem?_append_left (by rw [History.length_flatMap_toEvents]; omega),
      flatMap_toEvents_getElem?_even cs' k hk]

/-- **Herlihy–Wing Theorem 1 (Locality / Compositionality of Linearizability)**
([HerlihyWing1990], §3.1, Theorem 1, pp. 470–471; amended L2 proof of [SelaHerlihyPetrank2021],
§5.2, Theorem 5.1, pp. 7–9): a well-formed concurrent history `H` over typed objects `Obj` is
linearizable if and only if for every object `x : Obj`, its object subhistory
`History.objSubhistory H x` (`H | x`) is linearizable. -/
theorem isLinearizable_iff_forall_obj {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] (spec : ∀ x, SeqSpec P Op Resp x)
    {H : History P Op Resp} (hwf : History.WellFormed H) :
    IsLinearizable spec H ↔ ∀ x, IsLinearizable spec (History.objSubhistory H x) := by
  refine ⟨fun hlin x => hlin.objSubhistory x, fun hall => ?_⟩
  choose Rx Sx hRx_resp hRx_obj hRx_out hwf_x hSx_seq hSx_leg heq_x hprec_x using
    exists_normalized_obj_linearization hwf hall
  let objs := (H.map Event.obj).dedup
  have hobjs_nd : objs.Nodup := List.nodup_dedup _
  let R := objs.flatMap Rx
  let H' := H ++ R
  have hR_resp : History.IsRespList R := fun e hm => by
    obtain ⟨x, _, hex⟩ := List.mem_flatMap.mp hm
    exact hRx_resp x e hex
  have hH'_obj : ∀ x, History.objSubhistory H' x = History.objSubhistory H x ++ Rx x := by
    intro x
    simp only [H', R, History.objSubhistory_append,
      objSubhistory_flatMap_of_nodup hobjs_nd Rx (fun y _ => hRx_obj y) x]
    by_cases hx : x ∈ objs
    · simp only [hx, ↓reduceIte]
    · simp only [hx, ↓reduceIte,
        (hRx_out x (fun hm => hx (List.mem_dedup.mpr hm))).symm]
  have hwf' : History.WellFormed H' :=
    wellFormed_append_flatMap_resp hwf hobjs_nd Rx hRx_resp hRx_obj hwf_x
  have hpCalls_ex : ∀ p : P, ∃ cs : List (OpCall P Op Resp),
      History.complete (History.procSubhistory H' p) = cs.flatMap OpCall.toEvents ∧
      ∀ c ∈ cs, c.proc = p := by
    intro p
    obtain ⟨hseq_cp, hev_cp⟩ := History.complete_isSequential (hwf' p)
    obtain ⟨cs, hcs⟩ := History.exists_calls_of_isSequential_even hseq_cp hev_cp
    refine ⟨cs, hcs, fun c hc => ?_⟩
    have hinv_mem : Event.inv c.proc c.obj c.op ∈ cs.flatMap OpCall.toEvents :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_self⟩
    rw [← hcs] at hinv_mem
    exact of_decide_eq_true (List.mem_filter.mp (History.mem_of_mem_complete hinv_mem)).2
  choose pCalls hpCalls_eq hpCalls_proc using hpCalls_ex
  have hcomp_op_iff : ∀ e : OpId P,
      History.IsCompletedOp H' e ↔ e.idx < (pCalls e.proc).length := by
    intro e
    rw [← History.isCompletedOp_complete_iff hwf', History.isCompletedOp_iff_lt_length,
      History.procSubhistory_complete, hpCalls_eq e.proc, History.length_flatMap_toEvents]
    omega
  have hSxCalls_ex : ∀ x : Obj, ∃ cs : List (OpCall P Op Resp),
      Sx x = cs.flatMap OpCall.toEvents := fun x =>
    History.exists_calls_of_isSequential_even (hSx_seq x)
      (History.even_length_of_equivalent_complete (hwf_x x) (hSx_seq x) (heq_x x))
  choose callsX hSx_eq using hSxCalls_ex
  let α := { e : OpId P // History.IsCompletedOp H' e }
  let callOf : α → OpCall P Op Resp := fun a =>
    (pCalls a.1.proc)[a.1.idx]'((hcomp_op_iff a.1).mp a.2)
  have hcallOf_proc : ∀ a : α, (callOf a).proc = a.1.proc :=
    fun a => hpCalls_proc a.1.proc (callOf a) (List.getElem_mem _)
  let localOp : α → OpId P := fun a =>
    ⟨a.1.proc, countObjCalls (callOf a).obj ((pCalls a.1.proc).take a.1.idx)⟩
  have hlift_localOp : ∀ a : α,
      liftOp H' (callOf a).obj (localOp a) = a.1 ∧
      History.IsCompletedOp (History.objSubhistory H' (callOf a).obj) (localOp a) := by
    intro a
    have hk : a.1.idx < (pCalls a.1.proc).length := (hcomp_op_iff a.1).mp a.2
    obtain ⟨hno_even, hno_odd⟩ := nthObjPos_flatMap_toEvents (pCalls a.1.proc) a.1.idx hk
    rw [← hpCalls_eq a.1.proc] at hno_even hno_odd
    refine ⟨?_, ?_⟩
    · dsimp only [liftOp, localOp, callOf]
      rw [hno_even]
      ext
      · rfl
      · dsimp only; omega
    · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp a.2
      obtain ⟨_, hr_proj⟩ :=
        nthProcPos_objSubhistory_eq (nthObjPos_complete_eq (hwf' a.1.proc) hno_odd) hr
      dsimp only [History.IsCompletedOp, History.respPos, localOp, callOf]
      rw [hr_proj]; rfl
  have hlocalOp_Sx : ∀ a : α, History.IsCompletedOp (Sx (callOf a).obj) (localOp a) := by
    intro a
    have hc_H'x := (hlift_localOp a).2
    rw [hH'_obj] at hc_H'x
    exact ((heq_x (callOf a).obj).isCompletedOp_iff (localOp a)).mp
      ((History.isCompletedOp_complete_iff (hwf_x (callOf a).obj) (localOp a)).mpr hc_H'x)
  let rt : α → α → Prop := fun a b => History.prec H' a.1 b.1
  let loc : α → α → Prop := fun a b =>
    (callOf a).obj = (callOf b).obj ∧ History.prec (Sx (callOf a).obj) (localOp a) (localOp b)
  have hacyc : Acyclic (loc ⊔ rt) := by
    refine acyclic_sup_of_isIntervalOrder (fun a => (callOf a).obj) loc rt
      (History.isIntervalOrder_prec_completed H')
      (fun _ h => History.prec_irrefl _ _ h.2)
      (fun hab hbc => ⟨hab.1.trans hbc.1, History.prec_trans hab.2 (hab.1 ▸ hbc.2)⟩)
      (fun hab => hab.1)
      (fun {a b} hobj hrt => ⟨hobj, ?_⟩)
    obtain ⟨hlift_a, hc_ax⟩ := hlift_localOp a
    obtain ⟨hlift_b, hc_bx⟩ := hlift_localOp b
    rw [← hobj] at hlift_b hc_bx
    have hpr_H'x :
        History.prec (History.objSubhistory H' (callOf a).obj) (localOp a) (localOp b) := by
      refine (prec_objSubhistory_iff hwf' hc_ax hc_bx).mpr ?_
      rwa [hlift_a, hlift_b]
    rw [hH'_obj] at hpr_H'x hc_ax hc_bx
    exact hprec_x (callOf a).obj (localOp a) (localOp b) hc_ax hc_bx
      ((History.prec_append_resp_iff (hwf.objSubhistory (callOf a).obj) (hRx_resp _)
        (hwf_x _) hc_bx).mp hpr_H'x)
  let procs := (H'.map Event.proc).dedup
  have hprocs_nd : procs.Nodup := List.nodup_dedup _
  let elems : List α := procs.flatMap fun p =>
    (List.finRange (pCalls p).length).map fun k => ⟨⟨p, k.1⟩, (hcomp_op_iff ⟨p, k.1⟩).mpr k.2⟩
  have helems_mem : ∀ a : α, a ∈ elems := by
    intro a
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp a.2
    obtain ⟨hr_lt, hr_proc⟩ := History.nthProcPos_lt_length hr
    rw [List.getElem?_eq_getElem hr_lt, Option.map_some, Option.some.injEq] at hr_proc
    have hp_in_procs : a.1.proc ∈ procs :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨H'[r], List.getElem_mem hr_lt, hr_proc⟩)
    exact List.mem_flatMap.mpr ⟨a.1.proc, hp_in_procs,
      List.mem_map.mpr ⟨⟨a.1.idx, (hcomp_op_iff a.1).mp a.2⟩, List.mem_finRange _, by ext <;> rfl⟩⟩
  have helems_nd : elems.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun p _ => List.Nodup.map (fun k₁ k₂ h => Fin.ext (congrArg (fun a : α => a.1.idx) h))
      (List.nodup_finRange _),
      hprocs_nd.pairwise_of_forall_ne fun p₁ _ p₂ _ hpne => ?_⟩
    dsimp only [Function.onFun]
    rw [List.disjoint_left]
    intro a ha₁ ha₂
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha₁
    obtain ⟨_, _, heq⟩ := List.mem_map.mp ha₂
    exact hpne (congrArg (fun x : α => x.1.proc) heq).symm
  obtain ⟨order, hperm, hord_nd, hord_rel⟩ := exists_topoSort_of_acyclic hacyc helems_nd
  have hord_mem : ∀ a : α, a ∈ order := fun a => hperm.mem_iff.mpr (helems_mem a)
  -- Distinct, and no `loc ⊔ rt`-edge points backwards; inherited by every filter of `order`.
  have hpw : order.Pairwise fun a b => a ≠ b ∧ ¬ (loc ⊔ rt) b a :=
    List.pairwise_iff_getElem.mpr fun i j hi hj hij =>
      ⟨fun h => by have := (List.Nodup.getElem_inj_iff hord_nd).mp h; omega,
        fun h => by have := hord_rel j i hj hi (.single h); omega⟩
  let calls := order.map callOf
  let S := calls.flatMap OpCall.toEvents
  have hord_proc : ∀ p : P,
      (order.filter fun a => decide (a.1.proc = p)).map (fun a => a.1.idx) =
        List.range (pCalls p).length ∧
      (order.filter fun a => decide (a.1.proc = p)).map callOf = pCalls p := by
    intro p
    let ord_p := order.filter fun a => decide (a.1.proc = p)
    refine List.map_eq_of_strictMono_surj (src := ord_p) (dst := pCalls p)
      (fun a => a.1.idx) callOf ?_ ?_ ?_
    · intro a ha
      have hap : a.1.proc = p := of_decide_eq_true (List.mem_filter.mp ha).2
      have hlt : a.1.idx < (pCalls p).length := hap ▸ (hcomp_op_iff a.1).mp a.2
      refine ⟨hlt, ?_⟩
      dsimp only [callOf]; cases hap; rfl
    · intro i j hi hj hij
      obtain ⟨hne_ij, hback⟩ := List.pairwise_iff_getElem.mp (hpw.filter _) i j hi hj hij
      have hp_i : ord_p[i].1.proc = p :=
        of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi)).2
      have hp_j : ord_p[j].1.proc = p :=
        of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
      rcases lt_trichotomy ord_p[i].1.idx ord_p[j].1.idx with hlt | heq | hgt
      · exact hlt
      · exact absurd (Subtype.ext (OpId.ext (hp_i.trans hp_j.symm) heq)) hne_ij
      · exact absurd (Or.inr (History.prec_of_same_proc_lt (hp_j.trans hp_i.symm) hgt
          ord_p[j].2 ord_p[i].2)) hback
    · intro k hk
      let a : α := ⟨⟨p, k⟩, (hcomp_op_iff ⟨p, k⟩).mpr hk⟩
      exact ⟨a, List.mem_filter.mpr ⟨hord_mem a, decide_eq_true rfl⟩, rfl⟩
  have heq_S : History.Equivalent (History.complete H') S := by
    intro p
    rw [History.procSubhistory_complete, hpCalls_eq p]
    simp only [S, calls, History.procSubhistory_flatMap_toEvents, List.filter_map,
      Function.comp_def, hcallOf_proc]
    rw [(hord_proc p).2]
  have hopIdAt_order : ∀ (j : ℕ) (hj : j < order.length),
      opIdAt calls j (by simp only [calls, List.length_map]; exact hj) = order[j].1 := by
    intro j hj
    obtain ⟨hlt_f, hget_f⟩ := List.filter_getElem_count_take
      (fun a : α => decide (a.1.proc = order[j].1.proc)) order j hj (decide_eq_true rfl)
    have hidx := List.getElem_of_eq (hord_proc order[j].1.proc).1 (by simpa using hlt_f)
    simp only [List.getElem_map, List.getElem_range, hget_f] at hidx
    ext
    · simp only [opIdAt, calls, List.getElem_map, hcallOf_proc]
    · simp only [opIdAt, calls, List.getElem_map, hcallOf_proc, countProcCalls, ← List.map_take,
        List.filter_map, List.length_map, Function.comp_def, hidx]
  have hS_leg : History.IsLegal spec S := by
    intro x
    have hfil_obj : History.objSubhistory S x =
        ((order.filter fun a => decide ((callOf a).obj = x)).map callOf).flatMap
          OpCall.toEvents := by
      simp only [S, calls, History.objSubhistory_flatMap_toEvents, List.filter_map]; rfl
    rw [hfil_obj]
    let ord_x := order.filter fun a => decide ((callOf a).obj = x)
    have hlocal_in_callsX : ∀ a : α, (callOf a).obj = x →
        (localOp a).idx < countProcCalls (localOp a).proc (callsX x) := by
      intro a hax
      have hc_Sx : History.IsCompletedOp (Sx x) (localOp a) := hax ▸ hlocalOp_Sx a
      have hlen := (History.isCompletedOp_iff_lt_length _ (localOp a)).mp hc_Sx
      rw [hSx_eq x, History.procSubhistory_flatMap_toEvents,
        History.length_flatMap_toEvents] at hlen
      dsimp only [countProcCalls]; omega
    let posInSx : α → ℕ := fun a =>
      if hax : (callOf a).obj = x then
        (exists_opIdAt_of_lt_countProcCalls (callsX x) (localOp a)
          (hlocal_in_callsX a hax)).choose
      else 0
    have hposInSx_spec : ∀ a : α, (hax : (callOf a).obj = x) →
        ∃ hj : posInSx a < (callsX x).length,
          opIdAt (callsX x) (posInSx a) hj = localOp a := by
      intro a hax
      simp only [posInSx, hax, ↓reduceDIte]
      exact (exists_opIdAt_of_lt_countProcCalls (callsX x) (localOp a)
        (hlocal_in_callsX a hax)).choose_spec
    have hord_x_eq : ord_x.map callOf = callsX x := by
      refine (List.map_eq_of_strictMono_surj (src := ord_x) (dst := callsX x)
        posInSx callOf ?_ ?_ ?_).2
      · intro a ha
        have hax : (callOf a).obj = x := of_decide_eq_true (List.mem_filter.mp ha).2
        obtain ⟨hj, hop_eq⟩ := hposInSx_spec a hax
        refine ⟨hj, ?_⟩
        let p := a.1.proc
        have hproc_j : (callsX x)[posInSx a].proc = p := congrArg OpId.proc hop_eq
        have hcnt_j : countProcCalls p ((callsX x).take (posInSx a)) = (localOp a).idx := by
          have := congrArg OpId.idx hop_eq
          simpa only [opIdAt, localOp, hproc_j] using this
        obtain ⟨hlt_cx, hget_cx⟩ := List.filter_getElem_count_take
          (fun c : OpCall P Op Resp => decide (c.proc = p)) (callsX x) (posInSx a) hj
          (decide_eq_true hproc_j)
        have hk_p : a.1.idx < (pCalls p).length := (hcomp_op_iff a.1).mp a.2
        obtain ⟨hlt_pc, hget_pc⟩ := List.filter_getElem_count_take
          (fun c : OpCall P Op Resp => decide (c.obj = x)) (pCalls p) a.1.idx hk_p
          (decide_eq_true hax)
        have hlists_eq :
            ((pCalls p).filter fun c => decide (c.obj = x)) =
              ((callsX x).filter fun c => decide (c.proc = p)) := by
          apply flatMap_toEvents_injective
          rw [← History.objSubhistory_flatMap_toEvents, ← hpCalls_eq p,
            ← History.procSubhistory_complete, ← History.procSubhistory_objSubhistory_comm,
            ← History.complete_objSubhistory hwf' x, hH'_obj x, heq_x x p, hSx_eq x,
            History.procSubhistory_flatMap_toEvents]
        have hidx_same :
            (((pCalls p).take a.1.idx).filter fun c => decide (c.obj = x)).length =
              (((callsX x).take (posInSx a)).filter fun c => decide (c.proc = p)).length := by
          have h₁ : (((pCalls p).take a.1.idx).filter fun c => decide (c.obj = x)).length =
              (localOp a).idx := by dsimp only [localOp, countObjCalls]; rw [hax]
          exact h₁.trans hcnt_j.symm
        refine hget_pc.symm.trans (Eq.trans ?_ hget_cx)
        simp only [hlists_eq, hidx_same]
      · intro i j hi hj hij
        obtain ⟨hne_ij, hback⟩ := List.pairwise_iff_getElem.mp (hpw.filter _) i j hi hj hij
        have hx_i : (callOf ord_x[i]).obj = x :=
          of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi)).2
        have hx_j : (callOf ord_x[j]).obj = x :=
          of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
        obtain ⟨hj_i, hop_i⟩ := hposInSx_spec ord_x[i] hx_i
        obtain ⟨hj_j, hop_j⟩ := hposInSx_spec ord_x[j] hx_j
        have hpos_ne : posInSx ord_x[i] ≠ posInSx ord_x[j] := by
          intro hpeq
          have hloc_eq : localOp ord_x[i] = localOp ord_x[j] := by
            rw [← hop_i, ← hop_j]; congr 1
          have hlift_i := (hlift_localOp ord_x[i]).1
          have hlift_j := (hlift_localOp ord_x[j]).1
          rw [hx_i] at hlift_i; rw [hx_j, ← hloc_eq] at hlift_j
          exact hne_ij (Subtype.ext (hlift_i.symm.trans hlift_j))
        refine (Nat.lt_or_gt_of_ne hpos_ne).resolve_right fun hgt => hback (Or.inl ?_)
        have hpr_ji : History.prec (Sx x) (localOp ord_x[j]) (localOp ord_x[i]) := by
          rw [hSx_eq x, ← hop_j, ← hop_i]
          exact (prec_flatMap_toEvents_opIdAt_iff (callsX x) hj_j hj_i).mpr hgt
        exact (show loc ord_x[j] ord_x[i] from ⟨hx_j.trans hx_i.symm, hx_j ▸ hpr_ji⟩)
      · intro k hk
        let e_x := opIdAt (callsX x) k hk
        have hc_Sx_k : History.IsCompletedOp (Sx x) e_x := by
          rw [hSx_eq x, History.IsCompletedOp, (invPos_respPos_opIdAt (callsX x) k hk).2]
          rfl
        have hc_H'x_k : History.IsCompletedOp (History.objSubhistory H' x) e_x := by
          rw [hH'_obj x]
          exact (History.isCompletedOp_complete_iff (hwf_x x) e_x).mp
            (((heq_x x).isCompletedOp_iff e_x).mpr hc_Sx_k)
        obtain ⟨hc_H'_k, _, ⟨i_pos, hi_pos, hi_obj, _⟩, _⟩ := liftOp_spec hwf' hc_H'x_k
        let a : α := ⟨liftOp H' x e_x, hc_H'_k⟩
        have hax : (callOf a).obj = x := by
          have hget_i := History.nthProcPos_getElem? hi_pos
          have hev_a := procSubhistory_getElem?_even_of_complete (hwf' a.1.proc)
            (hpCalls_eq a.1.proc) ((hcomp_op_iff a.1).mp a.2)
          rw [hget_i, hev_a, Option.map_some, Event.obj_inv, Option.some.injEq] at hi_obj
          exact hi_obj
        obtain ⟨hlift_loc, hc_loc⟩ := hlift_localOp a
        rw [hax] at hlift_loc hc_loc
        have hloc_eq_ex : localOp a = e_x :=
          liftOp_inj_of_isCompletedOp hwf' hc_loc hc_H'x_k hlift_loc
        obtain ⟨hj_a, hop_a⟩ := hposInSx_spec a hax
        rw [hloc_eq_ex] at hop_a
        exact ⟨a, List.mem_filter.mpr ⟨hord_mem a, decide_eq_true hax⟩,
          opIdAt_injective hj_a hk hop_a⟩
    rw [hord_x_eq, ← hSx_eq x]
    exact hSx_leg x
  refine ⟨H', ⟨R, hR_resp, rfl, hwf'⟩, S, History.isSequential_flatMap_toEvents calls, hS_leg,
    heq_S, fun e₀ e₁ hc₀ hc₁ hpr_H => ?_⟩
  have hpr_H' : History.prec H' e₀ e₁ :=
    (History.prec_append_resp_iff hwf hR_resp hwf' hc₁).mpr hpr_H
  let a₀ : α := ⟨e₀, hc₀⟩
  let a₁ : α := ⟨e₁, hc₁⟩
  obtain ⟨i₀, hi₀, ha₀_eq⟩ := List.getElem_of_mem (hord_mem a₀)
  obtain ⟨i₁, hi₁, ha₁_eq⟩ := List.getElem_of_mem (hord_mem a₁)
  have hrel : TransGen (loc ⊔ rt) order[i₀] order[i₁] := by
    rw [ha₀_eq, ha₁_eq]
    exact TransGen.single (Or.inr hpr_H')
  have hlt_01 : i₀ < i₁ := hord_rel i₀ i₁ hi₀ hi₁ hrel
  have hi₀_c : i₀ < calls.length := by simp only [calls, List.length_map]; exact hi₀
  have hi₁_c : i₁ < calls.length := by simp only [calls, List.length_map]; exact hi₁
  have hpr_S := (prec_flatMap_toEvents_opIdAt_iff calls hi₀_c hi₁_c).mpr hlt_01
  rwa [hopIdAt_order i₀ hi₀, hopIdAt_order i₁ hi₁, ha₀_eq, ha₁_eq] at hpr_S

end Cslib.Distributed.ConcurrentObjects
