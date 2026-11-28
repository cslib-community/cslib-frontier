/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Cut

/-!
# The cost of the steps of the dealing program

A step of the dealing program of [AnthropicVPVNP2026] costs at most a bound in the lengths `Lc`
of the codes and in a bound `X` for the numbers of options (`stepBound`), as long as the values
that steps read are short: the values at the empty name, the row data, the digits of the numbers
of units and outcomes, and the steps of the straight-line program. Every step up to the checks
keeps these values short, so they cost at most `stepBound Lc X` along every run
(`exists_inv_dealSteps`). The guesses of the contents of the units cost little for the units that
are not cut, and `m + 1` times a bound in the number `mb` of digits of `m` for the cut units
(`exists_inv_contentSteps`).

## Main definitions

* `stepBound`: a bound for the cost of a step up to the checks.

## Main results

* `exists_inv_dealSteps`: the steps up to the checks cost at most `stepBound Lc X` each.
* `exists_inv_contentSteps`: the cost of the guesses of the contents.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: it computes the plan in `(MN)^C_tree Λ` steps, and the cut packets in
`kΛ · τΛ/v^300` steps). Ported from the source modules `Nc.Dl.Bd1` and `Nc.Dl.Bd2` (the cost of
the steps 9).
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- A bound for the cost of a step up to the checks, for codes of length at most `Lc` and at most
`X` options of a pick. -/
@[expose] def stepBound (Lc X : ℕ) : ℕ :=
  60 * Lc + 20 * X + X * (4 * (60 * Lc + 80)) + 180 * Lc + 200

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm : ℕ} {M : Moves F (K + K + A') E}
  {S : Type} [Fintype S] {C : Codes S M U0 U1 D pS} {m mb Lc : ℕ}

/-! ### Invariants of lists of steps -/

section Invariants

/-- The step `s` keeps the invariant `J` of states and costs at most `c` from its states. -/
private def Keeps (m mb : ℕ) (J : (List Bool → Tree) → Prop) (c : ℕ) (s : DStep) : Prop :=
  ∀ σ, J σ → s.cost m mb σ ≤ c ∧ ∀ σ' ∈ s.exec m σ, J σ'

private theorem Keeps.mono {J : (List Bool → Tree) → Prop} {c c' : ℕ} {s : DStep}
    (h : Keeps m mb J c s) (hc : c ≤ c') : Keeps m mb J c' s :=
  fun σ hσ => ⟨(h σ hσ).1.trans hc, (h σ hσ).2⟩

/-- Steps that keep an invariant give an invariant of the steps still to come and the state. -/
private theorem exists_inv {J : (List Bool → Tree) → Prop} {c : DStep → ℕ} {sts : List DStep}
    (h : ∀ s ∈ sts, Keeps m mb J (c s) s) {σ₀ : List Bool → Tree} (h₀ : J σ₀) :
    ∃ I : List DStep → (List Bool → Tree) → Prop, (∀ s rest σ, I (s :: rest) σ →
      s.cost m mb σ ≤ c s ∧ ∀ σ' ∈ s.exec m σ, I rest σ') ∧ I sts σ₀ :=
  ⟨fun rest σ => (∀ s ∈ rest, Keeps m mb J (c s) s) ∧ J σ, fun s _ _ ⟨h1, h2⟩ =>
    ⟨(h1 s List.mem_cons_self _ h2).1, fun σ' hσ' =>
      ⟨fun s' hs' => h1 s' (List.mem_cons_of_mem _ hs'), (h1 s List.mem_cons_self _ h2).2 σ' hσ'⟩⟩,
    h, h₀⟩

end Invariants

/-! ### Short values -/

section Short

/-- The names whose values steps up to the checks read. -/
private def Readable : PlanName S M U0 U1 pS → Prop
  | .empty | .rowData _ _ | .countDigit _ _ | .outcomeDigit _ | .gate _ => True
  | _ => False

/-- A state by names whose empty name is empty and whose readable values are short. -/
private structure Short (Lc : ℕ) (st : PlanName S M U0 U1 pS → Tree) : Prop where
  empty : st .empty = .nil
  len : ∀ y, Readable y → (st y).len ≤ Lc

omit [Fintype S] in
private theorem Short.update [DecidableEq S] {st : PlanName S M U0 U1 pS → Tree}
    (h : Short Lc st) {y : PlanName S M U0 U1 pS} (hy : y ≠ .empty) {v : Tree}
    (hv : Readable y → v.len ≤ Lc) : Short Lc (update st y v) :=
  ⟨by rw [update_of_ne hy.symm, h.empty], fun z hz => by
    by_cases hzy : z = y
    · subst hzy; simpa using hv hz
    · simpa [hzy] using h.len z hz⟩

omit [Fintype S] in
private theorem Short.assignAll [DecidableEq S] {st : PlanName S M U0 U1 pS → Tree}
    (h : Short Lc st) {o : List (PlanName S M U0 U1 pS × Tree)}
    (ho : ∀ b ∈ o, b.1 ≠ .empty ∧ (Readable b.1 → b.2.len ≤ Lc)) : Short Lc (assignAll st o) := by
  induction o generalizing st with
  | nil => exact h
  | cons b o ih =>
    exact ih (h.update (ho b List.mem_cons_self).1 (ho b List.mem_cons_self).2)
      fun b' hb' => ho b' (List.mem_cons_of_mem _ hb')

variable (C) in
/-- The states by names with short values. -/
private def ShortState (Lc : ℕ) (σ : List Bool → Tree) : Prop :=
  ∃ st, Short Lc st ∧ σ = extend C.name st fun _ => .nil

/-- A property that holds at the empty tree and at the values of `f` holds at every value of the
trie of `f`. -/
private theorem tget_trieOf_mem {α : Type*} [Fintype α] {code : α → List Bool} {f : α → Tree}
    {P : Tree → Prop} (h0 : P .nil) (hf : ∀ a, P (f a)) (p : List Bool) :
    P (tget p (trieOf code f)) := by
  rw [trieOf]
  induction (univ : Finset α).toList with
  | nil => rwa [List.foldr_nil, tget_nil]
  | cons a l ih => rw [List.foldr_cons, tget_tset]; split_ifs <;> simp [hf, ih]

/-- A property that holds at the empty tree and at `t` holds at every value of the trie with the
single value `t`. -/
private theorem tget_single_mem {P : Tree → Prop} (h0 : P .nil) {t : Tree} (ht : P t)
    (p : List Bool) : P (tget p (.cons t .nil)) := by
  rcases p with _ | ⟨_ | _, p⟩ <;> simpa [tget, tget_nil]

/-- All values of the trie `t` are short. -/
private def Looks (Lc : ℕ) (t : Tree) : Prop := ∀ q, (tget q t).len ≤ Lc

private theorem looks_nil : Looks Lc .nil := fun q => by simp [tget_nil, len]

private theorem looks_single {t : Tree} (ht : t.len ≤ Lc) : Looks Lc (.cons t .nil) :=
  tget_single_mem (P := fun t => t.len ≤ Lc) (by simp [len]) ht

variable (hnm : ∀ y, (C.name y).length ≤ Lc)
include hnm

omit [Fintype S] in
/-- An operation that reads readable names and writes a name other than the empty one. -/
private theorem keeps_op {x y z : PlanName S M U0 U1 pS} {φ : Tree} (hx : Readable x)
    (hy : Readable y) (hz : z ≠ .empty)
    (hφ : Readable z → ∀ p, Looks Lc (tget p φ)) :
    Keeps m mb (ShortState C Lc) (180 * Lc + 200) (.op (C.name x) (C.name y) (C.name z) φ) := by
  classical
  rintro _ ⟨st, hst, rfl⟩
  rw [exec_op C.name_injective]
  refine ⟨?_, fun σ' hσ' => ⟨_, hst.update hz fun h => hφ h _ _, List.mem_singleton.1 hσ'⟩⟩
  have := hnm x; have := hnm y; have := hnm z; have := hst.len x hx; have := hst.len y hy
  simp only [DStep.cost, C.name_injective.extend_apply]
  omega

omit [Fintype S] in
private theorem keeps_unary {x dst : PlanName S M U0 U1 pS} {f : Fin D → Tree} (hx : Readable x)
    (hdst : dst ≠ .empty) (hf : Readable dst → ∀ d, (f d).len ≤ Lc) :
    Keeps m mb (ShortState C Lc) (180 * Lc + 200) (C.unaryStep x dst f) :=
  keeps_op hnm hx trivial hdst fun h =>
    tget_trieOf_mem (P := Looks Lc) looks_nil fun d => looks_single (hf h d)

omit [Fintype S] in
private theorem keeps_const {dst : PlanName S M U0 U1 pS} {t : Tree} (hdst : dst ≠ .empty)
    (ht : Readable dst → t.len ≤ Lc) :
    Keeps m mb (ShortState C Lc) (180 * Lc + 200) (C.constStep dst t) :=
  keeps_op hnm trivial trivial hdst fun h =>
    tget_single_mem (P := Looks Lc) looks_nil (looks_single (ht h))

omit [Fintype S] in
/-- A pick from at most `X` options of at most `w` assignments each, to names other than the
empty one, with short values at readable names. -/
private theorem keeps_pick {α : Type*} {opts : List α} {o : α → List (PlanName S M U0 U1 pS × Tree)}
    {X w : ℕ} (hX : opts.length ≤ X) (hw : ∀ a ∈ opts, (o a).length ≤ w)
    (ho : ∀ a ∈ opts, ∀ b ∈ o a, b.1 ≠ .empty ∧ (Readable b.1 → b.2.len ≤ Lc)) :
    Keeps m mb (ShortState C Lc) (60 * Lc + 20 * X + X * (w * (60 * Lc + 80)) + 200)
      (C.pickStep opts o) := by
  classical
  rintro _ ⟨st, hst, rfl⟩
  refine ⟨?_, fun σ' hσ' => ?_⟩
  · have hsum : ((opts.map fun a => optionTree C.name (o a)).map fun t =>
        (t.toList.map fun y => 60 * y.hd.len + 80).sum).sum ≤ X * (w * (60 * Lc + 80)) := by
      rw [List.map_map]
      refine (List.sum_le_length_nsmul _ _ fun n hn => ?_).trans (by
        rw [smul_eq_mul, List.length_map]; exact Nat.mul_le_mul_right _ hX)
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hn
      simp only [Function.comp_apply, optionTree, toList_listT, List.map_map]
      refine (List.sum_le_length_nsmul _ (60 * Lc + 80) fun n hn => ?_).trans (by
        rw [smul_eq_mul, List.length_map]; exact Nat.mul_le_mul_right _ (hw a ha))
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hn
      have := hnm b.1
      simp only [Function.comp_apply, hd_cons, len_ofBits]
      omega
    have := hnm .empty
    simp only [Codes.pickStep, DStep.cost, C.name_injective.extend_apply, hst.empty, path, tget,
      hd_cons, toList_listT, List.length_map, len]
    omega
  · rw [C.exec_pickStep hst.empty] at hσ'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hσ'
    exact ⟨_, hst.assignAll (ho a ha), rfl⟩

omit [Fintype S] in
private theorem keeps_check (y : PlanName S M U0 U1 pS) :
    Keeps m mb (ShortState C Lc) (30 * Lc + 100) (.check (C.name y)) := by
  rintro σ hσ
  have := hnm y
  refine ⟨by simp only [DStep.cost]; omega, fun σ' hσ' => ?_⟩
  simp only [DStep.exec] at hσ'
  split_ifs at hσ' <;> simp_all

end Short

/-! ### The steps up to the checks -/

section Steps

variable {P : Plan M U0 U1} {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}
  (tab : SlpTab P grp D nI pS) {Q : Type} [Fintype Q] {X : ℕ}

omit [Fintype S] in
private theorem digitTree_len (hdc : ∀ d, (C.digit d).length ≤ Lc) (d : Fin D) :
    (C.digitTree d).len ≤ Lc := by
  rw [Codes.digitTree, len_ofBits]; exact hdc d

/-- **The cost of the steps up to the checks.** If the codes of the names, the digits and the row
data have length at most `Lc`, and `X` bounds the numbers of options of the picks, then every step
of `Codes.dealSteps` costs at most `stepBound Lc X` along every run from the state at the
beginning. -/
theorem exists_inv_dealSteps (hnm : ∀ y, (C.name y).length ≤ Lc)
    (hdc : ∀ d, (C.digit d).length ≤ Lc) (hrc : ∀ d, (C.rowData d).length ≤ Lc)
    (hXQ : Fintype.card Q + 1 ≤ X) (hXr : Fintype.card (RowData (K + K)) ≤ X)
    (hXU0 : U0 + 1 ≤ X) (hXU1 : U1 ≤ X) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q)
    (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    ∃ I : List DStep → (List Bool → Tree) → Prop, (∀ s rest σ, I (s :: rest) σ →
      s.cost m mb σ ≤ stepBound Lc X ∧ ∀ σ' ∈ s.exec m σ, I rest σ') ∧
      I (C.dealSteps tab qn i e hU0 hU1) (extend C.name (initialState pt) fun _ => .nil) := by
  classical
  have hop : 180 * Lc + 200 ≤ stepBound Lc X := by unfold stepBound; omega
  have hpk (w : ℕ) (hw : w ≤ 4) : 60 * Lc + 20 * X + X * (w * (60 * Lc + 80)) + 200 ≤
      stepBound Lc X := by
    have := Nat.mul_le_mul_left X (Nat.mul_le_mul_right (60 * Lc + 80) hw)
    unfold stepBound; omega
  refine exists_inv (J := ShortState C Lc) (c := fun _ => stepBound Lc X) (fun s hs => ?_)
    ⟨_, ⟨rfl, fun y hy => ?_⟩, rfl⟩
  swap
  · cases y <;> simp_all [Readable, initialState, len]
  simp only [Codes.dealSteps, Codes.choiceSteps, Codes.stateSteps, Codes.rowDataSteps,
    Codes.countSteps, Codes.outcomeSteps, Codes.rowCheckSteps, Codes.gateSteps,
    Codes.readOutSteps, Codes.checkSteps, List.mem_append, List.mem_map, mem_toList, mem_univ,
    true_and, List.mem_finRange] at hs
  rcases hs with (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨ν, rfl⟩) | ⟨⟨s', p⟩, rfl⟩ | ⟨k, rfl⟩ |
    ⟨a, rfl⟩ | ⟨_, (⟨a, rfl⟩ | ⟨c, rfl⟩), rfl⟩
  · refine (keeps_pick hnm (w := 1) ?_ (by simp) (by simp [Readable])).mono (hpk 1 (by omega))
    unfold stateOptions
    split_ifs <;> simp only [List.length_singleton, length_toList, card_univ] <;> omega
  · refine (keeps_pick hnm (w := 2) ?_ (by simp) ?_).mono (hpk 2 (by omega))
    · simpa using hXr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d - b (rfl | rfl) <;> simp [Readable, len_ofBits, hrc]
  · refine (keeps_pick hnm (w := 4) ?_ (fun n _ => ?_) ?_).mono (hpk 4 le_rfl)
    · simpa using hXU0
    · simp only [Codes.countOption, List.length_cons]; split_ifs <;> simp
    · simp only [Codes.countOption, List.mem_cons]
      rintro n - b (rfl | rfl | rfl | hb)
      · simp [Readable]
      · simp [Readable]
      · simp [Readable, digitTree_len hdc]
      · split_ifs at hb <;> simp_all [Readable]
  · refine (keeps_pick hnm (w := 3) ?_ (by simp) ?_).mono (hpk 3 (by omega))
    · simpa using hXU1
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro j - b (rfl | rfl | rfl) <;> simp [Readable, digitTree_len hdc]
  · simp only [uncurry_apply_pair, Codes.rowCheckStep]
    split_ifs <;> exact (keeps_op hnm (by exact trivial) (by exact trivial) (by simp)
      (by simp [Readable])).mono hop
  · unfold Codes.gateStep
    split_ifs with h1 h2 h3
    · exact (keeps_unary hnm (by rcases tab.input h1.choose with _ | _ <;> trivial) (by simp)
        fun _ => digitTree_len hdc).mono hop
    · exact (keeps_const hnm (by simp) fun _ => digitTree_len hdc _).mono hop
    · refine (keeps_op hnm (by exact trivial) (by exact trivial) (by simp) fun _ =>
        tget_trieOf_mem looks_nil fun d q => ?_).mono hop
      exact tget_trieOf_mem (P := fun t => t.len ≤ Lc) (by simp [len])
        (fun _ => digitTree_len hdc _) q
    · exact (keeps_const hnm (by simp) fun _ => by simp [len]).mono hop
  · rcases a with x | c | u <;>
      exact (keeps_unary hnm (by exact trivial) (by simp) (by simp [Readable])).mono hop
  all_goals exact (keeps_check hnm _).mono (by unfold stepBound; omega)

end Steps

/-! ### The guesses of the contents -/

variable {P : Plan M U0 U1} {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}
  (tab : SlpTab P grp D nI pS) {Q : Type} [Fintype Q]

/-- **The cost of the guesses of the contents.** Every state after `Codes.dealSteps`, from the
state at the beginning, comes from valid numbers of units `n` and good outcomes `o`, and along
every run from it the guesses of the contents cost at most `90 * Lc + 230` for every unit and
`(m + 1) * (60 * mb + 100)` more for every unit cut between two groups. -/
theorem exists_inv_contentSteps (hK : 0 < K) (hnm : ∀ y, (C.name y).length ≤ Lc)
    {pt : Fin K → Tree} {qn : Q → ℕ} {i e : Q} {hU0 : U0 < D} {hU1 : U1 ≤ D}
    {σ : List Bool → Tree} (hσ : σ ∈ execAll m (C.dealSteps tab qn i e hU0 hU1)
      (extend C.name (initialState pt) fun _ => .nil)) :
    ∃ (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1),
      tab.Valid n ∧ (∀ x, P.Good n o x) ∧
      ∃ (I : List DStep → (List Bool → Tree) → Prop) (c : DStep → ℕ), (∀ s rest σ,
        I (s :: rest) σ → s.cost m mb σ ≤ c s ∧ ∀ σ' ∈ s.exec m σ, I rest σ') ∧
        I C.contentSteps σ ∧ (C.contentSteps.map fun s => c s + 30).sum ≤
          Fintype.card (UnitId (K + K) U0 M.Channel U1) * (90 * Lc + 230) +
            (Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)).card *
              ((m + 1) * (60 * mb + 100)) := by
  classical
  obtain ⟨n, o, st, hn, ho, hcut, rfl⟩ := mem_execAll_dealSteps C tab hK hσ
  have hkeep : ∀ s ∈ C.contentSteps, Keeps m mb
      (fun σ => ∀ u, σ (C.name (.isCut u)) = st (.isCut u))
      (s.cost m mb (extend C.name st fun _ => .nil)) s := by
    intro s hs σ hσ
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hs
    refine ⟨by simp [DStep.cost, hσ, C.name_injective.extend_apply], fun σ' hσ' u' => ?_⟩
    simp only [DStep.exec] at hσ'
    split_ifs at hσ'
    · rw [List.mem_singleton.1 hσ', hσ]
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hσ'
      rw [update_of_ne (by simp [C.name_injective.eq_iff]), hσ]
  obtain ⟨I, hI, hI0⟩ := exists_inv hkeep fun u => C.name_injective.extend_apply _ _ _
  refine ⟨n, o, hn, ho, I, _, hI, hI0, ?_⟩
  rw [Codes.contentSteps, List.map_map, Function.comp_def, sum_map_toList]
  refine (sum_le_sum fun u _ => (?_ : _ ≤ 90 * Lc + 230 + if u ∈ Play.cutUnits
    (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E) then
      (m + 1) * (60 * mb + 100) else 0)).trans_eq ?_
  · have := hnm (.isCut u)
    have := hnm (.content u)
    by_cases hu : u ∈ Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E) <;>
      simp only [DStep.cost, C.name_injective.extend_apply, hcut, bit, hu, decide_true,
        decide_false, Bool.false_eq_true, ↓reduceIte, one, reduceCtorEq] <;> omega
  · rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, sum_ite_mem, univ_inter, sum_const,
      smul_eq_mul]

end Cslib.Circuits.Arithmetic.Separation.Dealing
