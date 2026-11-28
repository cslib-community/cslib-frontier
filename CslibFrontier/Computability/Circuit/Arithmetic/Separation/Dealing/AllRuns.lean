/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Runs
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.FullTrie
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Picks
import CslibFrontier.Foundations.Logic.Function.FoldlUpdate

/-!
# All runs of the dealing program

After its checks (`Codes.dealSteps`), the dealing program of [AnthropicVPVNP2026] guesses the
contents of the units that are cut between two groups (`Codes.contentSteps`): `ub` bits for a cut
unit and nothing for the others. The sum over the states after all its steps is the sum over the
choices that pass the checks and over the contents that are present exactly for the cut units, at
states with the values of the end (`Final`) that the templates of the scripts read
(`sum_execAll_allSteps`).

## Main definitions

* `Codes.contentSteps`: the guesses of the contents of the cut units.

## Main results

* `sum_execAll_allSteps`: the sum over the runs of all steps of the dealing program.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: it then guesses the contents of the cut packets). Ported from the source
modules `Nc.Dl.Run2` (the contents) and `Nc.Dl.Total`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm : ℕ} {M : Moves F (K + K + A') E}
  {S : Type} [Fintype S] [DecidableEq S] (C : Codes S M U0 U1 D pS) {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (tab : SlpTab P grp D nI pS)

namespace Codes

/-- Phase 9: guess the contents of the cut units. -/
@[expose] noncomputable def contentSteps : List DStep :=
  (univ : Finset (UnitId (K + K) U0 M.Channel U1)).toList.map fun u =>
    DStep.bits (C.name (.isCut u)) (C.name (.content u))

end Codes

/-! ### The contents of the cut units -/

section Contents

/-- The content of a unit with the reversed bits `w`. -/
private def contentOf (ub : ℕ) (w : List Bool) : UnitContent ub :=
  some fun j => w.reverse.getD j false

private theorem bits_contentOf {ub : ℕ} {w : List Bool} (h : w.length = ub) :
    (contentOf ub w).bits = w.reverse := by
  subst h
  refine List.ext_getElem (by simp [contentOf, UnitContent.bits]) fun k h1 h2 => ?_
  simp [contentOf, UnitContent.bits, List.getD_eq_getElem?_getD]

private theorem mem_allBits_iff {n : ℕ} {w : List Bool} : w ∈ allBits n ↔ w.length = n := by
  refine ⟨length_of_mem_allBits, fun h => ?_⟩
  induction n generalizing w with
  | zero => simp_all [allBits]
  | succ n ih =>
    obtain ⟨b, w, rfl⟩ := List.exists_cons_of_length_eq_add_one h
    cases b <;> simp [allBits, ih (by simpa using h)]

private theorem nodup_allBits (n : ℕ) : (allBits n).Nodup := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
    rw [allBits, List.nodup_append]
    exact ⟨ih.map fun _ _ h => by simpa using h, ih.map fun _ _ h => by simpa using h,
      by simp⟩

/-- The options of the content of a unit: any `ub` bits if it is cut, and none otherwise. -/
private def contentOptions (ub : ℕ) (c : Bool) : List (UnitContent ub) :=
  if c then (allBits ub).map (contentOf ub) else [none]

private theorem nodup_contentOptions (ub : ℕ) (c : Bool) : (contentOptions ub c).Nodup := by
  cases c
  · simp [contentOptions]
  · refine (nodup_allBits ub).map_on fun w hw w' hw' h => ?_
    have := congrArg UnitContent.bits h
    rw [bits_contentOf (mem_allBits_iff.1 hw), bits_contentOf (mem_allBits_iff.1 hw')] at this
    exact List.reverse_injective this

private theorem mem_contentOptions {ub : ℕ} {c : Bool} {w : UnitContent ub} :
    w ∈ contentOptions ub c ↔ (w ≠ none ↔ c = true) := by
  cases c
  · simp [contentOptions]
  · simp only [contentOptions, ↓reduceIte, List.mem_map, iff_true]
    refine ⟨fun ⟨u, _, h⟩ => h ▸ Option.some_ne_none _, fun h => ?_⟩
    obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
    refine ⟨(List.ofFn v).reverse, mem_allBits_iff.2 (by simp), ?_⟩
    simp only [contentOf, List.reverse_reverse, Option.some.injEq]
    funext j
    simp [List.getD_eq_getElem?_getD]

omit [Fintype S] [DecidableEq S] in
private theorem sum_contentSteps {B : Type} [CommRing B] {ub : ℕ}
    {st : PlanName S M U0 U1 pS → Tree} {cut : UnitId (K + K) U0 M.Channel U1 → Bool}
    (hc : ∀ u, st (.isCut u) = bit (cut u)) (h0 : ∀ u, st (.content u) = .nil)
    (Φ : (List Bool → Tree) → B) :
    ((execAll ub C.contentSteps (extend C.name st fun _ => .nil)).map Φ).sum =
      ∑ b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub, if ∀ u, b u ≠ none ↔ cut u = true then
        Φ (extend C.name (extend Name.content (fun u => ofBits (b u).bits) st) fun _ => .nil)
      else 0 := by
  classical
  rw [Codes.contentSteps, execAll_choices (L := fun st => extend C.name st fun _ => .nil)
    (ov := fun u w st => update st (.content u) (ofBits (UnitContent.bits w)))
    (good := fun st : PlanName S M U0 U1 pS → Tree => (∀ u, st (.isCut u) = bit (cut u)) ∧
      ∀ u, cut u = false → st (.content u) = .nil) (fun u st hst => ?_)
    (fun u st w hw hst => ⟨fun u' => ?_, fun u' hu' => ?_⟩) (nodup_toList _)
    ⟨hc, fun u _ => h0 u⟩ (fun _ => none),
    sum_funs _ (fun u => nodup_contentOptions ub (cut u)) _ (nodup_toList _)]
  · refine sum_congr rfl fun b _ => ?_
    have key : ((∀ u ∈ (univ : Finset _).toList, b u ∈ contentOptions ub (cut u)) ∧
        ∀ u ∉ (univ : Finset _).toList, b u = none) ↔ ∀ u, b u ≠ none ↔ cut u = true := by
      simp [mem_contentOptions]
    by_cases hb : ∀ u, b u ≠ none ↔ cut u = true
    · rw [ite_eq_left (key.2 hb), ite_eq_left hb,
        foldl_update_eq_extend (fun _ _ h => Name.content.inj h) _
          fun u => mem_toList.2 (mem_univ u)]
    · rw [ite_eq_right (mt key.1 hb), ite_eq_right hb]
  · rw [exec_bits C.name_injective, hst.1]
    cases h : cut u
    · have e : update st (.content u) (ofBits (UnitContent.bits (none : UnitContent ub))) = st := by
        rw [show ofBits (UnitContent.bits (none : UnitContent ub)) = st (.content u) from
          (hst.2 u h).symm, update_eq_self]
      simp [bit, contentOptions, e]
    · simp only [bit, ↓reduceIte, one, reduceCtorEq, contentOptions, List.map_map]
      exact List.map_congr_left fun w hw => by
        simp [bits_contentOf (mem_allBits_iff.1 hw)]
  · simp [hst.1]
  · by_cases hu : u' = u
    · subst hu
      simp only [hu', contentOptions, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hw
      simp [hw, UnitContent.bits, ofBits]
    · simp [hu, hst.2 u' hu']

end Contents

/-! ### All runs -/

section Total

variable {Q : Type} [Fintype Q] [DecidableEq Q] (pt : Fin K → Tree) (qn : Q → ℕ)
  (hU0 : U0 < D) (hU1 : U1 ≤ D) (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K))
  (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
  [DecidablePred tab.Valid] [∀ n o x, Decidable (P.Good n o x)]

omit [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] [DecidablePred tab.Valid]
  [∀ n o x, Decidable (P.Good n o x)] in
private theorem final_extend_content {ub ub' : ℕ}
    {b' : UnitId (K + K) U0 M.Channel U1 → UnitContent ub'}
    {st : PlanName S M U0 U1 pS → Tree} (h : Final C tab qn pt q ρ n o b' st)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    Final C tab qn pt q ρ n o b (extend Name.content (fun u => ofBits (b u).bits) st) where
  part κ := by simp [extend_apply', h.part]
  state a := by simp [extend_apply', h.state]
  flags s p := by simp [extend_apply', h.flags]
  writeKeys p p' := by simp [extend_apply', h.writeKeys]
  readKeys p p' := by simp [extend_apply', h.readKeys]
  selfAgree p := by simp [extend_apply', h.selfAgree]
  newKeys ν d := by simp [extend_apply', h.newKeys]
  gate k := by simp [extend_apply', h.gate]
  count x := by simp [extend_apply', h.count]
  content u := (show Injective (Name.content : _ → PlanName S M U0 U1 pS) from
    fun _ _ h => Name.content.inj h).extend_apply _ _ _

/-- **The runs of the dealing program.** There are states `st q ρ n o b` with the values of the
end (`Final`) such that the sum over the states after all steps of the dealing program, from the
parts `pt` of the input, is the sum over the states `q` between the blocks from `i` to `e`, the
valid row data `ρ`, the valid numbers of units `n`, the good outcomes `o` and the contents `b` of
the units that are present exactly for the units cut between two groups, at the states
`st q ρ n o b`. -/
theorem sum_execAll_allSteps {ub : ℕ} (hK : 0 < K) (i e : Q) :
    ∃ st : (Fin (K + 1) → Q) → (Option S → Fin (K + K) → RowData (K + K)) →
      (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) → (M.Channel → Fin U1) →
        (UnitId (K + K) U0 M.Channel U1 → UnitContent ub) → PlanName S M U0 U1 pS → Tree,
      (∀ q ρ n o b, Final C tab qn pt q ρ n o b (st q ρ n o b)) ∧
      ∀ (B : Type) [CommRing B] (Φ : (List Bool → Tree) → B),
        ((execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
          (extend C.name (initialState pt) fun _ => .nil)).map Φ).sum =
        ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
          ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
            ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), if tab.Valid n then
              ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
                ∑ b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub,
                  if ∀ u, b u ≠ none ↔ u ∈ Play.cutUnits (UnitId.holder M.channelParty)
                    (grp ⟨n, o⟩) (P.cur n o E) then
                    Φ (extend C.name (st q ρ n o b) fun _ => .nil) else 0
              else 0 else 0 else 0 else 0 := by
  obtain ⟨st, hst, hsum⟩ := sum_execAll_dealSteps (m := ub) C tab pt qn hU0 hU1 hK i e
  refine ⟨fun q ρ n o b => extend Name.content (fun u => ofBits (b u).bits) (st q ρ n o),
    fun q ρ n o b => final_extend_content C tab pt qn q ρ n o (hst q ρ n o).1 b, fun B _ Φ => ?_⟩
  rw [sum_execAll_append, hsum]
  refine sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
  have h9 : ∀ ρ n o, ((execAll ub C.contentSteps (extend C.name (st q ρ n o)
      fun _ => .nil)).map Φ).sum = ∑ b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub,
        if ∀ u, b u ≠ none ↔ u ∈ Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩)
          (P.cur n o E) then
          Φ (extend C.name (extend Name.content (fun u => ofBits (b u).bits) (st q ρ n o))
            fun _ => .nil) else 0 := fun ρ n o => by
    rw [sum_contentSteps C (hst q ρ n o).2 (hst q ρ n o).1.content]
    simp
  simp only [h9, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]

end Total

end Cslib.Circuits.Arithmetic.Separation.Dealing
