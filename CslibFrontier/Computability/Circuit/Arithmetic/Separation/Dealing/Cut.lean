/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.AllRuns
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Theorem
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccProg
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.FinalTables

/-!
# One cut by the dealing program

The dealing program of [AnthropicVPVNP2026] (`Codes.dealProgram`) writes the word of the letters
of its argument `z` (the bits `tbits z`, as the letters `bt`), cuts it into parts (`partTree`),
runs its steps, and fills one template for every group (`Codes.pieceTm`): the instance of the
program GROUP at the script of the group. Every state after its steps has the values of the end
(`mem_execAll_allSteps`), so the filled templates are the instances of GROUP at the scripts of
the groups. If the value of a universal automaton on the word is the plain sum of `z`, the
formula of the pieces gives that value as a sum over the choices, and the instances of GROUP are
small, plain and have the values of the groups, then the dealing program cuts plain sums into
pieces (`isCut_dealProgram`).

## Main definitions

* `partTree`: a part of the input, as the list of the codes of its letters.
* `Codes.pieceTm`: the template of the instance of GROUP at the script of a group.
* `Codes.dealProgram`: the dealing program.

## Main results

* `gets_partsT_eq_initialState`: the parts of the word, written at the names of the parts.
* `mem_execAll_allSteps`: every state after all steps has the values of the end.
* `mem_execAll_dealSteps`: every state after the steps up to the checks says which units are
  cut.
* `isCut_dealProgram`: the dealing program makes one cut.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54). Ported from the source module `Nc.Dl.Cut` and the states after the steps
of `Nc.Dl.Bd2`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- The part `κ` of the input `x`, as the list of the codes of its letters, last letter first. -/
def partTree {Γ : Type} {K c : ℕ} (cb : Option Γ → Fin c → Bool) (x : Fin K → List Γ)
    (κ : Fin K) : Tree :=
  wordsEnc (((x κ).map (letterCode cb)).reverse)

section Program

variable {F : Type} [CommSemiring F] {Γ S Q : Type} [Fintype S] [Fintype Q]
  {K A' E U0 U1 D nI pS mm ub c : ℕ} {M : Moves F (K + K + A') E}
  {P : Plan M U0 U1} {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}
  (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D nI pS)

/-! ### The states after the steps -/

section States

/-- A nonzero sum of conditional terms has a term whose condition holds. -/
private theorem exists_of_sum_ite_ne_zero {ι : Type*} [Fintype ι] {p : ι → Prop}
    [DecidablePred p] {f : ι → ℤ} (h : (∑ i, if p i then f i else 0) ≠ 0) : ∃ i, p i ∧ f i ≠ 0 :=
  let ⟨i, _, hi⟩ := exists_ne_zero_of_sum_ne_zero h
  ⟨i, ite_ne_right_iff.1 hi⟩

/-- The indicator of a member of a list sums to a nonzero value over the list. -/
private theorem sum_map_indicator_ne_zero {α : Type*} [DecidableEq α] {l : List α} {a : α}
    (h : a ∈ l) : (l.map fun b => if b = a then (1 : ℤ) else 0).sum ≠ 0 := by
  have : (1 : ℤ) ≤ (l.map fun b => if b = a then (1 : ℤ) else 0).sum :=
    List.single_le_sum (fun x hx => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; split_ifs <;> simp)
      _ (List.mem_map.2 ⟨a, h, ite_eq_left rfl⟩)
  omega

/-- **The states after all steps.** Every state after all steps of the dealing program, from the
parts `pt` of the input, has the values of the end (`Final`) for states `q` between the blocks
from `i` to `e`, valid row data `ρ`, valid numbers of units `n`, good outcomes `o` and contents
`b` that are present exactly for the cut units. -/
theorem mem_execAll_allSteps (hK : 0 < K) {pt : Fin K → Tree} {qn : Q → ℕ} {i e : Q}
    {hU0 : U0 < D} {hU1 : U1 ≤ D} {σ : List Bool → Tree}
    (hσ : σ ∈ execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
      (extend C.name (initialState pt) fun _ => .nil)) :
    ∃ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K))
      (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
      (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) (st : PlanName S M U0 U1 pS → Tree),
      (q 0 = i ∧ q (Fin.last K) = e) ∧ ValidRows ρ ∧ tab.Valid n ∧ (∀ x, P.Good n o x) ∧
      (∀ u, b u ≠ none ↔ u ∈ Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩)
        (P.cur n o E)) ∧ Final C tab qn pt q ρ n o b st ∧ σ = extend C.name st fun _ => .nil := by
  classical
  obtain ⟨st, hf, hs⟩ := sum_execAll_allSteps (ub := ub) C tab pt qn hU0 hU1 hK i e
  have h := sum_map_indicator_ne_zero hσ
  rw [hs] at h
  obtain ⟨q, hq, h⟩ := exists_of_sum_ite_ne_zero h
  obtain ⟨ρ, hρ, h⟩ := exists_of_sum_ite_ne_zero h
  obtain ⟨n, hn, h⟩ := exists_of_sum_ite_ne_zero h
  obtain ⟨o, ho, h⟩ := exists_of_sum_ite_ne_zero h
  obtain ⟨b, hb, h⟩ := exists_of_sum_ite_ne_zero h
  exact ⟨q, ρ, n, o, b, _, hq, hρ, hn, ho, hb, hf q ρ n o b, (ite_ne_right_iff.1 h).1.symm⟩

/-- **The states after the steps up to the checks.** Every state after `Codes.dealSteps`, from the
parts `pt` of the input, is a state by names `st` that has the bits that say which units are cut,
for valid numbers of units `n` and good outcomes `o`. -/
theorem mem_execAll_dealSteps (hK : 0 < K) {pt : Fin K → Tree} {qn : Q → ℕ} {i e : Q} {m : ℕ}
    {hU0 : U0 < D} {hU1 : U1 ≤ D} {σ : List Bool → Tree}
    (hσ : σ ∈ execAll m (C.dealSteps tab qn i e hU0 hU1)
      (extend C.name (initialState pt) fun _ => .nil)) :
    ∃ (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
      (st : PlanName S M U0 U1 pS → Tree), tab.Valid n ∧ (∀ x, P.Good n o x) ∧
      (∀ u, st (.isCut u) = bit (decide (u ∈ Play.cutUnits (UnitId.holder M.channelParty)
        (grp ⟨n, o⟩) (P.cur n o E)))) ∧ σ = extend C.name st fun _ => .nil := by
  classical
  obtain ⟨st, hf, hs⟩ := sum_execAll_dealSteps (m := m) C tab pt qn hU0 hU1 hK i e
  have h := sum_map_indicator_ne_zero hσ
  rw [hs] at h
  obtain ⟨q, -, h⟩ := exists_of_sum_ite_ne_zero h
  obtain ⟨ρ, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨n, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨o, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨⟨-, hn, ho⟩, h⟩ := ite_ne_right_iff.1 h
  exact ⟨n, o, _, hn, ho, (hf q ρ n o).2, (ite_ne_right_iff.1 h).1.symm⟩

end States

/-! ### The dealing program -/

namespace Codes

/-- The template of the instance of the program GROUP, of code `gp`, at the script of the group
`g` (`Codes.scriptTm`). -/
@[expose] noncomputable def pieceTm (tg : M.Role → ℕ) (bT bub : List Bool) (hD : 1 < D)
    (hmm : mm ≤ D) (gp : Tree) (g : Fin mm) : Tm :=
  .cons (.c gp) (C.scriptTm tab tg bT bub hD hmm g)

/-- **The dealing program.** It writes the word of its argument with the codes of the letters
`bt false` for a leaf and `bt true` for a node, cuts it into parts of `KT.val nl` letters at the
names of the parts, runs the steps up to the checks (`Codes.dealSteps`), guesses the contents of
the cut units (`Codes.contentSteps`) with `KT.val nub` bits each, and fills the template of the
instance of GROUP, of code `gp`, for every group. -/
@[expose] noncomputable def dealProgram (qn : Q → ℕ) (tg : M.Role → ℕ) (bT bub nl nub : List Bool)
    (hD : 1 < D) (hmm : mm ≤ D) (gp : Tree) (cb : Option Γ → Fin c → Bool) (bt : Bool → Γ)
    (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D) : Fm :=
  dealFormula (ofBits (letterCode cb (bt false))) (ofBits (letterCode cb (bt true)))
    ((List.finRange K).map fun κ => C.name (.part κ)) nl nub (C.dealSteps tab qn i e hU0 hU1)
    C.contentSteps ((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp))

end Codes

omit [Fintype S] [Fintype Q] in
/-- **The parts at their names.** Writing the parts of `ℓ` letters of the word of `z` at the
names of the parts, into the empty trie, gives the state at the beginning (`initialState`) with
the parts as lists of the codes of their letters (`partTree`). -/
theorem gets_partsT_eq_initialState (cb : Option Γ → Fin c → Bool) (bt : Bool → Γ) (ℓ : ℕ)
    (z : Tree) :
    gets (partsT ℓ ((List.finRange K).map fun κ => C.name (.part κ)) .nil
      (wordT (ofBits (letterCode cb (bt false))) (ofBits (letterCode cb (bt true))) z)) =
      extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt)))) fun _ => .nil := by
  classical
  obtain ⟨st, h1, h2, h3⟩ := gets_partsT C.name_injective ℓ ((List.finRange K).map Name.part)
    ((List.nodup_finRange K).map fun _ _ h => Name.part.inj h) .nil
    (wordT (ofBits (letterCode cb (bt false))) (ofBits (letterCode cb (bt true))) z) (fun _ => .nil)
    (by rw [gets_nil]; funext p; by_cases hp : ∃ y, C.name y = p <;> simp [extend, hp])
  rw [List.map_map] at h1
  refine h1.trans (congrArg (extend C.name · _) (funext fun y => ?_))
  cases y with
  | part κ =>
    have := h2 κ (by simp)
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at this
    rw [this, wordT_eq_map_tbits (fun d => ofBits (letterCode cb (bt d)))]
    simp [initialState, partTree, parts, wordsEnc, List.map_reverse, List.map_take, List.map_drop,
      Function.comp_def]
  | _ => exact h3 _ (by simp)

end Program

/-! ### One cut -/

section Cut

/-- The sum over the contents that are empty off the cut units is the sum over the contents that
are present exactly on them, if the terms vanish unless the cut units are present. -/
private theorem sum_common_eq_sum_ite {U W R : Type*} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [AddCommMonoid R] (e : W) (cut : Finset U) {f : (U → W) → R}
    (hf : ∀ b, f b ≠ 0 → ∀ u ∈ cut, b u ≠ e) :
    ∑ b ∈ Play.common e cut, f b = ∑ b, if ∀ u, b u ≠ e ↔ u ∈ cut then f b else 0 := by
  classical
  rw [← sum_filter]
  refine (sum_subset (fun b hb => Play.mem_common.2 fun u hu => ?_) fun b hb hb' => ?_).symm
  · exact of_not_not fun h => hu (((mem_filter.1 hb).2 u).1 h)
  · by_contra h
    refine hb' (mem_filter.2 ⟨mem_univ _, fun u => ⟨fun hu => ?_, hf b h u⟩⟩)
    exact of_not_not fun h' => hu (Play.mem_common.1 hb u h')

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {K A' E U0 U1 D nI pS mm ub c : ℕ}
  {M : Moves F (K + K + A') E} {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS)
  (tab : SlpTab P grp D nI pS) [DecidablePred tab.Valid] [∀ n o x, Decidable (P.Good n o x)]
  {θ : List Bool → F} {mu : Tape.Letter S Unit Γ → Matrix Q Q F} {qn : Q → ℕ} {tg : M.Role → ℕ}
  {bT bub nl nub : List Bool} {hD : 1 < D} {hmm : mm ≤ D} {gp : Tree}
  {cb : Option Γ → Fin c → Bool} {bt : Bool → Γ} {i e : Q} {hU0 : U0 < D} {hU1 : U1 ≤ D}
  {τ s τ' s' t T ℓ : ℕ}

/-- **One cut.** Suppose that, for every argument `z` of size at most `s`, with the parts `x` of
`ℓ = KT.val nl` letters of its word:
* the automaton `mu` has, on the word, the value `pv θ z` if `z` is `τ`-plain (`hU`);
* that value is the sum, over the states `q` from `i` to `e`, the valid row data `ρ`, the valid
  numbers of units `n`, the good outcomes `o` and the contents `b` of the cut units that are
  empty off them, of the products of the values of the groups (`hval`);
* the dealing program has the weighted list of the filled templates along its runs, in time `t`
  (`hdoes`);
* for every choice that passes the checks, the instance of GROUP at the script of every group has
  size at most `s'`, is `τ'`-plain and has the value of the group (`hpc`).

Then the dealing program cuts `(τ, s)` into `(τ', s')` with at most `mm` pieces in `t` steps. -/
theorem isCut_dealProgram (hK : 0 < K) (hnl : KT.val nl = ℓ) (hnub : KT.val nub = ub)
    (hU : ∀ z : Tree, z.size ≤ s → Plain θ τ z →
      Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) = pv θ z)
    (hval : ∀ z : Tree, z.size ≤ s → Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), if tab.Valid n then
            ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
              ∑ b ∈ Play.common (none : UnitContent ub)
                (Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)),
                ∏ g, P.groupValue mu T cb q (parts ℓ ((tbits z).map bt)) ρ n o (grp ⟨n, o⟩) g b
            else 0 else 0 else 0 else 0)
    (hdoes : ∀ z : Tree, z.size ≤ s → ∃ Qs : List (F × Tree),
      Does θ (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1) z Qs t ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt)))) fun _ => .nil),
        q.2 = listT (((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)).map
          fun t => t.expand σ)) ∧
      wsum Qs (pvProd θ) = ((execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt)))) fun _ => .nil)).map
          fun σ => (((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)).map
            fun t => pv θ (t.expand σ)).prod).sum)
    (hpc : ∀ z : Tree, z.size ≤ s → ∀ (q : Fin (K + 1) → Q)
      (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (o : M.Channel → Fin U1) (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) (g : Fin mm),
      ValidRows ρ → tab.Valid n → (∀ x, P.Good n o x) →
      (∀ u, b u ≠ none ↔ u ∈ Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩)
        (P.cur n o E)) →
      let y := Tree.cons gp (scriptEnc bT bub (groupScript qn cb P q (parts ℓ ((tbits z).map bt))
        ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg b))
      y.size ≤ s' ∧ Plain θ τ' y ∧
        pv θ y = P.groupValue mu T cb q (parts ℓ ((tbits z).map bt)) ρ n o (grp ⟨n, o⟩) g b) :
    IsCut θ τ s τ' s' mm t
      (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1).code := by
  classical
  subst hnl hnub
  intro z hz
  obtain ⟨Qs, hD', hmem, hsum⟩ := hdoes z hz
  set x := parts (KT.val nl) ((tbits z).map bt)
  -- the templates at a state with the values of the end
  have hpiece {q ρ n o st} {b : UnitId (K + K) U0 M.Channel U1 → UnitContent (KT.val nub)}
      (hst : Final C tab qn (partTree cb x) q ρ n o b st) (g : Fin mm) :
      (C.pieceTm tab tg bT bub hD hmm gp g).expand (extend C.name st fun _ => .nil) =
        .cons gp (scriptEnc bT bub (groupScript qn cb P q x ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg
          b)) := by
    rw [Codes.pieceTm, Tm.expand, Tm.expand, expand_scriptTm hst fun _ => rfl]
  have hpieces : ∀ r ∈ Qs, r.2.toList.length = mm ∧ ∀ y ∈ r.2.toList, y.size ≤ s' ∧
      Plain θ τ' y := by
    intro r hr
    obtain ⟨σ, hσ, hr2⟩ := hmem r hr
    obtain ⟨q, ρ, n, o, b, st, -, hρ, hn, ho, hb, hst, rfl⟩ := mem_execAll_allSteps C tab hK hσ
    refine ⟨by simp [hr2], fun y hy => ?_⟩
    simp only [hr2, toList_listT, List.map_map, List.mem_map, List.mem_finRange, true_and,
      Function.comp_apply] at hy
    obtain ⟨g, rfl⟩ := hy
    rw [hpiece hst]
    exact ⟨(hpc z hz q ρ n o b g hρ hn ho hb).1, (hpc z hz q ρ n o b g hρ hn ho hb).2.1⟩
  refine ⟨Qs, by rwa [Fm.ofTree_code], fun r hr => ⟨(hpieces r hr).1.le,
    fun y hy => ((hpieces r hr).2 y hy).1⟩, fun hpl => ⟨fun r hr y hy => ((hpieces r hr).2 y hy).2,
    ?_⟩⟩
  obtain ⟨st, hf, hs⟩ := sum_execAll_allSteps (ub := KT.val nub) C tab (partTree cb x) qn hU0 hU1
    hK i e
  rw [hsum, ← hU z hz hpl, hval z hz, hs]
  refine sum_congr rfl fun q _ => ite_congr rfl (fun _ => sum_congr rfl fun ρ _ => ite_congr rfl
    (fun hρ => sum_congr rfl fun n _ => ite_congr rfl (fun hn => sum_congr rfl fun o _ =>
      ite_congr rfl (fun ho => ?_) fun _ => rfl) fun _ => rfl) fun _ => rfl) fun _ => rfl
  rw [sum_common_eq_sum_ite]
  · refine sum_congr rfl fun b _ => ite_congr rfl (fun hb => ?_) fun _ => rfl
    rw [List.map_map, ← Fin.prod_univ_def]
    exact prod_congr rfl fun g _ => by
      rw [Function.comp_apply, hpiece (hf q ρ n o b), (hpc z hz q ρ n o b g hρ hn ho hb).2.2]
  · intro b hb u hu
    obtain ⟨hcur, hne⟩ := Play.mem_cutUnits.1 hu
    exact P.ne_none_of_groupValue_ne_zero (d := false) (fun h0 => hb (prod_eq_zero (mem_univ _) h0))
      hcur rfl hne.symm

end Cut

end Cslib.Circuits.Arithmetic.Separation.Dealing
