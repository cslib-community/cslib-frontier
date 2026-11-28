/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Group
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.GroupScript
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.BaseStep
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.BaseSums

/-!
# The script of a group: its value, its validity, and accepting runs

The program GROUP of the evaluator of [AnthropicVPVNP2026] computes the value of a group of
parties after the moves of a plan at the script of the group (`groupScript`): from the empty trie,
the weighted sum of `1` over the tries after the script is the value of the group
(`weightedSum_scriptSem_groupScript`), since the instructions of every base party and of every role
simulate its step (`simulates_base`, `simulates_role`) and the instructions of the end compare the
copies of the current units. All instructions of the script are valid (`valid_groupScript`). If
the script has an outcome at all, the numbers of units of the base parties of the group are
bounded (`count_le_of_accept`) and the outcomes of its roles are possible
(`outcome_eq_of_accept`).

## Main results

* `weightedSum_scriptSem_groupScript`: the value of a group at its script.
* `valid_groupScript`: the instructions of the script are valid.
* `count_le_of_accept`, `outcome_eq_of_accept`: what an outcome of the script tells.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source modules
`Nc.Grp.Group` and `Nc.Grp.Facts`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset Interpreter Interpreter.Tree List.StairRefinement

variable {F : Type} [CommRing F] {θ : List Bool → F} {Γ S Q : Type} [Fintype Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] {A' E K U0 U1 ub c T : ℕ}
  {G : Type} [DecidableEq G] {M : Moves F (K + K + A') E}
  (mu : Tape.Letter S Unit Γ → Matrix Q Q F) (cb : Option Γ → Fin c → Bool)
  (kinds : List (Σ L : Cut.Law F, L.Role)) {P : Plan M U0 U1} {q : Fin (K + 1) → Q}
  {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G} {key : Cell M U0 U1 → List Bool}
  {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.Role → ℕ}

/-! ### The value of a group -/

private theorem weightedSum_scriptSem_append (l l' : List Instruction) (t : Tree) (Ψ : Tree → F) :
    (scriptSem θ mu cb kinds T ub (l ++ l') t).weightedSum Ψ =
      (scriptSem θ mu cb kinds T ub l t).weightedSum fun t' =>
        (scriptSem θ mu cb kinds T ub l' t').weightedSum Ψ := by
  induction l generalizing t with
  | nil => simp
  | cons i l ih => simp only [List.cons_append, scriptSem_cons, List.weightedSum_weightedBind, ih]

/-- Instructions that simulate a list of steps, followed by `J`, make the sum over the executions
of the steps of what `J` makes. -/
private theorem weightedSum_scriptSem_steps {ι : Type*} (I : ι → List Instruction)
    (s : ι → WriteStep F (Cell M U0 U1) (UnitContent ub)) (J : List Instruction)
    (Gf : (Cell M U0 U1 → UnitContent ub) → F)
    (hJ : ∀ t σ, Stores ub key t σ →
      (scriptSem θ mu cb kinds T ub J t).weightedSum (fun _ => 1) = Gf σ) :
    ∀ l : List ι, (∀ i ∈ l, Simulates θ mu cb kinds T key (I i) (s i)) → ∀ {t σ},
      Stores ub key t σ → (scriptSem θ mu cb kinds T ub (l.flatMap I ++ J) t).weightedSum
        (fun _ => 1) = WriteStep.exec (l.map s) Gf σ
  | [], _, t, σ, hst => hJ t σ hst
  | i :: l, h, t, σ, hst => by
    rw [List.flatMap_cons, List.append_assoc, weightedSum_scriptSem_append, List.map_cons,
      WriteStep.exec_cons]
    exact h i List.mem_cons_self t σ _ _ hst fun t' σ' h' =>
      weightedSum_scriptSem_steps I s J Gf hJ l (fun j hj => h j (List.mem_cons_of_mem _ hj)) h'

/-- The instructions of the end compare the copies of the current units of the group. -/
private theorem weightedSum_scriptSem_end (hub : 0 < ub) {t : Tree}
    {σ : Cell M U0 U1 → UnitContent ub} (hst : Stores ub key t σ)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    (scriptSem θ mu cb kinds T ub (endInstructions P n o grp g key b) t).weightedSum (fun _ => 1) =
      if Play.GroupAgree (UnitId.holder M.channelParty) grp g (P.cur n o E) b
        (fun a u => σ ⟨a, u⟩) then 1 else 0 := by
  classical
  rw [scriptSem_of_checks mu cb kinds T (fun i => instructionSem θ mu cb kinds T ub i t ≠ [])
    fun i hi => ?_]
  · have hσ (c c' : Cell M U0 U1) : tget (key c) t = tget (key c') t ↔ σ c = σ c' := by
      simpa only [hst.2] using (ofBits_bits_injective hub).eq_iff
    have hσb (c : Cell M U0 U1) (w : UnitContent ub) :
        tget (key c) t = ofBits w.bits ↔ σ c = w := by
      simpa only [hst.2] using (ofBits_bits_injective hub).eq_iff
    have h : (∀ i ∈ endInstructions P n o grp g key b, instructionSem θ mu cb kinds T ub i t ≠ []) ↔
        Play.GroupAgree (UnitId.holder M.channelParty) grp g (P.cur n o E) b
          (fun a u => σ ⟨a, u⟩) := by
      simp only [endInstructions, List.forall_mem_filterMap, List.mem_filter, UnitId.list,
        mem_toList, mem_univ, true_and, decide_eq_true_eq]
      refine ⟨fun h => ⟨fun u hu h0 h1 => ?_, fun u hu d hd hd' => ?_⟩, fun h u hu i hi => ?_⟩
      · simpa [h0, h1, instructionSem, hσ] using h u hu
      · cases d <;> simp only [Bool.not_false, Bool.not_true] at hd' <;>
          simpa [hd, hd', instructionSem, hσb] using h u hu
      · split_ifs at hi with h0 h1 h1 <;> cases hi
        · simpa [instructionSem, hσ] using h.inner u hu h0 h1
        · simpa [instructionSem, hσb] using h.outer u hu false h0 h1
        · simpa [instructionSem, hσb] using h.outer u hu true h1 h0
    by_cases hg : Play.GroupAgree (UnitId.holder M.channelParty) grp g (P.cur n o E) b
      (fun a u => σ ⟨a, u⟩) <;> simp [h, hg]
  · obtain ⟨u, -, hu⟩ := List.mem_filterMap.1 hi
    split_ifs at hu <;> cases hu <;> simp only [instructionSem] <;> split_ifs <;> simp_all

/-- **The value of a group at its script.** From the empty trie, the weighted sum of `1` over the
tries after the script of the group `g` is the value of the group after the moves of the plan
`P`, for the contents `b` of the units that it shares with other groups. -/
theorem weightedSum_scriptSem_groupScript [DecidableEq Γ] [DecidableEq Q] {cap : ℕ}
    (hκ : Function.Injective (Sum.elim key dkey))
    (hub : 0 < ub) (hP : P.Ok cap) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩)
    (htab : ∀ (r : M.Role) i v g', ∃ e : WE, e.val θ = (M.law r.1).table r.2 i v g')
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    (scriptSem θ mu cb kinds T ub (groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb P q x ρ n o
      grp g key dkey tg b) .nil).weightedSum (fun _ => 1) =
      P.groupValue mu T cb q x ρ n o grp g b := by
  rw [groupValue_eq_exec hP]
  let I : Fin (K + K) ⊕ M.Role → List Instruction := Sum.elim
    (baseInstructions (fun z => (Fintype.equivFin Q z : ℕ)) cb q x ρ n key dkey)
    fun r => [roleInstruction P n o key tg r]
  let s : Fin (K + K) ⊕ M.Role → WriteStep F (Cell M U0 U1) (UnitContent ub) :=
    Sum.elim (baseWriteStep mu T cb q x ρ n o grp g) (roleWriteStep P n o grp g)
  let l := (baseParties grp g).map Sum.inl ++ (groupRoles grp g M).map Sum.inr
  rw [show groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b =
      l.flatMap I ++ endInstructions P n o grp g key b by
      simp only [l, I, groupScript, List.flatMap_append, List.flatMap_map, Sum.elim_inl,
        Sum.elim_inr, List.append_assoc, ← List.map_eq_flatMap],
    show groupSteps mu T cb P q x ρ n o grp g ub = l.map s by
      simp [l, s, groupSteps, Function.comp_def]]
  refine weightedSum_scriptSem_steps mu cb kinds I s _ _
    (fun t σ hst => weightedSum_scriptSem_end mu cb kinds hub hst b) l ?_ (Stores.nil key)
  rintro (p | r) hi <;> simp only [l, List.mem_append, List.mem_map, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, and_false, exists_false, or_false, false_or,
    exists_eq_right] at hi
  · exact simulates_base mu cb kinds hκ hub hmu hx (mem_baseParties.1 hi) (hρ · p)
  · exact simulates_role mu cb kinds T (hκ.comp Sum.inl_injective) hub (mem_groupRoles.1 hi)
      (hkind r) (htab r)

omit [Fintype Γ] [DecidableEq S] in
/-- **The instructions of the script of a group are valid** for GROUP, if the roles are numbered
as in the list `kinds`. -/
theorem valid_groupScript (hkind : ∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    ∀ i ∈ groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b,
      i.Valid Q c kinds := by
  intro i hi
  simp only [groupScript, List.mem_append, List.mem_flatMap, List.mem_map] at hi
  rcases hi with (⟨p, -, hi⟩ | ⟨r, -, rfl⟩) | hi
  · rcases List.mem_cons.1 hi with rfl | hi
    · induction p using Fin.addCases <;> simp [Instruction.Valid, letterCode, -Fin.natAdd_eq_addNat]
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
      trivial
  · exact ⟨_, hkind r, by simp [slotList]⟩
  · obtain ⟨u, -, hu⟩ := List.mem_filterMap.1 hi
    split_ifs at hu <;> cases hu <;> trivial

/-! ### Accepting runs -/

private theorem exists_of_scriptSem_ne_nil : ∀ {l : List Instruction} {t : Tree},
    scriptSem θ mu cb kinds T ub l t ≠ [] →
      ∀ i ∈ l, ∃ t', instructionSem θ mu cb kinds T ub i t' ≠ []
  | [], _, _, i, hi => absurd hi List.not_mem_nil
  | j :: l, t, h, i, hi => by
    rw [scriptSem_cons] at h
    obtain ⟨a, ha, r, hr, -⟩ :=
      List.mem_weightedBind_iff.1 (List.exists_mem_of_ne_nil _ h).choose_spec
    rcases List.mem_cons.1 hi with rfl | hi
    · exact ⟨t, List.ne_nil_of_mem ha⟩
    · exact exists_of_scriptSem_ne_nil (List.ne_nil_of_mem hr) i hi

omit [Fintype Γ] [DecidableEq S] in
/-- If a base party with the letters `w` on the sides of the tapes, at most `T` on the sides `d`
of all tapes, has an outcome, its numbers of units are bounded. -/
private theorem count_le_of_packSem_ne_nil [Finite Γ] (hub : 0 < ub) {p : Fin (K + K)}
    (hρ : ∀ s, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last)
    {w : Option S × Bool → List Γ} (hw : ∀ d, ∑ s, (w (s, d)).length ≤ T) {out : Outputs S}
    (ho : ∀ j, out j = ((w (outputSide j)).map (letterCode cb)).reverse) {t : Tree}
    (h : packSem F (separator cb) ub (baseBody ρ n key dkey p) out t ≠ []) :
    ∑ b, ((n p b : ℕ) + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  classical
  have hl := sum_map_packSem (F := F) (M' := ℕ) (T := T) (ub := ub) cb ρ n key dkey hρ (fun z =>
    (single_le_sum (f := fun s => (w (s, z.2)).length) (fun _ _ => Nat.zero_le _)
      (mem_univ z.1)).trans (hw z.2)) ho t fun _ => 1
  simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul,
    mul_one] at hl
  obtain ⟨R, -, hR⟩ := exists_ne_zero_of_sum_ne_zero (hl ▸ (List.length_pos_iff.2 h).ne')
  obtain ⟨⟨hcR, -⟩, hR⟩ := ite_ne_right_iff.1 hR
  obtain ⟨y, hy, ht⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hR
  obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.1 hy
  obtain ⟨C, -, hC⟩ := exists_ne_zero_of_sum_ne_zero ht
  obtain ⟨hcC, hC⟩ := ite_ne_right_iff.1 hC
  have cR := unitCount_eq_of_putStrings_ne_nil hub (List.ofFn fun b =>
    ((indicesBelow (n p b)).map fun k => key ⟨Fin.castAdd A' p, .init p b k⟩,
      segmentString cb fun s => R s b)) t (by
        simpa [baseBody, List.map_ofFn, Function.comp_def] using List.ne_nil_of_mem ht₁)
  have cC := unitCount_eq_of_putStrings_ne_nil hub (List.ofFn fun b =>
    ((indicesBelow (n b p)).map fun k => if b = p then dkey (p, k) else
      key ⟨Fin.castAdd A' p, .init b p k⟩, segmentString cb fun s => C s b)) t₁ (by
        simpa [baseBody, List.map_ofFn, Function.comp_def] using
          List.length_pos_iff.1 (Nat.pos_of_ne_zero hC))
  simp only [List.forall_mem_ofFn_iff, List.length_map, length_indicesBelow] at cR cC
  have e1 := sum_unitCount_le (ub := ub) (cb := cb) (X := R) (by simp only [hcR]; exact hw false)
  have e2 := sum_unitCount_le (ub := ub) (cb := cb) (X := C) (by simp only [hcC]; exact hw true)
  simp only [cR, cC, Fintype.card_option] at e1 e2
  rw [sum_add_distrib]; omega

variable (P q x ρ n o grp g key dkey tg) in
/-- **An accepting run bounds the units of the base parties.** If the script of a group has an
outcome, every base party `p` of the group has at most twice the units that its letters allow. -/
theorem count_le_of_accept (hub : 0 < ub) (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last)
    {b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub} {t : Tree}
    (h : scriptSem θ mu cb kinds T ub (groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb P q x ρ
      n o grp g key dkey tg b) t ≠ []) {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g) :
    ∑ b, ((n p b : ℕ) + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  obtain ⟨t', ht'⟩ := exists_of_scriptSem_ne_nil mu cb kinds h _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, mem_baseParties.2 hp, List.mem_cons_self⟩)))
  induction p using Fin.addCases with
  | left κ =>
    rw [Fin.addCases_left, instructionSem, dite_eq_left_of_eq_true (eq_true ⟨(Fintype.equivFin Q
      _).isLt, (Fintype.equivFin Q _).isLt⟩)] at ht'
    obtain ⟨a, ha, r, hr, -⟩ :=
      List.mem_weightedBind_iff.1 (List.exists_mem_of_ne_nil _ ht').choose_spec
    obtain ⟨u, hu, hout⟩ := exists_of_mem_simSem mu cb ha
    exact count_le_of_packSem_ne_nil cb hub (hρ · _) (w := sideLetters u)
      (fun d => hu ▸ sum_length_sideLetters_le u d) (fun j => congrFun hout j)
      (List.ne_nil_of_mem hr)
  | right κ =>
    rw [Fin.addCases_right, instructionSem] at ht'
    refine count_le_of_packSem_ne_nil cb hub (hρ · _)
      (w := fun z => if z = (none, false) then x κ else []) (fun d => ?_)
      (fun j => by simp only [inputOutputs]; split_ifs <;> simp) ht'
    cases d <;> simp [Fintype.sum_option, hx κ]

variable (P q x ρ n o grp g key dkey tg) in
/-- **An accepting run gives possible outcomes.** If the script of a group has an outcome, the
outcome of every role of the group is possible: there are indices of the law for the bits of the
move whose strings on every channel of the role fill as many units as the outcome says. -/
theorem outcome_eq_of_accept (hub : 0 < ub) (hkind : ∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩)
    {b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub} {t : Tree}
    (h : scriptSem θ mu cb kinds T ub (groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb P q x ρ
      n o grp g key dkey tg b) t ≠ []) {r : M.Role} (hr : grp (M.roleParty r) = g) :
    ∃ ι : Fin (P.count n o r.1 * ub) → (M.law r.1).Index, ∀ ν : (M.law r.1).ChannelAt r.2,
      (o ⟨r.1, ν.val⟩ : ℕ) =
        (∑ k, ((M.law r.1).labelLength + (M.law r.1).length (ι k) ν)) / ub := by
  obtain ⟨t', ht'⟩ := exists_of_scriptSem_ne_nil mu cb kinds h _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨r, mem_groupRoles.2 hr, rfl⟩)))
  simp only [roleInstruction, instructionSem, hkind, roleSem] at ht'
  obtain ⟨_, ht'⟩ := ite_ne_right_iff.1 ht'
  obtain ⟨a, ha, z, hz, -⟩ :=
    List.mem_weightedBind_iff.1 (List.exists_mem_of_ne_nil _ ht').choose_spec
  obtain ⟨ι, hι⟩ := exists_of_mem_run_roleTable _ _ ha
  have hc := unitCount_eq_of_putStrings_ne_nil hub (List.ofFn fun i =>
    ((indicesBelow (o ⟨r.1, ((channelList (M.law r.1) r.2).get i).val⟩).succ).map fun k =>
      key ⟨M.roleParty r, .new ⟨r.1, ((channelList (M.law r.1) r.2).get i).val⟩ k⟩,
      (a.2.outputs i).reverse)) t' (by
        simpa [List.map_ofFn, Function.comp_def, ← List.ofFn_getElem_eq_map] using
          List.ne_nil_of_mem (List.mem_map.1 hz).choose_spec.1)
  refine ⟨ι, fun ν => ?_⟩
  have hj := List.idxOf_lt_length_of_mem (l := channelList (M.law r.1) r.2)
    (mem_toList.2 (mem_univ ν))
  have := hc _ (List.mem_ofFn.2 ⟨⟨_, hj⟩, rfl⟩)
  simp [unitCount, hι, List.get_eq_getElem] at this; omega

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
