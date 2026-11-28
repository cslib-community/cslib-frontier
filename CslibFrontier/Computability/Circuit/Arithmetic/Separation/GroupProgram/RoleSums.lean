/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Executions
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Group
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.NodupFlatMap
import Mathlib.Data.List.GetD

/-!
# The instructions of a role do what its step does

The program GROUP of [AnthropicVPVNP2026] keeps the contents of the cells of a group in a trie
(`Stores`). Its instructions *simulate* a step of the group (`Simulates`) if, from a trie that
stores some contents, their weighted list of tries is the sum over the choices of the step of
its weight times the trie of the contents that it writes.

This file has what the instructions of base parties and of roles share: writing strings closed by
the bit `1` at the keys of lists of cells (`putStrings_spec`) and comparisons
(`scriptSem_of_checks`); and the simulation of the step of a role by its instruction
(`simulates_role`), through the runs of the transducer of the role.

## Main definitions

* `Stores`: a trie stores the contents of the cells.
* `Simulates`: instructions simulate a step.

## Main results

* `Stores.nil`: the empty trie stores empty contents.
* `ofBits_bits_injective`: a unit of positive width is determined by its bits.
* `putStrings_spec`: writing strings at the keys of lists of items.
* `unitCount_eq_of_putStrings_ne_nil`: writing gives a trie only if the numbers of units fit.
* `scriptSem_of_checks`: a list of comparisons keeps the trie or rejects.
* `exists_of_mem_run_roleTable`: what a run of the transducer of a role writes.
* `simulates_role`: the instruction of a role simulates its step.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source modules
`Nc.Grp.PutSum`, `Nc.Grp.SumPut`, `Nc.Grp.SumRole` and `Nc.Grp.StepRole`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset Interpreter Interpreter.Tree

variable {F : Type} [CommRing F] {θ : List Bool → F} {Γ S Q : Type} [Fintype Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] {A' E K U0 U1 ub c : ℕ} {M : Moves F (K + K + A') E}

/-- The trie `t` stores the contents `σ` of the cells at the keys `key`: its entries are units of
at most `ub` bits, and the entry at the key of a cell has the bits of its contents. -/
@[expose] def Stores (ub : ℕ) (key : Cell M U0 U1 → List Bool) (t : Tree)
    (σ : Cell M U0 U1 → UnitContent ub) : Prop :=
  StoreBound ub t ∧ ∀ c, tget (key c) t = ofBits (σ c).bits

theorem Stores.nil (key : Cell M U0 U1 → List Bool) : Stores ub key .nil fun _ => none :=
  ⟨StoreBound.nil ub, fun _ => tget_nil _⟩

variable (θ) in
/-- The instructions `I` simulate the step `s`: from a trie that stores the contents `σ`, the
weighted sum of `Ψ` over the tries after the instructions is the sum over the choices of the step
of its weight times `Ψ'` at the contents after it, whenever `Ψ` and `Ψ'` agree at tries and the
contents that they store. -/
@[expose] def Simulates (mu : Tape.Letter S Unit Γ → Matrix Q Q F) (cb : Option Γ → Fin c → Bool)
    (kinds : List (Σ L : Cut.Law F, L.Role)) (T : ℕ) (key : Cell M U0 U1 → List Bool)
    (I : List Instruction) (s : WriteStep F (Cell M U0 U1) (UnitContent ub)) : Prop :=
  ∀ (t : Tree) (σ : Cell M U0 U1 → UnitContent ub) (Ψ : Tree → F)
    (Ψ' : (Cell M U0 U1 → UnitContent ub) → F), Stores ub key t σ →
    (∀ t' σ', Stores ub key t' σ' → Ψ t' = Ψ' σ') →
    (scriptSem θ mu cb kinds T ub I t).weightedSum Ψ =
      ∑ ω ∈ s.choices, s.weight ω σ * Ψ' (s.written.piecewise (s.contents ω σ) σ)

/-! ### Writing strings -/

section Put

private theorem padTake_append_true (r : List Bool) :
    padTake ub (r ++ [true]) = (unitsOf ub r 0).bits := by
  rw [unitsOf_of_lt (Nat.succ_pos _), padTake]
  refine List.ext_getElem (by simp [UnitContent.bits]; omega) fun i h1 h2 => ?_
  have hi : i < ub := by simpa [UnitContent.bits] using h2
  simp only [UnitContent.bits, List.getElem_ofFn, zero_mul, zero_add, List.getD_eq_getElem?_getD]
  by_cases h : i < (r ++ [true]).length
  · rw [List.getElem?_eq_getElem h, Option.getD_some,
      List.getElem_append_left (by simp only [List.length_take]; omega), List.getElem_take]
  · rw [List.getElem?_eq_none (by omega), Option.getD_none,
      List.getElem_append_right (by simp only [List.length_take]; omega), List.getElem_replicate]

private theorem unitsOf_drop (hub : 0 < ub) {r : List Bool} (hr : ub ≤ r.length) (i : ℕ) :
    unitsOf ub (r.drop ub) i = unitsOf ub r (i + 1) := by
  simp only [unitsOf, unitCount, List.length_drop, Nat.div_eq_sub_div hub hr,
    Nat.add_lt_add_iff_right, ← List.drop_append_of_le_length hr, List.getD_eq_getElem?_getD,
    List.getElem?_drop, Nat.add_mul, one_mul]
  congr! 3 with b
  rw [Nat.add_comm _ ub, Nat.add_assoc]

variable {α : Type*} [DecidableEq α] {κ : α → List Bool}

/-- Writing a string closed by the bit `1` at the keys of a list of items. -/
private theorem putUnits_spec (hκ : κ.Injective) (hub : 0 < ub) {v : α → UnitContent ub} :
    ∀ (cs : List α) (r : List Bool), cs.Nodup →
      (∀ (i : ℕ) (h : i < cs.length), v cs[i] = unitsOf ub r i) → ∀ t, ∃ t',
      (unitCount ub r = cs.length → (StoreBound ub t → StoreBound ub t') ∧
        ∀ a, tget (κ a) t' = if a ∈ cs then ofBits (v a).bits else tget (κ a) t) ∧
      putUnits ub (cs.map κ) (r ++ [true]) t = if unitCount ub r = cs.length then [t'] else []
  | [], r, _, _, t => ⟨t, by simp [unitCount], by simp [putUnits, unitCount]⟩
  | a₀ :: cs, r, hnd, hv, t => by
    have h0 : v a₀ = unitsOf ub r 0 := hv 0 (by simp)
    set t₀ := tset (κ a₀) (ofBits (v a₀).bits) t
    have ht₀ : StoreBound ub t → StoreBound ub t₀ := fun h =>
      h.tset _ _ (UnitContent.length_bits_le _)
    have hget (a) : tget (κ a) t₀ = if a = a₀ then ofBits (v a₀).bits else tget (κ a) t := by
      simp only [t₀, tget_tset, hκ.eq_iff]
    rw [List.map_cons, putUnits, ite_eq_right_iff.2 (by simp), padTake_append_true, ← h0]
    rcases le_or_gt ub r.length with hr | hr
    · obtain ⟨t', h1, h2⟩ := putUnits_spec hκ hub cs (r.drop ub) (List.nodup_cons.1 hnd).2
        (fun i h => (hv (i + 1) (by simpa using h)).trans (unitsOf_drop hub hr i).symm) t₀
      have hc : unitCount ub r = unitCount ub (r.drop ub) + 1 := by
        simp only [unitCount, List.length_drop, Nat.div_eq_sub_div hub hr]
      refine ⟨t', fun h => ⟨fun hb => (h1 (by simpa [hc] using h)).1 (ht₀ hb), fun a => ?_⟩, ?_⟩
      · rw [(h1 (by simpa [hc] using h)).2, hget]
        by_cases ha : a = a₀ <;> simp [ha, (List.nodup_cons.1 hnd).1]
      · simpa only [List.drop_append_of_le_length hr, hc, List.length_cons,
          Nat.add_right_cancel_iff] using h2
    · rw [List.drop_eq_nil_of_le (by simp; omega)]
      have hc : unitCount ub r = 1 := by simp [unitCount, Nat.div_eq_of_lt hr]
      refine ⟨t₀, fun h => ⟨ht₀, fun a => ?_⟩, ?_⟩
      · obtain rfl : cs = [] := by simpa [hc] using h
        by_cases ha : a = a₀ <;> simp [hget, ha]
      · cases cs <;> simp [putUnits, hc, t₀]

/-- **Writing strings, closed by the bit `1`, at the keys of lists of items.** If every string
has as many units as its list has items, there is one trie after writing, at the key of an item
written it has the unit of the item, and at the keys of the other items it is unchanged; otherwise
there is none. -/
theorem putStrings_spec (hκ : κ.Injective) (hub : 0 < ub) {v : α → UnitContent ub} :
    ∀ (W : List (List α × List Bool)), (W.flatMap Prod.fst).Nodup →
      (∀ w ∈ W, ∀ (i : ℕ) (h : i < w.1.length), v w.1[i] = unitsOf ub w.2 i) → ∀ t, ∃ t',
      ((∀ w ∈ W, unitCount ub w.2 = w.1.length) → (StoreBound ub t → StoreBound ub t') ∧
        ∀ a, tget (κ a) t' = if a ∈ W.flatMap Prod.fst then ofBits (v a).bits else tget (κ a) t) ∧
      putStrings ub (W.map fun w => w.1.map κ) (W.map fun w => w.2 ++ [true]) t =
        if ∀ w ∈ W, unitCount ub w.2 = w.1.length then [t'] else []
  | [], _, _, t => ⟨t, by simp, by simp [putStrings]⟩
  | w :: W, hnd, hv, t => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨t₁, h1, h2⟩ := putUnits_spec hκ hub w.1 w.2 hnd.1 (hv w List.mem_cons_self) t
    simp only [List.map_cons, putStrings, List.headD_cons, List.tail_cons, h2,
      List.forall_mem_cons]
    by_cases hw : unitCount ub w.2 = w.1.length
    · obtain ⟨t', h3, h4⟩ := putStrings_spec hκ hub W hnd.2.1
        (fun w' hw' => hv w' (List.mem_cons_of_mem _ hw')) t₁
      refine ⟨t', fun ⟨_, h⟩ => ⟨fun hb => (h3 h).1 ((h1 hw).1 hb), fun a => ?_⟩, ?_⟩
      · rw [(h3 h).2, (h1 hw).2]
        by_cases ha' : a ∈ W.flatMap Prod.fst <;> simp [ha']
      · rw [ite_eq_left hw, List.flatMap_singleton, h4]
        exact if_congr (and_iff_right hw).symm rfl rfl
    · exact ⟨t₁, fun h => absurd h.1 hw, by simp [hw]⟩

private theorem unitCount_eq_of_putUnits_ne_nil (hub : 0 < ub) :
    ∀ (ks : List (List Bool)) (r : List Bool) (t : Tree), putUnits ub ks (r ++ [true]) t ≠ [] →
      unitCount ub r = ks.length
  | [], r, t, h => by simp [putUnits] at h
  | k :: ks, r, t, h => by
    rw [putUnits, ite_eq_right_iff.2 (by simp)] at h
    rcases le_or_gt ub r.length with hr | hr
    · rw [List.drop_append_of_le_length hr] at h
      simp only [List.length_cons, ← unitCount_eq_of_putUnits_ne_nil hub ks _ _ h, unitCount,
        List.length_drop, Nat.div_eq_sub_div hub hr]
    · rw [List.drop_eq_nil_of_le (by simp; omega)] at h
      cases ks <;> simp_all [putUnits, unitCount, Nat.div_eq_of_lt hr]

/-- Writing strings closed by the bit `1` gives a trie only if every string has as many units as
keys. -/
theorem unitCount_eq_of_putStrings_ne_nil (hub : 0 < ub) :
    ∀ (W : List (List (List Bool) × List Bool)) (t : Tree),
      putStrings ub (W.map Prod.fst) (W.map fun w => w.2 ++ [true]) t ≠ [] →
        ∀ w ∈ W, unitCount ub w.2 = w.1.length
  | [], _, _ => by simp
  | w :: W, t, h => by
    simp only [List.map_cons, putStrings, List.headD_cons, List.tail_cons, ne_eq,
      List.flatMap_eq_nil_iff, not_forall] at h
    obtain ⟨t₁, h1, h2⟩ := h
    exact List.forall_mem_cons.2 ⟨unitCount_eq_of_putUnits_ne_nil hub _ _ _
      (List.ne_nil_of_mem h1), unitCount_eq_of_putStrings_ne_nil hub W t₁ h2⟩

end Put

private theorem bits_eq_nil (hub : 0 < ub) {w : UnitContent ub} : w.bits = [] ↔ w = none := by
  cases w <;> simp [UnitContent.bits]
  omega

/-- For units of positive width, a unit is determined by its bits, as a tree. -/
theorem ofBits_bits_injective (hub : 0 < ub) :
    Function.Injective fun w : UnitContent ub => ofBits w.bits := fun v w h => by
  have h' : v.bits = w.bits := by simpa using congrArg Tree.path h
  by_cases hv : v = none
  · exact hv.trans ((bits_eq_nil hub).1 (h'.symm.trans ((bits_eq_nil hub).2 hv))).symm
  · exact UnitContent.bits_injOn hv (mt (bits_eq_nil hub).2 (h' ▸ mt (bits_eq_nil hub).1 hv)) h'

/-! ### Comparisons -/

variable (mu : Tape.Letter S Unit Γ → Matrix Q Q F) (cb : Option Γ → Fin c → Bool)
  (kinds : List (Σ L : Cut.Law F, L.Role)) (T : ℕ)

/-- A list of comparisons, each of which keeps the trie if it holds and rejects otherwise, keeps
the trie if all hold and rejects otherwise. -/
theorem scriptSem_of_checks {l : List Instruction} {t : Tree} (P : Instruction → Prop)
    [DecidablePred P]
    (h : ∀ i ∈ l, instructionSem θ mu cb kinds T ub i t = if P i then [(1, t)] else []) :
    scriptSem θ mu cb kinds T ub l t = if ∀ i ∈ l, P i then [(1, t)] else [] := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [scriptSem_cons, h i List.mem_cons_self]
    by_cases hi : P i <;> simp [hi, ih fun j hj => h j (List.mem_cons_of_mem _ hj),
      List.weightedBind]

/-! ### Roles -/

section Role

/-- The string on the channel `ν` of a role for the choices `f` of all blocks. -/
private abbrev roleString {L : Cut.Law F} {p : L.Role} {B : ℕ} (f : Fin B → RoleChoice L p)
    (ν : L.ChannelAt p) : List Bool :=
  sideString L.label (fun i => L.length i ν) (fun j => (f j).1) fun j => (f j).2 ν

/-- **The runs of the transducer of a role**: the sum over the choices of all blocks of the
product of the entries of the table at the bits read, at the state after the run. -/
private theorem weightedSum_run_roleTable (L : Cut.Law F) (p : L.Role)
    (htab : ∀ i v g, ∃ e : WE, e.val θ = L.table p i v g) :
    ∀ (B : ℕ) (ins : Fin (slotList L p).length → List Bool)
      (out : Fin (channelList L p).length → List Bool)
      (G : Transducer.State 1 (slotList L p).length (channelList L p).length Bool → F),
      (Transducer.run θ (roleTable θ L p) B ⟨0, ins, out⟩).weightedSum G =
        ∑ f : Fin B → RoleChoice L p,
          (∏ j, L.table p (f j).1 (fun e => (ins (slotIndex L p e)).getD j false) (f j).2) *
            G ⟨0, fun i => (ins i).drop B,
              fun i => (roleString f ((channelList L p).get i)).reverse ++ out i⟩
  | 0, ins, out, G => by simp [Transducer.run_zero, sideString]
  | B + 1, ins, out, G => by
    rw [Transducer.weightedSum_run_succ _ rfl, ← (Fin.consEquiv fun _ => RoleChoice L p).sum_comp,
      Fintype.sum_prod_type]
    refine sum_congr rfl fun z _ => ?_
    rw [Transducer.Choice.apply, weightedSum_run_roleTable L p htab B, mul_sum]
    refine sum_congr rfl fun f _ => ?_
    simp only [val_termOf (htab _ _ _), Fin.consEquiv_apply,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, sideString, List.ofFn_succ,
      List.flatten_cons, List.reverse_append, List.append_assoc, List.drop_tail, mul_assoc,
      List.getD_eq_getElem?_getD, List.getElem?_tail, List.head?_eq_getElem?,
      List.headD_eq_head?_getD, Fin.val_zero, Fin.val_succ]
    rfl

/-- What a run of the transducer of a role adds to a channel has, for some indices of the law for
all blocks, the length of the labels and the strings of the indices on the channel. -/
theorem exists_of_mem_run_roleTable (L : Cut.Law F) (p : L.Role) :
    ∀ {B : ℕ} {s : Transducer.State 1 (slotList L p).length (channelList L p).length Bool}
      {q : F × Transducer.State 1 (slotList L p).length (channelList L p).length Bool},
      q ∈ Transducer.run θ (roleTable θ L p) B s → ∃ ι : Fin B → L.Index, ∀ i,
        (q.2.outputs i).length = ∑ k, (L.labelLength + L.length (ι k) ((channelList L p).get i)) +
          (s.outputs i).length
  | 0, s, q, h => ⟨Fin.elim0, fun _ => by simp_all [Transducer.run_zero]⟩
  | B + 1, s, q, h => by
    rw [Transducer.run_succ] at h
    obtain ⟨a, ha, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 h
    obtain ⟨ι, hι⟩ := exists_of_mem_run_roleTable L p hr
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 ho
    exact ⟨Fin.cons z.1 ι, fun i => by
      simp only [hι, Transducer.Choice.apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        List.length_append, List.length_reverse, List.length_ofFn]
      omega⟩

variable {G : Type} [DecidableEq G] {P : Plan M U0 U1}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G} {key : Cell M U0 U1 → List Bool} {tg : M.Role → ℕ}

/-- **The instruction of a role simulates its step.** -/
theorem simulates_role (hkey : key.Injective) (hub : 0 < ub) {r : M.Role}
    (hr : grp (M.roleParty r) = g) (hkind : kinds[tg r]? = some ⟨M.law r.1, r.2⟩)
    (htab : ∀ i v g', ∃ e : WE, e.val θ = (M.law r.1).table r.2 i v g') :
    Simulates θ mu cb kinds T key [roleInstruction P n o key tg r]
      (roleWriteStep (ub := ub) P n o grp g r) := by
  intro t σ Ψ Ψ' hst hΨ
  have hct (u) : (tget (key ⟨M.roleParty r, u⟩) t).path = (σ ⟨M.roleParty r, u⟩).bits :=
    hst.2 _ ▸ path_ofBits _
  rw [scriptSem_cons, List.weightedSum_weightedBind]
  simp only [scriptSem_nil, List.weightedSum_singleton_one, roleInstruction, instructionSem, hkind,
    roleSem]
  have hcond : (∀ es ∈ (slotList (M.law r.1) r.2).map fun e =>
      ((P.ids n o ⟨r.1, e.val⟩).map fun u => key ⟨M.roleParty r, u⟩).reverse,
      ∀ k ∈ es, (tget k t).path ≠ []) ↔
      ∀ e : (M.law r.1).SlotAt r.2, ∀ u ∈ P.ids n o ⟨r.1, e.val⟩, σ ⟨M.roleParty r, u⟩ ≠ none := by
    simp [slotList, hct, bits_eq_nil hub]
  simp only [roleWriteStep]
  by_cases hp : ∀ e : (M.law r.1).SlotAt r.2, ∀ u ∈ P.ids n o ⟨r.1, e.val⟩,
    σ ⟨M.roleParty r, u⟩ ≠ none
  swap
  · rw [ite_eq_right (hcond.not.2 hp)]
    simp only [eq_false hp, false_and, ite_false, zero_mul, sum_const_zero, List.weightedSum_nil]
  rw [ite_eq_left (hcond.2 hp), List.weightedSum_weightedBind,
    weightedSum_run_roleTable _ _ htab]
  refine Fintype.sum_equiv ⟨fun f => ⟨fun j => (f j).1, fun j => (f j).2⟩,
    fun ig j => ⟨ig.1 j, ig.2 j⟩, fun _ => rfl, fun _ => rfl⟩ _ _ fun f => ?_
  have hins (e : (M.law r.1).SlotAt r.2) (j : ℕ) :
      ((((slotList (M.law r.1) r.2).map fun e =>
        ((P.ids n o ⟨r.1, e.val⟩).map fun u => key ⟨M.roleParty r, u⟩).reverse).map
          fun es => es.reverse.flatMap fun k => (tget k t).path).getD (slotIndex _ _ e) []).getD
            j false = (slotBits (P.count n o r.1) (P.ids n o ⟨r.1, e.val⟩)
              fun u => σ ⟨M.roleParty r, u⟩).getD j false := by
    conv_lhs => arg 1; rw [List.getD_eq_getElem _ _ (by simp),
      List.getElem_map, List.getElem_map]
    simp only [slotIndex, List.getElem_idxOf, List.reverse_reverse, List.flatMap_map, hct,
      slotBits, List.getD_append_replicate]
  set W := (channelList (M.law r.1) r.2).map fun ν =>
    ((indicesBelow (o ⟨r.1, ν.val⟩).succ).map fun k =>
      (⟨M.roleParty r, .new ⟨r.1, ν.val⟩ k⟩ : Cell M U0 U1), roleString f ν) with hWdef
  have hnd : (W.flatMap Prod.fst).Nodup := by
    rw [hWdef, List.flatMap_map]
    exact List.nodup_flatMap_map (nodup_toList _) (fun _ => nodup_indicesBelow _)
      fun ν k ν' k' h => by
        simp only [Cell.mk.injEq, UnitId.new.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
        exact ⟨Subtype.ext h.1, h.2⟩
  obtain ⟨t', h1, h2⟩ := putStrings_spec hkey hub (v := fun c => roleContents r
    ⟨fun j => (f j).1, fun j => (f j).2⟩ c.unit) W hnd (fun w hw i hi => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 hw
      simp [roleContents_new]) t
  have hW : putStrings ub ((channelList (M.law r.1) r.2).map fun ν =>
      (indicesBelow (o ⟨r.1, ν.val⟩).succ).map fun k => key ⟨M.roleParty r, .new ⟨r.1, ν.val⟩ k⟩)
      (List.ofFn fun j => (roleString f ((channelList (M.law r.1) r.2).get j)) ++ [true]) t =
      putStrings ub (W.map fun w => w.1.map key) (W.map fun w => w.2 ++ [true]) t := by
    simp [W, ← List.ofFn_getElem_eq_map]
  simp only [Equiv.coe_fn_mk, hins, eq_true hp, true_and, List.weightedSum_map_one, List.append_nil,
    List.reverse_reverse, hW, h2]
  have hc : (∀ w ∈ W, unitCount ub w.2 = w.1.length) ↔
      ∀ ν : (M.law r.1).ChannelAt r.2, unitCount ub (roleString f ν) = o ⟨r.1, ν.val⟩ + 1 := by
    simp only [W, List.forall_mem_map, List.length_map, length_indicesBelow, Fin.val_succ,
      channelList, Finset.mem_toList, Finset.mem_univ, forall_const]
  have hcells (c : Cell M U0 U1) : c ∈ W.flatMap Prod.fst ↔ c ∈ roleCells n o grp g r := by
    rw [mem_roleCells hr]
    simp only [W, List.flatMap_map, List.mem_flatMap, List.mem_map, mem_indicesBelow, channelList,
      Finset.mem_toList, Finset.mem_univ, true_and, Fin.val_succ, Nat.lt_succ_iff, Fin.val_fin_le,
      eq_comm (a := c)]
  simp only [hc]
  split_ifs with hb
  · rw [List.map_singleton, List.sum_singleton, mul_comm,
      hΨ t' _ ⟨(h1 (hc.2 hb)).1 hst.1, fun c => ?_⟩, mul_comm]
    by_cases hcc : c ∈ roleCells n o grp g r <;>
      simp [(h1 (hc.2 hb)).2, hcells c, hcc, Finset.piecewise, hst.2 c]
  · simp

end Role

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
