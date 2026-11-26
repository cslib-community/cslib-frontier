/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Ary.Packed.RawController
import CslibFrontier.Computability.TreeEval.Ary.IterativeCorrect
import CslibFrontier.Computability.TreeEval.Ary.IterativeBounds
import CslibFrontier.Foundations.Data.ZMod.NatCast

/-!
# Raw-controller transition correspondence

The runtime controller is compared with the existing iterative Cook–Mertz semantics. The
comparison enumeration appears only in theorem statements. An external reply must describe the
node currently requested, or the packed gate extension at the current child registers. These
explicit obligations are discharged by the actual node and gate-reading subroutines; no gate
function or tree is stored in a raw controller state.

## Main definitions

* `ReplyCorrect`: the external node or gate-extension reply needed by one transition.
* `Canonical`: exact padded bank cells and finite control representatives.

## Main results

* `step_ofCfg`: one raw transition preserves the existing configuration representation exactly.
* `iterate_step_ofCfg`: consecutive raw transitions realize the existing iterative controller.
* `exists_iterate_step_root`: the raw kernel returns the existing complete masking procedure's
  result, subject to the explicit external-reply contract.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

variable {p d r b : ℕ} [Fact p.Prime]

/-- The canonical enumeration used only by the comparison semantics. -/
@[expose] noncomputable def units (p : ℕ) [Fact p.Prime] : List (ZMod p)ˣ :=
  (List.range (p - 1)).map (TreeEval.Iter.zmodUnit p)

/-- A gate reply's field vector; invalid or leaf labels require the zero update. -/
@[expose] def expectedGate (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State (ZMod p) d r)
    (st : List (Ary.Iter.Frame (ZMod p) d)) (t : Fin (d + 1)) : Fin r → ZMod p :=
  match read (Ary.Iter.path st) with
  | .gate f => E f (fun j => S (Ary.reg t j))
  | _ => 0

/-- The reply contract for the exact lookup or gate update requested by a typed state. -/
@[expose] def ReplyCorrect (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (q : Ary.Iter.Cfg (ZMod p) d r)
    (reply : Reply) : Prop :=
  match q.mode with
  | .call _ _ => match read (Ary.Iter.path q.stack) with
    | .leaf v => reply.1 = 1 ∧ ∀ i : Fin r, (reply.2.getD i 0 : ZMod p) = e v i
    | .gate _ => reply.1 = 2
    | .none => reply.1 = 0
  | .ret => match q.stack with
    | [] => True
    | fr :: st => if fr.undo = false ∧ ¬fr.child.val + 1 < d then
      ∀ i : Fin r, (reply.2.getD i 0 : ZMod p) = expectedGate E read q.regs st fr.target i
      else True

private theorem toCfg_ret (hd : 0 < d) (bank : List ℕ)
    (st : List (Ary.Iter.Frame (ZMod p) d)) :
    toCfg p d r hd (bank, st.map ofFrame, none) = ⟨toRegs p d r bank, st, .ret⟩ := by
  simp only [toCfg, State.bank, State.stack, toMode, List.map_map, Function.comp_def,
    toFrame_ofFrame, List.map_id_fun', id_eq]

private theorem toCfg_call (hd : 0 < d) (bank : List ℕ)
    (st : List (Ary.Iter.Frame (ZMod p) d)) (c : ℕ) (t : Fin (d + 1)) :
    toCfg p d r hd (bank, st.map ofFrame, some (c, t.val)) =
      ⟨toRegs p d r bank, st, .call (c : ZMod p) t⟩ := by
  simp only [toCfg, State.bank, State.stack, toMode, List.map_map, Function.comp_def,
    toFrame_ofFrame, List.map_id_fun', id_eq, Nat.mod_eq_of_lt t.isLt]

private theorem unitAt_units {j : ℕ} (hj : j < p - 1) :
    ((j + 1 : ℕ) : ZMod p) = (Ary.Iter.unitAt (units p) j : ZMod p) := by
  rw [units, unitAt_zmodUnits hj, TreeEval.Iter.zmodUnit_val hj]

private theorem inverse_unitAt_units {j : ℕ} (hj : j < p - 1) :
    ((Reader.unitInv p j : ℕ) : ZMod p) =
      (((Ary.Iter.unitAt (units p) j)⁻¹ : (ZMod p)ˣ) : ZMod p) := by
  rw [units, unitAt_zmodUnits hj, Reader.cast_unitInv_eq hj]

private theorem toRegs_subBank_expected (E : Gate d b → (Fin d → Fin r → ZMod p) →
    Fin r → ZMod p) (read : List (Fin d) → Tree.Node d b)
    (S : Ary.State (ZMod p) d r) (st : List (Ary.Iter.Frame (ZMod p) d))
    (c : ZMod p) (t : Fin (d + 1)) (values : List ℕ)
    (hvalues : ∀ i : Fin r, (values.getD i 0 : ZMod p) = expectedGate E read S st t i) :
    toRegs p d r (subBank p r t.val c.val values (ofRegs S)) =
      Ary.Iter.updateAt E read (Ary.Iter.path st) c t S := by
  rw [toRegs_subBank (ofRegs S) values (length_ofRegs S) t c.val,
    toRegs_ofRegs, ZMod.natCast_zmod_val]
  unfold Ary.Iter.updateAt
  cases hread : read (Ary.Iter.path st) with
  | none | leaf _ =>
    simp only [hvalues, expectedGate, hread, Pi.zero_apply, mul_zero, sub_zero,
      Function.update_eq_self]
  | gate f =>
    simp only [Ary.gateUpdateWith, hvalues, expectedGate, hread]

private theorem toRegs_scale_unit (S : Ary.State (ZMod p) d r)
    (t : Fin (d + 1)) (j : Fin d) (round : ℕ) (hr : round < p - 1) :
    toRegs p d r (scaleBank p r (reg d t j) (round + 1) (ofRegs S)) =
      Ary.scale (Ary.reg t j) (Ary.Iter.unitAt (units p) round : ZMod p) S := by
  rw [reg_eq, toRegs_scaleBank (ofRegs S) (length_ofRegs S),
    toRegs_ofRegs, unitAt_units hr]

private theorem toRegs_scale_inverse (S : Ary.State (ZMod p) d r)
    (t : Fin (d + 1)) (j : Fin d) (round : ℕ) (hr : round < p - 1) :
    toRegs p d r (scaleBank p r (reg d t j) (Reader.unitInv p round) (ofRegs S)) =
      Ary.scale (Ary.reg t j)
        (((Ary.Iter.unitAt (units p) round)⁻¹ : (ZMod p)ˣ) : ZMod p) S := by
  rw [reg_eq, toRegs_scaleBank (ofRegs S) (length_ofRegs S),
    toRegs_ofRegs, inverse_unitAt_units hr]

/-- Every call, forward return, undo return and round transition agrees with the existing
controller, given exactly the external reply that step needs. The runtime controller itself
contains neither the comparison unit list nor the tree/gate functions. -/
theorem toCfg_step_ofCfg (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (q : Ary.Iter.Cfg (ZMod p) d r)
    (reply : Reply) (hreply : ReplyCorrect e E read q reply)
    (hround : ∀ fr ∈ q.stack, fr.round < p - 1) :
    toCfg p d r hd (step p d r reply (ofCfg q)) =
      Ary.Iter.step hd e E (units p) read q := by
  rcases q with ⟨S, st, mode⟩
  rcases reply with ⟨tag, vals⟩
  have hvalid := validBank_ofRegs (Fact.out : p.Prime).two_le S
  cases mode with
  | call c t =>
    cases hread : read (Ary.Iter.path st) with
    | leaf v =>
      obtain ⟨rfl, hvalues⟩ : tag = 1 ∧ ∀ i : Fin r, (vals.getD i 0 : ZMod p) = e v i := by
        simpa only [ReplyCorrect, hread] using hreply
      exact toCfg_step_call_leaf hd e E (units p) read S st c t v vals hread hvalues
    | none =>
      obtain rfl : tag = 0 := by simpa only [ReplyCorrect, hread] using hreply
      simp only [Ary.Iter.step, hread, ofCfg, ofMode, step, hvalid, ↓reduceIte, stepCore,
        Nat.reduceEqDiff, State.bank, State.stack, toCfg_ret, toRegs_ofRegs]
    | gate f =>
      obtain rfl : tag = 2 := by simpa only [ReplyCorrect, hread] using hreply
      have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
      dsimp only [ofCfg, ofMode]
      simp only [step, hvalid, ↓reduceIte, stepCore, Nat.reduceEqDiff, hp1]
      rw [toCfg_beginRound hd (units p) 0 c t (ofRegs S) (length_ofRegs S) st
        (unitAt_units (by omega)), toRegs_ofRegs]
      cases hus : units p with
      | nil => exact absurd hus (by simpa [units] using hp1)
      | cons u us => simp [Ary.Iter.step, hread]
  | ret =>
    cases st with
    | nil =>
      simp only [Ary.Iter.step_ret_nil, ofCfg, ofMode, step, hvalid, ↓reduceIte, stepCore, toCfg,
        State.bank, State.stack, toMode, List.map_nil, toRegs_ofRegs]
    | cons fr st =>
      have hr : fr.round < p - 1 := hround fr (by simp)
      simp only [ofCfg, ofMode, List.map_cons]
      by_cases hu : fr.undo = true
      · by_cases hj : fr.child.val + 1 < d
        · let child : Fin d := ⟨fr.child.val + 1, hj⟩
          rw [Ary.Iter.step_ret_undo_next hd e E (units p) read S fr st hu hj]
          simp only [step, hvalid, ↓reduceIte, stepCore, ofFrame, hu, hj, ↓reduceIte]
          rw [reg_eq fr.target child]
          refine (toCfg_call hd _ ({ fr with child := child, undo := true } :: st) _
            (Ary.reg fr.target child)).trans ?_
          rw [ZMod.natCast_self_sub_one, toRegs_scale_inverse S fr.target fr.child fr.round hr]
        · by_cases hi : fr.round + 1 < p - 1
          · rw [Ary.Iter.step_ret_undo_round hd e E (units p) read S fr st hu hj]
            · simp only [step, hvalid, ↓reduceIte, stepCore, ofFrame, hu, hj, hi, ↓reduceIte]
              rw [toCfg_beginRound hd (units p) (fr.round + 1) fr.coeff fr.target _
                (by simp [State.bank]) st (unitAt_units hi),
                toRegs_scale_inverse S fr.target fr.child fr.round hr]
            · simpa only [units, List.length_map, List.length_range] using hi
          · rw [Ary.Iter.step_ret_undo_last hd e E (units p) read S fr st hu hj]
            · simp only [step, hvalid, ↓reduceIte, stepCore, ofFrame, hu, hj, hi, ↓reduceIte]
              rw [toCfg_ret, toRegs_scale_inverse S fr.target fr.child fr.round hr]
            · simpa only [units, List.length_map, List.length_range] using hi
      · have huf : fr.undo = false := Bool.eq_false_iff.mpr hu
        by_cases hj : fr.child.val + 1 < d
        · let child : Fin d := ⟨fr.child.val + 1, hj⟩
          rw [Ary.Iter.step_ret_forward_next hd e E (units p) read S fr st huf hj]
          simp only [step, hvalid, ↓reduceIte, stepCore, ofFrame, huf, hj,
            Bool.false_eq_true, ↓reduceIte, State.bank]
          rw [reg_eq fr.target child]
          refine (toCfg_call hd _ ({ fr with child := child, undo := false } :: st) _
            (Ary.reg fr.target child)).trans ?_
          rw [Nat.cast_one, ← reg_eq fr.target child,
            toRegs_scale_unit S fr.target child fr.round hr]
        · have hv : ∀ i : Fin r, (vals.getD i 0 : ZMod p) =
              expectedGate E read S st fr.target i := by
            simpa only [ReplyCorrect, huf, hj, not_false_eq_true, and_self, ↓reduceIte]
              using hreply
          rw [Ary.Iter.step_ret_forward_last hd e E (units p) read S fr st huf hj]
          simp only [step, hvalid, ↓reduceIte, stepCore, ofFrame, huf, hj,
            Bool.false_eq_true, ↓reduceIte]
          rw [reg_eq fr.target ⟨0, hd⟩]
          refine (toCfg_call hd _ ({ fr with child := ⟨0, hd⟩, undo := true } :: st) _
            (Ary.reg fr.target ⟨0, hd⟩)).trans ?_
          rw [ZMod.natCast_self_sub_one, toRegs_subBank_expected E read S st fr.coeff
            fr.target vals hv]

/-- Canonical padded cells retain exactly one modulus offset. -/
@[expose] def CanonicalBank (p d r : ℕ) (bank : List ℕ) : Prop :=
  bank.length = (d + 1) * r ∧ ∀ v ∈ bank, p ≤ v ∧ v < 2 * p

/-- Canonical raw control fields use the exact finite indices and field representatives. -/
@[expose] def CanonicalFrame (p d : ℕ) (fr : Frame) : Prop :=
  fr.round < p - 1 ∧ fr.child < d ∧ fr.coeff < p ∧ fr.target < d + 1

/-- The raw configuration has no hidden slack or alternative field representatives. -/
@[expose] def Canonical (p d r : ℕ) (q : State) : Prop :=
  CanonicalBank p d r q.bank ∧ (∀ fr ∈ q.stack, CanonicalFrame p d fr) ∧
    ∀ c t, q.mode = some (c, t) → c < p ∧ t < d + 1

private theorem canonical_cell (v : ℕ) (hv : p ≤ v) (hv2 : v < 2 * p) :
    p + (v : ZMod p).val = v := by
  rw [ZMod.val_natCast, Nat.mod_eq_sub_mod hv, Nat.mod_eq_of_lt (by omega)]; omega

private theorem canonicalBank_ofRegs (S : Ary.State (ZMod p) d r) :
    CanonicalBank p d r (ofRegs S) := by
  refine ⟨length_ofRegs S, fun _ hv => ?_⟩
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hv
  have := ZMod.val_lt (S (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  exact ⟨Nat.le_add_right _ _, by dsimp only; omega⟩

private theorem canonicalBank_valid {bank : List ℕ} (hbank : CanonicalBank p d r bank) :
    validBank p d r bank = true :=
  (validBank_eq_true p d r bank).mpr
    ⟨(Fact.out : p.Prime).two_le, hbank.1, fun v hv => (hbank.2 v hv).1⟩

private theorem ofRegs_toRegs (bank : List ℕ) (hbank : CanonicalBank p d r bank) :
    ofRegs (toRegs p d r bank) = bank := by
  apply List.ext_getElem
  · simpa only [length_ofRegs] using hbank.1.symm
  · intro k hk hk'
    let z : Fin ((d + 1) * r) := ⟨k, by simpa only [length_ofRegs] using hk⟩
    have hindex : index r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2 = k :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
    have hcell := hbank.2 bank[k] (List.getElem_mem hk')
    simp only [ofRegs, List.getElem_ofFn, toRegs]
    change p + ((bank.getD (index r (finProdFinEquiv.symm z).1
      (finProdFinEquiv.symm z).2) 0 : ZMod p)).val = bank[k]
    rw [hindex]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    exact canonical_cell bank[k] hcell.1 hcell.2

omit [Fact p.Prime] in
private theorem ofFrame_toFrame (hd : 0 < d) (fr : Frame)
    (hfr : CanonicalFrame p d fr) : ofFrame (toFrame (p := p) hd fr) = fr := by
  rcases fr with ⟨round, child, undo, coeff, target⟩
  rcases hfr with ⟨hr, hc, hv, ht⟩
  simp only [toFrame, ofFrame, ZMod.val_natCast, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt ht]

omit [Fact p.Prime] in
private theorem ofMode_toMode (mode : Option (ℕ × ℕ))
    (hmode : ∀ c t, mode = some (c, t) → c < p ∧ t < d + 1) :
    ofMode (toMode p d mode) = mode := by
  rcases mode with _ | ⟨c, t⟩
  · rfl
  · obtain ⟨hc, ht⟩ := hmode c t rfl
    simp only [ofMode, toMode, ZMod.val_natCast, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt ht]

/-- Canonical raw states are exactly represented by the existing typed configurations. -/
theorem ofCfg_toCfg (hd : 0 < d) (q : State) (hq : Canonical p d r q) :
    ofCfg (toCfg p d r hd q) = q := by
  rcases q with ⟨bank, stack, mode⟩
  rcases hq with ⟨hbank, hstack, hmode⟩
  simp only [ofCfg, toCfg, ofRegs_toRegs bank hbank, List.map_map,
    ofMode_toMode mode hmode]
  congr 2
  calc
    stack.map (ofFrame ∘ toFrame hd) = stack.map id :=
      List.map_congr_left fun fr hfr => ofFrame_toFrame hd fr (hstack fr hfr)
    _ = stack := List.map_id stack

omit [Fact p.Prime] in
private theorem canonicalBank_mapIdx {bank : List ℕ} (hbank : CanonicalBank p d r bank)
    (t : ℕ) (g : ℕ → ℕ → ℕ) (hg : ∀ i v, g i v < p) :
    CanonicalBank p d r (bank.mapIdx fun k v => if k / r = t then p + g k v else v) := by
  refine ⟨by simpa only [List.length_mapIdx] using hbank.1, fun v hv => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hv
  have hcell := hbank.2 bank[i] (List.getElem_mem hi)
  have := hg i bank[i]
  split_ifs <;> omega

private theorem canonicalBank_scaleBank {bank : List ℕ} (hbank : CanonicalBank p d r bank)
    (t a : ℕ) : CanonicalBank p d r (scaleBank p r t a bank) :=
  canonicalBank_mapIdx hbank t _ fun _ _ => Nat.mod_lt _ (Fact.out : p.Prime).pos

private theorem canonicalBank_addBank {bank : List ℕ} (hbank : CanonicalBank p d r bank)
    (t c : ℕ) (values : List ℕ) : CanonicalBank p d r (addBank p r t c values bank) :=
  canonicalBank_mapIdx hbank t _ fun _ _ => Nat.mod_lt _ (Fact.out : p.Prime).pos

private theorem canonicalBank_subBank {bank : List ℕ} (hbank : CanonicalBank p d r bank)
    (t c : ℕ) (values : List ℕ) : CanonicalBank p d r (subBank p r t c values bank) :=
  canonicalBank_mapIdx hbank t _ fun _ _ => Nat.mod_lt _ (Fact.out : p.Prime).pos

omit [Fact p.Prime] in
private theorem canonical_ret {bank : List ℕ} {st : List Frame}
    (hbank : CanonicalBank p d r bank) (hst : ∀ fr ∈ st, CanonicalFrame p d fr) :
    Canonical p d r (bank, st, none) :=
  ⟨hbank, hst, fun c t h => by cases h⟩

omit [Fact p.Prime] in
private theorem canonical_call {bank : List ℕ} {st : List Frame} {c t : ℕ}
    (hbank : CanonicalBank p d r bank) (hst : ∀ fr ∈ st, CanonicalFrame p d fr)
    (hc : c < p) (ht : t < d + 1) : Canonical p d r (bank, st, some (c, t)) :=
  ⟨hbank, hst, fun _ _ h =>
    let p := Prod.mk.inj (Option.some.inj h)
    ⟨p.1 ▸ hc, p.2 ▸ ht⟩⟩

private theorem canonical_beginRound (hd : 0 < d) {bank : List ℕ} {st : List Frame}
    (hbank : CanonicalBank p d r bank) (hst : ∀ fr ∈ st, CanonicalFrame p d fr)
    {round c t : ℕ} (hr : round < p - 1) (hc : c < p) (ht : t < d + 1) :
    Canonical p d r (beginRound p d r round c t bank st) :=
  canonical_call (canonicalBank_scaleBank hbank _ _)
    (List.forall_mem_cons.2 ⟨⟨hr, hd, hc, ht⟩, hst⟩) (Fact.out : p.Prime).one_lt
    (Nat.mod_lt _ (Nat.succ_pos d))

/-- Canonical storage and control representatives survive every raw transition. -/
theorem canonical_step (hd : 0 < d) (reply : Reply) (q : State)
    (hq : Canonical p d r q) : Canonical p d r (step p d r reply q) := by
  rcases q with ⟨bank, stack, mode⟩
  rcases hq with ⟨hbank, hstack, hmode⟩
  have hvalid := canonicalBank_valid hbank
  simp only [step, hvalid, ↓reduceIte]
  rcases mode with _ | ⟨c, t⟩
  · cases stack with
    | nil => exact ⟨hbank, hstack, hmode⟩
    | cons fr st =>
      rcases fr with ⟨round, child, undo, coeff, target⟩
      obtain ⟨⟨hr, hj, hc, ht⟩, hst⟩ := List.forall_mem_cons.1 hstack
      have hreg (j : ℕ) : reg d target j < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
      have hneg : p - 1 < p := by have := (Fact.out : p.Prime).pos; omega
      cases undo with
      | true =>
        simp only [stepCore, ↓reduceIte]
        have hscaled := canonicalBank_scaleBank hbank (reg d target child)
          (Reader.unitInv p round)
        split_ifs with hjnext hrnext
        · exact canonical_call hscaled (List.forall_mem_cons.2 ⟨⟨hr, hjnext, hc, ht⟩, hst⟩) hneg
            (hreg _)
        · exact canonical_beginRound hd hscaled hst hrnext hc ht
        · exact canonical_ret hscaled hst
      | false =>
        simp only [stepCore, Bool.false_eq_true, ↓reduceIte]
        split_ifs with hjnext
        · exact canonical_call (canonicalBank_scaleBank hbank _ _)
            (List.forall_mem_cons.2 ⟨⟨hr, hjnext, hc, ht⟩, hst⟩) (Fact.out : p.Prime).one_lt
            (hreg _)
        · exact canonical_call (canonicalBank_subBank hbank target coeff reply.2)
            (List.forall_mem_cons.2 ⟨⟨hr, hd, hc, ht⟩, hst⟩) hneg (hreg _)
  · obtain ⟨hc, ht⟩ := hmode c t rfl
    have hp2 := (Fact.out : p.Prime).two_le
    simp only [stepCore]
    split_ifs with hleaf hgate hempty
    · exact canonical_ret (canonicalBank_addBank hbank t c reply.2) hstack
    · omega
    · exact canonical_beginRound hd hbank hstack (by omega) hc ht
    · exact canonical_ret hbank hstack

private theorem canonical_ofCfg (q : Ary.Iter.Cfg (ZMod p) d r)
    (hround : ∀ fr ∈ q.stack, fr.round < p - 1) : Canonical p d r (ofCfg q) := by
  refine ⟨canonicalBank_ofRegs q.regs, fun fr hfr => ?_, ?_⟩
  · obtain ⟨typed, htyped, rfl⟩ := List.mem_map.mp hfr
    exact ⟨hround typed htyped, typed.child.isLt, ZMod.val_lt typed.coeff,
      typed.target.isLt⟩
  · rcases q with ⟨_, _, ⟨c, t⟩ | _⟩
    · rintro _ _ ⟨rfl, rfl⟩
      exact ⟨ZMod.val_lt c, t.isLt⟩
    · exact fun _ _ => nofun

/-- The physical raw transition preserves the canonical representation exactly, not only after
decoding its field values. This permits consecutive raw transitions without re-encoding. -/
theorem step_ofCfg (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (q : Ary.Iter.Cfg (ZMod p) d r)
    (reply : Reply) (hreply : ReplyCorrect e E read q reply)
    (hround : ∀ fr ∈ q.stack, fr.round < p - 1) :
    step p d r reply (ofCfg q) = ofCfg (Ary.Iter.step hd e E (units p) read q) := by
  rw [← ofCfg_toCfg hd _ (canonical_step hd reply (ofCfg q) (canonical_ofCfg q hround)),
    toCfg_step_ofCfg hd e E read q reply hreply hround]

/-- Every consecutive raw transition realizes the existing iterative controller, from its
canonical initial representation, when each requested reply satisfies its explicit contract. -/
theorem iterate_step_ofCfg (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (q : Ary.Iter.Cfg (ZMod p) d r)
    (answer : State → Reply)
    (hanswer : ∀ n, ReplyCorrect e E read (Ary.Iter.runFrom hd e E (units p) read q n)
      (answer (ofCfg (Ary.Iter.runFrom hd e E (units p) read q n))))
    (hround : ∀ n, ∀ fr ∈ (Ary.Iter.runFrom hd e E (units p) read q n).stack,
      fr.round < p - 1) (n : ℕ) :
    (fun raw => step p d r (answer raw) raw)^[n] (ofCfg q) =
      ofCfg (Ary.Iter.runFrom hd e E (units p) read q n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      step_ofCfg hd e E read _ _ (hanswer n) (hround n), Ary.Iter.runFrom_succ]

/-- The consecutive raw controller realizes the existing complete masking procedure. All
external access is isolated in the explicit reply contract; native query subroutines must still
supply those replies and charge their computation. -/
theorem exists_iterate_step_root (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    {H : ℕ} (T : Tree d b H) (S : Ary.State (ZMod p) d r)
    (c : ZMod p) (t : Fin (d + 1)) (answer : State → Reply)
    (hanswer : ∀ n, ReplyCorrect e E T.nodeAt
      (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
      (answer (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)))) :
    ∃ N, (fun raw => step p d r (answer raw) raw)^[N]
        (ofCfg (Ary.Iter.initialCfg S c t)) =
      ofCfg (⟨Ary.procWith e E (units p) T c t S, [], .ret⟩ : Ary.Iter.Cfg (ZMod p) d r) := by
  obtain ⟨N, hN⟩ := Ary.Iter.exists_runFrom_root hd e E (units p) T S c t
  refine ⟨N, (iterate_step_ofCfg hd e E T.nodeAt _ answer hanswer (fun n fr hfr => ?_) N).trans
    (congrArg ofCfg hN)⟩
  simpa only [units, List.length_map, List.length_range] using
    (Ary.Iter.runFrom_initial_bounds T hd e E (units p) S c t n).2 fr hfr

end Cslib.TreeEval.Ary.Packed.RawController
