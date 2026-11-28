/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Tables

/-!
# The templates of the scripts

In the end, the dealing program of [AnthropicVPVNP2026] writes the script of every group by
filling a template (`Interpreter.Tm`) from its state (`Codes.scriptTm`). The template lists, in
the order of `groupScript`, the instructions of the base parties, of the roles and of the end; an
instruction is in the script if the group of its party, a step of the straight-line program, has
the number of the group, and a unit is compared in the end if it is current. If the state has the
values that the dealing program computes (`Final`), the filled template is the script of the group
(`expand_scriptTm`). The templates of lists and of conditional lists expand to lists
(`expand_listTm`, `toList_expand_ifTm`).

## Main definitions

* `listTm`, `catTm`, `ifTm`: templates of lists, of concatenations and of conditional lists.
* `Codes.valueTm`, `Codes.bodyTm`, `Codes.baseTm`, `Codes.basesTm`, `Codes.slotTm`,
  `Codes.roleTm`, `Codes.fixedTm`, `Codes.endTm`, `Codes.scriptTm`: the templates of the parts of
  a script, and of the script of a group.
* `Final`: the values of the dealing program in the end.

## Main results

* `expand_scriptTm`: the template of the script of a group gives the script of the group.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: it writes for each piece its script). Ported from the source module
`Nc.Dl.Scr`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

section Lists

/-- A template of a list: its expansion is the list of the expansions. -/
@[expose] def listTm : List Tm → Tm
  | [] => .c .nil
  | t :: ts => .cons t (listTm ts)

theorem expand_listTm (σ : List Bool → Tree) (ts : List Tm) :
    (listTm ts).expand σ = listT (ts.map (Tm.expand σ)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [listTm, Tm.expand, ih, listT]

/-- A template of a concatenation: its expansion is the concatenation of the expansions, which
are lists. -/
@[expose] def catTm : List Tm → Tm
  | [] => .c .nil
  | t :: ts => .app t (catTm ts)

private theorem expand_catTm (σ : List Bool → Tree) (ts : List Tm) :
    (catTm ts).expand σ = listT (ts.flatMap fun t => (t.expand σ).toList) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [catTm, Tm.expand, ih, toList_listT, List.flatMap_cons]

/-- The template `a` if the value at `p` is `t`, and the empty list otherwise. -/
@[expose] def ifTm (p : List Bool) (t : Tree) (a : Tm) : Tm := .ifeq p t a (.c .nil)

theorem toList_expand_ifTm (σ : List Bool → Tree) (p : List Bool) (t : Tree) (a : Tm) :
    ((ifTm p t a).expand σ).toList = if σ p = t then (a.expand σ).toList else [] := by
  rw [ifTm, Tm.expand]
  split_ifs <;> rfl

private theorem flatMap_ite {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (f : α → List β) : (l.flatMap fun a => if p a then f a else []) = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

end Lists

section Templates

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm ub : ℕ}
  {M : Moves F (K + K + A') E} {S Q : Type} [Fintype S] [DecidableEq S]
  (C : Codes S M U0 U1 D pS) {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (tab : SlpTab P grp D nI pS)

namespace Codes

/-- The template of the value at a name. -/
@[expose] def valueTm (x : PlanName S M U0 U1 pS) : Tm := .get (C.name x)

/-- The template of the body of the base party `p` (`baseBody`). -/
@[expose] noncomputable def bodyTm (p : Fin (K + K)) : Tm :=
  .cons (listTm ((tapes S).map fun s => C.valueTm (.flags s p)))
    (.cons (listTm (List.ofFn fun b => C.valueTm (.writeKeys p b)))
      (listTm (List.ofFn fun b => C.valueTm (.readKeys b p))))

/-- The template of the block or of the input part of the base party `p`. -/
@[expose] noncomputable def baseTm (p : Fin (K + K)) : Tm :=
  Fin.addCases (motive := fun _ => Tm)
    (fun κ => .cons (.c (num 0)) (.cons (.cons (C.valueTm (.state κ.castSucc))
      (C.valueTm (.state κ.succ))) (C.bodyTm p)))
    (fun κ => .cons (.c (num 1)) (.cons (C.valueTm (.part κ)) (C.bodyTm p))) p

/-- The template of the instructions of the base party `p` (`baseInstructions`). -/
@[expose] noncomputable def basesTm (p : Fin (K + K)) : Tm :=
  .cons (C.baseTm p) (C.valueTm (.selfAgree p))

/-- The template of the keys at the party `a` of the units given at the slot `z`, in reverse
order: the units whose step of `givenGate` is the digit `1`. -/
@[expose] noncomputable def slotTm (hD : 1 < D) (z : M.Slot) (a : Fin (K + K + A')) : Tm :=
  catTm ((UnitId.list (K + K) U0 M.Channel U1).reverse.map fun u =>
    ifTm (C.name (.gate (tab.givenGate z u))) (C.digitTree ⟨1, hD⟩)
      (.c (listT [ofBits (C.key ⟨a, u⟩)])))

/-- The template of the instruction of the role `r` (`roleInstruction`), number `tg r` in a list
of roles of laws. -/
@[expose] noncomputable def roleTm (tg : M.Role → ℕ) (hD : 1 < D) (r : M.Role) : Tm :=
  .cons (.c (num (4 + tg r))) (.cons (C.valueTm (.count r.1)) (.cons
    (listTm ((univ : Finset ((M.law r.1).SlotAt r.2)).toList.map fun e =>
      C.slotTm tab hD ⟨r.1, e.val⟩ (M.roleParty r)))
    (listTm ((univ : Finset ((M.law r.1).ChannelAt r.2)).toList.map fun ν =>
      C.valueTm (.newKeys ⟨r.1, ν.val⟩ (decide ((M.law r.1).channelEnd ν.val false ≠ r.2)))))))

/-- The template of the comparison of the contents at the key `k` with the contents of the
unit `u`. -/
@[expose] def fixedTm (k : List Bool) (u : UnitId (K + K) U0 M.Channel U1) : Tm :=
  listTm [.cons (.c (num 3)) (.cons (.c (ofBits k)) (C.valueTm (.content u)))]

/-- The template of the instructions of the end for the unit `u` and the group `g`
(`endInstructions`). -/
@[expose] noncomputable def endTm (hD : 1 < D) (hmm : mm ≤ D) (g : Fin mm)
    (u : UnitId (K + K) U0 M.Channel U1) : Tm :=
  let h (d : Bool) := UnitId.holder M.channelParty u d
  ifTm (C.name (.gate (tab.curGate u))) (C.digitTree ⟨1, hD⟩)
    (.ifeq (C.name (.gate (tab.groupGate (h false)))) (C.digitTree (Fin.castLE hmm g))
      (.ifeq (C.name (.gate (tab.groupGate (h true)))) (C.digitTree (Fin.castLE hmm g))
        (.c (listT [(Instruction.agree (C.key ⟨h false, u⟩) (C.key ⟨h true, u⟩)).enc]))
        (C.fixedTm (C.key ⟨h false, u⟩) u))
      (ifTm (C.name (.gate (tab.groupGate (h true)))) (C.digitTree (Fin.castLE hmm g))
        (C.fixedTm (C.key ⟨h true, u⟩) u)))

/-- The template of the script of the group `g` (`groupScript`), with the binary numbers `bT` of
steps and `bub` of bits of a unit. -/
@[expose] noncomputable def scriptTm (tg : M.Role → ℕ) (bT bub : List Bool) (hD : 1 < D)
    (hmm : mm ≤ D) (g : Fin mm) : Tm :=
  .cons (.c (.cons (ofBits bT) (ofBits bub))) (catTm (
    (List.finRange (K + K)).map (fun p => ifTm (C.name (.gate (tab.groupGate (Fin.castAdd A' p))))
      (C.digitTree (Fin.castLE hmm g)) (C.basesTm p)) ++
    (allRoles M).map (fun r => ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
      (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r])) ++
    (UnitId.list (K + K) U0 M.Channel U1).map (C.endTm tab hD hmm g)))

end Codes

/-- The values of the dealing program in the end that the templates of the scripts read, for the
parts `pt` of the input, the states `q` between the blocks (numbered by `qn`), the row data `ρ`,
the numbers of units `n`, the outcomes `o` and the contents `b` of the units. -/
structure Final (qn : Q → ℕ) (pt : Fin K → Tree) (q : Fin (K + 1) → Q)
    (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.Channel → Fin U1) (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub)
    (st : PlanName S M U0 U1 pS → Tree) : Prop where
  part : ∀ κ, st (.part κ) = pt κ
  state : ∀ a, st (.state a) = num (qn (q a))
  flags : ∀ s p, st (.flags s p) = flagsTree (ρ s p)
  writeKeys : ∀ p p', st (.writeKeys p p') = C.writeKeysTree p p' (n p p')
  readKeys : ∀ p p', st (.readKeys p p') = C.readKeysTree p p' (n p p')
  selfAgree : ∀ p, st (.selfAgree p) = C.selfAgreeTree p (n p p)
  newKeys : ∀ ν d, st (.newKeys ν d) = C.newKeysTree ν d (o ν)
  gate : ∀ k, st (.gate k) = C.digitTree (tab.fn k ⟨n, o⟩)
  count : ∀ x, st (.count x) = num (P.count n o x)
  content : ∀ u, st (.content u) = ofBits (b u).bits

end Templates

section Expand

variable {F : Type} [CommRing F] {K A' E U0 U1 D nI pS mm ub c : ℕ} {M : Moves F (K + K + A') E}
  {Γ S Q : Type} [Fintype S] {C : Codes S M U0 U1 D pS}
  {P : Plan M U0 U1} {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}
  {tab : SlpTab P grp D nI pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.Channel → Fin U1} {b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub}
  {st : PlanName S M U0 U1 pS → Tree} {hD : 1 < D} {hmm : mm ≤ D}

omit [Fintype S] in
private theorem expand_valueTm (x : PlanName S M U0 U1 pS) :
    (C.valueTm x).expand (extend C.name st fun _ => .nil) = st x :=
  C.name_injective.extend_apply _ _ _

omit [Fintype S] in
/-- The digit at a step that is `1` exactly if `p` holds. -/
private theorem digitTree_eq_one (C : Codes S M U0 U1 D pS) {d : Fin D} {p : Prop} [Decidable p]
    (hd : (d : ℕ) = if p then 1 else 0) : C.digitTree d = C.digitTree ⟨1, hD⟩ ↔ p := by
  rw [C.digitTree_injective.eq_iff, Fin.ext_iff, hd]
  split_ifs <;> simp [*]

/-- The party of a role is at the end `decide (channelEnd ν false ≠ r.2)` of its channel `ν`. -/
private theorem channelParty_decide (r : M.Role) (ν : (M.law r.1).ChannelAt r.2) :
    M.channelParty ⟨r.1, ν.val⟩ (decide ((M.law r.1).channelEnd ν.val false ≠ r.2)) =
      M.roleParty r := by
  obtain ⟨x, p⟩ := r
  obtain ⟨ν, d, hd⟩ := ν
  simp only [Moves.channelParty, Moves.channelRole, Moves.roleParty]
  congr 1
  cases d <;> by_cases h : (M.law x).channelEnd ν false = p <;> simp_all

omit [Fintype S] in
private theorem digitTree_group_iff (a : Fin (K + K + A')) (g : Fin mm) :
    C.digitTree (tab.fn (tab.groupGate a) ⟨n, o⟩) = C.digitTree (Fin.castLE hmm g) ↔
      grp ⟨n, o⟩ a = g := by
  rw [C.digitTree_injective.eq_iff, Fin.ext_iff, tab.fn_groupGate, Fin.val_castLE, Fin.val_inj]

variable (h : Final C tab qn pt q ρ n o b st)
include h

omit [Fintype S] in
private theorem gate_eq (k : Fin pS) : (extend C.name st fun _ => .nil) (C.name (.gate k)) =
    C.digitTree (tab.fn k ⟨n, o⟩) := by
  rw [C.name_injective.extend_apply, h.gate]


private theorem expand_basesTm {cb : Option Γ → Fin c → Bool} {x : Fin K → List Γ}
    (hpt : ∀ κ, pt κ = wordsEnc (((x κ).map (letterCode cb)).reverse)) (p : Fin (K + K)) :
    (C.basesTm p).expand (extend C.name st fun _ => .nil) =
      listT ((baseInstructions qn cb q x ρ n C.key C.dkey p).map Instruction.enc) := by
  have hbody : (C.bodyTm p).expand (extend C.name st fun _ => .nil) =
      (baseBody ρ n C.key C.dkey p).enc := by
    simp only [Codes.bodyTm, Tm.expand, expand_listTm, List.map_map, List.map_ofFn,
      Function.comp_def, expand_valueTm, h.flags, h.writeKeys, h.readKeys, Body.enc, baseBody,
      keysEnc, flagsTree, Codes.writeKeysTree, Codes.readKeysTree]
  rw [Codes.basesTm, Tm.expand, baseInstructions, List.map_cons, listT, expand_valueTm, h.selfAgree,
    Codes.selfAgreeTree, List.map_map]
  congr 1
  induction p using Fin.addCases <;>
    simp [Codes.baseTm, Tm.expand, expand_valueTm, h.state, h.part, hpt, hbody, Instruction.enc,
      -Fin.natAdd_eq_addNat]

omit [Fintype S] in
private theorem expand_slotTm (z : M.Slot) (a : Fin (K + K + A')) :
    (C.slotTm tab hD z a).expand (extend C.name st fun _ => .nil) =
      wordsEnc (((P.ids n o z).map fun u => C.key ⟨a, u⟩).reverse) := by
  rw [Codes.slotTm, expand_catTm, List.flatMap_map]
  simp only [toList_expand_ifTm, gate_eq h,
    digitTree_eq_one C (tab.fn_givenGate z _ ⟨n, o⟩), Tm.expand, toList_listT, flatMap_ite]
  simp [List.filter_reverse, Plan.ids, wordsEnc, Function.comp_def, ← List.map_eq_flatMap]

omit [Fintype S] in
private theorem expand_roleTm (tg : M.Role → ℕ) (r : M.Role) :
    (C.roleTm tab tg hD r).expand (extend C.name st fun _ => .nil) =
      (roleInstruction P n o C.key tg r).enc := by
  simp only [Codes.roleTm, Tm.expand, expand_listTm, List.map_map, Function.comp_def,
    expand_valueTm, h.count, expand_slotTm h, h.newKeys, Codes.newKeysTree, channelParty_decide,
    roleInstruction, Instruction.enc, keysEnc, slotList, channelList]

omit [Fintype S] in
private theorem flatMap_endTm (g : Fin mm) :
    ((UnitId.list (K + K) U0 M.Channel U1).flatMap fun u =>
      ((C.endTm tab hD hmm g u).expand (extend C.name st fun _ => .nil)).toList) =
        (endInstructions P n o (grp ⟨n, o⟩) g C.key b).map Instruction.enc := by
  rw [endInstructions]
  induction UnitId.list (K + K) U0 M.Channel U1 with
  | nil => rfl
  | cons u l ih =>
    rw [List.flatMap_cons, ih]
    by_cases hc : u ∈ P.cur n o E <;>
      by_cases h0 : grp ⟨n, o⟩ (UnitId.holder M.channelParty u false) = g <;>
      by_cases h1 : grp ⟨n, o⟩ (UnitId.holder M.channelParty u true) = g <;>
      simp [Codes.endTm, toList_expand_ifTm, gate_eq h,
        digitTree_eq_one C (tab.fn_curGate u ⟨n, o⟩), digitTree_group_iff, Tm.expand,
        Codes.fixedTm, expand_listTm, expand_valueTm, h.content, hc, h0, h1, Instruction.enc,
        listT, Tree.toList]

/-- **The script of a group.** If the state by names `st` has the values of the dealing program
in the end (`Final`), and the parts `pt` of the input are the codes of the letters of `x`, then
the template of the script of the group `g` gives its script `groupScript`. -/
theorem expand_scriptTm {cb : Option Γ → Fin c → Bool} {x : Fin K → List Γ}
    (hpt : ∀ κ, pt κ = wordsEnc (((x κ).map (letterCode cb)).reverse)) (tg : M.Role → ℕ)
    (bT bub : List Bool) (g : Fin mm) :
    (C.scriptTm tab tg bT bub hD hmm g).expand (extend C.name st fun _ => .nil) =
      scriptEnc bT bub (groupScript qn cb P q x ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg b) := by
  rw [Codes.scriptTm, Tm.expand, Tm.expand, expand_catTm, scriptEnc, groupScript]
  congr 1
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map,
    List.flatMap_map, flatMap_endTm h, List.map_append, List.map_append]
  congr 3
  · simp only [toList_expand_ifTm, gate_eq h, digitTree_group_iff, expand_basesTm h hpt,
      toList_listT]
    rw [flatMap_ite, baseParties_eq_filter, List.map_flatMap]
  · simp only [toList_expand_ifTm, gate_eq h, digitTree_group_iff, expand_listTm, List.map_cons,
      List.map_nil, expand_roleTm h, toList_listT]
    rw [flatMap_ite, groupRoles_eq_filter, ← List.map_eq_flatMap, List.map_map]
    rfl

end Expand

end Cslib.Circuits.Arithmetic.Separation.Dealing
