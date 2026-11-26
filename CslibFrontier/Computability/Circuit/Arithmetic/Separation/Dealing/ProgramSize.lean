/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Cut
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.StepSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccSize

/-!
# The size of the dealing program

The dealing program of [AnthropicVPVNP2026] (`Codes.dealProgram`) has size at most
`(dealBaseSize + 3000) * (X * Lc) ^ 4` (`size_dealProgram_le`), where `dealBaseSize` is the size
of the dealing formula with empty letters, names, binary numbers, steps and templates, `X` bounds
the numbers of the dealing program and `Lc` the lengths of its codes (`Codes.SizeBounds`). The
formula has size linear in the sizes of its letters, names, steps and templates; its steps have
size `O(X ^ 4 * Lc)` in all (`size_listT_dealSteps_le`), and its templates `O(X ^ 3 * Lc)` each.

## Main definitions

* `dealBaseSize`: the size of the dealing formula with empty letters, names, binary numbers, steps
  and templates.

## Main results

* `size_dealProgram_le`: the size of the dealing program.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 53: some program of size at most `v^a₀` cuts). Ported from the source module
`Nc.Dl.SizeDeal` (the templates and the program).
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- The size of the dealing formula whose letters are the empty tree and whose names, binary
numbers, steps and templates are empty. -/
def dealBaseSize : ℕ := (dealFormula .nil .nil [] [] [] [] [] []).code.size

/-- **The size of the dealing formula**: at most `dealBaseSize`, plus `4` times the size of the
bits `nub`, the size of the bits `nl`, twice the sizes of the letters, and the sizes of the lists
of the names, the steps and the templates. -/
private theorem size_dealFormula_le (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool)
    (sts sts' : List DStep) (ts : List Tm) :
    (dealFormula t0 t1 names nl nub sts sts' ts).code.size ≤
      dealBaseSize + 4 * (ofBits nub).size + (ofBits nl).size + 2 * t0.size + 2 * t1.size +
        (listT (names.map ofBits)).size + (listT (sts.map DStep.tree)).size +
          (listT (sts'.map DStep.tree)).size + (listT (ts.map Tm.tree)).size := by
  simp only [dealBaseSize, dealFormula, dstepsF, dstepF, bitsF, partsF, wordF, wordB, tmsF, foldF,
    foldB, mapF, mapB, lett, app, Fm.code, Tree.size, List.map_nil, listT, ofBits]
  omega

private theorem size_listTm (ts : List Tm) :
    (listTm ts).tree.size = (ts.map fun t => t.tree.size + 7).sum + 3 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [listTm, Tm.tree, Tree.size, ih, List.map_cons, List.sum_cons, num]; omega

private theorem size_catTm (ts : List Tm) :
    (catTm ts).tree.size = (ts.map fun t => t.tree.size + 11).sum + 3 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [catTm, Tm.tree, Tree.size, ih, List.map_cons, List.sum_cons, num]; omega

/-- At most `X` parts of size at most `a * u`, with `b` more for each. -/
private theorem sum_map_le_mul {ts : List Tm} {X a b u : ℕ} (hu : 1 ≤ u)
    (hl : ts.length ≤ X) (h : ∀ t ∈ ts, t.tree.size ≤ a * u) :
    (ts.map fun t => t.tree.size + b).sum ≤ (a + b) * (X * u) := by
  have := List.sum_le_length_nsmul (ts.map fun t => t.tree.size + b) (a * u + b)
    (by simpa using fun t ht => h t ht)
  have := Nat.mul_le_mul_right (a * u + b) hl
  have := Nat.mul_le_mul_left (b * X) hu
  simp only [List.length_map, smul_eq_mul] at *
  nlinarith

private theorem size_listTm_le_mul {ts : List Tm} {X a u : ℕ} (hu : 1 ≤ u) (hl : ts.length ≤ X)
    (h : ∀ t ∈ ts, t.tree.size ≤ a * u) : (listTm ts).tree.size ≤ (a + 7) * (X * u) + 3 := by
  rw [size_listTm]
  exact Nat.add_le_add_right (sum_map_le_mul hu hl h) 3

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm : ℕ}
  {M : Moves F (K + K + A') E} {S Q : Type} [Fintype S] [Fintype Q] {C : Codes S M U0 U1 D pS}
  {qn : Q → ℕ} {tg : M.Role → ℕ} {X Lc : ℕ} {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (tab : SlpTab P grp D nI pS)
  {hD : 1 < D} (H : C.SizeBounds qn tg X Lc)
include H

private theorem size_valueTm (y : PlanName S M U0 U1 pS) : (C.valueTm y).tree.size ≤ 9 * Lc := by
  have := H.size_ofBits_le (H.name y)
  have := H.one_le_Lc
  simp only [Codes.valueTm, Tm.tree, Tree.size, num]
  omega

private theorem size_basesTm (p : Fin (K + K)) : (C.basesTm p).tree.size ≤ 140 * (X * Lc) := by
  have hLc := H.one_le_Lc
  have h1 := H.le_mul_X Lc
  have hv := size_valueTm H
  have hl (ts : List Tm) (hl : ts.length ≤ X) (h : ∀ t ∈ ts, ∃ y, t = C.valueTm y) :
      (listTm ts).tree.size ≤ (9 + 7) * (X * Lc) + 3 :=
    size_listTm_le_mul hLc hl fun t ht => by obtain ⟨y, rfl⟩ := h t ht; exact hv y
  have l1 := hl ((tapes S).map fun s => C.valueTm (.flags s p)) (by simpa [tapes] using H.tapes)
    (by simp)
  have l2 := hl (List.ofFn fun b => C.valueTm (.writeKeys p b)) (by simpa using H.parties)
    (by simp)
  have l3 := hl (List.ofFn fun b => C.valueTm (.readKeys b p)) (by simpa using H.parties)
    (by simp)
  have := hv (.selfAgree p)
  induction p using Fin.addCases with
  | left κ =>
    have := hv (.state κ.castSucc)
    have := hv (.state κ.succ)
    simp only [Codes.basesTm, Codes.baseTm, Fin.addCases_left, Codes.bodyTm, Tm.tree, Tree.size,
      num] at *
    omega
  | right κ =>
    have := hv (.part κ)
    simp only [Codes.basesTm, Codes.baseTm, Fin.addCases_right, Codes.bodyTm, Tm.tree, Tree.size,
      num] at *
    omega

private theorem size_ifTm_le {k : Fin pS} {t : Tree} {a : Tm} (ht : t.size ≤ 5 * Lc) :
    (ifTm (C.name (.gate k)) t a).tree.size ≤ a.tree.size + 10 * Lc + 14 := by
  have := H.size_ofBits_le (H.name (.gate k))
  simp only [ifTm, Tm.tree, Tree.size, num]
  omega

private theorem size_digitTree (d : Fin D) : (C.digitTree d).size ≤ 5 * Lc :=
  H.size_ofBits_le (H.digit d)

private theorem size_slotTm (z : M.Slot) (a : Fin (K + K + A')) :
    (C.slotTm tab hD z a).tree.size ≤ 47 * (X * Lc) := by
  have := H.le_mul_X Lc
  have := H.one_le_Lc
  rw [Codes.slotTm, size_catTm]
  refine Nat.add_le_add_right (sum_map_le_mul (a := 33) H.one_le_Lc
    (by simpa [UnitId.list] using H.units) fun t ht => ?_) 3 |>.trans (by omega)
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
  have := size_ifTm_le H (k := tab.givenGate z u) (a := .c (listT [ofBits (C.key ⟨a, u⟩)]))
    (size_digitTree H ⟨1, hD⟩)
  have := H.size_ofBits_le (H.key ⟨a, u⟩)
  simp only [Tm.tree, listT, Tree.size, num] at *
  omega

private theorem size_roleTm (r : M.Role) : (C.roleTm tab tg hD r).tree.size ≤
    120 * (X * (X * Lc)) := by
  have a1 := H.le_mul_X Lc
  have a2 := H.le_mul_X (X * Lc)
  have a3 : X ≤ X * Lc := Nat.le_mul_of_pos_right X H.one_le_Lc
  have := H.one_le_Lc
  have l1 := size_listTm_le_mul (u := X * Lc) (a1.trans' H.one_le_Lc)
    (ts := (univ : Finset ((M.law r.1).SlotAt r.2)).toList.map fun e =>
      C.slotTm tab hD ⟨r.1, e.1⟩ (M.roleParty r)) (by simpa using H.slotsAt r) fun t ht => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 ht
        exact size_slotTm tab H _ _
  have l2 := size_listTm_le_mul (u := Lc) H.one_le_Lc
    (ts := (univ : Finset ((M.law r.1).ChannelAt r.2)).toList.map fun ν =>
      C.valueTm (.newKeys ⟨r.1, ν.1⟩ (decide ((M.law r.1).channelEnd ν.1 false ≠ r.2))))
    (by simpa using H.channelsAt r) fun t ht => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 ht
      exact size_valueTm H _
  have := size_valueTm H (.count r.1)
  have := H.roleNum r
  simp only [Codes.roleTm, Tm.tree, Tree.size, size_num, num] at *
  omega

private theorem size_endTm (hmm : mm ≤ D) (g : Fin mm) (u : UnitId (K + K) U0 M.Channel U1) :
    (C.endTm tab hD hmm g u).tree.size ≤ 300 * Lc := by
  have hd := size_digitTree H
  have := H.size_ofBits_le (H.name (.gate (tab.curGate u)))
  have := H.size_ofBits_le (H.name (.gate (tab.groupGate (UnitId.holder M.channelParty u false))))
  have := H.size_ofBits_le (H.name (.gate (tab.groupGate (UnitId.holder M.channelParty u true))))
  have := H.size_ofBits_le (H.key ⟨UnitId.holder M.channelParty u false, u⟩)
  have := H.size_ofBits_le (H.key ⟨UnitId.holder M.channelParty u true, u⟩)
  have := size_valueTm H (.content u)
  have := hd ⟨1, hD⟩
  have := hd (Fin.castLE hmm g)
  have := H.one_le_Lc
  simp only [Codes.endTm, ifTm, Codes.fixedTm, listTm, Tm.tree, Tree.size, Instruction.enc, listT,
    num] at *
  omega

private theorem size_pieceTm {bT bub : List Bool} (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)
    (hmm : mm ≤ D) {gp : Tree} (hgp : gp.size ≤ X) (g : Fin mm) :
    (C.pieceTm tab tg bT bub hD hmm gp g).tree.size ≤ 700 * (X * (X * (X * Lc))) := by
  have hX := H.one_le_X
  have hLc := H.one_le_Lc
  have a1 := H.le_mul_X Lc
  have a2 := H.le_mul_X (X * Lc)
  have a3 := H.le_mul_X (X * (X * Lc))
  have a4 : X ≤ X * Lc := Nat.le_mul_of_pos_right X hLc
  have hR : ((allRoles M).map fun r => ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
      (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r])).length ≤ X := by
    simpa using (show (allRoles M).Nodup from
      (pairwise_allRoles M).imp And.left).length_le_card.trans H.roles
  have s1 := sum_map_le_mul (a := 164) (b := 11) (a1.trans' hLc)
    (ts := (List.finRange (K + K)).map fun p => ifTm (C.name (.gate (tab.groupGate
      (Fin.castAdd A' p)))) (C.digitTree (Fin.castLE hmm g)) (C.basesTm p))
    (by simpa using H.parties)
    fun t ht => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 ht
      have := size_ifTm_le H (k := tab.groupGate (Fin.castAdd A' p)) (a := C.basesTm p)
        (size_digitTree H (Fin.castLE hmm g))
      have := size_basesTm H p
      omega
  have s2 := sum_map_le_mul (a := 154) (b := 11) (a2.trans' (a1.trans' hLc))
    (ts := (allRoles M).map fun r => ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
      (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r]))
    hR fun t ht => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ht
      have := size_ifTm_le H (k := tab.groupGate (M.roleParty r))
        (a := listTm [C.roleTm tab tg hD r])
        (size_digitTree H (Fin.castLE hmm g))
      have := size_roleTm (hD := hD) tab H r
      simp only [listTm, Tm.tree, Tree.size, num] at *
      omega
  have s3 := sum_map_le_mul (a := 300) (b := 11) hLc
    (ts := (UnitId.list (K + K) U0 M.Channel U1).map (C.endTm tab hD hmm g))
    (by simpa [UnitId.list] using H.units) fun t ht => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
      exact size_endTm (hD := hD) tab H hmm g u
  have := H.size_ofBits_le hbT
  have := H.size_ofBits_le hbub
  simp only [Codes.pieceTm, Codes.scriptTm, Tm.tree, Tree.size, size_catTm, List.map_append,
    List.sum_append, num]
  omega

variable {Γ : Type} {c : ℕ}

/-- **The size of the dealing program.** If `X` and `Lc` bound the numbers and the lengths of the
codes of the dealing program (`Codes.SizeBounds`), `X` also bounds the number `mm` of groups, the
length `c` of the codes of the letters and the size of the code `gp` of GROUP, and `Lc` the
lengths of the binary numbers `nl`, `nub`, `bT` and `bub`, then the dealing program has size at
most `(dealBaseSize + 3000) * (X * Lc) ^ 4`. -/
theorem size_dealProgram_le (hmX : mm ≤ X) (hc : c ≤ X) {nl nub bT bub : List Bool}
    (hnl : nl.length ≤ Lc) (hnub : nub.length ≤ Lc) (hbT : bT.length ≤ Lc)
    (hbub : bub.length ≤ Lc) (hmm : mm ≤ D) {gp : Tree} (hgp : gp.size ≤ X)
    (cb : Option Γ → Fin c → Bool) (bt : Bool → Γ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1).code.size ≤
      (dealBaseSize + 3000) * (X * Lc) ^ 4 := by
  have hX := H.one_le_X
  have hLc := H.one_le_Lc
  have a1 := H.le_mul_X Lc
  have a2 := H.le_mul_X (X * Lc)
  have a3 := H.le_mul_X (X * (X * Lc))
  have a4 := H.le_mul_X (X * (X * (X * Lc)))
  have a5 : X ≤ X * Lc := Nat.le_mul_of_pos_right X hLc
  have hb (d : Bool) : (ofBits (letterCode cb (bt d))).size ≤ 5 * X := by
    have := size_ofBits (letterCode cb (bt d))
    rw [letterCode, List.length_ofFn] at this
    rw [letterCode]
    omega
  have := hb false
  have := hb true
  have := H.size_ofBits_le hnl
  have := H.size_ofBits_le hnub
  have hn := size_listT_le_mul (a := 5) hX hLc
    (l := ((List.finRange K).map fun κ => C.name (.part κ)).map ofBits)
    (by simpa using (Nat.le_add_right K 1).trans H.blocks) fun t ht => by
      simp only [List.map_map, List.mem_map, List.mem_finRange, true_and] at ht
      obtain ⟨κ, rfl⟩ := ht
      exact H.size_ofBits_le (H.name _)
  have hs := size_listT_dealSteps_le H tab i e hU0 hU1
  have hs' := size_listT_contentSteps_le H
  have ht := size_listT_le_mul (a := 700) hX (a3.trans' (a2.trans' (a1.trans' hLc)))
    (l := ((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)).map Tm.tree)
    (by simpa using hmX) fun t ht => by
      simp only [List.map_map, List.mem_map, List.mem_finRange, true_and] at ht
      obtain ⟨g, rfl⟩ := ht
      exact size_pieceTm tab H hbT hbub hmm hgp g
  have hP : X * (X * (X * (X * Lc))) ≤ (X * Lc) ^ 4 := by
    calc X * (X * (X * (X * Lc))) = X ^ 4 * Lc := by ring
      _ ≤ X ^ 4 * Lc ^ 4 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) Lc)
      _ = (X * Lc) ^ 4 := by ring
  have h1 : 1 ≤ (X * Lc) ^ 4 := Nat.one_le_pow _ _ (Nat.mul_le_mul hX hLc)
  have := size_dealFormula_le (ofBits (letterCode cb (bt false))) (ofBits (letterCode cb (bt true)))
    ((List.finRange K).map fun κ => C.name (.part κ)) nl nub (C.dealSteps tab qn i e hU0 hU1)
    C.contentSteps ((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp))
  rw [Codes.dealProgram]
  have e : (dealBaseSize + 3000) * (X * Lc) ^ 4 = dealBaseSize * (X * Lc) ^ 4 +
    3000 * (X * Lc) ^ 4 := by ring
  have := Nat.le_mul_of_pos_right dealBaseSize h1
  omega

end Cslib.Circuits.Arithmetic.Separation.Dealing
