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
# The cost of the templates of the dealing program

At a state with the values of the end (`Final`), the template of the instance of GROUP at the
script of a group (`Codes.pieceTm`) costs at most `pieceBound Lc X` to fill
(`cost_pieceTm_le`), where `Lc` bounds the lengths of the codes of the names and of the digits,
and `X` bounds the numbers of the tapes, the base parties, the units, the roles and the slots and
channels of a role, and the units of a string plus one.

## Main definitions

* `pieceBound`: a bound for the cost of filling the template of a piece.

## Main results

* `cost_pieceTm_le`: the cost of filling the template of a piece.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: it writes for each piece its script). Ported from the source module
`Nc.Dl.Bd3`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- A bound for the cost of filling the template of a piece, for codes of length at most `Lc`
and at most `X` tapes, base parties, units, roles, slots and channels of a role, and units of a
string plus one. -/
@[expose] def pieceBound (Lc X : ℕ) : ℕ :=
  X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) +
    X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) +
    X * (2000 * Lc + 5000) + 1000

section Lists

variable {σ : List Bool → Tree} {X b : ℕ}

private theorem cost_listTm (ts : List Tm) :
    (listTm ts).cost σ = (ts.map fun t => t.cost σ + 100).sum + 20 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [listTm, Tm.cost, ih, List.map_cons, List.sum_cons]; omega

/-- At most `X` terms of at most `b` each, with `k` more for each, sum to at most `X * (b + k)`. -/
private theorem sum_map_add_le {α : Type*} {l : List α} {f : α → ℕ} {k : ℕ} (hl : l.length ≤ X)
    (h : ∀ a ∈ l, f a ≤ b) : (l.map fun a => f a + k).sum ≤ X * (b + k) :=
  (List.sum_le_length_nsmul _ (b + k) (by simpa using h)).trans
    (by simpa using Nat.mul_le_mul_right (b + k) hl)

private theorem cost_listTm_le {ts : List Tm} (hl : ts.length ≤ X) (h : ∀ t ∈ ts, t.cost σ ≤ b) :
    (listTm ts).cost σ ≤ X * (b + 100) + 20 := by
  rw [cost_listTm]
  exact Nat.add_le_add_right (sum_map_add_le hl h) 20

private theorem cost_catTm (ts : List Tm) : (catTm ts).cost σ =
    (ts.map fun t => t.cost σ + 62 * (t.expand σ).toList.length + 250).sum + 20 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [catTm, Tm.cost, ih, List.map_cons, List.sum_cons]; omega

/-- The cost of a concatenation whose parts cost at most `b` with `62` per element of their
expansions. -/
private theorem cost_catTm_le {ts : List Tm} (hl : ts.length ≤ X)
    (h : ∀ t ∈ ts, t.cost σ + 62 * (t.expand σ).toList.length ≤ b) :
    (catTm ts).cost σ ≤ X * (b + 250) + 20 := by
  rw [cost_catTm]
  exact Nat.add_le_add_right (sum_map_add_le hl h) 20

end Lists

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm ub : ℕ}
  {M : Moves F (K + K + A') E} {S Q : Type} [Fintype S] {C : Codes S M U0 U1 D pS}
  {P : Plan M U0 U1} {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}
  {tab : SlpTab P grp D nI pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.Channel → Fin U1} {b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub}
  {st : PlanName S M U0 U1 pS → Tree} {Lc X : ℕ} {hD : 1 < D}
  (hst : Final C tab qn pt q ρ n o b st) (hnm : ∀ y, (C.name y).length ≤ Lc)
  (hdc : ∀ d, (C.digit d).length ≤ Lc)

include hnm in
omit [Fintype S] in
private theorem cost_valueTm (y : PlanName S M U0 U1 pS) (σ : List Bool → Tree) :
    (C.valueTm y).cost σ ≤ 30 * Lc + 50 := by
  have := hnm y
  simp only [Codes.valueTm, Tm.cost]
  omega

include hst hnm hdc

omit [Fintype S] in
/-- A comparison reads the name of a step of the straight-line program and its digit. -/
private theorem cost_gate (k : Fin pS) : 30 * (C.name (.gate k)).length +
    60 * ((extend C.name st fun _ => .nil) (C.name (.gate k))).size ≤ 270 * Lc + 60 := by
  have := hnm (.gate k)
  have := size_ofBits (C.digit (tab.fn k ⟨n, o⟩))
  have := hdc (tab.fn k ⟨n, o⟩)
  rw [C.name_injective.extend_apply, hst.gate, Codes.digitTree]
  omega

omit [Fintype S] in
private theorem cost_ifTm (k : Fin pS) (t : Tree) (a : Tm) :
    (ifTm (C.name (.gate k)) t a).cost (extend C.name st fun _ => .nil) ≤
      a.cost (extend C.name st fun _ => .nil) + 270 * Lc + 280 := by
  have := cost_gate hst hnm hdc k
  simp only [ifTm, Tm.cost, ite_self]
  omega

variable (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K ≤ X)
  (hId : Fintype.card (UnitId (K + K) U0 M.Channel U1) ≤ X)
include hS hK2

omit hst hdc in
private theorem cost_basesTm (p : Fin (K + K)) :
    (C.basesTm p).cost (extend C.name st fun _ => .nil) ≤
      3 * (X * (30 * Lc + 150)) + 90 * Lc + 1000 := by
  have hl (ts : List Tm) (hl : ts.length ≤ X) (h : ∀ t ∈ ts, ∃ y, t = C.valueTm y) :
      (listTm ts).cost (extend C.name st fun _ => .nil) ≤ X * (30 * Lc + 150) + 20 :=
    cost_listTm_le hl fun t ht => by
      obtain ⟨y, rfl⟩ := h t ht
      exact cost_valueTm hnm y _
  have h1 := hl ((tapes S).map fun s => C.valueTm (.flags s p)) (by simpa [tapes] using hS)
    (by simp)
  have h2 := hl (List.ofFn fun b => C.valueTm (.writeKeys p b)) (by simpa using hK2) (by simp)
  have h3 := hl (List.ofFn fun b => C.valueTm (.readKeys b p)) (by simpa using hK2) (by simp)
  have h4 := cost_valueTm hnm (.selfAgree p) (extend C.name st fun _ => .nil)
  induction p using Fin.addCases with
  | left κ =>
    have := cost_valueTm hnm (.state κ.castSucc) (extend C.name st fun _ => .nil)
    have := cost_valueTm hnm (.state κ.succ) (extend C.name st fun _ => .nil)
    simp only [Codes.basesTm, Codes.baseTm, Fin.addCases_left, Codes.bodyTm, Tm.cost] at *
    omega
  | right κ =>
    have := cost_valueTm hnm (.part κ) (extend C.name st fun _ => .nil)
    simp only [Codes.basesTm, Codes.baseTm, Fin.addCases_right, Codes.bodyTm, Tm.cost] at *
    omega

include hId

omit [Fintype S] hS hK2 in
private theorem cost_slotTm (z : M.Slot) (a : Fin (K + K + A')) :
    (C.slotTm tab hD z a).cost (extend C.name st fun _ => .nil) ≤ X * (270 * Lc + 700) + 20 := by
  refine (cost_catTm_le (b := 270 * Lc + 450) (by simpa [UnitId.list] using hId)
    fun t ht => ?_).trans (le_of_eq (by ring))
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
  have h1 := cost_ifTm hst hnm hdc (tab.givenGate z u) (C.digitTree ⟨1, hD⟩)
    (.c (listT [ofBits (C.key ⟨a, u⟩)]))
  have h2 : ((ifTm (C.name (.gate (tab.givenGate z u))) (C.digitTree ⟨1, hD⟩)
      (.c (listT [ofBits (C.key ⟨a, u⟩)]))).expand (extend C.name st fun _ => .nil)).toList.length
        ≤ 1 := by
    rw [toList_expand_ifTm]; split_ifs <;> simp [Tm.expand]
  simp only [Tm.cost] at h1
  omega

variable (hSl : ∀ r : M.Role, Fintype.card ((M.law r.1).SlotAt r.2) ≤ X)
  (hCn : ∀ r : M.Role, Fintype.card ((M.law r.1).ChannelAt r.2) ≤ X)
include hSl hCn

omit [Fintype S] hS hK2 in
private theorem cost_roleTm (tg : M.Role → ℕ) (r : M.Role) :
    (C.roleTm tab tg hD r).cost (extend C.name st fun _ => .nil) ≤
      X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 30 * Lc + 500 := by
  have h1 := cost_listTm_le (σ := extend C.name st fun _ => .nil) (X := X)
    (ts := (univ : Finset ((M.law r.1).SlotAt r.2)).toList.map fun e =>
      C.slotTm tab hD ⟨r.1, e.1⟩ (M.roleParty r)) (by simpa using hSl r) fun t ht => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 ht
        exact cost_slotTm hst hnm hdc hId _ _
  have h2 := cost_listTm_le (σ := extend C.name st fun _ => .nil) (X := X)
    (ts := (univ : Finset ((M.law r.1).ChannelAt r.2)).toList.map fun ν =>
      C.valueTm (.newKeys ⟨r.1, ν.1⟩ (decide ((M.law r.1).channelEnd ν.1 false ≠ r.2))))
    (by simpa using hCn r) fun t ht => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 ht
      exact cost_valueTm hnm _ _
  have h3 := cost_valueTm hnm (.count r.1) (extend C.name st fun _ => .nil)
  simp only [Codes.roleTm, Tm.cost] at *
  linarith

omit [Fintype S] hS hK2 hId hSl hCn in
private theorem cost_endTm (hmm : mm ≤ D) (g : Fin mm) (u : UnitId (K + K) U0 M.Channel U1) :
    (C.endTm tab hD hmm g u).cost (extend C.name st fun _ => .nil) +
      62 * ((C.endTm tab hD hmm g u).expand (extend C.name st fun _ => .nil)).toList.length ≤
        2000 * Lc + 4062 := by
  have hl : ((C.endTm tab hD hmm g u).expand (extend C.name st fun _ => .nil)).toList.length ≤ 1 :=
    by
    simp only [Codes.endTm, toList_expand_ifTm, Tm.expand, Codes.fixedTm, expand_listTm]
    split_ifs <;> simp [toList_expand_ifTm, expand_listTm]
    split_ifs <;> simp
  have := cost_gate hst hnm hdc (tab.curGate u)
  have := cost_gate hst hnm hdc (tab.groupGate (UnitId.holder M.channelParty u false))
  have := cost_gate hst hnm hdc (tab.groupGate (UnitId.holder M.channelParty u true))
  have := cost_valueTm hnm (.content u) (extend C.name st fun _ => .nil)
  simp only [Codes.endTm, ifTm, Codes.fixedTm, listTm, Tm.cost, ite_self] at *
  omega

include hId hSl hCn

/-- **The cost of a piece.** At a state with the values of the end, filling the template of the
instance of GROUP at the script of a group costs at most `pieceBound Lc X`, if `Lc` bounds the
lengths of the codes of the names and the digits and `X` bounds the numbers of the tapes, the
base parties, the units, the roles and the slots and channels of a role, and the units of a
string plus one. -/
theorem cost_pieceTm_le (hXU0 : U0 + 1 ≤ X) (hR : Fintype.card M.Role ≤ X) (tg : M.Role → ℕ)
    (bT bub : List Bool) (hmm : mm ≤ D) (gp : Tree) (g : Fin mm) :
    (C.pieceTm tab tg bT bub hD hmm gp g).cost (extend C.name st fun _ => .nil) ≤
      pieceBound Lc X := by
  have h1 := cost_catTm_le (σ := extend C.name st fun _ => .nil) (X := X)
    (b := 3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 1750)
    (ts := (List.finRange (K + K)).map fun p => ifTm (C.name (.gate (tab.groupGate
      (Fin.castAdd A' p)))) (C.digitTree (Fin.castLE hmm g)) (C.basesTm p)) (by simpa using hK2)
    fun t ht => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 ht
      have := cost_ifTm hst hnm hdc (tab.groupGate (Fin.castAdd A' p))
        (C.digitTree (Fin.castLE hmm g)) (C.basesTm p)
      have := cost_basesTm (st := st) hnm hS hK2 p
      have : ((ifTm (C.name (.gate (tab.groupGate (Fin.castAdd A' p))))
          (C.digitTree (Fin.castLE hmm g)) (C.basesTm p)).expand
            (extend C.name st fun _ => .nil)).toList.length ≤ X := by
        rw [toList_expand_ifTm]
        split_ifs
        · simp [Codes.basesTm, Tm.expand, Codes.valueTm, C.name_injective.extend_apply,
            hst.selfAgree, Codes.selfAgreeTree, Tree.toList]
          omega
        · simp
      omega
  have h2 := cost_catTm_le (σ := extend C.name st fun _ => .nil) (X := X)
    (b := X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1250)
    (ts := (allRoles M).map fun r => ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
      (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r]))
    (by simpa using (show (allRoles M).Nodup from
      (pairwise_allRoles M).imp And.left).length_le_card.trans hR)
    fun t ht => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ht
      have := cost_ifTm hst hnm hdc (tab.groupGate (M.roleParty r))
        (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r])
      have := cost_roleTm (hD := hD) hst hnm hdc hId hSl hCn tg r
      have : ((ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
          (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r])).expand
            (extend C.name st fun _ => .nil)).toList.length ≤ 1 := by
        rw [toList_expand_ifTm]; split_ifs <;> simp [expand_listTm]
      simp only [listTm, Tm.cost] at *
      omega
  have h3 := cost_catTm_le (σ := extend C.name st fun _ => .nil) (X := X)
    (b := 2000 * Lc + 4750) (ts := (UnitId.list (K + K) U0 M.Channel U1).map
      (C.endTm tab hD hmm g)) (by simpa [UnitId.list] using hId) fun t ht => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
      have := cost_endTm (hD := hD) hst hnm hdc hmm g u
      omega
  have e (l₁ l₂ : List Tm) : (catTm (l₁ ++ l₂)).cost (extend C.name st fun _ => .nil) + 20 =
      (catTm l₁).cost (extend C.name st fun _ => .nil) +
        (catTm l₂).cost (extend C.name st fun _ => .nil) := by
    simp only [cost_catTm, List.map_append, List.sum_append]; omega
  have e₁ := e (((List.finRange (K + K)).map fun p => ifTm (C.name (.gate (tab.groupGate
    (Fin.castAdd A' p)))) (C.digitTree (Fin.castLE hmm g)) (C.basesTm p)) ++
      (allRoles M).map fun r => ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
        (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r]))
    ((UnitId.list (K + K) U0 M.Channel U1).map (C.endTm tab hD hmm g))
  have e₂ := e ((List.finRange (K + K)).map fun p => ifTm (C.name (.gate (tab.groupGate
    (Fin.castAdd A' p)))) (C.digitTree (Fin.castLE hmm g)) (C.basesTm p))
      ((allRoles M).map fun r => ifTm (C.name (.gate (tab.groupGate (M.roleParty r))))
        (C.digitTree (Fin.castLE hmm g)) (listTm [C.roleTm tab tg hD r]))
  simp only [Codes.pieceTm, Codes.scriptTm, Tm.cost, pieceBound]
  ring_nf at h1 h2 h3 ⊢
  omega

end Cslib.Circuits.Arithmetic.Separation.Dealing
