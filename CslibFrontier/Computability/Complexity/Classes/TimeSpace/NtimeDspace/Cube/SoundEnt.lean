/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundCopies
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundTr

/-!
# The entries of the tables of the formula

* `factorG`: the factor states of an entry, for an arbitrary parent and child clique;
  `Setup.factorSt_eq`: they are the factor states of the formula.
* `ent_row`, `ent_col`: an entry of a row (column) clique is the sum, over the valid codes of
  copies, of the product of the meanings of its factors.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset MergeProof

/-- The packed labels of node `v` of a child clique, at the labels coded by `args`. -/
def Θof (Cc : Clique) (v args : ℕ) : ℕ → Label := fun A' =>
  if h : A' < Cc.q ∧ v < Cc.q then decodeArgs Cc ⟨v, h.2⟩ args ⟨A', h.1⟩ else (0, 0)

/-- The rectangle factor at the quadruple `(A₁, A₂, B₁, B₂)`. -/
noncomputable def psiG (P Cc : Clique) (g : ℕ) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (ι : Rect g → ℤ × ℤ) (row : Bool) (v args ξ A₁ A₂ B₁ B₂ : ℕ) : St :=
  let nodes := Setup.holders g v row
  let Θ := Θof Cc v args
  let cp := copyAt P nodes ξ
  let nd : ℕ → ℕ → ℕ := fun A B => A * g + B
  if h : A₁ < A₂ ∧ B₁ < B₂ ∧ A₂ < g ∧ B₂ < g then
    let r : Rect g := ⟨((⟨A₁, by omega⟩, ⟨A₂, h.2.2.1⟩), (⟨B₁, by omega⟩, ⟨B₂, h.2.2.2⟩)),
      h.1, h.2.1⟩
    let k := (ι r).1; let c := (ι r).2
    let H : ℤ := diagWt a r
    if row then
      if v = A₁ then
        let m := unpack (packL g) (Θ A₂) (rStream g ⟨B₁, by omega⟩ ⟨B₂, h.2.2.2⟩)
        if (labelWt m : ℤ) ≤ H + k / 2 then
          let x := cp B₁ (nd A₂ B₂); let y := cp B₂ (nd A₂ B₁)
          .tr true x y m 0 (srcList true x y m).length (tgtMs true x y m) (k - c)
        else .zero
      else if v = A₂ then
        let m := unpack (packL g) (Θ A₁) (rStream g ⟨B₁, by omega⟩ ⟨B₂, h.2.2.2⟩)
        if (labelWt m : ℤ) ≤ H + k / 2 then
          let x := swapLabel (cp B₁ (nd A₁ B₂)); let y := swapLabel (cp B₂ (nd A₁ B₁))
          .tr false x y m 0 (srcList false x y m).length (tgtMs false x y m) c
        else .zero
      else .lit 1
    else
      if v = B₁ then
        let m := unpack (packL g) (Θ B₂) (rStream g ⟨A₁, by omega⟩ ⟨A₂, h.2.2.1⟩)
        if (labelWt m : ℤ) ≤ H - k / 2 then
          let x := cp A₁ (nd A₂ B₂); let y := swapLabel (cp A₂ (nd A₁ B₂))
          .tr true x y m 0 (srcList true x y m).length (tgtMs true x y m) (-k - c)
        else .zero
      else if v = B₂ then
        let m := unpack (packL g) (Θ B₁) (rStream g ⟨A₁, by omega⟩ ⟨A₂, h.2.2.1⟩)
        if (labelWt m : ℤ) ≤ H - k / 2 then
          let x := cp A₁ (nd A₂ B₁); let y := swapLabel (cp A₂ (nd A₁ B₁))
          .tr false x y m 0 (srcList false x y m).length (tgtMs false x y m) c
        else .zero
      else .lit 1
  else .lit 1

/-- The factor states of an entry, for a parent `P` and a child `Cc`. -/
noncomputable def factorG (rest : List ℕ) (P Cc : Clique) (g : ℕ)
    (a : Fin (g * g) → Fin (g * g) → ℕ)
    (ι : Rect g → ℤ × ℤ) (row : Bool) (v args ξ f : ℕ) : St :=
  let nodes := Setup.holders g v row
  let Θ := Θof Cc v args
  let cp := copyAt P nodes ξ
  let nd : ℕ → ℕ → ℕ := fun A B => A * g + B
  if f < g then .ent rest (nodes f) (slice P nodes ξ f)
  else if f < g + g * g then
    let t := f - g; let p := t / g; let p' := t % g
    .lit (if p < p' ∧ cp p (nodes p') ≠ cp p' (nodes p) then 0 else 1)
  else if f < g + g * g + g * g then
    let t := f - g - g * g; let o := t / g; let p := t % g
    .lit (if o ≠ v ∧ cp p (if row then nd o p else nd p o) ≠ unpack (packL g) (Θ o) (1 + p)
      then 0 else 1)
  else
    let (A₁, A₂, B₁, B₂) := quad g (f - g - g * g - g * g)
    psiG P Cc g a ι row v args ξ A₁ A₂ B₁ B₂

theorem Setup.factorSt_eq (S : Setup) (rest : List ℕ) (i v args ξ f : ℕ)
    (h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q) :
    S.factorSt rest i v args ξ f =
      factorG rest (S.clique rest) (S.clique (i :: rest)) (Nat.sqrt (S.clique rest).q)
        ((S.clique rest).recast _ h).a (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i)
        (orientRow ((S.clique rest).recast _ h).a
          fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1) v args ξ f := by
  simp only [Setup.factorSt, Setup.parentGrid, dite_eq_left h]
  rfl

/-- The meaning of a factor state at the parent `P`. -/
noncomputable def fval (P : Clique) : St → ℤ
  | .zero => 0
  | .lit w => w
  | .ent _ n x => cEntry P n x
  | .tr up x y m lo hi T c => Setup.trMean up x y m lo hi T c
  | _ => 0

theorem psiG_shape (P Cc : Clique) (g : ℕ) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (ι : Rect g → ℤ × ℤ) (row : Bool) (v args ξ A₁ A₂ B₁ B₂ : ℕ) :
    psiG P Cc g a ι row v args ξ A₁ A₂ B₁ B₂ = .zero ∨
      (∃ w, psiG P Cc g a ι row v args ξ A₁ A₂ B₁ B₂ = .lit w) ∨
      ∃ up x y m e, psiG P Cc g a ι row v args ξ A₁ A₂ B₁ B₂ =
        .tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) e := by
  unfold psiG
  dsimp only
  split_ifs <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩)

/-- **The shape of a factor state.** -/
theorem factorG_shape (rest : List ℕ) (P Cc : Clique) (g : ℕ) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (ι : Rect g → ℤ × ℤ) (row : Bool) (v args ξ f : ℕ) :
    factorG rest P Cc g a ι row v args ξ f = .zero ∨
      (∃ w, factorG rest P Cc g a ι row v args ξ f = .lit w) ∨
      (f < g ∧ factorG rest P Cc g a ι row v args ξ f =
        .ent rest (Setup.holders g v row f) (slice P (Setup.holders g v row) ξ f)) ∨
      ∃ up x y m e, factorG rest P Cc g a ι row v args ξ f =
        .tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) e := by
  by_cases h1 : f < g
  · exact Or.inr (Or.inr (Or.inl ⟨h1, by simp only [factorG, ite_eq_left h1]⟩))
  by_cases h2 : f < g + g * g
  · exact Or.inr (Or.inl (by simp only [factorG, ite_eq_right h1, ite_eq_left h2]; exact ⟨_, rfl⟩))
  by_cases h3 : f < g + g * g + g * g
  · exact Or.inr (Or.inl (by
      simp only [factorG, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]; exact ⟨_, rfl⟩))
  unfold factorG
  simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  generalize quad g (f - g - g * g - g * g) = qd
  obtain ⟨A₁, A₂, B₁, B₂⟩ := qd
  dsimp only
  rcases psiG_shape P Cc g a ι row v args ξ A₁ A₂ B₁ B₂ with h | ⟨w, h⟩ | ⟨up, x, y, m, e, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨w, h⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨up, x, y, m, e, h⟩))

/-! ### Arithmetic of the grid -/

theorem nd_div {g : ℕ} (A B : ℕ) (hB : B < g) : (A * g + B) / g = A := by
  have hg : 0 < g := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hB, zero_add]

theorem nd_mod {g : ℕ} (A B : ℕ) (hB : B < g) : (A * g + B) % g = B := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]

theorem quad_eq {g : ℕ} {A₁ A₂ B₁ B₂ : ℕ} (h1 : A₁ < g) (h2 : A₂ < g) (h3 : B₁ < g) (h4 : B₂ < g) :
    quad g ((A₁ * g + A₂) * (g * g) + (B₁ * g + B₂)) = (A₁, A₂, B₁, B₂) := by
  have e : (A₁ * g + A₂) * (g * g) + (B₁ * g + B₂) = ((A₁ * g + A₂) * g + B₁) * g + B₂ := by ring
  have d1 : (((A₁ * g + A₂) * g + B₁) * g + B₂) / g = (A₁ * g + A₂) * g + B₁ := nd_div _ _ h4
  have d2 : ((A₁ * g + A₂) * g + B₁) / g = A₁ * g + A₂ := nd_div _ _ h3
  have d3 : (A₁ * g + A₂) / g = A₁ := nd_div _ _ h2
  unfold quad
  rw [e, show g ^ 3 = g * g * g by ring, show g ^ 2 = g * g by ring]
  simp only [← Nat.div_div_eq_div_mul]
  rw [d1, d2, d3, nd_mod _ _ h4, nd_mod _ _ h3, nd_mod _ _ h2, Nat.mod_eq_of_lt h1]

theorem holders_lt {g v : ℕ} (hv : v < g) (row : Bool) {p : ℕ} (hp : p < g) :
    Setup.holders g v row p < g * g := by
  unfold Setup.holders
  split_ifs
  · exact (node (g := g) ⟨v, hv⟩ ⟨p, hp⟩).isLt
  · exact (node (g := g) ⟨p, hp⟩ ⟨v, hv⟩).isLt

theorem copyAt_eq (C : Clique) (nodes : ℕ → ℕ) (ξ p : ℕ) (hp : nodes p < C.q) (u : Fin C.q) :
    copyAt C nodes ξ p u = decodeArgs C ⟨nodes p, hp⟩ (slice C nodes ξ p) u := by
  unfold copyAt; rw [dite_eq_left ⟨hp, u.isLt⟩]

theorem prod_rect_dite {M : Type*} [CommMonoid M] {g : ℕ} (ψ : Rect g → M) :
    ∏ r : Rect g, ψ r = ∏ A₁ : Fin g, ∏ A₂ : Fin g, ∏ B₁ : Fin g, ∏ B₂ : Fin g,
      if h : A₁ < A₂ ∧ B₁ < B₂ then ψ ⟨((A₁, A₂), (B₁, B₂)), h⟩ else 1 := by
  classical
  let F : (Fin g × Fin g) × (Fin g × Fin g) → M := fun x =>
    if h : x.1.1 < x.1.2 ∧ x.2.1 < x.2.2 then ψ ⟨x, h⟩ else 1
  have e1 : ∏ r : Rect g, ψ r = ∏ r : Rect g, F r.1 := by
    refine Fintype.prod_congr _ _ fun r => ?_
    simp only [F, dite_eq_left r.2]
  have e2 := Finset.prod_subtype (p := fun x : (Fin g × Fin g) × (Fin g × Fin g) =>
    x.1.1 < x.1.2 ∧ x.2.1 < x.2.2) (F := inferInstance)
        (univ.filter fun x : (Fin g × Fin g) × (Fin g × Fin g) =>
    x.1.1 < x.1.2 ∧ x.2.1 < x.2.2) (by simp) F
  rw [e1, ← e2, Finset.prod_filter]
  have e3 : ∀ x, (if x.1.1 < x.1.2 ∧ x.2.1 < x.2.2 then F x else 1) = F x := fun x => by
    by_cases h : x.1.1 < x.1.2 ∧ x.2.1 < x.2.2
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; simp only [F, dite_eq_right h]
  simp only [e3, Fintype.prod_prod_type, F]

/-! ### The four blocks of factors -/

section Blocks

variable {g : ℕ} (aP : Fin (g * g) → Fin (g * g) → ℕ) (TP : Fin (g * g) → (Fin (g * g) → Label) → ℤ)
  (rest : List ℕ) (Cc : Clique) (a : Fin (g * g) → Fin (g * g) → ℕ)
      (ι : Rect g → ℤ × ℤ) (row : Bool)
  (v : Fin g) (args ξ : ℕ)

theorem block_ent (n : Fin g → Fin (g * g))
    (hn : ∀ p : Fin g, (n p).val = Setup.holders g v row p) :
    ∏ x ∈ range g, fval ⟨g * g, aP, TP⟩ (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ x) =
      ∏ B : Fin g, TP (n B) (fun u => copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ B u) := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine Fintype.prod_congr _ _ fun B => ?_
  have hx : (B : ℕ) < g := B.isLt
  have hlt : Setup.holders g v row B < g * g := holders_lt v.isLt row hx
  simp only [factorG, ite_eq_left hx, fval, cEntry]
  rw [dite_eq_left hlt]
  have e : ∀ u : Fin (g * g), copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ B u =
      decodeArgs ⟨g * g, aP, TP⟩ ⟨Setup.holders g v row B, hlt⟩
        (slice ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ B) u :=
    fun u => copyAt_eq ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ B hlt u
  simp only [e]
  have hnB : (⟨Setup.holders g v row B, hlt⟩ : Fin (g * g)) = n B := Fin.ext (hn B).symm
  rw [hnB]

theorem block_hor (n : Fin g → Fin (g * g))
    (hn : ∀ p : Fin g, (n p).val = Setup.holders g v row p) :
    ∏ x ∈ range (g * g), fval ⟨g * g, aP, TP⟩
        (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ (g + x)) =
      ∏ B : Fin g, ∏ B' : Fin g,
        if B < B' ∧ copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ B (n B') ≠
          copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ B' (n B) then 0 else 1 := by
  rw [← Fin.prod_univ_eq_prod_range (fun x => fval ⟨g * g, aP, TP⟩
    (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ (g + x))) (g * g), prod_nodes]
  refine Fintype.prod_congr _ _ fun B => Fintype.prod_congr _ _ fun B' => ?_
  have hv := (node B B').isLt
  have h1 : ¬ (g + (node B B' : ℕ) < g) := by omega
  have h2 : g + (node B B' : ℕ) < g + g * g := by omega
  have hd : (g + (node B B' : ℕ) - g) / g =
      B := by rw [Nat.add_sub_cancel_left, node_val, nd_div _ _ B'.isLt]
  have hm : (g + (node B B' : ℕ) - g) % g =
      B' := by rw [Nat.add_sub_cancel_left, node_val, nd_mod _ _ B'.isLt]
  simp only [factorG, ite_eq_right h1, ite_eq_left h2, hd, hm, fval, hn, Fin.lt_def]

theorem block_vert :
    ∏ x ∈ range (g * g), fval ⟨g * g, aP, TP⟩
        (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ (g + g * g + x)) =
      ∏ o : Fin g, ∏ p : Fin g,
        if (o : ℕ) ≠ v ∧ copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v row) ξ p
            (if row then o * g + p else p * g + o) ≠ unpack (packL g) (Θof Cc v args o) (1 + p)
          then 0 else 1 := by
  rw [← Fin.prod_univ_eq_prod_range (fun x => fval ⟨g * g, aP, TP⟩
    (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ (g + g * g + x))) (g * g), prod_nodes]
  refine Fintype.prod_congr _ _ fun o => Fintype.prod_congr _ _ fun p => ?_
  have hv := (node o p).isLt
  have h1 : ¬ (g + g * g + (node o p : ℕ) < g) := by omega
  have h2 : ¬ (g + g * g + (node o p : ℕ) < g + g * g) := by omega
  have h3 : g + g * g + (node o p : ℕ) < g + g * g + g * g := by omega
  have hd : (g + g * g + (node o p : ℕ) - g - g * g) / g = o := by
    rw [show g + g * g + (node o p : ℕ) - g - g * g =
        (node o p : ℕ) by omega, node_val, nd_div _ _ p.isLt]
  have hm : (g + g * g + (node o p : ℕ) - g - g * g) % g = p := by
    rw [show g + g * g + (node o p : ℕ) - g - g * g =
        (node o p : ℕ) by omega, node_val, nd_mod _ _ p.isLt]
  simp only [factorG, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, hd, hm, fval]

theorem block_psi :
    ∏ x ∈ range (g ^ 4), fval ⟨g * g, aP, TP⟩
        (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ (g + g * g + g * g + x)) =
      ∏ A₁ : Fin g, ∏ A₂ : Fin g, ∏ B₁ : Fin g, ∏ B₂ : Fin g,
        fval ⟨g * g, aP, TP⟩ (psiG ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ A₁ A₂ B₁ B₂) := by
  rw [show g ^ 4 = (g * g) * (g * g) by ring]
  rw [← Fin.prod_univ_eq_prod_range (fun x => fval ⟨g * g, aP, TP⟩
    (factorG rest ⟨g * g, aP, TP⟩ Cc g a ι row v args ξ (g + g * g + g * g + x)))
        ((g * g) * (g * g)),
    prod_nodes]
  simp only [prod_nodes (g := g)]
  refine Fintype.prod_congr _ _ fun A₁ => Fintype.prod_congr _ _ fun A₂ =>
    Fintype.prod_congr _ _ fun B₁ => Fintype.prod_congr _ _ fun B₂ => ?_
  have hv := (node (node A₁ A₂) (node B₁ B₂)).isLt
  have h1 : ¬ (g + g * g + g * g + (node (node A₁ A₂) (node B₁ B₂) : ℕ) < g) := by omega
  have h2 : ¬ (g + g * g + g * g + (node (node A₁ A₂) (node B₁ B₂) : ℕ) < g + g * g) := by omega
  have h3 : ¬ (g + g * g + g * g + (node (node A₁ A₂) (node B₁ B₂) : ℕ) < g + g * g + g * g) := by
    omega
  have hq : quad g (g + g * g + g * g + (node (node A₁ A₂) (node B₁ B₂) : ℕ) - g - g * g - g * g) =
      ((A₁ : ℕ), (A₂ : ℕ), (B₁ : ℕ), (B₂ : ℕ)) := by
    rw [show g + g * g + g * g + (node (node A₁ A₂) (node B₁ B₂) : ℕ) - g - g * g - g * g =
      (node (node A₁ A₂) (node B₁ B₂) : ℕ) by omega, node_val, node_val, node_val]
    exact quad_eq A₁.isLt A₂.isLt B₁.isLt B₂.isLt
  simp only [factorG, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, hq]

end Blocks

/-! ### The rectangle factors -/

section Psi

variable {g : ℕ} (aP : Fin (g * g) → Fin (g * g) → ℕ) (TP : Fin (g * g) → (Fin (g * g) → Label) → ℤ)
  (a : Fin (g * g) → Fin (g * g) → ℕ) (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ)
  (ι : Rect g → ℤ × ℤ) (v : Fin g) (args ξ : ℕ)

theorem Θof_row (A' : Fin g) : Θof (rowChild g a T ι) v args A' = decodeArgs (rowChild g a T ι) v
    args A' := by
  unfold Θof; rw [dite_eq_left ⟨A'.isLt, v.isLt⟩]; rfl

theorem Θof_col (A' : Fin g) : Θof (colChild g a T ι) v args A' = decodeArgs (colChild g a T ι) v
    args A' := by
  unfold Θof; rw [dite_eq_left ⟨A'.isLt, v.isLt⟩]; rfl

theorem psi_row (A₁ A₂ B₁ B₂ : Fin g) :
    fval ⟨g * g, aP, TP⟩ (psiG ⟨g * g, aP, TP⟩ (rowChild g a T ι) g a ι true v args ξ A₁ A₂ B₁ B₂) =
      if h : A₁ < A₂ ∧ B₁ < B₂ then
        rowPsi a ι v (decodeArgs (rowChild g a T ι) v args)
          (fun B u => copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v true) ξ B u)
              ⟨((A₁, A₂), (B₁, B₂)), h⟩
      else 1 := by
  by_cases h : A₁ < A₂ ∧ B₁ < B₂
  · rw [dite_eq_left h]
    simp only [psiG, dite_eq_left (show (A₁ : ℕ) < A₂ ∧ (B₁ : ℕ) < B₂ ∧ (A₂ : ℕ) < g ∧
        (B₂ : ℕ) < g from
      ⟨h.1, h.2, A₂.isLt, B₂.isLt⟩), rowPsi, ite_true, Θof_row]
    by_cases e1 : v = A₁
    · have e1' : (v : ℕ) = A₁ := congrArg Fin.val e1
      simp only [e1, ite_true]
      split_ifs <;> simp only [fval, trMean_root_up]; rfl
    · have e1' : (v : ℕ) ≠ A₁ := fun e => e1 (Fin.ext e)
      simp only [e1', e1, ite_false]
      by_cases e2 : v = A₂
      · have e2' : (v : ℕ) = A₂ := congrArg Fin.val e2
        simp only [e2, ite_true]
        split_ifs <;> simp only [fval, trMean_root_down]; rfl
      · have e2' : (v : ℕ) ≠ A₂ := fun e => e2 (Fin.ext e)
        simp only [e2', e2, ite_false]
        rfl
  · rw [dite_eq_right h]
    simp only [psiG]
    rw [dite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]
    rfl

theorem psi_col (A₁ A₂ B₁ B₂ : Fin g) :
    fval ⟨g * g, aP, TP⟩ (psiG ⟨g * g, aP, TP⟩ (colChild g a T ι) g a ι false v args
        ξ A₁ A₂ B₁ B₂) =
      if h : A₁ < A₂ ∧ B₁ < B₂ then
        colPsi a ι v (decodeArgs (colChild g a T ι) v args)
          (fun B u => copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v false) ξ B u)
              ⟨((A₁, A₂), (B₁, B₂)), h⟩
      else 1 := by
  by_cases h : A₁ < A₂ ∧ B₁ < B₂
  · rw [dite_eq_left h]
    simp only [psiG, dite_eq_left (show (A₁ : ℕ) < A₂ ∧ (B₁ : ℕ) < B₂ ∧ (A₂ : ℕ) < g ∧
        (B₂ : ℕ) < g from
      ⟨h.1, h.2, A₂.isLt, B₂.isLt⟩), colPsi, Bool.false_eq_true, ite_false, Θof_col]
    by_cases e1 : v = B₁
    · have e1' : (v : ℕ) = B₁ := congrArg Fin.val e1
      simp only [e1, ite_true]
      split_ifs <;> simp only [fval, trMean_root_up]; rfl
    · have e1' : (v : ℕ) ≠ B₁ := fun e => e1 (Fin.ext e)
      simp only [e1', e1, ite_false]
      by_cases e2 : v = B₂
      · have e2' : (v : ℕ) = B₂ := congrArg Fin.val e2
        simp only [e2, ite_true]
        split_ifs <;> simp only [fval, trMean_root_down]; rfl
      · have e2' : (v : ℕ) ≠ B₂ := fun e => e2 (Fin.ext e)
        simp only [e2', e2, ite_false]
        rfl
  · rw [dite_eq_right h]
    simp only [psiG]
    rw [dite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]
    rfl

end Psi

/-! ### The product of the factors -/

/-- The summand of the table of a row (eq:table). -/
noncomputable def rowSummand {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (A : Fin g)
    (Θ : Fin g → Label) (ξ : Fin g → Fin (g * g) → Label) : ℤ :=
  (∏ B, T (node A B) (ξ B)) *
    (∏ B, ∏ B', if B < B' ∧ ξ B (node A B') ≠ ξ B' (node A B) then 0 else 1) *
    (∏ A', ∏ B, if A' ≠ A ∧ ξ B (node A' B) ≠ unpack (packL g) (Θ A') (vStream B) then 0 else 1) *
    ∏ r : Rect g, rowPsi a ι A Θ ξ r

/-- The summand of the table of a column. -/
noncomputable def colSummand {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (B : Fin g)
    (Θ : Fin g → Label) (ξ : Fin g → Fin (g * g) → Label) : ℤ :=
  (∏ A, T (node A B) (ξ A)) *
    (∏ A, ∏ A', if A < A' ∧ ξ A (node A' B) ≠ ξ A' (node A B) then 0 else 1) *
    (∏ B', ∏ A, if B' ≠ B ∧ ξ A (node A B') ≠ unpack (packL g) (Θ B') (vStream A) then 0 else 1) *
    ∏ r : Rect g, colPsi a ι B Θ ξ r

section Prod

variable {g : ℕ} (aP : Fin (g * g) → Fin (g * g) → ℕ) (TP : Fin (g * g) → (Fin (g * g) → Label) → ℤ)
  (rest : List ℕ) (ι : Rect g → ℤ × ℤ) (v : Fin g) (args ξ : ℕ)

theorem prod_factor_row :
    ∏ f ∈ range (nFac g), fval ⟨g * g, aP, TP⟩
        (factorG rest ⟨g * g, aP, TP⟩ (rowChild g aP TP ι) g aP ι true v args ξ f) =
      rowSummand aP TP ι v (decodeArgs (rowChild g aP TP ι) v args)
        (fun B u => copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v true) ξ B u) := by
  unfold rowSummand
  rw [show nFac g = g + g * g + g * g + g ^ 4 from rfl, prod_range_add, prod_range_add,
      prod_range_add,
    block_ent aP TP rest _ aP ι true v args ξ (fun B => node v B) (fun p => rfl),
    block_hor aP TP rest _ aP ι true v args ξ (fun B => node v B) (fun p => rfl),
    block_vert, block_psi]
  simp only [psi_row]
  rw [← prod_rect_dite]
  congr 2
  refine Fintype.prod_congr _ _ fun o => Fintype.prod_congr _ _ fun p => ?_
  rw [Θof_row]
  simp only [ne_eq, Fin.val_eq_val, ite_true]
  rfl

theorem prod_factor_col :
    ∏ f ∈ range (nFac g), fval ⟨g * g, aP, TP⟩
        (factorG rest ⟨g * g, aP, TP⟩ (colChild g aP TP ι) g aP ι false v args ξ f) =
      colSummand aP TP ι v (decodeArgs (colChild g aP TP ι) v args)
        (fun A u => copyAt ⟨g * g, aP, TP⟩ (Setup.holders g v false) ξ A u) := by
  unfold colSummand
  rw [show nFac g = g + g * g + g * g + g ^ 4 from rfl, prod_range_add, prod_range_add,
      prod_range_add,
    block_ent aP TP rest _ aP ι false v args ξ (fun A => node A v) (fun p => rfl),
    block_hor aP TP rest _ aP ι false v args ξ (fun A => node A v) (fun p => rfl),
    block_vert, block_psi]
  simp only [psi_col]
  rw [← prod_rect_dite]
  congr 2
  refine Fintype.prod_congr _ _ fun o => Fintype.prod_congr _ _ fun p => ?_
  rw [Θof_col]
  simp only [ne_eq, Fin.val_eq_val, Bool.false_eq_true, ite_false]
  rfl

end Prod

theorem argsValid_iff (C : Clique) (v : Fin C.q) (args L : ℕ) :
    Setup.ArgsValid C v args L ↔ ∀ u, u ≠ v → validLabel L (decodeArgs C v args u) := by
  constructor
  · intro h u hu; exact h v u rfl hu
  · intro h w u hw hu
    obtain rfl : w = v := Fin.ext hw
    exact h u hu

open Classical in
theorem ent_row' (rest : List ℕ) {g : ℕ} (aP : Fin (g * g) → Fin (g * g) → ℕ)
    (TP : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (v : Fin g) (args : ℕ) :
    cEntry (rowChild g aP TP ι) v args =
      if Setup.ArgsValid (rowChild g aP TP ι) v args (packL g) then
        ∑ ξ ∈ range (2 ^ copiesWidth ⟨g * g, aP, TP⟩ (Setup.holders g v true) g),
          if CopiesValid ⟨g * g, aP, TP⟩ (Setup.holders g v true) g ξ then
            ∏ f ∈ range (nFac g), fval ⟨g * g, aP, TP⟩ (factorG rest ⟨g * g, aP, TP⟩
              (rowChild g aP TP ι) g aP ι true v args ξ f)
          else 0
      else 0 := by
  unfold cEntry
  rw [dite_eq_left (show (v : ℕ) < (rowChild g aP TP ι).q from v.isLt)]
  change rowTable aP TP ι v (decodeArgs (rowChild g aP TP ι) v args) = _
  unfold rowTable
  by_cases hv : Setup.ArgsValid (rowChild g aP TP ι) v args (packL g)
  · have h' : ∀ A' : Fin g, A' ≠ v → validLabel (packL g)
      (decodeArgs (rowChild g aP TP ι) v args A') :=
      fun A' hA' => hv v A' rfl hA'
    rw [ite_eq_left h', ite_eq_left hv]
    simp only [prod_factor_row]
    exact (sum_copies ⟨g * g, aP, TP⟩ (Setup.holders g v true) g
        (fun p hp => holders_lt v.isLt true hp)
      (fun B => node v B) (fun p => rfl)
          (rowSummand aP TP ι v (decodeArgs (rowChild g aP TP ι) v args))).symm
  · have h' : ¬ ∀ A' : Fin g, A' ≠ v → validLabel (packL g)
      (decodeArgs (rowChild g aP TP ι) v args A') :=
      fun h => hv fun w u hw hu => by
        obtain rfl : w = v := Fin.ext hw
        exact h u hu
    rw [ite_eq_right h', ite_eq_right hv]

open Classical in
theorem ent_col' (rest : List ℕ) {g : ℕ} (aP : Fin (g * g) → Fin (g * g) → ℕ)
    (TP : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (hk : ∀ r, Even (ι r).1)
    (v : Fin g) (args : ℕ) :
    cEntry (colChild g aP TP ι) v args =
      if Setup.ArgsValid (colChild g aP TP ι) v args (packL g) then
        ∑ ξ ∈ range (2 ^ copiesWidth ⟨g * g, aP, TP⟩ (Setup.holders g v false) g),
          if CopiesValid ⟨g * g, aP, TP⟩ (Setup.holders g v false) g ξ then
            ∏ f ∈ range (nFac g), fval ⟨g * g, aP, TP⟩ (factorG rest ⟨g * g, aP, TP⟩
              (colChild g aP TP ι) g aP ι false v args ξ f)
          else 0
      else 0 := by
  unfold cEntry
  rw [dite_eq_left (show (v : ℕ) < (colChild g aP TP ι).q from v.isLt)]
  change (colChild g aP TP ι).T v (decodeArgs (colChild g aP TP ι) v args) = _
  refine (colChild_T aP TP ι hk v _).trans ?_
  unfold colTable
  by_cases hv : Setup.ArgsValid (colChild g aP TP ι) v args (packL g)
  · have h' : ∀ A' : Fin g, A' ≠ v → validLabel (packL g)
      (decodeArgs (colChild g aP TP ι) v args A') :=
      fun A' hA' => hv v A' rfl hA'
    rw [ite_eq_left h', ite_eq_left hv]
    simp only [prod_factor_col]
    exact (sum_copies ⟨g * g, aP, TP⟩ (Setup.holders g v false) g
        (fun p hp => holders_lt v.isLt false hp)
      (fun A => node A v) (fun p => rfl)
          (colSummand aP TP ι v (decodeArgs (colChild g aP TP ι) v args))).symm
  · have h' : ¬ ∀ A' : Fin g, A' ≠ v → validLabel (packL g)
      (decodeArgs (colChild g aP TP ι) v args A') :=
      fun h => hv fun w u hw hu => by
        obtain rfl : w = v := Fin.ext hw
        exact h u hu
    rw [ite_eq_right h', ite_eq_right hv]

open Classical in
/-- **An entry of a row clique**, through the codes of copies. -/
theorem ent_row (rest : List ℕ) (P : Clique) {g : ℕ} (hP : P.q = g * g) (ι : Rect g → ℤ × ℤ)
    (v : Fin g) (args : ℕ) :
    cEntry (rowChild g (P.recast _ hP).a (P.recast _ hP).T ι) v args =
      if Setup.ArgsValid (rowChild g (P.recast _ hP).a (P.recast _ hP).T ι) v args (packL g) then
        ∑ ξ ∈ range (2 ^ copiesWidth P (Setup.holders g v true) g),
          if CopiesValid P (Setup.holders g v true) g ξ then
            ∏ f ∈ range (nFac g), fval P (factorG rest P
              (rowChild g (P.recast _ hP).a (P.recast _ hP).T ι) g (P.recast _ hP).a ι
                  true v args ξ f)
          else 0
      else 0 := by
  obtain ⟨q, aP, TP⟩ := P
  simp only at hP
  subst hP
  exact ent_row' rest aP TP ι v args

open Classical in
/-- **An entry of a column clique**, through the codes of copies. -/
theorem ent_col (rest : List ℕ) (P : Clique) {g : ℕ} (hP : P.q = g * g) (ι : Rect g → ℤ × ℤ)
    (hk : ∀ r, Even (ι r).1) (v : Fin g) (args : ℕ) :
    cEntry (colChild g (P.recast _ hP).a (P.recast _ hP).T ι) v args =
      if Setup.ArgsValid (colChild g (P.recast _ hP).a (P.recast _ hP).T ι) v args (packL g) then
        ∑ ξ ∈ range (2 ^ copiesWidth P (Setup.holders g v false) g),
          if CopiesValid P (Setup.holders g v false) g ξ then
            ∏ f ∈ range (nFac g), fval P (factorG rest P
              (colChild g (P.recast _ hP).a (P.recast _ hP).T ι) g (P.recast _ hP).a ι
                  false v args ξ f)
          else 0
      else 0 := by
  obtain ⟨q, aP, TP⟩ := P
  simp only at hP
  subst hP
  exact ent_col' rest aP TP ι hk v args

end Cslib.Complexity.NtimeDspace.Cube
