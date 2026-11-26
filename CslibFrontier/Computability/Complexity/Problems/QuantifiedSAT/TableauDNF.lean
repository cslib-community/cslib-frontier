/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Completeness
public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Hardness
public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Membership
public import CslibFrontier.Computability.Complexity.Classes.PH.Projection
public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Tableau
public import CslibFrontier.Computability.Complexity.CookLevin.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import CslibFrontier.Logics.Propositional.DNF
public import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Quantified tableau matrix normal forms

The tableau construction of [Arora and Barak, Exercise 5 §1][AroraBarak07]
retains a conjunctive or disjunctive matrix depending on the final block.
The tableau accepts the complemented verifier when the final block is universal.
-/

@[expose] public section

namespace Cslib.Complexity.QuantifiedSAT.WidthThree

open Cslib.Logic.PL Cslib.Complexity
open _root_.Turing.MultiTapeTM ComputableInPolyTime

/-- Two width-two clauses express equality of the two certificate wires. -/
def link (a b : Nat) : CNF Nat :=
  [[(a, false), (b, true)], [(a, true), (b, false)]]

theorem eval_link (σ : Nat → Bool) (a b : Nat) :
    (link a b).eval σ = (QBF.iff (.var a) (.var b)).eval σ := by
  cases ha : σ a <;> cases hb : σ b <;>
    simp [link, CNF.eval, Clause.eval, Literal.eval, QBF.iff, QBF.eval, ha, hb]

noncomputable def linksCNF {k : Nat} {State : Type} [Fintype State] (w : Nat) : CNF Nat :=
  (List.range (2 * w)).flatMap fun j =>
    link (TQBF.tabVar (CookLevin.Var.cert (k := k) (State := State) j)) (TQBF.certVar w j)

theorem eval_link_list (σ : Nat → Bool) (pairs : List (Nat × Nat)) :
    CNF.eval σ (pairs.flatMap fun p => link p.1 p.2) =
      (QBF.conj (pairs.map fun p => QBF.iff (.var p.1) (.var p.2))).eval σ := by
  induction pairs with
  | nil => rfl
  | cons p rest ih =>
    rw [List.flatMap_cons, CNF.eval_append, eval_link, ih]
    rfl

theorem eval_links {k : Nat} {State : Type} [Fintype State] (w : Nat) (σ : Nat → Bool) :
    (linksCNF (k := k) (State := State) w).eval σ = (TQBF.certLinks k State w).eval σ := by
  simpa [linksCNF, TQBF.certLinks, List.flatMap_map, Function.comp_def] using
    eval_link_list σ ((List.range (2*w)).map fun j =>
      (TQBF.tabVar (CookLevin.Var.cert (k := k) (State := State) j), TQBF.certVar w j))

noncomputable def tableauDNF {k : Nat} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : Nat) : DNF Nat :=
  ((linksCNF (k := k) (State := State) w) ++ tab.relabel TQBF.tabVar : CNF Nat).negate

theorem eval_tableauDNF {k : Nat} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : Nat) (σ : Nat → Bool) :
    (tableauDNF tab w).eval σ = ((TQBF.baseMatrix tab w).not).eval σ := by
  simp [tableauDNF, TQBF.baseMatrix, eval_links]

theorem polytime_negateCNF {V : Type} (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.negate (V := V)) (encCNFOver enc) (encCNFOver enc) := by
  change ComputableInPolyTime (List.map (List.map Std.Sat.Literal.negate))
    (encList (encList (encPair enc encBool))) (encList (encList (encPair enc encBool)))
  exact map (map (Literal.computableInPolyTime_negate enc))

attribute [local irreducible] ComputableInPolyTime

theorem polytime_tableauDNF {α : Type} {enc : α ↪ List Bool} {k : Nat}
    {State : Type} [Fintype State] {tab : α → CNF (CookLevin.Var k State)} {w : α → Nat}
    (htab : ComputableInPolyTime tab enc (encCNFOver CookLevin.encVar))
    (hw : ComputableInPolyTime w enc encUnary) :
    ComputableInPolyTime (fun a => tableauDNF (tab a) (w a)) enc (encCNFOver encNat) := by
  have hlink : ComputableInPolyTime (fun p : Nat × Nat => link p.1 p.2)
      (encPair encNat encNat) (encCNFOver encNat) := by
    unfold link
    fun_prop
  have hrelabel := (CNF.computableInPolyTime_relabel
    (TQBF.computableInPolyTime_tabVar (k := k) (State := State))).comp htab
  have hj := snd enc encUnary
  have hleft := (TQBF.computableInPolyTime_tabVar (k := k) (State := State)).comp
    ((CookLevin.computableInPolyTime_cert (k := k) (State := State)).comp hj)
  have hright := TQBF.computableInPolyTime_certVar (hw.comp (fst enc encUnary)) hj
  have hl : ComputableInPolyTime (fun a => linksCNF (k := k) (State := State) (w a))
      enc (encCNFOver encNat) :=
    flatMapWithInput (unary_range' (unary_mul' (const 2) hw)) (hlink.comp (hleft.prod hright))
  apply (polytime_negateCNF encNat).comp
  show ComputableInPolyTime (fun a => linksCNF (k := k) (State := State) (w a) ++
    (tab a).relabel TQBF.tabVar) enc (encCNFOver encNat)
  fun_prop

/-- Interpret the DNF as the negation of its dual CNF. -/
def matrix (dnf : DNF Nat) : QBF Nat := (QBF.ofCNF dnf.negate).not

theorem eval_matrix (dnf : DNF Nat) (σ : Nat → Bool) :
    (matrix dnf).eval σ = dnf.eval σ := by simp [matrix]

theorem negate_twice (cnf : CNF Nat) : cnf.negate.negate = cnf := by
  simp [CNF.negate, DNF.negate, Clause.negate, Term.negate, List.map_map, Function.comp_def]

theorem link_freeVars (σ : Nat) (pairs : List (Nat × Nat)) :
    σ ∈ (QBF.ofCNF (pairs.flatMap fun p => link p.1 p.2)).freeVars ↔
      σ ∈ (QBF.conj (pairs.map fun p => QBF.iff (.var p.1) (.var p.2))).freeVars := by
  induction pairs with
  | nil => simp [QBF.ofCNF, QBF.conj]
  | cons p pairs ih =>
    rw [List.flatMap_cons, QBF.mem_freeVars_ofCNF]
    have varsAppend (a b : CNF Nat) : (a ++ b).vars = a.vars ++ b.vars := by
      simp [CNF.vars]
    rw [varsAppend, List.mem_append, ← QBF.mem_freeVars_ofCNF
      (φ := pairs.flatMap fun p => link p.1 p.2), ih]
    change (_ ∨ _) ↔ σ ∈
      ((QBF.iff (.var p.1) (.var p.2)).and
        (QBF.conj (pairs.map fun a => QBF.iff (.var a.1) (.var a.2)))).freeVars
    simp [CNF.vars, link, or_assoc, or_left_comm, or_comm]

theorem tableau_freeVars {k : Nat} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : Nat) :
    (matrix (tableauDNF tab w)).freeVars = (TQBF.baseMatrix tab w).freeVars := by
  ext v
  have equalLinks := link_freeVars v ((List.range (2*w)).map fun j =>
    (TQBF.tabVar (CookLevin.Var.cert (k := k) (State := State) j), TQBF.certVar w j))
  have eq : v ∈ (linksCNF (k := k) (State := State) w).vars ↔
      v ∈ (TQBF.certLinks k State w).freeVars := by
    simpa [QBF.mem_freeVars_ofCNF, linksCNF, TQBF.certLinks, List.flatMap_map,
      Function.comp_def] using equalLinks
  simp [matrix, tableauDNF, negate_twice, TQBF.baseMatrix, QBF.mem_freeVars_ofCNF,
    show ∀ (a b : CNF Nat), (a ++ b).vars = a.vars ++ b.vars by
      intro a b
      simp [CNF.vars], eq]

end Cslib.Complexity.QuantifiedSAT.WidthThree




namespace Cslib.Complexity.QuantifiedSAT.WidthThree

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.QuantifiedSAT
open _root_.Turing Turing.MultiTapeTM ComputableInPolyTime TQBF

attribute [local irreducible] ComputableInPolyTime

abbrev Instance := List (List Nat) × DNF Nat

abbrev encoding : Instance ↪ List Bool :=
  encPair (encList (encList encNat)) (encCNFOver encNat)

def prenex (p : Instance) : PrenexQBF := ⟨p.1, matrix p.2⟩

theorem polytime_prenex : ComputableInPolyTime prenex encoding encPrenexQBF := by
  have hn : ComputableInPolyTime (DNF.negate (V := Nat))
      (encCNFOver encNat) (encCNFOver encNat) := by
    change ComputableInPolyTime (List.map (List.map Std.Sat.Literal.negate))
      (encCNFOver encNat) (encCNFOver encNat)
    exact map (map (Literal.computableInPolyTime_negate encNat))
  unfold prenex matrix
  have h := hn.comp (snd (encList (encList encNat)) (encCNFOver encNat))
  exact encPrenexQBF_mk_polyTime (fst _ _)
    (TQBF.computableInPolyTime_not (TQBF.computableInPolyTime_ofCNF h))

/-- Store either matrix polarity using the same list of signed terms. When the last block
is existential, its matrix is the dual CNF. -/
def prenexAt (r : Bool) (p : Instance) : PrenexQBF :=
  ⟨p.1, if r then QBF.ofCNF p.2.negate else matrix p.2⟩

theorem polytime_prenexAt (r : Bool) : ComputableInPolyTime (prenexAt r) encoding encPrenexQBF := by
  cases r
  · exact polytime_prenex
  · have d : ComputableInPolyTime (DNF.negate (V := Nat))
        (encCNFOver encNat) (encCNFOver encNat) :=
      map (map (Literal.computableInPolyTime_negate encNat))
    exact encPrenexQBF_mk_polyTime (fst _ _)
      (TQBF.computableInPolyTime_ofCNF
        (d.comp (snd (encList (encList encNat)) (encCNFOver encNat))))

theorem prenexAt_freeVars (r : Bool) (p : Instance) :
    (prenexAt r p).matrix.freeVars = (matrix p.2).freeVars := by
  cases r <;> simp [prenexAt, matrix]

theorem prenexAt_wf_iff (r : Bool) (p : Instance) (i : Nat) :
    (prenexAt r p).WellFormed i ↔ (prenex p).WellFormed i := by
  have h (p : Instance) : (prenexAt r p).matrix.QuantifierFree := by
    cases r <;> simp [prenexAt, matrix, QBF.quantifierFree_not, QBF.quantifierFree_ofCNF]
  simp only [PrenexQBF.WellFormed, prenexAt_freeVars, h, true_and]
  simp [prenex, prenexAt, matrix, QBF.quantifierFree_not, QBF.quantifierFree_ofCNF]

private theorem eval_tableauAt {k : Nat} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w n i : Nat) (r : Bool) (σ : Nat → Bool) :
    ((prenexAt r ((instanceOfTableau tab w n i r).blocks, tableauDNF tab w)).formula true).eval σ =
      ((instanceOfTableau tab w n i r).formula true).eval σ := by
  rw [Bool.eq_iff_iff, PrenexQBF.formula, PrenexQBF.formula, QBF.eval_blocks_eq_true_iff,
    QBF.eval_blocks_eq_true_iff]
  apply alternation_congr
  intro word
  cases r
  · simp [prenexAt, instanceOfTableau_matrix, eval_matrix, eval_tableauDNF]
  · simp [prenexAt, instanceOfTableau_matrix, QBF.eval_ofCNF, DNF.eval_negate, eval_tableauDNF]

/-- A shaped Cook–Levin reduction at any positive level. The last block's polarity
determines whether the output is interpreted as CNF or DNF. -/
theorem exists_normalFormReduction {α : Type} {enc : α ↪ List Bool} {A : Set α} {i : Nat}
    (hi : 1 ≤ i) (hA : A ∈ SigmaP i enc) :
    let r := !(Bool.not^[i] true)
    ∃ f : α → Instance, ComputableInPolyTime f enc encoding ∧
      (∀ a, (prenex (f a)).WellFormed i) ∧
      ∀ a, a ∈ A ↔ ((prenexAt r (f a)).formula true).eval (fun _ => false) = true := by
  obtain ⟨p, V, hp, hV, hAV⟩ := even_verifier hA
  let r := !(Bool.not^[i] true)
  let W (x : α × List Bool) := if r then V x else !(V x)
  have hW : ComputableInPolyTime W (encPair enc encBits) encBool := by
    unfold W
    cases r <;> fun_prop
  obtain ⟨c, d, k, State, hfinite, tm, htm⟩ :=
    Turing.MultiTapeTM.Internal.NormalForm.polyTime hW
  have := Fintype.ofFinite State
  classical
  let width (a : α) := i * p.eval (enc a).length
  let time (a : α) := c * (2 * (enc a).length + 2 * width a + 2) ^ d
  let tab (a : α) := CookLevin.tableau tm (frame (enc a)) (2 * width a) (time a)
  let f (a : α) := instanceOfTableau (tab a) (width a) (2 * p.eval (enc a).length) i r
  have hn : ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary :=
    (unary_eval p).comp (encoding_length enc)
  have hw : ComputableInPolyTime width enc encUnary := unary_mul.comp ((const i).prod hn)
  have htab : ComputableInPolyTime tab enc
      (encList (encList (encPair CookLevin.encVar encBool))) := by
    have hc := CookLevin.computableInPolyTime_tableau tm
    have hframe := bitsFrame enc
    unfold tab time
    fun_prop
  have hf := instanceOfTableau_polyTime i r htab hw (unary_mul.comp ((const 2).prod hn))
  refine ⟨fun a => ((f a).blocks, tableauDNF (tab a) (width a)),
    (encPrenexQBF_blocks_polyTime hf).prod (polytime_tableauDNF htab hw), ?_, ?_⟩
  · intro a
    have hmul : i * (2 * p.eval (enc a).length) = 2 * width a := by dsimp only [width]; ring
    have well := instanceOfTableau_wellFormed (tab a) (width a) _ i hi hmul r
    refine ⟨well.1, QBF.quantifierFree_not.mpr (QBF.quantifierFree_ofCNF _), ?_⟩
    change (matrix (tableauDNF (tab a) (width a))).freeVars ⊆ (f a).blocks.flatten.toFinset
    rw [tableau_freeVars]
    have eq : (f a).matrix.freeVars = (baseMatrix (tab a) (width a)).freeVars := by
      dsimp only [f]
      rw [instanceOfTableau_matrix]
      cases r <;> simp
    rw [← eq]
    exact well.2.2
  intro a
  have hmul : i * (2 * p.eval (enc a).length) = 2 * width a := by dsimp only [width]; ring
  rw [show ((prenexAt r ((f a).blocks, tableauDNF (tab a) (width a))).formula true).eval
      (fun _ => false) = ((f a).formula true).eval (fun _ => false) from
    eval_tableauAt (tab a) (width a) _ i r _]
  rw [hAV a, eval_instanceOfTableau (tab a) (width a) _ i hi true r
    (by simp only [r, Bool.not_not])]
  refine (eval_certBlocks (width a) _ i hmul true _ fun σ => ?_).symm
  let z := block σ (width a) 0 0 ++ block σ (width a) 1 0
  have hz : z.length = 2 * width a := by simp [z, length_block, two_mul]
  have hrun := (htm (a, z)).runFrom_initCfg
  have hlen : (encPair enc encBits (a, z)).length = 2 * (enc a).length + 2 * width a + 1 := by
    simp only [length_encPair, encBits_apply, hz]
    omega
  rw [hlen, encPair_apply, encBits_apply] at hrun
  have hbase : (baseFormula (tab a) (width a)).eval σ = W (a, z) := by
    rw [Bool.eq_iff_iff, eval_baseFormula]
    change (∃ τ, CookLevin.certWord τ (2 * width a) = z ∧ (tab a).eval τ = true) ↔ _
    rw [← hz, show tab a = CookLevin.tableau tm (frame (enc a)) z.length (time a) by rw [hz],
      CookLevin.exists_eval_tableau_iff,
      show time a = c * (2 * (enc a).length + 2 * width a + 1 + 1) ^ d from rfl, hrun.2]
    simpa only [encBool_apply, List.cons.injEq, and_true] using and_iff_right hrun.1
  cases hr : r <;> simp [hr, QBF.eval_not, hbase, W, z]

end Cslib.Complexity.QuantifiedSAT.WidthThree
