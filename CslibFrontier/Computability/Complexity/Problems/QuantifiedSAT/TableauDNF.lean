/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Completeness
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
# Two-block quantified DNF completeness

The existential-universal case of the tableau construction of
[Arora and Barak, Exercise 5 §1][AroraBarak07] can retain the matrix as a DNF.
Negating the conjunctive tableau for the complemented verifier places its
auxiliary variables in the existing universal block.
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

theorem length_linksCNF {k : Nat} {State : Type} [Fintype State] (w : Nat) :
    (linksCNF (k := k) (State := State) w).length = 4 * w := by
  have len (xs : List Nat) :
      (xs.flatMap fun j =>
        link (TQBF.tabVar (CookLevin.Var.cert (k := k) (State := State) j))
          (TQBF.certVar w j)).length = 2 * xs.length := by
    induction xs with
    | nil => rfl
    | cons j rest ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp [link]
      omega
  simpa only [linksCNF, List.length_range, ← Nat.mul_assoc] using len (List.range (2*w))

theorem length_tableauDNF {k : Nat} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : Nat) :
    (tableauDNF tab w).length = 4 * w + tab.length := by
  simp [tableauDNF, CNF.negate, length_linksCNF, CNF.relabel]

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

open QuantifiedSAT in
/-- The second block and all its tableau variables stay universal. -/
theorem eval_two_blocks {k : Nat} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w n : Nat) (σ : Nat → Bool) :
    QBF.eval σ (QBF.blocks true (instanceOfTableau tab w n 2 false).blocks
      (matrix (tableauDNF tab w))) = ((instanceOfTableau tab w n 2 false).formula true).eval σ := by
  rw [Bool.eq_iff_iff, PrenexQBF.formula, QBF.eval_blocks_eq_true_iff,
    QBF.eval_blocks_eq_true_iff]
  apply alternation_congr
  intro word
  rw [eval_matrix, eval_tableauDNF]
  simp [instanceOfTableau_matrix]

end Cslib.Complexity.QuantifiedSAT.WidthThree




namespace Cslib.Complexity.QuantifiedSAT.WidthThree

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.QuantifiedSAT
open _root_.Turing Turing.MultiTapeTM ComputableInPolyTime TQBF

attribute [local irreducible] ComputableInPolyTime

abbrev Instance := List (List Nat) × DNF Nat

abbrev encoding : Instance ↪ List Bool :=
  encPair (encList (encList encNat)) (encCNFOver encNat)

def prenex (p : Instance) : PrenexQBF := ⟨p.1, matrix p.2⟩

/-- Well-formed existential-universal quantified DNF in Frontier's encodings. -/
def DNF2 : Set Instance := { p | prenex p ∈ PrenexQBF.SigmaSAT 2 }

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

theorem dnf2_mem : DNF2 ∈ SigmaP 2 encoding := by
  have reduction : PolyTimeReducible encoding encPrenexQBF DNF2 (PrenexQBF.SigmaSAT 2) :=
    ⟨prenex, polytime_prenex, fun _ => Iff.rfl⟩
  exact reduction.mem_SigmaP (PrenexQBF.mem_SigmaP 2)

/-- Adapt Frontier's complemented-verifier tableau construction to retain
a DNF matrix and the original two certificate blocks. -/
theorem dnf2_hard_wellFormed {α : Type} (enc : α ↪ List Bool) (A : Set α)
    (hA : A ∈ SigmaP 2 enc) :
    ∃ f : α → Instance, ComputableInPolyTime f enc encoding ∧
      (∀ a, (prenex (f a)).WellFormed 2) ∧ (∀ a, a ∈ A ↔ f a ∈ DNF2) := by
  obtain ⟨p, V, hV, hAV⟩ := exists_replicate_of_mem_SigmaP hA
  let W (x : α × List Bool) := !(V x)
  have hW : ComputableInPolyTime W (encPair enc encBits) encBool := bool_not.comp hV
  obtain ⟨c, d, k, State, hfinite, tm, htm⟩ :=
    Turing.MultiTapeTM.Internal.NormalForm.polyTime hW
  have := Fintype.ofFinite State
  classical
  let width (a : α) := p.eval (enc a).length
  let time (a : α) := c * (2 * (enc a).length + 2 * width a + 2) ^ d
  let tab (a : α) := CookLevin.tableau tm (frame (enc a)) (2 * width a) (time a)
  let f (a : α) : PrenexQBF := instanceOfTableau (tab a) (width a) (width a) 2 false
  have hw : ComputableInPolyTime width enc encUnary :=
    (unary_eval p).comp (encoding_length enc)
  have htab : ComputableInPolyTime tab enc (encCNFOver CookLevin.encVar) := by
    have hc := CookLevin.computableInPolyTime_tableau tm
    have hframe := bitsFrame enc
    unfold tab time
    fun_prop
  have hf : ComputableInPolyTime f enc encPrenexQBF :=
    instanceOfTableau_polyTime 2 false htab hw hw
  have hdnf := polytime_tableauDNF htab hw
  have wf (a : α) : (prenex ((f a).blocks, tableauDNF (tab a) (width a))).WellFormed 2 := by
    have well := instanceOfTableau_wellFormed (tab a) (width a) (width a) 2 (by decide) rfl false
    refine ⟨well.1, ?_, ?_⟩
    · exact QBF.quantifierFree_not.mpr (QBF.quantifierFree_ofCNF _)
    · change (matrix (tableauDNF (tab a) (width a))).freeVars ⊆ (f a).blocks.flatten.toFinset
      rw [tableau_freeVars]
      simpa [instanceOfTableau_matrix] using well.2.2
  refine ⟨fun a => ((f a).blocks, tableauDNF (tab a) (width a)),
    (encPrenexQBF_blocks_polyTime hf).prod hdnf, wf, fun a => ?_⟩
  change a ∈ A ↔
    (prenex ((f a).blocks, tableauDNF (tab a) (width a))).WellFormed 2 ∧ _
  rw [and_iff_right (wf a)]
  change a ∈ A ↔
    (QBF.blocks true (f a).blocks (matrix (tableauDNF (tab a) (width a)))).eval
      (fun _ => false) = true
  rw [eval_two_blocks, hAV a,
    eval_instanceOfTableau (tab a) (width a) (width a) 2 (by decide) true false (by decide)]
  refine (eval_certBlocks (width a) _ 2 rfl true _ (fun σ => ?_)).symm
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
  simp [QBF.eval_not, hbase, W, z]

theorem dnf2_hard : SigmaPHard 2 encoding DNF2 := by
  intro α enc A hA
  obtain ⟨f, hf, _, hcorrect⟩ := dnf2_hard_wellFormed enc A hA
  exact ⟨f, hf, hcorrect⟩

theorem dnf2_complete : SigmaPComplete 2 encoding DNF2 := ⟨dnf2_mem, dnf2_hard⟩

end Cslib.Complexity.QuantifiedSAT.WidthThree
