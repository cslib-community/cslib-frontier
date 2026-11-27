/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Tableau
public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Parsing
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Complexity.CookLevin.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# Hardness of bounded-alternation quantified SAT

A native alternating verifier is padded to nonempty even-length certificate blocks. Its
Cook–Levin tableau quantifies the auxiliary variables in the final block. If that block is
universal, the tableau describes the complemented verifier and the matrix is negated.
Thus no extra alternation or assumed reduction-efficiency witness is needed.

This implements [Arora–Barak, Exercise 5 §1][AroraBarak07] and the construction suggested in
[Goldreich, Exercise 3.7][Goldreich2007DraftR2].
-/

public section

namespace Cslib.Complexity.QuantifiedSAT

open Cslib.Logic.PL _root_.Turing _root_.Turing.MultiTapeTM ComputableInPolyTime TQBF

private theorem even_verifier {α : Type} {enc : α ↪ List Bool} {A : Set α} {i : ℕ}
    (hA : A ∈ SigmaP i enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      (∀ n, 1 ≤ p.eval n) ∧ ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, a ∈ A ↔ Alternation true (List.replicate i (2 * p.eval (enc a).length))
        (fun w => V (a, w) = true) := by
  obtain ⟨p, V, hV, hAV⟩ := exists_replicate_of_mem_SigmaP hA
  let p' := p + 1
  let trim (x : α × List Bool) :=
    trimUniformBlocks (List.replicate i p) (enc x.1).length (2 * p'.eval (enc x.1).length) x.2
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := (encoding_length enc).comp (fst _ _)
  have htrim : ComputableInPolyTime trim (encPair enc encBits) encBits :=
    computableInPolyTime_trimUniformBlocks _ hn
      (unary_mul.comp ((const 2).prod ((unary_eval p').comp hn))) (snd _ _)
  refine ⟨p', fun x => V (x.1, trim x), ?_, hV.comp ((fst _ _).prod htrim), fun a => ?_⟩
  · intro n
    simp [p']
  · rw [hAV a]
    simp only [List.map_replicate]
    have ht := alternation_trimUniformBlocks (q := true) (ps := List.replicate i p)
      (n := (enc a).length) (M := 2 * p'.eval (enc a).length)
      (P := fun w => V (a, w) = true) (by
        intro p₀ hp₀
        obtain rfl := List.eq_of_mem_replicate hp₀
        simp [p']; omega)
    simpa only [List.length_replicate, List.map_replicate, trim] using ht.symm

/-- Every native `Σᵢ` verifier has a polynomial-time reduction to well-formed, nonempty-block
prenex formulas at the same positive level. This invariant also supports the dual reduction. -/
theorem exists_tableauReduction {α : Type} {enc : α ↪ List Bool} {A : Set α} {i : ℕ}
    (hi : 1 ≤ i) (hA : A ∈ SigmaP i enc) :
    ∃ f : α → PrenexQBF, ComputableInPolyTime f enc encPrenexQBF ∧
      ∀ a, (f a).WellFormed i ∧ (∀ b ∈ (f a).blocks, b ≠ []) ∧
        (a ∈ A ↔ ((f a).formula true).eval (fun _ => false) = true) := by
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
  refine ⟨f, instanceOfTableau_polyTime i r htab hw
    (unary_mul.comp ((const 2).prod hn)), fun a => ?_⟩
  have hmul : i * (2 * p.eval (enc a).length) = 2 * width a := by dsimp only [width]; ring
  have hwell := instanceOfTableau_wellFormed (tab a) (width a) _ i hi hmul r
  have hnonempty := instanceOfTableau_nonempty (tab a) (width a) (2 * p.eval (enc a).length) i hi
    (by have := hp (enc a).length; omega) r
  refine ⟨hwell, hnonempty, ?_⟩
  rw [hAV a, eval_instanceOfTableau (tab a) (width a) _ i hi true r
    (by simp only [r, Bool.not_not])]
  symm
  apply eval_certBlocks (width a) _ i hmul true
  intro σ
  let z := block σ (width a) 0 0 ++ block σ (width a) 1 0
  have hz : z.length = 2 * width a := by
    simp only [z, List.length_append, length_block]; omega
  have hrun := (htm (a, z)).runFrom_initCfg
  have hlen : (encPair enc encBits (a, z)).length = 2 * (enc a).length + 2 * width a + 1 := by
    simp only [length_encPair, encBits_apply, hz]
    omega
  rw [hlen, encPair_apply, encBits_apply] at hrun
  have hbase : (baseFormula (tab a) (width a)).eval σ = W (a, z) := by
    rw [Bool.eq_iff_iff, eval_baseFormula]
    change (∃ τ, CookLevin.certWord τ (2 * width a) = z ∧ (tab a).eval τ = true) ↔ _
    rw [← hz]
    rw [show tab a = CookLevin.tableau tm (frame (enc a)) z.length (time a) by rw [hz]]
    rw [CookLevin.exists_eval_tableau_iff]
    have heq : time a = c * (2 * (enc a).length + 2 * width a + 1 + 1) ^ d := rfl
    rw [heq, hrun.2]
    simp only [encBool_apply, List.cons.injEq, and_true]
    exact ⟨fun h => h.2, fun h => ⟨hrun.1, h⟩⟩
  cases hr : r <;> simp [hr, QBF.eval_not, hbase, W, z]

end Cslib.Complexity.QuantifiedSAT
