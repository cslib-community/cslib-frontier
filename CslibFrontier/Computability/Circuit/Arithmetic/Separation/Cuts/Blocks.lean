/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Run
public import CslibFrontier.Foundations.Data.List.StairRefinement
public import CslibFrontier.Foundations.Data.List.WordsLe
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunWord
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.ReduceOption

/-!
# Blocks of a run

Lemma I.2 of [AnthropicVPVNP2026] (module `Nc.Cut.Blocks`) cuts a run of `K * T` steps of an
automaton on tapes into `K` time *blocks* of `T` steps. The *weight* of a block from a state `q`
to a state `q'` that emits the words `v` on the channels (`Cut.blockWeight`) is the sum of the
weights of the runs of `T` steps from `q` to `q'` that emit `v`. The value of the automaton is
then a sum over the states between the blocks and over what the blocks emit, of the product of
the weights of the blocks (`Cut.runVal_blocks`): the words that the blocks emit on a channel are
concatenated, the two sides of every tape have to agree, and the input channels have to carry
the input.

## Main definitions

* `Cut.blockWeight`: the weight of the blocks of `T` steps between two states that emit given
  words.

## Main results

* `Tape.emit_flatten`: what a concatenation of runs emits.
* `Cut.sum_length_le_of_blockWeight_ne_zero`, `Cut.blockWeight_ne_zero`: a block of `T` steps
  emits at most `T` letters.
* `Cut.runVal_blocks`: the value of a run of `K * T` steps as a sum over states and over what
  the blocks emit.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma I.2 (Section I.3), which Proposition J.2 of Appendix J applies; module `Nc.Cut.Blocks`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation

open Finset List.StairRefinement Cslib.Automata.Weighted

variable {F Γ S J Q : Type*} [DecidableEq S] [DecidableEq J]

namespace Tape

/-- A concatenation of runs emits the concatenation of what the runs emit. -/
theorem emit_flatten {K : ℕ} (o : Fin K → List (Letter S J Γ)) (z : Ch S J) :
    emit (List.ofFn o).flatten z = cat fun k => emit (o k) z := by
  induction K with
  | zero => simp [emit, cat]
  | succ K ih => rw [List.ofFn_succ, List.flatten_cons, emit_appendR, ih, cat_succ]

end Tape

namespace Cut

open Tape

variable [Fintype Γ] [DecidableEq Γ] [Fintype S] [Fintype J] [Fintype Q] [DecidableEq Q]

section Semiring

variable [Semiring F] {mu : Letter S J Γ → Matrix Q Q F} {T : ℕ} {q q' : Q}
  {v : Ch S J → List Γ}

/-- The weight of the blocks of `T` steps from the state `q` to the state `q'` that emit the
words `v` on the channels: the sum of the weights of the runs of `T` steps that emit `v`. -/
@[expose] def blockWeight (mu : Letter S J Γ → Matrix Q Q F) (T : ℕ) (q q' : Q)
    (v : Ch S J → List Γ) : F :=
  ∑ o : Fin T → Letter S J Γ,
    if emit (List.ofFn o) = v then ((List.ofFn o).map mu).prod q q' else 0

/-- A block of `T` steps emits at most `T` letters on all channels together. -/
theorem sum_length_le_of_blockWeight_ne_zero (h : blockWeight mu T q q' v ≠ 0) :
    ∑ z, (v z).length ≤ T := by
  obtain ⟨o, -, ho⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨rfl, -⟩ := ite_ne_right_iff.1 ho
  simpa [emit] using (sum_length_proj _).trans_le (List.reduceOption_length_le (List.ofFn o))

/-- A block of `T` steps emits at most `T` letters on a channel. -/
theorem blockWeight_ne_zero (h : blockWeight mu T q q' v ≠ 0) (z : Ch S J) :
    v z ∈ List.wordsLe Γ T :=
  List.mem_wordsLe.2 <| (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ z)).trans
    (sum_length_le_of_blockWeight_ne_zero h)

end Semiring

/-- Families of `K` blocks of `T` steps, grouped by what the blocks emit. -/
private theorem sum_prod_blockWeight [CommSemiring F] (mu : Letter S J Γ → Matrix Q Q F)
    {K : ℕ} (T : ℕ) (q : Fin (K + 1) → Q) (c : (Fin K → Ch S J → List Γ) → Prop)
    [DecidablePred c] :
    (∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S J =>
        List.wordsLe Γ T,
      if c v then ∏ k, blockWeight mu T (q k.castSucc) (q k.succ) (v k) else 0) =
    ∑ o : Fin K → Fin T → Letter S J Γ, if c (fun k => emit (List.ofFn (o k))) then
      ∏ k, ((List.ofFn (o k)).map mu).prod (q k.castSucc) (q k.succ) else 0 := by
  simp only [blockWeight, prod_univ_sum, Fintype.piFinset_univ, prod_ite_zero, ite_sum_zero]
  rw [sum_comm]
  refine sum_congr rfl fun o _ => ?_
  rw [sum_eq_single_of_mem (fun k => emit (List.ofFn (o k)))
    (by simpa [Fintype.mem_piFinset] using fun k z => emit_length_le (List.ofFn (o k)) z)
    fun v _ hv => by
      simp [show ¬∀ k, emit (List.ofFn (o k)) = v k from fun h => hv (funext h).symm]]
  simp

/-- **Blocks.** The value of an automaton on a run of `K * T` steps is the sum, over the states
`q 0 = i, q 1, …, q K = e` between `K` blocks of `T` steps and over the words `v k z` of at most
`T` letters that the block `k` emits on the channel `z`, of the product of the weights of the
blocks; the sum is restricted to the `v` for which the two sides of every tape carry the same
concatenation, and every input channel carries the input. -/
theorem runVal_blocks [CommRing F] (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (K T : ℕ)
    (u : J → List Γ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S J =>
          List.wordsLe Γ T,
        if (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
          ∀ j, cat (fun k => v k (.inp j)) = u j then
          ∏ k, blockWeight mu T (q k.castSucc) (q k.succ) (v k) else 0
      else 0 := by
  -- a run of `K * T` steps is a family of `K` blocks of `T` steps
  let E : (Fin K → Fin T → Letter S J Γ) ≃ (Fin (K * T) → Letter S J Γ) :=
    (Equiv.curry _ _ _).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl _))
  have hE (o : Fin K → Fin T → Letter S J Γ) :
      List.ofFn (E o) = (List.ofFn fun k => List.ofFn (o k)).flatten := by
    rw [List.ofFn_eq_map (f := fun k => List.ofFn (o k)), ← List.flatMap_def,
      List.flatMap_ofFn_prod]
    rfl
  rw [runVal, ← E.sum_comp]
  simp only [hE, Matched, emit_flatten, List.map_flatten, List.prod_flatten, List.map_ofFn,
    Function.comp_def, Matrix.list_prod_ofFn_apply, sum_prod_blockWeight, ite_sum_zero]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by split_ifs <;> rfl

end Cut

end Cslib.Circuits.Arithmetic.Separation
