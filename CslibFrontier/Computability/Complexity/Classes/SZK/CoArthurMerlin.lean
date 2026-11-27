/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SZK
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound
import CslibFrontier.Computability.Complexity.Problems.StatisticalDifference.Overlap
import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Probability.BitString.AffineHash.Overlap

/-!
# Certifying overlap between two circuit output distributions

For each possible output, two independent affine hashes test whether both circuits have
preimages mapping to zero. The level selector gives weight `2 ^ j` to hashes with `j` output
bits. Four preimages certify the two tests. After polarization, the number of certified
strings separates near from far samplers by a factor of two. The Goldwasser–Sipser set
lower bound protocol gives an AM protocol for the complement.

## Main results

* `Cslib.Complexity.SZK_subset_coAM` places total languages reducing to Statistical
  Difference in coAM. The interactive characterization is tracked in
  [#3205](https://github.com/cslib-community/cslib-frontier/issues/3205).

## References

* [A. Sahai and S. Vadhan, *A complete problem for statistical zero knowledge*,
  Corollary 4.5][SahaiVadhan2003]
* [S. Goldwasser and M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
-/

namespace Cslib.Complexity.SDInstance

open Cslib Cslib.BitString.LinearHash Circuits Circuits.Boolean Finset Turing.MultiTapeTM

private abbrev hashWidth (n : ℕ) := n * n + n

private def groundWidth (x : SDInstance) :=
  x.outputs + ((x.inputs + 1) + ((hashWidth x.inputs + hashWidth x.inputs) + 6))

private def certWidth (n : ℕ) := (n + n) + (n + n)

private def preimageCheck (code : CircuitCode) (j n : ℕ) (y seed u : List Bool) : Bool :=
  decide (evalCircuitOutputs code u = y) && hashZero j n (seed.take (j * n + j)) u

private def pairCheck (x : SDInstance) (j : ℕ) (y seed w : List Bool) : Bool :=
  preimageCheck x.left.code j x.inputs y seed (w.take x.inputs) &&
    preimageCheck x.right.code j x.inputs y seed (w.drop x.inputs)

private def hasWitness (x : SDInstance) (w : List Bool) : Bool :=
  let n := x.inputs
  let M := hashWidth n
  let g := w.take x.groundWidth
  let cert := w.drop x.groundWidth
  let y := g.take x.outputs
  let tagSeeds := g.drop x.outputs
  let tag := tagSeeds.take (n + 1)
  let seeds := (tagSeeds.drop (n + 1)).take (M + M)
  let j := n - tag.idxOf true
  tag.any id && (pairCheck x j y (seeds.take M) (cert.take (n + n)) &&
    pairCheck x j y (seeds.drop M) (cert.drop (n + n)))

private theorem computableInPolyTime_preimageCheck {α : Type} {enc : α ↪ List Bool}
    {code : α → CircuitCode} {j n : α → ℕ} {y seed u : α → List Bool}
    (hcode : ComputableInPolyTime code enc encCode) (hj : ComputableInPolyTime j enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (hy : ComputableInPolyTime y enc encBits)
    (hs : ComputableInPolyTime seed enc encBits) (hu : ComputableInPolyTime u enc encBits) :
    ComputableInPolyTime (fun a => preimageCheck (code a) (j a) (n a) (y a) (seed a) (u a))
      enc encBool :=
  ComputableInPolyTime.bool_and'
    ((computableInPolyTime_evalCircuitOutputs hcode hu).decide_eq' hy)
    (computableInPolyTime_hashZero hj hn (ComputableInPolyTime.bitsTakeWithInput hs
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hj hn) hj)) hu)

private theorem computableInPolyTime_pairCheck {α : Type} {enc : α ↪ List Bool}
    {x : α → SDInstance} {j : α → ℕ} {y seed w : α → List Bool}
    (hx : ComputableInPolyTime x enc encSDInstance) (hj : ComputableInPolyTime j enc encUnary)
    (hy : ComputableInPolyTime y enc encBits) (hs : ComputableInPolyTime seed enc encBits)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun a => pairCheck (x a) (j a) (y a) (seed a) (w a)) enc encBool :=
  let h := computableInPolyTime_parts hx
  let hn := h.fst'.fst'
  ComputableInPolyTime.bool_and' (computableInPolyTime_preimageCheck h.snd'.fst' hj hn hy hs
    (ComputableInPolyTime.bitsTakeWithInput hw hn))
    (computableInPolyTime_preimageCheck h.snd'.snd' hj hn hy hs
      (ComputableInPolyTime.bitsDropWithInput hw hn))

private theorem computableInPolyTime_hasWitness {α : Type} {enc : α ↪ List Bool}
    {x : α → SDInstance} {w : α → List Bool} (hx : ComputableInPolyTime x enc encSDInstance)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun a => hasWitness (x a) (w a)) enc encBool := by
  have h := computableInPolyTime_parts hx
  have hn := h.fst'.fst'
  have hm := h.fst'.snd'
  have hM := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hn hn) hn
  have hseeds := ComputableInPolyTime.unary_add' hM hM
  have htag := ComputableInPolyTime.unary_add' hn (ComputableInPolyTime.const 1)
  have hground := ComputableInPolyTime.unary_add' hm (ComputableInPolyTime.unary_add' htag
    (ComputableInPolyTime.unary_add' hseeds (ComputableInPolyTime.const 6)))
  have hg := ComputableInPolyTime.bitsTakeWithInput hw hground
  have hc := ComputableInPolyTime.bitsDropWithInput hw hground
  have hy := ComputableInPolyTime.bitsTakeWithInput hg hm
  have hts := ComputableInPolyTime.bitsDropWithInput hg hm
  have ht := ComputableInPolyTime.bitsTakeWithInput hts htag
  have hs := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput hts htag) hseeds
  have hj := ComputableInPolyTime.unary_sub' hn (ComputableInPolyTime.idxOfWithInput
    (encA := encBool) (ComputableInPolyTime.bitsToList.comp ht) (ComputableInPolyTime.const true))
  have hpair := ComputableInPolyTime.unary_add' hn hn
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b)
    ht (ComputableInPolyTime.snd _ encBool)) (ComputableInPolyTime.bool_and'
    (computableInPolyTime_pairCheck hx hj hy (ComputableInPolyTime.bitsTakeWithInput hs hM)
      (ComputableInPolyTime.bitsTakeWithInput hc hpair))
    (computableInPolyTime_pairCheck hx hj hy (ComputableInPolyTime.bitsDropWithInput hs hM)
      (ComputableInPolyTime.bitsDropWithInput hc hpair)))

private theorem exists_append (n m : ℕ) (P : List Bool → Prop) :
    (∃ z : BitString (n + m), P (List.ofFn z)) ↔
      ∃ u : BitString n, ∃ v : BitString m, P (List.ofFn u ++ List.ofFn v) := by
  rw [(Fin.appendEquiv n m).surjective.exists]
  change (∃ p : BitString n × BitString m, P (List.ofFn (Fin.append p.1 p.2))) ↔ _
  simp only [Prod.exists, List.ofFn_fin_append]

private def hits (x : SDInstance) (y : BitString x.outputs) (j : ℕ) :=
  commonHashHits j {r | x.left.eval interpretation r = y}
    {r | x.right.eval interpretation r = y}

private theorem exists_pairCheck (x : SDInstance) (y : BitString x.outputs) (j : ℕ)
    (r : BitString (hashWidth x.inputs)) :
    (∃ w : BitString (x.inputs + x.inputs), pairCheck x j (List.ofFn y) (List.ofFn r)
      (List.ofFn w) = true) ↔ r ∈ x.hits y j := by
  rw [exists_append _ _ (fun w => pairCheck x j (List.ofFn y) (List.ofFn r) w = true)]
  simp only [pairCheck, preimageCheck, List.take_left' List.length_ofFn,
    List.drop_left' List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq,
    evalCircuitOutputs_code, List.ofFn_inj, hits, commonHashHits, mem_filter, mem_univ, true_and]
  aesop

private theorem exists_hasWitness (x : SDInstance) (y : BitString x.outputs)
    (tag : BitString (x.inputs + 1)) (r s : BitString (hashWidth x.inputs)) (pad : BitString 6) :
    (∃ w : BitString (certWidth x.inputs), hasWitness x
      ((List.ofFn y ++ (List.ofFn tag ++ ((List.ofFn r ++ List.ofFn s) ++ List.ofFn pad))) ++
        List.ofFn w) = true) ↔
      (List.ofFn tag).any id = true ∧
        r ∈ x.hits y (x.inputs - (List.ofFn tag).idxOf true) ∧
        s ∈ x.hits y (x.inputs - (List.ofFn tag).idxOf true) := by
  unfold certWidth
  rw [exists_append _ _ (fun w => hasWitness x ((List.ofFn y ++ (List.ofFn tag ++
    ((List.ofFn r ++ List.ofFn s) ++ List.ofFn pad))) ++ w) = true)]
  have hground : (List.ofFn y ++ (List.ofFn tag ++ ((List.ofFn r ++ List.ofFn s) ++
      List.ofFn pad))).length = x.groundWidth := by simp [groundWidth]; omega
  have hseeds : (List.ofFn r ++ List.ofFn s).length =
      hashWidth x.inputs + hashWidth x.inputs := by simp
  simp only [hasWitness, List.take_left' hground, List.drop_left' hground,
    List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    List.take_left' hseeds, Bool.and_eq_true, ← exists_pairCheck]
  aesop

private theorem card_witnessSet (x : SDInstance) :
    #{g : BitString x.groundWidth | ∃ w : BitString (certWidth x.inputs),
      hasWitness x (List.ofFn g ++ List.ofFn w) = true} =
      ∑ y : BitString x.outputs, ∑ tag : BitString (x.inputs + 1),
        ∑ r : BitString (hashWidth x.inputs), ∑ s : BitString (hashWidth x.inputs),
          ∑ _ : BitString 6, if (List.ofFn tag).any id = true ∧
            r ∈ x.hits y (x.inputs - (List.ofFn tag).idxOf true) ∧
            s ∈ x.hits y (x.inputs - (List.ofFn tag).idxOf true) then 1 else 0 := by
  classical
  let F := fun g : List Bool => if ∃ w : BitString (certWidth x.inputs),
    hasWitness x (g ++ List.ofFn w) = true then 1 else 0
  rw [card_filter]
  change (∑ g : BitString x.groundWidth, F (List.ofFn g)) = _
  unfold groundWidth
  rw [BitString.sum_ofFn_append x.outputs _ F]
  apply sum_congr rfl
  intro y _
  rw [BitString.sum_ofFn_append _ _ (fun v => F (List.ofFn y ++ v))]
  apply sum_congr rfl
  intro tag _
  let G := fun v => F (List.ofFn y ++ (List.ofFn tag ++ v))
  rw [BitString.sum_ofFn_append _ 6 G, BitString.sum_ofFn_append _ _ (fun seeds =>
    ∑ pad : BitString 6, G (seeds ++ List.ofFn pad))]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro pad _
  simp only [G, F, exists_hasWitness]

private theorem sum_pair_tests (m n H : ℕ) (P : BitString m → ℕ → BitString H → Prop)
    [∀ y j r, Decidable (P y j r)] :
    (∑ y : BitString m, ∑ t : BitString (n + 1), ∑ r : BitString H, ∑ s : BitString H,
      ∑ _ : BitString 6, if (List.ofFn t).any id ∧ P y (n - (List.ofFn t).idxOf true) r ∧
        P y (n - (List.ofFn t).idxOf true) s then 1 else 0) =
      64 * ∑ y : BitString m, ∑ j ∈ range (n + 1), 2 ^ j * #{r | P y j r} ^ 2 := by
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  rw [← BitString.sum_ofFn_first_true n (fun j => #{r | P y j r} ^ 2), mul_sum]
  apply sum_congr rfl
  intro t _
  by_cases ht : (List.ofFn t).any id
  · simp only [ht, true_and, ite_true, sum_const, card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, ← mul_sum]
    rw [pow_two, card_filter, sum_mul]
    norm_num only [Nat.cast_id, Nat.reducePow]
    apply congrArg (fun z : ℕ => 64 * z)
    apply sum_congr rfl
    intro r _
    by_cases hr : P y (n - (List.ofFn t).idxOf true) r
    · simp only [hr, true_and, ite_true, one_mul]
    · simp only [hr, false_and, ite_false, zero_mul, sum_const_zero]
  · simp only [ht, Bool.false_eq_true, false_and, ite_false, sum_const_zero, mul_zero]

private theorem card_eq_mul_affineOverlapCount (x : SDInstance) :
    #{g : BitString x.groundWidth | ∃ w : BitString (certWidth x.inputs),
      hasWitness x (List.ofFn g ++ List.ofFn w) = true} = 64 * x.affineOverlapCount := by
  rw [card_witnessSet, sum_pair_tests _ _ _ (fun y j r => r ∈ x.hits y j)]
  have he (y : BitString x.outputs) (j : ℕ) :
      univ.filter (fun r => r ∈ x.hits y j) = x.hits y j := filter_mem_eq_of_subset (subset_univ _)
  simp_rw [he]
  rfl

end Cslib.Complexity.SDInstance


namespace Cslib.Complexity

open Cslib Turing.MultiTapeTM
open SDInstance

/-- For the Statistical Difference definition of SZK, complements of SZK languages admit
Arthur–Merlin protocols. This is the coAM inclusion in [Sahai and Vadhan,
Corollary 4.5][SahaiVadhan2003] for total languages. -/
public theorem SZK_subset_coAM {α : Type} {enc : α ↪ List Bool} : SZK enc ⊆ coAM enc := by
  intro A hA
  obtain ⟨f, hf, hyes, hno⟩ :=
    (mem_PromiseSZK_iff_polyTimeReducible (hi := 2047 / 2048) (lo := 1 / 2048)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp hA
  have h := computableInPolyTime_parts hf
  have hn := h.fst'.fst'
  have hm := h.fst'.snd'
  have hM := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hn hn) hn
  have hK := ComputableInPolyTime.binary_two_pow.comp
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hn hM) hM)
  have hground : ComputableInPolyTime (fun a => (f a).groundWidth) enc encUnary := by
    unfold groundWidth hashWidth
    fun_prop
  have hcert : ComputableInPolyTime (fun a => certWidth (f a).inputs) enc encUnary := by
    unfold certWidth
    fun_prop
  change Aᶜ ∈ AM enc
  refine mem_AM_of_card_certifiedSet_of_length hground hcert
    (computableInPolyTime_hasWitness (hf.comp (ComputableInPolyTime.fst enc encBits))
      (ComputableInPolyTime.snd enc encBits)) hK (fun a => Nat.two_pow_pos _) ?_ ?_
  · intro a ha
    simp only [Function.comp_apply]
    rw [card_eq_mul_affineOverlapCount (f a)]
    exact le_mul_affineOverlapCount_of_close ((mem_no_statisticalDifference
      (by norm_num : (1 / 2048 : ℝ) < 2047 / 2048)).mp (hno ha))
  · intro a ha
    simp only [Function.comp_apply]
    rw [card_eq_mul_affineOverlapCount (f a)]
    exact mul_affineOverlapCount_le_of_far (mem_yes_statisticalDifference.mp
      (hyes (Set.notMem_compl_iff.mp ha)))

end Cslib.Complexity
