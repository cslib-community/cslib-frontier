/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.BinaryField
public import CslibFrontier.Probability.SmallBias.Powering
public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import CslibFrontier.Foundations.Data.BitString.List.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max

/-!
# Uniform polynomial-time construction of small-bias families

This is a construction milestone for the amplifying reduction in
[Goldreich2007DraftR5, Exercise 10.6],
not the gap-hardness result. The quadratic-system reduction and its violation-gap proof are
separate objectives.

Given a width `n` and a positive reciprocal-error parameter `k`, use the explicit binary field
of degree `w = floor(log₂(max 1 (n*k))) + 1`. Its size exceeds `n*k` and is at most
`2*(n*k+1)`. Enumerating all pairs of field elements and applying the AGHP powering construction
gives at most `4*(n*k+1)^2` masks, each of width `n`, with bias at most `1/k`.

The constructor includes trial-division search for the irreducible modulus, construction of its
multiplication table and every coordinate multiplication. Its inputs `n,k` are unary; the
polynomial-time certificate is uniform in both parameters. There is no advice table or
caller-supplied field operation.

## Main definitions

* `Cslib.BitString.poweringMasks`: the list of masks, including repeated masks.
* `Cslib.BitString.poweringWord`: the powering evaluator in field coordinates.

## Main results

* `Cslib.BitString.poweringMasks_polyTime`: uniform polynomial-time construction on unary inputs.
* `Cslib.BitString.poweringMasks_size`: the number and width of the masks.
* `Cslib.BitString.isSmallBias_poweringMasks`: bias of the uniform distribution on list entries.

## References

* [Alon, Goldreich, Håstad and Peralta][AlonGoldreichHastadPeralta1992],
  author-hosted June 14, 1992 version, §5, Construction 3 and Proposition 3, printed/PDF p. 10.
* [Goldreich][Goldreich2007DraftR5], Exercise 10.6.
-/

@[expose] public section

namespace Cslib.BitString

open Cslib.BinaryField Turing.MultiTapeTM ComputableInPolyTime
open Probability
open scoped BigOperators

/-- A power in coordinates, starting at the unit and multiplying `i` times by `x`. -/
def powerWord (tab : List (List (List Bool))) (x : List Bool) (i : ℕ) : List Bool :=
  (fun z => fieldMul tab z x)^[i] [true]

private theorem powerWord_polyTime {α : Type} {encIn : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {x : α → List Bool} {i : α → ℕ}
    (htab : ComputableInPolyTime tab encIn encTable)
    (hx : ComputableInPolyTime x encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a => powerWord (tab a) (x a) (i a)) encIn encBits := by
  unfold powerWord
  refine iterateWithInput_of_bounded_growth hi (const [true]) ?_
    ⟨((length_list (encList encBits)).comp htab).polyBounded, fun a z => ?_⟩
  · exact computableInPolyTime_fieldMul' (htab.comp (fst _ _)) (snd _ _)
      (hx.comp (fst _ _))
  · simp [length_fieldMul]

/-- Evaluate the powering construction using a multiplication table. Coordinates are padded to
its degree before taking the inner product. -/
def poweringWord (tab : List (List (List Bool))) (n : ℕ) (x y : List Bool) : List Bool :=
  (List.range n).map fun i => listDot (listRow tab.length 0 (powerWord tab x i)) y

@[simp] theorem length_poweringWord (tab : List (List (List Bool))) (n : ℕ) (x y : List Bool) :
    (poweringWord tab n x y).length = n := by simp [poweringWord]

private theorem fieldOfBits_powerWord {w : ℕ} (hw : w ≠ 0) (x : List Bool) (i : ℕ) :
    fieldOfBits (basis hw) (powerWord (fieldTable w) x i) =
      fieldOfBits (basis hw) x ^ i := by
  induction i with
  | zero => simp [powerWord, fieldOfBits_one hw]
  | succ i ih =>
    rw [powerWord, Function.iterate_succ_apply', ← powerWord,
      fieldOfBits_fieldMul (isMulTable_fieldTable hw), ih, pow_succ]

/-- The executable evaluator agrees with the abstract powering map on every seed. -/
theorem poweringWord_eq {w : ℕ} (hw : w ≠ 0) (n : ℕ) (x y : BitString w) :
    ofList n (poweringWord (fieldTable w) n (List.ofFn x) (List.ofFn y)) =
      powering (equivBits hw) n ((equivBits hw).symm x, (equivBits hw).symm y) := by
  have ht := (isMulTable_fieldTable hw).1
  funext i
  have hp : listRow (fieldTable w).length 0 (powerWord (fieldTable w) (List.ofFn x) i) =
      List.ofFn (equivBits hw ((equivBits hw).symm x ^ (i : ℕ))) := by
    apply List.ext_getElem (by simp [ht])
    intro j hj hj'
    have hjw : j < w := by simpa [ht] using hj
    have h := congrFun (congrArg (equivBits hw)
      (fieldOfBits_powerWord hw (List.ofFn x) i)) ⟨j, hjw⟩
    rw [equivBits_fieldOfBits] at h
    have hx : fieldOfBits (basis hw) (List.ofFn x) = (equivBits hw).symm x := by
      rw [fieldOfBits_basis]
      congr 1
      funext u
      simp
    rw [hx] at h
    rw [← getD_listRow_zero w _ _ hjw] at h
    rw [List.getD_eq_getElem (listRow w 0 (powerWord (fieldTable w) (List.ofFn x) i)) false
      (by simpa using hjw)] at h
    simpa only [ht, List.getElem_ofFn] using h
  change (poweringWord (fieldTable w) n (List.ofFn x) (List.ofFn y)).getD i false = _
  rw [poweringWord, List.getD_map_range _ false i.isLt, hp, listDot_ofFn]
  simp [powering]

/-- The positive field degree used for width `n` and reciprocal error `k`. -/
def smallBiasDegree (n k : ℕ) : ℕ := Nat.log 2 (max 1 (n * k)) + 1

private theorem degree_ne_zero (n k : ℕ) : smallBiasDegree n k ≠ 0 := by
  unfold smallBiasDegree
  omega

private theorem fieldSize_bounds (n k : ℕ) :
    n * k < 2 ^ smallBiasDegree n k ∧ 2 ^ smallBiasDegree n k ≤ 2 * (n * k + 1) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (max 1 (n * k))
  have h' := Nat.pow_log_le_self 2 (by omega : max 1 (n * k) ≠ 0)
  unfold smallBiasDegree
  rw [pow_succ]
  omega

/-- Enumerate the powering masks in binary seed order; repetitions are retained. -/
def poweringMasks (n k : ℕ) : List (List Bool) :=
  let w := smallBiasDegree n k
  let tab := fieldTable w
  (enumList w).flatMap fun x => (enumList w).map fun y => poweringWord tab n x y

/-- The table has polynomial size and every mask has the requested width. -/
theorem poweringMasks_size (n k : ℕ) :
    (poweringMasks n k).length = (2 ^ smallBiasDegree n k) ^ 2 ∧
      (poweringMasks n k).length ≤ 4 * (n * k + 1) ^ 2 ∧
      ∀ row ∈ poweringMasks n k, row.length = n := by
  have hlen : (poweringMasks n k).length = (2 ^ smallBiasDegree n k) ^ 2 := by
    simp [poweringMasks, List.length_flatMap, sq]
  refine ⟨hlen, ?_, ?_⟩
  · rw [hlen]
    calc (2 ^ smallBiasDegree n k) ^ 2 ≤ (2 * (n * k + 1)) ^ 2 :=
           Nat.pow_le_pow_left (fieldSize_bounds n k).2 2
         _ = 4 * (n * k + 1) ^ 2 := by ring
  · intro row hrow
    obtain ⟨x, _, hrow⟩ := List.mem_flatMap.mp hrow
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hrow
    simp

/-- The coordinate evaluator is polynomial-time, uniformly in the table and all inputs. -/
theorem poweringWord_polyTime {α : Type} {encIn : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {n : α → ℕ} {x y : α → List Bool}
    (htab : ComputableInPolyTime tab encIn encTable)
    (hn : ComputableInPolyTime n encIn encUnary)
    (hx : ComputableInPolyTime x encIn encBits)
    (hy : ComputableInPolyTime y encIn encBits) :
    ComputableInPolyTime (fun a => poweringWord (tab a) (n a) (x a) (y a)) encIn encBits := by
  unfold poweringWord
  refine mapToBitsWithInput (unary_range' hn) ?_
  apply bitsListDot ?_ (hy.comp (fst _ _))
  exact bitsRowWithInput ((length_list (encList encBits)).comp (htab.comp (fst _ _)))
    (const 0) (powerWord_polyTime (htab.comp (fst _ _)) (hx.comp (fst _ _)) (snd _ _))

/-- The entire mask table is constructed in uniform polynomial time on unary `(n,k)`. The
certificate includes the exhaustive modulus search, its trial divisions, the multiplication
table and all powering evaluations. -/
theorem poweringMasks_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => poweringMasks p.1 p.2)
      (encPair encUnary encUnary) (encList encBits) := by
  let enc := encPair encUnary encUnary
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => smallBiasDegree p.1 p.2) enc encUnary := by
    unfold smallBiasDegree
    fun_prop
  have hsize : PolyBounded (fun p : ℕ × ℕ => (enc p).length)
      (fun p => 2 ^ smallBiasDegree p.1 p.2) :=
    (((PolyBounded.const 2).mul
      (((fst encUnary encUnary).polyBounded.mul (snd encUnary encUnary).polyBounded).add
        (.const 1)))).mono fun p => (fieldSize_bounds p.1 p.2).2
  have hbound : ComputableInPolyTime
      (fun p : ℕ × ℕ => 2 ^ (smallBiasDegree p.1 p.2 + 1)) enc encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp (unary_add' hw (const 1)))
      (bound := fun p => 4 * (p.1 * p.2 + 1)) (by fun_prop) fun p => by
        have := (fieldSize_bounds p.1 p.2).2
        rw [pow_succ]
        omega
  have hmod := computableInPolyTime_bits_unary.comp
    (computableInPolyTime_leastIrreducibleCode.comp (hbound.prod hw))
  have htab : ComputableInPolyTime (fun p : ℕ × ℕ => fieldTable (smallBiasDegree p.1 p.2))
      enc encTable := by
    simpa only [fieldTable, modulusBits, Function.comp_def] using
      computableInPolyTime_powerMulTable.comp hmod
  have hseeds := bitsEnumList_of_polyBounded hw hsize
  unfold poweringMasks
  refine flatMapWithInput hseeds (mapWithInput (hseeds.comp (fst _ _)) ?_)
  exact poweringWord_polyTime (htab.comp ((fst _ _).comp (fst _ _)))
    ((fst encUnary encUnary).comp ((fst _ _).comp (fst _ _)))
    ((snd _ encBits).comp (fst _ _)) (snd _ encBits)

private theorem poweringMasks_eq_ofFn (n k : ℕ) :
    let w := smallBiasDegree n k
    poweringMasks n k = List.ofFn fun j : Fin (2 ^ w * 2 ^ w) =>
      poweringWord (fieldTable w) n
        (List.ofFn ((equivFin w).symm (finProdFinEquiv.symm j).1))
        (List.ofFn ((equivFin w).symm (finProdFinEquiv.symm j).2)) := by
  dsimp only
  rw [List.ofFn_mul]
  simp only [poweringMasks, enumList_eq_ofFn, List.flatMap, List.map_ofFn, Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hpair : (⟨i * 2 ^ smallBiasDegree n k + j, by nlinarith [i.isLt, j.isLt]⟩ :
      Fin (2 ^ smallBiasDegree n k * 2 ^ smallBiasDegree n k)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    change (i : ℕ) * 2 ^ smallBiasDegree n k + j = j + 2 ^ smallBiasDegree n k * i
    ring
  rw [hpair, Equiv.symm_apply_apply]

/-- Under a uniform seed pair, the explicitly evaluated family is `1/k`-biased. The uniform
seed order is exactly the double enumeration used by `poweringMasks`. -/
theorem isSmallBias_poweringWord (n : ℕ) {k : ℕ} (hk : 0 < k) :
    let w := smallBiasDegree n k
    IsSmallBias (1 / (k : ℝ))
      ((PMF.uniformOfFintype (BitString w × BitString w)).map fun s =>
        ofList n (poweringWord (fieldTable w) n (List.ofFn s.1) (List.ofFn s.2))) := by
  let w := smallBiasDegree n k
  have hw := degree_ne_zero n k
  let e := Equiv.prodCongr (equivBits hw).toEquiv (equivBits hw).toEquiv
  have hb := isSmallBias_powering (equivBits hw) (n := n)
  have hbound : ((n - 1 : ℕ) / Fintype.card (BinaryField w) : ℝ) ≤ 1 / k := by
    rw [BinaryField.card hw]
    have hpos : (0 : ℝ) < (2 ^ smallBiasDegree n k : ℕ) := by positivity
    rw [div_le_div_iff₀ hpos (by exact_mod_cast hk)]
    have hn : n - 1 ≤ n := Nat.sub_le _ _
    have hsize := (fieldSize_bounds n k).1.le
    norm_cast
    simpa only [one_mul] using (Nat.mul_le_mul_right k hn).trans hsize
  dsimp only
  intro S hS
  have h := hb.mono hbound S hS
  rw [bias_uniformOfFintype_map] at h ⊢
  have he := Fintype.expect_equiv e
    (fun s => chi ℝ S (powering (equivBits hw) n s))
    (fun s => chi ℝ S (ofList n
      (poweringWord (fieldTable w) n (List.ofFn s.1) (List.ofFn s.2)))) (fun s => by
        rw [poweringWord_eq hw]
        simp [e])
  rwa [he] at h

instance (n k : ℕ) : NeZero (poweringMasks n k).length :=
  ⟨by rw [(poweringMasks_size n k).1]; positivity⟩

/-- The uniform distribution on the entries of the constructed mask list is `1/k`-biased.
Repeated masks are counted with their multiplicities. -/
theorem isSmallBias_poweringMasks (n : ℕ) {k : ℕ} (hk : 0 < k) :
    IsSmallBias (ι := Fin n) (1 / (k : ℝ))
      ((PMF.uniformOfFintype (Fin (poweringMasks n k).length)).map
        fun i : Fin (poweringMasks n k).length =>
        ofList n ((poweringMasks n k).getD i [])) := by
  let w := smallBiasDegree n k
  have hlen : (poweringMasks n k).length = 2 ^ w * 2 ^ w := by
    simpa only [sq] using (poweringMasks_size n k).1
  let e : Fin (poweringMasks n k).length ≃ BitString w × BitString w :=
    (finCongr hlen).trans (finProdFinEquiv.symm.trans
      (Equiv.prodCongr (equivFin w).symm (equivFin w).symm))
  intro S hS
  have h := isSmallBias_poweringWord n hk S hS
  rw [bias_uniformOfFintype_map] at h ⊢
  have he := Fintype.expect_equiv e
    (fun i => chi ℝ S (ofList n ((poweringMasks n k).getD i [])))
    (fun s => chi ℝ S (ofList n
      (poweringWord (fieldTable w) n (List.ofFn s.1) (List.ofFn s.2)))) (fun i => by
        have hi : (i : ℕ) < 2 ^ w * 2 ^ w := hlen ▸ i.isLt
        have hrow := congrArg (fun rows : List (List Bool) => rows.getD (i : ℕ) [])
          (poweringMasks_eq_ofFn n k)
        rw [hrow]
        rw [List.getD_ofFn_of_lt _ hi []]
        rfl)
  rwa [he]

end Cslib.BitString
