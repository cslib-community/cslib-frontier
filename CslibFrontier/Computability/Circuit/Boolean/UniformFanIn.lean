/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.UniformDepth
import CslibFrontier.Computability.Circuit.SimulationDepth
import CslibFrontier.Computability.Circuit.Iteration
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Circuit.Encoding.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Tabulation
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-!
# Uniform fan-in reduction

Replacing a gate of unbounded fan-in by equal-width layers of binary disjunctions makes the
gate addresses and the incoming wires accessible by arithmetic on indices. At round `t`,
wire `i` reads the disjunction of `2^t` consecutive leaves, starting at `2^t i` modulo the
layer width. Thus the first wire reads all leaves after a logarithmic number of rounds.

## Main definitions

* `Unbounded.toFanInTwo` compiles a native single-output circuit over the unbounded basis.

## Main results

* `Unbounded.eval_toFanInTwo` preserves the computed function.
* `Unbounded.depth_toFanInTwo_le` bounds the extra depth by the source encoding length.
* `Unbounded.isLogspaceUniform_toFanInTwo` constructs the logspace generator.
* `logspaceUniformAC_subset_NC_succ` gives the resulting containment at every level.

## References

[Arora and Barak][AroraBarak09], §6.7.1, Definitions 6.24–6.25 and the following paragraph
(pp. 117–118), gives the fan-in simulation. Here the generator of Definition 6.14, §6.2,
writes the complete circuit on a write-only output tape. The layer construction makes the
logspace uniformity of the simulation explicit.
-/

public section

namespace Cslib.Circuits.Boolean

namespace Unbounded

private def cyclicIndex (k i : ℕ) : Fin (k + 1) :=
  ⟨i % (k + 1), Nat.mod_lt _ (by omega)⟩

private def orRound (k : ℕ) : Circuit Boolean.signature (k + 1) (k + 1) :=
  Circuit.pi fun i => Circuit.oneGate .or ![cyclicIndex k (2 * i), cyclicIndex k (2 * i + 1)]

private theorem eval_orRound (k i : ℕ) (x : BitString (k + 1)) :
    (orRound k).eval Boolean.interpretation x (cyclicIndex k i) =
      (x (cyclicIndex k (2 * i)) || x (cyclicIndex k (2 * i + 1))) := by
  simp only [orRound, Circuit.eval_pi, Circuit.eval_oneGate]
  change (x (cyclicIndex k (2 * (i % (k + 1)))) ||
    x (cyclicIndex k (2 * (i % (k + 1)) + 1))) = _
  congr 2 <;> apply Fin.ext
  · simp [cyclicIndex, Nat.mul_mod]
  · simp [cyclicIndex, Nat.add_mod, Nat.mul_mod]

private theorem eval_iterate_orRound (k t : ℕ) (x : BitString (k + 1)) (i : ℕ) :
    ((orRound k).iterate t).eval Boolean.interpretation x (cyclicIndex k i) = true ↔
      ∃ j < 2 ^ t, x (cyclicIndex k (i * 2 ^ t + j)) = true := by
  induction t generalizing i with
  | zero => simp [Circuit.iterate]
  | succ t ih =>
    rw [Circuit.iterate, Circuit.eval_comp, eval_orRound, Bool.or_eq_true,
      ih, ih]
    have hleft (j : ℕ) : 2 * i * 2 ^ t + j = i * 2 ^ (t + 1) + j := by ring
    have hright (j : ℕ) : (2 * i + 1) * 2 ^ t + j = i * 2 ^ (t + 1) + (j + 2 ^ t) := by ring
    simp only [hleft, hright]
    constructor
    · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
      · exact ⟨j, by rw [pow_succ]; omega, h⟩
      · exact ⟨j + 2 ^ t, by rw [pow_succ]; omega, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hlt : j < 2 ^ t
      · exact Or.inl ⟨j, hlt, h⟩
      · refine Or.inr ⟨j - 2 ^ t, by rw [pow_succ] at hj; omega, ?_⟩
        rwa [Nat.sub_add_cancel (by omega)]

private def negatesInput : Op → Bool
  | .or _ => false
  | _ => true

private def isAnd : Op → Bool
  | .and _ => true
  | _ => false

private def leaf (op : Op) (i : ℕ) : Circuit Boolean.signature op.arity 1 :=
  if h : i < op.arity then
    if negatesInput op then Circuit.oneGate .not (fun _ => ⟨i, h⟩)
    else Circuit.oneGate .or (fun _ => ⟨i, h⟩)
  else Circuit.oneGate (.const false) Fin.elim0

private def finalGate (k : ℕ) (op : Op) : Circuit Boolean.signature (k + 1) 1 :=
  if isAnd op then Circuit.oneGate .not (fun _ => 0)
  else Circuit.oneGate .or (fun _ => 0)

private def blockLayers (k : ℕ) (op : Op) : ℕ → Circuit Boolean.signature op.arity (k + 1)
  | 0 => Circuit.pi fun i => leaf op i
  | t + 1 => (orRound k).comp (blockLayers k op t)

private theorem eval_blockLayers (k t : ℕ) (op : Op) (x : BitString op.arity) :
    (blockLayers k op t).eval Boolean.interpretation x =
      ((orRound k).iterate t).eval Boolean.interpretation
        ((Circuit.pi fun i : Fin (k + 1) => leaf op i).eval Boolean.interpretation x) := by
  induction t with
  | zero => simp [blockLayers, Circuit.iterate]
  | succ t ih => simp only [blockLayers, Circuit.iterate, Circuit.eval_comp, ih]

private def fanInBlock (bound : ℕ) (op : Op) : Circuit Boolean.signature op.arity 1 :=
  let k := max bound op.arity
  (finalGate k op).comp (blockLayers k op (k + 1).log2.succ)

private theorem exists_true_leaf (k : ℕ) (op : Op) (hk : op.arity ≤ k + 1)
    (x : BitString op.arity) :
    (∃ i : Fin (k + 1), (leaf op i).eval Boolean.interpretation x 0 = true) ↔
      ∃ j : Fin op.arity, (x j != negatesInput op) = true := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i.val < op.arity
    · refine ⟨⟨i, h⟩, ?_⟩
      cases hn : negatesInput op <;> simpa [leaf, h, hn, Boolean.interpretation] using hi
    · simp [leaf, h, Boolean.interpretation] at hi
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, j.isLt.trans_le hk⟩, ?_⟩
    cases hn : negatesInput op <;> simpa [leaf, j.isLt, hn, Boolean.interpretation] using hj

private theorem computes_fanInBlock (bound : ℕ) (op : Op) :
    (fanInBlock bound op).Computes Boolean.interpretation (single (interpretation op)) := by
  let k := max bound op.arity
  let t := (k + 1).log2.succ
  have hk : op.arity ≤ k + 1 := (le_max_right _ _).trans (Nat.le_succ _)
  have ht : k + 1 ≤ 2 ^ t := (Nat.lt_log2_self (n := k + 1)).le
  intro x
  funext j
  let v := (Circuit.pi fun i : Fin (k + 1) => leaf op i).eval Boolean.interpretation x
  have hroot : ((orRound k).iterate t).eval Boolean.interpretation v 0 = true ↔
      ∃ j : Fin op.arity, (x j != negatesInput op) = true := by
    rw [← exists_true_leaf k op hk x]
    change ((orRound k).iterate t).eval Boolean.interpretation v (cyclicIndex k 0) = true ↔ _
    rw [eval_iterate_orRound]
    simp only [Nat.zero_mul, Nat.zero_add]
    constructor
    · rintro ⟨j, _, hj⟩
      exact ⟨cyclicIndex k j, by simpa [v] using hj⟩
    · rintro ⟨i, hi⟩
      refine ⟨i.val, i.isLt.trans_le ht, ?_⟩
      have he : cyclicIndex k i = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      simpa [v, he] using hi
  simp only [fanInBlock, Circuit.eval_comp, eval_blockLayers, single]
  change (finalGate k op).eval Boolean.interpretation
    (((orRound k).iterate t).eval Boolean.interpretation v) j = interpretation op x
  cases op with
  | not =>
    apply Bool.eq_iff_iff.mpr
    simpa [finalGate, isAnd, negatesInput, Boolean.interpretation, interpretation,
      Fin.exists_fin_one] using hroot
  | or m =>
    apply Bool.eq_iff_iff.mpr
    simpa [finalGate, isAnd, negatesInput, Boolean.interpretation, interpretation] using hroot
  | and m =>
    apply Bool.eq_iff_iff.mpr
    simpa [finalGate, isAnd, negatesInput, Boolean.interpretation, interpretation] using hroot.not

private theorem size_leaf (op : Op) (i : ℕ) : (leaf op i).size = 1 := by
  unfold leaf
  split
  · split <;> rfl
  · rfl

private theorem depth_leaf (op : Op) (i : ℕ) : (leaf op i).depth = 1 := by
  unfold leaf
  split
  · split <;> exact Circuit.depth_oneGate _ _
  · exact Circuit.depth_oneGate _ _

private theorem size_fanInBlock (bound : ℕ) (op : Op) :
    (fanInBlock bound op).size =
      (max bound op.arity + 1) * ((max bound op.arity + 1).log2 + 2) + 1 := by
  have hfinal (k : ℕ) : (finalGate k op).size = 1 := by unfold finalGate; split <;> rfl
  have h (k t : ℕ) : (blockLayers k op t).size = (t + 1) * (k + 1) := by
    induction t with
    | zero => simp [blockLayers, size_leaf]
    | succ t ih => simp [blockLayers, ih, orRound, Nat.succ_mul]
  simp [fanInBlock, hfinal, h, Nat.mul_comm]

private theorem depth_fanInBlock_le (bound : ℕ) (op : Op) :
    (fanInBlock bound op).depth ≤ (max bound op.arity + 1).log2 + 3 := by
  let k := max bound op.arity
  have hfinal : (finalGate k op).depth = 1 := by
    unfold finalGate
    split <;> exact Circuit.depth_oneGate _ _
  have hround : (orRound k).depth ≤ 1 :=
    Circuit.depth_pi_le _ fun _ => (Circuit.depth_oneGate _ _).le
  have hleaves : (Circuit.pi fun i : Fin (k + 1) => leaf op i).depth ≤ 1 :=
    Circuit.depth_pi_le _ fun _ => (depth_leaf ..).le
  have hd (t : ℕ) : (blockLayers k op t).depth ≤ t + 1 := by
    induction t with
    | zero => exact hleaves
    | succ t ih => exact (Circuit.depth_comp_le _ _).trans (by lia)
  exact (Circuit.depth_comp_le _ _).trans (by dsimp only [k] at *; lia [hd (k + 1).log2.succ])

private def leafRow (op : Op) (i : ℕ) : Boolean.Op × List ℕ :=
  if i < op.arity then
    if negatesInput op then (.not, [i]) else (.or, [i, i])
  else (.const false, [])

private def orRow (k offset i : ℕ) : Boolean.Op × List ℕ :=
  (.or, [offset + (2 * i) % (k + 1), offset + (2 * i + 1) % (k + 1)])

private theorem code_leaf (op : Op) (i : ℕ) :
    (leaf op i).code = ([leafRow op i], [op.arity]) := by
  unfold leaf leafRow
  split
  · split <;> rw [Circuit.code_oneGate] <;> rfl
  · rw [Circuit.code_oneGate]
    rfl

private theorem code_leaves (k : ℕ) (op : Op) :
    (Circuit.pi fun i : Fin (k + 1) => leaf op i).code =
      ((List.range (k + 1)).map (leafRow op), (List.range (k + 1)).map (op.arity + ·)) := by
  rw [Circuit.code_pi_singleton _ (fun i => leafRow op i) (fun i => code_leaf op i)]
  · congr 1
    exact (List.map_range_eq_ofFn _ _).symm

private theorem code_orRound (k : ℕ) :
    (orRound k).code =
      ((List.range (k + 1)).map (orRow k 0), (List.range (k + 1)).map ((k + 1) + ·)) := by
  rw [orRound, Circuit.code_pi_singleton _ (fun i => orRow k 0 i)]
  · congr 1
    exact (List.map_range_eq_ofFn _ _).symm
  · intro i
    rw [Circuit.code_oneGate]
    simp [orRow, cyclicIndex, List.ofFn_succ]

private def blockRow (k : ℕ) (op : Op) (i : ℕ) : Boolean.Op × List ℕ :=
  if i < k + 1 then leafRow op i
  else orRow k (op.arity + (i / (k + 1) - 1) * (k + 1)) (i % (k + 1))

private theorem compCodeWire_layer {Op : Type} (n offset width : ℕ) (gs : List (Op × List ℕ))
    (i : ℕ) :
    Circuit.compCodeWire n (gs, (List.range width).map (offset + ·)) i =
      if i < width then offset + i else n + gs.length + (i - width) := by
  simp only [Circuit.compCodeWire, List.length_map, List.length_range]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD]
    simp [h]
  · rfl

private theorem code_blockLayers (k t : ℕ) (op : Op) :
    (blockLayers k op t).code =
      ((List.range ((t + 1) * (k + 1))).map (blockRow k op),
        (List.range (k + 1)).map (op.arity + t * (k + 1) + ·)) := by
  induction t with
  | zero =>
    simp only [blockLayers, code_leaves, zero_add, one_mul, zero_mul, add_zero]
    congr 1
    exact List.map_congr_left fun i hi => by simp [blockRow, List.mem_range.mp hi]
  | succ t ih =>
    rw [blockLayers, Circuit.code_comp, code_orRound, ih, Circuit.compCode]
    let W := k + 1
    have hW : 0 < W := Nat.zero_lt_succ k
    have hshift (i : ℕ) (hi : i < W) :
        blockRow k op ((t + 1) * W + i) = orRow k (op.arity + t * W) i := by
      have hge : W ≤ (t + 1) * W + i := by dsimp only [W]; rw [Nat.succ_mul]; omega
      unfold blockRow
      change (if (t + 1) * W + i < W then _ else
        orRow k (op.arity + (((t + 1) * W + i) / W - 1) * W) (((t + 1) * W + i) % W)) = _
      rw [ite_eq_right (Nat.not_lt.mpr hge), Nat.mul_comm (t + 1) W, Nat.mul_add_div hW,
        Nat.div_eq_of_lt hi, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
      simp
    change ((List.range ((t + 1) * W)).map (blockRow k op) ++
        ((List.range W).map (orRow k 0)).map _, ((List.range W).map (W + ·)).map _) = _
    rw [show (t + 1 + 1) * W = (t + 1) * W + W from Nat.succ_mul ..,
      List.range_add (n := (t + 1) * W) (m := W),
      List.map_append, List.map_map, List.map_map, List.map_map]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply]
      rw [hshift _ (List.mem_range.mp hi)]
      simp only [orRow, List.map_cons, List.map_nil, zero_add, compCodeWire_layer]
      have h₁ := Nat.mod_lt (2 * i) hW
      have h₂ := Nat.mod_lt (2 * i + 1) hW
      simp [W] at h₁ h₂ ⊢
      omega
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, compCodeWire_layer, List.length_map, List.length_range]
      simp only [← show k + 1 = W from rfl]
      split <;> omega

private def finalRow (op : Op) (wire : ℕ) : Boolean.Op × List ℕ :=
  if isAnd op then (.not, [wire]) else (.or, [wire, wire])

private theorem code_finalGate (k : ℕ) (op : Op) :
    (finalGate k op).code = ([finalRow op 0], [k + 1]) := by
  unfold finalGate finalRow
  split <;> rw [Circuit.code_oneGate] <;> rfl

private def blockLength (k : ℕ) := ((k + 1).log2 + 2) * (k + 1) + 1

private def emittedRow (k : ℕ) (op : Op) (i : ℕ) : Boolean.Op × List ℕ :=
  if i < blockLength k - 1 then blockRow k op i
  else finalRow op (op.arity + (k + 1).log2.succ * (k + 1))

private theorem code_fanInBlock (bound : ℕ) (op : Op) :
    (fanInBlock bound op).code =
      ((List.range (blockLength (max bound op.arity))).map (emittedRow (max bound op.arity) op),
        [op.arity + (blockLength (max bound op.arity) - 1)]) := by
  let k := max bound op.arity
  change ((finalGate k op).comp _).code = _
  rw [Circuit.code_comp, code_finalGate, code_blockLayers, Circuit.compCode]
  let t := (k + 1).log2.succ
  let W := k + 1
  let N := (t + 1) * W
  change (_, _) = ((List.range (N + 1)).map (emittedRow k op), [op.arity + (N + 1 - 1)])
  rw [List.range_succ (n := N), List.map_append]
  simp only [List.map_cons, List.map_nil, Nat.add_sub_cancel]
  have hprefix : (List.range N).map (blockRow k op) = (List.range N).map (emittedRow k op) :=
    List.map_congr_left fun i hi => by
      change _ = if i < N + 1 - 1 then _ else _
      simp [List.mem_range.mp hi]
  rw [hprefix]
  congr 1
  · congr 1
    change [(_, (finalRow op 0).2.map _)] = [if N < N then _ else _]
    simp only [lt_self_iff_false, ite_false]
    unfold finalRow
    split <;> simp [compCodeWire_layer, k]
  · change [Circuit.compCodeWire op.arity
        ((List.range N).map (emittedRow k op), (List.range W).map (op.arity + t * W + ·)) W] =
      [op.arity + N]
    simp [compCodeWire_layer]

open Turing.MultiTapeTM

private def encodedLength {n : ℕ} (c : Circuit signature n 1) : ℕ :=
  (encCircuit 1 ⟨n, c⟩).length

private theorem arity_le_encodedLength {n : ℕ} (c : Circuit signature n 1) (i : Fin c.size) :
    (c.program.lines i).op.arity ≤ encodedLength c := by
  let g := (c.program.lines i).code
  have hg : g ∈ c.code.1 := by
    change g ∈ c.program.code
    rw [Program.code_eq_ofFn_lines]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hrow := length_le_encList_of_mem (Circuit.encGate encOp) hg
  have hwires := length_le_length_encList encNat g.2
  change signature.Arity (c.program.lines i).op ≤ _
  rw [← Line.length_code_snd]
  change g.2.length ≤ _
  rw [encodedLength, Circuit.encCircuit_apply, length_encPair, Circuit.encCode, length_encPair]
  rw [Circuit.encGate, length_encPair] at hrow
  dsimp only [Circuit.encGate] at *
  omega

/-- Compile a single-output unbounded fan-in circuit into a fan-in-two circuit. All gate
replacements have the same length, determined by the source circuit's encoding. -/
def toFanInTwo {n : ℕ} (c : Circuit signature n 1) : Circuit Boolean.signature n 1 :=
  c.simulate (fanInBlock (encodedLength c))

/-- The compiled circuit computes the same Boolean function on every assignment. -/
theorem eval_toFanInTwo {n : ℕ} (c : Circuit signature n 1) :
    (toFanInTwo c).eval Boolean.interpretation = c.eval interpretation :=
  Circuit.eval_simulate _ _ (computes_fanInBlock _)

/-- Each source depth level costs at most three plus the logarithm of one more than the source
encoding length. This also bounds gates with repeated incoming wires. -/
theorem depth_toFanInTwo_le {n : ℕ} (c : Circuit signature n 1) :
    (toFanInTwo c).depth ≤ (((encCircuit 1 ⟨n, c⟩).length + 1).log2 + 3) * c.depth := by
  refine (Circuit.depth_simulate_le _ _).trans (Circuit.depthWith_le_mul_depth _ fun i => ?_)
  change _ ≤ (encodedLength c + 1).log2 + 3
  simpa only [max_eq_left (arity_le_encodedLength c i)] using
    depth_fanInBlock_le (encodedLength c) (c.program.lines i).op

private theorem encodedLength_fl {C : (n : ℕ) → Circuit signature n 1}
    (hC : Circuit.IsLogspaceUniform encOp C) :
    ComputableInLogSpace (fun n => encodedLength (C n)) encUnary encUnary :=
  ComputableInLogSpace.bitsLength.comp' <|
    (ComputableInLogSpace.of_eq (encIn := encCircuit 1) (encMid := encBits)
      fun _ => rfl).comp hC

private theorem exists_depthBound {C : (n : ℕ) → Circuit signature n 1}
    (hC : Circuit.IsLogspaceUniform encOp C) :
    ∃ e, ∀ n, (encodedLength (C n) + 1).log2 + 3 ≤ e * (Nat.log 2 n + 1) := by
  have hsize : PolynomiallyBounded (fun n => encodedLength (C n)) :=
    hC.polynomiallyBounded_length
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => encodedLength (C n) + 1) (by fun_prop)
  refine ⟨e + 3, fun n => ?_⟩
  rw [Nat.log2_eq_log_two, Nat.add_mul]
  have := (Nat.log_le_clog 2 (encodedLength (C n) + 1)).trans (he n)
  omega

private theorem blockLength_fl {α : Type} {enc : α ↪ List Bool} {k : α → ℕ}
    (hk : ComputableInLogSpace k enc encUnary) :
    ComputableInLogSpace (fun x => blockLength (k x)) enc encUnary := by
  unfold blockLength
  fun_prop

private def mapInputs {G : Type} (w : ℕ → ℕ) (r : G × List ℕ) := (r.1, r.2.map w)

private theorem emittedRow_fl {α : Type} {enc : α ↪ List Bool} {k i : α → ℕ} {op : α → Op}
    {wire : α → ℕ → ℕ} (hk : ComputableInLogSpace k enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) (hop : ComputableInLogSpace op enc encOp)
    (ha : ComputableInLogSpace (fun x => (op x).arity) enc encUnary)
    (hw : ∀ {f : α → ℕ}, ComputableInLogSpace f enc encUnary →
      ComputableInLogSpace (fun x => wire x (f x)) enc encNat) :
    ComputableInLogSpace (fun x => mapInputs (wire x) (emittedRow (k x) (op x) (i x))) enc
      (Circuit.encGate Boolean.encOp) := by
  have hnum : ComputableInLogSpace (fun x => (op x).toNat) enc encUnary :=
    (ComputableInLogSpace.of_eq (encIn := encOp) (encMid := encUnary) fun _ => rfl).comp' hop
  have hand : ComputableInLogSpace (fun x => isAnd (op x)) enc encBool :=
    (ComputableInLogSpace.unaryEq (ComputableInLogSpace.unaryMod hnum (.const 2))
      (.const 1)).congr_fun fun x => by cases op x <;> simp [isAnd, Op.toNat]
  have hneg : ComputableInLogSpace (fun x => negatesInput (op x)) enc encBool :=
    (ComputableInLogSpace.bool_or (ComputableInLogSpace.unaryEq hnum (.const 0)) hand).congr_fun
      fun x => by cases op x <;> simp [negatesInput, isAnd, Op.toNat]
  have h1 (g : Boolean.Op) {f : α → ℕ} (hf : ComputableInLogSpace f enc encUnary) :
      ComputableInLogSpace (fun x => (g, [wire x (f x)])) enc (Circuit.encGate Boolean.encOp) :=
    ComputableInLogSpace.pair (.const g) (ComputableInLogSpace.listSingleton.comp' (hw hf))
  have h2 (g : Boolean.Op) {f l : α → ℕ} (hf : ComputableInLogSpace f enc encUnary)
      (hl : ComputableInLogSpace l enc encUnary) :
      ComputableInLogSpace (fun x => (g, [wire x (f x), wire x (l x)])) enc
        (Circuit.encGate Boolean.encOp) :=
    ComputableInLogSpace.pair (.const g) <|
      (hw hf).listCons (ComputableInLogSpace.listSingleton.comp' (hw hl))
  have hB := blockLength_fl hk
  have hf : ComputableInLogSpace (fun x => (op x).arity + ((k x + 1).log2 + 1) * (k x + 1))
      enc encUnary := by fun_prop
  have hp : ComputableInLogSpace
      (fun x => (op x).arity + (i x / (k x + 1) - 1) * (k x + 1)) enc encUnary := by fun_prop
  have hj : ComputableInLogSpace (fun x => i x % (k x + 1)) enc encUnary := by fun_prop
  unfold emittedRow blockRow leafRow finalRow orRow
  simp only [apply_ite (mapInputs _)]
  simp only [mapInputs, List.map_nil, List.map_cons]
  apply ComputableInLogSpace.ite_decide (encC := encBool) (by fun_prop)
  · apply ComputableInLogSpace.ite_decide (encC := encBool) (by fun_prop)
    · apply ComputableInLogSpace.ite_decide (encC := encBool) (by fun_prop)
      · exact ComputableInLogSpace.ite hneg (h1 _ hi) (h2 _ hi hi)
      · exact .const _
    · apply h2 <;> fun_prop
  · exact ComputableInLogSpace.ite hand (h1 _ hf) (h2 _ hf hf)

private def sourceLine {n : ℕ} (c : Circuit signature n 1) (i : ℕ) : Op × List ℕ :=
  c.program.code.getD i (.and 0, [])

private theorem sourceLine_spec {n : ℕ} (c : Circuit signature n 1) (i : ℕ) :
    let g := sourceLine c i
    g.2.length = g.1.arity ∧ ∀ j ∈ g.2, j < n + c.size := by
  by_cases hi : i < c.size
  · have he := c.program.getD_code ⟨i, hi⟩ (.and 0, [])
    unfold sourceLine
    rw [he]
    exact ⟨Line.length_code_snd _, by simp [Line.code, Wire.toNat_lt]⟩
  · have hlen : c.program.code.length ≤ i := (Program.length_code c.program).le.trans (by omega)
    unfold sourceLine
    rw [List.getD_eq_default _ _ hlen]
    simp [Op.arity]

private theorem code_fl {C : (n : ℕ) → Circuit signature n 1}
    (hC : Circuit.IsLogspaceUniform encOp C) :
    ComputableInLogSpace (fun n => (C n).code) encUnary (Circuit.encCode encOp) := by
  have h : ComputableInLogSpace (fun n => (n, (C n).code)) encUnary
      (encPair encUnary (Circuit.encCode encOp)) :=
    (ComputableInLogSpace.of_eq (encIn := encCircuit 1)
      (f := fun t => (t.1, t.2.code)) fun _ => rfl).comp' hC
  exact (ComputableInLogSpace.snd _ _).comp' h

private theorem sourceLine_fl {α : Type} {enc : α ↪ List Bool}
    {C : (n : ℕ) → Circuit signature n 1} (hC : Circuit.IsLogspaceUniform encOp C)
    {n i : α → ℕ} (hn : ComputableInLogSpace n enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun x => sourceLine (C (n x)) (i x)) enc (Circuit.encGate encOp) := by
  have h := (ComputableInLogSpace.fst _ _).comp' ((code_fl hC).comp' hn)
  unfold sourceLine
  simp only [List.getD_eq_getElem?_getD]
  exact (ComputableInLogSpace.optionGetD _).comp' (ComputableInLogSpace.getElem?' h hi)

private theorem polyBounded_wire {α : Type} {enc : α ↪ List Bool}
    {C : (n : ℕ) → Circuit signature n 1} (hC : Circuit.IsLogspaceUniform encOp C)
    {n f : α → ℕ} (hn : ComputableInLogSpace n enc encUnary)
    (hf : ∀ x, f x ≤ n x + (C (n x)).size) : PolyBounded (fun x => (enc x).length) f := by
  have h₁ : PolyBounded (fun x => (enc x).length) n := by simpa using hn.polyBounded_length
  have h₂ : PolyBounded (fun x => (enc x).length) (fun x => encodedLength (C (n x))) := by
    simpa using ((encodedLength_fl hC).comp' hn).polyBounded_length
  apply (h₁.add h₂).mono
  intro x
  apply (hf x).trans
  apply Nat.add_le_add_left
  exact Circuit.size_le_length_encCircuit (σ := signature) encOp ⟨n x, C (n x)⟩

private theorem wire_getD_le {n : ℕ} (c : Circuit signature n 1) (i j : ℕ) :
    (sourceLine c i).2.getD j 0 ≤ n + c.size := by
  by_cases hj : j < (sourceLine c i).2.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact ((sourceLine_spec c i).2 _ (List.getElem_mem hj)).le
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    omega

private def blockWire {n : ℕ} (c : Circuit signature n 1) (i w : ℕ) :=
  let g := sourceLine c i
  let B := blockLength (encodedLength c)
  if w < g.1.arity then Circuit.simulateWireNumber n B (g.2.getD w 0)
  else n + i * B + (w - g.1.arity)

private def gateEntry {n : ℕ} (c : Circuit signature n 1) (i j : ℕ) :=
  mapInputs (blockWire c i) (emittedRow (encodedLength c) (sourceLine c i).1 j)

private theorem simulateWireNumber_fl {α : Type} {enc : α ↪ List Bool} {n B w : α → ℕ}
    (hn : ComputableInLogSpace n enc encUnary) (hB : ComputableInLogSpace B enc encUnary)
    (hw : ComputableInLogSpace w enc encUnary) :
    ComputableInLogSpace (fun x => Circuit.simulateWireNumber (n x) (B x) (w x)) enc encUnary := by
  unfold Circuit.simulateWireNumber
  exact ComputableInLogSpace.ite_decide (hw.unaryLt hn) hw (by fun_prop)

private theorem gateEntry_fl {α : Type} {enc : α ↪ List Bool}
    {C : (n : ℕ) → Circuit signature n 1} (hC : Circuit.IsLogspaceUniform encOp C)
    {n i j : α → ℕ} (hn : ComputableInLogSpace n enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) (hj : ComputableInLogSpace j enc encUnary) :
    ComputableInLogSpace (fun x => gateEntry (C (n x)) (i x) (j x)) enc
      (Circuit.encGate Boolean.encOp) := by
  have hk := (encodedLength_fl hC).comp' hn
  have hB := blockLength_fl hk
  have hrow := sourceLine_fl hC hn hi
  have hargs := (ComputableInLogSpace.snd encOp (encList encNat)).comp' hrow
  have ha : ComputableInLogSpace (fun x => (sourceLine (C (n x)) (i x)).1.arity) enc encUnary :=
    (ComputableInLogSpace.listLength.comp' hargs).congr_fun fun x => (sourceLine_spec _ _).1.symm
  apply emittedRow_fl hk hj ((ComputableInLogSpace.fst _ _).comp' hrow) ha
  intro f hf
  have hbinary : ComputableInLogSpace (fun x => (sourceLine (C (n x)) (i x)).2.getD (f x) 0)
      enc encNat := by
    simp only [List.getD_eq_getElem?_getD]
    exact (ComputableInLogSpace.optionGetD 0).comp' (ComputableInLogSpace.getElem?' hargs hf)
  have hwire := hbinary.toUnary_of_polyBounded (polyBounded_wire hC hn fun x => wire_getD_le ..)
  apply ComputableInLogSpace.unaryToBinary
  unfold blockWire
  exact ComputableInLogSpace.ite_decide (hf.unaryLt ha) (simulateWireNumber_fl hn hB hwire)
    (by fun_prop)

private theorem outWire_fl {C : (n : ℕ) → Circuit signature n 1}
    (hC : Circuit.IsLogspaceUniform encOp C) :
    ComputableInLogSpace (fun n => Circuit.simulateWireNumber n (blockLength (encodedLength (C n)))
      ((C n).outputs 0).toNat) encUnary encNat := by
  have h := (ComputableInLogSpace.snd _ _).comp' (code_fl hC)
  have ho : ComputableInLogSpace (fun n => ((C n).outputs 0).toNat) encUnary encNat :=
    ((ComputableInLogSpace.listHeadD 0).comp' h).congr_fun fun n => by
      simp [Circuit.code, List.ofFn_succ]
  apply ComputableInLogSpace.unaryToBinary
  apply simulateWireNumber_fl .id (blockLength_fl (encodedLength_fl hC))
  exact ho.toUnary_of_polyBounded (polyBounded_wire hC .id fun n => (Wire.toNat_lt _).le)

private theorem code_simulate_fanInBlock {n : ℕ} (c : Circuit signature n 1) :
    let k := encodedLength c
    let B := blockLength k
    (c.simulate (fanInBlock k)).code =
      (((List.range c.size).map fun i => (List.range B).map (gateEntry c i)).flatten,
        [Circuit.simulateWireNumber n B (c.outputs 0).toNat]) := by
  let k := encodedLength c
  let B := blockLength k
  have hB : 0 < B := Nat.zero_lt_succ _
  have hmax (i : Fin c.size) : max k (c.program.lines i).op.arity = k :=
    max_eq_left (arity_le_encodedLength c i)
  have hb (i : Fin c.size) := code_fanInBlock k (c.program.lines i).op
  simp only [hmax] at hb
  change (c.simulate (fanInBlock k)).code = _
  rw [Circuit.code_simulate_uniform _ _ hB]
  · apply Prod.ext
    · simp only [← List.flatMap_def, ← List.map_coe_finRange_eq_range (n := c.size),
        List.flatMap_map]
      apply List.flatMap_congr
      intro i _
      have hline : sourceLine c i = (c.program.lines i).code := c.program.getD_code i _
      have hrows := congrArg Prod.fst (hb i)
      change (fanInBlock k (c.program.lines i).op).program.code = _ at hrows
      rw [hrows, List.map_map]
      apply List.map_congr_left
      intro j _
      unfold gateEntry mapInputs blockWire
      simp only [Function.comp_apply, hline, Line.code_fst]
      rfl
    · simp [Circuit.code, List.ofFn_succ, B, k]
  · intro i
    refine ⟨?_, ?_⟩
    · rw [size_fanInBlock, hmax, Nat.mul_comm (k + 1)]
      rfl
    · have hout := congrArg Prod.snd (hb i)
      simp only [Circuit.code, List.ofFn_succ, List.ofFn_zero, List.cons.injEq,
        and_true] at hout
      change _ = (c.program.lines i).op.arity + B - 1
      change _ = (c.program.lines i).op.arity + (B - 1) at hout
      omega

/-- A deterministic logspace generator for the native circuit also generates its fan-in-two
compilation. The new generator enumerates gate blocks and writes their binary wire numbers. -/
theorem isLogspaceUniform_toFanInTwo {C : (n : ℕ) → Circuit signature n 1}
    (hC : Circuit.IsLogspaceUniform encOp C) :
    Circuit.IsLogspaceUniform Boolean.encOp (fun n => toFanInTwo (C n)) := by
  have hsize : ComputableInLogSpace (fun n => (C n).size) encUnary encUnary :=
    (ComputableInLogSpace.listLength.comp'
      ((ComputableInLogSpace.fst _ _).comp' (code_fl hC))).congr_fun
        fun n => (Circuit.length_code_fst _).symm
  have hB := blockLength_fl (encodedLength_fl hC)
  have hentry := gateEntry_fl hC
    ((ComputableInLogSpace.fst encUnary encUnary).comp' (ComputableInLogSpace.fst _ encUnary))
    ((ComputableInLogSpace.snd encUnary encUnary).comp' (ComputableInLogSpace.fst _ encUnary))
    (ComputableInLogSpace.snd _ encUnary)
  have hblock := ComputableInLogSpace.map_range (.pair .unary .unary)
    (hB.comp' (ComputableInLogSpace.fst encUnary encUnary)) hentry
  have hg := (ComputableInLogSpace.listFlatten _).comp'
    (ComputableInLogSpace.map_range .unary hsize hblock)
  have ho := ComputableInLogSpace.listSingleton.comp' (outWire_fl hC)
  have hwriter := ComputableInLogSpace.pair (ComputableInLogSpace.id (encIn := encUnary))
    (ComputableInLogSpace.pair hg ho)
  apply hwriter.congr
  intro n
  simp only [Circuit.encCircuit_apply, toFanInTwo, code_simulate_fanInBlock]

end Unbounded

/-- **Logspace-uniform ACⁱ ⊆ logspace-uniform NCⁱ⁺¹.** Counting the length of the generated input
circuit bounds every occurring gate arity, including repeated wires. Each replacement has
logarithmic depth, and a single logspace transducer tabulates every wire of the new circuit. -/
theorem logspaceUniformAC_subset_NC_succ (i : ℕ) :
    LogspaceUniformAC i ⊆ LogspaceUniformNC (i + 1) := by
  rintro L ⟨C, hC, c, h⟩
  obtain ⟨e, he⟩ := Unbounded.exists_depthBound hC
  refine ⟨_, Unbounded.isLogspaceUniform_toFanInTwo hC, e * c, fun n => ⟨?_, ?_⟩⟩
  · intro x
    rw [Unbounded.eval_toFanInTwo]
    exact (h n).1 x
  · calc
      _ ≤ _ := Unbounded.depth_toFanInTwo_le (C n)
      _ ≤ (e * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) :=
        Nat.mul_le_mul (he n) (h n).2
      _ = _ := by ring

end Cslib.Circuits.Boolean
