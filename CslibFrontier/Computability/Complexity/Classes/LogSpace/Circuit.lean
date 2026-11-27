/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
import CslibFrontier.Computability.Complexity.Problems.STCON.Reduction
import CslibFrontier.Computability.Circuit.Boolean.AltFormula
import CslibFrontier.Computability.Circuit.Boolean.RepeatedSquaring
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Simps
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Circuits for nondeterministic logarithmic space

Each entry of a machine's configuration graph at a fixed input length depends on at most one
input bit. A first circuit supplies positive and negative literals and both constants to the
reflexive adjacency matrix. Repeated Boolean matrix squaring then computes reachability of the
accepting sink. The graph has polynomially many vertices, so its closure needs logarithmically
many squarings. This implements the Boolean matrix-powering argument of [Arora and Barak,
Chapter 6, Exercise 9(b–c), 2007 draft][AroraBarak07].

## Main results

* `Cslib.Complexity.exists_mem_AC_one_of_mem_NL` constructs a nonuniform AC¹ language agreeing
  with the given problem on every encoded instance, for arbitrary injective encodings.
* `Cslib.Complexity.NL_subset_AC_one` gives the nonuniform class containment for bit languages.
  Composing with `Cslib.Circuits.Boolean.AC_subset_NC_succ` at exponent one gives NC².

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, 2007 web draft,
  Chapter 6, Exercise 9(b–c)][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean
open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

private def symbolWire {n : ℕ} (i : ℕ) (f : Option Bool → Bool) : Fin (n + n) ⊕ Bool :=
  if h : i < n then
    match f (some false), f (some true) with
    | false, false => .inr false
    | true, true => .inr true
    | false, true => .inl (Fin.castAdd n ⟨i, h⟩)
    | true, false => .inl (Fin.natAdd n ⟨i, h⟩)
  else .inr (f none)

private theorem eval_symbolWire (w : List Bool) (i : ℕ) (f : Option Bool → Bool) :
    (symbolWire i f).elim (AltFormula.literals w.get) id = f w[i]? := by
  by_cases hi : i < w.length
  · rw [List.getElem?_eq_getElem hi]
    cases hf : f (some false) <;> cases ht : f (some true) <;> cases hx : w[i] <;>
      simp only [symbolWire, dite_eq_left hi, hf, ht, Sum.elim_inl, Sum.elim_inr, id_eq,
        AltFormula.literals, Fin.append_left, Fin.append_right, List.get_eq_getElem, hx,
        Bool.not_false, Bool.not_true]
  · simp [symbolWire, hi]

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

private abbrev vertices (k D n : ℕ) := vertexBound (k := k) (radix D n) + 1

private noncomputable def adjacencyWire (D n : ℕ) (ij : Fin (vertices k D n * vertices k D n)) :
    Fin (n + n) ⊕ Bool :=
  let (u, v) := finProdFinEquiv.symm ij
  if u = v then .inr true
  else if v.val < vertexBound (k := k) (radix D n) then
    symbolWire (queryIndex (k := k) (radix D n) u) (edgeWithSymbol ntm (radix D n) n u v)
  else .inr (bad (k := k) (State := State) (radix D n) n u)

private theorem eval_adjacencyWire (w : List Bool)
    (u v : Fin (vertices k (radixExponent State c) w.length)) :
    substitute (adjacencyWire ntm (radixExponent State c) w.length) (AltFormula.literals w.get)
      (finProdFinEquiv (u, v)) = true ↔
      Relation.ReflGen (STCON.configurationInstance ntm c w).Adj u v := by
  change _ ↔ Relation.ReflGen (fun a b : Fin (vertices k (radixExponent State c) w.length) =>
    STCON.sinkAdj ntm (radixExponent State c) w a b = true) u v
  simp only [substitute, adjacencyWire, Equiv.symm_apply_apply, Relation.reflGen_iff]
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, Ne.symm huv, ↓reduceIte, false_or, STCON.sinkAdj]
    split <;> simp [eval_symbolWire]

private noncomputable def acceptanceCircuit (n : ℕ) : Circuit Unbounded.signature n 1 :=
  let D := radixExponent State c
  let N := vertices k D n
  let start : Fin N := ⟨startID ntm (radix D n),
    (STCON.startID_lt_vertexBound ntm c n).trans (Nat.lt_succ_self _)⟩
  let target : Fin N := Fin.last _
  let inputs := ((substituteCircuit (adjacencyWire ntm D n)).mapOp
    Unbounded.deMorganToUnbounded).comp (AltFormula.literalsCircuit n)
  (Circuit.wiring _ (fun _ : Fin 1 => finProdFinEquiv (start, target))).comp
    (((squareCircuit N).iterate (Nat.clog 2 N)).comp inputs)

private theorem eval_acceptanceCircuit (w : List Bool) :
    (acceptanceCircuit ntm c w.length).eval Unbounded.interpretation w.get 0 = true ↔
      STCON.configurationInstance ntm c w ∈ STCON := by
  simp only [acceptanceCircuit, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply,
    Circuit.eval_mapOp (I := Boolean.interpretation), eval_substituteCircuit,
    AltFormula.eval_literalsCircuit, mem_STCON]
  exact (eval_iterate_squareCircuit_iff_reflTransGen (eval_adjacencyWire ntm c w)
    (fun _ => .refl) (Nat.le_pow_clog (by decide : 1 < 2) _) _ _).trans (by
      let I := STCON.configurationInstance ntm c w
      change Relation.ReflTransGen (Relation.ReflGen I.Adj) I.s I.t ↔ _
      rw [Relation.reflTransGen_reflGen])

private theorem depth_acceptanceCircuit_le (n : ℕ) :
    (acceptanceCircuit ntm c n).depth ≤
      2 + Nat.clog 2 (vertices k (radixExponent State c) n) * 2 := by
  circuit_bound [acceptanceCircuit]

private theorem size_acceptanceCircuit (n : ℕ) :
    let N := vertices k (radixExponent State c) n
    (acceptanceCircuit ntm c n).size = n + 2 + Nat.clog 2 N * (N ^ 2 * (N + 1)) := by
  simp only [acceptanceCircuit, Circuit.size_comp, Circuit.size_wiring, Circuit.size_iterate,
    size_squareCircuit, Circuit.size_mapOp, size_substituteCircuit, AltFormula.size_literalsCircuit]
  omega

/-- Every problem in nondeterministic logarithmic space has polynomial-size, logarithmic-depth
unbounded fan-in circuits on its encoded inputs. The circuit family defines a total bit language
even when the machine's space bound is guaranteed only on encoded instances. -/
theorem exists_mem_AC_one_of_mem_NL {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (h : A ∈ NL enc) : ∃ L ∈ AC 1, ∀ a, a ∈ A ↔ enc a ∈ L := by
  classical
  obtain ⟨k, State, _, ntm, c, h⟩ := h
  let := Fintype.ofFinite State
  let N := vertices k (radixExponent State c)
  have hN : PolynomiallyBounded N := by
    change PolynomiallyBounded (fun n => vertexBound (k := k) (radix (radixExponent State c) n) + 1)
    simp_rw [vertexBound_eq_pow]
    fun_prop
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log hN
  let f (n : ℕ) (x : BitString n) := (acceptanceCircuit ntm c n).eval Unbounded.interpretation x 0
  refine ⟨Language.ofSlices f, ⟨2 * e + 2, fun n => n + 2 + N n * (N n ^ 2 * (N n + 1)),
    by fun_prop, fun n => ?_⟩, fun a => ?_⟩
  · refine ⟨acceptanceCircuit ntm c n, fun x => ?_, ?_, ?_⟩
    · ext j
      fin_cases j
      simp [single, f]
    · calc
        _ ≤ 2 + Nat.clog 2 (N n) * 2 := depth_acceptanceCircuit_le ntm c n
        _ ≤ (2 * e + 2) * (Nat.log 2 n + 1) ^ 1 := by nlinarith [he n]
    · have hb : Nat.clog 2 (N n) ≤ N n :=
        Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
      exact (size_acceptanceCircuit ntm c n).le.trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right (N n ^ 2 * (N n + 1)) hb) (n + 2))
  · exact (h.1 a).2.trans ((STCON.configurationInstance_mem_iff ntm c (h.1 a).1).symm.trans
      (eval_acceptanceCircuit ntm c (enc a)).symm)

/-- **NL ⊆ nonuniform AC¹** for bit languages, with polynomial size and logarithmic depth in the
unbounded fan-in basis. -/
theorem NL_subset_AC_one : NL _root_.Turing.MultiTapeTM.encBits ⊆ AC 1 := by
  intro A hA
  obtain ⟨L, hL, h⟩ := exists_mem_AC_one_of_mem_NL hA
  exact (Set.ext h) ▸ hL

end Cslib.Complexity
