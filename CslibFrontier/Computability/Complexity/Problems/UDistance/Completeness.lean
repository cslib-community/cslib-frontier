/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.UDistance
public import CslibFrontier.Computability.Complexity.Problems.BoundedSTCON.Membership
import CslibFrontier.Computability.Complexity.Problems.STCON.Writer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Boolean
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-!
# Distances in undirected graphs are NL-complete

Exercise 5.24 of Goldreich's January 2007 draft (printed p. 198, PDF p. 82) asks to prove that
deciding whether an undirected graph has a path of length at most `K` between two designated
vertices (`Cslib.Complexity.UDistanceAtMost`), respectively whether their distance is exactly `K`
(`Cslib.Complexity.UDistanceEq`), is `NL`-complete under logarithmic-space many-one reductions.
The first is the literal question. The second is the shortest-distance reading of "a path of length
exactly `K`" (the distance is `K`), which the exercise's title and `NL = coNL` guideline support;
the literal simple-path question differs (see `Cslib.Complexity.UDistanceEq`).

Both are proved here for the native classes: `NL` is decided by one finite-state
nondeterministic machine within visited work space `c * (Nat.log2 n + 1)`, and reductions are
computed by deterministic machines within such space.

* **Membership, at most `K`** (`Cslib.Complexity.UDistanceAtMost.mem_NL`): the encoding of an
  instance is that of bounded directed connectivity on its directed graph, so Exercise 5.19
  (`Cslib.Complexity.BoundedSTCON.mem_NL`) applies through the identity on words.
* **Membership, exactly `K`** (`Cslib.Complexity.UDistanceEq.mem_NL`): the distance is `K` when it
  is at most `K` and not less than `K`. "Less than `K`" reduces to bounded directed connectivity
  by a new target after `t` (`Cslib.Complexity.STCONInstance.pendant`), so its complement is in
  `NL` by `NL = coNL` (`Cslib.Complexity.compl_mem_NL`), as the guideline says, and `NL` is closed
  under intersection (`Cslib.Complexity.inter_mem_NL`).
* **Hardness** (`Cslib.Complexity.UDistanceAtMost.logSpaceHard`,
  `Cslib.Complexity.UDistanceEq.logSpaceHard`): directed connectivity reduces to both through the
  guideline's layered graph (`Cslib.Complexity.STCONInstance.distanceInstance`), which is the
  undirected graph of the layered graph of Exercise 5.19 with bound `n`.

The writers of the pendant and of the undirected graph are instances of a generic counter
program (`Cslib.Complexity.STCONInstance.computableInLogSpace_of_entryExprs`); the number of
vertices is read by a finite-state transducer.

## Main results

* `Cslib.Complexity.UDistanceAtMost.logSpaceComplete`: distance at most `K` is `NL`-complete.
* `Cslib.Complexity.UDistanceEq.logSpaceComplete`: distance exactly `K` is `NL`-complete.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, January 2007 draft,
  Exercise 5.24][Goldreich2007DraftR2]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.CounterProgram.Expr

/-! ### Logarithmic-space maps -/

namespace STCONInstance

/-- The pendant instance is computed in logarithmic space. -/
theorem computableInLogSpace_pendant : ComputableInLogSpace pendant encSTCON encSTCON := by
  refine computableInLogSpace_of_entryExprs (numV := add (reg 0) (const 1)) (src := reg 1)
    (tgt := reg 0) (guard₁ := andB (ltB (reg 3) (reg 0)) (ltB (reg 4) (reg 0)))
    (pos₁ := add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3))
      (add (mul (reg 3) (reg 0)) (reg 4)))
    (guard₂ := const 0) (pos₂ := const 0)
    (test := andB (eqB (reg 3) (reg 2)) (eqB (reg 4) (reg 0))) 1
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun I => by have := I.length_encode; simp only [pendant, pow_one]; omega) fun I r c => ?_
  have ht := I.t.isLt
  simp only [entryOf, andB, eval_mul, eval_ltB, eval_eqB, eval_reg, eval_const, eval_add,
    List.getD_cons_zero, List.getD_cons_succ, lt_irrefl, decide_false, Bool.false_and,
    Bool.or_false]
  by_cases h : (r : ℕ) < I.n ∧ (c : ℕ) < I.n
  · rw [I.getElem?_encode_matrix h.1 h.2]
    simp [pendant, h, show (c : ℕ) ≠ I.n by omega]
  · simp only [pendant, h, ↓reduceDIte]
    have hc' : (c : ℕ) < I.n + 1 := c.isLt
    by_cases hc : (c : ℕ) < I.n
    · have hr : ¬(r : ℕ) < I.n := fun hr => h ⟨hr, hc⟩
      have hrt : (r : ℕ) ≠ I.t := by omega
      simp [hr, hrt]
    · by_cases hr : (r : ℕ) = I.t <;> simp [hr, show (c : ℕ) = I.n by omega]

/-- The undirected graph of an instance is computed in logarithmic space. -/
theorem computableInLogSpace_undirected : ComputableInLogSpace undirected encSTCON encUSTCON := by
  have h := computableInLogSpace_of_entryExprs (F := fun I => I.undirected.toSTCONInstance)
    (numV := reg 0) (src := reg 1) (tgt := reg 2)
    (guard₁ := add (sub (reg 3) (reg 4)) (sub (reg 4) (reg 3)))
    (pos₁ := add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3))
      (add (mul (reg 3) (reg 0)) (reg 4)))
    (guard₂ := add (sub (reg 3) (reg 4)) (sub (reg 4) (reg 3)))
    (pos₂ := add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3))
      (add (mul (reg 4) (reg 0)) (reg 3)))
    (test := const 0) 1
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun I => by have := I.length_encode; simp only [undirected, pow_one]
                 change I.n ≤ I.encode.length + 1; omega) fun I r c => ?_
  · exact h.congr fun _ => rfl
  · obtain ⟨r, hr⟩ := r
    obtain ⟨c, hc⟩ := c
    change r < I.n at hr
    change c < I.n at hc
    refine (I.undirected_adj ⟨r, hr⟩ ⟨c, hc⟩).trans ?_
    simp only [entryOf, eval_add, eval_sub, eval_mul, eval_reg, eval_const,
      List.getD_cons_zero, List.getD_cons_succ, lt_irrefl, decide_false, Bool.or_false]
    rw [I.getElem?_encode_matrix hr hc, I.getElem?_encode_matrix hc hr]
    by_cases hrc : r = c
    · subst hrc
      simp
    · have hpos : 0 < r - c + (c - r) := by omega
      simp [hpos, hrc]

/-- Reads the unary header `1^n` of an encoded instance: `true` while in the header. -/
private def headerT : Transducer Bool Bool where
  q₀ := true
  step q b := (q && b, if q && b then [true] else [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

private theorem headerT_run_false (w : List Bool) : headerT.run false w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [headerT] using ih

private theorem headerT_run (m : ℕ) (w : List Bool) :
    headerT.run true (List.replicate m true ++ false :: w) = List.replicate m true := by
  induction m with
  | zero => simpa [headerT] using headerT_run_false w
  | succ m ih => simpa [headerT, List.replicate_succ] using ih

/-- The number of vertices of an encoded instance is computed in logarithmic space, in binary. -/
theorem computableInLogSpace_n : ComputableInLogSpace STCONInstance.n encSTCON encNat :=
  ComputableInLogSpace.unaryToBinary <| headerT.computableInLogSpace fun I => by
    rw [encUnary_apply, encSTCON_apply, encode]
    exact (headerT_run _ _).symm

/-- **The layered hardness instance is computed in logarithmic space.** -/
theorem computableInLogSpace_distanceInstance :
    ComputableInLogSpace distanceInstance encSTCON encUDistance := by
  have hB : ComputableInLogSpace (fun J : STCONInstance => (⟨J, J.n⟩ : BoundedSTCONInstance))
      encSTCON encBoundedSTCON :=
    (ComputableInLogSpace.pair ComputableInLogSpace.id computableInLogSpace_n).congr fun _ => rfl
  have hU := computableInLogSpace_undirected.comp
    (BoundedSTCONInstance.computableInLogSpace_layered.comp hB)
  exact (ComputableInLogSpace.pair hU computableInLogSpace_n).congr fun _ => rfl

end STCONInstance

namespace UDistanceInstance

/-- The pendant bounded instance is computed in logarithmic space. -/
theorem computableInLogSpace_strict : ComputableInLogSpace strict encUDistance encBoundedSTCON := by
  have hp : ComputableInLogSpace (fun I : UDistanceInstance => (I.graph.toSTCONInstance, I.bound))
      encUDistance (encPair encSTCON encNat) :=
    ComputableInLogSpace.of_eq fun I => (encUDistance_eq_encPair I).symm
  exact (ComputableInLogSpace.pair
    (STCONInstance.computableInLogSpace_pendant.comp ((ComputableInLogSpace.fst _ _).comp hp))
    ((ComputableInLogSpace.snd _ _).comp hp)).congr fun _ => rfl

end UDistanceInstance

/-! ### Distance at most `K` -/

namespace UDistanceAtMost

/-- Distance at most `K` reduces to bounded directed connectivity by the identity on words. -/
theorem logSpaceReducible_BoundedSTCON :
    LogSpaceReducible encUDistance encBoundedSTCON UDistanceAtMost BoundedSTCON :=
  ⟨UDistanceInstance.toBoundedSTCON,
    ComputableInLogSpace.of_eq UDistanceInstance.encBoundedSTCON_toBoundedSTCON,
    fun I => I.toBoundedSTCON_mem_iff.symm⟩

/-- **Distance at most `K` in undirected graphs is in `NL`.** -/
theorem mem_NL : UDistanceAtMost ∈ NL encUDistance :=
  logSpaceReducible_BoundedSTCON.mem_NL BoundedSTCON.mem_NL

/-- Directed connectivity reduces to distance at most `K` through the layered graph. -/
theorem logSpaceReducible_STCON :
    LogSpaceReducible encSTCON encUDistance STCON UDistanceAtMost :=
  ⟨STCONInstance.distanceInstance, STCONInstance.computableInLogSpace_distanceInstance,
    fun J => J.distanceInstance_mem_UDistanceAtMost_iff.symm⟩

/-- **Distance at most `K` in undirected graphs is `NL`-hard** under logspace many-one
reductions. -/
theorem logSpaceHard : LogSpaceHard NL encUDistance UDistanceAtMost :=
  fun _ _ _ hA => (STCON.logSpaceReducible_of_mem_NL hA).trans logSpaceReducible_STCON

/-- **Distance at most `K` in undirected graphs is `NL`-complete** under logspace many-one
reductions (Goldreich's January 2007 draft, Exercise 5.24, "at most"). -/
theorem logSpaceComplete : LogSpaceComplete NL encUDistance UDistanceAtMost :=
  ⟨mem_NL, logSpaceHard⟩

end UDistanceAtMost

/-! ### Distance exactly `K` -/

namespace UDistanceEq

/-- **Distance exactly `K` in undirected graphs is in `NL`**, by `NL = coNL`. -/
theorem mem_NL : UDistanceEq ∈ NL encUDistance := by
  have hle : {I : UDistanceInstance | I.toBoundedSTCON ∈ BoundedSTCON} ∈ NL encUDistance :=
    LogSpaceReducible.mem_NL ⟨_, ComputableInLogSpace.of_eq
      UDistanceInstance.encBoundedSTCON_toBoundedSTCON, fun _ => Iff.rfl⟩ BoundedSTCON.mem_NL
  have hlt : {I : UDistanceInstance | I.strict ∈ BoundedSTCON} ∈ NL encUDistance :=
    LogSpaceReducible.mem_NL ⟨_, UDistanceInstance.computableInLogSpace_strict, fun _ => Iff.rfl⟩
      BoundedSTCON.mem_NL
  convert inter_mem_NL hle (compl_mem_NL hlt) using 1
  ext I
  exact I.mem_UDistanceEq_iff

/-- Directed connectivity reduces to distance exactly `K` through the layered graph. -/
theorem logSpaceReducible_STCON : LogSpaceReducible encSTCON encUDistance STCON UDistanceEq :=
  ⟨STCONInstance.distanceInstance, STCONInstance.computableInLogSpace_distanceInstance,
    fun J => J.distanceInstance_mem_UDistanceEq_iff.symm⟩

/-- **Distance exactly `K` in undirected graphs is `NL`-hard** under logspace many-one
reductions. -/
theorem logSpaceHard : LogSpaceHard NL encUDistance UDistanceEq :=
  fun _ _ _ hA => (STCON.logSpaceReducible_of_mem_NL hA).trans logSpaceReducible_STCON

/-- **Distance exactly `K` in undirected graphs is `NL`-complete** under logspace many-one
reductions: the shortest-distance reading of Goldreich's January 2007 draft, Exercise 5.24,
"exactly", not the literal simple-path question. -/
theorem logSpaceComplete : LogSpaceComplete NL encUDistance UDistanceEq :=
  ⟨mem_NL, logSpaceHard⟩

end UDistanceEq

end Cslib.Complexity
