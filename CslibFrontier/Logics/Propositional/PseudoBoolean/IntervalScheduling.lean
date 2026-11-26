/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import Mathlib.Data.List.Sort

/-!
# Certified weighted interval scheduling: a dynamic program that writes a VeriPB proof

Weighted interval scheduling takes `n` half-open intervals `[a i, f i)` with values `v i`, and asks
for the largest value `∑ i ∈ S, v i` of a set `S : Finset (Fin n)` of pairwise disjoint intervals:
`min (f i) (f j) ≤ max (a i) (a j)` for distinct `i, j ∈ S`. This file writes it as a
pseudo-Boolean problem and gives a dynamic program that writes, with its answer, a proof in the
kernel format of VeriPB that the answer is optimal, after §3.2 of [Demirović, McCreesh, McIlree,
Nordström, Oertel and Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024] and the
interval-scheduling solver of its supplement. The proof is checked by
`Cslib.Logic.PL.VeriPB.checkRed`; nothing about the dynamic program is proved.

**The encoding.** Interval `i` is the variable `i`. A set of pairwise disjoint intervals is a
clique of the *compatibility graph* `Cslib.Logic.PL.VeriPB.IntervalScheduling.compat a f`, in which
distinct intervals are adjacent when they are disjoint, so the formula is the clique encoding of
that graph, `Cslib.Logic.PL.VeriPB.Graph.cliqueConstraints`: the clause `¬xᵢ ∨ ¬xⱼ` for each pair
`i < j` of overlapping intervals. The objective, to be minimized, is the negated value
`Cslib.Logic.PL.VeriPB.negProfit v`. The formula and objective encode the problem
(`Cslib.Logic.PL.VeriPB.IntervalScheduling.encodes`), so an accepted proof with the conclusion
`BOUNDS lb : q lb` certifies the optimum `-lb`
(`Cslib.Logic.PL.VeriPB.Encodes.isGreatest_of_checkRed`).

**The dynamic program** (`Cslib.Logic.PL.VeriPB.IntervalScheduling.certify`). It orders the
intervals by finishing time, empty intervals first, as `i₁, …, iₙ`, and computes the optimum `O_k`
of the first `k` of them: `O_k` is the larger of `O_{k-1}`, without `i_k`, and `O_p + v_{i_k}`,
with it, where `i_{p+1}, …, i_{k-1}` are the intervals before `i_k`, counted back from it, that
overlap it. The states are a simple sum, as the paper says: for each `k` the proof reifies, by
`Cslib.Logic.PL.VeriPB.reify`, the variable `P_k ⇔ ∑_{j ≤ k} v_{i_j} x_{i_j} ≤ O_k`, and derives
`P_k` as a unit:
* `P_{k-1} ∧ ¬x_{i_k} ⇒ P_k`, by adding the forward half of `P_{k-1}` to the backward half of
  `P_k`;
* `P_p ∧ x_{i_k} ⇒ P_k`, by adding the forward half of `P_p`, the backward half of `P_k` and the
  clauses `¬x_{i_j} ∨ ¬x_{i_k}` for `p < j < k`, each times `v_{i_j}`;
* `P_k` by RUP from these and the units `P_{k-1}` and `P_p`, after which the two sums are deleted.

The proof logs an optimal selection with `soli`, which adds the improving constraint
`∑ vᵢ xᵢ ≥ O_n + 1`; the forward half of `P_n` plus that constraint is refuted by `P_n`. The
conclusion is `BOUNDS -O_n : q -O_n`. The order is not trusted: in another order the derivations
fail, and the checker rejects the proof. That the checker accepts it is not proved, nor that the
claimed optimum is right; the theorem
`Cslib.Logic.PL.VeriPB.IntervalScheduling.isGreatest_of_checkRed_certify` turns acceptance into
optimality.

## Main definitions

* `Cslib.Logic.PL.VeriPB.IntervalScheduling.compat`: the compatibility graph of the intervals.
* `Cslib.Logic.PL.VeriPB.IntervalScheduling.certify`: the proof-logging dynamic program.

## Main results

* `Cslib.Logic.PL.VeriPB.IntervalScheduling.encodes`: the encoding is correct.
* `Cslib.Logic.PL.VeriPB.IntervalScheduling.isGreatest_of_checkRed_certify`: if the checker
  accepts the proof of the dynamic program, its answer is the optimum.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB.IntervalScheduling

open Graph

variable {n : ℕ}

/-! ### The encoding -/

/-- **The compatibility graph** of the intervals `[a i, f i)`: distinct intervals are adjacent when
they are disjoint, `min (f i) (f j) ≤ max (a i) (a j)`. -/
@[expose]
def compat (a f : Fin n → ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ min (f i) (f j) ≤ max (a i) (a j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [min_comm, max_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (a f : Fin n → ℕ) : DecidableRel (compat a f).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- **The interval scheduling encoding is correct**: the clique encoding of the compatibility
graph and the negated value encode the maximization of the value over the sets of pairwise
disjoint intervals. -/
theorem encodes (a f v : Fin n → ℕ) :
    Encodes (cliqueConstraints (compat a f)) (negProfit v)
      {S : Finset (Fin n) | (S : Set (Fin n)).Pairwise fun i j => min (f i) (f j) ≤ max (a i) (a j)}
      fun S => ∑ i ∈ S, (v i : ℤ) :=
  encodes_negProfit v fun σ => by
    rw [forall_holds_cliqueConstraints_iff]
    exact ⟨fun h _ hi _ hj hij => (h hi hj hij).2, fun h _ hi _ hj hij => ⟨hij, h hi hj hij⟩⟩

/-! ### The proof-logging dynamic program -/

/-- The intervals `i` and `j` overlap. -/
private def overlaps (a f : Fin n → ℕ) (i j : Fin n) : Bool :=
  decide (max (a i) (a j) < min (f i) (f j))

/-- The order of the dynamic program: by finishing time, empty intervals first. -/
private def order (a f : Fin n → ℕ) : List (Fin n) :=
  let key := fun i : Fin n => if a i < f i then f i else 0
  (List.finRange n).insertionSort fun i j => key i ≤ key j

/-- A prefix of the order: its optimum, an optimal selection, and the numbers of the forward and
backward halves of its reified bound `P` and of the unit `P`. -/
private structure Pref where
  opt : ℕ
  sel : List ℕ
  fwd : ℕ
  bwd : ℕ
  unit : ℕ

/-- A placeholder prefix, never reached. -/
private def noPref : Pref := ⟨0, [], 0, 0, 0⟩

/-- The bound `∑ vᵢ xᵢ ≤ O` on the intervals `is`, as `∑ vᵢ ¬xᵢ ≥ ∑ vᵢ - O`, without zero
coefficients. -/
private def bound (v : Fin n → ℕ) (is : List (Fin n)) (O : ℕ) : PBConstr :=
  ⟨(is.filter (v · ≠ 0)).map fun i => (v i, (i.val, false)), (is.map v).sum - O⟩

/-- The number of the clause `¬xᵢ ∨ ¬xⱼ` in the formula `F`. -/
private def clauseId (F : List PBConstr) (i j : Fin n) : ℕ :=
  F.idxOf ⟨[(1, ((min i j).val, false)), (1, ((max i j).val, false))], 1⟩ + 1

/-- One step of the dynamic program, for the next interval `i` of the order `ord`: reify the bound
of the prefix ending at `i` and derive it as a unit. -/
private def step (a f v : Fin n → ℕ) (F : List PBConstr) (ord : List (Fin n))
    (X : ProofLog × List Pref) (i : Fin n) : ProofLog × List Pref :=
  let (e, Ps) := X
  let k := Ps.length
  let prev := Ps.getLastD noPref
  -- The intervals before `i`, counted back from it, that overlap it.
  let over := ((ord.take (k - 1)).reverse.takeWhile (overlaps a f i)).reverse
  let pp := Ps.getD (k - 1 - over.length) noPref
  let (O, sel) := if prev.opt < pp.opt + v i then (pp.opt + v i, i.val :: pp.sel)
    else (prev.opt, prev.sel)
  let (e, z, fw, bw) := e.reify (bound v (ord.take k) O)
  let (e, t₀) := e.pol [.id prev.fwd, .id bw, .add]
  let (e, t₁) := e.pol ([.id pp.fwd, .id bw, .add] ++
    (over.filter (v · ≠ 0)).flatMap fun j => [.id (clauseId F j i), .mul (v j), .add])
  let (e, u) := e.rup (Clause.toPB [(z, true)]) [.neg, .id prev.unit, .id t₀, .id pp.unit, .id t₁]
  (e.deld [t₀, t₁], Ps ++ [⟨O, sel, fw, bw, u⟩])

/-- **The proof-logging dynamic program** for the intervals `[a i, f i)` of values `v`. It returns a
claimed optimum and a candidate VeriPB proof with the conclusion `BOUNDS -optimum : q -optimum` for
the clique encoding of the compatibility graph and the negated value. No theorem says that the
checker accepts the proof or that the claimed optimum is right; when
`Cslib.Logic.PL.VeriPB.checkRed` accepts the proof on an instance, the claimed optimum is the
optimum there (`Cslib.Logic.PL.VeriPB.IntervalScheduling.isGreatest_of_checkRed_certify`). -/
def certify (a f v : Fin n → ℕ) : Certificate ℕ :=
  let F := cliqueConstraints (compat a f)
  let ord := order a f
  -- The solution is logged first, so its improving constraint is `F.length + 1`.
  let (e, z, fw, bw) := ProofLog.reify ⟨[], F.length + 2, n⟩ (bound v [] 0)
  let (e, u) := e.rup (Clause.toPB [(z, true)]) [.neg, .id bw]
  let (e, Ps) := ord.foldl (step a f v F ord) (e, [⟨0, [], fw, bw, u⟩])
  let last := Ps.getLastD noPref
  let (e, r) := e.pol [.id last.fwd, .id (F.length + 1), .add]
  let (e, q) := e.rup ⟨[], 1⟩ [.id last.unit, .id r]
  ⟨last.opt, e.proof [.soli ((List.finRange n).map fun i => (i.val, decide (i.val ∈ last.sel)))]
    (.bounds (some (-last.opt)) q (some (-last.opt)) none)⟩

/-- **If the checker accepts the proof of the dynamic program, its answer is the optimum**: the
largest value of a set of pairwise disjoint intervals. -/
theorem isGreatest_of_checkRed_certify {a f v : Fin n → ℕ}
    (h : checkRed (cliqueConstraints (compat a f)) (some (negProfit v)) (certify a f v).proof =
      true) :
    IsGreatest ((fun S : Finset (Fin n) => ∑ i ∈ S, v i) ''
      {S : Finset (Fin n) |
        (S : Set (Fin n)).Pairwise fun i j => min (f i) (f j) ≤ max (a i) (a j)})
      (certify a f v).optimum :=
  (encodes a f v).isGreatest_natCast_of_checkRed (fun _ => by push_cast; rfl) h rfl

end Cslib.Logic.PL.VeriPB.IntervalScheduling

end
