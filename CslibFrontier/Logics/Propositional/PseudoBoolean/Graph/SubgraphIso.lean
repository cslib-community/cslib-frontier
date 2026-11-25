/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Lad
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public import Mathlib.Combinatorics.SimpleGraph.Copy
import CslibFrontier.Foundations.Data.List.Append
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
-- `import all`: `name_isoNames_isoVar` and `isoNames_covers` unfold the unexposed bodies of
-- `Names.name`, `Names.nameChars`, `Names.next`, `isNameChar` and `isOPBName`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! # Subgraph isomorphism as a pseudo-Boolean satisfaction problem, end to end

CakePB's encoding of (non-induced) subgraph isomorphism [Gocht, McCreesh, Myreen, Nordström,
Oertel and Tan][GochtMcCreeshMyreenNordstromOertelTan2024] (`subgraph_isoScript.sml`, CakeML
commit `14856fcf`, `examples/pseudo_bool/graph_encoding/`), with its correctness theorem, and the
end-to-end theorems that turn a VeriPB proof of `SAT` or `UNSAT` accepted by the verified checker
into a statement about the graphs.

**The problem.** CakePB's `has_subgraph_iso` asks for an injective map from the vertices of the
pattern `P` to those of the target `T` that sends edges to edges; non-edges may go to edges. That
is a copy of `P` in `T` in Mathlib's sense, `SimpleGraph.Copy P T` (an injective homomorphism),
and the problem asks whether `P.IsContained T` (`P ⊑ T`). Mathlib's `P ↪g T` is the induced
notion, which also reflects adjacency; it is not the one CakePB encodes.

**The encoding** (`Cslib.Logic.PL.VeriPB.Graph.isoConstraints`, CakePB's `encode`) of a pattern
on `Fin p` and a target on `Fin t` has the variable `xₐᵤ = Cslib.Logic.PL.VeriPB.Graph.isoVar t a u`
(`a` is mapped to `u`) for each pattern vertex `a` and target vertex `u`, named `xa_u` in OPB text
as by CakePB (`Cslib.Logic.PL.VeriPB.Graph.isoNames`), and in CakePB's order:
* `∑ᵤ xₐᵤ ≥ 1` for each `a` (`has_mapping_al1`), then `∑ᵤ ~xₐᵤ ≥ t - 1`, that is `∑ᵤ xₐᵤ ≤ 1`, for
  each `a` (`has_mapping_am1`);
* `∑ₐ ~xₐᵤ ≥ p - 1`, that is `∑ₐ xₐᵤ ≤ 1`, for each `u` (`one_one`);
* `~xₐᵤ + ∑_{v ~ u} x_{bv} ≥ 1` for each `u`, each `a` and each neighbour `b` of `a`, in that order,
  the neighbours in increasing order (`edge_map`): if `a` goes to `u`, then `b` goes to a neighbour
  of `u`.

CakePB writes the per-pattern at-most-one constraints (`has_mapping_am1`) as `∑ᵤ xₐᵤ ≤ 1`; here
they are written in the `≥` form that CakePB's normalization gives them, the constraints of the
checker being `≥` constraints. CakePB already writes the per-target constraints (`one_one`) in the
`≥` form with negated literals, as here. An at-most-one constraint with no literal has degree `0`
here where CakePB's is negative: with `p = 0`, `one_one` is `≥ -1` in CakePB, and with `t = 0`,
`has_mapping_am1` is `≤ 1`, that is `≥ -1`. Both forms are trivial, and the constraints keep
CakePB's IDs. With `t = 0` the at-least-one constraint `has_mapping_al1` has no literal either; it
is `0 ≥ 1`, of degree `1` in both, and contradicts any pattern vertex.

**Correctness** (CakePB's `encode_correct`). An assignment satisfies the constraints exactly when
it is the graph of a copy of `P` in `T`
(`Cslib.Logic.PL.VeriPB.Graph.forall_holds_isoConstraints_iff`), so the constraints are
satisfiable exactly when `P ⊑ T` (`Cslib.Logic.PL.VeriPB.Graph.exists_holds_isoConstraints_iff`).

**End to end** (CakePB's `full_encode_sem_concl`). The encoding is printed as OPB text
(`Cslib.Logic.PL.VeriPB.Text.printOPB`) with CakePB's variable names, and the proof is checked
against that text by `Cslib.Logic.PL.VeriPB.Text.checkOPBOutput`; the round trip of the printer
carries the conclusion back to the encoding built in Lean. The text differs from `cake_pb_iso`'s
only in its constraint labels, which it does not print, and in the form of the at-most-one rows
above, so the constraint numbers and the variable names of a kernel proof for CakePB's encoding
are those of this one: a proof of the Glasgow Subgraph Solver, elaborated by VeriPB against
`cake_pb_iso`'s text, is checked here unchanged. No theorem relates this checker to CakePB's;
their agreement was checked on the fixtures of the tests.
A conclusion `SAT` gives `true` and `UNSAT` gives `false`; other conclusions give nothing.
* `Cslib.Logic.PL.VeriPB.Graph.isContained_iff_of_checkSubgraphIsoGraph`: if
  `Cslib.Logic.PL.VeriPB.Graph.checkSubgraphIsoGraph P T pbp = some b`, then `P ⊑ T ↔ b = true`.
* `Cslib.Logic.PL.VeriPB.Graph.isContained_iff_of_checkSubgraphIso` is the same for the checker
  `Cslib.Logic.PL.VeriPB.Graph.checkSubgraphIso`, which takes the pattern and the target as LAD
  text (`Cslib.Logic.PL.VeriPB.Graph.parseLAD`): if it returns `b`, both texts parse, and the
  pattern read is contained in the target read exactly when `b = true`.

The second is the pure functional specification of CakePB's `cake_pb_iso`, its
`check_unsat_3_sem` (`examples/pseudo_bool/array/subgraph_isoProgScript.sml`), with `SAT` and
`UNSAT` for the strings `s VERIFIED SUBGRAPH ISOMORPHIC` and `s VERIFIED NOT SUBGRAPH ISOMORPHIC`.
It is not CakePB's `main_semantics`, a theorem about the compiled x64 machine code, its file and
command-line I/O and its output, which nothing here covers.

The trusted base is the LAD reader, the definitions of `SimpleGraph`, `SimpleGraph.Copy` and
`SimpleGraph.IsContained`, and the Lean kernel for a check run by `decide +kernel`, or Lean's
compiler for a compiled run. The encoding, the OPB printer and reader, the proof reader and the
checker are verified.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Graph.isoVar`, `Cslib.Logic.PL.VeriPB.Graph.isoConstraints`: the
  variables and the constraints of the encoding.
* `Cslib.Logic.PL.VeriPB.Graph.isoName`, `Cslib.Logic.PL.VeriPB.Graph.isoNames`: CakePB's names
  `xa_u` of the variables.
* `Cslib.Logic.PL.VeriPB.Graph.checkSubgraphIsoGraph`,
  `Cslib.Logic.PL.VeriPB.Graph.checkSubgraphIso`: the checkers, for graphs built in Lean and for
  LAD graphs.

## Main results

* `Cslib.Logic.PL.VeriPB.Graph.forall_holds_isoConstraints_iff`,
  `Cslib.Logic.PL.VeriPB.Graph.exists_holds_isoConstraints_iff`: correctness of the encoding.
* `Cslib.Logic.PL.VeriPB.Graph.name_isoNames_isoVar`: the variable `xₐᵤ` is named `xa_u`.
* `Cslib.Logic.PL.VeriPB.Graph.isoNames_covers`: CakePB's names cover the encoding, the side
  condition of the round-trip theorems of `Cslib.Logic.PL.VeriPB.Print`, for a client that
  applies them to the printed encoding.
* `Cslib.Logic.PL.VeriPB.Graph.isContained_iff_of_checkSubgraphIsoGraph`,
  `Cslib.Logic.PL.VeriPB.Graph.isContained_iff_of_checkSubgraphIso`: the end-to-end theorems.

## References

* [S. Gocht, C. McCreesh, M. O. Myreen, J. Nordström, A. Oertel, Y. K. Tan, *End-to-End
  Verification for Subgraph Solving*][GochtMcCreeshMyreenNordstromOertelTan2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Graph

open PBConstr Text

variable {p t : ℕ}

/-! ### The encoding -/

/-- **The variable `xₐᵤ`** of the encoding, true when the pattern vertex `a` is mapped to the
target vertex `u`, among targets on `Fin t`: the variable `t·a + u`, written `xa_u` in OPB text
(`Cslib.Logic.PL.VeriPB.Graph.isoName`). -/
@[expose] def isoVar (t : ℕ) (a : Fin p) (u : Fin t) : ℕ := t * a.val + u.val

/-- **The subgraph isomorphism encoding** of a pattern `P` on `Fin p` and a target `T` on `Fin t`,
in CakePB's order: `∑ᵤ xₐᵤ ≥ 1` for each `a`; `∑ᵤ ~xₐᵤ ≥ t - 1` for each `a`; `∑ₐ ~xₐᵤ ≥ p - 1`
for each `u`; and `~xₐᵤ + ∑_{v ~ u} x_{bv} ≥ 1` for each `u`, each `a` and each neighbour `b` of
`a`. -/
@[expose] def isoConstraints (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] : List PBConstr :=
  (List.finRange p).map (fun a => ⟨(List.finRange t).map fun u => (1, (isoVar t a u, true)), 1⟩) ++
    (List.finRange p).map
      (fun a => ⟨(List.finRange t).map fun u => (1, (isoVar t a u, false)), t - 1⟩) ++
    (List.finRange t).map
      (fun u => ⟨(List.finRange p).map fun a => (1, (isoVar t a u, false)), p - 1⟩) ++
    (List.finRange t).flatMap fun u => (List.finRange p).flatMap fun a =>
      ((List.finRange p).filter (P.Adj a ·)).map fun b =>
        ⟨(1, (isoVar t a u, false)) ::
          ((List.finRange t).filter (T.Adj u ·)).map fun v => (1, (isoVar t b v, true)), 1⟩

/-! ### Correctness -/

/-- `xₐᵤ` is the index of `(a, u)` under Mathlib's `finProdFinEquiv`. -/
private theorem val_finProdFinEquiv_eq_isoVar (a : Fin p) (u : Fin t) :
    (finProdFinEquiv (a, u) : ℕ) = isoVar t a u := by
  rw [finProdFinEquiv_apply_val, isoVar, Nat.add_comm]

private theorem isoVar_inj {a a' : Fin p} {u u' : Fin t} (h : isoVar t a u = isoVar t a' u') :
    a = a' ∧ u = u' := by
  have hv : (finProdFinEquiv (a, u) : ℕ) = finProdFinEquiv (a', u') := by
    rw [val_finProdFinEquiv_eq_isoVar, val_finProdFinEquiv_eq_isoVar, h]
  exact Prod.ext_iff.1 (finProdFinEquiv.injective (Fin.ext hv))

/-- A sum of literals with coefficient `1` over all of `Fin k` counts the true ones. -/
private theorem lhs_finRange {k : ℕ} (g : Fin k → ℕ) (b : Bool) (σ : ℕ → Bool) :
    lhs σ ((List.finRange k).map fun x => (1, (g x, b))) =
      (Finset.univ.filter fun x => σ (g x) = b).card := by
  rw [Finset.card_filter, Fin.sum_univ_def, lhs, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, termVal, Literal.eval, one_mul]
  cases σ (g x) <;> cases b <;> rfl

/-- A sum of literals with coefficient `1` is positive when one of them is true. -/
private theorem one_le_lhs_iff {α : Type*} (L : List α) (g : α → ℕ) (σ : ℕ → Bool) :
    1 ≤ lhs σ (L.map fun x => (1, (g x, true))) ↔ ∃ x ∈ L, σ (g x) = true := by
  induction L with
  | nil => simp [lhs]
  | cons y L ih =>
    simp only [lhs, List.map_cons, List.sum_cons, termVal, Literal.eval, one_mul,
      List.mem_cons, exists_eq_or_imp] at ih ⊢
    rw [← ih]
    cases σ (g y) <;> simp

/-- The true and the false literals over all of `Fin k` together number `k`. -/
private theorem card_true_add_card_false {k : ℕ} (q : Fin k → Bool) :
    (Finset.univ.filter fun x => q x = true).card +
      (Finset.univ.filter fun x => q x = false).card = k := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun x => q x = true
  simpa only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] using this

/-- The constraints of the encoding hold exactly when each of its four families does. -/
private theorem forall_holds_isoConstraints_iff_aux (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (σ : ℕ → Bool) :
    (∀ c ∈ isoConstraints P T, c.Holds σ) ↔
      (∀ a : Fin p, 1 ≤ (Finset.univ.filter fun u => σ (isoVar t a u) = true).card) ∧
      (∀ a : Fin p, t - 1 ≤ (Finset.univ.filter fun u => σ (isoVar t a u) = false).card) ∧
      (∀ u : Fin t, p - 1 ≤ (Finset.univ.filter fun a : Fin p => σ (isoVar t a u) = false).card) ∧
      (∀ u : Fin t, ∀ a b : Fin p, P.Adj a b → σ (isoVar t a u) = true →
        ∃ v, T.Adj u v ∧ σ (isoVar t b v) = true) := by
  simp only [isoConstraints, List.forall_mem_append, List.forall_mem_map, List.mem_finRange,
    List.forall_mem_flatMap, List.mem_filter, decide_eq_true_eq, true_and, Holds,
    lhs_finRange, forall_const, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine forall_congr' fun u => forall_congr' fun a => ⟨fun h b hab hσ => ?_, fun h b hab => ?_⟩
  · have := h b hab
    simp only [lhs, List.map_cons, List.sum_cons, termVal, Literal.eval, hσ, one_mul] at this
    obtain ⟨v, hv, hσv⟩ := (one_le_lhs_iff _ _ σ).1 (by simpa [lhs] using this)
    exact ⟨v, by simpa using hv, hσv⟩
  · simp only [lhs, List.map_cons, List.sum_cons, termVal, Literal.eval, one_mul]
    cases hσ : σ (isoVar t a u)
    · simp
    · obtain ⟨v, hv, hσv⟩ := h b hab hσ
      simpa [lhs] using (one_le_lhs_iff (((List.finRange t).filter (T.Adj u ·)))
        (isoVar t b) σ).2 ⟨v, by simpa using hv, hσv⟩

/-- **The solutions of the encoding are the copies of the pattern** (CakePB's `encode_correct`):
an assignment satisfies the constraints of the encoding exactly when it is the graph of a copy
`f` of `P` in `T`, an injective map sending edges to edges, `xₐᵤ` being true when `f a = u`. -/
theorem forall_holds_isoConstraints_iff (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (σ : ℕ → Bool) :
    (∀ c ∈ isoConstraints P T, c.Holds σ) ↔
      ∃ f : P.Copy T, ∀ a u, σ (isoVar t a u) = decide (f a = u) := by
  rw [forall_holds_isoConstraints_iff_aux]
  constructor
  · rintro ⟨hal1, ham1, hinj, hedge⟩
    have hone : ∀ a, (Finset.univ.filter fun u => σ (isoVar t a u) = true).card = 1 := fun a => by
      have := card_true_add_card_false fun u => σ (isoVar t a u)
      have := hal1 a
      have := ham1 a
      omega
    choose f hf using fun a => Finset.card_eq_one.1 (hone a)
    have hσ : ∀ a u, σ (isoVar t a u) = decide (f a = u) := fun a u => by
      have := congrArg (u ∈ ·) (hf a)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        eq_iff_iff] at this
      rw [Bool.eq_iff_iff, decide_eq_true_eq, this, eq_comm]
    have hinj' : Function.Injective f := fun a b hab => by
      have hle : (Finset.univ.filter fun a : Fin p => σ (isoVar t a (f b)) = true).card ≤ 1 := by
        have := card_true_add_card_false fun a : Fin p => σ (isoVar t a (f b))
        have := hinj (f b)
        have := (Finset.univ.filter fun a : Fin p => σ (isoVar t a (f b)) = true).card_le_univ
        simp only [Fintype.card_fin] at this
        omega
      exact Finset.card_le_one.1 hle a (by simp [hσ, hab]) b (by simp [hσ])
    refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, hinj'⟩, hσ⟩
    obtain ⟨v, hv, hσv⟩ := hedge (f a) a b hab (by simp [hσ])
    rw [hσ, decide_eq_true_eq] at hσv
    exact hσv ▸ hv
  · rintro ⟨f, hσ⟩
    have hS : ∀ a, (Finset.univ.filter fun u => σ (isoVar t a u) = true) = {f a} := fun a => by
      ext u
      simp [hσ, eq_comm]
    refine ⟨fun a => by simp [hS], fun a => ?_, fun u => ?_, fun u a b hab ha => ?_⟩
    · have := card_true_add_card_false fun u => σ (isoVar t a u)
      rw [hS, Finset.card_singleton] at this
      omega
    · have hle : (Finset.univ.filter fun a : Fin p => σ (isoVar t a u) = true).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha b hb => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ, decide_eq_true_eq] at ha hb
          exact f.injective (ha.trans hb.symm)
      have := card_true_add_card_false fun a : Fin p => σ (isoVar t a u)
      omega
    · rw [hσ, decide_eq_true_eq] at ha
      exact ⟨f b, ha ▸ f.toHom.map_adj hab, by simp [hσ]⟩

/-- **The encoding is satisfiable exactly when the pattern has a copy in the target** (CakePB's
`encode_correct`, with `has_subgraph_iso` as `P ⊑ T`). -/
theorem exists_holds_isoConstraints_iff (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    (∃ σ : ℕ → Bool, ∀ c ∈ isoConstraints P T, c.Holds σ) ↔ P.IsContained T := by
  simp only [forall_holds_isoConstraints_iff]
  refine ⟨fun ⟨_, f, _⟩ => ⟨f⟩, fun ⟨f⟩ =>
    ⟨fun i => decide (∃ a u, isoVar t a u = i ∧ f a = u), f, fun a u =>
      decide_eq_decide.2 ⟨fun ⟨_, _, h, hfu⟩ => ?_, fun h => ⟨a, u, rfl, h⟩⟩⟩⟩
  obtain ⟨rfl, rfl⟩ := isoVar_inj h
  exact hfu

/-! ### CakePB's variable names -/

/-- **CakePB's name `xa_u`** of the variable `xₐᵤ` (the pattern vertex `a` mapped to the target
vertex `u`), as `cake_pb_iso` and the Glasgow Subgraph Solver write it. -/
@[expose] def isoName (a u : ℕ) : String :=
  String.ofList ('x' :: Nat.toDecimal a ++ '_' :: Nat.toDecimal u)

/-- **CakePB's names of the variables of the encoding**, for a pattern on `Fin p` and a target on
`Fin t`: the variable `xₐᵤ = t·a + u` (`Cslib.Logic.PL.VeriPB.Graph.isoVar`) is named `xa_u`
(`Cslib.Logic.PL.VeriPB.Graph.isoName`). -/
@[expose] def isoNames (p t : ℕ) : Names :=
  ⟨(List.range (p * t)).map fun i => isoName (i / t) (i % t), 0⟩

private theorem underscore_not_mem_toDecimal (n : ℕ) : '_' ∉ Nat.toDecimal n := fun h =>
  absurd (Nat.isDigit_of_mem_toDecimal h) (by decide)

private theorem isoName_inj {a u a' u' : ℕ} (h : isoName a u = isoName a' u') :
    a = a' ∧ u = u' := by
  have h := congrArg String.toList h
  rw [isoName, isoName, String.toList_ofList, String.toList_ofList] at h
  replace h := (List.cons.inj h).2
  obtain ⟨ha, hu⟩ := (List.append_cons_inj_of_notMem_prefix (underscore_not_mem_toDecimal a)
    (underscore_not_mem_toDecimal a')).1 h
  exact ⟨by simpa using congrArg Nat.ofDecimal? ha, by simpa using congrArg Nat.ofDecimal? hu⟩

private theorem isOPBName_isoName (a u : ℕ) : isOPBName (isoName a u) = true := by
  obtain ⟨d, ds, hd, -⟩ := Nat.exists_toDecimal_eq_cons a
  have hc (c) (hc : c ∈ Nat.toDecimal a ++ '_' :: Nat.toDecimal u) : isNameChar c = true := by
    rcases List.mem_append.1 hc with hc | hc
    · simp [isNameChar, Char.isAlphanum, Nat.isDigit_of_mem_toDecimal hc]
    · rcases List.mem_cons.1 hc with rfl | hc
      · decide
      · simp [isNameChar, Char.isAlphanum, Nat.isDigit_of_mem_toDecimal hc]
  rw [isOPBName, isoName, String.toList_ofList, hd, List.cons_append, List.cons_append]
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨by decide, fun c hc' => hc c (by rw [hd]; simpa using hc')⟩

private theorem isoVar_lt (a : Fin p) (u : Fin t) : isoVar t a u < p * t :=
  val_finProdFinEquiv_eq_isoVar a u ▸ (finProdFinEquiv (a, u)).isLt

private theorem lt_of_mem_varList_isoConstraints (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] {v : ℕ}
    (hv : v ∈ (⟨isoConstraints P T, none, none⟩ : Instance).varList) : v < p * t := by
  simp only [Instance.varList, Option.map_none, Option.getD_none, List.append_nil,
    List.mem_flatMap, List.mem_map] at hv
  obtain ⟨c, hc, ⟨k, x, b⟩, hx, rfl⟩ := hv
  simp only [isoConstraints, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
    List.mem_finRange, true_and] at hc
  rcases hc with ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨u, rfl⟩) | ⟨u, a, b', -, rfl⟩ <;>
    simp only [List.mem_cons, List.mem_map, List.mem_finRange, List.mem_filter, true_and,
      Prod.mk.injEq] at hx
  · obtain ⟨u, rfl, rfl, rfl⟩ := hx
    exact isoVar_lt a u
  · obtain ⟨u, rfl, rfl, rfl⟩ := hx
    exact isoVar_lt a u
  · obtain ⟨a, rfl, rfl, rfl⟩ := hx
    exact isoVar_lt a u
  · rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨w, _, rfl, rfl, rfl⟩
    · exact isoVar_lt a u
    · exact isoVar_lt b' w

/-- **CakePB's name of a variable**: the variable `xₐᵤ = t·a + u` is named `xa_u`. -/
@[simp] theorem name_isoNames_isoVar (a : Fin p) (u : Fin t) :
    (isoNames p t).name (isoVar t a u) = isoName a u := by
  have hlt := isoVar_lt a u
  have hd : isoVar t a u / t = a := by
    rw [isoVar, Nat.mul_add_div (Fin.pos u), Nat.div_eq_of_lt u.isLt,
      Nat.add_zero]
  have hm : isoVar t a u % t = u := by
    rw [isoVar, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
  simp [Names.name, Names.nameChars, isoNames, hlt, hd, hm]

/-- **CakePB's names cover the encoding** (`Cslib.Logic.PL.VeriPB.Text.Names.Covers`): they are
distinct OPB names, and every variable of the encoding is named, `xa_u`. -/
theorem isoNames_covers (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    (isoNames p t).Covers ⟨isoConstraints P T, none, none⟩ := by
  have hopb : ∀ s ∈ (isoNames p t).others, isOPBName s = true := fun s hs => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
    exact isOPBName_isoName _ _
  have hlt : ∀ v ∈ (⟨isoConstraints P T, none, none⟩ : Instance).varList,
      v < (isoNames p t).next := fun v hv => by
    simpa [Names.next, isoNames] using lt_of_mem_varList_isoConstraints P T hv
  refine ⟨⟨?_, fun s hs => isName_of_isOPBName (hopb s hs), fun _ _ _ _ => Nat.zero_le _⟩,
    hlt, fun v hv => Names.isOPBName_name hopb (hlt v hv)⟩
  refine List.nodup_range.map_on fun i _ j _ hij => ?_
  obtain ⟨hd, hm⟩ := isoName_inj hij
  rw [← Nat.div_add_mod i t, ← Nat.div_add_mod j t, hd, hm]

/-! ### End to end -/

/-- **The subgraph isomorphism checker for graphs built in Lean**: check the proof `pbp` against
the printed OPB text of the encoding of `P` and `T`, with CakePB's variable names `xa_u`
(`Cslib.Logic.PL.VeriPB.Graph.isoNames`), and read its conclusion: `true` for `SAT`, `false` for
`UNSAT`, nothing for the others. -/
def checkSubgraphIsoGraph (P : SimpleGraph (Fin p)) [DecidableRel P.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (pbp : String) : Option Bool :=
  (checkOPBOutput (printOPB ⟨isoConstraints P T, none, none⟩ (isoNames p t)) pbp).bind fun
    | (.sat _, _) => some true
    | (.unsat _, _) => some false
    | _ => none

/-- **The subgraph isomorphism checker for LAD graphs**: read the pattern and the target, then
check the proof `pbp` against their encoding
(`Cslib.Logic.PL.VeriPB.Graph.checkSubgraphIsoGraph`). -/
def checkSubgraphIso (pattern target pbp : String) : Option Bool :=
  (parseLAD pattern).bind fun gp => (parseLAD target).bind fun gt =>
    checkSubgraphIsoGraph gp.graph gt.graph pbp

/-- **Subgraph isomorphism from an accepted proof** (CakePB's `full_encode_sem_concl`): if the
checker accepts a proof against the encoding of `P` and `T` with the answer `b` (`SAT` for
`true`, `UNSAT` for `false`), then `P` has a copy in `T` exactly when `b` is `true`. -/
theorem isContained_iff_of_checkSubgraphIsoGraph {P : SimpleGraph (Fin p)} [DecidableRel P.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] {pbp : String} {b : Bool}
    (h : checkSubgraphIsoGraph P T pbp = some b) : P.IsContained T ↔ b = true := by
  obtain ⟨⟨concl, o⟩, hc, hb⟩ := Option.bind_eq_some_iff.1 h
  rw [← exists_holds_isoConstraints_iff]
  have hc' : (checkOPBOutput (printOPB ⟨isoConstraints P T, none, none⟩ (isoNames p t)) pbp).map
      (·.1) = some concl := by rw [hc]; rfl
  cases concl with
  | sat _ =>
    cases hb
    exact iff_of_true (exists_satisfies_of_checkOPB_printOPB (isoNames_covers P T) hc') rfl
  | unsat _ =>
    cases hb
    exact iff_of_false
      (fun ⟨σ, hσ⟩ => not_satisfiable_of_checkOPB_printOPB (isoNames_covers P T) hc' σ hσ)
      (by simp)
  | _ => cases hb

/-- **Subgraph isomorphism for LAD graphs** (CakePB's `check_unsat_3_sem`, the pure functional
specification of `cake_pb_iso`, not its compiled code): if the checker returns `b` for the LAD
texts `pattern` and `target` and the proof `pbp`, then both texts parse, and the pattern read has a
copy in the target read exactly when `b` is `true`. -/
theorem isContained_iff_of_checkSubgraphIso {pattern target pbp : String} {b : Bool}
    (h : checkSubgraphIso pattern target pbp = some b) :
    ∃ gp gt, parseLAD pattern = some gp ∧ parseLAD target = some gt ∧
      (gp.graph.IsContained gt.graph ↔ b = true) := by
  obtain ⟨gp, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨gt, ht, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨gp, gt, hp, ht, isContained_iff_of_checkSubgraphIsoGraph h⟩

end Cslib.Logic.PL.VeriPB.Graph
