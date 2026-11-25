/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRoutingLaw
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildTables
import Mathlib.Data.Set.Finite.List

/-!
# Cascade evaluation and prefix hybrid tests

Use one-bit message blocks and a two-bit key to exercise the separate widths and the extension
identity. The hybrid examples exercise mixed-length queries and prefix reuse.
-/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

private def toggle (key block : List Bool) : List Bool :=
  if block.headD false then key.map (!·) else key

example : cascadeFamily (fun _ => 1) toggle [true, false] [] = [true, false] :=
  cascadeFamily_nil _ _ _

example : cascadeFamily (fun _ => 1) toggle [true, false] [true, false] = [false, true] := by
  decide

example : cascadeFamily (fun _ => 1) toggle [true, false] ([true] ++ [true, false]) =
    cascadeFamily (fun _ => 1) toggle (cascadeFamily (fun _ => 1) toggle [true, false] [true])
      [true, false] :=
  cascadeFamily_append (fun key block _ => by
    unfold toggle
    split <;> simp) _ (by decide) (by decide) (by decide)

example : ComputableInPolyTime
    (fun p : List Bool × List Bool => cascadeFamily (fun _ => 1) (fun key _ => key) p.1 p.2)
    (encPair encBits encBits) encBits :=
  computableInPolyTime_cascadeFamily (ComputableInPolyTime.const 1) (fun _ _ _ => rfl)
    (ComputableInPolyTime.fst encBits encBits)

private def boundedWords (_ : ℕ) (word : List Bool) : Bool := decide (word.length ≤ 2)

private def compareReplies : OracleDistinguisher := fun _ _ => do
  let empty ← ProbOracleComp.query ((), [])
  let twoBits ← ProbOracleComp.query ((), [true, false])
  let repeated ← ProbOracleComp.query ((), [true, false])
  let malformed ← ProbOracleComp.query ((), [true, false, true])
  return empty != twoBits && twoBits == repeated && malformed.isEmpty

-- The final hybrid handles different valid lengths, a repeat, and an invalid word.
example :
    ProbComp.eval (cascadePrefixHybridGame boundedWords (fun _ => 1) toggle compareReplies 2 2) =
      ProbComp.eval (prfIdealGameOn boundedWords id compareReplies 2) :=
  eval_cascadePrefixHybridGame_eq_ideal _ _ fun query hquery => by
    simpa [boundedWords] using hquery

-- At one block of depth, distinct queries sharing a first block reuse its sampled label.
example :
    ProbComp.eval (prefixHybridOracle (boundedWords 2) (cascadeFamily (fun _ => 1) toggle)
        2 1 [true, true] [([true], [true, false])]) =
      PMF.pure ([false, true], [([true], [true, false])]) := by
  simp [prefixHybridOracle, boundedWords, ProbComp.eval_pure, memoize, cascadeFamily,
    BitString.listRows, BitString.listRow, toggle]

-- The eager table keeps the actual lengths of both the empty prefix and the two-bit prefix.
noncomputable local instance : Fintype {word : List Bool // word.length ≤ 2} :=
  (List.finite_length_le Bool 2).fintype

example :
    ProbComp.eval (cascadePrefixHybridGame boundedWords (fun _ => 1) toggle compareReplies 2 2) =
      (PMF.uniformOfFintype ({word : List Bool // word.length ≤ 2} → BitString 2)).bind
        fun table => OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (if boundedWords 2 request.2 then
            cascadeFamily (fun _ => 1) toggle
              (List.ofFn (table ⟨request.2.take 2, by simp⟩)) (request.2.drop 2)
            else []))) (compareReplies 2 []) :=
  eval_prefixHybridGame_eq_eager boundedWords (cascadeFamily (fun _ => 1) toggle) compareReplies 2 2

noncomputable local instance : Fintype {word : List Bool // word.length ≤ 1} :=
  (List.finite_length_le Bool 1).fintype

-- A word at the old cut uses its own label. Reading another bit switches to its child table.
example :
    let short : {word : List Bool // word.length ≤ 1} → BitString 1 := fun _ _ => true
    let children : BitString 1 → BitString 1 → BitString 1 :=
      fun parent block _ => parent 0 && block 0
    prefixHybridSplitAnswer (cascadeFamily (fun _ => 1) toggle) short children [true] = [true] ∧
      prefixHybridSplitAnswer (cascadeFamily (fun _ => 1) toggle) short children
        [true, false] = [false] := by
  exact ⟨(prefixHybridSplitAnswer_of_length_le (by decide)).trans rfl,
    (prefixHybridSplitAnswer_of_lt_length (by decide)).trans rfl⟩

example :
    ProbComp.eval (cascadePrefixHybridGame boundedWords (fun _ => 1) toggle compareReplies 2 2) =
      (PMF.uniformOfFintype
        (({word : List Bool // word.length ≤ 1} → BitString 2) ×
          (BitString 1 → BitString 1 → BitString 2))).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (if boundedWords 2 request.2 then
            prefixHybridSplitAnswer (cascadeFamily (fun _ => 1) toggle)
              tables.1 tables.2 request.2 else []))) (compareReplies 2 []) :=
  eval_prefixHybridGame_add_eq_split boundedWords (cascadeFamily (fun _ => 1) toggle)
    compareReplies 2 1 1 (by decide) (cascadeFamily_nil _ _) (fun _ _ h => h)

private def realValid (_ : ℕ) (word : List Bool) : Bool :=
  [[false], [true, false], [true, true]].contains word

-- An earlier short reply picks the next query, which is then repeated.
private def adaptiveSides : OracleDistinguisher := fun _ _ => do
  let short ← ProbOracleComp.query ((), [false])
  let long := [true, short.headD false]
  let first ← ProbOracleComp.query ((), long)
  let repeated ← ProbOracleComp.query ((), long)
  return first == repeated && short.headD false

private theorem adaptiveSides_prefixFree :
    IsPrefixFreeOn (realValid 2) 2 (adaptiveSides 2 []) := by
  have h : WordPrefixFree (fun _ => true) [[false], [true, false], [true, true]] := by
    unfold WordPrefixFree
    decide
  intro _ _ _ _ _ x _ hx y _ hy hne hprefix
  exact h x (by simpa [realValid] using hx) rfl y (by simpa [realValid] using hy) rfl hne hprefix

private theorem length_toggle (key block : List Bool) :
    (toggle key block).length = key.length := by
  unfold toggle
  split <;> simp

example :
    let Labels := {word : List Bool // word.length ≤ 1} → BitString 2
    ProbComp.eval (cascadePrefixHybridGame realValid (fun _ => 1) toggle adaptiveSides 2 1) =
      (PMF.uniformOfFintype (Labels × Labels)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
          PMF.pure (prefixHybridIndependentLabelOracle (realValid 2)
            (cascadeFamily (fun _ => 1) toggle) tables.1 tables.2 request.2)))
          (adaptiveSides 2 []) :=
  eval_prefixHybridGame_eq_independentLabels realValid (cascadeFamily (fun _ => 1) toggle)
    adaptiveSides 2 1
    (fun seed suffix hseed =>
      (length_cascadeFamily (fun key block _ => length_toggle key block) seed suffix).trans hseed)
    adaptiveSides_prefixFree

example :
    ProbComp.eval (cascadePrefixHybridGame realValid (fun _ => 1) toggle adaptiveSides 2 1) =
      cascadeChildTableGame realValid (fun _ => 1) toggle adaptiveSides 2 1
        ((PMF.uniformOfFintype (BitString 1 → BitString 2)).map fun keys parent block =>
          BitString.ofList 2 (toggle (List.ofFn (keys parent)) (List.ofFn block))) :=
  eval_cascadePrefixHybridGame_eq_childTables_real realValid (fun _ => 1) toggle adaptiveSides 2 1
    (by decide) (fun _ _ => Nat.one_dvd _) (fun key block _ => length_toggle key block)
    adaptiveSides_prefixFree

example :
    ProbComp.eval (cascadePrefixHybridGame realValid (fun _ => 1) toggle adaptiveSides 2 2) =
      cascadeChildTableGame realValid (fun _ => 1) toggle adaptiveSides 2 1
        (PMF.uniformOfFintype (BitString 1 → BitString 1 → BitString 2)) :=
  eval_cascadePrefixHybridGame_succ_eq_childTables_ideal realValid (fun _ => 1) toggle adaptiveSides
    2 1 (by decide) (fun _ _ => Nat.one_dvd _)

-- A new parent takes the next channel, while a repeat keeps that channel and state.
example :
    let old : CascadeChildRouterState := ⟨[[false]], [([false], [false, true])]⟩
    let next : CascadeChildRouterState := { old with parents := [[false], [true]] }
    let forwarded : WordOracleComp ℕ (List Bool × CascadeChildRouterState) := do
      let reply ← ProbOracleComp.query (1, [false])
      return (reply.take 2, next)
    cascadeChildRoute (boundedWords 2) (fun _ => 1) toggle 2 1 [true, false] old = forwarded ∧
      cascadeChildRoute (boundedWords 2) (fun _ => 1) toggle 2 1 [true, false] next =
        forwarded := by
  dsimp only
  constructor <;> simp [cascadeChildRoute, boundedWords, List.idxOf_cons_ne]

-- A cached query at the cut and an invalid long word consume no child-oracle call.
example :
    let state : CascadeChildRouterState := ⟨[], [([false], [false, true])]⟩
    cascadeChildRoute (boundedWords 2) (fun _ => 1) toggle 2 1 [false] state =
      pure ([false, true], state) ∧
    cascadeChildRoute (boundedWords 2) (fun _ => 1) toggle 2 1 [true, false, true] state =
      pure ([], state) :=
  ⟨rfl, rfl⟩

example :
    (cascadeChildRouter (realValid 2) (fun _ => 1) toggle 2 1
      (adaptiveSides 2 [])).IsQueryBounded 3 := by
  apply isQueryBounded_cascadeChildRouter
  exact (ProbOracleComp.IsQueryBounded.query _).bind fun _ =>
    (ProbOracleComp.IsQueryBounded.query _).bind fun _ =>
      (ProbOracleComp.IsQueryBounded.query _).bind fun _ => .pure _ 0

-- A short label determines the order in which the two parents are visited.
private def visitBothParents : WordOracleComp Unit Bool := do
  let short ← ProbOracleComp.query ((), [false])
  let start := short.headD false
  let first ← ProbOracleComp.query ((), [start, false])
  let other ← ProbOracleComp.query ((), [!start, true])
  let replay ← ProbOracleComp.query ((), [start, false])
  return first == replay && first != other

example :
    let distribution := PMF.uniformOfFintype (BitString 1 → BitString 2)
    (ProbOracleComp.runWith (cascadeChildChannelOracle distribution)
      (cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents) []).map
        Prod.fst =
      cascadeChildPrefixGame (boundedWords 2) (fun _ => 1) toggle 2 1 distribution
        visitBothParents :=
  runWith_cascadeChildRouter_eq_prefixGame (boundedWords 2) (fun _ => 1) toggle 2 1
    (PMF.uniformOfFintype (BitString 1 → BitString 2)) visitBothParents

-- The prefix-indexed oracle reads the next block and records the sampled row under its parent.
example :
    let row : BitString 1 → BitString 2 := fun block _ => block 0
    let initial : CascadeChildPrefixState 1 2 := ⟨[], fun _ => none⟩
    cascadeChildPrefixOracle (boundedWords 2) (fun _ => 1) toggle 2 1 (PMF.pure row)
      [false, true] initial =
      PMF.pure ([true, true], { initial with
        parentRows := Function.update initial.parentRows [false] (some row) }) := by
  have hword : List.ofFn (BitString.ofList 1 [true]) = [true] := BitString.ofFn_ofList rfl
  have hbit : BitString.ofList 1 [true] 0 = true := by
    simpa using congrArg (fun word : List Bool => word.headD false) hword
  simp [cascadeChildPrefixOracle, boundedWords, RandomOracle.answer, hbit]

-- An out-of-order channel leaves the table empty for the actual first request.
example (distribution : PMF (BitString 1 → BitString 2)) :
    cascadeChildChannelOracle distribution (1, [true]) [] = PMF.pure ([], []) ∧
    cascadeChildChannelOracle distribution (0, [true]) [] =
      distribution.map (fun row => (List.ofFn (row (BitString.ofList 1 [true])), [row])) :=
  ⟨rfl, rfl⟩
