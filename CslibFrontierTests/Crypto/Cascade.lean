/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildChallenge
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildReductionLaw
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRoutingPPT
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildTableLaw
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.SampledReductionLaw
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

-- The word used as a short index is also visited as a parent, with a separate child table.
example :
    let distribution := PMF.uniformOfFintype (BitString 1 → BitString 2)
    (ProbOracleComp.runWith (cascadeChildChannelOracle distribution)
      (cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents) []).map
        Prod.fst =
      cascadeChildTableGame boundedWords (fun _ => 1) toggle (fun _ _ => visitBothParents) 2 1
        (PMF.uniformOfFintype (BitString 1 → BitString 1 → BitString 2)) := by
  calc
    _ = cascadeChildPrefixGame (boundedWords 2) (fun _ => 1) toggle 2 1
        (PMF.uniformOfFintype (BitString 1 → BitString 2)) visitBothParents :=
      runWith_cascadeChildRouter_eq_prefixGame (boundedWords 2) (fun _ => 1) toggle 2 1
        (PMF.uniformOfFintype (BitString 1 → BitString 2)) visitBothParents
    _ = _ := by
      simpa only [PMF.pi_uniformOfFintype] using
        cascadeChildPrefixGame_eq_childTableGame boundedWords (fun _ => 1) toggle
          (fun _ _ => visitBothParents) 2 1 (PMF.uniformOfFintype (BitString 1 → BitString 2))

-- The first long query sends channel zero and reads at most two bits of its reply.
example :
    encodedCascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 (do
      let reply ← ProbOracleComp.query ((), [true, false])
      return reply == [true, false]) =
      (do
        let reply ← ProbOracleComp.query ((), encCascadeChildRequest (0, [false]))
        return reply.take 2 == [true, false]) := by
  simp only [encodedCascadeChildRouter, cascadeChildRouter, bind_pure_comp,
    OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query]
  simp [StateT.run, cascadeChildRoute, boundedWords, Functor.map_map]

-- Skipping channel zero cannot allocate channel one. Once zero is assigned, channel one
-- can be used and its subsequent calls leave the cursor unchanged.
example (table : Fin 2 → BitString 1 → BitString 2) :
    cascadeChildFiniteOracle table (1, [true]) 0 = PMF.pure ([], 0) ∧
      cascadeChildFiniteOracle table (1, [true]) 1 =
        PMF.pure (List.ofFn (table 1 (BitString.ofList 1 [true])), 2) ∧
      cascadeChildFiniteOracle table (1, [true]) 2 =
        PMF.pure (List.ofFn (table 1 (BitString.ofList 1 [true])), 2) :=
  ⟨rfl, rfl, rfl⟩

private theorem visitBothParents_isQueryBounded : visitBothParents.IsQueryBounded 4 :=
  (ProbOracleComp.IsQueryBounded.query _).bind fun _ =>
    (ProbOracleComp.IsQueryBounded.query _).bind fun _ =>
      (ProbOracleComp.IsQueryBounded.query _).bind fun _ =>
        (ProbOracleComp.IsQueryBounded.query _).bind fun _ => .pure _ 0

example :
    let source := PMF.uniformOfFintype (BitString 1 → BitString 2)
    let router := cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents
    (ProbOracleComp.runWith (cascadeChildChannelOracle source) router []).map Prod.fst =
      (PMF.pi (fun _ : Fin 4 => source)).bind fun table =>
        (ProbOracleComp.runWith (cascadeChildFiniteOracle table) router 0).map Prod.fst :=
  runWith_cascadeChildChannelOracle_eq_finite
    (PMF.uniformOfFintype (BitString 1 → BitString 2))
    (isQueryBounded_cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1
      visitBothParents_isQueryBounded)

-- Four admissible channels in a sampling range of eight.
example :
    let real := PMF.pure (fun _ : BitString 1 => BitString.ofList 2 [true, false])
    let ideal := PMF.uniformOfFintype (BitString 1 → BitString 2)
    let router := cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents
    Game.advantage
        ((ProbOracleComp.runWith (cascadeChildChannelOracle real) router []).map Prod.fst)
        ((ProbOracleComp.runWith (cascadeChildChannelOracle ideal) router []).map Prod.fst) =
      8 * Game.advantage
        (cascadeChildChallengeGame 4 8 real ideal real router)
        (cascadeChildChallengeGame 4 8 real ideal ideal router) :=
  advantage_cascadeChildChannelOracle_eq _ _
    (isQueryBounded_cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1
      visitBothParents_isQueryBounded) (by decide)

-- Every sampled channel is padding when the query budget is zero.
example (source : PMF (BitString 1 → BitString 2)) :
    cascadeChildChallengeGame 0 8 source source source (pure true) = PMF.pure false := by
  simp [cascadeChildChallengeGame]

-- A skipped first-use channel cannot forward even when it is the selected channel.
example :
    cascadeChildChallengeHandler toggle 1 2 2 1 [] (1, [true]) ⟨0, []⟩ =
      pure ([], ⟨0, []⟩) := rfl

-- The challenge receives the normalized block and only the first two reply bits are used.
example :
    cascadeChildChallengeHandler toggle 1 2 2 1 [] (1, []) ⟨1, []⟩ = (do
      let reply ← ProbOracleComp.query ((), [false])
      return (reply.take 2, ⟨2, []⟩)) := rfl

-- An earlier channel reuses its cached answer on two representations of the same block.
example :
    let state : CascadeChildChallengeState := ⟨1, [((0, [false]), [true, true])]⟩
    cascadeChildChallengeHandler toggle 1 2 2 1 [] (0, []) state =
      pure ([true, true], state) := rfl

-- A later channel uses its own key row without calling the challenge oracle.
example :
    cascadeChildChallengeHandler toggle 1 2 2 0 [true, true, true, false]
        (1, [true]) ⟨1, []⟩ =
      pure ([false, true], ⟨2, []⟩) := rfl

example : cascadeChildChallengeProgram toggle 1 2 0 0 (pure true) = pure false := rfl

example :
    let router := cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents
    (cascadeChildChallengeProgram toggle 1 2 4 3 router).IsQueryBounded 4 :=
  isQueryBounded_cascadeChildChallengeProgram toggle 1 2 4 3
    (isQueryBounded_cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1
      visitBothParents_isQueryBounded)

-- The adaptive client can observe an ideal row before visiting the challenge channel.
example :
    let keys := [true, false, false, true, false, false]
    let challenge (_ : BitString 1) := BitString.ofList 2 [true, true]
    let router := cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle 1 challenge req.2)))
        (cascadeChildChallengeAtProgram toggle 1 2 3 1 keys router) =
      (PMF.uniformOfFintype (Fin 3 × BitString 1 → BitString 2)).bind fun ideal =>
        let table (channel : Fin 3) (block : BitString 1) :=
          if channel < 1 then ideal (channel, block)
          else if channel = 1 then challenge block
          else BitString.ofList 2 (toggle (BitString.listRow 2 channel.val keys) (List.ofFn block))
        (ProbOracleComp.runWith (cascadeChildFiniteOracle table) router 0).map Prod.fst :=
  evalWith_cascadeChildChallengeAtProgram_eq_eager toggle
    (fun key block hk _ => by unfold toggle; split <;> simpa using hk) (1 : Fin 3) _ _ _

-- The wrapper samples eight indices for four channels of an adaptive client.
example :
    let router := cascadeChildRouter (boundedWords 2) (fun _ => 1) toggle 2 1 visitBothParents
    let source := PMF.pure (fun _ : BitString 1 => BitString.ofList 2 [true, false])
    (source.bind fun challenge =>
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle 1 challenge req.2)))
        (cascadeChildChallengeProgram toggle 1 2 4 3 router)) =
      cascadeChildChallengeGame 4 8 (cascadeKeyedChildFunctionLaw toggle 1 2)
        (PMF.uniformOfFintype (BitString 1 → BitString 2)) source router :=
  bind_evalWith_cascadeChildChallengeProgram_eq_game toggle
    (fun key block hk _ => by unfold toggle; split <;> simpa using hk) 4 3 _ _
