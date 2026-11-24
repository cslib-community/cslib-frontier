/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Alternation.NP
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Alternation.SavitchEndpoints
import CslibFrontier.Computability.Complexity.Classes.Alternation.SavitchTime
import CslibFrontier.Computability.Complexity.Classes.Alternation.TQBF
import CslibFrontier.Computability.Complexity.Classes.Constructible.UnaryClock
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Polynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Tests: alternating machines and `AP = PSPACE`

A one-state machine that emits its move and halts: existential, it accepts every input, and
universal, it accepts none, so both labels matter; both decide their problems within one step,
which puts `Set.univ` and `∅` in `AP` with explicit machines, and their games of moves are won and
lost. Two game verifiers, one won by the existential player's first move and one lost to the
universal player's, put `Set.univ` and `∅` in `AP` through the guess-then-verify machine.
Single-bit moves on concrete predicates, rounds of quantifiers on a concrete formula, and
Savitch's midpoint game on a two-word graph, and the endpoints of its plays: the midpoint of the
last level with each half, and the endpoint machine on the same moves, with two levels of the
same half, so that the last one is found and not the first. `Set.univ` and `∅`, in
nondeterministic polynomial space through `P`, are midpoint games won and lost on every instance.
With both endpoints missing, the leaf test of the midpoint game is the edge test of the initial
and accepting codes, and the reduction of `NSPACE s ⊆ ATIME ((n + s n) ^ 2)` to a quadratic-time
leaf test applies to the time-constructible `s n = n`.
-/

namespace CslibFrontierTests.Alternation

open Cslib Cslib.Complexity Cslib.Logic.PL Turing
open Turing.MultiTapeTM (encBits PolyBounded)

/-! ### A machine emitting its move -/

/-- The machine with one state that emits its move and halts; its state is universal when `u`
is `true`. -/
private def emitMove (u : Bool) : MultiTapeATM 0 Bool Unit where
  toPTM :=
    { initial := ()
      tr := fun _ _ _ _ b => .step ⟨0, Fin.elim0, some b, none⟩ Empty.elim Empty.elim }
  universal _ := u

/-- The move `b` halts with output `[b]`. -/
private theorem next_emitMove (u b : Bool) (input : List Bool) :
    ((emitMove u).next b ((emitMove u).toPTM.toNTM.initCfg input)).state = none ∧
      ((emitMove u).next b ((emitMove u).toPTM.toNTM.initCfg input)).output = [b] := by
  rw [MultiTapeATM.next_of_state _ (q := ()) rfl]
  exact ⟨rfl, rfl⟩

/-- Every list of one move halts. -/
private theorem runsInTime_emitMove (u : Bool) (input : List Bool) :
    (emitMove u).toPTM.toNTM.RunsInTime input 1 := by
  refine MultiTapeATM.runsInTime_iff_stepCoins.mpr fun coins hlen => ?_
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact (next_emitMove u b input).1

/-- Existential, the machine accepts by the move `true`. -/
example (input : List Bool) : (emitMove false).Accepts input := by
  refine ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
    ⟨true, ?_⟩⟩
  exact ⟨(next_emitMove false true input).1, (next_emitMove false true input).2⟩

/-- Universal, the machine rejects: the move `false` emits `[false]`. -/
example (input : List Bool) : ¬(emitMove true).Accepts input := by
  rw [MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true input),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false input).2] at this
  simp at this

/-- The existential machine decides `Set.univ` within one step. -/
private theorem decidesInTime_univ :
    (emitMove false).DecidesInTime encBits Set.univ fun _ => 1 := fun a =>
  ⟨runsInTime_emitMove false a, iff_of_true trivial
    ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
      ⟨true, (next_emitMove false true a).1, (next_emitMove false true a).2⟩⟩⟩

/-- The universal machine decides `∅` within one step. -/
private theorem decidesInTime_empty :
    (emitMove true).DecidesInTime encBits ∅ fun _ => 1 := fun a => by
  refine ⟨runsInTime_emitMove true a, iff_of_false (Set.notMem_empty a) ?_⟩
  rw [MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true (encBits a)),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false (encBits a)).2] at this
  simp at this

/-- `Set.univ ∈ AP` and `∅ ∈ AP` by explicit machines and time bounds, transferring to `PSPACE`
and game verifiers. -/
example (a : List Bool) (u : Bool) :
    ((Set.univ : Set (List Bool)) ∈ AP encBits ∧ (∅ : Set (List Bool)) ∈ AP encBits) ∧
    ¬(emitMove true).AcceptsWithin 1 ((emitMove true).toPTM.toNTM.initCfg a) ∧
    (Set.univ : Set (List Bool)) ∈ PSPACE encBits ∧
    (∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      MultiTapeTM.ComputableInPolyTime V (MultiTapeTM.encPair encBits encBits)
        MultiTapeTM.encBool ∧ IsGameVerifier encBits p V (∅ : Set (List Bool))) ∧
    (emitMove u).HaltsWithin 1 ((emitMove u).toPTM.toNTM.initCfg a) :=
  have huniv : (Set.univ : Set (List Bool)) ∈ AP encBits :=
    ⟨_, PolyBounded.const 1, 0, Unit, inferInstance, emitMove false, decidesInTime_univ⟩
  have hempty : (∅ : Set (List Bool)) ∈ AP encBits :=
    ⟨_, PolyBounded.const 1, 0, Unit, inferInstance, emitMove true, decidesInTime_empty⟩
  ⟨⟨huniv, hempty⟩,
   (decidesInTime_empty.mem_iff a).not.mp (Set.notMem_empty a),
   AP_subset_PSPACE huniv,
   exists_isGameVerifier_of_mem_AP hempty,
   MultiTapeATM.runsInTime_iff_haltsWithin.mp (runsInTime_emitMove u a)⟩

/-! ### Parametric alternating time and space -/

/-- The explicit machines put `Set.univ` in `ATIME 1` and `∅` in `ATIME (n ^ 0)`. The union
characterization of `AP` and `ATIME ⊆ ASPACE` then give `∅ ∈ AP` and `∅ ∈ ASPACE 1`. -/
example :
    (Set.univ : Set (List Bool)) ∈ ATIME encBits (fun _ => 1) ∧
    (∅ : Set (List Bool)) ∈ AP encBits ∧
    (∅ : Set (List Bool)) ∈ ASPACE encBits (fun _ => 1) :=
  have huniv : (Set.univ : Set (List Bool)) ∈ ATIME encBits (fun _ => 1) :=
    ⟨1, 0, 0, Unit, inferInstance, emitMove false, decidesInTime_univ.mono fun _ => by simp⟩
  have hempty : (∅ : Set (List Bool)) ∈ ATIME encBits (· ^ 0) :=
    ⟨1, 0, 0, Unit, inferInstance, emitMove true, decidesInTime_empty.mono fun _ => by simp⟩
  ⟨huniv, mem_AP_iff_exists_mem_ATIME.mpr ⟨0, hempty⟩,
    ATIME_subset_ASPACE (ATIME_mono (fun _ => by simp) hempty)⟩

/-- Conversely, `AP` membership through a time bound of `1` yields an exponent `k` with
`Set.univ ∈ ATIME (n ^ k)`. -/
example : ∃ k, (Set.univ : Set (List Bool)) ∈ ATIME encBits (· ^ k) :=
  mem_AP_iff_exists_mem_ATIME.mp
    ⟨_, PolyBounded.const 1, 0, Unit, inferInstance, emitMove false, decidesInTime_univ⟩

/-- The classes absorb constant factors and additive constants in both directions. -/
example : ATIME encBits (fun n => 3 * n + 5) = ATIME encBits id ∧
    ASPACE encBits (fun n => 2 * Nat.log2 n + 7) = ASPACE encBits Nat.log2 :=
  ⟨subset_antisymm (ATIME_mono_of_le_mul_add (C := 5) fun _ => by simp only [id]; omega)
      (ATIME_mono fun _ => by simp only [id]; omega),
    subset_antisymm (ASPACE_mono_of_le_mul_add (C := 7) fun _ => by omega)
      (ASPACE_mono fun _ => by omega)⟩

/-- The existential machine wins its game of moves on every input. -/
example (input : List Bool) : Alternation true (List.replicate (2 * 1) 1)
    fun w => (emitMove false).strict.runClosedCoins w input = [true] :=
  (MultiTapeATM.accepts_iff_alternation _ (runsInTime_emitMove false input)).mp
    ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
      ⟨true, (next_emitMove false true input).1, (next_emitMove false true input).2⟩⟩

/-- The universal machine loses its game of moves on every input. -/
example (input : List Bool) : ¬Alternation true (List.replicate (2 * 1) 1)
    fun w => (emitMove true).strict.runClosedCoins w input = [true] := by
  rw [← MultiTapeATM.accepts_iff_alternation _ (runsInTime_emitMove true input),
    MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true input),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false input).2] at this
  simp at this

/-! ### Games won by the first or the second move -/

/-- The game won when the first move is `true`. -/
private def firstMove (x : List Bool × List Bool) : Bool := x.2.getD 0 false

/-- The game won when the second move is `true`. -/
private def secondMove (x : List Bool × List Bool) : Bool := x.2.getD 1 false

private theorem computableInPolyTime_firstMove :
    MultiTapeTM.ComputableInPolyTime firstMove (MultiTapeTM.encPair encBits encBits)
      MultiTapeTM.encBool := by
  unfold firstMove
  fun_prop

private theorem computableInPolyTime_secondMove :
    MultiTapeTM.ComputableInPolyTime secondMove (MultiTapeTM.encPair encBits encBits)
      MultiTapeTM.encBool := by
  unfold secondMove
  fun_prop

/-- The existential player wins the game of one round by moving `true`. -/
private theorem isGameVerifier_firstMove :
    IsGameVerifier encBits 1 firstMove (Set.univ : Set (List Bool)) := fun a => by
  rw [Polynomial.eval_one, show 2 * 1 = 2 * 0 + 1 + 1 from rfl, List.replicate_succ,
    alternation_true_one_cons]
  simp only [List.replicate_succ, alternation_false_one_cons, List.replicate_zero,
    alternation_nil, firstMove, List.getD_cons_zero, Set.mem_univ, true_iff]
  exact ⟨true, fun _ => rfl⟩

/-- The universal player wins the game of one round by moving `false`. -/
private theorem isGameVerifier_secondMove :
    IsGameVerifier encBits 1 secondMove (∅ : Set (List Bool)) := fun a => by
  rw [Polynomial.eval_one, show 2 * 1 = 2 * 0 + 1 + 1 from rfl, List.replicate_succ,
    alternation_true_one_cons]
  simp only [List.replicate_succ, alternation_false_one_cons, List.replicate_zero,
    alternation_nil, secondMove, List.getD_cons_succ, List.getD_cons_zero, Set.mem_empty_iff_false,
    false_iff, not_exists, not_forall]
  exact fun _ => ⟨false, Bool.false_ne_true⟩

/-- `Set.univ ∈ AP` and `∅ ∈ AP` through the guess-then-verify machine, and `AP = PSPACE`
moves problems and game verifiers between the two classes. -/
example :
    ((Set.univ : Set (List Bool)) ∈ AP encBits ∧ (∅ : Set (List Bool)) ∈ AP encBits) ∧
    ((∅ : Set (List Bool)) ∈ PSPACE encBits ∧ (Set.univ : Set (List Bool)) ∈ PSPACE encBits) ∧
    ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      MultiTapeTM.ComputableInPolyTime V (MultiTapeTM.encPair encBits encBits)
        MultiTapeTM.encBool ∧ IsGameVerifier encBits p V (Set.univ : Set (List Bool)) :=
  have huniv_pspace : (Set.univ : Set (List Bool)) ∈ PSPACE encBits :=
    AP_eq_PSPACE ▸ isGameVerifier_firstMove.mem_AP computableInPolyTime_firstMove
  ⟨⟨isGameVerifier_firstMove.mem_AP computableInPolyTime_firstMove,
    isGameVerifier_secondMove.mem_AP computableInPolyTime_secondMove⟩,
   ⟨mem_PSPACE_iff_exists_isGameVerifier.mpr
      ⟨1, secondMove, computableInPolyTime_secondMove, isGameVerifier_secondMove⟩,
    huniv_pspace⟩,
   exists_isGameVerifier_of_mem_PSPACE huniv_pspace⟩

/-! ### Single-bit moves -/

/-- The existential player chooses the first move. -/
example : Alternation true (List.replicate 2 1) fun w => w.head? = some true := by
  rw [show 2 = 2 * 1 from rfl, alternation_replicate_succ]
  exact ⟨true, fun _ => by simp⟩

/-- The universal player chooses the second move. -/
example : ¬Alternation true (List.replicate 2 1) fun w => w[1]? = some true := by
  rw [show 2 = 2 * 1 from rfl, alternation_replicate_succ]
  rintro ⟨x, h⟩
  have := h false
  simp at this

/-- A predicate ignoring the moves. -/
example : Alternation false (List.replicate 3 1) fun _ => True :=
  alternation_const.mpr trivial

/-! ### Rounds of quantifiers -/

/-- `∃ x, ∀ y, x ∨ ¬y` holds: take `x` true. -/
example : (QBF.rounds [(0, 1)] ((QBF.var 0).or (QBF.var 1).not)).eval (fun _ => false) = true := by
  decide

/-- `∃ x, ∀ y, x ↔ y` fails. -/
example : (QBF.rounds [(0, 1)] (QBF.iff (.var 0) (.var 1))).eval (fun _ => false) = false := by
  decide

/-- The same formula as a game of two moves. -/
example : ¬Alternation true (List.replicate 2 1) fun z =>
    (QBF.iff (.var 0) (.var 1)).eval (QBF.updates (fun _ => false) [0, 1] z) = true := by
  have h := QBF.eval_rounds_eq_true_iff [(0, 1)] (QBF.iff (.var 0) (.var 1)) (fun _ => false)
  simp only [QBF.roundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_singleton, mul_one] at h
  rw [← h]
  decide

/-! ### Savitch's midpoint game -/

/-- The graph with one edge, from `[false]` to `[true]`. -/
private def oneEdge (u v : List Bool) : Bool := decide (u = [false] ∧ v = [true])

/-- The midpoint `[true]` and either half win the game at level `1`. -/
example : Cslib.Reachability.midpointGame oneEdge 1 1 [false] [true] [true, false, false, true] =
    true := by
  decide

/-- The existential player wins the midpoint game from `[false]` to `[true]`. -/
example : Alternation true (List.replicate (2 * ((1 + 1) * 1)) 1)
    fun z => Cslib.Reachability.midpointGame oneEdge 1 1 [false] [true] z = true :=
  (Cslib.Reachability.alternation_midpointGame_iff 1 [false] [true]).mpr (by decide)

/-- The existential player loses the midpoint game from `[true]` to `[false]`. -/
example : ¬Alternation true (List.replicate (2 * ((1 + 1) * 1)) 1)
    fun z => Cslib.Reachability.midpointGame oneEdge 1 1 [true] [false] z = true := by
  rw [Cslib.Reachability.alternation_midpointGame_iff]
  decide

/-! ### The endpoints of a play -/

/-- Moves of two levels at width `1`: midpoint `[true]` with half `true`, then midpoint `[false]`
with half `false`. -/
private def twoHalves : List Bool := [true, false, false, true, false, true, true, false]

/-- Moves of two levels at width `1` whose halves are both `true`: midpoints `[true]`, then
`[false]`. -/
private def bothTrue : List Bool := [true, false, false, true, false, false, false, true]

/-- Each endpoint comes from the last level with its half. -/
example : Cslib.Reachability.lastMidpoint 1 2 twoHalves true = some [true] ∧
    Cslib.Reachability.lastMidpoint 1 2 twoHalves false = some [false] := by
  decide

/-- With both halves `true`, the left endpoint is the midpoint of the second level, and the right
endpoint stays the initial one. -/
example : Cslib.Reachability.lastMidpoint 1 2 bothTrue true = some [false] ∧
    Cslib.Reachability.lastMidpoint 1 2 bothTrue false = none := by
  decide

/-- The endpoint machine on `twoHalves`: the encoded options `some [true]` and `some [false]`. -/
example : Cslib.Reachability.endpointWord true (1, 2, twoHalves) = [true, true] ∧
    Cslib.Reachability.endpointWord false (1, 2, twoHalves) = [true, false] := by
  simp [twoHalves, Cslib.Reachability.endpointWord, Cslib.Reachability.levelMarks,
    Cslib.Reachability.endpointZip]

/-- The endpoint machine on `bothTrue`: the encoded options `some [false]` and `none`. -/
example : Cslib.Reachability.endpointWord true (1, 2, bothTrue) = [true, false] ∧
    Cslib.Reachability.endpointWord false (1, 2, bothTrue) = [] := by
  simp [bothTrue, Cslib.Reachability.endpointWord, Cslib.Reachability.levelMarks,
    Cslib.Reachability.endpointZip]

/-- The play of `twoHalves` from `[false]` to `[true]` ends at `[true]` and `[false]`, which are
neither equal nor an edge. -/
example : Cslib.Reachability.midpointGame oneEdge 1 2 [false] [true] twoHalves = false := by
  rw [Cslib.Reachability.midpointGame_eq_reach_lastMidpoint]
  decide

/-- Trailing moves do not change a game that reads only its first move. -/
example : Alternation true ([1] ++ [1, 1]) (fun z => z.take 1 = [true]) :=
  (alternation_append_iff fun z => by
    simp only [List.sum_cons, List.sum_nil, List.take_take]; rfl).mpr ⟨[true], rfl, rfl⟩

/-! ### Nondeterministic space as a midpoint game -/

/-- Problems in `P` are in `NSPACE (· ^ j)` for some `j`. -/
private theorem exists_mem_NSPACE_of_mem_P {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (h : A ∈ P enc) : ∃ j, A ∈ NSPACE enc (· ^ j) :=
  mem_NPSPACE_iff_exists_mem_NSPACE.mp (PSPACE_subset_NPSPACE (P_subset_PSPACE h))

/-- `Set.univ`, in `NSPACE (· ^ j)` through `P`, is a midpoint game that the existential player
wins on every instance, at every width above the bound. -/
example {α : Type} (enc : α ↪ List Bool) : ∃ (j k : ℕ) (State : Type) (_ : Finite State)
    (ntm : MultiTapeNTM k Bool State) (K : ℕ), ∀ a w,
      K * ((enc a).length + (enc a).length ^ j + 1) ≤ w →
        Alternation true (List.replicate (2 * ((2 * w + 2 + 1) * (2 * w + 2))) 1) fun z =>
          Reachability.midpointGame ntm.codeEdge (2 * w + 2) (2 * w + 2)
            (MultiTapeNTM.viewCode w (ntm.initView (enc a))) (MultiTapeNTM.acceptCode w) z =
              true := by
  obtain ⟨j, hj⟩ := exists_mem_NSPACE_of_mem_P (enc := enc) (A := Set.univ)
    ⟨fun _ => true, MultiTapeTM.ComputableInPolyTime.const _, fun _ => by simp⟩
  obtain ⟨k, State, hfin, ntm, K, h⟩ := exists_midpointGame_of_mem_NSPACE hj
  exact ⟨j, k, State, hfin, ntm, K, fun a w hw => (h a w hw).mp (Set.mem_univ a)⟩

/-- `∅`, in `NSPACE (· ^ j)` through `P`, is a midpoint game that the existential player loses on
every instance, at every width above the bound. -/
example {α : Type} (enc : α ↪ List Bool) : ∃ (j k : ℕ) (State : Type) (_ : Finite State)
    (ntm : MultiTapeNTM k Bool State) (K : ℕ), ∀ a w,
      K * ((enc a).length + (enc a).length ^ j + 1) ≤ w →
        ¬Alternation true (List.replicate (2 * ((2 * w + 2 + 1) * (2 * w + 2))) 1) fun z =>
          Reachability.midpointGame ntm.codeEdge (2 * w + 2) (2 * w + 2)
            (MultiTapeNTM.viewCode w (ntm.initView (enc a))) (MultiTapeNTM.acceptCode w) z =
              true := by
  obtain ⟨j, hj⟩ := exists_mem_NSPACE_of_mem_P (enc := enc) (A := ∅)
    ⟨fun _ => false, MultiTapeTM.ComputableInPolyTime.const _, fun _ => by simp⟩
  obtain ⟨k, State, hfin, ntm, K, h⟩ := exists_midpointGame_of_mem_NSPACE hj
  exact ⟨j, k, State, hfin, ntm, K, fun a w hw => (h a w hw).not.mp (Set.notMem_empty a)⟩

/-! ### Nondeterministic space in alternating time -/

section MidpointLeaf

open Turing.MultiTapeTM

/-- With both endpoints missing, the leaf test of the midpoint game is the edge test of the code of
the initial view and the accepting code. -/
example {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State) (w : ℕ)
    (input : List Bool) :
    ntm.midpointLeaf w input none none =
      Reachability.reach ntm.codeEdge (2 * w + 2) 0
        (MultiTapeNTM.viewCode w (ntm.initView input)) (MultiTapeNTM.acceptCode w) :=
  rfl

/-- The hypothesis on `s` is satisfiable: `s n = n` is time-constructible, so `NSPACE n` is in
`ATIME ((n + n) ^ 2)`. -/
example {α : Type} (enc : α ↪ List Bool) :
    NSPACE enc (fun n => n) ⊆ ATIME enc fun n => (n + n) ^ 2 :=
  NSPACE_subset_ATIME_sq_of_timeConstructible timeConstructible_id

end MidpointLeaf

end CslibFrontierTests.Alternation
