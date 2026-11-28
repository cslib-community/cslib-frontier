/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Midpoint
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Context
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.RadixRounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Foundations.Data.BitString.ShortWords
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Tactic.Space
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Savitch's theorem for general space bounds

A nondeterministic machine whose computation paths on an input of length `n` visit at most `S`
work cells is simulated by a deterministic machine within space `O((S + log₂ n + 1) ^ 2)`: this is
Savitch's theorem [Savitch1970]. No constructibility of `S` is assumed; as in Sipser's proof of
Theorem 8.5 [Sipser2013], the simulation tries growing bounds. It runs Savitch's midpoint recursion
(`Cslib.Reachability.reach`) on the compact configuration graph of the machine
(`Turing.MultiTapeNTM.ConfigurationGraph`), whose vertices omit the input. A vertex of the graph of
radix `B` is stored as a word of `W = O(log B)` bits, so a chain of at most `W + 1` frames of the
recursion has `O(W ^ 2)` bits. The input is never copied: the edge test at the bottom of the
recursion needs exactly one input bit, at the input head of its source vertex.

No machine is built by hand, and the recursion is not specified here: it is the midpoint
recursion `Cslib.Reachability.reach`, which
`Turing.MultiTapeTM.ComputableInSpace.reach` runs within the space of one chain of frames for any
edge test of two stored words and the input. This file supplies the edge test of the graph on
words in that form (`Turing.MultiTapeNTM.SquareSavitch.inputEdge_inSpace`); it reads the one input
bit it needs at a computed position. The search over the radices is a loop of
`Turing.MultiTapeTM.ComputableInSpace.loopWith` whose registers are the radix and the answer.

The space bound `S` is not computed. The search tries the radices
`roundRadix State n j = 4 ^ j * startRadix State n` of
`Turing.MultiTapeNTM.ConfigurationGraph.roundRadix` in turn, the radices of Immerman's inductive
counting for nondeterministic space; Sipser's proof of Theorem 8.5 likewise tries the space bounds
`1, 2, 3, …` and checks whether the machine uses more. In round `j`, a first recursion asks
whether an overflowing vertex, one with a step leaving the radix, is reachable from the start
vertex; if it is, the search moves on to round `j + 1`. Otherwise every reachable view fits the
radix, and a second recursion on the same graph asks whether an accepting halted vertex is
reachable, which decides acceptance. A machine
within space `S` has no reachable overflow from round `4 * S + 1` on
(`Turing.MultiTapeNTM.ConfigurationGraph.fits_roundRadix_of_runsInSpace`), so every round has
vertices of `O(S + log₂ n + 1)` bits. To have a single target, the graph on words gains a sink, the
word of `W` ones: every target vertex steps to it
(`Turing.MultiTapeNTM.SquareSavitch.sinkReach_eq_true_iff`).

The sublinear form of Savitch's theorem is the extension stated in the final paragraph of
Section 8.4 of Sipser's third edition, just before Section 8.5 (p. 351): "We can extend Savitch's
theorem to hold for sublinear space bounds down to f(n) ≥ log n." Sipser's Theorem 8.5 itself
assumes `f(n) ≥ n`, and Arora and Barak's Theorem 4.14 assumes a space-constructible bound
`S(n) ≥ log n`. In the extension, the machine has a read-only input tape, and the configurations of
the machine on the input `w` record the state, the work tapes and the head positions but not `w`.
Here these are the vertices of the compact configuration graph, and the edge test reads the one
input bit it needs. The sources state the theorem for languages decided by
nondeterministic machines whose branches all halt; the statement here also covers machines that
only recognize the problem (branches may run forever), arbitrary per-instance bounds without
constructibility, and arbitrary instances under an encoding into `List Bool`.

## Main definitions

* `Turing.MultiTapeNTM.SquareSavitch.wordEdge`: the edges of the graph on words, given the round
  mode and the input bit at the source.
* `Turing.MultiTapeNTM.SquareSavitch.sinkReach`: the recursion from the start vertex to the sink.
* `Turing.MultiTapeNTM.SquareSavitch.search`: a round of the search over the radices.

## Main results

* `Turing.MultiTapeNTM.SquareSavitch.sinkReach_true_iff`,
  `Turing.MultiTapeNTM.SquareSavitch.sinkReach_false_iff`: the recursion decides reachable overflow,
  and without it acceptance.
* `Turing.MultiTapeNTM.exists_decidableInTimeAndSpace_sq`: **Savitch's theorem**: a problem
  recognized by a nondeterministic machine within space `S` is decided by a deterministic machine
  within space `O((S + log₂ n + 1) ^ 2)`.
* `Turing.MultiTapeNTM.SquareSavitch.inputEdge_inSpace`: the edge test, from two stored words,
  the stored radix and the input.
* `Turing.MultiTapeNTM.SquareSavitch.sinkReach_inSpace`: the recursion of a round within the space
  of its frames.

## References

* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]; journal text not inspected (paywalled), so no theorem number or
  page is cited.
* [M. Sipser, *Introduction to the Theory of Computation*, 3rd edition, Theorem 8.5 and its proof,
  and Section 8.4, final paragraph (p. 351)][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.14][AroraBarak09]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
-/

public section

namespace Turing.MultiTapeNTM.SquareSavitch

open MultiTapeTM ConfigurationGraph Cslib.Reachability
open Cslib.BitString (lowBits length_lowBits lsbValue_replicate_true)

/-! ### The graph on words -/

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)

/-- The targets of a round, given the input bit `symbol` at the vertex: the overflowing vertices
in overflow mode, and the accepting halted vertices otherwise. -/
noncomputable def target (overflowMode : Bool) (B n : ℕ) (symbol : Option Bool) (u : ℕ) : Bool :=
  if overflowMode then overflow ntm B n u symbol else bad (k := k) (State := State) B n u

/-- **The edges of the graph on words**, given the round mode and the input bit `symbol` at the
source: the edges of the compact configuration graph between the values of the words, and an edge
from every target vertex to the sink, the word of ones. -/
noncomputable def wordEdge (overflowMode : Bool) (B n : ℕ) (symbol : Option Bool)
    (u v : List Bool) : Bool :=
  edgeWithSymbol ntm B n (ofBits u) (ofBits v) symbol ||
    (target ntm overflowMode B n symbol (ofBits u) && v.all id)

/-- The edges of the graph on words on the input `w`: the input bit is read at the input head of
the source. -/
noncomputable def inputEdge (overflowMode : Bool) (B : ℕ) (w : List Bool) (u v : List Bool) :
    Bool :=
  wordEdge ntm overflowMode B w.length w[queryIndex (k := k) B (ofBits u)]? u v

/-- The target test on an actual input, reading the bit at `queryIndex`. -/
def Target (overflowMode : Bool) (B : ℕ) (w : List Bool) (u : ℕ) : Prop :=
  target ntm overflowMode B w.length w[queryIndex (k := k) B u]? u = true

/-- **The recursion of a round**: Savitch's midpoint recursion at depth `W = vertexWidth k B` on
the graph on words of width `W`, from the start vertex to the sink. -/
noncomputable def sinkReach (overflowMode : Bool) (B : ℕ) (w : List Bool) : Bool :=
  reach (inputEdge ntm overflowMode B w) (vertexWidth k B) (vertexWidth k B)
    (lowBits (vertexWidth k B) (startID ntm B)) (List.replicate (vertexWidth k B) true)

/-- Some overflowing vertex is reachable in the graph of radix `B`. -/
def OverflowReachable (B : ℕ) (w : List Bool) : Prop :=
  ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧ Overflow ntm B w u

/-! ### Reachability of the sink -/

section Graph

variable {ntm} {B : ℕ} {w : List Bool}

/-- No vertex is the sink. -/
private theorem vertexBound_le_ofBits_sink (B : ℕ) :
    vertexBound (k := k) B ≤ ofBits (List.replicate (vertexWidth k B) true) := by
  have h := lsbValue_replicate_true (vertexWidth k B)
  have := vertexBound_lt_two_pow_vertexWidth k B
  rw [ofBits_eq_lsbValue]
  omega

/-- Every target is a vertex of the graph. -/
private theorem lt_vertexBound_of_target {overflowMode : Bool} {n u : ℕ} {symbol : Option Bool}
    (h : target ntm overflowMode B n symbol u = true) : u < vertexBound (k := k) B := by
  cases overflowMode
  · simp only [target, Bool.false_eq_true, ↓reduceIte, bad, Bool.and_eq_true] at h
    exact lt_vertexBound_of_valid h.1.1
  · simp only [target, ↓reduceIte, overflow, Bool.and_eq_true] at h
    exact lt_vertexBound_of_valid h.1

/-- **The sink is reachable exactly when a target is.** Along the graph on words of width
`W = vertexWidth k B`, from the start vertex to the word of `W` ones. -/
theorem reflTransGen_sink_iff {overflowMode : Bool}
    (hstart : startID ntm B < vertexBound (k := k) B) :
    Relation.ReflTransGen (fun a b => a.length = vertexWidth k B ∧ b.length = vertexWidth k B ∧
        inputEdge ntm overflowMode B w a b = true)
      (lowBits (vertexWidth k B) (startID ntm B)) (List.replicate (vertexWidth k B) true) ↔
      ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
        Target ntm overflowMode B w u := by
  have hW := vertexBound_lt_two_pow_vertexWidth k B
  have hsink := vertexBound_le_ofBits_sink (k := k) B
  set W := vertexWidth k B
  have hsrc : ofBits (lowBits W (startID ntm B)) = startID ntm B :=
    ofBits_lowBits (hstart.trans hW)
  constructor
  · intro h
    have key : ∀ x, Relation.ReflTransGen (fun a b => a.length = W ∧ b.length = W ∧
          inputEdge ntm overflowMode B w a b = true) (lowBits W (startID ntm B)) x →
        (∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
          Target ntm overflowMode B w u) ∨
        (Relation.ReflTransGen (Edge ntm B w) (startID ntm B) (ofBits x) ∧
          x ≠ List.replicate W true) := by
      intro x hx
      induction hx with
      | refl =>
        refine .inr ⟨by rw [hsrc], fun h => ?_⟩
        have := congrArg ofBits h
        omega
      | @tail x y _ hxy ih =>
        obtain ⟨-, -, he⟩ := hxy
        rcases ih with ih | ⟨hr, -⟩
        · exact .inl ih
        simp only [inputEdge, wordEdge, Bool.or_eq_true, Bool.and_eq_true] at he
        rcases he with he | ⟨hb, -⟩
        · refine .inr ⟨hr.tail he, fun h => ?_⟩
          have := (lt_vertexBound_of_edgeWithSymbol he).2
          rw [h] at this
          omega
        · exact .inl ⟨_, hr, hb⟩
    rcases key _ h with h | ⟨-, h⟩
    · exact h
    · exact absurd rfl h
  · rintro ⟨u, hu, hb⟩
    have key : ∀ x, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) x →
        Relation.ReflTransGen (fun a b => a.length = W ∧ b.length = W ∧
          inputEdge ntm overflowMode B w a b = true) (lowBits W (startID ntm B)) (lowBits W x) ∧
        x < vertexBound (k := k) B := by
      intro x hx
      induction hx with
      | refl => exact ⟨.refl, hstart⟩
      | @tail a b _ hab ih =>
        have hlt := lt_vertexBound_of_edgeWithSymbol hab
        refine ⟨ih.1.tail ⟨length_lowBits _ _, length_lowBits _ _, ?_⟩, hlt.2⟩
        simp only [inputEdge, wordEdge, ofBits_lowBits (hlt.1.trans hW),
          ofBits_lowBits (hlt.2.trans hW)]
        rw [show edgeWithSymbol ntm B w.length a b w[queryIndex (k := k) B a]? = true from hab,
          Bool.true_or]
    have hu' : u < vertexBound (k := k) B := lt_vertexBound_of_target hb
    have hb' : target ntm overflowMode B w.length w[queryIndex (k := k) B u]? u = true := hb
    refine (key u hu).1.tail ⟨length_lowBits _ _, List.length_replicate, ?_⟩
    simp only [inputEdge, wordEdge, ofBits_lowBits (hu'.trans hW), hb', Bool.true_and,
      Bool.or_eq_true]
    exact .inr (by simp)

/-- **The recursion of a round decides whether a target is reachable**, for every radix above the
finite tags. -/
theorem sinkReach_eq_true_iff {overflowMode : Bool} (hB : Fintype.card (Option State) + 1 < B) :
    sinkReach ntm overflowMode B w = true ↔
      ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
        Target ntm overflowMode B w u := by
  have hstart := startID_lt (ntm := ntm) (k := k) hB
  have hsrc : (lowBits (vertexWidth k B) (startID ntm B)).length = vertexWidth k B :=
    length_lowBits _ _
  have hcard : {x | Relation.ReflTransGen (fun a b => a.length = vertexWidth k B ∧
      b.length = vertexWidth k B ∧ inputEdge ntm overflowMode B w a b = true)
      (lowBits (vertexWidth k B) (startID ntm B)) x}.encard ≤ 2 ^ vertexWidth k B + 1 := by
    refine (Set.encard_le_encard fun x hx => ?_).trans
      ((Cslib.BitString.encard_setOf_length_eq _).le.trans le_self_add)
    induction hx with
    | refl => exact hsrc
    | tail _ hstep _ => exact hstep.2.1
  rw [sinkReach, reach_iff hsrc List.length_replicate,
    ← Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard,
    reflTransGen_sink_iff hstart]

/-- **The overflow round decides reachable overflow.** -/
theorem sinkReach_true_iff (hB : Fintype.card (Option State) + 1 < B) :
    sinkReach ntm true B w = true ↔ OverflowReachable ntm B w :=
  sinkReach_eq_true_iff hB

/-- **Without reachable overflow, the acceptance round decides acceptance.** -/
theorem sinkReach_false_iff (hB : Fintype.card (Option State) + 1 < B)
    (hno : ¬ OverflowReachable ntm B w) :
    sinkReach ntm false B w = true ↔ ntm.Accepts w := by
  rw [accepts_iff_reachable_bad
    (fits_of_not_overflow (fits_init hB) fun u hu ho => hno ⟨u, hu, ho⟩),
    sinkReach_eq_true_iff hB]
  rfl

/-- **The late rounds have no reachable overflow**: for a machine within space `S`, from round
`4 * S + 1` on. -/
theorem not_overflowReachable_of_runsInSpace {S j : ℕ} (hs : ntm.RunsInSpace w S)
    (hj : 4 * S + 1 ≤ j) : ¬ OverflowReachable ntm (roundRadix State w.length j) w :=
  fun ⟨u, hu, ho⟩ => not_overflow_of_fits
    (fun _ hv => fits_roundRadix_of_runsInSpace hs hj hv) u hu ho

end Graph

/-! ### A round of the search, within the space of its frames -/

/-- The registers of the search over the radices. -/
structure SearchState where
  /-- The radix of the round. -/
  radix : ℕ
  /-- The answer, once it is known. -/
  answer : Option Bool

/-- The binary radix, framed, and the optional answer, in field order. -/
enc_structure encSearch : SearchState where radix : encNat, answer : (encOption encBool)

section Round

open ComputableInSpace

variable {α : Type} (enc : α ↪ List Bool)

/-- The registers of an edge test in a round: two stored words, framed, and the registers of the
search. -/
abbrev encEdgeRegisters : (List Bool × List Bool) × SearchState ↪ List Bool :=
  encPair (encPair encBits encBits) encSearch

attribute [local fun_prop] edgeWithSymbol_budget overflow_budget bad_budget

/-- **The edge test of the graph on words**, from two stored words, the stored radix and the
input: within the stored words and registers and the logarithm of the length of the input. The
one input bit is read at the input head of the source. -/
theorem inputEdge_inSpace (mode : Bool) :
    ComputableInSpace
      (fun q : ((List Bool × List Bool) × SearchState) × α =>
        inputEdge ntm mode q.1.2.radix (enc q.2) q.1.1.1 q.1.1.2)
      (encPair encEdgeRegisters enc) encBool
      fun q => (encEdgeRegisters q.1).length + Nat.log2 (enc q.2).length := by
  have hreg := budget_registers (encR := encEdgeRegisters) (encA := enc) (.refl _)
  have hn := budget_inputLength (encR := encEdgeRegisters) (encA := enc) (.refl _)
  have hbit := budget_inputBit (queryIndex_budget (k := k) (encSearch_radix_budget hreg.snd')
    (budget_ofBits hreg.fst'.fst')) (.refl _)
  space [inputEdge, wordEdge, target]

/-- The budget of a round at the radix of the registers: `W + 1` frames of `O(W)` bits for
vertices of `W` bits, the registers and the logarithm of the length of the input. -/
abbrev roundBudget (p : SearchState × α) : ℕ :=
  (vertexWidth k p.1.radix + 1) *
    (vertexWidth k p.1.radix + (encSearch p.1).length + Nat.log2 (enc p.2).length + 1)

/-- **The recursion of a round, within the space of its frames.** From the stored radix and the
input, the midpoint recursion at depth `W`, the width of the vertices, from the start vertex to
the sink is computable within space `O((W + 1) * (W + log₂ B + log₂ n + 1))`
(`Turing.MultiTapeTM.ComputableInSpace.reach`). -/
theorem sinkReach_inSpace (mode : Bool) :
    ComputableInSpace (fun p : SearchState × α => sinkReach ntm mode p.1.radix (enc p.2))
      (encPair encSearch enc) encBool (roundBudget (k := k) enc) := by
  -- the width and the endpoints, from the stored radix
  let S (p : SearchState × α) : ℕ :=
    vertexWidth k p.1.radix + (encSearch p.1).length + Nat.log2 (enc p.2).length
  have hctx : CoversContext encSearch enc S := .of_le fun p => by dsimp only [S]; omega
  have hB := encSearch_radix_budget (budget_registers hctx)
  have hN := vertexBound_budget (k := k) hB
  have hWu : ComputableInSpace (fun p : SearchState × α => vertexWidth k p.1.radix)
      (encPair encSearch enc) encUnary S :=
    (budget_comp_linear natSizeUnary hN).of_enc_eq fun _ => rfl
  have hWb : ComputableInSpace (fun p : SearchState × α => vertexWidth k p.1.radix)
      (encPair encSearch enc) encNat S :=
    (budget_comp_linear natSize hN).of_enc_eq fun _ => rfl
  have hpair := budget_prod hWb (startID_budget ntm hB)
  have hsrc : ComputableInSpace
      (fun p : SearchState × α => lowBits (vertexWidth k p.1.radix) (startID ntm p.1.radix))
      (encPair encSearch enc) encBits S :=
    budget_comp_linear listToBits ((lowBits_inSpace.comp hpair).weaken
      (.add (.refl _) (.add (.of_le fun p => by dsimp only [S]; omega) hpair.length_le)))
  have hreach := reach (S := S) (edge := fun p => inputEdge ntm mode p.1.radix (enc p.2))
    (E := fun p => 9 * vertexWidth k p.1.radix + 2 * (encSearch p.1).length +
      2 * Nat.log2 (enc p.2).length + 8)
    hWu hWb hsrc (budget_bitsReplicate true hWu) (assoc_context (inputEdge_inSpace ntm enc mode))
    (fun p x y hx hy => by
      simp only [length_encPair, encBits_apply, hx, hy]
      omega)
    fun p => ⟨length_lowBits _ _, List.length_replicate⟩
  refine (hreach.of_enc_eq fun _ => rfl).weaken ⟨16, fun p => ?_⟩
  have h₁ := log2_length_encPair_le encSearch enc p
  have h₂ := Nat.log2_le_self (vertexWidth k p.1.radix)
  dsimp only [S, roundBudget]
  nlinarith

/-- **A round of the search**: an overflow round that finds overflow moves to the next radix; one
that finds none is followed by the acceptance round at the same radix, whose value is the answer;
with an answer the search stops. -/
noncomputable def search (p : SearchState × α) : Option SearchState :=
  if p.1.answer.isSome then none
  else if sinkReach ntm true p.1.radix (enc p.2) then some ⟨4 * p.1.radix, none⟩
  else some ⟨p.1.radix, some (sinkReach ntm false p.1.radix (enc p.2))⟩

/-- A round of the search, within the budget of a round. -/
theorem search_inSpace : ComputableInSpace (search ntm enc) (encPair encSearch enc)
    (encOption encSearch) (roundBudget (k := k) enc) := by
  have hreg := budget_registers (encR := encSearch) (encA := enc) (Bs := roundBudget (k := k) enc)
    (.of_le fun p => by dsimp only [roundBudget]; nlinarith)
  have hover := sinkReach_inSpace ntm enc true
  have haccept := sinkReach_inSpace ntm enc false
  space [search]

end Round

variable (k State) in
/-- The constant factor of the width of the vertices in the rounds of a run. -/
noncomputable def widthConst : ℕ :=
  Fintype.card (Register k) * (Fintype.card (Option State) + 8) + 1

end Turing.MultiTapeNTM.SquareSavitch

namespace Turing.MultiTapeNTM

open MultiTapeTM ConfigurationGraph SquareSavitch ComputableInSpace

/-- **Savitch's theorem** [Savitch1970], for general space bounds. No constructibility is assumed:
the machine tries growing bounds, as in Sipser's proof of Theorem 8.5 [Sipser2013]. A
problem recognized by a nondeterministic machine whose computation paths on `enc a` visit at most
`S a` work cells, and whose branches need not halt, is decided by a deterministic machine within
space `O((S a + log₂ |enc a| + 1) ^ 2)`: a search over the radices of the compact configuration
graph of the machine (`Turing.MultiTapeNTM.SquareSavitch.search`), whose rounds run Savitch's
midpoint recursion on a chain of frames (`Turing.MultiTapeNTM.SquareSavitch.sinkReach_inSpace`). -/
theorem exists_decidableInTimeAndSpace_sq {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State} {S : α → ℕ}
    (hA : ntm.RecognizesInSpace enc A S) :
    ∃ t c, DecidableInTimeAndSpace A enc t
      fun a => c * (S a + Nat.log2 (enc a).length + 1) ^ 2 := by
  classical
  let : Fintype State := Fintype.ofFinite State
  -- the first round without reachable overflow
  have hex (a : α) : ∃ j, ¬ OverflowReachable ntm (roundRadix State (enc a).length j) (enc a) :=
    ⟨_, not_overflowReachable_of_runsInSpace (hA a).1 le_rfl⟩
  have hJ (a : α) : Nat.find (hex a) ≤ 4 * S a + 1 :=
    Nat.find_min' (hex a) (not_overflowReachable_of_runsInSpace (hA a).1 le_rfl)
  have hB (a : α) (j : ℕ) := card_lt_roundRadix (State := State) (enc a).length j
  -- the first radix
  have hinit : ComputableInSpace
      (fun a => (⟨roundRadix State (enc a).length 0, none⟩ : SearchState)) enc encSearch
      fun a => Nat.log2 (enc a).length :=
    (encSearch_mk_budget (budget_natMul (budget_natAdd (inputLength enc) (budget_const 2))
      (budget_const _)) (budget_const none)).of_enc_eq fun a => by rw [roundRadix_zero]; rfl
  have hloop := loopWith (step := search ntm enc)
    (B := fun a => (widthConst k State + 1) * (widthConst k State +
      2 * (Fintype.card (Option State) + 9) + 6) * (S a + Nat.log2 (enc a).length + 1) ^ 2)
    (fun a j => if j ≤ Nat.find (hex a) then ⟨roundRadix State (enc a).length j, none⟩
      else ⟨roundRadix State (enc a).length (Nat.find (hex a)), some (decide (a ∈ A))⟩)
    (fun a => Nat.find (hex a) + 1) hinit (search_inSpace ntm enc)
    (fun a => by simp)
    (fun a j hj => ?_) (fun a => by simp [search]) (fun a j hj => ?_)
  · obtain ⟨t, c, h, -⟩ := ((budget_optionGetD false (encSearch_answer_budget hloop)).of_enc_eq
      (encC := encBool) (g := fun a => decide (a ∈ A)) fun a => by simp).weaken
        (S₁ := fun a => (S a + Nat.log2 (enc a).length + 1) ^ 2)
        ⟨(widthConst k State + 1) * (widthConst k State +
          2 * (Fintype.card (Option State) + 9) + 6) + 2, fun a => by
          have : 1 ≤ (S a + Nat.log2 (enc a).length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
          have : Nat.log2 (enc a).length ≤ (S a + Nat.log2 (enc a).length + 1) ^ 2 :=
            (show _ ≤ S a + Nat.log2 (enc a).length + 1 by omega).trans
              (Nat.le_self_pow two_ne_zero _)
          nlinarith⟩
    exact ⟨t, 2 * c, decidableInTimeAndSpace_iff.mpr ⟨_, h.mono (fun _ => le_rfl) fun a => by
      have : 1 ≤ (S a + Nat.log2 (enc a).length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith, fun a => by simp⟩⟩
  · -- a round maps the registers to the next ones
    rcases Nat.lt_succ_iff.mp hj |>.lt_or_eq with hlt | rfl
    · have ho : sinkReach ntm true (roundRadix State (enc a).length j) (enc a) = true :=
        (sinkReach_true_iff (hB a j)).mpr (not_not.mp (Nat.find_min (hex a) hlt))
      simp only [hlt.le, ↓reduceIte, Nat.succ_le_of_lt hlt, search, Option.isSome_none,
        Bool.false_eq_true, ho, roundRadix_succ]
    · have hno := Nat.find_spec (hex a)
      have ho : sinkReach ntm true (roundRadix State (enc a).length (Nat.find (hex a))) (enc a) =
          false := Bool.eq_false_iff.mpr fun h => hno ((sinkReach_true_iff (hB a _)).mp h)
      have hacc : sinkReach ntm false (roundRadix State (enc a).length (Nat.find (hex a)))
          (enc a) = decide (a ∈ A) := by
        rw [Bool.eq_iff_iff, sinkReach_false_iff (hB a _) hno, decide_eq_true_iff]
        exact (hA a).2.symm
      simp only [le_refl, ↓reduceIte, search, Option.isSome_none, Bool.false_eq_true,
        ho, hacc, Nat.not_succ_le_self]
  · -- the budget of a round on the registers of the run
    obtain ⟨j', hj', o, hr⟩ : ∃ j' ≤ Nat.find (hex a), ∃ o : Option Bool,
        (if j ≤ Nat.find (hex a) then (⟨roundRadix State (enc a).length j, none⟩ : SearchState)
          else ⟨roundRadix State (enc a).length (Nat.find (hex a)), some (decide (a ∈ A))⟩) =
          ⟨roundRadix State (enc a).length j', o⟩ := by
      split_ifs with h
      · exact ⟨j, h, none, rfl⟩
      · exact ⟨_, le_rfl, _, rfl⟩
    rw [hr]
    have hj'S := hj'.trans (hJ a)
    have hW := vertexWidth_roundRadix_le k State (enc a).length j'
    have hBl : (encNat (roundRadix State (enc a).length j')).length ≤
        2 * j' + Nat.log2 (enc a).length + Fintype.card (Option State) + 5 := by
      rw [length_encNat_eq_size, Nat.size_le]
      exact (roundRadix_le_two_pow (State := State) (enc a).length j').trans_lt
        (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have ho : (encOption encBool o).length ≤ 2 := by rcases o with _ | b <;> simp
    simp only [roundBudget, encSearch_apply, encSearchFields, length_encPair]
    unfold widthConst
    generalize Fintype.card (Register k) = R at *
    generalize Fintype.card (Option State) = q at *
    generalize vertexWidth k (roundRadix State (enc a).length j') = W at *
    generalize (encNat (roundRadix State (enc a).length j')).length = Bl at *
    generalize (encOption encBool o).length = ol at *
    generalize hL : S a + Nat.log2 (enc a).length + 1 = L
    have hL1 : 1 ≤ L := by omega
    have hW' : W ≤ (R * (q + 8) + 1) * L := by
      have : 2 * j' + Nat.log2 (enc a).length + q + 4 ≤ (q + 8) * L := by nlinarith
      nlinarith
    have hBl' : Bl ≤ (q + 9) * L := by nlinarith
    generalize R * (q + 8) + 1 = Wc at *
    generalize Nat.log2 (enc a).length = ℓ at *
    have h₁ : W + 1 ≤ (Wc + 1) * L := by nlinarith
    have h₂ : W + (2 * Bl + 1 + ol) + ℓ + 1 ≤ (Wc + 2 * (q + 9) + 6) * L := by nlinarith
    calc (W + 1) * (W + (2 * Bl + 1 + ol) + ℓ + 1)
        ≤ (Wc + 1) * L * ((Wc + 2 * (q + 9) + 6) * L) := Nat.mul_le_mul h₁ h₂
      _ = (Wc + 1) * (Wc + 2 * (q + 9) + 6) * L ^ 2 := by ring

end Turing.MultiTapeNTM
