/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.NondeterministicChoice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

/-!
# Bounded same-input walk

A destination choice is followed by a deterministic adjacency call on the original word.
Only the false selector continues through deterministic steps. Successful walks return the
unused edge budget, and an invalid destination, exhausted budget or failed edge rejects.
The native compiler fixes the graph dimension and adjacency call clock. The original input
can still supply both endpoints and the edge budget.

## Main results

* `firstHalting_remainingFuel_iff` characterizes successful first halts by typed walks.
* `haltsWithin` and `length_run_le` bound all branches, including rejection.
* `exists_routines` compiles the walk from linear-space adjacency routines.
* `native_firstHalting_accept_iff` gives the exact accepting native traces.
-/

public section

namespace Turing.DoubleCounting.BoundedWalk

open Cslib.DoubleCounting.Scan.Binary

/-- The live registers of a bounded walk. -/
structure Registers (N : ℕ) where
  /-- Current vertex at the next destination boundary. -/
  current : Fin N
  /-- Target at which a stop is allowed. -/
  target : Fin N
  /-- Number of edges still permitted. -/
  fuel : ℕ

/-- Read binary endpoint ranks at a positive dimension, reducing each rank modulo the size. -/
@[expose] def Registers.ofRanks {N : ℕ} (positive : 0 < N) (current target fuel : ℕ) :
    Registers N :=
  ⟨⟨current % N, Nat.mod_lt _ positive⟩, ⟨target % N, Nat.mod_lt _ positive⟩, fuel⟩

/-- Reading the ranks of typed registers recovers those registers. -/
theorem Registers.ofRanks_val {N : ℕ} (positive : 0 < N) (r : Registers N) :
    Registers.ofRanks positive r.current.val r.target.val r.fuel = r := by
  cases r with
  | mk current target fuel =>
    simp only [ofRanks, Nat.mod_eq_of_lt current.isLt, Nat.mod_eq_of_lt target.isLt]

/-- Control state of the walk. A running adjacency call retains the destination and registers. -/
inductive State (N : ℕ) (τ : Type)
  | choose (registers : Registers N) (choice : NondeterministicChoice.State)
  | call (registers : Registers N) (destination : Fin N) (remaining : ℕ) (callee : τ)
  | done (result : Option ℕ)

variable {N : ℕ} {τ : Type}

private def boundary (r : Registers N) : State N τ :=
  .choose r (NondeterministicChoice.machine N).init

/-- Read the unused edge budget at a successful halt. -/
def remainingFuel : State N τ → Option ℕ
  | .done answer => answer
  | _ => none

/-- Detect the terminal phase, including rejecting halts. -/
def halted : State N τ → Bool
  | .done _ => true
  | _ => false

/-- Return the active callee's input position, or zero outside a call. -/
def query (calleeQuery : τ → ℕ) : State N τ → ℕ
  | .call _ _ _ s => calleeQuery s
  | _ => 0

/-- Update an active adjacency call. A completed successful call moves to its destination
and starts a fresh choice. -/
def advanceCall (edge : QueryMachine τ) (verdict : τ → Bool) (r : Registers N) (v : Fin N)
    (remaining : ℕ) (s : τ) (answer : Option Bool) (selector : Bool) : State N τ :=
  if selector then .done none
  else match remaining with
    | 0 => if edge.halted s && verdict s then boundary { r with current := v } else .done none
    | steps + 1 => .call r v steps (if edge.halted s then s else edge.next (s, answer))

/-- Consume a destination selector or route a completed choice. A valid continuation
spends one edge of fuel and enters the supplied adjacency subroutine. -/
def advanceChoice (start : Fin N → Fin N → τ) (clock : ℕ) (r : Registers N)
    (s : NondeterministicChoice.State) (selector : Bool) : State N τ :=
  if NondeterministicChoice.isHalted s then
    if selector then .done none
    else if s.stopped then .done (if r.current = r.target then some r.fuel else none)
    else
      match r.fuel, VertexReader.result s.reader with
      | fuel + 1, some v =>
        if hv : v < N then
          .call { r with fuel := fuel } ⟨v, hv⟩ clock (start r.current ⟨v, hv⟩)
        else .done none
      | _, _ => .done none
  else .choose r (NondeterministicChoice.advance s selector)

/-- Dispatch a walk transition from its phase, input reply, and selector. -/
def advance (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) : State N τ × Option Bool × Bool → State N τ
  | (.choose r s, _, selector) => advanceChoice start clock r s selector
  | (.call r v remaining s, answer, selector) =>
    advanceCall edge verdict r v remaining s answer selector
  | (.done r, _, _) => .done r

/-- The bounded walk with a supplied same-input adjacency subroutine and a common clock
for its calls. Each call uses the clock even if the subroutine halts earlier. -/
def machine (edge : QueryMachine τ) (start : Fin N → Fin N → τ) (verdict : τ → Bool)
    (clock : ℕ) (initial : Registers N) : NondeterministicQueryMachine (State N τ) where
  init := boundary initial
  query := query edge.query
  next := advance edge start verdict clock
  halted := halted
  accept s := (remainingFuel s).isSome

/-- The walk machine uses the same query observer at every entry. -/
theorem machine_query (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (initial : Registers N) :
    (machine edge start verdict clock initial).query = query edge.query := by
  unfold machine
  rfl

/-- The walk machine detects halt using only the phase. -/
theorem machine_halted (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (initial : Registers N) :
    (machine edge start verdict clock initial).halted = halted := by
  unfold machine
  rfl

/-- The transition dispatcher is independent of the initial registers. -/
theorem machine_next (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (initial : Registers N) :
    (machine edge start verdict clock initial).next = advance edge start verdict clock := by
  unfold machine
  rfl

/-- On a destination choice the machine uses the same routing at every entry. -/
theorem machine_next_choice (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (initial r : Registers N)
    (s : NondeterministicChoice.State) (answer : Option Bool) (selector : Bool) :
    (machine edge start verdict clock initial).next (.choose r s, answer, selector) =
      advanceChoice start clock r s selector := by
  unfold machine advance
  rfl

/-- On an active call the machine uses the call update for any initialization. -/
theorem machine_next_call (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (initial r : Registers N) (v : Fin N)
    (remaining : ℕ) (s : τ) (answer : Option Bool) (selector : Bool) :
    (machine edge start verdict clock initial).next (.call r v remaining s, answer, selector) =
      advanceCall edge verdict r v remaining s answer selector := by
  unfold machine advance
  rfl

/-- Changing the walk registers at entry leaves all transitions and verdicts unchanged. -/
theorem machine_withInit (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (initial registers : Registers N) :
    (machine edge start verdict clock initial).withInit
      (machine edge start verdict clock registers).init =
        machine edge start verdict clock registers := by
  unfold machine NondeterministicQueryMachine.withInit
  rfl

section Bounds

variable (edge : QueryMachine τ) (start : Fin N → Fin N → τ) (verdict : τ → Bool)
  (clock : ℕ) (initial : Registers N) (input : List Bool)

local notation "M" => machine edge start verdict clock initial
local notation "C" => NondeterministicChoice.machine N

private def widthInvariant : State N τ → Prop
  | .choose _ choice => choice.reader.width = N.size
  | _ => True

private def rank (N clock : ℕ) : State N τ → ℕ
  | .choose r s => r.fuel * (N.size + clock + 3) +
      if s.stopped then 1 else if s.reading then N.size - s.reader.cursor + 1 else N.size + 2
  | .call r _ ticks _ => r.fuel * (N.size + clock + 3) + (N.size + 2) + (ticks + 1)
  | .done _ => 0

private theorem rank_decreases (s : State N τ) (selector : Bool)
    (hs : widthInvariant s) (hlive : (M).halted s = false) :
    widthInvariant ((M).step input s selector) ∧
      rank N clock ((M).step input s selector) < rank N clock s := by
  cases s with
  | done answer => cases hlive
  | choose r choice =>
    change choice.reader.width = N.size at hs
    simp only [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
      machine, halted, Bool.false_eq_true, ite_false, advance, advanceChoice]
    split
    · have hpos : 0 < rank N clock (State.choose r choice : State N τ) := by
        cases hstop : choice.stopped <;> cases hread : choice.reading <;>
          simp [rank, hstop, hread]
      split
      · exact ⟨trivial, hpos⟩
      · split
        · exact ⟨trivial, hpos⟩
        · cases hfuel : r.fuel with
          | zero => exact ⟨trivial, hpos⟩
          | succ fuel =>
            cases VertexReader.result choice.reader with
            | none => exact ⟨trivial, hpos⟩
            | some v =>
              by_cases hv : v < N
              · simp only [dite_eq_left hv]
                refine ⟨trivial, ?_⟩
                cases hstop : choice.stopped <;> cases hread : choice.reading <;>
                  simp [rank, hfuel, Nat.succ_mul, hstop, hread] <;> omega
              · simp only [dite_eq_right hv]
                exact ⟨trivial, hpos⟩
    · rename_i hnot
      have h := Bool.eq_false_iff.mpr hnot
      have hstopped : choice.stopped = false := by
        cases hs' : choice.stopped
        · rfl
        · simp [NondeterministicChoice.isHalted, hs'] at h
      cases hreading : choice.reading
      · cases selector <;>
          simp [NondeterministicChoice.advance, hreading, widthInvariant, rank, hs, hstopped]
      · have hlt : choice.reader.cursor < N.size := by
          simpa [NondeterministicChoice.isHalted, VertexReader.isHalted, hreading, hstopped, hs]
            using h
        simp [NondeterministicChoice.advance, hreading, widthInvariant, rank,
          VertexReader.advance, hs, hstopped]
        omega
  | call r v remaining s =>
    simp only [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
      machine, halted, Bool.false_eq_true, ite_false, advance, advanceCall]
    cases selector
    · cases remaining
      · by_cases hs' : (edge.halted s && verdict s) = true
        · rw [ite_eq_left hs']
          exact ⟨rfl, by simp [rank, boundary, NondeterministicChoice.machine]⟩
        · rw [ite_eq_right hs']
          exact ⟨trivial, by simp [rank]⟩
      · simp [widthInvariant, rank]
    · simp [widthInvariant, rank]

/-- The common clock includes destination bits, the routing step, and adjacency return.
It bounds every branch, including failed calls and bad deterministic selectors. -/
theorem haltsWithin :
    (M).HaltsWithin input (initial.fuel * (N.size + clock + 3) + (N.size + 2)) := by
  have aux (choices : List Bool) (s : State N τ) (hs : widthInvariant s)
      (ht : rank N clock s ≤ choices.length) :
      (M).halted ((M).replay input choices s) = true := by
    induction choices generalizing s with
    | nil =>
      rw [NondeterministicQueryMachine.replay_nil]
      by_contra h
      have hlt := (rank_decreases edge start verdict clock initial input s false hs
        (Bool.eq_false_iff.mpr h)).2
      simp only [List.length_nil] at ht
      omega
    | cons selector rest ih =>
      rw [NondeterministicQueryMachine.replay_cons]
      cases h : (M).halted s with
      | true =>
        rw [(M).step_of_halted input h, (M).replay_of_halted input h]
        exact h
      | false =>
        have ⟨hInv, hRank⟩ := rank_decreases edge start verdict clock initial input
          s selector hs h
        exact ih _ hInv (by simp only [List.length_cons] at ht; omega)
  intro choices hlen
  apply aux choices (M).init
  · rfl
  · simp [machine, boundary, rank, NondeterministicChoice.machine, hlen]

end Bounds

section Workspace

open MultiTapeTM

private abbrev encVertex (N : ℕ) : Fin N ↪ List Bool := Fin.valEmbedding.trans encNat

/-- Binary current vertex and target, both framed, then the remaining binary fuel. -/
enc_structure encRegisters (N : ℕ) : Registers N where
  current : ((Fin.valEmbedding : Fin N ↪ ℕ).trans encNat),
  target : ((Fin.valEmbedding : Fin N ↪ ℕ).trans encNat),
  fuel : encNat

private def stateView (N : ℕ) (τ : Type) :
    State N τ ≃ (Registers N × NondeterministicChoice.State) ⊕
      ((Registers N × Fin N × ℕ × τ) ⊕ Option ℕ) where
  toFun
    | .choose r s => .inl (r, s)
    | .call r v ticks s => .inr (.inl (r, v, ticks, s))
    | .done answer => .inr (.inr answer)
  invFun
    | .inl (r, s) => .choose r s
    | .inr (.inl (r, v, ticks, s)) => .call r v ticks s
    | .inr (.inr result) => .done result
  left_inv := by intro s; cases s <;> rfl
  right_inv := by rintro (⟨r, s⟩ | (⟨r, v, ticks, s⟩ | result)) <;> rfl

private abbrev encChoose (N : ℕ) :=
  encPair (encRegisters N) NondeterministicChoice.encState

private abbrev encCallFields {ρ ν : Type} (encReg : ρ ↪ List Bool)
    (encDest : ν ↪ List Bool) (encCallee : τ ↪ List Bool) :=
  encPair encReg (encPair encDest (encPair encNat encCallee))

private abbrev encCall (N : ℕ) (encCallee : τ ↪ List Bool) :=
  encCallFields (encRegisters N) (encVertex N) encCallee

private abbrev encView (N : ℕ) (encCallee : τ ↪ List Bool) :=
  encSum (encChoose N) (encSum (encCall N encCallee) (encOption encNat))

/-- Tagged choice, suspended adjacency call, or final optional fuel. Vertices and clocks
use binary encodings, and the call stores the supplied callee encoding. -/
def encState (encCallee : τ ↪ List Bool) : State N τ ↪ List Bool :=
  encOfEquiv (stateView N τ) (encView N encCallee)

/-- A choice-phase word tags the framed register word followed by the destination reader. -/
def choiceWord (registers : List Bool) (reader : NondeterministicChoice.State) : List Bool :=
  encSum (encPair encBits NondeterministicChoice.encState) encBits (.inl (registers, reader))

private theorem encState_choice (encCallee : τ ↪ List Bool) (r : Registers N)
    (s : NondeterministicChoice.State) :
    encState encCallee (.choose r s) = choiceWord (encRegisters N r) s := rfl

/-- A walk entry encodes the supplied registers and the initial destination reader. -/
theorem encState_init (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) (r : Registers N) (encCallee : τ ↪ List Bool) :
    encState encCallee (machine edge start verdict clock r).init =
      choiceWord (encRegisters N r) (NondeterministicChoice.machine N).init := by
  unfold machine boundary
  exact encState_choice encCallee r _

variable (edge : QueryMachine τ) (start : Fin N → Fin N → τ) (verdict : τ → Bool)
  (clock : ℕ) (initial : Registers N) (input : List Bool)

local notation "M" => machine edge start verdict clock initial
local notation "C" => NondeterministicChoice.machine N

private theorem step_choose {r : Registers N} {s : NondeterministicChoice.State}
    (hlive : (C).halted s = false) (selector : Bool) :
    (M).step input (.choose r s) selector = .choose r ((C).step input s selector) := by
  have hchoice : NondeterministicChoice.isHalted s = false := hlive
  simp only [NondeterministicQueryMachine.step, machine, halted, Bool.false_eq_true, ite_false,
    advance, advanceChoice, hlive, hchoice]
  rfl

private theorem step_call_succ (r : Registers N) (v : Fin N) (ticks : ℕ) (s : τ) :
    (M).step input (.call r v (ticks + 1) s) false = .call r v ticks (edge.step input s) := by
  rfl

private def reachablePhase : State N τ → Prop
  | .choose r s => r.fuel ≤ initial.fuel ∧ ∃ bits, (C).run input bits = s
  | .call r v ticks s => r.fuel ≤ initial.fuel ∧
      ∃ t, t + ticks = clock ∧ edge.runFrom input (start r.current v) t = s
  | .done answer => ∀ fuel ∈ answer, fuel ≤ initial.fuel

private theorem boundary_reachable (r : Registers N) (h : r.fuel ≤ initial.fuel) :
    reachablePhase edge start clock initial input (boundary r) := ⟨h, [], rfl⟩

private theorem step_reachable (s : State N τ) (selector : Bool)
    (hs : reachablePhase edge start clock initial input s) :
    reachablePhase edge start clock initial input ((M).step input s selector) := by
  cases s with
  | done answer => exact hs
  | choose r choice =>
    obtain ⟨hfuel, bits, rfl⟩ := hs
    by_cases hc : (C).halted ((C).run input bits) = true
    · change NondeterministicChoice.isHalted ((C).run input bits) = true at hc
      simp only [NondeterministicQueryMachine.step, machine, halted, Bool.false_eq_true,
        ite_false, advance, advanceChoice, hc, ite_true]
      cases selector
      · simp only [Bool.false_eq_true, ite_false]
        split
        · intro f hf
          split at hf
          · have he : f = r.fuel := by simpa using hf.symm
            exact he ▸ hfuel
          · simp at hf
        · cases hr : r.fuel <;> cases VertexReader.result (((C).run input bits).reader)
          all_goals try exact fun _ h => by simp at h
          rename_i fuel v
          by_cases hv : v < N
          · simp only [dite_eq_left hv]
            exact ⟨show fuel ≤ initial.fuel by omega, 0, by simp, rfl⟩
          · simp only [dite_eq_right hv]
            exact fun _ h => by simp at h
      · exact fun _ h => by simp at h
    · rw [step_choose edge start verdict clock initial input (Bool.eq_false_iff.mpr hc)]
      exact ⟨hfuel, bits ++ [selector], (C).run_append input bits [selector]⟩
  | call r v ticks callee =>
    obtain ⟨hfuel, t, ht, rfl⟩ := hs
    cases selector
    · cases ticks
      · simp only [NondeterministicQueryMachine.step, machine, halted, Bool.false_eq_true,
          ite_false, advance, advanceCall]
        split
        · exact boundary_reachable edge start clock initial input _ hfuel
        · exact fun _ h => by simp at h
      · rw [step_call_succ edge start verdict clock initial input]
        exact ⟨hfuel, t + 1, by omega, QueryMachine.runFrom_succ _ _ _ _⟩
    · exact fun _ h => by simp at h

private theorem run_reachable (choices : List Bool) :
    reachablePhase edge start clock initial input ((M).run input choices) := by
  have aux (s : State N τ) (hs : reachablePhase edge start clock initial input s) :
      reachablePhase edge start clock initial input ((M).replay input choices s) := by
    induction choices generalizing s with
    | nil => exact hs
    | cons selector rest ih =>
      rw [NondeterministicQueryMachine.replay_cons]
      exact ih _ (step_reachable edge start verdict clock initial input s selector hs)
  exact aux _ (boundary_reachable edge start clock initial input initial le_rfl)

/-- Every encoded branch state fits the vertex and fuel registers, the bounded reader,
and at most one suspended adjacency call. The callee bound covers every call prefix. -/
theorem length_run_le (encCallee : τ ↪ List Bool) (calleeBound : ℕ)
    (hcallee : ∀ (u v : Fin N) t, t ≤ clock →
      (encCallee (edge.runFrom input (start u v) t)).length ≤ calleeBound)
    (choices : List Bool) :
    (encState encCallee ((M).run input choices)).length ≤
      12 * (encNat N).length + 4 * (Nat.log2 N.size + 1) +
      4 * (encNat initial.fuel).length + 2 * (encNat clock).length + calleeBound + 21 := by
  have hvertex (v : Fin N) : (encVertex N v).length ≤ (encNat N).length :=
    length_encNat_mono v.isLt.le
  have hregisters (r : Registers N) (hr : r.fuel ≤ initial.fuel) :
      (encRegisters N r).length ≤ 4 * (encNat N).length + (encNat initial.fuel).length + 2 := by
    simp only [encRegisters_apply, encRegistersFields, length_encPair]
    have hc := hvertex r.current
    have ht := hvertex r.target
    dsimp only [encVertex] at hc ht
    have hf := length_encNat_mono hr
    omega
  have hN : N.size = (encNat N).length := by rw [encNat_apply, Nat.size_eq_bits_len]
  have hreach := run_reachable edge start verdict clock initial input choices
  generalize (M).run input choices = state at hreach ⊢
  cases state with
  | choose r s =>
    obtain ⟨hr, bits, rfl⟩ := hreach
    have hs := NondeterministicChoice.length_run_le N input bits
    have hreg := hregisters r hr
    have henc : encState encCallee (.choose r ((C).run input bits)) =
        false :: encPair (encRegisters N) NondeterministicChoice.encState
          (r, (C).run input bits) := rfl
    simp only [henc, List.length_cons, length_encPair]
    omega
  | call r v ticks s =>
    obtain ⟨hr, t, ht, rfl⟩ := hreach
    have hreg := hregisters r hr
    have hv := hvertex v
    have hticks := length_encNat_mono (show ticks ≤ clock by omega)
    have hc := hcallee r.current v t (by omega)
    have henc : encState encCallee (.call r v ticks (edge.runFrom input (start r.current v) t)) =
        true :: false :: encPair (encRegisters N)
          (encPair (encVertex N) (encPair encNat encCallee))
          (r, v, ticks, edge.runFrom input (start r.current v) t) := rfl
    simp only [henc, List.length_cons, length_encPair]
    omega
  | done answer =>
    cases answer with
    | none => simp [encState, encOfEquiv, stateView]
    | some fuel =>
      have hf := length_encNat_mono (hreach fuel (by simp))
      simp only [encNat_apply] at hf
      simp [encState, encOfEquiv, stateView]
      omega

end Workspace

section Replay

open Cslib.DoubleCounting.Scan

variable (edge : QueryMachine τ) (start : Fin N → Fin N → τ) (verdict : τ → Bool)
  (clock : ℕ) (initial : Registers N) (input : List Bool)

local notation "M" => machine edge start verdict clock initial
local notation "C" => NondeterministicChoice.machine N

/-- Serialize one walk. Genuine destination bits use the canonical vertex encoding.
The other selectors are false, for the routing step and the clocked adjacency call. -/
def selectors (clock : ℕ) : List (Fin N) → List Bool
  | [] => [false, false]
  | v :: vs => (true :: vertex v) ++ List.replicate (clock + 2) false ++ selectors clock vs

/-- A complete walk selector can be a prefix of another only for the same destination list. -/
theorem eq_of_selectors_prefix (clock : ℕ) {a b : List (Fin N)}
    (h : selectors clock a <+: selectors clock b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons v vs => simp [selectors] at h
  | cons u us ih =>
    cases b with
    | nil => simp [selectors] at h
    | cons v vs =>
      simp only [selectors, List.cons_append, List.cons_prefix_cons, true_and,
        List.append_assoc] at h
      have hprefix : vertex u <+: vertex v :=
        List.prefix_of_prefix_length_le ((List.prefix_append _ _).trans h)
          (List.prefix_append _ _) (by simp)
      have hword : vertex u = vertex v := hprefix.eq_of_length (by simp)
      have huv : u = v := Option.some.inj
        (((decodeVertex_eq_some_iff _ u).2 rfl).symm.trans
          ((decodeVertex_eq_some_iff _ v).2 hword))
      subst v
      rw [List.prefix_append_right_inj, List.prefix_append_right_inj] at h
      exact congrArg (u :: ·) (ih h)

private theorem replay_choice_of_live (r : Registers N) (bits : List Bool)
    (s : NondeterministicChoice.State)
    (hlive : ∀ i < bits.length, (C).halted ((C).replay input (bits.take i) s) = false) :
    (M).replay input bits (.choose r s) = .choose r ((C).replay input bits s) :=
  (M).replay_map_of_live input (C) (State.choose r)
    (fun _ bit h => step_choose edge start verdict clock initial input h bit) bits s hlive

private theorem replay_choice (r : Registers N) (bits : List Bool)
    (s : NondeterministicChoice.State) (hfirst : (C).FirstHalting input bits s) :
    (M).replay input bits (.choose r s) = .choose r ((C).replay input bits s) :=
  replay_choice_of_live edge start verdict clock initial input r bits s hfirst.2

private theorem replay_call (r : Registers N) (v : Fin N) (ticks : ℕ) (s : τ) :
    (M).replay input (List.replicate ticks false) (.call r v ticks s) =
      .call r v 0 (edge.runFrom input s ticks) := by
  induction ticks generalizing s with
  | zero => rfl
  | succ ticks ih =>
    rw [List.replicate_succ, NondeterministicQueryMachine.replay_cons,
      step_call_succ edge start verdict clock initial input, ih]
    rw [show ticks + 1 = 1 + ticks by omega, QueryMachine.runFrom_add]
    rfl

private theorem route_stop (r : Registers N) (s : NondeterministicChoice.State)
    (hh : (C).halted s = true) (hs : s.stopped = true) :
    (M).step input (.choose r s) false =
      .done (if r.current = r.target then some r.fuel else none) := by
  change NondeterministicChoice.isHalted s = true at hh
  simp [NondeterministicQueryMachine.step, machine, halted, advance, advanceChoice, hh, hs]

private theorem route_vertex (r : Registers N) (s : NondeterministicChoice.State)
    (hh : (C).halted s = true) (hs : s.stopped = false) (v : Fin N)
    (hv : VertexReader.result s.reader = some v.val) :
    (M).step input (.choose r s) false =
      match r.fuel with
      | 0 => .done none
      | fuel + 1 => .call { r with fuel := fuel } v clock (start r.current v) := by
  change NondeterministicChoice.isHalted s = true at hh
  cases hf : r.fuel <;> simp [NondeterministicQueryMachine.step, machine, halted,
    advance, advanceChoice,
    hh, hs, hv, hf, v.isLt]

private def walkResult (adjacent : Fin N → Fin N → Bool) (r : Registers N)
    (tail : List (Fin N)) : Option ℕ :=
  (walkM readNext (fun u v => pure (adjacent u v)) r.target r.fuel r.current tail).1

private theorem route_invalid (r : Registers N) (s : NondeterministicChoice.State)
    (hh : (C).halted s = true) (hs : s.stopped = false)
    (hv : VertexReader.result s.reader = none) :
    (M).step input (.choose r s) false = .done none := by
  change NondeterministicChoice.isHalted s = true at hh
  cases hf : r.fuel <;>
    simp [NondeterministicQueryMachine.step, machine, halted, advance, advanceChoice,
      hh, hs, hv, hf]

private theorem replay_edge (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (r : Registers N) (v : Fin N) :
    (M).replay input ((true :: vertex v) ++ List.replicate (clock + 2) false) (boundary r) =
      match r.fuel with
      | 0 => .done none
      | fuel + 1 => if adjacent r.current v then boundary { r with current := v, fuel := fuel }
                    else .done none := by
  have ⟨hfirst, _, hresult⟩ :=
    (NondeterministicChoice.firstHalting_vertex_iff N input (true :: vertex v) v).mpr rfl
  have hstop : ((C).run input (true :: vertex v)).stopped = false := by
    rw [NondeterministicChoice.run_continue]
  rw [NondeterministicQueryMachine.replay_append, boundary,
    replay_choice edge start verdict clock initial input r _ _ hfirst,
    show clock + 2 = (clock + 1) + 1 by rfl,
    List.replicate_succ, NondeterministicQueryMachine.replay_cons,
    route_vertex edge start verdict clock initial input r _ hfirst.1 hstop v hresult]
  cases r.fuel with
  | zero =>
    rw [(M).replay_of_halted input (show (M).halted (.done none) = true by rfl)]
  | succ fuel =>
    rw [List.replicate_add, NondeterministicQueryMachine.replay_append,
      replay_call edge start verdict clock initial input,
      show List.replicate 1 false = [false] by rfl, NondeterministicQueryMachine.replay_cons,
      NondeterministicQueryMachine.replay_nil]
    simp [NondeterministicQueryMachine.step, machine, halted, advance, advanceCall, hclock, hedge]

private theorem replay_boundary (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (r : Registers N) (tail : List (Fin N)) :
    (M).replay input (selectors clock tail) (boundary r) = .done (walkResult adjacent r tail) := by
  induction tail generalizing r with
  | nil =>
    have ⟨hfirst, hstop⟩ := (NondeterministicChoice.firstHalting_stop_iff N input [false]).mpr rfl
    change (M).replay input ([false] ++ [false]) (boundary r) = _
    rw [NondeterministicQueryMachine.replay_append, boundary,
      replay_choice edge start verdict clock initial input r _ _ hfirst,
      NondeterministicQueryMachine.replay_cons,
      route_stop edge start verdict clock initial input r _ hfirst.1 hstop,
      NondeterministicQueryMachine.replay_nil, walkResult, walkM]
    rfl
  | cons v tail ih =>
    rw [selectors, NondeterministicQueryMachine.replay_append,
      replay_edge edge start verdict clock initial input adjacent hclock hedge r v,
      walkResult, walkM]
    cases hfuel : r.fuel with
    | zero =>
      rw [(M).replay_of_halted input (show (M).halted (.done none) = true by rfl)]
      rfl
    | succ fuel =>
      by_cases he : adjacent r.current v = true
      · simp only [he, ite_true]
        rw [ih]
        simp [walkResult, bind, StateT.bind, readNext, pure, StateT.pure, he]
      · simp only [he, Bool.false_eq_true, ite_false]
        rw [(M).replay_of_halted input (show (M).halted (.done none) = true by rfl)]
        simp [bind, StateT.bind, readNext, pure, StateT.pure, he]

private theorem live_before_stop (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (r : Registers N) (tail : List (Fin N)) {left : ℕ}
    (hs : walkResult adjacent r tail = some left) :
    ∃ pre, selectors clock tail = pre ++ [false] ∧
      (M).halted ((M).replay input pre (boundary r)) = false := by
  induction tail generalizing r with
  | nil =>
    have ⟨hfirst, _⟩ := (NondeterministicChoice.firstHalting_stop_iff N input [false]).mpr rfl
    refine ⟨[false], rfl, ?_⟩
    rw [boundary, replay_choice edge start verdict clock initial input r _ _ hfirst]
    rfl
  | cons v tail ih =>
    cases hfuel : r.fuel with
    | zero =>
      rw [walkResult, walkM, hfuel] at hs
      cases hs
    | succ fuel =>
      by_cases he : adjacent r.current v = true
      · have hrest :
          walkResult adjacent { r with current := v, fuel := fuel } tail = some left := by
          unfold walkResult at hs ⊢
          rw [walkM, hfuel] at hs
          simpa [bind, StateT.bind, readNext, pure, StateT.pure, he] using hs
        obtain ⟨pre, hpre, hlive⟩ := ih _ hrest
        let edgeSelectors := (true :: vertex v) ++ List.replicate (clock + 2) false
        refine ⟨edgeSelectors ++ pre, ?_, ?_⟩
        · simp only [edgeSelectors, selectors, hpre, List.append_assoc]
        · dsimp only [edgeSelectors]
          rw [NondeterministicQueryMachine.replay_append,
            replay_edge edge start verdict clock initial input adjacent hclock hedge r v,
            hfuel]
          simpa only [he, ite_true] using hlive
      · rw [walkResult, walkM, hfuel] at hs
        simp [bind, StateT.bind, readNext, pure, StateT.pure, he] at hs

/-- On the canonical selectors for any typed destination list, the returned fuel
agrees with the existing scan's walk, using the subroutine verdict on the original input. -/
theorem run_selectors (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (tail : List (Fin N)) :
    (M).run input (selectors clock tail) =
      .done ((walkM readNext (fun u v => pure (adjacent u v))
        initial.target initial.fuel initial.current tail).1) :=
  replay_boundary edge start verdict clock initial input adjacent hclock hedge initial tail

private theorem firstHalting_selectors (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (tail : List (Fin N)) {left : ℕ}
    (hs : (walkM readNext (fun u v => pure (adjacent u v))
      initial.target initial.fuel initial.current tail).1 = some left) :
    (M).FirstHalting input (selectors clock tail) (M).init ∧
      remainingFuel ((M).run input (selectors clock tail)) = some left := by
  have hr := run_selectors edge start verdict clock initial input adjacent hclock hedge tail
  rw [hs] at hr
  refine ⟨?_, by rw [hr]; rfl⟩
  obtain ⟨pre, hpre, hlive⟩ :=
    live_before_stop edge start verdict clock initial input adjacent hclock hedge initial tail hs
  rw [hpre]
  refine (M).firstHalting_append_singleton input pre false hlive ?_
  rw [← hpre]
  change (M).halted ((M).run input (selectors clock tail)) = true
  rw [hr]
  rfl

/-- An out-of-range fixed-width destination rejects before any adjacency call. -/
theorem run_invalid_vertex (bits : List Bool) (hwidth : bits.length = N.size)
    (hinvalid : decodeVertex (N := N) bits = none) :
    (M).run input (true :: (bits ++ [false])) = .done none := by
  have hfirst := (NondeterministicChoice.firstHalting_continue_iff N input bits).mpr hwidth
  have hstop : ((C).run input (true :: bits)).stopped = false := by
    rw [NondeterministicChoice.run_continue]
  have hresult : VertexReader.result ((C).run input (true :: bits)).reader = none := by
    rw [NondeterministicChoice.result_run_continue N input bits hwidth, hinvalid]
    rfl
  change (M).replay input ((true :: bits) ++ [false]) (boundary initial) = _
  rw [NondeterministicQueryMachine.replay_append, boundary,
    replay_choice edge start verdict clock initial input initial _ _ hfirst,
    NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.replay_nil]
  exact route_invalid edge start verdict clock initial input initial _ hfirst.1 hstop hresult

private theorem firstHalting_suffix (pre rest : List Bool) (s : State N τ)
    (hf : (M).FirstHalting input (pre ++ rest) s) :
    (M).FirstHalting input rest ((M).replay input pre s) := by
  induction pre generalizing s with
  | nil => exact hf
  | cons b pre ih =>
    exact ih _ (((M).firstHalting_cons_iff input b (pre ++ rest) s).mp hf).2

private theorem choice_prefix (r : Registers N) (bits : List Bool) {left : ℕ}
    (hret : (M).replay input bits (boundary r) = .done (some left)) :
    ∃ pre rest, bits = pre ++ rest ∧ (C).FirstHalting input pre (C).init := by
  have hhalt : (C).halted ((C).run input bits) = true := by
    by_contra h
    have hpre (i : ℕ) (_ : i < bits.length) :
        (C).halted ((C).replay input (bits.take i) (C).init) = false := by
      by_contra hi
      have hit := Bool.eq_true_of_not_eq_false hi
      apply h
      rw [NondeterministicQueryMachine.run, ← List.take_append_drop i bits,
        NondeterministicQueryMachine.replay_append, (C).replay_of_halted input hit]
      exact hit
    rw [boundary,
      replay_choice_of_live edge start verdict clock initial input r bits _ hpre] at hret
    cases hret
  obtain ⟨pre, ⟨⟨rest, hsplit⟩, hf, _⟩, _⟩ :=
    (C).existsUnique_firstHalting_prefix input hhalt
  exact ⟨pre, rest, hsplit.symm, hf⟩

private theorem successful_call (r : Registers N) (v : Fin N) (ticks : ℕ) (s : τ)
    (bits : List Bool) {left : ℕ}
    (hr : (M).replay input bits (.call r v ticks s) = .done (some left)) :
    ∃ rest, bits = List.replicate (ticks + 1) false ++ rest ∧
      verdict (edge.runFrom input s ticks) = true ∧
      (M).replay input rest (boundary {r with current := v}) = .done (some left) := by
  induction ticks generalizing s bits with
  | zero =>
    cases bits with
    | nil => cases hr
    | cons b rest =>
      rw [NondeterministicQueryMachine.replay_cons] at hr
      cases b
      · by_cases h : (edge.halted s && verdict s) = true
        · have hv := (Bool.and_eq_true_iff.mp h).2
          exact ⟨rest, rfl, hv, by
            simpa [NondeterministicQueryMachine.step, machine, halted, advance, advanceCall, h]
              using hr⟩
        · have hstep : (M).step input (.call r v 0 s) false = .done none := by
            simp [NondeterministicQueryMachine.step, machine, halted, advance, advanceCall, h]
          rw [hstep, (M).replay_of_halted input (show (M).halted (.done none) = true by rfl)] at hr
          cases hr
      · have hstep : (M).step input (.call r v 0 s) true = .done none := rfl
        rw [hstep, (M).replay_of_halted input (show (M).halted (.done none) = true by rfl)] at hr
        cases hr
  | succ ticks ih =>
    cases bits with
    | nil => cases hr
    | cons b rest =>
      rw [NondeterministicQueryMachine.replay_cons] at hr
      cases b
      · rw [step_call_succ edge start verdict clock initial input] at hr
        obtain ⟨suffix, hsplit, hret, hrest⟩ := ih _ _ hr
        refine ⟨suffix, ?_, ?_, hrest⟩
        · rw [hsplit]
          rfl
        · rw [show ticks + 1 = 1 + ticks by omega, QueryMachine.runFrom_add]
          exact hret
      · have hstep : (M).step input (.call r v (ticks + 1) s) true = .done none := rfl
        rw [hstep, (M).replay_of_halted input (show (M).halted (.done none) = true by rfl)] at hr
        cases hr

private theorem successful_walk (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (r : Registers N) (bits : List Bool) {left : ℕ}
    (hf : (M).FirstHalting input bits (boundary r))
    (hret : (M).replay input bits (boundary r) = .done (some left)) :
    ∃ tail, bits = selectors clock tail ∧ walkResult adjacent r tail = some left := by
  induction hr : r.fuel using Nat.strong_induction_on generalizing r bits with
  | ind fuel ih =>
    obtain ⟨pre, rest, rfl, hfirst⟩ :=
      choice_prefix edge start verdict clock initial input r bits hret
    have hsuffix := firstHalting_suffix edge start verdict clock initial input pre rest _ hf
    rw [NondeterministicQueryMachine.replay_append, boundary,
      replay_choice edge start verdict clock initial input r _ _ hfirst] at hret
    rw [boundary, replay_choice edge start verdict clock initial input r _ _ hfirst] at hsuffix
    cases rest with
    | nil => cases hret
    | cons b rest =>
      rw [NondeterministicQueryMachine.replay_cons] at hret
      have hlast := (((M).firstHalting_cons_iff input b rest _).mp hsuffix).2
      cases b
      · let s := (C).run input pre
        have hh : (C).halted s = true := hfirst.1
        have haccept : (C).accept s = true := by
          cases hs : s.stopped
          · have hreading : s.reading = true := by
              change NondeterministicChoice.isHalted s = true at hh
              exact (Bool.and_eq_true_iff.mp (by
                simpa [NondeterministicChoice.isHalted, hs] using hh)).1
            cases hv : VertexReader.result s.reader
            · change (M).replay input rest ((M).step input (.choose r s) false) = _ at hret
              rw [route_invalid edge start verdict clock initial input r s hh hs hv,
                (M).replay_of_halted input (show (M).halted (.done none) = true by rfl)] at hret
              cases hret
            · simp [NondeterministicChoice.machine, hs, hreading, hv]
          · simp [NondeterministicChoice.machine, hs]
        rcases (NondeterministicChoice.firstHalting_accept_iff N input pre).mp ⟨hfirst, haccept⟩
          with hstop | ⟨v, hvertex⟩
        · subst pre
          have hflag := (NondeterministicChoice.firstHalting_stop_iff N input [false]).mpr rfl |>.2
          rw [route_stop edge start verdict clock initial input r _ hfirst.1 hflag] at hret hlast
          cases rest with
          | nil =>
            refine ⟨[], rfl, ?_⟩
            rw [walkResult, walkM]
            exact State.done.inj hret
          | cons b rest =>
            have hbad := (((M).firstHalting_cons_iff input b rest _).mp hlast).1
            cases hbad
        · subst pre
          have hdecode := (NondeterministicChoice.firstHalting_vertex_iff N input _ v).mpr rfl
          have hstop : ((C).run input (true :: vertex v)).stopped = false := by
            rw [NondeterministicChoice.run_continue]
          rw [route_vertex edge start verdict clock initial input r _ hfirst.1 hstop v hdecode.2.2]
            at hret hlast
          cases hfuel : r.fuel with
          | zero =>
            rw [hfuel,
              (M).replay_of_halted input (show (M).halted (.done none) = true by rfl)] at hret
            cases hret
          | succ k =>
            rw [hfuel] at hret hlast
            obtain ⟨suffix, hsplit, hgood, hnext⟩ :=
              successful_call edge start verdict clock initial input {r with fuel := k} v clock
                (start r.current v) rest (left := left) hret
            have he : adjacent r.current v = true := (hedge r.current v).symm.trans hgood
            subst rest
            have hsuffix' := firstHalting_suffix edge start verdict clock initial input
              (List.replicate (clock + 1) false) suffix _ hlast
            rw [List.replicate_add, NondeterministicQueryMachine.replay_append,
              replay_call edge start verdict clock initial input,
              show List.replicate 1 false = [false] by rfl,
              NondeterministicQueryMachine.replay_cons,
              NondeterministicQueryMachine.replay_nil] at hsuffix'
            have hcallback := hclock r.current v
            simp only [NondeterministicQueryMachine.step, machine, halted, Bool.false_eq_true,
              ite_false, advance, advanceCall, hcallback, hgood, Bool.and_self, ite_true]
              at hsuffix'
            obtain ⟨tail, htail, hwalk⟩ := ih k (by omega) _ _ hsuffix' hnext rfl
            refine ⟨v :: tail, ?_, ?_⟩
            · simp only [selectors, htail, List.replicate_succ, List.cons_append, List.append_assoc]
            · unfold walkResult at hwalk ⊢
              rw [walkM, hfuel]
              simpa [bind, StateT.bind, readNext, pure, StateT.pure, he] using hwalk
      · have hh : NondeterministicChoice.isHalted ((C).run input pre) = true := hfirst.1
        have hstep : (M).step input (.choose r ((C).run input pre)) true = .done none := by
          simp [NondeterministicQueryMachine.step, machine, halted, advance, advanceChoice, hh]
        change (M).replay input rest ((M).step input (.choose r ((C).run input pre)) true) = _
          at hret
        rw [hstep, (M).replay_of_halted input (show (M).halted (.done none) = true by rfl)] at hret
        cases hret

/-- Successful first halts are exactly the canonical selectors of successful typed walks. -/
theorem firstHalting_remainingFuel_iff (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v)
    (bits : List Bool) (left : ℕ) :
    (M).FirstHalting input bits (M).init ∧ remainingFuel ((M).run input bits) = some left ↔
      ∃ tail, bits = selectors clock tail ∧
        (walkM readNext (fun u v => pure (adjacent u v))
          initial.target initial.fuel initial.current tail).1 = some left := by
  constructor
  · rintro ⟨hf, hresult⟩
    have hret : (M).run input bits = .done (some left) := by
      cases he : (M).run input bits
      · rw [he] at hresult
        cases hresult
      · rw [he] at hresult
        cases hresult
      · rw [he] at hresult
        exact congrArg State.done hresult
    exact successful_walk edge start verdict clock initial input adjacent hclock hedge
      initial bits hf hret
  · rintro ⟨tail, rfl, hwalk⟩
    exact firstHalting_selectors edge start verdict clock initial input adjacent hclock hedge
      tail hwalk

end Replay

section Native

open MultiTapeTM ComputableInSpace

variable {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ} {encCallee : τ ↪ List Bool}

/-- Assemble a walk's binary register word even when the vertex count depends on the input. -/
theorem registersWord_budget {dimension : α → ℕ} {r : (a : α) → Registers (dimension a)}
    (hcurrent : ComputableInSpace (fun a => (r a).current.val) encIn encNat budget)
    (htarget : ComputableInSpace (fun a => (r a).target.val) encIn encNat budget)
    (hfuel : ComputableInSpace (fun a => (r a).fuel) encIn encNat budget) :
    ComputableInSpace (fun a => encRegisters (dimension a) (r a)) encIn encBits budget :=
  (budget_prod hcurrent (budget_prod htarget hfuel)).of_enc_eq fun _ => rfl

private theorem registerFields_budget {dimension : α → ℕ} {r : (a : α) → Registers (dimension a)}
    (hr : ComputableInSpace (fun a => encRegisters (dimension a) (r a)) encIn encBits budget) :
    ComputableInSpace (fun a => ((r a).current.val, (r a).target.val, (r a).fuel))
      encIn (encPair encNat (encPair encNat encNat)) budget :=
  hr.of_enc_eq fun _ => rfl

/-- Build choice-phase words from registers and a reader supplied within the same budget.
The register word can encode a carrier that varies with the input. -/
theorem choiceWord_budget {r : α → List Bool} {s : α → NondeterministicChoice.State}
    (hr : ComputableInSpace r encIn encBits budget)
    (hs : ComputableInSpace s encIn NondeterministicChoice.encState budget) :
    ComputableInSpace (fun a => choiceWord (r a) (s a)) encIn encBits budget :=
  (budget_comp_linear (of_inO (ComputableInO.inl
    (encPair encBits NondeterministicChoice.encState) encBits)) (budget_prod hr hs)).of_enc_eq
      fun _ => rfl

private theorem choose_budget {r : α → Registers N} {s : α → NondeterministicChoice.State}
    (hr : ComputableInSpace r encIn (encRegisters N) budget)
    (hs : ComputableInSpace s encIn NondeterministicChoice.encState budget) :
    ComputableInSpace (fun a => State.choose (r a) (s a)) encIn (encState encCallee) budget :=
  (choiceWord_budget (hr.of_enc_eq fun _ => rfl) hs).of_enc_eq fun _ => rfl

/-- Load a walk boundary from certified endpoint and fuel registers. -/
theorem init_budget (edge : QueryMachine τ) (start : Fin N → Fin N → τ)
    (verdict : τ → Bool) (clock : ℕ) {registers : α → Registers N}
    (hr : ComputableInSpace registers encIn (encRegisters N) budget) :
    ComputableInSpace (fun a => (machine edge start verdict clock (registers a)).init)
      encIn (encState encCallee) budget :=
  choose_budget hr
    ((ComputableInSpace.constZero (NondeterministicChoice.machine N).init).mono_le
      fun _ => Nat.zero_le _)

private abbrev encCallWord (encCallee : τ ↪ List Bool) :=
  encCallFields encBits encNat encCallee

private theorem callWord_budget {dimension : α → ℕ} {r : (a : α) → Registers (dimension a)}
    {v : (a : α) → Fin (dimension a)} {ticks : α → ℕ} {s : α → τ}
    (hr : ComputableInSpace (fun a => encRegisters (dimension a) (r a)) encIn encBits budget)
    (hv : ComputableInSpace (fun a => (v a).val) encIn encNat budget)
    (hticks : ComputableInSpace ticks encIn encNat budget)
    (hs : ComputableInSpace s encIn encCallee budget) :
    ComputableInSpace (fun a => encState encCallee (.call (r a) (v a) (ticks a) (s a)))
      encIn encBits budget :=
  let right := encSum (encCallWord encCallee) (encOption encNat)
  (budget_comp_linear (of_inO (ComputableInO.inr encBits right))
    (budget_comp_linear (of_inO (ComputableInO.inl (encCallWord encCallee) (encOption encNat)))
      (budget_prod hr (budget_prod hv (budget_prod hticks hs))))).of_enc_eq fun _ => rfl

private theorem doneWord_budget {dimension : α → ℕ} {f : α → Option ℕ}
    (hf : ComputableInSpace f encIn (encOption encNat) budget) :
    ComputableInSpace
      (fun a => encState encCallee (.done (N := dimension a) (f a))) encIn encBits budget :=
  let right := encSum (encCallWord encCallee) (encOption encNat)
  (budget_comp_linear (of_inO (ComputableInO.inr encBits right))
    (budget_comp_linear (of_inO (ComputableInO.inr (encCallWord encCallee) (encOption encNat)))
      hf)).of_enc_eq fun _ => rfl

private theorem done_budget {f : α → Option ℕ}
    (hf : ComputableInSpace f encIn (encOption encNat) budget) :
    ComputableInSpace (fun a => State.done (N := N) (τ := τ) (f a)) encIn
      (encState encCallee) budget :=
  (doneWord_budget (dimension := fun _ => N) (encCallee := encCallee) hf).of_enc_eq fun _ => rfl

variable (edge : QueryMachine τ) (start : Fin N → Fin N → τ) (verdict : τ → Bool)
  (clock : ℕ) (initial : Registers N)

local notation "M" => machine edge start verdict clock initial
local notation "C" => NondeterministicChoice.machine N

private abbrev encAnswer := encPair (encOption encBool) encBool

/-- Certify destination choice at a dimension computed by the caller. The supplied start
certificate prepares the callee for any candidate whose binary ID fits the budget. -/
theorem advanceChoice_budget {dimension : α → ℕ} {r : (a : α) → Registers (dimension a)}
    {reader : α → NondeterministicChoice.State}
    {start : (a : α) → Fin (dimension a) → Fin (dimension a) → τ}
    (clock : ℕ) {selector : α → Bool}
    (hdim : ComputableInSpace dimension encIn encNat budget)
    (hr : ComputableInSpace (fun a => encRegisters (dimension a) (r a)) encIn encBits budget)
    (hreader : ComputableInSpace reader encIn NondeterministicChoice.encState budget)
    (hselector : ComputableInSpace selector encIn encBool budget)
    (hstart : ∀ v : (a : α) → Fin (dimension a),
      ComputableInSpace (fun a => (v a).val) encIn encNat budget →
      ComputableInSpace (fun a => start a (r a).current (v a)) encIn encCallee budget) :
    ComputableInSpace (fun a => encState encCallee
      (advanceChoice (start a) clock (r a) (reader a) (selector a)))
      encIn encBits budget := by
  have hregs := registerFields_budget hr
  have hcurrent := fst' hregs
  have htarget := fst' (snd' hregs)
  have hfuel := snd' (snd' hregs)
  have hh := budget_comp_linear NondeterministicChoice.isHalted_inSpace hreader
  have hstop := NondeterministicChoice.encState_stopped_budget hreader
  have hvOpt := budget_comp_linear VertexReader.result_inSpace
    (NondeterministicChoice.encState_reader_budget hreader)
  have hvNat := budget_optionGetD 0 hvOpt
  let v (a : α) : Fin (dimension a) :=
    ⟨(VertexReader.result (reader a).reader).getD 0 % dimension a,
      Nat.mod_lt _ (Nat.zero_lt_of_lt (r a).current.isLt)⟩
  have hv : ComputableInSpace (fun a => (v a).val) encIn encNat budget :=
    budget_natMod hvNat hdim
  have hvalid := budget_boolAnd (budget_optionIsSome hvOpt) (budget_natLt hvNat hdim)
  have hreject := doneWord_budget (dimension := dimension) (encCallee := encCallee)
    (encIn := encIn) (budget := budget)
    ((ComputableInSpace.constZero none).mono_le fun _ => Nat.zero_le _)
  have hstopAnswer := budget_ite (budget_natEq hcurrent htarget)
    (doneWord_budget (dimension := dimension) (encCallee := encCallee)
      (budget_optionSome hfuel)) hreject
  have hrest := registersWord_budget (r := fun a => { r a with fuel := (r a).fuel - 1 })
    hcurrent htarget (budget_natPred hfuel)
  have hclock := (ComputableInSpace.constZero (encIn := encIn) (encB := encNat) clock).mono_le
    (fun a => Nat.zero_le (budget a))
  have hcall := callWord_budget (v := v) hrest hv hclock (hstart v hv)
  have hroute := budget_ite hselector hreject
    (budget_ite hstop hstopAnswer
      (budget_ite (budget_boolAnd (budget_boolNot (budget_natIsZero hfuel)) hvalid)
        hcall hreject))
  have hread := choiceWord_budget hr
    (budget_comp_linear NondeterministicChoice.advance_inSpace (budget_prod hreader hselector))
  refine (budget_ite hh hroute hread).of_enc_eq ?_
  intro a
  cases hh' : NondeterministicChoice.isHalted (reader a)
  · simp [advanceChoice, hh', encState_choice]
  · cases selector a
    · cases hst : (reader a).stopped
      · cases hf : (r a).fuel <;> cases ho : VertexReader.result (reader a).reader
        all_goals try (solve | simp [advanceChoice, hh', hst, hf, ho])
        rename_i dest
        by_cases hdest : dest < dimension a <;>
          simp [advanceChoice, hh', hst, hf, ho, hdest, v, Nat.mod_eq_of_lt]
      · by_cases he : (r a).current = (r a).target <;>
          simp [advanceChoice, hh', hst, Fin.val_inj, he]
    · simp [advanceChoice, hh']

private theorem chooseNext_inSpace (encCallee : τ ↪ List Bool)
    (hstart : ComputableInSpace (fun p : Fin N × Fin N => start p.1 p.2)
      (encPair (encVertex N) (encVertex N)) encCallee
      (fun p => (encPair (encVertex N) (encVertex N) p).length)) :
    ComputableInSpace
      (fun p : (Registers N × NondeterministicChoice.State) × Option Bool × Bool =>
        (M).next (.choose p.1.1 p.1.2, p.2))
      (encPair (encChoose N) encAnswer) (encState encCallee)
      (fun p => (encPair (encChoose N) encAnswer p).length) := by
  have hphase := fst (encChoose N) encAnswer
  have hr := budget_comp_linear (fst (encRegisters N) NondeterministicChoice.encState) hphase
  have hs := budget_comp_linear (snd (encRegisters N) NondeterministicChoice.encState) hphase
  have hans := snd (encChoose N) encAnswer
  let enc := encPair (encChoose N) encAnswer
  let r (p : (Registers N × NondeterministicChoice.State) × Option Bool × Bool) := p.1.1
  have hdim := budget_const (encIn := enc) (encB := encNat) N (.refl _)
  have hrWord : ComputableInSpace (fun p => encRegisters N (r p)) enc encBits
      (fun p => (enc p).length) := hr.of_enc_eq fun _ => rfl
  have hcall (v : _ → Fin N)
      (hv : ComputableInSpace (fun p => (v p).val) enc encNat (fun p => (enc p).length)) :
      ComputableInSpace (fun p => start (r p).current (v p))
        enc encCallee (fun p => (enc p).length) :=
    budget_comp_linear hstart (budget_prod (encRegisters_current_budget N hr)
      (hv.of_enc_eq fun _ => rfl))
  exact (advanceChoice_budget (r := r) (start := fun _ => start) clock hdim hrWord hs
    (snd' hans) hcall).of_enc_eq fun _ => rfl

/-- Certify the call update from the encoded registers, destination, clock and callee.
The dimension may vary at each input. A return initializes the next destination reader
within the same budget. -/
theorem advanceCall_budget {edge : QueryMachine τ} {verdict : τ → Bool} {dimension : α → ℕ}
    {r : (a : α) → Registers (dimension a)} {v : (a : α) → Fin (dimension a)}
    {ticks : α → ℕ} {callee : α → τ} {answer : α → Option Bool} {selector : α → Bool}
    (hnext : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length))
    (hdim : ComputableInSpace dimension encIn encNat budget)
    (hr : ComputableInSpace (fun a => encRegisters (dimension a) (r a)) encIn encBits budget)
    (hv : ComputableInSpace (fun a => (v a).val) encIn encNat budget)
    (hticks : ComputableInSpace ticks encIn encNat budget)
    (hcallee : ComputableInSpace callee encIn encCallee budget)
    (hanswer : ComputableInSpace answer encIn (encOption encBool) budget)
    (hselector : ComputableInSpace selector encIn encBool budget) :
    ComputableInSpace (fun a => encState encCallee
      (advanceCall edge verdict (r a) (v a) (ticks a) (callee a) (answer a) (selector a)))
      encIn encBits budget := by
  have hregs := registerFields_budget hr
  have hhalt := budget_comp_linear hhalted hcallee
  have hvd := budget_comp_linear hverdict hcallee
  have hstep := budget_comp_linear hnext (budget_prod hcallee hanswer)
  have hcontinue := callWord_budget (r := r) (v := v) hr hv (budget_natPred hticks)
    (budget_ite hhalt hcallee hstep)
  have hresume := choiceWord_budget
    (registersWord_budget (r := fun a => { r a with current := v a })
      hv (fst' (snd' hregs)) (snd' (snd' hregs))) (NondeterministicChoice.init_budget hdim)
  have hreject := doneWord_budget (dimension := dimension) (encCallee := encCallee)
    (encIn := encIn) (budget := budget)
    ((ComputableInSpace.constZero none).mono_le fun _ => Nat.zero_le _)
  refine (budget_ite hselector hreject
    (budget_ite (budget_natIsZero hticks)
      (budget_ite (budget_boolAnd hhalt hvd) hresume hreject) hcontinue)).of_enc_eq ?_
  intro a
  cases selector a <;> cases ticks a <;> try rfl
  by_cases h : (edge.halted (callee a) && verdict (callee a)) = true
  · let r' := { r a with current := v a }
    have hword : encState encCallee (boundary r') =
        choiceWord (encRegisters (dimension a) r')
          (NondeterministicChoice.machine (dimension a)).init := rfl
    simpa [advanceCall, h, r'] using hword
  · simp [advanceCall, h]

private theorem callNext_inSpace (encCallee : τ ↪ List Bool)
    (hnext : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length)) :
    ComputableInSpace
      (fun p : (Registers N × Fin N × ℕ × τ) × Option Bool × Bool =>
        (M).next (.call p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2, p.2))
      (encPair (encCall N encCallee) encAnswer) (encState encCallee)
      (fun p => (encPair (encCall N encCallee) encAnswer p).length) := by
  let encRest := encPair (encVertex N) (encPair encNat encCallee)
  have hphase := fst (encCall N encCallee) encAnswer
  have hr := budget_comp_linear (fst (encRegisters N) encRest) hphase
  have hrest := budget_comp_linear (snd (encRegisters N) encRest) hphase
  have hv := budget_comp_linear (fst (encVertex N) (encPair encNat encCallee)) hrest
  have hstep := budget_comp_linear (snd (encVertex N) (encPair encNat encCallee)) hrest
  have hticks := fst' hstep
  have hcallee := snd' hstep
  have hanswer := snd (encCall N encCallee) encAnswer
  let enc := encPair (encCall N encCallee) encAnswer
  let r (p : (Registers N × Fin N × ℕ × τ) × Option Bool × Bool) := p.1.1
  let v (p : (Registers N × Fin N × ℕ × τ) × Option Bool × Bool) :=
    match p with | ⟨⟨_, v, _, _⟩, _⟩ => v
  have hdim := budget_const (encIn := enc) (encB := encNat) N (.refl _)
  have hrWord : ComputableInSpace (fun p => encRegisters N (r p)) enc encBits
      (fun p => (enc p).length) := hr.of_enc_eq fun _ => rfl
  have hvWord : ComputableInSpace (fun p => (v p).val) enc encNat
      (fun p => (enc p).length) := hv.of_enc_eq fun _ => rfl
  exact (advanceCall_budget (r := r) (v := v) hnext hhalted hverdict hdim hrWord hvWord
    hticks hcallee (fst' hanswer) (snd' hanswer)).of_enc_eq fun _ => rfl

section ReadState

private abbrev RegisterFields := ℕ × ℕ × ℕ

private abbrev encRegisterFields : RegisterFields ↪ List Bool :=
  encPair encNat (encPair encNat encNat)

private def registerFields (r : Registers N) : RegisterFields :=
  (r.current.val, r.target.val, r.fuel)

private abbrev ChoiceFields := RegisterFields × NondeterministicChoice.State

private abbrev CallFields (τ : Type) := RegisterFields × ℕ × ℕ × τ

/-- The vertex fields have the same binary layout with or without their range proofs. -/
private abbrev ReadState (τ : Type) :=
  ChoiceFields ⊕ (CallFields τ ⊕ Option ℕ)

private def readState : State N τ → ReadState τ
  | .choose r s => .inl (registerFields r, s)
  | .call r v ticks s => .inr (.inl (registerFields r, v.val, ticks, s))
  | .done reply => .inr (.inr reply)

private abbrev encReadChoice : ChoiceFields ↪ List Bool :=
  encPair encRegisterFields NondeterministicChoice.encState

private abbrev encReadCall (encCallee : τ ↪ List Bool) :=
  encCallFields encRegisterFields encNat encCallee

private abbrev encReadState (encCallee : τ ↪ List Bool) :=
  encSum encReadChoice (encSum (encReadCall encCallee) (encOption encNat))

variable {dimension : α → ℕ} {state : (a : α) → State (dimension a) τ}

private theorem readState_budget
    (hstate : ComputableInSpace (fun a => encState encCallee (state a)) encIn encBits budget) :
    ComputableInSpace (fun a => readState (state a)) encIn (encReadState encCallee) budget :=
  hstate.of_enc_eq fun a => by cases state a <;> rfl

/-- Decode the active query position from a walk state whose carrier may depend on the input. -/
theorem query_budget {calleeQuery : τ → ℕ}
    (hquery : ComputableInSpace calleeQuery encCallee encNat (fun s => (encCallee s).length))
    (hstate : ComputableInSpace (fun a => encState encCallee (state a)) encIn encBits budget) :
    ComputableInSpace (fun a => query calleeQuery (state a)) encIn encNat budget := by
  have hcall := budget_comp_linear hquery
    (snd' (snd' (snd encRegisterFields (encPair encNat (encPair encNat encCallee)))))
  have h := sumElim
    (budget_const (encIn := encReadChoice) 0 (.refl _))
    (sumElim hcall (budget_const (encIn := encOption encNat) 0 (.refl _)))
  exact (budget_comp_linear h (readState_budget hstate)).of_enc_eq
    fun a => by cases state a <;> rfl

/-- Detect a terminal walk state within the budget for its encoded word. -/
theorem halted_budget
    (hstate : ComputableInSpace (fun a => encState encCallee (state a)) encIn encBits budget) :
    ComputableInSpace (fun a => halted (state a)) encIn encBool budget := by
  have h := sumElim
    (budget_const (encIn := encReadChoice) (encB := encBool) false (.refl _))
    (sumElim (budget_const (encIn := encReadCall encCallee) (encB := encBool) false (.refl _))
      (budget_const (encIn := encOption encNat) (encB := encBool) true (.refl _)))
  exact (budget_comp_linear h (readState_budget hstate)).of_enc_eq
    fun a => by cases state a <;> rfl

/-- Decode unused fuel from a completed walk, including a runtime-dependent carrier. -/
theorem remainingFuel_budget
    (hstate : ComputableInSpace (fun a => encState encCallee (state a)) encIn encBits budget) :
    ComputableInSpace (fun a => remainingFuel (state a)) encIn (encOption encNat) budget := by
  have hid : ComputableInSpace id (encOption encNat) (encOption encNat)
      (fun s => (encOption encNat s).length) :=
    of_inO ComputableInDegree.id'.inO_one
  have h := sumElim
    (budget_const (encIn := encReadChoice) (encB := encOption encNat) none (.refl _))
    (sumElim (budget_const (encIn := encReadCall encCallee) (encB := encOption encNat)
      none (.refl _)) hid)
  exact (budget_comp_linear h (readState_budget hstate)).of_enc_eq
    fun a => by cases state a <;> rfl

private def positiveDimension (n : ℕ) : ℕ := (n - 1) + 1

private theorem positiveDimension_pos (n : ℕ) : 0 < positiveDimension n :=
  Nat.succ_pos _

private theorem positiveDimension_budget {n : α → ℕ}
    (hn : ComputableInSpace n encIn encNat budget) :
    ComputableInSpace (fun a => positiveDimension (n a)) encIn encNat budget :=
  budget_natSucc (budget_natPred hn)

private def readVertex (n v : ℕ) : Fin (positiveDimension n) :=
  ⟨v % positiveDimension n, Nat.mod_lt _ (positiveDimension_pos n)⟩

private def readRegisters (n : ℕ) (r : RegisterFields) : Registers (positiveDimension n) :=
  Registers.ofRanks (positiveDimension_pos n) r.1 r.2.1 r.2.2

private theorem readRegisters_budget {n : α → ℕ} {r : α → RegisterFields}
    (hn : ComputableInSpace (fun a => positiveDimension (n a)) encIn encNat budget)
    (hr : ComputableInSpace r encIn encRegisterFields budget) :
    ComputableInSpace (fun a => encRegisters _ (readRegisters (n a) (r a))) encIn encBits budget :=
  registersWord_budget (r := fun a => readRegisters (n a) (r a))
    (budget_natMod (fst' hr) hn) (budget_natMod (fst' (snd' hr)) hn) (snd' (snd' hr))

private theorem readVertex_succ (n : ℕ) (v : Fin (n + 1)) :
    readVertex (n + 1) v.val = v :=
  Fin.ext (Nat.mod_eq_of_lt v.isLt)

private theorem readRegisters_succ (n : ℕ) (r : Registers (n + 1)) :
    readRegisters (n + 1) (registerFields r) = r :=
  Registers.ofRanks_val (positiveDimension_pos (n + 1)) r

/-- Adjacency entry input: framed context and source ID, followed by the destination ID. -/
abbrev encStartRequest {κ : Type} (encContext : κ ↪ List Bool) : (κ × ℕ × ℕ) ↪ List Bool :=
  encPair encContext (encPair encNat encNat)

private abbrev DispatchContext (κ : Type) := κ × ℕ × Option Bool × Bool

private def dispatchDimension {κ : Type} (params : DispatchContext κ) : ℕ := params.2.1

private abbrev encDispatchContext {κ : Type} (encContext : κ ↪ List Bool) :
    DispatchContext κ ↪ List Bool :=
  encPair encContext (encPair encNat encAnswer)

private def chooseDispatch {κ : Type} (encCallee : τ ↪ List Bool)
    (startCall : κ → ℕ → ℕ → τ) (clock : ℕ) : ChoiceFields × DispatchContext κ → List Bool
  | ((r, reader), (ctx, n, _, selector)) =>
    encState encCallee (advanceChoice (fun u v => startCall ctx u.val v.val)
      clock (readRegisters n r) reader selector)

private theorem chooseDispatch_budget {κ : Type} {encContext : κ ↪ List Bool}
    {startCall : κ → ℕ → ℕ → τ} (clock : ℕ)
    (hstart : ComputableInSpace (fun (ctx, src, dst) => startCall ctx src dst)
      (encStartRequest encContext) encCallee (fun p => (encStartRequest encContext p).length)) :
    let enc := encPair encReadChoice (encDispatchContext encContext)
    ComputableInSpace
      (chooseDispatch encCallee startCall clock) enc encBits (fun p => (enc p).length) := by
  intro enc
  have hphase := fst encReadChoice (encDispatchContext encContext)
  have hctx := snd encReadChoice (encDispatchContext encContext)
  let n (p : ChoiceFields × DispatchContext κ) := dispatchDimension p.2
  let r (p : ChoiceFields × DispatchContext κ) := readRegisters (n p) p.1.1
  have hdim := positiveDimension_budget (n := n) (fst' (snd' hctx))
  have hfields := fst' hphase
  have hregs := readRegisters_budget (n := n) hdim hfields
  have hcurrent := budget_natMod (fst' hfields) hdim
  have hselect := snd' (snd' (snd' hctx))
  have hstart' (v : (p : ChoiceFields × DispatchContext κ) → Fin (positiveDimension (n p)))
      (hv : ComputableInSpace (fun p => (v p).val) enc encNat (fun p => (enc p).length)) :
      ComputableInSpace (fun p => startCall p.2.1 (r p).current.val (v p).val)
        enc encCallee (fun p => (enc p).length) :=
    budget_comp_linear hstart (budget_prod (fst' hctx) (budget_prod hcurrent hv))
  refine (advanceChoice_budget (dimension := fun p => positiveDimension (n p))
    (r := r) (start := fun p u v => startCall p.2.1 u.val v.val) clock hdim hregs
    (snd' hphase) hselect hstart').of_enc_eq ?_
  rintro ⟨⟨r, reader⟩, ⟨ctx, dimension, reply, selector⟩⟩
  rfl

private def callDispatch {κ : Type} (encCallee : τ ↪ List Bool)
    (call : QueryMachine τ) (verdict : τ → Bool) : CallFields τ × DispatchContext κ → List Bool
  | ((r, dest, remaining, callee), (_, n, reply, selector)) =>
    encState encCallee (advanceCall call verdict (readRegisters n r) (readVertex n dest)
      remaining callee reply selector)

private theorem callDispatch_budget {κ : Type} (encContext : κ ↪ List Bool)
    {call : QueryMachine τ} {verdict : τ → Bool}
    (hnext : ComputableInSpace call.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace call.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length)) :
    let enc := encPair (encReadCall encCallee) (encDispatchContext encContext)
    ComputableInSpace (callDispatch encCallee call verdict)
      enc encBits (fun p => (enc p).length) := by
  intro enc
  have hphase := fst (encReadCall encCallee) (encDispatchContext encContext)
  have hctx := snd (encReadCall encCallee) (encDispatchContext encContext)
  let n (p : CallFields τ × DispatchContext κ) := dispatchDimension p.2
  let r (p : CallFields τ × DispatchContext κ) := readRegisters (n p) p.1.1
  let dest (p : CallFields τ × DispatchContext κ) := readVertex (n p) p.1.2.1
  have hdim := positiveDimension_budget (n := n) (fst' (snd' hctx))
  have hregs := readRegisters_budget (n := n) hdim (fst' hphase)
  have hdst := budget_natMod (fst' (snd' hphase)) hdim
  have hcallee := snd' (snd' hphase)
  have hanswer := snd' (snd' hctx)
  refine (advanceCall_budget (dimension := fun p => positiveDimension (n p)) (r := r) (v := dest)
    hnext hhalted hverdict hdim hregs hdst (fst' hcallee) (snd' hcallee) (fst' hanswer)
    (snd' hanswer)).of_enc_eq ?_
  rintro ⟨⟨r, dest, ticks, callee⟩, ⟨ctx, dimension, reply, selector⟩⟩
  rfl

private theorem dispatch_readState_eq {κ : Type} {n : ℕ} {call : QueryMachine τ}
    {startCall : κ → ℕ → ℕ → τ} {verdict : τ → Bool} {clock : ℕ}
    (s : State n τ) (hp : 0 < n) (context : κ) (reply : Option Bool) (selector : Bool) :
    encState encCallee (advance call (fun u v => startCall context u.val v.val)
      verdict clock (s, reply, selector)) =
      (readState s).elim
        (fun choice =>
          chooseDispatch encCallee startCall clock (choice, context, n, reply, selector))
        (fun p => p.elim
          (fun active => callDispatch encCallee call verdict (active, context, n, reply, selector))
          (fun result => encState encCallee (.done (N := 0) result))) := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hp).elim
  | succ n =>
    cases s with
    | choose r reader =>
      simp only [advance, readState, Sum.elim_inl, chooseDispatch, readRegisters_succ]
      rfl
    | call r dest remaining callee =>
      simp only [advance, readState, Sum.elim_inl, Sum.elim_inr,
        callDispatch, readRegisters_succ, readVertex_succ]
      rfl
    | done result => rfl

/-- Dispatch the existing walk update on a nonempty carrier computed from the input. The
encoded choice and call fields use the same layout as in the fixed-dimension walk. -/
theorem advance_budget {κ : Type} {encContext : κ ↪ List Bool}
    {call : QueryMachine τ} {startCall : κ → ℕ → ℕ → τ} {verdict : τ → Bool} (clock : ℕ)
    {context : α → κ} {reply : α → Option Bool} {selector : α → Bool}
    (hstart : ComputableInSpace (fun (ctx, src, dst) => startCall ctx src dst)
      (encStartRequest encContext) encCallee (fun p => (encStartRequest encContext p).length))
    (hnext : ComputableInSpace call.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace call.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length))
    (hcontext : ComputableInSpace context encIn encContext budget)
    (hdim : ComputableInSpace dimension encIn encNat budget)
    (hpositive : ∀ a, 0 < dimension a)
    (hstate : ComputableInSpace (fun a => encState encCallee (state a)) encIn encBits budget)
    (hreply : ComputableInSpace reply encIn (encOption encBool) budget)
    (hselector : ComputableInSpace selector encIn encBool budget) :
    ComputableInSpace (fun a => encState encCallee
      (advance call (fun u v => startCall (context a) u.val v.val) verdict clock
        (state a, reply a, selector a))) encIn encBits budget := by
  have hdone := doneWord_budget (dimension := fun _ => 0) (encCallee := encCallee)
    (fst (encOption encNat) (encDispatchContext encContext))
  have h := sumElimFst (chooseDispatch_budget clock hstart)
    (sumElimFst (callDispatch_budget encContext hnext hhalted hverdict) hdone)
  refine (budget_comp_linear h (budget_prod (readState_budget hstate)
    (budget_prod hcontext (budget_prod hdim (budget_prod hreply hselector))))).of_enc_eq ?_
  intro a
  exact dispatch_readState_eq (state a) (hpositive a) (context a) (reply a) (selector a)

end ReadState

/-- The walk reads the original input at the active adjacency query position. -/
theorem query_inSpace (encCallee : τ ↪ List Bool)
    (hquery : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length)) :
    ComputableInSpace (M).query (encState encCallee) encNat
      (fun s => (encState encCallee s).length) :=
  query_budget (state := id) hquery (of_inO (ComputableInO.of_eq fun _ => rfl))

/-- Detect the walk’s terminal state in linear workspace. -/
theorem halted_inSpace (encCallee : τ ↪ List Bool) :
    ComputableInSpace (M).halted (encState encCallee) encBool
      (fun s => (encState encCallee s).length) :=
  halted_budget (state := id) (of_inO (ComputableInO.of_eq fun _ => rfl))

/-- Decode unused fuel at success, with no result on live or rejected states. -/
theorem remainingFuel_inSpace (encCallee : τ ↪ List Bool) :
    ComputableInSpace (remainingFuel (N := N) (τ := τ)) (encState encCallee) (encOption encNat)
      (fun s => (encState encCallee s).length) :=
  remainingFuel_budget (state := id) (of_inO (ComputableInO.of_eq fun _ => rfl))

private theorem accept_inSpace (encCallee : τ ↪ List Bool) :
    ComputableInSpace (M).accept (encState encCallee) encBool
      (fun s => (encState encCallee s).length) :=
  budget_optionIsSome (remainingFuel_inSpace encCallee)

/-- Advance one selector with linear workspace, including an active adjacency call. -/
theorem next_inSpace (encCallee : τ ↪ List Bool)
    (hstart : ComputableInSpace (fun p : Fin N × Fin N => start p.1 p.2)
      (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat)) encCallee
      (fun p =>
        (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat) p).length))
    (hnext : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length)) :
    ComputableInSpace (M).next
      (encPair (encState encCallee) (encPair (encOption encBool) encBool)) (encState encCallee)
      (fun p => (encPair (encState encCallee) (encPair (encOption encBool) encBool) p).length) := by
  have h := sumElimFst (chooseNext_inSpace edge start verdict clock initial encCallee hstart)
    (sumElimFst (callNext_inSpace edge start verdict clock initial encCallee hnext hhalted hverdict)
      (done_budget (encCallee := encCallee) (N := N) (fst (encOption encNat) encAnswer)))
  let view (p : State N τ × (Option Bool × Bool)) := (stateView N τ p.1, p.2)
  exact (h.of_encIn_eq view (fun _ => rfl)).of_enc_eq fun ⟨s, _⟩ => by cases s <;> rfl

open NondeterministicQueryMachine in
/-- Compile a fixed-dimension, fixed-callback-clock walk into native occurrence-sensitive
routines. The registers may be initialized from the original input. The space envelope covers
the encoded walk registers, every callee prefix, and the input position counter. -/
theorem exists_routines (encCallee : τ ↪ List Bool)
    (hstart : ComputableInSpace (fun p : Fin N × Fin N => start p.1 p.2)
      (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat)) encCallee
      (fun p => (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat) p).length))
    (hquery : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length))
    (hnext : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hhalted : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hverdict : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length))
    (registers : α → Registers N)
    (hregisters : ComputableInSpace registers encIn (encRegisters N) budget)
    (hlog : ∀ a, Nat.log2 (encIn a).length + 1 ≤ budget a)
    (hbound : ∀ a, (encNat N).length + (Nat.log2 N.size + 1) +
      (encNat (registers a).fuel).length + (encNat clock).length ≤ budget a)
    (hcallee : ∀ a (u v : Fin N) t, t ≤ clock →
      (encCallee (edge.runFrom (encIn a) (start u v) t)).length ≤ budget a) :
    Nonempty (Routines (M) (fun a => (machine edge start verdict clock (registers a)).init)
      encIn budget) := by
  have hsize (a : α) (selectors : List Bool) :
      (encState encCallee ((machine edge start verdict clock (registers a)).run
        (encIn a) selectors)).length ≤ 35 * budget a := by
    have hs := length_run_le edge start verdict clock (registers a) (encIn a)
      encCallee (budget a) (hcallee a) selectors
    have hb := hbound a
    have hp : 1 ≤ budget a := by have := hlog a; omega
    omega
  have hInit := init_budget (encCallee := encCallee) edge start verdict clock hregisters
  refine (M).exists_routines (query_inSpace edge start verdict clock initial encCallee hquery)
    (next_inSpace edge start verdict clock initial encCallee hstart hnext hhalted hverdict)
    (halted_inSpace edge start verdict clock initial encCallee)
    (accept_inSpace edge start verdict clock initial encCallee) _ budget hlog hInit ⟨35, hsize⟩

open NondeterministicQueryMachine Cslib.DoubleCounting.Scan in
/-- Accepting native occurrence lists are unique for their canonical selectors and exist
exactly for successful typed walks. -/
theorem native_firstHalting_accept_iff (registers : α → Registers N)
    (R : Routines (M) (fun a => (machine edge start verdict clock (registers a)).init)
      encIn budget)
    (a : α) (adjacent : Fin N → Fin N → Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom (encIn a) (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom (encIn a) (start u v) clock) = adjacent u v)
    (bits : List Bool) :
    (∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (encIn a)) indices =
        some (bits, final) ∧ final.Halted ∧ final.output = [true]) ↔
      ∃ (tail : List (Fin N)) (left : ℕ), bits = selectors clock tail ∧
        (walkM readNext (fun u v => pure (adjacent u v))
          (registers a).target (registers a).fuel (registers a).current tail).1 = some left := by
  let walk := machine edge start verdict clock (registers a)
  constructor
  · rintro ⟨_, ⟨final, hreplay, hhalts, hout⟩, _⟩
    obtain ⟨hfirst, houtput⟩ := R.replay_correct a hreplay hhalts
    have haccept : walk.accept (walk.run (encIn a) bits) = true :=
      List.cons.inj (houtput.symm.trans hout) |>.1
    change (remainingFuel (walk.run (encIn a) bits)).isSome = true at haccept
    obtain ⟨left, hl⟩ := Option.isSome_iff_exists.mp haccept
    obtain ⟨tail, hbits, hwalk⟩ :=
      (firstHalting_remainingFuel_iff edge start verdict clock (registers a) (encIn a)
        adjacent hclock hedge bits left).mp ⟨hfirst, hl⟩
    exact ⟨tail, left, hbits, hwalk⟩
  · rintro ⟨tail, left, rfl, hs⟩
    obtain ⟨hfirst, hresult⟩ := firstHalting_selectors edge start verdict clock (registers a)
      (encIn a) adjacent hclock hedge tail hs
    obtain ⟨indices, ⟨final, hreplay, hhalts⟩, hunique⟩ :=
      (R.existsUnique_replay_iff a (selectors clock tail)).mpr hfirst
    have hout := (R.replay_correct a hreplay hhalts).2
    have haccept : walk.accept (walk.run (encIn a) (selectors clock tail)) = true := by
      change (remainingFuel _).isSome = true
      rw [hresult]
      rfl
    have hout' := hout.trans (congrArg (fun b => [b]) haccept)
    exact ⟨indices, ⟨final, hreplay, hhalts, hout'⟩,
      fun other ⟨finish, hr, hh, _⟩ => hunique other ⟨finish, hr, hh⟩⟩

end Native

end Turing.DoubleCounting.BoundedWalk
