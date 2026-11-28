/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Reading bits from an oracle language

`Cslib.Complexity.queryBit w` submits the word `w` and reads the first bit of the reply. Against
an oracle language `A` it returns `decide (w ∈ A)` and makes exactly the one request `w`; for a
polynomial-time word it is strict oracle PPT, since the word is written on the query buffer and
only one bit of the reply is read. The oracle closure rules and the bounded-query classes build
their one-request certificates from this program.

## Main definitions

* `Cslib.Complexity.queryBit`: one request, reading one bit of the reply.
* `Cslib.Complexity.readBitsProgram` reads an indexed sequence of bit requests.

## Main results

* `Cslib.Complexity.interpret_readBitsProgram` identifies the replies with the membership bits.
* `Cslib.Complexity.isOraclePPTOn_readBitsProgram` certifies the strict running time.
* `Cslib.Complexity.interpret_queryBit`: against `A`, the request answers membership in `A`.
* `Cslib.Complexity.queriesWith_queryBit`: the program makes exactly one request.
* `Cslib.Complexity.isOraclePPTOn_queryBit`: one request for a polynomial-time word is strict
  oracle PPT.
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type}

/-- **One request**: submit the word `w` and read the first bit of the reply. -/
def queryBit (w : List Bool) : WordQueryComp Unit Bool :=
  (fun reply => decide (reply = [true])) <$> (List.take 1 <$> OracleComp.query ((), w))

open Classical in
/-- Against an oracle language, one request answers membership of its word. -/
theorem interpret_queryBit (A : Set (List Bool)) (w : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle A) (queryBit w) = decide (w ∈ A) := by
  change decide (List.take 1 (languageOracle A ((), w)) = [true]) = decide (w ∈ A)
  rw [languageOracle_apply]
  cases decide (w ∈ A) <;> rfl

/-- One request makes one request. -/
@[simp]
theorem queriesWith_queryBit (answer : Unit × List Bool → List Bool) (w : List Bool) :
    OracleComp.queriesWith answer (queryBit w) = [((), w)] := by
  simp [queryBit]

/-- One request for a polynomial-time word is strict oracle PPT: the word is written on the query
buffer and one bit of the reply is read. -/
theorem isOraclePPTOn_queryBit {req : α → List Bool} {input : α ↪ List Bool}
    (hreq : ComputableInPolyTime req input encBits) :
    IsOraclePPTOn input encBool
      (fun a => OracleComp.interpret ProbOracleComp.query (queryBit (req a))) := by
  simp only [queryBit, OracleComp.interpret_map, OracleComp.interpret_query]
  exact (IsOraclePPTOn.query_take () hreq (limit := fun _ => 1)
    (ComputableInPolyTime.const 1)).map
    (ComputableInPolyTime.id'.decide_eq' (ComputableInPolyTime.const [true]))

/-- One step of reading bits: ask for the next bit and append it. -/
def readBitStep (req : α → ℕ → List Bool) (a : α) (bits : List Bool) :
    WordQueryComp Unit (List Bool) :=
  (fun b => bits ++ [b]) <$> queryBit (req a bits.length)

/-- Ask for the words `req a 0, …, req a (count a - 1)` in turn and list the answers. -/
def readBitsProgram (req : α → ℕ → List Bool) (count : α → ℕ) (a : α) :
    WordQueryComp Unit (List Bool) :=
  OracleComp.iterate (count a) (readBitStep req a) []

open Classical in
/-- Against an oracle language, `readBitsProgram` lists the memberships of the requested words. -/
theorem interpret_readBitsProgram (A : Set (List Bool)) (req : α → ℕ → List Bool)
    (count : α → ℕ) (a : α) :
    OracleComp.interpret (m := Id) (languageOracle A) (readBitsProgram req count a) =
      List.ofFn fun i : Fin (count a) => decide (req a i ∈ A) := by
  rw [readBitsProgram, OracleComp.interpret_id_iterate]
  generalize count a = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, readBitStep, List.ofFn_succ_last, List.length_ofFn]
    simp [OracleComp.interpret_map, interpret_queryBit]; rfl

open ComputableInPolyTime in
theorem isOraclePPTOn_readBitsProgram {encA : α ↪ List Bool} {req : α → ℕ → List Bool}
    {count : α → ℕ}
    (hreq : ComputableInPolyTime (fun p : α × ℕ => req p.1 p.2) (encPair encA encUnary) encBits)
    (hcount : ComputableInPolyTime count encA encUnary) :
    IsOraclePPTOn encA encBits
      (fun a => OracleComp.interpret ProbOracleComp.query (readBitsProgram req count a)) := by
  have hstep : IsOraclePPTOn (encPair encA encBits) encBits
      (fun pair => OracleComp.interpret ProbOracleComp.query (readBitStep req pair.1 pair.2)) :=
    ((isOraclePPTOn_queryBit (hreq.comp ((fst encA encBits).prod
      (length_bits.comp (snd encA encBits))))).map_with
      (f := fun (pair : α × List Bool) (b : Bool) => pair.2 ++ [b])
      (bitsAppend ((fst _ _).snd') (bitsCons (snd _ _) (const [])))).congr
      fun _ _ _ _ => by simp only [readBitStep, OracleComp.interpret_map, Function.comp_apply]
  have hit := IsOraclePPTOn.iterateWith_spec (input := encA) (stateEncoding := encBits)
    (count := count) (initial := fun _ => []) (step := fun a s =>
      OracleComp.interpret ProbOracleComp.query (readBitStep req a s))
    hcount (by fun_prop) hstep (fun _ i s => s.length = i) (fun _ => rfl)
    (fun _ _ _ _ hs _ hnext => by
      simp only [readBitStep, OracleComp.interpret_map] at hnext
      obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      simp [hs])
    hcount.polyBounded fun _ _ _ hi hs => by simpa [hs] using hi
  simpa only [readBitsProgram, OracleComp.interpret_iterate] using hit.1

end Cslib.Complexity
