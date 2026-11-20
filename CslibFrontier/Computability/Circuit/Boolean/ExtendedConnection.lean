/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.RandomizedDepth
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

/-!
# Extended-connection uniformity and randomized logarithmic depth

In Ruzzo's extended connection language a query gives the circuit input length in
binary, a starting gate name, and a path of left and right arguments. An empty path
asks for the gate's type. A nonempty path asks for the name of its endpoint.
Circuit names need not be in program order. We reserve zero for the output wire.

The uniformity machine has alternating time logarithmic in the circuit input
length, as in [Ruzzo1981Uniform, §2] and [Cook1985Taxonomy, §2]. The machine reads
the short query tuple on a sequential input tape. This clock is measured against
the input length of the original language, whose polynomially many random bits
are additional circuit inputs.

## Main definitions

* `ExtendedConnectionQuery`: the gate type and path endpoint queries.
* `extendedConnectionLanguage`: the true queries to a named circuit family.
* `RNC1`: one-sided randomized logarithmic-depth circuits with extended-connection uniformity.

## Main results

* `RNC1_subset_nonuniformRNC1`: forgetting the alternating machine preserves the circuit bounds.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- An input wire is labelled by its input position, and a gate by its operation. -/
abbrev ConnectionKind := ℕ ⊕ Op

/-- A query of the type of a wire (empty path) or of the name reached by a nonempty path. -/
structure ExtendedConnectionQuery where
  /-- The input length of the language being decided. -/
  inputLength : ℕ
  /-- The name of the wire where the path begins. -/
  start : ℕ
  /-- Each bit selects the left (false) or right (true) argument. -/
  path : List Bool
  /-- A proposed wire type for an empty path or endpoint name for a nonempty path. -/
  target : ConnectionKind ⊕ ℕ

/-- Encode the length and names in binary, with tags for wire types and endpoint queries. -/
enc_structure encExtendedConnectionQuery : ExtendedConnectionQuery where
  inputLength : encNat, start : encNat, path : encBits,
  target : (encSum (encSum encNat encOp) encNat)

/-- Follow argument wires along a path. An attempted move beyond a leaf or along a
nonexistent argument has no endpoint. -/
@[expose] def followInputs {n : ℕ} (C : Circuit signature n 1) (w : Wire n C.size) :
    List Bool → Option (Wire n C.size)
  | [] => some w
  | side :: rest =>
    match w with
    | .input _ => none
    | .gate g =>
      let line := C.program.lines g
      if h : side.toNat < signature.Arity line.op then followInputs C (line.wires ⟨_, h⟩) rest
      else none

/-- The true extended connection queries to a circuit family with named wires.
The path bound is logarithmic in the selected size envelope. -/
@[expose] def extendedConnectionLanguage {inputs : ℕ → ℕ}
    (C : ∀ n, Circuit signature (inputs n) 1) (sizeBound : ℕ → ℕ)
    (name : ∀ n, Wire (inputs n) (C n).size ↪ ℕ) : Set ExtendedConnectionQuery :=
  {q | q.path.length ≤ Nat.log 2 (sizeBound q.inputLength) ∧
    ∃ w, name q.inputLength w = q.start ∧
      match q.path, q.target with
      | [], .inl kind =>
        (match w with
         | .input i => .inl i.val
         | .gate g => .inr ((C q.inputLength).program.lines g).op) = kind
      | _ :: _, .inr endpoint =>
        ∃ v, followInputs (C q.inputLength) w q.path = some v ∧
          name q.inputLength v = endpoint
      | _, _ => False}

/-- **RNC¹**, with Cook's extended-connection uniformity at logarithmic depth.
The output wire has name zero, and all wire names are bounded by the polynomial
size envelope. The alternating uniformity decider has a common logarithmic clock
for all queries, including negative answers. -/
@[expose] def RNC1 : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (s r : ℕ → ℕ), PolynomiallyBounded s ∧ PolynomiallyBounded r ∧
    ∃ (C : ∀ n, Circuit signature (n + r n) 1) (name : ∀ n, Wire (n + r n) (C n).size ↪ ℕ),
      (∀ n, name n ((C n).outputs 0) = 0 ∧ ∀ w, name n w < s n) ∧
      (∃ a b : ℕ, Turing.MultiTapeATM.DecidableInTime (extendedConnectionLanguage C s name)
        encExtendedConnectionQuery (fun q => a * (Nat.log 2 q.inputLength + 1) + b)) ∧
      ∀ n, (C n).depth ≤ c * (Nat.log 2 n + 1) ∧ n + r n + (C n).size ≤ s n ∧
        HasOneSidedError (C n) L}

/-- Extended-connection-uniform randomized circuits also give nonuniform randomized circuits. -/
theorem RNC1_subset_nonuniformRNC1 : RNC1 ⊆ NonuniformRNC1 := by
  rintro L ⟨c, s, r, hs, hr, C, _, _, _, hC⟩
  refine ⟨c, s, r, hs, hr, fun n => ⟨C n, ?_, ?_, (hC n).2.2⟩⟩
  · simpa only [pow_one] using (hC n).1
  · exact (Nat.le_add_left _ _).trans (hC n).2.1

end Cslib.Circuits.Boolean
