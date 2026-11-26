/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.Interpolation
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
import CslibFrontier.Computability.Circuit.Encoding.Evaluation
import Mathlib.Data.List.GetD

/-!
# Extracting interpolants from resolution refutations

Feasible interpolation (`Cslib.Logic.PL.CNF.IsProof.exists_interpolant`) proves that a resolution
refutation of `A(x, y) ∧ B(x, z)` with `s` lines has an interpolant computed by a De Morgan
circuit with at most `4 s` gates. Refutations are propositions there, so the circuit is obtained
by induction rather than computed. This file computes it: `Cslib.Logic.PL.CNF.interpolantCode`
reads the lines of a refutation and writes the code of the interpolant circuit as a list of gates
(`Cslib.Circuits.Circuit.code`). It follows Pudlák's construction
[Pudlák, Theorem 1][Pudlak1997], [Krajíček, Theorem 6.1][Krajicek1997], with the justification of
each line found by search, since the refutation records only its clauses.

The shared variables are natural numbers; shared variable `i` is input wire `i` of a circuit with
`n` inputs. The lines are read from the first to the last, and line `k` gets a fixed block of gates
(four in the De Morgan basis, two in the monotone basis of `MonotoneExtraction.lean`), with the
value of the line on the block's last wire (`Cslib.Logic.PL.Interpolant.lineGatesOf`,
`Cslib.Logic.PL.Interpolant.gatesOf`, `Cslib.Logic.PL.Interpolant.outputWireOf`):

* a clause of `A` gets the constant `false`, and otherwise a clause of `B` the constant `true`;
* otherwise the earlier lines are searched (`Cslib.Logic.PL.Interpolant.findStep`) for `c₁`, `c₂`
  and `v` with `(v, true) ∈ c₁`, `(v, false) ∈ c₂` and `c₁.resolvent c₂ v` equal to the line. In
  the De Morgan basis, a resolution on an `A`-private variable gets the disjunction of the values
  of `c₁` and `c₂`, one on a `B`-private variable their conjunction, and one on a shared variable
  `xᵢ` the selector `(¬xᵢ ∧ c₁) ∨ (xᵢ ∧ c₂)`, which takes all four gates;
* a line with no justification gets the constant `false`.

Gates that compute nothing are padded with constants. The output is the wire of the first empty
line. So the code always has `4 s` gates for `s` lines, each reading only earlier gates and the
input wires of the shared variables it meets (`Cslib.Logic.PL.Interpolant.length_gates`,
`Cslib.Logic.PL.Interpolant.isCodeFrom_gates`). On a refutation whose shared variables are below
`n`, it is the code of a circuit with `4 s` gates computing an interpolant
(`Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`, an instance of the signature-polymorphic
`Cslib.Logic.PL.Interpolant.ofCode_gatesOf`). The proof reuses the invariant of the non-computable
construction (`Cslib.Logic.PL.CNF.IsInterpolantAt`). On a list without an empty line, the output
wire is out of range and the code does not decode.

## Main definitions

* `Cslib.Logic.PL.Interpolant.Step`: a candidate resolution step, with its premises' positions.
* `Cslib.Logic.PL.Interpolant.findStep`, `Cslib.Logic.PL.Interpolant.lineGatesOf`,
  `Cslib.Logic.PL.Interpolant.gatesOf`, `Cslib.Logic.PL.Interpolant.outputWireOf`: signature- and
  stride-polymorphic resolution interpolant extraction.
* `Cslib.Logic.PL.Interpolant.lineGates`: the four De Morgan gates of one line.
* `Cslib.Logic.PL.Interpolant.gates`: the De Morgan gates of all lines.
* `Cslib.Logic.PL.CNF.interpolantCode`: the code of the interpolant circuit of a refutation.

## Main results

* `Cslib.Logic.PL.Interpolant.ofCode_gatesOf`: signature- and stride-polymorphic soundness and
  decoding theorem for fixed-stride interpolant code builders.
* `Cslib.Logic.PL.Interpolant.length_gates`, `Cslib.Logic.PL.Interpolant.isCodeFrom_gates`: the
  code has four gates per line and is well formed.
* `Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`: on a refutation, the code decodes to a
  circuit with four gates per line computing an interpolant.

## References

* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Boolean

namespace Interpolant

variable {V Y Z : Type*}

/-- A candidate resolution step: two lines with their positions, and the variable resolved on.
It justifies `left.resolvent right pivot` when `(pivot, true) ∈ left` and
`(pivot, false) ∈ right`. -/
structure Step (V : Type*) where
  /-- The premise containing the positive literal of `pivot`. -/
  left : Clause V
  /-- The position of `left` among the lines. -/
  leftIndex : ℕ
  /-- The premise containing the negative literal of `pivot`. -/
  right : Clause V
  /-- The position of `right` among the lines. -/
  rightIndex : ℕ
  /-- The variable resolved on. -/
  pivot : V

/-- Candidate resolution steps among `lines`: two lines, each with its position, and the variable
of a literal of the first. -/
def candidates (lines : List (Clause V)) : List (Step V) :=
  lines.zipIdx.flatMap fun (c₁, i₁) => lines.zipIdx.flatMap fun (c₂, i₂) =>
    c₁.map fun (v, _) => ⟨c₁, i₁, c₂, i₂, v⟩

/-- The first candidate resolution step among `lines` deriving `c`, if any. -/
def findStep [DecidableEq V] (lines : List (Clause V)) (c : Clause V) : Option (Step V) :=
  (candidates lines).find? fun t =>
    decide ((t.pivot, true) ∈ t.left ∧ (t.pivot, false) ∈ t.right ∧
      t.left.resolvent t.right t.pivot = c)

/-- Fixed-stride gates for one line `c` read after `earlier`, allocating `s` gates per line
starting at wire `n + s * earlier.length`, with each line's value on its last wire
`n + s * k + (s - 1)`. -/
def lineGatesOf {Op : Type*} [DecidableEq Y] [DecidableEq Z] (s : ℕ) (constOp : Bool → Op)
    (step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ))
    (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (earlier : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) : List (Op × List ℕ) :=
  if c ∈ A.relabel (Sum.map id Sum.inl) then List.replicate s (constOp false, [])
  else if c ∈ B.relabel (Sum.map id Sum.inr) then List.replicate s (constOp true, [])
  else (findStep earlier c).elim (List.replicate s (constOp false, [])) fun t =>
    step (n + s * earlier.length) (n + s * t.leftIndex + (s - 1)) (n + s * t.rightIndex + (s - 1))
      t.pivot

/-- Fixed-stride gates of all lines `lines`, listed from first to last, in program order. -/
def gatesOf {Op : Type*} [DecidableEq Y] [DecidableEq Z] (s : ℕ) (constOp : Bool → Op)
    (step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ))
    (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : List (Op × List ℕ) :=
  lines.zipIdx.flatMap fun (c, k) => lineGatesOf s constOp step n A B (lines.take k) c

/-- The last wire `n + s * k + (s - 1)` of the first empty line `k` among `lines`, listed from
first to last; past the last gate if there is none. -/
def outputWireOf (s n : ℕ) (lines : List (Clause V)) : ℕ :=
  n + s * (lines.map List.isEmpty).idxOf true + (s - 1)

/-- The gate `g` after three constant gates. -/
def padGate (g : Op × List ℕ) : List (Op × List ℕ) :=
  [(.const false, []), (.const false, []), (.const false, []), g]

/-- The four gates of a resolution step on `v`, starting at wire `base`, given the wires `w₁` and
`w₂` of its premises. On a shared variable `xᵢ` they compute the selector `(¬xᵢ ∧ w₁) ∨ (xᵢ ∧ w₂)`;
on an `A`-private variable the disjunction, and on a `B`-private variable the conjunction, of
`w₁` and `w₂`. -/
def resolventGates (base w₁ w₂ : ℕ) : ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ)
  | .inl i => [(.not, [i]), (.and, [base, w₁]), (.and, [i, w₂]), (.or, [base + 1, base + 2])]
  | .inr (.inl _) => padGate (.or, [w₁, w₂])
  | .inr (.inr _) => padGate (.and, [w₁, w₂])

variable [DecidableEq Y] [DecidableEq Z]

/-- The four gates of a line `c` read after the lines `earlier`, on wires `n + 4k` to `n + 4k + 3`
where `k` is the number of earlier lines. A clause of `A` gets `false` and a clause of `B` gets
`true`; otherwise the first candidate step among the earlier lines resolving to `c` gets its
`resolventGates`, and a line with no such step gets `false`. -/
def lineGates (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (earlier : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) : List (Op × List ℕ) :=
  lineGatesOf 4 Op.const resolventGates n A B earlier c

/-- The gates of all the lines `lines`, listed from first to last, in program order. -/
def gates (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z)) (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) :
    List (Op × List ℕ) :=
  gatesOf 4 Op.const resolventGates n A B lines

/-- The wire of the first empty line among `lines`, listed from first to last; past the last gate
if there is none. -/
def outputWire (n : ℕ) (lines : List (Clause V)) : ℕ :=
  outputWireOf 4 n lines

end Interpolant

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- **The interpolant circuit of a refutation**, as a code (`Cslib.Circuits.Circuit.code`). The
lines `ls` of a resolution refutation of `A.appendShared B` are listed from the last to the first,
as in `Cslib.Logic.PL.CNF.IsProof`; shared variable `i` is input wire `i` of a circuit with `n`
inputs. The gates are those of `Cslib.Logic.PL.Interpolant.gates` on the lines from the first to
the last, and the output is the wire of the first empty line. -/
def CNF.interpolantCode (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : List (Op × List ℕ) × List ℕ :=
  (Interpolant.gates n A B ls.reverse, [Interpolant.outputWire n ls.reverse])

end Cslib.Logic.PL

end

public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Boolean

universe v

namespace CNF.IsProof

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- If the shared variables of `A` and `B` are below `n`, so are those of every line of a
refutation of `A.appendShared B`. -/
theorem shared_lt {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
    {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls)
    (hA : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → i < n) (hB : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → i < n) :
    ∀ d ∈ ls, ∀ i b, (.inl i, b) ∈ d → i < n := by
  intro d hd i b hl
  obtain ⟨l, hl', hli⟩ := List.mem_map.1 (h.fst_mem_vars hd hl)
  obtain ⟨e, he, hle⟩ := List.mem_flatten.1 hl'
  rcases List.mem_append.1 he with he | he <;> obtain ⟨d', hd', rfl⟩ := List.mem_map.1 he <;>
    obtain ⟨l', hl'', rfl⟩ := List.mem_map.1 hle <;> rcases l' with ⟨_ | _, b'⟩ <;>
    simp only [Prod.map, Sum.map_inl, Sum.map_inr, id, reduceCtorEq, Sum.inl.injEq] at hli
  · exact hA d' hd' _ b' (hli ▸ hl'')
  · exact hB d' hd' _ b' (hli ▸ hl'')

end CNF.IsProof

namespace Interpolant

/-! ### Polymorphic fixed-stride extraction -/

section Polymorphic

variable {V Y Z : Type*}

/-- A found step resolves its indexed premises to the requested clause. -/
private theorem findStep_spec [DecidableEq V] {lines : List (Clause V)} {c : Clause V}
    {t : Step V} (ht : findStep lines c = some t) :
    ∃ (h₁ : t.leftIndex < lines.length) (h₂ : t.rightIndex < lines.length),
      lines[t.leftIndex] = t.left ∧ lines[t.rightIndex] = t.right ∧
        (t.pivot, true) ∈ t.left ∧ (t.pivot, false) ∈ t.right ∧
        t.left.resolvent t.right t.pivot = c := by
  have htest := List.find?_some ht
  simp only [decide_eq_true_eq] at htest
  obtain ⟨⟨c₁, i₁⟩, he₁, hm⟩ := List.mem_flatMap.1 (List.mem_of_find?_eq_some ht)
  obtain ⟨⟨c₂, i₂⟩, he₂, hm⟩ := List.mem_flatMap.1 hm
  obtain ⟨⟨v, _⟩, -, rfl⟩ := List.mem_map.1 hm
  obtain ⟨-, h₁, hc₁⟩ := List.mem_zipIdx he₁
  obtain ⟨-, h₂, hc₂⟩ := List.mem_zipIdx he₂
  simp only [Nat.zero_add, Nat.sub_zero] at h₁ h₂ hc₁ hc₂
  exact ⟨h₁, h₂, hc₁.symm, hc₂.symm, htest⟩

/-- A resolution step among the lines is a candidate. -/
private theorem mem_candidates_of_getElem {lines : List (Clause V)} {k₁ k₂ : ℕ}
    (h₁ : k₁ < lines.length) (h₂ : k₂ < lines.length) {v : V} (hv : (v, true) ∈ lines[k₁]) :
    (⟨lines[k₁], k₁, lines[k₂], k₂, v⟩ : Step V) ∈ candidates lines := by
  refine List.mem_flatMap.2 ⟨(lines[k₁], k₁), List.mem_zipIdx_iff_getElem?.2 (by simp),
    List.mem_flatMap.2 ⟨(lines[k₂], k₂), List.mem_zipIdx_iff_getElem?.2 (by simp),
      List.mem_map.2 ⟨(v, true), hv, rfl⟩⟩⟩

private theorem wire_lt_of_lt {s n m k : ℕ} (hs : 0 < s) (hk : k < m) :
    n + s * k + (s - 1) < n + s * m := by
  have hmk := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hk)
  rw [Nat.mul_succ] at hmk
  omega

variable {σ : Signature.{v}} [DecidableEq Y] [DecidableEq Z]

/-- Every line gets `s` gates when each resolution step produces `s` gates. -/
theorem length_lineGatesOf {Op : Type*} {s : ℕ} (constOp : Bool → Op)
    {step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ)}
    (hstep : ∀ base w₁ w₂ v, (step base w₁ w₂ v).length = s)
    (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) :
    (lineGatesOf s constOp step n A B lines c).length = s := by
  unfold lineGatesOf
  split_ifs <;> cases findStep lines c <;> simp [hstep]

/-- Reading one more line appends its gates. -/
theorem gatesOf_append_singleton {Op : Type*} (s : ℕ) (constOp : Bool → Op)
    (step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ))
    (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) :
    gatesOf s constOp step n A B (lines ++ [c]) =
      gatesOf s constOp step n A B lines ++ lineGatesOf s constOp step n A B lines c := by
  rw [gatesOf, List.zipIdx_append, List.flatMap_append, gatesOf]
  congr 1
  · refine List.flatMap_congr fun ⟨d, k⟩ he => ?_
    dsimp only
    have := (List.mem_zipIdx he).2.1
    rw [List.take_append_of_le_length (by omega)]
  · simp

/-- Fixed-stride extraction emits `s * lines.length` gates. -/
theorem length_gatesOf {Op : Type*} {s : ℕ} (constOp : Bool → Op)
    {step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ)}
    (hstep : ∀ base w₁ w₂ v, (step base w₁ w₂ v).length = s)
    (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) :
    (gatesOf s constOp step n A B lines).length = s * lines.length := by
  induction lines using List.reverseRecOn with
  | nil => simp [gatesOf]
  | append_singleton lines c ih =>
    rw [gatesOf_append_singleton, List.length_append, ih, length_lineGatesOf constOp hstep,
      List.length_append, List.length_singleton, Nat.mul_succ]

/-- Replicated nullary gates read no wires and are well formed from any index. -/
private theorem isCodeFrom_replicate_const {op : σ.Op} (hop : σ.Arity op = 0) (n m k : ℕ) :
    Program.IsCodeFrom σ n k (List.replicate m (op, [])) := by
  induction m generalizing k with
  | zero => trivial
  | succ m ih => exact ⟨⟨hop.symm, by simp⟩, ih (k + 1)⟩

/-- The gates of one line are well formed when the shared variables of earlier lines are below
`n`. -/
theorem isCodeFrom_lineGatesOf {s n : ℕ} {constOp : Bool → σ.Op}
    {step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (σ.Op × List ℕ)}
    {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
    {lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))} {c : Clause (ℕ ⊕ (Y ⊕ Z))}
    (hs : 0 < s) (hconst : ∀ b, σ.Arity (constOp b) = 0)
    (hstep_code : ∀ {m w₁ w₂ : ℕ} {v : ℕ ⊕ (Y ⊕ Z)},
      w₁ < n + m → w₂ < n + m → (∀ i, v = .inl i → i < n) →
        Program.IsCodeFrom σ n m (step (n + m) w₁ w₂ v))
    (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom σ n (s * lines.length) (lineGatesOf s constOp step n A B lines c) := by
  unfold lineGatesOf
  split_ifs with hA hB
  · exact isCodeFrom_replicate_const (hconst false) _ _ _
  · exact isCodeFrom_replicate_const (hconst true) _ _ _
  rcases hfind : findStep lines c with _ | t
  · exact isCodeFrom_replicate_const (hconst false) _ _ _
  obtain ⟨h₁, h₂, hc₁, -, hpivot, -, -⟩ := findStep_spec hfind
  exact hstep_code (wire_lt_of_lt hs h₁) (wire_lt_of_lt hs h₂)
    fun i hi => hvars t.left (hc₁ ▸ List.getElem_mem _) i true (hi ▸ hpivot)

/-- All extracted gates are well formed when the shared variables of `lines` are below `n`. -/
theorem isCodeFrom_gatesOf {s n : ℕ} {constOp : Bool → σ.Op}
    {step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (σ.Op × List ℕ)}
    {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)} {lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))}
    (hs : 0 < s) (hconst : ∀ b, σ.Arity (constOp b) = 0)
    (hstep_len : ∀ base w₁ w₂ v, (step base w₁ w₂ v).length = s)
    (hstep_code : ∀ {m w₁ w₂ : ℕ} {v : ℕ ⊕ (Y ⊕ Z)},
      w₁ < n + m → w₂ < n + m → (∀ i, v = .inl i → i < n) →
        Program.IsCodeFrom σ n m (step (n + m) w₁ w₂ v))
    (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom σ n 0 (gatesOf s constOp step n A B lines) := by
  induction lines using List.reverseRecOn with
  | nil => trivial
  | append_singleton lines c ih =>
    rw [gatesOf_append_singleton, Program.isCodeFrom_append, length_gatesOf constOp hstep_len,
      Nat.zero_add]
    exact ⟨ih fun d hd => hvars d (List.mem_append_left _ hd),
      isCodeFrom_lineGatesOf hs hconst hstep_code fun d hd => hvars d (List.mem_append_left _ hd)⟩

/-- The value of wire `w` after evaluating the gates `G` under `I` with the `n` inputs set by
`a`. -/
def wireValue (I : Interpretation σ Bool) (n : ℕ) (G : List (σ.Op × List ℕ)) (w : ℕ)
    (a : ℕ → Bool) : Bool :=
  (evalCode I false (List.ofFn fun i : Fin n => a i) G).getD w false

/-- Further gates leave the values of existing wires unchanged. -/
theorem wireValue_append_of_lt {I : Interpretation σ Bool} {n : ℕ}
    {G G' : List (σ.Op × List ℕ)} {w : ℕ} (hw : w < n + G.length) (a : ℕ → Bool) :
    wireValue I n (G ++ G') w a = wireValue I n G w a := by
  unfold wireValue
  rw [evalCode_append]
  obtain ⟨t, ht⟩ := prefix_evalCode I false (evalCode I false (List.ofFn fun i : Fin n => a i) G) G'
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hw)]

/-- Input wire `i` carries shared variable `i`. -/
theorem wireValue_input {I : Interpretation σ Bool} {n : ℕ} {G : List (σ.Op × List ℕ)} {i : ℕ}
    (hi : i < n) (a : ℕ → Bool) : wireValue I n G i a = a i := by
  unfold wireValue
  obtain ⟨t, ht⟩ := prefix_evalCode I false (List.ofFn fun i : Fin n => a i) G
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

/-- The value of a gate of a well-formed code is its operation applied to the values of its
arguments. -/
private theorem wireValue_gate (I : Interpretation σ Bool) {n : ℕ} {G : List (σ.Op × List ℕ)}
    (hG : Program.IsCodeFrom σ n 0 G) {j : ℕ} {op : σ.Op} {args : List ℕ}
    (hg : G[j]? = some (op, args)) (a : ℕ → Bool) :
    wireValue I n G (n + j) a =
      I op fun k => args[k.val]?.elim false fun v => wireValue I n G v a := by
  have h := getD_evalCode I false (List.ofFn fun i : Fin n => a i) (by simpa using hG) hg
  unfold wireValue
  simpa only [List.length_ofFn] using h

/-- The value of gate `j` of a block appended to well-formed gates. -/
theorem wireValue_block (I : Interpretation σ Bool) {n : ℕ} {G blk : List (σ.Op × List ℕ)}
    (hcode : Program.IsCodeFrom σ n 0 (G ++ blk)) {j : ℕ} {op : σ.Op} {args : List ℕ}
    (hg : blk[j]? = some (op, args)) (a : ℕ → Bool) :
    wireValue I n (G ++ blk) (n + G.length + j) a =
      I op fun k => args[k.val]?.elim false fun v => wireValue I n (G ++ blk) v a := by
  rw [Nat.add_assoc]
  exact wireValue_gate I hcode (by rw [List.getElem?_append_right (by omega)]; simpa using hg) a

/-- Evaluating a binary gate `(op, [w₁, w₂])` at offset `j` in an appended block when both wires
come from earlier gates or inputs (`w₁, w₂ < n + G.length`). -/
theorem wireValue_block_two (I : Interpretation σ Bool) (j : ℕ) (op : σ.Op) {n : ℕ}
    {G blk : List (σ.Op × List ℕ)} {w₁ w₂ : ℕ} (hcode : Program.IsCodeFrom σ n 0 (G ++ blk))
    (hg : blk[j]? = some (op, [w₁, w₂])) (hw₁ : w₁ < n + G.length) (hw₂ : w₂ < n + G.length)
    (a : ℕ → Bool) :
    wireValue I n (G ++ blk) (n + G.length + j) a =
      I op fun k => [wireValue I n G w₁ a, wireValue I n G w₂ a][k.val]?.getD false := by
  rw [wireValue_block I hcode hg a]
  congr 1; funext k
  match k.val with
  | 0 => exact wireValue_append_of_lt hw₁ a
  | 1 => exact wireValue_append_of_lt hw₂ a
  | _ + 2 => rfl

private theorem wireValue_replicate_const {I : Interpretation σ Bool} {s n : ℕ}
    {constOp : Bool → σ.Op} {G : List (σ.Op × List ℕ)} (hs : 0 < s)
    (hconst_eval : ∀ b f, I (constOp b) f = b) (b : Bool)
    (hcode : Program.IsCodeFrom σ n 0 (G ++ List.replicate s (constOp b, []))) :
    wireValue I n (G ++ List.replicate s (constOp b, [])) (n + G.length + (s - 1)) =
      fun _ => b := by
  funext a
  have hget : (List.replicate s (constOp b, ([] : List ℕ)))[s - 1]? = some (constOp b, []) := by
    simp [Nat.sub_lt hs Nat.one_pos]
  rw [wireValue_block I hcode hget, hconst_eval]

/-- **Polymorphic soundness and decoding for fixed-stride interpolant code builders.** Given a
clause-level invariant `Inv` preserved by `step` on resolution steps, `gatesOf` and `outputWireOf`
decode on any refutation `ls` whose shared variables are below `n` to a circuit of size
`s * ls.length` computing an interpolant of `A` and `B`. -/
theorem ofCode_gatesOf {I : Interpretation σ Bool} {s n : ℕ} {constOp : Bool → σ.Op}
    {step : ℕ → ℕ → ℕ → ℕ ⊕ (Y ⊕ Z) → List (σ.Op × List ℕ)}
    {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)} {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))}
    {Inv : Clause (ℕ ⊕ (Y ⊕ Z)) → ((ℕ → Bool) → Bool) → Prop}
    (hs : 0 < s) (hconst : ∀ b, σ.Arity (constOp b) = 0)
    (hconst_eval : ∀ b f, I (constOp b) f = b)
    (hstep_len : ∀ base w₁ w₂ v, (step base w₁ w₂ v).length = s)
    (hstep_code : ∀ {m w₁ w₂ : ℕ} {v : ℕ ⊕ (Y ⊕ Z)},
      w₁ < n + m → w₂ < n + m → (∀ i, v = .inl i → i < n) →
        Program.IsCodeFrom σ n m (step (n + m) w₁ w₂ v))
    (hInv_inl : ∀ {d}, d ∈ A → Inv (d.map (Prod.map (Sum.map id Sum.inl) id)) (fun _ => false))
    (hInv_inr : ∀ {d}, d ∈ B → Inv (d.map (Prod.map (Sum.map id Sum.inr) id)) (fun _ => true))
    (hInv_empty : ∀ {f}, Inv [] f → A.IsInterpolant B f)
    (hInv_step : ∀ {G : List (σ.Op × List ℕ)} {w₁ w₂ : ℕ} {c₁ c₂ : Clause (ℕ ⊕ (Y ⊕ Z))}
      {v : ℕ ⊕ (Y ⊕ Z)},
      w₁ < n + G.length → w₂ < n + G.length → (∀ i, v = .inl i → i < n) →
      Program.IsCodeFrom σ n 0 (G ++ step (n + G.length) w₁ w₂ v) →
      Inv c₁ (wireValue I n G w₁) →
      Inv c₂ (wireValue I n G w₂) →
      Inv (c₁.resolvent c₂ v)
        (wireValue I n (G ++ step (n + G.length) w₁ w₂ v) (n + G.length + (s - 1))))
    (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls)
    (hA : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → i < n)
    (hB : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → i < n) :
    ∃ C : Circuit σ n 1,
      Circuit.ofCode n 1
        (gatesOf s constOp step n A B ls.reverse, [outputWireOf s n ls.reverse]) = some C ∧
      C.size = s * ls.length ∧
      A.IsInterpolant B fun a => C.eval I (fun i => a i) 0 := by
  have hvars := h.shared_lt hA hB
  have hvars' : ∀ d ∈ ls.reverse, ∀ i b, (.inl i, b) ∈ d → i < n :=
    fun d hd => hvars d (List.mem_reverse.1 hd)
  have happend {lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))} {c : Clause (ℕ ⊕ (Y ⊕ Z))}
      (hv : ∀ d ∈ lines ++ [c], ∀ i b, (.inl i, b) ∈ d → i < n)
      (hinv : ∀ k (hk : k < lines.length), Inv lines[k]
        (wireValue I n (gatesOf s constOp step n A B lines) (n + s * k + (s - 1))))
      (hc : c ∈ A.appendShared B ∨ ∃ c₁ ∈ lines, ∃ c₂ ∈ lines, ∃ v,
        (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v) :
      ∀ k (hk : k < (lines ++ [c]).length), Inv (lines ++ [c])[k]
        (wireValue I n (gatesOf s constOp step n A B (lines ++ [c])) (n + s * k + (s - 1))) := by
    set G := gatesOf s constOp step n A B lines
    have hG : G.length = s * lines.length := length_gatesOf constOp hstep_len n A B lines
    have hcode : Program.IsCodeFrom σ n 0 (G ++ lineGatesOf s constOp step n A B lines c) := by
      rw [← gatesOf_append_singleton]
      exact isCodeFrom_gatesOf hs hconst hstep_len hstep_code hv
    intro k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have hval : wireValue I n (gatesOf s constOp step n A B (lines ++ [c]))
          (n + s * k + (s - 1)) = wireValue I n G (n + s * k + (s - 1)) := funext fun a => by
        rw [gatesOf_append_singleton]
        exact wireValue_append_of_lt (hG ▸ wire_lt_of_lt hs hk) a
      simpa only [List.getElem_append_left hk, hval] using hinv k hk
    · simp only [List.getElem_concat_length, gatesOf_append_singleton]
      have hbase : n + s * lines.length = n + G.length := by rw [hG]
      by_cases hcA : c ∈ A.relabel (Sum.map id Sum.inl)
      · have hline : lineGatesOf s constOp step n A B lines c =
            List.replicate s (constOp false, []) := by simp only [lineGatesOf, hcA, ↓reduceIte]
        rw [hline] at hcode ⊢
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hcA
        rw [hbase, wireValue_replicate_const hs hconst_eval false hcode]
        exact hInv_inl hd
      by_cases hcB : c ∈ B.relabel (Sum.map id Sum.inr)
      · have hline : lineGatesOf s constOp step n A B lines c =
            List.replicate s (constOp true, []) := by simp only [lineGatesOf, hcA, hcB, ↓reduceIte]
        rw [hline] at hcode ⊢
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hcB
        rw [hbase, wireValue_replicate_const hs hconst_eval true hcode]
        exact hInv_inr hd
      rcases hfind : findStep lines c with _ | t
      · exfalso
        rcases hc with hc | ⟨c₁, hc₁, c₂, hc₂, v, hv₁, hv₂, rfl⟩
        · rcases List.mem_append.1 hc with hc | hc
          exacts [hcA hc, hcB hc]
        · obtain ⟨k₁, hk₁, rfl⟩ := List.getElem_of_mem hc₁
          obtain ⟨k₂, hk₂, rfl⟩ := List.getElem_of_mem hc₂
          exact List.find?_eq_none.1 hfind _ (mem_candidates_of_getElem hk₁ hk₂ hv₁)
            (by simp [hv₁, hv₂])
      obtain ⟨h₁, h₂, hc₁, hc₂, hpivot, -, hres⟩ := findStep_spec hfind
      have hline : lineGatesOf s constOp step n A B lines c =
          step (n + G.length) (n + s * t.leftIndex + (s - 1))
            (n + s * t.rightIndex + (s - 1)) t.pivot := by
        simp only [lineGatesOf, hcA, hcB, ↓reduceIte, hfind, Option.elim_some, hbase]
      have hw₁ : n + s * t.leftIndex + (s - 1) < n + G.length := hG ▸ wire_lt_of_lt hs h₁
      have hw₂ : n + s * t.rightIndex + (s - 1) < n + G.length := hG ▸ wire_lt_of_lt hs h₂
      rw [hline] at hcode ⊢
      rw [hbase]
      obtain ⟨c₁, k₁, c₂, k₂, v⟩ := t
      dsimp only at h₁ h₂ hc₁ hc₂ hpivot hres hw₁ hw₂ hcode ⊢
      subst c
      exact hInv_step hw₁ hw₂
        (fun i hi => hv c₁ (List.mem_append_left _ (hc₁ ▸ List.getElem_mem _)) i true (hi ▸ hpivot))
        hcode (hc₁ ▸ hinv k₁ h₁) (hc₂ ▸ hinv k₂ h₂)
  have hrev : ∀ {ls' : List (Clause (ℕ ⊕ (Y ⊕ Z)))}, (A.appendShared B).IsProof ls' →
      (∀ d ∈ ls', ∀ i b, (.inl i, b) ∈ d → i < n) →
      ∀ k (hk : k < ls'.reverse.length), Inv ls'.reverse[k]
        (wireValue I n (gatesOf s constOp step n A B ls'.reverse) (n + s * k + (s - 1))) := by
    intro ls' hp hv
    induction hp with
    | nil => intro k hk; simp at hk
    | @mem ls' c _ hc ih =>
      rw [List.reverse_cons]
      exact happend (fun d hd => hv d (by simpa [or_comm] using hd))
        (ih fun d hd => hv d (List.mem_cons_of_mem _ hd)) (Or.inl hc)
    | @resolvent ls' c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
      rw [List.reverse_cons]
      exact happend (fun d hd => hv d (by simpa [or_comm] using hd))
        (ih fun d hd => hv d (List.mem_cons_of_mem _ hd))
        (Or.inr ⟨c₁, List.mem_reverse.2 h₁, c₂, List.mem_reverse.2 h₂, v, hv₁, hv₂, rfl⟩)
  set k := (ls.reverse.map List.isEmpty).idxOf true with hk_def
  have hk : k < ls.reverse.length := by
    simpa only [List.length_map] using List.idxOf_lt_length_of_mem (a := true)
      (l := ls.reverse.map List.isEmpty) (List.mem_map.2 ⟨[], List.mem_reverse.2 hnil, rfl⟩)
  have hempty : ls.reverse[k] = [] := List.isEmpty_iff.1 <| by
    rw [← List.getElem_map List.isEmpty]
    exact List.getElem_idxOf (by rw [List.length_map]; exact hk)
  have hcode := isCodeFrom_gatesOf (A := A) (B := B) hs hconst hstep_len hstep_code hvars'
  have hlen := length_gatesOf constOp hstep_len n A B ls.reverse
  set code := (gatesOf s constOp step n A B ls.reverse, [outputWireOf s n ls.reverse])
  have hsome : (Circuit.ofCode n 1 code : Option (Circuit σ n 1)).isSome := by
    rw [Circuit.isSome_ofCode_iff]
    refine ⟨hcode, rfl, ?_⟩
    simp only [code, outputWireOf, List.mem_singleton, forall_eq, hlen]
    rw [← hk_def]
    exact wire_lt_of_lt hs hk
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 hsome
  have hCcode := Circuit.code_of_ofCode_eq_some hC
  refine ⟨C, hC, ?_, ?_⟩
  · rw [← Circuit.length_code_fst, hCcode]
    simp only [code, hlen, List.length_reverse]
  · have hout : (C.outputs 0).toNat = n + s * k + (s - 1) := by
      have := congrArg (fun c => c.2) hCcode
      simp only [Circuit.code, code, outputWireOf, List.ofFn_succ, List.ofFn_zero] at this
      exact (List.cons.inj this).1
    have hinv := hrev h hvars k hk
    rw [hempty] at hinv
    convert hInv_empty hinv using 2 with a
    rw [Circuit.eval_eq_getD C I false, hout, hCcode]
    rfl

end Polymorphic

/-! ### De Morgan interpolant extraction -/

variable {Y Z : Type*} {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
  {lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))} {c : Clause (ℕ ⊕ (Y ⊕ Z))}

/-- A resolution step has four gates. -/
@[simp] theorem length_resolventGates (base w₁ w₂ : ℕ) (v : ℕ ⊕ (Y ⊕ Z)) :
    (resolventGates base w₁ w₂ v).length = 4 := by
  rcases v with _ | _ | _ <;> rfl

private theorem isCodeFrom_resolventGates {m w₁ w₂ : ℕ} {v : ℕ ⊕ (Y ⊕ Z)}
    (h₁ : w₁ < n + m) (h₂ : w₂ < n + m) (hv : ∀ i, v = .inl i → i < n) :
    Program.IsCodeFrom signature n m (resolventGates (n + m) w₁ w₂ v) := by
  rcases v with i | _ | _
  · have hi := hv i rfl
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> (simp; omega)
  all_goals exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, ⟨rfl, by simp; omega⟩, trivial⟩

variable [DecidableEq Y] [DecidableEq Z]

/-- Every line has four gates. -/
@[simp] theorem length_lineGates : (lineGates n A B lines c).length = 4 :=
  length_lineGatesOf Op.const length_resolventGates n A B lines c

/-- Reading one more line appends its gates. -/
theorem gates_append_singleton :
    gates n A B (lines ++ [c]) = gates n A B lines ++ lineGates n A B lines c :=
  gatesOf_append_singleton 4 Op.const resolventGates n A B lines c

/-- **The code has four gates per line.** -/
@[simp] theorem length_gates : (gates n A B lines).length = 4 * lines.length :=
  length_gatesOf Op.const length_resolventGates n A B lines

/-- **The gates of a line are well formed**, when the shared variables of the earlier lines are
below `n`. -/
theorem isCodeFrom_lineGates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom signature n (4 * lines.length) (lineGates n A B lines c) :=
  isCodeFrom_lineGatesOf (by decide) (fun _ => rfl) isCodeFrom_resolventGates hvars

/-- **The code is well formed** when the shared variables of the lines are below `n`: each gate
has the arity of its operation and reads only the shared-variable inputs and earlier gates. -/
theorem isCodeFrom_gates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom signature n 0 (gates n A B lines) :=
  isCodeFrom_gatesOf (by decide) (fun _ => rfl) length_resolventGates isCodeFrom_resolventGates
    hvars

end Interpolant

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- **Extracting the interpolant of a refutation.** If `ls` is a resolution refutation of
`A(x, y) ∧ B(x, z)` whose shared variables are below `n`, then `interpolantCode n A B ls` is the
code of a De Morgan circuit with `n` inputs and four gates per line of the refutation, computing an
interpolant of `A` and `B` [Pudlák, Theorem 1][Pudlak1997], [Krajíček, Theorem 6.1][Krajicek1997].
-/
theorem CNF.IsProof.ofCode_interpolantCode {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
    {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls)
    (hA : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → i < n) (hB : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → i < n) :
    ∃ C : Circuit signature n 1, Circuit.ofCode n 1 (CNF.interpolantCode n A B ls) = some C ∧
      C.size = 4 * ls.length ∧
      A.IsInterpolant B fun a => C.eval interpretation (fun i => a i) 0 := by
  refine Interpolant.ofCode_gatesOf (Inv := A.IsInterpolantAt B) (by decide) (fun _ => rfl)
    (fun _ _ => rfl) Interpolant.length_resolventGates Interpolant.isCodeFrom_resolventGates
    (fun hd => CNF.isInterpolantAt_relabel_inl hd) (fun hd => CNF.isInterpolantAt_relabel_inr hd)
    (fun h0 => h0.isInterpolant) ?_ h hnil hA hB
  intro G w₁ w₂ c₁ c₂ v hw₁ hw₂ hv hcode hg₁ hg₂
  rcases v with i | j | k
  · have hi := hv i rfl
    convert hg₁.resolvent_inl i hg₂ using 1
    funext a
    have e₀ := Interpolant.wireValue_block interpretation hcode (j := 0) (op := .not)
      (args := [i]) rfl a
    have e₁ := Interpolant.wireValue_block interpretation hcode (j := 1) (op := .and)
      (args := [n + G.length, w₁]) rfl a
    have e₂ := Interpolant.wireValue_block interpretation hcode (j := 2) (op := .and)
      (args := [i, w₂]) rfl a
    have e₃ := Interpolant.wireValue_block interpretation hcode (j := 3) (op := .or)
      (args := [n + G.length + 1, n + G.length + 2]) rfl a
    simp only [Nat.add_zero] at e₀
    rw [e₃]
    simp only [interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim,
      Fin.isValue, Fin.val_zero, Fin.val_one] at e₀ e₁ e₂ e₃ ⊢
    rw [e₁, e₂, e₀, Interpolant.wireValue_input hi, Interpolant.wireValue_append_of_lt hw₁,
      Interpolant.wireValue_append_of_lt hw₂]
  · convert hg₁.resolvent_inr_inl j hg₂ using 1
    exact funext (Interpolant.wireValue_block_two interpretation 3 .or hcode rfl hw₁ hw₂)
  · convert hg₁.resolvent_inr_inr k hg₂ using 1
    exact funext (Interpolant.wireValue_block_two interpretation 3 .and hcode rfl hw₁ hw₂)

end Cslib.Logic.PL
