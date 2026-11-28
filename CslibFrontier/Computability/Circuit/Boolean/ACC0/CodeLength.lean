/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.UniversalSimulation
public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Computability.Circuit.Boolean.Multiplicity
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Circuit.MapLines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Short codes for `AC⁰[q]` circuits

The size of a circuit counts its gates, not the wires they read, and a gate of the extended
unbounded fan-in basis may read a wire any number of times, so the code of a small circuit
(`Cslib.Circuits.Circuit.encCode`) may be long. Under `Unbounded.extInterpretation (modGate q)`
with `0 < q`, a conjunction or disjunction may read each of its wires once, and a `MOD_q` gate may
read each of its wires as often as its multiplicity modulo `q`. Replacing every line accordingly
(after `Unbounded.multLine`) keeps the function, the size and the depth bound, and bounds every
fan-in by `q * (n + s)` (`Unbounded.modCircuit`). A circuit of bounded fan-in has
a code of length polynomial in its inputs, gates, outputs and fan-in
(`Unbounded.length_encCode_le_of_arity_le`), so every `AC⁰[q]` circuit has an equivalent one of the
same size and no larger depth whose code has polynomial length
(`Unbounded.exists_length_encCode_le`). Hardwiring a prefix into small circuits for a language, or
the encoding of a circuit into small circuits for circuit evaluation, then gives circuits of depth
one larger whose codes have polynomial length (`Unbounded.exists_hardwirePrefix_code_le`,
`Unbounded.exists_computes_code_le`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.modCircuit`: the circuit whose gates read their wires as few
  times as `MOD_q` semantics allows.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_modCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.size_modCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.depth_modCircuit_le`,
  `Cslib.Circuits.Boolean.Unbounded.arity_lines_modCircuit_le`: the function, the size and the depth
  bound are kept, and every fan-in is at most `q * (n + s)`.
* `Cslib.Circuits.Boolean.Unbounded.length_encCode_le_of_arity_le`: the code length of a circuit of
  bounded fan-in.
* `Cslib.Circuits.Boolean.Unbounded.exists_length_encCode_le`: every `AC⁰[q]` circuit has an
  equivalent one of the same size, no larger depth and polynomial code length.
* `Cslib.Circuits.Boolean.Unbounded.exists_hardwirePrefix_code_le`: polynomial-size depth-`d`
  circuits for a language give, for every prefix, circuits of depth `d + 1` for the language with
  the prefix hardwired, whose codes are polynomial in the prefix length and the number of inputs.
* `Cslib.Circuits.Boolean.Unbounded.exists_computes_code_le`: the same for De Morgan circuits,
  from circuits for `circuitEvalLanguage`.
-/

public section

namespace Cslib.Circuits.Boolean.Unbounded

open Turing.MultiTapeTM

variable {n g m : ℕ}

/-! ### Reading wires modulo `q` -/

/-- The wires a symmetric gate reading `w i` with multiplicity `mult i` reads when each
multiplicity is taken modulo `q`. -/
@[expose] def modWires (q : ℕ) {N : ℕ} (mult : Fin N → ℕ) (w : Fin N → Wire n g) :
    List (Wire n g) :=
  (List.finRange N).flatMap fun i => List.replicate (mult i % q) (w i)

/-- A line of the basis with multiplicities as a line of the extended basis: an unbounded fan-in
gate is kept, and a symmetric gate reading `w i` with multiplicity `mult i` becomes an extra gate
reading `w i` as often as `mult i % q`. -/
@[expose] def modLine (q : ℕ) : Line multSignature n g → Line extSignature n g
  | ⟨.ac op, w⟩ => ⟨.ac op, w⟩
  | ⟨.gate _ mult, w⟩ => ⟨.gate (modWires q mult w).length, (modWires q mult w).get⟩

private theorem count_map_modWires (q : ℕ) {N : ℕ} (mult : Fin N → ℕ) (w : Fin N → Wire n g)
    (v : Wire n g → Bool) :
    ((modWires q mult w).map v).count true = ∑ i, mult i % q * (v (w i)).toNat := by
  rw [modWires, List.map_flatMap, List.count_flatMap, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, List.map_replicate, List.count_replicate]
  cases v (w i) <;> simp

/-- Reading wires modulo `q` keeps the value of a line under `MOD_q` semantics. -/
private theorem eval_modLine (q : ℕ) (line : Line multSignature n g) (x : Fin n → Bool)
    (gates : Fin g → Bool) :
    (modLine q line).eval (extInterpretation (modGate q)) x gates =
      line.eval (multInterpretation fun _ c => decide (c % q ≠ 0)) x gates := by
  obtain ⟨op, w⟩ := line
  cases op with
  | ac op => rfl
  | gate N mult =>
    change modGate q _ (Wire.elim x gates ∘ (modWires q mult w).get) =
      decide (multWeight mult (Wire.elim x gates ∘ w) % q ≠ 0)
    have hofFn : List.ofFn (Wire.elim x gates ∘ (modWires q mult w).get) =
        (modWires q mult w).map (Wire.elim x gates) := by
      rw [← List.ofFn_getElem_eq_map]
      rfl
    have hmod : (∑ i, mult i % q * (Wire.elim x gates (w i)).toNat) % q =
        (∑ i, mult i * (Wire.elim x gates (w i)).toNat) % q := by
      rw [Finset.sum_nat_mod]
      conv_rhs => rw [Finset.sum_nat_mod]
      exact congrArg (· % q) (Finset.sum_congr rfl fun i _ => Nat.mod_mul_mod _ _ _)
    rw [modGate, ← List.count_ofFn, hofFn, count_map_modWires, hmod]
    rfl

/-- Reading wires modulo `q` makes no line deeper. -/
private theorem depth_modLine_le (q : ℕ) (line : Line multSignature n g) (depths : Wire n g → ℕ) :
    (modLine q line).depth depths ≤ line.depth depths := by
  obtain ⟨op, w⟩ := line
  cases op with
  | ac op => exact le_rfl
  | gate N mult =>
    set line : Line multSignature n g := ⟨.gate N mult, w⟩
    have hpos := line.depth_pos depths
    have hle : ∀ a, depths (w a) ≤ line.depth depths - 1 := fun a => by
      have : depths (w a) < line.depth depths := line.wireDepth_lt_depth depths a
      omega
    refine ((Line.depth_le_add_one_iff _ depths (d := line.depth depths - 1)).2 fun j => ?_).trans
      (by omega)
    have hj : (modWires q mult w).get j ∈ modWires q mult w := List.get_mem _ _
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hj
    change depths ((modWires q mult w).get j) ≤ _
    rw [List.eq_of_mem_replicate hi]
    exact hle i

/-- Reading wires modulo `q > 0` reads at most `q` times as many wires as the line did. -/
private theorem arity_modLine_le {q : ℕ} (hq : 0 < q) (line : Line multSignature n g) :
    extSignature.Arity (modLine q line).op ≤ q * multSignature.Arity line.op := by
  obtain ⟨op, w⟩ := line
  cases op with
  | ac op => exact Nat.le_mul_of_pos_left _ hq
  | gate N mult =>
    change (modWires q mult w).length ≤ q * N
    rw [modWires, List.length_flatMap]
    calc ((List.finRange N).map fun i => (List.replicate (mult i % q) (w i)).length).sum
        ≤ ((List.finRange N).map fun _ => q).sum :=
          List.sum_le_sum fun i _ => by
            rw [List.length_replicate]
            exact (Nat.mod_lt _ hq).le
      _ = q * N := by simp [Nat.mul_comm]

/-! ### The normalized circuit -/

/-- The circuit whose conjunctions and disjunctions read their distinct wires once and whose
extra gates read each distinct wire as often as its multiplicity modulo `q`. -/
@[expose] def modCircuit (q : ℕ) (C : Circuit extSignature n m) : Circuit extSignature n m :=
  C.mapLines fun line => modLine q (multLine line)

/-- Normalizing fan-in keeps the size. -/
@[simp] theorem size_modCircuit (q : ℕ) (C : Circuit extSignature n m) :
    (modCircuit q C).size = C.size :=
  rfl

/-- **Normalizing fan-in keeps the function computed** under `MOD_q` semantics. -/
theorem eval_modCircuit (q : ℕ) (C : Circuit extSignature n m) :
    (modCircuit q C).eval (extInterpretation (modGate q)) =
      C.eval (extInterpretation (modGate q)) :=
  Circuit.eval_mapLines (fun line x gates => by
    rw [eval_modLine, eval_multLine (f := modGate q) (fun _ _ => rfl)]) C

/-- Normalizing fan-in makes no gate deeper. -/
theorem depth_modCircuit_le (q : ℕ) (C : Circuit extSignature n m) :
    (modCircuit q C).depth ≤ C.depth :=
  Circuit.depth_mapLines_le (fun line depths =>
    (depth_modLine_le q _ depths).trans (depth_multLine_le line depths)) C

/-- Every gate of `modCircuit q C`, for `0 < q`, reads at most `q * (n + C.size)` wires. -/
theorem arity_lines_modCircuit_le {q : ℕ} (hq : 0 < q) (C : Circuit extSignature n m)
    (k : Fin C.size) :
    extSignature.Arity ((modCircuit q C).program.lines k).op ≤ q * (n + C.size) :=
  Program.arity_lines_mapLines_le (B := fun t => q * t) (fun _ _ h => Nat.mul_le_mul_left q h)
    (fun line => (arity_modLine_le hq _).trans (Nat.mul_le_mul_left q (arity_multLine_le line)))
    C.program k

/-! ### Code length -/

private theorem toNat_le_arity (op : ExtOp) : op.toNat ≤ 3 * extSignature.Arity op + 3 := by
  rcases op with (_ | k | k) | k <;> simp only [ExtOp.toNat, ExtOp.arity, Op.arity] <;> omega

/-- **The code of a circuit of bounded fan-in is short**: if every gate of `c` reads at most `F`
wires, its code has length at most `32 (F + 1) (n + s + 1) (s + m + 1)` for `s = c.size`. -/
theorem length_encCode_le_of_arity_le (c : Circuit extSignature n m) {F : ℕ}
    (hF : ∀ k, extSignature.Arity (c.program.lines k).op ≤ F) :
    (Circuit.encCode encExtOp c.code).length ≤
      32 * (F + 1) * (n + c.size + 1) * (c.size + m + 1) := by
  set L := n + c.size
  have hwire (w : Wire n c.size) : (encNat w.toNat).length ≤ L :=
    (length_encNat_le_self _).trans (Wire.toNat_lt w).le
  have hgate (k : Fin c.size) :
      (Circuit.encGate encExtOp (c.program.lines k).code).length ≤ 7 * ((F + 1) * (L + 1)) := by
    set line := c.program.lines k
    have hop : (encExtOp line.op).length ≤ 3 * F + 3 := by
      have h := toNat_le_arity line.op
      have hFk : extSignature.Arity line.op ≤ F := hF k
      simp only [encExtOp, Function.Embedding.coeFn_mk, encUnary_apply, List.length_replicate]
      omega
    have hargs : (encList encNat line.code.2).length ≤ F * (2 * L + 1) := by
      have h := length_encList_le encNat line.code.2 (b := L) fun i hi => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
        exact hwire (line.wires j)
      rw [Line.length_code_snd] at h
      exact h.trans (Nat.mul_le_mul_right _ (hF k))
    rw [Circuit.encGate, length_encPair, Line.code_fst]
    nlinarith
  have hgates := length_encList_le (Circuit.encGate encExtOp) c.code.1
    (b := 7 * ((F + 1) * (L + 1))) fun gate hg => by
      rw [Circuit.code, Program.code_eq_ofFn_lines] at hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact hgate j
  rw [Circuit.length_code_fst] at hgates
  have houtputs : (encList encNat c.code.2).length ≤ m * (2 * L + 1) := by
    have h := length_encList_le encNat c.code.2 (b := L) fun i hi => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact hwire (c.outputs j)
    simpa [Circuit.code] using h
  have hLP : 2 * L + 1 ≤ 2 * ((F + 1) * (L + 1)) := by nlinarith
  have hP : 1 ≤ (F + 1) * (L + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  rw [Circuit.encCode, length_encPair,
    show 32 * (F + 1) * (L + 1) * (c.size + m + 1) =
      32 * ((F + 1) * (L + 1)) * (c.size + m + 1) by ring]
  generalize (F + 1) * (L + 1) = P at hgates hLP hP ⊢
  have h7 : c.size * (2 * (7 * P) + 1) ≤ 15 * (c.size * P) := by
    nlinarith [Nat.mul_le_mul_left c.size hP]
  have hm : m * (2 * L + 1) ≤ 2 * (m * P) := by nlinarith [Nat.mul_le_mul_left m hLP]
  nlinarith

/-- **Every `AC⁰[q]` circuit has a short code**, for `0 < q`: an equivalent circuit of the same size
and no larger depth whose code has length at most `32 (q (n + s) + 1) (n + s + 1) (s + m + 1)` for
`s = C.size`. -/
theorem exists_length_encCode_le {q : ℕ} (hq : 0 < q) (C : Circuit extSignature n m) :
    ∃ C' : Circuit extSignature n m,
      C'.eval (extInterpretation (modGate q)) = C.eval (extInterpretation (modGate q)) ∧
      C'.size = C.size ∧ C'.depth ≤ C.depth ∧
      (Circuit.encCode encExtOp C'.code).length ≤
        32 * (q * (n + C.size) + 1) * (n + C.size + 1) * (C.size + m + 1) :=
  ⟨modCircuit q C, eval_modCircuit q C, rfl, depth_modCircuit_le q C,
    length_encCode_le_of_arity_le _ (arity_lines_modCircuit_le hq C)⟩

/-! ### Hardwired circuits with short codes -/

/-- **Hardwiring a prefix into small circuits gives short codes.** Suppose a language `L` has
circuits of depth at most `d` and polynomially bounded size over the extended basis with `MOD_q`
gates, `0 < q`. Then there are `c` and `k` such that, for every prefix `p` and every number `r` of
live inputs, some circuit `W` of depth at most `d + 1` on `r` inputs has the value `p ++ v ∈ L` at
every input `v` and a code of length at most `c * (|p| + r + 1) ^ k`: hardwire `p` into the circuit
at length `|p| + r` and normalize its fan-in (`exists_length_encCode_le`). -/
theorem exists_hardwirePrefix_code_le {q d : ℕ} (hq : 0 < q) {L : Language Bool} {s : ℕ → ℕ}
    (hs : PolynomiallyBounded s)
    (hL : ∀ N, ∃ C : Circuit extSignature N 1,
      C.Computes (extInterpretation (modGate q)) (single (L.slice N)) ∧
      C.depth ≤ d ∧ C.size ≤ s N) :
    ∃ c k : ℕ, ∀ (p : List Bool) (r : ℕ), ∃ W : Circuit extSignature r 1,
      (∀ v : BitString r,
        W.eval (extInterpretation (modGate q)) v 0 = true ↔ p ++ List.ofFn v ∈ L) ∧
      W.depth ≤ d + 1 ∧
      (Circuit.encCode encExtOp W.code).length ≤ c * (p.length + r + 1) ^ k := by
  obtain ⟨cs, ks, hs_le⟩ := polynomiallyBounded_iff_le.1 hs
  let P : ℕ → ℕ := fun N => cs * (N + 1) ^ ks + 2
  let B : ℕ → ℕ := fun N => 32 * (q * (N + P N) + 1) * (N + P N + 1) * (P N + 1 + 1)
  have hB : PolynomiallyBounded B := by dsimp only [B, P]; fun_prop
  obtain ⟨cB, kB, hB_le⟩ := polynomiallyBounded_iff_le.1 hB
  refine ⟨cB, kB, fun p r => ?_⟩
  obtain ⟨C, hC, hCd, hCs⟩ := hL (p.length + r)
  obtain ⟨W, hWe, hWs, hWd, hWc⟩ := exists_length_encCode_le hq (hardwirePrefix toExt p C)
  refine ⟨W, fun v => ?_,
    hWd.trans ((depth_hardwirePrefix_le _ _ _).trans (Nat.add_le_add_right hCd 1)), ?_⟩
  · classical
    rw [hWe, eval_hardwirePrefix,
      congrFun (hC (BitString.ofList (p.length + r) (p ++ List.ofFn v))) 0]
    simp only [single, Language.slice]
    rw [BitString.ofFn_ofList (by simp), decide_eq_true_eq]
  · have hS : (hardwirePrefix toExt p C).size ≤ P (p.length + r) := by
      rw [size_hardwirePrefix]
      have := hCs.trans (hs_le (p.length + r))
      dsimp only [P]
      omega
    have hr : r ≤ p.length + r := Nat.le_add_left _ _
    calc (Circuit.encCode encExtOp W.code).length
        ≤ 32 * (q * (r + (hardwirePrefix toExt p C).size) + 1) *
            (r + (hardwirePrefix toExt p C).size + 1) *
            ((hardwirePrefix toExt p C).size + 1 + 1) := hWc
      _ ≤ B (p.length + r) := by dsimp only [B]; gcongr
      _ ≤ cB * (p.length + r + 1) ^ kB := hB_le _

/-- **Short codes for hardwired circuit evaluation.** Suppose `circuitEvalLanguage` has circuits of
depth at most `d` and polynomially bounded size over the extended basis with `MOD_q` gates,
`0 < q` (as `P ⊆ ACC⁰` gives). Then there are `c` and `k` such that every De Morgan circuit `C` on
`r` inputs is computed by a circuit of depth at most `d + 1` over that basis whose code has length
at most `c * (r + |C| + 1) ^ k`: hardwire `evalPrefix C`
(`exists_hardwirePrefix_code_le`, `length_evalPrefix_le`). -/
theorem exists_computes_code_le {q d : ℕ} (hq : 0 < q) {s : ℕ → ℕ} (hs : PolynomiallyBounded s)
    (hEval : ∀ N, ∃ C : Circuit extSignature N 1,
      C.Computes (extInterpretation (modGate q)) (single (circuitEvalLanguage.slice N)) ∧
      C.depth ≤ d ∧ C.size ≤ s N) :
    ∃ c k : ℕ, ∀ {r : ℕ} (C : Circuit Boolean.signature r 1), ∃ W : Circuit extSignature r 1,
      W.Computes (extInterpretation (modGate q)) (C.eval Boolean.interpretation) ∧ W.depth ≤ d + 1 ∧
      (Circuit.encCode encExtOp W.code).length ≤ c * (r + C.size + 1) ^ k := by
  obtain ⟨c, k, h⟩ := exists_hardwirePrefix_code_le hq hs hEval
  refine ⟨c * 249 ^ k, 2 * k, fun {r} C => ?_⟩
  obtain ⟨W, hWe, hWd, hWc⟩ := h (evalPrefix C) r
  refine ⟨W, fun v => ?_, hWd, ?_⟩
  · funext o
    rw [Subsingleton.elim o 0, Bool.eq_iff_iff, hWe, mem_circuitEvalLanguage_evalPrefix]
  · have hlog := Nat.log_le_self 2 (r + C.size + 1)
    have hlen := length_evalPrefix_le C
    have hpre : (evalPrefix C).length + r + 1 ≤ 249 * (r + C.size + 1) ^ 2 := by
      set t := r + C.size + 1 with ht
      have hC : C.size + 1 ≤ t := by omega
      have h1 : 124 * (C.size + 1) * (Nat.log 2 t + 1) ≤ 124 * t * (t + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hC) (by omega)
      have ht1 : t ≤ t ^ 2 := by nlinarith
      nlinarith
    calc (Circuit.encCode encExtOp W.code).length ≤ c * ((evalPrefix C).length + r + 1) ^ k := hWc
      _ ≤ c * (249 * (r + C.size + 1) ^ 2) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpre k)
      _ = c * 249 ^ k * (r + C.size + 1) ^ (2 * k) := by rw [mul_pow, ← pow_mul]; ring

end Cslib.Circuits.Boolean.Unbounded
