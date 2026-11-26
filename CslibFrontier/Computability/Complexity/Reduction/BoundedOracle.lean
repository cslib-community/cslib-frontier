/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Space
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.DisjointInstances
public import CslibFrontier.Computability.Complexity.FineGrained.SearchStep
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.QueryBounds

/-!
# Oracle reductions with explicit query and answer lengths

`Cslib.Complexity.PolyTimeTuringReducible`
(`CslibFrontier/Computability/Complexity/Reduction/Turing.lean`) and
`Cslib.Complexity.ComputableInPolyTimeWithOracle`
(`CslibFrontier/Computability/Complexity/Classes/Oracle.lean`) quantify over adaptive
deterministic `WordQueryComp` programs certified by `IsOraclePPTOn` against one-bit language
oracles. Fine-grained and exact exponential complexity require explicit quantitative accounting of
the oracle interaction across both decision and multi-bit function oracles:

* `Cslib.Complexity.OracleCallBound`: an `enc_structure`-backed record tracking four explicit
  quantities on each input `a`:
  * `qcount`: number of oracle queries issued along the run;
  * `qlen`: maximum bit-length of any single query word issued along the run;
  * `totalQlen`: total bit-length `∑ q, |q|` summed across all queries issued along the run;
  * `alen`: maximum bit-length of any oracle answer returned along the run.
* `Cslib.Complexity.BoundedOracleProgram`: a `#4391` `structure` packaging a deterministic adaptive
  `WordQueryComp` program, its `IsOraclePPTOn` certificate, an explicit `OracleCallBound` profile
  respected against `oracle : List Bool → List Bool`, and a polynomial-time unary answer-length
  allowance `alenCap` enabling open handler substitution.
* `Cslib.Complexity.BoundedOracleReduction`: the specialization to typed decision problems
  `(A, encA)` and `(B, encB)` against `languageOracle (encB '' B)` (`alen ≤ 1`).

In addition to identity, zero-query polynomial-time lifts, single-query many-one/function lifts,
and bridges to `PolyTimeTuringReducible` and `PWithOracleQueries`, this module extends
`Turing.MultiTapePTM` simulation from one-bit `receiveBit` to arbitrary word replies `receiveWord`,
proving:

1. **Composition (`BoundedOracleProgram.comp`, `BoundedOracleReduction.trans`):** explicit
   worst-case composition via `wordMax` and sharper linear `totalQlen` composition when the inner
   total query length is affine in the outer query length.
2. **Polynomial-time and polynomial-space multi-bit oracle transfer
   (`BoundedOracleProgram.computableInPolyTime`,
   `BoundedOracleProgram.exists_computableInO_polySpace`):**
   simulator workspace is bounded in terms of input length, clock, answer-length cap, and simulated
   oracle workspace — never as a polynomial in simulated oracle running time.
3. **Parameterized exponential and subexponential time transfer
   (`BoundedOracleReduction.decidableInExpTime`, `BoundedOracleReduction.decidableInSubexpTime`):**
   guarding oracle calls by a polynomial-time validity/length predicate that holds along
   `queriesWith` transfers `2 ^ (δ * μB)` deciders to `2 ^ (scale * δ * μA)` with polynomial
   overhead absorbing query count and construction cost.

## Main definitions

* `Cslib.Complexity.OracleCallBound`, `Cslib.Complexity.OracleCallBound.Respects`: explicit
  `(qcount, qlen, totalQlen, alen)` call budget and run satisfaction predicate.
* `Turing.MultiTapePTM.receiveWord`: multi-bit reply installation on `FiniteConfig`.
* `Cslib.Complexity.BoundedOracleProgram`: multi-bit functional oracle program with explicit query
  and answer length accounting.
* `Cslib.Complexity.BoundedOracleReduction`: language oracle reduction with explicit query and
  answer length accounting.

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_run_word`,
  `Turing.MultiTapePTM.exists_computableInO_run_word`: multi-bit clocked oracle machine simulation
  in polynomial time and in polynomial workspace.
* `Cslib.Complexity.BoundedOracleProgram.id`, `.ofPolyTime`, `.ofSingleQuery`, `.comp`,
  `.compAffine`, `.totalQueryLength_comp_affine`, `.computableInPolyTime`,
  `.exists_computableInO_polySpace`, `.computableInPolySpace`.
* `Cslib.Complexity.BoundedOracleReduction.refl`, `.ofPolyTime`, `.ofSizeSensitive`,
  `.transDecoded`, `.trans`, `.polyTimeTuringReducible`, `.mem_PWithOracleQueries`,
  `.ofPWithOracleQueries`, `.mem_P`, `.mem_PSPACE`, `.decidableInExpTime`,
  `.decidableInSubexpTime`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

public section

/-! ### Multi-bit oracle simulation on `Turing.MultiTapePTM` -/

namespace Turing.MultiTapePTM

open Cslib Cslib.Complexity MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

/-- Install a multi-bit word reply to the pending query on `p.1`; leave `p.1` unchanged when no
query is pending. -/
@[expose]
def receiveWord (p : FiniteConfig k Bool Control Operation × List Bool) :
    FiniteConfig k Bool Control Operation :=
  match machine.pendingQuery p.1 with
  | some (op, next) => p.1.receive op next p.2
  | none => p.1

/-- Against any word oracle `oracle : List Bool → List Bool`, one `answerStep` either installs
`oracle (machine.pendingRequest cfg)` via `receiveWord` or executes `localStep`. -/
theorem answerStep_word (oracle : List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Operation) :
    machine.answerStep (fun q => oracle q.2) cfg =
      if (machine.pendingQuery cfg).isSome then
        machine.receiveWord (cfg, oracle (machine.pendingRequest cfg))
      else machine.localStep cfg := by
  unfold answerStep receiveWord pendingRequest localStep pendingQuery
  cases cfg.tapes.state with
  | none => rfl
  | some control =>
    simp only [Option.map_some]
    cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
      false <;> rfl

/-- When every reply to a request of length at most `steps` has length at most `answerSize`, one
`answerStep` advances `FiniteConfig.SpaceBound` from `steps` to `steps + 1` with the same
`answerSize`. -/
theorem spaceBound_answerStep_word (oracle : List Bool → List Bool)
    {inputSize steps answerSize : ℕ} {cfg : FiniteConfig k Bool Control Operation}
    (h : FiniteConfig.SpaceBound inputSize steps answerSize cfg)
    (hans : ∀ w, w.length ≤ steps → (oracle w).length ≤ answerSize) :
    FiniteConfig.SpaceBound inputSize (steps + 1) answerSize
      (machine.answerStep (fun q => oracle q.2) cfg) := by
  unfold answerStep
  split
  · exact h.mono le_rfl (Nat.le_succ _) le_rfl
  · split
    · exact h.step _ _ _
    · exact h.receive _ _ _ (hans _ (h.query _))

private theorem spaceBound_iterate_answerStep_word (oracle : List Bool → List Bool)
    {w : List Bool} {steps answerSize : ℕ}
    (hans : ∀ u, u.length ≤ steps → (oracle u).length ≤ answerSize) :
    ∀ {i : ℕ}, i ≤ steps →
      FiniteConfig.SpaceBound w.length i answerSize
        ((machine.answerStep fun q => oracle q.2)^[i]
          (FiniteConfig.init machine.initial w))
  | 0, _ => (FiniteConfig.spaceBound_init _ _ 0).mono le_rfl le_rfl (Nat.zero_le _)
  | i + 1, hi => by
    rw [Function.iterate_succ_apply']
    exact machine.spaceBound_answerStep_word oracle
      (spaceBound_iterate_answerStep_word oracle hans (Nat.le_of_succ_le hi))
      fun u hu => hans u (hu.trans (Nat.le_of_succ_le hi))

section FiniteControl

variable [Finite Control] [Fintype Operation]

theorem receiveWord_pt : ComputableInPolyTime machine.receiveWord
    (encPair encFiniteConfig encBits) encFiniteConfig := by
  refine ComputableInPolyTime.finite_cases
    (tag := fun p : FiniteConfig k Bool Control Operation × List Bool => machine.pendingQuery p.1)
    (branch := fun q p => match q with
      | some (op, next) => p.1.receive op next p.2
      | none => p.1)
    (machine.pendingQuery_pt.comp (.fst encFiniteConfig encBits)) ?_
  rintro (_ | ⟨op, next⟩)
  · exact .fst _ _
  · exact ComputableInPolyTime.finiteConfig_receive (.fst encFiniteConfig encBits)
      (.snd encFiniteConfig encBits) op next

/-- **Independent time and space of one multi-bit oracle instruction.**
Charges `Tg` and `Sg` only when `(machine.pendingQuery cfg).isSome = true`. -/
theorem answerStep_word_inO {oracle : List Bool → List Bool} {Tg Sg : List Bool → ℕ}
    (horacle : ComputableInO oracle encBits encBits Tg Sg) :
    ∃ d : ℕ, ComputableInO (machine.answerStep fun q => oracle q.2)
      encFiniteConfig encFiniteConfig
      (fun cfg => ((encFiniteConfig cfg).length + 1) ^ d +
        if (machine.pendingQuery cfg).isSome = true then
          Tg (machine.pendingRequest cfg) +
            ((encFiniteConfig cfg).length +
              (oracle (machine.pendingRequest cfg)).length + 1) ^ d
        else 0)
      (fun cfg => ((encFiniteConfig cfg).length + 1) ^ d +
        if (machine.pendingQuery cfg).isSome = true then
          Sg (machine.pendingRequest cfg) +
            ((encFiniteConfig cfg).length +
              (oracle (machine.pendingRequest cfg)).length + 1) ^ d
        else 0) := by
  obtain ⟨d, h⟩ := exists_computableInO_searchStep (done := fun _ => false) (.const false)
    ((ComputableInPolyTime.of_finite (encOut := encBool) Option.isSome).comp
      machine.pendingQuery_pt)
    machine.pendingRequest_pt machine.localStep_pt machine.receiveWord_pt horacle
  exact ⟨d, (h.mono_le (fun _ => by simp only [true_and, encBits_apply]; exact le_rfl)
    (fun _ => by simp only [true_and, encBits_apply]; exact le_rfl)).of_enc_eq fun cfg => by
      simp only [Bool.false_eq_true, ite_false]; rw [machine.answerStep_word]; rfl⟩

theorem computableInPolyTime_answerStep_word {oracle : List Bool → List Bool}
    (horacle : ComputableInPolyTime oracle encBits encBits) :
    ComputableInPolyTime (machine.answerStep fun q => oracle q.2)
      encFiniteConfig encFiniteConfig :=
  (ComputableInPolyTime.ite
    ((ComputableInPolyTime.of_finite (encOut := encBool) Option.isSome).comp
      machine.pendingQuery_pt)
    (machine.receiveWord_pt.comp (.prod .id' (horacle.comp machine.pendingRequest_pt)))
    machine.localStep_pt).of_enc_eq fun cfg => by rw [machine.answerStep_word]; rfl

omit [Fintype Operation] in
/-- **A clocked multi-bit oracle run against a polynomial-time word oracle is polynomial-time.** -/
theorem computableInPolyTime_run_word [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {oracle : List Bool → List Bool} (horacle : ComputableInPolyTime oracle encBits encBits)
    (c d : ℕ) :
    ComputableInPolyTime (fun a => OracleComp.interpret (m := Id) (fun q => oracle q.2)
      (machine.run (pure false) (fun op word => OracleComp.query (op, word))
        (c * ((input a).length + 1) ^ d) (input a))) input encBits := by
  classical
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  obtain ⟨co, do', ho_len⟩ := horacle.polyBounded_length.exists_le
  let clk (a : α) : ℕ := c * ((input a).length + 1) ^ d
  let ansMax (a : α) : ℕ := co * (clk a + 1) ^ do'
  have hcount : ComputableInPolyTime clk input encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length input)).of_enc_eq fun _ => by simp [clk]
  have hspace (a : α) {i : ℕ} (hi : i ≤ clk a) :=
    machine.spaceBound_iterate_answerStep_word oracle (w := input a) (steps := clk a)
      (answerSize := ansMax a) (fun w hw => (ho_len w).trans (Nat.mul_le_mul_left co
        (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) do'))) hi
  have hbound : PolyBounded (fun a => (input a).length)
      (fun a => cf * ((input a).length + clk a + ansMax a + 1)) := by growth_poly
  have hit := ComputableInPolyTime.iterate hcount
    (ComputableInPolyTime.finiteConfig_init (by fun_prop) _)
    (machine.computableInPolyTime_answerStep_word horacle) hbound
    fun a i hi => (hcf _ _ _ _ (hspace a hi)).trans (Nat.mul_le_mul_left cf (by omega))
  exact ((show ComputableInPolyTime (fun cfg : FiniteConfig k Bool Control Operation =>
      cfg.tapes.output) encFiniteConfig encBits by fun_prop).comp hit).of_enc_eq fun a => by
    rw [machine.interpret_run_pure_false]; rfl

omit [Fintype Operation] in
/-- **A clocked multi-bit oracle run against a polynomial-space word oracle runs in polynomial
workspace**, with explicit time `O(poly(|a|) + (clock a + 1) * (poly(|a|) + wordMax Tg (clock a)))`
charging `Tg` only up to the clock and bounding space solely by input, simulated space, and
counters (never by simulated time `Tg`). -/
theorem exists_computableInO_run_word [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {oracle : List Bool → List Bool} {Tg Sg : List Bool → ℕ}
    (horacle : ComputableInO oracle encBits encBits Tg Sg)
    (hSg : PolyBounded List.length Sg) (c d : ℕ) :
    ∃ (c₀ e₀ : ℕ) (S : α → ℕ),
      PolyBounded (fun a => (input a).length) S ∧
      ComputableInO (fun a => OracleComp.interpret (m := Id) (fun q => oracle q.2)
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (c * ((input a).length + 1) ^ d) (input a))) input encBits
        (fun a => c₀ * ((input a).length + 1) ^ e₀ +
          (c * ((input a).length + 1) ^ d + 1) *
            (c₀ * ((input a).length + 1) ^ e₀ + wordMax Tg (c * ((input a).length + 1) ^ d)))
        S := by
  classical
  let _ := Fintype.ofFinite Operation
  let _ : Inhabited (FiniteConfig k Bool Control Operation) :=
    ⟨FiniteConfig.init machine.initial []⟩
  obtain ⟨e, hstep⟩ := machine.answerStep_word_inO horacle
  obtain ⟨cg, dg, hSg_le⟩ := hSg.exists_le
  obtain ⟨kg, ho_len⟩ := horacle.length_le
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  let clk (a : α) : ℕ := c * ((input a).length + 1) ^ d
  let sgMax (a : α) : ℕ := cg * (clk a + 1) ^ dg
  let ansMax (a : α) : ℕ := kg * (sgMax a + 1)
  have hsg_bound (a : α) {w : List Bool} (hw : w.length ≤ clk a) : Sg w ≤ sgMax a :=
    (hSg_le w).trans (Nat.mul_le_mul_left cg (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) dg))
  have hans_le (a : α) {w : List Bool} (hw : w.length ≤ clk a) : (oracle w).length ≤ ansMax a :=
    (ho_len w).trans (Nat.mul_le_mul_left kg (Nat.add_le_add_right (hsg_bound a hw) 1))
  have hn_pt : ComputableInPolyTime clk input encNat :=
    (ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
        (ComputableInPolyTime.encoding_length input))).of_enc_eq fun _ => by simp [clk]
  obtain ⟨dn, _, hn⟩ := hn_pt.exists_degree
  obtain ⟨di, _, hinit⟩ := (show ComputableInPolyTime
    (fun a => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input a))
    input encFiniteConfig from ComputableInPolyTime.finiteConfig_init (by fun_prop) _).exists_degree
  obtain ⟨do', _, hout⟩ := (show ComputableInPolyTime
    (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
    encFiniteConfig encBits by fun_prop).exists_degree
  let step := machine.answerStep fun q => oracle q.2
  have hspace (a : α) {i : ℕ} (hi : i ≤ clk a) :=
    machine.spaceBound_iterate_answerStep_word oracle (w := input a) (steps := clk a)
      (answerSize := ansMax a) (fun _ hw => hans_le a hw) hi
  let B (a : α) : ℕ := cf * ((input a).length + clk a + ansMax a + 1)
  have hlen (a : α) {i : ℕ} (hi : i ≤ clk a) :
      (encFiniteConfig (step^[i] (FiniteConfig.init machine.initial (input a)))).length ≤ B a :=
    (hcf _ _ _ _ (hspace a hi)).trans (Nat.mul_le_mul_left cf (by omega))
  let stepPoly (a : α) : ℕ := (B a + 1) ^ e + (B a + ansMax a + 1) ^ e
  have hstep_bd (F : List Bool → ℕ) (M : α → ℕ)
      (hF : ∀ a w, w.length ≤ clk a → F w ≤ M a) (a : α) (i : ℕ) (hi : i ≤ clk a) :
      ((encFiniteConfig (step^[i] (FiniteConfig.init machine.initial (input a)))).length + 1) ^ e +
        (if (machine.pendingQuery
            (step^[i] (FiniteConfig.init machine.initial (input a)))).isSome = true then
          F (machine.pendingRequest (step^[i] (FiniteConfig.init machine.initial (input a)))) +
            ((encFiniteConfig (step^[i] (FiniteConfig.init machine.initial (input a)))).length +
              (oracle (machine.pendingRequest
                (step^[i] (FiniteConfig.init machine.initial (input a))))).length + 1) ^ e
        else 0) ≤ stepPoly a + M a := by
    have hl := hlen a hi
    have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) e
    split_ifs
    · have hr := (machine.length_pendingRequest_le (hspace a hi)).trans hi
      have hp2 := Nat.pow_le_pow_left
        (Nat.add_le_add_right (Nat.add_le_add hl (hans_le a hr)) 1) e
      have hfm := hF a _ hr
      dsimp only [step, stepPoly] at hl hp1 hp2 hfm ⊢; omega
    · dsimp only [step, stepPoly] at hl hp1 ⊢; omega
  have hwhole := (hout.inO.comp (ComputableInO.iterate hn.inO hinit.inO hstep
    (hstep_bd Tg (fun a => wordMax Tg (clk a)) (fun a _ hw => le_wordMax Tg hw))
    (hstep_bd Sg sgMax (fun a _ hw => hsg_bound a hw))
    (fun a _ hi => hlen a hi))).of_enc_eq
    (g := fun a => OracleComp.interpret (m := Id) (fun q => oracle q.2)
      (machine.run (pure false) (fun op word => OracleComp.query (op, word)) (clk a) (input a)))
    fun a => by rw [machine.interpret_run_pure_false]; rfl
  obtain ⟨c₀, e₀, hc₀⟩ := (show PolyBounded (fun a => (input a).length)
    (fun a => ((input a).length + 1) ^ dn + ((input a).length + 1) ^ di +
      (B a + 1) ^ do' + stepPoly a + sgMax a + B a + (clk a + 1) ^ 2 + clk a) by
    growth_poly).exists_le
  refine ⟨c₀, e₀, fun a => c₀ * ((input a).length + 1) ^ e₀, by growth_poly,
    hwhole.mono_le (fun a => ?_) (fun a => ?_)⟩
  · have hfin := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen a le_rfl) 1) do'
    have hcl2 := Nat.pow_le_pow_left (Nat.add_le_add_right (length_encNat_le_self (clk a)) 1) 2
    have h₁ := hc₀ a
    dsimp only [step, clk] at hfin hcl2 h₁ ⊢
    rw [Nat.add_right_comm]
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  · have hfin := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen a le_rfl) 1) do'
    have hcl := length_encNat_le_self (clk a)
    have h₁ := hc₀ a
    dsimp only [step, clk] at hfin hcl h₁ ⊢
    omega

end FiniteControl

end Turing.MultiTapePTM

/-! ### `OracleCallBound`, `BoundedOracleProgram`, and `BoundedOracleReduction` -/

namespace Cslib.Complexity

open Probability _root_.Turing _root_.Turing.MultiTapeTM

@[expose] section
/-- Explicit quantitative profile of an oracle call budget on a single input:
`qcount` queries, each of bit-length at most `qlen`, with total bit-length at most `totalQlen`,
and each answer of bit-length at most `alen`. -/
@[ext]
structure OracleCallBound where
  /-- Maximum number of oracle queries issued along the run. -/
  qcount : ℕ
  /-- Maximum bit-length of any single query word issued along the run. -/
  qlen : ℕ
  /-- Maximum sum of bit-lengths of all query words issued along the run. -/
  totalQlen : ℕ
  /-- Maximum bit-length of any oracle answer read along the run. -/
  alen : ℕ
  deriving DecidableEq, Repr
end

/-- Framed binary encoding of `OracleCallBound`. -/
enc_structure encOracleCallBound : OracleCallBound where
  qcount : encNat, qlen : encNat, totalQlen : encNat, alen : encNat

namespace OracleCallBound

/-- Zero-query profile `(0, 0, 0, 0)`. -/
@[expose] def zero : OracleCallBound := ⟨0, 0, 0, 0⟩

/-- Single-query profile `(1, ql, ql, al)` for a query of length `≤ ql` and reply of length `≤ al`.
-/
@[expose] def single (ql al : ℕ) : OracleCallBound := ⟨1, ql, ql, al⟩

/-- Coordinatewise dominance between `OracleCallBound` profiles. -/
@[expose] def Le (b₁ b₂ : OracleCallBound) : Prop :=
  b₁.qcount ≤ b₂.qcount ∧ b₁.qlen ≤ b₂.qlen ∧ b₁.totalQlen ≤ b₂.totalQlen ∧ b₁.alen ≤ b₂.alen

/-- `prog` **respects** `b` against the word oracle `oracle : List Bool → List Bool`: along the
deterministic run `queriesWith (fun q => oracle q.2) prog`, query count is `≤ b.qcount`, each query
has length `≤ b.qlen`, total query length is `≤ b.totalQlen`, and each reply has length `≤ b.alen`.
-/
@[expose]
def Respects {β : Type} (oracle : List Bool → List Bool) (prog : WordQueryComp Unit β)
    (b : OracleCallBound) : Prop :=
  let qs := OracleComp.queriesWith (fun q => oracle q.2) prog
  qs.length ≤ b.qcount ∧
  (∀ q ∈ qs, q.2.length ≤ b.qlen) ∧
  (qs.map fun q => q.2.length).sum ≤ b.totalQlen ∧
  (∀ q ∈ qs, (oracle q.2).length ≤ b.alen)

theorem Respects.mono {β : Type} {oracle : List Bool → List Bool} {prog : WordQueryComp Unit β}
    {b₁ b₂ : OracleCallBound} (h : Respects oracle prog b₁) (hle : b₁.Le b₂) :
    Respects oracle prog b₂ := by
  rcases h with ⟨hqc, hql, htql, hal⟩
  rcases hle with ⟨hlqc, hlql, hltql, hlal⟩
  exact ⟨hqc.trans hlqc, fun q hq => (hql q hq).trans hlql,
    htql.trans hltql, fun q hq => (hal q hq).trans hlal⟩

theorem respects_pure {β : Type} (oracle : List Bool → List Bool) (x : β) (b : OracleCallBound) :
    Respects oracle (pure x) b := by
  simp [Respects]

theorem respects_map {β γ : Type} (oracle : List Bool → List Bool) (f : β → γ)
    (prog : WordQueryComp Unit β) (b : OracleCallBound) :
    Respects oracle (f <$> prog) b ↔ Respects oracle prog b := by
  simp [Respects, OracleComp.queriesWith_map]

/-- Composed call bound when an outer run with bound `b₁` answers each query `w` (`|w| ≤ b₁.qlen`)
using an inner oracle program with profile `b₂ w`. -/
@[expose]
noncomputable def comp (b₁ : OracleCallBound) (b₂ : List Bool → OracleCallBound) :
    OracleCallBound where
  qcount := b₁.qcount * wordMax (fun w => (b₂ w).qcount) b₁.qlen
  qlen := wordMax (fun w => (b₂ w).qlen) b₁.qlen
  totalQlen := b₁.qcount * wordMax (fun w => (b₂ w).totalQlen) b₁.qlen
  alen := wordMax (fun w => (b₂ w).alen) b₁.qlen

end OracleCallBound

/-- Auxiliary structural lemma for substituting a deterministic word-query handler `G` into an
outer `WordQueryComp` program `prog`. -/
private theorem interpret_and_queriesWith_subst {β : Type}
    (oracle₁ oracle₂ : List Bool → List Bool)
    (G : Unit × List Bool → WordQueryComp Unit (List Bool))
    (prog : WordQueryComp Unit β)
    (hG : ∀ q ∈ OracleComp.queriesWith (fun q => oracle₁ q.2) prog,
      OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2) :
    OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (OracleComp.interpret G prog) =
      OracleComp.interpret (m := Id) (fun q => oracle₁ q.2) prog ∧
    OracleComp.queriesWith (fun q' => oracle₂ q'.2) (OracleComp.interpret G prog) =
      (OracleComp.queriesWith (fun q => oracle₁ q.2) prog).flatMap fun q =>
        OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q) := by
  induction prog using PFunctor.FreeM.induction with
  | pure x => exact ⟨rfl, rfl⟩
  | lift_bind q cont ih =>
    change OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (OracleComp.query q >>= cont)) =
      OracleComp.interpret (m := Id) (fun q => oracle₁ q.2) (OracleComp.query q >>= cont) ∧
      OracleComp.queriesWith (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (OracleComp.query q >>= cont)) =
      (OracleComp.queriesWith (fun q => oracle₁ q.2) (OracleComp.query q >>= cont)).flatMap _
    rw [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_bind,
      OracleComp.queriesWith_bind, OracleComp.queriesWith_query_bind, List.flatMap_cons]
    have hq : OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2 :=
      hG q (List.mem_cons_self ..)
    rw [hq]
    obtain ⟨heval, hqs⟩ := ih (oracle₁ q.2) fun q' hq' => hG q' (List.mem_cons_of_mem _ hq')
    exact ⟨heval, congrArg (_ ++ ·) hqs⟩

private theorem forall_queriesWith_of_probQueriesSatisfy {β : Type}
    {p : Unit × List Bool → Prop} (answer : Unit × List Bool → List Bool)
    (prog : WordQueryComp Unit β)
    (h : (OracleComp.interpret ProbOracleComp.query prog).QueriesSatisfy p) :
    ∀ q ∈ OracleComp.queriesWith answer prog, p q := by
  induction prog using PFunctor.FreeM.induction with
  | pure _ => simp
  | lift_bind q cont ih =>
    change (OracleComp.interpret ProbOracleComp.query
      (OracleComp.query q >>= cont)).QueriesSatisfy p at h
    rw [OracleComp.interpret_bind, OracleComp.interpret_query, ProbOracleComp.query] at h
    obtain ⟨hpq, hcont⟩ := OracleComp.QueriesSatisfy.liftBind_iff.mp h
    intro q' hq'
    change q' ∈ OracleComp.queriesWith answer (OracleComp.query q >>= cont) at hq'
    rw [OracleComp.queriesWith_query_bind, List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · exact hpq
    · exact ih (answer q) (hcont (answer q)) q' hq'

/-- **Deterministic adaptive oracle program with explicit query and answer length bounds.**
Packages a `WordQueryComp` program computing `f : α → β` relative to `oracle : List Bool → List
Bool`, certified by `IsOraclePPTOn`, together with an explicit `OracleCallBound` profile `bound a`
and a polynomial-time unary reply-length allowance `alenCap a` (`(bound a).alen ≤ alenCap a`) used
when composing open oracle handlers. -/
structure BoundedOracleProgram {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (oracle : List Bool → List Bool) (f : α → β) where
  /-- Deterministic adaptive word-query program. -/
  program : α → WordQueryComp Unit β
  /-- Explicit `(qcount, qlen, totalQlen, alen)` profile on each input. -/
  bound : α → OracleCallBound
  /-- Polynomial-time unary upper allowance on reply lengths along the run. -/
  alenCap : α → ℕ
  /-- Strict oracle-PPT machine realization across all stateful handlers. -/
  isOraclePPTOn :
    IsOraclePPTOn encA encB (fun a => OracleComp.interpret ProbOracleComp.query (program a))
  /-- Polynomial-time certificate for `alenCap` in unary. -/
  computableInPolyTime_alenCap : ComputableInPolyTime alenCap encA encUnary
  /-- Functional correctness against `oracle`. -/
  eval_eq : ∀ a, OracleComp.interpret (m := Id) (fun q => oracle q.2) (program a) = f a
  /-- Every run respects `bound a`. -/
  respects_bound : ∀ a, OracleCallBound.Respects oracle (program a) (bound a)
  /-- `alenCap a` dominates `(bound a).alen`. -/
  alen_le_alenCap : ∀ a, (bound a).alen ≤ alenCap a

namespace BoundedOracleProgram

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- Number of queries budgeted on `a`. -/
@[expose] def qcount {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).qcount

/-- Per-query length budgeted on `a`. -/
@[expose] def qlen {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).qlen

/-- Total query length budgeted on `a`. -/
@[expose] def totalQlen {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).totalQlen

/-- Per-answer length budgeted on `a`. -/
@[expose] def alen {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).alen

/-- Weaken the `OracleCallBound` profile of `R` to any coordinatewise larger `bound'`. -/
@[expose]
def mono {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f)
    {bound' : α → OracleCallBound} {alenCap' : α → ℕ}
    (hbound : ∀ a, (R.bound a).Le (bound' a))
    (hcap_pt : ComputableInPolyTime alenCap' encA encUnary)
    (hcap_le : ∀ a, (bound' a).alen ≤ alenCap' a) :
    BoundedOracleProgram encA encB oracle f where
  program := R.program
  bound := bound'
  alenCap := alenCap'
  isOraclePPTOn := R.isOraclePPTOn
  computableInPolyTime_alenCap := hcap_pt
  eval_eq := R.eval_eq
  respects_bound a := (R.respects_bound a).mono (hbound a)
  alen_le_alenCap := hcap_le

/-- A plain polynomial-time function `f : α → β` lifts to a `0`-query `BoundedOracleProgram` with
`OracleCallBound.zero` relative to every word oracle. -/
@[expose]
def ofPolyTime {f : α → β} (hf : ComputableInPolyTime f encA encB)
    (oracle : List Bool → List Bool) :
    BoundedOracleProgram encA encB oracle f where
  program a := pure (f a)
  bound _ := OracleCallBound.zero
  alenCap _ := 0
  isOraclePPTOn := hf.isOraclePPTOn
  computableInPolyTime_alenCap := .const 0
  eval_eq _ := rfl
  respects_bound _ := OracleCallBound.respects_pure oracle _ _
  alen_le_alenCap _ := le_rfl

/-- Polynomial-time postprocessing `g : β → γ` preserves `bound` and `alenCap`. -/
@[expose]
def map {oracle : List Bool → List Bool} {f : α → β} {g : β → γ}
    (R : BoundedOracleProgram encA encB oracle f)
    (hg : ComputableInPolyTime g encB encC) :
    BoundedOracleProgram encA encC oracle (g ∘ f) where
  program a := g <$> R.program a
  bound := R.bound
  alenCap := R.alenCap
  isOraclePPTOn := by
    simpa only [OracleComp.interpret_map] using R.isOraclePPTOn.map hg
  computableInPolyTime_alenCap := R.computableInPolyTime_alenCap
  eval_eq a := by
    rw [OracleComp.interpret_map, R.eval_eq a]
    rfl
  respects_bound a := (OracleCallBound.respects_map oracle g (R.program a) (R.bound a)).mpr
    (R.respects_bound a)
  alen_le_alenCap := R.alen_le_alenCap

/-- Polynomial-time preprocessing `p : γ → α` pulls back `bound` and `alenCap` along `p`. -/
@[expose]
def preprocess {oracle : List Bool → List Bool} {f : α → β} {p : γ → α}
    (R : BoundedOracleProgram encA encB oracle f)
    (hp : ComputableInPolyTime p encC encA) :
    BoundedOracleProgram encC encB oracle (f ∘ p) where
  program c := R.program (p c)
  bound c := R.bound (p c)
  alenCap c := R.alenCap (p c)
  isOraclePPTOn := R.isOraclePPTOn.preprocess hp
  computableInPolyTime_alenCap := R.computableInPolyTime_alenCap.comp hp
  eval_eq c := R.eval_eq (p c)
  respects_bound c := R.respects_bound (p c)
  alen_le_alenCap c := R.alen_le_alenCap (p c)

/-- **Single-query oracle call** with explicit request generator `req : α → List Bool`, unary
answer-length cap `alenCap : α → ℕ`, and polynomial-time reply decoder `decode : α × List Bool →
β`. Issues `1` query of length `(req a).length` and reads at most `alenCap a` reply bits. -/
@[expose]
def ofSingleQuery {oracle : List Bool → List Bool} {req : α → List Bool} {alenCap : α → ℕ}
    {decode : α × List Bool → β}
    (hreq : ComputableInPolyTime req encA encBits)
    (halen : ComputableInPolyTime alenCap encA encUnary)
    (hdec : ComputableInPolyTime decode (encPair encA encBits) encB)
    (hle : ∀ a, (oracle (req a)).length ≤ alenCap a) :
    BoundedOracleProgram encA encB oracle (fun a => decode (a, oracle (req a))) where
  program a := (fun reply => decode (a, reply)) <$>
    (List.take (alenCap a) <$> OracleComp.query ((), req a))
  bound a := OracleCallBound.single (req a).length (oracle (req a)).length
  alenCap := alenCap
  isOraclePPTOn := by
    have hq := IsOraclePPTOn.query_take () hreq halen
    simpa only [OracleComp.interpret_map, OracleComp.interpret_query, Functor.map_map] using
      hq.map_with (f := fun a reply => decode (a, reply)) hdec
  computableInPolyTime_alenCap := halen
  eval_eq a := by
    simp only [OracleComp.interpret_map, Functor.map_map]
    change decode (a, (oracle (req a)).take (alenCap a)) = decode (a, oracle (req a))
    rw [List.take_of_length_le (hle a)]
  respects_bound a := by
    simp [OracleCallBound.Respects, OracleCallBound.single, OracleComp.queriesWith_map]
  alen_le_alenCap a := hle a

/-- **Identity word-oracle program** on `List Bool` given a polynomial-time unary bound `alenCap`
on `(oracle w).length`: makes `1` query `w` of length `w.length` and returns `oracle w`. -/
@[expose]
def id {oracle : List Bool → List Bool} {alenCap : List Bool → ℕ}
    (halen : ComputableInPolyTime alenCap encBits encUnary)
    (hle : ∀ w, (oracle w).length ≤ alenCap w) :
    BoundedOracleProgram encBits encBits oracle oracle :=
  ofSingleQuery (req := _root_.id) (alenCap := alenCap) (decode := Prod.snd)
    .id' halen (.snd encBits encBits) hle

private theorem list_sum_affine_le {ι : Type} (f g : ι → ℕ) (scale offset : ℕ) :
    ∀ (l : List ι), (∀ x ∈ l, f x ≤ scale * g x + offset) →
      (l.map f).sum ≤ scale * (l.map g).sum + offset * l.length
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have hxs := list_sum_affine_le f g scale offset xs fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

private theorem map_sum_le_mul {ι : Type} {f : ι → ℕ} {l : List ι} {m k : ℕ}
    (hmem : ∀ x ∈ l, f x ≤ m) (hlen : l.length ≤ k) : (l.map f).sum ≤ k * m := by
  refine le_trans ?_ (Nat.mul_le_mul_right m hlen)
  simpa only [List.length_map, smul_eq_mul] using
    List.sum_le_length_nsmul (l.map f) m (List.forall_mem_map.mpr hmem)

/-- Shared handler substitution identity for `BoundedOracleProgram.comp` and
`totalQueryLength_comp_affine`. -/
private theorem comp_interpret_and_queriesWith {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    let G (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
      List.take (R₁.alenCap a) <$> R₂.program q.2
    OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (R₁.program a)) = f a ∧
      OracleComp.queriesWith (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (R₁.program a)) =
      (OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)).flatMap fun q =>
        OracleComp.queriesWith (fun q' => oracle₂ q'.2) (R₂.program q.2) := by
  let G (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
    List.take (R₁.alenCap a) <$> R₂.program q.2
  have hG : ∀ q ∈ OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a),
      OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2 := fun q hq => by
    rw [show OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) =
        (OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (R₂.program q.2)).take
          (R₁.alenCap a) from OracleComp.interpret_map .., R₂.eval_eq q.2]
    exact List.take_of_length_le ((R₁.respects_bound a).2.2.2 q hq |>.trans (R₁.alen_le_alenCap a))
  obtain ⟨heval, hqs⟩ := interpret_and_queriesWith_subst oracle₁ oracle₂ G (R₁.program a) hG
  refine ⟨heval.trans (R₁.eval_eq a), ?_⟩
  simpa only [G, OracleComp.queriesWith_map] using hqs

/-- Polynomial reply-length allowance for `BoundedOracleProgram.comp`. -/
noncomputable def compCapPoly {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) : Polynomial ℕ :=
  let hqb := IsOraclePPTOn.query_bounds R₁.isOraclePPTOn
  let c₁ := Classical.choose hqb
  let d₁ := Classical.choose (Classical.choose_spec hqb)
  let hcap₂ : PolyBounded List.length R₂.alenCap := by growth_poly [R₂.computableInPolyTime_alenCap]
  let hex₂ := hcap₂.exists_le
  let c₂ := Classical.choose hex₂
  let d₂ := Classical.choose (Classical.choose_spec hex₂)
  Polynomial.C c₂ * (Polynomial.C c₁ * (Polynomial.X + 1) ^ d₁ + 1) ^ d₂

private theorem comp_isOraclePPTOn {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) :
    IsOraclePPTOn encA encB fun a => OracleComp.interpret ProbOracleComp.query
      (OracleComp.interpret
        (fun q : Unit × List Bool => List.take (R₁.alenCap a) <$> R₂.program q.2)
        (R₁.program a)) := by
  let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
  have htake_pt : ComputableInPolyTime
      (fun ⟨⟨a, _, _⟩, reply⟩ => reply.take (R₁.alenCap a)) (encPair EIn encBits) encBits :=
    ComputableInPolyTime.bitsTakeWithInput (.snd EIn encBits)
      (R₁.computableInPolyTime_alenCap.comp (by dsimp only [EIn]; fun_prop))
  have hhandler : IsOraclePPTOn EIn encBits fun p : α × (Unit × List Bool) =>
      OracleComp.interpret ProbOracleComp.query
        (List.take (R₁.alenCap p.1) <$> R₂.program p.2.2) := by
    simpa only [OracleComp.interpret_map] using
      (R₂.isOraclePPTOn.preprocess (input := EIn) (prepare := fun ⟨_, _, w⟩ => w)
        (by dsimp only [EIn]; fun_prop)).map_with
        (f := fun ⟨a, _⟩ reply => reply.take (R₁.alenCap a)) htake_pt
  have hsub := R₁.isOraclePPTOn.interpret_preprocess_open'
    (operationEncoding := encFinEnum Unit)
    (handler := fun a q => OracleComp.interpret ProbOracleComp.query
      (List.take (R₁.alenCap a) <$> R₂.program q.2))
    (prepare := _root_.id) (resources := fun a _ => R₁.alenCap a)
    .id' hhandler (R₁.computableInPolyTime_alenCap.comp (.fst encA encBits))
    fun a q reply hreply => by
      rw [OracleComp.interpret_map] at hreply
      obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le _ _
  convert hsub using 1
  funext a; rw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
  congr 1; funext q; simp only [ProbOracleComp.interpret_query]

private theorem comp_respects_bound {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    OracleCallBound.Respects oracle₂
      (OracleComp.interpret
        (fun q : Unit × List Bool => List.take (R₁.alenCap a) <$> R₂.program q.2)
        (R₁.program a))
      { (R₁.bound a).comp R₂.bound with
        alen := min ((R₁.bound a).comp R₂.bound).alen
          ((compCapPoly R₁ R₂).eval (encA a).length) } := by
  rcases R₁.respects_bound a with ⟨hqc₁, hql₁, _, _⟩
  dsimp only [OracleCallBound.Respects, OracleCallBound.comp]
  rw [(comp_interpret_and_queriesWith R₁ R₂ a).2]
  set qs₁ := OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_flatMap]
    exact map_sum_le_mul (fun q hq =>
      (R₂.respects_bound q.2).1.trans (le_wordMax (fun w => (R₂.bound w).qcount) (hql₁ q hq))) hqc₁
  · intro q' hq'
    obtain ⟨q, hq, hq'_mem⟩ := List.mem_flatMap.mp hq'
    exact ((R₂.respects_bound q.2).2.1 q' hq'_mem).trans
      (le_wordMax (fun w => (R₂.bound w).qlen) (hql₁ q hq))
  · rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
    exact map_sum_le_mul (fun q hq =>
      (R₂.respects_bound q.2).2.2.1.trans
        (le_wordMax (fun w => (R₂.bound w).totalQlen) (hql₁ q hq))) hqc₁
  · intro q' hq'
    obtain ⟨q, hq, hq'_mem⟩ := List.mem_flatMap.mp hq'
    have hal₂ := (R₂.respects_bound q.2).2.2.2 q' hq'_mem
    refine le_min (hal₂.trans (le_wordMax (fun w => (R₂.bound w).alen) (hql₁ q hq))) ?_
    let hqb := IsOraclePPTOn.query_bounds R₁.isOraclePPTOn
    have hq_clk : q.2.length ≤ Classical.choose hqb *
        ((encA a).length + 1) ^ Classical.choose (Classical.choose_spec hqb) :=
      forall_queriesWith_of_probQueriesSatisfy (fun q => oracle₁ q.2) (R₁.program a)
        (Classical.choose_spec (Classical.choose_spec hqb) a).2 q hq
    have hcap₂_poly : PolyBounded List.length R₂.alenCap := by
      growth_poly [R₂.computableInPolyTime_alenCap]
    let hex₂ := hcap₂_poly.exists_le
    have hcap₂_le := Classical.choose_spec (Classical.choose_spec hex₂) q.2
    simp only [compCapPoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    exact (hal₂.trans (R₂.alen_le_alenCap q.2)).trans (hcap₂_le.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hq_clk 1) _)))

/-- **Composition of `BoundedOracleProgram`s with explicit query and answer length accounting.**
Substitutes `R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁` for each query of
`R₁ : BoundedOracleProgram encA encB oracle₁ f`, truncating replies to `R₁.alenCap a` so open
machine realization (`IsOraclePPTOn.interpret_preprocess_open'`) holds against every stateful
external oracle while `OracleCallBound.comp` records the composed `(qcount, qlen, totalQlen, alen)`
budget (with `alen` additionally capped by the polynomial machine reply bound). -/
@[expose]
noncomputable def comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) :
    BoundedOracleProgram encA encB oracle₂ f where
  program a := OracleComp.interpret
    (fun q : Unit × List Bool => List.take (R₁.alenCap a) <$> R₂.program q.2) (R₁.program a)
  bound a :=
    let bc := (R₁.bound a).comp R₂.bound
    { bc with alen := min bc.alen ((compCapPoly R₁ R₂).eval (encA a).length) }
  alenCap a := (compCapPoly R₁ R₂).eval (encA a).length
  isOraclePPTOn := by exact comp_isOraclePPTOn R₁ R₂
  computableInPolyTime_alenCap := by
    exact ((ComputableInPolyTime.unary_eval (compCapPoly R₁ R₂)).comp
      (ComputableInPolyTime.encoding_length encA)).of_enc_eq fun _ => rfl
  eval_eq a := by exact (comp_interpret_and_queriesWith R₁ R₂ a).1
  respects_bound a := by exact comp_respects_bound R₁ R₂ a
  alen_le_alenCap _ := Nat.min_le_right _ _

@[simp]
theorem qcount_comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).qcount a = R₁.qcount a * wordMax R₂.qcount (R₁.qlen a) := rfl

@[simp]
theorem qlen_comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).qlen a = wordMax R₂.qlen (R₁.qlen a) := rfl

@[simp]
theorem totalQlen_comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).totalQlen a = R₁.qcount a * wordMax R₂.totalQlen (R₁.qlen a) := rfl

theorem alen_comp_le {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).alen a ≤ wordMax R₂.alen (R₁.qlen a) :=
  Nat.min_le_left _ _

/-- **Sharper affine `totalQlen` bound under composition:** when `R₂.totalQlen w ≤ scale * |w| +
offset`, the actual sum of inner query lengths along `(R₁.comp R₂).program a` is bounded by
`scale * R₁.totalQlen a + offset * R₁.qcount a`, preserving total-query-length sparsity rather than
multiplying `qcount * qlen`. -/
theorem totalQueryLength_comp_affine {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁)
    {scale offset : ℕ} (haff : ∀ w, R₂.totalQlen w ≤ scale * w.length + offset) (a : α) :
    ((OracleComp.queriesWith (fun q' => oracle₂ q'.2) ((R₁.comp R₂).program a)).map
        fun q' => q'.2.length).sum ≤
      scale * R₁.totalQlen a + offset * R₁.qcount a := by
  rcases R₁.respects_bound a with ⟨hqc₁, _, htql₁, _⟩
  dsimp only [comp]
  rw [(comp_interpret_and_queriesWith R₁ R₂ a).2, List.map_flatMap, List.flatMap_def,
    List.sum_flatten, List.map_map]
  set qs₁ := OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)
  have hstep := list_sum_affine_le
    (fun q : Unit × List Bool =>
      ((OracleComp.queriesWith (fun q' => oracle₂ q'.2) (R₂.program q.2)).map
        fun q' => q'.2.length).sum)
    (fun q => q.2.length) scale offset qs₁ fun q _ =>
      (R₂.respects_bound q.2).2.2.1.trans (haff q.2)
  exact hstep.trans
    (Nat.add_le_add (Nat.mul_le_mul_left scale htql₁) (Nat.mul_le_mul_left offset hqc₁))

/-- Composed `BoundedOracleProgram` refining `comp` with the sharper linear `totalQlen` budget
`scale * R₁.totalQlen a + offset * R₁.qcount a` when `R₂.totalQlen` is affine in query length. -/
@[expose]
noncomputable def compAffine {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁)
    {scale offset : ℕ} (haff : ∀ w, R₂.totalQlen w ≤ scale * w.length + offset) :
    BoundedOracleProgram encA encB oracle₂ f := by
  let C := R₁.comp R₂
  exact
    { program := C.program
      bound := fun a =>
        { C.bound a with totalQlen := scale * R₁.totalQlen a + offset * R₁.qcount a }
      alenCap := C.alenCap
      isOraclePPTOn := C.isOraclePPTOn
      computableInPolyTime_alenCap := C.computableInPolyTime_alenCap
      eval_eq := C.eval_eq
      respects_bound := fun a => by
        rcases C.respects_bound a with ⟨hqc, hql, _, hal⟩
        exact ⟨hqc, hql, totalQueryLength_comp_affine R₁ R₂ haff a, hal⟩
      alen_le_alenCap := C.alen_le_alenCap }

/-- **Polynomial-time transfer for multi-bit word oracles:** if `oracle : List Bool → List Bool` is
computable in polynomial time, any `BoundedOracleProgram` relative to `oracle` is computable in
polynomial time. -/
theorem computableInPolyTime {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f)
    (horacle : ComputableInPolyTime oracle encBits encBits) :
    ComputableInPolyTime f encA encB := by
  obtain ⟨_, _, machine, c, d, hrun⟩ := R.isOraclePPTOn.exists_fin_run_pure_false
  refine (machine.computableInPolyTime_run_word (input := encA) horacle c d).of_enc_eq fun a => ?_
  rw [← R.eval_eq a, ← hrun a (fun q => oracle q.2)]
  rfl

/-- **Explicit `ComputableInO` transfer in polynomial workspace for multi-bit word oracles:**
simulating `R` against `ComputableInO oracle encBits encBits Tg Sg` uses **polynomial workspace**
(depending only on input length, machine clock, answer-length growth, and `Sg` — never on `Tg`)
and charges `Tg` at most once per step up to the polynomial clock. -/
theorem exists_computableInO_polySpace {oracle : List Bool → List Bool} {f : α → β}
    {Tg Sg : List Bool → ℕ}
    (R : BoundedOracleProgram encA encB oracle f)
    (horacle : ComputableInO oracle encBits encBits Tg Sg)
    (hSg : PolyBounded List.length Sg) :
    ∃ (c₀ e₀ : ℕ) (S : α → ℕ), PolyBounded (fun a => (encA a).length) S ∧
      ∃ c₁ d₁ : ℕ,
        ComputableInO f encA encB
          (fun a => c₀ * ((encA a).length + 1) ^ e₀ +
            (c₁ * ((encA a).length + 1) ^ d₁ + 1) *
              (c₀ * ((encA a).length + 1) ^ e₀ +
                wordMax Tg (c₁ * ((encA a).length + 1) ^ d₁)))
          S := by
  obtain ⟨_, _, machine, c₁, d₁, hrun⟩ := R.isOraclePPTOn.exists_fin_run_pure_false
  obtain ⟨c₀, e₀, S, hSPoly, hcomp⟩ :=
    machine.exists_computableInO_run_word (input := encA) horacle hSg c₁ d₁
  refine ⟨c₀, e₀, S, hSPoly, c₁, d₁, hcomp.of_enc_eq fun a => ?_⟩
  rw [← R.eval_eq a, ← hrun a (fun q => oracle q.2)]
  rfl

/-- **Polynomial-space transfer for multi-bit word oracles:** if `oracle : List Bool → List Bool` is
computable in polynomial space, any `BoundedOracleProgram` relative to `oracle` is computable in
polynomial space. -/
theorem computableInPolySpace {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f)
    (horacle : ComputableInPolySpace oracle encBits encBits) :
    ComputableInPolySpace f encA encB := by
  obtain ⟨t, s, hs, hc, hl⟩ := horacle
  have hO : ComputableInO oracle encBits encBits t (fun w => s w.length) :=
    ⟨1, hc.mono (fun a => by simp only [one_mul]; omega)
      (fun a => by simp only [one_mul, encBits_apply]; omega),
      fun a => (hl a).trans (by simp only [one_mul, encBits_apply]; omega)⟩
  obtain ⟨_, _, S, hSPoly, _, _, c, htm, hout⟩ :=
    R.exists_computableInO_polySpace hO (.of_polynomiallyBounded List.length hs)
  exact ComputableInPolySpace.of_inSpace hSPoly ⟨_, c, htm, hout⟩

end BoundedOracleProgram

/-! ### `BoundedOracleReduction`: language oracle reductions with explicit call profiles -/

/-- Word-oracle adapter for a typed decision problem `(B, encB)`: maps `w : List Bool` to
`[decide (w ∈ encB '' B)]`, matching `languageOracle (encB '' B) ((), w)`. -/
@[expose]
noncomputable def encodedDecisionOracle {β : Type} (encB : β ↪ List Bool) (B : Set β)
    (w : List Bool) : List Bool :=
  languageOracle (encB '' B) ((), w)

@[simp]
theorem length_encodedDecisionOracle {β : Type} (encB : β ↪ List Bool) (B : Set β)
    (w : List Bool) : (encodedDecisionOracle encB B w).length = 1 := by
  simp [encodedDecisionOracle, languageOracle]

/-- **Deterministic adaptive oracle reduction between decision problems `(A, encA)` and `(B, encB)`
with explicit `(qcount, qlen, totalQlen, alen)` call accounting.** -/
structure BoundedOracleReduction {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) where
  /-- Deterministic adaptive word-query decider program. -/
  program : α → WordQueryComp Unit Bool
  /-- Explicit `(qcount, qlen, totalQlen, alen)` call profile on each input. -/
  bound : α → OracleCallBound
  /-- Strict oracle-PPT machine realization across all stateful handlers. -/
  isOraclePPTOn :
    IsOraclePPTOn encA encBool (fun a => OracleComp.interpret ProbOracleComp.query (program a))
  /-- Decision correctness relative to `encB '' B`. -/
  decides : ∀ a,
    a ∈ A ↔ OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (program a) = true
  /-- Every run against `encB '' B` respects `bound a`. -/
  respects_bound : ∀ a,
    OracleCallBound.Respects (encodedDecisionOracle encB B) (program a) (bound a)

namespace BoundedOracleReduction

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- Number of oracle queries budgeted on `a`. -/
@[expose] def qcount {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).qcount

/-- Per-query length budgeted on `a`. -/
@[expose] def qlen {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).qlen

/-- Total query length budgeted on `a`. -/
@[expose] def totalQlen {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).totalQlen

/-- Per-answer length budgeted on `a`. -/
@[expose] def alen {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).alen

/-- Weaken the call bound of a `BoundedOracleReduction` to any coordinatewise larger profile. -/
@[expose]
def mono {A : Set α} {B : Set β} (R : BoundedOracleReduction encA encB A B)
    {bound' : α → OracleCallBound} (h : ∀ a, (R.bound a).Le (bound' a)) :
    BoundedOracleReduction encA encB A B where
  program := R.program
  bound := bound'
  isOraclePPTOn := R.isOraclePPTOn
  decides := R.decides
  respects_bound a := (R.respects_bound a).mono (h a)

/-- Build a `BoundedOracleReduction` from a `BoundedOracleProgram` computing a decider `f` for `A`
against `encodedDecisionOracle encB B`. -/
@[expose]
def ofProgram {A : Set α} {B : Set β} {f : α → Bool}
    (P : BoundedOracleProgram encA encBool (encodedDecisionOracle encB B) f)
    (hf : ∀ a, a ∈ A ↔ f a = true) :
    BoundedOracleReduction encA encB A B where
  program := P.program
  bound := P.bound
  isOraclePPTOn := P.isOraclePPTOn
  decides a := by
    rw [hf a]
    have heq : (fun q : Unit × List Bool => encodedDecisionOracle encB B q.2) =
        languageOracle (encB '' B) := rfl
    rw [← P.eval_eq a, heq]
  respects_bound := P.respects_bound

open Classical in
/-- View a `BoundedOracleReduction` as a `BoundedOracleProgram` computing `fun a => decide (a ∈ A)`
with unary answer-length cap `1`. -/
@[expose]
noncomputable def toProgram {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) :
    BoundedOracleProgram encA encBool (encodedDecisionOracle encB B)
      (fun a => decide (a ∈ A)) where
  program := R.program
  bound a := { R.bound a with alen := min (R.bound a).alen 1 }
  alenCap _ := 1
  isOraclePPTOn := R.isOraclePPTOn
  computableInPolyTime_alenCap := .const 1
  eval_eq a := by
    have heq : (fun q : Unit × List Bool => encodedDecisionOracle encB B q.2) =
        languageOracle (encB '' B) := rfl
    rw [heq]
    exact Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((R.decides a).mpr h),
      fun h => (R.decides a).mp (of_decide_eq_true h)⟩
  respects_bound a := by
    rcases R.respects_bound a with ⟨hqc, hql, htql, hal⟩
    refine ⟨hqc, hql, htql, fun q hq => le_min (hal q hq) ?_⟩
    simp only [length_encodedDecisionOracle, le_refl]
  alen_le_alenCap _ := Nat.min_le_right _ _

/-- A problem in `P` has a `0`-query `BoundedOracleReduction` to every problem `B`. -/
@[expose]
noncomputable def ofPolyTime {A : Set α} (B : Set β) {f : α → Bool}
    (hf : ComputableInPolyTime f encA encBool) (hA : ∀ a, a ∈ A ↔ f a = true) :
    BoundedOracleReduction encA encB A B :=
  ofProgram (BoundedOracleProgram.ofPolyTime hf (encodedDecisionOracle encB B)) hA

/-- **Single-query lift from `SizeSensitiveReduction`:** a many-one `SizeSensitiveReduction` lifts
to a `1`-query `BoundedOracleReduction` with `qlen = totalQlen = |encB (R.toFun a)|` and `alen = 1`.
-/
@[expose]
noncomputable def ofSizeSensitive {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    (R : SizeSensitiveReduction encA encB μA μB)
    (hAB : ∀ a, a ∈ A ↔ R.toFun a ∈ B) :
    BoundedOracleReduction encA encB A B := by
  let req (a : α) : List Bool := encB (R.toFun a)
  have hreq : ComputableInPolyTime req encA encBits :=
    R.computableInPolyTime_toFun.of_enc_eq fun _ => rfl
  have hdec : ComputableInPolyTime
      (fun p : α × List Bool => p.2.headD false) (encPair encA encBits) encBool :=
    Decoder.bool.computableInPolyTime.comp (ComputableInPolyTime.snd encA encBits)
  let P := BoundedOracleProgram.ofSingleQuery (oracle := encodedDecisionOracle encB B)
    (req := req) (alenCap := fun _ => 1) (decode := fun p => p.2.headD false)
    hreq (.const 1) hdec (fun a => by simp only [length_encodedDecisionOracle, le_refl])
  refine ofProgram P fun a => ?_
  dsimp only [req, encodedDecisionOracle, languageOracle]
  simp only [List.headD_cons, decide_eq_true_eq, encB.injective.mem_set_image]
  exact hAB a

/-- **Identity / reflexivity (`refl`)** of `BoundedOracleReduction`: `1` query of length `|encA a|`
and `1`-bit reply. -/
@[expose]
noncomputable def refl (encA : α ↪ List Bool) (A : Set α) :
    BoundedOracleReduction encA encA A A :=
  ofSizeSensitive (SizeSensitiveReduction.refl encA (fun _ => 0)) (fun _ => Iff.rfl)

/-- Complement the source language `Aᶜ` without changing the `OracleCallBound` profile. -/
@[expose]
def complLeft {A : Set α} {B : Set β} (R : BoundedOracleReduction encA encB A B) :
    BoundedOracleReduction encA encB Aᶜ B where
  program a := Bool.not <$> R.program a
  bound := R.bound
  isOraclePPTOn := by
    have hnot : ComputableInPolyTime Bool.not encBool encBool :=
      ComputableInPolyTime.bool_not
    simpa only [OracleComp.interpret_map] using R.isOraclePPTOn.map hnot
  decides a := by
    rw [Set.mem_compl_iff, R.decides a, OracleComp.interpret_map]
    change ¬(_ = true) ↔ (!(OracleComp.interpret (m := Id) _ (R.program a))) = true
    cases OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (R.program a) <;> simp
  respects_bound a :=
    (OracleCallBound.respects_map (encodedDecisionOracle encB B) Bool.not (R.program a)
      (R.bound a)).mpr (R.respects_bound a)

/-- Every language's complement reduces to the language itself via `1` query (`Aᶜ ≤ B` for `B = A`).
-/
@[expose]
noncomputable def complSelf (encA : α ↪ List Bool) (A : Set α) :
    BoundedOracleReduction encA encA Aᶜ A :=
  (refl encA A).complLeft

private theorem computableInPolyTime_isCan {β : Type} {encB : β ↪ List Bool} (D : Decoder encB) :
    ComputableInPolyTime (fun w : List Bool => decide (encB (D.decode w) = w)) encBits encBool := by
  have hreenc : ComputableInPolyTime (fun b : β => (encB b : List Bool)) encB encBits :=
    ComputableInPolyTime.id'.of_enc_eq fun _ => rfl
  exact (hreenc.comp D.computableInPolyTime).decide_eq' .id'

private theorem decide_mem_image_eq_of_decoder {β : Type} {encB : β ↪ List Bool}
    (D : Decoder encB) {B : Set β} {g : β → Bool} (hgB : ∀ b, b ∈ B ↔ g b = true)
    (w : List Bool) [Decidable (w ∈ encB '' B)] :
    decide (w ∈ encB '' B) =
      if decide (encB (D.decode w) = w) then g (D.decode w) else false := by
  by_cases hcan : encB (D.decode w) = w
  · simp only [hcan, decide_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hgB]
    conv_lhs => rw [← hcan]
    exact encB.injective.mem_set_image
  · have hnot : w ∉ encB '' B := by
      rintro ⟨b, _, rfl⟩
      exact hcan (congrArg encB (D.decode_enc b))
    simp [hcan, hnot]

/-- Lift a typed `BoundedOracleReduction encB encC B C` to a word-level `BoundedOracleProgram`
answering `encodedDecisionOracle encB B` via a total polynomial-time `D : Decoder encB`:
non-canonical words (`encB (D.decode w) ≠ w`) are rejected in `0` queries, while canonical
encodings run `R₂`. -/
@[expose]
noncomputable def toDecodedWordProgram {B : Set β} {C : Set γ}
    (D : Decoder encB) (R₂ : BoundedOracleReduction encB encC B C) :
    BoundedOracleProgram encBits encBits
      (encodedDecisionOracle encC C) (encodedDecisionOracle encB B) where
  program w := if decide (encB (D.decode w) = w) then
    (fun b => [b]) <$> R₂.program (D.decode w) else pure [false]
  bound w := if decide (encB (D.decode w) = w) then
    { R₂.bound (D.decode w) with alen := 1 } else OracleCallBound.zero
  alenCap _ := 1
  isOraclePPTOn := by
    let isCan (w : List Bool) : Bool := decide (encB (D.decode w) = w)
    let yesProg (w : List Bool) : WordQueryComp Unit (List Bool) :=
      (fun b => [b]) <$> R₂.program (D.decode w)
    have hsingleton : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits :=
      ComputableInPolyTime.id'.of_enc_eq fun b => (encBool_apply b).symm
    have hyes_ppt : IsOraclePPTOn encBits encBits
        (fun w => OracleComp.interpret ProbOracleComp.query (yesProg w)) := by
      simpa only [yesProg, OracleComp.interpret_map] using
        (R₂.isOraclePPTOn.preprocess D.computableInPolyTime).map hsingleton
    have hno_ppt : IsOraclePPTOn encBits encBits
        (fun _ : List Bool =>
          OracleComp.interpret (spec := fun _ : Unit × List Bool => List Bool)
            ProbOracleComp.query (pure [false])) := by
      simpa only [OracleComp.interpret_pure] using
        (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) [false]).isOraclePPTOn
    exact (IsOraclePPTOn.cond (computableInPolyTime_isCan D) hyes_ppt hno_ppt).congr
      fun w _ _ _ => by by_cases hc : isCan w = true <;> simp [isCan, yesProg, hc]
  computableInPolyTime_alenCap := .const 1
  eval_eq w := by
    classical
    have hdec := decide_mem_image_eq_of_decoder D (B := B)
      (g := fun b => OracleComp.interpret (m := Id) (languageOracle (encC '' C)) (R₂.program b))
      R₂.decides w
    change OracleComp.interpret (m := Id) (languageOracle (encC '' C))
        (if decide (encB (D.decode w) = w) then
          (fun b => [b]) <$> R₂.program (D.decode w) else pure [false]) =
      [decide (w ∈ encB '' B)]
    rw [hdec]
    split_ifs
    · simp only [OracleComp.interpret_map]; rfl
    · rfl
  respects_bound w := by
    by_cases hc : decide (encB (D.decode w) = w) = true
    · simp only [hc, ↓reduceIte]
      have ⟨hqc, hql, htql, _⟩ := (OracleCallBound.respects_map (encodedDecisionOracle encC C)
        (fun b => [b]) (R₂.program (D.decode w)) (R₂.bound (D.decode w))).mpr
        (R₂.respects_bound (D.decode w))
      exact ⟨hqc, hql, htql, fun _ _ => by simp only [length_encodedDecisionOracle, le_refl]⟩
    · simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]
      exact OracleCallBound.respects_pure _ _ _
  alen_le_alenCap w := by split_ifs <;> simp [OracleCallBound.zero]

/-- **Transitivity (`transDecoded`) across any typed intermediate language `(B, encB)` equipped
with `D : Decoder encB`,** tracking explicit `(qcount, qlen, totalQlen, alen)` composition. -/
@[expose]
noncomputable def transDecoded {A : Set α} {B : Set β} {C : Set γ}
    (D : Decoder encB)
    (R₁ : BoundedOracleReduction encA encB A B)
    (R₂ : BoundedOracleReduction encB encC B C) :
    BoundedOracleReduction encA encC A C :=
  ofProgram (R₁.toProgram.comp (R₂.toDecodedWordProgram D)) (fun _ => by simp)

/-- **Transitivity (`trans`) across word-encoded intermediate languages `(B, encBits)`.** -/
@[expose]
noncomputable def trans {A : Set α} {B : Set (List Bool)} {C : Set γ}
    (R₁ : BoundedOracleReduction encA encBits A B)
    (R₂ : BoundedOracleReduction encBits encC B C) :
    BoundedOracleReduction encA encC A C :=
  R₁.transDecoded Decoder.bits R₂

/-! ### Bridges to `PolyTimeTuringReducible`, `PWithOracleQueries`, `P`, and `PSPACE` -/

/-- Every `BoundedOracleReduction` witnesses `PolyTimeTuringReducible` (`A ≤ᵖ_T B`). -/
theorem polyTimeTuringReducible {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) :
    PolyTimeTuringReducible encA encB A B := by
  classical
  exact ⟨fun a => decide (a ∈ A),
    ⟨R.program, R.isOraclePPTOn, fun a => R.toProgram.eval_eq a⟩,
    fun _ => by simp⟩

/-- If `R.qcount a ≤ r (encA a).length` for all `a`, then `R` places `A` in
`PWithOracleQueries (encB '' B) r encA`. -/
theorem mem_PWithOracleQueries {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) {r : ℕ → ℕ}
    (hr : ∀ a, R.qcount a ≤ r (encA a).length) :
    A ∈ PWithOracleQueries (encB '' B) r encA := by
  classical
  exact ⟨fun a => decide (a ∈ A), ⟨R.program, R.isOraclePPTOn,
    fun a => ⟨R.toProgram.eval_eq a, (R.respects_bound a).1.trans (hr a)⟩⟩, fun _ => by simp⟩

/-- Conversely, any membership witness `A ∈ PWithOracleQueries (encB '' B) r encA` yields a
`BoundedOracleReduction encA encB A B` with `qcount a = r |encA a|`, polynomial `qlen`,
`totalQlen = qcount * qlen`, and `alen = 1`. -/
noncomputable def ofPWithOracleQueries {A : Set α} {B : Set β} {r : ℕ → ℕ}
    (h : A ∈ PWithOracleQueries (encB '' B) r encA) :
    BoundedOracleReduction encA encB A B := by
  classical
  let f := Classical.choose h
  have hf_spec := Classical.choose_spec h
  let prog := Classical.choose hf_spec.1
  have hprog := Classical.choose_spec hf_spec.1
  let hqb_ex := IsOraclePPTOn.query_bounds hprog.1
  let c := Classical.choose hqb_ex
  let hc := Classical.choose_spec hqb_ex
  let d := Classical.choose hc
  have hqb : ∀ a, (OracleComp.interpret ProbOracleComp.query (prog a)).IsQueryBounded
        (c * ((encA a).length + 1) ^ d) ∧
      (OracleComp.interpret ProbOracleComp.query (prog a)).QueriesSatisfy
        (fun request => request.2.length ≤ c * ((encA a).length + 1) ^ d) :=
    Classical.choose_spec hc
  let ql (a : α) : ℕ := c * ((encA a).length + 1) ^ d
  refine
    { program := prog
      bound := fun a =>
        { qcount := r (encA a).length
          qlen := ql a
          totalQlen := r (encA a).length * ql a
          alen := 1 }
      isOraclePPTOn := hprog.1
      decides := fun a => by rw [hf_spec.2 a, (hprog.2 a).1]
      respects_bound := fun a => ?_ }
  set qs := OracleComp.queriesWith (fun q => encodedDecisionOracle encB B q.2) (prog a)
  have hqc : qs.length ≤ r (encA a).length := (hprog.2 a).2
  have hql : ∀ q ∈ qs, q.2.length ≤ ql a :=
    forall_queriesWith_of_probQueriesSatisfy _ (prog a) (hqb a).2
  exact ⟨hqc, hql, BoundedOracleProgram.map_sum_le_mul hql hqc,
    fun _ _ => by simp only [length_encodedDecisionOracle, le_refl]⟩

/-- **Polynomial-time transfer (`mem_P`)** across `BoundedOracleReduction` when `D : Decoder encB`
and `B ∈ P encB`. -/
theorem mem_P {A : Set α} {B : Set β} (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA := by
  classical
  obtain ⟨g, hg, hgB⟩ := hB
  let R_P : BoundedOracleReduction encB encBits B ∅ := ofPolyTime ∅ hg hgB
  let R_comp := R.transDecoded D R_P
  have horacle : ComputableInPolyTime (encodedDecisionOracle encBits ∅) encBits encBits :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) [false]).of_enc_eq
      fun w => by simp [encodedDecisionOracle, languageOracle]
  exact ⟨_, R_comp.toProgram.computableInPolyTime horacle, fun _ => by simp⟩

/-- **Polynomial-space transfer (`mem_PSPACE`)** across `BoundedOracleReduction` when
`D : Decoder encB` and `B ∈ PSPACE encB`. -/
theorem mem_PSPACE {A : Set α} {B : Set β} (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B) (hB : B ∈ PSPACE encB) :
    A ∈ PSPACE encA := by
  classical
  obtain ⟨_, S, hS, g, ⟨c, htm, hout⟩, hgB⟩ := exists_computableInO_of_mem_PSPACE hB
  have hdecB_ps : ComputableInPolySpace (fun w : List Bool =>
      if decide (encB (D.decode w) = w) then g (D.decode w) else false) encBits encBool :=
    ComputableInPolySpace.ite (.of_polyTime (computableInPolyTime_isCan D))
      ((ComputableInPolySpace.of_inSpace hS ⟨_, c, htm, hout⟩).comp
        (.of_polyTime D.computableInPolyTime))
      (.of_polyTime (.const false))
  have horacle : ComputableInPolySpace (encodedDecisionOracle encB B) encBits encBits := by
    have heq : encodedDecisionOracle encB B =
        fun w => [if decide (encB (D.decode w) = w) then g (D.decode w) else false] :=
      funext fun w => congrArg List.singleton (decide_mem_image_eq_of_decoder D hgB w)
    rw [heq]
    exact (ComputableInPolySpace.of_polyTime (show ComputableInPolyTime (fun b : Bool => [b])
      encBool encBits from ComputableInPolyTime.id'.of_enc_eq fun b =>
        (encBool_apply b).symm)).comp hdecB_ps
  exact ⟨_, R.toProgram.computableInPolySpace horacle, fun _ => by simp⟩

/-! ### Parameterized exponential and subexponential oracle transfer -/

open _root_.Turing.MultiTapeMachine in
/-- Single guarded step `stepGuard (K, cfg) = (K, answerStep (guardAns K) cfg)` with explicit
`ComputableInO` certificate, charging `t (D.decode req)` only when `req` is pending, canonical,
and within the parameter budget `μB (D.decode req) ≤ K`. -/
private theorem guardedStep_inO {β : Type} {encB : β ↪ List Bool}
    (D : Decoder encB) {μB : β → ℕ} (hμB : ComputableInPolyTime μB encB encNat)
    {g : β → Bool} {t : β → ℕ} (hg : ComputableInO g encB encBool t t)
    {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit) :
    let isActive (s : ℕ × FiniteConfig k Bool (Fin m) Unit) : Bool :=
      (machine.pendingQuery s.2).isSome &&
        (decide (encB (D.decode (machine.pendingRequest s.2)) = machine.pendingRequest s.2) &&
          decide (μB (D.decode (machine.pendingRequest s.2)) ≤ s.1))
    let guardAns (K : ℕ) (w : List Bool) : Bool :=
      if decide (encB (D.decode w) = w) && decide (μB (D.decode w) ≤ K) then
        g (D.decode w) else false
    ∃ d : ℕ, ComputableInO
      (fun s : ℕ × FiniteConfig k Bool (Fin m) Unit =>
        (s.1, machine.answerStep (fun q => [guardAns s.1 q.2]) s.2))
      (encPair encNat encFiniteConfig) (encPair encNat encFiniteConfig)
      (fun s => ((encPair encNat encFiniteConfig s).length + 1) ^ d +
        if isActive s then
          t (D.decode (machine.pendingRequest s.2)) +
            ((encPair encNat encFiniteConfig s).length +
              (encBool (g (D.decode (machine.pendingRequest s.2)))).length + 1) ^ d
        else 0)
      (fun s => ((encPair encNat encFiniteConfig s).length + 1) ^ d +
        if isActive s then
          t (D.decode (machine.pendingRequest s.2)) +
            ((encPair encNat encFiniteConfig s).length +
              (encBool (g (D.decode (machine.pendingRequest s.2)))).length + 1) ^ d
        else 0) := by
  classical
  let E := encPair encNat (encFiniteConfig (k := k) (State := Fin m) (Oracle := Unit))
  let subinst (s : ℕ × FiniteConfig k Bool (Fin m) Unit) : β :=
    D.decode (machine.pendingRequest s.2)
  have hbud_pt : ComputableInPolyTime Prod.fst E encNat := .fst _ _
  have hcfg_pt : ComputableInPolyTime Prod.snd E encFiniteConfig := .snd _ _
  have hpend_pt : ComputableInPolyTime (fun s => machine.pendingRequest s.2) E encBits :=
    machine.pendingRequest_pt.comp hcfg_pt
  have hsub_pt : ComputableInPolyTime subinst E encB := D.computableInPolyTime.comp hpend_pt
  have hisActive_pt : ComputableInPolyTime
      (fun s : ℕ × FiniteConfig k Bool (Fin m) Unit =>
        (machine.pendingQuery s.2).isSome &&
          (decide (encB (subinst s) = machine.pendingRequest s.2) &&
            decide (μB (subinst s) ≤ s.1))) E encBool :=
    ComputableInPolyTime.bool_and.comp
      ((((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt).comp hcfg_pt)
        |>.prod (ComputableInPolyTime.bool_and.comp
          (((computableInPolyTime_isCan D).comp hpend_pt).prod
            ((hμB.comp hsub_pt).binary_le' hbud_pt))))
  have hlocal_pt : ComputableInPolyTime
      (fun s : ℕ × FiniteConfig k Bool (Fin m) Unit =>
        (s.1, machine.answerStep (fun _ => [false]) s.2)) E E :=
    hbud_pt.prod ((machine.computableInPolyTime_answerStep_word (.const [false])).comp hcfg_pt)
  have hcomb_pt : ComputableInPolyTime
      (fun p : (ℕ × FiniteConfig k Bool (Fin m) Unit) × Bool =>
        (p.1.1, machine.receiveWord (p.1.2, [p.2]))) (encPair E encBool) E :=
    (hbud_pt.comp (.fst _ _)).prod (machine.receiveWord_pt.comp
      ((hcfg_pt.comp (.fst _ _)).prod
        ((ComputableInPolyTime.snd E encBool).of_enc_eq (encD := encBits) fun p =>
          (encBool_apply p.2).symm)))
  obtain ⟨d, h⟩ := exists_computableInO_searchStep (done := fun _ => false)
    (.const false) hisActive_pt hsub_pt hlocal_pt hcomb_pt hg
  refine ⟨d, (h.mono_le (fun _ => by simp only [true_and]; exact le_rfl)
    (fun _ => by simp only [true_and]; exact le_rfl)).of_enc_eq fun ⟨K, cfg⟩ => ?_⟩
  congr 1
  simp only [Bool.false_eq_true, ite_false]
  rw [machine.answerStep_word (fun w =>
    [if decide (encB (D.decode w) = w) && decide (μB (D.decode w) ≤ K) then
      g (D.decode w) else false]) cfg,
    machine.answerStep_word (fun _ => [false]) cfg]
  by_cases hpq : (machine.pendingQuery cfg).isSome = true
  · by_cases hc : (decide (encB (D.decode (machine.pendingRequest cfg)) =
          machine.pendingRequest cfg) &&
        decide (μB (D.decode (machine.pendingRequest cfg)) ≤ K)) = true <;>
      simp [hpq, hc, subinst]
  · simp [hpq]

/-- Agreement between `languageOracle (encB '' B)` and the budget-guarded oracle `guardAns K`
along every query actually issued by `R.program a`. -/
private theorem guardedRun_decides_iff {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (D : Decoder encB) (R : BoundedOracleReduction encA encB A B)
    {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit) {clk : α → ℕ}
    (hrun : ∀ a answer, encBool (OracleComp.interpret (m := Id) answer (R.program a)) =
      OracleComp.interpret (m := Id) answer
        (machine.run (pure false) (fun op word => OracleComp.query (op, word)) (clk a)
          (encA a)))
    {μB : β → ℕ} {g : β → Bool} (hgB : ∀ b, b ∈ B ↔ g b = true) {K : α → ℕ}
    (hparam : ∀ a q,
      q ∈ OracleComp.queriesWith (languageOracle (encB '' B)) (R.program a) →
        ∀ b, encB b = q.2 → μB b ≤ K a)
    (a : α) :
    let guardAns (w : List Bool) : Bool :=
      if decide (encB (D.decode w) = w) && decide (μB (D.decode w) ≤ K a) then
        g (D.decode w) else false
    a ∈ A ↔ ((machine.answerStep fun q => [guardAns q.2])^[clk a]
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output.headD
        false = true := by
  classical
  let ans_a : Unit × List Bool → List Bool := fun q =>
    [if decide (encB (D.decode q.2) = q.2) && decide (μB (D.decode q.2) ≤ K a) then
      g (D.decode q.2) else false]
  have hcongr : OracleComp.interpret (m := Id) ans_a (R.program a) =
      OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (R.program a) := by
    refine (OracleComp.interpret_id_congr (languageOracle (encB '' B)) ans_a (R.program a) ?_).1
    intro q hq
    refine congrArg List.singleton ?_
    rw [decide_mem_image_eq_of_decoder D hgB q.2]
    by_cases hcan : encB (D.decode q.2) = q.2 <;> simp_all [hparam a q hq (D.decode q.2)]
  have hm_out : ((machine.answerStep ans_a)^[clk a]
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output =
      encBool (OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (R.program a)) := by
    rw [← hcongr, hrun a ans_a, ← machine.interpret_run_pure_false]
  change a ∈ A ↔ ((machine.answerStep ans_a)^[clk a]
    (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output.headD
      false = true
  rw [hm_out, encBool_apply, List.headD_cons]
  exact R.decides a

/-- Real-valued ceiling/polynomial domination step for `decidableInExpTime`. -/
private theorem expTime_step_dom {dn di da e Cp E clk stepPoly stateB clockLen leafMax
    lenA finLen k_cost scale offset μA : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hfin : finLen ≤ stateB) (hclkLen : clockLen ≤ clk)
    (hleaf : (leafMax : ℝ) ≤ (k_cost : ℝ) * (2 ^ (δ * (scale * μA + offset : ℕ)) *
      ((clk : ℝ) + 1) ^ e) + k_cost + 1)
    (hCp : (lenA + 1) ^ dn + (lenA + 1) ^ di + (stateB + 1) ^ da +
      (clk + 1) * (stepPoly + stateB + (clk + 1) ^ 2 + (clk + 1) ^ e + 1) ≤
      Cp * (lenA + 1) ^ E) :
    (((lenA + 1) ^ dn + (lenA + 1) ^ di +
      (clk + 1) * (stepPoly + leafMax + stateB + (clockLen + 1) ^ 2) +
      (finLen + 1) ^ da : ℕ) : ℝ) ≤
      (⌈(Cp : ℝ) + Cp * (k_cost * 2 ^ (δ * offset) + (k_cost + 1))⌉₊ : ℝ) *
        (2 ^ ((scale * δ) * μA) * ((lenA : ℝ) + 1) ^ E) := by
  set P : ℝ := ((lenA : ℝ) + 1) ^ E
  set Y : ℝ := (2 : ℝ) ^ ((scale * δ) * μA)
  set C_big : ℝ := (Cp : ℝ) + Cp * (k_cost * 2 ^ (δ * offset) + (k_cost + 1))
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hYP : P ≤ Y * P := le_mul_of_one_le_left (by positivity) hY1
  have hbase : ((lenA + 1) ^ dn + (lenA + 1) ^ di + (finLen + 1) ^ da +
      (clk + 1) * (stepPoly + stateB + (clockLen + 1) ^ 2) : ℝ) ≤ Cp * P := by
    have hf := Nat.pow_le_pow_left (Nat.add_le_add_right hfin 1) da
    have hc := Nat.pow_le_pow_left (Nat.add_le_add_right hclkLen 1) 2
    have hm := Nat.mul_le_mul_left (clk + 1)
      (show stepPoly + stateB + (clockLen + 1) ^ 2 ≤
        stepPoly + stateB + (clk + 1) ^ 2 + (clk + 1) ^ e + 1 by omega)
    dsimp only [P]
    exact_mod_cast (show (lenA + 1) ^ dn + (lenA + 1) ^ di + (finLen + 1) ^ da +
      (clk + 1) * (stepPoly + stateB + (clockLen + 1) ^ 2) ≤ Cp * (lenA + 1) ^ E by omega)
  have hcpow : ((clk : ℝ) + 1) * ((clk : ℝ) + 1) ^ e ≤ Cp * P := by
    have hm := Nat.mul_le_mul_left (clk + 1)
      (show (clk + 1) ^ e ≤ stepPoly + stateB + (clk + 1) ^ 2 + (clk + 1) ^ e + 1 by omega)
    dsimp only [P]
    exact_mod_cast (show (clk + 1) * (clk + 1) ^ e ≤ Cp * (lenA + 1) ^ E by omega)
  have hclk1 : (clk : ℝ) + 1 ≤ Cp * P := by
    have hm := Nat.mul_le_mul_left (clk + 1)
      (show 1 ≤ stepPoly + stateB + (clk + 1) ^ 2 + (clk + 1) ^ e + 1 by omega)
    dsimp only [P]
    exact_mod_cast (show clk + 1 ≤ Cp * (lenA + 1) ^ E by omega)
  have hexp : (2 : ℝ) ^ (δ * (scale * μA + offset : ℕ)) = 2 ^ (δ * offset) * Y := by
    push_cast; rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  rw [hexp] at hleaf
  have hmul : ((clk : ℝ) + 1) * leafMax ≤
      (k_cost * 2 ^ (δ * offset)) * Y * (Cp * P) + (k_cost + 1 : ℝ) * (Cp * P) := by
    have h1 := mul_le_mul_of_nonneg_left hleaf (show (0 : ℝ) ≤ clk + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcpow
      (show (0 : ℝ) ≤ (k_cost : ℝ) * 2 ^ (δ * offset) * Y by positivity)
    have h3 := mul_le_mul_of_nonneg_left hclk1 (show (0 : ℝ) ≤ (k_cost : ℝ) + 1 by positivity)
    linarith
  have hbase_Y := mul_le_mul_of_nonneg_left hYP (show (0 : ℝ) ≤ Cp by positivity)
  have hk_Y := mul_le_mul_of_nonneg_left hYP
    (show (0 : ℝ) ≤ (Cp : ℝ) * (k_cost + 1) by positivity)
  refine (by push_cast at hbase ⊢; linarith : _ ≤ C_big * (Y * P)).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil C_big) (by positivity))

open _root_.Turing.MultiTapeMachine in
/-- **Parameterized exponential-time transfer across `BoundedOracleReduction`:**
when `D : Decoder encB` decodes canonical `encB`-words in polynomial time, `μA` and `μB` are
polynomial-time computable, and every query `q` issued by `R.program a` against `encB '' B`
with `encB b = q.2` satisfies `μB b ≤ scale * μA a + offset`, any `2 ^ (δ * μB b) * poly(|b|)`
decider for `B` transfers to a `2 ^ ((scale * δ) * μA a) * poly(|a|)` decider for `A` — with
polynomial overhead absorbing both query count and query construction cost. -/
theorem decidableInExpTime {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B)
    {scale offset : ℕ}
    (hμA : ComputableInPolyTime μA encA encNat)
    (hμB : ComputableInPolyTime μB encB encNat)
    (hparam : ∀ a q,
      q ∈ OracleComp.queriesWith (languageOracle (encB '' B)) (R.program a) →
        ∀ b, encB b = q.2 → μB b ≤ scale * μA a + offset)
    {δ : ℝ} (hδ : 0 ≤ δ) (hB : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (scale * δ) := by
  classical
  obtain ⟨e, h⟩ := hB
  obtain ⟨g, t, k_cost, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨k_tm, m_tm, machine, c_clk, d_clk, hrun⟩ := R.isOraclePPTOn.exists_fin_run_pure_false
  let _ : Inhabited β := ⟨D.decode []⟩
  let _ : Inhabited (ℕ × FiniteConfig k_tm Bool (Fin m_tm) Unit) :=
    ⟨(0, FiniteConfig.init machine.initial [])⟩
  obtain ⟨d_step, hstep⟩ := guardedStep_inO D hμB hg machine
  let K (a : α) : ℕ := scale * μA a + offset
  let clk (a : α) : ℕ := c_clk * ((encA a).length + 1) ^ d_clk
  let guardAns (K' : ℕ) (w : List Bool) : Bool :=
    if decide (encB (D.decode w) = w) && decide (μB (D.decode w) ≤ K') then
      g (D.decode w) else false
  let stepGuard (s : ℕ × FiniteConfig k_tm Bool (Fin m_tm) Unit) :=
    (s.1, machine.answerStep (fun q => [guardAns s.1 q.2]) s.2)
  let initSt (a : α) :=
    (K a, FiniteConfig.init (k := k_tm) (Oracle := Unit) machine.initial (encA a))
  have hK_pt : ComputableInPolyTime K encA encNat :=
    ((ComputableInPolyTime.const scale).binary_mul' hμA).binary_add' (.const offset)
  have hclk_pt : ComputableInPolyTime clk encA encNat :=
    (ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.unary_eval (Polynomial.C c_clk * (Polynomial.X + 1) ^ d_clk)).comp
        (ComputableInPolyTime.encoding_length encA))).of_enc_eq fun _ => by simp [clk]
  obtain ⟨dn, _, hn⟩ := hclk_pt.exists_degree
  have hinit_pt : ComputableInPolyTime initSt encA (encPair encNat encFiniteConfig) :=
    hK_pt.prod (show ComputableInPolyTime (fun a => FiniteConfig.init (k := k_tm) (Oracle := Unit)
      machine.initial (encA a)) encA encFiniteConfig from
        ComputableInPolyTime.finiteConfig_init (by fun_prop) _)
  obtain ⟨di, _, hi_deg⟩ := hinit_pt.exists_degree
  obtain ⟨da, _, ha_deg⟩ := (Decoder.bool.computableInPolyTime.comp
    ((show ComputableInPolyTime (fun cfg : FiniteConfig k_tm Bool (Fin m_tm) Unit =>
      cfg.tapes.output) encFiniteConfig encBits by fun_prop).comp
        (.snd encNat encFiniteConfig))).exists_degree
  have hiter_eq (a : α) (i : ℕ) : stepGuard^[i] (initSt a) =
      (K a, (machine.answerStep fun q => [guardAns (K a) q.2])^[i]
        (FiniteConfig.init machine.initial (encA a))) := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have hspace (a : α) {i : ℕ} (hi : i ≤ clk a) :=
    machine.spaceBound_iterate_answerStep_word (fun w => [guardAns (K a) w]) (w := encA a)
      (steps := clk a) (answerSize := 1) (fun _ _ => le_rfl) hi
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k_tm) (State := Fin m_tm) (Oracle := Unit)
  obtain ⟨cK, dK, hK_len⟩ := hK_pt.polyBounded_length.exists_le
  let stateBound (a : α) : ℕ := 2 * (cK * ((encA a).length + 1) ^ dK) + 1 +
    cf * ((encA a).length + clk a + 2)
  have hstate (a : α) (i : ℕ) (hi : i ≤ clk a) :
      (encPair encNat encFiniteConfig (stepGuard^[i] (initSt a))).length ≤ stateBound a := by
    rw [hiter_eq, length_encPair]
    have hcfg_len : (encFiniteConfig _).length ≤ cf * ((encA a).length + clk a + 2) :=
      (hcf _ _ _ _ (hspace a hi)).trans (Nat.mul_le_mul_left cf (by omega))
    have hk_len := hK_len a
    dsimp only [stateBound]
    omega
  let leafMax (a : α) : ℕ :=
    ⌈(k_cost : ℝ) * (2 ^ (δ * (K a : ℝ)) * ((clk a : ℝ) + 1) ^ e) + k_cost⌉₊
  let stepPoly (a : α) : ℕ := (stateBound a + 1) ^ d_step + (stateBound a + 2) ^ d_step
  have hround (a : α) (i : ℕ) (hi : i ≤ clk a) :
      let st := stepGuard^[i] (initSt a)
      let r := machine.pendingRequest st.2
      ((encPair encNat encFiniteConfig st).length + 1) ^ d_step +
        (if (machine.pendingQuery st.2).isSome &&
            (decide (encB (D.decode r) = r) && decide (μB (D.decode r) ≤ st.1)) then
          t (D.decode r) + ((encPair encNat encFiniteConfig st).length +
            (encBool (g (D.decode r))).length + 1) ^ d_step else 0) ≤
        stepPoly a + leafMax a := by
    intro st r
    have hst : (encPair encNat encFiniteConfig st).length ≤ stateBound a := hstate a i hi
    have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hst 1) d_step
    split_ifs with hact
    · rcases Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hact).2 with ⟨hcan_b, hle_b⟩
      have hst_eq := hiter_eq a i
      set b := D.decode r
      have hμ_le : μB b ≤ K a := by
        simpa only [st, hst_eq] using (of_decide_eq_true hle_b : μB b ≤ st.1)
      have hreq_len : (encB b).length ≤ clk a := by
        rw [of_decide_eq_true hcan_b]
        simpa only [r, st, hst_eq] using (machine.length_pendingRequest_le (hspace a hi)).trans hi
      have ht_le : t b ≤ leafMax a := by
        refine Nat.cast_le.mp ((ht b).trans (le_trans ?_ (Nat.le_ceil _)))
        have hexp : (2 : ℝ) ^ (δ * μB b) ≤ 2 ^ (δ * (K a : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hμ_le) hδ)
        gcongr
      have hp2 : ((encPair encNat encFiniteConfig st).length +
          (encBool (g b)).length + 1) ^ d_step ≤ (stateBound a + 2) ^ d_step := by
        simp only [encBool_apply, List.length_singleton]
        exact Nat.pow_le_pow_left (by omega) d_step
      dsimp only [stepPoly]; omega
    · dsimp only [stepPoly]; omega
  have hloop := ha_deg.inO.comp (ComputableInO.iterate hn.inO hi_deg.inO hstep hround hround hstate)
  obtain ⟨Cp, E, hCp⟩ := (show PolyBounded (fun a => (encA a).length)
    (fun a => ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
      (stateBound a + 1) ^ da + (clk a + 1) * (stepPoly a + stateBound a +
        (clk a + 1) ^ 2 + (clk a + 1) ^ e + 1)) by
    growth_poly).exists_le
  refine DecidableInExpTime.of_computableInO hloop (fun a => by
    change a ∈ A ↔ (stepGuard^[clk a] (initSt a)).2.tapes.output.headD false = true
    rw [hiter_eq a (clk a)]
    exact guardedRun_decides_iff D R machine (fun x ans => (hrun x ans).symm) hgB hparam a)
    ⌈(Cp : ℝ) + Cp * (k_cost * 2 ^ (δ * offset) + (k_cost + 1))⌉₊ E fun a =>
      expTime_step_dom hδ (hstate a (clk a) le_rfl) (length_encNat_le_self (clk a))
        (Nat.ceil_lt_add_one (by positivity)).le (hCp a)

/-- **Parameterized subexponential-time transfer across `BoundedOracleReduction`.** -/
theorem decidableInSubexpTime {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B)
    {scale offset : ℕ}
    (hμA : ComputableInPolyTime μA encA encNat)
    (hμB : ComputableInPolyTime μB encB encNat)
    (hparam : ∀ a q,
      q ∈ OracleComp.queriesWith (languageOracle (encB '' B)) (R.program a) →
        ∀ b, encB b = q.2 → μB b ≤ scale * μA a + offset)
    (hB : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro ε hε
  have hδ : 0 < ε / (scale + 1) := by positivity
  refine (R.decidableInExpTime D hμA hμB hparam hδ.le (hB _ hδ)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end BoundedOracleReduction

end Cslib.Complexity
