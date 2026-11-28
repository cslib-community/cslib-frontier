/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
public import CslibFrontier.Computability.Complexity.Classes.TFNP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise

/-!
# Few oracle queries do not help to solve search problems

If a search problem `R` in `FNP` (Goldreich's `PC`) is solved in polynomial time relative to some
oracle language `O` by a machine that makes at most `c log₂ n + c` requests on instances of encoded
length `n`, then `R` is in `FPSearch` (Goldreich's `PF`)
(`Cslib.Complexity.mem_FPSearch_of_computableInPolyTimeWithOracleQueries_log`,
[Goldreich, Exercise 2.10][Goldreich2006DraftR1]). The oracle is arbitrary: it need not be a
decision problem in `NP`, nor have anything to do with `R`. Contrapositively, a search problem in
`PC \ PF` is not solved by any polynomial-time oracle machine with that many requests, which is
why the self-reductions of the source make more than logarithmically many requests.

The proof enumerates the answers. There are at most `2 ^ (c log₂ n + c) ≤ 2 ^ c (n + 1) ^ c`
lists of answers to the requests, and for each of them the machine can be run without the oracle,
answering its requests from the list (`Turing.MultiTapePTM.popStep`). Running it along the list of
the true answers gives the true output (`Cslib.OracleComp.run_interpret_popAnswer`), so some list
gives a solution whenever one exists, and the verifier of `R` recognizes it. The general form
(`Cslib.Complexity.mem_FPSearch_of_computableInPolyTimeWithOracleQueries_of_two_pow_le`) only
asks that `2 ^ r n` be polynomially bounded, for a bound `r n` on the requests.

Answering requests from a list is a stateful oracle. A certificate of
`Cslib.Complexity.ComputableInPolyTimeWithOracle` quantifies over stateful oracles, so the
machine behind it, with every coin fixed to `false`, also reproduces the program against them
(`Cslib.Probability.IsOraclePPTOn.exists_run_pure_false_stateM`, the stateful form of
`Cslib.Probability.IsOraclePPTOn.exists_run_pure_false`). In particular it makes the same requests
as the program, not merely the same number of them.

## Main definitions

* `Cslib.OracleComp.popAnswer`: answer each request with the next bit of a list.
* `Turing.MultiTapePTM.popStep`: one instruction of a machine whose requests are answered from a
  list.

## Main results

* `Cslib.OracleComp.run_interpret_popAnswer`, `Cslib.OracleComp.run_interpret_popAnswer_congr`:
  answering requests from the list of the oracle's answers.
* `Turing.MultiTapePTM.run_interpret_popAnswer_run`,
  `Turing.MultiTapePTM.computableInPolyTime_popRun`: a clocked run against a list of answers is
  an iteration of `popStep` and is polynomial-time.
* `Cslib.Complexity.mem_FPSearch_of_computableInPolyTimeWithOracleQueries_of_two_pow_le`,
  `Cslib.Complexity.mem_FPSearch_of_computableInPolyTimeWithOracleQueries_log`: Goldreich,
  Exercise 2.10.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2006DraftR1],
  Exercise 2.10 (draft r1.pdf of December 2006, printed p. 106).
-/

@[expose] public section

namespace Cslib.OracleComp

variable {Operation β : Type}

/-- Answer each request with the next bit of a list of answers, `false` once it is exhausted. As a
stateful oracle it can be handed to a certificate of `Cslib.Probability.IsOraclePPTOn`; the run of a
program on a list of answers alone is `Cslib.OracleComp.runWithAnswers`. -/
def popAnswer (_ : Operation × List Bool) : StateM (List Bool) (List Bool) :=
  fun s => ([s.headD false], s.tail)

open Classical in
/-- Answering a program's requests with the list of the oracle's answers to them, in order, is
running it against the oracle; answers left over are not consumed. -/
theorem run_interpret_popAnswer (O : Set (List Bool))
    (program : Complexity.WordQueryComp Operation β) (rest : List Bool) :
    (OracleComp.interpret (m := StateM (List Bool)) popAnswer program).run
        ((queriesWith (Complexity.languageOracle O) program).map (fun q => decide (q.2 ∈ O)) ++
          rest) =
      (OracleComp.interpret (m := Id) (Complexity.languageOracle O) program, rest) := by
  induction program using PFunctor.FreeM.induction generalizing rest with
  | pure b => rfl
  | lift_bind q cont ih =>
    erw [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      queriesWith_query_bind, interpret_id_query_bind]
    rw [List.map_cons, List.cons_append]
    exact ih _ rest

/-- Answer lists that agree once both are padded with `false` give the same result. -/
theorem run_interpret_popAnswer_congr (program : Complexity.WordQueryComp Operation β)
    {s s' : List Bool} (h : ∀ i, s.getD i false = s'.getD i false) :
    ((OracleComp.interpret (m := StateM (List Bool)) popAnswer program).run s).1 =
      ((OracleComp.interpret (m := StateM (List Bool)) popAnswer program).run s').1 := by
  induction program using PFunctor.FreeM.induction generalizing s s' with
  | pure b => rfl
  | lift_bind q cont ih =>
    have h0 : s.headD false = s'.headD false := by cases s <;> cases s' <;> exact h 0
    erw [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind, StateT.run_bind]
    change ((OracleComp.interpret popAnswer (cont [s.headD false])).run s.tail).1 =
      ((OracleComp.interpret popAnswer (cont [s'.headD false])).run s'.tail).1
    exact h0 ▸ ih _ fun i => by cases s <;> cases s' <;> exact h (i + 1)

end Cslib.OracleComp

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

/-- One instruction of the run with every coin `false`, a query answered by the next bit of a
list of answers (`false` once the list is exhausted), which is then dropped. -/
def popStep (p : FiniteConfig k Bool Control Operation × List Bool) :
    FiniteConfig k Bool Control Operation × List Bool :=
  if (machine.pendingQuery p.1).isSome then (machine.receiveBit (p.1, p.2.headD false), p.2.tail)
  else (machine.localStep p.1, p.2)

private theorem run_interpret_popAnswer_finiteStep (cfg : FiniteConfig k Bool Control Operation)
    (s : List Bool) :
    (OracleComp.interpret (m := StateM (List Bool)) OracleComp.popAnswer
      (MultiTapeMachine.finiteStep machine
        (fun choices => choices <$> (pure false : OracleComp _ Bool))
        (fun op word => OracleComp.query (op, word)) cfg)).run s =
      machine.popStep (cfg, s) := by
  cases hs : cfg.tapes.state with
  | none => simp [finiteStep, hs, popStep, pendingQuery, localStep]; rfl
  | some control =>
    cases ht : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
      cfg.answerSymbols false with
    | step action symbol move => simp [finiteStep, hs, ht, popStep, pendingQuery, localStep]; rfl
    | query op next =>
      cases s <;> simp [finiteStep, hs, ht, StateT.run_map, popStep, pendingQuery, receiveBit] <;>
        rfl

/-- **A coin-fixed run against a list of answers is an iteration of `popStep`.** -/
theorem run_interpret_popAnswer_run (fuel : ℕ) (input s : List Bool) :
    (OracleComp.interpret (m := StateM (List Bool)) OracleComp.popAnswer
        (machine.run (pure false) (fun op word => OracleComp.query (op, word)) fuel input)).run s =
      Prod.map (fun cfg => cfg.tapes.output) id
        (machine.popStep^[fuel] (FiniteConfig.init machine.initial input, s)) := by
  change (OracleComp.interpret (m := StateM (List Bool)) OracleComp.popAnswer
    (MultiTapeMachine.run machine (fun choices => choices <$> (pure false : OracleComp _ Bool))
      (fun op word => OracleComp.query (op, word)) fuel input)).run s = _
  rw [← finiteRunFrom_init, finiteRunFrom, OracleComp.interpret_map, StateT.run_map]
  refine congrArg
    (Prod.map (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output) id) ?_
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [OracleComp.iterate_succ, OracleComp.interpret_bind, StateT.run_bind,
      Function.iterate_succ_apply', ← ih]
    exact machine.run_interpret_popAnswer_finiteStep _ _

/-- The configuration part of `popStep` is an instruction against the oracle answering the next
bit. -/
private theorem fst_popStep (p : FiniteConfig k Bool Control Operation × List Bool) :
    (machine.popStep p).1 = machine.answerStep (fun _ => [p.2.headD false]) p.1 := by
  rw [machine.answerStep_bit (fun _ => p.2.headD false), popStep]
  split_ifs <;> rfl

private theorem length_snd_popStep_le (p : FiniteConfig k Bool Control Operation × List Bool) :
    (machine.popStep p).2.length ≤ p.2.length := by
  unfold popStep
  split_ifs <;> simp

variable [Finite Control]

/-- An instruction against a list of answers is polynomial-time. -/
private theorem computableInPolyTime_popStep [Fintype Operation] :
    ComputableInPolyTime machine.popStep
    (encPair encFiniteConfig encBits) (encPair encFiniteConfig encBits) := by
  unfold popStep
  exact ComputableInPolyTime.ite
    ((ComputableInPolyTime.of_finite (encOut := encBool) Option.isSome).comp
      (machine.pendingQuery_pt.comp (ComputableInPolyTime.fst _ _)))
    ((machine.receiveBit_pt.comp ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
        (ComputableInPolyTime.snd _ _)))).prod
      (ComputableInPolyTime.bitsTail.comp (ComputableInPolyTime.snd _ _)))
    ((machine.localStep_pt.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))

/-- **A clocked run against a list of answers is polynomial-time** in the encoded input and the
list together. -/
theorem computableInPolyTime_popRun [Finite Operation] {α : Type} {input : α ↪ List Bool}
    (c d : ℕ) :
    ComputableInPolyTime (fun x : α × List Bool =>
      (machine.popStep^[c * ((input x.1).length + 1) ^ d]
        (FiniteConfig.init machine.initial (input x.1), x.2)).1.tapes.output)
      (encPair input encBits) encBits := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  have hcount : ComputableInPolyTime (fun x : α × List Bool =>
      c * ((input x.1).length + 1) ^ d) (encPair input encBits) encUnary :=
    (((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length input)).comp
        (ComputableInPolyTime.fst _ _)).of_enc_eq fun x => by simp
  have hinit : ComputableInPolyTime
      (fun x : α × List Bool =>
        (FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input x.1), x.2))
      (encPair input encBits) (encPair encFiniteConfig encBits) :=
    (ComputableInPolyTime.finiteConfig_init (by fun_prop) _).prod
      (ComputableInPolyTime.snd _ _)
  have hspace (x : α × List Bool) (i : ℕ) :
      FiniteConfig.SpaceBound (input x.1).length i 1
        (machine.popStep^[i] (FiniteConfig.init machine.initial (input x.1), x.2)).1 ∧
      (machine.popStep^[i] (FiniteConfig.init machine.initial (input x.1), x.2)).2.length ≤
        x.2.length := by
    induction i with
    | zero => exact ⟨FiniteConfig.spaceBound_init _ _ _, le_rfl⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply', fst_popStep]
      exact ⟨machine.spaceBound_answerStep (fun _ => _) ih.1,
        (machine.length_snd_popStep_le _).trans ih.2⟩
  have hbound : PolyBounded (fun x => (encPair input encBits x).length)
      (fun x => 2 * (cf * ((encPair input encBits x).length +
        c * ((encPair input encBits x).length + 1) ^ d + 1 + 1)) + 1 +
          (encPair input encBits x).length) := by growth_poly
  have hit := ComputableInPolyTime.iterate hcount hinit
    machine.computableInPolyTime_popStep hbound fun x i hi => by
      obtain ⟨h₁, h₂⟩ := hspace x i
      have hlen : (encPair input encBits x).length = 2 * (input x.1).length + 1 + x.2.length :=
        length_encPair x
      have hpow : c * ((input x.1).length + 1) ^ d ≤
          c * ((encPair input encBits x).length + 1) ^ d :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
      have hc : _ ≤ cf * ((encPair input encBits x).length +
          c * ((encPair input encBits x).length + 1) ^ d + 1 + 1) :=
        (hcf _ _ _ _ h₁).trans (Nat.mul_le_mul_left cf (by omega))
      rw [length_encPair, encBits_apply]; omega
  exact ComputableInPolyTime.comp
    (f := fun p : FiniteConfig k Bool Control Operation × List Bool => p.1.tapes.output)
    (by fun_prop) hit

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- The bits of the number with little-endian digits `l` are `l`, once both are padded with
`false`. -/
private theorem getD_bits_foldr_bit (l : List Bool) (i : ℕ) :
    (l.foldr Nat.bit 0).bits.getD i false = l.getD i false := by
  change (l.foldr Nat.bit 0).bits.getD i default = l.getD i default
  rw [List.getD_default_eq_getI, ← Nat.testBit_eq_inth]
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    cases i with
    | zero => simp
    | succ i => simpa [Nat.testBit_bit_succ] using ih i

variable {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop}

/-- **Few queries to any oracle give a polynomial-time solver.** A search problem in `FNP` solved
in polynomial time relative to some oracle language `O` with at most `r n` requests on instances of
encoded length `n`, where `2 ^ r n` is polynomially bounded, is in `FPSearch`: try every list of
`r n` answers, run the oracle program with the requests answered from the list, and keep an output
that the verifier accepts. -/
theorem mem_FPSearch_of_computableInPolyTimeWithOracleQueries_of_two_pow_le (hR : R ∈ FNP enc)
    {O : Set (List Bool)} {r : ℕ → ℕ} (P : Polynomial ℕ) (hr : ∀ n, 2 ^ r n ≤ P.eval n)
    {f : α → Option (List Bool)}
    (hf : ComputableInPolyTimeWithOracleQueries O r f enc (encOption encBits))
    (hsolve : SolvesSearch R f) : R ∈ FPSearch enc := by
  classical
  obtain ⟨-, V, hV, hRV⟩ := mem_FNP.mp hR
  obtain ⟨program, hcert, hprog⟩ := hf
  obtain ⟨k, Control, _, machine, c, d, hrun⟩ :=
    Probability.IsOraclePPTOn.exists_run_pure_false_stateM hcert
  -- the program run with the requests answered from a list
  let sim : α × List Bool → List Bool := fun x =>
    (machine.popStep^[c * ((enc x.1).length + 1) ^ d]
      (MultiTapeMachine.FiniteConfig.init machine.initial (enc x.1), x.2)).1.tapes.output
  have hsim : ComputableInPolyTime sim (encPair enc encBits) encBits :=
    machine.computableInPolyTime_popRun c d
  have hsim_eq (a : α) (s : List Bool) : sim (a, s) = encOption encBits
      ((OracleComp.interpret (m := StateM (List Bool)) OracleComp.popAnswer (program a)).run s).1 :=
    congrArg Prod.fst ((machine.run_interpret_popAnswer_run _ _ _).symm.trans
      (hrun a (List Bool) (fun q s => OracleComp.popAnswer q s) s))
  -- the candidate solution for the list of answers given by the bits of `j`
  let D : Decoder (encOption encBits) := Decoder.option Decoder.bits
  let cand : α × ℕ → Option (List Bool) := fun x => D.decode (sim (x.1, Nat.bits x.2))
  have hcand : ComputableInPolyTime cand (encPair enc encUnary) (encOption encBits) :=
    D.computableInPolyTime.comp (hsim.comp ((ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.natBits.comp
        (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)))))
  have hcand_eq (a : α) (j : ℕ) : cand (a, j) =
      ((OracleComp.interpret (m := StateM (List Bool)) OracleComp.popAnswer (program a)).run
        (Nat.bits j)).1 := by
    simp only [cand, hsim_eq, D.decode_enc]
  let ok : α × ℕ → Bool := fun x => (cand x).elim false fun w => V (x.1, w)
  have hok : ComputableInPolyTime ok (encPair enc encUnary) encBool :=
    ComputableInPolyTime.optionElimWithInput hcand (ComputableInPolyTime.const _)
      (hV.comp (((ComputableInPolyTime.fst _ _).comp
        (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)))
  let N : α → ℕ := fun a => P.eval (enc a).length
  let g : α → Option (List Bool) := fun a =>
    ((List.range (N a)).find? fun j => ok (a, j)).elim none fun j => cand (a, j)
  have hg : ComputableInPolyTime g enc (encOption encBits) :=
    ComputableInPolyTime.optionElimWithInput
      (ComputableInPolyTime.findWithInput
        (ComputableInPolyTime.range.comp
          ((ComputableInPolyTime.unary_eval P).comp (ComputableInPolyTime.encoding_length enc)))
        hok)
      (ComputableInPolyTime.const _) hcand
  refine mem_FPSearch.mpr ⟨hR, g, hg, fun a => ⟨fun w hw => ?_, fun hw ha => ?_⟩⟩
  · rcases hj : (List.range (N a)).find? (fun j => ok (a, j)) with _ | j <;>
      simp only [g, hj, Option.elim_none, reduceCtorEq, Option.elim_some] at hw
    exact (hRV a w).2 (by simpa only [ok, hw, Option.elim_some] using List.find?_some hj)
  · -- the true answers, as the bits of a number below `N a`
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, f a = some w₀ := Option.ne_none_iff_exists'.mp
      fun h => (hsolve a).2 h ha
    let answers := (OracleComp.queriesWith (languageOracle O) (program a)).map
      fun q => decide (q.2 ∈ O)
    have hlt : answers.foldr Nat.bit 0 < N a :=
      (Nat.foldr_bit_lt answers).trans_le ((Nat.pow_le_pow_right (by omega)
        (by simpa [answers] using (hprog a).2)).trans (hr _))
    have hcand_true : cand (a, answers.foldr Nat.bit 0) = some w₀ := by
      rw [hcand_eq, OracleComp.run_interpret_popAnswer_congr (program a) (s' := answers ++ [])
        (fun i => by rw [getD_bits_foldr_bit, List.append_nil]),
        OracleComp.run_interpret_popAnswer, (hprog a).1, hw₀]
    have hok_true : ok (a, answers.foldr Nat.bit 0) = true := by
      simpa only [ok, hcand_true, Option.elim_some] using (hRV a w₀).1 ((hsolve a).1 w₀ hw₀)
    rcases hj : (List.range (N a)).find? (fun j => ok (a, j)) with _ | j
    · exact List.find?_eq_none.mp hj _ (List.mem_range.mpr hlt) hok_true
    · simp only [g, hj, Option.elim_some] at hw
      simpa [ok, hw] using List.find?_some hj

/-- **Logarithmically many queries do not help**
[Goldreich, Exercise 2.10][Goldreich2006DraftR1]. A search problem in `PC` (`FNP`) solved in
polynomial time relative to any oracle language `O` with at most `c log₂ n + c` requests on
instances of encoded length `n` is in `PF` (`FPSearch`). Contrapositively, if `R ∈ PC \ PF`, no
such oracle machine solves the search problem of `R`, whatever decision oracle it consults, for
any constant `c`: it makes more than logarithmically many requests. -/
theorem mem_FPSearch_of_computableInPolyTimeWithOracleQueries_log (hR : R ∈ FNP enc)
    {O : Set (List Bool)} {c : ℕ} {f : α → Option (List Bool)}
    (hf : ComputableInPolyTimeWithOracleQueries O (fun n => c * Nat.log 2 n + c) f enc
      (encOption encBits))
    (hsolve : SolvesSearch R f) : R ∈ FPSearch enc := by
  refine mem_FPSearch_of_computableInPolyTimeWithOracleQueries_of_two_pow_le hR
    (Polynomial.C (2 ^ c) * (Polynomial.X + 1) ^ c) (fun n => ?_) hf hsolve
  have hlog : 2 ^ Nat.log 2 n ≤ n + 1 :=
    if hn : n = 0 then by simp [hn] else (Nat.pow_log_le_self 2 hn).trans (Nat.le_succ n)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, pow_add, mul_comm c, pow_mul, mul_comm (2 ^ c)]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlog c)

end Cslib.Complexity
