/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
public import CslibFrontier.Foundations.Computability.RecursiveInCode

/-!
# Relative computation of finite oracle machine runs

The ordinary work-tape update uses the primitive-recursive universal simulator. A local
instruction with a supplied membership answer is primitive recursive. Relative evaluation
iterates the encoded snapshots and searches for a halted configuration. In the simulation
an unused oracle answer does not affect ordinary instructions.

## Main results

* `OracleDesc.recursiveIn_eval`: partial evaluation of a finite machine is recursive in
  its Boolean membership oracle.
* `OracleDesc.exists_code_eval`: on every encoded input, the corresponding oracle code
  returns the encoded halted output, with the same domain of convergence.
* `OracleDesc.recursiveIn_evalUnary`: the machine can also be interpreted as a partial
  function on natural numbers via tally input and output.

This gives the machine-to-code direction. A code-to-machine compiler is a separate
milestone of [#6650](https://github.com/cslib-community/cslib-frontier/issues/6650).
-/

public section

namespace Turing.MultiTapeTM.Universal

namespace OracleInstruction

/-- Encode the step and query branches by a tagged sum of their fields. -/
def equivSum : OracleInstruction ≃ (Act × Bool) ⊕ (ℕ × ℕ) where
  toFun
    | .step action tally => .inl (action, tally)
    | .query yes no => .inr (yes, no)
  invFun
    | .inl (action, tally) => .step action tally
    | .inr (yes, no) => .query yes no
  left_inv i := by cases i <;> rfl
  right_inv i := by rcases i with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

instance : Primcodable OracleInstruction :=
  Primcodable.ofEquiv _ equivSum

end OracleInstruction

namespace OracleDesc

namespace Config

/-- Encode a snapshot by its ordinary configuration, query tally and output word. -/
def equivTuple : Config ≃ SCfg × ℕ × List ℕ where
  toFun c := (c.ordinary, c.queryLength, c.output)
  invFun | (ordinary, query, out) => ⟨ordinary, query, out⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance : Primcodable Config :=
  Primcodable.ofEquiv _ equivTuple

private theorem primrec_ordinary : Primrec Config.ordinary :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivTuple))

private theorem primrec_queryLength : Primrec Config.queryLength :=
  (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := equivTuple))

private theorem primrec_output : Primrec Config.output :=
  (Primrec.snd.comp Primrec.snd).comp (Primrec.of_equiv (e := equivTuple))

private theorem primrec_mk {α : Type*} [Primcodable α]
    {c : α → SCfg} {q : α → ℕ} {o : α → List ℕ}
    (hc : Primrec c) (hq : Primrec q) (ho : Primrec o) :
    Primrec fun a => (⟨c a, q a, o a⟩ : Config) :=
  (Primrec.of_equiv_symm (e := equivTuple)).comp (hc.pair (hq.pair ho))

end Config

private theorem primrec_setState {α : Type*} [Primcodable α]
    {c : α → SCfg} {s : α → Option ℕ} (hc : Primrec c) (hs : Primrec s) :
    Primrec fun a => { c a with state := s a } :=
  primrec_scfg_mk hs (primrec_scfg_inputPos.comp hc) (primrec_scfg_workTapes.comp hc)

private abbrev StepInput := List ℕ × Config × Bool

private theorem primrec_stepAction :
    Primrec₂ fun (p : StepInput) (a : Act × Bool) =>
      (⟨a.1.apply p.1 p.2.1.ordinary, p.2.1.queryLength + a.2.toNat,
        p.2.1.output ++ a.1.output.toList⟩ : Config) := by
  let x : Primrec fun p : StepInput × (Act × Bool) => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  let c : Primrec fun p : StepInput × (Act × Bool) => p.1.2.1 :=
    (Primrec.fst.comp Primrec.snd).comp Primrec.fst
  let a : Primrec fun p : StepInput × (Act × Bool) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  let tally : Primrec fun p : StepInput × (Act × Bool) => p.2.2.toNat :=
    (Primrec.dom_bool Bool.toNat).comp (Primrec.snd.comp Primrec.snd)
  exact Primrec₂.mk (Config.primrec_mk
    (primrec_act_apply.comp (a.pair (x.pair (Config.primrec_ordinary.comp c))))
    (Primrec.nat_add.comp (Config.primrec_queryLength.comp c) tally)
    (primrec_output_append.comp (Config.primrec_output.comp c) (primrec_act_output.comp a)))

private theorem primrec_queryAction :
    Primrec₂ fun (p : StepInput) (q : ℕ × ℕ) =>
      (⟨{ p.2.1.ordinary with state := some (bif p.2.2 then q.1 else q.2) }, 0,
        p.2.1.output⟩ : Config) := by
  let c : Primrec fun p : StepInput × (ℕ × ℕ) => p.1.2.1 :=
    (Primrec.fst.comp Primrec.snd).comp Primrec.fst
  let b : Primrec fun p : StepInput × (ℕ × ℕ) => p.1.2.2 :=
    (Primrec.snd.comp Primrec.snd).comp Primrec.fst
  exact Primrec₂.mk (Config.primrec_mk
    (primrec_setState (Config.primrec_ordinary.comp c)
      (Primrec.option_some.comp
        (Primrec.cond b (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))
    (Primrec.const 0) (Config.primrec_output.comp c))

/-- One oracle-machine instruction with a supplied membership answer is primitive recursive.
The finite transition table is fixed. -/
theorem primrec_stepWith (M : OracleDesc) :
    Primrec fun p : List ℕ × Config × Bool =>
      let (x, cfg, answer) := p
      M.stepWith x cfg answer := by
  let c : Primrec fun p : StepInput => p.2.1 := Primrec.fst.comp Primrec.snd
  have hhalt : Primrec fun p : StepInput =>
      { p.2.1 with ordinary := { p.2.1.ordinary with state := none } } :=
    Config.primrec_mk (primrec_setState (Config.primrec_ordinary.comp c) (Primrec.const none))
      (Config.primrec_queryLength.comp c) (Config.primrec_output.comp c)
  have hact : Primrec₂ fun (p : StepInput) (a : Key × OracleInstruction) =>
      p.2.1.applyInstruction p.1 p.2.2 a.2 := by
    refine Primrec₂.mk ((Primrec.sumCasesOn
      ((Primrec.of_equiv (e := OracleInstruction.equivSum)).comp (Primrec.snd.comp Primrec.snd))
      (primrec_stepAction.comp₂ (Primrec.fst.comp Primrec.fst).to₂ Primrec₂.right)
      (primrec_queryAction.comp₂ (Primrec.fst.comp Primrec.fst).to₂ Primrec₂.right)).of_eq ?_)
    rintro ⟨p, _, a⟩
    cases a <;> rfl
  have hsome : Primrec₂ fun (p : StepInput) (q : ℕ) =>
      match M.table.find? (·.1 = p.2.1.ordinary.key p.1 q) with
      | none => { p.2.1 with ordinary := { p.2.1.ordinary with state := none } }
      | some a => p.2.1.applyInstruction p.1 p.2.2 a.2 := by
    let key : Primrec fun p : StepInput × ℕ => p.1.2.1.ordinary.key p.1.1 p.2 :=
      primrec_scfg_key.comp
        ((Config.primrec_ordinary.comp (c.comp Primrec.fst)).pair
          ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
    refine Primrec₂.mk ((Primrec.option_casesOn
      (primrec_find_table.comp (Primrec.const M.table) key)
      (hhalt.comp Primrec.fst)
      (hact.comp₂ (Primrec.fst.comp Primrec.fst).to₂ Primrec₂.right)).of_eq ?_)
    intro p
    cases M.table.find? (·.1 = p.1.2.1.ordinary.key p.1.1 p.2) <;> rfl
  refine (Primrec.option_casesOn (primrec_scfg_state.comp (Config.primrec_ordinary.comp c))
    c hsome).of_eq ?_
  rintro ⟨x, cfg, answer⟩
  change _ = M.stepWith x cfg answer
  unfold stepWith
  cases cfg.ordinary.state with
  | none => rfl
  | some q => cases M.table.find? (·.1 = cfg.ordinary.key x q) <;> rfl

private abbrev oracleFunction (oracle : ℕ → Bool) : ℕ →. ℕ :=
  fun n => Part.some (oracle n).toNat

private def HasCode (f : (ℕ → Bool) → ℕ →. ℕ) : Prop :=
  ∃ c : Nat.RecursiveIn.Code, ∀ oracle, c.eval (oracleFunction oracle) = f oracle

namespace HasCode

open Nat.RecursiveIn (Code)

private theorem of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    HasCode (fun _ n => Part.some (f n)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Nat.Partrec.of_primrec hf)
  exact ⟨Code.ofPartrec c, fun oracle => (Code.eval_ofPartrec _ _).trans hc⟩

private theorem oracle : HasCode oracleFunction :=
  ⟨.oracle, fun _ => rfl⟩

private theorem comp {f h : (ℕ → Bool) → ℕ →. ℕ} (hf : HasCode f) (hh : HasCode h) :
    HasCode (fun oracle n => h oracle n >>= f oracle) := by
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨ch, hch⟩ := hh
  exact ⟨.comp cf ch, fun oracle => by rw [Code.eval, hcf, hch]⟩

private theorem pair {f h : (ℕ → Bool) → ℕ →. ℕ} (hf : HasCode f) (hh : HasCode h) :
    HasCode (fun oracle n => Nat.pair <$> f oracle n <*> h oracle n) := by
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨ch, hch⟩ := hh
  exact ⟨.pair cf ch, fun oracle => by rw [Code.eval, hcf, hch]⟩

private theorem prec {f h : (ℕ → Bool) → ℕ →. ℕ} (hf : HasCode f) (hh : HasCode h) :
    HasCode (fun oracle p =>
      let (a, n) := Nat.unpair p
      n.rec (f oracle a) fun y ih => do
        let i ← ih
        h oracle (Nat.pair a (Nat.pair y i))) := by
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨ch, hch⟩ := hh
  exact ⟨.prec cf ch, fun oracle => by rw [Code.eval, hcf, hch]⟩

private theorem rfind {f : (ℕ → Bool) → ℕ →. ℕ} (hf : HasCode f) :
    HasCode (fun oracle a =>
      Nat.rfind fun n => (fun m => m = 0) <$> f oracle (Nat.pair a n)) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨Code.rfind c, fun oracle => by
    funext a
    rw [Code.eval_rfind, hc]⟩

private theorem of_eq {f h : (ℕ → Bool) → ℕ →. ℕ} (hf : HasCode f)
    (hh : ∀ oracle n, f oracle n = h oracle n) : HasCode h := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun oracle => (hc oracle).trans (funext (hh oracle))⟩

private theorem recursiveIn {f : (ℕ → Bool) → ℕ →. ℕ} (hf : HasCode f)
    (oracle : ℕ → Bool) : Nat.RecursiveIn {oracleFunction oracle} (f oracle) := by
  obtain ⟨c, hc⟩ := hf
  exact Code.exists_code.mpr ⟨c, hc oracle⟩

end HasCode

private abbrev RunState := List ℕ × Config

private def decodeRunState (M : OracleDesc) (n : ℕ) : RunState :=
  (Encodable.decode n).getD ([], M.init)

private theorem primrec_decodeRunState (M : OracleDesc) : Primrec (decodeRunState M) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([], M.init))

private theorem hasCode_encodedStep (M : OracleDesc) :
    HasCode (fun oracle n =>
      let (x, c) := decodeRunState M n
      Part.some (Encodable.encode (x, M.step oracle x c))) := by
  let getState := primrec_decodeRunState M
  have hrequest : Nat.Primrec fun n => (decodeRunState M n).2.queryLength :=
    Primrec.nat_iff.mp (Config.primrec_queryLength.comp (Primrec.snd.comp getState))
  let unpack : Primrec fun p : ℕ × ℕ => decodeRunState M p.1 := getState.comp Primrec.fst
  let answer : Primrec fun p : ℕ × ℕ => decide (p.2 = 1) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 1)).decide
  have hnext : Primrec fun p : ℕ × ℕ =>
      Encodable.encode ((decodeRunState M p.1).1,
        M.stepWith (decodeRunState M p.1).1 (decodeRunState M p.1).2 (decide (p.2 = 1))) :=
    Primrec.encode.comp ((Primrec.fst.comp unpack).pair
      ((primrec_stepWith M).comp ((Primrec.fst.comp unpack).pair
        ((Primrec.snd.comp unpack).pair answer))))
  have hnat := Primrec.nat_iff.mp (hnext.comp Primrec.unpair)
  have hcall := HasCode.oracle.comp (HasCode.of_primrec hrequest)
  refine ((HasCode.of_primrec hnat).comp
    ((HasCode.of_primrec Nat.Primrec.id).pair hcall)).of_eq ?_
  intro oracle n
  simp only [id_eq, ← Part.pure_eq_some, pure_bind, map_pure, pure_seq, Nat.unpair_pair]
  cases hb : oracle (decodeRunState M n).2.queryLength <;> simp [step, hb]

private def decodeInput (n : ℕ) : List ℕ := (Encodable.decode n).getD []

private theorem primrec_decodeInput : Primrec decodeInput :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem hasCode_encodedRun (M : OracleDesc) :
    HasCode (fun oracle p =>
      let (n, t) := p.unpair
      let x := decodeInput n
      Part.some (Encodable.encode (x, M.runFor oracle x t))) := by
  have hinit : Nat.Primrec fun n => Encodable.encode (decodeInput n, M.init) :=
    Primrec.nat_iff.mp (Primrec.encode.comp (primrec_decodeInput.pair (Primrec.const M.init)))
  have hproject : Nat.Primrec fun p : ℕ => p.unpair.2.unpair.2 :=
    Primrec.nat_iff.mp ((Primrec.snd.comp Primrec.unpair).comp
      (Primrec.snd.comp Primrec.unpair))
  refine (HasCode.prec (HasCode.of_primrec hinit)
    ((hasCode_encodedStep M).comp (HasCode.of_primrec hproject))).of_eq ?_
  intro oracle p
  rcases hp : p.unpair with ⟨n, t⟩
  clear hp p
  dsimp only
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Nat.unpair_pair, Part.bind_eq_bind, Part.bind_some] at ih ⊢
    rw [ih]
    simp [decodeRunState, runFor, Function.iterate_succ_apply']

/-- The partial output of the machine. The time search stops at its first halted snapshot. -/
@[expose] def eval (M : OracleDesc) (oracle : ℕ → Bool) (x : List ℕ) : Part (List ℕ) :=
  (Nat.rfind fun t => Part.some (M.runFor oracle x t).ordinary.state.isNone).map
    fun t => (M.runFor oracle x t).output

private theorem runFor_eq_after_halt (M : OracleDesc) (oracle : ℕ → Bool) (x : List ℕ)
    {m n : ℕ} (hle : m ≤ n) (hhalt : (M.runFor oracle x m).ordinary.state = none) :
    M.runFor oracle x n = M.runFor oracle x m := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_comm m extra, runFor, Function.iterate_add_apply, ← runFor]
  exact Function.iterate_fixed (M.step_halted oracle x hhalt) extra

/-- A word is returned exactly when a finite run halts with that output. -/
theorem mem_eval_iff (M : OracleDesc) (oracle : ℕ → Bool) (x out : List ℕ) :
    out ∈ M.eval oracle x ↔ ∃ t, (M.runFor oracle x t).ordinary.state = none ∧
      (M.runFor oracle x t).output = out := by
  rw [eval, Part.mem_map_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, by simpa using Nat.rfind_spec ht, rfl⟩
  · rintro ⟨t, ht, ho⟩
    obtain ⟨m, hm, hle⟩ :=
      Nat.rfind_min' (p := fun i => (M.runFor oracle x i).ordinary.state.isNone) (m := t)
        (by simp [ht])
    have hhalt : (M.runFor oracle x m).ordinary.state = none := by
      simpa using Nat.rfind_spec hm
    exact ⟨m, hm, by simpa [M.runFor_eq_after_halt oracle x hle hhalt] using ho⟩


private theorem hasCode_haltTime (M : OracleDesc) :
    HasCode (fun oracle n =>
      Nat.rfind fun t => Part.some (M.runFor oracle (decodeInput n) t).ordinary.state.isNone) := by
  have hflag : Nat.Primrec fun p =>
      (decodeRunState M p).2.ordinary.state.isSome.toNat :=
    Primrec.nat_iff.mp ((Primrec.dom_bool Bool.toNat).comp (Primrec.option_isSome.comp
      (primrec_scfg_state.comp (Config.primrec_ordinary.comp
        (Primrec.snd.comp (primrec_decodeRunState M))))))
  refine (HasCode.rfind ((HasCode.of_primrec hflag).comp (hasCode_encodedRun M))).of_eq ?_
  intro oracle n
  congr 1
  funext t
  simp only [Nat.unpair_pair, Part.bind_eq_bind, Part.bind_some,
    decodeRunState, Encodable.encodek, Option.getD_some, Part.map_eq_map, Part.map_some]
  cases (M.runFor oracle (decodeInput n) t).ordinary.state <;> rfl

private theorem hasCode_evalEncoded (M : OracleDesc) :
    HasCode (fun oracle n =>
      (M.eval oracle (decodeInput n)).map Encodable.encode) := by
  have hout : Nat.Primrec fun n => Encodable.encode (decodeRunState M n).2.output :=
    Primrec.nat_iff.mp (Primrec.encode.comp
      (Config.primrec_output.comp (Primrec.snd.comp (primrec_decodeRunState M))))
  have hrun := (HasCode.of_primrec hout).comp (hasCode_encodedRun M)
  refine (hrun.comp ((HasCode.of_primrec Nat.Primrec.id).pair (hasCode_haltTime M))).of_eq ?_
  intro oracle n
  simp only [eval, Part.map_map, decodeRunState, Part.bind_some_eq_map, Function.comp_def,
    id_eq, Part.map_eq_map, Part.map_some, Encodable.encode_prod_val, Part.bind_eq_bind]
  rw [← Part.pure_eq_some (Nat.pair n), pure_seq, Part.map_eq_map, Part.map_map]
  simp [Function.comp_def]

/-- Relative evaluation of the finite oracle machine is partial recursive in its membership
oracle. The computation returns the entire halted output word and diverges when the machine
never halts. -/
theorem recursiveIn_eval (M : OracleDesc) (oracle : ℕ → Bool) :
    RecursiveIn {fun n => Part.some (oracle n).toNat} (M.eval oracle) := by
  change RecursiveIn {oracleFunction oracle} (M.eval oracle)
  simpa [RecursiveIn, decodeInput] using (hasCode_evalEncoded M).recursiveIn oracle


/-- Compile a finite machine to a single code that works with every membership oracle. -/
theorem exists_code_eval (M : OracleDesc) :
    ∃ c : Nat.RecursiveIn.Code, ∀ (oracle : ℕ → Bool) (x : List ℕ),
      c.eval (fun n => Part.some (oracle n).toNat) (Encodable.encode x) =
        (M.eval oracle x).map Encodable.encode := by
  obtain ⟨c, hc⟩ := hasCode_evalEncoded M
  refine ⟨c, fun oracle x => ?_⟩
  simpa [decodeInput] using congrFun (hc oracle) (Encodable.encode x)

/-- Evaluate a natural input on a tally tape and read the output length. -/
@[expose] def evalUnary (M : OracleDesc) (oracle : ℕ → Bool) (n : ℕ) : Part ℕ :=
  (M.eval oracle (List.replicate n 1)).map List.length

/-- A machine on unary natural inputs and outputs computes a partial recursive function
relative to the membership oracle. -/
theorem recursiveIn_evalUnary (M : OracleDesc) (oracle : ℕ → Bool) :
    Nat.RecursiveIn {fun n => Part.some (oracle n).toNat} (M.evalUnary oracle) := by
  have hin : Primrec fun n : ℕ => List.replicate n (1 : ℕ) :=
    (Primrec.list_map Primrec.list_range (Primrec.const 1).to₂).of_eq fun n => by simp
  have hinput := (Primrec.nat_iff.mp (Primrec.encode.comp hin)).recursiveIn
    (O := {oracleFunction oracle})
  have houtput := (Primrec.nat_iff.mp (Primrec.list_length.comp primrec_decodeInput)).recursiveIn
    (O := {oracleFunction oracle})
  change Nat.RecursiveIn {oracleFunction oracle} _
  refine (houtput.comp (((hasCode_evalEncoded M).recursiveIn oracle).comp hinput)).of_eq ?_
  intro n
  simp [decodeInput, evalUnary, Part.bind_some_eq_map, Part.map_map, Function.comp_def]

end OracleDesc

end Turing.MultiTapeTM.Universal
