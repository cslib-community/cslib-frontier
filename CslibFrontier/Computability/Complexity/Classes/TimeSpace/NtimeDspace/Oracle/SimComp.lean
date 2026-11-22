/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.SimStep
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# The parts of the simulation are computable in linear space

The step of the simulation of an oracle machine
(`Cslib.Complexity.NtimeDspace.Oracle.OracleTM.simNext`), the symbol
it writes (`simEmit`), the position of the simulated input head, and the halting test are
computable within space linear in the encoded simulation state, if the oracle is decidable within
linear space. Each universal step is Complexitylib's `Turing.MultiTapeTM.Universal.stepWith_inO`
on a fixed description.

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.OracleTM.simNext_inSpace`, `.simEmit_inSpace`,
`.simQuery_inSpace`,
  `.simHalted_inSpace`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
    _root_.Turing.MultiTapeTM.ComputableInSpace

/-- The encoding of the simulation states: the universal configuration and the query tape. -/
abbrev encSim : SCfg × List Bool ↪ List Bool := encPair eCfg encBits

/-- The encoding of the arguments of a step: the state and the bit read. -/
abbrev encSimIn : (SCfg × List Bool) × Option Bool ↪ List Bool := encPair encSim (encOption encBool)

namespace OracleTM

variable {k : ℕ} {State : Type} [Fintype State] (M : OracleTM k State) (eS : State ↪ ℕ)
  (A : Set (List Bool))

/-- The linear bound on the arguments of a step. -/
abbrev LIn (p : (SCfg × List Bool) × Option Bool) : ℕ := (encSimIn p).length

lemma cfg_inSpace : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool => p.1.1) encSimIn
    eCfg LIn :=
  (fst encSim (encOption encBool)).fst'

lemma buf_inSpace : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool => p.1.2) encSimIn
    encBits LIn :=
  (fst encSim (encOption encBool)).snd'

lemma bit_inSpace : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool => p.2) encSimIn
    (encOption encBool) LIn :=
  snd encSim (encOption encBool)

lemma fields_inSpace {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f : α → SCfg}
    (h : ComputableInSpace f enc eCfg S) :
    ComputableInSpace (fun a => ((f a).state, (f a).inputPos, (f a).workTapes)) enc eCfgFields S :=
  h.of_enc_eq fun _ => rfl

lemma symOf_inSpace : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool =>
    symOf p.1.1 p.2) encSimIn eSym LIn := by
  have hpos := (fields_inSpace cfg_inSpace).snd'.fst'
  have hz := budget_comp_lin natIsZero (.refl _) hpos
  have hm := budget_finite (encC := eSym) (fun r : Option Bool => r.map eBit) bit_inSpace
  refine (budget_ite hz (budget_const none (.refl _)) hm).of_enc_eq fun p => ?_
  simp only [symOf]
  split_ifs <;> simp_all

lemma stepWith_inSpace (d : Desc) : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool =>
    stepWith d p.1.1 (symOf p.1.1 p.2)) encSimIn (encPair eCfg eSym) LIn := by
  have hctx : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool =>
      (((d, p.1.1), symOf p.1.1 p.2) : WCtx)) encSimIn eWCtx LIn :=
    budget_prod (budget_prod (budget_const d (.refl _)) cfg_inSpace) symOf_inSpace
  have hstep : ComputableInSpace (fun c : WCtx => stepWith c.desc c.cfg c.sym) eWCtx
      (encPair eCfg eSym) fun c => (eWCtx c).length := of_inO stepWith_inO
  have h := budget_comp_lin hstep (.refl _) hctx
  exact h

lemma flag_inSpace (d : Desc) : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool =>
    (stepWith d p.1.1 (symOf p.1.1 p.2)).2.isSome) encSimIn encBool LIn :=
  budget_comp_lin (of_inO (ComputableInDegree.isSome encUnary).inO_one) (.refl _)
    (stepWith_inSpace d).snd'

lemma bitOf_inSpace (d₁ d₀ : Desc) : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool =>
    bitOf (stepWith d₁ p.1.1 (symOf p.1.1 p.2)).2.isSome
      (stepWith d₀ p.1.1 (symOf p.1.1 p.2)).2.isSome) encSimIn encBits LIn :=
  budget_finite (encC := encBits) (fun q : Bool × Bool => bitOf q.1 q.2)
    (budget_prod (flag_inSpace d₁) (flag_inSpace d₀))

variable {A}

open scoped Classical in
/-- **The step of the simulation is computable in linear space**, given a decider for the oracle
within linear space. -/
theorem simNext_inSpace
    (hA : ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    ComputableInSpace (M.simNext eS A) encSimIn encSim LIn := by
  classical
  have hmem : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool => decide (p.1.2 ∈ A))
      encSimIn encBool LIn :=
    budget_comp_lin hA (.of_le fun _ => le_rfl) buf_inSpace
  have hask := budget_prod (encC := encBits) (budget_ite hmem
    (stepWith_inSpace (desc eS eBit (M.answerTM true))).fst'
    (stepWith_inSpace (desc eS eBit (M.answerTM false))).fst') (budget_const [] (.refl _))
  have happ : ComputableInSpace (fun p : (SCfg × List Bool) × Option Bool =>
      p.1.2 ++ bitOf (stepWith (desc eS eBit (M.outTM (querySym true))) p.1.1
        (symOf p.1.1 p.2)).2.isSome (stepWith (desc eS eBit (M.outTM (querySym false))) p.1.1
        (symOf p.1.1 p.2)).2.isSome) encSimIn encBits LIn :=
    (append buf_inSpace (bitOf_inSpace (desc eS eBit (M.outTM (querySym true)))
      (desc eS eBit (M.outTM (querySym false)))) (encD := encBits) fun _ => rfl).weaken
      (.add (.refl _) (.refl _))
  have hord := budget_prod (stepWith_inSpace (desc eS eBit M.plainTM)).fst' happ
  refine (budget_ite (flag_inSpace (desc eS eBit (M.outTM flagSym))) hask hord).of_enc_eq
    fun p => ?_
  simp only [simNext]
  split_ifs <;> simp_all

theorem simEmit_inSpace : ComputableInSpace (M.simEmit eS) encSimIn encBits LIn := by
  refine (budget_ite (flag_inSpace (desc eS eBit (M.outTM flagSym))) (budget_const [] (.refl _))
    (bitOf_inSpace (desc eS eBit (M.outTM (outSym true)))
      (desc eS eBit (M.outTM (outSym false))))).of_enc_eq fun p => ?_
  simp only [simEmit]

lemma simCfg_inSpace : ComputableInSpace (fun s : SCfg × List Bool => s.1) encSim eCfg
    fun s => (encSim s).length :=
  fst eCfg encBits

/-- The position of the input bit read by the simulation. -/
theorem simQuery_inSpace : ComputableInSpace (fun s : SCfg × List Bool => s.1.inputPos - 1) encSim
    encNat fun s => (encSim s).length :=
  budget_comp_lin natPred linear_succ (fields_inSpace simCfg_inSpace).snd'.fst'

/-- The halting test of the simulation. -/
theorem simHalted_inSpace : ComputableInSpace (fun s : SCfg × List Bool => s.1.state.isNone)
    encSim encBool fun s => (encSim s).length := by
  have h := budget_comp_lin (of_inO (ComputableInDegree.isSome encUnary).inO_one) (.refl _)
    (fields_inSpace simCfg_inSpace).fst'
  refine (budget_finite (encC := encBool) (fun b : Bool => !b) h).of_enc_eq fun s => ?_
  cases s.1.state <;> rfl

end OracleTM

end Cslib.Complexity.NtimeDspace.Oracle
