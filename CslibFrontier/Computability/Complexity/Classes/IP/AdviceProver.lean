/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.IP.OptimalProver
public import CslibFrontier.Computability.Complexity.Classes.IP.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Padding
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm

/-!
# Interactive proofs with a prover computable from short advice

A deterministic prover that answers every message `q`, after the history `h` of the interaction,
with `G (w, (h, q))`, for a polynomial-time function `G` and a short advice word `w`, can be
replaced by Merlin sending `w`: Arthur runs the verifier himself, keeps the history, and answers
its messages by `G`. If the verifier is sound against every prover, so against the prover of every
advice word, this gives a Merlin–Arthur proof system [Babai][Babai1985],
[Arora and Barak, Section 8.2][AroraBarak09].

Fixing the coins `r` of the realizing machine of the verifier
(`Cslib.Probability.IsOraclePPTOn`), the run against the deterministic prover
`Cslib.Complexity.Prover.ofHistoryFun g` is a deterministic fold of the machine over the coins in
which every message is answered by `g` of the history, and the history grows by the message and
its reply (`Cslib.Complexity.Interaction.directRunState`). The acceptance probability against the
prover is the fraction of coin strings on which it accepts
(`Cslib.Complexity.Interaction.acceptProb_ofHistoryFun`). The fold is polynomial-time when `G` is
and the replies are truncated to a polynomial length
(`Cslib.Complexity.Interaction.computableInPolyTime_directRunState`). The theorem assumes that the
honest replies are no longer, so that the truncation changes nothing for them, while for every
other advice word Arthur runs against the truncating prover, which soundness covers. Merlin's
proof in `MA` has a fixed length: it is the advice, framed and padded to a length determined by
the bound on its length (`Cslib.BitString.padWord`).

## Main definitions

* `Cslib.Complexity.Interaction.directRunState`: the deterministic replay of the machine against
  such a prover.

## Main results

* `Cslib.Complexity.Interaction.acceptProb_ofHistoryFun`: acceptance against such a prover is a
  count of coin strings.
* `Cslib.Complexity.mem_MA_of_adviceProver`: an interactive proof whose honest prover is
  computable from short advice puts the problem in `MA`.

## References

* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability

namespace Interaction

open _root_.Turing _root_.Turing.MultiTapeTM

section Direct

variable {k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control Unit)

variable (k Control) in
/-- The state of the replay against a history-dependent prover: the configuration and the history
of messages and replies. -/
abbrev AdviceState := MultiTapeMachine.FiniteConfig k Bool Control Unit × History

/-- What an instruction of a machine does to a configuration and a history when the prover answers
every message `m` after `h` with `g h m`, the machine reading the first `t` bits of the reply. -/
def directBranch (g : History → List Bool → List Bool) (t : ℕ) :
    Option (MultiTapeMachine.Action k Bool Control Unit) → AdviceState k Control →
      AdviceState k Control
  | none, s => s
  | some (.step action symbol move), s => (s.1.step action symbol move, s.2)
  | some (.query op next), s =>
    (s.1.receive op next ((g s.2 (s.1.channels op).1).take t),
      s.2 ++ [((s.1.channels op).1, g s.2 (s.1.channels op).1)])

/-- One instruction of `M` with the coin `b`, answering messages by `g`. -/
def directStep (g : History → List Bool → List Bool) (t : ℕ) (s : AdviceState k Control)
    (b : Bool) : AdviceState k Control :=
  directBranch g t (instruction M s.1 b) s

/-- The configuration and history of `M` on the input `x` with the coins `r` against the prover
answering every message `m` after `h` by `g h m`: one instruction per coin. -/
def directRunState (g : History → List Bool → List Bool) (x r : List Bool) :
    AdviceState k Control :=
  r.foldl (directStep M g r.length) (MultiTapeMachine.FiniteConfig.init M.initial x, [])

/-- The final configuration of `directRunState`. -/
def directRun (g : History → List Bool → List Bool) (x r : List Bool) :
    MultiTapeMachine.FiniteConfig k Bool Control Unit :=
  (directRunState M g x r).1

/-- The handler of the prover `ofHistoryFun g`. -/
private noncomputable abbrev histHandler (g : History → List Bool → List Bool) :
    Unit × List Bool → StateT History PMF (List Bool) :=
  fun q h => PMF.pure (g h q.2, h ++ [(q.2, g h q.2)])

/-- An instruction with a fixed coin against `ofHistoryFun g` is `directStep`. -/
private theorem run_coinStep_ofHistoryFun (g : History → List Bool → List Bool) (t : ℕ)
    (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) (h : History) (b : Bool) :
    (OracleComp.interpret (histHandler g) (coinStep M t cfg b)).run h =
      PMF.pure (directStep M g t (cfg, h) b) := by
  unfold coinStep MultiTapeMachine.finiteStep directStep instruction
  rcases hs : cfg.tapes.state with _ | c
  · simp only [Option.map_none, directBranch, interp_norm, pmf_norm]
  · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      ⟨action, symbol, move⟩ | ⟨op, next⟩
    · simp only [Option.map_some, htr, directBranch, interp_norm, pmf_norm, map_pure,
        pure_bind]
    · simp only [Option.map_some, htr, directBranch, interp_norm, pmf_norm, map_pure,
        pure_bind, bind_map_left]
      exact PMF.pure_bind
        (g h (cfg.channels op).1, h ++ [((cfg.channels op).1, g h (cfg.channels op).1)])
        (fun p => PMF.pure (cfg.receive op next (List.take t p.1), p.2))

/-- The instructions with fixed coins against `ofHistoryFun g` are the fold of `directStep`. -/
private theorem run_foldlM_ofHistoryFun (g : History → List Bool → List Bool) (t : ℕ)
    (r : List Bool) (cfg : MultiTapeMachine.FiniteConfig k Bool Control Unit) (h : History) :
    (OracleComp.interpret (histHandler g) (r.foldlM (coinStep M t) cfg)).run h =
      PMF.pure (r.foldl (directStep M g t) (cfg, h)) := by
  induction r generalizing cfg h with
  | nil => simp only [List.foldlM_nil, List.foldl_nil, interp_norm, pmf_norm]
  | cons b r ih =>
    simp only [List.foldlM_cons, List.foldl_cons, interp_norm, pmf_norm,
      run_coinStep_ofHistoryFun, PMF.pure_bind, ih]

/-- The program of fixed coins is accepted by `ofHistoryFun g` exactly when `directRun` outputs
`[true]`. -/
theorem acceptFrom_ofHistoryFun_coinProgram (g : History → List Bool → List Bool) {t : ℕ}
    (x r : List Bool) (hr : r.length = t) :
    acceptFrom (Prover.ofHistoryFun g) [] (some (coinProgram M t x r)) =
      if (directRun M g x r).tapes.output = [true] then 1 else 0 := by
  subst hr
  simp only [acceptFrom, coinProgram, interp_norm, pmf_norm, run_foldlM_ofHistoryFun,
    directRun, directRunState, PMF.pure_map, PMF.pure_apply]
  by_cases h : (List.foldl (directStep M g r.length) (MultiTapeMachine.FiniteConfig.init
      M.initial x, []) r).1.tapes.output = [true] <;> simp [h]

/-- **Acceptance against `ofHistoryFun g` counts coin strings.** If the verifier `V` is realized
by the run of `M` under the clock `t`, then its acceptance probability against the prover
answering every message `m` after `h` by `g h m` is the fraction of the coin strings of length `t`
on which `directRun` accepts. -/
theorem acceptProb_ofHistoryFun {V : WordOracleComp Unit Bool} {t : ℕ} {x : List Bool}
    (hV : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (encBool <$> V) s =
      ProbOracleComp.runWith oracle (M.runOracle t x) s) (g : History → List Bool → List Bool) :
    acceptProb V (Prover.ofHistoryFun g) =
      ((Finset.univ.filter fun r : Fin t → Bool =>
        (directRun M g x (List.ofFn r)).tapes.output = [true]).card : ENNReal) / (2 ^ t : ℕ) := by
  rw [acceptProb_eq_sum M (by simpa only [ProbOracleComp.runWith_eq_run_interpret] using hV)]
  simp only [acceptFrom_ofHistoryFun_coinProgram M g x _ List.length_ofFn]
  rw [Finset.sum_boole, ENNReal.div_eq_inv_mul]
  push_cast
  rfl

/-! ### The replay is polynomial-time -/

section PolyTime

open ComputableInPolyTime

/-- The invariant of the replay after `i` instructions: bounded storage, and a history of at most
`i` entries whose messages are at most `i` bits long and whose replies are at most `R` bits
long. -/
private def DirectInv (n i t R : ℕ) (s : AdviceState k Control) : Prop :=
  MultiTapeMachine.FiniteConfig.SpaceBound n i t s.1 ∧ s.2.length ≤ i ∧
    ∀ e ∈ s.2, e.1.length ≤ i ∧ e.2.length ≤ R

omit M in
/-- The invariant holds at the start. -/
private theorem directInv_init (t R : ℕ) (state : Control) (input : List Bool) :
    DirectInv (k := k) input.length 0 t R
      (MultiTapeMachine.FiniteConfig.init (Oracle := Unit) state input, []) :=
  ⟨MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _, le_rfl, nofun⟩

/-- An instruction preserves the invariant, whenever the replies are at most `R` bits long. -/
private theorem directStep_inv {n i t R : ℕ} {s : AdviceState k Control}
    (g : History → List Bool → List Bool) (hg : ∀ h q, (g h q).length ≤ R)
    (hs : DirectInv n i t R s) (b : Bool) : DirectInv n (i + 1) t R (directStep M g t s b) := by
  obtain ⟨cfg, h⟩ := s
  obtain ⟨hspace, hlen, hent⟩ := hs
  unfold directStep instruction
  rcases hst : cfg.tapes.state with _ | c
  · simp only [Option.map_none, directBranch]
    exact ⟨hspace.mono le_rfl (by lia) le_rfl, by lia,
      fun e he => ⟨(hent e he).1.trans (by lia), (hent e he).2⟩⟩
  · rcases htr : M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      ⟨action, symbol, move⟩ | ⟨op, next⟩
    · simp only [Option.map_some, htr, directBranch]
      exact ⟨hspace.step action symbol move, by lia,
        fun e he => ⟨(hent e he).1.trans (by lia), (hent e he).2⟩⟩
    · simp only [Option.map_some, htr, directBranch]
      refine ⟨hspace.receive op next _ (List.length_take_le _ _), by simp; lia, ?_⟩
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact ⟨(hent e he).1.trans (by lia), (hent e he).2⟩
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨(hspace.query op).trans (by lia), hg _ _⟩

variable [Finite Control] {G : List Bool × (History × List Bool) → List Bool}
  (hG : ComputableInPolyTime G (encReplyInput encBits) encBits)
include hG

/-- A step of the replay is polynomial-time, given the time, the advice and the reply length. -/
private theorem computableInPolyTime_directStep :
    ComputableInPolyTime
      (fun p : ((ℕ × List Bool × ℕ) × AdviceState k Control) × Bool =>
        directStep M (fun h q => (G (p.1.1.2.1, (h, q))).take p.1.1.2.2) p.1.1.1 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encPair encBits encUnary))
        (encPair encFiniteConfig encHistory)) encBool) (encPair encFiniteConfig encHistory) := by
  unfold directStep
  refine finite_cases
    (tag := fun p : ((ℕ × List Bool × ℕ) × AdviceState k Control) × Bool =>
      instruction M p.1.2.1 p.2)
    (branch := fun tag p => directBranch (fun h q => (G (p.1.1.2.1, (h, q))).take p.1.1.2.2)
      p.1.1.1 tag p.1.2)
    (tagEncoding := encFinite (Option (MultiTapeMachine.Action k Bool Control Unit))) ?_ ?_
  · have h := computableInPolyTime_instruction M
    fun_prop
  · rintro (_ | ⟨action, symbol, move⟩ | ⟨op, next⟩)
    · simp only [directBranch]
      fun_prop
    · simp only [directBranch]
      fun_prop
    · simp only [directBranch]
      fun_prop

/-- **The replay is polynomial-time** in the input, the coins and the advice, when the replies are
truncated to `ρ (|x|)` bits for a polynomial `ρ`. -/
theorem computableInPolyTime_directRunState (ρ : Polynomial ℕ) :
    ComputableInPolyTime (fun p : List Bool × List Bool × List Bool =>
      directRunState M (fun h q => (G (p.2.2, (h, q))).take (ρ.eval p.1.length)) p.1 p.2.1)
      (encPair encBits (encPair encBits encBits)) (encPair encFiniteConfig encHistory) := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  have hρ : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => ρ.eval p.1.length)
      (encPair encBits (encPair encBits encBits)) encUnary :=
    (unary_eval ρ).comp (length_bits.comp (fst _ _))
  unfold directRunState
  refine (foldlWith_spec
    (par := fun p : List Bool × List Bool × List Bool =>
      (p.2.1.length, p.2.2, ρ.eval p.1.length))
    (list := fun p => p.2.1)
    (init := fun p => (MultiTapeMachine.FiniteConfig.init M.initial p.1, ([] : History)))
    (step := fun par s b => directStep M (fun h q => (G (par.2.1, (h, q))).take par.2.2)
      par.1 s b)
    (encP := encPair encUnary (encPair encBits encUnary)) (encA := encBool) (encL := encBits)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (computableInPolyTime_directStep M hG)
    (fun p consumed s => DirectInv p.1.length consumed.length p.2.1.length
      (ρ.eval p.1.length) s)
    (fun p => directInv_init _ _ _ _)
    (fun p consumed s b _ hs => by
      rw [List.length_append, List.length_singleton]
      exact directStep_inv M _ (fun h q => List.length_take_le _ _) hs b)
    (size := fun p =>
      2 * (cf * (3 * (encPair encBits (encPair encBits encBits) p).length + 1)) + 1 +
      (encPair encBits (encPair encBits encBits) p).length * (2 * (2 *
        (encPair encBits (encPair encBits encBits) p).length + 2 * ρ.eval p.1.length + 2) + 1))
    (by growth_poly)
    (fun p consumed s hprefix hs => ?_)).1
  obtain ⟨hspace, hlen, hent⟩ := hs
  have hcfg := hcf _ _ _ _ hspace
  have hcons : consumed.length ≤ p.2.1.length := hprefix.length_le
  have hhist := length_encList_le (encPair encBits encBits) s.2
    (b := 2 * consumed.length + 2 * ρ.eval p.1.length + 2) (fun e he => by
      simp only [length_encPair, encBits_apply]
      have := hent e he
      lia)
  have hL : (encPair encBits (encPair encBits encBits) p).length =
      2 * p.1.length + 1 + (2 * p.2.1.length + 1 + p.2.2.length) := by
    simp only [length_encPair, encBits_apply]
  have hs : (encPair encFiniteConfig encHistory s).length =
      2 * (encFiniteConfig s.1).length + 1 + (encHistory s.2).length := by
    simp
  rw [hs]
  have h1 : (encFiniteConfig s.1).length ≤
      cf * (3 * (encPair encBits (encPair encBits encBits) p).length + 1) :=
    hcfg.trans (Nat.mul_le_mul_left cf (by lia))
  have h2 : (encHistory s.2).length ≤ (encPair encBits (encPair encBits encBits) p).length *
      (2 * (2 * (encPair encBits (encPair encBits encBits) p).length +
        2 * ρ.eval p.1.length + 2) + 1) :=
    hhist.trans (Nat.mul_le_mul (by lia) (by lia))
  lia

end PolyTime

end Direct

end Interaction

open Interaction _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **An interactive proof with a prover computable from short advice gives `MA`.** If an
efficient verifier is sound with error `1 / 3` against every prover, and on every member some
advice word `w` of polynomial length makes the deterministic prover answering the message `q`
after the history `h` with `G (w, (h, q))`, for a polynomial-time `G` with polynomially long
replies, accepted with probability at least `2 / 3`, the problem is in `MA`: Merlin sends the
advice and Arthur runs the verifier against that prover, keeping the history himself.

The replies of the prover are required to have length at most `ρ (|enc a|)` on every member, so
that Arthur's computation stays polynomial-time on every proof: he truncates the replies to that
length, which changes nothing for the honest prover and, for any other advice word, gives a prover
against which soundness holds. -/
theorem mem_MA_of_adviceProver {verifier : α → WordOracleComp Unit Bool}
    (hppt : IsOraclePPTOn enc encBool verifier)
    (hsound : ∀ a ∉ A, ∀ P : Prover Unit, acceptProb (verifier a) P ≤ 1 / 3)
    {G : List Bool × (History × List Bool) → List Bool}
    (hG : ComputableInPolyTime G (encReplyInput encBits) encBits)
    (ℓ ρ : Polynomial ℕ)
    (hcomplete : ∀ a ∈ A, ∃ w : List Bool, w.length ≤ ℓ.eval (enc a).length ∧
      (∀ h q, (G (w, (h, q))).length ≤ ρ.eval (enc a).length) ∧
      2 / 3 ≤ acceptProb (verifier a) (Prover.ofHistoryFun fun h q => G (w, (h, q)))) :
    A ∈ MA enc := by
  obtain ⟨_, k, Control, hfin, M, c, d, hreal⟩ := hppt
  have := hfin
  obtain ⟨N, hNdef⟩ : ∃ N : Polynomial ℕ, N = 2 * ℓ + 1 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Polynomial ℕ, T = Polynomial.C c * (Polynomial.X + 1) ^ d :=
    ⟨_, rfl⟩
  have hT (a : α) : T.eval (enc a).length = c * ((enc a).length + 1) ^ d := by simp [hTdef]
  have hN (a : α) : N.eval (enc a).length = 2 * ℓ.eval (enc a).length + 1 := by simp [hNdef]
  obtain ⟨V, hVdef⟩ : ∃ V : α × List Bool → Bool, V = fun z =>
    decide ((directRun M (fun h q => (G (unframe (z.2.take (N.eval (enc z.1).length)),
      (h, q))).take (ρ.eval (enc z.1).length)) (enc z.1)
        (z.2.drop (N.eval (enc z.1).length))).tapes.output = [true]) := ⟨_, rfl⟩
  have hVeval (a : α) (y : Fin (N.eval (enc a).length) → Bool) (r : List Bool) :
      V (a, List.ofFn y ++ r) = decide ((directRun M (fun h q =>
        (G (unframe (List.ofFn y), (h, q))).take (ρ.eval (enc a).length)) (enc a) r).tapes.output =
          [true]) := by
    simp only [hVdef, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  have hcount (a : α) (y : Fin (N.eval (enc a).length) → Bool) :
      acceptProb (verifier a) (Prover.ofHistoryFun fun h q =>
        (G (unframe (List.ofFn y), (h, q))).take (ρ.eval (enc a).length)) =
        ((Finset.univ.filter fun r : Fin (T.eval (enc a).length) → Bool =>
          V (a, List.ofFn y ++ List.ofFn r) = true).card : ENNReal) /
          (2 ^ T.eval (enc a).length : ℕ) := by
    have h := acceptProb_ofHistoryFun M (fun S oracle s => hreal a S oracle s)
      (fun h q => (G (unframe (List.ofFn y), (h, q))).take (ρ.eval (enc a).length))
    rw [← hT a] at h
    simpa only [hVeval, decide_eq_true_eq] using h
  have hpos (a : α) : (2 ^ T.eval (enc a).length : ℕ) ≠ 0 := by positivity
  refine ⟨N, T, V, ?_, fun a => ⟨fun ha => ?_, fun ha y => ?_⟩⟩
  · have hrun := Interaction.computableInPolyTime_directRunState M hG ρ
    have hAcc : ComputableInPolyTime (fun p : List Bool × List Bool × List Bool =>
        decide ((directRun M (fun h q => (G (p.2.2, (h, q))).take (ρ.eval p.1.length)) p.1
          p.2.1).tapes.output = [true]))
        (encPair encBits (encPair encBits encBits)) encBool :=
      ComputableInPolyTime.decide_eq' (ComputableInPolyTime.finiteCfg_output.comp
        (ComputableInPolyTime.finiteConfig_tapes.comp
          ((ComputableInPolyTime.fst encFiniteConfig encHistory).comp hrun)))
        (ComputableInPolyTime.const [true])
    have hx : ComputableInPolyTime (fun z : α × List Bool => enc z.1) (encPair enc encBits)
        encBits :=
      (ComputableInPolyTime.of_eq (f := enc) (encOut := encBits) fun _ => rfl).comp
        (ComputableInPolyTime.fst enc encBits)
    have hlen : ComputableInPolyTime (fun z : α × List Bool => N.eval (enc z.1).length)
        (encPair enc encBits) encUnary :=
      ((ComputableInPolyTime.unary_eval N).comp
        (ComputableInPolyTime.encoding_length enc)).comp (ComputableInPolyTime.fst enc encBits)
    have hdrop := ComputableInPolyTime.bitsDropWithInput
      (ComputableInPolyTime.snd enc encBits) hlen
    have htake := ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.snd enc encBits) hlen
    have hall : ComputableInPolyTime (fun z : α × List Bool =>
        (enc z.1, z.2.drop (N.eval (enc z.1).length),
          unframe (z.2.take (N.eval (enc z.1).length))))
        (encPair enc encBits) (encPair encBits (encPair encBits encBits)) :=
      hx.prod (hdrop.prod (ComputableInPolyTime.unframe.comp htake))
    rw [hVdef]
    have hcomp := hAcc.comp hall
    exact hcomp
  · obtain ⟨w, hw, hρw, hacc⟩ := hcomplete a ha
    have hlen : (BitString.padWord (ℓ.eval (enc a).length) w).length = N.eval (enc a).length := by
      rw [BitString.length_padWord hw, hN]
    obtain ⟨y, hy⟩ : ∃ y : Fin (N.eval (enc a).length) → Bool, unframe (List.ofFn y) = w :=
      ⟨BitString.ofList _ (BitString.padWord (ℓ.eval (enc a).length) w), by
        rw [BitString.ofFn_ofList hlen]
        simp [BitString.padWord]⟩
    subst hy
    refine ⟨y, ?_⟩
    have hfun : (fun h q => (G (unframe (List.ofFn y), (h, q))).take (ρ.eval (enc a).length)) =
        fun h q => G (unframe (List.ofFn y), (h, q)) :=
      funext fun h => funext fun q => List.take_of_length_le (hρw h q)
    rw [← hfun, hcount a y,
      show (2 / 3 : ENNReal) = ((2 : ℕ) : ENNReal) / ((3 : ℕ) : ENNReal) by norm_num,
      ENNReal.natCast_div_le_natCast_div_iff (by norm_num) (hpos a)] at hacc
    unfold BoundedErrorAt
    exact hacc.trans_eq (Nat.mul_comm _ _)
  · have h := hsound a ha (Prover.ofHistoryFun fun h q =>
      (G (unframe (List.ofFn y), (h, q))).take (ρ.eval (enc a).length))
    rw [hcount a y,
      show (1 / 3 : ENNReal) = ((1 : ℕ) : ENNReal) / ((3 : ℕ) : ENNReal) by norm_num,
      ENNReal.natCast_div_le_natCast_div_iff (hpos a) (by norm_num)] at h
    rw [boundedErrorAt_false_iff]
    unfold acceptCount
    exact (Nat.mul_comm _ _).trans_le (h.trans_eq (Nat.one_mul _))

end Cslib.Complexity
