/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Asymptotic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi

/-!
# The empty coalition of a protocol family

When no party is corrupted, an environment against a `ProtocolFamily` sees the outputs of all
parties and nothing else: there is exactly one tuple of views of the parties in `∅`. This module
gives the generic API of that coalition.

`SimulatorFamily.empty P` is the simulator family of the empty coalition, which returns the empty
tuple of views; it is PPT for every encoding (`SimulatorFamily.isPPT_empty`).
`Environment.forgetViews` turns an environment against the empty coalition into an environment
against a coalition `I` that chooses the same inputs and ignores the views of `I`. This does not
change the real game (`ProtocolFamily.realGame_forgetViews`), and the ideal game of every simulator
family for `I` becomes the ideal game of `SimulatorFamily.empty P`
(`ProtocolFamily.idealGame_forgetViews`).

`ProtocolFamily.SemiHonestSecure.empty_of_forall_negligible` is the first property: if for some
coalition `I` and some simulator family for `I`, efficient or not, every environment has negligible
advantage between the real and the ideal game, then `P` is semi-honest secure against the empty
coalition for every encoding. The hypothesis is about all environments, not only the PPT ones: no
PPT certificate for `Environment.forgetViews` is proved here, so this does not derive security
against the empty coalition from `ProtocolFamily.SemiHonestSecure` against `I`.

This is original infrastructure, not a cited result. `ProtocolFamily.SemiHonestSecure` is compared
with its sources in `CslibFrontier/Crypto/Protocols/MPC/Asymptotic.lean`; against the empty
coalition it compares the outputs of the protocol with the outputs of the functionality, which is
correctness of the outputs up to a negligible error.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.SimulatorFamily.empty`: the simulator family of the empty coalition.
* `Cslib.Crypto.Protocols.MPC.Environment.forgetViews`: an environment against the empty coalition
  as an environment against any coalition.

## Main results

* `Cslib.Crypto.Protocols.MPC.SimulatorFamily.isPPT_empty`: the simulator family of the empty
  coalition is PPT for every encoding.
* `Cslib.Crypto.Protocols.MPC.ProtocolFamily.realGame_forgetViews`,
  `Cslib.Crypto.Protocols.MPC.ProtocolFamily.idealGame_forgetViews`: the games of a forgetful
  environment against a coalition are the games of the empty coalition.
* `Cslib.Crypto.Protocols.MPC.ProtocolFamily.SemiHonestSecure.empty_of_forall_negligible`:
  statistical closeness of the real and ideal games at any coalition gives security against the
  empty coalition.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Turing.MultiTapeTM

variable {m : ℕ} {P : ProtocolFamily m}

/-- The simulator family of the empty coalition of `P`: at every security parameter and public
parameters it returns the empty tuple of views, the only tuple of views of the parties in `∅`. -/
@[expose] def SimulatorFamily.empty (P : ProtocolFamily m) : SimulatorFamily P ∅ :=
  fun _ _ _ _ => pure fun i => isEmptyElim i

/-- The simulator family of the empty coalition is PPT for every encoding: its machine writes the
empty table of views. -/
theorem SimulatorFamily.isPPT_empty (E : P.Encoding) : (SimulatorFamily.empty P).IsPPT E :=
  (ComputableInPolyTime.dpi fun i : (∅ : Finset (Fin m)) => isEmptyElim i).isPPTOn.congr
    fun _ => rfl

/-- An environment against the empty coalition, as an environment against the coalition `I`: it
chooses the same inputs and state, and guesses from the state and the outputs of all parties,
ignoring the views of the parties in `I`. -/
@[expose] def Environment.forgetViews (Z : Environment P ∅) (I : Finset (Fin m)) :
    Environment P I where
  choose := Z.choose
  guess n d st r := Z.guess n d st (fun i => isEmptyElim i, r.2)

namespace ProtocolFamily

/-- The real game of a forgetful environment against the coalition `I` is the real game of the
empty coalition: the protocol runs on the same inputs, and the environment guesses from the same
outputs. -/
@[simp] theorem realGame_forgetViews (setup : ℕ → PMF P.Desc) (I : Finset (Fin m))
    (Z : Environment P ∅) (n : ℕ) :
    P.realGame setup I (Z.forgetViews I) n = P.realGame setup ∅ Z n := by
  simp only [realGame, Environment.forgetViews, Protocol.realJoint, PMF.monad_bind_eq_bind,
    PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun d => congrArg _ (funext fun c => congrArg _ (funext fun r => ?_)))
  exact congrArg (fun v => ProbComp.eval (Z.guess n d c.state v))
    (Prod.ext (Subsingleton.elim _ _) rfl)

/-- The ideal game of a forgetful environment against the coalition `I`, with any simulator family
`S` for `I`, is the ideal game of the empty coalition with `SimulatorFamily.empty P`: the
environment ignores the views that `S` produces. -/
@[simp] theorem idealGame_forgetViews (setup : ℕ → PMF P.Desc) {I : Finset (Fin m)}
    (S : SimulatorFamily P I) (Z : Environment P ∅) (n : ℕ) :
    P.idealGame setup I S (Z.forgetViews I) n =
      P.idealGame setup ∅ (SimulatorFamily.empty P) Z n := by
  simp only [idealGame, Environment.forgetViews, SimulatorFamily.empty, eval_idealJoint,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_map,
    PMF.pure_bind, PMF.bind_const, Function.comp_def]

/-- **Statistical closeness at any coalition gives security against the empty coalition.** If for
some coalition `I` and some simulator family `S` for `I`, which need not be PPT, every environment
against `I`, efficient or not, has negligible advantage between the real game and the ideal game
with `S`, then `P` is semi-honest secure against the empty coalition for every encoding `E`, with
the simulator family `SimulatorFamily.empty P`.

An environment against the empty coalition sees only the outputs of all parties, so the conclusion
says that the outputs of the protocol are indistinguishable from the outputs of the functionality:
correctness of the outputs up to a negligible error. The hypothesis is about all environments,
while `SemiHonestSecure setup I E` bounds only the PPT ones, so this theorem does not turn security
against `I` into security against the empty coalition. This is original infrastructure, not a
cited result. -/
theorem SemiHonestSecure.empty_of_forall_negligible {setup : ℕ → PMF P.Desc}
    {I : Finset (Fin m)} {S : SimulatorFamily P I}
    (h : ∀ Z : Environment P I, Negligible fun n =>
      Game.advantage (P.realGame setup I Z n) (P.idealGame setup I S Z n))
    (E : P.Encoding) : P.SemiHonestSecure setup ∅ E :=
  ⟨SimulatorFamily.empty P, SimulatorFamily.isPPT_empty E, fun Z _ => by
    simpa only [realGame_forgetViews, idealGame_forgetViews] using h (Z.forgetViews I)⟩

end ProtocolFamily

end Cslib.Crypto.Protocols.MPC
