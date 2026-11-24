/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.EmptyCoalition

/-!
# Tests for the empty coalition of a protocol family

A client of `CslibFrontier.Crypto.Protocols.MPC.EmptyCoalition` under module encapsulation, at a
generic protocol family `P`.

* `Environment.forgetViews` keeps the choosing stage, and forgetting the views of the empty
  coalition changes nothing.
* With `SimulatorFamily.empty P`, the ideal joint distribution of the empty coalition is the
  functionality's outputs beside the empty tuple of views.
* The advantage of a forgetful environment against a coalition `I`, with any simulator family for
  `I`, is the advantage of the environment against the empty coalition with
  `SimulatorFamily.empty P`.
* Perfect privacy against one coalition `I`, with a simulator family that need not be PPT, gives
  `ProtocolFamily.SemiHonestSecure` against the empty coalition for every encoding, through
  `ProtocolFamily.SemiHonestSecure.empty_of_forall_negligible`. Perfect privacy is one way to meet
  the hypothesis of that theorem; `idealJoint_sendSimulator` in
  `CslibFrontierTests.Crypto.MPCAsymptotic` proves it for a concrete protocol family at the
  coalition `{1}`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MPCEmptyCoalition

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC

variable {m : ℕ} {P : ProtocolFamily m}

/-! ### Forgetful environments and the empty simulator -/

/-- A forgetful environment chooses the same inputs and state. -/
example (Z : Environment P ∅) (I : Finset (Fin m)) : (Z.forgetViews I).choose = Z.choose :=
  rfl

/-- Forgetting the views of the empty coalition changes nothing: its tuple of views is unique. -/
example (Z : Environment P ∅) : Z.forgetViews ∅ = Z :=
  congrArg (Environment.mk Z.choose) (funext fun n => funext fun d => funext fun st =>
    funext fun _ => congrArg (Z.guess n d st) (Prod.ext (Subsingleton.elim _ _) rfl))

/-- With the empty simulator, the ideal joint distribution of the empty coalition is the
functionality's outputs beside the empty tuple of views. -/
example (n : ℕ) (d : P.Desc) (x : (i : Fin m) → P.In n d i) :
    ProbComp.eval (idealJoint (P.functionality n d) ∅ (SimulatorFamily.empty P n d) x) =
      (ProbComp.eval (P.functionality n d x)).map fun y => (fun i => isEmptyElim i, y) := by
  simp only [eval_idealJoint, SimulatorFamily.empty, ProbComp.eval_pure, PMF.pure_map]
  rfl

/-! ### Games and security against the empty coalition -/

/-- The advantage of a forgetful environment against `I`, with any simulator family for `I`, is the
advantage of the environment against the empty coalition with the empty simulator. -/
example (setup : ℕ → PMF P.Desc) {I : Finset (Fin m)} (S : SimulatorFamily P I)
    (Z : Environment P ∅) (n : ℕ) :
    Game.advantage (P.realGame setup I (Z.forgetViews I) n)
        (P.idealGame setup I S (Z.forgetViews I) n) =
      Game.advantage (P.realGame setup ∅ Z n) (P.idealGame setup ∅ (.empty P) Z n) := by
  rw [ProtocolFamily.realGame_forgetViews, ProtocolFamily.idealGame_forgetViews]

/-- **Perfect privacy against one coalition gives security against the empty coalition**, for
every encoding, although the simulator family `S` for `I` is not assumed to be PPT. -/
example {setup : ℕ → PMF P.Desc} {I : Finset (Fin m)} {S : SimulatorFamily P I}
    (h : ∀ n d x, ProbComp.eval (idealJoint (P.functionality n d) I (S n d) x) =
      (P.protocol n d).realJoint (P.world n d) I x) (E : P.Encoding) :
    P.SemiHonestSecure setup ∅ E :=
  .empty_of_forall_negligible (S := S) (fun Z => by
    simp only [ProtocolFamily.realGame_eq_idealGame h, Game.advantage_self]
    exact negligible_zero) E

end CslibFrontierTests.Crypto.MPCEmptyCoalition
