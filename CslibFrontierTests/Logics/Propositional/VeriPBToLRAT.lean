/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.ToLRAT
import CslibFrontierTests.Logics.Propositional.CNF.LRAT

/-!
# Clausal VeriPB proofs as LRAT certificates

On the four clauses over `a = 0` and `b = 1`, numbered `1` to `4`,

  `a ∨ b`, `a ∨ ¬b`, `¬a ∨ b`, `¬a ∨ ¬b`,

a clausal kernel proof derives `2 a ≥ 1` with the hints `1 ~ 1 2`: clause `1` first propagates
nothing, and propagates `b` once `~` has propagated `¬a`. It then derives the tautology
`a + ¬a ≥ 1`, which normalizes to `0 ≥ 0`, deletes it, and derives `0 ≥ 1` from `5 3 4`. The
kernel accepts it, and the LRAT checker accepts its back-translation: the RUP clause `a` with the
hints `1 1 2`, since LRAT starts from the negated clause, so the first hint `1` already propagates;
the deletion; the RUP step for the empty clause; and the empty-clause step for the conclusion. The
tautology is not translated.

Translating an LRAT certificate to VeriPB and back gives an accepted certificate, also for the
certificate with a superfluous non-unit hint, which the LRAT checker rejects: the back-translation
drops the hint. A proof with no steps, concluding with an empty clause of the formula, needs one
LRAT step. The round trip is also checked on the certificate CaDiCaL emits for PHP(5, 4).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBToLRAT

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Std.Tactic.BVDecide

/-- Every clause over two variables. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The clausal kernel proof. -/
private abbrev P : Proof :=
  ⟨[.rup ⟨[(2, (0, true))], 1⟩ [.id 1, .neg, .id 1, .id 2],
    .rup ⟨[(1, (0, true)), (1, (0, false))], 1⟩ [.neg], .del [6],
    .rup ⟨[], 1⟩ [.id 5, .id 3, .id 4]], 7⟩

example : check (φ.map Clause.toPB) P = true := by decide +kernel

example : P.steps.all Step.isClausal = true := by decide +kernel

example : (toLRAT φ P ==
    #[.addRup 5 #[1] #[1, 1, 2], .del #[6], .addRup 7 #[] #[5, 3, 4], .addEmpty 8 #[7]]) =
      true := by
  decide +kernel

example : φ.checkLRAT (toLRAT φ P) = true :=
  checkLRAT_toLRAT (by decide +kernel) (by decide +kernel)

example : φ.checkLRAT (toLRAT φ P) = true := by decide +kernel

/-- A `pol` step is not clausal. -/
example : (Step.pol [.id 1, .id 2, .add]).isClausal = false := by decide +kernel

/-- A proof with no steps, whose conclusion names the empty clause of the formula: the
back-translation needs one step and one hint more than the proof. -/
example : check (List.map Clause.toPB [[]]) ⟨[], 1⟩ = true ∧
    (toLRAT [[]] ⟨[], 1⟩ == #[.addEmpty 2 #[1]]) = true ∧
    CNF.checkLRAT [[]] (toLRAT [[]] ⟨[], 1⟩) = true := by
  decide +kernel

/-! ### Round trips -/

/-- The certificate with the superfluous non-unit hint `3`, which the LRAT checker rejects. -/
private abbrev certSuperfluous : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[3, 1, 2], .addEmpty 6 #[5, 3, 4]]

example : φ.checkLRAT certSuperfluous = false := by decide +kernel

example : (toLRAT φ (φ.toVeriPB certSuperfluous) ==
    #[.addRup 5 #[1] #[1, 2], .addRup 6 #[] #[5, 3, 4], .addEmpty 7 #[6]]) = true := by
  decide +kernel

example : φ.checkLRAT (toLRAT φ (φ.toVeriPB certSuperfluous)) = true := by decide +kernel

example : CNF.LRAT.php.checkLRAT
    (toLRAT CNF.LRAT.php (CNF.LRAT.php.toVeriPB CNF.LRAT.phpCert)) = true := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBToLRAT
