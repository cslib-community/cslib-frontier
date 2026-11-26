/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.OfLRAT
import CslibFrontier.Algorithms.Lean.CDCL.Watched
import CslibFrontier.Logics.Propositional.Pigeonhole
import CslibFrontierTests.Logics.Propositional.CNF.LRAT

/-!
# LRAT certificates as VeriPB proofs

The four clauses over `a = 0` and `b = 1`, numbered `1` to `4`,

  `a ∨ b`, `a ∨ ¬b`, `¬a ∨ b`, `¬a ∨ ¬b`,

have the certificate `5: a` with hints `1, 2`, then the empty clause with hints `5, 3, 4`. Its
translation is `rup a : ~ 1 2`, then `rup 0 ≥ 1 : 5 3 4`, with the conclusion `6`, and the
kernel accepts it, also through `checkRed`. Certificate numbers that are not consecutive are
renumbered, and a deletion of a number that is not present is dropped. A number may be reused
after its clause is deleted, or while that clause is still present: then the new clause shadows
the earlier one, a hint with the number names the new clause, and a deletion of the number
deletes both, so the translated `del` names both kernel numbers. A RUP clause with complementary
literals is a tautology, which the kernel accepts at once from its negation.

**The converse fails.** With the superfluous hint `3` first, `¬a ∨ b` has two literals left on
the trail `¬a`: the LRAT checker rejects the certificate, while the kernel skips the hint and
accepts the translation.

The kernel also checks, with `decide +kernel`, the translations of the certificates of
`Cslib.Algorithms.Lean.DPLL.solve` on these clauses and of `Cslib.Algorithms.Lean.CDCL.solve` on
the pigeonhole formula PHP(3, 2), and of the certificate CaDiCaL emits for PHP(5, 4).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBOfLRAT

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Algorithms.Lean Std.Tactic.BVDecide

/-- Every clause over two variables. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation: the unit clause `a`, then the empty clause. -/
private abbrev cert : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

example : (φ.toVeriPB cert).steps =
    [.rup ⟨[(1, (0, true))], 1⟩ [.neg, .id 1, .id 2], .rup ⟨[], 1⟩ [.id 5, .id 3, .id 4]] ∧
    (φ.toVeriPB cert).conclusion = 6 :=
  ⟨rfl, rfl⟩

example : check (φ.map Clause.toPB) (φ.toVeriPB cert) = true :=
  CNF.check_toVeriPB (by decide +kernel)

example : check (φ.map Clause.toPB) (φ.toVeriPB cert) = true := by decide +kernel

example : checkRed (φ.map Clause.toPB) none
    ⟨(φ.toVeriPB cert).steps.map .step, .unsat (φ.toVeriPB cert).conclusion⟩ = true :=
  CNF.checkRed_toVeriPB (by decide +kernel) none

/-- Certificate numbers far from the kernel numbers, a number reused after a deletion, and a
deletion of a number that is not present. -/
private abbrev certRenamed : Array LRAT.IntAction :=
  #[.addRup 100 #[1] #[1, 2], .del #[100, 77], .addRup 100 #[1] #[1, 2],
    .addEmpty 7 #[100, 3, 4]]

example : φ.checkLRAT certRenamed = true := by decide +kernel

example : (φ.toVeriPB certRenamed).steps =
    [.rup ⟨[(1, (0, true))], 1⟩ [.neg, .id 1, .id 2], .del [5],
      .rup ⟨[(1, (0, true))], 1⟩ [.neg, .id 1, .id 2], .rup ⟨[], 1⟩ [.id 6, .id 3, .id 4]] ∧
    (φ.toVeriPB certRenamed).conclusion = 7 :=
  ⟨rfl, rfl⟩

example : check (φ.map Clause.toPB) (φ.toVeriPB certRenamed) = true := by decide +kernel

/-- The number `100` reused while its clause `a ∨ b` is present: the unit `a` shadows it, the hint
`100` names `a`, and the deletion of `100` deletes both clauses. -/
private abbrev certShadowed : Array LRAT.IntAction :=
  #[.addRup 100 #[1, 2] #[1], .addRup 100 #[1] #[1, 2], .addRup 8 #[1] #[100], .del #[100],
    .addEmpty 9 #[8, 3, 4]]

example : φ.checkLRAT certShadowed = true := by decide +kernel

example : (φ.toVeriPB certShadowed).steps =
    [.rup ⟨[(1, (0, true)), (1, (1, true))], 1⟩ [.neg, .id 1],
      .rup ⟨[(1, (0, true))], 1⟩ [.neg, .id 1, .id 2], .rup ⟨[(1, (0, true))], 1⟩ [.neg, .id 6],
      .del [6, 5], .rup ⟨[], 1⟩ [.id 7, .id 3, .id 4]] ∧
    (φ.toVeriPB certShadowed).conclusion = 8 :=
  ⟨rfl, rfl⟩

example : check (φ.map Clause.toPB) (φ.toVeriPB certShadowed) = true := by decide +kernel

/-- A tautological RUP clause, `a ∨ ¬a ∨ b`: its negation conflicts at once. -/
private abbrev certTaut : Array LRAT.IntAction :=
  #[.addRup 5 #[1, -1, 2] #[1], .addRup 6 #[1] #[1, 2], .addEmpty 7 #[6, 3, 4]]

example : φ.checkLRAT certTaut = true := by decide +kernel

example : check (φ.map Clause.toPB) (φ.toVeriPB certTaut) = true := by decide +kernel

/-! ### The converse fails -/

/-- The certificate with the superfluous non-unit hint `3`. -/
private abbrev certSuperfluous : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[3, 1, 2], .addEmpty 6 #[5, 3, 4]]

example : φ.checkLRAT certSuperfluous = false := by decide +kernel

example : check (φ.map Clause.toPB) (φ.toVeriPB certSuperfluous) = true := by decide +kernel

/-! ### Certificates from the solvers -/

example : (match DPLL.solve φ with
    | .unsat c => check (φ.map Clause.toPB) (φ.toVeriPB c)
    | .sat _ => false) = true := by
  decide +kernel

/-- PHP(3, 2), with pigeon `i` in hole `j` as `2 * i + j`. -/
private abbrev php : CNF ℕ := (CNF.pigeonhole 3 2).relabel fun x => 2 * x.1.val + x.2.val

example : (match CDCL.solve php with
    | .unsat c => check (php.map Clause.toPB) (php.toVeriPB c)
    | .sat _ => false) = true := by
  decide +kernel

/-- The certificate CaDiCaL 3.0.1 emits for PHP(5, 4), with 47 RUP steps and 7 deletions
(`CslibFrontierTests.Logics.Propositional.CNF.LRAT.phpCert`), translates into an accepted kernel
proof. -/
example : check (CNF.LRAT.php.map Clause.toPB) (CNF.LRAT.php.toVeriPB CNF.LRAT.phpCert) = true := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBOfLRAT
