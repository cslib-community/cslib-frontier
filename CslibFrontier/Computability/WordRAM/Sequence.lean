/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Structured

/-!
# Reassociating structured native execution proofs

## Main results

* `WordRAM.ExecWithin.seq_iff`: split a block at its actual intermediate state and stage budgets.
* `WordRAM.ExecWithin.seq_assoc`: compose an already proved instruction block with the
  surrounding right-associated program, without repeating its execution proof.

Reassociation preserves the same data states and charged bound. This narrow proof-rule
module avoids extending the interface of the widely imported structured-code core.
-/

public section

namespace Cslib.WordRAM.ExecWithin

/-- Split sequential execution into actual intermediate data and charged stage budgets. -/
theorem seq_iff {B : Basis} {r w T : ℕ} {a b : Code B r} {x z : Data r} :
    ExecWithin w (.seq a b) x z T ↔
      ∃ y T₁ T₂, ExecWithin w a x y T₁ ∧ ExecWithin w b y z T₂ ∧ T₁ + T₂ ≤ T :=
  ⟨fun ⟨_, hn, .seq ha hb⟩ => ⟨_, _, _, ha.within, hb.within, hn⟩,
    fun ⟨_, _, _, ha, hb, hT⟩ => (ha.seq hb).mono hT⟩

/-- Sequential blocks may be regrouped while preserving every instruction charge. -/
theorem seq_assoc {B : Basis} {r w T : ℕ} {a b c : Code B r} {x y : Data r} :
    ExecWithin w (.seq (.seq a b) c) x y T ↔ ExecWithin w (.seq a (.seq b c)) x y T :=
  ⟨fun ⟨_, hn, .seq (.seq ha hb) hc⟩ => ⟨_, by omega, .seq ha (.seq hb hc)⟩,
    fun ⟨_, hn, .seq ha (.seq hb hc)⟩ => ⟨_, by omega, .seq (.seq ha hb) hc⟩⟩

end Cslib.WordRAM.ExecWithin
