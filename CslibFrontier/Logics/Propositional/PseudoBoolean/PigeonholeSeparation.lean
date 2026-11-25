/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.CompileCuttingPlanes
public import CslibFrontier.Logics.Propositional.CuttingPlanes.Pigeonhole
public import CslibFrontier.Logics.Propositional.Resolution.LRATLowerBound

/-!
# VeriPB refutes the pigeonhole principle in polynomial size, LRAT does not

Compiling the polynomial-size cutting planes refutation of the pigeonhole formula `PHP^m_n`
(`Cslib.Logic.PL.CuttingPlanes.refutableInSize_pigeonhole`) into `pol` steps
(`Cslib.Logic.PL.VeriPB.exists_check_cnf_of_refutableInSize`) gives, for `m > n`, a proof that the
VeriPB kernel checker accepts on the clauses of `PHP^m_n` with at most `(n + 1) (m + 1)²` steps,
each a `pol` step of at most three operations and no hints
(`Cslib.Logic.PL.VeriPB.exists_check_pigeonhole`). The formula's variables `Fin m × Fin n` are
renamed into `ℕ` along any injective map.

On `PHP^{n+1}_n`, every certificate that the LRAT checker accepts has
`2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min (H) (S · (n + 1) n)`, where `S` is its number of steps
and `H` its number of hints (`Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`, from
Haken's theorem). Together (`Cslib.Logic.PL.VeriPB.pigeonhole_separation`): VeriPB proofs of
`PHP^{n+1}_n` have `O(n³)` steps, while LRAT certificates have `2 ^ Ω(n)` steps and hints. As in
the cited results, the size of a proof counts steps and hints, not the bit size of coefficients.

## Main results

* `Cslib.Logic.PL.VeriPB.exists_check_pigeonhole`: polynomial-size VeriPB proofs of `PHP^m_n`.
* `Cslib.Logic.PL.VeriPB.pigeonhole_separation`: the separation from LRAT on `PHP^{n+1}_n`.
-/

public section

namespace Cslib.Logic.PL.VeriPB

open CNF CuttingPlanes

/-- **Polynomial-size VeriPB proofs of the pigeonhole principle.** For `m > n` and an injective
naming `f` of the variables `Fin m × Fin n` of `PHP^m_n` by `ℕ`, the VeriPB kernel checker accepts
a proof of `UNSAT` on the clauses of `PHP^m_n` with at most `(n + 1) (m + 1)²` steps, each a `pol`
step of at most three operations without saturation, the compiled lines of the cutting planes
refutation of [Cook, Coullard and Turán][CookCoullardTuran1987]. Coefficient sizes are not
measured. -/
theorem exists_check_pigeonhole {m n : ℕ} (h : n < m) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) :
    ∃ P : Proof, check (((pigeonhole m n).relabel f).map Clause.toPB) P = true ∧
      P.steps.length ≤ (n + 1) * (m + 1) ^ 2 ∧ P.steps.all Step.IsCP ∧
      ∀ s ∈ P.steps, ∃ ops, s = .pol ops ∧ ops.length ≤ 3 := by
  obtain ⟨P, hP, hlen, hcp, ann, hann⟩ := exists_check_cnf_of_refutableInSize
    (toIneqs_relabel hf (pigeonhole m n) ▸ (refutableInSize_pigeonhole h).relabel hf)
  refine ⟨P, hP, hlen, hcp, fun s hs => ?_⟩
  rw [hann, List.mem_map] at hs
  obtain ⟨l, -, rfl⟩ := hs
  obtain ⟨ops, hops, hlen, -⟩ := l.exists_toStep_eq_pol _
  exact ⟨ops, hops, hlen⟩

/-- **VeriPB is exponentially more succinct than LRAT on the pigeonhole principle.** For an
injective naming `f` of the variables of `PHP^{n+1}_n` by `ℕ`:

* the VeriPB kernel checker accepts a proof of `UNSAT` on its clauses with at most
  `(n + 1) (n + 2)²` steps, each a `pol` step of at most three operations, without hints;
* every certificate `cert` that the LRAT checker accepts on it has
  `2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min (H) (S · (n + 1) n)`, where `S = cert.size` is its
  number of steps and `H` its number of hints
  (`Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`), so `H` and `S` are `2 ^ Ω(n)`.

Size counts steps and hints; coefficient sizes are not measured, as in the cited results. That
VeriPB also polynomially simulates LRAT on every formula is the embedding of LRAT certificates
into `rup` steps, which this theorem does not state. -/
theorem pigeonhole_separation (n : ℕ) {f : Fin (n + 1) × Fin n → ℕ} (hf : Function.Injective f) :
    (∃ P : Proof, check (((pigeonhole (n + 1) n).relabel f).map Clause.toPB) P = true ∧
      P.steps.length ≤ (n + 1) * (n + 2) ^ 2 ∧ P.steps.all Step.IsCP ∧
      ∀ s ∈ P.steps, ∃ ops, s = .pol ops ∧ ops.length ≤ 3) ∧
    ∀ cert : Array Std.Tactic.BVDecide.LRAT.IntAction,
      ((pigeonhole (n + 1) n).relabel f).checkLRAT cert = true →
        2 ^ (n / 24) ≤ (n + 1) + n * (n + 1) ^ 2 +
          min (lratHintCount cert.toList) (cert.size * ((n + 1) * n)) :=
  ⟨exists_check_pigeonhole n.lt_succ_self hf, fun _ h => two_pow_le_of_checkLRAT_pigeonhole hf h⟩

end Cslib.Logic.PL.VeriPB
