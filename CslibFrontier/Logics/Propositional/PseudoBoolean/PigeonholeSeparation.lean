/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
public import CslibFrontier.Logics.Propositional.PseudoBoolean.CompileCuttingPlanes
public import CslibFrontier.Logics.Propositional.PseudoBoolean.OfLRAT
public import CslibFrontier.Logics.Propositional.Resolution.LRATLowerBound
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Logics.Propositional.CuttingPlanes.Pigeonhole

/-!
# VeriPB refutes the pigeonhole principle in polynomial size, LRAT does not

Compiling the polynomial-size cutting planes refutation of the pigeonhole formula `PHP^m_n`
[Cook, Coullard and Turán][CookCoullardTuran1987]
(`Cslib.Logic.PL.CuttingPlanes.refutableInSize_pigeonhole`) into `pol` steps
(`Cslib.Logic.PL.VeriPB.exists_check_cnf_of_refutableInSize`) gives, for `m > n`, a proof that the
VeriPB kernel checker [Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023]
accepts on the clauses of `PHP^m_n` with at most `(n + 1) (m + 1)²` steps, each a `pol` step of at
most three operations and no hints (`Cslib.Logic.PL.VeriPB.exists_check_pigeonhole`). The
formula's variables `Fin m × Fin n` are renamed into `ℕ` along any injective map.

On `PHP^{n+1}_n`, every certificate that the LRAT checker accepts has
`2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min (H) (S · (n + 1) n)`, where `S` is its number of steps
and `H` its number of hints (`Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`, from
[Haken's theorem][Haken1985]). Hence any translation of the accepted VeriPB proofs of
`PHP^{n+1}_n` with at most `s` steps into accepted LRAT certificates with `min (H) (S) ≤ g s`
needs `2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + g ((n + 1) (n + 2)²) · ((n + 1) n + 1)`
(`Cslib.Logic.PL.VeriPB.two_pow_le_of_forall_check_pigeonhole`), so no polynomially bounded `g`
does it (`Cslib.Logic.PL.VeriPB.not_exists_polynomiallyBounded_checkLRAT_pigeonhole`). Bounding
`min (H) (S)` rules out a polynomial simulation whether LRAT size counts steps, hints or both. The
translation need only handle the proofs made of `pol` steps without saturation.

**VeriPB versus LRAT.** Conversely, every certificate that the LRAT checker accepts, with `S`
steps and `H` hints, translates into a proof that the kernel checker accepts with at most `S` steps
and `H + S` hints (`Cslib.Logic.PL.CNF.check_toVeriPB`), so VeriPB polynomially simulates LRAT,
with linear overhead. With the above, VeriPB polynomially simulates LRAT and is exponentially more
succinct on `PHP^{n+1}_n`
(`Cslib.Logic.PL.VeriPB.check_toVeriPB_and_not_exists_polynomiallyBounded`;
`Cslib.Logic.PL.VeriPB.exists_check_pigeonhole_and_two_pow_le` for a fixed `n`). There the size of
a proof is its number of steps plus its number of hints, on both sides.

As in the cited results, the size of a proof counts steps and hints, not the bit size of
coefficients. These theorems are corollaries, original to this library, of the cited cutting planes
upper bound and resolution lower bound through the translations between VeriPB, cutting planes and
LRAT.

## Main results

* `Cslib.Logic.PL.VeriPB.exists_check_pigeonhole`: polynomial-size VeriPB proofs of `PHP^m_n`.
* `Cslib.Logic.PL.VeriPB.two_pow_le_of_forall_check_pigeonhole`: the quantitative separation from
  LRAT on `PHP^{n+1}_n`.
* `Cslib.Logic.PL.VeriPB.not_exists_polynomiallyBounded_checkLRAT_pigeonhole`: LRAT does not
  polynomially simulate VeriPB.
* `Cslib.Logic.PL.VeriPB.exists_check_pigeonhole_and_two_pow_le`,
  `Cslib.Logic.PL.VeriPB.check_toVeriPB_and_not_exists_polynomiallyBounded`: VeriPB polynomially
  simulates LRAT and is exponentially more succinct on `PHP^{n+1}_n`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
* [A. Haken, *The intractability of resolution*][Haken1985]
-/

public section

namespace Cslib.Logic.PL.VeriPB

open CNF CuttingPlanes
open Std.Tactic.BVDecide (LRAT.IntAction)

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
    (toIneqs_relabel hf (pigeonhole m n) ▸ (refutableInSize_pigeonhole h).relabel f)
  refine ⟨P, hP, hlen, hcp, fun s hs => ?_⟩
  rw [hann, List.mem_map] at hs
  obtain ⟨l, -, rfl⟩ := hs
  obtain ⟨ops, hops, hlen, -⟩ := l.exists_toStep_eq_pol _
  exact ⟨ops, hops, hlen⟩

/-- **Exponential separation of VeriPB from LRAT on `PHP^{n+1}_n`**
[Cook, Coullard and Turán][CookCoullardTuran1987] [Haken][Haken1985]. Let `f` be an injective
naming of the variables of `PHP^{n+1}_n` by `ℕ`. If every proof of `UNSAT` with at most `s` steps
that the VeriPB kernel checker accepts on the clauses of `PHP^{n+1}_n`, made of `pol` steps without
saturation, yields a certificate that the LRAT checker accepts with `min (H) (S) ≤ g s`, where `S`
is its number of steps and `H` its number of hints, then
`2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + g ((n + 1) (n + 2)²) · ((n + 1) n + 1)`. Size counts steps
and hints; coefficient sizes are not measured, as in the cited results. -/
theorem two_pow_le_of_forall_check_pigeonhole {n : ℕ} {f : Fin (n + 1) × Fin n → ℕ}
    (hf : Function.Injective f) {g : ℕ → ℕ}
    (hsim : ∀ (s : ℕ) (P : Proof),
      check (((pigeonhole (n + 1) n).relabel f).map Clause.toPB) P = true →
      P.steps.all Step.IsCP → P.steps.length ≤ s →
      ∃ cert : Array LRAT.IntAction, ((pigeonhole (n + 1) n).relabel f).checkLRAT cert = true ∧
        min (lratHintCount cert.toList) cert.size ≤ g s) :
    2 ^ (n / 24) ≤
      (n + 1) + n * (n + 1) ^ 2 + g ((n + 1) * (n + 2) ^ 2) * ((n + 1) * n + 1) := by
  obtain ⟨P, hP, hlen, hcp, -⟩ := exists_check_pigeonhole n.lt_succ_self hf
  obtain ⟨cert, hcert, hg⟩ := hsim _ P hP hcp hlen
  have hmin : min (lratHintCount cert.toList) (cert.size * ((n + 1) * n)) ≤
      min (lratHintCount cert.toList) cert.size * ((n + 1) * n + 1) := by
    rcases le_total (lratHintCount cert.toList) cert.size with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  exact (two_pow_le_of_checkLRAT_pigeonhole hf hcert).trans
    (Nat.add_le_add_left (hmin.trans (Nat.mul_le_mul_right _ hg)) _)

/-- **LRAT does not polynomially simulate VeriPB** [Cook, Coullard and
Turán][CookCoullardTuran1987] [Haken][Haken1985]. For injective namings `f n` of the variables of
`PHP^{n+1}_n` by `ℕ`, no polynomially bounded `g` turns every proof of `UNSAT` with at most `s`
steps that the VeriPB kernel checker accepts on the clauses of `PHP^{n+1}_n`, for every `n`, made of
`pol` steps without saturation, into a certificate that the LRAT checker accepts with
`min (H) (S) ≤ g s`, where `S` is its number of steps and `H` its number of hints. So LRAT size
counted in steps, in hints, or in both is not polynomial in VeriPB size counted in steps.
Coefficient sizes are not measured, as in the cited results. -/
theorem not_exists_polynomiallyBounded_checkLRAT_pigeonhole
    {f : ∀ n, Fin (n + 1) × Fin n → ℕ} (hf : ∀ n, Function.Injective (f n)) :
    ¬ ∃ g : ℕ → ℕ, PolynomiallyBounded g ∧ ∀ (n s : ℕ) (P : Proof),
      check (((pigeonhole (n + 1) n).relabel (f n)).map Clause.toPB) P = true →
      P.steps.all Step.IsCP → P.steps.length ≤ s →
      ∃ cert : Array LRAT.IntAction, ((pigeonhole (n + 1) n).relabel (f n)).checkLRAT cert = true ∧
        min (lratHintCount cert.toList) cert.size ≤ g s := by
  rintro ⟨g, hg, hsim⟩
  have hG : PolynomiallyBounded fun k => (24 * k + 1) + 24 * k * (24 * k + 1) ^ 2 +
      g ((24 * k + 1) * (24 * k + 2) ^ 2) * ((24 * k + 1) * (24 * k) + 1) := by
    have := hg.comp (g := fun k => (24 * k + 1) * (24 * k + 2) ^ 2) (by fun_prop)
    fun_prop
  obtain ⟨k, hk⟩ := hG.eventually_lt_two_pow.exists
  have := two_pow_le_of_forall_check_pigeonhole (hf (24 * k)) (hsim (24 * k))
  rw [show 24 * k / 24 = k by omega] at this
  exact absurd hk (not_lt.2 this)

/-! ### VeriPB polynomially simulates LRAT, and not conversely -/

/-- Steps without saturation, and deletions, have no hints. -/
theorem hintCount_eq_zero_of_all_isCP : ∀ {ss : List Step}, ss.all Step.IsCP → hintCount ss = 0
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := hintCount_eq_zero_of_all_isCP h.2
    cases s <;> simp_all [hintCount, Step.hintCount, Step.IsCP]

/-- **VeriPB refutes `PHP^{n+1}_n` in polynomial size, LRAT only in exponential size**
[Cook, Coullard and Turán][CookCoullardTuran1987] [Haken][Haken1985]. For an injective naming `f`
of the variables of `PHP^{n+1}_n` by `ℕ`, the VeriPB kernel checker accepts a proof of `UNSAT` on
its clauses with at most `(n + 1) (n + 2)²` steps and no hints, while every certificate that the
LRAT checker accepts, with `S` steps and `H` hints, has
`2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min (H) (S · (n + 1) n)`. Size counts steps and hints;
coefficient sizes are not measured, as in the cited results. -/
theorem exists_check_pigeonhole_and_two_pow_le {n : ℕ} {f : Fin (n + 1) × Fin n → ℕ}
    (hf : Function.Injective f) :
    (∃ P : Proof, check (((pigeonhole (n + 1) n).relabel f).map Clause.toPB) P = true ∧
      P.steps.length + hintCount P.steps ≤ (n + 1) * (n + 2) ^ 2) ∧
    ∀ cert : Array LRAT.IntAction, ((pigeonhole (n + 1) n).relabel f).checkLRAT cert = true →
      2 ^ (n / 24) ≤ (n + 1) + n * (n + 1) ^ 2 +
        min (lratHintCount cert.toList) (cert.size * ((n + 1) * n)) := by
  obtain ⟨P, hP, hlen, hcp, -⟩ := exists_check_pigeonhole n.lt_succ_self hf
  exact ⟨⟨P, hP, by rw [hintCount_eq_zero_of_all_isCP hcp]; exact hlen⟩,
    fun _ => two_pow_le_of_checkLRAT_pigeonhole hf⟩

/-- **VeriPB polynomially simulates LRAT and is exponentially more succinct on `PHP^{n+1}_n`**
[Cook, Coullard and Turán][CookCoullardTuran1987] [Haken][Haken1985]. The size of a proof is its
number of steps plus its number of hints, for LRAT certificates and VeriPB kernel proofs alike.

1. Every certificate that the LRAT checker accepts for a CNF `φ` translates, by
   `Cslib.Logic.PL.CNF.toVeriPB`, into a proof that the kernel checker accepts on the clauses of
   `φ`, of at most twice its size.
2. For injective namings `f n` of the variables of `PHP^{n+1}_n` by `ℕ`, the kernel checker
   accepts proofs of `UNSAT` on the clauses of `PHP^{n+1}_n` of size at most `(n + 1) (n + 2)²`.
3. No polynomially bounded `g` turns every proof of `UNSAT` of size at most `s` that the kernel
   checker accepts on the clauses of `PHP^{n+1}_n`, for every `n`, into a certificate that the
   LRAT checker accepts of size at most `g s`, even for proofs made of `pol` steps without
   saturation and deletions.

Coefficient sizes are not measured, as in the cited results. Part 3 also holds with the LRAT size
`min (H) (S)` and the VeriPB size counting steps only
(`Cslib.Logic.PL.VeriPB.not_exists_polynomiallyBounded_checkLRAT_pigeonhole`). -/
theorem check_toVeriPB_and_not_exists_polynomiallyBounded
    {f : ∀ n, Fin (n + 1) × Fin n → ℕ} (hf : ∀ n, Function.Injective (f n)) :
    (∀ (φ : CNF ℕ) (cert : Array LRAT.IntAction), φ.checkLRAT cert = true →
      check (φ.map Clause.toPB) (φ.toVeriPB cert) = true ∧
        (φ.toVeriPB cert).steps.length + hintCount (φ.toVeriPB cert).steps ≤
          2 * (cert.size + lratHintCount cert.toList)) ∧
    (∀ n, ∃ P : Proof, check (((pigeonhole (n + 1) n).relabel (f n)).map Clause.toPB) P = true ∧
      P.steps.length + hintCount P.steps ≤ (n + 1) * (n + 2) ^ 2) ∧
    ¬ ∃ g : ℕ → ℕ, PolynomiallyBounded g ∧ ∀ (n s : ℕ) (P : Proof),
      check (((pigeonhole (n + 1) n).relabel (f n)).map Clause.toPB) P = true →
      P.steps.all Step.IsCP → P.steps.length + hintCount P.steps ≤ s →
      ∃ cert : Array LRAT.IntAction, ((pigeonhole (n + 1) n).relabel (f n)).checkLRAT cert = true ∧
        cert.size + lratHintCount cert.toList ≤ g s := by
  refine ⟨fun φ cert h => ⟨check_toVeriPB h, ?_⟩,
    fun n => (exists_check_pigeonhole_and_two_pow_le (hf n)).1, ?_⟩
  · have := length_toVeriPB_le φ cert
    have := hintCount_toVeriPB_le φ cert
    omega
  · rintro ⟨g, hg, hsim⟩
    refine not_exists_polynomiallyBounded_checkLRAT_pigeonhole hf
      ⟨g, hg, fun n s P hP hcp hs => ?_⟩
    obtain ⟨cert, hcert, hle⟩ :=
      hsim n s P hP hcp (by rw [hintCount_eq_zero_of_all_isCP hcp, Nat.add_zero]; exact hs)
    exact ⟨cert, hcert, (min_le_right _ _).trans (by omega)⟩

end Cslib.Logic.PL.VeriPB
