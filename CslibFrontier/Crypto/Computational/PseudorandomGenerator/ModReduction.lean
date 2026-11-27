/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Tactic.PPT

/-!
# Pseudorandom residues from pseudorandom words

Boneh–Shoup Example 3.3 ([BonehShoup2023], pp. 86–87) reduces an `L`-bit pseudorandom word modulo
`m` to obtain an element of `{0, ..., m - 1}` that is computationally indistinguishable from
uniform when `m / 2 ^ L` is negligible.

Here `modWord m word` reads `word` most significant bit first (`BitString.binaryValue`) and
encodes the residue modulo `m` with `encNat`. The reduction `modDistinguisher m adversary`
evaluates `modWord (m n)` on its challenge word before running `adversary n`.

Compared with [BonehShoup2023], pp. 86–87: `2 ^ L ≥ m` is not assumed (for `m > 2 ^ L` the bound
exceeds `1`); the bound is `≤ m / 2 ^ L` where Example 3.2 proves `<`; the modulus `m` may depend
on the security parameter `n` and must then be computable in polynomial time (`hm`), which is what
makes the reduction `modDistinguisher` efficient; and the generator's security is used only as
indistinguishability of its output from uniform words.

## Main definitions

* `Cslib.Crypto.modWord`: reduce a binary word modulo `m` and re-encode the residue.
* `Cslib.Crypto.modDistinguisher`: the reduction that runs a residue distinguisher on `modWord`.

## Main results

* `Cslib.Crypto.closeTo_uniformList_map_modWord`: uniform `L`-bit words reduced modulo `m` are
  within `m / 2 ^ L` of uniform residues in `CloseTo` ([BonehShoup2023], Example 3.2, p. 86).
* `Cslib.Crypto.isPPT_modDistinguisher`: uniform strict-PPT certificate for `modDistinguisher`.
* `Cslib.Crypto.advantage_distinguishingGame_map_modWord_le`: concrete advantage bound for
  arbitrary word distributions.
* `Cslib.Crypto.ComputationallyIndistinguishable.map_modWord`: asymptotic security for word
  ensembles ([BonehShoup2023], Example 3.3, pp. 86–87).
* `Cslib.Crypto.advantage_generatorEnsemble_map_modWord_le`: the book's inequality
  `Distadv[A, P₀, P₁] ≤ PRGadv[B, G] + m / N`.
* `Cslib.Crypto.PseudorandomGenerator.indistinguishable_map_modWord`: asymptotic security for a
  `PseudorandomGenerator`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 3.11 (Examples 3.2–3.3, pp. 86–87).
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- As naturals, `sampleModNat width M` is within `M / 2 ^ width` of a uniform value below `M`. -/
private theorem closeTo_sampleModNat_fin (width M : ℕ) [NeZero M] :
    CloseTo (ProbComp.eval (ProbComp.sampleModNat width M))
      ((PMF.uniformOfFintype (Fin M)).map Fin.val) ((M : ℝ≥0) / 2 ^ width : ℝ≥0) := by
  refine Game.closeTo_iff_forall_advantage_bind_le.mpr fun test => ?_
  rw [PMF.bind_map]
  exact Game.advantage_bind_sampleModNat_fin_le width M test

/-- Read `word` as a binary number, most significant bit first (`BitString.binaryValue`), and write
its residue modulo `m` with `encNat`, least significant bit first. For `m = 0` the value is not
reduced. -/
@[expose] def modWord (m : ℕ) (word : List Bool) : List Bool :=
  encNat (BitString.binaryValue word % m)

/-- Reducing a uniform word of `L` bits is the bounded residue sampler `sampleModNat L m`. -/
theorem uniformList_map_modWord (L m : ℕ) :
    (BitString.uniformList L).map (modWord m) =
      (ProbComp.eval (ProbComp.sampleModNat L m)).map encNat := by
  simp only [ProbComp.sampleModNat, ProbComp.sampleBinaryNat, ProbComp.eval_map,
    BitString.eval_sampleList, PMF.map_comp]
  rfl

/-- The residue modulo `m` of a uniform word of `L` bits is within `m / 2 ^ L` of a uniform
residue ([BonehShoup2023], Example 3.2, p. 86, on binary words). -/
theorem closeTo_uniformList_map_modWord (L m : ℕ) [NeZero m] :
    CloseTo ((BitString.uniformList L).map (modWord m))
      ((PMF.uniformOfFintype (Fin m)).map fun i => encNat i.val) ((m : ℝ≥0) / 2 ^ L : ℝ≥0) := by
  rw [uniformList_map_modWord]
  simpa only [PMF.map_comp, Function.comp_def] using (closeTo_sampleModNat_fin L m).map encNat

/-- The reduction of [BonehShoup2023], Example 3.3, p. 86: reduce the challenge word modulo
`m n`, then run the given distinguisher on the residue. -/
def modDistinguisher (m : ℕ → ℕ) (adversary : Distinguisher) : Distinguisher :=
  fun n word => adversary n (modWord (m n) word)

/-- Reduction modulo a modulus computed from the unary parameter is polynomial time. -/
theorem computableInPolyTime_modWord {m : ℕ → ℕ} (hm : ComputableInPolyTime m encUnary encNat) :
    ComputableInPolyTime (fun p : ℕ × List Bool => modWord (m p.1) p.2)
      (encPair encUnary encBits) encBits := by
  exact (ComputableInPolyTime.binary_mod' (left := fun p : ℕ × List Bool =>
    BitString.binaryValue p.2) (right := fun p => m p.1) (by fun_prop) (by fun_prop)).encoding_comp

/-- The reduction is uniform strict PPT when the modulus is computable in polynomial time from
the unary security parameter and the given distinguisher is PPT. -/
theorem isPPT_modDistinguisher {m : ℕ → ℕ} {adversary : Distinguisher}
    (hm : ComputableInPolyTime m encUnary encNat) (hadversary : IsPPT encBool adversary) :
    IsPPT encBool (modDistinguisher m adversary) := by
  have hf := computableInPolyTime_modWord hm
  unfold modDistinguisher
  ppt

/-- Running a distinguisher on residues is running the reduction on the words. -/
theorem distinguishingGame_map_modWord (m : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ)
    (D : PMF (List Bool)) :
    distinguishingGame (D.map (modWord (m n))) (adversary n) =
      distinguishingGame D (modDistinguisher m adversary n) := by
  simp only [distinguishingGame_eq_bind, PMF.monad_bind_eq_bind, PMF.bind_map]
  rfl

/-- **Example 3.3, concrete bound** ([BonehShoup2023], p. 87): the advantage in telling residues of
samples of `D` from uniform residues is at most the advantage of the reduction in telling `D` from
uniform `L`-bit words, plus `m n / 2 ^ L`. -/
theorem advantage_distinguishingGame_map_modWord_le (m : ℕ → ℕ) [∀ n, NeZero (m n)]
    (adversary : Distinguisher) (n L : ℕ) (D : PMF (List Bool)) :
    Game.advantage (distinguishingGame (D.map (modWord (m n))) (adversary n))
        (distinguishingGame ((PMF.uniformOfFintype (Fin (m n))).map fun i => encNat i.val)
          (adversary n)) ≤
      Game.advantage (distinguishingGame D (modDistinguisher m adversary n))
        (distinguishingGame (BitString.uniformList L) (modDistinguisher m adversary n)) +
        (m n : ℝ≥0) / 2 ^ L := by
  refine (Game.advantage_triangle _
    (distinguishingGame ((BitString.uniformList L).map (modWord (m n))) (adversary n)) _).trans
    (add_le_add ?_ ?_)
  · rw [distinguishingGame_map_modWord, distinguishingGame_map_modWord]
  · exact Game.advantage_bind_le_of_closeTo (closeTo_uniformList_map_modWord L (m n))
      fun word => ProbComp.eval (adversary n word)

/-- **Example 3.3** ([BonehShoup2023], pp. 86–87): if an ensemble of words is computationally
indistinguishable from uniform words of `length n` bits, the modulus is efficiently computable
and `m n / 2 ^ length n` is negligible, then the residues modulo `m n` are computationally
indistinguishable from uniform residues. The efficiency hypothesis `hm` is present for the PPT
certificate of the reduction `modDistinguisher` (`isPPT_modDistinguisher`), and no failing case
without `hm` is known. -/
theorem ComputationallyIndistinguishable.map_modWord {X : ℕ → PMF (List Bool)} {length m : ℕ → ℕ}
    [∀ n, NeZero (m n)]
    (hX : ComputationallyIndistinguishable X fun n => BitString.uniformList (length n))
    (hm : ComputableInPolyTime m encUnary encNat)
    (hneg : Negligible fun n => (m n : ℝ≥0) / 2 ^ length n) :
    ComputationallyIndistinguishable (fun n => (X n).map (modWord (m n)))
      (fun n => (PMF.uniformOfFintype (Fin (m n))).map fun i => encNat i.val) :=
  fun adversary hadversary =>
    negligible_of_le ((hX _ (isPPT_modDistinguisher hm hadversary)).add hneg) fun n =>
      advantage_distinguishingGame_map_modWord_le m adversary n (length n) (X n)

/-- **Example 3.3, the book's inequality** ([BonehShoup2023], p. 87):
`Distadv[A, P₀, P₁] ≤ PRGadv[B, G] + m / N`, where `P₀` is the generator's output reduced modulo
`m n`, `P₁` is the uniform residue, `N = 2 ^ length n` and `B` is `modDistinguisher m A`, run in
the two programs of the generator's attack game. No hypothesis on the generator is used. -/
theorem advantage_generatorEnsemble_map_modWord_le (generator : List Bool → List Bool)
    (length m : ℕ → ℕ) [∀ n, NeZero (m n)] (adversary : Distinguisher) (n : ℕ) :
    Game.advantage
        (distinguishingGame ((generatorEnsemble generator n).map (modWord (m n))) (adversary n))
        (distinguishingGame ((PMF.uniformOfFintype (Fin (m n))).map fun i => encNat i.val)
          (adversary n)) ≤
      Game.advantage (ProbComp.eval (prgRealGame generator (modDistinguisher m adversary) n))
        (ProbComp.eval (prgIdealGame length (modDistinguisher m adversary) n)) +
        (m n : ℝ≥0) / 2 ^ length n := by
  rw [eval_prgRealGame, eval_prgIdealGame]
  exact advantage_distinguishingGame_map_modWord_le m adversary n (length n)
    (generatorEnsemble generator n)

/-- **Example 3.3 for a pseudorandom generator**: the generated word reduced modulo `m n` is
computationally indistinguishable from a uniform residue. The efficiency hypothesis `hm` is present
for the PPT certificate of the reduction `modDistinguisher`, and no failing case without `hm` is
known. -/
theorem PseudorandomGenerator.indistinguishable_map_modWord
    {generator : List Bool → List Bool} {length m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (h : PseudorandomGenerator generator length)
    (hm : ComputableInPolyTime m encUnary encNat)
    (hneg : Negligible fun n => (m n : ℝ≥0) / 2 ^ length n) :
    ComputationallyIndistinguishable
      (fun n => (generatorEnsemble generator n).map (modWord (m n)))
      (fun n => (PMF.uniformOfFintype (Fin (m n))).map fun i => encNat i.val) :=
  h.indistinguishable.map_modWord hm hneg

end Cslib.Crypto
