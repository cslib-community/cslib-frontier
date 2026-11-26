/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccProg
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccSize

/-!
# One scale is all scales: low degree is fast

`Interpreter.lem_lowdeg`, Lemma K.2 (Section K.2) of *VP ≠ VNP over every field*
[AnthropicVPVNP2026]. Let a polynomial `p` in the variables (place, symbol), with `N ≤ 2 ^ m`
places, be computed within `S ≤ 2 ^ M` nodes (`Arithmetic.ComputedWithin`). Then a program of size
`O(M + m + d)` exists, with a trie of `O(2 ^ (3 M) + 2 ^ (M + m))` constants. At the code of every
short word, its value is the sum of the homogeneous parts of `p` of degree at most `d`, within the
stated number of steps. All its runs stop, and it names only constants, not powers.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Paper.LowDeg`.

## Main results

* `Interpreter.lem_lowdeg`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Finset
open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

open MvPolynomial in
/-- **Paper: Lemma K.2.** Let a polynomial over `R` in the variables (place, symbol), with `n`
places, be computed within `S` nodes. A program of size `O(log S + log n + d)`, with `O((S + n)³)`
constants, has as value the sum of its parts of degree at most `d` at the code of the word of every
`z` with `|z| < n`, in `(d + |z| + 1) (log (S + n + d)) ^ O(1)` steps. All its runs stop, and it
names only constants, not powers. The bound `O(log S + log n)` on the height of the trie is the one
that the circuit lemma of Section K needs. -/
theorem lem_lowdeg : ∃ c : ℕ,
    ∀ (R : Type) [CommRing R] (M m N d S : ℕ) (p : MvPolynomial (Fin N × Option Bool) R),
    ComputedWithin p S → S ≤ 2 ^ M → N ≤ 2 ^ m →
    ∃ (K : KT R) (D : Tree),
      K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 ∧ K.ht ≤ 3 * M + m + 4 ∧ D.size ≤ c *
          (M + m + 1) + 2 * (d + 1) ∧
      ∀ (A : Type) [CommRing A] [Algebra A R] (θ : List Bool → A) (z : Tree), z.size < N →
        Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z,
          r.cost ≤ (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100 ∧
          ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) =
          ∑ i ∈ Finset.range (d + 1),
              MvPolynomial.eval (codeB R N (tbits z)) (MvPolynomial.homogeneousComponent i p) := by
  obtain ⟨c, hc⟩ := size_accF
  refine ⟨c, fun R _ M m N d S p hp hS hN => ?_⟩
  -- d' = d, but a constant needs d' = 1
  obtain ⟨d', q, hd', hd'1, hq, hqv⟩ : ∃ (d' : ℕ) (q : MvPolynomial (Fin N × Option Bool) R),
      0 < d' ∧ d' ≤ d + 1 ∧
      ComputedWithin q S ∧ ∀ u : Fin N × Option Bool → R, ∑ i ∈ Finset.range (d' + 1),
          (line u q).coeff i =
        ∑ i ∈ Finset.range (d + 1),
            MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨1, MvPolynomial.C (MvPolynomial.constantCoeff p), one_pos, le_rfl, ?_, fun u => ?_⟩
      · exact (computedWithin_C _).mono hp.pos
      · simp [Finset.sum_range_succ, line, MvPolynomial.homogeneousComponent_zero,
          MvPolynomial.constantCoeff_eq]
    · exact ⟨d, p, hd, Nat.le_succ d, hp, fun u => Finset.sum_congr rfl fun i _ => coeff_line u p i⟩
  obtain ⟨K, out, hout, hnds, hht, hkv⟩ := accF_kv hq hS hd' hN
  refine ⟨K, (accF M m d' out).code, hnds, hht, (hc M m d' out hout).trans (by omega),
      fun A _ _ θ z hz => ?_⟩
  have h := hkv A θ z hz
  rw [Fm.ofTree_code]
  refine ⟨h.hl, fun r hr => ⟨(h.evl.1 r hr).1.trans ?_, (h.evl.1 r hr).2⟩, by rw [h.evl.2, hqv]⟩
  exact Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hd'1) _) _) _

end Cslib.Circuits.Arithmetic.Separation.Interpreter
