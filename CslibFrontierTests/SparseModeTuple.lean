/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ModeTupleCode

open Cslib.SparseModeTuple

-- The first colour is empty. In the second, weight two has multiplicity three,
-- weight three is absent, and weight four has multiplicity one.
private def sample : List Row := [⟨1, ⟨1, 2⟩, [⟨1, 0⟩]⟩]

example : (encode sample).length = 19 := by decide

example : decode 25 (padded 25 sample) = some sample := decode_padded (by decide)

example : query (padded 25 sample) 1 1 = some 3 ∧
    query (padded 25 sample) 1 2 = some 0 ∧
    query (padded 25 sample) 1 3 = some 1 ∧
    query (padded 25 sample) 0 1 = some 0 ∧ query (padded 25 sample) 2 1 = some 0 := by
  simp only [query_padded]
  decide

example : decode 1 [false] ≠ some [] := by
  rw [ne_eq, decode_eq_some_iff]
  decide

-- The same canonical sparse syntax has an extra colour at m=1 and sits exactly at
-- the strict mass limit p=10. Increasing both bounds admits it.
example : validate 25 1 11 (padded 25 sample) = none ∧
    validate 25 2 10 (padded 25 sample) = none ∧
    validate 25 2 11 (padded 25 sample) = some sample := by
  simp only [validate_padded (show (encode sample).length ≤ 25 by decide)]
  decide

-- A single finite word simultaneously represents all exponents of an arbitrary array.
example {m n p : ℕ} (β : Fin m → Fin n → ℕ)
    (hβ : ∑ c, ∑ i : Fin n, (i.val + 1) * β c i ≤ p) :
    ∃ word : List Bool, word.length = 64 * Nat.sqrt (2 * m * p) + 3 ∧
      ∀ c i, query word c.val i.val = some (β c i) := by
  have h := length_encode_le (ofFn β) (colours_ofFn_le β) (by simpa [mass_ofFn] using hβ)
  exact ⟨padded _ (ofFn β), length_padded h, fun c i => by rw [query_padded, coord_ofFn]⟩

open Cslib.Circuits.Frontier ContractionSchedule

-- The node's single uniform guessing width supports all modes of every admissible tuple.
example {C s d M p : ℕ} (hb : ActiveBounds C s d M p) (ha : Active C s d M p)
    {i h packets : ℕ} (hi : i < taper s d) (hh : h * taper s d ≤ 3 * M + taper s d)
    (hk : packets * 2 ^ slotBits s d ≤ 3 * M)
    (β : Fin packets × Fin (2 ^ (i + 1)) × Fin (nodePrecision p h (slotBits s d) M i) → ℕ)
    (hβ : β ∈ TensorNetwork.modeBudget (fun z => z.2.2.val + 1)
      (nodePrecision p h (slotBits s d) M i)) :
    ∃ word : List Bool, word.length = 32 * branchExponent C s d ∧
      decode (32 * branchExponent C s d) word = some (modeRows β) ∧
      ∀ k t b, query word (finProdFinEquiv (k, t)).val b.val = some (β (k, t, b)) := by
  have hl := hb.length_modeRows_le ha hi hh hk β hβ
  exact ⟨padded _ (modeRows β), length_padded hl, decode_padded hl, fun k t b => by
    rw [query_padded, coord_modeRows]⟩
