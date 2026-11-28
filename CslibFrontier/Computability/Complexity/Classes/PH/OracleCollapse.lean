/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.PH
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Substitution
import CslibFrontier.Computability.Complexity.Classes.PH.Projection

/-!
# Collapse of the relativized polynomial hierarchy

The hierarchy relative to an oracle language uses the same alternating polynomial-length
certificate blocks as the ordinary hierarchy. Its terminal verifier is a deterministic
polynomial-time computation with access to the oracle.

If relative `P` and relative `NP` coincide on Boolean words, bounded existential quantification
preserves relative `P` on every instance encoding. Complementation gives the universal case.
Peeling off the first quantifier then proves collapse by induction on the number of blocks.

## Main definitions

* `Cslib.Complexity.SigmaPWithOracle`: an existential level relative to a language oracle.
* `Cslib.Complexity.PHWithOracle`: the union of the existential levels.

## Main results

* `Cslib.Complexity.PHWithOracle_subset_PWithOracle_of_eq_NPWithOracle`: equality of relative
  `P` and `NP` on raw words collapses the relative hierarchy for every instance encoding.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {O : Set (List Bool)}

/-- The existential level `k` relative to `O`. Its oracle verifier checks the concatenation of
`k` alternating blocks of polynomially long certificates, starting with an existential block. -/
@[expose]
def SigmaPWithOracle (O : Set (List Bool)) (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool), ps.length = k ∧
    ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc true ps V L}

/-- The polynomial hierarchy relative to `O`, with respect to the instance encoding `enc`. -/
@[expose]
def PHWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k, SigmaPWithOracle O k enc

/-- A bounded existential projection verified with an oracle remains in relative `NP` after
extending its instance encoding to raw words. The extension only has to agree on codewords. -/
private theorem npWithOracle_subset_pWithOracle
    (h : NPWithOracle O encBits ⊆ PWithOracle O encBits) :
    NPWithOracle O enc ⊆ PWithOracle O enc := by
  rintro L ⟨p, V, hV, hL⟩
  obtain ⟨W, hW, hWV⟩ := hV.exists_bool_extension
  let B : Set (List Bool) := {u | ∃ w : List Bool, w.length = p.eval u.length ∧
    W (encPair encBits encBits (u, w)) = true}
  have hB : B ∈ NPWithOracle O encBits :=
    ⟨p, _, hW.preprocess (ComputableInPolyTime.of_eq fun _ => rfl), fun _ => Iff.rfl⟩
  refine PolyTimeReducible.mem_PWithOracle
    ⟨enc, ComputableInPolyTime.of_eq fun _ => rfl, fun a => ?_⟩ (h hB)
  rw [hL a]
  exact exists_congr fun w => and_congr_right fun _ => by rw [← hWV (a, w)]; rfl

private theorem pWithOracle_of_alternatingVerifier
    (h : NPWithOracle O encBits ⊆ PWithOracle O encBits)
    {ps : List (Polynomial ℕ)} {q : Bool} {L : Set α} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool)
    (hL : IsAlternatingVerifier enc q ps V L) :
    L ∈ PWithOracle O enc := by
  induction ps generalizing α q with
  | nil =>
    exact ⟨fun a => V (a, []), hV.preprocess (.prod .id' (.const [])),
      fun a => by simpa using hL a⟩
  | cons p ps ih =>
    obtain ⟨B, g, hg, hB, hLB⟩ := hL.peel
    have hdec := ih (hV.preprocess hg) hB
    cases q with
    | true =>
      obtain ⟨W, hW, hBW⟩ := hdec
      exact npWithOracle_subset_pWithOracle h
        ⟨p, W, hW, fun a => (hLB a).trans
          (exists_congr fun w => and_congr_right fun _ => hBW (a, w))⟩
    | false =>
      obtain ⟨W, hW, hBW⟩ := compl_mem_PWithOracle hdec
      have hc : Lᶜ ∈ NPWithOracle O enc := ⟨p, W, hW, fun a => by
        simp only [Set.mem_compl_iff, hLB a, Bool.false_eq_true, ↓reduceIte,
          not_forall, exists_prop]
        exact exists_congr fun w => and_congr_right fun _ => hBW (a, w)⟩
      simpa only [compl_compl] using compl_mem_PWithOracle (npWithOracle_subset_pWithOracle h hc)

/-- If `P^O = NP^O` on Boolean words, then `PH^O ⊆ P^O` for any instance encoding.
The oracle is an arbitrary language of Boolean words. This is Exercise 5 §9 (printed p. 100,
PDF p. 116) of the 2007-01-08 Arora–Barak draft [AroraBarak07]. Its language formulation is the
case `enc = encBits`. -/
theorem PHWithOracle_subset_PWithOracle_of_eq_NPWithOracle
    (h : PWithOracle O encBits = NPWithOracle O encBits) :
    PHWithOracle O enc ⊆ PWithOracle O enc := by
  intro L hL
  obtain ⟨k, _, V, _, hV, hL⟩ := Set.mem_iUnion.mp hL
  exact pWithOracle_of_alternatingVerifier h.ge hV hL

/-- Every relative polynomial-time decider is an alternating verifier with zero blocks. -/
theorem PWithOracle_subset_PHWithOracle : PWithOracle O enc ⊆ PHWithOracle O enc := by
  rintro L ⟨f, hf, hL⟩
  exact Set.mem_iUnion.mpr ⟨0, [], fun x => f x.1, rfl,
    hf.preprocess (.fst enc encBits), fun a => by simpa using hL a⟩

/-- If `P^O = NP^O` on raw words, then the relativized hierarchy equals `P^O`
for every instance encoding. -/
theorem PHWithOracle_eq_PWithOracle_of_eq_NPWithOracle
    (h : PWithOracle O encBits = NPWithOracle O encBits) :
    PHWithOracle O enc = PWithOracle O enc :=
  (PHWithOracle_subset_PWithOracle_of_eq_NPWithOracle h).antisymm PWithOracle_subset_PHWithOracle

end Cslib.Complexity
