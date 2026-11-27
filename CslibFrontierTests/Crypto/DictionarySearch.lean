/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.DictionarySearch
import CslibFrontier.Crypto.Game

/-!
# Dictionary searches against a hash oracle: client tests

Instances and hypothesis-necessity checks for
`CslibFrontier.Crypto.Computational.DictionarySearch` under module encapsulation. Every check goes
through the public theorems, without exposing definition bodies.
-/

namespace CslibFrontierTests.Crypto.DictionarySearch

open Cslib Cslib.Crypto

/-! ### Instances -/

section Instances

variable {P S Sp Y : Type} [DecidableEq Y]

/-- A secret in `D` is found by the salted search, up to a collision at the same salt. -/
example (H : P × S → Y) (salt : S) (D : List P) {pw : P} (h : pw ∈ D) :
    ∃ w ∈ D,
      (dictionaryPreimageSearch (fun w : P => (w, salt)) (H (pw, salt)) D).evalPure H = some w ∧
        H (w, salt) = H (pw, salt) :=
  exists_evalPure_dictionaryPreimageSearch_of_mem H _ D h

/-- With a hash that has no collision at the salt, the salted search returns the secret itself. -/
example (salt : ℕ) (D : List ℕ) {pw : ℕ} (h : pw ∈ D) :
    (dictionaryPreimageSearch (fun w : ℕ => (w, salt)) (pw + salt) D).evalPure
      (fun x : ℕ × ℕ => x.1 + x.2) = some pw :=
  evalPure_dictionaryPreimageSearch_of_injOn (fun x : ℕ × ℕ => x.1 + x.2) _ D h
    fun _ _ _ _ h => Nat.add_right_cancel h

/-- The salted search asks only at the given salt. -/
example (salt : S) (vk : Y) (D : List P) :
    OracleComp.QueriesSatisfy (fun x : P × S => x.2 = salt)
      (dictionaryPreimageSearch (fun w : P => (w, salt)) vk D) :=
  (queriesSatisfy_dictionarySearch _ _ D).mono fun _ ⟨_, _, h⟩ => h ▸ rfl

/-- Section 18.4.1, "Limits of salting", in probability form: whatever the salt, a secret drawn
from `μ` is found at least as often as it lies in `D`, with `D.length` evaluations. -/
example [Inhabited P] (μ : PMF P) (H : P × S → Y) (salt : S) (D : List P) :
    (∀ vk : Y, OracleComp.IsQueryBounded (dictionaryPreimageSearch (fun w : P => (w, salt)) vk D)
        D.length) ∧
      μ.toOuterMeasure {pw | pw ∈ D} ≤
        (inversionExperiment μ (fun pw => H (pw, salt))
          (dictionaryInverter H (fun w : P => (w, salt)) D)) true :=
  dictionarySearch_inverts μ H _ D

/-- A secret that always lies in the dictionary is always found. -/
example [Inhabited P] (μ : PMF P) (H : P → Y) (D : List P) (h : ∀ pw ∈ μ.support, pw ∈ D) :
    (inversionExperiment μ H (dictionaryInverter H id D)) true = 1 := by
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  have hD : μ.toOuterMeasure {pw | pw ∈ D} = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff μ _).mpr h
  exact hD ▸ le_inversionExperiment_dictionaryInverter μ H id D

/-- Secret salts (Section 18.4.2): the search runs over `D ×ˢ Sp`, with `D.length * Sp.length`
calls. -/
example (salt : S) (vk : Y) (D : List P) (peppers : List Sp) :
    OracleComp.IsQueryBounded
      (dictionaryPreimageSearch (fun e : P × Sp => (e.1, salt, e.2)) vk (D ×ˢ peppers))
      (D.length * peppers.length) := by
  have h := isQueryBounded_dictionarySearch
    (fun e : P × Sp => (e.1, salt, e.2)) (fun y => decide (y = vk)) (D ×ˢ peppers)
  rwa [List.length_product] at h

/-- The verifier of password protocol version 3 tries every pepper: the same search over the
pepper space, with `peppers.length` calls. -/
example (pw : P) (salt : S) (vk : Y) (peppers : List Sp) :
    OracleComp.IsQueryBounded
      (Option.isSome <$> dictionaryPreimageSearch (fun p : Sp => (pw, salt, p)) vk peppers)
      peppers.length :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_dictionarySearch _ _ peppers)

/-- A table for every salt (Section 18.4.1, first strategy): `D.length * salts.length` calls. -/
example (D : List P) (salts : List S) :
    OracleComp.IsQueryBounded (dictionaryTable (Y := Y) (id : P × S → P × S) (D ×ˢ salts))
      (D.length * salts.length) := by
  have h := isQueryBounded_dictionaryTable (Y := Y) (id : P × S → P × S) (D ×ˢ salts)
  rwa [List.length_product] at h

/-- Separate searches over a salted file (Section 18.4.1, second strategy):
`F.length * D.length` calls. -/
example (D : List P) (F : List (S × Y)) :
    OracleComp.IsQueryBounded
      (F.mapM fun e => dictionaryPreimageSearch (fun w : P => (w, e.1)) e.2 D)
      (F.length * D.length) :=
  isQueryBounded_mapM_dictionaryPreimageSearch D (fun e w => (w, e.1)) Prod.snd F

/-- The batch search returns what separate searches return. -/
example {X : Type} (H : X → Y) (input : P → X) (D : List P) (F : List Y) :
    (dictionaryBatchSearch input D F).evalPure H =
      (F.mapM fun vk => dictionaryPreimageSearch input vk D).evalPure H := by
  rw [evalPure_dictionaryBatchSearch, OracleComp.evalPure_mapM]

/-- (18.3) on a file of three hashes and a dictionary of two candidates: the batch search makes at
most 2 calls, where three separate runs of (18.1) are bounded by 6. -/
example (vk₁ vk₂ vk₃ : ℕ) :
    OracleComp.IsQueryBounded (dictionaryBatchSearch (id : ℕ → ℕ) [0, 1] [vk₁, vk₂, vk₃]) 2 :=
  isQueryBounded_dictionaryBatchSearch id [0, 1] [vk₁, vk₂, vk₃]

/-- (18.2)–(18.3) evaluated: `H x = x % 3`, dictionary `[4, 1, 2, 7]`, file `[1, 2, 0]`. Three
candidates hash to `1` and the first in dictionary order is returned; nothing hashes to `0`. -/
example : (dictionaryBatchSearch (id : ℕ → ℕ) [4, 1, 2, 7] [1, 2, 0]).evalPure (· % 3) =
    [some 4, some 2, none] := by
  rw [evalPure_dictionaryBatchSearch]
  simp only [List.map_cons, List.map_nil, evalPure_dictionarySearch]
  decide

/-- The shape of the searches of Sections 21.11.3 and 21.11.4: one call at an input derived from
the candidate, then a test of the reply that is not an equality with a known hash. `dec` and the
derived input are parameters here; the chapter 21 package supplies them. -/
example {K C M Ctx : Type} [DecidableEq M] (H : P × Ctx → K) (dec : K → C → M)
    (ctx : Ctx) (c : C) (m : M) (D : List P) {pw : P} (hmem : pw ∈ D)
    (hdec : dec (H (pw, ctx)) c = m) :
    OracleComp.IsQueryBounded
        (dictionarySearch (fun w : P => (w, ctx)) (fun k => decide (dec k c = m)) D) D.length ∧
      ∃ w ∈ D,
        (dictionarySearch (fun w : P => (w, ctx))
          (fun k => decide (dec k c = m)) D).evalPure H = some w ∧
        dec (H (w, ctx)) c = m := by
  refine ⟨isQueryBounded_dictionarySearch _ _ D, ?_⟩
  obtain ⟨w, hw, hfind, hacc⟩ := exists_evalPure_dictionarySearch_of_mem (H := H)
    (input := fun w : P => (w, ctx)) (accept := fun k => decide (dec k c = m)) hmem (by simpa)
  exact ⟨w, hw, hfind, by simpa using hacc⟩

/-- The search of Section 18.6.1 against a MAC key derived as `H pw` (printed pp. 741–742): the
test is the MAC verification of one observed pair `(c, t)` under the candidate's key. -/
example {K Ch T : Type} (H : P → K) (verify : K → Ch → T → Bool) (c : Ch) (t : T) (D : List P)
    {pw : P} (hmem : pw ∈ D) (hver : verify (H pw) c t = true) :
    OracleComp.IsQueryBounded (dictionarySearch (id : P → P) (fun k => verify k c t) D)
        D.length ∧
      ∃ w ∈ D, (dictionarySearch (id : P → P) (fun k => verify k c t) D).evalPure H = some w ∧
        verify (H w) c t = true :=
  ⟨isQueryBounded_dictionarySearch _ _ D,
    exists_evalPure_dictionarySearch_of_mem (H := H) (input := id)
      (accept := fun k => verify k c t) hmem hver⟩

/-- The search of Section 21.11.6 after a server compromise (printed p. 912): the test reads one
component of the reply, `H'(pw', id_P, id_Q) = (π₀, ·)`. -/
example {Ctx A B : Type} [DecidableEq A] (H : P × Ctx → A × B) (ctx : Ctx) (D : List P)
    {pw : P} (hmem : pw ∈ D) :
    OracleComp.IsQueryBounded
        (dictionarySearch (fun w : P => (w, ctx))
          (fun y : A × B => decide (y.1 = (H (pw, ctx)).1)) D)
        D.length ∧
      ∃ w ∈ D,
        (dictionarySearch (fun w : P => (w, ctx))
          (fun y : A × B => decide (y.1 = (H (pw, ctx)).1)) D).evalPure H = some w ∧
        (H (w, ctx)).1 = (H (pw, ctx)).1 := by
  refine ⟨isQueryBounded_dictionarySearch _ _ D, ?_⟩
  obtain ⟨w, hw, hfind, hacc⟩ := exists_evalPure_dictionarySearch_of_mem (H := H)
    (input := fun w : P => (w, ctx))
    (accept := fun y : A × B => decide (y.1 = (H (pw, ctx)).1)) hmem (by simp)
  exact ⟨w, hw, hfind, by simpa using hacc⟩

/-- The book's `|D|` for a dictionary given as a finite set: the list of its elements has `D.card`
entries, so the search makes at most `D.card` calls. -/
example (vk : Y) (D : Finset P) :
    OracleComp.IsQueryBounded (dictionaryPreimageSearch (id : P → P) vk D.toList) D.card := by
  have h := isQueryBounded_dictionarySearch (id : P → P) (fun y => decide (y = vk)) D.toList
  rwa [Finset.length_toList] at h

/-- The search of Section 21.11.1 (printed p. 905) on the reply `v = H(pw, chb, 0, r, s)` of a
phished client: p. 905 prints the adversary's test as `H(pw′, r)` while the client sends
`H(pw, chb, 0, r, s)`; as recorded in #5752, this instance uses the full derived input with the
channel binding and both nonces. -/
example {Chb R : Type} (H : P × Chb × ℕ × R × R → Y) (chb : Chb) (r s : R) (D : List P)
    {pw : P} (hmem : pw ∈ D) :
    OracleComp.IsQueryBounded
        (dictionaryPreimageSearch (fun w : P => (w, chb, 0, r, s)) (H (pw, chb, 0, r, s)) D)
        D.length ∧
      ∃ w ∈ D,
        (dictionaryPreimageSearch (fun w : P => (w, chb, 0, r, s))
          (H (pw, chb, 0, r, s)) D).evalPure H = some w ∧
        H (w, chb, 0, r, s) = H (pw, chb, 0, r, s) :=
  ⟨isQueryBounded_dictionarySearch _ _ D,
    exists_evalPure_dictionaryPreimageSearch_of_mem H _ D hmem⟩

end Instances

/-- The bound in the form of `Game.succProbability`. -/
example {P Y : Type} [DecidableEq Y] [Inhabited P] (μ : PMF P) (H : P → Y) (D : List P) :
    (μ.toOuterMeasure {pw | pw ∈ D}).toNNReal ≤
      Game.succProbability (inversionExperiment μ H (dictionaryInverter H id D)) :=
  ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) (le_inversionExperiment_dictionaryInverter μ H id D)

/-! ### Failing cases -/

/-- With a collision the search returns the first colliding candidate, not the secret: the
hypothesis `Set.InjOn` of `evalPure_dictionaryPreimageSearch_of_injOn` cannot be dropped. Here
`H` is constant, the secret is `1`, and the output is `0`. -/
example :
    (dictionaryPreimageSearch id ((fun _ : ℕ => (0 : ℕ)) 1) [0, 1]).evalPure
      (fun _ : ℕ => (0 : ℕ)) = some 0 := by
  rw [evalPure_dictionarySearch]; decide

/-- Injectivity of `H` alone does not give the secret: the hypothesis of
`evalPure_dictionaryPreimageSearch_of_injOn` is injectivity of `w ↦ H (input w)` on `D`. Here
`H = id`, the derived input is constant, the secret is `1`, and the output is `0`. -/
example :
    (dictionaryPreimageSearch (fun _ : ℕ => (0 : ℕ)) ((id : ℕ → ℕ) ((fun _ : ℕ => (0 : ℕ)) 1))
      [0, 1]).evalPure (id : ℕ → ℕ) = some 0 := by
  rw [evalPure_dictionarySearch]; decide

/-- A secret outside the dictionary is not found: `pw ∈ D` cannot be dropped. -/
example :
    (dictionaryPreimageSearch id ((id : ℕ → ℕ) 2) [0, 1]).evalPure (id : ℕ → ℕ) = none := by
  rw [evalPure_dictionarySearch]; decide

/-- A secret that fails the test is not found: the hypothesis `hpw` of
`exists_evalPure_dictionarySearch_of_mem` cannot be dropped. -/
example : (dictionarySearch id (fun _ => false) [0, 1]).evalPure (id : ℕ → ℕ) = none := by
  rw [evalPure_dictionarySearch]; decide

/-- Two candidates need two calls when the first reply is rejected. -/
example : ¬ OracleComp.IsQueryBounded
    (dictionarySearch (id : ℕ → ℕ) (fun _ : ℕ => false) [0, 1]) 1 :=
  not_isQueryBounded_dictionarySearch (y₀ := 0) rfl (by simp)

/-- When every reply is accepted the search stops after one call, so the hypothesis
`accept y₀ = false` of `not_isQueryBounded_dictionarySearch` cannot be dropped. -/
example : OracleComp.IsQueryBounded
    (dictionarySearch (id : ℕ → ℕ) (fun _ : ℕ => true) [0, 1]) 1 := by
  rw [dictionarySearch_cons]
  exact (OracleComp.IsCostBounded.query _).bind fun _ => .pure _ 0

/-- A point mass outside the dictionary: the bound of `le_inversionExperiment_dictionaryInverter`
is `0 ≤ _`, and the search then returns `default`, which need not invert. The secret is `2`,
`H = id`, `D = [0, 1]`, `default = 0`. -/
example :
    ((dictionaryPreimageSearch id ((id : ℕ → ℕ) 2) [0, 1]).evalPure (id : ℕ → ℕ)).getD default ≠
      2 := by
  rw [evalPure_dictionarySearch]; decide

/-- With a collision the table lookup returns the first entry in dictionary order, as the search
does. -/
example : ((dictionaryTable id [0, 1]).evalPure fun _ : ℕ => (5 : ℕ)).lookup 5 = some 0 := by
  rw [evalPure_dictionaryTable]; decide

/-- A point mass outside the dictionary is never inverted: the secret is `2`, the search over
`[0, 1]` returns `default = 0`, and the experiment succeeds with probability exactly `0`. So the
left side of `le_inversionExperiment_dictionaryInverter` cannot be replaced by a positive
constant. -/
example : (inversionExperiment (PMF.pure (2 : ℕ)) (id : ℕ → ℕ)
    (dictionaryInverter id id [0, 1])) true = 0 := by
  rw [inversionExperiment_eq_bind_map, PMF.pure_bind, dictionaryInverter_apply, PMF.pure_map,
    evalPure_dictionarySearch, PMF.pure_apply]
  simp

/-- The bound of `le_inversionExperiment_dictionaryInverter` is a lower bound and can be strict:
with a constant `H` every output inverts, so a point mass outside the dictionary (`μ D = 0`) is
inverted with probability `1`. -/
example : (PMF.pure (2 : ℕ)).toOuterMeasure {pw | pw ∈ ([0, 1] : List ℕ)} = 0 ∧
    (inversionExperiment (PMF.pure (2 : ℕ)) (fun _ : ℕ => (0 : ℕ))
      (dictionaryInverter (fun _ : ℕ => (0 : ℕ)) id [0, 1])) true = 1 := by
  constructor
  · rw [PMF.toOuterMeasure_apply_eq_zero_iff]
    simp
  · rw [inversionExperiment_eq_bind_map, PMF.pure_bind, dictionaryInverter_apply, PMF.pure_map,
      PMF.pure_apply]
    simp

end CslibFrontierTests.Crypto.DictionarySearch
