/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Script
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.DSteps
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat

/-!
# Writing the units of strings into a trie

The program GROUP of [AnthropicVPVNP2026] keeps the units in a trie (`Interpreter.tset`,
`Interpreter.tget`), whose keys are bit lists. A string, closed by a final bit `1`, is cut into
units of `ub` bits, the last one filled up with zeros (`padTake`), which are written at given keys
(`putUnits`); the number of keys must be the number of units, otherwise nothing is written. Several
strings are written one after the other (`putStrings`).

One formula of the tree machine writes several strings, at a cost linear in the number of keys,
the length of the keys and `ub` (`putCost`).

## Main definitions

* `padTake`: the first `ub` bits of a string, filled up with zeros.
* `putUnits`, `putStrings`: write the units of one string and of several strings.
* `StoreBound`: every entry of a trie is a list of at most `ub` bits.

## Main results

* `StoreBound.nil`, `StoreBound.tset`, `StoreBound.tget`, `StoreBound.of_mem_putStrings`: the
  bound on the units holds for the empty trie and is kept by writing.
* `exists_formula_putStrings`: one formula writes several strings.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54); this file formalizes programs
of that evaluator, not the theorem. Ported from the source modules `Nc.Grp.PutDef`, `Nc.Grp.Put` and
`Nc.Grp.GroupProg`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The first `ub` bits of a string, filled up with zeros. -/
@[expose] def padTake (ub : ℕ) (r : List Bool) : List Bool :=
  r.take ub ++ List.replicate (ub - r.length) false

/-- Write the units of the string `r` at the keys: every key gets the next `ub` bits, filled up
with zeros (`padTake`); the result is empty if the string runs out before the keys or the keys
before the string. -/
@[expose] def putUnits (ub : ℕ) : List (List Bool) → List Bool → Tree → List Tree
  | [], r, t => if r = [] then [t] else []
  | k :: ks, r, t =>
    if r = [] then [] else putUnits ub ks (r.drop ub) (tset k (ofBits (padTake ub r)) t)

/-- Write the strings `strs` at the lists of keys `kss`, one after the other; a missing string is
empty. -/
@[expose] def putStrings (ub : ℕ) : List (List (List Bool)) → List (List Bool) → Tree →
    List Tree
  | [], _, t => [t]
  | ks :: kss, strs, t =>
    (putUnits ub ks (strs.headD []) t).flatMap (putStrings ub kss strs.tail)

/-- Every entry of the trie `t` is a list of at most `ub` bits. -/
@[expose] def StoreBound (ub : ℕ) (t : Tree) : Prop :=
  ∀ k, ∃ w : List Bool, tget k t = ofBits w ∧ w.length ≤ ub

private theorem length_padTake (ub : ℕ) (r : List Bool) : (padTake ub r).length = ub := by
  simp only [padTake, List.length_append, List.length_take, List.length_replicate]
  omega

theorem StoreBound.nil (ub : ℕ) : StoreBound ub .nil := fun _ => ⟨[], tget_nil _, Nat.zero_le _⟩

theorem StoreBound.tset {ub : ℕ} {t : Tree} (h : StoreBound ub t) (k w : List Bool)
    (hw : w.length ≤ ub) : StoreBound ub (tset k (ofBits w) t) := fun k' => by
  rw [tget_tset]
  split_ifs
  exacts [⟨w, rfl, hw⟩, h k']

/-- The entries of a bounded trie are bit lists. -/
theorem StoreBound.tget {ub : ℕ} {t : Tree} (h : StoreBound ub t) (k : List Bool) :
    Interpreter.tget k t = ofBits (Interpreter.tget k t).path ∧
      (Interpreter.tget k t).path.length ≤ ub := by
  obtain ⟨w, h1, h2⟩ := h k
  simpa [h1] using h2

private theorem StoreBound.of_mem_putUnits {ub : ℕ} {ks : List (List Bool)} {r : List Bool}
    {t t' : Tree} (h : StoreBound ub t) (ht' : t' ∈ putUnits ub ks r t) : StoreBound ub t' := by
  induction ks generalizing r t with
  | nil => by_cases hr : r = [] <;> simp_all [putUnits]
  | cons k ks ih =>
    simp only [putUnits] at ht'
    split_ifs at ht'
    exacts [absurd ht' List.not_mem_nil, ih (h.tset k _ (length_padTake _ _).le) ht']

theorem StoreBound.of_mem_putStrings {ub : ℕ} {kss : List (List (List Bool))}
    {strs : List (List Bool)} {t t' : Tree} (h : StoreBound ub t)
    (ht' : t' ∈ putStrings ub kss strs t) : StoreBound ub t' := by
  induction kss generalizing strs t with
  | nil => exact (List.mem_singleton.1 ht') ▸ h
  | cons ks kss ih =>
    obtain ⟨t1, h1, h2⟩ := List.mem_flatMap.1 ht'
    exact ih (h.of_mem_putUnits h1) h2

/-! ### The programs -/

private theorem padTake_succ (ub : ℕ) (r : List Bool) :
    padTake (ub + 1) r = r.headD false :: padTake ub r.tail := by
  cases r <;> simp [padTake, List.replicate_succ]

/-- Take the bits of a unit: the argument is (yardstick element, (rest, unit so far)). -/
private def unitStep : Fm :=
  .cons (.tl (.hd (.tl .id))) (.cons (.hd (.hd (.tl .id))) (.tl (.tl .id)))

/-- The unit at the front of a string, reversed, and the rest of the string. -/
private theorem unit_gives {s y : Fm} {x : Tree} {cs cy ub : ℕ} {r : List Bool}
    (hs : Gives θ s x (ofBits r) cs) (hy : Gives θ y x (num ub) cy) :
    Gives θ (foldF unitStep (.cons s (.quote .nil)) y) x
      (.cons (ofBits (r.drop ub)) (ofBits (padTake ub r).reverse)) (cs + cy + ub * 50 + 40) := by
  have h := foldF_gives_enc (θ := θ) (encE := fun _ : Unit => (.nil : Tree))
    (enc := fun s : List Bool × List Bool => .cons (ofBits s.1) (ofBits s.2)) (s₀ := (r, []))
    (g := fun _ s => (s.1.tail, s.1.headD false :: s.2)) (Inv := fun _ _ => True)
    (d := fun _ => 20) (step := unitStep) (xs := List.replicate ub ()) (hs.cons (Gives.quote _ _))
    (by simpa [← num_eq_listT_replicate] using hy) (fun _ _ s _ _ => by
      have g : Gives θ (.hd (.tl .id)) (.cons .nil (.cons (ofBits s.1) (ofBits s.2))) (ofBits s.1)
        3 := (Gives.id _).tl.hd
      exact ⟨((tl_ofBits s.1 ▸ g.tl).cons ((hd_ofBits s.1 ▸ g.hd).cons
        (Gives.id _).tl.tl)).mono (by omega), trivial⟩) trivial
  have e (ub : ℕ) (r acc : List Bool) : (List.replicate ub ()).foldl
      (fun s _ => (s.1.tail, s.1.headD false :: s.2)) (r, acc) =
        (r.drop ub, (padTake ub r).reverse ++ acc) := by
    induction ub generalizing r acc with
    | zero => simp [padTake]
    | succ ub ih =>
      rw [List.replicate_succ, List.foldl_cons, ih, padTake_succ]
      simp
  rw [e, List.append_nil] at h
  exact h.mono (by simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]; omega)

/-- Write one unit: the argument is (key, (yardstick, (rest, trie))). -/
private def putStep : Fm := .ite (.hd (.tl (.tl .id)))
  (lett (.cons .id (foldF unitStep (.cons (.hd (.tl (.tl .id))) (.quote .nil)) (.hd (.tl .id))))
    (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl .id)) (setF (.hd (.hd .id))
      (foldF .id (.quote (ofBits [])) (.tl (.tl .id))) (.tl (.tl (.tl (.hd .id))))))))
  .fail

variable (A) in
/-- One unit, on the rest of the string and the trie. -/
private def putOne (ub : ℕ) (k : List Bool) (s : List Bool × Tree) :
    List (A × (List Bool × Tree)) :=
  if s.1 = [] then [] else [(1, (s.1.drop ub, tset k (ofBits (padTake ub s.1)) s.2))]

private theorem putStep_does (ub : ℕ) (k : List Bool) (s : List Bool × Tree) :
    Does θ putStep (.cons (ofBits k) (.cons (num ub) (.cons (ofBits s.1) s.2)))
      ((putOne A ub k s).map (Prod.map id fun s => .cons (num ub) (.cons (ofBits s.1) s.2)))
      (400 * (ub + k.length + 1)) := by
  obtain ⟨r, t⟩ := s
  cases r with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl.hd (Does.fail _)).mono (by omega)
  | cons b r =>
    have h1 := unit_gives (θ := θ) (r := b :: r) (Gives.id (.cons (ofBits k)
      (.cons (num ub) (.cons (ofBits (b :: r)) t)))).tl.tl.hd (Gives.id _).tl.hd
    have h2 := Gives.letk h1 ((Gives.id _).hd.tl.hd.cons ((Gives.id _).tl.hd.cons
      (setF_gives (Gives.id _).hd.hd (rev_gives_ofBits (Gives.quote (ofBits []) _)
        (Gives.id _).tl.tl) (Gives.id _).hd.tl.tl.tl)))
    simp only [hd_cons, tl_cons, List.reverse_reverse, List.append_nil, path_ofBits] at h2
    refine (Does.ite_true (Gives.id _).tl.tl.hd (by simp [ofBits]) h2).mono ?_
    simp only [List.length_reverse, length_padTake, len_ofBits]
    omega

/-- Write the units of a string: the argument is (yardstick, (keys, (string, trie))). -/
private def putF : Fm := lett (foldF putStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id)))
  (.ite (.hd (.tl .id)) .fail (.tl (.tl .id)))

private theorem putF_does (ub : ℕ) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    Does θ putF (.cons (num ub) (.cons (wordsEnc keys) (.cons (ofBits r) t)))
      ((putUnits ub keys r t).map ((1 : A), ·))
      (430 * (keys.map fun k => ub + k.length + 1).sum + 100) := by
  have h1 := foldF_does_enc (θ := θ) (encE := ofBits) (xs := keys)
    (x := .cons (num ub) (.cons (wordsEnc keys) (.cons (ofBits r) t)))
    (enc := fun s : List Bool × Tree => .cons (num ub) (.cons (ofBits s.1) s.2)) (s₀ := (r, t))
    (f := putOne A ub) (Inv := fun _ _ => True) (d := fun k => 400 * (ub + k.length + 1))
    ((Gives.id _).hd.cons (Gives.id _).tl.tl) (Gives.id _).tl.hd
    (fun k _ s _ _ => ⟨putStep_does ub k s, fun _ _ => trivial⟩) trivial
  have h2 := Does.lett_enc (G := .ite (.hd (.tl .id)) .fail (.tl (.tl .id)))
    (f := fun s : List Bool × Tree => if s.1 = [] then [((1 : A), s.2)] else []) (d := 20) h1
    fun ⟨a, r, t⟩ _ => by
      cases r with
      | nil => exact (Does.ite_false (Gives.id _).tl.hd (Gives.id _).tl.tl).mono (by omega)
      | cons b r => exact (Does.ite_true (Gives.id _).tl.hd (by simp [ofBits])
          (Does.fail _)).mono (by omega)
  have e (keys : List (List Bool)) (r : List Bool) (t : Tree) :
      (keys.weightedFoldl (putOne A ub) (r, t)).weightedBind
        (fun s => if s.1 = [] then [((1 : A), s.2)] else []) =
        (putUnits ub keys r t).map (1, ·) := by
    induction keys generalizing r t with
    | nil => by_cases h : r = [] <;> simp [h, putUnits]
    | cons k ks ih =>
      by_cases h : r = []
      · simp [h, putUnits, putOne, List.weightedBind]
      · simp only [List.weightedFoldl_cons, putOne, putUnits, h, ↓reduceIte,
          List.weightedBind_singleton_one, ih]
  rw [e] at h2
  refine h2.mono ?_
  have := List.sum_le_sum (l := keys) (f := fun k => 400 * (ub + k.length + 1) + 30)
    (g := fun k => 430 * (ub + k.length + 1)) fun k _ => by omega
  rw [List.sum_map_mul_left] at this
  omega

/-- Write one string of several: the argument is (keys, (yardstick, (strings, trie))). -/
private def putsStep : Fm := .cons (.hd (.tl .id)) (.cons (.tl (.hd (.tl (.tl .id))))
  (lett (.cons (.hd (.tl .id)) (.cons (.hd .id) (.cons (.hd (.hd (.tl (.tl .id))))
    (.tl (.tl (.tl .id)))))) putF))

/-- **One formula writes several strings.** Its argument is (`num ub`, (lists of keys, (strings,
trie))). -/
theorem exists_formula_putStrings : ∃ F, ∀ (ub : ℕ) (kss : List (List (List Bool)))
    (strs : List (List Bool)) (t : Tree),
    Does θ F (.cons (num ub) (.cons (keysEnc kss) (.cons (wordsEnc strs) t)))
      ((putStrings ub kss strs t).map ((1 : A), ·)) (600 * (putCost ub kss + 1)) := by
  refine ⟨lett (foldF putsStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id))) (.tl (.tl .id)),
    fun ub kss strs t => ?_⟩
  have h1 := foldF_does_enc (θ := θ) (encE := wordsEnc) (xs := kss)
    (enc := fun s : List (List Bool) × Tree => .cons (num ub) (.cons (wordsEnc s.1) s.2))
    (s₀ := (strs, t)) (f := fun ks s => (putUnits ub ks (s.1.headD []) s.2).map fun t =>
      ((1 : A), (s.1.tail, t))) (Inv := fun _ _ => True)
    (d := fun ks => 430 * (ks.map fun k => ub + k.length + 1).sum + 140)
    (x := .cons (num ub) (.cons (keysEnc kss) (.cons (wordsEnc strs) t)))
    ((Gives.id _).hd.cons (Gives.id _).tl.tl) (Gives.id _).tl.hd (fun ks _ s _ _ => by
      set y := Tree.cons (wordsEnc ks) (.cons (num ub) (.cons (wordsEnc s.1) s.2))
      have g : Gives θ (.hd (.tl (.tl .id))) y (wordsEnc s.1) 4 := (Gives.id _).tl.tl.hd
      have e := Does.of_gives ((Gives.id y).tl.hd.cons ((Gives.id y).hd.cons
        ((hd_wordsEnc s.1 ▸ g.hd).cons (Gives.id y).tl.tl.tl)))
        (putF_does (θ := θ) (A := A) ub ks (s.1.headD []) s.2)
      refine ⟨((Does.cons (Gives.id y).tl.hd (Does.cons (tl_wordsEnc s.1 ▸ g.tl) e)).of_eq
        ?_).mono (by omega), fun _ _ => trivial⟩
      simp [y, Function.comp_def]) trivial
  have h2 := Does.lett_enc (G := .tl (.tl .id))
    (f := fun s : List (List Bool) × Tree => [((1 : A), s.2)]) (d := 3) h1
    fun _ _ => (Gives.id _).tl.tl
  have e (kss : List (List (List Bool))) (strs : List (List Bool)) (t : Tree) :
      (kss.weightedFoldl (fun ks s => (putUnits ub ks (s.1.headD []) s.2).map fun t =>
        ((1 : A), (s.1.tail, t))) (strs, t)).weightedBind (fun s => [((1 : A), s.2)]) =
        (putStrings ub kss strs t).map (1, ·) := by
    induction kss generalizing strs t with
    | nil => simp [putStrings]
    | cons ks kss ih =>
      rw [List.weightedFoldl_cons, List.weightedBind_assoc, List.weightedBind_map_one]
      simp only [ih, putStrings, List.map_flatMap]
  rw [e] at h2
  refine h2.mono ?_
  have := List.sum_le_sum (l := kss)
    (f := fun ks => 430 * (ks.map fun k => ub + k.length + 1).sum + 140 + 30)
    (g := fun ks => 600 * ((ks.map fun k => ub + k.length + 1).sum + 1)) fun k _ => by omega
  rw [List.sum_map_mul_left] at this
  simp only [putCost]
  omega

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
