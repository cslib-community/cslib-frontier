/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Script
public import CslibFrontier.Foundations.Data.List.Weighted
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# Cutting the letters of a tape into segments

A base party of the evaluator of [AnthropicVPVNP2026] writes on every tape a list of letters, and
the letters are cut into one segment for every partner. The letters come in reverse order, and
the segments are made from the last partner to the first one: the letters of the partner at hand
are taken one at a time, then its segment is closed and the next partner begins. Every segment is
closed by a separator and stands in front of the string that the partner has from the later tapes.
A flag of every partner says whether it gets nothing, something or anything (`flagAllows`).

One formula of the tree machine makes all cuts of the letters of a list of tapes, one tape after
the other, as a weighted list in which every cut has the weight `1`.

## Main definitions

* `flagAllows`: whether a flag allows what has been taken.
* `cuts`, `cutsClose`, `cutsTake`: all ways to cut the remaining letters.
* `tapeCuts`: all ways to cut the letters of a tape.
* `CutItem`, `CutItem.enc`: the flags and the letters of a tape, and their encoding.
* `cutTape`, `cutTapes`: the weighted lists of the cuts of one tape and of a list of tapes.

## Main results

* `length_le_of_mem_cutTapes`: the number of strings of a cut.
* `exists_formula_cutTapes`: one formula makes the cuts of a list of tapes.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54); this file formalizes programs
of that evaluator, not the theorem. Ported from the source modules `Nc.Grp.Seg` and `Nc.Grp.Base`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Whether a flag allows a segment: the flag `0` that nothing has been taken, the flag `1` that
something has been taken, and every other flag anything. -/
@[expose] def flagAllows : ℕ → Bool → Bool
  | 0, taken => !taken
  | 1, taken => taken
  | _, _ => true

/-- All ways to cut the letters `rest` with the separator `sep`. The partner at hand has the flag
`f`, `tk` says whether a letter has been taken for it, and `cur` is its string so far; `fs` and
`as` are the flags and the strings from the later tapes of the partners before it, and `out` are
the finished strings of the partners behind it. -/
def cuts (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ)
    (as rest out : List (List Bool)) : List (List (List Bool)) :=
  (if flagAllows f tk then
    match fs with
    | [] => if rest = [] then [cur :: out] else []
    | f' :: fs' => cuts sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)
  else []) ++
  match rest with
  | [] => []
  | a :: r => cuts sep f true (a ++ cur) fs as r out
termination_by fs.length + rest.length

/-- The cuts after the segment of the partner at hand is closed. -/
@[expose] def cutsClose (sep cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    List (List (List Bool)) :=
  match fs with
  | [] => if rest = [] then [cur :: out] else []
  | f' :: fs' => cuts sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)

/-- The cuts after a letter is taken for the partner at hand. -/
@[expose] def cutsTake (sep : List Bool) (f : ℕ) (cur : List Bool) (fs : List ℕ)
    (as rest out : List (List Bool)) : List (List (List Bool)) :=
  match rest with
  | [] => []
  | a :: r => cuts sep f true (a ++ cur) fs as r out

theorem cuts_eq (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ)
    (as rest out : List (List Bool)) : cuts sep f tk cur fs as rest out =
      (if flagAllows f tk then cutsClose sep cur fs as rest out else []) ++
        cutsTake sep f cur fs as rest out := by
  rw [cuts.eq_def]
  cases fs <;> cases rest <;> rfl

/-- All ways to cut the letters `l` of a tape, for partners with the flags `fl` and the strings
`accs` from the later tapes; none if there is no partner. -/
@[expose] def tapeCuts (sep : List Bool) (fl : List ℕ) (accs l : List (List Bool)) :
    List (List (List Bool)) :=
  match fl with
  | [] => []
  | f :: fs => cuts sep f false (sep ++ accs.headD []) fs accs.tail l []

/-- A tape to be cut. -/
structure CutItem where
  /-- The flags of the partners, the last partner first. -/
  flags : List ℕ
  /-- The letters, in reverse order. -/
  letters : List (List Bool)

/-- A `CutItem` as a tree. -/
@[expose] def CutItem.enc (it : CutItem) : Tree :=
  .cons (listT (it.flags.map num)) (wordsEnc it.letters)

variable (A) in
/-- The cuts of one tape as a weighted list with weights `1`, the strings of the partners in the
order of their flags. -/
@[expose] def cutTape (sep : List Bool) (it : CutItem) (accs : List (List Bool)) :
    List (A × List (List Bool)) :=
  (tapeCuts sep it.flags accs it.letters).map fun out => ((1 : A), out.reverse)

variable (A) in
/-- The cuts of a list of tapes, the last tape first. -/
@[expose] def cutTapes (sep : List Bool) (items : List CutItem) (accs : List (List Bool)) :
    List (A × List (List Bool)) :=
  items.weightedFoldl (cutTape A sep) accs

/-- Every cut has one string for every partner. -/
private theorem length_of_mem_cuts {sep cur : List Bool} {f : ℕ} {tk : Bool} {fs : List ℕ}
    {as rest out l : List (List Bool)} (h : l ∈ cuts sep f tk cur fs as rest out) :
    l.length = fs.length + out.length + 1 := by
  induction hn : fs.length + rest.length using Nat.strong_induction_on
    generalizing f tk cur fs as rest out with
  | _ n ih =>
  rw [cuts_eq, List.mem_append] at h
  rcases h with h | h
  · split_ifs at h
    · cases fs with
      | nil =>
        simp only [cutsClose] at h
        split_ifs at h
        · simp [List.mem_singleton.1 h]
        · simp at h
      | cons f' fs' =>
        have := ih _ (by simp only [List.length_cons] at hn; omega) h rfl
        simp only [List.length_cons] at this ⊢
        omega
    · simp at h
  · cases rest with
    | nil => simp [cutsTake] at h
    | cons a r => exact ih _ (by simp only [List.length_cons] at hn; omega) h rfl

/-- Every outcome of the cuts of a list of tapes has at most `N` strings if every tape has at most
`N` partners and there are at most `N` strings at the beginning. -/
theorem length_le_of_mem_cutTapes {sep : List Bool} {items : List CutItem}
    {accs : List (List Bool)} {N : ℕ} (h : ∀ it ∈ items, it.flags.length ≤ N)
    (ha : accs.length ≤ N) : ∀ r ∈ cutTapes A sep items accs, r.2.length ≤ N := by
  intro r hr
  simpa using List.mem_weightedFoldl_induction (Inv := fun _ s => s.length ≤ N) (m := 0)
    (fun it hit s _ _ q hq => by
      obtain ⟨out, hout, rfl⟩ := List.mem_map.1 hq
      have h1 := h it hit
      unfold tapeCuts at hout
      split at hout
      · exact absurd hout List.not_mem_nil
      · rename_i f fs hfl
        have := length_of_mem_cuts hout
        rw [hfl] at h1
        simp only [List.length_reverse, List.length_cons, List.length_nil] at this h1 ⊢
        omega) ha r hr

/-! ### The program -/

/-- The state of the cutting program. -/
private def segState (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ)
    (as rest out : List (List Bool)) : Tree :=
  listT [num f, bit tk, ofBits cur, listT (fs.map num), wordsEnc as, wordsEnc rest, wordsEnc out]

/-- A field of the state, in the argument (program, state). -/
private abbrev fld (i : ℕ) : Fm := nthF i (.tl .id)

/-- Close the segment: go on with the next partner, or stop if there is none and no letter is
left. -/
private def closeF (sep : List Bool) : Fm :=
  .ite (fld 3) (.run (.hd .id) (.cons (.hd .id) (listF [.hd (fld 3), .quote .nil,
      appF (.quote (ofBits sep)) (.hd (fld 4)), .tl (fld 3), .tl (fld 4), fld 5,
      .cons (fld 2) (fld 6)])))
    (.ite (fld 5) .fail (.cons (fld 2) (fld 6)))

/-- Take a letter. -/
private def takeF : Fm :=
  .ite (fld 5) (.run (.hd .id) (.cons (.hd .id) (listF [fld 0, .quote one,
    appF (.hd (fld 5)) (fld 2), fld 3, fld 4, .tl (fld 5), fld 6]))) .fail

/-- The cutting program: close the segment if the flag allows it, or take a letter. -/
private def segB (sep : List Bool) : Fm :=
  .ite .guess (.ite (fld 0) (.ite (.tl (fld 0)) (closeF sep) (.ite (fld 1) (closeF sep) .fail))
    (.ite (fld 1) .fail (closeF sep))) takeF

/-- **The cutting program makes all cuts**, at a cost linear in the number of letters and
partners. -/
private theorem segB_does {sep : List Bool} {c : ℕ} (hsep : sep.length ≤ c) (n : ℕ) :
    ∀ f tk cur fs as rest out, fs.length + rest.length = n → (∀ a ∈ rest, a.length ≤ c) →
      Does θ (segB sep) (.cons (segB sep).code (segState f tk cur fs as rest out))
        ((cuts sep f tk cur fs as rest out).map fun o => ((1 : A), wordsEnc o))
        ((62 * c + 300) * (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f tk cur fs as rest out hn hc
  set x := Tree.cons (segB sep).code (segState f tk cur fs as rest out)
  have hx : Gives θ .id x x 1 := Gives.id x
  have g0 : Gives θ (fld 0) x (num f) 3 := nthF_gives 0 hx.tl
  have g1 : Gives θ (fld 1) x (bit tk) 4 := nthF_gives 1 hx.tl
  have g2 : Gives θ (fld 2) x (ofBits cur) 5 := nthF_gives 2 hx.tl
  have g3 : Gives θ (fld 3) x (listT (fs.map num)) 6 := nthF_gives 3 hx.tl
  have g4 : Gives θ (fld 4) x (wordsEnc as) 7 := nthF_gives 4 hx.tl
  have g5 : Gives θ (fld 5) x (wordsEnc rest) 8 := nthF_gives 5 hx.tl
  have g6 : Gives θ (fld 6) x (wordsEnc out) 9 := nthF_gives 6 hx.tl
  -- a recursive call
  have hrec : ∀ f tk cur fs' as rest' out, fs'.length + rest'.length < n →
      (∀ a ∈ rest', a.length ≤ c) → Does θ (Fm.ofTree (segB sep).code)
        (.cons (segB sep).code (segState f tk cur fs' as rest' out))
        ((cuts sep f tk cur fs' as rest' out).map fun o => ((1 : A), wordsEnc o))
        ((62 * c + 300) * n) := fun f tk cur fs' as rest' out h1 h2 => by
    rw [Fm.ofTree_code]
    exact (ih _ h1 f tk cur fs' as rest' out rfl h2).mono (Nat.mul_le_mul_left _ h1)
  have hclose : Does θ (closeF sep) x
      ((cutsClose sep cur fs as rest out).map fun o => ((1 : A), wordsEnc o))
      ((62 * c + 300) * n + 62 * c + 200) := by
    cases fs with
    | nil =>
      cases rest with
      | nil => exact (Does.ite_false g3 (Does.ite_false g5 (g2.cons g6))).mono (by omega)
      | cons a r => exact (Does.ite_false g3 (Does.ite_true g5 (by simp [wordsEnc, listT])
          (Does.fail x))).mono (by omega)
    | cons f' fs' =>
      have e : Gives θ (appF (.quote (ofBits sep)) (.hd (fld 4))) x (ofBits (sep ++ as.headD []))
          _ := appF_gives_ofBits (Gives.quote _ x) (hd_wordsEnc as ▸ g4.hd)
      refine (Does.ite_true g3 (by simp [listT]) (Does.run hx.hd (hx.hd.cons (g3.hd.cons
        ((Gives.quote _ x).cons (e.cons (g3.tl.cons ((tl_wordsEnc as ▸ g4.tl).cons
        (g5.cons ((g2.cons g6).cons (Gives.quote _ x))))))))) (hrec f' false
        (sep ++ as.headD []) fs' as.tail rest (cur :: out)
        (by simp only [List.length_cons] at hn; omega) hc))).mono (by omega)
  have htake : Does θ takeF x ((cutsTake sep f cur fs as rest out).map fun o =>
      ((1 : A), wordsEnc o)) ((62 * c + 300) * n + 62 * c + 200) := by
    cases rest with
    | nil => exact (Does.ite_false g5 (Does.fail x)).mono (by omega)
    | cons a r =>
      have ha := hc a List.mem_cons_self
      refine (Does.ite_true g5 (by simp [wordsEnc, listT]) (Does.run hx.hd (hx.hd.cons (g0.cons
        ((Gives.quote _ x).cons ((appF_gives_ofBits g5.hd g2).cons (g3.cons (g4.cons
        (g5.tl.cons (g6.cons (Gives.quote _ x))))))))) (hrec f true (a ++ cur) fs as r out
        (by simp only [List.length_cons] at hn; omega)
        fun b hb => hc b (List.mem_cons_of_mem _ hb)))).mono (by omega)
  have hflag : Does θ (.ite (fld 0) (.ite (.tl (fld 0)) (closeF sep) (.ite (fld 1) (closeF sep)
      .fail)) (.ite (fld 1) .fail (closeF sep))) x
      ((if flagAllows f tk then cutsClose sep cur fs as rest out else []).map fun o =>
        ((1 : A), wordsEnc o)) ((62 * c + 300) * n + 62 * c + 230) := by
    rcases f with _ | _ | f <;> cases tk
    · exact (Does.ite_false g0 (Does.ite_false g1 hclose)).mono (by omega)
    · exact (Does.ite_false g0 (Does.ite_true g1 (by simp [bit, one]) (Does.fail x))).mono
        (by omega)
    · exact (Does.ite_true g0 (by simp [num]) (Does.ite_false g0.tl (Does.ite_false g1
        (Does.fail x)))).mono (by omega)
    · exact (Does.ite_true g0 (by simp [num]) (Does.ite_false g0.tl (Does.ite_true g1
        (by simp [bit, one]) hclose))).mono (by omega)
    all_goals exact (Does.ite_true g0 (by simp [num]) (Does.ite_true g0.tl (by simp [num])
      hclose)).mono (by omega)
  refine ((Does.either hflag htake).of_eq ?_).mono ?_
  · rw [cuts_eq, List.map_append]
  · rw [Nat.mul_succ]
    omega

/-- One tape: the argument is (item, strings from the later tapes). -/
private def tapeF (sep : List Bool) : Fm :=
  .ite (.hd (.hd .id)) (lett (lett (.cons (.quote (segB sep).code) (listF [.hd (.hd (.hd .id)),
      .quote .nil, appF (.quote (ofBits sep)) (.hd (.tl .id)), .tl (.hd (.hd .id)), .tl (.tl .id),
      .tl (.hd .id), .quote .nil])) (segB sep)) (foldF .id (.quote .nil) .id)) .fail

private theorem tapeF_does {sep : List Bool} {c : ℕ} (hsep : sep.length ≤ c) (it : CutItem)
    (accs : List (List Bool)) (hc : ∀ a ∈ it.letters, a.length ≤ c) :
    Does θ (tapeF sep) (.cons it.enc (wordsEnc accs))
      ((cutTape A sep it accs).map (Prod.map id wordsEnc))
      ((62 * c + 700) * (it.flags.length + it.letters.length + 1)) := by
  obtain ⟨fl, l⟩ := it
  set x := Tree.cons (CutItem.enc ⟨fl, l⟩) (wordsEnc accs)
  have hx : Gives θ .id x x 1 := Gives.id x
  dsimp only at hc ⊢
  cases fl with
  | nil => exact ((Does.ite_false hx.hd.hd (Does.fail x)).of_eq rfl).mono (by nlinarith)
  | cons f fs =>
    have e1 : Gives θ (.cons (.quote (segB sep).code) (listF [.hd (.hd (.hd .id)), .quote .nil,
        appF (.quote (ofBits sep)) (.hd (.tl .id)), .tl (.hd (.hd .id)), .tl (.tl .id),
        .tl (.hd .id), .quote .nil])) x (.cons (segB sep).code
          (segState f false (sep ++ accs.headD []) fs accs.tail l [])) (62 * c + 100) :=
      ((Gives.quote _ x).cons (hx.hd.hd.hd.cons ((Gives.quote _ x).cons
        ((appF_gives_ofBits (Gives.quote _ x) (hd_wordsEnc accs ▸ hx.tl.hd)).cons
        (hx.hd.hd.tl.cons ((tl_wordsEnc accs ▸ hx.tl.tl).cons (hx.hd.tl.cons
        ((Gives.quote _ x).cons (Gives.quote _ x))))))))).mono (by omega)
    have e2 := Does.of_gives e1 (segB_does (θ := θ) (A := A) hsep _ f false _ fs accs.tail l []
      rfl hc)
    have e3 := Does.lett_enc_enc (l := (cuts sep f false (sep ++ accs.headD []) fs accs.tail l
      []).map ((1 : A), ·)) (enc := wordsEnc) (f := fun o => [((1 : A), o.reverse)])
      (enc' := wordsEnc) (G := foldF .id (.quote .nil) .id) (d := (fs.length + 1) * 31 + 22)
      (by simpa [Function.comp_def] using e2) fun b hb => by
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hb
        have h := rev_gives (θ := θ) (Gives.quote (listT []) (wordsEnc o)) (Gives.id _)
        simp only [wordsEnc, List.append_nil, ← List.map_reverse, List.length_map,
          length_of_mem_cuts ho, List.length_nil] at h ⊢
        exact h.mono (by omega)
    refine ((Does.ite_true hx.hd.hd (by simp [x, CutItem.enc, listT]) e3).of_eq ?_).mono ?_
    · simp [cutTape, tapeCuts, List.weightedBind, List.flatMap_map, ← List.map_eq_flatMap,
        Function.comp_def]
    · simp only [List.length_cons]
      nlinarith

/-- **One formula makes the cuts of a list of tapes.** Its argument is the pair of the list of the
items of the tapes, the last tape first, and the strings of the partners from the later tapes. -/
theorem exists_formula_cutTapes (sep : List Bool) : ∃ F, ∀ (c N : ℕ) (items : List CutItem)
    (accs : List (List Bool)), sep.length ≤ c →
      (∀ it ∈ items, it.flags.length + it.letters.length ≤ N ∧ ∀ a ∈ it.letters, a.length ≤ c) →
      Does θ F (.cons (listT (items.map CutItem.enc)) (wordsEnc accs))
        ((cutTapes A sep items accs).map (Prod.map id wordsEnc))
        ((62 * c + 800) * (items.length * (N + 1) + 1)) := by
  refine ⟨foldF (tapeF sep) (.tl .id) (.hd .id), fun c N items accs hsep hc => ?_⟩
  have h := foldF_does_enc (θ := θ) (encE := CutItem.enc) (enc := wordsEnc) (f := cutTape A sep)
    (x := .cons (listT (items.map CutItem.enc)) (wordsEnc accs)) (xs := items)
    (Inv := fun _ _ => True)
    (d := fun it => (62 * c + 700) * (it.flags.length + it.letters.length + 1))
    (Gives.id _).tl (Gives.id _).hd (fun it _ accs hit _ =>
      ⟨tapeF_does hsep it accs (hc it hit).2, fun _ _ => trivial⟩) trivial
  refine h.mono ?_
  have h1 := List.sum_le_length_nsmul (items.map fun it =>
    (62 * c + 700) * (it.flags.length + it.letters.length + 1) + 30)
    ((62 * c + 700) * (N + 1) + 30) fun y hy => by
      obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hy
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by have := (hc it hit).1; omega)) 30
  have h2 : items.length * ((62 * c + 700) * (N + 1) + 30) ≤
      (62 * c + 800) * (items.length * (N + 1)) := by nlinarith
  rw [List.length_map, smul_eq_mul] at h1
  rw [mul_add_one]
  omega

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
