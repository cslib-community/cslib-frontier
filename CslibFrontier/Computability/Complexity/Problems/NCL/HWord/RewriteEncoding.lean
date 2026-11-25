/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteGadget
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.OfFn

/-!
# Overlapping-pair encodings and their local decoder

Source words are encoded by a start marker, overlapping adjacent pairs with exterior blanks,
and a finish marker. A source letter is read from the two pair positions that share it. The
decoder also reads arbitrary legal intermediate H-words, which may contain rule markers.

## Main definitions

* `HWord.RewriteGadget.encode`, `HWord.RewriteGadget.word`: symbolic and coded source words.
* `HWord.RewriteGadget.wordList`: the list algorithm for the same canonical encoding.
* `HWord.RewriteGadget.decode`: the partial local decoder on arbitrary coded words.

## Main results

* `HWord.RewriteGadget.word_legal`: canonical encoded words are legal.
* `HWord.RewriteGadget.decode_word`: canonical decoding recovers every source letter.
* `HWord.RewriteGadget.decode_some`: every source position decodes in every legal H-word.
* `HWord.RewriteGadget.readout_word`: the total source readout retracts canonical encodings.
* `HWord.RewriteGadget.Application.rewrites`: an indexed rule occurrence is a standard
  semi-Thue rewrite.
* `HWord.RewriteGadget.rule_word_reachable`: every rule occurrence reconfigures the complete
  canonical source word.
* `HWord.RewriteGadget.reachable_boundaries`: canonical end markers stay fixed along every
  legal intermediate trajectory.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014],
  arXiv:1405.0847v1, Section 3, proof of Theorem 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

variable {n q r : ℕ}

private def padded (s : Fin n → Fin q) (i : ℕ) : Option (Fin q) :=
  if hi : 1 ≤ i ∧ i ≤ n then some (s ⟨i - 1, by omega⟩) else none

private theorem padded_at (s : Fin n → Fin q) (i : Fin n) :
    padded s (i.val + 1) = some (s i) := by
  rw [padded, dite_eq_left (by constructor <;> omega)]
  congr 1

/-- A source word as overlapping pairs with two fixed end markers. -/
def encode (s : Fin n → Fin q) (i : Fin (n + 3)) : Symbol q r :=
  if i.val = 0 then .start else if i.val = n + 2 then .finish else
    .pair (padded s (i.val - 1)) (padded s i.val)

/-- The canonical encoded word over the fixed finite target alphabet. -/
noncomputable def word (s : Fin n → Fin q) : Fin (n + 3) → Fin (Fintype.card (Symbol q r)) :=
  code ∘ encode s

/-- Compute the canonical word by zipping the two blank-padded copies of the source list. -/
@[expose] noncomputable def wordList (s : List (Fin q)) :
    List (Fin (Fintype.card (Symbol q r))) :=
  code .start :: ((none :: s.map some).zip (s.map some ++ [none])).map
    (fun p => code (.pair p.1 p.2)) ++ [code .finish]

/-- The canonical word begins with the left end marker. -/
theorem word_start (s : Fin n → Fin q) : word (r := r) s 0 = code .start := by
  simp [word, encode]

/-- The canonical word ends with the right end marker. -/
theorem word_finish (s : Fin n → Fin q) :
    word (r := r) s ⟨n + 2, by omega⟩ = code .finish := by
  rw [word, Function.comp_apply, encode, ite_eq_right (by change n + 2 ≠ 0; omega),
    ite_eq_left rfl]

private theorem encode_pair (s : Fin n → Fin q) (i : Fin (n + 1)) :
    encode (r := r) s ⟨i.val + 1, by omega⟩ =
      .pair (padded s i.val) (padded s (i.val + 1)) := by
  rw [encode, ite_eq_right (by change i.val + 1 ≠ 0; omega),
    ite_eq_right (by change i.val + 1 ≠ n + 2; omega)]
  congr 1

private theorem zipWith_ofFn {α β γ : Type} (f : α → β → γ) {m : ℕ}
    (a : Fin m → α) (b : Fin m → β) :
    (List.ofFn a).zipWith f (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction m with
  | zero => simp
  | succ m ih => simp only [List.ofFn_succ, List.zipWith_cons_cons, ih]

private theorem padded_left (s : Fin n → Fin q) :
    List.ofFn (fun i : Fin (n + 1) => padded s i.val) = none :: (List.ofFn s).map some := by
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Fin.val_succ, padded_at]
  rw [List.ofFn_comp']
  simp [padded]

private theorem padded_right (s : Fin n → Fin q) :
    List.ofFn (fun i : Fin (n + 1) => padded s (i.val + 1)) =
      (List.ofFn s).map some ++ [none] := by
  rw [List.ofFn_succ']
  simp only [Fin.val_castSucc, padded_at, Fin.val_last, List.ofFn_comp']
  simp [padded, List.concat_eq_append]

/-- The list algorithm produces exactly the canonical finite-vector word. -/
theorem wordList_ofFn (s : Fin n → Fin q) :
    wordList (r := r) (List.ofFn s) = List.ofFn (word s) := by
  have hp : (fun i : Fin (n + 1) => word (r := r) s i.castSucc.succ) =
      fun i => code (.pair (padded s i.val) (padded s (i.val + 1))) := by
    funext i
    exact congrArg code (encode_pair s i)
  have hf : word (r := r) s (Fin.last (n + 1)).succ = code .finish := word_finish s
  have hw : List.ofFn (word (r := r) s) = code .start ::
      List.ofFn (fun i : Fin (n + 1) =>
        code (.pair (padded s i.val) (padded s (i.val + 1)))) ++ [code .finish] := by
    rw [List.ofFn_succ, word_start, List.ofFn_succ', hp, hf, List.concat_eq_append,
      List.cons_append]
  rw [wordList, ← padded_left, ← padded_right, List.map_zip_eq_zipWith, zipWith_ofFn, hw]
  rfl

/-- The first pair position sharing a source letter ends in that letter. -/
theorem encode_right (s : Fin n → Fin q) (i : Fin n) :
    ∃ a, encode (r := r) s ⟨i.val + 1, by omega⟩ = .pair a (some (s i)) := by
  rw [encode_pair s ⟨i.val, by omega⟩, padded_at]
  exact ⟨_, rfl⟩

/-- The second pair position sharing a source letter begins with that letter. -/
theorem encode_left (s : Fin n → Fin q) (i : Fin n) :
    ∃ b, encode (r := r) s ⟨i.val + 2, by omega⟩ = .pair (some (s i)) b := by
  have h := encode_pair (r := r) s ⟨i.val + 1, by omega⟩
  rw [padded_at] at h
  exact ⟨_, h⟩

/-- Canonical overlapping-pair encodings satisfy the compiled compatibility relation. -/
theorem word_legal (rules : Fin r → Rule q) (s : Fin n → Fin q) (hn : 0 < n) :
    HWord.Legal (compatibility rules) (word s) := by
  intro i j hij
  apply (compatibility_adj rules _ _).mpr
  by_cases hi : i.val = 0
  · have hj : j.val = 1 := by omega
    simp [encode, hi, hj, padded, Compatible]
    omega
  · by_cases hj : j.val = n + 2
    · have hi' : i.val = n + 1 := by omega
      simp [encode, hi', hj, padded, Compatible]
      omega
    · have hi' : 1 ≤ i.val ∧ i.val ≤ n := by omega
      have hj' : ¬j.val = 0 := by omega
      have hin : ¬i.val = n + 2 := by omega
      have hp : padded s i.val = some (s ⟨i.val - 1, by omega⟩) :=
        dite_eq_left hi'
      have he : j.val - 1 = i.val := by omega
      simp only [encode, hi, hj, hj', hin, Compatible, he, hp]
      exact ⟨_, rfl, rfl⟩

/-- Read a shared source letter from a pair on its left, or from the pair on its right. -/
@[expose] def read (left right : Symbol q r) : Option (Fin q) :=
  match left with
  | .pair _ a => a
  | _ => match right with
    | .pair a _ => a
    | _ => none

/-- Decode each original position from the two adjacent positions that represent it. -/
@[expose] noncomputable def decode (v : Fin (n + 3) → Fin (Fintype.card (Symbol q r)))
    (i : Fin n) : Option (Fin q) :=
  read (code.symm (v ⟨i.val + 1, by omega⟩)) (code.symm (v ⟨i.val + 2, by omega⟩))

/-- Decoding a canonical word recovers its original letters exactly. -/
theorem decode_word (s : Fin n → Fin q) (i : Fin n) :
    decode (r := r) (word s) i = some (s i) := by
  obtain ⟨a, ha⟩ := encode_right (r := r) s i
  simp only [decode, word, Function.comp_apply, Equiv.symm_apply_apply, ha, read]

private theorem read_some (rules : Fin r → Rule q) {a b c d : Symbol q r}
    (hab : Compatible rules a b) (hbc : Compatible rules b c)
    (hcd : Compatible rules c d) : ∃ x, read b c = some x := by
  cases b with
  | start => cases a <;> simp [Compatible] at hab
  | finish => cases c <;> simp [Compatible] at hbc
  | marker i =>
    cases c with
    | pair left right =>
      rcases hbc with h | h
      · exact ⟨(rules i).second, h⟩
      · exact ⟨(rules i).second', h⟩
    | _ => exact False.elim hbc
  | pair left right =>
    cases right with
    | some x => exact ⟨x, rfl⟩
    | none =>
      cases c with
      | finish => cases d <;> simp [Compatible] at hcd
      | _ => simp [Compatible] at hbc

/-- Consecutive positions of a coded legal word satisfy the symbolic compatibility relation. -/
theorem edge_view (rules : Fin r → Rule q)
    {v : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}
    (hv : HWord.Legal (compatibility rules) v) (i j : Fin (n + 3))
    (hij : i.val + 1 = j.val) : Compatible rules (code.symm (v i)) (code.symm (v j)) := by
  apply (compatibility_adj rules _ _).mp
  simpa only [Equiv.apply_symm_apply] using hv i j hij

/-- Every legal intermediate H-word supplies a letter at every original source position. -/
theorem decode_some (rules : Fin r → Rule q)
    {v : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}
    (hv : HWord.Legal (compatibility rules) v) (i : Fin n) :
    ∃ x, decode v i = some x := by
  exact read_some rules
    (edge_view rules hv ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ rfl)
    (edge_view rules hv ⟨i.val + 1, by omega⟩ ⟨i.val + 2, by omega⟩ rfl)
    (edge_view rules hv ⟨i.val + 2, by omega⟩ ⟨i.val + 3, by omega⟩ rfl)

/-- The source word decoded from an arbitrary legal compiled H-word. -/
noncomputable def readout (rules : Fin r → Rule q)
    (v : Fin (n + 3) → Fin (Fintype.card (Symbol q r)))
    (hv : HWord.Legal (compatibility rules) v) : Fin n → Fin q :=
  fun i => Classical.choose (decode_some rules hv i)

/-- The total readout is the unique letter supplied by each local decoder. -/
theorem readout_spec (rules : Fin r → Rule q)
    (v : Fin (n + 3) → Fin (Fintype.card (Symbol q r)))
    (hv : HWord.Legal (compatibility rules) v) (i : Fin n) :
    decode v i = some (readout rules v hv i) :=
  Classical.choose_spec (decode_some rules hv i)

/-- The actual total readout retracts every nonempty canonical source encoding. -/
theorem readout_word (rules : Fin r → Rule q) (s : Fin n → Fin q) (hn : 0 < n) :
    readout rules (word s) (word_legal rules s hn) = s := by
  funext i
  have h := readout_spec rules (word s) (word_legal rules s hn) i
  rw [decode_word] at h
  exact (Option.some.inj h).symm

/-- One occurrence of a two-letter rule, retaining every other source position. -/
structure Application (rule : Rule q) (s t : Fin n → Fin q) where
  /-- Position of the first letter. -/
  first : Fin n
  /-- Position of the second letter. -/
  second : Fin n
  /-- The two positions are consecutive. -/
  adjacent : first.val + 1 = second.val
  /-- First source letter. -/
  source_first : s first = rule.first
  /-- Second source letter. -/
  source_second : s second = rule.second
  /-- First target letter. -/
  target_first : t first = rule.first'
  /-- Second target letter. -/
  target_second : t second = rule.second'
  /-- Every other source position is retained. -/
  unchanged : ∀ i, i ≠ first → i ≠ second → s i = t i

private theorem front_rewrites (rules : Fin r → Rule q) (i : Fin r) {m : ℕ}
    {s t : Fin (m + 2) → Fin q} (app : Application (rules i) s t) (hf : app.first = 0) :
    Cslib.PostCorrespondence.Rewrites (RuleSet rules) (List.ofFn s) (List.ofFn t) := by
  have hs : app.second = (0 : Fin (m + 1)).succ :=
    Fin.ext (by
      have := app.adjacent; simp only [hf, Fin.val_zero] at this
      change app.second.val = 1; omega)
  have htail : (fun j : Fin m => s j.succ.succ) = fun j => t j.succ.succ := by
    funext j
    exact app.unchanged _ (Fin.ne_of_val_ne (by rw [hf]; change j.val + 2 ≠ 0; omega))
      (Fin.ne_of_val_ne (by rw [hs]; change j.val + 2 ≠ 1; omega))
  refine ⟨[], (rules i).domino, List.ofFn (fun j : Fin m => s j.succ.succ),
    ⟨i, Or.inl rfl⟩, ?_, ?_⟩
  · simp only [List.nil_append, List.ofFn_succ, Rule.domino, List.cons_append,
      List.nil_append, ← app.source_first, ← app.source_second, hf, hs]
  · simp only [List.nil_append, List.ofFn_succ, Rule.domino, List.cons_append,
      List.nil_append, ← app.target_first, ← app.target_second, hf, hs, htail]

private def tail_application {rule : Rule q} {s t : Fin (n + 1) → Fin q}
    (app : Application rule s t) (hf : app.first ≠ 0) :
    Application rule (fun j : Fin n => s j.succ) (fun j => t j.succ) := by
  have hfp : 0 < app.first.val := Nat.pos_of_ne_zero fun h => hf (Fin.ext h)
  let first : Fin n := ⟨app.first.val - 1, by have := app.first.isLt; omega⟩
  let second : Fin n :=
    ⟨app.second.val - 1, by have := app.second.isLt; have := app.adjacent; omega⟩
  have hfirst : first.succ = app.first :=
    Fin.ext (by dsimp only [first]; change app.first.val - 1 + 1 = _; omega)
  have hsecond : second.succ = app.second :=
    Fin.ext (by have := app.adjacent; dsimp only [second]; change app.second.val - 1 + 1 = _; omega)
  exact ⟨first, second, by have := app.adjacent; dsimp only [first, second]; omega,
    hfirst ▸ app.source_first, hsecond ▸ app.source_second,
    hfirst ▸ app.target_first, hsecond ▸ app.target_second,
    fun j hj hk => app.unchanged j.succ
      (fun he => hj (Fin.succ_injective n (he.trans hfirst.symm)))
      (fun he => hk (Fin.succ_injective n (he.trans hsecond.symm)))⟩

/-- An indexed rule occurrence is a genuine standard semi-Thue rewriting step. -/
theorem Application.rewrites (rules : Fin r → Rule q) (i : Fin r) {s t : Fin n → Fin q}
    (app : Application (rules i) s t) :
    Cslib.PostCorrespondence.Rewrites (RuleSet rules) (List.ofFn s) (List.ofFn t) := by
  induction n with
  | zero => exact Fin.elim0 app.first
  | succ n ih =>
    by_cases hf : app.first = 0
    · cases n with
      | zero =>
        have ha := app.adjacent
        have hb := app.second.isLt
        simp only [hf, Fin.val_zero] at ha
        omega
      | succ m => exact front_rewrites rules i app hf
    · have hr := (ih (tail_application app hf)).append_left [s 0]
      have hzero : s 0 = t 0 := app.unchanged 0 (Ne.symm hf)
        (Fin.ne_of_val_ne (by simpa only [Fin.val_zero, ← app.adjacent] using
          (Nat.succ_ne_zero _).symm))
      simpa only [List.ofFn_succ, List.cons_append, List.nil_append, hzero] using hr

private theorem padded_unchanged {rule : Rule q} {s t : Fin n → Fin q}
    (app : Application rule s t) (k : ℕ)
    (hfirst : k ≠ app.first.val + 1) (hsecond : k ≠ app.second.val + 1) :
    padded s k = padded t k := by
  rw [padded, padded]
  split
  · exact congrArg some (app.unchanged _ (Fin.ne_of_val_ne (by dsimp only; omega))
      (Fin.ne_of_val_ne (by dsimp only; omega)))
  · rfl

private theorem encode_unchanged {rule : Rule q} {s t : Fin n → Fin q}
    (app : Application rule s t) (p : Fin (n + 3))
    (h1 : p.val ≠ app.first.val + 1) (h2 : p.val ≠ app.first.val + 2)
    (h3 : p.val ≠ app.first.val + 3) : encode (r := r) s p = encode t p := by
  have hadj := app.adjacent
  rw [encode, encode]
  split
  next => rfl
  next hp =>
    split
    next => rfl
    next =>
      rw [padded_unchanged app _ (by omega) (by omega),
        padded_unchanged app _ (by omega) (by omega)]

private theorem word_window (s : Fin n → Fin q) (i j : Fin n) (hij : i.val + 1 = j.val) :
    ∀ u, segment (encode s ⟨i.val, by omega⟩)
      (.pair (padded s i.val) (some (s i))) (.pair (some (s i)) (some (s j)))
      (.pair (some (s j)) (padded s (i.val + 3))) (encode s ⟨i.val + 4, by omega⟩) u =
      word (r := r) s ((⟨i.val, by omega⟩ : Window (n + 3) 5).get u) := by
  have hp := padded_at s i
  have hq : padded s (i.val + 2) = some (s j) := by
    rw [show i.val + 2 = j.val + 1 by omega]
    exact padded_at s j
  have h1 := encode_pair (r := r) s ⟨i.val, by omega⟩
  have h2 := encode_pair (r := r) s ⟨i.val + 1, by omega⟩
  have h3 := encode_pair (r := r) s ⟨i.val + 2, by omega⟩
  simp only [hp, hq] at h1 h2 h3
  intro u
  fin_cases u <;> simp [segment, word, Window.get, h1, h2, h3]

private theorem patch_word {rule : Rule q} {s t : Fin n → Fin q}
    (app : Application rule s t) (window : Window (n + 3) 5)
    (hoff : window.offset = app.first.val)
    (target : Fin 5 → Fin (Fintype.card (Symbol q r)))
    (ht : ∀ u, target u = word t (window.get u)) : window.patch (word s) target = word t := by
  calc
    window.patch (word s) target = window.patch (word t) target := by
      funext p
      rw [Window.patch, Window.patch]
      split
      next => rfl
      next hp =>
        rw [hoff] at hp
        apply congrArg code
        exact encode_unchanged app p (by omega) (by omega) (by omega)
    _ = word t := window.patch_eq ht

private theorem window_edges (rules : Fin r → Rule q) (window : Window n 5)
    (base : Fin n → Fin (Fintype.card (Symbol q r)))
    (hlegal : HWord.Legal (compatibility rules) base) (v a b c w : Symbol q r)
    (hsrc : ∀ j, segment v a b c w j = base (window.get j)) :
    Compatible rules v a ∧ Compatible rules c w :=
  ⟨(compatibility_adj rules _ _).mp
      (by simpa [segment, ← hsrc 0, ← hsrc 1] using hlegal (window.get 0) (window.get 1) rfl),
    (compatibility_adj rules _ _).mp
      (by simpa [segment, ← hsrc 3, ← hsrc 4] using hlegal (window.get 3) (window.get 4) rfl)⟩

/-- Applying one source rule reconfigures the entire canonical encoded word, with all other
source letters and all outside H-word positions retained. -/
theorem rule_word_reachable (rules : Fin r → Rule q) (i : Fin r)
    {s t : Fin n → Fin q} (app : Application (rules i) s t) :
    HWord.Reachable (compatibility rules) (word s) (word t) := by
  let k := app.first.val
  have hki : k + 1 = app.second.val := app.adjacent
  have hk : k + 1 < n := by have := app.second.isLt; omega
  have hn : 0 < n := by omega
  let window : Window (n + 3) 5 := ⟨k, by omega⟩
  let v : Symbol q r := encode s ⟨k, by omega⟩
  let w : Symbol q r := encode s ⟨k + 4, by omega⟩
  let left := padded s k
  let right := padded s (k + 3)
  have hleft : padded t k = left := (padded_unchanged app k (by omega) (by omega)).symm
  have hright : padded t (k + 3) = right :=
    (padded_unchanged app (k + 3) (by omega) (by omega)).symm
  have hvw : encode (r := r) s ⟨k, by omega⟩ = encode t ⟨k, by omega⟩ :=
    encode_unchanged app _ (by change k ≠ k + 1; omega)
      (by change k ≠ k + 2; omega) (by change k ≠ k + 3; omega)
  have hww : encode (r := r) s ⟨k + 4, by omega⟩ = encode t ⟨k + 4, by omega⟩ :=
    encode_unchanged app _ (by change k + 4 ≠ k + 1; omega)
      (by change k + 4 ≠ k + 2; omega) (by change k + 4 ≠ k + 3; omega)
  let target := segment v (.pair left (some (rules i).first'))
    (.pair (some (rules i).first') (some (rules i).second'))
    (.pair (some (rules i).second') right) w
  have hsrc := word_window (r := r) s app.first app.second app.adjacent
  simp only [app.source_first, app.source_second] at hsrc
  have hdst := word_window (r := r) t app.first app.second app.adjacent
  dsimp only [k] at hvw hww hleft hright
  simp only [← hvw, ← hww, hleft, hright, app.target_first, app.target_second] at hdst
  have hlegal := word_legal rules s hn
  obtain ⟨hv, hw⟩ := window_edges rules window (word s) hlegal v _ _ _ w hsrc
  have hr := rule_in_window rules window (word s) hlegal i left right v w hv hw hsrc
  have hpatch := patch_word app window rfl target hdst
  exact hpatch ▸ hr

private theorem start_pair (rules : Fin r → Rule q) {v : Symbol q r}
    (h : Compatible rules .start v) : ∃ a, v = .pair none (some a) := by
  cases v <;> simp_all [Compatible]

private theorem finish_pair (rules : Fin r → Rule q) {v : Symbol q r}
    (h : Compatible rules v .finish) : ∃ a, v = .pair (some a) none := by
  cases v <;> simp_all [Compatible]

private theorem predecessor_blank (rules : Fin r → Rule q) {v : Symbol q r} (a : Fin q)
    (h : Compatible rules v (.pair none (some a))) : v = .start := by
  cases v <;> simp_all [Compatible]

private theorem successor_blank (rules : Fin r → Rule q) {v : Symbol q r} (a : Fin q)
    (h : Compatible rules (.pair (some a) none) v) : v = .finish := by
  cases v <;> simp_all [Compatible]

private theorem step_start (rules : Fin r → Rule q)
    {s t : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}
    (hs : HWord.Step (compatibility rules) s t) (hstart : s 0 = code .start) :
    t 0 = code .start := by
  obtain ⟨hs, ht, i, _, he⟩ := hs
  by_cases hi : i = 0
  · let next : Fin (n + 3) := ⟨1, by omega⟩
    have he1 : s next = t next :=
      he next (Fin.ne_of_val_ne (by rw [hi]; change 1 ≠ 0; omega))
    obtain ⟨a, ha⟩ := start_pair rules
      (by simpa only [hstart, Equiv.symm_apply_apply] using edge_view rules hs 0 next rfl)
    have h0 := predecessor_blank rules a
      (by simpa only [← he1, ha] using edge_view rules ht 0 next rfl)
    simpa only [Equiv.apply_symm_apply] using congrArg code h0
  · exact (he 0 (Ne.symm hi)).symm.trans hstart

private theorem step_finish (rules : Fin r → Rule q)
    {s t : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}
    (hs : HWord.Step (compatibility rules) s t)
    (hfinish : s ⟨n + 2, by omega⟩ = code .finish) :
    t ⟨n + 2, by omega⟩ = code .finish := by
  let last : Fin (n + 3) := ⟨n + 2, by omega⟩
  change s last = code .finish at hfinish
  change t last = code .finish
  obtain ⟨hs, ht, i, _, he⟩ := hs
  by_cases hi : i = last
  · let previous : Fin (n + 3) := ⟨n + 1, by omega⟩
    have he1 : s previous = t previous := he previous
      (Fin.ne_of_val_ne (by rw [hi]; change n + 1 ≠ n + 2; omega))
    obtain ⟨a, ha⟩ := finish_pair rules
      (by simpa only [hfinish, Equiv.symm_apply_apply] using edge_view rules hs previous last rfl)
    have h0 := successor_blank rules a
      (by simpa only [← he1, ha] using edge_view rules ht previous last rfl)
    simpa only [Equiv.apply_symm_apply] using congrArg code h0
  · exact (he last (Ne.symm hi)).symm.trans hfinish

/-- Both end markers of an encoded word are protected in every actual H-word trajectory. -/
theorem reachable_boundaries (rules : Fin r → Rule q)
    {s t : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}
    (hr : HWord.Reachable (compatibility rules) s t)
    (hstart : s 0 = code .start) (hfinish : s ⟨n + 2, by omega⟩ = code .finish) :
    t 0 = code .start ∧ t ⟨n + 2, by omega⟩ = code .finish := by
  induction hr with
  | refl => exact ⟨hstart, hfinish⟩
  | tail _ hs ih => exact ⟨step_start rules hs ih.1, step_finish rules hs ih.2⟩

end Cslib.Complexity.NCL.HWord.RewriteGadget
