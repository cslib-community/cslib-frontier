/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic

/-!
# Aho–Corasick Multi-Pattern String Matching

This module implements the pure reference pattern matching machine of `[AhoCorasick1975]` over
arbitrary alphabets with decidable equality: the scan of a text by a machine with given failure and
output tables (Algorithm 1, `scan`), the level-by-level construction of the failure and output
tables (Algorithm 3, `build`), and their composition (`search`). It proves that scanning with valid
tables reports exactly the keyword occurrences `occurrences P t` of
`CslibFrontier.Algorithms.Lean.AhoCorasick.Basic`, and that `build` produces valid tables.

For bounded integer alphabets `[0, σ)`, `CslibFrontier.Algorithms.WordRAM.AhoCorasick` constructs
the explicit integer-state array trie, BFS failure links, next-move table, and output-link chains
(Algorithms 2 and 3 and Section 6) and scans the text (Algorithm 1 with failure-depth potential) in
`O((‖P‖ + 1) · σ + |P| + |t| + occ)` Word-RAM instructions.

## Source conventions

* **States:** as in `[AhoCorasick1975]`, Section 4, a state is represented by its string
  (`IsNode P`). The goto function is the prefix test `IsNode P (u ++ [a])`, and the start state
  loops on every symbol that does not begin a keyword.
* **Output:** reported pairs `(i, y)` give the `1`-indexed end position `i` of the keyword `y`, as
  printed by Algorithm 1. A keyword listed several times in `P` is reported once per end position,
  and the empty keyword is never reported.
* **Tables:** a `Machine α` bundles a failure table and an output table, both functions on
  strings. `Machine.IsValid P M` says they agree with `failure P` and `output P` on every state.
* **Guarded failure loop:** `step` stops at the start state if a failure transition does not
  shorten the state. This never happens with a valid table and guarantees termination for any
  failure table.

## Main definitions

* `Cslib.Algorithms.Lean.AhoCorasick.Machine`: failure and output tables.
* `Cslib.Algorithms.Lean.AhoCorasick.Machine.IsValid`: the tables agree with `failure` and
  `output` on every state.
* `Cslib.Algorithms.Lean.AhoCorasick.step`: one operating cycle of Algorithm 1.
* `Cslib.Algorithms.Lean.AhoCorasick.scan`: Algorithm 1.
* `Cslib.Algorithms.Lean.AhoCorasick.build`: Algorithm 3.
* `Cslib.Algorithms.Lean.AhoCorasick.search`: build the machine, then scan.

## Main results

* `Cslib.Algorithms.Lean.AhoCorasick.scan_eq_occurrences`: with valid tables, the scan reports
  exactly `occurrences P t` (`[AhoCorasick1975]`, Theorem 1 for Algorithm 1).
* `Cslib.Algorithms.Lean.AhoCorasick.isValid_build`: Algorithm 3 computes valid tables
  (`[AhoCorasick1975]`, Theorem 1 for Algorithm 3).
* `Cslib.Algorithms.Lean.AhoCorasick.search_eq` and `mem_search_iff`.

## References

* [A. V. Aho and M. J. Corasick, *Efficient String Matching: An Aid to Bibliographic
  Search*][AhoCorasick1975]
-/

public section

namespace Cslib.Algorithms.Lean.AhoCorasick

variable {α : Type*} [DecidableEq α]

/-! ## Machines and validity -/

/-- Failure and output tables of a pattern matching machine whose states are represented by their
strings. -/
structure Machine (α : Type*) where
  /-- The failure function. -/
  fail : List α → List α
  /-- The output function. -/
  out : List α → List (List α)

/-- `M` has the correct failure and output values at `u`. -/
@[expose] def Machine.AgreesAt (P : List (List α)) (M : Machine α) (u : List α) : Prop :=
  M.fail u = failure P u ∧ M.out u = output P u

/-- `M` has the failure function and output function of `P` (`[AhoCorasick1975]`, Lemmas 1 and 2)
on every goto-graph state. This is stronger than the paper's (behavioural) validity, which only
asks that Algorithm 1 report the right occurrences: it fixes the tables on every state. -/
@[expose] def Machine.IsValid (P : List (List α)) (M : Machine α) : Prop :=
  ∀ u, IsNode P u → M.AgreesAt P u

/-! ## One operating cycle -/

/-- One operating cycle of Algorithm 1 of `[AhoCorasick1975]` with failure table `f`. A failure
transition that does not shorten the state (which cannot happen for a valid table) stops at the
start state. -/
def step (P : List (List α)) (f : List α → List α) (u : List α) (a : α) : List α :=
  if IsNode P (u ++ [a]) then
    u ++ [a]
  else if u = [] then
    []
  else if _hlt : (f u).length < u.length then
    step P f (f u) a
  else
    []
termination_by u.length

theorem step_eq_nextMove {P : List (List α)} {f : List α → List α} {u : List α} (a : α)
    (hf : ∀ v, IsNode P v → v.length ≤ u.length → f v = failure P v) (hu : IsNode P u) :
    step P f u a = nextMove P u a := by
  fun_induction step P f u a with
  | case1 u hnode =>
    exact (nextMove_of_isNode hnode).symm
  | case2 hnode =>
    exact (nextMove_of_not_isNode_of_eq_nil hnode rfl).symm
  | case3 u hnode hnil hlt ih =>
    have hfu : f u = failure P u := hf u hu (Nat.le_refl _)
    rw [nextMove_of_not_isNode hnode hnil, ← hfu]
    exact ih (fun v hv hvl => hf v hv (by omega)) (hfu ▸ isNode_failure P u)
  | case4 u hnode hnil hlt =>
    exact absurd (hf u hu (Nat.le_refl _) ▸ length_failure_lt P hnil) hlt

/-! ## Algorithm 1: the scan -/

/-- The operating cycles of Algorithm 1 of `[AhoCorasick1975]` on the remaining text `t`, from
state `u` after `i` symbols. -/
private def scanLoop (P : List (List α)) (M : Machine α) :
    List α → ℕ → List α → List (ℕ × List α)
  | [], _, _ => []
  | a :: t, i, u =>
    let v := step P M.fail u a
    let found := (M.out v).map fun y => (i + 1, y)
    found ++ scanLoop P M t (i + 1) v

/-- Algorithm 1 of `[AhoCorasick1975]`: run the pattern matching machine `M` on `t`, reporting
each keyword occurrence as its end position and the keyword. -/
def scan (P : List (List α)) (M : Machine α) (t : List α) : List (ℕ × List α) :=
  scanLoop P M t 0 []

private theorem scanLoop_eq_occurrences {P : List (List α)} {M : Machine α} (hM : M.IsValid P)
    (w t : List α) :
    occurrences P w ++ scanLoop P M t w.length (longestNodeSuffix P w) =
      occurrences P (w ++ t) := by
  induction t generalizing w with
  | nil => simp only [scanLoop, List.append_nil]
  | cons a t ih =>
    have hstep : step P M.fail (longestNodeSuffix P w) a = longestNodeSuffix P (w ++ [a]) := by
      rw [step_eq_nextMove a (fun v hv _ => (hM v hv).1) (isNode_longestNodeSuffix P w),
        longestNodeSuffix_append_singleton_eq_nextMove]
    simp only [scanLoop, hstep]
    have hout : M.out (longestNodeSuffix P (w ++ [a])) = output P (w ++ [a]) := by
      rw [(hM _ (isNode_longestNodeSuffix P _)).2, output_longestNodeSuffix]
    have := ih (w ++ [a])
    rw [List.length_append, List.length_singleton] at this
    rw [hout, ← List.append_assoc, ← occurrences_append_singleton, this, List.append_assoc,
      List.singleton_append]

/-- Correctness of Algorithm 1 (`[AhoCorasick1975]`, Theorem 1): with valid failure and output
tables, the scan reports exactly the keyword occurrences. -/
theorem scan_eq_occurrences {P : List (List α)} {M : Machine α} (hM : M.IsValid P) (t : List α) :
    scan P M t = occurrences P t := by
  have := scanLoop_eq_occurrences hM [] t
  rwa [occurrences_nil, List.nil_append, List.nil_append, List.length_nil, longestNodeSuffix_nil]
    at this

/-! ## Algorithm 3: the failure and output functions -/

/-- Record the failure state `f` of the state `v`, and its output (`[AhoCorasick1975]`, the last
two statements of Algorithm 3). -/
private def Machine.set (P : List (List α)) (M : Machine α) (v f : List α) : Machine α where
  fail w := if w = v then f else M.fail w
  out w := if w = v then (if v ∈ P then [v] else []) ++ M.out f else M.out w

/-- The tables before Algorithm 3's main loop: the start state and the states of depth `1` fail to
the start state, and the output of a state of depth `1` is the state itself if it is a keyword. -/
private def initMachine (P : List (List α)) : Machine α where
  fail _ := []
  out w := if w ≠ [] ∧ w ∈ P then [w] else []

/-- One round of Algorithm 3 of `[AhoCorasick1975]` (depth `d` to depth `d + 1`): for each keyword
`p` longer than `d`, compute the failure state of `p.take (d + 1)` by one operating cycle from the
failure state of `p.take d`. -/
private def level (P : List (List α)) (d : ℕ) : List (List α) → Machine α → Machine α
  | [], M => M
  | p :: ps, M =>
    if h : d < p.length then
      let f := step P M.fail (M.fail (p.take d)) (p[d]'h)
      level P d ps (M.set P (p.take (d + 1)) f)
    else
      level P d ps M

/-- Rounds `d, d + 1, …, d + n - 1` of Algorithm 3. -/
private def buildLoop (P : List (List α)) : ℕ → ℕ → Machine α → Machine α
  | 0, _, M => M
  | n + 1, d, M => buildLoop P n (d + 1) (level P d P M)

/-- The length of the longest keyword. -/
private def maxLength (P : List (List α)) : ℕ :=
  P.foldr (fun p m => max p.length m) 0

omit [DecidableEq α] in
private theorem length_le_maxLength {P : List (List α)} {p : List α} (hp : p ∈ P) :
    p.length ≤ maxLength P := by
  induction P with
  | nil => cases hp
  | cons q P ih =>
    exact (List.mem_cons.mp hp).elim (fun h => h ▸ Nat.le_max_left _ _) fun hp =>
      (ih hp).trans (Nat.le_max_right _ _)

/-- The pattern matching machine of `P`, built level by level (`[AhoCorasick1975]`,
Algorithm 3). -/
def build (P : List (List α)) : Machine α :=
  buildLoop P (maxLength P - 1) 1 (initMachine P)

/-- All keyword occurrences, computed by the Aho–Corasick algorithm. -/
def search (P : List (List α)) (t : List α) : List (ℕ × List α) :=
  scan P (build P) t

/-- `M` has the correct failure and output values on all states of depth at most `d`. -/
private def AgreesUpTo (P : List (List α)) (M : Machine α) (d : ℕ) : Prop :=
  ∀ w, IsNode P w → w.length ≤ d → M.AgreesAt P w

private theorem agreesUpTo_initMachine (P : List (List α)) : AgreesUpTo P (initMachine P) 1 := by
  intro w hw hlen
  refine ⟨(failure_eq_nil_of_length_le_one P hlen).symm, ?_⟩
  match w, hlen with
  | [], _ => simp only [initMachine, ne_eq, not_true_eq_false, false_and, ↓reduceIte, output_nil]
  | [b], _ =>
    simp only [initMachine, ne_eq, List.cons_ne_nil, not_false_eq_true, true_and, output_cons,
      output_nil]

/-- The failure state computed for `p.take (d + 1)`. -/
private theorem step_spec {P : List (List α)} {M : Machine α} {d : ℕ} (hd : 1 ≤ d)
    (hM : AgreesUpTo P M d) {p : List α} (hp : p ∈ P) (h : d < p.length) :
    step P M.fail (M.fail (p.take d)) (p[d]'h) = failure P (p.take (d + 1)) ∧
      M.fail (p.take d) = failure P (p.take d) := by
  have hlen : (p.take d).length = d := List.length_take_of_le (Nat.le_of_lt h)
  have hne : p.take d ≠ [] := fun h0 => by rw [h0, List.length_nil] at hlen; omega
  have hfd : M.fail (p.take d) = failure P (p.take d) :=
    (hM _ (isNode_take hp d) (Nat.le_of_eq hlen)).1
  refine ⟨?_, hfd⟩
  have hflt := length_failure_lt P hne
  rw [hfd, step_eq_nextMove _ (fun v hv hvl => (hM v hv (by omega)).1) (isNode_failure P _),
    List.take_add_one, getElem?_pos p d h, Option.toList_some, failure_append_singleton P hne]

/-- `Machine.set` changes the tables only at `v`. -/
private theorem agreesAt_set_of_ne {P : List (List α)} {M : Machine α} {v f w : List α}
    (hw : w ≠ v) (h : M.AgreesAt P w) : (M.set P v f).AgreesAt P w := by
  simp only [Machine.AgreesAt, Machine.set, hw, ↓reduceIte]
  exact h

/-- Recording the correct failure state of a nonempty state `v` whose failure state already has
the correct output makes the tables correct at `v`. -/
private theorem agreesAt_set {P : List (List α)} {M : Machine α} {v : List α} (hv : v ≠ [])
    (hout : M.out (failure P v) = output P (failure P v)) :
    (M.set P v (failure P v)).AgreesAt P v := by
  simp only [Machine.AgreesAt, Machine.set, ↓reduceIte, hout, true_and]
  exact (output_eq_of_ne_nil P hv).symm

private theorem level_spec {P : List (List α)} {d : ℕ} (hd : 1 ≤ d) :
    ∀ (ps : List (List α)) (M : Machine α), (∀ p ∈ ps, p ∈ P) → AgreesUpTo P M d →
      (∀ w, M.AgreesAt P w → (level P d ps M).AgreesAt P w) ∧
      ∀ p ∈ ps, (h : d < p.length) → (level P d ps M).AgreesAt P (p.take (d + 1)) := by
  intro ps
  induction ps with
  | nil => exact fun _ _ _ => ⟨fun _ h => h, fun _ hp => absurd hp List.not_mem_nil⟩
  | cons q ps ih =>
    intro M hps hM
    have hpsP : ∀ p ∈ ps, p ∈ P := fun p hp => hps p (List.mem_cons_of_mem q hp)
    rw [level]
    split_ifs with hq
    · rw [(step_spec hd hM (hps q List.mem_cons_self) hq).1]
      set v := q.take (d + 1)
      have hvlen : v.length = d + 1 := List.length_take_of_le hq
      have hvne : v ≠ [] := fun h0 => by simp [h0] at hvlen
      have hflt := length_failure_lt P hvne
      have hM1v := agreesAt_set hvne (hM _ (isNode_failure P v) (by omega)).2
      have hpres (w) (hw : M.AgreesAt P w) : (M.set P v (failure P v)).AgreesAt P w :=
        if hwv : w = v then hwv ▸ hM1v else agreesAt_set_of_ne hwv hw
      obtain ⟨ih1, ih2⟩ := ih _ hpsP fun w hw hwl => hpres w (hM w hw hwl)
      exact ⟨fun w hw => ih1 w (hpres w hw),
        List.forall_mem_cons.mpr ⟨fun _ => ih1 _ hM1v, ih2⟩⟩
    · obtain ⟨ih1, ih2⟩ := ih M hpsP hM
      exact ⟨ih1, List.forall_mem_cons.mpr ⟨fun hpd => absurd hpd hq, ih2⟩⟩

private theorem agreesUpTo_level {P : List (List α)} {d : ℕ} (hd : 1 ≤ d) {M : Machine α}
    (hM : AgreesUpTo P M d) : AgreesUpTo P (level P d P M) (d + 1) := by
  obtain ⟨h1, h2⟩ := level_spec hd P M (fun _ hp => hp) hM
  intro w hw hwl
  by_cases hwd : w.length ≤ d
  · exact h1 w (hM w hw hwd)
  · rcases hw with rfl | ⟨p, hp, hwp⟩
    · simp at hwd
    · have hwlen : w.length = d + 1 := by omega
      have := hwp.length_le
      rw [List.prefix_iff_eq_take.mp hwp, hwlen]
      exact h2 p hp (by omega)

private theorem agreesUpTo_buildLoop {P : List (List α)} :
    ∀ (n d : ℕ) (M : Machine α), 1 ≤ d → AgreesUpTo P M d →
      AgreesUpTo P (buildLoop P n d M) (d + n)
  | 0, _, _, _, hM => hM
  | n + 1, d, M, hd, hM => by
    simpa only [buildLoop, Nat.add_assoc, Nat.add_comm 1 n] using
      agreesUpTo_buildLoop n (d + 1) _ (by omega) (agreesUpTo_level hd hM)

/-- Correctness of Algorithm 3 (`[AhoCorasick1975]`, Lemmas 1 and 2, Theorem 1): the constructed
failure and output functions are those of `P` on every state. -/
theorem isValid_build (P : List (List α)) : (build P).IsValid P := by
  intro w hw
  refine agreesUpTo_buildLoop (maxLength P - 1) 1 (initMachine P) le_rfl
    (agreesUpTo_initMachine P) w hw ?_
  rcases hw with rfl | ⟨p, hp, hwp⟩
  · exact Nat.zero_le _
  · have := hwp.length_le
    have := length_le_maxLength hp
    omega

/-- Correctness of the Aho–Corasick algorithm (`[AhoCorasick1975]`, Theorem 1). -/
theorem search_eq (P : List (List α)) (t : List α) : search P t = occurrences P t :=
  scan_eq_occurrences (isValid_build P) t

theorem mem_search_iff {P : List (List α)} {t : List α} {i : ℕ} {y : List α} :
    (i, y) ∈ search P t ↔ IsOccurrence P t i y := by
  rw [search_eq, mem_occurrences_iff]

end Cslib.Algorithms.Lean.AhoCorasick
