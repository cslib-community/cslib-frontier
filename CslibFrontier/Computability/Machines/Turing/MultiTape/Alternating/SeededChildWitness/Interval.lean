/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCountGame
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildCounts

/-!
# One parent endpoint at the bottom of any bisection branch

A vertex singleton reads its label locally. A port or class singleton inside the genuine
range uses an existential parent endpoint pair, for both truth values. Padding or a candidate
past the prefix has value zero. The global count verification makes exactly one such choice
on each path, regardless of the number of bisections.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts

open Cslib Cslib.Circuits.Frontier.NativeChild EndpointQuery IntervalCountGame QuantifiedWord
open WordGameLeaf (config)

/-- Whether a selected singleton actually requires a parent edge. -/
@[expose] def Request.needsParent (r : Request) (q : EndpointQuery) (l : Labels) (j : ℕ) : Bool :=
  decide (j < r.size q l ∧ j < q.size) && match r with
    | .vertex _ => false
    | .port .. => true
    | .pack e _ => decide (j < e)

/-- Evaluate a selected singleton after filling the two parent endpoint keys, if needed. -/
@[expose] noncomputable def Request.onPair (r : Request) (q : EndpointQuery) (l : Labels) (j : ℕ)
    (p : ℕ × ℕ) : Bool :=
  match r with
  | .vertex _ => decide (j < r.size q l ∧ (l.split q).label j = l.group)
  | .port col _ => r.needsParent q l j &&
      decide ((l.split q).label (if col then p.2 else p.1) = l.group)
  | .pack _ ends => r.needsParent q l j &&
      decide (l.code p.1 = l.code ends.1 ∧ l.code p.2 = l.code ends.2)

private theorem atEndpoint_own {q : EndpointQuery} {es} (hq : q.Represents es) {j : ℕ}
    (hj : j < q.size) (f : ℕ × ℕ → Bool) :
    atEndpoint q j f = f (es.getD j (0, 0)) := by
  apply (atEndpoint_eq_iff hq hj f _).2
  exact ⟨_, (hq.2 j _).2 ⟨hq.1 ▸ hj, rfl⟩, rfl⟩

private theorem atEndpoint_pad {q : EndpointQuery} {es} (hq : q.Represents es) {j : ℕ}
    (hj : ¬ j < q.size) (f : ℕ × ℕ → Bool) : atEndpoint q j f = false := by
  classical
  simp [atEndpoint, hq.2, ← hq.1, hj]

/-- A certified pair recovers the actual signed summand, including padding. -/
theorem test_onPair {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels)
    (r : Request) (j : ℕ) (p : ℕ × ℕ)
    (hp : r.needsParent q l j = true → q.accepts j p) :
    (decide (j < r.size q l) && r.test q l j) = r.onPair q l j p := by
  by_cases hn : j < r.size q l
  · by_cases hj : j < q.size
    · cases r with
      | vertex bound => simp [Request.test, Request.onPair, hn]
      | port col bound =>
        have he := (hq.2 _ _).1 (hp (by simp [Request.needsParent, hj, hn]))
        rw [← he.2]
        simp [Request.test, Request.onPair, Request.needsParent, hn, hj, atEndpoint_own hq hj]
      | pack edge ends =>
        by_cases hc : j < edge
        · have he := (hq.2 _ _).1 (hp (by simp [Request.needsParent, hj, hn, hc]))
          rw [← he.2]
          simp [Request.test, Request.onPair, Request.needsParent, hn, hj, hc,
            atEndpoint_own hq hj]
        · simp [Request.test, Request.onPair, Request.needsParent, hn, hj, hc]
    · cases r <;> simp [Request.test, Request.onPair, Request.needsParent, hn, hj,
        atEndpoint_pad hq hj]
  · cases r <;> simp [Request.test, Request.onPair, Request.needsParent, hn]

/-- The signed singleton claim checks its local value and, on a separate universal branch,
the single genuine parent endpoint. Both coordinates of the common witness fit the vertex width. -/
theorem singleton_iff {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels)
    (hkeys : ∀ e p, q.accepts e p → p.1 < l.vertices ∧ p.2 < l.vertices)
    (r : Request) (j value : ℕ) :
    value = (decide (j < r.size q l) && r.test q l j).toNat ↔
      ∃ x y : Fin (2 ^ l.vertices.size), ∀ challenge : Bool,
        if challenge then (r.needsParent q l j = true → q.accepts j (x.val, y.val))
        else value = (r.onPair q l j (x.val, y.val)).toNat := by
  have hbound := Nat.lt_size_self l.vertices
  constructor
  · intro h
    by_cases hn : r.needsParent q l j = true
    · have hj : j < q.size := by
        have h₀ := (Bool.and_eq_true_iff.mp hn).1
        exact (of_decide_eq_true h₀).2
      let p := es.getD j (0, 0)
      have hp : q.accepts j p := (hq.2 j p).2 ⟨hq.1 ▸ hj, rfl⟩
      have hb := hkeys j p hp
      refine ⟨⟨p.1, hb.1.trans hbound⟩, ⟨p.2, hb.2.trans hbound⟩, ?_⟩
      rintro (_ | _)
      · exact h.trans (congrArg Bool.toNat (test_onPair hq l r j p (fun _ => hp)))
      · exact fun _ => hp
    · refine ⟨0, 0, ?_⟩
      rintro (_ | _)
      · exact h.trans (congrArg Bool.toNat (test_onPair hq l r j _ (fun h' => (hn h').elim)))
      · exact fun h' => (hn h').elim
  · rintro ⟨x, y, hv⟩
    exact (hv false).trans (congrArg Bool.toNat (test_onPair hq l r j _ (hv true))).symm

/-- The one finite quantified-word control evaluates the challenged count bit inside an open
endpoint segment. Its only outstanding obligation is the singleton verdict on the completed word.
The continuation occurs once and the flag overhead is quadratic in the binary range length. -/
theorem count_segment {k : ℕ} {S H : Type} (leaf : MultiTapeATM k Bool S) (tape : Fin k)
    {host : MultiTapeATM k Bool H} (sim : StateSimulation (QuantifiedWord.machine leaf tape) host)
    (mark : H → Bool) {input : List Bool} (ready meaning : Cfg k Bool H input → Prop)
    (q : EndpointQuery) (l : Labels) (r : Request) (bit : ℕ) (claim : Bool)
    (t : ℕ) (storage : Cfg k Bool Unit input)
    (hd : mark (sim.stateMap .dispatch) = false)
    (hc : ∀ p, mark (sim.stateMap (.choose p)) = false) :
    let n := r.size q l
    let f := fun j => decide (j < n) && r.test q l j
    (∀ xs : List Bool, xs.length = (flags n).length →
      let cfg := config tape (some (.leaf leaf.toPTM.initial)) xs xs.length storage
      TailCall.Segment host mark ready meaning t (cfg.mapState (Option.map sim.stateMap))
        (verdict f (route n bit claim xs))) →
    let cfg := config tape (some .dispatch) (flags n) 0 storage
    TailCall.Segment host mark ready meaning (t + 2 * (flags n).length + 1)
      (cfg.mapState (Option.map sim.stateMap)) ((r.value q l).testBit bit = claim) := by
  intro n f h
  have hg := QuantifiedWord.segment leaf tape sim mark ready meaning t storage
    (fun xs => verdict f (route n bit claim xs)) [] (flags n) hd hc
    (fun xs hx => by simpa only [List.nil_append] using h xs hx)
  apply hg.iff
  rw [Request.value_eq]
  exact plays_flags (r.test q l) n bit claim

end Turing.MultiTapeATM.SeededChildCounts
