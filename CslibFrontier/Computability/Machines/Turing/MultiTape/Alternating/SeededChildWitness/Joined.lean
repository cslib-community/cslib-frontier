/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Interval
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Segment
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Append

/-!
# All descendant endpoint choices on one tape

A shared parent proposal and universal selector precede the entire interval count game. Two
last existential fields name the parent endpoint at the selected singleton, then one universal
bit selects the short local equality or the recursive endpoint query. Every branch consumes the
same flag pattern, including padding, invalid arithmetic, and the direct parent branch.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts.Joined

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery
open SeededChildWitness Dispatch QuantifiedWord Cslib.BitString

/-- Two parent keys and a branch checking either the seed arithmetic or their parent membership. -/
@[expose] def pairFlags (w : ℕ) := List.replicate w false ++ (List.replicate w false ++ [true])

/-- The last three fields are least-significant-first. -/
@[expose] def pairTest (w : ℕ) (V : ℕ × ℕ → Bool → Prop) (xs : List Bool) : Prop :=
  V (lsbValue (xs.take w), lsbValue ((xs.drop w).take w)) (((xs.drop w).drop w).headD false)

private theorem takeField (w x : ℕ) (xs : List Bool) :
    (lowBits w x ++ xs).take w = lowBits w x := by
  simpa only [length_lowBits] using List.take_left (l₁ := lowBits w x) (l₂ := xs)

private theorem dropField (w x : ℕ) (xs : List Bool) : (lowBits w x ++ xs).drop w = xs := by
  simpa only [length_lowBits] using List.drop_left (l₁ := lowBits w x) (l₂ := xs)

private theorem plays_pair (w : ℕ) (V : ℕ × ℕ → Bool → Prop) :
    plays (pairTest w V) [] (pairFlags w) ↔ ∃ x y : Fin (2 ^ w), ∀ b, V (x.val, y.val) b := by
  rw [pairFlags, plays_exists_field]
  apply exists_congr
  intro x
  rw [plays_exists_field]
  apply exists_congr
  intro y
  simp only [plays, ↓reduceIte, List.nil_append, List.append_assoc, pairTest, takeField,
    dropField, lsbValue_lowBits x.isLt, lsbValue_lowBits y.isLt, List.headD_cons]

private theorem test_zero {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels)
    (r : Request) {j : ℕ} (hj : max q.size l.vertices ≤ j) :
    (decide (j < r.size q l) && r.test q l j) = false := by
  have hqj : ¬ j < q.size := by omega
  have huv : l.vertices ≤ j := by omega
  rw [test_onPair hq l r j (0, 0) (by simp [Request.needsParent, hqj])]
  cases r with
  | vertex b =>
    have hmin := (Nat.min_le_right b l.vertices).trans huv
    simp [Request.onPair, Request.size, Nat.not_lt.mpr hmin]
  | port col b => simp [Request.onPair, Request.needsParent, hqj]
  | pack e ends => simp [Request.onPair, Request.needsParent, hqj]

private theorem sum_padding (f : ℕ → Bool) {n N : ℕ} (hN : n ≤ N)
    (hz : ∀ i, n ≤ i → f i = false) :
    ∑ i ∈ Finset.range N, (f i).toNat = ∑ i ∈ Finset.range n, (f i).toNat := by
  rw [show N = n + (N - n) by omega, Finset.sum_range_add]
  have h : ∑ i ∈ Finset.range (N - n), (f (n + i)).toNat = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [hz (n + i) (by omega)]
  rw [h, Nat.add_zero]

private theorem count_common {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels)
    (r : Request) :
    let n := r.size q l
    let N := max q.size l.vertices
    ∑ j ∈ Finset.range N, (decide (j < n) && r.test q l j).toNat = r.value q l := by
  intro n N
  rw [Request.value_eq]
  let f j := decide (j < n) && r.test q l j
  have h₁ : ∑ j ∈ Finset.range n, (f j).toNat =
      ∑ j ∈ Finset.range n, (r.test q l j).toNat :=
    Finset.sum_congr rfl fun j hj => by simp [f, Finset.mem_range.mp hj]
  rw [← h₁]
  by_cases hn : n ≤ N
  · exact sum_padding f hn fun j hj => by simp [f, Nat.not_lt.mpr hj]
  · exact (sum_padding f (by omega : N ≤ n) fun _ hj => test_zero hq l r hj).symm

/-- The singleton terminal either fails locally or selects at most one positive parent query. -/
@[expose] noncomputable def leaf (q : EndpointQuery) (l : Labels) (r : Request)
    (result : Option (ℕ × ℕ)) (p : ℕ × ℕ) (challenge : Bool) : Prop :=
  match result with
  | none => False
  | some (j, value) =>
    if challenge then (r.needsParent q l j = true → q.accepts j p)
    else value = (r.onPair q l j p).toNat

/-- The two phases for a challenged count use fixed flags for all six modes. -/
@[expose] def countFlags (b : Public) := IntervalCountGame.flags (max b.edges b.vertices) ++
  pairFlags b.vertices.size

/-- Parse the same fixed bisection prefix on any selected count branch. -/
@[expose] noncomputable def countLeaf (q : EndpointQuery) (l : Labels) (r : Request)
    (bit : ℕ) (claim : Bool) (xs : List Bool) : Prop :=
  let N := max q.size l.vertices
  let k := (IntervalCountGame.flags N).length
  let result := IntervalCountGame.route N bit claim (xs.take k)
  pairTest l.vertices.size (leaf q l r result) (xs.drop k)

private theorem plays_count {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels)
    (hkeys : ∀ e p, q.accepts e p → p.1 < l.vertices ∧ p.2 < l.vertices)
    (r : Request) (bit : ℕ) (claim : Bool) (j : ℕ) :
    plays (countLeaf q l r bit claim) [] (countFlags ⟨q.size, l.vertices, j⟩) ↔
      (r.value q l).testBit bit = claim := by
  let N := max q.size l.vertices
  let f j := decide (j < r.size q l) && r.test q l j
  let padded j := decide (j < N) && f j
  have hp (j : ℕ) : padded j = f j := by
    by_cases hj : j < N
    · simp [padded, hj]
    · simp [padded, hj, f, test_zero hq l r (Nat.le_of_not_gt hj)]
  have hs (ys : List Bool) :
      plays (pairTest l.vertices.size (leaf q l r (IntervalCountGame.route N bit claim ys))) []
          (pairFlags l.vertices.size) ↔
        IntervalCountGame.verdict padded (IntervalCountGame.route N bit claim ys) := by
    rw [plays_pair]
    cases IntervalCountGame.route N bit claim ys with
    | none => simp [leaf, IntervalCountGame.verdict]
    | some pair =>
      rcases pair with ⟨j, v⟩
      simpa only [leaf, IntervalCountGame.verdict, hp] using (singleton_iff hq l hkeys r j v).symm
  have he := plays_split
    (fun xs => pairTest l.vertices.size (leaf q l r (IntervalCountGame.route N bit claim xs)))
    (fun xs => IntervalCountGame.verdict padded (IntervalCountGame.route N bit claim xs))
    (IntervalCountGame.flags N) (pairFlags l.vertices.size) (fun xs _ => hs xs)
  exact he.trans ((IntervalCountGame.plays_flags f N bit claim).trans
    (congrArg (fun v : ℕ => v.testBit bit = claim) (count_common hq l r)).to_iff)

/-- The full physical word for a descendant endpoint query, independent of its guessed fields. -/
@[expose] def flags (b : Public) := witnessFlags (width b) ++ countFlags b

/-- A single completed word reaches a direct local check, a direct parent endpoint, or one
singleton check inside one of the six selected counts. -/
@[expose] noncomputable def value (q : EndpointQuery) (l : Labels) (b : Public)
    (check : Proposal → Prop) (xs : List Bool) : Prop :=
  let cut := (witnessFlags (width b)).length
  let data := Dispatch.run (b, xs.take cut)
  match data.2 with
  | .inl false => check data.1
  | .inl true => q.accepts data.1.edge data.1.ends
  | .inr none => True
  | .inr (some (r, bit, claim)) => countLeaf q l (request r) bit claim (xs.drop cut)

/-- One physical choice word suffices for the genuine child endpoint predicate. Its final
branch uses short seed arithmetic and at most one parent endpoint. -/
theorem plays_child {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a) (group : ℕ)
    {q : EndpointQuery} {es} (hq : q.Represents es)
    (hkeys : ∀ e p, q.accepts e p → p.1 < U ∧ p.2 < U) (j : ℕ) (answer : ℕ × ℕ) :
    let l := Labels.ofSeed U a seed i group
    let b : Public := ⟨q.size, U, j⟩
    let check (p : Proposal) := SeededChildWitness.run
      ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, i.val, group, j,
        p.ends, answer, p.counts⟩ = true
    plays (value q l b check) [] (flags b) ↔ (q.child (l.split q)).accepts j answer := by
  intro l b check
  let V (xs ys : List Bool) : Prop :=
    let data := Dispatch.run (b, xs)
    match data.2 with
    | .inl false => check data.1
    | .inl true => q.accepts data.1.edge data.1.ends
    | .inr none => True
    | .inr (some (r, bit, claim)) => countLeaf q l (request r) bit claim ys
  have he := plays_split V (routedValue q l b check) (witnessFlags (width b)) (countFlags b)
    (fun xs _ => by
      rcases hd : Dispatch.run (b, xs) with ⟨p, side⟩
      dsimp only [V, routedValue]
      rw [hd]
      rcases side with (_ | _) | (_ | ⟨r, bit, claim⟩)
      · exact plays_constant _ _ _
      · exact plays_constant _ _ _
      · exact plays_constant _ _ _
      · exact plays_count hq l hkeys (request r) bit claim j)
  exact he.trans (child_iff_plays_dispatch seed i group hq hkeys j answer).symm

end Turing.MultiTapeATM.SeededChildCounts.Joined
