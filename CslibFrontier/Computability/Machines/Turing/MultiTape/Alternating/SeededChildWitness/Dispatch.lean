/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness
public import CslibFrontier.Computability.PolyTime.SeededChildWitness.Dispatch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-!
# Checking the count obligations after the common witness

A three-bit universal challenge picks one of eight branches. On a count branch the next
universal field chooses a bit of the proposed integer. The proof covers the full binary
range, including a width of zero and padded bit indices.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery
open SeededChildWitness Dispatch

/-- Interpret the native count code as one of the three recursive count requests. -/
@[expose] def request : Dispatch.Count → Request
  | .inl n => .vertex n
  | .inr (.inl (col, n)) => .port col n
  | .inr (.inr (e, p)) => .pack e p

/-- Interpretation of the single selected task in the physical dispatcher. -/
@[expose] def verdict (q : EndpointQuery) (l : Labels) (localTest parentTest : Prop) : Branch → Prop
  | .inl false => localTest
  | .inl true => parentTest
  | .inr none => True
  | .inr (some (code, j, claim)) => ((request code).value q l).testBit j = claim

private theorem count_branch (q : EndpointQuery) (l : Labels) (b : Public) (p : Proposal)
    (x y : Prop) {s : ℕ} (hs : 2 ≤ s) (w j : ℕ) :
    verdict q l x y (branch b p w s j) ↔
      (j < w → ((request (selected b p s).1).value q l).testBit j =
        (selected b p s).2.testBit j) := by
  have h₀ : s ≠ 0 := by omega
  have h₁ : s ≠ 1 := by omega
  by_cases hj : j < w
  · simp [branch, verdict, h₀, h₁, hj, Nat.min_eq_right hj.le]
  · simp [branch, verdict, h₀, h₁, hj]

private theorem select_eq_iff (q : EndpointQuery) (l : Labels) (b : Public) (p : Proposal)
    (x y : Prop) {s w : ℕ} (hs : 2 ≤ s)
    (ha : (request (selected b p s).1).value q l < 2 ^ w) (hp : (selected b p s).2 < 2 ^ w) :
    (∀ j : Fin (2 ^ Nat.clog 2 w), verdict q l x y (branch b p w s j.val)) ↔
      (request (selected b p s).1).value q l = (selected b p s).2 := by
  simp only [count_branch q l b p x y hs]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < w
    · exact h ⟨j, hj.trans_le (Nat.le_pow_clog (by decide : 1 < 2) w)⟩ hj
    · have hw : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
      rw [Nat.testBit_lt_two_pow (ha.trans_le hw), Nat.testBit_lt_two_pow (hp.trans_le hw)]
  · intro h j _
    rw [h]

private theorem all_counts {q : EndpointQuery} {l : Labels} {b : Public} {p : Proposal}
    (hsize : b.edges = q.size) (hu : b.vertices = l.vertices) (he : p.edge ≤ q.size)
    (hp : ∀ n ∈ p.fields, n < 2 ^ width b) (s : Fin 6) :
    (request (selected b p (s.val + 2)).1).value q l < 2 ^ width b ∧
      (selected b p (s.val + 2)).2 < 2 ^ width b := by
  have edge := Nat.le_max_left q.size l.vertices
  have vertex := Nat.le_max_right q.size l.vertices
  have hz : max q.size l.vertices < 2 ^ width b := by
    simpa only [width, hsize, hu] using Nat.lt_size_self (max q.size l.vertices)
  have count (r : Request) (h : r.size q l ≤ max q.size l.vertices) :
      r.value q l < 2 ^ width b := by
    rw [Request.value_eq]
    calc
      _ ≤ ∑ _j ∈ Finset.range (r.size q l), 1 := Finset.sum_le_sum fun j _ => by
        cases r.test q l j <;> decide
      _ < _ := by simpa using h.trans_lt hz
  have hport (c : Bool) (n : ℕ) (hn : n ≤ q.size) := count (.port c n) (hn.trans edge)
  have hvertex (n : ℕ) := count (.vertex n) ((Nat.min_le_right n l.vertices).trans vertex)
  have hpack := count (.pack p.edge p.ends) edge
  simp only [Proposal.fields, List.forall_mem_cons] at hp
  rcases hp with ⟨_, _, _, hr, hc, ht, hv, hU, hk, _⟩
  fin_cases s
  · exact ⟨hport false p.edge he, hr⟩
  · exact ⟨hport true p.edge he, hc⟩
  · exact ⟨hport false b.edges hsize.le, ht⟩
  · exact ⟨hvertex _, hv⟩
  · exact ⟨hvertex b.vertices, hU⟩
  · exact ⟨hpack, hk⟩

/-- The six complete integers are characterized by their six count requests. In particular
the truthful row total selects the vertex prefix for the requested child's actual side. -/
private theorem counts_eq_iff (q : EndpointQuery) (l : Labels) (b : Public) (p : Proposal)
    (hsize : b.edges = q.size) (hu : b.vertices = l.vertices) :
    p.counts = actualCounts q l p.edge b.child p.ends ↔ ∀ s : Fin 6,
      (request (selected b p (s.val + 2)).1).value q l = (selected b p (s.val + 2)).2 := by
  constructor
  · intro h s
    fin_cases s <;> simp [selected, request, h, actualCounts, hsize, hu]
  · intro h
    have h₀ := h 0
    have h₁ := h 1
    have h₂ := h 2
    have h₃ := h 3
    have h₄ := h 4
    have h₅ := h 5
    change (Request.port false p.edge).value q l = p.counts.rowPrefix at h₀
    change (Request.port true p.edge).value q l = p.counts.colPrefix at h₁
    change (Request.port false b.edges).value q l = p.counts.rowTotal at h₂
    change (Request.vertex (if b.child < p.counts.rowTotal then p.ends.1 else p.ends.2)).value q l =
      p.counts.vertexPrefix at h₃
    change (Request.vertex b.vertices).value q l = p.counts.vertexTotal at h₄
    change (Request.pack p.edge p.ends).value q l = p.counts.classRank at h₅
    rw [hsize] at h₂
    rw [hu] at h₄
    cases hc : p.counts with
    | mk rp cp rt vp vt cr =>
      simp only [hc] at h₀ h₁ h₂ h₃ h₄ h₅
      simp only [actualCounts, h₀, h₁, h₂, h₃, h₄, h₅]

/-- The eight branch checks with universal bit challenges implement the fixed proposal's
parent, local arithmetic and six count obligations. -/
theorem forall_branch_iff {q : EndpointQuery} {l : Labels} (b : Public) (p : Proposal)
    (hsize : b.edges = q.size) (hu : b.vertices = l.vertices)
    (hparent : q.accepts p.edge p.ends → p.edge ≤ q.size)
    (hp : ∀ n ∈ p.fields, n < 2 ^ width b) (localTest : Prop) :
    (∀ (s : Fin 8) (j : Fin (2 ^ Nat.clog 2 (width b))),
      verdict q l localTest (q.accepts p.edge p.ends) (branch b p (width b) s.val j.val)) ↔
      q.accepts p.edge p.ends ∧ p.counts = actualCounts q l p.edge b.child p.ends ∧ localTest := by
  let z : Fin (2 ^ Nat.clog 2 (width b)) := ⟨0, by positivity⟩
  constructor
  · intro h
    have hl : localTest := h 0 z
    have hg : q.accepts p.edge p.ends := h 1 z
    refine ⟨hg, (counts_eq_iff q l b p hsize hu).2 (fun s => ?_), hl⟩
    obtain ⟨ha, hx⟩ := all_counts hsize hu (hparent hg) hp s
    exact (select_eq_iff q l b p _ _ (by omega : 2 ≤ s.val + 2) ha hx).1
      (h ⟨s.val + 2, by omega⟩)
  · rintro ⟨hg, hc, hl⟩ s j
    by_cases hs₀ : s.val = 0
    · simp only [branch, hs₀, ↓reduceIte, verdict, hl]
    by_cases hs₁ : s.val = 1
    · simp only [branch, hs₁, Nat.reduceEqDiff, ↓reduceIte, verdict, hg]
    let i : Fin 6 := ⟨s.val - 2, by omega⟩
    have hi : i.val + 2 = s.val := by dsimp [i]; omega
    have h := (counts_eq_iff q l b p hsize hu).1 hc i
    rw [hi] at h
    exact (count_branch q l b p _ _ (by omega : 2 ≤ s.val) _ _).2 fun _ => congrArg
      (fun z : ℕ => z.testBit j.val) h

/-- The shared nine-field existential witness, the three universal selector bits, and the
universal bit-index challenge in their actual order. -/
@[expose] def witnessFlags (w : ℕ) : List Bool := List.replicate (9 * w) false ++
  (List.replicate 3 true ++ List.replicate (Nat.clog 2 w) true)

/-- Length of the entire physical witness and challenge prefix. -/
@[simp] theorem length_witnessFlags (w : ℕ) :
    (witnessFlags w).length = 9 * w + 3 + Nat.clog 2 w := by
  simp only [witnessFlags, List.length_append, List.length_replicate]
  omega

/-- The flag tape is polynomial-time computable from the binary graph parameters. -/
theorem computableInPolyTime_witnessFlags : MultiTapeTM.ComputableInPolyTime
    (fun b : Public => witnessFlags (width b)) encPublic MultiTapeTM.encBits := by
  open MultiTapeTM.ComputableInPolyTime in
    have hw := computableInPolyTime_width
    exact ((bitsReplicate false).comp (unary_mul' (const 9) hw)).bitsAppend
      ((const (List.replicate 3 true)).bitsAppend
        ((bitsReplicate true).comp (binary_clog_two.comp (unary_to_binary.comp hw))))

/-- Acceptance of one routed terminal. The original parsed proposal supplies both the local
arithmetic claim and the parent endpoint claim even on branches that check a single count bit. -/
@[expose] def routedValue (q : EndpointQuery) (l : Labels) (b : Public)
    (localTest : Proposal → Prop) (choices : List Bool) : Prop :=
  let data := Dispatch.run (b, choices)
  verdict q l (localTest data.1) (q.accepts data.1.edge data.1.ends) data.2

private theorem plays_challenges (q : EndpointQuery) (l : Labels) (b : Public)
    (localTest : Proposal → Prop) (xs : List Bool) (hx : xs.length = 9 * width b) :
    let p := parse (width b) xs
    QuantifiedWord.plays (routedValue q l b localTest) xs
      (List.replicate 3 true ++ List.replicate (Nat.clog 2 (width b)) true) ↔
      ∀ (s : Fin 8) (j : Fin (2 ^ Nat.clog 2 (width b))),
        verdict q l (localTest p) (q.accepts p.edge p.ends) (branch b p (width b) s.val j.val) := by
  open QuantifiedWord in
    dsimp only
    rw [plays_forall_field]
    apply forall_congr'
    intro sel
    have h := plays_forall_field (routedValue q l b localTest)
      (xs ++ BitString.lowBits 3 sel.val) [] (Nat.clog 2 (width b))
    simpa only [List.append_nil, plays, List.append_assoc, routedValue, run_prefix b xs hx] using h

/-- The entire concrete word game decides precisely the child endpoint claim. Every branch
now has one terminal: the local deterministic predicate, the parent query, or one count bit. -/
theorem child_iff_plays_dispatch {U a : ℕ} (seed : SeededLabels.Seed U (6 * a))
    (i : Fin a) (group : ℕ) {q : EndpointQuery} {es : List (ℕ × ℕ)} (hq : q.Represents es)
    (hkeys : ∀ e p, q.accepts e p → p.1 < U ∧ p.2 < U) (j : ℕ) (answer : ℕ × ℕ) :
    let l := Labels.ofSeed U a seed i group
    let b : Public := ⟨q.size, U, j⟩
    let localTest (p : Proposal) := SeededChildWitness.run
      ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, i.val, group, j,
        p.ends, answer, p.counts⟩ = true
    (q.child (l.split q)).accepts j answer ↔
      QuantifiedWord.plays (routedValue q l b localTest) [] (witnessFlags (width b)) := by
  intro l b localTest
  let w := width b
  let P (p : Proposal) := q.accepts p.edge p.ends ∧
    p.counts = actualCounts q l p.edge j p.ends ∧ localTest p
  have h₁ := child_iff_plays seed i group hq hkeys j answer
  change (q.child (l.split q)).accepts j answer ↔
    QuantifiedWord.plays (fun xs => P (parse w xs)) [] (List.replicate (9 * w) false) at h₁
  rw [h₁]
  let V := routedValue q l b localTest
  let flags := List.replicate 3 true ++ List.replicate (Nat.clog 2 w) true
  have hterm (xs : List Bool) (hx : xs.length = 9 * w) :
      QuantifiedWord.plays V xs flags ↔ P (parse w xs) :=
    (plays_challenges q l b localTest xs hx).trans (forall_branch_iff b (parse w xs) rfl rfl
      (fun hp => hq.1 ▸ ((hq.2 _ _).mp hp).1.le) (parse_fields_lt _ _) _)
  have hleft := QuantifiedWord.plays_exists_field (fun xs => P (parse w xs)) [] [] (9 * w)
  have hright := QuantifiedWord.plays_exists_field V [] flags (9 * w)
  simp only [List.append_nil, List.nil_append, QuantifiedWord.plays] at hleft
  simp only [List.nil_append] at hright
  change _ ↔ QuantifiedWord.plays V [] (List.replicate (9 * w) false ++ flags)
  rw [hleft, hright]
  exact exists_congr fun x => (hterm _ (BitString.length_lowBits (9 * w) x.val)).symm

end Turing.MultiTapeATM.SeededChildCounts
