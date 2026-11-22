/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Resolution.SemanticDerivation

/-!
# Tests: `LineProof` DAG combinators, simulation and semantic refutations

Checked examples for `Cslib.Logic.PL.LineProof` and
`Cslib.Logic.PL.CNF.IsProof.isSemanticRefutation`:

* **DAG sharing in `LineProof.comp`**: replaying a 5-line derivation `[7, 4, 3, 2, 1]` on top of
  `[3, 2, 1]` reuses both the shared hypotheses `1, 2` and the shared derived line `3 = 1 + 2`,
  prepending exactly the 2 new lines (`ls''.length = 2 < 5`).
* **Stepwise rule simulation (`LineProof.Grows.simulate` and `LineProof.simulate`)**: ternary
  addition rules `a, b, c ⊢ a + b + c` simulate in binary addition `a, b ⊢ a + b` with `k = 2`
  lines per step when referencing translated premises directly in `ls'`, and via standalone
  5-line rule derivations replayed with `LineProof.comp`.
* **Resolution to `SemanticDerivation`**: a 7-line resolution refutation of the split formula
  `(y ∧ (¬y ∨ x₀)) ∧ (z ∧ (¬z ∨ ¬x₀))`, where both sides are individually satisfiable, yields a
  7-line `IsSemanticRefutation` over `SemanticDerivation.initSets`.
-/

namespace CslibFrontierTests.LineProof

open Cslib Cslib.Logic.PL Cslib.Logic.PL.SemanticDerivation

/-! ### DAG sharing in `LineProof.comp` -/

/-- Binary addition rules `a, b ⊢ a + b` on natural numbers. -/
private def addRules : Set (LineRule ℕ) :=
  {r | ∃ a b, r = ⟨[a, b], a + b⟩}

/-- Ternary addition rules `a, b, c ⊢ a + b + c` on natural numbers. -/
private def add3Rules : Set (LineRule ℕ) :=
  {r | ∃ a b c, r = ⟨[a, b, c], a + b + c⟩}

/-- Base derivation `[3, 2, 1]` from `{1, 2, 4}`: hypotheses `1` and `2`, then `3 = 1 + 2`. -/
private theorem base_deriv : LineProof addRules {1, 2, 4} [3, 2, 1] :=
  (((LineProof.nil (R := addRules)).hyp (by simp)).hyp (by simp)).step
    (r := ⟨[1, 2], 1 + 2⟩) ⟨1, 2, rfl⟩ (by simp)

/-- Extension derivation `[7, 4, 3, 2, 1]` of length `5`: re-derives `3 = 1 + 2`, adds hypothesis
`4`, and derives `7 = 3 + 4`. -/
private theorem ext_deriv : LineProof addRules {1, 2, 4} [7, 4, 3, 2, 1] :=
  (base_deriv.hyp (by simp)).step (r := ⟨[3, 4], 3 + 4⟩) ⟨3, 4, rfl⟩ (by simp)

/-- Replaying `[7, 4, 3, 2, 1]` onto `[3, 2, 1]` via `LineProof.comp` skips `1`, `2` and the
already-derived `3`, adding exactly `2 < 5` lines (`4` and `7`). -/
example : ∃ ls'', LineProof addRules {1, 2, 4} (ls'' ++ [3, 2, 1]) ∧
    (∀ x ∈ ([7, 4, 3, 2, 1] : List ℕ), x ∈ ls'' ++ [3, 2, 1]) ∧
    ls''.length = 2 ∧ ls''.length < ([7, 4, 3, 2, 1] : List ℕ).length := by
  obtain ⟨ls'', h'', hmem, hsub, hnodup, hdisj⟩ :=
    ext_deriv.comp base_deriv fun x hx => Or.inl hx
  have hsub24 : ∀ x ∈ ls'', x = 7 ∨ x = 4 := by
    intro x hx
    have hx5 := hsub.subset hx
    have hxnot := hdisj x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx5 hxnot
    omega
  have h7 : 7 ∈ ls'' := by simpa using hmem 7 (by simp)
  have h4 : 4 ∈ ls'' := by simpa using hmem 4 (by simp)
  have hfin : ls''.toFinset = {7, 4} := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hsub24 x, by rintro (rfl | rfl) <;> assumption⟩
  have heq : ls''.length = 2 := by
    rw [← List.toFinset_card_of_nodup hnodup, hfin]
    decide
  exact ⟨ls'', h'', hmem, heq, by simp [heq]⟩

/-- Soundness (`LineProof.holds`) and rule monotonicity (`LineProof.mono_rules`): every line
derived from `{1, 2, 4}` under `addRules` (and hence under `addRules ∪ add3Rules`) is positive. -/
example : (∀ x ∈ ([7, 4, 3, 2, 1] : List ℕ), 0 < x) ∧
    LineProof (addRules ∪ add3Rules) {1, 2, 4} [7, 4, 3, 2, 1] := by
  refine ⟨ext_deriv.holds (fun x hx => by rcases hx with rfl | rfl | rfl <;> decide)
    fun r hr hp => ?_, ext_deriv.mono_rules Set.subset_union_left⟩
  obtain ⟨a, b, rfl⟩ := hr
  exact Nat.add_pos_left (hp a (by simp)) b

/-! ### Stepwise simulation (`LineProof.Grows.simulate` and `LineProof.simulate`) -/

/-- A 3-line ternary-addition derivation `[7, 3, 1]` (`1`, `3 = 1 + 1 + 1`, `7 = 3 + 3 + 1`). -/
private theorem ternary_deriv : LineProof add3Rules {1} [7, 3, 1] :=
  (((LineProof.nil (R := add3Rules)).hyp rfl).step
    (r := ⟨[1, 1, 1], 1 + 1 + 1⟩) ⟨1, 1, 1, rfl⟩ (by simp)).step
    (r := ⟨[3, 3, 1], 3 + 3 + 1⟩) ⟨3, 3, 1, rfl⟩ (by simp)

/-- Via `LineProof.Grows.simulate`, each ternary step `a + b + c` reuses `a, b, c ∈ ls'` directly
in `k = 2` binary steps (`a + b`, then `(a + b) + c`), giving at most `2 * 3 = 6` lines. -/
example : ∃ ls', LineProof addRules {1} ls' ∧ 7 ∈ ls' ∧ 3 ∈ ls' ∧ ls'.length ≤ 6 ∧
    ∀ x ∈ ls', 0 < x := by
  obtain ⟨ls', g, hmem⟩ := LineProof.Grows.simulate (R₂ := addRules) (Γ₂ := {1}) id 2
    ternary_deriv .nil
    (fun h' x hx _ => ⟨x :: _, (LineProof.Grows.hyp h' hx).mono (by decide), List.mem_cons_self⟩)
    fun h' r hr _ hp => by
      obtain ⟨a, b, c, rfl⟩ := hr
      have ha : a ∈ _ := (hp a (by simp)).2
      have hb : b ∈ _ := (hp b (by simp)).2
      have hc : c ∈ _ := (hp c (by simp)).2
      have g₁ := LineProof.Grows.step (r := ⟨[a, b], a + b⟩) h' ⟨a, b, rfl⟩ (by simp [ha, hb])
      have g₂ := LineProof.Grows.step (r := ⟨[a + b, c], (a + b) + c⟩) g₁.lineProof
        ⟨a + b, c, rfl⟩ (by simp [hc])
      exact ⟨_, g₁.trans g₂, List.mem_cons_self⟩
  refine ⟨ls', g.lineProof, hmem 7 (by simp), hmem 3 (by simp), g.length_of_nil,
    g.lineProof.holds (by simp) fun r hr hp => ?_⟩
  obtain ⟨a, b, rfl⟩ := hr
  exact Nat.add_pos_left (hp a (by simp)) b

/-- Standalone rule derivations of length `5` (`[a + b + c, a + b, c, b, a]`) translate `[7, 3, 1]`
via `LineProof.simulate` into at most `5 * 3 = 15` binary-addition lines. -/
example : ∃ ls', LineProof addRules {1} ls' ∧ (∀ x ∈ ([7, 3, 1] : List ℕ), x ∈ ls') ∧
    ls'.length ≤ 15 := by
  obtain ⟨ls', h', hmem, hlen⟩ := ternary_deriv.simulate (R₂ := addRules) (Γ₂ := {1}) id 5
    (fun x hx _ => ⟨[x], (LineProof.nil (R := addRules)).hyp hx, by simp, by simp⟩)
    fun r hr _ _ => by
      obtain ⟨a, b, c, rfl⟩ := hr
      set S : Set ℕ := {1} ∪ {y | y ∈ List.map id [a, b, c]}
      have ha : a ∈ S := Or.inr (by simp)
      have hb : b ∈ S := Or.inr (by simp)
      have hc : c ∈ S := Or.inr (by simp)
      have hm : LineProof addRules S [a + b + c, a + b, c, b, a] :=
        (((((LineProof.nil (R := addRules)).hyp ha).hyp hb).hyp hc).step
          (r := ⟨[a, b], a + b⟩) ⟨a, b, rfl⟩ (by simp)).step
          (r := ⟨[a + b, c], a + b + c⟩) ⟨a + b, c, rfl⟩ (by simp)
      exact ⟨_, hm, by simp, by simp⟩
  exact ⟨ls', h', hmem, hlen⟩

/-! ### Resolution refutations as semantic refutations -/

/-- Alice's CNF `y ∧ (¬y ∨ x₀)` over `Fin 1 ⊕ Unit` (satisfiable at `x₀ = true, y = true`). -/
private def cnfA : CNF (Fin 1 ⊕ Unit) :=
  [[(.inr (), true)], [(.inr (), false), (.inl 0, true)]]

/-- Bob's CNF `z ∧ (¬z ∨ ¬x₀)` over `Fin 1 ⊕ Unit` (satisfiable at `x₀ = false, z = true`). -/
private def cnfB : CNF (Fin 1 ⊕ Unit) :=
  [[(.inr (), true)], [(.inr (), false), (.inl 0, false)]]

private abbrev SharedVar := Fin 1 ⊕ (Unit ⊕ Unit)

/-- The combined CNF over shared variable `x₀` and private variables `y`, `z`. -/
private def splitCNF : CNF SharedVar :=
  cnfA.relabel (Sum.map id Sum.inl) ++ cnfB.relabel (Sum.map id Sum.inr)

/-- Explicit 7-line resolution refutation of `splitCNF`, newest line first. -/
private def splitRefutation : List (Clause SharedVar) :=
  let cy : Clause SharedVar := [(.inr (.inl ()), true)]
  let cyx : Clause SharedVar := [(.inr (.inl ()), false), (.inl 0, true)]
  let cx : Clause SharedVar := cy.resolvent cyx (.inr (.inl ()))
  let cz : Clause SharedVar := [(.inr (.inr ()), true)]
  let czx : Clause SharedVar := [(.inr (.inr ()), false), (.inl 0, false)]
  let cnx : Clause SharedVar := cz.resolvent czx (.inr (.inr ()))
  [cx.resolvent cnx (.inl 0), cnx, czx, cz, cx, cyx, cy]

private theorem isProof_splitRefutation : splitCNF.IsProof splitRefutation := by
  have h1 : splitCNF.IsProof [[(.inr (.inl ()), true)]] :=
    CNF.IsProof.nil.mem (by decide)
  have h2 := h1.mem (c := [(.inr (.inl ()), false), (.inl 0, true)]) (by decide)
  have h3 := h2.resolvent (c₁ := [(.inr (.inl ()), true)])
    (c₂ := [(.inr (.inl ()), false), (.inl 0, true)]) (.inr (.inl ()))
    (by decide) (by decide) (by decide) (by decide)
  have h4 := h3.mem (c := [(.inr (.inr ()), true)]) (by decide)
  have h5 := h4.mem (c := [(.inr (.inr ()), false), (.inl 0, false)]) (by decide)
  have h6 := h5.resolvent (c₁ := [(.inr (.inr ()), true)])
    (c₂ := [(.inr (.inr ()), false), (.inl 0, false)]) (.inr (.inr ()))
    (by decide) (by decide) (by decide) (by decide)
  exact h6.resolvent (c₁ := Clause.resolvent [(.inr (.inl ()), true)]
      [(.inr (.inl ()), false), (.inl 0, true)] (.inr (.inl ())))
    (c₂ := Clause.resolvent [(.inr (.inr ()), true)]
      [(.inr (.inr ()), false), (.inl 0, false)] (.inr (.inr ())))
    (.inl 0) (by decide) (by decide) (by decide) (by decide)

/-- Both sides are individually satisfiable (so the interpolation setup is nonvacuous), while
`CNF.IsProof.isSemanticRefutation` turns the 7-line resolution refutation into a 7-line semantic
refutation over `initSets`, certifying that no joint model exists. -/
example :
    let 𝒜 : Set (Set (Fin 1 ⊕ Unit → Bool)) := (fun c => {σ | c.eval σ = true}) '' {c | c ∈ cnfA}
    let ℬ : Set (Set (Fin 1 ⊕ Unit → Bool)) := (fun c => {σ | c.eval σ = true}) '' {c | c ∈ cnfB}
    (fun _ => true, fun _ => true) ∈ Models 𝒜 ∧
    (fun _ => false, fun _ => true) ∈ Models ℬ ∧
    IsSemanticRefutation (initSets 𝒜 ℬ)
      (fun j : Fin splitRefutation.reverse.length =>
        {σ | splitRefutation.reverse[j].eval σ = true}) ∧
    ¬ ∃ σ : SharedVar → Bool, ∀ S ∈ initSets 𝒜 ℬ, σ ∈ S := by
  intro 𝒜 ℬ
  have hA : (fun _ : Fin 1 => true, fun _ : Unit => true) ∈ Models 𝒜 := by
    rintro _ ⟨c, hc, rfl⟩
    simp only [Set.mem_ofPred_eq, cnfA, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  have hB : (fun _ : Fin 1 => false, fun _ : Unit => true) ∈ Models ℬ := by
    rintro _ ⟨c, hc, rfl⟩
    simp only [Set.mem_ofPred_eq, cnfB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  have href : IsSemanticRefutation (initSets 𝒜 ℬ)
      (fun j : Fin splitRefutation.reverse.length =>
        {σ | splitRefutation.reverse[j].eval σ = true}) := by
    refine isProof_splitRefutation.isSemanticRefutation (fun c hc => ?_) (by decide)
    simp only [splitCNF, CNF.relabel, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · refine Or.inl ⟨{σ | d.eval σ = true}, ⟨d, hd, rfl⟩, ?_⟩
      ext σ
      simp [leftCylinder]
    · refine Or.inr ⟨{σ | d.eval σ = true}, ⟨d, hd, rfl⟩, ?_⟩
      ext σ
      simp [rightCylinder]
  exact ⟨hA, hB, href, href.not_exists_forall_mem⟩

end CslibFrontierTests.LineProof
