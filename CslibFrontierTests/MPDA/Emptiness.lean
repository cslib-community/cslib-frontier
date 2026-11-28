/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.EmptinessComplete
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Clients of the emptiness procedure under module encapsulation. On two stacks, the MPDA
`crossNop` reads `nop ↓₀ ↓₁ ↑₀ ↑₁` along the control states `0 → 1 → 2 → 3 → 4 → 5`. That run is
accepting and `2`-hole-bounded, so repaired Algorithm 1 (`MPDA.isEmpty`) answers `false`, by
Theorem 1 (`MPDA.isEmpty_iff`). Its printed-start variant (`isEmptyPrinted`, defined here), which
starts from the initial state as line 10 of Algorithm 1 as printed in
[AkshayGastinKrishnaRoychowdhury2020] does and otherwise is `MPDA.isEmpty`, answers `true`. From
state `0` it can only open empty holes `(i, 0, 0)`, since `0` has no push, and cannot pop, so
every list it reaches ends in state `0`; and the well-nested acceptance check of line 3 cannot pass
the crossing pushes and pops. So starting from the initial state is not complete. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MPDA.Emptiness

open Cslib Cslib.Automata Cslib.Automata.MPDA

section Printed

variable {n : ℕ} {State Symbol Γ : Type*} [Fintype State] [DecidableEq State] [Fintype Symbol]
  [Fintype Γ] [DecidableEq Γ] (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- The initial lists of the search as printed (line 10 of Algorithm 1): an initial state and no
holes. -/
private def startLists : Finset (HoleList n State) :=
  (Finset.univ.filter (· ∈ M.start)).image fun s => ⟨[], s⟩

/-- The printed-start variant of repaired Algorithm 1: the search from the initial state. -/
private def isEmptyPrinted [DecidablePred (· ∈ M.accept)] (K : ℕ) : Bool :=
  M.isEmptyFrom (startLists M) K

omit [Fintype Symbol] [Fintype Γ] [DecidableEq Γ] [∀ s μ s', Decidable (M.Tr s μ s')] in
private theorem mem_startLists {μ : HoleList n State} :
    μ ∈ startLists M ↔ μ.holes = [] ∧ μ.last ∈ M.start := by
  obtain ⟨holes, last⟩ := μ
  simp [startLists, eq_comm, and_comm]

end Printed

/-- `nop`, then `↓₀ ↓₁ ↑₀ ↑₁`, along the control states `0 → 1 → 2 → 3 → 4 → 5`. -/
private def crossNop : MPDA 2 (Fin 6) Unit Unit where
  Tr s μ s' := match s.val, μ.2, s'.val with
    | 0, .nop, 1 => True
    | 1, .push i _, 2 => i = 0
    | 2, .push i _, 3 => i = 1
    | 3, .pop i _, 4 => i = 0
    | 4, .pop i _, 5 => i = 1
    | _, _, _ => False
  start := {0}
  accept := {5}

private instance (s : Fin 6) (μ : Unit × Op 2 Unit) (s' : Fin 6) :
    Decidable (crossNop.Tr s μ s') := by
  unfold crossNop
  dsimp only
  split <;> infer_instance

private instance : DecidablePred (· ∈ crossNop.start) := fun s =>
  inferInstanceAs (Decidable (s = 0))

private instance : DecidablePred (· ∈ crossNop.accept) := fun s =>
  inferInstanceAs (Decidable (s = 5))

/-- The run. -/
private def run : List (Unit × Op 2 Unit) :=
  [((), .nop), ((), .push 0 ()), ((), .push 1 ()), ((), .pop 0 ()), ((), .pop 1 ())]

private theorem run_run : crossNop.configLTS.MTr ⟨0, Stacks.empty⟩ run ⟨5, Stacks.empty⟩ := by
  refine .stepL (s2 := ⟨1, ![[], []]⟩) ?_ <|
    .stepL (s2 := ⟨2, ![[()], []]⟩) ?_ <|
    .stepL (s2 := ⟨3, ![[()], [()]]⟩) ?_ <|
    .stepL (s2 := ⟨4, ![[], [()]]⟩) ?_ <|
    .stepL ?_ .refl <;>
  refine configLTS_tr.mpr ⟨by decide, ?_⟩ <;>
  simp only [Op.apply_nop, Op.apply_push, Op.apply_pop] <;>
  funext k <;> fin_cases k <;> simp [Stacks.empty]

/-- The run is `2`-hole-bounded: a well-nested `nop`, two holes of one push each, then two pops
that close them. -/
private theorem run_holeBounded : HoleBounded 2 run := by
  have d₁ : HoleDerivation 2 [] ([] ++ [((), .nop)] : List (Unit × Op 2 Unit)) :=
    HoleDerivation.nil.wellNested (.nop .nil)
  have d₂ := d₁.hole (i := 0) (by decide) (HoleBlock.snoc (a := ()) (γ := ()) .nil .nil)
  have d₃ := d₂.hole (i := 1) (by decide) (HoleBlock.snoc (a := ()) (γ := ()) .nil .nil)
  have d₄ := (d₃.pop (pre := []) (b := ()) (by simp)).close (pre := [])
  have d₅ := (d₄.pop (pre := []) (post := []) (b := ()) (by simp)).close (pre := []) (post := [])
  exact d₅.holeBounded

/-- The word of the run is accepted by a `2`-hole-bounded run. -/
private theorem mem_boundedLanguage :
    run.map Prod.fst ∈ crossNop.boundedLanguage (HoleBounded 2) :=
  ⟨0, rfl, 5, rfl, run, rfl, run_run, run_holeBounded⟩

/-- The repaired search finds the run. -/
example : crossNop.isEmpty 2 = false := isEmpty_eq_false_of_mem_boundedLanguage mem_boundedLanguage

/-- Well-nested runs of `crossNop` stay put, apart from the `nop` from `0` to `1`. -/
private theorem wellNestedReach {s t : Fin 6} (h : crossNop.WellNestedReach s t) :
    t = s ∨ (s = 0 ∧ t = 1) := by
  induction h with
  | refl => exact .inl rfl
  | @nop s₁ s₂ s₃ a hT _ ih =>
    have : ∀ s₁ s₂ : Fin 6, crossNop.Tr s₁ ((), .nop) s₂ → s₁ = 0 ∧ s₂ = 1 := by decide
    obtain ⟨rfl, rfl⟩ := this _ _ hT
    rcases ih with rfl | ⟨h, -⟩
    · exact .inr ⟨rfl, rfl⟩
    · exact absurd h (by decide)
  | @pushPop s₁ s₂ s₃ s₄ s₅ a b i γ hT _ hT' _ ih _ =>
    have : ∀ (s₁ s₂ s₄ : Fin 6) (i : Fin 2), crossNop.Tr s₁ ((), .push i ()) s₂ →
        ¬crossNop.Tr s₂ ((), .pop i ()) s₄ ∧ s₂ ≠ 0 := by decide
    obtain ⟨hno, hs₂⟩ := this s₁ s₂ s₄ i hT
    rcases ih with rfl | ⟨h, -⟩
    · exact absurd hT' hno
    · exact absurd h hs₂

/-- Every list reached by the printed search ends in state `0`. -/
private theorem last_eq_zero {μ : HoleList 2 (Fin 6)}
    (h : crossNop.Reachable 2 (startLists crossNop) μ) : μ.last = 0 := by
  induction h with
  | init hμ => exact ((mem_startLists _).mp hμ).2
  | @step μ ν _ hν ih =>
    unfold successors at hν
    rcases Finset.mem_union.mp hν with hν | hν
    · split_ifs at hν
      · obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
        unfold addHole at hν
        obtain ⟨⟨s, s'⟩, hp, rfl⟩ := Finset.mem_image.mp hν
        obtain ⟨hp, rfl⟩ := Finset.mem_filter.mp hp
        rw [ih] at hp
        rcases ((mem_holeSegments (M := crossNop)).mp hp).cases_head with h | ⟨c, ⟨γ, hc⟩, -⟩
        · exact h.symm
        · obtain ⟨a, s₁, hT, -⟩ := (mem_atomicHoles (M := crossNop)).mp hc
          have hpush : ∀ (s₁ : Fin 6) (i : Fin 2) (a γ : Unit),
              ¬crossNop.Tr 0 (a, .push i γ) s₁ := by
            decide
          exact absurd hT (hpush _ _ _ _)
      · simp at hν
    · obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      unfold addPop at hν
      split at hν
      · simp at hν
      · have hpop : ∀ (i : Fin 2) (s' : Fin 6) (γ : Unit) (b : Unit),
            ¬crossNop.Tr 0 (b, .pop i γ) s' := by
          decide
        rcases Finset.mem_union.mp hν with hν | hν
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hν
          obtain ⟨-, -, -, ⟨b, hT⟩, -⟩ := Finset.mem_filter.mp ht
          rw [ih] at hT
          exact absurd hT (hpop _ _ _ _)
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hν
          obtain ⟨-, ⟨-, -, ⟨b, hT⟩, -⟩, -⟩ := Finset.mem_filter.mp ht
          rw [ih] at hT
          exact absurd hT (hpop _ _ _ _)

/-- The search from `init` answers `true` when no list it reaches can be completed. -/
private theorem isEmptyFrom_eq_true {n : ℕ} {State Symbol Γ : Type} [Fintype State]
    [DecidableEq State] [Fintype Symbol] [Fintype Γ] [DecidableEq Γ]
    {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')] [DecidablePred (· ∈ M.accept)]
    {K : ℕ} {init : Finset (HoleList n State)} (hinit : ∀ μ ∈ init, μ.holes = [])
    (h : ∀ μ, M.Reachable K init μ → ∀ f ∈ M.accept, (μ.last, f) ∉ M.wellNestedPairs) :
    M.isEmptyFrom init K = true := by
  rw [← Bool.not_eq_false]
  intro hfalse
  unfold isEmptyFrom at hfalse
  rw [decide_eq_false_iff_not, not_not] at hfalse
  obtain ⟨μ, hμ, -, f, hf, hwr⟩ := hfalse
  exact h μ ((mem_explore hinit).mp hμ) f (Finset.mem_filter.mp hf).2 hwr

/-- The search as printed misses the run. -/
example : isEmptyPrinted crossNop 2 = true := by
  refine isEmptyFrom_eq_true (fun ν hν => ((mem_startLists _).mp hν).1) fun μ hμ f hf hwr => ?_
  rw [last_eq_zero hμ] at hwr
  obtain rfl : f = 5 := hf
  rcases wellNestedReach ((mem_wellNestedPairs crossNop).mp hwr) with h | ⟨-, h⟩ <;>
    exact absurd h (by decide)

end CslibFrontierTests.MPDA.Emptiness
