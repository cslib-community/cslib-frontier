/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Emptiness
public import Mathlib.Data.FinEnum

/-! # Well-nested witnesses

A pair `(s, s')` of the set `WR` of [AkshayGastinKrishnaRoychowdhury2020] is unrolled into a
well-nested run of the control from `s` to `s'` (Algorithm 5 of Appendix C). The search
`MPDA.wnWitness k` tries the closure rules of `WellNestedReach` with fuel `k`: the identity pair, a
`nop` transition followed by a pair, and a push, a pair, the matching pop and a pair. Each rule
recurses with one unit of fuel less, so the search always terminates. A found sequence is a
well-nested run, and the search succeeds on every pair of the `k`-th iterate of the fixed point
that computes `WR` (`MPDA.wellNestedStep`). With the fuel used for `WR` (`MPDA.wrWitness`), it
therefore succeeds exactly on the pairs of `WR`.

Algorithm 5 as printed recurses on pairs chosen without such a measure: its last case may choose the
pair it was called on, so it need not terminate. The fuel is the repair.

The search enumerates letters, stack symbols and control states, so these types are `FinEnum`.

## Main definitions

- `MPDA.wnWitness`: the search for a well-nested run with fuel `k`.
- `MPDA.wrWitness`: the search with the fuel of `WR`.

## Main results

- `MPDA.wnWitness_spec`: a found sequence is well-nested and runs the control from `s` to `s'`.
- `MPDA.isSome_wrWitness`: the search succeeds on every pair of `WR`.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Symbol Γ : Type*} [FinEnum State] [FinEnum Symbol] [FinEnum Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- The search for a well-nested run of the control from `s` to `s'`, with fuel `k`: the empty
run, a `nop` transition followed by a run, or a push, a run, the matching pop and a run. -/
@[expose] def wnWitness : ℕ → State → State → Option (List (Symbol × Op n Γ))
  | 0, _, _ => none
  | k + 1, s, s' =>
    if s = s' then some [] else
      ((FinEnum.toList (Symbol × State)).findSome? fun (a, s₂) =>
        if M.Tr s (a, .nop) s₂ then (wnWitness k s₂ s').map ((a, .nop) :: ·) else none) <|>
      ((FinEnum.toList (Symbol × Symbol × Fin n × Γ × State × State × State)).findSome?
        fun (a, b, i, γ, s₂, s₃, s₄) =>
          if M.Tr s (a, .push i γ) s₂ ∧ M.Tr s₃ (b, .pop i γ) s₄ then
            (wnWitness k s₂ s₃).bind fun w₁ => (wnWitness k s₄ s').map fun w₂ =>
              (a, .push i γ) :: (w₁ ++ (b, .pop i γ) :: w₂)
          else none)

/-- The search for a well-nested run of the control from `s` to `s'`, with the fuel that computes
`WR`. -/
@[expose] def wrWitness (s s' : State) : Option (List (Symbol × Op n Γ)) :=
  M.wnWitness (Fintype.card (State × State)) s s'

variable {M}

/-- **Soundness of the search**: a found sequence is well-nested and runs the control from `s` to
`s'`. -/
theorem wnWitness_spec : ∀ {k : ℕ} {s s' : State} {w : List (Symbol × Op n Γ)},
    M.wnWitness k s s' = some w → WellNested w ∧ M.MTr s w s'
  | 0, _, _, _, h => by simp [wnWitness] at h
  | k + 1, s, s', w, h => by
    unfold wnWitness at h
    split_ifs at h with hss
    · obtain rfl := Option.some.inj h
      exact ⟨.nil, hss ▸ .refl⟩
    simp only [Option.orElse_eq_orElse, Option.orElse_eq_or] at h
    rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
    · obtain ⟨⟨a, s₂⟩, -, h⟩ := List.exists_of_findSome?_eq_some h
      split_ifs at h with hT
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hwn, hrun⟩ := wnWitness_spec hw'
      exact ⟨.nop hwn, .stepL hT hrun⟩
    · obtain ⟨⟨a, b, i, γ, s₂, s₃, s₄⟩, -, h⟩ := List.exists_of_findSome?_eq_some h
      split_ifs at h with hT
      obtain ⟨w₁, hw₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨w₂, hw₂, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hwn₁, hrun₁⟩ := wnWitness_spec hw₁
      obtain ⟨hwn₂, hrun₂⟩ := wnWitness_spec hw₂
      exact ⟨.pushPop hwn₁ hwn₂, .stepL hT.1 (hrun₁.comp _ (.stepL hT.2 hrun₂))⟩

/-- **Completeness of the search**: it succeeds on every pair of the `k`-th iterate of the fixed
point that computes `WR`. -/
theorem isSome_wnWitness : ∀ {k : ℕ} {s s' : State},
    (s, s') ∈ M.wellNestedStep^[k] ∅ → (M.wnWitness k s s').isSome
  | 0, _, _, h => by simp at h
  | k + 1, s, s', h => by
    rw [Function.iterate_succ_apply'] at h
    unfold wnWitness
    split_ifs with hss
    · rfl
    simp only [wellNestedStep, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.orElse_eq_orElse, Option.orElse_eq_or, Option.isSome_or, Bool.or_eq_true] at h ⊢
    rcases h with h | ⟨a, s₂, hT, h⟩ | ⟨a, b, i, γ, s₂, s₃, s₄, hT, h₂, hT', h₄⟩
    · exact absurd h hss
    · refine .inl (List.findSome?_isSome_iff.mpr ⟨(a, s₂), FinEnum.mem_toList _, ?_⟩)
      dsimp only
      simp only [hT, ↓reduceIte, Option.isSome_map]
      exact isSome_wnWitness h
    · refine .inr (List.findSome?_isSome_iff.mpr ⟨(a, b, i, γ, s₂, s₃, s₄), FinEnum.mem_toList _,
        ?_⟩)
      dsimp only
      obtain ⟨w₁, hw₁⟩ := Option.isSome_iff_exists.mp (isSome_wnWitness h₂)
      obtain ⟨w₂, hw₂⟩ := Option.isSome_iff_exists.mp (isSome_wnWitness h₄)
      simp [hT, hT', hw₁, hw₂]

/-- The search with the fuel of `WR` succeeds on every pair of `WR`. -/
theorem isSome_wrWitness {s s' : State} (h : (s, s') ∈ M.wellNestedPairs) :
    (M.wrWitness s s').isSome :=
  isSome_wnWitness h

/-- A pair has a found well-nested run exactly when it is in `WR`. -/
theorem isSome_wrWitness_iff {s s' : State} :
    (M.wrWitness s s').isSome ↔ (s, s') ∈ M.wellNestedPairs := by
  refine ⟨fun h => ?_, isSome_wrWitness⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hwn, hrun⟩ := wnWitness_spec hw
  exact (mem_wellNestedPairs M).mpr (wellNestedReach_iff.mpr ⟨w, hwn, hrun⟩)

end Cslib.Automata.MPDA
