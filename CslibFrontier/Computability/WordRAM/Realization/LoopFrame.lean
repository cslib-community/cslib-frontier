/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
public import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.DataStructure.Memory.TripleFrame
import CslibFrontier.Computability.WordRAM.Realization.Backend

/-!
# Loop framing, amortized potential inductions, and triple bridges for realization

This module connects `Memory.Triple` and `Memory.FramedTriple` to the `Realization` interpreter
(`memoryCost`, `clientResult`, `clientState`, `ValidHistory`), supplies the missing `Memory.alloc` /
`Memory.allocDirty` step lemmas, and provides single-pass invariant and amortized-potential loop
inductions for both `iterate` and `boundedWhile` with explicit `Memory.Modifies` framing.

## Main results

* `runClient_alloc`, `clientResult_alloc`, `clientState_alloc`, `validHistory_alloc_bind`,
  `clientResult_bind_alloc`, `clientState_bind_alloc`, `clientResult_bind_allocDirty`,
  `clientState_bind_allocDirty`: primitive allocation step reductions.
* `triple_iff_realization`, `framedTriple_iff_realization`: equivalence between memory triples
  and `Realization` judgments.
* `iterate_potential_spec`: amortized potential induction for `iterate` with `Memory.Modifies`
  framing.
* `boundedWhile_spec`: rank-bounded loop induction for `boundedWhile`.
* `boundedWhile_potential_spec`: amortized potential induction for `boundedWhile`.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-! ## Allocation step reductions -/

/-- Characterization of `(Memory.spec w).runClient` on `Memory.alloc`. -/
theorem runClient_alloc (w : ℕ) (s : Memory.State) (k : ℕ) :
    (Memory.spec w).runClient s (Memory.alloc k) =
      (s.frontier, ⟨clear s.mem s.frontier k, s.frontier + k⟩, [Memory.Op.alloc k]) :=
  rfl

/-- `Memory.alloc k` returns the old frontier. -/
@[simp, client_simps] theorem clientResult_alloc (w : ℕ) (s : Memory.State) (k : ℕ) :
    (Memory.spec w).clientResult s (Memory.alloc k) = s.frontier :=
  rfl

/-- `Memory.alloc k` clears `k` cells at the frontier and advances it by `k`. -/
theorem clientState_alloc (w : ℕ) (s : Memory.State) (k : ℕ) :
    (Memory.spec w).clientState s (Memory.alloc k) =
      ⟨clear s.mem s.frontier k, s.frontier + k⟩ :=
  rfl

/-- Split `ValidHistory` across `Memory.alloc k >>= q` in closed form. -/
theorem validHistory_alloc_bind {α : Type} {w : ℕ} {s : Memory.State} {k : ℕ}
    {q : ℕ → Memory.Prog α} (hk : Fits w (s.frontier + k))
    (hq : (Memory.spec w).ValidHistory ⟨clear s.mem s.frontier k, s.frontier + k⟩
      ((Memory.spec w).clientHistory ⟨clear s.mem s.frontier k, s.frontier + k⟩
        (q s.frontier))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.alloc k >>= q)) :=
  ⟨hk, hq⟩

/-- Reduce `clientResult` across `Memory.alloc k >>= q`. -/
theorem clientResult_bind_alloc {α : Type} (w : ℕ) (s : Memory.State) (k : ℕ)
    (q : ℕ → Memory.Prog α) :
    (Memory.spec w).clientResult s (Memory.alloc k >>= q) =
      (Memory.spec w).clientResult ⟨clear s.mem s.frontier k, s.frontier + k⟩ (q s.frontier) :=
  rfl

/-- Reduce `clientState` across `Memory.alloc k >>= q`. -/
theorem clientState_bind_alloc {α : Type} (w : ℕ) (s : Memory.State) (k : ℕ)
    (q : ℕ → Memory.Prog α) :
    (Memory.spec w).clientState s (Memory.alloc k >>= q) =
      (Memory.spec w).clientState ⟨clear s.mem s.frontier k, s.frontier + k⟩ (q s.frontier) :=
  rfl

/-- Reduce `clientResult` across `Memory.allocDirty k >>= q`. -/
theorem clientResult_bind_allocDirty {α : Type} (w : ℕ) (s : Memory.State) (k : ℕ)
    (q : ℕ → Memory.Prog α) :
    (Memory.spec w).clientResult s (Memory.allocDirty k >>= q) =
      (Memory.spec w).clientResult ⟨s.mem, s.frontier + k⟩ (q s.frontier) :=
  rfl

/-- Reduce `clientState` across `Memory.allocDirty k >>= q`. -/
theorem clientState_bind_allocDirty {α : Type} (w : ℕ) (s : Memory.State) (k : ℕ)
    (q : ℕ → Memory.Prog α) :
    (Memory.spec w).clientState s (Memory.allocDirty k >>= q) =
      (Memory.spec w).clientState ⟨s.mem, s.frontier + k⟩ (q s.frontier) :=
  rfl

/-! ## Triple bridges to `Realization` -/

/-- Equivalence between `Memory.Triple` and `Realization` interpreter quantities. -/
theorem triple_iff_realization {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {c : ℕ} {Q : α → Memory.State → Prop} :
    Memory.Triple w s p c Q ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      memoryCost p s ≤ c ∧
      Q ((Memory.spec 0).clientResult s p) ((Memory.spec 0).clientState s p) := by
  rw [Memory.triple_iff, ← memoryCost_eq_totalCost w, clientResult_width w, clientState_width w]

/-- Equivalence between `Memory.FramedTriple` and `Realization` interpreter quantities. -/
theorem framedTriple_iff_realization {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {c : ℕ} {S : Set ℕ} {Q : α → Memory.State → Prop} :
    Memory.FramedTriple w s p c S Q ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      memoryCost p s ≤ c ∧
      Memory.Modifies S s ((Memory.spec 0).clientState s p) ∧
      Q ((Memory.spec 0).clientResult s p) ((Memory.spec 0).clientState s p) := by
  rw [Memory.framedTriple_iff, ← memoryCost_eq_totalCost w, clientResult_width w,
    clientState_width w]

/-! ## Single-pass `iterate` potential induction -/

/-- Amortized potential-method induction for `iterate` with `Memory.Modifies` framing. -/
theorem iterate_potential_spec {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → δ × σ → Memory.State → Prop) (w : ℕ) (d : δ) (B n : ℕ)
    (inv : ℕ → σ → Memory.State → Prop) (pot : ℕ → σ → Memory.State → ℕ)
    (S : Set ℕ)
    (hstep : ∀ k < n, ∀ a s, inv k a s → safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      memoryCost (body (d, a)) s + pot (k + 1) a' s' ≤ pot k a s + B ∧
      Memory.Modifies S s s' ∧
      inv (k + 1) a' s')
    (a₀ : σ) (s₀ : Memory.State) (h₀ : inv 0 a₀ s₀) :
    let prog := iterate body d n a₀
    let a' := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe body safe w d n a₀ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ + pot n a' s' ≤ pot 0 a₀ s₀ + B * n ∧
    Memory.Modifies S s₀ s' ∧
    inv n a' s' := by
  induction n generalizing inv pot a₀ s₀ with
  | zero =>
    refine ⟨trivial, trivial, ?_, Memory.Modifies.refl S s₀, h₀⟩
    change memoryCost (Pure.pure a₀) s₀ + pot 0 a₀ s₀ ≤ pot 0 a₀ s₀ + B * 0
    rw [memoryCost_pure]
    omega
  | succ n ih =>
    obtain ⟨hs₀, hv₀, hc₀, hr₀, hinv₁⟩ := hstep 0 (Nat.succ_pos n) a₀ s₀ h₀
    set a₁ := (Memory.spec 0).clientResult s₀ (body (d, a₀))
    set s₁ := (Memory.spec 0).clientState s₀ (body (d, a₀))
    obtain ⟨hsn, hvn, hcn, hrn, hinvn⟩ :=
      ih (fun k => inv (k + 1)) (fun k => pot (k + 1))
        (fun k hk => hstep (k + 1) (Nat.succ_lt_succ hk)) a₁ s₁ hinv₁
    refine ⟨⟨hs₀, by rw [clientResult_width, clientState_width]; exact hsn⟩, ?_, ?_, ?_, ?_⟩
    · rw [iterate, validHistory_bind']; exact ⟨hv₀, hvn⟩
    · rw [iterate, memoryCost_bind', StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind, Nat.mul_succ]
      dsimp only [a₁, s₁] at hc₀ hcn
      omega
    · rw [iterate, StateTransitionSpec.clientState_bind]; exact Memory.Modifies.trans hr₀ hrn
    · rw [iterate, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      exact hinvn

/-! ## Single-pass `boundedWhile` invariant and potential inductions -/

/-- Amortized potential-method induction for `boundedWhile` with `Memory.Modifies` framing. -/
theorem boundedWhile_potential_spec {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    (w : ℕ) (d : δ) (B : ℕ)
    (I : σ → Memory.State → Prop) (rank pot : σ → Memory.State → ℕ) (S : Set ℕ)
    (hzero : ∀ a s, I a s → rank a s = 0 → ¬guard d a)
    (hstep : ∀ a s, I a s → guard d a →
      safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      memoryCost (body (d, a)) s + pot a' s' ≤ pot a s + B ∧
      Memory.Modifies S s s' ∧
      I a' s' ∧
      rank a' s' < rank a s) :
    ∀ (fuel : ℕ) (a : σ) (s : Memory.State), I a s → rank a s ≤ fuel →
      let prog := boundedWhile guard body d fuel a
      let a' := (Memory.spec 0).clientResult s prog
      let s' := (Memory.spec 0).clientState s prog
      whileSafe guard body safe w d fuel a s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
      ¬guard d a' ∧
      I a' s' ∧
      Memory.Modifies S s s' ∧
      memoryCost prog s + pot a' s' ≤ pot a s + B * rank a s := by
  intro fuel
  induction fuel with
  | zero =>
    intro a s hi hr
    have hg : ¬guard d a := hzero a s hi (Nat.eq_zero_of_le_zero hr)
    refine ⟨hg, trivial, hg, hi, Memory.Modifies.refl S s, ?_⟩
    simp only [boundedWhile, memoryCost_pure, StateTransitionSpec.clientResult_pure]
    rw [StateTransitionSpec.clientState_pure]
    omega
  | succ fuel ih =>
    intro a s hi hr
    by_cases hg : guard d a
    · obtain ⟨hs, hv₁, hc₁, hr₁, hi₁, hrank₁⟩ := hstep a s hi hg
      set a₁ := (Memory.spec 0).clientResult s (body (d, a))
      set s₁ := (Memory.spec 0).clientState s (body (d, a))
      obtain ⟨hs₂, hv₂, hstop, hi₂, hr₂, hc₂⟩ := ih a₁ s₁ hi₁ (by omega)
      have hbw : boundedWhile guard body d (fuel + 1) a =
          (body (d, a) >>= boundedWhile guard body d fuel) := by
        simp [boundedWhile, hg, ← PFunctor.FreeM.bind_eq_bind]
      have hmul : B + B * rank a₁ s₁ ≤ B * rank a s := by
        calc
          B + B * rank a₁ s₁ = B * (rank a₁ s₁ + 1) := by rw [Nat.mul_succ, Nat.add_comm]
          _ ≤ B * rank a s := Nat.mul_le_mul_left B hrank₁
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [whileSafe, hg, ↓reduceIte]
        exact ⟨hs, hs₂⟩
      · rw [hbw]
        exact validHistory_bind_step hv₁ hv₂
      · rw [hbw, StateTransitionSpec.clientResult_bind]
        exact hstop
      · rw [hbw, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
        exact hi₂
      · rw [hbw, StateTransitionSpec.clientState_bind]
        exact Memory.Modifies.trans hr₁ hr₂
      · rw [hbw, memoryCost_bind', StateTransitionSpec.clientResult_bind,
          StateTransitionSpec.clientState_bind]
        dsimp only [a₁, s₁] at hc₁ hc₂ hmul
        omega
    · have hbw := boundedWhile_of_not guard body d (fuel + 1) a hg
      refine ⟨by simp [whileSafe, hg], ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbw]; exact validHistory_pure w _ _
      · rw [hbw, StateTransitionSpec.clientResult_pure]; exact hg
      · rw [hbw, StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure]
        exact hi
      · rw [hbw, StateTransitionSpec.clientState_pure]; exact Memory.Modifies.refl S s
      · rw [hbw, StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure,
          memoryCost_pure]
        omega

/-- Rank-bounded loop invariant induction for `boundedWhile` with worst-case cost `B` per
iteration and `Memory.Modifies` framing. -/
theorem boundedWhile_spec {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    (w : ℕ) (d : δ) (B : ℕ)
    (I : σ → Memory.State → Prop) (rank : σ → Memory.State → ℕ) (S : Set ℕ)
    (hzero : ∀ a s, I a s → rank a s = 0 → ¬guard d a)
    (hstep : ∀ a s, I a s → guard d a →
      safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      memoryCost (body (d, a)) s ≤ B ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      Memory.Modifies S s s' ∧
      I a' s' ∧
      rank a' s' < rank a s) :
    ∀ (fuel : ℕ) (a : σ) (s : Memory.State), I a s → rank a s ≤ fuel →
      let prog := boundedWhile guard body d fuel a
      let a' := (Memory.spec 0).clientResult s prog
      let s' := (Memory.spec 0).clientState s prog
      whileSafe guard body safe w d fuel a s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
      ¬guard d a' ∧
      I a' s' ∧
      Memory.Modifies S s s' ∧
      memoryCost prog s ≤ B * rank a s := by
  intro fuel a s hi hr
  have h := boundedWhile_potential_spec guard body safe w d B I rank (fun _ _ => 0) S
    hzero (fun a s hi hg => by
      obtain ⟨hs, hv, hc, hm, hi', hr'⟩ := hstep a s hi hg
      exact ⟨hs, hv, by omega, hm, hi', hr'⟩) fuel a s hi hr
  simpa only [Nat.add_zero, Nat.zero_add] using h

end Cslib.WordRAM.Realization
