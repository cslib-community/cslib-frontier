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
public import Mathlib.Data.Rat.Defs
import CslibFrontier.Computability.WordRAM.Realization.Backend
import Mathlib.Data.Rat.Cast.Order

/-!
# Loop framing, amortized potential inductions, and triple bridges for realization

This module connects `Memory.Triple` and `Memory.FramedTriple` to the `Realization` interpreter
(`memoryCost`, `clientResult`, `clientState`, `ValidHistory`), supplies the missing `Memory.alloc` /
`Memory.allocDirty` step lemmas, and provides single-pass invariant and amortized-potential loop
inductions (`ℕ` and abstract-witness `ℚ` potential) for both `iterate` and `boundedWhile` with
explicit `Memory.Modifies` framing.

## Main results

* `runClient_alloc`, `clientResult_alloc`, `clientState_alloc`, `validHistory_alloc_bind`,
  `clientResult_bind_alloc`, `clientState_bind_alloc`, `clientResult_bind_allocDirty`,
  `clientState_bind_allocDirty`: primitive allocation step reductions.
* `triple_iff_realization`, `framedTriple_iff_realization`: equivalence between memory triples
  and `Realization` judgments.
* `iterate_rat_witness_spec`, `iterate_potential_spec`: witness-indexed `ℚ` and amortized `ℕ`
  potential inductions for `iterate` with `Memory.Modifies` framing.
* `boundedWhile_rat_witness_spec`, `boundedWhile_potential_spec`, `boundedWhile_spec`:
  witness-indexed `ℚ`, amortized `ℕ`, and rank-bounded worst-case inductions for `boundedWhile`.
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

/-! ## Witness-indexed rational potential loop inductions -/

private theorem rat_potential_step_add {a b : ℕ} {q₀ q₁ q₂ B R : ℚ}
    (h₁ : (a : ℚ) + q₁ ≤ q₀ + B) (h₂ : (b : ℚ) + q₂ ≤ q₁ + R) :
    ((a + b : ℕ) : ℚ) + q₂ ≤ q₀ + (B + R) := by
  calc
    ((a + b : ℕ) : ℚ) + q₂ = (a : ℚ) + ((b : ℚ) + q₂) := by rw [Nat.cast_add, add_assoc]
    _ ≤ (a : ℚ) + (q₁ + R) := add_le_add le_rfl h₂
    _ = ((a : ℚ) + q₁) + R := (add_assoc _ _ _).symm
    _ ≤ (q₀ + B) + R := add_le_add h₁ le_rfl
    _ = q₀ + (B + R) := add_assoc _ _ _

private theorem iterate_witness_spec_core {δ σ : Type} {W M : Type*} [Add M] [LE M]
    (castCost : ℕ → M) (stepCredit : M) (budget : ℕ → M)
    (hbase : ∀ p : M, castCost 0 + p ≤ p + budget 0)
    (hcomb : ∀ (a b n : ℕ) (q₀ q₁ q₂ : M),
      castCost a + q₁ ≤ q₀ + stepCredit →
      castCost b + q₂ ≤ q₁ + budget n →
      castCost (a + b) + q₂ ≤ q₀ + budget (n + 1))
    (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → δ × σ → Memory.State → Prop) (w : ℕ) (d : δ) (n : ℕ)
    (inv : ℕ → W → σ → Memory.State → Prop) (pot : ℕ → W → M) (S : Set ℕ)
    (hstep : ∀ k < n, ∀ wt a s, inv k wt a s →
      safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      ∃ wt' : W,
        inv (k + 1) wt' a' s' ∧
        castCost (memoryCost (body (d, a)) s) + pot (k + 1) wt' ≤ pot k wt + stepCredit ∧
        Memory.Modifies S s s')
    (wt₀ : W) (a₀ : σ) (s₀ : Memory.State) (h₀ : inv 0 wt₀ a₀ s₀) :
    let prog := iterate body d n a₀
    let a' := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe body safe w d n a₀ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    Memory.Modifies S s₀ s' ∧
    ∃ wt' : W, inv n wt' a' s' ∧
      castCost (memoryCost prog s₀) + pot n wt' ≤ pot 0 wt₀ + budget n := by
  induction n generalizing inv pot wt₀ a₀ s₀ with
  | zero =>
    refine ⟨trivial, trivial, Memory.Modifies.refl S s₀, wt₀, h₀, ?_⟩
    change castCost (memoryCost (Pure.pure a₀) s₀) + pot 0 wt₀ ≤ pot 0 wt₀ + budget 0
    rw [memoryCost_pure]
    exact hbase (pot 0 wt₀)
  | succ n ih =>
    obtain ⟨hs₀, hv₀, wt₁, hinv₁, hpot₀, hr₀⟩ := hstep 0 (Nat.succ_pos n) wt₀ a₀ s₀ h₀
    set a₁ := (Memory.spec 0).clientResult s₀ (body (d, a₀))
    set s₁ := (Memory.spec 0).clientState s₀ (body (d, a₀))
    obtain ⟨hsn, hvn, hrn, wt', hinvn, hpotn⟩ :=
      ih (fun k => inv (k + 1)) (fun k => pot (k + 1))
        (fun k hk => hstep (k + 1) (Nat.succ_lt_succ hk)) wt₁ a₁ s₁ hinv₁
    refine ⟨⟨hs₀, by rw [clientResult_width, clientState_width]; exact hsn⟩, ?_, ?_, wt', ?_, ?_⟩
    · rw [iterate, validHistory_bind']; exact ⟨hv₀, hvn⟩
    · rw [iterate, StateTransitionSpec.clientState_bind]; exact Memory.Modifies.trans hr₀ hrn
    · rw [iterate, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      exact hinvn
    · rw [iterate, memoryCost_bind']
      dsimp only [a₁, s₁] at hpot₀ hpotn
      exact hcomb _ _ n _ _ _ hpot₀ hpotn

private theorem boundedWhile_witness_spec_core {δ σ : Type} {W M : Type*} [Add M] [LE M]
    (castCost : ℕ → M) (stepCredit : M) (budget : ℕ → M)
    (hbase : ∀ (r : ℕ) (p : M), castCost 0 + p ≤ p + budget r)
    (hcomb : ∀ (a b r r' : ℕ) (q₀ q₁ q₂ : M), r' < r →
      castCost a + q₁ ≤ q₀ + stepCredit →
      castCost b + q₂ ≤ q₁ + budget r' →
      castCost (a + b) + q₂ ≤ q₀ + budget r)
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    (w : ℕ) (d : δ)
    (I : W → σ → Memory.State → Prop) (rank : W → ℕ) (pot : W → M) (S : Set ℕ)
    (hzero : ∀ wt a s, I wt a s → rank wt = 0 → ¬guard d a)
    (hstep : ∀ wt a s, I wt a s → guard d a →
      safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      ∃ wt' : W,
        I wt' a' s' ∧
        castCost (memoryCost (body (d, a)) s) + pot wt' ≤ pot wt + stepCredit ∧
        Memory.Modifies S s s' ∧
        rank wt' < rank wt) :
    ∀ (fuel : ℕ) (wt : W) (a : σ) (s : Memory.State), I wt a s → rank wt ≤ fuel →
      let prog := boundedWhile guard body d fuel a
      let a' := (Memory.spec 0).clientResult s prog
      let s' := (Memory.spec 0).clientState s prog
      whileSafe guard body safe w d fuel a s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
      ¬guard d a' ∧
      Memory.Modifies S s s' ∧
      ∃ wt' : W, I wt' a' s' ∧
        castCost (memoryCost prog s) + pot wt' ≤ pot wt + budget (rank wt) := by
  intro fuel
  induction fuel with
  | zero =>
    intro wt a s hi hr
    have hg : ¬guard d a := hzero wt a s hi (Nat.eq_zero_of_le_zero hr)
    refine ⟨hg, trivial, hg, Memory.Modifies.refl S s, wt, hi, ?_⟩
    dsimp only [boundedWhile]
    rw [memoryCost_pure]
    exact hbase (rank wt) (pot wt)
  | succ fuel ih =>
    intro wt a s hi hr
    cases (inferInstance : Decidable (guard d a)) with
    | isTrue hg =>
      obtain ⟨hs, hv₁, wt₁, hi₁, hpot₀, hr₁, hrank₁⟩ := hstep wt a s hi hg
      set a₁ := (Memory.spec 0).clientResult s (body (d, a))
      set s₁ := (Memory.spec 0).clientState s (body (d, a))
      obtain ⟨hs₂, hv₂, hstop, hr₂, wt', hi', hpot₂⟩ := ih wt₁ a₁ s₁ hi₁ (by omega)
      have hbw : boundedWhile guard body d (fuel + 1) a =
          (body (d, a) >>= boundedWhile guard body d fuel) := by
        simp [boundedWhile, hg, ← PFunctor.FreeM.bind_eq_bind]
      refine ⟨?_, ?_, ?_, ?_, wt', ?_, ?_⟩
      · simp only [whileSafe, hg, ↓reduceIte]
        exact ⟨hs, hs₂⟩
      · rw [hbw]
        exact validHistory_bind_step hv₁ hv₂
      · rw [hbw, StateTransitionSpec.clientResult_bind]
        exact hstop
      · rw [hbw, StateTransitionSpec.clientState_bind]
        exact Memory.Modifies.trans hr₁ hr₂
      · rw [hbw, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
        exact hi'
      · rw [hbw, memoryCost_bind']
        dsimp only [a₁, s₁] at hpot₀ hpot₂
        exact hcomb _ _ _ _ _ _ _ hrank₁ hpot₀ hpot₂
    | isFalse hg =>
      have hbw := boundedWhile_of_not guard body d (fuel + 1) a hg
      refine ⟨by simp [whileSafe, hg], ?_, ?_, ?_, wt, ?_, ?_⟩
      · rw [hbw]; exact validHistory_pure w _ _
      · rw [hbw, StateTransitionSpec.clientResult_pure]; exact hg
      · rw [hbw, StateTransitionSpec.clientState_pure]; exact Memory.Modifies.refl S s
      · rw [hbw, StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure]
        exact hi
      · rw [hbw, memoryCost_pure]
        exact hbase (rank wt) (pot wt)

/-- Amortized rational potential-method induction for `iterate` parameterized by an abstract
witness type `W`, rational step credit `B : ℚ`, and `Memory.Modifies` framing. -/
theorem iterate_rat_witness_spec {δ σ : Type} {W : Type*}
    (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → δ × σ → Memory.State → Prop) (w : ℕ) (d : δ) (B : ℚ) (n : ℕ)
    (inv : ℕ → W → σ → Memory.State → Prop) (pot : ℕ → W → ℚ) (S : Set ℕ)
    (hstep : ∀ k < n, ∀ wt a s, inv k wt a s →
      safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      ∃ wt' : W,
        inv (k + 1) wt' a' s' ∧
        (memoryCost (body (d, a)) s : ℚ) + pot (k + 1) wt' ≤ pot k wt + B ∧
        Memory.Modifies S s s')
    (wt₀ : W) (a₀ : σ) (s₀ : Memory.State) (h₀ : inv 0 wt₀ a₀ s₀) :
    let prog := iterate body d n a₀
    let a' := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe body safe w d n a₀ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    Memory.Modifies S s₀ s' ∧
    ∃ wt' : W, inv n wt' a' s' ∧ (memoryCost prog s₀ : ℚ) + pot n wt' ≤ pot 0 wt₀ + B * n :=
  iterate_witness_spec_core (M := ℚ) (fun k => (k : ℚ)) B (fun k => B * k)
    (fun _ => by simp)
    (fun _ _ m _ _ _ h₁ h₂ => by
      rw [Nat.cast_succ, mul_add, mul_one, add_comm (B * (m : ℚ)) B]
      exact rat_potential_step_add h₁ h₂)
    body safe w d n inv pot S hstep wt₀ a₀ s₀ h₀

/-- Amortized rational potential-method induction for `boundedWhile` parameterized by an abstract
witness type `W`, nonnegative step credit `B : ℚ`, rank `rank : W → ℕ`, and `Memory.Modifies`
framing. -/
theorem boundedWhile_rat_witness_spec {δ σ : Type} {W : Type*}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    (w : ℕ) (d : δ) (B : ℚ) (hB : 0 ≤ B)
    (I : W → σ → Memory.State → Prop) (rank : W → ℕ) (pot : W → ℚ) (S : Set ℕ)
    (hzero : ∀ wt a s, I wt a s → rank wt = 0 → ¬guard d a)
    (hstep : ∀ wt a s, I wt a s → guard d a →
      safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      let a' := (Memory.spec 0).clientResult s (body (d, a))
      let s' := (Memory.spec 0).clientState s (body (d, a))
      ∃ wt' : W,
        I wt' a' s' ∧
        (memoryCost (body (d, a)) s : ℚ) + pot wt' ≤ pot wt + B ∧
        Memory.Modifies S s s' ∧
        rank wt' < rank wt) :
    ∀ (fuel : ℕ) (wt : W) (a : σ) (s : Memory.State), I wt a s → rank wt ≤ fuel →
      let prog := boundedWhile guard body d fuel a
      let a' := (Memory.spec 0).clientResult s prog
      let s' := (Memory.spec 0).clientState s prog
      whileSafe guard body safe w d fuel a s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
      ¬guard d a' ∧
      Memory.Modifies S s s' ∧
      ∃ wt' : W, I wt' a' s' ∧
        (memoryCost prog s : ℚ) + pot wt' ≤ pot wt + B * rank wt :=
  boundedWhile_witness_spec_core (M := ℚ) (fun k => (k : ℚ)) B (fun r => B * r)
    (fun r _ => by
      rw [Nat.cast_zero, zero_add]
      exact le_add_of_nonneg_right (mul_nonneg hB (Nat.cast_nonneg r)))
    (fun _ _ r r' _ _ _ hrank h₁ h₂ => by
      have hrank_q : (r' : ℚ) + 1 ≤ (r : ℚ) := by
        have hle := (Nat.cast_le (α := ℚ)).mpr hrank
        rwa [Nat.cast_succ] at hle
      have hmul : B + B * (r' : ℚ) ≤ B * (r : ℚ) :=
        calc
          B + B * (r' : ℚ) = B * ((r' : ℚ) + 1) := by rw [mul_add, mul_one, add_comm]
          _ ≤ B * (r : ℚ) := mul_le_mul_of_nonneg_left hrank_q hB
      exact (rat_potential_step_add h₁ h₂).trans (add_le_add le_rfl hmul))
    guard body safe w d I rank pot S hzero hstep

/-! ## Single-pass `iterate` and `boundedWhile` `ℕ`-potential inductions -/

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
  obtain ⟨hsafe, hv, hmod, wt', ⟨hwt', hinv⟩, hle⟩ :=
    iterate_witness_spec_core (W := σ × Memory.State) (M := ℕ)
      (fun k => k) B (fun k => B * k)
      (fun _ => by omega)
      (fun _ _ _ _ _ _ h₁ h₂ => by rw [Nat.mul_succ]; omega)
      body safe w d n (fun k wt a s => wt = (a, s) ∧ inv k a s)
      (fun k wt => pot k wt.1 wt.2) S
      (fun k hk wt a s ⟨hwt, hi⟩ => by
        subst hwt
        obtain ⟨hs, hv, hc, hm, hi'⟩ := hstep k hk a s hi
        exact ⟨hs, hv, ((Memory.spec 0).clientResult s (body (d, a)),
          (Memory.spec 0).clientState s (body (d, a))), ⟨rfl, hi'⟩, hc, hm⟩)
      (a₀, s₀) a₀ s₀ ⟨rfl, h₀⟩
  subst hwt'
  exact ⟨hsafe, hv, hle, hmod, hinv⟩

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
  intro fuel a s hi hr
  obtain ⟨hsafe, hv, hstop, hmod, wt', ⟨hwt', hi'⟩, hle⟩ :=
    boundedWhile_witness_spec_core (W := σ × Memory.State) (M := ℕ)
      (fun k => k) B (fun r => B * r)
      (fun _ _ => by omega)
      (fun _ _ r r' _ _ _ hrank h₁ h₂ => by
        have hmul : B * (r' + 1) ≤ B * r := Nat.mul_le_mul_left B hrank
        rw [Nat.mul_succ] at hmul
        omega)
      guard body safe w d (fun wt a s => wt = (a, s) ∧ I a s)
      (fun wt => rank wt.1 wt.2) (fun wt => pot wt.1 wt.2) S
      (fun wt a s ⟨hwt, hI⟩ hrank => by subst hwt; exact hzero a s hI hrank)
      (fun wt a s ⟨hwt, hI⟩ hg => by
        subst hwt
        obtain ⟨hs, hv, hc, hm, hI', hrank'⟩ := hstep a s hI hg
        exact ⟨hs, hv, ((Memory.spec 0).clientResult s (body (d, a)),
          (Memory.spec 0).clientState s (body (d, a))), ⟨rfl, hI'⟩, hc, hm, hrank'⟩)
      fuel (a, s) a s ⟨rfl, hi⟩ hr
  subst hwt'
  exact ⟨hsafe, hv, hstop, hi', hmod, hle⟩

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

