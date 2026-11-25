/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Internal subroutines, realization, frames, and distance relation for Edmonds–Karp

Cross-submodule internal subroutines (`capAddr`, `flowAddr`, `predAddr`, `readResCap`,
`bfsInnerStep`..`cutOuterStep`), exact-basis realization proofs, state-preservation lemmas, and
the `DistRel` distance invariant for `Cslib.Algorithms.WordRAM.EdmondsKarp`. Imported privately
by `Bounds`, `BfsSemantics`, `Spec`, and `UniformBipartite` so none of these helpers enter
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp`'s public API.
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp.Internal

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.EdmondsKarp
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write

/-! ### Internal addresses and subroutines -/

/-- Address of the capacity `W u v`. -/
abbrev capAddr (c : Ctx) (u v : ℕ) : ℕ := c.matBase + u * c.n + v

/-- Address of the flow on the arc `(u, v)`. -/
abbrev flowAddr (c : Ctx) (u v : ℕ) : ℕ := c.scratchBase + u * c.n + v

/-- Address of the breadth-first-search parent of `x`. -/
abbrev predAddr (c : Ctx) (x : ℕ) : ℕ := c.scratchBase + c.n * c.n + c.n + x

/-- `omega` after unfolding the layout abbreviations and reducing projections. -/
local macro "ek_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr, Prod.fst, Prod.snd] at *
  omega))

/-- Close the arithmetic side goals of `realize` for the solver's programs. -/
local macro "ek_side" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr, Prod.fst, Prod.snd] at *
  first
  | assumption
  | (constructor <;> first | assumption | (constructor <;> assumption))
  | omega
  | (apply Fits.of_le ‹Fits _ (_ + (_ * _ + 2 * _))›; first | omega | nlinarith)
  | (apply Fits.of_le ‹Fits _ (_ * _ * _ + _ * _ * _ + 3 * _ + 1)›; first | omega | nlinarith)))

/-- Residual capacity `W u v - f u v + f v u` of the arc `(u, v)` (`d = ((c, u), v)`), guarded to
be at most `2 * B`. -/
@[expose] def readResCap (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let ((c, u), v) := d
  let cap ← Memory.read (capAddr c u v)
  let fuv ← Memory.read (flowAddr c u v)
  let fvu ← Memory.read (flowAddr c v u)
  if cap ≤ c.capBound ∧ fuv ≤ cap ∧ fvu ≤ c.capBound then pure (cap - fuv + fvu) else pure 0

/-- Innermost step of the search (`d = (((c, layer), u), v)`): reach `v` from `u` at distance
`layer + 1` when `v` is unreached and `(u, v)` has residual capacity. -/
@[expose] def bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let (((c, layer), u), v) := d
  let dv ← Memory.read (distAddr c v)
  let rc ← readResCap ((c, u), v)
  if dv = c.n ∧ 0 < rc then
    Memory.write (distAddr c v) (layer + 1)
    Memory.write (predAddr c v) u
    pure (v + 1)
  else
    pure (v + 1)

/-- Middle step of the search (`d = ((c, layer), u)`): expand `u` if it lies in layer `layer`. -/
@[expose] def bfsMidStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let ((c, layer), u) := d
  let du ← Memory.read (distAddr c u)
  if du = layer then
    let _ ← iterate bfsInnerStep ((c, layer), u) c.n 0
    pure (u + 1)
  else
    pure (u + 1)

/-- One layer of the search (`d = (c, layer)`). -/
@[expose] def bfsLayerStep (d : Ctx × ℕ) : Memory.Prog ℕ := do
  let (c, layer) := d
  let _ ← Memory.read 0
  let _ ← iterate bfsMidStep (c, layer) c.n 0
  pure (layer + 1)

/-- Layered breadth-first search from `s` (`d = (c, s)`) on the residual graph of the stored
flow. -/
@[expose] def bfsProg (d : Ctx × ℕ) : Memory.Prog Unit := do
  let (c, s) := d
  fillRange ((distAddr c 0, c.n), c.n)
  Memory.write (distAddr c s) 0
  Memory.write (predAddr c s) s
  let _ ← iterate bfsLayerStep c (c.n - 1) 0
  pure ()

/-- One step of the bottleneck walk (`d = (c, (cur, δ))`): move to the parent `p` of `cur` and
take the minimum of `δ` and the residual capacity of `(p, cur)`. -/
@[expose] def bnStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let (c, (cur, δ)) := d
  let _ ← Memory.read 0
  if cur < c.n then
    let p ← Memory.read (predAddr c cur)
    if p < c.n then
      let rc ← readResCap ((c, p), cur)
      if rc ≤ δ then pure (p, rc) else pure (p, δ)
    else pure (0, δ)
  else pure (0, δ)

/-- One step of the augmentation walk (`d = ((c, δ), cur)`): push `δ` units along the arc
`(p, cur)` from the parent `p` of `cur`, cancelling flow on `(cur, p)` first. -/
@[expose] def augStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let ((c, δ), cur) := d
  let _ ← Memory.read 0
  if cur < c.n then
    let p ← Memory.read (predAddr c cur)
    if p < c.n then
      let fcp ← Memory.read (flowAddr c cur p)
      let fpc ← Memory.read (flowAddr c p cur)
      if fpc ≤ c.capBound ∧ δ ≤ 2 * c.capBound then
        let r := if δ ≤ fcp then δ else fcp
        Memory.write (flowAddr c cur p) (fcp - r)
        Memory.write (flowAddr c p cur) (fpc + (δ - r))
        pure p
      else pure p
    else pure 0
  else pure 0

/-- One round (`d = ((c, (s, t)), flag)`, `flag = 0` while running): search, and if `t` is reached,
compute the bottleneck of the found path and push it. Returns `1` once `t` is not reached. -/
@[expose] def roundStep (d : (Ctx × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let ((c, (s, t)), flag) := d
  let _ ← Memory.read 0
  if flag = 0 then
    bfsProg (c, s)
    let dt ← Memory.read (distAddr c t)
    if 0 < dt ∧ dt < c.n then
      let r ← iterate bnStep c dt (t, 2 * c.capBound)
      let _ ← iterate augStep (c, r.2) dt t
      pure 0
    else pure 1
  else pure 1

/-- Inner step of the cut sum (`d = ((c, u), (v, acc))`): add `W u v` when `v` is unreached. -/
@[expose] def cutInnerStep (d : (Ctx × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let ((c, u), (v, acc)) := d
  let dv ← Memory.read (distAddr c v)
  let x ← Memory.read (capAddr c u v)
  if dv = c.n ∧ x ≤ c.capBound ∧ acc ≤ c.n * c.n * c.capBound then
    pure (v + 1, acc + x)
  else
    pure (v + 1, acc)

/-- Outer step of the cut sum (`d = (c, (u, acc))`): add the capacities from `u` to the unreached
vertices when `u` is reached. -/
@[expose] def cutOuterStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let (c, (u, acc)) := d
  let du ← Memory.read (distAddr c u)
  if du < c.n then
    let r ← iterate cutInnerStep (c, u) c.n (0, acc)
    pure (u + 1, r.2)
  else
    pure (u + 1, acc)

/-! ### Client result equations -/

theorem clientResult_bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsInnerStep d) = d.2 + 1 := by
  unfold bfsInnerStep
  rw [clientResult_bind_read, clientResult_bind]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

theorem clientResult_bfsMidStep (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsMidStep d) = d.2 + 1 := by
  unfold bfsMidStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

theorem clientResult_cutInnerStep_fst (cu : Ctx × ℕ) (va : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (cutInnerStep (cu, va))).1 = va.1 + 1 := by
  unfold cutInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> rfl

theorem clientResult_cutOuterStep_fst (c : Ctx) (ua : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (cutOuterStep (c, ua))).1 = ua.1 + 1 := by
  unfold cutOuterStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

/-! ### Realization (`Realizes`) for internal subroutines -/

private theorem readResCap_realizes :
    Realizes .exact readResCap (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.n ∧ d.2 < d.1.1.n) (fun _ _ => 0) := by
  unfold readResCap
  realize
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu, hv⟩ := h
    have h1 := List.mul_add_lt_sq hu hv
    have h2 := List.mul_add_lt_sq hv hu
    rcases d with ⟨⟨c, u⟩, v⟩
    ek_side

private theorem bfsInnerStep_realizes :
    Realizes .exact bfsInnerStep (WordEncoding.encode (α := ((Ctx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1.1 ∧ d.1.1.2 < d.1.1.1.n ∧ d.1.2 < d.1.1.1.n ∧
        d.2 < d.1.1.1.n) (fun _ _ => 0) := by
  unfold bfsInnerStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl, hu, hv⟩ := h
    ek_side

private theorem bfsMidStep_realizes :
    Realizes .exact bfsMidStep (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.n ∧ d.2 < d.1.1.n) (fun _ _ => 0) := by
  unfold bfsMidStep
  realize [bfsInnerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl, hu⟩ := h
    try ek_side
  exact iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1.1.n)
    (fun _ _ _ _ => ⟨⟨⟨hlay, hws, hwb⟩, hl, hu, by dsimp only at *; omega⟩, by
      dsimp only at *
      rw [clientResult_bfsInnerStep]; omega⟩) (Nat.zero_add _)

private theorem bfsLayerStep_realizes :
    Realizes .exact bfsLayerStep (WordEncoding.encode (α := Ctx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1 ∧ d.2 < d.1.n) (fun _ _ => 0) := by
  unfold bfsLayerStep
  realize [bfsMidStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl⟩ := h
    try ek_side
  exact iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1.n)
    (fun _ _ _ _ => ⟨⟨⟨hlay, hws, hwb⟩, hl, by dsimp only at *; omega⟩, by
      dsimp only at *
      rw [clientResult_bfsMidStep]; omega⟩) (Nat.zero_add _)

private theorem bfsProg_realizes :
    Realizes .exact bfsProg (WordEncoding.encode (α := Ctx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => CtxFits w d.1 ∧ d.2 < d.1.n) (fun _ _ => 0) := by
  unfold bfsProg
  realize [fillRange_realizes, bfsLayerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs⟩ := h
    try ek_side
  exact iterationSafe_of_stepInv _ _ w _ (fun rem (layer : ℕ) _ => layer + rem = d.1.n - 1)
    (fun _ _ _ _ => ⟨⟨⟨hlay, hws, hwb⟩, by dsimp only at *; omega⟩, by
      dsimp only [bfsLayerStep] at *
      simp only [client_simps]; omega⟩) (Nat.zero_add _)

private theorem bnStep_realizes :
    Realizes .exact bnStep (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => CtxFits w d.1) (fun _ _ => 0) := by
  unfold bnStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨hlay, hws, hwb⟩ := h
    ek_side

private theorem augStep_realizes :
    Realizes .exact augStep (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1) (fun _ _ => 0) := by
  unfold augStep
  realize
  all_goals
    obtain ⟨hlay, hws, hwb⟩ := h
    rcases d with ⟨⟨c, δ⟩, cur⟩
    ek_side

theorem roundStep_realizes :
    Realizes .exact roundStep (WordEncoding.encode (α := (Ctx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => let ((c, (s, t)), _) := d; CtxFits w c ∧ s < c.n ∧ t < c.n)
      (fun _ _ => 0) := by
  unfold roundStep
  realize [bfsProg_realizes, bnStep_realizes, augStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs, ht⟩ := h
    rcases d with ⟨⟨c, ⟨s, t⟩⟩, flag⟩
    try ek_side
  all_goals
    exact iterationSafe_of_stepInv _ _ w _ (fun _ _ _ => True)
      (fun _ _ _ _ => ⟨⟨hlay, hws, hwb⟩, trivial⟩) trivial

private theorem cutInnerStep_realizes :
    Realizes .exact cutInnerStep (WordEncoding.encode (α := (Ctx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.n ∧ d.2.1 < d.1.1.n) (fun _ _ => 0) := by
  unfold cutInnerStep
  realize
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu, hv⟩ := h
    have h1 := List.mul_add_lt_sq hu hv
    ek_side

theorem cutOuterStep_realizes :
    Realizes .exact cutOuterStep (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => let (c, (u, _)) := d; CtxFits w c ∧ u < c.n) (fun _ _ => 0) := by
  unfold cutOuterStep
  realize [cutInnerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu⟩ := h
    try ek_side
  exact iterationSafe_of_stepInv _ _ w _ (fun rem (va : ℕ × ℕ) _ => va.1 + rem = d.1.n)
    (fun _ _ _ _ => ⟨⟨⟨hlay, hws, hwb⟩, hu, by dsimp only at *; omega⟩, by
      dsimp only at *
      rw [clientResult_cutInnerStep_fst]; omega⟩) (Nat.zero_add _)

/-! ### State preservation and distance-monotonicity relation -/

theorem readResCap_state (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readResCap d) = s := by
  unfold readResCap
  rw [clientState_bind_read, clientState_bind_read, clientState_bind_read]
  split_ifs <;> rfl

theorem bnStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bnStep d) = s := by
  unfold bnStep
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind_read]
    split_ifs
    · rw [clientState_bind, readResCap_state]; split_ifs <;> rfl
    · rfl
  · rfl

theorem cutInnerStep_state (d : (Ctx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutInnerStep d) = s := by
  unfold cutInnerStep
  rw [clientState_bind_read, clientState_bind_read]
  split_ifs <;> rfl

theorem cutOuterStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutOuterStep d) = s := by
  unfold cutOuterStep
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind, clientState_iterate_eq_of _ _ (fun _ t => cutInnerStep_state _ t)]; rfl
  · rfl

theorem preservesAt_bfsProg {a : ℕ} {d : Ctx × ℕ} (hs : d.2 < d.1.n)
    (ha : a < distAddr d.1 0 ∨ predAddr d.1 d.1.n ≤ a) : PreservesAt a (bfsProg d) := by
  obtain ⟨c, src⟩ := d
  dsimp only at hs ha
  refine preservesAt_bind (fun s => (fillRange_spec _ _ _ s).2 _ (by ek_omega)) fun _ =>
    preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ =>
    preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ =>
    preservesAt_bind (preservesAt_iterate (fun _ => ?_) _ _) fun _ => preservesAt_pure _ _
  refine preservesAt_bind (preservesAt_read _ _) fun _ =>
    preservesAt_bind (preservesAt_iterate_nat fun _ _ => ⟨?_, fun _ => clientResult_bfsMidStep _ _⟩)
      fun _ => preservesAt_pure _ _
  refine preservesAt_bind (preservesAt_read _ _) fun _ =>
    preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind
    (preservesAt_iterate_nat fun _ _ => ⟨?_, fun _ => clientResult_bfsInnerStep _ _⟩)
    fun _ => preservesAt_pure _ _
  refine preservesAt_bind (preservesAt_read _ _) fun _ =>
    preservesAt_bind (fun t => congrArg (fun st => st.mem a) (readResCap_state _ t)) fun _ =>
    preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ =>
    preservesAt_map _ (preservesAt_write _ (by ek_omega))

/-- Between `t` and `t'`, every distance below `n` either is unchanged or went from `n` (unreached)
to `layer + 1`. -/
@[expose] def DistRel (c : Ctx) (layer : ℕ) (t t' : Memory.State) : Prop :=
  ∀ x < c.n, t'.mem (distAddr c x) = t.mem (distAddr c x) ∨
    (t.mem (distAddr c x) = c.n ∧ t'.mem (distAddr c x) = layer + 1)

theorem DistRel.refl (c : Ctx) (layer : ℕ) (t : Memory.State) : DistRel c layer t t :=
  fun _ _ => Or.inl rfl

theorem DistRel.trans {c : Ctx} {layer : ℕ}
    {t₁ t₂ t₃ : Memory.State} (h₁ : DistRel c layer t₁ t₂) (h₂ : DistRel c layer t₂ t₃) :
    DistRel c layer t₁ t₃ := fun x hx => by
  rcases h₁ x hx with h | ⟨ha, hb⟩ <;> rcases h₂ x hx with h' | ⟨ha', hb'⟩
  · exact Or.inl (h'.trans h)
  · exact Or.inr ⟨h ▸ ha', hb'⟩
  · exact Or.inr ⟨ha, h'.trans hb⟩
  · omega

private theorem bfsInnerStep_rel (d : ((Ctx × ℕ) × ℕ) × ℕ) (t : Memory.State) :
    DistRel d.1.1.1 d.1.1.2 t ((Memory.spec 0).clientState t (bfsInnerStep d)) := by
  rcases d with ⟨⟨⟨c, layer⟩, u⟩, v⟩
  intro x hx
  unfold bfsInnerStep
  dsimp only
  rw [clientState_bind_read, clientState_bind, readResCap_state]
  split_ifs with hc
  · rw [clientState_bind_write, clientState_bind_write, clientState_pure]
    dsimp only
    rw [Function.update_of_ne (by ek_omega)]
    by_cases hxv : x = v
    · subst hxv
      exact Or.inr ⟨hc.1, Function.update_self _ _ _⟩
    · exact Or.inl (Function.update_of_ne (by ek_omega) _ _)
  · exact Or.inl rfl

private theorem bfsInner_iterate_rel (c : Ctx) (layer u : ℕ)
    (m v₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsInnerStep ((c, layer), u) m v₀)) :=
  iterate_invariant_of bfsInnerStep ((c, layer), u) (fun _ _ t' => DistRel c layer t t')
    (fun _ v t' h => h.trans (bfsInnerStep_rel (((c, layer), u), v) t'))
    (DistRel.refl c layer t)

theorem bfsMidStep_rel (c : Ctx) (layer u : ℕ)
    (t : Memory.State) :
    DistRel c layer t ((Memory.spec 0).clientState t (bfsMidStep ((c, layer), u))) := by
  unfold bfsMidStep
  dsimp only
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind, clientState_pure]
    exact bfsInner_iterate_rel c layer u _ _ t
  · exact DistRel.refl c layer t

theorem bfsMid_iterate_rel (c : Ctx) (layer : ℕ)
    (m u₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsMidStep (c, layer) m u₀)) :=
  iterate_invariant_of bfsMidStep (c, layer) (fun _ _ t' => DistRel c layer t t')
    (fun _ u t' h => h.trans (bfsMidStep_rel c layer u t'))
    (DistRel.refl c layer t)

end Cslib.Algorithms.WordRAM.EdmondsKarp.Internal
