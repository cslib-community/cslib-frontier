/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Realize

/-!
# Word-Block Copy (`copyWords`) and Inequality Filter (`filterNe`)

Realizable Word-RAM primitives copying a word range (`copyWords`) and filtering out occurrences of a
single variable from an array (`filterNe`).

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.copyWords`: contiguous block copy.
* `Cslib.Algorithms.WordRAM.VariableElimination.filterNe`: append-only filter keeping words `≠ key`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Primitive 2: Block copy (`copyWords`) and inequality filter (`filterNe`) -/

/-- Arguments `(src, dst, len)` for `copyWords`. -/
structure CopyArgs where
  /-- Field `src` of `CopyArgs`. -/
  src : ℕ
  /-- Field `dst` of `CopyArgs`. -/
  dst : ℕ
  /-- Field `len` of `CopyArgs`. -/
  len : ℕ

/-- Product equivalence encoding `CopyArgs` as words. -/
@[expose] def CopyArgs.equiv : CopyArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.src, a.dst), a.len)
  invFun := fun ((src, dst), len) => ⟨src, dst, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding CopyArgs := .ofEquiv CopyArgs.equiv

private structure CopyState where
  src : ℕ
  dst : ℕ

private def CopyState.equiv : CopyState ≃ ℕ × ℕ where
  toFun s := (s.src, s.dst)
  invFun := fun (src, dst) => ⟨src, dst⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding CopyState := .ofEquiv CopyState.equiv

private def copyWordsStep (env : Unit × CopyState) : Memory.Prog CopyState := do
  let v ← Memory.read env.2.src
  Memory.write env.2.dst v
  pure ⟨env.2.src + 1, env.2.dst + 1⟩

/-- Copy `len` consecutive words from `src` to `dst`. -/
def copyWords (args : CopyArgs) : Memory.Prog Unit := do
  let _ ← iterate copyWordsStep () args.len ⟨args.src, args.dst⟩
  pure ()

theorem copyWords_cost (args : CopyArgs) (s : Memory.State) :
    memoryCost (copyWords args) s ≤ 2 * args.len := by
  unfold copyWords
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  exact memoryCost_iterate_le_of copyWordsStep 2 () (fun _ _ => le_rfl) args.len
    ⟨args.src, args.dst⟩ s

theorem copyWords_spec {w : ℕ} (args : CopyArgs) {xs : List ℕ} {F : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : Block.HoldsList args.src xs s.mem) (hlen : xs.length = args.len)
    (hsrcF : args.src + args.len ≤ F) (hFdst : F ≤ args.dst)
    (hdst : args.dst + args.len ≤ s.frontier) :
    let s' := (Memory.spec 0).clientState s (copyWords args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyWords args)) ∧
      s'.frontier = s.frontier ∧
      PreservesBelow F s s' ∧
      Block.HoldsList args.dst xs s'.mem := by
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (s := s) (body := copyWordsStep)
    (safe := fun _ _ _ => True) (d := ()) (n := args.len) (a₀ := ⟨args.src, args.dst⟩) (c := 2)
    (S := Set.Ico args.dst (args.dst + args.len))
    (fun k st t => t.frontier = s.frontier ∧ st.src = args.src + k ∧ st.dst = args.dst + k ∧
      ∀ j < k, t.mem (args.dst + j) = s.mem (args.src + j))
    ⟨rfl, rfl, rfl, by simp⟩ (fun k hk ⟨src, dst⟩ t ⟨hfr, hs, hd, hdone⟩ hmod => by
      dsimp only at hs hd; subst hs hd
      have hsrc := hmod.2 (args.src + k) (by omega) (by simp; omega)
      have hval : Fits w (t.mem (args.src + k)) := hsrc ▸ hwf.mem_fits _
      refine ⟨trivial, ?_⟩
      unfold copyWordsStep
      framed_triple
      dsimp only
      refine ⟨hfr, by omega, by omega, Nat.forall_lt_succ_right.2 ⟨fun j hj => ?_, by simp [hsrc]⟩⟩
      simp [hj.ne, hdone j hj]) fun _ t h _ => h
  have hft : Memory.FramedTriple w s (copyWords args) (2 * args.len)
      (Set.Ico args.dst (args.dst + args.len)) fun _ t => t.frontier = s.frontier ∧
        ∀ j < args.len, t.mem (args.dst + j) = s.mem (args.src + j) := by
    unfold copyWords
    exact Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
      fun _ _ h _ => Memory.FramedTriple.pure ⟨h.1, h.2.2.2⟩) (by omega) fun _ _ => id
  obtain ⟨hv, -, hm, hfr, hpost⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, hfr, ⟨by omega, hm.1, fun a ha => hm.2 a (by omega) (by simp; omega)⟩,
    fun ⟨i, hi⟩ => (hpost i (hlen ▸ hi)).trans (hxs ⟨i, hi⟩)⟩

theorem copyWords_realizes :
    Realizes .exact copyWords WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w (args.src + args.len) ∧ Fits w (args.dst + args.len))
      (fun _ _ => 0) := by
  unfold copyWords
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.src + j = d.src + d.len ∧ st.dst + j = d.dst + d.len)
    (fun j st t hinv => ?_) ⟨rfl, rfl⟩
  dsimp only
  refine ⟨⟨h.1.of_le (by omega), h.2.of_le (by omega)⟩, ?_⟩
  change (st.src + 1) + j = d.src + d.len ∧ (st.dst + 1) + j = d.dst + d.len
  omega

private structure FilterState where
  src : ℕ
  dst : ℕ
  count : ℕ

private def FilterState.equiv : FilterState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.src, s.dst), s.count)
  invFun := fun ((src, dst), count) => ⟨src, dst, count⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding FilterState := .ofEquiv FilterState.equiv

private def filterNeStep (env : ℕ × FilterState) : Memory.Prog FilterState := do
  let v ← Memory.read env.2.src
  if v = env.1 then
    pure ⟨env.2.src + 1, env.2.dst, env.2.count⟩
  else
    Memory.write env.2.dst v >>= fun _ =>
      pure ⟨env.2.src + 1, env.2.dst + 1, env.2.count + 1⟩

/-- Copy entries of `[ptr, ptr + len)` distinct from `key` to the frontier. -/
def filterNe (args : MemScanArgs) : Memory.Prog (ℕ × ℕ) := do
  let dst ← Memory.allocDirty args.len
  let res ← iterate filterNeStep args.target args.len ⟨args.base, dst, 0⟩
  pure (dst, res.count)

theorem filterNe_cost (args : MemScanArgs) (s : Memory.State) :
    memoryCost (filterNe args) s ≤ 1 + 2 * args.len := by
  unfold filterNe
  rw [memoryCost_bind', memoryCost_allocDirty, memoryCost_bind', memoryCost_pure, Nat.add_zero]
  refine Nat.add_le_add_left (memoryCost_iterate_le_of filterNeStep 2 args.target (fun a t => ?_)
    args.len ⟨args.base, s.frontier, 0⟩ ⟨s.mem, s.frontier + args.len⟩) 1
  simp only [filterNeStep, memoryCost_bind', memoryCost_read, clientResult_read, memoryCost_ite]
  split_ifs <;> simp [memoryCost_write, memoryCost_pure]

private theorem filterNeStep_eval (target : ℕ) (st : FilterState) (t : Memory.State) :
    (Memory.spec 0).clientResult t (filterNeStep (target, st)) =
      (if t.mem st.src = target then ⟨st.src + 1, st.dst, st.count⟩
      else ⟨st.src + 1, st.dst + 1, st.count + 1⟩) ∧
    (Memory.spec 0).clientState t (filterNeStep (target, st)) =
      if t.mem st.src = target then t
      else ⟨Function.update t.mem st.dst (t.mem st.src), t.frontier⟩ := by
  simp only [filterNeStep]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientResult_read, clientState_read]
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem filterNe_spec {w : ℕ} (args : MemScanArgs) {xs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len)
    (hfit : Fits w (s.frontier + args.len)) :
    let res := (Memory.spec 0).clientResult s (filterNe args)
    let s' := (Memory.spec 0).clientState s (filterNe args)
    let out := xs.filter fun v => decide (v ≠ args.target)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (filterNe args)) ∧
      s'.frontier = s.frontier + args.len ∧
      PreservesBelow s.frontier s s' ∧
      res.1 = s.frontier ∧
      res.2 = out.length ∧
      HoldsIn res.1 out s' := by
  let pre (k : ℕ) := (xs.take k).filter fun v => decide (v ≠ args.target)
  have hb := hxs.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (body := filterNeStep)
    (safe := fun _ _ _ => True) (d := args.target) (n := args.len) (c := 2)
    (s := ⟨s.mem, s.frontier + args.len⟩) (a₀ := ⟨args.base, s.frontier, 0⟩)
    (S := Set.Ici s.frontier)
    (fun k st t => t.frontier = s.frontier + args.len ∧ st.src = args.base + k ∧
      st.dst = s.frontier + st.count ∧ st.count = (pre k).length ∧ (pre k).length ≤ k ∧
      Block.HoldsList s.frontier (pre k) t.mem)
    ⟨rfl, rfl, rfl, by simp [pre], by simp [pre], by simpa [pre] using Block.holdsList_nil _ _⟩
    (fun k hk ⟨src, dst, cnt⟩ t ⟨hfr, hs, hd, hc, hle, hacc⟩ hmod => by
      dsimp only at hs hd hc; subst hs hc; subst hd
      have hkx : k < xs.length := by omega
      have hv : t.mem (args.base + k) = xs[k] :=
        (hmod.2 _ (by dsimp only; omega) (by simp; omega)).trans (hxs.get k hkx)
      have hvfit : Fits w (t.mem (args.base + k)) := hv ▸ hxs.get k hkx ▸ hwf.mem_fits _
      have hpre : pre (k + 1) = pre k ++ (if xs[k] = args.target then [] else [xs[k]]) := by
        simp only [pre, List.take_add_one, List.getElem?_eq_getElem hkx, Option.toList_some,
          List.filter_append, List.filter_cons, List.filter_nil]
        split_ifs <;> simp_all
      refine ⟨trivial, ?_⟩
      unfold filterNeStep
      framed_triple
      · rename_i hc; rw [hv] at hc
        dsimp only; rw [hpre, ite_eq_left hc, List.append_nil]
        exact ⟨hfr, by omega, rfl, rfl, by omega, hacc⟩
      · rename_i hc; rw [hv] at hc
        dsimp only; rw [hpre, ite_eq_right hc, List.length_append, List.length_singleton]
        refine ⟨hfr, by omega, by omega, rfl, by omega, Block.holdsList_append_iff.mpr
          ⟨hacc.frame fun a _ ha => Function.update_of_ne (by omega) _ _, ?_⟩⟩
        exact Block.holdsList_cons_iff.mpr ⟨by rw [hv]; exact Function.update_self ..,
          Block.holdsList_nil _ _⟩)
    fun _ _ h _ => h
  have hft : Memory.FramedTriple w s (filterNe args) (1 + 2 * args.len) (Set.Ici s.frontier)
      fun r t => t.frontier = s.frontier + args.len ∧ r.1 = s.frontier ∧
        r.2 = (pre args.len).length ∧ Block.HoldsList s.frontier (pre args.len) t.mem := by
    unfold filterNe
    exact Memory.FramedTriple.mono (Memory.FramedTriple.allocDirty_bind hfit
      (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl fun _ _ h _ =>
        Memory.FramedTriple.pure ⟨h.1, rfl, h.2.2.2.1, h.2.2.2.2.2⟩)) (by omega) fun _ _ => id
  obtain ⟨hv, -, hm, hfr, hr1, hr2, hh⟩ := framedTriple_iff_realization.mp hft
  simp only [pre, ← hlen, List.take_length] at hr2 hh
  have := List.length_filter_le (fun v => decide (v ≠ args.target)) xs
  exact ⟨hv, hfr, preservesBelow_of_modifies hm (.refl le_rfl), hr1, hr2,
    ⟨by omega, hr1 ▸ hh⟩⟩

theorem filterNe_realizes :
    Realizes .exact filterNe WordEncoding.encode WordEncoding.encode
      (fun w args s => Fits w (args.base + args.len) ∧ Fits w (s.frontier + args.len))
      (fun _ _ => 0) := by
  unfold filterNe
  realize
  refine iterationSafe_of_stepInv _ _ w _
    (fun j st _ => st.src + j = d.base + d.len ∧ st.dst + j ≤ s.frontier + d.len ∧
      st.count + j ≤ d.len)
    (fun j st t ⟨hsrc, hdst, hcnt⟩ => ?_)
    ⟨rfl, le_rfl, by simp⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact h.1.of_le (by omega)
    · exact ⟨h.1.of_le (by omega), h.2.of_le (by omega), h.1.of_le (by omega)⟩
  · rw [(filterNeStep_eval _ _ _).1]
    split_ifs <;> (dsimp only; omega)

theorem copyWords_frame (args : CopyArgs) (t : Memory.State) :
    ((Memory.spec 0).clientState t (copyWords args)).frontier = t.frontier ∧
    ∀ a, a < args.dst → ((Memory.spec 0).clientState t (copyWords args)).mem a = t.mem a := by
  obtain ⟨src, dst, n⟩ := args
  unfold copyWords
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  induction n generalizing src dst t with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    simp only [iterate]
    obtain ⟨hfr_i, hmem_i⟩ := ih ⟨Function.update t.mem dst (t.mem src), t.frontier⟩
      (src + 1) (dst + 1)
    exact ⟨hfr_i, fun a ha =>
      (hmem_i a (Nat.lt_succ_of_lt ha)).trans (Function.update_of_ne ha.ne _ t.mem)⟩

end Cslib.Algorithms.WordRAM.VariableElimination
