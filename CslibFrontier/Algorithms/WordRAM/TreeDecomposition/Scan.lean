/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagMask
public import CslibFrontier.Computability.WordRAM.Realization.PrefixFrame
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
public import CslibFrontier.DataStructure.Memory.TripleFrame
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Realize

/-!
# Shared memory-block and bag-scan primitives for tree-decomposition algorithms

Certified `Memory.Prog` routines over allocated memory blocks, shared by the Word-RAM dynamic
programs over tree decompositions
(`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet` and
`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP`):

* `powProg`: bounded-word exponentiation `base ^ exp` in `exp` loop steps;
* `bagMemProg`: linear membership scan of a materialized bag list (`memBag`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg`
* `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg`

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg_framed`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg_realizes`
* `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg_framed`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg_realizes`
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Bounded-word exponentiation (`powProg`) -/

/-- Arguments `(base, exp)` for `powProg`. -/
structure PowArgs where
  /-- Base word. -/
  base : ℕ
  /-- Exponent count. -/
  exp : ℕ

/-- Register tuple equivalence for `PowArgs`. -/
@[expose] def PowArgs.equiv : PowArgs ≃ ℕ × ℕ where
  toFun a := (a.base, a.exp)
  invFun := fun (base, exp) => ⟨base, exp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PowArgs := .ofEquiv PowArgs.equiv

private def powStep (env : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  pure (env.2 * env.1)

/-- Compute `args.base ^ args.exp` by repeated multiplication. -/
def powProg (args : PowArgs) : Memory.Prog ℕ :=
  iterate powStep args.base args.exp 1

theorem powProg_state (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (powProg args) = s := by
  unfold powProg
  exact clientState_iterate_eq_of powStep args.base (fun _ _ => rfl) args.exp 1 s

theorem powProg_result (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp := by
  have h := iterate_invariant_of powStep args.base
    (fun j acc _ => acc * args.base ^ j = args.base ^ args.exp)
    (fun j acc _ h => by rw [← h, pow_succ', ← Nat.mul_assoc]; rfl)
    (n := args.exp) (a := 1) (s := s) (Nat.one_mul _)
  simpa only [powProg, Nat.pow_zero, Nat.mul_one] using h

theorem powProg_spec {w : ℕ} (args : PowArgs) {s : Memory.State} (hs : 0 < s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (powProg args)) ∧
    (Memory.spec 0).clientState s (powProg args) = s ∧
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp ∧
    memoryCost (powProg args) s ≤ args.exp :=
  ⟨validHistory_iterate_inv (fun t => 0 < t.frontier) powStep args.base
      (fun _ t ht => validHistory_read_bind ht (validHistory_pure w t _)) args.exp 1 hs,
    powProg_state args s, powProg_result args s, by
      simpa only [powProg, Nat.one_mul] using
        memoryCost_iterate_le_of powStep 1 args.base (fun _ _ => le_rfl) args.exp 1 s⟩

/-- `powProg` as a framed triple: it only reads, returns `base ^ exp` and leaves the state
unchanged. -/
theorem powProg_framed {w : ℕ} (args : PowArgs) {s : Memory.State} (hs : 0 < s.frontier) :
    Memory.FramedTriple w s (powProg args) args.exp ∅ fun r t =>
      r = args.base ^ args.exp ∧ t = s :=
  let ⟨hv, hst, hr, hc⟩ := powProg_spec (w := w) args hs
  Memory.FramedTriple.of_readOnly hv hst hr hc

theorem powProg_realizes :
    Realizes .exact powProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.base ^ args.exp))
      (fun _ _ => 0) := by
  unfold powProg
  realize
  · exact h.1
  · obtain ⟨h1, hpow⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (acc : ℕ) (_ : Memory.State) =>
        j ≤ d.exp ∧ acc = d.base ^ (d.exp - j) ∧ Fits w acc)
      (fun j acc _ ⟨hj_le, hacc, _⟩ => ?_)
      ⟨le_rfl, by simp only [Nat.sub_self, Nat.pow_zero], h1⟩
    dsimp only [powStep]
    have hexp_step : d.exp - j = (d.exp - (j + 1)) + 1 := by omega
    have hprod : acc * d.base = d.base ^ (d.exp - j) := by
      rw [hacc, hexp_step, Nat.pow_succ]
    have hfit_next : Fits w (acc * d.base) := by
      rw [hprod]
      rcases Nat.eq_zero_or_pos d.base with hb0 | hb_pos
      · rw [hb0, zero_pow (by omega)]
        exact fits_zero w
      · exact hpow.of_le (Nat.pow_le_pow_right hb_pos (Nat.sub_le _ _))
    exact ⟨hfit_next, Nat.le_of_succ_le hj_le, hprod, hfit_next⟩

/-! ### Linear bag membership scan (`bagMemProg`) -/

private structure BagScanState where
  cur : ℕ
  found : ℕ

private def BagScanState.equiv : BagScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BagScanState := .ofEquiv BagScanState.equiv

/-- Arguments `(target, base, len)` for `bagMemProg`. -/
structure BagScanArgs where
  /-- Element sought. -/
  target : ℕ
  /-- Base address of the bag list in memory. -/
  base : ℕ
  /-- Length of the bag list. -/
  len : ℕ

/-- Register tuple equivalence for `BagScanArgs`. -/
@[expose] def BagScanArgs.equiv : BagScanArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.target, a.base), a.len)
  invFun := fun ((target, base), len) => ⟨target, base, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding BagScanArgs := .ofEquiv BagScanArgs.equiv

private def bagMemStep (env : ℕ × BagScanState) : Memory.Prog BagScanState := do
  let v ← Memory.read env.2.cur
  pure ⟨env.2.cur + 1, if v = env.1 then 1 else env.2.found⟩

/-- Return `1` if `args.target` occurs in the `args.len`-word slice at `args.base`, else `0`. -/
def bagMemProg (args : BagScanArgs) : Memory.Prog ℕ := do
  let res ← iterate bagMemStep args.target args.len ⟨args.base, 0⟩
  pure res.found

theorem bagMemProg_state (args : BagScanArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (bagMemProg args) = s := by
  unfold bagMemProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of bagMemStep args.target (fun _ _ => rfl) args.len ⟨args.base, 0⟩ s

theorem bagMemProg_spec {w : ℕ} (args : BagScanArgs) {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bagMemProg args)) ∧
    (Memory.spec 0).clientState s (bagMemProg args) = s ∧
    (Memory.spec 0).clientResult s (bagMemProg args) =
      (if memBag args.target xs then 1 else 0) ∧
    memoryCost (bagMemProg args) s ≤ args.len := by
  have hcost : memoryCost (bagMemProg args) s ≤ args.len := by
    unfold bagMemProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of bagMemStep 1 args.target (fun _ _ => le_rfl)
        args.len ⟨args.base, 0⟩ s
  suffices ∀ ys cur, HoldsIn cur ys s → ∀ found, (found = 0 ∨ found = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate bagMemStep args.target ys.length ⟨cur, found⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate bagMemStep args.target ys.length ⟨cur, found⟩)).found =
        if found = 1 ∨ memBag args.target ys = true then 1 else 0 by
    have hrun := this xs args.base hxs 0 (.inl rfl)
    rw [hlen] at hrun
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _), bagMemProg_state args s,
      ?_, hcost⟩
    unfold bagMemProg
    rw [StateTransitionSpec.clientResult_bind]
    exact hrun.2.trans (by cases memBag args.target xs <;> rfl)
  intro ys
  induction ys with
  | nil =>
    intro cur _ found hfd
    refine ⟨validHistory_pure w s _, ?_⟩
    rcases hfd with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur hcur found hfd
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    have hstep : (Memory.spec 0).clientResult s (bagMemStep (args.target, ⟨cur, found⟩)) =
        ⟨cur + 1, if u = args.target then 1 else found⟩ := by
      rw [← hmem_u]; rfl
    obtain ⟨hv, hr⟩ := ih (cur + 1) hrest (if u = args.target then 1 else found)
      (by split_ifs <;> simp [hfd])
    rw [← hstep] at hv hr
    have hlt : cur < s.frontier := by omega
    refine ⟨validHistory_bind_step (validHistory_read_bind hlt (validHistory_pure w s _)) hv,
      hr.trans ?_⟩
    by_cases heq : u = args.target <;> simp [memBag, heq, eq_comm]

/-- `bagMemProg` as a framed triple: it only reads, returns the membership flag and leaves the
state unchanged. -/
theorem bagMemProg_framed {w : ℕ} (args : BagScanArgs) {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len) :
    Memory.FramedTriple w s (bagMemProg args) args.len ∅ fun r t =>
      r = (if memBag args.target xs then 1 else 0) ∧ t = s :=
  let ⟨hv, hst, hr, hc⟩ := bagMemProg_spec (w := w) args hxs hlen
  Memory.FramedTriple.of_readOnly hv hst hr hc

theorem bagMemProg_realizes :
    Realizes .exact bagMemProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.base + args.len))
      (fun _ _ => 0) := by
  unfold bagMemProg
  realize
  obtain ⟨h1, hfit⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : BagScanState) (_ : Memory.State) =>
      st.cur + j = d.base + d.len ∧ st.found ≤ 1)
    (fun j st m ⟨hcur, hfd⟩ => ?_)
    ⟨rfl, Nat.zero_le _⟩
  dsimp only [bagMemStep]
  have hcur_fit : Fits w (st.cur + 1) := hfit.of_le (by omega)
  have hfd' : (if m.mem st.cur = d.target then 1 else st.found) ≤ 1 := by
    split_ifs <;> omega
  refine ⟨?_, by change (st.cur + 1) + j = d.base + d.len; omega, hfd'⟩
  split
  · exact ⟨hcur_fit, h1⟩
  · exact hcur_fit

end Cslib.Algorithms.WordRAM.TreeDecomposition
