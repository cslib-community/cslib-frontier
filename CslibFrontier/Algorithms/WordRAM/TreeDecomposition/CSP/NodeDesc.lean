/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Model
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Tactic.Realize

/-!
# Node descriptor framing invariants and generic DP table-fill lemma

This module provides the shared node-descriptor machinery used across all three parallel node
handler modules (`LeafIntro`, `Forget`, and `Join`) as well as `NodeStep`/`Pass`:

* `writeDescProg`: writes a 4-word node descriptor `[bagPtr, bagLen, tblPtr, tblLen]`.
* `FrameOutsideRange`: framing invariant preserving all previously allocated words outside a
  single descriptor slice `[lo, hi)`.
* `NodeDescAt`: semantic invariant tying a 4-word descriptor slot to `bagList S` and
  `dpInstTree counting q cs vars S`.
* `tableFillProg_spec`: generic indexed loop specification used by `introFillProg`,
  `forgetFillProg`, and `joinFillProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.DescWriteArgs`: arguments for `writeDescProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.writeDescProg`: 4-word node descriptor writer.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.FrameOutsideRange`: range-scoped memory framing
  predicate.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeDescAt`: descriptor-slot invariant for a subtree.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.writeDescProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.writeDescProg_realizes`: correctness and
  realization of `writeDescProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeDescAt.frame`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeDescAt.mono_frontier`: descriptor framing lemmas.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.tableFillProg_spec`: shared DP table-fill lemma.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Descriptor writes, framing invariants, and the four nice-tree node handlers -/

/-- Register arguments for the 4-word node descriptor writer `writeDescProg`. -/
structure DescWriteArgs where
  /-- Base address of the 4-word descriptor slot for the current tree node. -/
  dCur : ℕ
  /-- Base address of the materialized bag slice. -/
  bagPtr : ℕ
  /-- Length of the materialized bag slice. -/
  bagLen : ℕ
  /-- Base address of the DP table slice. -/
  tblPtr : ℕ
  /-- Length of the DP table slice (`q ^ bagLen`). -/
  tblLen : ℕ

/-- Tuple equivalence encoding `DescWriteArgs` into Word-RAM registers. -/
@[expose] def DescWriteArgs.equiv :
    DescWriteArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.dCur, a.bagPtr), a.bagLen), a.tblPtr), a.tblLen)
  invFun := fun ((((dc, bp), bl), tp), tl) => ⟨dc, bp, bl, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding DescWriteArgs := .ofEquiv DescWriteArgs.equiv

/-- Write the 4-word descriptor `[bagPtr, bagLen, tblPtr, tblLen]` at `a.dCur`. -/
def writeDescProg (a : DescWriteArgs) : Memory.Prog Unit := do
  Memory.write a.dCur a.bagPtr
  Memory.write (a.dCur + 1) a.bagLen
  Memory.write (a.dCur + 2) a.tblPtr
  Memory.write (a.dCur + 3) a.tblLen

/-- Memory framing invariant: `s₁` extends `s₀`'s frontier and preserves every previously
allocated address outside `[lo, hi)`. -/
@[expose] def FrameOutsideRange (lo hi : ℕ) (s₀ s₁ : Memory.State) : Prop :=
  s₀.frontier ≤ s₁.frontier ∧
  ∀ x < s₀.frontier, (x < lo ∨ hi ≤ x) → s₁.mem x = s₀.mem x

theorem FrameOutsideRange.refl (lo hi : ℕ) (s : Memory.State) :
    FrameOutsideRange lo hi s s :=
  ⟨le_rfl, fun _ _ _ => rfl⟩

theorem FrameOutsideRange.of_preservesBelow (lo hi : ℕ) {s₀ s₁ : Memory.State}
    (hp : PreservesBelow s₀.frontier s₀ s₁) :
    FrameOutsideRange lo hi s₀ s₁ :=
  ⟨hp.2.1, fun x hx _ => hp.2.2 x hx⟩

theorem FrameOutsideRange.mono_range {lo₁ hi₁ lo₂ hi₂ : ℕ} {s₀ s₁ : Memory.State}
    (h : FrameOutsideRange lo₁ hi₁ s₀ s₁) (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) :
    FrameOutsideRange lo₂ hi₂ s₀ s₁ :=
  ⟨h.1, fun x hx hout => h.2 x hx (hout.imp (fun hlt => lt_of_lt_of_le hlt hlo)
    (fun hge => le_trans hhi hge))⟩

theorem FrameOutsideRange.trans {lo hi : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : FrameOutsideRange lo hi s₀ s₁) (h₂ : FrameOutsideRange lo hi s₁ s₂) :
    FrameOutsideRange lo hi s₀ s₂ :=
  ⟨h₁.1.trans h₂.1, fun x hx hout =>
    (h₂.2 x (lt_of_lt_of_le hx h₁.1) hout).trans (h₁.2 x hx hout)⟩

theorem HoldsIn.frame_outsideRange {base lo hi : ℕ} {xs : List ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀)
    (hdisj : base + xs.length ≤ lo ∨ hi ≤ base)
    (hf : FrameOutsideRange lo hi s₀ s₁) :
    HoldsIn base xs s₁ := by
  refine ⟨h.1.trans hf.1, h.2.frame fun x hlo hhi => ?_⟩
  exact hf.2 x (by have := h.1; omega) (by omega)

/-- Memory validity, descriptor storage, and range-framing spec for `writeDescProg`. -/
theorem writeDescProg_spec {w : ℕ} (a : DescWriteArgs) {s : Memory.State}
    (hd : a.dCur + 4 ≤ s.frontier)
    (hbp : Fits w a.bagPtr) (hbl : Fits w a.bagLen)
    (htp : Fits w a.tblPtr) (htl : Fits w a.tblLen) :
    let s₁ := (Memory.spec 0).clientState s (writeDescProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeDescProg a)) ∧
    s₁.frontier = s.frontier ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s s₁ ∧
    s₁.mem a.dCur = a.bagPtr ∧
    s₁.mem (a.dCur + 1) = a.bagLen ∧
    s₁.mem (a.dCur + 2) = a.tblPtr ∧
    s₁.mem (a.dCur + 3) = a.tblLen ∧
    memoryCost (writeDescProg a) s ≤ 4 := by
  unfold writeDescProg
  let t₁ : Memory.State := ⟨Function.update s.mem a.dCur a.bagPtr, s.frontier⟩
  let t₂ : Memory.State := ⟨Function.update t₁.mem (a.dCur + 1) a.bagLen, s.frontier⟩
  let t₃ : Memory.State := ⟨Function.update t₂.mem (a.dCur + 2) a.tblPtr, s.frontier⟩
  let t₄ : Memory.State := ⟨Function.update t₃.mem (a.dCur + 3) a.tblLen, s.frontier⟩
  have hst : (Memory.spec 0).clientState s
      (Memory.write a.dCur a.bagPtr >>= fun _ =>
        Memory.write (a.dCur + 1) a.bagLen >>= fun _ =>
        Memory.write (a.dCur + 2) a.tblPtr >>= fun _ =>
        Memory.write (a.dCur + 3) a.tblLen) = t₄ := rfl
  refine ⟨validHistory_write_bind (by omega) hbp
      (validHistory_write_bind (by dsimp only; omega) hbl
        (validHistory_write_bind (by dsimp only; omega) htp
          (validHistory_write (by dsimp only; omega) htl))), by rw [hst], ?_, ?_, ?_, ?_, ?_,
    by simp only [memoryCost_bind', memoryCost_write]; omega⟩
  · rw [hst]
    exact ⟨le_rfl, fun x _ hout => by
      simp (disch := omega) only [t₄, t₃, t₂, t₁, Function.update_of_ne]⟩
  all_goals rw [hst]; simp (disch := omega) only [t₄, t₃, t₂, t₁, Function.update_of_ne,
    Function.update_self]

/-- Exact-basis Word-RAM realization certificate for `writeDescProg`. -/
theorem writeDescProg_realizes :
    Realizes .exact writeDescProg WordEncoding.encode WordEncoding.encode
      (fun w a _ => Fits w (a.dCur + 3))
      (fun _ _ => 0) := by
  unfold writeDescProg
  realize
  · exact h.of_le (by omega)
  · exact h.of_le (by omega)
  · exact h

/-- Invariant asserting that descriptor slot `[d, d + 4)` in memory `s` correctly references
the materialized bag and DP table of subtree `S`, both allocated at or above `F_lo`. -/
structure NodeDescAt (F_lo : ℕ) (counting : Bool) (q : ℕ)
    (cs : List (ConstraintTable q)) (vars : List ℕ) (S : NiceTree ℕ) (d : ℕ)
    (s : Memory.State) : Prop where
  /-- Descriptor slot lies strictly below the dynamic allocation threshold `F_lo`. -/
  desc_hi : d + 4 ≤ F_lo
  /-- Materialized bag pointer lies at or above `F_lo`. -/
  bag_lo : F_lo ≤ s.mem d
  /-- Stored bag length equals `(bagList S).length`. -/
  bag_len : s.mem (d + 1) = (bagList S).length
  /-- Materialized bag slice agrees with `bagList S`. -/
  bag_holds : HoldsIn (s.mem d) (bagList S) s
  /-- Materialized DP table pointer lies at or above `F_lo`. -/
  tbl_lo : F_lo ≤ s.mem (d + 2)
  /-- Stored DP table length equals `q ^ (bagList S).length`. -/
  tbl_len : s.mem (d + 3) = q ^ (bagList S).length
  /-- Materialized DP table slice agrees with `dpInstTree counting q cs vars S`. -/
  tbl_holds : HoldsIn (s.mem (d + 2)) (dpInstTree counting q cs vars S) s

/-- Frame `NodeDescAt` across writes strictly restricted to `[lo, hi)` (with `hi ≤ F_lo`). -/
theorem NodeDescAt.frame {F_lo : ℕ} {counting : Bool} {q : ℕ}
    {cs : List (ConstraintTable q)} {vars : List ℕ} {S : NiceTree ℕ} {d lo hi : ℕ}
    {s₀ s₁ : Memory.State} (h : NodeDescAt F_lo counting q cs vars S d s₀)
    (hd : d + 4 ≤ lo ∨ hi ≤ d) (hhi : hi ≤ F_lo)
    (hf : FrameOutsideRange lo hi s₀ s₁) :
    NodeDescAt F_lo counting q cs vars S d s₁ := by
  have hFlo_fr : F_lo ≤ s₀.frontier := by
    have := h.bag_lo; have := h.bag_holds.1; omega
  obtain ⟨hm0, hm1, hm2, hm3⟩ : s₁.mem d = s₀.mem d ∧ s₁.mem (d + 1) = s₀.mem (d + 1) ∧
      s₁.mem (d + 2) = s₀.mem (d + 2) ∧ s₁.mem (d + 3) = s₀.mem (d + 3) := by
    have := h.desc_hi
    refine ⟨hf.2 _ ?_ ?_, hf.2 _ ?_ ?_, hf.2 _ ?_ ?_, hf.2 _ ?_ ?_⟩ <;> omega
  exact
    ⟨h.desc_hi,
     by rw [hm0]; exact h.bag_lo,
     by rw [hm1]; exact h.bag_len,
     by rw [hm0]; exact h.bag_holds.frame_outsideRange (.inr (le_trans hhi h.bag_lo)) hf,
     by rw [hm2]; exact h.tbl_lo,
     by rw [hm3]; exact h.tbl_len,
     by rw [hm2]; exact h.tbl_holds.frame_outsideRange (.inr (le_trans hhi h.tbl_lo)) hf⟩

/-- Lift `NodeDescAt` monotonically across frontier-preserving allocations/writes. -/
theorem NodeDescAt.mono_frontier {F_lo : ℕ} {counting : Bool} {q : ℕ}
    {cs : List (ConstraintTable q)} {vars : List ℕ} {S : NiceTree ℕ} {d : ℕ}
    {s₀ s₁ : Memory.State}
    (h : NodeDescAt F_lo counting q cs vars S d s₀)
    (hp : PreservesBelow s₀.frontier s₀ s₁) :
    NodeDescAt F_lo counting q cs vars S d s₁ :=
  h.frame (.inr le_rfl) (by have := h.desc_hi; omega)
    (FrameOutsideRange.of_preservesBelow d d hp)

/-- Generic invariant-preserving loop specification for filling a contiguous DP table slice
`[tblPtr, tblPtr + tblLen)` in index order `0, 1, ..., tblLen - 1`. -/
theorem tableFillProg_spec {α : Type} {w : ℕ} (step : α × ℕ → Memory.Prog ℕ)
    (a : α) (tblPtr tblLen stepCost : ℕ) (targetTbl : List ℕ) (s : Memory.State)
    (Inv : Memory.State → Prop) (hinv : Inv s)
    (htarget_len : targetTbl.length = tblLen) (htbl_hi : tblPtr + tblLen ≤ s.frontier)
    (hstep : ∀ (k : ℕ) (t : Memory.State), (hk : k < tblLen) →
      let m := tblLen - (k + 1)
      Inv t → t.frontier = s.frontier → PreservesBelow tblPtr s t →
      HoldsIn tblPtr (targetTbl.take m) t →
      let entryVal := targetTbl[m]'(by
        have hm : tblLen - (k + 1) < tblLen := Nat.sub_lt (Nat.zero_lt_of_lt hk) (Nat.succ_pos k)
        simpa only [htarget_len] using hm)
      let t₁ : Memory.State := ⟨Function.update t.mem (tblPtr + m) entryVal, t.frontier⟩
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (step (a, m))) ∧
      (Memory.spec 0).clientState t (step (a, m)) = t₁ ∧
      (Memory.spec 0).clientResult t (step (a, m)) = m + 1 ∧
      Inv t₁ ∧
      memoryCost (step (a, m)) t ≤ stepCost) :
    let prog : Memory.Prog Unit := do let _ ← iterate step a tblLen 0; pure ()
    let s₁ := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow tblPtr s s₁ ∧
    HoldsIn tblPtr targetTbl s₁ ∧
    memoryCost prog s ≤ tblLen * stepCost := by
  have hloop := iterate_spec step (fun _ _ _ => True) w a stepCost tblLen
    (fun k c t => k = c ∧ Inv t ∧ t.frontier = s.frontier ∧ PreservesBelow tblPtr s t ∧
      HoldsIn tblPtr (targetTbl.take k) t) (fun _ => True) ?_ 0 s
    ⟨rfl, hinv, rfl, PreservesBelow.refl (by omega),
      by rw [List.take_zero]; exact HoldsIn.nil (by omega)⟩
  · obtain ⟨-, hv, hc, -, -, -, -, hfr, hp, hh⟩ := hloop
    rw [List.take_of_length_le htarget_len.le] at hh
    refine ⟨validHistory_bind_step hv (validHistory_pure w _ ()), ?_⟩
    rw [StateTransitionSpec.clientState_bind, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    exact ⟨hfr, hp, hh, hc.trans_eq (Nat.mul_comm _ _)⟩
  rintro k hk _ t ⟨rfl, hI, hfr, hp, hh⟩
  have hm : tblLen - (tblLen - (k + 1) + 1) = k := by omega
  obtain ⟨hv, hst, hres, hI₁, hc⟩ := hstep (tblLen - (k + 1)) t (by omega) hI hfr hp (by rwa [hm])
  simp only [hm] at hv hst hres hI₁ hc
  have hk' : k < targetTbl.length := htarget_len ▸ hk
  have htake_len : (targetTbl.take k).length = k := List.length_take_of_le (by omega)
  have hh₁ := holdsIn_append_one (v := targetTbl[k]'hk') hh (by rw [htake_len, hfr]; omega)
  rw [htake_len, ← List.take_succ_eq_append_getElem hk'] at hh₁
  refine ⟨trivial, hv, hc, ?_⟩
  rw [hst, hres]
  exact ⟨rfl, fun _ h => absurd trivial h, rfl, hI₁, hfr,
    hp.trans (preservesBelow_write (Nat.le_add_right _ _) (by omega)), hh₁⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
