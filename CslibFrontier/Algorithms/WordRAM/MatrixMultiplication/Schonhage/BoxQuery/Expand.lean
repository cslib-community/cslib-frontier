/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.ExpandMemory
import CslibFrontier.Computability.WordRAM.PreservesMask
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Complete native expansion of one query prefix

The program decodes the actual output digit, then pushes exactly the existing ordered
child family. This theorem covers all native setup, branch, descriptor and stack-store
instructions. It preserves older pending tasks and every word outside the new records.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem output_digit_nine_iff (z : OutVar) :
    (PrunedQuery.outputDigits.symm z).val = 9 ↔ z.IsInner := by decide +revert

/-- Native division and remainder read the existing output-coordinate digit exactly. -/
theorem query_digit_at {L k : ℕ} (η : OutStr L) (hk : k < L) :
    (PrunedQuery.queryIndex η).val / 10 ^ k % 10 =
      (PrunedQuery.outputDigits.symm (outAt η k)).val := by
  have hd := finFunctionFinEquiv_symm_apply_val (PrunedQuery.queryIndex η) (⟨k, hk⟩ : Fin L)
  simpa [PrunedQuery.queryIndex, Encoding.leafIndex, privateLeaf, outAt, hk,
    PrunedQuery.outputDigits] using hd.symm

/-- Registers that may change while computing and pushing the complete child family. -/
@[expose] def ExpandLocal (i : Fin registers) : Prop :=
  ExpandSetupLocal i ∨ IndexedPushLocal i

instance (i : Fin registers) : Decidable (ExpandLocal i) :=
  inferInstanceAs (Decidable (ExpandSetupLocal i ∨ IndexedPushLocal i))

private theorem expand_preserves (i : Fin registers) :
    ¬ExpandLocal i → expand.Preserves i :=
  Code.preserves_of_preservesAllPred (P := fun i => ¬ExpandLocal i) (c := expand)
    (by decide +kernel) i

/-- The actual internal-node code prepends exactly its genuine children, with no layout oracle. -/
theorem exec_expand {w L t F : ℕ} (η : OutStr L) (xs : List Term)
    (rest : List (List Term)) (x : Data registers)
    (hx : Good η t xs) (hk : xs.length < L)
    (hrest : StackMemory η F rest x.mem)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = rest.length)
    (hq : x.regs Reg.query = (PrunedQuery.queryIndex η).val)
    (ht : x.regs BoxTable.Reg.threshold = t)
    (hdepth : x.regs Reg.depth = xs.length) (hc : x.regs Reg.code = prefixCode xs)
    (hu : x.regs Reg.used = usedFrom η 0 xs) (he : x.regs Reg.stars = starsFrom η 0 xs)
    (hp : x.regs Reg.power = 10 ^ xs.length)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (h10 : x.regs BoxTable.Reg.ten = 10) (h9 : x.regs BoxTable.Reg.nine = 9)
    (h0 : x.regs BoxTable.Reg.nil = 0)
    (hfit : Fits w (F + 5 * (rest.length + 11) + 10 ^ (xs.length + 1) + xs.length +
      t + (PrunedQuery.queryIndex η).val + 32)) :
    ∃ y, ExecWithin w expand x y 178 ∧
      y.regs Reg.top = rest.length + (children η t xs).length ∧
      StackMemory η F (children η t xs ++ rest) y.mem ∧
      (∀ q, ¬(F + rest.length * 5 ≤ q ∧
        q < F + (rest.length + (children η t xs).length) * 5) → y.mem q = x.mem q) ∧
      (∀ i, ¬ExpandLocal i → y.regs i = x.regs i) := by
  have hused := hx.2.2
  have hstars := starsFrom_le η 0 xs
  have hcode := prefixCode_lt xs
  have hcode' : prefixCode xs + 9 * 10 ^ xs.length ≤ 10 ^ (xs.length + 1) := by
    rw [pow_succ]; omega
  have hcommon : Fits w (F + 5 * (rest.length + 11) + prefixCode xs +
      9 * 10 ^ xs.length + usedFrom η 0 xs + starsFrom η 0 xs + 32) := hfit.of_le (by omega)
  obtain ⟨a, ha, ad, ak, ap, am, af⟩ := exec_expandSetup x hq hdepth hp h1 h10
    (hfit.of_le (by rw [pow_succ]; omega))
  obtain ⟨aF, an, ac, au, ae, app, a5, a1, a9, a0, athreshold⟩ :
      a.regs Reg.stack = F ∧ a.regs Reg.top = rest.length ∧ a.regs Reg.code = prefixCode xs ∧
      a.regs Reg.used = usedFrom η 0 xs ∧ a.regs Reg.stars = starsFrom η 0 xs ∧
      a.regs Reg.power = 10 ^ xs.length ∧ a.regs Reg.five = 5 ∧ a.regs BoxTable.Reg.one = 1 ∧
      a.regs BoxTable.Reg.nine = 9 ∧ a.regs BoxTable.Reg.nil = 0 ∧
      a.regs BoxTable.Reg.threshold = t := by regs_frame
  have adigit : a.regs Reg.digit = (PrunedQuery.outputDigits.symm
      (outAt η xs.length)).val := ad.trans (query_digit_at η hk)
  have apow : a.regs Reg.childPower = 10 ^ (xs.length + 1) := by simpa only [pow_succ] using ap
  have arest : StackMemory η F rest a.mem := by simpa only [am] using hrest
  have hcond : (Cond.eq Reg.digit BoxTable.Reg.nine).Holds a ↔ (outAt η xs.length).IsInner := by
    simp only [Cond.holds_eq, adigit, a9, output_digit_nine_iff]
  by_cases hi : (outAt η xs.length).IsInner
  · let mid : List (List Term) := if usedFrom η 0 xs < t then
      List.ofFn (fun d : Fin 9 => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]) else []
    have hmid_len : mid.length ≤ 9 := by dsimp only [mid]; split_ifs <;> simp
    have hmid : ∃ b, ExecWithin w (.branch (.lt Reg.used BoxTable.Reg.threshold)
          nineChildren (ram[ Reg.temporary ← Reg.temporary ])) a b 155 ∧
        b.regs Reg.top = rest.length + mid.length ∧
        StackMemory η F (mid ++ rest) b.mem ∧
        (∀ q, ¬(F + rest.length * 5 ≤ q ∧ q < F + (rest.length + mid.length) * 5) →
          b.mem q = a.mem q) ∧
        (∀ i, ¬IndexedPushLocal i → b.regs i = a.regs i) := by
      by_cases hspare : usedFrom η 0 xs < t
      · obtain ⟨b, hb, bn, bm, bf⟩ := exec_nineChildren a aF an ak ac au ae app apow a5 a1
          (hcommon.of_le (by omega))
        have hs := arest.indexedChildren xs hi (List.ofFn fun i : Fin 9 => ⟨8 - i.val, by omega⟩)
        rw [reverse_nineChildren] at hs
        refine ⟨b, hb.branch_pos (by simpa only [Cond.holds_lt, au, athreshold] using hspare),
          by simpa only [mid, ite_eq_left hspare, List.length_ofFn] using bn,
          by simpa only [mid, ite_eq_left hspare, bm] using hs,
          fun q hq => by
            rw [bm, writeIndexedChildren_frame]
            simpa only [mid, ite_eq_left hspare, List.length_ofFn] using hq, bf⟩
      · refine ⟨a.set Reg.temporary (a.regs Reg.temporary),
          (ExecWithin.copy.branch_neg
            (by simpa only [Cond.holds_lt, au, athreshold] using hspare)).mono (by decide),
          by simp [mid, hspare, an], by simpa [mid, hspare] using arest,
          fun _ _ => rfl, fun i hi => Data.set_regs_of_ne (fun h => hi (Or.inl (Or.inl h))) _⟩
    obtain ⟨b, hb', bn, bs, bframe, bf⟩ := hmid
    obtain ⟨bF, bk, bc, bu, be, bp, bcp, b5, b1, b9, b0⟩ :
        b.regs Reg.stack = F ∧ b.regs Reg.depth = xs.length + 1 ∧ b.regs Reg.code = prefixCode xs ∧
        b.regs Reg.used = usedFrom η 0 xs ∧ b.regs Reg.stars = starsFrom η 0 xs ∧
        b.regs Reg.power = 10 ^ xs.length ∧ b.regs Reg.childPower = 10 ^ (xs.length + 1) ∧
        b.regs Reg.five = 5 ∧ b.regs BoxTable.Reg.one = 1 ∧ b.regs BoxTable.Reg.nine = 9 ∧
        b.regs BoxTable.Reg.nil = 0 := by regs_frame
    obtain ⟨y, hy, yn, ym, _⟩ := exec_p0Child b bF bn bk bc bu be bp bcp b5 b1 b9 b0
      (hcommon.of_le (by omega))
    have hex : ExecWithin w expand x y 178 :=
      (ha.seq ((hb'.seq hy).branch_pos (hcond.mpr hi))).mono (by omega)
    have hch : children η t xs = (xs ++ [.P0]) :: mid := by
      dsimp only [children, mid]; exact ite_eq_left hi
    refine ⟨y, hex, by simp only [hch, List.length_cons, yn]; omega, ?_, ?_,
      fun i h => hex.regs_eq (expand_preserves i h)⟩
    · simpa only [ym, hch, List.cons_append, List.length_append, Nat.add_comm mid.length] using
        bs.p0Child xs hi
    · intro q hqout
      rw [hch, List.length_cons] at hqout
      rw [ym, writeTask_frame _ _ _ _ _ _ _ _ _ (by omega), bframe _ (by omega), am]
  · have hd : (PrunedQuery.outputDigits.symm (outAt η xs.length)).val ≤ 9 :=
      Nat.le_of_lt_succ (PrunedQuery.outputDigits.symm _).isLt
    obtain ⟨y, hy, yn, ym, _⟩ := exec_privateChild a hd aF an ak ac au ae app apow adigit a5 a1
      (hcommon.of_le (by omega))
    have hex : ExecWithin w expand x y 178 :=
      (ha.seq (hy.branch_neg (mt hcond.mp hi))).mono (by omega)
    refine ⟨y, hex, by simpa [children, hi] using yn, ?_, ?_,
      fun i h => hex.regs_eq (expand_preserves i h)⟩
    · simpa only [ym, children, ite_eq_right hi, List.singleton_append] using
        arest.privateChild xs hi
    · intro q hqout
      rw [ym, writeTask_frame, am]
      simp only [children, ite_eq_right hi, List.length_singleton] at hqout
      omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
