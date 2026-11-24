/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Recursion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BitsGetElem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# A recursion that reads its input, within the space of one chain of frames

The value of the complete binary NAND tree whose leaves are the bits of a word, by the recursion
that evaluates the left subtree, then the right one unless the left one is false. A frame holds
the height and the index of a node and whether its second subtree is being evaluated. The body is
an ordinary function of a frame, the value just returned to it and the word; it reads the word at
a leaf. `Turing.MultiTapeTM.ComputableInSpace.recWith` runs it: the caller states what a frame
returns, a rank and the potential `(height + 1) * F` for frames of `F` bits. No stack, machine or
run is declared, and the space is `O(log² n)` for depth and frames of `O(log n)`.
-/

open Turing Turing.MultiTapeTM

namespace SpaceRecursionTest

/-- The NAND tree of height `k` over the bits of `w`, at the node with index `i` in its level. -/
def tree (w : List Bool) : ℕ → ℕ → Bool
  | 0, i => w[i]?.getD false
  | k + 1, i => !(tree w k (2 * i) && tree w k (2 * i + 1))

example : tree [true, true, false, true] 2 0 = true := by decide
example : tree [true, true, true, true] 2 0 = true := by decide
example : tree [true, false, true, false] 2 0 = false := by decide

/-- A frame of the recursion: a node of the tree, and whether its second subtree is being
evaluated, the first one having returned `true`. -/
structure Frame where
  /-- The height of the node. -/
  height : ℕ
  /-- The index of the node in its level. -/
  index : ℕ
  /-- Whether the second subtree is being evaluated. -/
  second : Bool

enc_structure encFrame : Frame where height : encNat, index : encNat, second : encBool

/-- A frame with the value just returned to it, if any. -/
abbrev encConfig : Frame × Option Bool ↪ List Bool := encPair encFrame (encOption encBool)

/-- The body: a leaf returns its bit; a node calls its first subtree, then its second one unless
the first returned `false`, and returns the NAND of the two values. -/
def body (p : (Frame × Option Bool) × List Bool) : (Frame × Frame) ⊕ Bool :=
  if p.1.2.isSome then
    if p.1.1.second then .inr (!p.1.2.getD false)
    else if p.1.2.getD false then
      .inl (⟨p.1.1.height, p.1.1.index, true⟩, ⟨p.1.1.height - 1, 2 * p.1.1.index + 1, false⟩)
    else .inr true
  else if decide (p.1.1.height = 0) then .inr (p.2[p.1.1.index]?.getD false)
  else .inl (⟨p.1.1.height, p.1.1.index, false⟩, ⟨p.1.1.height - 1, 2 * p.1.1.index, false⟩)

-- A leaf returns its bit, a node calls its first subtree, and a `false` from it is decisive.
example : body ((⟨0, 2, false⟩, none), [true, true, false]) = .inr false := rfl
example : body ((⟨1, 0, false⟩, none), [true, true]) = .inl (⟨1, 0, false⟩, ⟨0, 0, false⟩) := rfl
example : body ((⟨1, 0, false⟩, some false), [true, true]) = .inr true := rfl
example : body ((⟨1, 0, false⟩, some true), [true, true]) =
    .inl (⟨1, 0, true⟩, ⟨0, 1, false⟩) := rfl

/-- The budget of the body: the frame and the returned value, and the logarithm of the length of
the word. -/
abbrev budget (p : (Frame × Option Bool) × List Bool) : ℕ :=
  (encConfig p.1).length + Nat.log2 (encBits p.2).length

theorem body_inSpace : ComputableInSpace body (encPair encConfig encBits)
    (encSum (encPair encFrame encFrame) encBool) budget := by
  have hc : ComputableInSpace (fun p : (Frame × Option Bool) × List Bool => p.1)
      (encPair encConfig encBits) encConfig budget :=
    (ComputableInLogSpace.fst encConfig encBits).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _)
  have hconst {β : Type} (encB : β ↪ List Bool) (b : β) :
      ComputableInSpace (fun _ : (Frame × Option Bool) × List Bool => b)
        (encPair encConfig encBits) encB budget :=
    ComputableInSpace.budget_const b
  have hh := encFrame_height_budget hc.fst'
  have hi := encFrame_index_budget hc.fst'
  have ho := hc.snd'
  -- the bit of the word at the index of the frame
  have hfields : ComputableInLogSpace (fun f : Frame => (f.height, f.index, f.second)) encFrame
      encFrameFields := .of_eq fun f => (encFrame_apply f).symm
  have hbit : ComputableInSpace (fun p : (Frame × Option Bool) × List Bool => p.2[p.1.1.index]?)
      (encPair encConfig encBits) (encOption encBool) budget :=
    (ComputableInSpace.inputBit encBits).comp_logSpace_context
      (f := fun p : (Frame × Option Bool) × List Bool => (p.1.1.index, p.2))
      (ComputableInLogSpace.pair
        ((hfields.snd'.fst'.comp' (ComputableInLogSpace.fst encFrame (encOption encBool))).comp'
          (ComputableInLogSpace.fst encConfig encBits))
        (ComputableInLogSpace.snd encConfig encBits))
      (.of_le fun p => by
        have := encFrame_index_length_le p.1.1
        simp only [length_encPair]
        omega) fun _ => le_rfl
  have hpred := ComputableInSpace.budget_natPred hh
  have hleft := ComputableInSpace.budget_natMul (hconst encNat 2) hi
  have hright := ComputableInSpace.budget_natAdd hleft (hconst encNat 1)
  have hval := ComputableInSpace.budget_optionGetD false ho
  exact ComputableInSpace.budget_ite (ComputableInSpace.budget_optionIsSome ho)
    (ComputableInSpace.budget_ite (encFrame_second_budget hc.fst')
      (ComputableInSpace.budget_sumInr (ComputableInSpace.budget_boolNot hval))
      (ComputableInSpace.budget_ite hval
        (ComputableInSpace.budget_sumInl (ComputableInSpace.budget_prod
          (encFrame_mk_budget hh hi (hconst encBool true))
          (encFrame_mk_budget hpred hright (hconst encBool false))))
        (ComputableInSpace.budget_sumInr (hconst encBool true))))
    (ComputableInSpace.budget_ite (ComputableInSpace.budget_natIsZero hh)
      (ComputableInSpace.budget_sumInr (ComputableInSpace.budget_optionGetD false hbit))
      (ComputableInSpace.budget_sumInl (ComputableInSpace.budget_prod
        (encFrame_mk_budget hh hi (hconst encBool false))
        (encFrame_mk_budget hpred hleft (hconst encBool false)))))

/-- What a frame returns: a fresh frame the value of its node, and a frame that has received the
value `b` of a subtree the NAND of `b` and what is left to evaluate. -/
def val (w : List Bool) (c : Frame × Option Bool) : Bool :=
  match c.2 with
  | none => tree w c.1.height c.1.index
  | some b => if c.1.second then !b else !(b && tree w (c.1.height - 1) (2 * c.1.index + 1))

/-- The rank: the height first, then the stage of the frame. -/
def rank (c : Frame × Option Bool) : ℕ :=
  3 * c.1.height + match c.2 with
    | none => 2
    | some _ => if c.1.second then 0 else 1

/-- The frames that occur on `w`, for the tree of height `d`: a frame that has received a value
is an inner node, a fresh frame is in its first stage, and the node lies in the tree. -/
def Reach (d : ℕ) (c : Frame × Option Bool) : Prop :=
  (c.2.isSome → 1 ≤ c.1.height) ∧ (c.2 = none → c.1.second = false) ∧ c.1.height ≤ d ∧
    c.1.index < 2 ^ (d - c.1.height)

theorem length_encFrame_le {d : ℕ} {f : Frame} (hh : f.height ≤ d) (hi : f.index < 2 ^ d) :
    (encFrame f).length ≤ 4 * d + 6 := by
  have h₁ := length_encNat_le_of_lt_two_pow (hh.trans_lt Nat.lt_two_pow_self)
  have h₂ := length_encNat_le_of_lt_two_pow hi
  simp only [encFrame_apply, encFrameFields, length_encPair, encBool_apply, List.length_singleton]
  omega

theorem lt_two_pow_of_reach {d : ℕ} {c : Frame × Option Bool} (h : Reach d c) :
    c.1.index < 2 ^ d :=
  h.2.2.2.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

/-- The body on a reachable frame that calls: both frames are reachable and of smaller rank, and
the value of the frame is that of its resumption. -/
theorem body_call {d : ℕ} {w : List Bool} {c : Frame × Option Bool} {saved child : Frame}
    (hc : Reach d c) (hb : body (c, w) = .inl (saved, child)) :
    Reach d (child, none) ∧ Reach d (saved, some (val w (child, none))) ∧
      rank (child, none) < rank c ∧ rank (saved, some (val w (child, none))) < rank c ∧
      val w c = val w (saved, some (val w (child, none))) ∧
      saved.height = c.1.height ∧ saved.index = c.1.index ∧ child.height + 1 = c.1.height := by
  obtain ⟨⟨h, i, s⟩, o⟩ := c
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hc
  dsimp only at h₁ h₂ h₃ h₄
  have hpow : 2 ^ (d - (h - 1)) = 2 * 2 ^ (d - h) ∨ h = 0 := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · exact .inr rfl
    · exact .inl (by rw [show d - (h - 1) = d - h + 1 by omega, pow_succ, Nat.mul_comm])
  rcases o with _ | b
  · obtain rfl : s = false := h₂ rfl
    by_cases h0 : h = 0
    · simp [body, h0] at hb
    · simp only [body, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, h0, decide_false,
        Sum.inl.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      rcases hpow with hpow | hpow
      · refine ⟨⟨by simp, fun _ => rfl, by dsimp only; omega, by dsimp only; omega⟩,
          ⟨fun _ => by dsimp only; omega, by simp, h₃, h₄⟩, by simp [rank], by simp [rank],
          by simp [val, tree], rfl, rfl, rfl⟩
      · omega
  · have hpos := h₁ rfl
    cases s <;> cases b <;>
      simp only [body, Option.isSome_some, ↓reduceIte, Option.getD_some, Bool.false_eq_true,
        Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rcases hpow with hpow | hpow
    · refine ⟨⟨by simp, fun _ => rfl, by dsimp only; omega, by dsimp only; omega⟩,
        ⟨fun _ => hpos, by simp, h₃, h₄⟩, by simp [rank]; omega, by simp [rank],
        by simp [val], rfl, rfl, by dsimp only; omega⟩
    · omega

/-- The body on a reachable frame that returns: it returns the value of the frame. -/
theorem body_ret {d : ℕ} {w : List Bool} {c : Frame × Option Bool} {v : Bool} (hc : Reach d c)
    (hb : body (c, w) = .inr v) : val w c = v := by
  obtain ⟨⟨h, i, s⟩, o⟩ := c
  obtain ⟨h₁, h₂, -, -⟩ := hc
  dsimp only at h₁ h₂
  rcases o with _ | b
  · obtain rfl : s = false := h₂ rfl
    by_cases h0 : h = 0
    · subst h0
      simpa [body, val, tree] using hb
    · simp [body, h0] at hb
  · cases s <;> cases b <;> simp [body] at hb <;> simp [val, ← hb]

/-- **The NAND tree over a word** of the height of the binary logarithm of its length is
computable within space `O(log² n)`, by recursion on the tree. -/
theorem tree_inSpace :
    ComputableInSpace (fun w : List Bool => tree w (Nat.log2 w.length) 0) encBits encBool
      fun w => (Nat.log2 w.length + 1) ^ 2 := by
  -- the height of the tree: one less than the number of binary digits of the length
  have hsize : ComputableInSpace (fun w : List Bool => (encNat w.length).length) encBits encNat
      fun w => Nat.log2 (encBits w).length :=
    (computableInLogSpace_natBitLength.comp' computableInLogSpace_bitsLength).inSpace_of_length_log
      ⟨1, fun w => by
        simpa only [one_mul, encBits_apply] using
          length_encNat_le_log2 (length_encNat_le_self w.length)⟩
  have hheight : ComputableInSpace (fun w : List Bool => Nat.log2 w.length) encBits encNat
      fun w => Nat.log2 w.length :=
    ((ComputableInSpace.budget_natPred hsize).of_enc_eq fun w => by
      rw [Nat.log2_eq_size_sub_one, length_encNat_eq_size]).mono_le fun w => by
        rw [encBits_apply]
  have hrec := ComputableInSpace.recWith (encA := encBits) (encF := encFrame) (encB := encBool)
    (body := body) (init := fun w => ⟨Nat.log2 w.length, 0, false⟩)
    (S := fun w => Nat.log2 w.length)
    (B := fun w => (Nat.log2 w.length + 1) * (10 * Nat.log2 w.length + 20))
    val (fun _ => rank) (fun w c => (c.1.height + 1) * (10 * Nat.log2 w.length + 20))
    (fun w => Reach (Nat.log2 w.length))
    (encFrame_mk_budget hheight
      (ComputableInSpace.budget_const 0)
      (ComputableInSpace.budget_const false))
    body_inSpace
    (fun w => ⟨by simp, fun _ => rfl, le_rfl, by simp⟩)
    (fun w c saved child hc hb => by
      obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := body_call hc hb
      exact ⟨h₁, h₂, h₃, h₄, h₅⟩)
    (fun w c saved child hc hb => by
      obtain ⟨-, hs, -, -, -, hsh, hsi, hch⟩ := body_call hc hb
      have hlen := length_encFrame_le hs.2.2.1 (lt_two_pow_of_reach hs)
      dsimp only
      rw [hsh, ← hch]
      constructor <;> nlinarith)
    (fun w c v hc hb => body_ret hc hb)
    (fun w c hc => by
      have hlen := length_encFrame_le hc.2.2.1 (lt_two_pow_of_reach hc)
      have ho : (encOption encBool c.2).length ≤ 2 := by rcases c.2 with _ | b <;> simp
      simp only [budget, encConfig, length_encPair, encBits_apply]
      nlinarith)
    (fun w => le_rfl)
  exact hrec.weaken ⟨32, fun w => by
    simp only [encBits_apply]
    nlinarith [Nat.zero_le (Nat.log2 w.length)]⟩

/-- The value of the tree is decided in `DSPACE(log² n)`. -/
example : {w : List Bool | tree w (Nat.log2 w.length) 0 = true} ∈
    Cslib.Complexity.DSPACE encBits fun n => (Nat.log2 n + 1) ^ 2 :=
  Cslib.Complexity.setOf_mem_DSPACE_of_computableInSpace tree_inSpace fun _ => le_rfl

end SpaceRecursionTest
