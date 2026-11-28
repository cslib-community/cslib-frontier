/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives
import CslibFrontier.Tactic.EncLen

/-!
# Case analysis on a component, within given bounds

Case analysis on the second component of a pair, when that component is a tagged sum
(`Turing.MultiTapeTM.encSum`) or an option (`Turing.MultiTapeTM.encOption`). Each branch need
only be computable on its own case, and only the branch taken is charged, plus the length of the
encoded input. No default values of the component types are needed: the branches run on the
inputs of their case only.

## Main results

* `Turing.MultiTapeTM.ComputableInO.sumElimSnd`: case analysis on a sum component.
* `Turing.MultiTapeTM.ComputableInO.optionElimSnd`: case analysis on an option component.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

variable {π α β ε : Type} {encP : π ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encE : ε ↪ List Bool}

/-- A function whose encoded value is obtained from the encoded input by keeping its leading frame
and dropping `k` symbols after it, in linear time. -/
private lemma keepFrame_drop {σ : Type} {encS : σ ↪ List Bool} {h : σ → π × α} (k : ℕ)
    (hh : ∀ s, ∃ u, encS s = frame (encP (h s).1) ++ u ∧ encA (h s).2 = u.drop k) :
    ComputableInO h encS (encPair encP encA) (fun s => (encS s).length)
      (fun s => (encS s).length) := by
  have hlen : ∀ s, (encP (h s).1).length + (encA (h s).2).length ≤ (encS s).length := fun s => by
    obtain ⟨u, hs, hu⟩ := hh s
    rw [hs, hu, List.length_append, length_frame, List.length_drop]
    omega
  have h₁ : ComputableInO (fun s => (h s).1) encS (encFramed encP)
      (fun s => (encS s).length) (fun s => (encS s).length) := by
    have hu : ComputableInO (fun s => (h s).1) encS encP (fun s => (encS s).length)
        (fun s => (encS s).length) :=
      of_linear (.of_unframe fun s => by
        obtain ⟨u, hs, -⟩ := hh s
        rw [hs, unframe_frame_append])
    refine ((of_linear (.of_frame (f := fun x : π => x) (encIn := encP)
      (encMid := encFramed encP) fun _ => rfl)).comp hu).mono 2 (fun s => ?_) (fun s => ?_) <;>
    · have := hlen s
      omega
  -- the word after the frame, then `k` symbols dropped
  have hd : ComputableInO (fun s => dropFrame (encS s)) encS encBits
      (fun s => (encS s).length) (fun s => (encS s).length) :=
    of_linear (.of_dropFrame fun s => rfl)
  have hdrop : ∀ k : ℕ, ComputableInO (fun s => (dropFrame (encS s)).drop k) encS encBits
      (fun s => (encS s).length) (fun s => (encS s).length) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      refine (((of_linear (.of_tail (f := List.tail) (encIn := encBits) (encMid := encBits)
        fun _ => rfl)).comp ih).of_enc_eq (g := fun s => (dropFrame (encS s)).drop (k + 1))
        fun s => by simp [encBits]).mono 2 (fun s => ?_) (fun s => ?_) <;>
      · have : ((dropFrame (encS s)).drop k).length ≤ (encS s).length := by
          obtain ⟨u, hs, -⟩ := hh s
          rw [hs, dropFrame_frame_append, List.length_drop, List.length_append]
          omega
        simp only [encBits, Function.Embedding.refl_apply]
        omega
  have h₂ : ComputableInO (fun s => (h s).2) encS encA (fun s => (encS s).length)
      (fun s => (encS s).length) :=
    (hdrop k).of_enc_eq fun s => by
      obtain ⟨u, hs, hu⟩ := hh s
      rw [hu, hs, dropFrame_frame_append]
      rfl
  exact (h₁.append h₂ fun s => rfl).mono 2 (fun s => by omega) (fun s => by omega)

/-- **Case analysis on a sum component.** If `f` is computable on the left case and `g` on the
right case, so is the case analysis, within the bounds of the branch taken plus the length of the
encoded input. -/
theorem sumElimSnd {f : π × α → ε} {g : π × β → ε} {Tf Sf : π × α → ℕ}
    {Tg Sg : π × β → ℕ}
    (hf : ComputableInO f (encPair encP encA) encE Tf Sf)
    (hg : ComputableInO g (encPair encP encB) encE Tg Sg) :
    ComputableInO
      (fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b)))
      (encPair encP (encSum encA encB)) encE
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Tf (p.1, a)) (fun b => Tg (p.1, b)))
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Sf (p.1, a)) (fun b => Sg (p.1, b))) := by
  set enc := encPair encP (encSum encA encB)
  set F := fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b))
  -- the test
  have htest : ComputableInO (fun p : π × (α ⊕ β) => p.2.isLeft) enc encBool
      (fun p => (enc p).length) (fun p => (enc p).length) := by
    refine ((ComputableInO.isLeft_deg encA encB).inO_one.comp
      (snd encP (encSum encA encB))).mono 2 (fun p => ?_) (fun p => ?_) <;>
    · enc_len [enc]
  -- the two branches, on their cases
  let L : {p : π × (α ⊕ β) // p.2.isLeft = true} → π × α :=
    fun p => (p.val.1, p.val.2.getLeft (by simpa using p.property))
  let R : {p : π × (α ⊕ β) // p.2.isLeft = false} → π × β :=
    fun p => (p.val.1, p.val.2.getRight (by simpa using p.property))
  have hL := keepFrame_drop (encP := encP) (encA := encA)
    (encS := (Function.Embedding.subtype _).trans enc) (h := L) 1
    fun ⟨⟨x, s⟩, hs⟩ => by
      cases s with
      | inl a => exact ⟨false :: encA a, by simp [enc, L], rfl⟩
      | inr b => simp at hs
  have hR := keepFrame_drop (encP := encP) (encA := encB)
    (encS := (Function.Embedding.subtype _).trans enc) (h := R) 1
    fun ⟨⟨x, s⟩, hs⟩ => by
      cases s with
      | inl a => simp at hs
      | inr b => exact ⟨true :: encB b, by simp [enc, R], rfl⟩
  obtain ⟨c₀, ⟨k₀, Q₀, _, tm₀, h₀⟩, -⟩ := Internal.NormalForm.inO htest
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := Internal.NormalForm.inO (hf.comp hL)
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := Internal.NormalForm.inO (hg.comp hR)
  let Tl : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun a => Tf (p.1, a)) (fun _ => 0)
  let Sl : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun a => Sf (p.1, a)) (fun _ => 0)
  let Tr : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun _ => 0) (fun b => Tg (p.1, b))
  let Sr : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun _ => 0) (fun b => Sg (p.1, b))
  obtain ⟨k, K, Q, _, tm, h⟩ := Internal.conditional h₀ (f := F) (g := F)
    (tf := fun p => c₁ * ((enc p).length + Tl p + 1))
    (sf := fun p => c₁ * ((enc p).length + Sl p + 1))
    (tg := fun p => c₂ * ((enc p).length + Tr p + 1))
    (sg := fun p => c₂ * ((enc p).length + Sr p + 1))
    (fun ⟨⟨x, s⟩, hs⟩ => by
      cases s with
      | inl a => exact (h₁ ⟨(x, .inl a), hs⟩).mono le_rfl le_rfl
      | inr b => simp at hs)
    (fun ⟨⟨x, s⟩, hs⟩ => by
      cases s with
      | inr b => exact (h₂ ⟨(x, .inr b), hs⟩).mono le_rfl le_rfl
      | inl a => simp at hs)
  simp only [ite_self] at h
  refine of_bounds ⟨K, Q, inferInstance, tm, fun p => (h p).computesInTimeAndSpace⟩
    (c₀ + c₁ + c₂ + k + 1) (fun p => ?_) (fun p => ?_) (fun p => ?_)
  · obtain ⟨x, s⟩ := p
    cases s <;> simp only [Tl, Tr, Sum.isLeft_inl, Sum.isLeft_inr, Sum.elim_inl, Sum.elim_inr,
      ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, s⟩ := p
    cases s <;> simp only [Sl, Sr, Sum.isLeft_inl, Sum.isLeft_inr, Sum.elim_inl, Sum.elim_inr,
      ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, a | b⟩ := p
    · have h := l₁ ⟨(x, .inl a), rfl⟩
      simp only [Function.comp_apply, L, Sum.getLeft_inl, Function.Embedding.trans_apply,
        Function.Embedding.coe_subtype, F, Sum.elim_inl] at h ⊢
      nlinarith
    · have h := l₂ ⟨(x, .inr b), rfl⟩
      simp only [Function.comp_apply, R, Sum.getRight_inr, Function.Embedding.trans_apply,
        Function.Embedding.coe_subtype, F, Sum.elim_inr] at h ⊢
      nlinarith

/-- **Case analysis on an option component.** If `f` is computable on the first component in the
`none` case and `g` on the pair in the `some` case, so is the case analysis, within the bounds of
the branch taken plus the length of the encoded input. -/
theorem optionElimSnd {f : π → ε} {g : π × α → ε} {Tf Sf : π → ℕ} {Tg Sg : π × α → ℕ}
    (hf : ComputableInO f encP encE Tf Sf)
    (hg : ComputableInO g (encPair encP encA) encE Tg Sg) :
    ComputableInO (fun p : π × Option α => p.2.elim (f p.1) (fun a => g (p.1, a)))
      (encPair encP (encOption encA)) encE
      (fun p => (encPair encP (encOption encA) p).length +
        p.2.elim (Tf p.1) (fun a => Tg (p.1, a)))
      (fun p => (encPair encP (encOption encA) p).length +
        p.2.elim (Sf p.1) (fun a => Sg (p.1, a))) := by
  set enc := encPair encP (encOption encA)
  set F := fun p : π × Option α => p.2.elim (f p.1) (fun a => g (p.1, a))
  -- the test
  have htest : ComputableInO (fun p : π × Option α => p.2.isSome) enc encBool
      (fun p => (enc p).length) (fun p => (enc p).length) := by
    have he : ComputableInO (fun p : π × Option α => p.2.isNone) enc encBool
        (fun p => (enc p).length) (fun p => (enc p).length) := by
      have hd : ComputableInO (fun p : π × Option α => dropFrame (enc p)) enc encBits
          (fun p => (enc p).length) (fun p => (enc p).length) :=
        of_linear (.of_dropFrame fun p => rfl)
      refine ((of_linear (.of_isEmpty (f := List.isEmpty) (encIn := encBits) fun _ => rfl)).comp
        hd).of_enc_eq (fun p => ?_) |>.mono 2 (fun p => ?_) (fun p => ?_)
      · obtain ⟨x, _ | a⟩ := p <;> simp [enc, dropFrame_frame_append]
      all_goals
        enc_len [enc, encPair_apply, dropFrame_frame_append, encBits, Function.Embedding.refl_apply]
    refine ((ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
      Bool.not).inO_one.comp
      he).of_enc_eq (fun p => ?_) |>.mono 2 (fun p => ?_) (fun p => ?_)
    · obtain ⟨x, _ | a⟩ := p <;> rfl
    all_goals simp only [encBool_apply, List.length_singleton]; omega
  -- the two branches, on their cases
  let N : {p : π × Option α // p.2.isSome = false} → π := fun p => p.val.1
  let S : {p : π × Option α // p.2.isSome = true} → π × α :=
    fun p => (p.val.1, p.val.2.get p.property)
  have hN : ComputableInO N ((Function.Embedding.subtype _).trans enc) encP
      (fun s => ((Function.Embedding.subtype _).trans enc s).length)
      (fun s => ((Function.Embedding.subtype _).trans enc s).length) :=
    of_linear (.of_unframe fun ⟨⟨x, o⟩, _⟩ => by simp [enc, N, unframe_frame_append])
  have hS := keepFrame_drop (encP := encP) (encA := encA)
    (encS := (Function.Embedding.subtype _).trans enc) (h := S) 1
    fun ⟨⟨x, o⟩, ho⟩ => by
      cases o with
      | none => simp at ho
      | some a => exact ⟨true :: encA a, by simp [enc, S], rfl⟩
  obtain ⟨c₀, ⟨k₀, Q₀, _, tm₀, h₀⟩, -⟩ := Internal.NormalForm.inO htest
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := Internal.NormalForm.inO (hg.comp hS)
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := Internal.NormalForm.inO (hf.comp hN)
  let Ts : π × Option α → ℕ := fun p => p.2.elim 0 (fun a => Tg (p.1, a))
  let Ss : π × Option α → ℕ := fun p => p.2.elim 0 (fun a => Sg (p.1, a))
  let Tn : π × Option α → ℕ := fun p => p.2.elim (Tf p.1) (fun _ => 0)
  let Sn : π × Option α → ℕ := fun p => p.2.elim (Sf p.1) (fun _ => 0)
  obtain ⟨k, K, Q, _, tm, h⟩ := Internal.conditional h₀ (f := F) (g := F)
    (tf := fun p => c₁ * ((enc p).length + Ts p + 1))
    (sf := fun p => c₁ * ((enc p).length + Ss p + 1))
    (tg := fun p => c₂ * ((enc p).length + Tn p + 1))
    (sg := fun p => c₂ * ((enc p).length + Sn p + 1))
    (fun ⟨⟨x, o⟩, ho⟩ => by
      cases o with
      | some a => exact (h₁ ⟨(x, some a), ho⟩).mono le_rfl le_rfl
      | none => simp at ho)
    (fun ⟨⟨x, o⟩, ho⟩ => by
      cases o with
      | none => exact (h₂ ⟨(x, none), ho⟩).mono le_rfl le_rfl
      | some a => simp at ho)
  simp only [ite_self] at h
  refine of_bounds ⟨K, Q, inferInstance, tm, fun p => (h p).computesInTimeAndSpace⟩
    (c₀ + c₁ + c₂ + k + 1) (fun p => ?_) (fun p => ?_) (fun p => ?_)
  · obtain ⟨x, o⟩ := p
    cases o <;> simp only [Ts, Tn, Option.isSome_none, Option.isSome_some, Option.elim_none,
      Option.elim_some, ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, o⟩ := p
    cases o <;> simp only [Ss, Sn, Option.isSome_none, Option.isSome_some, Option.elim_none,
      Option.elim_some, ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, _ | a⟩ := p
    · have h := l₂ ⟨(x, none), rfl⟩
      simp only [Function.comp_apply, N, Function.Embedding.trans_apply,
        Function.Embedding.coe_subtype, F, Option.elim_none] at h ⊢
      nlinarith
    · have h := l₁ ⟨(x, some a), rfl⟩
      simp only [Function.comp_apply, S, Option.get_some, Function.Embedding.trans_apply,
        Function.Embedding.coe_subtype, F, Option.elim_some] at h ⊢
      nlinarith

end Turing.MultiTapeTM.ComputableInO
