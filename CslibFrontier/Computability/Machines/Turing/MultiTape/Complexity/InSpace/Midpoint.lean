/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.Savitch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Recursion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Context
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Tactic.Space

/-!
# The midpoint recursion in the space of its frames

Savitch's midpoint recursion `Cslib.Reachability.reach edge w d u v` asks whether `v` is reachable
from `u` within `2 ^ d` steps along edges between words of width `w`. It has depth `d` and a frame
holds a level and three words, so it runs in space `O((d + 1) * (w + log₂ d + 1))` plus the space
of one edge test. `Turing.MultiTapeTM.ComputableInSpace.reach` states this for an edge test that
is any certified function of two stored words and the read-only input: the edge test may read the
input, which is never copied.

The rule is an instance of `Turing.MultiTapeTM.ComputableInSpace.recWith`. A frame is a call
with the midpoint and the half being tried; the body answers a fresh call at level `0` with the
edge test, starts the first half at the word of zeros, moves from a successful first half to the
second, and from a failed half to the next midpoint by the binary counter
`Cslib.BitString.increment`. No stack, machine or run is described: the recursion is checked
against `Cslib.Reachability.reach` by the two equations of `recWith`.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.reach`: the midpoint recursion with an edge test of two
  stored words and the input, within the space of its frames and of one edge test.

## Implementation notes

The frames, the body and the value of a frame are private to this module.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
-/

namespace Cslib.Reachability.Midpoint

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Cslib.BitString (increment length_increment lsbValue lsbValue_lt lsbValue_increment
  lsbValue_injective lsbValue_replicate_false lsbValue_replicate_true mem_enumList)

/-- A frame of the midpoint recursion: the call at `level` from `src` to `dst`, with the midpoint
being tried, which is also the counter of the midpoints tried so far, and whether the second
half, from `mid` to `dst`, is being tried. -/
structure Frame where
  /-- The level of the call: it asks for a walk of at most `2 ^ level` steps. -/
  level : ℕ
  /-- The source of the call. -/
  src : List Bool
  /-- The target of the call. -/
  dst : List Bool
  /-- The midpoint being tried. -/
  mid : List Bool
  /-- Whether the second half is being tried. -/
  phase : Bool

/-- Binary level, the three words framed, and the phase bit, in field order. -/
private enc_structure encFrame : Frame where
  level : encNat, src : encBits, dst : encBits, mid : encBits, phase : encBool

variable {α : Type}

/-- **The answer of a frame**, from the frame, the value returned to it and the input.
* A fresh call at level `0` returns whether its target is its source or one edge away.
* A fresh call at a higher level calls its first half with the first midpoint, the word of zeros.
* A value `true` returned into the first half calls the second half; returned into the second
  half, the frame returns `true`.
* A value `false` advances the midpoint by the binary counter and calls the first half again;
  after the last midpoint the frame returns `false`. -/
def answer (edge : α → List Bool → List Bool → Bool) (w : α → ℕ)
    (p : (Frame × Option Bool) × α) : (Frame × Frame) ⊕ Bool :=
  if p.1.2.isSome then
    if p.1.2.getD false then
      if p.1.1.phase then .inr true
      else .inl (⟨p.1.1.level, p.1.1.src, p.1.1.dst, p.1.1.mid, true⟩,
        ⟨p.1.1.level - 1, p.1.1.mid, p.1.1.dst, [], false⟩)
    else if p.1.1.mid.all id then .inr false
    else .inl (⟨p.1.1.level, p.1.1.src, p.1.1.dst, increment p.1.1.mid, false⟩,
      ⟨p.1.1.level - 1, p.1.1.src, increment p.1.1.mid, [], false⟩)
  else if p.1.1.level = 0 then
    .inr (decide (p.1.1.src = p.1.1.dst) || edge p.2 p.1.1.src p.1.1.dst)
  else .inl (⟨p.1.1.level, p.1.1.src, p.1.1.dst, List.replicate (w p.2) false, false⟩,
    ⟨p.1.1.level - 1, p.1.1.src, List.replicate (w p.2) false, [], false⟩)

/-! ### What a frame returns -/

section Semantics

variable (edge : List Bool → List Bool → Bool) (W : ℕ)

/-- The midpoint `m` joins `u` and `v` at level `i`. -/
def via (i : ℕ) (u v m : List Bool) : Bool := reach edge W i u m && reach edge W i m v

/-- Some midpoint after the one with counter value `j` joins `u` and `v` at level `i`. -/
noncomputable def later (i : ℕ) (u v : List Bool) (j : ℕ) : Bool :=
  open Classical in
  decide (∃ m : List Bool, m.length = W ∧ j < lsbValue m ∧ via edge W i u v m = true)

/-- **What a frame returns**: a fresh call the value of the recursion, and a frame that has
received the value `b` of a half the value of the rest of its search over the midpoints. -/
noncomputable def val (c : Frame × Option Bool) : Bool :=
  match c.2 with
  | none => reach edge W c.1.level c.1.src c.1.dst
  | some b => (if c.1.phase then b else b && reach edge W (c.1.level - 1) c.1.mid c.1.dst) ||
      later edge W (c.1.level - 1) c.1.src c.1.dst (lsbValue c.1.mid)

/-- The rank of a frame: its level first, then the midpoints left, then the half. -/
def rank (c : Frame × Option Bool) : ℕ :=
  (2 * 2 ^ W + 2) * c.1.level + match c.2 with
    | none => 2 * 2 ^ W + 1
    | some _ => 2 * (2 ^ W - 1 - lsbValue c.1.mid) + if c.1.phase then 0 else 1

/-- The frames that occur at depth at most `D`: the endpoints have width `W`, and a frame that
has received a value is at a positive level with a midpoint of width `W`. -/
def Reach (D : ℕ) (c : Frame × Option Bool) : Prop :=
  c.1.level ≤ D ∧ c.1.src.length = W ∧ c.1.dst.length = W ∧ c.1.mid.length ≤ W ∧
    (c.2.isSome → 1 ≤ c.1.level ∧ c.1.mid.length = W)

variable {edge W}

/-- A call at a positive level tries the word of zeros and then the later midpoints. -/
theorem reach_succ_eq (i : ℕ) (u v : List Bool) :
    reach edge W (i + 1) u v =
      (via edge W i u v (List.replicate W false) || later edge W i u v 0) := by
  rw [Bool.eq_iff_iff]
  simp only [reach, List.any_eq_true, mem_enumList, Bool.or_eq_true, later, decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, h⟩
    rcases Nat.eq_zero_or_pos (lsbValue m) with h0 | h0
    · obtain rfl : m = List.replicate W false :=
        lsbValue_injective (by simp [hm]) (by rw [h0, lsbValue_replicate_false])
      exact .inl h
    · exact .inr ⟨m, hm, h0, h⟩
  · rintro (h | ⟨m, hm, -, h⟩)
    · exact ⟨_, List.length_replicate, h⟩
    · exact ⟨m, hm, h⟩

/-- A word that is not all ones is below the largest counter value. -/
theorem lsbValue_succ_lt_of_not_all {m : List Bool} (h : m.all id = false) :
    lsbValue m + 1 < 2 ^ m.length := by
  by_contra hlt
  have h₁ := lsbValue_lt m
  have h₂ := lsbValue_replicate_true m.length
  have hm : m = List.replicate m.length true :=
    lsbValue_injective (by simp) (by omega)
  rw [hm] at h
  simp at h

/-- After the last midpoint none is left. -/
theorem later_eq_false_of_all (i : ℕ) (u v : List Bool) {m : List Bool} (hm : m.length = W)
    (h : m.all id = true) : later edge W i u v (lsbValue m) = false := by
  simp only [later, decide_eq_false_iff_not, not_exists, not_and]
  intro m' hm' hlt
  have h₁ := lsbValue_lt m'
  have h₂ := lsbValue_replicate_true W
  obtain rfl : m = List.replicate W true := by
    rw [← hm]
    exact List.eq_replicate_iff.mpr ⟨rfl, fun b hb => by simpa using List.all_eq_true.mp h b hb⟩
  rw [hm'] at h₁
  omega

/-- After a midpoint that is not the last, the next one is tried, and then the later ones. -/
theorem later_eq_of_not_all (i : ℕ) (u v : List Bool) {m : List Bool} (hm : m.length = W)
    (h : m.all id = false) :
    later edge W i u v (lsbValue m) = (via edge W i u v (increment m) ||
      later edge W i u v (lsbValue (increment m))) := by
  have hinc := lsbValue_increment m (lsbValue_succ_lt_of_not_all h)
  rw [Bool.eq_iff_iff]
  simp only [later, Bool.or_eq_true, decide_eq_true_eq, hinc]
  constructor
  · rintro ⟨m', hm', hlt, h'⟩
    rcases (Nat.succ_le_of_lt hlt).eq_or_lt with heq | hgt
    · obtain rfl : m' = increment m :=
        lsbValue_injective (by simp [hm, hm']) (by rw [hinc]; exact heq.symm)
      exact .inl h'
    · exact .inr ⟨m', hm', hgt, h'⟩
  · rintro (h' | ⟨m', hm', hlt, h'⟩)
    · exact ⟨_, by simp [hm], by omega, h'⟩
    · exact ⟨m', hm', by omega, h'⟩

end Semantics

/-! ### The two equations of the recursion -/

section Equations

variable {edge : α → List Bool → List Bool → Bool} {w : α → ℕ} {a : α} {D : ℕ}
  {c : Frame × Option Bool}

/-- **The answer of a reachable frame that calls**: both frames are reachable and of smaller rank,
the frame returns what its resumption returns, the callee is one level down and the resumption at
the same level. -/
theorem answer_call {saved child : Frame} (hc : Reach (w a) D c)
    (hb : answer edge w (c, a) = .inl (saved, child)) :
    Reach (w a) D (child, none) ∧
      Reach (w a) D (saved, some (val (edge a) (w a) (child, none))) ∧
      rank (w a) (child, none) < rank (w a) c ∧
      rank (w a) (saved, some (val (edge a) (w a) (child, none))) < rank (w a) c ∧
      val (edge a) (w a) c = val (edge a) (w a) (saved, some (val (edge a) (w a) (child, none))) ∧
      child.level + 1 = c.1.level ∧ saved.level = c.1.level := by
  obtain ⟨⟨l, u, v, m, ph⟩, o⟩ := c
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hc
  unfold answer at hb
  dsimp only at h₁ h₂ h₃ h₄ h₆ hb
  generalize w a = W at *
  generalize edge a = e at *
  have hpow : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  rcases o with _ | b
  · by_cases h0 : l = 0
    · simp [h0] at hb
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, h0,
        Sum.inl.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
      refine ⟨⟨by dsimp only; omega, h₂, List.length_replicate, Nat.zero_le _, by simp⟩,
        ⟨h₁, h₂, h₃, by simp, fun _ => ⟨Nat.succ_le_succ (Nat.zero_le _), by simp⟩⟩,
        ?_, ?_, ?_, rfl, rfl⟩
      · simp only [rank, Nat.add_sub_cancel, Nat.mul_succ]
        omega
      · simp only [rank, lsbValue_replicate_false, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp [val, via, reach_succ_eq]
  · obtain ⟨hl, hm⟩ := h₆ rfl
    obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
    have hj := lsbValue_lt m
    rw [hm] at hj
    cases b
    · by_cases hall : m.all id = true
      · simp [hall] at hb
      · rw [Bool.not_eq_true] at hall
        simp only [Option.isSome_some, ↓reduceIte, Option.getD_some, Bool.false_eq_true,
          hall, Sum.inl.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have hlt := lsbValue_succ_lt_of_not_all hall
        have hinc := lsbValue_increment m hlt
        rw [hm] at hlt
        have hlen : (increment m).length = W := by rw [length_increment, hm]
        refine ⟨⟨by dsimp only; omega, h₂, hlen, Nat.zero_le _, by simp⟩,
          ⟨h₁, h₂, h₃, hlen.le, fun _ => ⟨by omega, hlen⟩⟩, ?_, ?_, ?_, rfl, rfl⟩
        · simp only [rank, Nat.add_sub_cancel, Nat.mul_succ]
          omega
        · simp only [rank, hinc, Bool.false_eq_true, ↓reduceIte]
          cases ph <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        · simp only [val, Nat.add_sub_cancel, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, later_eq_of_not_all i u v hm hall, via]
          cases ph <;> simp
    · cases ph
      · simp only [Option.isSome_some, ↓reduceIte, Option.getD_some, Bool.false_eq_true,
          Sum.inl.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        refine ⟨⟨by dsimp only; omega, hm, h₃, Nat.zero_le _, by simp⟩,
          ⟨h₁, h₂, h₃, h₄, fun _ => ⟨by omega, hm⟩⟩, ?_, ?_, ?_, rfl, rfl⟩
        · simp only [rank, Nat.add_sub_cancel, Nat.mul_succ, Bool.false_eq_true, ↓reduceIte]
          omega
        · simp only [rank, ↓reduceIte, Bool.false_eq_true]
          omega
        · simp [val]
      · simp at hb

/-- **The answer of a reachable frame that returns** is the value of the frame. -/
theorem answer_ret {r : Bool} (hc : Reach (w a) D c) (hb : answer edge w (c, a) = .inr r) :
    val (edge a) (w a) c = r := by
  obtain ⟨⟨l, u, v, m, ph⟩, o⟩ := c
  obtain ⟨-, -, -, -, h₆⟩ := hc
  dsimp only at h₆ hb
  rcases o with _ | b
  · by_cases h0 : l = 0
    · subst h0
      simpa [answer, val, reach] using hb
    · simp [answer, h0] at hb
  · obtain ⟨-, hm⟩ := h₆ rfl
    cases b
    · by_cases hall : m.all id = true
      · have := later_eq_false_of_all (edge := edge a) (l - 1) u v hm hall
        cases ph <;> simpa [answer, val, hall, this] using hb
      · simp [answer, hall] at hb
    · cases ph
      · simp [answer] at hb
      · simpa [answer, val] using hb

/-- A reachable frame is encoded within the width of its words and the size of the depth. -/
theorem length_encFrame_le (hc : Reach (w a) D c) :
    (encFrame c.1).length ≤ 6 * w a + 2 * Nat.log2 D + 12 := by
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hc
  have hl := length_encNat_le_log2 h₁
  simp only [encFrame_apply, encFrameFields, length_encPair, encBits_apply, encBool_apply,
    List.length_singleton]
  omega

end Equations

/-! ### The body within its budget -/

section Certificate

variable {encA : α ↪ List Bool} {edge : α → List Bool → List Bool → Bool} {w : α → ℕ}
  {S : α → ℕ} {T : (List Bool × List Bool) × α → ℕ}

/-- The first frame, within the budget of its parts. -/
theorem start_inSpace {d : α → ℕ} {u v : α → List Bool}
    (hd : ComputableInSpace d encA encNat S) (hu : ComputableInSpace u encA encBits S)
    (hv : ComputableInSpace v encA encBits S) :
    ComputableInSpace (fun a => (⟨d a, u a, v a, [], false⟩ : Frame)) encA encFrame S := by
  space

/-- The budget of the body: the frame in control, the width, one edge test on the endpoints of
the frame, and the logarithm of the length of the input. -/
abbrev answerBudget (encA : α ↪ List Bool) (S : α → ℕ) (T : (List Bool × List Bool) × α → ℕ)
    (p : (Frame × Option Bool) × α) : ℕ :=
  (encPair encFrame (encOption encBool) p.1).length + S p.2 + T ((p.1.1.src, p.1.1.dst), p.2) +
    Nat.log2 (encA p.2).length

/-- **The answer of a frame within its budget.** The leaves are the registers, the width, a
function of the input alone, and the edge test on the endpoints of the frame; `space` composes
the rest. -/
theorem answer_inSpace (hw : ComputableInSpace w encA encUnary S)
    (hedge : ComputableInSpace (fun q : (List Bool × List Bool) × α => edge q.2 q.1.1 q.1.2)
      (encPair (encPair encBits encBits) encA) encBool T) :
    ComputableInSpace (answer edge w) (encPair (encPair encFrame (encOption encBool)) encA)
      (encSum (encPair encFrame encFrame) encBool) (answerBudget encA S T) := by
  have hctx : CoversContext (encPair encFrame (encOption encBool)) encA (answerBudget encA S T) :=
    .of_le fun p => by dsimp only [answerBudget]; omega
  have hreg := budget_registers hctx
  have hwidth := budget_ofInput hw hctx (.of_le fun p => by dsimp only [answerBudget]; omega)
  have hframe : ComputableInLogSpace
      (fun p : (Frame × Option Bool) × α =>
        (p.1.1.level, p.1.1.src, p.1.1.dst, p.1.1.mid, p.1.1.phase))
      (encPair (encPair encFrame (encOption encBool)) encA) encFrameFields :=
    (ComputableInLogSpace.of_eq (f := fun f : Frame => (f.level, f.src, f.dst, f.mid, f.phase))
      fun f => (encFrame_apply f).symm).comp'
      ((ComputableInLogSpace.fst encFrame _).comp' (.fst _ encA))
  have hedge' := budget_subst hedge (hframe.snd'.fst'.pair hframe.snd'.snd'.fst') hctx
    (.of_le fun p => by dsimp only [answerBudget]; omega)
  space [answer]

end Certificate

end Cslib.Reachability.Midpoint

public section

namespace Turing.MultiTapeTM.ComputableInSpace

open Cslib.Reachability Cslib.Reachability.Midpoint

variable {α : Type} {encA : α ↪ List Bool}


/-- **The midpoint recursion in the space of its frames.** Let the edge test be any function of
two stored words and the input, computable within a budget `T` that is at most `E a` on words of
the width `w a`, and let the width, the depth and the endpoints be computable from the input
within `S`, the width in unary. Then Savitch's recursion `Cslib.Reachability.reach` at depth
`d a` between the endpoints is computable within space
`O(S + (d + 1) * (w + log₂ d + 1) + E + log n)` on inputs of length `n`: a chain of at most
`d + 1` frames, each holding a level and three words, and one edge test at a time. The constant
does not depend on the depth, and the input is read in place. -/
theorem reach {edge : α → List Bool → List Bool → Bool} {w d : α → ℕ} {u v : α → List Bool}
    {S E : α → ℕ} {T : (List Bool × List Bool) × α → ℕ}
    (hw : ComputableInSpace w encA encUnary S) (hd : ComputableInSpace d encA encNat S)
    (hu : ComputableInSpace u encA encBits S) (hv : ComputableInSpace v encA encBits S)
    (hedge : ComputableInSpace (fun q : (List Bool × List Bool) × α => edge q.2 q.1.1 q.1.2)
      (encPair (encPair encBits encBits) encA) encBool T)
    (hT : ∀ a x y, x.length = w a → y.length = w a → T ((x, y), a) ≤ E a)
    (hlen : ∀ a, (u a).length = w a ∧ (v a).length = w a) :
    ComputableInSpace (fun a => Cslib.Reachability.reach (edge a) (w a) (d a) (u a) (v a))
      encA encBool fun a =>
        S a + (d a + 1) * (w a + Nat.log2 (d a) + 1) + E a + Nat.log2 (encA a).length := by
  have hbody := answer_inSpace hw hedge
  have hinit := start_inSpace hd hu hv
  have hrec := recWith (encA := encA) (encF := encFrame) (encB := encBool)
    (B := fun a => (d a + 1) * (12 * w a + 4 * Nat.log2 (d a) + 30) + S a + E a +
      Nat.log2 (encA a).length)
    (fun a => val (edge a) (w a)) (fun a => rank (w a))
    (fun a c => (c.1.level + 1) * (12 * w a + 4 * Nat.log2 (d a) + 30) + S a + E a +
      Nat.log2 (encA a).length)
    (fun a => Reach (w a) (d a)) hinit hbody
    (fun a => ⟨le_rfl, (hlen a).1, (hlen a).2, Nat.zero_le _, by simp⟩)
    (fun a c saved child hc hb => by
      obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := answer_call hc hb
      exact ⟨h₁, h₂, h₃, h₄, h₅⟩)
    (fun a c saved child hc hb => by
      obtain ⟨-, hs, -, -, -, hcl, hsl⟩ := answer_call hc hb
      have hsize := length_encFrame_le hs
      dsimp only at hsize ⊢
      rw [hsl, ← hcl]
      constructor <;> nlinarith)
    (fun a c r hc hb => answer_ret hc hb)
    (fun a c hc => by
      have hsize := length_encFrame_le hc
      have ho : (encOption encBool c.2).length ≤ 2 := by rcases c.2 with _ | b <;> simp
      have hedge := hT a c.1.src c.1.dst hc.2.1 hc.2.2.1
      simp only [answerBudget, length_encPair]
      nlinarith)
    (fun a => le_rfl)
  refine (hrec.of_enc_eq fun _ => rfl).weaken ⟨32, fun a => ?_⟩
  dsimp only
  nlinarith

end Turing.MultiTapeTM.ComputableInSpace
