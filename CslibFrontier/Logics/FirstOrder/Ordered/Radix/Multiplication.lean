/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Radix.Decode
import CslibFrontier.Tactic.FirstOrder

/-!
# Native multiplication of radix words

A fixed number of Horner rounds multiplies a long word by another fixed-length word.
Each round first multiplies the original word by one digit, then shifts the accumulating
product and adds that contribution. This handles leading zero multiplier digits without
asking an unnecessarily large shift of the original word to fit.

## Main definitions

* `Cslib.Logic.FO.Ordered.Radix.multiply`: exact multiplication of fixed-length words.

## Main results

* `Cslib.Logic.FO.Ordered.Radix.realize_multiply`: ordinary word-product semantics,
  with overflow rejected by the affine checks.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Exercise 1.33(3): this is an explicit
  radix implementation of the tuple arithmetic suggested there.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.Radix

open FirstOrder Language Structure

/-- Fixed-length Horner multiplication, using two exact affine checks per multiplier digit. -/
noncomputable def multiply (L : Language) {α : Type*} {d m : ℕ}
    (B : (language L).Term α) (x : Fin d → (language L).Term α)
    (y : Fin m → (language L).Term α) (z : Fin d → (language L).Term α) :
    (language L).Formula α :=
  digits L B x ⊓ digits L B y ⊓ digits L B z ⊓
  Formula.iExs ((Fin (m + 1) ⊕ Fin m) × Fin d)
    ((Formula.iInf fun j : Fin d =>
        (Term.var (.inr (.inl 0, j))).equal ((z j).relabel Sum.inl)) ⊓
     (Formula.iInf fun j : Fin d =>
        (Term.var (.inr (.inl (Fin.last m), j))).equal (zero L)) ⊓
     Formula.iInf fun i : Fin m =>
       affine L (B.relabel Sum.inl) ((y i).relabel Sum.inl)
         (fun j => (x j).relabel Sum.inl) (fun _ => zero L)
         (fun j => .var (.inr (.inr i, j))) ⊓
       affine L (B.relabel Sum.inl) (B.relabel Sum.inl)
         (fun j => .var (.inr (.inl i.succ, j)))
         (fun j => .var (.inr (.inr i, j)))
         (fun j => .var (.inr (.inl i.castSucc, j))))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- When `1 < B` and `B ^ 3` fits in the universe, `multiply L B x y z` holds exactly when `x`,
`y` and `z` are radix-`B` words and the value of `z` is the product of those of `x` and `y`. -/
@[fo_realize]
theorem realize_multiply {d m : ℕ} (B : (language L).Term α)
    (x : Fin d → (language L).Term α) (y : Fin m → (language L).Term α)
    (z : Fin d → (language L).Term α) (v : α → Fin n)
    (hB : 1 < (B.realize v).val) (hBn : (B.realize v).val ^ 3 < n) :
    (multiply L B x y z).Realize v ↔
      (∀ i, ((x i).realize v).val < (B.realize v).val) ∧
      (∀ i, ((y i).realize v).val < (B.realize v).val) ∧
      (∀ i, ((z i).realize v).val < (B.realize v).val) ∧
      Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((x i).realize v).val) *
          Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((y i).realize v).val) =
        Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((z i).realize v).val) := by
  have ha (w : ((Fin (m + 1) ⊕ Fin m) × Fin d) → Fin n) b' x' y' z' :=
    realize_affine (d := d) (B.relabel Sum.inl) b' x' y' z' (Sum.elim v w)
      (by fo_simp; exact hB) (by fo_simp; exact hBn)
  fo_simp [multiply, ha, Fin.ext_iff, List.ofFn_const,
    Nat.ofDigits_replicate_zero, Nat.add_zero, and_assoc]
  constructor
  · rintro ⟨hx, hy, hz, w, hw0, hwe, hs⟩
    refine ⟨hx, hy, hz, ?_⟩
    let X := Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((x i).realize v).val)
    let R := fun i : Fin (m + 1) => Nat.ofDigits (B.realize v).val
      (List.ofFn fun j => (w (.inl i, j)).val)
    have he : R (Fin.last m) = 0 := by simp [R, hwe]
    have hr : ∀ i : Fin m, R i.castSucc =
        X * ((y i).realize v).val + (B.realize v).val * R i.succ := by
      intro i
      rcases hs i with ⟨_, _, _, _, ht, _, _, _, _, hi⟩
      dsimp [X, R] at *
      rw [← ht] at hi
      simpa only [Nat.mul_comm, Nat.add_comm] using hi.symm
    have hval := Nat.ofDigits_eq_of_quotients
      (fun i => X * ((y i).realize v).val) R he hr
    change X * _ = _
    rw [Nat.mul_ofDigits, List.map_ofFn]
    exact hval.trans (by simp only [R, hw0])
  · rintro ⟨hx, hy, hz, he⟩
    let X := Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((x i).realize v).val)
    let Y := Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((y i).realize v).val)
    have hZ := Nat.ofDigits_ofFn_lt hB _ hz
    have hXY : X * Y < (B.realize v).val ^ d := by simpa only [X, Y, he] using hZ
    obtain ⟨q, hq0, hqe, hqb, hqs⟩ := Nat.exists_radix_quotients (Nat.le_of_lt hB)
      (fun i => ((y i).realize v).val)
    choose R hR hRv using fun i : Fin (m + 1) =>
      exists_word (B.realize v) (lt_of_le_of_lt (Nat.mul_le_mul_left X (hqb i)) hXY)
    choose T hT hTv using fun i : Fin m => exists_word (B.realize v)
      (lt_of_le_of_lt (Nat.mul_le_mul_left X (show ((y i).realize v).val ≤ Y by
        have := hqs i; have := hqb i.castSucc; dsimp [Y]; lia)) hXY)
    refine ⟨hx, hy, hz, (fun p => Sum.elim (fun i => R i p.2) (fun i => T i p.2) p.1),
      ?_, ?_, ?_⟩
    · exact congrFun (Nat.ofDigits_ofFn_inj (x := fun j => (R 0 j).val) hB (hR 0) hz
        (by rw [hRv, hq0]; exact he))
    · exact congrFun (Nat.ofDigits_ofFn_inj (x := fun j => (R (Fin.last m) j).val)
        (y := fun _ => 0) hB (hR _) (fun _ => by lia)
        (by simp only [hRv, hqe, Nat.mul_zero, List.ofFn_const, Nat.ofDigits_replicate_zero]))
    · intro i
      refine ⟨Nat.le_of_lt (hy i), hx, (fun _ => by lia), hT i, ?_, le_refl _,
        hR i.succ, hT i, hR i.castSucc, ?_⟩
      · simpa only [X, Sum.elim_inr, Nat.mul_comm] using (hTv i).symm
      · simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hRv, hTv, hRv, hqs i]
        dsimp [X]
        ring

end Cslib.Logic.FO.Ordered.Radix
