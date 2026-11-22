/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Counting over a range with a stored counter

`Turing.MultiTapeTM.ComputableInSpace.countWith` counts the indices `i < m a` that satisfy a
predicate `p (i, a)` of a stored index and the input, where `p` is in the context form of
`Turing.MultiTapeTM.ComputableInSpace.loopWith`. The registers are the bound, the index and the
count, so the space is that of the bound and of `p`, plus the logarithm of the length of the
input, for any number of indices. Majority and existence over the range are corollaries.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.countWith`: the number of indices below a computed bound
  that satisfy a predicate in context form.
* `Turing.MultiTapeTM.ComputableInSpace.majorityWith`: whether more than half of them do.
* `Turing.MultiTapeTM.ComputableInSpace.anyWith`: whether one of them does.
-/

public section

namespace Turing.MultiTapeTM

open ComputableInSpace

/-- The body of the counting loop on the bound, the index and the count. -/
private def countStep {α : Type} (p : ℕ × α → Bool) (q : (ℕ × ℕ × ℕ) × α) :
    Option (ℕ × ℕ × ℕ) :=
  if q.1.2.1 < q.1.1 then
    some (q.1.1, q.1.2.1 + 1, q.1.2.2 + if p (q.1.2.1, q.2) then 1 else 0)
  else none

private theorem countP_range_succ {α : Type} (p : ℕ × α → Bool) (a : α) (j : ℕ) :
    (List.range (j + 1)).countP (fun i => p (i, a)) =
      (List.range j).countP (fun i => p (i, a)) + if p (j, a) then 1 else 0 := by
  rw [List.range_succ, List.countP_append]
  cases h : p (j, a) <;> simp [h]

/-- **Counting with a stored counter.** If the bound `m` is computable within `S`, and the
predicate `p` takes a stored index and the input within the length of the index plus `S`, then the
number of indices `i < m a` with `p (i, a)` is computable within `S + log₂ n` on inputs of length
`n`. -/
theorem ComputableInSpace.countWith {α : Type} {encA : α ↪ List Bool} {m : α → ℕ}
    {p : ℕ × α → Bool} {S : α → ℕ} (hm : ComputableInSpace m encA encNat S)
    (hp : ComputableInSpace p (encPair encNat encA) encBool
      fun q => (encNat q.1).length + S q.2) :
    ComputableInSpace (fun a => (List.range (m a)).countP fun i => p (i, a)) encA encNat
      fun a => S a + Nat.log2 (encA a).length := by
  obtain ⟨-, cm, -, hmout⟩ := id hm
  have hreg : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α => q.1)
      (encPair (encPair encNat (encPair encNat encNat)) encA)
      (encPair encNat (encPair encNat encNat))
      fun q => (encPair encNat (encPair encNat encNat) q.1).length +
        (S q.2 + Nat.log2 (encA q.2).length) :=
    ((ComputableInLogSpace.fst _ encA).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _)).mono_le fun _ => by omega
  have hpq : ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × α => p (q.1.2.1, q.2))
      (encPair (encPair encNat (encPair encNat encNat)) encA) encBool
      fun q => (encPair encNat (encPair encNat encNat) q.1).length +
        (S q.2 + Nat.log2 (encA q.2).length) :=
    hp.comp_logSpace_context (f := fun q : (ℕ × ℕ × ℕ) × α => (q.1.2.1, q.2))
      (S := fun a => S a + Nat.log2 (encA a).length)
      (ComputableInLogSpace.pair
        (((ComputableInLogSpace.fst encNat encNat).comp'
          (ComputableInLogSpace.snd encNat (encPair encNat encNat))).comp'
          (ComputableInLogSpace.fst _ encA))
        (ComputableInLogSpace.snd _ encA))
      (.of_le fun q => by simp only [length_encPair]; omega) fun _ => by omega
  have hconst {β : Type} (encB : β ↪ List Bool) (b : β) :
      ComputableInSpace (fun _ : (ℕ × ℕ × ℕ) × α => b)
        (encPair (encPair encNat (encPair encNat encNat)) encA) encB
        fun q => (encPair encNat (encPair encNat encNat) q.1).length +
          (S q.2 + Nat.log2 (encA q.2).length) :=
    (ComputableInSpace.constZero b).mono_le fun _ => Nat.zero_le _
  have hi := hreg.snd'.fst'
  have hstep : ComputableInSpace (countStep p)
      (encPair (encPair encNat (encPair encNat encNat)) encA)
      (encOption (encPair encNat (encPair encNat encNat)))
      fun q => (encPair encNat (encPair encNat encNat) q.1).length +
        (S q.2 + Nat.log2 (encA q.2).length) :=
    (budget_ite (budget_natLt hi hreg.fst')
      (budget_optionSome (budget_prod hreg.fst' (budget_prod (budget_natSucc hi)
        (budget_natAdd hreg.snd'.snd' (budget_ite hpq (hconst encNat 1) (hconst encNat 0))))))
      (hconst _ none)).of_enc_eq fun q => by
        unfold countStep
        by_cases h : q.1.2.1 < q.1.1 <;> simp [h]
  have hinit : ComputableInSpace (fun a => (m a, 0, 0)) encA
      (encPair encNat (encPair encNat encNat)) fun a => S a + Nat.log2 (encA a).length :=
    budget_prod (hm.mono_le fun _ => by omega) (budget_prod
      ((ComputableInSpace.constZero _).mono_le fun _ => Nat.zero_le _)
      ((ComputableInSpace.constZero _).mono_le fun _ => Nat.zero_le _))
  have hloop := ComputableInSpace.loopWith (step := countStep p)
    (B := fun a => 6 * (encNat (m a)).length + 3)
    (fun a j => (m a, j, (List.range j).countP fun i => p (i, a))) m
    hinit hstep (fun _ => rfl)
    (fun a j hj => by simp [countStep, hj, countP_range_succ])
    (fun a => by simp [countStep])
    (fun a j hj => by
      have h₁ := length_encNat_mono hj
      have h₂ := length_encNat_mono (((List.range j).countP_le_length).trans
        (by rw [List.length_range]; exact hj) : (List.range j).countP (fun i => p (i, a)) ≤ m a)
      simp only [length_encPair]
      omega)
  exact hloop.snd'.snd'.weaken ⟨7 * cm + 4, fun a => by
    dsimp only
    have := hmout a
    have h : 6 * (cm * (S a + 1)) ≤ 6 * (cm * (S a + Nat.log2 (encA a).length + 1)) :=
      Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left cm (by omega))
    have : (7 * cm + 4) * (S a + Nat.log2 (encA a).length + 1) =
        7 * (cm * (S a + Nat.log2 (encA a).length + 1)) +
          4 * (S a + Nat.log2 (encA a).length + 1) := by ring
    omega⟩

/-- **Majority over a range.** Whether more than half of the indices `i < m a` satisfy
`p (i, a)`, within `S + log₂ n`. -/
theorem ComputableInSpace.majorityWith {α : Type} {encA : α ↪ List Bool} {m : α → ℕ}
    {p : ℕ × α → Bool} {S : α → ℕ} (hm : ComputableInSpace m encA encNat S)
    (hp : ComputableInSpace p (encPair encNat encA) encBool
      fun q => (encNat q.1).length + S q.2) :
    ComputableInSpace (fun a => decide (m a < 2 * (List.range (m a)).countP fun i => p (i, a)))
      encA encBool fun a => S a + Nat.log2 (encA a).length :=
  budget_natLt (hm.mono_le fun _ => Nat.le_add_right _ _)
    (budget_natMul ((ComputableInSpace.constZero 2).mono_le fun _ => Nat.zero_le _)
      (hm.countWith hp))

/-- **Existence over a range.** Whether some index `i < m a` satisfies `p (i, a)`, within
`S + log₂ n`. -/
theorem ComputableInSpace.anyWith {α : Type} {encA : α ↪ List Bool} {m : α → ℕ}
    {p : ℕ × α → Bool} {S : α → ℕ} (hm : ComputableInSpace m encA encNat S)
    (hp : ComputableInSpace p (encPair encNat encA) encBool
      fun q => (encNat q.1).length + S q.2) :
    ComputableInSpace (fun a => (List.range (m a)).any fun i => p (i, a)) encA encBool
      fun a => S a + Nat.log2 (encA a).length :=
  (budget_natLt ((ComputableInSpace.constZero 0).mono_le fun _ => Nat.zero_le _)
    (hm.countWith hp)).of_enc_eq fun a => by
      congr 1
      rw [Bool.eq_iff_iff]
      simp [List.countP_pos_iff]

end Turing.MultiTapeTM
