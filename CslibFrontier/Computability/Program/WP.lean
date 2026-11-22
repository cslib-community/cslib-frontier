/-
Copyright (c) 2026 Samuel Schlesinger, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Program.Structured

/-!
# Weakest preconditions for structured programs

`WP I c x Q` states that the structured program `c` leads from `x` to some data `y` in some
number `n` of instructions such that `Q y n`. Its rules run through a program one instruction at
a time and hand the rest of the program the data reached, so a correctness proof follows the
program text: data instructions and conditionals are executed, a subprogram is replaced by its
specification (`WP.call`), and a loop by its invariant (`WP.loop`, `WP.loopUntil`).

A specification `∃ y, ExecWithin I c x y T ∧ P y` is `WP I c x fun y n => n ≤ T ∧ P y`
(`WP.exists_execWithin`).

## Main definitions

* `WP`: the weakest-precondition form of `ExecWithin`.

## Main results

* `WP.seq`, `WP.branch`, `WP.call`: sequencing, conditionals and subprograms.
* `WP.loop`, `WP.loopUntil`: loops, by an invariant and a measure that decreases.
* `WP.loopUntil_indexed`: the same with a ghost variant, which need not be a function of the
  data.
* `WP.loop_iter`, `WP.loopUntil_iter`: one iteration, for proofs by induction on the data a loop
  descends.

## References

This generalizes `Cslib.WordRAM.WP.Exact` to any instruction set: the count `n` is the exact
instruction count of an execution, where `Cslib.WordRAM.WP` holds of any bound on it. A
postcondition that bounds the count from above, as in `WP.exists_execWithin`, reads the same in
both.
-/

public section

namespace Cslib.Program

universe u v w

variable {I : InstructionSet.{u, v, w}}

/-- `WP I c x Q`: the program `c` leads from `x` to data `y`, in `n` instructions, with `Q y n`. -/
@[expose] def WP (I : InstructionSet.{u, v, w}) (c : Code I.Op I.Test) (x : I.Data)
    (Q : I.Data → ℕ → Prop) : Prop :=
  ∃ y n, Exec I c x y n ∧ Q y n

namespace WP

variable {c c₁ c₂ pos neg body : Code I.Op I.Test} {t : I.Test} {x y : I.Data}
  {Q Q' : I.Data → ℕ → Prop} {T : ℕ}

/-- A specification is a weakest precondition whose postcondition bounds the count. -/
theorem exists_execWithin {P : I.Data → Prop} (h : WP I c x fun y n => n ≤ T ∧ P y) :
    ∃ y, ExecWithin I c x y T ∧ P y :=
  let ⟨y, n, he, hn, hP⟩ := h
  ⟨y, ⟨n, hn, he⟩, hP⟩

/-- Weaken the postcondition. -/
theorem mono (h : WP I c x Q) (hQ : ∀ y n, Q y n → Q' y n) : WP I c x Q' :=
  let ⟨y, n, he, hq⟩ := h
  ⟨y, n, he, hQ y n hq⟩

/-- `skip` changes nothing and costs nothing. -/
theorem skip (h : Q x 0) : WP I .skip x Q := ⟨x, 0, .skip, h⟩

/-- A data instruction. -/
theorem op {o : I.Op} (ho : I.eval o x = some y) (h : Q y 1) : WP I (.op o) x Q :=
  ⟨y, 1, .op ho, h⟩

/-- Sequencing: run `c₁`, then run `c₂` from the data it reaches. The count of `c₁` is added
last, as in `Cslib.WordRAM.WP.seq`, so that the counts of a sequence accumulate as `(n + 1) + 1`
with the numerals on the right and not as `1 + (1 + n)`: deciding whether such a sum is a given
variable takes time exponential in its length. -/
theorem seq (h : WP I c₁ x fun y m => WP I c₂ y fun z n => Q z (n + m)) :
    WP I (.seq c₁ c₂) x Q :=
  let ⟨_, m, he₁, _, n, he₂, hq⟩ := h
  ⟨_, m + n, .seq he₁ he₂, Nat.add_comm m n ▸ hq⟩

/-- A conditional whose test holds. -/
theorem branch_pos (ht : I.Holds t x) (h : WP I pos x fun y n => Q y (n + 1)) :
    WP I (.branch t pos neg) x Q :=
  let ⟨y, n, he, hq⟩ := h
  ⟨y, n + 1, .branch_pos ht he, hq⟩

/-- A conditional whose test fails. -/
theorem branch_neg (ht : ¬I.Holds t x) (h : WP I neg x fun y n => Q y (n + 2)) :
    WP I (.branch t pos neg) x Q :=
  let ⟨y, n, he, hq⟩ := h
  ⟨y, n + 2, .branch_neg ht he, hq⟩

/-- A conditional, by cases on its test. -/
theorem branch (hpos : I.Holds t x → WP I pos x fun y n => Q y (n + 1))
    (hneg : ¬I.Holds t x → WP I neg x fun y n => Q y (n + 2)) :
    WP I (.branch t pos neg) x Q := by
  by_cases ht : I.Holds t x
  · exact branch_pos ht (hpos ht)
  · exact branch_neg ht (hneg ht)

/-- A subprogram, by its specification: continue from any data and count it allows. -/
theorem call {R : I.Data → Prop} (spec : ∃ y, ExecWithin I c x y T ∧ R y)
    (h : ∀ y, R y → ∀ n ≤ T, Q y n) : WP I c x Q :=
  let ⟨y, ⟨n, hn, he⟩, hR⟩ := spec
  ⟨y, n, he, h y hR n hn⟩

/-- Leaving a loop that runs until its test holds. -/
theorem loopUntil_exit (ht : I.Holds t x) (h : Q x 1) : WP I (.loopUntil t body) x Q :=
  ⟨x, 1, .loopUntil_exit ht, h⟩

/-- One iteration of a loop that runs until its test holds, then the loop again. The count of
the body is added last, as in `WP.seq`. -/
theorem loopUntil_iter (ht : ¬I.Holds t x)
    (h : WP I body x fun y m => WP I (.loopUntil t body) y fun z n => Q z (n + m + 2)) :
    WP I (.loopUntil t body) x Q :=
  let ⟨_, m, he₁, _, n, he₂, hq⟩ := h
  ⟨_, m + n + 2, .loopUntil_iter ht he₁ he₂, Nat.add_comm m n ▸ hq⟩

/-- Leaving a loop that runs while its test holds. -/
theorem loop_exit (ht : ¬I.Holds t x) (h : Q x 2) : WP I (.loop t body) x Q :=
  ⟨x, 2, .loop_exit ht, h⟩

/-- One iteration of a loop that runs while its test holds, then the loop again. The count of
the body is added last, as in `WP.seq`. -/
theorem loop_iter (ht : I.Holds t x)
    (h : WP I body x fun y m => WP I (.loop t body) y fun z n => Q z (n + m + 2)) :
    WP I (.loop t body) x Q :=
  let ⟨_, m, he₁, _, n, he₂, hq⟩ := h
  ⟨_, m + n + 2, .loop_iter ht he₁ he₂, Nat.add_comm m n ▸ hq⟩

/-- **Until rule.** A loop that runs until its test holds, by an invariant `P` and a measure `μ`
that every iteration of at most `T` instructions decreases. -/
theorem loopUntil (P : I.Data → Prop) (μ : I.Data → ℕ) (T : ℕ)
    (hbody : ∀ x, P x → ¬I.Holds t x → WP I body x fun y n => n ≤ T ∧ P y ∧ μ y < μ x)
    (hx : P x) (h : ∀ y, P y → I.Holds t y → ∀ n ≤ μ x * (T + 2) + 1, Q y n) :
    WP I (.loopUntil t body) x Q :=
  call (R := fun y => P y ∧ I.Holds t y)
    (ExecWithin.loopUntil_invariant P μ (fun x hx ht => exists_execWithin (hbody x hx ht)) hx)
    fun y hy => h y hy.1 hy.2

/-- **Until rule, with a ghost variant.** A loop that runs until its test holds, by an invariant
`P k` indexed by a number that every iteration of at most `T` instructions decreases. The index
need not be a function of the data: it may count proof data, such as the ancestors still to
visit. -/
theorem loopUntil_indexed (P : ℕ → I.Data → Prop) (T : ℕ)
    (hbody : ∀ k x, P k x → ¬I.Holds t x → WP I body x fun y n => n ≤ T ∧ ∃ j < k, P j y)
    {k : ℕ} (hx : P k x)
    (h : ∀ j y, j ≤ k → P j y → I.Holds t y → ∀ n ≤ k * (T + 2) + 1, Q y n) :
    WP I (.loopUntil t body) x Q := by
  induction k using Nat.strong_induction_on generalizing x Q with
  | _ k ih =>
    by_cases ht : I.Holds t x
    · exact loopUntil_exit ht (h k x le_rfl hx ht 1 (by omega))
    · refine loopUntil_iter ht ((hbody k x hx ht).mono ?_)
      rintro y m ⟨hm, j, hj, hy⟩
      refine ih j hj hy fun i z hi hz htz n hn => h i z (by omega) hz htz _ ?_
      have := Nat.mul_le_mul_right (T + 2) (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at this
      omega

/-- **While rule.** A loop that runs while its test holds, by an invariant `P` and a measure `μ`
that every iteration of at most `T` instructions decreases. -/
theorem loop (P : I.Data → Prop) (μ : I.Data → ℕ) (T : ℕ)
    (hbody : ∀ x, P x → I.Holds t x → WP I body x fun y n => n ≤ T ∧ P y ∧ μ y < μ x)
    (hx : P x) (h : ∀ y, P y → ¬I.Holds t y → ∀ n ≤ μ x * (T + 2) + 2, Q y n) :
    WP I (.loop t body) x Q :=
  call (R := fun y => P y ∧ ¬I.Holds t y)
    (ExecWithin.loop_invariant P μ (fun x hx ht => exists_execWithin (hbody x hx ht)) hx)
    fun y hy => h y hy.1 hy.2

end WP

end Cslib.Program
