/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Classes.PP.Time

/-!
# Iterated exponential, quasipolynomial and majority time bounds

The bottom exponent distinguishes the linear-exponent classes from their polynomial-exponent
counterparts. The resource classes measure the bounds in the encoded input length.

## Main definitions

* `EE`, `EEE`, `EEXP`, `NEE`, `NEEXP`: iterated exponential time.
* `ESPACE`, `EESPACE`: singly and doubly exponential space with linear bottom exponent.
* `PEXP`: exponential time with strict majority acceptance.
* `QP`: quasipolynomial time.
* `TOWER`: deterministic time bounded by an exponential tower of elementary height.
-/

@[expose] public section

open scoped Function

namespace Cslib.Complexity

variable {α : Type*}

/-- Deterministic double exponential time with linear bottom exponent
[ImpagliazzoKabanetsWigderson2002]. -/
def EE (enc : α ↪ List Bool) : Set (Set α) := ⋃ c, DTIME enc fun n => 2 ^ 2 ^ (c * n)

/-- Deterministic triple exponential time with linear bottom exponent
[ImpagliazzoKabanetsWigderson2002]. -/
def EEE (enc : α ↪ List Bool) : Set (Set α) := ⋃ c, DTIME enc fun n => 2 ^ 2 ^ 2 ^ (c * n)

/-- Deterministic double exponential time with polynomial bottom exponent. -/
def EEXP (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, DTIME enc fun n => 2 ^ 2 ^ n ^ k

/-- Nondeterministic double exponential time with linear bottom exponent. -/
def NEE (enc : α ↪ List Bool) : Set (Set α) := ⋃ c, NTIME enc fun n => 2 ^ 2 ^ (c * n)

/-- Nondeterministic double exponential time with polynomial bottom exponent. -/
def NEEXP (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, NTIME enc fun n => 2 ^ 2 ^ n ^ k

/-- Deterministic exponential space with linear exponent. -/
def ESPACE (enc : α ↪ List Bool) : Set (Set α) := ⋃ c, DSPACE enc fun n => 2 ^ (c * n)

/-- Deterministic double exponential space with linear bottom exponent. -/
def EESPACE (enc : α ↪ List Bool) : Set (Set α) := ⋃ c, DSPACE enc fun n => 2 ^ 2 ^ (c * n)

/-- Exponential time with strict majority acceptance, the analogue of `PP` for `EXP`
[BuhrmanFortnowThierauf1998]. -/
def PEXP (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, PPTIME enc fun n => 2 ^ n ^ k

/-- Quasipolynomial deterministic time `2 ^ (log n) ^ O(1)` [Babai2016GI].
The shift in the integer logarithm also covers empty inputs. -/
def QP (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k, DTIME enc fun n => 2 ^ (Nat.log2 n + 1) ^ k

/-- TOWER is deterministic time bounded by a tower of twos of elementary height
[Schmitz2016]. For each fixed `k`, iterating `x ↦ 2 ^ x` exactly `k` times on `n` gives an
elementary height bound. These bounds dominate all elementary functions, so the union suffices. -/
def TOWER (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k, DTIME enc fun n =>
    let exp₂ : ℕ → ℕ := fun x => 2 ^ x
    let height := (exp₂^[k]) n
    (exp₂^[height]) 0

end Cslib.Complexity
