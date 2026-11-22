/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Formula
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.NumBasic

/-!
# The codes of the states of the formula

The explicit machine of Lemma 6.4 follows an address from the root and keeps one state. This module
fixes the number that stands for a state (`Setup.code`); the programs of the numeric generator act
on these numbers, and `AGen.Agrees` relates them to the states of `Setup.gen`.

* A label is written by its Lemma 4.1 code, `lcode l = ofBits (msCode l.1 ++ msCode l.2)`, and a
  multiset of requests by `mcode σ = ofBits (msCode σ)`; labels are never decoded, since a label of
  weight `W` has a code of `O(√W)` bits but a list of distinct weights of up to `O(√W log W)` bits.
* A multiset of typed targets of a half-routing is written by its three parts, the types at the
  places `placeOf up 0, 1, 2` (`tcode`); the targets that occur have these places.
* A state that refers to the clique at a path `chs` carries the budget arrays of all the cliques on
  the path (`cacheC chs`: for `chs`, `chs.tail`, …, `[]`, the node count and the array `arrN` of
  width `fw`), as the machine of Lemma 6.4 keeps them. A child program updates the cache by one
  level (`BudgetNum.childN`), and a table entry one level up reads the next array.
* Integers by the zigzag code, typed places by `tgtNum`, lists by `NatList.enc`, and the kind of
  state by the first entry of its list: `0` zero, `1` literal, `2` clique, `3` last label,
  `4` entry, `5` range, `6` first-clique range, `7`–`9` transport.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open SumProduct.NatList Num

/-- The Lemma 4.1 code of a multiset, as a number. -/
def mcode (σ : Multiset ℕ) : ℕ := ofBits (msCode σ)

/-- The Lemma 4.1 code of a label, as a number (its two multiset codes, in turn). -/
def lcode (l : Label) : ℕ := ofBits (msCode l.1 ++ msCode l.2)

theorem labelCode_eq_lcode {a : ℕ} (ha : a ≠ 0) (l : Label) : labelCode a l = lcode l := by
  simp [labelCode, lcode, ha]

/-- The types at the place `placeOf up p` in a multiset of typed targets. -/
def tpart (up : Bool) (T : Multiset (HPlace × ℕ)) (p : ℕ) : Multiset ℕ :=
  (T.filter fun s => s.1 = placeOf up p).map Prod.snd

/-- The code of a multiset of typed targets: the codes of its three parts. -/
def tcode (up : Bool) (T : Multiset (HPlace × ℕ)) : ℕ :=
  SumProduct.NatList.enc [mcode (tpart up T 0), mcode (tpart up T 1), mcode (tpart up T 2)]

namespace Setup

variable (S : Setup)

/-- The budget array of the clique at a path, with its node count. -/
noncomputable def arrAt (chs : List ℕ) : ℕ :=
  SumProduct.NatList.enc [(S.clique chs).q, arrN (S.clique chs).q S.fw (Num.extN (S.clique chs).a)]

/-- The arrays of the cliques along a path, the clique at the path first. -/
noncomputable def cacheL : List ℕ → List ℕ
  | [] => [S.arrAt []]
  | i :: rest => S.arrAt (i :: rest) :: cacheL rest

/-- The cache of a path. -/
noncomputable def cacheC (chs : List ℕ) : ℕ := SumProduct.NatList.enc (S.cacheL chs)

/-- **The code of a state.** -/
noncomputable def code : St → ℕ
  | .zero => SumProduct.NatList.enc [0]
  | .lit v => SumProduct.NatList.enc [1, zz v]
  | .cl chs => SumProduct.NatList.enc [2, SumProduct.NatList.enc chs, S.cacheC chs]
  | .last chs i => SumProduct.NatList.enc [3, SumProduct.NatList.enc chs, S.cacheC chs, i]
  | .ent chs v args => SumProduct.NatList.enc [4, SumProduct.NatList.enc chs, S.cacheC chs, v, args]
  | .rng chs v args ξ lo
      hi => SumProduct.NatList.enc [5, SumProduct.NatList.enc chs, S.cacheC chs, v, args, ξ, lo, hi]
  | .rng0 v args lo hi => SumProduct.NatList.enc [6, S.cacheC [], v, args, lo, hi]
  | .tr up x y m lo hi T c =>
    SumProduct.NatList.enc [7, up.toNat, lcode x, lcode y, lcode m, lo, hi, tcode up T, zz c]
  | .trm up x y m lo ν hi t T₁ T₂ c₁ c₀ c₂ =>
    SumProduct.NatList.enc [8, up.toNat, lcode x, lcode y, lcode m, lo, ν, hi, tgtNum t, tcode up
        T₁, tcode up T₂,
      zz c₁, zz c₀, zz c₂]
  | .trr up x y m ν hi t T₂ c₀ c₂ =>
    SumProduct.NatList.enc [9, up.toNat, lcode x, lcode y, lcode m, ν, hi, tgtNum t, tcode up T₂, zz
        c₀, zz c₂]

end Setup

end Cslib.Complexity.NtimeDspace.Cube
