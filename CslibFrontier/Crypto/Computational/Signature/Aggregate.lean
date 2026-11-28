/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Winning conditions of the aggregate signature games

The two winning conditions of Boneh–Shoup's aggregate signature games ([BonehShoup2023],
Section 15.5.2, p. 632), stated for any types of public keys and messages so that both the
bit-string schemes of `Crypto.Computational.WordAggregateSignature` and typed schemes can use them.

Definition 15.4 gives the aggregate verification algorithm two vectors of equal length, a vector of
public keys and a vector of messages; both conditions reject vectors of unequal lengths.

## Main definitions

* `Cslib.Crypto.AggregateSignature.asigFresh`: the freshness condition of Attack Game 15.2.
* `Cslib.Crypto.AggregateSignature.sbAsigWin`: the success condition of Attack Game 15.3.

## Main results

* `Cslib.Crypto.AggregateSignature.asigFresh_eq_true_iff`,
  `Cslib.Crypto.AggregateSignature.sbAsigWin_eq_true_iff`: the two conditions as propositions.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 15.5.2 (Definition 15.4, Attack Games 15.2 and 15.3), pp. 630–633.
-/

public section

namespace Cslib.Crypto.AggregateSignature

variable {PK M : Type} [DecidableEq PK] [DecidableEq M]

/-- The freshness condition of Attack Game 15.2 ([BonehShoup2023], p. 632): the vectors `pks` and
`ms` have equal lengths, and some position `j` carries the challenge key `pk` and a message `ms[j]`
outside the list `queried` of signing queries. -/
@[expose]
def asigFresh (pk : PK) (pks : List PK) (ms : List M) (queried : List M) : Bool :=
  (pks.length == ms.length) && (pks.zip ms).any fun p => decide (p.1 = pk ∧ p.2 ∉ queried)

theorem asigFresh_eq_true_iff (pk : PK) (pks : List PK) (ms : List M) (queried : List M) :
    asigFresh pk pks ms queried = true ↔
      pks.length = ms.length ∧
        ∃ (j : ℕ) (hj : j < pks.length) (hj' : j < ms.length), pks[j] = pk ∧ ms[j] ∉ queried := by
  simp only [asigFresh, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_iff_getElem,
    List.length_zip, List.getElem_zip, decide_eq_true_eq]
  constructor
  · rintro ⟨hlen, ⟨p, ⟨j, hj, rfl⟩, hpk, hm⟩⟩
    exact ⟨hlen, j, by omega, by omega, hpk, hm⟩
  · rintro ⟨hlen, j, hj, _, hpk, hm⟩
    exact ⟨hlen, (pks[j], ms[j]), ⟨j, by omega, rfl⟩, hpk, hm⟩

/-- The success condition of Attack Game 15.3 ([BonehShoup2023], p. 632): the two pairs
`(pks, ms)` and `(pks', ms')` differ, each pair has vectors of equal lengths, and the aggregate
signature verifies for both (the verdicts `b₁` and `b₂`). -/
@[expose]
def sbAsigWin (b₁ b₂ : Bool) (pks : List PK) (ms : List M) (pks' : List PK) (ms' : List M) :
    Bool :=
  decide ((pks, ms) ≠ (pks', ms')) && (pks.length == ms.length) && (pks'.length == ms'.length) &&
    b₁ && b₂

theorem sbAsigWin_eq_true_iff (b₁ b₂ : Bool) (pks : List PK) (ms : List M) (pks' : List PK)
    (ms' : List M) :
    sbAsigWin b₁ b₂ pks ms pks' ms' = true ↔
      (pks, ms) ≠ (pks', ms') ∧ pks.length = ms.length ∧ pks'.length = ms'.length ∧
        b₁ = true ∧ b₂ = true := by
  simp only [sbAsigWin, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

end Cslib.Crypto.AggregateSignature
