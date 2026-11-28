/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.StepSize
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Time

/-!
# The time of GROUP at the scripts of the dealing program

The pieces of the dealing program of [AnthropicVPVNP2026] are the instances of the program GROUP
at the scripts of the groups, whose time is `groupTime` (P1's `groupTime_le`). For the codes of
the dealing program (`Codes.SizeBounds`), with at most `ι` base parties in the group, each with
at most `lh` units at the beginning, and at most `ev` cells and units read by its roles, this time
is at most `(Lc + 1) * (T + ub + 2) + ι * T + 3 * (ev + ι * lh) * (ub + Lc + 1) + 10 * X ^ 3`
(`groupTime_le_of_sizeBounds`).

GROUP reads the numbers `T` and `ub` most significant bit first (`BitString.binaryValue`), the
dealing program least significant bit first (`BitString.lsbValue`); the library lemma
`BitString.lsbValue_eq_binaryValue_reverse` relates the two.

## Main results

* `groupTime_le_of_sizeBounds`: the time of GROUP at the script of a group of the dealing
  program.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator in the proof
of Theorem J.3 (p. 54: it halts within `(#blocks · T + #bits of packets + #instructions · v^O(1))
(lg v)^O(1)` steps). Ported from the source module `Nc.Dl.GrpCost` (`grpTimeOK`, `exists_bits`),
on the constants of P1's `groupTime_le`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation

namespace Dealing

open Finset Cut GroupProgram

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype S] [Fintype Q] {A' E K U0 U1 D pS c : ℕ}
  {M : Moves F (K + K + A') E} {C : Codes S M U0 U1 D pS} {qn : Q → ℕ} {tg : M.Role → ℕ}
  {X Lc : ℕ} {G : Type} [DecidableEq G] {cb : Option Γ → Fin c → Bool} {P : Plan M U0 U1}
  {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G}

/-- **The time of GROUP at the script of a group of the dealing program.** If `X` and `Lc` bound
the numbers and the lengths of the codes of the dealing program, the binary words `bT` and `bub`
of `T` and `ub` have at most `Lc` bits, the plan is `cap`-bounded, the input parts have at most
`T` letters, and the group has at most `ι ≤ X` base parties, each with at most `lh` units at the
beginning, and at most `ev` cells and units read by its roles in all, then the time of GROUP at
the script of the group is at most
`(Lc + 1) * (T + ub + 2) + ι * T + 3 * (ev + ι * lh) * (ub + Lc + 1) + 10 * X ^ 3`. -/
theorem groupTime_le_of_sizeBounds (H : C.SizeBounds qn tg X Lc) {bT bub : List Bool} {T ub : ℕ}
    (hT : BitString.binaryValue bT = T) (hub : BitString.binaryValue bub = ub)
    (hlT : bT.length ≤ Lc) (hlub : bub.length ≤ Lc) {cap : ℕ} (hP : P.Ok cap)
    (hx : ∀ κ, (x κ).length ≤ T) {ι lh ev : ℕ}
    (hι : #{p : Fin (K + K) | grp (Fin.castAdd A' p) = g} ≤ ι) (hιX : ι ≤ X)
    (hlh : ∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤ lh)
    (hev : cellCount n o grp g + roleUnitCount P n o grp g ≤ ev)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    groupTime bT bub (groupScript qn cb P q x ρ n o grp g C.key C.dkey tg b) ≤
      (Lc + 1) * (T + ub + 2) + ι * T + 3 * (ev + ι * lh) * (ub + Lc + 1) + 10 * X ^ 3 := by
  have hb : (baseParties grp g).length = #{p : Fin (K + K) | grp (Fin.castAdd A' p) = g} := by
    rw [baseParties_eq_filter, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
    exact congrArg Finset.card (Finset.ext fun _ => by simp)
  refine (groupTime_le hT hub hlT hlub hP hx H.key H.dkey H.tapes H.parties H.roles H.slotsAt
    H.channelsAt (hb.trans_le hι) hιX hlh le_rfl le_rfl b).trans ?_
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hev _))) _) _

end Dealing

end Cslib.Circuits.Arithmetic.Separation
