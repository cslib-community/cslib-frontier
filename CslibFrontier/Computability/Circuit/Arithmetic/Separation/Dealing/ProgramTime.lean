/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.StepCost
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.StepSize
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.TemplateCost

/-!
# The time of the dealing program

At an argument `z` of size at most `s`, the dealing program of [AnthropicVPVNP2026]
(`Codes.dealProgram`) makes one list of filled templates for every state after its steps, as the
dealing theorem says (`dealFormula_does`), within `dealTime Lc X K mm ub bd s` steps
(`dealProgram_does`). The bound counts `60 * Lc + 100` steps for every letter of the word of `z`
and every part, `stepBound Lc X + 30` for each of the at most `4 * X ^ 2 + 7 * X` steps up to the
checks, `90 * Lc + 230` for the guess of the contents of every unit, `(ub + 1) * (60 * Lc + 100)`
more for each of at most `bd` cut units, and `pieceBound Lc X + 60` for each of the `mm`
templates. Here `X` and `Lc` bound the numbers and the lengths of the codes of the dealing program
(`Codes.SizeBounds`).

## Main definitions

* `dealTime`: the bound for the time of the dealing program.

## Main results

* `dealProgram_does`: what the dealing program computes, within `dealTime` steps.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: `G` takes `sΛ` steps for the word, `(MN)^C_tree Λ` steps for the plan and
`kΛ · τΛ/v^300` steps for the cut packets). Ported from the source module `Nc.Dl.Does`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Cslib.BitString (lsbValue)

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- The bound for the time of the dealing program at an argument of size at most `s`, with `K`
parts, `mm` templates, units of `ub` bits and at most `bd` cut units, for codes of length at most
`Lc` and numbers at most `X`. -/
@[expose] def dealTime (Lc X K mm ub bd s : ℕ) : ℕ :=
  60 * s + (s + K) * (60 * Lc + 100) + K * (60 * Lc + 130) +
    (4 * (X * X) + 7 * X) * (stepBound Lc X + 30) + X * (90 * Lc + 230) +
    bd * ((ub + 1) * (60 * Lc + 100)) + mm * (pieceBound Lc X + 60) + 300

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype S] [Fintype Q]
  {K A' E U0 U1 D nI pS mm c : ℕ} {M : Moves F (K + K + A') E} {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS}
  {qn : Q → ℕ} {tg : M.Role → ℕ} {X Lc : ℕ}

/-- **The time of the dealing program.** If `X` and `Lc` bound the numbers and the lengths of the
codes of the dealing program, the bits `nl` and `nub` of the length `ℓ` of a part and of the
number `ub` of bits of a unit have at most `Lc` digits, and every choice that passes the checks
cuts at most `bd` units, then at an argument `z` of size at most `s` the dealing program makes,
within `dealTime Lc X K mm ub bd s` steps, the lists of the filled templates at the states after
all its steps, and the weighted sum of the products of their plain sums is the sum over these
states. -/
theorem dealProgram_does (tab : SlpTab P grp D nI pS) (H : C.SizeBounds qn tg X Lc) (hK : 0 < K)
    {θ : List Bool → F} {nl nub bT bub : List Bool} {ℓ ub : ℕ} (hnl : lsbValue nl = ℓ)
    (hnub : lsbValue nub = ub) (hlnl : nl.length ≤ Lc) (hlnub : nub.length ≤ Lc) {hD : 1 < D}
    {hmm : mm ≤ D} {gp : Tree} {cb : Option Γ → Fin c → Bool} {bt : Bool → Γ} {i e : Q}
    {hU0 : U0 < D} {hU1 : U1 ≤ D} {bd : ℕ}
    (hbd : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) →
      #(Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)) ≤ bd)
    {s : ℕ} (z : Tree) (hz : z.size ≤ s) :
    ∃ Qs : List (F × Tree),
      Does θ (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1) z Qs
        (dealTime Lc X K mm ub bd s) ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt)))) fun _ => .nil),
        q.2 = listT (((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)).map
          fun t => t.expand σ)) ∧
      wsum Qs (pvProd θ) = ((execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt)))) fun _ => .nil)).map
          fun σ => (((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)).map
            fun t => pv θ (t.expand σ)).prod).sum := by
  classical
  subst hnl hnub
  have h0 := gets_partsT_eq_initialState C cb bt (lsbValue nl) z
  obtain ⟨I, hI, hI0⟩ := exists_inv_dealSteps (m := lsbValue nub) (mb := nub.length) tab H.name
    H.digit H.rowData H.states H.rowDatas H.initUnits H.newUnits
    (partTree cb (parts (lsbValue nl) ((tbits z).map bt))) qn i e hU0 hU1
  obtain ⟨Qs, hQ, hm, hs⟩ := dealFormula_does (θ := θ) (ofBits (letterCode cb (bt false)))
    (ofBits (letterCode cb (bt true))) ((List.finRange K).map fun κ => C.name (.part κ)) nl nub
    (C.dealSteps tab qn i e hU0 hU1) C.contentSteps
    ((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)) z (Ln := Lc)
    (ct := pieceBound Lc X)
    (c9 := X * (90 * Lc + 230) + bd * ((lsbValue nub + 1) * (60 * Lc + 100)))
    (fun _ hp => by obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hp; exact H.name _) hI
    (by rwa [h0]) fun σ hσ => by
      rw [h0] at hσ
      obtain ⟨n, o, hn, ho, I', c', hI', hI0', hc'⟩ :=
        exists_inv_contentSteps (mb := nub.length) tab hK H.name hσ
      refine ⟨⟨I', c', hI', hI0', hc'.trans ?_⟩, fun σ' hσ' t ht => ?_⟩
      · have := Nat.mul_le_mul_right (90 * Lc + 230) H.units
        have := Nat.mul_le_mul (hbd n o hn ho)
          (Nat.mul_le_mul_left (lsbValue nub + 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 60
            hlnub) 100))
        omega
      · obtain ⟨g, -, rfl⟩ := List.mem_map.1 ht
        obtain ⟨_, _, _, _, _, st, -, -, -, -, -, hst, rfl⟩ := mem_execAll_allSteps C tab hK
          (by rw [execAll_append]; exact List.mem_flatMap.2 ⟨σ, hσ, hσ'⟩)
        exact cost_pieceTm_le hst H.name H.digit H.tapes H.parties H.units H.slotsAt H.channelsAt
          H.initUnits H.roles tg bT bub hmm gp g
  rw [h0] at hm hs
  refine ⟨Qs, hQ.mono ?_, hm, hs⟩
  have := Nat.mul_le_mul_right (stepBound Lc X + 30) (length_dealSteps_le (C := C) (qn := qn) tab
    H.blocks H.parties H.tapes H.channels H.gates H.moves H.units i e hU0 hU1)
  have := Nat.mul_le_mul (Nat.add_le_add_right hz K)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 60 hlnl) 100)
  simp only [List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
    smul_eq_mul]
  unfold dealTime
  omega

end Cslib.Circuits.Arithmetic.Separation.Dealing
