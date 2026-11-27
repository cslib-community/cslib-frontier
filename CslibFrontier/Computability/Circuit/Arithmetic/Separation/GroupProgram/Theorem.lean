/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Time
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Accept

/-!
# The program GROUP at the script of a group

For a fixed automaton, a fixed code of the letters and a fixed list of roles of laws, one formula
of the tree machine is the program GROUP of the evaluator of [AnthropicVPVNP2026]: at the script
of a group (`groupScript`), its plain sum is the value of the group after the moves of a plan, at
a cost linear in the time `groupTime` of the script, and if it has an accepting run at all, the
numbers of units of the base parties of the group are bounded and the outcomes of its roles are
possible (`exists_group`).

## Main results

* `exists_group`: the program GROUP.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source module
`Nc.Grp.GroupThm`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset Interpreter

variable {F : Type} [CommRing F] {θ : List Bool → F} {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ]
  [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}

/-- **The program GROUP.** For an automaton `mu` whose entries are values of formulas, a code
`cb` of its letters and a list `kinds` of roles of laws whose tables are values of formulas, one
formula `GROUP` and one constant `κ` work for every plan `P` and every group `g`: at the script
of the group, with binary numbers `bT` of steps and `bub` of bits of a unit, the plain sum of
`GROUP` takes time at most `κ` times `groupTime` and is the value of the group, and if `GROUP` has
an outcome there, every base party of the group has at most twice the units that its letters
allow and the outcome of every role of the group is possible. -/
theorem exists_group (mu : Tape.Letter S Unit Γ → Matrix Q Q F) (cb : Option Γ → Fin c → Bool)
    (kinds : List (Σ L : Cut.Law F, L.Role)) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (htab : ∀ z ∈ kinds, ∀ i v g', ∃ e : WE, e.val θ = z.1.table z.2 i v g') :
    ∃ (GROUP : Fm) (κ : ℕ), ∀ {A' K E U0 U1 cap : ℕ} {G : Type} [DecidableEq G]
      {M : Moves F (K + K + A') E} (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
      (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (o : M.Channel → Fin U1) (grp : Fin (K + K + A') → G) (g : G)
      (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.Role → ℕ)
      (bT bub : List Bool) (b : UnitId (K + K) U0 M.Channel U1 → UnitContent
        (BitString.binaryValue bub)),
      Function.Injective (Sum.elim key dkey) → 0 < BitString.binaryValue bub → P.Ok cap →
      (∀ κ, (x κ).length ≤ BitString.binaryValue bT) →
      (∀ s p, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last) →
      (∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩) →
      let l := groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b
      Plain θ (κ * groupTime bT bub l) (.cons GROUP.code (scriptEnc bT bub l)) ∧
      pv θ (.cons GROUP.code (scriptEnc bT bub l)) =
        P.groupValue mu (BitString.binaryValue bT) cb q x ρ n o grp g b ∧
      (evl θ GROUP (scriptEnc bT bub l) ≠ [] →
        (∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤
          2 * ((BitString.binaryValue bT + (K + K) * (Fintype.card S + 1)) * c /
            BitString.binaryValue bub + (K + K))) ∧
        ∀ r : M.Role, grp (M.roleParty r) = g →
          ∃ ι : Fin (P.count n o r.1 * BitString.binaryValue bub) → (M.law r.1).Index,
            ∀ ν : (M.law r.1).ChannelAt r.2, (o ⟨r.1, ν.1⟩ : ℕ) =
              (∑ k, ((M.law r.1).labelLength + (M.law r.1).length (ι k) ν)) /
                BitString.binaryValue bub) := by
  obtain ⟨GROUP, κ, hF⟩ := exists_formula_scriptSem (θ := θ) (S := S) mu cb kinds
  refine ⟨GROUP, κ, ?_⟩
  intro A' K E U0 U1 cap G _ M P q x ρ n o grp g key dkey tg bT bub b hκ hub hP hx hρ hkind l
  have hD := hF bT bub l (valid_groupScript cb kinds hkind b)
  have hval := weightedSum_scriptSem_groupScript mu cb kinds (q := q) (n := n) (o := o)
    (grp := grp) (g := g) hκ hub hP hmu hx hρ hkind
    (fun r => htab _ (List.mem_of_getElem? (hkind r))) b
  obtain ⟨h1, h2⟩ := hD.plain
  refine ⟨h1, ?_, fun hacc => ?_⟩
  · rw [h2, ← hval, List.weightedSum, List.map_map]
    simp [l, Function.comp_def]
  · have hne : scriptSem θ mu cb kinds (BitString.binaryValue bT) (BitString.binaryValue bub) l
        .nil ≠ [] := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hacc
      obtain ⟨-, -, z, hz, -⟩ := hD.evl.1 r hr
      exact List.ne_nil_of_mem (List.mem_map.1 hz).choose_spec.1
    exact ⟨fun p hp => count_le_of_accept mu cb kinds P q x ρ n o grp g key dkey tg hub hx hρ hne
      hp, fun r hr => outcome_eq_of_accept mu cb kinds P q x ρ n o grp g key dkey tg hub hkind hne
      hr⟩

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
