/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Laws

/-!
# Laws at the vertices of different towers

The laws of Theorem G.2 of [AnthropicVPVNP2026] (p. 43) are laws on `U_h`: their roles are the
elements of `U_h` and their channels the near pairs. Theorem H.2 applies them at every vertex of
every tower of Proposition H.1 (p. 44), whose vertices all look like `U_h`. The laws at the
vertices of a tower (`VertexLaws`) depend on the tower only through its places, its near pairs
and the ends of the near pairs. An equivalence of places and one of near pairs that agree on the
ends carry them to another tower with the same numbers `b` and `r` (`VertexLaws.transfer`), with
the same laws and the same constants. For the towers `Cslib.SLTower.tower h n h2` of Proposition
H.1 the places, the near pairs and their ends do not depend on `n`, and the identities transfer
the laws from one of them to all others.

## Main definitions

* `VertexLaws.transfer`: the laws at the vertices of a tower, at the vertices of another tower
  with the same local structure.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem G.2 (p. 43) and Proposition H.1 (p. 44); modules `Nc.Tow.FromPrice` and `Nc.Vp.Main`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower

/-- An equivalence of types, on unordered pairs. -/
private def sym2Congr {α β : Type*} (φ : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map φ
  invFun := Sym2.map φ.symm
  left_inv q := by simp [Sym2.map_map]
  right_inv q := by simp [Sym2.map_map]

namespace VertexLaws

variable {F : Type*} [CommSemiring F] {h b D J r h' D' J' : ℕ} {T : Tower h b D J r}

/-- **Laws at the vertices of another tower.** An equivalence `φ` of the places at a vertex and an
equivalence `ψ` of the near pairs that agree on the ends of the near pairs carry the laws at the
vertices of `T` to a tower `T'` with the same number `b` of places at a vertex and the same `r`.
The laws and their constants are the same. -/
@[expose] def transfer (FL : VertexLaws F T) (T' : Tower h' b D' J' r) (φ : T.Fl ≃ T'.Fl)
    (ψ : T.Nr ≃ T'.Nr) (hφ : ∀ ν, s(φ (T.cN ν), φ (T.dN ν)) = s(T'.cN (ψ ν), T'.dN (ψ ν))) :
    VertexLaws F T' :=
  { FL with
    place d := (FL.place d).trans φ
    nearPair d := (FL.nearPair d).trans ψ
    place_channelEnd d ν := by
      simpa only [Sym2.map_mk, hφ, Equiv.trans_apply] using
        congrArg (Sym2.map φ) (FL.place_channelEnd d ν)
    exists_le_card_slot n t ht := by
      let e := sym2Congr φ
      have hN : T.NN2 (n ∘ e) = T'.NN2 n := by
        rw [Tower.NN2_def, Tower.NN2_def]
        exact congrArg _ (Fintype.sum_equiv e _ _ fun q => by
          simp only [Function.comp_apply, e, sym2Congr, Equiv.coe_fn_mk,
            Sym2.isDiag_map φ.injective])
      obtain ⟨d, hd⟩ := FL.exists_le_card_slot (n ∘ e) t (hN ▸ ht)
      refine ⟨d, fun q hq => ?_⟩
      have h1 := hd (e.symm q) (mt (Sym2.isDiag_map φ.symm.injective).1 hq)
      rw [Function.comp_apply, e.apply_symm_apply] at h1
      refine h1.trans (le_of_eq (congrArg (· * t) (congrArg card (filter_congr fun s _ => ?_))))
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.eq_symm_apply]
      rfl }

end VertexLaws

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
