/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.PortGraph

/-!
# Selector constraints for word reconfiguration

At each position, a positive clause selects a nonempty set of symbols. Negative binary clauses
forbid incompatible selections at consecutive positions. A selector is shared by its row clause
and all incident compatibility clauses. These are the Boolean constraints underlying the
character and relation gadgets in the proof of [VanDerZanden2015, Theorem 6].

## Main definitions

* `HWord.oneHot`: the unique-selection encoding of a word.

## Main results

* `HWord.legal_source_iff`: graph legality means nonempty, pairwise compatible selections.
* `HWord.reachable_oneHot_iff`: word reconfiguration is equivalent to selector reconfiguration.
* `HWord.PortGraph.reachable_oneHot_iff`: exact word reachability between physical states.

## References

* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*]
  [VanDerZanden2015], Theorem 6, pp. 286–289.
-/

public section

namespace Cslib.Complexity.NCL.HWord

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj]

/-- Selected symbols form nonempty sets with full compatibility between neighbouring sets. -/
structure SelectionLegal (s : Fin n × Fin q → Bool) : Prop where
  /-- At least one symbol is selected at every position. -/
  nonempty : ∀ i, ∃ a, s (i, a) = true
  /-- Every selected pair at consecutive positions is compatible. -/
  compatible : ∀ i j, i.val + 1 = j.val →
    ∀ a b, s (i, a) = true → s (j, b) = true → H.Adj a b

/-- A selector configuration includes the symbol of the word at every position. -/
private def Encodes (s : Fin n × Fin q → Bool) (w : Fin n → Fin q) : Prop :=
  ∀ i, s (i, w i) = true

/-- Select exactly the word's symbol at each position. -/
@[expose] def oneHot (w : Fin n → Fin q) (e : Fin n × Fin q) : Bool :=
  decide (w e.1 = e.2)

/-- The network's shared constraints recognize nonempty, mutually compatible symbol sets. -/
theorem legal_source_iff (s : Fin n × Fin q → Bool) :
    (PortGraph.network H n).sourceGraph.Legal s ↔ SelectionLegal H s := by
  rw [SelectorNetwork.legal_source_iff]
  refine ⟨fun hs => ⟨fun i => ?_, fun i j hij a b ha hb => ?_⟩,
    fun hs => ⟨fun i =>
      let ⟨a, ha⟩ := hs.nonempty i
      ⟨(i, a), PortGraph.network_row H _, ha⟩, fun r hr => ?_⟩⟩
  · obtain ⟨⟨j, a⟩, hj, ha⟩ := hs.nonempty i
    exact (PortGraph.network_row H (j, a)).symm.trans hj ▸ ⟨a, ha⟩
  · by_contra hab
    have hn : i.val + 1 < n := hij ▸ j.isLt
    have hc := hs.relation ⟨i, a, b⟩ (by simp [PortGraph.network_required, hn, hab])
    rw [PortGraph.network_endpoint_false, PortGraph.network_endpoint_true H _ hn,
      show (⟨i.val + 1, hn⟩ : Fin n) = j from Fin.ext hij] at hc
    simp [ha, hb] at hc
  · obtain ⟨hlt, hna⟩ : r.position.val + 1 < n ∧ ¬H.Adj r.first r.second := by
      simpa only [PortGraph.network_required, decide_eq_true_eq] using hr
    rw [PortGraph.network_endpoint_false, PortGraph.network_endpoint_true H r hlt]
    by_cases ha : s (r.position, r.first) = true
    · exact Or.inr (Bool.eq_false_iff.mpr fun hb => hna (hs.compatible _ _ rfl _ _ ha hb))
    · exact Or.inl (Bool.eq_false_iff.mpr ha)

private theorem legal_encoded {s : Fin n × Fin q → Bool} {w : Fin n → Fin q}
    (hs : (PortGraph.network H n).sourceGraph.Legal s) (hw : Encodes s w) : Legal H w :=
  fun i j hij => ((legal_source_iff H s).mp hs).compatible i j hij _ _ (hw i) (hw j)

/-- Unique selections are legal exactly when the encoded word is compatible. -/
theorem legal_oneHot_iff (w : Fin n → Fin q) :
    (PortGraph.network H n).sourceGraph.Legal (oneHot w) ↔ Legal H w :=
  ⟨fun h => legal_encoded H h fun _ => by simp [oneHot], fun hw => (legal_source_iff H _).mpr
    ⟨fun i => ⟨w i, by simp [oneHot]⟩, fun i j hij a b ha hb =>
      (of_decide_eq_true ha : w i = a) ▸ (of_decide_eq_true hb : w j = b) ▸ hw i j hij⟩⟩

private theorem decode_reachable {s t : Fin n × Fin q → Bool}
    (hr : (PortGraph.network H n).sourceGraph.Reachable s t)
    (w : Fin n → Fin q) (hw : Encodes s w) :
    ∃ v, Reachable H w v ∧ Encodes t v := by
  induction hr with
  | refl => exact ⟨w, .refl, hw⟩
  | @tail t u _ hm ih =>
    obtain ⟨v, hv, htv⟩ := ih
    obtain ⟨ht, hu, e, rfl⟩ := hm
    obtain ⟨b, hb⟩ := ((legal_source_iff H _).mp hu).nonempty e.1
    have huv : Encodes (reverse t e) (Function.update v e.1 b) := fun j => by
      rcases eq_or_ne j e.1 with rfl | hj
      · simpa only [Function.update_self] using hb
      · rw [reverse_of_ne t fun h => hj (congrArg Prod.fst h), Function.update_of_ne hj]
        exact htv j
    exact ⟨_, hv.trans (reachable_of_eq_off (legal_encoded H ht htv) (legal_encoded H hu huv) e.1
      fun j hj => (Function.update_of_ne hj b v).symm), huv⟩

private def union (s t : Fin n → Fin q) (e : Fin n × Fin q) : Bool :=
  decide (s e.1 = e.2 ∨ t e.1 = e.2)

private theorem legal_union {s t : Fin n → Fin q} (hs : Legal H s) (ht : Legal H t)
    (i : Fin n) (heq : ∀ j, j ≠ i → s j = t j) :
    (PortGraph.network H n).sourceGraph.Legal (union s t) := by
  apply (legal_source_iff H _).mpr
  constructor
  · exact fun j => ⟨s j, by simp [union]⟩
  · intro j k hjk a b ha hb
    have ha' : s j = a ∨ t j = a := of_decide_eq_true ha
    have hb' : s k = b ∨ t k = b := of_decide_eq_true hb
    by_cases hj : j = i
    · have hk : k ≠ i := by intro hk; subst j k; omega
      have hbk : s k = b := hb'.elim id (fun h => (heq k hk).trans h)
      rcases ha' with haj | haj
      · exact haj ▸ hbk ▸ hs j k hjk
      · exact haj ▸ ((heq k hk).symm.trans hbk) ▸ ht j k hjk
    · have haj : t j = a := ha'.elim (fun h => (heq j hj).symm.trans h) id
      rcases hb' with hbk | hbk
      · exact ((heq j hj).trans haj) ▸ hbk ▸ hs j k hjk
      · exact haj ▸ hbk ▸ ht j k hjk

private theorem reverse_oneHot {s t : Fin n → Fin q} (i : Fin n)
    (hne : s i ≠ t i) (heq : ∀ j, j ≠ i → s j = t j) :
    reverse (oneHot s) (i, t i) = union s t := by
  funext ⟨j, a⟩
  rcases eq_or_ne j i with rfl | hj
  · rcases eq_or_ne a (t j) with rfl | ha
    · simp [reverse, oneHot, union, hne]
    · simp [reverse, oneHot, union, ha, ha.symm]
  · simp [reverse, oneHot, union, hj, heq j hj]

private theorem lift_step {s t : Fin n → Fin q} (hst : Step H s t) :
    (PortGraph.network H n).sourceGraph.Reachable (oneHot s) (oneHot t) := by
  obtain ⟨hs, ht, i, hne, heq⟩ := hst
  have hu := legal_union H hs ht i heq
  have hlast : (PortGraph.network H n).sourceGraph.Step (oneHot t) (union s t) :=
    ⟨(legal_oneHot_iff H t).mpr ht, hu, (i, s i),
      (funext fun _ => by simp only [union, or_comm]).trans
        (reverse_oneHot i hne.symm fun j hj => (heq j hj).symm).symm⟩
  exact (Relation.ReflTransGen.single ⟨(legal_oneHot_iff H s).mpr hs, hu, (i, t i),
    (reverse_oneHot i hne heq).symm⟩).tail hlast.symm

/-- Single-symbol word paths correspond exactly to selector paths between unique selections. -/
theorem reachable_oneHot_iff {s t : Fin n → Fin q} :
    (PortGraph.network H n).sourceGraph.Reachable (oneHot s) (oneHot t) ↔ Reachable H s t := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨v, hv, htv⟩ := decode_reachable H hr s fun _ => by simp [oneHot]
    exact (funext fun i => (of_decide_eq_true (htv i)).symm : v = t) ▸ hv
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.trans (lift_step H hm)

namespace PortGraph

/-- Canonical one-hot physical configurations are legal exactly for compatible words. -/
theorem legal_oneHot_iff (w : Fin n → Fin q) :
    (network H n).graph.Legal ((network H n).encode (HWord.oneHot w)) ↔ HWord.Legal H w :=
  (SelectorNetwork.legal_encode_iff _ _).trans
    (HWord.legal_oneHot_iff H w)

/-- The concrete, well-formed weighted graph preserves and reflects word reconfiguration. -/
theorem reachable_oneHot_iff (s t : Fin n → Fin q) :
    (network H n).graph.Reachable ((network H n).encode (HWord.oneHot s))
      ((network H n).encode (HWord.oneHot t)) ↔ HWord.Reachable H s t := by
  refine (?_ : _ ↔ (network H n).sourceGraph.Reachable _ _).trans (HWord.reachable_oneHot_iff H)
  simpa only [SelectorNetwork.simulation_enc] using
    (network H n).simulation.reachable_enc_iff (a := HWord.oneHot s) (a' := HWord.oneHot t)

end PortGraph
end Cslib.Complexity.NCL.HWord
