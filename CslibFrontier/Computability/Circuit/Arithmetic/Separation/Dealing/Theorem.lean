/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Compose
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Parts
import CslibFrontier.Foundations.Data.List.Blocks

/-!
# The dealing program

The program `G` of [AnthropicVPVNP2026] (the proof of Theorem J.3) is a formula of the tree
machine of one shape (`dealFormula`): it writes the word of its argument, cuts it into parts that
it writes into a trie at given paths, runs a first list of steps and then a second one, and fills
a list of templates. Its weighted values are the filled templates, one list for every state after
the steps, and the weighted sum of the products of the plain sums of the filled templates is the
sum over those states (`dealFormula_does`); its cost is the cost of the word, of the parts, of the
steps and of the templates. With injective codes of names, the trie after the parts is a state by
names (`gets_partsT`).

## Main definitions

* `dealFormula`: the dealing program, for given steps and templates.

## Main results

* `dealFormula_does`: what the dealing program computes, and at which cost.
* `gets_partsT`: the parts written at the codes of names.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54). Ported from the source module `Nc.Dl.DealThm`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Interpreter Interpreter.Tree

section Program

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The dealing program: the word of the argument, with `t0` for a leaf and `t1` for a node, cut
into parts of `KT.val nl` letters at the paths `names`; the steps `sts` and then `sts'`, guessing
bit lists of `KT.val nub` bits; and the templates `ts`. -/
@[expose] def dealFormula (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool)
    (sts sts' : List DStep) (ts : List Tm) : Fm :=
  lett (dstepsF nub sts (partsF names nl (wordF t0 t1 .id)))
    (lett (dstepsF nub sts' .id) (tmsF ts .id))

/-- **The dealing program.** Let the steps `sts` cost at most `c` each along every run from the
trie of the parts of the word of `z` (an invariant `I` of the remaining steps and the state), and
let every state after them have an invariant for the steps `sts'` that bounds their costs by
`c9` in all, and states after which every template costs at most `ct`. Then the dealing program
at `z` makes, at the stated cost, one list of filled templates for every state after all steps,
and the weighted sum of the products of their plain sums is the sum over those states. -/
theorem dealFormula_does (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool)
    (sts sts' : List DStep) (ts : List Tm) (z : Tree) {Ln : ℕ} (hn : ∀ p ∈ names, p.length ≤ Ln)
    {I : List DStep → (List Bool → Tree) → Prop} {c : DStep → ℕ} {ct c9 : ℕ}
    (hI : ∀ st sts' σ, I (st :: sts') σ → st.cost (KT.val nub) nub.length σ ≤ c st ∧
      ∀ σ' ∈ st.exec (KT.val nub) σ, I sts' σ')
    (hI0 : I sts (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))))
    (h9 : ∀ σ ∈ execAll (KT.val nub) sts (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))),
      (∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
        (∀ st sts'' σ, I' (st :: sts'') σ → st.cost (KT.val nub) nub.length σ ≤ c' st ∧
          ∀ σ' ∈ st.exec (KT.val nub) σ, I' sts'' σ') ∧ I' sts' σ ∧
            (sts'.map fun st => c' st + 30).sum ≤ c9) ∧
      ∀ σ' ∈ execAll (KT.val nub) sts' σ, ∀ t ∈ ts, t.cost σ' ≤ ct) :
    ∃ Q : List (A × Tree),
      Does θ (dealFormula t0 t1 names nl nub sts sts' ts) z Q (60 * z.size +
        (z.size + names.length) * (60 * nl.length + 100) + names.length * (60 * Ln + 130) +
        (sts.map fun st => c st + 30).sum + c9 + ts.length * (ct + 60) + 300) ∧
      (∀ q ∈ Q, ∃ σ ∈ execAll (KT.val nub) (sts ++ sts')
        (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))),
          q.2 = listT (ts.map fun t => t.expand σ)) ∧
      wsum Q (Cut.pvProd θ) = ((execAll (KT.val nub) (sts ++ sts')
        (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z)))).map
          fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum := by
  generalize hσ0 : gets (partsT (KT.val nl) names .nil (wordT t0 t1 z)) = σ0 at hI0 h9 ⊢
  have hw := partsF_gives (wordF_gives (t0 := t0) (t1 := t1) (Gives.id (θ := θ) z)) names nl Ln hn
  rw [length_wordT] at hw
  obtain ⟨Q1, d1, m1, s1⟩ := dstepsF_does (θ := θ) nub sts hw hI (hσ0 ▸ hI0)
  rw [hσ0] at m1 s1
  -- the steps `sts'` and the templates, from every state after `sts`
  have h2 (W : Tree) : ∃ Q : List (A × Tree), gets W ∈ execAll (KT.val nub) sts σ0 →
      Does θ (lett (dstepsF nub sts' .id) (tmsF ts .id)) W Q (c9 + ts.length * (ct + 60) + 150) ∧
      (∀ q ∈ Q, ∃ σ ∈ execAll (KT.val nub) sts' (gets W),
        q.2 = listT (ts.map fun t => t.expand σ)) ∧
      wsum Q (Cut.pvProd θ) = ((execAll (KT.val nub) sts' (gets W)).map
        fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum := by
    by_cases hW : gets W ∈ execAll (KT.val nub) sts σ0
    swap
    · exact ⟨[], fun h => absurd h hW⟩
    obtain ⟨⟨I', c', hI', hI0', hc'⟩, ht⟩ := h9 _ hW
    obtain ⟨Q2, d2, m2, s2⟩ := dstepsF_does (θ := θ) nub sts' (Gives.id (θ := θ) W) hI' hI0'
    have d3 := Gives.after (G := tmsF ts .id)
      (f := fun W' => listT (ts.map fun t => t.expand (gets W'))) d2
      (d := 1 + ts.length * (ct + 60) + 30) fun q hq =>
        tmsF_gives (Gives.id (θ := θ) q.2) fun t htt => ht _ (m2 q hq) t htt
    refine ⟨_, fun _ => ⟨d3.mono (by omega), fun q hq => ?_, ?_⟩⟩
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact ⟨_, m2 q' hq', rfl⟩
    · rw [← s2]
      simp only [wsum, List.map_map, Function.comp_def, Cut.pvProd, toList_listT]
  choose R hR using h2
  have d4 := d1.lett (G := lett (dstepsF nub sts' .id) (tmsF ts .id)) (R := R)
    (d := c9 + ts.length * (ct + 60) + 150) fun q hq => (hR q.2 (m1 q hq)).1
  refine ⟨_, d4.mono (by omega), fun p hp => ?_, ?_⟩
  · obtain ⟨q, hq, r, hr, e, -⟩ := mem_bindW hp
    obtain ⟨σ, hσ, h⟩ := (hR q.2 (m1 q hq)).2.1 r hr
    exact ⟨σ, by rw [execAll_append, List.mem_flatMap]; exact ⟨_, m1 q hq, hσ⟩, by rw [e, h]⟩
  · rw [wsum_bindW, wsum_congr (φ' := fun W => ((execAll (KT.val nub) sts' (gets W)).map
      fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum) fun q hq => (hR q.2 (m1 q hq)).2.2,
      execAll_append, List.sum_map_flatMap]
    exact s1 fun σ => ((execAll (KT.val nub) sts' σ).map fun σ' =>
      (ts.map fun t => pv θ (t.expand σ')).prod).sum

end Program

section Parts

variable {ν : Type*} {nm : ν → List Bool}

/-- **The parts at names.** Writing the parts of `m` elements of `l` at the codes of the distinct
names `xs` into a trie whose values are the state by names `st` gives a state by names in which
the name `xs[k]` has the part `k`, reversed, and the other names keep their values. -/
theorem gets_partsT (hnm : Injective nm) (m : ℕ) (xs : List ν) (hxs : xs.Nodup) (W : Tree)
    (l : List Tree) (st : ν → Tree) (hW : gets W = extend nm st fun _ => .nil) :
    ∃ st' : ν → Tree, gets (partsT m (xs.map nm) W l) = extend nm st' (fun _ => .nil) ∧
      (∀ k (h : k < xs.length), st' xs[k] = listT ((l.drop (k * m)).take m).reverse) ∧
      ∀ y, y ∉ xs → st' y = st y := by
  classical
  induction xs generalizing W l st with
  | nil => exact ⟨st, hW, fun k h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | cons x xs ih =>
    rw [List.nodup_cons] at hxs
    rw [List.map_cons, partsT]
    obtain ⟨st', h1, h2, h3⟩ := ih hxs.2 (tset (nm x) (listT (l.take m).reverse) W) (l.drop m)
      (update st x (listT (l.take m).reverse)) (by rw [gets_tset, hW, hnm.extend_update])
    refine ⟨st', h1, fun k h => ?_, fun y hy => ?_⟩
    · cases k with
      | zero => simp [h3 x hxs.1]
      | succ k =>
        rw [List.getElem_cons_succ, h2 k (by simpa using h), List.drop_drop, Nat.succ_mul,
          Nat.add_comm]
    · rw [List.mem_cons, not_or] at hy
      rw [h3 y hy.2, update_of_ne hy.1]

end Parts

end Cslib.Circuits.Arithmetic.Separation.Dealing
