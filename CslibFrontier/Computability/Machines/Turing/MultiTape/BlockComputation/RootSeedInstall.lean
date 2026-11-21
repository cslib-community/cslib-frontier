/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootBalanceRequest
public import CslibFrontier.Computability.PolyTime.SeedChoice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Installing a chosen seed in the raw root request

One linear pass retains the schedule and graph size. Only the short seed context and
quantified choices are sent to the coefficient decoder. The four decoded coefficients
replace the template fields and the balance request receives the unconsumed moves.
-/

public section

namespace Turing.MultiTapeTM.RootSeedInstall

open Cslib RootBalanceRequest

private def fields (x : Input) : SeededPredecessor.Context × List Bool :=
  ((rootQuery x).context, x.2)

/-- Replace the seed and retain the graph and the choices following its coefficient word. -/
@[expose] def install (x : Input) : Input :=
  let data := SeedChoice.install ((rootQuery x).context, x.2)
  (({ rootQuery x with context := data.1 }, edgeCount x), data.2)

/-- Installing a seed does not touch the shared schedule or copy counts. -/
@[simp] theorem install_raw (x : Input) : (rootQuery (install x)).raw = (rootQuery x).raw := rfl

/-- The represented chosen seed and trailing rank challenge recover the exact intended request. -/
theorem install_word (p : Public)
    (s : BalancedSchedules.SeededLabels.Seed p.1.context.universeSize (6 * p.1.context.labelLength))
    (rest : List Bool) :
    install (p, SeedChoice.word s ++ rest) =
      (({p.1 with context := {p.1.context with c0 := s 0, c1 := s 1, c2 := s 2, c3 := s 3}},
        p.2), rest) := by
  simp [install, SeedChoice.install_word]

private theorem fields_deg : ComputableInDegree fields encInput SeedChoice.encData 1 1 := by
  have hp := ComputableInDegree.fst encPublic encBits
  have hg := (ComputableInDegree.fst RootPredecessorQuery.encInput encNat).comp hp
  exact (RootPredecessorQuery.encInput_context_deg.comp hg).prod (ComputableInDegree.snd _ _)

private theorem fields_size :
    PolyBounded shortSize (fun x => (SeedChoice.encData (fields x)).length) := by
  apply PolyBounded.of_forall_le 2 1
  intro x
  simp only [SeedChoice.encData, fields, length_encPair, encBits_apply, pow_one,
    shortSize, RootPredecessorQuery.shortSize]
  omega

/-- The installed record's arithmetic input is polynomial in the short fields and all choices. -/
theorem install_size : PolyBounded shortSize (shortSize ∘ install) := by
  have hd := SeedChoice.computableInPolyTime_install.polyBounded_length.comp
    (g := fields) fields_size
  refine (PolyBounded.self.add hd).mono ?_
  intro x
  have hh : (SeedChoice.install (fields x)).1 = (rootQuery (install x)).context := rfl
  have ht : (SeedChoice.install (fields x)).2 = (install x).2 := rfl
  simp only [Function.comp_apply, SeedChoice.encData, length_encPair, encBits_apply, hh, ht,
    shortSize, RootPredecessorQuery.shortSize, install_raw]
  change _ ≤ _ + (2 * _ + 1 + _)
  change (rootQuery x).raw.length.size + (rootQuery x).copies.size + _ + 1 +
    (edgeCount x).size + _ + 1 ≤ _
  omega

/-- Input preparation costs linear raw length plus a polynomial in the encoded metadata.
The polynomial decoder never receives the raw schedule. -/
theorem exists_computableInO : ∃ d, ComputableInO install encInput encInput
    (fun x => (rootQuery x).raw.length + shortSize x ^ d)
    (fun x => (rootQuery x).raw.length + shortSize x ^ d) := by
  have hp := ComputableInDegree.fst encPublic encBits
  have hg := (ComputableInDegree.fst RootPredecessorQuery.encInput encNat).comp hp
  have hn := (ComputableInDegree.snd RootPredecessorQuery.encInput encNat).comp hp
  have hr := (RootPredecessorQuery.encInput_raw_deg.comp hg).inO_one
  have hm := (RootPredecessorQuery.encInput_copies_deg.comp hg).inO_one
  obtain ⟨T, S, hT, hS, hs⟩ := SeedChoice.computableInPolyTime_install.exists_computableInO
  have hd := hs.comp fields_deg.inO_one
  have hc := (ComputableInDegree.fst SeededPredecessor.encContext encBits).inO_one.comp_linear hd
  have hw := (ComputableInDegree.snd SeededPredecessor.encContext encBits).inO_one.comp_linear hd
  have hgraph := (hr.prod (hm.prod hc)).of_enc_eq
    (g := fun x => rootQuery (install x)) (encC := RootPredecessorQuery.encInput) (fun _ => rfl)
  have h := (hgraph.prod hn.inO_one).prod hw
  let cost (x : Input) := 40 * (shortSize x + 2) + 2 * (T (fields x) + S (fields x))
  have hcost : PolyBounded shortSize cost :=
    ((PolyBounded.const 40).mul (PolyBounded.self.add (.const 2))).add
      ((PolyBounded.const 2).mul ((hT.comp (g := fields) fields_size).add (hS.comp fields_size)))
  obtain ⟨c, d, hu⟩ := hcost.exists_le_linear_add_pow (fun x => (rootQuery x).raw.length) 40
    (fun x => by simp [shortSize])
  refine ⟨d, h.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hu x) <;> have hh := length_encInput_le x <;>
    change (encInput x).length + ((encInput x).length + ((encInput x).length + _)) +
      (encInput x).length + ((encInput x).length + _) ≤ 40 * (rootQuery x).raw.length + cost x <;>
    dsimp only [cost] <;> omega

/-- Installing the coefficient fields and preparing the rank inputs share one sharp clock. -/
theorem exists_prepare_inO : ∃ d, ComputableInO (fun x => prepare (install x)) encInput encOutput
    (fun x => (rootQuery x).raw.length + shortSize x ^ d)
    (fun x => (rootQuery x).raw.length + shortSize x ^ d) := by
  obtain ⟨i, hi⟩ := exists_computableInO
  obtain ⟨j, hj⟩ := RootBalanceRequest.exists_computableInO
  have h := hj.comp hi
  have hu := (PolyBounded.self (size := shortSize)).pow i |>.add (install_size.pow j)
  obtain ⟨c, d, hc⟩ := hu.exists_le_linear_add_pow (fun x => (rootQuery x).raw.length) 2
    (fun x => by simp [shortSize])
  refine ⟨d, h.mono c (fun x => ?_) (fun x => ?_)⟩ <;> refine le_trans ?_ (hc x) <;>
    change (rootQuery x).raw.length + shortSize x ^ i +
      ((rootQuery (install x)).raw.length + _) ≤ _ <;>
    simp only [Function.comp_apply, install_raw] <;> omega

end Turing.MultiTapeTM.RootSeedInstall
