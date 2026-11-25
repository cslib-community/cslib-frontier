/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.SMN
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.DescriptionLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.TotalComputability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.RiceDispatch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-!
# Rice's theorem

Every nontrivial property of the behavior of machines is undecidable on their descriptions
(`Turing.MultiTapeTM.rice`) [Rice][Rice1953] [Sipser, Problem 5.28][Sipser2013]. The behavior of
the machine described by a word `w` (`Turing.MultiTapeTM.behavior`) relates each input of bits on
which it halts to the output it halts with; a property of behaviors is nontrivial when the
machine described by some word has it and the machine described by another does not. Equivalently,
a set of words that depends only on the behavior of the machines they describe, and is neither
empty nor everything, is undecidable (`Turing.MultiTapeTM.not_isDecidable_of_behavior`).

The proof goes through the two-way case of Kleene's recursion theorem
(`Turing.MultiTapeTM.exists_behavior_eq`) [Sipser, Theorem 6.3][Sipser2013]: for every computable
verdict `f` on words and descriptions `d false` and `d true`, some word `e` describes a machine
behaving as `d (f e)`. The full theorem allows any computable transformation of descriptions in
place of the choice between `d false` and `d true`; the choice is all that Rice's theorem needs.
Applied to a decider of the property, with `d true` outside the property and `d false` inside it,
it gives a word describing a machine inside the property exactly when it is outside. For each
input of bits `x`, halting on `x` is such a property (`Turing.MultiTapeTM.not_isDecidable_halts`),
the native form of Mathlib's `ComputablePred.halting_problem`.

The recursion theorem is Kleene's construction, from two constructions on descriptions. The s-m-n
theorem builds an input prefix into a description (`Turing.MultiTapeTM.Universal.hardwire`), in
polynomial time. Dispatching (`Turing.MultiTapeTM.Universal.dispatch`) runs a machine computing a
total function, keeping its output on a work tape, and then runs `d b` on that output without its
first bit `b` (`Turing.MultiTapeTM.Universal.Desc.computes_dispatch`). Let `t` describe the
machine that reads a word `y` before its input `x` and dispatches on `f (s y) :: x`, where `s y`
describes the machine described by `y` with `y` built in. Then `e = s t` describes a machine that
runs the machine described by `t` on `y = t` and `x`, so behaves as `d (f (s t))`. No universal
machine is needed: `d false` and `d true` are fixed, and their transitions are part of the
description of the dispatching machine, reading their input from the work tape as in
`Turing.MultiTapeTM.Universal.Redirect.redirect`. The dispatch program and its clean-machine run
proof are confined to `Internal.RiceDispatch`; ordinary imports of this facade expose the
computability and Rice statements without that machine-level premise.

## Main definitions

* `Turing.MultiTapeTM.behavior`: the behavior of the machine described by a word.

## Main results

* `Turing.MultiTapeTM.Universal.find?_desc`: transition lookup in a machine description.
* `Turing.MultiTapeTM.exists_behavior_eq`: the two-way case of the recursion theorem.
* `Turing.MultiTapeTM.rice`, `Turing.MultiTapeTM.not_isDecidable_of_behavior`: Rice's theorem.
* `Turing.MultiTapeTM.not_isDecidable_halts`: halting on a fixed input is undecidable.

## References

* [H. G. Rice, *Classes of Recursively Enumerable Sets and Their Decision Problems*][Rice1953]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM


open Universal

/-! ### The recursion theorem and Rice's theorem -/

/-- The behavior, on inputs of bits, of the machine described by the word `w`: the relation
between the inputs on which it halts and the outputs it halts with. -/
def behavior (w x : List Bool) (o : List ℕ) : Prop :=
  (decodeDesc w).Computes (x.map eBit) o

/-- Building the description of a word into itself, as an input prefix, is computable in
polynomial time. -/
theorem computableInPolyTime_selfHardwire :
    ComputableInPolyTime (fun y : List Bool => eDesc (hardwire (decodeDesc y) (frame y)))
      encBits encBits := by
  obtain ⟨_, _, hdec⟩ := exists_computableInDegree_decodeDesc
  exact (ComputableInPolyTime.of_eq (f := fun d : Desc => eDesc d) (encIn := eDesc)
    (encOut := encBits) fun _ => rfl).comp
      (computableInPolyTime_hardwire.comp (hdec.computableInPolyTime.prod (.bitsFrame encBits)))

/-- **Kleene's recursion theorem, in its two-way case.** For every computable verdict `f` on words
and descriptions `d false`, `d true`, some word `e` describes a machine behaving on inputs of bits
as `d (f e)` does: a machine can make its whole behavior depend on a computable verdict about its
own description. The full recursion theorem allows any computable transformation of descriptions
in place of the choice between `d false` and `d true`. The proof is Kleene's construction: a
machine reads a word `y` before its input, computes the verdict on the description of the machine
described by `y` with `y` built in, and dispatches on it; `e` is that description for `y` the
description of the machine itself. -/
theorem exists_behavior_eq {f : List Bool → Bool} (hf : IsComputable f encBits encBool)
    (d : Bool → Desc) : ∃ e : List Bool, ∀ (x : List Bool) (o : List ℕ),
      (decodeDesc e).Computes (x.map eBit) o ↔ (d (f e)).Computes (x.map eBit) o := by
  set s : List Bool → List Bool := fun y => eDesc (hardwire (decodeDesc y) (frame y))
  have hs : IsComputable s encBits encBits := computableInPolyTime_selfHardwire.isComputable
  have hg : IsComputable (fun p : List Bool × List Bool => f (s p.1) :: p.2)
      (encPair encBits encBits) encBits :=
    (ComputableInPolyTime.bitsCons (.fst _ _) (.snd _ _)).isComputable.comp
      ((hf.comp (hs.comp (ComputableInPolyTime.fst encBits encBits).isComputable)).prod
        (ComputableInPolyTime.snd encBits encBits).isComputable)
  obtain ⟨_, _, k, State, hfin, tm, htm⟩ := Internal.TotalComputability.normalizedMachine hg
  have := Fintype.ofFinite State
  set eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set T := dispatch eS tm d
  have hsT : s (eDesc T) = eDesc (hardwire T (frame (eDesc T))) := by
    simp only [s, decodeDesc_eDesc]
  refine ⟨s (eDesc T), fun x o => ?_⟩
  rw [hsT, decodeDesc_eDesc, Desc.computes_hardwire, ← hsT]
  exact Desc.computes_dispatch (w := frame (eDesc T) ++ x) (b := f (s (eDesc T))) (v := x) eS
    tm d (htm (eDesc T, x)) o

/-- **Rice's theorem.** Every nontrivial property of the behavior of machines is undecidable on
their descriptions: if `C` contains the behavior of the machine described by some word and not that
of the machine described by another, then the set of words describing machines whose behavior is
in `C` is undecidable [Rice][Rice1953] [Sipser, Problem 5.28][Sipser2013]. -/
theorem rice {C : Set (List Bool → List ℕ → Prop)} {w₀ w₁ : List Bool} (h₀ : behavior w₀ ∉ C)
    (h₁ : behavior w₁ ∈ C) : ¬IsDecidable {w | behavior w ∈ C} encBits := by
  intro hdec
  obtain ⟨f, hf, hP⟩ := hdec.exists_isComputable
  obtain ⟨e, he⟩ := exists_behavior_eq hf fun b => decodeDesc (if b then w₀ else w₁)
  have hmem := hP e
  rw [Set.mem_ofPred_eq, show behavior e = behavior (if f e then w₀ else w₁) from
    funext fun x => funext fun o => propext (he x o)] at hmem
  cases hfe : f e <;> simp_all

/-- **Rice's theorem, for sets of words.** A set of words that holds of a word or not according to
the behavior of the machine it describes, and is neither empty nor everything, is undecidable.
This is the counterpart of Mathlib's `ComputablePred.rice₂` for partial recursive codes. -/
theorem not_isDecidable_of_behavior {P : Set (List Bool)}
    (hP : ∀ w w', behavior w = behavior w' → w ∈ P → w' ∈ P) {w₀ w₁ : List Bool} (h₀ : w₀ ∉ P)
    (h₁ : w₁ ∈ P) : ¬IsDecidable P encBits := by
  have hset : {w | behavior w ∈ {B | ∃ w ∈ P, behavior w = B}} = P := by
    ext w
    exact ⟨fun ⟨w', hw', h⟩ => hP w' w h hw', fun hw => ⟨w, hw, rfl⟩⟩
  rw [← hset]
  exact rice (fun ⟨w, hw, h⟩ => h₀ (hP w w₀ h hw)) ⟨w₁, h₁, rfl⟩

/-! ### Halting on a fixed input -/

section FixedInput

open Universal.Redirect

/-- A description without transitions: it halts at once. -/
private def haltDesc : Desc := ⟨0, 0, []⟩

/-- A description staying in place forever on every input of bits. -/
private def loopDesc : Desc := ⟨0, 0, bitSyms.map fun i => (⟨0, i, []⟩, ⟨.zero, [], none, some 0⟩)⟩

private theorem computes_haltDesc (x : List ℕ) : haltDesc.Computes x [] :=
  ⟨1, rfl⟩

private theorem iterate_stepOut_loopDesc (x : List Bool) (t : ℕ) :
    (stepOut loopDesc (x.map eBit))^[t] (init loopDesc, []) = (init loopDesc, []) := by
  have he : ((⟨0, inputSymbol (x.map eBit) 1, []⟩, ⟨.zero, [], none, some 0⟩) : Key × Act) ∈
      loopDesc.table := List.mem_map.mpr ⟨_, inputSymbol_map_eBit_mem x 1, rfl⟩
  have hf := find?_eq_some_of_mem he fun e' he' _ => by
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp he'
    rfl
  exact Function.iterate_fixed
    (by rw [stepOut, step_of_find? (c := init loopDesc) (q := 0) rfl hf]; rfl) t

private theorem not_computes_loopDesc (x : List Bool) (o : List ℕ) :
    ¬loopDesc.Computes (x.map eBit) o := fun ⟨t, ht⟩ => by
  have := congrArg Prod.snd ht
  simp only [simulate, iterate_stepOut_loopDesc] at this
  exact Bool.false_ne_true this

/-- **Halting on a fixed input is undecidable**: for every input of bits `x`, no computable
function decides, of a word, whether the machine it describes halts on `x`. This is the native
counterpart of Mathlib's `ComputablePred.halting_problem`, a corollary of Rice's theorem. -/
theorem not_isDecidable_halts (x : List Bool) :
    ¬IsDecidable {w | (decodeDesc w).Halts (x.map eBit)} encBits := by
  have hset : {w | (decodeDesc w).Halts (x.map eBit)} =
      {w | behavior w ∈ {B : List Bool → List ℕ → Prop | ∃ o, B x o}} := by
    ext w
    exact Desc.halts_iff_exists_computes
  rw [hset]
  refine rice (w₀ := eDesc loopDesc) (w₁ := eDesc haltDesc) (fun ⟨o, h⟩ => ?_) ⟨[], ?_⟩
  · rw [behavior, decodeDesc_eDesc] at h
    exact not_computes_loopDesc x o h
  · rw [behavior, decodeDesc_eDesc]
    exact computes_haltDesc _

end FixedInput

end Turing.MultiTapeTM
