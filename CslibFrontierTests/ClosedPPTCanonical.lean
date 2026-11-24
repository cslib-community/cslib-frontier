/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.Finite
public import CslibFrontier.Computability.Probabilistic.Parameter
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Tactic.PolyTime

/-!
# Canonical plain closed-PPT clients

The clients compute words before sampling, retain caller data in sampled branches and traversal,
and discharge the invariant and size premises of a captured-input loop. Zero rounds and empty
finite/traversal inputs are included. All imports use the ordinary module boundary.
-/

public section

namespace CslibFrontierTests.ClosedPPTCanonical

open Cslib Cslib.Probability Turing.MultiTapeTM

assert_not_exists Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPTOn
assert_not_exists Cslib.Probability.IsPPTOn.cond'
assert_not_exists Cslib.Probability.IsPPTOn.ite'
assert_not_exists Cslib.Probability.IsPPTOn.iterateWith_spec'
assert_not_exists Cslib.Probability.IsPPTOn.iterate_of_length_le'

/-- A concrete word producer uses a plain deterministic certificate. -/
def mark (word : List Bool) : List Bool := word ++ [true]

theorem mark_polyTime : ComputableInPolyTime mark encBits encBits :=
  ComputableInPolyTime.bitsAppend ComputableInPolyTime.id' (.const [true])

example : IsPPTOn encBits encBits (fun word => pure (mark word)) := mark_polyTime.isPPTOn

example : mark [] = [true] ∧ mark [false, true] = [false, true, true] := ⟨rfl, rfl⟩

/-- A sampled value is paired with the complete original word. -/
noncomputable def retainedBit (word : List Bool) : ProbComp (List Bool × Bool) :=
  (fun bit => (word, bit)) <$> ProbComp.uniform Bool

theorem retainedBit_isPPTOn : IsPPTOn encBits (encPair encBits encBool) retainedBit :=
  (isPPTOn_uniform_bool encBits).pair ComputableInPolyTime.id'

/-- A plain computed guard selects sampling or an input-correlated pure result. -/
noncomputable def selected (word : List Bool) : ProbComp (List Bool × Bool) :=
  if word.headD false then retainedBit word else pure (word, false)

example : IsPPTOn encBits (encPair encBits encBool) selected :=
  IsPPTOn.cond (by fun_prop) retainedBit_isPPTOn
    (ComputableInPolyTime.id'.prod (.const false)).isPPTOn

example : selected [] = pure ([], false) := rfl

example : selected [false, true] = pure ([false, true], false) := rfl

example (word : List Bool) :
    ProbComp.eval (Prod.fst <$> retainedBit word) = PMF.pure word := by
  simp only [retainedBit, ProbComp.eval_map, PMF.map_comp, Function.comp_def]
  exact PMF.map_const _ _

/-- The captured first bit selects sampling or preservation of the one-bit state. -/
noncomputable def sampledStep (word : List Bool) (state : Bool) : ProbComp Bool :=
  if word.headD false then ProbComp.uniform Bool else pure state

theorem sampledStep_isPPTOn : IsPPTOn (encPair encBits encBool) encBool
    (fun pair => sampledStep pair.1 pair.2) :=
  IsPPTOn.cond (by fun_prop) (isPPTOn_uniform_bool (encPair encBits encBool))
    (ComputableInPolyTime.snd encBits encBool).isPPTOn

noncomputable def sampledLoop (word : List Bool) : ProbComp Bool :=
  OracleComp.iterate word.length (sampledStep word) false

-- Every supported prefix has the one-bit bound; the invariant additionally records the pure arm.
example : IsPPTOn encBits encBool sampledLoop ∧
    ∀ word state, state ∈ (ProbComp.eval (sampledLoop word)).support →
      word.headD false = false → state = false := by
  exact IsPPTOn.iterateWith_spec ComputableInPolyTime.length_bits (.const false)
    sampledStep_isPPTOn (fun word _ state => word.headD false = false → state = false)
    (fun _ _ => rfl) (by
      intro word _ state _ hstate next hnext hfalse
      have hstep : sampledStep word state = pure state := by
        unfold sampledStep
        rw [hfalse]
        rfl
      have hnext : next = state := by simpa [hstep] using hnext
      subst next
      exact hstate hfalse)
    (size := fun _ => 1) (.const 1) (fun _ _ _ _ _ => by simp)

example : sampledLoop [] = pure false := rfl

example : ProbComp.eval (sampledLoop []) = PMF.pure false := by simp [sampledLoop]

/-- The parameter is unary data, followed by the auxiliary word in its original order. -/
def parameterized (n : ℕ) (word : List Bool) : ProbComp (List Bool) :=
  pure (List.replicate n true ++ word)

theorem parameterized_isPPT : IsPPT encBits parameterized := by
  have hparameter : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 true)
      (encPair encUnary encBits) encBits :=
    (ComputableInPolyTime.fst encUnary encBits).of_enc_eq (fun _ => rfl)
  exact (ComputableInPolyTime.bitsAppend hparameter
    (ComputableInPolyTime.snd encUnary encBits)).isPPTOn

example : IsPPTOn encBits encBits (fun word => parameterized word.length (mark word)) :=
  parameterized_isPPT.preprocess ComputableInPolyTime.length_bits mark_polyTime

example : parameterized 1 [false] = pure [true, false] := rfl

-- Finite dispatch retains its empty-input case without adding an inhabitance premise.
example (empty : Empty ↪ List Bool) :
    IsPPTOn empty encBool (fun _ : Empty => pure false) := by
  exact IsPPTOn.finite_cases (tagEncoding := empty) (tag := id)
    (branch := fun _ _ => pure false) ComputableInPolyTime.id' (fun tag => Empty.elim tag)

/-- Pair every traversed bit with the retained caller; pair preparation charges the whole word. -/
def pairedTraverse (bits : List Bool) (word : List Bool) : ProbComp (List (List Bool × Bool)) :=
  bits.mapM (fun bit => pure (word, bit))

example (bits : List Bool) :
    IsPPTOn encBits (encList (encPair encBits encBool)) (pairedTraverse bits) :=
  IsPPTOn.mapMWith (ComputableInPolyTime.id'.isPPTOn) (ComputableInPolyTime.const bits)

example (word : List Bool) : pairedTraverse [] word = pure [] := rfl

example : pairedTraverse [false, true] [true] = pure [([true], false), ([true], true)] := by
  simp [pairedTraverse]

end CslibFrontierTests.ClosedPPTCanonical
