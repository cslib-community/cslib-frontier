/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAlgorithm
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives

/-!
# The ground endpoint claim of a recursive lookup

On the marked schedule, copy count, parent edge and two proposed vertex numbers, the machine
runs the actual root lookup and checks both returned keys. Rejected addresses have no endpoint
witness. Only short binary keys enter the final equality comparison.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointCheck

/-- The two proposed binary keys precede the existing marked schedule request. -/
abbrev Input := (ℕ × ℕ) × RootEndpointQuery.Input

abbrev encEnds := encPair encNat encNat
abbrev encInput := encPair encEnds RootEndpointInput.encInput

/-- Size of all fields used for binary arithmetic and equality. -/
@[expose] def shortSize (a : Input) : ℕ :=
  (encEnds a.1).length + RootEndpointInput.shortSize a.2 + 1

/-- A malformed schedule or a padded edge rejects every proposed pair. -/
@[expose] def check (k : ℕ) (a : Input) : Bool :=
  decide (RootEndpointQuery.query k a.2 = some a.1)

/-- Ground endpoint membership on a serialized query takes linear time in the raw movements
plus a fixed polynomial in the binary metadata. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (check k) encInput encBool
    (fun a => a.2.raw.length + shortSize a ^ d) (fun a => a.2.raw.length + shortSize a ^ d) := by
  obtain ⟨d₀, hroot⟩ := RootEndpointAlgorithm.exists_computableInO k
  have hr := hroot.comp (ComputableInDegree.snd encEnds RootEndpointInput.encInput).inO_one
  have ho : ComputableInDegree some encEnds RootEndpointFinish.encOutput 1 1 :=
    ComputableInDegree.optionSome
  have hg := (ho.comp (ComputableInDegree.fst encEnds RootEndpointInput.encInput)).inO_one
  have checkO := ComputableInO.eq' hr hg
  let sizeOut (a : Input) := (RootEndpointFinish.encOutput (RootEndpointQuery.query k a.2)).length
  let sizeGuess (a : Input) := (RootEndpointFinish.encOutput (some a.1)).length
  have hs (a : Input) : RootEndpointInput.shortSize a.2 ≤ shortSize a := by
    unfold shortSize
    omega
  have ho' : PolyBounded shortSize sizeOut :=
    (RootEndpointAlgorithm.length_output_polyBounded k).comp (g := Prod.snd)
      (PolyBounded.self.mono hs)
  have hg' : PolyBounded shortSize sizeGuess := PolyBounded.self.mono (fun a => by
    simp only [sizeGuess, RootEndpointFinish.encOutput, encOption_some, List.length_cons, shortSize,
      encEnds]
    omega)
  let minor (a : Input) := 4 * (shortSize a + 2) + shortSize a ^ d₀ +
    (sizeOut a + 1) * (sizeOut a + sizeGuess a + 1) + (2 * sizeOut a + sizeGuess a + 1)
  have hm : PolyBounded shortSize minor :=
    (((((PolyBounded.const 4).mul (PolyBounded.self.add (PolyBounded.const 2))).add
      (PolyBounded.self.pow d₀)).add ((ho'.add (PolyBounded.const 1)).mul
        ((ho'.add hg').add (PolyBounded.const 1)))).add
        ((((PolyBounded.const 2).mul ho').add hg').add (PolyBounded.const 1)))
  obtain ⟨c, d, h⟩ := hm.exists_le_linear_add_pow (fun a => a.2.raw.length) 5
    (fun a => by simp [shortSize])
  have hlen (a : Input) : (encInput a).length ≤ 2 * a.2.raw.length + 2 * shortSize a + 2 := by
    rw [length_encPair, RootEndpointInput.length_encInput]
    simp only [shortSize, RootEndpointInput.shortSize, Nat.size_eq_bits_len]
    omega
  refine ⟨d, checkO.mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (h a) <;>
    have hp := Nat.pow_le_pow_left (hs a) d₀ <;>
    have hl := hlen a <;>
    dsimp only [minor, sizeOut, sizeGuess, Function.comp_apply, Prod.snd, Prod.fst] <;>
    simp only [length_encPair] at * <;> omega

/-- A finite alternating leaf checks the endpoint claim on its private query tape and
arbitrary outer input. It starts and halts at the stated bound on both answers. -/
theorem exists_evaluator (k : ℕ) :
    ∃ (u : ℕ) (S : Type) (_ : Finite S) (atm : MultiTapeATM (u + 2) Bool S) (C d : ℕ),
      ∀ (a : Input) (outer : List Bool),
        let cfg := (WorkTapePredicate.config outer (encInput a)).withState (some atm.toPTM.initial)
        let time := C * (a.2.raw.length + shortSize a ^ d + 1)
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
          RootEndpointQuery.query k a.2 = some a.1) := by
  obtain ⟨d, h⟩ := exists_computableInO k
  obtain ⟨u, S, hS, runner, c, hr⟩ := WorkTapePredicate.exists_of_inO h
  let atm := MultiTapeATM.ofTMs (fun _ => runner) (fun _ => false)
  refine ⟨u, S, hS, atm, c, d, ?_⟩
  intro a outer
  dsimp only
  rw [MultiTapeATM.haltsWithin_ofTMs_const_iff, MultiTapeATM.acceptsWithin_ofTMs_const_iff]
  rw [show atm.toPTM.initial = runner.q₀ from rfl, hr]
  simp [WorkTapePredicate.config, check, Cfg.withState, tapesCfg]

end Turing.MultiTapeTM.RootEndpointCheck
