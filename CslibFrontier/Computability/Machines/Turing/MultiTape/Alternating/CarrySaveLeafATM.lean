/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeaf
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend

/-!
# Launch an alternating continuation from a carry-save leaf

The machine writes the carry flag, rewinds the path and serializes the six physical query fields.
An arbitrary alternating verifier then reads the query at its origin. The continuation's full clock
is charged once, while the preparation takes time linear in the path and serialized query lengths.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveLeafATM

open MultiTapeTM Cslib.CountingLeaf

private theorem prependView {k K : ℕ} {S P : Type} {host : List Bool}
    (prep : MultiTapeTM K Bool P) (run : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K)
    (start finish : Cfg K Bool Unit host) (view : Cfg k Bool Unit host) (n t : ℕ)
    (hr : prep.runFrom (start.withState (some prep.q₀)) n = finish.withState none)
    (hv : viewCfg e finish = view)
    (ht : run.HaltsWithin t (view.withState (some run.toPTM.initial))) :
    let atm := prependTM prep (run.extendTapes e)
    let cfg := start.withState (some atm.toPTM.initial)
    atm.HaltsWithin (n + t) cfg ∧ (atm.AcceptsWithin (n + t) cfg ↔
      run.AcceptsWithin t (view.withState (some run.toPTM.initial))) := by
  have he : viewCfg e (finish.withState (some (run.extendTapes e).toPTM.toNTM.q₀)) =
      view.withState (some run.toPTM.initial) := by
    change (viewCfg e finish).withState _ = _
    rw [hv]
    rfl
  have hh := (haltsWithin_extendTapes_iff run e t _).mpr (he ▸ ht)
  obtain ⟨hh', ha⟩ := prependTM_spec prep (run.extendTapes e) start finish n t hr hh
  exact ⟨hh', ha.trans ((acceptsWithin_extendTapes_iff run e t _).trans (by rw [he]))⟩

/-- Run the serializer on the physical fields and launch the supplied verifier on its private
work block with the encoded query at cell zero. -/
noncomputable def serialize {k : ℕ} {S : Type} (run : MultiTapeATM (k + 2) Bool S) :=
  prependTM (Serialize.machine.extendTapes (Native.serializerTapes k))
    (run.extendTapes (Fin.natAddEmb 6))

/-- Exact cost and continuation semantics starting from the six fields at their origins. -/
theorem serialize_spec {k : ℕ} {S : Type} (run : MultiTapeATM (k + 2) Bool S)
    (host : List Bool) (q : RawInput) (t : ℕ)
    (ht : run.HaltsWithin t ((WorkTapePredicate.config host (encRawInput q)).withState
      (some run.toPTM.initial))) :
    let start := (Native.initial k host q).withState (some (serialize run).toPTM.initial)
    let time := 2 * (encRawInput q).length + 5 + t
    (serialize run).HaltsWithin time start ∧ ((serialize run).AcceptsWithin time start ↔
      run.AcceptsWithin t ((WorkTapePredicate.config host (encRawInput q)).withState
        (some run.toPTM.initial))) :=
  prependView _ run _ _ _ _ _ t (Native.runFrom_serialize k q host)
    (Native.view_final k host q []) ht

/-- Write the selected carry and rewind the path before serializing and launching the verifier. -/
noncomputable def machine {k : ℕ} {S : Type} (run : MultiTapeATM (k + 2) Bool S) (carry : Bool) :=
  prependTM (CarrySaveLeaf.machine k carry)
    ((serialize run).extendTapes (CarrySaveLeaf.nativeTapes k))

/-- An arbitrary alternating leaf starts from the controller's actual tapes with an additive
preparation time independent of its subsequent work. -/
theorem spec {k : ℕ} {S : Type} (run : MultiTapeATM (k + 2) Bool S)
    (host context count width height bits path unary : List Bool) (frontier : ℤ)
    (status carry : Bool) (t : ℕ) :
    let q := CarrySaveLeaf.query context count width path bits carry
    let leaf := (WorkTapePredicate.config host (encRawInput q)).withState (some run.toPTM.initial)
    let start := (CarrySaveLeaf.initial k host context count width height bits path unary
      frontier status).withState (some (machine run carry).toPTM.initial)
    let time := path.length + 3 + (2 * (encRawInput q).length + 5) + t
    run.HaltsWithin t leaf → (machine run carry).HaltsWithin time start ∧
      ((machine run carry).AcceptsWithin time start ↔ run.AcceptsWithin t leaf) := by
  intro q leaf start time ht
  obtain ⟨hs, ha⟩ := serialize_spec run host q t ht
  have hp := (CarrySaveLeaf.runsBetween k host context count width height bits path unary
    frontier status carry).1
  have hv := CarrySaveLeaf.view_prepared k host context count width height bits path unary
    frontier status carry
  obtain ⟨hh, hr⟩ := prependView _ (serialize run) _ _ _ _ _ _ hp hv hs
  simpa only [time, start, leaf, machine, Nat.add_assoc] using And.intro hh (hr.trans ha)

end Turing.MultiTapeATM.CarrySaveLeafATM
