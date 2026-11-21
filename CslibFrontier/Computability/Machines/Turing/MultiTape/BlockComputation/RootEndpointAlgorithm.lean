/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointResolveShort
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointComplexity
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Mathlib.Data.Nat.Size

/-!
# Root endpoint lookup with a linear raw-schedule charge

For each fixed tape count, the machine prepares a short binary address and obtains two binary
indices from its classification. It supplies the raw schedule and these indices to the bounded
schedule endpoint scanner. A final computation receives the short classification and the scanner's
actual tagged answer. Direct rows and rejected addresses ignore the dummy scan answer.

The composition rules construct ordinary deterministic multitape machines. Only length measurement,
validation, projection, framing and the bounded scan are charged on the long schedule word.
Address arithmetic and answer resolution run on records whose encoded lengths are bounded by a
polynomial in the binary sizes of the schedule length, copy count and edge number.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointAlgorithm

open RootEndpointInput (shortSize)

/-- The two indices consumed by the certified schedule scan, together with the original raw word. -/
private def request (k : ℕ) (a : RootEndpointQuery.Input) : ScheduleEndpointQuery.Input :=
  let address := RootEndpointAddress.query k (RootEndpointInput.addressInput k a)
  let indices := RootEndpointAddress.scanIndices address
  ⟨a.raw, indices.1, indices.2⟩

private def resolveInput (k : ℕ) (a : RootEndpointQuery.Input) :
    Option RootEndpointAddress.Address × Option (Option ℕ) :=
  (RootEndpointAddress.query k (RootEndpointInput.addressInput k a),
    ScheduleEndpointQuery.query k (request k a))

private theorem run_eq (k : ℕ) (a : RootEndpointQuery.Input) :
    RootEndpointResolveShort.run (resolveInput k a) = RootEndpointQuery.query k a := by
  rw [RootEndpointInput.query_eq_addressInput]
  unfold resolveInput request
  cases ha : RootEndpointAddress.query k (RootEndpointInput.addressInput k a) with
  | none => exact RootEndpointResolveShort.run_none _
  | some address =>
    rcases address with ⟨row, column⟩
    cases row <;> simp [RootEndpointQuery.resolve, RootEndpointQuery.resolveRow,
      RootEndpointFinish.run, Function.comp_def, Option.map_map]

private theorem addressInput_size (k : ℕ) :
    PolyBounded shortSize (fun a => (RootEndpointAddress.encInput
      (RootEndpointInput.addressInput k a)).length) := by
  apply PolyBounded.of_forall_le 2 1
  intro a
  rw [pow_one]
  exact (RootEndpointInput.length_addressInput_le k a).trans
    (Nat.mul_le_mul_left _ (Nat.le_succ _))

private theorem resolveInput_size (k : ℕ) :
    PolyBounded shortSize
      (fun a => (RootEndpointResolveShort.encInput (resolveInput k a)).length) := by
  have hclass := (RootEndpointAddress.query_polyTime k).polyBounded_length.comp
    (g := RootEndpointInput.addressInput k) (addressInput_size k)
  have hscan : PolyBounded shortSize (fun a =>
      (ScheduleEndpointAnswer.encAnswer (ScheduleEndpointQuery.query k (request k a))).length) := by
    apply (PolyBounded.self.add (PolyBounded.const 2)).mono
    intro a
    have hb := ScheduleEndpointQuery.length_answer_le k (request k a)
    change _ ≤ a.raw.length.size + 2 at hb
    exact hb.trans (by unfold shortSize; omega)
  exact ((((PolyBounded.const 2).mul hclass).add (PolyBounded.const 1)).add hscan).mono
    fun a => by rw [RootEndpointResolveShort.encInput, length_encPair]; rfl

/-- The emitted answer is polynomial in the binary metadata even when a raw table is malformed.
This bounds the size paid by subsequent computations that use the two vertex keys. -/
theorem length_output_polyBounded (k : ℕ) : PolyBounded shortSize (fun a =>
    (RootEndpointFinish.encOutput (RootEndpointQuery.query k a)).length) := by
  have h := RootEndpointResolveShort.computableInPolyTime_run.polyBounded_length.comp
    (g := resolveInput k) (resolveInput_size k)
  simpa only [run_eq] using h

private theorem bound_clock {p : RootEndpointQuery.Input → ℕ} (hp : PolyBounded shortSize p) :
    ∃ c d, ∀ a, 3 * (RootEndpointInput.encInput a).length + p a ≤
      c * (a.raw.length + shortSize a ^ d + 1) := by
  have h := ((PolyBounded.const 6).mul (PolyBounded.self (size := shortSize))).add hp
  obtain ⟨c, d, hd⟩ := h.exists_le_linear_add_pow (fun a => a.raw.length) 6
    (fun a => by simp [shortSize])
  refine ⟨c, d, fun a => le_trans ?_ (hd a)⟩
  have he := RootEndpointInput.length_encInput a
  simp only [Nat.size_eq_bits_len] at he
  change _ ≤ 6 * a.raw.length + (6 * shortSize a + p a)
  unfold shortSize
  omega

/-- For each fixed source tape count, a finite native machine returns the total root-edge keys
within linear raw length plus a polynomial in the binary metadata. Both the time and the charged
workspace obey this bound. All machine parameters and constants precede the runtime input. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (RootEndpointQuery.query k)
    RootEndpointInput.encInput RootEndpointFinish.encOutput
    (fun a => a.raw.length + shortSize a ^ d) (fun a => a.raw.length + shortSize a ^ d) := by
  let prep := RootEndpointInput.addressInput k
  have hp := (RootEndpointInput.addressInput_deg k).inO_one
  have hraw := RootEndpointInput.encInput_raw_deg.inO_one
  have hclass := RootEndpointAddress.query_polyTime k
  have hindices := RootEndpointAddress.computableInPolyTime_scanIndices.comp hclass
  obtain ⟨ti, si, hti, hsi, hi⟩ := hindices.exists_computableInO
  obtain ⟨tc, sc, htc, hsc, hc⟩ := hclass.exists_computableInO
  have hreq := (hraw.prod (hi.comp hp)).of_enc_eq (g := request k)
    (encC := ScheduleEndpointInput.encInput) (fun _ => rfl)
  have hscan := (ScheduleEndpointEncoded.computableInO k).comp_linear hreq
  have hboth := (hc.comp hp).prod hscan
  obtain ⟨tf, sf, htf, hsf, hf⟩ :=
    RootEndpointResolveShort.computableInPolyTime_run.exists_computableInO
  have h := (hf.comp hboth).of_enc_eq (g := RootEndpointQuery.query k)
    (encC := RootEndpointFinish.encOutput) (fun a => congrArg _ (run_eq k a).symm)
  let cost (a : RootEndpointQuery.Input) :=
    (tc (prep a) + ti (prep a) + tf (resolveInput k a)) +
    (sc (prep a) + si (prep a) + sf (resolveInput k a))
  have ha := addressInput_size k
  have hb := resolveInput_size k
  have hcost : PolyBounded shortSize cost :=
    (((htc.comp (g := prep) ha).add (hti.comp (g := prep) ha)).add (htf.comp hb)).add
      (((hsc.comp (g := prep) ha).add (hsi.comp (g := prep) ha)).add (hsf.comp hb))
  obtain ⟨c, d, hd⟩ := bound_clock hcost
  refine ⟨d, h.mono c (fun a => ?_) (fun a => ?_)⟩
  · change ((RootEndpointInput.encInput a).length + tc (prep a) +
        ((RootEndpointInput.encInput a).length + ((RootEndpointInput.encInput a).length +
          ti (prep a)))) + tf (resolveInput k a) ≤ _
    refine le_trans ?_ (hd a)
    dsimp only [cost]
    omega
  · change ((RootEndpointInput.encInput a).length + sc (prep a) +
        ((RootEndpointInput.encInput a).length + ((RootEndpointInput.encInput a).length +
          si (prep a)))) + sf (resolveInput k a) ≤ _
    refine le_trans ?_ (hd a)
    dsimp only [cost]
    omega

end Turing.MultiTapeTM.RootEndpointAlgorithm
