/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Encoding
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# Self-closing door reachability belongs to PSPACE

Every reached location is the initial location or a listed tunnel exit. Consequently its
binary label and the door-state list fit in a number of bits linear in the explicit input
encoding. Self-delimiting padding embeds these configurations into fixed-width words. An
additional accepting word has incoming edges from configurations at the target location,
so the final door states remain unrestricted. Savitch's algorithm on these words gives the
polynomial-space upper bound for the directed symmetric self-closing door problem.

## Main results

* `Reachability_mem_PSPACE`: target-location reachability is in PSPACE for `encInstance`.

## References

* [Ani et al.][AniBosboomDemaineEtAl2021, Section 2.1]
* [M. Sipser][Sipser2013, Theorem 8.5]
-/

public section

namespace Cslib.Complexity.SelfClosingDoor

open _root_.Turing.MultiTapeTM

private def stateDecoder : Decoder encState :=
  (Decoder.pair Decoder.nat Decoder.bits).map
    (fun p => State.mk p.1 p.2) (fun s => (s.location, s.bits))
    (fun s => by cases s; rfl) (fun _ => rfl)

private def decode (word : List Bool) : State := stateDecoder.decode (unframe word.tail)

private def budget (I : Instance) : ℕ := 3 * (encInstance I).length + 1

private def width (I : Instance) : ℕ := 2 * budget I + 2

private def stateWord (I : Instance) (s : State) : List Bool :=
  false :: BitString.padWord (budget I) (encState s)

private def accept (I : Instance) : List Bool :=
  true :: List.replicate (2 * budget I + 1) false

private theorem decode_stateWord (I : Instance) (s : State) : decode (stateWord I s) = s := by
  simp only [decode, stateWord, List.tail_cons, BitString.padWord, unframe_frame_append,
    stateDecoder.decode_enc]

private theorem stateWord_ne_accept (I : Instance) (s : State) : stateWord I s ≠ accept I := by
  simp [stateWord, accept]

private theorem length_accept (I : Instance) : (accept I).length = width I := by
  simp [accept, width]

private theorem tunnel_target_bound (d : Door) (b : Bool) :
    (encNat (d.tunnel b).target).length ≤ (encDoor d).length := by
  cases b
  · exact (encTunnel_target_length_le d.zero).trans (encDoor_zero_length_le d)
  · exact (encTunnel_target_length_le d.one).trans (encDoor_one_length_le d)

private theorem location_bound {I : Instance} {s : State}
    (hr : Reachable I.doors I.initial s) :
    (encNat s.location).length ≤ (encInstance I).length := by
  induction hr with
  | refl => exact encInstance_start_length_le I
  | @tail t u _ hstep _ =>
    obtain ⟨_, i, _, rfl⟩ := hstep
    exact (tunnel_target_bound I.doors[i] _).trans
      ((length_le_encList_of_mem encDoor (List.getElem_mem i.isLt)).trans
        (encInstance_doors_length_le I))

private theorem state_bound {I : Instance} {s : State}
    (hr : Reachable I.doors I.initial s) : (encState s).length ≤ budget I := by
  have hl := location_bound hr
  have hv : s.bits.length = I.doors.length := hr.valid I.initial_valid
  have hm := (length_le_length_encList encDoor I.doors).trans (encInstance_doors_length_le I)
  simp only [encState_apply, encStateFields, length_encPair, encBits_apply, budget]; omega

private theorem length_stateWord {I : Instance} {s : State}
    (hr : Reachable I.doors I.initial s) : (stateWord I s).length = width I := by
  simp only [stateWord, List.length_cons, BitString.length_padWord (state_bound hr), width]

private def wordEdge (I : Instance) (a b : List Bool) : Bool :=
  decide (a = stateWord I (decode a)) &&
    ((decide (b = accept I) && decide ((decode a).location = I.target)) ||
      (decide (b = stateWord I (decode b)) && checkStep I.doors (decode a) (decode b)))

private theorem wordEdge_stateWord (I : Instance) (s : State) (b : List Bool) :
    wordEdge I (stateWord I s) b = true ↔
      (b = accept I ∧ s.location = I.target) ∨
        ∃ t, b = stateWord I t ∧ Step I.doors s t := by
  simp only [wordEdge, decode_stateWord, decide_true, Bool.true_and, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, checkStep_eq_true_iff]
  exact or_congr_right ⟨fun ⟨hb, hs⟩ => ⟨decode b, hb, hs⟩, fun ⟨t, hb, hs⟩ => by
    subst hb
    rw [decode_stateWord]
    exact ⟨rfl, hs⟩⟩

private theorem wordEdge_accept (I : Instance) (b : List Bool) :
    wordEdge I (accept I) b = false := by
  simp [wordEdge, (stateWord_ne_accept I (decode (accept I))).symm]

private def CodeStep (I : Instance) (a b : List Bool) : Prop :=
  a.length = width I ∧ b.length = width I ∧ wordEdge I a b = true

private theorem code_reachable {I : Instance} {s : State}
    (hr : Reachable I.doors I.initial s) :
    Relation.ReflTransGen (CodeStep I) (stateWord I I.initial) (stateWord I s) := by
  induction hr with
  | refl => exact .refl
  | @tail t u hprefix hstep ih =>
    exact ih.tail ⟨length_stateWord hprefix, length_stateWord (hprefix.tail hstep),
      (wordEdge_stateWord I t (stateWord I u)).2 (.inr ⟨u, rfl, hstep⟩)⟩

private theorem decode_reachable {I : Instance} {word : List Bool}
    (hr : Relation.ReflTransGen (CodeStep I) (stateWord I I.initial) word) :
    ∃ s, Reachable I.doors I.initial s ∧
      (word = stateWord I s ∨ word = accept I ∧ s.location = I.target) := by
  induction hr with
  | refl => exact ⟨I.initial, .refl, .inl rfl⟩
  | @tail a b _ hstep ih =>
    obtain ⟨s, hs, rfl | ⟨rfl, -⟩⟩ := ih
    · rcases (wordEdge_stateWord I s b).1 hstep.2.2 with h | ⟨t, rfl, hst⟩
      · exact ⟨s, hs, .inr h⟩
      · exact ⟨t, hs.tail hst, .inl rfl⟩
    · simp [CodeStep, wordEdge_accept] at hstep

private theorem accepts_iff_code_reachable (I : Instance) : I ∈ Reachability ↔
    Relation.ReflTransGen (CodeStep I) (stateWord I I.initial) (accept I) := by
  refine ⟨fun ⟨s, hr, hgoal⟩ => (code_reachable hr).tail
    ⟨length_stateWord hr, length_accept I, (wordEdge_stateWord I s _).2 (.inl ⟨rfl, hgoal⟩)⟩,
    fun hr => ?_⟩
  obtain ⟨s, hs, heq | ⟨_, hgoal⟩⟩ := decode_reachable hr
  · exact (stateWord_ne_accept I s heq.symm).elim
  · exact ⟨s, hs, hgoal⟩

private def solve (I : Instance) : Bool :=
  Cslib.Reachability.savitch (wordEdge I) (width I) (width I)
    (stateWord I I.initial) (accept I)

private theorem solve_eq_true_iff (I : Instance) : solve I = true ↔ I ∈ Reachability := by
  have hsrc : (stateWord I I.initial).length = width I := length_stateWord .refl
  have hcard : {word | Relation.ReflTransGen (CodeStep I)
      (stateWord I I.initial) word}.encard ≤ 2 ^ width I + 1 :=
    (Set.encard_le_encard fun word hword => by
      induction hword with | refl => exact hsrc | tail _ hstep _ => exact hstep.2.1).trans
      ((BitString.encard_setOf_length_eq _).le.trans le_self_add)
  rw [solve, Cslib.Reachability.savitch_iff hsrc (length_accept I)]
  exact (Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard).symm.trans
    (accepts_iff_code_reachable I).symm

private theorem decode_polyTime : ComputableInPolyTime decode encBits encState := by
  unfold decode
  fun_prop

private theorem budget_polyTime : ComputableInPolyTime budget encInstance encUnary :=
  .unary_add' (.unary_mul' (.const 3)
    (ComputableInPolyTime.length_bits.comp (.of_eq fun _ => rfl))) (.const 1)

private theorem width_polyTime : ComputableInPolyTime width encInstance encUnary :=
  .unary_add' (.unary_mul' (.const 2) budget_polyTime) (.const 2)

private theorem code_polyTime :
    ComputableInPolyTime (fun p : Instance × State => stateWord p.1 p.2)
      (encPair encInstance encState) encBits :=
  .bitsCons (.const false) (.bitsPadWord (budget_polyTime.comp (.fst _ _))
    ((ComputableInPolyTime.of_eq (f := encState) fun _ => rfl).comp (.snd _ _)))

private theorem accept_polyTime : ComputableInPolyTime accept encInstance encBits :=
  .bitsCons (.const true) ((ComputableInPolyTime.bitsReplicate false).comp
    (.unary_add' (.unary_mul' (.const 2) budget_polyTime) (.const 1)))

private theorem wordEdge_polyTime :
    ComputableInPolyTime (fun q : Instance × List Bool × List Bool =>
      wordEdge q.1 q.2.1 q.2.2) (Cslib.Reachability.encEdgeArgs encInstance) encBool := by
  have hi : ComputableInPolyTime Prod.fst
      (Cslib.Reachability.encEdgeArgs encInstance) encInstance := by
    unfold Cslib.Reachability.encEdgeArgs
    fun_prop
  have ha : ComputableInPolyTime (fun q : Instance × List Bool × List Bool => q.2.1)
      (Cslib.Reachability.encEdgeArgs encInstance) encBits := by
    unfold Cslib.Reachability.encEdgeArgs
    fun_prop
  have hb : ComputableInPolyTime (fun q : Instance × List Bool × List Bool => q.2.2)
      (Cslib.Reachability.encEdgeArgs encInstance) encBits := by
    unfold Cslib.Reachability.encEdgeArgs
    fun_prop
  have hsa := decode_polyTime.comp ha
  have hsb := decode_polyTime.comp hb
  exact (ha.decide_eq' (code_polyTime.comp (hi.prod hsa))).bool_and'
    (((hb.decide_eq' (accept_polyTime.comp hi)).bool_and'
        ((encState_location_polyTime hsa).decide_eq' (encInstance_target_polyTime hi))).bool_or'
      ((hb.decide_eq' (code_polyTime.comp (hi.prod hsb))).bool_and'
        (computableInPolyTime_checkStep (encInstance_doors_polyTime hi) hsa hsb)))

private theorem arguments_polyTime :
    ComputableInPolyTime (fun I : Instance =>
      (I, width I, width I, stateWord I I.initial, accept I))
      encInstance (Cslib.Reachability.encArgs encInstance) := by
  have := width_polyTime
  have := accept_polyTime
  have := code_polyTime.comp (ComputableInPolyTime.id'.prod Instance.computableInPolyTime_initial)
  unfold Cslib.Reachability.encArgs
  fun_prop

/-- Single-player target-location reachability for directed symmetric self-closing doors
is in PSPACE under the explicit door-list encoding with binary location labels. -/
theorem Reachability_mem_PSPACE : Reachability ∈ PSPACE encInstance := by
  obtain ⟨_, _, hspace, hc⟩ := Cslib.Reachability.exists_polyBounded_space_savitch
    wordEdge_polyTime arguments_polyTime (fun _ => length_stateWord .refl) length_accept
  exact mem_PSPACE_of_computableInTimeAndSpace hspace hc fun I => (solve_eq_true_iff I).symm

end Cslib.Complexity.SelfClosingDoor
