/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice

/-!
# Uniform runtime virtual-word access

A single query machine reads a framed binary data header followed by the original read-only
word. It stores only the header, a binary cursor and finite flags, then reads one original bit.
The original word is never copied into workspace. Both counters in the header are binary.
`access_inSpace` supplies a single native program with constants shared across all data.
`access_inOriginalLogSpace` measures its workspace against the original word length under the
explicit parameter-size conditions in `Admissible`. Outside that domain, `access` remains total
with the general header-size bound; a cut past the input uses the declared suffix offset.
This is an original implementation lemma supporting, rather than proving, Lemma 3.3 of
[GlasserNguyenReitwiessnerSelmanWitek2013].
-/

public section

namespace Turing.VirtualWord.Runtime

open MultiTapeTM ComputableInSpace

@[expose] section

/-- Runtime parameters followed by the unchanged original word. -/
@[ext]
structure Input where
  /-- Runtime prefix cut, stored suffix, and target address. -/
  data : Data
  /-- Unchanged original read-only word. -/
  original : List Bool
  deriving DecidableEq

/-- Retained header prefix (in reverse order) and current physical input cursor. -/
@[ext]
structure Scan where
  /-- Header bits retained so far, in reverse order. -/
  header : List Bool
  /-- Position just after the header once initialization has finished. -/
  cursor : ℕ
  deriving DecidableEq

/-- Reversed header and cursor, followed by payload/ready flags and a fetched bit. -/
@[ext]
structure State extends Scan where
  /-- Whether the next header symbol is payload rather than a frame marker. -/
  payload : Bool
  /-- Whether initialization has reached the end of the framed header. -/
  ready : Bool
  /-- The original-input bit, with a false default on a missing address. -/
  bit : Option Bool
  deriving DecidableEq

end

/-- A framed small header, then the literal original word. -/
enc_structure encInput : Input where
  data : encData,
  original : encBits

/-- Total decoding of the binary cut, literal suffix and binary address. -/
@[expose] def decode (w : List Bool) : Data :=
  ⟨ofBits (unframe w), unframe (dropFrame w), ofBits (dropFrame (dropFrame w))⟩

/-- Decoding the supplied header recovers every runtime parameter. -/
theorem decode_encData (d : Data) : decode (encData d) = d := by
  rcases d with ⟨cut, suffix, i⟩
  simp only [decode, encData_apply, encDataFields, encPair_apply, unframe_frame_append,
    dropFrame_frame_append, encBits_apply, encNat_apply, Data.mk.injEq, true_and]
  exact ⟨Nat.foldr_bit_bits cut, Nat.foldr_bit_bits i⟩

/-- Encoding of the retained reversed header and binary cursor. -/
enc_structure encScan : Scan where
  header : encBits,
  cursor : encNat

/-- Only the small header and binary cursor are charged. -/
enc_structure encState : State where
  toScan : encScan,
  payload : encBool,
  ready : encBool,
  bit : (encOption encBool)

/-- Initialize by scanning the framed small header, then fetch one original-input bit.
A missing frame marker ends initialization; a missing payload is decoded as false. -/
@[expose] def machine : QueryMachine State where
  init := { header := [], cursor := 0, payload := false, ready := false, bit := none }
  query s := if s.ready then s.cursor + (decode s.header.reverse).address else s.cursor
  next := fun (s, b) =>
    if s.ready then { s with ready := true, bit := some (b.getD false) }
    else if s.payload then
      { header := b.getD false :: s.header, cursor := s.cursor + 1,
        payload := false, ready := false, bit := none }
    else if b.getD false then
      { s with cursor := s.cursor + 1, payload := true, ready := false, bit := none }
    else
      { s with cursor := s.cursor + 1, payload := false, ready := true, bit := none }
  emit _ := []
  halted s := s.bit.isSome
  finish s := if s.bit.isSome then [answer (decode s.header.reverse) (s.bit.getD false)] else []

/-- At each frame marker only the already scanned header prefix is stored. -/
theorem run_marker (h x : List Bool) {k : ℕ} (hk : k ≤ h.length) :
    machine.run (frame h ++ x) (2 * k) =
      { header := (h.take k).reverse, cursor := 2 * k,
        payload := false, ready := false, bit := none } := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < h.length := by omega
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      QueryMachine.run_succ, QueryMachine.run_succ, ih (by omega)]
    simp only [QueryMachine.step, QueryMachine.read, machine, Bool.false_eq_true, ↓reduceIte,
      Option.isSome_none, (getElem?_frame_append h x hk').1, Option.getD_some,
      (getElem?_frame_append h x hk').2]
    rw [List.take_succ_eq_append_getElem hk', List.reverse_append]
    simp

/-- Between marker and payload the retained header has not grown. -/
theorem run_payload (h x : List Bool) {k : ℕ} (hk : k < h.length) :
    machine.run (frame h ++ x) (2 * k + 1) =
      { header := (h.take k).reverse, cursor := 2 * k + 1,
        payload := true, ready := false, bit := none } := by
  rw [QueryMachine.run_succ, run_marker h x (by omega)]
  simp [QueryMachine.step, QueryMachine.read, machine, (getElem?_frame_append h x hk).1]

/-- Initialization finishes with exactly the supplied header and the original-word offset. -/
theorem run_initialized (h x : List Bool) :
    machine.run (frame h ++ x) (2 * h.length + 1) =
      { header := h.reverse, cursor := 2 * h.length + 1,
        payload := false, ready := true, bit := none } := by
  rw [QueryMachine.run_succ, run_marker h x le_rfl]
  simp only [List.take_length, QueryMachine.step, QueryMachine.read, machine,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte, getElem?_frame_append_length,
    Option.getD_some]

/-- One further step reads the original input at the runtime address. -/
theorem run_halted (d : Data) (x : List Bool) :
    machine.run (encInput ⟨d, x⟩) (2 * (encData d).length + 2) =
      { header := (encData d).reverse, cursor := 2 * (encData d).length + 1,
        payload := false, ready := true, bit := some (x.getD d.address false) } := by
  change machine.run (frame (encData d) ++ x) _ = _
  rw [show 2 * (encData d).length + 2 = (2 * (encData d).length + 1) + 1 by omega,
    QueryMachine.run_succ, run_initialized]
  simp only [QueryMachine.step, QueryMachine.read, machine, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, List.reverse_reverse, decode_encData,
    getElem?_frame_append_boundary (encData d) x d.address, List.getD_eq_getElem?_getD]

/-- Every runtime parameter is an input to this one fixed machine, rather than part of its code. -/
theorem output (d : Data) (x : List Bool) :
    machine.output (encInput ⟨d, x⟩) (2 * (encData d).length + 2) =
      [answer d (x.getD d.address false)] := by
  unfold QueryMachine.output
  simp only [show machine.emit = fun _ => [] from rfl, ite_self, List.map_const',
    List.flatten_replicate_nil, List.nil_append]
  rw [run_halted]
  simp only [machine, Option.isSome_some, ↓reduceIte, List.reverse_reverse, decode_encData,
    Option.getD_some]

/-- Header decoding has native space linear in the actual header, even for noncanonical bits. -/
theorem decode_inSpace : ComputableInSpace decode encBits encData (fun w => w.length) := by
  have hu : ComputableInSpace unframe encBits encBits (fun w => w.length) :=
    of_inO (.of_linear (.of_unframe fun _ => rfl))
  have hd : ComputableInSpace dropFrame encBits encBits (fun w => w.length) :=
    of_inO (.of_linear (.of_dropFrame fun _ => rfl))
  have hn : ComputableInSpace ofBits encBits encNat (fun w => w.length) :=
    of_inO ComputableInO.bitsToNat
  exact encData_mk_budget (budget_comp_linear hn hu) (budget_comp_linear hu hd)
    (budget_comp_linear hn (budget_comp_linear hd hd))

/-- Decoding the reversed retained header is linear in the encoded runtime state. -/
theorem header_inSpace : ComputableInSpace (fun s : State => decode s.header.reverse)
    encState encData (fun s => (encState s).length) :=
  budget_comp_linear decode_inSpace (budget_comp_linear bitsReverse
    (encScan_header_budget (encState_toScan_budget (budget_id (.refl _)))))

/-- The runtime address is added to the original-word offset only after initialization. -/
theorem query_inSpace : ComputableInSpace machine.query encState encNat
    (fun s => (encState s).length) := by
  have hid := budget_id (enc := encState) (.refl _)
  have hc := encScan_cursor_budget (encState_toScan_budget hid)
  exact budget_ite (encState_ready_budget hid)
    (budget_natAdd hc (encData_address_budget header_inSpace)) hc

/-- Halting depends only on the fetched-bit flag. -/
theorem halted_inSpace : ComputableInSpace machine.halted encState encBool
    (fun s => (encState s).length) :=
  budget_finite (encC := encBool) Option.isSome (encState_bit_budget (budget_id (.refl _)))

/-- Header loading and the single original-input read use space linear in compact state. -/
theorem next_inSpace : ComputableInSpace machine.next
    (encPair encState (encOption encBool)) encState
    (fun p => (encPair encState (encOption encBool) p).length) := by
  have hs := fst encState (encOption encBool)
  have hscan := encState_toScan_budget hs
  have hh := encScan_header_budget hscan
  have hc := encScan_cursor_budget hscan
  have hp := encState_payload_budget hs
  have hr := encState_ready_budget hs
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (snd encState (encOption encBool))
  have hsome := budget_finite (encC := encOption encBool) some hb
  have hsingleton := hb.of_enc_eq (encC := encBits)
    (g := fun p : State × Option Bool => [p.2.getD false]) (fun _ => rfl)
  have hcons : ComputableInSpace
      (fun p : State × Option Bool => p.2.getD false :: p.1.header)
      (encPair encState (encOption encBool)) encBits
      (fun p => (encPair encState (encOption encBool) p).length) :=
    (hsingleton.append hh (fun _ => rfl)).weaken (.add (.refl _) (.refl _))
  have hn := budget_natSucc hc
  have hstep := encScan_mk_budget hh hn
  have hf := budget_const (encIn := encPair encState (encOption encBool)) (Bs := fun p =>
    (encPair encState (encOption encBool) p).length) (encB := encBool) false
  have ht := budget_const (encIn := encPair encState (encOption encBool)) (Bs := fun p =>
    (encPair encState (encOption encBool) p).length) (encB := encBool) true
  have hnone := budget_const (encIn := encPair encState (encOption encBool)) (Bs := fun p =>
    (encPair encState (encOption encBool) p).length) (encB := encOption encBool) none
  exact budget_ite hr (encState_mk_budget hscan hp ht hsome)
    (budget_ite hp (encState_mk_budget (encScan_mk_budget hcons hn) hf hf hnone)
      (budget_ite hb (encState_mk_budget hstep ht hf hnone)
        (encState_mk_budget hstep hf ht hnone)))

/-- No output is accumulated while scanning. -/
theorem emit_inSpace : ComputableInSpace machine.emit
    (encPair encState (encOption encBool)) encBits
    (fun p => (encPair encState (encOption encBool) p).length) := budget_const []

/-- The final answer uses the existing native selector certificate. -/
theorem finish_inSpace : ComputableInSpace machine.finish encState encBits
    (fun s => (encState s).length) := by
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (encState_bit_budget (budget_id (.refl _)))
  have ha := budget_comp_linear answer_inSpace (budget_prod header_inSpace hb)
  exact budget_ite halted_inSpace (budget_finite (encC := encBits) (fun b => [b]) ha)
    (budget_const [])

private theorem before_initialized (h x : List Bool) {t : ℕ} (ht : t < 2 * h.length + 1) :
    (machine.run (frame h ++ x) t).bit = none ∧
    (machine.run (frame h ++ x) t).header.length ≤ h.length ∧
    (machine.run (frame h ++ x) t).cursor ≤ 2 * h.length + 1 := by
  have hdiv := Nat.mod_add_div t 2
  rcases Nat.mod_two_eq_zero_or_one t with heven | hodd
  · have heq : t = 2 * (t / 2) := by omega
    rw [heq, run_marker h x (by omega)]
    simp only [List.length_reverse, List.length_take, true_and]
    omega
  · have heq : t = 2 * (t / 2) + 1 := by omega
    rw [heq, run_payload h x (by omega)]
    simp only [List.length_reverse, List.length_take, true_and]
    omega

/-- The fixed runtime machine first halts after loading the header and making one input query. -/
theorem first_halt (p : Input) :
    machine.halted (machine.run (encInput p) (2 * (encData p.data).length + 2)) = true ∧
    ∀ t < 2 * (encData p.data).length + 2,
      machine.halted (machine.run (encInput p) t) = false := by
  rcases p with ⟨d, x⟩
  refine ⟨by rw [run_halted]; rfl, fun t ht => ?_⟩
  dsimp only at ht
  by_cases hpre : t < 2 * (encData d).length + 1
  · simpa [machine] using (before_initialized (encData d) x hpre).1
  · obtain rfl : t = 2 * (encData d).length + 1 := by omega
    change (machine.run (frame (encData d) ++ x) _).bit.isSome = false
    rw [run_initialized]
    rfl

/-- Every live and halted state retains at most the supplied header and its binary scan offset. -/
theorem run_storage (p : Input) {t : ℕ} (ht : t ≤ 2 * (encData p.data).length + 2) :
    (machine.run (encInput p) t).header.length ≤ (encData p.data).length ∧
    (machine.run (encInput p) t).cursor ≤ 2 * (encData p.data).length + 1 := by
  rcases p with ⟨d, x⟩
  dsimp only at ht
  by_cases hpre : t < 2 * (encData d).length + 1
  · exact (before_initialized (encData d) x hpre).2
  · have heq : t = 2 * (encData d).length + 1 ∨ t = 2 * (encData d).length + 2 := by omega
    rcases heq with rfl | rfl
    · change (machine.run (frame (encData d) ++ x) _).header.length ≤ (encData d).length ∧
        (machine.run (frame (encData d) ++ x) _).cursor ≤ 2 * (encData d).length + 1
      rw [run_initialized]
      simp only [List.length_reverse, le_refl, and_self]
    · rw [run_halted]
      simp only [List.length_reverse, le_refl, and_self]

/-- Finite flags contribute at most eleven bits beyond the header and binary cursor. -/
theorem length_encState_le (s : State) :
    (encState s).length ≤ 4 * s.header.length + 2 * (encNat s.cursor).length + 11 := by
  have hb : (encOption encBool s.bit).length ≤ 2 := by cases s.bit <;> simp
  simp only [encState_apply, encStateFields, encScan_apply, encScanFields, length_encPair,
    encBits_apply, encBool_apply, List.length_singleton]
  omega

/-- State size is uniformly linear in the actual header plus a logarithmic input counter. -/
theorem length_run_le (p : Input) {t : ℕ} (ht : t ≤ 2 * (encData p.data).length + 2) :
    (encState (machine.run (encInput p) t)).length ≤
      16 * ((encData p.data).length + Nat.log2 (encInput p).length + 1) := by
  obtain ⟨hh, hc⟩ := run_storage p ht
  have hcursor : (machine.run (encInput p) t).cursor ≤ (encInput p).length := by
    have hlen : (encInput p).length = 2 * (encData p.data).length + 1 + p.original.length := by
      simp only [encInput_apply, encInputFields, length_encPair, encBits_apply]
    omega
  have hn := length_encNat_le_log2 hcursor
  have hs := length_encState_le (machine.run (encInput p) t)
  omega

/-- The total runtime operation. When the cut exceeds the original length it still uses the
specified cut as the suffix offset; no padded or reconstructed word is allocated. -/
@[expose] def access (p : Input) : Bool :=
  answer p.data (p.original.getD p.data.address false)

/-- One compiled native program handles all runtime cuts, suffixes and addresses, with shared
constants. The bound explicitly charges arbitrary header sizes, including invalid parameters. -/
theorem access_inSpace : ∃ time c, ComputableInTimeAndSpace access encInput encBool time
    (fun p => c * ((encData p.data).length + Nat.log2 (encInput p).length + 1)) := by
  refine machine.computableInSpace (encS := encState) (enc := encInput)
    query_inSpace next_inSpace emit_inSpace halted_inSpace
    finish_inSpace (fun p => 2 * (encData p.data).length + 2)
    (fun p => (first_halt p).1) (fun p => (first_halt p).2)
    (fun p => (output p.data p.original).symm)
    (fun p => (encData p.data).length + Nat.log2 (encInput p).length + 1) ?_
    ⟨16, fun p t ht => length_run_le p ht⟩
  intro p
  omega

/-- Admissible parameter sizes are measured against the original word, before its header. -/
@[expose] def Admissible (p : Input) : Prop :=
  p.data.cut ≤ p.original.length ∧ p.data.address ≤ p.original.length ∧
    p.data.suffix.length ≤ Nat.clog 2 p.original.length

/-- The entire encoded input has a small header; its length cannot hide a large workspace
allowance. This also covers original lengths zero and one. -/
theorem budget_le_original_log (p : Input) (hp : Admissible p) :
    (encData p.data).length + Nat.log2 (encInput p).length + 1 ≤
      17 * (Nat.log2 p.original.length + 1) := by
  rcases p with ⟨⟨cut, suffix, i⟩, x⟩
  obtain ⟨hc, hi, hs⟩ := hp
  have hstate := VirtualWord.length_encState_le_log false hc hi hs
  have hheader : (encData ⟨cut, suffix, i⟩).length ≤ 8 * (Nat.log2 x.length + 1) := by
    simp only [VirtualWord.encState_apply, VirtualWord.encStateFields, length_encPair,
      encBool_apply, List.length_singleton] at hstate
    omega
  have hlen : (encInput ⟨⟨cut, suffix, i⟩, x⟩).length =
      2 * (encData ⟨cut, suffix, i⟩).length + 1 + x.length := by
    simp only [encInput_apply, encInputFields, length_encPair, encBits_apply]
  have hpoly : (encInput ⟨⟨cut, suffix, i⟩, x⟩).length ≤ 17 * (x.length + 1) ^ 1 := by
    have := Nat.log2_le_self x.length
    simp only [pow_one]
    omega
  have hsize := length_encNat_le_of_le_mul_pow hpoly
  rw [encNat_apply, Nat.size_eq_bits_len] at hsize
  have hbound : (encInput ⟨⟨cut, suffix, i⟩, x⟩).length.size ≤
      8 * (Nat.log2 x.length + 1) := hsize
  have hlog : Nat.log2 (encInput ⟨⟨cut, suffix, i⟩, x⟩).length ≤
      (encInput ⟨⟨cut, suffix, i⟩, x⟩).length.size :=
    ((Nat.log2_lt (by omega)).mpr (Nat.lt_size_self _)).le
  dsimp only
  omega

/-- Physical runtime states occupy logarithmic space in the original word length. -/
theorem length_run_le_original_log (p : Input) (hp : Admissible p) {t : ℕ}
    (ht : t ≤ 2 * (encData p.data).length + 2) :
    (encState (machine.run (encInput p) t)).length ≤ 272 * (Nat.log2 p.original.length + 1) := by
  have h := (length_run_le p ht).trans (Nat.mul_le_mul_left 16 (budget_le_original_log p hp))
  exact h.trans_eq (by rw [← Nat.mul_assoc])

/-- The compiled program has logarithmic workspace in the original word length, uniformly
across all admissible runtime parameters. The framed input is explicit, not a large encoding
chosen to inflate the logarithmic bound. -/
theorem access_inOriginalLogSpace : ∃ time c, ComputableInTimeAndSpace
    (fun p : {p : Input // Admissible p} => access p.val)
    ((Function.Embedding.subtype Admissible).trans encInput) encBool time
    (fun p => c * (Nat.log2 p.val.original.length + 1)) := by
  obtain ⟨time, c, h⟩ := machine.computableInSpace (encS := encState)
    (enc := (Function.Embedding.subtype Admissible).trans encInput)
    (encOut := encBool) (f := fun p : {p : Input // Admissible p} => access p.val)
    query_inSpace next_inSpace emit_inSpace halted_inSpace finish_inSpace
    (fun p => 2 * (encData p.val.data).length + 2)
    (fun p => (first_halt p.val).1) (fun p => (first_halt p.val).2)
    (fun p => (output p.val.data p.val.original).symm)
    (fun p => 17 * (Nat.log2 p.val.original.length + 1))
    (fun p => by
      change Nat.log2 (encInput p.val).length + 1 ≤ _
      have := budget_le_original_log p.val p.property
      omega)
    ⟨16, fun p t ht => (length_run_le p.val ht).trans
      (Nat.mul_le_mul_left 16 (budget_le_original_log p.val p.property))⟩
  exact ⟨time, c * 17, h.mono (fun _ => le_rfl) fun _ => (Nat.mul_assoc c 17 _).symm.le⟩

/-- For a valid cut the runtime output is exactly the virtual-word bit, including its default. -/
theorem output_word (cut i : ℕ) (suffix x : List Bool) (hc : cut ≤ x.length) :
    machine.output (encInput ⟨⟨cut, suffix, i⟩, x⟩)
      (2 * (encData ⟨cut, suffix, i⟩).length + 2) =
        [(word x cut suffix).getD i false] := by
  rw [output, answer_eq_getD x cut suffix i hc]

end Turing.VirtualWord.Runtime
