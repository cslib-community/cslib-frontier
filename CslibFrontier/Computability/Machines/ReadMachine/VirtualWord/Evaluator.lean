/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Runtime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# Native repeated evaluation of a virtual input

A Boolean-state consumer scans the whole virtual word twice, retaining its state across reads
and across the pass boundary. The length is unbounded. Each outer address is translated to an
original-tail address and the runtime accessor selects its prefix/suffix bit before resuming the
consumer. Only the runtime header, its offset, a binary scan counter and one Boolean are stored.
The virtual word is a specification, never a workspace object. Constants are independent of
runtime cut, suffix and address. The supplied header's address field is ignored by the consumer.

This original implementation supports the QUERY-GENERATOR/EVALUATOR recomputation in the proof
of Lemma 3.3, expanded ECCC TR13-047, printed page 6
[GlasserNguyenReitwiessnerSelmanWitek2013]. Definitions 3.1–3.2 concern general logspace
transducers; this module handles only a two-pass Boolean-state evaluator. Generic native
predicate substitution, preparing the supplied header from a generator, regenerating answers,
the resource-certified suffix loop and adaptive-to-tt conversion remain unproved here.
-/

public section

namespace Turing.VirtualWord.Evaluator

open MultiTapeTM ComputableInSpace

/-- The declared virtual length; for valid cuts this is the reconstructed word's length. -/
@[expose] def width (d : Data) : ℕ := d.cut + d.suffix.length

/-- The declared width uses space linear in the encoded data, without allocating the word. -/
theorem width_data_inSpace : ComputableInSpace width encData encNat
    (fun d => (encData d).length) := by
  have hid := budget_id (enc := encData) (.refl _)
  have hl : ComputableInSpace List.length encBits encNat (fun w => w.length) :=
    (of_inO ComputableInO.lengthNat).weaken (.of_le_linear 1 1 fun _ => by omega)
  exact budget_natAdd (encData_cut_budget hid)
    (budget_comp_linear hl (encData_suffix_budget hid))

@[expose] section

/-- Runtime accessor state, binary consumer position, and saved Boolean evaluator state. -/
@[ext]
structure State where
  /-- State of the underlying runtime accessor. -/
  runtime : Runtime.State
  /-- Binary consumer scan position across the two virtual-word passes. -/
  pos : ℕ
  /-- Saved Boolean state of the consumer across reads and across the pass boundary. -/
  acc : Bool
  deriving DecidableEq

end

/-- Charge all retained data, including the suspended consumer state. -/
enc_structure encState : State where
  runtime : Runtime.encState,
  pos : encNat,
  acc : encBool

/-- Runtime data recovered from the retained small header. -/
@[expose] def data (s : State) : Data := Runtime.decode s.runtime.header.reverse

/-- The outer read address, reset at each pass boundary. -/
@[expose] def address (s : State) : ℕ := s.pos % width (data s)

/-- One translated read, using exactly the runtime accessor's selector. -/
@[expose] def bit (s : State) (b : Option Bool) : Bool :=
  answer ⟨(data s).cut, (data s).suffix, address s⟩ (b.getD false)

/-- A fixed consumer; its transition table is finite and independent of runtime parameters.
The accessor's initialization read is retained, then every evaluation read resumes the saved
Boolean state. A zero-width word halts immediately after initialization. -/
@[expose] def machine (δ : Bool × Bool → Bool) : QueryMachine State where
  init := ⟨Runtime.machine.init, 0, false⟩
  query s := if Runtime.machine.halted s.runtime then s.runtime.cursor + address s
    else Runtime.machine.query s.runtime
  next := fun (s, b) => if Runtime.machine.halted s.runtime then
      ⟨s.runtime, s.pos + 1, δ (s.acc, bit s b)⟩
    else ⟨Runtime.machine.next (s.runtime, b), s.pos, s.acc⟩
  emit _ := []
  halted s := Runtime.machine.halted s.runtime && !(decide (s.pos < 2 * width (data s)))
  finish s := [s.acc]

/-- Reference evaluation, defined by successive reads rather than constructing the word. -/
@[expose] def value (δ : Bool × Bool → Bool) (p : Runtime.Input) : ℕ → Bool
  | 0 => false
  | k + 1 => δ (value δ p k,
      answer ⟨p.data.cut, p.data.suffix, k % width p.data⟩
        (p.original.getD (k % width p.data) false))

/-- The finite evaluator's result after two complete passes. -/
@[expose] def evaluate (δ : Bool × Bool → Bool) (p : Runtime.Input) : Bool :=
  value δ p (2 * width p.data)

/-- The initialized accessor is held fixed while the consumer runs. -/
@[expose] def loaded (p : Runtime.Input) : Runtime.State :=
  { header := (encData p.data).reverse, cursor := 2 * (encData p.data).length + 1,
    payload := false, ready := true, bit := some (p.original.getD p.data.address false) }

/-- Initialization has exactly the accessor's states, with a constant suspended consumer. -/
theorem run_initializing (δ : Bool × Bool → Bool) (p : Runtime.Input) {t : ℕ}
    (ht : t ≤ 2 * (encData p.data).length + 2) :
    (machine δ).run (Runtime.encInput p) t =
      ⟨Runtime.machine.run (Runtime.encInput p) t, 0, false⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have h := (Runtime.first_halt p).2 t (by omega)
    simp only [QueryMachine.step, machine, h, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, QueryMachine.read, QueryMachine.run_succ]

/-- Every consumer read is redirected to the original read-only tail. -/
theorem read_loaded (δ : Bool × Bool → Bool) (p : Runtime.Input) (k : ℕ) (a : Bool) :
    (machine δ).read (Runtime.encInput p) ⟨loaded p, k, a⟩ =
      p.original[k % width p.data]? := by
  change (frame (encData p.data) ++ p.original)[(machine δ).query ⟨loaded p, k, a⟩]? = _
  simp only [machine, loaded, Runtime.machine, Option.isSome_some, ↓reduceIte, address, data,
    List.reverse_reverse, Runtime.decode_encData]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The unbounded read-loop invariant: exactly one finite transition per virtual bit. -/
theorem run_scanning (δ : Bool × Bool → Bool) (p : Runtime.Input) {k : ℕ}
    (hk : k ≤ 2 * width p.data) :
    (machine δ).run (Runtime.encInput p) (2 * (encData p.data).length + 2 + k) =
      ⟨loaded p, k, value δ p k⟩ := by
  induction k with
  | zero =>
    rw [Nat.add_zero, run_initializing δ p le_rfl]
    rcases p with ⟨d, x⟩
    rw [Runtime.run_halted]
    rfl
  | succ k ih =>
    rw [show 2 * (encData p.data).length + 2 + (k + 1) =
      (2 * (encData p.data).length + 2 + k) + 1 by omega,
      QueryMachine.run_succ, ih (by omega)]
    have hlt : k < 2 * width p.data := by omega
    have hh : (machine δ).halted ⟨loaded p, k, value δ p k⟩ = false := by
      simp only [machine, loaded, data, Runtime.machine, List.reverse_reverse,
        Runtime.decode_encData, Option.isSome_some, hlt, decide_true, Bool.not_true, Bool.true_and]
    rw [QueryMachine.step, hh]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [read_loaded]
    simp only [machine, loaded, Runtime.machine, Option.isSome_some, ↓reduceIte, bit, address,
      data, List.reverse_reverse, Runtime.decode_encData, value, List.getD_eq_getElem?_getD]

/-- Exact first halt, including the empty virtual word. -/
theorem first_halt (δ : Bool × Bool → Bool) (p : Runtime.Input) :
    let T := 2 * (encData p.data).length + 2 + 2 * width p.data
    (machine δ).halted ((machine δ).run (Runtime.encInput p) T) = true ∧
      ∀ t < T, (machine δ).halted ((machine δ).run (Runtime.encInput p) t) = false := by
  dsimp only
  constructor
  · rw [run_scanning δ p le_rfl]
    simp only [machine, loaded, data, Runtime.machine, List.reverse_reverse,
      Runtime.decode_encData, Option.isSome_some, lt_self_iff_false, decide_false,
      Bool.not_false, Bool.and_self]
  · intro t ht
    by_cases hi : t < 2 * (encData p.data).length + 2
    · rw [run_initializing δ p (by omega)]
      simp only [machine, (Runtime.first_halt p).2 t hi, Bool.false_and]
    · rw [show t = 2 * (encData p.data).length + 2 +
        (t - (2 * (encData p.data).length + 2)) by omega, run_scanning δ p (by omega)]
      simp only [machine, loaded, data, Runtime.machine, List.reverse_reverse,
        Runtime.decode_encData, Option.isSome_some,
        show t - (2 * (encData p.data).length + 2) < 2 * width p.data by omega,
        decide_true, Bool.not_true, Bool.true_and]

/-- The actual machine emits the evaluator result, without accumulating a virtual input. -/
theorem output (δ : Bool × Bool → Bool) (p : Runtime.Input) :
    (machine δ).output (Runtime.encInput p)
      (2 * (encData p.data).length + 2 + 2 * width p.data) = [evaluate δ p] := by
  unfold QueryMachine.output
  simp only [show (machine δ).emit = fun _ => [] from rfl, ite_self, List.map_const',
    List.flatten_replicate_nil, List.nil_append]
  rw [run_scanning δ p le_rfl]
  rfl

/-- For valid cuts the consumer transition reads exactly the reconstructed virtual word.
The modulo counter scans each address once per pass when the word is nonempty. -/
theorem value_word (δ : Bool × Bool → Bool) (cut : ℕ) (suffix x : List Bool)
    (hc : cut ≤ x.length) (k : ℕ) :
    value δ ⟨⟨cut, suffix, 0⟩, x⟩ (k + 1) =
      δ (value δ ⟨⟨cut, suffix, 0⟩, x⟩ k,
        (word x cut suffix).getD (k % (word x cut suffix).length) false) := by
  dsimp only [value]
  rw [answer_eq_getD x cut suffix _ hc, length_word x cut suffix hc]
  rfl

/-- Header decoding is native in the charged consumer state. -/
theorem data_inSpace : ComputableInSpace data encState encData
    (fun s => (encState s).length) :=
  budget_comp_linear (f := State.runtime) Runtime.header_inSpace
    (encState_runtime_budget (budget_id (.refl _)))

/-- The virtual length is computed from binary cut and the stored suffix only. -/
theorem width_inSpace : ComputableInSpace (fun s => width (data s)) encState encNat
    (fun s => (encState s).length) :=
  budget_comp_linear width_data_inSpace data_inSpace

/-- The outer scan address is binary, even for unbounded virtual lengths. -/
theorem address_inSpace : ComputableInSpace address encState encNat
    (fun s => (encState s).length) :=
  budget_natMod (encState_pos_budget (budget_id (.refl _))) width_inSpace

/-- All five consumer components have actual native linear-space realizations. -/
theorem components_inSpace (δ : Bool × Bool → Bool) :
    ComputableInSpace (machine δ).query encState encNat (fun s => (encState s).length) ∧
    ComputableInSpace (machine δ).next (encPair encState (encOption encBool)) encState
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine δ).emit (encPair encState (encOption encBool)) encBits
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine δ).halted encState encBool (fun s => (encState s).length) ∧
    ComputableInSpace (machine δ).finish encState encBits (fun s => (encState s).length) := by
  have hid := budget_id (enc := encState) (.refl _)
  have hs := encState_runtime_budget hid
  have hh := budget_comp_linear Runtime.halted_inSpace hs
  have hcursor := Runtime.encScan_cursor_budget (Runtime.encState_toScan_budget hs)
  have hq := budget_ite hh (budget_natAdd hcursor address_inSpace)
    (budget_comp_linear Runtime.query_inSpace hs)
  have hn := budget_natLt (encState_pos_budget hid) (budget_natAdd width_inSpace width_inSpace)
  have hhalt := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && !p.2)
    (budget_prod hh hn)
  have hfinish := budget_finite (encC := encBits) (fun b => [b]) (encState_acc_budget hid)
  have hp := fst encState (encOption encBool)
  have hrt := encState_runtime_budget hp
  have hpos := encState_pos_budget hp
  have hacc := encState_acc_budget hp
  have hd := budget_comp_linear data_inSpace hp
  have ha := budget_comp_linear address_inSpace hp
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (snd encState (encOption encBool))
  have hbit := budget_comp_linear answer_inSpace
    (budget_prod (encData_mk_budget (encData_cut_budget hd) (encData_suffix_budget hd) ha) hb)
  have hδ := budget_finite (encC := encBool) δ (budget_prod hacc hbit)
  have hready := budget_comp_linear Runtime.halted_inSpace hrt
  have hnext := budget_ite hready
    (encState_mk_budget hrt (budget_natSucc hpos) hδ)
    (encState_mk_budget (budget_comp_linear Runtime.next_inSpace
      (budget_prod hrt (snd encState (encOption encBool)))) hpos hacc)
  refine ⟨hq, hnext, budget_const [], ?_, hfinish⟩
  simpa only [machine, two_mul] using hhalt

/-- Explicit encoding cost: saved accessor state, binary loop counter and one bit. -/
theorem length_encState (s : State) :
    (encState s).length = 2 * (Runtime.encState s.runtime).length +
      2 * (encNat s.pos).length + 3 := by
  simp only [encState_apply, encStateFields, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- All live states fit a uniform budget; oversized cuts cost binary bits, not unary storage. -/
theorem length_run_le (δ : Bool × Bool → Bool) (p : Runtime.Input) {t : ℕ}
    (ht : t ≤ 2 * (encData p.data).length + 2 + 2 * width p.data) :
    (encState ((machine δ).run (Runtime.encInput p) t)).length ≤
      48 * ((encData p.data).length + Nat.log2 (Runtime.encInput p).length + 1) := by
  have hcounter : ∀ k ≤ 2 * width p.data,
      (encNat k).length ≤ 4 * ((encData p.data).length + 1) := by
    intro k hk
    have hlt_pow (m : ℕ) : m < 2 ^ (encNat m).length := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.lt_size_self m
    have hs' : (encNat p.data.suffix.length).length ≤ (encData p.data).length + 1 := by
      have h1 := encData_suffix_length_le p.data
      have h2 := length_encNat_le_self p.data.suffix.length
      simp only [encBits_apply] at h1
      omega
    have h₁ := (hlt_pow p.data.cut).trans_le
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (encData_cut_length_le p.data))
    have h₂ := (hlt_pow p.data.suffix.length).trans_le
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hs')
    have hkpow : k < 2 ^ ((encData p.data).length + 3) := by
      dsimp only [width] at hk
      rw [pow_succ, pow_succ, pow_succ]
      omega
    have := length_encNat_le_of_lt_two_pow hkpow
    omega
  by_cases hi : t ≤ 2 * (encData p.data).length + 2
  · rw [run_initializing δ p hi, length_encState]
    have h := Runtime.length_run_le p hi
    have hz : (encNat 0).length = 0 := rfl
    simp only [hz]
    omega
  · have hk : t - (2 * (encData p.data).length + 2) ≤ 2 * width p.data := by omega
    rw [show t = 2 * (encData p.data).length + 2 +
      (t - (2 * (encData p.data).length + 2)) by omega, run_scanning δ p hk, length_encState]
    have h := Runtime.length_run_le p (t := 2 * (encData p.data).length + 2) le_rfl
    have hn := hcounter _ hk
    rcases p with ⟨d, x⟩
    dsimp only at h hn hk ⊢
    rw [Runtime.run_halted] at h
    dsimp only [loaded] at h ⊢
    omega

/-- One actual native evaluator handles all runtime inputs with shared constants. -/
theorem evaluate_inSpace (δ : Bool × Bool → Bool) :
    ∃ time c, ComputableInTimeAndSpace (evaluate δ) Runtime.encInput encBool time
      (fun p => c * ((encData p.data).length + Nat.log2 (Runtime.encInput p).length + 1)) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace δ
  exact (machine δ).computableInSpace (encS := encState) (f := evaluate δ) hq hn he hh hf
    (fun p => 2 * (encData p.data).length + 2 + 2 * width p.data)
    (fun p => (first_halt δ p).1) (fun p => (first_halt δ p).2)
    (fun p => (output δ p).symm)
    (fun p => (encData p.data).length + Nat.log2 (Runtime.encInput p).length + 1)
    (fun p => by omega) ⟨48, fun p t ht => length_run_le δ p ht⟩

/-- Physical consumer states are logarithmic in the original word, with honest header bounds. -/
theorem length_run_le_original_log (δ : Bool × Bool → Bool) (p : Runtime.Input)
    (hp : Runtime.Admissible p) {t : ℕ}
    (ht : t ≤ 2 * (encData p.data).length + 2 + 2 * width p.data) :
    (encState ((machine δ).run (Runtime.encInput p) t)).length ≤
      816 * (Nat.log2 p.original.length + 1) := by
  exact ((length_run_le δ p ht).trans
    (Nat.mul_le_mul_left 48 (Runtime.budget_le_original_log p hp))).trans_eq
      (by rw [← Nat.mul_assoc])

/-- The native certificate measures workspace against the original length, uniformly over
runtime parameters. Only size admissibility is assumed, never a final transfer certificate. -/
theorem evaluate_inOriginalLogSpace (δ : Bool × Bool → Bool) :
    ∃ time c, ComputableInTimeAndSpace
      (fun p : {p : Runtime.Input // Runtime.Admissible p} => evaluate δ p.val)
      ((Function.Embedding.subtype Runtime.Admissible).trans Runtime.encInput) encBool time
      (fun p => c * (Nat.log2 p.val.original.length + 1)) := by
  let enc := (Function.Embedding.subtype Runtime.Admissible).trans Runtime.encInput
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace δ
  obtain ⟨time, c, h⟩ := (machine δ).computableInSpace (encS := encState) (enc := enc)
    (encOut := encBool)
    (f := fun p : {p : Runtime.Input // Runtime.Admissible p} => evaluate δ p.val)
    hq hn he hh hf
    (fun p => 2 * (encData p.val.data).length + 2 + 2 * width p.val.data)
    (fun p => (first_halt δ p.val).1) (fun p => (first_halt δ p.val).2)
    (fun p => (output δ p.val).symm)
    (fun p => 17 * (Nat.log2 p.val.original.length + 1))
    (fun p => by
      change Nat.log2 (Runtime.encInput p.val).length + 1 ≤ _
      have := Runtime.budget_le_original_log p.val p.property
      omega)
    ⟨48, fun p t ht => (length_run_le δ p.val ht).trans
      (Nat.mul_le_mul_left 48 (Runtime.budget_le_original_log p.val p.property))⟩
  refine ⟨time, c * 17, h.mono (fun _ => le_rfl) (fun p => ?_)⟩
  exact (Nat.mul_assoc c 17 _).symm.le

/-- The semantic specification is an ordinary finite-state fold of the actual virtual reads.
This list describes output semantics only; the native machine stores just one Boolean. -/
theorem value_eq_fold (δ : Bool × Bool → Bool) (cut : ℕ) (suffix x : List Bool)
    (hc : cut ≤ x.length) (k : ℕ) :
    value δ ⟨⟨cut, suffix, 0⟩, x⟩ k =
      ((List.range k).map fun j =>
        (word x cut suffix).getD (j % (word x cut suffix).length) false).foldl
          (fun a b => δ (a, b)) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [value_word δ cut suffix x hc k, ih]
    simp only [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

/-- Conventional semantics: the native result is the finite-state fold of two copies of the
virtual word. These copies occur only in the specification, never in the machine's state. -/
theorem evaluate_word (δ : Bool × Bool → Bool) (cut : ℕ) (suffix x : List Bool)
    (hc : cut ≤ x.length) :
    evaluate δ ⟨⟨cut, suffix, 0⟩, x⟩ =
      (word x cut suffix ++ word x cut suffix).foldl (fun a b => δ (a, b)) false := by
  unfold evaluate
  rw [value_eq_fold δ cut suffix x hc]
  rw [show width ⟨cut, suffix, 0⟩ = (word x cut suffix).length from
    (length_word x cut suffix hc).symm]
  let w := word x cut suffix
  have hm : ((List.range w.length).map fun j => w.getD (j % w.length) false) = w := by
    apply List.ext_getElem (by simp)
    intro i _ hi
    simp only [List.getElem_map, List.getElem_range, Nat.mod_eq_of_lt hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hs : ((List.range w.length).map fun j =>
      w.getD ((w.length + j) % w.length) false) = w := by
    simpa only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod] using hm
  change ((List.range (2 * w.length)).map fun j => w.getD (j % w.length) false).foldl
    (fun a b => δ (a, b)) false = _
  rw [two_mul, List.range_add, List.map_append, List.map_map, hm]
  simp only [Function.comp_def, hs, w]

end Turing.VirtualWord.Evaluator
