/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import Mathlib.Data.List.GetD

/-!
# Reading a fixed prefix and a stored suffix

The original word is read-only input. Only a binary prefix length, a stored suffix and a binary
address enter the accessor state. `machine` emits one bit and halts: it reads the original input
at prefix addresses and indexes the stored suffix otherwise. All five query-machine components
have native charged space certificates linear in this small state, independently of the length
of the original word. `word` is a semantic specification and is never computed into workspace.
The false default agrees with `Turing.ReadMachine`.

This is the virtual-input access operation needed in the proof of Lemma 3.3 of
[GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC TR13-047, printed page 6.
The paper's fixed prefix ends before its ceiling-logarithmic suffix. Initialization, query and
answer regeneration, suffix iteration and adaptive-to-tt conversion are separate obligations.
-/

public section

namespace Turing.VirtualWord

open MultiTapeTM

/-- The specified word; this list is not stored by the accessor. -/
@[expose] def word (x : List Bool) (cut : ℕ) (suffix : List Bool) : List Bool :=
  x.take cut ++ suffix

@[expose] section

/-- The only stored data: prefix length, stored suffix, and requested address. -/
@[ext]
structure Data where
  /-- Length of the prefix read from the original input word. -/
  cut : ℕ
  /-- Stored suffix bits following the prefix. -/
  suffix : List Bool
  /-- Requested virtual-word bit address. -/
  address : ℕ
  deriving DecidableEq

/-- State of the single-bit accessor: stored request data and a halting flag. -/
@[ext]
structure State where
  /-- Stored prefix cut, suffix, and target address. -/
  data : Data
  /-- Whether the single original-input read has already taken place. -/
  halted : Bool
  deriving DecidableEq

end

/-- Binary counters and the literal stored suffix. -/
enc_structure encData : Data where
  cut : encNat,
  suffix : encBits,
  address : encNat

/-- The state encoding charges the stored suffix, but never the original prefix. -/
enc_structure encState : State where
  data : encData,
  halted : encBool

/-- Select the original input bit or a bit of the stored suffix, defaulting to false. -/
@[expose] def answer (d : Data) (b : Bool) : Bool :=
  if d.address < d.cut then b else d.suffix.getD (d.address - d.cut) false

/-- One native input read suffices. The read is ignored at suffix addresses. -/
@[expose] def machine (d : Data) : QueryMachine State where
  init := ⟨d, false⟩
  query s := s.data.address
  next := fun (s, _) => ⟨s.data, true⟩
  emit := fun (s, b) => [answer s.data (b.getD false)]
  halted := State.halted
  finish _ := []

/-- Exact length, including an empty prefix or suffix. -/
theorem length_word (x : List Bool) (cut : ℕ) (suffix : List Bool) (h : cut ≤ x.length) :
    (word x cut suffix).length = cut + suffix.length := by
  simp only [word, List.length_append, List.length_take, Nat.min_eq_left h]

/-- Prefix, boundary, suffix and past-the-end reads all agree with the specified word. -/
theorem answer_eq_getD (x : List Bool) (cut : ℕ) (suffix : List Bool) (i : ℕ)
    (h : cut ≤ x.length) :
    answer ⟨cut, suffix, i⟩ (x.getD i false) = (word x cut suffix).getD i false := by
  simp only [answer, word, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_take, Nat.min_eq_left h]
  split_ifs with hi
  · simp [hi]
  · rfl

/-- The actual native run emits exactly the requested bit and then halts. -/
theorem output_one (d : Data) (x : List Bool) :
    (machine d).output x 1 = [answer d (x.getD d.address false)] := by
  simp [QueryMachine.output, QueryMachine.run, QueryMachine.step, QueryMachine.read, machine,
    List.getD_eq_getElem?_getD]

/-- Only the halting bit changes; the stored suffix is never enlarged. -/
theorem run_one (d : Data) (x : List Bool) : (machine d).run x 1 = ⟨d, true⟩ := rfl

open ComputableInSpace

/-- The selector is natively computable in charged space linear in the stored data and bit. -/
theorem answer_inSpace : ComputableInSpace (fun p : Data × Bool => answer p.1 p.2)
    (encPair encData encBool) encBool (fun p => (encPair encData encBool p).length) := by
  have hd := fst encData encBool
  have hc := encData_cut_budget hd
  have hs := encData_suffix_budget hd
  have hi := encData_address_budget hd
  have hlt := budget_comp_lin natLt (linear_succ) (budget_prod hi hc)
  have hsub := budget_natSub hi hc
  refine (budget_ite hlt (snd _ _)
    (budget_comp_linear (bitsGetD false) (budget_prod hs hsub))).of_enc_eq ?_
  intro p
  simp [answer]

/-- All components of the accessor have native certificates in the small stored state. -/
theorem components_inSpace (d : Data) :
    ComputableInSpace (machine d).query encState encNat (fun s => (encState s).length) ∧
    ComputableInSpace (machine d).next (encPair encState (encOption encBool)) encState
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine d).emit (encPair encState (encOption encBool)) encBits
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine d).halted encState encBool (fun s => (encState s).length) ∧
    ComputableInSpace (machine d).finish encState encBits (fun s => (encState s).length) := by
  have hid := budget_id (enc := encState) (.refl _)
  have hstate := fst encState (encOption encBool)
  have hdata := encState_data_budget hstate
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (snd encState (encOption encBool))
  have ha := budget_comp_linear answer_inSpace (budget_prod hdata hb)
  exact ⟨encData_address_budget (encState_data_budget hid),
    encState_mk_budget hdata (budget_const true),
    budget_finite (encC := encBits) (fun b => [b]) ha,
    encState_halted_budget hid, budget_const []⟩

/-- Explicit storage bound: two binary counters, the suffix, and a halting bit. -/
theorem length_encState (cut i : ℕ) (suffix : List Bool) (halt : Bool) :
    (encState ⟨⟨cut, suffix, i⟩, halt⟩).length =
      4 * (encNat cut).length + 4 * suffix.length + 2 * (encNat i).length + 6 := by
  simp only [encState_apply, encStateFields, encData_apply, encDataFields, length_encPair,
    encBits_apply, encBool_apply, List.length_singleton]
  omega

/-- For each fixed stored data `d`, the answer bit `answer d (x.getD d.address false)` is computable
from `x` within work space `c * ((encState ⟨d, false⟩).length + Nat.log2 x.length + 1)`, where the
machine, the time bound and the constant `c` may all depend on `d`. The original input is not
part of the charged workspace. This theorem supplies actual multi-tape machines, using the
query-machine compiler, rather than assuming an access certificate. One machine and one constant
for all data, read from the input tape, are given by
`Turing.VirtualWord.Runtime.access_inSpace`. -/
theorem access_inSpace (d : Data) :
    ∃ t c, ComputableInTimeAndSpace
      (fun x : List Bool => answer d (x.getD d.address false)) encBits encBool t
      (fun x => c * ((encState ⟨d, false⟩).length + Nat.log2 x.length + 1)) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace d
  refine (machine d).computableInSpace hq hn he hh hf (fun _ => 1)
    (fun _ => rfl) (fun x t ht => ?_) (fun x => ?_) _
    (fun _ => by simp only [encBits_apply]; omega) ⟨1, fun x t ht => ?_⟩
  · have : t = 0 := by omega
    subst t
    rfl
  · exact (output_one d x).symm
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
    · simp only [QueryMachine.run_zero, machine, Nat.one_mul]
      omega
    · rw [run_one]
      obtain ⟨cut, suffix, i⟩ := d
      simp only [length_encState, Nat.one_mul]
      omega

/-- A ceiling-logarithmic suffix and addresses at most the input length give an explicit
logarithmic state bound, including lengths zero and one. -/
theorem length_encState_le_log {n cut i : ℕ} {suffix : List Bool} (halt : Bool)
    (hc : cut ≤ n) (hi : i ≤ n) (hs : suffix.length ≤ Nat.clog 2 n) :
    (encState ⟨⟨cut, suffix, i⟩, halt⟩).length ≤ 16 * (Nat.log2 n + 1) := by
  have hcut := length_encNat_le_log2 hc
  have hindex := length_encNat_le_log2 hi
  have hclog : Nat.clog 2 n ≤ Nat.log2 n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_log2_self.le)
  rw [length_encState]
  omega

/-- A concrete logspace certificate on any input domain satisfying the stored-data bounds.
The domain hypotheses restrict data sizes, not correctness or an assumed resource certificate. -/
theorem access_inLogSpace (d : Data) (P : List Bool → Prop)
    (hcut : ∀ x, P x → d.cut ≤ x.length)
    (hindex : ∀ x, P x → d.address ≤ x.length)
    (hsuffix : ∀ x, P x → d.suffix.length ≤ Nat.clog 2 x.length) :
    ComputableInLogSpace (fun x : {x // P x} => answer d (x.val.getD d.address false))
      ((Function.Embedding.subtype P).trans encBits) encBool := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace d
  refine (machine d).computableInLogSpace hq hn he hh hf (fun _ => 1)
    (fun _ => rfl) (fun x t ht => ?_) (fun x => (output_one d x.val).symm)
    ⟨16, fun x t ht => ?_⟩
  · have : t = 0 := by omega
    subst t
    rfl
  · obtain ⟨cut, suffix, i⟩ := d
    have hbound := length_encState_le_log (n := x.val.length)
      (cut := cut) (i := i) (suffix := suffix)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
    · exact hbound false (hcut x.val x.property) (hindex x.val x.property)
        (hsuffix x.val x.property)
    · rw [run_one]
      exact hbound true (hcut x.val x.property) (hindex x.val x.property)
        (hsuffix x.val x.property)

end Turing.VirtualWord
