/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.SharedDictionary
import CslibFrontier.Computability.Circuit.Boolean.Minterms

/-!
# Sparse hardwired lookup

Split each key into two halves. The indicators of all possible half-words can be shared,
so testing each listed key costs one further conjunction. For each of the two halves of a
payload, group the matching indicators by the stored half-word. The disjoint groups use one
disjunction per entry in total. Recover the output coordinates by repeatedly merging flags
whose words differ only in their first bit.

## Main results

* `Cslib.Circuits.Boolean.Iteration.exists_sparseLookup` gives a circuit agreeing with an
  arbitrary word map on a finite domain of keys. Its size is linear in the domain size plus
  the number of possible half-words.
* `Cslib.Circuits.Boolean.Iteration.exists_lookupOr` gives the total operation for a table
  with repeated or missing keys.
* `Cslib.Circuits.Boolean.Iteration.synthesis_flaggedWords` and
  `Cslib.Circuits.Boolean.Iteration.synthesis_allMinterms` convert between binary words and
  families of flags with linear cost in the number of possible words.
* `Cslib.Circuits.Boolean.Iteration.synthesis_payloadBlock` returns the bitwise OR of the
  payloads of flagged table rows.

This is a direct finite construction for the lookup used in fixed-power circuits.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

variable {a n M : ℕ}

/-- OR the selected words coordinatewise. The flags may be arbitrary, including all false. -/
theorem synthesis_flaggedWords (k : ℕ) (s : Set (BooleanFunction a))
    (flag : BitString k → BooleanFunction a) (hf : ∀ w, flag w ∈ s) :
    Synthesis interpretation s
      (wires fun x i => decide (∃ w, flag w x = true ∧ w i = true)) (3 * 2 ^ k) := by
  induction k generalizing s with
  | zero =>
    refine (Synthesis.of_subset ?_).mono .rfl .rfl (Nat.zero_le _)
    rintro _ ⟨i, rfl⟩
    exact i.elim0
  | succ k ih =>
    let merged (w : BitString k) : BooleanFunction a :=
      fun x => flag (Fin.cons false w) x || flag (Fin.cons true w) x
    have hmerge : Synthesis interpretation s (Set.range merged) (2 ^ k) := by
      simpa [BitString.card] using Synthesis.family merged (fun _ => 1) fun w =>
        (Synthesis.of_mem (hf (Fin.cons false w))).or (Synthesis.of_mem (hf (Fin.cons true w)))
    have htail := hmerge.trans (ih (s ∪ Set.range merged) merged fun w => Or.inr ⟨w, rfl⟩)
    have hhead := Synthesis.exists_mem Finset.univ (fun w => flag (Fin.cons true w))
      (fun _ => 0) fun _ _ => Synthesis.of_mem (hf _)
    refine (hhead.union htail).mono .rfl ?_ ?_
    · rintro _ ⟨i, rfl⟩
      refine i.cases (Or.inl <| Set.mem_singleton_iff.mpr <| funext fun _ =>
        Bool.eq_iff_iff.mpr ?_) fun i => Or.inr ⟨i, funext fun _ => Bool.eq_iff_iff.mpr ?_⟩
      · simp [Fin.exists_fin_succ_pi]
      · simp [merged, Fin.exists_fin_succ_pi, Bool.exists_bool, or_and_right, exists_or]
    · simp only [pow_succ, Finset.sum_const, Finset.card_univ, BitString.card, smul_eq_mul]
      have := Nat.two_pow_pos k
      lia

/-- Return the bitwise OR of the payloads of all marked entries. Grouping by the stored
word charges each entry only once. -/
theorem synthesis_payloadBlock {k : ℕ} (s : Set (BooleanFunction a))
    (marked : Fin M → BooleanFunction a) (hm : ∀ j, marked j ∈ s)
    (value : Fin M → BitString k) :
    Synthesis interpretation s
      (wires fun x bit => decide (∃ j, marked j x = true ∧ value j bit = true))
      (M + 4 * 2 ^ k) := by
  classical
  let fiber (w : BitString k) := Finset.univ.filter fun j => value j = w
  let bucket (w : BitString k) : BooleanFunction a :=
    fun x => decide (∃ j ∈ fiber w, marked j x = true)
  have hsum : ∑ w, (fiber w).card = M := by
    simpa [fiber] using (Finset.card_eq_sum_card_fiberwise
      (s := .univ) (t := .univ) (f := value) (by simp)).symm
  have hb : Synthesis interpretation s (Set.range bucket) (M + 2 ^ k) := by
    simpa [Finset.sum_add_distrib, hsum] using Synthesis.family (I := interpretation) (s := s)
      bucket (fun w => (fiber w).card + 1) fun w => by
      simpa using (Synthesis.exists_mem (fiber w) marked (fun _ => 0) fun j _ =>
        Synthesis.of_mem (hm j)).congr_iff (g := bucket w) fun _ => by simp [bucket]
  refine (hb.trans (synthesis_flaggedWords k _ bucket fun w => Or.inr ⟨w, rfl⟩)).mono
    .rfl ?_ (by lia)
  rintro _ ⟨i, rfl⟩
  refine ⟨i, funext fun x => Bool.eq_iff_iff.mpr ?_⟩
  simp only [bucket, fiber, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  exact ⟨fun ⟨_, ⟨j, rfl, hj⟩, hbit⟩ => ⟨j, hj, hbit⟩,
    fun ⟨j, hj, hbit⟩ => ⟨value j, ⟨j, rfl, hj⟩, hbit⟩⟩

/-- Compute all equality indicators for an available word by sharing its prefix minterms. -/
theorem synthesis_allMinterms {k : ℕ} (s : Set (BooleanFunction a))
    (bits : BitString a → BitString k) (hb : wires bits ⊆ s) :
    Synthesis interpretation s
      (Set.range fun w : BitString k => fun x => decide (bits x = w))
      (4 * 2 ^ k) := by
  refine (Synthesis.circuit (I := interpretation) (s := s) (mintermCircuit k)
    (fun i x => bits x i) fun i => hb ⟨i, rfl⟩).mono .rfl ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact ⟨BitString.equivFin k w, funext fun _ => by simp⟩
  · have := size_mintermCircuit_add_three_le k
    lia

/-- Testing a whole key reuses the minterm for each half-word. -/
private theorem synthesize_matches {l r : ℕ} (keys : Fin M → BitString (l + r)) :
    Synthesis interpretation (inputs (l + r))
      (Set.range fun j x => decide (keys j = x))
      (4 * 2 ^ l + 4 * 2 ^ r + M) := by
  let left (w : BitString l) : BooleanFunction (l + r) := fun x => decide (x ∘ Fin.castAdd r = w)
  let right (w : BitString r) : BooleanFunction (l + r) := fun x => decide (x ∘ Fin.natAdd l = w)
  let halves := Set.range left ∪ Set.range right
  have hblock {k : ℕ} (get : Fin k → Fin (l + r)) :=
    synthesis_allMinterms (inputs (l + r)) (fun x => x ∘ get)
      (by rintro _ ⟨i, rfl⟩; exact ⟨get i, rfl⟩)
  have hmatch (j : Fin M) : Synthesis interpretation halves {fun x => decide (keys j = x)} 1 :=
    ((Synthesis.of_mem (I := interpretation) (s := halves)
      (f := left (keys j ∘ Fin.castAdd r)) (Or.inl ⟨_, rfl⟩)).and
      (Synthesis.of_mem (I := interpretation) (s := halves)
        (f := right (keys j ∘ Fin.natAdd l)) (Or.inr ⟨_, rfl⟩))).congr_iff fun x => by
      simp only [left, right, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨hl, hr⟩ => funext fun i => Fin.addCases (fun i => (congrFun hl i).symm)
        (fun i => (congrFun hr i).symm) i, fun h => h ▸ ⟨rfl, rfl⟩⟩
  simpa using ((hblock (Fin.castAdd r)).union (hblock (Fin.natAdd l))).trans
    ((Synthesis.family (fun j x => decide (keys j = x)) (fun _ => 1) hmatch).mono
      Set.subset_union_right .rfl le_rfl)

/-- Test an available `n`-bit word against every hardwired key, using a shared minterm
table for each half of the word. -/
theorem synthesis_tableMatches (s : Set (BooleanFunction a)) (bits : BitString a → BitString n)
    (hb : wires bits ⊆ s) (keys : Fin M → BitString n) :
    Synthesis interpretation s (Set.range fun j x => decide (keys j = bits x))
      (M + 8 * 2 ^ ((n + 1) / 2)) := by
  obtain ⟨l, r, rfl, hl, hr⟩ : ∃ l r, n = l + r ∧ l ≤ (n + 1) / 2 ∧ r ≤ (n + 1) / 2 :=
    ⟨n / 2, n - n / 2, by lia, by lia, by lia⟩
  obtain ⟨d, hd, hs⟩ := (synthesize_matches keys).exists_circuit_outputs
  refine (Synthesis.circuit (I := interpretation) (s := s) d (fun i x => bits x i)
    fun i => hb ⟨i, rfl⟩).mono .rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, funext fun x => congrFun (hd (bits x)) j⟩
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) hl
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    lia

/-- Emit a full payload word in two halves. The minterm budget is exponential only in a
half-word, even with arbitrary flags or repeated payloads. -/
theorem synthesis_tablePayload (s : Set (BooleanFunction a)) (marked : Fin M → BooleanFunction a)
    (hm : ∀ j, marked j ∈ s) (values : Fin M → BitString n) :
    Synthesis interpretation s
      (wires fun x bit => decide (∃ j, marked j x = true ∧ values j bit = true))
      (2 * M + 8 * 2 ^ ((n + 1) / 2)) := by
  obtain ⟨l, r, rfl, hl, hr⟩ : ∃ l r, n = l + r ∧ l ≤ (n + 1) / 2 ∧ r ≤ (n + 1) / 2 :=
    ⟨n / 2, n - n / 2, by lia, by lia, by lia⟩
  refine ((synthesis_payloadBlock s marked hm fun j => values j ∘ Fin.castAdd r).union
    (synthesis_payloadBlock s marked hm fun j => values j ∘ Fin.natAdd l)).mono .rfl ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) i
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) hl
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    lia

private theorem synthesis_singleLookupOr {k : ℕ} (s : Set (BooleanFunction a))
    (key : BitString a → BitString n) (hk : wires key ⊆ s) (keys : Fin M → BitString n)
    (values : Fin M → BitString k) :
    Synthesis interpretation s (wires (lookupOr keys values ∘ key))
      (3 * M + 8 * 2 ^ ((n + 1) / 2) + 8 * 2 ^ ((k + 1) / 2)) := by
  refine ((synthesis_tableMatches s key hk keys).trans
    (synthesis_tablePayload _ (fun j x => decide (keys j = key x))
      (fun j => Or.inr ⟨j, rfl⟩) values)).mono .rfl ?_ (by lia)
  rintro _ ⟨i, rfl⟩
  exact ⟨i, funext fun _ => Bool.eq_iff_iff.mpr (by simp [lookupOr])⟩

/-- One query against a fixed table of `n`-bit keys and values. Repeated keys return the
bitwise OR of their values, and missing keys return the all-false word. -/
theorem exists_lookupOr (keys values : Fin M → BitString n) :
    ∃ c : Circuit signature n n, c.Computes interpretation (lookupOr keys values) ∧
      c.size ≤ 3 * M + 16 * 2 ^ ((n + 1) / 2) := by
  have hin : wires (id : BitString n → BitString n) ⊆ inputs n := fun _ ⟨i, h⟩ => ⟨i, h⟩
  obtain ⟨c, hc, hs⟩ :=
    (synthesis_singleLookupOr (inputs n) id hin keys values).exists_circuit_outputs
  exact ⟨c, hc, by lia⟩

/-- Read a hardwired word of any width on a finite domain, given the query wires. The key and
payload each use two shared half-word tables. -/
theorem exists_synthesis_sparseLookup {k : ℕ} (domain : Finset (BitString n))
    (payload : BitString n → BitString k) (s : Set (BooleanFunction a))
    (key : BitString a → BitString n) (hk : wires key ⊆ s) :
    ∃ value : BitString a → BitString k,
      Synthesis interpretation s (wires value)
        (3 * domain.card + 8 * 2 ^ ((n + 1) / 2) + 8 * 2 ^ ((k + 1) / 2)) ∧
      ∀ x, key x ∈ domain → value x = payload (key x) := by
  classical
  let e := Fintype.equivFin ↥domain
  let keys (j : Fin (Fintype.card ↥domain)) : BitString n := (e.symm j).val
  refine ⟨lookupOr keys (payload ∘ keys) ∘ key, ?_, fun x hx => ?_⟩
  · simpa only [Fintype.card_coe] using synthesis_singleLookupOr s key hk keys (payload ∘ keys)
  · have hj : keys (e ⟨key x, hx⟩) = key x := congrArg Subtype.val (e.symm_apply_apply _)
    exact (lookupOr_of_eq (payload ∘ keys) (Subtype.val_injective.comp e.symm.injective) hj).trans
      (congrArg payload hj)

/-- An arbitrary payload on a finite domain has a De Morgan circuit using at most
`3 * domain.card + 16 * 2 ^ ⌈n/2⌉` gates. Constants are included in the bound. -/
theorem exists_sparseLookup (domain : Finset (BitString n))
    (payload : BitString n → BitString n) :
    ∃ c : Circuit signature n n, c.ComputesOn interpretation ↑domain payload ∧
      c.size ≤ 3 * domain.card + 16 * 2 ^ ((n + 1) / 2) := by
  obtain ⟨value, hv, hvalue⟩ := exists_synthesis_sparseLookup domain payload (inputs n) id
    (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
  obtain ⟨c, hc, hs⟩ := hv.exists_circuit_outputs
  exact ⟨c, fun x hx => (hc x).trans (hvalue x hx), by lia⟩

end Cslib.Circuits.Boolean.Iteration
