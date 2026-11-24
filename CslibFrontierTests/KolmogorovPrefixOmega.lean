/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Kolmogorov.ChaitinOmega

/-!
Regression clients, concrete finite witnesses, and axiom checks for prefix-free Kolmogorov
complexity, the Kraft–Chaitin inequality, Chaitin's halting probability `Ω`, Martin-Löf randomness,
and Chaitin's bit-incompleteness theorem.
-/

namespace CslibFrontierTests.KolmogorovPrefixOmega

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Encodable

/-! ### Self-delimiting decoding and header parsing witnesses -/

example :
    decodeSelfDelimiting? (selfDelimitingCode [true, false] ++ [true, true]) =
      some ([true, false], [true, true]) :=
  decodeSelfDelimiting?_selfDelimitingCode_append [true, false] [true, true]

example : decodeSelfDelimiting? [] = none := rfl

example : decodeSelfDelimiting? [true] = none := rfl

/- Rejects non-canonical length prefix (`k = 1`, `bits = [false]`, value `0` has `size 0 ≠ 1`). -/
example : decodeSelfDelimiting? [true, false, false, true, false] = none := rfl

example :
    parseCodeHeader (codeHeader Nat.Partrec.Code.zero ++ [false, true]) =
      some (Nat.Partrec.Code.zero, [false, true]) :=
  parseCodeHeader_codeHeader_append Nat.Partrec.Code.zero [false, true]

example : parseCodeHeader [] = none := rfl

example : parseCodeHeader [true, false, false, true, false] = none := rfl

/-! ### Prefix-free invariance and non-vacuity -/

-- `literal` is neither prefix-free nor minorizing prefix-free decoders.
example : ¬ literal.IsPrefixFree := by
  intro hpf
  have h1 : ([] : List Bool) ∈ literal.haltingSet := ⟨[], literal_produces.mpr rfl⟩
  have h2 : [false] ∈ literal.haltingSet := ⟨[false], literal_produces.mpr rfl⟩
  have heq := hpf [] h1 [false] h2 (List.nil_prefix)
  cases heq

example : ¬ literal.MinorizesPrefixPartrec := fun h => by
  let g : List Bool →. List Bool := fun q =>
    match decodeSelfDelimiting? q with
    | Option.none => Part.none
    | some (b, p) => if p = [] then Part.some (b ++ b) else Part.none
  have hg : Partrec g := by
    have hstep : Primrec₂ fun (q : List Bool) (_ : ℕ) =>
        match decodeSelfDelimiting? q with
        | Option.none => Option.none
        | some (b, p) => if p = [] then some (b ++ b) else Option.none := by
      have hf : Primrec fun bp : List Bool × List Bool =>
          if bp.2 = [] then some (bp.1 ++ bp.1) else Option.none :=
        Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const []))
          (Primrec.option_some.comp (Primrec.list_append.comp Primrec.fst Primrec.fst))
          (Primrec.const Option.none)
      refine Primrec₂.mk <| (Primrec.option_bind (primrec_decodeSelfDelimiting?.comp Primrec.fst)
        (hf.comp Primrec.snd).to₂).of_eq fun ⟨q, _⟩ => ?_
      cases decodeSelfDelimiting? q <;> rfl
    refine (Partrec.rfindOpt hstep.to_comp).of_eq fun q => ?_
    ext x
    cases hd : decodeSelfDelimiting? q with
    | none =>
      simp only [g, hd, Part.notMem_none, iff_false]
      intro hmem
      obtain ⟨_, hn⟩ := Nat.rfindOpt_spec hmem
      simp at hn
    | some bp =>
      rcases bp with ⟨b, p⟩
      by_cases hp : p = []
      · simp only [g, hd, hp, ↓reduceIte, Part.mem_some_iff]
        rw [Nat.rfindOpt_mono (fun {_ _ _} _ h => h)]
        simp [eq_comm]
      · simp only [g, hd, hp, ↓reduceIte, Part.notMem_none, iff_false]
        intro hmem
        obtain ⟨_, hn⟩ := Nat.rfindOpt_spec hmem
        simp at hn
  have hg_pf : InformationTheory.IsPrefixFree {q | (g q).Dom} := by
    refine isPrefixFree_range_selfDelimitingCode.anti fun q hq => ?_
    cases hd : decodeSelfDelimiting? q with
    | none => simp [g, hd] at hq
    | some bp =>
      rcases bp with ⟨b, p⟩
      by_cases hp : p = []
      · subst hp
        exact ⟨b, by simpa using decodeSelfDelimiting?_eq_some_iff.mp hd⟩
      · simp [g, hd, hp] at hq
  obtain ⟨c, hc⟩ := h g hg hg_pf
  let b : List Bool := List.replicate (3 * c + 12) true
  have hmem : b ++ b ∈ g (selfDelimitingCode b) := by simp [g]
  have hle := hc (selfDelimitingCode b) (b ++ b) hmem
  simp only [ecomplexity_literal, List.length_append, length_selfDelimitingCode] at hle
  have hle_nat : b.length + b.length ≤ b.length + 2 * b.length.size + 1 + c := by
    exact_mod_cast hle
  have hsz : 2 * b.length.size + 1 + c < b.length := by
    have hblen : b.length = 3 * c + 12 := by simp [b]
    have hbsize : b.length.size ≤ c + 4 := by
      have hpow : ∀ k : ℕ, 3 * k + 12 < 2 ^ (k + 4) := fun k => by
        induction k with
        | zero => norm_num
        | succ k ih =>
          rw [show k + 1 + 4 = (k + 4) + 1 by omega, pow_succ]
          omega
      exact Nat.size_le.mpr (hblen ▸ hpow c)
    omega
  omega

-- Invariance client for `universalPrefix` over `{M | M.IsPartrec ∧ M.IsPrefixFree}`.
example {M : DescriptionMethod ℕ} (hpart : M.IsPartrec) (hpf : M.IsPrefixFree) :
    ∃ c : ℕ, ∀ x : ℕ, universalPrefix.ecomplexity x ≤ M.ecomplexity x + c :=
  isAdditivelyOptimal_universalPrefix.exists_ecomplexity_le M ⟨hpart, hpf⟩

-- Prefix-free Chaitin incompleteness non-vacuity: true statements `n ≤ K(x)` with `n = 0`.
example : ∃ c : ℕ, ∀ x n, (x, n) ∈ {xn : ℕ × ℕ | xn.2 = 0} → n ≤ c :=
  minorizesPrefixPartrec_universalPrefix.exists_forall_le_of_rePred
    ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).computablePred.to_re.of_eq fun _ => Iff.rfl)
    fun x n h => by simp only [Set.mem_ofPred_eq] at h; simp [h]

/-! ### Executable binary Kraft–Chaitin allocator witnesses -/

example : kcAllocList [1, 2, 2] = some [[false], [true, false], [true, true]] := rfl

example : kcAllocList [2, 1, 2] = some [[false, false], [true], [false, true]] := rfl

example : kcAllocList [1, 1, 1] = none := rfl

example :
    ([[false], [true, false], [true, true]] : List (List Bool)).Pairwise PrefixDisjoint := by
  have hsum : (([1, 2, 2] : List ℕ).map fun ℓ => (2 : ℚ)⁻¹ ^ ℓ).sum ≤ 1 := by norm_num
  obtain ⟨codes, hcodes, -, hpair⟩ := kcAllocList_eq_some_of_sum_le_one hsum
  have heq : codes = [[false], [true, false], [true, true]] :=
    Option.some.inj (hcodes.symm.trans (by rfl))
  exact heq ▸ hpair

example :
    ([[false, false], [true], [false, true]] : List (List Bool)).Pairwise PrefixDisjoint := by
  have hsum : (([2, 1, 2] : List ℕ).map fun ℓ => (2 : ℚ)⁻¹ ^ ℓ).sum ≤ 1 := by norm_num
  obtain ⟨codes, hcodes, -, hpair⟩ := kcAllocList_eq_some_of_sum_le_one hsum
  have heq : codes = [[false, false], [true], [false, true]] :=
    Option.some.inj (hcodes.symm.trans (by rfl))
  exact heq ▸ hpair

/-! ### Finite `Ω` calculation and Chaitin's `Ω` regression clients -/

example :
    let twoProgramMethod : DescriptionMethod ℕ :=
      { run p :=
          if p = [false] then Computation.pure 0
          else if p = [true, false] then Computation.pure 1
          else Computation.empty ℕ }
    twoProgramMethod.IsPrefixFree ∧
      chaitinOmega twoProgramMethod ≤ 1 ∧
      chaitinOmega twoProgramMethod = (3 / 4 : ℝ) := by
  let twoProgramMethod : DescriptionMethod ℕ :=
    { run p :=
        if p = [false] then Computation.pure 0
        else if p = [true, false] then Computation.pure 1
        else Computation.empty ℕ }
  have hhalt :
      twoProgramMethod.haltingSet = ({[false], [true, false]} : Set (List Bool)) := by
    ext p
    simp only [haltingSet, Produces, twoProgramMethod, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    split_ifs with h1 h2
    · exact ⟨fun _ => Or.inl h1, fun _ =>
        ⟨0, Computation.mem_of_mem_runFor (n := 0) (Computation.runFor_pure 0 0 ▸ rfl)⟩⟩
    · exact ⟨fun _ => Or.inr h2, fun _ =>
        ⟨1, Computation.mem_of_mem_runFor (n := 0) (Computation.runFor_pure 1 0 ▸ rfl)⟩⟩
    · simp [h1, h2, Computation.notMem_empty]
  have hpf : twoProgramMethod.IsPrefixFree := by
    intro p hp q hq hpq
    rw [hhalt] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp at hpq ⊢
  refine ⟨hpf, hpf.chaitinOmega_le_one, ?_⟩
  have ha_mem : [false] ∈ twoProgramMethod.haltingSet :=
    (Set.ext_iff.mp hhalt _).mpr (Or.inl rfl)
  have hb_mem : [true, false] ∈ twoProgramMethod.haltingSet :=
    (Set.ext_iff.mp hhalt _).mpr (Or.inr rfl)
  let a : twoProgramMethod.haltingSet := ⟨[false], ha_mem⟩
  let b : twoProgramMethod.haltingSet := ⟨[true, false], hb_mem⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Subtype.val h
    simp [a, b] at hv
  let S : Finset twoProgramMethod.haltingSet := {a, b}
  have hzero : ∀ p ∉ S, (2 : ℝ)⁻¹ ^ (p : List Bool).length = 0 := fun p hp => by
    exfalso
    rcases (Set.ext_iff.mp hhalt _).mp p.2 with h1 | h2
    · exact hp (Finset.mem_insert.mpr (Or.inl (Subtype.ext h1)))
    · exact hp (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h2))))
  rw [chaitinOmega, tsum_eq_sum hzero, Finset.sum_pair hab]
  simp only [a, b, List.length_cons, List.length_nil]
  norm_num

-- Kraft–Chaitin client: prefix-free complexity bounds for request sequence `i ↦ (i + 1, i)`.
example :
    ∃ c : ℕ, ∀ i : ℕ, universalPrefix.ecomplexity i ≤ (i + 1 : ℕ) + c := by
  let req : ℕ → Option (ℕ × ℕ) := fun i => some (i + 1, i)
  have hreq : Computable req :=
    Computable.option_some.comp (Computable.pair Computable.succ Computable.id)
  have hsum : Summable fun i : ℕ =>
      match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ := by
    simpa [req, pow_succ'] using
      (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
        (2 : ℝ)⁻¹
  have hbound : ∑' i : ℕ,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1 := by
    have htsum : (∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + 1)) = 1 := by
      rw [show (fun i : ℕ => (2 : ℝ)⁻¹ ^ (i + 1)) = fun i => (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ i from
        funext fun i => by rw [pow_succ']]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    simpa [req] using htsum.le
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix.kraftChaitin hreq hsum hbound
  exact ⟨c, fun i => hc i (i + 1) i rfl⟩

example : 0 < chaitinOmega universalPrefix ∧ chaitinOmega universalPrefix < 1 :=
  ⟨chaitinOmega_universalPrefix_pos, chaitinOmega_universalPrefix_lt_one⟩

example : ¬ Computable (realBit (chaitinOmega universalPrefix)) :=
  not_computable_realBit_chaitinOmega_universalPrefix

example : Irrational (chaitinOmega universalPrefix) :=
  irrational_chaitinOmega_universalPrefix

example : ¬ ComputablePred fun q : List Bool => q ∈ universalPrefix.haltingSet :=
  not_computablePred_haltingSet_universalPrefix

example :
    ∃ c : ℕ, ∀ n : ℕ,
      n ≤ universalPrefixBits.complexity (realPrefix (chaitinOmega universalPrefix) n) + c :=
  exists_le_complexity_realPrefix_chaitinOmega

example :
    IsMartinLofRandom (realBit (chaitinOmega universalPrefix)) ∧
      ¬ IsMartinLofRandom (fun _ => false) :=
  ⟨isMartinLofRandom_chaitinOmega, not_isMartinLofRandom_of_computable (Computable.const false)⟩

example {S : Set (ℕ × Bool)} (hS : REPred fun p => p ∈ S)
    (hsound : ∀ i b, (i, b) ∈ S → realBit (chaitinOmega universalPrefix) i = b) : S.Finite :=
  finite_of_rePred_of_sound_realBit_chaitinOmega hS hsound

/-! ### Choice-free axiom checks -/

/--
info: 'Cslib.Kolmogorov.PrefixDisjoint.symm' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.PrefixDisjoint.symm

/--
info: 'Cslib.Kolmogorov.PrefixDisjoint.of_prefix_left' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.PrefixDisjoint.of_prefix_left

/--
info: 'Cslib.Kolmogorov.prefixDisjoint_append_false_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.prefixDisjoint_append_false_true

end CslibFrontierTests.KolmogorovPrefixOmega
