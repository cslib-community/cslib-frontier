/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.BSADecide
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# `BSA` is decidable in linear space

`bsaDecide` decides `BSA` (`bsaDecide_eq`), within space linear in the query
(`computableInSpace_BSA`): the shape test is a finite automaton read in one pass; the padding test
compares `2^|w|` with `b` in binary; and under the padding `2^|w| ≤ b`, decoding the description
`w` (polynomial in `|w|`) and the budgeted universal run (linear in the description, the budget
`b`, the clock `2^(b+1)` in binary and `log |x|`) fit in space `O(b)`.

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.bsaDecide_eq`,
`Cslib.Complexity.NtimeDspace.Oracle.computableInSpace_BSA`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-- The budget of a query: the number of symbols after the two frames. -/
def bsaBudget (q : List Bool) : ℕ := (dropFrame (dropFrame q)).length

/-- **The decision procedure for `BSA`.** -/
noncomputable def bsaDecide (q : List Bool) : Bool :=
  if bsaValid q && decide (2 ^ (unframe q).length ≤ bsaBudget q) then
    budgetAccepts (budgetedUniversal (decodeDesc (unframe q), (unframe (dropFrame q)).map eBit,
      2 ^ (bsaBudget q + 1), bsaBudget q))
  else false

open scoped Classical in
theorem bsaDecide_eq (q : List Bool) : bsaDecide q = decide (q ∈ BSA) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    simp only [bsaDecide] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hv, hp⟩ := hc
    refine ⟨unframe q, unframe (dropFrame q), bsaBudget q, eq_bsaQuery_of_valid hv, hp, ?_⟩
    exact (acceptsWithin_iff_budgeted _ _ _).mpr h
  · rintro ⟨w, x, b, rfl, hp, ha⟩
    obtain ⟨h1, h2, h3⟩ := parts_bsaQuery w x b
    have hb : bsaBudget (bsaQuery w x b) = b := by simp [bsaBudget, h3]
    simp only [bsaDecide, bsaValid_bsaQuery, h1, h2, hb, hp, decide_true, Bool.and_self, ite_true]
    exact (acceptsWithin_iff_budgeted _ _ _).mp ha

open ComputableInSpace in
/-- The shape test, in linear space. -/
lemma bsaValid_inSpace : ComputableInSpace bsaValid encBits encBool fun q => q.length := by
  have hcard : Nat.card VSt = 6 := by rw [Nat.card_eq_fintype_card]; rfl
  have hl : ComputableInSpace (fun q : List Bool => q) encBits encBits fun q => q.length :=
    of_inO ComputableInO.id'
  have hi : ComputableInSpace (fun _ : List Bool => VSt.f1) encBits (encFinite VSt)
      fun q => q.length := const _
  have hs : ComputableInSpace (fun p : VSt × Bool => vstep p.1 p.2)
      (encPair (encFinite VSt) encBool)
      (encFinite VSt) fun p => (encPair (encFinite VSt) encBool p).length := of_finite _
  have hfold := foldl (encA := encBool) (encL := encBits) hl hi hs (Q := fun _ => 14)
    (B := fun _ => 6)
    (fun q i hi => by
      have := length_encFinite_lt (((q.take i).foldl vstep VSt.f1))
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun q i hi => by
      have := length_encFinite_lt (((q.take i).foldl vstep VSt.f1))
      omega)
  refine (budget_finite (encC := encBool) (fun s : VSt => decide (s = .r))
    (hfold.weaken ⟨25, fun q => ?_⟩)).of_enc_eq fun q => rfl
  simp only [encBits_apply]
  omega

open ComputableInSpace in
/-- The padding test, in linear space. -/
lemma bsaPad_inSpace : ComputableInSpace (fun q => decide (2 ^ (unframe q).length ≤ bsaBudget q))
    encBits encBool fun q => q.length := by
  have hu : ComputableInSpace unframe encBits encBits fun q => q.length :=
    of_inO (ComputableInO.of_linear (.of_unframe fun _ => rfl))
  have hd : ComputableInSpace dropFrame encBits encBits fun q => q.length :=
    of_inO (ComputableInO.of_linear (.of_dropFrame fun _ => rfl))
  have hw : ComputableInSpace (fun q => 2 ^ (unframe q).length) encBits encNat fun q => q.length :=
    budget_comp_lin (g := fun a : List Bool => 2 ^ (encBits a).length)
      (of_inO (ComputableInDegree.two_pow_length encBits).inO_one) (.refl _) hu
  have hr := budget_comp_lin hd (.refl _) hd
  have hb : ComputableInSpace bsaBudget encBits encNat fun q => q.length :=
    budget_comp_lin (g := fun l : List Bool => l.length) (of_inO ComputableInO.lengthNat)
      ⟨1, fun l => by simp [encBits_apply]⟩ hr
  have hlt := budget_comp_lin natLt linear_succ (budget_prod hb hw)
  refine (budget_finite (encC := encBool) (fun b : Bool => !b) hlt).of_enc_eq fun q => ?_
  simp only [encBool_apply, List.cons.injEq, and_true]
  by_cases h : 2 ^ (unframe q).length ≤ bsaBudget q
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

/-- **`BSA` is decidable within linear space.** -/
theorem computableInSpace_BSA : open scoped Classical in
    ComputableInSpace (fun q => decide (q ∈ BSA)) encBits encBool fun q => q.length := by
  classical
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  have hu : ComputableInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hdr : ComputableInO dropFrame encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableInO.of_linear (.of_dropFrame fun _ => rfl)
  have hdesc := hdec.inO.comp hu
  have hsym := Universal.computableInO_map_eBit.comp (hu.comp hdr)
  have hbU := ComputableInO.lengthUnary.comp (hdr.comp hdr)
  have hclock := ((ComputableInDegree.two_pow_length encUnary).inO_one.comp_linear
    (ComputableInDegree.unary_succ.inO_one.comp hbU)).of_enc_eq (encC := encNat)
    (g := fun q : List Bool => 2 ^ (bsaBudget q + 1)) fun q => by
      simp only [Function.comp_apply, encUnary_apply, List.length_replicate, bsaBudget]
  have hU := computableInO_budgetedUniversal.comp
    (hdesc.prod (hsym.prod (hclock.prod hbU)))
  have hacc := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp_linear
        (Cslib.Complexity.Diagonal.computableInO_verdict.comp hU)
  obtain ⟨cD, -, hcD⟩ := hdesc
  obtain ⟨cA, hcA⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
    (by fun_prop)
  have hc := (bsaValid_inSpace.prod bsaPad_inSpace)
  have hc' := ComputableInSpace.budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (hc.weaken (S₁ := fun q : List Bool => q.length) ⟨2, fun q => by
      show q.length + q.length ≤ 2 * (q.length + 1); omega⟩)
  have h := ComputableInSpace.ite hc' (ComputableInSpace.of_inO hacc)
    (ComputableInSpace.const (encB := encBool) false)
  refine (h.weaken ⟨300 * (cD + 1) * (cA + 1) + 300, fun q => ?_⟩).of_enc_eq fun q => ?_
  · dsimp only [Function.comp_apply, encBits_apply]
    split_ifs with hs
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hv, hp⟩ := hs
      have hq := congrArg List.length (eq_bsaQuery_of_valid hv)
      rw [length_bsaQuery] at hq
      have hdq : (dropFrame q).length = 2 * (unframe (dropFrame q)).length + 1 + bsaBudget q := by
        conv_lhs => rw [eq_bsaQuery_of_valid hv]
        simp [bsaQuery, bsaBudget, List.append_assoc]
      have hA : ((unframe q).length + 1) ^ dd ≤ cA * q.length :=
        (hcA _).trans (Nat.mul_le_mul_left _ (by simp only [bsaBudget] at hp hq; omega))
      have hD := hcD q
      have hB := budgetSpace_le (decodeDesc (unframe q)) ((unframe (dropFrame q)).map eBit)
        (bsaBudget q) (2 ^ (bsaBudget q + 1))
      have hO := length_eOut_budgetedUniversal_le (decodeDesc (unframe q))
        ((unframe (dropFrame q)).map eBit) (bsaBudget q) (2 ^ (bsaBudget q + 1))
      have hclk : (encNat (2 ^ (bsaBudget q + 1))).length = bsaBudget q + 2 := by
        rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
      have hlen : (encNat (((unframe (dropFrame q)).map eBit).length + 1)).length ≤
          (unframe (dropFrame q)).length + 1 := by
        rw [List.length_map]; exact Universal.length_encNat_le _
      have hr : (encUnary (dropFrame (dropFrame q)).length).length =
          (dropFrame (dropFrame q)).length := by simp
      have hmax : ((unframe (dropFrame q)).map eBit).foldr max 0 ≤ 1 :=
        listMax_le fun b _ => by cases b <;> decide
      simp only [descLen, Function.comp_apply, encBits_apply] at hB hD
      have e₁ : cD * (q.length + ((unframe q).length + 1) ^ dd + 1) ≤
          cD * (q.length + cA * q.length + 1) := Nat.mul_le_mul_left _ (by omega)
      have e₂ : cD * (q.length + cA * q.length + 1) + cA * q.length ≤
          (cD + 1) * (cA + 1) * (q.length + 1) := by
        have : (cD + 1) * (cA + 1) * (q.length + 1) =
            cD * (q.length + cA * q.length + 1) + cA * q.length + (cD * cA + cA + q.length + 1)
            := by ring
        omega
      have e₃ : (300 * (cD + 1) * (cA + 1) + 300) * (q.length + 1) =
          300 * ((cD + 1) * (cA + 1) * (q.length + 1)) + 300 * (q.length + 1) := by ring
      simp only [bsaBudget] at *
      omega
    · have : 2 * (q.length + 1) ≤ (300 * (cD + 1) * (cA + 1) + 300) * (q.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  · rw [← bsaDecide_eq]
    rfl

end Cslib.Complexity.NtimeDspace.Oracle
