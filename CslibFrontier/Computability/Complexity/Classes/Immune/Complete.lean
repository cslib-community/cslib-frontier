/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Immune
public import CslibFrontier.Computability.Complexity.Problems.BoundedHalting
import CslibFrontier.Computability.Complexity.Classes.EXP.Padding
import CslibFrontier.Computability.Complexity.Classes.Ladner.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Problems complete for exponential time are not `P`-immune

**Berman's theorem** [Berman][Berman1976]: a problem that is `≤ᵖₘ`-complete for `E` has an infinite
subset in `P`, so it is not `P`-immune. This contrasts with the `P`-bi-immune problems in `E`
[Balcázar and Schöning][BalcazarSchoening1985]
(`CslibFrontier.Computability.Complexity.Classes.Immune.Construction`). Juedes and Lutz recall
Berman's theorem in their study of the complexity and distribution of hard problems
[Juedes and Lutz][JuedesLutz1995].
The argument below gives the same for the complement, so a complete problem is not `P`-bi-immune
(`Cslib.Complexity.not_isBiImmune_P_of_polyTimeComplete_E`). The same holds for `EXP`
(`Cslib.Complexity.not_isBiImmune_P_of_polyTimeComplete_EXP`). Problems are on bit words.
Bounded halting with a binary time bound is complete for `E`
(`Cslib.Complexity.BoundedHalting.polyTimeComplete_E`), so the hypothesis is met, and
`Cslib.Complexity.BoundedHalting.not_isBiImmune_P` applies the theorem to it.

Let `A` be decided within time `T`, and fix `b : Bool`. The test `C_b` reads the machine described
at the start of its input `w` (`Turing.MultiTapeTM.Universal.decodeDesc` of the first framed word)
and runs it on `w` for `G |w|` steps, where `G` eventually exceeds every polynomial: `2 ^ n` for
`E` and `2 ^ n ^ (k + 1)` for `EXP`. Suppose it halts with an output `y` no longer than `w`. Then
`w ∈ C_b` exactly when the decider of `A` rejects `y` within `T |w|` steps, and therefore exactly
when `y ∉ A`. Otherwise `w ∈ C_b` exactly when `b = true`. By padding, `C_b` is in `E` (resp.
`EXP`), so a polynomial-time reduction `f` maps `C_b` to `A`. Run the test on the description of
`f` padded with `m` zeros, `w_m`, with `m` large enough that `G |w_m|` exceeds the running time of
`f`. If `f w_m` were no longer than `w_m`, then `w_m ∈ C_b ↔ f w_m ∉ A` would contradict the
reduction. So `f w_m` is longer than `w_m`, and `f w_m ∈ A ↔ w_m ∈ C_b ↔ b = true`. Since
`|w_m| ≥ m`, the words `f w_m` with large `m` form an infinite problem in `P`: to recognize `y`,
try the `m ≤ |y|`. This problem lies inside `A` for `b = true` and inside `Aᶜ` for `b = false`.

## Main results

* `Cslib.Complexity.exists_infinite_subset_mem_P_of_polyTimeComplete_E`,
  `Cslib.Complexity.exists_infinite_subset_mem_P_of_polyTimeComplete_EXP`: a problem complete for
  `E` (resp. `EXP`) under polynomial-time many-one reductions, and its complement, have infinite
  subsets in `P`.
* `Cslib.Complexity.not_isBiImmune_P_of_polyTimeComplete_E`,
  `Cslib.Complexity.not_isBiImmune_P_of_polyTimeComplete_EXP`: such a problem is not
  `P`-bi-immune; in fact neither it nor its complement is `P`-immune.
* `Cslib.Complexity.BoundedHalting.exists_infinite_subset_mem_P`,
  `Cslib.Complexity.BoundedHalting.not_isBiImmune_P`: in particular for bounded halting with a
  binary time bound.

## References

* [J. L. Balcázar, U. Schöning, *Bi-immune sets for complexity classes*][BalcazarSchoening1985]
* [L. Berman, *On the structure of complete sets: almost everywhere complexity and infinitely often
  speedup*][Berman1976]
* [D. W. Juedes, J. H. Lutz, *The complexity and distribution of hard problems*][JuedesLutz1995]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Ladner

/-- The run of the machine described at the start of `w` on `w` itself, for `N` steps. -/
private noncomputable def simRun (w : List Bool) (N : ℕ) : List ℕ × Bool :=
  universal (decodeDesc (unframe w), w.map eBit, N)

/-- **Berman's test.** If the machine described at the start of `w` halts on `w` within `N` steps
with an output `y` no longer than `w`, the test is the opposite of the answer of the machine `dA`
on `y` within `κ N` steps; otherwise it is `b`. -/
private noncomputable def bermanTest (dA : Desc) (κ : ℕ → ℕ) (b : Bool) (p : List Bool × ℕ) :
    Bool :=
  if (simRun p.1 p.2).2 = true ∧ (simRun p.1 p.2).1.length ≤ p.1.length then
    !decide (universal (dA, (simRun p.1 p.2).1, κ p.2) = ([eBit true], true))
  else b

private theorem computableInPolyTime_bermanTest (dA : Desc) {κ : ℕ → ℕ}
    (hκ : ComputableInPolyTime κ encUnary encUnary) (b : Bool) :
    ComputableInPolyTime (bermanTest dA κ b) (encPair encBits encUnary) encBool := by
  have hs : ComputableInPolyTime (fun p : List Bool × ℕ => simRun p.1 p.2)
      (encPair encBits encUnary) eOut := by
    unfold simRun
    fun_prop
  unfold bermanTest
  fun_prop

/-- **Berman's argument.** Let `A` be decided by the machine described by `dA` within `κ (G n)`
steps on the words of length at most `n`, for large `n`, where `G` eventually exceeds every
polynomial. If, for both `b`, the words `w` with `bermanTest dA κ b (w, G |w|)` reduce to `A` in
polynomial time, then `A` and its complement have infinite subsets in `P`. -/
private theorem exists_infinite_subset_mem_P_of_reducible {A : Set (List Bool)}
    {g : List Bool → Bool} (hg : ∀ y, y ∈ A ↔ g y = true) (dA : Desc) {κ G : ℕ → ℕ} {L : ℕ}
    (hdA : ∀ n ≥ L, ∀ y : List Bool, y.length ≤ n →
      universal (dA, y.map eBit, κ (G n)) = ([eBit (g y)], true))
    (hG : ∀ t : ℕ → ℕ, PolynomiallyBounded t → ∀ᶠ n in Filter.atTop, t n ≤ G n)
    (hred : ∀ b, PolyTimeReducible encBits encBits
      {w | bermanTest dA κ b (w, G w.length) = true} A) :
    (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ A) ∧ (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ Aᶜ) := by
  -- for each `b`, an infinite problem in `P` inside `A` or its complement, according to `b`
  have key (b : Bool) : ∃ Q ∈ P encBits, Q.Infinite ∧ ∀ y ∈ Q, (y ∈ A ↔ b = true) := by
    obtain ⟨f, hf, hfA⟩ := hred b
    obtain ⟨t, _, ht, _, _, State, _, tm, htm⟩ := id hf
    have := Fintype.ofFinite State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    have hrun (x : List Bool) : (tm.runFrom (tm.initCfg x) (t x.length)).Halted ∧
        (tm.runFrom (tm.initCfg x) (t x.length)).output = f x :=
      (htm x).runFrom_of_le le_rfl
    -- the description of the reduction, padded with `m` zeros
    let pw (m : ℕ) : List Bool := frame (eDesc (desc eS eBit tm)) ++ List.replicate m false
    have hpw (m : ℕ) : m ≤ (pw m).length := by simp [pw]
    have hpad : ComputableInPolyTime pw encUnary encBits :=
      ComputableInPolyTime.bitsAppend (.const _) (.bitsReplicate false)
    have himage : ComputableInPolyTime (fun m => f (pw m)) encUnary encBits := hf.comp hpad
    obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hG t ht)
    let M := max M₁ L
    have hsim (m : ℕ) (hm : M ≤ m) :
        simRun (pw m) (G (pw m).length) = ((f (pw m)).map eBit, true) := by
      rw [simRun, decodeDesc_unframe_frame_append]
      exact universal_desc_of_halted_map eS tm (t := fun x => t x.length) hrun
        (hM₁ _ (by have := hpw m; omega))
    -- the reduction lengthens the padded descriptions
    have hlong (m : ℕ) (hm : M ≤ m) : (pw m).length < (f (pw m)).length := by
      by_contra! hle
      have h := hfA (pw m)
      simp only [Set.mem_ofPred_eq, bermanTest, hsim m hm, List.length_map, hle, and_self,
        ite_true, hdA _ (by have := hpw m; omega) _ hle, hg] at h
      cases hgf : g (f (pw m)) <;> simp [hgf, eBit] at h
    refine ⟨{y | ∃ m, M ≤ m ∧ f (pw m) = y}, ?_, ?_, ?_⟩
    · -- a witness `m` is at most the length of `y`
      have htest : ComputableInPolyTime
          (fun q : List Bool × ℕ => decide (M ≤ q.2) && decide (f (pw q.2) = q.1))
          (encPair encBits encUnary) encBool := by fun_prop
      have hlist : ComputableInPolyTime (fun y : List Bool => List.range (y.length + 1))
          encBits (encList encUnary) := by fun_prop
      refine ⟨fun y => (List.range (y.length + 1)).any fun m => decide (M ≤ m) &&
        decide (f (pw m) = y), ComputableInPolyTime.anyWithInput hlist htest, fun y => ?_⟩
      simp only [Set.mem_ofPred_eq, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m, by have := hpw m; have := hlong m hm; omega, hm, rfl⟩
      · rintro ⟨m, -, hm, rfl⟩
        exact ⟨m, hm, rfl⟩
    · -- the lengths are unbounded
      intro hfin
      obtain ⟨B, hB⟩ := (hfin.image List.length).bddAbove
      have := hB ⟨f (pw (M + B)), ⟨M + B, by omega, rfl⟩, rfl⟩
      have := hpw (M + B)
      have := hlong (M + B) (by omega)
      omega
    · rintro _ ⟨m, hm, rfl⟩
      rw [← hfA]
      simp only [Set.mem_ofPred_eq, bermanTest, hsim m hm, List.length_map,
        not_le.mpr (hlong m hm), and_false, ite_false]
  obtain ⟨Q₁, hQ₁, hinf₁, hA₁⟩ := key true
  obtain ⟨Q₀, hQ₀, hinf₀, hA₀⟩ := key false
  exact ⟨⟨Q₁, hQ₁, hinf₁, fun y hy => (hA₁ y hy).mpr rfl⟩,
    ⟨Q₀, hQ₀, hinf₀, fun y hy => by simpa using hA₀ y hy⟩⟩

variable {A : Set (List Bool)}

/-- **Berman's theorem for `E`** [Berman][Berman1976]: a problem complete for `E` under
polynomial-time many-one reductions has an infinite subset in `P`, and so does its complement. -/
theorem exists_infinite_subset_mem_P_of_polyTimeComplete_E (h : PolyTimeComplete @E encBits A) :
    (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ A) ∧ (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ Aᶜ) := by
  obtain ⟨k, c₁, c₂, _, hdec⟩ := mem_E_iff.mp h.1
  obtain ⟨g, ⟨_, State, _, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hdec
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine exists_infinite_subset_mem_P_of_reducible hg (desc eS eBit tm)
    (κ := fun N => c₁ * N ^ k + c₂) (G := fun n => 2 ^ n) (L := 0) (fun n _ y hy => ?_)
    (fun t ht => (PolynomiallyBounded.eventually_lt_two_pow ht).mono fun _ => le_of_lt)
    fun b => h.2 encBits _
      (setOf_mem_E_of_computableInPolyTime_pad (computableInPolyTime_bermanTest _ (by fun_prop) b))
  refine universal_desc_of_halted eS tm (t := fun x => c₁ * 2 ^ (k * x.length) + c₂)
    (fun x => (htm x).runFrom_of_le le_rfl) ?_
  rw [← pow_mul, mul_comm n k]
  gcongr

/-- **Berman's theorem for `EXP`**: a problem complete for `EXP` under polynomial-time many-one
reductions has an infinite subset in `P`, and so does its complement. -/
theorem exists_infinite_subset_mem_P_of_polyTimeComplete_EXP
    (h : PolyTimeComplete @EXP encBits A) :
    (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ A) ∧ (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ Aᶜ) := by
  obtain ⟨k, c₁, c₂, _, hdec⟩ := mem_EXP_iff.mp h.1
  obtain ⟨g, ⟨_, State, _, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hdec
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine exists_infinite_subset_mem_P_of_reducible hg (desc eS eBit tm)
    (κ := fun N => c₁ * N + c₂) (G := fun n => 2 ^ n ^ (k + 1)) (L := 1) (fun n hn y hy => ?_)
    (fun t ht => (PolynomiallyBounded.eventually_lt_two_pow ht).mono fun n hn =>
      hn.le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow k.succ_ne_zero n)))
    fun b => h.2 encBits _ (setOf_mem_EXP_of_computableInPolyTime_pad
      (computableInPolyTime_bermanTest _ (by fun_prop) b)
      (L := fun w => w.length ^ (k + 1)) (by fun_prop))
  refine universal_desc_of_halted eS tm (t := fun x => c₁ * 2 ^ x.length ^ k + c₂)
    (fun x => (htm x).runFrom_of_le le_rfl) ?_
  have hexp : y.length ^ k ≤ n ^ (k + 1) :=
    (Nat.pow_le_pow_left hy k).trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp)) _

/-- **No problem complete for `E` is `P`-bi-immune**; in fact neither the problem nor its
complement is `P`-immune [Berman][Berman1976]. -/
theorem not_isImmune_P_of_polyTimeComplete_E (h : PolyTimeComplete @E encBits A) :
    ¬ IsImmune (P encBits) A ∧ ¬ IsImmune (P encBits) Aᶜ :=
  let ⟨⟨_, hB, hinf, hBA⟩, ⟨_, hB', hinf', hBA'⟩⟩ :=
    exists_infinite_subset_mem_P_of_polyTimeComplete_E h
  ⟨fun hA => hinf (hA.finite_of_subset hB hBA), fun hA => hinf' (hA.finite_of_subset hB' hBA')⟩

/-- **No problem complete for `EXP` is `P`-bi-immune**; in fact neither the problem nor its
complement is `P`-immune. -/
theorem not_isImmune_P_of_polyTimeComplete_EXP (h : PolyTimeComplete @EXP encBits A) :
    ¬ IsImmune (P encBits) A ∧ ¬ IsImmune (P encBits) Aᶜ :=
  let ⟨⟨_, hB, hinf, hBA⟩, ⟨_, hB', hinf', hBA'⟩⟩ :=
    exists_infinite_subset_mem_P_of_polyTimeComplete_EXP h
  ⟨fun hA => hinf (hA.finite_of_subset hB hBA), fun hA => hinf' (hA.finite_of_subset hB' hBA')⟩

/-- **No problem complete for `E` is `P`-bi-immune.** -/
theorem not_isBiImmune_P_of_polyTimeComplete_E (h : PolyTimeComplete @E encBits A) :
    ¬ IsBiImmune (P encBits) A :=
  fun hA => (not_isImmune_P_of_polyTimeComplete_E h).1 hA.isImmune

/-- **No problem complete for `EXP` is `P`-bi-immune.** -/
theorem not_isBiImmune_P_of_polyTimeComplete_EXP (h : PolyTimeComplete @EXP encBits A) :
    ¬ IsBiImmune (P encBits) A :=
  fun hA => (not_isImmune_P_of_polyTimeComplete_EXP h).1 hA.isImmune

/-- **Berman's theorem for bounded halting**: bounded halting with a binary time bound, which is
complete for `E`, has an infinite subset in `P`, and so does its complement. -/
theorem BoundedHalting.exists_infinite_subset_mem_P :
    (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ BoundedHalting) ∧
      (∃ B ∈ P encBits, B.Infinite ∧ B ⊆ BoundedHaltingᶜ) :=
  exists_infinite_subset_mem_P_of_polyTimeComplete_E BoundedHalting.polyTimeComplete_E

/-- **Bounded halting is not `P`-bi-immune**, although it is not in `P`
(`Cslib.Complexity.BoundedHalting.notMem_P`). -/
theorem BoundedHalting.not_isBiImmune_P : ¬ IsBiImmune (P encBits) BoundedHalting :=
  not_isBiImmune_P_of_polyTimeComplete_E BoundedHalting.polyTimeComplete_E

end Cslib.Complexity
