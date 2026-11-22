/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CompCount
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# The counting classes of Theorem 7.1

The paper (§7) defines `⊕TIME[t]`, `Mod_qTIME[t]` and `C=TIME[t]` by nondeterministic
machines with running time `O(t)`, all of whose computations halt, whose number of accepting
computations is odd, nonzero modulo `q`, or equal to the number of rejecting computations. Here
the machine is a closed binary-choice table (`MultiTapePTM k Bool State`, one binary choice per
step, as in Complexitylib's `BPTIME`/`PPTIME`); a computation is a choice sequence up to the
halting step, counted by `CompCount.compCount` (its canonical coin string); accepting means
halting with output `[true]` and rejecting halting with output `[false]`. The clock is
`c₁ t(n) + c₂` as in Complexitylib's time classes.

## Main definitions

* `ParityTIME`, `ModTIME`, `CeqTIME`.

## Main results

* `univ_mem_ParityTIME`, `empty_mem_ParityTIME`, … : nonvacuity (one-step machines).
* `parityTIME_decided`, `modTIME_decided`, `ceqTIME_decided`: Theorem 7.1 for these classes from
  the clocked bits (`ClockedBits`); with `*_subset_dspace_of_residues`, from `ClockedResidues`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.SumProduct Exact CompCount Cslib Cslib.Complexity
  Cslib.Complexity.CountingSimulation _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type}

/-- **`⊕TIME[t]`**: an odd number of accepting computations, all computations halting within
`O(t)`. -/
def ParityTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (M : MultiTapePTM k Bool State), ∀ a,
      HaltsWithin M (enc a) (c₁ * t (enc a).length + c₂) ∧
        (a ∈ A ↔ Odd (compCount M [true] (enc a) (c₁ * t (enc a).length + c₂)))}

/-- **`Mod_qTIME[t]`**: a number of accepting computations not divisible by `q`. -/
def ModTIME (q : ℕ) (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (M : MultiTapePTM k Bool State), ∀ a,
      HaltsWithin M (enc a) (c₁ * t (enc a).length + c₂) ∧
        (a ∈ A ↔ ¬ q ∣ compCount M [true] (enc a) (c₁ * t (enc a).length + c₂))}

/-- **`C=TIME[t]`**: as many accepting as rejecting computations. -/
def CeqTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (M : MultiTapePTM k Bool State), ∀ a,
      HaltsWithin M (enc a) (c₁ * t (enc a).length + c₂) ∧
        (a ∈ A ↔ compCount M [true] (enc a) (c₁ * t (enc a).length + c₂) =
          compCount M [false] (enc a) (c₁ * t (enc a).length + c₂))}

/-! ### Nonvacuity: one-step machines -/

/-- The machine halting at its first step, emitting `f` of its coin. -/
def oneStep (f : Bool → Option Bool) : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step ⟨0, fun _ => (none, 0), f bit, none⟩ Empty.elim Empty.elim

theorem stepCoins_oneStep (f : Bool → Option Bool) (x : List Bool) (b : Bool) (cs : List Bool) :
    ((oneStep f).stepCoins (b :: cs) (Cfg.init (oneStep f).initial x)).state = none ∧
      ((oneStep f).stepCoins (b :: cs) (Cfg.init (oneStep f).initial x)).output = (f b).toList := by
  rw [MultiTapePTM.stepCoins_cons]
  have hs : (Cfg.init (oneStep f).initial x : Cfg 0 Bool Unit x).state = some () := rfl
  rw [MultiTapeTM.step_of_state hs]
  simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  set c := ((⟨0, fun _ => (none, 0), f b, none⟩ : Turing.Action 0 Bool Unit).apply
    (Cfg.init (oneStep f).initial x))
  have hc : c.state = none := rfl
  change ((oneStep f).stepCoins cs c).state = none ∧ ((oneStep f).stepCoins cs c).output = _
  rw [HaltCount.stepCoins_of_halted _ cs hc]
  exact ⟨rfl, by simp [c, Action.apply]⟩

theorem acceptCount_one (V : List Bool × List Bool → Bool) (x : List Bool) :
    Complexity.acceptCount V x 1 =
      (if V (x, [true]) = true then 1 else 0) + (if V (x, [false]) = true then 1 else 0) := by
  unfold Complexity.acceptCount
  rw [BitString.card_filter_ofFn_succ 0 (fun w => V (x, w) = true)]
  congr 1 <;> rw [Finset.card_filter] <;> simp

open Classical in
theorem compCount_oneStep (f : Bool → Option Bool) (x out : List Bool) :
    compCount (oneStep f) out x 1 =
      (if (f true).toList = out then 1 else 0) + (if (f false).toList = out then 1 else 0) := by
  unfold compCount
  rw [acceptCount_one]
  have hc : ∀ b, CanonFrom (oneStep f) (Cfg.init (oneStep f).initial x) [b] := fun b =>
    ⟨fun h => absurd h (by simp [oneStep]), trivial⟩
  congr 1
  · obtain ⟨h1, h2⟩ := stepCoins_oneStep f x true []
    simp only [decide_eq_true_eq, h1, h2, hc true, true_and]
  · obtain ⟨h1, h2⟩ := stepCoins_oneStep f x false []
    simp only [decide_eq_true_eq, h1, h2, hc false, true_and]

theorem haltsWithin_oneStep (f : Bool → Option Bool) (x : List Bool) :
    HaltsWithin (oneStep f) x 1 := fun coins hc => by
  rcases coins with _ | ⟨b, cs⟩
  · simp at hc
  · exact (stepCoins_oneStep f x b cs).1

variable {enc : α ↪ List Bool} {t : ℕ → ℕ}

/-- The clock `0 · t + 1`. -/
theorem one_clock (n : ℕ) : 0 * t n + 1 = 1 := by simp

theorem univ_mem_ParityTIME : (Set.univ : Set α) ∈ ParityTIME enc t :=
  ⟨0, 1, 0, Unit, inferInstance, oneStep fun b => if b then some true else none, fun a => by
    rw [one_clock]
    exact ⟨haltsWithin_oneStep _ _, by simp [compCount_oneStep]⟩⟩

theorem empty_mem_ParityTIME : (∅ : Set α) ∈ ParityTIME enc t :=
  ⟨0, 1, 0, Unit, inferInstance, oneStep fun _ => none, fun a => by
    rw [one_clock]
    exact ⟨haltsWithin_oneStep _ _, by simp [compCount_oneStep]⟩⟩

theorem univ_mem_ModTIME {q : ℕ} (hq : 2 ≤ q) : (Set.univ : Set α) ∈ ModTIME q enc t :=
  ⟨0, 1, 0, Unit, inferInstance, oneStep fun b => if b then some true else none, fun a => by
    rw [one_clock]
    refine ⟨haltsWithin_oneStep _ _, ?_⟩
    simp only [compCount_oneStep, Set.mem_univ, true_iff]
    simp only [ite_true, Option.toList_some, Bool.false_eq_true, ite_false, Option.toList_none]
    norm_num
    omega⟩

theorem empty_mem_ModTIME {q : ℕ} : (∅ : Set α) ∈ ModTIME q enc t :=
  ⟨0, 1, 0, Unit, inferInstance, oneStep fun _ => none, fun a => by
    rw [one_clock]
    exact ⟨haltsWithin_oneStep _ _, by simp [compCount_oneStep]⟩⟩

theorem univ_mem_CeqTIME : (Set.univ : Set α) ∈ CeqTIME enc t :=
  ⟨0, 1, 0, Unit, inferInstance, oneStep some, fun a => by
    rw [one_clock]
    exact ⟨haltsWithin_oneStep _ _, by simp [compCount_oneStep]⟩⟩

theorem empty_mem_CeqTIME : (∅ : Set α) ∈ CeqTIME enc t :=
  ⟨0, 1, 0, Unit, inferInstance, oneStep fun b => if b then some true else none, fun a => by
    rw [one_clock]
    exact ⟨haltsWithin_oneStep _ _, by simp [compCount_oneStep]⟩⟩

/-! ### Theorem 7.1 for the counting classes -/

/-- The halting test and the counts at a clock where every run has halted. -/
theorem compCount_at_halt {k : ℕ} {State : Type} {M : MultiTapePTM k Bool State} {a : List Bool}
    {T τ : ℕ} (hT : HaltsWithin M a T) (hτ : HaltsWithin M a τ) (out : List Bool) :
    compCount M out a τ = compCount M out a T := by
  rcases le_total T τ with h | h
  · exact compCount_eq_of_halted hT h out
  · exact (compCount_eq_of_halted hτ h out).symm

/-- **The common clock search of the counting classes.** Given a binary-choice machine `M`
halting within `c₁ t(n) + c₂` and a decision program built from the bits of the clocked accept
counts of `drain M` and `drain (flip M)` (the numbers of accepting and rejecting computations),
correct whenever these counts are the counts of `M`, the problem is decided in time
`2^(C·SqrtLog t)` and space `C·SqrtLog t`. -/
theorem decided_of_compCounts (hB : ClockedBits) (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    {k : ℕ} {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (c₁ c₂ : ℕ)
    (hhalt : ∀ a : List Bool, HaltsWithin M a (c₁ * t a.length + c₂))
    (Dq : Prog → Prog → Prog) (τD : ℕ)
    (hD : ∀ (Pa Pr : Prog) (a : List Bool) (τ D : ℕ), Prog'.closed 3 Pa = true →
      Prog'.closed 3 Pr = true → 2 ≤ D → τD ≤ τ → a.length ≤ τ →
      compCount M [true] a (c₁ * t a.length + c₂) ≤ 2 ^ paddedTime τ →
      compCount M [false] a (c₁ * t a.length + c₂) ≤ 2 ^ paddedTime τ →
      BitsOK a Pa τ a.length (compCount M [true] a (c₁ * t a.length + c₂)) (2 ^ (D * SqrtLog τ)) →
      BitsOK a Pr τ a.length (compCount M [false] a (c₁ * t a.length + c₂))
        (2 ^ (D * SqrtLog τ)) →
      (Dq Pa Pr).Bounded a (2 ^ (D * SqrtLog τ)) [τ, a.length] ∧
        (0 < (Dq Pa Pr).eval a [τ, a.length] ↔ a ∈ A)) :
    DecidedInSqrtLog t A := by
  classical
  obtain ⟨PH, CH, τH, hPHc, hPH⟩ := hB k State (HaltCount.haltMark M)
  obtain ⟨Pa, CA, τA, hPac, hPa⟩ := hB k (Option State) (drain M)
  obtain ⟨Pr, CR, τR, hPrc, hPr⟩ := hB k (Option State) (drain (flip M))
  set C := CH + CA + CR + 2
  have hhaltT : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ →
      (0 < (bitAtPad PH).eval a [τ, a.length] ↔ HaltsWithin M a (paddedTime τ)) := by
    intro a τ ha hτ
    rw [eval_bitAtPad hPHc (bitsOK_of hPH ha hτ (D := C) (by omega)),
      ← eq_two_pow_iff_bit acceptCount_le_two_pow, HaltCount.acceptCount_haltMark_eq_two_pow_iff]
    rfl
  refine decidable_of_clockedTests ht A (bitAtPad PH) (Dq Pa Pr) C C
    (max (max (max τH τA) (max τR τD)) 2) c₁ c₂ ?_ ?_ ?_
  · intro a τ ha hτ
    exact bounded_bitAtPad hPHc (bitsOK_of hPH ha (by omega) (by omega)) (by omega)
      (two_mul_add_two_le (by omega))
  · intro a τ ha hτ hT
    exact (hhaltT a τ ha (by omega)).mpr ((hhalt a).mono (hT.trans (le_paddedTime τ)))
  · intro a τ ha hτ hpos
    have hall := (hhaltT a τ ha (by omega)).mp hpos
    have hallf : HaltsWithin (flip M) a (paddedTime τ) := (haltsWithin_flip M).mpr hall
    have eA : (drain M).acceptCount a (paddedTime τ) = compCount M [true] a
        (c₁ * t a.length + c₂) := by
      rw [acceptCount_drain M hall, compCount_at_halt (hhalt a) hall]
    have eR : (drain (flip M)).acceptCount a (paddedTime τ) =
        compCount M [false] a (c₁ * t a.length + c₂) := by
      rw [acceptCount_drain (flip M) hallf, compCount_flip, compCount_at_halt (hhalt a) hall]
    have hokA := bitsOK_of hPa ha (show τA ≤ τ by omega) (D := C) (by omega)
    have hokR := bitsOK_of hPr ha (show τR ≤ τ by omega) (D := C) (by omega)
    have hZa : compCount M [true] a (c₁ * t a.length + c₂) ≤ 2 ^ paddedTime τ :=
      eA ▸ acceptCount_le_two_pow
    have hZr : compCount M [false] a (c₁ * t a.length + c₂) ≤ 2 ^ paddedTime τ :=
      eR ▸ acceptCount_le_two_pow
    rw [eA] at hokA
    rw [eR] at hokR
    exact hD Pa Pr a τ C hPac hPrc (by omega) (by omega) ha hZa hZr hokA hokR

/-- The counts are at most `2^T` for every clock `T` at which they are taken at `paddedTime τ`. -/
theorem compCount_le_of_halt {k : ℕ} {State : Type} {M : MultiTapePTM k Bool State}
    {a : List Bool} {T τ : ℕ} (hT : HaltsWithin M a T) (hτ : HaltsWithin M a τ)
    (out : List Bool) : compCount M out a T ≤ 2 ^ τ := by
  rw [← compCount_at_halt hT hτ]; exact acceptCount_le_two_pow

/-- **Theorem 7.1 for `⊕TIME`**, from the clocked bits. -/
theorem parityTIME_decided (hB : ClockedBits) (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    (hA : A ∈ ParityTIME encBits t) : DecidedInSqrtLog t A := by
  obtain ⟨c₁, c₂, k, State, hfin, M, hM⟩ := hA
  simp only [encBits_apply] at hM
  refine decided_of_compCounts hB ht M c₁ c₂ (fun a => (hM a).1) (fun Pa _ => bitProg Pa 0) 0
    fun Pa Pr a τ D hPa _ hD _ ha _ _ hokA _ => ⟨bounded_bitProg hPa hokA (Nat.zero_le _), ?_⟩
  rw [eval_bitProg hPa hokA, (hM a).2, pow_zero, Nat.div_one, Nat.odd_iff]
  omega

/-- **Theorem 7.1 for `Mod_qTIME`**, from the clocked bits. -/
theorem modTIME_decided (hB : ClockedBits) (ht : ∀ n, n ≤ t n) {q : ℕ} (hq : 1 ≤ q)
    {A : Set (List Bool)} (hA : A ∈ ModTIME q encBits t) : DecidedInSqrtLog t A := by
  obtain ⟨c₁, c₂, k, State, hfin, M, hM⟩ := hA
  simp only [encBits_apply] at hM
  refine decided_of_compCounts hB ht M c₁ c₂ (fun a => (hM a).1) (fun Pa _ => modProg Pa q)
    (q + 2) fun Pa Pr a τ D hPa _ hD hτ ha hZa _ hokA _ => ⟨bounded_modProg hPa hokA hq
      (by omega) (two_mul_add_two_le hD)
      ((by omega : 2 * q + 2 ≤ 2 * τ + 2).trans (two_mul_add_two_le hD)), ?_⟩
  rw [eval_modProg hPa hokA, horner_bits _ q _ (lt_of_le_of_lt hZa
    (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))), (hM a).2,
    Nat.dvd_iff_mod_eq_zero]
  omega

/-- **Theorem 7.1 for `C=TIME`**, from the clocked bits. -/
theorem ceqTIME_decided (hB : ClockedBits) (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    (hA : A ∈ CeqTIME encBits t) : DecidedInSqrtLog t A := by
  obtain ⟨c₁, c₂, k, State, hfin, M, hM⟩ := hA
  simp only [encBits_apply] at hM
  refine decided_of_compCounts hB ht M c₁ c₂ (fun a => (hM a).1) eqBitsProg 2
    fun Pa Pr a τ D hPa hPr hD hτ ha hZa hZr hokA hokR =>
      ⟨bounded_eqBitsProg hPa hPr hokA hokR (by omega) (two_mul_add_two_le hD), ?_⟩
  have hlt : ∀ Z, Z ≤ 2 ^ paddedTime τ → Z < 2 ^ (paddedTime τ + 1) := fun Z hZ =>
    lt_of_le_of_lt hZ (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
  rw [eval_eqBitsProg hPa hPr hokA hokR, (hM a).2, eq_iff_bits (hlt _ hZa) (hlt _ hZr)]
  split_ifs with h <;> simp [h]

/-! ### Theorem 7.1 from the clocked residues -/

/-- **Theorem 7.1 for `⊕TIME`**: `⊕TIME[t] ⊆ DSPACE[t/√log t]`, from a residue form of
Theorem 2.3 at an arbitrary clock. -/
theorem parityTIME_subset_dspace_of_residues (hR : ClockedResidues) (ht : ∀ n, n ≤ t n) :
    ParityTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) := fun _ hA =>
  (parityTIME_decided (clockedBits_of_clockedResidues hR) ht hA).mem_DSPACE

/-- **Theorem 7.1 for `Mod_qTIME`** (`q ≥ 1`). -/
theorem modTIME_subset_dspace_of_residues (hR : ClockedResidues) (ht : ∀ n, n ≤ t n) {q : ℕ}
    (hq : 1 ≤ q) : ModTIME q encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) := fun _ hA =>
  (modTIME_decided (clockedBits_of_clockedResidues hR) ht hq hA).mem_DSPACE

/-- **Theorem 7.1 for `C=TIME`**. -/
theorem ceqTIME_subset_dspace_of_residues (hR : ClockedResidues) (ht : ∀ n, n ≤ t n) :
    CeqTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) := fun _ hA =>
  (ceqTIME_decided (clockedBits_of_clockedResidues hR) ht hA).mem_DSPACE

end Cslib.Complexity.NtimeDspace.Cross
