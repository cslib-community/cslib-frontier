/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.Time.SigmaThree
public import CslibFrontier.Computability.Complexity.Classes.Time.Polynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.LinearClock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Foundations.Data.BitString.Binary
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Random-Access vs Sequential Alternating Time, Relativization, and Checkpoint Speedups

This module formalizes four core structural ingredients for the containment question
`Σ₂TIME(T) ⊆ Σ₃TIME(T / √(log T))`:

1. **Sequential-input obstruction (`lastBitLanguage`)**: On sequential-input `MultiTapeATM`,
   deciding whether the last bit of `x` is `true` lies in `DTIME(n) ⊆ Σ₂TIME(n)` yet fails to
   lie in `ATIME(n / √(log n))` because a machine running for `t ≤ n - 1` steps satisfies
   `inputPos ≤ t + 1` and cannot reach cell `n - 1` (`cfg.inputPos = n`). This forces
   random-access input conventions for sublinear-in-`T` bounds when `F(T) < n`.
2. **Clocked Index-Tape Alternating Machines (`RAATM`)**: We formalize multitape alternating
   Turing machines with a sequential-edit binary index tape (`idxTape`) and unit-cost input query
   `input[addr]?`, prove `O(log n)` input-length discovery (`lastBitLanguage ∈ RADTIME(log n)`),
   check model compatibility with the supplied bit-counting hypothesis `(H)`, and prove an
   `RAATM` selector-bit composition theorem.
3. **Relativization counterexample**: Using `∀`-winning subtree query counting (`≤ 2^t` queried
   strings on a depth-`t` binary alternating oracle tree), we prove an unconditional oracle
   separation showing `NTIME^A(T) ⊈ ATIME^A(t)` whenever `2^t < 2^T`, refuting relativized
   forms of both the target containment and `(H)`.
4. **Unconditional checkpoint speedups (`NTISP` & asymmetric `Σ₂-TISP`)**: We prove abstract
   clocked block-simulation theorems with explicit completeness, soundness, and certificate
   accounting (`Σ₃` for nondeterministic block simulation, `Σ₂` for deterministic simulation),
   and establish the arithmetic bound `√(T * (T / log T)) = O(T / √(log T))`.

## Main results

* `Cslib.Complexity.lastBitLanguage_mem_DTIME`
* `Cslib.Complexity.lastBitLanguage_mem_SigmaTwoTIME`
* `Cslib.Complexity.lastBitLanguage_notMem_ATIME_sqrtLog`
* `Cslib.Complexity.lastBitLanguage_mem_RADTIME_log`
* `Cslib.Complexity.RAATM.accepts_iff_accCount_pos`
* `Cslib.Complexity.exists_RAATIME_evaluator_of_H`
* `Cslib.Complexity.forall_RAATIME_evaluator_of_H`
* `Cslib.Complexity.selectorBit_composition`
* `Cslib.Complexity.oracle_separation_family`
* `Cslib.Complexity.RAATM_ntisp_block_simulation`
* `Cslib.Complexity.sigma2AsymmetricBlockSimulation`
* `Cslib.Complexity.sqrt_mul_le_div_sqrt_log`

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP Question*][BakerGillSolovay1975]
* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

public section

namespace Cslib.Complexity

open Turing
open Turing.MultiTapeTM

/-! ### Part I: Sequential-input separation on `MultiTapeATM` -/

section SequentialSeparation

/-- The language of non-empty bit strings whose last bit is `true`. -/
def lastBitLanguage : Set (List Bool) :=
  {x | x.getLast? = some true}

private def lastBitT : Transducer Bool (Option Bool) where
  q₀ := none
  step _ b := (some b, [])
  final q := [q.getD false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem lastBitT_run (q : Option Bool) (x : List Bool) :
    lastBitT.run q x = [match x.getLast? with | some b => b | none => q.getD false] := by
  induction x generalizing q with
  | nil => rfl
  | cons a xs ih =>
    change [] ++ lastBitT.run (some a) xs = _
    rw [List.nil_append, ih (some a)]
    cases xs with
    | nil => rfl
    | cons c cs =>
      cases hlast : (c :: cs).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) (List.cons_ne_nil c cs)
      | some _ => simp [hlast]

theorem computableInO_indicator_lastBitLanguage :
    ComputableInO (Turing.MultiTapeTM.indicator lastBitLanguage) encBits encBool
      (fun x => x.length) (fun x => x.length) := by
  have hrun : ∀ x : List Bool,
      lastBitT.run none x = encBool (Turing.MultiTapeTM.indicator lastBitLanguage x) := by
    intro x
    rw [lastBitT_run]
    cases h : x.getLast? with
    | none => simp [Turing.MultiTapeTM.indicator, lastBitLanguage, h]
    | some b => cases b <;> simp [Turing.MultiTapeTM.indicator, lastBitLanguage, h]
  exact (ComputableInDegree.of_transducer lastBitT fun l => (hrun l).symm).inO_one

/-- On sequential multitape machines, `lastBitLanguage` is decidable in linear time `O(n)`. -/
theorem lastBitLanguage_mem_DTIME : lastBitLanguage ∈ DTIME encBits id := by
  rcases computableInO_indicator_lastBitLanguage with ⟨c, hc, -⟩
  refine ⟨c, c, fun n => c * (n + 1), ?_⟩
  exact hc.mono (fun a => by simp [id, Nat.mul_add]) (fun _ => le_rfl)

/-- On sequential multitape verifiers, `lastBitLanguage` lies in `Σ₂TIME(n)`. -/
theorem lastBitLanguage_mem_SigmaTwoTIME : lastBitLanguage ∈ SigmaTwoTIME encBits id := by
  rw [mem_SigmaTwoTIME_iff]
  let V : List Bool × (List Bool × List Bool) → Bool :=
    fun x => Turing.MultiTapeTM.indicator lastBitLanguage x.1
  refine ⟨V, 1, ?_, fun a L _ => ?_⟩
  · have hfst : ComputableInO (fun x : List Bool × (List Bool × List Bool) => x.1)
        (encPair encBits (encPair encBits encBits)) encBits
        (fun x => (encPair encBits (encPair encBits encBits) x).length)
        (fun x => (encPair encBits (encPair encBits encBits) x).length) := by fun_prop
    exact computableInO_indicator_lastBitLanguage.comp_linear hfst
  · simp only [V, Turing.MultiTapeTM.indicator, lastBitLanguage, Set.mem_ofPred_eq]
    constructor
    · intro ha
      refine ⟨List.replicate L false, List.length_replicate, fun _ _ => ?_⟩
      simp [ha]
    · rintro ⟨_, -, h⟩
      have h' := h (List.replicate L false) List.length_replicate
      by_cases ha : a.getLast? = some true
      · exact ha
      · simp [ha] at h'

/-- Two configurations over same-length inputs whose state, head positions, work tapes, and
output agree. -/
private def SameExceptLast {k : ℕ} {State : Type} {x₁ x₂ : List Bool}
    (c₁ : Cfg k Bool State x₁) (c₂ : Cfg k Bool State x₂) : Prop :=
  c₁.state = c₂.state ∧
    c₁.inputPos.val = c₂.inputPos.val ∧
    c₁.workTapes = c₂.workTapes ∧
    c₁.workTapePos = c₂.workTapePos ∧
    c₁.output = c₂.output

private theorem inputSymbol_eq_of_sameExceptLast {k : ℕ} {State : Type} {n : ℕ}
    {x₁ x₂ : List Bool} (hx₁ : x₁.length = n) (hx₂ : x₂.length = n)
    (hagree : ∀ i : ℕ, i + 1 < n → x₁[i]? = x₂[i]?)
    {c₁ : Cfg k Bool State x₁} {c₂ : Cfg k Bool State x₂}
    (hsame : SameExceptLast c₁ c₂) (hpos : c₁.inputPos.val + 1 ≤ n) :
    c₁.inputSymbol = c₂.inputSymbol := by
  rcases hsame with ⟨_, hposEq, _, _, _⟩
  unfold Cfg.inputSymbol
  by_cases hz1 : c₁.inputPos = 0
  · have hz2 : c₂.inputPos = 0 := Fin.ext (hposEq.symm.trans (congrArg Fin.val hz1))
    rw [dite_eq_left hz1, dite_eq_left hz2]
  · have hz2 : c₂.inputPos ≠ 0 := fun h => hz1 (Fin.ext (hposEq.trans (congrArg Fin.val h)))
    have hval1 : c₁.inputPos.val ≠ 0 := fun h => hz1 (Fin.ext h)
    have hhi1 : c₁.inputPos.val ≠ x₁.length + 1 := by omega
    have hhi2 : c₂.inputPos.val ≠ x₂.length + 1 := by omega
    rw [dite_eq_right hz1, dite_eq_right hz2]
    rw [dite_eq_right hhi1, dite_eq_right hhi2]
    have hidx : (c₁.inputPos.val - 1) + 1 < n := by omega
    have hget := hagree (c₁.inputPos.val - 1) hidx
    have hl1 : c₁.inputPos.val - 1 < x₁.length := by omega
    have hl2' : c₁.inputPos.val - 1 < x₂.length := by omega
    rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2'] at hget
    have hbit : x₁[c₁.inputPos.val - 1] = x₂[c₂.inputPos.val - 1] := by
      have := Option.some.inj hget
      simpa [hposEq] using this
    exact congrArg some hbit

private theorem val_congr {m₁ m₂ : ℕ} (p₁ : Fin (m₁ + 2)) (p₂ : Fin (m₂ + 2)) (dir : SignType)
    (hm : m₁ = m₂) (hp : p₁.val = p₂.val) :
    (moveInputPos p₁ dir).val = (moveInputPos p₂ dir).val := by
  subst hm
  obtain rfl : p₁ = p₂ := Fin.ext hp
  rfl

private theorem next_sameExceptLast {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State)
    {n : ℕ} {x₁ x₂ : List Bool} (hx₁ : x₁.length = n) (hx₂ : x₂.length = n)
    (hagree : ∀ i : ℕ, i + 1 < n → x₁[i]? = x₂[i]?)
    {c₁ : Cfg k Bool State x₁} {c₂ : Cfg k Bool State x₂}
    (hsame : SameExceptLast c₁ c₂) (hpos : c₁.inputPos.val + 1 ≤ n) (b : Bool) :
    SameExceptLast (atm.next b c₁) (atm.next b c₂) ∧
      (atm.next b c₁).inputPos.val ≤ c₁.inputPos.val + 1 := by
  let tm := (atm.toPTM.withCoin b).toTM
  have hst : c₁.state = c₂.state := hsame.1
  cases hstate : c₁.state with
  | none =>
    have hstate2 : c₂.state = none := hst.symm.trans hstate
    have hn1 : atm.next b c₁ = c₁ := by
      refine (MultiTapeTM.step_iff (tm := tm)).mp ?_
      simp [MultiTapeNTM.Step, hstate]
    have hn2 : atm.next b c₂ = c₂ := by
      refine (MultiTapeTM.step_iff (tm := tm)).mp ?_
      simp [MultiTapeNTM.Step, hstate2]
    rw [hn1, hn2]
    exact ⟨hsame, Nat.le_succ _⟩
  | some q =>
    have hstate2 : c₂.state = some q := hst.symm.trans hstate
    have hn1 : atm.next b c₁ = (tm.tr q c₁.inputSymbol c₁.workTapeSymbols).apply c₁ :=
      MultiTapeTM.step_of_state (tm := tm) hstate
    have hn2 : atm.next b c₂ = (tm.tr q c₂.inputSymbol c₂.workTapeSymbols).apply c₂ :=
      MultiTapeTM.step_of_state (tm := tm) hstate2
    have hin : c₁.inputSymbol = c₂.inputSymbol :=
      inputSymbol_eq_of_sameExceptLast hx₁ hx₂ hagree hsame hpos
    have hw : c₁.workTapeSymbols = c₂.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, hsame.2.2.1, hsame.2.2.2.1]
    rw [hn1, hn2, hin, hw]
    let act := tm.tr q c₂.inputSymbol c₂.workTapeSymbols
    have hpos_val : (act.apply c₁).inputPos.val = (act.apply c₂).inputPos.val := by
      change (moveInputPos c₁.inputPos act.inputTape).val =
        (moveInputPos c₂.inputPos act.inputTape).val
      exact val_congr c₁.inputPos c₂.inputPos act.inputTape (hx₁.trans hx₂.symm) hsame.2.1
    refine ⟨⟨rfl, hpos_val, ?_, ?_, ?_⟩, ?_⟩
    · funext i
      dsimp only [Action.apply]
      rw [hsame.2.2.1, hsame.2.2.2.1]
    · funext i
      dsimp only [Action.apply]
      rw [hsame.2.2.2.1]
    · dsimp only [Action.apply]
      rw [hsame.2.2.2.2]
    · simpa [Action.apply] using Turing.val_moveInputPos_le c₁.inputPos act.inputTape

private theorem acceptsWithin_congr_exceptLast {k : ℕ} {State : Type}
    (atm : MultiTapeATM k Bool State) {n : ℕ} {x₁ x₂ : List Bool}
    (hx₁ : x₁.length = n) (hx₂ : x₂.length = n)
    (hagree : ∀ i : ℕ, i + 1 < n → x₁[i]? = x₂[i]?) :
    ∀ (d : ℕ) (c₁ : Cfg k Bool State x₁) (c₂ : Cfg k Bool State x₂),
      SameExceptLast c₁ c₂ → c₁.inputPos.val + d ≤ n →
        (atm.AcceptsWithin d c₁ ↔ atm.AcceptsWithin d c₂) := by
  intro d
  induction d with
  | zero =>
    intro c₁ c₂ hsame _
    rw [MultiTapeATM.AcceptsWithin.eq_1, MultiTapeATM.AcceptsWithin.eq_1]
    rw [hsame.1, hsame.2.2.2.2]
  | succ d ih =>
    intro c₁ c₂ hsame hbound
    rw [MultiTapeATM.AcceptsWithin.eq_2, MultiTapeATM.AcceptsWithin.eq_2]
    have hst : c₁.state = c₂.state := hsame.1
    cases hstate : c₁.state with
    | none =>
      have hstate2 : c₂.state = none := hst.symm.trans hstate
      simp [hstate2, hsame.2.2.2.2]
    | some q =>
      have hstate2 : c₂.state = some q := hst.symm.trans hstate
      have hpos : c₁.inputPos.val + 1 ≤ n := by omega
      have ih_b (b : Bool) : atm.AcceptsWithin d (atm.next b c₁) ↔
          atm.AcceptsWithin d (atm.next b c₂) := by
        obtain ⟨hsame', hle⟩ := next_sameExceptLast atm hx₁ hx₂ hagree hsame hpos b
        exact ih (atm.next b c₁) (atm.next b c₂) hsame' (by omega)
      simp only [hstate2]
      by_cases hu : atm.universal q = true
      · simp only [hu]
        exact forall_congr' ih_b
      · simp only [hu]
        exact exists_congr ih_b

/-- No sequential `MultiTapeATM` can decide `lastBitLanguage` if for some length `n ≥ 2` it halts
within `n - 1` steps on both `[false, ..., false, true]` and `[false, ..., false, false]`. -/
theorem lastBitLanguage_not_decidesInTime_lt {k : ℕ} {State : Type}
    (atm : MultiTapeATM k Bool State) {t : List Bool → ℕ}
    (hdec : atm.DecidesInTime encBits lastBitLanguage t)
    {n : ℕ} (hn : 2 ≤ n)
    (ht1 : t (List.replicate (n - 1) false ++ [true]) ≤ n - 1)
    (ht2 : t (List.replicate (n - 1) false ++ [false]) ≤ n - 1) : False := by
  let x₁ : List Bool := List.replicate (n - 1) false ++ [true]
  let x₂ : List Bool := List.replicate (n - 1) false ++ [false]
  have hx1_len : x₁.length = n := by simp [x₁]; omega
  have hx2_len : x₂.length = n := by simp [x₂]; omega
  have hagree : ∀ i : ℕ, i + 1 < n → x₁[i]? = x₂[i]? := by
    intro i hi
    have hi' : i < n - 1 := by omega
    have hr1 : i < (List.replicate (n - 1) false).length := by simp [hi']
    simp [x₁, x₂, List.getElem?_append_left hr1]
  have hmem1 : x₁ ∈ lastBitLanguage := by
    simp [lastBitLanguage, x₁]
  have hnot2 : x₂ ∉ lastBitLanguage := by
    simp [lastBitLanguage, x₂]
  obtain ⟨hrun1, hiff1⟩ := hdec x₁
  obtain ⟨hrun2, hiff2⟩ := hdec x₂
  have hacc1 : atm.Accepts x₁ := hiff1.mp hmem1
  have hrun1' : atm.toPTM.toNTM.RunsInTime x₁ (n - 1) :=
    fun p hp => hrun1 p (ht1.trans hp)
  have hrun2' : atm.toPTM.toNTM.RunsInTime x₂ (n - 1) :=
    fun p hp => hrun2 p (ht2.trans hp)
  have hw1 : atm.AcceptsWithin (n - 1) (atm.toPTM.toNTM.initCfg x₁) :=
    (Turing.MultiTapeATM.accepts_iff_acceptsWithin hrun1').mp hacc1
  have hsame : SameExceptLast (atm.toPTM.toNTM.initCfg x₁) (atm.toPTM.toNTM.initCfg x₂) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hpos : (atm.toPTM.toNTM.initCfg x₁).inputPos.val + (n - 1) ≤ n := by
    change 1 + (n - 1) ≤ n
    omega
  have hw2 : atm.AcceptsWithin (n - 1) (atm.toPTM.toNTM.initCfg x₂) :=
    (acceptsWithin_congr_exceptLast atm hx1_len hx2_len hagree (n - 1)
      (atm.toPTM.toNTM.initCfg x₁) (atm.toPTM.toNTM.initCfg x₂) hsame hpos).mp hw1
  have hacc2 : atm.Accepts x₂ :=
    (Turing.MultiTapeATM.accepts_iff_acceptsWithin hrun2').mpr hw2
  exact hnot2 (hiff2.mpr hacc2)

private theorem two_mul_le_two_pow (k : ℕ) (hk : 4 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk4 : 4 ≤ k
    · have ih' := ih hk4
      have hpow : 2 ≤ 2 ^ k := by
        calc 2 ≤ 2 * k := by omega
          _ ≤ 2 ^ k := ih'
      rw [Nat.pow_succ]
      omega
    · have hk3 : k = 3 := by omega
      subst hk3
      norm_num

theorem div_sqrt_log_eventually_lt (c₁ c₂ : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧ c₁ * (n / Nat.sqrt (Nat.log 2 n)) + c₂ ≤ n - 1 := by
  let M : ℕ := 2 * c₁ + c₂ + 4
  let k : ℕ := M * M
  have hM4 : 4 ≤ M := by dsimp [M]; omega
  have hk_pos : 1 ≤ k := by dsimp [k]; exact Nat.mul_pos (by omega) (by omega)
  have hsqrt : Nat.sqrt k = M := Nat.sqrt_eq M
  refine ⟨2 ^ k, Nat.le_self_pow (by omega) 2, ?_⟩
  have hlog : Nat.log 2 (2 ^ k) = k := Nat.log_pow (by omega) k
  rw [hlog, hsqrt]
  have hmul : 2 * (c₁ * (2 ^ k / M)) ≤ 2 ^ k := by
    calc 2 * (c₁ * (2 ^ k / M)) = (2 * c₁) * (2 ^ k / M) := by ring
      _ ≤ M * (2 ^ k / M) := Nat.mul_le_mul_right _ (by dsimp [M]; omega)
      _ ≤ 2 ^ k := Nat.mul_div_le _ _
  have hM_le_k : 4 * M ≤ k := by
    dsimp [k]
    exact Nat.mul_le_mul_right M hM4
  have hk4 : 4 ≤ k := by omega
  have h2k : 2 * k ≤ 2 ^ k := two_mul_le_two_pow k hk4
  have hc2 : 2 * (c₂ + 2) ≤ 2 ^ k := by
    have : 2 * (c₂ + 2) ≤ 2 * M := by dsimp [M]; omega
    omega
  omega

/-- **`lastBitLanguage` is NOT in sequential `ATIME(n / √(log n))`**, demonstrating that
random-access input access is necessary for any `o(n)` time bound when `T = n`. -/
theorem lastBitLanguage_notMem_ATIME_sqrtLog :
    lastBitLanguage ∉ ATIME encBits (fun n => n / Nat.sqrt (Nat.log 2 n)) := by
  rintro ⟨c₁, c₂, k, State, hfin, atm, hdec⟩
  obtain ⟨n, hn2, hlt⟩ := div_sqrt_log_eventually_lt c₁ c₂
  let x₁ : List Bool := List.replicate (n - 1) false ++ [true]
  let x₂ : List Bool := List.replicate (n - 1) false ++ [false]
  have hx1_len : (encBits x₁).length = n := by change x₁.length = n; simp [x₁]; omega
  have hx2_len : (encBits x₂).length = n := by change x₂.length = n; simp [x₂]; omega
  have ht1 : c₁ * ((encBits x₁).length / Nat.sqrt (Nat.log 2 (encBits x₁).length)) + c₂ ≤
      n - 1 := by
    rw [hx1_len]
    exact hlt
  have ht2 : c₁ * ((encBits x₂).length / Nat.sqrt (Nat.log 2 (encBits x₂).length)) + c₂ ≤
      n - 1 := by
    rw [hx2_len]
    exact hlt
  exact lastBitLanguage_not_decidesInTime_lt atm hdec hn2 ht1 ht2

/-- Sequential `Σ₂TIME(n)` is not contained in sequential `ATIME(n / √(log n))`. -/
theorem not_SigmaTwoTIME_subset_ATIME_seq :
    ¬ (SigmaTwoTIME encBits id ⊆ ATIME encBits (fun n => n / Nat.sqrt (Nat.log 2 n))) :=
  fun hsub => lastBitLanguage_notMem_ATIME_sqrtLog (hsub lastBitLanguage_mem_SigmaTwoTIME)

end SequentialSeparation

/-! ### Part II: Clocked Index-Tape Alternating Machines (`RAATM`) -/

section RandomAccessMachine

/-- Decode an LSB-first binary natural number stored on tape cells `[pos, pos + fuel)`,
stopping at the first blank (`none`). -/
def decodeIndexAux (tape : ℤ → Option Bool) (pos fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match tape (pos : ℤ) with
    | none => 0
    | some b => (if b then 1 else 0) + 2 * decodeIndexAux tape (pos + 1) fuel'

theorem decodeIndexAux_eq_zero_of_blank (tape : ℤ → Option Bool) (pos : ℕ)
    (hblank : ∀ j : ℕ, pos ≤ j → tape (j : ℤ) = none) :
    ∀ fuel : ℕ, decodeIndexAux tape pos fuel = 0 := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel' => simp [decodeIndexAux, hblank pos le_rfl]

theorem decodeIndexAux_stable (tape : ℤ → Option Bool) (hi : ℕ)
    (hblank : ∀ j : ℕ, hi ≤ j → tape (j : ℤ) = none) :
    ∀ (fuel pos : ℕ), hi ≤ pos + fuel →
      decodeIndexAux tape pos fuel = decodeIndexAux tape pos (hi - pos) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos _hle
    have hp : hi ≤ pos := by omega
    rw [Nat.sub_eq_zero_of_le hp]
  | succ fuel' ih =>
    intro pos hle
    by_cases hp : hi ≤ pos
    · rw [Nat.sub_eq_zero_of_le hp, decodeIndexAux]
      exact decodeIndexAux_eq_zero_of_blank tape pos (fun j hj => hblank j (hp.trans hj))
        (fuel' + 1)
    · have hsub : hi - pos = (hi - (pos + 1)) + 1 := by omega
      rw [hsub]
      dsimp only [decodeIndexAux]
      cases hcell : tape (pos : ℤ) with
      | none => rfl
      | some b =>
        rw [ih (pos + 1) (by omega)]

theorem decodeIndexAux_pow (tape : ℤ → Option Bool) (p : ℕ)
    (hzeros : ∀ j : ℕ, j < p → tape (j : ℤ) = some false)
    (hone : tape (p : ℤ) = some true) :
    decodeIndexAux tape 0 (p + 1) = 2 ^ p := by
  have aux : ∀ (d pos : ℕ), pos ≤ p → p - pos = d →
      decodeIndexAux tape pos (p + 1 - pos) = 2 ^ d := by
    intro d
    induction d with
    | zero =>
      intro pos hpos hdiff
      have hpeq : pos = p := by omega
      subst hpeq
      rw [show pos + 1 - pos = 1 from by omega]
      dsimp only [decodeIndexAux]
      rw [hone]
      rfl
    | succ d ih =>
      intro pos hpos hdiff
      have hlt : pos < p := by omega
      have hsub : p + 1 - pos = (p + 1 - (pos + 1)) + 1 := by omega
      rw [hsub]
      dsimp only [decodeIndexAux]
      rw [hzeros pos hlt, ih (pos + 1) (by omega) (by omega), Nat.pow_succ, Nat.mul_comm]
      simp
  exact aux p 0 (Nat.zero_le p) (Nat.sub_zero p)

private theorem decodeIndexAux_eq_of_agree (tape tape' : ℤ → Option Bool) (q fq : ℕ)
    (h : ∀ i : ℕ, q ≤ i → tape' (i : ℤ) = tape (i : ℤ)) :
    decodeIndexAux tape' q fq = decodeIndexAux tape q fq := by
  induction fq generalizing q with
  | zero => rfl
  | succ fq' ih =>
    dsimp only [decodeIndexAux]
    rw [h q le_rfl]
    cases tape (q : ℤ) with
    | none => rfl
    | some b =>
      dsimp only
      rw [ih (q + 1) (fun i hi => h i (by omega))]

theorem decodeIndexAux_flipBit (tape tape' : ℤ → Option Bool) (j p : ℕ) (hj : j < p)
    (hbelow : ∀ i : ℕ, i ≤ j → tape (i : ℤ) = some false)
    (hagree_lt : ∀ i : ℕ, i ≠ j → tape' (i : ℤ) = tape (i : ℤ))
    (hflip : tape' (j : ℤ) = some true) :
    decodeIndexAux tape' 0 (p + 1) = decodeIndexAux tape 0 (p + 1) + 2 ^ j := by
  have aux : ∀ (fuel pos : ℕ), pos ≤ j → j + 1 < pos + fuel →
      decodeIndexAux tape' pos fuel = decodeIndexAux tape pos fuel + 2 ^ (j - pos) := by
    intro fuel
    induction fuel with
    | zero => intro _ _ hlt; omega
    | succ fuel' ih =>
      intro pos hpos hlt
      by_cases heq : pos = j
      · have hjpos : j - pos = 0 := by omega
        rw [hjpos, Nat.pow_zero]
        dsimp only [decodeIndexAux]
        have hfl : tape' (pos : ℤ) = some true := by simpa [heq] using hflip
        have hbl : tape (pos : ℤ) = some false := hbelow pos (by omega)
        rw [hfl, hbl]
        dsimp only
        have htail : decodeIndexAux tape' (pos + 1) fuel' = decodeIndexAux tape (pos + 1) fuel' :=
          decodeIndexAux_eq_of_agree tape tape' (pos + 1) fuel'
            (fun i hi => hagree_lt i (by omega))
        rw [htail]
        simp
        omega
      · have hpos_lt : pos < j := by omega
        dsimp only [decodeIndexAux]
        rw [hagree_lt pos (by omega), hbelow pos hpos_lt.le]
        dsimp only
        rw [ih (pos + 1) (by omega) (by omega)]
        have hpow : j - pos = (j - (pos + 1)) + 1 := by omega
        rw [hpow, Nat.pow_succ]
        simp
        ring
  simpa using aux (p + 1) 0 (Nat.zero_le j) (by omega)

/-- Configuration of a clocked multitape alternating machine with an explicit sequential binary
index tape (`idxTape`) and `k` work tapes. -/
structure RACfg (k : ℕ) (State : Type) where
  /-- Current control state, or `none` if halted. -/
  state : Option State
  /-- Latched Boolean acceptance bit recorded upon halting. -/
  accept : Bool
  /-- Bidirectional sequential binary index tape holding query address bits. -/
  idxTape : ℤ → Option Bool
  /-- Head position on the binary index tape. -/
  idxPos : ℤ
  /-- Tracked upper bound on written non-negative index-tape cells for decoding. -/
  idxHi : ℕ
  /-- Bidirectional work tapes indexed by `Fin k`. -/
  workTape : Fin k → ℤ → Option Bool
  /-- Head positions on the `k` work tapes. -/
  workPos : Fin k → ℤ

/-- Initial configuration starting in `q₀` with all tapes blank and heads at `0`. -/
@[expose] def RACfg.init {k : ℕ} {State : Type} (q₀ : State) : RACfg k State where
  state := some q₀
  accept := false
  idxTape _ := none
  idxPos := 0
  idxHi := 0
  workTape _ _ := none
  workPos _ := 0

/-- Initial configuration with pre-loaded auxiliary binary string on worktape `0`. -/
@[expose] def RACfg.initWithAux {k : ℕ} {State : Type} (q₀ : State) (_hk : 0 < k)
    (aux : List Bool) : RACfg k State where
  state := some q₀
  accept := false
  idxTape _ := none
  idxPos := 0
  idxHi := 0
  workTape i z :=
    if i.val = 0 then
      if hz0 : 0 ≤ z then if hzl : z.toNat < aux.length then some aux[z.toNat] else none
      else none
    else none
  workPos _ := 0

/-- Decoded non-negative input query address stored on the index tape. -/
@[expose] def RACfg.addr {k : ℕ} {State : Type} (c : RACfg k State) : ℕ :=
  decodeIndexAux c.idxTape 0 c.idxHi

/-- Single-step action of an `RAATM` machine. -/
structure RAAction (k : ℕ) (State : Type) where
  /-- Next control state, or `none` to halt. -/
  nextState : Option State
  /-- Output acceptance bit latched when `nextState = none`. -/
  outBit : Bool
  /-- Optional cell update on `idxTape` (`none` leaves the cell unchanged). -/
  idxWrite : Option (Option Bool)
  /-- Head movement on `idxTape` (`-1`, `0`, or `+1`). -/
  idxMove : SignType
  /-- Optional cell updates on each work tape `Fin k`. -/
  workWrite : Fin k → Option (Option Bool)
  /-- Head movements on each work tape `Fin k`. -/
  workMove : Fin k → SignType

/-- Clocked multitape alternating Turing machine with sequential binary index tape and
unit-cost random-access query `input[c.addr]?`. -/
structure RAATM (k : ℕ) (State : Type) where
  /-- Initial control state. -/
  q₀ : State
  /-- Quantifier label (`true` = universal `∀`, `false` = existential `∃`). -/
  univ : State → Bool
  /-- Transition function taking state, index symbol, work symbols, queried input symbol, and
  branching coin `b`. -/
  tr : State → Option Bool → (Fin k → Option Bool) → Option Bool → Bool → RAAction k State

/-- Single transition of `M` on input `input` along branching coin `b : Bool`. -/
@[expose] def RAATM.step {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool)
    (b : Bool) (c : RACfg k State) : RACfg k State :=
  match c.state with
  | none => c
  | some q =>
    let act := M.tr q (c.idxTape c.idxPos) (fun i => c.workTape i (c.workPos i))
      input[c.addr]? b
    { state := act.nextState
      accept := if act.nextState.isNone then act.outBit else c.accept
      idxTape := match act.idxWrite with
        | none => c.idxTape
        | some s => Function.update c.idxTape c.idxPos s
      idxPos := c.idxPos + (act.idxMove : ℤ)
      idxHi := match act.idxWrite with
        | some (some _) => max c.idxHi (Int.toNat (c.idxPos + 1))
        | _ => c.idxHi
      workTape := fun i => match act.workWrite i with
        | none => c.workTape i
        | some s => Function.update (c.workTape i) (c.workPos i) s
      workPos := fun i => c.workPos i + (act.workMove i : ℤ) }

/-- Deterministically execute a list of branching coins from `c`. -/
@[expose] def RAATM.runCoins {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool) :
    RACfg k State → List Bool → RACfg k State
  | c, [] => c
  | c, b :: bs => M.runCoins input (M.step input b c) bs

theorem RAATM.runCoins_append {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool)
    (c : RACfg k State) (xs ys : List Bool) :
    M.runCoins input c (xs ++ ys) = M.runCoins input (M.runCoins input c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons a xs ih => exact ih (M.step input a c)

/-- Executing any further coins from a halted configuration leaves the configuration unchanged. -/
theorem RAATM.runCoins_halt_eq {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool)
    {c : RACfg k State} (hc : c.state = none) (bs : List Bool) :
    M.runCoins input c bs = c := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [RAATM.runCoins, show M.step input b c = c from by simp [RAATM.step, hc]]
    exact ih

/-- Alternating evaluation predicate within budget `n` steps from configuration `c`. -/
@[expose] def RAATM.AcceptsWithin {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool) :
    ℕ → RACfg k State → Prop
  | 0, c => c.state = none ∧ c.accept = true
  | n + 1, c =>
    match c.state with
    | none => c.accept = true
    | some q =>
      if M.univ q = true then ∀ b : Bool, M.AcceptsWithin input n (M.step input b c)
      else ∃ b : Bool, M.AcceptsWithin input n (M.step input b c)

theorem RAATM.AcceptsWithin.mono {k : ℕ} {State : Type} {M : RAATM k State}
    {input : List Bool} {n m : ℕ} {c : RACfg k State}
    (h : M.AcceptsWithin input n c) (hnm : n ≤ m) : M.AcceptsWithin input m c := by
  induction m generalizing n c with
  | zero =>
    obtain rfl : n = 0 := by omega
    exact h
  | succ m ih =>
    cases n with
    | zero =>
      rcases h with ⟨hst, hacc⟩
      simp [RAATM.AcceptsWithin, hst, hacc]
    | succ n =>
      unfold RAATM.AcceptsWithin at h ⊢
      cases hst : c.state with
      | none => simpa [hst] using h
      | some q =>
        simp only [hst] at h ⊢
        by_cases hu : M.univ q = true
        · simp only [hu, ↓reduceIte] at h ⊢
          exact fun b => ih (h b) (by omega)
        · simp only [hu] at h ⊢
          obtain ⟨b, hb⟩ := h
          exact ⟨b, ih hb (by omega)⟩

/-- Acceptance of `M` on `input`. -/
@[expose] def RAATM.Accepts {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool) : Prop :=
  ∃ t, M.AcceptsWithin input t (RACfg.init M.q₀)

/-- Clocked halting predicate: every `t`-step branch halts. -/
@[expose] def RAATM.ClockedHalts {k : ℕ} {State : Type} (M : RAATM k State) (input : List Bool)
    (t : ℕ) : Prop :=
  ∀ bs : List Bool, bs.length = t → (M.runCoins input (RACfg.init M.q₀) bs).state = none

/-- Machine `M` is deterministic if every transition ignores the branching coin `b` and has
existential labels. -/
@[expose] def RAATM.IsDeterministic {k : ℕ} {State : Type} (M : RAATM k State) : Prop :=
  (∀ q, M.univ q = false) ∧
    ∀ q i w inSym b₁ b₂, M.tr q i w inSym b₁ = M.tr q i w inSym b₂

/-- Machine `M` has bounded alternation depth `m` (with `startUniv = false` for `Σ_m` and
`startUniv = true` for `Π_m`) when states can be stratified into monotonic phases `0 .. m - 1`
matching `M.univ` (note `m = 0` yields an empty `Fin 0` phase type). -/
@[expose] def RAATM.HasPhaseBound {k : ℕ} {State : Type} (m : ℕ) (startUniv : Bool)
    (M : RAATM k State) : Prop :=
  ∃ phase : State → Fin m,
    (∀ q, M.univ q = (startUniv ^^ ((phase q).val % 2 == 1))) ∧
    ∀ q i w inSym b q', (M.tr q i w inSym b).nextState = some q' → phase q ≤ phase q'

/-- `M` decides language `A` within clocked time `t : List Bool → ℕ`. -/
@[expose] def RAATM.DecidesInTime {k : ℕ} {State : Type} (M : RAATM k State)
    (A : Set (List Bool)) (t : List Bool → ℕ) : Prop :=
  ∀ x, M.ClockedHalts x (t x) ∧ (x ∈ A ↔ M.Accepts x)

/-- Random-access deterministic time `DTIME_Idx(t)`. -/
@[expose] def RADTIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {A | ∃ c₁ c₂ k State, Finite State ∧ ∃ M : RAATM k State,
    M.IsDeterministic ∧ M.DecidesInTime A (fun x => c₁ * t x.length + c₂)}

/-- Random-access nondeterministic time `NTIME_Idx(t)`. -/
@[expose] def RANTIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {A | ∃ c₁ c₂ k State, Finite State ∧ ∃ M : RAATM k State,
    RAATM.HasPhaseBound 1 false M ∧ M.DecidesInTime A (fun x => c₁ * t x.length + c₂)}

/-- Random-access co-nondeterministic time `coNTIME_Idx(t)`. -/
@[expose] def RACoNTIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {A | ∃ c₁ c₂ k State, Finite State ∧ ∃ M : RAATM k State,
    RAATM.HasPhaseBound 1 true M ∧ M.DecidesInTime A (fun x => c₁ * t x.length + c₂)}

/-- Bounded-alternation random-access `Σ_m TIME(t)` (`RASigmaTime 0 t = ∅`). -/
@[expose] def RASigmaTime (m : ℕ) (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {A | ∃ c₁ c₂ k State, Finite State ∧ ∃ M : RAATM k State,
    RAATM.HasPhaseBound m false M ∧ M.DecidesInTime A (fun x => c₁ * t x.length + c₂)}

/-- Bounded-alternation random-access `Π_m TIME(t)` (`RAPiTime 0 t = ∅`). -/
@[expose] def RAPiTime (m : ℕ) (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {A | ∃ c₁ c₂ k State, Finite State ∧ ∃ M : RAATM k State,
    RAATM.HasPhaseBound m true M ∧ M.DecidesInTime A (fun x => c₁ * t x.length + c₂)}

/-- Random-access `Σ₂TIME(t)`. -/
abbrev RASigmaTwoTime (t : ℕ → ℕ) : Set (Set (List Bool)) := RASigmaTime 2 t

/-- Random-access `Σ₃TIME(t)`. -/
abbrev RASigmaThreeTime (t : ℕ → ℕ) : Set (Set (List Bool)) := RASigmaTime 3 t

/-- Unrestricted-alternation random-access `ATIME(t)`. -/
def RAATIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {A | ∃ c₁ c₂ k State, Finite State ∧ ∃ M : RAATM k State,
    M.DecidesInTime A (fun x => c₁ * t x.length + c₂)}

theorem RADTIME_subset_RANTIME {t : ℕ → ℕ} : RADTIME t ⊆ RANTIME t := by
  rintro A ⟨c₁, c₂, k, State, hfin, M, hdet, hdec⟩
  refine ⟨c₁, c₂, k, State, hfin, M, ?_, hdec⟩
  exact ⟨fun _ => 0, fun q => by simp [hdet.1 q], fun _ _ _ _ _ _ _ => le_rfl⟩

theorem RASigmaTime_mono_depth {m₁ m₂ : ℕ} (_hm : m₁ ≤ m₂) {t : ℕ → ℕ} :
    RASigmaTime m₁ t ⊆ RASigmaTime m₂ t := by
  rintro A ⟨c₁, c₂, k, State, hfin, M, ⟨phase, huniv, hmono⟩, hdec⟩
  refine ⟨c₁, c₂, k, State, hfin, M, ⟨fun q => ⟨(phase q).val, lt_of_lt_of_le (phase q).2 _hm⟩,
    fun q => huniv q, fun q i w inb b q' h => hmono q i w inb b q' h⟩, hdec⟩

theorem RANTIME_subset_RASigmaTwoTime {t : ℕ → ℕ} : RANTIME t ⊆ RASigmaTwoTime t :=
  RASigmaTime_mono_depth (by omega)

theorem RASigmaTwoTime_subset_RASigmaThreeTime {t : ℕ → ℕ} :
    RASigmaTwoTime t ⊆ RASigmaThreeTime t :=
  RASigmaTime_mono_depth (by omega)

theorem RASigmaThreeTime_subset_RAATIME {t : ℕ → ℕ} :
    RASigmaThreeTime t ⊆ RAATIME t := by
  rintro A ⟨c₁, c₂, k, State, hfin, M, _, hdec⟩
  exact ⟨c₁, c₂, k, State, hfin, M, hdec⟩

/-! #### Constructive `O(log n)` input-length discovery and `lastBitLanguage ∈ RADTIME(log n)` -/

private inductive LastBitState where
  | start
  | probe
  | setProbeBit
  | binSet
  | binTest
  | readLast
  deriving DecidableEq

private instance : Finite LastBitState :=
  Finite.of_equiv (Fin 6)
    { toFun := fun i => match i with
        | 0 => .start
        | 1 => .probe
        | 2 => .setProbeBit
        | 3 => .binSet
        | 4 => .binTest
        | 5 => .readLast
      invFun := fun s => match s with
        | .start => 0
        | .probe => 1
        | .setProbeBit => 2
        | .binSet => 3
        | .binTest => 4
        | .readLast => 5
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun s => by cases s <;> rfl }

/-- Deterministic `RAATM` deciding `lastBitLanguage` in `O(log(n + 2))` steps via exponential
probing followed by in-place binary search on the index tape. -/
private def lastBitRAMachine : RAATM 1 LastBitState where
  q₀ := .start
  univ _ := false
  tr q _ wSym inSym _ :=
    match q with
    | .start =>
      match inSym with
      | none => ⟨none, false, none, 0, fun _ => none, fun _ => 0⟩
      | some _ =>
        ⟨some .probe, false, some (some true), 0, fun _ => some (some true), fun _ => 0⟩
    | .probe =>
      match inSym with
      | some _ =>
        ⟨some .setProbeBit, false, some (some false), 1, fun _ => none, fun _ => 1⟩
      | none =>
        if wSym 0 = some true then
          ⟨some .readLast, false, some (some false), 0, fun _ => none, fun _ => 0⟩
        else
          ⟨some .binSet, false, some none, -1, fun _ => none, fun _ => -1⟩
    | .setProbeBit =>
      ⟨some .probe, false, some (some true), 0, fun _ => none, fun _ => 0⟩
    | .binSet =>
      ⟨some .binTest, false, some (some true), 0, fun _ => none, fun _ => 0⟩
    | .binTest =>
      match inSym with
      | some b =>
        if wSym 0 = some true then
          ⟨none, b, none, 0, fun _ => none, fun _ => 0⟩
        else
          ⟨some .binSet, false, none, -1, fun _ => none, fun _ => -1⟩
      | none =>
        if wSym 0 = some true then
          ⟨some .readLast, false, some (some false), 0, fun _ => none, fun _ => 0⟩
        else
          ⟨some .binSet, false, some (some false), -1, fun _ => none, fun _ => -1⟩
    | .readLast =>
      ⟨none, inSym.getD false, none, 0, fun _ => none, fun _ => 0⟩

private theorem lastBitRAMachine_det : lastBitRAMachine.IsDeterministic :=
  ⟨fun _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- Execution invariant for the `O(log n)` binary-search phase on `lastBitRAMachine`. -/
private def BinInv (input : List Bool) (p j : ℕ) (c : RACfg 1 LastBitState) : Prop :=
  c.state = some .binSet ∧
    c.idxPos = (j : ℤ) ∧
    c.workPos 0 = (j : ℤ) ∧
    c.idxHi = p + 1 ∧
    (∀ z : ℤ, c.workTape 0 z = if z = 0 then some true else none) ∧
    (∀ i : ℕ, i ≤ j → c.idxTape (i : ℤ) = some false) ∧
    (∀ i : ℕ, j < i → i < p → ∃ b : Bool, c.idxTape (i : ℤ) = some b) ∧
    (∀ i : ℕ, p ≤ i → c.idxTape (i : ℤ) = none) ∧
    c.addr < input.length ∧
    input.length ≤ c.addr + 2 ^ (j + 1)

private theorem runCoins_det_eq {k : ℕ} {State : Type} (M : RAATM k State)
    (hdet : M.IsDeterministic) (input : List Bool) (bs : List Bool) (c : RACfg k State) :
    M.runCoins input c bs = M.runCoins input c (List.replicate bs.length false) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    have hstep : M.step input b c = M.step input false c := by
      unfold RAATM.step
      cases c.state with
      | none => rfl
      | some q => simp [hdet.2 q _ _ _ b false]
    rw [RAATM.runCoins, List.length_cons, List.replicate_succ, RAATM.runCoins, hstep]
    exact ih (M.step input false c)

private theorem acceptsWithin_det_iff {k : ℕ} {State : Type} (M : RAATM k State)
    (hdet : M.IsDeterministic) (input : List Bool) (t : ℕ) (c : RACfg k State) :
    M.AcceptsWithin input t c ↔
      let cf := M.runCoins input c (List.replicate t false)
      cf.state = none ∧ cf.accept = true := by
  induction t generalizing c with
  | zero => simp [RAATM.AcceptsWithin, RAATM.runCoins]
  | succ t ih =>
    unfold RAATM.AcceptsWithin
    cases hst : c.state with
    | none =>
      have hhalt : M.runCoins input c (List.replicate (t + 1) false) = c := by
        clear ih
        induction t with
        | zero => simp [RAATM.runCoins, RAATM.step, hst]
        | succ t iht =>
          rw [List.replicate_succ, RAATM.runCoins]
          have hs : M.step input false c = c := by simp [RAATM.step, hst]
          rw [hs]
          exact iht
      simp [hhalt, hst]
    | some q =>
      simp only [hdet.1 q, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨b, hb⟩
        have hstep : M.step input b c = M.step input false c := by
          unfold RAATM.step
          simp only [hst, hdet.2 q _ _ _ b false]
        rw [hstep] at hb
        exact (ih (M.step input false c)).mp
          (by simpa [List.replicate_succ, RAATM.runCoins] using hb)
      · intro h
        exact ⟨false, (ih (M.step input false c)).mpr
          (by simpa [List.replicate_succ, RAATM.runCoins] using h)⟩

private theorem lastBitRAMachine_bin_run (input : List Bool) (p : ℕ) :
    ∀ j : ℕ, ∀ c : RACfg 1 LastBitState, j < p → BinInv input p j c →
      ∃ steps ≤ 2 * j + 3,
        let cf := lastBitRAMachine.runCoins input c (List.replicate steps false)
        cf.state = none ∧ cf.accept = (input.getLast? == some true) := by
  intro j
  induction j with
  | zero =>
    intro c _ hinv
    rcases hinv with ⟨hst, hip, hwp, hhi, hwt, hlow, _, hhigh, hlt, hle⟩
    have hhiVal_eq : c.addr < input.length ∧ input.length ≤ c.addr + 2 := by
      simpa using And.intro hlt hle
    let c1 := lastBitRAMachine.step input false c
    have hc1_st : c1.state = some .binTest := by simp [c1, RAATM.step, lastBitRAMachine, hst]
    have hc1_addr : c1.addr = c.addr + 1 := by
      dsimp only [RACfg.addr, c1, RAATM.step, lastBitRAMachine]
      rw [hst]
      dsimp only [RACfg.idxHi]
      have hmax : max (p + 1) (Int.toNat (c.idxPos + 1)) = p + 1 := by omega
      rw [hhi, hmax, hip]
      change decodeIndexAux (Function.update c.idxTape (0 : ℤ) (some true)) 0 (p + 1) =
        decodeIndexAux c.idxTape 0 (p + 1) + 2 ^ 0
      refine decodeIndexAux_flipBit c.idxTape (Function.update c.idxTape (0 : ℤ) (some true))
        0 p ‹0 < p› hlow (fun i hi => Function.update_of_ne (by omega) _ _)
        (Function.update_self _ _ _)
    have hc1_wt : c1.workTape 0 (c1.workPos 0) = some true := by
      simp [c1, RAATM.step, lastBitRAMachine, hst, hwp, hwt]
    have hc1_wt_fn : (fun i : Fin 1 => c1.workTape i (c1.workPos i)) = fun _ => some true := by
      funext i; rw [Subsingleton.elim i 0]; exact hc1_wt
    cases hin1 : input[c1.addr]? with
    | some b =>
      have hlt1 : c1.addr < input.length := (List.getElem?_eq_some_iff.mp hin1).1
      have hlast : c1.addr = input.length - 1 := by omega
      have hgetLast : input.getLast? = some b := by
        cases input with
        | nil => simp at hlt1
        | cons a as =>
          rw [List.getLast?_eq_getElem?]
          simpa [hlast] using hin1
      refine ⟨2, by omega, ?_⟩
      change (lastBitRAMachine.step input false c1).state = none ∧
        (lastBitRAMachine.step input false c1).accept = (input.getLast? == some true)
      simp only [RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, ↓reduceIte, hgetLast]
      simp
    | none =>
      have hlast : c.addr = input.length - 1 := by
        have hge : input.length ≤ c1.addr := by
          by_contra hlt_n
          have hsome := List.getElem?_eq_getElem (by omega : c1.addr < input.length)
          simp [hin1] at hsome
        omega
      have hgetLast : input.getLast? = some (input[c.addr]) := by
        cases input with
        | nil => simp at hlt
        | cons a as =>
          rw [List.getLast?_eq_getElem?, show (a :: as).length - 1 = c.addr from hlast.symm]
          exact List.getElem?_eq_getElem hlt
      let c2 := lastBitRAMachine.step input false c1
      have hc2_st : c2.state = some .readLast := by
        dsimp only [c2]
        simp only [RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, ↓reduceIte]
      have hc1_ip : c1.idxPos = 0 := by simp [c1, RAATM.step, lastBitRAMachine, hst, hip]
      have hc1_hi : c1.idxHi = p + 1 := by
        dsimp only [c1, RAATM.step, lastBitRAMachine]
        rw [hst, hhi, hip]
        exact Nat.max_eq_left (by omega)
      have hc2_tape : c2.idxTape = c.idxTape := by
        dsimp only [c2]
        simp only [RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, ↓reduceIte, hc1_ip]
        funext z
        by_cases hz : z = 0
        · subst hz
          have h0 : c.idxTape 0 = some false := by simpa using hlow 0 le_rfl
          simp [c1, RAATM.step, lastBitRAMachine, hst, hip, h0]
        · simp [c1, RAATM.step, lastBitRAMachine, hst, hip, Function.update_of_ne hz]
      have hc2_hi : c2.idxHi = p + 1 := by
        dsimp only [c2]
        simp only [RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, ↓reduceIte,
          hc1_ip, hc1_hi]
        exact Nat.max_eq_left (by omega)
      have hc2_addr : c2.addr = c.addr := by
        simp [RACfg.addr, hc2_tape, hc2_hi, hhi]
      refine ⟨3, by omega, ?_⟩
      change (lastBitRAMachine.step input false c2).state = none ∧
        (lastBitRAMachine.step input false c2).accept = (input.getLast? == some true)
      simp only [RAATM.step, lastBitRAMachine, hc2_st, hc2_addr,
        List.getElem?_eq_getElem hlt, hgetLast]
      simp
  | succ j ih =>
    intro c hjp hinv
    rcases hinv with ⟨hst, hip, hwp, hhi, hwt, hlow, hmid, hhigh, hlt, hle⟩
    let c1 := lastBitRAMachine.step input false c
    have hc1_st : c1.state = some .binTest := by simp [c1, RAATM.step, lastBitRAMachine, hst]
    have hc1_ip : c1.idxPos = ((j + 1 : ℕ) : ℤ) := by
      simp [c1, RAATM.step, lastBitRAMachine, hst, hip]
    have hc1_wp : c1.workPos 0 = ((j + 1 : ℕ) : ℤ) := by
      simp [c1, RAATM.step, lastBitRAMachine, hst, hwp]
    have hc1_workTape : c1.workTape 0 = c.workTape 0 := by
      simp [c1, RAATM.step, lastBitRAMachine, hst]
    have hc1_wt : c1.workTape 0 (c1.workPos 0) = none := by
      rw [hc1_workTape, hwt, hc1_wp]
      exact ite_eq_right (by omega)
    have hc1_wt_fn : (fun i : Fin 1 => c1.workTape i (c1.workPos i)) = fun _ => none := by
      funext i; rw [Subsingleton.elim i 0]; exact hc1_wt
    have hc1_tape : c1.idxTape = Function.update c.idxTape ((j + 1 : ℕ) : ℤ) (some true) := by
      dsimp only [c1]
      simp only [RAATM.step, lastBitRAMachine, hst, hip]
    have hc1_addr : c1.addr = c.addr + 2 ^ (j + 1) := by
      dsimp only [RACfg.addr, c1, RAATM.step, lastBitRAMachine]
      rw [hst, hhi, hip]
      have hmax : max (p + 1) (Int.toNat (((j + 1 : ℕ) : ℤ) + 1)) = p + 1 := by omega
      rw [hmax]
      exact decodeIndexAux_flipBit c.idxTape
        (Function.update c.idxTape ((j + 1 : ℕ) : ℤ) (some true)) (j + 1) p hjp hlow
        (fun i hi => Function.update_of_ne (by omega) _ _) (Function.update_self _ _ _)
    let c2 := lastBitRAMachine.step input false c1
    have hc1_hi : c1.idxHi = p + 1 := by
      dsimp only [c1, RAATM.step, lastBitRAMachine]; rw [hst, hhi, hip]
      exact Nat.max_eq_left (by omega)
    have hbin2 : BinInv input p j c2 := by
      cases hin1 : input[c1.addr]? with
      | some b =>
        have hc1_lt : c1.addr < input.length := (List.getElem?_eq_some_iff.mp hin1).1
        have hc2_tape : c2.idxTape = c1.idxTape := by
          simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn]
        have hc2_hi : c2.idxHi = p + 1 := by
          simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_hi]
        have haddr2 : c2.addr = c1.addr := by
          simp [RACfg.addr, hc2_tape, hc2_hi, hc1_hi]
        refine ⟨by simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn],
          by simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_ip],
          by simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_wp],
          hc2_hi,
          fun z => by
            simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_workTape, hwt z],
          fun i hi => by
            rw [hc2_tape, hc1_tape, Function.update_of_ne (by omega)]
            exact hlow i (by omega),
          fun i hi hltp => by
            rw [hc2_tape, hc1_tape]
            by_cases hij : i = j + 1
            · subst hij; exact ⟨true, Function.update_self _ _ _⟩
            · rw [Function.update_of_ne (by omega)]
              exact hmid i (by omega) hltp,
          fun i hi => by
            rw [hc2_tape, hc1_tape, Function.update_of_ne (by omega)]
            exact hhigh i hi,
          haddr2 ▸ hc1_lt,
          by
            rw [haddr2, hc1_addr]
            have h2pow : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) + 2 ^ (j + 1) := by
              rw [Nat.pow_succ]; ring
            omega⟩
      | none =>
        have hc1_ge : input.length ≤ c1.addr := by
          by_contra hlt_n
          have hsome := List.getElem?_eq_getElem (by omega : c1.addr < input.length)
          simp [hin1] at hsome
        have hidx_eq : c2.idxTape = c.idxTape := by
          have hc2_t : c2.idxTape = Function.update c1.idxTape c1.idxPos (some false) := by
            simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn]
          rw [hc2_t, hc1_ip, hc1_tape]
          funext z
          by_cases hz : z = ((j + 1 : ℕ) : ℤ)
          · subst hz
            rw [Function.update_self]
            exact (hlow (j + 1) le_rfl).symm
          · rw [Function.update_of_ne hz, Function.update_of_ne hz]
        have hc2_hi : c2.idxHi = p + 1 := by
          simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_hi, hc1_ip]
          omega
        have haddr2 : c2.addr = c.addr := by
          simp [RACfg.addr, hidx_eq, hc2_hi, hhi]
        refine ⟨by simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn],
          by simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_ip],
          by simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_wp],
          hc2_hi,
          fun z => by
            simp [c2, RAATM.step, lastBitRAMachine, hc1_st, hin1, hc1_wt_fn, hc1_workTape, hwt z],
          fun i hi => by rw [hidx_eq]; exact hlow i (by omega),
          fun i hi hltp => by
            rw [hidx_eq]
            by_cases hij : i = j + 1
            · subst hij; exact ⟨false, hlow (j + 1) le_rfl⟩
            · exact hmid i (by omega) hltp,
          fun i hi => by rw [hidx_eq]; exact hhigh i hi,
          haddr2 ▸ hlt,
          by rw [haddr2]; omega⟩
    obtain ⟨steps, hle_s, hrun⟩ := ih c2 (by omega) hbin2
    refine ⟨steps + 2, by omega, ?_⟩
    have hr : lastBitRAMachine.runCoins input c (List.replicate (steps + 2) false) =
        lastBitRAMachine.runCoins input c2 (List.replicate steps false) := rfl
    simpa [hr] using hrun

private def ProbeInv (input : List Bool) (p : ℕ) (c : RACfg 1 LastBitState) : Prop :=
  c.state = some .probe ∧
    c.idxPos = (p : ℤ) ∧
    c.workPos 0 = (p : ℤ) ∧
    c.idxHi = p + 1 ∧
    (∀ z : ℤ, c.workTape 0 z = if z = 0 then some true else none) ∧
    (∀ i : ℕ, i < p → c.idxTape (i : ℤ) = some false) ∧
    c.idxTape (p : ℤ) = some true ∧
    (∀ i : ℕ, p + 1 ≤ i → c.idxTape (i : ℤ) = none) ∧
    (p = 0 ∨ 2 ^ (p - 1) < input.length)

private theorem lastBitRAMachine_probe_none_run (input : List Bool) (hne : 1 ≤ input.length)
    (p : ℕ) (c : RACfg 1 LastBitState) (hinv : ProbeInv input p c)
    (hpow_gt : input.length ≤ 2 ^ p) :
    ∃ steps ≤ 2 * p + 3,
      let cf := lastBitRAMachine.runCoins input c (List.replicate steps false)
      cf.state = none ∧ cf.accept = (input.getLast? == some true) := by
  rcases hinv with ⟨hst, hip, hwp, hhi, hwt, hlow, htop, hnone, hpow⟩
  have haddr : c.addr = 2 ^ p := by
    rw [RACfg.addr, hhi]
    exact decodeIndexAux_pow c.idxTape p hlow htop
  have hin : input[c.addr]? = none := by
    rw [haddr]
    exact List.getElem?_eq_none hpow_gt
  by_cases hp0 : p = 0
  · subst hp0
    have hlen1 : input.length = 1 := by omega
    have hc1_wt : c.workTape 0 (c.workPos 0) = some true := by rw [hwp, hwt]; rfl
    let c1 := lastBitRAMachine.step input false c
    have hc1_st : c1.state = some .readLast := by
      simp [c1, RAATM.step, lastBitRAMachine, hst, hin, hc1_wt]
    have hc1_tape : c1.idxTape = Function.update c.idxTape c.idxPos (some false) := by
      simp [c1, RAATM.step, lastBitRAMachine, hst, hin, hc1_wt]
    have hc1_hi : c1.idxHi = 1 := by
      have hmx : max c.idxHi (Int.toNat (c.idxPos + 1)) = 1 := by simp [hhi, hip]
      simp [c1, RAATM.step, lastBitRAMachine, hst, hin, hc1_wt, hmx]
    have hc1_addr : c1.addr = 0 := by
      rw [RACfg.addr, hc1_hi, hc1_tape, hip]
      simp [decodeIndexAux]
    have hlast0 : input.getLast? = input[0]? := by
      cases input with
      | nil => simp at hne
      | cons a as =>
        cases as with
        | nil => rfl
        | cons _ _ => simp at hlen1
    refine ⟨2, by omega, ?_⟩
    change (lastBitRAMachine.step input false c1).state = none ∧
      (lastBitRAMachine.step input false c1).accept = (input.getLast? == some true)
    dsimp only [RAATM.step, lastBitRAMachine]
    rw [hc1_st, hc1_addr, ← hlast0]
    cases hget : input.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hget) (by intro h; simp [h] at hne)
    | some b => simp
  · have hp_pos : 1 ≤ p := by omega
    have hprev : 2 ^ (p - 1) < input.length := hpow.resolve_left hp0
    have hwt_none : c.workTape 0 (c.workPos 0) = none := by
      rw [hwp, hwt]; exact ite_eq_right (by omega)
    let c1 := lastBitRAMachine.step input false c
    have hc1_eq : c1 = {
        state := some .binSet
        accept := c.accept
        idxTape := Function.update c.idxTape c.idxPos none
        idxPos := c.idxPos + ((-1 : SignType) : ℤ)
        idxHi := c.idxHi
        workTape := fun i => c.workTape i
        workPos := fun i => c.workPos i + ((-1 : SignType) : ℤ) } := by
      dsimp only [c1, RAATM.step, lastBitRAMachine]
      rw [hst, hin]
      simp [hwt_none]
    have hbin : BinInv input p (p - 1) c1 := by
      have hc1_tape : ∀ i : ℕ, c1.idxTape (i : ℤ) =
          if i = p then none else c.idxTape (i : ℤ) := by
        intro i
        rw [hc1_eq]; dsimp only; rw [hip]
        by_cases hip' : i = p
        · subst hip'; simp
        · simp [hip']
      have hc1_hi : c1.idxHi = p + 1 := by rw [hc1_eq]; exact hhi
      have hc1_addr : c1.addr = 0 := by
        rw [RACfg.addr, hc1_hi]
        clear hprev hwt_none
        have hz : ∀ pos fuel, pos + fuel ≤ p + 1 →
            decodeIndexAux c1.idxTape pos fuel = 0 := by
          intro pos fuel hpf
          induction fuel generalizing pos with
          | zero => rfl
          | succ f ihf =>
            dsimp only [decodeIndexAux]
            by_cases hpp : pos < p
            · rw [hc1_tape pos, ite_eq_right (by omega), hlow pos hpp]
              rw [ihf (pos + 1) (by omega)]; rfl
            · have hpeq : pos = p := by omega
              subst hpeq; rw [hc1_tape pos]; simp
        exact hz 0 (p + 1) (Nat.zero_add (p + 1)).le
      refine ⟨by rw [hc1_eq],
        by rw [hc1_eq]; dsimp only; rw [hip]; simp; omega,
        by rw [hc1_eq]; dsimp only; rw [hwp]; simp; omega,
        hc1_hi,
        fun z => by rw [hc1_eq]; exact hwt z,
        fun i hi => by rw [hc1_tape i, ite_eq_right (by omega)]; exact hlow i (by omega),
        fun i hi hltp => by omega,
        fun i hi => by
          by_cases hpi : i = p
          · simp [hc1_tape, hpi]
          · rw [hc1_tape i, ite_eq_right hpi]; exact hnone i (by omega),
        by rw [hc1_addr]; omega,
        by rw [hc1_addr, Nat.zero_add, show p - 1 + 1 = p from by omega]; exact hpow_gt⟩
    obtain ⟨steps, hle_s, hrun⟩ := lastBitRAMachine_bin_run input p (p - 1) c1 (by omega) hbin
    refine ⟨steps + 1, by omega, ?_⟩
    have hr : lastBitRAMachine.runCoins input c (List.replicate (steps + 1) false) =
        lastBitRAMachine.runCoins input c1 (List.replicate steps false) := rfl
    simpa [hr] using hrun

private theorem lastBitRAMachine_probe_run (input : List Bool) (hne : 1 ≤ input.length) :
    ∀ kRem p : ℕ, p + kRem = Nat.log 2 input.length + 1 →
      ∀ c : RACfg 1 LastBitState, ProbeInv input p c →
        ∃ steps ≤ 4 * (Nat.log 2 input.length + 1 - p) + 2 * p + 3,
          let cf := lastBitRAMachine.runCoins input c (List.replicate steps false)
          cf.state = none ∧ cf.accept = (input.getLast? == some true) := by
  intro kRem
  induction kRem with
  | zero =>
    intro p hsum c hinv
    have hpow_gt : input.length ≤ 2 ^ p := by
      have hp_eq : p = Nat.log 2 input.length + 1 := by omega
      rw [hp_eq]
      exact (Nat.lt_pow_succ_log_self (by omega) input.length).le
    obtain ⟨steps, hle, hrun⟩ := lastBitRAMachine_probe_none_run input hne p c hinv hpow_gt
    exact ⟨steps, by omega, hrun⟩
  | succ kRem ih =>
    intro p hsum c hinv
    rcases hinv with ⟨hst, hip, hwp, hhi, hwt, hlow, htop, hnone, hpow⟩
    have haddr : c.addr = 2 ^ p := by
      rw [RACfg.addr, hhi]; exact decodeIndexAux_pow c.idxTape p hlow htop
    cases hin : input[c.addr]? with
    | none =>
      have hpow_gt : input.length ≤ 2 ^ p := by
        rw [haddr] at hin
        by_contra hlt_n
        have hsome := List.getElem?_eq_getElem (by omega : 2 ^ p < input.length)
        simp [hin] at hsome
      have hinv' : ProbeInv input p c := ⟨hst, hip, hwp, hhi, hwt, hlow, htop, hnone, hpow⟩
      obtain ⟨steps, hle, hrun⟩ := lastBitRAMachine_probe_none_run input hne p c hinv' hpow_gt
      exact ⟨steps, by omega, hrun⟩
    | some b =>
      have h2p_lt : 2 ^ p < input.length := haddr ▸ (List.getElem?_eq_some_iff.mp hin).1
      let c1 := lastBitRAMachine.step input false c
      let c2 := lastBitRAMachine.step input false c1
      have hc1_st : c1.state = some .setProbeBit := by
        dsimp only [c1]; simp only [RAATM.step, lastBitRAMachine, hst, hin]
      have hc1_ip : c1.idxPos = ((p + 1 : ℕ) : ℤ) := by
        simp [c1, RAATM.step, lastBitRAMachine, hst, hin, hip]
      have hc1_wp : c1.workPos 0 = ((p + 1 : ℕ) : ℤ) := by
        simp [c1, RAATM.step, lastBitRAMachine, hst, hin, hwp]
      have hc1_hi : c1.idxHi = p + 1 := by
        dsimp only [c1]; simp only [RAATM.step, lastBitRAMachine, hst, hin, hhi, hip]
        exact Nat.max_eq_left (by omega)
      have hprobe2 : ProbeInv input (p + 1) c2 := by
        have hc2_tape : ∀ i : ℕ, c2.idxTape (i : ℤ) =
            if i = p + 1 then some true else if i = p then some false else c.idxTape (i : ℤ) := by
          intro i
          dsimp only [c2]
          simp only [RAATM.step, lastBitRAMachine, hc1_st, hc1_ip]
          dsimp only [c1]
          simp only [RAATM.step, lastBitRAMachine, hst, hin, hip]
          by_cases h1 : i = p + 1
          · subst h1
            rw [Function.update_self]
            simp
          · rw [Function.update_of_ne (by omega)]
            by_cases h2 : i = p
            · subst h2; simp
            · rw [Function.update_of_ne (by omega)]
              simp [h1, h2]
        refine ⟨by dsimp only [c2]; simp only [RAATM.step, lastBitRAMachine, hc1_st],
          by dsimp only [c2]; simp only [RAATM.step, lastBitRAMachine, hc1_st, hc1_ip]; rfl,
          by dsimp only [c2]; simp only [RAATM.step, lastBitRAMachine, hc1_st, hc1_wp]; rfl,
          by dsimp only [c2]; simp only [RAATM.step, lastBitRAMachine, hc1_st, hc1_ip, hc1_hi]
             omega,
          fun z => by
            dsimp only [c2]; simp only [RAATM.step, lastBitRAMachine, hc1_st]
            dsimp only [c1]; simp only [RAATM.step, lastBitRAMachine, hst, hin]
            exact hwt z,
          fun i hi => by
            rw [hc2_tape i]
            by_cases hip' : i = p
            · subst hip'; simp
            · simp [show i ≠ p + 1 from by omega, hip', hlow i (by omega)],
          by rw [hc2_tape (p + 1)]; simp,
          fun i hi => by
            rw [hc2_tape i]
            simp only [show i ≠ p + 1 from by omega, show i ≠ p from by omega, ↓reduceIte]
            exact hnone i (by omega),
          Or.inr (by simpa using h2p_lt)⟩
      obtain ⟨steps, hle_s, hrun⟩ := ih (p + 1) (by omega) c2 hprobe2
      refine ⟨steps + 2, by omega, ?_⟩
      have hr : lastBitRAMachine.runCoins input c (List.replicate (steps + 2) false) =
          lastBitRAMachine.runCoins input c2 (List.replicate steps false) := rfl
      simpa [hr] using hrun

/-- `lastBitLanguage ∈ RADTIME(log(n + 2))`: binary search discovers `x.length` and reads
`x[n - 1]` in `O(log n)` steps. -/
theorem lastBitLanguage_mem_RADTIME_log :
    lastBitLanguage ∈ RADTIME (fun n => Nat.log 2 (n + 2)) := by
  refine ⟨4, 12, 1, LastBitState, inferInstance, lastBitRAMachine, lastBitRAMachine_det, ?_⟩
  intro x
  let T : ℕ := 4 * Nat.log 2 (x.length + 2) + 12
  have hex_halt : ∃ steps ≤ T,
      let cf := lastBitRAMachine.runCoins x (RACfg.init .start) (List.replicate steps false)
      cf.state = none ∧ cf.accept = (x.getLast? == some true) := by
    cases hx0 : x[0]? with
    | none =>
      have hxnil : x = [] := List.getElem?_eq_none_iff.mp hx0 |> fun h =>
        List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
      refine ⟨1, by omega, ?_⟩
      simp [RAATM.runCoins, RAATM.step, lastBitRAMachine, RACfg.init, RACfg.addr, decodeIndexAux,
        hxnil]
    | some b0 =>
      have hne : 1 ≤ x.length := by
        cases x with | nil => simp at hx0 | cons _ _ => simp
      let c1 := lastBitRAMachine.step x false (RACfg.init .start)
      have hinit_addr : (RACfg.init (k := 1) LastBitState.start).addr = 0 := rfl
      have hc1_rw : c1 = {
          state := some .probe
          accept := false
          idxTape := Function.update (fun _ => none) 0 (some true)
          idxPos := 0
          idxHi := 1
          workTape := fun _ => Function.update (fun _ => none) 0 (some true)
          workPos := fun _ => 0 } := by
        dsimp only [c1, RAATM.step, lastBitRAMachine]
        rw [hinit_addr, hx0]
        simp [RACfg.init]
      have hprobe0 : ProbeInv x 0 c1 := by
        refine ⟨by simp [hc1_rw], by simp [hc1_rw], by simp [hc1_rw], by simp [hc1_rw],
          fun z => by rw [hc1_rw]; by_cases hz : z = 0 <;> simp [hz, Function.update],
          fun i hi => by omega,
          by simp [hc1_rw],
          fun i hi => by rw [hc1_rw]; simp [Function.update_of_ne (by omega : (i : ℤ) ≠ 0)],
          Or.inl rfl⟩
      obtain ⟨steps, hle_s, hrun⟩ := lastBitRAMachine_probe_run x hne
        (Nat.log 2 x.length + 1) 0 (by omega) c1 hprobe0
      have hlog_le : Nat.log 2 x.length ≤ Nat.log 2 (x.length + 2) :=
        Nat.log_mono_right (by omega)
      refine ⟨steps + 1, by omega, ?_⟩
      change (lastBitRAMachine.runCoins x c1 (List.replicate steps false)).state = none ∧
        (lastBitRAMachine.runCoins x c1 (List.replicate steps false)).accept =
          (x.getLast? == some true)
      exact hrun
  obtain ⟨s, hs_le, hs_st, hs_acc⟩ := hex_halt
  have hstay : ∀ m : ℕ, s ≤ m →
      lastBitRAMachine.runCoins x (RACfg.init .start) (List.replicate m false) =
        lastBitRAMachine.runCoins x (RACfg.init .start) (List.replicate s false) := by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [List.replicate_add, RAATM.runCoins_append, lastBitRAMachine.runCoins_halt_eq x hs_st]
  refine ⟨fun bs hbs => ?_, ?_⟩
  · change (lastBitRAMachine.runCoins x (RACfg.init .start) bs).state = none
    rw [runCoins_det_eq lastBitRAMachine lastBitRAMachine_det, hbs, hstay T hs_le]
    exact hs_st
  · rw [lastBitLanguage, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨s, (acceptsWithin_det_iff lastBitRAMachine lastBitRAMachine_det x s _).mpr ?_⟩
      change (lastBitRAMachine.runCoins x (RACfg.init .start)
          (List.replicate s false)).state = none ∧
        (lastBitRAMachine.runCoins x (RACfg.init .start)
          (List.replicate s false)).accept = true
      rw [hs_st, hs_acc]
      simp [hx]
    · rintro ⟨t, ht⟩
      have hcf := (acceptsWithin_det_iff lastBitRAMachine lastBitRAMachine_det x t _).mp ht
      change (lastBitRAMachine.runCoins x (RACfg.init .start)
          (List.replicate t false)).state = none ∧
        (lastBitRAMachine.runCoins x (RACfg.init .start)
          (List.replicate t false)).accept = true at hcf
      by_cases hts : s ≤ t
      · rw [hstay t hts, hs_acc] at hcf
        simpa using hcf.2
      · have hkeep : lastBitRAMachine.runCoins x (RACfg.init .start) (List.replicate s false) =
            lastBitRAMachine.runCoins x (RACfg.init .start) (List.replicate t false) := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (by omega : t ≤ s)
          rw [hd, List.replicate_add, RAATM.runCoins_append,
            lastBitRAMachine.runCoins_halt_eq x hcf.1]
        rw [hkeep, hcf.2] at hs_acc
        simpa using hs_acc.symm

/-! #### Hypothesis `(H)` compatibility (`DTIME ∪ NTIME ∪ coNTIME ⊆ ATIME(O(F(T) + log T))`) -/

/-- Exact number of accepting `t`-bit branching paths of `M` on `input`. -/
noncomputable def RAATM.accCount {k : ℕ} {State : Type} (M : RAATM k State)
    (input : List Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (2 ^ t) =>
    (M.runCoins input (RACfg.init M.q₀) (List.ofFn (fun p : Fin t => i.val.testBit p.val))).accept =
      true).card

/-- Auxiliary-argument acceptance for a pre-loaded `j` bit string on worktape `0`. -/
@[expose] def RAATM.AcceptsFromAux {k : ℕ} {State : Type} (M : RAATM (k + 1) State)
    (input aux : List Bool) : Prop :=
  ∃ t, M.AcceptsWithin input t (RACfg.initWithAux M.q₀ (Nat.succ_pos k) aux)

/-- Bit-index problem associated to a clocked NTM `M` running in time `T`. -/
def ntmAccBitLanguage {k : ℕ} {State : Type} (M : RAATM k State) (T : ℕ → ℕ) :
    Set (List Bool × List Bool) :=
  {p | ∃ j : ℕ, p.2 = List.ofFn (fun i : Fin (Nat.log 2 (T p.1.length) + 1) =>
      j.testBit i.val) ∧
    (M.accCount p.1 (T p.1.length)).testBit j = true}

/-- **Supplied Hypothesis `(H)`** in the Index-TM random-access model: for every clocked
nondeterministic `RAATM` running in `T(|x|)` steps, any specified bit `j` (encoded in binary on
the auxiliary worktape) of `accCount M x (T |x|)` is computable in `RAATIME(O(F(T)))` from
configuration `RACfg.initWithAux`. -/
@[expose] def HypothesisH (T F : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (State : Type) (_ : Finite State) (M : RAATM k State),
    RAATM.HasPhaseBound 1 false M →
    (∀ x, M.ClockedHalts x (T x.length)) →
    ∃ (c₁ c₂ kE : ℕ) (StateE : Type) (_ : Finite StateE) (E : RAATM (kE + 1) StateE),
      ∀ (x : List Bool) (jBits : List Bool),
        jBits.length = Nat.log 2 (T x.length) + 1 →
        (∀ bs : List Bool, bs.length = c₁ * F (T x.length) + c₂ →
          (E.runCoins x (RACfg.initWithAux E.q₀ (Nat.succ_pos kE) jBits) bs).state = none) ∧
        ((E.AcceptsFromAux x jBits) ↔
          ∃ j : ℕ, jBits = List.ofFn (fun i : Fin (Nat.log 2 (T x.length) + 1) =>
              j.testBit i.val) ∧
            (M.accCount x (T x.length)).testBit j = true)

private theorem accCount_le_two_pow {k : ℕ} {State : Type} (M : RAATM k State)
    (input : List Bool) (t : ℕ) : M.accCount input t ≤ 2 ^ t := by
  unfold RAATM.accCount
  simpa using (Finset.card_filter_le _ _ : _ ≤ (Finset.univ : Finset (Fin (2 ^ t))).card)

private theorem hasPhaseBound_one_univ_false {k : ℕ} {State : Type} {M : RAATM k State}
    (hphase : RAATM.HasPhaseBound 1 false M) : ∀ q, M.univ q = false := by
  obtain ⟨phase, huniv, _⟩ := hphase
  intro q
  have h0 : (phase q).val = 0 := Nat.lt_one_iff.mp (phase q).2
  simpa [h0] using huniv q

private theorem acceptsWithin_existential_iff {k : ℕ} {State : Type} (M : RAATM k State)
    (huniv : ∀ q, M.univ q = false) (input : List Bool) (t : ℕ) (c : RACfg k State) :
    M.AcceptsWithin input t c ↔
      ∃ bs : List Bool, bs.length = t ∧
        (M.runCoins input c bs).state = none ∧ (M.runCoins input c bs).accept = true := by
  induction t generalizing c with
  | zero =>
    constructor
    · intro ⟨hst, hacc⟩
      exact ⟨[], rfl, hst, hacc⟩
    · rintro ⟨bs, hlen, hst, hacc⟩
      obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen
      exact ⟨hst, hacc⟩
  | succ t ih =>
    unfold RAATM.AcceptsWithin
    cases hst : c.state with
    | none =>
      constructor
      · intro hacc
        refine ⟨List.replicate (t + 1) false, List.length_replicate, ?_⟩
        rw [M.runCoins_halt_eq input hst]
        exact ⟨hst, hacc⟩
      · rintro ⟨bs, _, hst', hacc'⟩
        rw [M.runCoins_halt_eq input hst] at hst' hacc'
        exact hacc'
    | some q =>
      simp only [huniv q, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨b, hb⟩
        obtain ⟨bs, hlen, hst', hacc'⟩ := (ih (M.step input b c)).mp hb
        exact ⟨b :: bs, by simp [hlen], hst', hacc'⟩
      · rintro ⟨bs, hlen, hst', hacc'⟩
        cases bs with
        | nil => simp at hlen
        | cons b bs =>
          refine ⟨b, (ih (M.step input b c)).mpr ⟨bs, by simp at hlen; omega, hst', hacc'⟩⟩

/-- Acceptance equivalence connecting clocked nondeterministic `RAATM` acceptance with positive
accepting-path count `0 < M.accCount x (T x.length)`. -/
theorem RAATM.accepts_iff_accCount_pos {T : ℕ → ℕ} {k : ℕ} {State : Type} (M : RAATM k State)
    (hphase : RAATM.HasPhaseBound 1 false M) (hhalt : ∀ x, M.ClockedHalts x (T x.length))
    (x : List Bool) :
    M.Accepts x ↔ 0 < M.accCount x (T x.length) := by
  have huniv := hasPhaseBound_one_univ_false hphase
  have hwithin : M.Accepts x ↔ M.AcceptsWithin x (T x.length) (RACfg.init M.q₀) := by
    constructor
    · rintro ⟨t, ht⟩
      rw [acceptsWithin_existential_iff M huniv] at ht ⊢
      obtain ⟨bs, hlen, hst, hacc⟩ := ht
      by_cases htle : t ≤ T x.length
      · refine ⟨bs ++ List.replicate (T x.length - t) false, by simp [hlen]; omega, ?_⟩
        rw [RAATM.runCoins_append, M.runCoins_halt_eq x hst]
        exact ⟨hst, hacc⟩
      · have hle : T x.length ≤ t := by omega
        let bs₁ := bs.take (T x.length)
        have hlen1 : bs₁.length = T x.length := by simp [bs₁, hlen, hle]
        have hst1 : (M.runCoins x (RACfg.init M.q₀) bs₁).state = none := hhalt x bs₁ hlen1
        have heq_run : M.runCoins x (RACfg.init M.q₀) bs =
            M.runCoins x (RACfg.init M.q₀) bs₁ := by
          conv_lhs => rw [← List.take_append_drop (T x.length) bs]
          rw [RAATM.runCoins_append]
          exact M.runCoins_halt_eq x hst1 _
        rw [heq_run] at hacc
        exact ⟨bs₁, hlen1, hst1, hacc⟩
    · exact fun h => ⟨T x.length, h⟩
  rw [hwithin, acceptsWithin_existential_iff M huniv]
  unfold RAATM.accCount
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨bs, hlen, _, hacc⟩
    refine ⟨⟨Cslib.BitString.lsbValue bs, hlen ▸ Cslib.BitString.lsbValue_lt bs⟩,
      Finset.mem_univ _, ?_⟩
    have hof : List.ofFn (fun p : Fin (T x.length) =>
        (Cslib.BitString.lsbValue bs).testBit p.val) = bs := by
      have hlb := Cslib.BitString.lowBits_lsbValue bs
      rw [Cslib.BitString.lowBits_eq_ofFn] at hlb
      refine List.ext_getElem (by simp [hlen]) fun j hj1 hj2 => ?_
      have hget := congrArg (fun l : List Bool => l[j]?) hlb
      simp [hj2]
    rw [hof]
    exact hacc
  · rintro ⟨i, -, hacc⟩
    let bs := List.ofFn (fun p : Fin (T x.length) => i.val.testBit p.val)
    have hlen : bs.length = T x.length := by simp [bs]
    exact ⟨bs, hlen, hhalt x bs hlen, hacc⟩

private theorem accCount_pos_iff_exists_bit {k : ℕ} {State : Type} (M : RAATM k State)
    (input : List Bool) (t : ℕ) :
    0 < M.accCount input t ↔ ∃ j < 2 ^ (Nat.log 2 t + 1),
      (M.accCount input t).testBit j = true := by
  constructor
  · intro hpos
    have hex : ∃ j, (M.accCount input t).testBit j = true := by
      by_contra hall
      push Not at hall
      have hz : M.accCount input t = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        simpa [Nat.zero_testBit] using Bool.eq_false_iff.mpr (hall j)
      omega
    obtain ⟨j, hj⟩ := hex
    have hle : M.accCount input t ≤ 2 ^ t := accCount_le_two_pow M input t
    have hjt : j ≤ t := by
      by_contra hgt
      have hbig : M.accCount input t < 2 ^ j := by
        calc M.accCount input t ≤ 2 ^ t := hle
          _ < 2 ^ j := Nat.pow_lt_pow_right (by omega) (by omega)
      have hfalse := Nat.testBit_lt_two_pow hbig
      rw [hfalse] at hj
      exact Bool.false_ne_true hj
    have ht_lt : t < 2 ^ (Nat.log 2 t + 1) := Nat.lt_pow_succ_log_self (by omega) t
    exact ⟨j, by omega, hj⟩
  · rintro ⟨j, -, hj⟩
    by_contra h0
    have hz : M.accCount input t = 0 := by omega
    rw [hz, Nat.zero_testBit] at hj
    exact Bool.false_ne_true hj

/-- Model-compatibility check (positive branch): under Hypothesis `(H)`, there is a uniform
evaluator `E` checking `#acc > 0` by guessing `Nat.log 2 (T |x|) + 1` bits for the bit index
`j ≤ T |x|` and running `(H)` in alternating time `O(F(T) + log T)`. -/
theorem exists_RAATIME_evaluator_of_H {T F : ℕ → ℕ} (hH : HypothesisH T F)
    {k : ℕ} {State : Type} [Finite State] (M : RAATM k State)
    (hphase : RAATM.HasPhaseBound 1 false M) (hhalt : ∀ x, M.ClockedHalts x (T x.length)) :
    ∃ (c₁ c₂ kE : ℕ) (StateE : Type) (_ : Finite StateE) (E : RAATM (kE + 1) StateE),
      ∀ x : List Bool,
        (∀ jBits : List Bool, jBits.length = Nat.log 2 (T x.length) + 1 →
          ∀ bs : List Bool, bs.length = c₁ * F (T x.length) + c₂ →
            (E.runCoins x (RACfg.initWithAux E.q₀ (Nat.succ_pos kE) jBits) bs).state = none) ∧
        ((∃ b : List Bool, b.length = Nat.log 2 (T x.length) + 1 ∧
          E.AcceptsFromAux x b) ↔ 0 < M.accCount x (T x.length)) := by
  obtain ⟨c₁, c₂, kE, StateE, hfinE, E, hEspec⟩ := hH k State ‹_› M hphase hhalt
  refine ⟨c₁, c₂, kE, StateE, hfinE, E, fun x => ?_⟩
  refine ⟨fun jBits hlen bs hbs => (hEspec x jBits hlen).1 bs hbs, ?_⟩
  rw [accCount_pos_iff_exists_bit]
  constructor
  · rintro ⟨jBits, hlen, hacc⟩
    obtain ⟨j, -, hbit⟩ := ((hEspec x jBits hlen).2).mp hacc
    have hle : M.accCount x (T x.length) ≤ 2 ^ (T x.length) := accCount_le_two_pow M x (T x.length)
    have hjt : j ≤ T x.length := by
      by_contra hgt
      have hltj : T x.length < j := by omega
      have hpowj : 2 ^ (T x.length) < 2 ^ j :=
        Nat.pow_lt_pow_right (by omega) hltj
      have hfalse := Nat.testBit_lt_two_pow (hle.trans_lt hpowj)
      rw [hfalse] at hbit
      exact Bool.false_ne_true hbit
    exact ⟨j, lt_of_le_of_lt hjt (Nat.lt_pow_succ_log_self (by omega) _), hbit⟩
  · rintro ⟨j, _, hbit⟩
    let jBits := List.ofFn (fun i : Fin (Nat.log 2 (T x.length) + 1) => j.testBit i.val)
    have hjBits_len : jBits.length = Nat.log 2 (T x.length) + 1 := by simp [jBits]
    refine ⟨jBits, hjBits_len, ((hEspec x jBits hjBits_len).2).mpr ⟨j, rfl, hbit⟩⟩

/-- Complementary model-compatibility check (`RACoNTIME`): a single uniform evaluator `E` tests
`#acc = 0` iff EVERY bit index `j` of width `Nat.log 2 (T |x|) + 1` returns `false`. -/
theorem forall_RAATIME_evaluator_of_H {T F : ℕ → ℕ} (hH : HypothesisH T F)
    {k : ℕ} {State : Type} [Finite State] (M : RAATM k State)
    (hphase : RAATM.HasPhaseBound 1 false M) (hhalt : ∀ x, M.ClockedHalts x (T x.length)) :
    ∃ (c₁ c₂ kE : ℕ) (StateE : Type) (_ : Finite StateE) (E : RAATM (kE + 1) StateE),
      ∀ x : List Bool,
        (∀ jBits : List Bool, jBits.length = Nat.log 2 (T x.length) + 1 →
          ∀ bs : List Bool, bs.length = c₁ * F (T x.length) + c₂ →
            (E.runCoins x (RACfg.initWithAux E.q₀ (Nat.succ_pos kE) jBits) bs).state = none) ∧
        ((∀ b : List Bool, b.length = Nat.log 2 (T x.length) + 1 →
          ¬ E.AcceptsFromAux x b) ↔ M.accCount x (T x.length) = 0) := by
  obtain ⟨c₁, c₂, kE, StateE, hfinE, E, hE⟩ :=
    exists_RAATIME_evaluator_of_H hH M hphase hhalt
  refine ⟨c₁, c₂, kE, StateE, hfinE, E, fun x => ?_⟩
  refine ⟨(hE x).1, ?_⟩
  have heq := not_congr (hE x).2
  push Not at heq
  simpa using heq

/-! #### Abstract RA Selector-Bit Composition Theorem -/

/-- Evaluator predicate for the merged `∃ ∀ ∃` branch after adding a universal selector bit. -/
def selectorEval {α C U V W P Q : Type} (E : α → C → U → V → W → Bool)
    (B : α → C → P → Q → Bool) (x : α) (cu : C × U) :
    (svp : (side : Bool) × cond side P V) → cond svp.1 Q W → Prop
  | ⟨false, v⟩, w => E x cu.1 cu.2 v w = true
  | ⟨true, p⟩, q => B x cu.1 p q = false

/-- **Selector-bit composition theorem**: if a switch witness `c` satisfies an `∃ ∀ ∃` test `E`
and the negation of an `∃ ∀` test `B`, adding one universal selector bit `side : Bool` merges
`(∃ u ∀ v ∃ w, E c u v w) ∧ ¬(∃ p ∀ q, B c p q)` directly into a single `∃ ∀ ∃` quantifier
block `(∃ (c, u) ∀ (side, chal) ∃ resp)` with challenge size `max(|V|, |P|) + 1`. -/
theorem selectorBit_composition {α C U V W P Q : Type} {A : Set α}
    {E : α → C → U → V → W → Bool} {B : α → C → P → Q → Bool}
    (hA : ∀ x : α, x ∈ A ↔ ∃ c : C,
      (∃ u : U, ∀ v : V, ∃ w : W, E x c u v w = true) ∧
      ¬ (∃ p : P, ∀ q : Q, B x c p q = true)) :
    ∀ x : α, x ∈ A ↔
      ∃ cu : C × U, ∀ svp : (side : Bool) × cond side P V,
        ∃ wq : cond svp.1 Q W, selectorEval E B x cu svp wq := by
  intro x
  rw [hA x]
  constructor
  · rintro ⟨c, ⟨u, hu⟩, hB⟩
    push Not at hB
    refine ⟨(c, u), fun ⟨side, chal⟩ => ?_⟩
    cases side
    · obtain ⟨w, hw⟩ := hu chal
      exact ⟨w, hw⟩
    · obtain ⟨q, hq⟩ := hB chal
      exact ⟨q, Bool.eq_false_iff.mpr hq⟩
  · rintro ⟨⟨c, u⟩, h⟩
    refine ⟨c, ⟨u, fun v => ?_⟩, ?_⟩
    · obtain ⟨w, hw⟩ := h ⟨false, v⟩
      exact ⟨w, hw⟩
    · push Not
      intro p
      obtain ⟨q, hq⟩ := h ⟨true, p⟩
      exact ⟨q, Bool.eq_false_iff.mp hq⟩

end RandomAccessMachine

/-! ### Part III: Relativization Counterexample via `∀`-Winning Subtree Query Counting -/

section RelativizationBarrier

/-- Finite binary alternating oracle decision tree of depth `≤ d`:
at each internal node, either evaluates a leaf boolean, queries oracle `A` on bitstring `q`,
takes an existential `∃` branch over two subtrees, or takes a universal `∀` branch over two
subtrees. -/
inductive OracleAltTree where
  | leaf (b : Bool)
  | query (q : List Bool) (tTrue tFalse : OracleAltTree)
  | existNode (left right : OracleAltTree)
  | univNode (left right : OracleAltTree)

/-- Depth (time bound) of an alternating oracle tree. -/
def OracleAltTree.depth : OracleAltTree → ℕ
  | .leaf _ => 0
  | .query _ t₁ t₂ => 1 + max t₁.depth t₂.depth
  | .existNode t₁ t₂ => 1 + max t₁.depth t₂.depth
  | .univNode t₁ t₂ => 1 + max t₁.depth t₂.depth

/-- Semantics of an alternating oracle tree relative to oracle `A : List Bool → Bool`. -/
def OracleAltTree.eval (A : List Bool → Bool) : OracleAltTree → Bool
  | .leaf b => b
  | .query q t₁ t₂ => if A q = true then t₁.eval A else t₂.eval A
  | .existNode t₁ t₂ => t₁.eval A || t₂.eval A
  | .univNode t₁ t₂ => t₁.eval A && t₂.eval A

/-- Set of oracle strings queried along an accepting `∀`-minimal strategy subtree (`existNode`
picks whichever child accepts, `univNode` keeps both children, `query` follows `A q`). -/
noncomputable def witnessQueriedSet (A : List Bool → Bool) :
    OracleAltTree → Finset (List Bool)
  | .leaf _ => ∅
  | .query q t₁ t₂ =>
    insert q (if A q = true then witnessQueriedSet A t₁ else witnessQueriedSet A t₂)
  | .existNode t₁ t₂ =>
    if t₁.eval A = true then witnessQueriedSet A t₁ else witnessQueriedSet A t₂
  | .univNode t₁ t₂ => witnessQueriedSet A t₁ ∪ witnessQueriedSet A t₂

/-- **Query-count bound on accepting `∀`-subtrees**:
Every depth-`d` binary alternating oracle tree has an accepting strategy querying at most
`2 ^ d` strings (and trivially `< 2 ^ (d + 1)`). Notice that only universal branches double the
strategy size; existential nodes branch once and query nodes take one outcome. -/
theorem witnessQueriedSet_card_le (A : List Bool → Bool) (T : OracleAltTree) :
    (witnessQueriedSet A T).card ≤ 2 ^ T.depth := by
  induction T with
  | leaf _ => simp [witnessQueriedSet, OracleAltTree.depth]
  | query q t₁ t₂ ih₁ ih₂ =>
    dsimp only [witnessQueriedSet, OracleAltTree.depth]
    have hcard : (insert q (if A q = true then witnessQueriedSet A t₁ else
        witnessQueriedSet A t₂)).card ≤
        (if A q = true then witnessQueriedSet A t₁ else witnessQueriedSet A t₂).card + 1 :=
      Finset.card_insert_le _ _
    have hpow : 1 ≤ 2 ^ max t₁.depth t₂.depth := Nat.one_le_pow _ 2 (by omega)
    have hsub : (if A q = true then witnessQueriedSet A t₁ else
        witnessQueriedSet A t₂).card ≤ 2 ^ max t₁.depth t₂.depth := by
      split_ifs
      · exact ih₁.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      · exact ih₂.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    rw [Nat.add_comm 1 _, Nat.pow_succ]
    omega
  | existNode t₁ t₂ ih₁ ih₂ =>
    dsimp only [witnessQueriedSet, OracleAltTree.depth]
    split_ifs
    · exact ih₁.trans (Nat.pow_le_pow_right (by omega)
        (le_trans (le_max_left _ _) (Nat.le_add_left _ 1)))
    · exact ih₂.trans (Nat.pow_le_pow_right (by omega)
        (le_trans (le_max_right _ _) (Nat.le_add_left _ 1)))
  | univNode t₁ t₂ ih₁ ih₂ =>
    dsimp only [witnessQueriedSet, OracleAltTree.depth]
    have h1 : (witnessQueriedSet A t₁).card ≤ 2 ^ max t₁.depth t₂.depth :=
      ih₁.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have h2 : (witnessQueriedSet A t₂).card ≤ 2 ^ max t₁.depth t₂.depth :=
      ih₂.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    have hu := Finset.card_union_le (witnessQueriedSet A t₁) (witnessQueriedSet A t₂)
    rw [Nat.add_comm 1 _, Nat.pow_succ]
    omega

/-- Any oracle `B` agreeing with `A` on `witnessQueriedSet A T` forces `T.eval B = true`
whenever `T.eval A = true`. -/
theorem eval_eq_true_of_eqOn_witnessQueriedSet {A B : List Bool → Bool} {T : OracleAltTree}
    (heval : T.eval A = true)
    (hagree : ∀ q ∈ witnessQueriedSet A T, B q = A q) :
    T.eval B = true := by
  induction T with
  | leaf b => simpa [OracleAltTree.eval] using heval
  | query q t₁ t₂ ih₁ ih₂ =>
    dsimp only [witnessQueriedSet] at hagree
    have hq : B q = A q := hagree q (Finset.mem_insert_self _ _)
    dsimp only [OracleAltTree.eval] at heval ⊢
    rw [hq]
    by_cases ha : A q = true
    · simp only [ha] at heval hagree ⊢
      exact ih₁ heval fun r hr => hagree r (Finset.mem_insert_of_mem hr)
    · simp only [ha] at heval hagree ⊢
      exact ih₂ heval fun r hr => hagree r (Finset.mem_insert_of_mem hr)
  | existNode t₁ t₂ ih₁ ih₂ =>
    dsimp only [OracleAltTree.eval] at heval ⊢
    dsimp only [witnessQueriedSet] at hagree
    by_cases h1 : t₁.eval A = true
    · simp only [h1] at hagree
      simp [ih₁ h1 hagree]
    · simp only [h1] at hagree
      have h2 : t₂.eval A = true := by
        cases h1b : t₁.eval A <;> simp_all
      simp [ih₂ h2 hagree]
  | univNode t₁ t₂ ih₁ ih₂ =>
    dsimp only [OracleAltTree.eval] at heval ⊢
    dsimp only [witnessQueriedSet] at hagree
    rw [Bool.and_eq_true] at heval ⊢
    exact ⟨ih₁ heval.1 (fun q hq => hagree q (Finset.mem_union_left _ hq)),
      ih₂ heval.2 (fun q hq => hagree q (Finset.mem_union_right _ hq))⟩

private theorem card_bitStrings_of_length (L : ℕ) :
    ∃ U : Finset (List Bool), U.card = 2 ^ L ∧ ∀ y, y ∈ U ↔ y.length = L := by
  let f : Fin (2 ^ L) → List Bool := fun i => List.ofFn (fun p : Fin L => i.val.testBit p.val)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < L
    · have := congrArg (fun l : List Bool => l[i]?) hab
      simpa [f, hi] using this
    · have ha : a.val < 2 ^ L := a.isLt
      have hb : b.val < 2 ^ L := b.isLt
      have hpow : 2 ^ L ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (ha.trans_le hpow),
        Nat.testBit_lt_two_pow (hb.trans_le hpow)]
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective Finset.univ hf_inj, Finset.card_fin]
  · intro y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, -, rfl⟩
      simp [f]
    · rintro rfl
      refine Finset.mem_image.mpr
        ⟨⟨Cslib.BitString.lsbValue y, Cslib.BitString.lsbValue_lt y⟩, Finset.mem_univ _, ?_⟩
      simp [f]

/-- Dualize an alternating oracle tree (flipping leaves and swapping `∃`/`∀`). -/
def OracleAltTree.negate : OracleAltTree → OracleAltTree
  | .leaf b => .leaf (!b)
  | .query q t₁ t₂ => .query q t₁.negate t₂.negate
  | .existNode t₁ t₂ => .univNode t₁.negate t₂.negate
  | .univNode t₁ t₂ => .existNode t₁.negate t₂.negate

theorem OracleAltTree.depth_negate (T : OracleAltTree) : T.negate.depth = T.depth := by
  induction T with
  | leaf _ => rfl
  | query _ _ _ ih₁ ih₂ => simp [OracleAltTree.negate, OracleAltTree.depth, ih₁, ih₂]
  | existNode _ _ ih₁ ih₂ => simp [OracleAltTree.negate, OracleAltTree.depth, ih₁, ih₂]
  | univNode _ _ ih₁ ih₂ => simp [OracleAltTree.negate, OracleAltTree.depth, ih₁, ih₂]

theorem OracleAltTree.eval_negate (A : List Bool → Bool) (T : OracleAltTree) :
    T.negate.eval A = !(T.eval A) := by
  induction T with
  | leaf _ => rfl
  | query q _ _ ih₁ ih₂ =>
    dsimp only [OracleAltTree.negate, OracleAltTree.eval]
    split_ifs <;> simp [ih₁, ih₂]
  | existNode _ _ ih₁ ih₂ =>
    simp [OracleAltTree.negate, OracleAltTree.eval, ih₁, ih₂, Bool.not_or]
  | univNode _ _ ih₁ ih₂ =>
    simp [OracleAltTree.negate, OracleAltTree.eval, ih₁, ih₂, Bool.not_and]

private structure OracleStage where
  pos : Finset (List Bool)
  frozen : Finset (List Bool)
  pos_sub : pos ⊆ frozen

private noncomputable def oracleAt (st : OracleStage) (y : List Bool) : Bool :=
  letI : DecidablePred (· ∈ st.pos) := Classical.decPred _
  decide (y ∈ st.pos)

private noncomputable def nextOracleStage {T : ℕ → ℕ}
    (hT_unbounded : ∀ B : ℕ, ∃ N, ∀ n ≥ N, B ≤ T n)
    (tree : ℕ → ℕ → OracleAltTree) (ht : ∀ e, ∃ N, ∀ n ≥ N, (tree e n).depth < T n)
    (e : ℕ) (st : OracleStage) :
    {st' : OracleStage × ℕ //
      st.frozen ⊆ st'.1.frozen ∧
      (∀ q ∈ st.frozen, q ∈ st'.1.pos ↔ q ∈ st.pos) ∧
      ((∃ y : List Bool, y.length = T st'.2 ∧ oracleAt st'.1 y = true) ↔
        ¬ ((tree e st'.2).eval (oracleAt st'.1) = true)) ∧
      (∀ y : List Bool, y.length = T st'.2 → y ∈ st'.1.frozen) ∧
      (∀ B : List Bool → Bool,
        (∀ q ∈ st'.1.frozen, B q = oracleAt st'.1 q) →
        (tree e st'.2).eval B = (tree e st'.2).eval (oracleAt st'.1))} := by
  classical
  let maxF : ℕ := st.frozen.sup List.length + 1
  let N₁ := Classical.choose (hT_unbounded maxF)
  have hN₁ := Classical.choose_spec (hT_unbounded maxF)
  let N₂ := Classical.choose (ht e)
  have hN₂ := Classical.choose_spec (ht e)
  let n := max N₁ N₂
  have hTn_big : maxF ≤ T n := hN₁ n (le_max_left _ _)
  have hlen_frozen : ∀ q ∈ st.frozen, q.length < T n := fun q hq =>
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hq)) hTn_big
  have hdepth : (tree e n).depth < T n := hN₂ n (le_max_right _ _)
  let U := Classical.choose (card_bitStrings_of_length (T n))
  have hU_spec := Classical.choose_spec (card_bitStrings_of_length (T n))
  have hUcard : U.card = 2 ^ T n := hU_spec.1
  have hUmem : ∀ y, y ∈ U ↔ y.length = T n := hU_spec.2
  let Ae := oracleAt st
  by_cases hev : (tree e n).eval Ae = true
  · let S := witnessQueriedSet Ae (tree e n)
    let st' : OracleStage :=
      { pos := st.pos
        frozen := st.frozen ∪ S ∪ U
        pos_sub := st.pos_sub.trans (Finset.subset_union_left.trans Finset.subset_union_left) }
    have hfrozen_sub : st.frozen ⊆ st'.frozen :=
      Finset.subset_union_left.trans Finset.subset_union_left
    have hpos_agree : ∀ q ∈ st.frozen, q ∈ st'.pos ↔ q ∈ st.pos := fun _ _ => Iff.rfl
    have heval' : (tree e n).eval (oracleAt st') = true := by
      refine eval_eq_true_of_eqOn_witnessQueriedSet hev fun q hq => ?_
      simp [oracleAt, st', Ae]
    have hno_y : ¬ (∃ y : List Bool, y.length = T n ∧ oracleAt st' y = true) := by
      rintro ⟨y, hylen, hytrue⟩
      have hyp : y ∈ st.pos := by simpa [oracleAt, st'] using hytrue
      have hlt := hlen_frozen y (st.pos_sub hyp)
      omega
    refine ⟨⟨st', n⟩, hfrozen_sub, hpos_agree, ?_, ?_, ?_⟩
    · simp [hno_y, heval']
    · intro y hy
      exact Finset.mem_union_right _ ((hUmem y).mpr hy)
    · intro B hB
      have hevB : (tree e n).eval B = true := by
        refine eval_eq_true_of_eqOn_witnessQueriedSet hev fun q hq => ?_
        have hqF : q ∈ st'.frozen := Finset.mem_union_left _ (Finset.mem_union_right _ hq)
        rw [hB q hqF]
        simp [oracleAt, st', Ae]
      rw [hevB, heval']
  · let S := witnessQueriedSet Ae (tree e n).negate
    have hScard : S.card ≤ 2 ^ (tree e n).depth := by
      simpa [OracleAltTree.depth_negate] using witnessQueriedSet_card_le Ae (tree e n).negate
    have hlt : S.card < U.card := by
      have hpow : 2 ^ (tree e n).depth < 2 ^ T n := Nat.pow_lt_pow_right (by omega) hdepth
      omega
    have hex_unqueried : ∃ y, y ∈ U ∧ y ∉ S := by
      by_contra hall
      push Not at hall
      have := Finset.card_le_card hall
      omega
    let y₀ := Classical.choose hex_unqueried
    have hy₀_spec := Classical.choose_spec hex_unqueried
    have hy₀U : y₀ ∈ U := hy₀_spec.1
    have hy₀S : y₀ ∉ S := hy₀_spec.2
    have hy₀_len : y₀.length = T n := (hUmem y₀).mp hy₀U
    let st' : OracleStage :=
      { pos := insert y₀ st.pos
        frozen := insert y₀ (st.frozen ∪ S ∪ U)
        pos_sub := fun q hq => by
          rcases Finset.mem_insert.mp hq with rfl | hq'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_union_left _ (st.pos_sub hq'))) }
    have hfrozen_sub : st.frozen ⊆ st'.frozen := fun q hq =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hq))
    have hpos_agree : ∀ q ∈ st.frozen, q ∈ st'.pos ↔ q ∈ st.pos := by
      intro q hq
      have hlt := hlen_frozen q hq
      constructor
      · intro h
        rcases Finset.mem_insert.mp h with heq | hmem
        · subst heq; omega
        · exact hmem
      · intro h
        exact Finset.mem_insert_of_mem h
    have hev_neg₀ : (tree e n).negate.eval Ae = true := by
      rw [OracleAltTree.eval_negate]
      cases h : (tree e n).eval Ae <;> simp_all
    have hagree_S : ∀ q ∈ S, oracleAt st' q = Ae q := by
      intro q hq
      have hneq : q ≠ y₀ := fun heq => hy₀S (heq ▸ hq)
      simp [oracleAt, st', Ae, hneq]
    have hev_neg₁ : (tree e n).negate.eval (oracleAt st') = true :=
      eval_eq_true_of_eqOn_witnessQueriedSet hev_neg₀ hagree_S
    have hev₁ : (tree e n).eval (oracleAt st') = false := by
      rw [OracleAltTree.eval_negate] at hev_neg₁
      simpa using hev_neg₁
    have hy₀_pos : oracleAt st' y₀ = true := by simp [oracleAt, st']
    refine ⟨⟨st', n⟩, hfrozen_sub, hpos_agree, ?_, ?_, ?_⟩
    · simp [hev₁, (⟨y₀, hy₀_len, hy₀_pos⟩ : ∃ y, y.length = T n ∧ oracleAt st' y = true)]
    · intro y hy
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hUmem y).mpr hy))
    · intro B hB
      have hevB_neg : (tree e n).negate.eval B = true := by
        refine eval_eq_true_of_eqOn_witnessQueriedSet hev_neg₀ fun q hq => ?_
        have hqF : q ∈ st'.frozen :=
          Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hq))
        rw [hB q hqF, hagree_S q hq]
      rw [OracleAltTree.eval_negate] at hevB_neg
      have hevB : (tree e n).eval B = false := by simpa using hevB_neg
      rw [hevB, hev₁]

private noncomputable def stageSeq {T : ℕ → ℕ}
    (hT_unbounded : ∀ B : ℕ, ∃ N, ∀ n ≥ N, B ≤ T n)
    (tree : ℕ → ℕ → OracleAltTree) (ht : ∀ e, ∃ N, ∀ n ≥ N, (tree e n).depth < T n) :
    ℕ → OracleStage × ℕ
  | 0 => (⟨∅, ∅, Finset.Subset.rfl⟩, 0)
  | e + 1 => (nextOracleStage hT_unbounded tree ht e (stageSeq hT_unbounded tree ht e).1).1

private theorem stageSeq_monotone {T : ℕ → ℕ}
    (hT_unbounded : ∀ B : ℕ, ∃ N, ∀ n ≥ N, B ≤ T n)
    (tree : ℕ → ℕ → OracleAltTree) (ht : ∀ e, ∃ N, ∀ n ≥ N, (tree e n).depth < T n) :
    ∀ e k : ℕ, e ≤ k →
      (stageSeq hT_unbounded tree ht e).1.frozen ⊆ (stageSeq hT_unbounded tree ht k).1.frozen ∧
      ∀ q ∈ (stageSeq hT_unbounded tree ht e).1.frozen,
        q ∈ (stageSeq hT_unbounded tree ht k).1.pos ↔
          q ∈ (stageSeq hT_unbounded tree ht e).1.pos := by
  intro e k hek
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hek
  induction d with
  | zero => exact ⟨Finset.Subset.rfl, fun _ _ => Iff.rfl⟩
  | succ d ih =>
    have ihd := ih (by omega)
    have hstep := (nextOracleStage hT_unbounded tree ht (e + d)
      (stageSeq hT_unbounded tree ht (e + d)).1).2
    refine ⟨ihd.1.trans hstep.1, fun q hq => ?_⟩
    have hq' := ihd.1 hq
    exact (hstep.2.1 q hq').trans (ihd.2 q hq)

/-- **Baker–Gill–Solovay diagonal oracle separation (`NTIME^A(T) ⊈ ATIME^A(t)`)**:
For any unbounded length map `T` and any uniform sequence of alternating oracle trees `tree e n`
with `depth (tree e n) < T n` eventually in `n` (such as `depth ≤ O(T / √(log T))`), there exists
a single oracle `A` separating `L_OR^A(T)` from EVERY machine `e` simultaneously. -/
theorem oracle_separation_family {T : ℕ → ℕ}
    (hT_unbounded : ∀ B : ℕ, ∃ N, ∀ n ≥ N, B ≤ T n)
    (tree : ℕ → ℕ → OracleAltTree)
    (ht : ∀ e, ∃ N, ∀ n ≥ N, (tree e n).depth < T n) :
    ∃ A : List Bool → Bool, ∀ e : ℕ, ∃ n : ℕ,
      ((∃ y : List Bool, y.length = T n ∧ A y = true) ↔ ¬ ((tree e n).eval A = true)) := by
  classical
  let A : List Bool → Bool := fun q =>
    if h : ∃ k : ℕ, q ∈ (stageSeq hT_unbounded tree ht k).1.frozen then
      decide (q ∈ (stageSeq hT_unbounded tree ht h.choose).1.pos)
    else false
  have hagree_stage : ∀ (k : ℕ) (q : List Bool),
      q ∈ (stageSeq hT_unbounded tree ht k).1.frozen →
      A q = oracleAt (stageSeq hT_unbounded tree ht k).1 q := by
    intro k q hqf
    have hex : ∃ m : ℕ, q ∈ (stageSeq hT_unbounded tree ht m).1.frozen := ⟨k, hqf⟩
    simp only [A, hex, ↓reduceDIte, oracleAt]
    have hmq : q ∈ (stageSeq hT_unbounded tree ht hex.choose).1.frozen := Classical.choose_spec hex
    rcases le_total hex.choose k with hmk | hkm
    · have hm := (stageSeq_monotone hT_unbounded tree ht hex.choose k hmk).2 q hmq
      simp [hm]
    · have hk := (stageSeq_monotone hT_unbounded tree ht k hex.choose hkm).2 q hqf
      simp [hk]
  refine ⟨A, fun e => ?_⟩
  let next := nextOracleStage hT_unbounded tree ht e (stageSeq hT_unbounded tree ht e).1
  let n := next.1.2
  have hstage_eq : (stageSeq hT_unbounded tree ht (e + 1)) = next.1 := rfl
  refine ⟨n, ?_⟩
  have hspec := next.2
  have hiff_st := hspec.2.2.1
  have hlen_frozen : ∀ y : List Bool, y.length = T n →
      y ∈ next.1.1.frozen := hspec.2.2.2.1
  have hy_agree : (∃ y : List Bool, y.length = T n ∧ A y = true) ↔
      (∃ y : List Bool, y.length = T n ∧ oracleAt next.1.1 y = true) := by
    refine exists_congr fun y => and_congr_right fun hy => ?_
    rw [hagree_stage (e + 1) y (hstage_eq ▸ hlen_frozen y hy)]
    rfl
  have hev_agree : (tree e n).eval A = (tree e n).eval (oracleAt next.1.1) :=
    hspec.2.2.2.2 A fun q hq => by
      rw [hagree_stage (e + 1) q (hstage_eq ▸ hq)]
      rfl
  rw [hy_agree, hev_agree]
  exact hiff_st

end RelativizationBarrier

/-! ### Part IV: Unconditional Clocked Checkpoint Speedups (`NTISP` & Asymmetric `Σ₂-TISP`) -/

section CheckpointSpeedups

/-- Run `w` steps of a transition `step : C → Bool → C` along boolean vector `Fin b → Bool`. -/
def runBlock {C : Type} (step : C → Bool → C) : ∀ {b : ℕ}, C → (Fin b → Bool) → C
  | 0, c, _ => c
  | _ + 1, c, w => runBlock step (step c (w 0)) (fun i => w i.succ)

/-- Run `len` steps of `step` reading from a `ℕ → Bool` tape starting at `off`. -/
def runWindow {C : Type} (step : C → Bool → C) (w : ℕ → Bool) :
    ℕ → ℕ → C → C
  | _, 0, c => c
  | off, len + 1, c => runWindow step w (off + 1) len (step c (w off))

private theorem runWindow_add {C : Type} (step : C → Bool → C) (w : ℕ → Bool)
    (off a b : ℕ) (c : C) :
    runWindow step w off (a + b) c =
      runWindow step w (off + a) b (runWindow step w off a c) := by
  induction a generalizing off c with
  | zero => simp [runWindow]
  | succ a ih =>
    rw [Nat.succ_add, runWindow, ih (off + 1) (step c (w off)),
      show off + 1 + a = off + (a + 1) from by omega]
    rfl

private theorem runBlock_eq_runWindow {C : Type} (step : C → Bool → C) (b off : ℕ)
    (w : ℕ → Bool) (blk : Fin b → Bool) (hblk : ∀ i : Fin b, blk i = w (off + i.val))
    (c : C) :
    runBlock step c blk = runWindow step w off b c := by
  induction b generalizing off c with
  | zero => rfl
  | succ b ih =>
    dsimp only [runBlock, runWindow]
    rw [hblk 0, Fin.val_zero, Nat.add_zero]
    refine ih (off + 1) (fun i => blk i.succ) ?_ (step c (w off))
    intro i
    have hsucc : (i.succ : Fin (b + 1)).val = i.val + 1 := Fin.val_succ i
    have hi' := hblk i.succ
    simpa [hsucc, show off + (i.val + 1) = off + 1 + i.val from by omega] using hi'

/-- **Unconditional `NTISP` checkpoint block simulation (`∃ ∀ ∃` / `Σ₃`)**:
`∃ w : Fin (m * b) → Bool, acc (runBlock step c₀ w) = true` holds if and only if
there exist `m + 1` checkpoints `ck : Fin (m + 1) → C` (`ck 0 = c₀`, `acc (ck m) = true`)
such that for every block `∀ j : Fin m`, there exists `∃ w_j : Fin b → Bool` bridging
`ck j` to `ck (j + 1)`. Certificate length is `(m + 1) * W`, block check cost is `b`. -/
theorem ntmBlockSimulation {C : Type} (step : C → Bool → C) (acc : C → Bool)
    (c₀ : C) (m b : ℕ) (hb : 0 < b) :
    (∃ w : Fin (m * b) → Bool, acc (runBlock step c₀ w) = true) ↔
      ∃ ck : Fin (m + 1) → C,
        (ck 0 = c₀ ∧ acc (ck ⟨m, Nat.lt_succ_self m⟩) = true) ∧
        ∀ j : Fin m, ∃ blk : Fin b → Bool,
          runBlock step (ck ⟨j.val, by omega⟩) blk = ck ⟨j.val + 1, by omega⟩ := by
  constructor
  · rintro ⟨w, hw⟩
    let padW : ℕ → Bool := fun i => if hi : i < m * b then w ⟨i, hi⟩ else false
    let ck : Fin (m + 1) → C := fun i => runWindow step padW 0 (i.val * b) c₀
    have hck0 : ck 0 = c₀ := by simp [ck, runWindow]
    have hw_win : runBlock step c₀ w = ck ⟨m, Nat.lt_succ_self m⟩ := by
      refine runBlock_eq_runWindow step (m * b) 0 padW w ?_ c₀
      intro i
      simp [padW, i.isLt]
    refine ⟨ck, ⟨hck0, hw_win ▸ hw⟩, fun j => ?_⟩
    let blk : Fin b → Bool := fun i => padW (j.val * b + i.val)
    refine ⟨blk, ?_⟩
    rw [runBlock_eq_runWindow step b (j.val * b) padW blk (fun _ => rfl)]
    dsimp [ck]
    have hmul : (j.val + 1) * b = j.val * b + b := by ring
    rw [hmul, runWindow_add]
    simp
  · rintro ⟨ck, ⟨h0, hm⟩, hstep⟩
    choose blk hblk using hstep
    let padW : ℕ → Bool := fun i =>
      if hi : i / b < m then
        if hr : i % b < b then blk ⟨i / b, hi⟩ ⟨i % b, hr⟩ else false
      else false
    have hinv : ∀ j : ℕ, (hj : j ≤ m) →
        runWindow step padW 0 (j * b) c₀ = ck ⟨j, by omega⟩ := by
      intro j
      induction j with
      | zero =>
        intro _
        simpa [runWindow] using h0.symm
      | succ j ih =>
        intro hj
        have hmul : (j + 1) * b = j * b + b := by ring
        rw [hmul, runWindow_add, Nat.zero_add, ih (by omega)]
        have hlt : j < m := by omega
        have hrw := runBlock_eq_runWindow step b (j * b) padW (blk ⟨j, hlt⟩) ?_
          (ck ⟨j, by omega⟩)
        · rw [← hrw]
          exact hblk ⟨j, hlt⟩
        · intro i
          dsimp only [padW]
          have hdiv : (j * b + i.val) / b = j := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
          have hmod : (j * b + i.val) % b = i.val := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
          simp [hdiv, hmod, hlt, i.isLt]
    let w : Fin (m * b) → Bool := fun i => padW i.val
    refine ⟨w, ?_⟩
    have hw_win : runBlock step c₀ w = ck ⟨m, Nat.lt_succ_self m⟩ :=
      (runBlock_eq_runWindow step (m * b) 0 padW w (fun i => by simp [w]) c₀).trans
        (hinv m le_rfl)
    rw [hw_win]
    exact hm

/-- **Unconditional deterministic checkpoint simulation (`∃ ∀` / `Σ₂`)**:
`acc (step^[m * b] c₀) = true` holds if and only if there exist `m + 1` checkpoints
`ck : Fin (m + 1) → C` with `ck 0 = c₀`, `acc (ck m) = true`, and `∀ j : Fin m`,
`step^[b] (ck j) = ck (j + 1)`. -/
theorem detBlockSimulation {C : Type} (step : C → C) (acc : C → Bool)
    (c₀ : C) (m b : ℕ) :
    acc (step^[m * b] c₀) = true ↔
      ∃ ck : Fin (m + 1) → C,
        (ck 0 = c₀ ∧ acc (ck ⟨m, Nat.lt_succ_self m⟩) = true) ∧
        ∀ j : Fin m, step^[b] (ck ⟨j.val, by omega⟩) = ck ⟨j.val + 1, by omega⟩ := by
  constructor
  · intro hacc
    let ck : Fin (m + 1) → C := fun i => step^[i.val * b] c₀
    have hck0 : ck 0 = c₀ := by simp [ck]
    refine ⟨ck, ⟨hck0, hacc⟩, fun j => ?_⟩
    dsimp [ck]
    rw [← Function.iterate_add_apply step b (j.val * b) c₀]
    congr 2
    ring
  · rintro ⟨ck, ⟨h0, hm⟩, hstep⟩
    have hinv : ∀ i : Fin (m + 1), ck i = step^[i.val * b] c₀ := by
      intro ⟨i, hi⟩
      induction i with
      | zero => simpa using h0
      | succ i ih =>
        have ih' := ih (by omega)
        have hs := hstep ⟨i, by omega⟩
        dsimp only at hs
        rw [← hs, ih', ← Function.iterate_add_apply step b (i * b) c₀]
        congr 2
        ring
    rw [hinv ⟨m, Nat.lt_succ_self m⟩] at hm
    exact hm

/-- Verification predicate for the **Asymmetric `Σ₂-TISP` Speedup**. -/
def sigma2AsymEval {C : Type} {r : ℕ} (step₁ : C → Bool → C)
    (step₂ : (Fin r → Bool) → C → C)
    (acc : C → Bool) (c₀ : C) (m₁ b₁ m₂ b₂ : ℕ)
    (csw : C) (ck₁ : Fin (m₁ + 1) → C) :
    (svp : (side : Bool) × cond side ((Fin r → Bool) × (Fin (m₂ + 1) → C)) (Fin m₁)) →
      cond svp.1 (Fin m₂) (Fin b₁ → Bool) → Prop
  | ⟨false, j₁⟩, blk =>
    ck₁ 0 = c₀ ∧ ck₁ ⟨m₁, Nat.lt_succ_self m₁⟩ = csw ∧
      runBlock step₁ (ck₁ ⟨j₁.val, by omega⟩) blk = ck₁ ⟨j₁.val + 1, by omega⟩
  | ⟨true, (y, ck₂)⟩, j₂ =>
    ck₂ 0 ≠ csw ∨ acc (ck₂ ⟨m₂, Nat.lt_succ_self m₂⟩) = true ∨
      (step₂ y)^[b₂] (ck₂ ⟨j₂.val, by omega⟩) ≠ ck₂ ⟨j₂.val + 1, by omega⟩

/-- **Unconditional Asymmetric `Σ₂-TISP` Speedup Theorem**:
Suppose Phase 1 runs existentially for `m₁ * b₁` steps (`step₁`) to reach switch configuration
`c_sw`, and Phase 2 consumes at most `r` universal choice bits `y : Fin r → Bool` and then runs
deterministically for `m₂ * b₂` steps (`step₂ y`) checking `acc`. Note that Phase 1 may use full
`m₁ * b₁ = T` existential bits! Then acceptance holds iff a single 3-quantifier (`∃ ∀ ∃`) protocol
with outer existential `(c_sw, ck₁)`, middle universal `(side, j₁ | (y, ck₂))`, and inner
existential `(blk | j₂)` accepts. -/
theorem sigma2AsymmetricBlockSimulation {C : Type} {r : ℕ}
    (step₁ : C → Bool → C) (step₂ : (Fin r → Bool) → C → C) (acc : C → Bool)
    (c₀ : C) (m₁ b₁ m₂ b₂ : ℕ) (hm₁ : 0 < m₁) (hb₁ : 0 < b₁) (hm₂ : 0 < m₂) :
    (∃ w₁ : Fin (m₁ * b₁) → Bool,
      ∀ y : Fin r → Bool, acc ((step₂ y)^[m₂ * b₂] (runBlock step₁ c₀ w₁)) = true) ↔
    ∃ cu : C × (Fin (m₁ + 1) → C),
      ∀ svp : (side : Bool) × cond side ((Fin r → Bool) × (Fin (m₂ + 1) → C)) (Fin m₁),
        ∃ wq : cond svp.1 (Fin m₂) (Fin b₁ → Bool),
          sigma2AsymEval step₁ step₂ acc c₀ m₁ b₁ m₂ b₂ cu.1 cu.2 svp wq := by
  classical
  constructor
  · rintro ⟨w₁, hw₁⟩
    let csw := runBlock step₁ c₀ w₁
    have hE : ∃ ck₁ : Fin (m₁ + 1) → C, (ck₁ 0 = c₀ ∧ ck₁ ⟨m₁, Nat.lt_succ_self m₁⟩ = csw) ∧
        ∀ j : Fin m₁, ∃ blk : Fin b₁ → Bool,
          runBlock step₁ (ck₁ ⟨j.val, by omega⟩) blk = ck₁ ⟨j.val + 1, by omega⟩ := by
      obtain ⟨ck₁, ⟨h0, hm⟩, hs⟩ :=
        (ntmBlockSimulation step₁ (fun c => decide (c = csw)) c₀ m₁ b₁ hb₁).mp ⟨w₁, by simp [csw]⟩
      exact ⟨ck₁, ⟨h0, by simpa using hm⟩, hs⟩
    obtain ⟨ck₁, ⟨h0, hm⟩, hstep₁⟩ := hE
    refine ⟨(csw, ck₁), fun ⟨side, chal⟩ => ?_⟩
    cases side
    · obtain ⟨blk, hblk⟩ := hstep₁ chal
      exact ⟨blk, h0, hm, hblk⟩
    · rcases chal with ⟨y, ck₂⟩
      by_contra hbad
      push Not at hbad
      have hfalse : acc ((step₂ y)^[m₂ * b₂] csw) = false := by
        have h0' := not_or.mp (hbad ⟨0, hm₂⟩)
        have hcm' := not_or.mp h0'.2
        have hc0 : ck₂ 0 = csw := not_ne_iff.mp h0'.1
        have hcm : acc (ck₂ ⟨m₂, Nat.lt_succ_self m₂⟩) = false :=
          Bool.eq_false_iff.mpr hcm'.1
        have hsteps : ∀ j : Fin m₂,
            (step₂ y)^[b₂] (ck₂ ⟨j.val, by omega⟩) = ck₂ ⟨j.val + 1, by omega⟩ := fun j =>
          not_ne_iff.mp (not_or.mp (not_or.mp (hbad j)).2).2
        have hdet := (detBlockSimulation (step₂ y) (fun c => !(acc c)) csw m₂ b₂).mpr
          ⟨ck₂, ⟨hc0, by simp [hcm]⟩, hsteps⟩
        simpa using hdet
      have htrue := hw₁ y
      simp [csw, htrue] at hfalse
  · rintro ⟨⟨csw, ck₁⟩, h⟩
    have hE_all : ∀ j : Fin m₁, ck₁ 0 = c₀ ∧ ck₁ ⟨m₁, Nat.lt_succ_self m₁⟩ = csw ∧
        ∃ blk : Fin b₁ → Bool,
          runBlock step₁ (ck₁ ⟨j.val, by omega⟩) blk = ck₁ ⟨j.val + 1, by omega⟩ := by
      intro j
      obtain ⟨blk, h0, hm, hblk⟩ := h ⟨false, j⟩
      exact ⟨h0, hm, blk, hblk⟩
    obtain ⟨h0, hm, _⟩ := hE_all ⟨0, hm₁⟩
    obtain ⟨w₁, hw₁⟩ := (ntmBlockSimulation step₁ (fun c => decide (c = csw)) c₀ m₁ b₁ hb₁).mpr
      ⟨ck₁, ⟨h0, by simp [hm]⟩, fun j => (hE_all j).2.2⟩
    have hcsw_eq : runBlock step₁ c₀ w₁ = csw := by simpa using hw₁
    refine ⟨w₁, fun y => ?_⟩
    rw [hcsw_eq]
    by_contra hreject
    have hrej_bool : (!(acc ((step₂ y)^[m₂ * b₂] csw))) = true := by
      cases hacc : acc ((step₂ y)^[m₂ * b₂] csw) <;> simp_all
    obtain ⟨ck₂, ⟨h20, h2m⟩, h2step⟩ :=
      (detBlockSimulation (step₂ y) (fun c => !(acc c)) csw m₂ b₂).mp hrej_bool
    obtain ⟨j₂, hj₂⟩ := h ⟨true, (y, ck₂)⟩
    rcases hj₂ with hne | hacc_true | hstep_ne
    · exact hne h20
    · simp [hacc_true] at h2m
    · exact hstep_ne (h2step j₂)

/-- **Exact arithmetic bound for balanced checkpoint speedups**:
Whenever per-configuration bit length satisfies `W ≤ C * (T / Nat.log 2 T)` (`2 ≤ T`),
the balanced checkpoint simulation cost `Nat.sqrt (T * W)` is at most
`2 * (Nat.sqrt C + 1) * (T / Nat.sqrt (Nat.log 2 T))` = `O(T / √(log T))`. -/
theorem sqrt_mul_le_div_sqrt_log {T W C : ℕ} (hT : 2 ≤ T)
    (hW : W ≤ C * (T / Nat.log 2 T)) :
    Nat.sqrt (T * W) ≤ 2 * (Nat.sqrt C + 1) * (T / Nat.sqrt (Nat.log 2 T)) := by
  let L : ℕ := Nat.log 2 T
  let s : ℕ := Nat.sqrt L
  have hL_pos : 1 ≤ L := by
    by_contra h0
    have hL0 : Nat.log 2 T = 0 := by omega
    have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) T
    rw [hL0] at hlt
    omega
  have hs_pos : 1 ≤ s := Nat.sqrt_pos.mpr hL_pos
  have hs_le_L : s * s ≤ L := Nat.sqrt_le L
  have hs_le_T : s ≤ T := by
    calc s ≤ L := Nat.sqrt_le_self L
      _ ≤ T := Nat.log_le_self 2 T
  have hq_pos : 1 ≤ T / s := Nat.div_pos hs_le_T hs_pos
  have hT_lt : T < s * (T / s + 1) := by
    have hmod : T % s < s := Nat.mod_lt T hs_pos
    have hdiv := Nat.div_add_mod T s
    nlinarith
  have hprod_s : s * s * (T * (T / L)) ≤ T * T := by
    calc s * s * (T * (T / L))
        ≤ L * (T * (T / L)) := Nat.mul_le_mul_right _ hs_le_L
      _ = T * (L * (T / L)) := by ring
      _ ≤ T * T := Nat.mul_le_mul_left T (Nat.mul_div_le T L)
  have hT_sq_lt : T * T < (s * s) * ((T / s + 1) * (T / s + 1)) := by
    calc T * T < (s * (T / s + 1)) * (s * (T / s + 1)) := Nat.mul_self_lt_mul_self hT_lt
      _ = (s * s) * ((T / s + 1) * (T / s + 1)) := by ring
  have hcore : T * (T / L) < (T / s + 1) * (T / s + 1) :=
    Nat.lt_of_mul_lt_mul_left (hprod_s.trans_lt hT_sq_lt)
  have hC : C < (Nat.sqrt C + 1) * (Nat.sqrt C + 1) := by
    simpa [Nat.pow_two] using Nat.lt_succ_sqrt C
  have hbound : T * W ≤ ((Nat.sqrt C + 1) * (T / s + 1)) * ((Nat.sqrt C + 1) * (T / s + 1)) := by
    calc T * W ≤ T * (C * (T / L)) := Nat.mul_le_mul_left T hW
      _ = C * (T * (T / L)) := by ring
      _ ≤ C * ((T / s + 1) * (T / s + 1)) := Nat.mul_le_mul_left C hcore.le
      _ ≤ ((Nat.sqrt C + 1) * (Nat.sqrt C + 1)) * ((T / s + 1) * (T / s + 1)) :=
          Nat.mul_le_mul_right _ hC.le
      _ = ((Nat.sqrt C + 1) * (T / s + 1)) * ((Nat.sqrt C + 1) * (T / s + 1)) := by ring
  have hsqrt : Nat.sqrt (T * W) ≤ (Nat.sqrt C + 1) * (T / s + 1) := by
    calc Nat.sqrt (T * W) ≤ Nat.sqrt (((Nat.sqrt C + 1) * (T / s + 1)) *
        ((Nat.sqrt C + 1) * (T / s + 1))) := Nat.sqrt_le_sqrt hbound
      _ = (Nat.sqrt C + 1) * (T / s + 1) := Nat.sqrt_eq _
  have hq2 : T / s + 1 ≤ 2 * (T / s) := by omega
  calc Nat.sqrt (T * W) ≤ (Nat.sqrt C + 1) * (T / s + 1) := hsqrt
    _ ≤ (Nat.sqrt C + 1) * (2 * (T / s)) := Nat.mul_le_mul_left _ hq2
    _ = 2 * (Nat.sqrt C + 1) * (T / s) := by ring

/-- Configuration `c` uses at most spatial window `[-S, S]` on the index and work tapes. -/
def RACfg.WithinWindow {k : ℕ} {State : Type} (S : ℕ) (c : RACfg k State) : Prop :=
  (-(S : ℤ) ≤ c.idxPos ∧ c.idxPos ≤ (S : ℤ)) ∧
    c.idxHi ≤ S + 1 ∧
    (∀ z : ℤ, z < -(S : ℤ) ∨ (S : ℤ) < z → c.idxTape z = none) ∧
    (∀ i : Fin k, -(S : ℤ) ≤ c.workPos i ∧ c.workPos i ≤ (S : ℤ)) ∧
    (∀ (i : Fin k) (z : ℤ), z < -(S : ℤ) ∨ (S : ℤ) < z → c.workTape i z = none)

theorem RACfg.init_withinWindow {k : ℕ} {State : Type} (q₀ : State) (S : ℕ) :
    (RACfg.init q₀ : RACfg k State).WithinWindow S := by
  refine ⟨⟨by simp [RACfg.init], by simp [RACfg.init]⟩,
    by simp [RACfg.init], fun _ _ => rfl,
    fun _ => ⟨by simp [RACfg.init], by simp [RACfg.init]⟩, fun _ _ _ => rfl⟩

/-- Finite packed representation of an `RAATM` configuration restricted to tape window `[-S, S]`.
When `S = O(T / log T)`, the bit-length `compactCfgBitWidth k stateBits S` is `O(T / log T)`. -/
structure RACfgCompact (k : ℕ) (State : Type) (S : ℕ) where
  /-- Current control state, or `none` if halted. -/
  state : Option State
  /-- Latched Boolean acceptance bit. -/
  accept : Bool
  /-- Index-tape cell contents on `[-S, S]` shifted to `[0, 2 * S]`. -/
  idxCells : Fin (2 * S + 1) → Option Bool
  /-- Head position on `idxCells` (offset `+ S`). -/
  idxPos : Fin (2 * S + 1)
  /-- Tracked binary-decoding upper bound `idxHi ≤ S + 1`. -/
  idxHi : Fin (S + 2)
  /-- Work-tape cell contents on `[-S, S]` for each of the `k` tapes. -/
  workCells : Fin k → Fin (2 * S + 1) → Option Bool
  /-- Head positions on each of the `k` work tapes (offset `+ S`). -/
  workPos : Fin k → Fin (2 * S + 1)

/-- Explicit bit-length charge for encoding a `RACfgCompact k State S` checkpoint, counting `1`
tag bit for `Option State` (`stateBits + 1`), `1` bit for `accept : Bool`, `2` bits per
`Option Bool` cell on the `k + 1` active windows of length `2 * S + 1`, plus binary head positions
and `idxHi` ceiling. -/
@[expose] def compactCfgBitWidth (k stateBits S : ℕ) : ℕ :=
  stateBits + 2 + 2 * (2 * S + 1) * (k + 1) +
    (k + 1) * (Nat.log 2 (2 * S + 1) + 1) + (Nat.log 2 (S + 2) + 1)

theorem compactCfgBitWidth_le (k stateBits S : ℕ) :
    compactCfgBitWidth k stateBits S ≤
      (4 * k + 4) * S + stateBits + 2 * k + 5 +
        (k + 2) * (Nat.log 2 (2 * S + 1) + 1) := by
  have hlog : Nat.log 2 (S + 2) ≤ Nat.log 2 (2 * S + 1) + 1 := by
    have hle : S + 2 ≤ 2 * (2 * S + 1) := by omega
    calc Nat.log 2 (S + 2) ≤ Nat.log 2 (2 * (2 * S + 1)) := Nat.log_mono_right hle
      _ ≤ Nat.log 2 (2 * S + 1) + 1 := by
        by_cases hz : 2 * S + 1 = 0
        · omega
        · rw [Nat.mul_comm 2 _, Nat.log_mul_base (by omega) hz]
  unfold compactCfgBitWidth
  nlinarith

/-- Pack an `RACfg` into the bounded window `[-S, S]`. -/
@[expose] def RACfg.pack {k : ℕ} {State : Type} (S : ℕ) (c : RACfg k State) :
    RACfgCompact k State S where
  state := c.state
  accept := c.accept
  idxCells j := c.idxTape ((j.val : ℤ) - (S : ℤ))
  idxPos := ⟨Int.toNat (c.idxPos + (S : ℤ)) % (2 * S + 1), Nat.mod_lt _ (by omega)⟩
  idxHi := ⟨c.idxHi % (S + 2), Nat.mod_lt _ (by omega)⟩
  workCells i j := c.workTape i ((j.val : ℤ) - (S : ℤ))
  workPos i := ⟨Int.toNat (c.workPos i + (S : ℤ)) % (2 * S + 1), Nat.mod_lt _ (by omega)⟩

/-- Unpack a `RACfgCompact k State S` checkpoint back into an unbounded `RACfg k State`. -/
@[expose] def RACfgCompact.unpack {k : ℕ} {State : Type} {S : ℕ} (cp : RACfgCompact k State S) :
    RACfg k State where
  state := cp.state
  accept := cp.accept
  idxTape z :=
    if hz : -(S : ℤ) ≤ z ∧ z ≤ (S : ℤ) then
      cp.idxCells ⟨Int.toNat (z + (S : ℤ)), by omega⟩
    else none
  idxPos := (cp.idxPos.val : ℤ) - (S : ℤ)
  idxHi := cp.idxHi.val
  workTape i z :=
    if hz : -(S : ℤ) ≤ z ∧ z ≤ (S : ℤ) then
      cp.workCells i ⟨Int.toNat (z + (S : ℤ)), by omega⟩
    else none
  workPos i := ((cp.workPos i).val : ℤ) - (S : ℤ)

theorem RACfgCompact.unpack_pack {k : ℕ} {State : Type} {S : ℕ} {c : RACfg k State}
    (hw : c.WithinWindow S) :
    (c.pack S).unpack = c := by
  rcases c with ⟨st, acc, it, ip, ihi, wt, wp⟩
  rcases hw with ⟨hip, hhi, hit, hwp, hwt⟩
  dsimp only [RACfg.pack, RACfgCompact.unpack] at hip hhi hit hwp hwt ⊢
  congr 1
  · funext z
    split_ifs with hz
    · rw [show ((Int.toNat (z + (S : ℤ)) : ℤ) - (S : ℤ)) = z from by omega]
    · exact (hit z (by omega)).symm
  · have hlt : Int.toNat (ip + (S : ℤ)) < 2 * S + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · exact Nat.mod_eq_of_lt (by omega)
  · funext i z
    split_ifs with hz
    · rw [show ((Int.toNat (z + (S : ℤ)) : ℤ) - (S : ℤ)) = z from by omega]
    · exact (hwt i z (by omega)).symm
  · funext i
    have hwi := hwp i
    have hlt : Int.toNat (wp i + (S : ℤ)) < 2 * S + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

private theorem runBlock_eq_runCoins {k : ℕ} {State : Type} (M : RAATM k State)
    (input : List Bool) (b : ℕ) (c : RACfg k State) (blk : Fin b → Bool) :
    runBlock (fun cfg coin => M.step input coin cfg) c blk =
      M.runCoins input c (List.ofFn blk) := by
  induction b generalizing c with
  | zero => simp [runBlock, List.ofFn_zero, RAATM.runCoins]
  | succ b ih =>
    rw [runBlock, List.ofFn_succ, RAATM.runCoins]
    exact ih (M.step input (blk 0) c) (fun i => blk i.succ)

/-- **Concrete `RAATM` `NTISP` checkpoint speedup reduction**: any `m * b`-step nondeterministic
`RAATM` computation keeping all reachable configurations in tape window `[-S, S]` reduces
equivalently (`↔`) to an existential guess of `m + 1` compact checkpoints `RACfgCompact k State S`
followed by a universal check over `j : Fin m` of a `b`-bit local existential extension (`Σ₃`). -/
theorem RAATM_ntisp_block_simulation {k : ℕ} {State : Type} (M : RAATM k State)
    (hphase : RAATM.HasPhaseBound 1 false M) (input : List Bool) (S m b : ℕ) (hb : 0 < b)
    (hwin : ∀ bs : List Bool, bs.length ≤ m * b →
      (M.runCoins input (RACfg.init M.q₀) bs).WithinWindow S) :
    M.AcceptsWithin input (m * b) (RACfg.init M.q₀) ↔
      ∃ ck : Fin (m + 1) → RACfgCompact k State S,
        (ck 0).unpack = RACfg.init M.q₀ ∧
          ((ck ⟨m, Nat.lt_succ_self m⟩).unpack.state = none ∧
            (ck ⟨m, Nat.lt_succ_self m⟩).unpack.accept = true) ∧
          ∀ j : Fin m, ∃ blk : Fin b → Bool,
            runBlock (fun c coin => M.step input coin c)
              (ck ⟨j.val, by omega⟩).unpack blk =
                (ck ⟨j.val + 1, by omega⟩).unpack := by
  have huniv := hasPhaseBound_one_univ_false hphase
  let step : RACfg k State → Bool → RACfg k State := fun c coin => M.step input coin c
  let acc : RACfg k State → Bool := fun c => c.state.isNone && c.accept
  have hacc_iff (c : RACfg k State) : acc c = true ↔ c.state = none ∧ c.accept = true := by
    cases hst_c : c.state <;> simp [acc, hst_c]
  rw [acceptsWithin_existential_iff M huniv]
  constructor
  · rintro ⟨bs, hlen, hst, hacc⟩
    let w : Fin (m * b) → Bool := fun p => bs[p.val]'(by omega)
    have hblock_win : runBlock step (RACfg.init M.q₀) w =
        M.runCoins input (RACfg.init M.q₀) bs := by
      rw [runBlock_eq_runCoins]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro i hi1 hi2
      simp [w]
    have hacc_block : acc (runBlock step (RACfg.init M.q₀) w) = true := by
      rw [hblock_win]
      exact (hacc_iff _).mpr ⟨hst, hacc⟩
    obtain ⟨ck_raw, ⟨h0, hm⟩, hsteps⟩ :=
      (ntmBlockSimulation step acc (RACfg.init M.q₀) m b hb).mp ⟨w, hacc_block⟩
    have hraw_win : ∀ j : Fin (m + 1), (ck_raw j).WithinWindow S := by
      intro j
      clear hacc_block hblock_win hm hst hacc hlen bs w
      have hreach : ∀ r : ℕ, (hr : r ≤ m) →
          ∃ pref : List Bool, pref.length = r * b ∧
            M.runCoins input (RACfg.init M.q₀) pref = ck_raw ⟨r, by omega⟩ := by
        intro r
        induction r with
        | zero =>
          intro _
          exact ⟨[], by simp, by simp [RAATM.runCoins, h0]⟩
        | succ r ihr =>
          intro hr
          obtain ⟨pref, hplen, hpeq⟩ := ihr (by omega)
          obtain ⟨blk, hblk⟩ := hsteps ⟨r, by omega⟩
          refine ⟨pref ++ List.ofFn blk, by simp [hplen]; ring, ?_⟩
          rw [RAATM.runCoins_append, hpeq, ← runBlock_eq_runCoins]
          exact hblk
      obtain ⟨pref, hplen, hpeq⟩ := hreach j.val (by omega)
      rw [← hpeq]
      apply hwin pref
      rw [hplen]
      exact Nat.mul_le_mul_right b (Nat.lt_succ_iff.mp j.2)
    refine ⟨fun j => (ck_raw j).pack S, ?_, ?_, ?_⟩
    · rw [RACfgCompact.unpack_pack (hraw_win 0), h0]
    · rw [RACfgCompact.unpack_pack (hraw_win ⟨m, Nat.lt_succ_self m⟩)]
      exact (hacc_iff _).mp hm
    · intro j
      obtain ⟨blk, hblk⟩ := hsteps j
      refine ⟨blk, ?_⟩
      rw [RACfgCompact.unpack_pack (hraw_win ⟨j.val, by omega⟩),
        RACfgCompact.unpack_pack (hraw_win ⟨j.val + 1, by omega⟩)]
      exact hblk
  · rintro ⟨ck, h0, hm, hsteps⟩
    obtain ⟨w, hw⟩ := (ntmBlockSimulation step acc (RACfg.init M.q₀) m b hb).mpr
      ⟨fun j => (ck j).unpack, ⟨h0, (hacc_iff _).mpr hm⟩, hsteps⟩
    refine ⟨List.ofFn w, by simp, ?_⟩
    have hbw : M.runCoins input (RACfg.init M.q₀) (List.ofFn w) =
        runBlock step (RACfg.init M.q₀) w := (runBlock_eq_runCoins M input (m * b) _ w).symm
    rw [hbw]
    exact (hacc_iff _).mp hw

end CheckpointSpeedups

end Cslib.Complexity

