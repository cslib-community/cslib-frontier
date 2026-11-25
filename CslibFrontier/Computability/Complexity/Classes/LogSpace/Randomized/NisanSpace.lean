/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.Nisan
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NisanGenerator
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.CoinReplay
import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# `BPL ⊆ DSPACE(log² n)`

Nisan's theorem [Nisan1992]: a language decided by a fair-coin machine in logarithmic space with
bounded two-sided error (`Cslib.Complexity.BPL`) is decided deterministically within space
`O(log² n)` (`Cslib.Complexity.BPL_subset_DSPACE_log2_sq`).

The deterministic machine enumerates the seeds of Nisan's generator on bit strings, packed in the
naturals below `2 ^ s` (`Cslib.Crypto.PRG.Nisan.seedOfNat`), where `s = O(log² n)` is the seed
length of `Cslib.Complexity.exists_acceptNisanSeeds_of_mem_BPL` for inputs of length `n`. For each
seed it replays the fair-coin machine on the generated coins
(`Turing.MultiTapePTM.replayCoins_inSpace_context`), recomputing every coin from the seed in space
linear in the seed (`Cslib.Crypto.PRG.Nisan.computableInSpace_bitGeneratorNat`), and it counts the
accepting seeds (`Turing.MultiTapeTM.ComputableInSpace.majorityWith`). The packed seeds enumerate
the seeds of the generator (`Cslib.Complexity.countP_range_bitGeneratorNat_accepts`), so the count
is `Turing.MultiTapePTM.acceptNisanSeeds`, which exceeds half of the seeds exactly on members.

## Main results

* `Cslib.Complexity.countP_range_bitGeneratorNat_accepts`: the packed seeds on which the replay
  accepts are counted by `Turing.MultiTapePTM.acceptNisanSeeds`.
* `Cslib.Complexity.BPL_subset_DSPACE_log2_sq`: `BPL ⊆ DSPACE(log² n)`.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- **Counting accepted packed seeds**: the naturals below `2 ^ (n + r (3 n - 1))` on whose packed
seed (`Cslib.Crypto.PRG.Nisan.seedOfNat`) the machine accepts the `2 ^ r n` output bits of
`Cslib.Crypto.PRG.Nisan.bitGeneratorNat`, read as its coins, are as many as the seeds of
`Cslib.Crypto.PRG.Nisan.bitGenerator n r` it accepts. -/
theorem countP_range_bitGeneratorNat_accepts {k : ℕ} {State : Type}
    (M : MultiTapePTM k Bool State) (input : List Bool) (n r : ℕ) :
    ((List.range (2 ^ (n + r * (3 * n - 1)))).countP fun z => decide
      ((M.stepCoins (List.ofFn fun j : Fin (2 ^ r * n) => Crypto.PRG.Nisan.bitGeneratorNat n r z j)
          (M.toNTM.initCfg input)).Halted ∧
        (M.stepCoins
          (List.ofFn fun j : Fin (2 ^ r * n) => Crypto.PRG.Nisan.bitGeneratorNat n r z j)
          (M.toNTM.initCfg input)).output = [true])) =
      M.acceptNisanSeeds input n r := by
  classical
  have hfun (z : ℕ) :
      (List.ofFn fun j : Fin (2 ^ r * n) => Crypto.PRG.Nisan.bitGeneratorNat n r z j) =
        List.ofFn (Crypto.PRG.Nisan.bitGenerator n r (Crypto.PRG.Nisan.seedOfNat n r z)) :=
    congrArg List.ofFn (funext fun j => Crypto.PRG.Nisan.bitGeneratorNat_eq n r z j j.isLt)
  have h := Crypto.PRG.Nisan.countP_range_seedOfNat n r fun s => decide
    ((M.stepCoins (List.ofFn (Crypto.PRG.Nisan.bitGenerator n r s))
        (M.toNTM.initCfg input)).Halted ∧
      (M.stepCoins (List.ofFn (Crypto.PRG.Nisan.bitGenerator n r s))
        (M.toNTM.initCfg input)).output = [true])
  simp only [hfun]
  refine h.trans ?_
  rw [MultiTapePTM.acceptNisanSeeds]
  exact congrArg Finset.card (Finset.filter_congr fun s _ => decide_eq_true_iff)

/-! ### The parameters in `O(log² m)` space -/

/-- `⌊log₂⌋` of the length of a word, within logarithmic space. -/
private theorem log2_length_inSpace :
    ComputableInSpace (fun w : List Bool => Nat.log2 w.length) encBits encNat
      fun w => Nat.log2 (encBits w).length :=
  (ComputableInLogSpace.unaryToBinary
      (ComputableInLogSpace.unaryLog2 ComputableInLogSpace.bitsLength)).inSpace_of_length_log
    ⟨1, fun w => by
      simpa only [one_mul, encBits_apply] using
        length_encNat_le_log2 (Nat.log2_le_self w.length)⟩

/-- The budget `(log₂ m + 1)²` on words of length `m`. -/
private abbrev logSqBudget (w : List Bool) : ℕ := (Nat.log2 w.length + 1) ^ 2

private theorem log2_le_logSqBudget (w : List Bool) : Nat.log2 w.length ≤ logSqBudget w :=
  (Nat.le_succ _).trans (Nat.le_self_pow two_ne_zero _)

private theorem log2_budget :
    ComputableInSpace (fun w : List Bool => Nat.log2 w.length) encBits encNat logSqBudget :=
  log2_length_inSpace.mono_le fun w => by
    rw [encBits_apply]
    exact log2_le_logSqBudget w

/-- The number of hash seeds `r = d (log₂ m + 2) + 1` on inputs of length `m`. -/
private abbrev nisanHashSeeds (d : ℕ) (w : List Bool) : ℕ := d * (Nat.log2 w.length + 2) + 1

/-- The block length `n = 2 (2 r + 3)`. -/
private abbrev nisanBlockLen (d : ℕ) (w : List Bool) : ℕ := 2 * (2 * nisanHashSeeds d w + 3)

/-- The seed length `n + r (3 n - 1)`. -/
private abbrev nisanSeedLen (d : ℕ) (w : List Bool) : ℕ :=
  nisanBlockLen d w + nisanHashSeeds d w * (3 * nisanBlockLen d w - 1)

private theorem hashSeeds_budget (d : ℕ) :
    ComputableInSpace (nisanHashSeeds d) encBits encNat logSqBudget :=
  ComputableInSpace.budget_natAdd
    (ComputableInSpace.budget_natMul (ComputableInSpace.budget_const d)
      (ComputableInSpace.budget_natAdd log2_budget (ComputableInSpace.budget_const 2)))
    (ComputableInSpace.budget_const 1)

private theorem blockLen_budget (d : ℕ) :
    ComputableInSpace (nisanBlockLen d) encBits encNat logSqBudget :=
  ComputableInSpace.budget_natMul (ComputableInSpace.budget_const 2)
    (ComputableInSpace.budget_natAdd
      (ComputableInSpace.budget_natMul (ComputableInSpace.budget_const 2) (hashSeeds_budget d))
      (ComputableInSpace.budget_const 3))

private theorem seedLen_budget (d : ℕ) :
    ComputableInSpace (nisanSeedLen d) encBits encNat logSqBudget :=
  ComputableInSpace.budget_natAdd (blockLen_budget d)
    (ComputableInSpace.budget_natMul (hashSeeds_budget d)
      (ComputableInSpace.budget_natSub
        (ComputableInSpace.budget_natMul (ComputableInSpace.budget_const 3) (blockLen_budget d))
        (ComputableInSpace.budget_const 1)))

/-- The number of coins `2 ^ r n`. -/
private theorem coinCount_budget (d : ℕ) :
    ComputableInSpace (fun w => 2 ^ nisanHashSeeds d w * nisanBlockLen d w) encBits encNat
      logSqBudget :=
  ComputableInSpace.budget_natMul
    (ComputableInSpace.budget_natPow_variable (ComputableInSpace.budget_const 2)
      (hashSeeds_budget d) (.of_le_linear (6 * d + 6) 8 fun w => by
        have h2 : (encNat 2).length = 2 := rfl
        have hlen := length_encNat_le_log2 (le_refl (nisanHashSeeds d w))
        have hlog := Nat.log2_le_self (nisanHashSeeds d w)
        have hsq := Nat.le_self_pow two_ne_zero (Nat.log2 w.length + 1)
        simp only [logSqBudget, h2] at hsq ⊢
        nlinarith))
    (blockLen_budget d)

/-- The number of seeds `2 ^ s`, given the bound on the seed length `s`. -/
private theorem two_pow_seedLen_budget {α : Type} {enc : α ↪ List Bool} (d : ℕ)
    (hs : ∀ a, nisanSeedLen d (enc a) ≤ 39 * (2 * d + 1) ^ 2 * (Nat.log2 (enc a).length + 1) ^ 2) :
    ComputableInSpace (fun a => 2 ^ nisanSeedLen d (enc a)) enc encNat
      fun a => logSqBudget (enc a) :=
  ComputableInSpace.budget_natPow_variable (ComputableInSpace.budget_const 2)
    ((seedLen_budget d).of_encIn_eq enc fun a => (encBits_apply (enc a)).symm)
    (.of_le_linear (4 * 39 * (2 * d + 1) ^ 2) 4 fun a => by
      have h2 : (encNat 2).length = 2 := rfl
      have hlen := length_encNat_le_log2 (le_refl (nisanSeedLen d (enc a)))
      have hlog := Nat.log2_le_self (nisanSeedLen d (enc a))
      have hsa := hs a
      simp only [logSqBudget, h2] at hsa ⊢
      nlinarith)

/-- A budget for a packed seed `z` and an input `a` of length `m` that covers the logarithm of
the length of the encoded pair: the seed twice and `(log₂ m + 1)²`. -/
private abbrev replayBudget {α : Type} (enc : α ↪ List Bool) (b : ℕ × α) : ℕ :=
  2 * (encNat b.1).length + logSqBudget (enc b.2) + 2

private theorem log2_le_replayBudget {α : Type} (enc : α ↪ List Bool) (b : ℕ × α) :
    Nat.log2 (encPair encNat enc b).length ≤ replayBudget enc b :=
  (log2_length_encPair_le encNat enc b).trans (by
    have := log2_le_logSqBudget (enc b.2)
    simp only [replayBudget]
    omega)

/-- A function of the input computed within `(log₂ m + 1)²`, with a packed seed stored first. -/
private theorem ofInput_seedBudget {α β : Type} {enc : α ↪ List Bool} {encC : β ↪ List Bool}
    {g : List Bool → β} (hg : ComputableInSpace g encBits encC logSqBudget) :
    ComputableInSpace (fun b : ℕ × α => g (enc b.2)) (encPair encNat enc) encC
      fun b => (encNat b.1).length + logSqBudget (enc b.2) :=
  (hg.of_encIn_eq enc fun a => (encBits_apply (enc a)).symm).comp_logSpace_context
    (ComputableInLogSpace.snd encNat enc) (.of_le fun _ => Nat.le_add_left _ _)
    fun a => log2_le_logSqBudget (enc a)

/-- A function of the input computed within `(log₂ m + 1)²`, with a coin index stored first. -/
private theorem ofInput_coinBudget {α β : Type} {enc : α ↪ List Bool} {encC : β ↪ List Bool}
    {g : List Bool → β} (hg : ComputableInSpace g encBits encC logSqBudget) :
    ComputableInSpace (fun q : ℕ × (ℕ × α) => g (enc q.2.2))
      (encPair encNat (encPair encNat enc)) encC
      fun q => (encNat q.1).length + replayBudget enc q.2 :=
  (hg.of_encIn_eq enc fun a => (encBits_apply (enc a)).symm).comp_logSpace_context
    ((ComputableInLogSpace.snd encNat enc).comp' (ComputableInLogSpace.snd encNat
      (encPair encNat enc)))
    (.of_le fun q => by simp only [replayBudget]; omega) (log2_le_replayBudget enc)

/-- **A coin of Nisan's generator, on a packed seed and the input**: bit `j` of the generator with
the parameters of the input `a` on the packed seed `z`, with `j` stored. -/
private theorem coin_inSpace {α : Type} {enc : α ↪ List Bool} (d : ℕ) :
    ComputableInSpace (fun q : ℕ × (ℕ × α) => Crypto.PRG.Nisan.bitGeneratorNat
        (nisanBlockLen d (enc q.2.2)) (nisanHashSeeds d (enc q.2.2)) q.2.1 q.1)
      (encPair encNat (encPair encNat enc)) encBool
      fun q => (encNat q.1).length + ((encNat q.2.1).length + logSqBudget (enc q.2.2)) := by
  have hj : ComputableInSpace (fun q : ℕ × (ℕ × α) => q.1) (encPair encNat (encPair encNat enc))
      encNat fun q => (encNat q.1).length + replayBudget enc q.2 :=
    ((ComputableInLogSpace.fst encNat (encPair encNat enc)).inSpace_context
    (.of_le fun _ => Nat.le_add_right _ _)).mono_le fun q => by
      have := log2_le_replayBudget enc q.2
      omega
  have hz := (ComputableInSpace.budget_id (enc := encNat) (.refl _)).comp_logSpace_context
    ((ComputableInLogSpace.fst encNat enc).comp' (ComputableInLogSpace.snd encNat
      (encPair encNat enc)))
    (.of_le fun q => by simp only [replayBudget]; omega) (log2_le_replayBudget enc)
  have h := ComputableInSpace.budget_comp_linear
    Crypto.PRG.Nisan.computableInSpace_bitGeneratorNat
    (Crypto.PRG.Nisan.encNisanBitArgs_mk_budget (ofInput_coinBudget (blockLen_budget d))
      (ofInput_coinBudget (hashSeeds_budget d)) hz hj)
  exact h.weaken (.of_le_linear 2 2 fun q => by simp only [replayBudget]; omega)

/-- **`BPL ⊆ DSPACE(log² n)`** [Nisan1992]: every language in `Cslib.Complexity.BPL`, decided by
a fair-coin machine that on inputs of length `n` uses `O(log n)` work-tape cells and halts on every
branch, accepting members on at least two thirds of the coin strings and non-members on at most one
third, is in `Cslib.Complexity.DSPACE` for the bound `log₂ n ^ 2`, that is decided by a
deterministic machine within `c₁ log₂² n + c₂` work-tape cells. The constants `c₁` and `c₂` of
`DSPACE` absorb the space `(log₂ n + 1)² + log₂ n` of the construction, also on inputs of length
`0` and `1`. The machine counts the packed seeds of Nisan's generator on which the replay of the
fair-coin machine accepts and compares the count with half of the seeds. -/
theorem BPL_subset_DSPACE_log2_sq {α : Type} {enc : α ↪ List Bool} :
    BPL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 := by
  intro A hA
  obtain ⟨k, State, hfin, M, c, d, hs, hM⟩ := exists_acceptNisanSeeds_of_mem_BPL hA
  have hrep := M.replayCoins_inSpace_context c hs (ofInput_seedBudget (coinCount_budget d))
    (coin_inSpace d) fun a => log2_le_logSqBudget (enc a)
  have hf := (two_pow_seedLen_budget d fun a => (hM a _ _ rfl rfl).1).majorityWith hrep
  refine DSPACE_mono_of_le_mul_add (C := 5) (s₁ := fun n => (Nat.log2 n + 1) ^ 2 + Nat.log2 n)
    (fun n => by nlinarith) ?_
  convert setOf_mem_DSPACE_of_computableInSpace hf
    (s := fun n => (Nat.log2 n + 1) ^ 2 + Nat.log2 n) fun a => le_rfl using 1
  ext a
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq]
  rw [countP_range_bitGeneratorNat_accepts]
  obtain ⟨-, hmem, hnot⟩ := hM a _ _ rfl rfl
  exact ⟨hmem, fun h => by_contra fun ha => absurd h (Nat.lt_asymm (hnot ha))⟩

end Cslib.Complexity
