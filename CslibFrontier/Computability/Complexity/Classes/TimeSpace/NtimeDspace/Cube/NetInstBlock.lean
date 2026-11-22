/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.NetTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.NetInst
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Network access for the block networks (Lemma 2.2)

For a fair-coin machine `M : MultiTapePTM k Bool State` with `e : State ≃ Fin s`, an input `w`, a
clock `τ` and a schedule number `σ`, the block network `G_{w,τ,σ}` of Lemma 2.2 is
`blockNetworkOf M e (w, τ, σ)` (Complexitylib); from `τ ≥ 2` on it is rows-first bipartite
(`rowsFirst_of_two_le`), and `blockNet M e w τ σ hd = EdgeNet.ofExplicit ℤ _ _ hd` is the integer
edge network on its vertices, with value the contraction (`blockNet_value`).

The network terms `blockNetT M e nT τT σT` read it through the interface `NetT` of
`NetTerms.lean`, from terms `nT` for the input length, `τT` for the clock and `σT` for the
schedule: they are the terms `clkEdgesT`, `clkVerticesT`, `edgeUT`, `edgeWT`, `clkArityT`,
`clkPortT` and `clkWeightT` of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/NetTerm.lean`. The value
contract `NetAcc` comes from the
`denote_*` lemmas there (for `ZMod 0 = ℤ`, the table entries are the exact weights), the tier
contract `NetTiers` from `tm_clkAccessors` and `tm_ends1`, at every budget
`L ≥ blockBudget k s · (⌊log₂ τ⌋ + 1)` (`block_facts` checks the numeric hypotheses of those
lemmas). The schedule term must have tier `1`, so `σ < 2^L`: a schedule number has `O(τ / log τ)`
bits, so budgets of order `SqrtLog τ` contain it.

## Main definitions

* `blockNet`: the block network as an integer edge network; `blockNetT`: its network terms.
* `blockBudget k s`: the constant of the budget.

## Main results

* `blockNet_value`: the value of `blockNet` is the contraction of the block network.
* `blockNet_acc`, `blockNet_evalNonneg`, `blockNet_tiers`: the contracts of `NetTerms.lean`.
* `block_facts`: the numeric hypotheses of `NetTerm.tm_clkAccessors` at the budget.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross NtimeDspace.Cross.NetTerm
  _root_.Turing _root_.Turing.MultiTapePTM Cslib.Complexity.CountingSimulation
      Cslib.Circuits.Frontier

/-! ### Numeric facts at the budget -/

section Facts

variable {k s : ℕ}

/-- `N ≤ 4 (3k+1)(s+k+4) · τ` at every clock `τ ≥ 2` (copied from WalkFacts,
`edgesN_le_mul`, which belongs to the earlier route). -/
theorem edgesN_le_mul' {τ : ℕ} (hτ : 2 ≤ τ) : edgesN k s τ ≤ 4 * (3 * k + 1) * (s + k + 4) * τ := by
  have e : edgesN k s τ = 2 * (3 * k + 1) * (s + k + 4) * paddedTime τ := by
    unfold edgesN paddedTime MultiTapePTM.letterBits; ring
  rw [e]
  have h := paddedTime_add_one_le hτ
  calc 2 * (3 * k + 1) * (s + k + 4) * paddedTime τ ≤ 2 * (3 * k + 1) * (s + k + 4) * (2 * τ) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 4 * (3 * k + 1) * (s + k + 4) * τ := by ring

/-- `3^m ≤ 2^(2m)`. -/
theorem pow3_le' (m : ℕ) : 3 ^ m ≤ 2 ^ (2 * m) := by
  calc 3 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ (2 * m) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

variable (k s) in
/-- **The budget constant of the block networks**: the accessors of `blockNetT` have the tiers of
`NetTiers` at every budget `L ≥ blockBudget k s · (⌊log₂ τ⌋ + 1)`. -/
def blockBudget : ℕ :=
  LocalSim.width k * (s + 31) + 3 * (4 * (3 * k + 1) * (s + k + 4)).log2 +
    (LocalSim.keyCount k s * k + LocalSim.keyCount k s + LocalSim.width k + 3 ^ k) +
    6 * (3 * k + 1) * (s + k + 4) + 3 * (s + k + 4) + 3 * s + 3 * k + 4 * k + s + 128

/-- **The numeric hypotheses of `tm_clkAccessors`** at the clock `τ ≥ 2` and the input `w`
(`|w| ≤ τ`), at every budget `L ≥ blockBudget k s · (⌊log₂ τ⌋ + 1)`; the last is the bound
`6 (3k+1)(s+k+4) ⌊log₂ τ⌋` on the degrees (admissibility) below `L`. -/
theorem block_facts {w : List Bool} {τ L : ℕ} (hτ : 2 ≤ τ) (hw : w.length ≤ τ)
    (hL : blockBudget k s * (τ.log2 + 1) ≤ L) :
    16 ≤ L ∧ τ < 2 ^ L ∧ w.length < 2 ^ L ∧ edgesN k s τ ^ 3 < 2 ^ L ∧
      4 * k + s + 100 < 2 ^ L ∧
      LocalSim.keyCount k s * k + LocalSim.keyCount k s + LocalSim.width k + 3 ^ k < 2 ^ L ∧
      LocalSim.radix (blockLength τ) w.length s ^ LocalSim.width k < 2 ^ L ∧
      3 ^ (3 * blockLength τ) < 2 ^ L ∧ (s + 1) * (blockLength τ ^ (k + 1) * 3) < 2 ^ L ∧
      letterBits k s (blockLength τ) < L ∧ 6 * (3 * k + 1) * (s + k + 4) * Nat.log 2 τ < L := by
  -- `omega` does not know that `3 ^ k` is nonnegative after casting, so name it
  obtain ⟨P, hP⟩ : ∃ P, 3 ^ k = P := ⟨_, rfl⟩
  have c1 : 128 ≤ blockBudget k s := by simp only [blockBudget, hP]; omega
  have cE : 3 * (4 * (3 * k + 1) * (s + k + 4)).log2 + 8 ≤ blockBudget k s := by
    simp only [blockBudget, hP]; omega
  have cK : LocalSim.keyCount k s * k + LocalSim.keyCount k s + LocalSim.width k + 3 ^ k + 1 ≤
      blockBudget k s := by simp only [blockBudget, hP]; omega
  have cC : 4 * k + s + 101 ≤ blockBudget k s := by simp only [blockBudget, hP]; omega
  have cR : LocalSim.width k * (s + 31) ≤ blockBudget k s := by simp only [blockBudget, hP]; omega
  have c8 : 3 * s + 3 * k + 6 ≤ blockBudget k s := by simp only [blockBudget, hP]; omega
  have c9 : 3 * (s + k + 4) + 1 ≤ blockBudget k s := by simp only [blockBudget, hP]; omega
  have cD : 6 * (3 * k + 1) * (s + k + 4) + 1 ≤ blockBudget k
      s := by simp only [blockBudget, hP]; omega
  generalize blockBudget k s = A at *
  set ℓ := τ.log2 with hℓ
  have hlog : Nat.log 2 τ = ℓ := (Nat.log2_eq_log_two).symm
  have hA' : ∀ a ≤ A, a * (ℓ + 1) ≤ L := fun a ha => (Nat.mul_le_mul_right _ ha).trans hL
  have hAL : A ≤ L := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hL
  have hℓL : ℓ + 1 ≤ L := by have := hA' 1 (by omega); omega
  have hτ2 : τ < 2 ^ (ℓ + 1) := Nat.lt_log2_self
  have hb : blockLength τ ≤ 3 * ℓ := by
    rw [← hlog]; exact Nat.clog_two_add_two_le_three_mul_log_two hτ
  have hb1 : 1 ≤ blockLength τ := one_le_blockLength τ
  have hτL : τ < 2 ^ L := hτ2.trans_le (Nat.pow_le_pow_right (by norm_num) hℓL)
  have hlarge : ∀ {X : ℕ}, X < A → X < 2 ^ L := fun h =>
    (h.trans_le hAL).trans Nat.lt_two_pow_self
  refine
      ⟨by omega, hτL, lt_of_le_of_lt hw hτL, ?_, hlarge (by omega), hlarge (by omega), ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the cube of the number of edges
    generalize hKdef : 4 * (3 * k + 1) * (s + k + 4) = K at cE
    have hK2 : K < 2 ^ (K.log2 + 1) := Nat.lt_log2_self
    have hE : edgesN k s τ ≤ 2 ^ (K.log2 + ℓ + 2) := by
      calc edgesN k s τ ≤ K * τ := hKdef ▸ edgesN_le_mul' hτ
        _ ≤ 2 ^ (K.log2 + 1) * 2 ^ (ℓ + 1) := Nat.mul_le_mul hK2.le hτ2.le
        _ = 2 ^ (K.log2 + ℓ + 2) := by rw [← pow_add]; congr 1; omega
    have h3 : edgesN k s τ ^ 3 ≤ 2 ^ (3 * (K.log2 + ℓ + 2)) := by
      rw [pow_mul']; exact Nat.pow_le_pow_left hE 3
    have hle : 3 * (K.log2 + ℓ + 2) + 1 ≤ L := by
      have h := hA' _ cE
      nlinarith [Nat.zero_le (K.log2 * ℓ)]
    calc edgesN k s τ ^ 3 ≤ 2 ^ (3 * (K.log2 + ℓ + 2)) := h3
      _ < 2 ^ (3 * (K.log2 + ℓ + 2) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hle
  · -- the radix
    set b := blockLength τ with hb_def
    set n := w.length with hn_def
    set E := 8 * b + ℓ + s + 4 with hE
    have h1 : 3 ^ (4 * b) < 2 ^ E + 1 := by
      have := pow3_le' (4 * b)
      have : 2 ^ (2 * (4 * b)) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : n < 2 ^ E := by
      have : 2 ^ (ℓ + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3 : s + 3 < 2 ^ E := by
      have : 2 ^ (s + 3) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.lt_two_pow_self (n := s + 3)
      omega
    have h4 : 2 ^ (E + 2) = 4 * 2 ^ E := by rw [pow_add]; ring
    have hrad : LocalSim.radix b n s < 2 ^ (E + 2) := by unfold LocalSim.radix; omega
    have hw0 : LocalSim.width k ≠ 0 := by unfold LocalSim.width; omega
    have hE2 : E + 2 ≤ (s + 31) * (ℓ + 1) := by
      have : (s + 31) * (ℓ + 1) = s * ℓ + 31 * ℓ + s + 31 := by ring
      omega
    have hEL : (E + 2) * LocalSim.width k ≤ L :=
      calc (E + 2) * LocalSim.width k ≤ (s + 31) * (ℓ + 1) * LocalSim.width k :=
            Nat.mul_le_mul_right _ hE2
        _ = (LocalSim.width k * (s + 31)) * (ℓ + 1) := by ring
        _ ≤ L := hA' _ cR
    calc LocalSim.radix b n s ^ LocalSim.width k < (2 ^ (E + 2)) ^ LocalSim.width k :=
          Nat.pow_lt_pow_left hrad hw0
      _ = 2 ^ ((E + 2) * LocalSim.width k) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hEL
  · -- `3^(3b)`
    have h := hA' 19 (by omega)
    exact (pow3_le' (3 * blockLength τ)).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  · -- the cell values
    set b := blockLength τ with hb_def
    have hbk : b ^ (k + 1) ≤ 2 ^ (b * (k + 1)) :=
      (Nat.pow_le_pow_left (Nat.lt_two_pow_self).le (k + 1)).trans_eq (pow_mul _ _ _).symm
    have hb1' : 1 ≤ b ^ (k + 1) := Nat.one_le_pow _ _ hb1
    have h33 : (s + 1) * 3 < 2 ^ (3 * s + 3) := by
      have := Nat.lt_two_pow_self (n := 3 * s + 3); omega
    have hm1 : (s + 1) * 3 * b ^ (k + 1) < 2 ^ (3 * s + 3) * 2 ^ (b * (k + 1)) :=
      calc (s + 1) * 3 * b ^ (k + 1) < 2 ^ (3 * s + 3) * b ^ (k + 1) :=
            Nat.mul_lt_mul_of_pos_right h33 hb1'
        _ ≤ 2 ^ (3 * s + 3) * 2 ^ (b * (k + 1)) := Nat.mul_le_mul_left _ hbk
    rw [← pow_add] at hm1
    have hle : 3 * s + 3 + b * (k + 1) ≤ L := by
      have h := hA' _ c8
      nlinarith [Nat.mul_le_mul_right (k + 1) hb, Nat.zero_le (s * ℓ), Nat.zero_le (k * ℓ)]
    calc (s + 1) * (b ^ (k + 1) * 3) = (s + 1) * 3 * b ^ (k + 1) := by ring
      _ < 2 ^ (3 * s + 3 + b * (k + 1)) := hm1
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hle
  · -- the letter bits
    unfold MultiTapePTM.letterBits
    have h := hA' _ c9
    nlinarith [Nat.mul_le_mul_left (s + k + 4) hb]
  · -- the degrees
    rw [hlog]
    generalize 6 * (3 * k + 1) * (s + k + 4) = Cd at cD ⊢
    have h := hA' _ cD
    nlinarith

end Facts

/-! ### The block network and its terms -/

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

omit [DecidableEq State] in
/-- From the clock `τ = 2` on, the block network is rows-first bipartite. -/
theorem rowsFirst_of_two_le (w : List Bool) {τ : ℕ} (σ : ℕ) (hτ : 2 ≤ τ) :
    RowsFirst machine e w τ σ :=
  (explicitAdmissible_blockNetworkOf machine e w σ hτ).1

/-- **The block network `G_{w,τ,σ}` as an integer edge network** (Lemma 2.2): the edge network
of `blockNetworkOf machine e (w, τ, σ)` with its table entries in `ℤ`. -/
noncomputable abbrev blockNet (w : List Bool) (τ σ : ℕ) (hd : RowsFirst machine e w τ σ) :
    EdgeNet ℤ (Fin (blockNetworkOf machine e (w, τ, σ)).2.vertices.length) :=
  EdgeNet.ofExplicit ℤ _ _ hd

/-- **The network terms of the block networks**, from terms for the input length `nT`, the clock
`τT` and the schedule `σT`. -/
def blockNetT (nT τT σT : Term) : NetT where
  MT := clkEdgesT k s τT
  VT := clkVerticesT k s τT
  uT := edgeUT k s τT σT
  wT := edgeWT k s τT
  degT := clkArityT k s τT σT
  portT := clkPortT k s τT σT
  evalT := clkWeightT k s machine e nT τT σT

variable {machine e} {w : List Bool} {τ σ L : ℕ} {env : List ℕ} {nT τT σT : Term}

omit [DecidableEq State] in
/-- **The value of the block network** is the contraction of `G_{w,τ,σ}`. -/
theorem blockNet_value (hd : RowsFirst machine e w τ σ) :
    (blockNet machine e w τ σ hd).value =
      ((blockNetworkOf machine e (w, τ, σ)).2.contraction : ℤ) :=
  EdgeNet.value_ofExplicit ℤ _ _ _

omit [DecidableEq State] in
theorem blockNet_M (hd : RowsFirst machine e w τ σ) :
    (blockNet machine e w τ σ hd).M = edgesN k s τ :=
  M_blockEdgeNet (p := 0) hd

omit [DecidableEq State] in
/-- The table entries in `ℤ` are those in `ZMod 0`. -/
theorem blockNet_eval_toNat (hd : RowsFirst machine e w τ σ)
    (v : Fin (blockNetworkOf machine e (w, τ, σ)).2.vertices.length) (bs : List Bool) :
    ((blockNet machine e w τ σ hd).eval v bs).toNat =
      ((blockEdgeNet machine e 0 w τ σ hd).eval v bs).val := by
  change ((ExplicitTensorNetwork.entry _ bs : ℕ) : ℤ).toNat =
    ((ExplicitTensorNetwork.entry _ bs : ℕ) : ZMod 0).val
  rw [Int.toNat_natCast, ZMod.val_natCast, Nat.mod_zero]

omit [DecidableEq State] in
/-- The table entries are nonnegative. -/
theorem blockNet_evalNonneg (hd : RowsFirst machine e w τ σ) :
    EvalNonneg (blockNet machine e w τ σ hd) := fun v x _ => by
  change (0 : ℤ) ≤ ((ExplicitTensorNetwork.entry _ x : ℕ) : ℤ)
  exact Int.natCast_nonneg _

omit [DecidableEq State] in
/-- **The value contract** of the block-network terms, when `nT`, `τT` and `σT` have the values
`|w|`, `τ` and `σ`. -/
theorem blockNet_acc (hd : RowsFirst machine e w τ σ) (hn : Val w env nT w.length)
    (hτ : Val w env τT τ) (hσ : Val w env σT σ) :
    NetAcc (blockNet machine e w τ σ hd) w env (blockNetT machine e nT τT σT) := by
  classical
  exact
    { vM := ⟨StableAt.clkEdgesT hτ.1 hτ.2,
        (denote_clkEdgesT hτ.1 hτ.2).trans (blockNet_M hd).symm⟩
      vV := ⟨StableAt.clkVerticesT hτ.1 hτ.2, denote_clkVerticesT_length hτ.1 hτ.2⟩
      vu E hE a i ha hi := by
        have hτE := hτ.up hE
        have hσE := hσ.up hE
        refine ⟨StableAt.edgeUT hτE.1 hτE.2 hσE.1 ha.1, ?_⟩
        rw [uN_of_lt hi]
        exact denote_edgeUT hτE.1 hτE.2 hσE.1 hσE.2 (p := 0) hd ha.1 ha.2 hi
      vw E hE a i ha hi := by
        have hτE := hτ.up hE
        refine ⟨StableAt.edgeWT hτE.1 hτE.2 ha.1, ?_⟩
        rw [wN_of_lt hi]
        exact denote_edgeWT hτE.1 hτE.2 (σ := σ) (p := 0) hd ha.2 hi
      vdeg E hE a x ha hx := by
        have hτE := hτ.up hE
        have hσE := hσ.up hE
        refine ⟨StableAt.clkArityT hτE.1 hτE.2 hσE.1 ha.1, ?_⟩
        rw [degN_of_lt hx]
        exact denote_clkArityT hτE.1 hτE.2 hσE.1 hσE.2 (p := 0) hd ha.1 (v := ⟨x, hx⟩) ha.2
      vport E hE a b x j ha hb hx hj := by
        have hτE := hτ.up hE
        have hσE := hσ.up hE
        refine ⟨StableAt.clkPortT hτE.1 hτE.2 hσE.1 ha.1 hb.1, ?_⟩
        rw [degN_of_lt hx] at hj
        rw [portN_of_lt hx hj]
        exact denote_clkPortT hτE.1 hτE.2 hσE.1 hσE.2 (p := 0) hd ha.1 (v := ⟨x, hx⟩) ha.2 hb.1
          (j := ⟨j, hj⟩) hb.2
      veval E hE a b x A ha hb hx _ := by
        have hnE := hn.up hE
        have hτE := hτ.up hE
        have hσE := hσ.up hE
        refine ⟨StableAt.clkWeightT hnE.1 hnE.2 hτE.1 hτE.2 hσE.1 ha.1 hb.1, ?_⟩
        have h := denote_evalAtT hnE.1 hnE.2 hτE.1 hτE.2 hσE.1 hσE.2 (p := 0) hd (pT := const 0) rfl
          ha.1 (v := ⟨x, hx⟩) ha.2 hb.1 hb.2
        rw [NetTerm.evalAtT, denote_mod, denote_const, Nat.mod_zero] at h
        rw [evalN_of_lt hx, blockNet_eval_toNat hd]
        exact h }

omit [DecidableEq State] in
/-- **The tier contract** of the block-network terms at the clock `τ ≥ 2`, for an input with
`|w| ≤ τ`, at every budget `L ≥ blockBudget k s · (⌊log₂ τ⌋ + 1)`, when `nT`, `τT` and `σT` have
the values `|w|`, `τ`, `σ` and tier `1` (in particular `σ < 2^L`). -/
theorem blockNet_tiers (hd : RowsFirst machine e w τ σ) (hτ2 : 2 ≤ τ) (hwτ : w.length ≤ τ)
    (hL : blockBudget k s * (τ.log2 + 1) ≤ L)
    (hn : Val w env nT w.length) (tn : Tm w L 1 nT env)
    (hτ : Val w env τT τ) (tτ : Tm w L 1 τT env)
    (hσ : Val w env σT σ) (tσ : Tm w L 1 σT env) :
    NetTiers (blockNet machine e w τ σ hd) w L env (blockNetT machine e nT τT σT) := by
  classical
  obtain ⟨h16, -, -, hcube, hconst, hkey, hRw, h3b, hccv, hm0, hD⟩ :=
    block_facts (k := k) (s := s) hτ2 hwτ hL
  have hL8 : 8 ≤ L := by omega
  have hadm := explicitAdmissible_blockNetworkOf machine e w σ hτ2
  have hports : ∀ v, ((blockNet machine e w τ σ hd).ports v).length ≤
      6 * (3 * k + 1) * (s + k + 4) * Nat.log 2 τ :=
    fun v => NetTerm.length_ports_le (p := 0) hd hadm v
  have hdeg : ∀ v < verticesN k s τ, (explicitPortsNum k (numBlocks τ)
      (letterBits k s (blockLength τ)) (σT.denote w env) v).length ≤
        6 * (3 * k + 1) * (s + k + 4) * Nat.log 2 τ := by
    intro v hv
    rw [hσ.2]
    have hv' : v < (blockNetworkOf machine e (w, τ, σ)).2.vertices.length := by
      rw [NetTerm.length_vertices]; exact hv
    have h1 := NetTerm.length_ports (p := 0) hd ⟨v, hv'⟩
    have h2 := NetTerm.length_ports_le (p := 0) hd hadm ⟨v, hv'⟩
    rw [h1] at h2
    exact h2
  obtain ⟨har, hpo, hwt, -⟩ := tm_clkAccessors (machine := machine) (e := e) hL8 tn hn.1 hn.2 tτ
    hτ.1 hτ.2 hτ2 hcube hconst hkey hRw h3b hccv hm0 tσ hσ.1 hD hdeg
  obtain ⟨hu1, hw1⟩ := tm_ends1 hL8 tτ hτ.1 hτ.2 hτ2 hcube hconst hm0 tσ hσ.1 hσ.2 hd
  have hM : ∀ {i : ℕ}, i < (blockNet machine e w τ σ hd).M → i < edgesN k s τ := fun hi =>
    hi.trans_eq (blockNet_M hd)
  have hV : ∀ {x : ℕ}, x < (blockNetworkOf machine e (w, τ, σ)).2.vertices.length →
      x < verticesN k s τ := fun hx => hx.trans_eq NetTerm.length_vertices
  exact {
    hL := h16
    hΔ := fun v => (hports v).trans hD.le
    tM := tm_clkEdgesT hL8 tτ hτ.1 hτ.2 hτ2 hcube hconst
    tV := tm_clkVerticesT hL8 tτ hτ.1 hτ.2 hτ2 hcube hconst
    tu := fun E hE a i ha ta hi =>
      hu1 E hE a (ta.mono (by norm_num)) ha.1 (Sm.of_stable ha.1 (by rw [ha.2]; exact hM hi))
    tw := fun E hE a i ha ta hi =>
      hw1 E hE a (ta.mono (by norm_num)) ha.1 (Sm.of_stable ha.1 (by rw [ha.2]; exact hM hi))
    tdeg := fun E hE a _ _ ta _ => har E hE a (ta.mono (by norm_num))
    tport := fun E hE a b _ _ _ ta _ tb _ _ =>
      hpo E hE a b (ta.mono (by norm_num)) (tb.mono (by norm_num))
    teval := fun E hE a b x _ ha ta hb tb hx _ =>
      hwt E hE a b (ta.mono (by norm_num)) ha.1 (Sm.of_stable ha.1 (by rw [ha.2]; exact hV hx))
        (tb.mono (by norm_num)) hb.1 }

end Cslib.Complexity.NtimeDspace.Cube.Num
