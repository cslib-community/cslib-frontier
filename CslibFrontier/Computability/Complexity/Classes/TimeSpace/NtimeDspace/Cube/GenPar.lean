/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.NetInstBlock
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.StSize

/-!
# The parameter of the programs of the formula (Lemma 6.4)

The programs `cubeProg T` of `GenTerm.lean` read their inputs from terms over one parameter
`[par]`. Here the parameter is the list code (`SumProduct.NatList.enc`) of the numbers the
programs need, and every input term reads one field (`parFieldT j`). This gives the inputs `CubeT`
for the two network instances:

* `famCubeT F` for a logspace family (`famNetT`, `NetInst.lean`), at `famPar s P B fw K H`, the
  code of `[s, P, B, fw, K, H]`;
* `blockCubeT M e` for the block networks (`blockNetT`, `NetInstBlock.lean`), at
  `blockPar n τ σ P B fw K H`, the code of `[n, τ, σ, P, B, fw, K, H]` with `n = |w|`.

## Main definitions

* `parFieldT j`: field `j` of the parameter.
* `famPar`, `famCubeT`, `blockPar`, `blockCubeT`.

## Main results

* `val_parFieldT`, `tm_parFieldT`: the value of a field, and its tier `1` when every field (of at
  most `14`) is below `2^L` and `15 ≤ L`.
* `famCube_in`, `famCube_tiers`: `CubeIn` for a member of the family, and the tiers of the input
  terms (`NetTiers` and tier `1` of the five numbers) for `(2C + 3)(⌊log₂ s⌋ + 1) ≤ L`.
* `blockCube_in`, `blockCube_tiers`: the same for the block networks, at clocks `τ ≥ 2` with
  `|w| ≤ τ` and `blockBudget k s · (⌊log₂ τ⌋ + 1) ≤ L`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross SumProduct

variable {w : List Bool} {L : ℕ}

/-! ### Fields of the parameter -/

/-- Field `j` of the parameter at the bottom of the environment. -/
def parFieldT (j : ℕ) : Term := stGetT (lvl 0) j

theorem stGet_enc_getD : ∀ (l : List ℕ) (j : ℕ), j < l.length →
    stGet (NatList.enc l) j = l.getD j 0
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => by simp
  | _ :: l, j + 1, h => by
    rw [stGet_cons_succ, List.getD_cons_succ]
    exact stGet_enc_getD l j (by simpa using h)

theorem val_parFieldT (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    Val w [NatList.enc l] (parFieldT j) (l.getD j 0) :=
  (val_stGetT (val_lvl_at (w := w) (e := [NatList.enc l]) (l := 0) (by simp)) j).congr
    (stGet_enc_getD l j hj)

/-- **The tier of a field of the parameter**: `1`, when the parameter has at most `14` fields, all
below `2^L`, and `15 ≤ L`. -/
theorem tm_parFieldT {l : List ℕ} (hl : l.length ≤ 14) (hs : ∀ x ∈ l, x < 2 ^ L) (hL : 15 ≤ L)
    {j : ℕ} (hj : j < l.length) : Tm w L 1 (parFieldT j) [NatList.enc l] := by
  have hp : NatList.enc l < 2 ^ (29 * L) :=
    (enc_lt_of_mem hl hs).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have v0 : Val w [NatList.enc l] (lvl 0) (NatList.enc l) := val_lvl_at (by simp)
  have t0 : Tm w L 29 (lvl 0) [NatList.enc l] := tm_lvl (by simp) hp
  refine tm_val (tm_stGetT v0 t0 (by norm_num) (by norm_num) (by omega) j hj)
      (val_parFieldT l hj) ?_
  rw [one_mul, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact hs _ (List.getElem_mem hj)

/-! ### A logspace family -/

/-- The parameter of a logspace family: the code of `[s, P, B, fw, K, H]`. -/
def famPar (s P B fw K H : ℕ) : ℕ := NatList.enc [s, P, B, fw, K, H]

/-- **The inputs of the programs for a logspace family**: the network terms `famNetT F` at the
size field, and the fields `P`, `B`, `fw`, `K`, `H`. -/
def famCubeT (F : LogspaceNetFamily) : CubeT :=
  ⟨famNetT F (parFieldT 0), parFieldT 1, parFieldT 2, parFieldT 3, parFieldT 4, parFieldT 5⟩

section Fam

variable {F : LogspaceNetFamily} {s P B fw K H : ℕ}

/-- **The input values for a member of the family.** -/
theorem famCube_in (hm : F.Mem w s) :
    CubeIn (F.net w s) w (famPar s P B fw K H) (famCubeT F) P B fw K H :=
  ⟨famNet_acc hm (val_parFieldT [s, P, B, fw, K, H] (j := 0) (by simp)),
    val_parFieldT [s, P, B, fw, K, H] (j := 1) (by simp),
    val_parFieldT [s, P, B, fw, K, H] (j := 2) (by simp),
    val_parFieldT [s, P, B, fw, K, H] (j := 3) (by simp),
    val_parFieldT [s, P, B, fw, K, H] (j := 4) (by simp),
    val_parFieldT [s, P, B, fw, K, H] (j := 5) (by simp)⟩

/-- **The tiers of the inputs for a member of the family**, when the six fields are below `2^L`,
`16 ≤ L` and `(2C + 3)(⌊log₂ s⌋ + 1) ≤ L`. -/
theorem famCube_tiers (hm : F.Mem w s) (hs : ∀ x ∈ [s, P, B, fw, K, H], x < 2 ^ L) (h16 : 16 ≤ L)
    (hL : (2 * F.C + 3) * (s.log2 + 1) ≤ L) :
    NetTiers (F.net w s) w L [famPar s P B fw K H] (famCubeT F).N ∧
      Tm w L 1 (famCubeT F).PT [famPar s P B fw K H] ∧
      Tm w L 1 (famCubeT F).BT [famPar s P B fw K H] ∧
      Tm w L 1 (famCubeT F).fwT [famPar s P B fw K H] ∧
      Tm w L 1 (famCubeT F).KT [famPar s P B fw K H] ∧
      Tm w L 1 (famCubeT F).HT [famPar s P B fw K H] := by
  have t := fun j (hj : j < 6) => tm_parFieldT (w := w) (l := [s, P, B, fw, K, H]) (by simp) hs
    (by omega) (j := j) (by simpa using hj)
  exact ⟨famNet_tiers hm (val_parFieldT [s, P, B, fw, K, H] (j := 0) (by simp)) (t 0 (by norm_num))
    h16 hL, t 1 (by norm_num), t 2 (by norm_num), t 3 (by norm_num), t 4 (by norm_num),
    t 5 (by norm_num)⟩

end Fam

/-! ### The block networks -/

open _root_.Turing _root_.Turing.MultiTapePTM Cslib.Complexity.CountingSimulation
    Cslib.Circuits.Frontier
  NtimeDspace.Cross.NetTerm

/-- The parameter of the block networks: the code of `[n, τ, σ, P, B, fw, K, H]`. -/
def blockPar (n τ σ P B fw K H : ℕ) : ℕ := NatList.enc [n, τ, σ, P, B, fw, K, H]

section Block

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

/-- **The inputs of the programs for the block networks**: the network terms `blockNetT` at the
fields `n`, `τ`, `σ`, and the fields `P`, `B`, `fw`, `K`, `H`. -/
def blockCubeT : CubeT :=
  ⟨blockNetT machine e (parFieldT 0) (parFieldT 1) (parFieldT 2), parFieldT 3, parFieldT 4,
    parFieldT 5, parFieldT 6, parFieldT 7⟩

variable {machine e} {τ σ P B fw K H : ℕ}

omit [DecidableEq State] in
/-- **The input values for a block network**, at the parameter with `n = |w|`. -/
theorem blockCube_in (hd : RowsFirst machine e w τ σ) :
    CubeIn (blockNet machine e w τ σ hd) w (blockPar w.length τ σ P B fw K H)
      (blockCubeT machine e) P B fw K H :=
  ⟨blockNet_acc hd (val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 0) (by simp))
      (val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 1) (by simp))
      (val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 2) (by simp)),
    val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 3) (by simp),
    val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 4) (by simp),
    val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 5) (by simp),
    val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 6) (by simp),
    val_parFieldT [w.length, τ, σ, P, B, fw, K, H] (j := 7) (by simp)⟩

omit [DecidableEq State] in
/-- **The tiers of the inputs for a block network**, at clocks `τ ≥ 2` with `|w| ≤ τ`, when the
eight fields are below `2^L`, `16 ≤ L` and `blockBudget k s · (⌊log₂ τ⌋ + 1) ≤ L`. -/
theorem blockCube_tiers (hd : RowsFirst machine e w τ σ) (hτ2 : 2 ≤ τ) (hwτ : w.length ≤ τ)
    (hs : ∀ x ∈ [w.length, τ, σ, P, B, fw, K, H], x < 2 ^ L) (h16 : 16 ≤ L)
    (hL : blockBudget k s * (τ.log2 + 1) ≤ L) :
    NetTiers (blockNet machine e w τ σ hd) w L [blockPar w.length τ σ P B fw K H]
        (blockCubeT machine e).N ∧
      Tm w L 1 (blockCubeT machine e).PT [blockPar w.length τ σ P B fw K H] ∧
      Tm w L 1 (blockCubeT machine e).BT [blockPar w.length τ σ P B fw K H] ∧
      Tm w L 1 (blockCubeT machine e).fwT [blockPar w.length τ σ P B fw K H] ∧
      Tm w L 1 (blockCubeT machine e).KT [blockPar w.length τ σ P B fw K H] ∧
      Tm w L 1 (blockCubeT machine e).HT [blockPar w.length τ σ P B fw K H] := by
  classical
  have t := fun j (hj : j < 8) => tm_parFieldT (w := w) (l := [w.length, τ, σ, P, B, fw, K, H])
    (by simp) hs (by omega) (j := j) (by simpa using hj)
  have v := fun j (hj : j < 8) => val_parFieldT (w := w) [w.length, τ, σ, P, B, fw, K, H] (j := j)
    (by simpa using hj)
  exact ⟨blockNet_tiers hd hτ2 hwτ hL (v 0 (by norm_num)) (t 0 (by norm_num)) (v 1 (by norm_num))
    (t 1 (by norm_num)) (v 2 (by norm_num)) (t 2 (by norm_num)), t 3 (by norm_num),
    t 4 (by norm_num), t 5 (by norm_num), t 6 (by norm_num), t 7 (by norm_num)⟩

end Block

end Cslib.Complexity.NtimeDspace.Cube.Num
