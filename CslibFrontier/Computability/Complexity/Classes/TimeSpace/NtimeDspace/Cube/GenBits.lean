/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BitEval
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenTier

/-!
# The bits of `Z(G)` from the programs of the formula

The evaluator `mainT` of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/SumProduct/Eval.lean`
(Proposition 3.2, `GenProg.main_spec`), run on the
programs `cubeProg T` of the formula, computes bit `j` of `Z(G)` at the parameter `[par]`, when the
precision is `P = j + 1`, the fuel and the budget are both `L` (`CubeIn … P B fw K L`), and the
bundle `CubeTiers` holds at `L`. The root bit `j = P - 1` and the budget `X = 128 L - 1` are read
from the input terms of the precision and the fuel (`rootProg`, `budgetProg`).

`cube_bit` discharges the hypotheses of `main_spec`:

* the cost of the recursion is the cost of the formula (`cubeProg_cost`), at most a given `c < L`;
* every precision is `P ≤ 2^ℓ` and every parameter is below `2^(7L)` (the tier of the width
  program), so `V = P + 2^(7L)` bounds precision plus parameter and has size at most `7L + 1`;
* along a valid path every index has bit length at most the cost and the code of the path has
  bit length at most `2 · cost + 1` (`SPTree.elen_valid_le`, for `ℓ ≥ 2`), so the tiers give
  `PathBounded` at `2^(128 L)` (`cubeProg_pathBounded`, `cubeProg_bitBounded`);
* the value of the recursion is `Z(G) mod 2^P` (`cubeProg_value`), whose bit `j < P` is bit `j`
  of `Z(G) ≥ 0`.

## Main definitions

* `rootProg T`, `budgetProg T`: the programs of the root bit `P - 1` and of the budget `128 H - 1`.
* `formulaBitT T`: the evaluator on the programs of the formula.

## Main results

* `SPTree.elen_valid_le`: the bit length of the code of a valid path, and of its indices.
* `GenFun.precLe_tree`, `GenFun.prec_tree_le`, `GenFun.param_tree_le`.
* `cube_bit`: **the bits of `Z(G)`**, with every value below `2^(128 L)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NatList

namespace SPTree

/-- **Codes of valid paths.** For `ℓ ≥ 2`, along a valid path the code has bit length at most
`2 · cost + 1` (the cost of the subtree at the end counted twice), and every index has bit length
at most the cost. -/
theorem elen_valid_le {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (t : SPTree) : ∀ π : List ℕ, Valid t π →
    elen π + 2 * (node t π).cost ℓ ≤ 2 * t.cost ℓ + 1 ∧ ∀ i ∈ π, Nat.size i ≤ t.cost ℓ
  | [], _ => ⟨by change 1 + 2 * t.cost ℓ ≤ 2 * t.cost ℓ + 1; omega, by simp⟩
  | i :: π, ⟨hπ, hi⟩ => by
    obtain ⟨ih1, ih2⟩ := elen_valid_le hℓ t π hπ
    have hc := cost_child ℓ hi
    have hsz : 2 * Nat.size i + 1 ≤ 2 * (node t π).nodeCost ℓ ∧
        Nat.size i ≤ (node t π).nodeCost ℓ := by
      generalize node t π = u at hi
      cases u with
      | leaf => exact hi.elim
      | sum P w f =>
        have : Nat.size i ≤ w := Nat.size_le.mpr hi
        simp only [nodeCost]; omega
      | prod P a b =>
        have hi' : i < 2 := hi
        have : Nat.size i ≤ 1 := Nat.size_le.mpr (by simpa using hi')
        simp only [nodeCost]; omega
      | shift P σ a =>
        have : i = 0 := hi
        subst this
        simp only [nodeCost, Nat.size_zero]; omega
    refine ⟨?_, fun x hx => ?_⟩
    · rw [elen_cons, node_cons]; omega
    · rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact ih2 x hx

end SPTree

namespace GenFun

variable (g : GenFun)

/-- All precisions of the unfolding are at most `B` when the precision of every state is. -/
theorem precLe_tree {B : ℕ} (h : ∀ st, g.prec st ≤ B) : ∀ n st, (g.tree n st).PrecLe B
  | 0, _ => Nat.zero_le _
  | n + 1, st => by
    simp only [tree]
    split_ifs
    · exact ⟨h st, fun i _ => precLe_tree h n _⟩
    · exact ⟨h st, precLe_tree h n _, precLe_tree h n _⟩
    · exact ⟨h st, precLe_tree h n _⟩
    · exact h st

theorem prec_tree_le (n st : ℕ) : (g.tree n st).prec ≤ g.prec st := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simp only [tree]; split_ifs <;> simp [SPTree.prec]

theorem param_tree_le (n st : ℕ) : (g.tree n st).param ≤ g.param st := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simp only [tree]; split_ifs <;> simp [SPTree.param]

end GenFun

end Cslib.Complexity.NtimeDspace.SumProduct

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgLang NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct
  NtimeDspace.Cross

/-! ### The programs of the root bit and the budget -/

/-- The root bit `P - 1`, from the precision. -/
def rootProg (T : CubeT) : Prog := Exact.closeAt 1 (sub T.PT (const 1) 1)

/-- The budget `X = 128 H - 1`, from the fuel `H`. -/
def budgetProg (T : CubeT) : Prog := Exact.closeAt 1 (sub (mul (const 128) T.HT) (const 1) 1)

/-- **The evaluator on the programs of the formula** (Proposition 3.2), over `[par]`. -/
def formulaBitT (T : CubeT) : Term := mainT (cubeProg T).queries (rootProg T) (budgetProg T)

theorem value_nonneg_of {V : ℕ} {G : EdgeNet ℤ (Fin V)} (h : EvalNonneg G) : 0 ≤ G.value :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun v _ => h v _ (by simp)

theorem toNat_testBit (n j : ℕ) : (n.testBit j).toNat = n / 2 ^ j % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h]

section Bit

variable {S : Setup} {T : CubeT} {w : List Bool} {par L D A B j ℓ c : ℕ}

/-- **The bits of `Z(G)`** (Theorem 2.3 at one parameter). At a parameter whose input terms have
the values of the setup with precision `P = j + 1`, reader fuel `B` and fuel `L`, under the bundle
`CubeTiers` at `L`, for `2 ≤ ℓ`, `P ≤ 2^ℓ`, `P < 2^L` and a bound `c < L` on the cost of the formula
at every fuel, the evaluator returns bit `j` of `Z(G)`, with every value below `2^(128 L)`. -/
theorem cube_bit (hI : CubeIn S.G w par T S.P B S.fw S.K L) (hG : CubeTiers S w L par T D A B)
    (hP : S.P = j + 1) (hPL : S.P < 2 ^ L) (hℓ : 2 ≤ ℓ) (hPℓ : S.P ≤ 2 ^ ℓ)
    (hc : ∀ n, (S.gen.tree S.P n (.cl [])).cost ℓ ≤ c) (hcL : c < L) :
    (formulaBitT T).denote w [par] = S.G.value.toNat / 2 ^ j % 2 ∧
      (formulaBitT T).Bnd w (2 ^ (128 * L)) [par] := by
  have hL := hG.hL
  obtain ⟨X, hXdef⟩ : ∃ X, X = 128 * L - 1 := ⟨_, rfl⟩
  have hX1 : X + 1 = 128 * L := by omega
  -- the programs of the root bit and the budget
  have t1 : Tm w L 1 (const 1) [par] := tm_const (Nat.one_lt_two_pow (by omega)) (by norm_num)
  have tR : Tm w L 1 (sub T.PT (const 1)) [par] := tm_sub hG.tP t1
  have t128 : Tm w L 1 (const 128) [par] :=
    tm_const ((show 128 < 2 ^ 16 by norm_num).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))) (by norm_num)
  have tX : Tm w L 2 (sub (mul (const 128) T.HT) (const 1)) [par] :=
    tm_sub (tm_mul t128 hG.tH (by norm_num) (by norm_num)) t1
  have hrootv : (rootProg T).eval w [par] = j ∧ (rootProg T).Bounded w (2 ^ (X + 1)) [par] := by
    refine ⟨(Exact.eval_closeAt _ 1 [par] rfl).trans ?_, ?_⟩
    · change (sub T.PT (const 1)).denote w [par] = j
      rw [denote_sub, hI.vP.2, denote_const]; omega
    · rw [hX1]; exact (Exact.bounded_closeAt _ 1 [par] rfl).mpr tR.bnd
  have hXv : (budgetProg T).eval w [par] = X ∧ (budgetProg T).Bounded w (2 ^ (X + 1)) [par] := by
    refine ⟨(Exact.eval_closeAt _ 1 [par] rfl).trans ?_, ?_⟩
    · change (sub (mul (const 128) T.HT) (const 1)).denote w [par] = X
      rw [denote_sub, denote_mul, hI.vH.2, denote_const, denote_const]; exact hXdef.symm
    · rw [hX1]; exact (Exact.bounded_closeAt _ 1 [par] rfl).mpr tX.bnd
  -- the tree
  have hfun := cubeProg_toFun S hI
  have hprec : ∀ st, ((cubeProg T).toFun w par).prec st = S.P := fun st => by rw [hfun]; rfl
  have hcost : ((cubeProg T).tree w par).cost ℓ ≤ c := by
    rw [cubeProg_cost S hG.hS hG.he hG.hA hG.hB hG.hnn hI ℓ]; exact hc L
  have hnode : ∀ π, SPTree.Valid ((cubeProg T).tree w par) π → SPTree.node
      ((cubeProg T).tree w par) π =
      ((cubeProg T).toFun w par).tree ((cubeProg T).fuel₀ w par - π.length)
        (((cubeProg T).toFun w par).stateAt ((cubeProg T).init₀ w par) π) :=
    fun π hπ => (((cubeProg T).toFun w par).node_tree _ _ π hπ).2
  have hprecN : ∀ π, SPTree.Valid ((cubeProg T).tree w par) π →
      (SPTree.node ((cubeProg T).tree w par) π).prec ≤ S.P := fun π hπ => by
    rw [hnode π hπ, ← hprec (((cubeProg T).toFun w par).stateAt ((cubeProg T).init₀ w par) π)]
    exact GenFun.prec_tree_le _ _ _
  have hparamN : ∀ π, SPTree.Valid ((cubeProg T).tree w par) π →
      (SPTree.node ((cubeProg T).tree w par) π).param < 2 ^ (7 * L) := fun π hπ => by
    obtain ⟨st, h1, h2, h3⟩ := cubeProg_pathState S hG.hS hG.he hG.hA hG.hB hG.hnn hI π hπ
    rw [hnode π hπ]
    refine (GenFun.param_tree_le _ _ _).trans_lt ?_
    rw [h1]
    exact (eval_close (cubeWidthT T.BT T.fwT (lvl 1)) [S.code st, par]).trans_lt
      (tm_cubeWidth_at hG hI h2 h3).lt
  -- the bound `V`
  obtain ⟨V, hV⟩ : ∃ V, V = S.P + 2 ^ (7 * L) := ⟨_, rfl⟩
  have hVsize : V.size ≤ 7 * L + 1 := by
    refine Nat.size_le.mpr ?_
    have : S.P < 2 ^ (7 * L) :=
      hPL.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [pow_succ]; omega
  have hpaths : ∀ π, SPTree.Valid ((cubeProg T).tree w par) π →
      (cubeProg T).PathBounded (w := w) par (2 ^ (X + 1)) π := fun π hπ => by
    obtain ⟨h1, h2⟩ := SPTree.elen_valid_le hℓ _ π hπ
    rw [hX1]
    refine cubeProg_pathBounded hG hI π hπ ?_ fun i hi => ?_
    · have he := NatList.enc_lt π
      have h8 : 9 ≤ 2 ^ (128 * L) :=
        (show 9 ≤ 2 ^ 4 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hel : 2 ^ NatList.elen π ≤ 2 ^ (128 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases le_total (NatList.enc π) 8 with h | h
      · rw [max_eq_right h]; exact h8
      · rw [max_eq_left h]; omega
    · exact (Nat.lt_size_self i).trans_le (Nat.pow_le_pow_right (by norm_num)
        (((h2 i hi).trans hcost).trans hcL.le))
  -- the evaluator
  obtain ⟨hval, hbnd⟩ := GenProg.main_spec (cubeProg T) w par j ℓ V X
    (Exact.closed_closeAt _ _) (Exact.closed_closeAt _ _) (by omega)
    (((cubeProg T).toFun w par).precLe_tree (fun st => (hprec st).trans_le hPℓ) _ _)
    (fun π hπ => by have := hprecN π hπ; have := hparamN π hπ; omega)
    (by rw [hV, hP, add_assoc]; exact Nat.le_add_right _ _)
    (by
      have h34 := Nat.mul_le_mul_left 34 hcost
      change 34 * ((cubeProg T).tree w par).cost ℓ + 2 * V.size + 16 ≤ X
      omega)
    hrootv hXv hpaths
    (fun π k hπ _ hk => by
      rw [hX1]
      exact cubeProg_bitBounded hG hI π hπ (hk.trans_le (hprecN π hπ) |>.trans hPL))
  refine ⟨hval.trans ?_, by rw [← hX1]; exact hbnd⟩
  rw [cubeProg_value S hG.hS hG.he hG.hA hG.hB hG.hnn hI (by omega) hc
    (by have := Nat.div_le_self c ℓ; omega)]
  rw [← Int.toNat_of_nonneg (value_nonneg_of hG.hnn), testBit_res_nat _ _ _ (by omega),
    Int.toNat_natCast]
  exact toNat_testBit _ _

end Bit

end Cslib.Complexity.NtimeDspace.Cube.Num
