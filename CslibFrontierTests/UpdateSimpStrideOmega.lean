/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of update_simp, stride_omega, and PackedSlice)

public import CslibFrontier.Tactic.UpdateSimp
public import CslibFrontier.DataStructure.Dictionary.WordRAM.PackedSlice
public import CslibFrontier.Computability.WordRAM.Allocation

/-!
# Tests for `update_simp`, `stride_omega`, and `PackedSlice`

Exercises ordinary `module` client access (without `import all`) across:
* `update_simp` and `reduceUpdate`: chained `Function.update`, conditional `ite` peeling without
  `split_ifs`, `let`-binding preservation on deep conditional chains, `Data.write`/`Data.set`
  projections, hypothesis rewriting (`at h ⊢`), and head definition unfolding;
* `stride_omega`: 2D strided bounds across all product orientations, strided injectivity and
  distinctness via trichotomy, monotone `2 ^ k` and same-exponent bounds, variable-divisor
  `div`/`mod` identities and comparison bridges, and `@[wram_arith]` unfolding;
* `PackedSlice`: concrete nonvacuous `WriteOutside` and `DisjointIntervals` witnesses, plus
  `packedView_congr` and `packedView_writePacked_disjoint`;
* `#guard_msgs` failure diagnostics and state-restoration checks.
-/

public section

namespace UpdateSimpStrideOmegaTest

open Cslib.WordRAM
open Cslib.Tactic.UpdateSimp (reduceUpdate)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## 1. `stride_omega`: 2D strided bounds, trichotomy, `2 ^ k`, and `div`/`mod` -/

/-- Tagged layout helpers for testing `@[wram_arith]` unfolding inside `stride_omega`. -/
@[wram_arith, expose] def bucketBase (base b S : ℕ) : ℕ := base + b * S
@[wram_arith, expose] def totalEnd (base B S : ℕ) : ℕ := base + B * S

section StrideOmegaTests

variable {a b B s r r' e₁ e₂ w q n D : ℕ}

-- 2D strided bounds across all four factor orientations (`a * s`, `s * a`)
example (hab : a < b) (hr : r < s) : a * s + r < b * s := by
  fail_if_success omega
  stride_omega

example (hab : a < b) (hr : r < s) : s * a + r < b * s := by stride_omega

example (hab : a < b) (hr : r < s) : a * s + r < s * b := by stride_omega

example (hab : a < b) (hr : r < s) : s * a + r < s * b := by stride_omega

example (hab : a ≤ b) : s * a ≤ b * s := by stride_omega

-- `@[wram_arith]` unfolding combined with 2D strided bounds
example (hb : b < B) (hr : r < s) : bucketBase a b s + r < totalEnd a B s := by
  stride_omega

-- Strided trichotomy: injectivity and disequality without knowing the order of `(a, b)`
example (hr : r < s) (hr' : r' < s) (heq : a * s + r = b * s + r') : a = b ∧ r = r' := by
  constructor <;> stride_omega

example (hr : r < s) (hr' : r' < s) (hne : ¬(a = b ∧ r = r')) :
    a * s + r ≠ s * b + r' := by
  stride_omega

-- Monotone `2 ^ k` bounds, doubling step `2 * 2 ^ e₁ ≤ 2 ^ e₂`, and order injectivity
example (h : e₁ < e₂) : 2 ^ e₁ + 2 ^ e₁ ≤ 2 ^ e₂ := by
  fail_if_success omega
  stride_omega

example (h : e₁ ≤ e₂) (hx : a < 2 ^ e₁) : Fits e₂ a := by stride_omega

example (heq : 2 ^ e₁ = 2 ^ e₂) : e₁ = e₂ := by stride_omega

-- Chained strided product inside `2 ^ (…)` exponent
example (ha : a < b) (hfit : 2 ^ (b * s) ≤ 2 ^ w) (hx : r < 2 ^ ((a + 1) * s)) :
    Fits w r := by
  stride_omega

-- Variable-divisor `div`/`mod`: `div_le_self`, `mod_le`, `mod_lt` (via product positivity),
-- Euclidean `(q * s + r) / s = q` & `% s = r` in all 4 sum/product orientations, and `div < m`
example (hfit : Fits w q) : Fits w (q / n % D) ∧ Fits w (q % D / n) :=
  ⟨by stride_omega, by stride_omega⟩

example (hlt : q < n * D) : q / D < n ∧ q % n < n :=
  ⟨by stride_omega, by stride_omega⟩

example (hr : r < s) :
    (q * s + r) / s = q ∧ (q * s + r) % s = r ∧
    (s * q + r) / s = q ∧ (s * q + r) % s = r ∧
    (r + q * s) / s = q ∧ (r + q * s) % s = r ∧
    (r + s * q) / s = q ∧ (r + s * q) % s = r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> stride_omega

end StrideOmegaTests

/-! ## 2. `update_simp` and `reduceUpdate`: linear conditional peeling & `let` sharing -/

/-- Sample map update with nested `let`-bound conditional writes, modeling `gmPushSlab`. -/
def sampleChain (S : ℕ) (f : ℕ → ℕ) (b q p : ℕ) : ℕ → ℕ :=
  let f₁ := Function.update (Function.update f (100 + 2 * p) b) (100 + 2 * p + 1) q
  let f₂ := if 0 < q then Function.update f₁ (50 + p) 99 else f₁
  let f₃ := if q < S then Function.update f₂ (10 + b * S + q) p else f₂
  Function.update f₃ 0 (p + 1)

section UpdateSimpTests

-- Peeling a conditional chain WITHOUT splitting undecided `if` guards (`0 < q`, `q < S`)
example (S : ℕ) (f : ℕ → ℕ) (b b' q s p : ℕ)
    (hs : s < S) (hne : ¬(b' = b ∧ s = q)) :
    sampleChain S f b q p (10 + b' * S + s) =
      (if 0 < q then Function.update
        (Function.update (Function.update f (100 + 2 * p) b) (100 + 2 * p + 1) q)
        (50 + p) 99 else
        Function.update (Function.update f (100 + 2 * p) b) (100 + 2 * p + 1) q)
        (10 + b' * S + s) := by
  update_simp [sampleChain]

-- Reading disjoint low header slot `1` collapses all 4 `let`/conditional layers to `f 1`
example (S : ℕ) (f : ℕ → ℕ) (b q p : ℕ) :
    sampleChain S f b q p 1 = f 1 := by
  update_simp [sampleChain]

/-- Deep `let`-chain of 12 independent undecided conditional updates: `split_ifs` would create
`2 ^ 12 = 4096` branches, whereas `update_simp` peels linearly in `O(12)` steps. -/
def deepChain (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) : ℕ → ℕ :=
  let g1 := if P 1 then Function.update f 1 10 else f
  let g2 := if P 2 then Function.update g1 2 20 else g1
  let g3 := if P 3 then Function.update g2 3 30 else g2
  let g4 := if P 4 then Function.update g3 4 40 else g3
  let g5 := if P 5 then Function.update g4 5 50 else g4
  let g6 := if P 6 then Function.update g5 6 60 else g5
  let g7 := if P 7 then Function.update g6 7 70 else g6
  let g8 := if P 8 then Function.update g7 8 80 else g7
  let g9 := if P 9 then Function.update g8 9 90 else g8
  let g10 := if P 10 then Function.update g9 10 100 else g9
  let g11 := if P 11 then Function.update g10 11 110 else g10
  if P 12 then Function.update g11 12 120 else g11

example (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] :
    deepChain P f 0 = f 0 := by
  update_simp [deepChain]

-- Conditional `then` and `else` updates with distinct base functions and matched indices
example (f g : ℕ → ℕ) (p : Prop) [Decidable p] (k : ℕ) :
    (if p then Function.update f (k + 1) 7 else Function.update g (k + 2) 8) k =
      (if p then f else g) k := by
  update_simp

example (f g : ℕ → ℕ) (a k : ℕ) :
    (if k = a then Function.update f a 42 else g) k = if k = a then 42 else g k := by
  update_simp

-- Nested `Function.update` inside the index argument of an outer `Function.update`
example (td dt : ℕ → ℕ) (n c t : ℕ) (ht : t < n) (hne : td t ≠ c) :
    Function.update dt c n (Function.update td n c t) = dt (td t) := by
  update_simp

example (td dt : ℕ → ℕ) (n c : ℕ) :
    Function.update dt c n (Function.update td n c n) = n := by
  update_simp

-- `Data.write` / `Data.set` projections and hypothesis rewriting `at h ⊢`
example (d : Data 4) (a : ℕ)
    (h : ((d.write (a + 1) 99).set 2 7).mem a = 5) :
    ((if a < 10 then d.write (a + 2) 88 else d.set 1 3).mem a) = 5 := by
  update_simp at h ⊢
  exact h

-- `reduceUpdate` simproc inside `simp only`
example (f : ℕ → ℕ) (i : ℕ) :
    Function.update (Function.update f (i + 1) 9) i 4 i +
      Function.update f (i + 2) 7 i = 4 + f i := by
  simp only [reduceUpdate]

end UpdateSimpTests

/-! ## 3. `PackedSlice`: concrete nonvacuous instances and disjoint slice views -/

section PackedSliceTests

-- Nonvacuous concrete instance of `WriteOutside`, `DisjointIntervals`, `packedView_congr`,
-- and `packedView_writePacked_disjoint`
example :
    let mem : ℕ → ℕ := fun _ => 0
    let mem' := writePacked 10 4 64 mem 2 13
    let mem₂ := Function.update mem' 50 999
    WriteOutside 10 (10 + packedWords 8 4 64) mem mem' ∧
    DisjointIntervals 10 (10 + packedWords 8 4 64) 30 (30 + packedWords 8 4 64) ∧
    readPacked 10 4 64 mem' 2 = 13 ∧
    (fun i => if i < 8 then readPacked 10 4 64 mem₂ i else 0) =
      (fun i => if i < 8 then readPacked 10 4 64 mem' i else 0) ∧
    (fun i => if i < 8 then readPacked 30 4 64 mem' i else 0) =
      (fun i => if i < 8 then readPacked 30 4 64 mem i else 0) := by
  intro mem mem' mem₂
  have hw : 0 < 64 := by decide
  have hidx : 2 < 8 := by decide
  have hdisj : DisjointIntervals 10 (10 + packedWords 8 4 64) 30 (30 + packedWords 8 4 64) :=
    Or.inl (by unfold packedWords; decide)
  refine ⟨writePacked_writeOutside hw hidx le_rfl le_rfl mem, hdisj,
    readPacked_writePacked_self 10 4 64 mem 2 (by decide),
    packedView_congr hw fun addr haddr => ?_,
    packedView_writePacked_disjoint hw hidx hdisj.symm mem⟩
  have hpw : packedWords 8 4 64 = 3 := by decide
  dsimp only [mem₂]
  update_simp

end PackedSliceTests

/-! ## 4. Failure diagnostics (`#guard_msgs`) and state restoration -/

/--
error: stride_omega: could not close goal with `omega`
-/
#guard_msgs (substring := true) in
example (a b s : ℕ) (h : a ≤ b) : a * s + s ≤ b * s := by
  stride_omega

/--
error: update_simp: made no progress on target
-/
#guard_msgs in
example (f : ℕ → ℕ) (a k : ℕ) : Function.update f a 1 k = f k := by
  update_simp

-- Failed calls restore state cleanly
example (a b : ℕ) (h : a < b) : a ≤ b := by
  fail_if_success update_simp
  fail_if_success (have : b < a := by stride_omega)
  omega

end UpdateSimpStrideOmegaTest
