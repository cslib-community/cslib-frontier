/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.SpanProgram.EliminationSynthesis
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.LinearEquivalence
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

/-!
# The algorithm `Lin` and the program `P_L`: checked instances

Checks of Theorem 22.14 ([BonehShoup2023], p. 981) over `ZMod 5`:

* parts (a) and (b) as a caller applies them to the two-out-of-three program of Example 22.2,
  with the book's hypothesis on the access structure as well as on acceptance;
* the book's remark that part (b) implies the privacy of Theorem 22.13, derived from part (b)
  alone;
* the values of `Lin`, of the kernel vector and of `P_L`, by kernel reduction, including the
  book's vectors `λ₁ = (1, 0)`, `λ₂ = (1)`, `λ₃ = (1, 0)` for Example 22.3 and the values outside
  the domains of the algorithms;
* the two circuit bounds turned into circuits for three parties, one row and two columns;
* each hypothesis is needed: `Lin` fails on a coalition that is not accepted, and `P_L` of an
  accepted coalition is never equivalent to `P`.
-/

public section

namespace CslibFrontierTests.SpanProgramElimination

open Cslib.Circuits Cslib.Crypto.Protocols.SecretSharing
open Cslib.Probability Cslib.Probability.PMF
open scoped Matrix

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Example 22.2 ([BonehShoup2023], p. 979) with `t = 2`, `N = 3`, `q = 5`: party `i` holds the
row `(1, i + 1)`. -/
def shamir23 : MonotoneSpanProgram (ZMod 5) (Fin 3) where
  tailDim := 1
  rowDim := fun _ => 1
  matrix i := !![1, (i.val + 1 : ZMod 5)]

/-- The coalition `{0, 1}` is accepted, with weights `2` and `4`. -/
theorem shamir23_accepts_01 : shamir23.Accepts {0, 1} := by
  rw [MonotoneSpanProgram.accepts_iff_exists_vecMul]
  let w : (i : ({0, 1} : Finset (Fin 3))) → Fin (shamir23.rowDim i.1) → ZMod 5 :=
    fun i => match i with
      | ⟨0, _⟩ => ![2]
      | ⟨1, _⟩ => ![4]
  refine ⟨w, ?_⟩
  ext j
  fin_cases j <;> decide

/-- The coalition `{1}` is not accepted: `(1, 2)` is orthogonal to its row and has first entry
one. -/
theorem shamir23_not_accepts_1 : ¬ shamir23.Accepts {1} := by
  refine MonotoneSpanProgram.not_accepts_of_exists_nullVector shamir23 ![1, 2] rfl ?_
  intro i hi
  fin_cases i <;> first | exact absurd hi (by decide) | decide

/-- Theorem 22.14(a) as a caller uses it: `Lin` reconstructs for an accepted coalition. -/
example (k : LinearKey shamir23) (secret : ZMod 5) :
    ∑ i : ({0, 1} : Finset (Fin 3)),
      shamir23.recombination {0, 1} i.1 ⬝ᵥ linearShare shamir23 k secret i.1 = secret :=
  sum_recombination_dotProduct_linearShare shamir23 shamir23_accepts_01 k secret

/-- The same with the book's hypothesis, a coalition authorized in the access structure that the
program recognizes ([BonehShoup2023], Definition 22.21, p. 978). -/
example (hs : shamir23.accessStructure.authorized {0, 1}) (k : LinearKey shamir23)
    (secret : ZMod 5) :
    ∑ i : ({0, 1} : Finset (Fin 3)),
      shamir23.recombination {0, 1} i.1 ⬝ᵥ linearShare shamir23 k secret i.1 = secret :=
  sum_recombination_dotProduct_linearShare shamir23 hs k secret

/-- Theorem 22.14(b) as a caller uses it: for a coalition that is not accepted, the normal form
gives the same distribution of shares, and the share of a member is the same for every secret. -/
example (secret : ZMod 5) :
    (linearUniformAccessScheme (shamir23.normalForm {1})).shareDist
        (uniformOfFintype (LinearKey (shamir23.normalForm {1}))) secret =
      (linearUniformAccessScheme shamir23).shareDist (uniformOfFintype (LinearKey shamir23))
        secret ∧
      ∀ (k : LinearKey (shamir23.normalForm {1})) (secret' : ZMod 5),
        linearShare (shamir23.normalForm {1}) k secret 1 =
          linearShare (shamir23.normalForm {1}) k secret' 1 :=
  ⟨shareDist_linearUniformAccessScheme_normalForm shamir23 shamir23_not_accepts_1 secret,
    fun k secret' => linearShare_eq_of_col_zero _
      (shamir23.normalForm_matrix_zero (by decide)) k secret secret'⟩

/-- `P_L` accepts the same coalitions as `P`: the normal form for the rejected coalition `{1}`
still accepts `{0, 1}` and still rejects `{1}`. -/
example : (shamir23.normalForm {1}).Accepts {0, 1} ∧ ¬ (shamir23.normalForm {1}).Accepts {1} :=
  ⟨(shamir23.accepts_normalForm shamir23_not_accepts_1 {0, 1}).mpr shamir23_accepts_01,
    fun h => shamir23_not_accepts_1 ((shamir23.accepts_normalForm shamir23_not_accepts_1 {1}).mp h)⟩

/-- Outside the domains: `Lin` of the rejected coalition `{1}` is zero for every party, the kernel
vector of the accepted coalition `{0, 1}` is zero, and its normal form accepts no coalition. -/
example (i : Fin 3) (t : Finset (Fin 3)) :
    shamir23.recombination {1} i = 0 ∧ shamir23.nullVector {0, 1} = 0 ∧
      ¬ (shamir23.normalForm {0, 1}).Accepts t :=
  ⟨shamir23.recombination_eq_zero_of_not_accepts shamir23_not_accepts_1 i,
    shamir23.nullVector_eq_zero_of_accepts shamir23_accepts_01,
    shamir23.not_accepts_normalForm_of_accepts shamir23_accepts_01 t⟩

/-- "clearly implies Theorem 22.13" ([BonehShoup2023], p. 981): the privacy theorem for uniform
keys follows from Theorem 22.14(b). -/
example {F : Type*} [Field F] [Fintype F] [DecidableEq F] {N : ℕ}
    (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)} (hs : ¬ P.Accepts s)
    (secret₀ secret₁ : F) :
    AccessStructure.viewDistOf (uniformOfFintype (LinearKey P)) (linearShare P) s secret₀ =
      AccessStructure.viewDistOf (uniformOfFintype (LinearKey P)) (linearShare P) s secret₁ := by
  have key : ∀ secret,
      AccessStructure.viewDistOf (uniformOfFintype (LinearKey P)) (linearShare P) s secret =
        (uniformOfFintype (LinearKey P)).map
          fun k (i : s) => linearShare (P.normalForm s) k secret i.1 := by
    intro secret
    have h₁ : AccessStructure.viewDistOf (uniformOfFintype (LinearKey P)) (linearShare P) s
        secret = ((linearUniformAccessScheme P).shareDist (uniformOfFintype (LinearKey P))
          secret).map fun sh (i : s) => sh i.1 :=
      (PMF.map_comp (fun k => linearShare P k secret) _ (fun sh (i : s) => sh i.1)).symm
    have h₂ : ((linearUniformAccessScheme (P.normalForm s)).shareDist
        (uniformOfFintype (LinearKey (P.normalForm s))) secret).map (fun sh (i : s) => sh i.1) =
        (uniformOfFintype (LinearKey P)).map
          fun k (i : s) => linearShare (P.normalForm s) k secret i.1 :=
      PMF.map_comp (fun k => linearShare (P.normalForm s) k secret) _ (fun sh (i : s) => sh i.1)
    have h := congrArg (fun D => PMF.map (fun sh (i : s) => sh i.1) D)
      (shareDist_linearUniformAccessScheme_normalForm P hs secret)
    exact h₁.trans (h.symm.trans h₂)
  rw [key, key]
  congr 1
  funext k i
  exact linearShare_eq_of_col_zero _ (P.normalForm_matrix_zero i.2) k secret₀ secret₁

/-! ### Values

Each value is stated through a `fun` at the literal index type: stated directly, as in
`shamir23.recombination {0, 1} 0 = ![2]`, the two sides have types that agree only after unfolding
`shamir23`, and `decide` finds no instance. -/

/-- `Lin({0, 1})` is the pair of Lagrange coefficients at zero of the points `1` and `2`; the
party outside the coalition gets the zero vector. -/
example : (fun row : Fin 1 => shamir23.recombination {0, 1} 0 row) = ![2] ∧
    (fun row : Fin 1 => shamir23.recombination {0, 1} 1 row) = ![4] ∧
    (fun row : Fin 1 => shamir23.recombination {0, 1} 2 row) = ![0] := by
  decide +kernel

/-- The kernel vector of the coalition `{1}`. -/
example : (fun c : Fin 2 => shamir23.nullVector {1} c) = ![1, 2] := by
  decide +kernel

/-- `P_L` for `L = {1}`: the row of party `1` becomes `(0, 2)`; the second column is kept. -/
example :
    (Matrix.of fun (row : Fin 1) (c : Fin 2) => (shamir23.normalForm {1}).matrix 0 row c) =
      !![3, 1] ∧
    (Matrix.of fun (row : Fin 1) (c : Fin 2) => (shamir23.normalForm {1}).matrix 1 row c) =
      !![0, 2] ∧
    (Matrix.of fun (row : Fin 1) (c : Fin 2) => (shamir23.normalForm {1}).matrix 2 row c) =
      !![2, 3] := by
  decide +kernel

/-- On an accepted coalition the kernel vector is zero and `normalForm` zeroes the first column
of every party, also outside the coalition. -/
example :
    (Matrix.of fun (row : Fin 1) (c : Fin 2) => (shamir23.normalForm {0, 1}).matrix 2 row c) =
      !![0, 3] := by
  decide +kernel

/-- Example 22.3 ([BonehShoup2023], p. 979) on `Fin 4` over `ZMod 5`, restated from
`CslibFrontierTests.Crypto.LinearSecretSharing` so that kernel reduction can unfold it. -/
def example22_3 : MonotoneSpanProgram (ZMod 5) (Fin 4) where
  tailDim := 4
  rowDim := ![2, 1, 2, 1]
  matrix
    | 0 => !![1, 1, 0, 0, 0; 1, 0, 0, 1, 0]
    | 1 => !![0, 0, 1, 0, 0]
    | 2 => !![0, -1, -1, 0, 0; 0, 0, 0, 0, 1]
    | 3 => !![0, 0, 0, -1, -1]

/-- The vectors `λ₁ = (1, 0)`, `λ₂ = (1)`, `λ₃ = (1, 0)` that the book gives for
`Lin({1, 2, 3})` ([BonehShoup2023], p. 981). -/
example : (fun row : Fin 2 => example22_3.recombination {0, 1, 2} 0 row) = ![1, 0] ∧
    (fun row : Fin 1 => example22_3.recombination {0, 1, 2} 1 row) = ![1] ∧
    (fun row : Fin 2 => example22_3.recombination {0, 1, 2} 2 row) = ![1, 0] := by
  decide +kernel

/-! ### Circuits -/

/-- The bound for `Lin` yields a circuit: for three parties with one row and two columns each, a
circuit whose inputs are the six matrix entries and the three membership values, with at most
`611` gates, outputs `Lin` of the coalition `{i | x (6 + i) ≠ 0}`. -/
example :
    ∃ c : Circuit _ (6 + 3) 3,
      c.Computes (fullInterpretation (k := 2))
        (fun (x : Fin (6 + 3) → ZMod 5) j =>
          (MonotoneSpanProgram.mk 1 (fun _ : Fin 3 => 1)
            fun i _ c => x (Fin.castAdd 3 (finProdFinEquiv (i, c)))).recombination
              (Finset.univ.filter fun i => x (Fin.natAdd 6 i) ≠ 0) j 0) ∧
      c.size ≤ 611 := by
  have h := Synthesis.full_recombination (F := ZMod 5) (N' := 6 + 3) (src := inputs (6 + 3)) 1
    (fun _ : Fin 3 => 1) (fun i _ c x => x (Fin.castAdd 3 (finProdFinEquiv (i, c))))
    (fun i x => x (Fin.natAdd 6 i)) (fun i _ c => ⟨_, rfl⟩) (fun i => ⟨_, rfl⟩)
  refine (h.mono Set.Subset.rfl ?_ (by norm_num [kernelVecCost])).exists_circuit_outputs
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j, 0⟩, rfl⟩

/-- The same for `P_L`: a circuit with the same nine inputs and at most `309` gates outputs the
six entries of `normalForm` of the coalition `{i | x (6 + i) ≠ 0}`. -/
example :
    ∃ c : Circuit _ (6 + 3) (3 * 2),
      c.Computes (fullInterpretation (k := 2))
        (fun (x : Fin (6 + 3) → ZMod 5) (o : Fin (3 * 2)) =>
          ((MonotoneSpanProgram.mk 1 (fun _ : Fin 3 => 1)
            fun i _ c => x (Fin.castAdd 3 (finProdFinEquiv (i, c)))).normalForm
              (Finset.univ.filter fun i => x (Fin.natAdd 6 i) ≠ 0)).matrix
                (finProdFinEquiv.symm o).1 (0 : Fin 1) ((finProdFinEquiv.symm o).2 : Fin 2)) ∧
      c.size ≤ 309 := by
  have h := Synthesis.full_normalForm (F := ZMod 5) (N' := 6 + 3) (src := inputs (6 + 3)) 1
    (fun _ : Fin 3 => 1) (fun i _ c x => x (Fin.castAdd 3 (finProdFinEquiv (i, c))))
    (fun i x => x (Fin.natAdd 6 i)) (fun i _ c => ⟨_, rfl⟩) (fun i => ⟨_, rfl⟩)
  refine (h.mono Set.Subset.rfl ?_ (by norm_num [kernelVecCost])).exists_circuit_outputs
  rintro _ ⟨o, rfl⟩
  exact ⟨⟨⟨(finProdFinEquiv.symm o).1, 0⟩, (finProdFinEquiv.symm o).2⟩, rfl⟩

/-! ### The hypotheses are needed -/

/-- **`Lin` needs an accepted coalition.** For the coalition `{1}`, which is not accepted, no
vector at all reconstructs the secret from the share of party `1`, so the output of `Lin` does
not either: the keys `![0]` with secret `0` and `![3]` with secret `4` give party `1` the same
share. -/
example : ¬ ∀ (k : LinearKey shamir23) (secret : ZMod 5),
    ∑ i : ({1} : Finset (Fin 3)),
      shamir23.recombination {1} i.1 ⬝ᵥ linearShare shamir23 k secret i.1 = secret := by
  intro h
  have hone : linearShare shamir23 ![3] 4 1 = linearShare shamir23 ![0] 0 1 := by
    funext row
    fin_cases row
    decide
  have hshare : ∀ i : ({1} : Finset (Fin 3)),
      linearShare shamir23 ![3] 4 i.1 = linearShare shamir23 ![0] 0 i.1 := by
    rintro ⟨i, hi⟩
    obtain rfl : i = 1 := Finset.mem_singleton.1 hi
    exact hone
  have h₀ := h ![0] 0
  have h₁ := h ![3] 4
  simp only [hshare] at h₁
  exact absurd (h₀.symm.trans h₁) (by decide)

/-- **`P_L` needs a coalition that is not accepted.** For an accepted coalition `s` the program
`P.normalForm s` is never equivalent to `P`: `Lin` recovers the secret from the shares of `P`,
while in `P.normalForm s` the members' shares do not depend on the secret. -/
theorem not_shareDist_normalForm_of_accepts {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {N : ℕ} (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)}
    (hs : P.Accepts s) :
    ¬ ∀ secret, (linearUniformAccessScheme (P.normalForm s)).shareDist
        (uniformOfFintype (LinearKey (P.normalForm s))) secret =
      (linearUniformAccessScheme P).shareDist (uniformOfFintype (LinearKey P)) secret := by
  intro h
  let g : ((i : Fin N) → LinearShare P i) → F := fun sh =>
    ∑ i : s, P.recombination s i.1 ⬝ᵥ sh i.1
  have hP : ∀ secret, ((linearUniformAccessScheme P).shareDist
      (uniformOfFintype (LinearKey P)) secret).map g = PMF.pure secret := by
    intro secret
    change ((uniformOfFintype (LinearKey P)).map fun k => linearShare P k secret).map g = _
    rw [PMF.map_comp]
    have : (g ∘ fun k => linearShare P k secret) = Function.const _ secret :=
      funext fun k => sum_recombination_dotProduct_linearShare P hs k secret
    rw [this, PMF.map_const]
  have hN : ∀ secret₀ secret₁, ((linearUniformAccessScheme (P.normalForm s)).shareDist
      (uniformOfFintype (LinearKey (P.normalForm s))) secret₀).map g =
      ((linearUniformAccessScheme (P.normalForm s)).shareDist
        (uniformOfFintype (LinearKey (P.normalForm s))) secret₁).map g := by
    intro secret₀ secret₁
    have e : ∀ secret, ((linearUniformAccessScheme (P.normalForm s)).shareDist
        (uniformOfFintype (LinearKey (P.normalForm s))) secret).map g =
        (uniformOfFintype (LinearKey P)).map
          fun k => g (linearShare (P.normalForm s) k secret) :=
      fun secret => PMF.map_comp (fun k => linearShare (P.normalForm s) k secret) _ g
    refine (e secret₀).trans (Eq.trans ?_ (e secret₁).symm)
    congr 1
    funext k
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (P.recombination s i.1 ⬝ᵥ ·)
        (linearShare_eq_of_col_zero _ (P.normalForm_matrix_zero i.2) k secret₀ secret₁)
  have h01 : (PMF.pure (0 : F)) = PMF.pure 1 := by
    rw [← hP 0, ← hP 1, ← h 0, ← h 1]
    exact hN 0 1
  have := congrArg (fun D : PMF F => D 0) h01
  simp at this

end CslibFrontierTests.SpanProgramElimination
