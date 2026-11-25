/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Leaf
public import CslibFrontier.Computability.Communication.NOF.Randomized
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cylinder intersections and the multiparty discrepancy bound

A set of inputs is a *cylinder in the `i`-th dimension* when membership does not depend on the
`i`-th part of the input, and a *cylinder intersection* is an intersection of cylinders, one in each
dimension (`NOF.IsCylinder`, `NOF.IsCylinderIntersection`) [Jukna, Section 5.4, p. 140][Jukna2012].
A cylinder in the `i`-th dimension is a set of inputs determined by what player `i` sees, so a
cylinder intersection is the set `NOF.cylinderIntersection φ` of inputs `x` that pass a test
`φ i (view i x)` of every player `i` (`NOF.isCylinderIntersection_iff`). After a player writes a
bit, the inputs consistent with the blackboard so far still form a cylinder intersection, so the
inputs reaching a leaf of a protocol form a cylinder intersection, on which the output is constant.

The *discrepancy* of `f : (∀ i, X i) → Bool` under a distribution `ν` on inputs is the largest
imbalance `|ν(C ∩ f⁻¹ false) - ν(C ∩ f⁻¹ true)|` over cylinder intersections `C`
(`NOF.discrepancy`) [Jukna, Section 5.5, p. 143][Jukna2012]; discrepancy lower bounds for NOF
protocols go back to Babai, Nisan and Szegedy [BabaiNisanSzegedy1992]. Splitting a cylinder
intersection at each node of the protocol, the correlation under `ν` of `f` with the output of a
protocol of depth `c` on a cylinder intersection is at most `2 ^ c` times the discrepancy
(`NOF.Protocol.abs_sum_mul_signVal_le`). This correlation is `1 - 2 ε` on all inputs, for a protocol
erring with probability `ε` on inputs drawn from `ν` (`NOF.Protocol.sum_mul_signVal_eq`). Hence a
protocol sending `c` bits with error `1 / 2 - γ` under `ν` has `2 γ ≤ 2 ^ c disc_ν(f)`
(`NOF.Protocol.two_mul_le_two_pow_mul_discrepancy`), and by averaging the same holds for
public-coin protocols with error `1 / 2 - γ` on every input
(`NOF.PublicCoin.two_mul_le_two_pow_mul_discrepancy`). For protocols computing `f` exactly this is
`c ≥ log₂ (1 / disc_ν(f))` (`NOF.Protocol.one_le_two_pow_mul_discrepancy`).

## Main definitions

* `Cslib.Communication.NOF.IsCylinder`, `Cslib.Communication.NOF.IsCylinderIntersection`:
  cylinders and cylinder intersections.
* `Cslib.Communication.NOF.cylinderIntersection`: the cylinder intersection of a family of tests.
* `Cslib.Communication.NOF.discrepancy`: the discrepancy of a Boolean function under a
  distribution.

## Main results

* `Cslib.Communication.NOF.Protocol.isCylinderIntersection_leaf`: the inputs reaching a leaf of a
  protocol form a cylinder intersection.
* `Cslib.Communication.NOF.isCylinderIntersection_iff`: cylinder intersections are the sets
  `cylinderIntersection φ`.
* `Cslib.Communication.NOF.Protocol.abs_sum_mul_signVal_le`: correlation with a protocol on a
  cylinder intersection.
* `Cslib.Communication.NOF.Protocol.two_mul_le_two_pow_mul_discrepancy`,
  `Cslib.Communication.NOF.PublicCoin.two_mul_le_two_pow_mul_discrepancy`: the discrepancy bound.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [L. Babai, N. Nisan and M. Szegedy, *Multiparty protocols, pseudorandom generators for logspace,
  and time-space trade-offs*][BabaiNisanSzegedy1992]
-/

@[expose] public section

namespace Cslib.Communication.NOF

open Finset BitString Probability

universe u v

variable {ι : Type u} {X : ι → Type v}

/-! ### Cylinder intersections -/

/-- A set of inputs is a *cylinder in the `i`-th dimension* when membership does not depend on the
`i`-th part of the input. -/
def IsCylinder [DecidableEq ι] (i : ι) (C : Set (∀ j, X j)) : Prop :=
  ∀ x (a : X i), Function.update x i a ∈ C ↔ x ∈ C

/-- A *cylinder intersection* is an intersection of cylinders, one in each dimension. -/
def IsCylinderIntersection [DecidableEq ι] (C : Set (∀ j, X j)) : Prop :=
  ∃ D : ι → Set (∀ j, X j), (∀ i, IsCylinder i (D i)) ∧ C = ⋂ i, D i

/-- The cylinder intersection of the tests `φ i`: the inputs `x` such that every player `i` accepts
what they see, `φ i (view i x) = true`. -/
def cylinderIntersection (φ : ∀ i, View X i → Bool) : Set (∀ j, X j) :=
  {x | ∀ i, φ i (view i x) = true}

@[simp] theorem mem_cylinderIntersection {φ : ∀ i, View X i → Bool} {x : ∀ j, X j} :
    x ∈ cylinderIntersection φ ↔ ∀ i, φ i (view i x) = true :=
  Iff.rfl

/-- With finitely many players, membership in a cylinder intersection is decidable. Sums over
cylinder intersections use this instance for every index type, including `Fin k`. -/
instance decidableMemCylinderIntersection [Fintype ι] (φ : ∀ i, View X i → Bool) :
    DecidablePred (· ∈ cylinderIntersection φ) :=
  fun x => Fintype.decidableForallFintype (α := ι) (p := fun i => φ i (view i x) = true)

@[simp] theorem cylinderIntersection_true :
    cylinderIntersection (fun _ _ => true : ∀ i, View X i → Bool) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ => rfl

/-- **Cylinder intersections are the sets of inputs passing a test of every player**: membership in
a cylinder in the `i`-th dimension is determined by what player `i` sees. -/
theorem isCylinderIntersection_iff [DecidableEq ι] {C : Set (∀ j, X j)} :
    IsCylinderIntersection C ↔ ∃ φ : ∀ i, View X i → Bool, C = cylinderIntersection φ := by
  classical
  constructor
  · rintro ⟨D, hD, rfl⟩
    refine ⟨fun i v => decide (∃ y ∈ D i, view i y = v), Set.ext fun x => ?_⟩
    simp only [Set.mem_iInter, mem_cylinderIntersection, decide_eq_true_eq]
    refine forall_congr' fun i => ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => ?_⟩
    have hxy : Function.update y i (x i) = x := funext fun j =>
      if hj : j = i then hj ▸ Function.update_self ..
      else (Function.update_of_ne hj ..).trans (congrFun hyx ⟨j, hj⟩)
    exact hxy ▸ (hD i y (x i)).mpr hy
  · rintro ⟨φ, rfl⟩
    exact ⟨fun i => {x | φ i (view i x) = true},
      fun _ _ _ => by simp only [Set.mem_ofPred_eq, view_update_self], by ext; simp⟩

/-- **Leaves are cylinder intersections**: the inputs reaching a given leaf form a cylinder
intersection. -/
theorem Protocol.isCylinderIntersection_leaf [DecidableEq ι] {Z : Type*} (p : Protocol X Z)
    (l : Fin p.leafCount) : IsCylinderIntersection {x | p.leaf x = l} := by
  refine ⟨fun i => {x | ∃ y, p.leaf y = l ∧ view i y = view i x},
    fun _ _ _ => by simp only [Set.mem_ofPred_eq, view_update_self], Set.ext fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  refine ⟨fun hx i => ⟨x, hx, rfl⟩, fun hx => ?_⟩
  choose y hy hview using hx
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · have := p.leafCount_eq_one_of_isEmpty
    exact Fin.ext (by have := (p.leaf x).isLt; have := l.isLt; omega)
  · rw [p.leaf_eq_of_view_eq hview (fun j j' => (hy j).trans (hy j').symm) i, hy i]

/-! ### Discrepancy -/

section Discrepancy

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]

/-- The *discrepancy* of `f : (∀ i, X i) → Bool` under a distribution `ν` on inputs: the largest
imbalance `|ν(C ∩ f⁻¹ false) - ν(C ∩ f⁻¹ true)|` of `f` on a cylinder intersection
`C = cylinderIntersection φ`, written as the signed sum `|∑_{x ∈ C} ν(x) (-1)^{f x}|`. -/
noncomputable def discrepancy (ν : PMF (∀ i, X i)) (f : (∀ i, X i) → Bool) : ℝ :=
  ⨆ φ : ∀ i, View X i → Bool,
    |∑ x with x ∈ cylinderIntersection φ, (ν x).toReal * signVal (f x)|

variable {ν : PMF (∀ i, X i)} {f : (∀ i, X i) → Bool}

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] in
/-- The signed sum of `f` under `ν` over any set of inputs has absolute value at most one. -/
theorem abs_sum_mul_signVal_le_one {α : Type*} [Finite α] (ν : PMF α) (f : α → Bool)
    (s : Finset α) : |∑ x ∈ s, (ν x).toReal * signVal (f x)| ≤ 1 := by
  have := Fintype.ofFinite α
  refine (abs_sum_le_sum_abs _ _).trans <| (sum_congr rfl fun x _ => ?_).trans_le <|
    (sum_le_univ_sum_of_nonneg fun _ => ENNReal.toReal_nonneg).trans_eq (PMF.sum_toReal ν)
  rw [abs_mul, abs_signVal, mul_one, abs_of_nonneg ENNReal.toReal_nonneg]

theorem abs_sum_le_discrepancy (ν : PMF (∀ i, X i)) (f : (∀ i, X i) → Bool)
    (φ : ∀ i, View X i → Bool) :
    |∑ x with x ∈ cylinderIntersection φ, (ν x).toReal * signVal (f x)| ≤ discrepancy ν f :=
  le_ciSup (f := fun φ : ∀ i, View X i → Bool =>
      |∑ x with x ∈ cylinderIntersection φ, (ν x).toReal * signVal (f x)|)
    ⟨1, Set.forall_mem_range.mpr fun _ => abs_sum_mul_signVal_le_one ν f _⟩ φ

theorem discrepancy_nonneg : 0 ≤ discrepancy ν f :=
  (abs_nonneg _).trans (abs_sum_le_discrepancy ν f fun _ _ => true)

theorem discrepancy_le_one : discrepancy ν f ≤ 1 :=
  ciSup_le fun _ => abs_sum_mul_signVal_le_one ν f _

/-- The discrepancy is attained on some cylinder intersection. -/
theorem exists_abs_sum_eq_discrepancy (ν : PMF (∀ i, X i)) (f : (∀ i, X i) → Bool) :
    ∃ φ : ∀ i, View X i → Bool,
      |∑ x with x ∈ cylinderIntersection φ, (ν x).toReal * signVal (f x)| = discrepancy ν f :=
  exists_eq_ciSup_of_finite

/-! ### The discrepancy bound -/

namespace Protocol

/-- **Correlation with a protocol on a cylinder intersection**: on the cylinder intersection of the
tests `φ`, the correlation under `ν` of `f` with the output of a protocol is at most `2 ^ depth`
times the discrepancy of `f` under `ν`. The bit written at each node splits the cylinder
intersection into two. -/
theorem abs_sum_mul_signVal_le (p : Protocol X Bool) (ν : PMF (∀ i, X i))
    (f : (∀ i, X i) → Bool) (φ : ∀ i, View X i → Bool) :
    |∑ x with x ∈ cylinderIntersection φ,
        (ν x).toReal * signVal (f x) * signVal (p.run x)| ≤ 2 ^ p.depth * discrepancy ν f := by
  induction p generalizing φ with
  | output z =>
    simp only [run_output, depth_output, pow_zero, one_mul]
    rw [← sum_mul, abs_mul, abs_signVal, mul_one]
    exact abs_sum_le_discrepancy ν f φ
  | speak i send p₀ p₁ ih₀ ih₁ =>
    let ψ (b : Bool) : ∀ j, View X j → Bool :=
      Function.update φ i fun v => φ i v && (send v == b)
    have hψ (b : Bool) (x : ∀ j, X j) :
        x ∈ cylinderIntersection (ψ b) ↔
          x ∈ cylinderIntersection φ ∧ send (view i x) = b := by
      simp only [mem_cylinderIntersection, ψ,
        Function.forall_update_iff φ (p := fun j (g : View X j → Bool) => g (view j x) = true),
        Bool.and_eq_true, beq_iff_eq]
      exact ⟨fun ⟨⟨hi, hb⟩, hne⟩ => ⟨fun j => if hj : j = i then hj ▸ hi else hne j hj, hb⟩,
        fun ⟨h, hb⟩ => ⟨⟨h i, hb⟩, fun j _ => h j⟩⟩
    have hsplit : ∑ x with x ∈ cylinderIntersection φ,
          (ν x).toReal * signVal (f x) * signVal ((speak i send p₀ p₁).run x) =
        ∑ x with x ∈ cylinderIntersection (ψ false),
            (ν x).toReal * signVal (f x) * signVal (p₀.run x) +
          ∑ x with x ∈ cylinderIntersection (ψ true),
            (ν x).toReal * signVal (f x) * signVal (p₁.run x) := by
      simp only [sum_filter, hψ, ← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ cylinderIntersection φ <;> cases hs : send (view i x) <;> simp [hx, hs]
    have hD : 0 ≤ discrepancy ν f := discrepancy_nonneg
    have h₀ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (a := (2 : ℝ)) one_le_two (le_max_left p₀.depth p₁.depth)) hD
    have h₁ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (a := (2 : ℝ)) one_le_two (le_max_right p₀.depth p₁.depth)) hD
    rw [hsplit, depth_speak, pow_succ]
    linarith [abs_add_le (∑ x with x ∈ cylinderIntersection (ψ false),
        (ν x).toReal * signVal (f x) * signVal (p₀.run x))
      (∑ x with x ∈ cylinderIntersection (ψ true),
        (ν x).toReal * signVal (f x) * signVal (p₁.run x)),
      ih₀ (ψ false), ih₁ (ψ true)]

/-- The correlation under `ν` of `f` with the output of a protocol is `1 - 2 ε`, where `ε` is the
probability that the protocol errs on inputs drawn from `ν`. -/
theorem sum_mul_signVal_eq (p : Protocol X Bool) (ν : PMF (∀ i, X i)) (f : (∀ i, X i) → Bool) :
    ∑ x, (ν x).toReal * signVal (f x) * signVal (p.run x) =
      1 - 2 * p.distributionalError ν (fun x b => f x = b) := by
  classical
  rw [distributionalError, PMF.errorProb_eq_sum, ← PMF.sum_toReal ν, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_assoc, signVal_mul_signVal]
  by_cases h : f x = p.run x <;> simp only [h, ite_true, ite_false] <;> ring

/-- **The discrepancy bound** for deterministic protocols, generalising
[Jukna, Section 5.5, p. 143][Jukna2012] (stated there for the uniform distribution and exact
protocols) to any distribution and advantage, as in [BabaiNisanSzegedy1992]: a protocol erring
with probability at most `1 / 2 - γ` on inputs drawn from `ν` has `2 γ ≤ 2 ^ depth · disc_ν(f)`. -/
theorem two_mul_le_two_pow_mul_discrepancy (p : Protocol X Bool) {γ : ℝ}
    (hp : p.distributionalError ν (fun x b => f x = b) ≤ 1 / 2 - γ) :
    2 * γ ≤ 2 ^ p.depth * discrepancy ν f := by
  have h := p.abs_sum_mul_signVal_le ν f fun _ _ => true
  simp only [cylinderIntersection_true, Set.mem_univ, filter_true, p.sum_mul_signVal_eq] at h
  exact (le_trans (by linarith) (le_abs_self _)).trans h

/-- **The discrepancy bound for exact protocols**: a protocol computing `f` has
`1 ≤ 2 ^ depth · disc_ν(f)`, that is, it sends at least `log₂ (1 / disc_ν(f))` bits. -/
theorem one_le_two_pow_mul_discrepancy {p : Protocol X Bool} (hp : p.run = f)
    (ν : PMF (∀ i, X i)) : 1 ≤ 2 ^ p.depth * discrepancy ν f := by
  have := p.two_mul_le_two_pow_mul_discrepancy (ν := ν) (f := f) (γ := 1 / 2)
    (by simp [distributionalError, PMF.errorProb, hp])
  linarith

end Protocol

/-- **The discrepancy bound** for exact protocols: if `f` has communication complexity at most `c`,
then `1 ≤ 2 ^ c · disc_ν(f)` for every distribution `ν`. -/
theorem Protocol.one_le_two_pow_mul_discrepancy_of_ecomplexityFun_le {c : ℕ}
    (h : Protocol.ecomplexityFun f ≤ c) (ν : PMF (∀ i, X i)) :
    1 ≤ 2 ^ c * discrepancy ν f := by
  obtain ⟨p, hp, hc⟩ := Protocol.ecomplexityFun_le_iff.mp h
  exact (p.one_le_two_pow_mul_discrepancy hp ν).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hc) discrepancy_nonneg)

namespace PublicCoin

/-- **The discrepancy bound** for public-coin protocols: a public-coin protocol sending at most `c`
bits and computing `f` with error at most `1 / 2 - γ` on every input has
`2 γ ≤ 2 ^ c · disc_ν(f)` for every distribution `ν`. -/
theorem Solves.two_mul_le_two_pow_mul_discrepancy {μ : PublicCoin X Bool} {γ : ℝ} {c : ℕ}
    (hμ : μ.Solves (1 / 2 - γ) (fun x b => f x = b) Set.univ) (hc : μ.depth ≤ c)
    (ν : PMF (∀ i, X i)) : 2 * γ ≤ 2 ^ c * discrepancy ν f := by
  obtain ⟨p, hp, herr⟩ := hμ.exists_distributionalError_le ν fun _ _ => trivial
  have hd : p.depth ≤ c := by exact_mod_cast (depth_le_depth hp).trans hc
  exact (p.two_mul_le_two_pow_mul_discrepancy herr).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hd) discrepancy_nonneg)

/-- **The discrepancy bound**, generalising [Jukna, Section 5.5, p. 143][Jukna2012] (stated there
for the uniform distribution) [BabaiNisanSzegedy1992]: if `f` has public-coin
communication complexity at most `c` with error `1 / 2 - γ`, then `2 γ ≤ 2 ^ c · disc_ν(f)` for
every distribution `ν`. -/
theorem two_mul_le_two_pow_mul_discrepancy {γ : ℝ} {c : ℕ}
    (h : ecomplexityFun (1 / 2 - γ) f ≤ c) (ν : PMF (∀ i, X i)) :
    2 * γ ≤ 2 ^ c * discrepancy ν f := by
  obtain ⟨μ, hμ, hc⟩ := ecomplexity_le_iff.mp h
  exact hμ.two_mul_le_two_pow_mul_discrepancy hc ν

end PublicCoin

end Discrepancy

end Cslib.Communication.NOF
