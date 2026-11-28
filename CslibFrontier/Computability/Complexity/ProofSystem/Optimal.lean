/-
Copyright (c) 2026 Josh Liebow-Feeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Liebow-Feeser
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.ProofSystem
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Reduction.Isomorphism.Paddable
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.SAT.Paddable
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Optimal and p-optimal proof systems

Following [Krajíček and Pudlák][KrajicekPudlak1989], a proof system `P` for a set `L` is *optimal*
(`Cslib.Complexity.ProofSystem.IsOptimal`) when it simulates every proof system for `L`, and
*p-optimal* (`Cslib.Complexity.ProofSystem.IsPOptimal`) when it p-simulates every proof system for
`L`.

Any two proof systems `P` and `Q` for `L` admit a combined proof system `P.join Q` that routes a
proof word to `P` or `Q` according to its leading tag bit, witnessing that `Simulates` and
`PSimulates` are directed preorders with binary joins
(`Cslib.Complexity.ProofSystem.pSimulates_join_iff`,
`Cslib.Complexity.ProofSystem.simulates_join_iff`). Every polynomially bounded proof system is
optimal (`Cslib.Complexity.ProofSystem.PolynomiallyBounded.isOptimal`), so when an optimal system
exists, it is polynomially bounded if and only if some proof system is polynomially bounded — and
for `UNSAT`, if and only if `NP = coNP`
(`Cslib.Complexity.ProofSystem.IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP`).

An optimal proof system `P` for `L` proves every `NP` subset `X ⊆ L` with proofs of length
polynomial in the encoded instance length
(`Cslib.Complexity.ProofSystem.IsOptimal.polyBounded_on_NP_subset`). For any paddable decodable
language `L` (`Cslib.Complexity.Paddable`), the converse also holds
(`Cslib.Complexity.ProofSystem.exists_isOptimal_iff_of_paddable`), specializing via
`Cslib.Complexity.UNSAT_paddable` to the full `(2) ↔ (3)` equivalence of
[KrajicekPudlak1989, Theorem 2.1(i)] for `UNSAT`
(`Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_iff`).

## Source-to-Lean mapping

* **Simulation direction and the order behind `join`:** In [KrajicekPudlak1989, §0, p. 1063],
  `P ≤ Q` means "`P` simulates `Q`", so a common simulator is a common lower bound and an optimal
  system is a least element. In `CslibFrontier.Computability.Complexity.ProofSystem`,
  `P.Simulates Q` and `P.PSimulates Q` likewise place the simulating system on the left. To view
  `P.join Q` as a binary join (least upper bound) and optimal systems as greatest elements, define
  the reversed order `P ≤ Q` by `Q.Simulates P` (respectively `Q.PSimulates P`), which reverses the
  source's ordering `≤`.
* **`UNSAT` vs. `TAUT`:** [KrajicekPudlak1989] states propositional proof systems for `TAUT`.
  `Cslib.Complexity.ProofSystem.IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP`,
  `Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_of_NP_eq_coNP`, and
  `Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_iff` state the `UNSAT` (`encCNF`) refutation
  analogues, using `Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded` and
  `Cslib.Complexity.UNSAT_paddable` without transporting a proof system between `TAUT` and `UNSAT`.
* **Direct source content vs. derived library facts:** Common-bound existence (`join` with
  `join_simulates_left`, `join_simulates_right`), the `(2) ↔ (3)` equivalence of Theorem 2.1(i)
  (`IsOptimal.polyBounded_on_NP_subset`, `exists_isOptimal_iff_of_paddable`, and
  `exists_isOptimal_UNSAT_iff`, §2, pp. 1066–1067; proved in the paper via first-order arithmetic
  consistency statements `(3) → (5) → (4) → (1) → (2)` on pp. 1070–1071, and proved directly here
  for any paddable decodable language by padding proof systems into `NP` subsets), and the `UNSAT`
  analogue of §0's `NP = coNP` observation reflect statements in [KrajicekPudlak1989]. Universal
  join properties (`pSimulates_join_iff`, `simulates_join_iff`), fixed-system consequences
  (`IsPOptimal.isOptimal`, `PolynomiallyBounded.isOptimal`, closure under simulation), and the
  `NP` / `P` existence facts (`exists_isPOptimal_of_mem_P`, etc.) are derived library facts built
  on the existing API.
* **Existence boundary:** Unconditional existence of an optimal or p-optimal proof system for
  `UNSAT` is an open problem ([KrajicekPudlak1989, §0, p. 1063]) and is not claimed.

## Main definitions

* `Cslib.Complexity.ProofSystem.IsOptimal`: optimality with respect to `Simulates`.
* `Cslib.Complexity.ProofSystem.IsPOptimal`: p-optimality with respect to `PSimulates`.
* `Cslib.Complexity.ProofSystem.join`: tagged disjoint-union proof system combining two systems.
* `Cslib.Complexity.ProofSystem.ofDecider`: proof system built from a polynomial-time decider.

## Main results

* `Cslib.Complexity.ProofSystem.pSimulates_join_iff`,
  `Cslib.Complexity.ProofSystem.simulates_join_iff`: `join` is a binary join for both
  `PSimulates` and `Simulates`.
* `Cslib.Complexity.ProofSystem.IsPOptimal.isOptimal`,
  `Cslib.Complexity.ProofSystem.IsOptimal.of_simulates`,
  `Cslib.Complexity.ProofSystem.IsPOptimal.of_pSimulates`: closure and uniqueness up to mutual
  simulation.
* `Cslib.Complexity.ProofSystem.PolynomiallyBounded.isOptimal`: every polynomially bounded proof
  system is optimal.
* `Cslib.Complexity.ProofSystem.IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP`: an optimal
  refutation system for `UNSAT` is polynomially bounded iff `NP = coNP`.
* `Cslib.Complexity.ProofSystem.IsOptimal.polyBounded_on_NP_subset`: forward `(2) → (3)` direction
  of [KrajicekPudlak1989, Theorem 2.1(i)].
* `Cslib.Complexity.ProofSystem.exists_isOptimal_iff_of_paddable`,
  `Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_iff`: full `(2) ↔ (3)` equivalence of
  [KrajicekPudlak1989, Theorem 2.1(i)] for paddable decodable languages and for `UNSAT`.
* `Cslib.Complexity.ProofSystem.exists_isOptimal_of_mem_NP`,
  `Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_of_NP_eq_coNP`,
  `Cslib.Complexity.ProofSystem.exists_isPOptimal_of_mem_P`: conditional existence results.

## References

* [J. Krajíček, P. Pudlák, *Propositional Proof Systems, the Consistency of First Order Theories
  and the Complexity of Computations*][KrajicekPudlak1989], §0 (p. 1063), §1 (pp. 1065–1066), and
  §2, Statements (2), (3), (7) and Theorem 2.1(i) (pp. 1066–1067)
* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
-/

public section

namespace Cslib.Complexity.ProofSystem

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {L : Set α}

/-! ### Optimality and p-optimality -/

/-- `P` is an **optimal** proof system for `L` [KrajicekPudlak1989, §0, p. 1063; §2, Statement (2),
p. 1066]: it simulates every proof system for `L`. In [KrajicekPudlak1989], `P ≤ Q` denotes that
`P` simulates `Q`, so an optimal system is a least element of `≤`; here `P.Simulates Q` places the
simulating system on the left. -/
@[expose]
def IsOptimal (P : ProofSystem enc L) : Prop :=
  ∀ Q : ProofSystem enc L, P.Simulates Q

/-- `P` is a **p-optimal** proof system for `L` [KrajicekPudlak1989, §2, Statement (7), p. 1067]:
it p-simulates every proof system for `L`. -/
@[expose]
def IsPOptimal (P : ProofSystem enc L) : Prop :=
  ∀ Q : ProofSystem enc L, P.PSimulates Q

/-- Every p-optimal proof system is optimal. This is a derived fixed-system consequence of the
definitions and `PSimulates.simulates` (underlying the existential `(7) → (2)` implication in
[KrajicekPudlak1989, Theorem 2.1(i)]; Theorem 2.1(ii) treats equivalences among `(6)–(9)`). -/
theorem IsPOptimal.isOptimal {P : ProofSystem enc L} (hP : P.IsPOptimal) : P.IsOptimal :=
  fun Q => (hP Q).simulates

/-- Optimality transfers upward along simulation. -/
theorem IsOptimal.of_simulates {P Q : ProofSystem enc L} (hP : P.IsOptimal) (hQP : Q.Simulates P) :
    Q.IsOptimal :=
  fun R => hQP.trans (hP R)

/-- p-optimality transfers upward along p-simulation. -/
theorem IsPOptimal.of_pSimulates {P Q : ProofSystem enc L} (hP : P.IsPOptimal)
    (hQP : Q.PSimulates P) : Q.IsPOptimal :=
  fun R => hQP.trans (hP R)

/-- Relative to an optimal proof system `P`, a system `Q` is optimal iff it simulates `P`. -/
theorem IsOptimal.simulates_iff {P : ProofSystem enc L} (hP : P.IsOptimal)
    (Q : ProofSystem enc L) : Q.IsOptimal ↔ Q.Simulates P :=
  ⟨fun hQ => hQ P, hP.of_simulates⟩

/-- Relative to a p-optimal proof system `P`, a system `Q` is p-optimal iff it p-simulates `P`. -/
theorem IsPOptimal.pSimulates_iff {P : ProofSystem enc L} (hP : P.IsPOptimal)
    (Q : ProofSystem enc L) : Q.IsPOptimal ↔ Q.PSimulates P :=
  ⟨fun hQ => hQ P, hP.of_pSimulates⟩

/-- Any two optimal proof systems for `L` mutually simulate each other. -/
theorem IsOptimal.mutual_simulates {P Q : ProofSystem enc L} (hP : P.IsOptimal)
    (hQ : Q.IsOptimal) : P.Simulates Q ∧ Q.Simulates P :=
  ⟨hP Q, hQ P⟩

/-- Any two p-optimal proof systems for `L` mutually p-simulate each other. -/
theorem IsPOptimal.mutual_pSimulates {P Q : ProofSystem enc L} (hP : P.IsPOptimal)
    (hQ : Q.IsPOptimal) : P.PSimulates Q ∧ Q.PSimulates P :=
  ⟨hP Q, hQ P⟩

/-! ### Tagged join of two proof systems -/

/-- Combine a proof system `P` for `L` with a proof system `Q` for a subset `X ⊆ L` by tagging
proofs with a leading bit (`false` for `P`, `true` for `Q`, with `[]` defaulting to `P []`). -/
private def joinSubset (P : ProofSystem enc L) {X : Set α} (hXL : X ⊆ L)
    (Q : ProofSystem enc X) : ProofSystem enc L where
  toFun π := if π.headD false then Q (π.drop 1) else P (π.drop 1)
  computable :=
    (headD (encA := encBool) (encL := encBits) false).ite'
      (Q.computable.comp (bitsDropWithInput id' (const 1)))
      (P.computable.comp (bitsDropWithInput id' (const 1)))
  range_eq := by
    refine Set.Subset.antisymm ?_ fun a ha => ?_
    · rintro _ ⟨π, rfl⟩
      dsimp only
      split_ifs
      · exact hXL (Q.mem _)
      · exact P.mem _
    · obtain ⟨π, rfl⟩ := P.exists_eq ha
      exact ⟨false :: π, rfl⟩

/-- The **tagged join** of two proof systems `P` and `Q` for `L`: a proof `false :: π` is evaluated
by `P`, a proof `true :: π` is evaluated by `Q`, and the empty word defaults to `P []`. Defining the
order `A ≤ B` by `B.PSimulates A` (or `B.Simulates A`), which reverses the ordering of
[KrajicekPudlak1989, §0, p. 1063], `P.join Q` is a least upper bound (join) of `P` and `Q`,
corresponding to the source's common lower bound. -/
def join (P Q : ProofSystem enc L) : ProofSystem enc L :=
  joinSubset P Set.Subset.rfl Q

@[simp]
theorem join_false_cons (P Q : ProofSystem enc L) (π : List Bool) :
    P.join Q (false :: π) = P π := by
  rfl

@[simp]
theorem join_true_cons (P Q : ProofSystem enc L) (π : List Bool) :
    P.join Q (true :: π) = Q π := by
  rfl

@[simp]
theorem join_nil (P Q : ProofSystem enc L) : P.join Q [] = P [] := by
  rfl

/-- `P.join Q` p-simulates `P` by prepending the tag bit `false`. -/
theorem join_pSimulates_left (P Q : ProofSystem enc L) : (P.join Q).PSimulates P :=
  ⟨fun π => [false] ++ π, bitsAppend (const [false]) id', fun _ => rfl⟩

/-- `P.join Q` p-simulates `Q` by prepending the tag bit `true`. -/
theorem join_pSimulates_right (P Q : ProofSystem enc L) : (P.join Q).PSimulates Q :=
  ⟨fun π => [true] ++ π, bitsAppend (const [true]) id', fun _ => rfl⟩

/-- `P.join Q` simulates `P`. -/
theorem join_simulates_left (P Q : ProofSystem enc L) : (P.join Q).Simulates P :=
  (join_pSimulates_left P Q).simulates

/-- `P.join Q` simulates `Q`. -/
theorem join_simulates_right (P Q : ProofSystem enc L) : (P.join Q).Simulates Q :=
  (join_pSimulates_right P Q).simulates

/-- `P.join Q` is a binary join (least upper bound) in the order `A ≤ B` given by
`B.PSimulates A`. -/
theorem pSimulates_join_iff {R P Q : ProofSystem enc L} :
    R.PSimulates (P.join Q) ↔ R.PSimulates P ∧ R.PSimulates Q := by
  refine ⟨fun h => ⟨h.trans (join_pSimulates_left P Q), h.trans (join_pSimulates_right P Q)⟩, ?_⟩
  rintro ⟨⟨t₁, ht₁, hRP⟩, ⟨t₂, ht₂, hRQ⟩⟩
  refine ⟨fun π => if π.headD false then t₂ (π.drop 1) else t₁ (π.drop 1), ?_, fun π => ?_⟩
  · exact (headD (encA := encBool) (encL := encBits) false).ite'
      (ht₂.comp (bitsDropWithInput id' (const 1)))
      (ht₁.comp (bitsDropWithInput id' (const 1)))
  · change R (if π.headD false then t₂ (π.drop 1) else t₁ (π.drop 1)) =
      if π.headD false then Q (π.drop 1) else P (π.drop 1)
    split_ifs
    · exact hRQ _
    · exact hRP _

/-- `P.join Q` is a binary join (least upper bound) in the order `A ≤ B` given by
`B.Simulates A`. -/
theorem simulates_join_iff {R P Q : ProofSystem enc L} :
    R.Simulates (P.join Q) ↔ R.Simulates P ∧ R.Simulates Q := by
  refine ⟨fun h => ⟨h.trans (join_simulates_left P Q), h.trans (join_simulates_right P Q)⟩, ?_⟩
  rintro ⟨⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩⟩
  refine ⟨p₁ + p₂, fun π => ?_⟩
  have hdrop : (π.drop 1).length ≤ π.length := by simp
  change ∃ π', R π' = (if π.headD false then Q (π.drop 1) else P (π.drop 1)) ∧
    π'.length ≤ (p₁ + p₂).eval π.length
  split_ifs
  · obtain ⟨π', hπ', hlen⟩ := hp₂ (π.drop 1)
    exact ⟨π', hπ', hlen.trans ((p₂.eval_mono hdrop).trans (by
      rw [Polynomial.eval_add]
      exact Nat.le_add_left _ _))⟩
  · obtain ⟨π', hπ', hlen⟩ := hp₁ (π.drop 1)
    exact ⟨π', hπ', hlen.trans ((p₁.eval_mono hdrop).trans (by
      rw [Polynomial.eval_add]
      exact Nat.le_add_right _ _))⟩

/-! ### Polynomial bounds, Cook–Reckhow, and `NP` subsets -/

/-- Every polynomially bounded proof system is optimal: since every proof system `Q` computes
`Q π` in polynomial time, `(enc (Q π)).length` is polynomially bounded in `π.length`. -/
theorem PolynomiallyBounded.isOptimal {P : ProofSystem enc L} (hP : P.PolynomiallyBounded) :
    P.IsOptimal := by
  obtain ⟨p, hp⟩ := hP
  intro Q
  obtain ⟨c, d, hle⟩ := Q.computable.polyBounded_length.exists_le
  refine ⟨p.comp (.C c * (.X + 1) ^ d), fun π => ?_⟩
  obtain ⟨π', hπ', hlen⟩ := hp (Q π) (Q.mem π)
  refine ⟨π', hπ', ?_⟩
  rw [Polynomial.eval_comp]
  exact hlen.trans (p.eval_mono (by simpa using hle π))

/-- An optimal proof system is polynomially bounded iff some proof system for `L` is polynomially
bounded. -/
theorem IsOptimal.polynomiallyBounded_iff_exists_polynomiallyBounded {P : ProofSystem enc L}
    (hP : P.IsOptimal) :
    P.PolynomiallyBounded ↔ ∃ Q : ProofSystem enc L, Q.PolynomiallyBounded :=
  ⟨fun h => ⟨P, h⟩, fun ⟨Q, hQ⟩ => hQ.of_simulates (hP Q)⟩

/-- For a decodable encoding, an optimal proof system for `L` is polynomially bounded iff
`L ∈ NP enc`. -/
theorem IsOptimal.polynomiallyBounded_iff_mem_NP {P : ProofSystem enc L} (hP : P.IsOptimal)
    (D : Decoder enc) : P.PolynomiallyBounded ↔ L ∈ NP enc := by
  rw [hP.polynomiallyBounded_iff_exists_polynomiallyBounded,
    exists_polynomiallyBounded_iff_mem_NP D P.nonempty]

/-- An optimal refutation system for `UNSAT` is polynomially bounded iff `NP = coNP`: the `UNSAT`
analogue of [KrajicekPudlak1989, §0, p. 1063] (stated there for `TAUT`), obtained from
`Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded` [CookReckhow1979]. -/
theorem IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP {P : ProofSystem encCNF UNSAT}
    (hP : P.IsOptimal) :
    P.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC := by
  rw [hP.polynomiallyBounded_iff_exists_polynomiallyBounded,
    ← NP_eq_coNP_iff_exists_polynomiallyBounded]

/-- **Forward `(2) → (3)` direction of [KrajicekPudlak1989, Theorem 2.1(i)]**: an optimal proof
system `P` for `L` proves every `NP` subset `X ⊆ L` with proofs of length polynomial in the
encoded instance length.

For any paddable decodable language (and in particular for `UNSAT`), the converse `(3) → (2)` also
holds, giving the full `(2) ↔ (3)` equivalence in
`Cslib.Complexity.ProofSystem.exists_isOptimal_iff_of_paddable` and
`Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_iff`. -/
theorem IsOptimal.polyBounded_on_NP_subset {P : ProofSystem enc L} (hP : P.IsOptimal)
    (D : Decoder enc) {X : Set α} (hXL : X ⊆ L) (hX : X ∈ NP enc) :
    ∃ p : Polynomial ℕ, ∀ a ∈ X, ∃ π, P π = a ∧ π.length ≤ p.eval (enc a).length := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · exact ⟨0, fun _ h => h.elim⟩
  · obtain ⟨q, V, hV, hVX⟩ := hX
    let Q := ofVerifier D hV hVX ha₀
    obtain ⟨r, hr⟩ := polynomiallyBounded_ofVerifier D hV hVX ha₀
    obtain ⟨s, hs⟩ := hP (joinSubset P hXL Q)
    refine ⟨s.comp (r + 1), fun a ha => ?_⟩
    obtain ⟨π, hQπ, hlen⟩ := hr a ha
    obtain ⟨π', hPπ', hlen'⟩ := hs (true :: π)
    refine ⟨π', ?_, ?_⟩
    · simpa [joinSubset, Q, hQπ] using hPπ'
    · rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one]
      have hsucc : (true :: π).length ≤ r.eval (enc a).length + 1 := by
        simpa [List.length_cons] using Nat.add_le_add_right hlen 1
      exact hlen'.trans (s.eval_mono hsucc)

/-- **Equivalence `(2) ↔ (3)` of [KrajicekPudlak1989, Theorem 2.1(i)] for paddable decodable
languages**: a paddable language `L` (`Cslib.Complexity.Paddable`) with a total polynomial-time
decoder has an optimal proof system if and only if some proof system for `L` proves every `NP`
subset of `L` with proofs of length polynomial in the encoded instance length.

In [KrajicekPudlak1989, §2–§3, pp. 1066–1067, 1070–1071], `(3) → (2)` is established for `TAUT` via
first-order arithmetic consistency statements `(3) → (5) → (4) → (1) → (2)`. Here we prove the
converse directly from `Paddable`: unpadding `P` yields an optimal system because every proof
system `Q` embeds its pairs `(Q w, w)` into the `NP` subset
`{pad (Q w) (frame (enc (Q w)) ++ w) | w}`. -/
theorem exists_isOptimal_iff_of_paddable (D : Decoder enc) (hL : Paddable enc L) :
    (∃ P : ProofSystem enc L, P.IsOptimal) ↔
      ∃ P : ProofSystem enc L,
        ∀ X : Set α, X ⊆ L → X ∈ NP enc →
          ∃ p : Polynomial ℕ, ∀ a ∈ X, ∃ π, P π = a ∧ π.length ≤ p.eval (enc a).length := by
  refine ⟨fun ⟨P, hP⟩ => ⟨P, fun _ hX hNP => hP.polyBounded_on_NP_subset D hX hNP⟩, ?_⟩
  rintro ⟨P, hP⟩
  classical
  obtain ⟨pad, unpad, hpad, hunpad, hdec, hmem⟩ := hL
  obtain ⟨a₀, ha₀⟩ := P.nonempty
  obtain ⟨_, _, hD⟩ := D.computable
  have hDpoly : ComputableInPolyTime D.decode encBits enc := hD.computableInPolyTime
  let unpadInst : α → α := fun b =>
    let y := unpad b
    let a := D.decode (unframe y)
    if decide (pad a y = b) then a else a₀
  have hunpadInst_poly : ComputableInPolyTime unpadInst enc enc := by
    have ha : ComputableInPolyTime (fun b => D.decode (unframe (unpad b))) enc enc :=
      hDpoly.comp (unframe.comp hunpad)
    exact (decide_eq' (hpad.comp (ha.prod hunpad)) id').ite' ha (const a₀)
  have hunpadInst_pad : ∀ a w, unpadInst (pad a (frame (enc a) ++ w)) = a := by
    intro a w
    simp [unpadInst, hdec, unframe_frame_append, D.decode_enc]
  have hunpadInst_mem : ∀ {b}, b ∈ L → unpadInst b ∈ L := by
    intro b hb
    dsimp only [unpadInst]
    split_ifs with h
    · exact (hmem _ _).1 ((decide_eq_true_eq.mp h).symm ▸ hb)
    · exact ha₀
  let P' : ProofSystem enc L := {
    toFun := fun π => unpadInst (P π)
    computable := hunpadInst_poly.comp P.computable
    range_eq := by
      refine Set.Subset.antisymm ?_ fun a ha => ?_
      · rintro _ ⟨π, rfl⟩
        exact hunpadInst_mem (P.mem π)
      · obtain ⟨π, hπ⟩ := P.exists_eq ((hmem a (frame (enc a) ++ [])).2 ha)
        exact ⟨π, by dsimp only; rw [hπ, hunpadInst_pad a []]⟩
  }
  refine ⟨P', fun Q => ?_⟩
  let embed : List Bool → α := fun w => pad (Q w) (frame (enc (Q w)) ++ w)
  have hembed : ComputableInPolyTime embed encBits enc :=
    hpad.comp (Q.computable.prod (bitsAppend ((bitsFrame enc).comp Q.computable) id'))
  let X : Set α := {b | ∃ w : List Bool, embed w = b}
  have hX_sub : X ⊆ L := by
    rintro _ ⟨w, rfl⟩
    exact (hmem _ _).2 (Q.mem w)
  obtain ⟨cu, du, hcu⟩ := hunpad.polyBounded_length.exists_le
  have hcheck : ComputableInPolyTime (fun x : α × List Bool => decide (embed x.2 = x.1))
      (encPair enc encBits) encBool :=
    decide_eq' (hembed.comp (snd enc encBits)) (fst enc encBits)
  have hX_NP : X ∈ NP enc :=
    mem_NP_of_witness (p := .C cu * (.X + 1) ^ du) Decoder.bits hcheck
      (fun _ _ => decide_eq_true_iff) (by
        rintro b w rfl
        refine ⟨w, rfl, ?_⟩
        have hw : w.length ≤ (unpad (embed w)).length := by
          simp [embed, hdec]
        exact hw.trans (by simpa using hcu (embed w)))
  obtain ⟨p, hp⟩ := hP X hX_sub hX_NP
  obtain ⟨ce, de, hce⟩ := hembed.polyBounded_length.exists_le
  refine ⟨p.comp (.C ce * (.X + 1) ^ de), fun w => ?_⟩
  obtain ⟨π, hPπ, hlen⟩ := hp (embed w) ⟨w, rfl⟩
  refine ⟨π, ?_, ?_⟩
  · change unpadInst (P π) = Q w
    rw [hPπ, hunpadInst_pad]
  · rw [Polynomial.eval_comp]
    exact hlen.trans (p.eval_mono (by simpa using hce w))

/-- **Equivalence `(2) ↔ (3)` of [KrajicekPudlak1989, Theorem 2.1(i)] for `UNSAT`**: `UNSAT` has an
optimal refutation system if and only if some refutation system for `UNSAT` has polynomial-length
refutations on every `NP` subset of `UNSAT`. -/
theorem exists_isOptimal_UNSAT_iff :
    (∃ P : ProofSystem encCNF UNSAT, P.IsOptimal) ↔
      ∃ P : ProofSystem encCNF UNSAT,
        ∀ X : Set (Cslib.Logic.PL.CNF ℕ), X ⊆ UNSAT → X ∈ NP encCNF →
          ∃ p : Polynomial ℕ, ∀ φ ∈ X, ∃ π, P π = φ ∧ π.length ≤ p.eval (encCNF φ).length :=
  exists_isOptimal_iff_of_paddable cnfDecoder UNSAT_paddable

/-! ### Conditional existence of optimal and p-optimal proof systems -/

/-- Every nonempty decodable `NP` set has an optimal proof system. -/
theorem exists_isOptimal_of_mem_NP (D : Decoder enc) (hL : L.Nonempty) (hNP : L ∈ NP enc) :
    ∃ P : ProofSystem enc L, P.IsOptimal := by
  obtain ⟨P, hP⟩ := (exists_polynomiallyBounded_iff_mem_NP D hL).2 hNP
  exact ⟨P, hP.isOptimal⟩

/-- If `NP = coNP`, then `UNSAT` has an optimal refutation system: the `UNSAT` analogue of
[KrajicekPudlak1989, §0, p. 1063], obtained via `NP_eq_coNP_iff_exists_polynomiallyBounded`. -/
theorem exists_isOptimal_UNSAT_of_NP_eq_coNP
    (h : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) :
    ∃ P : ProofSystem encCNF UNSAT, P.IsOptimal := by
  obtain ⟨P, hP⟩ := NP_eq_coNP_iff_exists_polynomiallyBounded.1 h
  exact ⟨P, hP.isOptimal⟩

/-- The **proof system of a polynomial-time decider** `f` for `L`, with a default member `a₀`:
each word is decoded by `D`; if `f` accepts the decoded instance, the word proves it, and
otherwise it proves `a₀`. -/
def ofDecider (D : Decoder enc) {f : α → Bool} (hf : ComputableInPolyTime f enc encBool)
    (hfL : ∀ a, a ∈ L ↔ f a = true) {a₀ : α} (ha₀ : a₀ ∈ L) : ProofSystem enc L where
  toFun π := if f (D.decode π) then D.decode π else a₀
  computable := (hf.comp D.computableInPolyTime).ite' D.computableInPolyTime (const a₀)
  range_eq := by
    refine Set.Subset.antisymm ?_ fun a ha => ?_
    · rintro _ ⟨π, rfl⟩
      dsimp only
      split_ifs with h
      · exact (hfL _).2 h
      · exact ha₀
    · refine ⟨enc a, ?_⟩
      simp [D.decode_enc, (hfL a).1 ha]

/-- In `ofDecider`, the encoding of any member `a ∈ L` proves `a` itself. -/
theorem ofDecider_enc (D : Decoder enc) {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) (hfL : ∀ a, a ∈ L ↔ f a = true)
    {a₀ : α} (ha₀ : a₀ ∈ L) {a : α} (ha : a ∈ L) :
    ofDecider D hf hfL ha₀ (enc a) = a := by
  change (if f (D.decode (enc a)) then D.decode (enc a) else a₀) = a
  simp [D.decode_enc, (hfL a).1 ha]

/-- The proof system of a polynomial-time decider is p-optimal: any proof `π` in any proof system
`Q` is translated in polynomial time to `enc (Q π)`. -/
theorem isPOptimal_ofDecider (D : Decoder enc) {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) (hfL : ∀ a, a ∈ L ↔ f a = true)
    {a₀ : α} (ha₀ : a₀ ∈ L) : (ofDecider D hf hfL ha₀).IsPOptimal := by
  intro Q
  refine ⟨fun π => enc (Q π),
    (of_eq (f := enc) (encOut := encBits) fun _ => rfl).comp Q.computable, fun π => ?_⟩
  exact ofDecider_enc D hf hfL ha₀ (Q.mem π)

/-- Every nonempty decodable set in `P` has a p-optimal proof system. -/
theorem exists_isPOptimal_of_mem_P (D : Decoder enc) (hL : L.Nonempty)
    (hP : L ∈ Complexity.P enc) : ∃ Q : ProofSystem enc L, Q.IsPOptimal := by
  obtain ⟨f, hf, hfL⟩ := hP
  obtain ⟨a₀, ha₀⟩ := hL
  exact ⟨ofDecider D hf hfL ha₀, isPOptimal_ofDecider D hf hfL ha₀⟩

end Cslib.Complexity.ProofSystem
