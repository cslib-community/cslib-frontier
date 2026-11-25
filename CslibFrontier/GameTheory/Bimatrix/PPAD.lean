/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.FNP
public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses
import CslibFrontier.GameTheory.Bimatrix.RationalVertex
import CslibFrontier.GameTheory.Bimatrix.ShapleyOrientation
import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
import CslibFrontier.Computability.Circuit.Rational.Runtime.Point
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Computability.PolyTime.Int.Table
import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

/-!
# Two-player Nash equilibrium is in PPAD

Finding a mixed Nash equilibrium of a two-player bimatrix game with rational payoffs belongs to
`PPAD` [Papadimitriou1994PPAD], [vonStengel2007], Chapter 3.

The encoded game type `BimatrixCode` (under `encBimatrix`), strategy-pair encoding `StrategyPair`
(under `encWitness`), exact rational Nash search relation `BimatrixNash`, and its `FNP` membership
are developed in `CslibFrontier.GameTheory.Bimatrix.FNP`.

The reduction to `EndOfLine` normalizes `(A, B)` to positive integers in `[1, H]`, perturbs the
right-hand sides of the best-response polytopes `(P, Q)` by powers of `K_B = 2 ^ bitBound m n H`,
and walks completely-labelled / `k₀ = 0`-almost-completely-labelled basis pairs `(T₁, T₂)`
represented by `2 * (m + n)` bits (with the artificial origin `(T₁⁰, T₂⁰)` mapped to `0^(2(m+n))`).
Incident half-edges are oriented by Shapley's determinant index (`ShapleyOrientation`), pivoting
without division via `detRows` and `cramerRows`. Every unbalanced non-origin vertex yields an
unperturbed exact rational Nash equilibrium by Cramer rounding (`RationalVertex`), giving a
polynomial-time search reduction to `endOfLineRel` (`BimatrixNash_mem_PPAD`).

## Main definitions

* `Cslib.GameTheory.BimatrixCode.vertexLen`, `Cslib.GameTheory.BimatrixCode.pred`,
  `Cslib.GameTheory.BimatrixCode.succ`: polynomial-time Shapley-oriented Lemke–Howson graph maps.
* `Cslib.GameTheory.BimatrixCode.extractNash`: polynomial-time exact rational Nash witness
  extractor.

## Main results

* `Cslib.GameTheory.BimatrixCode.BimatrixNash.isNash`: witnesses of well-formed codes decode to
  mixed Nash equilibria of `c.toGame`.
* `Cslib.GameTheory.BimatrixCode.extractNash_sound`: every end-of-line witness extracts via
  `extractNash` to a valid rational Nash equilibrium witness.
* `Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_endOfLineRel`,
  `Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_PPAD`: two-player Nash is in `PPAD`.
* `Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_TFNP`,
  `Cslib.GameTheory.BimatrixCode.BimatrixNash_isTotalSearch`,
  `Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_EndOfLine`: totality and
  `EndOfLine` reduction corollaries.

## References

* [C. E. Lemke and J. T. Howson, Jr., *Equilibrium points of bimatrix games*][LemkeHowson1964]
* [L. S. Shapley, *A note on the Lemke–Howson algorithm*][Shapley1974]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Chapter 3
-/

public section

namespace Cslib.GameTheory.BimatrixCode

open Cslib Cslib.BitString Cslib.Circuits.Rational Cslib.Complexity Cslib.GameTheory.BimatrixGame
  Mathlib.Tactic.Matrix Matrix
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Section 1: Positive normalization, vertex encoding, and polytope execution -/

/-- Positive integer shift `1 + ∑ |scaled entries|` ensuring all payoffs are strictly positive. -/
private def shiftVal (c : BimatrixCode) : ℤ :=
  let D := clearScale c
  1 + (c.matA.map fun row => (row.map fun q => |(scaledEntry D q)|).sum).sum +
    (c.matB.map fun row => (row.map fun q => |(scaledEntry D q)|).sum).sum

/-- Positive entry upper bound `H = 2 * (shiftVal c).natAbs`. -/
private def HVal (c : BimatrixCode) : ℕ :=
  2 * (shiftVal c).natAbs

/-- Positive integer normalized payoff matrices `posMatWith D S M`. -/
private def posMatWith (D S : ℤ) (M : List (List ℚ)) : List (List ℤ) :=
  M.map fun row => row.map fun q => scaledEntry D q + S

/-- Positive integer normalized payoff matrices `posMat c M`. -/
private def posMat (c : BimatrixCode) (M : List (List ℚ)) : List (List ℤ) :=
  posMatWith (clearScale c) (shiftVal c) M

@[local fun_prop]
private theorem shiftVal_polytime :
    ComputableInPolyTime shiftVal encBimatrix encIntBin := by
  unfold shiftVal
  have habs : ∀ {α : Type} {encIn : α ↪ List Bool} {f : α → ℤ},
      ComputableInPolyTime f encIn encIntBin →
        ComputableInPolyTime (fun x => |f x|) encIn encIntBin := by
    intro α encIn f hf
    have hc : ComputableInPolyTime (fun x => ((f x).natAbs : ℤ)) encIn encIntBin := by fun_prop
    simpa only [Int.natCast_natAbs] using hc
  have hrow1 : ComputableInPolyTime
      (fun p : BimatrixCode × List ℚ => (p.2.map fun q => |scaledEntry (clearScale p.1) q|).sum)
      (encPair encBimatrix (encList encRat)) encIntBin := by
    refine intBin_sum.comp (mapWithInput (encA := encRat) (snd _ _) ?_)
    exact habs (scaledEntry_polytime
      (clearScale_polytime.comp ((fst _ _).comp (fst _ _))) (snd _ _))
  have hs1 : ComputableInPolyTime
      (fun c : BimatrixCode =>
        (c.matA.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum)
      encBimatrix encIntBin :=
    intBin_sum.comp (mapWithInput (encA := encList encRat) (encBimatrix_matA_polyTime .id') hrow1)
  have hs2 : ComputableInPolyTime
      (fun c : BimatrixCode =>
        (c.matB.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum)
      encBimatrix encIntBin :=
    intBin_sum.comp (mapWithInput (encA := encList encRat) (encBimatrix_matB_polyTime .id') hrow1)
  exact intBin_add' (intBin_add' (const 1) hs1) hs2

@[local fun_prop]
private theorem HVal_polytime :
    ComputableInPolyTime HVal encBimatrix encNat := by
  unfold HVal
  fun_prop

private theorem posMatWith_polytime {α : Type} {encIn : α ↪ List Bool}
    {D S : α → ℤ} {M : α → List (List ℚ)}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hS : ComputableInPolyTime S encIn encIntBin)
    (hM : ComputableInPolyTime M encIn (encList (encList encRat))) :
    ComputableInPolyTime (fun x => posMatWith (D x) (S x) (M x)) encIn encIntTable := by
  have hrow : ComputableInPolyTime
      (fun p : (ℤ × ℤ) × List ℚ => p.2.map fun q => scaledEntry p.1.1 q + p.1.2)
      (encPair (encPair encIntBin encIntBin) (encList encRat)) (encList encIntBin) := by
    refine mapWithInput (encA := encRat) (snd _ _) ?_
    exact intBin_add'
      (scaledEntry_polytime ((fst encIntBin encIntBin).comp ((fst _ _).comp (fst _ _))) (snd _ _))
      ((snd encIntBin encIntBin).comp ((fst _ _).comp (fst _ _)))
  have hm : ComputableInPolyTime
      (fun x => (M x).map fun row => row.map fun q => scaledEntry (D x) q + S x)
      encIn encIntTable := by
    refine mapWithInput (encA := encList encRat) hM ?_
    exact hrow.comp (((hD.prod hS).comp (fst _ _)).prod (snd _ _))
  simpa only [posMatWith] using hm

private theorem posMatA_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => posMat c c.matA) encBimatrix encIntTable :=
  posMatWith_polytime clearScale_polytime shiftVal_polytime (encBimatrix_matA_polyTime .id')

private theorem posMatB_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => posMat c c.matB) encBimatrix encIntTable :=
  posMatWith_polytime clearScale_polytime shiftVal_polytime (encBimatrix_matB_polyTime .id')

@[instance_reducible]
private def sumLinearOrder (m n : ℕ) : LinearOrder (Fin m ⊕ Fin n) :=
  LinearOrder.lift' finSumFinEquiv finSumFinEquiv.injective

private local instance (priority := high) instLinearOrderFinSumPPAD (m n : ℕ) :
    LinearOrder (Fin m ⊕ Fin n) :=
  sumLinearOrder m n

private local instance (priority := high) instLEFinSumPPAD (m n : ℕ) :
    LE (Fin m ⊕ Fin n) :=
  (sumLinearOrder m n).toLE

private local instance (priority := high) instLTFinSumPPAD (m n : ℕ) :
    LT (Fin m ⊕ Fin n) :=
  (sumLinearOrder m n).toLT

private def finsetOfList (m n : ℕ) (L : List ℕ) : Finset (Fin m ⊕ Fin n) :=
  Finset.univ.filter fun r => (finSumFinEquiv r).1 ∈ L

@[simp]
private lemma mem_finsetOfList {m n : ℕ} {L : List ℕ} {r : Fin m ⊕ Fin n} :
    r ∈ finsetOfList m n L ↔ (finSumFinEquiv r).1 ∈ L := by
  simp [finsetOfList]

private lemma card_finsetOfList {m n : ℕ} {L : List ℕ} (hnd : L.Nodup)
    (hlt : ∀ k ∈ L, k < m + n) : (finsetOfList m n L).card = L.length := by
  have himg : finsetOfList m n L = L.attach.toFinset.image (fun x =>
      finSumFinEquiv.symm ⟨x.1, hlt x.1 x.2⟩) := by
    ext r
    simp only [mem_finsetOfList, Finset.mem_image, List.mem_toFinset, List.mem_attach, true_and]
    exact ⟨fun hr => ⟨⟨(finSumFinEquiv r).1, hr⟩, by simp⟩,
      fun ⟨⟨k, hk⟩, hEq⟩ => by simpa [← hEq] using hk⟩
  rw [himg, Finset.card_image_of_injective]
  · simp [List.toFinset_card_of_nodup (List.nodup_attach.2 hnd)]
  · exact fun x y hxy => Subtype.ext (by simpa using congrArg (fun z => (finSumFinEquiv z).1) hxy)

private lemma orderIsoOfFin_finsetOfList {m n k : ℕ} {L : List ℕ} (hsort : L.Pairwise (· < ·))
    (hlt : ∀ r ∈ L, r < m + n) (_hlen : L.length = k)
    (hcard : (finsetOfList m n L).card = k) (i : Fin k) :
    (finSumFinEquiv ((finsetOfList m n L).orderIsoOfFin hcard i).1).1 = L.getD i.1 0 := by
  let T := finsetOfList m n L
  let e : Fin k ≃o T := T.orderIsoOfFin hcard
  let f : Fin k → ℕ := fun j => (finSumFinEquiv ((e j).1)).1
  have hf_mono : StrictMono f := fun a b hab =>
    Nat.lt_of_le_of_ne (e.le_iff_le.2 hab.le) fun h =>
      hab.ne <| e.injective <| Subtype.ext <| finSumFinEquiv.injective <| Fin.ext h
  have hsort_ofFn : (List.ofFn f).Pairwise (· < ·) :=
    List.pairwise_iff_getElem.2 fun a b _ _ hab => by
      simpa only [List.getElem_ofFn] using hf_mono (Fin.mk_lt_mk.2 hab)
  have heq : List.ofFn f = L := hsort_ofFn.eq_of_mem_iff hsort fun x => by
    rw [List.mem_ofFn]
    exact ⟨fun ⟨j, hj⟩ => hj ▸ mem_finsetOfList.1 (e j).2, fun hx =>
      ⟨e.symm ⟨finSumFinEquiv.symm ⟨x, hlt x hx⟩, by simp [T, mem_finsetOfList, hx]⟩,
        by simp [f]⟩⟩
  exact (List.getD_ofFn f i 0).symm.trans (congrArg (·.getD i.1 0) heq)

private lemma eq_of_finsetOfList_eq {m n : ℕ} {L₁ L₂ : List ℕ}
    (hs₁ : L₁.Pairwise (· < ·)) (hs₂ : L₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ L₁, r < m + n) (hlt₂ : ∀ r ∈ L₂, r < m + n)
    (hfin : finsetOfList m n L₁ = finsetOfList m n L₂) : L₁ = L₂ :=
  hs₁.eq_of_mem_iff hs₂ fun k => by
    by_cases hk : k < m + n
    · simpa only [mem_finsetOfList, Equiv.apply_symm_apply] using
        Finset.ext_iff.1 hfin (finSumFinEquiv.symm ⟨k, hk⟩)
    · exact ⟨fun h => absurd (hlt₁ k h) hk, fun h => absurd (hlt₂ k h) hk⟩

/-- Positive normalized integer matrix `A` of `c`. -/
private def posMatA (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℤ :=
  fun i j => ((posMat c c.matA).getD i.1 []).getD j.1 0

/-- Positive normalized integer matrix `B` of `c`. -/
private def posMatB (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℤ :=
  fun i j => ((posMat c c.matB).getD i.1 []).getD j.1 0

private lemma posMat_getD_eq {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    posMatA c i j = scaledEntry (clearScale c) (c.toMatA i j) + shiftVal c ∧
      posMatB c i j = scaledEntry (clearScale c) (c.toMatB i j) + shiftVal c := by
  obtain ⟨_, _, hl2, hr1, hr2⟩ := hc
  have aux : ∀ (M : List (List ℚ)) (hlen : M.length = c.rows)
      (hrows : ∀ r ∈ M, r.length = c.cols),
      ((posMat c M).getD i.1 []).getD j.1 0 =
        scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0) + shiftVal c := by
    intro M hlen hrows
    have hi : i.1 < M.length := by rw [hlen]; exact i.2
    have hrlen : (M.getD i.1 []).length = c.cols := hrows _ (List.getD_mem [] hi)
    have hj : j.1 < (M.getD i.1 []).length := by rw [hrlen]; exact j.2
    have h1 : (posMat c M).getD i.1 [] =
        (M.getD i.1 []).map fun q => scaledEntry (clearScale c) q + shiftVal c :=
      List.getD_map_of_lt _ M [] [] hi
    rw [h1]
    exact List.getD_map_of_lt _ (M.getD i.1 []) 0 0 hj
  exact ⟨aux c.matA rfl hr1, aux c.matB hl2 hr2⟩

private lemma abs_scaledEntry_lt_shiftVal {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    |scaledEntry (clearScale c) (c.toMatA i j)| < shiftVal c ∧
      |scaledEntry (clearScale c) (c.toMatB i j)| < shiftVal c := by
  obtain ⟨_, _, hl2, hr1, hr2⟩ := hc
  have aux : ∀ (M : List (List ℚ)) (hlen : M.length = c.rows)
      (hrows : ∀ r ∈ M, r.length = c.cols),
      |scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0)| ≤
        (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum := by
    intro M hlen hrows
    have hi : i.1 < M.length := by rw [hlen]; exact i.2
    have hrmem : M.getD i.1 [] ∈ M := List.getD_mem [] hi
    have hj : j.1 < (M.getD i.1 []).length := by rw [hrows _ hrmem]; exact j.2
    have hqmem : (M.getD i.1 []).getD j.1 0 ∈ M.getD i.1 [] := List.getD_mem 0 hj
    have h1 : |scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0)| ≤
        ((M.getD i.1 []).map fun q => |scaledEntry (clearScale c) q|).sum :=
      List.single_le_sum (fun x hx => by
        rcases List.mem_map.1 hx with ⟨q, _, rfl⟩; exact abs_nonneg _)
        _ (List.mem_map.2 ⟨_, hqmem, rfl⟩)
    have h2 : ((M.getD i.1 []).map fun q => |scaledEntry (clearScale c) q|).sum ≤
        (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum :=
      List.single_le_sum (fun x hx => by
        rcases List.mem_map.1 hx with ⟨row, _, rfl⟩
        exact List.sum_nonneg fun y hy => by
          rcases List.mem_map.1 hy with ⟨q, _, rfl⟩; exact abs_nonneg _)
        _ (List.mem_map.2 ⟨_, hrmem, rfl⟩)
    exact h1.trans h2
  have hnonneg : ∀ M : List (List ℚ),
      0 ≤ (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum := by
    intro M
    exact List.sum_nonneg fun x hx => by
      rcases List.mem_map.1 hx with ⟨row, _, rfl⟩
      exact List.sum_nonneg fun y hy => by
        rcases List.mem_map.1 hy with ⟨q, _, rfl⟩; exact abs_nonneg _
  have hA := aux c.matA rfl hr1
  have hB := aux c.matB hl2 hr2
  have hn1 := hnonneg c.matA
  have hn2 := hnonneg c.matB
  dsimp only [shiftVal, toMatA, toMatB] at *
  exact ⟨by omega, by omega⟩

private lemma shiftVal_pos (c : BimatrixCode) : 1 ≤ shiftVal c := by
  have hnonneg : ∀ M : List (List ℚ),
      0 ≤ (M.map fun row => (row.map fun q => |scaledEntry (clearScale c) q|).sum).sum :=
    fun M => List.sum_nonneg fun x hx => by
      rcases List.mem_map.1 hx with ⟨row, _, rfl⟩
      exact List.sum_nonneg fun y hy => by
        rcases List.mem_map.1 hy with ⟨q, _, rfl⟩; exact abs_nonneg _
  have h1 := hnonneg c.matA
  have h2 := hnonneg c.matB
  dsimp only [shiftVal]
  omega

private lemma posMat_bounds {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    1 ≤ HVal c ∧ 1 ≤ posMatA c i j ∧ posMatA c i j ≤ (HVal c : ℤ) ∧
      1 ≤ posMatB c i j ∧ posMatB c i j ≤ (HVal c : ℤ) := by
  have hs := shiftVal_pos c
  have hH : (HVal c : ℤ) = 2 * shiftVal c := by
    dsimp only [HVal]
    push_cast
    rw [abs_of_nonneg (by omega)]
  obtain ⟨hposA, hposB⟩ := posMat_getD_eq hc i j
  obtain ⟨habsA, habsB⟩ := abs_scaledEntry_lt_shiftVal hc i j
  have hbd : ∀ {p s : ℤ}, p = s + shiftVal c → |s| < shiftVal c → 1 ≤ p ∧ p ≤ (HVal c : ℤ) := by
    intro p s hp habs
    have := neg_abs_le s
    have := le_abs_self s
    exact ⟨by omega, by omega⟩
  obtain ⟨hA1, hA2⟩ := hbd hposA habsA
  obtain ⟨hB1, hB2⟩ := hbd hposB habsB
  exact ⟨by omega, hA1, hA2, hB1, hB2⟩

private lemma isNash_posMat {c : BimatrixCode} (hc : c.WellFormed)
    (x : Fin c.rows → ℝ) (y : Fin c.cols → ℝ) :
    ({ A := (posMatA c).map Int.cast, B := (posMatB c).map Int.cast } :
        BimatrixGame (Fin c.rows) (Fin c.cols)).IsNash x y ↔ c.toGame.IsNash x y := by
  have ⟨_, _, hl2, hr1, hr2⟩ := hc
  have hDc : (0 : ℝ) < (clearScale c : ℝ) := by exact_mod_cast clearScale_pos c
  have hentry_eq : ∀ {M : List (List ℚ)} (hM : M = c.matA ∨ M = c.matB)
      (hlen : M.length = c.rows) (hrows : ∀ r ∈ M, r.length = c.cols)
      {P : Matrix (Fin c.rows) (Fin c.cols) ℤ} {G : Matrix (Fin c.rows) (Fin c.cols) ℝ}
      (hP : ∀ i j, P i j =
        scaledEntry (clearScale c) ((M.getD i.1 []).getD j.1 0) + shiftVal c)
      (hG : ∀ i j, G i j = (((M.getD i.1 []).getD j.1 0 : ℚ) : ℝ))
      (i : Fin c.rows) (j : Fin c.cols),
      ((P.map Int.cast) i j : ℝ) = (clearScale c : ℝ) * G i j + (shiftVal c : ℝ) := by
    intro M hM hlen hrows P G hP hG i j
    have hi : i.1 < M.length := by rw [hlen]; exact i.2
    have hrmem := List.getD_mem [] hi
    have hj : j.1 < (M.getD i.1 []).length := by rw [hrows _ hrmem]; exact j.2
    have hsc := congrArg (Rat.cast : ℚ → ℝ)
      (scaledEntry_cast (den_dvd_clearScale hM hrmem (List.getD_mem 0 hj)))
    push_cast at hsc
    dsimp only [Matrix.map_apply]
    rw [hP i j, hG i j]
    push_cast
    exact congrArg (· + (shiftVal c : ℝ)) hsc
  let GD : BimatrixGame (Fin c.rows) (Fin c.cols) :=
    BimatrixGame.mk ((clearScale c : ℝ) • c.toGame.A) ((clearScale c : ℝ) • c.toGame.B)
  have hA_eq' : (posMatA c).map (Int.cast : ℤ → ℝ) = (GD.addConst (shiftVal c : ℝ)).A := by
    ext i j
    rw [BimatrixGame.addConst_A_apply]
    exact hentry_eq (Or.inl rfl) rfl hr1 (fun a b => (posMat_getD_eq hc a b).1)
      (fun _ _ => rfl) i j
  have hB_eq' : (posMatB c).map (Int.cast : ℤ → ℝ) = (GD.addConst (shiftVal c : ℝ)).B := by
    ext i j
    rw [BimatrixGame.addConst_B_apply]
    exact hentry_eq (Or.inr rfl) hl2 hr2 (fun a b => (posMat_getD_eq hc a b).2)
      (fun _ _ => rfl) i j
  have hadd : ({ A := (posMatA c).map Int.cast, B := (posMatB c).map Int.cast } :
        BimatrixGame (Fin c.rows) (Fin c.cols)) = GD.addConst (shiftVal c : ℝ) :=
    congr_arg₂ BimatrixGame.mk hA_eq' hB_eq'
  rw [hadd, BimatrixGame.isNash_addConst, BimatrixGame.isNash_smul hDc c.toGame]

private def bitBoundVal (c : BimatrixCode) : ℕ :=
  bitBound c.rows c.cols (HVal c)

/-- Target Shapley orientation `(-1) ^ (c.rows + c.cols)` computed without exponentiation. -/
private def targetSign (c : BimatrixCode) : ℤ :=
  if decide (((c.rows + c.cols : ℤ) - 2 * ((c.rows + c.cols : ℤ).tdiv 2)) = 0) then 1 else -1

private lemma targetSign_eq (c : BimatrixCode) :
    targetSign c = (-1 : ℤ) ^ (c.rows + c.cols) := by
  have hsub : ∀ k : ℕ, (k : ℤ) - 2 * ((k : ℤ).tdiv 2) = ((k % 2 : ℕ) : ℤ) := fun k => by
    change (k : ℤ) - 2 * ((k / 2 : ℕ) : ℤ) = _
    have := Nat.div_add_mod k 2
    omega
  dsimp only [targetSign]
  rw [← Int.natCast_add, hsub, ← Nat.div_add_mod (c.rows + c.cols) 2]
  rcases Nat.mod_two_eq_zero_or_one (c.rows + c.cols) with h | h <;>
    simp [h, pow_add, pow_mul]

/-- Vertex bit-length for the PPAD graph: `2 * (rows + cols)` on well-formed inputs, else `0`. -/
@[expose] def vertexLen (c : BimatrixCode) : ℕ :=
  if c.wellFormedB then 2 * (c.rows + c.cols) else 0

/-- Decode player-1 tight row indices in `[0 .. rows + cols - 1]` from bit string `u`,
XORed with the artificial origin mask `k < rows`. -/
private def decodeT₁ (c : BimatrixCode) (u : List Bool) : List ℕ :=
  (List.range (c.rows + c.cols)).filter fun k => (u.getD k false) != decide (k < c.rows)

/-- Decode player-2 tight row indices in `[0 .. rows + cols - 1]` from bit string `u`,
XORed with the artificial origin mask `rows ≤ k`. -/
private def decodeT₂ (c : BimatrixCode) (u : List Bool) : List ℕ :=
  (List.range (c.rows + c.cols)).filter fun k =>
    (u.getD (c.rows + c.cols + k) false) != decide (c.rows ≤ k)

/-- Encode basis label lists `(T₁, T₂)` into a `2 * (rows + cols)`-bit vertex string, mapping the
artificial origin `([0..m-1], [m..m+n-1])` to `0^(2*(m+n))`. -/
private def encodeNodes (c : BimatrixCode) (T₁ T₂ : List ℕ) : List Bool :=
  let d := c.rows + c.cols
  (List.range (2 * d)).map fun k =>
    if k < d then decide (k ∈ T₁) != decide (k < c.rows)
    else decide (k - d ∈ T₂) != decide (c.rows ≤ k - d)

private lemma length_encodeNodes (c : BimatrixCode) (T₁ T₂ : List ℕ) :
    (encodeNodes c T₁ T₂).length = 2 * (c.rows + c.cols) := by
  simp [encodeNodes]

private lemma encodeNodes_origin (c : BimatrixCode) :
    encodeNodes c (List.range c.rows) ((List.range c.cols).map (· + c.rows)) =
      zeroVertex (2 * (c.rows + c.cols)) := by
  refine List.ext_getElem (by simp [encodeNodes]) fun k hk1 hk2 => ?_
  simp only [encodeNodes, List.length_map, List.length_range] at hk1
  simp only [encodeNodes, zeroVertex, List.getElem_map, List.getElem_range, List.getElem_replicate]
  by_cases hkd : k < c.rows + c.cols
  · rw [ite_eq_left hkd]
    simp [List.mem_range, bne_self_eq_false]
  · rw [ite_eq_right hkd]
    have hmem : (k - (c.rows + c.cols) ∈
        (List.range c.cols).map (· + c.rows)) ↔ c.rows ≤ k - (c.rows + c.cols) := by
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨j, _, hj⟩; omega
      · intro hge
        refine ⟨k - (c.rows + c.cols) - c.rows, by omega, by omega⟩
    simp [hmem, bne_self_eq_false]

private lemma decodeT₁_sorted (c : BimatrixCode) (u : List Bool) :
    (decodeT₁ c u).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma decodeT₂_sorted (c : BimatrixCode) (u : List Bool) :
    (decodeT₂ c u).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma decodeT₁_lt (c : BimatrixCode) (u : List Bool) {k : ℕ} (hk : k ∈ decodeT₁ c u) :
    k < c.rows + c.cols := by
  simp only [decodeT₁, List.mem_filter, List.mem_range] at hk
  exact hk.1

private lemma decodeT₂_lt (c : BimatrixCode) (u : List Bool) {k : ℕ} (hk : k ∈ decodeT₂ c u) :
    k < c.rows + c.cols := by
  simp only [decodeT₂, List.mem_filter, List.mem_range] at hk
  exact hk.1

private lemma encodeNodes_decode {c : BimatrixCode} {u : List Bool}
    (hu : u.length = 2 * (c.rows + c.cols)) :
    encodeNodes c (decodeT₁ c u) (decodeT₂ c u) = u := by
  refine List.ext_getElem (by simp [encodeNodes, hu]) fun k hk1 hk2 => ?_
  simp only [encodeNodes, List.getElem_map, List.getElem_range]
  have hget : u.getD k false = u[k] := List.getD_eq_getElem u false hk2
  by_cases hkd : k < c.rows + c.cols
  · simp only [hkd, ↓reduceIte, decodeT₁, List.mem_filter, List.mem_range, true_and, hget]
    cases u[k] <;> cases decide (k < c.rows) <;> decide
  · have hkd2 : k - (c.rows + c.cols) < c.rows + c.cols := by
      simp only [encodeNodes, List.length_map, List.length_range] at hk1
      omega
    have hsumk : c.rows + c.cols + (k - (c.rows + c.cols)) = k := by omega
    simp only [hkd, ↓reduceIte, decodeT₂, List.mem_filter, List.mem_range, hkd2, true_and,
      hsumk, hget]
    cases u[k] <;> cases decide (c.rows ≤ k - (c.rows + c.cols)) <;> decide

private lemma decodeT₁_encodeNodes {c : BimatrixCode} (T₁ T₂ : List ℕ) {k : ℕ}
    (hk : k < c.rows + c.cols) :
    k ∈ decodeT₁ c (encodeNodes c T₁ T₂) ↔ k ∈ T₁ := by
  have hklen : k < (encodeNodes c T₁ T₂).length := by simp [encodeNodes]; omega
  simp only [decodeT₁, List.mem_filter, List.mem_range, hk, true_and]
  rw [List.getD_eq_getElem _ false hklen]
  simp only [encodeNodes, List.getElem_map, List.getElem_range, hk, ↓reduceIte]
  cases hkT : decide (k ∈ T₁) <;> cases decide (k < c.rows) <;> simp_all

private lemma decodeT₂_encodeNodes {c : BimatrixCode} (T₁ T₂ : List ℕ) {k : ℕ}
    (hk : k < c.rows + c.cols) :
    k ∈ decodeT₂ c (encodeNodes c T₁ T₂) ↔ k ∈ T₂ := by
  have hklen : c.rows + c.cols + k < (encodeNodes c T₁ T₂).length := by
    simp [encodeNodes]; omega
  have hnotlt : ¬ c.rows + c.cols + k < c.rows + c.cols := by omega
  simp only [decodeT₂, List.mem_filter, List.mem_range, hk, true_and]
  rw [List.getD_eq_getElem _ false hklen]
  simp only [encodeNodes, List.getElem_map, List.getElem_range, hnotlt, ↓reduceIte,
    Nat.add_sub_cancel_left]
  cases hkT : decide (k ∈ T₂) <;> cases decide (c.rows ≤ k) <;> simp_all

private lemma decodeT₁_zeroVertex (c : BimatrixCode) :
    decodeT₁ c (zeroVertex (2 * (c.rows + c.cols))) = List.range c.rows :=
  (decodeT₁_sorted c _).eq_of_mem_iff List.pairwise_lt_range fun k => by
    rw [← encodeNodes_origin c]
    exact ⟨fun hk => (decodeT₁_encodeNodes _ _ (decodeT₁_lt c _ hk)).1 hk,
      fun hk => (decodeT₁_encodeNodes _ _ (by rw [List.mem_range] at hk; omega)).2 hk⟩

private lemma decodeT₂_zeroVertex (c : BimatrixCode) :
    decodeT₂ c (zeroVertex (2 * (c.rows + c.cols))) = (List.range c.cols).map (· + c.rows) := by
  have hsort : ((List.range c.cols).map (· + c.rows)).Pairwise (· < ·) :=
    List.pairwise_lt_range.map _ fun _ _ h => by omega
  refine (decodeT₂_sorted c _).eq_of_mem_iff hsort fun k => ?_
  rw [← encodeNodes_origin c]
  refine ⟨fun hk => (decodeT₂_encodeNodes _ _ (decodeT₂_lt c _ hk)).1 hk, fun hk => ?_⟩
  rcases List.mem_map.1 hk with ⟨j, hj, rfl⟩
  exact (decodeT₂_encodeNodes _ _ (by rw [List.mem_range] at hj; omega)).2 hk

private theorem mapToBitsWithInput_poly {α β : Type} {encIn : α ↪ List Bool}
    {enc : β ↪ List Bool} {list : α → List β} {f : α → β → Bool}
    (hlist : ComputableInPolyTime list encIn (encList enc))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair encIn enc) encBool) :
    ComputableInPolyTime (fun a => (list a).map (f a)) encIn encBits :=
  (ComputableInPolyTime.mapToBitsWithInput hlist hf)

private theorem bool_xor_polytime {α : Type} {encIn : α ↪ List Bool}
    {a b : α → Bool} (ha : ComputableInPolyTime a encIn encBool)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => a x != b x) encIn encBool :=
  (ComputableInPolyTime.of_finite (fun p : Bool × Bool => p.1 != p.2)).comp (ha.prod hb)

@[local fun_prop]
private theorem bitBoundVal_polytime :
    ComputableInPolyTime bitBoundVal encBimatrix encUnary := by
  have hlog : ∀ H : ℕ, Nat.log 2 H = H.size - 1 := fun H => by
    rw [← Nat.log2_eq_log_two, Nat.log2_eq_size_sub_one]
  have hb : ComputableInPolyTime
      (fun c : BimatrixCode => 4 * (c.rows + c.cols) * (c.rows + c.cols + ((HVal c).size - 1) + 3))
      encBimatrix encUnary := by
    have hd := unary_add.comp (codeRows_polytime.prod codeCols_polytime)
    have h4d := unary_mul.comp ((const 4).prod hd)
    have hsize := unary_sub.comp ((binary_size.comp HVal_polytime).prod (const 1))
    have hsum := unary_add.comp ((unary_add.comp (hd.prod hsize)).prod (const 3))
    exact unary_mul.comp (h4d.prod hsum)
  exact hb.of_enc_eq (encD := encUnary) fun c => by
    dsimp only [bitBoundVal, bitBound]
    rw [hlog]

@[local fun_prop]
private theorem targetSign_polytime :
    ComputableInPolyTime targetSign encBimatrix encIntBin := by
  unfold targetSign
  have hd : ComputableInPolyTime (fun c : BimatrixCode => (c.rows + c.cols : ℤ))
      encBimatrix encIntBin :=
    intBin_natCast.comp (unary_to_binary.comp
      (unary_add.comp (codeRows_polytime.prod codeCols_polytime)))
  have hrem := intBin_sub' hd (intBin_mul' (const 2) (intBin_tdiv' hd (const 2)))
  exact ite' (decide_eq' hrem (const (encOut := encIntBin) 0))
    (const (encOut := encIntBin) 1) (const (encOut := encIntBin) (-1))

@[local fun_prop]
private theorem vertexLen_polytime :
    ComputableInPolyTime vertexLen encBimatrix encUnary := by
  unfold vertexLen
  exact ite' wellFormedB_polytime
    (unary_mul.comp ((const 2).prod (unary_add.comp (codeRows_polytime.prod codeCols_polytime))))
    (const 0)

private theorem filterRangeXorGetD_polytime
    {idx : BimatrixCode × ℕ → ℕ} {mask : BimatrixCode × ℕ → Bool}
    (hidx : ComputableInPolyTime idx (encPair encBimatrix encUnary) encUnary)
    (hmask : ComputableInPolyTime mask (encPair encBimatrix encUnary) encBool) :
    ComputableInPolyTime
      (fun p : BimatrixCode × List Bool =>
        (List.range (p.1.rows + p.1.cols)).filter fun k =>
          p.2.getD (idx (p.1, k)) false != mask (p.1, k))
      (encPair encBimatrix encBits) (encList encUnary) := by
  have hc0 := fst encBimatrix encBits
  refine filterWithInput
    (range.comp (unary_add.comp ((codeRows_polytime.comp hc0).prod
      (codeCols_polytime.comp hc0)))) ?_
  have hck := (hc0.comp (fst (encPair encBimatrix encBits) encUnary)).prod
    (snd (encPair encBimatrix encBits) encUnary)
  have hu := (snd encBimatrix encBits).comp (fst (encPair encBimatrix encBits) encUnary)
  exact bool_xor_polytime
    (bitsGetD false |>.comp (hu.prod (hidx.comp hck)))
    (hmask.comp hck)

@[local fun_prop]
private theorem decodeT₁_polytime :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₁ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) :=
  filterRangeXorGetD_polytime (snd _ _)
    (unary_lt' (snd _ _) (codeRows_polytime.comp (fst _ _)))

@[local fun_prop]
private theorem decodeT₂_polytime :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₂ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := by
  have hm := codeRows_polytime.comp (fst encBimatrix encUnary)
  have hn := codeCols_polytime.comp (fst encBimatrix encUnary)
  exact filterRangeXorGetD_polytime
    (unary_add.comp ((unary_add.comp (hm.prod hn)).prod (snd _ _)))
    (unary_le' hm (snd _ _))

private theorem encodeNodes_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {T₁ T₂ : α → List ℕ}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => encodeNodes (c x) (T₁ x) (T₂ x)) encIn encBits := by
  unfold encodeNodes
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  refine mapToBitsWithInput_poly (range.comp (unary_mul.comp ((const 2).prod hd))) ?_
  have hlt := unary_lt' (snd encIn encUnary) (hd.comp (fst encIn encUnary))
  have hsub := unary_sub.comp ((snd encIn encUnary).prod (hd.comp (fst encIn encUnary)))
  have hle := unary_le' (hm.comp (fst encIn encUnary)) hsub
  have hk1 := bool_xor_polytime (decide_mem (h1.comp (fst encIn encUnary)) (snd encIn encUnary))
    (unary_lt' (snd encIn encUnary) (hm.comp (fst encIn encUnary)))
  have hk2 := bool_xor_polytime (decide_mem (h2.comp (fst encIn encUnary)) hsub) hle
  exact ite_decide hlt hk1 hk2

/-- All `m + n` rows of `intMatP (posMatB c)` as `List (List ℤ)`. -/
private def allRowsP (c : BimatrixCode) : List (List ℤ) :=
  let Bpos := posMat c c.matB
  tabulateTable (c.rows + c.cols) c.rows fun r i =>
    if r < c.rows then if i = r then -1 else 0 else rowEntry Bpos i (r - c.rows)

/-- All `m + n` entries of the perturbed RHS `pertRhsPInt` for `P_ε`. -/
private def allRhsP (c : BimatrixCode) : List ℤ :=
  let E := bitBoundVal c
  (List.range (c.rows + c.cols)).map fun r =>
    if r < c.rows then 0
    else ((2 ^ (E * c.cols) : ℕ) : ℤ) + ((2 ^ (E * (c.cols - 1 - (r - c.rows))) : ℕ) : ℤ)

/-- All `m + n` rows of `intMatQ (posMatA c)` as `List (List ℤ)`. -/
private def allRowsQ (c : BimatrixCode) : List (List ℤ) :=
  let Apos := posMat c c.matA
  tabulateTable (c.rows + c.cols) c.cols fun r j =>
    if r < c.rows then rowEntry Apos r j else if j = r - c.rows then -1 else 0

/-- All `m + n` entries of the perturbed RHS `pertRhsQInt` for `Q_ε`. -/
private def allRhsQ (c : BimatrixCode) : List ℤ :=
  let E := bitBoundVal c
  (List.range (c.rows + c.cols)).map fun r =>
    if r < c.rows then
      ((2 ^ (E * c.rows) : ℕ) : ℤ) + ((2 ^ (E * (c.rows - 1 - r)) : ℕ) : ℤ)
    else 0

/-- All `m + n` entries of the unperturbed RHS `intRhsP`. -/
private def allIntRhsP (c : BimatrixCode) : List ℤ :=
  (List.range (c.rows + c.cols)).map fun r => if r < c.rows then 0 else 1

/-- All `m + n` entries of the unperturbed RHS `intRhsQ`. -/
private def allIntRhsQ (c : BimatrixCode) : List ℤ :=
  (List.range (c.rows + c.cols)).map fun r => if r < c.rows then 1 else 0

/-- Extract the `k × k` basis submatrix for row list `T` from full row table `allRows`. -/
private def subRows (k : ℕ) (allRows : List (List ℤ)) (T : List ℕ) : List (List ℤ) :=
  T.map fun r => (List.range k).map fun j => rowEntry allRows r j

/-- Extract the `k`-element RHS vector for row list `T` from full RHS list `rhsAll`. -/
private def subRhs (rhsAll : List ℤ) (T : List ℕ) : List ℤ :=
  T.map fun r => rowEntry [rhsAll] 0 r

/-- Replace column `col` of `k × k` list matrix `M` with vector `rhs`. -/
private def updateColRows (k : ℕ) (M : List (List ℤ)) (col : ℕ) (rhs : List ℤ) :
    List (List ℤ) :=
  tabulateTable k k fun r j => if j = col then rowEntry [rhs] 0 r else rowEntry M r j

/-- Cramer vector `(det (M.updateCol i rhs))_{i < k}`. -/
private def cramerVecRows (k : ℕ) (M : List (List ℤ)) (rhs : List ℤ) : List ℤ :=
  (List.range k).map fun i => detRows (updateColRows k M i rhs)

/-- Executable feasibility check matching `IsFeasibleBasis` on `(k, allRows, rhsAll, T)`. -/
private def isFeasibleBasisRows (k d : ℕ) (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (T : List ℕ) : Bool :=
  let M := subRows k allRows T
  let D := detRows M
  let cv := cramerVecRows k M (subRhs rhsAll T)
  decide (D ≠ 0) &&
    (List.range d).all fun r =>
      let row := (List.range k).map fun j => rowEntry allRows r j
      decide (D.sign * ListMatrix.dotProduct k row cv ≤ |D| * rowEntry [rhsAll] 0 r)

private lemma rowCellC_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.1.1.1)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encBimatrix :=
  (fst encBimatrix encIntTable).comp
    ((fst (encPair encBimatrix encIntTable) encUnary).comp
      (fst (encPair (encPair encBimatrix encIntTable) encUnary) encUnary))

private lemma rowCellM_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.1.1.2)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntTable :=
  (snd encBimatrix encIntTable).comp
    ((fst (encPair encBimatrix encIntTable) encUnary).comp
      (fst (encPair (encPair encBimatrix encIntTable) encUnary) encUnary))

private lemma rowCellR_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.1.2)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encUnary :=
  (snd (encPair encBimatrix encIntTable) encUnary).comp
    (fst (encPair (encPair encBimatrix encIntTable) encUnary) encUnary)

private lemma rowCellK_polytime :
    ComputableInPolyTime (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ => p.2)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encUnary :=
  snd (encPair (encPair encBimatrix encIntTable) encUnary) encUnary

private lemma tabulateSplitRows_polytime {dim : BimatrixCode → ℕ}
    (hdim : ComputableInPolyTime dim encBimatrix encUnary)
    {mat : BimatrixCode → List (List ℤ)}
    (hmat : ComputableInPolyTime mat encBimatrix encIntTable)
    {entry : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ → ℤ}
    (hentry : ComputableInPolyTime entry
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntBin)
    {g : BimatrixCode → List (List ℤ)}
    (hg : ∀ c, g c = tabulateTable (c.rows + c.cols) (dim c) fun r k =>
      entry (((c, mat c), r), k)) :
    ComputableInPolyTime g encBimatrix encIntTable := by
  have hwith : ComputableInPolyTime
      (fun p : BimatrixCode × List (List ℤ) =>
        tabulateTable (p.1.rows + p.1.cols) (dim p.1) fun r k => entry ((p, r), k))
      (encPair encBimatrix encIntTable) encIntTable :=
    computableInPolyTime_tabulateTable
      (unary_add.comp ((codeRows_polytime.comp (fst encBimatrix encIntTable)).prod
        (codeCols_polytime.comp (fst encBimatrix encIntTable))))
      (hdim.comp (fst encBimatrix encIntTable)) hentry
  exact (hwith.comp ((id' (encIn := encBimatrix)).prod hmat)).of_enc_eq
    (encD := encIntTable) fun c => congrArg encIntTable (hg c)

@[local fun_prop]
private theorem allRowsP_polytime :
    ComputableInPolyTime allRowsP encBimatrix encIntTable := by
  have hentry : ComputableInPolyTime
      (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ =>
        if p.1.2 < p.1.1.1.rows then if p.2 = p.1.2 then -1 else 0
        else rowEntry p.1.1.2 p.2 (p.1.2 - p.1.1.1.rows))
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntBin := by
    have hm := codeRows_polytime.comp rowCellC_polytime
    have h1 := ite_decide (decide_eq' rowCellK_polytime rowCellR_polytime)
      (const (encOut := encIntBin) (-1)) (const (encOut := encIntBin) 0)
    have h2 := computableInPolyTime_rowEntry rowCellM_polytime rowCellK_polytime
      (unary_sub.comp (rowCellR_polytime.prod hm))
    exact ite_decide (unary_lt' rowCellR_polytime hm) h1 h2
  exact tabulateSplitRows_polytime codeRows_polytime posMatB_polytime hentry fun _ => rfl

@[local fun_prop]
private theorem allRowsQ_polytime :
    ComputableInPolyTime allRowsQ encBimatrix encIntTable := by
  have hentry : ComputableInPolyTime
      (fun p : ((BimatrixCode × List (List ℤ)) × ℕ) × ℕ =>
        if p.1.2 < p.1.1.1.rows then rowEntry p.1.1.2 p.1.2 p.2
        else if p.2 = p.1.2 - p.1.1.1.rows then -1 else 0)
      (encPair (encPair (encPair encBimatrix encIntTable) encUnary) encUnary) encIntBin := by
    have hm := codeRows_polytime.comp rowCellC_polytime
    have h1 := computableInPolyTime_rowEntry rowCellM_polytime rowCellR_polytime rowCellK_polytime
    have h2 := ite_decide
      (decide_eq' rowCellK_polytime (unary_sub.comp (rowCellR_polytime.prod hm)))
      (const (encOut := encIntBin) (-1)) (const (encOut := encIntBin) 0)
    exact ite_decide (unary_lt' rowCellR_polytime hm) h1 h2
  exact tabulateSplitRows_polytime codeCols_polytime posMatA_polytime hentry fun _ => rfl

private theorem pertTerm_polytime {α : Type} {encIn : α ↪ List Bool}
    {E dim idx : α → ℕ}
    (hE : ComputableInPolyTime E encIn encUnary)
    (hdim : ComputableInPolyTime dim encIn encUnary)
    (hidx : ComputableInPolyTime idx encIn encUnary) :
    ComputableInPolyTime
      (fun x => ((2 ^ (E x * dim x) : ℕ) : ℤ) + ((2 ^ (E x * (dim x - 1 - idx x)) : ℕ) : ℤ))
      encIn encIntBin :=
  intBin_add' (intBin_natCast.comp (binary_two_pow.comp (unary_mul.comp (hE.prod hdim))))
    (intBin_natCast.comp (binary_two_pow.comp
      (unary_mul.comp (hE.prod (unary_sub.comp
        ((unary_sub.comp (hdim.prod (const 1))).prod hidx))))))

/-- `m + n`-entry lists with one entry map on the `P` rows `r < m` and another on the `Q` rows. -/
private theorem mapSplitRange_polytime {fL fR : BimatrixCode × ℕ → ℤ}
    (hfL : ComputableInPolyTime fL (encPair encBimatrix encUnary) encIntBin)
    (hfR : ComputableInPolyTime fR (encPair encBimatrix encUnary) encIntBin) :
    ComputableInPolyTime
      (fun c : BimatrixCode =>
        (List.range (c.rows + c.cols)).map fun r => if r < c.rows then fL (c, r) else fR (c, r))
      encBimatrix (encList encIntBin) :=
  mapWithInput (encA := encUnary)
    (range.comp (unary_add.comp (codeRows_polytime.prod codeCols_polytime)))
    (ite_decide (unary_lt' (snd _ _) (codeRows_polytime.comp (fst _ _))) hfL hfR)

@[local fun_prop]
private theorem allRhsP_polytime :
    ComputableInPolyTime allRhsP encBimatrix (encList encIntBin) :=
  mapSplitRange_polytime (const 0)
    (pertTerm_polytime (bitBoundVal_polytime.comp (fst _ _)) (codeCols_polytime.comp (fst _ _))
      (unary_sub.comp ((snd _ _).prod (codeRows_polytime.comp (fst _ _)))))

@[local fun_prop]
private theorem allRhsQ_polytime :
    ComputableInPolyTime allRhsQ encBimatrix (encList encIntBin) :=
  mapSplitRange_polytime
    (pertTerm_polytime (bitBoundVal_polytime.comp (fst _ _)) (codeRows_polytime.comp (fst _ _))
      (snd _ _))
    (const 0)

@[local fun_prop]
private theorem allIntRhsP_polytime :
    ComputableInPolyTime allIntRhsP encBimatrix (encList encIntBin) :=
  mapSplitRange_polytime (const 0) (const 1)

@[local fun_prop]
private theorem allIntRhsQ_polytime :
    ComputableInPolyTime allIntRhsQ encBimatrix (encList encIntBin) :=
  mapSplitRange_polytime (const 1) (const 0)

private lemma rowEntry_single (l : List ℤ) (r : ℕ) :
    rowEntry [l] 0 r = l.getD r 0 := by
  simp [rowEntry]

private theorem subRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {allRows : α → List (List ℤ)} {T : α → List ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => subRows (k x) (allRows x) (T x)) encIn encIntTable := by
  unfold subRows
  refine mapWithInput (encA := encUnary) hT ?_
  refine mapWithInput (encA := encUnary) (range.comp (hk.comp (fst _ _))) ?_
  exact computableInPolyTime_rowEntry (hall.comp ((fst _ _).comp (fst _ _)))
    ((snd _ _).comp (fst _ _)) (snd _ _)

/-- Reading entry `idx x` of the one-row table `[rhs x]` is polynomial-time computable. -/
private theorem rowEntry_singleton_polytime {α : Type} {encIn : α ↪ List Bool}
    {rhs : α → List ℤ} {idx : α → ℕ}
    (hrhs : ComputableInPolyTime rhs encIn (encList encIntBin))
    (hidx : ComputableInPolyTime idx encIn encUnary) :
    ComputableInPolyTime (fun x => rowEntry [rhs x] 0 (idx x)) encIn encIntBin := by
  have hcons : ComputableInPolyTime (fun l : List ℤ => [l]) (encList encIntBin) encIntTable := by
    fun_prop
  exact computableInPolyTime_rowEntry (hcons.comp hrhs) (const 0) hidx

private theorem subRhs_polytime {α : Type} {encIn : α ↪ List Bool}
    {rhsAll : α → List ℤ} {T : α → List ℕ}
    (hrhs : ComputableInPolyTime rhsAll encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => subRhs (rhsAll x) (T x)) encIn (encList encIntBin) :=
  mapWithInput (encA := encUnary) hT
    (rowEntry_singleton_polytime (hrhs.comp (fst _ _)) (snd _ _))

private theorem updateColRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k col : α → ℕ} {M : α → List (List ℤ)} {rhs : α → List ℤ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hM : ComputableInPolyTime M encIn encIntTable)
    (hcol : ComputableInPolyTime col encIn encUnary)
    (hrhs : ComputableInPolyTime rhs encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => updateColRows (k x) (M x) (col x) (rhs x))
      encIn encIntTable := by
  unfold updateColRows
  refine computableInPolyTime_tabulateTable hk hk ?_
  have hx := (fst encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  have hr := (snd encIn encUnary).comp (fst (encPair encIn encUnary) encUnary)
  have hj := snd (encPair encIn encUnary) encUnary
  exact ite_decide (decide_eq' hj (hcol.comp hx))
    (rowEntry_singleton_polytime (hrhs.comp hx) hr)
    (computableInPolyTime_rowEntry (hM.comp hx) hr hj)

private theorem cramerVecRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {M : α → List (List ℤ)} {rhs : α → List ℤ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hM : ComputableInPolyTime M encIn encIntTable)
    (hrhs : ComputableInPolyTime rhs encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => cramerVecRows (k x) (M x) (rhs x))
      encIn (encList encIntBin) := by
  unfold cramerVecRows
  refine mapWithInput (encA := encUnary) (range.comp hk) ?_
  exact detRows_polytime.comp (updateColRows_polytime (hk.comp (fst _ _)) (hM.comp (fst _ _))
    (snd _ _) (hrhs.comp (fst _ _)))

private theorem isFeasibleBasisRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k d : α → ℕ} {allRows : α → List (List ℤ)} {rhsAll : α → List ℤ} {T : α → List ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hrhs : ComputableInPolyTime rhsAll encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime
      (fun x => isFeasibleBasisRows (k x) (d x) (allRows x) (rhsAll x) (T x)) encIn encBool := by
  let encP := encPair encUnary (encPair encUnary (encPair encIntTable
    (encPair (encList encIntBin) (encList encUnary))))
  let baseFn : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ → Bool :=
    fun q => isFeasibleBasisRows q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  have hbase : ComputableInPolyTime baseFn encP encBool := by
    have hq_k : ComputableInPolyTime (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.1)
        encP encUnary := fst _ _
    have hq_d : ComputableInPolyTime (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.1)
        encP encUnary := (fst _ _).comp (snd _ _)
    have hq_all : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.2.1) encP encIntTable :=
      (fst _ _).comp ((snd _ _).comp (snd _ _))
    have hq_rhs : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.2.2.1)
        encP (encList encIntBin) :=
      (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
    have hq_T : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ => q.2.2.2.2)
        encP (encList encUnary) :=
      (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
    have hM := subRows_polytime hq_k hq_all hq_T
    have hD := detRows_polytime.comp hM
    have hcv := cramerVecRows_polytime hq_k hM (subRhs_polytime hq_rhs hq_T)
    have hallcheck : ComputableInPolyTime
        (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ =>
          (List.range q.2.1).all fun r =>
            decide ((detRows (subRows q.1 q.2.2.1 q.2.2.2.2)).sign *
              ListMatrix.dotProduct q.1 ((List.range q.1).map fun j => rowEntry q.2.2.1 r j)
                (cramerVecRows q.1 (subRows q.1 q.2.2.1 q.2.2.2.2)
                  (subRhs q.2.2.2.1 q.2.2.2.2)) ≤
              |detRows (subRows q.1 q.2.2.1 q.2.2.2.2)| *
                rowEntry [q.2.2.2.1] 0 r)) encP encBool := by
      refine allWithInput (encA := encUnary) (range.comp hq_d) ?_
      have hx := fst encP encUnary
      have hr := snd encP encUnary
      have habs : ComputableInPolyTime
          (fun q : ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ =>
            |detRows (subRows q.1 q.2.2.1 q.2.2.2.2)|) encP encIntBin :=
        (intBin_natCast.comp (intBin_natAbs.comp hD)).of_enc_eq (encD := encIntBin) fun q => by
          simp only [Function.comp_apply, Int.natCast_natAbs]
      have hrow_r : ComputableInPolyTime
          (fun p : (ℕ × ℕ × List (List ℤ) × List ℤ × List ℕ) × ℕ =>
            (List.range p.1.1).map fun j => rowEntry p.1.2.2.1 p.2 j)
          (encPair encP encUnary) (encList encIntBin) := by
        refine mapWithInput (encA := encUnary) (range.comp (hq_k.comp hx)) ?_
        exact computableInPolyTime_rowEntry
          (hq_all.comp (hx.comp (fst (encPair encP encUnary) encUnary)))
          (hr.comp (fst (encPair encP encUnary) encUnary)) (snd (encPair encP encUnary) encUnary)
      have hdot := listDotProduct.comp ((hq_k.comp hx).prod (hrow_r.prod (hcv.comp hx)))
      have hlhs := intBin_mul' (intBin_sign.comp (hD.comp hx)) hdot
      have hrhs' := intBin_mul' (habs.comp hx) (rowEntry_singleton_polytime (hq_rhs.comp hx) hr)
      exact intBin_le' hlhs hrhs'
    exact bool_and' (bool_not.comp (decide_eq' hD (const 0))) hallcheck
  exact (hbase.comp (hk.prod (hd.prod (hall.prod (hrhs.prod hT))))).of_enc_eq
    (encD := encBool) fun _ => rfl

private lemma subRows_eq_basisMat {m n k : ℕ} (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ)
    (allRows : List (List ℤ))
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    let Tset := finsetOfList m n T
    have hcard : Tset.card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    (subRows k allRows T).length = k ∧
      (∀ i j : Fin k, rowEntry (subRows k allRows T) i.1 j.1 = basisMat M_int Tset hcard i j) ∧
      detRows (subRows k allRows T) = (basisMat M_int Tset hcard).det := by
  intro Tset hcard
  have hsublen : (subRows k allRows T).length = k := by simp [subRows, hlen]
  have hentry : ∀ i j : Fin k,
      rowEntry (subRows k allRows T) i.1 j.1 = basisMat M_int Tset hcard i j := by
    intro i j
    have hi : i.1 < T.length := by rw [hlen]; exact i.2
    have hrow : (subRows k allRows T).getD i.1 [] =
        (List.range k).map fun j' => rowEntry allRows (T.getD i.1 0) j' :=
      List.getD_map_of_lt _ T 0 [] hi
    have hj : j.1 < k := j.2
    have hent : rowEntry (subRows k allRows T) i.1 j.1 =
        rowEntry allRows (T.getD i.1 0) j.1 := by
      change ((subRows k allRows T).getD i.1 []).getD j.1 0 = rowEntry allRows (T.getD i.1 0) j.1
      rw [hrow, List.getD_map_range _ 0 hj]
    have hord := orderIsoOfFin_finsetOfList hsort hlt hlen hcard i
    have hmem : T.getD i.1 0 ∈ T := List.getD_mem 0 hi
    have hlt_i : T.getD i.1 0 < m + n := hlt _ hmem
    have hhall := hall ⟨T.getD i.1 0, hlt_i⟩ j
    rw [hent, hhall]
    have hsymm : finSumFinEquiv.symm ⟨T.getD i.1 0, hlt_i⟩ =
        ((finsetOfList m n T).orderIsoOfFin hcard i).1 := by
      apply finSumFinEquiv.injective
      ext
      simp only [Equiv.apply_symm_apply]
      exact hord.symm
    rw [hsymm]
    rfl
  exact ⟨hsublen, hentry, detRows_eq_det_of_rowEntry _ hsublen hentry⟩

private lemma cramerVecRows_eq_cramerVec {m n k : ℕ} (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ)
    (b_int : Fin m ⊕ Fin n → ℤ) (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    have hcard : (finsetOfList m n T).card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    let cv := cramerVecRows k (subRows k allRows T) (subRhs rhsAll T)
    cv.length = k ∧
      ∀ i : Fin k, cv.getD i.1 0 = cramerVec M_int b_int (finsetOfList m n T) hcard i := by
  intro hcard cv
  obtain ⟨_, hentry, _⟩ := subRows_eq_basisMat M_int allRows hall hsort hlt hlen
  have hsubRhs : ∀ r : Fin k,
      (subRhs rhsAll T).getD r.1 0 = b_int ↑(((finsetOfList m n T).orderIsoOfFin hcard) r) := by
    intro r
    have hr : r.1 < T.length := by rw [hlen]; exact r.2
    have h1 : (subRhs rhsAll T).getD r.1 0 = rowEntry [rhsAll] 0 (T.getD r.1 0) :=
      List.getD_map_of_lt _ T 0 0 hr
    rw [h1, rowEntry_single]
    have hlt_r : T.getD r.1 0 < m + n := hlt _ (List.getD_mem 0 hr)
    rw [hrhs ⟨T.getD r.1 0, hlt_r⟩]
    have hord := orderIsoOfFin_finsetOfList hsort hlt hlen hcard r
    have hsymm : finSumFinEquiv.symm ⟨T.getD r.1 0, hlt_r⟩ =
        ((finsetOfList m n T).orderIsoOfFin hcard r).1 := by
      apply finSumFinEquiv.injective
      ext
      simp only [Equiv.apply_symm_apply]
      exact hord.symm
    rw [hsymm]
  have hlen_cv : cv.length = k := by simp [cv, cramerVecRows]
  have hget : ∀ i : Fin k,
      cv.getD i.1 0 = cramerVec M_int b_int (finsetOfList m n T) hcard i := by
    intro i
    have h1 : cv.getD i.1 0 =
        detRows (updateColRows k (subRows k allRows T) i.1 (subRhs rhsAll T)) :=
      List.getD_map_range _ 0 i.2
    let B := basisMat M_int (finsetOfList m n T) hcard
    let v : Fin k → ℤ := fun r => b_int ↑(((finsetOfList m n T).orderIsoOfFin hcard) r)
    have hup_len : (updateColRows k (subRows k allRows T) i.1 (subRhs rhsAll T)).length = k := by
      simp [updateColRows, tabulateTable]
    have hup_entry : ∀ r j : Fin k,
        rowEntry (updateColRows k (subRows k allRows T) i.1 (subRhs rhsAll T)) r.1 j.1 =
          (B.updateCol i v) r j := by
      intro r j
      dsimp only [updateColRows]
      rw [rowEntry_tabulateTable, ite_eq_left ⟨r.2, j.2⟩, rowEntry_single]
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl, Matrix.updateCol_apply, ite_eq_left rfl]
        exact hsubRhs r
      · have hne : j.1 ≠ i.1 := fun h => hji (Fin.ext h)
        rw [ite_eq_right hne, Matrix.updateCol_apply, ite_eq_right hji]
        exact hentry r j
    rw [h1, detRows_eq_det_of_rowEntry _ hup_len hup_entry, ← Matrix.cramer_apply]
    rfl
  exact ⟨hlen_cv, hget⟩

private lemma isFeasibleBasisRows_iff {m n k : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    have hcard : (finsetOfList m n T).card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    isFeasibleBasisRows k (m + n) allRows rhsAll T = true ↔
      IsFeasibleBasis M_int b_int (finsetOfList m n T) hcard := by
  intro hcard
  obtain ⟨_, _, hdet⟩ := subRows_eq_basisMat M_int allRows hall hsort hlt hlen
  obtain ⟨_, hcv⟩ := cramerVecRows_eq_cramerVec M_int b_int allRows rhsAll hall hrhs hsort hlt hlen
  have hdot : ∀ r : Fin (m + n),
      ListMatrix.dotProduct k ((List.range k).map fun j => rowEntry allRows r.1 j)
        (cramerVecRows k (subRows k allRows T) (subRhs rhsAll T)) =
        M_int (finSumFinEquiv.symm r) ⬝ᵥ cramerVec M_int b_int (finsetOfList m n T) hcard := by
    intro r
    rw [ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [List.getD_map_range _ 0 j.2, hall r j, hcv j]
  simp only [isFeasibleBasisRows, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, hdet, IsFeasibleBasis]
  constructor
  · rintro ⟨hne, hall_le⟩
    refine ⟨hne, fun r => ?_⟩
    let r' := finSumFinEquiv r
    have h1 := hall_le r'.1 r'.2
    have h2 : finSumFinEquiv.symm r' = r := Equiv.symm_apply_apply finSumFinEquiv r
    rw [hdot r', rowEntry_single, hrhs r', h2] at h1
    exact h1
  · rintro ⟨hne, hall_le⟩
    refine ⟨hne, fun r hr => ?_⟩
    have h1 := hall_le (finSumFinEquiv.symm ⟨r, hr⟩)
    rw [rowEntry_single rhsAll r, hrhs ⟨r, hr⟩, hdot ⟨r, hr⟩]
    exact h1

/-! ### Section 2: Executable pivoting, Shapley orientation, and PPAD graph -/

private lemma finSumFinEquiv_symm_of_lt {m n r : ℕ} (hr : r < m) :
    finSumFinEquiv.symm ⟨r, Nat.lt_of_lt_of_le hr (Nat.le_add_right m n)⟩ = Sum.inl ⟨r, hr⟩ := by
  apply finSumFinEquiv.injective
  simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left, Fin.castAdd_mk]

private lemma finSumFinEquiv_symm_of_le {m n r : ℕ} (hm : m ≤ r) (hr : r < m + n) :
    finSumFinEquiv.symm ⟨r, hr⟩ = Sum.inr ⟨r - m, by omega⟩ := by
  apply finSumFinEquiv.injective
  simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right, Fin.natAdd_mk]
  ext
  simp only
  omega

private lemma rowEntry_tabulateTable_sumElim {m n k : ℕ} {h : ℕ → ℕ → ℤ}
    {M : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ}
    (hl : ∀ (i : Fin m) (j : Fin k), h i.1 j.1 = M (.inl i) j)
    (hr : ∀ (i : Fin n) (j : Fin k), h (m + i.1) j.1 = M (.inr i) j)
    (r : Fin (m + n)) (j : Fin k) :
    rowEntry (tabulateTable (m + n) k h) r.1 j.1 = M (finSumFinEquiv.symm r) j := by
  rw [rowEntry_tabulateTable, ite_eq_left ⟨r.2, j.2⟩]
  by_cases hlt : r.1 < m
  · have hr' : r = ⟨r.1, by omega⟩ := Fin.ext rfl
    rw [hr', finSumFinEquiv_symm_of_lt hlt]
    exact hl ⟨r.1, hlt⟩ j
  · have hm : m ≤ r.1 := Nat.le_of_not_lt hlt
    rw [finSumFinEquiv_symm_of_le hm r.2, ← hr ⟨r.1 - m, by omega⟩ j]
    exact congrFun (congrArg h (by dsimp only; omega)) j.1

private lemma neg_one_diag_ite {k : ℕ} (a b : Fin k) :
    (if b.1 = a.1 then (-1 : ℤ) else 0) = if a = b then -1 else 0 := by
  by_cases hab : a = b
  · subst hab; simp
  · have hne : b.1 ≠ a.1 := fun h => hab (Fin.ext h.symm)
    rw [ite_eq_right hne, ite_eq_right hab]

private lemma allRowsP_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) (j : Fin c.rows) :
    rowEntry (allRowsP c) r.1 j.1 = intMatP (posMatB c) (finSumFinEquiv.symm r) j :=
  rowEntry_tabulateTable_sumElim
    (fun i j => by rw [ite_eq_left i.2, intMatP_inl, neg_one_diag_ite])
    (fun i j => by simp [intMatP_inr, posMatB, rowEntry]) r j

private lemma allRowsQ_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) (j : Fin c.cols) :
    rowEntry (allRowsQ c) r.1 j.1 = intMatQ (posMatA c) (finSumFinEquiv.symm r) j :=
  rowEntry_tabulateTable_sumElim
    (fun i j => by rw [ite_eq_left i.2, intMatQ_inl]; rfl)
    (fun i j => by
      have hnot : ¬ c.rows + i.1 < c.rows := by omega
      rw [ite_eq_right hnot, Nat.add_sub_cancel_left, intMatQ_inr, neg_one_diag_ite]) r j

private lemma getD_map_range_sumElim {m n : ℕ} {h : ℕ → ℤ}
    {f' : Fin m → ℤ} {g' : Fin n → ℤ}
    (hf : ∀ i : Fin m, h i.1 = f' i)
    (hg : ∀ j : Fin n, h (m + j.1) = g' j) (r : Fin (m + n)) :
    ((List.range (m + n)).map h).getD r.1 0 = Sum.elim f' g' (finSumFinEquiv.symm r) := by
  rw [List.getD_map_range _ 0 r.2]
  by_cases hr : r.1 < m
  · have hr' : r = ⟨r.1, by omega⟩ := Fin.ext rfl
    rw [hr', finSumFinEquiv_symm_of_lt hr, Sum.elim_inl]
    exact hf ⟨r.1, hr⟩
  · have hm : m ≤ r.1 := Nat.le_of_not_lt hr
    rw [finSumFinEquiv_symm_of_le hm r.2, Sum.elim_inr, ← hg ⟨r.1 - m, by omega⟩]
    exact congrArg h (by dsimp only; omega)

private lemma allRhsP_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allRhsP c).getD r.1 0 =
      pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => ite_eq_left i.2) (fun _ => by simp [pow_mul]) r

private lemma allRhsQ_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allRhsQ c).getD r.1 0 =
      pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => by simp [i.2, pow_mul]) (fun _ => by simp) r

private lemma allIntRhsP_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allIntRhsP c).getD r.1 0 = intRhsP c.rows c.cols (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => ite_eq_left i.2) (fun _ => by simp) r

private lemma allIntRhsQ_spec (c : BimatrixCode) (r : Fin (c.rows + c.cols)) :
    (allIntRhsQ c).getD r.1 0 = intRhsQ c.rows c.cols (finSumFinEquiv.symm r) :=
  getD_map_range_sumElim (fun i => ite_eq_left i.2) (fun _ => by simp) r

private lemma pertP_nondegenerate {c : BimatrixCode} (hc : c.WellFormed) :
    IsNondegenerateSystem
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) :=
  isNondegenerateSystem_pertP (posMat_bounds hc ⟨0, hc.1⟩ ⟨0, hc.2.1⟩).1
    (fun i j => ⟨(posMat_bounds hc i j).2.2.2.1, (posMat_bounds hc i j).2.2.2.2⟩)
    (by exact_mod_cast kernelVecBound_mul_lt_two_pow_bitBound hc.1 hc.2.1)

private lemma pertQ_nondegenerate {c : BimatrixCode} (hc : c.WellFormed) :
    IsNondegenerateSystem
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) :=
  isNondegenerateSystem_pertQ (posMat_bounds hc ⟨0, hc.1⟩ ⟨0, hc.2.1⟩).1
    (fun i j => ⟨(posMat_bounds hc i j).2.1, (posMat_bounds hc i j).2.2.1⟩)
    (by exact_mod_cast kernelVecBound_mul_lt_two_pow_bitBound_symm hc.1 hc.2.1)

private lemma pertP_recession {c : BimatrixCode} (hc : c.WellFormed) (v : Fin c.rows → ℚ)
    (hv : ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ) *ᵥ
      v ≤ 0) :
    v = 0 :=
  recession_intMatP hc.2.1 (fun i j => (posMat_bounds hc i j).2.2.2.1) v hv

private lemma pertQ_recession {c : BimatrixCode} (hc : c.WellFormed) (v : Fin c.cols → ℚ)
    (hv : ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ) *ᵥ
      v ≤ 0) :
    v = 0 :=
  recession_intMatQ hc.1 (fun i j => (posMat_bounds hc i j).2.1) v hv

/-- Sorted replacement `(T \ {l}) ∪ {c}` bounded below `d`. -/
private def replaceSorted (d : ℕ) (T : List ℕ) (l c : ℕ) : List ℕ :=
  (List.range d).filter fun x => decide (x = c) || (decide (x ∈ T) && !decide (x = l))

private lemma replaceSorted_sorted (d : ℕ) (T : List ℕ) (l c : ℕ) :
    (replaceSorted d T l c).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma replaceSorted_lt {d : ℕ} {T : List ℕ} {l c x : ℕ}
    (hx : x ∈ replaceSorted d T l c) : x < d := by
  simp only [replaceSorted, List.mem_filter, List.mem_range] at hx
  exact hx.1

private lemma mem_replaceSorted {d : ℕ} {T : List ℕ} {l c x : ℕ} :
    x ∈ replaceSorted d T l c ↔ x < d ∧ (x = c ∨ (x ∈ T ∧ x ≠ l)) := by
  simp only [replaceSorted, List.mem_filter, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]

private lemma finsetOfList_replaceSorted {m n : ℕ} {T : List ℕ}
    {l' c' : Fin m ⊕ Fin n} :
    finsetOfList m n (replaceSorted (m + n) T (finSumFinEquiv l').1 (finSumFinEquiv c').1) =
      insert c' ((finsetOfList m n T).erase l') := by
  ext r
  have heq : ∀ a b : Fin m ⊕ Fin n, (finSumFinEquiv a).1 = (finSumFinEquiv b).1 ↔ a = b :=
    fun a b => ⟨fun h => finSumFinEquiv.injective (Fin.ext h),
      congrArg fun z => (finSumFinEquiv z).1⟩
  simp only [mem_finsetOfList, Finset.mem_insert, Finset.mem_erase, mem_replaceSorted,
    (finSumFinEquiv r).2, true_and, ne_eq, heq, and_comm]

private lemma replaceSorted_polytime {α : Type} {encIn : α ↪ List Bool}
    {d : α → ℕ} {T : α → List ℕ} {l c : α → ℕ}
    (hd : ComputableInPolyTime d encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList encUnary))
    (hl : ComputableInPolyTime l encIn encUnary)
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => replaceSorted (d x) (T x) (l x) (c x))
      encIn (encList encUnary) := by
  unfold replaceSorted
  refine filterWithInput (range.comp hd) ?_
  have hx := fst encIn encUnary
  have he := snd encIn encUnary
  exact bool_or' (decide_eq' he (hc.comp hx))
    (bool_and' (decide_mem (hT.comp hx) he) (bool_not.comp (decide_eq' he (hl.comp hx))))

/-- Executable pivot step on a sorted basis list `T` dropping label `l`. -/
private def pivotBasisRows (k d : ℕ) (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (T : List ℕ) (l : ℕ) : List ℕ :=
  ((List.range d).find? fun c =>
    !decide (c ∈ T) && isFeasibleBasisRows k d allRows rhsAll (replaceSorted d T l c)).elim T
    (replaceSorted d T l)

private theorem pivotBasisRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {k d : α → ℕ} {allRows : α → List (List ℤ)} {rhsAll : α → List ℤ}
    {T : α → List ℕ} {l : α → ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hrhs : ComputableInPolyTime rhsAll encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary))
    (hl : ComputableInPolyTime l encIn encUnary) :
    ComputableInPolyTime (fun x => pivotBasisRows (k x) (d x) (allRows x) (rhsAll x) (T x) (l x))
      encIn (encList encUnary) := by
  unfold pivotBasisRows
  have hfind : ComputableInPolyTime
      (fun x => (List.range (d x)).find? fun c =>
        !decide (c ∈ T x) &&
          isFeasibleBasisRows (k x) (d x) (allRows x) (rhsAll x)
            (replaceSorted (d x) (T x) (l x) c))
      encIn (encOption encUnary) := by
    refine findWithInput (range.comp hd) ?_
    have hx := fst encIn encUnary
    have hc := snd encIn encUnary
    have hrep := replaceSorted_polytime (hd.comp hx) (hT.comp hx) (hl.comp hx) hc
    exact bool_and' (bool_not.comp (decide_mem (hT.comp hx) hc))
      (isFeasibleBasisRows_polytime (hk.comp hx) (hd.comp hx) (hall.comp hx) (hrhs.comp hx) hrep)
  exact optionElimWithInput hfind hT
    (replaceSorted_polytime (hd.comp (fst encIn encUnary)) (hT.comp (fst encIn encUnary))
      (hl.comp (fst encIn encUnary)) (snd encIn encUnary))

private lemma pivotBasisRows_spec {m n k : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
      (fun r => (b_int r : ℚ)))
    (hrec : ∀ v : Fin k → ℚ,
      (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ) *ᵥ v ≤ 0 → v = 0)
    {T : List ℕ} (_hsort : T.Pairwise (· < ·)) (_hlt : ∀ r ∈ T, r < m + n) (_hlen : T.length = k)
    (hcard : (finsetOfList m n T).card = k)
    (hfb : IsFeasibleBasis M_int b_int (finsetOfList m n T) hcard)
    {l' : Fin m ⊕ Fin n} (hl' : l' ∈ finsetOfList m n T) :
    let l := (finSumFinEquiv l').1
    let T' := pivotBasisRows k (m + n) allRows rhsAll T l
    let x := ratBasisSol M_int b_int (finsetOfList m n T) hcard
    T'.Pairwise (· < ·) ∧ (∀ r ∈ T', r < m + n) ∧ T'.length = k ∧
      ∃ hcard' : (finsetOfList m n T').card = k,
        IsFeasibleBasis M_int b_int (finsetOfList m n T') hcard' ∧
          finsetOfList m n T' = tightRows (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
            (fun r => (b_int r : ℚ))
            (pivotVertex (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
              (fun r => (b_int r : ℚ)) x l') := by
  intro l T' x
  set M_Q : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ := M_int.map Int.cast
  set b_Q : Fin m ⊕ Fin n → ℚ := fun r => (b_int r : ℚ)
  obtain ⟨hx_v, _⟩ := isVertex_ratBasisSol_of_isFeasibleBasis hfb (K := ℚ)
  have htx : tightRows M_Q b_Q x = finsetOfList m n T := tightRows_ratBasisSol_eq hfb hnd
  have hl_tight : l' ∈ tightRows M_Q b_Q x := htx ▸ hl'
  obtain ⟨hy_v, hyx, hy_sub⟩ := hx_v.pivotVertex_spec hnd hrec hl_tight
  set y := pivotVertex M_Q b_Q x l'
  obtain ⟨hTy, hfb_y, -⟩ := exists_isFeasibleBasis_of_isVertex hnd hy_v
  set T_y := tightRows M_Q b_Q y
  have hTy' : T_y.card = k := hTy
  have hl'_not_y : l' ∉ T_y := hx_v.notMem_tightRows_pivotVertex hnd hrec hl_tight
  have hsub_erase : (finsetOfList m n T).erase l' ⊆ T_y := htx ▸ hy_sub
  have hcard_erase : ((finsetOfList m n T).erase l').card = k - 1 := by
    rw [Finset.card_erase_of_mem hl', hcard]
  have hkpos : 1 ≤ k := by
    rw [← hcard]
    exact Finset.card_pos.2 ⟨l', hl'⟩
  have hcard_sdiff : (T_y \ (finsetOfList m n T).erase l').card = 1 := by
    have hadd := Finset.card_sdiff_add_card_inter T_y ((finsetOfList m n T).erase l')
    have hinter : T_y ∩ (finsetOfList m n T).erase l' = (finsetOfList m n T).erase l' :=
      Finset.inter_eq_right.2 hsub_erase
    rw [hinter, hTy', hcard_erase] at hadd
    omega
  obtain ⟨c', hc'eq⟩ := Finset.card_eq_one.1 hcard_sdiff
  have hc'_sdiff : c' ∈ T_y \ (finsetOfList m n T).erase l' := by simp [hc'eq]
  have hc'_y : c' ∈ T_y := (Finset.mem_sdiff.1 hc'_sdiff).1
  have hc'_not_erase : c' ∉ (finsetOfList m n T).erase l' := (Finset.mem_sdiff.1 hc'_sdiff).2
  have hc'_ne_l' : c' ≠ l' := fun h => hl'_not_y (h ▸ hc'_y)
  have hc'_not_Tset : c' ∉ finsetOfList m n T := fun h =>
    hc'_not_erase (Finset.mem_erase.2 ⟨hc'_ne_l', h⟩)
  have hTy_eq : T_y = insert c' ((finsetOfList m n T).erase l') := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      by_cases hzc : z = c'
      · exact hzc ▸ Finset.mem_insert_self _ _
      · have hzs : z ∈ T_y \ (finsetOfList m n T).erase l' → False := by
          intro hm
          rw [hc'eq, Finset.mem_singleton] at hm
          exact hzc hm
        by_contra hnot
        exact hzs (Finset.mem_sdiff.2 ⟨hz, fun hm => hnot (Finset.mem_insert_of_mem hm)⟩)
    · rw [Finset.card_insert_of_notMem hc'_not_erase, hcard_erase, hTy']
      omega
  set cNat := (finSumFinEquiv c').1
  have hcNat_lt : cNat < m + n := (finSumFinEquiv c').2
  have hcNat_not_T : cNat ∉ T := fun h => hc'_not_Tset (mem_finsetOfList.2 h)
  have hrep_c_fin : finsetOfList m n (replaceSorted (m + n) T l cNat) = T_y := by
    rw [finsetOfList_replaceSorted, hTy_eq]
  have hrep_c_sort : (replaceSorted (m + n) T l cNat).Pairwise (· < ·) :=
    replaceSorted_sorted _ _ _ _
  have hrep_c_lt : ∀ r ∈ replaceSorted (m + n) T l cNat, r < m + n := fun _ hr =>
    replaceSorted_lt hr
  have hrep_c_len : (replaceSorted (m + n) T l cNat).length = k := by
    have hc1 := card_finsetOfList hrep_c_sort.nodup hrep_c_lt
    rw [hrep_c_fin, hTy'] at hc1
    exact hc1.symm
  have hfb_rep_c : IsFeasibleBasis M_int b_int
      (finsetOfList m n (replaceSorted (m + n) T l cNat))
      ((card_finsetOfList hrep_c_sort.nodup hrep_c_lt).trans hrep_c_len) := by
    have hEq := hrep_c_fin
    revert hfb_y
    simp only [hEq]
    exact fun h => h
  have htest_c :
      (!decide (cNat ∈ T) &&
        isFeasibleBasisRows k (m + n) allRows rhsAll (replaceSorted (m + n) T l cNat)) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hcNat_not_T,
      (isFeasibleBasisRows_iff M_int b_int allRows rhsAll hall hrhs hrep_c_sort hrep_c_lt
        hrep_c_len).2 hfb_rep_c⟩
  set pred := fun c => !decide (c ∈ T) &&
    isFeasibleBasisRows k (m + n) allRows rhsAll (replaceSorted (m + n) T l c)
  have hne_none : (List.range (m + n)).find? pred ≠ none := by
    intro hnone
    have hfalse := (List.find?_eq_none.1 hnone) cNat (List.mem_range.2 hcNat_lt)
    exact hfalse htest_c
  obtain ⟨c₀, hfind⟩ := Option.ne_none_iff_exists'.1 hne_none
  have hT'_eq : T' = replaceSorted (m + n) T l c₀ := by
    dsimp only [T', pivotBasisRows]
    change ((List.range (m + n)).find? pred).elim T (replaceSorted (m + n) T l) = _
    rw [hfind]
    rfl
  have hc₀_mem : c₀ ∈ List.range (m + n) := List.mem_of_find?_eq_some hfind
  have hc₀_lt : c₀ < m + n := List.mem_range.1 hc₀_mem
  have hc₀_pred : pred c₀ = true := List.find?_some hfind
  simp only [pred, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc₀_pred
  obtain ⟨hc₀_not_T, hc₀_feas⟩ := hc₀_pred
  have hT'_sort : T'.Pairwise (· < ·) := hT'_eq ▸ replaceSorted_sorted _ _ _ _
  have hT'_lt : ∀ r ∈ T', r < m + n := fun _ hr => replaceSorted_lt (hT'_eq ▸ hr)
  set c₀' : Fin m ⊕ Fin n := finSumFinEquiv.symm ⟨c₀, hc₀_lt⟩
  have hc₀'_val : (finSumFinEquiv c₀').1 = c₀ :=
    congrArg Fin.val (Equiv.apply_symm_apply finSumFinEquiv ⟨c₀, hc₀_lt⟩)
  have hc₀'_not_Tset : c₀' ∉ finsetOfList m n T := by
    rw [mem_finsetOfList, hc₀'_val]
    exact hc₀_not_T
  have hc₀'_not_erase : c₀' ∉ (finsetOfList m n T).erase l' := fun h =>
    hc₀'_not_Tset (Finset.mem_erase.1 h).2
  have hT'_fin : finsetOfList m n T' = insert c₀' ((finsetOfList m n T).erase l') := by
    rw [hT'_eq, ← hc₀'_val]
    exact finsetOfList_replaceSorted
  have hT'_card : (finsetOfList m n T').card = k := by
    rw [hT'_fin, Finset.card_insert_of_notMem hc₀'_not_erase, hcard_erase]
    omega
  have hT'_len : T'.length = k := (card_finsetOfList hT'_sort.nodup hT'_lt).symm.trans hT'_card
  have hfb_T' : IsFeasibleBasis M_int b_int (finsetOfList m n T')
      ((card_finsetOfList hT'_sort.nodup hT'_lt).trans hT'_len) :=
    (isFeasibleBasisRows_iff M_int b_int allRows rhsAll hall hrhs hT'_sort hT'_lt hT'_len).1
      (hT'_eq ▸ hc₀_feas)
  set z := ratBasisSol M_int b_int (finsetOfList m n T')
    ((card_finsetOfList hT'_sort.nodup hT'_lt).trans hT'_len)
  have hz_v : IsVertex M_Q b_Q z := (isVertex_ratBasisSol_of_isFeasibleBasis hfb_T' (K := ℚ)).1
  have htz : tightRows M_Q b_Q z = finsetOfList m n T' := tightRows_ratBasisSol_eq hfb_T' hnd
  have hzx : z ≠ x := by
    intro hzx
    have hc₀_in_tz : c₀' ∈ tightRows M_Q b_Q z := by
      rw [htz, hT'_fin]
      exact Finset.mem_insert_self _ _
    rw [hzx, htx] at hc₀_in_tz
    exact hc₀'_not_Tset hc₀_in_tz
  have hz_erase : (tightRows M_Q b_Q x).erase l' ⊆ tightRows M_Q b_Q z := by
    rw [htx, htz, hT'_fin]
    exact Finset.subset_insert _ _
  have hzy : z = y := hx_v.eq_pivotVertex hnd hrec hl_tight hz_v hzx hz_erase
  refine ⟨hT'_sort, hT'_lt, hT'_len, hT'_card, hfb_T', ?_⟩
  rw [← htz, hzy]

private lemma leaveLabel_comm {κ : Type*} [DecidableEq κ] [LinearOrder κ]
    (A B : Finset κ) (k₀ : κ) :
    LemkeHowson.leaveLabel A B k₀ = LemkeHowson.leaveLabel B A k₀ := by
  simp only [LemkeHowson.leaveLabel, Finset.union_comm A B, Finset.inter_comm A B]

/-- Executable tie-breaking leaving label matching `ShapleyOrientation.leaveLabel` for `k₀ = 0`. -/
private def leaveLabelExec (T₁ T₂ : List ℕ) : ℕ :=
  if decide (0 ∈ T₁) || decide (0 ∈ T₂) then 0
  else (T₁.filter fun x => decide (x ∈ T₂)).getD 0 0

private theorem leaveLabelExec_polytime {α : Type} {encIn : α ↪ List Bool}
    {T₁ T₂ : α → List ℕ}
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => leaveLabelExec (T₁ x) (T₂ x)) encIn encUnary := by
  unfold leaveLabelExec
  refine ite' (bool_or' (decide_mem h1 (const 0)) (decide_mem h2 (const 0))) (const 0) ?_
  have hfilt : ComputableInPolyTime
      (fun x => (T₁ x).filter fun y => decide (y ∈ T₂ x)) encIn (encList encUnary) :=
    filterWithInput h1 (decide_mem (h2.comp (fst _ _)) (snd _ _))
  exact listGetDWithInput hfilt (const 0) 0

private lemma leaveLabelExec_eq {m n : ℕ} (hm : 0 < m)
    {T₁ T₂ : List ℕ} (hsort₁ : T₁.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < m + n) (_hlt₂ : ∀ r ∈ T₂, r < m + n) :
    (finSumFinEquiv (LemkeHowson.leaveLabel (finsetOfList m n T₁) (finsetOfList m n T₂)
      (Sum.inl ⟨0, hm⟩))).1 = leaveLabelExec T₁ T₂ := by
  set T₁s := finsetOfList m n T₁
  set T₂s := finsetOfList m n T₂
  set k₀ : Fin m ⊕ Fin n := Sum.inl ⟨0, hm⟩
  have hk₀_val : (finSumFinEquiv k₀).1 = 0 := rfl
  have hk₀_mem : k₀ ∈ T₁s ∪ T₂s ↔ 0 ∈ T₁ ∨ 0 ∈ T₂ := by
    simp only [Finset.mem_union, T₁s, T₂s, mem_finsetOfList, hk₀_val]
  by_cases h0 : 0 ∈ T₁ ∨ 0 ∈ T₂
  · simp only [LemkeHowson.leaveLabel, ite_eq_left (hk₀_mem.2 h0), leaveLabelExec, Bool.or_eq_true,
      decide_eq_true_eq, ite_eq_left h0, hk₀_val]
  · have hnmem : k₀ ∉ T₁s ∪ T₂s := fun h => h0 (hk₀_mem.1 h)
    simp only [LemkeHowson.leaveLabel, ite_eq_right hnmem, leaveLabelExec, Bool.or_eq_true,
      decide_eq_true_eq, ite_eq_right h0]
    by_cases hne : (T₁s ∩ T₂s).Nonempty
    · rw [dite_eq_left hne]
      have hmin_mem : (T₁s ∩ T₂s).min' hne ∈ T₁s ∩ T₂s := Finset.min'_mem _ hne
      set min_v := (finSumFinEquiv ((T₁s ∩ T₂s).min' hne)).1
      have hmin_T1 : min_v ∈ T₁ := mem_finsetOfList.1 (Finset.mem_inter.1 hmin_mem).1
      have hmin_T2 : min_v ∈ T₂ := mem_finsetOfList.1 (Finset.mem_inter.1 hmin_mem).2
      set F := T₁.filter fun x => decide (x ∈ T₂)
      have hmin_F : min_v ∈ F := List.mem_filter.2 ⟨hmin_T1, decide_eq_true hmin_T2⟩
      have hF_ne : F ≠ [] := List.ne_nil_of_mem hmin_F
      have hF_sort : F.Pairwise (· < ·) := hsort₁.filter _
      rcases hFc : F with _ | ⟨a, rest⟩
      · exact absurd hFc hF_ne
      · have ha_mem_F : a ∈ F := hFc ▸ List.mem_cons_self
        have ha_T1 : a ∈ T₁ := (List.mem_filter.1 ha_mem_F).1
        have ha_T2 : a ∈ T₂ := of_decide_eq_true (List.mem_filter.1 ha_mem_F).2
        have ha_lt : a < m + n := hlt₁ a ha_T1
        set a' : Fin m ⊕ Fin n := finSumFinEquiv.symm ⟨a, ha_lt⟩
        have ha'_val : (finSumFinEquiv a').1 = a :=
          congrArg Fin.val (Equiv.apply_symm_apply finSumFinEquiv ⟨a, ha_lt⟩)
        have ha'_mem : a' ∈ T₁s ∩ T₂s := Finset.mem_inter.2
          ⟨mem_finsetOfList.2 (ha'_val.symm ▸ ha_T1), mem_finsetOfList.2 (ha'_val.symm ▸ ha_T2)⟩
        have hle1 : (T₁s ∩ T₂s).min' hne ≤ a' := Finset.min'_le _ a' ha'_mem
        have hle1_nat : min_v ≤ a := by
          change (finSumFinEquiv ((T₁s ∩ T₂s).min' hne)).1 ≤ (finSumFinEquiv a').1 at hle1
          rwa [ha'_val] at hle1
        have hle2_nat : a ≤ min_v := by
          rcases List.mem_cons.1 (hFc ▸ hmin_F) with rfl | h
          · exact le_rfl
          · exact ((List.pairwise_cons.1 (hFc ▸ hF_sort)).1 min_v h).le
        exact le_antisymm hle1_nat hle2_nat
    · rw [dite_eq_right hne]
      have hF_empty : (T₁.filter fun x => decide (x ∈ T₂)) = [] := by
        by_contra hneF
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hneF
        have ha_T1 : a ∈ T₁ := (List.mem_filter.1 ha).1
        have ha_T2 : a ∈ T₂ := of_decide_eq_true (List.mem_filter.1 ha).2
        have ha_lt : a < m + n := hlt₁ a ha_T1
        set a' := finSumFinEquiv.symm ⟨a, ha_lt⟩
        have ha'_val : (finSumFinEquiv a').1 = a :=
          congrArg Fin.val (Equiv.apply_symm_apply finSumFinEquiv ⟨a, ha_lt⟩)
        exact hne ⟨a', Finset.mem_inter.2
          ⟨mem_finsetOfList.2 (ha'_val.symm ▸ ha_T1), mem_finsetOfList.2 (ha'_val.symm ▸ ha_T2)⟩⟩
      rw [hF_empty, List.getD_nil, hk₀_val]

/-- Image of `ShapleyOrientation.halfEdgeFun` on `[0 .. m+n-1]` for `k₀ = 0`. -/
private def halfEdgeList (T₁ T₂ : List ℕ) (side : Bool) : List ℕ :=
  let l := leaveLabelExec T₁ T₂
  (if !side then T₁.map fun x => if decide (x = l) then 0 else x else T₁) ++
    (if side then T₂.map fun x => if decide (x = l) then 0 else x else T₂)

private theorem halfEdgeList_polytime {α : Type} {encIn : α ↪ List Bool}
    {T₁ T₂ : α → List ℕ} {side : α → Bool}
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary))
    (hs : ComputableInPolyTime side encIn encBool) :
    ComputableInPolyTime (fun x => halfEdgeList (T₁ x) (T₂ x) (side x))
      encIn (encList encUnary) := by
  have hl := leaveLabelExec_polytime h1 h2
  have hmap : ∀ (T : α → List ℕ),
      ComputableInPolyTime T encIn (encList encUnary) →
      ComputableInPolyTime (fun x => (T x).map fun y =>
        if decide (y = leaveLabelExec (T₁ x) (T₂ x)) then 0 else y) encIn (encList encUnary) := by
    intro T hT
    refine mapWithInput hT ?_
    exact ite' (decide_eq' (snd _ _) (hl.comp (fst _ _))) (const 0) (snd _ _)
  unfold halfEdgeList
  exact listAppend' (ite' (bool_not.comp hs) (hmap T₁ h1) h1) (ite' hs (hmap T₂ h2) h2)

/-- `d × d` permutation matrix rows for index list `L`. -/
private def permRows (d : ℕ) (L : List ℕ) : List (List ℤ) :=
  tabulateTable d d fun i j => if decide (L.getD i 0 = j) then 1 else 0

private theorem permRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {d : α → ℕ} {L : α → List ℕ}
    (hd : ComputableInPolyTime d encIn encUnary)
    (hL : ComputableInPolyTime L encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => permRows (d x) (L x)) encIn encIntTable :=
  computableInPolyTime_tabulateTable hd hd
    (ite' (decide_eq'
        (listGetDWithInput (hL.comp ((fst encIn encUnary).comp (fst _ _)))
          ((snd encIn encUnary).comp (fst _ _)) 0)
        (snd _ _))
      (const (encOut := encIntBin) 1) (const (encOut := encIntBin) 0))

private lemma detRows_permRows {d : ℕ} (σ : Equiv.Perm (Fin d)) {L : List ℕ}
    (hL : ∀ i : Fin d, (σ i).1 = L.getD i.1 0) :
    detRows (permRows d L) = (Equiv.Perm.sign σ : ℤ) := by
  have hlen : (permRows d L).length = d := by simp [permRows, tabulateTable]
  have hentry : ∀ i j : Fin d,
      rowEntry (permRows d L) i.1 j.1 = ((1 : Matrix (Fin d) (Fin d) ℤ).submatrix σ id) i j := by
    intro i j
    dsimp only [permRows]
    rw [rowEntry_tabulateTable, ite_eq_left ⟨i.2, j.2⟩, Matrix.submatrix_apply, id_eq,
      Matrix.one_apply, ← hL i]
    by_cases hij : σ i = j
    · simp [hij]
    · simp [hij, Fin.val_ne_of_ne hij]
  simp [detRows_eq_det_of_rowEntry _ hlen hentry, Matrix.det_permute]

/-- Executable Shapley orientation index in `{-1, 0, 1}` using integer determinants. -/
private def halfEdgeIndexExec (c : BimatrixCode) (T₁ T₂ : List ℕ) (side : Bool) : ℤ :=
  let d := c.rows + c.cols
  let M₁ := subRows c.rows (allRowsP c) T₁
  let M₂ := subRows c.cols (allRowsQ c) T₂
  detRows (permRows d (halfEdgeList T₁ T₂ side)) * (detRows M₁).sign * (detRows M₂).sign

private theorem halfEdgeIndexExec_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {T₁ T₂ : α → List ℕ} {side : α → Bool}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (h1 : ComputableInPolyTime T₁ encIn (encList encUnary))
    (h2 : ComputableInPolyTime T₂ encIn (encList encUnary))
    (hs : ComputableInPolyTime side encIn encBool) :
    ComputableInPolyTime (fun x => halfEdgeIndexExec (c x) (T₁ x) (T₂ x) (side x))
      encIn encIntBin := by
  unfold halfEdgeIndexExec
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  have hperm := detRows_polytime.comp (permRows_polytime hd (halfEdgeList_polytime h1 h2 hs))
  have hm1 := detRows_polytime.comp
    (subRows_polytime hm (allRowsP_polytime.comp hc) h1)
  have hm2 := detRows_polytime.comp
    (subRows_polytime hn (allRowsQ_polytime.comp hc) h2)
  exact intBin_mul' (intBin_mul' hperm (intBin_sign.comp hm1)) (intBin_sign.comp hm2)

private lemma halfEdgeIndexExec_eq (c : BimatrixCode) (hm : 0 < c.rows)
    {T₁ T₂ : List ℕ} (hsort₁ : T₁.Pairwise (· < ·)) (hsort₂ : T₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < c.rows + c.cols) (hlt₂ : ∀ r ∈ T₂, r < c.rows + c.cols)
    (hlen₁ : T₁.length = c.rows) (hlen₂ : T₂.length = c.cols) (side : Bool)
    (hacl : ∀ k : Fin c.rows ⊕ Fin c.cols,
      k ≠ .inl ⟨0, hm⟩ → k ∈ finsetOfList c.rows c.cols T₁ ∨ k ∈ finsetOfList c.rows c.cols T₂)
    (hact : if side then .inl ⟨0, hm⟩ ∉ finsetOfList c.rows c.cols T₁
      else .inl ⟨0, hm⟩ ∉ finsetOfList c.rows c.cols T₂) :
    have hcard₁ : (finsetOfList c.rows c.cols T₁).card = c.rows :=
      (card_finsetOfList hsort₁.nodup hlt₁).trans hlen₁
    have hcard₂ : (finsetOfList c.rows c.cols T₂).card = c.cols :=
      (card_finsetOfList hsort₂.nodup hlt₂).trans hlen₂
    halfEdgeIndexExec c T₁ T₂ side =
      LemkeHowson.halfEdgeIndex
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
        (finsetOfList c.rows c.cols T₁) (finsetOfList c.rows c.cols T₂)
        hcard₁ hcard₂ (.inl ⟨0, hm⟩) side := by
  intro hcard₁ hcard₂
  set T₁s := finsetOfList c.rows c.cols T₁
  set T₂s := finsetOfList c.rows c.cols T₂
  set k₀ : Fin c.rows ⊕ Fin c.cols := .inl ⟨0, hm⟩
  have hbij : Function.Bijective (LemkeHowson.halfEdgeFun T₁s T₂s hcard₁ hcard₂ k₀ side) :=
    LemkeHowson.halfEdgeFun_bijective_of_acl (Fintype.card_sum.trans (by simp)) hcard₁ hcard₂
      hacl hact
  rw [LemkeHowson.halfEdgeIndex, dite_eq_left hbij]
  dsimp only
  set π : Equiv.Perm (Fin c.rows ⊕ Fin c.cols) :=
    (Equiv.ofBijective _ hbij).trans (Equiv.refl _).symm
  set σ : Equiv.Perm (Fin (c.rows + c.cols)) := Equiv.permCongr finSumFinEquiv π
  have hσ_sign : (Equiv.Perm.sign σ : ℤ) = (Equiv.Perm.sign π : ℤ) := by
    rw [Equiv.Perm.sign_permCongr]
  have hleave := leaveLabelExec_eq hm hsort₁ hlt₁ hlt₂
  have hmap_leave : ∀ {k : ℕ} {T : List ℕ} (hlen : T.length = k)
      (hcard : (finsetOfList c.rows c.cols T).card = k) (j : Fin k)
      (hord : (finSumFinEquiv (((finsetOfList c.rows c.cols T).orderIsoOfFin hcard) j).1).1 =
        T.getD j.1 0),
      (finSumFinEquiv (if (((finsetOfList c.rows c.cols T).orderIsoOfFin hcard).toEquiv j :
          Fin c.rows ⊕ Fin c.cols) = LemkeHowson.leaveLabel T₁s T₂s k₀ then k₀
        else (((finsetOfList c.rows c.cols T).orderIsoOfFin hcard).toEquiv j :
          Fin c.rows ⊕ Fin c.cols))).1 =
        (T.map fun x => if decide (x = leaveLabelExec T₁ T₂) then 0 else x).getD j.1 0 := by
    intro k T hlen hcard j hord
    rw [List.getD_map_of_lt _ T 0 0 (hlen ▸ j.2)]
    have hiff : (((finsetOfList c.rows c.cols T).orderIsoOfFin hcard).toEquiv j :
          Fin c.rows ⊕ Fin c.cols) = LemkeHowson.leaveLabel T₁s T₂s k₀ ↔
        T.getD j.1 0 = leaveLabelExec T₁ T₂ :=
      ⟨fun h => by rw [← hord]; exact congrArg (fun z => (finSumFinEquiv z).1) h |>.trans hleave,
       fun h => finSumFinEquiv.injective (Fin.ext (hord.trans (h.trans hleave.symm)))⟩
    by_cases hc_eq : T.getD j.1 0 = leaveLabelExec T₁ T₂
    · rw [ite_eq_left (hiff.2 hc_eq), ite_eq_left (decide_eq_true hc_eq)]; rfl
    · have hne_c : decide (T.getD j.1 0 = leaveLabelExec T₁ T₂) ≠ true :=
        fun h => hc_eq (of_decide_eq_true h)
      rw [ite_eq_right (mt hiff.1 hc_eq), ite_eq_right hne_c]; exact hord
  have hσ_list : ∀ i : Fin (c.rows + c.cols),
      (σ i).1 = (halfEdgeList T₁ T₂ side).getD i.1 0 := by
    intro i
    change (finSumFinEquiv (LemkeHowson.halfEdgeFun T₁s T₂s hcard₁ hcard₂ k₀ side
      (finSumFinEquiv.symm i))).1 = (halfEdgeList T₁ T₂ side).getD i.1 0
    have hlhs_len :
        (if !side then T₁.map fun x => if decide (x = leaveLabelExec T₁ T₂) then 0 else x
          else T₁).length = c.rows := by
      cases side <;> simp [hlen₁]
    by_cases hi : i.1 < c.rows
    · have hi' : i = ⟨i.1, by omega⟩ := Fin.ext rfl
      have hget_app : (halfEdgeList T₁ T₂ side).getD i.1 0 =
          (if !side then T₁.map fun x => if decide (x = leaveLabelExec T₁ T₂) then 0 else x
            else T₁).getD i.1 0 :=
        List.getD_append _ _ 0 i.1 (by rw [hlhs_len]; exact hi)
      rw [hget_app, hi', finSumFinEquiv_symm_of_lt hi]
      have hord := orderIsoOfFin_finsetOfList hsort₁ hlt₁ hlen₁ hcard₁ ⟨i.1, hi⟩
      cases side
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inl, Bool.not_false, ↓reduceIte]
        exact hmap_leave hlen₁ hcard₁ ⟨i.1, hi⟩ hord
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inl, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        exact hord
    · have hge : c.rows ≤ i.1 := Nat.le_of_not_lt hi
      rw [finSumFinEquiv_symm_of_le hge i.2]
      dsimp only [halfEdgeList]
      rw [List.getD_append_right _ _ 0 i.1 (by rw [hlhs_len]; exact hge), hlhs_len]
      have hsub : i.1 - c.rows < c.cols := by omega
      have hord := orderIsoOfFin_finsetOfList hsort₂ hlt₂ hlen₂ hcard₂ ⟨i.1 - c.rows, hsub⟩
      cases side
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]
        exact hord
      · simp only [LemkeHowson.halfEdgeFun, Sum.elim_inr, ↓reduceIte]
        exact hmap_leave hlen₂ hcard₂ ⟨i.1 - c.rows, hsub⟩ hord
  have hdet_perm : detRows (permRows (c.rows + c.cols) (halfEdgeList T₁ T₂ side)) =
      (Equiv.Perm.sign π : ℤ) :=
    (detRows_permRows σ hσ_list).trans hσ_sign
  have hcast_det : ∀ {k : ℕ} (M : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin k) ℤ)
      (Ts : Finset (Fin c.rows ⊕ Fin c.cols)) (hcard : Ts.card = k),
      ((M.map Int.cast : Matrix _ _ ℚ).submatrix
        (fun i => (Ts.orderIsoOfFin hcard i : Fin c.rows ⊕ Fin c.cols)) (Equiv.refl _)).det =
        ((basisMat M Ts hcard).det : ℚ) := fun M Ts hcard => by
    rw [show (M.map Int.cast : Matrix _ _ ℚ).submatrix
          (fun i => (Ts.orderIsoOfFin hcard i : Fin c.rows ⊕ Fin c.cols)) (Equiv.refl _) =
          (basisMat M Ts hcard).map Int.cast from rfl, ← Int.cast_det]
  have hsub₁ := subRows_eq_basisMat (intMatP (posMatB c)) (allRowsP c) (allRowsP_spec c)
    hsort₁ hlt₁ hlen₁
  have hsub₂ := subRows_eq_basisMat (intMatQ (posMatA c)) (allRowsQ c) (allRowsQ_spec c)
    hsort₂ hlt₂ hlen₂
  dsimp only [halfEdgeIndexExec]
  dsimp only [T₁s, T₂s] at hbij ⊢
  rw [hdet_perm, hsub₁.2.2, hsub₂.2.2, hcast_det (intMatP (posMatB c)) _ hcard₁,
    hcast_det (intMatQ (posMatA c)) _ hcard₂,
    LemkeHowson.signOfK_intCast, LemkeHowson.signOfK_intCast]

/-- Executable check that `u` encodes a valid `k₀ = 0`-almost-completely-labelled basis pair. -/
private def isValidNodeExec (c : BimatrixCode) (u : List Bool) : Bool :=
  let d := c.rows + c.cols
  let T₁ := decodeT₁ c u
  let T₂ := decodeT₂ c u
  c.wellFormedB &&
  decide (u.length = 2 * d) &&
  decide (T₁.length = c.rows) &&
  decide (T₂.length = c.cols) &&
  ((List.range d).all fun k => decide (k = 0) || decide (k ∈ T₁) || decide (k ∈ T₂)) &&
  isFeasibleBasisRows c.rows d (allRowsP c) (allRhsP c) T₁ &&
  isFeasibleBasisRows c.cols d (allRowsQ c) (allRhsQ c) T₂

@[local fun_prop]
private theorem isValidNodeExec_polytime :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => isValidNodeExec p.1 p.2)
      (encPair encBimatrix encBits) encBool := by
  unfold isValidNodeExec
  have hc := fst encBimatrix encBits
  have hu := snd encBimatrix encBits
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  have h1 := decodeT₁_polytime
  have h2 := decodeT₂_polytime
  have hall : ComputableInPolyTime
      (fun p : BimatrixCode × List Bool =>
        (List.range (p.1.rows + p.1.cols)).all fun k =>
          decide (k = 0) || decide (k ∈ decodeT₁ p.1 p.2) || decide (k ∈ decodeT₂ p.1 p.2))
      (encPair encBimatrix encBits) encBool := by
    refine allWithInput (range.comp hd) ?_
    have hp := fst (encPair encBimatrix encBits) encUnary
    have hk := snd (encPair encBimatrix encBits) encUnary
    exact bool_or' (bool_or' (decide_eq' hk (const 0)) (decide_mem (h1.comp hp) hk))
      (decide_mem (h2.comp hp) hk)
  have hf1 := isFeasibleBasisRows_polytime hm hd (allRowsP_polytime.comp hc)
    (allRhsP_polytime.comp hc) h1
  have hf2 := isFeasibleBasisRows_polytime hn hd (allRowsQ_polytime.comp hc)
    (allRhsQ_polytime.comp hc) h2
  refine bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
    (wellFormedB_polytime.comp hc)
    (decide_eq' (length_bits.comp hu) (unary_mul.comp ((const 2).prod hd))))
    (decide_eq' ((length_list encUnary).comp h1) hm))
    (decide_eq' ((length_list encUnary).comp h2) hn))
    hall) hf1) hf2

/-- Follow the active half-edge with orientation `-targetSign c` (`wantNeg = true`) or
`targetSign c` (`wantNeg = false`), fixing non-valid or non-matching nodes. -/
private def stepGraph (wantNeg : Bool) (c : BimatrixCode) (u : List Bool) : List Bool :=
  if !isValidNodeExec c u then u
  else
    let d := c.rows + c.cols
    let T₁ := decodeT₁ c u
    let T₂ := decodeT₂ c u
    let wanted := if wantNeg then -targetSign c else targetSign c
    let l := leaveLabelExec T₁ T₂
    if !decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁ T₂ false = wanted) then
      encodeNodes c (pivotBasisRows c.rows d (allRowsP c) (allRhsP c) T₁ l) T₂
    else if !decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂ true = wanted) then
      encodeNodes c T₁ (pivotBasisRows c.cols d (allRowsQ c) (allRhsQ c) T₂ l)
    else u

/-- Polynomial-time predecessor map on encoded Lemke–Howson graph nodes (`-targetSign c`). -/
def pred (p : BimatrixCode × List Bool) : List Bool := stepGraph true p.1 p.2

/-- Polynomial-time successor map on encoded Lemke–Howson graph nodes (`+targetSign c`). -/
def succ (p : BimatrixCode × List Bool) : List Bool := stepGraph false p.1 p.2

private theorem stepGraph_polytime (wantNeg : Bool) :
    ComputableInPolyTime (fun p : BimatrixCode × List Bool => stepGraph wantNeg p.1 p.2)
      (encPair encBimatrix encBits) encBits := by
  unfold stepGraph
  have hc := fst encBimatrix encBits
  have hu := snd encBimatrix encBits
  have hm := codeRows_polytime.comp hc
  have hn := codeCols_polytime.comp hc
  have hd := unary_add.comp (hm.prod hn)
  have h1 := decodeT₁_polytime
  have h2 := decodeT₂_polytime
  have hts := targetSign_polytime.comp hc
  have hwanted : ComputableInPolyTime
      (fun p : BimatrixCode × List Bool =>
        if wantNeg then -targetSign p.1 else targetSign p.1)
      (encPair encBimatrix encBits) encIntBin := by
    cases wantNeg
    · exact hts.of_enc_eq fun _ => rfl
    · exact (intBin_sub' (const 0) hts).of_enc_eq fun _ => by simp
  have hl := leaveLabelExec_polytime h1 h2
  have hidxL := halfEdgeIndexExec_polytime hc h1 h2 (const false)
  have hidxR := halfEdgeIndexExec_polytime hc h1 h2 (const true)
  have hpiv1 := pivotBasisRows_polytime hm hd (allRowsP_polytime.comp hc)
    (allRhsP_polytime.comp hc) h1 hl
  have hpiv2 := pivotBasisRows_polytime hn hd (allRowsQ_polytime.comp hc)
    (allRhsQ_polytime.comp hc) h2 hl
  have hleft := bool_and' (bool_not.comp (decide_mem h2 (const 0))) (decide_eq' hidxL hwanted)
  have hright := bool_and' (bool_not.comp (decide_mem h1 (const 0))) (decide_eq' hidxR hwanted)
  exact ite' (bool_not.comp isValidNodeExec_polytime) hu
    (ite' hleft (encodeNodes_polytime hc hpiv1 h2)
      (ite' hright (encodeNodes_polytime hc h1 hpiv2) hu))

private theorem pred_polytime :
    ComputableInPolyTime pred (encPair encBimatrix encBits) encBits :=
  stepGraph_polytime true

private theorem succ_polytime :
    ComputableInPolyTime succ (encPair encBimatrix encBits) encBits :=
  stepGraph_polytime false

private lemma length_stepGraph (wantNeg : Bool) (c : BimatrixCode) (u : List Bool)
    (hu : u.length = vertexLen c) : (stepGraph wantNeg c u).length = vertexLen c := by
  dsimp only [stepGraph]
  cases hv : isValidNodeExec c u
  · simpa using hu
  · have hwf : c.wellFormedB = true := by
      simp only [isValidNodeExec, Bool.and_eq_true] at hv
      exact hv.1.1.1.1.1.1
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp [length_encodeNodes, vertexLen, hwf, hu]

private lemma length_pred (c : BimatrixCode) (u : List Bool) (hu : u.length = vertexLen c) :
    (pred (c, u)).length = vertexLen c :=
  length_stepGraph true c u hu

private lemma length_succ (c : BimatrixCode) (u : List Bool) (hu : u.length = vertexLen c) :
    (succ (c, u)).length = vertexLen c :=
  length_stepGraph false c u hu

private lemma isFeasibleBasis_of_basisMat_eq_neg_one {κ : Type*}
    [LinearOrder κ] {k : ℕ} {M : Matrix κ (Fin k) ℤ} {b : κ → ℤ} {T : Finset κ}
    (hcard : T.card = k) (hB : basisMat M T hcard = -1)
    (hbT : ∀ i : Fin k, b (T.orderIsoOfFin hcard i) = 0) (hb_nn : ∀ r : κ, 0 ≤ b r) :
    IsFeasibleBasis M b T hcard := by
  have hdet : (basisMat M T hcard).det ≠ 0 := by
    rw [hB, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_ne_zero _ (by decide)
  have hcv : cramerVec M b T hcard = 0 := by
    have hmul : basisMat M T hcard *ᵥ cramerVec M b T hcard = 0 := by
      dsimp only [cramerVec]
      rw [Matrix.mulVec_cramer]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hbT i, mul_zero]
    rwa [hB, Matrix.neg_mulVec, Matrix.one_mulVec, neg_eq_zero] at hmul
  refine ⟨hdet, fun r => ?_⟩
  rw [hcv, dotProduct_zero, mul_zero]
  exact mul_nonneg (abs_nonneg _) (hb_nn r)

private lemma isValidNodeExec_zeroVertex {c : BimatrixCode} (hc : c.WellFormed) :
    isValidNodeExec c (zeroVertex (vertexLen c)) = true := by
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  have hvlen : vertexLen c = 2 * (c.rows + c.cols) := by simp [vertexLen, hwb]
  have hT₁_eq : decodeT₁ c (zeroVertex (2 * (c.rows + c.cols))) = List.range c.rows :=
    decodeT₁_zeroVertex c
  have hT₂_eq : decodeT₂ c (zeroVertex (2 * (c.rows + c.cols))) =
      (List.range c.cols).map (· + c.rows) := decodeT₂_zeroVertex c
  have hsort₁ : (List.range c.rows).Pairwise (· < ·) := List.pairwise_lt_range
  have hsort₂ : ((List.range c.cols).map (· + c.rows)).Pairwise (· < ·) :=
    List.pairwise_lt_range.map _ fun _ _ h => by omega
  have hlt₁ : ∀ r ∈ List.range c.rows, r < c.rows + c.cols := fun r hr => by
    rw [List.mem_range] at hr; omega
  have hlt₂ : ∀ r ∈ (List.range c.cols).map (· + c.rows), r < c.rows + c.cols := by
    intro r hr
    rcases List.mem_map.1 hr with ⟨j, hj, rfl⟩
    rw [List.mem_range] at hj
    omega
  have hlen₁ : (List.range c.rows).length = c.rows := List.length_range
  have hlen₂ : ((List.range c.cols).map (· + c.rows)).length = c.cols := by simp
  have hcard₁ : (finsetOfList c.rows c.cols (List.range c.rows)).card = c.rows :=
    (card_finsetOfList hsort₁.nodup hlt₁).trans hlen₁
  have hcard₂ : (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))).card =
      c.cols := (card_finsetOfList hsort₂.nodup hlt₂).trans hlen₂
  have ho₁ (i : Fin c.rows) :
      ((finsetOfList c.rows c.cols (List.range c.rows)).orderIsoOfFin hcard₁ i).1 = Sum.inl i := by
    have ho := orderIsoOfFin_finsetOfList hsort₁ hlt₁ hlen₁ hcard₁ i
    rw [List.getD_eq_getElem _ 0 (by simp [i.2]), List.getElem_range] at ho
    apply finSumFinEquiv.injective
    ext
    exact ho
  have ho₂ (i : Fin c.cols) :
      ((finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))).orderIsoOfFin
        hcard₂ i).1 = Sum.inr i := by
    have ho := orderIsoOfFin_finsetOfList hsort₂ hlt₂ hlen₂ hcard₂ i
    rw [List.getD_map_range _ 0 i.2] at ho
    apply finSumFinEquiv.injective
    ext
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
    omega
  have hB₁_neg : basisMat (intMatP (posMatB c))
      (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁ = -1 := by
    ext i j
    dsimp only [basisMat, Matrix.submatrix_apply, id_eq]
    rw [ho₁ i, intMatP_inl]
    by_cases hij : i = j <;> simp [hij]
  have hB₂_neg : basisMat (intMatQ (posMatA c))
      (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂ = -1 := by
    ext i j
    dsimp only [basisMat, Matrix.submatrix_apply, id_eq]
    rw [ho₂ i, intMatQ_inr]
    by_cases hij : i = j <;> simp [hij]
  have hfb₁ : IsFeasibleBasis (intMatP (posMatB c))
      (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
      (finsetOfList c.rows c.cols (List.range c.rows)) hcard₁ :=
    isFeasibleBasis_of_basisMat_eq_neg_one hcard₁ hB₁_neg
      (fun i => by simp [ho₁ i, pertRhsPInt]) fun
      | .inl _ => by simp [pertRhsPInt]
      | .inr _ => by simp only [pertRhsPInt, Sum.elim_inr]; positivity
  have hfb₂ : IsFeasibleBasis (intMatQ (posMatA c))
      (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
      (finsetOfList c.rows c.cols ((List.range c.cols).map (· + c.rows))) hcard₂ :=
    isFeasibleBasis_of_basisMat_eq_neg_one hcard₂ hB₂_neg
      (fun i => by simp [ho₂ i, pertRhsQInt]) fun
      | .inl _ => by simp only [pertRhsQInt, Sum.elim_inl]; positivity
      | .inr _ => by simp [pertRhsQInt]
  have hf1 : isFeasibleBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c)
      (List.range c.rows) = true :=
    (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
      hsort₁ hlt₁ hlen₁).2 hfb₁
  have hf2 : isFeasibleBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c)
      ((List.range c.cols).map (· + c.rows)) = true :=
    (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
      hsort₂ hlt₂ hlen₂).2 hfb₂
  have hall : ((List.range (c.rows + c.cols)).all fun k =>
      decide (k = 0) || decide (k ∈ List.range c.rows) ||
        decide (k ∈ (List.range c.cols).map (· + c.rows))) = true := by
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_range, List.mem_map]
    by_cases hkr : k < c.rows
    · exact .inl (.inr hkr)
    · exact .inr ⟨k - c.rows, by omega, by omega⟩
  simp only [isValidNodeExec, hwb, hvlen, length_zeroVertex, hT₁_eq, hT₂_eq, hlen₁, hlen₂, hall,
    hf1, hf2, decide_true, Bool.and_self]

private lemma validNode_props {c : BimatrixCode} (hc : c.WellFormed) {u : List Bool}
    (hu : isValidNodeExec c u = true) :
    u.length = 2 * (c.rows + c.cols) ∧
      (decodeT₁ c u).length = c.rows ∧ (decodeT₂ c u).length = c.cols ∧
      (∀ k : Fin c.rows ⊕ Fin c.cols, k ≠ .inl ⟨0, hc.1⟩ →
        k ∈ finsetOfList c.rows c.cols (decodeT₁ c u) ∨
          k ∈ finsetOfList c.rows c.cols (decodeT₂ c u)) ∧
      ∃ (h1 : (finsetOfList c.rows c.cols (decodeT₁ c u)).card = c.rows)
        (h2 : (finsetOfList c.rows c.cols (decodeT₂ c u)).card = c.cols),
        IsFeasibleBasis (intMatP (posMatB c))
          (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
          (finsetOfList c.rows c.cols (decodeT₁ c u)) h1 ∧
        IsFeasibleBasis (intMatQ (posMatA c))
          (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
          (finsetOfList c.rows c.cols (decodeT₂ c u)) h2 := by
  simp only [isValidNodeExec, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hu
  rcases hu with ⟨⟨⟨⟨⟨⟨_, hlen_u⟩, hlen₁⟩, hlen₂⟩, hall⟩, hf1⟩, hf2⟩
  have hlt₁ : ∀ r ∈ decodeT₁ c u, r < c.rows + c.cols := fun _ hr => decodeT₁_lt c u hr
  have hlt₂ : ∀ r ∈ decodeT₂ c u, r < c.rows + c.cols := fun _ hr => decodeT₂_lt c u hr
  have hcard₁ : (finsetOfList c.rows c.cols (decodeT₁ c u)).card = c.rows :=
    (card_finsetOfList (decodeT₁_sorted c u).nodup hlt₁).trans hlen₁
  have hcard₂ : (finsetOfList c.rows c.cols (decodeT₂ c u)).card = c.cols :=
    (card_finsetOfList (decodeT₂_sorted c u).nodup hlt₂).trans hlen₂
  have hacl : ∀ k : Fin c.rows ⊕ Fin c.cols, k ≠ .inl ⟨0, hc.1⟩ →
      k ∈ finsetOfList c.rows c.cols (decodeT₁ c u) ∨
        k ∈ finsetOfList c.rows c.cols (decodeT₂ c u) := by
    intro k hk
    have hkne : (finSumFinEquiv k).1 ≠ 0 := by
      intro h0
      apply hk
      apply finSumFinEquiv.injective
      ext
      exact h0
    rcases hall (finSumFinEquiv k).1 (finSumFinEquiv k).2 with (h0 | h1) | h2
    · exact absurd h0 hkne
    · exact .inl (mem_finsetOfList.2 h1)
    · exact .inr (mem_finsetOfList.2 h2)
  have hfb₁ := (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c)
    (allRhsP_spec c) (decodeT₁_sorted c u) hlt₁ hlen₁).1 hf1
  have hfb₂ := (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c)
    (allRhsQ_spec c) (decodeT₂_sorted c u) hlt₂ hlen₂).1 hf2
  exact ⟨hlen_u, hlen₁, hlen₂, hacl, hcard₁, hcard₂, hfb₁, hfb₂⟩

private lemma node_of_isValidNodeExec {c : BimatrixCode} (hc : c.WellFormed) {u : List Bool}
    (hu : isValidNodeExec c u = true) :
    ∃ (h1 : (finsetOfList c.rows c.cols (decodeT₁ c u)).card = c.rows)
      (h2 : (finsetOfList c.rows c.cols (decodeT₂ c u)).card = c.cols)
      (p : LemkeHowson.Node
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        (.inl ⟨0, hc.1⟩)),
      tightRows
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x =
        finsetOfList c.rows c.cols (decodeT₁ c u) ∧
      tightRows
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y =
        finsetOfList c.rows c.cols (decodeT₂ c u) ∧
      p.x = ratBasisSol (intMatP (posMatB c))
        (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (finsetOfList c.rows c.cols (decodeT₁ c u)) h1 ∧
      p.y = ratBasisSol (intMatQ (posMatA c))
        (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (finsetOfList c.rows c.cols (decodeT₂ c u)) h2 := by
  obtain ⟨_, _, _, hacl, hcard₁, hcard₂, hfb₁, hfb₂⟩ := validNode_props hc hu
  set x := ratBasisSol (intMatP (posMatB c))
    (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
    (finsetOfList c.rows c.cols (decodeT₁ c u)) hcard₁
  set y := ratBasisSol (intMatQ (posMatA c))
    (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
    (finsetOfList c.rows c.cols (decodeT₂ c u)) hcard₂
  have htx : tightRows
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) x =
      finsetOfList c.rows c.cols (decodeT₁ c u) :=
    tightRows_ratBasisSol_eq hfb₁ (pertP_nondegenerate hc)
  have hty : tightRows
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) y =
      finsetOfList c.rows c.cols (decodeT₂ c u) :=
    tightRows_ratBasisSol_eq hfb₂ (pertQ_nondegenerate hc)
  exact ⟨hcard₁, hcard₂,
    ⟨x, y, (isVertex_ratBasisSol_of_isFeasibleBasis hfb₁ (K := ℚ)).1,
      (isVertex_ratBasisSol_of_isFeasibleBasis hfb₂ (K := ℚ)).1,
      fun k hk => by rw [htx, hty]; exact hacl k hk⟩,
    htx, hty, rfl, rfl⟩

private lemma halfEdgeIndex_congr {m n : ℕ}
    (A₁ : Matrix (Fin m ⊕ Fin n) (Fin m) ℚ)
    (A₂ : Matrix (Fin m ⊕ Fin n) (Fin n) ℚ)
    {T₁ T₁' T₂ T₂' : Finset (Fin m ⊕ Fin n)}
    (hT₁ : T₁.card = m) (hT₁' : T₁'.card = m)
    (hT₂ : T₂.card = n) (hT₂' : T₂'.card = n)
    (h1 : T₁ = T₁') (h2 : T₂ = T₂') (k₀ : Fin m ⊕ Fin n) (side : Bool) :
    LemkeHowson.halfEdgeIndex A₁ A₂ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      T₁ T₂ hT₁ hT₂ k₀ side =
    LemkeHowson.halfEdgeIndex A₁ A₂ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      T₁' T₂' hT₁' hT₂' k₀ side := by
  subst h1 h2
  rfl

private lemma halfEdgeIndexExec_eq_of_node {c : BimatrixCode} (hc : c.WellFormed)
    {T₁ T₂ : List ℕ} (hs₁ : T₁.Pairwise (· < ·)) (hs₂ : T₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < c.rows + c.cols) (hlt₂ : ∀ r ∈ T₂, r < c.rows + c.cols)
    (hlen₁ : T₁.length = c.rows) (hlen₂ : T₂.length = c.cols)
    (p : LemkeHowson.Node
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
      (.inl ⟨0, hc.1⟩))
    (htx : tightRows
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x =
      finsetOfList c.rows c.cols T₁)
    (hty : tightRows
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y =
      finsetOfList c.rows c.cols T₂)
    (hT₁p : (tightRows
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x).card = c.rows)
    (hT₂p : (tightRows
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y).card = c.cols)
    (side : Bool) (hact : if side then 0 ∉ T₁ else 0 ∉ T₂) :
    halfEdgeIndexExec c T₁ T₂ side =
      LemkeHowson.halfEdgeIndex
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
        (tightRows _ _ p.x) (tightRows _ _ p.y) hT₁p hT₂p (.inl ⟨0, hc.1⟩) side := by
  have hacl : ∀ k : Fin c.rows ⊕ Fin c.cols,
      k ≠ .inl ⟨0, hc.1⟩ → k ∈ finsetOfList c.rows c.cols T₁ ∨ k ∈ finsetOfList c.rows c.cols T₂ :=
    fun k hk => by simpa only [htx, hty] using p.almostCompletelyLabeled k hk
  have hact' : if side then .inl ⟨0, hc.1⟩ ∉ finsetOfList c.rows c.cols T₁
      else .inl ⟨0, hc.1⟩ ∉ finsetOfList c.rows c.cols T₂ := by
    cases side <;> exact fun h => hact (mem_finsetOfList.1 h)
  rw [halfEdgeIndexExec_eq c hc.1 hs₁ hs₂ hlt₁ hlt₂ hlen₁ hlen₂ side hacl hact']
  exact halfEdgeIndex_congr _ _ _ _ _ _ htx.symm hty.symm _ side

private lemma halfEdgeIndexExec_true_eq_neg_false_of_node {c : BimatrixCode} (hc : c.WellFormed)
    {T₁ T₂ : List ℕ} (hs₁ : T₁.Pairwise (· < ·)) (hs₂ : T₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < c.rows + c.cols) (hlt₂ : ∀ r ∈ T₂, r < c.rows + c.cols)
    (hlen₁ : T₁.length = c.rows) (hlen₂ : T₂.length = c.cols)
    (p : LemkeHowson.Node
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
      (.inl ⟨0, hc.1⟩))
    (htx : tightRows
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x =
      finsetOfList c.rows c.cols T₁)
    (hty : tightRows
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y =
      finsetOfList c.rows c.cols T₂)
    (h01 : 0 ∉ T₁) (h02 : 0 ∉ T₂) :
    halfEdgeIndexExec c T₁ T₂ true = -halfEdgeIndexExec c T₁ T₂ false := by
  have hT₁p : (tightRows _ _ p.x).card = c.rows :=
    htx ▸ (card_finsetOfList hs₁.nodup hlt₁).trans hlen₁
  have hT₂p : (tightRows _ _ p.y).card = c.cols :=
    hty ▸ (card_finsetOfList hs₂.nodup hlt₂).trans hlen₂
  rw [halfEdgeIndexExec_eq_of_node hc hs₁ hs₂ hlt₁ hlt₂ hlen₁ hlen₂ p htx hty hT₁p hT₂p true h01,
    halfEdgeIndexExec_eq_of_node hc hs₁ hs₂ hlt₁ hlt₂ hlen₁ hlen₂ p htx hty hT₁p hT₂p false h02]
  exact LemkeHowson.halfEdgeIndex_true_eq_neg_false (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Fintype.card_sum.trans (by simp)) p (hT₁ := hT₁p) (hT₂ := hT₂p) fun hcl => by
      rcases (LemkeHowson.completelyLabeled_iff.1 hcl) (.inl ⟨0, hc.1⟩) with h1 | h2
      · exact h01 (mem_finsetOfList.1 (htx ▸ h1))
      · exact h02 (mem_finsetOfList.1 (hty ▸ h2))

private lemma abs_halfEdgeIndexExec_eq_one_of_node {c : BimatrixCode} (hc : c.WellFormed)
    {T₁ T₂ : List ℕ} (hs₁ : T₁.Pairwise (· < ·)) (hs₂ : T₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ T₁, r < c.rows + c.cols) (hlt₂ : ∀ r ∈ T₂, r < c.rows + c.cols)
    (hlen₁ : T₁.length = c.rows) (hlen₂ : T₂.length = c.cols)
    (p : LemkeHowson.Node
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
      (.inl ⟨0, hc.1⟩))
    (htx : tightRows
      ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
      (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.x =
      finsetOfList c.rows c.cols T₁)
    (hty : tightRows
      ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
      (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) p.y =
      finsetOfList c.rows c.cols T₂)
    (side : Bool) (hact : if side then 0 ∉ T₁ else 0 ∉ T₂) :
    |halfEdgeIndexExec c T₁ T₂ side| = 1 := by
  have hT₁p : (tightRows _ _ p.x).card = c.rows :=
    htx ▸ (card_finsetOfList hs₁.nodup hlt₁).trans hlen₁
  have hT₂p : (tightRows _ _ p.y).card = c.cols :=
    hty ▸ (card_finsetOfList hs₂.nodup hlt₂).trans hlen₂
  rw [halfEdgeIndexExec_eq_of_node hc hs₁ hs₂ hlt₁ hlt₂ hlen₁ hlen₂ p htx hty hT₁p hT₂p side hact]
  have hne0 := LemkeHowson.halfEdgeIndex_ne_zero (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Fintype.card_sum.trans (by simp)) p (hT₁ := hT₁p) (hT₂ := hT₂p) (side := side) (by
      cases side
      · exact fun h => hact (mem_finsetOfList.1 (hty ▸ h))
      · exact fun h => hact (mem_finsetOfList.1 (htx ▸ h)))
  have hs1 : ∀ u : ℤˣ, |(u : ℤ)| ≤ 1 := fun u => by
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  have hs2 : ∀ x : ℚ, |LemkeHowson.signOfK x| ≤ 1 := fun x => by
    simp only [LemkeHowson.signOfK]; cases SignType.sign x <;> norm_num
  have hle1 : |LemkeHowson.halfEdgeIndex
      ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ)
      ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ)
      (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      (tightRows _ _ p.x) (tightRows _ _ p.y) hT₁p hT₂p (.inl ⟨0, hc.1⟩) side| ≤ 1 := by
    simp only [LemkeHowson.halfEdgeIndex]
    split_ifs
    · rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hs1 _) (hs2 _) (abs_nonneg _) (by norm_num))
        (hs2 _) (abs_nonneg _) (by norm_num)
    · norm_num
  have hpos := abs_pos.2 hne0
  omega

private lemma decodeT₁_encodeNodes_eq {c : BimatrixCode} {v : List Bool} {L₁ L₂ : List ℕ}
    (hv : v = encodeNodes c L₁ L₂) (hsort : L₁.Pairwise (· < ·))
    (hlt : ∀ k ∈ L₁, k < c.rows + c.cols) : decodeT₁ c v = L₁ :=
  (decodeT₁_sorted c v).eq_of_mem_iff hsort fun k =>
    ⟨fun hk => (decodeT₁_encodeNodes L₁ L₂ (decodeT₁_lt c v hk)).1 (hv ▸ hk),
     fun hk => hv ▸ (decodeT₁_encodeNodes L₁ L₂ (hlt k hk)).2 hk⟩

private lemma decodeT₂_encodeNodes_eq {c : BimatrixCode} {v : List Bool} {L₁ L₂ : List ℕ}
    (hv : v = encodeNodes c L₁ L₂) (hsort : L₂.Pairwise (· < ·))
    (hlt : ∀ k ∈ L₂, k < c.rows + c.cols) : decodeT₂ c v = L₂ :=
  (decodeT₂_sorted c v).eq_of_mem_iff hsort fun k =>
    ⟨fun hk => (decodeT₂_encodeNodes L₁ L₂ (decodeT₂_lt c v hk)).1 (hv ▸ hk),
     fun hk => hv ▸ (decodeT₂_encodeNodes L₁ L₂ (hlt k hk)).2 hk⟩

private lemma almostComplete_all_range_eq_true (m n : ℕ) (L₁ L₂ : List ℕ)
    {k₀ : Fin m ⊕ Fin n} (hk₀ : (finSumFinEquiv k₀).1 = 0)
    (hacl : ∀ k : Fin m ⊕ Fin n, k ≠ k₀ → k ∈ finsetOfList m n L₁ ∨ k ∈ finsetOfList m n L₂) :
    ((List.range (m + n)).all fun k =>
      decide (k = 0) || decide (k ∈ L₁) || decide (k ∈ L₂)) = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hk0 : k = 0
  · exact .inl (.inl hk0)
  · have hk' : finSumFinEquiv.symm ⟨k, hk⟩ ≠ k₀ := fun h => by
      apply hk0
      have h1 := congrArg (fun z => (finSumFinEquiv z).1) h
      simp only [Equiv.apply_symm_apply] at h1
      exact h1.trans hk₀
    rcases hacl _ hk' with h1 | h2
    · exact .inl (.inr (by simpa [Equiv.apply_symm_apply] using mem_finsetOfList.1 h1))
    · exact .inr (by simpa [Equiv.apply_symm_apply] using mem_finsetOfList.1 h2)

private lemma pivotBasisRows_acl_roundTrip {m n k k_fix : ℕ} (hm : 0 < m)
    (hk_sum : k + k_fix = m + n)
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (rhsAll : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), rhsAll.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
      (fun r => (b_int r : ℚ)))
    (hrec : ∀ v : Fin k → ℚ,
      (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ) *ᵥ v ≤ 0 → v = 0)
    {T T_fix : List ℕ}
    (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n) (hlen : T.length = k)
    (hcard : (finsetOfList m n T).card = k)
    (hcard_fix : (finsetOfList m n T_fix).card = k_fix)
    (hfb : IsFeasibleBasis M_int b_int (finsetOfList m n T) hcard)
    (hacl : ∀ r : Fin m ⊕ Fin n, r ≠ .inl ⟨0, hm⟩ →
      r ∈ finsetOfList m n T ∨ r ∈ finsetOfList m n T_fix)
    (hk₀_not_fix : (.inl ⟨0, hm⟩ : Fin m ⊕ Fin n) ∉ finsetOfList m n T_fix)
    {x : Fin k → ℚ}
    (hx_v : IsVertex (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
      (fun r => (b_int r : ℚ)) x)
    (htx : tightRows (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
      (fun r => (b_int r : ℚ)) x = finsetOfList m n T)
    (hx_eq : x = ratBasisSol M_int b_int (finsetOfList m n T) hcard)
    {l_exec : ℕ}
    (hl_exec : (finSumFinEquiv (LemkeHowson.leaveLabel (finsetOfList m n T)
      (finsetOfList m n T_fix) (.inl ⟨0, hm⟩))).1 = l_exec)
    {l_back : List ℕ → ℕ}
    (hl_back : ∀ T', T'.Pairwise (· < ·) → (∀ r ∈ T', r < m + n) →
      (finSumFinEquiv (LemkeHowson.leaveLabel (finsetOfList m n T')
        (finsetOfList m n T_fix) (.inl ⟨0, hm⟩))).1 = l_back T') :
    let T' := pivotBasisRows k (m + n) allRows rhsAll T l_exec
    let q := pivotVertex (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
      (fun r => (b_int r : ℚ)) x
      (LemkeHowson.leaveLabel (finsetOfList m n T) (finsetOfList m n T_fix) (.inl ⟨0, hm⟩))
    T'.Pairwise (· < ·) ∧ (∀ r ∈ T', r < m + n) ∧ T'.length = k ∧
      isFeasibleBasisRows k (m + n) allRows rhsAll T' = true ∧
      T' ≠ T ∧
      (∀ r : Fin m ⊕ Fin n, r ≠ .inl ⟨0, hm⟩ →
        r ∈ finsetOfList m n T' ∨ r ∈ finsetOfList m n T_fix) ∧
      IsVertex (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
        (fun r => (b_int r : ℚ)) q ∧
      q ≠ x ∧
      VertexAdj (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
        (fun r => (b_int r : ℚ)) x q ∧
      tightRows (M_int.map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin k) ℚ)
        (fun r => (b_int r : ℚ)) q = finsetOfList m n T' ∧
      pivotBasisRows k (m + n) allRows rhsAll T' (l_back T') = T := by
  intro T' q
  set Ts := finsetOfList m n T
  set Tfs := finsetOfList m n T_fix
  set k₀ : Fin m ⊕ Fin n := .inl ⟨0, hm⟩
  set l' := LemkeHowson.leaveLabel Ts Tfs k₀
  have hsum_card : Fintype.card (Fin m ⊕ Fin n) = k + k_fix := by simp [hk_sum]
  have hl'_in_Ts : l' ∈ Ts := by
    by_cases hk₀_in : k₀ ∈ Ts
    · simp only [l', LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inl hk₀_in))]
      exact hk₀_in
    · exact (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard hcard_fix
        hacl (Finset.notMem_union.2 ⟨hk₀_in, hk₀_not_fix⟩)).1).1
  have hpiv := pivotBasisRows_spec M_int b_int allRows rhsAll hall hrhs hnd hrec
    hsort hlt hlen hcard hfb hl'_in_Ts
  dsimp only [Ts, l'] at hpiv
  rw [hl_exec, ← hx_eq] at hpiv
  obtain ⟨hT'_sort, hT'_lt, hT'_len, hcard', hfb', hT'_tight⟩ := hpiv
  have hl'_in_x : l' ∈ tightRows (M_int.map Int.cast : Matrix _ _ ℚ) (fun r => (b_int r : ℚ)) x :=
    htx ▸ hl'_in_Ts
  obtain ⟨hq_v, hq_ne, hq_sub⟩ := hx_v.pivotVertex_spec hnd hrec hl'_in_x
  have hT'_not_l' : l' ∉ finsetOfList m n T' :=
    hT'_tight ▸ hx_v.notMem_tightRows_pivotVertex hnd hrec hl'_in_x
  have hacl_q : ∀ r : Fin m ⊕ Fin n, r ≠ k₀ → r ∈ finsetOfList m n T' ∨ r ∈ Tfs := by
    intro r hr
    by_cases hrl : r = l'
    · subst hrl
      have hk₀_not_T : k₀ ∉ Ts := fun h => hr (by
        simp only [l', LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inl h))])
      exact .inr (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard
        hcard_fix hacl (Finset.notMem_union.2 ⟨hk₀_not_T, hk₀_not_fix⟩)).1).2
    · rcases hacl r hr with h1 | h2
      · exact .inl (hT'_tight ▸ hq_sub (Finset.mem_erase.2 ⟨hrl, htx ▸ h1⟩))
      · exact .inr h2
  have hadj : VertexAdj (M_int.map Int.cast : Matrix _ _ ℚ) (fun r => (b_int r : ℚ)) x q :=
    (vertexAdj_iff_exists_pivotVertex hnd hrec hx_v).2 ⟨l', hl'_in_x, rfl⟩
  have hf' : isFeasibleBasisRows k (m + n) allRows rhsAll T' = true :=
    (isFeasibleBasisRows_iff _ _ allRows rhsAll hall hrhs hT'_sort hT'_lt hT'_len).2 hfb'
  have hT'_ne : T' ≠ T := fun heq => hT'_not_l' (congrArg (finsetOfList m n) heq ▸ hl'_in_Ts)
  let m'_fin := LemkeHowson.leaveLabel (finsetOfList m n T') Tfs k₀
  have hm'_eq_leave := hl_back T' hT'_sort hT'_lt
  have hm'_in_T' : m'_fin ∈ finsetOfList m n T' := by
    by_cases hk₀_q : k₀ ∈ finsetOfList m n T'
    · simp only [m'_fin, LemkeHowson.leaveLabel, ite_eq_left (Finset.mem_union.2 (.inl hk₀_q))]
      exact hk₀_q
    · exact (Finset.mem_inter.1 (LemkeHowson.mem_inter_of_acl_not_mem hsum_card hcard' hcard_fix
        hacl_q (Finset.notMem_union.2 ⟨hk₀_q, hk₀_not_fix⟩)).1).1
  have hqm'_eq_x : pivotVertex (M_int.map Int.cast : Matrix _ _ ℚ) (fun r => (b_int r : ℚ))
      q m'_fin = x := by
    symm
    refine hq_v.eq_pivotVertex hnd hrec (hT'_tight ▸ hm'_in_T') hx_v hq_ne.symm ?_
    rw [← hT'_tight, htx]
    intro z hz
    rw [Finset.mem_erase] at hz
    have hnot_fix : z ∉ Tfs := by
      by_cases hzk₀ : z = k₀
      · exact hzk₀ ▸ hk₀_not_fix
      · intro hzf
        by_cases hk₀_q : k₀ ∈ finsetOfList m n T'
        · have he := LemkeHowson.inter_eq_empty_of_mem_union hsum_card hcard' hcard_fix
            hacl_q (Finset.mem_union.2 (.inl hk₀_q))
          have hmem : z ∈ finsetOfList m n T' ∩ Tfs := Finset.mem_inter.2 ⟨hz.2, hzf⟩
          rw [he] at hmem
          exact Finset.notMem_empty z hmem
        · exact hz.1 (Finset.mem_singleton.1 ((LemkeHowson.mem_inter_of_acl_not_mem hsum_card
            hcard' hcard_fix hacl_q (Finset.notMem_union.2 ⟨hk₀_q, hk₀_not_fix⟩)).2 ▸
            Finset.mem_inter.2 ⟨hz.2, hzf⟩))
    have hzk₀ : z ≠ k₀ := fun hzk => by
      have hk₀_q : k₀ ∈ finsetOfList m n T' ∪ Tfs := Finset.mem_union.2 (.inl (hzk ▸ hz.2))
      have hm_eq : m'_fin = k₀ := by
        dsimp only [m'_fin]; rw [LemkeHowson.leaveLabel, ite_eq_left hk₀_q]
      exact hz.1 (hzk.trans hm_eq.symm)
    exact (hacl z hzk₀).resolve_right hnot_fix
  have hpiv_back := pivotBasisRows_spec M_int b_int allRows rhsAll hall hrhs hnd hrec
    hT'_sort hT'_lt hT'_len hcard' hfb' hm'_in_T'
  have hrat_q : ratBasisSol M_int b_int (finsetOfList m n T') hcard' = q := by
    apply (isVertex_ratBasisSol_of_isFeasibleBasis hfb' (K := ℚ)).1.eq_of_tightRows_eq
    rw [tightRows_ratBasisSol_eq hfb' hnd, ← hT'_tight]
  dsimp only at hpiv_back
  rw [hrat_q, hqm'_eq_x, hm'_eq_leave, htx] at hpiv_back
  obtain ⟨hTb_sort, hTb_lt, _, _, _, hTb_fin⟩ := hpiv_back
  exact ⟨hT'_sort, hT'_lt, hT'_len, hf', hT'_ne, hacl_q, hq_v, hq_ne, hadj, hT'_tight.symm,
    eq_of_finsetOfList_eq hTb_sort hsort hTb_lt hlt hTb_fin⟩

private lemma encodeNodes_valid_decode {c : BimatrixCode} (hc : c.WellFormed)
    {v : List Bool} {L₁ L₂ : List ℕ} (hv : v = encodeNodes c L₁ L₂)
    (hs₁ : L₁.Pairwise (· < ·)) (hs₂ : L₂.Pairwise (· < ·))
    (hlt₁ : ∀ r ∈ L₁, r < c.rows + c.cols) (hlt₂ : ∀ r ∈ L₂, r < c.rows + c.cols)
    (hlen₁ : L₁.length = c.rows) (hlen₂ : L₂.length = c.cols)
    (hf₁ : isFeasibleBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) L₁ = true)
    (hf₂ : isFeasibleBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) L₂ = true)
    (hacl : ∀ k : Fin c.rows ⊕ Fin c.cols, k ≠ .inl ⟨0, hc.1⟩ →
      k ∈ finsetOfList c.rows c.cols L₁ ∨ k ∈ finsetOfList c.rows c.cols L₂) :
    decodeT₁ c v = L₁ ∧ decodeT₂ c v = L₂ ∧ isValidNodeExec c v = true := by
  have hd₁ := decodeT₁_encodeNodes_eq hv hs₁ hlt₁
  have hd₂ := decodeT₂_encodeNodes_eq hv hs₂ hlt₂
  have hwb := (wellFormed_iff_wellFormedB c).1 hc
  have hlen_v : v.length = 2 * (c.rows + c.cols) := by rw [hv, length_encodeNodes]
  have hall := almostComplete_all_range_eq_true c.rows c.cols L₁ L₂ rfl hacl
  refine ⟨hd₁, hd₂, ?_⟩
  simp only [isValidNodeExec, hwb, hlen_v, hd₁, hd₂, hlen₁, hlen₂, hall, hf₁, hf₂,
    decide_true, Bool.and_self]

private lemma stepGraph_roundTrip {c : BimatrixCode} (hc : c.WellFormed) (wantNeg : Bool)
    {u : List Bool} (hu : isValidNodeExec c u = true)
    (hact :
      (!decide (0 ∈ decodeT₂ c u) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false =
          if wantNeg then -targetSign c else targetSign c)) = true ∨
      (!decide (0 ∈ decodeT₁ c u) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) true =
          if wantNeg then -targetSign c else targetSign c)) = true) :
    let v := stepGraph wantNeg c u
    isValidNodeExec c v = true ∧ v ≠ u ∧ stepGraph (!wantNeg) c v = u := by
  intro v
  have hsum_card : Fintype.card (Fin c.rows ⊕ Fin c.cols) = c.rows + c.cols := by simp
  obtain ⟨hcard₁, hcard₂, p, htx, hty, hpx_eq, hpy_eq⟩ := node_of_isValidNodeExec hc hu
  obtain ⟨hlen_u, hlen₁, hlen₂, hacl, _, _, hfb₁, hfb₂⟩ := validNode_props hc hu
  let T₁ := decodeT₁ c u
  let T₂ := decodeT₂ c u
  let k₀ : Fin c.rows ⊕ Fin c.cols := Sum.inl ⟨0, hc.1⟩
  let wanted := if wantNeg then -targetSign c else targetSign c
  let wanted' := if !wantNeg then -targetSign c else targetSign c
  have hw_opp : wanted' = -wanted := by cases wantNeg <;> simp [wanted, wanted']
  have hvalid_b : (!isValidNodeExec c u) = false := by simp [hu]
  by_cases hL : (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁ T₂ false = wanted)) = true
  · have hv_eq : v = encodeNodes c
        (pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁
          (leaveLabelExec T₁ T₂)) T₂ := by
      simp only [v, stepGraph, hvalid_b, Bool.false_eq_true, ↓reduceIte, T₁, T₂]
      rw [ite_eq_left hL]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hL
    obtain ⟨h0_not_T₂, hidxL⟩ := hL
    obtain ⟨hT₁'_sort, hT₁'_lt, hT₁'_len, hf1', hT₁'_ne, hacl_q, hqx_v, hqx_ne, hadj_x,
      hT₁'_tight, hT₁b_eq⟩ :=
      pivotBasisRows_acl_roundTrip hc.1 rfl (intMatP (posMatB c))
        (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
        (pertP_nondegenerate hc) (pertP_recession hc)
        (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlen₁ hcard₁ hcard₂ hfb₁ hacl
        (fun h => h0_not_T₂ (mem_finsetOfList.1 h)) p.isVertex_x htx hpx_eq
        (leaveLabelExec_eq hc.1 (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr)
          (fun _ hr => decodeT₂_lt c u hr))
        (fun T' hs' hlt' => leaveLabelExec_eq hc.1 hs' hlt' (fun _ hr => decodeT₂_lt c u hr))
    let T₁' := pivotBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁
      (leaveLabelExec T₁ T₂)
    let q_node : LemkeHowson.Node
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) k₀ :=
      ⟨_, p.y, hqx_v, p.isVertex_y, fun k hk => by rw [hT₁'_tight, hty]; exact hacl_q k hk⟩
    have hf2' : isFeasibleBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂ = true :=
      (isFeasibleBasisRows_iff _ _ (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
        (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr) hlen₂).2 hfb₂
    obtain ⟨hv_dec1, hv_dec2, hv_valid⟩ := encodeNodes_valid_decode hc hv_eq hT₁'_sort
      (decodeT₂_sorted c u) hT₁'_lt (fun _ hr => decodeT₂_lt c u hr) hT₁'_len hlen₂ hf1' hf2'
      hacl_q
    have hv_ne : v ≠ u := fun heq => hT₁'_ne (hv_dec1.symm.trans (congrArg (decodeT₁ c) heq))
    have hidxL_v : halfEdgeIndexExec c T₁' T₂ false = wanted' := by
      have hcard₁' := (card_finsetOfList hT₁'_sort.nodup hT₁'_lt).trans hT₁'_len
      rw [halfEdgeIndexExec_eq_of_node hc hT₁'_sort (decodeT₂_sorted c u) hT₁'_lt
          (fun _ hr => decodeT₂_lt c u hr) hT₁'_len hlen₂ q_node hT₁'_tight hty
          (hT₁'_tight ▸ hcard₁') (hty ▸ hcard₂) false h0_not_T₂,
        LemkeHowson.halfEdgeIndex_pivot_left_eq_neg (pertP_nondegenerate hc)
          (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hsum_card
          (p := p) (q := q_node) (hT₁p := htx ▸ hcard₁) (hT₁q := hT₁'_tight ▸ hcard₁')
          (hT₂p := hty ▸ hcard₂) (hT₂q := hty ▸ hcard₂)
          rfl hqx_ne.symm (LemkeHowson.graph_adj.2 (.inr ⟨rfl, hadj_x⟩)),
        ← halfEdgeIndexExec_eq_of_node hc (decodeT₁_sorted c u) (decodeT₂_sorted c u)
          (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr) hlen₁ hlen₂ p htx hty
          (htx ▸ hcard₁) (hty ▸ hcard₂) false h0_not_T₂,
        hidxL, hw_opp]
    have hL_v :
        (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁' T₂ false = wanted')) = true := by
      simp [h0_not_T₂, hidxL_v]
    refine ⟨hv_valid, hv_ne, ?_⟩
    simp only [stepGraph, hv_valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv_dec1, hv_dec2]
    change (if (!decide (0 ∈ T₂) && decide (halfEdgeIndexExec c T₁' T₂ false = wanted')) = true
        then _ else _) = _
    rw [ite_eq_left hL_v, hT₁b_eq]
    exact encodeNodes_decode hlen_u
  · have hR : (!decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂ true = wanted)) = true :=
      hact.resolve_left hL
    have hv_eq : v = encodeNodes c T₁
        (pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂
          (leaveLabelExec T₁ T₂)) := by
      simp only [v, stepGraph, hvalid_b, Bool.false_eq_true, ↓reduceIte, T₁, T₂]
      rw [ite_eq_right hL, ite_eq_left hR]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hR
    obtain ⟨h0_not_T₁, hidxR⟩ := hR
    have hl2_exec : (finSumFinEquiv (LemkeHowson.leaveLabel (finsetOfList c.rows c.cols T₂)
        (finsetOfList c.rows c.cols T₁) k₀)).1 = leaveLabelExec T₁ T₂ := by
      rw [leaveLabel_comm]
      exact leaveLabelExec_eq hc.1 (decodeT₁_sorted c u)
        (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
    have hl2_back : ∀ T', T'.Pairwise (· < ·) → (∀ r ∈ T', r < c.rows + c.cols) →
        (finSumFinEquiv (LemkeHowson.leaveLabel (finsetOfList c.rows c.cols T')
          (finsetOfList c.rows c.cols T₁) k₀)).1 = leaveLabelExec T₁ T' := by
      intro T' _ hlt'
      rw [leaveLabel_comm]
      exact leaveLabelExec_eq hc.1 (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlt'
    obtain ⟨hT₂'_sort, hT₂'_lt, hT₂'_len, hf2', hT₂'_ne, hacl_q_symm, hqy_v, hqy_ne, hadj_y,
      hT₂'_tight_raw, hT₂b_eq⟩ :=
      pivotBasisRows_acl_roundTrip hc.1 (Nat.add_comm _ _) (intMatQ (posMatA c))
        (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c))
        (allRowsQ c) (allRhsQ c) (allRowsQ_spec c) (allRhsQ_spec c)
        (pertQ_nondegenerate hc) (pertQ_recession hc)
        (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr) hlen₂ hcard₂ hcard₁ hfb₂
        (fun r hr => (hacl r hr).symm)
        (fun h => h0_not_T₁ (mem_finsetOfList.1 h)) p.isVertex_y hty hpy_eq hl2_exec hl2_back
    let T₂' := pivotBasisRows c.cols (c.rows + c.cols) (allRowsQ c) (allRhsQ c) T₂
      (leaveLabelExec T₁ T₂)
    have hacl_q : ∀ r : Fin c.rows ⊕ Fin c.cols,
        r ≠ k₀ → r ∈ finsetOfList c.rows c.cols T₁ ∨ r ∈ finsetOfList c.rows c.cols T₂' :=
      fun r hr => (hacl_q_symm r hr).symm
    let q_node : LemkeHowson.Node
        ((intMatP (posMatB c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.rows) ℚ)
        (fun r => (pertRhsPInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ))
        ((intMatQ (posMatA c)).map Int.cast : Matrix (Fin c.rows ⊕ Fin c.cols) (Fin c.cols) ℚ)
        (fun r => (pertRhsQInt c.rows c.cols ((2 : ℤ) ^ bitBoundVal c) r : ℚ)) k₀ :=
      ⟨p.x, _, p.isVertex_x, hqy_v, fun k hk => by rw [htx, hT₂'_tight_raw]; exact hacl_q k hk⟩
    have hf1' : isFeasibleBasisRows c.rows (c.rows + c.cols) (allRowsP c) (allRhsP c) T₁ = true :=
      (isFeasibleBasisRows_iff _ _ (allRowsP c) (allRhsP c) (allRowsP_spec c) (allRhsP_spec c)
        (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlen₁).2 hfb₁
    obtain ⟨hv_dec1, hv_dec2, hv_valid⟩ := encodeNodes_valid_decode hc hv_eq
      (decodeT₁_sorted c u) hT₂'_sort (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len
      hf1' hf2' hacl_q
    have hv_ne : v ≠ u := fun heq => hT₂'_ne (hv_dec2.symm.trans (congrArg (decodeT₂ c) heq))
    have hidxR_v : halfEdgeIndexExec c T₁ T₂' true = wanted' := by
      have hcard₂' := (card_finsetOfList hT₂'_sort.nodup hT₂'_lt).trans hT₂'_len
      rw [halfEdgeIndexExec_eq_of_node hc (decodeT₁_sorted c u) hT₂'_sort
          (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len q_node htx hT₂'_tight_raw
          (htx ▸ hcard₁) (hT₂'_tight_raw ▸ hcard₂') true h0_not_T₁,
        LemkeHowson.halfEdgeIndex_pivot_right_eq_neg (pertQ_nondegenerate hc)
          (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) hsum_card
          (p := p) (q := q_node) (hT₁p := htx ▸ hcard₁) (hT₁q := htx ▸ hcard₁)
          (hT₂p := hty ▸ hcard₂) (hT₂q := hT₂'_tight_raw ▸ hcard₂')
          rfl hqy_ne.symm (LemkeHowson.graph_adj.2 (.inl ⟨rfl, hadj_y⟩)),
        ← halfEdgeIndexExec_eq_of_node hc (decodeT₁_sorted c u) (decodeT₂_sorted c u)
          (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr) hlen₁ hlen₂ p htx hty
          (htx ▸ hcard₁) (hty ▸ hcard₂) true h0_not_T₁,
        hidxR, hw_opp]
    have hL_v_false :
        (!decide (0 ∈ T₂') && decide (halfEdgeIndexExec c T₁ T₂' false = wanted')) = false := by
      by_cases h02' : 0 ∈ T₂'
      · simp [h02']
      · simp only [Bool.and_eq_false_imp, Bool.not_eq_true', decide_eq_false_iff_not]
        intro _ heq_f
        have hopp := halfEdgeIndexExec_true_eq_neg_false_of_node hc (decodeT₁_sorted c u)
          hT₂'_sort (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len q_node htx
          hT₂'_tight_raw h0_not_T₁ h02'
        have habs := abs_halfEdgeIndexExec_eq_one_of_node hc (decodeT₁_sorted c u)
          hT₂'_sort (fun _ hr => decodeT₁_lt c u hr) hT₂'_lt hlen₁ hT₂'_len q_node htx
          hT₂'_tight_raw false h02'
        rw [hidxR_v, heq_f] at hopp
        have hw0 : wanted' = 0 := by omega
        rw [heq_f, hw0] at habs
        norm_num at habs
    have hR_v :
        (!decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂' true = wanted')) = true := by
      simp [h0_not_T₁, hidxR_v]
    refine ⟨hv_valid, hv_ne, ?_⟩
    simp only [stepGraph, hv_valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv_dec1, hv_dec2]
    change (if (!decide (0 ∈ T₂') && decide (halfEdgeIndexExec c T₁ T₂' false = wanted')) = true
        then _ else
        if (!decide (0 ∈ T₁) && decide (halfEdgeIndexExec c T₁ T₂' true = wanted')) = true
        then _ else _) = _
    rw [ite_eq_right (Bool.eq_false_iff.1 hL_v_false), ite_eq_left hR_v, hT₂b_eq]
    exact encodeNodes_decode hlen_u

private lemma finsetOfList_range_rows (m n : ℕ) :
    finsetOfList m n (List.range m) = Finset.univ.image Sum.inl := by
  ext r
  simp only [mem_finsetOfList, List.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  cases r with
  | inl i => exact ⟨fun _ => ⟨i, rfl⟩, fun _ => i.2⟩
  | inr j =>
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => absurd hi (by simp)⟩
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at h
    omega

private lemma finsetOfList_map_add_rows (m n : ℕ) :
    finsetOfList m n ((List.range n).map (· + m)) = Finset.univ.image Sum.inr := by
  ext r
  simp only [mem_finsetOfList, List.mem_map, List.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  cases r with
  | inl i =>
    refine ⟨?_, fun ⟨j, hj⟩ => absurd hj (by simp)⟩
    rintro ⟨j, _, hj⟩
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hj
    omega
  | inr j => exact ⟨fun _ => ⟨j, rfl⟩, fun _ => ⟨j.1, j.2, by simp [Nat.add_comm]⟩⟩

private lemma endOfLineRel_wellFormed_props {c : BimatrixCode} (hc : c.WellFormed) {u : List Bool}
    (hu : endOfLineRel vertexLen pred succ c u) :
    isValidNodeExec c u = true ∧ u ≠ zeroVertex (vertexLen c) ∧
      (0 ∈ decodeT₁ c u ∨ 0 ∈ decodeT₂ c u) := by
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  have hvlen : vertexLen c = 2 * (c.rows + c.cols) := by simp [vertexLen, hwb]
  have hvalid_zero := isValidNodeExec_zeroVertex hc
  have hu_valid : isValidNodeExec c u = true := by
    by_contra hnot
    have hnot' : (!isValidNodeExec c u) = true := by cases h : isValidNodeExec c u <;> simp_all
    have hp : pred (c, u) = u := by
      dsimp only [pred, stepGraph]
      rw [ite_eq_left hnot']
    have hs : succ (c, u) = u := by
      dsimp only [succ, stepGraph]
      rw [ite_eq_left hnot']
    have hin : hasIn vertexLen pred succ c u = false := by simp [hasIn, hp]
    have hout : hasOut vertexLen pred succ c u = false := by simp [hasOut, hs]
    have hne : u ≠ zeroVertex (vertexLen c) := fun h => hnot (h ▸ hvalid_zero)
    rcases hu with ⟨-, hrel⟩
    simp [hin, hout, hne] at hrel
  set u0 := zeroVertex (vertexLen c)
  have hT₁_eq0 : decodeT₁ c u0 = List.range c.rows := by
    dsimp only [u0]; rw [hvlen, decodeT₁_zeroVertex]
  have hT₂_eq0 : decodeT₂ c u0 = (List.range c.cols).map (· + c.rows) := by
    dsimp only [u0]; rw [hvlen, decodeT₂_zeroVertex]
  have h01_0 : 0 ∈ decodeT₁ c u0 := by rw [hT₁_eq0, List.mem_range]; exact hc.1
  have h02_0 : 0 ∉ decodeT₂ c u0 := by
    rw [hT₂_eq0, List.mem_map]
    rintro ⟨j, _, hj⟩
    have := hc.1
    omega
  have hidx0 : halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) false = targetSign c := by
    obtain ⟨_, hlen₁, hlen₂, hacl, _, _, _, _⟩ := validNode_props hc hvalid_zero
    have hA₁_neg :
        ((intMatP (posMatB c)).map Int.cast : Matrix _ _ ℚ).submatrix
          ((Equiv.refl (Fin c.rows ⊕ Fin c.cols)) ∘ Sum.inl) (Equiv.refl _) = -1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.refl_apply, Matrix.map_apply,
        intMatP_inl, Matrix.neg_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    have hA₂_neg :
        ((intMatQ (posMatA c)).map Int.cast : Matrix _ _ ℚ).submatrix
          ((Equiv.refl (Fin c.rows ⊕ Fin c.cols)) ∘ Sum.inr) (Equiv.refl _) = -1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.refl_apply, Matrix.map_apply,
        intMatQ_inr, Matrix.neg_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    rw [halfEdgeIndexExec_eq c hc.1 (decodeT₁_sorted c u0) (decodeT₂_sorted c u0)
        (fun _ hr => decodeT₁_lt c u0 hr) (fun _ hr => decodeT₂_lt c u0 hr) hlen₁ hlen₂ false
        hacl (fun h => h02_0 (mem_finsetOfList.1 h)),
      LemkeHowson.halfEdgeIndex_zero_zero _ _ _ _ _ _ _
        (hT₁_eq0 ▸ finsetOfList_range_rows c.rows c.cols)
        (hT₂_eq0 ▸ finsetOfList_map_add_rows c.rows c.cols) hA₁_neg hA₂_neg,
      ← targetSign_eq]
  have hpred0 : pred (c, u0) = u0 := by
    have hnotv : (!isValidNodeExec c u0) = false := by
      simp only [hvalid_zero, Bool.not_true]
    have hne_neg : halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) false ≠ -targetSign c := by
      rw [hidx0]
      have hts := targetSign_eq c
      rcases neg_one_pow_eq_or ℤ (c.rows + c.cols) with h | h <;> rw [h] at hts <;> omega
    have hcond1 : (!decide (0 ∈ decodeT₂ c u0) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) false = -targetSign c)) =
        false := by
      simp [hne_neg]
    have hcond2 : (!decide (0 ∈ decodeT₁ c u0) &&
        decide (halfEdgeIndexExec c (decodeT₁ c u0) (decodeT₂ c u0) true = -targetSign c)) =
        false := by
      simp [h01_0]
    dsimp only [pred, stepGraph]
    simp only [hnotv, Bool.false_eq_true, ↓reduceIte, hcond1, hcond2]
  have hu_ne_zero : u ≠ u0 := by
    intro h0
    subst h0
    have hrt := stepGraph_roundTrip hc false hvalid_zero (.inl (by simp [h02_0, hidx0]))
    have hout : hasOut vertexLen pred succ c u0 = true := by
      simp only [hasOut, decide_eq_true_eq]
      exact ⟨hrt.2.2, hrt.2.1, hrt.2.1⟩
    rcases hu with ⟨-, hrel⟩
    simp [u0, hout] at hrel
  have hcl : 0 ∈ decodeT₁ c u ∨ 0 ∈ decodeT₂ c u := by
    by_contra hnot
    push Not at hnot
    obtain ⟨h01, h02⟩ := hnot
    obtain ⟨_, hlen₁, hlen₂, _, _, _, _, _⟩ := validNode_props hc hu_valid
    obtain ⟨_, _, p, htx, hty, _, _⟩ := node_of_isValidNodeExec hc hu_valid
    have hidx_opp := halfEdgeIndexExec_true_eq_neg_false_of_node hc (decodeT₁_sorted c u)
      (decodeT₂_sorted c u) (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
      hlen₁ hlen₂ p htx hty h01 h02
    have habs1 := abs_halfEdgeIndexExec_eq_one_of_node hc (decodeT₁_sorted c u)
      (decodeT₂_sorted c u) (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => decodeT₂_lt c u hr)
      hlen₁ hlen₂ p htx hty false h02
    have hidx_sq : (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false = targetSign c) ∨
        (halfEdgeIndexExec c (decodeT₁ c u) (decodeT₂ c u) false = -targetSign c) := by
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs1
      have hts := targetSign_eq c
      rcases neg_one_pow_eq_or ℤ (c.rows + c.cols) with hts1 | hts1 <;> rw [hts1] at hts <;>
        rcases habs1 with h1 | h1 <;> [exact .inl (by omega); exact .inr (by omega);
          exact .inr (by omega); exact .inl (by omega)]
    have hout : hasOut vertexLen pred succ c u = true := by
      have hrt := stepGraph_roundTrip hc false hu_valid
        (hidx_sq.imp (fun hpos => by simp [h02, hpos])
          (fun hneg => by simp [h01, hidx_opp, hneg]))
      have hne0 : succ (c, u) ≠ u0 := fun h0 =>
        hu_ne_zero ((hrt.2.2.symm.trans (congrArg (fun w => pred (c, w)) h0)).trans hpred0)
      simp only [hasOut, decide_eq_true_eq]
      exact ⟨hrt.2.2, hrt.2.1, hne0⟩
    have hin : hasIn vertexLen pred succ c u = true := by
      have hrt := stepGraph_roundTrip hc true hu_valid
        (hidx_sq.symm.imp (fun hneg => by simp [h02, hneg])
          (fun hpos => by simp [h01, hidx_opp, hpos]))
      simp only [hasIn, decide_eq_true_eq]
      exact ⟨hrt.2.2, hrt.2.1, hu_ne_zero⟩
    rcases hu with ⟨-, hrel⟩
    have hu_ne' : u ≠ zeroVertex (vertexLen c) := hu_ne_zero
    simp [hin, hout, hu_ne'] at hrel
  exact ⟨hu_valid, hu_ne_zero, hcl⟩

/-! ### Section 3: Witness extraction and `PPAD` membership -/

/-- Sign-adjusted unperturbed Cramer numerator vector `det(M_T).sign • cramerVec(M_T, b|_T)`
computed from row lists without division. -/
private def extractStrategyNum (k : ℕ) (allRows : List (List ℤ)) (allRhs : List ℤ)
    (T : List ℕ) : List ℤ :=
  let M := subRows k allRows T
  let s := (detRows M).sign
  (cramerVecRows k M (subRhs allRhs T)).map fun x => s * x

/-- Normalize a list of integer weights by their sum into exact rationals via `Rat.divInt`. -/
private def normalizeRatList (nums : List ℤ) : List ℚ :=
  let S := nums.sum
  nums.map fun num => Rat.divInt num S

private theorem extractStrategyNum_polytime {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {allRows : α → List (List ℤ)} {allRhs : α → List ℤ} {T : α → List ℕ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hall : ComputableInPolyTime allRows encIn encIntTable)
    (hrhs : ComputableInPolyTime allRhs encIn (encList encIntBin))
    (hT : ComputableInPolyTime T encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => extractStrategyNum (k x) (allRows x) (allRhs x) (T x))
      encIn (encList encIntBin) := by
  have hM := subRows_polytime hk hall hT
  have hs := intBin_sign.comp (detRows_polytime.comp hM)
  have hcv := cramerVecRows_polytime hk hM (subRhs_polytime hrhs hT)
  unfold extractStrategyNum
  refine mapWithInput (encA := encIntBin) hcv ?_
  exact intBin_mul' (hs.comp (fst encIn encIntBin)) (snd encIn encIntBin)

private theorem normalizeRatList_polytime {α : Type} {encIn : α ↪ List Bool}
    {nums : α → List ℤ} (hnums : ComputableInPolyTime nums encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => normalizeRatList (nums x)) encIn (encList encRat) := by
  have hS := intBin_sum.comp hnums
  unfold normalizeRatList
  refine mapWithInput (encA := encIntBin) hnums ?_
  exact rat_divInt' (snd encIn encIntBin) (hS.comp (fst encIn encIntBin))

/-- Polynomial-time Nash witness extractor from any non-origin end-of-line basis pair `(T₁, T₂)`.
Produces the canonical bit-encoded pair `(x, y)` on well-formed games and `[]` otherwise. -/
def extractNash (p : BimatrixCode × List Bool) : List Bool :=
  let c := p.1
  let u := p.2
  if c.wellFormedB then
    let T₁ := decodeT₁ c u
    let T₂ := decodeT₂ c u
    let x := normalizeRatList (extractStrategyNum c.rows (allRowsP c) (allIntRhsP c) T₁)
    let y := normalizeRatList (extractStrategyNum c.cols (allRowsQ c) (allIntRhsQ c) T₂)
    encWitness ⟨x, y⟩
  else []

private theorem extractNash_polytime :
    ComputableInPolyTime extractNash (encPair encBimatrix encBits) encBits := by
  have hc := fst encBimatrix encBits
  have h1 : ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₁ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := decodeT₁_polytime
  have h2 : ComputableInPolyTime (fun p : BimatrixCode × List Bool => decodeT₂ p.1 p.2)
      (encPair encBimatrix encBits) (encList encUnary) := decodeT₂_polytime
  have hx := normalizeRatList_polytime
    (extractStrategyNum_polytime (codeRows_polytime.comp hc) (allRowsP_polytime.comp hc)
      (allIntRhsP_polytime.comp hc) h1)
  have hy := normalizeRatList_polytime
    (extractStrategyNum_polytime (codeCols_polytime.comp hc) (allRowsQ_polytime.comp hc)
      (allIntRhsQ_polytime.comp hc) h2)
  have hpair := encWitness_mk_polyTime hx hy
  have hreenc : ComputableInPolyTime (fun s : StrategyPair => encWitness s) encWitness encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  unfold extractNash
  exact (ite' (wellFormedB_polytime.comp hc) (hreenc.comp hpair) (const [])).of_enc_eq
    fun _ => rfl

private lemma extractStrategyNum_spec {m n k : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (allRhs : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), allRhs.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) :
    have hcard : (finsetOfList m n T).card = k := (card_finsetOfList hsort.nodup hlt).trans hlen
    let nums := extractStrategyNum k allRows allRhs T
    nums.length = k ∧
      ∀ i : Fin k, nums.getD i.1 0 = basisSignNum M_int b_int (finsetOfList m n T) hcard i := by
  intro hcard nums
  obtain ⟨_, _, hsub_det⟩ := subRows_eq_basisMat M_int allRows hall hsort hlt hlen
  obtain ⟨hcv_len, hcv_get⟩ :=
    cramerVecRows_eq_cramerVec M_int b_int allRows allRhs hall hrhs hsort hlt hlen
  refine ⟨by simp [nums, extractStrategyNum, hcv_len], fun i => ?_⟩
  dsimp only [nums, extractStrategyNum]
  rw [List.getD_map_of_lt _ _ 0 0 (by rw [hcv_len]; exact i.2), hsub_det, hcv_get i]
  rfl

private lemma normalizeRatList_spec {k : ℕ} {nums : List ℤ} (hlen : nums.length = k)
    (hnn : ∀ i : Fin k, 0 ≤ nums.getD i.1 0) (hpos : 0 < nums.sum) :
    let v := normalizeRatList nums
    v.length = k ∧ (∀ q ∈ v, 0 ≤ q) ∧
      ∀ i : Fin k, v.getD i.1 0 = (nums.getD i.1 0 : ℚ) / (nums.sum : ℚ) := by
  intro v
  have hmem_nn : ∀ x ∈ nums, 0 ≤ x := by
    intro x hx
    rcases List.mem_iff_getElem.1 hx with ⟨i, hi, rfl⟩
    have hi' : i < k := hlen ▸ hi
    simpa only [List.getD_eq_getElem nums 0 hi] using hnn ⟨i, hi'⟩
  refine ⟨by simp [v, normalizeRatList, hlen], ?_, ?_⟩
  · intro q hq
    rcases List.mem_map.1 hq with ⟨num, hnum, rfl⟩
    rw [Rat.divInt_eq_div]
    exact div_nonneg (by exact_mod_cast hmem_nn num hnum) (by exact_mod_cast hpos.le)
  · intro i
    dsimp only [v, normalizeRatList]
    rw [List.getD_map_of_lt _ nums 0 0 (by rw [hlen]; exact i.2), Rat.divInt_eq_div]

private lemma list_sum_eq_one_of_div {k : ℕ} {v : List ℚ} {num : List ℤ}
    (hv_len : v.length = k) (hnum_len : num.length = k) (hpos : 0 < num.sum)
    (hget : ∀ i : Fin k, v.getD i.1 0 = (num.getD i.1 0 : ℚ) / (num.sum : ℚ)) :
    v.sum = 1 := by
  rw [← List.ofFn_getD_eq_of_length (l := v) 0 hv_len, List.sum_ofFn]
  have hne0 : (num.sum : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  calc ∑ i : Fin k, v.getD i.1 0
      = ∑ i : Fin k, (num.getD i.1 0 : ℚ) / (num.sum : ℚ) :=
        Finset.sum_congr rfl fun i _ => hget i
    _ = (∑ i : Fin k, (num.getD i.1 0 : ℚ)) / (num.sum : ℚ) := by rw [Finset.sum_div]
    _ = (num.sum : ℚ) / (num.sum : ℚ) := by
        rw [← Int.cast_sum, ← List.sum_ofFn, List.ofFn_getD_eq_of_length 0 hnum_len]
    _ = 1 := div_self hne0

/-- Lower bound on the framed bit-length of `encList enc l` from an elementwise lower bound. -/
theorem length_encList_ge_mul {α : Type*} (enc : α ↪ List Bool) (l : List α) (K : ℕ)
    (hK : ∀ a ∈ l, K ≤ (enc a).length) : l.length * (2 * K + 1) ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    have ha := hK a (by simp)
    have hl := ih fun b hb => hK b (by simp [hb])
    omega

private lemma size_prod_le {α : Type*} (l : List α) (f w : α → ℕ)
    (h : ∀ x ∈ l, (f x).size ≤ w x) : (l.map f).prod.size ≤ (l.map w).sum + 1 := by
  have hp := Int.size_natAbs_prod_le ((l.map f).map (Nat.cast : ℕ → ℤ))
  rw [← Nat.cast_list_prod, Int.natAbs_natCast, List.map_map, List.map_map] at hp
  have hsum : (l.map fun x => ((f x : ℤ).natAbs.size)).sum ≤ (l.map w).sum :=
    List.sum_le_sum fun x hx => by simpa only [Int.natAbs_natCast] using h x hx
  exact hp.trans (Nat.add_le_add_right hsum 1)

private lemma natAbs_prod_mat (M : List (List ℚ)) :
    Int.natAbs ((M.map fun row : List ℚ => (row.map fun q => (q.den : ℤ)).prod).prod) =
      (M.map fun row : List ℚ => (row.map fun q => q.den).prod).prod := by
  have hrow (row : List ℚ) : (row.map fun q => (q.den : ℤ)).prod = ↑(row.map Rat.den).prod := by
    simpa only [List.map_map, Function.comp_def] using (Nat.cast_list_prod (row.map Rat.den)).symm
  simpa only [hrow, ← Function.comp_def, ← List.map_map, ← Nat.cast_list_prod] using
    Int.natAbs_natCast _

private lemma natAbs_sum_mat (D : ℤ) (M : List (List ℚ)) :
    ((M.map fun row : List ℚ => (row.map fun q => (scaledEntry D q).natAbs).sum).sum : ℤ) =
      (M.map fun row : List ℚ => (row.map fun q => |scaledEntry D q|).sum).sum := by
  simp [Nat.cast_list_sum, List.map_map, Function.comp_def]

private lemma size_HVal_and_dims_le {c : BimatrixCode} (hc : c.WellFormed) :
    38 * c.rows * c.cols + 1 ≤ (encBimatrix c).length ∧
      (HVal c).size ≤ 4 * (encBimatrix c).length + 4 := by
  set L := (encBimatrix c).length
  have hL : L = 2 * (encList (encList encRat) c.matA).length + 1 +
      (encList (encList encRat) c.matB).length := by
    dsimp only [L]
    rw [encBimatrix_apply, length_encPair]
  have hlen1_le : (encList (encList encRat) c.matA).length ≤ L := by omega
  have hlen2_le : (encList (encList encRat) c.matB).length ≤ L := by omega
  have hrows_cols : 38 * c.rows * c.cols + 1 ≤ L := by
    have hmat_len : ∀ M : List (List ℚ), M.length = c.rows →
        (∀ row ∈ M, row.length = c.cols) →
        c.rows * (2 * (c.cols * 9) + 1) ≤ (encList (encList encRat) M).length := by
      intro M hMlen hMrow
      have hrow_ge : ∀ row ∈ M, c.cols * 9 ≤ (encList encRat row).length := by
        intro row hrow
        rw [← hMrow row hrow]
        exact length_encList_ge_mul encRat row 4 fun q _ =>
          Turing.MultiTapeTM.four_le_length_encRat q
      have hm_ge := length_encList_ge_mul (encList encRat) M (c.cols * 9) hrow_ge
      rwa [hMlen] at hm_ge
    have h1_ge := hmat_len c.matA rfl hc.2.2.2.1
    have h2_ge := hmat_len c.matB hc.2.2.1 hc.2.2.2.2
    have hmul_eq : c.rows * (2 * (c.cols * 9) + 1) = 18 * (c.rows * c.cols) + c.rows := by ring
    rw [hmul_eq] at h1_ge h2_ge
    rw [mul_assoc]
    omega
  have hprod_mat_le : ∀ M : List (List ℚ),
      Nat.size ((M.map fun row : List ℚ => (row.map fun q => q.den).prod).prod) ≤
        (encList (encList encRat) M).length + 1 := by
    intro M
    refine size_prod_le M _ (fun row => 2 * (encList encRat row).length + 1) ?_ |>.trans ?_
    · intro row _
      have hrow_p : Nat.size (row.map fun q => q.den).prod ≤
          (row.map fun q => (encRat q).length).sum + 1 :=
        size_prod_le row _ (fun q => (encRat q).length) fun q _ => by
          have hlen_eq := Turing.MultiTapeTM.length_encRat q
          omega
      have hsum_le :=
        hrow_p.trans (Nat.add_le_add_right (sum_length_le_length_encList encRat row) 1)
      omega
    · rw [← length_encList (encList encRat) M]
  have hD_size : (clearScale c).natAbs.size ≤ L := by
    have h1 := hprod_mat_le c.matA
    have h2 := hprod_mat_le c.matB
    have hm := Nat.size_mul_le
      (c.matA.map fun row : List ℚ => (row.map fun q => q.den).prod).prod
      (c.matB.map fun row : List ℚ => (row.map fun q => q.den).prod).prod
    have hnat : (clearScale c).natAbs =
        (c.matA.map fun row : List ℚ => (row.map fun q => q.den).prod).prod *
          (c.matB.map fun row : List ℚ => (row.map fun q => q.den).prod).prod := by
      dsimp only [clearScale]
      rw [Int.natAbs_mul, natAbs_prod_mat, natAbs_prod_mat]
    have hne0 : 1 ≤ (encList (encList encRat) c.matA).length := by
      have h1_ge := length_encList_ge_mul (encList encRat) c.matA 0 fun _ _ => Nat.zero_le _
      have hr : 1 ≤ c.matA.length := hc.1
      omega
    rw [hnat]
    omega
  have hsum_mat_le : ∀ M : List (List ℚ), (encList (encList encRat) M).length ≤ L →
      Nat.size ((M.map fun row : List ℚ =>
          (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum) ≤ 4 * L := by
    intro M hML
    have hM_len : M.length ≤ L := (length_le_length_encList (encList encRat) M).trans hML
    have hM_sum := Nat.size_sum_le
      (l := M.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum)
      (b := 3 * L) fun s hs => by
        rcases List.mem_map.1 hs with ⟨row, hrow, rfl⟩
        have hrow_enc : (encList encRat row).length ≤ L :=
          (length_le_encList_of_mem (encList encRat) hrow).trans hML
        have hrow_len : row.length ≤ L := (length_le_length_encList encRat row).trans hrow_enc
        have hrow_sum := Nat.size_sum_le
          (l := row.map fun q => (scaledEntry (clearScale c) q).natAbs) (b := 2 * L)
          fun s' hs' => by
            rcases List.mem_map.1 hs' with ⟨q, hq, rfl⟩
            have hq_enc : (encRat q).length ≤ L :=
              (length_le_encList_of_mem encRat hq).trans hrow_enc
            have hq_num : q.num.natAbs.size ≤ L := by
              have hlen_eq := Turing.MultiTapeTM.length_encRat q
              omega
            have hsc_le : (scaledEntry (clearScale c) q).natAbs ≤
                q.num.natAbs * (clearScale c).natAbs := by
              dsimp only [scaledEntry]
              rw [Int.natAbs_mul, Int.natAbs_tdiv, Int.natAbs_natCast]
              exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
            have hsc_size := (Nat.size_le_size hsc_le).trans (Nat.size_mul_le _ _)
            omega
        rw [List.length_map] at hrow_sum
        exact hrow_sum.trans (by
          have hl := (Nat.size_le_self row.length).trans hrow_len
          omega)
    rw [List.length_map] at hM_sum
    exact hM_sum.trans (by
      have hl := (Nat.size_le_self M.length).trans hM_len
      omega)
  have hs1 := hsum_mat_le c.matA hlen1_le
  have hs2 := hsum_mat_le c.matB hlen2_le
  have hshift_nat : (shiftVal c).natAbs =
      1 + (c.matA.map fun row : List ℚ =>
          (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum +
        (c.matB.map fun row : List ℚ =>
          (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum := by
    have hs_pos : 0 ≤ shiftVal c := le_of_lt (shiftVal_pos c)
    apply Nat.cast_injective (R := ℤ)
    rw [Int.natAbs_of_nonneg hs_pos]
    dsimp only [shiftVal]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, natAbs_sum_mat, natAbs_sum_mat]
  have hshift_size : (shiftVal c).natAbs.size ≤ 4 * L + 2 := by
    rw [hshift_nat]
    have ha := Nat.size_add_le_max
      (1 + (c.matA.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum)
      (c.matB.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum
    have hb := Nat.size_add_le_max 1
      (c.matA.map fun row : List ℚ =>
        (row.map fun q => (scaledEntry (clearScale c) q).natAbs).sum).sum
    have h1_size : (1 : ℕ).size = 1 := by decide
    omega
  have hH_size : (HVal c).size ≤ 4 * L + 4 := by
    dsimp only [HVal]
    have hm := Nat.size_mul_le 2 (shiftVal c).natAbs
    have h2_size : (2 : ℕ).size = 2 := by decide
    omega
  exact ⟨hrows_cols, hH_size⟩

private lemma isRationalNash_of_toGame_isNash {c : BimatrixCode} {x y : List ℚ}
    (hx_len : x.length = c.rows) (hy_len : y.length = c.cols)
    (hx_nn : ∀ q ∈ x, 0 ≤ q) (hx_sum : x.sum = 1)
    (hy_nn : ∀ q ∈ y, 0 ≤ q) (hy_sum : y.sum = 1)
    (hGameNash : c.toGame.IsNash (strategyVec x) (strategyVec y)) :
    c.IsRationalNash x y := by
  obtain ⟨h₁, h₂⟩ := BimatrixGame.isNash_iff.1 hGameNash
  refine ⟨hx_len, hy_len, hx_nn, hx_sum, hy_nn, hy_sum, fun i => ?_, fun j => ?_⟩
  · rw [← Rat.cast_le (K := ℝ)]
    have h := h₁.le_payoff₁ i
    rw [BimatrixGame.payoff₁_eq_dotProduct] at h
    simpa only [strategyVec_apply, toGame, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, mul_assoc] using h
  · rw [← Rat.cast_le (K := ℝ)]
    have h := h₂.le_payoff₂ j
    rw [BimatrixGame.payoff₂_eq_dotProduct, dotProduct_comm (strategyVec y)] at h
    simp only [strategyVec_apply, toGame, Matrix.vecMul, dotProduct, Matrix.map_apply,
      Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, mul_assoc] at h ⊢
    rw [Finset.sum_comm] at h
    exact h

private lemma strategy_pair_size_bd {k H L : ℕ} (hkL : k ≤ L) (hH_sz : H.size ≤ 4 * L + 4)
    {num_l : List ℤ} (hlen : num_l.length = k)
    (hbd : ∀ i : Fin k, |num_l.getD i.1 0| ≤ ((k.factorial * H ^ k : ℕ) : ℤ))
    (hpos : 0 < num_l.sum) :
    ∀ q ∈ normalizeRatList num_l, (encRat q).length ≤ 3 * (k * (5 * L + 5) + 2) + 3 := by
  intro q hq
  rcases List.mem_map.1 hq with ⟨num, hnum, rfl⟩
  rcases List.mem_iff_getElem.1 hnum with ⟨idx, hidx, rfl⟩
  have hidx' : idx < k := hlen ▸ hidx
  let i : Fin k := ⟨idx, hidx'⟩
  have hnum_eq : num_l[idx] = num_l.getD i.1 0 :=
    (List.getD_eq_getElem num_l 0 hidx).symm
  have hbd_num : num_l[idx].natAbs ≤ k.factorial * H ^ k := by
    rw [hnum_eq]
    have hbi := hbd i
    rw [← Int.natCast_natAbs] at hbi
    exact Int.ofNat_le.1 hbi
  have hbd_sum : num_l.sum.natAbs ≤ k * (k.factorial * H ^ k) := by
    have hS_nn : 0 ≤ num_l.sum := hpos.le
    have hS_Z : (num_l.sum : ℤ) ≤ ((k * (k.factorial * H ^ k) : ℕ) : ℤ) := by
      rw [← List.ofFn_getD_eq_of_length (l := num_l) 0 hlen, List.sum_ofFn]
      calc ∑ i' : Fin k, num_l.getD i'.1 0
          ≤ ∑ _i' : Fin k, ((k.factorial * H ^ k : ℕ) : ℤ) :=
            Finset.sum_le_sum fun i' _ => (le_abs_self _).trans (hbd i')
        _ = ((k * (k.factorial * H ^ k) : ℕ) : ℤ) := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_mul]
    exact Int.ofNat_le.1 (by simpa only [Int.natAbs_of_nonneg hS_nn] using hS_Z)
  have hfac := Nat.size_factorial_le k
  have hpow := Nat.size_pow_le H k
  have hks := Nat.size_le_self k
  have hbase_sz : (k.factorial * H ^ k).size ≤ k * (5 * L + 4) + 2 := by
    have hm := Nat.size_mul_le k.factorial (H ^ k)
    have hkk : k * k.size ≤ k * L := Nat.mul_le_mul_left k (hks.trans hkL)
    have hkH : k * H.size ≤ k * (4 * L + 4) := Nat.mul_le_mul_left k hH_sz
    have hmul : k * L + 1 + (k * (4 * L + 4) + 1) = k * (5 * L + 4) + 2 := by ring
    omega
  have hsum_sz : num_l.sum.natAbs.size ≤ k * (5 * L + 5) + 2 := by
    have hs := (Nat.size_le_size hbd_sum).trans (Nat.size_mul_le _ _)
    have hsum_eq : k + (k * (5 * L + 4) + 2) = k * (5 * L + 5) + 2 := by ring
    omega
  have hnum_sz : num_l[idx].natAbs.size ≤ k * (5 * L + 5) + 2 := by
    have hs := (Nat.size_le_size hbd_num).trans hbase_sz
    have hle : k * (5 * L + 4) ≤ k * (5 * L + 5) := Nat.mul_le_mul_left k (by omega)
    omega
  exact (length_encRat_le _
    (Rat.natAbs_num_divInt_le _ _ hpos.ne')
    (Rat.den_divInt_le _ _ hpos.ne')).trans (by omega)

private lemma witness_length_arith {m n L ax ay : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hrc : 38 * m * n + 1 ≤ L)
    (hx : ax ≤ m * (6 * (m * (5 * L + 5) + 2) + 7))
    (hy : ay ≤ n * (6 * (n * (5 * L + 5) + 2) + 7)) :
    2 * ax + 1 + ay ≤ 120 * L ^ 3 + 400 * L + 100 := by
  have hL2_le : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  -- One player's bound, used for both players.
  have side_bd {k a : ℕ} (hk : 38 * k ≤ L) (ha : a ≤ k * (6 * (k * (5 * L + 5) + 2) + 7)) :
      a ≤ 2 * L ^ 3 + L := by
    have hk2_le : 1444 * k ^ 2 ≤ L ^ 2 := by
      calc 1444 * k ^ 2 = (38 * k) * (38 * k) := by ring
        _ ≤ L * L := Nat.mul_le_mul hk hk
        _ = L ^ 2 := (sq L).symm
    have hk2L_le : 1444 * (k ^ 2 * L) ≤ L ^ 3 := by
      calc 1444 * (k ^ 2 * L) = 1444 * k ^ 2 * L := (mul_assoc _ _ _).symm
        _ ≤ L ^ 2 * L := Nat.mul_le_mul_right L hk2_le
        _ = L ^ 3 := by ring
    rw [show k * (6 * (k * (5 * L + 5) + 2) + 7) = 30 * (k ^ 2 * L) + 30 * k ^ 2 + 19 * k by
      ring] at ha
    omega
  have hm_le : 38 * m ≤ 38 * m * n := Nat.le_mul_of_pos_right _ hn
  have hn_le : 38 * n ≤ 38 * m * n := by
    calc 38 * n = 38 * 1 * n := by ring
      _ ≤ 38 * m * n := Nat.mul_le_mul_right n (Nat.mul_le_mul_left 38 hm)
  have hax := side_bd (by omega) hx
  have hay := side_bd (by omega) hy
  omega

/-- One player's extracted strategy: normalizing the sign-adjusted Cramer numerators of the basis
`T` gives a probability vector equal to the normalized basis numerators, with the per-player
encoding length bound used by `witness_length_arith`. -/
private lemma extractSide_spec {m n k H L : ℕ}
    (M_int : Matrix (Fin m ⊕ Fin n) (Fin k) ℤ) (b_int : Fin m ⊕ Fin n → ℤ)
    (allRows : List (List ℤ)) (allRhs : List ℤ)
    (hall : ∀ (r : Fin (m + n)) (j : Fin k),
      rowEntry allRows r.1 j.1 = M_int (finSumFinEquiv.symm r) j)
    (hrhs : ∀ (r : Fin (m + n)), allRhs.getD r.1 0 = b_int (finSumFinEquiv.symm r))
    {T : List ℕ} (hsort : T.Pairwise (· < ·)) (hlt : ∀ r ∈ T, r < m + n)
    (hlen : T.length = k) (hcard : (finsetOfList m n T).card = k)
    (hnum_nn : ∀ i : Fin k, 0 ≤ basisSignNum M_int b_int (finsetOfList m n T) hcard i)
    (hS_pos : 0 < ∑ i : Fin k, basisSignNum M_int b_int (finsetOfList m n T) hcard i)
    (hbd : ∀ i : Fin k,
      |basisSignNum M_int b_int (finsetOfList m n T) hcard i| ≤ ((k.factorial * H ^ k : ℕ) : ℤ))
    (hkL : k ≤ L) (hH_sz : H.size ≤ 4 * L + 4) :
    let v := normalizeRatList (extractStrategyNum k allRows allRhs T)
    v.length = k ∧ (∀ q ∈ v, 0 ≤ q) ∧ v.sum = 1 ∧
      (strategyVec v : Fin k → ℝ) =
        (fun i => ((basisSignNum M_int b_int (finsetOfList m n T) hcard i : ℤ) : ℝ) /
          ((∑ i : Fin k, basisSignNum M_int b_int (finsetOfList m n T) hcard i : ℤ) : ℝ)) ∧
      (encList encRat v).length ≤ k * (6 * (k * (5 * L + 5) + 2) + 7) := by
  intro v
  obtain ⟨hnum_len, hnum_get⟩ := extractStrategyNum_spec M_int b_int allRows allRhs
    hall hrhs hsort hlt hlen
  let num_l := extractStrategyNum k allRows allRhs T
  have hS_eq : num_l.sum = ∑ i : Fin k, basisSignNum M_int b_int (finsetOfList m n T) hcard i := by
    rw [← List.ofFn_getD_eq_of_length (l := num_l) 0 hnum_len, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => hnum_get i
  have hv := normalizeRatList_spec hnum_len (fun i => by rw [hnum_get i]; exact hnum_nn i)
    (hS_eq ▸ hS_pos)
  have hB := strategy_pair_size_bd hkL hH_sz hnum_len (fun i => by rw [hnum_get i]; exact hbd i)
    (hS_eq ▸ hS_pos)
  refine ⟨hv.1, hv.2.1, list_sum_eq_one_of_div hv.1 hnum_len (hS_eq ▸ hS_pos) hv.2.2, ?_, ?_⟩
  · ext i
    rw [strategyVec_apply, hv.2.2 i, hnum_get i, hS_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
  · have hl := length_encList_le encRat v hB
    rw [hv.1] at hl
    exact hl.trans (Nat.mul_le_mul_left _ (by omega))

/-- Every vertex solving `endOfLineRel vertexLen pred succ c` extracts via `extractNash` to a
solution of `BimatrixNash c`. -/
theorem extractNash_sound {c : BimatrixCode} {u : List Bool}
    (hu : endOfLineRel vertexLen pred succ c u) :
    BimatrixNash c (extractNash (c, u)) := by
  by_cases hwb : c.wellFormedB = true
  · have hc : c.WellFormed := (wellFormed_iff_wellFormedB c).2 hwb
    obtain ⟨hu_valid, hu_ne0, hcl0⟩ := endOfLineRel_wellFormed_props hc hu
    obtain ⟨hlen_u, hlen₁, hlen₂, hacl, hcard₁, hcard₂, hfb₁, hfb₂⟩ := validNode_props hc hu_valid
    let T₁ := decodeT₁ c u
    let T₂ := decodeT₂ c u
    let T₁s := finsetOfList c.rows c.cols T₁
    let T₂s := finsetOfList c.rows c.cols T₂
    have huniv : T₁s ∪ T₂s = Finset.univ := by
      ext k
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hk : k = Sum.inl ⟨0, hc.1⟩
      · subst hk
        rcases hcl0 with h0 | h0
        · exact .inl (mem_finsetOfList.2 h0)
        · exact .inr (mem_finsetOfList.2 h0)
      · exact hacl k hk
    have hne0 : (T₁s, T₂s) ≠ (Finset.univ.image Sum.inl, Finset.univ.image Sum.inr) := by
      intro heq
      have hT₁_eq : T₁ = List.range c.rows :=
        eq_of_finsetOfList_eq (decodeT₁_sorted c u) List.pairwise_lt_range
          (fun _ hr => decodeT₁_lt c u hr) (fun _ hr => by rw [List.mem_range] at hr; omega)
          ((congrArg Prod.fst heq).trans (finsetOfList_range_rows c.rows c.cols).symm)
      have hT₂_eq : T₂ = (List.range c.cols).map (· + c.rows) :=
        eq_of_finsetOfList_eq (decodeT₂_sorted c u)
          (List.pairwise_lt_range.map _ fun _ _ h => by omega)
          (fun _ hr => decodeT₂_lt c u hr)
          (fun _ hr => by
            rcases List.mem_map.1 hr with ⟨j, hj, rfl⟩; rw [List.mem_range] at hj; omega)
          ((congrArg Prod.snd heq).trans (finsetOfList_map_add_rows c.rows c.cols).symm)
      have hu_eq : u = zeroVertex (vertexLen c) := by
        have hvlen : vertexLen c = 2 * (c.rows + c.cols) := by simp [vertexLen, hwb]
        rw [hvlen, ← encodeNodes_origin c, ← hT₁_eq, ← hT₂_eq]
        exact (encodeNodes_decode hlen_u).symm
      exact hu_ne0 hu_eq
    have hH : 1 ≤ HVal c := (posMat_bounds hc ⟨0, hc.1⟩ ⟨0, hc.2.1⟩).1
    have hA_bd : ∀ i j, 1 ≤ posMatA c i j ∧ posMatA c i j ≤ (HVal c : ℤ) := fun i j =>
      ⟨(posMat_bounds hc i j).2.1, (posMat_bounds hc i j).2.2.1⟩
    have hB_bd : ∀ i j, 1 ≤ posMatB c i j ∧ posMatB c i j ≤ (HVal c : ℤ) := fun i j =>
      ⟨(posMat_bounds hc i j).2.2.2.1, (posMat_bounds hc i j).2.2.2.2⟩
    have hex := BimatrixGame.isNash_extractNum hc.1 hc.2.1 hH hA_bd hB_bd hfb₁ hfb₂ huniv hne0
    dsimp only at hex
    obtain ⟨hnumP_nn, hS₁_pos, hP_bd, hnumQ_nn, hS₂_pos, hQ_bd, hNashPos⟩ := hex
    obtain ⟨hrc, hH_size⟩ := size_HVal_and_dims_le hc
    set L := (encBimatrix c).length
    have hm_le_L : c.rows ≤ L := by
      have h1 :=
        calc c.rows ≤ 38 * c.rows * 1 := by omega
          _ ≤ 38 * c.rows * c.cols := Nat.mul_le_mul_left _ hc.2.1
      omega
    have hn_le_L : c.cols ≤ L := by
      have h1 :=
        calc c.cols ≤ 38 * 1 * c.cols := by omega
          _ ≤ 38 * c.rows * c.cols := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 38 hc.1)
      omega
    obtain ⟨hx_len, hx_nn, hx_sum, hx_getR, hlen_x⟩ := extractSide_spec (intMatP (posMatB c))
      (intRhsP c.rows c.cols) (allRowsP c) (allIntRhsP c) (allRowsP_spec c) (allIntRhsP_spec c)
      (decodeT₁_sorted c u) (fun _ hr => decodeT₁_lt c u hr) hlen₁ hcard₁ hnumP_nn hS₁_pos hP_bd
      hm_le_L hH_size
    obtain ⟨hy_len, hy_nn, hy_sum, hy_getR, hlen_y⟩ := extractSide_spec (intMatQ (posMatA c))
      (intRhsQ c.rows c.cols) (allRowsQ c) (allIntRhsQ c) (allRowsQ_spec c) (allIntRhsQ_spec c)
      (decodeT₂_sorted c u) (fun _ hr => decodeT₂_lt c u hr) hlen₂ hcard₂ hnumQ_nn hS₂_pos hQ_bd
      hn_le_L hH_size
    let x := normalizeRatList (extractStrategyNum c.rows (allRowsP c) (allIntRhsP c) T₁)
    let y := normalizeRatList (extractStrategyNum c.cols (allRowsQ c) (allIntRhsQ c) T₂)
    have hGameNash : c.toGame.IsNash (strategyVec x) (strategyVec y) := by
      rw [hx_getR, hy_getR]
      exact (isNash_posMat hc _ _).1 hNashPos
    have hRatNash : c.IsRationalNash x y :=
      isRationalNash_of_toGame_isNash hx_len hy_len hx_nn hx_sum hy_nn hy_sum hGameNash
    have hw_eq : extractNash (c, u) = encWitness ⟨x, y⟩ := by
      dsimp only [extractNash]
      simp only [hwb, ite_true]
      rfl
    have hlen_w : (extractNash (c, u)).length ≤ 120 * L ^ 3 + 400 * L + 100 := by
      rw [hw_eq, encWitness_apply]
      change (encPair (encList encRat) (encList encRat) (x, y)).length ≤
        120 * L ^ 3 + 400 * L + 100
      rw [length_encPair]
      exact witness_length_arith hc.1 hc.2.1 hrc hlen_x hlen_y
    simp only [BimatrixNash, hwb, ite_true, witnessPoly_eval]
    exact ⟨hlen_w, ⟨x, y⟩, hw_eq, hRatNash⟩
  · have hwf : c.wellFormedB = false := Bool.eq_false_iff.2 hwb
    simp only [BimatrixNash, extractNash, hwf, Bool.false_eq_true, ite_false]

/-- Every solution witness of a well-formed game decodes to a Nash equilibrium of `c.toGame`. -/
theorem BimatrixNash.isNash {c : BimatrixCode} {w : List Bool}
    (hc : c.WellFormed) (hw : BimatrixNash c w) :
    ∃ s : StrategyPair, w = encWitness s ∧ c.toGame.IsNash (strategyVec s.x) (strategyVec s.y) := by
  have hwb : c.wellFormedB = true := (wellFormed_iff_wellFormedB c).1 hc
  simp only [BimatrixNash, hwb, ite_true] at hw
  obtain ⟨-, s, rfl, hrat⟩ := hw
  exact ⟨s, rfl, hrat.toGame_isNash⟩

/-- Two-player rational Nash equilibrium search-reduces in polynomial time to the canonical
PPAD problem `endOfLineRel vertexLen pred succ`. -/
theorem BimatrixNash_searchReducible_endOfLineRel :
    SearchReducible encBimatrix encBimatrix BimatrixNash (endOfLineRel vertexLen pred succ) :=
  .of_isTotalSearch (isTotalSearch_endOfLineRel length_succ) ComputableInPolyTime.id'
    extractNash_polytime fun _ _ hw => extractNash_sound hw

/-- **Two-player rational Nash equilibrium is in `PPAD`.** -/
theorem BimatrixNash_mem_PPAD : BimatrixNash ∈ PPAD encBimatrix :=
  mem_PPAD.2 ⟨BimatrixNash_mem_FNP, vertexLen, pred, succ,
    vertexLen_polytime, pred_polytime, succ_polytime, length_pred, length_succ,
    BimatrixNash_searchReducible_endOfLineRel⟩

/-- **Two-player rational Nash equilibrium is in `TFNP`** (and hence total by Brouwer /
Lemke–Howson). -/
theorem BimatrixNash_mem_TFNP : BimatrixNash ∈ TFNP encBimatrix :=
  PPAD_subset_TFNP BimatrixNash_mem_PPAD

/-- **Totality of two-player Nash:** every encoded rational game has a valid rational Nash
equilibrium witness (or empty witness on malformed inputs). -/
theorem BimatrixNash_isTotalSearch : IsTotalSearch BimatrixNash :=
  BimatrixNash_mem_TFNP.2

/-- **Reduction to circuit `EndOfLine`:** two-player rational Nash search-reduces in polynomial
time to canonical circuit `EndOfLine`. -/
theorem BimatrixNash_searchReducible_EndOfLine :
    SearchReducible encBimatrix encEndOfLine BimatrixNash EndOfLine :=
  EndOfLine_searchComplete.2 _ _ BimatrixNash_mem_PPAD

end Cslib.GameTheory.BimatrixCode
