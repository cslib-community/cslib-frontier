/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.TaggedCompiler
public import Cslib.Computability.Circuit.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Circuit.Frontier.Compiler.OpenBitNetwork
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.BatchPrice
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TrivalentVolume
import CslibFrontier.Computability.Circuit.InnerSize
import CslibFrontier.Foundations.Data.Nat.Asymptotics

/-!
# Signed workloads transfer a compiler saving to element distinctness

Given a signed computation with a polynomial-size Boolean verifier, minimize the volume of
a trivalent network for each batch of its signed tensor. Disjoint verifier networks give the
initial upper bound. A hard batch interval forces the minimum cost per exterior bit to stay
within a factor two under all replications available to the compiler at some scale. Compiling
a minimizing network at that scale makes the cost of the tagged-permutation tests explicit.
The signed projection from distinctness realizes those tests.

The conditional theorem takes the actual hard-batch bound from [OpenAI2026HamiltonianPermanent,
Theorem 12.1] and the normalized tagged-network compiler of [OpenAI2026EuclideanSpectrum,
Proposition 14.1] used in [OpenAI2026MatrixExponentNineFourths, “Finite fields with ports”].
The source verifier checks a machine clocked for `ℓ ^ 100` steps, rejects nonzero unused guess
bits, and returns a sign. Here the verifier is a supplied circuit accepting a padded guess
and its requested sign. Its signed network, disjoint copies, minimizing networks, normalization,
joint substitution, replication and growth estimates are constructed or proved inside the transfer.
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Filter Frontier Frontier.OpenBitNetwork Finset

-- With L binary digits, the initial polynomial cost is below two to this many rounds.
private theorem initial_rounds (h b A : ℕ) :
    (h ^ b) ^ A < 2 ^ ((b * A + 1) * (Nat.log 2 h + 1)) := by
  let L := Nat.log 2 h + 1
  have hl : h ≤ 2 ^ L := (Nat.lt_pow_succ_log_self one_lt_two h).le
  calc
    (h ^ b) ^ A = h ^ (b * A) := (pow_mul _ _ _).symm
    _ ≤ (2 ^ L) ^ (b * A) := Nat.pow_le_pow_left hl _
    _ = 2 ^ (b * A * L) := by rw [← pow_mul, Nat.mul_comm L]
    _ < _ := Nat.pow_lt_pow_right one_lt_two (by dsimp [L]; rw [add_mul, one_mul]; lia)

-- L rounds on the log scale, each with a quadratic-log replication exponent, cost o(h).
private theorem eventual_replication_window (C b A : ℕ) :
    ∀ᶠ h : ℕ in atTop,
      let L := Nat.log 2 h + 1
      (2 ^ h) ^ 2 * (2 ^ (C * L ^ 2)) ^ ((b * A + 1) * L) ≤ (2 ^ h) ^ 3 := by
  have lower := (Nat.tendsto_log_atTop one_lt_two).eventually
    (Nat.eventually_mul_add_one_pow_le_pow (C * (b * A + 1)) 3 one_lt_two)
  filter_upwards [lower, eventually_ge_atTop 1] with h hlog hh
  let L := Nat.log 2 h + 1
  have hbudget : C * L ^ 2 * ((b * A + 1) * L) ≤ h :=
    (show C * L ^ 2 * ((b * A + 1) * L) = C * (b * A + 1) * L ^ 3 by ring).le.trans
      (hlog.trans (Nat.pow_log_le_self 2 (by lia)))
  have hd : (2 ^ (C * L ^ 2)) ^ ((b * A + 1) * L) ≤ 2 ^ h := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hbudget
  exact (Nat.mul_le_mul_left _ hd).trans_eq (pow_succ _ 2).symm

private theorem hard_range {h b : ℕ} {ξ : ℝ} (hh : 6 ≤ h) (hb : 2 ≤ (b : ℝ) * ξ)
    {j : ℕ} (hj : j ≤ (2 ^ h) ^ 3) :
    (j : ℝ) ≤ (2 : ℝ) ^ (((h ^ b : ℕ) : ℝ) ^ ξ) := by
  have hhR : 6 ≤ (h : ℝ) := by exact_mod_cast hh
  have hlen : 3 * (h : ℝ) ≤ ((h ^ b : ℕ) : ℝ) ^ ξ := calc
    _ ≤ (h : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    _ ≤ (h : ℝ) ^ ((b : ℝ) * ξ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = _ := by rw [Real.rpow_natCast_mul (Nat.cast_nonneg _), Nat.cast_pow]
  calc
    (j : ℝ) ≤ (((2 ^ h) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hj
    _ = (2 : ℝ) ^ (3 * (h : ℝ)) := by
      rw [← Nat.cast_ofNat (R := ℝ) (n := 3), ← Nat.cast_mul, Real.rpow_natCast, mul_comm 3 h,
        pow_mul]
      push_cast
      rfl
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlen

private theorem absorb_boundary {h b C : ℕ} {a δ : ℝ} (hh : 6 ≤ h) (hb : b ≠ 0)
    (hexp : a + ((C + 2 : ℕ) : ℝ) ≤ (b : ℝ) * δ) :
    (h : ℝ) ^ a * (((Nat.log 2 h + 1) ^ C : ℕ) + 6 * h / (h ^ b : ℕ)) ≤
      ((h ^ b : ℕ) : ℝ) ^ δ := by
  have hhR : 6 ≤ (h : ℝ) := by exact_mod_cast hh
  have hl : h ≤ h ^ b := Nat.le_self_pow hb _
  have hℓ : 0 < ((h ^ b : ℕ) : ℝ) := by positivity
  have hfrac : 6 * (h : ℝ) / (h ^ b : ℕ) ≤ 6 :=
    (div_le_iff₀ hℓ).mpr (by exact_mod_cast Nat.mul_le_mul_left 6 hl)
  let z := h ^ (C + 1)
  have hz : h ≤ z := Nat.le_self_pow (Nat.succ_ne_zero _) _
  have hlog : (Nat.log 2 h + 1) ^ C ≤ z :=
    (Nat.pow_le_pow_left (Nat.log_lt_self 2 (by lia) : Nat.log 2 h < h) _).trans
      (Nat.pow_le_pow_right (by lia) (Nat.le_succ C))
  have hsum : (((Nat.log 2 h + 1) ^ C : ℕ) : ℝ) + 6 * h / (h ^ b : ℕ) ≤
      (h : ℝ) ^ (C + 2) := calc
    _ ≤ (z : ℝ) + z :=
      add_le_add (by exact_mod_cast hlog) (hfrac.trans (by exact_mod_cast hh.trans hz))
    _ = 2 * z := by ring
    _ ≤ (h : ℝ) * z := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ = _ := by dsimp [z]; rw [Nat.cast_pow, pow_succ _ (C + 1), mul_comm]
  calc
    _ ≤ (h : ℝ) ^ a * (h : ℝ) ^ (C + 2) := mul_le_mul_of_nonneg_left hsum
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (h : ℝ) ^ (a + ((C + 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    _ ≤ (h : ℝ) ^ ((b : ℝ) * δ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = _ := by rw [Real.rpow_natCast_mul (Nat.cast_nonneg _), Nat.cast_pow]

open scoped Classical in
/-- Conditional transfer of a compiler saving `h ^ a` to the volume of every realization of
`t` distinctness tests, uniformly for `1 ≤ t ≤ 2 * 2 ^ h` and all sufficiently large `h`.
The number `x ℓ j` is the workload cost per bit. The hypotheses bound it above by disjoint
implementations, bound it below on hard batches, and charge an exact compilation against an
actual trivalent routing network. The factor three allows normalization of the workload.
The conclusion counts the `3 * 2 ^ h * h` routing ports per test. -/
private theorem eventually_batch_volume_of_hard_workload_of_compiler
    (R : Type) [CommRing R] (x : ℕ → ℕ → ℝ) {a δ ξ K : ℝ} {A C : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hξ : 0 < ξ) (hK : 0 ≤ K)
    (poly : ∀ᶠ ℓ : ℕ in atTop, ∀ j : ℕ, 0 < j → x ℓ j ≤ (ℓ ^ A : ℕ))
    (hard : ∀ᶠ ℓ : ℕ in atTop, ∀ j : ℕ, 0 < j →
      (j : ℝ) ≤ (2 : ℝ) ^ ((ℓ : ℝ) ^ ξ) → (ℓ : ℝ) ^ δ ≤ x ℓ j)
    (compile : ∀ᶠ h : ℕ in atTop, let n := 2 ^ h; let L := Nat.log 2 h + 1
      ∀ ℓ j t : ℕ, 0 < ℓ → 0 < j → 0 < t → t ≤ 2 * n →
        (n : ℝ) ≤ (j * ℓ : ℕ) * x ℓ j →
        3 * (j * ℓ : ℕ) * x ℓ j ≤ (n ^ 4 : ℕ) →
        ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E]
          (M : OpenBitNetwork R (Fin t × RoutingBit h) V E), M.Trivalent →
          (∀ z, M.contraction z = ∏ i : Fin t,
            if TaggedPermutation (fun q => z (i, q)) then 1 else 0) →
          ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ^ (C * L ^ 2) ∧ x ℓ (j * d) ≤
            K * M.volume / (t * (3 * n * h) : ℕ) *
              (x ℓ j / (h : ℝ) ^ a + (L ^ C : ℕ) +
                (t * (3 * n * h) : ℕ) / (d * j * ℓ : ℕ))) :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 * 2 ^ h →
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E]
        (N : OpenBitNetwork R (Fin t × Fin (2 ^ (h + 1) * (2 * (h + 1)))) V E), N.Trivalent →
        (∀ z, N.contraction z = ∏ i : Fin t,
          if elementDistinctness (2 ^ (h + 1)) (2 * (h + 1)) (fun q => z (i, q)) then 1 else 0) →
        (h : ℝ) ^ a * (t * (3 * 2 ^ h * h) : ℕ) ≤ 4 * K * N.volume := by
  classical
  obtain ⟨b, hb⟩ := exists_nat_gt (max 2 (max ((a + ((C + 2 : ℕ) : ℝ)) / δ) (2 / ξ)))
  have hbpos : 0 < b := by
    have h := (le_max_left _ _).trans_lt hb
    exact_mod_cast (show (0 : ℝ) < b by linarith)
  have hab : a + ((C + 2 : ℕ) : ℝ) ≤ (b : ℝ) * δ := (div_le_iff₀ hδ).mp
    ((le_max_left _ _).trans ((le_max_right _ _).trans hb.le))
  have hξb : 2 ≤ (b : ℝ) * ξ := (div_le_iff₀ hξ).mp
    ((le_max_right _ _).trans ((le_max_right _ _).trans hb.le))
  have length : Tendsto (fun h : ℕ => h ^ b) atTop atTop := tendsto_pow_atTop hbpos.ne'
  filter_upwards [length.eventually poly, length.eventually hard, compile,
    eventual_replication_window C b A, Nat.eventually_mul_pow_le_pow 3 (b * (A + 1)) one_lt_two,
    eventually_ge_atTop 6] with h hp hhEnough hc hwindow hbudget hh
  intro t ht htN V E iV iE de N hN hED
  obtain ⟨M, _, hM, hvol, htag⟩ := exists_taggedPermutationNetwork N hN hED
  let n := 2 ^ h
  let ℓ := h ^ b
  let L := Nat.log 2 h + 1
  let D := 2 ^ (C * L ^ 2)
  have hn : 0 < n := Nat.two_pow_pos _
  have hℓ : 0 < ℓ := Nat.pow_pos (by lia)
  have hD : 0 < D := Nat.two_pow_pos _
  have he {j : ℕ} (lower : n ^ 2 ≤ j) (upper : j ≤ n ^ 3) : (ℓ : ℝ) ^ δ ≤ x ℓ j :=
    hhEnough j ((Nat.pow_pos hn).trans_le lower) (hard_range hh hξb upper)
  have one : 1 ≤ (ℓ : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hℓ) hδ.le
  have hs : x ℓ (n ^ 2) ≤ (ℓ ^ A : ℕ) := hp _ (Nat.pow_pos hn)
  have hnorm : 3 * ℓ * ℓ ^ A ≤ n := calc
    _ = 3 * h ^ (b * (A + 1)) := by dsimp [ℓ]; rw [pow_mul, pow_succ]; ring
    _ ≤ _ := hbudget
  apply le_trans _ (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hvol) (by positivity))
  apply BatchPrice.gain_mul_ports_le_four_mul_volume_of_compiler (x := x ℓ)
    (D := D) (rounds := (b * A + 1) * L) hn (by lia) ht htN hℓ
    (zero_lt_one.trans_le (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ h by lia)) ha.le))
    hK hwindow
  · exact hs.trans_lt (by exact_mod_cast initial_rounds h b A)
  · intro j lo hi
    exact (max_le one (absorb_boundary hh hbpos.ne' hab)).trans (he lo hi)
  · intro j hj hjD hcost
    have hjpos := (Nat.pow_pos hn).trans_le hj
    have hjmax : j ≤ n ^ 3 := (Nat.le_mul_of_pos_right _ hD).trans hjD
    have minBudget : (n : ℝ) ≤ (j * ℓ : ℕ) * x ℓ j := calc
      (n : ℝ) ≤ ((j * ℓ : ℕ) : ℝ) := by
        exact_mod_cast ((Nat.le_self_pow (by decide : 2 ≠ 0) n).trans hj).trans
          (Nat.le_mul_of_pos_right _ hℓ)
      _ ≤ _ := le_mul_of_one_le_right (Nat.cast_nonneg _) (one.trans (he hj hjmax))
    have maxBudget : 3 * (j * ℓ : ℕ) * x ℓ j ≤ (n ^ 4 : ℕ) := calc
      _ ≤ (3 : ℝ) * (j * ℓ : ℕ) * (ℓ ^ A : ℕ) :=
        mul_le_mul_of_nonneg_left (hcost.trans hs) (by positivity)
      _ ≤ _ := by
        exact_mod_cast calc
          3 * (j * ℓ) * ℓ ^ A = j * (3 * ℓ * ℓ ^ A) := by ring
          _ ≤ n ^ 3 * n := Nat.mul_le_mul hjmax hnorm
          _ = n ^ 4 := (pow_succ _ 3).symm
    exact @hc ℓ j t hℓ hjpos ht htN minBudget maxBudget V E iV iE de M hM htag

/-- The table of signed counts computed by a Boolean verifier. The last hidden bit requests
a negative contribution when set and a positive contribution otherwise. The other hidden
bits supply the padded nondeterministic choices. -/
@[expose] public noncomputable def signedVerifierTable (R : Type*) [CommRing R] {ℓ g : ℕ}
    (c : Circuit (fullSignature 2 Bool) (ℓ + (g + 1)) 1) (x : Fin ℓ → Bool) : R :=
  ∑ y : Fin (g + 1) → Bool, (if y (Fin.last g) then -1 else 1) *
    (if c.eval fullInterpretation (Sum.elim x y ∘ finSumFinEquiv.symm) 0 then 1 else 0)

private theorem exists_verifier_network (R : Type) [CommRing R] {ℓ g : ℕ}
    (c : Circuit (fullSignature 2 Bool) (ℓ + (g + 1)) 1) :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (N : OpenBitNetwork R (Fin ℓ) V E), N.Trivalent ∧
        N.volume ≤ 2 * (ℓ + (g + 1)) + 8 * c.size + 5 ∧
        ∀ x, N.contraction x = signedVerifierTable R c x := by
  classical
  obtain ⟨V, E, _, _, _, M, hM, hvol, hc⟩ :=
    Compiler.exists_trivalent_openBitNetwork c fullInterpretation R c.fanInAtMost_fullSignature
  let wt (i : Fin (g + 1)) (b : Bool) : R :=
    if i = Fin.last g then (if b then -1 else 1) else 1
  refine ⟨V, E, inferInstance, inferInstance, inferInstance, M.cap finSumFinEquiv wt,
    hM.cap _ _, (M.volume_cap_le _ _).trans hvol, fun x => ?_⟩
  rw [M.contraction_cap]
  unfold signedVerifierTable
  apply Finset.sum_congr (by ext y; simp)
  intro y _
  rw [hc]
  congr 1
  simp [wt]

private theorem verifier_size_bound {ℓ A s : ℕ} (hℓ : 2 ≤ ℓ) (hs : s ≤ ℓ ^ A) :
    2 * (ℓ + (ℓ ^ 100 + 1)) + 8 * s + 5 ≤ ℓ ^ (A + 105) := by
  let p := ℓ ^ (A + 100)
  have h1 : 1 ≤ p := Nat.one_le_pow _ _ (by lia)
  have hbase : ℓ ≤ p := Nat.le_self_pow (by lia : A + 100 ≠ 0) _
  have h100 : ℓ ^ 100 ≤ p := Nat.pow_le_pow_right (by lia) (by lia)
  have hsize : s ≤ p := hs.trans (Nat.pow_le_pow_right (by lia) (by lia))
  have h5 : 19 ≤ ℓ ^ 5 := (by decide : 19 ≤ 2 ^ 5).trans (Nat.pow_le_pow_left hℓ _)
  calc
    _ ≤ 19 * p := by lia
    _ ≤ ℓ ^ 5 * p := Nat.mul_le_mul_right _ h5
    _ = _ := by dsimp [p]; rw [← pow_add]; congr 1; lia

/-- The signed table of a verifier, replicated across all its allowed batches, has strictly
superlinear volume per copy. The bound permits internal wires between the copies. -/
@[expose] public def HasHardVerifierBatches (R : Type) [CommRing R]
    (ver : (ℓ : ℕ) → Circuit (fullSignature 2 Bool) (ℓ + (ℓ ^ 100 + 1)) 1)
    (δ ξ : ℝ) : Prop :=
  ∀ᶠ ℓ : ℕ in atTop, ∀ j : ℕ, 0 < j → (j : ℝ) ≤ (2 : ℝ) ^ ((ℓ : ℝ) ^ ξ) →
    ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E]
      (N : OpenBitNetwork R (Fin j × Fin ℓ) V E), N.Trivalent →
      (∀ z, N.contraction z =
        ∏ i : Fin j, signedVerifierTable R (ver ℓ) (fun k => z (i, k))) →
      (j : ℝ) * (ℓ : ℝ) ^ (1 + δ) < N.volume

private theorem amortize {p g s x d B L price y : ℝ} (hg : 0 < g) (hs : 0 < s) (hd : 0 < d)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hprice : 0 ≤ price)
    (hp : p ≤ 3 * s * x) (hy : y ≤ price * (d * (p / g + s * L) + B)) :
    y / (d * s) ≤ 3 * price * (x / g + L + B / (d * s)) := by
  apply (div_le_iff₀ (mul_pos hd hs)).mpr
  calc
    _ ≤ _ := hy
    _ ≤ price * (d * (3 * s * x / g + s * L) + B) := by gcongr
    _ ≤ price * (3 * (d * (s * x / g + s * L) + B)) := by
      apply mul_le_mul_of_nonneg_left _ hprice
      rw [show 3 * s * x / g = 3 * (s * x / g) by ring]
      nlinarith only [mul_nonneg hd.le (mul_nonneg hs.le hL), hB]
    _ = _ := by field_simp

open scoped Classical in
/-- Conditional transfer from hard signed verifier batches and the charged compiler to the
volume of every joint distinctness network. The one-copy signed network, disjoint upper
bound, minimizing networks and their normalization all arise inside the proof. -/
private theorem predecessor_volume
    (R : Type) [CommRing R]
    (ver : (ℓ : ℕ) → Circuit (fullSignature 2 Bool) (ℓ + (ℓ ^ 100 + 1)) 1)
    {a δ ξ K : ℝ} {A C : ℕ} (ha : 0 < a) (hδ : 0 < δ) (hξ : 0 < ξ) (hK : 0 ≤ K)
    (poly : ∀ᶠ ℓ : ℕ in atTop, (ver ℓ).size ≤ ℓ ^ A)
    (hard : HasHardVerifierBatches R ver δ ξ) (compile : HasChargedTaggedCompiler R a K C) :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 * 2 ^ h →
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E]
        (N : OpenBitNetwork R (Fin t × Fin (2 ^ (h + 1) * (2 * (h + 1)))) V E), N.Trivalent →
        (∀ z, N.contraction z = ∏ i : Fin t,
          if elementDistinctness (2 ^ (h + 1)) (2 * (h + 1)) (fun q => z (i, q)) then 1 else 0) →
        (h : ℝ) ^ a * (t * (3 * 2 ^ h * h) : ℕ) ≤ 4 * (3 * K) * N.volume := by
  classical
  let T (ℓ j : ℕ) (z : Fin j × Fin ℓ → Bool) :=
    ∏ i : Fin j, signedVerifierTable R (ver ℓ) (fun k => z (i, k))
  let μ (ℓ j : ℕ) := minTrivalentVolume (T ℓ j)
  let x (ℓ j : ℕ) : ℝ := μ ℓ j / (j * ℓ : ℕ)
  have realized (ℓ j : ℕ) : ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E)
      (_ : DecidableEq E) (N : OpenBitNetwork R (Fin j × Fin ℓ) V E), N.Trivalent ∧
      N.volume ≤ j * (2 * (ℓ + (ℓ ^ 100 + 1)) + 8 * (ver ℓ).size + 5) ∧
      ∀ z, N.contraction z = T ℓ j z := by
    obtain ⟨_, _, _, _, _, P, hp, hv, hc⟩ := exists_verifier_network R (ver ℓ)
    obtain ⟨V, E, _, _, _, Q, hq, hqv, hqc⟩ := OpenBitNetwork.exists_tensorPower P hp j
    exact ⟨V, E, inferInstance, inferInstance, inferInstance, Q, hq,
      hqv.trans (Nat.mul_le_mul_left j hv), fun z => by simp only [hqc, hc, T]⟩
  have opt (ℓ j : ℕ) : ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (N : OpenBitNetwork R (Fin j × Fin ℓ) V E), N.Trivalent ∧
      (∀ z, N.contraction z = T ℓ j z) ∧ N.volume = μ ℓ j := by
    obtain ⟨_, _, _, _, _, N, hN, _, hT⟩ := realized ℓ j
    exact exists_volume_eq_minTrivalentVolume _ N hN hT
  have hx {ℓ j : ℕ} (hℓ : 0 < ℓ) (hj : 0 < j) :
      ((j * ℓ : ℕ) : ℝ) * x ℓ j = μ ℓ j := by
    dsimp only [x]
    field_simp [show ((j * ℓ : ℕ) : ℝ) ≠ 0 by positivity]
  apply eventually_batch_volume_of_hard_workload_of_compiler R x (A := A + 105) (C := C)
    ha hδ hξ (by positivity : 0 ≤ 3 * K)
  · filter_upwards [poly, eventually_ge_atTop 2] with ℓ hpoly hℓ
    intro j hj
    obtain ⟨_, _, _, _, _, N, hN, hv, hc⟩ := realized ℓ j
    have hm : μ ℓ j ≤ j * ℓ ^ (A + 105) :=
      (minTrivalentVolume_le _ N hN hc).trans
        (hv.trans (Nat.mul_le_mul_left j (verifier_size_bound hℓ hpoly)))
    apply (div_le_iff₀ (by positivity : 0 < ((j * ℓ : ℕ) : ℝ))).mpr
    exact_mod_cast hm.trans (show j * ℓ ^ (A + 105) ≤ ℓ ^ (A + 105) * (j * ℓ) by
      calc _ ≤ j * ℓ ^ (A + 105) * ℓ := Nat.le_mul_of_pos_right _ (by lia)
           _ = _ := by ring)
  · filter_upwards [hard, eventually_ge_atTop 1] with ℓ hhard hℓ
    intro j hj hjmax
    obtain ⟨V, E, _, _, _, N, hN, hc, hv⟩ := opt ℓ j
    have hl := @hhard j hj hjmax V E _ _ _ N hN hc
    rw [hv, Real.rpow_add (by positivity), Real.rpow_one] at hl
    apply (le_of_mul_le_mul_left · (by positivity : 0 < ((j * ℓ : ℕ) : ℝ)))
    rw [hx hℓ hj, Nat.cast_mul]
    linarith only [hl]
  · filter_upwards [compile, eventually_ge_atTop 1] with h hcomp hh
    dsimp only at hcomp ⊢
    intro ℓ j t hℓ hj ht htmax hmin hmax W F iW iF dF M hM htag
    obtain ⟨V, E, _, _, _, P, hP, hT, hpv⟩ := opt ℓ j
    obtain ⟨S, hS, hsv, hSC⟩ := P.exists_normalized hP
    have hST : ∀ z, S.contraction z = T ℓ j z := fun z => (hSC z).trans (hT z)
    have lower : 2 ^ h ≤ S.volume := by
      apply le_trans _ (minTrivalentVolume_le _ S hS.trivalent hST)
      change 2 ^ h ≤ μ ℓ j
      exact_mod_cast (show (2 ^ h : ℕ) ≤ (μ ℓ j : ℝ) by rw [← hx hℓ hj]; exact hmin)
    have upper : S.volume ≤ (2 ^ h) ^ 4 := by
      apply hsv.trans
      rw [hpv]
      have he : 3 * (μ ℓ j : ℝ) ≤ ((2 ^ h) ^ 4 : ℕ) := by
        rw [← hx hℓ hj]
        linarith only [hmax]
      exact_mod_cast he
    obtain ⟨d, hd, hdmax, V', E', _, _, _, Q, hQ, hQC, hqv⟩ :=
      @hcomp t ht htmax _ _ _ _ _ _ _ _ S hS lower upper W F iW iF dF M hM htag
    refine ⟨d, hd, hdmax, ?_⟩
    let e : Fin (j * d) × Fin ℓ ≃ Fin d × (Fin j × Fin ℓ) :=
      (Equiv.prodCongr (finProdFinEquiv.symm.trans (Equiv.prodComm _ _)) (Equiv.refl _)).trans
        (Equiv.prodAssoc _ _ _)
    obtain ⟨Q', _, _, hQ', hv', hc'⟩ := Q.exists_pin hQ e.toEmbedding (fun _ => false)
    have out : ∀ z, Q'.contraction z = T ℓ (j * d) z := by
      intro z
      rw [hc', hQC]
      simp only [hST, T]
      rw [← Fintype.prod_prod_type']
      refine Fintype.prod_equiv (M := R)
        ((Equiv.prodComm (Fin d) (Fin j)).trans finProdFinEquiv) _ _ fun p => ?_
      apply congrArg (signedVerifierTable R (ver ℓ))
      funext i
      have he : e (finProdFinEquiv (p.2, p.1), i) = (p.1, p.2, i) := by simp [e]
      rw [← he]
      exact e.injective.extend_apply z (fun _ => false) _
    have hm : μ ℓ (j * d) ≤ Q.volume := (minTrivalentVolume_le _ Q' hQ' out).trans hv'
    simp only [Fintype.card_prod, Fintype.card_fin] at hqv
    have hs : (S.volume : ℝ) ≤ 3 * ((j * ℓ : ℕ) : ℝ) * x ℓ j := by
      rw [mul_assoc, hx hℓ hj, ← hpv]
      exact_mod_cast hsv
    have he := amortize (show 0 < (h : ℝ) ^ a by positivity)
      (show 0 < ((j * ℓ : ℕ) : ℝ) by positivity) (show 0 < (d : ℝ) by positivity)
      (show 0 ≤ ((t * (3 * 2 ^ h * h) : ℕ) : ℝ) by positivity)
      (show 0 ≤ (((Nat.log 2 h + 1) ^ C : ℕ) : ℝ) by positivity)
      (show 0 ≤ K * M.volume / (t * (3 * 2 ^ h * h) : ℕ) by positivity)
      hs ((Nat.cast_le.mpr hm).trans hqv)
    have hjd : ((j * d * ℓ : ℕ) : ℝ) = (d : ℝ) * (j * ℓ : ℕ) := by push_cast; ring
    have hdj : ((d * j * ℓ : ℕ) : ℝ) = (d : ℝ) * (j * ℓ : ℕ) := by push_cast; ring
    dsimp only [x]
    rw [hjd, hdj]
    convert he using 1; ring

private theorem rescale {a K v : ℝ} {h t : ℕ} (ha : 0 ≤ a) (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hh : 1 ≤ h) (cost : (h : ℝ) ^ a * (t * (3 * 2 ^ h * h) : ℕ) ≤ 4 * (3 * K) * v) :
    1 / (32 * (K + 1) * (2 : ℝ) ^ a) * (t * (2 ^ (h + 1) * (2 * (h + 1))) : ℕ) *
      ((h + 1 : ℕ) : ℝ) ^ a ≤ v := by
  have hp : 0 < (2 : ℝ) ^ a := by positivity
  have hg : ((h + 1 : ℕ) : ℝ) ^ a ≤ (2 : ℝ) ^ a * (h : ℝ) ^ a := calc
    _ ≤ (2 * (h : ℝ)) ^ a := Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show h + 1 ≤ 2 * h by lia)) ha
    _ = _ := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
  have hw : t * (2 ^ (h + 1) * (2 * (h + 1))) ≤ 8 * (t * 2 ^ h * h) := by
    have hd := Nat.mul_le_mul_left (t * 2 ^ h) (show h + 1 ≤ 2 * h by lia)
    rw [pow_succ]
    nlinarith only [hd]
  have hc : (t * 2 ^ h * h : ℕ) * (h : ℝ) ^ a ≤ 4 * (K + 1) * v := by
    push_cast at cost ⊢
    nlinarith only [cost, hv]
  have htop : (t * (2 ^ (h + 1) * (2 * (h + 1))) : ℕ) * (((h + 1 : ℕ) : ℝ) ^ a) ≤
      (32 * (K + 1) * (2 : ℝ) ^ a) * v := calc
    _ ≤ ((8 * (t * 2 ^ h * h) : ℕ) : ℝ) * ((2 : ℝ) ^ a * (h : ℝ) ^ a) :=
      mul_le_mul (Nat.cast_le.mpr hw) hg (by positivity) (by positivity)
    _ = (8 * (2 : ℝ) ^ a) * ((t * 2 ^ h * h : ℕ) * (h : ℝ) ^ a) := by
      push_cast
      ring
    _ ≤ (8 * (2 : ℝ) ^ a) * (4 * (K + 1) * v) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring
  have hpos : 0 < 32 * (K + 1) * (2 : ℝ) ^ a := by positivity
  rw [mul_comm _ v] at htop
  simpa only [div_mul_eq_mul_div, one_mul] using (div_le_iff₀ hpos).mpr htop

open scoped Classical in
/-- Conditional transfer from a polynomial-size signed verifier with hard batches and an exact
tagged-permutation compiler. If the compiler saves
a factor `h ^ a`, every joint network for at most `2 ^ w` element-distinctness tests costs
a factor `Ω(w ^ a)` per exterior bit for all sufficiently large widths `w`. -/
public theorem eventually_batch_volume_of_hard_verifier_of_compiler
    (R : Type) [CommRing R]
    (ver : (ℓ : ℕ) → Circuit (fullSignature 2 Bool) (ℓ + (ℓ ^ 100 + 1)) 1)
    {a δ ξ K : ℝ} {A C : ℕ} (ha : 0 < a) (hδ : 0 < δ) (hξ : 0 < ξ) (hK : 0 ≤ K)
    (poly : ∀ᶠ ℓ : ℕ in atTop, (ver ℓ).size ≤ ℓ ^ A)
    (hard : HasHardVerifierBatches R ver δ ξ) (compile : HasExactTaggedCompiler R a K C) :
    ∀ᶠ w : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 ^ w →
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E]
        (N : OpenBitNetwork R (Fin t × Fin (2 ^ w * (2 * w))) V E), N.Trivalent →
        (∀ z, N.contraction z = ∏ i : Fin t,
          if elementDistinctness (2 ^ w) (2 * w) (fun q => z (i, q)) then 1 else 0) →
        1 / (32 * (3 * K + 2) * (2 : ℝ) ^ a) * (t * (2 ^ w * (2 * w)) : ℕ) *
          (w : ℝ) ^ a ≤ N.volume := by
  have hk : 0 ≤ 3 * K + 1 := by positivity
  have raw := predecessor_volume R ver ha hδ hξ hk poly hard (compile.charged hK)
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually raw, eventually_ge_atTop 2] with w lower hw
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : w ≠ 0)
  simp only [Nat.succ_sub_one] at lower
  intro t ht htmax V E _ _ _ N hN hc
  rw [show 3 * K + 2 = 3 * K + 1 + 1 by ring]
  exact rescale ha.le hk (Nat.cast_nonneg _) (by lia)
    (lower t ht (by rwa [pow_succ, Nat.mul_comm] at htmax) V E N hN hc)

end Cslib.Circuits.Boolean.ElementDistinctness
