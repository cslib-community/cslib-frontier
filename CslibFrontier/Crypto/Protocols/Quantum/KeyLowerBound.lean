/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Quantum.OneTimePad
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Holevo
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF.ToReal

/-!
# The `2n`-bit key lower bound for private quantum channels

[Ambainis, Mosca, Tapp, and de Wolf][AmbainisMoscaTappdeWolf2000] prove that the `2n`-bit quantum
one-time pad (`Cslib.Crypto.Protocols.Quantum.OneTimePad`) is optimal: any **private quantum
channel** (PQC, Definition 3.1) that hides every `n`-qubit state—even if restricted to unentangled
product states, and even when encryption may append an arbitrary finite ancilla in a fixed mixed
state `ρa` before applying key-dependent unitaries `U k`—requires at least `2n` bits of Shannon key
entropy (`two_mul_card_le_entropy_of_unentangled`, Corollary 5.4;
`two_mul_card_le_entropy_of_pureStates`, Corollary 5.5) and hence at least `4ⁿ` keys in the key
support (`four_pow_card_le_of_unentangled`).

The proof follows Section 5 and Appendix A of
[Ambainis, Mosca, Tapp, and de Wolf][AmbainisMoscaTappdeWolf2000]:
1. **Quantum Shannon bound for classical basis messages** (`logb_card_le_entropy_of_basis`,
   Theorem 5.3): if a PQC with ancilla `ρa` maps every computational-basis state `|x⟩⟨x|` on `ℂ^ι`
   to the same state `ρ₀`, then `S(ρ₀) ≤ H(p) + S(ρa)` (by `holevoInformation_le_entropy` applied
   to a single basis input) while `log₂ |ι| + S(ρa) ≤ S(ρ₀)` (by `holevoInformation_nonneg` applied
   to the maximally mixed input), giving `log₂ |ι| ≤ H(p)`.
2. **Off-diagonal annihilation on product states** (`encryptAvg_single_eq_zero_of_ne`, Lemma 4.4):
   by strong induction on the Hamming distance `d` between `x ≠ y` in `α → Bool` and discrete
   Fourier cancellation over `2^d` single-qubit phase combinations, hiding all unentangled `n`-qubit
   states forces `encryptAvg p U ρa (|x⟩⟨y|) = 0` for `x ≠ y`.
3. **Bell-basis / superdense reduction** (`exists_basis_pqc_of_unentangled`, Theorem 5.2): encoding
   `(a, b) ∈ (α → Bool) × (α → Bool)` into the generalized Bell state `(X^a Z^b ⊗ 1) |Φ⟩` and
   encrypting only the second `n`-qubit register with `(p, U, ρa)` maps every basis pair `(a, b)`
   to `(1 / 2ⁿ) ⊗ ρ₀` by step 2, yielding a classical-basis PQC on `4ⁿ` basis states with the same
   key distribution `p`. Applying step 1 gives `2n ≤ H(p)`.

## Main definitions

* `Cslib.Crypto.Protocols.Quantum.encryptAvg`: key-averaged unitary encryption with ancilla `ρa`.
* `Cslib.Crypto.Protocols.Quantum.IsPrivateQuantumChannel`: AMTW Definition 3.1.
* `Cslib.Crypto.Protocols.Quantum.unentangledPureStates`: `n`-qubit product unit states `ℋ₂^{⊗ n}`.

## Main results

* `Cslib.Crypto.Protocols.Quantum.logb_card_le_entropy_of_basis`: AMTW Theorem 5.3
  (`log₂ |ι| ≤ H(p)`).
* `Cslib.Crypto.Protocols.Quantum.encryptAvg_single_eq_zero_of_ne`: AMTW Lemma 4.4.
* `Cslib.Crypto.Protocols.Quantum.exists_basis_pqc_of_unentangled`: AMTW Theorem 5.2.
* `Cslib.Crypto.Protocols.Quantum.two_mul_card_le_entropy_of_unentangled`,
  `Cslib.Crypto.Protocols.Quantum.four_pow_card_le_of_unentangled`: AMTW Corollary 5.4 (`2n ≤ H(p)`
  and `4ⁿ ≤ |supp(p)|` for unentangled `n`-qubit states with arbitrary ancilla).
* `Cslib.Crypto.Protocols.Quantum.two_mul_card_le_entropy_of_pureStates`,
  `Cslib.Crypto.Protocols.Quantum.two_mul_card_le_entropy_noAncilla`: AMTW Corollary 5.5 and
  Theorem 5.1 (`2n ≤ H(p)` for general `n`-qubit states, with or without ancilla).

## References

* [A. Ambainis, M. Mosca, A. Tapp, R. de Wolf, *Private Quantum
  Channels*][AmbainisMoscaTappdeWolf2000], Definition 3.1, Lemma 4.4, Theorems 5.1–5.3,
  Corollaries 5.4–5.5.
-/

public section

namespace Cslib.Crypto.Protocols.Quantum

open Matrix Finset Cslib.Quantum Cslib.BitString
open Cslib.Probability.PMF
open scoped ComplexOrder Kronecker

private theorem sum_kronecker {ι₁ ι₂ κ₁ κ₂ β : Type*} (s : Finset β)
    (f : β → Matrix ι₁ ι₂ ℂ) (B : Matrix κ₁ κ₂ ℂ) :
    (∑ x ∈ s, f x) ⊗ₖ B = ∑ x ∈ s, f x ⊗ₖ B := by
  ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩; simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]

section GeneralRegister

variable {K ι κ : Type*} [Fintype K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The key-averaged encryption map `M ↦ ∑_k p(k) U_k (M ⊗ ρa) U_kᴴ` of a private quantum channel
with key distribution `p`, encryption unitaries `U`, and ancilla state `ρa`
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Definition 3.1). -/
@[expose] noncomputable def encryptAvg (p : PMF K) (U : K → unitaryGroup (ι × κ) ℂ)
    (ρa : Matrix κ κ ℂ) (M : Matrix ι ι ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  ∑ k, (p k).toReal •
    ((U k : Matrix (ι × κ) (ι × κ) ℂ) * (M ⊗ₖ ρa) * (U k : Matrix (ι × κ) (ι × κ) ℂ)ᴴ)

/-- A **Private Quantum Channel** (PQC) hiding a set `S` of pure states on `ℂ^ι` using key
distribution `p : PMF K`, encryption unitaries `U : K → unitaryGroup (ι × κ) ℂ`, ancilla density
matrix `ρa`, and eavesdropper state `ρ₀`
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Definition 3.1, generalized from
`Fin N` keys and qubit spaces to arbitrary finite key and register types). -/
structure IsPrivateQuantumChannel (S : Set (EuclideanSpace ℂ ι)) (p : PMF K)
    (U : K → unitaryGroup (ι × κ) ℂ) (ρa : Matrix κ κ ℂ)
    (ρ₀ : Matrix (ι × κ) (ι × κ) ℂ) : Prop where
  /-- The ancilla register is initialized to a valid density matrix. -/
  ancilla_density : IsDensityMatrix ρa
  /-- Every pure state in `S` maps to the same key-averaged ciphertext state `ρ₀`. -/
  encryptAvg_eq : ∀ ψ ∈ S, encryptAvg p U ρa (pureState ψ) = ρ₀

/-- Restricting the plaintext set preserves the private-quantum-channel property. -/
theorem IsPrivateQuantumChannel.mono {S T : Set (EuclideanSpace ℂ ι)} (hST : S ⊆ T)
    {p : PMF K} {U : K → unitaryGroup (ι × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix (ι × κ) (ι × κ) ℂ} (h : IsPrivateQuantumChannel T p U ρa ρ₀) :
    IsPrivateQuantumChannel S p U ρa ρ₀ :=
  ⟨h.ancilla_density, fun ψ hψ => h.encryptAvg_eq ψ (hST hψ)⟩

private theorem encryptAvg_zero (p : PMF K) (U : K → unitaryGroup (ι × κ) ℂ)
    (ρa : Matrix κ κ ℂ) : encryptAvg p U ρa 0 = 0 := by
  simp [encryptAvg]

private theorem encryptAvg_add (p : PMF K) (U : K → unitaryGroup (ι × κ) ℂ)
    (ρa : Matrix κ κ ℂ) (A B : Matrix ι ι ℂ) :
    encryptAvg p U ρa (A + B) = encryptAvg p U ρa A + encryptAvg p U ρa B := by
  simp only [encryptAvg, add_kronecker, Matrix.mul_add, Matrix.add_mul, smul_add,
    Finset.sum_add_distrib]

private theorem encryptAvg_smul (p : PMF K) (U : K → unitaryGroup (ι × κ) ℂ)
    (ρa : Matrix κ κ ℂ) (c : ℂ) (A : Matrix ι ι ℂ) :
    encryptAvg p U ρa (c • A) = c • encryptAvg p U ρa A := by
  rw [encryptAvg, encryptAvg, Finset.smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [smul_kronecker, Matrix.mul_smul, Matrix.smul_mul, smul_comm]

private theorem encryptAvg_sum {β : Type*} (p : PMF K) (U : K → unitaryGroup (ι × κ) ℂ)
    (ρa : Matrix κ κ ℂ) (s : Finset β) (f : β → Matrix ι ι ℂ) :
    encryptAvg p U ρa (∑ b ∈ s, f b) = ∑ b ∈ s, encryptAvg p U ρa (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [encryptAvg_zero]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, encryptAvg_add, ih]

/-- **Quantum Shannon lower bound for classical basis messages**
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Theorem 5.3): any private quantum
channel (with arbitrary ancilla `ρa`) that hides all computational-basis states `{|x⟩ | x : ι}` of
a nonempty register `ℂ^ι` requires Shannon key entropy `log₂ |ι| ≤ H(p)`. -/
theorem logb_card_le_entropy_of_basis [Nonempty ι]
    {p : PMF K} {U : K → unitaryGroup (ι × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix (ι × κ) (ι × κ) ℂ}
    (h : IsPrivateQuantumChannel (Set.range (ket (ι := ι))) p U ρa ρ₀) :
    Real.logb 2 (Fintype.card ι) ≤ entropy p := by
  let x₀ : ι := Classical.arbitrary ι
  have hx₀ : encryptAvg p U ρa (pureState (ket x₀)) = ρ₀ :=
    h.encryptAvg_eq (ket x₀) ⟨x₀, rfl⟩
  let σ₁ (k : K) : Matrix (ι × κ) (ι × κ) ℂ :=
    (U k : Matrix (ι × κ) (ι × κ) ℂ) * (pureState (ket x₀) ⊗ₖ ρa) *
      (U k : Matrix (ι × κ) (ι × κ) ℂ)ᴴ
  have hket_dens : IsDensityMatrix (pureState (ket x₀)) :=
    isDensityMatrix_pureState (norm_ket x₀)
  have hprod₁ : IsDensityMatrix (pureState (ket x₀) ⊗ₖ ρa) := by
    refine ⟨hket_dens.posSemidef.kronecker h.ancilla_density.posSemidef, ?_⟩
    rw [trace_kronecker, hket_dens.trace_eq_one, h.ancilla_density.trace_eq_one, mul_one]
  have hσ₁ (k : K) : IsDensityMatrix (σ₁ k) := hprod₁.conj_unitary (U k).2
  have hσ₁_S (k : K) : vonNeumannEntropy (σ₁ k) = vonNeumannEntropy ρa := by
    have hU : (U k : Matrix (ι × κ) (ι × κ) ℂ)ᴴ * (U k : Matrix (ι × κ) (ι × κ) ℂ) = 1 :=
      (mem_unitaryGroup_iff').mp (U k).2
    rw [vonNeumannEntropy_conj_isometry hU hprod₁.posSemidef.isHermitian,
      vonNeumannEntropy_kronecker hket_dens h.ancilla_density,
      vonNeumannEntropy_pureState (norm_ket x₀), zero_add]
  have hupper : vonNeumannEntropy ρ₀ - vonNeumannEntropy ρa ≤ entropy p := by
    have hle := holevoInformation_le_entropy p hσ₁
    rw [holevoInformation, show ∑ k, (p k).toReal • σ₁ k = ρ₀ from hx₀] at hle
    simp_rw [hσ₁_S, ← Finset.sum_mul, sum_toReal p, one_mul] at hle
    exact hle
  let π : Matrix ι ι ℂ := (Fintype.card ι : ℂ)⁻¹ • 1
  have hπ_dens : IsDensityMatrix π := by
    constructor
    · rw [show π = (Fintype.card ι : ℝ)⁻¹ • (1 : Matrix ι ι ℂ) by ext i j; simp [π]]
      exact PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
    · simp [π, trace_smul, trace_one]
  have hone_sum : (1 : Matrix ι ι ℂ) = ∑ x : ι, pureState (ket x) := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Finset.sum_eq_single i]
      · simp [pureState_apply]
      · intro x _ hx; simp [pureState_apply, Ne.symm hx]
      · simp
    · rw [Matrix.one_apply_ne hij]
      refine (Finset.sum_eq_zero fun x _ => ?_).symm
      by_cases hix : i = x
      · subst hix; simp [pureState_apply, Ne.symm hij]
      · simp [pureState_apply, hix]
  have hπ_avg : encryptAvg p U ρa π = ρ₀ := by
    have hcard_ne : (Fintype.card ι : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    dsimp only [π]
    rw [hone_sum, encryptAvg_smul, encryptAvg_sum]
    have hall (x : ι) : encryptAvg p U ρa (pureState (ket x)) = ρ₀ :=
      h.encryptAvg_eq (ket x) ⟨x, rfl⟩
    simp_rw [hall]
    ext p₁ p₂
    rw [Matrix.smul_apply, Matrix.sum_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      smul_eq_mul, inv_mul_cancel_left₀ hcard_ne]
  let σ₂ (k : K) : Matrix (ι × κ) (ι × κ) ℂ :=
    (U k : Matrix (ι × κ) (ι × κ) ℂ) * (π ⊗ₖ ρa) * (U k : Matrix (ι × κ) (ι × κ) ℂ)ᴴ
  have hprod₂ : IsDensityMatrix (π ⊗ₖ ρa) := by
    refine ⟨hπ_dens.posSemidef.kronecker h.ancilla_density.posSemidef, ?_⟩
    rw [trace_kronecker, hπ_dens.trace_eq_one, h.ancilla_density.trace_eq_one, mul_one]
  have hσ₂ (k : K) : IsDensityMatrix (σ₂ k) := hprod₂.conj_unitary (U k).2
  have hσ₂_S (k : K) :
      vonNeumannEntropy (σ₂ k) = Real.logb 2 (Fintype.card ι) + vonNeumannEntropy ρa := by
    have hU : (U k : Matrix (ι × κ) (ι × κ) ℂ)ᴴ * (U k : Matrix (ι × κ) (ι × κ) ℂ) = 1 :=
      (mem_unitaryGroup_iff').mp (U k).2
    rw [vonNeumannEntropy_conj_isometry hU hprod₂.posSemidef.isHermitian,
      vonNeumannEntropy_kronecker hπ_dens h.ancilla_density, vonNeumannEntropy_maximallyMixed]
  have hlower : Real.logb 2 (Fintype.card ι) + vonNeumannEntropy ρa ≤ vonNeumannEntropy ρ₀ := by
    have hnn := holevoInformation_nonneg p hσ₂
    rw [holevoInformation, show ∑ k, (p k).toReal • σ₂ k = ρ₀ from hπ_avg] at hnn
    simp_rw [hσ₂_S, ← Finset.sum_mul, sum_toReal p, one_mul] at hnn
    linarith
  linarith

end GeneralRegister

/-! ### Unentangled `n`-qubit states and the `2n`-bit lower bound -/

section Qubits

variable {K α κ : Type*} [Fintype K] [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

/-- The set `ℋ₂^{⊗ n}` of unentangled `n`-qubit pure states (`n = |α|`): unit vectors on
`ℂ^{α → Bool}` whose amplitudes factor as `∏ i, φ_i(u_i)` for single-qubit unit vectors `φ_i`
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Section 4 and Corollary 5.4). -/
def unentangledPureStates (α : Type*) [Fintype α] : Set (EuclideanSpace ℂ (α → Bool)) :=
  {ψ | ∃ φ : α → EuclideanSpace ℂ Bool,
    (∀ i, ‖φ i‖ = 1) ∧ ∀ u, ψ.ofLp u = ∏ i, (φ i).ofLp (u i)}

omit [DecidableEq α] in
@[simp]
theorem mem_unentangledPureStates (ψ : EuclideanSpace ℂ (α → Bool)) :
    ψ ∈ unentangledPureStates α ↔
      ∃ φ : α → EuclideanSpace ℂ Bool,
        (∀ i, ‖φ i‖ = 1) ∧ ∀ u, ψ.ofLp u = ∏ i, (φ i).ofLp (u i) := by
  rfl

/-- Every unentangled product state has unit Euclidean norm. -/
theorem norm_eq_one_of_mem_unentangledPureStates {ψ : EuclideanSpace ℂ (α → Bool)}
    (hψ : ψ ∈ unentangledPureStates α) : ‖ψ‖ = 1 := by
  obtain ⟨φ, hφ_norm, hφ_eq⟩ := hψ
  have hsq : ‖ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm (u : α → Bool) : ‖ψ.ofLp u‖ ^ 2 = ∏ i : α, ‖(φ i).ofLp (u i)‖ ^ 2 := by
      rw [hφ_eq u, norm_prod, Finset.prod_pow]
    simp_rw [hterm]
    rw [← Fintype.prod_sum (fun i b => ‖(φ i).ofLp b‖ ^ 2)]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← EuclideanSpace.norm_sq_eq, hφ_norm i, one_pow]
  nlinarith [norm_nonneg ψ]

omit [DecidableEq α] in
/-- Computational-basis states are unentangled product states. -/
theorem ket_mem_unentangledPureStates (x : α → Bool) :
    ket x ∈ unentangledPureStates α := by
  refine ⟨fun i => ket (x i), fun i => norm_ket (x i), fun u => ?_⟩
  by_cases hux : u = x
  · subst hux
    simp [ket_apply]
  · have hex : ∃ i, u i ≠ x i := by
      by_contra hall
      push Not at hall
      exact hux (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    simp only [ket_apply, hux, ite_false]
    exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])).symm

/-- **Off-diagonal annihilation** ([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000],
Lemma 4.4): if a private quantum channel hides every unentangled `n`-qubit pure state, then it
annihilates every off-diagonal computational-basis unit `|x⟩⟨y|` (`x ≠ y`). -/
theorem encryptAvg_single_eq_zero_of_ne {p : PMF K}
    {U : K → unitaryGroup ((α → Bool) × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix ((α → Bool) × κ) ((α → Bool) × κ) ℂ}
    (h : IsPrivateQuantumChannel (unentangledPureStates α) p U ρa ρ₀)
    {x y : α → Bool} (hxy : x ≠ y) :
    encryptAvg p U ρa (single x y 1) = 0 := by
  have hdiag (z : α → Bool) : encryptAvg p U ρa (single z z 1) = ρ₀ := by
    have hpure : pureState (ket z) = single z z (1 : ℂ) := by
      ext u u'
      by_cases hu : u = z <;> by_cases hu' : u' = z <;>
        simp [pureState_apply, hu, hu', Ne.symm]
    rw [← hpure]
    exact h.encryptAvg_eq (ket z) (ket_mem_unentangledPureStates z)
  have main : ∀ d : ℕ, ∀ x y : α → Bool, x ≠ y →
      (univ.filter fun i => x i ≠ y i).card = d →
        encryptAvg p U ρa (single x y 1) = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro x y hxy hd
      let D : Finset α := univ.filter fun i => x i ≠ y i
      have hD_card : D.card = d := hd
      let embed (w : ↥D → Bool) : α → Bool :=
        fun i => if hi : i ∈ D then (if w ⟨i, hi⟩ then y i else x i) else x i
      let flip (w : ↥D → Bool) : ↥D → Bool := fun j => !w j
      have hembed_inj : Function.Injective embed := by
        intro w₁ w₂ hw
        funext ⟨i, hi⟩
        have hxy_i : x i ≠ y i := (Finset.mem_filter.mp hi).2
        have hi_eq := congrFun hw i
        simp only [embed, hi, ↓reduceDIte] at hi_eq
        cases hw₁ : w₁ ⟨i, hi⟩ <;> cases hw₂ : w₂ ⟨i, hi⟩ <;>
          simp only [hw₁, hw₂, Bool.false_eq_true, ↓reduceIte] at hi_eq
        · rfl
        · exact absurd hi_eq hxy_i
        · exact absurd hi_eq.symm hxy_i
        · rfl
      have hembed_zero : embed (fun _ => false) = x := by
        funext i; simp [embed]
      have hembed_flip_zero : embed (flip (fun _ => false)) = y := by
        funext i
        dsimp only [embed, flip]
        by_cases hi : i ∈ D
        · simp [hi]
        · have heq : x i = y i := by
            by_contra hne
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
          simp [hi, heq]
      have hphase_eq (v : ↥D → Bool) :
          ∑ w : ↥D → Bool,
            (∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1) •
              encryptAvg p U ρa (single (embed w) (embed (flip w)) 1) = 0 := by
        let φ (i : α) : EuclideanSpace ℂ Bool :=
          if hi : i ∈ D then
            (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
              (ket (x i) + (if v ⟨i, hi⟩ then Complex.I else 1) • ket (y i))
          else ket (x i)
        have hφ_norm (i : α) : ‖φ i‖ = 1 := by
          by_cases hi : i ∈ D
          · simp only [φ, hi, ↓reduceDIte]
            have hne_i : x i ≠ y i := (Finset.mem_filter.mp hi).2
            let z : EuclideanSpace ℂ Bool :=
              (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
                (ket (x i) + (if v ⟨i, hi⟩ then Complex.I else 1) • ket (y i))
            have hsq : ‖z‖ ^ 2 = 1 := by
              dsimp only [z]
              rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
                Real.sq_sqrt (by norm_num), EuclideanSpace.norm_sq_eq, Fintype.sum_bool]
              cases hxi : x i <;> cases hyi : y i
              · exact absurd (hxi.trans hyi.symm) hne_i
              · rcases Bool.eq_false_or_eq_true (v ⟨i, hi⟩) with hv | hv <;>
                  simp [hv] <;> norm_num
              · rcases Bool.eq_false_or_eq_true (v ⟨i, hi⟩) with hv | hv <;>
                  simp [hv] <;> norm_num
              · exact absurd (hxi.trans hyi.symm) hne_i
            exact (sq_eq_one_iff.mp hsq).resolve_right (by linarith [norm_nonneg z])
          · simp only [φ, hi, ↓reduceDIte]
            exact norm_ket (x i)
        let Ψ : EuclideanSpace ℂ (α → Bool) :=
          WithLp.toLp 2 fun u => ∏ i : α, (φ i).ofLp (u i)
        have hΨ_mem : Ψ ∈ unentangledPureStates α := ⟨φ, hφ_norm, fun _ => rfl⟩
        have hΨ_support (u : α → Bool) (hu : ¬ ∀ i, i ∉ D → u i = x i) :
            Ψ.ofLp u = 0 := by
          push Not at hu
          obtain ⟨i, hiD, hui⟩ := hu
          refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
          dsimp only [φ]
          simp [hiD, hui]
        have hΨ_range (u : α → Bool) (hu : ∀ i, i ∉ D → u i = x i) :
            ∃ w : ↥D → Bool, embed w = u := by
          refine ⟨fun j => decide (u j.1 ≠ x j.1), ?_⟩
          funext i
          by_cases hi : i ∈ D
          · simp only [embed, hi, ↓reduceDIte]
            have hxy_i : x i ≠ y i := (Finset.mem_filter.mp hi).2
            by_cases hux : u i = x i
            · simp [hux]
            · simp only [decide_eq_true_eq.mpr hux, ↓reduceIte]
              cases hx : x i <;> cases hy : y i <;> cases hu_i : u i <;> simp_all
          · simp only [embed, hi, ↓reduceDIte, hu i hi]
        have hΨ_embed (w : ↥D → Bool) :
            Ψ.ofLp (embed w) =
              (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ d *
                ∏ j : ↥D, (if w j && v j then Complex.I else 1) := by
          change (∏ i : α, (φ i).ofLp (embed w i)) = _
          rw [← Finset.prod_subset (Finset.subset_univ D)]
          · rw [← Finset.prod_coe_sort D (fun i => (φ i).ofLp (embed w i))]
            have hfactor (j : ↥D) :
                (φ j.1).ofLp (embed w j.1) =
                  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if w j && v j then Complex.I else 1) := by
              have hxy_j : x j.1 ≠ y j.1 := (Finset.mem_filter.mp j.2).2
              simp only [φ, embed, j.2, ↓reduceDIte]
              rcases Bool.eq_false_or_eq_true (w j) with hwj | hwj <;>
                rcases Bool.eq_false_or_eq_true (v j) with hvj | hvj <;>
                simp [hwj, hvj, ket_apply, hxy_j, Ne.symm hxy_j]
            simp_rw [hfactor]
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
              hD_card]
          · intro i _ hiD
            dsimp only [φ, embed]
            simp [hiD]
        have hpure_sum :
            pureState Ψ =
              ∑ w : ↥D → Bool, ∑ w' : ↥D → Bool,
                (Ψ.ofLp (embed w) * star (Ψ.ofLp (embed w'))) •
                  single (embed w) (embed w') (1 : ℂ) := by
          ext u u'
          rw [pureState_apply, Matrix.sum_apply]
          simp only [Matrix.sum_apply, Matrix.smul_apply, single_apply, smul_eq_mul, mul_ite,
            mul_one, mul_zero]
          by_cases hu : ∀ i, i ∉ D → u i = x i
          · by_cases hu' : ∀ i, i ∉ D → u' i = x i
            · obtain ⟨w, rfl⟩ := hΨ_range u hu
              obtain ⟨w', rfl⟩ := hΨ_range u' hu'
              rw [Finset.sum_eq_single w]
              · rw [Finset.sum_eq_single w']
                · simp
                · intro w₂ _ hw₂
                  have hne : embed w₂ ≠ embed w' := fun he => hw₂ (hembed_inj he)
                  simp [hne]
                · simp
              · intro w₁ _ hw₁
                refine Finset.sum_eq_zero fun w₂ _ => ?_
                have hne : embed w₁ ≠ embed w := fun he => hw₁ (hembed_inj he)
                simp [hne]
              · simp
            · rw [hΨ_support u' hu', star_zero, mul_zero]
              refine (Finset.sum_eq_zero fun w₁ _ => Finset.sum_eq_zero fun w₂ _ => ?_).symm
              have hne : embed w₂ ≠ u' := by
                intro he; subst he
                exact hu' fun i hi => by simp [embed, hi]
              simp [hne]
          · rw [hΨ_support u hu, zero_mul]
            refine (Finset.sum_eq_zero fun w₁ _ => Finset.sum_eq_zero fun w₂ _ => ?_).symm
            have hne : embed w₁ ≠ u := by
              intro he; subst he
              exact hu fun i hi => by simp [embed, hi]
            simp [hne]
        have henc_Ψ := h.encryptAvg_eq Ψ hΨ_mem
        rw [hpure_sum, encryptAvg_sum] at henc_Ψ
        simp_rw [encryptAvg_sum, encryptAvg_smul] at henc_Ψ
        have hsqrt_sq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by
          rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
          norm_num
        have hinner (w : ↥D → Bool) :
            ∑ w' : ↥D → Bool,
              (Ψ.ofLp (embed w) * star (Ψ.ofLp (embed w'))) •
                encryptAvg p U ρa (single (embed w) (embed w') 1) =
              ((2 : ℂ)⁻¹ ^ d) • ρ₀ +
                ((2 : ℂ)⁻¹ ^ d * (∏ j : ↥D, if v j then -Complex.I else 1) *
                  (∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1)) •
                  encryptAvg p U ρa (single (embed w) (embed (flip w)) 1) := by
          have hflip_ne : flip w ≠ w := by
            obtain ⟨i₀, hi₀⟩ : D.Nonempty := by
              have hex : ∃ i, x i ≠ y i := by
                by_contra hall; push Not at hall; exact hxy (funext hall)
              obtain ⟨i₀, hi₀⟩ := hex
              exact ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
            intro hfw
            have := congrFun hfw ⟨i₀, hi₀⟩
            dsimp only [flip] at this
            cases w ⟨i₀, hi₀⟩ <;> simp at this
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hflip_ne, Finset.mem_univ _⟩)]
          have hrest :
              ∑ w' ∈ (Finset.univ.erase w).erase (flip w),
                (Ψ.ofLp (embed w) * star (Ψ.ofLp (embed w'))) •
                  encryptAvg p U ρa (single (embed w) (embed w') 1) = 0 := by
            refine Finset.sum_eq_zero fun w' hw' => ?_
            have hw'_ne_flip : w' ≠ flip w := (Finset.mem_erase.mp hw').1
            have hw'_ne_w : w' ≠ w := (Finset.mem_erase.mp (Finset.mem_erase.mp hw').2).1
            have hne_emb : embed w ≠ embed w' := fun he => hw'_ne_w (hembed_inj he).symm
            have hlt : (univ.filter fun i => embed w i ≠ embed w' i).card < d := by
              have hsub : (univ.filter fun i => embed w i ≠ embed w' i) ⊂ D := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨fun i hi => ?_, fun heq => hw'_ne_flip ?_⟩
                · by_contra hiD
                  have hne_i := (Finset.mem_filter.mp hi).2
                  simp only [embed, hiD, ↓reduceDIte] at hne_i
                  exact hne_i rfl
                · funext ⟨i, hi⟩
                  have hi' : i ∈ univ.filter (fun i => embed w i ≠ embed w' i) := heq ▸ hi
                  have hne_i := (Finset.mem_filter.mp hi').2
                  simp only [embed, flip, hi, ↓reduceDIte] at hne_i ⊢
                  cases hw_i : w ⟨i, hi⟩ <;> cases hw'_i : w' ⟨i, hi⟩
                  · rw [ite_eq_right (by simp [hw_i]), ite_eq_right (by simp [hw'_i])] at hne_i
                    exact absurd rfl hne_i
                  · rfl
                  · rfl
                  · rw [ite_eq_left (by simp [hw_i]), ite_eq_left (by simp [hw'_i])] at hne_i
                    exact absurd rfl hne_i
              rw [← hD_card]
              exact Finset.card_lt_card hsub
            rw [ih _ hlt (embed w) (embed w') hne_emb rfl, smul_zero]
          rw [hrest, add_zero, hdiag (embed w)]
          congr 2
          · rw [hΨ_embed w]
            have h1 : ∏ j : ↥D, (if w j && v j then Complex.I else 1) *
                star (if w j && v j then Complex.I else 1) = 1 := by
              refine Finset.prod_eq_one fun j _ => ?_
              rcases Bool.eq_false_or_eq_true (w j) with hw | hw <;>
                rcases Bool.eq_false_or_eq_true (v j) with hv | hv <;>
                simp [hw, hv]
            calc
              ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ d *
                  ∏ j : ↥D, if w j && v j then Complex.I else 1) *
                star ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ d *
                  ∏ j : ↥D, if w j && v j then Complex.I else 1)
                  = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ d *
                      ∏ j : ↥D, (if w j && v j then Complex.I else 1) *
                        star (if w j && v j then Complex.I else 1) := by
                    rw [star_mul', star_pow, star_prod, Complex.star_def, Complex.conj_ofReal,
                      mul_mul_mul_comm, ← mul_pow, ← Finset.prod_mul_distrib]
              _ = (2 : ℂ)⁻¹ ^ d := by rw [hsqrt_sq, h1, mul_one]
          · rw [hΨ_embed w, hΨ_embed (flip w)]
            have h2 :
                (∏ j : ↥D, (if w j && v j then Complex.I else 1)) *
                   star (∏ j : ↥D, (if flip w j && v j then Complex.I else 1)) =
                  (∏ j : ↥D, if v j then -Complex.I else 1) *
                    (∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1) := by
              rw [star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl fun j _ => ?_
              dsimp only [flip]
              rcases Bool.eq_false_or_eq_true (w j) with hw | hw <;>
                rcases Bool.eq_false_or_eq_true (v j) with hv | hv <;>
                simp [hw, hv]
            calc
              ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ d *
                  ∏ j : ↥D, if w j && v j then Complex.I else 1) *
                star ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ d *
                  ∏ j : ↥D, if flip w j && v j then Complex.I else 1)
                  = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ d *
                      ((∏ j : ↥D, if w j && v j then Complex.I else 1) *
                        star (∏ j : ↥D, if flip w j && v j then Complex.I else 1)) := by
                    rw [star_mul', star_pow, Complex.star_def, Complex.conj_ofReal,
                      mul_mul_mul_comm, ← mul_pow]
              _ = (2 : ℂ)⁻¹ ^ d * (∏ j : ↥D, if v j then -Complex.I else 1) *
                    (∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1) := by
                    rw [hsqrt_sq, h2, mul_assoc]
        simp_rw [hinner] at henc_Ψ
        rw [Finset.sum_add_distrib] at henc_Ψ
        have hdiag_sum : ∑ _w : ↥D → Bool, ((2 : ℂ)⁻¹ ^ d) • ρ₀ = ρ₀ := by
          ext p₁ p₂
          simp [Matrix.sum_apply, hD_card]
        rw [hdiag_sum] at henc_Ψ
        have hzero :
            ∑ w : ↥D → Bool,
              ((2 : ℂ)⁻¹ ^ d * (∏ j : ↥D, if v j then -Complex.I else 1) *
                (∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1)) •
                encryptAvg p U ρa (single (embed w) (embed (flip w)) 1) = 0 :=
          add_eq_left.mp henc_Ψ
        have hc_ne : ((2 : ℂ)⁻¹ ^ d * ∏ j : ↥D, if v j then -Complex.I else 1) ≠ 0 := by
          refine mul_ne_zero (pow_ne_zero d (inv_ne_zero (by norm_num))) ?_
          rw [Finset.prod_ne_zero_iff]
          intro j _
          rcases Bool.eq_false_or_eq_true (v j) with hv | hv <;> simp [hv, Complex.I_ne_zero]
        simp_rw [← smul_smul ((2 : ℂ)⁻¹ ^ d * ∏ j : ↥D, if v j then -Complex.I else 1),
          ← Finset.smul_sum] at hzero
        exact (smul_eq_zero.mp hzero).resolve_left hc_ne
      have hsum_v :
          ∑ v : ↥D → Bool, ∑ w : ↥D → Bool,
            (∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1) •
              encryptAvg p U ρa (single (embed w) (embed (flip w)) 1) = 0 := by
        simp_rw [hphase_eq, Finset.sum_const_zero]
      rw [Finset.sum_comm] at hsum_v
      simp_rw [← Finset.sum_smul] at hsum_v
      have hchar (w : ↥D → Bool) :
          (∑ v : ↥D → Bool, ∏ j : ↥D, if w j && v j then (-1 : ℂ) else 1) =
            if w = fun _ => false then (2 : ℂ) ^ d else 0 := by
        rw [← Fintype.prod_sum (fun j b => if w j && b then (-1 : ℂ) else 1)]
        by_cases hw0 : w = fun _ => false
        · subst hw0
          simp only [Bool.false_and, ↓reduceIte, Fintype.sum_bool, Finset.prod_const,
            Finset.card_univ, Fintype.card_coe, hD_card]
          norm_num
        · rw [ite_eq_right hw0]
          have hex : ∃ j : ↥D, w j = true := by
            by_contra hall
            apply hw0
            funext j
            cases hwj : w j
            · rfl
            · exact absurd hwj (by push Not at hall; exact hall j)
          obtain ⟨j₀, hj₀⟩ := hex
          refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
          rw [hj₀, Fintype.sum_bool]
          simp
      simp_rw [hchar, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        hembed_zero, hembed_flip_zero] at hsum_v
      exact (smul_eq_zero.mp hsum_v).resolve_left (pow_ne_zero d (by norm_num))
  exact main _ x y hxy rfl

/-- **Bell-basis reduction** ([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000],
Theorem 5.2): any private quantum channel hiding all unentangled `n`-qubit pure states with key
distribution `p` and ancilla `ρa` yields a private quantum channel hiding all `4ⁿ` computational
basis states of `((α → Bool) × (α → Bool))` with the same key distribution `p` and ancilla `ρa`. -/
theorem exists_basis_pqc_of_unentangled {p : PMF K}
    {U : K → unitaryGroup ((α → Bool) × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix ((α → Bool) × κ) ((α → Bool) × κ) ℂ}
    (h : IsPrivateQuantumChannel (unentangledPureStates α) p U ρa ρ₀) :
    ∃ (U' : K → unitaryGroup (((α → Bool) × (α → Bool)) × κ) ℂ)
      (ρ₀' : Matrix (((α → Bool) × (α → Bool)) × κ) (((α → Bool) × (α → Bool)) × κ) ℂ),
      IsPrivateQuantumChannel
        (Set.range (ket (ι := (α → Bool) × (α → Bool)))) p U' ρa ρ₀' := by
  let Q := α → Bool
  have hcardQ : Fintype.card Q = 2 ^ Fintype.card α := by
    rw [Fintype.card_fun, Fintype.card_bool]
  have hscale :
      ((Real.sqrt (Fintype.card Q) : ℂ))⁻¹ *
        ((Real.sqrt (Fintype.card Q) : ℂ))⁻¹ =
        (Fintype.card Q : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  let B : Matrix (Q × Q) (Q × Q) ℂ :=
    Matrix.of fun yz ab => ((Real.sqrt (Fintype.card Q) : ℂ))⁻¹ *
      pauliString ab.1 ab.2 yz.1 yz.2
  have hB_mem : B ∈ unitaryGroup (Q × Q) ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hinner (y : Q) :
        ∑ z : Q, (Bᴴ (a, b) (y, z)) * B (y, z) (a', b') =
          if a = a' then
            (Fintype.card Q : ℂ)⁻¹ *
              ((signVal (b ⬝ᵥ (y + a)) * signVal (b' ⬝ᵥ (y + a)) : ℝ) : ℂ)
          else 0 := by
      simp only [B, conjTranspose_apply, of_apply, pauliString_apply]
      by_cases ha : a = a'
      · subst ha
        rw [ite_eq_left rfl, Finset.sum_eq_single (y + a)]
        · simp only [↓reduceIte, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
          push_cast
          linear_combination ((signVal (b ⬝ᵥ (y + a)) : ℂ) * signVal (b' ⬝ᵥ (y + a))) * hscale
        · intro z _ hz; simp [hz]
        · simp
      · rw [ite_eq_right ha]
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases hza : z = y + a
        · subst hza
          have hne : y + a ≠ y + a' := fun he => ha (add_left_cancel he)
          simp [hne]
        · simp [hza]
    simp_rw [hinner]
    by_cases ha : a = a'
    · subst ha
      simp only [↓reduceIte, ← Finset.mul_sum]
      have hbij : (∑ y : Q, ((signVal (b ⬝ᵥ (y + a)) * signVal (b' ⬝ᵥ (y + a)) : ℝ) : ℂ)) =
          ∑ z : Q, ((signVal (b ⬝ᵥ z) * signVal (b' ⬝ᵥ z) : ℝ) : ℂ) :=
        Fintype.sum_equiv (Equiv.addRight a) _ _ fun _ => rfl
      have horth := sum_signVal_dotProduct_mul_signVal_dotProduct b b'
      rw [hbij, ← Complex.ofReal_sum, horth]
      by_cases hb : b = b'
      · subst hb
        simp only [↓reduceIte, Matrix.one_apply_eq, Complex.ofReal_pow, Complex.ofReal_ofNat,
          hcardQ, Nat.cast_pow, Nat.cast_ofNat]
        exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
      · have hne : ((a, b) : Q × Q) ≠ (a, b') := fun hp => hb (Prod.mk.inj hp).2
        rw [ite_eq_right hb, Matrix.one_apply_ne hne, Complex.ofReal_zero, mul_zero]
    · have hne : ((a, b) : Q × Q) ≠ (a', b') := fun hp => ha (Prod.mk.inj hp).1
      rw [Matrix.one_apply_ne hne]
      simp [ha]
  let e : ((Q × Q) × κ) ≃ (Q × (Q × κ)) := Equiv.prodAssoc Q Q κ
  let reind := reindexAlgEquiv ℂ ℂ e.symm
  have hreind_conjTranspose (M : Matrix (Q × (Q × κ)) (Q × (Q × κ)) ℂ) :
      (reind M)ᴴ = reind Mᴴ := rfl
  have hreind_unitary {M : Matrix (Q × (Q × κ)) (Q × (Q × κ)) ℂ}
      (hM : M ∈ unitaryGroup (Q × (Q × κ)) ℂ) :
      reind M ∈ unitaryGroup ((Q × Q) × κ) ℂ := by
    have hMM : Mᴴ * M = 1 := by
      simpa only [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hM
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, hreind_conjTranspose, ← map_mul, hMM,
      map_one]
  let U' (k : K) : unitaryGroup ((Q × Q) × κ) ℂ :=
    ⟨reind ((1 : Matrix Q Q ℂ) ⊗ₖ (U k : Matrix (Q × κ) (Q × κ) ℂ)) *
        (B ⊗ₖ (1 : Matrix κ κ ℂ)),
      (unitaryGroup ((Q × Q) × κ) ℂ).mul_mem
        (hreind_unitary (kronecker_mem_unitary (one_mem _) (U k).2))
        (kronecker_mem_unitary hB_mem (one_mem _))⟩
  let ρ₀' : Matrix ((Q × Q) × κ) ((Q × Q) × κ) ℂ :=
    reind (((Fintype.card Q : ℂ)⁻¹ • (1 : Matrix Q Q ℂ)) ⊗ₖ ρ₀)
  refine ⟨U', ρ₀', h.ancilla_density, ?_⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have hdiag (z : Q) : encryptAvg p U ρa (single z z 1) = ρ₀ := by
    have hpure : pureState (ket z) = single z z (1 : ℂ) := by
      ext u u'
      by_cases hu : u = z <;> by_cases hu' : u' = z <;>
        simp [pureState_apply, hu, hu', Ne.symm]
    rw [← hpure]
    exact h.encryptAvg_eq (ket z) (ket_mem_unentangledPureStates z)
  have hBell_ket :
      B * pureState (ket (a, b)) * Bᴴ =
        (Fintype.card Q : ℂ)⁻¹ •
          ∑ z : Q, ∑ z' : Q,
            (pauliString a b * single z z' (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ
              single z z' (1 : ℂ) := by
    ext ⟨y, z₀⟩ ⟨y', z₀'⟩
    have hstar_sqrt : star ((Real.sqrt (Fintype.card Q) : ℂ)) =
        (Real.sqrt (Fintype.card Q) : ℂ) :=
      Complex.conj_ofReal _
    have hL :
        (B * pureState (ket (a, b)) * Bᴴ) (y, z₀) (y', z₀') =
          (Fintype.card Q : ℂ)⁻¹ *
            (pauliString a b y z₀ * star (pauliString a b y' z₀')) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (a, b)]
      · rw [Matrix.mul_apply, Finset.sum_eq_single (a, b)]
        · simp only [B, of_apply, pureState_apply, ket_apply, ↓reduceIte, mul_one, star_one,
            conjTranspose_apply, star_mul', star_inv₀, hstar_sqrt]
          linear_combination (pauliString a b y z₀ * star (pauliString a b y' z₀')) * hscale
        · intro pq _ hpq; simp [pureState_apply, hpq]
        · simp
      · intro pq _ hpq
        have h0 : (B * pureState (ket (a, b))) (y, z₀) pq = 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun rs _ => ?_
          by_cases hrs : rs = (a, b)
          · subst hrs; simp [pureState_apply, hpq]
          · simp [pureState_apply, hrs]
        rw [h0, zero_mul]
      · simp
    rw [hL, Matrix.smul_apply, Matrix.sum_apply, Finset.sum_eq_single z₀]
    · rw [Matrix.sum_apply, Finset.sum_eq_single z₀']
      · simp only [kroneckerMap_apply, single_apply_same, mul_one, smul_eq_mul]
        congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single z₀']
        · rw [Matrix.mul_apply, Finset.sum_eq_single z₀]
          · simp [conjTranspose_apply]
          · intro w _ hw; simp [Ne.symm hw]
          · simp
        · intro w _ hw
          have h0 : (pauliString a b * single z₀ z₀' (1 : ℂ)) y w = 0 := by
            rw [Matrix.mul_apply]
            refine Finset.sum_eq_zero fun v _ => ?_
            simp [Ne.symm hw]
          rw [h0, zero_mul]
        · simp
      · intro z' _ hz'; simp [kroneckerMap_apply, hz']
      · simp
    · intro z _ hz
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun z' _ => ?_
      simp [kroneckerMap_apply, hz]
    · simp
  have hreind_assoc (X Y : Matrix Q Q ℂ) (Z : Matrix κ κ ℂ) :
      (X ⊗ₖ Y) ⊗ₖ Z = reind (X ⊗ₖ (Y ⊗ₖ Z)) := by
    ext ⟨⟨q₁, q₂⟩, r₁⟩ ⟨⟨q₁', q₂'⟩, r₂⟩
    simp only [reind, e, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_symm,
      Equiv.prodAssoc_apply, kroneckerMap_apply, mul_assoc]
  have hstep (k : K) :
      (U' k : Matrix ((Q × Q) × κ) ((Q × Q) × κ) ℂ) *
          (pureState (ket (a, b)) ⊗ₖ ρa) *
          (U' k : Matrix ((Q × Q) × κ) ((Q × Q) × κ) ℂ)ᴴ =
        (Fintype.card Q : ℂ)⁻¹ •
          ∑ z : Q, ∑ z' : Q,
            reind ((pauliString a b * single z z' (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ
              ((U k : Matrix (Q × κ) (Q × κ) ℂ) * (single z z' (1 : ℂ) ⊗ₖ ρa) *
                (U k : Matrix (Q × κ) (Q × κ) ℂ)ᴴ)) := by
    let M₁ := reind ((1 : Matrix Q Q ℂ) ⊗ₖ (U k : Matrix (Q × κ) (Q × κ) ℂ))
    have hassoc :
        (M₁ * (B ⊗ₖ (1 : Matrix κ κ ℂ))) * (pureState (ket (a, b)) ⊗ₖ ρa) *
            (M₁ * (B ⊗ₖ (1 : Matrix κ κ ℂ)))ᴴ =
          M₁ * ((B ⊗ₖ (1 : Matrix κ κ ℂ)) * (pureState (ket (a, b)) ⊗ₖ ρa) *
            (B ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) * M₁ᴴ := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    change (M₁ * (B ⊗ₖ (1 : Matrix κ κ ℂ))) * (pureState (ket (a, b)) ⊗ₖ ρa) *
        (M₁ * (B ⊗ₖ (1 : Matrix κ κ ℂ)))ᴴ = _
    rw [hassoc, conjTranspose_kronecker B (1 : Matrix κ κ ℂ), conjTranspose_one,
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      hBell_ket, smul_kronecker, sum_kronecker]
    simp_rw [sum_kronecker, hreind_assoc]
    rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun z' _ => ?_
    dsimp only [M₁]
    rw [hreind_conjTranspose, ← map_mul, ← map_mul, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one]
  unfold encryptAvg
  simp_rw [hstep, smul_comm _ (Fintype.card Q : ℂ)⁻¹, ← Finset.smul_sum]
  have hswap :
      (∑ k : K, (p k).toReal • ∑ z : Q, ∑ z' : Q,
          reind ((pauliString a b * single z z' (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ
            ((U k : Matrix (Q × κ) (Q × κ) ℂ) * (single z z' (1 : ℂ) ⊗ₖ ρa) *
              (U k : Matrix (Q × κ) (Q × κ) ℂ)ᴴ))) =
        ∑ z : Q, ∑ z' : Q,
          reind ((pauliString a b * single z z' (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ
            encryptAvg p U ρa (single z z' (1 : ℂ))) := by
    ext p₁ p₂
    simp only [reind, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, kroneckerMap_apply, encryptAvg, Complex.real_smul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun z' _ => sum_congr rfl fun k _ => by ring
  rw [hswap]
  have hcollapse (z : Q) :
      (∑ z' : Q,
          reind ((pauliString a b * single z z' (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ
            encryptAvg p U ρa (single z z' (1 : ℂ)))) =
        reind ((pauliString a b * single z z (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ ρ₀) := by
    rw [Finset.sum_eq_single z]
    · rw [hdiag z]
    · intro z' _ hz'
      rw [encryptAvg_single_eq_zero_of_ne h (Ne.symm hz'), kronecker_zero]
      rfl
    · simp
  simp_rw [hcollapse]
  have hsum_pauli :
      (∑ z : Q, pauliString a b * single z z (1 : ℂ) * (pauliString a b)ᴴ) = 1 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_one, Matrix.mul_one]
    have hP := pauliString_mem_unitaryGroup a b
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose] at hP
    exact hP
  have hreind_sum :
      (Fintype.card Q : ℂ)⁻¹ •
          (∑ z : Q, reind ((pauliString a b * single z z (1 : ℂ) * (pauliString a b)ᴴ) ⊗ₖ ρ₀)) =
        ρ₀' := by
    dsimp only [ρ₀']
    rw [← hsum_pauli, smul_kronecker, sum_kronecker, map_smul, map_sum]
  exact hreind_sum

/-- **Key-entropy lower bound for unentangled `n`-qubit states**
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Corollary 5.4): any private quantum
channel hiding all unentangled `n`-qubit pure states (`n = |α|`), even with an arbitrary finite
ancilla `ρa`, requires at least `2n` bits of Shannon key entropy. -/
theorem two_mul_card_le_entropy_of_unentangled {p : PMF K}
    {U : K → unitaryGroup ((α → Bool) × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix ((α → Bool) × κ) ((α → Bool) × κ) ℂ}
    (h : IsPrivateQuantumChannel (unentangledPureStates α) p U ρa ρ₀) :
    2 * (Fintype.card α : ℝ) ≤ entropy p := by
  obtain ⟨U', ρ₀', h'⟩ := exists_basis_pqc_of_unentangled h
  have hbound := logb_card_le_entropy_of_basis h'
  have hcard :
      Real.logb 2 (Fintype.card ((α → Bool) × (α → Bool))) = 2 * (Fintype.card α : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, ← pow_add, ← two_mul,
      Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb,
      div_self (Real.log_pos (by norm_num)).ne', mul_one, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- **Key-count lower bound for unentangled `n`-qubit states**
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Corollary 5.4): if `p` is supported
on `s : Finset K`, any private quantum channel hiding all unentangled `n`-qubit pure states
satisfies `4ⁿ ≤ |s|`. -/
theorem four_pow_card_le_of_unentangled {p : PMF K}
    {U : K → unitaryGroup ((α → Bool) × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix ((α → Bool) × κ) ((α → Bool) × κ) ℂ}
    (h : IsPrivateQuantumChannel (unentangledPureStates α) p U ρa ρ₀)
    {s : Finset K} (hs : p.support ⊆ ↑s) :
    4 ^ Fintype.card α ≤ s.card := by
  obtain ⟨k₀, hk₀⟩ := p.support_nonempty
  have hs_pos : (0 : ℝ) < s.card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨k₀, hs hk₀⟩)
  have hent : 2 * (Fintype.card α : ℝ) ≤ Real.logb 2 s.card :=
    (two_mul_card_le_entropy_of_unentangled h).trans
      (entropy_le_logb_card_of_support_subset p hs)
  have hrpow : (2 : ℝ) ^ (2 * (Fintype.card α : ℝ)) ≤ (s.card : ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hs_pos).mp hent
  have h4 : (2 : ℝ) ^ (2 * (Fintype.card α : ℝ)) = ((4 ^ Fintype.card α : ℕ) : ℝ) := by
    rw [show (2 * (Fintype.card α : ℝ)) = ((2 * Fintype.card α : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
    norm_num
  rw [h4] at hrpow
  exact_mod_cast hrpow

/-- **Key-entropy lower bound for all `n`-qubit pure states**
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Corollary 5.5): any private quantum
channel hiding all unit pure `n`-qubit states (with arbitrary ancilla `ρa`) requires at least
`2n` bits of Shannon key entropy, matching `Cslib.Crypto.Protocols.Quantum.OneTimePad`. -/
theorem two_mul_card_le_entropy_of_pureStates {p : PMF K}
    {U : K → unitaryGroup ((α → Bool) × κ) ℂ} {ρa : Matrix κ κ ℂ}
    {ρ₀ : Matrix ((α → Bool) × κ) ((α → Bool) × κ) ℂ}
    (h : IsPrivateQuantumChannel {ψ : EuclideanSpace ℂ (α → Bool) | ‖ψ‖ = 1} p U ρa ρ₀) :
    2 * (Fintype.card α : ℝ) ≤ entropy p :=
  two_mul_card_le_entropy_of_unentangled
    (h.mono fun _ => norm_eq_one_of_mem_unentangledPureStates)

/-- **Ancilla-free `2n`-bit key-entropy lower bound**
([Ambainis, Mosca, Tapp, de Wolf][AmbainisMoscaTappdeWolf2000], Theorem 5.1 / Corollary 5.5
without ancilla): if unitaries `U : K → unitaryGroup (α → Bool) ℂ` under key law `p : PMF K` map
every unit pure `n`-qubit state to the same ciphertext state `ρ₀`, then `2n ≤ H(p)`. -/
theorem two_mul_card_le_entropy_noAncilla (p : PMF K)
    (U : K → unitaryGroup (α → Bool) ℂ) (ρ₀ : OneTimePad.Op α)
    (h : ∀ ψ : EuclideanSpace ℂ (α → Bool), ‖ψ‖ = 1 →
      ∑ k : K, (p k).toReal •
        ((U k : OneTimePad.Op α) * pureState ψ * (U k : OneTimePad.Op α)ᴴ) = ρ₀) :
    2 * (Fintype.card α : ℝ) ≤ entropy p := by
  let U₁ (k : K) : unitaryGroup ((α → Bool) × Unit) ℂ :=
    ⟨(U k : OneTimePad.Op α) ⊗ₖ (1 : Matrix Unit Unit ℂ),
      kronecker_mem_unitary (U k).2 (one_mem _)⟩
  have hρa : IsDensityMatrix (1 : Matrix Unit Unit ℂ) := ⟨PosSemidef.one, by simp⟩
  have hpqc : IsPrivateQuantumChannel {ψ : EuclideanSpace ℂ (α → Bool) | ‖ψ‖ = 1}
      p U₁ (1 : Matrix Unit Unit ℂ) (ρ₀ ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
    refine ⟨hρa, fun ψ hψ => ?_⟩
    unfold encryptAvg
    have hterm (k : K) :
        (U₁ k : Matrix ((α → Bool) × Unit) ((α → Bool) × Unit) ℂ) *
            (pureState ψ ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
            (U₁ k : Matrix ((α → Bool) × Unit) ((α → Bool) × Unit) ℂ)ᴴ =
          ((U k : OneTimePad.Op α) * pureState ψ * (U k : OneTimePad.Op α)ᴴ) ⊗ₖ
            (1 : Matrix Unit Unit ℂ) := by
      dsimp only [U₁]
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
        Matrix.mul_one, Matrix.mul_one]
    simp_rw [hterm, ← smul_kronecker, ← sum_kronecker, h ψ hψ]
  exact two_mul_card_le_entropy_of_pureStates hpqc

end Qubits

end Cslib.Crypto.Protocols.Quantum
