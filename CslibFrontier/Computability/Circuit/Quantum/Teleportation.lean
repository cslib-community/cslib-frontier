/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.GateMatrix
public import CslibFrontier.Foundations.Quantum.Bell
public import CslibFrontier.Foundations.Quantum.Bipartite
public import CslibFrontier.Foundations.Quantum.Register
public import Cslib.Probability.PMF

/-!
# Quantum teleportation

**Teleportation** [Bennett et al.][BennettBrassardCrepeauJozsaPeresWootters1993];
[de Wolf][deWolf2019], Section 1.5. Alice holds an unknown qubit `ψ` and shares a Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` with Bob. The three qubits are indexed by `(Bool × Bool) × Bool`:
Alice's input qubit and her half of the Bell state, then Bob's half. The protocol:

1. Alice applies a CNOT to her two qubits (her input is the control), then a Hadamard to her input
   qubit (`Cslib.Quantum.teleportUnitary`). The joint state is
   `½ ∑_{a,b} |a, b⟩ ⊗ X^b Z^a ψ` (`Cslib.Quantum.teleportState_apply`).
2. Alice measures her two qubits in the computational basis. Each outcome `(a, b)` has probability
   `1/4`, whatever `ψ` is (`Cslib.Quantum.measure_teleportState_map_fst`), and leaves Bob's qubit in
   the post-measurement state `X^b Z^a ψ` (`Cslib.Quantum.postMeasure`).
3. Alice sends `(a, b)` to Bob, who applies the correction `Z^a X^b`
   (`Cslib.Quantum.teleportCorrection`): first `X` if `b = 1`, then `Z` if `a = 1`. He holds `ψ`
   (`Cslib.Quantum.teleportCorrection_postMeasure`).

`Cslib.Quantum.teleportation` states the single-qubit result. The measurement is the
computational-basis measurement of `CslibFrontier/Foundations/Quantum/Measurement.lean`, read on
Alice's qubits through the marginal `PMF.map Prod.fst`. Bob's corrected state is the corresponding
post-measurement state of `CslibFrontier/Foundations/Quantum/Bipartite.lean`.

By linearity, the same protocol teleports **one half of an entangled state**
(`Cslib.Quantum.teleportation_entangled`): when a reference system with finite basis `ι` and Alice's
input qubit start in any joint unit pure state `Ψ ∈ ℂ^{ι × Bool}`, Alice's outcome `(a, b)` is still
uniformly distributed on `Bool × Bool` (leaking nothing about `Ψ` or its correlations with the
reference), and applying `I_ι ⊗ Z^a X^b` (`onSecond (teleportCorrection a b)`) on the reference and
Bob's qubit recovers the exact joint state `Ψ`. Taking `ι = Bool` and `Ψ = bell` gives
**entanglement swapping**: starting from two independent Bell pairs `bell ⊗ bell` shared by
Charlie–Alice and Alice–Bob, Alice's Bell measurement and Bob's local correction leave Charlie and
Bob sharing `bell` without ever having interacted.

Scope: pure states with an arbitrary finite-dimensional reference register. Mixed-state channel
formulations of teleportation are not formalized here.

## Main definitions

* `Cslib.Quantum.teleportInput`: the initial state `ψ ⊗ Φ⁺`.
* `Cslib.Quantum.teleportUnitary`: Alice's unitary, the CNOT and then the Hadamard on her two
  qubits, tensored with the identity on any remaining register.
* `Cslib.Quantum.teleportState`: the joint state before Alice's measurement.
* `Cslib.Quantum.teleportCorrection`: Bob's correction `Z^a X^b`.
* `Cslib.Quantum.teleportEntangledInput`, `Cslib.Quantum.teleportEntangledState`: the initial and
  pre-measurement four-register states when Alice's input is entangled with a reference register
  `ι`.

## Main results

* `Cslib.Quantum.teleportState_apply`: the amplitudes of the joint state before measurement.
* `Cslib.Quantum.measure_teleportState_map_fst`: Alice's outcome is uniform on `Bool × Bool`.
* `Cslib.Quantum.teleportCorrection_postMeasure`: Bob's corrected post-measurement state is `ψ`.
* `Cslib.Quantum.teleportation`: single-qubit teleportation.
* `Cslib.Quantum.teleportEntangledState_apply`,
  `Cslib.Quantum.measure_teleportEntangledState_map_fst`,
  `Cslib.Quantum.teleportCorrection_postMeasure_entangled`,
  `Cslib.Quantum.teleportation_entangled`: teleportation of one half of an entangled state
  (specializing at `Ψ = bell` to entanglement swapping).

## References

* [C. H. Bennett, G. Brassard, C. Crépeau, R. Jozsa, A. Peres, W. K. Wootters, *Teleporting an
  unknown quantum state via dual classical and Einstein-Podolsky-Rosen
  channels*][BennettBrassardCrepeauJozsaPeresWootters1993]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Gate
open scoped Kronecker

/-- The initial state `ψ ⊗ Φ⁺` of teleportation, indexed by
`((Alice's input, Alice's Bell half), Bob's Bell half)`. -/
noncomputable def teleportInput (ψ : EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ ((Bool × Bool) × Bool) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodAssoc Bool Bool Bool).symm (prodState ψ bell)

theorem teleportInput_apply (ψ : EuclideanSpace ℂ Bool) (a b c : Bool) :
    (teleportInput ψ).ofLp ((a, b), c) = ψ.ofLp a * bell.ofLp (b, c) :=
  prodState_apply ψ bell (a, (b, c))

theorem norm_teleportInput (ψ : EuclideanSpace ℂ Bool) : ‖teleportInput ψ‖ = ‖ψ‖ := by
  rw [teleportInput, LinearIsometryEquiv.norm_map, norm_prodState, norm_bell, mul_one]

/-- Alice's unitary in teleportation, acting on her two qubits and trivially on any remaining
register `κ`: a CNOT on her two qubits, controlled by her input qubit, followed by a Hadamard on
her input qubit. -/
noncomputable def teleportUnitary {κ : Type*} [Fintype κ] [DecidableEq κ] :
    unitaryGroup ((Bool × Bool) × κ) ℂ :=
  onFirst (onFirst ⟨hadamardMatrix, hadamardMatrix_mem_unitaryGroup⟩) *
    onFirst ⟨cnotMatrix, cnotMatrix_mem_unitaryGroup⟩

private theorem teleportUnitary_mulVec_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : (Bool × Bool) × κ → ℂ) (a b : Bool) (k : κ) :
    ((teleportUnitary (κ := κ) : Matrix ((Bool × Bool) × κ) ((Bool × Bool) × κ) ℂ) *ᵥ v)
        ((a, b), k) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (v ((false, b), k) + (if a then -1 else 1) * v ((true, !b), k)) := by
  simp only [teleportUnitary, Submonoid.coe_mul, coe_onFirst, ← mulVec_mulVec,
    kronecker_one_mulVec_apply, hadamardMatrix_mulVec, cnotMatrix_mulVec, Bool.bne_false,
    Bool.bne_true]

private theorem bell_amplitude_combine (f : Bool → ℂ) (a b c : Bool) :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (f false * bell.ofLp (b, c) + (if a then -1 else 1) * (f true * bell.ofLp (!b, c))) =
      (1 / 2 : ℂ) * ((if a && (b ^^ c) then -1 else 1) * f (b ^^ c)) := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [← hs, bell_apply, bell_apply]
  cases a <;> cases b <;> cases c <;> simp <;> ring

/-- The joint state of teleportation before Alice's measurement. -/
noncomputable def teleportState (ψ : EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ ((Bool × Bool) × Bool) :=
  unitaryEquiv teleportUnitary (teleportInput ψ)

theorem norm_teleportState (ψ : EuclideanSpace ℂ Bool) : ‖teleportState ψ‖ = ‖ψ‖ := by
  rw [teleportState, LinearIsometryEquiv.norm_map, norm_teleportInput]

/-- The joint state before Alice's measurement is `½ ∑_{a,b} |a, b⟩ ⊗ X^b Z^a ψ`: its amplitude at
`|a, b, c⟩` is `½ (-1)^{a (b ⊕ c)} ψ_{b ⊕ c}` [de Wolf][deWolf2019], Section 1.5. -/
theorem teleportState_apply (ψ : EuclideanSpace ℂ Bool) (a b c : Bool) :
    (teleportState ψ).ofLp ((a, b), c) =
      (1 / 2 : ℂ) * ((if a && (b ^^ c) then -1 else 1) * ψ.ofLp (b ^^ c)) := by
  rw [teleportState, unitaryEquiv_apply, teleportUnitary_mulVec_apply, teleportInput_apply,
    teleportInput_apply, bell_amplitude_combine (fun x => ψ.ofLp x)]

/-- Bob's correction `Z^a X^b` in teleportation: first `X` if `b = 1`, then `Z` if `a = 1`. -/
noncomputable def teleportCorrection (a b : Bool) : unitaryGroup Bool ℂ :=
  (if a then ⟨pauliZ, pauliZ_mem_unitaryGroup⟩ else 1) *
    (if b then ⟨pauliX, pauliX_mem_unitaryGroup⟩ else 1)

/-- Bob's correction maps `v` to `((-1)^{a c} v_{c ⊕ b})_c`. -/
theorem teleportCorrection_mulVec (a b : Bool) (v : Bool → ℂ) (c : Bool) :
    ((teleportCorrection a b : Matrix Bool Bool ℂ) *ᵥ v) c =
      (if a && c then -1 else 1) * v (c ^^ b) := by
  cases a <;> cases b <;> cases c <;> simp [teleportCorrection, ← mulVec_mulVec]

/-- Bob's correction maps the unnormalized post-measurement state of outcome `(a, b)` to `ψ/2`. -/
theorem teleportCorrection_condState (ψ : EuclideanSpace ℂ Bool) (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (condState (a, b) (teleportState ψ)) =
      (1 / 2 : ℂ) • ψ := by
  ext c
  rw [unitaryEquiv_apply, teleportCorrection_mulVec, condState_apply, teleportState_apply]
  cases a <;> cases b <;> cases c <;> simp

theorem norm_condState_teleportState (ψ : EuclideanSpace ℂ Bool) (a b : Bool) :
    ‖condState (a, b) (teleportState ψ)‖ = ‖ψ‖ / 2 := by
  rw [← LinearIsometryEquiv.norm_map (unitaryEquiv (teleportCorrection a b)),
    teleportCorrection_condState, norm_smul, norm_div, norm_one, RCLike.norm_ofNat]
  ring

/-- In teleportation of a unit qubit, each outcome `(a, b)` of Alice's measurement has
probability `1/4`. -/
theorem measure_teleportState_map_fst_apply (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1)
    (a b : Bool) :
    (measure (teleportState ψ) ((norm_teleportState ψ).trans hψ)).map Prod.fst (a, b) = 4⁻¹ := by
  rw [measure_map_fst_apply _ ((norm_teleportState ψ).trans hψ), norm_condState_teleportState, hψ,
    show ((1 : ℝ) / 2) ^ 2 = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- In teleportation of a unit qubit, Alice's measurement outcome is uniform on `Bool × Bool`,
independently of the teleported qubit. -/
theorem measure_teleportState_map_fst (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1) :
    (measure (teleportState ψ) ((norm_teleportState ψ).trans hψ)).map Prod.fst =
      Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) := by
  ext ⟨a, b⟩
  rw [measure_teleportState_map_fst_apply ψ hψ, Cslib.Probability.PMF.uniformOfFintype_apply,
    Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- After outcome `(a, b)` of Alice's measurement, Bob's correction `Z^a X^b` turns his
post-measurement qubit into the teleported qubit `ψ`. -/
theorem teleportCorrection_postMeasure (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1) (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState ψ)) = ψ := by
  rw [postMeasure_def, LinearIsometryEquiv.map_smul, teleportCorrection_condState,
    norm_condState_teleportState, hψ, smul_smul]
  norm_num

/-- **Quantum teleportation** [Bennett et al.][BennettBrassardCrepeauJozsaPeresWootters1993];
[de Wolf][deWolf2019], Section 1.5. Alice holds a unit qubit `ψ` and shares the Bell state with
Bob. She applies a CNOT and then a Hadamard to her two qubits and measures them. Her outcome
`(a, b)` is uniformly distributed, and for every outcome Bob's correction `Z^a X^b` turns his
post-measurement qubit into `ψ`. -/
theorem teleportation (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1) :
    (measure (teleportState ψ) ((norm_teleportState ψ).trans hψ)).map Prod.fst =
        Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) ∧
      ∀ a b : Bool,
        unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState ψ)) = ψ :=
  ⟨measure_teleportState_map_fst ψ hψ, teleportCorrection_postMeasure ψ hψ⟩

/-! ### Teleporting one half of an entangled state -/

section Entangled

variable {ι : Type*}

private def teleportEntangledEquiv (ι : Type*) :
    (ι × Bool) × (Bool × Bool) ≃ (Bool × Bool) × (ι × Bool) where
  toFun := fun ⟨⟨r, a⟩, ⟨b, c⟩⟩ => ((a, b), (r, c))
  invFun := fun ⟨⟨a, b⟩, ⟨r, c⟩⟩ => ((r, a), (b, c))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- The initial four-register state of entangled teleportation: a bipartite pure state
`Ψ ∈ ℂ^{ι × Bool}` shared between a reference system `ι` and Alice's input qubit, tensored with the
Bell state `Φ⁺` shared by Alice and Bob, regrouped as
`((Alice's input, Alice's Bell half), (reference, Bob's Bell half))`. -/
noncomputable def teleportEntangledInput [Fintype ι] (Ψ : EuclideanSpace ℂ (ι × Bool)) :
    EuclideanSpace ℂ ((Bool × Bool) × (ι × Bool)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (teleportEntangledEquiv ι) (prodState Ψ bell)

theorem teleportEntangledInput_apply [Fintype ι] (Ψ : EuclideanSpace ℂ (ι × Bool)) (a b : Bool)
    (r : ι) (c : Bool) :
    (teleportEntangledInput Ψ).ofLp ((a, b), (r, c)) = Ψ.ofLp (r, a) * bell.ofLp (b, c) := by
  change (prodState Ψ bell).ofLp ((r, a), (b, c)) = _
  exact prodState_apply Ψ bell ((r, a), (b, c))

theorem norm_teleportEntangledInput [Fintype ι] (Ψ : EuclideanSpace ℂ (ι × Bool)) :
    ‖teleportEntangledInput Ψ‖ = ‖Ψ‖ := by
  rw [teleportEntangledInput, LinearIsometryEquiv.norm_map, norm_prodState, norm_bell, mul_one]

/-- The joint state of entangled teleportation before Alice's measurement, after Alice applies
`teleportUnitary` to her two qubits while the reference register `ι` and Bob's qubit stay fixed. -/
noncomputable def teleportEntangledState [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) :
    EuclideanSpace ℂ ((Bool × Bool) × (ι × Bool)) :=
  unitaryEquiv teleportUnitary (teleportEntangledInput Ψ)

theorem norm_teleportEntangledState [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) : ‖teleportEntangledState Ψ‖ = ‖Ψ‖ := by
  rw [teleportEntangledState, LinearIsometryEquiv.norm_map, norm_teleportEntangledInput]

/-- Before Alice measures, the amplitude at `((a, b), (r, c))` is
`½ (-1)^{a (b ⊕ c)} Ψ_{(r, b ⊕ c)}`: conditioned on `(a, b)`, the reference and Bob's qubit are in
`(I_ι ⊗ X^b Z^a) Ψ`. -/
theorem teleportEntangledState_apply [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (a b : Bool) (r : ι) (c : Bool) :
    (teleportEntangledState Ψ).ofLp ((a, b), (r, c)) =
      (1 / 2 : ℂ) * ((if a && (b ^^ c) then -1 else 1) * Ψ.ofLp (r, b ^^ c)) := by
  rw [teleportEntangledState, unitaryEquiv_apply, teleportUnitary_mulVec_apply,
    teleportEntangledInput_apply, teleportEntangledInput_apply,
    bell_amplitude_combine (fun x => Ψ.ofLp (r, x))]

/-- Acting as `I_ι` on the reference and as `teleportCorrection a b` on Bob's qubit maps the
unnormalized conditional state of outcome `(a, b)` to `Ψ / 2`. -/
theorem teleportCorrection_condState_entangled [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (a b : Bool) :
    unitaryEquiv (onSecond (teleportCorrection a b))
        (condState (a, b) (teleportEntangledState Ψ)) =
      (1 / 2 : ℂ) • Ψ := by
  ext ⟨r, c⟩
  rw [unitaryEquiv_apply, coe_onSecond, one_kronecker_mulVec_apply]
  dsimp only
  rw [teleportCorrection_mulVec, condState_apply, teleportEntangledState_apply]
  cases a <;> cases b <;> cases c <;> simp

theorem norm_condState_teleportEntangledState [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (a b : Bool) :
    ‖condState (a, b) (teleportEntangledState Ψ)‖ = ‖Ψ‖ / 2 := by
  rw [← LinearIsometryEquiv.norm_map (unitaryEquiv (onSecond (teleportCorrection a b))),
    teleportCorrection_condState_entangled, norm_smul, norm_div, norm_one, RCLike.norm_ofNat]
  ring

/-- When teleporting one half of a unit bipartite state `Ψ ∈ ℂ^{ι × Bool}`, each outcome `(a, b)`
of Alice's measurement has probability `1/4`. -/
theorem measure_teleportEntangledState_map_fst_apply [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (hΨ : ‖Ψ‖ = 1) (a b : Bool) :
    (measure (teleportEntangledState Ψ)
        ((norm_teleportEntangledState Ψ).trans hΨ)).map Prod.fst (a, b) = 4⁻¹ := by
  rw [measure_map_fst_apply _ ((norm_teleportEntangledState Ψ).trans hΨ),
    norm_condState_teleportEntangledState, hΨ,
    show ((1 : ℝ) / 2) ^ 2 = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- When teleporting one half of a unit bipartite state `Ψ ∈ ℂ^{ι × Bool}`, Alice's measurement
outcome is uniform on `Bool × Bool`, independently of `Ψ` and its entanglement with `ι`. -/
theorem measure_teleportEntangledState_map_fst [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (hΨ : ‖Ψ‖ = 1) :
    (measure (teleportEntangledState Ψ)
        ((norm_teleportEntangledState Ψ).trans hΨ)).map Prod.fst =
      Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) := by
  ext ⟨a, b⟩
  rw [measure_teleportEntangledState_map_fst_apply Ψ hΨ,
    Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- After outcome `(a, b)` of Alice's measurement, Bob's local correction `I_ι ⊗ Z^a X^b` restores
the joint state of the reference system and Bob's qubit to `Ψ`. -/
theorem teleportCorrection_postMeasure_entangled [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (hΨ : ‖Ψ‖ = 1) (a b : Bool) :
    unitaryEquiv (onSecond (teleportCorrection a b))
        (postMeasure (a, b) (teleportEntangledState Ψ)) = Ψ := by
  rw [postMeasure_def, LinearIsometryEquiv.map_smul, teleportCorrection_condState_entangled,
    norm_condState_teleportEntangledState, hΨ, smul_smul]
  norm_num

/-- **Teleportation of one half of an entangled state**
[Bennett et al.][BennettBrassardCrepeauJozsaPeresWootters1993]; [de Wolf][deWolf2019], Section 1.5.
A reference system `ι` and Alice's input qubit start in a unit pure state `Ψ ∈ ℂ^{ι × Bool}`, and
Alice and Bob share the Bell state `Φ⁺`. Alice applies CNOT and Hadamard to her two qubits and
measures them: her outcome `(a, b)` is uniformly distributed on `Bool × Bool`, and for every
outcome Bob's local correction `I_ι ⊗ Z^a X^b` leaves the reference and Bob's qubit in `Ψ`.
At `ι = Bool` and `Ψ = bell`, this is entanglement swapping. -/
theorem teleportation_entangled [Fintype ι] [DecidableEq ι]
    (Ψ : EuclideanSpace ℂ (ι × Bool)) (hΨ : ‖Ψ‖ = 1) :
    (measure (teleportEntangledState Ψ)
        ((norm_teleportEntangledState Ψ).trans hΨ)).map Prod.fst =
      Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) ∧
    ∀ a b : Bool,
      unitaryEquiv (onSecond (teleportCorrection a b))
        (postMeasure (a, b) (teleportEntangledState Ψ)) = Ψ :=
  ⟨measure_teleportEntangledState_map_fst Ψ hΨ, teleportCorrection_postMeasure_entangled Ψ hΨ⟩

end Entangled

end Cslib.Quantum
