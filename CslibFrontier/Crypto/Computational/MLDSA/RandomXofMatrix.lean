/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.ExpandAProgramming
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import CslibFrontier.Probability.PMF.UniformExtend

/-!
# Drawing the ML-DSA matrix inside the shared random-XOF game

[FIPS 204][NISTFIPS204], Algorithm 6 derives the public seed through SHAKE256 and reads
its matrix under SHAKE128. Conditional on that seed, the matrix addresses are distinct entries
of the independent SHAKE128 table. Resampling the 894-byte prefixes there preserves the
distribution of the entire pair of raw oracles, including every longer and overlapping read.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability ExtendableOutput

private abbrev MatrixByte (s : Level) := Cell s × Fin 894

private def flatten (s : Level) : MatrixPrefixes s ≃ (MatrixByte s → Byte) where
  toFun t p := t p.1.1 p.1.2 p.2
  invFun f i j k := f ((i, j), k)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem address_length (rho : List Byte) {s : Level} (p : Cell s) :
    (address rho p).length = 8 * (rho.length + 2) := by
  simp [address, Keccak.length_bytesToBitsLE]

private def point {a b : ℕ} {s : Level} (rho : List Byte) (ha : 8 * (rho.length + 2) ≤ a)
    (hb : 894 ≤ b) (p : MatrixByte s) : RawWord a × Fin b :=
  (word (address rho p.1) ((address_length ..).le.trans ha), Fin.castLE hb p.2)

private theorem point_injective {a b : ℕ} {s : Level} (rho : List Byte)
    (ha : 8 * (rho.length + 2) ≤ a) (hb : 894 ≤ b) :
    Function.Injective (point (s := s) rho ha hb) := by
  intro p q h
  have hx := word_inj (hx := ((address_length rho p.1).le.trans ha))
    (hy := ((address_length rho q.1).le.trans ha)) (congrArg Prod.fst h)
  have hc := congrArg (cellAt s rho) hx
  simp only [cellAt_address, Option.some.injEq] at hc
  exact Prod.ext hc (Fin.ext (congrArg (fun v => v.2.val) h))

private theorem overwrite {a b : ℕ} {s : Level} (base : Xofs) (t : Table a b)
    (rho : List Byte) (ha : 8 * (rho.length + 2) ≤ a) (hb : 894 ≤ b) (g : MatrixPrefixes s) :
    ({base with h128 := install base.h128 t} : Xofs).withMatrixPrefixes s rho g =
      {base with
        h128 := install base.h128 (Function.extend (point rho ha hb) (flatten s g) t)} := by
  unfold Xofs.withMatrixPrefixes
  apply congrArg (fun stream => Xofs.mk stream base.h256)
  apply ext_byteAt
  intro x i
  change byteAt ((install base.h128 t).withPrefixes _) x i = _
  rw [byteAt_withPrefixes]
  simp only [byteAt_install]
  by_cases h : x.length ≤ a ∧ i < b
  · simp only [dite_eq_left h]
    let z : RawWord a × Fin b := (word x h.1, ⟨i, h.2⟩)
    by_cases hit : ∃ p : MatrixByte s, point rho ha hb p = z
    · obtain ⟨p, hp⟩ := hit
      have hx := word_inj (hx := (address_length rho p.1).le.trans ha) (hy := h.1)
        (congrArg Prod.fst hp)
      have hi : p.2.val = i := congrArg (fun z => z.2.val) hp
      change _ = Function.extend (point rho ha hb) (flatten s g) t z
      rw [← hp, (point_injective rho ha hb).extend_apply]
      subst x; subst i
      simp only [cellAt_address, Option.map_some, Option.bind_some, List.getElem?_ofFn,
        dite_eq_left p.2.isLt, Option.getD_some, flatten, Equiv.coe_fn_mk, Fin.eta]
    · change _ = Function.extend (point rho ha hb) (flatten s g) t z
      rw [Function.extend_apply' _ _ _ hit]
      cases hc : cellAt s rho x with
      | none => rfl
      | some cell =>
        have hi : ¬ i < 894 := by
          intro small
          apply hit
          refine ⟨(cell, ⟨i, small⟩), ?_⟩
          obtain rfl := address_of_cellAt hc
          rfl
        simp only [Option.map_some, Option.bind_some, List.getElem?_ofFn, dite_eq_right hi,
          Option.getD_none, z]
  · simp only [dite_eq_right h]
    cases hc : cellAt s rho x with
    | none => rfl
    | some cell =>
      have ha' : x.length ≤ a := by rw [← address_of_cellAt hc, address_length]; exact ha
      have hi : ¬ i < 894 := fun small => h ⟨ha', small.trans_le hb⟩
      simp only [Option.map_some, Option.bind_some, List.getElem?_ofFn, dite_eq_right hi,
        Option.getD_none]

private theorem resample_at_seed {a b : ℕ} {s : Level} (base : Xofs) (rho : List Byte)
    (ha : 8 * (rho.length + 2) ≤ a) (hb : 894 ≤ b) {α : Type} (k : Xofs → PMF α) :
    ((PMF.uniformOfFintype (Table a b)).bind fun t =>
      (PMF.uniformOfFintype (MatrixPrefixes s)).bind fun g =>
        k (({base with h128 := install base.h128 t} : Xofs).withMatrixPrefixes s rho g)) =
      (PMF.uniformOfFintype (Table a b)).bind fun t =>
        k {base with h128 := install base.h128 t} := by
  let finish (t : Table a b) := k {base with h128 := install base.h128 t}
  have eq := PMF.uniformOfFintype_bind_bind_extend (κ := Byte)
    (point (s := s) rho ha hb) finish
  rw [← PMF.uniformOfFintype_map_equiv (flatten s)] at eq
  simpa only [overwrite base _ rho ha hb, PMF.bind_map, finish, Function.comp_def] using eq

/-- Resampling the SHAKE128 matrix rows at the public FIPS seed preserves every continuation
of the joint XOFs and original 32-byte key seed, including later adaptive queries. -/
theorem uniformPrefixes_resampleMatrix (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) {α : Type} (run : Xofs → FixedBytes 32 → PMF α) :
    let R := base.uniformPrefixes a b
    let S := PMF.uniformOfFintype (FixedBytes 32)
    (R.bind fun H => S.bind fun seed =>
      (PMF.uniformOfFintype (MatrixPrefixes s)).bind fun t =>
        run (H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) t) seed) =
      R.bind fun H => S.bind fun seed => run H seed := by
  intro R S
  let U := PMF.uniformOfFintype (Table a b)
  simp only [R, independent_tables, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.bind U ·)
  funext t
  rw [PMF.bind_comm U S, PMF.bind_comm U S]
  apply congrArg (PMF.bind S ·)
  funext seed
  let G : Xofs := {base with h256 := install base.h256 t}
  let rho := (G.expandKeySeed s seed).take 32
  have len : rho.length ≤ 32 := List.length_take_le ..
  exact resample_at_seed (s := s) G rho (by lia) hb (fun H => run H seed)

private def readSetup (s : Level) (H : Xofs) (seed : FixedBytes 32) :
    Xofs × Option (PublicMatrix s × KeyPair) := (H, do
  let keys ← H.keyGen s seed
  let A ← H.expandA s (keys.publicKey.take 32)
  return (A, keys))

/-- Sampling the independent FIPS matrix prefixes inside an already sampled pair of random
XOFs preserves their entire joint law with the honest public matrix and key pair. The table
covers every 34-byte matrix input and its first 894 output bytes. -/
theorem uniformPrefixes_matrixSetup (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) :
    ((base.uniformPrefixes a b).bind fun H => matrixSetup H s) =
      (base.uniformPrefixes a b).bind (fun H =>
        (PMF.uniformOfFintype (FixedBytes 32)).map fun seed => (H, do
          let keys ← H.keyGen s seed
          let A ← H.expandA s (keys.publicKey.take 32)
          return (A, keys))) := by
  simpa only [matrixSetup, readSetup, PMF.map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    Function.comp_def] using
    uniformPrefixes_resampleMatrix base s ha hb (fun H seed => PMF.pure (readSetup s H seed))

namespace QuantumSigningForger

private theorem forgery_from_setup (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (seed : FixedBytes 32) :
    ((C.runAtSetup s (readSetup s H seed)).map (·.any SignedMatrixTrial.wins)) =
      match H.keyGen s seed with
      | none => PMF.pure false
      | some keys => (C.transcript H s keys).map fun (f, log) =>
          H.winsForgery s keys.publicKey f log := by
  cases hg : H.keyGen s seed with
  | none => simp [readSetup, hg, runAtSetup]
  | some keys =>
    obtain ⟨rho, sk, hm, pk, _, _⟩ := privateKey_of_keyGen hg
    have mat : H.expandA s (keys.publicKey.take 32) = some sk.A := by
      rwa [pk, take_encodePublic]
    simp [readSetup, hg, mat, runAtSetup, PMF.map_comp, SignedMatrixTrial.wins, Function.comp_def]

/-- Equality of the strong-forgery game sampled before the seed with the averaged
matrix-prefix game. The equality holds for the full adaptive quantum experiment. -/
theorem randomPrefixGame_eq_matrixTrial (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b : ℕ} (ha : 272 ≤ a) (hb : 894 ≤ b) :
    C.randomPrefixGame s base a b = (base.uniformPrefixes a b).bind fun H =>
      (C.matrixTrial s H).map (·.any SignedMatrixTrial.wins) := by
  have joint : ((base.uniformPrefixes a b).bind fun H => matrixSetup H s) =
      (base.uniformPrefixes a b).bind (fun H =>
        (PMF.uniformOfFintype (FixedBytes 32)).map (readSetup s H)) :=
    uniformPrefixes_matrixSetup base s ha hb
  have eq := congrArg (fun p => PMF.bind p fun z =>
    (C.runAtSetup s z).map (·.any SignedMatrixTrial.wins)) joint
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, forgery_from_setup] at eq
  unfold randomPrefixGame forgeryGame Xofs.keyExperiment
  simp only [matrixTrial, PMF.monad_bind_eq_bind, PMF.map_bind]
  rw [eq]
  apply congrArg (fun f => (base.uniformPrefixes a b).bind f)
  funext H
  apply congrArg (fun f => (PMF.uniformOfFintype (FixedBytes 32)).bind f)
  funext seed
  cases H.keyGen s seed <;> rfl

/-- The strong-forgery probability in the finite random-XOF experiment is bounded by the
fresh-digest and raw SHAKE256 collision events and by the success of the extracted vector on
an independently supplied uniform Hermite MSIS matrix. The solver draws its own pair of
tables and runs the quantum forger once. All three terms retain the original signing access. -/
theorem randomPrefixGame_forgery_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 272 ≤ a) (hb : 894 ≤ b) :
    let R := base.uniformPrefixes a b
    let trial := R.bind (C.matrixTrial s)
    Game.succProbability (C.randomPrefixGame s base a b) ≤
      Game.succProbability (trial.map (·.any SignedMatrixTrial.newDigestWin)) +
      (Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
        Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
          ((R.bind fun H => C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
            (ModuleSIS.hermiteMatrix A) (max (2 * (s.params.γ₁ - s.params.β))
              (4 * s.params.γ₂ + 2)) v)))) := by
  intro R trial
  let run (A : PublicMatrix s) := R.bind fun H => C.programmedTrial s H A
  have eq : (PMF.uniformOfFintype (PublicMatrix s)).bind run = trial := by
    unfold run trial
    rw [PMF.bind_comm]
    simp only [C.uniform_programmedTrial]
  have bound := SignedMatrixTrial.bound_of_verifiedLog run (by
    intro A u hu
    obtain ⟨H, _, h⟩ := (PMF.mem_support_bind_iff ..).mp hu
    exact (C.verified_programmedTrial h).2)
  dsimp only at bound
  rw [eq] at bound
  rw [randomPrefixGame_eq_matrixTrial C s base ha hb, ← PMF.map_bind]
  simpa only [run, trial, R, matrixSolver, PMF.map_bind, PMF.map_comp,
    Function.comp_def] using bound

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
