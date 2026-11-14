/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Basic
public import CslibFrontier.Probability.IID
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.Uniform.Translate

/-!
# AND, OR, and parallel composition of Sigma protocols

Two Sigma protocols with a common challenge type combine into protocols proving knowledge of
witnesses for both statements, or for at least one of them, without revealing which
([BonehShoup2023], Section 19.7). A single Sigma protocol also composes with itself in `k`-fold
parallel repetition on the same statement with independent challenges `Fin k → C`
([BonehShoup2023], Exercise 19.6, pp. 810–811; our `parallelRepetition` allows `k = 0`, whereas
Exercise 19.6 assumes `k ≥ 1`).

The AND-proof runs both protocols in parallel and sends the same challenge to both. The OR-proof
needs the challenges to form a finite additive group; Boneh and Shoup use `{0, 1}ⁿ` with
exclusive or, which is the bit-string group with `+`. A prover with a witness for one statement
simulates the other side with a challenge of its own choice, and answers the verifier's
challenge `c` by splitting it as `c₀ + c₁`. A witness for the OR relation is `Sum.inl x₀` or
`Sum.inr x₁`. The honest OR prover is determined by the two simulators, which are therefore
parameters of `orProof`. In `k`-fold parallel repetition (`parallelRepetition`), the prover draws
`k` independent commitments, answers each coordinate challenge `c j` independently, and extraction
uses the first coordinate `j : Fin k` where the two challenge tuples differ.

## Main definitions

* `SigmaProtocol.andProof`, `SigmaProtocol.andExtract`, `SigmaProtocol.andSimulate`.
* `SigmaProtocol.orRelation`, `SigmaProtocol.orProof`, `SigmaProtocol.orExtract`,
  `SigmaProtocol.orSimulate`.
* `SigmaProtocol.parallelRepetition`, `SigmaProtocol.parallelExtract`,
  `SigmaProtocol.parallelSimulate`.

## Main results

* `SigmaProtocol.andProof_complete`, `SigmaProtocol.andProof_specialSoundness`,
  `SigmaProtocol.andProof_specialHVZK`: Theorem 19.18.
* `SigmaProtocol.orProof_complete`, `SigmaProtocol.orProof_specialSoundness`,
  `SigmaProtocol.orProof_specialHVZK`: Theorem 19.19.
* `SigmaProtocol.parallelRepetition_complete`, `SigmaProtocol.parallelRepetition_specialSoundness`,
  `SigmaProtocol.parallelRepetition_specialHVZK`: parallel repetition preserves completeness,
  special soundness, and special HVZK.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 19.6 (pp. 810–811) and Section 19.7.
* [R. Cramer, I. Damgård, B. Schoenmakers, *Proofs of Partial Knowledge and Simplified Design
  of Witness Hiding Protocols*][CramerDamgardSchoenmakers1994]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

universe u

variable {X₀ Y₀ T₀ Z₀ X₁ Y₁ T₁ Z₁ C : Type u}

/-! ### AND -/

section And

/-- The AND-proof ([BonehShoup2023], Section 19.7.1): commit with both provers and answer the
shared challenge with both. -/
noncomputable def andProof (P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀)
    (P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁) :
    SigmaProtocol (X₀ × X₁) (Y₀ × Y₁) (T₀ × T₁) C (Z₀ × Z₁) where
  State := P₀.State × P₁.State
  commit x y := do
    let a ← P₀.commit x.1 y.1
    let b ← P₁.commit x.2 y.2
    return ((a.1, b.1), (a.2, b.2))
  respond x y s c := (P₀.respond x.1 y.1 s.1 c, P₁.respond x.2 y.2 s.2 c)
  verify y t c z := P₀.verify y.1 t.1 c z.1 && P₁.verify y.2 t.2 c z.2

/-- The AND extractor applies each extractor to its half of the conversations. -/
def andExtract {W₀ W₁ : Type u} (extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → W₀)
    (extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → W₁) (y : Y₀ × Y₁) (t : T₀ × T₁) (c : C)
    (z : Z₀ × Z₁) (c' : C) (z' : Z₀ × Z₁) : W₀ × W₁ :=
  (extract₀ y.1 t.1 c z.1 c' z'.1, extract₁ y.2 t.2 c z.2 c' z'.2)

/-- The AND simulator runs both simulators independently at the shared challenge. -/
noncomputable def andSimulate (simulate₀ : Y₀ → C → PMF (T₀ × Z₀))
    (simulate₁ : Y₁ → C → PMF (T₁ × Z₁)) (y : Y₀ × Y₁) (c : C) :
    PMF ((T₀ × T₁) × (Z₀ × Z₁)) := do
  let a ← simulate₀ y.1 c
  let b ← simulate₁ y.2 c
  return ((a.1, b.1), (a.2, b.2))

variable {P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁}
  {R₀ : X₀ → Y₀ → Prop} {R₁ : X₁ → Y₁ → Prop}

/-- An AND conversation is accepting exactly when both halves are accepting at the shared
challenge. -/
@[simp] theorem andProof_accepts_iff {y : Y₀ × Y₁} {t : T₀ × T₁} {c : C} {z : Z₀ × Z₁} :
    (P₀.andProof P₁).Accepts y t c z ↔ P₀.Accepts y.1 t.1 c z.1 ∧ P₁.Accepts y.2 t.2 c z.2 := by
  simp only [Accepts, andProof, Bool.and_eq_true]

/-- The AND-proof's honest transcript pairs independent honest transcripts at the shared
challenge. -/
theorem andProof_transcript (x : X₀ × X₁) (y : Y₀ × Y₁) (c : C) :
    (P₀.andProof P₁).transcript x y c = do
      let a ← P₀.transcript x.1 y.1 c
      let b ← P₁.transcript x.2 y.2 c
      return ((a.1, b.1), (a.2, b.2)) := by
  simp only [pmf_norm, transcript, andProof]

/-- Theorem 19.18 of [BonehShoup2023]: completeness. -/
theorem andProof_complete (h₀ : P₀.Complete R₀) (h₁ : P₁.Complete R₁) :
    (P₀.andProof P₁).Complete fun x y => R₀ x.1 y.1 ∧ R₁ x.2 y.2 := by
  rintro x y ⟨hx₀, hx₁⟩ c tz htz
  simp only [andProof_transcript, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
  obtain ⟨a, ha, b, hb, rfl⟩ := htz
  exact andProof_accepts_iff.mpr ⟨h₀ _ _ hx₀ c a ha, h₁ _ _ hx₁ c b hb⟩

/-- Theorem 19.18 of [BonehShoup2023]: special soundness. -/
theorem andProof_specialSoundness {W₀ W₁ : Type u} {R₀' : W₀ → Y₀ → Prop} {R₁' : W₁ → Y₁ → Prop}
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → W₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → W₁} (h₀ : P₀.SpecialSoundness R₀' extract₀)
    (h₁ : P₁.SpecialSoundness R₁' extract₁) :
    (P₀.andProof P₁).SpecialSoundness (fun x y => R₀' x.1 y.1 ∧ R₁' x.2 y.2)
      (andExtract extract₀ extract₁) := by
  intro y t c z c' z' hc hz hz'
  rw [andProof_accepts_iff] at hz hz'
  exact ⟨h₀ _ _ _ _ _ _ hc hz.1 hz'.1, h₁ _ _ _ _ _ _ hc hz.2 hz'.2⟩

/-- Theorem 19.18 of [BonehShoup2023]: special honest-verifier zero knowledge. -/
theorem andProof_specialHVZK {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)}
    {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)} (h₀ : P₀.SpecialHVZK R₀ simulate₀)
    (h₁ : P₁.SpecialHVZK R₁ simulate₁) :
    (P₀.andProof P₁).SpecialHVZK (fun x y => R₀ x.1 y.1 ∧ R₁ x.2 y.2)
      (andSimulate simulate₀ simulate₁) where
  accepts y c tz htz := by
    simp only [andSimulate, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
    obtain ⟨a, ha, b, hb, rfl⟩ := htz
    exact andProof_accepts_iff.mpr ⟨h₀.accepts _ _ a ha, h₁.accepts _ _ b hb⟩
  transcript_eq x y hxy c := by
    rw [andProof_transcript, andSimulate, h₀.transcript_eq _ _ hxy.1,
      h₁.transcript_eq _ _ hxy.2]

end And

/-! ### OR -/

section Or

/-- The OR relation: a witness for the first statement or a witness for the second
([BonehShoup2023], Equation 19.23). -/
def orRelation (R₀ : X₀ → Y₀ → Prop) (R₁ : X₁ → Y₁ → Prop) : X₀ ⊕ X₁ → Y₀ × Y₁ → Prop
  | .inl x, y => R₀ x y.1
  | .inr x, y => R₁ x y.2

variable [AddCommGroup C] [Fintype C]

/-- The OR-proof ([BonehShoup2023], Section 19.7.2). With a witness for one side, the prover
simulates the other side at a uniform challenge `c'`, commits honestly on its own side, and
answers the verifier's challenge `c` on its own side at `c - c'`. The response
`(c₀, z₀, z₁)` names the first side's challenge; the second side's is `c - c₀`. -/
noncomputable def orProof (P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀) (P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁)
    (simulate₀ : Y₀ → C → PMF (T₀ × Z₀)) (simulate₁ : Y₁ → C → PMF (T₁ × Z₁)) :
    SigmaProtocol (X₀ ⊕ X₁) (Y₀ × Y₁) (T₀ × T₁) C (C × Z₀ × Z₁) where
  State := (X₀ × P₀.State × C × Z₁) ⊕ (X₁ × P₁.State × C × Z₀)
  commit
    | .inl x, y => do
      let c₁ ← PMF.uniformOfFintype C
      let b ← simulate₁ y.2 c₁
      let a ← P₀.commit x y.1
      return ((a.1, b.1), .inl (x, a.2, c₁, b.2))
    | .inr x, y => do
      let c₀ ← PMF.uniformOfFintype C
      let a ← simulate₀ y.1 c₀
      let b ← P₁.commit x y.2
      return ((a.1, b.1), .inr (x, b.2, c₀, a.2))
  respond _ y s c := match s with
    | .inl (x, s₀, c₁, z₁) => (c - c₁, P₀.respond x y.1 s₀ (c - c₁), z₁)
    | .inr (x, s₁, c₀, z₀) => (c₀, z₀, P₁.respond x y.2 s₁ (c - c₀))
  verify y t c
    | (c₀, z₀, z₁) => P₀.verify y.1 t.1 c₀ z₀ && P₁.verify y.2 t.2 (c - c₀) z₁

/-- The OR extractor uses the first side when the first side's challenges differ, and the
second side otherwise. -/
def orExtract [DecidableEq C] {W₀ W₁ : Type u} (extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → W₀)
    (extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → W₁) (y : Y₀ × Y₁) (t : T₀ × T₁) (c : C)
    (z : C × Z₀ × Z₁) (c' : C) (z' : C × Z₀ × Z₁) : W₀ ⊕ W₁ :=
  let (c₀, z₀, z₁) := z
  let (c₀', z₀', z₁') := z'
  if c₀ = c₀' then .inr (extract₁ y.2 t.2 (c - c₀) z₁ (c' - c₀') z₁')
  else .inl (extract₀ y.1 t.1 c₀ z₀ c₀' z₀')

/-- The OR simulator splits the challenge uniformly and simulates both sides. -/
noncomputable def orSimulate (simulate₀ : Y₀ → C → PMF (T₀ × Z₀))
    (simulate₁ : Y₁ → C → PMF (T₁ × Z₁)) (y : Y₀ × Y₁) (c : C) :
    PMF ((T₀ × T₁) × C × Z₀ × Z₁) := do
  let c₀ ← PMF.uniformOfFintype C
  let a ← simulate₀ y.1 c₀
  let b ← simulate₁ y.2 (c - c₀)
  return ((a.1, b.1), c₀, a.2, b.2)

variable {P₀ : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ : SigmaProtocol X₁ Y₁ T₁ C Z₁}
  {R₀ : X₀ → Y₀ → Prop} {R₁ : X₁ → Y₁ → Prop}
  {simulate₀ : Y₀ → C → PMF (T₀ × Z₀)} {simulate₁ : Y₁ → C → PMF (T₁ × Z₁)}

/-- An OR conversation `(c₀, z₀, z₁)` for the challenge `c` is accepting exactly when the first
side accepts at `c₀` and the second at `c - c₀`. -/
@[simp] theorem orProof_accepts_iff {y : Y₀ × Y₁} {t : T₀ × T₁} {c c₀ : C} {z₀ : Z₀} {z₁ : Z₁} :
    (orProof P₀ P₁ simulate₀ simulate₁).Accepts y t c (c₀, z₀, z₁) ↔
      P₀.Accepts y.1 t.1 c₀ z₀ ∧ P₁.Accepts y.2 t.2 (c - c₀) z₁ := by
  simp only [Accepts, orProof, Bool.and_eq_true]

/-- With a witness for the first statement, the OR prover simulates the second side at a
uniform challenge and answers honestly on the first side. -/
theorem orProof_transcript_inl (x : X₀) (y : Y₀ × Y₁) (c : C) :
    (orProof P₀ P₁ simulate₀ simulate₁).transcript (.inl x) y c = do
      let c₁ ← PMF.uniformOfFintype C
      let b ← simulate₁ y.2 c₁
      let a ← P₀.transcript x y.1 (c - c₁)
      return ((a.1, b.1), c - c₁, a.2, b.2) := by
  simp only [pmf_norm, transcript, orProof]

/-- With a witness for the second statement, the OR prover simulates the first side at a
uniform challenge and answers honestly on the second side. -/
theorem orProof_transcript_inr (x : X₁) (y : Y₀ × Y₁) (c : C) :
    (orProof P₀ P₁ simulate₀ simulate₁).transcript (.inr x) y c = do
      let c₀ ← PMF.uniformOfFintype C
      let a ← simulate₀ y.1 c₀
      let b ← P₁.transcript x y.2 (c - c₀)
      return ((a.1, b.1), c₀, a.2, b.2) := by
  simp only [pmf_norm, transcript, orProof]

/-- Theorem 19.19 of [BonehShoup2023]: completeness. It uses that both simulators output
accepting conversations. -/
theorem orProof_complete (h₀ : P₀.Complete R₀) (h₁ : P₁.Complete R₁)
    (hs₀ : P₀.SpecialHVZK R₀ simulate₀) (hs₁ : P₁.SpecialHVZK R₁ simulate₁) :
    (orProof P₀ P₁ simulate₀ simulate₁).Complete (orRelation R₀ R₁) := by
  rintro (x | x) y hxy c tz htz
  · simp only [orProof_transcript_inl, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
    obtain ⟨c₁, -, b, hb, a, ha, rfl⟩ := htz
    refine orProof_accepts_iff.mpr ⟨h₀ x y.1 hxy (c - c₁) a ha, ?_⟩
    simpa only [sub_sub_cancel] using hs₁.accepts y.2 c₁ b hb
  · simp only [orProof_transcript_inr, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
    obtain ⟨c₀, -, a, ha, b, hb, rfl⟩ := htz
    exact orProof_accepts_iff.mpr ⟨hs₀.accepts y.1 c₀ a ha, h₁ x y.2 hxy (c - c₀) b hb⟩

/-- Theorem 19.19 of [BonehShoup2023]: special soundness. Distinct challenges differ on the
first side's challenge or on the second side's. -/
theorem orProof_specialSoundness [DecidableEq C] {W₀ W₁ : Type u}
    {R₀' : W₀ → Y₀ → Prop} {R₁' : W₁ → Y₁ → Prop}
    {extract₀ : Y₀ → T₀ → C → Z₀ → C → Z₀ → W₀}
    {extract₁ : Y₁ → T₁ → C → Z₁ → C → Z₁ → W₁} (h₀ : P₀.SpecialSoundness R₀' extract₀)
    (h₁ : P₁.SpecialSoundness R₁' extract₁) :
    (orProof P₀ P₁ simulate₀ simulate₁).SpecialSoundness (orRelation R₀' R₁')
      (orExtract extract₀ extract₁) := by
  intro y t c z c' z' hc hz hz'
  rw [orProof_accepts_iff] at hz hz'
  by_cases h : z.1 = z'.1
  · rw [orExtract, ite_eq_left h]
    refine h₁ _ _ _ _ _ _ ?_ hz.2 hz'.2
    rwa [h, Ne, sub_left_inj]
  · rw [orExtract, ite_eq_right h]
    exact h₀ _ _ _ _ _ _ h hz.1 hz'.1

/-- Theorem 19.19 of [BonehShoup2023]: special honest-verifier zero knowledge. The honest
prover's own-side challenge `c - c'` is uniform, and its own-side transcript is replaced by a
simulation. -/
theorem orProof_specialHVZK (hs₀ : P₀.SpecialHVZK R₀ simulate₀)
    (hs₁ : P₁.SpecialHVZK R₁ simulate₁) :
    (orProof P₀ P₁ simulate₀ simulate₁).SpecialHVZK (orRelation R₀ R₁)
      (orSimulate simulate₀ simulate₁) where
  accepts y c tz htz := by
    simp only [orSimulate, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
    obtain ⟨c₀, -, a, ha, b, hb, rfl⟩ := htz
    exact orProof_accepts_iff.mpr ⟨hs₀.accepts _ _ a ha, hs₁.accepts _ _ b hb⟩
  transcript_eq
    | .inl x, y, hxy, c => by
      rw [orProof_transcript_inl, orSimulate]
      simp only [← hs₀.transcript_eq x y.1 hxy, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      conv_lhs => rw [← PMF.uniformOfFintype_map_sub_left c, PMF.bind_map]
      simp only [Function.comp_def, sub_sub_cancel]
      exact congrArg _ (funext fun _ => PMF.bind_comm _ _ _)
    | .inr x, y, hxy, c => by
      rw [orProof_transcript_inr, orSimulate]
      simp only [hs₁.transcript_eq x y.2 hxy]

end Or

/-! ### Parallel repetition -/

section Parallel

variable {X Y T Z : Type u}

/-- `k`-fold parallel repetition of a Sigma protocol `P` on the same statement with independent
challenges ([BonehShoup2023], Exercise 19.6, pp. 810–811; allowing `k = 0`): commit `k` independent
times, answer each coordinate challenge `c j` independently, and verify all `k` coordinates. -/
noncomputable def parallelRepetition (P : SigmaProtocol X Y T C Z) (k : ℕ) :
    SigmaProtocol X Y (Fin k → T) (Fin k → C) (Fin k → Z) where
  State := Fin k → P.State
  commit x y := (PMF.iid (P.commit x y) k).map fun ts => (fun j => (ts j).1, fun j => (ts j).2)
  respond x y s c := fun j => P.respond x y (s j) (c j)
  verify y t c z := (List.finRange k).all fun j => P.verify y (t j) (c j) (z j)

/-- The parallel-repetition extractor finds the first coordinate `j : Fin k` where the two
challenge tuples differ and runs `extract` on that coordinate's conversations. -/
def parallelExtract [DecidableEq C] {W : Type u} [Inhabited W]
    (extract : Y → T → C → Z → C → Z → W) (k : ℕ) (y : Y) (t : Fin k → T) (c : Fin k → C)
    (z : Fin k → Z) (c' : Fin k → C) (z' : Fin k → Z) : W :=
  match (List.finRange k).find? (fun j => c j != c' j) with
  | some j => extract y (t j) (c j) (z j) (c' j) (z' j)
  | none => default

/-- The parallel-repetition simulator runs `simulate` independently at each coordinate challenge
`c j`. -/
noncomputable def parallelSimulate (simulate : Y → C → PMF (T × Z)) (k : ℕ) (y : Y)
    (c : Fin k → C) : PMF ((Fin k → T) × (Fin k → Z)) :=
  (PMF.piFin fun j => simulate y (c j)).map fun tz => (fun j => (tz j).1, fun j => (tz j).2)

variable {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}

/-- A parallel-repetition conversation is accepting iff every coordinate conversation is accepting.
-/
@[simp] theorem parallelRepetition_accepts_iff {k : ℕ} {y : Y} {t : Fin k → T} {c : Fin k → C}
    {z : Fin k → Z} :
    (P.parallelRepetition k).Accepts y t c z ↔ ∀ j : Fin k, P.Accepts y (t j) (c j) (z j) := by
  simp only [Accepts, parallelRepetition, List.all_eq_true, List.mem_finRange, forall_const]

/-- The honest transcript of `parallelRepetition` is the coordinatewise product of the honest
transcripts at `c j`. -/
theorem parallelRepetition_transcript (k : ℕ) (x : X) (y : Y) (c : Fin k → C) :
    (P.parallelRepetition k).transcript x y c =
      (PMF.piFin fun j => P.transcript x y (c j)).map
        fun tz => (fun j => (tz j).1, fun j => (tz j).2) := by
  simp only [transcript, parallelRepetition, PMF.piFin_map, PMF.piFin_const, PMF.map_comp]
  rfl

/-- Completeness is preserved under `k`-fold parallel repetition. -/
theorem parallelRepetition_complete {k : ℕ} (h : P.Complete R) :
    (P.parallelRepetition k).Complete R := by
  intro x y hxy c tz htz
  rw [parallelRepetition_transcript, PMF.mem_support_map_iff] at htz
  obtain ⟨v, hv, rfl⟩ := htz
  rw [PMF.mem_support_piFin_iff] at hv
  exact parallelRepetition_accepts_iff.mpr fun j => h x y hxy (c j) (v j) (hv j)

/-- Special soundness is preserved under `k`-fold parallel repetition: two distinct challenge
tuples `c ≠ c'` must differ at some coordinate `j : Fin k`. -/
theorem parallelRepetition_specialSoundness [DecidableEq C] {W : Type u} [Inhabited W] {k : ℕ}
    {R' : W → Y → Prop} {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R' extract) :
    (P.parallelRepetition k).SpecialSoundness R' (parallelExtract extract k) := by
  intro y t c z c' z' hc hz hz'
  rw [parallelRepetition_accepts_iff] at hz hz'
  unfold parallelExtract
  cases hfind : (List.finRange k).find? (fun j => c j != c' j) with
  | none =>
    exfalso
    apply hc
    funext j
    have hj := List.find?_eq_none.mp hfind j (List.mem_finRange j)
    simpa using hj
  | some j =>
    have hj : c j ≠ c' j := by
      simpa using List.find?_some hfind
    exact h y (t j) (c j) (z j) (c' j) (z' j) hj (hz j) (hz' j)

/-- Special honest-verifier zero knowledge is preserved under `k`-fold parallel repetition. -/
theorem parallelRepetition_specialHVZK {k : ℕ} {simulate : Y → C → PMF (T × Z)}
    (h : P.SpecialHVZK R simulate) :
    (P.parallelRepetition k).SpecialHVZK R (parallelSimulate simulate k) where
  accepts y c tz htz := by
    unfold parallelSimulate at htz
    rw [PMF.mem_support_map_iff] at htz
    obtain ⟨v, hv, rfl⟩ := htz
    rw [PMF.mem_support_piFin_iff] at hv
    exact parallelRepetition_accepts_iff.mpr fun j => h.accepts y (c j) (v j) (hv j)
  transcript_eq x y hxy c := by
    rw [parallelRepetition_transcript, parallelSimulate]
    simp only [h.transcript_eq x y hxy]

end Parallel

end Cslib.Crypto.Protocols.SigmaProtocol
