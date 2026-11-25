/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.MultivariateQuadratic
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
public import CslibFrontier.Crypto.Protocols.UOV.Games
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import CslibFrontier.Probability.PMF.Support
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Rescaling attacks against homogeneous preimage games

`rescaleAttack` makes one oracle call and scales the answer. For a homogeneous quadratic
public map `P`, its two instantiations distinguish security notions that must not be confused:

* `rescaleAttack_freshTarget` queries `a⁻² • y` and returns a preimage of `y`. It succeeds with
  probability one, for every correct answer distribution, when `y ≠ 0`, `a ≠ 0`, and `a² ≠ 1`.
  Thus producing a preimage of an *unqueried target* is not a suitable one-more UOV game.
* `rescaleAttack_zeroOpening` queries the structured message and opening `(w, 0)`. If both
  blocks vanish at zero, its scaled answer certifies the fresh semantic message `a² • w` at the
  same opening. This is the algebraic attack on the earlier VOLE-ACT-MQ target family.

`structuredTarget F G w r = (F r + w, G r)` makes the semantic message separate from its
opening. The blocks may be arbitrary functions: only their values at zero matter here, so the
same interface covers both homogeneous and inhomogeneous quadratic blocks. A nonzero tail at
zero blocks this specific fixed-opening rescaling (`rescale_ne_zeroOpening_of_tail_ne_zero`);
it is not a security theorem for the corrected construction.

The attack programs and their exact probabilities are original game-level results. The rescaling
results require correct oracle answers only on the single query made, and do not implement a UOV
signer. The raw zero-target forgery does not query the oracle or require its correctness. Their
query certificates bound external calls, not running time. Classical-ROM hash-and-sign
composition for abstract trapdoor preimage systems (including `UOV.idealRawScheme`) is supplied in
`Cslib.Crypto.UOV.HashAndSign`, while the concrete round-3 UOV signer, concrete `Keccak-p[800, 12]`,
and runtime PPT certificates remain tracked in #4987 and #7068.

## Main definitions

* `Cslib.Crypto.UOV.rescaleAttack`: one oracle call followed by scalar multiplication.
* `Cslib.Crypto.UOV.structuredTarget`: the two-block ACT-MQ target expression.

## Main results

* `Cslib.Crypto.UOV.rescaleAttack_freshTarget`: certain success in the unqueried-target game.
* `Cslib.Crypto.UOV.rescaleAttack_zeroOpening`: certain fresh-message success when both blocks
  vanish at zero.
* `Cslib.Crypto.UOV.rescale_ne_zeroOpening_of_tail_ne_zero`: a nonzero tail blocks every
  nonidentity rescaling at the fixed zero opening.
* `Cslib.Crypto.UOV.verify_scale_of_quadratic`, `Cslib.Crypto.UOV.verify_scale_option_of_quadratic`:
  verification preservation under homogeneous quadratic rescaling when `F 0 = 0` and `G 0 = 0`.
* `Cslib.Crypto.UOV.eval_rawZeroForger`: raw UOV target EUF-CMA is broken without a query,
  by the known preimage zero of target zero, independently of the preimage oracle.

## References

* [VOLE-ACT][VOLEACT2026], "MQ zero-opening scaling forgery". The theorem abstracts the vector
  equation in that section; it does not encode balances as bytes or claim the concrete credit sum.
-/

public section

namespace Cslib.Crypto.UOV

open Probability

variable {K X Query : Type} [Field K] [AddCommGroup X] [Module K X]

/-- Ask the supplied oracle query once, and multiply its answer by `a`.
The query is explicit so the same program serves raw and structured preimage games. -/
@[expose] def rescaleAttack (a : K) (query : Query) :
    ProbOracleComp (fun _ : Query => X) X := do
  let answer ← ProbOracleComp.query query
  return a • answer

/-- The rescaling attack uses at most one external oracle call, independently of its reply. -/
theorem rescaleAttack_queryBound (a : K) (query : Query) :
    (rescaleAttack (X := X) a query).IsQueryBounded 1 :=
  ProbOracleComp.IsQueryBounded.query_bind_pure query (a • ·)

section RawTarget

variable {Y : Type} [AddCommGroup Y] [Module K Y] [DecidableEq Y]

/-- For a nonzero target, one correct answer at the inverse-squared target gives a valid
preimage of an unqueried target with probability one. This is an attack on that freshness game,
not on the fixed-budget one-more game that asks for more challenge preimages than queries. -/
theorem rescaleAttack_freshTarget (P : QuadraticMap K X Y) (a : K) (y : Y)
    (ha : a ≠ 0) (hsquare : a * a ≠ 1) (hy : y ≠ 0) (oracle : Y → ProbComp X)
    (hanswer : ∀ answer ∈ (ProbComp.eval (oracle ((a * a)⁻¹ • y))).support,
      P answer = (a * a)⁻¹ • y) :
    (ProbComp.eval ((rescaleAttack a ((a * a)⁻¹ • y)).runLog oracle)).map
      (fun result => decide (P result.1 = y ∧
        y ∉ result.2.map Prod.fst ∧ result.2.length = 1)) = PMF.pure true := by
  rw [rescaleAttack, ProbOracleComp.runLog_query_bind_pure, ProbComp.eval_map, PMF.map_comp]
  apply PMF.map_eq_pure_iff.mpr
  intro answer hmem
  have hvalid : P (a • answer) = y := by
    rw [P.map_smul, hanswer answer hmem, smul_smul,
      mul_inv_cancel₀ (mul_ne_zero ha ha), one_smul]
  have hfresh : (a * a)⁻¹ • y ≠ y := by
    intro heq
    have hinv : (a * a)⁻¹ = 1 :=
      smul_left_injective K hy (heq.trans (one_smul K y).symm)
    exact hsquare (inv_eq_one.mp hinv)
  exact decide_eq_true ⟨hvalid, by
    simpa only [List.map_cons, List.map_nil, List.mem_singleton] using Ne.symm hfresh, rfl⟩

end RawTarget

section StructuredTarget

variable {Message Tail Opening : Type} [AddCommGroup Message] [Module K Message]
  [AddCommGroup Tail] [Module K Tail] [Zero Opening]

/-- The ACT-MQ target: the semantic message is added to the first block of the opening map,
while the second block binds the opening. This expression also permits constant terms. -/
@[expose] def structuredTarget (front : Opening → Message) (tail : Opening → Tail)
    (message : Message) (opening : Opening) : Message × Tail :=
  (front opening + message, tail opening)

private theorem structuredTarget_smul_zeroOpening
    (P : QuadraticMap K X (Message × Tail))
    (front : Opening → Message) (tail : Opening → Tail)
    (hfront : front 0 = 0) (htail : tail 0 = 0)
    (a : K) {answer : X} {message : Message}
    (hanswer : P answer = structuredTarget front tail message 0) :
    P (a • answer) = structuredTarget front tail ((a * a) • message) 0 := by
  rw [P.map_smul, hanswer]
  simp [structuredTarget, hfront, htail]

/-- When both blocks vanish at zero, the one-call rescaling program certifies a fresh semantic
message with probability one. Freshness ignores the opening. This abstract vector statement
does not assert that scalar multiplication preserves an application's message-format predicate. -/
theorem rescaleAttack_zeroOpening [DecidableEq Message] [DecidableEq Tail]
    (P : QuadraticMap K X (Message × Tail))
    (front : Opening → Message) (tail : Opening → Tail)
    (hfront : front 0 = 0) (htail : tail 0 = 0)
    (a : K) (hsquare : a * a ≠ 1) (message : Message) (hmessage : message ≠ 0)
    (oracle : Message × Opening → ProbComp X)
    (hanswer : ∀ answer ∈ (ProbComp.eval (oracle (message, 0))).support,
      P answer = structuredTarget front tail message 0) :
    (ProbComp.eval ((rescaleAttack a (message, (0 : Opening))).runLog oracle)).map
      (fun result => decide
        (P result.1 = structuredTarget front tail ((a * a) • message) 0 ∧
          (a * a) • message ∉ result.2.map (fun ((msg, _), _) => msg) ∧
          result.2.length = 1)) = PMF.pure true := by
  rw [rescaleAttack, ProbOracleComp.runLog_query_bind_pure, ProbComp.eval_map, PMF.map_comp]
  apply PMF.map_eq_pure_iff.mpr
  intro answer hmem
  have hvalid : P (a • answer) = structuredTarget front tail ((a * a) • message) 0 :=
    structuredTarget_smul_zeroOpening P front tail hfront htail a (hanswer answer hmem)
  have hfresh : (a * a) • message ≠ message := by
    intro heq
    exact hsquare (smul_left_injective K hmessage (heq.trans (one_smul K message).symm))
  exact decide_eq_true ⟨hvalid, by
    simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hfresh, rfl⟩

/-- Scaling a valid raw preimage under a homogeneous quadratic map when `F 0 = 0` and `G 0 = 0`
yields a valid preimage for `(a * a) • μ` at opening `0`. -/
theorem verify_scale_of_quadratic {PK SK : Type} [DecidableEq Message] [DecidableEq Tail]
    (pubMap : PK → QuadraticMap K X (Message × Tail))
    (S : Signature.Scheme PK SK (Message × Tail) X)
    (hver : ∀ pk target s, S.verify pk target s = decide (pubMap pk s = target))
    (F : Opening → Message) (G : Opening → Tail) (hF : F 0 = 0) (hG : G 0 = 0)
    {pk : PK} {μ : Message} {s : X} (hs : S.verify pk (structuredTarget F G μ 0) s = true)
    (a : K) :
    S.verify pk (structuredTarget F G ((a * a) • μ) 0) (a • s) = true := by
  rw [hver] at hs ⊢
  exact decide_eq_true
    (structuredTarget_smul_zeroOpening (pubMap pk) F G hF hG a (of_decide_eq_true hs))

/-- Optional-preimage (`Option X`) scaling helper matching the verifier shape of
`UOV.idealRawScheme`: scaling with `Option.map (a • ·)` preserves validity under a homogeneous
quadratic verifier when `F 0 = 0` and `G 0 = 0`. -/
theorem verify_scale_option_of_quadratic {PK SK : Type} [DecidableEq Message] [DecidableEq Tail]
    (pubMap : PK → QuadraticMap K X (Message × Tail))
    (S : Signature.Scheme PK SK (Message × Tail) (Option X))
    (hver : ∀ pk target opt, S.verify pk target opt =
      match opt with | none => false | some s => decide (pubMap pk s = target))
    (F : Opening → Message) (G : Opening → Tail) (hF : F 0 = 0) (hG : G 0 = 0)
    {pk : PK} {μ : Message} {opt : Option X}
    (hopt : S.verify pk (structuredTarget F G μ 0) opt = true) (a : K) :
    S.verify pk (structuredTarget F G ((a * a) • μ) 0) (Option.map (a • ·) opt) = true := by
  cases opt with
  | none =>
    rw [hver] at hopt
    simp at hopt
  | some s =>
    rw [hver] at hopt ⊢
    exact decide_eq_true
      (structuredTarget_smul_zeroOpening (pubMap pk) F G hF hG a (of_decide_eq_true hopt))

/-- A nonzero tail at zero blocks this fixed-opening rescaling: no semantic message can make
the scaled preimage verify at opening zero when the squared scalar is not one.
This rules out only the specified attack, not other openings or other attacks. -/
theorem rescale_ne_zeroOpening_of_tail_ne_zero
    (P : QuadraticMap K X (Message × Tail))
    (front : Opening → Message) (tail : Opening → Tail)
    (htail : tail 0 ≠ 0) (a : K) (hsquare : a * a ≠ 1)
    {answer : X} {message : Message}
    (hanswer : P answer = structuredTarget front tail message 0) (message' : Message) :
    P (a • answer) ≠ structuredTarget front tail message' 0 := by
  intro heq
  rw [P.map_smul, hanswer] at heq
  apply hsquare
  apply smul_left_injective K htail
  simpa [structuredTarget] using congrArg Prod.snd heq

end StructuredTarget

/-! ## Raw certification is not a signature security assumption -/

/-- The all-zero preimage certifies target zero under every homogeneous UOV public map.
This attacker is relevant to raw target EUF-CMA, whose output target is adversary-chosen. -/
@[expose] def rawZeroForger {F : Type} [Field F] {v o : Nat}
    (_ : MultivariateQuadraticMap F (Fin (v + o)) (Fin o)) :
    ProbOracleComp (fun _ : Fin o → F => Option (Fin (v + o) → F))
      ((Fin o → F) × Option (Fin (v + o) → F)) := pure (0, some 0)

/-- The raw zero-target forgery makes no oracle call. -/
theorem rawZeroForger_queryBounded {F : Type} [Field F] {v o : Nat}
    (P : MultivariateQuadraticMap F (Fin (v + o)) (Fin o)) :
    (rawZeroForger P).IsQueryBounded 0 :=
  OracleComp.IsCostBounded.pure _ _

/-- Raw-target EUF-CMA succeeds with probability one even if the oracle always fails.
Consequently the generic target-forgery/binding partition alone cannot justify ACT-MQ security;
its structured-message game and the random-target one-more game remain separate problems. -/
theorem eval_rawZeroForger {F : Type} [Field F] [Fintype F] [DecidableEq F] {v o : Nat}
    (derive : IdealKeyMaterial F v o → (Fin o → F) →
      ProbComp (Option (Fin (v + o) → F))) :
    ProbComp.eval ((idealRawScheme derive).eufCmaExperiment rawZeroForger) = PMF.pure true := by
  have h : PMF.map (fun _ => true) (ProbComp.eval (idealKeyGen F v o)) = PMF.pure true :=
    PMF.map_const _ _
  simpa [Signature.Scheme.eufCmaExperiment, forgeExperiment, rawZeroForger,
    ProbOracleComp.runLogWith, StateT.run_pure, idealRawScheme, freshMessage] using h

end Cslib.Crypto.UOV
