/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind

/-!
# Ajtai's hash function and collision finding

Ajtai's function `ajtaiHash A x = A x mod q` on integer vectors is linear, so two distinct inputs
with the same hash differ by a nonzero kernel vector of `A`. When both inputs lie in `[0, β]^m`
the difference is a short integer solution with bound `β` (`IsAjtaiCollision.isSolution_sub`);
when both lie in `[-β, β]^m` it is one with bound `2 * β` (`isSolution_sub_of_abs_le`). No
primality assumption on `q` is needed.

`ajtaiCollisionExperiment q β F` draws a uniform `A ∈ ℤ_q^{n×m}`, and the typed finder `F` wins
when it returns a collision in `[0, β]^m`. The SIS solver `collisionToSIS F` returns the
difference of `F`'s pair, and `ajtaiAdvantage_le_sisAdvantage` bounds the collision-finding
advantage by its SIS advantage for every modulus, dimension, bound and finder.

Ajtai's hash family of [GoldreichGoldwasserHalevi1996], Section 3, hashes a string
`s ∈ {0,1}^m`, here a word of length `m`, to `A s mod q` under a uniform key `A` (`ajtaiSetup`,
`ajtaiWordHash`). Their Theorem 2, that the family is collision resistant when SIS is hard, is
`SIS.collisionResistantForOn_ajtaiWordHash`. For a SIS parameter family `P` with bound at least
`1` and with `P.m` computable in polynomial time, `SIS P` gives `CollisionResistantForOn` for the
family against uniform strict PPT finders. The reduction `ajtaiWordCollisionToSIS` is
`collisionToSIS` applied to the finder's words read as 0/1 vectors, and
`isPPT_ajtaiWordCollisionToSIS` proves it efficient from the finder's certificate. SIS is
assumed; its worst-case hardness ([Ajtai1996], Theorem 1) is not formalized.

## Main definitions

* `Cslib.Crypto.ajtaiHash`: Ajtai's linear hash function on integer vectors.
* `Cslib.Crypto.IsAjtaiCollision`: a collision in `[0, β]^m`.
* `Cslib.Crypto.ajtaiCollisionExperiment`, `Cslib.Crypto.ajtaiAdvantage`: the typed
  collision-finding experiment at one instance, and its success probability.
* `Cslib.Crypto.collisionToSIS`: the SIS solver built from a typed collision finder.
* `Cslib.Crypto.binaryVec`: a word read as a 0/1 integer vector.
* `Cslib.Crypto.ajtaiSetup`, `Cslib.Crypto.ajtaiWordHash`: Ajtai's hash family on words for a SIS
  parameter family.
* `Cslib.Crypto.ajtaiWordCollisionToSIS`: the SIS solver built from a word collision finder.

## Main results

* `Cslib.Crypto.IsAjtaiCollision.isSolution_sub`, `Cslib.Crypto.isSolution_sub_of_abs_le`:
  collisions give short integer solutions.
* `Cslib.Crypto.ajtaiAdvantage_le_sisAdvantage`,
  `Cslib.Crypto.succProbability_collisionGameFor_ajtaiWordHash_le`: at one instance, the
  collision-finding success is at most the SIS advantage of the reduction.
* `Cslib.Crypto.isPPT_ajtaiWordCollisionToSIS`: the reduction is a PPT SIS solver.
* `Cslib.Crypto.SIS.collisionResistantForOn_ajtaiWordHash`: Ajtai's hash family is collision
  resistant under SIS ([GoldreichGoldwasserHalevi1996], Theorem 2).

## References

* [M. Ajtai, *Generating Hard Instances of Lattice Problems*][Ajtai1996]
* [O. Goldreich, S. Goldwasser, S. Halevi, *Collision-Free Hashing from Lattice
  Problems*][GoldreichGoldwasserHalevi1996]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023]
-/
@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

variable {n m q : ℕ}

/-- Ajtai's linear hash function `x ↦ A x mod q` on integer vectors. Its kernel is the lattice
`Λ(ν, q)` of [Ajtai1996] ("The definition of the random class", p. 4), where `ν` lists the
columns of `A`. -/
def ajtaiHash (A : Matrix (Fin n) (Fin m) (ZMod q)) (x : Fin m → ℤ) : Fin n → ZMod q :=
  A *ᵥ (Int.cast ∘ x)

/-- Ajtai's hash function is additive. -/
theorem ajtaiHash_sub (A : Matrix (Fin n) (Fin m) (ZMod q)) (x y : Fin m → ℤ) :
    ajtaiHash A (x - y) = ajtaiHash A x - ajtaiHash A y := by
  rw [ajtaiHash, ajtaiHash, ajtaiHash, ← Matrix.mulVec_sub]
  exact congrArg (A *ᵥ ·) (funext fun i => Int.cast_sub (x i) (y i))

/-- Distinct inputs in `[-β, β]^m` with the same Ajtai hash differ by a short integer solution
with bound `2 * β`. -/
theorem isSolution_sub_of_abs_le {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    {x y : Fin m → ℤ} (hxy : x ≠ y) (hx : ∀ i, |x i| ≤ β) (hy : ∀ i, |y i| ≤ β)
    (h : ajtaiHash A x = ajtaiHash A y) :
    SIS.IsSolution A (2 * β) (x - y) :=
  ⟨sub_ne_zero.mpr hxy, fun i => by
    have hx' := abs_le.mp (hx i)
    have hy' := abs_le.mp (hy i)
    simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat, abs_le]
    omega,
    show ajtaiHash A (x - y) = 0 by rw [ajtaiHash_sub, h, sub_self]⟩

/-- `(x, y)` is a collision of Ajtai's hash function for `A` in `[0, β]^m`: distinct inputs in
`[0, β]^m` with the same hash. -/
def IsAjtaiCollision (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) : Prop :=
  x ≠ y ∧ (∀ i, 0 ≤ x i ∧ x i ≤ β) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ β) ∧
    ajtaiHash A x = ajtaiHash A y

instance (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) :
    Decidable (IsAjtaiCollision A β x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A collision in `[0, β]^m` differs by a short integer solution with bound `β`. -/
theorem IsAjtaiCollision.isSolution_sub {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    {x y : Fin m → ℤ} (h : IsAjtaiCollision A β x y) : SIS.IsSolution A β (x - y) :=
  let ⟨hxy, hx, hy, hxy'⟩ := h
  ⟨sub_ne_zero.mpr hxy, fun i => by
    have hx' := hx i
    have hy' := hy i
    simp only [Pi.sub_apply, abs_le]
    omega,
    show ajtaiHash A (x - y) = 0 by rw [ajtaiHash_sub, hxy', sub_self]⟩

/-- The SIS solver built from a collision finder: run the finder and return the difference of
its pair. -/
def collisionToSIS (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ)))
    (A : Matrix (Fin n) (Fin m) (ZMod q)) : ProbComp (Fin m → ℤ) := do
  let (x, y) ← F A
  return x - y

section Experiment

variable (q) [NeZero q]

/-- The Ajtai collision-finding experiment for modulus `q`, dimensions `n × m` and box
`[0, β]^m`: the challenger draws a uniform `A ∈ ℤ_q^{n×m}`; the finder wins when it returns a
collision of `ajtaiHash A` in the box. -/
noncomputable def ajtaiCollisionExperiment (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) :
    ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
  let (x, y) ← F A
  return decide (IsAjtaiCollision A β x y)

/-- The collision-finding advantage of `F`: its success probability in
`ajtaiCollisionExperiment`. -/
noncomputable def ajtaiAdvantage (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (ajtaiCollisionExperiment q β F))

/-- Every typed collision finder's advantage is at most the SIS advantage of `collisionToSIS`, for
every nonzero modulus, dimension and bound. This is the concrete step of
[GoldreichGoldwasserHalevi1996], Theorem 2, for inputs in `[0, β]^m` instead of `{0,1}^m`: the
difference of a collision in `[0, β]^m` is a SIS solution with bound `β`. -/
theorem ajtaiAdvantage_le_sisAdvantage (β : ℕ)
    (F : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp ((Fin m → ℤ) × (Fin m → ℤ))) :
    ajtaiAdvantage q β F ≤ sisAdvantage q β (collisionToSIS F) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [ajtaiCollisionExperiment, sisExperiment, collisionToSIS, bind_assoc,
    ProbComp.eval_bind]
  exact PMF.bind_apply_mono_on_support _ _ fun A _ =>
    PMF.bind_apply_mono_on_support _ _ fun ⟨x, y⟩ _ => by
      by_cases h : IsAjtaiCollision A β x y <;> simp [h, IsAjtaiCollision.isSolution_sub]

end Experiment

/-! ### Ajtai's hash family on words -/

/-- The word `s` read as a 0/1 integer vector of length `m`: coordinate `i` is bit `i` of
`BitString.ofList m s`, which pads short words with `false` and ignores bits beyond `m`. -/
def binaryVec (m : ℕ) (s : List Bool) : Fin m → ℤ :=
  fun i => ((BitString.ofList m s i).toNat : ℤ)

/-- Words of length `m` are determined by their 0/1 vectors. -/
theorem binaryVec_injOn {m : ℕ} {s₁ s₂ : List Bool} (h₁ : s₁.length = m) (h₂ : s₂.length = m)
    (h : binaryVec m s₁ = binaryVec m s₂) : s₁ = s₂ := by
  rw [← BitString.ofFn_ofList h₁, ← BitString.ofFn_ofList h₂]
  refine congrArg List.ofFn (funext fun i => ?_)
  have hi := congrFun h i
  simp only [binaryVec, Nat.cast_inj] at hi
  revert hi
  cases BitString.ofList m s₁ i <;> cases BitString.ofList m s₂ i <;> simp

/-- Two distinct words of length `m` with the same Ajtai hash form a collision in `[0, β]^m` for
every `β ≥ 1`. -/
private theorem isAjtaiCollision_binaryVec {A : Matrix (Fin n) (Fin m) (ZMod q)} {β : ℕ}
    (hβ : 1 ≤ β) {s₁ s₂ : List Bool} (h₁ : s₁.length = m) (h₂ : s₂.length = m) (hne : s₁ ≠ s₂)
    (h : ajtaiHash A (binaryVec m s₁) = ajtaiHash A (binaryVec m s₂)) :
    IsAjtaiCollision A β (binaryVec m s₁) (binaryVec m s₂) := by
  have hbox (s : List Bool) (i : Fin m) : 0 ≤ binaryVec m s i ∧ binaryVec m s i ≤ β := by
    cases hb : BitString.ofList m s i <;> simp [binaryVec, hb, (by exact_mod_cast hβ : (1 : ℤ) ≤ β)]
  exact ⟨fun hv => hne (binaryVec_injOn h₁ h₂ hv), hbox s₁, hbox s₂, h⟩

section Family

variable (P : SISParams)

/-- The key law of Ajtai's hash family at security parameter `κ`: a uniform matrix
`A ∈ ℤ_q^{n×m}`, for the dimensions and modulus that `P` assigns to `κ`, returned as the SIS
input `⟨κ, A⟩` ([GoldreichGoldwasserHalevi1996], Section 3, p. 4). -/
noncomputable def ajtaiSetup (κ : ℕ) : PMF P.Input :=
  (ProbComp.eval (ProbComp.uniform (Matrix (Fin (P.n κ)) (Fin (P.m κ)) (ZMod (P.q κ))))).map
    fun A => ⟨κ, A⟩

/-- Ajtai's hash family on words ([GoldreichGoldwasserHalevi1996], Section 3, p. 4). The key `d`
is a SIS input `⟨κ, A⟩`, and the word `s` hashes to `A s mod q`, where `s` is read as a 0/1
vector of length `m = P.m κ` (`binaryVec`). On the words of length `m`, the source's message space
`{0,1}^m`, this is the source's `h_A(s) = A s mod q`. -/
def ajtaiWordHash (d : P.Input) (s : List Bool) : Fin (P.n d.secParam) → ZMod (P.q d.secParam) :=
  ajtaiHash d.matrix (binaryVec (P.m d.secParam) s)

/-- The SIS solver built from a collision finder for `ajtaiWordHash`. It gives the finder `κ` and
the key `⟨κ, A⟩`, reads both returned words as 0/1 vectors, and returns their difference
(`collisionToSIS`). This is the reduction in the proof of [GoldreichGoldwasserHalevi1996],
Theorem 2 (p. 5). -/
def ajtaiWordCollisionToSIS (F : CollisionFinderFor P.Input) : P.Solver :=
  fun κ => collisionToSIS fun A =>
    (fun (s₁, s₂) => (binaryVec (P.m κ) s₁, binaryVec (P.m κ) s₂)) <$> F κ ⟨κ, A⟩

variable {P}

/-- At one security parameter `κ` with `P.β κ ≥ 1`, a collision finder's success probability
against `ajtaiWordHash` on the words of length `P.m κ` is at most the SIS advantage of
`ajtaiWordCollisionToSIS`. This is the concrete step of [GoldreichGoldwasserHalevi1996],
Theorem 2; it goes through the typed bound `ajtaiAdvantage_le_sisAdvantage`. -/
theorem succProbability_collisionGameFor_ajtaiWordHash_le (F : CollisionFinderFor P.Input)
    {κ : ℕ} (hβ : 1 ≤ P.β κ) :
    Game.succProbability (collisionGameFor (ajtaiSetup P) (ajtaiWordHash P)
        (fun _ d s => s.length == P.m d.secParam) F κ) ≤
      sisAdvantage (P.q κ) (P.β κ) (ajtaiWordCollisionToSIS P F κ) := by
  refine (Game.succProbability_mono ?_).trans (ajtaiAdvantage_le_sisAdvantage (P.q κ) (P.β κ) _)
  simp only [collisionGameFor, Game.withSetup, collisionExperiment, ajtaiSetup,
    ajtaiCollisionExperiment, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
    PMF.bind_map, Function.comp_def]
  refine PMF.bind_apply_mono_on_support _ _ fun A _ =>
    PMF.bind_apply_mono_on_support _ _ fun (s₁, s₂) _ => ?_
  by_cases hcol : isCollisionFor (ajtaiWordHash P) (fun _ d s => s.length == P.m d.secParam) κ
      ⟨κ, A⟩ s₁ s₂ = true
  · obtain ⟨h₁, h₂, hne, hH⟩ := isCollisionFor_eq_true_iff.mp hcol
    have hA := isAjtaiCollision_binaryVec hβ (beq_iff_eq.mp h₁) (beq_iff_eq.mp h₂) hne hH
    simp only [hcol, hA, decide_true, le_refl]
  · simp only [Bool.eq_false_iff.mpr hcol, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
      zero_le]

/-- Subtracting the 0/1 vectors of two words and encoding the result as a SIS answer takes
polynomial time in the unary length and the two words. -/
private theorem computableInPolyTime_encodeVec_binaryVec_sub :
    ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
        SIS.encodeVec (binaryVec p.1 p.2.1 - binaryVec p.1 p.2.2))
      (encPair encUnary (encPair encBits encBits)) encBits := by
  have hbit : ComputableInPolyTime (fun b : Bool => (b.toNat : ℤ)) encBool encIntBin := .of_finite _
  have hp := ComputableInPolyTime.id'
    (encIn := encPair (encPair encUnary (encPair encBits encBits)) encUnary)
  have hleft := hp.fst'.snd'.fst'.bitsGetDWithInput hp.snd' false
  have hright := hp.fst'.snd'.snd'.bitsGetDWithInput hp.snd' false
  have h : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      (List.range p.1).map fun i =>
        ((p.2.1.getD i false).toNat : ℤ) - ((p.2.2.getD i false).toNat : ℤ))
      (encPair encUnary (encPair encBits encBits)) (encList encIntBin) :=
    ComputableInPolyTime.mapWithInput
      (f := fun p i => ((p.2.1.getD i false).toNat : ℤ) - ((p.2.2.getD i false).toNat : ℤ))
      (ComputableInPolyTime.range.comp
        (ComputableInPolyTime.fst encUnary (encPair encBits encBits)))
      (ComputableInPolyTime.intBin_sub' (hbit.comp hleft) (hbit.comp hright))
  convert h.encoding_comp using 1
  funext ⟨m, s₁, s₂⟩
  refine congrArg (encList encIntBin) (List.ext_getElem (by simp) fun _ _ _ => ?_)
  simp [binaryVec, BitString.ofList]

/-- `ajtaiWordCollisionToSIS` is a PPT SIS solver when the collision finder is uniform strict PPT
and `P.m` is computable in polynomial time. -/
theorem isPPT_ajtaiWordCollisionToSIS (hm : ComputableInPolyTime P.m encUnary encUnary)
    {F : CollisionFinderFor P.Input}
    (hF : IsPPTOn (encPair encUnary P.encInput) (encPair encBits encBits) fun p => F p.1 p.2) :
    (ajtaiWordCollisionToSIS P F).IsPPT := by
  have hsec := SISParams.computableInPolyTime_secParam (P := P)
  have hpost : ComputableInPolyTime
      (fun p : P.Input × List Bool × List Bool =>
        SIS.encodeVec (binaryVec (P.m p.1.secParam) p.2.1 - binaryVec (P.m p.1.secParam) p.2.2))
      (encPair P.encInput (encPair encBits encBits)) encBits :=
    computableInPolyTime_encodeVec_binaryVec_sub.comp
      (((hm.comp hsec).comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  exact ((hF.preprocess (hsec.prod ComputableInPolyTime.id')).map_with
    (f := fun x w =>
      SIS.encodeVec (binaryVec (P.m x.secParam) w.1 - binaryVec (P.m x.secParam) w.2)) hpost).congr
    fun _ => by simp [ajtaiWordCollisionToSIS, collisionToSIS]

/-- **Ajtai's hash family is collision resistant under SIS** ([GoldreichGoldwasserHalevi1996],
Theorem 2, p. 4). Let `P` be a SIS parameter family whose column count `P.m` is computable in
polynomial time and whose bound `P.β` is at least `1`. If `SIS P` holds, then no uniform strict PPT
finder that is given `κ` and the key `⟨κ, A⟩`, for a uniform `A ∈ ℤ_q^{n×m}`, finds two distinct
words of length `m` with the same hash `A s mod q`, except with negligible probability. This is
collision resistance in the standard model, `CollisionResistantForOn` ([BonehShoup2023],
Definition 8.2 and Attack Game 8.1), with digests typed in `ℤ_q^n`.

The proof applies `SIS P` to `ajtaiWordCollisionToSIS`, which returns the difference
`s₁ - s₂ ∈ {-1, 0, 1}^m` of the colliding words as in the source's proof, through its
certificate `isPPT_ajtaiWordCollisionToSIS`.

This statement differs from the source in these ways.
* The source takes `n` as the security parameter and requires `n log q < m ≤ q / (2 n⁴)` and
  `q = O(n^c)` (Section 2.2, p. 3). Here the security parameter is `κ`, and `P` is any family with
  `P.m` computable in polynomial time and `P.β ≥ 1`. The reduction uses no relation between the
  parameters. The source needs them for its Theorem 1, which reduces worst-case lattice problems
  to Problem (A2), and for compression (Section 3.1, p. 5); this theorem claims neither.
* The assumption is `SIS P`, with `ℓ_∞` bound `P.β κ`. At `P.β = 1` it is the source's Problem
  (A2) (Section 2.3, p. 4), whose solutions are the nonzero `x ∈ {-1, 0, 1}^m` with `Mx ≡ 0`
  `(mod q)`. A larger bound makes the assumption stronger. With bound `0`, `SIS P` holds vacuously,
  which is why `P.β ≥ 1` is required.
* Theorem 2 is stated for (expected) running time `T(n, m, q)`. Here finders and SIS solvers are
  uniform strict PPT, and the conclusion is negligible success.
* The key law `ajtaiSetup P` is a distribution. Its efficient sampling and the cost of evaluating
  the hash, which Definition 8.2 also asks for, are not certified here.
* `P.m` must be computable in polynomial time so that the reduction can write an answer of
  length `m` when the finder's words have the wrong length. -/
theorem SIS.collisionResistantForOn_ajtaiWordHash
    (hm : ComputableInPolyTime P.m encUnary encUnary) (hβ : ∀ κ, 1 ≤ P.β κ) (hSIS : SIS P) :
    CollisionResistantForOn P.encInput (ajtaiSetup P) (ajtaiWordHash P)
      (fun _ d s => s.length == P.m d.secParam) :=
  CollisionResistantForOn.of_negligible fun F hF =>
    negligible_of_le (hSIS _ (isPPT_ajtaiWordCollisionToSIS hm hF))
      fun κ => succProbability_collisionGameFor_ajtaiWordHash_le F (hβ κ)

end Family

end Cslib.Crypto
