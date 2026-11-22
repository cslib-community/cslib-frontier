/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.MatrixOracle
public import CslibFrontier.Crypto.Computational.MLDSA.MatrixSampling
public import CslibFrontier.Crypto.Computational.SIS.Hermite
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# The ML-DSA key-only game with shared classical matrix and commitment oracles

For a published rounded byte key, the corrected witness in [BaiEtAl2021Dilithium], §6.2.1,
equation (10), has its low component, response and challenge in the columns of
`[I | A | -t]`. The verifier queries its reconstructed commitment, and that commitment times
`2γ₂` is the module product of the witness.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.SharedDigest

open Probability OracleComp

attribute [local instance 2000] instBEqOfDecidableEq

private abbrev RightBlock (s : Level) := Matrix (Fin s.params.k) (Fin (s.params.ℓ + 1)) Poly

/-- The bijection `(A,t) ↦ [A | −t]` between the decision challenge and the right block of
the standard Hermite Module-SIS instance. -/
private def rightBlock (s : Level) : (PublicMatrix s × (Fin s.params.k → Poly)) ≃ RightBlock s where
  toFun x i := Fin.snoc (x.1 i) (-x.2 i)
  invFun B := (fun i j => B i j.castSucc, fun i => -B i (Fin.last _))
  left_inv x := by
    obtain ⟨A, t⟩ := x
    simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_neg]
  right_inv B := by
    funext i j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

/-- Systematic self-target matrix with the standard Hermite right block `[A | −t]`. -/
def systematic (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly :=
  ModuleSIS.hermiteMatrix (rightBlock s (A, t))

private theorem systematic_row (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly)
    (i : Fin s.params.k) : systematic s A t i =
      Fin.snoc (Fin.append (fun j => if j = i then (1 : Negacyclic (ZMod 8380417) 256).coeffs
        else 0) (A i)) (-t i) := by
  unfold systematic ModuleSIS.hermiteMatrix
  change Fin.append _ (Fin.snoc (A i) (-t i)) = _
  exact Fin.append_snoc _ _ _

/-- Integer lift of the three blocks of a self-target witness, with the challenge last. -/
def liftWitness (s : Level) (y : SelfTargetCandidate s.params) :
    Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ :=
  fun i j => ((Fin.snoc (α := fun _ => Poly) (Fin.append y.u y.z) y.c i) j).valMinAbs

/-- Multiplying the three lifted blocks by the systematic matrix gives the full self-target
product, including the public-key rounding correction in any corrected low block. -/
theorem systematic_liftWitness (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly)
    (y : SelfTargetCandidate s.params) :
    moduleSISMap (systematic s A t) (fun i j => (liftWitness s y i j : ZMod 8380417)) =
      selfTargetMap s.params ⟨A, t⟩ y.u y.z y.c := by
  have hc : (fun i j => (liftWitness s y i j : ZMod 8380417)) =
      Fin.append y.u (Fin.snoc y.z y.c) := by
    funext i j
    simp only [liftWitness, ZMod.coe_valMinAbs, Fin.append_snoc]
  rw [hc, systematic, ModuleSIS.moduleSISMap_hermiteMatrix]
  change y.u + moduleSISMap (fun i => Fin.snoc (A i) (-t i)) (Fin.snoc y.z y.c) = _
  funext i
  simp only [moduleSISMap, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, neg_negacyclicMul, selfTargetMap, verifierCommitment,
    Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, negacyclicMul_comm (t i) y.c]

private theorem liftWitness_bound {s : Level} {y : SelfTargetCandidate s.params} {radius : ℕ}
    (hu : ModuleSIS.inInfNormBound radius y.u) (hz : ModuleSIS.inInfNormBound radius y.z)
    (hc : InBall s.params.τ y.c) (hr : 1 ≤ radius) :
    ∀ i j, |liftWitness s y i j| ≤ radius := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [liftWitness] using (hc.1 j).trans (show (1 : ℤ) ≤ (radius : ℤ) by exact_mod_cast hr)
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · change |(Fin.snoc (α := fun _ => Poly) (Fin.append y.u y.z) y.c
          ((Fin.castAdd _ a).castSucc) j).valMinAbs| ≤ _
      simpa only [Fin.snoc_castSucc, Fin.append_left] using hu a j
    · change |(Fin.snoc (α := fun _ => Poly) (Fin.append y.u y.z) y.c
          ((Fin.natAdd _ b).castSucc) j).valMinAbs| ≤ _
      simpa only [Fin.snoc_castSucc, Fin.append_right] using hz b j

private abbrev MatrixInstance (s : Level) :=
  Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly

/-- Recover the matrix and full vector from the nonidentity blocks of a systematic instance. -/
def fullKey (s : Level) (M : Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly) :
    MLDSA.PublicKey s.params where
  A i j := M i ((Fin.natAdd _ j).castSucc)
  t i := -M i (Fin.last _)

/-- Projecting the nonidentity blocks of the systematic matrix recovers its public-key data. -/
@[simp] theorem fullKey_systematic (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    fullKey s (systematic s A t) = ⟨A, t⟩ := by
  simp only [fullKey, systematic_row, Fin.snoc_castSucc, Fin.append_right, Fin.snoc_last, neg_neg]

private structure Opening (s : Level) where
  signature : Signature s
  challenge : Poly

private def opening (s : Level) (f : Forgery) : Option (Opening s) := do
  guard (f.context.length ≤ 255)
  let σ ← sigDecode s f.signature
  let c ← sampleInBall s σ.digest
  guard (ResponseShort s.params σ.z)
  return ⟨σ, c⟩

private theorem opening_eq_some_iff {s : Level} {f : Forgery} {o : Opening s} :
    opening s f = some o ↔
      f.context.length ≤ 255 ∧ sigDecode s f.signature = some o.signature ∧
        sampleInBall s o.signature.digest = some o.challenge ∧
        ResponseShort s.params o.signature.z := by
  cases o
  simp [opening, Option.bind_eq_some_iff, Option.guard_eq_some']

private abbrev Digest (s : Level) := FixedBytes (digestBytes s)
private abbrev Point (s : Level) := ModuleSIS.SelfTarget.Point s.params.k 256 8380417

private def commitmentPoint (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (o : Opening s) : Point s :=
  (messageRepresentative bytes (formattedMessage f), fun i j =>
    ((hintedCommitment s (publicKey s bytes A) o.signature o.challenge i j *
      (2 * s.params.γ₂ : ℕ) : ℤ) : ZMod 8380417))

/-- Key-only byte verification with a classical commitment query. The query contains the
message representative and the hinted high commitment on its canonical `2γ₂` grid.
The digest bytes in the signature must match the oracle reply exactly. -/
def verify (s : Level) (bytes : List Byte) (A : PublicMatrix s) (f : Forgery) :
    OracleComp (fun _ : ModuleSIS.SelfTarget.Point s.params.k 256 8380417 =>
      FixedBytes (digestBytes s)) Bool :=
  if bytes.length = 32 + 320 * s.params.k then
    match opening s f with
    | none => pure false
    | some o => do
      let digest ← query (commitmentPoint s bytes A f o)
      return decide (digest.toList = o.signature.digest)
  else pure false

/-- The concrete SHAKE digest at a grid point, represented by the parameter set's number of
bytes. This is the deterministic oracle used to recover the FIPS byte verifier. -/
@[expose] def shakeReply (s : Level) (p : ModuleSIS.SelfTarget.Point s.params.k 256 8380417) :
    FixedBytes (digestBytes s) := fun i =>
  (commitmentDigest s (highBitsVec s.params p.2) p.1).get
    (i.cast (length_commitmentDigest s _ _).symm)

private theorem toList_shakeReply (s : Level) (p : Point s) :
    (shakeReply s p).toList = commitmentDigest s (highBitsVec s.params p.2) p.1 := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [FixedBytes.toList, List.getElem_ofFn, shakeReply]
    rfl

private theorem highBits_commitmentPoint (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (o : Opening s) :
    highBitsVec s.params (commitmentPoint s bytes A f o).2 =
      hintedCommitment s (publicKey s bytes A) o.signature o.challenge := by
  have hq : 4 * s.params.γ₂ < s.params.q := by cases s <;> decide
  funext i j
  exact highBits_intCast_mul s.valid.γ₂_pos s.valid.two_mul_γ₂_dvd
      (useHint_nonneg s.valid.γ₂_pos hq _ _)
      (useHint_lt s.valid.γ₂_pos s.valid.two_mul_γ₂_dvd hq _ _)

private theorem shakeReply_at (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (o : Opening s) :
    (shakeReply s (commitmentPoint s bytes A f o)).toList =
      commitmentDigest s (hintedCommitment s (publicKey s bytes A) o.signature o.challenge)
        (messageRepresentative bytes (formattedMessage f)) := by
  rw [toList_shakeReply, highBits_commitmentPoint]
  rfl

/-- Supplying concrete SHAKE replies to the oracle verifier reproduces byte verification at the
supplied matrix `A` (`verifyWithExpansion s (fun _ => some A)`) on the same byte key, context,
message and signature. Concrete Algorithm 3 expands `A` from the 32-byte public seed via
`expandA s` ([NISTFIPS204], Algorithm 8, line 5, p. 27), so recovering concrete Algorithm 3
specializes this equivalence under successful seed expansion
(`verifyWithExpansion_encodePublic`). -/
theorem verify_shakeReply_iff (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) :
    interpret (m := Id) (shakeReply s) (verify s bytes A f) = true ↔
      verifyWithExpansion s (fun _ => some A) bytes f.message f.context f.signature =
        some true := by
  rw [verifyWithMatrix_eq_some_true_iff]
  unfold verify
  split_ifs with hlen
  · cases ho : opening s f with
    | none =>
      simp only [interpret_pure, hlen, true_and]
      change false = true ↔ _
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨hctx, σ, c, hσ, hc, hz, _⟩
      exact Option.some_ne_none _
        (((opening_eq_some_iff (o := ⟨σ, c⟩)).mpr ⟨hctx, hσ, hc, hz⟩).symm.trans ho)
    | some o =>
      obtain ⟨hctx, hσ, hc, hz⟩ := opening_eq_some_iff.mp ho
      simp only [bind_pure_comp, interpret_map, interpret_query, hctx, hlen, true_and]
      change decide ((shakeReply s (commitmentPoint s bytes A f o)).toList =
        o.signature.digest) = true ↔ _
      simp [shakeReply_at, hσ, hc, hz]
  · simp [hlen]

/-- The raw FIPS address of a module product and message representative. Products with
the same high bits give the same word. -/
def pointAddress (s : Level) (p : ModuleSIS.SelfTarget.Point s.params.k 256 8380417) : List Bool :=
  commitmentInput s (highBitsVec s.params p.2) p.1

private def decodePoint (s : Level) (raw : List Bool) : Point s :=
  (raw.take 512, fun i j =>
    ((unpackCommitment s 512 raw i j * (2 * s.params.γ₂ : ℕ) : ℤ) : ZMod 8380417))

private theorem decodePoint_address {s : Level} {p : Point s}
    (hm : p.1.length = 512) (hv : OnCommitmentGrid s p.2) :
    decodePoint s (pointAddress s p) = p := by
  have hw (i j) : 0 ≤ highBitsVec s.params p.2 i j ∧ highBitsVec s.params p.2 i j <
      (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ) :=
    ⟨highBits_nonneg s.valid.γ₂_pos _, highBits_lt s.valid.γ₂_pos s.valid.two_mul_γ₂_dvd
      s.valid.one_lt_q _⟩
  apply Prod.ext
  · change (commitmentInput s _ _).take 512 = _
    simpa only [hm] using take_commitmentInput s (highBitsVec s.params p.2) p.1
  · funext i j
    change ((unpackCommitment s 512 (pointAddress s p) i j * _ : ℤ) : ZMod 8380417) = _
    rw [← hm, pointAddress, unpackCommitment_input p.1 hw]
    exact (hv i j).symm

/-- Inject arbitrary raw hash words into the algebraic oracle. A canonical FIPS word
uses its decoded verifier point. Other words use disjoint internal memoization keys. -/
def rawPoint (s : Level) : List Bool ↪ ModuleSIS.SelfTarget.Point s.params.k 256 8380417 :=
  let represent (raw : List Bool) :=
    let p := decodePoint s raw
    if p.1.length = 512 ∧ pointAddress s p = raw then p
    else (List.replicate 513 false ++ raw, 0)
  let recover (p : Point s) := if p.1.length = 512 then pointAddress s p else p.1.drop 513
  ⟨represent, Function.LeftInverse.injective (g := recover) (by
    intro raw
    simp only [represent]
    split
    · rename_i h
      simp [recover, h.1, h.2]
    · have hlen : (List.replicate 513 false ++ raw).length ≠ 512 := by
        rw [List.length_append, List.length_replicate]
        omega
      simp only [recover, hlen, ite_false]
      simpa only [List.length_replicate] using List.drop_left (l₁ := List.replicate 513 false)
        (l₂ := raw))⟩

/-- The raw simulator's address coincides with the algebraic verifier's query. -/
theorem rawPoint_pointAddress {s : Level} {p : ModuleSIS.SelfTarget.Point s.params.k 256 8380417}
    (hm : p.1.length = 512) (hv : OnCommitmentGrid s p.2) :
    rawPoint s (pointAddress s p) = p := by
  change (if (decodePoint s (pointAddress s p)).1.length = 512 ∧
    pointAddress s (decodePoint s (pointAddress s p)) = pointAddress s p then _ else _) = _
  rw [decodePoint_address hm hv]
  simp only [hm, and_self, ite_true]

/-- A fixed-width message representative and a ring product on the verifier's grid. -/
abbrev GridPoint (s : Level) := BitString 512 × {v : Fin s.params.k → Poly // OnCommitmentGrid s v}

/-- The FIPS raw address is injective on full grid points, including its message prefix. -/
@[expose] def gridAddress (s : Level) : GridPoint s ↪ BitString s.commitmentInputBits where
  toFun p := BitString.ofList _ (commitmentInput s (highBitsVec s.params p.2.val) (List.ofFn p.1))
  inj' := by
    rintro ⟨mx, x, hx⟩ ⟨my, y, hy⟩ h
    have len (m : BitString 512) (v : Fin s.params.k → Poly) :
        (commitmentInput s (highBitsVec s.params v) (List.ofFn m)).length =
          s.commitmentInputBits :=
      commitmentInput_length s (highBitsVec s.params v) (μ := List.ofFn m) List.length_ofFn
    have he : commitmentInput s (highBitsVec s.params x) (List.ofFn mx) =
        commitmentInput s (highBitsVec s.params y) (List.ofFn my) := by
      simpa only [BitString.ofFn_ofList (len mx x), BitString.ofFn_ofList (len my y)] using
        congrArg List.ofFn (show BitString.ofList _
            (commitmentInput s (highBitsVec s.params x) (List.ofFn mx)) =
          BitString.ofList _
            (commitmentInput s (highBitsVec s.params y) (List.ofFn my)) from h)
    have decode_raw {μ : List Bool} {v : Fin s.params.k → Poly}
        (hμ : μ.length = 512) (hv : OnCommitmentGrid s v) :
        decodePoint s (commitmentInput s (highBitsVec s.params v) μ) = (μ, v) :=
      decodePoint_address (p := (μ, v)) hμ hv
    have hp : (List.ofFn mx, x) = (List.ofFn my, y) := by
      have hd := congrArg (decodePoint s) he
      rwa [decode_raw List.length_ofFn hx, decode_raw List.length_ofFn hy] at hd
    obtain ⟨hm, hv⟩ := Prod.mk.inj hp
    exact Prod.ext (List.ofFn_injective hm) (Subtype.ext hv)

private theorem commitmentPoint_onGrid (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (o : Opening s) : OnCommitmentGrid s (commitmentPoint s bytes A f o).2 := by
  unfold OnCommitmentGrid
  rw [highBits_commitmentPoint]
  exact fun _ _ => rfl

/-- The byte verifier only queries canonical grid points with a 512-bit message prefix. -/
theorem interpret_verify_congr {m : Type → Type} [Monad m] [LawfulMonad m] {s : Level}
    (bytes : List Byte) (A : PublicMatrix s) (f : Forgery)
    (R S : ModuleSIS.SelfTarget.Point s.params.k 256 8380417 → m (FixedBytes (digestBytes s)))
    (agree : ∀ p, p.1.length = 512 → OnCommitmentGrid s p.2 → R p = S p) :
    interpret R (verify s bytes A f) = interpret S (verify s bytes A f) := by
  by_cases hl : bytes.length = 32 + 320 * s.params.k
  · cases ho : opening s f with
    | none => simp [verify, hl, ho]
    | some o =>
      simp only [verify, hl, ite_true, ho, bind_pure_comp, interpret_map, interpret_query]
      rw [agree (commitmentPoint s bytes A f o) (length_messageRepresentative ..)
        (commitmentPoint_onGrid s bytes A f o)]
  · simp [verify, hl]

private def witness (s : Level) (pk : MLDSA.PublicKey s.params) (bytes : List Byte)
    (f : Forgery) (o : Opening s) : SelfTargetCandidate s.params :=
  SelfTargetCandidate.ofCompressedForgery s.params 13 pk
    (messageRepresentative bytes (formattedMessage f)) ⟨o.signature.z, o.signature.h, o.challenge⟩

private theorem product_witness (s : Level) (rho : FixedBytes 32) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) (f : Forgery) (o : Opening s) :
    let bytes := encodePublic s rho.toList t
    let y := witness s ⟨A, t⟩ bytes f o
    (y.msg, moduleSISMap (systematic s A t) (fun i j => (liftWitness s y i j : ZMod 8380417))) =
      commitmentPoint s bytes A f o := by
  dsimp only
  rw [systematic_liftWitness]
  simp only [witness, SelfTargetCandidate.ofCompressedForgery]
  rw [selfTargetMap_compressedForgeryLowPart]
  unfold commitmentPoint hintedCommitment compressedVerifierCommitment
  rw [decode_encodePublic, publicKey_matrix]
  rfl

private theorem short_witness {s : Level} {pk : MLDSA.PublicKey s.params} {bytes : List Byte}
    {f : Forgery} {o : Opening s} (h : opening s f = some o) :
    ∀ i j, |liftWitness s (witness s pk bytes f o) i j| ≤
      compressedSelfTargetRadius s.params 13 := by
  obtain ⟨_, _, hc, hz⟩ := opening_eq_some_iff.mp h
  have hball := inBall_of_sampleInBall hc
  have hv : compressedVerify s.params 13 (fun _ => o.challenge) pk
      (messageRepresentative bytes (formattedMessage f))
      ⟨o.signature.z, o.signature.h, o.challenge⟩ := by
    simp [compressedVerify, hz, hball]
  have hy := isSelfTargetSolution_of_compressedVerify s.valid (by cases s <;> decide)
    (by decide : 0 < 13) hv
  exact liftWitness_bound hy.1 hy.2.1 hball (by unfold compressedSelfTargetRadius; omega)

private theorem accepts_digest_of_opening {s : Level} (pk : MLDSA.PublicKey s.params)
    (bytes : List Byte) {f : Forgery} {o : Opening s} {d : FixedBytes (digestBytes s)}
    (ho : opening s f = some o) (hd : d.toList = o.signature.digest) :
    ModuleSIS.SelfTarget.accepts (expandDigest s) (compressedSelfTargetRadius s.params 13)
      (liftWitness s (witness s pk bytes f o)) d := by
  apply decide_eq_true
  refine ⟨short_witness ho, ?_⟩
  simpa [expandDigest, hd, liftWitness, witness, SelfTargetCandidate.ofCompressedForgery]
    using (opening_eq_some_iff.mp ho).2.2.1

/-- Adversary with saved private randomness and a joint interface for matrix-seed and
commitment-digest queries. -/
abbrev Forger (s : Level) (Coins : Type) :=
  List Byte → Coins → OracleComp
    ((fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ
      (fun _ : ModuleSIS.SelfTarget.Point s.params.k 256 8380417 => FixedBytes (digestBytes s)))
    Forgery

/-- Saved randomness used by the two runs of the fork. Every query has a fresh independent
matrix available, and cached seeds keep their original answer. -/
structure Saved (s : Level) (Coins : Type) where
  /-- The forger's private coins. -/
  coins : Coins
  /-- Public matrix seed sampled independently of the challenge. -/
  seed : FixedBytes 32
  /-- An independent matrix for each query position up to the forger's budget. -/
  matrices : List (PublicMatrix s)

private def sampleBytes (n : ℕ) : ProbComp (FixedBytes n) := replicateFin n (ProbComp.unifFin 255)

private theorem eval_sampleBytes (n : ℕ) :
    (sampleBytes n).eval = PMF.uniformOfFintype (FixedBytes n) := by
  simp only [sampleBytes, ProbComp.eval_replicateFin, ProbComp.eval_unifFin,
    PMF.pi_uniformOfFintype]

/-- Draw private coins, a fresh matrix seed, and `Q` independent responses from the matrix
sampler. The default samples exactly uniform matrices. -/
def sampleSaved {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins)
    (matrix : ProbComp (PublicMatrix s) := MatrixOracle.sampleMatrix s) :
    ProbComp (Saved s Coins) := do
  let r ← coins
  let rho ← sampleBytes 32
  let tape ← replicateFin Q matrix
  return ⟨r, rho, List.ofFn tape⟩

private abbrev Cache (s : Level) := List (FixedBytes 32 × PublicMatrix s)
private abbrev DigestOracle (s : Level) := fun _ : Point s => Digest s

private def handler (s : Level) (matrix : PublicMatrix s) :
    (q : FixedBytes 32 ⊕ Point s) → StateT (Cache s) (OracleComp (DigestOracle s))
      (((fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ DigestOracle s) q) := sumHandler
  (fun rho : FixedBytes 32 => memoize (m := OracleComp (DigestOracle s))
    (fun _ => pure matrix) rho)
  (fun p : Point s => (fun cache : Cache s => (fun d => (d, cache)) <$> query p))

private def runForger {Coins : Type} (s : Level) (adv : Forger s Coins)
    (r : Saved s Coins) (pk : MLDSA.PublicKey s.params) :
    OracleComp (DigestOracle s) Forgery :=
  Prod.fst <$> (interpret (withSampleList 0 (handler s))
    (adv (encodePublic s r.seed.toList pk.t) r.coins)).run ([(r.seed, pk.A)], r.matrices)

/-- Read the corrected systematic self-target vector and message from the final byte forgery.
A malformed opening maps to the zero vector. -/
def extract (s : Level) (pk : MLDSA.PublicKey s.params) (bytes : List Byte)
    (f : Forgery) : List Bool × (Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ) :=
  match opening s f with
  | none => ([], 0)
  | some o =>
    let y := witness s pk bytes f o
    (y.msg, liftWitness s y)

/-- Fixed-table extraction from an accepted byte output. The verifier checks the complete
digest, and the last witness coordinate is the Algorithm 29 expansion of that very digest.
The adversary that produced the bytes may have accessed its table coherently. -/
theorem accepts_extract_of_verify {s : Level} (rho : FixedBytes 32) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly)
    (reply : ModuleSIS.SelfTarget.Point s.params.k 256 8380417 → FixedBytes (digestBytes s))
    (f : Forgery)
    (accept : interpret (m := Id) reply (verify s (encodePublic s rho.toList t) A f) = true) :
    let y := extract s ⟨A, t⟩ (encodePublic s rho.toList t) f
    let v := ModuleSIS.SelfTarget.product (systematic s A t) y.2
    (y.1.length = 512 ∧ OnCommitmentGrid s v) ∧
      ModuleSIS.SelfTarget.accepts (expandDigest s) (compressedSelfTargetRadius s.params 13) y.2
        (reply (y.1, v)) = true := by
  cases ho : opening s f with
  | none => simp [verify, ho] at accept
  | some o =>
    have hp := product_witness s rho A t f o
    have he : (reply (commitmentPoint s (encodePublic s rho.toList t) A f o)).toList =
        o.signature.digest := by
      simp only [verify, length_encodePublic, FixedBytes.length_toList, ite_true, ho,
        bind_pure_comp, interpret_map, interpret_query] at accept
      exact of_decide_eq_true accept
    simp only [extract, ho, ModuleSIS.SelfTarget.product, hp]
    refine ⟨⟨length_messageRepresentative .., ?_⟩, accepts_digest_of_opening _ _ ho he⟩
    rw [show moduleSISMap (systematic s A t) _ =
        (commitmentPoint s (encodePublic s rho.toList t) A f o).2 from congrArg Prod.snd hp]
    exact commitmentPoint_onGrid s (encodePublic s rho.toList t) A f o

/-- Run the byte-key adversary on the original matrix seed and rounded bytes while it
queries the same digest oracle as the final self-target check. -/
def solver {Coins : Type} (s : Level) (adv : Forger s Coins) :
    ModuleSIS.SelfTarget.Adversary s.params.k (s.params.k + s.params.ℓ) 256 8380417
      (FixedBytes (digestBytes s)) (Saved s Coins) := fun M r =>
  let pk := fullKey s M
  (extract s pk (encodePublic s r.seed.toList pk.t)) <$> runForger s adv r pk

private theorem solver_bounded {Coins : Type} {s : Level} {adv : Forger s Coins} {Q : ℕ}
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) (M) (r) :
    (solver s adv M r).IsQueryBounded Q := by
  apply (isCostBounded_map_iff _ _ _).mpr
  apply (isCostBounded_map_iff _ _ _).mpr
  apply IsCostBounded.run_interpret _ (hQ _ _)
  intro q state
  rcases state with ⟨cache, tape⟩
  rcases q with rho | p
  · apply (isCostBounded_map_iff _ _ _).mpr
    change IsCostBounded _ (memoize (fun _ => pure (tape.headD 0)) rho cache) 1
    cases he : cache.lookup rho with
    | none => rw [memoize_of_none _ _ _ he, pure_bind]; exact .pure _ _
    | some v => rw [memoize_of_some _ _ _ _ he]; exact .pure _ _
  · apply (isCostBounded_map_iff _ _ _).mpr
    apply (isCostBounded_map_iff _ _ _).mpr
    exact IsCostBounded.query p

private def runDigest (s : Level) (program : OracleComp (DigestOracle s) Bool) : ProbComp Bool :=
  Prod.fst <$> (interpret (memoize fun _ => sampleBytes (digestBytes s)) program).run []

private theorem memoize_digest (s : Level) (p : Point s) (cache : List (Point s × Digest s)) :
      memoize (fun _ => PMF.uniformOfFintype (Digest s)) p cache =
        Protocols.ROMSignature.oracle (Digest s) p cache := by
  change _ = (Protocols.ROMSignature.oracle (Digest s) p).run cache
  cases h : cache.lookup p with
  | none =>
    rw [memoize_of_none _ _ _ h, Protocols.ROMSignature.run_oracle_of_lookup_eq_none h]
    rfl
  | some d =>
    rw [memoize_of_some _ _ _ _ h, Protocols.ROMSignature.run_oracle_of_lookup_eq_some h]
    rfl

private theorem eval_runDigest (s : Level) (program : OracleComp (DigestOracle s) Bool) :
    (runDigest s program).eval = ((interpret (Protocols.ROMSignature.oracle (Digest s))
      program).run []).map Prod.fst := by
  simp only [runDigest, ProbComp.eval_map, map_run_interpret ProbComp.isMonadHom_eval,
    ProbComp.eval_memoize, eval_sampleBytes]
  simp only [memoize_digest]

private abbrev Both (s : Level) :=
  (fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ DigestOracle s

private abbrev DigestCache (s : Level) := List (Point s × Digest s)

private noncomputable def stepAt (s : Level) (v : PublicMatrix s) :=
  RandomOracle.memoizeSum (fun _ : FixedBytes 32 => PMF.pure v)
    (fun _ : Point s => PMF.uniformOfFintype (Digest s))

private theorem tape_run {s : Level} {α : Type} (program : OracleComp (Both s) α)
    (mc : Cache s) (dc : DigestCache s) (tape : List (PublicMatrix s)) :
    ((interpret (Protocols.ROMSignature.oracle (Digest s))
      ((interpret (withSampleList 0 (handler s)) program).run (mc, tape))).run dc).map
      (fun ((a, (mc', tape')), dc') => (a, (mc', dc'), tape')) =
    (interpret (withSampleList 0 (stepAt s)) program).run ((mc, dc), tape) := by
  rw [run_interpret_run_interpret]
  simp only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  refine run_interpret_map_state _ _ (fun st => ((st.1.1, st.2), st.1.2)) ?_ program
    ((mc, tape), dc)
  rintro (k | p) ⟨⟨m, t⟩, d⟩
  · cases h : m.lookup k <;>
      simp only [StateT.run, withSampleList, handler, sumHandler, memoize, h, bind_pure_comp,
        map_pure, interpret_pure, stepAt, RandomOracle.memoizeSum_inl, pmf_norm, Function.comp_def]
    all_goals
      change PMF.map _ (PMF.pure _) = _
      simp
  · simp only [StateT.run, withSampleList, handler, sumHandler, interpret_map, interpret_query,
      stepAt, RandomOracle.memoizeSum_inr, memoize_digest, Functor.map_map, pmf_norm,
      Function.comp_def]
    change PMF.map _ ((Protocols.ROMSignature.oracle (Digest s) p d).map
      (fun (a, state) => ((a, m, t.tail), state))) = _
    rw [PMF.map_comp]
    rfl

private theorem run_both {s : Level} {α : Type} {program : OracleComp (Both s) α} {Q : ℕ}
    (hQ : program.IsQueryBounded Q) (mc : Cache s) (dc : DigestCache s) :
    ((PMF.iid (PMF.uniformOfFintype (PublicMatrix s)) Q).map List.ofFn).bind (fun tape =>
      (interpret (Protocols.ROMSignature.oracle (Digest s))
        (Prod.fst <$> (interpret (withSampleList 0 (handler s)) program).run (mc, tape))).run dc) =
      ((interpret (RandomOracle.memoizeSum
        (fun _ : FixedBytes 32 => PMF.uniformOfFintype (PublicMatrix s))
        (fun _ : Point s => PMF.uniformOfFintype (Digest s))) program).run (mc, dc)).map
        fun (a, _, dc') => (a, dc') := by
  let fresh := PMF.uniformOfFintype (PublicMatrix s)
  have hp := hQ.run_interpret_presample fresh 0 (stepAt s) (mc, dc)
  have online (q : FixedBytes 32 ⊕ Point s) (state : Cache s × DigestCache s) :
      (fresh.bind fun v => stepAt s v q state) = RandomOracle.memoizeSum
        (fun _ : FixedBytes 32 => fresh) (fun _ : Point s => PMF.uniformOfFintype (Digest s))
        q state := by
    rcases state with ⟨m, d⟩
    rcases q with k | p
    · cases h : m.lookup k with
      | none => simp [stepAt, RandomOracle.memoizeSum_inl, memoize_of_none _ k m h, pmf_norm]
      | some v => simp [stepAt, RandomOracle.memoizeSum_inl, memoize_of_some _ k m v h, pmf_norm]
    · simp only [stepAt, RandomOracle.memoizeSum_inr, PMF.bind_const]
  simp only [online] at hp
  rw [← hp, PMF.map_bind]
  congr 1 with tape
  rw [run_interpret_map, ← tape_run]
  simp only [PMF.map_comp, PMF.monad_map_eq_map, Function.comp_def]
  rfl

private def trial {Coins : Type} (s : Level) (adv : Forger s Coins) (r : Saved s Coins)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) : ProbComp Bool :=
  runDigest s (do
    let f ← runForger s adv r ⟨A, t⟩
    verify s (encodePublic s r.seed.toList t) A f)

/-- Run the byte forger and verifier on a full Module-LWE challenge with the indicated
distribution of private coins, a public seed, and saved matrix answers. Their digest cache is
shared through verification. -/
def distinguisherFromSaved {Coins : Type} (s : Level) (saved : ProbComp (Saved s Coins))
    (adv : Forger s Coins) (A : PublicMatrix s) (t : Fin s.params.k → Poly) : ProbComp Bool := do
  let r ← saved
  trial s adv r A t

/-- The Module-LWE distinguisher with independent, exactly uniform auxiliary matrices. -/
def distinguisher {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins)
    (adv : Forger s Coins) :=
  distinguisherFromSaved s (sampleSaved s Q coins) adv

private theorem fixed_le {Coins : Type} (s : Level) (adv : Forger s Coins) (r : Saved s Coins)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    (trial s adv r A t).eval true ≤
        ModuleSIS.SelfTarget.game (expandDigest s) (compressedSelfTargetRadius s.params 13)
          (PMF.pure r) (solver s adv) (systematic s A t) true := by
  simp only [trial, eval_runDigest, run_interpret_bind, ModuleSIS.SelfTarget.game, solver,
    fullKey_systematic, interpret_map, StateT.run_map, pmf_norm, Function.comp_def]
  apply Probability.PMF.bind_apply_mono_on_support
  intro result _
  obtain ⟨f, cache⟩ := result
  cases ho : opening s f with
  | none => simp [verify, ho]
  | some o =>
    have hp := product_witness s r.seed A t f o
    simp only [verify, length_encodePublic, FixedBytes.length_toList, ite_true, ho, extract,
      ModuleSIS.SelfTarget.product, hp, run_interpret_bind, run_interpret_query,
      run_interpret_pure, pmf_norm]
    apply Probability.PMF.bind_apply_mono_on_support
    intro result _
    obtain ⟨d, cache'⟩ := result
    by_cases he : d.toList = o.signature.digest
    · simp [he, accepts_digest_of_opening (⟨A, t⟩) (encodePublic s r.seed.toList t) ho he]
    · simp [he]

private noncomputable def matrixDigestOracle (s : Level) :=
  RandomOracle.memoizeSum (fun _ : FixedBytes 32 => PMF.uniformOfFintype (PublicMatrix s))
    (fun _ : Point s => PMF.uniformOfFintype (Digest s))

private noncomputable def onlineTrial {Coins : Type} (s : Level) (adv : Forger s Coins) (r : Coins)
    (rho : FixedBytes 32) (A : PublicMatrix s) (t : Fin s.params.k → Poly)
    (cache : Cache s × DigestCache s) : Game := do
  let bytes := encodePublic s rho.toList t
  let (f, _, dc) ← (interpret (matrixDigestOracle s) (adv bytes r)).run cache
  ((interpret (Protocols.ROMSignature.oracle (Digest s)) (verify s bytes A f)).run dc).map Prod.fst

private theorem trial_eq_online {Coins : Type} (s : Level) (Q : ℕ) (adv : Forger s Coins)
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) (r : Coins) (rho : FixedBytes 32)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    (PMF.iid (PMF.uniformOfFintype (PublicMatrix s)) Q).bind (fun tape =>
      (trial s adv ⟨r, rho, List.ofFn tape⟩ A t).eval) =
      onlineTrial s adv r rho A t ([(rho, A)], []) := by
  let bytes := encodePublic s rho.toList t
  let finish (x : Forgery × DigestCache s) :=
    ((interpret (Protocols.ROMSignature.oracle (Digest s))
      (verify s bytes A x.1)).run x.2).map Prod.fst
  have h := congrArg (fun μ => PMF.bind μ finish)
    (run_both (hQ bytes r) [(rho, A)] [])
  simpa only [trial, eval_runDigest, runForger, onlineTrial, matrixDigestOracle, bytes, finish,
    run_interpret_bind, pmf_norm, Function.comp_def] using h

/-- Run the byte forger and final digest check with the matrix cache left by key generation
and an initially empty digest cache. Both share all digest entries throughout the trial. -/
noncomputable def observe {Coins : Type} (s : Level) (coins : ProbComp Coins)
    (adv : Forger s Coins) : MatrixOracle.Observable s := fun rho A t cache => do
  let r ← coins.eval
  onlineTrial s adv r rho A t (cache, [])

/-- The raw classical matrix-seed and digest-word interfaces. -/
abbrev RawOracleSpec (s : Level) := (fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ
  (fun _ : List Bool => FixedBytes (digestBytes s))

/-- Classical byte forgers may query the digest at arbitrary bit strings. -/
abbrev RawForger (s : Level) (Coins : Type) :=
  List Byte → Coins → OracleComp (RawOracleSpec s) Forgery

private def rawQueries (s : Level) : (q : FixedBytes 32 ⊕ List Bool) →
    OracleComp (Both s) (RawOracleSpec s q) :=
  sumHandler (fun k => query (spec := Both s) (.inl k))
    (fun w => query (spec := Both s) (.inr (rawPoint s w)))

/-- Run a raw byte forger using one algebraic-oracle query for each raw-word query. -/
def pointForger {Coins : Type} (s : Level) (adv : RawForger s Coins) : Forger s Coins :=
  fun pk r => interpret (rawQueries s) (adv pk r)

theorem pointForger_bounded {Coins : Type} {s : Level} {adv : RawForger s Coins} {bytes r Q}
    (h : (adv bytes r).IsQueryBounded Q) : (pointForger s adv bytes r).IsQueryBounded Q := by
  apply h.interpret
  rintro (k | w) <;> exact IsCostBounded.query _

private def rawVerifier (s : Level) (bytes : List Byte) (A : PublicMatrix s) (f : Forgery) :
    OracleComp (RawOracleSpec s) Bool :=
  interpret (fun p => query (.inr (pointAddress s p))) (verify s bytes A f)

private theorem rawVerifier_point (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) :
    interpret (rawQueries s) (rawVerifier s bytes A f) =
      liftRight (spec₁ := fun _ : FixedBytes 32 => PublicMatrix s) (verify s bytes A f) := by
  rw [rawVerifier, interpret_interpret, liftRight, substitute_eq_interpret]
  apply interpret_verify_congr
  intro p hm hv
  simp only [interpret_query, rawQueries, sumHandler]
  rw [rawPoint_pointAddress (s := s) (p := p) hm hv]

private noncomputable def rawOracle (s : Level) :=
  RandomOracle.memoizeSum (fun _ : FixedBytes 32 => PMF.uniformOfFintype (PublicMatrix s))
    (fun _ : List Bool => PMF.uniformOfFintype (Digest s))

private theorem run_raw {s : Level} {α : Type} (prog : OracleComp (RawOracleSpec s) α)
    (mc : Cache s) (dc : List (List Bool × Digest s)) :
    ((interpret (rawOracle s) prog).run (mc, dc)).map
        (fun (a, m, d) => (a, m, d.map fun e => (rawPoint s e.1, e.2))) =
      (interpret (matrixDigestOracle s) (interpret (rawQueries s) prog)).run
        (mc, dc.map fun e => (rawPoint s e.1, e.2)) := by
  rw [interpret_interpret]
  refine run_interpret_map_state _ _ (fun st => (st.1, st.2.map fun e => (rawPoint s e.1, e.2)))
    ?_ prog (mc, dc)
  rintro (k | w) ⟨m, d⟩
  · simp only [rawOracle, rawQueries, sumHandler, interpret_query, matrixDigestOracle,
      RandomOracle.memoizeSum_inl, PMF.map_comp, Function.comp_def]
  · simp only [rawOracle, rawQueries, sumHandler, interpret_query, matrixDigestOracle,
      RandomOracle.memoizeSum_inr, PMF.map_comp, Function.comp_def]
    have h := memoize_map (m := PMF) (rawPoint s) (id : Digest s → _)
      (fun _ => PMF.uniformOfFintype _) (fun _ => PMF.uniformOfFintype _)
      (fun _ => (PMF.map_id _).symm) w d
    have h' := congrArg (PMF.map (fun (a, d') => (a, m, d'))) h
    simpa only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, id_eq] using h'

/-- The raw classical game runs the verifier on the same digest cache as the adversary.
Both use the literal untagged FIPS commitment string. -/
noncomputable def observeRaw {Coins : Type} (s : Level) (coins : ProbComp Coins)
    (adv : RawForger s Coins) : MatrixOracle.Observable s := fun rho A t mc => do
  let r ← coins.eval
  let bytes := encodePublic s rho.toList t
  ((interpret (rawOracle s) (adv bytes r >>= rawVerifier s bytes A)).run (mc, [])).map Prod.fst

/-- Exact raw-address simulation, including the final byte check, unrestricted adaptive
queries, repeated words and words outside the FIPS commitment grid. -/
theorem observeRaw_eq {Coins : Type} (s : Level) (coins : ProbComp Coins)
    (adv : RawForger s Coins) :
    observeRaw s coins adv = observe s coins (pointForger s adv) := by
  funext rho A t mc
  apply congrArg (PMF.bind coins.eval)
  funext r
  let bytes := encodePublic s rho.toList t
  let checked := adv bytes r >>= rawVerifier s bytes A
  have h := congrArg (PMF.map Prod.fst) (run_raw checked mc [])
  simp only [PMF.map_comp, Function.comp_def, List.map_nil] at h
  refine h.trans ?_
  simp only [checked, interpret_bind, rawVerifier_point, StateT.run_bind, PMF.monad_bind_eq_bind,
    onlineTrial, pointForger, PMF.map_bind]
  apply congrArg (PMF.bind _)
  funext ⟨f, m, d⟩
  rw [show matrixDigestOracle s = RandomOracle.memoizeSum _ _ from rfl,
    RandomOracle.run_interpret_memoizeSum_liftRight, PMF.map_comp]
  have same : memoize (fun _ : Point s => PMF.uniformOfFintype (Digest s)) =
      Protocols.ROMSignature.oracle (Digest s) := by
    funext p cache
    exact memoize_digest s p cache
  rw [same]
  rfl

/-- The Hermite instance obtained by prefixing the identity to a single uniform right block. -/
noncomputable def instances (s : Level) : PMF
    (Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly) :=
  (PMF.uniformOfFintype (RightBlock s)).map ModuleSIS.hermiteMatrix

/-- Independent uniform draws of `A,t` produce precisely the standard Hermite distribution. -/
theorem instances_eq_sample (s : Level) :
    instances s = (do
      let A ← PMF.uniformOfFintype (PublicMatrix s)
      let t ← PMF.uniformOfFintype (Fin s.params.k → Poly)
      return systematic s A t) := by
  rw [instances, ← PMF.uniformOfFintype_map_equiv (rightBlock s), ← PMF.uniformOfFintype_prod]
  simp only [PMF.map_comp, pmf_norm, systematic, Function.comp_def]
  rfl

/-- The real Module-LWE challenge with the explicit distinguisher reproduces the entire
online key-only acceptance law, including adaptive seed lookups and continued verification
with the digest cache. The query bound justifies presampling the reduction's matrix tape. -/
theorem keyOnlyGame_eq_moduleLWE_realGame {Coins : Type} (s : Level) (Q : ℕ)
    (coins : ProbComp Coins) (adv : Forger s Coins)
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) :
    MatrixOracle.realKeyGame s (observe s coins adv) =
      ModuleLWE.realGame (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) (distinguisher s Q coins adv) := by
  apply MatrixOracle.realKeyGame_eq_realGame_of_planted
  intro A t
  simp only [MatrixOracle.planted, observe, distinguisher, distinguisherFromSaved, sampleSaved,
    ProbComp.eval_bind,
    ProbComp.eval_pure, eval_sampleBytes, ProbComp.eval_replicateFin,
    MatrixOracle.eval_sampleMatrix,
    ← PMF.iid_eq_pi, pmf_norm, trial_eq_online s Q adv hQ]
  pmf_swap

private theorem random_le_selfTarget {Coins : Type} (s : Level) (saved : ProbComp (Saved s Coins))
    (adv : Forger s Coins) :
    ModuleLWE.randomGame (distinguisherFromSaved s saved adv) true ≤
      ((instances s).bind (ModuleSIS.SelfTarget.game (expandDigest s)
        (compressedSelfTargetRadius s.params 13) saved.eval
        (solver s adv))) true := by
  simp only [ModuleLWE.randomGame, ModuleLWE.eval_randomExperiment, distinguisherFromSaved,
    ProbComp.eval_bind, instances_eq_sample, ModuleSIS.SelfTarget.game, pmf_norm]
  apply Probability.PMF.bind_apply_mono_on_support
  intro A _
  apply Probability.PMF.bind_apply_mono_on_support
  intro t _
  apply Probability.PMF.bind_apply_mono_on_support
  intro r _
  simpa only [ModuleSIS.SelfTarget.game, pmf_norm] using fixed_le s adv r A t

/-- Replay the two forgeries on a Hermite right block. Each of the two tapes has `Q + 1`
independent FIPS digests, and both runs use the same adversary coins and matrix tape. -/
def kernelSolver {Coins : Type} (s : Level) (Q : ℕ) (saved : ProbComp (Saved s Coins))
    (adv : Forger s Coins) (B : Matrix (Fin s.params.k) (Fin (s.params.ℓ + 1)) Poly) :
    ProbComp (Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ) :=
  ModuleSIS.SelfTarget.reduction 0 (expandDigest s) (compressedSelfTargetRadius s.params 13) Q
    saved (replicateFin (Q + 1) (sampleBytes (digestBytes s)))
    (solver s adv) (ModuleSIS.hermiteMatrix B)

private theorem eval_hermite {Coins : Type} (s : Level) (Q : ℕ) (saved : ProbComp (Saved s Coins))
    (adv : Forger s Coins) :
    let R := compressedSelfTargetRadius s.params 13
    (ModuleSIS.hermiteExperiment (2 * R) (kernelSolver s Q saved adv)).eval =
      (instances s).bind fun M => (ModuleSIS.SelfTarget.reductionLaw 0 (expandDigest s) R Q
        saved.eval (solver s adv) M).map
          fun z => decide (ModuleSIS.IsSolution M (2 * R) z) := by
  dsimp only
  have tape : ProbComp.eval (replicateFin (Q + 1) (sampleBytes (digestBytes s))) =
      PMF.uniformOfFintype _ := by
    simp only [ProbComp.eval_replicateFin, eval_sampleBytes, PMF.pi_uniformOfFintype]
  simp only [ModuleSIS.hermiteExperiment, instances, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, kernelSolver, ModuleSIS.SelfTarget.eval_reduction
      _ _ _ _ _ _ tape, PMF.bind_map, Function.comp_def]
  rfl

private theorem real_le_moduleLWE_add_fork {Coins : Type} (s : Level) (Q : ℕ)
    (saved : ProbComp (Saved s Coins)) (adv : Forger s Coins)
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) :
    let radius := compressedSelfTargetRadius s.params 13
    let D := distinguisherFromSaved s saved adv
    ((ModuleLWE.realGame (MatrixOracle.shortVectorLaw s s.params.ℓ)
      (MatrixOracle.shortVectorLaw s s.params.k) D) true).toReal ≤
      ModuleLWE.advantage (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) D +
      ((Q + 1 : ℕ) / ((256 : ℝ) ^ digestBytes s) + Real.sqrt ((Q + 1 : ℕ) *
        ((ModuleSIS.hermiteExperiment (2 * radius)
          (kernelSolver s Q saved adv)).eval true +
              ModuleSIS.SelfTarget.collisionMass (expandDigest s)).toReal)) := by
  dsimp only
  rw [eval_hermite]
  have hs := selfTarget_digest_fork s Q (instances s) saved.eval (solver s adv) (solver_bounded hQ)
  have hr := (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (random_le_selfTarget s saved adv)).trans hs
  have hl := Game.coe_succProbability_le_add_of_advantage_le
    (g₀ := ModuleLWE.realGame (MatrixOracle.shortVectorLaw s s.params.ℓ)
      (MatrixOracle.shortVectorLaw s s.params.k) (distinguisherFromSaved s saved adv))
    (g₁ := ModuleLWE.randomGame (distinguisherFromSaved s saved adv)) (le_refl _)
  rw [Game.coe_succProbability, Game.coe_succProbability] at hl
  exact hl.trans (by rw [add_comm]; exact add_le_add le_rfl hr)

/-- Raw-word classical key-only forgery is bounded by short-secret MLWE, a two-run Hermite
Module-SIS experiment and the collision probability of concrete Algorithm 29 on SHAKE256
digests. Its only bound here is one. A final digest lookup covers a forgery on a fresh point. -/
theorem keyOnly_le_moduleLWE_add_fork {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins)
    (rawAdv : RawForger s Coins) (hQ : ∀ bytes r, (rawAdv bytes r).IsQueryBounded Q) :
    let adv := pointForger s rawAdv
    let radius := compressedSelfTargetRadius s.params 13
    ((MatrixOracle.realKeyGame s (observeRaw s coins rawAdv)) true).toReal ≤
      ModuleLWE.advantage (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) (distinguisher s Q coins adv) +
      ((Q + 1 : ℕ) / ((256 : ℝ) ^ digestBytes s) + Real.sqrt ((Q + 1 : ℕ) *
        ((ModuleSIS.hermiteExperiment (2 * radius)
          (kernelSolver s Q (sampleSaved s Q coins) adv)).eval true +
              ModuleSIS.SelfTarget.collisionMass (expandDigest s)).toReal)) := by
  let adv := pointForger s rawAdv
  have bounded (bytes r) : (adv bytes r).IsQueryBounded Q := pointForger_bounded (hQ bytes r)
  rw [observeRaw_eq, keyOnlyGame_eq_moduleLWE_realGame s Q coins adv bounded]
  exact real_le_moduleLWE_add_fork s Q (sampleSaved s Q coins) adv bounded

/-- Classical key-only reduction with bounded fair-bit sampling of every auxiliary matrix.
The `Q`-entry matrix tape is drawn once and replayed across the fork. The challenger supplies
the matrix at the public seed. Only the change from the real online oracle to the bounded
distinguisher incurs a statistical loss. -/
theorem keyOnly_le_moduleLWE_add_fork_fairMatrices {Coins : Type} (s : Level) (Q attempts : ℕ)
    (coins : ProbComp Coins) (rawAdv : RawForger s Coins)
    (hQ : ∀ bytes r, (rawAdv bytes r).IsQueryBounded Q) :
    let adv := pointForger s rawAdv
    let radius := compressedSelfTargetRadius s.params 13
    let saved := sampleSaved s Q coins (MatrixOracle.sampleMatrixFair s attempts)
    ((MatrixOracle.realKeyGame s (observeRaw s coins rawAdv)) true).toReal ≤
      (Q * s.params.k * s.params.ℓ * 256 : ℕ) * (8191 / 8388608 : ℝ) ^ attempts +
      (ModuleLWE.advantage (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) (distinguisherFromSaved s saved adv) +
      ((Q + 1 : ℕ) / ((256 : ℝ) ^ digestBytes s) + Real.sqrt ((Q + 1 : ℕ) *
        ((ModuleSIS.hermiteExperiment (2 * radius)
          (kernelSolver s Q saved adv)).eval true +
              ModuleSIS.SelfTarget.collisionMass (expandDigest s)).toReal))) := by
  let adv := pointForger s rawAdv
  have bounded (bytes r) : (adv bytes r).IsQueryBounded Q := pointForger_bounded (hQ bytes r)
  rw [observeRaw_eq]
  let saved := sampleSaved s Q coins (MatrixOracle.sampleMatrixFair s attempts)
  let δ : ℝ := (Q * s.params.k * s.params.ℓ * 256 : ℕ) * (8191 / 8388608 : ℝ) ^ attempts
  have ht := (closeTo_of_dist_le_ofReal (MatrixOracle.dist_matrixTapeFair_le s Q attempts)).symm
  have hreal : CloseTo (MatrixOracle.realKeyGame s (observe s coins adv))
      (ModuleLWE.realGame (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) (distinguisherFromSaved s saved adv))
      (ENNReal.ofReal δ) := by
    rw [keyOnlyGame_eq_moduleLWE_realGame s Q coins adv bounded]
    simp only [ModuleLWE.realGame, ModuleLWE.eval_realExperiment, distinguisher,
      distinguisherFromSaved, saved, sampleSaved, ProbComp.eval_bind, ProbComp.eval_pure, pmf_norm]
    iterate 5
      apply CloseTo.bind_right
      intro _ _
    rw [ProbComp.eval_replicateFin, MatrixOracle.eval_sampleMatrix, PMF.pi_uniformOfFintype]
    exact ht.bind_left _
  have hp := hreal.abs_toReal_sub_le (by dsimp [δ]; positivity) {true}
  simp only [PMF.toOuterMeasure_apply_singleton] at hp
  have h := real_le_moduleLWE_add_fork s Q saved adv bounded
  exact (sub_le_iff_le_add.mp (abs_le.mp hp).2).trans (add_le_add_right h δ)

end Cslib.Crypto.MLDSA.FIPS204.SharedDigest
