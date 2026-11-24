/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.RandomXofMatrix
public import CslibFrontier.Crypto.Computational.MLDSA.SigningSimulation
public import CslibFrontier.Probability.IID.FirstSome
-- Reads private `Table`, `RawWord`, `install`, and `byteAt_install`, plus `uniformPrefixes`.
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
-- Reads private `verified_programmedTrial` and unexposed `matrixTrial` and `programmedTrial`.
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
-- Reads private `AttemptCommitment`, `expandMaskFrom`, `firstAccepted`, and `Xofs.expandMask`.
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
-- Unfolds unexposed `packSigned`, `unpackSigned`, `Level.params`, and `commitmentDigest`.
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
-- Reads private `maskSet`, `mask_nonempty`, and `mem_intervalVectors`, plus `signingMaskLaw`.
import all CslibFrontier.Crypto.Computational.MLDSA.SigningSimulation
import CslibFrontier.Probability.PMF.UniformExtend
import CslibFrontier.Probability.PMF.Support

/-!
# Algorithm 34 masks in the shared random-XOF signing game

[FIPS 204][NISTFIPS204], Algorithms 7 and 34, read one SHAKE256 stream per 64-byte masking
seed and two-byte nonce. BitUnpack sends its initial bytes bijectively to the signed
coefficient box. The table is indexed by the literal 528-bit input and sampled before any
key generation or quantum interaction. Its other uses, including Algorithm 33 at a coincident
address and longer adversarial queries, see the same bytes. When those expansion bytes are
private, the full capped signing loop has the same signature-or-failure law as drawing a fresh
mask from `signingMaskLaw` on every attempt. Both executions hash each commitment with the
ambient XOF and stop on sparse-challenge exhaustion.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- One signed integer from Algorithm 34's half-open interval `(-γ₁, γ₁]`. -/
abbrev MaskCoefficient (s : Level) := ↥(Finset.Ioc (-(s.params.γ₁ : ℤ)) (s.params.γ₁ : ℤ))

/-- At a 528-bit masking seed and nonce address, store all 256 signed coefficients. -/
abbrev MaskTable (s : Level) := BitString 528 → Fin 256 → MaskCoefficient s

instance (s : Level) : Nonempty (MaskCoefficient s) :=
  ⟨⟨0, Finset.mem_Ioc.mpr (by
    have h : 0 < s.params.γ₁ := by cases s <;> decide
    exact ⟨by lia, by lia⟩)⟩⟩

private abbrev width (s : Level) := s.params.γ₁.log2 + 1

private theorem range_width (s : Level) : 2 ^ width s = 2 * s.params.γ₁ := by cases s <;> decide

private def ringRow {s : Level} (r : Fin 256 → MaskCoefficient s) : Poly :=
  fun j => ((r j).val : ZMod 8380417)

private theorem centered {s : Level} (r : Fin 256 → MaskCoefficient s) (j : Fin 256) :
    ((ringRow r) j).valMinAbs = (r j).val := by
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_⟩
  have bounds := Finset.mem_Ioc.mp (r j).property
  have limit : 2 * s.params.γ₁ < 8380417 := by cases s <;> decide
  constructor <;> norm_num <;> lia

private def packRow (s : Level) (r : Fin 256 → MaskCoefficient s) : FixedBytes (32 * width s) :=
  fun i => (packSigned (width s) s.params.γ₁ (fun _ : Fin 1 => ringRow r))[i.val]'(by
    simpa only [packSigned, length_packCoeffs, Nat.mul_one] using i.isLt)

private theorem packRow_list (s : Level) (r : Fin 256 → MaskCoefficient s) :
    (packRow s r).toList = packSigned (width s) s.params.γ₁ (fun _ : Fin 1 => ringRow r) := by
  apply List.ext_getElem
  · simp [packSigned]
  · intro i hi _
    simp only [FixedBytes.toList, List.getElem_ofFn, packRow]

private theorem unpack_row (s : Level) (r : Fin 256 → MaskCoefficient s) (j : Fin 256) :
    ((unpackSigned 1 (width s) s.params.γ₁ (packRow s r).toList).get 0).get j = (ringRow r) j := by
  rw [packRow_list]
  apply (List.append_nil _ ▸ unpackSigned_packSigned (width := width s) (upper := s.params.γ₁)
    (fun _ : Fin 1 => ringRow r) [] ?_ 0 j)
  intro _ j
  rw [centered, range_width]
  have bounds := Finset.mem_Ioc.mp (r j).property
  lia

private noncomputable def packedEquiv (s : Level) :
    (Fin 256 → MaskCoefficient s) ≃ FixedBytes (32 * width s) :=
  Equiv.ofBijective (packRow s) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
    intro u v h
    funext j
    apply Subtype.ext
    rw [← centered u j, ← centered v j, ← unpack_row s u j, ← unpack_row s v j, h], by
    have size : Fintype.card (MaskCoefficient s) = 2 ^ width s := by
      rw [range_width]
      simp only [MaskCoefficient, Fintype.card_coe, Int.card_Ioc]
      lia
    simp only [FixedBytes, Fintype.card_fun, size, Fintype.card_fin, Byte]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring⟩)

/-- The raw SHAKE256 word for one Algorithm 34 polynomial, including the two-byte nonce.
Algorithm 33 accesses precisely the same stream if supplied the same word. -/
def maskAddress (seed : FixedBytes 64) (nonce : ℕ) : BitString 528 :=
  BitString.ofList 528 (Keccak.bytesToBitsLE (nonceInput seed.toList nonce))

private theorem maskAddress_bits (seed : FixedBytes 64) (nonce : ℕ) :
    List.ofFn (maskAddress seed nonce) = Keccak.bytesToBitsLE (nonceInput seed.toList nonce) :=
  BitString.ofFn_ofList (length_nonceInput_bits seed nonce)

private abbrev MaskByte (s : Level) := BitString 528 × Fin (maskPolyBytes s)

private noncomputable def packedTable (s : Level) : MaskTable s ≃ (MaskByte s → Byte) where
  toFun t p := packRow s (t p.1) p.2
  invFun t x := (packedEquiv s).symm (fun i => t (x, i))
  left_inv t := funext fun x => (packedEquiv s).symm_apply_apply (t x)
  right_inv t := funext fun p => congrFun ((packedEquiv s).apply_symm_apply
    (fun i => t (p.1, i))) p.2

private def maskPoint {s : Level} {a b : ℕ} (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b)
    (p : MaskByte s) : RawWord a × Fin b :=
  (word (List.ofFn p.1) (by rwa [List.length_ofFn]), Fin.castLE hb p.2)

private theorem maskPoint_injective {s : Level} {a b : ℕ} (ha : 528 ≤ a)
    (hb : maskPolyBytes s ≤ b) : Function.Injective (maskPoint ha hb) := by
  intro p q h
  have raw := congrArg (fun v : RawWord a × Fin b => List.ofFn v.1.2) h
  simp only [maskPoint, word, BitString.ofFn_ofList rfl] at raw
  exact Prod.ext (List.ofFn_inj.mp raw) (Fin.ext (congrArg (fun v => v.2.val) h))

/-- Sample the finite raw XOF pair with its Algorithm 34 prefixes set to the packed signed
polynomials in `masks`. Every other sampled byte, including each longer stream suffix,
is independent and uniform. The background supplies bytes beyond the finite table. -/
noncomputable def Xofs.sampleWithMasks (base : Xofs) {s : Level} {a b : ℕ}
    (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b) (masks : MaskTable s) : PMF Xofs := do
  let t₂ ← PMF.uniformOfFintype (Table a b)
  let t₁ ← PMF.uniformOfFintype (Table a b)
  return ⟨install base.h128 t₁, install base.h256
    (Function.extend (maskPoint ha hb) (packedTable s masks) t₂)⟩

/-- Installing independent uniform signed mask coefficients before key generation preserves
the distribution of the entire finite pair of raw SHAKE oracles. Any subsequent signing and
coherent quantum access, including repeated or overlapping reads, uses that same pair. -/
theorem Xofs.uniform_sampleWithMasks (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b) :
    (PMF.uniformOfFintype (MaskTable s)).bind (base.sampleWithMasks ha hb) =
      base.uniformPrefixes a b := by
  let finish (t₂ : Table a b) := (PMF.uniformOfFintype (Table a b)).map fun t₁ =>
    Xofs.mk (install base.h128 t₁) (install base.h256 t₂)
  have eq := PMF.uniformOfFintype_bind_bind_extend (κ := Byte) (maskPoint ha hb) finish
  rw [← PMF.uniformOfFintype_map_equiv (packedTable s)] at eq
  simp only [PMF.bind_map, Function.comp_def] at eq
  rw [independent_tables]
  unfold Xofs.sampleWithMasks
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm (PMF.uniformOfFintype (MaskTable s))]
  simpa only [finish, PMF.map, Function.comp_def] using eq

private theorem read_mask_row {s : Level} {a b : ℕ} (ha : 528 ≤ a)
    (hb : maskPolyBytes s ≤ b) (base : ExtendableOutput) (t : Table a b) (masks : MaskTable s)
    (seed : FixedBytes 64) (nonce : ℕ) :
    (install base (Function.extend (maskPoint ha hb) (packedTable s masks) t)).readBytes
      (nonceInput seed.toList nonce) (maskPolyBytes s) =
        (packRow s (masks (maskAddress seed nonce))).toList := by
  let x := Keccak.bytesToBitsLE (nonceInput seed.toList nonce)
  let G := install base (Function.extend (maskPoint ha hb) (packedTable s masks) t)
  change G.read x (maskPolyBytes s) = _
  apply List.ext_getElem
  · rw [G.length_read, FixedBytes.length_toList]
  · intro i hi _
    have hit : i < maskPolyBytes s := hi.trans_le (G.length_read ..).le
    let k : MaskByte s := (maskAddress seed nonce, ⟨i, hit⟩)
    have hx : x.length ≤ a := (length_nonceInput_bits seed nonce).le.trans ha
    have loc : maskPoint ha hb k = (word x hx, ⟨i, hit.trans_le hb⟩) := by
      unfold maskPoint k
      simp only [maskAddress_bits]
      rfl
    rw [ExtendableOutput.getElem_read G x hit]
    simp only [G, byteAt_install, dite_eq_left (And.intro hx (hit.trans_le hb)), ← loc,
      (maskPoint_injective ha hb).extend_apply, FixedBytes.toList, List.getElem_ofFn]
    rfl

/-- The raw SHAKE256 read at the seed and nonce returns the FIPS packing of the supplied
coefficients. This is also the stream available to Algorithm 33 and coherent prefix queries. -/
theorem Xofs.read_mask_of_mem_sampleWithMasks {base H : Xofs} {s : Level} {a b : ℕ}
    {ha : 528 ≤ a} {hb : maskPolyBytes s ≤ b} {masks : MaskTable s}
    (h : H ∈ (base.sampleWithMasks ha hb masks).support) (seed : FixedBytes 64) (nonce : ℕ) :
    H.h256.readBytes (nonceInput seed.toList nonce) (maskPolyBytes s) =
      packSigned (s.params.γ₁.log2 + 1) s.params.γ₁ (fun _ : Fin 1 => fun j =>
        ((masks (maskAddress seed nonce) j).val : ZMod 8380417)) := by
  simp only [Xofs.sampleWithMasks, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨t₂, _, t₁, _, rfl⟩ := h
  exact (read_mask_row ha hb base.h256 t₂ masks seed nonce).trans (packRow_list ..)

/-- At every oracle in the sampled pair, the actual Algorithm 34 decoder returns the
specified signed coefficients at the actual raw input. This is simultaneous over all masking
seeds and counters, including seeds chosen from that same oracle and all 814 signing attempts. -/
theorem Xofs.expandMask_of_mem_sampleWithMasks {base H : Xofs} {s : Level} {a b : ℕ}
    {ha : 528 ≤ a} {hb : maskPolyBytes s ≤ b} {masks : MaskTable s}
    (h : H ∈ (base.sampleWithMasks ha hb masks).support) (seed : FixedBytes 64) (κ : ℕ)
    (i : Fin s.params.ℓ) (j : Fin 256) :
    (((H.expandMask s seed.toList κ).get i).get j) =
      ((masks (maskAddress seed (κ + i.val)) j).val : ZMod 8380417) := by
  simp only [Xofs.expandMask, expandMaskFrom, Vector.get_ofFn]
  rw [Xofs.read_mask_of_mem_sampleWithMasks h seed (κ + i.val)]
  let row := masks (maskAddress seed (κ + i.val))
  change ((unpackSigned 1 (width s) s.params.γ₁
    (packSigned (width s) s.params.γ₁ (fun _ : Fin 1 => ringRow row))).get 0).get j = _
  rw [← packRow_list]
  exact unpack_row s row j

private abbrev ScheduledRow (s : Level) := Fin 814 × Fin s.params.ℓ

private def schedule (s : Level) (p : ScheduledRow s) : ℕ :=
  signingAttemptCounter s.params 0 p.1 + p.2.val

private theorem nonce_lt (s : Level) (p : ScheduledRow s) : schedule s p < 65536 := by
  have h := p.1.isLt
  have hi := p.2.isLt
  cases s <;> dsimp [schedule, signingAttemptCounter, Level.params, Params.mldsa44,
    Params.mldsa65, Params.mldsa87] at * <;> lia

private theorem schedule_injective (s : Level) (seed : FixedBytes 64) :
    Function.Injective (fun p : ScheduledRow s => maskAddress seed (schedule s p)) := by
  intro p q h
  have raw := congrArg List.ofFn h
  simp only [maskAddress_bits] at raw
  have same := eq_of_nonceInput_eq (nonce_lt s p) (nonce_lt s q)
    (Keccak.bytesToBitsLE_injective raw)
  have ip := p.2.isLt
  have iq := q.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> cases s <;>
    dsimp [schedule, signingAttemptCounter, Level.params, Params.mldsa44, Params.mldsa65,
      Params.mldsa87] at * <;> lia

/-- At a fixed masking seed, the 814 scheduled Algorithm 7 attempts occupy distinct
Algorithm 34 addresses. Their entire array of signed coefficient rows is uniform together,
including the last polynomial of the last attempt. -/
private theorem uniform_scheduledMasks (s : Level) (seed : FixedBytes 64) :
    (PMF.uniformOfFintype (MaskTable s)).map (fun masks (p : Fin 814 × Fin s.params.ℓ) =>
      masks (maskAddress seed (schedule s p))) =
    PMF.uniformOfFintype (Fin 814 × Fin s.params.ℓ → Fin 256 → MaskCoefficient s) :=
  PMF.uniformOfFintype_pi_map_comp_embedding
    (α := Fin 256 → MaskCoefficient s) ⟨_, schedule_injective s seed⟩

/-- In the original joint random-XOF experiment, Algorithm 34 at a fixed seed produces an
independent uniform signed coefficient at every position in the full 814-attempt schedule.
The output coefficients are embedded in the FIPS ring. -/
private theorem Xofs.uniformPrefixes_expandMask_coefficients (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b) (seed : FixedBytes 64) :
    (base.uniformPrefixes a b).map (fun H (p : Fin 814 × Fin s.params.ℓ) (j : Fin 256) =>
      (((H.expandMask s seed.toList (signingAttemptCounter s.params 0 p.1)).get p.2).get j)) =
      (PMF.uniformOfFintype (Fin 814 × Fin s.params.ℓ → Fin 256 → MaskCoefficient s)).map
        fun rows p j => ((rows p j).val : ZMod 8380417) := by
  let cast (r : ScheduledRow s → Fin 256 → MaskCoefficient s) (p : ScheduledRow s) := ringRow (r p)
  have eq := congrArg (PMF.map cast) (uniform_scheduledMasks s seed)
  rw [PMF.map_comp] at eq
  rw [← base.uniform_sampleWithMasks s ha hb, PMF.map_bind]
  refine Eq.trans ?_ eq
  simp only [PMF.map, Function.comp_def]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (MaskTable s)))
  funext masks
  apply PMF.bind_eq_pure_of_forall_mem_support
  intro H hH
  congr 1
  funext p j
  exact Xofs.expandMask_of_mem_sampleWithMasks hH seed _ p.2 j

private abbrev Coefficients (s : Level) := Fin s.params.ℓ → Fin 256 → MaskCoefficient s

private theorem maskLaw_coefficients (s : Level) :
    (PMF.uniformOfFintype (Coefficients s)).map (fun r i => ringRow (r i)) =
      signingMaskLaw s.params (by cases s <;> decide) := by
  classical
  let pack (r : Coefficients s) : ↥(maskSet s.params) :=
    ⟨fun i => ringRow (r i), (mem_intervalVectors s.params).2 fun i j => by
      have hj := Finset.mem_Ioc.mp (r i j).property
      exact ⟨(r i j).val, ⟨by lia, hj.2⟩, rfl⟩⟩
  have inj : Function.Injective pack := by
    intro r t h
    funext i j
    apply Subtype.ext
    have eq := congrArg (fun v : ↥(maskSet s.params) => (v.val i j).valMinAbs) h
    simpa only [pack, centered] using eq
  have onto : Function.Surjective pack := by
    intro y
    have mem := (mem_intervalVectors s.params).mp y.property
    choose x hx eq using mem
    let r : Coefficients s := fun i j => ⟨x i j, Finset.mem_Ioc.mpr ⟨by have := (hx i j).1; lia,
      (hx i j).2⟩⟩
    exact ⟨r, Subtype.ext (funext fun i => funext fun j => eq i j)⟩
  let e := Equiv.ofBijective pack ⟨inj, onto⟩
  let _ : Nonempty ↥(maskSet s.params) := Finset.nonempty_coe_sort.mpr
    (mask_nonempty s.params (by cases s <;> decide))
  have law := PMF.uniformOfFintype_finset_map_val (maskSet s.params)
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.map_comp] at law
  exact law

private theorem iid_coefficients (s : Level) (k : ℕ) :
    (PMF.uniformOfFintype (Fin k × Fin s.params.ℓ → Fin 256 → MaskCoefficient s)).map
        (fun r i j => ringRow (r (i, j))) =
      PMF.iid (signingMaskLaw s.params (by cases s <;> decide)) k := by
  rw [← maskLaw_coefficients, PMF.iid_map, PMF.iid_uniformOfFintype,
    ← PMF.uniformOfFintype_map_equiv
      (Equiv.curry (Fin k) (Fin s.params.ℓ) (Fin 256 → MaskCoefficient s)), PMF.map_comp]
  rfl

/-- All 814 scheduled Algorithm 34 masks have the joint IID law used by the signing simulator. -/
theorem Xofs.uniformPrefixes_expandMask_schedule (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b) (seed : FixedBytes 64) :
    (base.uniformPrefixes a b).map (fun H (t : Fin 814) =>
      ringVectorCoeffs (H.expandMask s seed.toList (signingAttemptCounter s.params 0 t))) =
      PMF.iid (signingMaskLaw s.params (by cases s <;> decide)) 814 := by
  have law := congrArg (PMF.map Function.curry)
    (base.uniformPrefixes_expandMask_coefficients s ha hb seed)
  rw [← iid_coefficients]
  simp only [PMF.map_comp] at law
  convert law using 1 <;> apply congrArg (fun g => PMF.map g _) <;>
    funext x i k j <;> rfl

/-- Reading the 814 scheduled mask polynomials from a uniform two-byte-indexed XOF row table
produces i.i.d. uniform masks in the signing mask distribution. -/
theorem iid_maskFromRow (s : Level) :
    (PMF.uniformOfFintype (FixedBytes 2 → FixedBytes (maskPolyBytes s))).map
        (fun row (i : Fin 814) =>
          ringVectorCoeffs (maskFromRow s row (signingAttemptCounter s.params 0 i))) =
      PMF.iid (signingMaskLaw s.params (by cases s <;> decide)) 814 := by
  let tag : ScheduledRow s ↪ FixedBytes 2 := ⟨fun p => nonceSuffix (schedule s p), by
    intro p q h
    apply schedule_injective s 0
    simp only [maskAddress, nonceInput, h]⟩
  let read (r : ScheduledRow s → FixedBytes (maskPolyBytes s)) (i : Fin 814) (k : Fin s.params.ℓ) :=
    ((unpackSigned 1 (width s) s.params.γ₁ (r (i, k)).toList).get 0).get
  have law := congrArg (PMF.map read)
    (PMF.uniformOfFintype_pi_map_comp_embedding (α := FixedBytes (maskPolyBytes s)) tag)
  let enc := Equiv.piCongrRight (fun _ : ScheduledRow s => packedEquiv s)
  rw [PMF.map_comp, ← PMF.uniformOfFintype_map_equiv enc, PMF.map_comp] at law
  rw [← iid_coefficients]
  convert law using 1
  · apply congrArg (fun g => PMF.map g _)
    funext r i k j
    simp only [maskFromRow, expandMaskFrom, ringVectorCoeffs, Vector.get_ofFn, Function.comp_apply,
      read, width, schedule, tag, Function.Embedding.coeFn_mk]
  · apply congrArg (fun g => PMF.map g _)
    funext r i k j
    exact (unpack_row s (r (i, k)) j).symm

private theorem cappedReplay {X Y : Type} (p : PMF X) (μ : PMF Y) (mask : X → ℕ → Y)
    (finish : Y → Option (Option (List Byte))) (stride k : ℕ)
    (law : p.map (fun x (i : Fin k) => mask x (0 + i.val * stride)) = PMF.iid μ k) :
    p.map (fun x => firstAccepted stride (fun nonce => finish (mask x nonce)) k 0) =
      ((List.range k).findSomeM? fun _ => μ.map (terminalReply ∘ finish)).map Option.join := by
  let run (u : Fin k → Y) := Fin.findSome? fun i => terminalReply (finish (u i))
  have schedule := congrArg (PMF.map run) law
  rw [PMF.map_comp] at schedule
  have online (xs : List ℕ) (len : xs.length = k) : (PMF.iid μ k).map run =
      xs.findSomeM? (fun _ => μ.map (terminalReply ∘ finish)) := by
    subst k
    exact PMF.iid_map_findSome μ (terminalReply ∘ finish) xs
  rw [← online _ (List.length_range (n := k)), ← schedule, PMF.map_comp]
  apply congrArg (fun f => PMF.map f p)
  funext x
  exact firstAccepted_eq_terminal stride _ k 0

/-- Drawing independent full-width bytes per nonce and drawing a fresh mask from the signing
simulator's coefficient box give the same native 814-attempt signing result. The ambient
commitment and challenge XOF is fixed throughout. Sparse expansion failure stops signing,
whereas a rejected response advances to the next mask. -/
theorem Xofs.privateMaskRetries_eq_iid (H : Xofs) (s : Level) (sk : PrivateKey s)
    (A : PublicMatrix s) (μ : List Bool) :
    let finish := fun (y : Fin s.params.ℓ → Poly) =>
      let w := moduleSISMap A y
      let d := H.commitmentDigest s (highBitsVec s.params w) μ
      finishSigningAttempt s sk y w d (H.sampleInBall s d)
    (PMF.uniformOfFintype (FixedBytes 2 → FixedBytes (maskPolyBytes s))).map (fun row =>
      H.signingRetries s sk A μ (maskFromRow s row)) =
      ((List.range 814).findSomeM? fun _ =>
        (signingMaskLaw s.params (by cases s <;> decide)).map fun y =>
          (finish y).elim (some none) (Option.map some)).map Option.join := by
  intro finish
  have native : H.attemptWithMask s sk A μ = finish := by
    funext y
    simp only [Xofs.attemptWithMask, AttemptCommitment.ofMask, tabulateRingVector_eq, finish]
  have stop : (fun y => (finish y).elim (some none) (Option.map some)) =
      terminalReply ∘ finish := by
    funext y
    simp only [Function.comp_apply]
    cases finish y <;> rfl
  simp only [Xofs.signingRetries, native, stop]
  exact cappedReplay _ (signingMaskLaw s.params (by cases s <;> decide))
    (fun row nonce => ringVectorCoeffs (maskFromRow s row nonce)) finish s.params.ℓ 814
    (iid_maskFromRow s)

namespace QuantumSigningForger

/-- The quantum signing trial with the independent uniform lattice matrix and a pre-sampled
table of signed masking coefficients has the joint law of the matrix-prefix hybrid
averaged over the finite random XOFs. The equality retains both raw oracles, the public key,
final forgery, whole signing
log and setup failures, so it applies in particular to the fresh-digest event. -/
theorem uniform_matrix_masks_trial (C : QuantumSigningForger) (base : Xofs) (s : Level)
    {a b : ℕ} (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b) :
    ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
      (PMF.uniformOfFintype (MaskTable s)).bind fun masks =>
        (base.sampleWithMasks ha hb masks).bind fun H => C.programmedTrial s H A) =
      (base.uniformPrefixes a b).bind (C.matrixTrial s) := by
  simp only [← PMF.bind_bind (PMF.uniformOfFintype (MaskTable s)),
    Xofs.uniform_sampleWithMasks]
  rw [PMF.bind_comm]
  simp only [C.uniform_programmedTrial]

/-- The original finite random-XOF strong-forgery game equals the execution with independent
uniform matrix and signed-mask table. The sampled widths cover the literal mask addresses and
the full 894-byte matrix prefixes, in addition to the shorter Algorithm 34 reads. -/
theorem randomPrefixGame_eq_matrix_masks (C : QuantumSigningForger) (base : Xofs) (s : Level)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 894 ≤ b) :
    let hm : maskPolyBytes s ≤ b := (show maskPolyBytes s ≤ 894 by cases s <;> decide).trans hb
    C.randomPrefixGame s base a b =
      (PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
        (PMF.uniformOfFintype (MaskTable s)).bind fun masks =>
          (base.sampleWithMasks ha hm masks).bind fun H =>
            (C.programmedTrial s H A).map (·.any SignedMatrixTrial.wins) := by
  intro hm
  rw [C.randomPrefixGame_eq_matrixTrial s base (by lia) hb, ← PMF.map_bind,
    ← C.uniform_matrix_masks_trial base s ha hm]
  simp only [PMF.map_bind]

/-- The SHAKE128 matrix installation leaves the entire SHAKE256 stream from the supplied mask
table intact. Thus even a seed selected after earlier coherent queries or signing replies reads
the very same coefficients at every counter of a surviving trial. -/
theorem expandMask_of_mem_programmedTrial (C : QuantumSigningForger) {s : Level}
    {a b : ℕ} {base H : Xofs} {ha : 528 ≤ a} {hb : maskPolyBytes s ≤ b} {masks : MaskTable s}
    (hH : H ∈ (base.sampleWithMasks ha hb masks).support) {A : PublicMatrix s}
    {u : SignedMatrixTrial s} (hu : some u ∈ (C.programmedTrial s H A).support)
    (seed : FixedBytes 64) (κ : ℕ) (i : Fin s.params.ℓ) (j : Fin 256) :
    (((u.xofs.expandMask s seed.toList κ).get i).get j) =
      ((masks (maskAddress seed (κ + i.val)) j).val : ZMod 8380417) := by
  simpa only [Xofs.expandMask, (C.verified_programmedTrial hu).1] using
    Xofs.expandMask_of_mem_sampleWithMasks hH seed κ i j

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
