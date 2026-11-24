/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
-- Reads private `prob`, `meanGap_of_agree`, `mean_query_sqrt_le`, and `expansionContinuation`.
import all CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
import CslibFrontier.Probability.PMF.Uniform

/-!
# Sampling a commitment digest after native signing and coherent SHAKE queries

The mask fixes the packed commitment suffix before the forger chooses a message. A second
independent digest table supplies all words with this suffix. Conditional on the earlier
interaction using the original table, the digest at the subsequently chosen message representative
can be redrawn exactly. The cost of separating the earlier interaction depends on the largest
atom of the mask commitment and on the earlier signing and coherent queries. This is an original
one-attempt comparison for the byte signer of [NISTFIPS204], Algorithm 7 and Appendix C, using
the quantum query disturbance argument of [BBBV1997].
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability Cslib.Quantum
open scoped ENNReal

private abbrev Word (s : Level) := BitString s.commitmentInputBits
private abbrev Digest (s : Level) := BitString (8 * digestBytes s)
private abbrev Register (s : Level) := Word s → Digest s
private abbrev Mask (s : Level) := Fin s.params.ℓ → Poly

-- Clear the representative, retaining the complete packed commitment in its original position.
private def suffixKey (s : Level) (i : Word s) : Word s :=
  BitString.ofList _ (List.ofFn (0 : BitString 512) ++ (List.ofFn i).drop 512)

private theorem suffixKey_addr (s : Level) (A : PublicMatrix s) (m : BitString 512) (y : Mask s) :
    suffixKey s (maskCommitmentAddress s A m y) = maskCommitmentAddress s A 0 y := by
  unfold suffixKey maskCommitmentAddress
  rw [BitString.ofFn_ofList (commitmentInput_length s _ List.length_ofFn)]
  unfold commitmentInput
  have drop (l : List Bool) : (List.ofFn m ++ l).drop 512 = l := by
    simpa only [List.length_ofFn] using List.drop_left (l₁ := List.ofFn m) (l₂ := l)
  simp only [drop]

private def replaceSuffix (s : Level) (A : PublicMatrix s) (y : Mask s)
    (D E : Register s) (i : Word s) : Digest s :=
  if suffixKey s i = maskCommitmentAddress s A 0 y then E i else D i

private theorem prob_read_diff {R : Type} (s : Level) (A : PublicMatrix s) (D E : Register s)
    (run : DigestReads s R) {K : ℕ} (bounded : run.IsQueryBounded K) :
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | OracleComp.evalPure (replaceSuffix s A y D E) run ≠ OracleComp.evalPure D run} ≤
        K * commitmentGuessProbability s.params (by cases s <;> decide) A := by
  let μ := signingMaskLaw s.params (by cases s <;> decide)
  apply le_trans _ (prob_mask_trace_changes s A 0 D run bounded (suffixKey s)
    (fun y T => replaceSuffix s A y D T) (fun y T i ne => by simp [replaceSuffix, ne]))
  exact μ.toOuterMeasure.mono (fun _ different => ⟨E, different⟩)

private theorem suffix_query_event (s : Level) (H : Xofs) (A : PublicMatrix s)
    (D E : Register s) (a b : ℕ) (x : BitString (a + 2)) :
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | (H.withDigestRegister s (replaceSuffix s A y D E)).queryTable a b x ≠
        (H.withDigestRegister s D).queryTable a b x} ≤
      commitmentGuessProbability s.params (by cases s <;> decide) A := by
  let μ := signingMaskLaw s.params (by cases s <;> decide)
  refine (μ.toOuterMeasure.mono ?_).trans (maskCommitmentAddress_singleton_le s A 0
    (suffixKey s (Xofs.digestLookup s x)))
  intro y different
  by_contra miss
  apply different
  rw [queryTable_register, queryTable_register]
  simp [replaceSuffix, Ne.symm miss]

-- On independent uniform input tables, exchanging the selected suffix in both directions
-- is an involution. Its first projection therefore has the original uniform law.
private theorem uniform_replaceSuffix {α : Type} (s : Level) (A : PublicMatrix s) (y : Mask s)
    (score : Register s → PMF α) :
    ((PMF.uniformOfFintype (Register s)).bind fun D =>
      (PMF.uniformOfFintype (Register s)).bind fun E => score (replaceSuffix s A y D E)) =
        (PMF.uniformOfFintype (Register s)).bind score := by
  let swap (p : Register s × Register s) :=
    (replaceSuffix s A y p.1 p.2, replaceSuffix s A y p.2 p.1)
  have inv : Function.Involutive swap := by
    rintro ⟨D, E⟩
    apply Prod.ext <;> funext i <;> by_cases h : suffixKey s i = maskCommitmentAddress s A 0 y <;>
      simp [swap, replaceSuffix, h]
  exact PMF.uniformOfFintype_bind_bind_fst_equiv inv.toPerm score

private theorem uniform_write_selected {α : Type} (s : Level) (A : PublicMatrix s) (y : Mask s)
    (m : BitString 512) (D : Register s) (score : Register s → PMF α) :
    ((PMF.uniformOfFintype (Register s)).bind fun E =>
      (PMF.uniformOfFintype (Digest s)).bind fun v =>
        score (Function.update (replaceSuffix s A y D E) (maskCommitmentAddress s A m y) v)) =
      (PMF.uniformOfFintype (Register s)).bind fun E => score (replaceSuffix s A y D E) := by
  let i := maskCommitmentAddress s A m y
  have commute E v : Function.update (replaceSuffix s A y D E) i v =
      replaceSuffix s A y D (Function.update E i v) := by
    funext x
    by_cases hx : x = i
    · subst x
      simp [replaceSuffix, i, suffixKey_addr]
    · simp [replaceSuffix, Function.update_of_ne hx]
  have law := PMF.uniformOfFintype_bind_bind_adaptiveUpdate (κ := Digest s)
    (fun _ => i) (fun _ _ => rfl) (fun E => score (replaceSuffix s A y D E))
  simpa only [← commute] using law

namespace QuantumSigningForger

private abbrev Row (s : Level) := FixedBytes 2 → FixedBytes (maskPolyBytes s)
private inductive Preparation where
  | answered (reply : Option (List Byte))
  | ready (representative : BitString 512)

private def Preparation.point : Preparation → BitString 512
  | .answered _ => 0
  | .ready m => m

private def Preparation.isReady : Preparation → Bool
  | .answered _ => false
  | .ready _ => true

private abbrev Probe (s : Level) (α : Type) := α → List (Row s) → DigestReads s Preparation
private abbrev After (s : Level) (C : QuantumSigningForger) (α : Type) :=
  α → List Forgery → List (Row s) → Preparation → Test C

private noncomputable def before {C : QuantumSigningForger} {α : Type} (s : Level) (H : Xofs)
    (D : Register s) (keys : KeyPair) (prog : C.Program α)
    (probe : Probe s α) (after : After s C α) (dev : C.Device) (log : List Forgery)
    (rows : List (Row s)) : Game :=
  let G := H.withDigestRegister s D
  scored prog G (fun row q => G.signWithExpansionRow s keys.secretKey q row)
    (fun x l t => after x l t (OracleComp.evalPure D (probe x t))) dev log rows

private theorem before_gap {C : QuantumSigningForger} {α : Type} (s : Level) (H : Xofs)
    (D E : Register s) (A : PublicMatrix s) (keys : KeyPair) (prog : C.Program α)
    (probe : Probe s α) (after : Mask s → After s C α)
    (dev : C.Device) (log : List Forgery) (rows : List (Row s)) {qH qS : ℕ}
    (hash : OracleComp.IsCostBounded (fun x => (isXofQuery x).toNat) prog qH)
    (calls : OracleComp.IsCostBounded (fun x => (isSigningCall x).toNat) prog qS)
    {K : ℕ} (pre : ∀ x t, (probe x t).IsQueryBounded K) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    PMF.meanAbsDiffAt μ true
      (fun y => before s H (replaceSuffix s A y D E) keys prog probe (after y) dev log rows)
      (fun y => before s H D keys prog probe (after y) dev log rows) ≤
        4 * qH * √δ + (815 * qS + K) * δ := by
  classical
  intro μ δ
  let base := H.withDigestRegister s D
  let new y := H.withDigestRegister s (replaceSuffix s A y D E)
  have finite : commitmentGuessProbability s.params (by cases s <;> decide) A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)
  apply le_trans (scored_meanGap_le (C := C) μ base new
    (fun row q => base.signWithExpansionRow s keys.secretKey q row)
    (fun y row q => (new y).signWithExpansionRow s keys.secretKey q row)
    (fun y x l t => after y x l t (OracleComp.evalPure D (probe x t)))
    (fun y x l t => after y x l t (OracleComp.evalPure (replaceSuffix s A y D E) (probe x t)))
    (Q := 4 * √δ) (S := 815 * δ) (T := K * δ) (by positivity) (by positivity)
    ?_ ?_ ?_ hash calls dev log rows)
  · ring_nf
    rfl
  · intro d M
    apply mean_query_gap_of_root μ base new d M ENNReal.toReal_nonneg
    exact mean_query_sqrt_le μ base new d M true fun x =>
      ENNReal.toReal_mono finite (suffix_query_event s H A D E _ _ x)
  · intro row q
    let run := H.signDigestQueriesWithMask s keys.secretKey q (fun _ _ => row) (maskFromRow s)
    have h := prob_read_diff s A D E run (H.signDigestQueriesWithMask_bounded ..)
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) finite) h
    simpa only [run, Xofs.evalPure_signDigestQueriesWithMask, Xofs.signWithExpansionRow,
      ENNReal.toReal_mul, Nat.cast_ofNat, ENNReal.toReal_ofNat] using hb
  · intro x l t d
    let run := probe x t
    let bad := {y | OracleComp.evalPure (replaceSuffix s A y D E) run ≠ OracleComp.evalPure D run}
    refine (meanGap_of_agree μ _ _ bad ?_).trans ?_
    · intro y hy
      rw [show OracleComp.evalPure (replaceSuffix s A y D E) (probe x t) =
        OracleComp.evalPure D (probe x t) from not_ne_iff.mp hy]
    · have h := prob_read_diff s A D E run (pre x t)
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) finite) h

private abbrev ReplyTest (s : Level) (C : QuantumSigningForger) (α : Type) :=
  Mask s → Register s → After s C α

private noncomputable def stage {C : QuantumSigningForger} {α : Type} (s : Level) (H : Xofs)
    (P D : Register s) (A : PublicMatrix s) (keys : KeyPair) (prog : C.Program α)
    (probe : Probe s α) (score : ReplyTest s C α)
    (dev : C.Device) (log : List Forgery) (rows : List (Row s)) (write : Bool)
    (y : Mask s) (v : Digest s) :=
  before s H P keys prog probe (fun x l t m =>
    let table := if write && m.isReady then
      Function.update D (maskCommitmentAddress s A m.point y) v else D
    score y table x l t m) dev log rows

private theorem detached_eq {C : QuantumSigningForger} {α : Type} (s : Level) (H : Xofs)
    (D : Register s) (A : PublicMatrix s) (keys : KeyPair) (prog : C.Program α)
    (probe : Probe s α) (score : ReplyTest s C α)
    (dev : C.Device) (log : List Forgery) (rows : List (Row s)) (y : Mask s) :
    let run w E := stage s H D (replaceSuffix s A y D E) A keys prog probe score
      dev log rows w y
    ((PMF.uniformOfFintype (Register s)).bind fun E =>
      (PMF.uniformOfFintype (Digest s)).bind (run true E)) =
      (PMF.uniformOfFintype (Register s)).bind fun E => run false E 0 := by
  intro run
  change ((PMF.uniformOfFintype (Register s)).bind fun E =>
    (PMF.uniformOfFintype (Digest s)).bind fun v => run true E v) = _
  dsimp only [run, stage, before, scored, Bool.false_and, Bool.true_and, Bool.false_eq_true,
    ↓reduceIte]
  generalize (OracleComp.interpret
    (m := StateT ((C.Device × List Forgery) × List (Row s)) PMF) _ prog).run _ = execution
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Digest s)) execution,
    PMF.bind_comm (PMF.uniformOfFintype (Register s)) execution]
  apply congrArg (PMF.bind execution ·)
  funext ⟨x, ⟨d, l⟩, t⟩
  dsimp only
  let prep := OracleComp.evalPure D (probe x t)
  cases enabled : prep.isReady with
  | false => simp only [← show prep = OracleComp.evalPure D (probe x t) from rfl,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
  | true =>
    simp only [← show prep = OracleComp.evalPure D (probe x t) from rfl,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte]
    exact uniform_write_selected s A y prep.point D (fun T => observe (score y T x l t prep) d)

private theorem abs_common_bind {ι : Type} [Finite ι] (p : PMF ι) (a b : ι → Game)
    {L : ℝ} (bounds : ∀ i, |prob (a i) - prob (b i)| ≤ L) :
    |prob (p.bind a) - prob (p.bind b)| ≤ L := by
  let _ := Fintype.ofFinite ι
  exact (PMF.abs_bind_sub_le_meanAbsDiffAt p true a b).trans (PMF.sum_mul_le p _ _ bounds)

private theorem refresh_after_prefix {C : QuantumSigningForger} {α : Type}
    (s : Level) (H : Xofs) (A : PublicMatrix s) (keys : KeyPair)
    (prog : C.Program α) (probe : Probe s α) (score : ReplyTest s C α)
    (dev : C.Device) (log : List Forgery) (rows : List (Row s)) {qH qS : ℕ}
    (hash : OracleComp.IsCostBounded (fun x => (isXofQuery x).toNat) prog qH)
    (calls : OracleComp.IsCostBounded (fun x => (isSigningCall x).toNat) prog qS)
    {K : ℕ} (pre : ∀ x t, (probe x t).IsQueryBounded K) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let U := PMF.uniformOfFintype (Register s)
    let V := PMF.uniformOfFintype (Digest s)
    let go P T w := stage s H P T A keys prog probe score dev log rows w
    let original w := μ.bind fun y => U.bind fun T => V.bind (go T T w y)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |prob (original true) - prob (original false)| ≤ 2 * (4 * qH * √δ + (815 * qS + K) * δ) := by
  classical
  intro μ U V go original δ
  let expanded (detached write : Bool) := U.bind fun B => U.bind fun E => V.bind fun v =>
    μ.bind fun y => let T := replaceSuffix s A y B E
      go (if detached then B else T) T write y v
  have swapSamples (f : Register s → Register s → Digest s → Mask s → Game) :
      (U.bind fun B => U.bind fun E => V.bind fun v => μ.bind (f B E v)) =
        μ.bind fun y => U.bind fun B => U.bind fun E => V.bind fun v => f B E v y := by
    simp_rw [PMF.bind_comm V μ, PMF.bind_comm U μ]
  have original_eq (write) : original write = expanded false write := by
    dsimp only [original, expanded, Bool.false_eq_true, ↓reduceIte]
    rw [swapSamples]
    apply congrArg (PMF.bind μ ·)
    funext y
    exact (uniform_replaceSuffix s A y (fun T => V.bind (go T T write y))).symm
  have off : expanded true true = expanded true false := by
    dsimp only [expanded, ↓reduceIte]
    rw [swapSamples, swapSamples]
    apply congrArg (PMF.bind μ ·)
    funext y
    apply congrArg (PMF.bind U ·)
    funext B
    refine (detached_eq s H B A keys prog probe score dev log rows y).trans ?_
    apply congrArg (PMF.bind U ·)
    funext E
    simp [go, stage, PMF.bind_const]
  have bound (write) :
      |prob (expanded false write) - prob (expanded true write)| ≤
        4 * qH * √δ + (815 * qS + K) * δ := by
    apply abs_common_bind U
    intro B
    apply abs_common_bind U
    intro E
    apply abs_common_bind V
    intro v
    apply (PMF.abs_bind_sub_le_meanAbsDiffAt μ true _ _).trans
    exact before_gap s H B E A keys prog probe (fun y x l t m =>
      let T := replaceSuffix s A y B E
      let final := if write && m.isReady then
        Function.update T (maskCommitmentAddress s A m.point y) v else T
      score y final x l t m) dev log rows hash calls pre
  rw [original_eq, original_eq]
  have h := abs_sub_le (prob (expanded false true)) (prob (expanded true true))
    (prob (expanded false false))
  have right := bound false
  rw [← off, abs_sub_comm] at right
  simpa only [two_mul] using h.trans (add_le_add (bound true) right)

private inductive Boundary (C : QuantumSigningForger) where
  | finished (f : Forgery)
  | signing (q : SigningQuery) (next : Option (List Byte) → C.Program Forgery)

private def resumeProgram {C : QuantumSigningForger} : Boundary C → C.Program Forgery
  | .finished f => .pure f
  | .signing q k => .liftBind (.inr (.inr q)) k

-- Stop immediately before the indexed signing call. Private coins, measurements, coherent
-- queries and earlier complete signing requests are still executed by the native controller.
private def cut {C : QuantumSigningForger} : C.Program Forgery → ℕ → C.Program (Boundary C)
  | .pure f, _ => .pure (.finished f)
  | .liftBind (.inl n) k, j => .liftBind (.inl n) fun r => cut (C := C) (k r) j
  | .liftBind (.inr (.inl cmd)) k, j =>
    .liftBind (.inr (.inl cmd)) fun r => cut (C := C) (k r) j
  | .liftBind (.inr (.inr q)) k, 0 => .pure (.signing q k)
  | .liftBind (.inr (.inr q)) k, j + 1 =>
    .liftBind (.inr (.inr q)) fun r => cut (C := C) (k r) j

private theorem cut_cost {C : QuantumSigningForger} {prog : C.Program Forgery} {cost} {n : ℕ}
    (h : OracleComp.IsCostBounded cost prog n) (j : ℕ) :
    OracleComp.IsCostBounded cost (cut (C := C) prog j) n := by
  induction h generalizing j with
  | pure f n => exact .pure _ _
  | liftBind cmd k n _ ih =>
    rcases cmd with coin | cmd | q
    · exact .liftBind _ _ n fun r => ih r j
    · exact .liftBind _ _ n fun r => ih r j
    · cases j with
      | zero => exact .pure _ _
      | succ j => exact .liftBind _ _ n fun r => ih r j

private theorem cut_signing {C : QuantumSigningForger} (prog : C.Program Forgery) (j : ℕ) :
    OracleComp.IsCostBounded (fun x => (isSigningCall x).toNat) (cut (C := C) prog j) j := by
  induction prog generalizing j with
  | pure f => exact .pure _ _
  | liftBind cmd k ih =>
    rcases cmd with coin | cmd | q
    · exact .liftBind _ _ j fun r => ih r j
    · exact .liftBind _ _ j fun r => ih r j
    · cases j with
      | zero => exact .pure _ _
      | succ j => exact .liftBind _ _ j fun r => ih r j

private def probePrefix {C : QuantumSigningForger} (s : Level) (H : Xofs) (tr : List Byte)
    (scan : List.Vector Bool 512 → DigestReads s (Option (Option (List Byte)))) :
    Boundary C → DigestReads s Preparation
  | .finished _ => pure (.answered none)
  | .signing q _ => do
    if 255 < q.context.length then return .answered none
    let m ← representativeQuery H s tr (formatMessage q.message q.context)
    let r ← scan m
    return match r with
      | some reply => .answered reply
      | none => .ready (BitString.ofList 512 m.toList)

private theorem probePrefix_bounded {C : QuantumSigningForger} (s : Level) (H : Xofs) (tr)
    {scan} {n : ℕ} (bound : ∀ m, (scan m).IsQueryBounded n) (x : Boundary C) :
    (probePrefix s H tr scan x).IsQueryBounded (1 + n) := by
  cases x with
  | finished => exact .pure _ _
  | signing q k =>
    simp only [probePrefix]
    split
    · exact .pure _ _
    · exact OracleComp.IsCostBounded.bind (n := 1) (m := n) (rep_bounded ..) (fun m =>
        OracleComp.IsCostBounded.bind (n := n) (m := 0) (bound m) (fun _ => .pure _ _))

private def preparedPrefix {C : QuantumSigningForger} (G : Xofs) (tr : List Byte)
    (scan : List Bool → Option (Option (List Byte))) : Boundary C → Preparation
  | .finished _ => .answered none
  | .signing q _ =>
    if 255 < q.context.length then .answered none else
      let m := G.representativeFromTr tr (formatMessage q.message q.context)
      match scan m with
      | some reply => .answered reply
      | none => .ready (BitString.ofList 512 m)

private theorem eval_probePrefix {C : QuantumSigningForger} (s : Level) (H : Xofs)
    (tr : List Byte) (D : Register s) (scan native)
    (eq : ∀ m, OracleComp.evalPure D (scan m) = native m.toList) (x : Boundary C) :
    OracleComp.evalPure D (probePrefix s H tr scan x) =
      preparedPrefix (H.withDigestRegister s D) tr native x := by
  cases x with
  | finished => rfl
  | signing q _ =>
    by_cases h : 255 < q.context.length <;>
      simp [probePrefix, preparedPrefix, h, OracleComp.evalPure_bind, OracleComp.evalPure_pure,
        eq, eval_rep]

private def probeTrials {C : QuantumSigningForger} (s : Level) (H : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (j : Fin 814) : Probe s (Boundary C) := fun x rows =>
  probePrefix s H sk.tr (fun m => terminalDigestQueries H s sk A m
    (maskFromRow s (rows.headD 0)) j 0) x

private theorem probeTrials_bounded {C : QuantumSigningForger} (s : Level) (H : Xofs) (A)
    (sk : PrivateKey s) (j : Fin 814) (x : Boundary C) (rows) :
    (probeTrials s H A sk j x rows).IsQueryBounded (1 + j.val) :=
  probePrefix_bounded s H sk.tr (fun _ => terminalDigestQueries_bounded ..) x

-- Decode the nonce row into a vector once before the signing attempt looks up its coefficients.
private def rowAttempt (s : Level) (G : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (m : List Bool) (row : Row s) (nonce : ℕ) : Option (Option (List Byte)) :=
  G.attemptWithMask s sk A m (ringVectorCoeffs (maskFromRow s row nonce))

-- On the public game side the earlier attempts read their digests through the actual XOF.
private def nativePreparation {C : QuantumSigningForger} (s : Level) (G : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (j : Fin 814) : Boundary C → List (Row s) → Preparation := fun x rows =>
  preparedPrefix G sk.tr (fun m => (List.finRange j.val).findSome? fun i => terminalReply
    (rowAttempt s G A sk m (rows.headD 0) (i.val * s.params.ℓ))) x

private theorem eval_probe {C : QuantumSigningForger} (s : Level) (H : Xofs) (D : Register s)
    (A sk j) (x : Boundary C) (rows) :
    OracleComp.evalPure D (probeTrials s H A sk j x rows) =
      nativePreparation s (H.withDigestRegister s D) A sk j x rows := by
  apply eval_probePrefix
  intro m
  simpa only [rowAttempt, Nat.zero_add] using
    eval_terminalDigestQueries H s D sk A m (maskFromRow s (rows.headD 0)) j 0

-- Everything after the cut, including all remaining retries, sees the table selected at the
-- distinguished attempt. The FIPS error and successful signing log are handled before resuming.
private def afterTrial {C : QuantumSigningForger} (s : Level) (G : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (j : Fin 814) (y : Mask s) (x : Boundary C) (prep : Preparation)
    (log : List Forgery) (rows : List (Row s)) : C.Program Forgery × List Forgery × List (Row s) :=
  match x with
  | .finished f => (.pure f, log, rows)
  | .signing q k =>
    let reply := match prep with
      | .answered r => r
      | .ready m => do
        let result ← G.attemptWithMask s sk A (List.ofFn m) y
        match result with
        | some sig => some sig
        | none =>
          firstAccepted s.params.ℓ (rowAttempt s G A sk (List.ofFn m) (rows.headD 0))
            (813 - j.val) ((j.val + 1) * s.params.ℓ)
    (k reply, q.logReply reply log, rows.tail)

private noncomputable def nativeStage (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (D : Register s) (A : PublicMatrix s) (sk : PrivateKey s) (keys : KeyPair) (index : ℕ)
    (j : Fin 814) (rows : List (Row s)) (write : Bool) (y : Mask s) (v : Digest s) : Game := do
  let G := H.withDigestRegister s D
  let prog := cut (C := C) (C.program keys.publicKey) index
  let (x, (dev, log), rest) ← (OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall
    (0 : Row s) (fun row => C.signingCommand G
      (fun q => G.signWithExpansionRow s keys.secretKey q row)))
    prog).run ((C.initialDevice, []), rows)
  let prep := nativePreparation s G A sk j x rest
  let table := if write && prep.isReady then
    Function.update D (maskCommitmentAddress s A prep.point y) v else D
  let F := H.withDigestRegister s table
  let (tail, signed, remaining) := afterTrial s F A sk j y x prep log rest
  C.expansionContinuation s F A keys tail dev signed remaining

private noncomputable def trialTest (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (j : Fin 814) :
    ReplyTest s C (Boundary C) := fun y D x log rows prep =>
  let G := H.withDigestRegister s D
  let (prog, signed, remaining) := afterTrial s G A sk j y x prep log rows
  (scored_readout prog G (fun row q => G.signWithExpansionRow s keys.secretKey q row)
    (fun f l _ => POVM.const (SignedMatrixTrial.newDigestWin ⟨G, A, keys.publicKey, f, l⟩))
    signed remaining).choose

private theorem stage_eq_nativeStage (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (D : Register s) (A : PublicMatrix s) (sk : PrivateKey s) (keys : KeyPair) (index : ℕ)
    (j : Fin 814) (rows : List (Row s)) (write : Bool) (y : Mask s) (v : Digest s) :
    stage s H D D A keys (cut (C := C) (C.program keys.publicKey) index) (probeTrials s H A sk j)
      (C.trialTest s H A keys sk j) C.initialDevice [] rows write y v =
      C.nativeStage s H D A sk keys index j rows write y v := by
  simp only [stage, before, scored, nativeStage, PMF.monad_bind_eq_bind]
  apply congrArg (PMF.bind _ ·)
  funext ⟨x, ⟨dev, log⟩, rest⟩
  rw [eval_probe]
  dsimp only [trialTest, expansionContinuation]
  exact ((scored_readout ..).choose_spec dev).symm

/-- Fresh-digest strong-forgery decision in the private mask-expansion experiment with a selected
mask drawn from the FIPS coefficient box. The two zero-based indices select a signing request
and an attempt within its minimum Appendix C cap. Earlier native calls and retries can finish
before the selected attempt. If it is reached, read the shared commitment digest, or install
a fresh digest and keep it on rejection. The continuing signer and verifier see that same stream.
The supplied row tape uses the convention of `expansionContinuation`. -/
noncomputable def commitmentTrialGame (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (index : ℕ) (j : Fin 814) (rows : List (FixedBytes 2 →
      FixedBytes (maskPolyBytes s))) (write : Bool) : Game := do
  let some sk := decodePrivate s keys.secretKey | return false
  let some A := H.expandA s sk.rho | return false
  let y ← signingMaskLaw s.params (by cases s <;> decide)
  let D ← PMF.uniformOfFintype (Register s)
  let v ← PMF.uniformOfFintype (Digest s)
  C.nativeStage s H D A sk keys index j rows write y v

/-- Replacing the shared commitment digest by a fresh uniform digest in a selected native
signing attempt after adaptive signing and coherent SHAKE queries. The bound on fresh-digest
wins charges earlier quantum queries, at most 815 table reads per earlier request, a representative
lookup, and all preceding retries within this request. Each branch resumes the actual forger and
FIPS verifier, including errors, log entries and the residual quantum device. -/
theorem abs_commitmentTrialGame_write_sub_read_le (C : QuantumSigningForger) (s : Level)
    (H : Xofs) (keys : KeyPair) (index : ℕ) (j : Fin 814)
    (rows : List (FixedBytes 2 → FixedBytes (maskPolyBytes s))) {qH : ℕ} (hash : C.XofCallsLe qH) :
    let p write := Game.succProbability (C.commitmentTrialGame s H keys index j rows write)
    |(p true : ℝ) - (p false : ℝ)| ≤ ((do
      let sk ← decodePrivate s keys.secretKey
      let A ← H.expandA s sk.rho
      let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
      return 2 * (4 * qH * √δ + (815 * index + (1 + j.val)) * δ)) : Option ℝ).getD 0 := by
  intro p
  simp only [p, Game.coe_succProbability, commitmentTrialGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  cases hd : decodePrivate s keys.secretKey with
  | none => simp
  | some sk =>
    cases mat : H.expandA s sk.rho with
    | none => simp [mat]
    | some A =>
      let prior := cut (C := C) (C.program keys.publicKey) index
      have h := refresh_after_prefix s H A keys prior (probeTrials s H A sk j)
        (C.trialTest s H A keys sk j) C.initialDevice [] rows (cut_cost (hash _) index)
        (cut_signing _ index) (fun x t => probeTrials_bounded s H A sk j x t)
      have same D w y : stage s H D D A keys prior (probeTrials s H A sk j)
          (C.trialTest s H A keys sk j) C.initialDevice [] rows w y =
          C.nativeStage s H D A sk keys index j rows w y :=
        funext fun v => stage_eq_nativeStage C s H D A sk keys index j rows w y v
      simpa only [same, prob, mat, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def, Option.getD_some, Nat.cast_add, Nat.cast_one] using h

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
