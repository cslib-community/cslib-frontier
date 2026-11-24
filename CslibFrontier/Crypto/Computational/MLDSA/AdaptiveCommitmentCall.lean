/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.ExpansionTrial
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.PMF.Bind
public import CslibFrontier.Crypto.Computational.MLDSA.RejectedCommitmentWrites
import all CslibFrontier.Crypto.Computational.MLDSA.PriorCommitmentRefresh
import all CslibFrontier.Crypto.Computational.MLDSA.DigestSigningQueries
import all CslibFrontier.Crypto.Computational.MLDSA.RejectedCommitmentWrites
import all CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXofMask
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.ExpansionTrial

/-!
# Replacing the commitment reads of an adaptive ML-DSA signing request

Earlier attempts of the selected request read the native digest and later attempts install a
fresh digest on the same stream. On rejection, the next retry sees all earlier writes. At the
end of the request the forger resumes with its actual signing reply and residual quantum state.
We use the 814-attempt option in [NISTFIPS204], Appendix C, Table 3. The comparison of rejected
writes addresses the rejection bias described in [BarbosaEtAl2023], §3.1.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
open Cslib.Probability Cslib.Quantum

private def scanMasks (s : Level) (H : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (ys : List (Mask s)) {C : QuantumSigningForger} : Probe s (Boundary C) := fun x _ =>
  probePrefix s H sk.tr (fun m => ys.findSomeM? (attemptQuery H s sk A m.toList)) x

private theorem scanMasks_bounded {C : QuantumSigningForger} (s : Level) (H : Xofs) (A sk)
    (ys : List (Mask s)) (x : Boundary C) (rows) :
    (scanMasks s H A sk ys x rows).IsQueryBounded (1 + ys.length) := by
  apply probePrefix_bounded
  intro m
  simpa only [Nat.mul_one] using (OracleComp.IsCostBounded.findSomeM?
    (cost := fun _ => 1) (n := 1) (xs := ys) (f := attemptQuery H s sk A m.toList)
    (fun _ _ => .liftBind _ _ 0 fun _ => .pure _ _))

private def scanned {C : QuantumSigningForger} (s : Level) (G : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (ys : List (Mask s)) : Boundary C → Preparation :=
  preparedPrefix G sk.tr fun m =>
    ys.findSome? fun y => terminalReply (G.attemptWithMask s sk A m y)

private theorem eval_scanMasks {C : QuantumSigningForger} (s : Level) (H : Xofs)
    (A sk ys) (D : Register s) (x : Boundary C) (rows) :
    OracleComp.evalPure D (scanMasks s H A sk ys x rows) =
      scanned s (H.withDigestRegister s D) A sk ys x := by
  apply eval_probePrefix
  intro m
  simp only [OracleComp.evalPure_findSomeM?, eval_attemptQuery H s D sk A m.toList m.toList_length]

private def nextPreparation (s : Level) (G : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (y : Mask s) : Preparation → Preparation
  | .answered r => .answered r
  | .ready m => match terminalReply (G.attemptWithMask s sk A (List.ofFn m) y) with
      | some r => .answered r
      | none => .ready m

private theorem scanned_snoc {C : QuantumSigningForger} (s : Level) (G : Xofs) (A sk)
    (ys : List (Mask s)) (y : Mask s) (x : Boundary C) :
    scanned s G A sk (ys ++ [y]) x = nextPreparation s G A sk y (scanned s G A sk ys x) := by
  cases x with
  | finished => rfl
  | signing q k =>
    by_cases h : 255 < q.context.length
    · simp [scanned, preparedPrefix, h, nextPreparation]
    · let m := G.representativeFromTr sk.tr (formatMessage q.message q.context)
      have bits : List.ofFn (BitString.ofList 512 m) = m := BitString.ofFn_ofList
        (by simp only [m, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE,
          G.h256.length_read])
      simp only [scanned, preparedPrefix, h, ↓reduceIte, List.findSome?_append]
      cases ys.findSome? (fun y => terminalReply (G.attemptWithMask s sk A m y)) with
      | some r => rfl
      | none =>
        dsimp only [m] at bits
        simp only [Option.none_or, List.findSome?_cons, List.findSome?_nil,
          nextPreparation, bits]
        cases terminalReply (G.attemptWithMask s sk A
          (G.representativeFromTr sk.tr (formatMessage q.message q.context)) y) <;> rfl

-- Conditional on its initial table and representative, the remaining randomized retry loop
-- induces a measurement on every possible incoming device state.
private theorem retries_readout (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (m : BitString 512)
    (done : Register s → Option (List Byte) → C.Device → Game)
    (test : ∀ T r, ∃ M : Test C, ∀ d, done T r d = observe M d)
    (keep : Bool) (fuel : ℕ) (D : Register s) :
    ∃ M : Test C, ∀ d, runRegisterRetries
        (signingMaskLaw s.params (by cases s <;> decide)) (PMF.uniformOfFintype _)
        (maskCommitmentAddress s A m) (installedAttempt s H A sk m)
        (fun T r => done T r d) keep fuel D = observe M d := by
  classical
  induction fuel generalizing D with
  | zero => exact test D none
  | succ fuel ih =>
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let V := PMF.uniformOfFintype (Digest s)
    have branch (v : Digest s) (y : Mask s) :
        let T := Function.update D (maskCommitmentAddress s A m y) v
        ∃ M : Test C, ∀ d, (match installedAttempt s H A sk m D y v with
          | some r => done T r d
          | none => runRegisterRetries μ V (maskCommitmentAddress s A m)
              (installedAttempt s H A sk m) (fun T r => done T r d) keep fuel
                (if keep then T else D)) = observe M d := by
      intro T
      cases installedAttempt s H A sk m D y v with
      | some r => exact test T r
      | none => exact ih _
    choose M law using branch
    refine ⟨POVM.mixture V (fun v => POVM.mixture μ (M v)), fun d => ?_⟩
    simp only [runRegisterRetries, PMF.monad_bind_eq_bind,
      observe, POVM.measureDensity_mixture]
    apply congrArg (PMF.bind V ·)
    funext v
    apply congrArg (PMF.bind μ ·)
    funext y
    cases h : installedAttempt s H A sk m D y v <;>
      simpa only [h, μ, V, observe] using law v y d

private structure AfterCall (C : QuantumSigningForger) (s : Level) where
  run : Register s → C.Program Forgery → C.Device → List Forgery → List (Row s) → Game
  readout : ∀ T prog l t, ∃ M : Test C, ∀ d, run T prog d l t = observe M d

private noncomputable def nativeAfter (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) : AfterCall C s where
  run T := C.expansionContinuation s (H.withDigestRegister s T) A keys
  readout _ _ _ _ := scored_readout ..

private noncomputable def resumeRetries (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (next : AfterCall C s) (sk : PrivateKey s) (D : Register s) (fuel : ℕ)
    (x : Boundary C) (prep : Preparation) (l : List Forgery) (t : List (Row s))
    (dev : C.Device) : Game :=
  match x with
  | .finished f => next.run D (.pure f) dev l t
  | .signing q k =>
    let done T r := next.run T
      (k r) dev (q.logReply r l) t.tail
    match prep with
    | .answered r => done D r
    | .ready m => runRegisterRetries (signingMaskLaw s.params (by cases s <;> decide))
        (PMF.uniformOfFintype _) (maskCommitmentAddress s A m) (installedAttempt s H A sk m)
        done true fuel D

private theorem resume_readout (C : QuantumSigningForger) (s : Level) (H A)
    (next : AfterCall C s) (sk)
    (D : Register s) (fuel : ℕ) (x : Boundary C) (prep : Preparation) (l : List Forgery)
    (t : List (Row s)) :
    ∃ M : Test C, ∀ d, C.resumeRetries s H A next sk D fuel x prep l t d = observe M d := by
  cases x with
  | finished f => exact next.readout D (.pure f) l t
  | signing q k =>
    cases prep with
    | answered r => exact next.readout D (k r) (q.logReply r l) t.tail
    | ready m =>
      exact retries_readout C s H A sk m (fun T r d => next.run T (k r) d (q.logReply r l) t.tail)
        (fun T r => next.readout T (k r) (q.logReply r l) t.tail) true fuel D

private noncomputable abbrev cutInteraction (C : QuantumSigningForger) (s : Level) (G : Xofs)
    (keys : KeyPair) (i : ℕ) (rows : List (Row s)) :=
  C.prefixInteraction s G keys (C.program keys.publicKey) i C.initialDevice [] rows

private noncomputable def callWindow (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (next : AfterCall C s)
    (i : ℕ) (rows : List (Row s))
    (ys : List (Mask s)) (fuel : ℕ) (D : Register s) : Game :=
  let G := H.withDigestRegister s D
  (C.cutInteraction s G keys i rows).bind fun (x, (d, l), t) =>
    C.resumeRetries s H A next sk D fuel x (scanned s G A sk ys x) l t d

private noncomputable def middleTest (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (next : AfterCall C s) (sk : PrivateKey s)
    (fuel : ℕ) : ReplyTest s C (Boundary C) := fun y T x l t prep =>
  (C.resume_readout s H A next sk T fuel x
    (nextPreparation s (H.withDigestRegister s T) A sk y prep) l t).choose

private theorem stage_run (C : QuantumSigningForger) (s : Level) (H A keys sk)
    (next : AfterCall C s)
    (i : ℕ) (rows : List (Row s)) (ys : List (Mask s)) (fuel : ℕ) (D : Register s)
    (w : Bool) (y : Mask s) (v : Digest s) :
    stage s H D D A keys (cut (C := C) (C.program keys.publicKey) i) (scanMasks s H A sk ys)
        (C.middleTest s H A next sk fuel) C.initialDevice [] rows w y v =
      (C.cutInteraction s (H.withDigestRegister s D) keys i rows).bind fun (x, (dev, l), t) =>
        let p := scanned s (H.withDigestRegister s D) A sk ys x
        let T := if w && p.isReady then Function.update D (maskCommitmentAddress s A p.point y) v
          else D
        C.resumeRetries s H A next sk T fuel x (nextPreparation s (H.withDigestRegister s T)
          A sk y p) l t dev := by
  simp only [stage, before, scored, cutInteraction, prefixInteraction]
  apply congrArg (PMF.bind _ ·)
  funext ⟨x, ⟨d,l⟩, t⟩
  rw [eval_scanMasks]
  exact ((C.resume_readout ..).choose_spec d).symm

private theorem read_stage (C : QuantumSigningForger) (s : Level) (H A keys sk)
    (next : AfterCall C s)
    (i : ℕ) (rows : List (Row s)) (ys : List (Mask s)) (fuel : ℕ) (D : Register s)
    (y : Mask s) (v : Digest s) :
    stage s H D D A keys (cut (C := C) (C.program keys.publicKey) i) (scanMasks s H A sk ys)
        (C.middleTest s H A next sk fuel) C.initialDevice [] rows false y v =
      C.callWindow s H A keys sk next i rows (ys ++ [y]) fuel D := by
  simp only [stage_run, Bool.false_and, Bool.false_eq_true, ↓reduceIte, callWindow, scanned_snoc]

private theorem write_stage (C : QuantumSigningForger) (s : Level) (H A keys sk)
    (next : AfterCall C s)
    (i : ℕ) (rows : List (Row s)) (ys : List (Mask s)) (fuel : ℕ) (D : Register s) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let V := PMF.uniformOfFintype (Digest s)
    (V.bind fun v => μ.bind fun y =>
      stage s H D D A keys (cut (C := C) (C.program keys.publicKey) i) (scanMasks s H A sk ys)
        (C.middleTest s H A next sk fuel) C.initialDevice [] rows true y v) =
      C.callWindow s H A keys sk next i rows ys (fuel + 1) D := by
  intro μ V
  let G := H.withDigestRegister s D
  let past := C.cutInteraction s G keys i rows
  simp only [stage_run, callWindow]
  simp_rw [PMF.bind_comm μ (C.cutInteraction s (H.withDigestRegister s D) keys i rows),
    PMF.bind_comm V (C.cutInteraction s (H.withDigestRegister s D) keys i rows)]
  apply congrArg (PMF.bind past ·)
  funext ⟨x, ⟨d,l⟩, t⟩
  cases x with
  | finished f => simp [scanned, preparedPrefix, Preparation.isReady, resumeRetries]
  | signing q k =>
    cases ready : scanned s G A sk ys (.signing q k) with
    | answered r => simp [Preparation.isReady, nextPreparation, resumeRetries]
    | ready m =>
      simp only [Preparation.isReady, Bool.and_self, ↓reduceIte, Preparation.point,
        nextPreparation, resumeRetries, runRegisterRetries, PMF.monad_bind_eq_bind,
        installedAttempt]
      apply congrArg (PMF.bind V ·)
      funext v
      apply congrArg (PMF.bind μ ·)
      funext y
      cases terminalReply ((H.withDigestRegister s
        (Function.update D (maskCommitmentAddress s A m y) v)).attemptWithMask
          s sk A (List.ofFn m) y) <;> rfl

private theorem window_step (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (next : AfterCall C s)
    (i : ℕ) (rows : List (Row s))
    (ys : List (Mask s)) (fuel : ℕ) {qH : ℕ} (hash : C.XofCallsLe qH) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let U := PMF.uniformOfFintype (Register s)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |prob (U.bind (C.callWindow s H A keys sk next i rows ys (fuel + 1))) -
      prob (μ.bind fun y => U.bind (C.callWindow s H A keys sk next i rows (ys ++ [y]) fuel))| ≤
        2 * (4 * qH * √δ + (815 * i + (1 + ys.length)) * δ) := by
  intro μ U δ
  let V := PMF.uniformOfFintype (Digest s)
  let prog := cut (C := C) (C.program keys.publicKey) i
  let probe := scanMasks s H A sk ys (C := C)
  let test := C.middleTest s H A next sk fuel
  let go D w y v := stage s H D D A keys prog probe test C.initialDevice [] rows w y v
  have h := refresh_after_prefix s H A keys prog probe test C.initialDevice [] rows
    (cut_cost (hash _) i) (cut_signing _ i) (fun x t => scanMasks_bounded s H A sk ys x t)
  change |prob (μ.bind fun y => U.bind fun D => V.bind (go D true y)) -
    prob (μ.bind fun y => U.bind fun D => V.bind (go D false y))| ≤ _ at h
  have w : (μ.bind fun y => U.bind fun D => V.bind (go D true y)) =
      U.bind (C.callWindow s H A keys sk next i rows ys (fuel + 1)) := by
    rw [PMF.bind_comm μ U]
    apply congrArg (PMF.bind U ·)
    funext D
    rw [PMF.bind_comm μ V]
    exact C.write_stage s H A keys sk next i rows ys fuel D
  have r D y : V.bind (go D false y) =
      C.callWindow s H A keys sk next i rows (ys ++ [y]) fuel D := by
    simp only [go, prog, probe, test, read_stage, PMF.bind_const]
  simpa only [w, r, Nat.cast_add, Nat.cast_one] using h

-- Draw a fixed number of native masks without inspecting the digest table. The resulting
-- list is ordered as the signer will inspect it, including masks left unused on early return.
private noncomputable abbrev maskList (s : Level) (k : ℕ) : PMF (List (Mask s)) :=
  (PMF.iid (signingMaskLaw s.params (by cases s <;> decide)) k).map List.ofFn

private theorem all_windows (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (next : AfterCall C s)
    (i : ℕ) (rows : List (Row s))
    (ys : List (Mask s)) (fuel : ℕ) (cap : ys.length + fuel ≤ 814) {qH : ℕ}
    (hash : C.XofCallsLe qH) :
    let U := PMF.uniformOfFintype (Register s)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |prob (U.bind (C.callWindow s H A keys sk next i rows ys fuel)) -
      prob ((maskList s fuel).bind fun zs =>
        U.bind (C.callWindow s H A keys sk next i rows (ys ++ zs) 0))| ≤
      fuel * (2 * (4 * qH * √δ + (815 * i + 814) * δ)) := by
  intro U δ
  let μ := signingMaskLaw s.params (by cases s <;> decide)
  let B := 2 * (4 * qH * √δ + (815 * i + 814) * δ)
  induction fuel generalizing ys with
  | zero => simp [maskList, PMF.iid]
  | succ k ih =>
    let adjacentLaw y := U.bind (C.callWindow s H A keys sk next i rows (ys ++ [y]) k)
    let last y := (maskList s k).bind fun zs =>
      U.bind (C.callWindow s H A keys sk next i rows ((ys ++ [y]) ++ zs) 0)
    have adjacent := C.window_step s H A keys sk next i rows ys k hash
    have grow : 1 + ys.length ≤ 814 := by lia
    have one : |prob (U.bind (C.callWindow s H A keys sk next i rows ys (k + 1))) -
        prob (μ.bind adjacentLaw)| ≤ B := by
      apply adjacent.trans
      dsimp only [B, δ]
      gcongr
      exact_mod_cast grow
    have rest : |prob (μ.bind adjacentLaw) - prob (μ.bind last)| ≤ k * B := by
      apply abs_common_bind
      intro y
      exact ih (ys ++ [y]) (by simp only [List.length_append, List.length_singleton]; lia)
    have endLaw : ((maskList s (k + 1)).bind fun zs =>
        U.bind (C.callWindow s H A keys sk next i rows (ys ++ zs) 0)) = μ.bind last := by
      simp only [maskList, PMF.iid, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_bind,
        PMF.map_comp, PMF.bind_map, Function.comp_def, List.ofFn_cons, last, μ,
        List.append_assoc, List.singleton_append]
    rw [endLaw]
    exact (abs_sub_le _ (prob (μ.bind adjacentLaw)) _).trans
      ((add_le_add one rest).trans_eq (by push_cast; ring))

private theorem maskList_eq_row (s : Level) :
    maskList s 814 = (PMF.uniformOfFintype (Row s)).map (fun r => List.ofFn (rowMasks s r)) := by
  let μ := signingMaskLaw s.params (by cases s <;> decide)
  have lists (n : ℕ) (schedule : Row s → Fin n → Mask s)
      (law : (PMF.uniformOfFintype (Row s)).map schedule = PMF.iid μ n) :
      maskList s n = (PMF.uniformOfFintype (Row s)).map (fun r => List.ofFn (schedule r)) := by
    rw [maskList, ← law, PMF.map_comp]
    rfl
  exact lists 814 (rowMasks s) (iid_maskFromRow s)

private theorem all_reads_sign (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    (next : AfterCall C s) (D : Register s) (q : SigningQuery)
    (k : Option (List Byte) → C.Program Forgery) (d : C.Device) (l : List Forgery)
    (rest : List (Row s)) :
    let G := H.withDigestRegister s D
    let U := PMF.uniformOfFintype (Row s)
    (U.bind fun r => (maskList s 814).bind fun ys =>
      C.resumeRetries s H A next sk D 0 (.signing q k) (scanned s G A sk ys (.signing q k))
        l (r :: rest) d) =
      U.bind fun r =>
        let v := G.signWithExpansionRow s keys.secretKey q r
        next.run D (k v) d (q.logReply v l) rest := by
  intro G U
  let m := G.representativeFromTr sk.tr (formatMessage q.message q.context)
  let draw (ys : List (Mask s)) := if 255 < q.context.length then none else
    (ys.findSome? (fun y => terminalReply (G.attemptWithMask s sk A m y))).join
  let conclude r := next.run D (k r) d (q.logReply r l) rest
  have read (ys : List (Mask s)) (r : Row s) :
      C.resumeRetries s H A next sk D 0 (.signing q k) (scanned s G A sk ys (.signing q k))
        l (r :: rest) d = conclude (draw ys) := by
    by_cases large : 255 < q.context.length
    · simp only [scanned, preparedPrefix, draw, large, ↓reduceIte, resumeRetries,
        conclude, List.tail_cons]
    · simp only [scanned, preparedPrefix, draw, large, ↓reduceIte, resumeRetries,
        conclude, List.tail_cons]
      cases ys.findSome? (fun y => terminalReply (G.attemptWithMask s sk A m y)) <;> rfl
  have native (r : Row s) : G.signWithExpansionRow s keys.secretKey q r =
      draw (List.ofFn (rowMasks s r)) := by
    by_cases large : 255 < q.context.length
    · simp only [Xofs.signWithExpansionRow, Nat.not_le.mpr large, guard, ↓reduceIte,
        Option.failure_eq_none, Option.bind_eq_bind, Option.bind_none, draw, large]
    · have hG : G.expandA s sk.rho = some A := (Xofs.expandA_congr (H := H) rfl s _).trans mat
      simp only [Xofs.signWithExpansionRow, Nat.le_of_not_gt large, guard, ↓reduceIte,
        Option.pure_def, Option.bind_eq_bind, Option.bind_some, key, hG, draw, large,
        ← tupleReply_row, tupleReply, Fin.findSome?_eq_findSome?_finRange,
        List.ofFn_eq_map, List.findSome?_map]
      rfl
  simp only [read, PMF.bind_const, maskList_eq_row, PMF.bind_map, native]
  rfl

private theorem read_window_eq (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    {n : ℕ} (i : Fin n) (D : Register s) :
    let U := PMF.uniformOfFintype (Fin n → Row s)
    let G := H.withDigestRegister s D
    (U.bind fun rows => (maskList s 814).bind fun ys =>
      C.callWindow s H A keys sk (C.nativeAfter s H A keys) i (List.ofFn rows) ys 0 D) =
    U.bind fun rows => C.expansionContinuation s G A keys (C.program keys.publicKey)
      C.initialDevice [] (List.ofFn rows) := by
  intro U G
  let left (t : List (Row s)) := (maskList s 814).bind fun ys =>
    C.callWindow s H A keys sk (C.nativeAfter s H A keys) i t ys 0 D
  let right (t : List (Row s)) := C.expansionContinuation s G A keys (C.program keys.publicKey)
    C.initialDevice [] t
  apply uniform_tape_eq s i left right
  intro pre rows len
  let go (ys : List (Mask s)) (x : Boundary C) (d : C.Device) (l : List Forgery)
      (t : List (Row s)) := C.resumeRetries s H A (C.nativeAfter s H A keys) sk D 0 x
        (scanned s G A sk ys x) l t d
  change ((PMF.uniformOfFintype (Row s)).bind fun r => (maskList s 814).bind fun ys =>
      C.prefixRun s G keys (C.program keys.publicKey) i C.initialDevice [] (pre ++ r :: rows)
        (go ys)) = _
  rw [← len]
  apply C.prefixRun_eq s G keys A (maskList s 814) go
  · intros; rfl
  · intro q k d l rest
    exact C.all_reads_sign s H keys sk A key mat (C.nativeAfter s H A keys) D q k d l rest

private noncomputable def chosenCall (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (i : ℕ) (D : Register s) (keep : Bool)
    (rows : List (Row s)) : Game :=
  let G := H.withDigestRegister s D
  (C.cutInteraction s G keys i rows).bind fun (x, (d,l), t) =>
    match x with
    | .finished f => C.expansionContinuation s G A keys (.pure f) d l t
    | .signing q k => C.freshDigestSigningCall s H keys q D keep k d l t.tail

private theorem write_window_eq (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    (i : ℕ) (D : Register s) (rows : List (Row s)) :
    C.callWindow s H A keys sk (C.nativeAfter s H A keys) i rows [] 814 D =
      C.chosenCall s H A keys i D true rows := by
  apply congrArg (PMF.bind (C.cutInteraction s (H.withDigestRegister s D) keys i rows) ·)
  funext ⟨x, ⟨d,l⟩, t⟩
  cases x with
  | finished f => rfl
  | signing q k =>
    by_cases large : 255 < q.context.length <;>
      simp only [freshDigestSigningCall, key, mat, ↓reduceIte, scanned, preparedPrefix,
        resumeRetries, nativeAfter, retryCall, registerRequest, large, List.findSome?_nil]

private theorem cut_cost_after {C : QuantumSigningForger} {cost : Request C → ℕ}
    {prog : C.Program Forgery} {K : ℕ} (bounded : OracleComp.IsCostBounded cost prog K)
    (i : ℕ) {q : SigningQuery} {next : Option (List Byte) → C.Program Forgery}
    (reached : Boundary.signing q next ∈ OracleComp.supportWith (fun _ => Set.univ)
      (cut (C := C) prog i)) (r : Option (List Byte)) :
    OracleComp.IsCostBounded cost (next r) K := by
  induction prog generalizing i with
  | pure f => cases Set.mem_singleton_iff.mp reached
  | liftBind cmd k ih =>
    have sub (b) := ((OracleComp.IsCostBounded.liftBind_iff.mp bounded).2 b).mono
      (Nat.sub_le K _)
    have earlier (left : ℕ) (move : cut (C := C) (.liftBind cmd k) i =
        .liftBind cmd (fun b => cut (C := C) (k b) left)) :
        OracleComp.IsCostBounded cost (next r) K := by
      rw [move] at reached
      simp only [OracleComp.supportWith, Set.mem_iUnion, Set.mem_univ, exists_prop,
        true_and] at reached
      obtain ⟨b, hb⟩ := reached
      exact ih b (sub b) left hb
    rcases cmd with coin | op | ask
    · exact earlier i rfl
    · exact earlier i rfl
    · cases i with
      | zero =>
        have eq : Boundary.signing q next = Boundary.signing ask k :=
          Set.mem_singleton_iff.mp reached
        cases eq
        exact sub r
      | succ i => exact earlier i rfl

-- Average a bound at an adaptive signing boundary over the native execution which reaches it.
private theorem cut_bind_gap (C : QuantumSigningForger) (s : Level) (G : Xofs) (keys : KeyPair)
    (i : ℕ) (rows : List (Row s))
    (left right : Boundary C × (C.Device × List Forgery) × List (Row s) → Game)
    {e : ℝ} (he : 0 ≤ e)
    (bound : ∀ x d l t, x ∈ OracleComp.supportWith (fun _ => Set.univ)
      (cut (C := C) (C.program keys.publicKey) i) →
      |prob (left (x, (d, l), t)) - prob (right (x, (d, l), t))| ≤ e) :
    let past := C.cutInteraction s G keys i rows
    |prob (past.bind left) - prob (past.bind right)| ≤ e := by
  intro past
  let ε : NNReal := ⟨e, he⟩
  change |(Game.succProbability (past.bind left) : ℝ) - Game.succProbability (past.bind right)| ≤
    (ε : ℝ)
  rw [← Game.coe_advantage]
  apply NNReal.coe_le_coe.mpr (Game.advantage_bind_le_of_support past _ _ ?_)
  rintro ⟨x, ⟨d, l⟩, t⟩ hx
  apply NNReal.coe_le_coe.mp
  rw [Game.coe_advantage]
  apply bound
  rw [show past = _ from (OracleComp.runWith_eq_run_interpret _ _ _).symm] at hx
  exact OracleComp.mem_supportWith_of_mem_support_runWith _ (fun _ _ _ _ _ => Set.mem_univ _) hx

private theorem erase_at_cut (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    {qH n : ℕ} (hash : C.XofCallsLe qH) (calls : C.SigningCallsLe n)
    (i : ℕ) (D : Register s) (rows : List (Row s)) :
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |prob (C.chosenCall s H A keys i D true rows) -
      prob (C.chosenCall s H A keys i D false rows)| ≤ 814 * (4 * qH * √δ + (815 * n + 2) * δ) := by
  intro δ
  let G := H.withDigestRegister s D
  unfold chosenCall
  apply C.cut_bind_gap s G keys i rows _ _ (by positivity)
  intro x d l t possible
  cases x with
  | finished f =>
    simp only [sub_self, abs_zero]
    positivity
  | signing q k =>
    have h := C.abs_freshDigestSigningCall_keep_sub_erase_le s H keys q D k d l t.tail
      (cut_cost_after (hash _) i possible) (cut_cost_after (calls _) i possible)
    simpa only [Game.coe_succProbability, prob, key, mat, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.getD_some, δ] using h

-- Average both comparisons with the same actual generated matrix. First pay for changing
-- ambient reads throughout the request, then for removing all the writes made on rejection.
private theorem conditioned_call_gap (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    {qH n : ℕ} (hash : C.XofCallsLe qH) (calls : C.SigningCallsLe n) (i : Fin n) :
    let rows := PMF.uniformOfFintype (Fin n → Row s)
    let U := PMF.uniformOfFintype (Register s)
    let native := U.bind fun D => rows.bind fun rs =>
      C.expansionContinuation s (H.withDigestRegister s D) A keys (C.program keys.publicKey)
        C.initialDevice [] (List.ofFn rs)
    let programmed := rows.bind fun rs => U.bind fun D =>
      C.chosenCall s H A keys i D false (List.ofFn rs)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |prob programmed - prob native| ≤
      814 * (4 * qH * √δ + (815 * n + 2) * δ) +
        814 * (2 * (4 * qH * √δ + (815 * i.val + 814) * δ)) := by
  intro rows U native programmed δ
  let fresh := rows.bind fun rs => U.bind fun D => C.chosenCall s H A keys i D true (List.ofFn rs)
  let first (rs : Fin n → Row s) : Game := (maskList s 814).bind fun ys =>
    U.bind (C.callWindow s H A keys sk (C.nativeAfter s H A keys) i (List.ofFn rs) ys 0)
  have source : rows.bind first = native := by
    dsimp only [first, native]
    simp_rw [PMF.bind_comm (maskList s 814) U, PMF.bind_comm rows U]
    apply congrArg (PMF.bind U ·)
    funext D
    exact C.read_window_eq s H keys sk A key mat i D
  have erase : |prob programmed - prob fresh| ≤ 814 * (4 * qH * √δ + (815 * n + 2) * δ) := by
    rw [abs_sub_comm]
    apply abs_common_bind rows
    intro rs
    exact abs_common_bind U _ _ fun D => C.erase_at_cut s H keys sk A key mat hash calls i D _
  have refresh : |prob fresh - prob native| ≤
      814 * (2 * (4 * qH * √δ + (815 * i.val + 814) * δ)) := by
    rw [← source]
    apply abs_common_bind rows
    intro rs
    have windows := C.all_windows s H A keys sk (C.nativeAfter s H A keys) i (List.ofFn rs)
      [] 814 (by simp) hash
    have write : C.callWindow s H A keys sk (C.nativeAfter s H A keys) i (List.ofFn rs) [] 814 =
        fun D => C.chosenCall s H A keys i D true (List.ofFn rs) :=
      funext fun D => C.write_window_eq s H keys sk A key mat i D _
    simpa only [List.nil_append, write, Nat.cast_ofNat, first, δ] using windows
  exact (abs_sub_le _ (prob fresh) _).trans (add_le_add erase refresh)

/-- Serve the indexed signing request with the terminal-write handler from the public-pair
signing reduction. Other requests use the native private-expansion signer. Each attempted mask and
digest at the selected request is freshly sampled, all later queries and the verifier use
the resulting stream, and the verifier scores a forgery only on the fresh-digest branch. -/
noncomputable def refreshedCallGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b : ℕ) {n : ℕ} (i : Fin n) : Game := do
  let H ← base.uniformPrefixes a b
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  let some keys := H.keyGen s seed | return false
  let some A := H.expandA s (keys.publicKey.take 32) | return false
  let rows ← PMF.uniformOfFintype (Fin n → Row s)
  let D ← PMF.uniformOfFintype (Register s)
  C.chosenCall s H A keys i D false (List.ofFn rows)

/-- Replacing every commitment read at a fixed index in an adaptive FIPS signing interaction with
the simulator's terminal-write signing service changes fresh-digest forgery probability by at
most the displayed seeded-matrix average. The two summands account for erasing rejected writes
and for refreshing the ambient digest after earlier coherent queries and native rejections. -/
theorem abs_refreshedCallGame_sub_freshExpansionGame_le (C : QuantumSigningForger)
    (s : Level) (base : Xofs) {a b n qH : ℕ} (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) (calls : C.SigningCallsLe n) (hash : C.XofCallsLe qH)
    (i : Fin n) :
    let matrices := (base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).map fun seed => do
        let keys ← H.keyGen s seed
        H.expandA s (keys.publicKey.take 32)
    let win := Game.succProbability (C.refreshedCallGame s base a b i)
    let orig := Game.succProbability (C.freshExpansionGame s base a b)
    |(win : ℝ) - (orig : ℝ)| ≤ ∑ A : Option (PublicMatrix s), (matrices A).toReal *
      (A.elim 0 fun M =>
        let δ := (commitmentGuessProbability s.params (by cases s <;> decide) M).toReal
        814 * (4 * qH * √δ + (815 * n + 2) * δ) +
          814 * (2 * (4 * qH * √δ + (815 * i.val + 814) * δ))) := by
  intro matrices win orig
  let U := PMF.uniformOfFintype (Fin n → Row s)
  let law := PMF.uniformOfFintype (FixedBytes 32)
  let cost (A : Option (PublicMatrix s)) := A.elim 0 fun M =>
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) M).toReal
    814 * (4 * qH * √δ + (815 * n + 2) * δ) +
      814 * (2 * (4 * qH * √δ + (815 * i.val + 814) * δ))
  let test : Bool → Xofs → FixedBytes 32 → Game := fun written H seed =>
    match H.keyGen s seed with
    | some keys =>
      if written then
        match H.expandA s (keys.publicKey.take 32) with
        | some A => U.bind fun rs => (PMF.uniformOfFintype (Register s)).bind fun D =>
            C.chosenCall s H A keys i D false (List.ofFn rs)
        | _ => PMF.pure false
      else U.bind fun rs => C.commitmentTrialGame s H keys i 0 (List.ofFn rs) false
    | _ => PMF.pure false
  rw [show orig = Game.succProbability (C.expansionTrialGame s base a b i 0 false) from
    congrArg Game.succProbability (C.expansionTrialGame_read_eq_freshExpansionGame
      s base ha hb calls i 0).symm]
  simp only [win, refreshedCallGame, expansionTrialGame, Game.coe_succProbability,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  apply seeded_gap_le s base a b test cost
  intro H seed
  cases kg : H.keyGen s seed with
  | none => simp [test, kg, generatedMatrix, cost, prob]
  | some keys =>
    obtain ⟨rho, pair, mat, pk, sk, _⟩ := privateKey_of_keyGen kg
    have pub : H.expandA s (keys.publicKey.take 32) = some pair.A := by
      rw [pk, take_encodePublic, mat]
    simp only [test, kg, pub, Bool.false_eq_true, ↓reduceIte, generatedMatrix, Option.bind_eq_bind,
      Option.bind_some, cost, Option.elim_some]
    have read := C.read_at_generated s H seed keys kg i 0
    dsimp only at read
    simp only [Xofs.expandA_congr (K := H.withDigestRegister s _) (H := H) rfl s, pub] at read
    rw [show (U.bind fun rs => C.commitmentTrialGame s H keys i 0 (List.ofFn rs) false) = _
      from read]
    exact C.conditioned_call_gap s H keys _ pair.A sk mat hash calls i

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
