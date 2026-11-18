/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PriorCommitmentRefresh
import all CslibFrontier.Crypto.Computational.MLDSA.PriorCommitmentRefresh
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXofMask
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning

/-!
# Refreshing a digest in the byte-row signing experiment

In the private-expansion experiment the nonce-indexed byte row supplies the masks for the capped
signer of [NISTFIPS204], Algorithms 7 and 34. Resampling one coordinate preserves the joint law
of all 814 scheduled masks. Stopping and resuming the adaptive controller at that attempt therefore
preserves its read-only forgery law. This yields an original bound on replacing one digest in the
seeded private-expansion experiment, averaged over its actual public matrices.
-/

public section
namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability Cslib.Quantum

private def rowMasks (s : Level) (row : FixedBytes 2 → FixedBytes (maskPolyBytes s))
    (i : Fin 814) : Fin s.params.ℓ → Poly :=
  ringVectorCoeffs (maskFromRow s row (signingAttemptCounter s.params 0 i))

private theorem replace_row_mask {α : Type} (s : Level) (j : Fin 814)
    (score : (Fin 814 → Fin s.params.ℓ → Poly) → PMF α) :
    ((PMF.uniformOfFintype (FixedBytes 2 → FixedBytes (maskPolyBytes s))).bind fun row =>
      (signingMaskLaw s.params (by cases s <;> decide)).bind fun y =>
        score (Function.update (rowMasks s row) j y)) =
    (PMF.uniformOfFintype (FixedBytes 2 → FixedBytes (maskPolyBytes s))).bind
      (fun row => score (rowMasks s row)) := by
  classical
  have law := iid_maskFromRow s
  change (PMF.uniformOfFintype _).map (rowMasks s) = _ at law
  let U := PMF.uniformOfFintype (Coefficients s)
  let read (c : Coefficients s) := fun i => ringRow (c i)
  have box : U.map read = signingMaskLaw s.params (by cases s <;> decide) := maskLaw_coefficients s
  let rerun (v : Fin 814 → Fin s.params.ℓ → Poly) :=
    (signingMaskLaw s.params (by cases s <;> decide)).bind fun y => score (Function.update v j y)
  change (PMF.bind _ (rerun ∘ rowMasks s)) = PMF.bind _ (score ∘ rowMasks s)
  rw [← PMF.bind_map, ← PMF.bind_map, law, ← box,
    PMF.iid_map, PMF.iid_uniformOfFintype, PMF.bind_map, PMF.bind_map]
  simp only [rerun, ← box, PMF.bind_map]
  have commute (v : Fin 814 → Coefficients s) (c : Coefficients s) :
      Function.update (fun i => read (v i)) j (read c) =
      fun i => read (Function.update v j c i) := by
    funext i
    by_cases h : i = j <;> simp [h, Function.update_of_ne]
  change (PMF.bind (PMF.uniformOfFintype (Fin 814 → Coefficients s)) (fun v =>
    U.bind fun c => score (Function.update (fun i => read (v i)) j (read c)))) = _
  simp_rw [commute]
  exact PMF.uniformOfFintype_bind_bind_adaptiveUpdate (fun _ => j) (fun _ _ => rfl)
    (fun v => score (fun i => read (v i)))

-- Separate the tests before the selected nonce. A terminal error prevents further attempts.
private theorem split_firstAccepted (step : ℕ) (tryAt : ℕ → Option (Option (List Byte)))
    (pre post start : ℕ) :
    firstAccepted step tryAt (pre + post) start =
      match Fin.findSome? (fun i : Fin pre => terminalReply (tryAt (start + i.val * step))) with
      | some r => r
      | none => firstAccepted step tryAt post (start + pre * step) := by
  induction pre generalizing start with
  | zero => simp [Fin.findSome?]
  | succ pre ih =>
    rw [Nat.succ_add, Fin.findSome?_succ]
    have next (i : Fin pre) : start + i.succ.val * step = start + step + i.val * step := by
      rw [Fin.val_succ, Nat.succ_mul]
      lia
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, next]
    cases h : tryAt start with
    | none => simp [firstAccepted, terminalReply, h]
    | some r =>
      cases r with
      | some sig => simp [firstAccepted, terminalReply, h]
      | none =>
        have eq : start + (pre + 1) * step = start + step + pre * step := by
          rw [Nat.succ_mul]
          lia
        simpa only [firstAccepted, h, Option.bind_some, terminalReply, Option.map_none,
          Option.none_or, Option.bind_eq_bind, eq] using ih (start + step)


private def tupleReply (s : Level) (G : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (m : List Bool) (v : Fin 814 → Fin s.params.ℓ → Poly) : Option (List Byte) :=
  (Fin.findSome? fun i => terminalReply (G.attemptWithMask s sk A m (v i))).join

private theorem tupleReply_row (s : Level) (G : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (m : List Bool) (r) :
    tupleReply s G A sk m (rowMasks s r) = G.signingRetries s sk A m (maskFromRow s r) := by
  rw [Xofs.signingRetries, firstAccepted_eq_terminal]
  rfl

private theorem find_updated (s : Level) (G : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (m : List Bool) (r) (j : Fin 814) (y : Fin s.params.ℓ → Poly) :
    tupleReply s G A sk m (Function.update (rowMasks s r) j y) =
    (match (List.finRange j.val).findSome? (fun i => terminalReply (G.attemptWithMask s sk A m
        (ringVectorCoeffs (maskFromRow s r (i.val * s.params.ℓ))))) with
    | some reply => reply
    | none => do
      let result ← G.attemptWithMask s sk A m y
      match result with
      | some sig => some sig
      | none =>
        firstAccepted s.params.ℓ (fun n => G.attemptWithMask s sk A m
          (ringVectorCoeffs (maskFromRow s r n))) (813 - j.val) ((j.val + 1) * s.params.ℓ)) := by
  let step := s.params.ℓ
  have pos : 0 < step := by cases s <;> decide
  let cutAt := j.val * step
  let raw n := ringVectorCoeffs (maskFromRow s r n)
  let attempt n := G.attemptWithMask s sk A m (Function.update raw cutAt y n)
  have addr (i : Fin 814) : Function.update (rowMasks s r) j y i =
      Function.update raw cutAt y (i.val * step) := by
    by_cases h : i = j
    · subst i
      simp [cutAt]
    · have ne : i.val * step ≠ cutAt := fun eq =>
        h (Fin.ext (Nat.eq_of_mul_eq_mul_right pos eq))
      rw [Function.update_of_ne h, Function.update_of_ne ne]
      simp only [rowMasks, signingAttemptCounter, Nat.zero_add, raw, step]
  have full : tupleReply s G A sk m (Function.update (rowMasks s r) j y) =
      firstAccepted step attempt 814 0 := by
    rw [firstAccepted_eq_terminal]
    simp only [tupleReply, Nat.zero_add, addr, attempt]
  rw [full, congrArg (fun n => firstAccepted step attempt n 0)
    (show 814 = j.val + (1 + (813 - j.val)) by lia), split_firstAccepted,
    ← Fin.findSome?_eq_findSome?_finRange]
  have before (i : Fin j.val) : attempt (i.val * step) =
      G.attemptWithMask s sk A m (raw (i.val * step)) := by
    have ne : i.val * step ≠ cutAt := Nat.ne_of_lt (Nat.mul_lt_mul_of_pos_right i.isLt pos)
    simp [attempt, ne]
  simp only [Nat.zero_add, before]
  cases done : Fin.findSome? (fun i : Fin j.val => terminalReply
    (G.attemptWithMask s sk A m (raw (i.val * step)))) with
  | some reply => rfl
  | none =>
    change firstAccepted step attempt (1 + (813 - j.val)) cutAt = _
    rw [Nat.one_add, firstAccepted]
    have mid : attempt cutAt = G.attemptWithMask s sk A m y := by simp [attempt]
    rw [mid]
    cases h : G.attemptWithMask s sk A m y with
    | none => simp only [Option.bind_eq_bind, Option.bind_none]
    | some reply =>
      cases reply with
      | some sig => simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      | none =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        change firstAccepted step attempt (813 - j.val) (cutAt + step) = _
        have start : (j.val + 1) * step = cutAt + step := Nat.succ_mul j.val step
        rw [firstAccepted_eq_terminal, firstAccepted_eq_terminal, start]
        apply congrArg Option.join
        apply congrArg Fin.findSome?
        funext i
        have ne : cutAt + step + i.val * step ≠ cutAt := by lia
        simp [attempt, Function.update_of_ne ne, raw, step]

namespace QuantumSigningForger

private theorem afterTrial_read {C : QuantumSigningForger} (s : Level) (G : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (q : SigningQuery) (k : Option (List Byte) →
      C.Program Forgery) (j : Fin 814) (y : Fin s.params.ℓ → Poly) (r rows log) :
    let m := G.representativeFromTr sk.tr (formatMessage q.message q.context)
    let reply := if 255 < q.context.length then none else
      tupleReply s G A sk m (Function.update (rowMasks s r) j y)
    afterTrial s G A sk j y (.signing q k)
        (nativePreparation s G A sk j (.signing q k) (r :: rows)) log (r :: rows) =
      (k reply, q.logReply reply log, rows) := by
  intro m reply
  by_cases over : 255 < q.context.length
  · simp [afterTrial, nativePreparation, preparedPrefix, reply, over]
  · have bits : List.ofFn (BitString.ofList 512 m) = m := BitString.ofFn_ofList
      (by simp only [m, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, G.h256.length_read])
    simp only [afterTrial, nativePreparation, preparedPrefix, rowAttempt, reply, over, ↓reduceIte,
      List.headD_cons,
      List.tail_cons, find_updated]
    cases done : (List.finRange j.val).findSome? (fun i => terminalReply
      (G.attemptWithMask s sk A m (ringVectorCoeffs (maskFromRow s r (i.val * s.params.ℓ))))) with
    | some reply => rfl
    | none =>
      dsimp only [m] at bits
      simp only [bits]
      rfl

private abbrev Resume (C : QuantumSigningForger) (s : Level) :=
  Boundary C → C.Device → List Forgery → List (Row s) → Game

-- Pause the actual controller immediately before the indexed signing call and pass the full
-- remaining state to the specified continuation. Early termination passes the final forgery.
private noncomputable def prefixInteraction (C : QuantumSigningForger) (s : Level) (G : Xofs)
    (keys : KeyPair) (prog : C.Program Forgery) (i : ℕ) (dev : C.Device) (l : List Forgery)
    (t : List (Row s)) :=
  (OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (0 : Row s)
    (fun row => C.signingCommand G (fun q => G.signWithExpansionRow s keys.secretKey q row)))
    (cut (C := C) prog i)).run ((dev, l), t)

private noncomputable def prefixRun (C : QuantumSigningForger) (s : Level) (G : Xofs)
    (keys : KeyPair) (prog : C.Program Forgery) (i : ℕ) (dev : C.Device) (l : List Forgery)
    (t : List (Row s)) (resume : Resume C s) : Game :=
  (C.prefixInteraction s G keys prog i dev l t).bind fun (x, (d, log), rest) => resume x d log rest

private theorem prefixRun_step (C : QuantumSigningForger) (s : Level) (G keys)
    {cmd : Request C} (k : _ → C.Program Forgery) (i i' : ℕ)
    (push : cut (C := C) (.liftBind cmd k) i =
      .liftBind cmd (fun b => cut (C := C) (k b) i')) (dev log rows) (resume : Resume C s) :
    C.prefixRun s G keys (.liftBind cmd k) i dev log rows resume =
    ((OracleComp.withSampleListWhen isSigningCall (0 : Row s)
      (fun row => C.signingCommand G (fun q => G.signWithExpansionRow s keys.secretKey q row))
      cmd).run ((dev, log), rows)).bind fun (b, (d, l), t) =>
        C.prefixRun s G keys (k b) i' d l t resume := by
  simp only [prefixRun, prefixInteraction, push,
    show PFunctor.FreeM.liftBind cmd (fun b => cut (C := C) (k b) i') =
    (OracleComp.query cmd >>= fun b => cut (C := C) (k b) i') from rfl,
    OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
    PMF.monad_bind_eq_bind, PMF.bind_bind]
  rfl

private theorem prefixRun_eq {V : Type} (C : QuantumSigningForger) (s : Level) (G : Xofs)
    (keys : KeyPair) (A : PublicMatrix s) (μ : PMF V) (resume : V → Resume C s)
    (finish : ∀ y f d l t, resume y (.finished f) d l t =
      C.expansionContinuation s G A keys (.pure f) d l t)
    (sign : ∀ q k d l t, ((PMF.uniformOfFintype (Row s)).bind fun r =>
        μ.bind fun y => resume y (.signing q k) d l (r :: t)) =
      (PMF.uniformOfFintype (Row s)).bind fun r =>
        let sig := G.signWithExpansionRow s keys.secretKey q r
        C.expansionContinuation s G A keys (k sig) d (q.logReply sig l) t)
    (prog : C.Program Forgery) (dev : C.Device) (log : List Forgery) (pre rows : List (Row s)) :
    let U := PMF.uniformOfFintype (Row s)
    (U.bind fun r => μ.bind fun y =>
      C.prefixRun s G keys prog pre.length dev log (pre ++ r :: rows) (resume y)) =
    U.bind fun r => C.expansionContinuation s G A keys prog dev log (pre ++ r :: rows) := by
  intro U
  induction prog generalizing pre dev log with
  | pure f =>
    simp only [prefixRun, prefixInteraction, cut, PFunctor.FreeM.pure_eq_pure,
      OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.pure_bind, finish, PMF.bind_const]
  | liftBind cmd k ih =>
    have step (c : Request C) (next : _ → C.Program Forgery) (d : C.Device) (l t) :
        C.expansionContinuation s G A keys (.liftBind c next) d l t =
        ((OracleComp.withSampleListWhen isSigningCall (0 : Row s) (fun r => C.signingCommand G
          (fun q => G.signWithExpansionRow s keys.secretKey q r)) c).run ((d, l), t)).bind
          fun (b, (st, log'), t') => C.expansionContinuation s G A keys (next b) st log' t' :=
      scored_step (q := c) (k := next) ..
    let handler (r : Row s) := C.signingCommand G
      (fun q => G.signWithExpansionRow s keys.secretKey q r)
    have off (skip : isSigningCall cmd = false) (push : ∀ i, cut (C := C) (.liftBind cmd k) i =
        .liftBind cmd (fun b => cut (C := C) (k b) i)) :
        (U.bind fun r => μ.bind fun y =>
          C.prefixRun s G keys (.liftBind cmd k) pre.length dev log (pre ++ r :: rows) (resume y)) =
        U.bind fun r => C.expansionContinuation s G A keys (.liftBind cmd k)
          dev log (pre ++ r :: rows) := by
      simp only [prefixRun_step _ _ _ _ _ _ _ (push _), step, OracleComp.withSampleListWhen,
        skip, Bool.false_eq_true, ↓reduceIte, StateT.run, PMF.bind_map, Function.comp_def]
      let p := handler 0 cmd (dev, log)
      conv_rhs => rw [PMF.bind_comm U p]
      conv_lhs =>
        arg 2; ext r
        rw [PMF.bind_comm μ p]
      rw [PMF.bind_comm U p]
      exact congrArg (PMF.bind p ·) (funext fun z => ih z.1 z.2.1 z.2.2 pre)
    rcases cmd with coin | op | q
    · exact off rfl (fun _ => rfl)
    · exact off rfl (fun _ => rfl)
    · have ordinary (d : C.Device) (l : List Forgery) (r : Row s) (t : List (Row s)) :
          let sig := G.signWithExpansionRow s keys.secretKey q r
          C.expansionContinuation s G A keys (.liftBind (.inr (.inr q)) k) d l (r :: t) =
            C.expansionContinuation s G A keys (k sig) d (q.logReply sig l) t :=
        scored_sign (ask := q) (k := k) ..
      cases pre with
      | nil =>
        simp only [List.length_nil, List.nil_append, prefixRun, prefixInteraction, cut,
          PFunctor.FreeM.pure_eq_pure, OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure,
          PMF.pure_bind, ordinary]
        exact sign q k dev log rows
      | cons p pre =>
        have push : cut (C := C) (.liftBind (.inr (.inr q)) k) (pre.length + 1) =
            .liftBind (.inr (.inr q)) (fun b => cut (C := C) (k b) pre.length) := rfl
        simp only [List.length_cons, List.cons_append, prefixRun_step _ _ _ _ _ _ _ push,
          ordinary, OracleComp.withSampleListWhen, isSigningCall, Sum.elim_inr, ↓reduceIte,
          OracleComp.withSampleList,
          List.headD_cons, List.tail_cons, signingCommand, OracleComp.sumHandler, StateT.run,
          pmf_norm]
        exact ih _ _ _ pre

private noncomputable def readUntil (C : QuantumSigningForger) (s : Level) (G : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (prog : C.Program Forgery)
    (i : ℕ) (j : Fin 814) (dev : C.Device) (log : List Forgery) (rows : List (Row s))
    (y : Mask s) : Game :=
  C.prefixRun s G keys prog i dev log rows fun x d l t =>
    let (next, signed, rest) := afterTrial s G A sk j y x (nativePreparation s G A sk j x t) l t
    C.expansionContinuation s G A keys next d signed rest

private theorem readUntil_eq (C : QuantumSigningForger) (s : Level) (G : Xofs) (keys : KeyPair)
    (sk : PrivateKey s) (A : PublicMatrix s) (key : decodePrivate s keys.secretKey = some sk)
    (mat : G.expandA s sk.rho = some A) (prog : C.Program Forgery)
    (j : Fin 814) (dev : C.Device) (log : List Forgery) (pre rows : List (Row s)) :
    let U := PMF.uniformOfFintype (Row s)
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    (U.bind fun r => μ.bind fun y =>
      C.readUntil s G A keys sk prog pre.length j dev log (pre ++ r :: rows) y) =
    U.bind fun r => C.expansionContinuation s G A keys prog dev log (pre ++ r :: rows) := by
  apply prefixRun_eq
  · intros
    rfl
  · intro q k dev log rows
    let m := G.representativeFromTr sk.tr (formatMessage q.message q.context)
    let reply v := if 255 < q.context.length then none else tupleReply s G A sk m v
    let score v := C.expansionContinuation s G A keys (k (reply v)) dev
      (q.logReply (reply v) log) rows
    have native (r : Row s) : G.signWithExpansionRow s keys.secretKey q r =
        reply (rowMasks s r) := by
      by_cases large : 255 < q.context.length
      · simp [Xofs.signWithExpansionRow, reply, large, Nat.not_le.mpr large]
      · simp [Xofs.signWithExpansionRow, reply, large, Nat.le_of_not_gt large, key, mat, m,
          tupleReply_row]
    simp only [afterTrial_read, native]
    exact replace_row_mask s j score

private theorem uniform_tape_eq (s : Level) {n : ℕ} (i : Fin n)
    (left right : List (Row s) → Game)
    (same : ∀ pre rows, pre.length = i.val →
      ((PMF.uniformOfFintype (Row s)).bind fun r => left (pre ++ r :: rows)) =
      (PMF.uniformOfFintype (Row s)).bind fun r => right (pre ++ r :: rows)) :
    let U := PMF.uniformOfFintype (Fin n → Row s)
    (U.bind fun v => left (List.ofFn v)) = U.bind fun v => right (List.ofFn v) := by
  intro U
  have split (v : Fin n → Row s) (r : Row s) : List.ofFn (Function.update v i r) =
      (List.ofFn v).take i.val ++ r :: (List.ofFn v).drop (i.val + 1) := by
    rw [← show (List.ofFn v).set i.val r = _ from List.set_eq_take_append_cons_drop.trans
      (ite_eq_left (by simp))]
    apply List.ext_getElem
    · simp
    · intro h h₁ h₂
      rw [List.getElem_ofFn, List.getElem_set]
      by_cases eq : i.val = h
      · subst h
        simp
      · have ne : (⟨h, by simpa using h₁⟩ : Fin n) ≠ i := fun e => eq (congrArg Fin.val e).symm
        simp [eq, Function.update_of_ne ne]
  have mix (f : List (Row s) → Game) :
      (U.bind fun v => (PMF.uniformOfFintype (Row s)).bind fun r =>
        f (List.ofFn (Function.update v i r))) = U.bind (fun v => f (List.ofFn v)) :=
    PMF.uniformOfFintype_bind_bind_adaptiveUpdate (fun _ => i) (fun _ _ => rfl)
      (fun v => f (List.ofFn v))
  change (U.bind fun v => left (List.ofFn v)) = U.bind fun v => right (List.ofFn v)
  rw [← mix left, ← mix right]
  apply congrArg (PMF.bind U ·)
  funext v
  simp only [split]
  have len : ((List.ofFn v).take i.val).length = i.val := by simp
  exact same _ _ len

private theorem uniform_readUntil (C : QuantumSigningForger) (s : Level) (G : Xofs) (keys : KeyPair)
    (sk : PrivateKey s) (A : PublicMatrix s) (key : decodePrivate s keys.secretKey = some sk)
    (mat : G.expandA s sk.rho = some A) {n : ℕ} (i : Fin n) (j : Fin 814) :
    let U := PMF.uniformOfFintype (Fin n → Row s)
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let prog := C.program keys.publicKey
    (U.bind fun rs => μ.bind fun y =>
      C.readUntil s G A keys sk prog i j C.initialDevice [] (List.ofFn rs) y) =
    U.bind fun rs => C.expansionContinuation s G A keys prog C.initialDevice [] (List.ofFn rs) := by
  intro U μ prog
  let left (t : List (Row s)) := μ.bind fun y =>
    C.readUntil s G A keys sk prog i j C.initialDevice [] t y
  let right (t : List (Row s)) := C.expansionContinuation s G A keys prog C.initialDevice [] t
  apply uniform_tape_eq s i left right
  intro pre rows len
  simpa only [len] using C.readUntil_eq s G keys sk A key mat prog j C.initialDevice [] pre rows

private theorem read_at_generated (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (seed : FixedBytes 32) (keys : KeyPair) (kg : H.keyGen s seed = some keys)
    {n : ℕ} (i : Fin n) (j : Fin 814) :
    let rows := PMF.uniformOfFintype (Fin n → Row s)
    (rows.bind fun rs => C.commitmentTrialGame s H keys i j (List.ofFn rs) false) =
      (PMF.uniformOfFintype (Register s)).bind fun D =>
        let G := H.withDigestRegister s D
        match G.expandA s (keys.publicKey.take 32) with
        | some A => rows.bind fun rs => C.expansionContinuation s G A keys
            (C.program keys.publicKey) C.initialDevice [] (List.ofFn rs)
        | _ => PMF.pure false := by
  intro rows
  obtain ⟨rho, pair, mat, pk, sk, _⟩ := privateKey_of_keyGen kg
  have pub : H.expandA s (keys.publicKey.take 32) = some pair.A := by
    rw [pk, take_encodePublic, mat]
  simp only [commitmentTrialGame, sk, mat, PMF.monad_bind_eq_bind,
    Xofs.expandA_congr (K := H.withDigestRegister s _) (H := H) rfl s, pub]
  let μ := signingMaskLaw s.params (by cases s <;> decide)
  let U := PMF.uniformOfFintype (Register s)
  have eval (priv : PrivateKey s) D (rs : Fin n → Row s) y : ∀ v,
      C.nativeStage s H D pair.A priv keys i j (List.ofFn rs) false y v =
      C.readUntil s (H.withDigestRegister s D) pair.A keys priv (C.program keys.publicKey)
        i j C.initialDevice [] (List.ofFn rs) y := fun _ => rfl
  simp only [eval, PMF.bind_const]
  conv_lhs => arg 2; ext rs; rw [PMF.bind_comm μ U]
  rw [PMF.bind_comm rows U]
  apply congrArg (PMF.bind U ·)
  funext D
  exact C.uniform_readUntil s _ keys _ pair.A sk
    ((Xofs.expandA_congr (K := H.withDigestRegister s D) (H := H) rfl ..).trans mat) i j

/-- The private-expansion signing experiment with one selected attempt. The actual seeded
setup and the entire private row tape are sampled before running the forger. At that attempt
the signer reads the shared digest, or writes a fresh digest and retains it on rejection. -/
noncomputable def expansionTrialGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b : ℕ) {n : ℕ} (i : Fin n) (j : Fin 814) (write : Bool) : Game := do
  let H ← base.uniformPrefixes a b
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  let some keys := H.keyGen s seed | return false
  let rows ← PMF.uniformOfFintype (Fin n → Row s)
  C.commitmentTrialGame s H keys i j (List.ofFn rows) write

/-- Reading at the selected attempt has the exact fresh-digest forgery law of the original
private-expansion signer, for every covered request and retry index. The row is sampled even
when an earlier signature, fatal error, or early termination makes the selection unreachable. -/
theorem expansionTrialGame_read_eq_freshExpansionGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b)
    (calls : C.SigningCallsLe n) (i : Fin n) (j : Fin 814) :
    C.expansionTrialGame s base a b i j false = C.freshExpansionGame s base a b := by
  let check (G : Xofs) : Game := do
    let seed ← PMF.uniformOfFintype (FixedBytes 32)
    let some keys := G.keyGen s seed | return false
    let some A := G.expandA s (keys.publicKey.take 32) | return false
    let rows ← PMF.uniformOfFintype (Fin n → Row s)
    C.expansionContinuation s G A keys (C.program keys.publicKey) C.initialDevice []
      (List.ofFn rows)
  have law := congrArg (fun p : PMF (Register s × Xofs) => p.bind (fun v => check v.2))
    (base.uniformPrefixes_digestRegister s ha hb)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at law
  rw [C.freshExpansionGame_eq_expansionContinuation s base a b calls]
  change _ = (base.uniformPrefixes a b).bind check
  rw [← law]
  simp only [expansionTrialGame, PMF.monad_bind_eq_bind]
  apply congrArg (PMF.bind (base.uniformPrefixes a b) ·)
  funext H
  simp only [check, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, Xofs.keyGen_withDigestRegister]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Register s))]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (FixedBytes 32)) ·)
  funext seed
  cases kg : H.keyGen s seed with
  | none => simp
  | some keys => exact C.read_at_generated s H seed keys kg i j

private def generatedMatrix (s : Level) (H : Xofs) (seed : FixedBytes 32) :
    Option (PublicMatrix s) := do
  let keys ← H.keyGen s seed
  H.expandA s (keys.publicKey.take 32)

private theorem seeded_gap_le (s : Level) (base : Xofs) (a b : ℕ)
    (test : Bool → Xofs → FixedBytes 32 → Game) (cost : Option (PublicMatrix s) → ℝ)
    (point : ∀ H seed, |prob (test true H seed) - prob (test false H seed)| ≤
      cost (generatedMatrix s H seed)) :
    let law := PMF.uniformOfFintype (FixedBytes 32)
    let matrices := (base.uniformPrefixes a b).bind fun H => law.map (generatedMatrix s H)
    |prob ((base.uniformPrefixes a b).bind fun H => law.bind (test true H)) -
      prob ((base.uniformPrefixes a b).bind fun H => law.bind (test false H))| ≤
      ∑ A, (matrices A).toReal * cost A := by
  classical
  intro law matrices
  unfold matrices Xofs.uniformPrefixes
  simp only [PMF.bind_map, Function.comp_def, PMF.sum_bind_mul, PMF.sum_map_mul]
  apply (PMF.abs_bind_sub_le_meanAbsDiffAt _ true _ _).trans
  apply Finset.sum_le_sum
  intro table _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply (PMF.abs_bind_sub_le_meanAbsDiffAt _ true _ _).trans
  apply Finset.sum_le_sum
  intro seed _
  exact mul_le_mul_of_nonneg_left (point _ seed) ENNReal.toReal_nonneg

/-- At one attempt in the original private-expansion experiment, persistent reprogramming costs
the average of the prior-query bound under the actual seeded matrix distribution. Failed key
generation contributes zero. The same sampled streams are used for setup, signing, verification
and public queries. -/
theorem abs_expansionTrialGame_write_sub_freshExpansionGame_le (C : QuantumSigningForger)
    (s : Level) (base : Xofs) {a b n qH : ℕ} (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) (calls : C.SigningCallsLe n) (hash : C.XofCallsLe qH)
    (i : Fin n) (j : Fin 814) :
    let matrices := (base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).map fun seed => do
        let keys ← H.keyGen s seed
        H.expandA s (keys.publicKey.take 32)
    let win := Game.succProbability (C.expansionTrialGame s base a b i j true)
    let orig := Game.succProbability (C.freshExpansionGame s base a b)
    |(win : ℝ) - (orig : ℝ)| ≤ ∑ A : Option (PublicMatrix s), (matrices A).toReal *
      (A.elim 0 fun M =>
        let δ := (commitmentGuessProbability s.params (by cases s <;> decide) M).toReal
        2 * (4 * qH * √δ + (815 * i.val + (1 + j.val)) * δ)) := by
  classical
  intro matrices win orig
  let law := PMF.uniformOfFintype (FixedBytes 32)
  let U := PMF.uniformOfFintype (Fin n → Row s)
  let cost (A : Option (PublicMatrix s)) : ℝ := A.elim 0 fun M =>
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) M).toReal
    2 * (4 * qH * √δ + (815 * i.val + (1 + j.val)) * δ)
  let test (w : Bool) (H : Xofs) (seed : FixedBytes 32) : Game :=
    match H.keyGen s seed with
    | some keys => U.bind fun rows => C.commitmentTrialGame s H keys i j (List.ofFn rows) w
    | _ => PMF.pure false
  have point H seed : |prob (test true H seed) - prob (test false H seed)| ≤
      cost (generatedMatrix s H seed) := by
    cases kg : H.keyGen s seed with
    | none => simp [test, kg, generatedMatrix, cost, prob]
    | some keys =>
      obtain ⟨rho, pair, mat, pk, sk, _⟩ := privateKey_of_keyGen kg
      simp only [test, kg, generatedMatrix, Option.bind_eq_bind, Option.bind_some, pk,
        take_encodePublic, mat]
      apply abs_common_bind
      intro rs
      have h := C.abs_commitmentTrialGame_write_sub_read_le s H keys i j (List.ofFn rs) hash
      simpa only [Game.coe_succProbability, prob, sk, mat, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.getD_some, cost, Option.elim_some] using h
  rw [show orig = Game.succProbability (C.expansionTrialGame s base a b i j false) from
    congrArg Game.succProbability (C.expansionTrialGame_read_eq_freshExpansionGame
      s base ha hb calls i j).symm]
  simp only [win, Game.coe_succProbability, expansionTrialGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  change |prob ((base.uniformPrefixes a b).bind fun H => law.bind (test true H)) -
    prob ((base.uniformPrefixes a b).bind fun H => law.bind (test false H))| ≤
    ∑ A, (matrices A).toReal * cost A
  exact seeded_gap_le s base a b test cost point

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
