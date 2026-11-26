/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PriorCommitmentRefresh
-- Reads private `Boundary`, `Mask`, `Register`, `abs_common_bind`, and `commitmentTrialGame`.
import all CslibFrontier.Crypto.Computational.MLDSA.PriorCommitmentRefresh
import CslibFrontier.Crypto.Computational.MLDSA.RandomXofMask

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
  have law : (PMF.uniformOfFintype _).map (rowMasks s) =
      PMF.iid (signingMaskLaw s.params (by cases s <;> decide)) 814 := iid_maskFromRow s
  let rerun (v : Fin 814 → Fin s.params.ℓ → Poly) :=
    (signingMaskLaw s.params (by cases s <;> decide)).bind fun y => score (Function.update v j y)
  change (PMF.bind _ (rerun ∘ rowMasks s)) = PMF.bind _ (score ∘ rowMasks s)
  rw [← PMF.bind_map, ← PMF.bind_map, law]
  simpa only [rerun, PMF.bind_bind, PMF.pure_bind] using
    congrArg (fun p => p.bind score)
      (PMF.iid_bind_update (signingMaskLaw s.params (by cases s <;> decide)) j)

-- Separate the tests before the selected nonce. A terminal error prevents further attempts.
private theorem split_firstAccepted (step : ℕ) (tryAt : ℕ → Option (Option (List Byte)))
    (pre post start : ℕ) :
    firstAccepted step tryAt (pre + post) start =
      match Fin.findSome? (fun i : Fin pre => terminalReply (tryAt (start + i.val * step))) with
      | some r => r
      | none => firstAccepted step tryAt post (start + pre * step) := by
  unfold firstAccepted
  induction pre generalizing start with
  | zero => simp [Fin.findSome?]
  | succ pre ih =>
    rw [Nat.succ_add, Fin.findSome?_succ]
    have next (i : Fin pre) : start + i.succ.val * step = start + step + i.val * step := by
      rw [Fin.val_succ, Nat.succ_mul]; omega
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, next]
    rcases h : tryAt start with _ | (_ | sig)
    · simp [signingRetryLoop, id_bind_eq, id_pure_eq, terminalReply, h]
    · have eq : start + (pre + 1) * step = start + step + pre * step := by ring
      simpa only [signingRetryLoop, id_bind_eq, id_pure_eq, id_eq, h, terminalReply,
        Option.map_none, Option.none_or, eq] using ih (start + step)
    · simp [signingRetryLoop, id_bind_eq, id_pure_eq, terminalReply, h]


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
    rcases eq_or_ne i j with rfl | h
    · simp [cutAt]
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
    rw [Nat.one_add, firstAccepted, signingRetryLoop]
    have mid : attempt cutAt = G.attemptWithMask s sk A m y := by simp [attempt]
    simp only [id_bind_eq, id_pure_eq, id_eq, mid]
    rcases h : G.attemptWithMask s sk A m y with _ | (_ | sig)
    · rfl
    · change firstAccepted step attempt (813 - j.val) (cutAt + step) = _
      rw [firstAccepted_eq_terminal, firstAccepted_eq_terminal, Nat.succ_mul j.val step]
      refine congrArg Option.join (congrArg Fin.findSome? (funext fun i => ?_))
      have ne : cutAt + step + i.val * step ≠ cutAt := by lia
      simp [attempt, Function.update_of_ne ne, raw, step, cutAt]
    · rfl

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
  · have bits : List.ofFn (BitString.ofList 512
        (G.representativeFromTr sk.tr (formatMessage q.message q.context))) = m :=
      BitString.ofFn_ofList (by
        simp only [Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, G.h256.length_read])
    simp only [afterTrial, nativePreparation, preparedPrefix, rowAttempt, reply, over, ↓reduceIte,
      List.headD_cons, List.tail_cons, find_updated]
    cases (List.finRange j.val).findSome? (fun i => terminalReply
      (G.attemptWithMask s sk A m (ringVectorCoeffs (maskFromRow s r (i.val * s.params.ℓ)))))
    · simp only [bits, m]; rfl
    · rfl

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

-- Past native replies depend only on the rows they have consumed. At a signing boundary all
-- those rows have been spent. Early termination leaves the unused rows before the suffix.
private theorem prefixRun_split (C : QuantumSigningForger) (s : Level) (G : Xofs) (keys : KeyPair)
    (prog : C.Program Forgery) (d : C.Device) (log : List Forgery) (pre suffix : List (Row s))
    (resume : Resume C s) :
    C.prefixRun s G keys prog pre.length d log (pre ++ suffix) resume =
      C.prefixRun s G keys prog pre.length d log pre (fun x st l t =>
        resume x st l (match x with | .finished _ => t ++ suffix | .signing .. => suffix)) := by
  induction prog generalizing d log pre with
  | pure f =>
    simp only [prefixRun, prefixInteraction, cut, PFunctor.FreeM.pure_eq_pure,
      OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.pure_bind]
  | liftBind cmd k ih =>
    have off (skip : isSigningCall cmd = false) (push : ∀ i, cut (C := C) (.liftBind cmd k) i =
        .liftBind cmd (fun b => cut (C := C) (k b) i)) :
        C.prefixRun s G keys (.liftBind cmd k) pre.length d log (pre ++ suffix) resume =
          C.prefixRun s G keys (.liftBind cmd k) pre.length d log pre (fun x st l t =>
            resume x st l (match x with | .finished _ => t ++ suffix | .signing .. => suffix)) := by
      simp only [prefixRun_step _ _ _ _ _ _ _ (push _), OracleComp.withSampleListWhen, skip,
        Bool.false_eq_true, ↓reduceIte, StateT.run, PMF.bind_map, Function.comp_def]
      exact congrArg (PMF.bind _) (funext fun ⟨r, st, l⟩ => ih r st l pre)
    rcases cmd with coin | op | q
    · exact off rfl fun _ => rfl
    · exact off rfl fun _ => rfl
    · cases pre with
      | nil =>
        simp only [List.length_nil, List.nil_append, prefixRun, prefixInteraction, cut,
          PFunctor.FreeM.pure_eq_pure, OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure,
          PMF.pure_bind]
      | cons r pre =>
        have push : cut (C := C) (.liftBind (.inr (.inr q)) k) (pre.length + 1) =
            .liftBind (.inr (.inr q)) (fun b => cut (C := C) (k b) pre.length) := rfl
        simp only [List.length_cons, List.cons_append, prefixRun_step _ _ _ _ _ _ _ push,
          OracleComp.withSampleListWhen, isSigningCall, Sum.elim_inr, ↓reduceIte,
          OracleComp.withSampleList, List.headD_cons, List.tail_cons, signingCommand,
          OracleComp.sumHandler, StateT.run, pmf_norm]
        exact ih _ _ _ pre

private theorem cut_resume (C : QuantumSigningForger) (prog : C.Program Forgery) (i : ℕ) :
    (cut prog i >>= resumeProgram) = prog := by
  induction prog generalizing i with
  | pure f => rfl
  | liftBind cmd k ih =>
    rcases cmd with _ | _ | q <;> cases i
    on_goal 5 => rfl
    all_goals exact congrArg (PFunctor.FreeM.liftBind _) (funext fun r => ih r _)

private theorem prefixRun_mix {V : Type} (C : QuantumSigningForger) (s : Level)
    (G : Xofs) (keys : KeyPair) (μ : PMF V) (resume : V → Resume C s) (ref : Resume C s)
    (finish : ∀ y f d l t, resume y (.finished f) d l t = ref (.finished f) d l t)
    (sign : ∀ q k d l t, ((PMF.uniformOfFintype (Row s)).bind fun r =>
        μ.bind fun y => resume y (.signing q k) d l (r :: t)) =
      (PMF.uniformOfFintype (Row s)).bind fun r => ref (.signing q k) d l (r :: t))
    (prog : C.Program Forgery) (dev : C.Device) (log : List Forgery) (pre rows : List (Row s)) :
    let U := PMF.uniformOfFintype (Row s)
    (U.bind fun r => μ.bind fun y =>
      C.prefixRun s G keys prog pre.length dev log (pre ++ r :: rows) (resume y)) =
    U.bind fun r => C.prefixRun s G keys prog pre.length dev log (pre ++ r :: rows) ref := by
  intro U
  let prior := C.prefixInteraction s G keys prog pre.length dev log pre
  simp only [prefixRun_split]
  unfold prefixRun
  change (U.bind fun r => μ.bind fun y => prior.bind _) = U.bind fun r => prior.bind _
  simp_rw [PMF.bind_comm μ prior, PMF.bind_comm U prior]
  apply congrArg (PMF.bind prior ·)
  funext ⟨x, ⟨d, l⟩, t⟩
  cases x with
  | finished f => simp only [finish, PMF.bind_const]
  | signing q k => exact sign q k d l rows

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
  let full : Resume C s := fun x d l t =>
    C.expansionContinuation s G A keys (resumeProgram x) d l t
  have ordinary (q : SigningQuery) (k : Option (List Byte) → C.Program Forgery) (d : C.Device)
      (l : List Forgery) (r : Row s) (t : List (Row s)) :
      full (.signing q k) d l (r :: t) = C.expansionContinuation s G A keys
        (k (G.signWithExpansionRow s keys.secretKey q r)) d
        (q.logReply (G.signWithExpansionRow s keys.secretKey q r) l) t := by
    simp only [full, resumeProgram, expansionContinuation, scored_eq_measured]
    change measured _ _ (OracleComp.query (.inr (.inr q)) >>= k) _ _ _ = _
    simp only [measured_sign (C := C) (ask := q) (k := k), tapeReply, List.headD_cons,
      List.tail_cons, PMF.pure_bind]
  have ref (t : List (Row s)) : C.prefixRun s G keys prog pre.length dev log t full =
      C.expansionContinuation s G A keys prog dev log t := by
    conv_rhs => rw [← C.cut_resume prog pre.length]
    simp only [full, prefixRun, prefixInteraction, expansionContinuation, scored,
      OracleComp.run_interpret_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
  simp_rw [← ref]
  exact prefixRun_mix C s G keys μ resume full finish
    (fun q k d l t => by simpa only [ordinary] using sign q k d l t) prog dev log pre rows

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
  · exact fun _ _ _ _ _ => rfl
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
    refine List.ext_getElem (by simp) fun h h₁ h₂ => ?_
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
  refine congrArg (PMF.bind U ·) (funext fun v => ?_)
  simp only [split]
  exact same _ _ (by simp)

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
  exact uniform_tape_eq s i
    (fun t => μ.bind fun y => C.readUntil s G A keys sk prog i j C.initialDevice [] t y)
    (C.expansionContinuation s G A keys prog C.initialDevice []) fun pre rows len => by
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
  exact congrArg (PMF.bind U ·) (funext fun D => C.uniform_readUntil s _ keys _ pair.A sk
    ((Xofs.expandA_congr (K := H.withDigestRegister s D) (H := H) rfl ..).trans mat) i j)

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

-- The independent uniform register can be reinstalled in a seeded raw-stream game without
-- changing its distribution, including on inputs whose raw SHAKE domains overlap.
private theorem average_register (s : Level) (base : Xofs) {a b : ℕ}
    (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b)
    (source target : Xofs → FixedBytes 32 → Game)
    (law : ∀ H seed, source H seed = (PMF.uniformOfFintype (Register s)).bind fun D =>
      target (H.withDigestRegister s D) seed) :
    let U := PMF.uniformOfFintype (FixedBytes 32)
    ((base.uniformPrefixes a b).bind fun H => U.bind (source H)) =
      (base.uniformPrefixes a b).bind fun H => U.bind (target H) := by
  intro U
  let D := PMF.uniformOfFintype (Register s)
  have reg := congrArg (fun p : PMF (Register s × Xofs) => p.bind fun x => U.bind (target x.2))
    (base.uniformPrefixes_digestRegister s ha hb)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at reg
  rw [← reg]
  exact congrArg (PMF.bind (base.uniformPrefixes a b))
    (funext fun H => by rw [funext (law H), PMF.bind_comm U D])


/-- Reading at the selected attempt has the exact fresh-digest forgery law of the original
private-expansion signer, for every covered request and retry index. The row is sampled even
when an earlier signature, fatal error, or early termination makes the selection unreachable. -/
theorem expansionTrialGame_read_eq_freshExpansionGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b)
    (calls : C.SigningCallsLe n) (i : Fin n) (j : Fin 814) :
    C.expansionTrialGame s base a b i j false = C.freshExpansionGame s base a b := by
  rw [C.freshExpansionGame_eq_expansionContinuation s base a b calls]
  simp only [expansionTrialGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  apply average_register s base ha hb
  intro H seed
  simp only [Xofs.keyGen_withDigestRegister]
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
  refine (PMF.abs_bind_sub_le_meanAbsDiffAt _ true _ _).trans
    (Finset.sum_le_sum fun table _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  exact (PMF.abs_bind_sub_le_meanAbsDiffAt _ true _ _).trans
    (Finset.sum_le_sum fun seed _ =>
      mul_le_mul_of_nonneg_left (point _ seed) ENNReal.toReal_nonneg)

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
