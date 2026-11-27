/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.PPT.Link
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# Strict polynomial time for UC machine composition

In `A.comp D`, the caller `A` uses `D` for every imported query. The two machines retain
their states between activations. Each time the composite receives an external request, the
caller's PPT certificate can run at an internal prefix bound large enough for every reply it
receives from `D`. The callee retains the external prefix bound for its own imported queries.

`PPTCertificate.compOfReachable` constructs the joint certificate given an efficiently
computable cap on the internal replies reachable from each decoded pre-state and an
additive bound on the growth of the joint encoded state.

`PPTCertificate.compOfBoundedState` derives the joint-state bound from a public polynomial
capacity for the callee. A callee at or below capacity may allocate up to that capacity.
An already larger state may persist or shrink. Arbitrarily many internal calls then cost
at most one capacity allowance in persistent state growth per external activation.
`PPTCertificate.isPPT_comp_of_replyBounded_boundedState` applies this rule with a
machine-wide reply bound. A non-growing callee has capacity zero in this rule, including
the stateless relay in `Machine.IsPPTFamily.comp_of_replyBounded_subsingleton`.
`Machine.IsReplyBounded.comp` transports global bounds on both machines' replies to
the exported replies of the composite.
These are original library constructions for strict PPT.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Cslib.Probability Turing.MultiTapeTM

/-- The external parameter, channel, request and packed pre-activation state. -/
private abbrev Call (n : ℕ) (ch : Type) := PPTParam n × (ch × List Bool) × List Bool

variable {n : ℕ} {ιI ιJ ιE : Type} {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type}

private abbrev joined (A : ℕ → Finset (Fin n) → Machine J E)
    (D : ℕ → Finset (Fin n) → Machine I J) :=
  fun κ C => (A κ C).comp (D κ C)

/-- Frame the caller's state followed by the callee's state. Each decoder is total. -/
@[expose] def StateCodec.comp {A : ℕ → Finset (Fin n) → Machine J E}
    {D : ℕ → Finset (Fin n) → Machine I J} (ca : StateCodec A) (cd : StateCodec D) :
    StateCodec (fun κ C => (A κ C).comp (D κ C)) := fun κ C => {
  enc := encPair (ca κ C).enc (cd κ C).enc
  decode := fun w => ((ca κ C).decode (unframe w), (cd κ C).decode (dropFrame w))
  decode_enc := fun ⟨a, d⟩ => by
    change ((ca κ C).decode (unframe (encPair _ _ (a, d))),
      (cd κ C).decode (dropFrame (encPair _ _ (a, d)))) = (a, d)
    simp [unframe_frame_append, dropFrame_frame_append, (ca κ C).decode_enc, (cd κ C).decode_enc] }

variable {A : ℕ → Finset (Fin n) → Machine J E} {D : ℕ → Finset (Fin n) → Machine I J}

private noncomputable abbrev callEnc (n : ℕ) {ι : Type} {Q : ι → Type} (iE : WordInterface Q) :=
  encHandlerCall (encPPTParam n) (encFinite iE.Channel) encBits

/-- All supported internal replies fit when running this caller from the two decoded
states, with the original imported prefix bound and an arbitrary external oracle. -/
private def Fits (iI : WordInterface I) (iJ : WordInterface J) (iE : WordInterface E)
    (ca : StateCodec A) (cd : StateCodec D) (cap : Call n iE.Channel → ℕ) : Prop :=
  ∀ (x : Call n iE.Channel) (σ : Type)
    (o : iI.Channel × List Bool → StateT σ PMF (List Bool)) (t : σ),
    let p := x.1
    let s := (StateCodec.comp ca cd p.secParam p.corrupted).decode x.2.2
    let q := iE.decodeQuery x.2.1.1 x.2.1.2
    RepliesFitOn (D p.secParam p.corrupted) iI iJ p.replyBound (cap x) o
      (((A p.secParam p.corrupted).handle q).run s.1) s.2 t

private def pack (p : List Bool × List Bool) : List Bool := encPair encBits encBits p

private theorem pack_poly : ComputableInPolyTime pack (encPair encBits encBits) encBits :=
  ComputableInPolyTime.of_eq fun _ => rfl

variable {iI : WordInterface I} {iJ : WordInterface J} {iE : WordInterface E}

private theorem paired_init (a : PPTCertificate A iJ iE) (d : PPTCertificate D iI iJ) :
    IsPPTOn (encPPTParam n) encBits (fun p =>
      (StateCodec.comp a.codec d.codec p.secParam p.corrupted).enc <$>
        (joined A D p.secParam p.corrupted).init) := by
  let e := encPPTParam n
  let aInit := fun x : PPTParam n × List Bool =>
    (a.codec x.1.secParam x.1.corrupted).enc <$> (A x.1.secParam x.1.corrupted).init
  have ha : IsPPTOn (encPair e encBits) encBits aInit :=
    a.init.preprocess (ComputableInPolyTime.fst e encBits)
  have hpack : ComputableInPolyTime
      (fun x : (PPTParam n × List Bool) × List Bool => pack (x.2, x.1.2))
      (encPair (encPair e encBits) encBits) encBits :=
    pack_poly.comp (by fun_prop)
  have hstep : IsPPTOn (encPair e encBits) encBits
      (fun x : PPTParam n × List Bool => (fun w => pack (w, x.2)) <$> aInit x) :=
    @IsPPTOn.map_with (PPTParam n × List Bool) (List Bool) (List Bool)
      (encPair e encBits) encBits encBits aInit (fun x w => pack (w, x.2)) ha hpack
  have hj := @IsPPTOn.bind_with (PPTParam n) (List Bool) (List Bool) e encBits encBits
    (fun p => (d.codec p.secParam p.corrupted).enc <$> (D p.secParam p.corrupted).init)
    (fun p w => (fun u => pack (u, w)) <$> aInit (p, w)) d.init hstep
  refine hj.congr fun p => ?_
  simp only [aInit, joined, Machine.comp, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.bind_map, PMF.map_bind, PMF.map_comp, PMF.pure_map,
    Function.comp_def, StateCodec.comp, pack]
  rfl

private theorem paired_norm (a : PPTCertificate A iJ iE) (d : PPTCertificate D iI iJ) :
    ComputableInPolyTime (fun x : PPTParam n × List Bool =>
      let c := StateCodec.comp a.codec d.codec x.1.secParam x.1.corrupted
      c.enc (c.decode x.2)) (encPair (encPPTParam n) encBits) encBits := by
  let e := encPPTParam n
  have hp := ComputableInPolyTime.fst e encBits
  have hw := ComputableInPolyTime.snd e encBits
  exact pack_poly.comp ((a.normalize.comp (hp.prod (ComputableInPolyTime.unframe.comp hw))).prod
    (d.normalize.comp (hp.prod (ComputableInPolyTime.dropFrame.comp hw))))

private abbrev withCap (p : PPTParam n) (b : ℕ) : PPTParam n := ⟨p.secParam, b, p.corrupted⟩

private def initialWord (cd : StateCodec D) (x : Call n iE.Channel) : List Bool :=
  let c := cd x.1.secParam x.1.corrupted
  c.enc (c.decode (dropFrame x.2.2))

/-- The caller uses the internal cap. The callee keeps the original prefix bound for
its own imported oracle. Its initializer here recovers the supplied encoded state. -/
private def wordSimulation (iI : WordInterface I) (iJ : WordInterface J) (iE : WordInterface E)
    (ca : StateCodec A) (cd : StateCodec D) (cap : Call n iE.Channel → ℕ)
    (x : Call n iE.Channel) : WordOracleComp iI.Channel ((List Bool × List Bool) × List Bool) :=
  (OracleComp.interpret (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (wordHandle D iI iJ cd x.1))
    (wordHandle A iJ iE ca (withCap x.1 (cap x)) x.2.1 (unframe x.2.2))).run
      (initialWord (iE := iE) cd x)

private theorem simulation_poly (a : PPTCertificate A iJ iE) (d : PPTCertificate D iI iJ)
    (cap : Call n iE.Channel → ℕ) (hc : ComputableInPolyTime cap (callEnc n iE) encUnary) :
    IsOraclePPTOn (callEnc n iE) (encPair (encPair encBits encBits) encBits)
      (wordSimulation iI iJ iE a.codec d.codec cap) := by
  let W := callEnc n iE
  let P := encPPTParam n
  let prepare := fun x : Call n iE.Channel =>
    (withCap x.1 (cap x), x.2.1, unframe x.2.2)
  have hp : ComputableInPolyTime (fun x : Call n iE.Channel => x.1) W P := by
    unfold W P callEnc encHandlerCall; fun_prop
  have hw : ComputableInPolyTime (fun x : Call n iE.Channel => x.2.2) W encBits := by
    unfold W callEnc encHandlerCall; fun_prop
  have hprep : ComputableInPolyTime prepare W (callEnc n iE) := by
    unfold prepare withCap W P callEnc encHandlerCall at *
    fun_prop
  have hinit := d.normalize.comp (hp.prod (ComputableInPolyTime.dropFrame.comp hw))
  have hhandler := d.handle.preprocess
    ((hp.comp (ComputableInPolyTime.fst W
      (encPair (encPair (encFinite iJ.Channel) encBits) encBits))).prod
      (ComputableInPolyTime.snd _ _))
  have hg := d.growth_poly.comp
    ((hp.comp (ComputableInPolyTime.fst W encBits)).prod
      (ComputableInPolyTime.snd _ _)).polyBounded_length
  exact IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth
    (Operation := iJ.Channel) (External := iI.Channel) (operationEncoding := encFinite iJ.Channel)
    (program := fun y : Call n iE.Channel => wordHandle A iJ iE a.codec y.1 y.2.1 y.2.2)
    (handler := fun x => wordHandle D iI iJ d.codec x.1)
    a.handle hprep hhandler hinit
    (fun x s => s ∈ Set.range (d.codec x.1.secParam x.1.corrupted).enc)
    (fun x => ⟨_, rfl⟩) hg (fun x req s hinv r hr => d.preserve_wordHandle x.1 req s hinv r hr)

private def finish (v : (List Bool × List Bool) × List Bool) : List Bool × List Bool :=
  (v.1.1, pack (v.1.2, v.2))

private theorem finish_poly :
    ComputableInPolyTime finish (encPair (encPair encBits encBits) encBits)
      (encPair encBits encBits) :=
  (by fun_prop : ComputableInPolyTime (fun v : (List Bool × List Bool) × List Bool => v.1.1)
     (encPair (encPair encBits encBits) encBits) encBits).prod (pack_poly.comp (by fun_prop))

/-- Exact one-activation time bound. The coupling carries both successor states,
the reply and the external oracle's successor state. -/
private theorem link_handle (a : PPTCertificate A iJ iE) (d : PPTCertificate D iI iJ)
    (cap : Call n iE.Channel → ℕ) (hc : ComputableInPolyTime cap (callEnc n iE) encUnary)
    (fits : Fits iI iJ iE a.codec d.codec cap) :
    IsOraclePPTOn (callEnc n iE) (encPair encBits encBits) (fun x : Call n iE.Channel =>
      wordHandle (joined A D) iI iE (StateCodec.comp a.codec d.codec) x.1 x.2.1 x.2.2) := by
  refine ((simulation_poly a d cap hc).map finish_poly).congr fun x σ o t => ?_
  let p := x.1
  let q := iE.decodeQuery x.2.1.1 x.2.1.2
  let sa := (a.codec p.secParam p.corrupted).decode (unframe x.2.2)
  let sd := (d.codec p.secParam p.corrupted).decode (dropFrame x.2.2)
  let prog := ((A p.secParam p.corrupted).handle q).run sa
  have hstep := runWith_wordHandle_lowerWith_eq_runWith_lowerWith_runFrom_of_repliesFit
    D iI iJ d.codec p (cap x) prog o sd t (fits x σ o t)
  simp only [wordSimulation, wordHandle, OracleComp.interpret_map, ProbOracleComp.runWith_map,
    withCap, initialWord]
  erw [StateT.run_map, ProbOracleComp.runWith_map, hstep]
  have ht : ((joined A D p.secParam p.corrupted).handle q).run
      ((StateCodec.comp a.codec d.codec p.secParam p.corrupted).decode x.2.2) =
      Equiv.prodAssoc _ _ _ <$> (D p.secParam p.corrupted).runFrom prog sd := rfl
  erw [ht]
  simp only [ProbOracleComp.lowerWith]
  erw [ProbOracleComp.simulate_map, ProbOracleComp.runWith_map]
  simp only [PMF.map_comp]
  rfl

/-- A strict PPT certificate for the pointwise composite. For each external request and
encoded pre-state, `cap` bounds the replies supported along the caller's interaction with
the callee. The joint state must grow additively in the parameter and external request. -/
def PPTCertificate.compOfReachable (a : PPTCertificate A iJ iE)
    (d : PPTCertificate D iI iJ)
    (cap : PPTParam n × (iE.Channel × List Bool) × List Bool → ℕ)
    (hc : ComputableInPolyTime cap (encHandlerCall (encPPTParam n) (encFinite iE.Channel) encBits)
      encUnary)
    (fits : ∀ (x : PPTParam n × (iE.Channel × List Bool) × List Bool) (σ : Type)
      (o : iI.Channel × List Bool → StateT σ PMF (List Bool)) (t : σ),
      let (p, (channel, request), stateWord) := x
      let s := (a.codec.comp d.codec p.secParam p.corrupted).decode stateWord
      let q := iE.decodeQuery channel request
      RepliesFitOn (D p.secParam p.corrupted) iI iJ p.replyBound (cap x) o
        (((A p.secParam p.corrupted).handle q).run s.1) s.2 t)
    (growth : PPTParam n → List Bool → ℕ)
    (hg : PolyBounded (fun x : PPTParam n × List Bool => (encPair (encPPTParam n) encBits x).length)
      (fun x => growth x.1 x.2))
    (preserves : ∀ (p : PPTParam n) (req : iE.Channel × List Bool)
      (s : (A p.secParam p.corrupted).State × (D p.secParam p.corrupted).State),
      let codec := a.codec.comp d.codec
      let w := (codec p.secParam p.corrupted).enc s
      ∀ r ∈ OracleComp.support
          (wordHandle (fun κ C => (A κ C).comp (D κ C)) iI iE codec p req w),
        r.2.length ≤ w.length + growth p req.2) :
    PPTCertificate (fun κ C => (A κ C).comp (D κ C)) iI iE where
  codec := StateCodec.comp a.codec d.codec
  init := paired_init a d
  normalize := paired_norm a d
  handle := link_handle a d cap hc fits
  growth := growth
  growth_poly := hg
  preserve := preserves

/-- A received reply that fits the prefix is among the outcomes of the isolated
caller's lowered query. The word oracle can supply that very encoding. -/
private theorem supported_reply (iJ : WordInterface J) (q : ιJ) (r : J q) (L : ℕ)
    (hr : (iJ.reply q r).length ≤ L) :
    r ∈ OracleComp.support (ProbOracleComp.lowerWith iJ L (ProbOracleComp.query q)) := by
  simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery]
  refine OracleComp.mem_supportWith_map_iff.mpr ⟨iJ.reply q r,
    OracleComp.mem_supportWith_map_iff.mpr ⟨iJ.reply q r, ?_, List.take_of_length_le hr⟩,
    iJ.decodeReply_reply q r⟩
  simp [ProbOracleComp.query]

/-- The projected caller result is supported at the internal prefix. Any measure of
callee state that is nonincreasing on a single step is nonincreasing across the run. -/
private theorem runFrom_bounds {α : Type} (m : Machine I J)
    (iI : WordInterface I) (iJ : WordInterface J) (b L : ℕ) (size : m.State → ℕ)
    (step : ∀ q s (y : J q × m.State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI b ((m.handle q).run s)) →
      (iJ.reply q y.1).length ≤ L ∧ size y.2 ≤ size s)
    (prog : ProbOracleComp J α) (s : m.State) (x : α × m.State)
    (hx : x ∈ OracleComp.support (ProbOracleComp.lowerWith iI b (m.runFrom prog s))) :
    x.1 ∈ OracleComp.support (ProbOracleComp.lowerWith iJ L prog) ∧ size x.2 ≤ size s := by
  induction prog generalizing s x with
  | pure a =>
    change x ∈ OracleComp.support (pure (a, s) : WordOracleComp iI.Channel _) at hx
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
    exact ⟨by simp [ProbOracleComp.lowerWith, OracleComp.support], le_rfl⟩
  | liftBind op cont ih =>
    cases op with
    | inl k =>
      change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI b
        (m.runFrom (ProbOracleComp.sample (ProbComp.unifFin k) >>= cont) s)) at hx
      rw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left] at hx
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
        ProbOracleComp.simulate_sample] at hx
      obtain ⟨u, _, hu⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
      obtain ⟨hu', bound⟩ := ih u s x hu
      refine ⟨?_, bound⟩
      change x.1 ∈ OracleComp.support (ProbOracleComp.lowerWith iJ L
        (ProbOracleComp.sample (ProbComp.unifFin k) >>= cont))
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
        ProbOracleComp.simulate_sample]
      exact OracleComp.mem_supportWith_bind_iff.mpr ⟨u, by simp [PMF.uniformOfFintype_apply], hu'⟩
    | inr q =>
      change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI b
        (m.runFrom (ProbOracleComp.query q >>= cont) s)) at hx
      rw [Machine.runFrom_bind, Machine.runFrom_query] at hx
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind] at hx
      obtain ⟨y, hy, hx'⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
      obtain ⟨hq, hs⟩ := step q s y hy
      obtain ⟨hout, hend⟩ := ih y.1 y.2 x hx'
      refine ⟨?_, hend.trans hs⟩
      change x.1 ∈ OracleComp.support
        (ProbOracleComp.lowerWith iJ L (ProbOracleComp.query q >>= cont))
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind]
      exact OracleComp.mem_supportWith_bind_iff.mpr ⟨y.1, supported_reply iJ q y.1 L hq, hout⟩

section BoundedState

variable (a : PPTCertificate A iJ iE)
    (d : PPTCertificate D iI iJ) (L : PPTParam n → ℕ)
    (hL : ComputableInPolyTime L (encPPTParam n) encUnary)
    (B : PPTParam n → ℕ) (hB : PolyBounded (fun p => (encPPTParam n p).length) B)
    (returned : ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((D p.secParam p.corrupted).handle q).run s)) → (iJ.reply q y.1).length ≤ L p)
    (boundedState : ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((D p.secParam p.corrupted).handle q).run s)) →
      ((d.codec p.secParam p.corrupted).enc y.2).length ≤
        max (B p) ((d.codec p.secParam p.corrupted).enc s).length)

/-- Construct a certificate with the paired state codec. The caller runs at reply cap `L p`
and the callee runs at the external prefix. At fixed parameters `p`, the callee's encoded
state after any number of internal calls has length at most the larger of `B p` and its
initial length for this activation. Only the reply cap must be computed by the interpreter. -/
def PPTCertificate.compOfBoundedState :
    PPTCertificate (fun κ C => (A κ C).comp (D κ C)) iI iE := by
  let inner := fun p : PPTParam n => (⟨p.secParam, L p, p.corrupted⟩ : PPTParam n)
  have inner_poly : ComputableInPolyTime inner (encPPTParam n) (encPPTParam n) := by
    unfold inner; fun_prop
  have prep : ComputableInPolyTime (fun x : PPTParam n × List Bool => (inner x.1, x.2))
      (encPair (encPPTParam n) encBits) (encPair (encPPTParam n) encBits) := by fun_prop
  let growth := fun p w => 2 * a.growth (inner p) w + B p
  refine PPTCertificate.compOfReachable a d (fun x => L x.1) (hL.comp ?_) ?_ growth
    (((PolyBounded.const 2).mul (a.growth_poly.comp prep.polyBounded_length)).add
      (hB.comp (ComputableInPolyTime.fst (encPPTParam n) encBits).polyBounded_length)) ?_
  · unfold encHandlerCall; fun_prop
  · intro x σ o t
    apply RepliesFitOn.of_global
    exact returned x.1
  · intro p req st
    dsimp only
    intro r hr
    let q := iE.decodeQuery req.1 req.2
    simp only [wordHandle, Machine.comp, StateT.run,
      ProbOracleComp.lowerWith, ProbOracleComp.simulate_map] at hr
    obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
    obtain ⟨v, hv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hy
    erw [WordCodec.decode_enc] at hv
    have leaf := runFrom_bounds (D p.secParam p.corrupted) iI iJ p.replyBound (L p)
      (fun s => max (B p) ((d.codec p.secParam p.corrupted).enc s).length)
      (fun j s y hy => ⟨returned p j s y hy, max_le (le_max_left _ _) (boundedState p j s y hy)⟩)
      (((A p.secParam p.corrupted).handle q).run st.1) st.2 v hv
    have caller := a.preserve (inner p) req st.1
        (iE.reply q v.1.1, (a.codec p.secParam p.corrupted).enc v.1.2) (by
      unfold wordHandle
      rw [WordCodec.decode_enc]
      exact OracleComp.mem_supportWith_map_iff.mpr ⟨v.1, leaf.1, rfl⟩)
    change ((a.codec p.secParam p.corrupted).enc v.1.2).length ≤
      ((a.codec p.secParam p.corrupted).enc st.1).length + a.growth (inner p) req.2 at caller
    have callee : max (B p) ((d.codec p.secParam p.corrupted).enc v.2).length ≤
        max (B p) ((d.codec p.secParam p.corrupted).enc st.2).length := leaf.2
    change (encPair (a.codec p.secParam p.corrupted).enc (d.codec p.secParam p.corrupted).enc
      (v.1.2, v.2)).length ≤ (encPair (a.codec p.secParam p.corrupted).enc
      (d.codec p.secParam p.corrupted).enc (st.1, st.2)).length + growth p req.2
    simp only [length_encPair, growth]
    omega

/-- The composed certificate uses the paired encodings of the supplied certificates. -/
@[simp] theorem PPTCertificate.compOfBoundedState_codec :
    (a.compOfBoundedState d L hL B hB returned boundedState).codec = a.codec.comp d.codec := (rfl)

end BoundedState

private theorem exists_computable_replyCap (bounded : Machine.IsReplyBounded D iI iJ) :
    ∃ L : PPTParam n → ℕ, ComputableInPolyTime L (encPPTParam n) encUnary ∧
      ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
        y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
          (((D p.secParam p.corrupted).handle q).run s)) → (iJ.reply q y.1).length ≤ L p := by
  obtain ⟨bound, poly, returned⟩ := bounded
  obtain ⟨c, k, majorizes⟩ := poly.exists_le
  refine ⟨fun p => c * ((encPPTParam n p).length + 1) ^ k, ?_,
    fun p q s y hy => (returned p q s y hy).trans (majorizes p)⟩
  have clock : ComputableInPolyTime (fun l : ℕ => c * (l + 1) ^ k) encUnary encUnary := by
    fun_prop
  exact clock.comp (ComputableInPolyTime.encoding_length (encPPTParam n))

/-- A global polynomial bound on each side of a link bounds the caller's exported replies
when the two machines run together. The caller uses a prefix that fits every internal reply. -/
theorem Machine.IsReplyBounded.comp (ha : Machine.IsReplyBounded A iJ iE)
    (hd : Machine.IsReplyBounded D iI iJ) :
    Machine.IsReplyBounded (fun κ C => (A κ C).comp (D κ C)) iI iE := by
  obtain ⟨bound, hbound, caller⟩ := ha
  obtain ⟨L, hL, callee⟩ := exists_computable_replyCap hd
  let inner := fun p : PPTParam n => (⟨p.secParam, L p, p.corrupted⟩ : PPTParam n)
  have inner_poly : ComputableInPolyTime inner (encPPTParam n) (encPPTParam n) := by
    unfold inner; fun_prop
  refine ⟨fun p => bound (inner p), hbound.comp inner_poly.polyBounded_length, ?_⟩
  intro p q s x hx
  simp only [Machine.comp, StateT.run, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_map] at hx
  obtain ⟨v, hv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
  exact caller (inner p) q s.1 v.1 (runFrom_bounds (D p.secParam p.corrupted) iI iJ
    p.replyBound (L p) (fun _ => 0) (fun j t y hy => ⟨callee p j t y hy, le_rfl⟩)
    (((A p.secParam p.corrupted).handle q).run s.1) s.2 v hv).1

/-- A machine-wide reply bound and polynomial state capacity suffice for every certified caller.
A computable unary polynomial majorizes the reply bound supplied by `Machine.IsReplyBounded`. -/
theorem PPTCertificate.isPPT_comp_of_replyBounded_boundedState (a : PPTCertificate A iJ iE)
    (d : PPTCertificate D iI iJ) (bounded : Machine.IsReplyBounded D iI iJ)
    (B : PPTParam n → ℕ) (hB : PolyBounded (fun p => (encPPTParam n p).length) B)
    (boundedState : ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((D p.secParam p.corrupted).handle q).run s)) →
      ((d.codec p.secParam p.corrupted).enc y.2).length ≤
        max (B p) ((d.codec p.secParam p.corrupted).enc s).length) :
    Machine.IsPPTFamily (fun κ C => (A κ C).comp (D κ C)) iI iE := by
  obtain ⟨L, hL, returned⟩ := exists_computable_replyCap bounded
  exact ⟨a.compOfBoundedState d L hL B hB returned boundedState⟩

/-- A non-growing callee needs no state allowance. The caller may adapt its internal
requests to its old state and the replies it receives. -/
theorem PPTCertificate.isPPT_comp_of_computableCap_nongrowing (a : PPTCertificate A iJ iE)
    (d : PPTCertificate D iI iJ) (L : PPTParam n → ℕ)
    (hL : ComputableInPolyTime L (encPPTParam n) encUnary)
    (returned : ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((D p.secParam p.corrupted).handle q).run s)) → (iJ.reply q y.1).length ≤ L p)
    (nongrowing : ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((D p.secParam p.corrupted).handle q).run s)) →
      ((d.codec p.secParam p.corrupted).enc y.2).length ≤
        ((d.codec p.secParam p.corrupted).enc s).length) :
    Machine.IsPPTFamily (fun κ C => (A κ C).comp (D κ C)) iI iE :=
  ⟨a.compOfBoundedState d L hL (fun _ => 0) (PolyBounded.const 0) returned
    (fun p q s y hy => (nongrowing p q s y hy).trans (le_max_right _ _))⟩

/-- With a global reply bound, a non-growing state satisfies the capacity rule at zero. -/
theorem PPTCertificate.isPPT_comp_of_replyBounded_nongrowing (a : PPTCertificate A iJ iE)
    (d : PPTCertificate D iI iJ) (bounded : Machine.IsReplyBounded D iI iJ)
    (nongrowing : ∀ (p : PPTParam n) q s (y : J q × (D p.secParam p.corrupted).State),
      y ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((D p.secParam p.corrupted).handle q).run s)) →
      ((d.codec p.secParam p.corrupted).enc y.2).length ≤
        ((d.codec p.secParam p.corrupted).enc s).length) :
    Machine.IsPPTFamily (fun κ C => (A κ C).comp (D κ C)) iI iE :=
  a.isPPT_comp_of_replyBounded_boundedState d bounded (fun _ => 0) (PolyBounded.const 0)
    (fun p q s y hy => (nongrowing p q s y hy).trans (le_max_right _ _))

/-- A relay with subsingleton state satisfies the size condition for every codec,
even when its codec depends on the security parameter or corruption set. -/
theorem Machine.IsPPTFamily.comp_of_replyBounded_subsingleton (ha : Machine.IsPPTFamily A iJ iE)
    (hd : Machine.IsPPTFamily D iI iJ) (bounded : Machine.IsReplyBounded D iI iJ)
    (one : ∀ κ C, Subsingleton (D κ C).State) :
    Machine.IsPPTFamily (fun κ C => (A κ C).comp (D κ C)) iI iE := by
  obtain ⟨a⟩ := ha
  obtain ⟨d⟩ := hd
  apply a.isPPT_comp_of_replyBounded_nongrowing d bounded
  intro p q s y _
  rw [(one p.secParam p.corrupted).elim y.2 s]

end Cslib.Crypto.Protocols.UC
