/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import CslibFrontier.Computability.Probabilistic.QueryBounds
public import CslibFrontier.Crypto.Protocols.UC.PPT.Composition
public import CslibFrontierTests.Crypto.UCComputational.Primitive

/-!
# A command translator for a one-use child

The real child saves the raw setting bit. The ideal child saves its complement. Both release
the complete private word on the first authorized party input. The child translator
complements raw commands and preserves routed party inputs. Its lifted simulator also checks
the reply tags on the parent interface.
-/

public section

namespace CslibFrontierTests.Crypto.UCComputational.Relay

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

abbrev Word := List Bool

/-- Forward one translated request and project its typed response. -/
@[expose] def forward {Q R : Type} (req : Q → Q) (ans : Q → R → R) :
    Adversary 1 Q R Q R := fun _ _ => {
  State := PUnit
  init := pure PUnit.unit
  handle q s := (fun r => (ans q r,s)) <$> ProbOracleComp.query (spec := netSpec Q R) (req q) }

/-- Polynomial-time request translation and response projection certify this open relay. -/
theorem forward_ppt {Q R : Type} (port : WordPort Q R) (req : Q → Q) (ans : Q → R → R)
    (hreq : ComputableInPolyTime req port.query port.query)
    (hans : ComputableInPolyTime (fun x : Q × R => ans x.1 x.2)
      (encPair port.query port.reply) port.reply) :
    (forward req ans).IsPPT port port := by
  let T := PPTParam 1 × (Unit × Word) × Word
  let enc := encHandlerCall (encPPTParam 1) (encFinite Unit) encBits
  let read := fun x : T => port.queryDecoder.decode x.2.1.2
  have hr : ComputableInPolyTime read enc port.query := port.queryDecoder.computableInPolyTime.comp
    (by unfold enc T encHandlerCall; fun_prop)
  have bound : ComputableInPolyTime (fun x : T => x.1.replyBound) enc encUnary := by
    unfold enc T encHandlerCall; fun_prop
  have send := (IsOraclePPTOn.query_take () (hreq.comp hr).encoding_comp bound).map
    port.replyDecoder.computableInPolyTime
  have hcalc := (hans.comp ((hr.comp (ComputableInPolyTime.fst enc port.reply)).prod
    (ComputableInPolyTime.snd enc port.reply))).encoding_comp
  have impl := send.map_with (f := fun x r => (port.reply (ans (read x) r), ([] : Word)))
    (hcalc.prod (ComputableInPolyTime.const (encIn := encPair enc port.reply)
      (encOut := encBits) []))
  refine ⟨{ codec := fun _ _ => punitWordCodec
            init := (ComputableInPolyTime.const (encIn := encPPTParam 1)
               (encOut := encBits) []).isPPTOn
            handle := ?_
            normalize := ComputableInPolyTime.const (encIn := encPair (encPPTParam 1) encBits) []
            growth _ _ := 0
            growth_poly := PolyBounded.const 0
            preserve := ?_ }⟩
  · refine impl.congr fun x σ o t => ?_
    apply congrArg (fun prog => ProbOracleComp.runWith o prog t)
    simp [wordHandle, forward, punitWordCodec, StateT.run, read, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_query, WordInterface.lowerQuery, WordInterface.net, Functor.map_map]
    rfl
  · intro p rq s v hv
    obtain ⟨y,_,rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hv
    rfl

variable {I O N B J K X Y Q R : Type}

private abbrev CQ := RoutedNetQ 1 J X
private abbrev CR := RoutedNetR K Y
private abbrev OQ := RoutedNetQ 1 I (N ⊕ CQ (J := J) (X := X))
private abbrev ORsp := RoutedNetR O (B ⊕ CR (K := K) (Y := Y))

private def childQuery : OQ (I := I) (N := N) (J := J) (X := X) → Bool
  | .inr (.inr _) => true
  | _ => false

private def project (q : OQ (I := I) (N := N) (J := J) (X := X))
    (r : ORsp (O := O) (B := B) (K := K) (Y := Y)) : ORsp (O := O) (B := B) (K := K) (Y := Y) :=
  if childQuery q then .inr (.inr (subReply r)) else outerReply r

variable (party : WordPort (Fin 1 × I) (Option O)) (raw : WordPort N B)
    (sub : WordPort (Fin 1 × J) (Option K)) (subNet : WordPort X Y)
local notation "net" => Computational.outerNetPort party raw sub subNet
local notation "child" => WordPort.sum sub subNet
local notation "inner" => WordPort.sum raw child

private theorem project_ppt :
    ComputableInPolyTime (fun x => project x.1 x.2)
      (encPair (net).query (net).reply) (net).reply := by
  have tag : ComputableInPolyTime childQuery (net).query encBool := by
    let left := ComputableInPolyTime.const (encIn := party.query) (encOut := encBool) false
    let mid := ComputableInPolyTime.const (encIn := raw.query) (encOut := encBool) false
    let right := ComputableInPolyTime.const (encIn := (child).query) (encOut := encBool) true
    exact (ComputableInPolyTime.sumElim left (ComputableInPolyTime.sumElim mid right)).of_enc_eq
      (fun q => by rcases q with _ | (_ | _) <;> rfl)
  let left := ComputableInPolyTime.sumInl party.reply (inner).reply
  let right := ComputableInPolyTime.sumInr party.reply (inner).reply
  let rawTag := right.comp (ComputableInPolyTime.sumInl raw.reply (child).reply)
  let childTag := right.comp (ComputableInPolyTime.sumInr raw.reply (child).reply)
  have outer : ComputableInPolyTime outerReply (net).reply (net).reply := by
    let miss := ComputableInPolyTime.const (encIn := (child).reply)
      (encOut := (net).reply) (.inl none)
    exact (ComputableInPolyTime.sumElim left (ComputableInPolyTime.sumElim rawTag miss)).of_enc_eq
      (fun r => by rcases r with _ | (_ | _) <;> rfl)
  have subs : ComputableInPolyTime (fun r => Sum.inr (Sum.inr (subReply r)))
      (net).reply (net).reply := by
    let miss : ORsp (O := O) (B := B) (K := K) (Y := Y) := .inr (.inr (.inl none))
    let p := ComputableInPolyTime.const (encIn := party.reply) (encOut := (net).reply) miss
    let n := ComputableInPolyTime.const (encIn := raw.reply) (encOut := (net).reply) miss
    exact (ComputableInPolyTime.sumElim p (ComputableInPolyTime.sumElim n childTag)).of_enc_eq
      (fun r => by rcases r with _ | (_ | _) <;> rfl)
  exact (tag.comp (ComputableInPolyTime.fst _ _)).ite'
    (subs.comp (ComputableInPolyTime.snd _ _)) (outer.comp (ComputableInPolyTime.snd _ _))

private theorem projected_length (q : OQ (I := I) (N := N) (J := J) (X := X))
    (r : ORsp (O := O) (B := B) (K := K) (Y := Y)) :
    ((net).reply (project q r)).length ≤ ((net).reply r).length +
      ((net).reply (.inl none)).length + ((net).reply (.inr (.inr (.inl none)))).length := by
  rcases q with _ | (_ | _) <;> rcases r with _ | (_ | _)
  all_goals simp only [project, childQuery, Bool.false_eq_true, ↓reduceIte, outerReply, subReply]
  all_goals omega

private theorem composed_forward_ppt (control : WordPort Q R)
    (req : OQ (I := I) (N := N) (J := J) (X := X) → _)
    (req_ppt : ComputableInPolyTime req (net).query (net).query)
    (A : ExecAdversary 1 I O (N ⊕ RoutedNetQ 1 J X) (B ⊕ RoutedNetR K Y) Q R)
    (ha : A.IsPPT net control) : (compSim (forward req project) A).IsPPT net control := by
  have hd := forward_ppt net req project req_ppt (project_ppt party raw sub subNet)
  obtain ⟨a⟩ := ha
  obtain ⟨d⟩ := hd
  obtain ⟨c, k, hc⟩ := (net).replyDecoder.computableInPolyTime.polyBounded_length.exists_le
  let m := ((net).reply (.inl none)).length + ((net).reply (.inr (.inr (.inl none)))).length
  apply PPTCertificate.isPPT_comp_of_computableCap_nongrowing a d
    (fun p => c * (p.replyBound + 1) ^ k + m)
  · fun_prop
  · intro p q s x hx
    have run : (((forward req project) p.secParam p.corrupted).handle q).run s =
        (fun r => (project q r,s)) <$> ProbOracleComp.query (spec := netSpec _ _) (req q) := rfl
    rw [run] at hx
    erw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_map,
      ProbOracleComp.simulate_query, WordInterface.lowerQuery] at hx
    obtain ⟨_, ha, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
    obtain ⟨_, hw, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp ha
    obtain ⟨w, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hw
    let v := w.take p.replyBound
    have h := projected_length party raw sub subNet q ((net).replyDecoder.decode v)
    have hdec := hc v
    change ((net).reply ((net).replyDecoder.decode v)).length ≤ c * (v.length + 1)^k at hdec
    have hpow : (v.length + 1)^k ≤ (p.replyBound + 1)^k :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (List.length_take_le ..) _) _
    change ((net).reply (project q ((net).replyDecoder.decode v))).length ≤ _
    exact h.trans (by
      dsimp only [m]
      rw [Nat.add_assoc]
      exact Nat.add_le_add_right
        (hdec.trans (Nat.mul_le_mul_left c hpow)) _)
  · intro _ _ s y _
    rw [Subsingleton.elim (α := PUnit) y.2 s]

/-- Any efficient rewrite of a child request can be lifted through a parent and
combined with the outer adversary when the relay returns the child's reply verbatim. -/
theorem compSim_rewrite_ppt (control : WordPort Q R) (req : RoutedNetQ 1 J X → RoutedNetQ 1 J X)
    (hq : ComputableInPolyTime req (child).query (child).query)
    (A : ExecAdversary 1 I O (N ⊕ RoutedNetQ 1 J X) (B ⊕ RoutedNetR K Y) Q R)
    (ha : A.IsPPT net control) :
    (compSim (hybridSim (forward req (fun _ (r : RoutedNetR K Y) => r))) A).IsPPT net control := by
  let send : OQ (I := I) (N := N) (J := J) (X := X)
    → OQ (I := I) (N := N) (J := J) (X := X) := fun q =>
    match q with
    | .inr (.inr s) => .inr (.inr (req s))
    | q => q
  let onRaw := ComputableInPolyTime.sumInl raw.query (child).query
  let onSub := (ComputableInPolyTime.sumInr raw.query (child).query).comp hq
  have hs : ComputableInPolyTime send (net).query (net).query :=
    (ComputableInPolyTime.sumElim (ComputableInPolyTime.sumInl party.query (inner).query)
      ((ComputableInPolyTime.sumInr party.query (inner).query).comp
        (ComputableInPolyTime.sumElim onRaw onSub))).of_enc_eq
          (fun q => by rcases q with _ | (_ | _) <;> rfl)
  have lift : hybridSim (In := I) (Out := O) (NetQ := N) (NetR := B)
      (forward req (fun _ (r : RoutedNetR K Y) => r)) = forward send project := by
    funext κ C
    unfold hybridSim hybridSimMachine forward
    congr 1
    funext q s
    rcases q with _ | (_ | _) <;> rfl
  rw [lift]
  exact composed_forward_ppt party raw sub subNet control send hs A ha

end CslibFrontierTests.Crypto.UCComputational.Relay

namespace CslibFrontierTests.Crypto.UCComputational.Child

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

abbrev Word := List Bool
abbrev Result := Word × Word
abbrev Q := RoutedNetQ 1 Word Bool
abbrev R := RoutedNetR Result Bool

abbrev party := Primitive.serviceParty

@[expose] def raw : WordPort Bool Bool := ⟨encBool, Decoder.bool, encBool, Decoder.bool⟩

abbrev network := WordPort.sum party raw

@[expose] def service (inverted : Bool)
    : HybridFunctionality 1 Word Result Bool Bool Primitive.SamplePort where
  State := Bool × Bool
  init _ _ := pure (false, false)
  onInput _ w s := if s.2 then pure (none, s) else do
    let r ← ProbOracleComp.query ()
    return (some (s.1 :: w, r), (s.1, true))
  onBackdoor cmd s := pure (true, (if inverted then !cmd else cmd, s.2))

abbrev protocol (inverted : Bool) (draw : Computational.Sampler) :=
  (service inverted).close (fun κ _ => Primitive.resource (draw κ))

@[expose] def flip : Q → Q
  | .inl party => .inl party
  | .inr cmd => .inr (!cmd)

abbrev relay : ExecAdversary 1 Word Result Bool Bool Q R :=
  Relay.forward flip (fun _ r => r)

/-- Both sides initialize from the same sample law. Complementing the raw command
aligns the complete step kernels, including the spent flag and resource state. -/
theorem machine_eq (draw : Computational.Sampler) (κ : ℕ) (C : Finset (Fin 1)) :
    execMachine (protocol false draw) (dummyAdversary 1 Q R) κ C =
    execMachine (protocol true draw) relay κ C := by
  unfold execMachine Machine.comp
  congr 1
  funext q s
  rcases q with ⟨i,w⟩ | (⟨i,w⟩ | bit)
  · rfl
  · rfl
  · cases bit <;> rfl

theorem translation_exact (draw : Computational.Sampler) (C : Finset (Fin 1))
    (Z : Environment 1 Word Result Q R) (κ : ℕ) (z : Word) :
    exec (protocol false draw) (dummyAdversary 1 Q R) C Z κ z =
    exec (protocol true draw) relay C Z κ z := by
  unfold exec
  rw [machine_eq]

theorem translation_with_adversary {U V : Type} (draw : Computational.Sampler)
    (A : ExecAdversary 1 Word Result Bool Bool U V) (C : Finset (Fin 1))
    (Z : Environment 1 Word Result U V) (κ : ℕ) (z : Word) :
    (exec (protocol false draw) A C Z κ z).eval =
    (exec (protocol true draw) (compSim relay A) C Z κ z).eval := by
  rw [exec_eq_exec_dummy (protocol false draw) A, exec_compSim, translation_exact]

private abbrev readCost : ℕ ⊕ Unit → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
private abbrev routed (inv : Bool) (κ : ℕ) (C : Finset (Fin 1)) :=
  routeCorrupt C ((service inv).toMachine κ C)

private theorem input_budget {α : Type} (inv : Bool) (κ : ℕ) (C : Finset (Fin 1))
    (i : Fin 1) (w : Word) (s : Bool × Bool)
    (next : (Option Result × (Bool × Bool)) → ProbOracleComp Primitive.SamplePort α)
    (ih : ∀ r : Option Result, OracleComp.IsCostBounded readCost (next (r,s.1,true)) 0) :
    OracleComp.IsCostBounded readCost
      ((((service inv).toMachine κ C).handle (.inl (i,w))).run s >>= next)
      (if s.2 then 0 else 1) := by
  rcases s with ⟨h, _ | _⟩
  · exact .liftBind (.inr ()) _ 0 (fun r => ih (some (h :: w, r)))
  · exact ih none

/-- Any continuation, including one driven by future adversarial commands, can
read the private word at most once from a fresh state and zero times from a spent state. -/
private theorem read_budget_from {α : Type} (inv : Bool) (κ : ℕ) (C : Finset (Fin 1))
    (p : ProbOracleComp (execSpec 1 Word Result Q R) α) (s : Bool × Bool) :
    OracleComp.IsCostBounded readCost ((routed inv κ C).runFrom p s) (if s.2 then 0 else 1) := by
  induction p using OracleComp.induction generalizing s with
  | pure a => exact .pure _ _
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    rw [Machine.runFrom_bind (routed inv κ C) _ cont s, Machine.runFrom_call (routed inv κ C) q s]
    cases q with
    | inl k =>
      change OracleComp.IsCostBounded _ ((do
        let x ← (do let a ← ProbOracleComp.sample (ProbComp.unifFin k); pure (a,s))
        (routed inv κ C).runFrom (cont x.1) x.2)) _
      simp only [bind_assoc, pure_bind]
      exact .liftBind (.inl k) _ _ (fun a => ih a s)
    | inr q =>
      rcases q with ⟨i,w⟩ | ⟨i,w⟩ | c
      · simp only [Machine.handler, OracleComp.sumHandler, routed]
        erw [routeCorrupt_handle_inl]
        by_cases h : i ∈ C
        · simp only [h, ↓reduceIte]
          exact ih none s
        · simp only [h, ↓reduceIte]
          exact input_budget inv κ C i w s _ (fun r => ih r (s.1,true))
      · simp only [Machine.handler, OracleComp.sumHandler, routed]
        erw [routeCorrupt_handle_inr_inl]
        by_cases h : i ∈ C
        · simp only [h, ↓reduceIte]
          erw [bind_map_left]
          exact input_budget inv κ C i w s
            (fun x => (routed inv κ C).runFrom (cont (.inl x.1)) x.2)
            (fun r => ih (.inl r) (s.1,true))
        · simp only [h, ↓reduceIte]
          exact ih (.inl none) s
      · exact ih (.inr true) (if inv then !c else c, s.2)

theorem private_reads {α : Type} (inv : Bool) (κ : ℕ) (C : Finset (Fin 1))
    (p : ProbOracleComp (execSpec 1 Word Result Q R) α) :
    OracleComp.IsCostBounded (Sum.elim (fun _ : ℕ => 0) (fun _ : Unit => 1))
      ((routeCorrupt C ((service inv).toMachine κ C)).link p) 1 := by
  change OracleComp.IsCostBounded readCost (ProbOracleComp.sample (pure (false,false)) >>= fun s =>
    Prod.fst <$> (routed inv κ C).runFrom p s) 1
  rw [ProbOracleComp.sample_pure, pure_bind, OracleComp.isCostBounded_map_iff]
  exact read_budget_from inv κ C p (false,false)

theorem flip_ppt : ComputableInPolyTime flip network.query network.query := by
  exact (ComputableInPolyTime.sumElim (ComputableInPolyTime.sumInl party.query encBool)
    ((ComputableInPolyTime.sumInr party.query encBool).comp
      (ComputableInPolyTime.of_finite Bool.not (encIn := encBool) (encOut := encBool)))).of_enc_eq
    (fun q => by cases q <;> rfl)

theorem relay_ppt : relay.IsPPT network network :=
  Relay.forward_ppt network _ _ flip_ppt (ComputableInPolyTime.snd _ _)

/-- Request translation at the child interface preserves all the caller's state. -/
theorem compSim_child_relay_ppt {U V : Type} (control : WordPort U V)
    (A : ExecAdversary 1 Word Result Bool Bool U V) (ha : A.IsPPT network control) :
    (compSim relay A).IsPPT network control := by
  apply Machine.IsPPTFamily.comp_of_replyBounded_subsingleton ha relay_ppt _
    (fun _ _ => inferInstanceAs (Subsingleton PUnit))
  obtain ⟨L, poly, fit⟩ := Machine.isReplyBounded_id (n := 1) (WordInterface.net network)
  exact ⟨L, poly, fun p q s x hx => fit p (flip q) s x hx⟩

/-- The same cost certificate applies to the literal simulator after one parent lift. -/
theorem compSim_relay_ppt {I O N B U V : Type} (outerParty : WordPort (Fin 1 × I) (Option O))
    (outerRaw : WordPort N B) (control : WordPort U V)
    (A : ExecAdversary 1 I O (N ⊕ Q) (B ⊕ R) U V)
    (ha : A.IsPPT (Computational.outerNetPort outerParty outerRaw party raw) control) :
    (compSim (hybridSim relay) A).IsPPT
      (Computational.outerNetPort outerParty outerRaw party raw) control :=
  Relay.compSim_rewrite_ppt outerParty outerRaw party raw control flip flip_ppt A ha

private abbrev stateEncoding := encPair encBool encBool
private abbrev stateDecoder := Decoder.pair Decoder.bool Decoder.bool
private def stateCodec : WordCodec (Bool × Bool) :=
  ⟨stateEncoding, stateDecoder.decode, stateDecoder.decode_enc⟩
private abbrev iE := WordInterface.protocol party raw
private abbrev X := PPTParam 1 × (iE.Channel × Word) × Word
private noncomputable abbrev eX := encHandlerCall (encPPTParam 1) (encFinite iE.Channel) encBits
private abbrev decode (x : X) := stateDecoder.decode x.2.2
private abbrev payload (x : X) := (party.queryDecoder.decode x.2.1.2).2
private abbrev setting (inverted : Bool) (x : X) :=
  if inverted then !(raw.queryDecoder.decode x.2.1.2) else raw.queryDecoder.decode x.2.1.2

/-- Both bits survive across activations, and the encoded state always has the same length.
Only a fresh party input performs a private read. It writes the entire permitted prefix. -/
theorem service_ppt (inverted : Bool) :
    Machine.IsPPTFamily (service inverted).toMachine Primitive.sampleWire
      (WordInterface.protocol party raw) := by
  let query := fun x : X => List.take x.1.replyBound <$>
    ProbOracleComp.query (spec := fun _ : Primitive.sampleWire.Channel × Word => Word)
      ((),encUnit ())
  let send := fun (x : X) (r : Word) =>
    (party.reply (some ((decode x).1 :: payload x, r)), stateEncoding ((decode x).1, true))
  let spent := fun x : X => (party.reply none, stateEncoding (decode x))
  let set := fun x : X => (raw.reply true, stateEncoding (setting inverted x, (decode x).2))
  let branches : iE.Channel → X → WordOracleComp Primitive.sampleWire.Channel (Word × Word)
    | .inl () => fun x => if (decode x).2 then pure (spent x) else send x <$> query x
    | .inr () => fun x => pure (set x)
  have hs : ComputableInPolyTime decode eX stateEncoding :=
    stateDecoder.computableInPolyTime.comp (by unfold eX encHandlerCall; fun_prop)
  have stored := (ComputableInPolyTime.fst encBool encBool).comp hs
  have used := (ComputableInPolyTime.snd encBool encBool).comp hs
  have word : ComputableInPolyTime (fun x : X => x.2.1.2) eX encBits := by
    unfold eX encHandlerCall; fun_prop
  have hp : ComputableInPolyTime payload eX encBits :=
    ((ComputableInPolyTime.snd (encFinEnum (Fin 1)) encBits).comp
      party.queryDecoder.computableInPolyTime).comp word
  have cmd : ComputableInPolyTime (setting inverted) eX encBool := by
    exact (ComputableInPolyTime.of_finite (fun b : Bool => if inverted then !b else b)
      (encIn := encBool) (encOut := encBool)).comp (raw.queryDecoder.computableInPolyTime.comp word)
  have spentP : ComputableInPolyTime spent eX (encPair encBits encBits) :=
    (ComputableInPolyTime.const (party.reply none)).prod hs.encoding_comp
  have setP : ComputableInPolyTime set eX (encPair encBits encBits) :=
    (ComputableInPolyTime.const (raw.reply true)).prod (cmd.prod used).encoding_comp
  have tagged := ComputableInPolyTime.bitsCons stored hp
  have hreply := ((ComputableInPolyTime.optionSome (encPair encBits encBits)).comp
    ((tagged.comp (ComputableInPolyTime.fst eX encBits)).prod
      (ComputableInPolyTime.snd eX encBits))).encoding_comp
  have sendP : ComputableInPolyTime (fun x : X × Word => send x.1 x.2)
      (encPair eX encBits) (encPair encBits encBits) :=
    hreply.prod (((stored.prod (ComputableInPolyTime.const true)).encoding_comp).comp
      (ComputableInPolyTime.fst eX encBits))
  have readP : IsOraclePPTOn eX encBits query := IsOraclePPTOn.query_take () (.const _) (by
    unfold eX encHandlerCall; fun_prop)
  have channel : ComputableInPolyTime (fun x : X => x.2.1.1) eX (encFinite iE.Channel) := by
    unfold eX encHandlerCall; fun_prop
  have runP := IsOraclePPTOn.finite_cases (branch := branches) channel (by
    rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · exact IsOraclePPTOn.cond used spentP.isPPTOn.isOraclePPTOn (readP.map_with sendP)
    · exact setP.isPPTOn.isOraclePPTOn)
  refine ⟨{ codec := fun _ _ => stateCodec
            init := (ComputableInPolyTime.const (encIn := encPPTParam 1) (encOut := encBits)
              (stateEncoding (false,false))).isPPTOn
            handle := ?_
            normalize := stateDecoder.computableInPolyTime.encoding_comp.comp
              (ComputableInPolyTime.snd (encPPTParam 1) encBits)
            growth _ _ := 0
            growth_poly := PolyBounded.const 0
            preserve := ?_ }⟩
  · refine runP.congr fun x σ o t => ?_
    rcases x with ⟨p, ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, w⟩, sw⟩
    · rcases h : stateDecoder.decode sw with ⟨b,usedBit⟩
      cases usedBit <;>
        simp [wordHandle, service, HybridFunctionality.toMachine, iE, WordInterface.protocol,
          WordInterface.sum, WordInterface.net, branches, stateCodec, spent, send, payload,
          decode, query, StateT.run, ProbOracleComp.lowerWith, WordInterface.lowerQuery,
          Primitive.sampleWire, Decoder.bits, ProbOracleComp.simulate_query, Functor.map_map,
          ProbOracleComp.simulate_pure, h] <;> rfl
    · rfl
  · intro p rq s out hout
    obtain ⟨y,_,rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hout
    rcases s with ⟨(_|_), (_|_)⟩ <;> rcases y.2 with ⟨(_|_), (_|_)⟩ <;> rfl

end CslibFrontierTests.Crypto.UCComputational.Child
