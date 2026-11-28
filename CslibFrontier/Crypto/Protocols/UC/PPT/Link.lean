/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Composition
public import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind

/-!
# Strict-PPT closure of UC linking

Library infrastructure toward #6043 (no cited result): proves that linking a strict-PPT UC
environment with a strict-PPT machine family preserves `Environment.IsPPT` when a polynomial-time
computable cap covers every reply on their interaction. A machine-wide reply bound
(`Machine.IsReplyBounded`) gives such a cap for every caller.

## Modelling decisions and restrictions

* **Reply-length bound (`Machine.IsReplyBounded`).** Unlike [Canetti2020]'s cumulative import-based
  runtime budgets (Section 3.2), `PPTCertificate` truncates imported replies per activation at
  `PPTParam.replyBound` while leaving internal typed messages untruncated. `Machine.IsReplyBounded`
  requires every encoded reply exported by `M` to fit within a polynomial in the encoded activation
  parameter `PPTParam` alone (not in the request word or state). This gives a state-independent
  internal truncation cap `L(e)` at which the outer environment's `PPT` certificate is instantiated
  via `Environment.IsPPT.isOraclePPTOn_run_wordHandle`, ensuring no internal reply is truncated.
  Protocols that export payloads of unbounded environment-chosen length back to an outer caller are
  excluded from this global hypothesis. The tests in `CslibFrontierTests.Crypto.UCPPTLink`
  include a strict-PPT lifted adversary whose linked environment fails `Environment.IsPPT`.

The caller-relative theorem below also admits machine families with unbounded exports when
the specified caller reaches only replies covered by an efficiently computable cap.

## Main definitions

* `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded`: every supported exported reply word fits in
  a polynomial of `(encPPTParam n p).length`.

* `Cslib.Crypto.Protocols.UC.RepliesFitOn`: a cap on the replies along the supported
  continuations of one caller linked to one machine.
* `Cslib.Crypto.Protocols.UC.Computational.ReplyCap`: one computable cap covers the reachable
  replies for a given tester, machine family and corruption set.

## Main results

* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.isOraclePPTOn_lowerWith_link_of_reachable`:
  a caller-specific cap on supported replies suffices for strict oracle-PPT linking.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.link_of_reachable`: the linked UC environment is
  strict PPT under the same caller-specific cap.
* `Cslib.Crypto.Protocols.UC.WordInterface.exists_polyBounded_reply_take`,
  `Cslib.Crypto.Protocols.UC.Machine.isReplyBounded_id`: polynomial reply-length bound for
  truncated replies and for the forwarding machine `Machine.id`.
* `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded.routeCorrupt`,
  `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded.liftRight`,
  `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded.hybridWrap`: structural transfer lemmas for
  static-corruption routing, right-side interface lifting, and hybrid protocol wrapping.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.isOraclePPTOn_lowerWith_link`: linking a strict-PPT
  environment with any reply-bounded strict-PPT machine family yields a uniform strict oracle-PPT
  program over the machine's lowered imported interface.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.link`: linking a strict-PPT environment with a
  reply-bounded strict-PPT machine family preserves `Environment.IsPPT`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Turing.MultiTapeTM Cslib.Probability

/-! ### Message-bound predicates -/

/-- Library construction (no cited definition): every encoded reply that the machine family `M`
exports, in any activation from any state with imported replies read up to `p.replyBound` bits,
has length at most a polynomial in `(encPPTParam n p).length` alone. -/
@[expose] def Machine.IsReplyBounded {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E) (iI : WordInterface I) (iE : WordInterface E) : Prop :=
  ∃ bound : PPTParam n → ℕ,
    PolyBounded (fun p => (encPPTParam n p).length) bound ∧
    ∀ (p : PPTParam n) (q : ιE) (s : (M p.secParam p.corrupted).State),
      ∀ x ∈ OracleComp.support
          (ProbOracleComp.lowerWith iI p.replyBound (((M p.secParam p.corrupted).handle q).run s)),
        (iE.reply q x.1).length ≤ bound p

/-! ### Transfer lemmas -/

/-- Library infrastructure (no cited result): static-corruption routing preserves
`Machine.IsReplyBounded`; every routed reply is either a party/network reply from `M` (possibly
tagged with one sum bit) or a constant `none` reply. -/
theorem Machine.IsReplyBounded.routeCorrupt {n : ℕ} {ιI : Type} {I : ιI → Type}
    {In Out NetQ NetR : Type} {iI : WordInterface I}
    {party : WordPort (Fin n × In) (Option Out)} {netPort : WordPort NetQ NetR}
    {M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR)}
    (h : Machine.IsReplyBounded M iI (WordInterface.protocol party netPort)) :
    Machine.IsReplyBounded (fun κ C => routeCorrupt C (M κ C))
      iI (WordInterface.protocol party (WordPort.sum party netPort)) := by
  obtain ⟨bound, hpoly, hle⟩ := h
  refine ⟨fun p => bound p + (party.reply none).length + 1,
    (hpoly.add (PolyBounded.const _)).add (PolyBounded.const 1), fun p q => ?_⟩
  rcases q with ⟨i, inp⟩ | ⟨i, inp⟩ | nq <;>
    simp only [UC.routeCorrupt, WordInterface.protocol, WordInterface.sum, WordInterface.net,
      WordPort.sum] <;> intro s x hx
  · split_ifs at hx with hi
    · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    · exact (hle p (.inl (i, inp)) s x hx).trans (by omega)
  · split_ifs at hx with hi
    · simp only [StateT.run_map, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map] at hx
      obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
      rw [encSum_inl, List.length_cons]
      exact Nat.succ_le_succ ((hle p (.inl (i, inp)) s y hy).trans (Nat.le_add_right _ _))
    · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
      rw [encSum_inl, List.length_cons]; omega
  · simp only [StateT.run_map, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map] at hx
    obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
    rw [encSum_inr, List.length_cons]
    exact Nat.succ_le_succ ((hle p (.inr nq) s y hy).trans (Nat.le_add_right _ _))

/-- Library infrastructure (no cited result): a reply word truncated at `p.replyBound`, decoded and
re-encoded through a `WordInterface`, has length at most a polynomial in
`(encPPTParam n p).length`. -/
theorem WordInterface.exists_polyBounded_reply_take {n : ℕ} {ι : Type} {E : ι → Type}
    (I : WordInterface E) :
    ∃ bound : PPTParam n → ℕ, PolyBounded (fun p => (encPPTParam n p).length) bound ∧
      ∀ (p : PPTParam n) (q : ι) (w : List Bool),
        (I.reply q (I.decodeReply q (List.take p.replyBound w))).length ≤ bound p := by
  obtain ⟨c, d, hnorm⟩ := I.computable_replyNormalize.polyBounded_length.exists_le
  have hrb : PolyBounded (fun p : PPTParam n => (encPPTParam n p).length) (·.replyBound) := by
    simpa only [encUnary_apply, List.length_replicate] using
      (by fun_prop : ComputableInPolyTime (fun p : PPTParam n => p.replyBound)
        (encPPTParam n) encUnary).polyBounded_length
  refine ⟨fun p => c * (2 * Nat.card I.Channel + 2 + p.replyBound) ^ d,
    (PolyBounded.const c).mul
      (((PolyBounded.const (2 * Nat.card I.Channel + 2)).add hrb).pow d),
    fun p q w => ?_⟩
  rw [I.reply_decodeReply]
  have hch := length_encFinite_lt (I.channel q)
  refine (hnorm (I.channel q, List.take p.replyBound w)).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_left ?_ d))
  simp only [length_encPair, encBits_apply, List.length_take]; omega

/-- Every supported output of forwarding a single lowered query and keeping state `s` decodes a
reply word truncated at `limit`. -/
private theorem exists_word_of_mem_support_lowerWith_query_bind_pure
    {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) (limit : ℕ) (q : ι) (s : σ) {x : E q × σ}
    (hx : x ∈ OracleComp.support
      (ProbOracleComp.lowerWith I limit (ProbOracleComp.query q >>= fun r => pure (r, s)))) :
    ∃ w : List Bool, x.1 = I.decodeReply q (List.take limit w) := by
  simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery] at hx
  obtain ⟨r, hr, hx'⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
  obtain ⟨t, ht, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
  obtain ⟨w, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp ht
  obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx'
  exact ⟨w, rfl⟩

/-- Library infrastructure (no cited result): the forwarding machine `Machine.id` is
`Machine.IsReplyBounded`: each exported reply is an imported reply truncated at `p.replyBound`
and re-encoded. -/
theorem Machine.isReplyBounded_id {n : ℕ} {ι : Type} {E : ι → Type} (I : WordInterface E) :
    Machine.IsReplyBounded (n := n) (fun _ _ => Machine.id E) I I := by
  obtain ⟨bound, hpoly, hle⟩ := I.exists_polyBounded_reply_take (n := n)
  refine ⟨bound, hpoly, fun p q s x hx => ?_⟩
  obtain ⟨w, hw⟩ := exists_word_of_mem_support_lowerWith_query_bind_pure I p.replyBound q s hx
  exact hw ▸ hle p q w

/-- Library infrastructure (no cited result): lifting a reply-bounded machine family past a left
pass-through interface preserves `Machine.IsReplyBounded`; forwarded left-channel replies are
normalized from at most `p.replyBound` bits in polynomial time, and right-channel replies are
bounded by `M`'s bound. -/
theorem Machine.IsReplyBounded.liftRight {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    {iL : WordInterface L} {iR : WordInterface R} {iE : WordInterface E}
    {M : ℕ → Finset (Fin n) → Machine R E}
    (h : Machine.IsReplyBounded M iR iE) :
    Machine.IsReplyBounded (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) := by
  obtain ⟨bound, hpoly, hle⟩ := h
  obtain ⟨boundL, hpolyL, hleL⟩ := iL.exists_polyBounded_reply_take (n := n)
  refine ⟨fun p => bound p + boundL p, hpoly.add hpolyL, fun p q s x hx => ?_⟩
  let s' : (M p.secParam p.corrupted).State := s
  cases q with
  | inl qL =>
    obtain ⟨w, hw⟩ := exists_word_of_mem_support_lowerWith_query_bind_pure
      (iL.sum iR) p.replyBound (.inl qL) s' hx
    simpa only [WordInterface.sum] using (hw ▸ hleL p qL w).trans (Nat.le_add_left _ _)
  | inr qE =>
    change x ∈ OracleComp.support (ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
      (Machine.liftRightProgram L (((M p.secParam p.corrupted).handle qE).run s'))) at hx
    rw [support_lowerWith_liftRightProgram iL iR] at hx
    exact (hle p qE s' x hx).trans (Nat.le_add_right _ _)

/-- Library infrastructure (no cited result), toward #6043: `hybridWrap` preserves
`Machine.IsReplyBounded`; network replies gain one sum bit, and forwarded subroutine-network replies
are bounded as for `Machine.id`. -/
theorem Machine.IsReplyBounded.hybridWrap
    {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut}
    {party : WordPort (Fin n × In) (Option Out)} {net : WordPort NetQ NetR}
    {subParty : WordPort (Fin n × SubIn) (Option SubOut)} {nq : WordPort NQ NR}
    (h : Machine.IsReplyBounded ρ (WordInterface.net subParty) (WordInterface.protocol party net)) :
    Machine.IsReplyBounded (fun κ C => UC.hybridWrap (NQ := NQ) (NR := NR) (ρ κ C))
      (WordInterface.protocol subParty nq)
      (WordInterface.protocol party (WordPort.sum net nq)) := by
  obtain ⟨bρ, hbρ, hle⟩ := h
  obtain ⟨bN, hbN, hleN⟩ := (WordInterface.net nq).exists_polyBounded_reply_take (n := n)
  refine ⟨fun p => bρ p + 1 + bN p, (hbρ.add (PolyBounded.const 1)).add hbN, fun p q => ?_⟩
  rcases q with qp | qm | qs <;> simp only [UC.hybridWrap] <;> intro s x hx
  · rw [StateT.run, support_lowerWith_liftParty subParty nq] at hx
    exact (hle p (.inl qp) s x hx).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · simp only [StateT.run_map] at hx
    simp only [StateT.run, liftParty_map, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_map] at hx
    obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
    rw [← OracleComp.support, ← ProbOracleComp.lowerWith,
      support_lowerWith_liftParty subParty nq] at hy
    have h1 := hle p (.inr qm) s y hy
    simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net, WordPort.sum,
      encSum_inl, List.length_cons] at h1 ⊢
    omega
  · simp only [StateT.run_lift, bind_map_left, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure,
      WordInterface.lowerQuery] at hx
    obtain ⟨w, _, hx'⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx'
    have h1 : (nq.reply _).length ≤ bN p := hleN p qs w
    simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net, WordPort.sum,
      encSum_inr, List.length_cons] at h1 ⊢
    omega

/-! ### Linking -/

/-- Every actually returned exported word fits the cap along this typed execution. The
imported oracle and its state are shared by the handler and the continuation. -/
inductive RepliesFitOn
    {ιI ιE α : Type} {I : ιI → Type} {E : ιE → Type}
    (m : Machine I E) (iI : WordInterface I) (iE : WordInterface E)
    (b L : ℕ) {State : Type}
    (oracle : iI.Channel × List Bool → StateT State PMF (List Bool)) :
    ProbOracleComp E α → m.State → State → Prop where
  | pure (a : α) (s0 : m.State) (s : State) :
      RepliesFitOn m iI iE b L oracle (PFunctor.FreeM.pure a) s0 s
  | coin {k : ℕ} {cont : Fin (k + 1) → ProbOracleComp E α} {s0 : m.State} {s : State}
      (next : ∀ a, RepliesFitOn m iI iE b L oracle (cont a) s0 s) :
      RepliesFitOn m iI iE b L oracle
        (PFunctor.FreeM.liftBind (Sum.inl k : ℕ ⊕ ιE) cont) s0 s
  | query {q : ιE} {cont : E q → ProbOracleComp E α} {s0 : m.State} {s : State}
      (fits : ∀ x ∈ (ProbOracleComp.runWith oracle
          (ProbOracleComp.lowerWith iI b ((m.handle q).run s0)) s).support,
        let (reply, _) := x.1
        (iE.reply q reply).length ≤ L)
      (next : ∀ x ∈ (ProbOracleComp.runWith oracle
          (ProbOracleComp.lowerWith iI b ((m.handle q).run s0)) s).support,
        let ((reply, nextMachine), nextOracle) := x
        RepliesFitOn m iI iE b L oracle (cont reply) nextMachine nextOracle) :
      RepliesFitOn m iI iE b L oracle
        (PFunctor.FreeM.liftBind (Sum.inr q : ℕ ⊕ ιE) cont) s0 s

/-- The typed execution visits the same continuations when its proof uses a larger cap. -/
theorem RepliesFitOn.mono_cap
    {ιI ιE α : Type} {I : ιI → Type} {E : ιE → Type}
    {m : Machine I E} {iI : WordInterface I} {iE : WordInterface E} {b L L' : ℕ}
    {State : Type} {oracle : iI.Channel × List Bool → StateT State PMF (List Bool)}
    {prog : ProbOracleComp E α} {s0 : m.State} {s : State}
    (h : RepliesFitOn m iI iE b L oracle prog s0 s) (larger : L ≤ L') :
    RepliesFitOn m iI iE b L' oracle prog s0 s := by
  induction h with
  | pure a st t => exact .pure a st t
  | coin _ ih => exact .coin ih
  | query fits _ ih => exact .query (fun x hx => (fits x hx).trans larger) ih

/-- The global reply-length premise from Frontier's existing linking theorem suffices
on every supported continuation, for every imported stateful oracle. -/
theorem RepliesFitOn.of_global
    {ιI ιE α : Type} {I : ιI → Type} {E : ιE → Type}
    (m : Machine I E) (iI : WordInterface I) (iE : WordInterface E)
    (b L : ℕ) {State : Type}
    (oracle : iI.Channel × List Bool → StateT State PMF (List Bool))
    (bound : ∀ q s0 (x : E q × m.State),
        x ∈ OracleComp.support (ProbOracleComp.lowerWith iI b ((m.handle q).run s0)) →
        (iE.reply q x.1).length ≤ L)
    (prog : ProbOracleComp E α) (s0 : m.State) (s : State) :
    RepliesFitOn m iI iE b L oracle prog s0 s := by
  induction prog generalizing s0 s with
  | pure a => exact .pure a s0 s
  | liftBind q cont ih =>
    cases q with
    | inl k => exact .coin (fun a => ih a s0 s)
    | inr q =>
      exact .query (fun x hx => bound q s0 x.1 (ProbOracleComp.mem_support_of_mem oracle hx))
        (fun ((reply, nextMachine), nextOracle) _ => ih reply nextMachine nextOracle)

/-- Truncating exported replies preserves the full joint distribution of result,
encoded machine state and imported-oracle state on a supported execution. -/
theorem runWith_wordHandle_lowerWith_eq_runWith_lowerWith_runFrom_of_repliesFit
    {n : ℕ} {ιI ιE α : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E)
    (iI : WordInterface I) (iE : WordInterface E) (codec : StateCodec M)
    (p : PPTParam n) (L : ℕ)
    (prog : ProbOracleComp E α) {State : Type}
    (oracle : iI.Channel × List Bool → StateT State PMF (List Bool))
    (s0 : (M p.secParam p.corrupted).State) (s : State)
    (hfit : RepliesFitOn (M p.secParam p.corrupted) iI iE p.replyBound L oracle prog s0 s) :
    ProbOracleComp.runWith oracle
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (wordHandle M iI iE codec p))
          (ProbOracleComp.lowerWith iE L prog)).run
          ((codec p.secParam p.corrupted).enc s0)) s =
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.lowerWith iI p.replyBound
          ((M p.secParam p.corrupted).runFrom prog s0)) s).map
        (fun ((a, nextMachine), nextOracle) =>
          ((a, (codec p.secParam p.corrupted).enc nextMachine), nextOracle)) := by
  let m := M p.secParam p.corrupted
  let cod := codec p.secParam p.corrupted
  let H :=
    OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (wordHandle M iI iE codec p)
  change ProbOracleComp.runWith oracle
      ((OracleComp.interpret H (ProbOracleComp.lowerWith iE L prog)).run (cod.enc s0)) s =
    (ProbOracleComp.runWith oracle
      (ProbOracleComp.lowerWith iI p.replyBound (m.runFrom prog s0)) s).map
      (fun x => ((x.1.1, cod.enc x.1.2), x.2))
  induction hfit with
  | pure a s0 s =>
    simp [ProbOracleComp.lowerWith, Machine.runFrom, OracleComp.interpret_pure]
  | @coin k cont s0 s _ ih =>
    have hk : PFunctor.FreeM.liftBind (Sum.inl k : ℕ ⊕ ιE) cont =
        (ProbOracleComp.sample (ProbComp.unifFin k) >>= cont) := rfl
    rw [hk, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_sample, Machine.runFrom_bind, Machine.runFrom_sample,
      ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_map,
      ProbOracleComp.simulate_sample]
    simp only [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.interpret_sample,
      ProbComp.unifFin, OracleComp.interpret_query, H, StateT.run_lift,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_pure, PMF.bind_map, PMF.map_bind, PMF.bind_bind, PMF.pure_bind,
      Function.comp_def, Prod.map_apply, id_eq]
    exact congrArg _ (funext fun a => ih a)
  | @query eQ cont s0 s fits _ ih =>
    have hq_eq : PFunctor.FreeM.liftBind (Sum.inr eQ : ℕ ⊕ ιE) cont =
        (ProbOracleComp.query eQ >>= cont) := rfl
    rw [hq_eq, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, WordInterface.lowerQuery, Machine.runFrom_bind,
      Machine.runFrom_query, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind]
    have hwh : wordHandle M iI iE codec p (iE.channel eQ, iE.request eQ) (cod.enc s0) =
        (fun res => (iE.reply eQ res.1, cod.enc res.2)) <$>
          ProbOracleComp.lowerWith iI p.replyBound ((m.handle eQ).run s0) := by
      unfold wordHandle
      generalize hq : iE.decodeQuery (iE.channel eQ) (iE.request eQ) = q'
      obtain rfl := hq.symm.trans (iE.decodeQuery_request eQ)
      simp only [cod, m, (codec p.secParam p.corrupted).decode_enc]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_map, StateT.run_bind,
      StateT.run_map, ProbOracleComp.interpret_query, H]
    simp only [StateT.run, hwh, ProbOracleComp.lowerWith,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, PMF.bind_map, PMF.map_bind,
      Function.comp_def, Prod.map, id_eq]
    refine PMF.bind_congr_on_support _ _ _ fun x hx => ?_
    rw [List.take_of_length_le (fits x hx),
      iE.decodeReply_reply]
    exact ih x hx

/-- A caller-specific cap suffices for strict-PPT linking. Its unary value must be efficiently
computable from the original environment parameters. For each imported oracle and supported
initial machine state, the caller must respect the cap along every supported continuation. -/
theorem Environment.IsPPT.isOraclePPTOn_lowerWith_link_of_reachable
    {n : ℕ} {ιI : Type} {I : ιI → Type} {In Out AdvQ AdvR : Type}
    {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort AdvQ AdvR}
    {Z : Environment n In Out AdvQ AdvR} {iI : WordInterface I}
    {M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out AdvQ AdvR)}
    (hZ : Z.IsPPT party adv)
    (hM : Machine.IsPPTFamily M iI (WordInterface.exec party adv))
    (C : Finset (Fin n)) (cap : EnvParam → ℕ)
    (hcap : ComputableInPolyTime cap encEnvParam encUnary)
    (hreach : ∀ (e : EnvParam) (State : Type)
      (oracle : iI.Channel × List Bool → StateT State PMF (List Bool)) (sO : State)
      (s0 : (M e.secParam C).State), s0 ∈ (M e.secParam C).init.eval.support →
      RepliesFitOn (M e.secParam C) iI (WordInterface.exec party adv) e.replyBound
        (cap e) oracle (Z e.secParam e.aux) s0 sO) :
    IsOraclePPTOn (Operation := iI.Channel) encEnvParam encBool
      (fun e : EnvParam =>
        ProbOracleComp.lowerWith iI e.replyBound ((M e.secParam C).link (Z e.secParam e.aux))) := by
  rcases hM with ⟨cert⟩
  let param : EnvParam → PPTParam n := fun e => ⟨e.secParam, e.replyBound, C⟩
  let envParam : EnvParam → EnvParam := fun e => ⟨e.secParam, cap e, e.aux⟩
  have hconst : ComputableInPolyTime (fun _ : EnvParam => C)
      encEnvParam (encFinite (Finset (Fin n))) := .const C
  have hparam : ComputableInPolyTime param encEnvParam (encPPTParam n) := by fun_prop
  have henv : ComputableInPolyTime envParam encEnvParam encEnvParam := by fun_prop
  refine (hZ.isOraclePPTOn_run_wordHandle cert hparam henv).congr fun e State oracle s => ?_
  simp only [wordRun, wordRunFrom, Machine.link, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample, ProbOracleComp.simulate_map,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map,
    ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun s0 hs0 => ?_
  have hstep := congrArg (PMF.map (Prod.map Prod.fst id))
    (runWith_wordHandle_lowerWith_eq_runWith_lowerWith_runFrom_of_repliesFit M iI
      (WordInterface.exec party adv) cert.codec (param e) (cap e)
      (Z e.secParam e.aux) oracle s0 s (hreach e State oracle s s0 hs0))
  simp only [param, ProbOracleComp.lowerWith, PMF.map_comp] at hstep
  exact hstep

namespace Computational

/-- A uniform caller-specific cap on encoded machine replies for a fixed static corruption set.
The same polynomial-time computable cap covers all external stateful oracles and each supported
initial machine state. It can depend on the security parameter, auxiliary word and reply bound. -/
@[expose] def ReplyCap {n : ℕ} {ι : Type} {I : ι → Type} {In Out Q R : Type}
    (M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out Q R))
    (iI : WordInterface I) (party : WordPort (Fin n × In) (Option Out)) (adv : WordPort Q R)
    (C : Finset (Fin n)) (Z : Environment n In Out Q R) : Prop :=
  ∃ cap : EnvParam → ℕ, ComputableInPolyTime cap encEnvParam encUnary ∧
    ∀ (e : EnvParam) (State : Type)
      (oracle : iI.Channel × List Bool → StateT State PMF (List Bool))
      (sO : State) (s0 : (M e.secParam C).State), s0 ∈ (M e.secParam C).init.eval.support →
      RepliesFitOn (M e.secParam C) iI (WordInterface.exec party adv) e.replyBound
        (cap e) oracle (Z e.secParam e.aux) s0 sO

/-- A polynomial majorant of a machine-wide reply bound gives a computable cap for each caller. -/
theorem ReplyCap.of_global {n : ℕ} {ι : Type} {I : ι → Type} {In Out Q R : Type}
    {M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out Q R)}
    {iI : WordInterface I} {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort Q R}
    (Z : Environment n In Out Q R) (C : Finset (Fin n))
    (hMR : Machine.IsReplyBounded M iI (WordInterface.exec party adv)) :
    ReplyCap M iI party adv C Z := by
  obtain ⟨bound, hpoly, hle⟩ := hMR
  obtain ⟨c, d, hcd⟩ := hpoly.exists_le
  let param : EnvParam → PPTParam n := fun e => ⟨e.secParam, e.replyBound, C⟩
  let cap : EnvParam → ℕ := fun e => c * ((encPPTParam n (param e)).length + 1) ^ d
  have hconst : ComputableInPolyTime (fun _ : EnvParam => C)
      encEnvParam (encFinite (Finset (Fin n))) := .const C
  have hparam : ComputableInPolyTime param encEnvParam (encPPTParam n) := by fun_prop
  have hcap : ComputableInPolyTime cap encEnvParam encUnary :=
    (show ComputableInPolyTime (fun k : ℕ => c * (k + 1) ^ d) encUnary encUnary by fun_prop).comp
      ((ComputableInPolyTime.encoding_length (encPPTParam n)).comp hparam)
  refine ⟨cap, hcap, fun e _ _ _ _ _ => ?_⟩
  apply RepliesFitOn.mono_cap _ (hcd (param e))
  apply RepliesFitOn.of_global
  exact hle (param e)

end Computational

/-- Library infrastructure (no cited result): linking a strict-PPT environment against any
reply-bounded strict-PPT machine family yields a uniform strict oracle-PPT program over the
machine's lowered imported interface. -/
theorem Environment.IsPPT.isOraclePPTOn_lowerWith_link
    {n : ℕ} {ιI : Type} {I : ιI → Type} {In Out AdvQ AdvR : Type}
    {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort AdvQ AdvR}
    {Z : Environment n In Out AdvQ AdvR}
    {iI : WordInterface I}
    {M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out AdvQ AdvR)}
    (hZ : Z.IsPPT party adv)
    (hM : Machine.IsPPTFamily M iI (WordInterface.exec party adv))
    (hMR : Machine.IsReplyBounded M iI (WordInterface.exec party adv))
    (C : Finset (Fin n)) :
    IsOraclePPTOn (Operation := iI.Channel) encEnvParam encBool
      (fun e : EnvParam =>
        ProbOracleComp.lowerWith iI e.replyBound ((M e.secParam C).link (Z e.secParam e.aux))) := by
  obtain ⟨cap, hcap, hreach⟩ := Computational.ReplyCap.of_global Z C hMR
  exact hZ.isOraclePPTOn_lowerWith_link_of_reachable hM C cap hcap hreach

/-- Library infrastructure (no cited result), toward #6043 (not Proposition 7 of [Canetti2020]):
linking a strict-PPT environment against a certified machine family with polynomially bounded
replies gives a strict-PPT environment for the machine's imported ports. -/
theorem Environment.IsPPT.link
    {n : ℕ} {In Out AdvQ AdvR In' Out' Q' R' : Type}
    {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort AdvQ AdvR}
    {party' : WordPort (Fin n × In') (Option Out')} {adv' : WordPort Q' R'}
    {Z : Environment n In Out AdvQ AdvR}
    {M : ℕ → Finset (Fin n) →
      Machine (execSpec n In' Out' Q' R') (execSpec n In Out AdvQ AdvR)}
    (hZ : Z.IsPPT party adv)
    (hM : Machine.IsPPTFamily M (WordInterface.exec party' adv') (WordInterface.exec party adv))
    (hMR : Machine.IsReplyBounded M (WordInterface.exec party' adv') (WordInterface.exec party adv))
    (C : Finset (Fin n)) :
    Environment.IsPPT (fun κ z => (M κ C).link (Z κ z)) party' adv' :=
  hZ.isOraclePPTOn_lowerWith_link hM hMR C

/-- Linking on an execution interface preserves strict PPT under a caller-specific reply cap. -/
theorem Environment.IsPPT.link_of_reachable
    {n : ℕ} {In Out AdvQ AdvR In' Out' Q' R' : Type}
    {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort AdvQ AdvR}
    {party' : WordPort (Fin n × In') (Option Out')} {adv' : WordPort Q' R'}
    {Z : Environment n In Out AdvQ AdvR}
    {M : ℕ → Finset (Fin n) →
      Machine (execSpec n In' Out' Q' R') (execSpec n In Out AdvQ AdvR)}
    (hZ : Z.IsPPT party adv)
    (hM : Machine.IsPPTFamily M (WordInterface.exec party' adv') (WordInterface.exec party adv))
    (C : Finset (Fin n)) (cap : EnvParam → ℕ)
    (hcap : ComputableInPolyTime cap encEnvParam encUnary)
    (hreach : ∀ (e : EnvParam) (State : Type)
      (oracle : (WordInterface.exec party' adv').Channel × List Bool → StateT State PMF (List Bool))
      (sO : State) (s0 : (M e.secParam C).State), s0 ∈ (M e.secParam C).init.eval.support →
      RepliesFitOn (M e.secParam C) (WordInterface.exec party' adv') (WordInterface.exec party adv)
        e.replyBound (cap e) oracle (Z e.secParam e.aux) s0 sO) :
    Environment.IsPPT (fun κ z => (M κ C).link (Z κ z)) party' adv' :=
  hZ.isOraclePPTOn_lowerWith_link_of_reachable hM C cap hcap hreach

end Cslib.Crypto.Protocols.UC
