/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Composition
public import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Strict-PPT closure of UC linking and adversary absorption

Library infrastructure toward #6043 (no cited result): proves that linking a strict-PPT UC
environment with a strict-PPT machine family (and absorbing a strict-PPT adversary into a
strict-PPT environment) preserves `Environment.IsPPT`, under a polynomial reply-length bound
(`Machine.IsReplyBounded`) on the machine family.

## Modelling decisions and restrictions

* **Reply-length bound (`Machine.IsReplyBounded`).** Unlike [Canetti2020]'s cumulative import-based
  runtime budgets (Section 3.2), `PPTCertificate` truncates imported replies per activation at
  `PPTParam.replyBound` while leaving internal typed messages untruncated. `Machine.IsReplyBounded`
  requires every encoded reply exported by `M` to fit within a polynomial in the encoded activation
  parameter `PPTParam` alone (not in the request word or state). This gives a state-independent
  internal truncation cap `L(e)` at which the outer environment's `PPT` certificate is instantiated
  via `Environment.IsPPT.isOraclePPTOn_runWith_wordHandle`, ensuring no internal reply is truncated.
  Protocols that relay payloads of unbounded environment-chosen length back to an outer caller are
  excluded; the test module `CslibFrontierTests.Crypto.UCPPTLink` gives a concrete PPT relay
  witnessing `¬ Machine.IsReplyBounded`.
* **Request-length bound (`Machine.IsRequestBounded`).** Bounds every outgoing request word emitted
  by `M` on its imported interface by a polynomial in `(PPTParam, request)` (not in the state).
  Together with a call budget, this supports sequential composition (`Machine.comp`) under the
  state-independent additive `growth` contract of `PPTCertificate`.

## Main definitions

* `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded`: every supported exported reply word fits in
  a polynomial of `(encPPTParam n p).length`.
* `Cslib.Crypto.Protocols.UC.Machine.IsRequestBounded`: every imported request word fits in a
  polynomial of `(encPair (encPPTParam n) encBits (p, iE.request q)).length`.

## Main results

* `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded.routeCorrupt`,
  `Cslib.Crypto.Protocols.UC.Machine.IsRequestBounded.routeCorrupt`,
  `Cslib.Crypto.Protocols.UC.Machine.IsReplyBounded.liftRight`,
  `Cslib.Crypto.Protocols.UC.Machine.IsRequestBounded.liftRight`: structural transfer lemmas for
  static-corruption routing and right-side interface lifting.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.isOraclePPTOn_lowerWith_link`: linking a strict-PPT
  environment with any reply-bounded strict-PPT machine family yields a uniform strict oracle-PPT
  program over the machine's lowered imported interface.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.link`: linking a strict-PPT environment with a
  reply-bounded strict-PPT machine family preserves `Environment.IsPPT`.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.absorbAdversary`: absorbing a reply-bounded
  strict-PPT adversary into a strict-PPT environment preserves `Environment.IsPPT`.
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

/-- Library construction (no cited definition): every request word that the machine family `M`
emits on its imported interface, in any activation from any state with imported replies read up to
`p.replyBound` bits, has length at most a polynomial in
`(encPair (encPPTParam n) encBits (p, iE.request q)).length`. -/
@[expose] def Machine.IsRequestBounded {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E) (iI : WordInterface I) (iE : WordInterface E) : Prop :=
  ∃ bound : PPTParam n × List Bool → ℕ,
    PolyBounded (fun pw => (encPair (encPPTParam n) encBits pw).length) bound ∧
    ∀ (p : PPTParam n) (q : ιE) (s : (M p.secParam p.corrupted).State),
      OracleComp.QueriesSatisfy
        (fun op => Sum.elim (fun _ => True) (fun cw => cw.2.length ≤ bound (p, iE.request q)) op)
        (ProbOracleComp.lowerWith iI p.replyBound (((M p.secParam p.corrupted).handle q).run s))

/-! ### Transfer lemmas -/

/-- Static-corruption routing preserves `Machine.IsReplyBounded`: every routed reply is either a
party/network reply from `M` (possibly tagged with one sum bit) or a constant `none` reply. -/
theorem Machine.IsReplyBounded.routeCorrupt {n : ℕ} {ιI : Type} {I : ιI → Type}
    {In Out NetQ NetR : Type} {iI : WordInterface I}
    {party : WordPort (Fin n × In) (Option Out)} {netPort : WordPort NetQ NetR}
    {M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR)}
    (h : Machine.IsReplyBounded M iI (WordInterface.protocol party netPort)) :
    Machine.IsReplyBounded (fun κ C => routeCorrupt C (M κ C))
      iI (WordInterface.protocol party (WordPort.sum party netPort)) := by
  obtain ⟨bound, hpoly, hle⟩ := h
  refine ⟨fun p => bound p + (party.reply none).length + 1,
    (hpoly.add (PolyBounded.const _)).add (PolyBounded.const 1), fun p q s x hx => ?_⟩
  let s' : (M p.secParam p.corrupted).State := s
  cases q with
  | inl ix =>
    rcases ix with ⟨i, inp⟩
    by_cases hi : i ∈ p.corrupted
    · change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        ((if i ∈ p.corrupted then pure none
          else (M p.secParam p.corrupted).handle (.inl (i, inp))).run s')) at hx
      simp only [hi, ↓reduceIte, StateT.run_pure, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure] at hx
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
      simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net]
      omega
    · change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        ((if i ∈ p.corrupted then pure none
          else (M p.secParam p.corrupted).handle (.inl (i, inp))).run s')) at hx
      simp only [hi, ↓reduceIte] at hx
      have h1 := hle p (.inl (i, inp)) s' x hx
      simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net] at h1 ⊢
      omega
  | inr rq =>
    cases rq with
    | inl ix =>
      rcases ix with ⟨i, inp⟩
      by_cases hi : i ∈ p.corrupted
      · change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
          ((if i ∈ p.corrupted then Sum.inl <$> (M p.secParam p.corrupted).handle (.inl (i, inp))
            else pure (.inl none)).run s')) at hx
        simp only [hi, ↓reduceIte, StateT.run_map, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_map] at hx
        obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
        have h1 := hle p (.inl (i, inp)) s' y hy
        simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net, WordPort.sum,
          encSum_inl, List.length_cons] at h1 ⊢
        omega
      · change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
          ((if i ∈ p.corrupted then Sum.inl <$> (M p.secParam p.corrupted).handle (.inl (i, inp))
            else pure (.inl none)).run s')) at hx
        simp only [hi, ↓reduceIte, StateT.run_pure, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_pure] at hx
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx
        simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net, WordPort.sum,
          encSum_inl, List.length_cons]
        omega
    | inr nq =>
      change x ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        ((Sum.inr <$> (M p.secParam p.corrupted).handle (.inr nq)).run s')) at hx
      simp only [StateT.run_map, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map] at hx
      obtain ⟨y, hy, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hx
      have h1 := hle p (.inr nq) s' y hy
      simp only [WordInterface.protocol, WordInterface.sum, WordInterface.net, WordPort.sum,
        encSum_inr, List.length_cons] at h1 ⊢
      omega

/-- Static-corruption routing preserves `Machine.IsRequestBounded`: routed adversary requests strip
the leading sum tag before forwarding to `M`, so `bound (p, w) + bound (p, w.tail)` dominates all
outgoing request words. -/
theorem Machine.IsRequestBounded.routeCorrupt {n : ℕ} {ιI : Type} {I : ιI → Type}
    {In Out NetQ NetR : Type} {iI : WordInterface I}
    {party : WordPort (Fin n × In) (Option Out)} {netPort : WordPort NetQ NetR}
    {M : ℕ → Finset (Fin n) → Machine I (protocolSpec n In Out NetQ NetR)}
    (h : Machine.IsRequestBounded M iI (WordInterface.protocol party netPort)) :
    Machine.IsRequestBounded (fun κ C => routeCorrupt C (M κ C))
      iI (WordInterface.protocol party (WordPort.sum party netPort)) := by
  obtain ⟨bound, hpoly, hq⟩ := h
  have htail : PolyBounded
      (fun pw : PPTParam n × List Bool => (encPair (encPPTParam n) encBits pw).length)
      (fun pw => bound (pw.1, pw.2.tail)) :=
    hpoly.comp (PolyBounded.self.mono fun pw => by
      simp only [length_encPair, encBits_apply, List.length_tail]
      omega)
  refine ⟨fun pw => bound pw + bound (pw.1, pw.2.tail), hpoly.add htail, fun p q s => ?_⟩
  let s' : (M p.secParam p.corrupted).State := s
  cases q with
  | inl ix =>
    rcases ix with ⟨i, inp⟩
    by_cases hi : i ∈ p.corrupted
    · change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith iI p.replyBound
        ((if i ∈ p.corrupted then pure none
          else (M p.secParam p.corrupted).handle (.inl (i, inp))).run s'))
      simp only [hi, ↓reduceIte, StateT.run_pure, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure]
      exact OracleComp.QueriesSatisfy.pure _
    · change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith iI p.replyBound
        ((if i ∈ p.corrupted then pure none
          else (M p.secParam p.corrupted).handle (.inl (i, inp))).run s'))
      simp only [hi, ↓reduceIte]
      refine (hq p (.inl (i, inp)) s').mono fun op hop => ?_
      cases op with
      | inl _ => trivial
      | inr cw =>
        simp only [Sum.elim_inr, Sum.elim_inl, WordInterface.protocol, WordInterface.sum,
          WordInterface.net] at hop ⊢
        omega
  | inr rq =>
    cases rq with
    | inl ix =>
      rcases ix with ⟨i, inp⟩
      by_cases hi : i ∈ p.corrupted
      · change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith iI p.replyBound
          ((if i ∈ p.corrupted then Sum.inl <$> (M p.secParam p.corrupted).handle (.inl (i, inp))
            else pure (.inl none)).run s'))
        simp only [hi, ↓reduceIte, StateT.run_map, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_map, OracleComp.queriesSatisfy_map_iff]
        refine (hq p (.inl (i, inp)) s').mono fun op hop => ?_
        cases op with
        | inl _ => trivial
        | inr cw =>
          simp only [Sum.elim_inr, Sum.elim_inl, WordInterface.protocol, WordInterface.sum,
            WordInterface.net, WordPort.sum, encSum_inl, List.tail_cons] at hop ⊢
          omega
      · change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith iI p.replyBound
          ((if i ∈ p.corrupted then Sum.inl <$> (M p.secParam p.corrupted).handle (.inl (i, inp))
            else pure (.inl none)).run s'))
        simp only [hi, ↓reduceIte, StateT.run_pure, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_pure]
        exact OracleComp.QueriesSatisfy.pure _
    | inr nq =>
      change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith iI p.replyBound
        ((Sum.inr <$> (M p.secParam p.corrupted).handle (.inr nq)).run s'))
      simp only [StateT.run_map, ProbOracleComp.lowerWith, ProbOracleComp.simulate_map,
        OracleComp.queriesSatisfy_map_iff]
      refine (hq p (.inr nq) s').mono fun op hop => ?_
      cases op with
      | inl _ => trivial
      | inr cw =>
        simp only [Sum.elim_inr, WordInterface.protocol, WordInterface.sum, WordInterface.net,
          WordPort.sum, encSum_inr, List.tail_cons] at hop ⊢
        omega

private theorem lowerWith_liftRightProgram {ιL ιR α : Type} {L : ιL → Type} {R : ιR → Type}
    (iL : WordInterface L) (iR : WordInterface R) (limit : ℕ) (prog : ProbOracleComp R α) :
    ProbOracleComp.lowerWith (iL.sum iR) limit (Machine.liftRightProgram L prog) =
      ProbOracleComp.simulate
        (fun cw : iR.Channel × List Bool =>
          ProbOracleComp.query (spec := fun _ : (iL.sum iR).Channel × List Bool => List Bool)
            (.inr cw.1, cw.2))
        (ProbOracleComp.lowerWith iR limit prog) := by
  induction prog with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | inl m =>
      change ProbOracleComp.lowerWith (iL.sum iR) limit
        (Machine.liftRightProgram L (ProbOracleComp.sample (ProbComp.unifFin m) >>= cont)) =
        ProbOracleComp.simulate _ (ProbOracleComp.lowerWith iR limit
          (ProbOracleComp.sample (ProbComp.unifFin m) >>= cont))
      have hl : Machine.liftRightProgram L (ProbOracleComp.sample (ProbComp.unifFin m) >>= cont) =
          ProbOracleComp.sample (ProbComp.unifFin m) >>= fun a =>
            Machine.liftRightProgram L (cont a) := by
        simp only [Machine.liftRightProgram, OracleComp.interpret_bind,
          ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
        rfl
      rw [hl]
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
        ProbOracleComp.simulate_sample]
      exact congrArg (ProbOracleComp.sample (ProbComp.unifFin m) >>= ·) (funext ih)
    | inr r =>
      change ProbOracleComp.lowerWith (iL.sum iR) limit
        (Machine.liftRightProgram L (ProbOracleComp.query r >>= cont)) =
        ProbOracleComp.simulate _ (ProbOracleComp.lowerWith iR limit
          (ProbOracleComp.query r >>= cont))
      have hl : Machine.liftRightProgram L (ProbOracleComp.query r >>= cont) =
          ProbOracleComp.query (spec := L ⊕ₒ R) (.inr r) >>= fun a =>
            Machine.liftRightProgram L (cont a) := by
        simp only [Machine.liftRightProgram, OracleComp.interpret_bind,
          ProbOracleComp.interpret_query]
      rw [hl]
      simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
        ProbOracleComp.simulate_query, ProbOracleComp.simulate_map, WordInterface.lowerQuery,
        WordInterface.sum, Sum.map_inr, Sum.elim_inr]
      exact congrArg _ (funext ih)

private theorem mem_support_simulate_channelMap {C₁ C₂ α : Type} (f : C₁ → C₂)
    (prog : WordOracleComp C₁ α) {x : α}
    (hx : x ∈ OracleComp.support
      (ProbOracleComp.simulate
        (fun cw : C₁ × List Bool =>
          ProbOracleComp.query (spec := fun _ : C₂ × List Bool => List Bool) (f cw.1, cw.2))
        prog)) :
    x ∈ OracleComp.support prog := by
  induction prog with
  | pure a => exact hx
  | liftBind q cont ih =>
    cases q with
    | inl m =>
      change x ∈ OracleComp.support
        (ProbOracleComp.simulate
          (fun cw : C₁ × List Bool =>
            ProbOracleComp.query (spec := fun _ : C₂ × List Bool => List Bool) (f cw.1, cw.2))
          (ProbOracleComp.sample (ProbComp.unifFin m) >>= cont)) at hx
      rw [ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample] at hx
      obtain ⟨a, _, hcont⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
      change x ∈ OracleComp.support (ProbOracleComp.sample (ProbComp.unifFin m) >>= cont)
      exact OracleComp.mem_supportWith_bind_iff.mpr
        ⟨a, by simp [ProbOracleComp.support_sample, ProbComp.eval_unifFin], ih a hcont⟩
    | inr cw =>
      change x ∈ OracleComp.support
        (ProbOracleComp.simulate
          (fun cw : C₁ × List Bool =>
            ProbOracleComp.query (spec := fun _ : C₂ × List Bool => List Bool) (f cw.1, cw.2))
          (ProbOracleComp.query cw >>= cont)) at hx
      rw [ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query] at hx
      obtain ⟨w, _, hcont⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
      change x ∈ OracleComp.support
        (ProbOracleComp.query (spec := fun _ : C₁ × List Bool => List Bool) cw >>= cont)
      exact OracleComp.mem_supportWith_bind_iff.mpr
        ⟨w, by simp [ProbOracleComp.supportWith_query], ih w hcont⟩

private theorem queriesSatisfy_simulate_channelMap {C₁ C₂ α : Type} (f : C₁ → C₂) {B : ℕ}
    (prog : WordOracleComp C₁ α)
    (h : OracleComp.QueriesSatisfy
      (fun op : ℕ ⊕ (C₁ × List Bool) => Sum.elim (fun _ => True) (fun cw => cw.2.length ≤ B) op)
      prog) :
    OracleComp.QueriesSatisfy
      (fun op : ℕ ⊕ (C₂ × List Bool) => Sum.elim (fun _ => True) (fun cw => cw.2.length ≤ B) op)
      (ProbOracleComp.simulate
        (fun cw : C₁ × List Bool =>
          ProbOracleComp.query (spec := fun _ : C₂ × List Bool => List Bool) (f cw.1, cw.2))
        prog) := by
  induction prog with
  | pure a => exact OracleComp.QueriesSatisfy.pure a
  | liftBind q cont ih =>
    rw [OracleComp.QueriesSatisfy.liftBind_iff] at h
    cases q with
    | inl m =>
      change OracleComp.QueriesSatisfy _
        (ProbOracleComp.simulate
          (fun cw : C₁ × List Bool =>
            ProbOracleComp.query (spec := fun _ : C₂ × List Bool => List Bool) (f cw.1, cw.2))
          (ProbOracleComp.sample (ProbComp.unifFin m) >>= cont))
      rw [ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample]
      refine OracleComp.QueriesSatisfy.bind ?_ (fun a => ih a (h.2 a))
      exact OracleComp.QueriesSatisfy.query trivial
    | inr cw =>
      change OracleComp.QueriesSatisfy _
        (ProbOracleComp.simulate
          (fun cw : C₁ × List Bool =>
            ProbOracleComp.query (spec := fun _ : C₂ × List Bool => List Bool) (f cw.1, cw.2))
          (ProbOracleComp.query cw >>= cont))
      rw [ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query]
      refine OracleComp.QueriesSatisfy.bind ?_ (fun a => ih a (h.2 a))
      exact OracleComp.QueriesSatisfy.query h.1

/-- Lifting a reply-bounded machine family past a left pass-through interface preserves
`Machine.IsReplyBounded`: forwarded left-channel replies are normalized from at most `p.replyBound`
bits in polynomial time, and right-channel replies are bounded by `M`'s bound. -/
theorem Machine.IsReplyBounded.liftRight {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    {iL : WordInterface L} {iR : WordInterface R} {iE : WordInterface E}
    {M : ℕ → Finset (Fin n) → Machine R E}
    (h : Machine.IsReplyBounded M iR iE) :
    Machine.IsReplyBounded (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) := by
  obtain ⟨bound, hpoly, hle⟩ := h
  obtain ⟨c, d, hnorm⟩ := iL.computable_replyNormalize.polyBounded_length.exists_le
  have hrb : PolyBounded (fun p : PPTParam n => (encPPTParam n p).length)
      (fun p => p.replyBound) := by
    have hc : ComputableInPolyTime (fun p : PPTParam n => p.replyBound)
        (encPPTParam n) encUnary := by
      fun_prop
    simpa only [encUnary_apply, List.length_replicate] using hc.polyBounded_length
  let boundL : PPTParam n → ℕ :=
    fun p => c * (2 * Nat.card iL.Channel + 2 + p.replyBound) ^ d
  have hpolyL : PolyBounded (fun p : PPTParam n => (encPPTParam n p).length) boundL :=
    (PolyBounded.const c).mul
      (((PolyBounded.const (2 * Nat.card iL.Channel + 2)).add hrb).pow d)
  refine ⟨fun p => bound p + boundL p, hpoly.add hpolyL, fun p q s x hx => ?_⟩
  let s' : (M p.secParam p.corrupted).State := s
  cases q with
  | inl qL =>
    change x ∈ OracleComp.support (ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
      (ProbOracleComp.query (spec := L ⊕ₒ R) (.inl qL) >>= fun r => pure (r, s'))) at hx
    simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
      WordInterface.sum] at hx
    obtain ⟨r, hr, hx'⟩ := OracleComp.mem_supportWith_bind_iff.mp hx
    obtain ⟨t, ht, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
    obtain ⟨w, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp ht
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hx'
    change (iL.reply qL (iL.decodeReply qL (List.take p.replyBound w))).length ≤ bound p + boundL p
    rw [iL.reply_decodeReply]
    have h1 : (iL.replyNormalize (iL.channel qL) (List.take p.replyBound w)).length ≤
        c * ((encPair (encFinite iL.Channel) encBits
          (iL.channel qL, List.take p.replyBound w)).length + 1) ^ d := by
      simpa only [encBits_apply] using hnorm (iL.channel qL, List.take p.replyBound w)
    have hch : (encFinite iL.Channel (iL.channel qL)).length ≤ Nat.card iL.Channel :=
      (length_encFinite_lt _).le
    have hlen : (encPair (encFinite iL.Channel) encBits
        (iL.channel qL, List.take p.replyBound w)).length + 1 ≤
        2 * Nat.card iL.Channel + 2 + p.replyBound := by
      simp only [length_encPair, encBits_apply, List.length_take]
      omega
    have h2 : c * ((encPair (encFinite iL.Channel) encBits
        (iL.channel qL, List.take p.replyBound w)).length + 1) ^ d ≤ boundL p :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left hlen d)
    omega
  | inr qE =>
    change x ∈ OracleComp.support (ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
      (Machine.liftRightProgram L (((M p.secParam p.corrupted).handle qE).run s'))) at hx
    rw [lowerWith_liftRightProgram] at hx
    have hy := mem_support_simulate_channelMap Sum.inr _ hx
    have h1 := hle p qE s' x hy
    change (iE.reply qE x.1).length ≤ bound p + boundL p
    omega

/-- Lifting a request-bounded machine family past a left pass-through interface preserves
`Machine.IsRequestBounded`: forwarded left-channel requests emit their incoming word verbatim, and
right-channel requests preserve word lengths under channel tagging. -/
theorem Machine.IsRequestBounded.liftRight {n : ℕ} {ιL ιR ιE : Type}
    {L : ιL → Type} {R : ιR → Type} {E : ιE → Type}
    {iL : WordInterface L} {iR : WordInterface R} {iE : WordInterface E}
    {M : ℕ → Finset (Fin n) → Machine R E}
    (h : Machine.IsRequestBounded M iR iE) :
    Machine.IsRequestBounded (fun κ C => Machine.liftRight L (M κ C)) (iL.sum iR) (iL.sum iE) := by
  obtain ⟨bound, hpoly, hq⟩ := h
  have hword : PolyBounded
      (fun pw : PPTParam n × List Bool => (encPair (encPPTParam n) encBits pw).length)
      (fun pw => pw.2.length) :=
    PolyBounded.self.mono fun pw => by
      simp only [length_encPair, encBits_apply]
      omega
  refine ⟨fun pw => bound pw + pw.2.length, hpoly.add hword, fun p q s => ?_⟩
  let s' : (M p.secParam p.corrupted).State := s
  cases q with
  | inl qL =>
    change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
      (ProbOracleComp.query (spec := L ⊕ₒ R) (.inl qL) >>= fun r => pure (r, s')))
    simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, WordInterface.lowerQuery,
      WordInterface.sum]
    refine OracleComp.QueriesSatisfy.bind ?_ (fun _ => OracleComp.QueriesSatisfy.pure _)
    rw [OracleComp.queriesSatisfy_map_iff, OracleComp.queriesSatisfy_map_iff]
    refine OracleComp.QueriesSatisfy.query ?_
    change (iL.request qL).length ≤ bound (p, iL.request qL) + (iL.request qL).length
    omega
  | inr qE =>
    change OracleComp.QueriesSatisfy _ (ProbOracleComp.lowerWith (iL.sum iR) p.replyBound
      (Machine.liftRightProgram L (((M p.secParam p.corrupted).handle qE).run s')))
    rw [lowerWith_liftRightProgram]
    refine queriesSatisfy_simulate_channelMap Sum.inr _ ?_
    refine (hq p qE s').mono fun op hop => ?_
    cases op with
    | inl _ => trivial
    | inr cw =>
      simp only [Sum.elim_inr, WordInterface.sum] at hop ⊢
      omega

/-! ### Linking and adversary absorption -/

private theorem pmf_bind_congr_support {α β : Type} (p : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext y
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

/-- State-intertwining law between word-level execution of a lowered program against `wordHandle`
(with exported replies truncated at `L`) and lowering the typed execution `M.runFrom` against the
imported interface `iI`, whenever every encoded exported reply of `M` fits within `L`. -/
private theorem runWith_wordHandle_lowerWith_eq_runWith_lowerWith_runFrom
    {n : ℕ} {ιI ιE α : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E)
    (iI : WordInterface I) (iE : WordInterface E) (codec : StateCodec M)
    (p : PPTParam n) (L : ℕ)
    (hbound : ∀ (q : ιE) (s : (M p.secParam p.corrupted).State)
      (x : E q × (M p.secParam p.corrupted).State),
      x ∈ OracleComp.support (ProbOracleComp.lowerWith iI p.replyBound
        (((M p.secParam p.corrupted).handle q).run s)) →
      (iE.reply q x.1).length ≤ L)
    (prog : ProbOracleComp E α) {State : Type}
    (oracle : iI.Channel × List Bool → StateT State PMF (List Bool))
    (s0 : (M p.secParam p.corrupted).State) (s : State) :
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
        (fun x => ((x.1.1, (codec p.secParam p.corrupted).enc x.1.2), x.2)) := by
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
  induction prog generalizing s0 s with
  | pure a =>
    simp [ProbOracleComp.lowerWith, Machine.runFrom, OracleComp.interpret_pure]
  | liftBind q cont ih =>
    cases q with
    | inl k =>
      change ProbOracleComp.runWith oracle
          ((OracleComp.interpret H
            (ProbOracleComp.lowerWith iE L
              (ProbOracleComp.sample (ProbComp.unifFin k) >>= cont))).run (cod.enc s0)) s =
        (ProbOracleComp.runWith oracle
          (ProbOracleComp.lowerWith iI p.replyBound
            (m.runFrom (ProbOracleComp.sample (ProbComp.unifFin k) >>= cont) s0)) s).map
          (fun x => ((x.1.1, cod.enc x.1.2), x.2))
      rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample]
      rw [Machine.runFrom_bind, Machine.runFrom_sample]
      rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_map,
        ProbOracleComp.simulate_sample]
      simp only [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.interpret_sample,
        ProbComp.unifFin, OracleComp.interpret_query, H, StateT.run_lift,
        ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_pure, PMF.bind_map, PMF.map_bind, PMF.bind_bind, PMF.pure_bind,
        Function.comp_def, Prod.map_apply, id_eq]
      exact congrArg _ (funext fun a => ih a s0 s)
    | inr eQ =>
      change ProbOracleComp.runWith oracle
          ((OracleComp.interpret H
            (ProbOracleComp.lowerWith iE L
              (ProbOracleComp.query eQ >>= cont))).run (cod.enc s0)) s =
        (ProbOracleComp.runWith oracle
          (ProbOracleComp.lowerWith iI p.replyBound
            (m.runFrom (ProbOracleComp.query eQ >>= cont) s0)) s).map
          (fun x => ((x.1.1, cod.enc x.1.2), x.2))
      rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query,
        WordInterface.lowerQuery]
      rw [Machine.runFrom_bind, Machine.runFrom_query]
      rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind]
      have hwh : wordHandle M iI iE codec p (iE.channel eQ, iE.request eQ) (cod.enc s0) =
          (fun res => (iE.reply eQ res.1, cod.enc res.2)) <$>
            ProbOracleComp.lowerWith iI p.replyBound ((m.handle eQ).run s0) := by
        unfold wordHandle
        have hq : iE.decodeQuery (iE.channel eQ) (iE.request eQ) = eQ :=
          iE.decodeQuery_request eQ
        generalize iE.decodeQuery (iE.channel eQ) (iE.request eQ) = q' at hq ⊢
        subst hq
        simp only [cod, m, (codec p.secParam p.corrupted).decode_enc]
      simp only [OracleComp.interpret_bind, OracleComp.interpret_map, StateT.run_bind,
        StateT.run_map, ProbOracleComp.interpret_query, H]
      simp only [StateT.run, hwh, ProbOracleComp.lowerWith,
        ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, PMF.bind_map, PMF.map_bind,
        Function.comp_def, Prod.map, id_eq]
      refine pmf_bind_congr_support _ fun x hx => ?_
      have hsupp : x.1 ∈ OracleComp.support
          (ProbOracleComp.lowerWith iI p.replyBound ((m.handle eQ).run s0)) :=
        ProbOracleComp.mem_support_of_mem oracle hx
      have hlen : (iE.reply eQ x.1.1).length ≤ L := hbound eQ s0 x.1 hsupp
      rw [List.take_of_length_le hlen, iE.decodeReply_reply]
      exact ih x.1.1 x.1.2 x.2

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
  rcases hM with ⟨cert⟩
  rcases hMR with ⟨bound, hpoly, hle⟩
  obtain ⟨c, d, hcd⟩ := hpoly.exists_le
  let param : EnvParam → PPTParam n := fun e => ⟨e.secParam, e.replyBound, C⟩
  let cap : EnvParam → ℕ := fun e => c * ((encPPTParam n (param e)).length + 1) ^ d
  let envParam : EnvParam → EnvParam := fun e => ⟨e.secParam, cap e, e.aux⟩
  have hconst : ComputableInPolyTime (fun _ : EnvParam => C)
      encEnvParam (encFinite (Finset (Fin n))) :=
    ComputableInPolyTime.const C
  have hparam : ComputableInPolyTime param encEnvParam (encPPTParam n) := by
    fun_prop
  have hcap : ComputableInPolyTime cap encEnvParam encUnary := by
    have hpolyFn : ComputableInPolyTime (fun k : ℕ => c * (k + 1) ^ d) encUnary encUnary := by
      fun_prop
    exact hpolyFn.comp ((ComputableInPolyTime.encoding_length (encPPTParam n)).comp hparam)
  have henv : ComputableInPolyTime envParam encEnvParam encEnvParam := by
    fun_prop
  have hrun := hZ.isOraclePPTOn_runWith_wordHandle cert hparam henv
  refine hrun.congr fun e State oracle s => ?_
  simp only [wordRunWith, wordRunFromWith, Machine.link, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample, ProbOracleComp.simulate_map,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map,
    ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun s0 => ?_)
  have hfit : ∀ (q : (Fin n × In) ⊕ AdvQ)
      (st : (M (param e).secParam (param e).corrupted).State)
      (x : execSpec n In Out AdvQ AdvR q × (M (param e).secParam (param e).corrupted).State),
      x ∈ OracleComp.support (ProbOracleComp.lowerWith iI (param e).replyBound
        (((M (param e).secParam (param e).corrupted).handle q).run st)) →
      ((WordInterface.exec party adv).reply q x.1).length ≤ cap e := by
    intro q st x hx
    exact (hle (param e) q st x hx).trans (hcd (param e))
  have hstep := runWith_wordHandle_lowerWith_eq_runWith_lowerWith_runFrom M iI
    (WordInterface.exec party adv) cert.codec (param e) (cap e) hfit
    (Z (envParam e).secParam (envParam e).aux) oracle s0 s
  have hstep' := congrArg (PMF.map (Prod.map Prod.fst id)) hstep
  simp only [param, envParam, ProbOracleComp.lowerWith, PMF.map_comp] at hstep'
  exact hstep'

/-- Library infrastructure (no cited result), toward #6043 (not Proposition 7 of [Canetti2020]):
linking a strict-PPT environment against a certified machine family with polynomially bounded
replies
gives a strict-PPT environment for the machine's imported ports. -/
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

/-- Library infrastructure (no cited result), toward #6043 (not Proposition 7 of [Canetti2020]):
running a reply-bounded strict-PPT adversary inside a strict-PPT environment preserves strict
PPT. -/
theorem Environment.IsPPT.absorbAdversary
    {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    {Z : Environment n In Out AdvQ AdvR}
    {A : Adversary n AdvQ AdvR NetQ NetR}
    {party : WordPort (Fin n × In) (Option Out)}
    {net : WordPort NetQ NetR} {adv : WordPort AdvQ AdvR}
    (hZ : Z.IsPPT party adv) (hA : A.IsPPT net adv)
    (hAR : Machine.IsReplyBounded A (WordInterface.net net) (WordInterface.net adv))
    (C : Finset (Fin n)) :
    (absorbAdversary C A Z).IsPPT party net :=
  hZ.link (hA.liftAdversary (party := party)) (hAR.liftRight (iL := WordInterface.net party)) C

end Cslib.Crypto.Protocols.UC
