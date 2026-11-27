/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Adaptive
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Languages.Probabilistic.Oracle.Vector

/-!
# Distributed protocols with per-party state isolation

Library construction (no cited definition): `DistributedProtocol` compiles `n` structurally isolated
per-party local states (`Fin n → PartyState`) plus a shared network/channel state (`NetState`) into
both static `Protocol` (`UC.Execution`) and snapshot adaptive `AdaptiveProtocol` (`UC.Adaptive`).

Unlike monolithic `Protocol` and `AdaptiveProtocol` machines, where protocol authors must
manually route per-party state and supply an arbitrary `view` projection:

* `initParty` initializes each party `i : Fin n` independently via `OracleComp.pi`.
* `onInput κ i x` accesses and updates only party `i`'s own `PartyState` and the shared `NetState`.
* `onNet κ q` accesses and updates only `NetState`.
* `toAdaptive` uses the canonical per-party local-state projection `fun _ i s => s.parties i`.

## Main definitions

* `Cslib.Crypto.Protocols.UC.DistributedState`: per-party state array paired with shared
  network state.
* `Cslib.Crypto.Protocols.UC.DistributedProtocol`: protocol builder isolating per-party state.
* `Cslib.Crypto.Protocols.UC.DistributedProtocol.toMachine`, `.toProtocol`, `.toAdaptive`: compilers
  to `Machine`, static `Protocol`, and `AdaptiveProtocol`.
* `Cslib.Crypto.Protocols.UC.DistributedProtocol.PolyBounded`: polynomial call-budget witness for
  distributed protocol components.

## Main results

* `Cslib.Crypto.Protocols.UC.DistributedProtocol.toMachine_isBounded`,
  `.toProtocol_polyBounded`, `.toAdaptive_polyBounded`: call-budget propagation.
* `Cslib.Crypto.Protocols.UC.DistributedProtocol.mem_support_init_iff`,
  `.applyInitialCorruptions_parties_of_not_mem`, `.mem_support_closeEval_handle_input`,
  `.mem_support_closeEval_handle_net`: initialization and single-step local-state isolation.
* `Cslib.Crypto.Protocols.UC.DistributedProtocol.corruptRouter_runFrom_parties_eq`,
  `.execMachine_runFrom_parties_eq`, `.adaptiveRouter_runFrom_parties_eq`: end-to-end honest-party
  local-state isolation under static and adaptive corruption routing.
* `Cslib.Crypto.Protocols.UC.DistributedProtocol.toAdaptive_toStatic_of_onCorrupt_eq`: static
  round-trip compatibility.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open Polynomial (eval)

/-- Library construction (no cited definition): state of an `n`-party distributed protocol,
separating per-party local states `parties : Fin n → PartyState` from the shared network or
channel state `net : NetState`. -/
@[ext] structure DistributedState (n : ℕ) (PartyState NetState : Type) : Type where
  /-- Per-party local states indexed by party identifier. -/
  parties : Fin n → PartyState
  /-- Shared network or channel state. -/
  net : NetState

/-- Library construction (no cited definition): an `n`-party distributed protocol with
structurally isolated per-party local states.

Each party `i` initializes independently (`initParty`), interacts on input only with its own
`PartyState` and the shared `NetState` (`onInput`), and cannot directly read or modify any other
party `j ≠ i`'s local state. Adversary network queries (`onNet`) interact only with `NetState`. -/
structure DistributedProtocol (n : ℕ) (In Out NetQ NetR : Type) : Type 1 where
  /-- Local state type of each individual party. -/
  PartyState : Type
  /-- Shared network or channel state type. -/
  NetState : Type
  /-- Independent initial local-state sampler for party `i` at security parameter `κ`. -/
  initParty : ℕ → Fin n → ProbComp PartyState
  /-- Initial shared network-state sampler at security parameter `κ`. -/
  initNet : ℕ → ProbComp NetState
  /-- Party `i`'s input activation, reading and updating only `(parties i, net)`. -/
  onInput : ℕ → Fin n → In → StateT (PartyState × NetState) ProbComp (Option Out)
  /-- Adversary network activation, reading and updating only `net`. -/
  onNet : ℕ → NetQ → StateT NetState ProbComp NetR
  /-- Local state transformation applied when party `i` is corrupted (defaults to identity). -/
  onCorrupt : ℕ → Fin n → PartyState → PartyState := fun _ _ s => s

namespace DistributedProtocol

variable {n : ℕ} {In Out NetQ NetR : Type}

/-- Library construction (no cited definition): compile a `DistributedProtocol` at security
parameter `κ` into a closed `Machine` over `protocolSpec`.

Parties initialize independently via `OracleComp.pi`; party inputs update only `parties i` and
`net`; network queries update only `net`. -/
@[expose] def toMachine (P : DistributedProtocol n In Out NetQ NetR) (κ : ℕ) :
    Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR) where
  State := DistributedState n P.PartyState P.NetState
  init := do
    let parties ← OracleComp.pi (P.initParty κ)
    let net ← P.initNet κ
    return { parties, net }
  handle
    | .inl (i, x) => fun s => do
        let (out, (ps', ns')) ←
          ProbOracleComp.sample ((P.onInput κ i x).run (s.parties i, s.net))
        return (out, { parties := Function.update s.parties i ps', net := ns' })
    | .inr q => fun s => do
        let (r, ns') ← ProbOracleComp.sample ((P.onNet κ q).run s.net)
        return (r, { s with net := ns' })

/-- Library construction (no cited definition): compile a `DistributedProtocol` into a static
`Protocol` whose machine is `P.toMachine κ` (independent of the static corruption set `C`). -/
@[expose] def toProtocol (P : DistributedProtocol n In Out NetQ NetR) :
    Protocol n In Out NetQ NetR :=
  fun κ _ => P.toMachine κ

/-- Library construction (no cited definition): compile a `DistributedProtocol` into an
`AdaptiveProtocol` with canonical per-party view `fun _ i s => s.parties i` and per-party
corruption hook `P.onCorrupt`. -/
@[expose] def toAdaptive (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory := .nonErasing) :
    AdaptiveProtocol n In Out NetQ NetR P.PartyState where
  machine := P.toMachine
  view _ i s := s.parties i
  onCorrupt κ i s :=
    { s with parties := Function.update s.parties i (P.onCorrupt κ i (s.parties i)) }
  memory := mem

/-! ### Call budgets -/

/-- Library construction (no cited definition): polynomial call-budget witness for a
`DistributedProtocol`, bounding private coin draws in `initParty`, `initNet`, `onInput`, and
`onNet` by polynomials in `κ`. -/
structure PolyBounded (P : DistributedProtocol n In Out NetQ NetR)
    (pInitP pInitN pIn pNet : Polynomial ℕ) : Prop where
  /-- Per-party initialization call budget. -/
  initParty : ∀ κ i, (P.initParty κ i).IsQueryBounded (pInitP.eval κ)
  /-- Network initialization call budget. -/
  initNet : ∀ κ, (P.initNet κ).IsQueryBounded (pInitN.eval κ)
  /-- Per-activation party input call budget. -/
  onInput : ∀ κ i x ps ns, ((P.onInput κ i x).run (ps, ns)).IsQueryBounded (pIn.eval κ)
  /-- Per-activation network query call budget. -/
  onNet : ∀ κ q ns, ((P.onNet κ q).run ns).IsQueryBounded (pNet.eval κ)

/-- Library infrastructure (no cited result): if each initialization and activation component of
`P` is call-bounded, then `P.toMachine κ` is call-bounded by `n * bInitP + bInitN + bIn + bNet`. -/
theorem toMachine_isBounded (P : DistributedProtocol n In Out NetQ NetR)
    {κ bInitP bInitN bIn bNet : ℕ}
    (hInitP : ∀ i, (P.initParty κ i).IsQueryBounded bInitP)
    (hInitN : (P.initNet κ).IsQueryBounded bInitN)
    (hIn : ∀ i x ps ns, ((P.onInput κ i x).run (ps, ns)).IsQueryBounded bIn)
    (hNet : ∀ q ns, ((P.onNet κ q).run ns).IsQueryBounded bNet) :
    (P.toMachine κ).IsBounded (n * bInitP + bInitN + bIn + bNet) := by
  refine ⟨?_, fun q s => ?_⟩
  · refine ((OracleComp.isCostBounded_pi hInitP).bind fun _ =>
      hInitN.bind fun _ => .pure _ 0).mono ?_
    omega
  · rcases q with ⟨i, x⟩ | q
    · refine ((Machine.isQueryBounded_sample (hIn i x (s.parties i) s.net)).bind fun _ =>
        .pure _ 0).mono ?_
      omega
    · refine ((Machine.isQueryBounded_sample (hNet q s.net)).bind fun _ =>
        .pure _ 0).mono ?_
      omega

/-- Library infrastructure (no cited result): polynomial call budgets of a `DistributedProtocol`
propagate to `P.toProtocol`. -/
theorem toProtocol_polyBounded {P : DistributedProtocol n In Out NetQ NetR}
    {pInitP pInitN pIn pNet : Polynomial ℕ}
    (h : P.PolyBounded pInitP pInitN pIn pNet) :
    P.toProtocol.PolyBounded (Polynomial.C n * pInitP + pInitN + pIn + pNet) := fun κ _ => by
  simpa only [toProtocol, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    P.toMachine_isBounded (h.initParty κ) (h.initNet κ) (h.onInput κ) (h.onNet κ)

/-- Library infrastructure (no cited result): polynomial call budgets of a `DistributedProtocol`
propagate to `P.toAdaptive mem`. -/
theorem toAdaptive_polyBounded {P : DistributedProtocol n In Out NetQ NetR}
    {pInitP pInitN pIn pNet : Polynomial ℕ}
    (h : P.PolyBounded pInitP pInitN pIn pNet) (mem : PartyMemory := .nonErasing) :
    (P.toAdaptive mem).PolyBounded (Polynomial.C n * pInitP + pInitN + pIn + pNet) := fun κ => by
  simpa only [toAdaptive, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    P.toMachine_isBounded (h.initParty κ) (h.initNet κ) (h.onInput κ) (h.onNet κ)

/-! ### Initialization and single-step local-state isolation -/

/-- Library infrastructure (no cited result): a distributed state is in the support of
`(P.toMachine κ).init` iff each party's local state is in its independent initializer's support
and `net` is in `initNet`'s support. -/
theorem mem_support_init_iff (P : DistributedProtocol n In Out NetQ NetR) (κ : ℕ)
    (s : DistributedState n P.PartyState P.NetState) :
    s ∈ (ProbComp.eval (P.toMachine κ).init).support ↔
      (∀ i, s.parties i ∈ (ProbComp.eval (P.initParty κ i)).support) ∧
        s.net ∈ (ProbComp.eval (P.initNet κ)).support := by
  change s ∈ (ProbComp.eval ((OracleComp.pi (P.initParty κ)) >>= fun parties =>
    P.initNet κ >>= fun net => pure { parties, net })).support ↔ _
  erw [ProbComp.eval_bind, PMF.mem_support_bind_iff]
  constructor
  · rintro ⟨parties, hparties, hnet⟩
    erw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnet
    obtain ⟨net, hnet', hs⟩ := hnet
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hs
    subst hs
    exact ⟨(ProbComp.mem_support_pi_iff _ _).mp hparties, hnet'⟩
  · rintro ⟨hparties, hnet⟩
    refine ⟨s.parties, (ProbComp.mem_support_pi_iff _ _).mpr hparties, ?_⟩
    erw [ProbComp.eval_bind, PMF.mem_support_bind_iff]
    refine ⟨s.net, hnet, ?_⟩
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff]

/-- Library infrastructure (no cited result): corrupting party `i` leaves every other party
`j ≠ i`'s local state unchanged. -/
theorem toAdaptive_onCorrupt_parties_ne (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) {i j : Fin n} (hji : j ≠ i)
    (s : DistributedState n P.PartyState P.NetState) :
    ((P.toAdaptive mem).onCorrupt κ i s).parties j = s.parties j :=
  Function.update_of_ne hji _ _

/-- Library infrastructure (no cited result): corrupting party `i` leaves `net` unchanged. -/
@[simp] theorem toAdaptive_onCorrupt_net (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) (i : Fin n)
    (s : DistributedState n P.PartyState P.NetState) :
    ((P.toAdaptive mem).onCorrupt κ i s).net = s.net := rfl

private theorem foldl_onCorrupt_parties_of_not_mem (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) (C₀ : Finset (Fin n)) {j : Fin n} (hj : j ∉ C₀)
    (l : List (Fin n)) (s : DistributedState n P.PartyState P.NetState) :
    (l.foldl (fun acc i => if i ∈ C₀ then (P.toAdaptive mem).onCorrupt κ i acc else acc) s).parties
      j = s.parties j := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
    refine (ih (if i ∈ C₀ then (P.toAdaptive mem).onCorrupt κ i s else s)).trans ?_
    by_cases hi : i ∈ C₀
    · simp only [hi, ↓reduceIte]
      exact P.toAdaptive_onCorrupt_parties_ne mem κ (fun (h : j = i) => hj (h ▸ hi)) s
    · simp only [hi, ↓reduceIte]

private theorem foldl_onCorrupt_net (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) (C₀ : Finset (Fin n))
    (l : List (Fin n)) (s : DistributedState n P.PartyState P.NetState) :
    (l.foldl (fun acc i => if i ∈ C₀ then (P.toAdaptive mem).onCorrupt κ i acc else acc) s).net =
      s.net := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
    refine (ih (if i ∈ C₀ then (P.toAdaptive mem).onCorrupt κ i s else s)).trans ?_
    by_cases hi : i ∈ C₀ <;> simp only [hi, ↓reduceIte]
    exact P.toAdaptive_onCorrupt_net mem κ i s

/-- Library infrastructure (no cited result): initial corruptions `C₀` leave every uncorrupted
party `j ∉ C₀`'s local state unchanged. -/
theorem applyInitialCorruptions_parties_of_not_mem (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) (C₀ : Finset (Fin n)) {j : Fin n} (hj : j ∉ C₀)
    (s : DistributedState n P.PartyState P.NetState) :
    ((P.toAdaptive mem).applyInitialCorruptions κ C₀ s).parties j = s.parties j :=
  P.foldl_onCorrupt_parties_of_not_mem mem κ C₀ hj (List.finRange n) s

/-- Library infrastructure (no cited result): initial corruptions leave the shared network state
`net` unchanged. -/
theorem applyInitialCorruptions_net (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) (C₀ : Finset (Fin n))
    (s : DistributedState n P.PartyState P.NetState) :
    ((P.toAdaptive mem).applyInitialCorruptions κ C₀ s).net = s.net :=
  P.foldl_onCorrupt_net mem κ C₀ (List.finRange n) s

/-- Library infrastructure (no cited result): activating party `i` leaves every other party
`j ≠ i`'s local state unchanged on every supported outcome. -/
theorem mem_support_closeEval_handle_input (P : DistributedProtocol n In Out NetQ NetR)
    (κ : ℕ) (i : Fin n) (x : In) (s : DistributedState n P.PartyState P.NetState)
    {y : Option Out × DistributedState n P.PartyState P.NetState}
    (hy : y ∈ (Machine.closeEval (((P.toMachine κ).handle (.inl (i, x))).run s)).support) :
    ∀ {j : Fin n}, j ≠ i → y.2.parties j = s.parties j := by
  intro j hji
  change y ∈ (Machine.closeEval (ProbOracleComp.sample ((P.onInput κ i x).run (s.parties i, s.net))
    >>= fun (out, (ps', ns')) =>
      pure (out, { parties := Function.update s.parties i ps', net := ns' }))).support at hy
  rw [Machine.mem_support_closeEval_bind] at hy
  obtain ⟨⟨out, ps', ns'⟩, _, hy'⟩ := hy
  rw [Machine.mem_support_closeEval_pure] at hy'
  rw [hy']
  exact Function.update_of_ne hji _ _

/-- Library infrastructure (no cited result): a network query leaves every party's local state
unchanged on every supported outcome. -/
theorem mem_support_closeEval_handle_net (P : DistributedProtocol n In Out NetQ NetR)
    (κ : ℕ) (q : NetQ) (s : DistributedState n P.PartyState P.NetState)
    {y : NetR × DistributedState n P.PartyState P.NetState}
    (hy : y ∈ (Machine.closeEval (((P.toMachine κ).handle (.inr q)).run s)).support) :
    y.2.parties = s.parties := by
  change y ∈ (Machine.closeEval (ProbOracleComp.sample ((P.onNet κ q).run s.net)
    >>= fun (r, ns') => pure (r, { s with net := ns' }))).support at hy
  rw [Machine.mem_support_closeEval_bind] at hy
  obtain ⟨⟨r, ns'⟩, _, hy'⟩ := hy
  rw [Machine.mem_support_closeEval_pure] at hy'
  rw [hy']

/-! ### End-to-end execution honest-party isolation -/

/-- Library infrastructure (no cited result): under static `corruptRouter C (P.toMachine κ)`,
for any honest party `j ∉ C` and any program `prog` that never queries party `j` directly on the
party port, `j`'s local state `s.parties j` is invariant across the entire `Machine.runFrom`
execution (even under arbitrary corrupted-party activations and network queries). -/
theorem corruptRouter_runFrom_parties_eq (P : DistributedProtocol n In Out NetQ NetR)
    (κ : ℕ) (C : Finset (Fin n)) (j : Fin n) (hj : j ∉ C) {α : Type}
    (prog : ProbOracleComp
      (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) α)
    (hprog : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => ∀ x, q ≠ .inl (j, x)) prog)
    (s : DistributedState n P.PartyState P.NetState)
    {y : α × DistributedState n P.PartyState P.NetState}
    (hy : y ∈ (Machine.closeEval ((corruptRouter C (P.toMachine κ)).runFrom prog s)).support) :
    y.2.parties j = s.parties j := by
  symm
  refine Machine.mem_support_closeEval_runFrom_invariant (corruptRouter C (P.toMachine κ))
    (fun q => ∀ x, q ≠ .inl (j, x)) (fun s₁ s₂ => s₁.parties j = s₂.parties j)
    (fun _ => rfl) (fun h₁ h₂ => h₁.trans h₂) prog hprog s hy ?_
  intro q s' y' hq hy'
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | nq⟩
  · by_cases hi : i ∈ C
    · simp only [corruptRouter, hi, ↓reduceIte] at hy'
      change y' ∈ (Machine.closeEval (pure (none, s'))).support at hy'
      rw [Machine.mem_support_closeEval_pure] at hy'
      rw [hy']
    · have hji : j ≠ i := fun h => hq x (congrArg (fun k => Sum.inl (k, x)) h.symm)
      simp only [corruptRouter, hi, ↓reduceIte] at hy'
      exact (P.mem_support_closeEval_handle_input κ i x s' hy' hji).symm
  · by_cases hi : i ∈ C
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp only [corruptRouter, hi, ↓reduceIte] at hy'
      dsimp only [Functor.map, StateT.map] at hy'
      erw [Machine.mem_support_closeEval_bind] at hy'
      obtain ⟨z, hz, hy''⟩ := hy'
      erw [Machine.mem_support_closeEval_pure] at hy''
      rw [hy'']
      exact (P.mem_support_closeEval_handle_input κ i x s' hz hji).symm
    · simp only [corruptRouter, hi, ↓reduceIte] at hy'
      change y' ∈ (Machine.closeEval (pure (Sum.inl none, s'))).support at hy'
      rw [Machine.mem_support_closeEval_pure] at hy'
      rw [hy']
  · simp only [corruptRouter] at hy'
    dsimp only [Functor.map, StateT.map] at hy'
    erw [Machine.mem_support_closeEval_bind] at hy'
    obtain ⟨z, hz, hy''⟩ := hy'
    erw [Machine.mem_support_closeEval_pure] at hy''
    rw [hy'']
    exact congrFun (P.mem_support_closeEval_handle_net κ nq s' hz).symm j

private theorem queriesSatisfy_liftAdversary_runFrom {AdvQ AdvR : Type}
    (A : Machine (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) (netSpec AdvQ AdvR))
    (j : Fin n) {α : Type} (prog : ProbOracleComp (execSpec n In Out AdvQ AdvR) α)
    (hprog : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => ∀ x, q ≠ .inl (j, x)) prog)
    (sA : A.State) :
    OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => ∀ x, q ≠ .inl (j, x))
      ((liftAdversary (n := n) (In := In) (Out := Out) A).runFrom prog sA) := by
  induction prog using OracleComp.induction generalizing sA with
  | pure a =>
    erw [Machine.runFrom_pure]
    exact OracleComp.QueriesSatisfy.pure _
  | query_bind q cont ih =>
    erw [OracleComp.QueriesSatisfy.liftBind_iff] at hprog
    rcases hprog with ⟨hq, hcont⟩
    erw [PFunctor.FreeM.bind_eq_bind, Machine.runFrom_bind]
    refine OracleComp.QueriesSatisfy.bind ?_ fun p => ih p.1 (by simpa using hcont p.1) p.2
    rcases q with k | (⟨i, x⟩ | a)
    · dsimp only [Machine.runFrom, liftAdversary, Machine.liftRight]
      change OracleComp.QueriesSatisfy _ ((fun a => (a, sA)) <$> OracleComp.query (Sum.inl k))
      rw [OracleComp.queriesSatisfy_map_iff]
      exact OracleComp.QueriesSatisfy.query trivial
    · erw [Machine.runFrom_query]
      change OracleComp.QueriesSatisfy _
        ((fun r => (r, sA)) <$> OracleComp.query (Sum.inr (Sum.inl (i, x))))
      rw [OracleComp.queriesSatisfy_map_iff]
      exact OracleComp.QueriesSatisfy.query
        (fun x' h => hq x' (by simp only [Sum.inl.injEq] at h ⊢; exact h))
    · erw [Machine.runFrom_query]
      change OracleComp.QueriesSatisfy _
        (Machine.liftRightProgram (partySpec n In Out) ((A.handle a).run sA))
      refine OracleComp.IsCostBounded.interpret (cost := fun _ => 0) (fun q' => ?_)
        (OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun _ => rfl) _)
      rcases q' with k | q'
      · exact OracleComp.QueriesSatisfy.query trivial
      · exact OracleComp.QueriesSatisfy.query (fun x => by simp)

/-- Library infrastructure (no cited result): in the full static UC execution machine
`execMachine P.toProtocol A κ C`, for any honest party `j ∉ C` and any environment program
`prog` that never queries party `j` directly, `j`'s local state `parties j` is invariant across
`Machine.runFrom`, regardless of adversary `A`'s behavior. -/
theorem execMachine_runFrom_parties_eq (P : DistributedProtocol n In Out NetQ NetR)
    {AdvQ AdvR : Type} (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
    (κ : ℕ) (C : Finset (Fin n)) (j : Fin n) (hj : j ∉ C) {α : Type}
    (prog : ProbOracleComp (execSpec n In Out AdvQ AdvR) α)
    (hprog : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => ∀ x, q ≠ .inl (j, x)) prog)
    (sA : (A κ C).State) (sP : DistributedState n P.PartyState P.NetState)
    {a : α} {sA' : (A κ C).State} {sP' : DistributedState n P.PartyState P.NetState}
    (hy : (a, sA', sP') ∈ (Machine.closeEval
      ((execMachine P.toProtocol A κ C).runFrom prog (sA, sP))).support) :
    sP'.parties j = sP.parties j := by
  dsimp only [execMachine, toProtocol] at hy
  erw [Machine.runFrom_comp, Machine.closeEval_map, PMF.mem_support_map_iff] at hy
  obtain ⟨⟨⟨a₀, sA₀⟩, sP₀⟩, hz, h_eq⟩ := hy
  cases h_eq
  exact P.corruptRouter_runFrom_parties_eq κ C j hj _
    (queriesSatisfy_liftAdversary_runFrom (A κ C) j prog hprog sA) sP hz

/-- Library infrastructure (no cited result): under `adaptiveRouter mode (P.toAdaptive mem) κ C₀`,
for any initially uncorrupted party `j ∉ s.corrupted` and any program `prog` that neither
activates `j` on the environment party port nor corrupts `j`, `j` remains uncorrupted and `j`'s
local state `inner.parties j` is invariant across the entire `Machine.runFrom` execution in both
`.static` and `.adaptive` modes. -/
theorem adaptiveRouter_runFrom_parties_eq (P : DistributedProtocol n In Out NetQ NetR)
    (mode : CorruptionMode) (mem : PartyMemory) (κ : ℕ) (C₀ : Finset (Fin n))
    (j : Fin n) {α : Type}
    (prog : ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR P.PartyState) α)
    (hprog : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => (∀ x, q ≠ .inl (.party j x)) ∧ q ≠ .inr (.corrupt j))
      prog)
    (s : AdaptiveRouterState (DistributedState n P.PartyState P.NetState) P.PartyState n)
    (hj : j ∉ s.corrupted)
    {y : α × AdaptiveRouterState (DistributedState n P.PartyState P.NetState) P.PartyState n}
    (hy : y ∈ (Machine.closeEval
      ((adaptiveRouter mode (P.toAdaptive mem) κ C₀).runFrom prog s)).support) :
    j ∉ y.2.corrupted ∧ y.2.inner.parties j = s.inner.parties j := by
  have hR := Machine.mem_support_closeEval_runFrom_invariant
    (adaptiveRouter mode (P.toAdaptive mem) κ C₀)
    (fun q => (∀ x, q ≠ .inl (.party j x)) ∧ q ≠ .inr (.corrupt j))
    (fun s₁ s₂ => j ∉ s₁.corrupted → j ∉ s₂.corrupted ∧ s₂.inner.parties j = s₁.inner.parties j)
    (fun _ h => ⟨h, rfl⟩)
    (fun h₁₂ h₂₃ h => let ⟨hb, hpb⟩ := h₁₂ h; let ⟨hc, hpc⟩ := h₂₃ hb; ⟨hc, hpc.trans hpb⟩)
    prog hprog s hy ?_
  · exact hR hj
  · intro q s' y' hq hy' hj'
    rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | nq)
    · have hji : j ≠ i :=
        fun h => hq.1 x (congrArg (fun k => Sum.inl (AdaptivePartyQ.party k x)) h.symm)
      by_cases hi : i ∈ s'.corrupted
      · simp only [adaptiveRouter, hi, ↓reduceIte, StateT.run] at hy'
        erw [Machine.mem_support_closeEval_pure] at hy'
        rw [hy']
        exact ⟨hj', rfl⟩
      · simp only [adaptiveRouter, hi, ↓reduceIte, StateT.run] at hy'
        erw [Machine.mem_support_closeEval_bind] at hy'
        obtain ⟨⟨out, s''⟩, hs'', hy''⟩ := hy'
        erw [Machine.mem_support_closeEval_pure] at hy''
        rw [hy'']
        exact ⟨hj', P.mem_support_closeEval_handle_input κ i x s'.inner hs'' hji⟩
    · simp only [adaptiveRouter, StateT.run] at hy'
      erw [Machine.mem_support_closeEval_pure] at hy'
      rw [hy']
      exact ⟨hj', rfl⟩
    · by_cases hi : i ∈ s'.corrupted
      · have hji : j ≠ i := fun h => hj' (h ▸ hi)
        simp only [adaptiveRouter, hi, ↓reduceIte, StateT.run] at hy'
        erw [Machine.mem_support_closeEval_bind] at hy'
        obtain ⟨⟨out, s''⟩, hs'', hy''⟩ := hy'
        erw [Machine.mem_support_closeEval_pure] at hy''
        rw [hy'']
        exact ⟨hj', P.mem_support_closeEval_handle_input κ i x s'.inner hs'' hji⟩
      · simp only [adaptiveRouter, hi, ↓reduceIte, StateT.run] at hy'
        erw [Machine.mem_support_closeEval_pure] at hy'
        rw [hy']
        exact ⟨hj', rfl⟩
    · have hji : j ≠ i :=
        fun h => hq.2 (congrArg (fun k => Sum.inr (AdaptiveNetQ.corrupt k)) h.symm)
      cases mode with
      | static =>
        simp only [adaptiveRouter, StateT.run] at hy'
        split_ifs at hy' <;> erw [Machine.mem_support_closeEval_pure] at hy' <;> rw [hy'] <;>
          exact ⟨hj', rfl⟩
      | adaptive =>
        simp only [adaptiveRouter, StateT.run] at hy'
        erw [Machine.mem_support_closeEval_pure] at hy'
        rw [hy']
        by_cases hi : i ∈ s'.corrupted
        · simp only [hi, ↓reduceIte]
          exact ⟨hj', trivial⟩
        · simp only [hi, ↓reduceIte, Finset.mem_insert, not_or]
          exact ⟨⟨hji, hj'⟩, P.toAdaptive_onCorrupt_parties_ne mem κ hji s'.inner⟩
    · simp only [adaptiveRouter, StateT.run] at hy'
      erw [Machine.mem_support_closeEval_bind] at hy'
      obtain ⟨⟨r, s''⟩, hs'', hy''⟩ := hy'
      erw [Machine.mem_support_closeEval_pure] at hy''
      rw [hy'']
      exact ⟨hj', congrFun (P.mem_support_closeEval_handle_net κ nq s'.inner hs'') j⟩

/-- Library infrastructure (no cited result): under `P.toAdaptive mem`, the canonical
corruption report's `current` field for party `i` is `s.inner.parties i`. -/
@[simp] theorem toAdaptive_corruptionReport_current (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (κ : ℕ) (i : Fin n)
    (s : AdaptiveRouterState (DistributedState n P.PartyState P.NetState) P.PartyState n) :
    ((P.toAdaptive mem).corruptionReport κ i s).current = s.inner.parties i := rfl

/-- Library infrastructure (no cited result): when `P.onCorrupt` is the identity, converting
`P.toAdaptive mem` back to a static protocol yields `P.toProtocol`. -/
theorem toAdaptive_toStatic_of_onCorrupt_eq (P : DistributedProtocol n In Out NetQ NetR)
    (mem : PartyMemory) (hon : ∀ κ i ps, P.onCorrupt κ i ps = ps) :
    (P.toAdaptive mem).toStatic = P.toProtocol := by
  funext κ C
  have hid : (P.toAdaptive mem).applyInitialCorruptions κ C = id := by
    funext s
    have hstep : ∀ (l : List (Fin n)) (s' : DistributedState n P.PartyState P.NetState),
        l.foldl (fun acc i => if i ∈ C then (P.toAdaptive mem).onCorrupt κ i acc else acc) s' =
          s' := by
      intro l s'
      induction l generalizing s' with
      | nil => rfl
      | cons i l ih =>
        refine (ih (if i ∈ C then (P.toAdaptive mem).onCorrupt κ i s' else s')).trans ?_
        by_cases hi : i ∈ C
        · simp only [hi, ↓reduceIte]
          apply DistributedState.ext
          · funext k
            by_cases hk : k = i
            · subst hk; simp [toAdaptive, hon]
            · exact P.toAdaptive_onCorrupt_parties_ne mem κ hk s'
          · rfl
        · simp only [hi, ↓reduceIte]
          rfl
    exact hstep (List.finRange n) s
  have hid' : (P.toAdaptive mem).applyInitialCorruptions κ C <$> (P.toMachine κ).init =
      (P.toMachine κ).init := by
    erw [hid, id_map]
  change Machine.mk ((P.toAdaptive mem).machine κ).State
    ((P.toAdaptive mem).applyInitialCorruptions κ C <$> (P.toMachine κ).init)
    (P.toMachine κ).handle = P.toProtocol κ C
  rw [hid']
  dsimp only [toAdaptive, toProtocol]

end DistributedProtocol

end Cslib.Crypto.Protocols.UC
