/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Membership tally with same-input walk calls

The membership scan visits candidate vertices in increasing rank order. It chooses whether
to check a walk for each candidate. One suspended call retains the cursor and the tally while
the walk reads the original input. A return records the difference between the initial and
remaining walk budgets. When all candidates have been processed, the tally comparison reports
the membership bit, with a passing negative result distinct from rejection.

## Main definitions

* `Turing.DoubleCounting.MembershipTally.machine`: one membership scan using a supplied walk.
* `Turing.DoubleCounting.MembershipTally.withBoundedWalk`: the scan with the canonical bounded
  walk reading the original input.

## Main results

* `Turing.DoubleCounting.MembershipTally.withBoundedWalk_native_firstHalting_iff`: exactly one
  accepting native occurrence list for the selectors of each passing typed scan.

The native scanner fixes the graph dimension and adjacency clock. Its query parameters are
input-dependent. The branch correspondence is for one membership query.
-/

public section

namespace Turing.DoubleCounting.MembershipTally

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace

/-- Runtime parameters for a membership query. -/
structure Context where
  /-- Number of vertices. -/
  size : ℕ
  /-- Rank of the start vertex. -/
  source : ℕ
  /-- Rank whose membership is queried. -/
  target : ℕ
  /-- Maximum length of each candidate walk. -/
  radius : ℕ
  /-- Required number and total length of the selected walks. -/
  expected : Tally

/-- Binary graph dimensions, endpoint ranks, and required tally. -/
enc_structure encContext : Context where
  size : encNat, source : encNat, target : encNat, radius : encNat, expected : encTally

/-- Binary tally followed by the membership bit. -/
enc_structure encResult : Scan.Result where tally : encTally, hit : encBool

/-- Registers retained between and during candidate walks. -/
structure Registers where
  /-- Parameters retained across all calls. -/
  context : Context
  /-- Rank of the next candidate or the candidate currently being checked. -/
  cursor : ℕ
  /-- Tally for the already processed candidates. -/
  observed : Scan.Result

/-- Encode the context, cursor, and observed tally. -/
enc_structure encRegisters : Registers where
  context : encContext, cursor : encNat, observed : encResult

/-- Boundary, in-progress walk, or terminal membership verdict. -/
abbrev State (τ : Type) := Registers ⊕ ((Registers × τ) ⊕ Option Bool)

/-- Encode the phase and retain the complete suspended registers and callee state. -/
def encState {τ : Type} (encT : τ ↪ List Bool) : State τ ↪ List Bool :=
  encSum encRegisters (encSum (encPair encRegisters encT) (encOption encBool))

/-- Enter a query at the first candidate with an empty tally. -/
@[expose] def initial {τ : Type} (ctx : Context) : State τ :=
  .inl ⟨ctx, 0, Scan.Result.zero⟩

/-- Advance after skipping the current candidate. -/
@[expose] def Registers.skip (r : Registers) : Registers :=
  { r with cursor := r.cursor + 1 }

/-- Advance after checking the current candidate's walk. -/
@[expose] def Registers.record (r : Registers) (remaining : ℕ) : Registers :=
  { r.skip with
    observed := r.observed.recordWalk r.context.radius remaining (r.cursor == r.context.target) }

/-- The tally never counts more candidates or walk length than the processed prefix allows. -/
def Registers.Bounded (r : Registers) : Prop :=
  r.cursor ≤ r.context.size ∧
    r.observed.tally.count ≤ r.cursor ∧
    r.observed.tally.lengthSum ≤ r.cursor * r.context.radius

private theorem initial_bounded (ctx : Context) :
    (⟨ctx, 0, Scan.Result.zero⟩ : Registers).Bounded := by
  simp [Registers.Bounded, Scan.Result.zero]

private theorem Registers.Bounded.skip {r : Registers} (h : r.Bounded)
    (hlive : r.cursor < r.context.size) : r.skip.Bounded := by
  rcases h with ⟨_, hc, hs⟩
  refine ⟨Nat.succ_le_of_lt hlive, hc.trans (Nat.le_succ _), ?_⟩
  exact hs.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

private theorem Registers.Bounded.record {r : Registers} (h : r.Bounded)
    (hlive : r.cursor < r.context.size) (remaining : ℕ) : (r.record remaining).Bounded := by
  rcases h with ⟨_, hc, hs⟩
  refine ⟨Nat.succ_le_of_lt hlive, Nat.succ_le_succ hc, ?_⟩
  exact (Nat.add_le_add hs (Nat.sub_le _ _)).trans_eq (Nat.succ_mul _ _).symm

private theorem skip_inSpace :
    ComputableInSpace Registers.skip encRegisters encRegisters (fun r => (encRegisters r).length) :=
  let h := budget_id (enc := encRegisters) (.refl _)
  encRegisters_mk_budget (encRegisters_context_budget h)
    (budget_natSucc (encRegisters_cursor_budget h)) (encRegisters_observed_budget h)

private theorem record_inSpace :
    ComputableInSpace (fun p : Registers × ℕ => p.1.record p.2)
      (encPair encRegisters encNat) encRegisters
      (fun p => (encPair encRegisters encNat p).length) := by
    have hr := fst encRegisters encNat
    have hc := encRegisters_context_budget hr
    have hi := encRegisters_cursor_budget hr
    have ho := encRegisters_observed_budget hr
    have ht := encResult_tally_budget ho
    have hcount := budget_natSucc (encTally_count_budget ht)
    have hspent := budget_natSub (encContext_radius_budget hc) (snd encRegisters encNat)
    have hsum := budget_natAdd (encTally_lengthSum_budget ht) hspent
    have hhit := budget_boolOr (encResult_hit_budget ho)
      (budget_natEq hi (encContext_target_budget hc))
    exact encRegisters_mk_budget hc (budget_natSucc hi)
      (encResult_mk_budget (encTally_mk_budget hcount hsum) hhit)

/-- Read the membership bit from a successful tally. A rejected tally or a live state
has no result. -/
@[expose] def reply {τ : Type} : State τ → Option Bool
  | .inr (.inr result) => result
  | _ => none

/-- A successful reply identifies the terminal state and preserves its membership bit. -/
theorem reply_eq_some_iff {τ : Type} (s : State τ) (hit : Bool) :
    reply s = some hit ↔ s = .inr (.inr (some hit)) := by
  rcases s with r | (pending | result) <;> simp [reply]

/-- Select candidates and call the supplied walk on the original input. At return and at the
terminal check only the false choice can succeed. A successful negative reply accepts as a
callback occurrence and carries the terminal value `some false`. -/
@[expose] def machine {τ : Type} (ctx : Context) (walk : NondeterministicQueryMachine τ)
    (enter : Registers → τ) (result : τ → Option ℕ) : NondeterministicQueryMachine (State τ) where
  init := initial ctx
  query
    | .inr (.inl (_, s)) => walk.query s
    | _ => 0
  next
    | (.inl r, _, choice) =>
      if r.cursor < r.context.size then
        if choice then .inr (.inl (r, enter r)) else .inl r.skip
      else
        .inr (.inr (if choice then none else r.observed.finish r.context.expected))
    | (.inr (.inl (r, s)), read, choice) =>
      if walk.halted s then
        if choice then .inr (.inr none)
        else match result s with
          | none => .inr (.inr none)
          | some remaining => .inl (r.record remaining)
      else
        .inr (.inl (r, walk.next (s, read, choice)))
    | (.inr (.inr hit), _, _) => .inr (.inr hit)
  halted
    | .inr (.inr _) => true
    | _ => false
  accept s := (reply s).isSome

/-- Initialize the empty tally in workspace linear in the encoded query parameters. -/
theorem initial_inSpace {τ : Type} (encT : τ ↪ List Bool) :
    ComputableInSpace (initial (τ := τ)) encContext (encState encT)
      (fun ctx => (encContext ctx).length) := by
  have hc := budget_id (enc := encContext) (.refl _)
  have hcursor := budget_const (encIn := encContext) (encB := encNat) 0 (.refl _)
  have hresult := budget_const (encIn := encContext) (encB := encResult)
    Scan.Result.zero (.refl _)
  have htag := of_inO (ComputableInO.inl encRegisters
    (encSum (encPair encRegisters encT) (encOption encBool)))
  have hinit := budget_comp_linear htag (encRegisters_mk_budget hc hcursor hresult)
  exact hinit

/-- The query is the active walk's read position, or zero between calls. -/
theorem query_inSpace {τ : Type} (encT : τ ↪ List Bool) (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (hq : ComputableInSpace walk.query encT encNat (fun t => (encT t).length)) :
    ComputableInSpace (machine ctx walk enter result).query (encState encT) encNat
      (fun s => (encState encT s).length) := by
  have hwalk := budget_comp_linear hq (snd encRegisters encT)
  have hother := budget_const (encIn := encOption encBool) (encB := encNat) 0 (.refl _)
  have hstart := budget_const (encIn := encRegisters) (encB := encNat) 0 (.refl _)
  exact (sumElim hstart (sumElim hwalk hother)).of_enc_eq fun
    | .inl _ | .inr (.inl _) | .inr (.inr _) => rfl

/-- The halt test reads only the phase tag. -/
theorem halted_inSpace {τ : Type} (encT : τ ↪ List Bool) (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ) :
    ComputableInSpace (machine ctx walk enter result).halted (encState encT) encBool
      (fun s => (encState encT s).length) := by
  have hs := budget_const (encIn := encRegisters) (encB := encBool) false (.refl _)
  have hw := budget_const (encIn := encPair encRegisters encT) (encB := encBool) false (.refl _)
  have hf := budget_const (encIn := encOption encBool) (encB := encBool) true (.refl _)
  exact (sumElim hs (sumElim hw hf)).of_enc_eq fun
    | .inl _ | .inr (.inl _) | .inr (.inr _) => rfl

/-- Decode the optional terminal membership bit in linear workspace. -/
theorem reply_inSpace {τ : Type} (encT : τ ↪ List Bool) :
    ComputableInSpace reply (encState encT) (encOption encBool)
      (fun s => (encState encT s).length) := by
  have hs := budget_const (encIn := encRegisters) (encB := encOption encBool) none (.refl _)
  have hw := budget_const (encIn := encPair encRegisters encT) (encB := encOption encBool)
    none (.refl _)
  have hf := budget_id (enc := encOption encBool) (.refl _)
  exact (sumElim hs (sumElim hw hf)).of_enc_eq fun
    | .inl _ | .inr (.inl _) | .inr (.inr _) => rfl

/-- Acceptance is the presence of a membership bit at the terminal boundary. -/
theorem accept_inSpace {τ : Type} (encT : τ ↪ List Bool) (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ) :
    ComputableInSpace (machine ctx walk enter result).accept (encState encT) encBool
      (fun s => (encState encT s).length) :=
  budget_optionIsSome (reply_inSpace encT)

/-- Stepping a tally uses native linear workspace in its encoded state and supplied read and
choice, given linear-space walk entry, step, halt, and result operations. -/
theorem next_inSpace {τ : Type} (encT : τ ↪ List Bool) (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (he : ComputableInSpace enter encRegisters encT (fun r => (encRegisters r).length))
    (hn : ComputableInSpace walk.next (encPair encT (encPair (encOption encBool) encBool)) encT
      (fun p => (encPair encT (encPair (encOption encBool) encBool) p).length))
    (hh : ComputableInSpace walk.halted encT encBool (fun t => (encT t).length))
    (hr : ComputableInSpace result encT (encOption encNat) (fun t => (encT t).length)) :
    ComputableInSpace (machine ctx walk enter result).next
      (encPair (encState encT) (encPair (encOption encBool) encBool)) (encState encT)
      (fun p => (encPair (encState encT) (encPair (encOption encBool) encBool) p).length) := by
  let encRead := encPair (encOption encBool) encBool
  let encWalk := encPair encRegisters encT
  let encDone := encOption encBool
  let encInner := encSum encWalk encDone
  have select := of_inO (ComputableInO.inl encRegisters encInner)
  have active := of_inO (ComputableInO.inr encRegisters encInner)
  have enterTag := of_inO (ComputableInO.inl encWalk encDone)
  have stopTag := of_inO (ComputableInO.inr encWalk encDone)
  have running := budget_comp_linear active enterTag
  have finished := budget_comp_linear active stopTag
  have hr₀ := fst encRegisters encRead
  have hb₀ := snd' (snd encRegisters encRead)
  have hctx := encRegisters_context_budget hr₀
  have hobs := encRegisters_observed_budget hr₀
  have hfinish := budget_comp_linear matches_inSpace
    (budget_prod (encResult_tally_budget hobs) (encContext_expected_budget hctx))
  have hno₀ := budget_const (encIn := encPair encRegisters encRead) (encB := encDone) none (.refl _)
  have hhit := budget_ite hfinish (budget_optionSome (encResult_hit_budget hobs)) hno₀
  have hstop := budget_comp_linear finished (budget_ite hb₀ hno₀ hhit)
  have hsize := budget_natLt (encRegisters_cursor_budget hr₀) (encContext_size_budget hctx)
  have hskip := budget_comp_linear select (budget_comp_linear skip_inSpace hr₀)
  have henter := budget_comp_linear running (budget_prod hr₀ (budget_comp_linear he hr₀))
  have hboundary := budget_ite hsize (budget_ite hb₀ henter hskip) hstop
  have hr₁ := fst' (fst encWalk encRead)
  have ht := snd' (fst encWalk encRead)
  have hb₁ := snd' (snd encWalk encRead)
  have hhalt := budget_comp_linear hh ht
  have hnext := budget_comp_linear hn (budget_prod ht (snd encWalk encRead))
  have hrun := budget_comp_linear running (budget_prod hr₁ hnext)
  let reject : State τ := .inr (.inr none)
  have hreturn := budget_comp_linear
    (optionElimSnd (budget_const (encIn := encRegisters) (encB := encState encT) reject (.refl _))
      (budget_comp_linear select record_inSpace))
    (budget_prod hr₁ (budget_comp_linear hr ht))
  have hpending := budget_ite hhalt
    (budget_ite hb₁ (budget_const reject (.refl _)) hreturn) hrun
  have hdone := budget_comp_linear finished (fst encDone encRead)
  refine (sumElimFst hboundary (sumElimFst hpending hdone)).of_enc_eq ?_
  rintro ⟨r | (⟨r, t⟩ | b), read, choice⟩
  · cases choice <;> simp [machine, Scan.Result.finish, encState, encInner, encWalk, encDone]
  · cases choice <;> cases h : result t <;>
      simp [machine, h, reject, encState, encInner, encWalk, encDone]
  · rfl

private theorem replay_pending {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (r : Registers) (bits : List Bool) (t : τ)
    (h : walk.FirstHalting input bits t) :
    (machine ctx walk enter result).replay input bits (.inr (.inl (r, t))) =
      .inr (.inl (r, walk.replay input bits t)) := by
  induction bits generalizing t with
  | nil => rfl
  | cons choice bits ih =>
    obtain ⟨hlive, htail⟩ := (walk.firstHalting_cons_iff input choice bits t).mp h
    have hstep : (machine ctx walk enter result).step input (.inr (.inl (r, t))) choice =
        .inr (.inl (r, walk.step input t choice)) := by
      simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hlive]
    rw [NondeterministicQueryMachine.replay_cons, hstep, ih _ htail, walk.replay_cons]

/-- A selected walk runs on the same input and records its returned remaining fuel. The
select marker and the unique continuing return marker surround the walk's exact choice list. -/
theorem replay_checked_walk {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (r : Registers) (hcursor : r.cursor < r.context.size)
    (bits : List Bool) (remaining : ℕ)
    (h : walk.FirstHalting input bits (enter r))
    (hresult : result (walk.replay input bits (enter r)) = some remaining) :
    (machine ctx walk enter result).replay input (true :: (bits ++ [false])) (.inl r) =
      .inl (r.record remaining) := by
  rw [NondeterministicQueryMachine.replay_cons]
  have hstep : (machine ctx walk enter result).step input (.inl r) true =
      .inr (.inl (r, enter r)) := by
    simp [NondeterministicQueryMachine.step, machine, hcursor]
  rw [hstep, NondeterministicQueryMachine.replay_append, replay_pending _ _ _ _ _ _ _ _ h,
    NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.replay_nil]
  simp [NondeterministicQueryMachine.step, machine, h.1, hresult]

/-- A successful tally trace from a suspended walk contains that walk's first-halting
choices followed by the false return choice and the remaining tally trace. -/
theorem firstHalting_walk_return {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (r : Registers) (choices : List Bool) (t : τ) (hit : Bool)
    (h : (machine ctx walk enter result).FirstHalting input choices (.inr (.inl (r, t))))
    (hend : (machine ctx walk enter result).replay input choices (.inr (.inl (r, t))) =
      .inr (.inr (some hit))) :
    let M := machine ctx walk enter result
    ∃ bits rest remaining, choices = bits ++ false :: rest ∧
      walk.FirstHalting input bits t ∧
      result (walk.replay input bits t) = some remaining ∧
      M.FirstHalting input rest (.inl (r.record remaining)) ∧
      M.replay input rest (.inl (r.record remaining)) = .inr (.inr (some hit)) := by
  let M := machine ctx walk enter result
  induction choices generalizing t with
  | nil => cases hend
  | cons choice choices ih =>
    have htail := ((M.firstHalting_cons_iff input choice choices _).mp h).2
    rw [M.replay_cons] at hend
    by_cases hhalt : walk.halted t = true
    · have reject (hstep : M.step input (.inr (.inl (r, t))) choice = .inr (.inr none)) :
          False := by
        rw [hstep, M.replay_of_halted input (show M.halted (.inr (.inr none)) = true from rfl)]
          at hend
        cases hend
      cases choice
      · cases hresult : result t with
        | none =>
          exact (reject (by simp [M, NondeterministicQueryMachine.step, machine, hhalt,
            hresult])).elim
        | some remaining =>
          have hstep : M.step input (.inr (.inl (r, t))) false =
              .inl (r.record remaining) := by
            simp [M, NondeterministicQueryMachine.step, machine, hhalt, hresult]
          rw [hstep] at htail hend
          exact ⟨[], choices, remaining, rfl, ⟨hhalt, by simp⟩, hresult, htail, hend⟩
      · exact (reject (by simp [M, NondeterministicQueryMachine.step, machine, hhalt])).elim
    · have hlive : walk.halted t = false := Bool.eq_false_iff.mpr hhalt
      have hstep : M.step input (.inr (.inl (r, t))) choice =
          .inr (.inl (r, walk.step input t choice)) := by
        simp [M, NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
          machine, hlive]
      rw [hstep] at htail hend
      obtain ⟨bits, rest, remaining, hbits, hfirst, hresult, hrest, hdone⟩ :=
        ih (walk.step input t choice) htail hend
      refine ⟨choice :: bits, rest, remaining, by simp only [List.cons_append, hbits], ?_,
        ?_, hrest, hdone⟩
      · exact (walk.firstHalting_cons_iff input choice bits t).mpr ⟨hlive, hfirst⟩
      · rwa [walk.replay_cons]

private def renderSelection {N : ℕ} (selectors : List (Fin N) → List Bool) :
    Option (List (Fin N)) → List Bool
  | none => [false]
  | some tail => true :: (selectors tail ++ [false])

private def renderFrom {N : ℕ} (selectors : List (Fin N) → List Bool)
    (branch : Scan.Branch N) (n : ℕ) : ℕ → List Bool
  | 0 => [false]
  | fuel + 1 =>
    if h : n < N then
      renderSelection selectors (branch ⟨n, h⟩) ++ renderFrom selectors branch (n + 1) fuel
    else [false]

private def renderPrefix {N : ℕ} (walkSelectors : List (Fin N) → List Bool)
    (branch : Scan.Branch N) : ℕ → List Bool
  | 0 => []
  | n + 1 => renderPrefix walkSelectors branch n ++
    if h : n < N then renderSelection walkSelectors (branch ⟨n, h⟩) else []

private theorem render_split {N : ℕ} (walkSelectors : List (Fin N) → List Bool)
    (branch : Scan.Branch N) (n : ℕ) (hn : n ≤ N) :
    renderFrom walkSelectors branch 0 N =
      renderPrefix walkSelectors branch n ++ renderFrom walkSelectors branch n (N - n) := by
  induction n with
  | zero => simp [renderPrefix]
  | succ n ih =>
    have hlt : n < N := hn
    have hsub : N - n = (N - (n + 1)) + 1 := by omega
    rw [ih hlt.le, hsub]
    simp only [renderFrom, dite_eq_left hlt, renderPrefix, List.append_assoc]

/-- Serialize the candidate selections, the selected walk traces and the terminal tally check. -/
def selectors {N : ℕ} (walkSelectors : List (Fin N) → List Bool)
    (branch : Scan.Branch N) : List Bool :=
  renderFrom walkSelectors branch 0 N

/-- A walk serialization with no ambiguous prefix yields distinct traces for distinct
candidate selections. -/
theorem selectors_injective {N : ℕ} (walkSelectors : List (Fin N) → List Bool)
    (hwalk : ∀ {a b}, walkSelectors a <+: walkSelectors b → a = b) :
    Function.Injective (selectors walkSelectors) := by
  intro a b heq
  have h {n fuel : ℕ} (hsize : n + fuel = N)
      (hbits : renderFrom walkSelectors a n fuel = renderFrom walkSelectors b n fuel) :
      ∀ v : Fin N, n ≤ v.val → a v = b v := by
    induction fuel generalizing n with
    | zero =>
      intro v hv
      have := v.isLt
      omega
    | succ fuel ih =>
      have hn : n < N := by omega
      let current : Fin N := ⟨n, hn⟩
      simp only [renderFrom, dite_eq_left hn] at hbits
      have hselection : a current = b current := by
        change renderSelection walkSelectors (a current) ++ _ =
          renderSelection walkSelectors (b current) ++ _ at hbits
        cases ha : a current <;> cases hb : b current
        · rfl
        · simp [ha, hb, renderSelection] at hbits
        · simp [ha, hb, renderSelection] at hbits
        · rename_i left right
          have hwalkBits := List.cons.inj (by simpa only [ha, hb, renderSelection,
            List.cons_append, List.append_assoc] using hbits :
              true :: (walkSelectors left ++ [false] ++
                renderFrom walkSelectors a (n + 1) fuel) =
              true :: (walkSelectors right ++ [false] ++
                renderFrom walkSelectors b (n + 1) fuel))
          have hpLeft : walkSelectors left <+:
              walkSelectors left ++ [false] ++ renderFrom walkSelectors a (n + 1) fuel :=
            ⟨[false] ++ renderFrom walkSelectors a (n + 1) fuel, (List.append_assoc _ _ _).symm⟩
          have hpRight : walkSelectors right <+:
              walkSelectors left ++ [false] ++ renderFrom walkSelectors a (n + 1) fuel :=
            ⟨[false] ++ renderFrom walkSelectors b (n + 1) fuel, by
              rw [← List.append_assoc]
              exact hwalkBits.2.symm⟩
          rcases List.prefix_or_prefix_of_prefix hpLeft hpRight with hp | hp
          · exact congrArg some (hwalk hp)
          · exact congrArg some (hwalk hp).symm
      change renderSelection walkSelectors (a current) ++ _ =
        renderSelection walkSelectors (b current) ++ _ at hbits
      rw [hselection] at hbits
      intro v hv
      by_cases he : v.val = n
      · have hh : v = current := Fin.ext he
        subst v
        exact hselection
      · exact ih (by omega) (List.append_cancel_left hbits) v (by omega)
  funext v
  exact h (n := 0) (fuel := N) (by simp) heq v (Nat.zero_le _)

/-- A successful typed scan prefix reaches the corresponding binary selection boundary,
provided the selected walks have exact same-input replays with the returned fuel. -/
private theorem replay_of_tallyPrefix {τ : Type} {N : ℕ}
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (radius : ℕ) (expected : Tally) (branch : Scan.Branch N)
    (walkSelectors : List (Fin N) → List Bool)
    (hwalk : ∀ (v : Fin N) (acc : Scan.Result) (tail : List (Fin N)) (remaining : ℕ),
      (Scan.walkM Scan.readNext (fun u v => pure (edge u v)) v radius source tail).1 =
        some remaining →
      let r : Registers := ⟨⟨N, source.val, target.val, radius, expected⟩, v.val, acc⟩
      walk.FirstHalting input (walkSelectors tail) (enter r) ∧
        result (walk.replay input (walkSelectors tail) (enter r)) = some remaining)
    {n : ℕ} (hn : n ≤ N) (acc : Scan.Result)
    (hacc : Scan.tallyPrefix edge source target radius branch hn = some acc) :
    let ctx : Context := ⟨N, source.val, target.val, radius, expected⟩
    (machine ctx walk enter result).run input (renderPrefix walkSelectors branch n) =
      .inl ⟨ctx, n, acc⟩ := by
  let ctx : Context := ⟨N, source.val, target.val, radius, expected⟩
  let M := machine ctx walk enter result
  change M.run input (renderPrefix walkSelectors branch n) = .inl ⟨ctx, n, acc⟩
  induction n generalizing acc with
  | zero =>
    rw [Scan.tallyPrefix_zero] at hacc
    cases hacc
    rfl
  | succ n ih =>
    have hlt : n < N := hn
    rw [Scan.tallyPrefix_succ edge source target radius branch hlt] at hacc
    obtain ⟨prior, hp, hlast⟩ := Option.bind_eq_some_iff.mp hacc
    have hprefix := ih hlt.le prior hp
    dsimp only [renderPrefix]
    rw [dite_eq_left hlt]
    let v : Fin N := ⟨n, hlt⟩
    let r : Registers := ⟨ctx, n, prior⟩
    change M.run input (renderPrefix walkSelectors branch n) = .inl r at hprefix
    change (match branch v with
      | none => some prior
      | some tail => (Scan.walkM Scan.readNext (fun u v => pure (edge u v))
          v radius source tail).1.map (fun left => prior.recordWalk radius left (v == target))) =
      some acc at hlast
    cases hbranch : branch v with
    | none =>
      rw [hbranch] at hlast
      cases hlast
      rw [renderSelection, M.run_append, hprefix, M.replay_cons, M.replay_nil]
      simp [M, NondeterministicQueryMachine.step, machine, ctx, r, Registers.skip, hlt]
    | some tail =>
      rw [hbranch] at hlast
      obtain ⟨left, hleft, rfl⟩ := Option.map_eq_some_iff.mp hlast
      obtain ⟨hbits, hresult⟩ := hwalk v prior tail left hleft
      rw [renderSelection, M.run_append, hprefix]
      have hstep := replay_checked_walk ctx walk enter result input r
        (show r.cursor < r.context.size from hlt) (walkSelectors tail) left hbits hresult
      rw [hstep]
      rfl

/-- A complete tally with matching totals first halts after the final false choice.
A passing negative tally returns `some false` and is an accepting occurrence. -/
theorem firstHalting_finish {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input bits : List Bool) (observed : Scan.Result) (hit : Bool)
    (hboundary : (machine ctx walk enter result).run input bits =
      .inl ⟨ctx, ctx.size, observed⟩)
    (hfinish : observed.finish ctx.expected = some hit) :
    let M := machine ctx walk enter result
    M.FirstHalting input (bits ++ [false]) M.init ∧
      M.run input (bits ++ [false]) = .inr (.inr (some hit)) := by
  let M := machine ctx walk enter result
  change M.FirstHalting input (bits ++ [false]) M.init ∧
    M.run input (bits ++ [false]) = .inr (.inr (some hit))
  have hlast : M.run input (bits ++ [false]) = .inr (.inr (some hit)) := by
    rw [M.run_append, hboundary, M.replay_cons, M.replay_nil]
    simp [M, NondeterministicQueryMachine.step, machine, hfinish]
  refine ⟨M.firstHalting_append_singleton input bits false (s := M.init) ?_ ?_, hlast⟩
  · change M.halted (M.run input bits) = false
    rw [hboundary]
    rfl
  · change M.halted (M.run input (bits ++ [false])) = true
    rw [hlast]
    rfl

/-- Replay a successful typed scan as a first-halting membership tally, using the supplied
same-input replay of each successful typed walk. -/
theorem firstHalting_of_scan {τ : Type} {N : ℕ}
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (radius : ℕ) (expected : Tally) (branch : Scan.Branch N) (hit : Bool)
    (walkSelectors : List (Fin N) → List Bool)
    (hwalk : ∀ (v : Fin N) (acc : Scan.Result) (tail : List (Fin N)) (remaining : ℕ),
      (Scan.walkM Scan.readNext (fun u v => pure (edge u v)) v radius source tail).1 =
        some remaining →
      let r : Registers := ⟨⟨N, source.val, target.val, radius, expected⟩, v.val, acc⟩
      walk.FirstHalting input (walkSelectors tail) (enter r) ∧
        result (walk.replay input (walkSelectors tail) (enter r)) = some remaining)
    (h : Scan.run edge source target radius expected branch = some hit) :
    let M := machine ⟨N, source.val, target.val, radius, expected⟩ walk enter result
    M.FirstHalting input (selectors walkSelectors branch) M.init ∧
      M.run input (selectors walkSelectors branch) = .inr (.inr (some hit)) := by
  rw [Scan.run_eq_finish] at h
  obtain ⟨acc, hacc, hfinish⟩ := Option.bind_eq_some_iff.mp h
  have hprior := replay_of_tallyPrefix walk enter result input edge
    source target radius expected branch walkSelectors hwalk le_rfl acc hacc
  simpa [selectors, render_split walkSelectors branch N le_rfl, renderFrom] using
    firstHalting_finish _ walk enter result input (renderPrefix walkSelectors branch N)
      acc hit hprior hfinish

/-- Decode the selected candidates of a successful first-halting tally, given a decoder for
each successful first-halting walk. The typed scan performs the same terminal tally check. -/
theorem exists_scan_of_firstHalting {τ : Type} {N : ℕ}
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (radius : ℕ) (expected : Tally) (walkSelectors : List (Fin N) → List Bool)
    (hwalk : ∀ (v : Fin N) (acc : Scan.Result) (bits : List Bool) (remaining : ℕ),
      let r : Registers := ⟨⟨N, source.val, target.val, radius, expected⟩, v.val, acc⟩
      walk.FirstHalting input bits (enter r) →
      result (walk.replay input bits (enter r)) = some remaining →
      ∃ tail, bits = walkSelectors tail ∧
        (Scan.walkM Scan.readNext (fun u v => pure (edge u v)) v radius source tail).1 =
        some remaining)
    (bits : List Bool) (hit : Bool) :
    let M := machine ⟨N, source.val, target.val, radius, expected⟩ walk enter result
    M.FirstHalting input bits M.init →
    M.run input bits = .inr (.inr (some hit)) →
    ∃ branch, bits = selectors walkSelectors branch ∧
      Scan.run edge source target radius expected branch = some hit := by
  classical
  let ctx : Context := ⟨N, source.val, target.val, radius, expected⟩
  let M := machine ctx walk enter result
  have decode (choices : List Bool) (n : ℕ) (hn : n ≤ N) (acc : Scan.Result)
      (branch : Scan.Branch N)
      (htally : Scan.tallyPrefix edge source target radius branch hn = some acc)
      (hfirst : M.FirstHalting input choices (.inl ⟨ctx, n, acc⟩))
      (hend : M.replay input choices (.inl ⟨ctx, n, acc⟩) = .inr (.inr (some hit))) :
      ∃ branch', (∀ v : Fin N, v.val < n → branch' v = branch v) ∧
        choices = renderFrom walkSelectors branch' n (N - n) ∧
        Scan.run edge source target radius expected branch' = some hit := by
    induction hm : N - n using Nat.strongRecOn generalizing choices n acc branch with
    | ind m ih =>
      cases choices with
      | nil => cases hend
      | cons choice choices =>
        let r : Registers := ⟨ctx, n, acc⟩
        change M.replay input (choice :: choices) (.inl r) = _ at hend
        have htail := ((M.firstHalting_cons_iff input choice choices (.inl r)).mp hfirst).2
        rw [M.replay_cons] at hend
        by_cases hlive : n < N
        · let v : Fin N := ⟨n, hlive⟩
          have extend (selection : Option (List (Fin N))) (acc' : Scan.Result)
              (hselection : (match selection with
                | none => some acc
                | some tail => (Scan.walkM Scan.readNext (fun u v => pure (edge u v))
                    v radius source tail).1.map
                      (fun left => acc.recordWalk radius left (v == target))) = some acc') :
              Scan.tallyPrefix edge source target radius (Function.update branch v selection)
                (Nat.succ_le_of_lt hlive) = some acc' := by
            rw [Scan.tallyPrefix_succ edge source target radius _ hlive]
            have hprior : Scan.tallyPrefix edge source target radius
                (Function.update branch v selection) hlive.le = some acc := by
              refine (Scan.tallyPrefix_congr edge source target radius hlive.le
                (b := branch) ?_).trans htally
              intro u hu
              have huv : u ≠ v := fun he => (Nat.ne_of_lt hu) (congrArg Fin.val he)
              rw [Function.update_of_ne huv]
            rw [hprior]
            change (match Function.update branch v selection v with
              | none => some acc
              | some tail => (Scan.walkM Scan.readNext (fun u v => pure (edge u v))
                  v radius source tail).1.map
                    (fun left => acc.recordWalk radius left (v == target))) = some acc'
            rwa [Function.update_self]
          have keep (selection : Option (List (Fin N))) (branch' : Scan.Branch N)
              (h : ∀ u : Fin N, u.val < n + 1 → branch' u = Function.update branch v selection u) :
              (∀ u : Fin N, u.val < n → branch' u = branch u) ∧
                branch' v = selection := by
            refine ⟨?_, (h v (Nat.lt_succ_self n)).trans (Function.update_self v selection branch)⟩
            intro u hu
            rw [h u (by omega), Function.update_of_ne (show u ≠ v from
              fun he => (Nat.ne_of_lt hu) (congrArg Fin.val he))]
          have hsub : m = (N - (n + 1)) + 1 := by omega
          cases choice
          · have hstep : M.step input (.inl r) false = .inl r.skip := by
              simp [M, NondeterministicQueryMachine.step, machine, r, ctx, hlive]
            rw [hstep] at htail hend
            obtain ⟨branch', hp, hbits, hdone⟩ :=
              ih (N - (n + 1)) (by omega) choices (n + 1) (Nat.succ_le_of_lt hlive) acc _
                (extend none acc rfl) htail hend rfl
            obtain ⟨hprior, hselect⟩ := keep none branch' hp
            exact ⟨branch', hprior, by
              simp only [hsub, renderFrom, dite_eq_left hlive,
                show branch' ⟨n, hlive⟩ = none from hselect, renderSelection,
                List.singleton_append, hbits], hdone⟩
          · have hstep : M.step input (.inl r) true = .inr (.inl (r, enter r)) := by
              simp [M, NondeterministicQueryMachine.step, machine, r, ctx, hlive]
            rw [hstep] at htail hend
            obtain ⟨walkBits, rest, left, hsplit, hwalkFirst, hfuel, hrest, hdone⟩ :=
              firstHalting_walk_return ctx walk enter result input r choices (enter r) hit
                htail hend
            obtain ⟨tail, hwalkBits, hcheck⟩ := hwalk v acc walkBits left hwalkFirst hfuel
            have hacc : (r.record left).observed = acc.recordWalk radius left (v == target) := rfl
            obtain ⟨branch', hp, hbits, hdone⟩ :=
              ih (N - (n + 1)) (by omega) rest (n + 1) (Nat.succ_le_of_lt hlive)
                (r.record left).observed _ (extend (some tail) _ (by simp [hacc, hcheck]))
                hrest hdone rfl
            obtain ⟨hprior, hselect⟩ := keep (some tail) branch' hp
            exact ⟨branch', hprior, by
              simp only [hsub, renderFrom, dite_eq_left hlive,
                show branch' ⟨n, hlive⟩ = some tail from hselect, renderSelection,
                List.cons_append, List.append_assoc, List.nil_append, hsplit,
                hwalkBits, hbits], hdone⟩
        · have hN : n = N := by omega
          have hstep : M.step input (.inl r) choice =
              .inr (.inr (if choice then none else acc.finish expected)) := by
            simp [M, NondeterministicQueryMachine.step, machine, r, ctx, hlive]
          rw [hstep] at htail
          have halt : M.halted (.inr (.inr (if choice then none else acc.finish expected))) =
              true := rfl
          have hnil : choices = [] := by
            cases choices with
            | nil => rfl
            | cons head rest =>
              have hlive := ((M.firstHalting_cons_iff input head rest _).mp htail).1
              rw [halt] at hlive
              cases hlive
          rw [hstep, M.replay_of_halted input halt] at hend
          cases choice
          · have hfinish : acc.finish expected = some hit := by simpa using hend
            subst n
            refine ⟨branch, fun _ _ => rfl, ?_, ?_⟩
            · have hm0 : m = 0 := by omega
              simp [hnil, hm0, renderFrom]
            · rw [Scan.run_eq_finish, htally]
              exact hfinish
          · cases hend
  change M.FirstHalting input bits M.init → M.run input bits = .inr (.inr (some hit)) →
    ∃ branch, bits = selectors walkSelectors branch ∧
      Scan.run edge source target radius expected branch = some hit
  intro hfirst hend
  obtain ⟨branch, _, hbits, hscan⟩ := decode bits 0 (Nat.zero_le N) Scan.Result.zero
    (fun _ => none) (Scan.tallyPrefix_zero edge source target radius _) hfirst hend
  exact ⟨branch, by simpa [selectors] using hbits, hscan⟩

/-- If successful walk calls have exact, prefix-free selector encodings, a successful
first-halting tally corresponds to a unique typed scan with the same membership reply. -/
theorem firstHalting_iff_scan {τ : Type} {N : ℕ}
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (radius : ℕ) (expected : Tally) (walkSelectors : List (Fin N) → List Bool)
    (hprefix : ∀ {a b}, walkSelectors a <+: walkSelectors b → a = b)
    (hwalk : ∀ (v : Fin N) (acc : Scan.Result) (bits : List Bool) (remaining : ℕ),
      let r : Registers := ⟨⟨N, source.val, target.val, radius, expected⟩, v.val, acc⟩
      walk.FirstHalting input bits (enter r) ∧
        result (walk.replay input bits (enter r)) = some remaining ↔
      ∃ tail, bits = walkSelectors tail ∧
        (Scan.walkM Scan.readNext (fun u v => pure (edge u v)) v radius source tail).1 =
          some remaining)
    (bits : List Bool) (hit : Bool) :
    let M := machine ⟨N, source.val, target.val, radius, expected⟩ walk enter result
    M.FirstHalting input bits M.init ∧ reply (M.run input bits) = some hit ↔
      ∃! branch, bits = selectors walkSelectors branch ∧
        Scan.run edge source target radius expected branch = some hit := by
  dsimp only
  rw [reply_eq_some_iff]
  constructor
  · rintro ⟨hfirst, hend⟩
    obtain ⟨branch, hbits, hscan⟩ := exists_scan_of_firstHalting walk enter result input edge
      source target radius expected walkSelectors
      (fun v acc ws left hf hr => (hwalk v acc ws left).mp ⟨hf, hr⟩) bits hit hfirst hend
    exact ⟨branch, ⟨hbits, hscan⟩, fun other hother =>
      selectors_injective walkSelectors hprefix (hother.1.symm.trans hbits)⟩
  · rintro ⟨branch, ⟨rfl, hscan⟩, _⟩
    exact firstHalting_of_scan walk enter result input edge source target radius expected branch
      hit walkSelectors
      (fun v acc tail left hw => (hwalk v acc (walkSelectors tail) left).mpr ⟨tail, rfl, hw⟩)
      hscan

private def Invariant {τ : Type} (ctx : Context) (walk : NondeterministicQueryMachine τ)
    (enter : Registers → τ) (input : List Bool) : State τ → Prop
  | .inl r => r.context = ctx ∧ r.Bounded
  | .inr (.inl (r, s)) => r.context = ctx ∧ r.Bounded ∧ r.cursor < ctx.size ∧
      ∃ choices, walk.replay input choices (enter r) = s
  | .inr (.inr _) => True

private theorem invariant_step {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) {s : State τ}
    (hs : Invariant ctx walk enter input s) (choice : Bool) :
    Invariant ctx walk enter input ((machine ctx walk enter result).step input s choice) := by
  rcases s with r | (⟨r, t⟩ | hit)
  · obtain ⟨hr, hb⟩ := hs
    by_cases hlive : r.cursor < r.context.size
    · cases choice
      · simpa [NondeterministicQueryMachine.step, machine, hlive, Invariant]
          using And.intro (show r.skip.context = ctx from hr) (hb.skip hlive)
      · simpa [NondeterministicQueryMachine.step, machine, hlive, Invariant] using
          And.intro hr (And.intro hb (And.intro (hr ▸ hlive)
            (show ∃ choices, walk.replay input choices (enter r) = enter r from ⟨[], rfl⟩)))
    · simp [NondeterministicQueryMachine.step, machine, hlive, Invariant]
  · obtain ⟨hr, hb, hlive, choices, hchoices⟩ := hs
    by_cases hhalt : walk.halted t = true
    · cases choice
      · cases hresult : result t with
        | none => simp [NondeterministicQueryMachine.step, machine, hhalt, hresult, Invariant]
        | some remaining =>
          simpa [NondeterministicQueryMachine.step, machine, hhalt, hresult, Invariant] using
            And.intro (show (r.record remaining).context = ctx from hr)
              (hb.record (hr.symm ▸ hlive) remaining)
      · simp [NondeterministicQueryMachine.step, machine, hhalt, Invariant]
    · simp only [NondeterministicQueryMachine.step, machine, Bool.false_eq_true, ite_false,
        hhalt, Invariant]
      refine ⟨hr, hb, hlive, choices ++ [choice], ?_⟩
      rw [walk.replay_append, hchoices, walk.replay_cons, walk.replay_nil,
        NondeterministicQueryMachine.step, ite_eq_right hhalt]
      rfl
  · exact True.intro

private theorem invariant_replay {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input choices : List Bool) {s : State τ} (hs : Invariant ctx walk enter input s) :
    Invariant ctx walk enter input ((machine ctx walk enter result).replay input choices s) := by
  induction choices generalizing s with
  | nil => exact hs
  | cons choice choices ih =>
    rw [NondeterministicQueryMachine.replay_cons]
    exact ih (invariant_step ctx walk enter result input hs choice)

private theorem length_registers_le (r : Registers) (h : r.Bounded) :
    (encRegisters r).length ≤
      2 * (encContext r.context).length + 6 * (Nat.log2 r.context.size + 1) +
        2 * (Nat.log2 (r.context.size * r.context.radius) + 1) + 6 := by
  obtain ⟨hi, hc, hs⟩ := h
  have hcursor := length_encNat_le_log2 hi
  have hcount := length_encNat_le_log2 (hc.trans hi)
  have hsum := length_encNat_le_log2 (hs.trans (Nat.mul_le_mul_right _ hi))
  simp only [encRegisters_apply, encRegistersFields, encResult_apply, encResultFields,
    encTally_apply, encTallyFields, encBool_apply, List.length_singleton, length_encPair]
  omega

/-- Bound the phase, retained tally registers, and a suspended walk of at most `walkBound` bits. -/
@[expose] def stateBound (ctx : Context) (walkBound : ℕ) : ℕ :=
  4 * (encContext ctx).length + 12 * (Nat.log2 ctx.size + 1) +
    4 * (Nat.log2 (ctx.size * ctx.radius) + 1) + walkBound + 15

/-- Charge the complete suspended tally and the walk state on every finite branch prefix. -/
theorem length_replay_le {τ : Type} (encT : τ ↪ List Bool) (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (budget : ℕ)
    (hwalk : ∀ r : Registers, r.context = ctx → r.Bounded → r.cursor < ctx.size →
      ∀ choices, (encT (walk.replay input choices (enter r))).length ≤ budget)
    (choices : List Bool) :
    (encState encT ((machine ctx walk enter result).run input choices)).length ≤
      stateBound ctx budget := by
  unfold stateBound
  have hi : Invariant ctx walk enter input (initial ctx) := ⟨rfl, initial_bounded ctx⟩
  have hb := invariant_replay ctx walk enter result input choices hi
  change Invariant ctx walk enter input ((machine ctx walk enter result).run input choices) at hb
  generalize (machine ctx walk enter result).run input choices = s at hb ⊢
  rcases s with r | (⟨r, t⟩ | b)
  · obtain ⟨hr, h⟩ := hb
    have hreg := length_registers_le r h
    rw [hr] at hreg
    simp only [encState, encSum_inl, List.length_cons]
    omega
  · obtain ⟨hr, h, hlive, bits, rfl⟩ := hb
    have hreg := length_registers_le r h
    rw [hr] at hreg
    have ht := hwalk r hr h hlive bits
    simp only [encState, encSum_inr, encSum_inl, List.length_cons, length_encPair]
    omega
  · cases b <;>
      simp [encState, encSum_inr, encOption, encBool_apply]

private def ClockBound {τ : Type} (walk : NondeterministicQueryMachine τ)
    (enter : Registers → τ) (input : List Bool) (walkClock elapsed : ℕ) : State τ → Prop
  | .inl r => elapsed ≤ r.cursor * (walkClock + 2)
  | .inr (.inl (r, s)) => ∃ bits, walk.replay input bits (enter r) = s ∧
      bits.length ≤ walkClock ∧ elapsed ≤ r.cursor * (walkClock + 2) + 1 + bits.length
  | .inr (.inr _) => True

private theorem clock_step {τ : Type} (ctx : Context)
    (walk : NondeterministicQueryMachine τ) (enter : Registers → τ) (result : τ → Option ℕ)
    (input : List Bool) (walkClock elapsed : ℕ)
    (hwalk : ∀ r : Registers, r.context = ctx → r.Bounded → r.cursor < ctx.size →
      (walk.withInit (enter r)).HaltsWithin input walkClock)
    {s : State τ} (hs : Invariant ctx walk enter input s)
    (hb : ClockBound walk enter input walkClock elapsed s) (choice : Bool) :
    ClockBound walk enter input walkClock (elapsed + 1)
      ((machine ctx walk enter result).step input s choice) := by
  rcases s with r | (⟨r, t⟩ | hit)
  · change elapsed ≤ r.cursor * (walkClock + 2) at hb
    by_cases hlive : r.cursor < r.context.size
    · cases choice
      · simp only [NondeterministicQueryMachine.step, machine, Bool.false_eq_true, ite_false,
          hlive, ite_true, ClockBound, Registers.skip, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [NondeterministicQueryMachine.step, machine, Bool.false_eq_true, ite_false,
          hlive, ite_true, ClockBound]
        exact ⟨[], rfl, Nat.zero_le _, by simpa using Nat.succ_le_succ hb⟩
    · simp [NondeterministicQueryMachine.step, machine, hlive, ClockBound]
  · obtain ⟨hr, hbounded, hlive, _⟩ := hs
    obtain ⟨bits, heq, hle, htotal⟩ := hb
    by_cases hhalt : walk.halted t = true
    · cases choice
      · cases hresult : result t with
        | none => simp [NondeterministicQueryMachine.step, machine, hhalt, hresult, ClockBound]
        | some remaining =>
          simp only [NondeterministicQueryMachine.step, machine, Bool.false_eq_true, ite_false,
            hhalt, ite_true, hresult, ClockBound, Registers.record, Registers.skip, Nat.add_mul,
            Nat.one_mul]
          omega
      · simp [NondeterministicQueryMachine.step, machine, hhalt, ClockBound]
    · have hlt : bits.length < walkClock := by
        refine lt_of_le_of_ne hle ?_
        intro he
        apply hhalt
        have hh := hwalk r hr hbounded hlive bits he
        rwa [NondeterministicQueryMachine.run_withInit, heq] at hh
      simp only [NondeterministicQueryMachine.step, machine, Bool.false_eq_true, ite_false,
        hhalt, ClockBound]
      refine ⟨bits ++ [choice], ?_, ?_, ?_⟩
      · rw [walk.replay_append, heq, walk.replay_cons, walk.replay_nil,
          NondeterministicQueryMachine.step, ite_eq_right hhalt]
        rfl
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.length_append, List.length_singleton]
        omega
  · exact True.intro

/-- A common walk clock gives a stopping clock for every branch of the tally, including
branches with rejected walks and incorrect final tallies. -/
theorem haltsWithin {τ : Type} (ctx : Context) (walk : NondeterministicQueryMachine τ)
    (enter : Registers → τ) (result : τ → Option ℕ) (input : List Bool) (walkClock : ℕ)
    (hwalk : ∀ r : Registers, r.context = ctx → r.Bounded → r.cursor < ctx.size →
      (walk.withInit (enter r)).HaltsWithin input walkClock) :
    (machine ctx walk enter result).HaltsWithin input (ctx.size * (walkClock + 2) + 1) := by
  let M := machine ctx walk enter result
  have hr (bits : List Bool) : ClockBound walk enter input walkClock bits.length
      (M.run input bits) := by
    induction bits using List.reverseRecOn with
    | nil => simp [M, machine, initial, ClockBound]
    | append_singleton bits choice ih =>
      have hi : Invariant ctx walk enter input (initial ctx) := ⟨rfl, initial_bounded ctx⟩
      have hs : Invariant ctx walk enter input (M.run input bits) :=
        invariant_replay ctx walk enter result input bits hi
      rw [M.run_append, M.replay_cons, M.replay_nil, List.length_append, List.length_singleton]
      exact clock_step ctx walk enter result input walkClock bits.length hwalk hs ih choice
  intro bits hlen
  have hi : Invariant ctx walk enter input (initial ctx) := ⟨rfl, initial_bounded ctx⟩
  have hs : Invariant ctx walk enter input (M.run input bits) :=
    invariant_replay ctx walk enter result input bits hi
  have hb := hr bits
  change M.halted (M.run input bits) = true
  generalize M.run input bits = s at hs hb ⊢
  rcases s with r | (⟨r, t⟩ | hit)
  · obtain ⟨hr, hcursor, _⟩ := hs
    change bits.length ≤ r.cursor * (walkClock + 2) at hb
    rw [hr] at hcursor
    have hle := Nat.mul_le_mul_right (walkClock + 2) hcursor
    omega
  · obtain ⟨_, _, hcursor, _⟩ := hs
    obtain ⟨ws, _, hws, hclock⟩ := hb
    have hle := Nat.mul_le_mul_right (walkClock + 2) (Nat.succ_le_of_lt hcursor)
    rw [Nat.succ_mul] at hle
    omega
  · rfl

section BoundedWalk

variable {N : ℕ} {τ : Type}

private def rankOr (fallback : Fin N) (rank : ℕ) : Fin N :=
  if h : rank < N then ⟨rank, h⟩ else fallback

private def walkRegisters (fallback : Fin N) (r : Registers) : BoundedWalk.Registers N :=
  ⟨rankOr fallback r.context.source, rankOr fallback r.cursor, r.context.radius⟩

private theorem walkRegisters_mk (fallback source target v : Fin N)
    (radius : ℕ) (expected : Tally) (acc : Scan.Result) :
    walkRegisters fallback ⟨⟨N, source.val, target.val, radius, expected⟩, v.val, acc⟩ =
      ⟨source, v, radius⟩ := by
  simp [walkRegisters, rankOr, source.isLt, v.isLt]

variable (edge : QueryMachine τ) (start : Fin N → Fin N → τ) (verdict : τ → Bool)
  (clock : ℕ) (fallback : Fin N)

private def fixedWalk := BoundedWalk.machine edge start verdict clock ⟨fallback, fallback, 0⟩

private def enterBoundedWalk (r : Registers) : BoundedWalk.State N τ :=
  (BoundedWalk.machine edge start verdict clock (walkRegisters fallback r)).init

local notation "W" => fixedWalk edge start verdict clock fallback
local notation "enterWalk" => enterBoundedWalk edge start verdict clock fallback

/-- The tally using the canonical bounded walk and a fixed same-input adjacency callback. -/
def withBoundedWalk (ctx : Context) :
    NondeterministicQueryMachine (State (BoundedWalk.State N τ)) :=
  machine ctx W enterWalk BoundedWalk.remainingFuel

/-- Changing the query parameters at entry leaves all tally transitions unchanged. -/
theorem withBoundedWalk_withInit (ctx newContext : Context) :
    (withBoundedWalk edge start verdict clock fallback ctx).withInit (initial newContext) =
      withBoundedWalk edge start verdict clock fallback newContext := by
  unfold withBoundedWalk NondeterministicQueryMachine.withInit
  rfl

private theorem boundedWalk_replay (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target v : Fin N)
    (radius : ℕ) (expected : Tally) (acc : Scan.Result) (bits : List Bool) (left : ℕ)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v) :
    let r : Registers := ⟨⟨N, source.val, target.val, radius, expected⟩, v.val, acc⟩
    (W).FirstHalting input bits (enterWalk r) ∧
        BoundedWalk.remainingFuel ((W).replay input bits (enterWalk r)) = some left ↔
      ∃ tail, bits = BoundedWalk.selectors clock tail ∧
        (Scan.walkM Scan.readNext (fun u v => pure (adjacent u v)) v radius source tail).1 =
          some left := by
  let regs : BoundedWalk.Registers N := ⟨source, v, radius⟩
  dsimp only [enterBoundedWalk]
  rw [walkRegisters_mk]
  have hreentry := BoundedWalk.machine_withInit edge start verdict clock
    ⟨fallback, fallback, 0⟩ regs
  have h := BoundedWalk.firstHalting_remainingFuel_iff edge start verdict clock regs
    input adjacent hclock hedge bits left
  rw [← hreentry, NondeterministicQueryMachine.run_withInit] at h
  simpa only [fixedWalk, NondeterministicQueryMachine.firstHalting_withInit,
    NondeterministicQueryMachine.init_withInit, regs] using h

/-- A successful first-halting tally uses exactly the selectors of a successful typed scan.
The returned membership bit distinguishes successful negative replies from rejected traces. -/
theorem withBoundedWalk_firstHalting_iff (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (expected : Tally) (bits : List Bool) (hit : Bool)
    (hclock : ∀ u v, edge.halted (edge.runFrom input (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom input (start u v) clock) = adjacent u v) :
    let M := withBoundedWalk edge start verdict clock fallback
      ⟨N, source.val, target.val, radius, expected⟩
    M.FirstHalting input bits M.init ∧ M.run input bits = .inr (.inr (some hit)) ↔
      ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
        Scan.run adjacent source target radius expected branch = some hit := by
  simpa only [reply_eq_some_iff, withBoundedWalk] using
    firstHalting_iff_scan W enterWalk BoundedWalk.remainingFuel input adjacent source target
      radius expected (BoundedWalk.selectors clock) (BoundedWalk.eq_of_selectors_prefix clock)
      (fun v acc ws left => boundedWalk_replay edge start verdict clock fallback input adjacent
        source target v radius expected acc ws left hclock hedge) bits hit

/-- Charge the full candidate scan clock, including all rejecting walk and tally choices. -/
theorem withBoundedWalk_haltsWithin (ctx : Context) (input : List Bool) :
    (withBoundedWalk edge start verdict clock fallback ctx).HaltsWithin input
      (ctx.size * (ctx.radius * (N.size + clock + 3) + (N.size + 2) + 2) + 1) := by
  apply haltsWithin
  intro r hr _ _
  unfold fixedWalk enterBoundedWalk
  rw [BoundedWalk.machine_withInit]
  simpa only [walkRegisters, hr] using
    BoundedWalk.haltsWithin edge start verdict clock (walkRegisters fallback r) input

/-- Encoded tally and walk registers plus one adjacency callback state. -/
def boundedWalkStateBound (N clock : ℕ) (ctx : Context) (calleeBound : ℕ) : ℕ :=
  stateBound ctx (12 * (encNat N).length + 4 * (Nat.log2 N.size + 1) +
    4 * (encNat ctx.radius).length + 2 * (encNat clock).length + calleeBound + 21)

/-- Charge both the suspended tally and the entire bounded walk on all branch prefixes. -/
theorem withBoundedWalk_length_run_le (encCallee : τ ↪ List Bool)
    (ctx : Context) (input : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ (u v : Fin N) t, t ≤ clock →
      (encCallee (edge.runFrom input (start u v) t)).length ≤ calleeBound)
    (bits : List Bool) :
    (encState (BoundedWalk.encState encCallee)
      ((withBoundedWalk edge start verdict clock fallback ctx).run input bits)).length ≤
      boundedWalkStateBound N clock ctx calleeBound := by
  unfold boundedWalkStateBound
  apply length_replay_le
  intro r hr _ _ choices
  rw [← NondeterministicQueryMachine.run_withInit, fixedWalk, enterBoundedWalk,
    BoundedWalk.machine_withInit]
  simpa only [walkRegisters, hr] using
    BoundedWalk.length_run_le edge start verdict clock (walkRegisters fallback r)
      input encCallee calleeBound hcallee choices

private theorem rankOr_budget {α : Type} {enc : α ↪ List Bool} {budget : α → ℕ}
    (fallback : Fin N) {rank : α → ℕ} (hr : ComputableInSpace rank enc encNat budget) :
    ComputableInSpace (fun a => rankOr fallback (rank a)) enc
      (Fin.valEmbedding.trans encNat) budget := by
  have hN : ComputableInSpace (fun _ => N) enc encNat budget :=
    (ComputableInSpace.constZero N).mono_le fun _ => Nat.zero_le _
  have hfallback : ComputableInSpace (fun _ => fallback.val) enc encNat budget :=
    (ComputableInSpace.constZero fallback.val).mono_le fun _ => Nat.zero_le _
  refine (budget_ite (budget_natLt hr hN) hr hfallback).of_enc_eq ?_
  intro a
  by_cases h : rank a < N <;> simp [rankOr, h]

private theorem enterWalk_inSpace (encCallee : τ ↪ List Bool) :
    ComputableInSpace enterWalk encRegisters (BoundedWalk.encState encCallee)
      (fun r => (encRegisters r).length) := by
  have hr := budget_id (enc := encRegisters) (.refl _)
  have hc := encRegisters_context_budget hr
  have hregisters := BoundedWalk.encRegisters_mk_budget N
    (rankOr_budget fallback (encContext_source_budget hc))
    (rankOr_budget fallback (encRegisters_cursor_budget hr))
    (encContext_radius_budget hc)
  exact BoundedWalk.init_budget edge start verdict clock hregisters

/-- Query the original input at the active bounded-walk position. -/
theorem withBoundedWalk_query_inSpace (ctx : Context) (encCallee : τ ↪ List Bool)
    (hq : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length)) :
    ComputableInSpace (withBoundedWalk edge start verdict clock fallback ctx).query
      (encState (BoundedWalk.encState encCallee)) encNat
      (fun s => (encState (BoundedWalk.encState encCallee) s).length) :=
  query_inSpace _ ctx W enterWalk _ (BoundedWalk.query_inSpace edge start verdict clock
    ⟨fallback, fallback, 0⟩ encCallee hq)

/-- Detect a terminal tally, including a rejected one, in linear workspace. -/
theorem withBoundedWalk_halted_inSpace (ctx : Context) (encCallee : τ ↪ List Bool) :
    ComputableInSpace (withBoundedWalk edge start verdict clock fallback ctx).halted
      (encState (BoundedWalk.encState encCallee)) encBool
      (fun s => (encState (BoundedWalk.encState encCallee) s).length) :=
  halted_inSpace _ ctx W enterWalk _

/-- Step the composed tally in linear workspace, using the supplied adjacency certificates. -/
theorem withBoundedWalk_next_inSpace (ctx : Context) (encCallee : τ ↪ List Bool)
    (hstart : ComputableInSpace (fun p : Fin N × Fin N => start p.1 p.2)
      (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat)) encCallee
      (fun p => (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat) p).length))
    (hn : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hh : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hv : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length)) :
    let E := encState (BoundedWalk.encState (N := N) encCallee)
    let encStep := encPair E (encPair (encOption encBool) encBool)
    ComputableInSpace (withBoundedWalk edge start verdict clock fallback ctx).next encStep E
      (fun p => (encStep p).length) :=
  next_inSpace _ ctx W enterWalk _
    (enterWalk_inSpace edge start verdict clock fallback encCallee)
    (BoundedWalk.next_inSpace edge start verdict clock ⟨fallback, fallback, 0⟩ encCallee
      hstart hn hh hv)
    (BoundedWalk.halted_inSpace edge start verdict clock ⟨fallback, fallback, 0⟩ encCallee)
    (BoundedWalk.remainingFuel_inSpace encCallee)

open NondeterministicQueryMachine in
/-- Compile a tally for fixed graph dimension and adjacency clock. The query parameters come
from the original input. The space budget covers all tally, walk and adjacency branches. -/
theorem withBoundedWalk_exists_routines {α : Type} (enc : α ↪ List Bool) (S : α → ℕ)
    (ctx : Context) (context : α → Context) (encCallee : τ ↪ List Bool)
    (hcontext : ComputableInSpace context enc encContext S)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hstart : ComputableInSpace (fun p : Fin N × Fin N => start p.1 p.2)
      (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat)) encCallee
      (fun p => (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat) p).length))
    (hq : ComputableInSpace edge.query encCallee encNat (fun s => (encCallee s).length))
    (hn : ComputableInSpace edge.next (QueryMachine.encStateRead encCallee) encCallee
      (fun p => (QueryMachine.encStateRead encCallee p).length))
    (hh : ComputableInSpace edge.halted encCallee encBool (fun s => (encCallee s).length))
    (hv : ComputableInSpace verdict encCallee encBool (fun s => (encCallee s).length))
    (calleeBound : α → ℕ)
    (hcallee : ∀ a (u v : Fin N) t, t ≤ clock →
      (encCallee (edge.runFrom (enc a) (start u v) t)).length ≤ calleeBound a)
    (hstate : ∀ a, boundedWalkStateBound N clock (context a) (calleeBound a) ≤ S a) :
    Nonempty (Routines (withBoundedWalk edge start verdict clock fallback ctx)
      (fun a => initial (context a)) enc S) := by
  let E := BoundedWalk.encState (N := N) encCallee
  have hinit := budget_comp_linear (initial_inSpace E) hcontext
  refine (withBoundedWalk edge start verdict clock fallback ctx).exists_routines
    (withBoundedWalk_query_inSpace edge start verdict clock fallback ctx encCallee hq)
    (withBoundedWalk_next_inSpace edge start verdict clock fallback ctx encCallee hstart hn hh hv)
    (withBoundedWalk_halted_inSpace edge start verdict clock fallback ctx encCallee)
    (accept_inSpace E ctx W enterWalk _) _ S hlog hinit ⟨1, ?_⟩
  intro a bits
  rw [withBoundedWalk_withInit, Nat.one_mul]
  exact (withBoundedWalk_length_run_le edge start verdict clock fallback encCallee
    (context a) (enc a) (calleeBound a) (hcallee a) bits).trans (hstate a)

open NondeterministicQueryMachine in
/-- Native accepting occurrence lists exist exactly for the canonical selectors of
passing typed scans, with one occurrence list per selector list. -/
theorem withBoundedWalk_native_firstHalting_iff {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (ctx : Context) (context : α → Context)
    (R : Routines (withBoundedWalk edge start verdict clock fallback ctx)
      (fun a => initial (context a)) enc S)
    (a : α) (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (expected : Tally) (bits : List Bool)
    (hcontext : context a = ⟨N, source.val, target.val, radius, expected⟩)
    (hclock : ∀ u v, edge.halted (edge.runFrom (enc a) (start u v) clock) = true)
    (hedge : ∀ u v, verdict (edge.runFrom (enc a) (start u v) clock) = adjacent u v) :
    (∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
        some (bits, final) ∧ final.Halted ∧ final.output = [true]) ↔
      ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
        ∃ hit, Scan.run adjacent source target radius expected branch = some hit := by
  let M := withBoundedWalk edge start verdict clock fallback ctx
  let startState : State (BoundedWalk.State N τ) := initial (context a)
  have hM : M.withInit startState = withBoundedWalk edge start verdict clock fallback
      ⟨N, source.val, target.val, radius, expected⟩ := by
    dsimp only [M, startState]
    rw [withBoundedWalk_withInit, hcontext]
  have hspec (hit : Bool) :=
    withBoundedWalk_firstHalting_iff edge start verdict clock fallback (enc a) adjacent
      source target radius expected bits hit hclock hedge
  have hiff (hit : Bool) :
      M.FirstHalting (enc a) bits startState ∧
          M.replay (enc a) bits startState = .inr (.inr (some hit)) ↔
        ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
          Scan.run adjacent source target radius expected branch = some hit := by
    simpa only [← hM, init_withInit, firstHalting_withInit, run_withInit] using hspec hit
  have accept_iff (s : State (BoundedWalk.State N τ)) :
      M.accept s = true ↔ ∃ hit, s = .inr (.inr (some hit)) := by
    change (reply s).isSome = true ↔ _
    simp only [Option.isSome_iff_exists, reply_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨final, hreplay, hhalt, hout⟩, _⟩
    obtain ⟨hfirst, houtput⟩ := R.replay_correct a hreplay hhalt
    have haccept := List.cons.inj (houtput.symm.trans hout) |>.1
    obtain ⟨hit, hresult⟩ := (accept_iff _).mp haccept
    obtain ⟨branch, ⟨hbits, hscan⟩, _⟩ := (hiff hit).mp ⟨hfirst, hresult⟩
    refine ⟨branch, ⟨hbits, hit, hscan⟩, fun other hother => ?_⟩
    exact selectors_injective _ (BoundedWalk.eq_of_selectors_prefix clock)
      (hother.1.symm.trans hbits)
  · rintro ⟨branch, ⟨hbits, hit, hscan⟩, _⟩
    have hbranch : ∃! b, bits = selectors (BoundedWalk.selectors clock) b ∧
        Scan.run adjacent source target radius expected b = some hit :=
      ⟨branch, ⟨hbits, hscan⟩, fun _ hother =>
        selectors_injective _ (BoundedWalk.eq_of_selectors_prefix clock)
          (hother.1.symm.trans hbits)⟩
    obtain ⟨hfirst, hresult⟩ := (hiff hit).mpr hbranch
    obtain ⟨indices, ⟨final, hreplay, hhalt⟩, hunique⟩ :=
      (R.existsUnique_replay_iff a bits).mpr hfirst
    have hout := (R.replay_correct a hreplay hhalt).2
    have haccept := (accept_iff _).mpr ⟨hit, hresult⟩
    exact ⟨indices, ⟨final, hreplay, hhalt, by rwa [haccept] at hout⟩,
      fun other ⟨finish, hr, hh, _⟩ => hunique other ⟨finish, hr, hh⟩⟩

end BoundedWalk

end Turing.DoubleCounting.MembershipTally
