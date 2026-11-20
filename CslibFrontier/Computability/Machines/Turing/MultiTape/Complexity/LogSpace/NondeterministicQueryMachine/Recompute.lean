/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.NondeterministicBudget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.List.Countdown

/-!
# Nondeterministic query machines on a recomputed input

A nondeterministic query machine `M` can read the output of a deterministic machine, described by
`d`, instead of its own input, without ever storing that output: whenever `M` queries a position
`j`, the machine `Turing.NondeterministicQueryMachine.recompute M d` simulates `d` from the start
on its real input, reading that input in place, and counts down the symbols `d` emits to the one
at `j`. Only the state of `M`, the configuration of `d` and the countdown are stored. This is the
recomputation of [Sipser, Theorem 8.23][Sipser2013] for a nondeterministic reader: the
nondeterministic choices are used only by the steps of `M`, and the steps of `d` ignore them.

When `d` describes a machine computing `f` in logarithmic space, the configurations of `d` and the
countdown take logarithmic space, so the native compiler of query machines turns `M` on the inputs
`encB (f a)` into a native recognizer on the inputs `enc a`
(`Turing.NondeterministicQueryMachine.exists_recognizesInSpace_recompute`).

## Main definitions

* `Turing.NondeterministicQueryMachine.RecomputeState`: the state of `M`, the configuration of
  `d` and the countdown.
* `Turing.NondeterministicQueryMachine.recompute`: `M` reading the output of `d`.

## Main results

* `Turing.NondeterministicQueryMachine.recompute_accepts_iff`: `M` on the recomputed input accepts
  exactly when `M` accepts the output of `d`.
* `Turing.NondeterministicQueryMachine.exists_recognizesInSpace_recompute`: a nondeterministic
  query machine on the output of a logarithmic-space function is recognized by a native machine
  in the space of its states.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.23][Sipser2013]
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine

open MultiTapeTM MultiTapeTM.Universal ComputableInSpace

/-- The state of a nondeterministic query machine reading the output of a deterministic machine,
recomputed on demand. -/
structure RecomputeState (σ : Type) where
  /-- The state of the reading machine. -/
  inner : σ
  /-- The configuration of the simulated deterministic machine. -/
  cfg : SCfg
  /-- The countdown to the queried output symbol: it reaches `0` at that symbol. -/
  count : ℕ
  /-- The queried output bit, once the countdown has reached it. -/
  found : Bool

/-- States of the recomputation, as their fields: the state of the reading machine, the
configuration, the countdown in binary and the bit found. -/
enc_structure eRecompute (σ : Type) (encS : σ ↪ List Bool) : RecomputeState σ where
  inner : encS, cfg : eCfg, count : encNat, found : encBool

/-! ### The countdown over emitted symbols -/

/-- Count down one emitted symbol: at `1`, the symbol is the queried one, read as a bit. -/
def tick (p : ℕ × Bool) (n : ℕ) : ℕ × Bool := (p.1 - 1, if p.1 = 1 then decide (n ≠ 0) else p.2)

/-- Count down the symbol a step emits, if any. -/
def tickOpt (p : ℕ × Bool) (o : Option ℕ) : ℕ × Bool := o.elim p (tick p)

private theorem foldl_tick_toList (p : ℕ × Bool) (o : Option ℕ) :
    o.toList.foldl tick p = tickOpt p o := by
  cases o <;> rfl

/-! ### The machine -/

variable {σ : Type} (M : NondeterministicQueryMachine σ) (d : Desc)

/-- The state that runs `d` from the start to fetch the bit `M` queries in the state `s`. -/
def recomputeStart (s : σ) : RecomputeState σ := ⟨s, Universal.init d, M.query s + 1, false⟩

/-- The answer of a finished countdown: the bit found, or `none` when the output was too short. -/
def RecomputeState.answer (s : RecomputeState σ) : Option Bool :=
  if s.count = 0 then some s.found else none

/-- A step of the recomputation, on the answer to its query and the choice bit: while
`d` runs, a step of `d` reading the real input, counting down the symbol it emits; once `d` has
halted, a step of `M` on the bit found, with the choice, restarting `d` for the next query. -/
def recomputeNext (p : RecomputeState σ × Option Bool × Bool) : RecomputeState σ :=
  let ⟨s, ⟨read, choice⟩⟩ := p
  if s.cfg.state.isSome then
    ⟨s.inner, (stepWith d s.cfg (nuSym s.cfg.inputPos read)).1,
      (tickOpt (s.count, s.found) (stepWith d s.cfg (nuSym s.cfg.inputPos read)).2).1,
      (tickOpt (s.count, s.found) (stepWith d s.cfg (nuSym s.cfg.inputPos read)).2).2⟩
  else recomputeStart M d (M.next (s.inner, s.answer, choice))

/-- **The machine `M` reading the output of the deterministic machine described by `d`**, which
is recomputed from the real input whenever `M` queries a bit. It halts and accepts with `M`. -/
def recompute : NondeterministicQueryMachine (RecomputeState σ) where
  init := recomputeStart M d M.init
  query s := s.cfg.inputPos - 1
  next := recomputeNext M d
  halted s := M.halted s.inner
  accept s := M.accept s.inner

/-! ### Correctness -/

section Correct

variable {M d} {x y : List Bool} {u : ℕ}

/-- The symbols `d` emits in its first `r` steps on `x`. -/
def emitted (d : Desc) (x : List Bool) (r : ℕ) : List ℕ :=
  ((List.range r).map fun j =>
    (Universal.step d (x.map eBit) (Universal.run d (x.map eBit) j)).2.toList).flatten

/-- The state after `r` steps of `d` while `M` waits in `m`. -/
private def recomputeAt (M : NondeterministicQueryMachine σ) (d : Desc) (x : List Bool) (m : σ)
    (r : ℕ) : RecomputeState σ :=
  ⟨m, Universal.run d (x.map eBit) r, ((emitted d x r).foldl tick (M.query m + 1, false)).1,
    ((emitted d x r).foldl tick (M.query m + 1, false)).2⟩

private theorem recomputeAt_zero (m : σ) : recomputeAt M d x m 0 = recomputeStart M d m := rfl

/-- The symbol the recomputation reads is the symbol under the input head of `d`. -/
private theorem nuSym_read (s : RecomputeState σ) :
    nuSym s.cfg.inputPos ((recompute M d).read x s) = inputSymbol (x.map eBit) s.cfg.inputPos := by
  simp only [nuSym, NondeterministicQueryMachine.read, recompute, inputSymbol]
  split_ifs with h
  · rfl
  · rw [← List.map_drop, List.head?_map, List.head?_drop]

private theorem step_recompute_eq {s : RecomputeState σ} (hs : M.halted s.inner = false)
    (c : Bool) :
    (recompute M d).step x s c = recomputeNext M d (s, (recompute M d).read x s, c) := by
  unfold NondeterministicQueryMachine.step
  simp only [recompute, hs, Bool.false_eq_true, ↓reduceIte]

/-- While `d` runs, a step of the recomputation is a step of `d`. -/
private theorem step_recomputeAt_of_lt
    (hhalt : ∀ r, (Universal.run d (x.map eBit) r).state = none ↔ u ≤ r)
    {m : σ} (hm : M.halted m = false) {r : ℕ} (hr : r < u) (c : Bool) :
    (recompute M d).step x (recomputeAt M d x m r) c = recomputeAt M d x m (r + 1) := by
  have hrun : (recomputeAt M d x m r).cfg.state.isSome = true := by
    change (Universal.run d (x.map eBit) r).state.isSome = true
    rw [Option.isSome_iff_ne_none, ne_eq, hhalt]
    omega
  rw [step_recompute_eq hm, recomputeNext]
  simp only [hrun, ↓reduceIte, nuSym_read, ← step_eq_stepWith]
  simp only [recomputeAt, Universal.run_succ, emitted, List.range_succ, List.map_append,
    List.flatten_append, List.foldl_append, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, foldl_tick_toList]

/-- Once `d` has halted, a step of the recomputation is a step of `M` on the output of `d`. -/
private theorem step_recomputeAt_halt
    (hhalt : ∀ r, (Universal.run d (x.map eBit) r).state = none ↔ u ≤ r)
    (hy : emitted d x u = y.map eBit) {m : σ} (hm : M.halted m = false) (c : Bool) :
    (recompute M d).step x (recomputeAt M d x m u) c = recomputeAt M d x (M.step y m c) 0 := by
  have hrun : (recomputeAt M d x m u).cfg.state.isSome = false := by
    change (Universal.run d (x.map eBit) u).state.isSome = false
    rw [Bool.eq_false_iff, ne_eq, Option.isSome_iff_ne_none, not_not, hhalt]
  have hans : (recomputeAt M d x m u).answer = M.read y m := by
    simp only [RecomputeState.answer, recomputeAt, hy]
    unfold tick
    rw [List.foldl_countdown (fun n => decide (n ≠ 0)) _ _ _ 0]
    simp only [show 0 < M.query m + 1 by omega, true_and,
      List.length_map, NondeterministicQueryMachine.read, Nat.add_sub_cancel]
    by_cases hq : M.query m < y.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq]
      simp only [show M.query m + 1 - y.length = 0 by omega, show M.query m + 1 ≤ y.length by omega,
        ↓reduceIte, Option.map_some, Option.getD_some]
      cases y[M.query m] <;> rfl
    · rw [List.getElem?_eq_none (by omega)]
      simp only [show M.query m + 1 - y.length ≠ 0 by omega, ↓reduceIte]
  rw [step_recompute_eq hm, recomputeNext]
  simp only [hrun, Bool.false_eq_true, ↓reduceIte, hans, recomputeAt_zero]
  unfold NondeterministicQueryMachine.step
  simp only [hm, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Once `M` has halted, the recomputation has halted. -/
private theorem step_recomputeAt_of_halted {m : σ} (hm : M.halted m = true) (r : ℕ) (c : Bool) :
    (recompute M d).step x (recomputeAt M d x m r) c = recomputeAt M d x m r :=
  (recompute M d).step_of_halted x (s := recomputeAt M d x m r) hm c

variable (hhalt : ∀ r, (Universal.run d (x.map eBit) r).state = none ↔ u ≤ r)
  (hy : emitted d x u = y.map eBit)
include hhalt hy

/-- A block of `u` ignored choices and one choice of `M` is a step of `M`. -/
private theorem replay_block (m : σ) (c : Bool) :
    (recompute M d).replay x (List.replicate u false ++ [c]) (recomputeAt M d x m 0) =
      recomputeAt M d x (M.step y m c) 0 := by
  cases hm : M.halted m
  · have hpre (i : ℕ) (hi : i ≤ u) : (recompute M d).replay x (List.replicate i false)
        (recomputeAt M d x m 0) = recomputeAt M d x m i := by
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [List.replicate_succ', replay_append, ih (by omega), replay_cons, replay_nil,
          step_recomputeAt_of_lt hhalt hm (by omega)]
    rw [replay_append, hpre u le_rfl, replay_cons, replay_nil, step_recomputeAt_halt hhalt hy hm]
  · rw [(recompute M d).replay_of_halted x (s := recomputeAt M d x m 0) hm, M.step_of_halted y hm]

/-- Blocks of choices replay `M`. -/
private theorem replay_blocks (cs : List Bool) (m : σ) :
    (recompute M d).replay x (cs.flatMap fun c => List.replicate u false ++ [c])
        (recomputeAt M d x m 0) = recomputeAt M d x (M.replay y cs m) 0 := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => rw [List.flatMap_cons, replay_append, replay_block hhalt hy, ih, replay_cons]

/-- Every state the recomputation reaches waits in a state `M` reaches, with `d` within its
halting time. -/
private theorem exists_replay_eq (cs' : List Bool) (cs : List Bool) {r : ℕ} (hr : r ≤ u) (m : σ) :
    ∃ cs₂ r₂, r₂ ≤ u ∧ (recompute M d).replay x cs' (recomputeAt M d x (M.replay y cs m) r) =
      recomputeAt M d x (M.replay y cs₂ m) r₂ := by
  induction cs' generalizing cs r with
  | nil => exact ⟨cs, r, hr, rfl⟩
  | cons c cs' ih =>
    rw [replay_cons]
    cases hm : M.halted (M.replay y cs m)
    · rcases Nat.lt_or_ge r u with hlt | hge
      · rw [step_recomputeAt_of_lt hhalt hm hlt]
        exact ih cs (by omega)
      · obtain rfl : r = u := by omega
        have hs : M.step y (M.replay y cs m) c = M.replay y (cs ++ [c]) m := by
          rw [replay_append]
          rfl
        rw [step_recomputeAt_halt hhalt hy hm, hs]
        exact ih (cs ++ [c]) (Nat.zero_le _)
    · rw [step_recomputeAt_of_halted hm]
      exact ih cs hr

/-- **The recomputation accepts exactly when `M` accepts the output of `d`.** -/
theorem recompute_accepts_iff (m : σ) :
    ((recompute M d).withInit (recomputeStart M d m)).Accepts x ↔ (M.withInit m).Accepts y := by
  constructor
  · rintro ⟨cs', hh, ha⟩
    rw [run_withInit, ← recomputeAt_zero (x := x)] at hh ha
    obtain ⟨cs, r, -, he⟩ := exists_replay_eq hhalt hy cs' [] (Nat.zero_le u) m
    rw [replay_nil] at he
    rw [he] at hh ha
    exact ⟨cs, hh, ha⟩
  · rintro ⟨cs, hh, ha⟩
    refine ⟨cs.flatMap fun c => List.replicate u false ++ [c], ?_, ?_⟩ <;>
      rwa [run_withInit, ← recomputeAt_zero (x := x), replay_blocks hhalt hy]

end Correct

/-! ### The parts, in linear space -/

section Certificates

variable {M d} {encS : σ ↪ List Bool}

private theorem tickOpt_eq (p : ℕ × Bool) (o : Option ℕ) : tickOpt p o =
    if o.isSome then (p.1 - 1, if decide (p.1 = 1) then decide (o ≠ some 0) else p.2) else p := by
  cases o <;> simp [tickOpt, tick]

private theorem tickOpt_budget {γ : Type} {encIn : γ ↪ List Bool} {Bs : γ → ℕ} {p : γ → ℕ × Bool}
    {o : γ → Option ℕ} (hp : ComputableInSpace p encIn (encPair encNat encBool) Bs)
    (ho : ComputableInSpace o encIn eSym Bs) :
    ComputableInSpace (fun x => tickOpt (p x) (o x)) encIn (encPair encNat encBool) Bs := by
  have heq : ComputableInSpace (fun q : Option ℕ × Option ℕ => decide (q.1 = q.2))
      (encPair eSym eSym) encBool fun q => (encPair eSym eSym q).length :=
    of_inO (ComputableInO.eq eSym)
  have hzero : ComputableInSpace (fun x => decide (o x ≠ some 0)) encIn encBool Bs :=
    (budget_finite (encC := encBool) Bool.not (budget_comp_linear heq
      (budget_prod ho ((constZero (some 0)).mono_le fun _ => Nat.zero_le _)))).of_enc_eq
      fun _ => by simp
  have hone := budget_natEq hp.fst' ((constZero 1).mono_le fun _ => Nat.zero_le _)
  refine (budget_ite (budget_optionIsSome ho)
    (budget_prod (budget_natPred hp.fst') (budget_ite hone hzero hp.snd')) hp).of_enc_eq
    fun x => by rw [tickOpt_eq]

variable (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
  (hnext : ComputableInSpace M.next
    (encPair encS (encPair (encOption encBool) encBool)) encS
    fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
  (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
  (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length)

private theorem recompute_id : ComputableInSpace (fun s : RecomputeState σ => s)
    (eRecompute σ encS) (eRecompute σ encS) fun s => (eRecompute σ encS s).length :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

theorem recompute_query_inSpace : ComputableInSpace (recompute M d).query (eRecompute σ encS)
    encNat fun s => (eRecompute σ encS s).length :=
  budget_natPred (eCfg_inputPos_budget (eRecompute_cfg_budget σ encS recompute_id))

include hhalted in
theorem recompute_halted_inSpace : ComputableInSpace (recompute M d).halted (eRecompute σ encS)
    encBool fun s => (eRecompute σ encS s).length :=
  budget_comp_linear (f := fun s : RecomputeState σ => s.inner) hhalted
    (eRecompute_inner_budget σ encS recompute_id)

include haccept in
theorem recompute_accept_inSpace : ComputableInSpace (recompute M d).accept (eRecompute σ encS)
    encBool fun s => (eRecompute σ encS s).length :=
  budget_comp_linear (f := fun s : RecomputeState σ => s.inner) haccept
    (eRecompute_inner_budget σ encS recompute_id)

include hquery in
private theorem recomputeStart_budget {γ : Type} {encIn : γ ↪ List Bool} {Bs : γ → ℕ} {m : γ → σ}
    (hm : ComputableInSpace m encIn encS Bs) :
    ComputableInSpace (fun x => recomputeStart M d (m x)) encIn (eRecompute σ encS) Bs :=
  eRecompute_mk_budget σ encS hm ((constZero (Universal.init d)).mono_le fun _ => Nat.zero_le _)
    (budget_natSucc (budget_comp_linear hquery hm))
    ((constZero false).mono_le fun _ => Nat.zero_le _)

include hquery hnext in
theorem recompute_next_inSpace : ComputableInSpace (recompute M d).next
    (encPair (eRecompute σ encS) (encPair (encOption encBool) encBool)) (eRecompute σ encS)
    fun p => (encPair (eRecompute σ encS) (encPair (encOption encBool) encBool) p).length := by
  have hp := fst (eRecompute σ encS) (encPair (encOption encBool) encBool)
  have hq := snd (eRecompute σ encS) (encPair (encOption encBool) encBool)
  have hinner := eRecompute_inner_budget σ encS hp
  have hcfg := eRecompute_cfg_budget σ encS hp
  have hcount := eRecompute_count_budget σ encS hp
  have hfound := eRecompute_found_budget σ encS hp
  have hans : ComputableInSpace (fun q : RecomputeState σ × Option Bool × Bool => q.1.answer)
      _ (encOption encBool) _ :=
    (budget_ite (budget_natIsZero hcount) (budget_optionSome hfound)
      ((constZero none).mono_le fun _ => Nat.zero_le _)).of_enc_eq fun _ => by
        simp only [RecomputeState.answer, decide_eq_true_eq]
  have hm := budget_comp_linear hnext (budget_prod hinner (budget_prod hans hq.snd'))
  have hsym := nuSym_budget (eCfg_inputPos_budget hcfg) hq.fst'
  have hstep := budget_comp_linear (of_inO stepWith_inO)
    (budget_prod (budget_prod ((constZero d).mono_le fun _ => Nat.zero_le _) hcfg) hsym)
  have htick := tickOpt_budget (budget_prod hcount hfound) hstep.snd'
  exact (budget_ite (budget_optionIsSome (eCfg_state_budget hcfg))
    (eRecompute_mk_budget σ encS hinner hstep.fst' htick.fst' htick.snd')
    (recomputeStart_budget hquery hm)).of_enc_eq fun _ => rfl

end Certificates

/-! ### Logarithmic space -/

/-- The size of the states of the recomputation, in the reading machine's state, the configuration
of `d` and the queried position. -/
private theorem length_eRecompute_recomputeAt_le {encS : σ ↪ List Bool} (x : List Bool) (m : σ)
    (r : ℕ) :
    (eRecompute σ encS (recomputeAt M d x m r)).length ≤
      2 * (encS m).length + 2 * (eCfg (Universal.run d (x.map eBit) r)).length +
        2 * (encNat (M.query m + 1)).length + 8 := by
  have hc : ((emitted d x r).foldl tick (M.query m + 1, false)).1 ≤ M.query m + 1 := by
    unfold tick
    rw [List.foldl_countdown (fun n => decide (n ≠ 0)) _ _ _ 0]
    omega
  have := length_encNat_mono hc
  simp only [eRecompute_apply, recomputeAt, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- **A nondeterministic query machine on the output of a logarithmic-space function is recognized
in the space of its states.** Let `M` have parts computable in space linear in its encoded
states, start in a state computable in space `O(S)` from `enc a`, and, on the inputs
`encB (f a)`, reach only states of length `O(S a)`, where `S a` is at least logarithmic in the
length of `enc a`. If `f` is computable in logarithmic space, a native nondeterministic machine
recognizes, within space `O(S)` on the inputs `enc a`, the inputs `a` on which `M` accepts
`encB (f a)`: it recomputes each bit of `encB (f a)` that `M` queries. -/
theorem exists_recognizesInSpace_recompute {α β : Type} {enc : α ↪ List Bool}
    {encB : β ↪ List Bool} {encS : σ ↪ List Bool}
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length)
    {f : α → β} (hf : ComputableInLogSpace f enc encB) (start : α → σ)
    (S : α → ℕ) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hstart : ComputableInSpace start enc encS S)
    (hsize : ∃ c, ∀ a choices,
      (encS ((M.withInit (start a)).run (encB (f a)) choices)).length ≤ c * S a) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.RecognizesInSpace enc {a | (M.withInit (start a)).Accepts (encB (f a))}
        (fun a => c * S a) := by
  obtain ⟨t, cf, kf, Sf, _, tm, htm⟩ := hf
  let := Fintype.ofFinite Sf
  obtain ⟨ef, hef⟩ := Countable.exists_injective_nat Sf
  set d := desc ⟨ef, hef⟩ eBit tm
  choose u hu_le hu using fun a => exists_haltsAt_of_runsInTime (htm a).2.1
  have hhalt (a : α) := run_desc_halted ⟨ef, hef⟩ tm (enc a) (hu a)
  have hy (a : α) : emitted d (enc a) (u a) = (encB (f a)).map eBit :=
    (congrArg Prod.fst (simulate_eq d _ (u a))).symm.trans
      (simulate_desc_output ⟨ef, hef⟩ tm (enc a) (htm a).1 (hu a))
  obtain ⟨cS, hS⟩ := hsize
  obtain ⟨cq, hcq⟩ := hquery.length_le
  set K := 12 * descLen d + 40
  refine exists_recognizesInSpace (recompute M d) recompute_query_inSpace
    (recompute_next_inSpace hquery hnext) (recompute_halted_inSpace hhalted)
    (recompute_accept_inSpace haccept) (fun a => recomputeStart M d (start a))
    (fun a => (recompute_accepts_iff (hhalt a) (hy a) (start a)).symm) S hlog
    (recomputeStart_budget hquery hstart)
    ⟨2 * cS + 2 * K * (cf + 3) + 2 * cq * (cS + 1) + 12, fun a choices => ?_⟩
  rw [run_withInit, ← recomputeAt_zero (x := enc a)]
  obtain ⟨cs, r, hr, he⟩ := exists_replay_eq (hhalt a) (hy a) choices [] (Nat.zero_le _) (start a)
  rw [replay_nil] at he
  rw [he]
  refine (length_eRecompute_recomputeAt_le M d (encS := encS) _ _ _).trans ?_
  have hm := hS a cs
  rw [run_withInit] at hm
  set m := M.replay (encB (f a)) cs (start a)
  have hcfg := (length_eCfg_le_cfgSpace d _ hr).trans
    (cfgSpace_desc_le ⟨ef, hef⟩ tm (enc a) (htm a).2.2 (u a))
  have hq := hcq m
  have hq1 : (encNat (M.query m + 1)).length ≤ (encNat (M.query m)).length + 1 :=
    length_encNat_add_le _ 1
  have hn : (encNat ((enc a).length + 1)).length ≤ Nat.log2 (enc a).length + 2 :=
    length_encNat_le_log2_add_two le_rfl
  have hl := hlog a
  simp only at hcfg
  have h1 : cf * (Nat.log2 (enc a).length + 1) + (encNat ((enc a).length + 1)).length + 1 ≤
      (cf + 3) * S a := by nlinarith
  have h2 : (eCfg (Universal.run d ((enc a).map eBit) r)).length ≤ K * ((cf + 3) * S a) :=
    hcfg.trans (Nat.mul_le_mul_left K h1)
  have h3 : cq * ((encS m).length + 1) ≤ cq * (cS * S a + S a) :=
    Nat.mul_le_mul_left cq (by omega)
  nlinarith

end Turing.NondeterministicQueryMachine
