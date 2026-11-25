/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.QueryLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.HaltsAt

/-!
# Loops whose body is any function of stored registers and the input

`Turing.MultiTapeTM.ComputableInSpace` charges the value of a function but not its read-only
input. A function of stored *registers* `r` and a read-only *context* `a` is therefore a function
on pairs, with the registers first, within a budget that charges only the registers:

`ComputableInSpace f (encPair encR encA) encB fun p => (encR p.1).length + S p.2`.

This module calls that the *context form*. The registers come first because `encPair` frames its
first component: the encoded pair is the framed registers followed by the context verbatim.

The main result runs such a function with the context on the input tape and the registers in the
state of a query machine, repeatedly: `Turing.MultiTapeTM.ComputableInSpace.loopWith` is a loop
whose body `step : ρ × α → Option ρ` is any certified function of the pair, in context form or
within any other budget, with no restriction on how it reads the input. The loop machine
simulates the machine of the body, in the
representation of `Turing.VirtualWord.Native.machine`, on a virtual input: a read inside the
framed registers is served from the state, and a read past them is a read of the real input,
shifted. The output of the body is collected in the state and becomes the registers of the next
round. So the space is that of the body, of the registers and of a position counter, whatever the
number of rounds; the constant does not depend on it either. Composition by recomputation
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space`), by contrast, multiplies the bound by
a constant for every nested stage.

The trajectory of the registers is a hypothesis: the caller names the registers `r a j` of every
round, shows that the body maps each to the next and stops at the last, and bounds the budget of
the body on them. Nothing is inferred about the loop, and the budget of the body is not used on
registers that the loop does not hold.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.loopWith`: a loop whose body is any function of stored
  registers and the input, within the space of the body and of the registers.
* `Turing.MultiTapeTM.ComputableInSpace.loopWith_of_invariant`: the same from an invariant with a
  decreasing variant, which gives termination, the bound on the body and the result.
* `Turing.MultiTapeTM.ComputableInSpace.comp_logSpace_context`: a budgeted function after a
  logspace rearrangement of registers and context, in context form.
* `Turing.MultiTapeTM.ComputableInLogSpace.inSpace_context`: a logspace function of registers and
  the input with a short value, in context form.

## Implementation notes

The loop machine, its state and its invariant are private to this module.
-/

namespace Turing.MultiTapeTM.StoredLoop

open Universal ComputableInSpace

/-- The state of the loop. -/
structure State where
  /-- The encoded registers. -/
  reg : List Bool
  /-- The framed registers, the stored prefix of the virtual input of the body. -/
  pre : List Bool
  /-- The output of the body collected in the current round. -/
  acc : List Bool
  /-- The configuration of the simulated body. -/
  cfg : SCfg
  /-- Whether the loop has stopped. -/
  stop : Bool

/-- States of the loop, as their fields: the three words framed, then the framed configuration
and the stopping bit. -/
private enc_structure encState : State where
  reg : encBits, pre : encBits, acc : encBits, cfg : eCfg, stop : encBool

/-- The position of the simulated input head in the virtual input. -/
def vpos (s : State) : ℕ := s.cfg.inputPos - 1

/-- The position read in the input: the virtual position past the stored prefix. -/
def query (s : State) : ℕ := vpos s - s.pre.length

/-- The bit of the virtual input under the simulated head: a bit of the stored prefix, or the bit
read in the input. -/
def symbol (s : State) (b : Option Bool) : Option Bool :=
  if vpos s < s.pre.length then some (s.pre.getD (vpos s) false) else b

/-- The virtual input of the body: the framed registers followed by the input. On encoded
registers and an encoded input it is the encoded pair. -/
abbrev vinput (reg w : List Bool) : List Bool := frame reg ++ w

/-- A round: a step of the simulated body, collecting its output; once the body has halted, stop
if its output is empty, and otherwise start the body again on the registers it returned. -/
def next (d : Desc) (p : State × Option Bool) : State :=
  if p.1.cfg.state.isNone then
    if p.1.acc.isEmpty then ⟨p.1.reg, p.1.pre, p.1.acc, p.1.cfg, true⟩
    else ⟨p.1.acc.tail, frame p.1.acc.tail, [], init d, false⟩
  else ⟨p.1.reg, p.1.pre,
    p.1.acc ++ (VirtualWord.Native.machine d).emit (p.1.cfg, symbol p.1 p.2),
    (VirtualWord.Native.machine d).next (p.1.cfg, symbol p.1 p.2), false⟩

/-- The length of a bit word, in binary, within linear space. -/
private theorem bitsLength_inSpace : ComputableInSpace (fun l : List Bool => l.length) encBits
    encNat fun l => (encBits l).length :=
  of_inO ComputableInO.lengthNat

/-- The position read in the input, within space linear in the state. -/
theorem query_inSpace :
    ComputableInSpace query encState encNat fun s => (encState s).length := by
  have hid := budget_id (enc := encState) (.refl _)
  exact budget_natSub (budget_natPred (eCfg_inputPos_budget (encState_cfg_budget hid)))
    (budget_comp_linear bitsLength_inSpace (encState_pre_budget hid))

/-- The stopping test, within space linear in the state. -/
theorem stop_inSpace :
    ComputableInSpace State.stop encState encBool fun s => (encState s).length :=
  encState_stop_budget (budget_id (.refl _))

/-- A round, within space linear in the state and the bit read: the step of the simulated body is
that of `Turing.VirtualWord.Native.components_inSpace`, on the bit selected by `symbol`. -/
theorem next_inSpace (d : Desc) :
    ComputableInSpace (next d) (QueryMachine.encStateRead encState) encState
      fun p => (QueryMachine.encStateRead encState p).length := by
  obtain ⟨-, hn, he, hh, -⟩ := VirtualWord.Native.components_inSpace d
  have hp := fst encState (encOption encBool)
  have hb := snd encState (encOption encBool)
  have hreg := encState_reg_budget hp
  have hpre := encState_pre_budget hp
  have hacc := encState_acc_budget hp
  have hcfg := encState_cfg_budget hp
  have hvpos := budget_natPred (eCfg_inputPos_budget hcfg)
  have hlt := budget_natLt hvpos (budget_comp_linear bitsLength_inSpace hpre)
  have hsym : ComputableInSpace (fun p : State × Option Bool => symbol p.1 p.2)
      (QueryMachine.encStateRead encState) (encOption encBool)
      fun p => (QueryMachine.encStateRead encState p).length :=
    (budget_ite hlt (budget_optionSome (budget_comp_linear (bitsGetD false)
      (budget_prod hpre hvpos))) hb).of_enc_eq fun p => by
        unfold symbol vpos
        by_cases h : p.1.cfg.inputPos - 1 < p.1.pre.length <;> simp [h]
  have hin := budget_prod hcfg hsym
  have happ : ComputableInSpace (fun p : State × Option Bool =>
      p.1.acc ++ (VirtualWord.Native.machine d).emit (p.1.cfg, symbol p.1 p.2))
      (QueryMachine.encStateRead encState) encBits
      fun p => (QueryMachine.encStateRead encState p).length :=
    (hacc.append (budget_comp_linear he hin) fun _ => rfl).weaken (.add (.refl _) (.refl _))
  have hrun := encState_mk_budget hreg hpre happ (budget_comp_linear hn hin)
    (budget_const false)
  have hstop := encState_mk_budget hreg hpre hacc hcfg (budget_const true)
  have htail := budget_comp_linear
    (of_inO (.of_linear (ListEncoding.tail encBool)) :
      ComputableInSpace List.tail encBits encBits fun w => (encBits w).length) hacc
  have hrestart := encState_mk_budget htail
    (budget_comp_linear (ComputableInSpace.frame encBits) htail) (budget_const [])
    (budget_const (init d)) (budget_const false)
  have hempty := budget_comp_linear
    (of_inO (ComputableInDegree.isEmpty (enc₁ := encBool) (enc := encBits)).inO_one) hacc
  exact (budget_ite (budget_comp_linear hh hcfg) (budget_ite hempty hstop hrestart) hrun).of_enc_eq
    fun _ => rfl

/-! ### The rounds of the loop -/

section Rounds

variable (d : Desc) (w : List Bool)

/-- The bit under the simulated head is the bit of the virtual input, the stored prefix followed
by the input. -/
theorem symbol_read (s : State) : symbol s (w[query s]?) = (s.pre ++ w)[vpos s]? := by
  unfold symbol query
  split_ifs with h
  · rw [List.getElem?_append_left h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_append_right (Nat.le_of_not_gt h)]

/-- The output of the simulated body grows by the emission of a step. -/
theorem output_succ (x : List Bool) (t : ℕ) :
    (VirtualWord.Native.machine d).output x (t + 1) =
      (VirtualWord.Native.machine d).output x t ++
        if (VirtualWord.Native.machine d).halted ((VirtualWord.Native.machine d).run x t) then []
        else (VirtualWord.Native.machine d).emit ((VirtualWord.Native.machine d).run x t,
          (VirtualWord.Native.machine d).read x ((VirtualWord.Native.machine d).run x t)) := by
  simp only [QueryMachine.output, show (VirtualWord.Native.machine d).finish = fun _ => [] from rfl,
    List.append_nil, List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
    List.flatten_singleton]

/-- The output of the simulated body does not shrink. -/
theorem length_output_mono (x : List Bool) {t u : ℕ} (h : t ≤ u) :
    ((VirtualWord.Native.machine d).output x t).length ≤
      ((VirtualWord.Native.machine d).output x u).length := by
  induction u, h using Nat.le_induction with
  | base => rfl
  | succ u _ ih =>
    rw [output_succ, List.length_append]
    omega

/-- While the body runs, a round of the loop is a step of the body on the virtual input. -/
theorem round_run (reg pre : List Bool) (t : ℕ)
    (h : ((VirtualWord.Native.machine d).run (pre ++ w) t).state.isNone = false) :
    queryRound query (next d) w ⟨reg, pre, (VirtualWord.Native.machine d).output (pre ++ w) t,
        (VirtualWord.Native.machine d).run (pre ++ w) t, false⟩ =
      ⟨reg, pre, (VirtualWord.Native.machine d).output (pre ++ w) (t + 1),
        (VirtualWord.Native.machine d).run (pre ++ w) (t + 1), false⟩ := by
  have hh : (VirtualWord.Native.machine d).halted
      ((VirtualWord.Native.machine d).run (pre ++ w) t) = false := h
  rw [queryRound, next, symbol_read, output_succ, QueryMachine.run_succ, QueryMachine.step, hh]
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Once the body has halted, a round stops the loop if the body returned nothing, and otherwise
starts the body on the registers it returned. -/
theorem round_halted (s : State) (h : s.cfg.state.isNone = true) (b : Option Bool) :
    next d (s, b) = if s.acc.isEmpty then ⟨s.reg, s.pre, s.acc, s.cfg, true⟩
      else ⟨s.acc.tail, frame s.acc.tail, [], init d, false⟩ := by
  simp only [next, h, ↓reduceIte]

/-! ### The invariant -/

variable (N : ℕ) (regs : ℕ → List Bool) (T : ℕ → ℕ)

/-- The state of the loop in round `j`, after `t` steps of the body on the registers `regs j`. -/
def running (j t : ℕ) : State :=
  ⟨regs j, frame (regs j), (VirtualWord.Native.machine d).output (vinput (regs j) w) t,
    (VirtualWord.Native.machine d).run (vinput (regs j) w) t, false⟩

/-- The state in which the loop stops, after round `N`. -/
def stopped : State :=
  ⟨regs N, frame (regs N), [],
    (VirtualWord.Native.machine d).run (vinput (regs N) w) (T N), true⟩

/-- The invariant of the loop whose body halts after `T j` steps in round `j` and which stops
after round `N`: the state is that of round `j ≤ N` after `t ≤ T j` steps of the body, or the
stopped state. The variant `m` bounds the rounds of the query loop that are left. -/
def Inv (m : ℕ) (s : State) : Prop :=
  (∃ j ≤ N, ∃ t ≤ T j, s = running d w regs j t ∧
    m = (N - j) * ((Finset.range (N + 1)).sup T + 2) + (T j - t) + 1) ∨
  (s = stopped d w N regs T ∧ m = 0)

/-- The invariant holds at the start of the first round. -/
theorem inv_start :
    ∃ m, Inv d w N regs T m ⟨regs 0, frame (regs 0), [], init d, false⟩ :=
  ⟨_, .inl ⟨0, Nat.zero_le _, 0, Nat.zero_le _, rfl, rfl⟩⟩

variable {d w N regs T}

/-- A round keeps the invariant and decreases the variant, when the body does not halt before
`T j` steps in round `j`, returns the registers of the next round in rounds before `N`, and returns
nothing in round `N`. -/
theorem inv_round
    (hrun : ∀ j ≤ N, ∀ t < T j,
      ((VirtualWord.Native.machine d).run (vinput (regs j) w) t).state.isNone = false)
    (hhalt : ∀ j ≤ N,
      ((VirtualWord.Native.machine d).run (vinput (regs j) w) (T j)).state.isNone = true)
    (hnext : ∀ j < N, (VirtualWord.Native.machine d).output (vinput (regs j) w) (T j) =
      true :: regs (j + 1))
    (hlast : (VirtualWord.Native.machine d).output (vinput (regs N) w) (T N) = [])
    {m : ℕ} {s : State} (h : Inv d w N regs T m s) (hs : s.stop = false) :
    ∃ m' < m, Inv d w N regs T m' (queryRound query (next d) w s) := by
  rcases h with ⟨j, hj, t, ht, rfl, rfl⟩ | ⟨rfl, -⟩
  · rcases Nat.lt_or_ge t (T j) with hlt | hge
    · exact ⟨_, by omega, .inl ⟨j, hj, t + 1, hlt, round_run d w _ _ t (hrun j hj t hlt), rfl⟩⟩
    · obtain rfl : t = T j := Nat.le_antisymm ht hge
      rw [queryRound, round_halted d _ (hhalt j hj)]
      rcases Nat.lt_or_ge j N with hjN | hjN
      · have hT : T (j + 1) ≤ (Finset.range (N + 1)).sup T :=
          Finset.le_sup (f := T) (Finset.mem_range.mpr (by omega))
        refine ⟨(N - (j + 1)) * ((Finset.range (N + 1)).sup T + 2) + (T (j + 1) - 0) + 1, ?_,
          .inl ⟨j + 1, hjN, 0, Nat.zero_le _, ?_, rfl⟩⟩
        · obtain ⟨e, he⟩ : ∃ e, N - j = e + 1 := ⟨N - j - 1, by omega⟩
          rw [he, show N - (j + 1) = e by omega, Nat.succ_mul]
          omega
        · simp only [running, hnext j hjN, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.tail_cons]
          rfl
      · obtain rfl : j = N := Nat.le_antisymm hj hjN
        refine ⟨0, by omega, .inr ⟨?_, rfl⟩⟩
        simp only [running, hlast, List.isEmpty_nil, ↓reduceIte, stopped]
  · cases hs

/-- Where the loop has stopped, the invariant determines the state. -/
theorem eq_stopped_of_inv {m : ℕ} {s : State} (h : Inv d w N regs T m s)
    (hs : s.stop = true) :
    s = stopped d w N regs T := by
  rcases h with ⟨j, -, t, -, rfl, -⟩ | ⟨rfl, -⟩
  · cases hs
  · rfl

/-- Under the invariant, the state holds the registers of a round `j ≤ N`, their frame, a prefix
of the output of the body, and a configuration of the body on the virtual input. -/
theorem exists_of_inv {m : ℕ} {s : State} (h : Inv d w N regs T m s) :
    ∃ j ≤ N, ∃ t, s.reg = regs j ∧ s.pre = frame (regs j) ∧
      s.acc.length ≤ ((VirtualWord.Native.machine d).output (vinput (regs j) w) (T j)).length ∧
      s.cfg = (VirtualWord.Native.machine d).run (vinput (regs j) w) t := by
  rcases h with ⟨j, hj, t, ht, rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨j, hj, t, rfl, rfl, length_output_mono d _ ht, rfl⟩
  · exact ⟨N, le_rfl, T N, rfl, rfl, Nat.zero_le _, rfl⟩

end Rounds

end Turing.MultiTapeTM.StoredLoop

public section

namespace Turing.MultiTapeTM.StoredLoop

open Universal ComputableInSpace


/-- The logarithm of a sum is at most one summand plus the logarithm of the other. -/
private theorem log2_add_le (u v : ℕ) : Nat.log2 (u + v) ≤ u + Nat.log2 v + 1 := by
  rcases Nat.eq_zero_or_pos (u + v) with h | h
  · simp [h]
  · refine Nat.le_of_lt_succ ((Nat.log2_lt h.ne').mpr ?_)
    calc u + v < 2 ^ u + 2 ^ (Nat.log2 v + 1) := Nat.add_lt_add Nat.lt_two_pow_self Nat.lt_log2_self
      _ ≤ 2 ^ (u + Nat.log2 v + 1) + 2 ^ (u + Nat.log2 v + 1) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 2 ^ (u + Nat.log2 v + 1 + 1) := by rw [pow_succ]; ring

/-- The logarithm of the length of an encoded pair is within the length of its first component
plus the logarithm of the length of the second. -/
theorem _root_.Turing.MultiTapeTM.log2_length_encPair_le {α ρ : Type} (encR : ρ ↪ List Bool)
    (encA : α ↪ List Bool) (p : ρ × α) : Nat.log2 (encPair encR encA p).length ≤
      2 * (encR p.1).length + Nat.log2 (encA p.2).length + 2 := by
  rw [length_encPair]
  exact (log2_add_le _ _).trans (by omega)

/-- **A budgeted function after a logspace rearrangement of registers and context.** If `g` is
computable within the budget `Sg`, `f` is a logspace function of stored registers and a context,
and the budget of `g` at `f p` is within the registers plus a budget `S` of the context that is at
least the logarithm of its length, then `g ∘ f` is in context form with the budget `S`: the
logarithm of the length of the encoded pair, which composition by recomputation
(`Turing.MultiTapeTM.ComputableInSpace.comp_logSpace`) adds, is within the registers plus the
logarithm of the length of the context. This substitutes the registers or the context of a
function in context form. -/
theorem _root_.Turing.MultiTapeTM.ComputableInSpace.comp_logSpace_context
    {α ρ β γ : Type} {encA : α ↪ List Bool} {encR : ρ ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {g : β → γ} {f : ρ × α → β} {Sg : β → ℕ}
    {S : α → ℕ} (hg : ComputableInSpace g encB encC Sg)
    (hf : ComputableInLogSpace f (encPair encR encA) encB)
    (hS : (fun p => Sg (f p)) ≼ fun p => (encR p.1).length + S p.2)
    (hlog : ∀ a, Nat.log2 (encA a).length ≤ S a) :
    ComputableInSpace (fun p => g (f p)) (encPair encR encA) encC
      fun p => (encR p.1).length + S p.2 :=
  (hg.comp_logSpace hf).weaken (.add hS ⟨3, fun p => by
    have h := log2_length_encPair_le encR encA p
    have := hlog p.2
    dsimp only
    omega⟩)

/-- **A logspace function of stored registers and the input, with a short value, in context
form.** Logarithmic space in the length of the encoded pair is within the registers plus the
logarithm of the length of the input, so the function is computable within that budget once its
value fits it. This turns the rules of `Turing.MultiTapeTM.ComputableInLogSpace`, such as
projections and composition with a function of the input alone, into bodies of
`Turing.MultiTapeTM.ComputableInSpace.loopWith`. -/
theorem _root_.Turing.MultiTapeTM.ComputableInLogSpace.inSpace_context {α ρ β : Type}
    {encA : α ↪ List Bool} {encR : ρ ↪ List Bool} {encB : β ↪ List Bool} {f : ρ × α → β}
    (h : ComputableInLogSpace f (encPair encR encA) encB)
    (hlen : (fun p => (encB (f p)).length) ≼
      fun p => (encR p.1).length + Nat.log2 (encA p.2).length) :
    ComputableInSpace f (encPair encR encA) encB
      fun p => (encR p.1).length + Nat.log2 (encA p.2).length :=
  (ComputableInSpace.budget_id (.refl _)).comp_logSpace_context h hlen fun _ => le_rfl

/-- **A loop whose body is any function of stored registers and the input.** The body
`step : ρ × α → Option ρ` takes the registers and the input, and returns the next registers or
`none` to stop. Let it be computable within any budget `T` of the registers and the input, where
the registers are charged and the input is not, and let the registers of the loop from `init a` be
`r a 0, …, r a (n a)`, the body stopping at the last, with `T (r a j, a) ≤ B a` in every round.
Then the final registers are computable within space `O(S + B + log n)` on inputs of length `n`:
the body is simulated on the virtual input `encPair encR encA (r, a)`, whose framed first
component is stored and whose second component is the input itself. The budget of the body is
only used on the registers of the run, so it may grow with registers that the loop never holds;
the registers themselves are short because the value of the body is charged to its budget. -/
theorem _root_.Turing.MultiTapeTM.ComputableInSpace.loopWith {α ρ : Type} {encA : α ↪ List Bool}
    {encR : ρ ↪ List Bool} {step : ρ × α → Option ρ} {init : α → ρ} {S B : α → ℕ}
    {T : ρ × α → ℕ} (r : α → ℕ → ρ) (n : α → ℕ)
    (hinit : ComputableInSpace init encA encR S)
    (hstep : ComputableInSpace step (encPair encR encA) (encOption encR) T)
    (h0 : ∀ a, r a 0 = init a)
    (hsucc : ∀ a, ∀ j < n a, step (r a j, a) = some (r a (j + 1)))
    (hstop : ∀ a, step (r a (n a), a) = none)
    (hT : ∀ a, ∀ j ≤ n a, T (r a j, a) ≤ B a) :
    ComputableInSpace (fun a => r a (n a)) encA encR
      fun a => S a + B a + Nat.log2 (encA a).length := by
  classical
  obtain ⟨c₀, hc₀⟩ := hinit.length_le
  obtain ⟨time, c, ⟨k, Q, _, tm, htm⟩, hout⟩ := hstep
  let : Fintype Q := Fintype.ofFinite Q
  let eS : Q ↪ ℕ := (Fintype.equivFin Q).toEmbedding.trans Fin.valEmbedding
  -- the registers of a round are the start value or a value of the body, which is charged
  have hsize (a : α) (j : ℕ) (hj : j ≤ n a) :
      (encR (r a j)).length ≤ c₀ * (S a + 1) + c * (B a + 1) := by
    rcases j with _ | j
    · rw [h0]
      exact (hc₀ a).trans (Nat.le_add_right _ _)
    · have h := hout (r a j, a)
      rw [hsucc a j (by omega), encOption_some, List.length_cons] at h
      have : c * (T (r a j, a) + 1) ≤ c * (B a + 1) :=
        Nat.mul_le_mul_left c (Nat.succ_le_succ (hT a j (by omega)))
      omega
  -- the first halt of the body in each round, on its virtual input
  choose τ _ hτ using fun a j => exists_haltsAt_of_runsInTime (htm (r a j, a)).2.1
  have hrun (a : α) (j t : ℕ) (ht : t < τ a j) :
      ((VirtualWord.Native.machine (desc eS eBit tm)).run (vinput (encR (r a j)) (encA a))
        t).state.isNone = false :=
    (VirtualWord.Native.halted_native eS tm _ t).trans
      (Bool.eq_false_iff.mpr (Option.isNone_iff_eq_none.not.mpr ((hτ a j).not_halted ht)))
  have hhalt (a : α) (j : ℕ) :
      ((VirtualWord.Native.machine (desc eS eBit tm)).run (vinput (encR (r a j)) (encA a))
        (τ a j)).state.isNone = true :=
    (VirtualWord.Native.halted_native eS tm _ (τ a j)).trans
      (Option.isNone_iff_eq_none.mpr (hτ a j).halted)
  have hfinal (a : α) (j : ℕ) :
      (VirtualWord.Native.machine (desc eS eBit tm)).output (vinput (encR (r a j)) (encA a))
        (τ a j) = encOption encR (step (r a j, a)) := by
    rw [VirtualWord.Native.output_native]
    exact output_haltsAt (htm (r a j, a)).1 (hτ a j)
  obtain ⟨C, hC⟩ := VirtualWord.Native.budget_le eS tm
  -- the start state
  have hreg : ComputableInSpace (fun a => encR (init a)) encA encBits fun a => S a + B a :=
    (hinit.of_enc_eq fun _ => rfl).mono_le fun a => Nat.le_add_right _ _
  have hconst {β : Type} (encB : β ↪ List Bool) (b : β) :
      ComputableInSpace (fun _ : α => b) encA encB fun a => S a + B a :=
    ComputableInSpace.budget_const b
  have hstart := encState_mk_budget hreg
    (ComputableInSpace.budget_comp_linear (ComputableInSpace.frame encBits) hreg)
    (hconst encBits [])
    (hconst eCfg (Universal.init (desc eS eBit tm))) (hconst encBool false)
  have hloop := ComputableInSpace.queryLoop_of_invariant
    (f := fun a => stopped (desc eS eBit tm) (encA a) (n a) (fun j => encR (r a j)) (τ a))
    (fun a m s => Inv (desc eS eBit tm) (encA a) (n a) (fun j => encR (r a j)) (τ a) m s)
    hstart query_inSpace (next_inSpace _) stop_inSpace
    (fun a => by
      have h := inv_start (desc eS eBit tm) (encA a) (n a) (fun j => encR (r a j)) (τ a)
      rwa [h0 a] at h)
    (fun a m s h hs => inv_round (fun j _ t ht => hrun a j t ht) (fun j _ => hhalt a j)
      (fun j hj => by rw [hfinal, hsucc a j hj, encOption_some])
      (by rw [hfinal, hstop a, encOption_none]) h hs)
    (fun a m s h hs => eq_stopped_of_inv h hs)
    ⟨7 + 6 * (c₀ + c) + 2 * c + 2 * (C * (c + 2 * (c₀ + c) + 3)), fun a m s h => ?_⟩
  · exact (encState_reg_budget hloop).of_enc_eq fun _ => rfl
  · obtain ⟨j, hj, t, hsreg, hspre, hsacc, hscfg⟩ := exists_of_inv h
    have hR := hsize a j hj
    have hTj : c * (T (r a j, a) + 1) ≤ c * (B a + 1) :=
      Nat.mul_le_mul_left c (Nat.succ_le_succ (hT a j hj))
    have hlenR : s.reg.length = (encR (r a j)).length := by rw [hsreg]
    have hlenP : s.pre.length = 2 * (encR (r a j)).length + 1 := by rw [hspre, length_frame]
    have hlenA : s.acc.length ≤ c * (T (r a j, a) + 1) :=
      hsacc.trans ((congrArg List.length (hfinal a j)).le.trans (hout (r a j, a)))
    have hcfg := VirtualWord.Native.length_native_run_le_of_space eS tm
      (vinput (encR (r a j)) (encA a)) t (c * (T (r a j, a) + 1)) (htm (r a j, a)).2.2
    have hbud := hC (vinput (encR (r a j)) (encA a)).length (c * (T (r a j, a) + 1))
    have hlog := log2_add_le (2 * (encR (r a j)).length + 1) (encA a).length
    rw [List.length_append, length_frame] at hbud hcfg
    rw [← hscfg] at hcfg
    change (encState s).length ≤ (7 + 6 * (c₀ + c) + 2 * c + 2 * (C * (c + 2 * (c₀ + c) + 3))) *
      (S a + B a + Nat.log2 (encA a).length + 1)
    simp only [encState_apply, encStateFields, length_encPair, encBits_apply, encBool_apply,
      List.length_singleton]
    generalize (encR (r a j)).length = R at *
    generalize Nat.log2 (encA a).length = ℓ at *
    generalize Nat.log2 (2 * R + 1 + (encA a).length) = ℓ' at *
    generalize (eCfg s.cfg).length = E at *
    generalize VirtualWord.Native.budget eS tm (2 * R + 1 + (encA a).length)
      (c * (T (r a j, a) + 1)) = G at *
    generalize c * (T (r a j, a) + 1) = A at *
    generalize hL : S a + B a + ℓ + 1 = L
    have h₀ : c₀ * (S a + 1) ≤ c₀ * L := Nat.mul_le_mul_left c₀ (by omega)
    have h₁ : c * (B a + 1) ≤ c * L := Nat.mul_le_mul_left c (by omega)
    have h₂ : E ≤ C * (c * L + 2 * (c₀ * L + c * L) + 3 * L) :=
      (hcfg.trans hbud).trans (Nat.mul_le_mul_left C (by omega))
    have h₃ : (7 + 6 * (c₀ + c) + 2 * c + 2 * (C * (c + 2 * (c₀ + c) + 3))) * L =
        7 * L + 6 * (c₀ * L + c * L) + 2 * (c * L) +
          2 * (C * (c * L + 2 * (c₀ * L + c * L) + 3 * L)) := by ring
    rw [h₃]
    omega

/-- **A loop over stored registers and the input, from an invariant with a variant.** As
`Turing.MultiTapeTM.ComputableInSpace.loopWith`, with the registers of every round replaced by an
invariant `Inv a m r` of the registers `r` on the input `a`, indexed by a variant `m`: it holds
at the start, a round keeps it with a smaller variant, it bounds the budget of the body, and
where the body stops it determines the registers as `f a`. Then `f` is computable within space
`O(S + B + log n)`. -/
theorem _root_.Turing.MultiTapeTM.ComputableInSpace.loopWith_of_invariant {α ρ : Type}
    {encA : α ↪ List Bool} {encR : ρ ↪ List Bool} {step : ρ × α → Option ρ} {init f : α → ρ}
    {S B : α → ℕ} {T : ρ × α → ℕ} (Inv : α → ℕ → ρ → Prop)
    (hinit : ComputableInSpace init encA encR S)
    (hstep : ComputableInSpace step (encPair encR encA) (encOption encR) T)
    (h0 : ∀ a, ∃ m, Inv a m (init a))
    (hround : ∀ a m r r', Inv a m r → step (r, a) = some r' → ∃ m' < m, Inv a m' r')
    (hstop : ∀ a m r, Inv a m r → step (r, a) = none → r = f a)
    (hT : ∀ a m r, Inv a m r → T (r, a) ≤ B a) :
    ComputableInSpace f encA encR fun a => S a + B a + Nat.log2 (encA a).length := by
  classical
  -- a round that stays at the registers where the body stops
  let G (a : α) (r : ρ) : ρ := (step (r, a)).getD r
  have hex (a : α) : ∀ m r, Inv a m r → ∃ N, step ((G a)^[N] r, a) = none ∧
      (∀ j < N, (step ((G a)^[j] r, a)).isSome) ∧ ∀ j ≤ N, ∃ m', Inv a m' ((G a)^[j] r) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r hr
      cases hs : step (r, a) with
      | none =>
        exact ⟨0, hs, fun j hj => absurd hj (Nat.not_lt_zero _),
          fun j hj => ⟨m, (Nat.le_zero.mp hj).symm ▸ hr⟩⟩
      | some r' =>
        obtain ⟨m', hm', hr'⟩ := hround a m r r' hr hs
        obtain ⟨N, hN, hlt, hinv⟩ := ih m' hm' r' hr'
        have hG : G a r = r' := by simp only [G, hs, Option.getD_some]
        refine ⟨N + 1, by rwa [Function.iterate_succ_apply, hG], ?_, ?_⟩
        · rintro (_ | j) hj
          · simp only [Function.iterate_zero, id_eq, hs, Option.isSome_some]
          · rw [Function.iterate_succ_apply, hG]
            exact hlt j (by omega)
        · rintro (_ | j) hj
          · exact ⟨m, hr⟩
          · rw [Function.iterate_succ_apply, hG]
            exact hinv j (by omega)
  choose m₀ hm₀ using h0
  choose N hN hlt hinv using fun a => hex a (m₀ a) (init a) (hm₀ a)
  refine (ComputableInSpace.loopWith (fun a j => (G a)^[j] (init a)) N hinit hstep
    (fun _ => rfl) (fun a j hj => ?_) hN fun a j hj => ?_).of_enc_eq fun a => ?_
  · obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (hlt a j hj)
    rw [Function.iterate_succ_apply', hr']
    simp only [G, hr', Option.getD_some]
  · obtain ⟨m', hm'⟩ := hinv a j hj
    exact hT a m' _ hm'
  · obtain ⟨m', hm'⟩ := hinv a (N a) le_rfl
    rw [hstop a m' _ hm' (hN a)]

end Turing.MultiTapeTM.StoredLoop
