/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Recursion over stored frames and the input, within the space of the deepest chain

A recursive procedure is given by its *body*, a function of a frame, of the value that a call has
just returned to the frame, if any, and of the read-only input. The body answers with a call, the
frame to resume when the call returns together with the frame of the callee, or with the value
that the frame returns:

`body : (φ × Option β) × α → (φ × φ) ⊕ β`.

`Turing.MultiTapeTM.ComputableInSpace.recWith` runs such a body on a stack of frames. The space is
that of the frames saved along one chain of calls, of the body and of a position counter, with a
constant that does not depend on the depth of the recursion: the stack is the registers of one
loop of `Turing.MultiTapeTM.ComputableInSpace.loopWith`, and a round runs the body once on the
frame in control. Composition by recomputation, by contrast, multiplies the bound by a constant
for every level.

Nothing is inferred about the recursion. The caller gives the value `val` that every reachable
frame returns, a rank that decreases from a frame to its callee and to its own resumption, and a
potential `need`: a frame needs at least the budget of the body on it, and a frame that calls
needs its saved frame, one more unit and the need of the callee. With frames of `F` bits and
depth `D` the potential `(depth + 1) * F` gives space `O(D * F)`; a potential that sums frame
sizes decreasing along a chain gives the sum, which may be far smaller.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.recWith`: the value of a recursion whose body is any
  function of a frame, a returned value and the input, within the space of the deepest chain of
  saved frames.
* `Turing.MultiTapeTM.ComputableInSpace.budget_sumInl`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_sumInr`: the two answers of a body, within a
  budget.

## Implementation notes

The stack, the round of the loop and its invariant are private to this module.
-/

namespace Turing.MultiTapeTM.CallStack

open ComputableInSpace

variable {α φ β : Type}

/-- The registers of the loop that runs a recursion. -/
structure Registers (φ β : Type) where
  /-- The frame in control, with the value that a call has just returned to it, if any. -/
  config : φ × Option β
  /-- The frames that wait for a value, the innermost first. -/
  callers : List φ
  /-- Whether the recursion has returned its value. -/
  done : Bool

/-- Registers as their fields: the framed pair of the frame in control and the returned value,
the framed list of waiting frames, and the stopping bit. -/
private enc_structure encRegisters (φ : Type) (β : Type) (encF : φ ↪ List Bool)
    (encB : β ↪ List Bool) : Registers φ β logspace where
  config : (encPair encF (encOption encB)), callers : (encList encF), done : encBool

/-- The registers after the body has answered: a call saves the resumed frame and gives control
to the callee; a returned value goes to the innermost waiting frame, or ends the recursion. The
frame `d` fills the registers once no frame is left. -/
def advance (d : φ) (q : Registers φ β × ((φ × φ) ⊕ β)) : Registers φ β :=
  q.2.elim (fun sc => ⟨(sc.2, none), sc.1 :: q.1.callers, false⟩)
    fun v => if q.1.callers.isEmpty then ⟨(d, some v), [], true⟩
      else ⟨(q.1.callers.headD d, some v), q.1.callers.tail, false⟩

/-- A round of the loop: run the body on the frame in control, or stop. -/
def step (d : φ) (body : (φ × Option β) × α → (φ × φ) ⊕ β) (p : Registers φ β × α) :
    Option (Registers φ β) :=
  if p.1.done then none else some (advance d (p.1, body (p.1.config, p.2)))

variable {encA : α ↪ List Bool} (encF : φ ↪ List Bool) (encB : β ↪ List Bool)

/-- The registers after an answer, within space linear in the registers and the answer. -/
theorem advance_inSpace (d : φ) :
    ComputableInSpace (advance (β := β) d)
      (encPair (encRegisters φ β encF encB) (encSum (encPair encF encF) encB))
      (encRegisters φ β encF encB)
      fun q =>
        (encPair (encRegisters φ β encF encB) (encSum (encPair encF encF) encB) q).length := by
  have hcall : ComputableInSpace
      (fun p : Registers φ β × (φ × φ) => (⟨(p.2.2, none), p.2.1 :: p.1.callers, false⟩ :
        Registers φ β))
      (encPair (encRegisters φ β encF encB) (encPair encF encF)) (encRegisters φ β encF encB)
      fun p => (encPair (encRegisters φ β encF encB) (encPair encF encF) p).length := by
    have hr := fst (encRegisters φ β encF encB) (encPair encF encF)
    have hsc := snd (encRegisters φ β encF encB) (encPair encF encF)
    exact encRegisters_mk_budget φ β encF encB
      (budget_prod hsc.snd' (budget_const none))
      (budget_cons hsc.fst' (encRegisters_callers_budget φ β encF encB hr))
      (budget_const false)
  have hret : ComputableInSpace
      (fun p : Registers φ β × β => if p.1.callers.isEmpty then (⟨(d, some p.2), [], true⟩ :
        Registers φ β) else ⟨(p.1.callers.headD d, some p.2), p.1.callers.tail, false⟩)
      (encPair (encRegisters φ β encF encB) encB) (encRegisters φ β encF encB)
      fun p => (encPair (encRegisters φ β encF encB) encB p).length := by
    have hc := encRegisters_callers_budget φ β encF encB (fst (encRegisters φ β encF encB) encB)
    have hv := budget_optionSome (snd (encRegisters φ β encF encB) encB)
    exact budget_ite (budget_isEmpty hc)
      (encRegisters_mk_budget φ β encF encB (budget_prod (budget_const d) hv)
        (budget_const []) (budget_const true))
      (encRegisters_mk_budget φ β encF encB (budget_prod (budget_headD d hc) hv)
        (budget_tail hc) (budget_const false))
  exact (sumElimSnd hcall hret).of_enc_eq fun _ => rfl

variable {encF encB}

/-- A round, within the registers, the budget of the body on the frame in control and the
logarithm of the length of the input; a round that stops needs no more than the registers. -/
theorem step_inSpace (d : φ) {body : (φ × Option β) × α → (φ × φ) ⊕ β}
    {T : (φ × Option β) × α → ℕ}
    (hbody : ComputableInSpace body (encPair (encPair encF (encOption encB)) encA)
      (encSum (encPair encF encF) encB) T) :
    ComputableInSpace (step d body) (encPair (encRegisters φ β encF encB) encA)
      (encOption (encRegisters φ β encF encB)) fun p =>
        (encRegisters φ β encF encB p.1).length + Nat.log2 (encA p.2).length +
          if p.1.done then 0 else T (p.1.config, p.2) +
            (encRegisters φ β encF encB p.1).length + Nat.log2 (encA p.2).length := by
  have hreg : ComputableInSpace (fun p : Registers φ β × α => p.1)
      (encPair (encRegisters φ β encF encB) encA) (encRegisters φ β encF encB)
      fun p => (encRegisters φ β encF encB p.1).length + Nat.log2 (encA p.2).length :=
    (ComputableInLogSpace.fst _ encA).inSpace_context (.of_le fun _ => Nat.le_add_right _ _)
  -- the frame in control and the input: a logspace rearrangement of the registers and the input
  have hproj : ComputableInLogSpace (fun p : Registers φ β × α => (p.1.config, p.2))
      (encPair (encRegisters φ β encF encB) encA)
      (encPair (encPair encF (encOption encB)) encA) := by fun_prop
  have hbody' : ComputableInSpace (fun p : Registers φ β × α => body (p.1.config, p.2))
      (encPair (encRegisters φ β encF encB) encA) (encSum (encPair encF encF) encB)
      fun p => T (p.1.config, p.2) + (encRegisters φ β encF encB p.1).length +
        Nat.log2 (encA p.2).length :=
    (hbody.comp_logSpace hproj).weaken ⟨3, fun p => by
      have := log2_length_encPair_le (encRegisters φ β encF encB) encA p
      dsimp only
      omega⟩
  have hadv := budget_optionSome (budget_comp_linear (advance_inSpace encF encB d)
    (budget_prod (hreg.mono_le fun p => by omega) hbody'))
  exact ((encRegisters_done_budget φ β encF encB hreg).ite (constZero none) hadv).of_enc_eq
    fun _ => rfl

/-! ### The invariant -/

section Invariant

variable (encF) (val : φ × Option β → β) (rank need : φ × Option β → ℕ)
  (Reach : φ × Option β → Prop) (result : β) (K : ℕ)

/-- The cost of the waiting frames: their encodings, and one unit each. -/
def cost (l : List φ) : ℕ := (l.map fun g => (encF g).length + 1).sum

/-- The encoded list of waiting frames is within twice their cost. -/
theorem length_encList_le (l : List φ) : (encList encF l).length ≤ 2 * cost encF l := by
  rw [length_encList]
  induction l with
  | nil => simp [cost]
  | cons g l ih =>
    simp only [cost, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- A waiting frame is within the cost of the list. -/
theorem length_le_cost_cons (g : φ) (l : List φ) : (encF g).length ≤ cost encF (g :: l) := by
  simp only [cost, List.map_cons, List.sum_cons]
  omega

/-- Returning the value `v` to the waiting frames leads to the value `result`: every waiting
frame is reachable with the value it receives, fits the bound `K` with the frames below it, and
passes on its own value. -/
def Returns : List φ → β → Prop
  | [], v => v = result
  | g :: rest, v => Reach (g, some v) ∧ cost encF rest + need (g, some v) ≤ K ∧
      Returns rest (val (g, some v))

/-- The rounds that the waiting frames still owe, as powers of three of their ranks. -/
def pending : List φ → β → ℕ
  | [], _ => 0
  | g :: rest, v => 3 ^ rank (g, some v) + pending rest (val (g, some v))

variable (encB) in
/-- The invariant of the loop: the stopped registers hold the result; otherwise the frame in
control is reachable, fits the bound `K` with the waiting frames, which lead to the result, and
is encoded within `M`. The variant `m` bounds the rounds that are left. -/
def Inv (d : φ) (M m : ℕ) (s : Registers φ β) : Prop :=
  (s = ⟨(d, some result), [], true⟩ ∧ (encB result).length ≤ M ∧ m = 0) ∨
  (s.done = false ∧ Reach s.config ∧ cost encF s.callers + need s.config ≤ K ∧
    Returns encF val need Reach result K s.callers (val s.config) ∧
    (encF s.config.1).length ≤ M ∧ (encOption encB s.config.2).length ≤ M ∧
    m = 3 ^ rank s.config + pending val rank s.callers (val s.config))

variable {encF val rank need Reach result K}

/-- Two powers of three with exponents below `n` are together below the power with exponent
`n`. -/
theorem three_pow_add_lt {i j n : ℕ} (hi : i < n) (hj : j < n) : 3 ^ i + 3 ^ j < 3 ^ n := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h₁ : 3 ^ i ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₂ : 3 ^ j ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₃ : 0 < 3 ^ n := Nat.pow_pos (by norm_num)
  rw [pow_succ]
  omega

/-- A round keeps the invariant and decreases the variant, when the answers of the body on the
reachable frames agree with `val`, decrease the rank, fit the potential and are encoded within
`M`. -/
theorem inv_round {a : α} {d : φ} {M : ℕ} {body : (φ × Option β) × α → (φ × φ) ⊕ β}
    (hcall : ∀ c saved child, Reach c → body (c, a) = .inl (saved, child) →
      Reach (child, none) ∧ Reach (saved, some (val (child, none))) ∧
      rank (child, none) < rank c ∧ rank (saved, some (val (child, none))) < rank c ∧
      val c = val (saved, some (val (child, none))))
    (hspace : ∀ c saved child, Reach c → body (c, a) = .inl (saved, child) →
      (encF saved).length + 1 + need (child, none) ≤ need c ∧
      need (saved, some (val (child, none))) ≤ need c)
    (hret : ∀ c v, Reach c → body (c, a) = .inr v → val c = v)
    (hout : ∀ c, Reach c → need c ≤ K →
      (encSum (encPair encF encF) encB (body (c, a))).length ≤ M)
    (hKM : K ≤ M) {m : ℕ} {s s' : Registers φ β}
    (h : Inv encF encB val rank need Reach result K d M m s) (hs : step d body (s, a) = some s') :
    ∃ m' < m, Inv encF encB val rank need Reach result K d M m' s' := by
  rcases h with ⟨rfl, -, -⟩ | ⟨hd, hR, hK, hRet, -, -, rfl⟩
  · simp [step] at hs
  obtain ⟨config, callers, done⟩ := s
  obtain rfl : done = false := hd
  dsimp only at hR hK hRet ⊢
  simp only [step, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
  subst hs
  have hlen := hout config hR (by omega)
  cases hb : body (config, a) with
  | inl sc =>
    obtain ⟨saved, child⟩ := sc
    obtain ⟨hRc, hRs, hrc, hrs, hval⟩ := hcall config saved child hR hb
    obtain ⟨hn₁, hn₂⟩ := hspace config saved child hR hb
    rw [hb, encSum_inl, List.length_cons, length_encPair] at hlen
    rw [show advance d (⟨config, callers, false⟩, Sum.inl (saved, child)) =
      ⟨(child, none), saved :: callers, false⟩ from rfl]
    have hpow := three_pow_add_lt hrc hrs
    refine ⟨3 ^ rank (child, none) + (3 ^ rank (saved, some (val (child, none))) +
      pending val rank callers (val config)), by omega,
      .inr ⟨rfl, hRc, ?_, ⟨hRs, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
    · simp only [cost, List.map_cons, List.sum_cons] at hK ⊢
      omega
    · dsimp only
      omega
    · rw [← hval]
      exact hRet
    · dsimp only at hlen ⊢
      omega
    · simp only [encOption_none, List.length_nil]
      omega
    · simp only [pending, hval]
  | inr v =>
    obtain rfl := hret config v hR hb
    rw [hb, encSum_inr, List.length_cons] at hlen
    have hpos : 0 < 3 ^ rank config := Nat.pow_pos (by norm_num)
    rcases callers with _ | ⟨g, rest⟩
    · obtain rfl : val config = result := hRet
      rw [show advance d (⟨config, [], false⟩, Sum.inr (val config)) =
        ⟨(d, some (val config)), [], true⟩ from rfl]
      exact ⟨0, by omega, .inl ⟨rfl, by omega, rfl⟩⟩
    · obtain ⟨hRg, hKg, hRet'⟩ := hRet
      have hg := length_le_cost_cons encF g rest
      rw [show advance d (⟨config, g :: rest, false⟩, Sum.inr (val config)) =
        ⟨(g, some (val config)), rest, false⟩ from rfl]
      refine ⟨3 ^ rank (g, some (val config)) + pending val rank rest (val (g, some (val config))),
        ?_, .inr ⟨rfl, hRg, hKg, hRet', ?_, ?_, rfl⟩⟩
      · simp only [pending]
        omega
      · dsimp only
        omega
      · simp only [encOption_some, List.length_cons]
        omega

/-- Where the loop stops, the invariant determines the registers. -/
theorem eq_of_inv_of_step_eq_none {a : α} {d : φ} {M m : ℕ}
    {body : (φ × Option β) × α → (φ × φ) ⊕ β} {s : Registers φ β}
    (h : Inv encF encB val rank need Reach result K d M m s) (hs : step d body (s, a) = none) :
    s = ⟨(d, some result), [], true⟩ := by
  rcases h with ⟨rfl, -, -⟩ | ⟨hd, -⟩
  · rfl
  · simp [step, hd] at hs

/-- Under the invariant the registers are short. -/
theorem length_encRegisters_le {d : φ} {M m : ℕ} {s : Registers φ β}
    (h : Inv encF encB val rank need Reach result K d M m s) :
    (encRegisters φ β encF encB s).length ≤ 6 * M + 4 * K + 4 * (encF d).length + 10 := by
  rcases h with ⟨rfl, hres, -⟩ | ⟨-, -, hK, -, hf, ho, -⟩
  · simp only [encRegisters_apply, encRegistersFields, length_encPair, encOption_some,
      List.length_cons, length_encList, List.map_nil, List.sum_nil, encBool_apply,
      List.length_nil]
    omega
  · have hl := length_encList_le encF s.callers
    simp only [encRegisters_apply, encRegistersFields, length_encPair, encBool_apply,
      List.length_singleton]
    omega

end Invariant

end Turing.MultiTapeTM.CallStack

public section

namespace Turing.MultiTapeTM.ComputableInSpace

open CallStack

variable {α φ β γ : Type} {encA : α ↪ List Bool} {encF : φ ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool}

/-- The left summand of a value computed within a budget, within the budget. -/
theorem budget_sumInl {S : α → ℕ} {f : α → β} (hf : ComputableInSpace f encA encB S) :
    ComputableInSpace (fun a => (Sum.inl (f a) : β ⊕ γ)) encA (encSum encB encC) S :=
  (((constZero [false]).append hf (encB := encBits) fun _ => rfl).mono_le fun _ =>
    (Nat.zero_add _).le)

/-- The right summand of a value computed within a budget, within the budget. -/
theorem budget_sumInr {S : α → ℕ} {f : α → γ} (hf : ComputableInSpace f encA encC S) :
    ComputableInSpace (fun a => (Sum.inr (f a) : β ⊕ γ)) encA (encSum encB encC) S :=
  (((constZero [true]).append hf (encB := encBits) fun _ => rfl).mono_le fun _ =>
    (Nat.zero_add _).le)

/-- **Recursion over stored frames and the input.** The body takes a frame, the value that a call
has just returned to it, if any, and the input. It answers `.inl (saved, child)` to call the frame
`child` and resume the frame `saved` with the value of the call, or `.inr v` to return `v`. Let
the body be computable within a budget `T`, and on every input let

* `Reach` hold of the frames that occur, starting from `(init a, none)`;
* `val` be the value that a reachable frame returns: the value of its resumption after a call,
  and the value that the body returns;
* `rank` decrease from a calling frame to its callee and to its resumption;
* `need` be at least the budget of the body on a reachable frame, and for a calling frame at
  least its saved frame, one more unit and the need of the callee, and at least the need of its
  resumption.

Then the value of the frame `init a` is computable within space `O(S + B + log n)` on inputs of
length `n`, where `B a` bounds the need of the first frame. The constant does not depend on the
depth of the recursion. -/
theorem recWith {body : (φ × Option β) × α → (φ × φ) ⊕ β} {init : α → φ} {S B : α → ℕ}
    {T : (φ × Option β) × α → ℕ} (val : α → φ × Option β → β)
    (rank need : α → φ × Option β → ℕ) (Reach : α → φ × Option β → Prop)
    (hinit : ComputableInSpace init encA encF S)
    (hbody : ComputableInSpace body (encPair (encPair encF (encOption encB)) encA)
      (encSum (encPair encF encF) encB) T)
    (hstart : ∀ a, Reach a (init a, none))
    (hcall : ∀ a c saved child, Reach a c → body (c, a) = .inl (saved, child) →
      Reach a (child, none) ∧ Reach a (saved, some (val a (child, none))) ∧
      rank a (child, none) < rank a c ∧ rank a (saved, some (val a (child, none))) < rank a c ∧
      val a c = val a (saved, some (val a (child, none))))
    (hspace : ∀ a c saved child, Reach a c → body (c, a) = .inl (saved, child) →
      (encF saved).length + 1 + need a (child, none) ≤ need a c ∧
      need a (saved, some (val a (child, none))) ≤ need a c)
    (hret : ∀ a c v, Reach a c → body (c, a) = .inr v → val a c = v)
    (hneed : ∀ a c, Reach a c → T (c, a) ≤ need a c)
    (hB : ∀ a, need a (init a, none) ≤ B a) :
    ComputableInSpace (fun a => val a (init a, none)) encA encB
      fun a => S a + B a + Nat.log2 (encA a).length := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · exact (hinit.of_enc_eq fun a => isEmptyElim a).mono_le fun a => isEmptyElim a
  obtain ⟨c₀, hc₀⟩ := hinit.length_le
  obtain ⟨k, hk⟩ := hbody.length_le
  -- the frame that fills the stopped registers, and the bound on the frame in control
  let d : φ := init a₀
  let M (a : α) : ℕ := c₀ * (S a + 1) + k * (B a + 1) + B a
  have hstartReg : ComputableInSpace
      (fun a => (⟨(init a, none), [], false⟩ : Registers φ β)) encA
      (encRegisters φ β encF encB) S :=
    encRegisters_mk_budget φ β encF encB
      (budget_prod hinit (budget_const none))
      (budget_const [])
      (budget_const false)
  have hloop := loopWith_of_invariant
    (f := fun a => (⟨(d, some (val a (init a, none))), [], true⟩ : Registers φ β))
    (B := fun a => 2 * (6 * M a + 4 * B a + 4 * (encF d).length + 10) + B a +
      2 * Nat.log2 (encA a).length)
    (fun a m s => Inv encF encB (val a) (rank a) (need a) (Reach a) (val a (init a, none)) (B a)
      d (M a) m s)
    hstartReg (step_inSpace d hbody)
    (fun a => ⟨_, .inr ⟨rfl, hstart a, by simpa [cost] using hB a, rfl,
      (hc₀ a).trans (by dsimp only [M]; omega), by simp, rfl⟩⟩)
    (fun a m s s' h hs => inv_round (hcall a) (hspace a) (hret a)
      (fun c hc hcK => (hk (c, a)).trans (by
        have : k * (T (c, a) + 1) ≤ k * (B a + 1) :=
          Nat.mul_le_mul_left k (Nat.succ_le_succ ((hneed a c hc).trans hcK))
        dsimp only [M]
        omega))
      (by dsimp only [M]; omega) h hs)
    (fun a m s h hs => eq_of_inv_of_step_eq_none h hs)
    (fun a m s h => by
      have hlen := length_encRegisters_le h
      rcases h with ⟨rfl, -, -⟩ | ⟨hd, hR, hK, -⟩
      · simp only [↓reduceIte]
        omega
      · have := hneed a s.config hR
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        omega)
  have hval := budget_optionGetD (val a₀ (init a₀, none))
    (encRegisters_config_budget φ β encF encB hloop).snd'
  refine (hval.of_enc_eq fun _ => rfl).weaken
    ⟨12 * c₀ + 12 * k + 8 * (encF d).length + 44, fun a => ?_⟩
  dsimp only [M]
  generalize hL : S a + B a + Nat.log2 (encA a).length + 1 = L
  have h₀ : c₀ * (S a + 1) ≤ c₀ * L := Nat.mul_le_mul_left c₀ (by omega)
  have h₁ : k * (B a + 1) ≤ k * L := Nat.mul_le_mul_left k (by omega)
  have h₂ : (encF d).length ≤ (encF d).length * L := Nat.le_mul_of_pos_right _ (by omega)
  have h₃ : (12 * c₀ + 12 * k + 8 * (encF d).length + 44) * L =
      12 * (c₀ * L) + 12 * (k * L) + 8 * ((encF d).length * L) + 44 * L := by ring
  rw [h₃]
  omega

end Turing.MultiTapeTM.ComputableInSpace
