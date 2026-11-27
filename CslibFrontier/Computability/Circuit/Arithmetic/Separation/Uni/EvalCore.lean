/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Det
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Machine
public import Mathlib.Data.Finset.Lattice.Fold
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith

/-!
# The universal machine evaluates formulas: the frame of the proof

The universal machine keeps trees in its heap (`Uni.Represents`). To evaluate the formula coded by
the tree at register `1` at the tree at register `2` (`Uni.EvalReady`), it reads the opcode of the
code, evaluates the subformulas, and returns the value to the frame whose address is in
register `3` (`Uni.Returns`). `Uni.EvalsTo θ supp c x l` says that this is correct for the code `c`
at `x` if `l` is the list of the accepting runs of the formula: the sum of the weights of the runs
of the machine is the sum over the runs `r` in `l` without named constants of the weight of `r`
times the sum after the return of the value of `r` (`Uni.plainValue`), and one step of the
formula costs at most `Uni.codeCost supp` steps of the machine.

All steps but the guesses are forced (`Uni.sumTo_rule`). `Uni.InMode.sumTo_step` is the one form
of a forced step that the proofs use: the rule is found by unification from the mode and the
loaded record, and the state after the step is `Uni.step`, whose mode, registers and heap are
computed by `rfl`.

This file has the constructs whose evaluation uses no subformula (`quote`, `id`, `guess`, `fail`,
and `mul`, at which the machine stops).

## Main definitions

* `Uni.Represents`, `Uni.InMode`, `Uni.Returns`, `Uni.EvalReady`, `Uni.EvalsTo`.
* `Uni.nameLength`, `Uni.codeCost`, `Uni.plainWeight`, `Uni.plainValue`.

## Main results

* `Uni.InMode.sumTo_rule`, `Uni.InMode.sumTo_step`, `Uni.InMode.sumTo_zero`: forced steps.
* `Uni.EvalReady.sumTo_decode`: reading the opcode, and the step after it.
* `Uni.sumTo_readName`: reading the name of a constant.
* `Uni.plainValue_map_tick`, `Uni.plainValue_seq`, `Uni.plainValue_seq₃`: the sums over the runs
  of a formula, from the sums over the runs of its subformulas.
* `Uni.EvalsTo.nil`, `Uni.EvalsTo.quote`, `Uni.EvalsTo.id`, `Uni.EvalsTo.fail`,
  `Uni.EvalsTo.mul`, `Uni.EvalsTo.guess`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix I (the proof of Proposition I.1, "The pointer machine"), modules `Nc.Uni.EvalU` and
  `Nc.Uni.EvThm`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Interpreter (Tree Fm Run)

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The address `a` represents the tree in the heap `H`. -/
@[expose] def Represents (H : List (Rec RecKind)) : ℕ → Tree → Prop
  | a, .nil => a = 0
  | a, .cons t u =>
    ∃ p q s, ((.cons, ![a, p, q, s]) : Rec RecKind) ∈ H ∧ Represents H p t ∧ Represents H q u

theorem Represents.mono {H H' : List (Rec RecKind)} (hH : H ⊆ H') {a : ℕ} {t : Tree}
    (h : Represents H a t) : Represents H' a t := by
  induction t generalizing a with
  | nil => exact h
  | cons t u iht ihu =>
    obtain ⟨p, q, s, h₁, h₂, h₃⟩ := h
    exact ⟨p, q, s, hH h₁, iht h₂, ihu h₃⟩

theorem Represents.step {σ : Config supp} {a : ℕ} {t : Tree} (h : Represents σ.heap a t)
    {r : Rule supp} {p q s : ℕ} : Represents (step θ σ r p q s).heap a t :=
  h.mono (heap_subset_step σ r p q s)

theorem WellFormed.nil_mem {σ : Config supp} (hσ : WellFormed σ) {a : ℕ} (ha : a = 0) :
    ((.nil, ![a, 0, 0, 0]) : Rec RecKind) ∈ σ.heap := ha ▸ hσ.nil

/-- The record at an address that represents a tree. -/
theorem Represents.load {σ : Config supp} (hσ : WellFormed σ) {a : ℕ} {t : Tree}
    (h : Represents σ.heap a t) :
    ∃ p q s, ((consOrNil (decide (t ≠ .nil)), ![a, p, q, s]) : Rec RecKind) ∈ σ.heap ∧
      Represents σ.heap p t.hd ∧ Represents σ.heap q t.tl := by
  cases t with
  | nil => exact ⟨0, 0, 0, hσ.nil_mem h, rfl, rfl⟩
  | cons t u => exact h

/-- The state `σ` is well formed and in the mode `md`, its heap contains `H`, and its input
is `inp`. -/
structure InMode (σ : Config supp) (md : Mode (Name supp)) (H : List (Rec RecKind))
    (inp : List Bool) : Prop where
  wf : WellFormed σ
  mode : σ.mode = md
  heap : H ⊆ σ.heap
  inp : σ.inp = inp

namespace InMode

variable {σ σ' : Config supp} {md md' : Mode (Name supp)} {H H' : List (Rec RecKind)}
  {inp : List Bool} {κ : RecKind} {p q s : ℕ} {r : Rule supp} {S : A} {B : ℤ}

theorem mono (h : InMode σ md H inp) (hH : H' ⊆ H) : InMode σ md H' inp :=
  ⟨h.wf, h.mode, List.Subset.trans hH h.heap, h.inp⟩

theorem self (h : InMode σ md H inp) : InMode σ md σ.heap inp :=
  ⟨h.wf, h.mode, List.Subset.refl _, h.inp⟩

/-- The state after a step that reads no input. -/
private theorem step (h : InMode σ md H inp) (hd : (rule θ supp r).dst = md' := by rfl)
    (hrd : (rule θ supp r).rd = none := by rfl) : InMode (step θ σ r p q s) md' H inp :=
  ⟨h.wf.step r p q s, hd, List.Subset.trans h.heap (heap_subset_step σ r p q s), by
    simpa [inp_step, hrd] using h.inp⟩

/-- A record of `H` is in the heap; its address may be given by an equation. -/
theorem mem_of_eq (h : InMode σ md H inp) {k k' f₀ f₁ f₂ : ℕ}
    (hm : ((κ, ![k', f₀, f₁, f₂]) : Rec RecKind) ∈ H) (hk : k = k') :
    ((κ, ![k, f₀, f₁, f₂]) : Rec RecKind) ∈ σ.heap := hk ▸ h.heap hm

/-- The record that a step allocated, at its address. -/
theorem frame_mem (h : InMode σ' md (Uni.step θ σ r p q s).heap inp) {k : ℕ} (hk : k = σ.n + 1) :
    ((rule θ supp r).ak, ![k, env σ p q s ((rule θ supp r).af 0),
      env σ p q s ((rule θ supp r).af 1), env σ p q s ((rule θ supp r).af 2)]) ∈ σ'.heap :=
  h.mem_of_eq (mem_heap_step σ r p q s) hk

/-- **A forced step**: in the mode `md` with the record of kind `κ` loaded, the run sum is the
weight of the rule `nextRule supp md κ` times the run sum after the step. -/
theorem sumTo_rule (hσ : InMode σ md H inp)
    (hrec : ((κ, ![σ.regs (loadReg md), p, q, s]) : Rec RecKind) ∈ σ.heap)
    (hr : nextRule supp md κ = some r)
    (h : InMode (Uni.step θ σ r p q s) (rule θ supp r).dst H inp →
      Mach.SumTo (universalMachine θ supp) (Uni.step θ σ r p q s) S (B - 1))
    (hs : (rule θ supp r).src = md := by rfl) (hk : (rule θ supp r).lk = κ := by rfl)
    (hrd : (rule θ supp r).rd = none := by rfl) :
    Mach.SumTo (universalMachine θ supp) σ ((rule θ supp r).wt * S) B := by
  have hσ' := hσ
  obtain ⟨wf, rfl, -, -⟩ := hσ
  refine (Uni.sumTo_rule wf hrec r hr ?_ ?_ hs hk (h (hσ'.step rfl hrd))).mono (by omega)
  · intro e
    rw [e] at hr
    cases κ <;> cases hr
  · rintro ⟨e, rfl⟩
    rw [e] at hr
    cases hr

/-- A forced step with a rule of weight `1`. -/
theorem sumTo_step (hσ : InMode σ md H inp)
    (hrec : ((κ, ![σ.regs (loadReg md), p, q, s]) : Rec RecKind) ∈ σ.heap)
    (hr : nextRule supp md κ = some r)
    (h : InMode (Uni.step θ σ r p q s) (rule θ supp r).dst H inp →
      Mach.SumTo (universalMachine θ supp) (Uni.step θ σ r p q s) S (B - 1))
    (hs : (rule θ supp r).src = md := by rfl) (hk : (rule θ supp r).lk = κ := by rfl)
    (hrd : (rule θ supp r).rd = none := by rfl) (hw : (rule θ supp r).wt = 1 := by rfl) :
    Mach.SumTo (universalMachine θ supp) σ S B := by
  simpa [hw] using hσ.sumTo_rule hrec hr h hs hk hrd

/-- No rule applies. -/
theorem sumTo_zero (hσ : InMode σ md H inp)
    (hrec : ((κ, ![σ.regs (loadReg md), p, q, s]) : Rec RecKind) ∈ σ.heap)
    (hr : nextRule supp md κ = none) (B : ℤ) (hP : md ≠ .parse := by rintro ⟨⟩)
    (hD : md ≠ .decode 7 := by rintro ⟨⟩) (hz : md ≠ .halt := by rintro ⟨⟩) :
    Mach.SumTo (universalMachine θ supp) σ 0 B := by
  obtain ⟨wf, rfl, -, -⟩ := hσ
  exact sumTo_stuck wf hrec hr hP (fun e => hD e.1) hz B

end InMode

variable {σ : Config supp} {H : List (Rec RecKind)} {k : ℕ} {inp : List Bool} {o a x : Tree}
  {S : A} {B : ℤ}

/-- What happens when the value `o` is returned to the frame at the address `k`: the run sum
is `S`, within `B` steps. -/
@[expose] def Returns (θ : List Bool → A) (supp : Finset (List Bool)) (H : List (Rec RecKind))
    (k : ℕ) (inp : List Bool) (o : Tree) (S : A) (B : ℤ) : Prop :=
  ∀ σ : Config supp, InMode σ .ret H inp → σ.regs 2 = k → Represents σ.heap (σ.regs 1) o →
    Mach.SumTo (universalMachine θ supp) σ S B

/-- The bound for the lengths of names. -/
@[expose] def nameLength (supp : Finset (List Bool)) : ℕ := supp.sup List.length

variable (supp) in
/-- The number of steps of the machine for one step of the evaluation. -/
@[expose] def codeCost : ℤ := 40 + 2 * (nameLength supp : ℤ)

theorem codeCost_ge : 40 ≤ codeCost supp := le_add_of_nonneg_right (by positivity)

private theorem length_le_nameLength {p : List Bool} (hp : p ∈ prefixes supp) :
    p.length ≤ nameLength supp := by
  obtain ⟨q, hq, h⟩ := mem_prefixes.1 hp
  exact h.length_le.trans (Finset.le_sup (f := List.length) hq)

/-- Reading a name: from the mode `thetaHead p` with the rest `w` of the name at register `1`,
the machine multiplies by `θ (p ++ w.path)` and returns `nil` to the frame at register `2`. -/
theorem sumTo_readName (hθ : ∀ q, q ∉ supp → θ q = 0) (w : Tree) :
    ∀ (p : Name supp) (σ : Config supp), InMode σ (.thetaHead p) H inp →
      Represents σ.heap (σ.regs 1) w → σ.regs 2 = k → Returns θ supp H k inp .nil S B →
      Mach.SumTo (universalMachine θ supp) σ (θ (p.1 ++ w.path) * S)
        (B + 1 + 2 * (nameLength supp - p.1.length : ℕ)) := by
  induction w with
  | nil =>
    intro p σ hσ hw hk h
    rw [Tree.path, List.append_nil]
    exact .mono (hσ.sumTo_rule (B := B + 1) (hσ.wf.nil_mem hw) rfl fun h₁ =>
      .mono (h _ h₁ hk hσ.wf.r0) (by omega)) (by omega)
  | cons a b _ ih =>
    intro p σ hσ hw hk h
    obtain ⟨pa, pb, s, hrec, ha, hb⟩ := hw
    refine hσ.sumTo_step hrec rfl fun h₁ => ?_
    obtain ⟨x₁, x₂, x₃, hx, -, -⟩ := ha.step.load h₁.wf
    rw [Tree.path, List.append_cons]
    generalize decide (a ≠ .nil) = bt at hx ⊢
    by_cases hp : p.1 ++ [bt] ∈ prefixes supp
    · have hl := length_le_nameLength hp
      exact h₁.sumTo_step hx (r := .thetaBit p ⟨_, hp⟩ bt rfl)
        (by cases bt <;> exact dite_eq_left hp)
        fun h₂ => .mono (ih ⟨_, hp⟩ _ h₂ hb.step.step hk h) (by
          simp only [List.length_append, List.length_singleton] at hl ⊢; omega)
    · rw [hθ _ fun hq => hp (mem_prefixes.2 ⟨_, hq, List.prefix_append _ _⟩), zero_mul]
      exact h₁.sumTo_zero hx (by cases bt <;> exact dite_eq_right hp) _

/-- The weight of a run that names no constants; the other runs count `0`. -/
@[expose] def plainWeight (r : Run A) : A := if r.bill = [] then r.th else 0

/-- The sum, over the runs `r` without named constants, of the weight of `r` times `m r`. -/
@[expose] def plainValue (m : Run A → A) (l : List (Run A)) : A :=
  (l.map fun r => plainWeight r * m r).sum

@[simp] theorem plainWeight_det (n : ℕ) (o : Tree) : plainWeight (.det n o : Run A) = 1 := rfl

@[simp] theorem plainWeight_tick (r : Run A) (o : Tree) :
    plainWeight (r.tick o) = plainWeight r := rfl

@[simp] theorem plainWeight_seq (r s : Run A) :
    plainWeight (r.seq s) = plainWeight r * plainWeight s := by
  by_cases hr : r.bill = [] <;> by_cases hs : s.bill = [] <;> simp [plainWeight, Run.seq, hr, hs]

theorem plainValue_map_tick (m : Run A → A) (l : List (Run A)) (f : Run A → Tree) :
    plainValue m (l.map fun r => r.tick (f r)) = plainValue (fun r => m (r.tick (f r))) l := by
  simp [plainValue, Function.comp_def]

/-- One run after the other. -/
theorem plainValue_seq (m : Run A → A) (la : List (Run A)) (L : Run A → List (Run A))
    (f : Run A → Run A → Tree) :
    plainValue m (la.flatMap fun r => (L r).map fun s => (r.seq s).tick (f r s)) =
      plainValue (fun r => plainValue (fun s => m ((r.seq s).tick (f r s))) (L r)) la := by
  simp only [plainValue, List.sum_map_flatMap, List.map_map, Function.comp_def, plainWeight_tick,
    plainWeight_seq, mul_assoc, List.sum_map_mul_left]

/-- Three runs, one after the other. -/
theorem plainValue_seq₃ (m : Run A → A) (la lb : List (Run A))
    (L : Run A → Run A → List (Run A)) :
    plainValue m (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t =>
        ((r.seq s).seq t).tick t.out) =
      plainValue (fun r => plainValue (fun s => plainValue (fun t =>
        m (((r.seq s).seq t).tick t.out)) (L r s)) lb) la := by
  simp only [plainValue, List.sum_map_flatMap, List.map_map, Function.comp_def, plainWeight_tick,
    plainWeight_seq, mul_assoc, List.sum_map_mul_left]

/-- The machine is about to evaluate the formula with the code `c` at the tree `x`, to return
the value to the frame at `k`. -/
structure EvalReady (σ : Config supp) (c x : Tree) (H : List (Rec RecKind)) (k : ℕ)
    (inp : List Bool) : Prop where
  inMode : InMode σ .eval H inp
  code : Represents σ.heap (σ.regs 1) c
  arg : Represents σ.heap (σ.regs 2) x
  frame : σ.regs 3 = k

/-- Reading the number of an opcode, from the `j`-th step on. -/
private theorem sumTo_opcodeChain (o : Tree) : ∀ (j : Fin 11) (σ : Config supp),
    InMode σ (.decode j) H inp → Represents σ.heap (σ.regs 1) o →
    (∀ (j' : Fin 11) (σ' : Config supp), j + o.len = j' → InMode σ' (.decode j') H inp →
      σ'.regs 1 = 0 → σ'.regs 2 = σ.regs 2 → σ'.regs 3 = σ.regs 3 → σ'.regs 4 = σ.regs 4 →
      Mach.SumTo (universalMachine θ supp) σ' S B) →
    (11 ≤ j + o.len → S = 0) → Mach.SumTo (universalMachine θ supp) σ S (B + o.len) := by
  induction o with
  | nil =>
    intro j σ hσ ho h _
    simpa [Tree.len] using h j σ rfl hσ ho rfl rfl rfl
  | cons a b _ ih =>
    intro j σ hσ ho h hS
    obtain ⟨p, q, s, hrec, -, hq⟩ := ho
    simp only [Tree.len] at h hS ⊢
    by_cases hj : j.1 < 10
    · refine hσ.sumTo_step hrec (dite_eq_left hj) fun h₁ => ?_
      exact .mono (ih ⟨j + 1, by omega⟩ _ h₁ hq.step
        (fun j' σ' e => h j' σ' (by dsimp only at e; omega))
        fun hl => hS (by dsimp only at hl; omega)) (by omega)
    · obtain rfl := hS (by omega)
      exact hσ.sumTo_zero hrec (dite_eq_right hj) _ (by simp) (by rintro ⟨⟩; exact hj (by decide))

/-- **Reading the opcode** of the code `cons o a`: `o.len + 1` steps lead to the mode
`decode o.len`, with `a` at register `2`, the argument at register `3` and the frame at
register `4`. Numbers from `11` on are no opcodes, and the machine stops. -/
private theorem EvalReady.sumTo_opcode (hσ : EvalReady σ (.cons o a) x H k inp)
    (h : ∀ j : Fin 11, o.len = j → ∀ σ' : Config supp, InMode σ' (.decode j) H inp →
      σ'.regs 1 = 0 → Represents σ'.heap (σ'.regs 2) a → Represents σ'.heap (σ'.regs 3) x →
      σ'.regs 4 = k → Mach.SumTo (universalMachine θ supp) σ' S B)
    (h0 : 11 ≤ o.len → S = 0) : Mach.SumTo (universalMachine θ supp) σ S (B + 11) := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hσ.code
  refine hσ.inMode.sumTo_step hrec rfl fun h₁ => ?_
  exact .mono (sumTo_opcodeChain (B := B + 10 - o.len) o 0 _ h₁.self hp.step
    (fun j' σ' e h' e₁ e₂ e₃ e₄ => .mono (h j' (by simpa using e) σ' (h'.mono h₁.heap) e₁
      (e₂ ▸ hq.step.mono h'.heap) (e₃ ▸ hσ.arg.step.mono h'.heap) (e₄.trans hσ.frame)) (by omega))
    (by simpa using h0)) (by omega)

/-- Reading the opcode `j` and the step after it, by the rule for the mode `decode j`. -/
theorem EvalReady.sumTo_decode (hσ : EvalReady σ (.cons o a) x H k inp) (j : Fin 11)
    (ho : o.len = j) {r : Rule supp} (hr : nextRule supp (.decode j) .nil = some r)
    (h : ∀ σ' : Config supp, Represents σ'.heap (σ'.regs 2) a →
      Represents σ'.heap (σ'.regs 3) x → σ'.regs 4 = k →
      InMode (step θ σ' r 0 0 0) (rule θ supp r).dst H inp →
      Mach.SumTo (universalMachine θ supp) (step θ σ' r 0 0 0) S B)
    (hs : (rule θ supp r).src = .decode j := by rfl) (hk : (rule θ supp r).lk = .nil := by rfl)
    (hrd : (rule θ supp r).rd = none := by rfl) (hw : (rule θ supp r).wt = 1 := by rfl) :
    Mach.SumTo (universalMachine θ supp) σ S (B + 12) := by
  refine (hσ.sumTo_opcode (B := B + 1) (fun j' hj' σ' h' h₁ ha hx hk' => ?_)
    fun hl => absurd hl (by omega)).mono (by omega)
  obtain rfl : j' = j := Fin.ext (hj'.symm.trans ho)
  exact h'.sumTo_step (h'.wf.nil_mem h₁) hr (fun h₂ => (h σ' ha hx hk' h₂).mono (by omega))
    hs hk hrd hw

variable (θ supp) in
/-- **The machine evaluates the code `c` at `x` correctly**, if `l` is the list of the accepting
runs: from a state that is ready, the run sum is `plainValue m l` within `B` steps, if for every
run `r` in `l` without named constants the run sum after the return of the value of `r` is `m r`
within `B - codeCost supp * r.cost` steps. -/
@[expose] def EvalsTo (c x : Tree) (l : List (Run A)) : Prop :=
  ∀ (σ : Config supp) (H : List (Rec RecKind)) (k : ℕ) (inp : List Bool),
    EvalReady σ c x H k inp → ∀ (m : Run A → A) (B : ℤ),
    (∀ r ∈ l, r.bill = [] → Returns θ supp H k inp r.out (m r) (B - codeCost supp * r.cost)) →
    Mach.SumTo (universalMachine θ supp) σ (plainValue m l) B

/-- The return of the value of the only run of `quote` and `id`. -/
private theorem Returns.det {v : Tree} {m : Run A → A} (h : ∀ r ∈ [(.det 1 v : Run A)],
    r.bill = [] → Returns θ supp H k inp r.out (m r) (B - codeCost supp * r.cost)) :
    Returns θ supp H k inp v (plainValue m [.det 1 v]) (B - 13) := fun σ hσ hk hv => by
  simpa [plainValue] using (h (.det 1 v) (by simp) rfl σ hσ hk hv).mono (by
    simp only [Run.det, Nat.cast_one]; linarith [codeCost_ge (supp := supp)])

/-- The empty code is `quote nil`. -/
theorem EvalsTo.nil : EvalsTo θ supp .nil x [.det 1 .nil] := fun _ _ _ _ hσ _ _ h =>
  hσ.inMode.sumTo_step (hσ.inMode.wf.nil_mem hσ.code) rfl fun h₁ =>
    .mono (Returns.det h _ h₁ hσ.frame hσ.code) (by omega)

theorem EvalsTo.quote (ho : o.len = 0) : EvalsTo θ supp (.cons o a) x [.det 1 a] :=
  fun _ _ _ _ hσ _ B h => .mono (hσ.sumTo_decode (B := B - 12) 0 ho rfl fun _ ha _ hk h₂ =>
    .mono (Returns.det h _ h₂ hk ha.step) (by omega)) (by omega)

theorem EvalsTo.id (ho : o.len = 1) : EvalsTo θ supp (.cons o a) x [.det 1 x] :=
  fun _ _ _ _ hσ _ B h => .mono (hσ.sumTo_decode (B := B - 12) 1 ho rfl fun _ _ hx hk h₂ =>
    .mono (Returns.det h _ h₂ hk hx.step) (by omega)) (by omega)

/-- The opcodes `8` (`fail`) and `10` (`mul`) and the numbers from `11` on have no rule. -/
private theorem EvalReady.sumTo_noRule (hσ : EvalReady σ (.cons o a) x H k inp)
    (ho : o.len = 8 ∨ o.len = 10 ∨ 11 ≤ o.len) :
    Mach.SumTo (universalMachine θ supp) σ 0 B := by
  refine .mono (hσ.sumTo_opcode (B := B - 11) (fun j hj σ₁ h₁ h₁₁ _ _ _ => ?_) fun _ => rfl)
    (by omega)
  obtain rfl | rfl : j = 8 ∨ j = 10 := by rw [Fin.ext_iff, Fin.ext_iff]; omega
  all_goals exact h₁.sumTo_zero (h₁.wf.nil_mem h₁₁) rfl _

theorem EvalsTo.fail (ho : o.len = 8 ∨ 11 ≤ o.len) : EvalsTo θ supp (.cons o a) x [] :=
  fun _ _ _ _ hσ _ _ _ => hσ.sumTo_noRule (by omega)

/-- Naming a constant stops the machine: such runs do not count. -/
theorem EvalsTo.mul (ho : o.len = 10) (l : List (Run A)) : EvalsTo θ supp (.cons o a) x
    (l.map fun r => ⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩) := by
  intro σ H k inp hσ m B _
  simpa [plainValue, plainWeight, Function.comp_def] using hσ.sumTo_noRule (by omega)

/-- The rules for the mode `decode 7` at the empty record are the two guesses. -/
private theorem eq_decodeGuess {r : Rule supp} (hs : (rule θ supp r).src = .decode 7)
    (hk : (rule θ supp r).lk = .nil) : ∃ b, r = .base (.decodeGuess b) := by
  cases r with
  | base r =>
    cases r <;> first | exact ⟨_, rfl⟩ | simp [rule, baseRule, RuleData.basic] at hs hk
  | _ => simp [rule, RuleData.basic] at hs

theorem EvalsTo.guess (ho : o.len = 7) :
    EvalsTo θ supp (.cons o a) x [.det 1 .nil, .det 1 Tree.one] := by
  intro σ H k inp hσ m B h
  have hB : B - codeCost supp * (1 : ℕ) ≤ B - 12 := by
    push_cast; linarith [codeCost_ge (supp := supp)]
  simp only [plainValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    plainWeight_det]
  refine .mono (hσ.sumTo_opcode (B := B - 11) (fun j hj σ₁ hσ₁ h₁₁ _ _ hk => ?_) (by omega))
    (by omega)
  obtain rfl : j = 7 := Fin.ext (hj.symm.trans ho)
  have hrec : ((.nil, ![σ₁.regs (loadReg σ₁.mode), 0, 0, 0]) : Rec RecKind) ∈ σ₁.heap :=
    hσ₁.mode.symm ▸ hσ₁.wf.nil_mem h₁₁
  have g₀ := (h (.det 1 .nil) (by simp) rfl (step θ σ₁ (.base (.decodeGuess false)) 0 0 0)
    hσ₁.step hk hσ₁.wf.r0).mono hB
  have g₁ := (h (.det 1 Tree.one) (by simp) rfl (step θ σ₁ (.base (.decodeGuess true)) 0 0 0)
    hσ₁.step hk ⟨_, _, _, mem_heap_step σ₁ _ 0 0 0, hσ₁.wf.r0, hσ₁.wf.r0⟩).mono hB
  refine .mono (Mach.SumTo.two (B := B - 12) (hσ₁.mode.symm ▸ by rintro ⟨⟩) _ _
    (by rintro ⟨⟩) (fun st => ?_) g₀ g₁)
    (by omega)
  rw [fire_iff hσ₁.wf hrec, hσ₁.mode]
  constructor
  · rintro ⟨e₁, e₂, -, e₄⟩
    obtain ⟨_ | _, hb⟩ := eq_decodeGuess e₁ e₂
    exacts [.inl (Prod.ext hb e₄), .inr (Prod.ext hb e₄)]
  · rintro (rfl | rfl) <;> exact ⟨rfl, rfl, List.nil_prefix, rfl⟩

end Cslib.Circuits.Arithmetic.Separation.Uni
