/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.GhostLoop
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.Computability.WordRAM.RegisterCopy
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.Tactic.FinIndex

/-!
# Bounded memory-client loops

Bounded iteration remains an ordinary `Memory.Prog` term. The local-work currency counts body
work and every iteration, including iterations issuing no memory query. The native realization
uses one fixed body emitter and static registers for the mutable state and countdown counter.

## Main definitions

* `iterate`: bounded iteration in the existing memory-client monad.
* `iterationWork`, `iterationSafe`: local work and domains along the actual semantic states.
* `loopEmit`, `loopBody`: the native loop with a fixed body emitter, and one native iteration,
  over the register bank `stateSlot`, `counterSlot`, `zeroSlot`, `oneSlot`, `bodySlot`.

## Main results

* `iterationSum_eq`: the native grading rule's semantic sum is memory charge plus local work.
* `loopEmit_entry`, `loopBody_tail`: the native loop's entry prologue and the control tail of one
  iteration, shared by the deterministic and randomized loop realizations.
* `bodyBank_layout`, `bodySlot_injective`, `stateSlot_ne_bodySlot`,
  `regs_comp_append_eq_appendWords`, `loopEmit_not_readsWidth`, `loopEmit_instantiate`: the body
  bank's register premises, the state words read back as appended words, width-freedom of the loop,
  and instantiating a body contract at `loopEmit`'s sub-banks.
* `iterationWork_zero`: evaluate local work when the body has no local-work charge.
* `Realizes.Witness.loopEmit_spec`: the loop emitter with additive per-iteration overhead.
* `Realizes.Witness.iterateRuntime`, `Realizes.iterateRuntime`: one uniform body witness or
  certificate realizes a runtime-bounded loop.

The iteration grading and realization are original infrastructure over the existing free monad
and structured Word-RAM code. No additional program syntax or memory model is introduced.
Fixed-environment transport laws are provided by the `LoopCongr` module.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ σ : Type} {B : Basis} {r k l : ℕ}

/-- Execute one fixed body family a runtime-bounded number of times. -/
def iterate (body : δ × σ → Memory.Prog σ) (d : δ) : ℕ → σ → Memory.Prog σ
  | 0, s => pure s
  | n + 1, s => do
      let s' ← body (d, s)
      iterate body d n s'

/-- Local computation and one control-work unit per iteration, along actual semantic states. -/
def iterationWork (body : δ × σ → Memory.Prog σ) (work : (δ × σ) → Memory.State → ℕ)
    (d : δ) : ℕ → σ → Memory.State → ℕ
  | 0, _, _ => 0
  | n + 1, a, s =>
      work (d, a) s + iterationWork body work d n
        ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a))) + 1

/-- With no body-local work, the local grade is exactly one control unit per iteration. -/
@[simp] theorem iterationWork_zero (body : δ × σ → Memory.Prog σ) (d : δ) (n : ℕ) (a : σ)
    (s : Memory.State) : iterationWork body (fun _ _ => 0) d n a s = n := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih => simp only [iterationWork, ih, Nat.zero_add]

/-- Every executed body must satisfy its explicit domain at the reached state. -/
def iterationSafe (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ) :
    ℕ → σ → Memory.State → Prop
  | 0, _, _ => True
  | n + 1, a, s => safe w (d, a) s ∧ iterationSafe body safe w d n
      ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))

/-- Memory cost and certified local work decompose at each actual iteration. -/
theorem iteration_charge_succ (body : δ × σ → Memory.Prog σ)
    (work : (δ × σ) → Memory.State → ℕ) (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (iterate body d (n + 1) a) s + iterationWork body work d (n + 1) a s =
      memoryCost (body (d, a)) s + work (d, a) s +
      (memoryCost (iterate body d n ((Memory.spec 0).clientResult s (body (d, a))))
        ((Memory.spec 0).clientState s (body (d, a))) +
      iterationWork body work d n ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))) + 1 := by
  rw [show iterate body d (n + 1) a =
    (body (d, a)).bind (iterate body d n) from rfl, memoryCost_bind]
  simp only [iterationWork]
  omega

/-- One semantic iteration updates both the mutable value and the complete memory state. -/
def iterationStep (body : δ × σ → Memory.Prog σ) (d : δ) (a : σ × Memory.State) :
    σ × Memory.State :=
  ((Memory.spec 0).clientResult a.2 (body (d, a.1)),
    (Memory.spec 0).clientState a.2 (body (d, a.1)))

/-- The interpreter follows precisely the bounded semantic transition, not an arbitrary state. -/
theorem iterate_result_state (body : δ × σ → Memory.Prog σ) (d : δ) (n : ℕ) (a : σ)
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (iterate body d n a),
      (Memory.spec 0).clientState s (iterate body d n a)) =
      (iterationStep body d)^[n] (a, s) := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    rw [show iterate body d (n + 1) a =
      (body (d, a)).bind (iterate body d n) from rfl]
    simpa only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_bind, Function.iterate_succ_apply, iterationStep] using
      ih ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))

/-- The native grading rule's semantic sum is exactly memory charge plus local iteration work. -/
theorem iterationSum_eq (body : δ × σ → Memory.Prog σ)
    (work : (δ × σ) → Memory.State → ℕ) (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    iterationSum (iterationStep body d)
        (fun q => memoryCost (body (d, q.1)) q.2 + work (d, q.1) q.2) n (a, s) + n =
      memoryCost (iterate body d n a) s + iterationWork body work d n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    rw [iterationSum, iteration_charge_succ]
    have h := ih ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))
    dsimp only [iterationStep] at *
    omega

/-- The loop's state words, which are also its result slots. -/
def stateSlot {l n : ℕ} (i : Fin l) : Fin (l + (l + n + 3) + 1) :=
  ⟨i.val, by omega⟩

/-- The loop's countdown register. -/
def counterSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l, by omega⟩
/-- A register holding zero, for the loop test. -/
def zeroSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l + 1, by omega⟩
/-- A register holding one, for the countdown. -/
def oneSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l + 2, by omega⟩

/-- The body's scratch bank inside the loop's bank. -/
def bodySlot {l n : ℕ} (i : Fin (l + n + 1)) : Fin (l + (l + n + 3) + 1) :=
  ⟨l + 3 + i.val, by omega⟩

/-- One native iteration: run the body on the environment and state words, copy its result into
the state words and count down. -/
def loopBody {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
    (Fin (l + n + 1) → Fin r) → Code .exact r)
    (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
    (tmp : Fin (l + (l + n + 3) + 1) → Fin r) : Code .exact r :=
  .seq (emit frontier (Fin.append (fun i : Fin k => src ⟨i.val, by omega⟩)
    (fun i => tmp (stateSlot i))) (fun i => tmp (bodySlot i))) <|
    .seq (copyBank (fun i : Fin l => tmp (bodySlot (Fin.castAdd (n + 1) i)))
      (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) <|
      .seq (.op (.const (tmp (oneSlot l n)) 1))
        (.op (.exactBin .sub (tmp (counterSlot l n))
          (tmp (counterSlot l n)) (tmp (oneSlot l n))))

/-- The native loop: install the state words and the counter, then iterate `loopBody` while the
counter is positive. -/
def loopEmit {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
    (Fin (l + n + 1) → Fin r) → Code .exact r)
    (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
    (tmp : Fin (l + (l + n + 3) + 1) → Fin r) : Code .exact r :=
  .seq (copyBank (fun i : Fin l => src ⟨k + i.val, by omega⟩)
    (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) <|
    .seq (.op (.copy (tmp (counterSlot l n)) (src ⟨k + l, by omega⟩))) <|
      .seq (.op (.const (tmp (zeroSlot l n)) 0))
        (.loop (.lt (tmp (zeroSlot l n)) (tmp (counterSlot l n)))
          (loopBody emit frontier src tmp))

/-- Registers holding the environment words followed by the state words read back the appended
words. -/
theorem regs_comp_append_eq_appendWords (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {x : Data r} {env : Fin k → Fin r} {st : Fin l → Fin r} {d : δ} {a : σ}
    (henv : ∀ i, x.regs (env i) = input d i) (hst : ∀ i, x.regs (st i) = output a i) :
    x.regs ∘ Fin.append env st = appendWords input output (d, a) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa [appendWords, Fin.appendEquiv] using henv i
  · simpa [appendWords, Fin.appendEquiv] using hst i

/-- A body bank `tmp ∘ btS` inside an injective scratch bank `tmp` meets the register hypotheses
of the body's certificate, which reads the environment `env` and the state words `tmp ∘ stS`. -/
theorem bodyBank_layout {m p : ℕ} {frontier : Fin r} {env : Fin k → Fin r}
    {tmp : Fin m → Fin r} {stS : Fin l → Fin m} {btS : Fin p → Fin m}
    (hi : Function.Injective tmp) (hbt : Function.Injective btS) (hsb : ∀ i j, stS i ≠ btS j)
    (hd : ∀ i j, env i ≠ tmp j) (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, env i ≠ frontier) :
    Function.Injective (fun j => tmp (btS j)) ∧
      (∀ i j, Fin.append env (fun i => tmp (stS i)) i ≠ tmp (btS j)) ∧
      (∀ j, tmp (btS j) ≠ frontier) ∧
      ∀ i, Fin.append env (fun i => tmp (stS i)) i ≠ frontier := by
  refine ⟨hi.comp hbt, fun i j => ?_, fun j => hf _, fun i => ?_⟩ <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [Fin.append_left] using hd i (btS j)
  · simpa only [Fin.append_right] using hi.ne (hsb i j)
  · simpa only [Fin.append_left] using hs i
  · simpa only [Fin.append_right] using hf (stS i)

/-- The native loop reads the word width only where its body does. -/
theorem loopEmit_not_readsWidth {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code .exact r)
    {frontier : Fin r} {src : Fin (k + l + 1) → Fin r} {tmp : Fin (l + (l + n + 3) + 1) → Fin r}
    (hnw : ¬(emit frontier (Fin.append (fun i : Fin k => src ⟨i.val, by omega⟩)
      (fun i => tmp (stateSlot i))) fun i => tmp (bodySlot i)).ReadsWidth) :
    ¬(loopEmit emit frontier src tmp).ReadsWidth := by
  simpa [loopEmit, loopBody, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    copyBank_not_readsWidth] using hnw

/-- The loop's body bank does not repeat a register. -/
theorem bodySlot_injective {n : ℕ} : Function.Injective (bodySlot (l := l) (n := n)) := by
  fin_index [bodySlot]

/-- The loop's state words lie outside its body bank. -/
theorem stateSlot_ne_bodySlot {n : ℕ} (i : Fin l) (j : Fin (l + n + 1)) :
    stateSlot (n := n) i ≠ bodySlot j := by
  fin_index [stateSlot, bodySlot]

/-- Instantiate a body emitter's register-bank contract at the sub-banks of `loopEmit`, pairing
width-freedom of `loopEmit` with the instantiated body contract. -/
theorem loopEmit_instantiate {n : ℕ}
    (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code .exact r)
    {P : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) → (Fin (l + n + 1) → Fin r) → Prop}
    (he : ∀ {r : ℕ} (frontier : Fin r) (bs : Fin (k + l) → Fin r)
      (bt : Fin (l + n + 1) → Fin r),
      Function.Injective bt → (∀ i j, bs i ≠ bt j) → (∀ j, bt j ≠ frontier) →
      (∀ i, bs i ≠ frontier) → ¬(emit frontier bs bt).ReadsWidth ∧ P frontier bs bt)
    {frontier : Fin r} {src : Fin (k + l + 1) → Fin r}
    {tmp : Fin (l + (l + n + 3) + 1) → Fin r}
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(loopEmit emit frontier src tmp).ReadsWidth ∧
      P frontier (Fin.append (fun i : Fin k => src ⟨i.val, by omega⟩)
        (fun i => tmp (stateSlot i))) (fun i => tmp (bodySlot i)) := by
  obtain ⟨hbt, hbdis, hbf, hbs⟩ := bodyBank_layout
    (env := fun i : Fin k => src ⟨i.val, by omega⟩) hi bodySlot_injective
    stateSlot_ne_bodySlot (fun _ _ => hd _ _) hf (fun _ => hs _)
  obtain ⟨hnw, hrun⟩ := he frontier _ _ hbt hbdis hbf hbs
  exact ⟨loopEmit_not_readsWidth emit hnw, hrun⟩

/-- Entering the native loop of `loopEmit`: copy the state words into the bank, install the
counter and clear the zero register. Memory, the frontier and every register outside the scratch
bank are unchanged. -/
theorem loopEmit_entry (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ)) {n : ℕ}
    {frontier : Fin r} {src : Fin (k + l + 1) → Fin r} {tmp : Fin (l + (l + n + 3) + 1) → Fin r}
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j) (hf : ∀ j, tmp j ≠ frontier)
    {w : ℕ} {x : Data r} {d : δ} {a : σ} {fuel : ℕ} (hx : x.Bounded w)
    (hin : x.regs ∘ src = (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
      (Fin.appendEquiv (k + l) 1).toEmbedding) ((d, a), fuel)) :
    ∃ x₁ x₂ z,
      ExecWithin (B := .exact) w (copyBank (fun i : Fin l => src ⟨k + i.val, by omega⟩)
        (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) x x₁ (l + 1) ∧
      ExecWithin (B := .exact) w (.op (.copy (tmp (counterSlot l n)) (src ⟨k + l, by omega⟩)))
        x₁ x₂ 1 ∧
      ExecWithin (B := .exact) w (.op (.const (tmp (zeroSlot l n)) 0)) x₂ z 1 ∧
      z.Bounded w ∧ memoryState frontier z = memoryState frontier x ∧
      (∀ i : Fin k, z.regs (src ⟨i.val, by omega⟩) = input d i) ∧
      (∀ i, z.regs (tmp (stateSlot i)) = output a i) ∧
      z.regs (tmp (counterSlot l n)) = fuel ∧ z.regs (tmp (zeroSlot l n)) = 0 ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → z.regs i = x.regs i := by
  let st : Fin l → Fin r := fun i => tmp (stateSlot i)
  let ctr := tmp (counterSlot l n)
  let zero := tmp (zeroSlot l n)
  let env : Fin k → Fin r := fun i => src ⟨i.val, by omega⟩
  have hct : ctr ≠ zero := hi.ne (by fin_index [counterSlot, zeroSlot])
  have henv (i : Fin k) : x.regs (src (Fin.castAdd 1 (Fin.castAdd l i))) = input d i := by
    simpa [appendWords, Fin.appendEquiv] using congrFun hin (Fin.castAdd 1 (Fin.castAdd l i))
  have hstate (i : Fin l) : x.regs (src (Fin.castAdd 1 (Fin.natAdd k i))) = output a i := by
    simpa [appendWords, Fin.appendEquiv] using congrFun hin (Fin.castAdd 1 (Fin.natAdd k i))
  have hfuel : x.regs (src (Fin.natAdd (k + l) 0)) = fuel := by
    simpa [Fin.appendEquiv] using congrFun hin (Fin.natAdd (k + l) 0)
  obtain ⟨x₁, h₁, h₁m, h₁s, h₁f⟩ := copyBank_exec (fun i : Fin l => src ⟨k + i.val, by omega⟩)
    st zero (fun i j h => Fin.ext (congrArg Fin.val (hi h) :)) (fun _ _ => hd _ _) w x
  let x₂ := x₁.set ctr fuel
  let z := x₂.set zero 0
  have h₁fuel : x₁.regs (src ⟨k + l, by omega⟩) = fuel := (h₁f _ fun _ => (hd _ _).symm).trans hfuel
  have h₂ : ExecWithin (B := .exact) w (.op (.copy ctr (src ⟨k + l, by omega⟩))) x₁ x₂ 1 := by
    wram_exec [h₁fuel]
  have h₃ : ExecWithin (B := .exact) w (.op (.const zero 0)) x₂ z 1 := .const (fits_zero w)
  refine ⟨x₁, x₂, z, h₁, h₂, h₃, (h₁.seq (h₂.seq h₃)).bounded hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Memory.State.ext h₁m ?_
    change (x₂.set zero 0).regs frontier = x.regs frontier
    wram_simp [x₂]
    exact h₁f frontier fun i => hf _
  · intro i
    wram_simp [z, x₂]
    exact (h₁f _ fun _ => (hd _ _).symm).trans (henv i)
  · intro i
    change z.regs (st i) = _
    wram_simp [z, x₂, st, zero, ctr]
    exact (h₁s i).trans (hstate i)
  · change z.regs ctr = fuel
    wram_simp [z, x₂]
  · change z.regs zero = 0
    wram_simp [z]
  · intro i hif htmp
    wram_simp [z, x₂]
    exact h₁f _ fun _ => htmp _

/-- The control tail of one iteration of `loopBody`, after the body ran from `y` to `u`: copy the
body's result words into the state words and count down. Memory, the frontier, the zero register
and every register outside the scratch bank keep their values. -/
theorem loopBody_tail {n : ℕ} (frontier : Fin r) (tmp : Fin (l + (l + n + 3) + 1) → Fin r)
    (hi : Function.Injective tmp) (hf : ∀ j, tmp j ≠ frontier) (w j : ℕ) {y u : Data r}
    (hub : u.Bounded w) (hyc : y.regs (tmp (counterSlot l n)) = j + 1)
    (huf : ∀ i, i ≠ frontier → (∀ b, tmp (bodySlot b) ≠ i) → u.regs i = y.regs i) :
    ∃ y', ExecWithin (B := .exact) w
        (.seq (copyBank (fun i : Fin l => tmp (bodySlot (Fin.castAdd (n + 1) i)))
          (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) <|
          .seq (.op (.const (tmp (oneSlot l n)) 1))
            (.op (.exactBin .sub (tmp (counterSlot l n)) (tmp (counterSlot l n))
              (tmp (oneSlot l n))))) u y' (l + 3) ∧
      memoryState frontier y' = memoryState frontier u ∧
      (∀ i, y'.regs (tmp (stateSlot i)) = u.regs (tmp (bodySlot (Fin.castAdd (n + 1) i)))) ∧
      y'.regs (tmp (counterSlot l n)) = j ∧
      y'.regs (tmp (zeroSlot l n)) = y.regs (tmp (zeroSlot l n)) ∧
      ∀ i, i ≠ frontier → (∀ b, tmp b ≠ i) → y'.regs i = y.regs i := by
  let st : Fin l → Fin r := fun i => tmp (stateSlot i)
  let ctr := tmp (counterSlot l n)
  let zero := tmp (zeroSlot l n)
  let one := tmp (oneSlot l n)
  have hco : ctr ≠ one := hi.ne (by fin_index [counterSlot, oneSlot])
  have hzc : zero ≠ ctr := hi.ne (by fin_index [counterSlot, zeroSlot])
  have hzo : zero ≠ one := hi.ne (by fin_index [zeroSlot, oneSlot])
  have hregbt (a : Fin (l + (l + n + 3) + 1)) (ha : a.val < l + 3) :
      ∀ j, tmp (bodySlot j) ≠ tmp a :=
    fun j => hi.ne (by fin_index [bodySlot])
  have hregst (a : Fin (l + (l + n + 3) + 1)) (ha : l ≤ a.val) : ∀ i, st i ≠ tmp a :=
    fun i => hi.ne (by fin_index [stateSlot])
  obtain ⟨v, hv, hvm, hvs, hvf⟩ := copyBank_exec
    (fun i : Fin l => tmp (bodySlot (Fin.castAdd (n + 1) i))) st zero
    (fun i j h => Fin.ext (congrArg Fin.val (hi h) :))
    (fun i j => hi.ne (stateSlot_ne_bodySlot j _).symm) w u
  have huc : u.regs ctr = j + 1 := (huf _ (hf _) (hregbt _ (by simp [counterSlot]))).trans hyc
  have hvctr : v.regs ctr = j + 1 := (hvf _ (hregst _ (by simp [counterSlot]))).trans huc
  have hvzero : v.regs zero = y.regs zero := by
    rw [hvf _ (hregst _ (by simp [zeroSlot])), huf _ (hf _) (hregbt _ (by simp [zeroSlot]))]
  have hjfit : Fits w j := (hub.1 ctr).of_le (by omega)
  let t := v.set one 1
  let y' := t.set ctr j
  have ht : ExecWithin (B := .exact) w (.op (.const one 1)) v t 1 :=
    .const ((hub.1 ctr).of_le (by omega))
  have htc : t.regs ctr = j + 1 := by wram_simp [t, hvctr]
  have htone : t.regs one = 1 := by simp [t, Data.set]
  have hdec : ExecWithin w (.op (.exactBin .sub ctr ctr one)) t y' 1 := by
    wram_exec [htc, htone]
  refine ⟨y', (hv.seq (ht.seq hdec)).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · refine Memory.State.ext hvm ?_
    change (t.set ctr j).regs frontier = u.regs frontier
    wram_simp [t]
    exact hvf frontier fun i => hf _
  · intro i
    change (t.set ctr j).regs (st i) = _
    wram_simp [t, st, one, ctr]
    exact hvs i
  · change y'.regs ctr = j
    wram_simp [y']
  · change y'.regs zero = y.regs zero
    wram_simp [y', t, hvzero]
  · intro i hif htmp
    wram_simp [y', t]
    rw [hvf _ fun _ => htmp _, huf _ hif fun _ => htmp _]

private def LoopInv (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → (δ × σ) → Memory.State → Prop)
    {n : ℕ} (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
    (tmp : Fin (l + (l + n + 3) + 1) → Fin r) (w : ℕ) (d₀ : δ) (x : Data r)
    (j : ℕ) (q : σ × Memory.State) (y : Data r) : Prop :=
  y.Bounded w ∧ memoryState frontier y = q.2 ∧
  (∀ i : Fin k, y.regs (src ⟨i.val, by omega⟩) = input d₀ i) ∧
  (∀ i, y.regs (tmp (stateSlot i)) = output q.1 i) ∧
  y.regs (tmp (counterSlot l n)) = j ∧ y.regs (tmp (zeroSlot l n)) = 0 ∧
  iterationSafe body safe w d₀ j q.1 q.2 ∧
  (Memory.spec w).ValidHistory q.2 ((Memory.spec w).clientHistory q.2 (iterate body d₀ j q.1)) ∧
  ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i

private theorem loopBody_tail_inv {input : δ ↪ (Fin k → ℕ)} {output : σ ↪ (Fin l → ℕ)}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {n : ℕ} {frontier : Fin r} {src : Fin (k + l + 1) → Fin r}
    {tmp : Fin (l + (l + n + 3) + 1) → Fin r}
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w j : ℕ} {d₀ : δ} {q : σ × Memory.State} {x y u : Data r}
    (hIy : LoopInv input output body safe frontier src tmp w d₀ x (j + 1) q y)
    (hub : u.Bounded w)
    (hum : memoryState frontier u = (Memory.spec w).clientState q.2 (body (d₀, q.1)))
    (huo : ∀ i : Fin l, u.regs (tmp (bodySlot (Fin.castAdd (n + 1) i))) =
      output ((Memory.spec w).clientResult q.2 (body (d₀, q.1))) i)
    (huf : ∀ i, i ≠ frontier → (∀ b, tmp (bodySlot b) ≠ i) → u.regs i = y.regs i) :
    ∃ y', ExecWithin (B := .exact) w
        (.seq (copyBank (fun i : Fin l => tmp (bodySlot (Fin.castAdd (n + 1) i)))
          (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) <|
          .seq (.op (.const (tmp (oneSlot l n)) 1))
            (.op (.exactBin .sub (tmp (counterSlot l n)) (tmp (counterSlot l n))
              (tmp (oneSlot l n))))) u y' (l + 3) ∧
      LoopInv input output body safe frontier src tmp w d₀ x j (iterationStep body d₀ q) y' := by
  obtain ⟨_, _, hye, _, hyc, hyz, hysafe, hyv, hyframe⟩ := hIy
  have hvparts := (validHistory_bind w (body (d₀, q.1)) (iterate body d₀ j) q.2).mp hyv
  rw [clientState_width] at hum
  simp only [clientResult_width] at huo
  obtain ⟨y', ht, htm, hts, htc, htz, htf⟩ :=
    loopBody_tail frontier tmp hi hf w j hub hyc huf
  exact ⟨y', ht, ht.bounded hub, htm.trans hum,
    fun i => (htf _ (hs _) fun _ => (hd _ _).symm).trans (hye i),
    fun i => (hts i).trans (huo i), htc, htz.trans hyz, hysafe.2,
    by simpa only [clientState_width w, clientResult_width w, iterationStep] using hvparts.2,
    fun i hif htmp => (htf i hif htmp).trans (hyframe i hif htmp)⟩

private theorem LoopInv.finish {input : δ ↪ (Fin k → ℕ)} {output : σ ↪ (Fin l → ℕ)}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {n : ℕ} {frontier : Fin r} {src : Fin (k + l + 1) → Fin r}
    {tmp : Fin (l + (l + n + 3) + 1) → Fin r} {w fuel : ℕ} {d₀ : δ} {a₀ : σ}
    {s₀ : Memory.State} {x y : Data r}
    (hIy : LoopInv input output body safe frontier src tmp w d₀ x 0
      ((iterationStep body d₀)^[fuel] (a₀, s₀)) y) :
    memoryState frontier y = (Memory.spec w).clientState s₀ (iterate body d₀ fuel a₀) ∧
      (∀ i : Fin l, y.regs (tmp (stateSlot i)) =
        output ((Memory.spec w).clientResult s₀ (iterate body d₀ fuel a₀)) i) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  rw [← iterate_result_state body d₀ fuel a₀ s₀] at hIy
  obtain ⟨_, hym, _, hys, _, _, _, _, hyf⟩ := hIy
  exact ⟨hym.trans (clientState_width w _ _).symm,
    fun i => (hys i).trans (congrArg (output · i) (clientResult_width w _ _).symm), hyf⟩

namespace Realizes

/-- The existing loop emitter retains the complete realization postcondition while paying
body charges and state/control overhead separately. This bounds that supplied emitter, not a
classically reselected implementation. -/
theorem Witness.loopEmit_spec (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Witness .exact body (appendWords input output) output safe work) :
    ∀ {r : ℕ} (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
      (tmp : Fin (l + (l + h.scratchSize + 3) + 1) → Fin r),
      Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
      (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
      ¬(loopEmit h.code frontier src tmp).ReadsWidth ∧
      ∀ (w : ℕ) (d : (δ × σ) × ℕ) (x : Data r), x.Bounded w →
        x.regs ∘ src = (((appendWords input output).prodMap
            (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) d →
        iterationSafe body safe w d.1.1 d.2 d.1.2 (memoryState frontier x) →
        (Memory.spec w).ValidHistory (memoryState frontier x)
          ((Memory.spec w).clientHistory (memoryState frontier x)
            (iterate body d.1.1 d.2 d.1.2)) →
        ∃ y, ExecWithin w (loopEmit h.code frontier src tmp) x y
            (h.factor * (memoryCost (iterate body d.1.1 d.2 d.1.2) (memoryState frontier x) +
              iterationWork body work d.1.1 d.2 d.1.2 (memoryState frontier x)) +
                (l + 5) * (d.2 + 1)) ∧
          memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x)
            (iterate body d.1.1 d.2 d.1.2) ∧
          (∀ i : Fin l, y.regs (tmp (Fin.castAdd ((l + h.scratchSize + 3) + 1) i)) =
            output ((Memory.spec w).clientResult (memoryState frontier x)
              (iterate body d.1.1 d.2 d.1.2)) i) ∧
          ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := loopEmit_instantiate h.code h.code_spec hi hd hf hs
  refine ⟨hnw, ?_⟩
  intro w ⟨⟨d₀, a₀⟩, fuel⟩ x hx hin hsafe hv
  let s₀ := memoryState frontier x
  obtain ⟨x₁, x₂, z, h₁, h₂, h₃, hzb, hzm, hze, hzs, hzc, hzz, hzf⟩ :=
    loopEmit_entry input output hi hd hf hx hin
  let I := LoopInv input output body safe frontier src tmp w d₀ x
  have hIz : I fuel (a₀, s₀) z := ⟨hzb, hzm, hze, hzs, hzc, hzz, hsafe, hv, hzf⟩
  have hbody : ∀ j q y, I (j + 1) q y →
      (Cond.lt (tmp (zeroSlot l h.scratchSize)) (tmp (counterSlot l h.scratchSize))).Holds y ∧ ∃ y',
        ExecWithin w (loopBody h.code frontier src tmp) y y'
          (h.factor * (memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2 + 1) + (l + 3)) ∧
        I j (iterationStep body d₀ q) y' := by
    intro j q y hIy
    have ⟨hyb, hym, hye, hys, hyc, hyz, hysafe, hyv, _⟩ := hIy
    refine ⟨by simp [Cond.Holds, hyz, hyc], ?_⟩
    have hvparts := (validHistory_bind w (body (d₀, q.1)) (iterate body d₀ j) q.2).mp hyv
    obtain ⟨u, hu, hum, huo, huf⟩ := hrun w (d₀, q.1) y hyb
      (regs_comp_append_eq_appendWords input output hye hys)
      (hym ▸ hysafe.1) (hym ▸ hvparts.1)
    rw [hym] at hu hum huo
    obtain ⟨y', ht, hIy'⟩ := loopBody_tail_inv hi hd hf hs hIy (hu.bounded hyb) hum huo huf
    exact ⟨y', (hu.seq ht).mono (by omega), hIy'⟩
  obtain ⟨y, hy, hIy⟩ := ExecWithin.loop_invariant_state_additive I (iterationStep body d₀)
    (fun q => memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2)
    (fun _ _ hI => by simp [Cond.Holds, hI.2.2.2.2.1, hI.2.2.2.2.2.1]) hbody hIz
  have hsumC := congrArg (h.factor * ·) (iterationSum_eq body work d₀ fuel a₀ s₀)
  obtain ⟨hym, hys, hyf⟩ := hIy.finish
  exact ⟨y, (h₁.seq (h₂.seq (h₃.seq hy))).mono (by nlinarith [hsumC]), hym, hys, hyf⟩

/-- Retain the supplied body and the existing loop emitter as data. Its original coarse
realization contract follows from the sharper same-emitter `loopEmit_spec`. -/
def Witness.iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Witness .exact body
      (appendWords input output) output safe work) :
    Witness .exact (fun ((d, a), fuel) => iterate body d fuel a)
      (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s)
      (fun ((d, a), fuel) s => iterationWork body work d fuel a s) where
  scratchSize := l + h.scratchSize + 3
  factor := h.factor + 2 * l + 8
  code := loopEmit h.code
  code_spec := by
    intro r frontier src tmp hi hd hf hs
    obtain ⟨hnw, hrun⟩ := h.loopEmit_spec input output frontier src tmp hi hd hf hs
    refine ⟨hnw, ?_⟩
    intro w d x hx hin hsafe hv
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv
    refine ⟨y, hy.mono ?_, hm, hout, hframe⟩
    have hcount : d.2 ≤ memoryCost (iterate body d.1.1 d.2 d.1.2) (memoryState frontier x) +
        iterationWork body work d.1.1 d.2 d.1.2 (memoryState frontier x) := by
      have := iterationSum_eq body work d.1.1 d.2 d.1.2 (memoryState frontier x); omega
    have hscaled := Nat.mul_le_mul_left (l + 5) (Nat.add_le_add_right hcount 1)
    nlinarith [hscaled]

/-- The existential runtime-loop realization erases the retained supplied emitter. -/
theorem iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Realizes .exact body
      (appendWords input output) output safe work) :
    Realizes .exact (fun ((d, a), fuel) => iterate body d fuel a)
      (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s)
      (fun ((d, a), fuel) s => iterationWork body work d fuel a s) :=
  (Witness.iterateRuntime input output (Witness.ofRealizes h)).toRealizes

end Realizes

namespace RealizesBounded

private theorem lift_regOnly {L w T : ℕ} {c : Code B r} {x y : Data r}
    (h : ExecWithin w c x y T) (hc : IsRegOnlyCode c) : ExecBounded w L c x y T :=
  .of_execWithin_regOnly hc h

/-- Frontier-bounded realization of runtime-bounded `iterate`. -/
theorem iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : RealizesBounded .exact body (appendWords input output) output safe work) :
    RealizesBounded .exact (fun ((d, a), fuel) => iterate body d fuel a)
      (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s)
      (fun ((d, a), fuel) s => iterationWork body work d fuel a s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨l + n + 3, C + 2 * l + 8, loopEmit emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := loopEmit_instantiate emit he hi hd hf hs
  refine ⟨hnw, ?_⟩
  rintro w ⟨⟨d₀, a₀⟩, fuel⟩ x hx hin hsafe hv
  let s₀ := memoryState frontier x
  let L_end := ((Memory.spec 0).clientState s₀ (iterate body d₀ fuel a₀)).frontier
  obtain ⟨x₁, x₂, z, h₁, h₂, h₃, hzb, hzm, hze, hzs, hzc, hzz, hzf⟩ :=
    loopEmit_entry input output hi hd hf hx hin
  let I : ℕ → (σ × Memory.State) → Data r → Prop := fun j q y =>
    LoopInv input output body safe frontier src tmp w d₀ x j q y ∧
      ((Memory.spec 0).clientState q.2 (iterate body d₀ j q.1)).frontier ≤ L_end
  have hIz : I fuel (a₀, s₀) z :=
    ⟨⟨hzb, hzm, hze, hzs, hzc, hzz, hsafe, hv, hzf⟩, le_rfl⟩
  have hbody : ∀ j q y, I (j + 1) q y →
      (Cond.lt (tmp (zeroSlot l n)) (tmp (counterSlot l n))).Holds y ∧ ∃ y',
        ExecBounded w L_end (loopBody emit frontier src tmp) y y'
          (C * (memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2 + 1) + (l + 3)) ∧
        I j (iterationStep body d₀ q) y' := by
    rintro j q y ⟨hIy, hL⟩
    have ⟨hyb, hym, hye, hys, hyc, hyz, hysafe, hyv, _⟩ := hIy
    refine ⟨by simp [Cond.Holds, hyz, hyc], ?_⟩
    have hvparts := (validHistory_bind w (body (d₀, q.1)) (iterate body d₀ j) q.2).mp hyv
    obtain ⟨u, hu, hum, huo, huf⟩ := hrun w (d₀, q.1) y hyb
      (regs_comp_append_eq_appendWords input output hye hys)
      (hym ▸ hysafe.1) (hym ▸ hvparts.1)
    rw [hym] at hu hum huo
    have hL' : ((Memory.spec 0).clientState (iterationStep body d₀ q).2
        (iterate body d₀ j (iterationStep body d₀ q).1)).frontier ≤ L_end := by
      simpa only [iterationStep, iterate, StateTransitionSpec.clientState,
        StateTransitionSpec.clientResult, ← PFunctor.FreeM.bind_eq_bind,
        StateTransitionSpec.runClient_bind] using hL
    have hu_le : u.regs frontier ≤ L_end :=
      (congrArg Memory.State.frontier (hum.trans (clientState_width w _ _))).trans_le
        ((Memory.frontier_le_clientState (w := 0) _ _).trans hL')
    obtain ⟨y', ht, hIy'⟩ := loopBody_tail_inv hi hd hf hs hIy (hu.bounded hyb) hum huo huf
    have htb := lift_regOnly (L := L_end) ht ⟨copyBank_isRegOnlyCode _ _ _, trivial, trivial⟩
    exact ⟨y', ((hu.mono_bound hu_le).seq htb).mono (by omega), hIy', hL'⟩
  obtain ⟨y, hy, hIy, _⟩ := ExecBounded.loop_invariant_state_additive I (iterationStep body d₀)
    (fun q => memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2)
    (fun _ _ hI => by simp [Cond.Holds, hI.1.2.2.2.2.1, hI.1.2.2.2.2.2.1]) hbody hIz
  obtain ⟨hym, hys, hyf⟩ := hIy.finish
  have hy_fr : y.regs frontier = L_end :=
    congrArg Memory.State.frontier (hym.trans (clientState_width w _ _))
  have hwhole := (lift_regOnly h₁ (copyBank_isRegOnlyCode _ _ _)).seq
    ((lift_regOnly h₂ trivial).seq ((lift_regOnly h₃ trivial).seq hy))
  rw [← hy_fr] at hwhole
  have hsum := iterationSum_eq body work d₀ fuel a₀ s₀
  have hscaled := Nat.mul_le_mul_left (l + 5)
    (by omega : fuel + 1 ≤ memoryCost (iterate body d₀ fuel a₀) s₀ +
      iterationWork body work d₀ fuel a₀ s₀ + 1)
  refine ⟨y, hwhole.mono ?_, hym, hys, hyf⟩
  change _ ≤ (C + 2 * l + 8) *
    (memoryCost (iterate body d₀ fuel a₀) s₀ + iterationWork body work d₀ fuel a₀ s₀ + 1)
  nlinarith [congrArg (C * ·) hsum, hscaled]

end RealizesBounded
end Cslib.WordRAM.Realization
