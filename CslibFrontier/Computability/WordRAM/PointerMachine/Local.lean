/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Randomized

/-!
# Local-address RAM simulation

A finite RAM interval has address registers separate from scalar registers. Each cell holds a
scalar and a reference. The only address arithmetic is successor and predecessor, with a
distinguished null reference for a move outside the interval.

The pointer representation has one record per cell, with immutable predecessor and successor
links. The representation is supplied at entry. Each RAM instruction translates to one
pointer instruction, and structured executions preserve instruction counts.

Schönhage describes the real-time equivalence of storage modification machines and successor
RAMs [Schonhage1980], abstract. The compiler here goes from the typed local-address RAM to the
pointer machine.

## Main definitions

* `Data`, `Direction`, `Op`, `Test`, `instructionSet`: the typed local-address RAM.
* `layout`, `encode`, `compile`: its linked representation and compiler.
* `evalRand`: the interpretation with randomized scalar operations.

## Main results

* `exec_compile`: exact simulation of structured executions.
* `executes_compile`: the corresponding flat pointer-machine program, including its final halt.
* `execRand_compile`: exact joint distribution of output states and instruction counts for
  structured runs with common probabilistic scalar primitives.
* `runRand_compile`: output distribution of the assembled randomized pointer-machine program.
-/

public section

namespace Cslib.WordRAM.Local

open Cslib PointerMachine

/-- A local-address RAM with `n` cells, `p` address registers and `d` scalar registers. -/
structure Data (M : Model) (n p d : ℕ) where
  /-- Address registers. -/
  addr : Fin p → Option (Fin n)
  /-- Scalar registers. -/
  scalars : Fin d → M.Value
  /-- Data stored at each RAM address. -/
  values : Fin n → M.Value
  /-- References stored at each RAM address. -/
  refs : Fin n → Option (Fin n)

variable {M : Model} {n p d : ℕ}

/-- A local address move. -/
inductive Direction where
  | next
  | prev

/-- Move within the interval, returning null at its endpoints. -/
@[expose] def Direction.move : Direction → Fin n → Option (Fin n)
  | .next, a => if h : a.val + 1 < n then some ⟨a.val + 1, h⟩ else none
  | .prev, a => if a.val = 0 then none else some ⟨a.val - 1, by omega⟩

/-- The operations of the local-address RAM. -/
inductive Op (M : Model) (p d : ℕ) where
  | null (dst : Fin p)
  | copyAddr (dst src : Fin p)
  | move (dir : Direction) (dst src : Fin p)
  | copyData (dst src : Fin d)
  | scalar (o : M.Op) (dst a b : Fin d)
  | loadData (dst : Fin d) (src : Fin p)
  | storeData (dst : Fin p) (src : Fin d)
  | loadAddr (dst src : Fin p)
  | storeAddr (dst src : Fin p)

/-- Operations through null leave the state unchanged. -/
@[expose] def Op.eval (x : Data M n p d) : Op M p d → Data M n p d
  | .null dst => { x with addr := Function.update x.addr dst none }
  | .copyAddr dst src => { x with addr := Function.update x.addr dst (x.addr src) }
  | .move dir dst src => (x.addr src).elim x fun a =>
      { x with addr := Function.update x.addr dst (dir.move a) }
  | .copyData dst src => { x with scalars := Function.update x.scalars dst (x.scalars src) }
  | .scalar o dst a b =>
      { x with scalars := Function.update x.scalars dst (M.evalOp o (x.scalars a) (x.scalars b)) }
  | .loadData dst src => (x.addr src).elim x fun a =>
      { x with scalars := Function.update x.scalars dst (x.values a) }
  | .storeData dst src => (x.addr dst).elim x fun a =>
      { x with values := Function.update x.values a (x.scalars src) }
  | .loadAddr dst src => (x.addr src).elim x fun a =>
      { x with addr := Function.update x.addr dst (x.refs a) }
  | .storeAddr dst src => (x.addr dst).elim x fun a =>
      { x with refs := Function.update x.refs a (x.addr src) }

/-- The local-address RAM can test reference equality and compare scalar data. -/
inductive Test (M : Model) (p d : ℕ) where
  | addrEq (a b : Fin p)
  | scalar (t : M.Test) (a b : Fin d)

/-- Structured instruction semantics for the local-address RAM. -/
@[expose, reducible] def instructionSet (M : Model) (n p d : ℕ) : Program.InstructionSet where
  Data := Data M n p d
  Op := Op M p d
  Test := Test M p d
  eval o x := some (o.eval x)
  Holds
    | .addrEq a b, x => x.addr a = x.addr b
    | .scalar t a b, x => M.evalTest t (x.scalars a) (x.scalars b) = true

instance (t : Test M p d) (x : Data M n p d) :
    Decidable ((instructionSet M n p d).Holds t x) := by
  cases t with
  | addrEq a b => exact inferInstanceAs (Decidable (x.addr a = x.addr b))
  | scalar t a b =>
    exact inferInstanceAs (Decidable (M.evalTest t (x.scalars a) (x.scalars b) = true))

/-- Record fields for the reference, successor and predecessor, and one scalar payload. -/
@[expose, reducible] def layout (p d : ℕ) : Layout := ⟨p, d, 3, 1⟩

private def addrCode (a : Option (Fin n)) : Pointer := a.map Fin.val

private def cell (x : Data M n p d) (a : Fin n) : Record M (layout p d) :=
  ⟨fun f => if f = 0 then addrCode (x.refs a) else if f = 1 then
      addrCode (Direction.next.move a) else addrCode (Direction.prev.move a),
    fun _ => x.values a⟩

/-- Encode an interval as a doubly linked chain of records in address order. -/
def encode (x : Data M n p d) : State M (layout p d) :=
  ⟨0, addrCode ∘ x.addr, x.scalars, List.ofFn (cell x)⟩

/-- Encoded states start at label zero. -/
@[simp] theorem encode_pc (x : Data M n p d) : (encode x).pc = 0 := by simp [encode]

/-- Encoded pointer registers contain the corresponding cell indices. -/
theorem encode_ptr (x : Data M n p d) (r : Fin p) :
    (encode x).ptr r = (x.addr r).map Fin.val := by simp [encode, addrCode]

/-- The linked representation uses exactly one record per source cell. -/
@[simp] theorem encode_heap_length (x : Data M n p d) : (encode x).heap.length = n := by
  simp [encode]

/-- Reading a payload from the encoded heap gives its source cell value. -/
theorem encode_heap_getElem_data (x : Data M n p d) (a : Fin n)
    (h : a.val < (encode x).heap.length) :
    ((encode x).heap[a.val]'h).data 0 = x.values a := by
  simp [encode, List.getElem_ofFn, cell]

private theorem addrCode_bound {a : Option (Fin n)} {i : ℕ} (h : addrCode a = some i) :
    i < n := by
  cases a with
  | none => simp [addrCode] at h
  | some a =>
    have he : a.val = i := by simpa [addrCode] using h
    exact he ▸ a.isLt

/-- All references in the initial linked representation designate allocated records or null. -/
theorem encode_valid (x : Data M n p d) : (encode x).Valid := by
  rw [State.Valid, encode_heap_length]
  refine ⟨fun _ _ h => addrCode_bound h, ?_⟩
  intro r hr f i h
  change r ∈ List.ofFn (cell x) at hr
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hr
  change (if f = 0 then addrCode (x.refs a) else if f = 1 then
    addrCode (Direction.next.move a) else addrCode (Direction.prev.move a)) = some i at h
  split at h
  · exact addrCode_bound h
  · split at h <;> exact addrCode_bound h

private theorem deref_encode (x : Data M n p d) (r : Fin p) :
    (encode x).deref r = (x.addr r).map (cell x) := by
  cases h : x.addr r with
  | none => simp [encode, State.deref, addrCode, h]
  | some a => simp [encode, State.deref, addrCode, h, List.getElem?_ofFn, a.isLt]

private def lowerOp : Op M p d → PointerMachine.Op M (layout p d)
  | .null dst => .null dst
  | .copyAddr dst src => .movePtr dst src
  | .move .next dst src => .loadPtr dst 1 src
  | .move .prev dst src => .loadPtr dst 2 src
  | .copyData dst src => .moveData dst src
  | .scalar o dst a b => .op o dst a b
  | .loadData dst src => .loadData dst 0 src
  | .storeData dst src => .storeData 0 dst src
  | .loadAddr dst src => .loadPtr dst 0 src
  | .storeAddr dst src => .storePtr 0 dst src

private def lowerTest : Test M p d → PointerMachine.Test M (layout p d)
  | .addrEq a b => .ptrEq a b
  | .scalar t a b => .data t a b

/-- Compile local-address programs, preserving their control flow. -/
def compile : Program.Code (Op M p d) (Test M p d) → Code M (layout p d)
  | .skip => .skip
  | .op o => .op (lowerOp o)
  | .seq a b => .seq (compile a) (compile b)
  | .branch t a b => .branch (lowerTest t) (compile a) (compile b)
  | .loop t b => .loop (lowerTest t) (compile b)
  | .loopUntil t b => .loopUntil (lowerTest t) (compile b)

/-- Compilation preserves the number of assembled instructions. -/
@[simp] theorem size_compile (c : Program.Code (Op M p d) (Test M p d)) :
    (compile c).size = c.size := by
  induction c <;> simp [compile, Program.Code.size, *]

private theorem test_correct (t : Test M p d) (x : Data M n p d) :
    (lowerTest t).Holds (encode x) ↔ (instructionSet M n p d).Holds t x := by
  cases t with
  | scalar => rfl
  | addrEq a b =>
    change addrCode (x.addr a) = addrCode (x.addr b) ↔ x.addr a = x.addr b
    cases x.addr a <;> cases x.addr b <;> simp [addrCode, Fin.ext_iff]

private theorem encode_updateAddr (x : Data M n p d) (r : Fin p) (a : Option (Fin n)) :
    encode { x with addr := Function.update x.addr r a } = (encode x).setPtr r (addrCode a) := by
  unfold encode State.setPtr
  congr 1
  funext j
  by_cases h : j = r <;> simp [h, Function.comp_apply]

private theorem ofFn_modify_eq {α : Type*} {f f' : Fin n → α}
    (a : Fin n) (g : α → α) (hit : g (f a) = f' a) (miss : ∀ i ≠ a, f i = f' i) :
    (List.ofFn f).modify a.val g = List.ofFn f' := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_modify, List.getElem_ofFn]
    split
    · rename_i he
      subst i
      simpa only [List.getElem_ofFn] using hit
    · rename_i he
      rw [List.getElem_ofFn]
      exact miss _ (fun h => he (congrArg Fin.val h).symm)

private theorem op_correct (o : Op M p d) (x : Data M n p d) :
    (lowerOp o).effect (encode x) = encode (o.eval x) := by
  cases o with
  | null r => exact (encode_updateAddr x r none).symm
  | copyAddr r s => exact (encode_updateAddr x r (x.addr s)).symm
  | copyData => rfl
  | scalar => rfl
  | move dir r s =>
    cases dir <;> cases h : x.addr s <;>
      simp [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
        deref_encode, Op.eval, h, cell, encode_updateAddr]
  | loadAddr r s =>
    cases h : x.addr s <;>
      simp [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
        deref_encode, Op.eval, h, cell, encode_updateAddr]
  | loadData r s =>
    simp only [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
      deref_encode, Op.eval]
    cases x.addr s <;> rfl
  | storeAddr r s =>
    cases h : x.addr r with
    | none => simp [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
        State.modify, encode, addrCode, Op.eval, h]
    | some a =>
      simp only [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
        State.modify, encode, addrCode, Function.comp_apply, Op.eval, h, Option.elim, Option.map]
      congr 1
      apply ofFn_modify_eq a
      · congr 1
        funext f
        by_cases hf : f = 0 <;> simp [cell, hf, addrCode, Option.map]
      · intro i hi
        simp [cell, Function.update_of_ne hi]
  | storeData r s =>
    cases h : x.addr r with
    | none => simp [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
        State.modify, encode, addrCode, Op.eval, h]
    | some a =>
      simp only [lowerOp, PointerMachine.Op.effect, PointerMachine.Op.instr, Instr.effect,
        State.modify, encode, addrCode, Function.comp_apply, Op.eval, h, Option.elim, Option.map]
      congr 1
      apply ofFn_modify_eq a
      · congr 1
        funext f
        have : f = 0 := Subsingleton.elim _ _
        simp [cell, this]
      · intro i hi
        simp [cell, Function.update_of_ne hi]

/-- Every source structured run executes on the linked representation at the same cost. -/
theorem exec_compile {c : Program.Code (Op M p d) (Test M p d)} {x y : Data M n p d}
    {t : ℕ} (h : Program.Exec (instructionSet M n p d) c x y t) :
    PointerMachine.Exec (compile c) (encode x) (encode y) t := by
  refine Program.Exec.rec (I := instructionSet M n p d)
    (motive := fun c x y t _ => PointerMachine.Exec (compile c) (encode x) (encode y) t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x
    exact .skip
  · intro o x y he
    cases Option.some.inj he
    exact Program.Exec.op (congrArg some (op_correct _ _))
  · intro _ _ _ _ _ _ _ _ _ ih₁ ih₂
    exact .seq ih₁ ih₂
  · intro _ _ _ _ _ _ ht _ ih
    exact .branch_pos ((test_correct _ _).2 ht) ih
  · intro _ _ _ _ _ _ ht _ ih
    exact .branch_neg (fun h => ht ((test_correct _ _).1 h)) ih
  · intro _ _ _ ht
    exact .loop_exit (fun h => ht ((test_correct _ _).1 h))
  · intro _ _ _ _ _ _ _ ht _ _ ih₁ ih₂
    exact .loop_iter ((test_correct _ _).2 ht) ih₁ ih₂
  · intro _ _ _ ht
    exact .loopUntil_exit ((test_correct _ _).2 ht)
  · intro _ _ _ _ _ _ _ ht _ _ ih₁ ih₂
    exact .loopUntil_iter (fun h => ht ((test_correct _ _).1 h)) ih₁ ih₂

/-- The encoded scalar registers retain their source values. -/
@[simp] theorem encode_data (x : Data M n p d) : (encode x).data = x.scalars := by simp [encode]

/-- Assembling the simulation adds only the final halt to the source instruction count. -/
theorem executes_compile {c : Program.Code (Op M p d) (Test M p d)} {x y : Data M n p d}
    {t : ℕ} (h : Program.Exec (instructionSet M n p d) c x y t) :
    Executes (compile c).program (encode x)
      { encode y with pc := (compile c).size } (t + 1) :=
  (exec_compile h).executes rfl

/-! ## Probabilistic scalar primitives -/

private theorem addrCode_injective : Function.Injective (addrCode (n := n)) :=
  Option.map_injective Fin.val_injective

private theorem encode_injective :
    Function.Injective (encode (M := M) (n := n) (p := p) (d := d)) :=
  fun x y h => by
    have ha : x.addr = y.addr := funext fun r =>
      addrCode_injective (congrArg (fun s => s.ptr r) h)
    have hs : x.scalars = y.scalars := congrArg State.data h
    have hc : cell x = cell y := List.ofFn_injective (congrArg State.heap h)
    have hv : x.values = y.values :=
      funext fun a => congrArg (fun f => (f a).data 0) hc
    have hr : x.refs = y.refs := funext fun a => addrCode_injective (by
      simpa [cell] using congrArg (fun f => (f a).ptr 0) hc)
    cases x
    cases y
    congr

/-- Interpret scalar operations using probabilistic kernels. Address operations and memory
access keep their deterministic meanings. Each operation costs one instruction. -/
@[expose] def evalRand (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    (o : Op M p d) (x : Data M n p d) : Option (ProbComp (Data M n p d)) :=
  some (match o with
    | .scalar op dst a b => (fun v => { x with scalars := Function.update x.scalars dst v })
        <$> kernel op (x.scalars a) (x.scalars b)
    | _ => pure (o.eval x))

private theorem eval_rand_correct (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    (o : Op M p d) (x : Data M n p d) :
    PointerMachine.Op.evalRand kernel (lowerOp o) (encode x) =
      (evalRand kernel o x).map (encode <$> ·) := by
  cases o with
  | scalar =>
    simp only [evalRand, PointerMachine.Op.evalRand, lowerOp, Option.map_some, Functor.map_map]
    rfl
  | move dir =>
    cases dir
    · simpa [evalRand, PointerMachine.Op.evalRand, lowerOp] using op_correct (.move .next _ _) x
    · simpa [evalRand, PointerMachine.Op.evalRand, lowerOp] using op_correct (.move .prev _ _) x
  | _ => simp [evalRand, PointerMachine.Op.evalRand, lowerOp, ← op_correct]

private def encodeResult (z : Data M n p d × ℕ) : State M (layout p d) × ℕ :=
  (encode z.1, z.2)

/-- With matching scalar kernels, compilation preserves the entire distribution of results and
instruction counts of each terminating structured execution. -/
theorem execRand_compile (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    {c : Program.Code (Op M p d) (Test M p d)} {x : Data M n p d}
    {m : ProbComp (Data M n p d × ℕ)}
    (h : Program.ExecRand (I := instructionSet M n p d) (evalRand kernel) c x m) :
    Program.ExecRand (I := PointerMachine.instructionSet M (layout p d))
      (PointerMachine.Op.evalRand kernel) (compile c) (encode x)
      ((fun z => (encode z.1, z.2)) <$> m) := by
  let lift (f : Data M n p d → ProbComp (Data M n p d × ℕ)) :=
    Function.extend encode (fun x => encodeResult <$> f x)
      (fun x => pure (x, 0))
  have hlift (f) (x : Data M n p d) : lift f (encode x) = (encodeResult <$> f x) :=
    encode_injective.extend_apply _ _ _
  have hsupport {m : ProbComp (Data M n p d × ℕ)} {z}
      (hz : z ∈ (encodeResult <$> m).support) : ∃ o ∈ m.support, encodeResult o = z :=
    OracleComp.mem_supportWith_map_iff.mp hz
  have chain (a : ProbComp (Data M n p d × ℕ)) (b : Data M n p d → ProbComp (Data M n p d × ℕ))
      (extra : ℕ) :
      (do
        let z₁ ← encodeResult <$> a
        let z₂ ← lift b z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + extra)) =
      (encodeResult <$> do
        let z₁ ← a
        let z₂ ← b z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + extra)) := by
    simp [bind_map_left, map_bind, encodeResult, hlift]
  refine Program.ExecRand.rec
    (motive := fun c x m _ => Program.ExecRand (I := PointerMachine.instructionSet M (layout p d))
      (PointerMachine.Op.evalRand kernel) (compile c) (encode x) (encodeResult <$> m))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x
    simpa [compile, encodeResult] using
      (Program.ExecRand.skip (I := PointerMachine.instructionSet M (layout p d))
        (evalRand := PointerMachine.Op.evalRand kernel) (x := encode x))
  · intro o x m he
    have he' : PointerMachine.Op.evalRand kernel (lowerOp o) (encode x) = some (encode <$> m) := by
      rw [eval_rand_correct, he, Option.map_some]
    simpa [compile, Functor.map_map, encodeResult] using
      Program.ExecRand.op (I := PointerMachine.instructionSet M (layout p d)) he'
  · intro _ c₂ _ a b _ _ ih₁ ih₂
    have h₂ : ∀ z ∈ (encodeResult <$> a).support,
        Program.ExecRand (I := PointerMachine.instructionSet M (layout p d))
          (PointerMachine.Op.evalRand kernel) (compile c₂) z.1 (lift b z.1) := by
      intro z hz
      obtain ⟨o, ho, rfl⟩ := hsupport hz
      simpa only [encodeResult, hlift] using ih₂ o ho
    have hc := chain a b 0
    simp only [Nat.add_zero] at hc
    rw [← hc]
    exact Program.ExecRand.seq ih₁ h₂
  · intro _ _ _ _ _ ht _ ih
    simpa [compile, Functor.map_map, encodeResult] using
      Program.ExecRand.branch_pos ((test_correct _ _).2 ht) ih
  · intro _ _ _ _ _ ht _ ih
    simpa [compile, Functor.map_map, encodeResult] using
      Program.ExecRand.branch_neg (fun h => ht ((test_correct _ _).1 h)) ih
  · intro t body x ht
    simpa [compile, encodeResult] using
      (Program.ExecRand.loop_exit (I := PointerMachine.instructionSet M (layout p d))
        (evalRand := PointerMachine.Op.evalRand kernel) (body := compile body)
        (fun h => ht ((test_correct t x).1 h)))
  · intro t body x a b ht _ _ ih₁ ih₂
    have h₂ : ∀ z ∈ (encodeResult <$> a).support,
        Program.ExecRand (I := PointerMachine.instructionSet M (layout p d))
          (PointerMachine.Op.evalRand kernel) (compile (.loop t body)) z.1 (lift b z.1) := by
      intro z hz
      obtain ⟨o, ho, rfl⟩ := hsupport hz
      simpa only [encodeResult, hlift] using ih₂ o ho
    simpa only [compile, ← chain a b 2] using
      Program.ExecRand.loop_iter ((test_correct t x).2 ht) ih₁ h₂
  · intro t body x ht
    simpa [compile, encodeResult] using
      (Program.ExecRand.loopUntil_exit (I := PointerMachine.instructionSet M (layout p d))
        (evalRand := PointerMachine.Op.evalRand kernel) (body := compile body)
        ((test_correct t x).2 ht))
  · intro t body x a b ht _ _ ih₁ ih₂
    have h₂ : ∀ z ∈ (encodeResult <$> a).support,
        Program.ExecRand (I := PointerMachine.instructionSet M (layout p d))
          (PointerMachine.Op.evalRand kernel) (compile (.loopUntil t body)) z.1 (lift b z.1) := by
      intro z hz
      obtain ⟨o, ho, rfl⟩ := hsupport hz
      simpa only [encodeResult, hlift] using ih₂ o ho
    simpa only [compile, ← chain a b 2] using
      Program.ExecRand.loopUntil_iter (fun h => ht ((test_correct t x).1 h)) ih₁ h₂

/-- A budget covering every structured run reaches the compiled halt with the encoded output
distribution. -/
theorem runRand_compile (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    {c : Program.Code (Op M p d) (Test M p d)} {x : Data M n p d}
    {m : ProbComp (Data M n p d × ℕ)} {T : ℕ}
    (h : Program.ExecRand (I := instructionSet M n p d) (evalRand kernel) c x m)
    (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    PointerMachine.runRand kernel (compile c).program T (encode x) =
      (fun z => { encode z.1 with pc := (compile c).size }) <$> m := by
  have hcost : ∀ z ∈ ((fun z => (encode z.1, z.2)) <$> m).support, z.2 ≤ T := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact hT a ha
  have hstart : { encode x with pc := 0 } = encode x := by unfold encode; rfl
  simpa only [Functor.map_map, hstart] using
    PointerMachine.runRand_program kernel (execRand_compile kernel h) hcost

end Cslib.WordRAM.Local
