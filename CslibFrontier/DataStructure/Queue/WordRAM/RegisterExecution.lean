/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterProgram

/-!
# Paid initialization and execution of the resident queue

The proof uses the shared Backend's public packing and live-execution facts. In particular,
the maintained count words are already present in native source registers, rather than being
reinstalled by the external controller. Operation code and packing are the globally fixed family
from `RegisterProgram`; the initializer remains parameterized by literal base and capacity.

## Main results

* `initialized_rep`: the six register writes establish the empty two-array representation.
* `initialize_queue`: arbitrary dirty bounded data admits paid constant-time initialization.
* `execute_enqueue`, `execute_dequeue`: the same native dispatcher implements both methods.
* `execute`, `certificate`: scaled native payment and the existing dynamic certificate.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM

open Cslib.WordRAM Cslib.WordRAM.Realization
open RegisterMetadata

private theorem src_injective : Function.Injective src := Backend.src_injective family false

private theorem result_injective : Function.Injective result := fun _ _ h => by
  simpa using Backend.tmp_injective family true h

private theorem src_ne_result (i : Fin 5) (j : Fin 4) : src i ≠ result j :=
  Backend.src_ne_tmp family false true i _

private theorem src_ne_frontier (i : Fin 5) : src i ≠ Backend.frontier family :=
  Backend.src_ne_frontier family false i

private theorem result_ne_frontier (i : Fin 4) : result i ≠ Backend.frontier family :=
  Backend.tmp_ne_frontier family true _

private theorem tag_ne_zero : tag ≠ zero := result_injective.ne (by decide)

private theorem prepare_frame (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers)
    (i : Fin registers) (ht : i ≠ tag) (ha : i ≠ src 4) :
    ((implementation w capacity).prepare o x).regs i = x.regs i := by
  apply DynamicProgram.prepare_regs_of_not_input
  simp [implementation, ht, ha]

private theorem prepare_src (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers)
    (i : Fin 5) :
    ((implementation w capacity).prepare o x).regs (src i) =
      if i = 4 then (match o with | .enqueue v => v | .dequeue => 0) else x.regs (src i) := by
  have ht : src i ≠ tag := src_ne_result i 0
  have hs : src i = src 4 ↔ i = 4 := src_injective.eq_iff
  cases o <;> simp [DynamicProgram.prepare, implementation, ht, hs]

private theorem prepare_tag (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers) :
    ((implementation w capacity).prepare o x).regs tag =
      match o with | .enqueue _ => 0 | .dequeue => 1 := by
  cases o <;> simp [DynamicProgram.prepare, implementation]

private theorem prepare_frontier (w capacity : ℕ) (o : Queue.QueueOp ℕ)
    (x : Data registers) :
    ((implementation w capacity).prepare o x).regs (Backend.frontier family) =
      x.regs (Backend.frontier family) :=
  prepare_frame _ _ _ _ _ (result_ne_frontier 0).symm (src_ne_frontier 4).symm

private theorem encoded_fits {w capacity : ℕ} (h1 : Fits w 1) (o : Queue.QueueOp ℕ)
    (hv : match o with | .enqueue v => Fits w v | .dequeue => True)
    (i : Fin registers) : Fits w ((implementation w capacity).encode o i) := by
  cases o <;> dsimp only [implementation] <;> split
  exacts [fits_zero w, hv, h1, fits_zero w]

private theorem prepare_bounded {w capacity : ℕ} (o : Queue.QueueOp ℕ)
    {x : Data registers} (hx : x.Bounded w) (h1 : Fits w 1)
    (hv : match o with | .enqueue v => Fits w v | .dequeue => True) :
    ((implementation w capacity).prepare o x).Bounded w :=
  DynamicProgram.prepare_bounded _ hx (fun i _ => encoded_fits h1 o hv i)

private noncomputable def staged (w capacity : ℕ) (o : Queue.QueueOp ℕ)
    (x : Data registers) : Data registers :=
  ((implementation w capacity).prepare o x).set zero 0

private theorem stage_exec (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers) :
    Exec (B := .standard) w (.op (.const zero 0)) ((implementation w capacity).prepare o x)
      (staged w capacity o x) 1 := Exec.const (fits_zero w)

private theorem staged_bounded {w capacity : ℕ} (o : Queue.QueueOp ℕ)
    {x : Data registers} (hx : x.Bounded w) (h1 : Fits w 1)
    (hv : match o with | .enqueue v => Fits w v | .dequeue => True) :
    (staged w capacity o x).Bounded w :=
  (stage_exec w capacity o x).bounded (prepare_bounded o hx h1 hv)

private theorem staged_input {w base capacity : ℕ} {front back : List ℕ} {x : Data registers}
    (hr : Rep w base capacity front back x) (o : Queue.QueueOp ℕ) :
    (staged w capacity o x).regs ∘ src =
      ![front.length, back.length, base, capacity,
        match o with | .enqueue v => v | .dequeue => 0] := by
  funext i
  change Function.update _ zero 0 (src i) = _
  rw [Function.update_of_ne (src_ne_result i 1), prepare_src]
  fin_cases i <;> simp [hr.frontLen_eq, hr.backLen_eq, hr.base_eq, hr.capacity_eq]

private theorem staged_memory (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers) :
    memoryState (Backend.frontier family) (staged w capacity o x) =
      memoryState (Backend.frontier family) x := by
  exact Memory.State.ext (DynamicProgram.prepare_mem (implementation w capacity) o x)
    ((Function.update_of_ne (result_ne_frontier 1).symm 0 _).trans
      (prepare_frontier w capacity o x))

private theorem staged_tag (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers) :
    (staged w capacity o x).regs tag =
      match o with | .enqueue _ => 0 | .dequeue => 1 := by
  exact (Function.update_of_ne tag_ne_zero 0 _).trans (prepare_tag w capacity o x)

private theorem staged_zero (w capacity : ℕ) (o : Queue.QueueOp ℕ) (x : Data registers) :
    (staged w capacity o x).regs zero = 0 := by
  simp only [staged, Data.set_regs, Function.update_self]

private noncomputable def committed (m : Counts) (x : Data registers) : Data registers :=
  (x.set (src 0) m.front).set (src 1) m.rear

private theorem commit_exec {w : ℕ} {x : Data registers} {m : Counts}
    (h0 : x.regs (result 0) = m.front) (h1 : x.regs (result 1) = m.rear) :
    Exec w commit x (committed m x) 2 := by
  have h0' : Exec (B := .standard) w (.op (.copy (src 0) (result 0))) x
      (x.set (src 0) m.front) 1 := by
    simpa only [h0] using (Exec.copy (B := .standard) (w := w)
      (x := x) (d := src 0) (s := result 0))
  have hr : (x.set (src 0) m.front).regs (result 1) = m.rear := by
    simpa only [Data.set_regs, Function.update_of_ne (src_ne_result 0 1).symm] using h1
  exact h0'.seq (by
    simpa only [hr] using (Exec.copy (B := .standard) (w := w)
      (x := x.set (src 0) m.front) (d := src 1) (s := result 1)))

private theorem committed_other (m : Counts) (x : Data registers) (i : Fin registers)
    (h0 : i ≠ src 0) (h1 : i ≠ src 1) : (committed m x).regs i = x.regs i := by
  simp only [committed, Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h0]

private theorem committed_counts (m : Counts) (x : Data registers) :
    (committed m x).regs (src 0) = m.front ∧ (committed m x).regs (src 1) = m.rear := by
  have hn : src 0 ≠ src 1 := src_injective.ne (by decide)
  simp [committed, Data.set, hn]

/-- Committing counts `⟨front.length, back.length⟩` over a backend result that kept `src 2`,
`src 3` and the frontier represents `front` and `back`. -/
private theorem committed_rep {w base capacity : ℕ} {front back : List ℕ} {b : Data registers}
    (hcb : (committed ⟨front.length, back.length⟩ b).Bounded w)
    (h2 : b.regs (src 2) = base) (h3 : b.regs (src 3) = capacity)
    (hf : b.regs (Backend.frontier family) = base + 2 * capacity)
    (hs : front.length + back.length ≤ capacity)
    (hfc : Block.HoldsList base front.reverse b.mem)
    (hbc : Block.HoldsList (base + capacity) back.reverse b.mem) :
    Rep w base capacity front back (committed ⟨front.length, back.length⟩ b) :=
  ⟨hcb,
    (committed_other _ b _ (src_injective.ne (by decide)) (src_injective.ne (by decide))).trans h2,
    (committed_other _ b _ (src_injective.ne (by decide)) (src_injective.ne (by decide))).trans h3,
    (committed_other _ b _ (src_ne_frontier 0).symm (src_ne_frontier 1).symm).trans hf,
    (committed_counts _ b).1, (committed_counts _ b).2, hs, hfc, hbc⟩

private theorem enqueue_result_eq (i : Fin 2) :
    Backend.tmp family false (Fin.castAdd ((family false).realizes.scratchSize + 1) i) =
      result (Fin.castAdd 2 i) := Backend.tmp_eq_of_val_eq family false true rfl

private theorem initialized_input (base capacity : ℕ) (x : Data registers) :
    (initialized base capacity x).regs ∘ src = ![0, 0, base, capacity, x.regs (src 4)] := by
  have hz (i : Fin 5) : src i ≠ zero := src_ne_result i 1
  have hf (i : Fin 5) : src i ≠ Backend.frontier family := src_ne_frontier i
  have hs (i j : Fin 5) : src i = src j ↔ i = j := src_injective.eq_iff
  funext i
  fin_cases i <;> simp [initialized, Data.set, hz, hf, hs]

private theorem initialized_frontier (base capacity : ℕ) (x : Data registers) :
    (initialized base capacity x).regs (Backend.frontier family) = base + 2 * capacity := by
  have hz : Backend.frontier family ≠ zero := (result_ne_frontier 1).symm
  have hs (i : Fin 5) : Backend.frontier family ≠ src i := (src_ne_frontier i).symm
  simp [initialized, Data.set, hz, hs]

/-- The actual six writes establish the empty representation under precisely the original
end-fit condition, with no assumption on initial registers or dirty memory. -/
theorem initialized_rep {w base capacity : ℕ} {x : Data registers} (hx : x.Bounded w)
    (hc : Fits w (base + 2 * capacity)) : Rep w base capacity [] []
      (initialized base capacity x) := by
  have hin := initialized_input base capacity x
  exact ⟨(initialize_exec hx hc).2.1, congrFun hin 2, congrFun hin 3,
    initialized_frontier base capacity x, congrFun hin 0, congrFun hin 1,
    Nat.zero_le _, Block.holdsList_nil _ _, Block.holdsList_nil _ _⟩

/-- Paid raw initialization establishes the existing FIFO meaning and preserves all memory.
The original small-width and capacity-zero cases are included; tag delivery later retains its
separate `Fits w 1` requirement. -/
theorem initialize_queue {w base capacity : ℕ} {x : Data registers} (hx : x.Bounded w)
    (hc : Fits w (base + 2 * capacity)) :
    ∃ ready, Exec w (initializeCode base capacity) x ready 6 ∧
      QueueRep w base capacity [] ready ∧ ready.mem = x.mem := by
  exact ⟨initialized base capacity x, (initialize_exec hx hc).1,
    ⟨[], [], rfl, initialized_rep hx hc⟩, rfl⟩

/-- The fixed dispatcher executes enqueue from resident metadata, pays the zero test and
two count copies, and includes the final call halt in its bound. The original two arrays are
the complete memory footprint. -/
theorem execute_enqueue {w base capacity v : ℕ} {front back : List ℕ} {x : Data registers}
    (h1 : Fits w 1) (hr : Rep w base capacity front back x)
    (hs : front.length + back.length < capacity) (hv : Fits w v) :
    ∃ y n, Exec w program ((implementation w capacity).prepare (.enqueue v) x) y n ∧
      n + 1 ≤ 2 * Backend.factor family + 5 ∧ Rep w base capacity front (v :: back) y ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  let d : Input := ![front.length, back.length, base, capacity, v]
  let z := staged w capacity (.enqueue v) x
  have hdom : enqueueDomain w d (memoryState (Backend.frontier family) x) :=
    ⟨hs, hr.frontier_eq.ge, hv⟩
  have hz : z.Bounded w := staged_bounded (.enqueue v) hr.bounded h1 hv
  have hin : z.regs ∘ Backend.src family false = (family false).input d :=
    staged_input hr (.enqueue v)
  have hdomz : enqueueDomain w d (memoryState (Backend.frontier family) z) := by
    rwa [staged_memory]
  obtain ⟨b, n, hb, hn, hm, ho, hbb, hframe⟩ := Backend.exists_exec_live family false d hz hin
    hdomz (valid_enqueue hdomz)
  rw [staged_memory] at hm
  have hn' : n ≤ 2 * Backend.factor family := by
    change n ≤ Backend.factor family * (memoryCost (enqueue d)
      (memoryState (Backend.frontier family) z) + 0 + 1) at hn
    simpa only [memoryCost_enqueue, Nat.add_zero, Nat.mul_comm] using hn
  let m : Counts := ⟨front.length, back.length + 1⟩
  have hcommit : Exec w commit b (committed m b) 2 := commit_exec
    ((congrArg b.regs (enqueue_result_eq 0)).symm.trans (ho 0))
    ((congrArg b.regs (enqueue_result_eq 1)).symm.trans (ho 1))
  have hcond : (Cond.eq tag zero).Holds z :=
    (staged_tag w capacity (.enqueue v) x).trans (staged_zero w capacity (.enqueue v) x).symm
  have he : Exec w program ((implementation w capacity).prepare (.enqueue v) x)
      (committed m b) (1 + (n + 1 + 2)) :=
    (stage_exec w capacity (.enqueue v) x).seq ((Exec.branch_pos hcond hb).seq hcommit)
  have hsrc (i : Fin 5) : b.regs (src i) = d i := by
    rw [hframe _ (src_ne_frontier i) (fun a => (Backend.src_ne_tmp family false false i a).symm)]
    exact congrFun hin i
  have hmemw : b.mem =
      ((Memory.spec w).clientState (memoryState (Backend.frontier family) x) (enqueue d)).mem :=
    congrArg Memory.State.mem hm
  have hmem : b.mem =
      ((Memory.spec 0).clientState (memoryState (Backend.frontier family) x) (enqueue d)).mem := by
    simpa only [clientState_width w] using hmemw
  have hcontents := enqueue_contents (d := d) front back
    (memoryState (Backend.frontier family) x) rfl rfl hs hr.front_contents hr.back_contents
  exact ⟨committed m b, 1 + (n + 1 + 2), he, by omega,
    committed_rep (hcommit.bounded hbb) (hsrc 2) (hsrc 3)
      ((congrArg Memory.State.frontier hm).trans hr.frontier_eq)
      (by simp only [List.length_cons]; omega) (hmem ▸ hcontents.2.1) (hmem ▸ hcontents.2.2),
    hmemw ▸ enqueue_modifies hdom⟩

/-- The negative native branch performs the source transfer/pop, commits both returned
counts, and decodes its faithful option result. The bound includes the negative branch's
two instructions and the call halt, without charging any hidden metadata installation. -/
theorem execute_dequeue {w base capacity : ℕ} {front back : List ℕ} {x : Data registers}
    (h1 : Fits w 1) (hr : Rep w base capacity front back x) :
    let p := pairStep ⟨front, back⟩ .dequeue
    ∃ y n, Exec w program ((implementation w capacity).prepare .dequeue x) y n ∧
      n + 1 ≤ Backend.factor family *
        (memoryCost (dequeue ![front.length, back.length, base, capacity, 0])
          (memoryState (Backend.frontier family) x) + 1) + 6 ∧
      Rep w base capacity p.1.front p.1.rear y ∧
      (implementation w capacity).decode .dequeue y.regs = some p.2 ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  let d : Input := ![front.length, back.length, base, capacity, 0]
  let p := pairStep ⟨front, back⟩ .dequeue
  let z := staged w capacity .dequeue x
  have hdom : transferDomain w d (memoryState (Backend.frontier family) x) :=
    ⟨hr.size_le, hr.frontier_eq.ge⟩
  have hw : Memory.WellFormed w (memoryState (Backend.frontier family) x) :=
    wellFormed_memoryState hr.bounded
  have hi := dequeue_invariant hw hdom
  have hcontents := dequeue_contents (d := d) front back
    (memoryState (Backend.frontier family) x) hw rfl rfl hr.size_le hr.frontier_eq.ge
    hr.front_contents hr.back_contents
  have hz : z.Bounded w := staged_bounded .dequeue hr.bounded h1 trivial
  have hin : z.regs ∘ Backend.src family true = (family true).input d := funext fun i =>
    (congrArg z.regs (Backend.src_eq_of_val_eq family true false rfl)).trans
      (congrFun (staged_input hr .dequeue) i)
  have hdomz : transferDomain w d (memoryState (Backend.frontier family) z) := by
    rwa [staged_memory]
  obtain ⟨b, n, hb, hn, hm, ho, hbb, hframe⟩ := Backend.exists_exec_live family true d hz hin
    hdomz (by rw [staged_memory]; exact hi.1)
  rw [staged_memory] at hm hn ho
  rw [clientResult_width w, hcontents.1] at ho
  have hn' : n ≤ Backend.factor family *
      (memoryCost (dequeue d) (memoryState (Backend.frontier family) x) + 1) := by
    simpa only [Nat.add_zero] using hn
  let m : Counts := ⟨p.1.front.length, p.1.rear.length⟩
  have hcommit : Exec w commit b (committed m b) 2 := commit_exec (ho 0) (ho 1)
  have hcond : ¬(Cond.eq tag zero).Holds z := by
    simp [z, Cond.Holds, staged_tag, staged_zero]
  have he : Exec w program ((implementation w capacity).prepare .dequeue x)
      (committed m b) (1 + (n + 2 + 2)) :=
    (stage_exec w capacity .dequeue x).seq ((Exec.branch_neg hcond hb).seq hcommit)
  have hsrc (i : Fin 5) : b.regs (src i) = d i := by
    rw [hframe _ (src_ne_frontier i) (fun a => (Backend.src_ne_tmp family false true i a).symm)]
    exact congrFun (staged_input hr .dequeue) i
  have hm0 := hm.trans (clientState_width w _ _)
  have hfrontier : b.regs (Backend.frontier family) = x.regs (Backend.frontier family) :=
    (congrArg Memory.State.frontier hm0).trans hi.2.2.2.1
  have hmem : b.mem =
      ((Memory.spec 0).clientState (memoryState (Backend.frontier family) x) (dequeue d)).mem :=
    congrArg Memory.State.mem hm0
  have hs := pairStep_length_le (w := w) (capacity := capacity) (s := ⟨front, back⟩)
    (by simpa only [Stacks.contents_length] using hr.size_le) .dequeue trivial
  refine ⟨committed m b, 1 + (n + 2 + 2), he, by
      dsimp only [d] at hn'; omega,
    committed_rep (hcommit.bounded hbb) (hsrc 2) (hsrc 3) (hfrontier.trans hr.frontier_eq)
      (by simpa only [Stacks.contents_length] using hs) (hmem ▸ hcontents.2.1)
      (hmem ▸ hcontents.2.2), ?_, hmem ▸ hi.2.2.2.2.2⟩
  have ht : (committed m b).regs (result 2) = optionWords p.2 0 :=
    (committed_other m b _ (src_ne_result 0 2).symm (src_ne_result 1 2).symm).trans (ho 2)
  have hv : (committed m b).regs (result 3) = optionWords p.2 1 :=
    (committed_other m b _ (src_ne_result 0 3).symm (src_ne_result 1 3).symm).trans (ho 3)
  rw [decode_dequeue, ht, hv]
  cases p.2 <;> rfl

/-- One admissible call of the fixed native queue. The terminal rear potential is retained;
the globally chosen exchange factor, control, metadata copies and halt are all charged.
The external controller and tag/payload delivery remain the original dynamic-call boundary. -/
theorem execute {w base capacity : ℕ} {front back : List ℕ} {x : Data registers}
    (h1 : Fits w 1) (hr : Rep w base capacity front back x) (o : Queue.QueueOp ℕ)
    (hv : (spec w capacity).valid (Stacks.contents ⟨front, back⟩) o) :
    let p := pairStep ⟨front, back⟩ o
    ∃ y n, Exec w program ((implementation w capacity).prepare o x) y n ∧
      (implementation w capacity).decode o y.regs = some p.2 ∧
      Rep w base capacity p.1.front p.1.rear y ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      n + 1 + potential y ≤ 4 * Backend.factor family + 6 + potential x := by
  cases o with
  | enqueue v =>
    change (Stacks.contents ⟨front, back⟩).length < capacity ∧ Fits w v at hv
    rw [Stacks.contents_length] at hv
    obtain ⟨y, n, he, hn, hry, hm⟩ := execute_enqueue h1 hr hv.1 hv.2
    refine ⟨y, n, he, rfl, hry, hm, ?_⟩
    simp only [potential, hry.backLen_eq, hr.backLen_eq, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    omega
  | dequeue =>
    obtain ⟨y, n, he, hn, hry, ha, hm⟩ := execute_dequeue h1 hr
    let d : Input := ![front.length, back.length, base, capacity, 0]
    have hw : Memory.WellFormed w (memoryState (Backend.frontier family) x) :=
      wellFormed_memoryState hr.bounded
    have hdom : transferDomain w d (memoryState (Backend.frontier family) x) :=
      ⟨hr.size_le, hr.frontier_eq.ge⟩
    have hcontents := dequeue_contents (d := d) front back
      (memoryState (Backend.frontier family) x) hw rfl rfl hr.size_le hr.frontier_eq.ge
      hr.front_contents hr.back_contents
    have hpay := dequeue_memory_amortized hw hdom
    rw [hcontents.1] at hpay
    change memoryCost (dequeue d) (memoryState (Backend.frontier family) x) +
      2 * (pairStep ⟨front, back⟩ .dequeue).1.rear.length ≤ 3 + 2 * back.length at hpay
    change n + 1 ≤ Backend.factor family *
      (memoryCost (dequeue d) (memoryState (Backend.frontier family) x) + 1) + 6 at hn
    refine ⟨y, n, he, ha, hry, hm, ?_⟩
    simp only [potential, hry.backLen_eq, hr.backLen_eq]
    nlinarith [Nat.mul_le_mul_left (Backend.factor family) hpay]

/-- The fixed realized dispatcher implements the original bounded FIFO specification via
the existing dynamic certificate. Its representation retains resident count words; no
memory-only Backend implementation is asserted. The bounded resident frontier equals the physical
end, so its fit already follows from `Rep`; raw initialization keeps its explicit end-fit
premise. -/
noncomputable def certificate {w base capacity : ℕ} (h1 : Fits w 1) :
    DynamicCertificate (implementation w capacity) w :=
  DynamicCertificate.ofFn
    (rep := QueueRep w base capacity)
    (bounded := fun h => by obtain ⟨_, _, _, hr⟩ := h; exact hr.bounded)
    (arguments_fit := fun o hv i _ => by
      exact encoded_fits h1 o (by
        cases o with
        | enqueue v => exact hv.2
        | dequeue => trivial) i)
    (execute := fun o hr hv => by
      obtain ⟨front, back, rfl, hr⟩ := hr
      obtain ⟨y, n, he, ha, hy, _, _⟩ := execute h1 hr o hv
      have hs := pairStep_correct ⟨front, back⟩ o
      exact ⟨y, n, he, ha.trans (congrArg some (congrArg Prod.snd hs)),
        ⟨_, _, (congrArg Prod.fst hs).symm, hy⟩⟩)

end Cslib.DataStructure.Queue.WordRAM
