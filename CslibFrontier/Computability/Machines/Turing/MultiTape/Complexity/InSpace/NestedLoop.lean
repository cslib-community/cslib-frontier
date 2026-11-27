/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Recursion
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Space of nested loops with a recursive query in each iteration

One iteration launches a job one level lower and incorporates the reply into the current
register. The innermost level reads the common input directly. Only the suspended registers
occupy space across recursive calls. The time spent evaluating earlier siblings is unrestricted.

## Main definitions

* `Turing.MultiTapeTM.NestedLoop` describes the register update, query and return value.
* `Turing.MultiTapeTM.NestedLoop.run` folds the answers of all children at each level.
* `Turing.MultiTapeTM.NestedLoop.body` performs one local call or return.

## Main results

* `Turing.MultiTapeTM.NestedLoop.inSpace` adds the space of the deepest chain of suspended frames
  to the local body's workspace and the input-position counter.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A read-only input shared by a hierarchy of loops. Every positive-level iteration makes
one recursive query at the preceding level. Level arguments to the operations denote the
current frame's level. -/
structure NestedLoop (α J R β : Type) where
  /-- The value of a level-zero job. -/
  base : α → J → β
  /-- The initial register of a job. -/
  start : α → ℕ → J → R
  /-- The number of iterations at a level. The level-zero body ignores this count. -/
  rounds : α → ℕ → ℕ
  /-- The job launched by the current register. -/
  query : α → ℕ → J → R → J
  /-- Incorporate the lower-level reply in the register. -/
  update : α → ℕ → J → R → β → R
  /-- Read the final result from the register. -/
  finish : α → ℕ → J → R → β

namespace NestedLoop

variable {α J R β : Type} (L : NestedLoop α J R β)

/-- Evaluate a job by recursively folding its children's replies. -/
def run (a : α) : ℕ → J → β
  | 0, j => L.base a j
  | d + 1, j =>
    L.finish a (d + 1) j ((fun r =>
      L.update a (d + 1) j r (run a d (L.query a (d + 1) j r)))^[L.rounds a (d + 1)]
      (L.start a (d + 1) j))

/-- A suspended invocation. The register is saved before the next child's response. -/
structure Frame (J R : Type) where
  /-- Depth remaining below this job. -/
  level : ℕ
  /-- The job at this level. -/
  job : J
  /-- Number of iterations still to launch. -/
  remaining : ℕ
  /-- State before consuming an incoming reply. -/
  reg : R

/-- Binary level, job, binary number of remaining iterations and register, paired in field order
with each left component framed. -/
enc_structure encFrame (J : Type) (R : Type) (ej : J ↪ List Bool) (er : R ↪ List Bool) :
    Frame J R logspace where
  level : encNat, job : ej, remaining : encNat, reg : er

/-- A fresh invocation whose register and remaining iteration count are initialized. -/
def entry (a : α) (d : ℕ) (j : J) : Frame J R :=
  ⟨d, j, L.rounds a d, L.start a d j⟩

/-- Perform the next local operation on a frame and any reply waiting for it. A left result
suspends a frame and launches a child. A right result returns a value. -/
def body (p : (Frame J R × Option β) × α) : (Frame J R × Frame J R) ⊕ β :=
  let ((f, reply), a) := p
  let r := reply.elim f.reg (L.update a f.level f.job f.reg)
  match f.level, f.remaining with
  | 0, _ => .inr (L.base a f.job)
  | d + 1, 0 => .inr (L.finish a (d + 1) f.job r)
  | d + 1, k + 1 => .inl (⟨d + 1, f.job, k, r⟩,
      L.entry a d (L.query a (d + 1) f.job r))

private def value (a : α) (c : Frame J R × Option β) : β :=
  match c.1.level with
  | 0 => L.base a c.1.job
  | d + 1 =>
    L.finish a (d + 1) c.1.job ((fun r =>
      L.update a (d + 1) c.1.job r (L.run a d (L.query a (d + 1) c.1.job r)))^[c.1.remaining]
      (c.2.elim c.1.reg (L.update a c.1.level c.1.job c.1.reg)))

private theorem value_entry (a : α) (d : ℕ) (j : J) :
    L.value a (L.entry a d j, none) = L.run a d j := by
  cases d <;> rfl

/-- The first rank at a given level exceeds all possible freshly launched child ranks. -/
private def offset (a : α) : ℕ → ℕ
  | 0 => 0
  | d + 1 => offset a d + L.rounds a d + 1

/-- Framed current frame and optional reply, followed by the read-only input. -/
abbrev encBodyInput (ea : α ↪ List Bool) (ej : J ↪ List Bool) (er : R ↪ List Bool)
    (eb : β ↪ List Bool) :=
  encPair (encPair (encFrame J R ej er) (encOption eb)) ea

/-- One tag followed by a pair of saved and child frames, or by the returned value. -/
abbrev encBodyOutput (ej : J ↪ List Bool) (er : R ↪ List Bool) (eb : β ↪ List Bool) :=
  encSum (encPair (encFrame J R ej er) (encFrame J R ej er)) eb

/-- If the local body works within `B` bits on reachable invocations and every suspended frame
is at most `F` bits long, a job at depth `D` takes space
`O(S + D * (F + 1) + B + log n)`, where `S` is the initialization budget.
The invariant may depend on both the common input and the returned value. -/
theorem inSpace {ea : α ↪ List Bool} {ej : J ↪ List Bool} {er : R ↪ List Bool}
    {eb : β ↪ List Bool} {D S F B : α → ℕ} {job : α → J}
    {T : (Frame J R × Option β) × α → ℕ} (Valid : α → Frame J R × Option β → Prop)
    (hinit : ComputableInSpace (fun a => L.entry a (D a) (job a)) ea (encFrame J R ej er) S)
    (hbody : ComputableInSpace L.body (encBodyInput ea ej er eb) (encBodyOutput ej er eb) T)
    (hstart : ∀ a, Valid a (L.entry a (D a) (job a), none))
    (hcall : ∀ a c s t, Valid a c → L.body (c, a) = .inl (s, t) →
      Valid a (t, none) ∧ Valid a (s, some (L.run a t.level t.job)) ∧
        (encFrame J R ej er s).length ≤ F a)
    (hbudget : ∀ a c, Valid a c → T (c, a) ≤ B a) :
    ComputableInSpace (fun a => L.run a (D a) (job a)) ea eb
      fun a => S a + (D a * (F a + 1) + B a) + Nat.log2 (ea a).length := by
  let rank (a : α) (c : Frame J R × Option β) := L.offset a c.1.level + c.1.remaining
  let need (a : α) (c : Frame J R × Option β) := c.1.level * (F a + 1) + B a
  have h := ComputableInSpace.recWith (B := fun a => D a * (F a + 1) + B a)
    L.value rank need Valid hinit hbody hstart
    (fun a c s t hc hst => by
      obtain ⟨hf, hs, _⟩ := hcall a c s t hc hst
      rcases c with ⟨⟨d,j,k,r⟩,o⟩
      cases d with
      | zero => simp [body] at hst
      | succ d =>
        cases k with
        | zero => simp [body] at hst
        | succ k =>
          simp only [body, Sum.inl.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          refine ⟨hf, ?_, ?_, ?_, ?_⟩
          · rw [value_entry]
            exact hs
          · dsimp [rank, entry, offset]
            omega
          · dsimp [rank, entry]
            omega
          · rw [value_entry]
            simp only [value, Option.elim_some, Function.iterate_succ_apply])
    (fun a c s t hc hst => by
      obtain ⟨_, _, hlen⟩ := hcall a c s t hc hst
      rcases c with ⟨⟨d,j,k,r⟩,o⟩
      cases d with
      | zero => simp [body] at hst
      | succ d =>
        cases k with
        | zero => simp [body] at hst
        | succ k =>
          simp only [body, Sum.inl.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          dsimp only [need, entry] at *
          rw [Nat.succ_mul]
          omega)
    (fun a c v _ hv => by
      rcases c with ⟨⟨d,j,k,r⟩,o⟩
      cases d with
      | zero => simpa [value, body] using hv
      | succ d =>
        cases k with
        | zero => simpa [value, body] using hv
        | succ k => simp [body] at hv)
    (fun a c hc => (hbudget a c hc).trans (Nat.le_add_left _ _))
    (fun _ => le_rfl)
  simpa only [value_entry] using h

end NestedLoop

end Turing.MultiTapeTM
