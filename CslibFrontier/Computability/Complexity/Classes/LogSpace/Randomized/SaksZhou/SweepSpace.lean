/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SaksZhou.Sweep
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NestedLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Tactic.Space

/-!
# Space for a seeded Saks–Zhou walk

The sweep stores its positions, destination selection, residual label and hit count in
binary. Its input word and the common seed can remain read-only at all levels.

## Main results

* `Cslib.Probability.SaksZhou.sweepUpdate_inSpace` computes one sweep step within the
  shared space budget for its inputs and the letter selector.
-/

public section

namespace Cslib.Probability.SaksZhou

open Turing.MultiTapeTM ComputableInSpace

/-- Starting block, position, column, current vertex, candidate, residual and hits, in
that order. All fields are binary naturals, with each left component framed. -/
enc_structure encSweepState : SweepState logspace where
  x : encNat, t : encNat, j : encNat, current : encNat, candidate : encNat, residual : encNat,
  hits : encNat

/-- The row and column of a recursive matrix-entry request, including possible sink and marker
indices. -/
structure SweepJob where
  /-- Source index. -/
  row : ℕ
  /-- Destination index. -/
  column : ℕ

/-- The framed binary row index, followed by the binary column index. -/
enc_structure encSweepJob : SweepJob logspace where row : encNat, column : encNat

/-- Run the nested sweep for a matrix entry. Each pass through a column asks for one entry
at the preceding depth. `roundValue` takes the positive level and the completed hit count.
Requests outside the matrix have value zero, including queries for marker columns. -/
@[expose] def sweepLoop {α : Type} (width steps starts scale : α → ℕ)
    (label : α → ℕ → ℕ → ℕ) (base : α → SweepJob → ℕ) (roundValue : α → ℕ → ℕ → ℕ) :
    NestedLoop α SweepJob SweepState ℕ where
  base a j := if j.row < width a ∧ j.column < width a then base a j else 0
  start a _ j := sweepStart (width a) j.row
  rounds a _ := starts a * ((width a + 2) * steps a + 1)
  query _ _ _ r := ⟨r.current, r.j⟩
  update a _ j r ans := sweepUpdate (width a) (steps a) (scale a) j.row j.column (label a) r ans
  finish a d j r := if j.row < width a ∧ j.column < width a then roundValue a d r.hits else 0

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

/-- Initialize a sweep within the workspace available for the binary width and source. -/
theorem sweepStart_inSpace {n src : α → ℕ} (hn : ComputableInSpace n enc encNat S)
    (hs : ComputableInSpace src enc encNat S) :
    ComputableInSpace (fun a => sweepStart (n a) (src a)) enc encSweepState S := by
  exact encSweepState_mk_budget (budget_const 0) (budget_const 0) (budget_natSucc hn)
    hs (budget_const 0) (budget_const 0) (budget_const 0)

/-- A sweep update fits a common workspace for its registers, binary numerical parameters,
and the current pseudorandom letter. -/
theorem sweepUpdate_inSpace {n len scale src dst ans : α → ℕ}
    {letter : α → ℕ → ℕ → ℕ} {state : α → SweepState}
    (hn : ComputableInSpace n enc encNat S) (hl : ComputableInSpace len enc encNat S)
    (hm : ComputableInSpace scale enc encNat S) (hs : ComputableInSpace src enc encNat S)
    (hd : ComputableInSpace dst enc encNat S) (ha : ComputableInSpace ans enc encNat S)
    (hr : ComputableInSpace state enc encSweepState S)
    (hlet : ComputableInSpace (fun a => letter a (state a).x (state a).t) enc encNat S) :
    ComputableInSpace (fun a => sweepUpdate (n a) (len a) (scale a) (src a) (dst a)
      (letter a) (state a) (ans a)) enc encSweepState S := by
  have hx := encSweepState_x_budget hr
  have ht := encSweepState_t_budget hr
  have hj := encSweepState_j_budget hr
  have hu := encSweepState_current_budget hr
  have hc := encSweepState_candidate_budget hr
  have hrem := encSweepState_residual_budget hr
  have hh := encSweepState_hits_budget hr
  have hweight := budget_natMul ha hm
  unfold sweepUpdate
  refine budget_iteProp (budget_natEq ht hl) ?_ ?_
  · exact encSweepState_mk_budget (budget_natSucc hx) (budget_const 0) (budget_natSucc hn)
      hs (budget_const 0) (budget_const 0) (budget_natAdd hh
        (budget_iteProp (budget_natEq hu hd) (budget_const 1) (budget_const 0)))
  refine budget_iteProp (budget_natEq hj (budget_natSucc hn)) ?_ ?_
  · exact encSweepState_mk_budget hx ht (budget_const 0) hu (budget_const 0) hlet hh
  refine budget_iteProp (budget_natEq hj hn) ?_ ?_
  · exact encSweepState_mk_budget hx (budget_natSucc ht) (budget_natSucc hn)
      hc (budget_const 0) (budget_const 0) hh
  refine budget_iteProp (budget_decideAnd (budget_natEq hj hc) (budget_natLe hweight hrem)) ?_ ?_
  · exact encSweepState_mk_budget hx ht (budget_natSucc hj) hu (budget_natSucc hc)
      (budget_natSub hrem hweight) hh
  · exact encSweepState_mk_budget hx ht (budget_natSucc hj) hu hc hrem hh

/-- Registers in one frame contain the binary level and remaining sweep count, the two
binary vertex indices, and the seven sweep registers. -/
abbrev encSweepFrame := NestedLoop.encFrame SweepJob SweepState encSweepJob encSweepState

/-- Framed sweep frame, optional binary answer, then the read-only common context. -/
abbrev encSweepInput (enc : α ↪ List Bool) :=
  NestedLoop.encBodyInput enc encSweepJob encSweepState encNat

/-- Current sweep frame and optional answer paired with the common read-only input. -/
abbrev SweepInput (α : Type) := (NestedLoop.Frame SweepJob SweepState × Option ℕ) × α

/-- The local call or return fits its common workspace. The rounder acts on the completed
hit count, while the letter selector acts on the saved sweep position. -/
theorem sweepLoop_body_inSpace {S : SweepInput α → ℕ} {n steps starts scale : α → ℕ}
    {letter : α → ℕ → ℕ → ℕ} {base : α → SweepJob → ℕ} {roundValue : α → ℕ → ℕ → ℕ}
    (hconfig : ComputableInSpace (Prod.fst : SweepInput α → _)
      (encSweepInput enc) (encPair encSweepFrame (encOption encNat)) S)
    (hn : ComputableInSpace (fun p : SweepInput α => n p.2) (encSweepInput enc) encNat S)
    (hl : ComputableInSpace (fun p : SweepInput α => steps p.2) (encSweepInput enc) encNat S)
    (hst : ComputableInSpace (fun p : SweepInput α => starts p.2) (encSweepInput enc) encNat S)
    (hm : ComputableInSpace (fun p : SweepInput α => scale p.2) (encSweepInput enc) encNat S)
    (hletter : ComputableInSpace (fun ((f, _), a) => letter a f.reg.x f.reg.t)
      (encSweepInput enc) encNat S)
    (hbase : ComputableInSpace (fun ((f, _), a) => base a f.job) (encSweepInput enc) encNat S)
    (hround : ∀ hits, ComputableInSpace hits (encSweepInput enc) encNat S →
      ComputableInSpace (fun p : SweepInput α => roundValue p.2 p.1.fst.level (hits p))
        (encSweepInput enc) encNat S) :
    ComputableInSpace (sweepLoop n steps starts scale letter base roundValue).body
      (encSweepInput enc) (NestedLoop.encBodyOutput encSweepJob encSweepState encNat) S := by
  have hframe := hconfig.fst'
  have hopt := hconfig.snd'
  have hd := NestedLoop.encFrame_level_budget SweepJob SweepState encSweepJob encSweepState hframe
  have hjob := NestedLoop.encFrame_job_budget SweepJob SweepState encSweepJob encSweepState hframe
  have hleft := NestedLoop.encFrame_remaining_budget SweepJob SweepState encSweepJob encSweepState
    hframe
  have hreg := NestedLoop.encFrame_reg_budget SweepJob SweepState encSweepJob encSweepState hframe
  have hrow := encSweepJob_row_budget hjob
  have hcol := encSweepJob_column_budget hjob
  have hvalid := budget_decideAnd (budget_natLt hrow hn) (budget_natLt hcol hn)
  have hnext := budget_ite (budget_optionIsSome hopt)
    (sweepUpdate_inSpace hn hl hm hrow hcol (budget_optionGetD 0 hopt) hreg hletter) hreg
  have hchild := encSweepJob_mk_budget (encSweepState_current_budget hnext)
    (encSweepState_j_budget hnext)
  have hcount := budget_natMul hst (budget_natSucc (budget_natMul (budget_natAdd hn
    (budget_const 2)) hl))
  have hspawn := NestedLoop.encFrame_mk_budget SweepJob SweepState encSweepJob encSweepState
    (budget_natPred hd) hchild hcount (sweepStart_inSpace hn (encSweepState_current_budget hnext))
  have hsave := NestedLoop.encFrame_mk_budget SweepJob SweepState encSweepJob encSweepState
    hd hjob (budget_natPred hleft) hnext
  have hret := hround _ (encSweepState_hits_budget hnext)
  have h := budget_iteProp (budget_natEq hd (budget_const 0))
    (budget_sumInr (budget_iteProp hvalid hbase (budget_const 0)))
    (budget_iteProp (budget_natEq hleft (budget_const 0))
      (budget_sumInr (budget_iteProp hvalid hret (budget_const 0)))
      (budget_sumInl (budget_prod hsave hspawn)))
  apply h.of_enc_eq
  rintro ⟨⟨⟨d, j, k, r⟩, o⟩, a⟩
  cases d <;> cases k <;> cases o <;> rfl

end Cslib.Probability.SaksZhou
