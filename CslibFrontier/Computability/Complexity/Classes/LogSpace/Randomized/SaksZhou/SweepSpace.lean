/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
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
    (hbase : ComputableInSpace (fun ((f, _), a) =>
      if f.job.row < n a ∧ f.job.column < n a then base a f.job else 0)
      (encSweepInput enc) encNat S)
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
    (budget_sumInr hbase)
    (budget_iteProp (budget_natEq hleft (budget_const 0))
      (budget_sumInr (budget_iteProp hvalid hret (budget_const 0)))
      (budget_sumInl (budget_prod hsave hspawn)))
  apply h.of_enc_eq
  rintro ⟨⟨⟨d, j, k, r⟩, o⟩, a⟩
  cases d <;> cases k <;> cases o <;> rfl

private structure StateBound (n blocks elapsed : ℕ) (r : SweepState) : Prop where
  x : r.x ≤ elapsed
  t : r.t ≤ elapsed
  j : r.j ≤ n + 1
  current : r.current ≤ n + 1
  candidate : r.candidate ≤ n + 1
  residual : r.residual ≤ blocks
  hits : r.hits ≤ elapsed

private theorem StateBound.start {n blocks src : ℕ} (hs : src ≤ n + 1) :
    StateBound n blocks 0 (sweepStart n src) :=
  ⟨by rfl, by rfl, by rfl, hs, Nat.zero_le _, Nat.zero_le _, by rfl⟩

private theorem StateBound.succ {n blocks elapsed : ℕ} {r : SweepState}
    (h : StateBound n blocks elapsed r) : StateBound n blocks (elapsed + 1) r :=
  ⟨Nat.le_succ_of_le h.x, Nat.le_succ_of_le h.t, h.j, h.current, h.candidate, h.residual,
    Nat.le_succ_of_le h.hits⟩

private theorem StateBound.update {n blocks elapsed len scale src dst answer : ℕ}
    {r : SweepState} {letter : ℕ → ℕ → ℕ} (h : StateBound n blocks elapsed r)
    (hs : src ≤ n + 1) (hl : letter r.x r.t ≤ blocks) :
    StateBound n blocks (elapsed + 1) (sweepUpdate n len scale src dst letter r answer) := by
  rcases h with ⟨hx, ht, hj, hu, hc, hr, hh⟩
  unfold sweepUpdate
  split_ifs <;> (constructor <;> dsimp only <;> omega)

private structure FrameBound (d n blocks total : ℕ) (f : NestedLoop.Frame SweepJob SweepState) :
    Prop where
  level : f.level ≤ d
  row : f.job.row ≤ n + 1
  column : f.job.column ≤ n + 1
  remaining : f.remaining ≤ total
  reg : StateBound n blocks (total - f.remaining) f.reg

private theorem FrameBound.length_le {d n blocks total : ℕ}
    {f : NestedLoop.Frame SweepJob SweepState} (h : FrameBound d n blocks total f) :
    (encSweepFrame f).length ≤
      32 * ((encNat (max (max d (n + 1)) (max blocks total))).length + 1) := by
  let M := max (max d (n + 1)) (max blocks total)
  have hd : d ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn : n + 1 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hb : blocks ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have ht : total ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have he : total - f.remaining ≤ M := (Nat.sub_le ..).trans ht
  have := length_encNat_mono (h.level.trans hd)
  have := length_encNat_mono (h.row.trans hn)
  have := length_encNat_mono (h.column.trans hn)
  have := length_encNat_mono (h.remaining.trans ht)
  have := length_encNat_mono (h.reg.x.trans he)
  have := length_encNat_mono (h.reg.t.trans he)
  have := length_encNat_mono (h.reg.j.trans hn)
  have := length_encNat_mono (h.reg.current.trans hn)
  have := length_encNat_mono (h.reg.candidate.trans hn)
  have := length_encNat_mono (h.reg.residual.trans hb)
  have := length_encNat_mono (h.reg.hits.trans he)
  change _ ≤ 32 * ((encNat M).length + 1)
  simp only [encSweepFrame, NestedLoop.encFrame_apply, NestedLoop.encFrameFields, encSweepJob_apply,
    encSweepJobFields, encSweepState_apply, encSweepStateFields, length_encPair]
  omega

/-- A binary length bound for one suspended frame. It counts depth, matrix width,
block count, and the total number of sweeps, independently of the shared seed. -/
@[expose] def sweepFrameBits (depth width blocks total : ℕ) : ℕ :=
  32 * ((encNat (max (max depth (width + 1)) (max blocks total))).length + 1)

/-- The recursive sweep uses one binary frame per level and pays the shared seed and local
workspace only once. The bounded starting indices include the sink and marker. `answerBits`
bounds the size of any genuine recursive result. -/
theorem sweepLoop_inSpace {D S G answerBits n steps starts scale : α → ℕ}
    {letter : α → ℕ → ℕ → ℕ} {base : α → SweepJob → ℕ} {roundValue : α → ℕ → ℕ → ℕ}
    {root : α → SweepJob}
    (hroot : ∀ a, (root a).row ≤ n a + 1 ∧ (root a).column ≤ n a + 1)
    (hletter : ∀ a x t, letter a x t ≤ starts a)
    (hanswer : ∀ a d j, d ≤ D a → j.row ≤ n a + 1 → j.column ≤ n a + 1 →
      (encNat ((sweepLoop n steps starts scale letter base roundValue).run a d j)).length ≤
        answerBits a)
    (hinit : ComputableInSpace (fun a =>
      (sweepLoop n steps starts scale letter base roundValue).entry a (D a) (root a))
      enc encSweepFrame S)
    (hbody : ComputableInSpace (sweepLoop n steps starts scale letter base roundValue).body
      (encSweepInput enc) (NestedLoop.encBodyOutput encSweepJob encSweepState encNat)
      fun p => (encPair encSweepFrame (encOption encNat) p.1).length + G p.2) :
    ComputableInSpace (fun a => (sweepLoop n steps starts scale letter base roundValue).run a
      (D a) (root a)) enc encNat fun a =>
        let total := starts a * ((n a + 2) * steps a + 1)
        let F := sweepFrameBits (D a) (n a) (starts a) total
        S a + (D a * (F + 1) + (2 * F + answerBits a + G a + 2)) + Nat.log2 (enc a).length := by
  let L := sweepLoop n steps starts scale letter base roundValue
  let total a := starts a * ((n a + 2) * steps a + 1)
  let F a := sweepFrameBits (D a) (n a) (starts a) (total a)
  let V (a : α) (c : NestedLoop.Frame SweepJob SweepState × Option ℕ) :=
    FrameBound (D a) (n a) (starts a) (total a) c.1 ∧
      ∀ v, c.2 = some v → (encNat v).length ≤ answerBits a
  apply L.inSpace (F := F) (B := fun a => 2 * F a + answerBits a + G a + 2) V hinit hbody
  · intro a
    refine ⟨⟨le_rfl, (hroot a).1, (hroot a).2, le_rfl, ?_⟩, by simp⟩
    simpa [L, sweepLoop, NestedLoop.entry, total] using
      (StateBound.start (blocks := starts a) (hroot a).1)
  · rintro a ⟨⟨d,j,k,s⟩,o⟩ saved child ⟨hb, _⟩ hc
    cases d with
    | zero => simp [L, NestedLoop.body] at hc
    | succ d =>
      cases k with
      | zero => simp [L, NestedLoop.body] at hc
      | succ k =>
        simp only [L, NestedLoop.body, Sum.inl.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        let r := o.elim s ((sweepLoop n steps starts scale letter base roundValue).update
          a (d + 1) j s)
        have hk : k + 1 ≤ total a := hb.remaining
        have he : total a - k = total a - (k + 1) + 1 := by omega
        have hr : StateBound (n a) (starts a) (total a - k) r := by
          rw [he]
          cases o with
          | none => exact hb.reg.succ
          | some ans => exact hb.reg.update hb.row (hletter a _ _)
        have hchild : FrameBound (D a) (n a) (starts a) (total a)
            (L.entry a d ⟨r.current, r.j⟩) := by
          refine ⟨(Nat.le_succ _).trans hb.level, hr.current, hr.j, le_rfl, ?_⟩
          simpa only [L, NestedLoop.entry, sweepLoop, total, Nat.sub_self] using
            (StateBound.start (blocks := starts a) hr.current)
        have hsave : FrameBound (D a) (n a) (starts a) (total a)
            (⟨d + 1, j, k, r⟩ : NestedLoop.Frame SweepJob SweepState) :=
          ⟨hb.level, hb.row, hb.column, (Nat.le_succ _).trans hk, hr⟩
        refine ⟨⟨hchild, by simp⟩, ⟨hsave, ?_⟩, hsave.length_le⟩
        intro v hv
        have hh : L.run a d ⟨r.current, r.j⟩ = v := Option.some.inj hv
        rw [← hh]
        exact hanswer _ _ _ hchild.level hchild.row hchild.column
  · rintro a ⟨f, o⟩ ⟨hf, ho⟩
    have hlen : (encSweepFrame f).length ≤ F a := hf.length_le
    rw [length_encPair]
    cases o with
    | none => simp only [encOption_none, List.length_nil]; omega
    | some v =>
      have := ho v rfl
      simp only [encOption_some, List.length_cons]
      omega

end Cslib.Probability.SaksZhou
