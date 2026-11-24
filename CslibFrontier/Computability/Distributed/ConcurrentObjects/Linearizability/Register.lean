/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Basic
import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.CallIndex

/-!
# Atomic read/write registers and sequential-consistency separations

Sequential atomic read/write register specification (`RegOp`, `RegResp`, `registerStep`,
`registerSeqSpec`) and explicit register counterparts of the `H_7` and `H_8` counterexamples of
[HerlihyWing1990] (§3.3, p. 472) separating linearizability from sequential consistency and showing
that sequential consistency is not local across multiple objects.

## Main definitions

* `Cslib.Distributed.ConcurrentObjects.RegOp`,
  `Cslib.Distributed.ConcurrentObjects.RegResp`,
  `Cslib.Distributed.ConcurrentObjects.registerSeqSpec`: sequential atomic read/write register
  operations, responses, and `SeqSpec`.

## Main results

* `Cslib.Distributed.ConcurrentObjects.exists_sequentiallyConsistent_not_linearizable`: explicit
  well-formed single-register history that is sequentially consistent but not linearizable
  (register counterpart of `H_7` in [HerlihyWing1990], §3.3, p. 472).
* `Cslib.Distributed.ConcurrentObjects.exists_obj_sequentiallyConsistent_not_global`: **non-locality
  of sequential consistency** — explicit well-formed 2-process, 2-register history whose per-object
  subhistories are each sequentially consistent while the combined history is not sequentially
  consistent (register counterpart of `H_8` in [HerlihyWing1990], §3.3, p. 472).

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

/-- Operations on an atomic read/write register over value type `V`. -/
inductive RegOp (V : Type*) where
  /-- Read the current register value. -/
  | read
  /-- Write `val` to the register. -/
  | write (val : V)
  deriving @[expose] DecidableEq

/-- Responses returned by an atomic read/write register over value type `V`. -/
inductive RegResp (V : Type*) where
  /-- Return `val` from a `read`. -/
  | readRet (val : V)
  /-- Acknowledge a completed `write`. -/
  | writeAck
  deriving @[expose] DecidableEq

/-- Sequential transition function of an atomic read/write register. -/
@[expose]
def registerStep {V : Type*} (s : V) : RegOp V → V × RegResp V
  | .read => (s, .readRet s)
  | .write v => (v, .writeAck)

/-- Sequential specification of an atomic read/write register `x : Obj` initialized to `init`. -/
def registerSeqSpec {P Obj V : Type*} (x : Obj) (init : V) :
    SeqSpec P (fun _ : Obj => RegOp V) (fun _ : Obj => RegResp V) x :=
  SeqSpec.ofMachine x init registerStep

private theorem resp_ext_eq_nil_of_even_proc {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R : History P Op Resp} (hwf : History.WellFormed H)
    (hev : ∀ p : P, (History.procSubhistory H p).length % 2 = 0)
    (hrespR : History.IsRespList R) (hwf' : History.WellFormed (H ++ R)) : R = [] := by
  cases R with
  | nil => rfl
  | cons e rs =>
    cases e with
    | inv _ _ _ => exact Bool.noConfusion (hrespR _ List.mem_cons_self)
    | resp p x res =>
      have hp := hwf' p
      rw [History.procSubhistory_append] at hp
      have hresp_p : History.IsRespList (History.procSubhistory (.resp p x res :: rs) p) :=
        fun a ha => hrespR a (List.mem_filter.mp ha).1
      have hnil_p :=
        History.isRespList_eq_nil_of_isSequential_even (hwf p) (hev p) hresp_p hp
      simp only [History.procSubhistory_cons, Event.proc_resp, ↓reduceIte] at hnil_p
      nomatch hnil_p

private theorem filter_proc_bool_length_sum {Obj : Type*} {Op Resp : Obj → Type*}
    (l : List (OpCall Bool Op Resp)) :
    (l.filter fun c => decide (c.proc = false)).length +
      (l.filter fun c => decide (c.proc = true)).length = l.length := by
  have h := List.length_eq_length_filter_add (l := l) (fun c => decide (c.proc = false))
  have hnot : (fun c : OpCall Bool Op Resp => !decide (c.proc = false)) =
      fun c => decide (c.proc = true) := by
    funext c; cases c.proc <;> rfl
  rw [hnot] at h
  exact h.symm

private theorem dekker_write_not_lt_stale_read
    {c0 c1 c2 c3 : OpCall Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool)}
    (reg : Bool)
    (hleg : History.objSubhistory ([c0, c1, c2, c3].flatMap OpCall.toEvents) reg ∈
      (registerSeqSpec reg false).allowed)
    {jA0 jA1 jB0 jB1 : ℕ}
    (hjA0 : jA0 < 4) (hjA1 : jA1 < 4) (hjB0 : jB0 < 4) (hjB1 : jB1 < 4)
    (hltA : jA0 < jA1) (hltB : jB0 < jB1)
    (hne00 : jA0 ≠ jB0) (hne01 : jA0 ≠ jB1) (hne10 : jA1 ≠ jB0) (hne11 : jA1 ≠ jB1)
    (eA0 : [c0, c1, c2, c3][jA0] = ⟨reg, reg, .write true, .writeAck⟩)
    (eA1 : [c0, c1, c2, c3][jA1] = ⟨reg, !reg, .read, .readRet false⟩)
    (eB0 : [c0, c1, c2, c3][jB0] = ⟨!reg, !reg, .write true, .writeAck⟩)
    (eB1 : [c0, c1, c2, c3][jB1] = ⟨!reg, reg, .read, .readRet false⟩) :
    ¬ jA0 < jB1 := by
  intro hlt
  rw [History.objSubhistory_flatMap_toEvents] at hleg
  unfold registerSeqSpec at hleg
  rw [SeqSpec.mem_ofMachine_allowed] at hleg
  have hother : ∀ (k : ℕ) (hk : k < 4), k ≠ jA0 → k ≠ jB1 →
      decide (([c0, c1, c2, c3][k]'hk).obj = reg) = false := by
    intro k hk h1 h2
    have hor : k = jA1 ∨ k = jB0 := by omega
    rcases hor with rfl | rfl
    · rw [eA1]; cases reg <;> rfl
    · rw [eB0]; cases reg <;> rfl
  have h6 : (jA0 = 0 ∧ jB1 = 1) ∨ (jA0 = 0 ∧ jB1 = 2) ∨ (jA0 = 0 ∧ jB1 = 3) ∨
      (jA0 = 1 ∧ jB1 = 2) ∨ (jA0 = 1 ∧ jB1 = 3) ∨ (jA0 = 2 ∧ jB1 = 3) := by omega
  have hfil : ([c0, c1, c2, c3].filter fun c => decide (c.obj = reg)) =
      [⟨reg, reg, .write true, .writeAck⟩, ⟨!reg, reg, .read, .readRet false⟩] := by
    rcases h6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h2 := hother 2 (by omega) (by omega) (by omega)
      have h3 := hother 3 (by omega) (by omega) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eB1 h2 h3
      simp only [List.filter, eA0, eB1, h2, h3, decide_true]
    · have h1 := hother 1 (by omega) (by omega) (by omega)
      have h3 := hother 3 (by omega) (by omega) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eB1 h1 h3
      simp only [List.filter, eA0, eB1, h1, h3, decide_true]
    · have h1 := hother 1 (by omega) (by omega) (by omega)
      have h2 := hother 2 (by omega) (by omega) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eB1 h1 h2
      simp only [List.filter, eA0, eB1, h1, h2, decide_true]
    · have h0 := hother 0 (by omega) (by omega) (by omega)
      have h3 := hother 3 (by omega) (by omega) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eB1 h0 h3
      simp only [List.filter, eA0, eB1, h0, h3, decide_true]
    · have h0 := hother 0 (by omega) (by omega) (by omega)
      have h2 := hother 2 (by omega) (by omega) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eB1 h0 h2
      simp only [List.filter, eA0, eB1, h0, h2, decide_true]
    · have h0 := hother 0 (by omega) (by omega) (by omega)
      have h1 := hother 1 (by omega) (by omega) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eB1 h0 h1
      simp only [List.filter, eA0, eB1, h0, h1, decide_true]
  rw [hfil] at hleg
  simp only [List.flatMap_cons, List.flatMap_nil, OpCall.toEvents, List.cons_append,
    List.nil_append, SeqSpec.evalMachine, registerStep] at hleg
  obtain ⟨_, _, _, _, _, _, _, hbad, _⟩ := hleg
  nomatch hbad

/-- Original explicit 2-process, 1-register history that is **sequentially consistent** (`B`'s
`read false` can be ordered before `A`'s `write true`) yet **not linearizable** (`A`'s `write true`
completed in real time before `B`'s `read false` was invoked), witnessing the single-object
separation of [HerlihyWing1990], §3.3, p. 472 (register counterpart of queue history `H_7`). -/
theorem exists_sequentiallyConsistent_not_linearizable :
    ∃ H : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool),
      History.WellFormed H ∧
      IsSequentiallyConsistent (fun x => registerSeqSpec x false) H ∧
      ¬ IsLinearizable (fun x => registerSeqSpec x false) H := by
  let H : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool) :=
    [.inv false () (.write true), .resp false () .writeAck,
     .inv true () .read, .resp true () (.readRet false)]
  have hwfH : History.WellFormed H := fun b => by cases b <;> trivial
  refine ⟨H, hwfH, ?_, ?_⟩
  · let S : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool) :=
      [.inv true () .read, .resp true () (.readRet false),
       .inv false () (.write true), .resp false () .writeAck]
    refine ⟨H, History.IsExtension.refl hwfH, S, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_⟩
    · intro x; cases x
      unfold registerSeqSpec; rw [SeqSpec.mem_ofMachine_allowed]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
    · intro b; cases b <;> rfl
  · rintro ⟨H', ⟨R, hrespR, rfl, hwf'⟩, S, hseqS, hlegS, heqS, hprecS⟩
    have hR_nil : R = [] :=
      resp_ext_eq_nil_of_even_proc hwfH (fun b => by cases b <;> decide) hrespR hwf'
    subst hR_nil
    rw [List.append_nil] at hwf' heqS hprecS
    have hpr_S := hprecS ⟨false, 0⟩ ⟨true, 0⟩ rfl rfl ⟨1, 2, rfl, rfl, by omega⟩
    have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
    obtain ⟨cs, rfl⟩ := History.exists_calls_of_isSequential_even hseqS hevS
    have hlen_cs : cs.length = 2 := by
      have hf := congrArg List.length (heqS false)
      have ht := congrArg List.length (heqS true)
      rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at hf ht
      have hp_sum := filter_proc_bool_length_sum cs
      have hf_val : (History.procSubhistory (History.complete H) false).length = 2 := rfl
      have ht_val : (History.procSubhistory (History.complete H) true).length = 2 := rfl
      rw [hf_val] at hf; rw [ht_val] at ht
      omega
    match cs, hlen_cs with
    | [c₀, c₁], _ =>
      have hleg0 := hlegS ()
      rw [History.objSubhistory_eq_self_of_forall_obj (fun _ _ => rfl)] at hleg0
      unfold registerSeqSpec at hleg0
      rw [SeqSpec.mem_ofMachine_allowed] at hleg0
      cases hp₀ : c₀.proc
      · cases hp₁ : c₁.proc
        · have ht := heqS true
          simp only [History.procSubhistory_flatMap_toEvents, List.filter, hp₀, hp₁,
            Bool.false_eq_true, decide_false, List.flatMap_nil] at ht
          nomatch ht
        · have hf_eq := heqS false
          have ht_eq := heqS true
          have hf_comp :
              History.procSubhistory (History.complete H) false =
                ([⟨false, (), .write true, .writeAck⟩] :
                  List (OpCall Bool (fun _ : Unit => RegOp Bool)
                    (fun _ : Unit => RegResp Bool))).flatMap OpCall.toEvents := rfl
          have ht_comp :
              History.procSubhistory (History.complete H) true =
                ([⟨true, (), .read, .readRet false⟩] :
                  List (OpCall Bool (fun _ : Unit => RegOp Bool)
                    (fun _ : Unit => RegResp Bool))).flatMap OpCall.toEvents := rfl
          rw [hf_comp, History.procSubhistory_flatMap_toEvents] at hf_eq
          rw [ht_comp, History.procSubhistory_flatMap_toEvents] at ht_eq
          simp only [List.filter, hp₀, hp₁, decide_true, Bool.true_eq_false,
            Bool.false_eq_true, decide_false] at hf_eq ht_eq
          have hc₀_eq := flatMap_toEvents_injective hf_eq
          have hc₁_eq := flatMap_toEvents_injective ht_eq
          injection hc₀_eq with hc₀_val
          injection hc₁_eq with hc₁_val
          rw [← hc₀_val, ← hc₁_val] at hleg0
          simp only [List.flatMap_cons, List.flatMap_nil, OpCall.toEvents, List.cons_append,
            List.nil_append, SeqSpec.evalMachine, registerStep] at hleg0
          obtain ⟨_, _, _, _, _, _, _, hbad, _⟩ := hleg0
          nomatch hbad
      · cases hp₁ : c₁.proc
        · obtain ⟨r, i, hr, hi, hlt⟩ := hpr_S
          simp only [History.respPos, History.invPos, List.flatMap_cons, List.flatMap_nil,
            OpCall.toEvents, List.cons_append, List.nil_append, History.nthProcPos,
            List.nthFilterPos, Event.proc_inv, Event.proc_resp, hp₀, hp₁, Nat.mul_zero,
            Nat.zero_add, decide_true, decide_false, Bool.true_eq_false, ↓reduceIte,
            Option.map_some, Option.some.injEq] at hr hi
          omega
        · have hf := heqS false
          simp only [History.procSubhistory_flatMap_toEvents, List.filter, hp₀, hp₁,
            Bool.true_eq_false, decide_false, List.flatMap_nil] at hf
          nomatch hf

/-- Original explicit 2-process, 2-register **non-locality of sequential consistency** witness
(register counterpart of two-queue history `H_8` in [HerlihyWing1990], §3.3, p. 472): there exists a
well-formed 2-process (`Bool`), 2-register (`Bool`, both initialized to `false`) history `H` such
that `History.objSubhistory H false` and `History.objSubhistory H true` are each sequentially
consistent, yet `H` itself is **not** sequentially consistent. -/
theorem exists_obj_sequentiallyConsistent_not_global :
    ∃ H : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool),
      History.WellFormed H ∧
      (∀ x : Bool, IsSequentiallyConsistent (fun y => registerSeqSpec y false)
        (History.objSubhistory H x)) ∧
      ¬ IsSequentiallyConsistent (fun y => registerSeqSpec y false) H := by
  let H : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool) :=
    [.inv false false (.write true), .resp false false .writeAck,
     .inv true true (.write true), .resp true true .writeAck,
     .inv false true .read, .resp false true (.readRet false),
     .inv true false .read, .resp true false (.readRet false)]
  have hwfH : History.WellFormed H := fun p => by cases p <;> trivial
  refine ⟨H, hwfH, ?_, ?_⟩
  · intro x
    let Sx : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool) :=
      [.inv (!x) x .read, .resp (!x) x (.readRet false),
       .inv x x (.write true), .resp x x .writeAck]
    refine ⟨History.objSubhistory H x, History.IsExtension.refl (hwfH.objSubhistory x),
      Sx, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_⟩
    · intro y; cases x <;> cases y <;> (unfold registerSeqSpec; rw [SeqSpec.mem_ofMachine_allowed])
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
      · trivial
      · trivial
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
    · intro p; cases x <;> cases p <;> rfl
  · rintro ⟨H', ⟨R, hrespR, rfl, hwf'⟩, S, hseqS, hlegS, heqS⟩
    have hR_nil : R = [] :=
      resp_ext_eq_nil_of_even_proc hwfH (fun b => by cases b <;> decide) hrespR hwf'
    subst hR_nil
    rw [List.append_nil] at hwf' heqS
    have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
    obtain ⟨cs, rfl⟩ := History.exists_calls_of_isSequential_even hseqS hevS
    have hc_cnt : ∀ b : Bool, countProcCalls b cs = 2 := by
      intro b
      have hb := congrArg List.length (heqS b)
      rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at hb
      have hb_val : (History.procSubhistory (History.complete H) b).length = 4 := by
        cases b <;> rfl
      rw [hb_val] at hb
      dsimp only [countProcCalls]; omega
    have hcF0 := hc_cnt false
    have hcT0 := hc_cnt true
    obtain ⟨jF0, hjF0, hopF0⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨false, 0⟩
      (by dsimp only; omega)
    obtain ⟨jF1, hjF1, hopF1⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨false, 1⟩
      (by dsimp only; omega)
    obtain ⟨jT0, hjT0, hopT0⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨true, 0⟩
      (by dsimp only; omega)
    obtain ⟨jT1, hjT1, hopT1⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨true, 1⟩
      (by dsimp only; omega)
    have hcs_F : cs.filter (fun c => decide (c.proc = false)) =
        [⟨false, false, .write true, .writeAck⟩, ⟨false, true, .read, .readRet false⟩] :=
      flatMap_toEvents_injective
        (by rw [← History.procSubhistory_flatMap_toEvents, ← heqS false]; rfl)
    have hcs_T : cs.filter (fun c => decide (c.proc = true)) =
        [⟨true, true, .write true, .writeAck⟩, ⟨true, false, .read, .readRet false⟩] :=
      flatMap_toEvents_injective
        (by rw [← History.procSubhistory_flatMap_toEvents, ← heqS true]; rfl)
    have hc_S : ∀ b i, i < 2 → History.IsCompletedOp (cs.flatMap OpCall.toEvents) ⟨b, i⟩ := by
      intro b i hi
      rw [History.isCompletedOp_iff_lt_length, History.procSubhistory_flatMap_toEvents,
        History.length_flatMap_toEvents]
      have hb := hc_cnt b
      dsimp only [countProcCalls] at hb ⊢
      omega
    have hj_ord : ∀ b {j0 j1} (hj0 : j0 < cs.length) (hj1 : j1 < cs.length),
        opIdAt cs j0 hj0 = ⟨b, 0⟩ → opIdAt cs j1 hj1 = ⟨b, 1⟩ → j0 < j1 := by
      intro b j0 j1 hj0 hj1 hop0 hop1
      have hpr := History.prec_of_same_proc_lt (e₀ := ⟨b, 0⟩) (e₁ := ⟨b, 1⟩) rfl
        (by dsimp only; omega) (hc_S b 0 (by omega)) (hc_S b 1 (by omega))
      rw [← hop0, ← hop1] at hpr
      exact (prec_flatMap_toEvents_opIdAt_iff cs hj0 hj1).mp hpr
    have hjF_lt := hj_ord false hjF0 hjF1 hopF0 hopF1
    have hjT_lt := hj_ord true hjT0 hjT1 hopT0 hopT1
    have hval_at : ∀ (j : ℕ) (hj : j < cs.length) (b : Bool) (idx : ℕ),
        opIdAt cs j hj = ⟨b, idx⟩ →
          ∃ hlt : idx < (cs.filter fun c => decide (c.proc = b)).length,
            (cs.filter fun c => decide (c.proc = b))[idx]'hlt = cs[j] := by
      intro j hj b idx hop
      have hpb : cs[j].proc = b := congrArg OpId.proc hop
      have hidx : countProcCalls b (cs.take j) = idx := by
        have := congrArg OpId.idx hop
        simpa only [opIdAt, hpb] using this
      obtain ⟨hlt, hget⟩ := List.filter_getElem_count_take (fun c => decide (c.proc = b)) cs j hj
        (decide_eq_true hpb)
      dsimp only [countProcCalls] at hidx
      subst hidx
      exact ⟨hlt, hget⟩
    obtain ⟨_, hgetF0⟩ := hval_at jF0 hjF0 false 0 hopF0
    obtain ⟨_, hgetF1⟩ := hval_at jF1 hjF1 false 1 hopF1
    obtain ⟨_, hgetT0⟩ := hval_at jT0 hjT0 true 0 hopT0
    obtain ⟨_, hgetT1⟩ := hval_at jT1 hjT1 true 1 hopT1
    simp only [hcs_F, List.getElem_cons_zero, List.getElem_cons_succ] at hgetF0 hgetF1
    simp only [hcs_T, List.getElem_cons_zero, List.getElem_cons_succ] at hgetT0 hgetT1
    have hlen_cs4 : cs.length = 4 := by
      have h := filter_proc_bool_length_sum cs
      dsimp only [countProcCalls] at hcF0 hcT0
      omega
    obtain ⟨c0, c1, c2, c3, rfl⟩ : ∃ c0 c1 c2 c3, cs = [c0, c1, c2, c3] := by
      match cs, hlen_cs4 with
      | [c0, c1, c2, c3], _ => exact ⟨c0, c1, c2, c3, rfl⟩
    have hne_FT00 : jF0 ≠ jT0 := fun h => by subst h; rw [hopF0] at hopT0; nomatch hopT0
    have hne_FT01 : jF0 ≠ jT1 := fun h => by subst h; rw [hopF0] at hopT1; nomatch hopT1
    have hne_FT10 : jF1 ≠ jT0 := fun h => by subst h; rw [hopF1] at hopT0; nomatch hopT0
    have hne_FT11 : jF1 ≠ jT1 := fun h => by subst h; rw [hopF1] at hopT1; nomatch hopT1
    simp only [List.length_cons, List.length_nil] at hjF0 hjF1 hjT0 hjT1
    have hnot_F0_lt_T1 : ¬ jF0 < jT1 :=
      dekker_write_not_lt_stale_read false (hlegS false) hjF0 hjF1 hjT0 hjT1 hjF_lt hjT_lt
        hne_FT00 hne_FT01 hne_FT10 hne_FT11 hgetF0.symm hgetF1.symm hgetT0.symm hgetT1.symm
    have hnot_T0_lt_F1 : ¬ jT0 < jF1 :=
      dekker_write_not_lt_stale_read true (hlegS true) hjT0 hjT1 hjF0 hjF1 hjT_lt hjF_lt
        hne_FT00.symm hne_FT10.symm hne_FT01.symm hne_FT11.symm
        hgetT0.symm hgetT1.symm hgetF0.symm hgetF1.symm
    omega

end Cslib.Distributed.ConcurrentObjects
