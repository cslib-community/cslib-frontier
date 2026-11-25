/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterEncoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.StepPolyTime
import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD

/-!
# Constraint logic as a guarded register program

The registers store the edge directions of an AND/OR constraint graph. At its hub the program
can reverse one edge and enter a shared read-only check of all vertices. A complete return to
the hub therefore performs one legal constraint-logic move. A second read-only branch accepts
exactly the requested target configuration. The construction allows loops and parallel edges.

This reduction is an original implementation of the standard configuration-graph simulation.
Its source is the explicit AND/OR NCL language of [HearnDemaine2005, Sections 2.1–2.2].

## Main definitions

* `Cslib.Complexity.SelfClosingDoor.RegisterProgram.NCLCompiler.compile`: the total compiler.

## Main results

* `Cslib.Complexity.SelfClosingDoor.RegisterProgram.NCLCompiler.compile_accepts_iff`:
  register-program acceptance is equivalent to the source configuration reachability problem.
* `Cslib.Complexity.SelfClosingDoor.RegisterProgram.NCLCompiler.computableInPolyTime_compile`:
  the total compiler is polynomial-time for the explicit binary NCL encoding.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram.NCLCompiler

open NCL

private abbrev Input := AndOrNCL.Instance

private def check (v : ℕ) : ℕ := 2 + v

private def target (x : Input) (i : ℕ) : ℕ := 3 + x.graph.vertices.length + i

private def middle (x : Input) (v k p : ℕ) : ℕ :=
  4 + x.graph.vertices.length + x.initial.length + 16 * v + 2 * k + p

private def test (a b r : ℕ) (v : Bool) : Instruction := ⟨a, b, r, v, v⟩

private def pattern (k : ℕ) : List Bool :=
  [decide (k % 2 = 1), decide (k / 2 % 2 = 1), decide (k / 4 % 2 = 1)]

private def defaultPort : WeightedPort ℕ := ⟨⟨0, false⟩, 0⟩

private def port (v : Vertex ℕ) (i : ℕ) : WeightedPort ℕ := v.ports.getD i defaultPort

private def localVertex (v : Vertex ℕ) : Vertex ℕ :=
  ⟨v.ports.zipIdx.map (fun (p, i) => ⟨⟨i, p.port.dir⟩, p.weight⟩), v.minInflow⟩

private def branchInstruction (x : Input) (v k : ℕ) (a : Vertex ℕ) (p : ℕ) : Instruction :=
  test (if p = 0 then check v else middle x v k (p - 1))
    (if p = 2 then check (v + 1) else middle x v k p)
    (port a p).port.edge ((pattern k).getD p false)

private def branch (x : Input) (v k : ℕ) (a : Vertex ℕ) : List Instruction :=
  if (localVertex a).checkSat (pattern k) then
    (List.range 3).map (branchInstruction x v k a)
  else []

private def flips (x : Input) : List Instruction :=
  (List.range x.initial.length).flatMap fun i =>
    [⟨0, check 0, i, false, true⟩, ⟨0, check 0, i, true, false⟩]

private def checks (x : Input) : List Instruction :=
  x.graph.vertices.zipIdx.flatMap fun (a, v) =>
    (List.range 8).flatMap fun k => branch x v k a

private def targetTests (x : Input) : List Instruction :=
  x.target.zipIdx.map fun (b, i) => test (target x i) (target x (i + 1)) i b

private def raw (x : Input) : Program where
  instructions := flips x ++ checks x ++ targetTests x
  jumps := [⟨check x.graph.vertices.length, 0⟩, ⟨0, target x 0⟩,
    ⟨target x x.target.length, 1⟩]
  initial := x.initial
  start := 0
  target := 1

private def guard (x : Input) : Bool :=
  x.graph.checkValid && decide (x.initial.length = x.graph.edgeCount) &&
    decide (x.target.length = x.graph.edgeCount) && x.graph.checkLegal x.initial

private def reject : Program := ⟨[], [], [], 0, 1⟩

/-- Compile explicit AND/OR NCL data to a finite register program, rejecting malformed inputs. -/
def compile (x : AndOrNCL.Instance) : Program :=
  if guard x then raw x else reject

private theorem guard_spec (x : Input) : guard x = true ↔
    x.graph.Valid ∧ x.initial.length = x.graph.edgeCount ∧
      x.target.length = x.graph.edgeCount ∧
      x.graph.graph.Legal (x.graph.config x.initial) := by
  simp only [guard, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨⟨hv, hs⟩, ht⟩, hl⟩ =>
    have hv := (AndOrGraph.checkValid_eq_true_iff x.graph).1 hv
    ⟨hv, hs, ht, (x.graph.checkLegal_eq_true_iff hv.1 x.initial).1 hl⟩,
    fun ⟨hv, hs, ht, hl⟩ => ⟨⟨⟨(AndOrGraph.checkValid_eq_true_iff _).2 hv, hs⟩, ht⟩,
      (x.graph.checkLegal_eq_true_iff hv.1 x.initial).2 hl⟩⟩

private theorem vertex_shape {x : Input} (hx : x.graph.Valid) {a : Vertex ℕ}
    (ha : a ∈ x.graph.vertices) : a.ports.length = 3 :=
  ((Vertex.checkAndOr_eq_true_iff a).1
    (List.all_eq_true.1 ((x.graph.checkVertices_eq_true_iff hx.1).2 hx.2.1) a ha)).shape.1

private theorem port_bound {x : Input} (hx : x.graph.Valid) {a : Vertex ℕ}
    (ha : a ∈ x.graph.vertices) {i : ℕ} (hi : i < 3) :
    (port a i).port.edge < x.graph.edgeCount :=
  hx.1 a ha (port a i) <| by
    rw [port, List.getD_eq_getElem _ _ (by rw [vertex_shape hx ha]; exact hi)]
    exact List.getElem_mem _

private theorem pattern_exists (a b c : Bool) :
    ∃ k < 8, pattern k = [a, b, c] := by
  refine ⟨(if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0), ?_, ?_⟩
  all_goals cases a <;> cases b <;> cases c <;> decide +kernel

private theorem local_check {a : Vertex ℕ} (ha : a.ports.length = 3)
    (s u : List Bool)
    (h0 : s.getD (port a 0).port.edge false = u.getD 0 false)
    (h1 : s.getD (port a 1).port.edge false = u.getD 1 false)
    (h2 : s.getD (port a 2).port.edge false = u.getD 2 false) :
    (localVertex a).checkSat u = a.checkSat s := by
  obtain ⟨p, q, r, hp⟩ := List.length_eq_three.1 ha
  simp only [port, hp, List.getD] at h0 h1 h2
  simp [localVertex, hp, Vertex.checkSat, Vertex.Sat, Vertex.inflow, Port.In, ← h0, ← h1, ← h2]

private theorem set_read (s : List Bool) (i : ℕ) (b : Bool) (hi : i < s.length)
    (hb : s.getD i false = b) : s.set i b = s := by
  rw [← hb, List.getD_eq_getElem _ _ hi]; exact List.set_getElem_self hi

private theorem test_step {p : Program} {a b r : ℕ} {v : Bool} {s : List Bool}
    (hi : test a b r v ∈ p.instructions) (hs : s.length = p.initial.length)
    (hr : r < s.length) (hv : s.getD r false = v) :
    p.Step ⟨a, s⟩ ⟨b, s⟩ :=
  ⟨hs, Or.inr ⟨test a b r v, hi, hr, rfl, hv, by simp only [test, set_read s r v hr hv]⟩⟩

private theorem jump_step {p : Program} {a b : ℕ} {s : List Bool}
    (hi : (⟨a, b⟩ : Tunnel) ∈ p.jumps) (hs : s.length = p.initial.length) :
    p.Step ⟨a, s⟩ ⟨b, s⟩ :=
  ⟨hs, Or.inl ⟨⟨a, b⟩, hi, rfl, rfl⟩⟩

private def vertex (x : Input) (v : ℕ) : Vertex ℕ :=
  x.graph.vertices.getD v ⟨[], 0⟩

private def Origin (x : Input) (s : List Bool) : Prop :=
  x.graph.graph.Reachable (x.graph.config x.initial) (x.graph.config s)

private def Candidate (x : Input) (s : List Bool) : Prop :=
  ∃ before e, before.length = x.initial.length ∧ Origin x before ∧
    e < x.initial.length ∧ s = before.modify e Bool.not

private def Passed (x : Input) (s : List Bool) (v : ℕ) : Prop :=
  ∀ j < v, (vertex x j).checkSat s = true

private def Matched (x : Input) (s : List Bool) (v k p : ℕ) : Prop :=
  ∀ j ≤ p, s.getD (port (vertex x v) j).port.edge false = (pattern k).getD j false

private def TargetPrefix (x : Input) (s : List Bool) (i : ℕ) : Prop :=
  ∀ j < i, s.getD j false = x.target.getD j false

private def Good (x : Input) (s : State) : Prop :=
  s.bits.length = x.initial.length ∧
    ((s.location = 0 ∧ Origin x s.bits) ∨
      (∃ v, v ≤ x.graph.vertices.length ∧ s.location = check v ∧
        Candidate x s.bits ∧ Passed x s.bits v) ∨
      (∃ v k p, v < x.graph.vertices.length ∧ k < 8 ∧ p < 2 ∧
        s.location = middle x v k p ∧ Candidate x s.bits ∧ Passed x s.bits v ∧
        (localVertex (vertex x v)).checkSat (pattern k) = true ∧ Matched x s.bits v k p) ∨
      (∃ i, i ≤ x.initial.length ∧ s.location = target x i ∧ Origin x s.bits ∧
        TargetPrefix x s.bits i) ∨
      (s.location = 1 ∧ Origin x s.bits ∧ s.bits = x.target))

private theorem good_hub {x : Input} {s : State} (hg : Good x s)
    (hl : s.location = 0) : Origin x s.bits := by
  rcases hg.2 with ⟨_, h⟩ | ⟨v, hv, he, _⟩ |
    ⟨v, k, p, hv, hk, hp, he, _⟩ | ⟨i, hi, he, _⟩ | ⟨he, _⟩
  · exact h
  all_goals first | omega | (simp only [check, target, middle] at he; omega)

private theorem good_check {x : Input} {s : State} (hg : Good x s)
    {v : ℕ} (hv : v ≤ x.graph.vertices.length) (hl : s.location = check v) :
    Candidate x s.bits ∧ Passed x s.bits v := by
  rcases hg.2 with ⟨he, _⟩ | ⟨w, hw, he, hc, hp⟩ |
    ⟨w, k, p, hw, hk, hp, he, _⟩ | ⟨i, hi, he, _⟩ | ⟨he, _⟩
  · simp only [check] at hl; omega
  · exact (show w = v by simp only [check] at he hl; omega) ▸ ⟨hc, hp⟩
  all_goals simp only [check, target, middle] at he hl; omega

private theorem good_middle {x : Input} {s : State} (hg : Good x s)
    {v k p : ℕ} (hv : v < x.graph.vertices.length) (hk : k < 8) (hp : p < 2)
    (hl : s.location = middle x v k p) :
    Candidate x s.bits ∧ Passed x s.bits v ∧
      (localVertex (vertex x v)).checkSat (pattern k) = true ∧ Matched x s.bits v k p := by
  rcases hg.2 with ⟨he, _⟩ | ⟨w, hw, he, _⟩ |
    ⟨w, l, q, hw, hq, hlq, he, hc, hpassed, hsat, hm⟩ | ⟨i, hi, he, _⟩ | ⟨he, _⟩
  · simp only [middle] at hl; omega
  · simp only [check, middle] at he hl; omega
  · simp only [middle] at he hl
    obtain ⟨rfl, rfl, rfl⟩ : w = v ∧ l = k ∧ q = p := ⟨by omega, by omega, by omega⟩
    exact ⟨hc, hpassed, hsat, hm⟩
  all_goals simp only [target, middle] at he hl; omega

private theorem good_target {x : Input} {s : State} (hg : Good x s)
    {i : ℕ} (hi : i ≤ x.initial.length) (hl : s.location = target x i) :
    Origin x s.bits ∧ TargetPrefix x s.bits i := by
  rcases hg.2 with ⟨he, _⟩ | ⟨w, hw, he, _⟩ |
    ⟨w, k, p, hw, hk, hp, he, _⟩ | ⟨j, hj, he, hr, hm⟩ | ⟨he, _⟩
  · simp only [target] at hl; omega
  · simp only [check, target] at he hl; omega
  · simp only [target, middle] at he hl; omega
  · exact (show j = i by simp only [target] at he hl; omega) ▸ ⟨hr, hm⟩
  · simp only [target] at hl; omega

private theorem good_accept {x : Input} {s : State} (hg : Good x s)
    (hl : s.location = 1) : Origin x x.target := by
  rcases hg.2 with ⟨he, _⟩ | ⟨w, hw, he, _⟩ |
    ⟨w, k, p, hw, hk, hp, he, _⟩ | ⟨j, hj, he, _⟩ | ⟨_, hr, hm⟩
  any_goals first | omega | (simp only [check, target, middle] at he; omega)
  exact hm ▸ hr

private theorem vertex_mem {x : Input} {v : ℕ} (hv : v < x.graph.vertices.length) :
    vertex x v ∈ x.graph.vertices := by
  rw [vertex, List.getD_eq_getElem _ _ hv]; exact List.getElem_mem _

private theorem vertex_of_zipIdx {x : Input} {a : Vertex ℕ} {v : ℕ}
    (ha : (a, v) ∈ x.graph.vertices.zipIdx) :
    v < x.graph.vertices.length ∧ a = vertex x v := by
  obtain ⟨hv, he⟩ := List.mem_zipIdx' ha
  exact ⟨hv, he.trans (List.getD_eq_getElem _ _ hv).symm⟩

private theorem passed_legal {x : Input} (hx : x.graph.Valid) {s : List Bool}
    (hp : Passed x s x.graph.vertices.length) :
    x.graph.graph.Legal (x.graph.config s) := by
  rw [← x.graph.checkLegal_eq_true_iff hx.1 s, AndOrGraph.checkLegal, List.all_eq_true,
    List.forall_mem_iff_getElem]
  exact fun j hj => by simpa only [vertex, List.getD_eq_getElem _ _ hj] using hp j hj

private theorem candidate_origin {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount)
    (hinitial : x.graph.graph.Legal (x.graph.config x.initial)) {s : List Bool}
    (hc : Candidate x s) (hp : Passed x s x.graph.vertices.length) : Origin x s := by
  obtain ⟨before, e, hb, hr, he, rfl⟩ := hc
  let edge : Fin x.graph.edgeCount := ⟨e, by omega⟩
  exact hr.tail ⟨hr.legal hinitial, passed_legal hx hp, edge,
    x.graph.config_modify_not before (hb.trans hlen) edge⟩

private theorem test_step_iff (a b r : ℕ) (v : Bool) (s t : State) :
    (test a b r v).Step s t ↔ r < s.bits.length ∧ s.location = a ∧
      s.bits.getD r false = v ∧ t = ⟨b, s.bits⟩ :=
  ⟨fun ⟨hr, hl, hv, h⟩ =>
      ⟨hr, hl, hv, h.trans (congrArg (State.mk b) (set_read s.bits r v hr hv))⟩,
    fun ⟨hr, hl, hv, h⟩ =>
      ⟨hr, hl, hv, h.trans (congrArg (State.mk b) (set_read s.bits r v hr hv).symm)⟩⟩

private theorem mem_flips {x : Input} {i : Instruction} (hi : i ∈ flips x) :
    ∃ e b, e < x.initial.length ∧ i = ⟨0, check 0, e, b, !b⟩ := by
  obtain ⟨e, he, hi⟩ := List.mem_flatMap.1 hi
  rcases (by simpa using hi : i = _ ∨ i = _) with rfl | rfl
  · exact ⟨e, false, List.mem_range.1 he, rfl⟩
  · exact ⟨e, true, List.mem_range.1 he, rfl⟩

private theorem mem_checks {x : Input} {i : Instruction} (hi : i ∈ checks x) :
    ∃ v k p, v < x.graph.vertices.length ∧ k < 8 ∧ p < 3 ∧
      (localVertex (vertex x v)).checkSat (pattern k) = true ∧
      i = branchInstruction x v k (vertex x v) p := by
  obtain ⟨⟨a, v⟩, ha, hi⟩ := List.mem_flatMap.1 hi
  obtain ⟨hv, rfl⟩ := vertex_of_zipIdx ha
  obtain ⟨k, hk, hi⟩ := List.mem_flatMap.1 hi
  rw [branch] at hi; split_ifs at hi with hsat
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact ⟨v, k, p, hv, List.mem_range.1 hk, List.mem_range.1 hp, hsat, rfl⟩
  · cases hi

private theorem branch_good {x : Input} (hx : x.graph.Valid) {v k p : ℕ}
    (hv : v < x.graph.vertices.length) (hk : k < 8) (hp : p < 3)
    (hsat : (localVertex (vertex x v)).checkSat (pattern k) = true)
    {s t : State} (hg : Good x s)
    (hstep : (branchInstruction x v k (vertex x v) p).Step s t) : Good x t := by
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 by omega) with rfl | rfl | rfl <;>
    simp only [branchInstruction, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, test_step_iff]
      at hstep <;>
    obtain ⟨_, hl, hb, rfl⟩ := hstep
  · obtain ⟨hc, hpassed⟩ := good_check hg hv.le hl
    exact ⟨hg.1, Or.inr <| Or.inr <| Or.inl ⟨v, k, 0, hv, hk, by omega, rfl, hc, hpassed, hsat,
      fun j hj => (show j = 0 by omega) ▸ hb⟩⟩
  · obtain ⟨hc, hpassed, _, hm⟩ := good_middle hg hv hk (by omega : 0 < 2) hl
    refine ⟨hg.1, Or.inr <| Or.inr <| Or.inl ⟨v, k, 1, hv, hk, by omega, rfl, hc, hpassed, hsat,
      fun j hj => ?_⟩⟩
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl; exacts [hm 0 (by omega), hb]
  · obtain ⟨hc, hpassed, _, hm⟩ := good_middle hg hv hk (by omega : 1 < 2) hl
    have hchecked := (local_check (vertex_shape hx (vertex_mem hv)) s.bits (pattern k)
      (hm 0 (by omega)) (hm 1 (by omega)) hb).symm.trans hsat
    exact ⟨hg.1, Or.inr <| Or.inl ⟨v + 1, by omega, rfl, hc, fun j hj =>
      if he : j = v then he ▸ hchecked else hpassed j (by omega)⟩⟩

private theorem set_flip {s : List Bool} {e : ℕ} {b : Bool}
    (he : e < s.length) (hb : s.getD e false = b) :
    s.set e (!b) = s.modify e Bool.not := by
  have hget : s.get ⟨e, he⟩ = b := (List.getD_eq_get s false ⟨e, he⟩).symm.trans hb
  rw [List.modify_eq_set_get Bool.not he, hget]

private theorem flip_good {x : Input} {e : ℕ} {b : Bool}
    (he : e < x.initial.length) {s t : State} (hg : Good x s)
    (hstep : (⟨0, check 0, e, b, !b⟩ : Instruction).Step s t) : Good x t := by
  obtain ⟨hr, hl, hb, rfl⟩ := hstep
  rw [set_flip hr hb]
  exact ⟨by simpa only [List.length_modify] using hg.1, Or.inr <| Or.inl ⟨0, Nat.zero_le _, rfl,
    ⟨s.bits, e, hg.1, good_hub hg hl, he, rfl⟩, fun _ hj => by omega⟩⟩

private theorem target_good {x : Input} (ht : x.target.length = x.initial.length)
    {i : Instruction} (hi : i ∈ targetTests x) {s t : State} (hg : Good x s)
    (hstep : i.Step s t) : Good x t := by
  obtain ⟨⟨b, j⟩, hj, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hjm, hb⟩ := List.mem_zipIdx' hj
  obtain ⟨_, hl, hv, rfl⟩ := (test_step_iff ..).1 hstep
  obtain ⟨hr, hp⟩ := good_target hg (by omega) hl
  exact ⟨hg.1, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨j + 1, by omega, rfl, hr, fun k hk =>
    if he : k = j then he ▸ hv.trans (hb.trans (List.getD_eq_getElem _ _ hjm).symm)
    else hp k (by omega)⟩⟩

private theorem jump_good {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount)
    (ht : x.target.length = x.initial.length)
    (hinitial : x.graph.graph.Legal (x.graph.config x.initial))
    {s t : State} (hg : Good x s)
    (hstep : ∃ a ∈ (raw x).jumps, s.location = a.source ∧ t = ⟨a.target, s.bits⟩) :
    Good x t := by
  obtain ⟨a, ha, hl, rfl⟩ := hstep
  rcases (by simpa [raw] using ha : a = _ ∨ a = _ ∨ a = _) with rfl | rfl | rfl
  · obtain ⟨hc, hp⟩ := good_check hg le_rfl hl
    exact ⟨hg.1, Or.inl ⟨rfl, candidate_origin hx hlen hinitial hc hp⟩⟩
  · exact ⟨hg.1, Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨0, Nat.zero_le _, rfl, good_hub (s := s) hg hl, fun _ hj => by omega⟩⟩
  · obtain ⟨hr, hp⟩ := good_target hg (by omega) hl
    refine ⟨hg.1, Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨rfl, hr, List.ext_getElem (hg.1.trans ht.symm) fun j hs hj => ?_⟩⟩
    simpa only [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ hj] using hp j hj

private theorem step_good {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount)
    (ht : x.target.length = x.initial.length)
    (hinitial : x.graph.graph.Legal (x.graph.config x.initial))
    {s t : State} (hg : Good x s) (hstep : (raw x).Step s t) : Good x t := by
  rcases hstep with ⟨_, hj | ⟨i, hi, hs⟩⟩
  · exact jump_good hx hlen ht hinitial hg hj
  · simp only [raw, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · obtain ⟨e, b, he, rfl⟩ := mem_flips hi; exact flip_good he hg hs
    · obtain ⟨v, k, p, hv, hk, hp, hsat, rfl⟩ := mem_checks hi
      exact branch_good hx hv hk hp hsat hg hs
    · exact target_good ht hi hg hs

private theorem raw_sound {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount)
    (ht : x.target.length = x.graph.edgeCount)
    (hinitial : x.graph.graph.Legal (x.graph.config x.initial))
    (h : (raw x).Accepts) : Origin x x.target := by
  obtain ⟨t, hrun, htarget⟩ := h
  have hgood : Good x t := by
    clear htarget
    induction hrun with
    | refl => exact ⟨rfl, Or.inl ⟨rfl, .refl⟩⟩
    | tail _ hm ih => exact step_good hx hlen (ht.trans hlen.symm) hinitial ih hm
  exact good_accept hgood htarget

private theorem branch_mem {x : Input} {v k p : ℕ}
    (hv : v < x.graph.vertices.length) (hk : k < 8) (hp : p < 3)
    (hsat : (localVertex (vertex x v)).checkSat (pattern k) = true) :
    branchInstruction x v k (vertex x v) p ∈ (raw x).instructions := by
  simp only [raw, List.mem_append]
  refine Or.inl <| Or.inr <| List.mem_flatMap.2 ⟨(vertex x v, v),
    List.mem_zipIdx_iff_getElem?.2 (by simp [vertex, hv]),
    List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩
  rw [branch, hsat]
  exact List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩

private theorem flip_mem {x : Input} {e : ℕ} (he : e < x.initial.length) (b : Bool) :
    (⟨0, check 0, e, b, !b⟩ : Instruction) ∈ (raw x).instructions := by
  simp only [raw, List.mem_append]
  exact Or.inl <| Or.inl <| List.mem_flatMap.2 ⟨e, List.mem_range.2 he, by cases b <;> simp⟩

private theorem run_vertex {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount) {s : List Bool}
    (hs : s.length = x.initial.length) {v : ℕ} (hv : v < x.graph.vertices.length)
    (hlegal : (vertex x v).checkSat s = true) :
    (raw x).Reachable ⟨check v, s⟩ ⟨check (v + 1), s⟩ := by
  obtain ⟨k, hk, hpattern⟩ := pattern_exists
    (s.getD (port (vertex x v) 0).port.edge false)
    (s.getD (port (vertex x v) 1).port.edge false)
    (s.getD (port (vertex x v) 2).port.edge false)
  have hm (j : ℕ) (hj : j < 3) :
      s.getD (port (vertex x v) j).port.edge false = (pattern k).getD j false := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp [hpattern]
  have hsat := (local_check (vertex_shape hx (vertex_mem hv)) s (pattern k)
    (hm 0 (by omega)) (hm 1 (by omega)) (hm 2 (by omega))).trans hlegal
  have hstep (p a b : ℕ) (hp : p < 3)
      (hi : branchInstruction x v k (vertex x v) p =
        test a b (port (vertex x v) p).port.edge ((pattern k).getD p false)) :
      (raw x).Step ⟨a, s⟩ ⟨b, s⟩ :=
    test_step (hi ▸ branch_mem hv hk hp hsat) hs
      (by have := port_bound hx (vertex_mem hv) hp; omega) (hm p hp)
  exact ((Relation.ReflTransGen.single (hstep 0 (check v) (middle x v k 0) (by omega) rfl)).tail
    (hstep 1 (middle x v k 0) (middle x v k 1) (by omega) rfl)).tail
    (hstep 2 (middle x v k 1) (check (v + 1)) (by omega) rfl)

private theorem run_checks {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount) {s : List Bool}
    (hs : s.length = x.initial.length) (hlegal : x.graph.graph.Legal (x.graph.config s)) :
    (raw x).Reachable ⟨check 0, s⟩ ⟨check x.graph.vertices.length, s⟩ := by
  have hall := List.all_eq_true.1 ((x.graph.checkLegal_eq_true_iff hx.1 s).2 hlegal)
  suffices ∀ v ≤ x.graph.vertices.length, (raw x).Reachable ⟨check 0, s⟩ ⟨check v, s⟩ from
    this _ le_rfl
  intro v hv
  induction v with
  | zero => exact .refl
  | succ v ih =>
    exact (ih (by omega)).trans (run_vertex hx hlen hs (by omega) (hall _ (vertex_mem (by omega))))

private theorem run_source_step {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount) {s t : List Bool}
    (hs : s.length = x.initial.length) (ht : t.length = x.initial.length)
    (hstep : x.graph.graph.Step (x.graph.config s) (x.graph.config t)) :
    (raw x).Reachable ⟨0, s⟩ ⟨0, t⟩ := by
  have hc := (x.graph.checkStep_eq_true_iff hx.1 s t).2 ⟨hs.trans hlen, ht.trans hlen, hstep⟩
  simp only [AndOrGraph.checkStep, Bool.and_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨_, _, e, he, rfl⟩ := hc
  have hm : (raw x).Step ⟨0, s⟩ ⟨check 0, s.modify e Bool.not⟩ :=
    ⟨hs, Or.inr ⟨⟨0, check 0, e, s.getD e false, !(s.getD e false)⟩, flip_mem (by omega) _,
      he, rfl, rfl, congrArg (State.mk (check 0)) (set_flip he rfl).symm⟩⟩
  exact ((Relation.ReflTransGen.single hm).trans
    (run_checks hx hlen (by simpa only [List.length_modify] using hs) hstep.legal_right)).tail
    (jump_step (by simp [raw]) (by simpa only [raw, List.length_modify] using hs))

private theorem run_target {x : Input} (ht : x.target.length = x.initial.length) :
    (raw x).Reachable ⟨0, x.target⟩ ⟨1, x.target⟩ := by
  have hrun : ∀ i ≤ x.target.length,
      (raw x).Reachable ⟨target x 0, x.target⟩ ⟨target x i, x.target⟩ := by
    intro i hi
    induction i with
    | zero => exact .refl
    | succ i ih =>
      have hib : i < x.target.length := by omega
      refine (ih (by omega)).tail (test_step ?_ ht hib rfl)
      simp only [raw, List.mem_append]
      exact Or.inr <| List.mem_map.2 ⟨(x.target.getD i false, i),
        List.mem_zipIdx_iff_getElem?.2 (by simp [hib]), rfl⟩
  exact ((Relation.ReflTransGen.single
    (jump_step (by simp [raw]) ht)).trans (hrun _ le_rfl)).tail (jump_step (by simp [raw]) ht)

private theorem raw_complete {x : Input} (hx : x.graph.Valid)
    (hlen : x.initial.length = x.graph.edgeCount)
    (ht : x.target.length = x.graph.edgeCount) (hr : Origin x x.target) : (raw x).Accepts := by
  have hrun : (raw x).Reachable ⟨0, x.initial⟩ ⟨0, x.target⟩ := by
    have hsim {a b : Fin x.graph.edgeCount → Bool} (h : x.graph.graph.Reachable a b) :
        (raw x).Reachable ⟨0, List.ofFn a⟩ ⟨0, List.ofFn b⟩ := by
      induction h with
      | refl => exact .refl
      | tail _ hm ih =>
        exact ih.trans (run_source_step hx hlen
          (by simpa only [List.length_ofFn] using hlen.symm)
          (by simpa only [List.length_ofFn] using hlen.symm)
          (by simpa only [AndOrGraph.config_ofFn] using hm))
    simpa only [AndOrGraph.ofFn_config _ _ hlen, AndOrGraph.ofFn_config _ _ ht] using hsim hr
  exact ⟨⟨1, x.target⟩, hrun.trans (run_target (ht.trans hlen.symm)), rfl⟩

private theorem reject_not_accepts : ¬ reject.Accepts := by
  rintro ⟨t, hrun, ht⟩
  cases hrun with
  | refl => simp [reject, Program.initialState] at ht
  | tail _ hm => simp [Program.Step, reject] at hm

/-- The compiled finite register program accepts exactly the valid NCL source instances. -/
theorem compile_accepts_iff (x : AndOrNCL.Instance) :
    (compile x).Accepts ↔ x ∈ AndOrNCL := by
  by_cases hg : guard x = true
  · rw [compile, ite_eq_left hg]
    obtain ⟨hv, hs, ht, hl⟩ := (guard_spec x).1 hg
    exact ⟨fun hr => ⟨hv, hs, ht, hl, raw_sound hv hs ht hl hr⟩,
      fun ⟨_, _, _, _, hr⟩ => raw_complete hv hs ht hr⟩
  · rw [compile, ite_eq_right hg]
    exact ⟨fun hr => (reject_not_accepts hr).elim,
      fun hx => (hg ((guard_spec x).2 ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩)).elim⟩

open _root_.Turing.MultiTapeTM

/-- A source paired with a vertex and its unary position, framing each first component. -/
private abbrev encEmission := encPair encAndOrNCL (encPair (encVertex encNat) encUnary)

@[fun_prop] private theorem check_polyTime {α : Type} {enc : α ↪ List Bool}
    {v : α → ℕ} (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun a => check (v a)) enc encNat := by
  unfold check; fun_prop

@[fun_prop] private theorem target_polyTime {α : Type} {enc : α ↪ List Bool}
    {x : α → Input} {i : α → ℕ}
    (hx : ComputableInPolyTime x enc encAndOrNCL)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => target (x a) (i a)) enc encNat := by
  have hn : ComputableInPolyTime (fun a => (x a).graph.vertices.length) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold target; fun_prop

@[fun_prop] private theorem middle_polyTime {α : Type} {enc : α ↪ List Bool}
    {x : α → Input} {v k p : α → ℕ}
    (hx : ComputableInPolyTime x enc encAndOrNCL)
    (hv : ComputableInPolyTime v enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hp : ComputableInPolyTime p enc encNat) :
    ComputableInPolyTime (fun a => middle (x a) (v a) (k a) (p a)) enc encNat := by
  have hn : ComputableInPolyTime (fun a => (x a).graph.vertices.length) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hm : ComputableInPolyTime (fun a => (x a).initial.length) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold middle; fun_prop

@[fun_prop] private theorem test_polyTime {α : Type} {enc : α ↪ List Bool}
    {a b r : α → ℕ} {v : α → Bool}
    (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat)
    (hr : ComputableInPolyTime r enc encNat)
    (hv : ComputableInPolyTime v enc encBool) :
    ComputableInPolyTime (fun x => test (a x) (b x) (r x) (v x)) enc encInstruction := by
  unfold test; fun_prop

private theorem port_polyTime (i : ℕ) :
    ComputableInPolyTime (fun v : Vertex ℕ => port v i)
      (encVertex encNat) (encWeightedPort encNat) := by
  unfold port; fun_prop

private theorem localVertex_polyTime :
    ComputableInPolyTime localVertex (encVertex encNat) (encVertex encNat) := by
  have hm : ComputableInPolyTime
      (fun q : WeightedPort ℕ × ℕ => (⟨⟨q.2, q.1.port.dir⟩, q.1.weight⟩ : WeightedPort ℕ))
      (encPair (encWeightedPort encNat) encUnary) (encWeightedPort encNat) := by
    have hi : ComputableInPolyTime (fun q : WeightedPort ℕ × ℕ => q.2)
        (encPair (encWeightedPort encNat) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    fun_prop
  have hp := (ComputableInPolyTime.map hm).comp (by fun_prop : ComputableInPolyTime
    (fun v : Vertex ℕ => v.ports.zipIdx) (encVertex encNat)
    (encList (encPair (encWeightedPort encNat) encUnary)))
  unfold localVertex; fun_prop

private theorem branchInstruction_polyTime (k p : ℕ) :
    ComputableInPolyTime
      (fun q : Input × (Vertex ℕ × ℕ) => branchInstruction q.1 q.2.2 k q.2.1 p)
      encEmission encInstruction := by
  have hi : ComputableInPolyTime (fun q : Input × (Vertex ℕ × ℕ) => q.2.2)
      encEmission encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hp := (port_polyTime p).comp (by fun_prop : ComputableInPolyTime
    (fun q : Input × (Vertex ℕ × ℕ) => q.2.1) encEmission (encVertex encNat))
  unfold branchInstruction; split_ifs <;> fun_prop

private theorem branch_polyTime (k : ℕ) :
    ComputableInPolyTime
      (fun q : Input × (Vertex ℕ × ℕ) => branch q.1 q.2.2 k q.2.1)
      encEmission (encList encInstruction) := by
  have htest := Vertex.computableInPolyTime_checkSat
    (localVertex_polyTime.comp (by fun_prop : ComputableInPolyTime
      (fun q : Input × (Vertex ℕ × ℕ) => q.2.1) encEmission (encVertex encNat)))
    (ComputableInPolyTime.const (pattern k))
  have hbody := ComputableInPolyTime.mapConst (List.range 3)
    (fun p _ => branchInstruction_polyTime k p)
  unfold branch; fun_prop

private theorem flips_polyTime :
    ComputableInPolyTime flips encAndOrNCL (encList encInstruction) := by
  have hbody : ComputableInPolyTime
      (fun i => [Instruction.mk 0 (check 0) i false true,
        Instruction.mk 0 (check 0) i true false]) encUnary (encList encInstruction) := by
    have hi := ComputableInPolyTime.unary_to_binary; fun_prop
  unfold flips
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (ComputableInPolyTime.flatten encInstruction).comp ((ComputableInPolyTime.map hbody).comp
      (by fun_prop : ComputableInPolyTime (fun x : Input => List.range x.initial.length)
        encAndOrNCL (encList encUnary)))

private theorem checks_polyTime :
    ComputableInPolyTime checks encAndOrNCL (encList encInstruction) := by
  unfold checks
  exact ComputableInPolyTime.flatMapWithInput (by fun_prop)
    (ComputableInPolyTime.flatMapConst (List.range 8) fun k _ => branch_polyTime k)

private theorem targetTests_polyTime :
    ComputableInPolyTime targetTests encAndOrNCL (encList encInstruction) := by
  unfold targetTests
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  have hi : ComputableInPolyTime (fun q : Input × (Bool × ℕ) => q.2.2)
      (encPair encAndOrNCL (encPair encBool encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  fun_prop

private theorem raw_polyTime : ComputableInPolyTime raw encAndOrNCL encProgram := by
  have hf := flips_polyTime
  have hc := checks_polyTime
  have ht := targetTests_polyTime
  have hn : ComputableInPolyTime (fun x : Input => x.graph.vertices.length)
      encAndOrNCL encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hm : ComputableInPolyTime (fun x : Input => x.target.length)
      encAndOrNCL encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hi : ComputableInPolyTime (fun x : Input => x.initial) encAndOrNCL encBits :=
    ComputableInPolyTime.listToBits.comp (by fun_prop)
  unfold raw; fun_prop

private theorem guard_polyTime : ComputableInPolyTime guard encAndOrNCL encBool := by
  have hs : ComputableInPolyTime (fun x : Input => x.initial.length)
      encAndOrNCL encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have ht : ComputableInPolyTime (fun x : Input => x.target.length)
      encAndOrNCL encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hg : ComputableInPolyTime (fun x : Input => x.graph) encAndOrNCL encAndOrGraph := by
    fun_prop
  have he : ComputableInPolyTime (fun x : Input => x.graph.edgeCount) encAndOrNCL encNat := by
    fun_prop
  exact (((AndOrGraph.computableInPolyTime_checkValid.comp hg).bool_and'
    (hs.decide_eq' he)).bool_and' (ht.decide_eq' he)).bool_and'
    (AndOrGraph.computableInPolyTime_checkLegal hg
      (ComputableInPolyTime.listToBits.comp (by fun_prop)))

/-- The explicit guarded-register compiler is polynomial-time on the standard NCL encoding.
All unbounded scans range over explicit lists; the eight local patterns are fixed. -/
@[fun_prop] theorem computableInPolyTime_compile :
    ComputableInPolyTime compile encAndOrNCL encProgram := by
  have hg := guard_polyTime; have hr := raw_polyTime
  unfold compile reject; fun_prop

end Cslib.Complexity.SelfClosingDoor.RegisterProgram.NCLCompiler
