/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Forget
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Join
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.LeafIntro
import CslibFrontier.Tactic.Realize

/-!
# Node-step dispatcher, iteration splitting lemmas, and subtree invariant

This module combines `leafNodeProg`, `introNodeProg`, `forgetNodeProg`, and `joinNodeProg` into
the tagged post-order dispatcher `nodeStep` and its loop wrapper `iterNodesProg`. It also records
the `iterate` composition lemmas (`clientState_iterate_add`, `memoryCost_iterate_add`, etc.),
`holdsIn_encode_decode`, the inductive specification `SubtreeFullSpec`, and the shared arithmetic
setup `subtree_setup`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.NodeEnv`: shared memory-layout environment for the
  bottom-up pass.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.nodeStep`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.iterNodesProg`: single-node dispatcher and post-order
  iteration loop.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.nodeStepSafe`: word-width safety predicate.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.subtreeEnv`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.SubtreeFullSpec`: subtree induction specification.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.iterNodesProg_realizes`: exact-basis realization
  certificate for the dispatcher loop.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.subtree_setup`: common word-width and layout facts.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Environment bundle threaded through the bottom-up nice-tree DP pass (`nodeStep`). -/
structure NodeEnv where
  /-- Mode flag (`1` for exact model counting, `0` for satisfiability). -/
  mode : ℕ
  /-- Domain size `q`. -/
  q : ℕ
  /-- Base address of the serialized active-variable list `vars`. -/
  varsPtr : ℕ
  /-- Length of the serialized `vars` list. -/
  varsLen : ℕ
  /-- Base address of the serialized post-order node array. -/
  treePtr : ℕ
  /-- Base address of the serialized constraint-table array. -/
  consRawPtr : ℕ
  /-- Number of serialized constraint tables. -/
  numCons : ℕ
  /-- Base address of the allocated 4-word-per-node descriptor table. -/
  descBase : ℕ

/-- Tuple equivalence encoding `NodeEnv` into Word-RAM registers. -/
@[expose] def NodeEnv.equiv :
    NodeEnv ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) where
  toFun e := (((((((e.mode, e.q), e.varsPtr), e.varsLen), e.treePtr), e.consRawPtr),
    e.numCons), e.descBase)
  invFun := fun (((((((md, q), vp), vl), tp), cp), nc), db) =>
    ⟨md, q, vp, vl, tp, cp, nc, db⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding NodeEnv := .ofEquiv NodeEnv.equiv

/-- Dispatch one post-order nice-tree node `p.2` to `leafNodeProg`, `introNodeProg`,
`forgetNodeProg`, or `joinNodeProg`. -/
@[expose] def nodeStep (p : NodeEnv × ℕ) : Memory.Prog ℕ := do
  let env := p.1
  let cur := p.2
  let tag ← Memory.read (env.treePtr + 4 * cur)
  let arg ← Memory.read (env.treePtr + 4 * cur + 1)
  let ch1 ← Memory.read (env.treePtr + 4 * cur + 2)
  let ch2 ← Memory.read (env.treePtr + 4 * cur + 3)
  let dCur := env.descBase + 4 * cur
  if tag = 0 then
    let _ ← leafNodeProg ⟨env.consRawPtr, env.numCons, dCur⟩
    pure (cur + 1)
  else if tag = 1 then
    let _ ← introNodeProg ⟨env.q, arg, env.consRawPtr, env.numCons, env.descBase + 4 * ch1, dCur⟩
    pure (cur + 1)
  else if tag = 2 then
    let _ ← forgetNodeProg ⟨env.mode, env.q, arg, env.varsPtr, env.varsLen,
      env.descBase + 4 * ch1, dCur⟩
    pure (cur + 1)
  else
    let _ ← joinNodeProg ⟨env.q, env.descBase + 4 * ch1, env.descBase + 4 * ch2, dCur⟩
    pure (cur + 1)

/-- Word-width safety predicate guarding one iteration of `nodeStep`. -/
@[expose] def nodeStepSafe (w : ℕ) (p : NodeEnv × ℕ) (s : Memory.State) : Prop :=
  let env := p.1
  let cur := p.2
  let dCur := env.descBase + 4 * cur
  Fits w 4 ∧ Fits w (cur + 1) ∧
  Fits w (env.treePtr + 4 * cur + 3) ∧
  Fits w (dCur + 3) ∧
  ((s.mem (env.treePtr + 4 * cur) = 0 ∧
      ∃ (q : ℕ) (cs : List (ConstraintTable q)),
        0 < q ∧ cs.length = env.numCons ∧
        HoldsIn env.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
        Fits w (env.consRawPtr + (cs.flatMap ConstraintTable.encode).length)) ∨
   (s.mem (env.treePtr + 4 * cur) = 1 ∧
      0 < env.q ∧ Fits w env.q ∧ Fits w (s.mem (env.treePtr + 4 * cur + 1)) ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2) + 3) ∧
      ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
        (cs : List (ConstraintTable env.q)) (vars : List ℕ),
        Memory.WellFormed w s ∧ cs.length = env.numCons ∧
        HoldsIn env.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
        env.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ F_lo ∧
        NodeDescAt F_lo counting env.q cs vars child
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2)) s ∧
        F_lo ≤ s.frontier ∧
        Fits w (s.frontier +
          ((s.mem (env.treePtr + 4 * cur + 1) :: bagList child).length +
            env.q ^ (s.mem (env.treePtr + 4 * cur + 1) :: bagList child).length))) ∨
   (s.mem (env.treePtr + 4 * cur) = 2 ∧
      0 < env.q ∧ Fits w env.q ∧ Fits w (env.varsPtr + env.varsLen) ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2) + 3) ∧
      ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
        (cs : List (ConstraintTable env.q)) (vars : List ℕ),
        env.mode = (if counting then 1 else 0) ∧
        (∀ u ∈ bagList child, Fits w u) ∧
        NodeDescAt F_lo counting env.q cs vars child
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2)) s ∧
        F_lo ≤ s.frontier ∧
        Fits w (env.q ^ (bagList child).length) ∧
        Fits w (s.frontier +
          max (bagList child).length
            (((bagList child).erase (s.mem (env.treePtr + 4 * cur + 1))).length +
              env.q ^ ((bagList child).erase (s.mem (env.treePtr + 4 * cur + 1))).length)) ∧
        Fits w (if counting then env.q ^ (NiceTree.forget
          (s.mem (env.treePtr + 4 * cur + 1)) child).size else 1)) ∨
   (s.mem (env.treePtr + 4 * cur) ≠ 0 ∧ s.mem (env.treePtr + 4 * cur) ≠ 1 ∧
      s.mem (env.treePtr + 4 * cur) ≠ 2 ∧
      0 < env.q ∧ Fits w env.q ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2) + 3) ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 3) + 2) ∧
      ∃ (F_lo : ℕ) (counting : Bool) (left right : NiceTree ℕ)
        (cs : List (ConstraintTable env.q)) (vars : List ℕ),
        NodeDescAt F_lo counting env.q cs vars left
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2)) s ∧
        NodeDescAt F_lo counting env.q cs vars right
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 3)) s ∧
        Fits w (env.q ^ (bagList right).length) ∧
        Fits w (s.frontier + env.q ^ (bagList left).length) ∧
        Fits w (if counting then env.q ^ (NiceTree.join left right).size else 1)))

/-- Exact-basis Word-RAM realization certificate for `nodeStep`. -/
private theorem nodeStep_realizes :
    Realizes .exact nodeStep WordEncoding.encode WordEncoding.encode
      nodeStepSafe (fun _ _ => 0) := by
  unfold nodeStep
  realize [leafNodeProg_realizes, introNodeProg_realizes, forgetNodeProg_realizes,
    joinNodeProg_realizes]
  all_goals
    obtain ⟨h4, hcur1, htree3, hdCur3, hbranch⟩ := h
    first
    | exact h4.of_le (by decide)
    | exact htree3.of_le (by omega)
    | exact hdCur3.of_le (by omega)
    | (rcases hbranch with
        ⟨ht0', q, cs, hq, hlen, hcs, hend⟩ |
        ⟨ht0', _⟩ | ⟨ht0', _⟩ | ⟨ht0', _⟩ <;>
      omega)
    | (rcases hbranch with
        ⟨ht0', _⟩ |
        ⟨ht0', hq, hfit_q, hfit_arg, hfit_dCh, hex⟩ |
        ⟨ht0', _⟩ | ⟨_, ht1', _⟩ <;>
      first
      | omega
      | exact hfit_dCh.of_le (by omega))
    | (rcases hbranch with
        ⟨ht0', _⟩ | ⟨ht0', _⟩ |
        ⟨ht0', hq, hfit_q, hfit_vars, hfit_dCh, hex⟩ |
        ⟨_, _, ht2', _⟩ <;>
      first
      | omega
      | exact hfit_dCh.of_le (by omega))
    | (rcases hbranch with
        ⟨ht0', _⟩ | ⟨ht0', _⟩ | ⟨ht0', _⟩ |
        ⟨ht0', ht1', ht2', hq, hfit_q, hfit_dL, hfit_dR, hex⟩ <;>
      first
      | contradiction
      | exact hfit_q
      | exact hfit_dL.of_le (by omega)
      | exact hfit_dR.of_le (by omega)
      | exact hex)

/-- Execute `count` consecutive `nodeStep` iterations starting at node index `start`. -/
@[expose] def iterNodesProg (d : (NodeEnv × ℕ) × ℕ) : Memory.Prog ℕ :=
  let ((env, start), count) := d
  iterate nodeStep env count start

/-- Exact-basis Word-RAM realization certificate for `iterNodesProg`. -/
theorem iterNodesProg_realizes :
    Realizes .exact iterNodesProg WordEncoding.encode WordEncoding.encode
      (fun w d s =>
        let ((env, start), count) := d
        iterationSafe nodeStep nodeStepSafe w env count start s)
      (fun _ _ => 0) :=
  Realizes.iterate₀ WordEncoding.encode WordEncoding.encode nodeStep_realizes (fun _ _ => by
    unfold nodeStep; dsimp only; rw [memoryCost_bind', memoryCost_read]; omega)

/-- Running `n₁ + n₂` iterations runs `n₁` iterations and then `n₂` more. -/
private theorem iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ) (n₁ n₂ : ℕ)
    (a : σ) : iterate body d (n₁ + n₂) a = iterate body d n₁ a >>= iterate body d n₂ := by
  induction n₁ generalizing a with
  | zero => rw [Nat.zero_add]; exact (pure_bind a _).symm
  | succ n₁ ih =>
    rw [Nat.succ_add]
    exact (congrArg (body (d, a) >>= ·) (funext ih)).trans (bind_assoc _ _ _).symm

theorem clientState_iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State) :
    (Memory.spec 0).clientState s (iterate body d (n₁ + n₂) a) =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s (iterate body d n₁ a))
        (iterate body d n₂ ((Memory.spec 0).clientResult s (iterate body d n₁ a))) := by
  rw [iterate_add, StateTransitionSpec.clientState_bind]

theorem clientResult_iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (iterate body d (n₁ + n₂) a) =
      (Memory.spec 0).clientResult ((Memory.spec 0).clientState s (iterate body d n₁ a))
        (iterate body d n₂ ((Memory.spec 0).clientResult s (iterate body d n₁ a))) := by
  rw [iterate_add, StateTransitionSpec.clientResult_bind]

theorem memoryCost_iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (iterate body d (n₁ + n₂) a) s =
      memoryCost (iterate body d n₁ a) s +
        memoryCost (iterate body d n₂ ((Memory.spec 0).clientResult s (iterate body d n₁ a)))
          ((Memory.spec 0).clientState s (iterate body d n₁ a)) := by
  rw [iterate_add, memoryCost_bind']

theorem validHistory_iterate_add {w : ℕ} {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (d : δ) (n₁ n₂ : ℕ) (a : σ) (s : Memory.State)
    (hv₁ : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n₁ a)))
    (hv₂ : let s₁ := (Memory.spec 0).clientState s (iterate body d n₁ a)
      let r₁ := (Memory.spec 0).clientResult s (iterate body d n₁ a)
      (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ (iterate body d n₂ r₁))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate body d (n₁ + n₂) a)) := by
  rw [iterate_add]
  exact validHistory_bind_step hv₁ hv₂

theorem iterationSafe_add {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State)
    (hs₁ : iterationSafe body safe w d n₁ a s)
    (hs₂ : iterationSafe body safe w d n₂
      ((Memory.spec 0).clientResult s (iterate body d n₁ a))
      ((Memory.spec 0).clientState s (iterate body d n₁ a))) :
    iterationSafe body safe w d (n₁ + n₂) a s := by
  induction n₁ generalizing a s with
  | zero =>
    rw [Nat.zero_add]
    exact hs₂
  | succ n₁ ih =>
    rw [Nat.succ_add]
    refine ⟨hs₁.1, ih _ _ hs₁.2 ?_⟩
    change iterationSafe body safe w d n₂
      ((Memory.spec 0).clientResult s (body (d, a) >>= iterate body d n₁))
      ((Memory.spec 0).clientState s (body (d, a) >>= iterate body d n₁)) at hs₂
    rwa [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind] at hs₂

theorem holdsIn_encode_decode (inst : TreeCSPInstance) :
    let s₀ := Memory.State.init inst.encode
    let treePtr := 6 + inst.vars.length
    let consRawPtr := treePtr + 4 * inst.tree.size
    s₀.frontier = inst.encode.length + 1 ∧
    inst.encode.length = 5 + inst.vars.length + 4 * inst.tree.size +
      (inst.constraints.flatMap ConstraintTable.encode).length ∧
    s₀.mem 1 = (if inst.counting then 1 else 0) ∧
    s₀.mem 2 = inst.domainSize ∧
    s₀.mem 3 = inst.vars.length ∧
    s₀.mem 4 = inst.constraints.length ∧
    s₀.mem 5 = inst.tree.size ∧
    HoldsIn 6 inst.vars s₀ ∧
    HoldsIn treePtr (encodeNiceTree inst.tree) s₀ ∧
    HoldsIn consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₀ := by
  let s₀ := Memory.State.init inst.encode
  have hlen : inst.encode.length = 5 + inst.vars.length + 4 * inst.tree.size +
      (inst.constraints.flatMap ConstraintTable.encode).length := by
    simp only [TreeCSPInstance.encode, List.length_append, List.length_cons, List.length_nil,
      length_encodeNiceTree]
  have hall : HoldsIn 1 inst.encode s₀ := holdsIn_init inst.encode
  simp only [TreeCSPInstance.encode, HoldsIn.append_iff, HoldsIn.cons_iff, List.length_append,
    List.length_cons, List.length_nil, length_encodeNiceTree, ← Nat.add_assoc,
    Nat.reduceAdd] at hall
  obtain ⟨⟨⟨⟨_, hm1, _, hm2, _, hm3, _, hm4, _, hm5, _⟩, hvars⟩, htree⟩, hcons⟩ := hall
  exact ⟨rfl, hlen, hm1, hm2, hm3, hm4, hm5, hvars, htree,
    by simpa only [Nat.add_assoc] using hcons⟩

/-- Static `NodeEnv` decoded from `Memory.State.init inst.encode`. -/
abbrev subtreeEnv (inst : TreeCSPInstance) : NodeEnv :=
  ⟨if inst.counting then 1 else 0, inst.domainSize, 6, inst.vars.length,
    6 + inst.vars.length, 6 + inst.vars.length + 4 * inst.tree.size,
    inst.constraints.length, inst.encode.length + 1⟩

/-- Inductive specification proved for every subtree `S` executed by `iterate nodeStep`. -/
abbrev SubtreeFullSpec (w : ℕ) (inst : TreeCSPInstance) (S : NiceTree ℕ) (offset : ℕ)
    (s : Memory.State) : Prop :=
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  offset + S.size ≤ inst.tree.size →
  maxTableExp S ≤ maxTableExp inst.tree →
  maxTreeVert S ≤ maxTreeVert inst.tree →
  Memory.WellFormed w s →
  F_lo ≤ s.frontier →
  s.frontier + S.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) ≤
    F_lo + inst.tree.size *
      (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) →
  HoldsIn env.varsPtr inst.vars s →
  HoldsIn (env.treePtr + 4 * offset) (encodeNiceTreeAux offset S) s →
  HoldsIn env.consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s →
  let prog := iterate nodeStep env S.size offset
  let sEnd := (Memory.spec 0).clientState s prog
  iterationSafe nodeStep nodeStepSafe w env S.size offset s ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
  (Memory.spec 0).clientResult s prog = offset + S.size ∧
  sEnd.frontier ≤
    s.frontier + S.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) ∧
  FrameOutsideRange (env.descBase + 4 * offset)
    (env.descBase + 4 * (offset + S.size)) s sEnd ∧
  NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars S
    (env.descBase + 4 * (offset + S.size - 1)) sEnd ∧
  memoryCost prog s ≤
    S.size *
      (16 + 4 * maxTableExp inst.tree + inst.vars.length +
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 +
            3 * inst.constraints.length +
            inst.totalArity * (2 * maxTableExp inst.tree + 3)))

theorem subtree_setup {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    let env := subtreeEnv inst
    let F_lo := env.descBase + 4 * inst.tree.size
    let E := maxTableExp inst.tree
    let perSpace := E + 2 + inst.domainSize ^ E
    1 ≤ inst.domainSize ^ E ∧
    Fits w 4 ∧
    Fits w inst.domainSize ∧
    Fits w inst.tree.size ∧
    Fits w (F_lo + inst.tree.size * perSpace) ∧
    env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length = env.descBase ∧
    env.varsPtr + env.varsLen ≤ env.descBase ∧
    env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length ≤ env.descBase ∧
    0 < inst.tree.size ∧
    perSpace ≤ inst.tree.size * perSpace ∧
    (∀ A : ℕ, A ≤ E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3) →
      inst.domainSize ^ E * A ≤
        inst.domainSize ^ E *
          (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))) ∧
    (∀ S, maxTreeVert S ≤ maxTreeVert inst.tree → ∀ u ∈ bagList S, Fits w u) := by
  intro env F_lo E perSpace
  have hpow_ge1 : 1 ≤ inst.domainSize ^ E := Nat.one_le_pow E inst.domainSize inst.domainSize_pos
  have hlen_enc := (holdsIn_encode_decode inst).2.1
  have hfit_q : Fits w inst.domainSize := hw.of_le <| by
    have h1q : inst.domainSize ≤ inst.domainSize * inst.domainSize ^ maxTableExp inst.tree :=
      Nat.le_mul_of_pos_right _ hpow_ge1
    unfold TreeCSPInstance.wordBound
    dsimp only
    omega
  have hfit_total : Fits w (F_lo + inst.tree.size * perSpace) := hw.of_le <| by
    dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *
    unfold TreeCSPInstance.wordBound
    dsimp only
    omega
  have hcons_len_bound : env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length = env.descBase := by
    dsimp only [env, subtreeEnv]
    omega
  have hvars_lt_desc : env.varsPtr + env.varsLen ≤ env.descBase := by
    dsimp only [env, subtreeEnv]
    omega
  refine ⟨hpow_ge1,
    hw.of_le (by dsimp only [TreeCSPInstance.wordBound]; omega),
    hfit_q,
    hw.of_le (by dsimp only [TreeCSPInstance.wordBound]; omega),
    hfit_total, hcons_len_bound, hvars_lt_desc, hcons_len_bound.le, inst.tree.size_pos,
    Nat.le_mul_of_pos_left perSpace inst.tree.size_pos,
    fun _ hA => Nat.mul_le_mul_left _ hA, fun S hmv u hu => hw.of_le ?_⟩
  have hum := (mem_bagList_le_maxTreeVert S hu).trans hmv
  have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
    (le_max_left _ _).trans (le_max_right _ _)
  dsimp only [TreeCSPInstance.wordBound]
  omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
