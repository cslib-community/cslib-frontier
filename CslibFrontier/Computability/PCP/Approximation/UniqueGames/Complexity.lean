/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.LabelCover
public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Words
import CslibFrontier.Computability.PCP.Encoded.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.OptionMatch

/-!
# Polynomial-time membership for satisfiable unique games

For each fixed finite alphabet `Fin L`, label propagation
(`Cslib.Complexity.UniqueGames.Propagation.solve`) runs in polynomial time on the multi-tape Turing
machine model under the graph encoding `Graph.encoding (encPi (encFinEnum (Fin L)))` of
`Cslib.Complexity.UniqueGamesConjecture`.

To avoid building closures of type `ℕ → Fin L` at runtime, we evaluate a table-reading check
directly on `(Propagation.run (List.finRange L) g).table`, show it agrees pointwise with
`(Propagation.solve (List.finRange L) g).isSome`, and combine it with
`Propagation.solvedBy_gapUniqueGames_one` and `Propagation.solve_isSome_iff`.

For `L = 0`, `Fin 0` is empty, so no labelling `ℕ → Fin 0` exists: every unique game vacuously
has `unsatVal = 0` and is a yes-instance of `GapUniqueGames (Fin 0) 1 s` (with no no-instances),
while `{g : Graph (Fin 0 → Fin 0) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable}`
is empty. Both belong to `PromiseP` / `P`.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.computableInPolyTime_isSome_solve`: for every
  `[NeZero L]`, `(solve (List.finRange L) ·).isSome` is computable in polynomial time under
  `Graph.encoding (encPi (encFinEnum (Fin L)))`.
* `Cslib.Complexity.gapUniqueGames_one_mem_PromiseP_of_pos`: for `0 < L` and every `s : ℝ`,
  `GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L))))`.
* `Cslib.Complexity.gapUniqueGames_zero_mem_PromiseP`: explicit characterization and `PromiseP`
  membership for `L = 0`.
* `Cslib.Complexity.gapUniqueGames_one_mem_PromiseP`: unconditional `PromiseP` membership for all
  `L : ℕ` and `s : ℝ`.
* `Cslib.Complexity.isUniqueGame_mem_P`, `Cslib.Complexity.satisfiable_uniqueGame_mem_P`: `P`
  membership for recognizing unique games and deciding their satisfiability.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

section PolyTime

open ComputableInPolyTime

private noncomputable def encUGFn (L : ℕ) : (Fin L → Fin L) ↪ List Bool :=
  encPi (encFinEnum (Fin L))

private noncomputable abbrev encUGGraph (L : ℕ) : Graph (Fin L → Fin L) ↪ List Bool :=
  Graph.encoding (encUGFn L)

private noncomputable abbrev encUGEdge (L : ℕ) : Edge (Fin L → Fin L) ↪ List Bool :=
  Edge.encoding (encUGFn L)

private noncomputable abbrev encUGTable (L : ℕ) : List (Option (Fin L → Fin L)) ↪ List Bool :=
  encList (encOption (encUGFn L))

private noncomputable def encUGCand (L : ℕ) : (Fin L → Bool) ↪ List Bool :=
  encPi encBool

private abbrev encUGVerts : List ℕ ↪ List Bool :=
  encList encUnary

private noncomputable def encUGState (L : ℕ) : State (Fin L) ↪ List Bool :=
  (⟨fun S => ((S.table, S.cand), (S.stack, S.comp)), fun S₁ S₂ h => by
    cases S₁; cases S₂; simp_all⟩ : State (Fin L) ↪ _).trans
    (encPair (encPair (encUGTable L) (encUGCand L)) (encPair encUGVerts encUGVerts))

private theorem encUGState_apply (L : ℕ) (S : State (Fin L)) :
    encUGState L S =
      encPair (encPair (encUGTable L) (encUGCand L)) (encPair encUGVerts encUGVerts)
        ((S.table, S.cand), (S.stack, S.comp)) :=
  rfl

private theorem poly_state_unpack (L : ℕ) :
    ComputableInPolyTime
      (fun S : State (Fin L) => ((S.table, S.cand), (S.stack, S.comp)))
      (encUGState L)
      (encPair (encPair (encUGTable L) (encUGCand L)) (encPair encUGVerts encUGVerts)) :=
  .of_eq fun _ => rfl

@[local fun_prop]
private theorem poly_state_table {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool} {s : γ → State (Fin L)}
    (hs : ComputableInPolyTime s encIn (encUGState L)) :
    ComputableInPolyTime (fun x => (s x).table) encIn (encUGTable L) :=
  (poly_state_unpack L).fst'.fst'.comp hs

@[local fun_prop]
private theorem poly_state_cand {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool} {s : γ → State (Fin L)}
    (hs : ComputableInPolyTime s encIn (encUGState L)) :
    ComputableInPolyTime (fun x => (s x).cand) encIn (encUGCand L) :=
  (poly_state_unpack L).fst'.snd'.comp hs

@[local fun_prop]
private theorem poly_state_stack {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool} {s : γ → State (Fin L)}
    (hs : ComputableInPolyTime s encIn (encUGState L)) :
    ComputableInPolyTime (fun x => (s x).stack) encIn encUGVerts :=
  (poly_state_unpack L).snd'.fst'.comp hs

@[local fun_prop]
private theorem poly_state_comp {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool} {s : γ → State (Fin L)}
    (hs : ComputableInPolyTime s encIn (encUGState L)) :
    ComputableInPolyTime (fun x => (s x).comp) encIn encUGVerts :=
  (poly_state_unpack L).snd'.snd'.comp hs

@[local fun_prop]
private theorem poly_state_mk {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool}
    {table : γ → List (Option (Fin L → Fin L))} {cand : γ → Fin L → Bool}
    {stack comp : γ → List ℕ}
    (htable : ComputableInPolyTime table encIn (encUGTable L))
    (hcand : ComputableInPolyTime cand encIn (encUGCand L))
    (hstack : ComputableInPolyTime stack encIn encUGVerts)
    (hcomp : ComputableInPolyTime comp encIn encUGVerts) :
    ComputableInPolyTime (fun x => State.mk (table x) (cand x) (stack x) (comp x))
      encIn (encUGState L) :=
  ((htable.prod hcand).prod (hstack.prod hcomp)).of_enc_eq fun _ => rfl

private lemma optBound_spec (L : ℕ) (o : Option (Fin L → Fin L)) :
    (encOption (encUGFn L) o).length ≤ L * (2 * L + 1) + 1 := by
  cases o with
  | none => simp [encOption_none]
  | some f =>
    have hpi : (encUGFn L f).length ≤ Fintype.card (Fin L) * (2 * L + 1) :=
      length_encPi_le (encFinEnum (Fin L)) f fun i =>
        (length_encFinEnum_lt (f i)).le.trans (by simp)
    simp only [Fintype.card_fin, encUGFn, encOption_some, List.length_cons] at hpi ⊢
    omega

private lemma candBound_spec (L : ℕ) (c : Fin L → Bool) :
    (encUGCand L c).length ≤ 3 * L := by
  have hpi : (encUGCand L c).length ≤ Fintype.card (Fin L) * (2 * 1 + 1) :=
    length_encPi_le encBool c fun i => by simp [encBool_apply]
  simp only [Fintype.card_fin, encUGCand] at hpi ⊢
  omega

private lemma length_encList_replicate_none {α : Type} (n : ℕ) (enc : α ↪ List Bool) :
    (encList (encOption enc) (List.replicate n none)).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, encList_cons, encOption_none, ih]

private lemma length_encUGState_eq (L : ℕ) (S : State (Fin L)) :
    (encUGState L S).length =
      4 * (encUGTable L S.table).length + 2 * (encUGCand L S.cand).length +
        2 * (encUGVerts S.stack).length + (encUGVerts S.comp).length + 4 := by
  simp only [encUGState_apply, length_encPair]; omega

private lemma length_encUGTable_le_mul (L : ℕ) (t : List (Option (Fin L → Fin L))) :
    (encUGTable L t).length ≤ t.length * (2 * (L * (2 * L + 1) + 1) + 1) :=
  length_encList_le (encOption (encUGFn L)) t fun o _ => optBound_spec L o

@[local fun_prop]
private theorem poly_slots (L : ℕ) :
    ComputableInPolyTime (slots (C := Fin L → Fin L)) (encUGGraph L) encUnary := by
  unfold slots
  refine foldlWith_of_bounded_growth
    (encP := encBool) (encB := encUnary) (encA := encUGEdge L)
    (par := fun _ => true) (list := fun g => g.edges) (init := fun g => g.vertices)
    (step := fun _ n e => max n (max e.src e.dst + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun g => (encUGGraph L g).length) .self fun g n e he => ?_
  have hmem := SizedListEncoding.length_elem_le (encA := encUGEdge L)
    (encL := encList (encUGEdge L)) g.edges e he
  have hle : (encList (encUGEdge L) g.edges).length ≤ (encUGGraph L g).length := by
    change _ ≤ (encPair encUnary (encList (encUGEdge L)) (g.vertices, g.edges)).length
    rw [length_encPair]
    dsimp only
    omega
  have hend : e.src + 1 ≤ (encUGEdge L e).length ∧ e.dst + 1 ≤ (encUGEdge L e).length := by
    rw [show (encUGEdge L e).length =
        (encPair encUnary (encPair encUnary (encUGFn L)) (e.src, e.dst, e.constraint)).length
      from rfl, length_encPair, length_encPair]
    dsimp only
    simp only [encUnary_apply, List.length_replicate]
    omega
  simp only [encUnary_apply, List.length_replicate]
  exact max_le (Nat.le_add_right _ _) (by omega)

@[local fun_prop]
private theorem poly_init (L : ℕ) :
    ComputableInPolyTime (init (α := Fin L)) (encUGGraph L) (encUGState L) := by
  unfold init
  exact poly_state_mk (replicate (poly_slots L) (const (none : Option (Fin L → Fin L))))
    (const (fun _ => true)) (const []) (const [])

@[local fun_prop]
private theorem poly_start (L : ℕ) :
    ComputableInPolyTime (fun p : State (Fin L) × ℕ => start p.1 p.2)
      (encPair (encUGState L) encUnary) (encUGState L) := by
  unfold start; fun_prop

@[local fun_prop]
private theorem poly_push {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool}
    {s : γ → State (Fin L)} {w : γ → ℕ} {f : γ → Fin L → Fin L}
    (hs : ComputableInPolyTime s encIn (encUGState L))
    (hw : ComputableInPolyTime w encIn encUnary)
    (hf : ComputableInPolyTime f encIn (encUGFn L)) :
    ComputableInPolyTime (fun x => push (s x) (w x) (f x)) encIn (encUGState L) := by
  unfold push; fun_prop

@[local fun_prop]
private theorem poly_get {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool}
    {s : γ → State (Fin L)} {v : γ → ℕ}
    (hs : ComputableInPolyTime s encIn (encUGState L))
    (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => (s x).get (v x)) encIn (encOption (encUGFn L)) := by
  unfold State.get
  exact (listGetD (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
    ((poly_state_table hs).prod hv)

private theorem scan_eq_elim {α : Type} [DecidableEq α] (labels : List α)
    (g : Graph (α → α)) (S : State α) :
    scan labels g S =
      S.stack.head?.elim S fun u =>
        (adj g u).foldl (visit labels)
          (State.mk S.table S.cand (S.stack.drop 1) (u :: S.comp)) := by
  unfold scan; cases S.stack <;> rfl

@[local fun_prop]
private theorem poly_extend (L : ℕ) :
    ComputableInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) => extend (List.finRange L) p.1 p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := by
  unfold extend
  option_match_to_elim
  have hpre : ComputableInPolyTime
      (fun r : (Fin L → Fin L) × (Fin L → Fin L) => preimage (List.finRange L) r.1 ∘ r.2)
      (encPair (encUGFn L) (encUGFn L)) (encUGFn L) := of_finite _
  have hcomp : ComputableInPolyTime
      (fun r : (Fin L → Fin L) × (Fin L → Fin L) => r.1 ∘ r.2)
      (encPair (encUGFn L) (encUGFn L)) (encUGFn L) := of_finite _
  refine optionElimWithInput (by fun_prop)
    (optionElimWithInput (by fun_prop) (by fun_prop)
      (poly_push (by fun_prop) (by fun_prop)
        (hpre.comp ((Edge.isPolyTime_constraint (fst' id').snd').prod (snd' id')))))
    (optionElimWithInput (by fun_prop)
      (poly_push (by fun_prop) (by fun_prop)
        (hcomp.comp ((Edge.isPolyTime_constraint (fst' id').snd').prod (snd' id'))))
      (by fun_prop))

@[local fun_prop]
private theorem poly_prune (L : ℕ) :
    ComputableInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) => prune p.1 p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := by
  unfold prune
  option_match_to_elim
  have hcandFin : ComputableInPolyTime
      (fun r : ((Fin L → Bool) × (Fin L → Fin L)) × ((Fin L → Fin L) × (Fin L → Fin L)) =>
        fun a => r.1.1 a && decide (r.2.1 (r.1.2 a) = r.2.2 a))
      (encPair (encPair (encUGCand L) (encUGFn L)) (encPair (encUGFn L) (encUGFn L)))
      (encUGCand L) := of_finite _
  refine optionElimWithInput (by fun_prop) (by fun_prop)
    (optionElimWithInput (by fun_prop) (by fun_prop) ?_)
  exact poly_state_mk (by fun_prop)
    (hcandFin.comp
      (((poly_state_cand (fst' (fst' (fst' id')))).prod (fst' id').snd').prod
        ((Edge.isPolyTime_constraint (fst' (fst' id')).snd').prod (snd' id'))))
    (by fun_prop) (by fun_prop)

@[local fun_prop]
private theorem poly_visit (L : ℕ) :
    ComputableInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) => visit (List.finRange L) p.1 p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := by
  unfold visit; fun_prop

@[local fun_prop]
private theorem poly_adj (L : ℕ) :
    ComputableInPolyTime (fun p : Graph (Fin L → Fin L) × ℕ => adj p.1 p.2)
      (encPair (encUGGraph L) encUnary) (encList (encUGEdge L)) := by
  unfold adj incident
  refine filterWithInput (by fun_prop) ?_
  fun_prop

private def visitGrowth (L : ℕ) (n : ℕ) : ℕ :=
  4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * n + 1) + 6 * L

private lemma length_encUGState_push_le (L : ℕ) (S : State (Fin L)) (w : ℕ) (f : Fin L → Fin L) :
    (encUGState L (push S w f)).length ≤
      (encUGState L S).length + 4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * w + 1) := by
  have htab := length_encList_set_le (encOption (encUGFn L)) S.table w (some f)
  change (encUGTable L (S.table.set w (some f))).length ≤
    (encUGTable L S.table).length + 2 * (encOption (encUGFn L) (some f)).length + 1 at htab
  have hopt := optBound_spec L (some f)
  have hst : (encUGVerts (w :: S.stack)).length = 2 * w + 1 + (encUGVerts S.stack).length := by
    simp [encUGVerts, encList_cons, length_frame, encUnary_apply]
  rw [length_encUGState_eq, length_encUGState_eq]
  simp only [push]; omega

private lemma length_encUGState_prune_le (L : ℕ) (S : State (Fin L)) (e : Edge (Fin L → Fin L)) :
    (encUGState L (prune S e)).length ≤ (encUGState L S).length + 6 * L := by
  unfold prune
  split
  · rename_i f h _ _
    have hcand := candBound_spec L (fun a => S.cand a && decide (e.constraint (f a) = h a))
    rw [length_encUGState_eq, length_encUGState_eq]; dsimp only; omega
  · exact Nat.le_add_right _ _

private lemma length_encUGState_visit_le (L : ℕ) (labels : List (Fin L)) (S : State (Fin L))
    (e : Edge (Fin L → Fin L)) (n : ℕ) (hsrc : e.src < n) (hdst : e.dst < n) :
    (encUGState L (visit labels S e)).length ≤
      (encUGState L S).length + visitGrowth L n := by
  unfold visit visitGrowth
  have hp := length_encUGState_prune_le L (extend labels S e) e
  have he : (encUGState L (extend labels S e)).length ≤
      (encUGState L S).length + 4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * n + 1) := by
    unfold extend
    rcases hs : S.get e.src with _ | f <;> rcases hd : S.get e.dst with _ | h <;> dsimp only
    · omega
    · have := length_encUGState_push_le L S e.src (preimage labels e.constraint ∘ h); omega
    · have := length_encUGState_push_le L S e.dst (e.constraint ∘ f); omega
    · omega
  omega

@[local fun_prop]
private theorem poly_visitGrowth_comp {γ : Type} {encIn : γ ↪ List Bool} (L : ℕ)
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun x => visitGrowth L (n x)) encIn encUnary := by
  unfold visitGrowth
  exact unary_add.comp
    ((unary_add.comp ((const (4 * (2 * (L * (2 * L + 1) + 1) + 1))).prod
      (unary_mul.comp ((const 2).prod
        (unary_add.comp ((unary_mul.comp ((const 2).prod hn)).prod (const 1))))))).prod
      (const (6 * L)))

@[local fun_prop]
private theorem poly_scan (L : ℕ) :
    ComputableInPolyTime
      (fun p : Graph (Fin L → Fin L) × State (Fin L) => scan (List.finRange L) p.1 p.2)
      (encPair (encUGGraph L) (encUGState L)) (encUGState L) := by
  simp_rw [scan_eq_elim]
  refine optionElimWithInput (by fun_prop) (by fun_prop) ?_
  refine foldlWith_of_bounded_growth
    (encP := encBool) (encB := encUGState L) (encA := encUGEdge L)
    (encL := encList (encUGEdge L))
    (encIn := encPair (encPair (encUGGraph L) (encUGState L)) encUnary)
    (par := fun _ => true)
    (list := fun q => adj q.1.1 q.2)
    (init := fun q => State.mk q.1.2.table q.1.2.cand (q.1.2.stack.drop 1) (q.2 :: q.1.2.comp))
    (step := fun (_ : Bool) => visit (List.finRange L))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun q => visitGrowth L (slots q.1.1))
    (poly_visitGrowth_comp L ((poly_slots L).comp (fst' (fst' id')))).polyBounded
    fun q acc e he => length_encUGState_visit_le L (List.finRange L) acc e (slots q.1.1)
      (src_lt_slots (List.mem_filter.mp he).1) (dst_lt_slots (List.mem_filter.mp he).1)

@[local fun_prop]
private theorem poly_settle (L : ℕ) [NeZero L] :
    ComputableInPolyTime (settle (List.finRange L)) (encUGState L) (encUGState L) := by
  unfold settle
  have hcandPick : ComputableInPolyTime
      (fun S : State (Fin L) => ((List.finRange L).find? S.cand).getD default)
      (encUGState L) (encFinEnum (Fin L)) :=
    (of_finite (fun c : Fin L → Bool => ((List.finRange L).find? c).getD default)).comp
      (by fun_prop)
  have hfreeze : ComputableInPolyTime
      (fun p : Fin L × Option (Fin L → Fin L) => freeze p.1 p.2)
      (encPair (encFinEnum (Fin L)) (encOption (encUGFn L))) (encOption (encUGFn L)) :=
    of_finite _
  have htable : ComputableInPolyTime
      (fun S : State (Fin L) => S.comp.foldl
        (fun t v =>
          t.set v (freeze (((List.finRange L).find? S.cand).getD default) (t.getD v none)))
        S.table)
      (encUGState L) (encUGTable L) := by
    refine foldlWith_of_bounded_growth
      (encP := encFinEnum (Fin L)) (encB := encUGTable L) (encA := encUnary)
      (par := fun S : State (Fin L) => ((List.finRange L).find? S.cand).getD default)
      (list := fun S : State (Fin L) => S.comp) (init := fun S : State (Fin L) => S.table)
      (step := fun c t v => t.set v (freeze c (t.getD v none)))
      hcandPick (by fun_prop) (by fun_prop) ?_
      (growth := fun _ => 2 * (L * (2 * L + 1) + 1) + 1)
      (PolyBounded.const _) fun S t v _ => ?_
    · exact ComputableInPolyTime.listSetWithInput (encOption (encUGFn L))
        (by fun_prop) (by fun_prop)
        (hfreeze.comp ((fst _ _).fst'.prod
          ((listGetD (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
            ((fst _ _).snd'.prod (snd _ _)))))
    · have hle := length_encList_set_le (encOption (encUGFn L)) t v
        (freeze (((List.finRange L).find? S.cand).getD default) (t.getD v none))
      have hopt := optBound_spec L
        (freeze (((List.finRange L).find? S.cand).getD default) (t.getD v none))
      change (encList (encOption (encUGFn L)) _).length ≤
        (encList (encOption (encUGFn L)) t).length + (2 * (L * (2 * L + 1) + 1) + 1)
      omega
  exact poly_state_mk htable (by fun_prop) (by fun_prop) (const [])

private lemma length_encUGState_scan_le (L : ℕ) (labels : List (Fin L))
    (g : Graph (Fin L → Fin L)) (S : State (Fin L)) :
    (encUGState L (scan labels g S)).length ≤
      (encUGState L S).length + g.edges.length * visitGrowth L (slots g) := by
  unfold scan
  cases hs : S.stack with
  | nil => exact Nat.le_add_right _ _
  | cons u rest =>
    dsimp only
    let S₀ : State (Fin L) :=
      { table := S.table, cand := S.cand, stack := rest, comp := u :: S.comp }
    have hS₀ : (encUGState L S₀).length ≤ (encUGState L S).length := by
      simp only [S₀, length_encUGState_eq, hs, encUGVerts, encList_cons, List.length_append]
      omega
    have hfold : ∀ (l : List (Edge (Fin L → Fin L))) (acc : State (Fin L)),
        (∀ e ∈ l, e ∈ g.edges) →
        (encUGState L (l.foldl (visit labels) acc)).length ≤
          (encUGState L acc).length + l.length * visitGrowth L (slots g) := by
      intro l acc hl
      induction l generalizing acc with
      | nil => simp
      | cons e l ih =>
        have he := hl e (List.mem_cons_self ..)
        have hv := length_encUGState_visit_le L labels acc e (slots g)
          (src_lt_slots he) (dst_lt_slots he)
        have hih := ih (visit labels acc e) fun e' he' => hl e' (List.mem_cons_of_mem _ he')
        simp only [List.foldl_cons, List.length_cons, Nat.succ_mul] at hih hv ⊢
        omega
    exact (hfold (adj g u) S₀ fun e he => (List.mem_filter.mp he).1).trans
      (Nat.add_le_add hS₀ (Nat.mul_le_mul_right _ (List.length_filter_le _ _)))

private lemma length_encUGState_iterate_scan_le (L : ℕ) (labels : List (Fin L))
    (g : Graph (Fin L → Fin L)) (S : State (Fin L)) (k : ℕ) :
    (encUGState L ((scan labels g)^[k] S)).length ≤
      (encUGState L S).length + k * (g.edges.length * visitGrowth L (slots g)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := length_encUGState_scan_le L labels g ((scan labels g)^[k] S)
    rw [Nat.succ_mul]
    omega

private lemma length_encUGState_settle_le (L : ℕ) [NeZero L] (labels : List (Fin L))
    (S : State (Fin L)) :
    (encUGState L (settle labels S)).length ≤
      4 * (S.table.length * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
        2 * (encUGVerts S.stack).length + 4 := by
  have htab := (length_encUGTable_le_mul L (settle labels S).table).trans
    (by rw [settle_length])
  have hcand := candBound_spec L (settle labels S).cand
  have hcomp : (settle labels S).comp = [] := rfl
  have hstack : (settle labels S).stack = S.stack := rfl
  simp only [length_encUGState_eq, hstack, hcomp, encUGVerts, encList_nil, List.length_nil]
  omega

private theorem poly_step (L : ℕ) [NeZero L] :
    ComputableInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        step (List.finRange L) p.1.1 p.1.2 p.2)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) := by
  unfold step
  option_match_to_elim
  have hiter : ComputableInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        (scan (List.finRange L) p.1.1)^[slots p.1.1] (start p.1.2 p.2.src))
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) :=
    iterateWith_of_bounded_growth
      (encIn := encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L))
      (encPar := encUGGraph L) (encState := encUGState L)
      (par := fun p => p.1.1) (count := fun p => slots p.1.1)
      (init := fun p => start p.1.2 p.2.src) (step := scan (List.finRange L))
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (growth := fun p => p.1.1.edges.length * visitGrowth L (slots p.1.1))
      (by fun_prop : ComputableInPolyTime (fun p : (Graph (Fin L → Fin L) × State (Fin L)) ×
        Edge (Fin L → Fin L) => p.1.1.edges.length * visitGrowth L (slots p.1.1))
        (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) encUnary).polyBounded
      fun p acc => length_encUGState_scan_le L (List.finRange L) p.1.1 acc
  exact optionElimWithInput (by fun_prop) ((poly_settle L).comp hiter) (by fun_prop)

private def runBound (L : ℕ) (g : Graph (Fin L → Fin L)) : ℕ :=
  4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
    2 * (4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
      2 * (2 * slots g + 1) + 4 + slots g * (g.edges.length * visitGrowth L (slots g))) + 4

private lemma length_encUGState_step_le (L : ℕ) [NeZero L]
    (g : Graph (Fin L → Fin L)) (acc : State (Fin L)) (e : Edge (Fin L → Fin L))
    (he : e ∈ g.edges) (hlen : acc.table.length = slots g)
    (hbound : (encUGState L acc).length ≤ runBound L g) :
    (encUGState L (step (List.finRange L) g acc e)).length ≤ runBound L g := by
  unfold step
  rcases acc.get e.src with _ | _
  · dsimp only
    have hsrc : e.src < slots g := src_lt_slots he
    have hstartLen : (start acc e.src).table.length = slots g := by
      simpa [start, List.length_set] using hlen
    have hS₀ : (encUGState L (start acc e.src)).length ≤
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
          2 * (2 * slots g + 1) + 4 := by
      have htab := length_encUGTable_le_mul L (start acc e.src).table
      rw [hstartLen] at htab
      have hcand := candBound_spec L (fun _ : Fin L => true)
      have hst : (encUGVerts [e.src]).length = 2 * e.src + 1 := by
        simp [encUGVerts, encList_cons, encList_nil, length_frame, encUnary_apply]
      rw [length_encUGState_eq]
      dsimp only [start] at htab ⊢
      rw [hst]
      simp only [encList_nil, List.length_nil]
      omega
    have hiter := length_encUGState_iterate_scan_le L (List.finRange L) g
      (start acc e.src) (slots g)
    have hstack : (encUGVerts ((scan (List.finRange L) g)^[slots g]
        (start acc e.src)).stack).length ≤
        (encUGState L ((scan (List.finRange L) g)^[slots g] (start acc e.src))).length := by
      rw [length_encUGState_eq]; omega
    have hset := length_encUGState_settle_le L (List.finRange L)
      ((scan (List.finRange L) g)^[slots g] (start acc e.src))
    rw [length_iterate_scan, hstartLen] at hset
    unfold runBound; omega
  · exact hbound

private theorem poly_run (L : ℕ) [NeZero L] :
    ComputableInPolyTime (run (List.finRange L)) (encUGGraph L) (encUGState L) := by
  unfold run
  have hboundPoly : PolyBounded (fun g => (encUGGraph L g).length) (runBound L) := by
    growth_poly [poly_slots L, poly_visitGrowth_comp L (poly_slots L),
      Graph.isPolyTime_edges (enc := encUGFn L) .id']
  refine foldlWith
    (encP := encUGGraph L) (encB := encUGState L) (encA := encUGEdge L)
    (par := id) (list := fun g => g.edges) (init := init) (step := step (List.finRange L))
    id' (by fun_prop) (by fun_prop) (poly_step L) (B := runBound L) hboundPoly
    fun g i hi => ?_
  suffices ∀ j ≤ g.edges.length,
      (List.foldl (step (List.finRange L) g) (init g) (g.edges.take j)).table.length = slots g ∧
      (encUGState L (List.foldl (step (List.finRange L) g) (init g) (g.edges.take j))).length ≤
        runBound L g from (this i hi).2
  intro j hj
  induction j with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, init, List.length_replicate, true_and]
    have htab := length_encList_replicate_none (slots g) (encUGFn L)
    have hcand := candBound_spec L (fun _ : Fin L => true)
    rw [length_encUGState_eq]
    simp only [htab, encUGVerts, encList_nil, List.length_nil, runBound]
    omega
  | succ j ih =>
    obtain ⟨hlen, hbound⟩ := ih (Nat.le_of_succ_le hj)
    have htake : g.edges.take (j + 1) = g.edges.take j ++ [g.edges[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := List.foldl (step (List.finRange L) g) (init g) (g.edges.take j)
    exact ⟨(length_step _ g acc g.edges[j]).trans hlen,
      length_encUGState_step_le L g acc g.edges[j] (List.getElem_mem hj) hlen hbound⟩

private def checkTable {α : Type} [DecidableEq α] [Inhabited α]
    (table : List (Option (α → α))) (g : Graph (α → α)) : Bool :=
  g.edges.all fun e =>
    let l : ℕ → α := fun v => (table.getD v none).elim default fun f => f default
    decide (e.constraint (l e.src) = l e.dst)

private theorem checkTable_run_eq_isSome_solve {α : Type} [DecidableEq α] [Inhabited α]
    (labels : List α) (g : Graph (α → α)) :
    checkTable (run labels g).table g = (solve labels g).isSome := by
  have hcheck : checkTable (run labels g).table g = check g (labelling labels g) := rfl
  rw [hcheck]
  unfold solve
  split_ifs with h <;> simp [h]

private def tableVal {L : ℕ} [NeZero L] (o : Option (Fin L → Fin L)) : Fin L :=
  o.elim default fun f => f default

private theorem poly_checkTable (L : ℕ) [NeZero L] :
    ComputableInPolyTime
      (fun p : List (Option (Fin L → Fin L)) × Graph (Fin L → Fin L) =>
        checkTable p.1 p.2)
      (encPair (encUGTable L) (encUGGraph L)) encBool := by
  change ComputableInPolyTime
      (fun p : List (Option (Fin L → Fin L)) × Graph (Fin L → Fin L) =>
        p.2.edges.all fun e =>
          decide (e.constraint (tableVal (p.1.getD e.src none)) = tableVal (p.1.getD e.dst none)))
      (encPair (encUGTable L) (encUGGraph L)) encBool
  refine allWithInput (by fun_prop) ?_
  have hval : ComputableInPolyTime (tableVal (L := L))
      (encOption (encUGFn L)) (encFinEnum (Fin L)) := of_finite _
  have hchk : ComputableInPolyTime
      (fun r : (Fin L → Fin L) × (Fin L × Fin L) => decide (r.1 r.2.1 = r.2.2))
      (encPair (encUGFn L) (encPair (encFinEnum (Fin L)) (encFinEnum (Fin L)))) encBool :=
    of_finite _
  refine hchk.comp ((Edge.isPolyTime_constraint (snd' id')).prod
    ((hval.comp ((listGetD (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
      ((fst' (fst' id')).prod (Edge.isPolyTime_src (snd' id'))))).prod
     (hval.comp ((listGetD (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
      ((fst' (fst' id')).prod (Edge.isPolyTime_dst (snd' id')))))))

end PolyTime

/-- Label propagation over `List.finRange L` is polynomial-time computable in the multi-tape
Turing machine model under the `UniqueGamesConjecture` graph encoding. -/
theorem computableInPolyTime_isSome_solve (L : ℕ) [NeZero L] :
    ComputableInPolyTime (fun g : Graph (Fin L → Fin L) => (solve (List.finRange L) g).isSome)
      (Graph.encoding (encPi (encFinEnum (Fin L)))) encBool := by
  simpa only [Function.comp_def, checkTable_run_eq_isSome_solve, encUGGraph, encUGFn] using
    (poly_checkTable L).comp ((poly_state_table (poly_run L)).prod .id')

end Cslib.Complexity.UniqueGames.Propagation

namespace Cslib.Complexity

open Cslib.Complexity.UniqueGames.Propagation Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- For `0 < L`, `GapUniqueGames (Fin L) 1 s` is in `PromiseP` under the encoding of
`UniqueGamesConjecture`, via label propagation over `List.finRange L`. -/
theorem gapUniqueGames_one_mem_PromiseP_of_pos {L : ℕ} (hL : 0 < L) (s : ℝ) :
    GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L)))) := by
  have : NeZero L := ⟨hL.ne'⟩
  exact mem_PromiseP_iff.2 ⟨_, computableInPolyTime_isSome_solve L,
    solvedBy_gapUniqueGames_one (fun a => List.mem_finRange a) s⟩

/-- Over `Fin 0`, no labelling `ℕ → Fin 0` exists, so no graph is satisfiable. -/
theorem not_satisfiable_fin_zero (g : Graph (Fin 0 → Fin 0)) :
    ¬ (g.toGraph permutationEval).Satisfiable := by
  rintro ⟨σ, _⟩
  exact Fin.elim0 (σ 0)

/-- Over `Fin 0`, the empty infimum gives `unsatVal = 0`, so every unique game is a yes-instance
of `GapUniqueGames (Fin 0) 1 s`. -/
theorem gapUniqueGames_zero_yes (s : ℝ) :
    (GapUniqueGames (Fin 0) 1 s).yes = {g : Graph (Fin 0 → Fin 0) | IsUniqueGame g} := by
  ext g
  simp [GapUniqueGames, PromiseProblem.restrict, ConstraintGraph.unsatVal]

/-- Over `Fin 0`, `GapUniqueGames (Fin 0) 1 s` has no no-instances: every unique game has value
`1`, which cannot simultaneously satisfy `1 ≤ s` and `s < 1`. -/
theorem gapUniqueGames_zero_no (s : ℝ) :
    (GapUniqueGames (Fin 0) 1 s).no = ∅ := by
  ext g
  simp only [GapUniqueGames, PromiseProblem.restrict, PromiseProblem.gapMax,
    ConstraintGraph.unsatVal, Real.iInf_of_isEmpty, sub_zero, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, _⟩
  exact h1.not_gt h2

/-- `GapUniqueGames (Fin 0) 1 s ∈ PromiseP`: every unique game is a yes-instance and there are
no no-instances, so the constant-`true` decider solves the promise problem. -/
theorem gapUniqueGames_zero_mem_PromiseP (s : ℝ) :
    GapUniqueGames (Fin 0) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin 0)))) := by
  refine mem_PromiseP_iff.2 ⟨fun _ => true, .const true, fun g _ => rfl, fun g hg => ?_⟩
  rw [gapUniqueGames_zero_no] at hg
  exact hg.elim

/-- For every alphabet size `L : ℕ` and soundness threshold `s : ℝ`, `GapUniqueGames (Fin L) 1 s`
belongs to `PromiseP` under the encoding used by `UniqueGamesConjecture`. -/
theorem gapUniqueGames_one_mem_PromiseP (L : ℕ) (s : ℝ) :
    GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L)))) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact gapUniqueGames_zero_mem_PromiseP s
  · exact gapUniqueGames_one_mem_PromiseP_of_pos hL s

private def isUniqueGameBool (L : ℕ) (g : Graph (Fin L → Fin L)) : Bool :=
  g.edges.all fun e => decide (Function.Bijective e.constraint)

private theorem isUniqueGameBool_eq_true (L : ℕ) (g : Graph (Fin L → Fin L)) :
    isUniqueGameBool L g = true ↔ IsUniqueGame g := by
  simp [isUniqueGameBool, IsUniqueGame]

private theorem computableInPolyTime_isUniqueGameBool (L : ℕ) :
    ComputableInPolyTime (isUniqueGameBool L)
      (Graph.encoding (encPi (encFinEnum (Fin L)))) encBool := by
  refine ComputableInPolyTime.allWithInput (Graph.isPolyTime_edges .id') ?_
  exact (ComputableInPolyTime.of_finite
    (fun f : Fin L → Fin L => decide (Function.Bijective f))).comp (by fun_prop)

/-- Checking `IsUniqueGame` belongs to `P` for every fixed alphabet size `L`. -/
theorem isUniqueGame_mem_P (L : ℕ) :
    {g : Graph (Fin L → Fin L) | IsUniqueGame g} ∈
      P (Graph.encoding (encPi (encFinEnum (Fin L)))) :=
  ⟨isUniqueGameBool L, computableInPolyTime_isUniqueGameBool L,
    fun g => (isUniqueGameBool_eq_true L g).symm⟩

/-- Deciding satisfiability of unique games belongs to `P` for every fixed alphabet size `L`. -/
theorem satisfiable_uniqueGame_mem_P (L : ℕ) :
    {g : Graph (Fin L → Fin L) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} ∈
      P (Graph.encoding (encPi (encFinEnum (Fin L)))) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · suffices {g : Graph (Fin 0 → Fin 0) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable}
        = ∅ by
      rw [this]
      exact empty_mem_P
    ext g
    simp [not_satisfiable_fin_zero g]
  · have : NeZero L := ⟨hL.ne'⟩
    refine ⟨fun g => isUniqueGameBool L g && (solve (List.finRange L) g).isSome, ?_, fun g => ?_⟩
    · exact ComputableInPolyTime.bool_and.comp
        ((computableInPolyTime_isUniqueGameBool L).prod (computableInPolyTime_isSome_solve L))
    · simp only [Set.mem_ofPred_eq, Bool.and_eq_true, isUniqueGameBool_eq_true,
        and_congr_right_iff]
      intro hg
      exact (solve_isSome_iff (fun a => List.mem_finRange a) hg).symm

end Cslib.Complexity
