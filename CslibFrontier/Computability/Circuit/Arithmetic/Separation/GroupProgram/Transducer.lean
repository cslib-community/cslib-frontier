/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Lists
public import CslibFrontier.Foundations.Data.List.Weighted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Ring

/-!
# Transducers of the group program

A *transducer* has a finite control, `nI` input lists of bits and `nO` output lists of letters. In
every step it reads the first bit of every input list (`false` at the end of a list) and removes
it, and its table gives, for the control and the bits read, a list of *choices*: a choice has a
weight, which is a term in the named constants of the ring, the next control, and a constant word
for every output list, which is pushed on it. The outcomes of a run are a weighted list of states
(`List.weightedFoldl`).

One formula of the tree machine runs a transducer for any number of steps, at constant cost a
step. The loops of the evaluator of [AnthropicVPVNP2026] that guess letters or bits and multiply
by entries of a matrix or of a node tensor are such runs.

This is a device of the interpreter and not a general notion of automata. A weighted automaton
(`Cslib.Automata.Weighted.Rep`, a linear representation with its series `List Ω → F`) has weights
in the ring and assigns a number to a word; here the weights are terms (`Interpreter.WE`), which a
formula can multiply by, the semantics is the weighted list of the states after a given number of
steps, as `Interpreter.Does` needs it, and the input lists are read together and padded by
`false`. The class `Cslib.Automata.Transducer` is a relation between words, without weights.

## Main definitions

* `Transducer.Choice`: a choice, with its `weight`, the `next` control and the words to `push`.
* `Transducer.State`: a state, with its `control`, `inputs` and `outputs`.
* `Transducer.State.enc`: a state as a tree.
* `Transducer.Choice.apply`: the state after a choice.
* `Transducer.step`, `Transducer.run`: the weighted lists of one step and of `k` steps.

## Main results

* `Transducer.exists_formula_run`: one formula runs a transducer, in time linear in the number of
  steps.
* `Transducer.mem_run_induction`: an invariant of the steps holds at every outcome of a run.
* `Transducer.weightedSum_run_succ`: one more step of a run, as a sum over the choices.
* `Transducer.exists_length_le_of_mem_run`: the output lists grow by a constant a step.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3 (the evaluator in the proof of
Theorem J.3); module `Nc.Grp.Trans`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

namespace Transducer

/-- A choice of a transducer with `nC` controls and `nO` output lists of letters in `Λ`. -/
structure Choice (nC nO : ℕ) (Λ : Type) where
  /-- The weight, a term in the named constants. -/
  weight : WE
  /-- The next control. -/
  next : Fin nC
  /-- The words that are pushed on the output lists. -/
  push : Fin nO → List Λ

/-- A state of a transducer with `nC` controls, `nI` input lists of bits and `nO` output lists of
letters in `Λ`. -/
structure State (nC nI nO : ℕ) (Λ : Type) where
  /-- The control. -/
  control : Fin nC
  /-- The input lists. -/
  inputs : Fin nI → List Bool
  /-- The output lists. -/
  outputs : Fin nO → List Λ

variable {A : Type} [CommRing A] {θ : List Bool → A} {Λ : Type} {nC nI nO : ℕ}

/-- A state as a tree: the control as a number, the list of the input lists, and the list of the
output lists, whose letters are encoded by `eL`. -/
@[expose] def State.enc (eL : Λ → Tree) (s : State nC nI nO Λ) : Tree :=
  .cons (num s.control) (.cons (listT (List.ofFn fun i => ofBits (s.inputs i)))
    (listT (List.ofFn fun j => listT ((s.outputs j).map eL))))

/-- The state after a choice: the first bit of every input list is removed, and the words of the
choice are pushed on the output lists. -/
@[expose] def Choice.apply (o : Choice nC nO Λ) (s : State nC nI nO Λ) : State nC nI nO Λ where
  control := o.next
  inputs i := (s.inputs i).tail
  outputs j := o.push j ++ s.outputs j

/-- One step of the transducer with the table `tab`: the choices at the control and the first bits
of the input lists, with the values of their weights. -/
@[expose] def step (θ : List Bool → A) (tab : Fin nC → (Fin nI → Bool) → List (Choice nC nO Λ))
    (s : State nC nI nO Λ) : List (A × State nC nI nO Λ) :=
  (tab s.control fun i => (s.inputs i).headD false).map fun o => (o.weight.val θ, o.apply s)

/-- A run of `k` steps. -/
@[expose] def run (θ : List Bool → A) (tab : Fin nC → (Fin nI → Bool) → List (Choice nC nO Λ))
    (k : ℕ) (s : State nC nI nO Λ) : List (A × State nC nI nO Λ) :=
  (List.replicate k ()).weightedFoldl (fun _ s => step θ tab s) s

variable {tab : Fin nC → (Fin nI → Bool) → List (Choice nC nO Λ)}

theorem run_zero (s : State nC nI nO Λ) : run θ tab 0 s = [(1, s)] := rfl

theorem run_succ (k : ℕ) (s : State nC nI nO Λ) :
    run θ tab (k + 1) s = (step θ tab s).weightedBind (run θ tab k) := rfl

/-- One more step of a run, from a state at which the table lists the choices `ch z` of a finite
type: the sum over these choices of their weight times the run after them. -/
theorem weightedSum_run_succ {Z : Type} [Fintype Z] (ch : Z → Choice nC nO Λ)
    {s : State nC nI nO Λ}
    (hs : tab s.control (fun i => (s.inputs i).headD false) =
      (Finset.univ : Finset Z).toList.map ch)
    (k : ℕ) (G : State nC nI nO Λ → A) :
    (run θ tab (k + 1) s).weightedSum G =
      ∑ z, (ch z).weight.val θ * (run θ tab k ((ch z).apply s)).weightedSum G := by
  rw [run_succ, List.weightedSum_weightedBind, step, hs, List.map_map, List.weightedSum,
    List.map_map]
  exact Finset.sum_map_toList _ _

/-- An invariant of the steps, with a counter of the steps, holds at every outcome of a run. -/
theorem mem_run_induction {Inv : ℕ → State nC nI nO Λ → Prop} {k m : ℕ} {s : State nC nI nO Λ}
    (h : ∀ s m, Inv m s → ∀ q ∈ step θ tab s, Inv (m + 1) q.2) (hs : Inv m s) :
    ∀ q ∈ run θ tab k s, Inv (m + k) q.2 := by
  have := List.mem_weightedFoldl_induction (xs := List.replicate k ()) (fun _ _ => h) hs
  rwa [List.length_replicate] at this

variable (eL : Λ → Tree)

/-- An input list of a state. -/
private theorem gives_input (s : State nC nI nO Λ) (i : Fin nI) :
    Gives θ (nthF i (.hd (.tl .id))) (s.enc eL) (ofBits (s.inputs i)) (3 + nI) :=
  nthF_gives_ofFn (o := fun i => ofBits (s.inputs i)) i (Gives.id _).tl.hd

/-- An output list of a state. -/
private theorem gives_output (s : State nC nI nO Λ) (j : Fin nO) :
    Gives θ (nthF j (.tl (.tl .id))) (s.enc eL) (listT ((s.outputs j).map eL)) (3 + nO) :=
  nthF_gives_ofFn (o := fun j => listT ((s.outputs j).map eL)) j (Gives.id _).tl.tl

/-- A formula for one choice. -/
private theorem exists_formula_choice (o : Choice nC nO Λ) : ∃ F κ, ∀ s : State nC nI nO Λ,
    Does θ F (s.enc eL) [(o.weight.val θ, (o.apply s).enc eL)] κ :=
  ⟨.ite o.weight.fm .fail (.cons (.quote (num o.next)) (.cons
    (listF (List.ofFn fun i : Fin nI => .tl (nthF i (.hd (.tl .id)))))
    (listF (List.ofFn fun j : Fin nO => pushF ((o.push j).map eL) (nthF j (.tl (.tl .id))))))),
    _, fun s => by
    have h1 : Gives θ (listF (List.ofFn fun i : Fin nI => .tl (nthF i (.hd (.tl .id)))))
        (s.enc eL) (listT (List.ofFn fun i => ofBits (s.inputs i).tail)) _ :=
      listF_gives fun i => tl_ofBits _ ▸ (gives_input eL s i).tl
    have h2 : Gives θ
        (listF (List.ofFn fun j : Fin nO => pushF ((o.push j).map eL) (nthF j (.tl (.tl .id)))))
        (s.enc eL) (listT (List.ofFn fun j => listT ((o.push j ++ s.outputs j).map eL))) _ :=
      listF_gives fun j => List.map_append ▸
        (pushF_gives ((o.push j).map eL) (gives_output eL s j)).mono
          (Nat.add_le_add_left (Finset.le_sup (f := fun j => 2 * ((o.push j).map eL).length)
            (Finset.mem_univ j)) _)
    exact (Does.ite_nil (o.weight.does (s.enc eL))
      ((Gives.quote _ _).cons (h1.cons h2))).of_eq (by simp [State.enc, Choice.apply])⟩

/-- A formula for the choices of a list. -/
private theorem exists_formula_choices (os : List (Choice nC nO Λ)) :
    ∃ F κ, ∀ s : State nC nI nO Λ,
      Does θ F (s.enc eL) (os.map fun o => (o.weight.val θ, (o.apply s).enc eL)) κ := by
  induction os with
  | nil => exact ⟨.fail, 0, fun s => Does.fail _⟩
  | cons o os ih =>
    obtain ⟨F, κ, h⟩ := ih
    obtain ⟨G, κ', h'⟩ := exists_formula_choice (θ := θ) (nI := nI) eL o
    exact ⟨.ite .guess G F, max κ' κ + 2, fun s => Does.either (h' s) (h s)⟩

/-- A formula for one step. -/
private theorem exists_formula_step (tab : Fin nC → (Fin nI → Bool) → List (Choice nC nO Λ)) :
    ∃ F κ, ∀ s : State nC nI nO Λ,
      Does θ F (s.enc eL) ((step θ tab s).map (Prod.map id (State.enc eL))) κ := by
  choose F κ h using fun z : Fin nC × (Fin nI → Bool) =>
    exists_formula_choices (θ := θ) (nI := nI) eL (tab z.1 z.2)
  refine ⟨switchF (.hd .id) (List.ofFn fun c : Fin nC =>
    dispF nI (fun i => .hd (nthF i (.hd (.tl .id)))) fun v => F (c, v)),
    (nC + 1) * (2 + nC + 1) + (nI * (3 + nI + 1 + 1) + Finset.univ.sup κ), fun s => ?_⟩
  have h1 := dispF_does (g := fun i => .hd (nthF i (.hd (.tl .id))))
    (k := fun v => F (s.control, v)) (v := fun i => (s.inputs i).headD false)
    (fun i => hd_ofBits _ ▸ (gives_input eL s i).hd)
    ((h (s.control, fun i => (s.inputs i).headD false) s).mono
      (Finset.le_sup (Finset.mem_univ _)))
  refine ((switchF_does (Gives.id (s.enc eL)).hd (by simp) h1).of_eq ?_).mono
    (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) _)
  simp [step, Function.comp_def]

/-- **One formula runs a transducer**: at the pair of the number `k` of steps and a state, its
weighted list of values is the list of the encodings of the outcomes of the run of `k` steps, and
its cost is linear in `k`. -/
theorem exists_formula_run (tab : Fin nC → (Fin nI → Bool) → List (Choice nC nO Λ)) :
    ∃ F κ, ∀ (k : ℕ) (s : State nC nI nO Λ),
      Does θ F (.cons (num k) (s.enc eL)) ((run θ tab k s).map (Prod.map id (State.enc eL)))
        (κ * (k + 1)) := by
  obtain ⟨F, κ, h⟩ := exists_formula_step (θ := θ) eL tab
  refine ⟨foldF (lett (.tl .id) F) (.tl .id) (.hd .id), κ + 60, fun k s => ?_⟩
  have h1 : Gives θ (.hd .id) (.cons (num k) (s.enc eL))
      (listT ((List.replicate k ()).map fun _ => .nil)) 2 := by
    rw [List.map_replicate, ← num_eq_listT_replicate]
    exact (Gives.id _).hd
  refine (foldF_does_enc (enc := State.enc eL) (f := fun _ s => step θ tab s)
    (Inv := fun _ _ => True) (d := fun _ => κ + 4) (Gives.id _).tl h1
    (fun _ _ s _ _ => ⟨(Does.of_gives (Gives.id _).tl (h s)).mono (by omega), fun _ _ => trivial⟩)
    trivial).mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

/-- The output lists of a run from empty output lists grow by a constant a step. -/
theorem exists_length_le_of_mem_run (tab : Fin nC → (Fin nI → Bool) → List (Choice nC nO Λ)) :
    ∃ κ, ∀ (k : ℕ) (s : State nC nI nO Λ), (∀ j, s.outputs j = []) →
      ∀ q ∈ run θ tab k s, ∀ j, (q.2.outputs j).length ≤ κ * k := by
  let g : Fin nC × (Fin nI → Bool) → ℕ := fun z =>
    ((tab z.1 z.2).map fun o => Finset.univ.sup fun j => (o.push j).length).foldr max ⊥
  have hg : ∀ c v, ∀ o ∈ tab c v, ∀ j, (o.push j).length ≤ Finset.univ.sup g :=
    fun c v o ho j => (List.le_max_of_le (List.mem_map_of_mem ho)
      (Finset.le_sup (f := fun j => (o.push j).length) (Finset.mem_univ j))).trans
      (Finset.le_sup (f := g) (Finset.mem_univ (c, v)))
  refine ⟨Finset.univ.sup g, fun k s hs q hq j => ?_⟩
  simpa using mem_run_induction (m := 0)
    (Inv := fun m s => ∀ j, (s.outputs j).length ≤ Finset.univ.sup g * m)
    (fun s m hm q hq j => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hq
      have := hg _ _ o ho j
      have := hm j
      simp only [Choice.apply, List.length_append, Nat.mul_succ]
      omega) (fun j => by simp [hs j]) q hq j

end Transducer

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
