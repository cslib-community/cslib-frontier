/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.Game.AlphaBeta
public import Cslib.Algorithms.Lean.Query.FreeM
import Cslib.Foundations.Control.Monad.IsMonadHom.List

/-!
# Minimax and alpha-beta search in the query model

The interface of a game is a query type (`GameQuery`): a search algorithm learns about a game only
by asking whether a state is terminal, for its utility or heuristic evaluation, for the player to
move, for its legal moves and for the result of a move. Depth-limited minimax (`minimaxM`, the
textbook's H-MINIMAX), fail-hard alpha-beta (`alphaBetaHardM`) and fail-soft alpha-beta
(`alphaBetaSoftM`, the textbook's `ALPHA-BETA-SEARCH` with a depth cut-off) are written once, as
programs in an arbitrary monad against an interpretation `q` of these queries, in the manner of
`List.mergeSortM`. They search the game from a state `s` to a depth `n`, visiting the moves in the
order of `actions`.

* Interpreting the queries by a game `g` and an evaluation function `eval` in a lawful monad, the
  programs compute the tree algorithms of `CslibFrontier.Algorithms.Lean.Search.Game.Minimax` and
  `CslibFrontier.Algorithms.Lean.Search.Game.AlphaBeta` on the unfolded tree `g.unfold eval n s`
  (`minimaxM_pure`, `alphaBetaHardM_pure`, `alphaBetaSoftM_pure`); with `m = Id` these are the
  pure algorithms.
* Interpreted in `FreeM (GameQuery S A U)` by `FreeM.lift` (`minimaxQ`, `alphaBetaHardQ`,
  `alphaBetaSoftQ`), they are query programs whose number of queries along the path that an
  oracle determines is `FreeM.countQueries`, and the oracle's answers are read off by `FreeM.eval`
  (`eval_minimaxQ`, `eval_alphaBetaHardQ`, `eval_alphaBetaSoftQ`). Any monad morphism commutes
  with the programs (`Cslib.IsMonadHom.map_minimaxM` and its siblings), which is how evaluation
  transfers.

The pruning theorem is the query-model statement that alpha-beta never does more work than
minimax: for every oracle and every weighting of the queries by natural numbers, the weighted
query cost (`FreeM.cost`) of alpha-beta search, fail-hard or fail-soft and with any window, is at
most that of minimax search to the same depth (`cost_alphaBetaHardQ_le_cost_minimaxQ`,
`cost_alphaBetaSoftQ_le_cost_minimaxQ`). With unit weights this bounds the number of queries
(`FreeM.countQueries_eq_cost_one`), and with weight one on `utility` and `eval` queries and zero
on the others it bounds the number of leaves evaluated. The bound holds for every oracle, not
only for those coming from a game; the tests exhibit a game where alpha-beta makes strictly fewer
queries. As with all query bounds, pure computation is not charged: this is not a running-time
claim.

## Main definitions

* `Cslib.Algorithms.Lean.Search.GameQuery`: the queries a search algorithm makes about a game.
* `Cslib.Algorithms.Lean.Search.Game.oracle`: the oracle answering queries from a game and an
  evaluation function.
* `Cslib.Algorithms.Lean.Search.minimaxM`, `Cslib.Algorithms.Lean.Search.alphaBetaHardM`,
  `Cslib.Algorithms.Lean.Search.alphaBetaSoftM`: monad-polymorphic depth-limited minimax and
  alpha-beta search; `minimaxQ`, `alphaBetaHardQ` and `alphaBetaSoftQ` are their query programs.

## Main results

* `Cslib.Algorithms.Lean.Search.eval_minimaxQ`, `Cslib.Algorithms.Lean.Search.eval_alphaBetaHardQ`,
  `Cslib.Algorithms.Lean.Search.eval_alphaBetaSoftQ`: evaluating the query programs against
  `g.oracle eval` gives the tree algorithms on `g.unfold eval n s`; with
  `GameTree.alphaBetaHard_eq` and its fail-soft counterparts, alpha-beta search of a game computes
  depth-limited minimax as specified.
* `Cslib.Algorithms.Lean.Search.cost_alphaBetaHardQ_le_cost_minimaxQ`,
  `Cslib.Algorithms.Lean.Search.cost_alphaBetaSoftQ_le_cost_minimaxQ`: alpha-beta search has at
  most the weighted query cost of minimax search, for every oracle.

## References

* [S. Russell, P. Norvig, *Artificial Intelligence: A Modern Approach*][RussellNorvig2020],
  Sections 5.2 and 5.3.
-/

public section

namespace Cslib.Algorithms.Lean.Search

/-- The queries a search algorithm makes about a game with states `S`, moves `A` and utilities
`U`, each indexed by the type of its answer. -/
inductive GameQuery (S A U : Type) : Type → Type where
  /-- Is the state terminal? -/
  | isTerminal (s : S) : GameQuery S A U Bool
  /-- The utility of a (terminal) state for MAX. -/
  | utility (s : S) : GameQuery S A U U
  /-- The heuristic evaluation of a (non-terminal) state for MAX, used at the depth cut-off. -/
  | eval (s : S) : GameQuery S A U U
  /-- The player to move in a state. -/
  | toMove (s : S) : GameQuery S A U Player
  /-- The legal moves in a state. -/
  | actions (s : S) : GameQuery S A U (List A)
  /-- The state resulting from a move. -/
  | result (s : S) (a : A) : GameQuery S A U S

/-- The oracle answering game queries from the game `g` and the evaluation function `eval`. -/
@[expose] def Game.oracle {S A U : Type} (g : Game S A U) (eval : S → U) :
    {ι : Type} → GameQuery S A U ι → ι
  | _, .isTerminal s => g.isTerminal s
  | _, .utility s => g.utility s
  | _, .eval s => eval s
  | _, .toMove s => g.toMove s
  | _, .actions s => g.actions s
  | _, .result s a => g.result s a

section Oracle

variable {S A U : Type} (g : Game S A U) (eval : S → U)

@[simp] theorem Game.oracle_isTerminal (s : S) : g.oracle eval (.isTerminal s) = g.isTerminal s :=
  rfl

@[simp] theorem Game.oracle_utility (s : S) : g.oracle eval (.utility s) = g.utility s := rfl

@[simp] theorem Game.oracle_eval (s : S) : g.oracle eval (.eval s) = eval s := rfl

@[simp] theorem Game.oracle_toMove (s : S) : g.oracle eval (.toMove s) = g.toMove s := rfl

@[simp] theorem Game.oracle_actions (s : S) : g.oracle eval (.actions s) = g.actions s := rfl

@[simp] theorem Game.oracle_result (s : S) (a : A) : g.oracle eval (.result s a) = g.result s a :=
  rfl

end Oracle

variable {S A U : Type} [LinearOrder U]

section Programs

variable {m : Type → Type*} [Monad m] (q : {ι : Type} → GameQuery S A U ι → m ι)

/-- Depth-limited minimax search (H-MINIMAX, [RussellNorvig2020], Section 5.3) from the state `s`
with `n` moves to go, against the interpretation `q` of the game queries: a terminal state is
worth its utility, a non-terminal state at depth `0` its heuristic evaluation, and any other state
the largest (for MAX to move) or smallest (for MIN) value of the states its moves lead to, folded
from `⊥` (or `⊤`) over the moves in order. -/
@[expose] def minimaxM [BoundedOrder U] : ℕ → S → m U
  | 0, s => do if ← q (.isTerminal s) then q (.utility s) else q (.eval s)
  | n + 1, s => do
    if ← q (.isTerminal s) then q (.utility s)
    else do
      let p ← q (.toMove s)
      let as ← q (.actions s)
      match p with
      | .max => as.foldlM (fun v a => do return max v (← minimaxM n (← q (.result s a)))) ⊥
      | .min => as.foldlM (fun v a => do return min v (← minimaxM n (← q (.result s a)))) ⊤

/-- The moves `as` of a node of MAX at the state `s` in fail-hard alpha-beta search with the window
`[a, b]`, where `child` searches a successor state: each move's result is searched with the current
window and its value raises `a`, until `a` reaches `b`. -/
@[expose] def alphaBetaHardMaxM (child : U → U → S → m U) (s : S) (a b : U) : List A → m U
  | [] => pure a
  | x :: as => do
    let a' := max a (← child a b (← q (.result s x)))
    if b ≤ a' then pure a' else alphaBetaHardMaxM child s a' b as

/-- The moves `as` of a node of MIN at the state `s` in fail-hard alpha-beta search with the window
`[a, b]`, where `child` searches a successor state: each move's result is searched with the current
window and its value lowers `b`, until `b` reaches `a`. -/
@[expose] def alphaBetaHardMinM (child : U → U → S → m U) (s : S) (a b : U) : List A → m U
  | [] => pure b
  | x :: as => do
    let b' := min b (← child a b (← q (.result s x)))
    if b' ≤ a then pure b' else alphaBetaHardMinM child s a b' as

/-- Depth-limited fail-hard alpha-beta search from the state `s` with `n` moves to go and the window
`[a, b]`, against the interpretation `q` of the game queries; leaf values are clamped into the
window. -/
@[expose] def alphaBetaHardM : ℕ → U → U → S → m U
  | 0, a, b, s => do
    let x ← if ← q (.isTerminal s) then q (.utility s) else q (.eval s)
    return max a (min x b)
  | n + 1, a, b, s => do
    if ← q (.isTerminal s) then return max a (min (← q (.utility s)) b)
    else do
      let p ← q (.toMove s)
      let as ← q (.actions s)
      match p with
      | .max => alphaBetaHardMaxM q (alphaBetaHardM n) s a b as
      | .min => alphaBetaHardMinM q (alphaBetaHardM n) s a b as

/-- The moves `as` of a node of MAX at the state `s` in fail-soft alpha-beta search with the window
`[a, b]` and best value `v` so far (`MAX-VALUE`), where `child` searches a successor state: each
move's result is searched with the current window and its value raises `v` and `a`, until `v`
reaches `b`. -/
@[expose] def alphaBetaSoftMaxM (child : U → U → S → m U) (s : S) (a b v : U) : List A → m U
  | [] => pure v
  | x :: as => do
    let v' := max v (← child a b (← q (.result s x)))
    if b ≤ v' then pure v' else alphaBetaSoftMaxM child s (max a v') b v' as

/-- The moves `as` of a node of MIN at the state `s` in fail-soft alpha-beta search with the window
`[a, b]` and best value `v` so far (`MIN-VALUE`), where `child` searches a successor state: each
move's result is searched with the current window and its value lowers `v` and `b`, until `v`
reaches `a`. -/
@[expose] def alphaBetaSoftMinM (child : U → U → S → m U) (s : S) (a b v : U) : List A → m U
  | [] => pure v
  | x :: as => do
    let v' := min v (← child a b (← q (.result s x)))
    if v' ≤ a then pure v' else alphaBetaSoftMinM child s a (min b v') v' as

/-- Depth-limited fail-soft alpha-beta search (`ALPHA-BETA-SEARCH` with a depth cut-off,
[RussellNorvig2020], Sections 5.2.3 and 5.3) from the state `s` with `n` moves to go and the window
`[a, b]`, against the interpretation `q` of the game queries. -/
@[expose] def alphaBetaSoftM [BoundedOrder U] : ℕ → U → U → S → m U
  | 0, _, _, s => do if ← q (.isTerminal s) then q (.utility s) else q (.eval s)
  | n + 1, a, b, s => do
    if ← q (.isTerminal s) then q (.utility s)
    else do
      let p ← q (.toMove s)
      let as ← q (.actions s)
      match p with
      | .max => alphaBetaSoftMaxM q (alphaBetaSoftM n) s a b ⊥ as
      | .min => alphaBetaSoftMinM q (alphaBetaSoftM n) s a b ⊤ as

end Programs

/-- Depth-limited minimax search as a query program. -/
abbrev minimaxQ [BoundedOrder U] (n : ℕ) (s : S) : FreeM (GameQuery S A U) U :=
  minimaxM FreeM.lift n s

/-- Depth-limited fail-hard alpha-beta search as a query program. -/
abbrev alphaBetaHardQ (n : ℕ) (a b : U) (s : S) : FreeM (GameQuery S A U) U :=
  alphaBetaHardM FreeM.lift n a b s

/-- Depth-limited fail-soft alpha-beta search as a query program. -/
abbrev alphaBetaSoftQ [BoundedOrder U] (n : ℕ) (a b : U) (s : S) : FreeM (GameQuery S A U) U :=
  alphaBetaSoftM FreeM.lift n a b s

/-! ## Transfer along monad morphisms -/

section Transfer

variable {m n : Type → Type*} [Monad m] [Monad n] {f : {β : Type} → m β → n β}

private theorem map_alphaBetaHardMaxM (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (child : U → U → S → m U) (s : S) (a b : U)
    (as : List A) :
    f (alphaBetaHardMaxM q child s a b as) =
      alphaBetaHardMaxM (fun op => f (q op)) (fun a b s => f (child a b s)) s a b as := by
  induction as generalizing a with
  | nil => simp [alphaBetaHardMaxM, hf.map_pure]
  | cons x as ih => simp [alphaBetaHardMaxM, hf.map_bind, apply_ite f, hf.map_pure, ih]

private theorem map_alphaBetaHardMinM (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (child : U → U → S → m U) (s : S) (a b : U)
    (as : List A) :
    f (alphaBetaHardMinM q child s a b as) =
      alphaBetaHardMinM (fun op => f (q op)) (fun a b s => f (child a b s)) s a b as := by
  induction as generalizing b with
  | nil => simp [alphaBetaHardMinM, hf.map_pure]
  | cons x as ih => simp [alphaBetaHardMinM, hf.map_bind, apply_ite f, hf.map_pure, ih]

private theorem map_alphaBetaSoftMaxM (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (child : U → U → S → m U) (s : S) (a b v : U)
    (as : List A) :
    f (alphaBetaSoftMaxM q child s a b v as) =
      alphaBetaSoftMaxM (fun op => f (q op)) (fun a b s => f (child a b s)) s a b v as := by
  induction as generalizing a v with
  | nil => simp [alphaBetaSoftMaxM, hf.map_pure]
  | cons x as ih => simp [alphaBetaSoftMaxM, hf.map_bind, apply_ite f, hf.map_pure, ih]

private theorem map_alphaBetaSoftMinM (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (child : U → U → S → m U) (s : S) (a b v : U)
    (as : List A) :
    f (alphaBetaSoftMinM q child s a b v as) =
      alphaBetaSoftMinM (fun op => f (q op)) (fun a b s => f (child a b s)) s a b v as := by
  induction as generalizing b v with
  | nil => simp [alphaBetaSoftMinM, hf.map_pure]
  | cons x as ih => simp [alphaBetaSoftMinM, hf.map_bind, apply_ite f, hf.map_pure, ih]

/-- A monad morphism commutes with depth-limited minimax search. -/
theorem _root_.Cslib.IsMonadHom.map_minimaxM [BoundedOrder U] (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (d : ℕ) (s : S) :
    f (minimaxM q d s) = minimaxM (fun op => f (q op)) d s := by
  induction d generalizing s with
  | zero => simp [minimaxM, hf.map_bind, apply_ite f]
  | succ d ih =>
    simp only [minimaxM, hf.map_bind, apply_ite f]
    congr 1; funext t; congr 1; congr 1; funext p; congr 1; funext as
    cases p <;> simp [hf.map_listFoldlM, hf.map_bind, hf.map_pure, ih]

/-- A monad morphism commutes with depth-limited fail-hard alpha-beta search. -/
theorem _root_.Cslib.IsMonadHom.map_alphaBetaHardM (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (d : ℕ) (a b : U) (s : S) :
    f (alphaBetaHardM q d a b s) = alphaBetaHardM (fun op => f (q op)) d a b s := by
  induction d generalizing a b s with
  | zero => simp [alphaBetaHardM, hf.map_bind, apply_ite f, hf.map_pure]
  | succ d ih =>
    simp only [alphaBetaHardM, hf.map_bind, apply_ite f, hf.map_pure]
    congr 1; funext t; congr 1; congr 1; funext p; congr 1; funext as
    cases p <;> simp [map_alphaBetaHardMaxM hf, map_alphaBetaHardMinM hf, ih]

/-- A monad morphism commutes with depth-limited fail-soft alpha-beta search. -/
theorem _root_.Cslib.IsMonadHom.map_alphaBetaSoftM [BoundedOrder U] (hf : IsMonadHom m n f)
    (q : {ι : Type} → GameQuery S A U ι → m ι) (d : ℕ) (a b : U) (s : S) :
    f (alphaBetaSoftM q d a b s) = alphaBetaSoftM (fun op => f (q op)) d a b s := by
  induction d generalizing a b s with
  | zero => simp [alphaBetaSoftM, hf.map_bind, apply_ite f]
  | succ d ih =>
    simp only [alphaBetaSoftM, hf.map_bind, apply_ite f]
    congr 1; funext t; congr 1; congr 1; funext p; congr 1; funext as
    cases p <;> simp [map_alphaBetaSoftMaxM hf, map_alphaBetaSoftMinM hf, ih]

end Transfer

/-! ## Evaluation -/

section Pure

variable {m : Type → Type*} [Monad m] [LawfulMonad m]

private theorem foldl_max_eq_maxValue [BoundedOrder U] {β : Type} (h : β → GameTree U) (v : U)
    (l : List β) : l.foldl (fun v x => max v (h x).minimax) v = GameTree.maxValue v (l.map h) := by
  induction l generalizing v with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem foldl_min_eq_minValue [BoundedOrder U] {β : Type} (h : β → GameTree U) (v : U)
    (l : List β) : l.foldl (fun v x => min v (h x).minimax) v = GameTree.minValue v (l.map h) := by
  induction l generalizing v with
  | nil => simp
  | cons x l ih => simp [ih]

/-- Minimax search, with the queries answered by a game and an evaluation function in a lawful
monad, is minimax on the unfolded game tree. -/
theorem minimaxM_pure [BoundedOrder U] (g : Game S A U) (eval : S → U) (d : ℕ) (s : S) :
    minimaxM (m := m) (fun op => pure (g.oracle eval op)) d s =
      pure (g.unfold eval d s).minimax := by
  induction d generalizing s with
  | zero => cases h : g.isTerminal s <;> simp [minimaxM, Game.unfold, h]
  | succ d ih =>
    cases h : g.isTerminal s
    · cases hp : g.toMove s <;>
        simp [minimaxM, Game.unfold, h, hp, ih, foldl_max_eq_maxValue,
          foldl_min_eq_minValue]
    · simp [minimaxM, Game.unfold, h]

private theorem alphaBetaHardMaxM_pure (o : {ι : Type} → GameQuery S A U ι → ι)
    (h : S → GameTree U) (child : U → U → S → m U)
    (hchild : ∀ a b s', child a b s' = pure ((h s').alphaBetaHard a b)) (s : S) (a b : U)
    (as : List A) :
    alphaBetaHardMaxM (fun op => pure (o op)) child s a b as =
      pure (GameTree.alphaBetaHardMax a b (as.map fun x => h (o (.result s x)))) := by
  induction as generalizing a with
  | nil => simp [alphaBetaHardMaxM]
  | cons x as ih =>
    simp only [alphaBetaHardMaxM, pure_bind, hchild, List.map_cons,
      GameTree.alphaBetaHardMax_cons]
    split_ifs <;> simp [ih]

private theorem alphaBetaHardMinM_pure (o : {ι : Type} → GameQuery S A U ι → ι)
    (h : S → GameTree U) (child : U → U → S → m U)
    (hchild : ∀ a b s', child a b s' = pure ((h s').alphaBetaHard a b)) (s : S) (a b : U)
    (as : List A) :
    alphaBetaHardMinM (fun op => pure (o op)) child s a b as =
      pure (GameTree.alphaBetaHardMin a b (as.map fun x => h (o (.result s x)))) := by
  induction as generalizing b with
  | nil => simp [alphaBetaHardMinM]
  | cons x as ih =>
    simp only [alphaBetaHardMinM, pure_bind, hchild, List.map_cons,
      GameTree.alphaBetaHardMin_cons]
    split_ifs <;> simp [ih]

/-- Fail-hard alpha-beta search, with the queries answered by a game and an evaluation function in
a lawful monad, is fail-hard alpha-beta on the unfolded game tree. -/
theorem alphaBetaHardM_pure (g : Game S A U) (eval : S → U) (d : ℕ) (a b : U) (s : S) :
    alphaBetaHardM (m := m) (fun op => pure (g.oracle eval op)) d a b s =
      pure ((g.unfold eval d s).alphaBetaHard a b) := by
  induction d generalizing a b s with
  | zero => cases h : g.isTerminal s <;> simp [alphaBetaHardM, Game.unfold, h]
  | succ d ih =>
    cases h : g.isTerminal s
    · cases hp : g.toMove s <;>
        simp [alphaBetaHardM, Game.unfold, h, hp,
          alphaBetaHardMaxM_pure _ _ _ ih, alphaBetaHardMinM_pure _ _ _ ih]
    · simp [alphaBetaHardM, Game.unfold, h]

private theorem alphaBetaSoftMaxM_pure [BoundedOrder U] (o : {ι : Type} → GameQuery S A U ι → ι)
    (h : S → GameTree U) (child : U → U → S → m U)
    (hchild : ∀ a b s', child a b s' = pure ((h s').alphaBetaSoft a b)) (s : S) (a b v : U)
    (as : List A) :
    alphaBetaSoftMaxM (fun op => pure (o op)) child s a b v as =
      pure (GameTree.alphaBetaSoftMax a b v (as.map fun x => h (o (.result s x)))) := by
  induction as generalizing a v with
  | nil => simp [alphaBetaSoftMaxM]
  | cons x as ih =>
    simp only [alphaBetaSoftMaxM, pure_bind, hchild, List.map_cons,
      GameTree.alphaBetaSoftMax_cons]
    split_ifs <;> simp [ih]

private theorem alphaBetaSoftMinM_pure [BoundedOrder U] (o : {ι : Type} → GameQuery S A U ι → ι)
    (h : S → GameTree U) (child : U → U → S → m U)
    (hchild : ∀ a b s', child a b s' = pure ((h s').alphaBetaSoft a b)) (s : S) (a b v : U)
    (as : List A) :
    alphaBetaSoftMinM (fun op => pure (o op)) child s a b v as =
      pure (GameTree.alphaBetaSoftMin a b v (as.map fun x => h (o (.result s x)))) := by
  induction as generalizing b v with
  | nil => simp [alphaBetaSoftMinM]
  | cons x as ih =>
    simp only [alphaBetaSoftMinM, pure_bind, hchild, List.map_cons,
      GameTree.alphaBetaSoftMin_cons]
    split_ifs <;> simp [ih]

/-- Fail-soft alpha-beta search, with the queries answered by a game and an evaluation function in
a lawful monad, is fail-soft alpha-beta on the unfolded game tree. -/
theorem alphaBetaSoftM_pure [BoundedOrder U] (g : Game S A U) (eval : S → U) (d : ℕ) (a b : U)
    (s : S) :
    alphaBetaSoftM (m := m) (fun op => pure (g.oracle eval op)) d a b s =
      pure ((g.unfold eval d s).alphaBetaSoft a b) := by
  induction d generalizing a b s with
  | zero => cases h : g.isTerminal s <;> simp [alphaBetaSoftM, Game.unfold, h]
  | succ d ih =>
    cases h : g.isTerminal s
    · cases hp : g.toMove s <;>
        simp [alphaBetaSoftM, Game.unfold, h, hp,
          alphaBetaSoftMaxM_pure _ _ _ ih, alphaBetaSoftMinM_pure _ _ _ ih]
    · simp [alphaBetaSoftM, Game.unfold, h]

end Pure

/-- Evaluating the minimax query program against the oracle of a game and an evaluation function
gives minimax on the unfolded game tree (H-MINIMAX). -/
@[simp] theorem eval_minimaxQ [BoundedOrder U] (g : Game S A U) (eval : S → U) (d : ℕ) (s : S) :
    (minimaxQ d s).eval (g.oracle eval) = (g.unfold eval d s).minimax :=
  Id.pure_injective <|
    ((FreeM.isMonadHom_pure_eval (g.oracle eval)).map_minimaxM FreeM.lift d s).trans
      (minimaxM_pure g eval d s)

/-- Evaluating the fail-hard alpha-beta query program against the oracle of a game and an
evaluation function gives fail-hard alpha-beta on the unfolded game tree; by
`GameTree.alphaBetaHard_eq`, this is depth-limited minimax clamped into the window. -/
@[simp] theorem eval_alphaBetaHardQ (g : Game S A U) (eval : S → U) (d : ℕ) (a b : U) (s : S) :
    (alphaBetaHardQ d a b s).eval (g.oracle eval) = (g.unfold eval d s).alphaBetaHard a b :=
  Id.pure_injective <|
    ((FreeM.isMonadHom_pure_eval (g.oracle eval)).map_alphaBetaHardM FreeM.lift d a b s).trans
      (alphaBetaHardM_pure g eval d a b s)

/-- Evaluating the fail-soft alpha-beta query program against the oracle of a game and an
evaluation function gives fail-soft alpha-beta on the unfolded game tree, which is correct by
`GameTree.alphaBetaSoft_eq_minimax` and its siblings. -/
@[simp] theorem eval_alphaBetaSoftQ [BoundedOrder U] (g : Game S A U) (eval : S → U) (d : ℕ)
    (a b : U) (s : S) :
    (alphaBetaSoftQ d a b s).eval (g.oracle eval) = (g.unfold eval d s).alphaBetaSoft a b :=
  Id.pure_injective <|
    ((FreeM.isMonadHom_pure_eval (g.oracle eval)).map_alphaBetaSoftM FreeM.lift d a b s).trans
      (alphaBetaSoftM_pure g eval d a b s)

/-! ## Pruning: alpha-beta makes no more queries than minimax -/

section Cost

variable (oracle : {ι : Type} → GameQuery S A U ι → ι) (weight : {ι : Type} → GameQuery S A U ι → ℕ)

/-- The weighted query cost that minimax search spends on the moves `as` at the state `s`, where
`child` searches a successor state: for each move, the weight of its `result` query plus the cost of
the search below it. -/
private def movesCost (child : S → FreeM (GameQuery S A U) U) (s : S) (as : List A) : ℕ :=
  (as.map fun a => weight (.result s a) + (child (oracle (.result s a))).cost oracle weight).sum

omit [LinearOrder U] in
/-- The cost of the loop of minimax search over the moves `as` at the state `s`, which asks for
each move's result and searches it with `child`, combining values with `comb`: the sum over the
moves of the `result` query's weight and the cost of the search below it. -/
private theorem cost_foldlM_child (comb : U → U → U) (child : S → FreeM (GameQuery S A U) U)
    (s : S) (v : U) (as : List A) :
    (as.foldlM (fun v a => FreeM.lift (GameQuery.result s a) >>= fun s' =>
      child s' >>= fun w => pure (comb v w)) v).cost oracle weight =
      movesCost oracle weight child s as := by
  induction as generalizing v with
  | nil => simp [movesCost]
  | cons a as ih =>
    simp only [movesCost] at ih ⊢
    simp only [List.foldlM_cons, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift,
      FreeM.cost_pure, ih, List.map_cons, List.sum_cons]
    omega

private theorem cost_alphaBetaHardMaxM_le (childAB : U → U → S → FreeM (GameQuery S A U) U)
    (childMM : S → FreeM (GameQuery S A U) U)
    (hchild : ∀ a b s', (childAB a b s').cost oracle weight ≤ (childMM s').cost oracle weight)
    (s : S) (a b : U) (as : List A) :
    (alphaBetaHardMaxM FreeM.lift childAB s a b as).cost oracle weight ≤
      movesCost oracle weight childMM s as := by
  induction as generalizing a with
  | nil => simp [alphaBetaHardMaxM, movesCost]
  | cons x as ih =>
    simp only [alphaBetaHardMaxM, movesCost, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift,
      List.map_cons, List.sum_cons] at ih ⊢
    have := hchild a b (oracle (.result s x))
    split_ifs
    · simp only [FreeM.cost_pure]; omega
    · grind

private theorem cost_alphaBetaHardMinM_le (childAB : U → U → S → FreeM (GameQuery S A U) U)
    (childMM : S → FreeM (GameQuery S A U) U)
    (hchild : ∀ a b s', (childAB a b s').cost oracle weight ≤ (childMM s').cost oracle weight)
    (s : S) (a b : U) (as : List A) :
    (alphaBetaHardMinM FreeM.lift childAB s a b as).cost oracle weight ≤
      movesCost oracle weight childMM s as := by
  induction as generalizing b with
  | nil => simp [alphaBetaHardMinM, movesCost]
  | cons x as ih =>
    simp only [alphaBetaHardMinM, movesCost, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift,
      List.map_cons, List.sum_cons] at ih ⊢
    have := hchild a b (oracle (.result s x))
    split_ifs
    · simp only [FreeM.cost_pure]; omega
    · grind

/-- **Alpha-beta pruning saves work, fail-hard** (query model): for every oracle, every weighting
of the queries by natural numbers and every window, depth-limited fail-hard alpha-beta search has
at most the weighted query cost of depth-limited minimax search to the same depth. -/
theorem cost_alphaBetaHardQ_le_cost_minimaxQ [BoundedOrder U] (d : ℕ) (a b : U) (s : S) :
    (alphaBetaHardQ (A := A) d a b s).cost oracle weight ≤
      (minimaxQ (A := A) d s).cost oracle weight := by
  induction d generalizing a b s with
  | zero =>
    simp only [alphaBetaHardQ, minimaxQ, alphaBetaHardM, minimaxM, FreeM.cost_liftBind]
    split <;> simp
  | succ d ih =>
    simp only [alphaBetaHardQ, minimaxQ] at ih ⊢
    simp only [alphaBetaHardM, minimaxM, FreeM.cost_liftBind]
    split
    · simp
    · simp only [FreeM.cost_liftBind]
      cases oracle (.toMove s)
      · simp only [cost_foldlM_child]
        grw [cost_alphaBetaHardMaxM_le oracle weight _ _ ih]
      · simp only [cost_foldlM_child]
        grw [cost_alphaBetaHardMinM_le oracle weight _ _ ih]

private theorem cost_alphaBetaSoftMaxM_le (childAB : U → U → S → FreeM (GameQuery S A U) U)
    (childMM : S → FreeM (GameQuery S A U) U)
    (hchild : ∀ a b s', (childAB a b s').cost oracle weight ≤ (childMM s').cost oracle weight)
    (s : S) (a b v : U) (as : List A) :
    (alphaBetaSoftMaxM FreeM.lift childAB s a b v as).cost oracle weight ≤
      movesCost oracle weight childMM s as := by
  induction as generalizing a v with
  | nil => simp [alphaBetaSoftMaxM, movesCost]
  | cons x as ih =>
    simp only [alphaBetaSoftMaxM, movesCost, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift,
      List.map_cons, List.sum_cons] at ih ⊢
    have := hchild a b (oracle (.result s x))
    split_ifs
    · simp only [FreeM.cost_pure]; omega
    · grind

private theorem cost_alphaBetaSoftMinM_le (childAB : U → U → S → FreeM (GameQuery S A U) U)
    (childMM : S → FreeM (GameQuery S A U) U)
    (hchild : ∀ a b s', (childAB a b s').cost oracle weight ≤ (childMM s').cost oracle weight)
    (s : S) (a b v : U) (as : List A) :
    (alphaBetaSoftMinM FreeM.lift childAB s a b v as).cost oracle weight ≤
      movesCost oracle weight childMM s as := by
  induction as generalizing b v with
  | nil => simp [alphaBetaSoftMinM, movesCost]
  | cons x as ih =>
    simp only [alphaBetaSoftMinM, movesCost, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift,
      List.map_cons, List.sum_cons] at ih ⊢
    have := hchild a b (oracle (.result s x))
    split_ifs
    · simp only [FreeM.cost_pure]; omega
    · grind

/-- **Alpha-beta pruning saves work, fail-soft** (query model): for every oracle, every weighting
of the queries by natural numbers and every window, depth-limited fail-soft alpha-beta search has
at most the weighted query cost of depth-limited minimax search to the same depth. -/
theorem cost_alphaBetaSoftQ_le_cost_minimaxQ [BoundedOrder U] (d : ℕ) (a b : U) (s : S) :
    (alphaBetaSoftQ (A := A) d a b s).cost oracle weight ≤
      (minimaxQ (A := A) d s).cost oracle weight := by
  induction d generalizing a b s with
  | zero => simp [alphaBetaSoftQ, minimaxQ, alphaBetaSoftM, minimaxM]
  | succ d ih =>
    simp only [alphaBetaSoftQ, minimaxQ] at ih ⊢
    simp only [alphaBetaSoftM, minimaxM, FreeM.cost_liftBind]
    split
    · simp
    · simp only [FreeM.cost_liftBind]
      cases oracle (.toMove s)
      · simp only [cost_foldlM_child]
        grw [cost_alphaBetaSoftMaxM_le oracle weight _ _ ih]
      · simp only [cost_foldlM_child]
        grw [cost_alphaBetaSoftMinM_le oracle weight _ _ ih]

end Cost

end Cslib.Algorithms.Lean.Search
