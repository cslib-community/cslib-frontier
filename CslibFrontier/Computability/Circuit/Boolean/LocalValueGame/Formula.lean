/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame

/-!
# Local Boolean access to recursive formulas

At each node, a bounded-depth Boolean formula combines values requested from lower-ranked
nodes. Expanding its gates and redirecting its input leaves gives one local Boolean decoder.
An absent source is the constant false. A present source is reached through a disjunction whose
two children coincide, so following it adds one gate and preserves the claimed bit.

The construction reuses the existing `Formula` and `LocalValueGame.Decoder` representations.
Local semantic equations imply correctness of the expanded decoder, and a uniform formula-depth
bound gives a decreasing gate rank. The source-rank hypothesis covers every declared source,
including ports not used by a node's formula. These are semantic gate-access results; native
encoding and update costs remain separate obligations of `LocalValueGame.exists_machine`.
-/

public section

namespace Cslib.Circuits.Boolean.LocalValueGame.FormulaExpansion

variable {α : Type} {n : ℕ}

/-- A node context and the formula currently being traversed within it. -/
structure Address (α : Type) (n : ℕ) where
  /-- The node whose source ports supply the formula inputs. -/
  node : α
  /-- The current formula, initially the full formula of the node. -/
  formula : Formula signature n
  deriving DecidableEq

/-- Start at the full local formula of the requested node. -/
@[expose] def root (node : α → Formula signature n) (a : α) : Address α n :=
  ⟨a, node a⟩

/-- Expand formula gates and redirect input leaves to the next node's full formula. -/
@[expose] def decoder (node : α → Formula signature n)
    (source : α → Fin n → Option α) : Decoder (Address α n) where
  op a := match a.formula with
    | .input i => (source a.node i).elim (.const false) (fun _ => .or)
    | .gate op _ => op
  child a b := match a.formula with
    | .input i => (source a.node i).elim a (root node)
    | .gate (.const _) _ => a
    | .gate .not args => ⟨a.node, args 0⟩
    | .gate .and args => ⟨a.node, args (if b then 1 else 0)⟩
    | .gate .or args => ⟨a.node, args (if b then 1 else 0)⟩

/-- The value of a local formula when its inputs use the given node semantics. -/
@[expose] def value (source : α → Fin n → Option α) (semantic : α → Bool)
    (a : Address α n) : Bool :=
  a.formula.eval interpretation (fun i => (source a.node i).elim false semantic)

/-- Formula depth pays for internal moves; each drop of node rank pays for a fresh local formula
and the one gate used to redirect to it. This rank is proof data, not computed by the decoder. -/
@[expose] def rank (depthBound : ℕ) (nodeRank : α → ℕ) (a : Address α n) : ℕ :=
  (depthBound + 1) * nodeRank a.node + a.formula.depth

variable (node : α → Formula signature n) (source : α → Fin n → Option α)

/-- Consistent recursive node values satisfy every Boolean gate equation after expansion. -/
theorem value_eq_eval (semantic : α → Bool)
    (hvalue : ∀ a, semantic a =
      (node a).eval interpretation (fun i => (source a i).elim false semantic))
    (a : Address α n) :
    value source semantic a = (decoder node source).eval (value source semantic) a := by
  rcases a with ⟨a, f⟩
  cases f with
  | input i =>
    cases hs : source a i with
    | none => simp [value, decoder, Decoder.eval, hs]
    | some a' => simp [value, decoder, Decoder.eval, root, hs, ← hvalue a']
  | gate op args =>
    cases op <;> rfl

/-- At the root of a local formula the expanded value is its specified recursive value. -/
theorem value_root (semantic : α → Bool)
    (hvalue : ∀ a, semantic a =
      (node a).eval interpretation (fun i => (source a i).elim false semantic)) (a : α) :
    value source semantic (root node a) = semantic a :=
  (hvalue a).symm

/-- Every used Boolean edge lowers the expanded rank. The source condition is imposed on all
declared ports, so it also covers arbitrary formula addresses with the same node context. -/
theorem descends {depthBound : ℕ} {nodeRank : α → ℕ}
    (hdepth : ∀ a, (node a).depth ≤ depthBound)
    (hsource : ∀ a i a', source a i = some a' → nodeRank a' < nodeRank a) :
    (decoder node source).Descends (rank depthBound nodeRank) := by
  intro a b
  rcases a with ⟨a, f⟩
  cases f with
  | input i =>
    cases hs : source a i with
    | none => simp only [decoder, hs, Option.elim_none]
    | some a' =>
      have hlt := hsource a i a' hs
      have hd := hdepth a'
      have hm := Nat.mul_le_mul_left (depthBound + 1) (Nat.succ_le_of_lt hlt)
      rw [Nat.mul_succ] at hm
      simp only [decoder, hs, Option.elim_some, rank, root, Formula.depth_input]
      omega
  | gate op args =>
    have harg (i : Fin (signature.Arity op)) :
        (args i).depth < (Formula.gate op args).depth :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ i))
    cases op with
    | const v => trivial
    | not =>
      have h := harg 0
      simp only [decoder, rank]
      omega
    | and =>
      have h := harg (if b then 1 else 0)
      simp only [decoder, rank]
      omega
    | or =>
      have h := harg (if b then 1 else 0)
      simp only [decoder, rank]
      omega

end Cslib.Circuits.Boolean.LocalValueGame.FormulaExpansion
