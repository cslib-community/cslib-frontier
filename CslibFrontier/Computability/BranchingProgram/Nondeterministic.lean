/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup

/-!
# Nondeterministic branching programs

A *nondeterministic branching program* over inputs `x : ι → α` is a directed acyclic multigraph
with a source and a target, in which each wire is either unlabelled (a *rectifier*) or labelled by
a test `x i = a` (a *contact*). An input switches on the rectifiers and the contacts whose tests it
passes, and the program accepts it when some path from the source to the target uses only wires
that are switched on. The size of a program is its number of contacts
[Jukna, Section 1.3][Jukna2012]. Over `Bool` the tests are the literals; tests over a larger
alphabet are those of [Jukna, Section 15.2][Jukna2012].

`NBP ι α n` lists `n` nodes in a topological order, as `BranchingProgram.Nodes` does for
deterministic programs: the first node is the target, each later node is given by the list of
wires leaving it for earlier nodes, and the last node is the source. The number of paths from a
node to the target that an input switches on is defined by structural recursion (`NBP.paths`,
`NBP.pathCount`), so it computes by `decide` on a concrete program. This one count gives the
modes of acceptance: a nondeterministic program accepts when the count is nonzero (`NBP.Accepts`),
and a parity branching program when it is odd (`NBP.AcceptsParity`).

The recursion for `NBP.paths` recomputes the counts of earlier nodes at every use. Two compiler
replacements avoid this. `NBP.pathsVector` stores the count of every node in a vector, in
topological order, and the compiler uses it for `NBP.paths` (`NBP.paths_eq_pathsImpl`).
For `NBP.pathCount` (`NBP.pathCount_eq_pathCountImpl`), the compiler counts the switched-on
wires of the source directly when they all lead to the target, and otherwise pushes the number
of paths from the source down the program in an array ending at the highest head of those wires,
with a private helper. A node that no path from the source reaches is stepped
past without reading its wires, and the push stops below the lowest node other than the target that
a path reaches. The kernel
definitions, their simplification rules and kernel reduction (`decide`, `rfl`) are unchanged.
Separate calls of `NBP.paths` may recompute the vector. Compiler replacements apply to callers
compiled with this module imported, not previously compiled callers. This module does not certify a
runtime bound.

A deterministic branching program is a nondeterministic one in which every input switches on
exactly one way out of each query node: a query node has a contact for each letter and an accepting
sink has a rectifier to the target (`BranchingProgram.toNBP`). Its path count is `1` on the inputs
it accepts and `0` on the others (`BranchingProgram.pathCount_toNBP`), and it has at most
`Fintype.card α` contacts for each node of the deterministic program
(`BranchingProgram.size_toNBP_le`).

## Main definitions

* `Cslib.BranchingPrograms.NBP.Wire`: a wire to an earlier node, a rectifier or a contact;
  `Cslib.BranchingPrograms.NBP.Wire.equivProd` identifies it with its head and label.
* `Cslib.BranchingPrograms.NBP`: a nondeterministic branching program.
* `Cslib.BranchingPrograms.NBP.size`: its number of contacts.
* `Cslib.BranchingPrograms.NBP.pathCount`: the number of source-to-target paths an input switches
  on.
* `Cslib.BranchingPrograms.NBP.pathsVector`, `Cslib.BranchingPrograms.NBP.pathsImpl`: the path
  counts of all nodes stored in a vector, and the compiler implementation of `NBP.paths` reading it.
* `Cslib.BranchingPrograms.NBP.pathCountImpl`: the compiler implementation of `NBP.pathCount`,
  which pushes path counts down from the source in an array.
* `Cslib.BranchingPrograms.NBP.Accepts`, `Cslib.BranchingPrograms.NBP.AcceptsParity`:
  nondeterministic and parity acceptance.
* `Cslib.BranchingPrograms.BranchingProgram.toNBP`: a deterministic program as a nondeterministic
  one.

## Main results

* `Cslib.BranchingPrograms.NBP.get_pathsVector`: the stored counts agree with `NBP.paths`.
* `Cslib.BranchingPrograms.NBP.paths_eq_pathsImpl`,
  `Cslib.BranchingPrograms.NBP.pathCount_eq_pathCountImpl`: proved compiler replacements.
* `Cslib.BranchingPrograms.BranchingProgram.pathCount_toNBP`: a deterministic program switches on
  one path on the inputs it accepts and none on the others.
* `Cslib.BranchingPrograms.BranchingProgram.size_toNBP_le`: it has at most `Fintype.card α`
  contacts for each of its nodes.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Sections 1.3 and
  15.2][Jukna2012]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

/-- A wire leaving a node of a nondeterministic branching program for one of the `n` earlier
nodes: a rectifier, or a contact testing one coordinate of the input. -/
structure NBP.Wire (ι α : Type*) (n : ℕ) where
  /-- The earlier node the wire leads to. -/
  head : Fin n
  /-- `none` for a rectifier, and `some (i, a)` for a contact testing `x i = a`. -/
  label : Option (ι × α)
  deriving DecidableEq

namespace NBP.Wire

variable {ι α : Type*} {n : ℕ}

/-- A wire is its head and its label. -/
def equivProd : Wire ι α n ≃ Fin n × Option (ι × α) where
  toFun w := (w.head, w.label)
  invFun p := ⟨p.1, p.2⟩

instance [Fintype ι] [Fintype α] : Fintype (Wire ι α n) :=
  Fintype.ofEquiv _ equivProd.symm

/-- There are `n * (|ι| |α| + 1)` wires to `n` earlier nodes: a rectifier and a contact for each
test, to each node. -/
theorem card [Fintype ι] [Fintype α] :
    Fintype.card (Wire ι α n) = n * (Fintype.card ι * Fintype.card α + 1) := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
    Fintype.card_prod]

end NBP.Wire

/-- A *nondeterministic branching program* over inputs `ι → α`, with `n` nodes in topological
order: the first node is the target, each later node has a list of wires to earlier nodes, and the
last node is the source [Jukna, Section 1.3][Jukna2012]. -/
inductive NBP (ι α : Type*) : ℕ → Type _ where
  /-- The program whose only node is the target. -/
  | target : NBP ι α 1
  /-- The nodes of `P` followed by a node with the given wires to them. -/
  | node {n : ℕ} (P : NBP ι α n) (wires : List (NBP.Wire ι α n)) : NBP ι α (n + 1)

namespace NBP

variable {ι α : Type*}

/-- The size of a program: its number of contacts. -/
def size : {n : ℕ} → NBP ι α n → ℕ
  | _, target => 0
  | _, node P wires => P.size + wires.countP (·.label.isSome)

variable [DecidableEq α]

/-- Whether the input `x` switches the wire on: a rectifier always, and a contact when `x` passes
its test. -/
def Wire.on {n : ℕ} (w : Wire ι α n) (x : ι → α) : Bool :=
  w.label.all fun p => x p.1 = p.2

/-- The number of paths from each node to the target on which `x` switches every wire on. -/
def paths (x : ι → α) : {n : ℕ} → NBP ι α n → Fin n → ℕ
  | _, target, _ => 1
  | _, node P wires, v =>
    Fin.lastCases (((wires.filter (·.on x)).map fun w => P.paths x w.head).sum) (P.paths x) v

/-- An earlier node has the same paths in a longer program. -/
@[simp] theorem paths_node_castSucc {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (x : ι → α) (v : Fin n) : (P.node wires).paths x v.castSucc = P.paths x v := by
  simp [paths]

/-- The paths from the last node go through its wires that are switched on. -/
@[simp] theorem paths_node_last {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (x : ι → α) :
    (P.node wires).paths x (Fin.last n) =
      ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum := by
  simp [paths]

/-- The target has one path to itself, the empty one. -/
@[simp] theorem paths_zero (x : ι → α) : ∀ {n : ℕ} (P : NBP ι α (n + 1)), P.paths x 0 = 1
  | 0, target => rfl
  | _ + 1, node P wires => (paths_node_castSucc P wires x 0).trans (paths_zero x P)

/-- The number of paths from the source to the target on which `x` switches every wire on. -/
def pathCount : {n : ℕ} → NBP ι α n → (ι → α) → ℕ
  | _, target, _ => 1
  | _, node P wires, x => ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum

/-- The number of paths from each node to the target on which `x` switches every wire on, computed
node by node in topological order and stored in a vector. -/
def pathsVector (x : ι → α) : {n : ℕ} → NBP ι α n → Vector ℕ n
  | _, target => #v[1]
  | _, node P wires =>
    let prior := P.pathsVector x
    prior.push ((wires.filter (·.on x)).map fun w => prior.get w.head).sum

/-- The stored counts agree with `NBP.paths`. -/
@[simp] theorem get_pathsVector (x : ι → α) :
    ∀ {n : ℕ} (P : NBP ι α n), (P.pathsVector x).get = P.paths x
  | _, target => by
    funext v
    rw [Fin.fin_one_eq_zero v]
    rfl
  | _, node P wires => by
    funext v
    refine Fin.lastCases ?_ (fun v => ?_) v
    · simp [pathsVector, get_pathsVector x P]
    · simp [pathsVector, get_pathsVector x P]

/-- Compiler implementation of `NBP.paths` reading the stored counts. -/
def pathsImpl (x : ι → α) {n : ℕ} (P : NBP ι α n) : Fin n → ℕ :=
  (P.pathsVector x).get

/-- Proved compiler replacement of `NBP.paths` by `NBP.pathsImpl`. -/
@[csimp] theorem paths_eq_pathsImpl : @paths = @pathsImpl := by
  funext ι α _ x n P
  exact (get_pathsVector x P).symm

/-- Push path counts down the program from the source. Entry `i` of `c` is the number of paths
from the source that have reached node `i`, and the result is the number of ways to complete them
to the target with wires switched on by `x`. The bound `lo` is at most every node other than the
target with a nonzero entry; once the current node is below `lo`, entry `0` is returned. A node
whose entry is `0`, or lies past the end of `c`, is stepped past without reading its wires; any
other node adds its entry to the entries of the heads of its switched-on wires. -/
private def pathCountFrom (x : ι → α) : {n : ℕ} → NBP ι α n → Array ℕ → ℕ → ℕ
  | _, target, c, _ => c[0]?.getD 0
  | _, node (n := n) P wires, c, lo =>
    if n < lo then c[0]?.getD 0
    else
      let k := c[n]?.getD 0
      if k = 0 then P.pathCountFrom x c lo
      else
        let on := wires.filter (·.on x)
        P.pathCountFrom x (on.foldl (fun c w => c.modify w.head.val (· + k)) c)
          (on.foldr (fun w b => if w.head.val = 0 then b else min w.head.val b) lo)

/-- The number of switched-on paths from node `i`, and `0` past the last node. -/
private def pathsAt (x : ι → α) {n : ℕ} (P : NBP ι α n) (i : ℕ) : ℕ :=
  if h : i < n then P.paths x ⟨i, h⟩ else 0

/-- The number of completions of `f i` paths at each node `i < k`. -/
private def weight (x : ι → α) {n : ℕ} (P : NBP ι α n) (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, f i * pathsAt x P i

private theorem weight_succ (x : ι → α) {n : ℕ} (P : NBP ι α n) (f : ℕ → ℕ) (k : ℕ) :
    weight x P f (k + 1) = weight x P f k + f k * pathsAt x P k :=
  Finset.sum_range_succ _ k

/-- The number of completions of the paths counted by the array `c`. -/
private def weightA (x : ι → α) {n : ℕ} (P : NBP ι α n) (c : Array ℕ) : ℕ :=
  weight x P (fun i => c[i]?.getD 0) c.size

private theorem pathsAt_fin (x : ι → α) {n : ℕ} (P : NBP ι α n) (v : Fin n) :
    pathsAt x P v.val = P.paths x v := by
  simp [pathsAt]

private theorem pathsAt_self (x : ι → α) {n : ℕ} (P : NBP ι α n) : pathsAt x P n = 0 := by
  simp [pathsAt]

private theorem pathsAt_zero (x : ι → α) : ∀ {n : ℕ} (P : NBP ι α n), pathsAt x P 0 = 1
  | _, target => rfl
  | _, node P wires => by
    unfold pathsAt
    split
    · exact paths_zero x (node P wires)
    · omega

private theorem paths_of_val_eq_zero (x : ι → α) {n : ℕ} (P : NBP ι α n) (v : Fin n)
    (hv : v.val = 0) : P.paths x v = 1 := by
  rw [← pathsAt_fin, hv, pathsAt_zero]

private theorem pathsAt_node_of_ne (x : ι → α) {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    {i : ℕ} (hi : i ≠ n) : pathsAt x (node P wires) i = pathsAt x P i := by
  unfold pathsAt
  split <;> split
  · exact paths_node_castSucc P wires x ⟨i, by omega⟩
  · omega
  · omega
  · rfl

private theorem pathsAt_node_self (x : ι → α) {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n)) :
    pathsAt x (node P wires) n = ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum := by
  unfold pathsAt
  split
  · exact paths_node_last P wires x
  · omega

private theorem weight_low (x : ι → α) {m : ℕ} (Q : NBP ι α m) (f : ℕ → ℕ)
    (hf : ∀ i, 1 ≤ i → i < m → f i = 0) : ∀ k, weight x Q f k = if 0 < k then f 0 else 0
  | 0 => by simp [weight]
  | k + 1 => by
    rw [weight_succ, weight_low x Q f hf k]
    rcases k with _ | k
    · simp [pathsAt_zero]
    · by_cases hk : k + 1 < m
      · simp [hf (k + 1) (by omega) hk]
      · simp [pathsAt, hk]

private theorem weight_node (x : ι → α) {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (f : ℕ → ℕ) : ∀ k, weight x (node P wires) f k = weight x P f k +
      if n < k then f n * ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum else 0
  | 0 => by simp [weight]
  | k + 1 => by
    rw [weight_succ, weight_succ, weight_node x P wires f k]
    by_cases hk : k = n
    · subst hk
      rw [pathsAt_node_self, pathsAt_self]
      simp
    · rw [pathsAt_node_of_ne x P wires hk]
      have h : n < k + 1 ↔ n < k := by omega
      simp only [h]
      ac_rfl

private theorem weight_update (x : ι → α) {n : ℕ} (P : NBP ι α n) (f g : ℕ → ℕ) (h a : ℕ)
    (hg : ∀ i, g i = f i + if i = h then a else 0) :
    ∀ k, weight x P g k = weight x P f k + if h < k then a * pathsAt x P h else 0
  | 0 => by simp [weight]
  | k + 1 => by
    rw [weight_succ, weight_succ, weight_update x P f g h a hg k, hg k]
    by_cases hk : k = h
    · subst hk
      simp [Nat.add_mul, Nat.add_assoc]
    · have h' : h < k + 1 ↔ h < k := by omega
      simp only [hk, h', ↓reduceIte, Nat.add_zero]
      ac_rfl

private theorem weight_zero (x : ι → α) {n : ℕ} (P : NBP ι α n) (f : ℕ → ℕ) (hf : ∀ i, f i = 0)
    (k : ℕ) : weight x P f k = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [hf, Nat.zero_mul]

private theorem getD_modify (c : Array ℕ) {h : ℕ} (hh : h < c.size) (a i : ℕ) :
    (c.modify h (· + a))[i]?.getD 0 = c[i]?.getD 0 + if i = h then a else 0 := by
  rw [Array.getElem?_modify]
  by_cases hi : h = i
  · subst hi
    simp [hh]
  · have hi' : ¬i = h := fun e => hi e.symm
    simp [hi, hi']

private theorem weightA_low (x : ι → α) {m : ℕ} (Q : NBP ι α m) (c : Array ℕ)
    (hc : ∀ i, 1 ≤ i → i < m → c[i]?.getD 0 = 0) : weightA x Q c = c[0]?.getD 0 := by
  unfold weightA
  rw [weight_low x Q _ hc]
  split
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]
    rfl

omit [DecidableEq α] in
private theorem lowHead_le_self {m : ℕ} (lo : ℕ) : ∀ l : List (Wire ι α m),
    l.foldr (fun w b => if w.head.val = 0 then b else min w.head.val b) lo ≤ lo
  | [] => Nat.le_refl _
  | w :: l => by
    rw [List.foldr_cons]
    have := lowHead_le_self lo l
    split <;> omega

omit [DecidableEq α] in
private theorem lowHead_le_head {m : ℕ} (lo : ℕ) :
    ∀ (l : List (Wire ι α m)) (w : Wire ι α m), w ∈ l → w.head.val ≠ 0 →
      l.foldr (fun w b => if w.head.val = 0 then b else min w.head.val b) lo ≤ w.head.val
  | [], _, hw, _ => by simp at hw
  | v :: l, w, hw, h0 => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hw with rfl | hw
    · simp only [h0, ↓reduceIte]
      omega
    · have := lowHead_le_head lo l w hw h0
      split <;> omega

omit [DecidableEq α] in
private theorem getElem?_foldl_modify {m : ℕ} (a i : ℕ) :
    ∀ (ws : List (Wire ι α m)) (c : Array ℕ), (∀ w ∈ ws, w.head.val ≠ i) →
      (ws.foldl (fun c w => c.modify w.head.val (· + a)) c)[i]? = c[i]?
  | [], _, _ => rfl
  | w :: ws, c, h => by
    rw [List.foldl_cons, getElem?_foldl_modify a i ws _ fun v hv => h v (by simp [hv]),
      Array.getElem?_modify]
    simp only [h w (by simp), ↓reduceIte]

private theorem weightA_node (x : ι → α) {n : ℕ} (P : NBP ι α n) (wires : List (Wire ι α n))
    (c : Array ℕ) : weightA x (node P wires) c = weightA x P c +
      if n < c.size then
        c[n]?.getD 0 * ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum
      else 0 :=
  weight_node x P wires _ c.size

private theorem weightA_modify (x : ι → α) {n : ℕ} (P : NBP ι α n) (c : Array ℕ) {h : ℕ}
    (hh : h < c.size) (a : ℕ) :
    weightA x P (c.modify h (· + a)) = weightA x P c + a * pathsAt x P h := by
  unfold weightA
  rw [Array.size_modify, weight_update x P _ _ h a (getD_modify c hh a)]
  simp only [hh, ↓reduceIte]

private theorem weightA_foldl (x : ι → α) {n m : ℕ} (P : NBP ι α n) (a : ℕ) :
    ∀ (ws : List (Wire ι α m)) (c : Array ℕ), (∀ w ∈ ws, w.head.val < c.size) →
      weightA x P (ws.foldl (fun c w => c.modify w.head.val (· + a)) c) =
        weightA x P c + a * (ws.map fun w => pathsAt x P w.head.val).sum
  | [], c, _ => by simp
  | w :: ws, c, hws => by
    rw [List.foldl_cons, weightA_foldl x P a ws _ fun v hv => by
        rw [Array.size_modify]; exact hws v (by simp [hv]),
      weightA_modify x P c (hws w (by simp)) a]
    simp [Nat.mul_add, Nat.add_assoc]

private theorem weightA_replicate (x : ι → α) {n : ℕ} (P : NBP ι α n) (m : ℕ) :
    weightA x P (Array.replicate m 0) = 0 :=
  weight_zero x P _ (fun i => by rw [Array.getElem?_replicate]; split <;> rfl) _

private theorem pathCountFrom_eq (x : ι → α) :
    ∀ {n : ℕ} (P : NBP ι α n) (c : Array ℕ) (lo : ℕ),
      (∀ i, 1 ≤ i → i < lo → i < n → c[i]?.getD 0 = 0) → P.pathCountFrom x c lo = weightA x P c
  | _, target, c, _, _ => (weightA_low x target c fun _ _ _ => by omega).symm
  | _, node (n := n) P wires, c, lo, hc => by
    rw [pathCountFrom]
    split
    · rename_i hlo
      exact (weightA_low x _ c fun i h1 h2 => hc i h1 (by omega) h2).symm
    · rw [weightA_node]
      dsimp only
      by_cases hk : c[n]?.getD 0 = 0
      · simp only [hk, ↓reduceIte]
        rw [pathCountFrom_eq x P c lo fun i h1 h2 h3 => hc i h1 h2 (by omega)]
        split <;> simp
      · have hn : n < c.size := by
          by_contra hn
          exact hk (by rw [Array.getElem?_eq_none (by omega)]; rfl)
        simp only [hk, hn, ↓reduceIte]
        rw [pathCountFrom_eq x P _ _ ?_,
          weightA_foldl x P _ _ c fun w _ => lt_trans w.head.isLt hn]
        · simp only [pathsAt_fin]
        · intro i h1 h2 h3
          rw [getElem?_foldl_modify _ i _ c fun w hw he => ?_]
          · exact hc i h1 (Nat.lt_of_lt_of_le h2 (lowHead_le_self lo _)) (by omega)
          · have := lowHead_le_head lo _ w hw (by omega)
            omega

omit [DecidableEq α] in
private theorem lt_foldr_max {n : ℕ} {l : List (Wire ι α n)} {w : Wire ι α n} (hw : w ∈ l) :
    w.head.val < l.foldr (fun w m => max (w.head.val + 1) m) 0 := by
  rw [← List.foldr_map (f := fun w : Wire ι α n => w.head.val + 1) (g := max)]
  exact List.le_max_of_le' 0 (List.mem_map_of_mem (f := fun w : Wire ι α n => w.head.val + 1) hw)
    le_rfl

/-- Compiler implementation of `NBP.pathCount`. When every switched-on wire of the source leads to
the target, it counts those wires; otherwise it pushes the source's paths down the program with
the private `pathCountFrom`, in an array that ends at the highest head of those wires. -/
@[no_expose] def pathCountImpl : {n : ℕ} → NBP ι α n → (ι → α) → ℕ
  | _, target, _ => 1
  | _, node P wires, x =>
    let on := wires.filter (·.on x)
    if on.all (·.head.val == 0) then on.length
    else
      let m := on.foldr (fun w m => max (w.head.val + 1) m) 0
      P.pathCountFrom x (on.foldl (fun c w => c.modify w.head.val (· + 1)) (Array.replicate m 0))
        (on.foldr (fun w b => if w.head.val = 0 then b else min w.head.val b) m)

/-- Proved compiler replacement of `NBP.pathCount` by `NBP.pathCountImpl`. -/
@[csimp] theorem pathCount_eq_pathCountImpl : @pathCount = @pathCountImpl := by
  funext ι α _ n P x
  cases P with
  | target => rfl
  | node P wires =>
    change ((wires.filter (·.on x)).map fun w => P.paths x w.head).sum = _
    rw [pathCountImpl]
    dsimp only
    split
    · rename_i hall
      rw [List.map_congr_left fun w hw => paths_of_val_eq_zero x P w.head
        (by simpa using List.all_eq_true.mp hall w hw)]
      simp
    · rw [pathCountFrom_eq x P _ _ ?_, weightA_foldl x P 1 _ _ fun w hw => by
          rw [Array.size_replicate]; exact lt_foldr_max hw,
        weightA_replicate, Nat.zero_add, Nat.one_mul]
      · simp only [pathsAt_fin]
      · intro i h1 h2 _
        rw [getElem?_foldl_modify _ i _ _ fun w hw he => ?_]
        · rw [Array.getElem?_replicate]
          split <;> rfl
        · have := lowHead_le_head
            ((wires.filter (·.on x)).foldr (fun w m => max (w.head.val + 1) m) 0) _ w hw
            (by omega)
          omega

/-- A nondeterministic branching program *accepts* an input that switches on some path from the
source to the target. -/
def Accepts {n : ℕ} (P : NBP ι α n) (x : ι → α) : Prop :=
  P.pathCount x ≠ 0

instance {n : ℕ} (P : NBP ι α n) (x : ι → α) : Decidable (P.Accepts x) :=
  inferInstanceAs (Decidable (P.pathCount x ≠ 0))

/-- A *parity branching program* accepts an input that switches on an odd number of paths from the
source to the target [Jukna, Section 1.3][Jukna2012]. -/
def AcceptsParity {n : ℕ} (P : NBP ι α n) (x : ι → α) : Prop :=
  Odd (P.pathCount x)

instance {n : ℕ} (P : NBP ι α n) (x : ι → α) : Decidable (P.AcceptsParity x) :=
  inferInstanceAs (Decidable (Odd (P.pathCount x)))

end NBP

namespace BranchingProgram

variable {ι α : Type*} [Fintype α]

/-- The wires of a node of a deterministic program: a contact for each letter at a query node, a
rectifier to the target at an accepting sink, and no wire at a rejecting sink. -/
noncomputable def Step.wires {n : ℕ} : Step ι α (Fin n) → List (NBP.Wire ι α (n + 1))
  | .sink true => [⟨0, none⟩]
  | .sink false => []
  | .branch i next => Finset.univ.toList.map fun a => ⟨(next a).succ, some (i, a)⟩

/-- A sequence of deterministic nodes as a nondeterministic program: a new target, then the same
nodes with the wires `Step.wires`. -/
noncomputable def Nodes.toNBP : {n : ℕ} → Nodes ι α n → NBP ι α (n + 1)
  | _, .empty => .target
  | _, .node P step => .node P.toNBP step.wires

/-- A deterministic program as a nondeterministic one: a new source with a rectifier to the start
node. -/
noncomputable def toNBP (P : BranchingProgram ι α) : NBP ι α (P.size + 2) :=
  .node P.nodes.toNBP [⟨P.start.succ, none⟩]

/-- The nondeterministic program of a sequence of `n` deterministic nodes has at most
`Fintype.card α` contacts for each node. -/
theorem Nodes.size_toNBP_le :
    ∀ {n : ℕ} (P : Nodes ι α n), P.toNBP.size ≤ Fintype.card α * n
  | _, .empty => Nat.zero_le _
  | _, .node P step => by
    rw [toNBP, NBP.size, Nat.mul_succ]
    refine Nat.add_le_add (size_toNBP_le P) ?_
    cases step with
    | sink b => cases b <;> simp [Step.wires]
    | branch i next => exact List.countP_le_length.trans (by simp [Step.wires])

/-- The nondeterministic program of a deterministic one has at most `Fintype.card α` contacts for
each node: its size, counting contacts, is at most `Fintype.card α` times the size, counting
nodes, of the deterministic program. -/
theorem size_toNBP_le (P : BranchingProgram ι α) :
    P.toNBP.size ≤ Fintype.card α * P.size := by
  simpa [toNBP, NBP.size] using Nodes.size_toNBP_le P.nodes

variable [DecidableEq α]

private theorem filter_on_wires (i : ι) {n : ℕ} (next : α → Fin n) (x : ι → α) :
    ((Finset.univ.toList.map fun a => (⟨(next a).succ, some (i, a)⟩ : NBP.Wire ι α (n + 1))).filter
      (·.on x)) = [⟨(next (x i)).succ, some (i, x i)⟩] := by
  have hon : ((fun w : NBP.Wire ι α (n + 1) => w.on x) ∘
      fun a => (⟨(next a).succ, some (i, a)⟩ : NBP.Wire ι α (n + 1))) =
      fun a => decide (a = x i) :=
    funext fun a => by simp [NBP.Wire.on, eq_comm]
  rw [List.filter_map, hon, List.filter_eq,
    List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.mpr (Finset.mem_univ _))]
  rfl

/-- From each node, a deterministic program switches on one path to the target when it reaches an
accepting sink, and none otherwise. -/
theorem Nodes.paths_toNBP (x : ι → α) :
    ∀ {n : ℕ} (P : Nodes ι α n) (v : Fin n),
      P.toNBP.paths x v.succ = if P.eval x v then 1 else 0
  | _, .empty, v => v.elim0
  | _, .node P step, v => by
    induction v using Fin.lastCases with
    | last =>
      cases step with
      | sink b => cases b <;> simp [Fin.succ_last, toNBP, Step.wires, NBP.Wire.on]
      | branch i next =>
        simp [Fin.succ_last, toNBP, Step.wires, filter_on_wires, eval_node_last_branch,
          paths_toNBP x P]
    | cast v =>
      rw [Fin.succ_castSucc, toNBP, NBP.paths_node_castSucc, eval_node_castSucc]
      exact paths_toNBP x P v

/-- **A deterministic branching program is an unambiguous nondeterministic one**: it switches on
one path from the source to the target on the inputs it accepts, and none on the others. -/
theorem pathCount_toNBP (P : BranchingProgram ι α) (x : ι → α) :
    P.toNBP.pathCount x = if P.eval x then 1 else 0 := by
  rw [eval, ← Nodes.paths_toNBP x P.nodes P.start]
  simp [toNBP, NBP.pathCount, NBP.Wire.on]

end BranchingProgram

end Cslib.BranchingPrograms
