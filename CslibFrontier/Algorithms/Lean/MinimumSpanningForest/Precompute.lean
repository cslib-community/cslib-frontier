/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Precomputing comparison programs for small labeled graphs

Section 4.1 of [PettieRamachandran2002] precomputes a table indexed by unweighted topologies.
The catalog below materializes an array trie on the two endpoint strings of a labeled multigraph.
Reading an entry descends one vector level per endpoint. Pointer-only batch lookup as described
in §6 has a different representation.

For a finite-table search allowing `q` possible comparisons, both answer restrictions together
partition the rows. We count the full search space, including the alternatives that end early.
The `cutoff_volume` theorem bounds its total table size at the triple-logarithmic cutoff.

## References

* [PettieRamachandran2002], §§4.1, 6.
-/

public section

namespace Cslib.Multigraph.MSFPrecompute

universe u

variable {k m n maxVertices maxEdges : ℕ} {E V Q X α : Type}

/-- An eager table indexed by a length-`d` string of labels smaller than `n`. -/
@[expose] def Table (n : ℕ) (α : Type u) : ℕ → Type u
  | 0 => α
  | d + 1 => Vector (Table n α d) n

/-- Fill every leaf with its key-dependent entry. -/
def tabulate {n : ℕ} {α : Type u} : (d : ℕ) → ((Fin d → Fin n) → α) → Table n α d
  | 0, f => f Fin.elim0
  | d + 1, f => Vector.ofFn fun a => tabulate d fun g => f (Fin.cases a g)

/-- Read a filled table by following its key. -/
def read {n : ℕ} {α : Type u} : (d : ℕ) → Table n α d → (Fin d → Fin n) → α
  | 0, x, _ => x
  | d + 1, t, s =>
    let children : Vector (Table n α d) n := t
    read d children[(s 0).val] (fun i => s i.succ)

@[simp] theorem read_tabulate {n : ℕ} {α : Type u} (d : ℕ) (f : (Fin d → Fin n) → α)
    (s : Fin d → Fin n) : read d (tabulate d f) s = f s := by
  induction d with
  | zero =>
    have h : (Fin.elim0 : Fin 0 → Fin n) = s := funext fun i => Fin.elim0 i
    simp [read, tabulate, h]
  | succ d ih =>
    simp only [read, tabulate, Vector.getElem_ofFn, ih]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i

/-- One level per label on each of the two endpoint strings. -/
abbrev Catalog (n m : ℕ) (α : Type u) := Table n (Table n α m) m

/-- Fill the catalog for every labeled topology on `m` edges and `n` vertices.
Different orientations of the same edge yield the same undirected graph. -/
def build {n m : ℕ} {α : Type u} (make : (Fin m → Sym2 (Fin n)) → α) : Catalog n m α :=
  tabulate m fun left => tabulate m fun right => make (fun e => s(left e, right e))

/-- Follow the two length-`m` endpoint strings into a previously constructed catalog. -/
def lookup {n m : ℕ} {α : Type u} (table : Catalog n m α) (left right : Fin m → Fin n) : α :=
  read m (read m table left) right

@[simp] theorem lookup_build {n m : ℕ} {α : Type u} (make : (Fin m → Sym2 (Fin n)) → α)
    (left right : Fin m → Fin n) :
    lookup (build make) left right = make (fun e => s(left e, right e)) := by
  simp [lookup, build]

/-- Materialize the optimal weight-comparison program for each small topology. -/
@[expose] def optimalCatalog (n m : ℕ) :
    Catalog n m (FreeM (Cslib.Query.LEQuery (Fin m)) (Finset (Fin m))) :=
  build optimalMSFProgram

/-- Reading the precomputed program recovers the program synthesized for these endpoints. -/
@[simp] theorem lookup_optimalCatalog (left right : Fin m → Fin n) :
    lookup (optimalCatalog n m) left right =
      optimalMSFProgram (fun e => s(left e, right e)) := by
  simp [optimalCatalog]

/-- A vector with index-dependent entry types. The index stored alongside each value allows
a precomputed comparison program to have the correct edge-label type after lookup. -/
structure IndexedVector (K : Fin k → Type u) where
  /-- Cells in index order, each paired with its dependent index. -/
  entries : Vector (Σ i, K i) k
  index : ∀ i : Fin k, entries[i].1 = i

namespace IndexedVector

/-- Construct an eager indexed vector, including its index alignment proof. -/
def ofFn {K : Fin k → Type u} (f : (i : Fin k) → K i) : IndexedVector K :=
  ⟨Vector.ofFn (fun i => ⟨i, f i⟩), by simp⟩

/-- Get the entry at a given index. -/
def get {K : Fin k → Type u} (v : IndexedVector K) (i : Fin k) : K i :=
  (v.index i) ▸ v.entries[i].2

@[simp] theorem get_ofFn {K : Fin k → Type u} (f : (i : Fin k) → K i) (i : Fin k) :
    (ofFn f).get i = f i := by
  have align (t : Σ j, K j) (index : t.1 = i) (stored : t = ⟨i, f i⟩) :
      index ▸ t.2 = f i := by
    subst t
    rfl
  apply align
  simp [ofFn]

end IndexedVector

/-- Tables for every pair of vertex and edge sizes within the two cutoffs. -/
abbrev Bank (maxVertices maxEdges : ℕ) :=
  IndexedVector (fun n : Fin (maxVertices+1) => IndexedVector (fun m : Fin (maxEdges+1) =>
    Catalog n m (FreeM (Cslib.Query.LEQuery (Fin m)) (Finset (Fin m)))))

/-- Synthesize and store every program before the partition pieces are supplied. -/
def fillBank (maxVertices maxEdges : ℕ) : Bank maxVertices maxEdges :=
  IndexedVector.ofFn fun n => IndexedVector.ofFn fun m => optimalCatalog n m

private def orderedEnds [LinearOrder V] : Sym2 V → V × V :=
  Sym2.lift ⟨fun a b => (min a b, max a b), by simp [min_comm, max_comm]⟩

private theorem orderedEnds_mk [LinearOrder V] (e : Sym2 V) :
    s((orderedEnds e).1, (orderedEnds e).2) = e := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases le_total a b with h | h
    · simp [orderedEnds, min_eq_left h, max_eq_right h]
    · simp [orderedEnds, min_eq_right h, max_eq_left h]

/-- Run the stored comparison program on a compactly relabeled edge subset. The fallback handles
pieces outside the supplied size range, making the solver total for arbitrary multigraphs. -/
def cachedMSFOn [LinearOrder E] [LinearOrder V] (bank : Bank maxVertices maxEdges)
    (ends : E → Sym2 V) (S : Finset E) : FreeM (Cslib.Query.LEQuery E) (Finset E) :=
  if hv : (OptimalTree.vertices ends S).card < maxVertices + 1 then
    if he : S.card < maxEdges + 1 then
      let edges := S.orderEmbOfFin rfl
      let table := (bank.get ⟨_, hv⟩).get ⟨_, he⟩
      let topology := OptimalTree.localEnds ends S
      let prog := lookup table (fun i => (orderedEnds (topology i)).1)
        (fun i => (orderedEnds (topology i)).2)
      Finset.map edges.toEmbedding <$> Cslib.Query.LEQuery.relabel edges prog
    else optimalMSFOn ends S
  else optimalMSFOn ends S

/-- The cached solver returns exactly the native subgraph program, for every edge subset. -/
@[simp] theorem cachedMSFOn_fill [LinearOrder E] [LinearOrder V] (v m : ℕ)
    (ends : E → Sym2 V) (S : Finset E) :
    cachedMSFOn (fillBank v m) ends S = optimalMSFOn ends S := by
  unfold cachedMSFOn
  split <;> try rfl
  split <;> try rfl
  simp [fillBank, optimalMSFOn, orderedEnds_mk]

/-- The enumeration works even for loops and repeated edges. -/
theorem key_count (n m : ℕ) :
    Fintype.card ((Fin m → Fin n) × (Fin m → Fin n)) = n ^ (2*m) := by
  simp [two_mul, pow_add]

/-- A full level of possible finite-table search calls. The Boolean oracle is evaluated on the
stored rank rows. For each candidate pair, a row belongs to just one child. -/
def branches (pairs : List Q) (answer : X → Q → Bool) (rows : List X) : List (List X) :=
  pairs.flatMap fun q => [rows.filter (fun x => answer x q), rows.filter (fun x => !(answer x q))]

@[simp] theorem length_branches (pairs : List Q) (answer : X → Q → Bool) (rows : List X) :
    (branches pairs answer rows).length = 2*pairs.length := by
  induction pairs with
  | nil => simp [branches]
  | cons q qs ih => simp [branches] at ih ⊢; omega

@[simp] theorem rows_branches (pairs : List Q) (answer : X → Q → Bool) (rows : List X) :
    ((branches pairs answer rows).map List.length).sum = pairs.length*rows.length := by
  induction pairs with
  | nil => simp [branches]
  | cons q qs ih =>
    change (rows.filter _).length +
      ((rows.filter _).length + ((branches qs answer rows).map List.length).sum) = _
    rw [ih, ← Nat.add_assoc]
    have split : (rows.filter (fun x => answer x q)).length +
        (rows.filter (fun x => !(answer x q))).length = rows.length := by
      clear ih
      induction rows with
      | nil => rfl
      | cons x xs hh => cases e : answer x q <;> simp [e] <;> omega
    rw [split, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- All potential promises at a fixed depth, including the subcalls skipped by early success.
This also counts empty promises. -/
def level (pairs : List Q) (answer : X → Q → Bool) : ℕ → List X → List (List X)
  | 0, rows => [rows]
  | d+1, rows => (level pairs answer d rows).flatMap (branches pairs answer)

private theorem stats_flatMap (parents : List (List X)) (pairs : List Q) (answer : X → Q → Bool) :
    (parents.flatMap (branches pairs answer)).length = parents.length*(2*pairs.length) ∧
    ((parents.flatMap (branches pairs answer)).map List.length).sum =
      pairs.length*(parents.map List.length).sum := by
  induction parents with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.mul_add, Nat.add_mul, Nat.add_comm]

/-- More calls than rows can be present. Node count and row count therefore have different bases. -/
theorem level_size (pairs : List Q) (answer : X → Q → Bool) (d : ℕ) (rows : List X) :
    (level pairs answer d rows).length = (2*pairs.length)^d ∧
    ((level pairs answer d rows).map List.length).sum = pairs.length^d*rows.length := by
  induction d with
  | zero => simp [level]
  | succ d ih =>
    obtain ⟨a, b⟩ := stats_flatMap (level pairs answer d rows) pairs answer
    exact ⟨by simp [level, pow_succ, ih, a], by
      rw [ih.2] at b
      simpa [level, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using b⟩

private theorem length_assignments (vals : List α) (n : ℕ) :
    (OptimalTree.assignments vals n).length = vals.length ^ n := by
  induction n with
  | zero => simp [OptimalTree.assignments]
  | succ n ih =>
    simp [OptimalTree.assignments, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- A call or stored rank row at a potential depth-`d` state in the actual search for
`OptimalTree.atDepth`. The initial promise contains only injective rank assignments. -/
theorem rank_level_size (m d : ℕ) :
    let states := level (OptimalTree.pairs m)
      (fun (rank : Fin m → Fin m) (q : Fin m × Fin m) => decide (rank q.1 ≤ rank q.2)) d
      (OptimalTree.ranks m)
    states.length + (states.map List.length).sum ≤ (2*m^2)^d + (m^2)^d*m^m := by
  dsimp only
  have hr : (OptimalTree.ranks m).length ≤ m^m := by
    simpa only [OptimalTree.ranks, length_assignments, List.length_finRange] using
      (List.length_filter_le (l := OptimalTree.assignments (List.finRange m) m)
        (p := fun r => decide (∀ a b, r a = r b → a = b)))
  obtain ⟨a, b⟩ := level_size (OptimalTree.pairs m)
    (fun (rank : Fin m → Fin m) (q : Fin m × Fin m) => decide (rank q.1 ≤ rank q.2)) d
    (OptimalTree.ranks m)
  rw [a, b, OptimalTree.length_pairs, ← pow_two]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _

/-- Upper bound on search cells for all bounded size pairs, all ordered endpoint catalogs and
every search depth `h ≤ m²`. A cell is one possible search-call occurrence or one rank row at that
call. We allow `m^m` rank rows as an upper bound on the injective rank maps. -/
def volume (r : ℕ) : ℕ :=
  let m := r^2
  let q := m^2
  (r+1)*(m+1) * r^(2*m) * (q+1)^2 * ((2*q+1)^q + (q+1)^q * m^m)

/-- Number of calls and rank rows in the full expansion of iterative deepening, over
every endpoint-string pair on vertex labels `Fin n` and edge labels `Fin m`. -/
def catalogCells (n m : ℕ) : ℕ :=
  n^(2*m) * ∑ h ∈ Finset.range (m^2+1), ∑ d ∈ Finset.range (h+1),
    ((2*m^2)^d + (m^2)^d * m^m)

/-- Total structural cell bound for vertices up to `r` and edges up to `r²`. -/
def allCatalogCells (r : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (r+1), ∑ m ∈ Finset.range (r^2+1), catalogCells n m

private theorem sum_range_le (f : ℕ → ℕ) (k b : ℕ) (hf : ∀ i < k, f i ≤ b) :
    ∑ i ∈ Finset.range k, f i ≤ k*b := by
  calc
    _ ≤ ∑ _ ∈ Finset.range k, b :=
      Finset.sum_le_sum fun i hi => hf i (Finset.mem_range.mp hi)
    _ = _ := by simp

/-- The sum over topology sizes, search budgets and recursion levels is bounded by `volume`. -/
theorem allCatalogCells_le (r : ℕ) : allCatalogCells r ≤ volume r := by
  by_cases hr : r = 0
  · subst r
    simp [allCatalogCells, catalogCells, volume]
  have pos : 0 < r := by omega
  let M := r^2
  let Q := M^2
  let B := (2*Q+1)^Q + (Q+1)^Q * M^M
  have posM : 0 < M := Nat.pow_pos pos
  have per (n m : ℕ) (hn : n ≤ r) (hm : m ≤ M) :
      catalogCells n m ≤ r^(2*M) * ((Q+1)*((Q+1)*B)) := by
    have hqm : m^2 ≤ Q := Nat.pow_le_pow_left hm 2
    have key := (Nat.pow_le_pow_left hn (2*m)).trans
      (Nat.pow_le_pow_right pos (Nat.mul_le_mul_left 2 hm))
    refine Nat.mul_le_mul key ?_
    refine (sum_range_le _ _ _ ?_).trans (Nat.mul_le_mul_right _ (by omega))
    intro h hh
    have hhq : h ≤ Q := by omega
    refine (sum_range_le _ _ B ?_).trans (Nat.mul_le_mul_right _ (by omega))
    intro d hd
    have hdq : d ≤ Q := by omega
    have hnode := (Nat.pow_le_pow_left (show 2*m^2 ≤ 2*Q+1 by omega) d).trans
      (Nat.pow_le_pow_right (by omega) hdq)
    have hrow := (Nat.pow_le_pow_left (show m^2 ≤ Q+1 by omega) d).trans
      (Nat.pow_le_pow_right (by omega) hdq)
    have hnum := (Nat.pow_le_pow_left hm m).trans (Nat.pow_le_pow_right posM hm)
    exact Nat.add_le_add hnode (Nat.mul_le_mul hrow hnum)
  refine (sum_range_le _ _ _ (fun n hn =>
    sum_range_le _ _ _ (fun m hm => per n m (by omega) (by dsimp [M]; omega)))).trans ?_
  dsimp [B, M, Q, volume]
  rw [pow_two ((r^2)^2 + 1)]
  exact le_of_eq (by ac_rfl)

private def scale (r : ℕ) := 2*(r+2)^4+4

private theorem volume_le (r : ℕ) : volume r ≤ 2^(8*(scale r)^2) := by
  let m := r^2
  let q := m^2
  let b := scale r
  have hm : r ≤ m := Nat.le_pow (by decide)
  have hq : m ≤ q := Nat.le_pow (by decide)
  have hqb : 2*q+2 ≤ b := by
    dsimp [q, m, b, scale]
    nlinarith [Nat.zero_le r, Nat.zero_le (r^2), Nat.zero_le (r^3)]
  have bpos : 1 ≤ b := by omega
  have bound {a k : ℕ} (ha : a ≤ b) (hk : k ≤ b) : a^k ≤ b^b :=
    (Nat.pow_le_pow_left ha _).trans (Nat.pow_le_pow_right bpos hk)
  have factor : 2 ≤ b^b := (show 2 ≤ b by omega).trans (Nat.le_pow (by omega))
  change (r+1)*(m+1) * r^(2*m) * (q+1)^2 * ((2*q+1)^q + (q+1)^q * m^m) ≤ _
  calc
    _ ≤ (b*b)*(b^b)*(b^b)*(2*(b^b*b^b)) := by
      have h1 := bound (a := 2*q+1) (k := q) (by omega) (by omega)
      have h2 := bound (a := q+1) (k := q) (by omega) (by omega)
      have h3 := bound (a := m) (k := m) (by omega) (by omega)
      have up := Nat.mul_le_mul h2 h3
      have h1' := h1.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < b^b))
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
          (bound (by omega) (by omega))) (bound (by omega) (by omega))) (by omega)
    _ ≤ (b^b * b^b)*(b^b)*(b^b)*(b^b*(b^b*b^b)) := by
      gcongr <;> apply Nat.le_pow <;> omega
    _ = b^(7*b) := by
      rw [show 7*b = b+b+b+b+b+b+b by omega]
      simp only [pow_add]
      ac_rfl
    _ ≤ (2^b)^(7*b) := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ ≤ _ := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by dsimp [b]; nlinarith)

/-- The exact PR choice of a triple iterated logarithm, rounded conservatively up by one. -/
def cutoff (n : ℕ) : ℕ := n.log2.log2.log2 + 1

private theorem eventually_scale :
    ∀ᶠ k : ℕ in Filter.atTop, 8*(scale (k+1))^2 ≤ 2^k := by
  have little := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 8 (r := 2) (by norm_num)
  have h := little.bound (show (0:ℝ) < 1/16384 by norm_num)
  filter_upwards [h, Filter.eventually_ge_atTop (3 : ℕ)] with k hk hk3
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)^8),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 2^k)] at hk
  have x : k+1+2 ≤ 2*k := by omega
  have hs : scale (k+1) ≤ 36*k^4 := by
    unfold scale
    have hh := Nat.pow_le_pow_left x 4
    have : 1 ≤ k^4 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hsq := Nat.pow_le_pow_left hs 2
  have hh' : 16384*k^8 ≤ 2^k := by exact_mod_cast (show (16384:ℝ)*(k:ℝ)^8 ≤ 2^k by linarith)
  -- Use a larger constant in the exponential domination for the leading coefficient.
  exact (by nlinarith)

/-- At the triple-logarithmic cutoff the exhaustive search cells fit even within
`⌊log₂ n⌋`, eventually in the ambient vertex count. -/
theorem cutoff_volume : ∀ᶠ n : ℕ in Filter.atTop, volume (cutoff n) ≤ n.log2 := by
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 eventually_scale
  refine Filter.eventually_atTop.2 ⟨2 ^ (2 ^ (2 ^ (k+2))), ?_⟩
  intro n hn
  have h0 : n ≠ 0 := by have := Nat.two_pow_pos (2 ^ (2 ^ (k+2))); omega
  have h1 := (Nat.le_log2 h0).2 hn
  have h2 : n.log2 ≠ 0 := by have := Nat.two_pow_pos (2 ^ (k+2)); omega
  have h3 := (Nat.le_log2 h2).2 h1
  have h4 : n.log2.log2 ≠ 0 := by have := Nat.two_pow_pos (k+2); omega
  have h5 := (Nat.le_log2 h4).2 h3
  apply (volume_le (cutoff n)).trans
  apply (Nat.pow_le_pow_right (by decide : 0 < 2) ?_).trans (Nat.log2_self_le h2)
  exact (hk _ (by omega)).trans (Nat.log2_self_le h4)

/-- All search cells for all catalog sizes together eventually fit within logarithmic space
when counted across recursion levels and search budgets. -/
theorem cutoff_catalogCells : ∀ᶠ n : ℕ in Filter.atTop, allCatalogCells (cutoff n) ≤ n.log2 :=
  cutoff_volume.mono fun n hn => (allCatalogCells_le (cutoff n)).trans hn

end Cslib.Multigraph.MSFPrecompute
