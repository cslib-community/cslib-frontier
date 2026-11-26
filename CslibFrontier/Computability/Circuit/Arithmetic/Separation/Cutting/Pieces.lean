/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.ThinTrees
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ScriptSize
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Tables
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Time
public import CslibFrontier.Foundations.Combinatorics.StagedTree
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Pieces.Program

/-!
# The pieces of thin trees

Proposition J.2 of [AnthropicVPVNP2026] (p. 52, and its proof, p. 53) cuts the thin trees of
Theorem H.2 (`Trees.ThinTrees`) into pieces. For the numbers `n` of initial units and the outcomes
`o`, the tree of the parties is a tree by stages (`Cslib.StagedTree`), with the weight `1` at the
`K + K` base parties and the units `units n o` between the parties and their parents. Its
pieces for the budgets `K + K` and `Y = lg M ^ C * M * (N + M ^ 2)` (Theorem H.2(b)) and the number
`k > 0` are the pieces of the parties (`ThinTrees.piece`); there are fewer than
`pieceCount k = 1 + C + b * (depth * k)` of them (Proposition J.2: "at most `kΛ` pieces"). For good
outcomes and at most `N` units at every base party, a piece has

* at most `4 (K + K) / k` base parties (`ThinTrees.card_base_piece_le`);
* at most `Λ M ^ (1 - γ) (N + M ^ 2)` units with exactly one holder in it besides the `M ^ C` dead
  ones, in the form `card * w ≤ Y + M ^ C * w` for a gain `w` (`ThinTrees.card_oneIn_piece_le`);
* few cells and units read by its roles (`ThinTrees.cellCount_add_roleUnitCount_le`).

A straight-line program computes what each table does, the pieces and the check of the numbers of
units (`ThinTrees.exists_slpTab`): the program of the thin trees (Theorem H.2(d)), on the numbers
of initial units and the outcomes as inputs, and `2 * depth + 6` stages of `Y ^ 12` gates
(`Pieces.pieces_stage`).

## Main definitions

* `Trees.ThinTrees.pieceCount`: the bound for the number of pieces.
* `Trees.ThinTrees.piece`: the piece of a party.

## Main results

* `Trees.ThinTrees.card_base_piece_le`, `Trees.ThinTrees.card_oneIn_piece_le`,
  `Trees.ThinTrees.cellCount_add_roleUnitCount_le`: the bounds of a piece.
* `Trees.ThinTrees.exists_slpTab`: the program of the pieces.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition J.2 (p. 52) and its proof ("Heavy nodes and pieces", "The bounds", p. 53); module
  `Paper.Pieces`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Trees.ThinTrees

open Finset Cut Interpreter Dealing GroupProgram

section Pieces

variable {R : Type} [CommSemiring R] {laws : List (Law R)} {K N ℓ M b G C : ℕ} {γ : ℝ}
  (TT : ThinTrees laws (K + K) N ℓ M b G C γ)

/-! ### The tree and its pieces -/

/-- The tree of the parties for the numbers `n` of initial units and the outcomes `o`, as a tree by
stages: the parents, stages, depth and root of the thin trees. -/
private def stagedTree (n : Fin (K + K) → Fin (K + K) → Fin (N + 1))
    (o : TT.moves.Channel → Fin TT.U1) : StagedTree (Fin (K + K + TT.A')) where
  parent := TT.parent n o
  stage := TT.stage
  depth := TT.depth
  root := TT.root
  stage_le := TT.stage_le
  stage_eq_depth_iff := TT.stage_eq_depth_iff _
  stage_parent := TT.stage_parent n o _

/-- The weight of a party: `1` at the base parties. -/
private def baseWeight (p : Fin (K + K + TT.A')) : ℕ := if (p : ℕ) < K + K then 1 else 0

private theorem sum_baseWeight : ∑ p, TT.baseWeight p = K + K := by
  rw [Fin.sum_univ_add]
  simp [baseWeight]

/-- The bound for the number of pieces of the cut by `k`: `1 + C + b * (depth * k)`. -/
@[expose] def pieceCount (k : ℕ) : ℕ := 1 + C + b * (TT.depth * k)

/-- The pieces of the tree for the numbers `n` and the outcomes `o`, by number. -/
private def pieceNat (k : ℕ) (n : Fin (K + K) → Fin (K + K) → Fin (N + 1))
    (o : TT.moves.Channel → Fin TT.U1) (p : Fin (K + K + TT.A')) : ℕ :=
  (TT.stagedTree n o).piece TT.baseWeight (TT.units n o) (K + K) (lg M ^ C * M * (N + M ^ 2)) k p

/-- **The piece of a party** (Proposition J.2, its proof, p. 53) for the numbers `n` of initial
units, the outcomes `o` and the cut by `k > 0`: the piece of the party in the tree of the parties
by stages, with the weight `1` at the base parties and the weights `units n o`, the budgets `K + K`
and `lg M ^ C * M * (N + M ^ 2)` and the number `k` (`Cslib.StagedTree.piece`). -/
def piece {k : ℕ} (hk : 0 < k) (n : Fin (K + K) → Fin (K + K) → Fin (N + 1))
    (o : TT.moves.Channel → Fin TT.U1) (p : Fin (K + K + TT.A')) : Fin (TT.pieceCount k) :=
  ⟨TT.pieceNat k n o p, (TT.stagedTree n o).piece_lt hk TT.sum_baseWeight.le (TT.sum_units_le n o)
    (TT.card_children_le n o) (TT.card_children_root_le n o) p⟩

/-! ### The bounds of a piece -/

variable {n : Fin (K + K) → Fin (K + K) → Fin (N + 1)} {o : TT.moves.Channel → Fin TT.U1} {k : ℕ}

/-- `k` times the base parties of a piece are at most `4 (K + K)`. -/
private theorem mul_sum_baseWeight_le (hk : 0 < k) (hkK : k ≤ 4 * (K + K)) (hM : 0 < M)
    (g : Fin (TT.pieceCount k)) :
    k * ∑ p with TT.piece hk n o p = g, TT.baseWeight p ≤ 4 * (K + K) := by
  rw [mul_sum, filter_congr fun p _ => Fin.ext_iff]
  refine (TT.stagedTree n o).sum_piece_le _ (fun p => ?_) (fun x hx => ?_) _
  · exact (Nat.mul_le_mul_left k (show TT.baseWeight p ≤ 1 by
      unfold baseWeight; split_ifs <;> omega)).trans (by omega)
  · refine le_of_eq_of_le ?_ (StagedTree.light_given_le
      (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) hM) (by positivity)) hx)
    simp only [StagedTree.sumBelow, mul_sum]

/-- **The base parties of a piece** (Proposition J.2: "A piece has at most `CK/k` blocks and
parts"): at most `4 (K + K) / k`, if `k ≤ 4 (K + K)`. -/
theorem card_base_piece_le (hk : 0 < k) (hkK : k ≤ 4 * (K + K)) (hM : 0 < M)
    (g : Fin (TT.pieceCount k)) :
    #{p : Fin (K + K) | TT.piece hk n o (Fin.castAdd TT.A' p) = g} * k ≤ 4 * (K + K) := by
  refine le_of_eq_of_le ?_ (TT.mul_sum_baseWeight_le (n := n) (o := o) hk hkK hM g)
  rw [sum_filter, Fin.sum_univ_add, mul_comm, card_filter]
  simp [baseWeight]

/-- Each unit has two holders. -/
private theorem sum_card_filter_holds_le {U P : Type*} [Fintype P] [DecidableEq P]
    (h : U → Bool → P) (S : Finset U) : ∑ a, #(S.filter (Play.Holds h a)) ≤ 2 * #S := by
  simp only [card_filter]
  rw [sum_comm, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun u _ => (card_filter _ _).symm.trans_le <|
    (card_le_card (t := {h u false, h u true}) fun a ha => ?_).trans card_le_two
  rcases (mem_filter.1 ha).2 with ⟨false | true, rfl⟩ <;> simp

/-- **The cut units of a piece** (the proof of Proposition J.2, p. 53: "By part (b) of the theorem
a piece has at most `ΛM^(1−γ)Nℓ ≤ KTΛ/v^300` bits in cut packets, besides the dead ones"): for a
gain `w`, under which `X` units at one party with Theorem H.2(b)'s bound
`Λ M ^ (1 - γ) (N + M ^ 2)` give `X * w ≤ Y`, the units with exactly one holder in a piece times `w`
are at most `Y + M ^ C * w`, for good outcomes and at most `N` units at every base party. -/
theorem card_oneIn_piece_le (hk : 0 < k) (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N)
    (hg : ∀ x, TT.plan.Good n o x) {w : ℕ}
    (hw : ∀ X : ℕ, (X : ℝ) ≤ (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) →
      X * w ≤ lg M ^ C * M * (N + M ^ 2)) (g : Fin (TT.pieceCount k)) :
    #((TT.plan.cur n o TT.E).filter
        (OneIn (UnitId.holder TT.moves.channelParty) (TT.piece hk n o) g)) * w ≤
      lg M ^ C * M * (N + M ^ 2) + M ^ C * w := by
  set S := Play.cutUnits (UnitId.holder TT.moves.channelParty) id
    (TT.plan.cur n o TT.E \ TT.dead o)
  obtain ⟨x, hx⟩ := (TT.stagedTree n o).exists_piece_boundary (g := TT.baseWeight)
    (u := TT.units n o) (M := K + K) (Y := lg M ^ C * M * (N + M ^ 2)) (k := k) g
  have hx' : ∀ q, q ≠ TT.root → ¬(TT.pieceNat k n o q = g ↔
      TT.pieceNat k n o (TT.parent n o q) = g) → q = x ∨ TT.parent n o q = x := hx
  have hsub : (TT.plan.cur n o TT.E).filter
      (OneIn (UnitId.holder TT.moves.channelParty) (TT.piece hk n o) g) ⊆
      S.filter (Play.Holds (UnitId.holder TT.moves.channelParty) x) ∪ TT.dead o := fun u hu => by
    obtain ⟨hcur, hone⟩ := mem_filter.1 hu
    simp only [OneIn, piece, Fin.ext_iff, xor_iff_not_iff] at hone
    by_cases hd : u ∈ TT.dead o
    · exact mem_union_right _ hd
    have hS : u ∈ S := Play.mem_cutUnits.2 ⟨mem_sdiff.2 ⟨hcur, hd⟩,
      fun e => hone (iff_of_eq (congrArg (fun a => TT.pieceNat k n o a = g) e))⟩
    obtain ⟨q, hq, he⟩ := TT.exists_parent n hn o hg u hS
    have hb := hx' q hq fun hiff => by
      rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hone
      exacts [hone hiff, hone hiff.symm]
    refine mem_union_left _ (mem_filter.2 ⟨hS, ?_⟩)
    rcases Sym2.mem_iff.1 (he.symm ▸ Sym2.mem_iff.2 (hb.imp Eq.symm Eq.symm)) with e | e
    exacts [⟨false, e.symm⟩, ⟨true, e.symm⟩]
  refine (Nat.mul_le_mul_right w ((card_le_card hsub).trans (card_union_le _ _))).trans ?_
  rw [add_mul]
  exact Nat.add_le_add (hw _ (TT.card_filter_holds_le hn hg x))
    (Nat.mul_le_mul_right w (TT.card_dead_le o))

/-- **All bits of a piece** (the proof of Proposition J.2, p. 53: "Packets used up and zeros in
slots change this by a constant factor only, apart from `ΛN` at each given node"): for the gain
`w ≥ k` of `card_oneIn_piece_le`, `k` times the units that the parties of a piece ever hold and that
its roles read is at most `C (4 Y) + 4 (K + K) (Λ N) + 2 C M ^ C k`, for good outcomes and at most
`N` units at every base party, if `k ≤ 4 (K + K)`. -/
theorem cellCount_add_roleUnitCount_le (hk : 0 < k) (hkK : k ≤ 4 * (K + K)) (hM : 0 < M)
    (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) (hg : ∀ x, TT.plan.Good n o x) {w : ℕ}
    (hkw : k ≤ w) (hw : ∀ X : ℕ, (X : ℝ) ≤ (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) →
      X * w ≤ lg M ^ C * M * (N + M ^ 2)) (g : Fin (TT.pieceCount k)) :
    (cellCount n o (TT.piece hk n o) g + roleUnitCount TT.plan n o (TT.piece hk n o) g) * k ≤
      C * (4 * (lg M ^ C * M * (N + M ^ 2))) + 4 * (K + K) * (lg M ^ C * N) +
        2 * C * M ^ C * k := by
  set T := TT.stagedTree n o
  set h := UnitId.holder TT.moves.channelParty
  set Y := lg M ^ C * M * (N + M ^ 2)
  set P := univ.filter fun p => TT.piece hk n o p = g
  -- the units held and read, party by party
  have e : cellCount n o (TT.piece hk n o) g + roleUnitCount TT.plan n o (TT.piece hk n o) g =
      ∑ p ∈ P, (#((Plan.seenAt n o TT.E).filter (Play.Holds h p)) +
        ∑ r with TT.moves.roleParty r = p,
          (1 + Fintype.card ((TT.moves.law r.1).SlotAt r.2)) * TT.plan.count n o r.1) := by
    rw [sum_add_distrib, cellCount, roleUnitCount,
      ← sum_fiberwise_of_maps_to (g := TT.moves.roleParty) (t := P) fun r hr => by
        simpa [P] using hr]
    refine congrArg _ (sum_congr rfl fun p hp => sum_congr ?_ fun _ _ => rfl)
    rw [filter_filter]
    exact filter_congr fun r _ => ⟨And.right, fun hr => ⟨hr ▸ (mem_filter.1 hp).2, hr⟩⟩
  rw [e]
  refine (Nat.mul_le_mul_right k (sum_le_sum fun p _ =>
    TT.card_held_add_le n hn o hg p)).trans ?_
  rw [sum_add_distrib, sum_add_distrib, add_mul, add_mul]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · -- the units between the parties of the piece and their parents
    rw [← mul_sum, Nat.mul_assoc, sum_mul]
    refine Nat.mul_le_mul_left C (le_of_eq_of_le (sum_congr (filter_congr fun p _ => Fin.ext_iff)
      fun _ _ => rfl) (T.sum_piece_le (g := TT.baseWeight) (u := TT.units n o) (M := K + K) (Y := Y)
        (k := k) (fun p => (TT.units n o p + ∑ c ∈ T.children p, TT.units n o c) * k)
        (fun p => ?_) (fun x hx => ?_) g))
    · exact (Nat.mul_le_mul_left _ hkw).trans ((hw _ (TT.units_add_sum_le n o p)).trans
        (by omega))
    · have h1 := StagedTree.light_units_le (T := T) (by omega) hx
      have h2 := T.sumBelow_children_le (TT.units n o) x
      simp only [StagedTree.sumBelow, ← sum_mul, sum_add_distrib] at h1 h2 ⊢
      nlinarith
  · -- the units at the beginning of the base parties of the piece
    calc (∑ p ∈ P, if (p : ℕ) < K + K then lg M ^ C * N else 0) * k
        = (k * ∑ p ∈ P, TT.baseWeight p) * (lg M ^ C * N) := by
          rw [mul_sum, sum_mul, sum_mul]
          exact sum_congr rfl fun p _ => by unfold baseWeight; split_ifs <;> ring
      _ ≤ _ := Nat.mul_le_mul_right _ (TT.mul_sum_baseWeight_le hk hkK hM g)
  · -- the dead units
    refine Nat.mul_le_mul_right k ?_
    rw [← mul_sum, Nat.mul_comm 2 C, Nat.mul_assoc]
    exact Nat.mul_le_mul_left C (((sum_le_sum_of_subset (subset_univ P)).trans
      (sum_card_filter_holds_le h (TT.dead o))).trans (Nat.mul_le_mul_left 2 (TT.card_dead_le o)))

/-! ### The program of the pieces -/

/-- **The program of the pieces** (Proposition J.2: "The packets, the pieces and what each node
tensor consists of are computed from the numbers of packets and the outcomes by `v^C` binary
operations on numbers below `v^C`"): if `Y ≥ 6` bounds `(M N) ^ C`, `N`, the depth and the
number of the inputs, a program over the numbers below `Y ^ 4` with at most `Y ^ 15` steps
computes what the dealing program needs of the plan of the thin trees, with the pieces of the cut
by `k` as the groups, and checks that every base party has at most `N` units. It is the program
of the thin trees (Theorem H.2(d)) followed by `2 * depth + 6` stages of `Y ^ 12` gates. -/
theorem exists_slpTab (hk : 0 < k) {Y : ℕ} (hY : 6 ≤ Y) (hMN : (M * N) ^ C ≤ Y) (hN : N ≤ Y)
    (hdepth : TT.depth ≤ Y) (hin : (K + K) * (K + K) + Fintype.card TT.moves.Channel ≤ Y) :
    ∃ (nI pS : ℕ) (tab : SlpTab TT.plan (fun x => TT.piece hk x.counts x.outcomes) (Y ^ 4) nI pS),
      pS ≤ Y ^ 15 ∧ ∀ n, tab.Valid n ↔ ∀ p, ∑ a, ((n p a : ℕ) + n a p) ≤ N := by
  have hB : StepBase (Y ^ 4) Y := ⟨by omega, le_rfl⟩
  have hY4 : Y < Y ^ 4 := lt_of_eq_of_lt (pow_one Y).symm (Nat.pow_lt_pow_right (by omega)
    (by norm_num))
  have hKY : K + K ≤ Y := (Nat.le_add_right _ _).trans (TT.parties_le.trans hMN)
  have : NeZero (Y ^ 4) := ⟨by positivity⟩
  -- the inputs: the numbers of initial units and the outcomes
  let e := Fintype.equivFin ((Fin (K + K) × Fin (K + K)) ⊕ TT.moves.Channel)
  let inp (i : Fin (Fintype.card ((Fin (K + K) × Fin (K + K)) ⊕ TT.moves.Channel)))
      (x : (Fin (K + K) → Fin (K + K) → Fin (N + 1)) × (TT.moves.Channel → Fin TT.U1)) :
      Fin (Y ^ 4) :=
    ⟨Sum.elim (fun q => (x.1 q.1 q.2 : ℕ)) (fun ν => (x.2 ν : ℕ)) (e.symm i), by
      rcases e.symm i with q | ν
      · exact (Nat.lt_succ_iff.1 (x.1 q.1 q.2).2).trans_lt (hN.trans_lt hY4)
      · exact (x.2 ν).2.trans_le ((TT.U1_le.trans hMN).trans hY4.le)⟩
  -- the program of the thin trees, on these inputs
  have hlt (f) (hf : f ∈ TT.program.computed) (x) : f x < (M * N) ^ C :=
    TT.program.slpN.elim fun _ hP => (hP f hf).elim fun _ hj => hj x ▸ Fin.isLt _
  have hσ (i : Fin TT.program.numInputs) : ∃ j, ∀ x, inp j x =
      ⟨TT.program.input i x, (TT.program.input i x).2.trans_le (hMN.trans hY4.le)⟩ := by
    rcases TT.program.input_eq i with ⟨a, c, h⟩ | ⟨ν, h⟩
    · exact ⟨e (.inl (a, c)), fun x => Fin.ext (by simp [inp, h])⟩
    · exact ⟨e (.inr ν), fun x => Fin.ext (by simp [inp, h])⟩
  choose σ hσ using hσ
  have s0 : SlpN inp ((M * N) ^ C + 0 * Y ^ 12) TT.program.computed := by
    rw [zero_mul, add_zero]
    exact (TT.program.slpN.castLE (hMN.trans hY4.le) (fun _ _ => rfl)).mapInputs σ hσ
  -- the pieces
  obtain ⟨H1, s1, u1, f1⟩ := Pieces.pieces_stage (T := fun x : (Fin (K + K) → Fin (K + K) →
      Fin (N + 1)) × (TT.moves.Channel → Fin TT.U1) => TT.stagedTree x.1 x.2) (st := TT.stage)
    (dp := TT.depth) (rt := TT.root) (g := TT.baseWeight)
    (u := fun x : (Fin (K + K) → Fin (K + K) → Fin (N + 1)) × (TT.moves.Channel → Fin TT.U1) =>
      TT.units x.1 x.2) (M := K + K)
    (Yh := lg M ^ C * M * (N + M ^ 2)) (k := k) hB (by simpa using TT.parties_le.trans hMN)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s0 (fun q q' => TT.program.parent_mem q q')
    (fun q => TT.program.units_mem q)
    (fun q => (show TT.baseWeight q ≤ 1 by unfold baseWeight; split_ifs <;> omega).trans
      (by omega)) fun x q => (hlt _ (TT.program.units_mem q) x).le.trans hMN
  -- the cut units
  obtain ⟨H2, s2, u2, f2⟩ := hB.stage (a := 2) s1 (fun u => Set.indicator {x | u ∈ Play.cutUnits
      (UnitId.holder TT.moves.channelParty) (TT.piece hk x.1 x.2) (TT.plan.cur x.1 x.2 TT.E)} 1)
    (e := 1) (by simpa using TT.card_unit_le.trans hMN)
    (fun u => costP_iff.1 ((hB.and (CostP.of_mem (u1 (TT.program.cur_mem u)))
      (hB.rel (· ≠ ·) (Cost.of_mem (f1 (UnitId.holder TT.moves.channelParty u false)))
        (Cost.of_mem (f1 (UnitId.holder TT.moves.channelParty u true))))).congr fun x => by
          simp only [Play.mem_cutUnits, ne_eq, Fin.ext_iff]; rfl)) (by norm_num)
  -- the check of the numbers of units
  have hpair (x : (Fin (K + K) → Fin (K + K) → Fin (N + 1)) × (TT.moves.Channel → Fin TT.U1))
      (p a : Fin (K + K)) : (x.1 p a : ℕ) + x.1 a p ≤ 2 * Y :=
    (Nat.add_le_add (Nat.lt_succ_iff.1 (x.1 p a).2) (Nat.lt_succ_iff.1 (x.1 a p).2)).trans
      (by omega)
  have hY3 : 2 * Y ≤ 2 * Y ^ 3 := Nat.mul_le_mul_left 2 (Nat.le_self_pow (by norm_num) Y)
  obtain ⟨H3, s3, u3, f3⟩ := hB.stage (a := 6) s2
    (fun _ : Unit => {x | ∀ p, ∑ a, ((x.1 p a : ℕ) + x.1 a p) ≤ N}.indicator 1) (e := 0)
    (by simp) (fun _ => costP_iff.1 (hB.forall_univ (by simpa using hKY) fun p =>
      hB.rel1 (· ≤ N) (hB.sum univ (by simpa using hKY) (fun a _ => hB.op (· + ·)
        (Cost.of_mem (u2 (u1 (TT.program.initial_mem p a))))
        (Cost.of_mem (u2 (u1 (TT.program.initial_mem a p))))
        fun x => hB.lt_of_le_two_mul_pow_three ((hpair x p a).trans hY3))
        fun x => hB.lt_of_le_two_mul_pow_three ((sum_le_sum fun a _ => hpair x p a).trans (by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
          have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
          nlinarith [hY23])))))
    (by norm_num)
  -- the program as a list of steps
  obtain ⟨fn, hfn, hmem⟩ := s3.exists_isSlpStep
  choose gate hgate using hmem
  have hc : Fintype.card ((Fin (K + K) × Fin (K + K)) ⊕ TT.moves.Channel) ≤ Y := by
    simpa using hin
  have h1 : 2 * Y ≤ Y ^ 13 := (Nat.mul_le_mul_right Y (by omega : 2 ≤ Y)).trans
    (by rw [← pow_two]; exact Nat.pow_le_pow_right (by omega) (by norm_num))
  have h2 : 4 * Y ^ 13 ≤ Y ^ 15 :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 2 ≤ Y) 2)).trans_eq
      (pow_add Y 2 13).symm
  have h3 : (0 + 2 * TT.depth + 4 + 1 + 1) * Y ^ 12 ≤ 3 * Y ^ 13 :=
    calc _ ≤ (3 * Y) * Y ^ 12 := Nat.mul_le_mul_right _ (by omega)
      _ = 3 * Y ^ 13 := by ring
  have hind {P : (Fin (K + K) → Fin (K + K) → Fin (N + 1)) × (TT.moves.Channel → Fin TT.U1) →
      Prop} [DecidablePred P] (x) : (Set.indicator {x | P x} 1 x : ℕ) = 1 ↔ P x := by
    by_cases h : P x <;> simp [h]
  refine ⟨_, _,
    { input := e.symm, inp := fun i x => inp i (x.counts, x.outcomes), inp_val := fun i x => rfl,
      fn := fun k x => fn k (x.counts, x.outcomes), isSlpStep := fun k hk => (hfn k hk).comp _,
      curGate := fun u => gate _ (u3 (u2 (u1 (TT.program.cur_mem u)))),
      fn_curGate := fun u x => (hgate _ _ _).trans (by simp [Set.indicator_apply]),
      cutGate := fun u => gate _ (u3 (f2 u)),
      fn_cutGate := fun u x => (hgate _ _ _).trans (by simp [Set.indicator_apply]),
      givenGate := fun z u => gate _ (u3 (u2 (u1 (TT.program.given_mem z u)))),
      fn_givenGate := fun z u x => (hgate _ _ _).trans (by simp [Set.indicator_apply]),
      countGate := fun y => gate _ (u3 (u2 (u1 (TT.program.count_mem y)))),
      fn_countGate := fun y x => hgate _ _ _, Valid := fun n => ∀ p, ∑ a, ((n p a : ℕ) + n a p) ≤ N,
      validGate := gate _ (f3 ()), fn_validGate := fun x => (hgate _ _ _).symm ▸ hind _,
      goodGate := fun y => gate _ (u3 (u2 (u1 (TT.program.good_mem y)))),
      fn_goodGate := fun y x => (hgate _ _ _).symm ▸ hind _,
      groupGate := fun a => gate _ (u3 (u2 (f1 a))), fn_groupGate := fun a x => hgate _ _ _ },
    by omega, fun n => Iff.rfl⟩

end Pieces

end Cslib.Circuits.Arithmetic.Separation.Trees.ThinTrees
