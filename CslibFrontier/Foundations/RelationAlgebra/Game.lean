/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.AtomicNetwork
public import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Pairing

/-!
# The representation game on atomic networks

The game `G(A)` of [HirschHodkinson2001], Definition 1, is played by ∀ and ∃ on the atomic
networks of a finite relation algebra `A`. ∀ opens with an atom, and ∃ answers with a network
having an edge labelled by it. In each later round ∀ picks an edge `(m, n)` of the current network
`N` and atoms `a`, `b` with `N(m, n) ≤ a;b`, and ∃ answers with a network extending `N` that has
a node `p` with `N(m, p) = a` and `N(p, n) = b`. ∃ wins a play when she answers in every round.
Theorem 1 of the source states that `A` is representable if and only if ∃ has a winning strategy.

## Formalization

* The rules mention only the converse, the identity atoms and the cycles, so the game is defined
  for an `AtomFrame`. For the frame of an `AtomStructure A` it is the game of the complex algebra
  of `A`, and every finite relation algebra is the complex algebra of its atom structure. No law
  of an atom structure is assumed: they all hold on a frame on which ∃ has a winning strategy
  (`AtomStructure.ofHasWinningStrategy`).
* A `Position` is a network on `Fin n`, and `P ≤ Q` means that `P` is the restriction of `Q` to
  its first `P.size` nodes. A chain `N₀ ⊆ N₁ ⊆ ⋯` of finite networks as in the source becomes a
  chain of positions when its nodes are numbered in the order in which they appear, and the rules
  do not depend on the names of the nodes.
* A `Strategy` gives ∃'s network as a function of the current network and the move of ∀, and it
  is winning when it answers legally at every network reachable in a play that follows it. Whether
  a move or an answer is legal depends only on the current network, so ∃ gains nothing from
  strategies that depend on the whole play: the networks arising when she follows a winning one
  form a set as in `hasWinningStrategy_iff`, which yields a winning strategy in the present sense.
* The source's Convention 1 is not part of the definition: ∃ may add any number of nodes, and ∀
  may make a move that already has a witness. A family of networks closed under single-node
  answers to the moves that have no witness yet gives a winning strategy
  (`HasWinningStrategy.of_forall_exists_comap_castSucc`); the converse is not proved here.
* `Representable` asks for an injective homomorphism into a product of algebras of all relations
  on a set. The source's representations are isomorphisms onto an algebra of relations on one set
  whose unit is an equivalence relation; restricting to the classes of the unit turns one into the
  other [HirschHodkinson1997], Section 3.2. The source's representations have non-empty domains;
  here the index and base types may be empty, so the one-element algebra is representable and ∃
  wins the game on no atoms, in which ∀ has no opening move.

## Main definitions

* `Cslib.RelationAlgebra.AtomFrame.Position`, `Position.Move`, `Position.Answers`: the finite
  networks, the moves of ∀ and the legal answers of ∃.
* `Cslib.RelationAlgebra.AtomFrame.Strategy`, `Strategy.IsWinning`, `HasWinningStrategy`: the
  strategies of ∃.
* `Cslib.RelationAlgebra.AtomStructure.ofHasWinningStrategy`: the atom structure on a frame on
  which ∃ has a winning strategy; its associativity is [HirschHodkinson2001], Lemma 7.

## Main results

* `Cslib.RelationAlgebra.AtomFrame.hasWinningStrategy_iff`: ∃ has a winning strategy if and only
  if some set of networks realizes every atom and is closed under answering the moves of ∀.
* `Cslib.RelationAlgebra.AtomFrame.HasWinningStrategy.exists_saturated`, `.of_saturated`: over
  countably many atoms, ∃ has a winning strategy if and only if every atom labels an edge of a
  saturated network.
* `Cslib.RelationAlgebra.representable_complexAlgebra_iff`,
  `Cslib.RelationAlgebra.representable_iff_hasWinningStrategy`: Theorem 1 of
  [HirschHodkinson2001], for the complex algebra of a finite atom structure and for a finite
  relation algebra. The two directions are
  `Cslib.RelationAlgebra.Representation.hasWinningStrategy`, for representations in any universes,
  and `Cslib.RelationAlgebra.AtomFrame.HasWinningStrategy.representable`, which needs only
  countably many atoms. The proof is that of [HirschHodkinson1997], Lemma 6.

## References

* [R. Hirsch, I. Hodkinson, *Step by step — building representations in algebraic
  logic*][HirschHodkinson1997]
* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

universe u v w

namespace Cslib.RelationAlgebra

variable {α : Type u}

namespace AtomFrame

variable (F : AtomFrame α)

/-- A position of the game `G(F)`: a finite atomic network, with its nodes numbered
`0, …, size - 1`. -/
structure Position where
  /-- The number of nodes. -/
  size : ℕ
  /-- The network on the nodes `0, …, size - 1`. -/
  network : AtomicNetwork F (Fin size)

variable {F}

namespace Position

/-- `P ≤ Q` when `Q` extends `P`: the nodes of `P` are nodes of `Q`, with the same labels. -/
instance : Preorder F.Position where
  le P Q := ∃ h : P.size ≤ Q.size, Q.network.comap (Fin.castLEEmb h) = P.network
  le_refl P := ⟨le_rfl, rfl⟩
  le_trans P Q R := fun ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ => ⟨h₁.trans h₂, by rw [← e₁, ← e₂]; rfl⟩

theorem size_mono : Monotone (size : F.Position → ℕ) := fun _ _ h => h.1

theorem network_castLE {P Q : F.Position} (h : P ≤ Q) (i j : Fin P.size) :
    Q.network (i.castLE (size_mono h)) (j.castLE (size_mono h)) = P.network i j :=
  congrArg (fun N : AtomicNetwork F _ => N i j) h.2

/-- A move of ∀ at the position `P`: two nodes `m`, `n` and two atoms `a`, `b` whose product lies
above the label of `(m, n)`. -/
structure Move (P : F.Position) where
  /-- The first node of the edge picked. -/
  m : Fin P.size
  /-- The second node of the edge picked. -/
  n : Fin P.size
  /-- The atom demanded on the edge from `m` to the witness. -/
  a : α
  /-- The atom demanded on the edge from the witness to `n`. -/
  b : α
  /-- The source's `a;b ≥ N(m, n)`. -/
  legal : (a, b, P.network m n) ∈ F.cycles

/-- The position `Q` is a legal response of ∃ to the move `v` at `P`: it extends `P` and has a
node `p` with `Q(m, p) = a` and `Q(p, n) = b`. -/
@[expose]
def Answers (Q : F.Position) {P : F.Position} (v : P.Move) : Prop :=
  ∃ h : P ≤ Q, ∃ p, Q.network (v.m.castLE (size_mono h)) p = v.a ∧
    Q.network p (v.n.castLE (size_mono h)) = v.b

end Position

variable (F) in
/-- A strategy for ∃ in the game `G(F)`: her network in the opening round, as a function of the
atom picked by ∀, and her network in each later round, as a function of the current network and
the move of ∀. -/
structure Strategy where
  /-- The network ∃ plays in round zero when ∀ picks the atom `a`. -/
  opening : α → F.Position
  /-- The network ∃ plays when ∀ makes the move `v` at the network `P`. -/
  answer (P : F.Position) : P.Move → F.Position

namespace Strategy

/-- The networks that arise in the plays of `G(F)` in which ∃ follows the strategy `σ`. -/
inductive Reachable (σ : F.Strategy) : F.Position → Prop
  /-- Her network in round zero, for each atom ∀ may pick. -/
  | opening (a : α) : σ.Reachable (σ.opening a)
  /-- Her network after a move of ∀ at a network that has arisen. -/
  | answer {P : F.Position} (v : P.Move) : σ.Reachable P → σ.Reachable (σ.answer P v)

/-- A strategy is winning when it gives a legal response in every round of every play in which ∃
follows it: her opening network has an edge labelled by the atom ∀ picked, and each later network
answers his move. -/
structure IsWinning (σ : F.Strategy) : Prop where
  opening (a : α) : ∃ m n, (σ.opening a).network m n = a
  answer {P : F.Position} (v : P.Move) : σ.Reachable P → (σ.answer P v).Answers v

end Strategy

variable (F) in
/-- ∃ has a winning strategy in the game `G(F)` of [HirschHodkinson2001], Definition 1. -/
@[expose]
def HasWinningStrategy : Prop := ∃ σ : F.Strategy, σ.IsWinning

/-- ∃ has a winning strategy exactly when some set of networks contains, for every atom, a network
with an edge so labelled, and contains a response to every move of ∀ at each of its members. -/
theorem hasWinningStrategy_iff : F.HasWinningStrategy ↔ ∃ W : Set F.Position,
    (∀ a, ∃ P ∈ W, ∃ m n, P.network m n = a) ∧ ∀ P ∈ W, ∀ v : P.Move, ∃ Q ∈ W, Q.Answers v := by
  classical
  refine ⟨fun ⟨σ, hσ⟩ => ⟨{P | σ.Reachable P}, fun a => ⟨_, .opening a, hσ.opening a⟩,
      fun _ hP v => ⟨_, .answer v hP, hσ.answer v hP⟩⟩, fun ⟨W, hopen, hW⟩ => ?_⟩
  choose opening hopenW hopen using hopen
  have hW' (P : F.Position) (v : P.Move) : ∃ Q, P ∈ W → Q ∈ W ∧ Q.Answers v :=
    if hP : P ∈ W then
      let ⟨Q, hQ⟩ := hW P hP v
      ⟨Q, fun _ => hQ⟩
    else ⟨P, fun h => (hP h).elim⟩
  choose answer hanswer using hW'
  have hreach (P : F.Position) (hP : Strategy.Reachable ⟨opening, answer⟩ P) : P ∈ W := by
    induction hP with
    | opening a => exact hopenW a
    | answer v _ ih => exact (hanswer _ v ih).1
  exact ⟨⟨opening, answer⟩, hopen, fun {P} v hP => (hanswer P v (hreach P hP)).2⟩

/-- The form of [HirschHodkinson2001], Convention 1, parts (1) and (2): to win, it is enough that
∃ answers the moves that have no witness yet, each by adding a single node as the witness. -/
theorem HasWinningStrategy.of_forall_exists_comap_castSucc
    (W : ∀ n, Set (AtomicNetwork F (Fin n)))
    (opening : ∀ a, ∃ n, ∃ N ∈ W n, ∃ i j, N i j = a)
    (answer : ∀ n, ∀ N ∈ W n, ∀ i j a b, (a, b, N i j) ∈ F.cycles →
      (∀ p, N i p = a → N p j ≠ b) → ∃ N' ∈ W (n + 1), N'.comap Fin.castSuccEmb = N ∧
        N' i.castSucc (Fin.last n) = a ∧ N' (Fin.last n) j.castSucc = b) :
    F.HasWinningStrategy := by
  classical
  exact hasWinningStrategy_iff.mpr ⟨{P | P.network ∈ W P.size},
    fun a =>
      let ⟨n, N, hN, h⟩ := opening a
      ⟨⟨n, N⟩, hN, h⟩,
    fun ⟨n, N⟩ hN ⟨i, j, a, b, hab⟩ =>
      if hp : ∃ p, N i p = a ∧ N p j = b then ⟨⟨n, N⟩, hN, le_rfl, hp⟩
      else let ⟨N', hN', hNN', hab'⟩ := answer n N hN i j a b hab fun p ha hb => hp ⟨p, ha, hb⟩
        ⟨⟨n + 1, N'⟩, hN', ⟨n.le_succ, hNN'⟩, Fin.last n, hab'⟩⟩

/-- If every atom labels an edge of some saturated network, then ∃ has a winning strategy: she
plays finite subnetworks of these networks. -/
theorem HasWinningStrategy.of_saturated
    (h : ∀ a, ∃ (D : Type w) (N : AtomicNetwork F D), N.Saturated ∧ ∃ m n, N m n = a) :
    F.HasWinningStrategy := by
  classical
  -- a finite set of nodes can be enlarged to contain any further node
  have extend {D : Type w} {k : ℕ} (f : Fin k ↪ D) (p : D) : ∃ (k' : ℕ) (f' : Fin k' ↪ D)
      (hk : k ≤ k'), (∀ i, f' (i.castLE hk) = f i) ∧ p ∈ Set.range f' :=
    if hp : p ∈ Set.range f then ⟨k, f, le_rfl, fun _ => rfl, hp⟩
    else ⟨k + 1, ⟨Fin.snoc f p, Fin.snoc_injective_of_injective f.injective hp⟩, k.le_succ,
      fun i => Fin.snoc_castSucc (α := fun _ => D) p f i,
      Fin.last k, Fin.snoc_last (α := fun _ => D) p f⟩
  refine hasWinningStrategy_iff.mpr ⟨{P | ∃ (D : Type w) (N : AtomicNetwork F D)
    (f : Fin P.size ↪ D), N.Saturated ∧ N.comap f = P.network}, fun a => ?_, ?_⟩
  · obtain ⟨D, N, hN, m, n, rfl⟩ := h a
    obtain ⟨_, f₁, -, -, i, rfl⟩ := extend (.ofIsEmpty : Fin 0 ↪ D) m
    obtain ⟨k₂, f₂, hk, hf, j, rfl⟩ := extend f₁ n
    exact ⟨⟨k₂, N.comap f₂⟩, ⟨D, N, f₂, hN, rfl⟩, i.castLE hk, j, by simp [hf]⟩
  · rintro P ⟨D, N, f, hN, hP⟩ ⟨m, n, a, b, hab⟩
    obtain ⟨p, rfl, rfl⟩ := hN (hP ▸ hab)
    obtain ⟨k', f', hk, hf, q, rfl⟩ := extend f p
    exact ⟨⟨k', N.comap f'⟩, ⟨D, N, f', hN, rfl⟩,
      ⟨hk, hP ▸ AtomicNetwork.ext fun _ _ => by simp [hf]⟩, q, by simp [hf], by simp [hf]⟩

/-- If ∃ has a winning strategy and there are countably many atoms, then every atom labels an edge
of a saturated network: the limit of a play in which ∀ picks the atom and then makes every move
eventually. -/
theorem HasWinningStrategy.exists_saturated [Countable α] (h : F.HasWinningStrategy) (a : α) :
    ∃ (D : Type) (N : AtomicNetwork F D), N.Saturated ∧ ∃ m n, N m n = a := by
  obtain ⟨W, hopen, hW⟩ := hasWinningStrategy_iff.mp h
  obtain ⟨P₀, hP₀, m₀, n₀, ha⟩ := hopen a
  have : Nonempty α := ⟨a⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ × ℕ × α × α)
  -- a round in which ∀ makes the move coded by `d`, if `d` codes a move
  have step (P : W) (d : ℕ × ℕ × α × α) : ∃ Q : W, P.1 ≤ Q.1 ∧
      ∀ v : P.1.Move, (v.m.1, v.n.1, v.a, v.b) = d → Q.1.Answers v := by
    by_cases hd : ∃ v : P.1.Move, (v.m.1, v.n.1, v.a, v.b) = d
    · obtain ⟨v, rfl⟩ := hd
      obtain ⟨Q, hQ, hQv⟩ := hW P.1 P.2 v
      refine ⟨⟨Q, hQ⟩, hQv.1, fun ⟨_, _, _, _, _⟩ hv => ?_⟩
      cases v
      simp only [Prod.mk.injEq, Fin.val_inj] at hv
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
      exact hQv
    · exact ⟨P, le_rfl, fun v hv => (hd ⟨v, hv⟩).elim⟩
  choose next hle hnext using step
  -- the play in which the moves of ∀ follow `e`, each code recurring infinitely often
  let play : ℕ → W := fun k => k.rec ⟨P₀, hP₀⟩ fun k P => next P (e k.unpair.1)
  have hplay : Monotone fun k => (play k).1 := monotone_nat_of_le_succ fun k => hle _ _
  have lt_size {i k l : ℕ} (hkl : k ≤ l) (hi : i < (play k).1.size) : i < (play l).1.size :=
    hi.trans_le (Position.size_mono (hplay hkl))
  -- its limit
  let D : Type := {i : ℕ // ∃ k, i < (play k).1.size}
  have common (d e : D) : ∃ k, d.1 < (play k).1.size ∧ e.1 < (play k).1.size :=
    let ⟨k, hk⟩ := d.2
    let ⟨l, hl⟩ := e.2
    ⟨max k l, lt_size (le_max_left k l) hk, lt_size (le_max_right k l) hl⟩
  choose lvl hlvl using common
  let label (d e : D) : α := (play (lvl d e)).1.network ⟨d, (hlvl d e).1⟩ ⟨e, (hlvl d e).2⟩
  have label_eq (d e : D) (k : ℕ) (hd : d.1 < (play k).1.size) (he : e.1 < (play k).1.size) :
      label d e = (play k).1.network ⟨d, hd⟩ ⟨e, he⟩ :=
    (le_total k (lvl d e)).elim (fun hk => Position.network_castLE (hplay hk) ⟨d, hd⟩ ⟨e, he⟩)
      fun hk => (Position.network_castLE (hplay hk) ⟨d, (hlvl d e).1⟩ ⟨e, (hlvl d e).2⟩).symm
  let N : AtomicNetwork F D :=
    { label := label
      label_mem_id := (AtomicNetwork.label_mem_id _).trans (Fin.ext_iff.trans Subtype.ext_iff.symm)
      conv_label := fun d e => by
        rw [label_eq e d _ (hlvl d e).2 (hlvl d e).1]
        exact AtomicNetwork.conv_label _ _ _
      label_mem_cycles := fun d e f => by
        obtain ⟨l, hf⟩ := f.2
        have hd := lt_size (le_max_left (lvl d e) l) (hlvl d e).1
        have he := lt_size (le_max_left (lvl d e) l) (hlvl d e).2
        have hf := lt_size (le_max_right (lvl d e) l) hf
        rw [label_eq d e _ hd he, label_eq e f _ he hf, label_eq d f _ hd hf]
        exact AtomicNetwork.label_mem_cycles _ _ _ _ }
  refine ⟨D, N, fun m n a b hab => ?_, ⟨m₀, 0, m₀.2⟩, ⟨n₀, 0, n₀.2⟩,
    (label_eq _ _ 0 m₀.2 n₀.2).trans ha⟩
  obtain ⟨j, hj⟩ := he (m, n, a, b)
  let k := Nat.pair j (lvl m n)
  have hm := lt_size (Nat.right_le_pair j (lvl m n)) (hlvl m n).1
  have hn := lt_size (Nat.right_le_pair j (lvl m n)) (hlvl m n).2
  obtain ⟨_, p, hpa, hpb⟩ := hnext (play k) (e k.unpair.1)
    ⟨⟨m, hm⟩, ⟨n, hn⟩, a, b, label_eq m n k hm hn ▸ hab⟩ (by rw [Nat.unpair_pair, hj])
  exact ⟨⟨p, k + 1, p.2⟩, (label_eq _ _ (k + 1) (lt_size k.le_succ hm) p.2).trans hpa,
    (label_eq _ _ (k + 1) p.2 (lt_size k.le_succ hn)).trans hpb⟩

end AtomFrame

/-- In a set of networks closed under ∃'s responses, a move at a member is answered by a member
containing a copy of it and a witness. -/
private theorem exists_answer {F : AtomFrame α} {W : Set F.Position}
    (hW : ∀ P ∈ W, ∀ v : P.Move, ∃ Q ∈ W, Q.Answers v) {P : F.Position} (hP : P ∈ W)
    (m n : Fin P.size) {a b : α} (hab : (a, b, P.network m n) ∈ F.cycles) :
    ∃ Q ∈ W, ∃ f : Fin P.size → Fin Q.size, (∀ i j, Q.network (f i) (f j) = P.network i j) ∧
      ∃ p, Q.network (f m) p = a ∧ Q.network p (f n) = b :=
  let ⟨Q, hQ, hPQ, hp⟩ := hW P hP ⟨m, n, a, b, hab⟩
  ⟨Q, hQ, Fin.castLE (AtomFrame.Position.size_mono hPQ), AtomFrame.Position.network_castLE hPQ, hp⟩

/-- A frame on which ∃ has a winning strategy is an atom structure. Associativity is
[HirschHodkinson2001], Lemma 7: ∀ opens with `p ≤ r;q`, then demands `r`, `q` on that edge and
`s`, `t` on the new edge labelled `q`, and the remaining edge of the resulting network is the atom
required. The source assumes the other laws; they follow in the same way from at most one move. -/
@[expose, simps]
def AtomStructure.ofHasWinningStrategy (F : AtomFrame α) (h : F.HasWinningStrategy) :
    AtomStructure α where
  conv := F.conv
  id := F.id
  cycles := F.cycles
  assoc {r q p s t} h₁ h₂ := by
    obtain ⟨W, hopen, hW⟩ := AtomFrame.hasWinningStrategy_iff.mp h
    obtain ⟨P, hP, m, n, rfl⟩ := hopen p
    obtain ⟨Q, hQ, f, hf, x, rfl, rfl⟩ := exists_answer hW hP m n h₁
    obtain ⟨R, hR, g, hg, y, rfl, rfl⟩ := exists_answer hW hQ x (f n) h₂
    refine ⟨R.network (g (f m)) y, ?_, ?_⟩
    · rw [← hf m n, ← hg (f m) (f n)]
      exact R.network.label_mem_cycles _ _ _
    · rw [← hg (f m) x]
      exact R.network.label_mem_cycles _ _ _
  id_cycle_right {s r p} hs hc := by
    obtain ⟨W, hopen, hW⟩ := AtomFrame.hasWinningStrategy_iff.mp h
    obtain ⟨P, hP, m, n, rfl⟩ := hopen p
    obtain ⟨Q, hQ, f, hf, x, rfl, rfl⟩ := exists_answer hW hP m n hc
    rw [← hf m n, Q.network.label_mem_id.mp hs]
  exists_id_cycle_right r := by
    obtain ⟨W, hopen, -⟩ := AtomFrame.hasWinningStrategy_iff.mp h
    obtain ⟨P, hP, m, n, rfl⟩ := hopen r
    exact ⟨P.network n n, P.network.label_mem_id.mpr rfl, P.network.label_mem_cycles m n n⟩
  cycle_left {r s t} hc := by
    obtain ⟨W, hopen, hW⟩ := AtomFrame.hasWinningStrategy_iff.mp h
    obtain ⟨P, hP, m, n, rfl⟩ := hopen t
    obtain ⟨Q, hQ, f, hf, x, rfl, rfl⟩ := exists_answer hW hP m n hc
    rw [← hf m n, Q.network.conv_label]
    exact Q.network.label_mem_cycles _ _ _

@[simp]
theorem AtomStructure.frame_ofHasWinningStrategy (F : AtomFrame α) (h : F.HasWinningStrategy) :
    (AtomStructure.ofHasWinningStrategy F h).frame = F := rfl

variable {A : AtomStructure α}

/-- If ∃ has a winning strategy in the game of an atom structure with countably many atoms, then
its complex algebra is representable. -/
theorem AtomFrame.HasWinningStrategy.representable [Countable α]
    (h : A.frame.HasWinningStrategy) : Representable (ComplexAlgebra A) := by
  choose D N hN m n hmn using h.exists_saturated
  refine ⟨α, fun a => ULift.{u} (D a),
    ⟨.pi fun a => ((hN a).comap Equiv.ulift).hom, fun x y hxy => ?_⟩⟩
  ext a
  simpa [hmn] using congr(((⟨m a⟩, ⟨n a⟩) : ULift (D a) × ULift (D a)) ∈ $hxy a)

/-- If the complex algebra of a finite atom structure has a representation, with index and base
types in any universes, then ∃ has a winning strategy in its game. -/
theorem Representation.hasWinningStrategy [Finite α] {ι : Type v} {β : ι → Type w}
    (r : Representation (ComplexAlgebra A) ι β) : A.frame.HasWinningStrategy :=
  .of_saturated fun a => by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (show r.hom ⟨{a}⟩ ≠ ⊥ from fun h =>
      (congr(a ∈ $(r.injective (h.trans (map_bot r.hom).symm)))).mp rfl)
    obtain ⟨⟨x, y⟩, hxy⟩ := Set.nonempty_iff_ne_empty.mpr hi
    obtain ⟨N, hN, hmem⟩ := ((RelationAlgebraHom.eval _ i).comp r.hom).exists_saturated
    exact ⟨β i, N, hN, x, y, (hmem _ x y).mp hxy⟩

/-- **Theorem 1 of [HirschHodkinson2001]**: the complex algebra of a finite atom structure is
representable if and only if ∃ has a winning strategy in its game. -/
theorem representable_complexAlgebra_iff [Finite α] (A : AtomStructure α) :
    Representable (ComplexAlgebra A) ↔ A.frame.HasWinningStrategy :=
  ⟨fun ⟨_, _, ⟨r⟩⟩ => r.hasWinningStrategy, fun h => h.representable⟩

/-- **Theorem 1 of [HirschHodkinson2001]**, as stated there: a finite relation algebra is
representable if and only if ∃ has a winning strategy in the game on its atoms. -/
theorem representable_iff_hasWinningStrategy (α : Type u) [RelationAlgebra α] [Finite α] :
    Representable α ↔ (atomStructure α).frame.HasWinningStrategy := by
  cases nonempty_fintype α
  let : CompleteAtomicRelationAlgebra α :=
    { ‹RelationAlgebra α›, Fintype.toCompleteAtomicBooleanAlgebra α with }
  have e : RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) := complexAlgebraEquiv
  exact Iff.trans ⟨.of_injective e.symm.toHom (EquivLike.injective e.symm),
    .of_injective e.toHom (EquivLike.injective e)⟩ (representable_complexAlgebra_iff _)

end Cslib.RelationAlgebra
