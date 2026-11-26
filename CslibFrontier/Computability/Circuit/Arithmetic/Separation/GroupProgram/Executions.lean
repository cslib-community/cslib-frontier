/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.GroupScript
public import CslibFrontier.Foundations.Algebra.BigOperators.WriteSteps
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves

/-!
# The value of a group as a sum over executions

The value of a group of parties after the moves of a plan (`Cut.Plan.groupValue`) is a sum, over
the contents of the copies of units at the parties of the group, of the product of the tables of
the parties. The evaluator of [AnthropicVPVNP2026] guesses these contents one step after the
other: first every base party of the group writes its copies of the initial units
(`baseWriteStep`), choosing what it writes and reads; then every role of the group, in the order
of the moves, writes the copies of the new units of its channels (`roleWriteStep`), choosing an
index and the strings for every bit. The factor of a step is the table of its party or role, every
cell of the group is written once and a step reads only what the steps before it have written, so
the value of the group is the sum over all executions of the steps (`groupValue_eq_exec`).

## Main definitions

* `groupCells`: the cells of a group.
* `baseCells`, `initialContents`, `InitialFits`, `baseWriteStep`: the cells that a base party
  writes, their contents, the conditions on its choice, and its step.
* `roleCells`, `roleContents`, `roleWriteStep`: the cells that a role writes, their contents, and
  its step.
* `groupSteps`: the steps of a group.

## Main results

* `mem_groupCells`, `mem_baseCells`, `mem_roleCells`, `roleCells_subset_groupCells`,
  `roleContents_new`: the cells and the contents.
* `groupValue_eq_exec`: the value of a group is the sum over the executions of its steps, of the
  condition that the copies of the current units agree within the group and with the contents of
  the units shared with other groups.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54) guesses the contents of the
inner packets and then compares them. Ported from the source modules `Nc.Grp.GrpSteps` and
`Nc.Grp.GrpVal`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset Tape

variable {F : Type*} {Γ S Q : Type} [CommSemiring F] [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {A' E K U0 U1 ub c : ℕ} {G : Type*} [DecidableEq G]
  {M : Moves F (K + K + A') E}

/-- The cells of the group `g`: the copies, at the parties of the group, of the units seen in the
end that they hold. -/
def groupCells (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) : Finset (Cell M U0 U1) :=
  {c | grp c.party = g ∧ c.unit ∈ Plan.seenAt n o E ∧
    Play.Holds (UnitId.holder M.channelParty) c.party c.unit}

@[simp] theorem mem_groupCells {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.Channel → Fin U1} {grp : Fin (K + K + A') → G} {g : G} {c : Cell M U0 U1} :
    c ∈ groupCells n o grp g ↔ grp c.party = g ∧ c.unit ∈ Plan.seenAt n o E ∧
      Play.Holds (UnitId.holder M.channelParty) c.party c.unit := by
  simp [groupCells]

/-- The cells that the base party `p` writes: its copies of the initial units seen in the end, if
it is in the group `g`. -/
def baseCells (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) (p : Fin (K + K)) : Finset (Cell M U0 U1) :=
  (groupCells n o grp g).filter fun c => c.party = Fin.castAdd A' p ∧ c.unit ∈ initialUnits n

/-- The cells that the role `r` writes: the copies at its party of the new units of its move seen
in the end, if its party is in the group `g`. -/
def roleCells (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) (r : M.Role) : Finset (Cell M U0 U1) :=
  (groupCells n o grp g).filter fun c => c.party = M.roleParty r ∧ c.unit ∈ newUnits M r.1 o

section Subset

variable {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G}

theorem roleCells_subset_groupCells (r : M.Role) : roleCells n o grp g r ⊆ groupCells n o grp g :=
  filter_subset _ _

end Subset

/-- The contents that the base party `p` writes, for what it writes (`R`) and reads (`C`): unit
`k` of the string from `a` to `b` is unit `k` of the bit string of the segments that `p` writes
for `b` if `a = p`, and of the segments that `p` reads from `a` otherwise. New units are
absent. -/
@[expose] noncomputable def initialContents {N : Type*} (cb : Option Γ → BitString c)
    (R C : Option S → Fin (K + K) → List Γ) (p : Fin (K + K)) :
    UnitId (K + K) U0 N U1 → UnitContent ub
  | .init a b k => unitsOf ub (segmentString cb fun s => if a = p then R s b else C s a) k
  | .new _ _ => none

/-- The conditions on what the base party `p` writes (`R`) and reads (`C`), besides its weight:
the row data `ρ` are those of `R`, the strings from `p` to every party `b` and from `b` to `p`
have `n p b` and `n b p` units, and the string from `p` to itself has the same first `U0` units
as written and as read. -/
@[expose] noncomputable def InitialFits (ub U0 : ℕ) (cb : Option Γ → BitString c)
    (ρ : Option S → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) :
    Prop :=
  (∀ s, (ρ s).Ok (R s)) ∧ (∀ b, unitCount ub (segmentString cb fun s => R s b) = n p b) ∧
    (∀ b, unitCount ub (segmentString cb fun s => C s b) = n b p) ∧
    ∀ k : Fin U0, unitsOf ub (segmentString cb fun s => R s p) k =
      unitsOf ub (segmentString cb fun s => C s p) k

noncomputable instance (ub U0 : ℕ) (cb : Option Γ → BitString c) (ρ : Option S → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) :
    Decidable (InitialFits ub U0 cb ρ n p R C) := by
  unfold InitialFits
  infer_instance

/-- The contents that the role `r` writes for the indices and strings `ig` of its blocks: unit
`k` of a channel of the role is unit `k` of the string on the channel (`Cut.sideString`). -/
@[expose] noncomputable def roleContents (r : M.Role) {B : ℕ}
    (ig : Σ i : Fin B → (M.law r.1).Index,
      ∀ j (ν : (M.law r.1).ChannelAt r.2), BitString ((M.law r.1).length (i j) ν)) :
    UnitId (K + K) U0 M.Channel U1 → UnitContent ub
  | .init _ _ _ => none
  | .new ν k => if h : ∃ ν' : (M.law r.1).ChannelAt r.2, (⟨r.1, ν'.1⟩ : M.Channel) = ν then
      unitsOf ub (sideString (M.law r.1).label (fun i => (M.law r.1).length i h.choose) ig.1
        fun j => ig.2 j h.choose) k
    else none

theorem roleContents_new (r : M.Role) {B : ℕ}
    (ig : Σ i : Fin B → (M.law r.1).Index,
      ∀ j (ν : (M.law r.1).ChannelAt r.2), BitString ((M.law r.1).length (i j) ν))
    (ν : (M.law r.1).ChannelAt r.2) (k : Fin U1) :
    roleContents (ub := ub) (U0 := U0) r ig (.new ⟨r.1, ν.1⟩ k) =
      unitsOf ub (sideString (M.law r.1).label (fun i => (M.law r.1).length i ν) ig.1
        fun j => ig.2 j ν) k := by
  have h : ∃ ν' : (M.law r.1).ChannelAt r.2, (⟨r.1, ν'.1⟩ : M.Channel) = ⟨r.1, ν.1⟩ := ⟨ν, rfl⟩
  rw [roleContents, dite_eq_left_of_eq_true (eq_true h),
    Subtype.ext (eq_of_heq (Sigma.mk.inj h.choose_spec).2)]

section Steps

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → BitString c)
  (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
  (o : M.Channel → Fin U1) (grp : Fin (K + K + A') → G) (g : G)

/-- The step of the base party `p` of the group `g`: it chooses what `p` writes (`R`) and reads
(`C`), at most `T` letters for every party on every tape, with the weight of `p`
(`Cut.partyWeight`) under the conditions `InitialFits`, and writes the copies at `p` of the
initial units of the group (`initialContents`). It reads no cell. -/
@[expose] noncomputable def baseWriteStep (p : Fin (K + K)) :
    WriteStep F (Cell M U0 U1) (UnitContent ub) where
  Choice := (Option S → Fin (K + K) → List Γ) × (Option S → Fin (K + K) → List Γ)
  choices := (Fintype.piFinset fun _ => Fintype.piFinset fun _ => List.wordsLe Γ T) ×ˢ
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => List.wordsLe Γ T
  written := baseCells n o grp g p
  weight RC _ := if InitialFits ub U0 cb (fun s => ρ s p) (fun a b => n a b) p RC.1 RC.2 then
    partyWeight mu T q x p RC.1 RC.2 else 0
  contents RC _ c := initialContents cb RC.1 RC.2 p c.unit
  read := ∅

/-- The step of the role `r` of the group `g`: it chooses an index and the strings on the
channels of the role for each of the `count * ub` bits of the move, with the product of the
entries of the table of the role at the bits given at its slots, provided that these units are
present and that the strings on the channels have as many units as the outcome says; and it
writes the copies at the party of the role of the new units of the move (`roleContents`). It reads
the copies at its party of the units given at its slots. -/
@[expose] noncomputable def roleWriteStep (r : M.Role) :
    WriteStep F (Cell M U0 U1) (UnitContent ub) where
  Choice := Σ i : Fin (P.count n o r.1 * ub) → (M.law r.1).Index,
    ∀ j (ν : (M.law r.1).ChannelAt r.2), BitString ((M.law r.1).length (i j) ν)
  choices := univ
  written := roleCells n o grp g r
  weight ig y := if (∀ e : (M.law r.1).SlotAt r.2, ∀ u ∈ P.ids n o ⟨r.1, e.1⟩,
      y ⟨M.roleParty r, u⟩ ≠ none) ∧ ∀ ν : (M.law r.1).ChannelAt r.2,
      unitCount ub (sideString (M.law r.1).label (fun i => (M.law r.1).length i ν) ig.1
        fun j => ig.2 j ν) = o ⟨r.1, ν.1⟩ + 1 then
    ∏ j, (M.law r.1).table r.2 (ig.1 j) (fun e => (slotBits (P.count n o r.1)
      (P.ids n o ⟨r.1, e.1⟩) fun u => y ⟨M.roleParty r, u⟩).getD j false) (ig.2 j) else 0
  contents ig _ c := roleContents r ig c.unit
  read := univ.filter fun c => c.party = M.roleParty r ∧
    ∃ e : (M.law r.1).SlotAt r.2, c.unit ∈ P.given n o ⟨r.1, e.1⟩

/-- The steps of the group `g`: its base parties, then its roles in the order of the moves. -/
@[expose] noncomputable def groupSteps (ub : ℕ) :
    List (WriteStep F (Cell M U0 U1) (UnitContent ub)) :=
  (baseParties grp g).map (baseWriteStep mu T cb q x ρ n o grp g) ++
    (groupRoles grp g M).map (roleWriteStep P n o grp g)

end Steps

section Facts

variable {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → BitString c}
  {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.Channel → Fin U1} {grp : Fin (K + K + A') → G} {g : G}

/-- The party of a role holds a new unit of its move exactly at the channels of the role. -/
private theorem holds_new_iff {r : M.Role} {ν : (M.law r.1).Channel} {k : Fin U1} :
    Play.Holds (UnitId.holder M.channelParty) (M.roleParty r)
        (.new ⟨r.1, ν⟩ k : UnitId (K + K) U0 M.Channel U1) ↔
      Play.Holds (M.law r.1).channelEnd r.2 ν := by
  simp only [Play.Holds, UnitId.holder, Moves.channelParty, Moves.channelRole, Moves.roleParty,
    (M.party_injective _).eq_iff]

/-- A unit given at a slot of a move is not a new unit of this move or of a later one. -/
private theorem notMem_newUnits {cap : ℕ} (hP : P.Ok cap) {z : M.Slot}
    {u : UnitId (K + K) U0 M.Channel U1} (hu : u ∈ P.given n o z) {x' : Fin E} (hx : z.1 ≤ x') :
    u ∉ newUnits M x' o := by
  have h := (Plan.mem_cur.1 (hP.given_subset n o z hu)).1
  rcases u with ⟨⟩ | ⟨ν, k⟩
  · exact init_notMem_newUnits
  · exact fun hnew => ((new_mem_newUnits.1 hnew).1 ▸ (Plan.new_mem_seenAt.1 h).1).not_ge hx

/-- Every cell of the group is written by exactly the steps of the group. -/
private theorem writtenCells_groupSteps :
    WriteStep.writtenCells (groupSteps mu T cb P q x ρ n o grp g ub) = groupCells n o grp g := by
  ext ⟨a, u⟩
  simp only [WriteStep.mem_writtenCells, groupSteps, List.mem_append, List.mem_map]
  refine ⟨fun ⟨s, hs, hc⟩ => ?_, fun hc => ?_⟩
  · rcases hs with ⟨p, -, rfl⟩ | ⟨r, -, rfl⟩ <;> exact (mem_filter.1 hc).1
  obtain ⟨h1, h2, d, h3⟩ := mem_groupCells.1 hc
  dsimp only at h1 h2 h3
  rcases u with ⟨a', b', k⟩ | ⟨ν, k⟩
  · obtain ⟨p, rfl⟩ : ∃ p, a = Fin.castAdd A' p := ⟨bif d then b' else a', h3.symm⟩
    exact ⟨_, .inl ⟨p, mem_baseParties.2 h1, rfl⟩,
      mem_filter.2 ⟨hc, rfl, init_mem_initialUnits.2 (Plan.init_mem_seenAt.1 h2)⟩⟩
  · subst h3
    exact ⟨_, .inr ⟨M.channelRole ν d, mem_groupRoles.2 h1, rfl⟩,
      mem_filter.2 ⟨hc, rfl, new_mem_newUnits.2 ⟨rfl, (Plan.new_mem_seenAt.1 h2).2⟩⟩⟩

/-- **The steps of a group are sequential.** -/
private theorem sequential_groupSteps {cap : ℕ} (hP : P.Ok cap) :
    WriteStep.Sequential (groupSteps mu T cb P q x ρ n o grp g ub) := by
  have hread (r r' : M.Role) (h : r.1 ≤ r'.1) :
      Disjoint (roleWriteStep (ub := ub) P n o grp g r).read
        (roleWriteStep (ub := ub) P n o grp g r').written := by
    refine disjoint_left.2 fun c hc hc' => ?_
    obtain ⟨-, -, e, he⟩ := mem_filter.1 hc
    exact notMem_newUnits hP he h (mem_filter.1 hc').2.2
  refine WriteStep.Sequential.of_pairwise (List.pairwise_append.2 ⟨?_, ?_, ?_⟩) ?_
  · refine List.pairwise_map.2 ((nodup_baseParties grp g).imp fun hpp' =>
      ⟨disjoint_left.2 fun c hc hc' => hpp' ?_, disjoint_empty_left _⟩)
    exact Fin.castAdd_injective _ _ ((mem_filter.1 hc).2.1.symm.trans (mem_filter.1 hc').2.1)
  · refine List.pairwise_map.2 ((pairwise_groupRoles grp g M).imp fun {r r'} h =>
      ⟨disjoint_left.2 fun ⟨a, u⟩ hc hc' => h.1 ?_, hread _ _ h.2⟩)
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hc
    obtain ⟨-, h1', h2'⟩ := mem_filter.1 hc'
    obtain ⟨ν, k, rfl, -⟩ := mem_newUnits.1 h2
    rcases r, r' with ⟨⟨x, p⟩, ⟨x', p'⟩⟩
    obtain rfl : x = x' := (new_mem_newUnits.1 h2').1
    exact congrArg (Sigma.mk x) (M.party_injective x (h1.symm.trans h1'))
  · refine List.forall_mem_map.2 fun p _ => List.forall_mem_map.2 fun r _ =>
      ⟨disjoint_left.2 fun ⟨a, u⟩ hc hc' => ?_, disjoint_empty_left _⟩
    cases u
    · exact absurd (mem_filter.1 hc').2.2 init_notMem_newUnits
    · exact absurd (mem_filter.1 hc).2.2 new_notMem_initialUnits
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs <;> obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
    · exact ⟨disjoint_empty_left _, fun _ _ _ _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
    refine ⟨hread r r le_rfl, fun ω _ y y' hy => ⟨?_, fun _ _ => rfl⟩⟩
    have h (e : (M.law r.1).SlotAt r.2) : ∀ u ∈ P.ids n o ⟨r.1, e.1⟩,
        y ⟨M.roleParty r, u⟩ = y' ⟨M.roleParty r, u⟩ := fun u hu =>
      hy _ (mem_filter.2 ⟨mem_univ _, rfl, e, Plan.mem_ids.1 hu⟩)
    have hs (e : (M.law r.1).SlotAt r.2) : slotBits (P.count n o r.1) (P.ids n o ⟨r.1, e.1⟩)
        (fun u => y ⟨M.roleParty r, u⟩) = slotBits (P.count n o r.1) (P.ids n o ⟨r.1, e.1⟩)
        (fun u => y' ⟨M.roleParty r, u⟩) :=
      congrArg (· ++ _) (List.flatMap_congr fun u hu => congrArg _ (h e u hu))
    simp only [roleWriteStep, hs]
    exact if_congr (and_congr_left' (forall_congr' fun e => forall₂_congr fun u hu => by
      rw [h e u hu])) rfl rfl

/-- The cells that a base party of the group writes are its copies of the initial units of the
strings from and to it. -/
theorem mem_baseCells {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g)
    {c : Cell M U0 U1} : c ∈ baseCells n o grp g p ↔
      ∃ (a b : Fin (K + K)) (k : Fin U0), (k : ℕ) < n a b ∧ (a = p ∨ b = p) ∧
        c = ⟨Fin.castAdd A' p, .init a b k⟩ := by
  simp only [baseCells, mem_filter, mem_groupCells]
  refine ⟨fun ⟨⟨_, _, hh⟩, hpc, hu⟩ => ?_, ?_⟩
  · obtain ⟨a, ⟨a', b', k⟩ | ⟨ν, k⟩⟩ := c
    · dsimp only at hpc hh hu
      subst hpc
      exact ⟨a', b', k, init_mem_initialUnits.1 hu, by simpa [UnitId.holds_init, eq_comm] using hh,
        rfl⟩
    · exact absurd hu new_notMem_initialUnits
  · rintro ⟨a, b, k, hk, hab, rfl⟩
    exact ⟨⟨hp, Plan.init_mem_seenAt.2 hk, UnitId.holds_init.2 (by rcases hab with rfl | rfl <;>
      simp)⟩, rfl, init_mem_initialUnits.2 hk⟩

/-- The cells that a role of the group writes are the copies at its party of the new units of
its channels. -/
theorem mem_roleCells {r : M.Role} (hr : grp (M.roleParty r) = g) {c : Cell M U0 U1} :
    c ∈ roleCells n o grp g r ↔ ∃ (ν : (M.law r.1).ChannelAt r.2) (k : Fin U1),
      k ≤ o ⟨r.1, ν.1⟩ ∧ c = ⟨M.roleParty r, .new ⟨r.1, ν.1⟩ k⟩ := by
  simp only [roleCells, mem_filter, mem_groupCells]
  refine ⟨fun ⟨⟨_, _, hh⟩, hpc, hu⟩ => ?_, ?_⟩
  · obtain ⟨ν, k, hu', hk⟩ := mem_newUnits.1 hu
    obtain ⟨a, u⟩ := c
    dsimp only at hpc hu' hh
    subst hpc hu'
    exact ⟨⟨ν, holds_new_iff.1 hh⟩, k, hk, rfl⟩
  · rintro ⟨ν, k, hk, rfl⟩
    exact ⟨⟨hr, Plan.new_mem_seenAt.2 ⟨r.1.2, hk⟩, holds_new_iff.2 ν.2⟩, rfl,
      new_mem_newUnits.2 ⟨rfl, hk⟩⟩

private theorem ite_ite_zero {P Q R : Prop} {_ : Decidable P} {_ : Decidable Q} {_ : Decidable R}
    {a : F} (h : P ∧ Q ↔ R) : (if P then (if Q then a else 0) else 0) = if R then a else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp_all

/-- The factor of a base party is its table at the beginning, at its copies of the units. -/
private theorem factor_baseWriteStep {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g)
    {y : Cell M U0 U1 → UnitContent ub} (hy : ∀ c ∉ groupCells n o grp g, y c = none) :
    (baseWriteStep mu T cb q x ρ n o grp g p).factor y = initialTable mu T cb q x
      (fun s => ρ s p) (fun a b => n a b) p fun u => y ⟨Fin.castAdd A' p, u⟩ := by
  simp only [WriteStep.factor, baseWriteStep]
  rw [initialTable, ← sum_product']
  refine sum_congr rfl fun RC _ => ite_ite_zero ⟨fun ⟨hw, h1, h2, h3, h4⟩ => ?_,
    fun ⟨h1, h2, h3⟩ => ⟨fun c hc => ?_, h1, fun b => (h2 b).1, fun b => (h3 b).1,
      fun k => ((h2 p).2 k).symm.trans ((h3 p).2 k)⟩⟩
  · have key (a b : Fin (K + K)) (k : Fin U0) (hab : a = p ∨ b = p) :
        y ⟨Fin.castAdd A' p, .init a b k⟩ = unitsOf ub
          (segmentString cb fun s => if a = p then RC.1 s b else RC.2 s a) k := by
      by_cases hk : (k : ℕ) < n a b
      · exact hw _ ((mem_baseCells hp).2 ⟨a, b, k, hk, hab, rfl⟩)
      · rw [hy _ fun hc => hk (Plan.init_mem_seenAt.1 (mem_groupCells.1 hc).2.1), eq_comm,
          unitsOf_eq_none]
        rcases hab with rfl | rfl <;> split_ifs <;> simp_all
    refine ⟨h1, fun b => ⟨h2 b, fun k => by simpa using key p b k (.inl rfl)⟩,
      fun b => ⟨h3 b, fun k => (key b p k (.inr rfl)).trans ?_⟩⟩
    by_cases h : b = p <;> simp [h, h4 k]
  · obtain ⟨a, b, k, -, rfl | rfl, rfl⟩ := (mem_baseCells hp).1 hc
    · simp [initialContents, (h2 b).2 k]
    · by_cases hap : a = b <;> simp [initialContents, hap, (h2 b).2 k, (h3 a).2 k]

/-- The factor of a role is its table, at the copies of the units at its party. -/
private theorem factor_roleWriteStep {r : M.Role} (hr : grp (M.roleParty r) = g)
    {y : Cell M U0 U1 → UnitContent ub} (hy : ∀ c ∉ groupCells n o grp g, y c = none) :
    (roleWriteStep P n o grp g r).factor y =
      roleTableAt P n o r fun u => y ⟨M.roleParty r, u⟩ := by
  simp only [WriteStep.factor, roleWriteStep, roleTableAt, Cut.roleTable]
  split_ifs with hpres
  swap
  · exact sum_eq_zero fun ig _ => by simp only [eq_false hpres, false_and, ite_false, ite_self]
  rw [← univ_sigma_univ, sum_sigma]
  refine sum_congr rfl fun i _ => sum_congr rfl fun ig _ => ?_
  simp only [eq_true hpres, true_and]
  refine ite_ite_zero ⟨fun ⟨h, hc⟩ ν => ⟨hc ν, fun k => ?_⟩, fun h => ⟨fun c hc => ?_,
    fun ν => (h ν).1⟩⟩
  · change y ⟨M.roleParty r, .new ⟨r.1, ν.1⟩ k⟩ = _
    by_cases hk : k ≤ o ⟨r.1, ν.1⟩
    · rw [h _ ((mem_roleCells hr).2 ⟨ν, k, hk, rfl⟩), roleContents_new]
    · rw [hy _ fun hc => hk (Plan.new_mem_seenAt.1 (mem_groupCells.1 hc).2.1).2, eq_comm,
        unitsOf_eq_none, hc ν]
      exact Nat.succ_le_of_lt (not_le.1 hk)
  · obtain ⟨ν, k, -, rfl⟩ := (mem_roleCells hr).1 hc
    exact ((h ν).2 k).trans (roleContents_new r ⟨i, ig⟩ ν k).symm

/-- The product of the factors of the steps is the product of the tables of the parties of the
group after the moves. -/
private theorem prod_factor {y : Cell M U0 U1 → UnitContent ub}
    (hy : ∀ c ∉ groupCells n o grp g, y c = none) :
    ((groupSteps mu T cb P q x ρ n o grp g ub).map fun s => s.factor y).prod =
      ∏ a with grp a = g, finalTable P mu T cb q x ρ n o a fun u => y ⟨a, u⟩ := by
  simp only [groupSteps, List.map_append, List.map_map, List.prod_append, finalTable, partyTable,
    prod_mul_distrib]
  congr 1
  · rw [← List.prod_toFinset _ (nodup_baseParties grp g), prod_filter, Fin.prod_univ_add]
    simp only [initialTables, Fin.addCases_left, Fin.addCases_right, ite_self, prod_const_one,
      mul_one, ← prod_filter]
    exact prod_congr (by ext; simp [mem_baseParties]) fun p hp =>
      factor_baseWriteStep (by simpa using hp) hy
  · rw [← List.prod_toFinset _ (nodup_groupRoles grp g M), prod_comm]
    simp only [prod_ite_eq, mem_filter, mem_univ, true_and, ← prod_filter]
    exact prod_congr (by ext; simp [mem_groupRoles]) fun r hr =>
      factor_roleWriteStep (by simpa using hr) hy

/-- **The value of a group is the sum over the executions of its steps**, from empty contents, of
the condition that the copies of the current units agree within the group and are the contents
`b` of the units shared with other groups. -/
theorem groupValue_eq_exec {cap : ℕ} (hP : P.Ok cap)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    P.groupValue mu T cb q x ρ n o grp g b =
      WriteStep.exec (groupSteps mu T cb P q x ρ n o grp g ub)
      (fun y => if Play.GroupAgree (UnitId.holder M.channelParty) grp g (P.cur n o E) b
        (fun a u => y ⟨a, u⟩) then 1 else 0) fun _ => none := by
  rw [← WriteStep.sum_prod_factor_mul_eq_exec (sequential_groupSteps hP),
    writtenCells_groupSteps, Plan.groupValue, Play.groupValue_eq_sum_filter, sum_filter]
  refine sum_equiv ⟨fun z c => z c.party c.unit, fun y a u => y ⟨a, u⟩, fun _ => rfl, fun _ => rfl⟩
    (fun z => ?_) fun z hz => ?_
  · simp only [Play.mem_groupContents, mem_filter, mem_univ, true_and, mem_groupCells]
    exact ⟨fun h c => h c.party c.unit, fun h a u => h ⟨a, u⟩⟩
  · rw [Equiv.coe_fn_mk, prod_factor fun c hc => (Play.mem_groupContents.1 hz) c.party c.unit
      (by simpa using hc), mul_ite, mul_one, mul_zero]

end Facts

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
