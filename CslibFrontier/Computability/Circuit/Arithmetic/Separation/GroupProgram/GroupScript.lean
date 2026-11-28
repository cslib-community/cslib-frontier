/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Moves
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Rows
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Bases

/-!
# The script of a group

The evaluator of [AnthropicVPVNP2026] computes the value of a group of parties after the moves of
a plan (`Cut.Plan.groupValue`) by the program GROUP, at a script (`groupScript`) that lists, in
order:

* for every base party of the group (`baseParties`), the instruction of its block or of its input
  part (`baseInstructions`), whose body (`baseBody`) says how the letters of its tapes are cut for
  the partners (`rowFlag`) and at which keys the units of the strings that it writes and reads
  are put, followed by the comparisons of the two copies of the units from the party to itself;
* for every role of the group, in the order of the moves (`groupRoles`), its instruction
  (`roleInstruction`);
* the comparisons of the copies of the current units that the group holds with each other and
  with the contents of the units shared with other groups (`endInstructions`).

A copy of a unit at a party is a cell (`Cell`); the script puts the cell `c` at the key `key c`
of the trie of GROUP, and the second copy of unit `k` from the base party `p` to itself at the key
`dkey (p, k)`.

## Main definitions

* `Cell`, `Cell.equivProd`: the copy of a unit at a party, and cells as pairs.
* `baseParties`, `allRoles`, `groupRoles`: the base parties of a group, all roles of the moves,
  and the roles of a group.
* `indicesBelow`, `rowFlag`, `baseBody`: the keys of the first units of a string, the flags of the
  partners in a row, and the body of a base party.
* `baseInstructions`, `roleInstruction`, `endInstructions`, `groupScript`: the instructions of a
  base party, of a role and of the end, and the script of a group.

## Main results

* `mem_baseParties`, `nodup_baseParties`, `mem_allRoles`, `pairwise_allRoles`,
  `mem_groupRoles`, `pairwise_groupRoles`, `nodup_groupRoles`: the base parties and the roles.
* `length_indicesBelow`, `getElem_indicesBelow`, `mem_indicesBelow`, `nodup_indicesBelow`: the
  keys of the first units.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source module
`Nc.Grp.Script` (its script half) and `Nc.Grp.GrpSteps`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset

section Lists

variable {F : Type*} [CommSemiring F] {A A' E K U0 U1 : ℕ} {G : Type*} [DecidableEq G]

/-- A cell: the copy of a unit at a party. -/
structure Cell (M : Moves F (K + K + A') E) (U0 U1 : ℕ) where
  /-- The party that holds the copy. -/
  party : Fin (K + K + A')
  /-- The unit. -/
  unit : UnitId (K + K) U0 M.Channel U1

/-- A cell as the pair of its party and its unit. -/
@[expose] def Cell.equivProd (M : Moves F (K + K + A') E) (U0 U1 : ℕ) :
    Cell M U0 U1 ≃ Fin (K + K + A') × UnitId (K + K) U0 M.Channel U1 where
  toFun c := (c.party, c.unit)
  invFun z := ⟨z.1, z.2⟩

instance (M : Moves F (K + K + A') E) (U0 U1 : ℕ) : DecidableEq (Cell M U0 U1) :=
  (Cell.equivProd M U0 U1).decidableEq

instance (M : Moves F (K + K + A') E) (U0 U1 : ℕ) : Fintype (Cell M U0 U1) :=
  Fintype.ofEquiv _ (Cell.equivProd M U0 U1).symm

/-- The base parties of the group `g`, in their order. -/
def baseParties (grp : Fin (K + K + A') → G) (g : G) : List (Fin (K + K)) :=
  (List.finRange (K + K)).filter fun p => grp (Fin.castAdd A' p) = g

theorem mem_baseParties {grp : Fin (K + K + A') → G} {g : G} {p : Fin (K + K)} :
    p ∈ baseParties grp g ↔ grp (Fin.castAdd A' p) = g := by
  simp [baseParties]

theorem nodup_baseParties (grp : Fin (K + K + A') → G) (g : G) : (baseParties grp g).Nodup :=
  (List.nodup_finRange _).filter _

/-- The base parties of the group `g` are the base parties in `g`, in their order. -/
theorem baseParties_eq_filter (grp : Fin (K + K + A') → G) (g : G) :
    baseParties grp g = (List.finRange (K + K)).filter fun p => grp (Fin.castAdd A' p) = g := by
  unfold baseParties
  rfl

/-- All roles of all moves, in the order of the moves. -/
@[expose] noncomputable def allRoles (M : Moves F A E) : List M.Role :=
  (List.finRange E).flatMap fun x => (univ : Finset (M.law x).Role).toList.map (Sigma.mk x)

theorem mem_allRoles (M : Moves F A E) (r : M.Role) : r ∈ allRoles M := by
  simpa [allRoles] using ⟨r.1, r.2, rfl⟩

/-- The roles of all moves are distinct, and listed in the order of the moves. -/
theorem pairwise_allRoles (M : Moves F A E) :
    (allRoles M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 := by
  refine List.pairwise_flatMap.2 ⟨fun x _ => List.pairwise_map.2 ((nodup_toList _).imp
    fun h => ⟨fun e => h (eq_of_heq (Sigma.mk.inj e).2), le_rfl⟩), ?_⟩
  refine (List.pairwise_lt_finRange E).imp fun hx r hr r' hr' => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨p', -, rfl⟩ := List.mem_map.1 hr'
  exact ⟨fun e => hx.ne (Sigma.mk.inj e).1, hx.le⟩

/-- The roles of the group `g`, in the order of the moves. -/
noncomputable def groupRoles (grp : Fin A → G) (g : G) (M : Moves F A E) : List M.Role :=
  (allRoles M).filter fun r => grp (M.roleParty r) = g

/-- The roles of the group `g` are the roles whose party is in `g`, in the order of
`allRoles`. -/
theorem groupRoles_eq_filter (grp : Fin A → G) (g : G) (M : Moves F A E) :
    groupRoles grp g M = (allRoles M).filter fun r => grp (M.roleParty r) = g := by
  unfold groupRoles
  rfl

theorem mem_groupRoles {grp : Fin A → G} {g : G} {M : Moves F A E} {r : M.Role} :
    r ∈ groupRoles grp g M ↔ grp (M.roleParty r) = g := by
  simp [groupRoles, mem_allRoles]

theorem pairwise_groupRoles (grp : Fin A → G) (g : G) (M : Moves F A E) :
    (groupRoles grp g M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 :=
  (pairwise_allRoles M).filter _

theorem nodup_groupRoles (grp : Fin A → G) (g : G) (M : Moves F A E) :
    (groupRoles grp g M).Nodup :=
  (pairwise_groupRoles grp g M).imp And.left

end Lists

/-- The indices below `m`, for `m ≤ U`, in increasing order: the numbers of the first `m` units of
a string. -/
@[expose] def indicesBelow {U : ℕ} (m : Fin (U + 1)) : List (Fin U) :=
  List.ofFn (Fin.castLE (Nat.lt_succ_iff.1 m.isLt))

section Indices

variable {U : ℕ} (m : Fin (U + 1))

@[simp] theorem length_indicesBelow : (indicesBelow m).length = m := List.length_ofFn

@[simp] theorem getElem_indicesBelow (i : ℕ) (h : i < (indicesBelow m).length) :
    ((indicesBelow m)[i] : ℕ) = i := by
  simp [indicesBelow]

@[simp] theorem mem_indicesBelow {k : Fin U} : k ∈ indicesBelow m ↔ (k : ℕ) < m := by
  simp only [indicesBelow, List.mem_ofFn, Fin.ext_iff, Fin.val_castLE]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun h => ⟨⟨k, h⟩, rfl⟩⟩

theorem nodup_indicesBelow : (indicesBelow m).Nodup :=
  List.nodup_ofFn.2 (Fin.castLE_injective _)

end Indices

/-- The flag of the partner `b` in a row with the data `d`: `0` for every partner if the party
writes nothing, and otherwise `1` for the first and the last partner, `2` for a partner strictly
between them, and `0` for the others. -/
@[expose] def rowFlag {A : ℕ} (d : RowData A) (b : Fin A) : ℕ :=
  if d.empty then 0 else if b = d.first ∨ b = d.last then 1 else
    if d.first ≤ b ∧ b ≤ d.last then 2 else 0

section Script

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [Fintype S] [DecidableEq S]
  {A' E K U0 U1 ub c : ℕ} {G : Type} [DecidableEq G] {M : Moves F (K + K + A') E}

/-- The body of the instruction of the base party `p`: for every tape, the flags of the partners
in its row, the last partner first; for every partner `b`, the keys of the copies at `p` of the
first `n p b` units of the string from `p` to `b`, and those of the first `n b p` units of the
string from `b` to `p`, where the units from `p` to itself are read at the keys `dkey`. -/
@[expose] noncomputable def baseBody (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (p : Fin (K + K)) : Body where
  flags := (tapes S).map fun s => (List.ofFn fun b => rowFlag (ρ s p) b).reverse
  writeKeys := List.ofFn fun b => (indicesBelow (n p b)).map fun k =>
    key ⟨Fin.castAdd A' p, .init p b k⟩
  readKeys := List.ofFn fun b => (indicesBelow (n b p)).map fun k =>
    if b = p then dkey (p, k) else key ⟨Fin.castAdd A' p, .init b p k⟩

/-- The instructions of the base party `p`: the block from the state `q κ` to the state
`q (κ + 1)` (numbered by `qn`) for the block `κ`, or the input part `x κ` with the codes `cb` of
the letters, in reverse order, for the input party `κ`; then the comparisons of the two copies of
the units from `p` to itself. -/
@[expose] noncomputable def baseInstructions {Q : Type} (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool)
    (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (p : Fin (K + K)) : List Instruction :=
  Fin.addCases (motive := fun _ => Instruction)
    (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (baseBody ρ n key dkey p))
    (fun κ => .input ((x κ).map (letterCode cb)).reverse (baseBody ρ n key dkey p)) p ::
  (indicesBelow (n p p)).map fun k => .agree (key ⟨Fin.castAdd A' p, .init p p k⟩) (dkey (p, k))

/-- The instruction of the role `r`, number `tg r` in a list of roles of laws: for every slot,
the keys of the units given, in reverse order, and for every channel the keys of its new units at
the party of the role. -/
@[expose] noncomputable def roleInstruction (P : Plan M U0 U1)
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (key : Cell M U0 U1 → List Bool) (tg : M.Role → ℕ) (r : M.Role) : Instruction :=
  .role (tg r) (P.count n o r.1)
    ((slotList (M.law r.1) r.2).map fun e =>
      ((P.ids n o ⟨r.1, e.val⟩).map fun u => key ⟨M.roleParty r, u⟩).reverse)
    ((channelList (M.law r.1) r.2).map fun ν =>
      (indicesBelow (o ⟨r.1, ν.val⟩).succ).map fun k => key ⟨M.roleParty r, .new ⟨r.1, ν.val⟩ k⟩)

/-- The instructions of the end, for every current unit in the end that the group `g` holds: the
copies at its two holders agree if both are in the group, and the copy at the holder in the group
has the bits of the unit `b` if only one is. -/
@[expose] noncomputable def endInstructions (P : Plan M U0 U1)
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) (key : Cell M U0 U1 → List Bool)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) : List Instruction :=
  ((UnitId.list (K + K) U0 M.Channel U1).filter (· ∈ P.cur n o E)).filterMap fun u =>
    if grp (UnitId.holder M.channelParty u false) = g then
      some (if grp (UnitId.holder M.channelParty u true) = g then
        .agree (key ⟨UnitId.holder M.channelParty u false, u⟩)
          (key ⟨UnitId.holder M.channelParty u true, u⟩)
      else .fixed (key ⟨UnitId.holder M.channelParty u false, u⟩) (b u).bits)
    else if grp (UnitId.holder M.channelParty u true) = g then
      some (.fixed (key ⟨UnitId.holder M.channelParty u true, u⟩) (b u).bits)
    else none

/-- **The script of a group**: the instructions of its base parties, of its roles and of the
end. -/
@[expose] noncomputable def groupScript {Q : Type} (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool)
    (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.Role → ℕ)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) : List Instruction :=
  (baseParties grp g).flatMap (baseInstructions qn cb q x ρ n key dkey) ++
    (groupRoles grp g M).map (roleInstruction P n o key tg) ++ endInstructions P n o grp g key b

end Script

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
