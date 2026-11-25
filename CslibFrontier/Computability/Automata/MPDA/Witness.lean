/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.EmptinessComplete
public import CslibFrontier.Computability.Automata.MPDA.WellNestedWitness
import CslibFrontier.Foundations.Data.List.Forall2

/-! # Generating a witness run

When the search of Algorithm 1 of [AkshayGastinKrishnaRoychowdhury2020] answers `false`, the
function `MPDA.witness` computes an accepting `K`-hole-bounded run (Section 4, Algorithms 5 and 6
of Appendix C).

The run is built backwards from an accepting list, as in Algorithm 6. Each open hole carries a
realization: its atomic hole segments, newest first. These play the role of the source's witness
stacks. A step back over a pop (`AddPop`) adds the popped atomic segment to the realization of the
hole it shrinks or closes, and appends the pop and a well-nested run (`MPDA.wrWitness`). A step
back over a new hole (`AddHole`) appends the block of the hole's realization, each atomic segment a
push followed by a well-nested run (`MPDA.blockWitness`). Each step reuses a step of the soundness
proof (`MPDA.RunsTo`).

To keep the backward search finite, predecessors are taken from the lists the search reaches in
one round fewer (`MPDA.reachUpTo`), computed once until they stabilize (`MPDA.stableLayers`).

The search enumerates letters, stack symbols and control states, so these types are `FinEnum`.

## Main definitions

- `MPDA.witness`: a run for a `K`-hole-bounded accepting run, if the search finds one.

## Main results

- `MPDA.witness_spec`: a returned run is accepting and `K`-hole-bounded.
- `MPDA.isSome_witness_iff`: a run is returned exactly when the search answers `false`.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Symbol Γ : Type*} [FinEnum State] [FinEnum Symbol] [FinEnum Γ]

/-! ## Blocks of realizations -/

section Block

variable (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- A run of the atomic hole segment `(s, γ, t)` of stack `i`: a push of `γ`, then a well-nested
run. -/
@[expose] def atomicWitness (i : Fin n) (s : State) (γ : Γ) (t : State) :
    Option (List (Symbol × Op n Γ)) :=
  (FinEnum.toList (Symbol × State)).findSome? fun (a, s₁) =>
    if M.Tr s (a, .push i γ) s₁ then (M.wrWitness s₁ t).map ((a, .push i γ) :: ·) else none

/-- The state where a realization from `s`, newest segment first, ends. -/
@[expose] def realizationEnd (s : State) : List (Γ × State) → State
  | [] => s
  | (_, t) :: _ => t

/-- The run of a realization from `s`: its atomic segments, oldest first. -/
@[expose] def blockWitness (i : Fin n) (s : State) :
    List (Γ × State) → Option (List (Symbol × Op n Γ))
  | [] => some []
  | (γ, t) :: r => (blockWitness i s r).bind fun v =>
      (M.atomicWitness i (realizationEnd s r) γ t).map (v ++ ·)

variable {M}

theorem Realizes.realizationEnd {i : Fin n} {s t : State} {r : List (Γ × State)}
    (h : M.Realizes i s t r) : MPDA.realizationEnd s r = t := by
  cases h <;> rfl

theorem atomicWitness_spec {i : Fin n} {s t : State} {γ : Γ} {u : List (Symbol × Op n Γ)}
    (h : M.atomicWitness i s γ t = some u) :
    ∃ (a : Symbol) (s₁ : State) (ws : List (Symbol × Op n Γ)), u = (a, .push i γ) :: ws ∧
      M.Tr s (a, .push i γ) s₁ ∧ WellNested ws ∧ M.MTr s₁ ws t := by
  obtain ⟨⟨a, s₁⟩, -, h⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at h
  split_ifs at h with hT
  obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hwn, hrun⟩ := wnWitness_spec hws
  exact ⟨a, s₁, ws, rfl, hT, hwn, hrun⟩

theorem isSome_atomicWitness {i : Fin n} {s t : State} {γ : Γ}
    (h : ⟨s, γ, t⟩ ∈ M.atomicHoles i) : (M.atomicWitness i s γ t).isSome := by
  obtain ⟨a, s₁, hT, hwn⟩ := (mem_atomicHoles M).mp h
  refine List.findSome?_isSome_iff.mpr ⟨(a, s₁), FinEnum.mem_toList _, ?_⟩
  simpa only [hT, ↓reduceIte, Option.isSome_map] using
    isSome_wrWitness ((mem_wellNestedPairs M).mpr hwn)

/-- The run of a realization is a block run of it. -/
theorem blockWitness_spec {i : Fin n} {s t : State} {r : List (Γ × State)}
    (hr : M.Realizes i s t r) :
    ∀ {v : List (Symbol × Op n Γ)}, M.blockWitness i s r = some v → M.BlockRun i s t r v := by
  induction hr with
  | nil =>
    rintro _ ⟨⟩
    exact blockRun_nil
  | cons hr' _ ih =>
    intro v h
    obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hr'.realizationEnd] at hu
    obtain ⟨a, s₁, ws, rfl, hT, hws, hwsrun⟩ := atomicWitness_spec hu
    exact (ih hv').snoc hT hws hwsrun

theorem isSome_blockWitness {i : Fin n} {s t : State} {r : List (Γ × State)}
    (hr : M.Realizes i s t r) : (M.blockWitness i s r).isSome := by
  induction hr with
  | nil => rfl
  | cons hr' hγ ih =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ih
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (isSome_atomicWitness hγ)
    simp [blockWitness, hv, hr'.realizationEnd, hu]

end Block

/-! ## Rounds of the search -/

section Rounds

variable (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- The lists reached in at most `k` steps of the search. -/
@[expose] def reachUpTo (K : ℕ) : ℕ → Finset (HoleList n State)
  | 0 => M.initialLists
  | k + 1 => reachUpTo K k ∪ (reachUpTo K k).biUnion (M.successors K)

/-- The rounds `reachUpTo K (k - 1), …, reachUpTo K 0`, newest first. -/
@[expose] def layers (K : ℕ) : ℕ → List (Finset (HoleList n State))
  | 0 => []
  | k + 1 => M.reachUpTo K k :: layers K k

/-- The rounds of the search, computed until they stabilize or the fuel runs out. -/
@[expose] def stableLayers (K : ℕ) :
    ℕ → List (Finset (HoleList n State)) → List (Finset (HoleList n State))
  | 0, Ls => Ls
  | _ + 1, [] => []
  | f + 1, R :: Ls =>
    let R' := R ∪ R.biUnion (M.successors K)
    if R' = R then R :: Ls else stableLayers K f (R' :: R :: Ls)

variable {M}

theorem reachUpTo_mono {K : ℕ} {k k' : ℕ} (h : k ≤ k') : M.reachUpTo K k ⊆ M.reachUpTo K k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem reachUpTo_stable {K k : ℕ} (h : M.reachUpTo K (k + 1) = M.reachUpTo K k) :
    ∀ j, M.reachUpTo K (k + j) = M.reachUpTo K k
  | 0 => rfl
  | j + 1 => (congrArg (fun R => R ∪ R.biUnion (M.successors K)) (reachUpTo_stable h j)).trans h

/-- The worklist loop only adds lists reached in as many more steps as it has fuel. -/
theorem explore_subset_reachUpTo {K : ℕ} :
    ∀ (f D : ℕ) (visited todo : Finset (HoleList n State)),
      visited ⊆ M.reachUpTo K D → todo ⊆ visited →
      M.explore K f visited todo ⊆ M.reachUpTo K (D + f)
  | 0, D, visited, _, hv, _ => hv
  | f + 1, D, visited, todo, hv, ht => by
    unfold explore
    split_ifs
    · exact hv.trans (reachUpTo_mono (by omega))
    rw [show D + (f + 1) = D + 1 + f by omega]
    refine explore_subset_reachUpTo f (D + 1) _ _ (Finset.union_subset
      (hv.trans (reachUpTo_mono (by omega))) ?_) Finset.subset_union_right
    intro μ hμ
    obtain ⟨ν, hν, hμ⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hμ).1
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨ν, hv (ht hν), hμ⟩)

/-- The stabilized rounds are the rounds up to some `e`, and contain every list reached within the
fuel. -/
theorem stableLayers_eq {K : ℕ} :
    ∀ (f k : ℕ), ∃ e, k ≤ e ∧ M.stableLayers K f (M.layers K (k + 1)) = M.layers K (e + 1) ∧
      M.reachUpTo K (k + f) ⊆ M.reachUpTo K e
  | 0, k => ⟨k, le_rfl, rfl, le_rfl⟩
  | f + 1, k => by
    simp only [layers, stableLayers]
    split_ifs with hfix
    · refine ⟨k, le_rfl, rfl, ?_⟩
      rw [reachUpTo_stable (k := k) hfix (f + 1)]
    · obtain ⟨e, hke, heq, hsub⟩ := stableLayers_eq f (k + 1)
      refine ⟨e, by omega, ?_, by rw [show k + (f + 1) = k + 1 + f by omega]; exact hsub⟩
      simpa [layers, reachUpTo] using heq

end Rounds

/-! ## The backward search -/

section Backward

variable (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

/-- The lists `rs` realize the hole triples `holes`, one by one. -/
@[expose] def RealizesAll (rs : List (List (Γ × State))) (holes : List (HoleTriple n State)) :
    Prop :=
  List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r) rs holes

/-- A list without holes reached by a well-nested run from an initial state. -/
@[expose] def initWitness (μ : HoleList n State) : Option (List (Symbol × Op n Γ)) :=
  if μ.holes = [] then
    (FinEnum.toList State).findSome? fun s₀ => if s₀ ∈ M.start then M.wrWitness s₀ μ.last else none
  else none

/-- A step back over a new hole: the last hole of `μ` is new, and its realization is the last of
`rs`. -/
@[expose] def holeBack (K : ℕ) (R : Finset (HoleList n State))
    (rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ)))
    (μ : HoleList n State) (rs : List (List (Γ × State))) : Option (List (Symbol × Op n Γ)) :=
  match μ.holes.reverse, rs.reverse with
  | ⟨i, s, t⟩ :: hs, r :: rs' =>
    if (⟨hs.reverse, s⟩ : HoleList n State) ∈ R ∧ t = μ.last ∧ hs.length < K then
      (rec ⟨hs.reverse, s⟩ rs'.reverse).bind fun w => (M.blockWitness i s r).map (w ++ ·)
    else none
  | _, _ => none

/-- A step back over a pop that shrinks the hole at position `j` of `μ`: the parent list has the
larger hole, whose realization adds the popped atomic segment. -/
@[expose] def popBack (R : Finset (HoleList n State))
    (rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ)))
    (μ : HoleList n State) (rs : List (List (Γ × State))) : Option (List (Symbol × Op n Γ)) :=
  (List.range μ.holes.length).findSome? fun j =>
    match (μ.holes[j]? : Option (HoleTriple n State)), rs[j]? with
    | some ⟨i, s₁, s₂⟩, some r =>
      (FinEnum.toList (Γ × State × State × State × Symbol)).findSome? fun (γ, s₃, ℓ, ℓ', b) =>
        if M.Tr ℓ (b, .pop i γ) ℓ' ∧ (∀ h ∈ μ.holes.drop (j + 1), h.stack ≠ i) ∧
            (⟨μ.holes.take j ++ ⟨i, s₁, s₃⟩ :: μ.holes.drop (j + 1), ℓ⟩ : HoleList n State) ∈ R ∧
            ⟨s₂, γ, s₃⟩ ∈ M.atomicHoles i then
          (rec ⟨μ.holes.take j ++ ⟨i, s₁, s₃⟩ :: μ.holes.drop (j + 1), ℓ⟩
            (rs.take j ++ ((γ, s₃) :: r) :: rs.drop (j + 1))).bind fun w =>
              (M.wrWitness ℓ' μ.last).map fun v => w ++ (b, .pop i γ) :: v
        else none
    | _, _ => none

/-- A step back over a pop that closes a hole: the parent list has one more hole, at position
`j`, realized by the popped atomic segment alone. -/
@[expose] def closeBack (R : Finset (HoleList n State))
    (rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ)))
    (μ : HoleList n State) (rs : List (List (Γ × State))) : Option (List (Symbol × Op n Γ)) :=
  (List.range (μ.holes.length + 1)).findSome? fun j =>
    (FinEnum.toList (Fin n × State × Γ × State × State × State × Symbol)).findSome?
      fun (i, s₁, γ, s₃, ℓ, ℓ', b) =>
        if M.Tr ℓ (b, .pop i γ) ℓ' ∧ (∀ h ∈ μ.holes.drop j, h.stack ≠ i) ∧
            (⟨μ.holes.take j ++ ⟨i, s₁, s₃⟩ :: μ.holes.drop j, ℓ⟩ : HoleList n State) ∈ R ∧
            ⟨s₁, γ, s₃⟩ ∈ M.atomicHoles i then
          (rec ⟨μ.holes.take j ++ ⟨i, s₁, s₃⟩ :: μ.holes.drop j, ℓ⟩
            (rs.take j ++ [(γ, s₃)] :: rs.drop j)).bind fun w =>
              (M.wrWitness ℓ' μ.last).map fun v => w ++ (b, .pop i γ) :: v
        else none

/-- The backward search (Algorithm 6) from the list `μ` whose holes are realized by `rs`, with
predecessors taken from the rounds `Rs`, newest first. -/
@[expose] def holeWitness (K : ℕ) :
    List (Finset (HoleList n State)) → HoleList n State → List (List (Γ × State)) →
      Option (List (Symbol × Op n Γ))
  | [], μ, _ => M.initWitness μ
  | R :: Rs, μ, rs =>
    M.initWitness μ <|> (M.holeBack K R (holeWitness K Rs) μ rs <|>
      (M.popBack R (holeWitness K Rs) μ rs <|> M.closeBack R (holeWitness K Rs) μ rs))

end Backward

/-! ## Soundness of the backward search -/

section BackwardSound

variable {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

private theorem take_append_cons_drop {α : Type*} {l : List α} {j : ℕ} {x : α}
    (h : l[j]? = some x) :
    l.take j ++ x :: l.drop (j + 1) = l := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  conv_rhs => rw [← List.take_append_drop j l, List.drop_eq_getElem_cons hj]

theorem initWitness_spec {K : ℕ} {μ : HoleList n State} {w : List (Symbol × Op n Γ)}
    (h : M.initWitness μ = some w) : μ.holes = [] ∧ M.RunsTo K μ [] w := by
  unfold initWitness at h
  split_ifs at h with hh
  obtain ⟨s₀, -, h⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at h with hs₀
  obtain ⟨hwn, hrun⟩ := wnWitness_spec h
  obtain ⟨holes, last⟩ := μ
  cases hh
  exact ⟨rfl, runsTo_init hs₀ hwn hrun⟩

variable (M) in
/-- The hypothesis on the recursive call of a backward step. -/
abbrev RecSound (K : ℕ)
    (rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ))) : Prop :=
  ∀ ν rs w, M.RealizesAll rs ν.holes → rec ν rs = some w → M.RunsTo K ν rs w

omit [DecidablePred (· ∈ M.start)] in
theorem holeBack_spec {K : ℕ} {R : Finset (HoleList n State)}
    {rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ))}
    (hrec : RecSound M K rec) {μ : HoleList n State} {rs : List (List (Γ × State))}
    {w : List (Symbol × Op n Γ)} (hrs : M.RealizesAll rs μ.holes)
    (h : M.holeBack K R rec μ rs = some w) : M.RunsTo K μ rs w := by
  obtain ⟨holes, last⟩ := μ
  unfold holeBack at h
  dsimp only at h hrs
  split at h
  next i s t hs r rs' hh hr =>
    split_ifs at h with hc
    obtain ⟨-, rfl, hK⟩ := hc
    obtain ⟨w', hw', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [List.reverse_eq_cons_iff] at hh hr
    subst hh hr
    have hlen : rs'.reverse.length = hs.reverse.length := by
      have := hrs.length_eq
      simp only [List.length_append, List.length_reverse, List.length_singleton] at this ⊢
      omega
    obtain ⟨hpre, hlast⟩ := List.Forall₂.split_of_length_eq hlen hrs
    cases hlast with
    | cons hreal _ =>
      exact (hrec ⟨hs.reverse, s⟩ _ _ hpre hw').hole (by simpa using hK)
        (blockWitness_spec hreal hv)
  next => simp at h

omit [DecidablePred (· ∈ M.start)] in
theorem popBack_spec {K : ℕ} {R : Finset (HoleList n State)}
    {rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ))}
    (hrec : RecSound M K rec) {μ : HoleList n State} {rs : List (List (Γ × State))}
    {w : List (Symbol × Op n Γ)} (hrs : M.RealizesAll rs μ.holes)
    (h : M.popBack R rec μ rs = some w) : M.RunsTo K μ rs w := by
  obtain ⟨holes, last⟩ := μ
  unfold popBack at h
  dsimp only at h hrs
  obtain ⟨j, -, h⟩ := List.exists_of_findSome?_eq_some h
  split at h
  next i s₁ s₂ r hhj hrj =>
    obtain ⟨⟨γ, s₃, ℓ, ℓ', b⟩, -, h⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at h
    split_ifs at h with hc
    obtain ⟨hb, hpost, -, hγ⟩ := hc
    obtain ⟨w', hw', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hwn, hvrun⟩ := wnWitness_spec hv
    have hlen : (rs.take j).length = (holes.take j).length := by simp [hrs.length_eq]
    rw [← take_append_cons_drop hhj, ← take_append_cons_drop hrj] at hrs ⊢
    obtain ⟨hrpre, hrest⟩ := List.Forall₂.split_of_length_eq hlen hrs
    cases hrest with
    | cons hr hrpost =>
    have hν : M.RealizesAll (rs.take j ++ ((γ, s₃) :: r) :: rs.drop (j + 1))
        (holes.take j ++ ⟨i, s₁, s₃⟩ :: holes.drop (j + 1)) :=
      List.rel_append hrpre (.cons (.cons hr hγ) hrpost)
    exact (hrec _ _ _ hν hw').pop (splitLastHole_eq_some_of hpost _) hlen hb hwn hvrun
  next => simp at h

omit [DecidablePred (· ∈ M.start)] in
theorem closeBack_spec {K : ℕ} {R : Finset (HoleList n State)}
    {rec : HoleList n State → List (List (Γ × State)) → Option (List (Symbol × Op n Γ))}
    (hrec : RecSound M K rec) {μ : HoleList n State} {rs : List (List (Γ × State))}
    {w : List (Symbol × Op n Γ)} (hrs : M.RealizesAll rs μ.holes)
    (h : M.closeBack R rec μ rs = some w) : M.RunsTo K μ rs w := by
  obtain ⟨holes, last⟩ := μ
  unfold closeBack at h
  dsimp only at h hrs
  obtain ⟨j, -, h⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨⟨i, s₁, γ, s₃, ℓ, ℓ', b⟩, -, h⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hb, hpost, -, hγ⟩ := hc
  obtain ⟨w', hw', h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hwn, hvrun⟩ := wnWitness_spec hv
  have hlen : (rs.take j).length = (holes.take j).length := by simp [hrs.length_eq]
  rw [← List.take_append_drop j holes, ← List.take_append_drop j rs] at hrs ⊢
  obtain ⟨hrpre, hrpost⟩ := List.Forall₂.split_of_length_eq hlen hrs
  have hν : M.RealizesAll (rs.take j ++ [(γ, s₃)] :: rs.drop j)
      (holes.take j ++ ⟨i, s₁, s₃⟩ :: holes.drop j) :=
    List.rel_append hrpre (.cons (.cons .nil hγ) hrpost)
  exact (hrec _ _ _ hν hw').popClose (splitLastHole_eq_some_of hpost _) hlen hb hwn hvrun

/-- **Soundness of the backward search**: a found run reaches the list. -/
theorem holeWitness_spec {K : ℕ} :
    ∀ (Rs : List (Finset (HoleList n State))), RecSound M K (M.holeWitness K Rs)
  | [], μ, rs, w, hrs, h => by
    obtain ⟨hh, hw⟩ := initWitness_spec (K := K) h
    exact List.forall₂_nil_right_iff.mp (hh ▸ hrs) ▸ hw
  | R :: Rs, μ, rs, w, hrs, h => by
    simp only [holeWitness, Option.orElse_eq_orElse, Option.orElse_eq_or] at h
    rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
    · obtain ⟨hh, hw⟩ := initWitness_spec (K := K) h
      exact List.forall₂_nil_right_iff.mp (hh ▸ hrs) ▸ hw
    rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
    · exact holeBack_spec (holeWitness_spec Rs) hrs h
    rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
    · exact popBack_spec (holeWitness_spec Rs) hrs h
    · exact closeBack_spec (holeWitness_spec Rs) hrs h

end BackwardSound

/-! ## Completeness of the backward search -/

section BackwardComplete

variable {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)]

private theorem isSome_bind_map {α β γ : Type*} {a : Option α} {b : Option β} (f : α → β → γ)
    (ha : a.isSome) (hb : b.isSome) : (a.bind fun x => b.map (f x)).isSome := by
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp hb
  rfl

theorem isSome_initWitness {μ : HoleList n State} (h : μ ∈ M.initialLists) :
    (M.initWitness μ).isSome := by
  obtain ⟨hh, s₀, hs₀, hwr⟩ := mem_initialLists.mp h
  simp only [initWitness, hh, ↓reduceIte, List.findSome?_isSome_iff]
  exact ⟨s₀, FinEnum.mem_toList _, by simp [hs₀, isSome_wrWitness hwr]⟩

theorem isSome_holeWitness_of_init {K : ℕ} {Rs : List (Finset (HoleList n State))}
    {μ : HoleList n State} {rs : List (List (Γ × State))} (h : μ ∈ M.initialLists) :
    (M.holeWitness K Rs μ rs).isSome := by
  cases Rs with
  | nil => exact isSome_initWitness h
  | cons R Rs =>
    simp only [holeWitness, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.isSome_or,
      isSome_initWitness h, Bool.true_or]

/-- **Completeness of the backward search**: from a list reached in `d` steps, with any
realization of its holes, the search with at least `d` rounds succeeds. -/
theorem isSome_holeWitness {K : ℕ} :
    ∀ (d : ℕ) {μ : HoleList n State}, μ ∈ M.reachUpTo K d → ∀ {e : ℕ}, d ≤ e →
      ∀ {rs : List (List (Γ × State))}, M.RealizesAll rs μ.holes →
        (M.holeWitness K (M.layers K e) μ rs).isSome
  | 0, μ, hμ, e, _, rs, _ => isSome_holeWitness_of_init hμ
  | d + 1, μ, hμ, e, hde, rs, hrs => by
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · exact isSome_holeWitness d hμ (by omega) hrs
    obtain ⟨ν, hνd, hν⟩ := Finset.mem_biUnion.mp hμ
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hνe : ν ∈ M.reachUpTo K e := reachUpTo_mono (by omega) hνd
    have ih : ∀ {rs'}, M.RealizesAll rs' ν.holes → (M.holeWitness K (M.layers K e) ν rs').isSome :=
      fun h => isSome_holeWitness d hνd (by omega) h
    simp only [layers, holeWitness, Option.orElse_eq_orElse, Option.orElse_eq_or,
      Option.isSome_or, Bool.or_eq_true]
    refine .inr ?_
    obtain ⟨holesν, ℓν⟩ := ν
    simp only [successors, Finset.mem_union] at hν
    rcases hν with hν | hν
    · -- A new hole.
      refine .inl ?_
      split_ifs at hν with hK <;> [skip; simp at hν]
      obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      obtain ⟨⟨s, t⟩, hss, rfl⟩ := Finset.mem_image.mp hν
      obtain ⟨-, hs⟩ := Finset.mem_filter.mp hss
      simp only at hs hK
      subst hs
      obtain ⟨rs₀, rs₁, rfl, -, hrs₀, hrs₁⟩ := List.Forall₂.split_right hrs
      cases hrs₁ with
      | cons hr h =>
      cases h
      unfold holeBack
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.reverse_reverse]
      split_ifs with hc
      · exact isSome_bind_map _ (ih hrs₀) (isSome_blockWitness hr)
      · exact absurd (by simp [hνe, hK]) hc
    · obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      unfold addPop at hν
      rcases hsp : splitLastHole i holesν with _ | ⟨pre, ⟨s₁, s₃⟩, post⟩
      · simp [hsp] at hν
      obtain ⟨hνh, hpost⟩ := splitLastHole_eq_some hsp
      subst hνh
      simp only [hsp, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hν
      rcases hν with ⟨⟨s₂, γ, s', s''⟩, ⟨-, hγ, ⟨b, hb⟩, hwr⟩, rfl⟩ |
        ⟨⟨s₂, γ, s', s''⟩, ⟨⟨-, hγ, ⟨b, hb⟩, hwr⟩, rfl⟩, rfl⟩
      · -- The hole shrinks.
        refine .inr (.inl ?_)
        obtain ⟨rpre, r, rpost, rfl, hlen, hrpre, hr, hrpost⟩ :=
          List.Forall₂.split_right_cons hrs
        unfold popBack
        refine List.findSome?_isSome_iff.mpr ⟨pre.length, List.mem_range.mpr (by simp), ?_⟩
        have hh : (pre ++ ⟨i, s₁, s₂⟩ :: post)[pre.length]? = some ⟨i, s₁, s₂⟩ := by simp
        have hr' : (rpre ++ r :: rpost)[pre.length]? = some r := by rw [← hlen]; simp
        simp only [hh, hr']
        refine List.findSome?_isSome_iff.mpr ⟨(γ, s₃, ℓν, s', b), FinEnum.mem_toList _, ?_⟩
        simp only [List.take_left, List.take_left' hlen,
          show (pre ++ ⟨i, s₁, s₂⟩ :: post).drop (pre.length + 1) = post by simp,
          show (rpre ++ r :: rpost).drop (pre.length + 1) = rpost by simp [← hlen]]
        split_ifs with hc
        · exact isSome_bind_map _ (ih (List.rel_append hrpre (.cons (.cons hr hγ) hrpost)))
            (isSome_wrWitness hwr)
        · exact absurd ⟨hb, hpost, hνe, hγ⟩ hc
      · -- The hole closes.
        refine .inr (.inr ?_)
        obtain ⟨rpre, rpost, rfl, hlen, hrpre, hrpost⟩ := List.Forall₂.split_right hrs
        unfold closeBack
        refine List.findSome?_isSome_iff.mpr ⟨pre.length, List.mem_range.mpr (by simp), ?_⟩
        refine List.findSome?_isSome_iff.mpr ⟨(i, s₂, γ, s₃, ℓν, s', b), FinEnum.mem_toList _,
          ?_⟩
        simp only [List.take_left, List.drop_left, List.take_left' hlen, List.drop_left' hlen]
        split_ifs with hc
        · exact isSome_bind_map _ (ih (List.rel_append hrpre (.cons (.cons .nil hγ) hrpost)))
            (isSome_wrWitness hwr)
        · exact absurd ⟨hb, hpost, hνe, hγ⟩ hc

end BackwardComplete

/-! ## The witness -/

section Witness

variable (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]
  [DecidablePred (· ∈ M.start)] [DecidablePred (· ∈ M.accept)]

/-- **Witness generation** (Section 4 of [AkshayGastinKrishnaRoychowdhury2020]): an accepting
`K`-hole-bounded run, if the search of Algorithm 1 finds one. The rounds of the search are
computed until they stabilize; from an accepting list, the run is built backwards
(`MPDA.holeWitness`) and ends with a well-nested run to a final state. -/
@[expose] def witness (K : ℕ) : Option (List (Symbol × Op n Γ)) :=
  let Ls := M.stableLayers K (listBound n State K) [M.initialLists]
  (FinEnum.toList (State × State)).findSome? fun (ℓ, f) =>
    if f ∈ M.accept ∧ (⟨[], ℓ⟩ : HoleList n State) ∈ Ls.headD ∅ then
      (M.wrWitness ℓ f).bind fun v => (M.holeWitness K Ls.tail ⟨[], ℓ⟩ []).map (· ++ v)
    else none

variable {M}

/-- **Soundness of the witness**: a returned run is accepting and `K`-hole-bounded. -/
theorem witness_spec {K : ℕ} {w : List (Symbol × Op n Γ)} (h : M.witness K = some w) :
    ∃ s₀ ∈ M.start, ∃ f ∈ M.accept, M.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨f, Stacks.empty⟩ ∧
      HoleBounded K w := by
  obtain ⟨⟨ℓ, f⟩, -, h⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hf, -⟩ := hc
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hwn, hvrun⟩ := wnWitness_spec hv
  obtain ⟨s₀, hs₀, hrun, hb⟩ :=
    (holeWitness_spec _ ⟨[], ℓ⟩ [] w' List.Forall₂.nil hw').accepting rfl hwn hvrun
  exact ⟨s₀, hs₀, f, hf, hrun, hb⟩

/-- A returned run reads a word of the `K`-hole-bounded language. -/
theorem map_fst_mem_boundedLanguage_of_witness {K : ℕ} {w : List (Symbol × Op n Γ)}
    (h : M.witness K = some w) : w.map Prod.fst ∈ M.boundedLanguage (HoleBounded K) := by
  obtain ⟨s₀, hs₀, f, hf, hrun, hb⟩ := witness_spec h
  exact ⟨s₀, hs₀, f, hf, w, rfl, hrun, hb⟩

/-- **Completeness of the witness**: a run is returned exactly when the search of Algorithm 1
answers `false`, that is, by Theorem 1, exactly when the `K`-hole-bounded language is not
empty. -/
theorem isSome_witness_iff {K : ℕ} : (M.witness K).isSome ↔ M.isEmpty K = false := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, hw⟩ := Option.isSome_iff_exists.mp h
    exact isEmpty_eq_false_of_mem_boundedLanguage (map_fst_mem_boundedLanguage_of_witness hw)
  · simp only [isEmpty, isEmptyFrom, decide_eq_false_iff_not, not_not] at h
    obtain ⟨⟨_, ℓ⟩, hμ, rfl, f, hf, hwr⟩ := h
    have hμR := explore_subset_reachUpTo _ 0 _ _ le_rfl le_rfl hμ
    obtain ⟨e, -, heq, hsub⟩ := stableLayers_eq (M := M) (K := K) (listBound n State K) 0
    have hL : M.stableLayers K (listBound n State K) [M.initialLists] = M.layers K (e + 1) := heq
    refine List.findSome?_isSome_iff.mpr ⟨(ℓ, f), FinEnum.mem_toList _, ?_⟩
    simp only [hL]
    split_ifs with hc
    · exact isSome_bind_map (fun v w => w ++ v) (isSome_wrWitness hwr)
        (isSome_holeWitness e (hsub hμR) le_rfl .nil)
    · exact absurd ⟨(Finset.mem_filter.mp hf).2, hsub hμR⟩ hc

end Witness

end Cslib.Automata.MPDA
