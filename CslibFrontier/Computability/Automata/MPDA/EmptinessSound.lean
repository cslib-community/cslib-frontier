/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Emptiness
public import CslibFrontier.Computability.Automata.MPDA.HoleDerivation
public import CslibFrontier.Computability.Automata.MPDA.Underapprox
import CslibFrontier.Foundations.Data.List.Forall2

/-! # Soundness of the emptiness procedure

If repaired Algorithm 1 of [AkshayGastinKrishnaRoychowdhury2020] (`MPDA.isEmpty`) answers `false`,
the MPDA has a `K`-hole-bounded accepting run.

A list of the search abstracts each open hole by a triple `(i, s, t)` of `HSᵢ`. For every choice
of a chain of atomic hole segments realizing each triple (`MPDA.Realizes`), a reachable list comes
from a hole derivation (`MPDA.HoleDerivation`) together with a run of the MPDA whose stacks hold
the symbols pushed by the chosen segments (`MPDA.RunsTo`). Each step of the search extends such a
run: a new hole by a block of atomic segments (`MPDA.BlockRun`), a pop by the pop and a well-nested
run (`MPDA.RunsTo.pop`, `MPDA.RunsTo.popClose`). The witness generation of Section 4 reuses these
steps. A pop of the search splits off the last atomic segment
of a hole, so the realization of the shrunk hole extends to one of the old hole that ends with the
popped push. Hole derivations build `K`-hole-bounded sequences (`MPDA.HoleDerivation.holeBounded`).

## Main results

- `MPDA.Reachable.exists_runsTo`: every realization of the holes of a reachable list is pushed by a
  run that reaches the list.
- `MPDA.exists_mem_boundedLanguage_of_isEmpty_eq_false`: if `isEmpty M K = false`, some word has
  a `K`-hole-bounded accepting run.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Symbol Γ : Type*}

/-! ## Stack contents of open chains -/

/-- The stacks holding the pushes of open chains: on each stack, the pushes of later chains above
those of earlier ones, the newest push of a chain on top. -/
@[expose] def stacksOf (C : List (HoleChain n Γ)) : Stacks n Γ := fun i =>
  ((C.filter fun c => c.stack = i).reverse.flatMap fun c => c.pushes.map Prod.snd)

theorem stacksOf_nil : stacksOf ([] : List (HoleChain n Γ)) = Stacks.empty := rfl

theorem stacksOf_append_singleton (C : List (HoleChain n Γ)) (c : HoleChain n Γ) :
    stacksOf (C ++ [c]) =
      Function.update (stacksOf C) c.stack (c.pushes.map Prod.snd ++ stacksOf C c.stack) := by
  funext j
  by_cases hj : j = c.stack
  · subst hj
    simp [stacksOf, List.filter_append]
  · simp [stacksOf, List.filter_append, Function.update_of_ne hj, Ne.symm hj]

theorem stacksOf_pop {pre post : List (HoleChain n Γ)} {i : Fin n} {p : ℕ} {γ : Γ}
    {ps : List (ℕ × Γ)} (hpost : ∀ c ∈ post, c.stack ≠ i) :
    stacksOf (pre ++ ⟨i, (p, γ) :: ps⟩ :: post) =
      Function.update (stacksOf (pre ++ ⟨i, ps⟩ :: post)) i
        (γ :: stacksOf (pre ++ ⟨i, ps⟩ :: post) i) := by
  have hfilter : ∀ q : List (ℕ × Γ),
      (post.filter fun c => decide (c.stack = i)) = [] := fun _ =>
    List.filter_eq_nil_iff.mpr fun c hc => by simpa using hpost c hc
  funext j
  by_cases hj : j = i
  · subst hj
    simp [stacksOf, List.filter_append, hfilter []]
  · simp [stacksOf, List.filter_append, Function.update_of_ne hj, Ne.symm hj]

theorem stacksOf_close {pre post : List (HoleChain n Γ)} {i : Fin n} :
    stacksOf (pre ++ ⟨i, []⟩ :: post) = stacksOf (pre ++ post) := by
  funext j
  by_cases hj : i = j <;> simp [stacksOf, List.filter_append, hj]

/-! ## Runs that reach a list -/

section Runs

variable {M : MPDA n State Symbol Γ}

variable (M) in
/-- The run `v` from `s` to `t` is a hole block of stack `i` at every position, and pushes the
symbols of the realization `r` on stack `i` from any stacks. -/
def BlockRun (i : Fin n) (s t : State) (r : List (Γ × State)) (v : List (Symbol × Op n Γ)) :
    Prop :=
  (∀ L, ∃ ps : List (ℕ × Γ), HoleBlock i L v ps ∧ ps.map Prod.snd = r.map Prod.fst) ∧
    ∀ σ : Stacks n Γ,
      M.configLTS.MTr ⟨s, σ⟩ v ⟨t, Function.update σ i (r.map Prod.fst ++ σ i)⟩

theorem blockRun_nil {i : Fin n} {s : State} : M.BlockRun i s s [] [] :=
  ⟨fun _ => ⟨[], .nil, rfl⟩, fun σ => by simp⟩

/-- A block extends by an atomic hole segment: a push of `γ` on stack `i`, then a well-nested
run. -/
theorem BlockRun.snoc {i : Fin n} {s t' s₁ t : State} {r : List (Γ × State)}
    {v ws : List (Symbol × Op n Γ)} {a : Symbol} {γ : Γ} (h : M.BlockRun i s t' r v)
    (hpush : M.Tr t' (a, .push i γ) s₁) (hws : WellNested ws) (hwsrun : M.MTr s₁ ws t) :
    M.BlockRun i s t ((γ, t) :: r) (v ++ (a, .push i γ) :: ws) := by
  obtain ⟨hv, hrun⟩ := h
  refine ⟨fun L => ?_, fun σ => ?_⟩
  · obtain ⟨ps, hb, hps⟩ := hv L
    exact ⟨(L + v.length, γ) :: ps, .snoc hb hws, by simp [hps]⟩
  have hσ : Function.update (Function.update σ i (r.map Prod.fst ++ σ i)) i
      (γ :: Function.update σ i (r.map Prod.fst ++ σ i) i) =
      Function.update σ i (((γ, t) :: r).map Prod.fst ++ σ i) := by
    simp
  refine (hrun σ).comp _
    (.stepL (s2 := ⟨s₁, Function.update σ i (((γ, t) :: r).map Prod.fst ++ σ i)⟩)
      (configLTS_tr.mpr ⟨hpush, Op.apply_push.mpr hσ.symm⟩) (hws.configLTS_mTr hwsrun _))

variable (M) in
/-- A run of the MPDA from an initial state with empty stacks to the last state of the list `μ`,
with a hole derivation whose chains have the stacks of the hole triples of `μ` and push the symbols
of the realizations `rs`. -/
def RunsTo (K : ℕ) (μ : HoleList n State) (rs : List (List (Γ × State)))
    (w : List (Symbol × Op n Γ)) : Prop :=
  ∃ s₀ ∈ M.start, ∃ C : List (HoleChain n Γ), HoleDerivation K C w ∧
    List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) C μ.holes ∧
    List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd = r.map Prod.fst) C rs ∧
    M.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨μ.last, stacksOf C⟩

/-- A well-nested run from an initial state reaches a list without holes. -/
theorem runsTo_init {K : ℕ} {s₀ s : State} {v : List (Symbol × Op n Γ)} (hs₀ : s₀ ∈ M.start)
    (hv : WellNested v) (hvrun : M.MTr s₀ v s) : M.RunsTo K ⟨[], s⟩ [] v := by
  refine ⟨s₀, hs₀, [], List.nil_append v ▸ .wellNested .nil hv, .nil, .nil, ?_⟩
  rw [stacksOf_nil]
  exact hv.configLTS_mTr hvrun _

/-- **A new hole**: a block run of a realization extends the run by the
new hole triple, while fewer than `K` holes are open. -/
theorem RunsTo.hole {K : ℕ} {ν : HoleList n State} {rs : List (List (Γ × State))}
    {w v : List (Symbol × Op n Γ)} {i : Fin n} {t : State} {r : List (Γ × State)}
    (h : M.RunsTo K ν rs w) (hK : ν.holes.length < K) (hv : M.BlockRun i ν.last t r v) :
    M.RunsTo K ⟨ν.holes ++ [⟨i, ν.last, t⟩], t⟩ (rs ++ [r]) (w ++ v) := by
  obtain ⟨s₀, hs₀, C, hd, hst, hsym, hrun⟩ := h
  obtain ⟨hv, hvrun⟩ := hv
  obtain ⟨ps, hb, hps⟩ := hv w.length
  refine ⟨s₀, hs₀, C ++ [⟨i, ps⟩], .hole hd (by rw [hst.length_eq]; exact hK) hb,
    List.rel_append hst (.cons rfl .nil), List.rel_append hsym (.cons hps .nil),
    hrun.comp _ ?_⟩
  rw [stacksOf_append_singleton]
  simpa [hps] using hvrun (stacksOf C)

/-- The common part of a pop: the run takes the pop of the newest push of the last hole of stack
`i`, which leaves that hole's chain with one push less. -/
private theorem RunsTo.pop_aux {K : ℕ} {ν : HoleList n State} {w : List (Symbol × Op n Γ)}
    {i : Fin n} {pre post : List (HoleTriple n State)} {s₁ s₃ s' : State} {γ : Γ} {b : Symbol}
    {rpre rpost : List (List (Γ × State))} {r : List (Γ × State)}
    (h : M.RunsTo K ν (rpre ++ ((γ, s₃) :: r) :: rpost) w)
    (hsplit : splitLastHole i ν.holes = some (pre, (s₁, s₃), post))
    (hlen : rpre.length = pre.length) (hb : M.Tr ν.last (b, .pop i γ) s') :
    ∃ s₀ ∈ M.start, ∃ (Cpre Cpost : List (HoleChain n Γ)) (ps : List (ℕ × Γ)),
      HoleDerivation K (Cpre ++ ⟨i, ps⟩ :: Cpost) (w ++ [(b, .pop i γ)]) ∧
      List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) Cpre pre ∧
      List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) Cpost post ∧
      List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd = r.map Prod.fst)
        Cpre rpre ∧
      List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd = r.map Prod.fst)
        Cpost rpost ∧ ps.map Prod.snd = r.map Prod.fst ∧
      M.configLTS.MTr ⟨s₀, Stacks.empty⟩ (w ++ [(b, .pop i γ)])
        ⟨s', stacksOf (Cpre ++ ⟨i, ps⟩ :: Cpost)⟩ := by
  obtain ⟨hμh, hpost⟩ := splitLastHole_eq_some hsplit
  obtain ⟨s₀, hs₀, C, hd, hst, hsym, hrun⟩ := h
  rw [hμh] at hst
  obtain ⟨Cpre, c₀, Cpost, rfl, hClen, hstpre, hc₀, hstpost⟩ := hst.split_right_cons
  obtain ⟨hsympre, hsymrest⟩ := List.Forall₂.split_of_length_eq (hClen.trans hlen.symm) hsym
  cases hsymrest with
  | cons hsym₀ hsympost =>
  obtain ⟨stk, pushes⟩ := c₀
  simp only at hc₀ hsym₀
  subst stk
  obtain ⟨⟨p, γ'⟩, ps, rfl⟩ : ∃ e ps, pushes = e :: ps := by
    cases pushes with
    | nil => simp at hsym₀
    | cons e ps => exact ⟨e, ps, rfl⟩
  simp only [List.map_cons, List.cons.injEq] at hsym₀
  obtain ⟨rfl, hps⟩ := hsym₀
  have hCpost : ∀ c ∈ Cpost, c.stack ≠ i := by
    intro c hc
    obtain ⟨h, hh, hch⟩ := List.Forall₂.exists_mem_of_mem hstpost hc
    rw [hch]
    exact hpost h hh
  refine ⟨s₀, hs₀, Cpre, Cpost, ps, .pop hd hCpost, hstpre, hstpost, hsympre, hsympost, hps,
    hrun.comp _ (.single _ (configLTS_tr.mpr ⟨hb, ?_⟩))⟩
  exact Op.apply_pop.mpr (stacksOf_pop hCpost)

/-- **A pop that shrinks a hole**: the pop of the newest push of the last hole of stack `i`,
followed by a well-nested run, drops the last atomic segment of that hole's realization. -/
theorem RunsTo.pop {K : ℕ} {ν : HoleList n State} {w v : List (Symbol × Op n Γ)} {i : Fin n}
    {pre post : List (HoleTriple n State)} {s₁ s₂ s₃ s' s'' : State} {γ : Γ} {b : Symbol}
    {rpre rpost : List (List (Γ × State))} {r : List (Γ × State)}
    (h : M.RunsTo K ν (rpre ++ ((γ, s₃) :: r) :: rpost) w)
    (hsplit : splitLastHole i ν.holes = some (pre, (s₁, s₃), post))
    (hlen : rpre.length = pre.length) (hb : M.Tr ν.last (b, .pop i γ) s')
    (hv : WellNested v) (hvrun : M.MTr s' v s'') :
    M.RunsTo K ⟨pre ++ ⟨i, s₁, s₂⟩ :: post, s''⟩ (rpre ++ r :: rpost)
      (w ++ (b, .pop i γ) :: v) := by
  obtain ⟨s₀, hs₀, Cpre, Cpost, ps, hd, hstpre, hstpost, hsympre, hsympost, hps, hrun⟩ :=
    h.pop_aux hsplit hlen hb
  rw [show w ++ (b, .pop i γ) :: v = w ++ [(b, .pop i γ)] ++ v by simp]
  exact ⟨s₀, hs₀, Cpre ++ ⟨i, ps⟩ :: Cpost, .wellNested hd hv,
    List.rel_append hstpre (.cons rfl hstpost), List.rel_append hsympre (.cons hps hsympost),
    hrun.comp _ (hv.configLTS_mTr hvrun _)⟩

/-- **A pop that closes a hole**: the pop of the only pending push of the last hole of stack `i`,
followed by a well-nested run, removes that hole. -/
theorem RunsTo.popClose {K : ℕ} {ν : HoleList n State} {w v : List (Symbol × Op n Γ)}
    {i : Fin n} {pre post : List (HoleTriple n State)} {s₁ s₃ s' s'' : State} {γ : Γ}
    {b : Symbol} {rpre rpost : List (List (Γ × State))}
    (h : M.RunsTo K ν (rpre ++ [(γ, s₃)] :: rpost) w)
    (hsplit : splitLastHole i ν.holes = some (pre, (s₁, s₃), post))
    (hlen : rpre.length = pre.length) (hb : M.Tr ν.last (b, .pop i γ) s')
    (hv : WellNested v) (hvrun : M.MTr s' v s'') :
    M.RunsTo K ⟨pre ++ post, s''⟩ (rpre ++ rpost) (w ++ (b, .pop i γ) :: v) := by
  obtain ⟨s₀, hs₀, Cpre, Cpost, ps, hd, hstpre, hstpost, hsympre, hsympost, hps, hrun⟩ :=
    h.pop_aux hsplit hlen hb
  obtain rfl : ps = [] := by simpa using hps
  rw [show w ++ (b, .pop i γ) :: v = w ++ [(b, .pop i γ)] ++ v by simp]
  refine ⟨s₀, hs₀, Cpre ++ Cpost, .wellNested hd.close hv, List.rel_append hstpre hstpost,
    List.rel_append hsympre hsympost, hrun.comp _ ?_⟩
  rw [stacksOf_close]
  exact hv.configLTS_mTr hvrun _

/-- A run reaching a list without holes, followed by a well-nested run to a final state, is an
accepting `K`-hole-bounded run. -/
theorem RunsTo.accepting {K : ℕ} {μ : HoleList n State} {w v : List (Symbol × Op n Γ)}
    {f : State} (h : M.RunsTo K μ [] w) (hholes : μ.holes = []) (hv : WellNested v)
    (hvrun : M.MTr μ.last v f) :
    ∃ s₀ ∈ M.start, M.configLTS.MTr ⟨s₀, Stacks.empty⟩ (w ++ v) ⟨f, Stacks.empty⟩ ∧
      HoleBounded K (w ++ v) := by
  obtain ⟨s₀, hs₀, C, hd, hst, -, hrun⟩ := h
  rw [hholes] at hst
  obtain rfl : C = [] := by cases hst; rfl
  rw [stacksOf_nil] at hrun
  exact ⟨s₀, hs₀, hrun.comp _ (hv.configLTS_mTr hvrun _), (hd.wellNested hv).holeBounded⟩

end Runs

/-! ## Realizations of hole triples -/

section Realize

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ] [DecidableEq Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- A chain of atomic hole segments of stack `i` from `s` to `t`, as the pushed symbols and the
states after each segment, newest first. -/
inductive Realizes (i : Fin n) (s : State) : State → List (Γ × State) → Prop where
  | nil : Realizes i s s []
  | cons {t' t : State} {γ : Γ} {r : List (Γ × State)} :
    Realizes i s t' r → ⟨t', γ, t⟩ ∈ M.atomicHoles i → Realizes i s t ((γ, t) :: r)

variable {M}

/-- The hole triples of `HSᵢ` are exactly those with a realization. -/
theorem mem_holeSegments_iff_realizes {i : Fin n} {s t : State} :
    (s, t) ∈ M.holeSegments i ↔ ∃ r, M.Realizes i s t r := by
  rw [mem_holeSegments]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], .nil⟩
    | tail _ hstep ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨γ, hγ⟩ := hstep
      exact ⟨_, .cons hr hγ⟩
  · rintro ⟨r, hr⟩
    induction hr with
    | nil => exact .refl
    | cons _ hγ ih => exact ih.tail ⟨_, hγ⟩

omit [DecidableEq Γ] in
/-- A realization of a hole triple gives a run of the MPDA that is a hole block at every position
and pushes the realization's symbols on stack `i` from any stacks (`MPDA.BlockRun`). -/
theorem Realizes.exists_blockRun {i : Fin n} {s t : State} {r : List (Γ × State)}
    (hr : M.Realizes i s t r) : ∃ v, M.BlockRun i s t r v := by
  induction hr with
  | nil => exact ⟨[], blockRun_nil⟩
  | cons _ hγ ih =>
    obtain ⟨v, hv⟩ := ih
    obtain ⟨a, s₁, hpush, hwn⟩ := (mem_atomicHoles M).mp hγ
    obtain ⟨ws, hws, hwsrun⟩ := wellNestedReach_iff.mp hwn
    exact ⟨_, hv.snoc hpush hws hwsrun⟩

end Realize


/-! ## Reachable lists come from hole derivations -/

section Sound

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ] [DecidableEq Γ]
  {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')] [DecidablePred (· ∈ M.start)]

/-- **The soundness invariant**: for every realization of the hole triples of a reachable list,
some run of the MPDA reaches the list (`MPDA.RunsTo`). -/
theorem Reachable.exists_runsTo {K : ℕ} {μ : HoleList n State}
    (hμ : M.Reachable K M.initialLists μ) :
    ∀ rs : List (List (Γ × State)),
      List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r) rs
        μ.holes →
      ∃ w, M.RunsTo K μ rs w := by
  induction hμ with
  | @init μ hμ =>
    intro rs hrs
    obtain ⟨hholes, s₀, hs₀, hwr⟩ := mem_initialLists.mp hμ
    obtain ⟨holes, last⟩ := μ
    simp only at hholes hrs
    subst hholes
    cases hrs
    obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
    exact ⟨v, runsTo_init hs₀ hv hvrun⟩
  | @step μ ν _ hν ih =>
    intro rs hrs
    simp only [successors, Finset.mem_union] at hν
    rcases hν with hν | hν
    · -- A new hole.
      split_ifs at hν with hK
      swap
      · simp at hν
      obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      obtain ⟨⟨s, s'⟩, hss, rfl⟩ := Finset.mem_image.mp hν
      obtain ⟨-, hs⟩ := Finset.mem_filter.mp hss
      simp only at hs
      subst hs
      obtain ⟨rs₀, rs₁, rfl, -, hrs₀, hrs₁⟩ := List.Forall₂.split_right hrs
      obtain ⟨r, rfl⟩ : ∃ r, rs₁ = [r] := by
        cases hrs₁ with
        | cons _ h => cases h; exact ⟨_, rfl⟩
      have hr : M.Realizes i μ.last s' r := by cases hrs₁; assumption
      obtain ⟨w, hw⟩ := ih rs₀ hrs₀
      obtain ⟨v, hv⟩ := hr.exists_blockRun
      exact ⟨w ++ v, hw.hole hK hv⟩
    · -- A pop.
      obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      unfold addPop at hν
      rcases hsp : splitLastHole i μ.holes with _ | ⟨pre, ⟨s₁, s₃⟩, post⟩
      · simp [hsp] at hν
      obtain ⟨hμh, -⟩ := splitLastHole_eq_some hsp
      simp only [hsp, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hν
      rcases hν with ⟨⟨s₂, γ, s', s''⟩, ⟨-, hγ, ⟨b, hb⟩, hwr⟩, rfl⟩ |
        ⟨⟨s₂, γ, s', s''⟩, ⟨⟨-, hγ, ⟨b, hb⟩, hwr⟩, rfl⟩, rfl⟩
      · -- The hole shrinks.
        simp only at hrs ⊢
        obtain ⟨rpre, r, rpost, rfl, hlen, hrpre, hr, hrpost⟩ := List.Forall₂.split_right_cons hrs
        obtain ⟨w, hw⟩ := ih _ (by
          rw [hμh]; exact List.rel_append hrpre (.cons (.cons hr hγ) hrpost))
        obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
        exact ⟨_, hw.pop hsp hlen hb hv hvrun⟩
      · -- The hole closes.
        simp only at hrs ⊢
        obtain ⟨rpre, rpost, rfl, hlen, hrpre, hrpost⟩ := List.Forall₂.split_right hrs
        obtain ⟨w, hw⟩ := ih _ (by
          rw [hμh]; exact List.rel_append hrpre (.cons (.cons .nil hγ) hrpost))
        obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
        exact ⟨_, hw.popClose hsp hlen hb hv hvrun⟩

/-- **Soundness of repaired Algorithm 1** of [AkshayGastinKrishnaRoychowdhury2020]: if the search
answers `false`, some word has a `K`-hole-bounded accepting run. -/
theorem exists_mem_boundedLanguage_of_isEmpty_eq_false [DecidablePred (· ∈ M.accept)] {K : ℕ}
    (h : M.isEmpty K = false) : ∃ x, x ∈ M.boundedLanguage (HoleBounded K) := by
  unfold isEmpty isEmptyFrom at h
  rw [decide_eq_false_iff_not, not_not] at h
  obtain ⟨μ, hμ, hholes, f, hf, hwr⟩ := h
  obtain ⟨w, hw⟩ := ((mem_explore fun ν hν => (mem_initialLists.mp hν).1).mp hμ).exists_runsTo []
    (by rw [hholes]; exact .nil)
  obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
  obtain ⟨s₀, hs₀, hrun, hb⟩ := hw.accepting hholes hv hvrun
  exact ⟨_, s₀, hs₀, f, (Finset.mem_filter.mp hf).2, w ++ v, rfl, hrun, hb⟩

end Sound

end Cslib.Automata.MPDA
