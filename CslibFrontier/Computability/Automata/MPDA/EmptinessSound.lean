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
the symbols pushed by the chosen segments. A pop of the search splits off the last atomic segment
of a hole, so the realization of the shrunk hole extends to one of the old hole that ends with the
popped push. Hole derivations build `K`-hole-bounded sequences (`MPDA.HoleDerivation.holeBounded`).

## Main results

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
/-- A realization of a hole triple gives a hole block and a run of the MPDA that pushes the
realization's symbols on stack `i`. -/
theorem Realizes.exists_holeBlock {i : Fin n} {s t : State} {r : List (Γ × State)}
    (hr : M.Realizes i s t r) (L : ℕ) (σ : Stacks n Γ) :
    ∃ (v : List (Symbol × Op n Γ)) (ps : List (ℕ × Γ)), HoleBlock i L v ps ∧
      ps.map Prod.snd = r.map Prod.fst ∧
      M.configLTS.MTr ⟨s, σ⟩ v ⟨t, Function.update σ i (r.map Prod.fst ++ σ i)⟩ := by
  induction hr with
  | nil => exact ⟨[], [], .nil, rfl, by simp⟩
  | @cons t' t γ r _ hγ ih =>
    obtain ⟨v, ps, hb, hps, hrun⟩ := ih
    obtain ⟨a, s₁, hpush, hwn⟩ := (mem_atomicHoles M).mp hγ
    obtain ⟨ws, hws, hwsrun⟩ := wellNestedReach_iff.mp hwn
    refine ⟨v ++ (a, .push i γ) :: ws, (L + v.length, γ) :: ps, .snoc hb hws, by simp [hps], ?_⟩
    have hσ : Function.update (Function.update σ i (r.map Prod.fst ++ σ i)) i
        (γ :: Function.update σ i (r.map Prod.fst ++ σ i) i) =
        Function.update σ i (((γ, t) :: r).map Prod.fst ++ σ i) := by
      simp
    refine hrun.comp _ (.stepL (s2 := ⟨s₁, Function.update σ i (((γ, t) :: r).map Prod.fst ++ σ i)⟩)
      (configLTS_tr.mpr ⟨hpush, Op.apply_push.mpr hσ.symm⟩) (hws.configLTS_mTr hwsrun _))

end Realize


/-! ## Reachable lists come from hole derivations -/

section Sound

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ] [DecidableEq Γ]
  {M : MPDA n State Symbol Γ} [∀ s μ s', Decidable (M.Tr s μ s')] [DecidablePred (· ∈ M.start)]

/-- **The soundness invariant**: for every realization of the hole triples of a reachable list,
there is a hole derivation of a run of the MPDA, from an initial state with empty stacks to the
last state of the list, whose chains push the realization's symbols. -/
theorem Reachable.exists_holeDerivation {K : ℕ} {μ : HoleList n State}
    (hμ : M.Reachable K M.initialLists μ) :
    ∀ rs : List (List (Γ × State)),
      List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r) rs μ.holes →
      ∃ s₀ ∈ M.start, ∃ (w : List (Symbol × Op n Γ)) (C : List (HoleChain n Γ)),
        HoleDerivation K C w ∧
        List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) C μ.holes ∧
        List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd = r.map Prod.fst)
          C rs ∧
        M.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨μ.last, stacksOf C⟩ := by
  induction hμ with
  | @init μ hμ =>
    intro rs hrs
    obtain ⟨hholes, s₀, hs₀, hwr⟩ := mem_initialLists.mp hμ
    rw [hholes] at hrs
    cases hrs
    obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
    refine ⟨s₀, hs₀, [] ++ v, [], .wellNested .nil hv, by rw [hholes]; exact .nil, .nil, ?_⟩
    rw [stacksOf_nil]
    exact hv.configLTS_mTr hvrun _
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
      obtain ⟨hhs, hs⟩ := Finset.mem_filter.mp hss
      simp only at hs
      subst hs
      obtain ⟨rs₀, rs₁, rfl, hlen, hrs₀, hrs₁⟩ := List.Forall₂.split_right hrs
      obtain ⟨r, rfl⟩ : ∃ r, rs₁ = [r] := by
        cases hrs₁ with
        | cons _ h => cases h; exact ⟨_, rfl⟩
      have hr : M.Realizes i μ.last s' r := by cases hrs₁; assumption
      obtain ⟨s₀, hs₀, w, C, hd, hst, hsym, hrun⟩ := ih rs₀ hrs₀
      obtain ⟨v, ps, hb, hps, hrun'⟩ := hr.exists_holeBlock w.length (stacksOf C)
      refine ⟨s₀, hs₀, w ++ v, C ++ [⟨i, ps⟩], .hole hd (by rw [hst.length_eq]; exact hK) hb,
        List.rel_append hst (.cons rfl .nil), List.rel_append hsym (.cons hps .nil),
        hrun.comp _ ?_⟩
      rw [stacksOf_append_singleton]
      simpa [hps] using hrun'
    · -- A pop.
      obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      unfold addPop at hν
      rcases hsp : splitLastHole i μ.holes with _ | ⟨pre, ⟨s₁, s₃⟩, post⟩
      · simp [hsp] at hν
      obtain ⟨hμh, hpost⟩ := splitLastHole_eq_some hsp
      simp only [hsp, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hν
      -- The common part: the run to the pop and the pop itself.
      have hpop : ∀ (s₂ : State) (γ : Γ) (s' : State) (rpre rpost : List (List (Γ × State)))
          (r : List (Γ × State)), ⟨s₂, γ, s₃⟩ ∈ M.atomicHoles i →
          (∃ b, M.Tr μ.last (b, .pop i γ) s') → rpre.length = pre.length →
          List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r)
            rpre pre →
          M.Realizes i s₁ s₂ r →
          List.Forall₂ (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r)
            rpost post →
          ∃ s₀ ∈ M.start, ∃ (w : List (Symbol × Op n Γ)) (Cpre Cpost : List (HoleChain n Γ))
            (ps : List (ℕ × Γ)), HoleDerivation K (Cpre ++ ⟨i, ps⟩ :: Cpost) w ∧
            List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) Cpre pre ∧
            List.Forall₂ (fun c (h : HoleTriple n State) => c.stack = h.stack) Cpost post ∧
            List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd =
              r.map Prod.fst) Cpre rpre ∧
            List.Forall₂ (fun c (r : List (Γ × State)) => c.pushes.map Prod.snd =
              r.map Prod.fst) Cpost rpost ∧ ps.map Prod.snd = r.map Prod.fst ∧
            M.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨s', stacksOf (Cpre ++ ⟨i, ps⟩ :: Cpost)⟩ := by
        intro s₂ γ s' rpre rpost r hγ ⟨b, hb⟩ hlen hrpre hr hrpost
        have hrs' : List.Forall₂
            (fun r (h : HoleTriple n State) => M.Realizes h.stack h.src h.dst r)
            (rpre ++ ((γ, s₃) :: r) :: rpost) μ.holes := by
          rw [hμh]
          exact List.rel_append hrpre (.cons (.cons hr hγ) hrpost)
        obtain ⟨s₀, hs₀, w, C, hd, hst, hsym, hrun⟩ := ih _ hrs'
        rw [hμh] at hst
        obtain ⟨Cpre, c₀, Cpost, rfl, hClen, hstpre, hc₀, hstpost⟩ := hst.split_right_cons
        have hsym' := List.Forall₂.split_of_length_eq (hClen.trans hlen.symm) hsym
        obtain ⟨hsympre, hsymrest⟩ := hsym'
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
        refine ⟨s₀, hs₀, w ++ [(b, .pop i γ')], Cpre, Cpost, ps, .pop hd hCpost, hstpre, hstpost,
          hsympre, hsympost, hps, hrun.comp _ (.single _ (configLTS_tr.mpr ⟨hb, ?_⟩))⟩
        exact Op.apply_pop.mpr (stacksOf_pop hCpost)
      rcases hν with ⟨⟨s₂, γ, s', s''⟩, ⟨hhs, hγ, hpopt, hwr⟩, rfl⟩ |
        ⟨⟨s₂, γ, s', s''⟩, ⟨⟨hhs, hγ, hpopt, hwr⟩, rfl⟩, rfl⟩
      · -- The hole shrinks.
        simp only at hrs ⊢
        obtain ⟨rpre, r, rpost, rfl, hlen, hrpre, hr, hrpost⟩ := List.Forall₂.split_right_cons hrs
        obtain ⟨s₀, hs₀, w, Cpre, Cpost, ps, hd, hstpre, hstpost, hsympre, hsympost, hps, hrun⟩ :=
          hpop s₂ γ s' rpre rpost r hγ hpopt hlen hrpre hr hrpost
        obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
        exact ⟨s₀, hs₀, w ++ v, Cpre ++ ⟨i, ps⟩ :: Cpost, .wellNested hd hv,
          List.rel_append hstpre (.cons rfl hstpost), List.rel_append hsympre (.cons hps hsympost),
          hrun.comp _ (hv.configLTS_mTr hvrun _)⟩
      · -- The hole closes.
        simp only at hrs ⊢
        obtain ⟨rpre, rpost, rfl, hlen, hrpre, hrpost⟩ := List.Forall₂.split_right hrs
        obtain ⟨s₀, hs₀, w, Cpre, Cpost, ps, hd, hstpre, hstpost, hsympre, hsympost, hps, hrun⟩ :=
          hpop s₂ γ s' rpre rpost [] hγ hpopt hlen hrpre .nil hrpost
        obtain rfl : ps = [] := by simpa using hps
        obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
        refine ⟨s₀, hs₀, w ++ v, Cpre ++ Cpost, .wellNested hd.close hv,
          List.rel_append hstpre hstpost, List.rel_append hsympre hsympost, hrun.comp _ ?_⟩
        rw [stacksOf_close]
        exact hv.configLTS_mTr hvrun _

/-- **Soundness of repaired Algorithm 1** of [AkshayGastinKrishnaRoychowdhury2020]: if the search
answers `false`, some word has a `K`-hole-bounded accepting run. -/
theorem exists_mem_boundedLanguage_of_isEmpty_eq_false [DecidablePred (· ∈ M.accept)] {K : ℕ}
    (h : M.isEmpty K = false) : ∃ x, x ∈ M.boundedLanguage (HoleBounded K) := by
  unfold isEmpty isEmptyFrom at h
  rw [decide_eq_false_iff_not, not_not] at h
  obtain ⟨μ, hμ, hholes, f, hf, hwr⟩ := h
  obtain ⟨s₀, hs₀, w, C, hd, hst, -, hrun⟩ :=
    ((mem_explore fun ν hν => (mem_initialLists.mp hν).1).mp hμ).exists_holeDerivation []
      (by rw [hholes]; exact .nil)
  rw [hholes] at hst
  obtain rfl : C = [] := by cases hst; rfl
  obtain ⟨v, hv, hvrun⟩ := wellNestedReach_iff.mp ((mem_wellNestedPairs M).mp hwr)
  refine ⟨(w ++ v).map Prod.fst, s₀, hs₀, f, (Finset.mem_filter.mp hf).2, w ++ v, rfl, ?_,
    (hd.wellNested hv).holeBounded⟩
  rw [stacksOf_nil] at hrun
  exact hrun.comp _ (hv.configLTS_mTr hvrun _)

end Sound

end Cslib.Automata.MPDA
