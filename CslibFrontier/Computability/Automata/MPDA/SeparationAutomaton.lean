/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Separation

/-! # A visibly MPDA recognizing `L_bh`

We construct a finite visibly MPDA `MPDA.HoleSeparation.automaton` that accepts exactly the
language `L_bh` of [AkshayGastinKrishnaRoychowdhury2020]. With the run-level bounds of
`MPDA.HoleSeparation`, this proves the second sentence of Proposition 2 for visibly MPDAs as a
statement about languages with bounded acceptance (`MPDA.boundedLanguage`): `L_bh` is the
`2`-hole-bounded language of this automaton, and for every `K` it is not the `K`-scope-, context- or
round-bounded language of any visibly MPDA.

The automaton pushes `outer` for the letters of `aⁿ bⁿ` and `inner` for the letters `a` and `b`
inside groups. In a group `aᵖ cᵖ⁺¹ b^q d^(q+1)`, the letters `c` pop the `p` symbols `inner` and
then exactly one `outer`, and likewise for `d`. Acceptance with empty stacks forces as many groups
as letters `a` and as letters `b` in the prefix.

## Main definitions

- `MPDA.HoleSeparation.automaton`: the automaton.

## Main results

- `MPDA.HoleSeparation.language_automaton`: it recognizes exactly `L_bh`.
- `MPDA.HoleSeparation.language_separates_holeBounded_scopeBounded`: `L_bh` separates hole-bounded
  from scope-, context- and round-bounded languages, the second sentence of Proposition 2 for
  visibly MPDAs.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA.HoleSeparation

/-! ## The automaton -/

/-- Stack symbols: `outer` for the prefix `aⁿ bⁿ`, `inner` inside groups. -/
inductive Sym where
  | outer | inner
  deriving DecidableEq

/-- Control states: reading the prefix `aⁿ` (`pa`) or `bⁿ` (`pb`); inside a group, reading its
letters `a` (`ga`), `c` (`gc`), the first `b` or `d` after its extra `c` (`gb`), its letters `b`
(`gB`) or `d` (`gd`); and after a complete group (`ge`). -/
inductive State where
  | pa | pb | ga | gc | gb | gB | gd | ge
  deriving DecidableEq

instance : Finite Sym :=
  Finite.of_injective (β := Fin 2) (fun | .outer => 0 | .inner => 1) (by
    intro x y h
    cases x <;> cases y <;> simp_all)

instance : Finite State :=
  Finite.of_injective (β := Fin 8)
    (fun | .pa => 0 | .pb => 1 | .ga => 2 | .gc => 3 | .gb => 4 | .gB => 5 | .gd => 6 | .ge => 7)
    (by intro x y h; cases x <;> cases y <;> simp_all)

/-- The transitions of `automaton`. -/
inductive Step : State → Letter × Op 2 Sym → State → Prop where
  | pa_a : Step .pa (.a, .push 0 .outer) .pa
  | pa_b : Step .pa (.b, .push 1 .outer) .pb
  | pb_b : Step .pb (.b, .push 1 .outer) .pb
  | pb_a : Step .pb (.a, .push 0 .inner) .ga
  | pb_c : Step .pb (.c, .pop 0 .outer) .gb
  | ga_a : Step .ga (.a, .push 0 .inner) .ga
  | ga_c : Step .ga (.c, .pop 0 .inner) .gc
  | gc_c : Step .gc (.c, .pop 0 .inner) .gc
  | gc_c' : Step .gc (.c, .pop 0 .outer) .gb
  | gb_b : Step .gb (.b, .push 1 .inner) .gB
  | gb_d : Step .gb (.d, .pop 1 .outer) .ge
  | gB_b : Step .gB (.b, .push 1 .inner) .gB
  | gB_d : Step .gB (.d, .pop 1 .inner) .gd
  | gd_d : Step .gd (.d, .pop 1 .inner) .gd
  | gd_d' : Step .gd (.d, .pop 1 .outer) .ge
  | ge_a : Step .ge (.a, .push 0 .inner) .ga
  | ge_c : Step .ge (.c, .pop 0 .outer) .gb

/-- A visibly MPDA recognizing `L_bh`. -/
@[expose] def automaton : MPDA 2 State Letter Sym where
  Tr := Step
  start := {.pa}
  accept := {.pa, .ge}

theorem automaton_isVisibly : automaton.IsVisibly kind := fun _ _ _ _ h => by cases h <;> rfl

/-! ## Runs -/

private theorem step_iff {q q' : State} {μ : Letter × Op 2 Sym} {s₀ s₁ : List Sym}
    {σ : Stacks 2 Sym} :
    automaton.configLTS.Tr ⟨q, Stacks.pair s₀ s₁⟩ μ ⟨q', σ⟩ ↔
      Step q μ q' ∧ μ.2.Apply (Stacks.pair s₀ s₁) σ :=
  configLTS_tr

/-! ## Every accepted word is in `L_bh` -/

/-- The prefix `aⁿ bᵏ` followed by complete groups. -/
private def pre (n k : ℕ) (gs : List (List Letter)) : List Letter :=
  List.replicate n .a ++ List.replicate k .b ++ gs.flatten

/-- Every member of `gs` is a group. -/
private def Grouped (gs : List (List Letter)) : Prop := ∀ g ∈ gs, ∃ p q, g = group p q

/-- The reachable configurations: for each control state, the input read so far and the stack
contents. `n` and `k` count the letters `a` and `b` of the prefix, and `gs` the complete groups. -/
private def Inv : State → List Sym → List Sym → List Letter → Prop
  | .pa, s₀, s₁, u => ∃ n, u = List.replicate n .a ∧ s₀ = List.replicate n .outer ∧ s₁ = []
  | .pb, s₀, s₁, u => ∃ n k, u = List.replicate n .a ++ List.replicate (k + 1) .b ∧
      s₀ = List.replicate n .outer ∧ s₁ = List.replicate (k + 1) .outer
  | .ga, s₀, s₁, u => ∃ n k gs p, Grouped gs ∧ gs.length ≤ n ∧ gs.length ≤ k ∧ 1 ≤ p ∧
      u = pre n k gs ++ List.replicate p .a ∧
      s₀ = List.replicate p .inner ++ List.replicate (n - gs.length) .outer ∧
      s₁ = List.replicate (k - gs.length) .outer
  | .gc, s₀, s₁, u => ∃ n k gs p r, Grouped gs ∧ gs.length ≤ n ∧ gs.length ≤ k ∧ 1 ≤ r ∧
      r ≤ p ∧ u = pre n k gs ++ List.replicate p .a ++ List.replicate r .c ∧
      s₀ = List.replicate (p - r) .inner ++ List.replicate (n - gs.length) .outer ∧
      s₁ = List.replicate (k - gs.length) .outer
  | .gb, s₀, s₁, u => ∃ n k gs p, Grouped gs ∧ gs.length < n ∧ gs.length ≤ k ∧
      u = pre n k gs ++ List.replicate p .a ++ List.replicate (p + 1) .c ∧
      s₀ = List.replicate (n - gs.length - 1) .outer ∧ s₁ = List.replicate (k - gs.length) .outer
  | .gB, s₀, s₁, u => ∃ n k gs p q, Grouped gs ∧ gs.length < n ∧ gs.length ≤ k ∧ 1 ≤ q ∧
      u = pre n k gs ++ List.replicate p .a ++ List.replicate (p + 1) .c ++ List.replicate q .b ∧
      s₀ = List.replicate (n - gs.length - 1) .outer ∧
      s₁ = List.replicate q .inner ++ List.replicate (k - gs.length) .outer
  | .gd, s₀, s₁, u => ∃ n k gs p q r, Grouped gs ∧ gs.length < n ∧ gs.length ≤ k ∧ 1 ≤ r ∧
      r ≤ q ∧ u = pre n k gs ++ List.replicate p .a ++ List.replicate (p + 1) .c ++
        List.replicate q .b ++ List.replicate r .d ∧
      s₀ = List.replicate (n - gs.length - 1) .outer ∧
      s₁ = List.replicate (q - r) .inner ++ List.replicate (k - gs.length) .outer
  | .ge, s₀, s₁, u => ∃ n k gs, Grouped gs ∧ gs.length ≤ n ∧ gs.length ≤ k ∧ u = pre n k gs ∧
      s₀ = List.replicate (n - gs.length) .outer ∧ s₁ = List.replicate (k - gs.length) .outer

private theorem replicate_eq_cons {y : ℕ} {γ : Sym} {t : List Sym}
    (h : List.replicate y Sym.outer = γ :: t) :
    0 < y ∧ γ = .outer ∧ t = List.replicate (y - 1) .outer := by
  rcases y with _ | y
  · simp at h
  · simp only [List.replicate_succ, List.cons.injEq] at h
    exact ⟨by omega, h.1.symm, by simpa using h.2.symm⟩

private theorem replicate_append_eq_cons {x y : ℕ} {γ : Sym} {t : List Sym}
    (h : List.replicate x Sym.inner ++ List.replicate y .outer = γ :: t) :
    (0 < x ∧ γ = .inner ∧ t = List.replicate (x - 1) .inner ++ List.replicate y .outer) ∨
      (x = 0 ∧ 0 < y ∧ γ = .outer ∧ t = List.replicate (y - 1) .outer) := by
  rcases x with _ | x
  · simp only [List.replicate_zero, List.nil_append] at h
    exact .inr ⟨rfl, replicate_eq_cons h⟩
  · simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
    exact .inl ⟨by omega, h.1.symm, by simpa using h.2.symm⟩

private theorem pre_append_group (n k : ℕ) (gs : List (List Letter)) (p q : ℕ) :
    pre n k gs ++ List.replicate p .a ++ List.replicate (p + 1) .c ++ List.replicate q .b ++
      List.replicate (q + 1) .d = pre n k (gs ++ [group p q]) := by
  simp [pre, group, List.append_assoc]

private theorem grouped_append_singleton {gs : List (List Letter)} {g : List Letter}
    (hg : Grouped gs) (hg' : ∃ p q, g = group p q) : Grouped (gs ++ [g]) :=
  fun x hx => (List.mem_append.mp hx).elim (hg x) fun h => List.mem_singleton.mp h ▸ hg'

/-- One transition preserves the invariant. -/
private theorem inv_step {q q' : State} {s₀ s₁ : List Sym} {u : List Letter}
    {μ : Letter × Op 2 Sym} {σ : Stacks 2 Sym} (hinv : Inv q s₀ s₁ u)
    (h : automaton.configLTS.Tr ⟨q, Stacks.pair s₀ s₁⟩ μ ⟨q', σ⟩) :
    ∃ t₀ t₁, σ = Stacks.pair t₀ t₁ ∧ Inv q' t₀ t₁ (u ++ [μ.1]) := by
  obtain ⟨hstep, happ⟩ := step_iff.mp h
  cases hstep with
  | pa_a =>
    obtain ⟨n, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_zero_pair.mp happ, n + 1, by simp [List.replicate_succ'],
      by simp [List.replicate_succ], rfl⟩
  | pa_b =>
    obtain ⟨n, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_one_pair.mp happ, n, 0, by simp, rfl, rfl⟩
  | pb_b =>
    obtain ⟨n, k, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_one_pair.mp happ, n, k + 1,
      by simp [List.replicate_succ', List.append_assoc], rfl, by simp [List.replicate_succ]⟩
  | pb_a =>
    obtain ⟨n, k, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_zero_pair.mp happ, n, k + 1, [], 1, fun _ h => by simp at h,
      by simp, by simp, le_rfl, by simp [pre], by simp, by simp⟩
  | pb_c =>
    obtain ⟨n, k, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    obtain ⟨hn, -, rfl⟩ := replicate_eq_cons ht
    exact ⟨_, _, rfl, n, k + 1, [], 0, fun _ h => by simp at h, by simpa using hn, by simp,
      by simp [pre], by simp, by simp⟩
  | ga_a =>
    obtain ⟨n, k, gs, p, hg, hn, hk, hp, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_zero_pair.mp happ, n, k, gs, p + 1, hg, hn, hk, by omega,
      by simp [List.replicate_succ', List.append_assoc], by simp [List.replicate_succ], rfl⟩
  | ga_c =>
    obtain ⟨n, k, gs, p, hg, hn, hk, hp, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    rcases replicate_append_eq_cons ht with ⟨-, -, rfl⟩ | ⟨rfl, -⟩
    · exact ⟨_, _, rfl, n, k, gs, p, 1, hg, hn, hk, le_rfl, hp, by simp [List.append_assoc],
        rfl, rfl⟩
    · omega
  | gc_c =>
    obtain ⟨n, k, gs, p, r, hg, hn, hk, hr, hrp, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    rcases replicate_append_eq_cons ht with ⟨hpr, -, rfl⟩ | ⟨-, -, h, -⟩
    · exact ⟨_, _, rfl, n, k, gs, p, r + 1, hg, hn, hk, by omega, by omega,
        by simp [List.replicate_succ', List.append_assoc], rfl, rfl⟩
    · cases h
  | gc_c' =>
    obtain ⟨n, k, gs, p, r, hg, hn, hk, hr, hrp, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    rcases replicate_append_eq_cons ht with ⟨-, h, -⟩ | ⟨hpr, hn', -, rfl⟩
    · cases h
    · obtain rfl : r = p := by omega
      exact ⟨_, _, rfl, n, k, gs, r, hg, by omega, hk,
        by simp [List.replicate_succ', List.append_assoc], rfl, rfl⟩
  | gb_b =>
    obtain ⟨n, k, gs, p, hg, hn, hk, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_one_pair.mp happ, n, k, gs, p, 1, hg, hn, hk, le_rfl, by simp,
      rfl, by simp⟩
  | gb_d =>
    obtain ⟨n, k, gs, p, hg, hn, hk, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_one_pair.mp happ
    obtain ⟨hk', -, rfl⟩ := replicate_eq_cons ht
    refine ⟨_, _, rfl, n, k, gs ++ [group p 0], grouped_append_singleton hg ⟨p, 0, rfl⟩,
      by simp; omega, by simp; omega, ?_, ?_, ?_⟩
    · simp [← pre_append_group]
    all_goals simp [Nat.sub_sub]
  | gB_b =>
    obtain ⟨n, k, gs, p, q, hg, hn, hk, hq, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_one_pair.mp happ, n, k, gs, p, q + 1, hg, hn, hk, by omega,
      by simp [List.replicate_succ', List.append_assoc], rfl, by simp [List.replicate_succ]⟩
  | gB_d =>
    obtain ⟨n, k, gs, p, q, hg, hn, hk, hq, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_one_pair.mp happ
    rcases replicate_append_eq_cons ht with ⟨-, -, rfl⟩ | ⟨rfl, -⟩
    · exact ⟨_, _, rfl, n, k, gs, p, q, 1, hg, hn, hk, le_rfl, hq,
        by simp [List.append_assoc], rfl, rfl⟩
    · omega
  | gd_d =>
    obtain ⟨n, k, gs, p, q, r, hg, hn, hk, hr, hrq, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_one_pair.mp happ
    rcases replicate_append_eq_cons ht with ⟨hqr, -, rfl⟩ | ⟨-, -, h, -⟩
    · exact ⟨_, _, rfl, n, k, gs, p, q, r + 1, hg, hn, hk, by omega, by omega,
        by simp [List.replicate_succ', List.append_assoc], rfl, rfl⟩
    · cases h
  | gd_d' =>
    obtain ⟨n, k, gs, p, q, r, hg, hn, hk, hr, hrq, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_one_pair.mp happ
    rcases replicate_append_eq_cons ht with ⟨-, h, -⟩ | ⟨hqr, hk', -, rfl⟩
    · cases h
    · obtain rfl : r = q := by omega
      refine ⟨_, _, rfl, n, k, gs ++ [group p r], grouped_append_singleton hg ⟨p, r, rfl⟩,
        by simp; omega, by simp; omega, ?_, ?_, ?_⟩
      · simp [← pre_append_group, List.replicate_succ', List.append_assoc]
      all_goals simp [Nat.sub_sub]
  | ge_a =>
    obtain ⟨n, k, gs, hg, hn, hk, rfl, rfl, rfl⟩ := hinv
    exact ⟨_, _, Op.apply_push_zero_pair.mp happ, n, k, gs, 1, hg, hn, hk, le_rfl, rfl, by simp,
      rfl⟩
  | ge_c =>
    obtain ⟨n, k, gs, hg, hn, hk, rfl, rfl, rfl⟩ := hinv
    obtain ⟨t, ht, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    obtain ⟨hn', -, rfl⟩ := replicate_eq_cons ht
    exact ⟨_, _, rfl, n, k, gs, 0, hg, by omega, hk, by simp, by congr 1, rfl⟩

private theorem mem_language_of_accepts {w : List Letter} (h : Acceptor.Accepts automaton w) :
    w ∈ language := by
  obtain ⟨_, rfl, s', hs', μs, rfl, hrun⟩ := h
  rw [Stacks.empty_eq_pair] at hrun
  obtain ⟨_, _, hc, hinv⟩ :=
    exists_inv_pair_of_configLTS_mTr Inv inv_step hrun ⟨0, rfl, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := Stacks.eq_pair_iff.mp hc.symm
  rcases hs' with rfl | rfl
  · obtain ⟨n, hu, h0, -⟩ := hinv
    obtain rfl : n = 0 := by simpa using congrArg List.length h0.symm
    exact ⟨0, [], rfl, by simp, by simpa using hu⟩
  · obtain ⟨n, k, gs, hg, hn, hk, hu, h0, h1⟩ := hinv
    have l0 := congrArg List.length h0
    have l1 := congrArg List.length h1
    simp only [List.length_nil, List.length_replicate] at l0 l1
    obtain rfl : n = gs.length := by omega
    obtain rfl : k = gs.length := by omega
    exact ⟨gs.length, gs, rfl, hg, by simpa [pre] using hu⟩

/-! ## Every word of `L_bh` is accepted -/

private theorem replicate_append_cons {β : Type*} (p : ℕ) (x : β) (l : List β) :
    List.replicate p x ++ x :: l = x :: (List.replicate p x ++ l) := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ,
    List.cons_append]

private theorem replicate_append_singleton {β : Type*} (p : ℕ) (x : β) :
    List.replicate p x ++ [x] = x :: List.replicate p x := by
  simpa using replicate_append_cons p x []

/-- A run on one group, from `pb` or `ge`, pops one `outer` from each stack. -/
private theorem run_group {q₀ : State} (hq₀ : q₀ = .pb ∨ q₀ = .ge) (p q : ℕ) (t₀ t₁ : List Sym) :
    ∃ μs : List (Letter × Op 2 Sym), μs.map Prod.fst = group p q ∧
      automaton.configLTS.MTr ⟨q₀, Stacks.pair (.outer :: t₀) (.outer :: t₁)⟩ μs
        ⟨.ge, Stacks.pair t₀ t₁⟩ := by
  -- The letters `aᵖ cᵖ⁺¹`, ending in `gb` with the `outer` of stack `0` popped.
  obtain ⟨μ₁, hμ₁, h₁⟩ : ∃ μ₁ : List (Letter × Op 2 Sym),
      μ₁.map Prod.fst = List.replicate p .a ++ List.replicate (p + 1) .c ∧
      automaton.configLTS.MTr ⟨q₀, Stacks.pair (.outer :: t₀) (.outer :: t₁)⟩ μ₁
        ⟨.gb, Stacks.pair t₀ (.outer :: t₁)⟩ := by
    rcases p with _ | p
    · refine ⟨[(.c, .pop 0 .outer)], rfl, .single _ (step_iff.mpr ⟨?_, Op.apply_pop_zero_pair.mpr
        ⟨_, rfl, rfl⟩⟩)⟩
      rcases hq₀ with rfl | rfl <;> [exact .pb_c; exact .ge_c]
    · refine ⟨(.a, .push 0 .inner) :: List.replicate p (.a, .push 0 .inner) ++
        (.c, .pop 0 .inner) :: List.replicate p (.c, .pop 0 .inner) ++ [(.c, .pop 0 .outer)],
        by simp [List.replicate_succ, replicate_append_singleton], ?_⟩
      have hfirst : automaton.configLTS.Tr ⟨q₀, Stacks.pair (.outer :: t₀) (.outer :: t₁)⟩
          (.a, .push 0 .inner) ⟨.ga, Stacks.pair (.inner :: .outer :: t₀) (.outer :: t₁)⟩ := by
        refine step_iff.mpr ⟨?_, Op.apply_push_zero_pair.mpr rfl⟩
        rcases hq₀ with rfl | rfl <;> [exact .pb_a; exact .ge_a]
      refine .comp _ (.comp _ (.stepL hfirst
        (configLTS_mTr_replicate_push_zero (M := automaton) Step.ga_a _ p _))
        (.stepL (step_iff.mpr
          ⟨.ga_c, Op.apply_pop_zero_pair.mpr ⟨_, replicate_append_cons _ _ _, rfl⟩⟩)
        (configLTS_mTr_replicate_pop_zero (M := automaton) Step.gc_c _ p _)))
        (.single _ (step_iff.mpr ⟨.gc_c', Op.apply_pop_zero_pair.mpr ⟨_, rfl, rfl⟩⟩))
  -- The letters `b^q d^(q+1)`, ending in `ge` with the `outer` of stack `1` popped.
  obtain ⟨μ₂, hμ₂, h₂⟩ : ∃ μ₂ : List (Letter × Op 2 Sym),
      μ₂.map Prod.fst = List.replicate q .b ++ List.replicate (q + 1) .d ∧
      automaton.configLTS.MTr ⟨.gb, Stacks.pair t₀ (.outer :: t₁)⟩ μ₂ ⟨.ge, Stacks.pair t₀ t₁⟩ := by
    rcases q with _ | q
    · exact ⟨[(.d, .pop 1 .outer)], rfl, .single _ (step_iff.mpr ⟨.gb_d, Op.apply_pop_one_pair.mpr
        ⟨_, rfl, rfl⟩⟩)⟩
    · refine ⟨(.b, .push 1 .inner) :: List.replicate q (.b, .push 1 .inner) ++
        (.d, .pop 1 .inner) :: List.replicate q (.d, .pop 1 .inner) ++ [(.d, .pop 1 .outer)],
        by simp [List.replicate_succ, replicate_append_singleton], ?_⟩
      refine .comp _ (.comp _ (.stepL (step_iff.mpr ⟨.gb_b, Op.apply_push_one_pair.mpr rfl⟩)
        (configLTS_mTr_replicate_push_one (M := automaton) Step.gB_b _ q _))
        (.stepL (step_iff.mpr ⟨.gB_d,
        Op.apply_pop_one_pair.mpr ⟨_, replicate_append_cons _ _ _, rfl⟩⟩)
        (configLTS_mTr_replicate_pop_one (M := automaton) Step.gd_d _ q _)))
        (.single _ (step_iff.mpr ⟨.gd_d', Op.apply_pop_one_pair.mpr ⟨_, rfl, rfl⟩⟩))
  exact ⟨μ₁ ++ μ₂, by simp [hμ₁, hμ₂, group, List.append_assoc], .comp _ h₁ h₂⟩

/-- Runs on sequences of groups, from `pb` or `ge`. -/
private theorem run_groups : ∀ (gs : List (List Letter)), Grouped gs → gs ≠ [] →
    ∀ {q₀ : State}, (q₀ = .pb ∨ q₀ = .ge) →
      ∃ μs : List (Letter × Op 2 Sym), μs.map Prod.fst = gs.flatten ∧
        automaton.configLTS.MTr ⟨q₀, Stacks.pair (List.replicate gs.length .outer)
          (List.replicate gs.length .outer)⟩ μs ⟨.ge, Stacks.pair [] []⟩
  | [], _, h, _, _ => absurd rfl h
  | g :: gs, hg, _, q₀, hq₀ => by
    obtain ⟨p, q, rfl⟩ := hg g List.mem_cons_self
    obtain ⟨μ₁, hμ₁, h₁⟩ := run_group hq₀ p q (List.replicate gs.length .outer)
      (List.replicate gs.length .outer)
    by_cases hgs : gs = []
    · subst hgs
      exact ⟨μ₁, by simpa using hμ₁, by simpa using h₁⟩
    · obtain ⟨μ₂, hμ₂, h₂⟩ := run_groups gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
        hgs (q₀ := .ge) (.inr rfl)
      exact ⟨μ₁ ++ μ₂, by simp [hμ₁, hμ₂], by simpa [List.replicate_succ] using .comp _ h₁ h₂⟩

private theorem accepts_of_mem_language {w : List Letter} (h : w ∈ language) :
    Acceptor.Accepts automaton w := by
  obtain ⟨n, gs, hlen, hg, rfl⟩ := h
  rcases n with _ | n
  · obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact ⟨.pa, rfl, .pa, .inl rfl, [], rfl, .refl⟩
  -- The prefix `aⁿ⁺¹ bⁿ⁺¹`.
  have hpre : automaton.configLTS.MTr ⟨.pa, Stacks.empty⟩
      (List.replicate (n + 1) (.a, .push 0 .outer) ++ (.b, .push 1 .outer) ::
        List.replicate n (.b, .push 1 .outer))
      ⟨.pb, Stacks.pair (List.replicate (n + 1) .outer) (List.replicate (n + 1) .outer)⟩ := by
    rw [Stacks.empty_eq_pair]
    refine .comp _
      (by simpa using configLTS_mTr_replicate_push_zero (M := automaton) Step.pa_a [] (n + 1) [])
      (.stepL (step_iff.mpr ⟨.pa_b, Op.apply_push_one_pair.mpr rfl⟩) ?_)
    simpa [List.replicate_succ'] using
      configLTS_mTr_replicate_push_one (M := automaton) Step.pb_b
        (List.replicate (n + 1) .outer) n [.outer]
  obtain ⟨μs, hμs, hrun⟩ := run_groups gs hg (by rintro rfl; simp at hlen) (q₀ := .pb) (.inl rfl)
  rw [hlen] at hrun
  refine ⟨.pa, rfl, .ge, .inr rfl, (List.replicate (n + 1) (.a, .push 0 .outer) ++
    (.b, .push 1 .outer) :: List.replicate n (.b, .push 1 .outer)) ++ μs,
    by simp [hμs, List.replicate_succ, List.append_assoc],
    by simpa [Stacks.empty_eq_pair] using hpre.comp _ hrun⟩

/-! ## The separation of languages -/

/-- `automaton` recognizes exactly `L_bh`. -/
theorem language_automaton : Acceptor.language automaton = language :=
  Set.ext fun _ => ⟨mem_language_of_accepts, accepts_of_mem_language⟩

/-- **`L_bh` separates hole-bounded from scope-, context- and round-bounded languages**, the second
sentence of Proposition 2 of [AkshayGastinKrishnaRoychowdhury2020] (arXiv:2002.05950v2, Section
2.1, printed pp. 6–7) for visibly MPDAs, with bounded acceptance. The language `L_bh` is the
`2`-hole-bounded language of a finite visibly MPDA, which also recognizes exactly `L_bh`; and for
every `K`, no visibly MPDA, finite or not, has `L_bh` as its `K`-scope-, `K`-context- or
`K`-round-bounded language. The source states the separation for the visible operation sequence;
whether it holds when stack operations are hidden is open (cslib-frontier issue #6712). -/
theorem language_separates_holeBounded_scopeBounded :
    (∃ (State Sym : Type) (_ : Finite State) (_ : Finite Sym) (M : MPDA 2 State Letter Sym),
      M.IsVisibly kind ∧ Acceptor.language M = language ∧
        M.boundedLanguage (HoleBounded 2) = language) ∧
    ∀ (K : ℕ) {State Γ : Type*} (M : MPDA 2 State Letter Γ), M.IsVisibly kind →
      M.boundedLanguage (ScopeBounded K) ≠ language ∧
        M.boundedLanguage (ContextBounded K) ≠ language ∧
        M.boundedLanguage (RoundBounded K) ≠ language := by
  refine ⟨⟨State, Sym, inferInstance, inferInstance, automaton, automaton_isVisibly,
    language_automaton, Set.ext fun w => ⟨fun ⟨s, hs, s', hs', μs, hμs, h, _⟩ =>
      language_automaton ▸ ⟨s, hs, s', hs', μs, hμs, h⟩, fun hw => ?_⟩⟩, ?_⟩
  · obtain ⟨s, hs, s', hs', μs, rfl, h⟩ := accepts_of_mem_language hw
    exact ⟨s, hs, s', hs', μs, rfl, h, holeBounded_two automaton_isVisibly h hw⟩
  · intro K State Γ M hM
    -- No run on `word (K + 1) ∈ L_bh` is `K'`-scope-bounded for `K' < 2 * (K + 1)`.
    have hnot : ∀ (K' : ℕ), K' < 2 * (K + 1) → ∀ (P : List (Letter × Op 2 Γ) → Prop),
        (∀ μs, P μs → ScopeBounded K' μs) → M.boundedLanguage P ≠ language := by
      intro K' hK' P hP heq
      have hw : word (K + 1) ∈ M.boundedLanguage P := heq ▸ word_mem_language (K + 1)
      obtain ⟨s, hs, s', hs', μs, hμs, h, hb⟩ := hw
      exact not_scopeBounded hM h hμs hK' (hP μs hb)
    exact ⟨hnot K (by omega) _ fun _ h => h, hnot K (by omega) _ fun _ h => h.scopeBounded,
      hnot (K * 2) (by omega) _ fun _ h => h.contextBounded.scopeBounded⟩

end Cslib.Automata.MPDA.HoleSeparation
