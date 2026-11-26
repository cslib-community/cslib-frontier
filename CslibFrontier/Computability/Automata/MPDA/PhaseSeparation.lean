/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.SeparationAutomaton
import CslibFrontier.Foundations.Data.List.Extract
import CslibFrontier.Foundations.Data.List.Flatten
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Hole-bounded and phase-bounded languages are incomparable

The last sentence of Proposition 2 of [AkshayGastinKrishnaRoychowdhury2020] states that there is a
language accepted by phase-bounded MPDAs but not by hole-bounded ones, and vice versa. The
witnesses are visibly pushdown languages over `a`, `b`, `c`, `d`, where `a` and `b` push on stacks
`0` and `1` and `c` and `d` pop from them:

- `L_bh` (`MPDA.HoleSeparation.language`) is `2`-hole-bounded (`holeBounded_two`), but its words
  `aᵐ bᵐ (c d)ᵐ` alternate `2 * m` pops between the two stacks, so they need `2 * m` phases.
- `L' = {(a b)ⁿ cⁿ dⁿ}` (`MPDA.HoleSeparation.phaseLanguage`) is `2`-phase-bounded, but after
  `(a b)ⁿ` each of the `n` pending `a`s is the first pending push of its own hole.

As in `MPDA.HoleSeparation`, the statements are for MPDAs that read the letters visibly, and the
separation of languages uses bounded acceptance (`MPDA.boundedLanguage`). A finite visibly MPDA
`MPDA.HoleSeparation.phaseAutomaton` recognizes exactly `L'`.

## Main definitions

- `MPDA.HoleSeparation.phaseLanguage`: the language `L'`.
- `MPDA.HoleSeparation.phaseAutomaton`: a finite visibly MPDA recognizing `L'`.

## Main results

- `MPDA.HoleSeparation.not_phaseBounded`: runs on `aᵐ bᵐ (c d)ᵐ ∈ L_bh` are not `K`-phase-bounded
  for `K < 2 * m`.
- `MPDA.HoleSeparation.phaseBounded_two`: runs on words of `L'` are `2`-phase-bounded.
- `MPDA.HoleSeparation.not_holeBounded`: runs on `(a b)ⁿ cⁿ dⁿ ∈ L'` are not `K`-hole-bounded for
  `K < n`.
- `MPDA.HoleSeparation.language_phaseAutomaton`: `phaseAutomaton` recognizes exactly `L'`.
- `MPDA.HoleSeparation.holeBounded_incomparable_phaseBounded`: `L'` is the `2`-phase-bounded but
  no `K`-hole-bounded language of a visibly MPDA, and `L_bh` the `2`-hole-bounded but no
  `K`-phase-bounded one.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Γ α : Type*}

/-- A factor containing pops from two different stacks is not a phase. -/
private theorem not_isPhase_extract {w : List (α × Op n Γ)} {a b s₁ s₂ : ℕ} {μ₁ μ₂ : α × Op n Γ}
    {i j : Fin n} {γ₁ γ₂ : Γ} (hij : i ≠ j) (h₁ : a ≤ s₁ ∧ s₁ < b) (h₂ : a ≤ s₂ ∧ s₂ < b)
    (hμ₁ : w[s₁]? = some μ₁) (hμ₂ : w[s₂]? = some μ₂) (hp₁ : μ₁.2 = .pop i γ₁)
    (hp₂ : μ₂.2 = .pop j γ₂) : ¬IsPhase (w.extract a b) := fun h =>
  hij (h μ₁ (List.mem_extract_iff_getElem?.mpr ⟨s₁, h₁.1, h₁.2, hμ₁⟩)
    μ₂ (List.mem_extract_iff_getElem?.mpr ⟨s₂, h₂.1, h₂.2, hμ₂⟩) i j γ₁ γ₂ hp₁ hp₂)

namespace HoleSeparation

variable {M : MPDA 2 State Letter Γ}

/-! ## `L_bh` is not phase-bounded -/

/-- **`L_bh` is not phase-bounded**: a run of a visibly MPDA on `aᵐ bᵐ (c d)ᵐ` is not
`K`-phase-bounded for `K < 2 * m`, since its `2 * m` pops alternate between the two stacks. This is
the claim "`L_bh` is not k-phase bounded" in the proof of Proposition 2 of
[AkshayGastinKrishnaRoychowdhury2020] (arXiv:2002.05950v2, printed p. 7). -/
theorem not_phaseBounded (hM : M.IsVisibly kind) {c c' : Config 2 State Γ}
    {w : List (Letter × Op 2 Γ)} (h : M.configLTS.MTr c w c') {m : ℕ}
    (hw : w.map Prod.fst = word m) {K : ℕ} (hK : K < 2 * m) : ¬PhaseBounded K w := by
  intro hs
  have hkind := hM.kind_eq h
  have hlen : w.length = 4 * m := by rw [← List.length_map (f := Prod.fst), hw]; simp [word]; omega
  -- The `j`-th pop pops from stack `j % 2`.
  have hpop : ∀ j < 2 * m, ∃ μ γ, w[2 * m + j]? = some μ ∧
      μ.2 = .pop (⟨j % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) γ := by
    intro j hj
    have hletter : (w.map Prod.fst)[2 * m + j]? = some (if j % 2 = 0 then .c else .d) := by
      rw [hw, word, List.getElem?_append_right (by simp; omega), List.getElem?_flatten_replicate]
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, show 2 * m + j - (m + m) = j by omega,
        show j < m * (0 + 1 + 1) by omega, ↓reduceIte]
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;> simp [hj2]
    rw [List.getElem?_map] at hletter
    obtain ⟨μ, hμ, hμ1⟩ := Option.map_eq_some_iff.mp hletter
    have hk := hkind μ (List.mem_of_getElem? hμ)
    rw [hμ1] at hk
    obtain ⟨γ, hγ⟩ : ∃ γ, μ.2 = .pop (⟨j % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) γ := by
      refine Op.kind_eq_pop.mp (hk.trans ?_)
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;> simp [hj2, kind]
    exact ⟨μ, γ, hμ, hγ⟩
  have hcard := List.Splits.card_le (fun _ _ huv hv => IsPhase.of_isInfix huv hv) hs
    ((Finset.range (2 * m)).image (2 * m + ·))
    (by simp only [Finset.forall_mem_image, Finset.mem_range]; intros; omega) (by
      simp only [Finset.forall_mem_image, Finset.mem_range]
      intro j hj j' hj' htt'
      obtain ⟨μ₁, γ₁, hμ₁, hp₁⟩ := hpop j hj
      obtain ⟨μ₂, γ₂, hμ₂, hp₂⟩ := hpop (j + 1) (by omega)
      exact not_isPhase_extract (s₂ := 2 * m + (j + 1)) (by simp [Fin.ext_iff]; omega)
        ⟨le_rfl, by omega⟩ ⟨by omega, by omega⟩ hμ₁ hμ₂ hp₁ hp₂)
  rw [Finset.card_image_of_injective _ (add_right_injective _), Finset.card_range] at hcard
  omega

/-! ## The language `L'` -/

/-- The word `(a b)ⁿ cⁿ dⁿ`. -/
@[expose] def phaseWord (n : ℕ) : List Letter :=
  (List.replicate n [.a, .b]).flatten ++ List.replicate n .c ++ List.replicate n .d

/-- The language `L' = {(a b)ⁿ cⁿ dⁿ}` of [AkshayGastinKrishnaRoychowdhury2020]. -/
@[expose] def phaseLanguage : Language Letter := {w | ∃ n, w = phaseWord n}

/-- The letters of `(a b)ⁿ cⁿ dⁿ` by position. -/
private theorem getElem?_phaseWord (n t : ℕ) :
    (phaseWord n)[t]? =
      if t < 2 * n then some (if t % 2 = 0 then .a else .b)
      else if t < 3 * n then some .c else if t < 4 * n then some .d else none := by
  have hab : (List.replicate n [Letter.a, .b]).flatten.length = 2 * n := by simp; omega
  rw [phaseWord]
  by_cases h₁ : t < 2 * n
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_flatten_replicate]
    simp only [List.length_cons, List.length_nil, show t < n * (0 + 1 + 1) by omega, ↓reduceIte,
      h₁]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]
  by_cases h₂ : t < 3 * n
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hab,
      List.getElem?_replicate]
    simp only [h₁, h₂, show t - 2 * n < n by omega, ↓reduceIte]
  · rw [List.getElem?_append_right (by simp; omega), List.length_append, hab,
      List.length_replicate, List.getElem?_replicate]
    simp only [h₁, h₂, show t - (2 * n + n) < n ↔ t < 4 * n by omega, ↓reduceIte]

/-- The positions of the letters of `(a b)ⁿ cⁿ dⁿ`. -/
private theorem phaseWord_cases {n t : ℕ} {x : Letter} (h : (phaseWord n)[t]? = some x) :
    (t < 2 * n ∧ x = if t % 2 = 0 then .a else .b) ∨ (2 * n ≤ t ∧ t < 3 * n ∧ x = .c) ∨
      (3 * n ≤ t ∧ t < 4 * n ∧ x = .d) := by
  rw [getElem?_phaseWord] at h
  if h₁ : t < 2 * n then exact .inl ⟨h₁, by simpa [h₁] using h.symm⟩
  else if h₂ : t < 3 * n then exact .inr (.inl ⟨by omega, h₂, by simpa [h₁, h₂] using h.symm⟩)
  else if h₃ : t < 4 * n then exact .inr (.inr ⟨by omega, h₃, by simpa [h₁, h₂, h₃] using h.symm⟩)
  else simp [h₁, h₂, h₃] at h

/-- **`L'` is `2`-phase-bounded**: every run of a visibly MPDA on a word of `L'` splits into the
phase `(a b)ⁿ cⁿ`, which pops only from stack `0`, and the phase `dⁿ`. This is the claim "`L'` is
2-phase bounded" in the proof of Proposition 2 of [AkshayGastinKrishnaRoychowdhury2020]
(arXiv:2002.05950v2, printed p. 7). -/
theorem phaseBounded_two (hM : M.IsVisibly kind) {c c' : Config 2 State Γ}
    {w : List (Letter × Op 2 Γ)} (h : M.configLTS.MTr c w c')
    (hw : w.map Prod.fst ∈ phaseLanguage) : PhaseBounded 2 w := by
  obtain ⟨n, hn⟩ := hw
  have hkind := hM.kind_eq h
  rw [phaseWord] at hn
  obtain ⟨w₁, w₂, rfl, hw₁, hw₂⟩ := List.map_eq_append_iff.mp hn
  refine ⟨[w₁, w₂], by simp, by simp, ?_⟩
  -- Each part pops from one stack.
  have hphase : ∀ (u : List (Letter × Op 2 Γ)) (o : Fin 2), (∀ μ ∈ u, μ.2.kind = kind μ.1) →
      (∀ x ∈ u.map Prod.fst, ∀ i, kind x = .pop i → i = o) → IsPhase u := by
    intro u o hu hx
    have hpop : ∀ μ ∈ u, ∀ i γ, μ.2 = .pop i γ → i = o := fun μ hμ i γ hpop =>
      hx μ.1 (List.mem_map_of_mem hμ) i (by rw [← hu μ hμ, hpop]; rfl)
    exact fun μ hμ ν hν i j γ δ hμp hνp => (hpop μ hμ i γ hμp).trans (hpop ν hν j δ hνp).symm
  simp only [List.forall_mem_cons]
  refine ⟨hphase _ 0 (fun μ hμ => hkind μ (by simp [hμ])) fun x hx i hi => ?_,
    hphase _ 1 (fun μ hμ => hkind μ (by simp [hμ])) fun x hx i hi => ?_, nofun⟩
  · rw [hw₁] at hx
    simp only [List.mem_append, List.mem_flatten, List.mem_replicate] at hx
    rcases hx with ⟨l, ⟨-, rfl⟩, hl⟩ | ⟨-, rfl⟩
    · rcases (by simpa using hl : x = .a ∨ x = .b) with rfl | rfl <;> simp_all [kind]
    · simp_all [kind]
  · simpa [kind, (List.mem_replicate.mp (hw₂ ▸ hx)).2] using hi.symm

/-! ## `L'` is not hole-bounded -/

section NotHoleBounded

variable {w : List (Letter × Op 2 Γ)} {n : ℕ}

/-- On a factor of letters `a` and `b` only, no stack height decreases, and the height of stack
`1` increases if the factor contains a `b`. -/
private theorem net_of_ab {u : List (Letter × Op 2 Γ)} (hk : ∀ μ ∈ u, μ.2.kind = kind μ.1)
    (hab : ∀ μ ∈ u, μ.1 = .a ∨ μ.1 = .b) :
    (∀ i, 0 ≤ net i u) ∧ ((∃ μ ∈ u, μ.1 = .b) → 1 ≤ net 1 u) := by
  have hterm : ∀ i, ∀ x ∈ (u.map Prod.fst).map fun l => (kind l).net i, 0 ≤ x := by
    intro i x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hl
    rcases hab μ hμ with h | h <;> rw [h] <;> simp only [kind, OpKind.net] <;> split_ifs <;>
      simp
  refine ⟨fun i => net_eq_of_kind hk i ▸ List.sum_nonneg (hterm i), fun ⟨μ, hμ, hb⟩ => ?_⟩
  rw [net_eq_of_kind hk]
  refine le_trans ?_ (List.single_le_sum (hterm 1) _ (List.mem_map.mpr
    ⟨μ.1, List.mem_map_of_mem hμ, rfl⟩))
  rw [hb]
  simp [kind, OpKind.net]

/-- Positions before `2 * n` carry `a` or `b`. -/
private theorem ab_of_lt (hw : w.map Prod.fst = phaseWord n) {a b : ℕ} (hb : b ≤ 2 * n) :
    ∀ μ ∈ w.extract a b, μ.1 = .a ∨ μ.1 = .b := by
  intro μ hμ
  obtain ⟨t, -, htb, ht⟩ := List.mem_extract_iff_getElem?.mp hμ
  have hl : (phaseWord n)[t]? = some μ.1 := by rw [← hw, List.getElem?_map, ht]; rfl
  rcases phaseWord_cases hl with ⟨-, h⟩ | ⟨h₁, -, -⟩ | ⟨h₁, -, -⟩ <;>
    [(split_ifs at h <;> simp [h]); omega; omega]

/-- **`L'` is not hole-bounded**: a run of a visibly MPDA on `(a b)ⁿ cⁿ dⁿ` is not `K`-hole-bounded
for `K < n`. After `(a b)ⁿ`, each pending `a` is a hole push, since the `b` after it stays pending
until after its matching `c`, and two pending `a`s never belong to the same hole, since a `b`
separates them. This is the claim "`L'` is not hole-bounded" in the proof of Proposition 2 of
[AkshayGastinKrishnaRoychowdhury2020] (arXiv:2002.05950v2, printed p. 7). -/
theorem not_holeBounded (hM : M.IsVisibly kind) {c c' : Config 2 State Γ}
    (h : M.configLTS.MTr c w c') (hw : w.map Prod.fst = phaseWord n) {K : ℕ} (hK : K < n) :
    ¬HoleBounded K w := by
  intro hb
  have hkind := hM.kind_eq h
  have hlen : w.length = 4 * n := by
    rw [← List.length_map (f := Prod.fst), hw, phaseWord]; simp; omega
  have hlet : ∀ {t : ℕ} {μ : Letter × Op 2 Γ}, w[t]? = some μ → (phaseWord n)[t]? = some μ.1 :=
    fun ht => by rw [← hw, List.getElem?_map, ht]; rfl
  have hkext : ∀ a b, ∀ μ ∈ w.extract a b, μ.2.kind = kind μ.1 := fun a b μ hμ =>
    hkind μ ((List.extract_isInfix w a b).subset hμ)
  have hlt {t} {μ : Letter × Op 2 Γ} (ht : t < 2 * n) (hμ : w[t]? = some μ) :
      μ.1 = if t % 2 = 0 then .a else .b := by
    rcases phaseWord_cases (hlet hμ) with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [exact h; omega; omega]
  -- The entry at a position, with its letter.
  have hentry : ∀ t < 4 * n, ∃ μ, w[t]? = some μ ∧ (phaseWord n)[t]? = some μ.1 := fun t ht =>
    ⟨w[t]'(by omega), List.getElem?_eq_getElem _, hlet (List.getElem?_eq_getElem _)⟩
  -- Every position `2 * i` with `i < n` is the first pending push of a hole after `(a b)ⁿ`.
  have hmem : ∀ i < n, OpenHolePush w (2 * n - 1) (2 * i) ∧
      ¬∃ p, SameHole w (2 * n - 1) p (2 * i) := by
    intro i hi
    obtain ⟨μ, hμ, -⟩ := hentry (2 * i) (by omega)
    have hμa : μ.1 = .a := by
      simpa [show 2 * i % 2 = 0 by omega] using hlt (by omega) hμ
    obtain ⟨γ, hγ⟩ := Op.kind_eq_push.mp ((hkind μ (List.mem_of_getElem? hμ)).trans
      (by rw [hμa]; rfl))
    have hpush : w[2 * i]? = some (μ.1, .push 0 γ) := by rw [hμ, ← hγ]
    -- The `b` right after it.
    obtain ⟨ν, hν, -⟩ := hentry (2 * i + 1) (by omega)
    have hνb : ν.1 = .b := by
      simpa [show (2 * i + 1) % 2 = 1 by omega] using hlt (by omega) hν
    have hpend : PendingAt w (2 * i) (2 * n - 1) := by
      refine ⟨by omega, by omega, 0, ⟨μ.1, γ, hpush⟩, fun k => ?_⟩
      refine (net_of_ab (fun μ hμ => hkext _ _ μ (List.mem_of_mem_take hμ))
        (fun μ hμ => ab_of_lt hw (by omega) μ (List.mem_of_mem_take hμ))).1 0
    refine ⟨⟨⟨⟨0, μ.1, γ, hpush⟩, ?_⟩, hpend⟩, ?_⟩
    · -- The `b` after the push stays pending until after the matching pop.
      rintro ⟨m, hm, hwn⟩
      obtain ⟨-, j, ⟨a', γ', hj⟩, ⟨b', δ, hmpop⟩, -, -⟩ := hm
      simp only [hpush, Option.some.injEq, Prod.mk.injEq, Op.push.injEq] at hj
      obtain ⟨-, rfl, -⟩ := hj
      have hm := hlet hmpop
      have hmk := hkind _ (List.mem_of_getElem? hmpop)
      simp only [Op.kind] at hmk
      have hm2 : 2 * n ≤ m ∧ m < 3 * n := by
        rcases phaseWord_cases hm with ⟨-, h⟩ | ⟨h₁, h₂, -⟩ | ⟨-, -, h⟩
        · split_ifs at h <;> subst h <;> simp [kind] at hmk
        · exact ⟨h₁, h₂⟩
        · subst h; simp [kind] at hmk
      have hnet := hwn.net_eq_zero 1
      rw [← w.extract_append_extract (show 2 * i ≤ 2 * n by omega) (show 2 * n ≤ m + 1 by omega),
        net_append] at hnet
      have h₁ := (net_of_ab (u := w.extract (2 * i) (2 * n)) (hkext _ _) (ab_of_lt hw le_rfl)).2
        ⟨ν, List.mem_extract_iff_getElem?.mpr ⟨_, by omega, by omega, hν⟩, hνb⟩
      -- The factor from `2 * n` to `m` carries only `c`s, which do not touch stack `1`.
      have h₂ : net 1 (w.extract (2 * n) (m + 1)) = 0 := by
        rw [net_eq_of_kind (hkext _ _)]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
        obtain ⟨μ', hμ', rfl⟩ := List.mem_map.mp hl
        obtain ⟨t, ht₁, ht₂, ht⟩ := List.mem_extract_iff_getElem?.mp hμ'
        rcases phaseWord_cases (hlet ht) with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ <;>
          [omega; simp [h, kind, OpKind.net]; omega]
      omega
    · -- A `b` separates any earlier pending `a` from this one.
      rintro ⟨p, hpq, -, -, ⟨j, ⟨a₁, γ₁, hp⟩, ⟨a₂, γ₂, hq⟩⟩, hwn⟩
      simp only [hpush, Option.some.injEq, Prod.mk.injEq, Op.push.injEq] at hq
      obtain ⟨-, rfl, -⟩ := hq
      have hpl := hlet hp
      have hpk := hkind _ (List.mem_of_getElem? hp)
      have hp2 : p % 2 = 0 := by
        by_contra hodd
        rcases phaseWord_cases hpl with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
          simp_all [kind, Op.kind]
      obtain ⟨ν', hν', -⟩ := hentry (2 * i - 1) (by omega)
      have hν'b : ν'.1 = .b := by
        simpa [show (2 * i - 1) % 2 = 1 by omega] using hlt (by omega) hν'
      have hν'mem : ν' ∈ w.extract (p + 1) (2 * i) :=
        List.mem_extract_iff_getElem?.mpr ⟨_, by omega, by omega, hν'⟩
      have h₁ := (net_of_ab (u := w.extract (p + 1) (2 * i)) (hkext _ _)
        (ab_of_lt hw (by omega))).2 ⟨ν', hν'mem, hν'b⟩
      have := hwn.net_eq_zero 1
      omega
  -- So at least `n` holes are open after `(a b)ⁿ`.
  have hsubset : ((Finset.range n).image (2 * ·) : Set ℕ) ⊆
      {q | OpenHolePush w (2 * n - 1) q ∧ ¬∃ p, SameHole w (2 * n - 1) p q} := by
    rw [Finset.coe_image, Set.image_subset_iff]
    exact fun i hi => hmem i (Finset.mem_range.mp hi)
  have hfin : {q | OpenHolePush w (2 * n - 1) q ∧ ¬∃ p, SameHole w (2 * n - 1) p q}.Finite :=
    (Set.finite_le_nat (2 * n - 1)).subset fun q hq => hq.1.2.1
  have := Set.ncard_le_ncard hsubset hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (mul_right_injective₀ two_ne_zero),
    Finset.card_range] at this
  have := hb (2 * n - 1) (by omega)
  unfold openHoles at this
  omega

end NotHoleBounded

/-! ## An automaton recognizing `L'` -/

/-- Control states of `phaseAutomaton`: reading `(a b)ⁿ` before an `a` (`x`) or before a `b`
(`y`), reading `cⁿ` (`cs`), and reading `dⁿ` (`ds`). -/
inductive PhaseState where
  | x | y | cs | ds
  deriving DecidableEq

instance : Finite PhaseState :=
  Finite.of_injective (β := Fin 4) (fun | .x => 0 | .y => 1 | .cs => 2 | .ds => 3)
    (by intro p q h; cases p <;> cases q <;> simp_all)

/-- The transitions of `phaseAutomaton`. -/
inductive PhaseStep : PhaseState → Letter × Op 2 Unit → PhaseState → Prop where
  | x_a : PhaseStep .x (.a, .push 0 ()) .y
  | y_b : PhaseStep .y (.b, .push 1 ()) .x
  | x_c : PhaseStep .x (.c, .pop 0 ()) .cs
  | cs_c : PhaseStep .cs (.c, .pop 0 ()) .cs
  | cs_d : PhaseStep .cs (.d, .pop 1 ()) .ds
  | ds_d : PhaseStep .ds (.d, .pop 1 ()) .ds

/-- A visibly MPDA recognizing `L'`: the `a`s and `b`s push, and the `c`s and `d`s pop them. -/
@[expose] def phaseAutomaton : MPDA 2 PhaseState Letter Unit where
  Tr := PhaseStep
  start := {.x}
  accept := {.x, .ds}

theorem phaseAutomaton_isVisibly : phaseAutomaton.IsVisibly kind := by
  intro s l op s' h
  cases h <;> rfl

private theorem phaseStep_iff {q q' : PhaseState} {μ : Letter × Op 2 Unit} {s₀ s₁ : List Unit}
    {σ : Stacks 2 Unit} :
    phaseAutomaton.configLTS.Tr ⟨q, Stacks.pair s₀ s₁⟩ μ ⟨q', σ⟩ ↔
      PhaseStep q μ q' ∧ μ.2.Apply (Stacks.pair s₀ s₁) σ :=
  configLTS_tr

/-- The reachable configurations of `phaseAutomaton`: the input read so far and the stack
heights. -/
private def PhaseInv : PhaseState → List Unit → List Unit → List Letter → Prop
  | .x, s₀, s₁, u => ∃ k, u = (List.replicate k [Letter.a, .b]).flatten ∧ s₀.length = k ∧
      s₁.length = k
  | .y, s₀, s₁, u => ∃ k, u = (List.replicate k [Letter.a, .b]).flatten ++ [.a] ∧
      s₀.length = k + 1 ∧ s₁.length = k
  | .cs, s₀, s₁, u => ∃ k r, 1 ≤ r ∧ r ≤ k ∧
      u = (List.replicate k [Letter.a, .b]).flatten ++ List.replicate r .c ∧
      s₀.length = k - r ∧ s₁.length = k
  | .ds, s₀, s₁, u => ∃ k r t, r ≤ k ∧ 1 ≤ t ∧ t ≤ k ∧
      u = (List.replicate k [Letter.a, .b]).flatten ++ List.replicate r .c ++
        List.replicate t .d ∧ s₀.length = k - r ∧ s₁.length = k - t

private theorem phaseInv_step {q q' : PhaseState} {s₀ s₁ : List Unit} {u : List Letter}
    {μ : Letter × Op 2 Unit} {σ : Stacks 2 Unit} (hinv : PhaseInv q s₀ s₁ u)
    (h : phaseAutomaton.configLTS.Tr ⟨q, Stacks.pair s₀ s₁⟩ μ ⟨q', σ⟩) :
    ∃ t₀ t₁, σ = Stacks.pair t₀ t₁ ∧ PhaseInv q' t₀ t₁ (u ++ [μ.1]) := by
  obtain ⟨hstep, happ⟩ := phaseStep_iff.mp h
  cases hstep with
  | x_a =>
    obtain ⟨k, rfl, h₀, h₁⟩ := hinv
    exact ⟨_, _, Op.apply_push_zero_pair.mp happ, k, rfl, by simp [h₀], h₁⟩
  | y_b =>
    obtain ⟨k, rfl, h₀, h₁⟩ := hinv
    refine ⟨_, _, Op.apply_push_one_pair.mp happ, k + 1, ?_, h₀, by simp [h₁]⟩
    simp [List.replicate_succ', List.flatten_append]
  | x_c =>
    obtain ⟨k, rfl, h₀, h₁⟩ := hinv
    obtain ⟨t, rfl, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    simp only [List.length_cons] at h₀
    exact ⟨_, _, rfl, k, 1, le_rfl, by omega, by simp, by omega, h₁⟩
  | cs_c =>
    obtain ⟨k, r, hr, hrk, rfl, h₀, h₁⟩ := hinv
    obtain ⟨t, rfl, rfl⟩ := Op.apply_pop_zero_pair.mp happ
    simp only [List.length_cons] at h₀
    exact ⟨_, _, rfl, k, r + 1, by omega, by omega, by simp [List.replicate_succ'], by omega, h₁⟩
  | cs_d =>
    obtain ⟨k, r, hr, hrk, rfl, h₀, h₁⟩ := hinv
    obtain ⟨t, rfl, rfl⟩ := Op.apply_pop_one_pair.mp happ
    simp only [List.length_cons] at h₁
    exact ⟨_, _, rfl, k, r, 1, hrk, le_rfl, by omega, by simp, h₀, by omega⟩
  | ds_d =>
    obtain ⟨k, r, t', hrk, ht, htk, rfl, h₀, h₁⟩ := hinv
    obtain ⟨t, rfl, rfl⟩ := Op.apply_pop_one_pair.mp happ
    simp only [List.length_cons] at h₁
    exact ⟨_, _, rfl, k, r, t' + 1, hrk, by omega, by omega,
      by simp [List.replicate_succ', List.append_assoc], h₀, by omega⟩

private theorem mem_phaseLanguage_of_accepts {w : List Letter}
    (h : Acceptor.Accepts phaseAutomaton w) : w ∈ phaseLanguage := by
  obtain ⟨s, rfl, s', hs', μs, rfl, hrun⟩ := h
  rw [Stacks.empty_eq_pair] at hrun
  obtain ⟨s₀, s₁, hc, hinv⟩ :=
    exists_inv_pair_of_configLTS_mTr PhaseInv phaseInv_step hrun ⟨0, rfl, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := Stacks.eq_pair_iff.mp hc.symm
  rcases hs' with rfl | rfl
  · obtain ⟨k, hu, h₀, -⟩ := hinv
    exact ⟨0, by simp_all [phaseWord]⟩
  · obtain ⟨k, r, t, hrk, -, htk, hu, h₀, h₁⟩ := hinv
    obtain ⟨rfl, rfl⟩ : r = k ∧ t = r := by simp only [List.length_nil] at h₀ h₁; omega
    exact ⟨t, hu⟩

/-- Repeating `a b` from `x` pushes on both stacks. -/
private theorem phase_run_ab : ∀ (k : ℕ) (s₀ s₁ : List Unit),
    phaseAutomaton.configLTS.MTr ⟨.x, Stacks.pair s₀ s₁⟩
      (List.replicate k [(Letter.a, Op.push 0 ()), (.b, .push 1 ())]).flatten
      ⟨.x, Stacks.pair (List.replicate k () ++ s₀) (List.replicate k () ++ s₁)⟩
  | 0, _, _ => .refl
  | k + 1, s₀, s₁ => by
    rw [List.replicate_succ, List.flatten_cons]
    refine .stepL (phaseStep_iff.mpr ⟨.x_a, Op.apply_push_zero_pair.mpr rfl⟩)
      (.stepL (phaseStep_iff.mpr ⟨.y_b, Op.apply_push_one_pair.mpr rfl⟩) ?_)
    simpa [List.replicate_succ', List.append_assoc] using phase_run_ab k (() :: s₀) (() :: s₁)

private theorem accepts_of_mem_phaseLanguage {w : List Letter} (h : w ∈ phaseLanguage) :
    Acceptor.Accepts phaseAutomaton w := by
  obtain ⟨n, rfl⟩ := h
  have hab := phase_run_ab n [] []
  simp only [List.append_nil] at hab
  rcases n with _ | m
  · exact ⟨.x, rfl, .x, .inl rfl, [], by simp [phaseWord], .refl⟩
  -- Then `cᵐ⁺¹` and `dᵐ⁺¹`.
  have hcs := configLTS_mTr_replicate_pop_zero (M := phaseAutomaton) PhaseStep.cs_c
    (List.replicate (m + 1) ()) m []
  have hds := configLTS_mTr_replicate_pop_one (M := phaseAutomaton) PhaseStep.ds_d [] m []
  simp only [List.append_nil] at hcs hds
  refine ⟨.x, rfl, .ds, .inr rfl,
    (List.replicate (m + 1) [(Letter.a, Op.push 0 ()), (.b, .push 1 ())]).flatten ++
    ((Letter.c, Op.pop 0 ()) ::
    List.replicate m (.c, .pop 0 ())) ++ ((Letter.d, Op.pop 1 ()) :: List.replicate m
    (.d, .pop 1 ())), ?_, ?_⟩
  · simp [phaseWord, List.replicate_succ, List.append_assoc]
  · rw [Stacks.empty_eq_pair]
    exact (hab.comp _
      (.stepL (phaseStep_iff.mpr ⟨.x_c, Op.apply_pop_zero_pair.mpr ⟨_, rfl, rfl⟩⟩) hcs)).comp _
      (.stepL (phaseStep_iff.mpr ⟨.cs_d, Op.apply_pop_one_pair.mpr ⟨_, rfl, rfl⟩⟩) hds)

/-- `phaseAutomaton` recognizes exactly `L'`. -/
theorem language_phaseAutomaton : Acceptor.language phaseAutomaton = phaseLanguage :=
  Set.ext fun _ => ⟨mem_phaseLanguage_of_accepts, accepts_of_mem_phaseLanguage⟩

/-! ## The incomparability of languages -/

/-- **Hole-bounded and phase-bounded languages are incomparable**, the last sentence of
Proposition 2 of [AkshayGastinKrishnaRoychowdhury2020] (arXiv:2002.05950v2, Section 2.1, printed
pp. 6–7) for visibly MPDAs, with bounded acceptance (`MPDA.boundedLanguage`). The language `L'` is
the `2`-phase-bounded language of a finite visibly MPDA, which also recognizes exactly `L'`, but
for every `K` it is not the `K`-hole-bounded language of any visibly MPDA; and the language `L_bh`
is the `2`-hole-bounded language of a finite visibly MPDA
(`language_separates_holeBounded_scopeBounded`), but for every `K` it is not the `K`-phase-bounded
language of any visibly MPDA. So neither class of languages contains the other. -/
theorem holeBounded_incomparable_phaseBounded.{u₁, u₂, u₃, u₄} :
    ((∃ (State Sym : Type) (_ : Finite State) (_ : Finite Sym) (M : MPDA 2 State Letter Sym),
      M.IsVisibly kind ∧ Acceptor.language M = phaseLanguage ∧
        M.boundedLanguage (PhaseBounded 2) = phaseLanguage) ∧
      ∀ (K : ℕ) {State : Type u₁} {Γ : Type u₂} (M : MPDA 2 State Letter Γ), M.IsVisibly kind →
        M.boundedLanguage (HoleBounded K) ≠ phaseLanguage) ∧
    ((∃ (State Sym : Type) (_ : Finite State) (_ : Finite Sym) (M : MPDA 2 State Letter Sym),
      M.IsVisibly kind ∧ Acceptor.language M = language ∧
        M.boundedLanguage (HoleBounded 2) = language) ∧
      ∀ (K : ℕ) {State : Type u₃} {Γ : Type u₄} (M : MPDA 2 State Letter Γ), M.IsVisibly kind →
        M.boundedLanguage (PhaseBounded K) ≠ language) := by
  refine ⟨⟨⟨PhaseState, Unit, inferInstance, inferInstance, phaseAutomaton,
    phaseAutomaton_isVisibly, language_phaseAutomaton, Set.ext fun w =>
      ⟨fun ⟨s, hs, s', hs', μs, hμs, h, _⟩ =>
        language_phaseAutomaton ▸ ⟨s, hs, s', hs', μs, hμs, h⟩,
        fun hw => ?_⟩⟩, ?_⟩, language_separates_holeBounded_scopeBounded.{0, 0}.1, ?_⟩
  · obtain ⟨s, hs, s', hs', μs, rfl, h⟩ := accepts_of_mem_phaseLanguage hw
    exact ⟨s, hs, s', hs', μs, rfl, h, phaseBounded_two phaseAutomaton_isVisibly h hw⟩
  · intro K State Γ M hM heq
    have hmem : phaseWord (K + 1) ∈ M.boundedLanguage (HoleBounded K) := heq ▸ ⟨K + 1, rfl⟩
    obtain ⟨s, hs, s', hs', μs, hμs, h, hb⟩ := hmem
    exact not_holeBounded hM h hμs (by omega) hb
  · intro K State Γ M hM heq
    obtain ⟨s, hs, s', hs', μs, hμs, h, hb⟩ := heq ▸ word_mem_language (K + 1)
    exact not_phaseBounded hM h hμs (by omega) hb

end HoleSeparation

end Cslib.Automata.MPDA
