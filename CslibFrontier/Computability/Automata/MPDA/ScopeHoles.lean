/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Automata.MPDA.OneHole
import CslibFrontier.Foundations.Data.List.Extract
public import CslibFrontier.Computability.Automata.MPDA.Underapprox
import Mathlib.Data.Finset.Max

/-! # Scope-bounded runs are hole-bounded

The first sentence of Proposition 2 in Section 2.1 of [AkshayGastinKrishnaRoychowdhury2020] says
that the accepted runs bounded by `K` in rounds, contexts or scope are `K'`-hole-bounded for some
`K' ≤ K`. For scope and contexts we prove this with `K' = K`; for rounds we prove it with
`K' = K * n`.

At a position `x`, take the first pending push of each open hole, and the pop matching the earliest
of them, which comes after `x`. No two of these positions lie in a common context:

- two first pending pushes of open holes on the same stack in one context would belong to the
  same hole, since the factor between the last open hole push before the second one and the second
  one is then well-nested;
- a hole push and the matching pop of an earlier push in one context would be closed inside that
  context, so it would not be a hole push.

The factor from the earliest push to its pop has at most `K + 1` contexts, so there are at most
`K` open holes at `x`.

## Main results

- `MPDA.ScopeBounded.holeBounded`: complete `K`-scope-bounded runs are `K`-hole-bounded.
- `MPDA.RoundBounded.holeBounded`: complete runs with at most `K` rounds are
  `K * n`-hole-bounded.

## Implementation notes

The statements are about complete runs, from empty stacks to empty stacks, as are the accepting
runs of the source. Without this, pushes that are never popped could open unboundedly many holes
in a sequence that is trivially scope-bounded.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α β State : Type*}

/-! ## Factors and runs -/

private theorem exists_configLTS_mTr_extract {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {w : List (α × Op n Γ)} (h : M.configLTS.MTr c w c') (a b : ℕ) :
    ∃ c₁ c₂, M.configLTS.MTr c₁ (w.extract a b) c₂ := by
  rw [← List.take_append_drop a w] at h
  obtain ⟨c₁, -, h₁⟩ := LTS.MTr.split h
  rw [← List.take_append_drop (b - a) (w.drop a)] at h₁
  obtain ⟨c₂, h₂, -⟩ := LTS.MTr.split h₁
  exact ⟨c₁, c₂, by rwa [List.extract_eq_take_drop]⟩

private theorem net_take_append_nonneg {i : Fin n} {u v : List (α × Op n Γ)}
    (hu : ∀ k, 0 ≤ net i (u.take k)) (hv : ∀ k, 0 ≤ net i (v.take k)) (k : ℕ) :
    0 ≤ net i ((u ++ v).take k) := by
  rw [List.take_append, net_append]
  exact add_nonneg (hu k) (hv _)

/-! ## Single contexts -/

private theorem IsContext.isContextOf {v : List (α × Op n Γ)} (h : IsContext v)
    {μ : α × Op n Γ} (hμ : μ ∈ v) {i : Fin n} (hi : μ.2.stack = some i) : IsContextOf i v := by
  obtain ⟨o, ho⟩ := h
  rcases ho μ hμ with h' | h' <;> rw [hi] at h' <;> cases h'
  exact ho

private theorem net_eq_zero_of_isContextOf {i j : Fin n} (hij : i ≠ j) :
    ∀ {u : List (α × Op n Γ)}, IsContextOf i u → net j u = 0
  | [], _ => rfl
  | (a, op) :: u, h => by
    rw [net_cons, net_eq_zero_of_isContextOf hij fun μ hμ => h μ (List.mem_cons_of_mem _ hμ)]
    rcases h (a, op) List.mem_cons_self with h' | h' <;> cases op <;>
      simp_all [Op.stack, Op.net]

/-- A run that uses one stack, never goes below the initial height of that stack and returns to
it is well-nested. -/
private theorem wellNested_of_isContextOf {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {v : List (α × Op n Γ)} (hrun : M.configLTS.MTr c v c') {i : Fin n} (hv : IsContextOf i v)
    (hnet : net i v = 0) (hk : ∀ k, 0 ≤ net i (v.take k)) : WellNested v := by
  refine wellNested_of_not_crossing hrun (fun j => ?_) ?_
  · by_cases hij : i = j
    · subst hij
      exact ⟨hnet, hk⟩
    · exact ⟨net_eq_zero_of_isContextOf hij hv, fun k =>
        (net_eq_zero_of_isContextOf hij fun μ hμ => hv μ (List.mem_of_mem_take hμ)).symm.le⟩
  · rintro ⟨i', j', p, q, z, hij, -, -, ⟨a, γ, hp⟩, ⟨b, δ, hq⟩, -, -⟩
    have h₁ : i' = i := by simpa [Op.stack] using hv _ (List.mem_of_getElem? hp)
    have h₂ : j' = i := by simpa [Op.stack] using hv _ (List.mem_of_getElem? hq)
    exact hij (h₁.trans h₂.symm)

private theorem IsContextOf.eq_of_isPushOn {w : List (α × Op n Γ)} {i j : Fin n} {a b q : ℕ}
    (hctx : IsContextOf i (w.extract a b)) (haq : a ≤ q) (hqb : q < b) (hj : IsPushOn w j q) :
    j = i := by
  obtain ⟨a', γ, hj'⟩ := hj
  simpa [Op.stack] using hctx _ (List.mem_extract_iff_getElem?.mpr ⟨q, haq, hqb, hj'⟩)

/-- A push matched inside a single context is closed by a well-nested continuation. -/
private theorem wellMatched_of_isContextOf {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {w : List (α × Op n Γ)} (hrun : M.configLTS.MTr c w c') {i : Fin n} {p m : ℕ}
    (hm : Matches w p m) (hp : IsPushOn w i p) (hctx : IsContextOf i (w.extract p (m + 1))) :
    WellMatched w p := by
  refine ⟨m, hm, ?_⟩
  obtain ⟨hpm, ⟨b, δ, hmpop⟩, hk, hnet⟩ := hm.of_isPushOn hp
  obtain ⟨a, γ, hppush⟩ := hp
  obtain ⟨c₁, c₂, hrun'⟩ := exists_configLTS_mTr_extract hrun p (m + 1)
  have e : w.extract p (m + 1) =
      (a, Op.push i γ) :: (w.extract (p + 1) m ++ [(b, .pop i δ)]) := by
    rw [← w.extract_append_extract (Nat.le_succ p) (show p + 1 ≤ m + 1 by omega),
      ← w.extract_append_extract (show p + 1 ≤ m by omega) (Nat.le_succ m),
      List.extract_eq_singleton hppush, List.extract_eq_singleton hmpop]
    rfl
  refine wellNested_of_isContextOf hrun' hctx ?_ fun k => ?_
  · rw [e, net_cons, net_append, hnet, net_cons, net_nil]
    simp [Op.net]
  · rw [e]
    rcases k with _ | k
    · simp
    · rw [List.take_succ_cons, net_cons, List.take_append, net_append]
      have h₁ := hk k
      rcases Nat.eq_zero_or_pos (k - (w.extract (p + 1) m).length) with h | h
      · rw [h, List.take_zero, net_nil]
        simp only [Op.net, Op.kind, OpKind.net, ↓reduceIte]
        omega
      · rw [List.take_of_length_le (l := w.extract (p + 1) m) (by omega),
          List.take_of_length_le (l := [(b, Op.pop i δ)]) (by rw [List.length_singleton]; omega),
          hnet]
        simp [Op.net]

/-! ## Matches -/

/-- A push inside a well-nested factor is closed by a well-nested continuation. -/
private theorem WellNested.wellMatched_of_extract {w : List (α × Op n Γ)} {s e q : ℕ}
    {i : Fin n} (hw : WellNested (w.extract s e)) (he : e ≤ w.length) (hsq : s ≤ q)
    (hqe : q < e) (hq : IsPushOn w i q) : WellMatched w q := by
  obtain ⟨a, γ, hq⟩ := hq
  obtain ⟨m', hm', hwn⟩ := hw.exists_wellMatched (p := q - s) (i := i)
    ⟨a, γ, by rw [List.getElem?_extract _ (by omega), Nat.add_sub_cancel' hsq, hq]⟩
  have hlen : (w.extract s e).length = e - s := by simp; omega
  have hm'len := hm'.lt_length
  have hw' : w = w.take s ++ (w.extract s e ++ w.drop e) := by
    rw [List.extract_eq_take_drop, show w.drop e = (w.drop s).drop (e - s) by
      rw [List.drop_drop]; congr 1; omega, List.take_append_drop, List.take_append_drop]
  refine ⟨s + m', ?_, ?_⟩
  · have := (matches_append_left (w.take s) _ (q - s) m').mpr (hm'.append_right (w.drop e))
    rwa [← hw', List.length_take, Nat.min_eq_left (by omega), Nat.add_sub_cancel' hsq] at this
  · rw [List.extract_extract _ (by omega), Nat.add_sub_cancel' hsq] at hwn
    rwa [Nat.add_assoc]

/-- The first point after a push where its stack goes below its height before the push is the
matching pop. -/
private theorem exists_matches_of_net_neg {w : List (α × Op n Γ)} {i : Fin n} {p e : ℕ}
    (hp : IsPushOn w i p) (he : e ≤ w.length) (hneg : net i (w.extract (p + 1) e) < 0) :
    ∃ m < e, Matches w p m := by
  obtain ⟨u, b, δ, u', hv, hu, hk⟩ :=
    exists_first_pop i (w.extract (p + 1) e) 0 (by simpa using hneg)
  simp only [Nat.cast_zero, zero_add] at hu hk
  have hlen : (w.extract (p + 1) e).length = e - (p + 1) := by simp; omega
  have hulen : u.length < e - (p + 1) := by simp [← hlen, hv]
  have hu' : w.extract (p + 1) (p + 1 + u.length) = u := by
    simp [← w.take_extract (Nat.le_add_right _ _) (show p + 1 + u.length ≤ e by omega), hv]
  refine ⟨p + 1 + u.length, by omega, by omega, i, hp, ⟨b, δ, ?_⟩, by rwa [hu'], by rwa [hu']⟩
  simp [← List.getElem?_extract _ hulen, hv]

private theorem PendingAt.lt_of_matches {w : List (α × Op n Γ)} {i : Fin n} {p x m : ℕ}
    (h : PendingAt w p x) (hp : IsPushOn w i p) (hm : Matches w p m) : x < m := by
  obtain ⟨-, -, hk⟩ := h.of_isPushOn hp
  obtain ⟨hpm, ⟨b, δ, hmpop⟩, -, hnet⟩ := hm.of_isPushOn hp
  by_contra hxm
  exact absurd (hk _) (not_le.mpr (net_neg_of_pop (by omega) (by omega) hmpop hnet))

/-! ## Open holes and contexts -/

/-- A hole push at or after a matched push `r₁` and before its pop `m₁` does not share a context
with `m₁`. -/
private theorem not_isContext_extract_pop {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {w : List (α × Op n Γ)} (hrun : M.configLTS.MTr c w c') {i : Fin n} {r₁ m₁ a : ℕ}
    (hm₁ : Matches w r₁ m₁) (hr₁ : IsPushOn w i r₁) (ha : HolePush w a) (hr₁a : r₁ ≤ a)
    (ham : a < m₁) : ¬IsContext (w.extract a (m₁ + 1)) := by
  intro hctx
  obtain ⟨-, ⟨b, δ, hpop⟩, hk, hnet⟩ := hm₁.of_isPushOn hr₁
  have hctx' : IsContextOf i (w.extract a (m₁ + 1)) :=
    hctx.isContextOf (List.mem_extract_iff_getElem?.mpr ⟨_, by omega, by omega, hpop⟩) rfl
  obtain ⟨⟨j, hj⟩, hnwm⟩ := ha
  obtain rfl := hctx'.eq_of_isPushOn le_rfl (by omega) hj
  apply hnwm
  rcases Nat.eq_or_lt_of_le hr₁a with rfl | hlt
  · exact wellMatched_of_isContextOf hrun hm₁ hj hctx'
  · have hsplit : net j (w.extract (a + 1) m₁) < 0 := by
      have h₀ := hk (a - (r₁ + 1))
      rw [w.take_extract (by omega) (by omega)] at h₀
      rw [← w.extract_append_extract (show r₁ + 1 ≤ a by omega) (show a ≤ m₁ by omega),
        net_append, ← w.extract_append_extract (show a ≤ a + 1 by omega)
          (show a + 1 ≤ m₁ by omega), net_append] at hnet
      obtain ⟨a', γ, hj'⟩ := hj
      rw [net_extract_succ hj'] at hnet
      simp only [Op.net, Op.kind, OpKind.net, ↓reduceIte] at hnet
      omega
    obtain ⟨m, hm, hmatch⟩ :=
      exists_matches_of_net_neg hj (by have := hm₁.lt_length; omega) hsplit
    have ham' := hmatch.1
    refine wellMatched_of_isContextOf hrun hmatch hj fun μ hμ => hctx' μ ?_
    rw [← w.take_extract (show a ≤ m + 1 by omega) (show m + 1 ≤ m₁ + 1 by omega)] at hμ
    exact List.mem_of_mem_take hμ

/-- The first pending pushes of two distinct open holes do not share a context. -/
private theorem not_isContext_extract_holes {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {w : List (α × Op n Γ)} (hrun : M.configLTS.MTr c w c') {x a b : ℕ}
    (ha : OpenHolePush w x a) (hb : OpenHolePush w x b) (hbrep : ¬∃ p, SameHole w x p b)
    (hab : a < b) : ¬IsContext (w.extract a (b + 1)) := by
  classical
  intro hctx
  obtain ⟨⟨⟨i, hai⟩, -⟩, -⟩ := id ha
  obtain ⟨⟨⟨j, hbj⟩, hbnwm⟩, hbpend⟩ := id hb
  obtain ⟨a', γ, hai'⟩ := id hai
  have hctx' : IsContextOf i (w.extract a (b + 1)) :=
    hctx.isContextOf (List.mem_extract_iff_getElem?.mpr ⟨_, le_rfl, by omega, hai'⟩) rfl
  obtain ⟨b', δ, hbj'⟩ := id hbj
  obtain rfl := hctx'.eq_of_isPushOn (by omega) (by omega) hbj
  -- The last open hole push on stack `j` before `b`.
  let P := (Finset.range b).filter fun p => a ≤ p ∧ OpenHolePush w x p ∧ IsPushOn w j p
  have hPne : P.Nonempty := ⟨a, by simp [P, hab, ha, hai]⟩
  have hp' := P.max'_mem hPne
  simp only [P, Finset.mem_filter, Finset.mem_range] at hp'
  obtain ⟨hp'b, hap', hp'open, hp'j⟩ := hp'
  have hmax : ∀ s, a ≤ s → s < b → OpenHolePush w x s → IsPushOn w j s → s ≤ P.max' hPne :=
    fun s h₁ h₂ h₃ h₄ => P.le_max' s (by simp [P, h₁, h₂, h₃, h₄])
  set p' := P.max' hPne
  apply hbrep
  refine ⟨p', hp'b, hp'open, hb, ⟨j, hp'j, hbj⟩, ?_⟩
  obtain ⟨-, -, hbk⟩ := hbpend.of_isPushOn hbj
  obtain ⟨hp'x, hxlen, hp'k⟩ := hp'open.2.of_isPushOn hp'j
  have hbx : b ≤ x := hbpend.1
  have hk : ∀ k, 0 ≤ net j ((w.extract (p' + 1) b).take k) := fun k => by
    rw [← w.take_extract (show p' + 1 ≤ b by omega) (show b ≤ x + 1 by omega), List.take_take]
    exact hp'k _
  have hctxv : IsContextOf j (w.extract (p' + 1) b) := fun μ hμ => hctx' μ (by
    have e : w.extract (p' + 1) b = (w.extract a (b + 1)).extract (p' + 1 - a) (b - a) := by
      rw [List.extract_extract _ (by omega)]
      congr 1 <;> omega
    rw [e] at hμ
    exact (List.extract_isInfix _ _ _).subset hμ)
  obtain ⟨c₁, c₂, hrunv⟩ := exists_configLTS_mTr_extract hrun (p' + 1) b
  refine wellNested_of_isContextOf hrunv hctxv ?_ hk
  by_contra hne
  have hpos : 0 < net j (w.extract (p' + 1) b) :=
    lt_of_le_of_ne (by simpa only [List.take_length] using hk (w.extract (p' + 1) b).length)
      (Ne.symm hne)
  obtain ⟨q, hq, hqj, hqk⟩ := exists_pending_push hk hpos
  have hlen : (w.extract (p' + 1) b).length = b - (p' + 1) := by simp; omega
  -- The push at `p' + 1 + q` is still pending at `x`.
  have hsj : IsPushOn w j (p' + 1 + q) := by
    obtain ⟨a'', γ'', h⟩ := hqj
    exact ⟨a'', γ'', by rw [← List.getElem?_extract _ (a := p' + 1) (b := b) (by omega), h]⟩
  have hspend : PendingAt w (p' + 1 + q) x := by
    refine ⟨by omega, hxlen, j, hsj, fun k => ?_⟩
    have e : w.extract (p' + 1 + q + 1) (x + 1) =
        (w.extract (p' + 1) b).drop (q + 1) ++
          (w.extract b (b + 1) ++ w.extract (b + 1) (x + 1)) := by
      rw [List.drop_eq_extract, hlen, List.extract_extract _ (by omega),
        w.extract_append_extract (show b ≤ b + 1 by omega) (show b + 1 ≤ x + 1 by omega),
        show p' + 1 + (b - (p' + 1)) = b by omega,
        w.extract_append_extract (show p' + 1 + (q + 1) ≤ b by omega) (show b ≤ x + 1 by omega)]
      rfl
    rw [e]
    refine net_take_append_nonneg hqk (net_take_append_nonneg (fun k => ?_) hbk) k
    rw [List.extract_eq_singleton hbj']
    rcases k with _ | k <;> simp [Op.net]
  by_cases hs : HolePush w (p' + 1 + q)
  · have := hmax (p' + 1 + q) (by omega) (by omega) ⟨hs, hspend⟩ hsj
    omega
  · obtain ⟨m, hm, hwn⟩ : WellMatched w (p' + 1 + q) := not_not.1 fun h => hs ⟨⟨j, hsj⟩, h⟩
    have hxm := hspend.lt_of_matches hsj hm
    exact hbnwm (hwn.wellMatched_of_extract (by have := hm.lt_length; omega) (by omega)
      (by omega) hbj)

/-! ## Scope-bounded runs are hole-bounded -/

/-- The first sentence of Proposition 2 in Section 2.1 of [AkshayGastinKrishnaRoychowdhury2020],
for scope: the label sequence of a complete `K`-scope-bounded run is `K`-hole-bounded. -/
theorem ScopeBounded.holeBounded {M : MPDA n State α Γ} {s s' : State} {w : List (α × Op n Γ)}
    {K : ℕ} (h : ScopeBounded K w)
    (hrun : M.configLTS.MTr ⟨s, Stacks.empty⟩ w ⟨s', Stacks.empty⟩) : HoleBounded K w := by
  classical
  intro x hx
  have hbal := balanced_of_configLTS_mTr hrun
  change {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q}.ncard ≤ K
  set R := {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q} with hRdef
  rcases R.eq_empty_or_nonempty with hR | hR
  · simp [hR]
  -- The earliest first pending push of an open hole, and its matching pop.
  set r₁ := Nat.find hR
  have hr₁ : r₁ ∈ R := Nat.find_spec hR
  have hmin : ∀ q ∈ R, r₁ ≤ q := fun q hq => Nat.find_min' hR hq
  obtain ⟨⟨⟨i, hr₁i⟩, -⟩, hr₁pend⟩ := hr₁.1
  have hr₁x : r₁ ≤ x := hr₁pend.1
  obtain ⟨a₁, γ₁, hr₁i'⟩ := id hr₁i
  have hneg : net i (w.extract (r₁ + 1) w.length) < 0 := by
    have h₀ : net i (w.extract 0 w.length) = 0 := by
      simpa [List.extract_eq_take_drop] using (hbal i).1
    have h₁ : 0 ≤ net i (w.extract 0 r₁) := by
      simpa [List.extract_eq_take_drop] using (hbal i).2 r₁
    rw [← w.extract_append_extract (Nat.zero_le r₁) (show r₁ ≤ w.length by omega),
      ← w.extract_append_extract (show r₁ ≤ r₁ + 1 by omega) (show r₁ + 1 ≤ w.length by omega),
      net_append, net_append, net_extract_succ hr₁i'] at h₀
    simp only [Op.net, Op.kind, OpKind.net, ↓reduceIte] at h₀
    omega
  obtain ⟨m₁, -, hm₁⟩ := exists_matches_of_net_neg hr₁i le_rfl hneg
  have hxm₁ : x < m₁ := hr₁pend.lt_of_matches hr₁i hm₁
  have hm₁len := hm₁.lt_length
  -- The representatives, as a finite set of positions up to `x`.
  let T : Finset ℕ := (Finset.range (x + 1)).filter (· ∈ R)
  have hRT : R = ↑T := by
    ext q
    simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨fun hq => ⟨by have := hq.1.2.1; omega, hq⟩, fun hq => hq.2⟩
  have hge : ∀ t ∈ insert m₁ T, r₁ ≤ t := (Finset.forall_mem_insert _ _ _).2
    ⟨by omega, fun t ht => hmin t (Finset.mem_filter.mp ht).2⟩
  have hinj : Set.InjOn (· - r₁) ↑(insert m₁ T) := fun a ha b hb (hab : a - r₁ = b - r₁) => by
    have := hge a ha
    have := hge b hb
    omega
  have hle_m₁ : ∀ a ∈ insert m₁ T, a ≤ m₁ := (Finset.forall_mem_insert _ _ _).2
    ⟨le_rfl, fun a ha => by have := Finset.mem_range.1 (Finset.mem_filter.mp ha).1; omega⟩
  have hcard := List.Splits.card_le (fun _ _ huv hv => IsContext.of_isInfix huv hv) (h r₁ m₁ hm₁)
    ((insert m₁ T).image (· - r₁)) ?hT ?hTP
  · rw [Finset.card_image_of_injOn hinj, Finset.card_insert_of_notMem (by
      simp only [T, Finset.mem_filter, Finset.mem_range]
      omega)] at hcard
    rw [hRT, Set.ncard_coe_finset]
    omega
  case hT =>
    intro _ ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    have := hge a ha
    have := hle_m₁ a ha
    simp
    omega
  case hTP =>
    intro t ht t' ht' htt'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht'
    have hra := hge a ha
    have hrb := hge b hb
    have hab : a < b := by omega
    have hbm := hle_m₁ b hb
    rw [List.extract_extract _ (by omega), Nat.add_sub_cancel' hra,
      show r₁ + (b - r₁ + 1) = b + 1 by omega]
    have haR := (Finset.mem_filter.mp ((Finset.mem_insert.mp ha).resolve_left (by omega))).2
    rcases Finset.mem_insert.mp hb with rfl | hbT
    · exact not_isContext_extract_pop hrun hm₁ hr₁i haR.1.1 hra (by omega)
    · exact not_isContext_extract_holes hrun haR.1 (Finset.mem_filter.mp hbT).2.1
        (Finset.mem_filter.mp hbT).2.2 hab

/-- The first sentence of Proposition 2 in Section 2.1 of [AkshayGastinKrishnaRoychowdhury2020],
for rounds, with the bound `K * n` instead of `K`: the label sequence of a complete run with at
most `K` rounds is `K * n`-hole-bounded. -/
theorem RoundBounded.holeBounded {M : MPDA n State α Γ} {s s' : State} {w : List (α × Op n Γ)}
    {K : ℕ} (h : RoundBounded K w)
    (hrun : M.configLTS.MTr ⟨s, Stacks.empty⟩ w ⟨s', Stacks.empty⟩) : HoleBounded (K * n) w :=
  h.contextBounded.scopeBounded.holeBounded hrun

end Cslib.Automata.MPDA
