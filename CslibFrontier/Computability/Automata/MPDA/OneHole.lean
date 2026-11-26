/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Holes
import CslibFrontier.Foundations.Data.List.Extract

/-! # One hole is no hole

For complete runs, one open hole at a time is no more permissive than none: the label sequence of
a run of an MPDA from empty stacks to empty stacks is `1`-hole-bounded exactly when it is
well-nested. Theorem 2 in Appendix G.1 of [AkshayGastinKrishnaRoychowdhury2020] states this for
accepting runs, in the discussion of the multi-producer consumer benchmark, with an informal
proof.

The argument goes through crossings. A crossing is a push on stack `i` with its matching pop, and
a push on another stack strictly between them that is still pending at the pop.

- A crossing yields two open holes just before the pop, so it rules out `1`-hole-boundedness.
- A complete run without crossings is well-nested. On a complete run every stack returns to its
  initial height without going below it, and the first pop of the stack pushed first closes that
  push; the absence of crossings makes the factor in between, and the rest, well-nested again.

Well-nested sequences are `0`-hole-bounded (`MPDA.WellNested.holeBounded_zero`), so a complete run
is also `0`-hole-bounded exactly when it is well-nested.

## Main definitions

- `MPDA.Crossing`: a push on one stack that is pending across a matched pair of another stack.

## Main results

- `MPDA.Crossing.not_holeBounded_one`: a sequence with a crossing is not `1`-hole-bounded.
- `MPDA.holeBounded_one_iff_wellNested`: Theorem 2 in Appendix G.1 of
  [AkshayGastinKrishnaRoychowdhury2020].

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α β : Type*}

/-! ## Factors -/

theorem net_extract_succ {w : List (α × Op n Γ)} {a : ℕ} {μ : α × Op n Γ}
    (h : w[a]? = some μ) (i : Fin n) : net i (w.extract a (a + 1)) = μ.2.net i := by
  rw [List.extract_eq_singleton h, net_cons, net_nil, add_zero]

/-! ## Unpacking matches and pending pushes -/

theorem Matches.of_isPushOn {w : List (α × Op n Γ)} {i : Fin n} {p m : ℕ}
    (h : Matches w p m) (hp : IsPushOn w i p) :
    p < m ∧ (∃ b γ, w[m]? = some (b, .pop i γ)) ∧
      (∀ k, 0 ≤ net i ((w.extract (p + 1) m).take k)) ∧ net i (w.extract (p + 1) m) = 0 := by
  obtain ⟨hpm, j, hj, hm, hk, hnet⟩ := h
  obtain rfl := hp.unique hj
  exact ⟨hpm, hm, hk, hnet⟩

theorem PendingAt.of_isPushOn {w : List (α × Op n Γ)} {i : Fin n} {p x : ℕ}
    (h : PendingAt w p x) (hp : IsPushOn w i p) :
    p ≤ x ∧ x < w.length ∧ ∀ k, 0 ≤ net i ((w.extract (p + 1) (x + 1)).take k) := by
  obtain ⟨hpx, hx, j, hj, hk⟩ := h
  obtain rfl := hp.unique hj
  exact ⟨hpx, hx, hk⟩

/-- If the stack `i` returns to its height before position `m`, where it pops, then the factor
up to `m'` pops below that height. -/
theorem net_neg_of_pop {w : List (α × Op n Γ)} {i : Fin n} {a m m' : ℕ} {b : α} {γ : Γ}
    (ham : a ≤ m) (hmm' : m < m') (hm : w[m]? = some (b, .pop i γ))
    (hnet : net i (w.extract a m) = 0) : net i ((w.extract a m').take (m + 1 - a)) < 0 := by
  rw [w.take_extract (by omega) (by omega), ← w.extract_append_extract ham (Nat.le_succ m),
    net_append, hnet, net_extract_succ hm]
  simp [Op.net]

/-- A push has at most one matching pop. -/
private theorem Matches.unique {w : List (α × Op n Γ)} {p m m' : ℕ} (h : Matches w p m)
    (h' : Matches w p m') : m = m' := by
  obtain ⟨-, i, hp, -⟩ := id h
  obtain ⟨hpm, ⟨b, γ, hm⟩, hk, hnet⟩ := h.of_isPushOn hp
  obtain ⟨hpm', ⟨b', γ', hm'⟩, hk', hnet'⟩ := h'.of_isPushOn hp
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd (hk' _) (not_le.mpr (net_neg_of_pop (by omega) hlt hm hnet))
  · exact heq
  · exact absurd (hk _) (not_le.mpr (net_neg_of_pop (by omega) hgt hm' hnet'))

/-! ## Crossings -/

/-- A crossing of `w`: the push at `p` on stack `i` is matched by the pop at `z`, and the push at
`q` on another stack `j`, strictly between them, is still pending at `z`. -/
@[expose] def Crossing (w : List (α × Op n Γ)) : Prop :=
  ∃ (i j : Fin n) (p q z : ℕ), i ≠ j ∧ p < q ∧ q < z ∧ IsPushOn w i p ∧ IsPushOn w j q ∧
    Matches w p z ∧ PendingAt w q z

section Crossing

variable {w : List (α × Op n Γ)} {i j : Fin n} {p q z : ℕ}

/-- The outer push of a crossing is a hole push. -/
private theorem crossing_holePush_left (hpq : p < q) (hqz : q < z) (hp : IsPushOn w i p)
    (hq : IsPushOn w j q) (hpz : Matches w p z) (hqp : PendingAt w q z) : HolePush w p := by
  refine ⟨⟨i, hp⟩, ?_⟩
  rintro ⟨m, hm, hws⟩
  obtain rfl := hm.unique hpz
  obtain ⟨-, -, hqk⟩ := hqp.of_isPushOn hq
  have h₁ := hws.net_take_nonneg j (q - p)
  rw [w.take_extract hpq.le (by omega)] at h₁
  have h₂ := hqk (m + 1 - (q + 1))
  rw [w.take_extract (by omega) le_rfl] at h₂
  have h₃ := hws.net_eq_zero j
  rw [← w.extract_append_extract (show p ≤ q by omega) (show q ≤ m + 1 by omega),
    ← w.extract_append_extract (show q ≤ q + 1 by omega) (show q + 1 ≤ m + 1 by omega),
    net_append, net_append] at h₃
  obtain ⟨a, γ, hqa⟩ := hq
  rw [net_extract_succ hqa] at h₃
  simp only [Op.net, Op.kind, OpKind.net, ↓reduceIte] at h₃
  omega

/-- The inner push of a crossing is a hole push. -/
private theorem crossing_holePush_right (hij : i ≠ j) (hpq : p < q) (hqz : q < z)
    (hp : IsPushOn w i p) (hq : IsPushOn w j q) (hpz : Matches w p z) (hqp : PendingAt w q z) :
    HolePush w q := by
  refine ⟨⟨j, hq⟩, ?_⟩
  rintro ⟨m, hm, hws⟩
  obtain ⟨hqm, ⟨b, γ, hmpop⟩, -, hmnet⟩ := hm.of_isPushOn hq
  obtain ⟨-, -, hqk⟩ := hqp.of_isPushOn hq
  have hmz : z < m := by
    by_contra hcon
    exact absurd (hqk _) (not_le.mpr (net_neg_of_pop (by omega) (by omega) hmpop hmnet))
  have h₁ := hws.net_take_nonneg i (z + 1 - q)
  rw [w.take_extract (by omega) (by omega)] at h₁
  obtain ⟨-, ⟨b', γ', hzpop⟩, hpk, hpnet⟩ := hpz.of_isPushOn hp
  have h₂ := hpk (q - (p + 1))
  rw [w.take_extract (by omega) (by omega)] at h₂
  rw [← w.extract_append_extract (show p + 1 ≤ q by omega) (show q ≤ z by omega),
    ← w.extract_append_extract (show q ≤ q + 1 by omega) (show q + 1 ≤ z by omega),
    net_append, net_append] at hpnet
  rw [← w.extract_append_extract (show q ≤ q + 1 by omega) (show q + 1 ≤ z + 1 by omega),
    ← w.extract_append_extract (show q + 1 ≤ z by omega) (show z ≤ z + 1 by omega),
    net_append, net_append] at h₁
  obtain ⟨a, δ, hqa⟩ := hq
  rw [net_extract_succ hqa] at hpnet h₁
  rw [net_extract_succ hzpop] at h₁
  simp only [Op.net, Op.kind, OpKind.net, Ne.symm hij, ↓reduceIte] at hpnet h₁
  omega

/-- Every open hole push lies in an open hole whose first pending push is on the same stack. -/
private theorem exists_first_openHolePush {x : ℕ} (hq : OpenHolePush w x q) (hqi : IsPushOn w i q) :
    ∃ r, OpenHolePush w x r ∧ IsPushOn w i r ∧ ¬∃ p, SameHole w x p r := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    by_cases h : ∃ p, SameHole w x p q
    · obtain ⟨p, hpq, hp, -, ⟨j, hpj, hqj⟩, -⟩ := h
      obtain rfl := hqi.unique hqj
      exact ih p hpq hp hpj
    · exact ⟨q, hq, hqi, h⟩

private theorem openHoles_finite (w : List (α × Op n Γ)) (x : ℕ) :
    {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q}.Finite :=
  (Set.finite_le_nat x).subset fun _ hq => hq.1.2.1

/-- A crossing gives two open holes just before the pop of the crossing, one for each stack. -/
private theorem Crossing.two_le_openHoles (hij : i ≠ j) (hpq : p < q) (hqz : q < z)
    (hp : IsPushOn w i p) (hq : IsPushOn w j q) (hpz : Matches w p z) (hqp : PendingAt w q z) :
    2 ≤ openHoles w (z - 1) := by
  have hzlen := hpz.lt_length
  obtain ⟨-, -, hpk, -⟩ := hpz.of_isPushOn hp
  obtain ⟨-, -, hqk⟩ := hqp.of_isPushOn hq
  have hpx : PendingAt w p (z - 1) :=
    ⟨by omega, by omega, i, hp, by rwa [show z - 1 + 1 = z by omega]⟩
  have hqx : PendingAt w q (z - 1) := by
    refine ⟨by omega, by omega, j, hq, fun k => ?_⟩
    rw [show z - 1 + 1 = z by omega,
      ← w.take_extract (show q + 1 ≤ z by omega) (Nat.le_succ z), List.take_take]
    exact hqk _
  obtain ⟨r, hr, hri, hrl⟩ :=
    exists_first_openHolePush ⟨crossing_holePush_left hpq hqz hp hq hpz hqp, hpx⟩ hp
  obtain ⟨r', hr', hr'j, hr'l⟩ :=
    exists_first_openHolePush ⟨crossing_holePush_right hij hpq hqz hp hq hpz hqp, hqx⟩ hq
  have hne : r ≠ r' := fun h => hij (hri.unique (h ▸ hr'j))
  have hsub :
      ({r, r'} : Set ℕ) ⊆ {q | OpenHolePush w (z - 1) q ∧ ¬∃ p, SameHole w (z - 1) p q} :=
    Set.pair_subset ⟨hr, hrl⟩ ⟨hr', hr'l⟩
  unfold openHoles
  rw [← Set.ncard_pair hne]
  exact Set.ncard_le_ncard hsub (openHoles_finite w _)

/-- A sequence with a crossing is not `1`-hole-bounded. -/
theorem Crossing.not_holeBounded_one (h : Crossing w) : ¬HoleBounded 1 w := by
  obtain ⟨i, j, p, q, z, hij, hpq, hqz, hp, hq, hpz, hqp⟩ := h
  intro hb
  have := hb (z - 1) (by have := hpz.lt_length; omega)
  have := Crossing.two_le_openHoles hij hpq hqz hp hq hpz hqp
  omega

end Crossing

/-! ## Shifting crossings into larger sequences -/

section Shift

variable {v l r : List (α × Op n Γ)} {i : Fin n} {p x : ℕ}

private theorem IsPushOn.append_left (h : IsPushOn v i p) (l : List (α × Op n Γ)) :
    IsPushOn (l ++ v) i (l.length + p) := by
  obtain ⟨a, γ, h⟩ := h
  refine ⟨a, γ, ?_⟩
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, h]

private theorem IsPushOn.append_right (h : IsPushOn v i p) (r : List (α × Op n Γ)) :
    IsPushOn (v ++ r) i p := by
  obtain ⟨a, γ, h⟩ := h
  have hp := (List.getElem?_eq_some_iff.mp h).1
  exact ⟨a, γ, by rw [List.getElem?_append_left hp, h]⟩

private theorem PendingAt.append_left (h : PendingAt v p x) (l : List (α × Op n Γ)) :
    PendingAt (l ++ v) (l.length + p) (l.length + x) := by
  obtain ⟨hpx, hx, j, hj, hk⟩ := h
  refine ⟨by omega, by simp; omega, j, IsPushOn.append_left hj l, ?_⟩
  rwa [show l.length + p + 1 = l.length + (p + 1) by omega,
    show l.length + x + 1 = l.length + (x + 1) by omega, List.extract_append_left]

private theorem PendingAt.append_right (h : PendingAt v p x) (r : List (α × Op n Γ)) :
    PendingAt (v ++ r) p x := by
  obtain ⟨hpx, hx, j, hj, hk⟩ := h
  refine ⟨hpx, by simp; omega, j, IsPushOn.append_right hj r, ?_⟩
  rwa [List.extract_append_right _ _ (by omega)]

private theorem Crossing.append_left (h : Crossing v) (l : List (α × Op n Γ)) :
    Crossing (l ++ v) := by
  obtain ⟨i, j, p, q, z, hij, hpq, hqz, hp, hq, hpz, hqp⟩ := h
  exact ⟨i, j, l.length + p, l.length + q, l.length + z, hij, by omega, by omega,
    hp.append_left l, hq.append_left l, (matches_append_left l v p z).mpr hpz,
    hqp.append_left l⟩

private theorem Crossing.append_right (h : Crossing v) (r : List (α × Op n Γ)) :
    Crossing (v ++ r) := by
  obtain ⟨i, j, p, q, z, hij, hpq, hqz, hp, hq, hpz, hqp⟩ := h
  exact ⟨i, j, p, q, z, hij, hpq, hqz, hp.append_right r, hq.append_right r,
    hpz.append_right r, hqp.append_right r⟩

end Shift

/-! ## Balanced sequences -/

/-- A sequence is balanced if no prefix pops below the initial height of any stack and every stack
returns to its initial height. The label sequences of complete runs are balanced. -/
@[expose] def Balanced (w : List (α × Op n Γ)) : Prop :=
  ∀ i, net i w = 0 ∧ ∀ k, 0 ≤ net i (w.take k)

private theorem Op.net_cases (i : Fin n) (op : Op n Γ) :
    op.net i = 0 ∨ (op.net i = 1 ∧ ∃ γ, op = .push i γ) ∨ (op.net i = -1 ∧ ∃ γ, op = .pop i γ) := by
  cases op with
  | nop => exact .inl rfl
  | push j γ => by_cases hj : j = i <;> simp [Op.net, hj]
  | pop j γ => by_cases hj : j = i <;> simp [Op.net, hj]

private theorem take_eq_extract (w : List β) (b : ℕ) : w.take b = w.extract 0 b := by
  simp [List.extract]

private theorem exists_first_pop_cons {d d' : ℕ} {i : Fin n} {μ : α × Op n Γ}
    {u : List (α × Op n Γ)} (hstep : (d : ℤ) + μ.2.net i = d') (hu : (d' : ℤ) + net i u = 0)
    (hk : ∀ k, 0 ≤ (d' : ℤ) + net i (u.take k)) :
    (d : ℤ) + net i (μ :: u) = 0 ∧ ∀ k, 0 ≤ (d : ℤ) + net i ((μ :: u).take k) := by
  refine ⟨by rw [net_cons]; omega, fun k => ?_⟩
  cases k with
  | zero => simp
  | succ k => rw [List.take_succ_cons, net_cons]; have := hk k; omega

/-- The first point where the height of stack `i`, starting at `d`, drops below zero is a pop on
stack `i`. -/
theorem exists_first_pop (i : Fin n) :
    ∀ (v : List (α × Op n Γ)) (d : ℕ), (d : ℤ) + net i v < 0 →
      ∃ u b δ u', v = u ++ (b, Op.pop i δ) :: u' ∧ (d : ℤ) + net i u = 0 ∧
        ∀ k, 0 ≤ (d : ℤ) + net i (u.take k)
  | [], d, hv => by simp at hv; omega
  | (a, op) :: v, d, hv => by
    rw [net_cons] at hv
    rcases Op.net_cases i op with h | ⟨h, γ, rfl⟩ | ⟨h, γ, rfl⟩
    · obtain ⟨u, b, δ, u', rfl, hu, hk⟩ := exists_first_pop i v d (by rw [h] at hv; omega)
      exact ⟨(a, op) :: u, b, δ, u', rfl, exists_first_pop_cons (by simp [h]) hu hk⟩
    · obtain ⟨u, b, δ, u', rfl, hu, hk⟩ :=
        exists_first_pop i v (d + 1) (by rw [h] at hv; push_cast; omega)
      exact ⟨(a, .push i γ) :: u, b, δ, u', rfl,
        exists_first_pop_cons (by simp [Op.net]) hu hk⟩
    · rcases d with _ | d
      · exact ⟨[], a, γ, v, rfl, by simp, fun k => by simp⟩
      · obtain ⟨u, b, δ, u', rfl, hu, hk⟩ :=
          exists_first_pop i v d (by rw [h] at hv; push_cast at hv; omega)
        exact ⟨(a, .pop i γ) :: u, b, δ, u', rfl,
          exists_first_pop_cons (by simp [Op.net]) hu hk⟩

/-- If no prefix of `u` pops below the initial height of stack `j` and `u` ends strictly above it,
then some push on stack `j` in `u` is still pending at the end of `u`. -/
theorem exists_pending_push {j : Fin n} {u : List (α × Op n Γ)}
    (hk : ∀ k, 0 ≤ net j (u.take k)) (hpos : 0 < net j u) :
    ∃ q < u.length, IsPushOn u j q ∧ ∀ k, 0 ≤ net j ((u.drop (q + 1)).take k) := by
  classical
  let P : ℕ → Prop := fun k => net j (u.take k) = 0
  let K := Nat.findGreatest P u.length
  have hPK : P K := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (by simp [P])
  have hKle : K ≤ u.length := Nat.findGreatest_le _
  have hgt : ∀ k, K < k → k ≤ u.length → 1 ≤ net j (u.take k) := fun k hk₁ hk₂ => by
    have := Nat.findGreatest_is_greatest hk₁ hk₂
    have := hk k
    simp only [P] at *
    omega
  have hKlt : K < u.length := lt_of_le_of_ne hKle fun h => by
    simp only [P, h, List.take_length] at hPK
    omega
  obtain ⟨μ, hμ⟩ : ∃ μ, u[K]? = some μ := ⟨u[K], List.getElem?_eq_getElem hKlt⟩
  have hstep : net j (u.take (K + 1)) = net j (u.take K) + μ.2.net j := by
    rw [take_eq_extract, take_eq_extract,
      ← u.extract_append_extract (Nat.zero_le K) (Nat.le_succ K), net_append, net_extract_succ hμ]
  have h1 := hgt (K + 1) (by omega) (by omega)
  rw [hstep, show net j (u.take K) = 0 from hPK] at h1
  obtain ⟨a, op⟩ := μ
  rcases Op.net_cases j op with h | ⟨h, γ, rfl⟩ | ⟨h, γ, rfl⟩
  · simp only [h] at h1
    omega
  · refine ⟨K, hKlt, ⟨a, γ, hμ⟩, fun k => ?_⟩
    have hK1 : net j (u.take (K + 1)) = 1 := by rw [hstep, hPK, h]; rfl
    by_cases hk' : K + 1 + k ≤ u.length
    · have := hgt (K + 1 + k) (by omega) hk'
      rw [List.take_add, net_append, hK1] at this
      omega
    · rw [List.take_of_length_le (by simp; omega)]
      have hu := List.take_length (l := u) ▸ hgt u.length hKlt le_rfl
      have hsum : net j u = net j (u.take (K + 1)) + net j (u.drop (K + 1)) := by
        rw [← net_append, List.take_append_drop]
      omega
  · simp only [h] at h1
    omega

/-! ## Prefixes and suffixes of balanced sequences -/

private theorem IsPushOn.cons {v : List (α × Op n Γ)} {i : Fin n} {p : ℕ} (h : IsPushOn v i p)
    (μ : α × Op n Γ) : IsPushOn (μ :: v) i (p + 1) := by
  obtain ⟨a, γ, h⟩ := h
  exact ⟨a, γ, by rw [List.getElem?_cons_succ, h]⟩

private theorem PendingAt.cons {v : List (α × Op n Γ)} {p x : ℕ} (h : PendingAt v p x)
    (μ : α × Op n Γ) : PendingAt (μ :: v) (p + 1) (x + 1) := by
  obtain ⟨hpx, hx, j, hj, hk⟩ := h
  refine ⟨by omega, by simp; omega, j, IsPushOn.cons hj μ, ?_⟩
  rwa [List.extract_cons_succ]

/-- A push pending at `x` stays pending across a transition that does not pop its stack. -/
private theorem PendingAt.succ {w : List (α × Op n Γ)} {j : Fin n} {p x : ℕ} {μ : α × Op n Γ}
    (h : PendingAt w p x) (hp : IsPushOn w j p) (hμ : w[x + 1]? = some μ) (hnet : 0 ≤ μ.2.net j) :
    PendingAt w p (x + 1) := by
  obtain ⟨hpx, -, hk⟩ := h.of_isPushOn hp
  have hlen := (List.getElem?_eq_some_iff.mp hμ).1
  refine ⟨by omega, hlen, j, hp, fun k => ?_⟩
  rw [← w.extract_append_extract (show p + 1 ≤ x + 1 by omega) (Nat.le_succ (x + 1)),
    List.extract_eq_singleton hμ, List.take_append, net_append]
  have h₁ := hk k
  have h₂ : 0 ≤ net j (List.take (k - (w.extract (p + 1) (x + 1)).length) [μ]) := by
    rcases k - (w.extract (p + 1) (x + 1)).length with _ | m
    · simp
    · simpa using hnet
  omega

private theorem net_take_nonneg_of_append {j : Fin n} {u r : List (α × Op n Γ)}
    (h : ∀ k, 0 ≤ net j ((u ++ r).take k)) (k : ℕ) : 0 ≤ net j (u.take k) := by
  by_cases hk : k ≤ u.length
  · have := h k
    rwa [List.take_append_of_le_length hk] at this
  · have := h u.length
    rwa [List.take_append_of_le_length le_rfl, List.take_length,
      ← List.take_of_length_le (show u.length ≤ k by omega)] at this

private theorem net_take_nonneg_of_append_left {j : Fin n} {l v : List (α × Op n Γ)}
    (h : ∀ k, 0 ≤ net j ((l ++ v).take k)) (hl : net j l = 0) (k : ℕ) :
    0 ≤ net j (v.take k) := by
  have := h (l.length + k)
  rwa [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, net_append,
    hl, zero_add] at this

/-! ## Stacks along runs -/

variable {State : Type*}

/-- How a stack operation changes stack `i`: it is left unchanged, a symbol is pushed onto it, or
a symbol is popped from it. -/
private theorem Op.Apply.cases {op : Op n Γ} {σ σ' : Stacks n Γ} (h : op.Apply σ σ') (i : Fin n) :
    (σ' i = σ i ∧ op.net i = 0) ∨ (∃ γ, σ' i = γ :: σ i ∧ op.net i = 1) ∨
      (∃ γ, σ i = γ :: σ' i ∧ op.net i = -1) := by
  cases op with
  | nop =>
    rw [Op.apply_nop] at h
    exact .inl ⟨congrFun h i, rfl⟩
  | push j γ =>
    rw [Op.apply_push] at h
    subst h
    rcases eq_or_ne j i with rfl | hj
    · exact .inr (.inl ⟨γ, by simp, by simp [Op.net]⟩)
    · exact .inl ⟨Function.update_of_ne (Ne.symm hj) _ _, by simp [Op.net, hj]⟩
  | pop j γ =>
    rw [Op.apply_pop] at h
    subst h
    rcases eq_or_ne j i with rfl | hj
    · exact .inr (.inr ⟨γ, by simp, by simp [Op.net]⟩)
    · exact .inl ⟨(Function.update_of_ne (Ne.symm hj) _ _).symm, by simp [Op.net, hj]⟩

/-- Along a run, the height of each stack changes by the net effect of the run on it. -/
private theorem configLTS_mTr_length {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {w : List (α × Op n Γ)} (h : M.configLTS.MTr c w c') (i : Fin n) :
    ((c'.contents i).length : ℤ) = (c.contents i).length + net i w := by
  induction h with
  | refl => simp
  | stepL htr _ ih =>
    rw [ih, net_cons]
    rcases (configLTS_tr.mp htr).2.cases i with ⟨h, h'⟩ | ⟨γ, h, h'⟩ | ⟨γ, h, h'⟩
    · rw [h, h']; omega
    all_goals rw [h, h', List.length_cons]; push_cast; omega

/-- The label sequence of a run from empty stacks to empty stacks is balanced. -/
theorem balanced_of_configLTS_mTr {M : MPDA n State α Γ} {s s' : State}
    {w : List (α × Op n Γ)}
    (h : M.configLTS.MTr ⟨s, Stacks.empty⟩ w ⟨s', Stacks.empty⟩) : Balanced w := by
  refine fun i => ⟨by simpa [Stacks.empty] using (configLTS_mTr_length h i).symm, fun k => ?_⟩
  rw [← List.take_append_drop k w] at h
  obtain ⟨c, h₁, -⟩ := LTS.MTr.split h
  have := configLTS_mTr_length h₁ i
  simp only [Stacks.empty, List.length_nil, Nat.cast_zero, zero_add] at this
  omega

/-! ## Complete runs without crossings are well-nested -/

private theorem wellNested_of_not_crossing_aux {M : MPDA n State α Γ} :
    ∀ (N : ℕ) (w : List (α × Op n Γ)) (c c' : Config n State Γ), w.length ≤ N →
      M.configLTS.MTr c w c' → Balanced w → ¬Crossing w → WellNested w
  | 0, [], _, _, _, _, _, _ => .nil
  | N + 1, [], _, _, _, _, _, _ => .nil
  | N + 1, (a, op) :: w', c, c', hlen, hrun, hbal, hcr => by
    obtain ⟨c₁, htr, hrun'⟩ := LTS.MTr.cons_iff.mp hrun
    have hlen' : w'.length ≤ N := by simp at hlen; omega
    cases op with
    | nop =>
      refine .nop (wellNested_of_not_crossing_aux N w' c₁ c' hlen' hrun'
        (fun j => ⟨?_, fun k => ?_⟩) fun h => hcr (h.append_left [(a, .nop)]))
      · have := (hbal j).1
        rwa [net_cons, show (Op.nop : Op n Γ).net j = 0 from rfl, zero_add] at this
      · have := (hbal j).2 (k + 1)
        rwa [List.take_succ_cons, net_cons, show (Op.nop : Op n Γ).net j = 0 from rfl,
          zero_add] at this
    | pop j γ => simpa [Op.net] using (hbal j).2 1
    | push i γ =>
      have hw'i : net i w' = -1 := by
        have := (hbal i).1
        simp only [net_cons, Op.net, Op.kind, OpKind.net, ↓reduceIte] at this
        omega
      obtain ⟨u, b, δ, u', rfl, hu0, huk⟩ := exists_first_pop i w' 0 (by simp [hw'i])
      simp only [Nat.cast_zero, zero_add] at hu0 huk
      -- The prefixes of `u` never pop below the initial height of any stack.
      have hupre : ∀ j k, 0 ≤ net j (u.take k) := fun j => by
        rcases eq_or_ne i j with rfl | hij
        · exact huk
        · refine net_take_nonneg_of_append (r := (b, .pop i δ) :: u') fun k => ?_
          have h0 : (Op.push i γ : Op n Γ).net j = 0 := by simp [Op.net, hij]
          simpa only [List.take_succ_cons, net_cons, h0, zero_add] using (hbal j).2 (k + 1)
      -- Every stack returns to its initial height at the end of `u`, otherwise a push in `u` is
      -- pending across the matched pair, which is a crossing.
      have hunet : ∀ j, net j u = 0 := by
        intro j
        rcases eq_or_ne i j with rfl | hij
        · exact hu0
        · by_contra hne
          have hpos : 0 < net j u := by
            have := hupre j u.length
            rw [List.take_length] at this
            omega
          obtain ⟨q, hq, hqj, hqk⟩ := exists_pending_push (hupre j) hpos
          apply hcr
          have hfu : ((a, Op.push i γ) :: (u ++ (b, Op.pop i δ) :: u')).extract 1
              (u.length + 1) = u := by
            simp [List.extract]
          have hqu : PendingAt u q (u.length - 1) := by
            refine ⟨by omega, by omega, j, hqj, fun k => ?_⟩
            rw [show u.length - 1 + 1 = u.length by omega, List.extract,
              List.take_of_length_le (l := u.drop (q + 1)) (by simp)]
            exact hqk k
          have hqw := (hqu.append_right ((b, .pop i δ) :: u')).cons (a, .push i γ)
          rw [show u.length - 1 + 1 = u.length by omega] at hqw
          refine ⟨i, j, 0, q + 1, u.length + 1, hij, by omega, by omega, ⟨a, γ, rfl⟩,
            (hqj.append_right _).cons _, ⟨by omega, i, ⟨a, γ, rfl⟩, ⟨b, δ, by simp⟩, by rwa [hfu],
              by rwa [hfu]⟩,
            hqw.succ (μ := (b, .pop i δ)) ((hqj.append_right _).cons _) (by simp) ?_⟩
          simp [Op.net, hij]
      -- `u'` is balanced as well.
      have hL : ∀ j, net j ((a, Op.push i γ) :: (u ++ [(b, Op.pop i δ)])) = 0 := fun j => by
        rw [net_cons, net_append, net_cons, net_nil, hunet j]
        have := Op.net_pop j i δ γ
        dsimp only
        omega
      have e : (a, Op.push i γ) :: (u ++ (b, Op.pop i δ) :: u') =
          ((a, Op.push i γ) :: (u ++ [(b, Op.pop i δ)])) ++ u' := by simp
      have hbal' : Balanced u' := fun j => by
        have h₁ := e ▸ (hbal j).1
        rw [net_append, hL j, zero_add] at h₁
        exact ⟨h₁, net_take_nonneg_of_append_left (e ▸ (hbal j).2) (hL j)⟩
      -- The runs on `u` and `u'`.
      obtain ⟨c₂, hrunu, hrest⟩ := LTS.MTr.split hrun'
      obtain ⟨c₃, hν, hrunu'⟩ := LTS.MTr.cons_iff.mp hrest
      -- The interior `u` is well-nested by induction, so it leaves the stacks unchanged.
      have hlu : u.length ≤ N := by simp at hlen; omega
      have hwu : WellNested u :=
        wellNested_of_not_crossing_aux N u c₁ c₂ hlu hrunu (fun j => ⟨hunet j, hupre j⟩)
          fun h => hcr ((h.append_right ((b, .pop i δ) :: u')).append_left [(a, .push i γ)])
      -- Hence the pop matches the symbol of the push.
      have hδ : δ = γ := by
        have := congrFun (hwu.contents_eq hrunu) i
        rw [Op.apply_push.mp (configLTS_tr.mp htr).2,
          Op.apply_pop.mp (configLTS_tr.mp hν).2] at this
        simp only [Function.update_self, List.cons.injEq] at this
        exact this.1
      subst hδ
      have hlu' : u'.length ≤ N := by simp at hlen; omega
      exact .pushPop hwu
        (wellNested_of_not_crossing_aux N u' c₃ c' hlu' hrunu' hbal' fun h =>
          hcr (e ▸ h.append_left _))

/-- A balanced run without crossings is well-nested. -/
theorem wellNested_of_not_crossing {M : MPDA n State α Γ} {c c' : Config n State Γ}
    {w : List (α × Op n Γ)} (h : M.configLTS.MTr c w c') (hb : Balanced w) (hc : ¬Crossing w) :
    WellNested w :=
  wellNested_of_not_crossing_aux w.length w c c' le_rfl h hb hc

/-! ## One hole is no hole -/

/-- **One hole is no hole**, Theorem 2 in Appendix G.1 of [AkshayGastinKrishnaRoychowdhury2020]
(arXiv:2002.05950v2): the label sequence of a complete run, from empty stacks to empty stacks, is
`1`-hole-bounded exactly when it is well-nested. -/
theorem holeBounded_one_iff_wellNested {M : MPDA n State α Γ} {s s' : State}
    {w : List (α × Op n Γ)}
    (h : M.configLTS.MTr ⟨s, Stacks.empty⟩ w ⟨s', Stacks.empty⟩) :
    HoleBounded 1 w ↔ WellNested w :=
  ⟨fun hb => wellNested_of_not_crossing h (balanced_of_configLTS_mTr h)
      fun hc => hc.not_holeBounded_one hb,
    fun hw => hw.holeBounded_zero.mono (Nat.zero_le 1)⟩

end Cslib.Automata.MPDA
