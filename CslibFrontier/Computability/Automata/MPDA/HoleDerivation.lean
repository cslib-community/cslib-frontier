/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.OneHole
import CslibFrontier.Foundations.Data.List.Extract

/-! # Hole derivations

A hole derivation builds a sequence of transitions from three kinds of blocks, keeping track of
the open holes as chains of pending pushes: a well-nested block, a new hole made of atomic hole
segments `↓ws ↓ws ⋯` of one stack (each a push followed by a well-nested sequence), and a pop that
matches the newest push of the last open hole of its stack. These are the steps of the search of
Algorithm 1 of [AkshayGastinKrishnaRoychowdhury2020] (`AddHole`, `AddPop` and the well-nested
continuations through `WR`).

Every sequence built with at most `K` open holes is `K`-hole-bounded
(`MPDA.HoleDerivation.holeBounded`): at each position, the first pending pushes of open holes in
the sense of Definition 1 map injectively to the open chains.

## Main definitions

- `MPDA.HoleBlock`: a block of atomic hole segments of one stack.
- `MPDA.HoleDerivation`: hole derivations with at most `K` open chains.

## Main results

- `MPDA.HoleDerivation.holeBounded`: sequences built by hole derivations are `K`-hole-bounded.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α : Type*}

/-! ## Pending pushes -/

section Pending

variable {w v : List (α × Op n Γ)} {p q x y : ℕ}

/-- Whether a push is pending at a position only depends on the sequence up to that position. -/
theorem pendingAt_append_iff (hx : x < w.length) : PendingAt (w ++ v) p x ↔ PendingAt w p x := by
  unfold PendingAt
  have hext : (w ++ v).extract (p + 1) (x + 1) = w.extract (p + 1) (x + 1) :=
    List.extract_append_right _ _ (by omega)
  constructor
  · rintro ⟨hpx, -, i, ⟨a, γ, hp⟩, hk⟩
    refine ⟨hpx, hx, i, ⟨a, γ, ?_⟩, fun k => hext ▸ hk k⟩
    rwa [List.getElem?_append_left (by omega)] at hp
  · rintro ⟨hpx, -, i, ⟨a, γ, hp⟩, hk⟩
    refine ⟨hpx, by simp; omega, i, ⟨a, γ, ?_⟩, fun k => hext.symm ▸ hk k⟩
    rwa [List.getElem?_append_left (by omega)]

/-- A push pending at a position is pending at every earlier position from the push on. -/
theorem PendingAt.anti (h : PendingAt w p x) (hpy : p ≤ y) (hyx : y ≤ x) : PendingAt w p y := by
  obtain ⟨hpx, hx, i, hp, hk⟩ := h
  refine ⟨hpy, by omega, i, hp, fun k => ?_⟩
  rw [← w.take_extract (show p + 1 ≤ y + 1 by omega) (show y + 1 ≤ x + 1 by omega),
    List.take_take]
  exact hk _

/-- A push pending at `x` stays pending at `y ≥ x` if no prefix of the factor after `x` pops below
its initial height on the stack of the push. -/
theorem PendingAt.extend (h : PendingAt w p x) (hxy : x ≤ y) (hy : y < w.length)
    (hk : ∀ (i : Fin n), (∃ a γ, w[p]? = some (a, .push i γ)) →
      ∀ k, 0 ≤ net i ((w.extract (x + 1) (y + 1)).take k)) : PendingAt w p y := by
  obtain ⟨hpx, -, i, hp, hk'⟩ := h
  refine ⟨by omega, hy, i, hp, fun k => ?_⟩
  rw [← w.extract_append_extract (show p + 1 ≤ x + 1 by omega) (show x + 1 ≤ y + 1 by omega),
    List.take_append, net_append]
  have h₁ := hk' k
  have h₂ := hk i hp (k - (w.extract (p + 1) (x + 1)).length)
  by_cases hkl : k ≤ (w.extract (p + 1) (x + 1)).length
  · rw [show k - (w.extract (p + 1) (x + 1)).length = 0 by omega]
    simp only [List.take_zero, net_nil, add_zero]
    exact h₁
  · rw [List.take_of_length_le (by omega)] at h₁ ⊢
    have := hk' (w.extract (p + 1) (x + 1)).length
    rw [List.take_length] at this
    omega

/-- A push matched at `m` is no longer pending from `m` on. -/
theorem not_pendingAt_of_matches {m : ℕ} (h : Matches w q m) (hmx : m ≤ x) :
    ¬PendingAt w q x := by
  obtain ⟨hqm, i, hq, ⟨b, γ, hm⟩, -, hnet⟩ := h
  rintro ⟨-, hx, j, hq', hk⟩
  obtain rfl := IsPushOn.unique hq' hq
  have := hk (m + 1 - (q + 1))
  have hneg := net_neg_of_pop (w := w) (a := q + 1) (m' := x + 1) (by omega) (by omega) hm hnet
  omega

/-- A push inside a well-nested factor is closed by a well-nested continuation inside that
factor. -/
theorem exists_matches_of_wellNested {a b : ℕ} {i : Fin n} (hwn : WellNested (w.extract a b))
    (hb : b ≤ w.length) (haq : a ≤ q) (hqb : q < b) (hq : IsPushOn w i q) :
    ∃ m, Matches w q m ∧ m < b ∧ WellMatched w q := by
  have hsplit : w.take a ++ w.extract a b ++ w.drop b = w := by
    rw [List.extract_eq_take_drop, ← List.take_add, show a + (b - a) = b by omega,
      List.take_append_drop]
  have hpush : IsPushOn (w.extract a b) i (q - a) := by
    obtain ⟨c, γ, hq⟩ := hq
    refine ⟨c, γ, ?_⟩
    rw [List.extract_eq_take_drop, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_cancel' haq, hq]
  obtain ⟨m, hm, hmwn⟩ := hwn.exists_wellMatched hpush
  have hmlen := hm.lt_length
  rw [List.extract_eq_take_drop, List.length_take, List.length_drop] at hmlen
  have hwm := (show WellMatched (w.extract a b) (q - a) from ⟨m, hm, hmwn⟩).append
    (w.take a) (w.drop b)
  rw [hsplit, List.length_take, min_eq_left (by omega), Nat.add_sub_cancel' haq] at hwm
  have hM := (matches_append_left (w.take a) (w.extract a b ++ w.drop b) (q - a) m).mpr
    (hm.append_right _)
  rw [← List.append_assoc, hsplit, List.length_take, min_eq_left (by omega),
    Nat.add_sub_cancel' haq] at hM
  exact ⟨a + m, hM, by omega, hwm⟩

end Pending

/-! ## Chains of pending pushes -/

/-- An open hole as a chain of pushes on one stack: their positions and pushed symbols, newest
first. -/
structure HoleChain (n : ℕ) (Γ : Type*) where
  /-- The stack of the hole. -/
  stack : Fin n
  /-- The positions and symbols of the pushes, newest first. -/
  pushes : List (ℕ × Γ)

/-- Consecutive pushes of a chain are separated by a well-nested factor, newest first. -/
@[expose] def Chained (w : List (α × Op n Γ)) (ps : List (ℕ × Γ)) : Prop :=
  ps.IsChain fun e e' => e'.1 < e.1 ∧ WellNested (w.extract (e'.1 + 1) e.1)

/-- A snapshot of the open holes at position `x` of `w`: at most `K` chains of pending pushes,
consecutive pushes of a chain separated by well-nested factors, and every other push pending at
`x` inside a well-nested factor of `w`. -/
@[expose] def Snapshot (K : ℕ) (w : List (α × Op n Γ)) (x : ℕ) (C : List (HoleChain n Γ)) :
    Prop :=
  C.length ≤ K ∧
  (∀ c ∈ C, ∀ e ∈ c.pushes, (∃ a, w[e.1]? = some (a, .push c.stack e.2)) ∧ PendingAt w e.1 x) ∧
  (∀ c ∈ C, Chained w c.pushes) ∧
  ∀ q, PendingAt w q x → (∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q) ∨
    ∃ a b, a ≤ q ∧ q < b ∧ b ≤ w.length ∧ WellNested (w.extract a b)

section Counting

variable {w : List (α × Op n Γ)} {x : ℕ} {K : ℕ} {C : List (HoleChain n Γ)}

theorem Chained.pairwise {ps : List (ℕ × Γ)} (h : Chained w ps) :
    ps.Pairwise fun e e' => e'.1 < e.1 := by
  have : IsTrans (ℕ × Γ) (fun e e' => e'.1 < e.1) := ⟨fun _ _ _ h h' => h'.trans h⟩
  exact (h.imp fun _ _ h => h.1).pairwise

/-- In a chain, a push older than another one has a direct older neighbour of the newer one, at or
after it, separated from the newer one by a well-nested factor. -/
private theorem exists_older_neighbour {ps : List (ℕ × Γ)} (h : Chained w ps) {e e' : ℕ × Γ}
    (he : e ∈ ps) (he' : e' ∈ ps) (hlt : e.1 < e'.1) :
    ∃ f ∈ ps, e.1 ≤ f.1 ∧ f.1 < e'.1 ∧ WellNested (w.extract (f.1 + 1) e'.1) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp he'
  have hpw := h.pairwise
  rw [List.pairwise_append, List.pairwise_cons] at hpw
  -- `e` comes after `e'`.
  have hel₂ : e ∈ l₂ := by
    rcases List.mem_append.mp he with hl | hl
    · exact absurd (hpw.2.2 e hl e' List.mem_cons_self) (by omega)
    · exact (List.mem_cons.mp hl).resolve_left fun h => hlt.ne (congrArg Prod.fst h)
  obtain ⟨f, l₃, rfl⟩ : ∃ f l₃, l₂ = f :: l₃ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hel₂)
  have hchain : (e' :: f :: l₃).IsChain fun e e' => e'.1 < e.1 ∧
      WellNested (w.extract (e'.1 + 1) e.1) := (List.IsChain.right_of_append h)
  obtain ⟨hfe', hwn⟩ := (List.isChain_cons_cons.mp hchain).1
  refine ⟨f, by simp, ?_, hfe', hwn⟩
  rcases List.mem_cons.mp hel₂ with rfl | hl
  · exact le_rfl
  · exact ((List.pairwise_cons.mp hpw.2.1.2).1 e hl).le

/-- **Counting holes**: the open holes at `x`, in the sense of Definition 1, are at most the
chains of a snapshot at `x`. -/
theorem Snapshot.openHoles_le (h : Snapshot K w x C) : openHoles w x ≤ C.length := by
  obtain ⟨-, hpend, hchain, hcover⟩ := h
  classical
  set S := {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q}
  -- Each counted push lies in a chain.
  have hin : ∀ q ∈ S, ∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q := by
    rintro q ⟨⟨⟨⟨i, hpush⟩, hnot⟩, hq⟩, -⟩
    rcases hcover q hq with h | ⟨a, b, haq, hqb, hb, hwn⟩
    · exact h
    · obtain ⟨-, -, -, hwm⟩ := exists_matches_of_wellNested hwn hb haq hqb hpush
      exact absurd hwm hnot
  let f : ℕ → ℕ := fun q => C.findIdx fun c => c.pushes.any (·.1 == q)
  have hf : ∀ q ∈ S, ∃ hlt : f q < C.length, ∃ e ∈ (C[f q]'hlt).pushes, e.1 = q := by
    intro q hq
    obtain ⟨c, hc, e, he, rfl⟩ := hin q hq
    have hlt : f e.1 < C.length :=
      List.findIdx_lt_length_of_exists ⟨c, hc, List.any_eq_true.mpr ⟨e, he, by simp⟩⟩
    have := List.findIdx_getElem (w := hlt)
    simp only [List.any_eq_true, beq_iff_eq] at this
    exact ⟨hlt, this⟩
  -- Two counted pushes in the same chain are equal.
  have hinj : Set.InjOn f S := by
    intro q hq q' hq' hqq'
    obtain ⟨hlt, e, he, rfl⟩ := hf q hq
    obtain ⟨hlt', e', he', rfl⟩ := hf q' hq'
    replace he : e ∈ (C[f e'.1]'hlt').pushes := by simpa only [hqq'] using he
    set c := C[f e'.1]'hlt'
    have hc : c ∈ C := List.getElem_mem _
    by_contra hne
    -- Order the two pushes; the newer one is not the first pending push of its hole.
    suffices key : ∀ {e e' : ℕ × Γ}, e ∈ c.pushes → e' ∈ c.pushes → e.1 < e'.1 → e'.1 ∈ S →
        False by
      rcases lt_or_gt_of_ne hne with h | h
      · exact key he he' h hq'
      · exact key he' he h hq
    intro e e' he he' hlt hS
    obtain ⟨⟨⟨⟨i, hpush'⟩, hnot'⟩, hq'x⟩, hfirst⟩ := hS
    obtain ⟨g, hg, heg, hge', hwn⟩ := exists_older_neighbour (hchain c hc) he he' hlt
    obtain ⟨⟨a, hga⟩, hgx⟩ := hpend c hc g hg
    obtain ⟨⟨a', hea'⟩, -⟩ := hpend c hc e' he'
    have hgpush : IsPushOn w c.stack g.1 := ⟨a, g.2, hga⟩
    -- The older neighbour is a hole push: otherwise it would enclose the newer one.
    have hghole : HolePush w g.1 := by
      refine ⟨⟨c.stack, hgpush⟩, fun ⟨m, hm, hmwn⟩ => hnot' ?_⟩
      have hmx : x < m := lt_of_not_ge fun hmx => not_pendingAt_of_matches hm hmx hgx
      obtain ⟨-, -, -, hwm⟩ := exists_matches_of_wellNested hmwn
        (by have := hm.lt_length; omega) (by omega) (by have := hq'x.1; omega) ⟨a', e'.2, hea'⟩
      exact hwm
    exact hfirst ⟨g.1, hge', ⟨hghole, hgx⟩, ⟨⟨⟨c.stack, ⟨a', e'.2, hea'⟩⟩, hnot'⟩, hq'x⟩,
      ⟨c.stack, hgpush, a', e'.2, hea'⟩, hwn⟩
  calc openHoles w x = S.ncard := rfl
    _ ≤ ((Finset.range C.length : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun q hq => by
          obtain ⟨hlt, -⟩ := hf q hq
          simpa using hlt) hinj (Finset.finite_toSet _)
    _ = C.length := by rw [Set.ncard_coe_finset, Finset.card_range]

end Counting

/-! ## Hole derivations -/

/-- A block of atomic hole segments of stack `i` starting at position `L`: pushes on stack `i`, each
followed by a well-nested sequence. `ps` lists the positions and symbols of the pushes, newest
first. -/
inductive HoleBlock (i : Fin n) (L : ℕ) : List (α × Op n Γ) → List (ℕ × Γ) → Prop where
  | nil : HoleBlock i L [] []
  | snoc {v ws : List (α × Op n Γ)} {ps : List (ℕ × Γ)} {a : α} {γ : Γ} :
    HoleBlock i L v ps → WellNested ws →
      HoleBlock i L (v ++ (a, .push i γ) :: ws) ((L + v.length, γ) :: ps)

/-- Hole derivations with at most `K` open holes: a well-nested block, a new hole as a block of
atomic hole segments while fewer than `K` holes are open, a pop matching the newest push of the
last open hole of its stack, or closing a hole without pending pushes. These are the steps of the
search of Algorithm 1 of [AkshayGastinKrishnaRoychowdhury2020]. -/
inductive HoleDerivation (K : ℕ) : List (HoleChain n Γ) → List (α × Op n Γ) → Prop where
  | nil : HoleDerivation K [] []
  | wellNested {C : List (HoleChain n Γ)} {w v : List (α × Op n Γ)} :
    HoleDerivation K C w → WellNested v → HoleDerivation K C (w ++ v)
  | hole {C : List (HoleChain n Γ)} {w v : List (α × Op n Γ)} {ps : List (ℕ × Γ)} {i : Fin n} :
    HoleDerivation K C w → C.length < K → HoleBlock i w.length v ps →
      HoleDerivation K (C ++ [⟨i, ps⟩]) (w ++ v)
  | pop {pre post : List (HoleChain n Γ)} {w : List (α × Op n Γ)} {ps : List (ℕ × Γ)}
    {i : Fin n} {p : ℕ} {γ : Γ} {b : α} :
    HoleDerivation K (pre ++ ⟨i, (p, γ) :: ps⟩ :: post) w → (∀ c ∈ post, c.stack ≠ i) →
      HoleDerivation K (pre ++ ⟨i, ps⟩ :: post) (w ++ [(b, .pop i γ)])
  | close {pre post : List (HoleChain n Γ)} {w : List (α × Op n Γ)} {i : Fin n} :
    HoleDerivation K (pre ++ ⟨i, []⟩ :: post) w → HoleDerivation K (pre ++ post) w

/-- The open chains at the end of `w`: at most `K` chains of pushes pending at the last position,
with no other pending push, consecutive pushes of a chain separated by well-nested factors, and
the pushes of earlier chains before those of later ones. -/
@[expose] def HoleBoundary (K : ℕ) (w : List (α × Op n Γ)) (C : List (HoleChain n Γ)) : Prop :=
  C.length ≤ K ∧
  (∀ c ∈ C, ∀ e ∈ c.pushes, (∃ a, w[e.1]? = some (a, .push c.stack e.2)) ∧
    PendingAt w e.1 (w.length - 1)) ∧
  (∀ c ∈ C, Chained w c.pushes) ∧
  (∀ q, PendingAt w q (w.length - 1) → ∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q) ∧
  C.Pairwise fun c c' => ∀ e ∈ c.pushes, ∀ e' ∈ c'.pushes, e.1 < e'.1

section Invariant

variable {K : ℕ} {w v : List (α × Op n Γ)} {C : List (HoleChain n Γ)}

theorem chained_append {ps : List (ℕ × Γ)} (h : Chained w ps) (hps : ∀ e ∈ ps, e.1 < w.length) :
    Chained (w ++ v) ps := by
  induction ps with
  | nil => exact .nil
  | cons e t ih =>
    rcases t with _ | ⟨e', t⟩
    · exact .singleton _
    · obtain ⟨⟨hlt, hwn⟩, ht⟩ := List.isChain_cons_cons.mp h
      refine List.isChain_cons_cons.mpr ⟨⟨hlt, ?_⟩, ih ht fun e he => hps e (by simp_all)⟩
      rwa [List.extract_append_right _ _ (by have := hps e (by simp); omega)]

theorem Snapshot.append {x : ℕ} (h : Snapshot K w x C) (hx : x < w.length) :
    Snapshot K (w ++ v) x C := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hpos : ∀ c ∈ C, ∀ e ∈ c.pushes, e.1 < w.length := fun c hc e he => by
    obtain ⟨⟨a, ha⟩, -⟩ := h₂ c hc e he
    exact (List.getElem?_eq_some_iff.mp ha).1
  refine ⟨h₁, fun c hc e he => ?_, fun c hc => chained_append (h₃ c hc) (hpos c hc), fun q hq => ?_⟩
  · obtain ⟨⟨a, ha⟩, hp⟩ := h₂ c hc e he
    exact ⟨⟨a, by rw [List.getElem?_append_left (hpos c hc e he), ha]⟩,
      (pendingAt_append_iff hx).mpr hp⟩
  · rcases h₄ q ((pendingAt_append_iff hx).mp hq) with h | ⟨a, b, haq, hqb, hb, hwn⟩
    · exact .inl h
    · refine .inr ⟨a, b, haq, hqb, by simp; omega, ?_⟩
      rwa [List.extract_append_right _ _ hb]

theorem HoleBoundary.snapshot (h : HoleBoundary K w C) : Snapshot K w (w.length - 1) C :=
  ⟨h.1, h.2.1, h.2.2.1, fun q hq => .inl (h.2.2.2.1 q hq)⟩

/-- The pushes of the chains lie in `w`. -/
theorem HoleBoundary.lt_length (h : HoleBoundary K w C) {c : HoleChain n Γ} (hc : c ∈ C)
    {e : ℕ × Γ} (he : e ∈ c.pushes) : e.1 < w.length := by
  obtain ⟨⟨a, ha⟩, -⟩ := h.2.1 c hc e he
  exact (List.getElem?_eq_some_iff.mp ha).1

/-- Pushes pending at the end of `w` stay pending through a well-nested block. -/
private theorem pendingAt_append_wellNested {q x : ℕ} (hv : WellNested v) (hw : w ≠ [])
    (hq : PendingAt w q (w.length - 1)) (hx₁ : w.length ≤ x) (hx₂ : x < (w ++ v).length) :
    PendingAt (w ++ v) q x := by
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  refine ((pendingAt_append_iff (by omega)).mpr hq).extend (by omega) hx₂ fun i _ k => ?_
  rw [show w.length - 1 + 1 = w.length + 0 by omega, show x + 1 = w.length + (x + 1 - w.length)
    by omega, List.extract_append_left, List.extract_eq_take_drop, List.drop_zero,
    List.take_take]
  exact hv.net_take_nonneg i _

theorem HoleBoundary.append_wellNested (h : HoleBoundary K w C) (hv : WellNested v) :
    HoleBoundary K (w ++ v) C ∧
      ∀ x, w.length ≤ x → x < (w ++ v).length → Snapshot K (w ++ v) x C := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have hb : HoleBoundary K w C := ⟨h₁, h₂, h₃, h₄, h₅⟩
  rcases eq_or_ne v [] with rfl | hvne
  · simp only [List.append_nil]
    exact ⟨hb, fun x hx hx' => by omega⟩
  have hvlen : 0 < v.length := List.length_pos_iff.mpr hvne
  -- The chains stay pending through `v`.
  have hpend : ∀ c ∈ C, ∀ e ∈ c.pushes, ∀ x, w.length ≤ x → x < (w ++ v).length →
      PendingAt (w ++ v) e.1 x := by
    intro c hc e he x hx₁ hx₂
    have hw : w ≠ [] := List.ne_nil_of_length_pos (by have := hb.lt_length hc he; omega)
    exact pendingAt_append_wellNested hv hw (h₂ c hc e he).2 hx₁ hx₂
  have hpos := fun c hc e he => hb.lt_length (c := c) hc (e := e) he
  have hpush : ∀ c ∈ C, ∀ e ∈ c.pushes, ∃ a, (w ++ v)[e.1]? = some (a, .push c.stack e.2) :=
    fun c hc e he => by
      obtain ⟨⟨a, ha⟩, -⟩ := h₂ c hc e he
      exact ⟨a, by rw [List.getElem?_append_left (hpos c hc e he), ha]⟩
  have hchain : ∀ c ∈ C, Chained (w ++ v) c.pushes := fun c hc =>
    chained_append (h₃ c hc) (hpos c hc)
  have hv' : (w ++ v).extract w.length (w ++ v).length = v := by
    simp
  -- Pending pushes before `v` are pushes of the chains.
  have hold : ∀ q x, q < w.length → w.length ≤ x + 1 → PendingAt (w ++ v) q x →
      ∃ c ∈ C, ∃ e ∈ c.pushes, e.1 = q := by
    intro q x hq hx hp
    exact h₄ q ((pendingAt_append_iff (by omega)).mp (hp.anti (by omega) (by omega)))
  refine ⟨⟨h₁, fun c hc e he => ⟨hpush c hc e he, hpend c hc e he _ (by simp; omega)
    (by simp; omega)⟩, hchain, fun q hq => ?_, h₅⟩, fun x hx₁ hx₂ => ⟨h₁,
    fun c hc e he => ⟨hpush c hc e he, hpend c hc e he x hx₁ hx₂⟩, hchain, fun q hq => ?_⟩⟩
  · by_cases hqw : q < w.length
    · exact hold q _ hqw (by simp; omega) hq
    · -- A pending push of `v` would be matched inside `v`.
      exfalso
      obtain ⟨-, -, i, ⟨a, γ, hqa⟩, -⟩ := id hq
      obtain ⟨m, hm, hmb, -⟩ := exists_matches_of_wellNested (q := q) (i := i) (a := w.length)
        (b := (w ++ v).length) (by rw [hv']; exact hv) le_rfl (by omega)
        (by have := hq.1; have := hq.2.1; omega) ⟨a, γ, hqa⟩
      exact not_pendingAt_of_matches hm (by omega) hq
  · by_cases hqw : q < w.length
    · exact .inl (hold q x hqw (by omega) hq)
    · exact .inr ⟨w.length, (w ++ v).length, by omega, by have := hq.1; omega, le_rfl,
        by rw [hv']; exact hv⟩

/-- A push on stack `i` at the last position joins the newest chain. -/
theorem HoleBoundary.append_push {i : Fin n} {ps : List (ℕ × Γ)} {a : α} {γ : Γ}
    (h : HoleBoundary K w (C ++ [⟨i, ps⟩]))
    (hlink : ∀ e ∈ ps.head?, WellNested (w.extract (e.1 + 1) w.length)) :
    HoleBoundary K (w ++ [(a, .push i γ)]) (C ++ [⟨i, (w.length, γ) :: ps⟩]) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := id h
  set w' := w ++ [(a, Op.push i γ)]
  have hlen : w'.length = w.length + 1 := by simp [w']
  have hpos := fun c (hc : c ∈ C ++ [⟨i, ps⟩]) e (he : e ∈ c.pushes) => h.lt_length hc he
  -- Old pending pushes stay pending.
  have hold : ∀ q, PendingAt w q (w.length - 1) → PendingAt w' q (w'.length - 1) := by
    intro q hq
    have hw : 0 < w.length := by have := hq.2.1; omega
    refine ((pendingAt_append_iff (by omega)).mpr hq).extend (by rw [hlen]; omega)
      (by rw [hlen]; omega) fun j _ k => ?_
    rw [hlen, show w.length - 1 + 1 = w.length by omega, show w.length + 1 - 1 + 1 =
      w.length + 1 by omega]
    rcases k with _ | k
    · simp
    · simp only [net, Op.net, OpKind.net, Op.kind, Int.reduceNeg, List.extract_eq_take_drop,
        add_tsub_cancel_left, List.drop_left', List.take_succ_cons, List.take_nil, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      split_ifs <;> simp
  have hnew : PendingAt w' w.length (w'.length - 1) :=
    ⟨by omega, by omega, i, ⟨a, γ, by simp [w']⟩, fun k => by
      rw [hlen, show w.length + 1 - 1 + 1 = w.length + 1 by omega, List.extract_eq_take_drop,
        Nat.sub_self, List.take_zero, List.take_nil]
      simp⟩
  have hmem : ∀ c ∈ C ++ [⟨i, (w.length, γ) :: ps⟩], c ∈ C ∨ c = ⟨i, (w.length, γ) :: ps⟩ :=
    fun c hc => by simpa using hc
  refine ⟨by simpa using h₁, fun c hc e he => ?_, fun c hc => ?_, fun q hq => ?_, ?_⟩
  · rcases hmem c hc with hc | rfl
    · obtain ⟨⟨a', ha⟩, hp⟩ := h₂ c (by simp [hc]) e he
      exact ⟨⟨a', by rw [List.getElem?_append_left (hpos c (by simp [hc]) e he), ha]⟩,
        hold _ hp⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨⟨a, by simp [w']⟩, hnew⟩
      · obtain ⟨⟨a', ha⟩, hp⟩ := h₂ ⟨i, ps⟩ (by simp) e he
        exact ⟨⟨a', by rw [List.getElem?_append_left (hpos ⟨i, ps⟩ (by simp) e he), ha]⟩,
          hold _ hp⟩
  · rcases hmem c hc with hc | rfl
    · exact chained_append (h₃ c (by simp [hc])) (hpos c (by simp [hc]))
    · have hps : Chained w' ps := chained_append (h₃ ⟨i, ps⟩ (by simp)) (hpos ⟨i, ps⟩ (by simp))
      rcases ps with _ | ⟨e', t⟩
      · exact .singleton _
      · refine List.isChain_cons_cons.mpr ⟨⟨hpos ⟨i, e' :: t⟩ (by simp) e' (by simp), ?_⟩, hps⟩
        rw [List.extract_append_right _ _ le_rfl]
        exact hlink e' (by simp)
  · by_cases hqw : q < w.length
    · obtain ⟨c, hc, e, he, rfl⟩ := h₄ q ((pendingAt_append_iff (by omega)).mp
        (hq.anti (y := w.length - 1) (by omega) (by rw [hlen]; omega)))
      rcases List.mem_append.mp hc with hc | hc
      · exact ⟨c, by simp [hc], e, he, rfl⟩
      · obtain rfl := List.mem_singleton.mp hc
        exact ⟨⟨i, (w.length, γ) :: ps⟩, by simp, e, List.mem_cons_of_mem _ he, rfl⟩
    · exact ⟨⟨i, (w.length, γ) :: ps⟩, by simp, (w.length, γ), by simp,
        by have := hq.1; rw [hlen] at this; omega⟩
  · rw [List.pairwise_append] at h₅ ⊢
    refine ⟨h₅.1, by simp, fun c hc c' hc' e he e' he' => ?_⟩
    obtain rfl := List.mem_singleton.mp hc'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hpos c (by simp [hc]) e he
    · exact h₅.2.2 c hc ⟨i, ps⟩ (by simp) e he e' he'

/-- A pop on stack `i` matches the newest push of the last open hole of stack `i`. -/
theorem HoleBoundary.append_pop {pre post : List (HoleChain n Γ)} {i : Fin n} {p : ℕ} {γ : Γ}
    {ps : List (ℕ × Γ)} {b : α} (h : HoleBoundary K w (pre ++ ⟨i, (p, γ) :: ps⟩ :: post))
    (hpost : ∀ c ∈ post, c.stack ≠ i) :
    HoleBoundary K (w ++ [(b, .pop i γ)]) (pre ++ ⟨i, ps⟩ :: post) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := id h
  set c₀ : HoleChain n Γ := ⟨i, (p, γ) :: ps⟩
  set w' := w ++ [(b, Op.pop i γ)]
  have hlen : w'.length = w.length + 1 := by simp [w']
  have hc₀ : c₀ ∈ pre ++ c₀ :: post := by simp
  obtain ⟨⟨a₀, hp₀⟩, hpend₀⟩ := h₂ c₀ hc₀ (p, γ) (by simp [c₀])
  have hpw : p < w.length := h.lt_length hc₀ (e := (p, γ)) (by simp [c₀])
  rw [List.pairwise_append, List.pairwise_cons] at h₅
  -- Every other push of stack `i` in the chains is older than `p`.
  have holder : ∀ c ∈ pre ++ c₀ :: post, ∀ e ∈ c.pushes, c.stack = i → e.1 ≠ p → e.1 < p := by
    intro c hc e he hci hne
    rcases List.mem_append.mp hc with hc | hc
    · exact h₅.2.2 c hc c₀ (by simp) e he (p, γ) (by simp [c₀])
    · rcases List.mem_cons.mp hc with rfl | hc
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd rfl hne
        · exact (List.pairwise_cons.mp ((h₃ c₀ hc₀).pairwise)).1 e he
      · exact absurd hci (hpost c hc)
  -- No push of stack `i` after `p` is pending: stack `i` is back at its height after `p`.
  have hnet : net i (w.extract (p + 1) w.length) = 0 := by
    obtain ⟨-, -, hk⟩ := hpend₀.of_isPushOn ⟨a₀, γ, hp₀⟩
    rw [show w.length - 1 + 1 = w.length by omega] at hk
    have hge := hk (w.extract (p + 1) w.length).length
    rw [List.take_length] at hge
    by_contra hne
    obtain ⟨q, hq, ⟨a, δ, hqa⟩, hqk⟩ := exists_pending_push (u := w.extract (p + 1) w.length) hk
      (lt_of_le_of_ne hge (Ne.symm hne))
    rw [List.extract_eq_take_drop, List.length_take, List.length_drop] at hq
    have hqw : p + 1 + q < w.length := by omega
    have hqa' : w[p + 1 + q]? = some (a, .push i δ) := by
      rwa [List.extract_eq_take_drop, List.getElem?_take_of_lt (by omega),
        List.getElem?_drop] at hqa
    have hqpend : PendingAt w (p + 1 + q) (w.length - 1) := by
      refine ⟨by omega, by omega, i, ⟨a, δ, hqa'⟩, fun k => ?_⟩
      have hd : (w.extract (p + 1) w.length).drop (q + 1) =
          w.extract (p + 1 + q + 1) (w.length - 1 + 1) := by
        rw [List.extract_eq_take_drop, List.extract_eq_take_drop, List.drop_take, List.drop_drop,
          show w.length - (p + 1) - (q + 1) = w.length - 1 + 1 - (p + 1 + q + 1) by omega,
          show p + 1 + (q + 1) = p + 1 + q + 1 by omega]
      exact hd ▸ hqk k
    obtain ⟨c, hc, e, he, he'⟩ := h₄ _ hqpend
    obtain ⟨⟨a', hea⟩, -⟩ := h₂ c hc e he
    have hci : c.stack = i := IsPushOn.unique ⟨a', e.2, hea⟩ ⟨a, δ, he' ▸ hqa'⟩
    have := holder c hc e he hci (by omega)
    omega
  -- The factor up to the pop is the factor up to the end of `w`, then the pop.
  have hsplit : ∀ e, e ≤ w.length →
      w'.extract e (w'.length - 1 + 1) = w.extract e w.length ++ [(b, .pop i γ)] := by
    intro e he
    rw [hlen, show w.length + 1 - 1 + 1 = w.length + 1 by omega,
      ← w'.extract_append_extract he (Nat.le_succ _), List.extract_append_right _ _ le_rfl]
    congr 1
    simp [w', List.extract_eq_take_drop]
  -- `p` is no longer pending after the pop.
  have hpnot : ¬PendingAt w' p (w'.length - 1) := by
    rintro ⟨-, -, j, ⟨a, δ, hj⟩, hk⟩
    rw [List.getElem?_append_left hpw] at hj
    obtain rfl := IsPushOn.unique ⟨a₀, γ, hp₀⟩ ⟨a, δ, hj⟩
    have := hk ((w'.extract (p + 1) (w'.length - 1 + 1)).length)
    rw [List.take_length, hsplit _ (by omega), net_append, hnet] at this
    simp [net, Op.net, c₀] at this
  -- The other pushes stay pending.
  have hstay : ∀ c ∈ pre ++ c₀ :: post, ∀ e ∈ c.pushes, e.1 ≠ p →
      PendingAt w' e.1 (w'.length - 1) := by
    intro c hc e he hne
    obtain ⟨⟨a, hea⟩, hep⟩ := h₂ c hc e he
    have hew : e.1 < w.length := h.lt_length hc he
    refine ⟨by omega, by omega, c.stack, ⟨a, e.2, by rw [List.getElem?_append_left hew, hea]⟩,
      fun k => ?_⟩
    obtain ⟨-, -, hk⟩ := hep.of_isPushOn ⟨a, e.2, hea⟩
    rw [show w.length - 1 + 1 = w.length by omega] at hk
    rw [hsplit _ (by omega), List.take_append, net_append]
    have hk₁ := hk k
    by_cases hkl : k ≤ (w.extract (e.1 + 1) w.length).length
    · rw [show k - (w.extract (e.1 + 1) w.length).length = 0 by omega]
      simpa using hk₁
    rw [List.take_of_length_le (by omega)] at hk₁ ⊢
    have hpopnet : net c.stack (List.take (k - (w.extract (e.1 + 1) w.length).length)
        [(b, Op.pop i γ)]) = if c.stack = i then -1 else 0 := by
      rw [List.take_of_length_le (by simp only [List.length_singleton]; omega)]
      by_cases hci : c.stack = i <;> simp [net, Op.net, hci, Ne.symm]
    rw [hpopnet]
    split_ifs with hci
    · -- Stack `i` is at least one above its height after `e`: the push at `p` is pending.
      have hlt := holder c hc e he hci hne
      have hsum : net i (w.extract (e.1 + 1) w.length) =
          net i (w.extract (e.1 + 1) p) + 1 + net i (w.extract (p + 1) w.length) := by
        rw [← w.extract_append_extract (show e.1 + 1 ≤ p by omega) (show p ≤ w.length by omega),
          ← w.extract_append_extract (show p ≤ p + 1 by omega) (show p + 1 ≤ w.length by omega),
          List.extract_eq_singleton hp₀]
        simp [net, Op.net, add_assoc, c₀]
      have hpre := hk (p - (e.1 + 1))
      rw [w.take_extract (show e.1 + 1 ≤ p by omega) (show p ≤ w.length by omega)] at hpre
      rw [hci] at hk₁ hpre ⊢
      omega
    · simpa using hk₁
  have hps : ∀ e ∈ ps, e.1 < p :=
    (List.pairwise_cons.mp ((h₃ c₀ hc₀).pairwise)).1
  -- Each push of the new chains is a push of the old chains other than `p`.
  have hmap : ∀ c ∈ pre ++ ⟨i, ps⟩ :: post, ∀ e ∈ c.pushes,
      ∃ c' ∈ pre ++ c₀ :: post, e ∈ c'.pushes ∧ c'.stack = c.stack ∧ e.1 ≠ p := by
    intro c hc e he
    rcases List.mem_append.mp hc with hc | hc
    · refine ⟨c, by simp [hc], he, rfl, ?_⟩
      have := h₅.2.2 c hc c₀ (by simp) e he (p, γ) (by simp [c₀])
      omega
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨c₀, hc₀, List.mem_cons_of_mem _ he, rfl, by have := hps e he; omega⟩
      · refine ⟨c, by simp [hc], he, rfl, ?_⟩
        have := h₅.2.1.1 c hc (p, γ) (by simp [c₀]) e he
        omega
  refine ⟨by simpa using h₁, fun c hc e he => ?_, fun c hc => ?_, fun q hq => ?_, ?_⟩
  · obtain ⟨c', hc', he', hst, hne⟩ := hmap c hc e he
    obtain ⟨⟨a, hea⟩, -⟩ := h₂ c' hc' e he'
    refine ⟨⟨a, ?_⟩, hstay c' hc' e he' hne⟩
    rw [List.getElem?_append_left (h.lt_length hc' he'), hea, hst]
  · have hpos : ∀ e ∈ c.pushes, e.1 < w.length := fun e he => by
      obtain ⟨c', hc', he', -⟩ := hmap c hc e he
      exact h.lt_length hc' he'
    refine chained_append ?_ hpos
    rcases List.mem_append.mp hc with hc | hc
    · exact h₃ c (by simp [hc])
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact (h₃ c₀ hc₀).tail
      · exact h₃ c (by simp [hc])
  · have hqw : q < w.length := by
      by_contra hqw
      obtain ⟨hqx, -, j, ⟨a, δ, hqa⟩, -⟩ := hq
      rw [hlen] at hqx
      obtain rfl : q = w.length := by omega
      simp [w'] at hqa
    obtain ⟨c, hc, e, he, rfl⟩ := h₄ q ((pendingAt_append_iff (by omega)).mp
      (hq.anti (y := w.length - 1) (by omega) (by rw [hlen]; omega)))
    have hne : e.1 ≠ p := fun h' => hpnot (h' ▸ hq)
    rcases List.mem_append.mp hc with hc | hc
    · exact ⟨c, by simp [hc], e, he, rfl⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd rfl hne
        · exact ⟨⟨i, ps⟩, by simp, e, he, rfl⟩
      · exact ⟨c, by simp [hc], e, he, rfl⟩
  · rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨h₅.1, ⟨fun c hc e he e' he' => h₅.2.1.1 c hc e (List.mem_cons_of_mem _ he) e' he',
      h₅.2.1.2⟩, fun c hc c' hc' e he e' he' => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact h₅.2.2 c hc c₀ (by simp) e he e' (List.mem_cons_of_mem _ he')
    · exact h₅.2.2 c hc c' (by simp [hc']) e he e' he'

/-- Closing a hole without pending pushes. -/
theorem HoleBoundary.close {pre post : List (HoleChain n Γ)} {i : Fin n}
    (h : HoleBoundary K w (pre ++ ⟨i, []⟩ :: post)) : HoleBoundary K w (pre ++ post) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have hsub : ∀ c ∈ pre ++ post, c ∈ pre ++ ⟨i, []⟩ :: post := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc <;> simp [hc]
  refine ⟨by simp at h₁ ⊢; omega, fun c hc => h₂ c (hsub c hc), fun c hc => h₃ c (hsub c hc),
    fun q hq => ?_, h₅.sublist ((List.sublist_cons_self _ post).append_left pre)⟩
  obtain ⟨c, hc, e, he, rfl⟩ := h₄ q hq
  rcases List.mem_append.mp hc with hc | hc
  · exact ⟨c, by simp [hc], e, he, rfl⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at he
    · exact ⟨c, by simp [hc], e, he, rfl⟩

/-- A hole block opens a new chain. -/
theorem HoleBlock.boundary {i : Fin n} {L : ℕ} {v : List (α × Op n Γ)} {ps : List (ℕ × Γ)}
    (hb : HoleBlock i L v ps) :
    ∀ {w : List (α × Op n Γ)} {C : List (HoleChain n Γ)}, w.length = L → C.length < K →
      HoleBoundary K w C → (∀ x < w.length, ∃ Cx, Snapshot K w x Cx) →
      HoleBoundary K (w ++ v) (C ++ [⟨i, ps⟩]) ∧
        (∀ x < (w ++ v).length, ∃ Cx, Snapshot K (w ++ v) x Cx) ∧
        ∀ e ∈ ps.head?, WellNested ((w ++ v).extract (e.1 + 1) (w ++ v).length) := by
  induction hb with
  | nil =>
    intro w C hL hC h hs
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    simp only [List.append_nil]
    refine ⟨⟨by simp; omega, fun c hc e he => ?_, fun c hc => ?_, fun q hq => ?_, ?_⟩, hs,
      by simp⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact h₂ c hc e he
      · simp [List.mem_singleton.mp hc] at he
    · rcases List.mem_append.mp hc with hc | hc
      · exact h₃ c hc
      · simp [List.mem_singleton.mp hc, Chained]
    · obtain ⟨c, hc, e, he, rfl⟩ := h₄ q hq
      exact ⟨c, by simp [hc], e, he, rfl⟩
    · rw [List.pairwise_append]
      exact ⟨h₅, by simp, by simp⟩
  | @snoc v ws ps a γ _ hws ih =>
    intro w C hL hC h hs
    obtain ⟨hB, hS, hlink⟩ := ih hL hC h hs
    have hW : (w ++ v).length = L + v.length := by simp [hL]
    have hB' := hB.append_push (a := a) (γ := γ) hlink
    rw [hW] at hB'
    obtain ⟨hB'', hS''⟩ := hB'.append_wellNested hws
    have heq : w ++ (v ++ (a, Op.push i γ) :: ws) = w ++ v ++ [(a, .push i γ)] ++ ws := by simp
    rw [heq]
    refine ⟨hB'', fun x hx => ?_, fun e he => ?_⟩
    · by_cases hx₁ : x < (w ++ v).length
      · obtain ⟨Cx, hCx⟩ := hS x hx₁
        exact ⟨Cx, (hCx.append (v := [(a, .push i γ)]) hx₁).append (by simp; omega)⟩
      by_cases hx₂ : x = (w ++ v).length
      · have hidx : (w ++ v ++ [(a, Op.push i γ)]).length - 1 = x := by simp [hx₂]
        exact ⟨_, hidx ▸ hB'.snapshot.append (v := ws) (by simp)⟩
      · exact ⟨_, hS'' x (by simp at hx₁ ⊢; omega) hx⟩
    · obtain rfl := Option.mem_some_iff.mp he
      have hlen' : L + v.length + 1 = (w ++ v ++ [(a, Op.push i γ)]).length := by
        simp [hL, add_assoc]
      rw [hlen', List.extract_eq_take_drop, List.drop_left' rfl,
        List.take_of_length_le (by simp; omega)]
      exact hws

/-- The invariant of hole derivations: the open chains at the end, and a snapshot at every
position. -/
theorem HoleDerivation.invariant {K : ℕ} {C : List (HoleChain n Γ)} {w : List (α × Op n Γ)}
    (h : HoleDerivation K C w) :
    HoleBoundary K w C ∧ ∀ x < w.length, ∃ Cx, Snapshot K w x Cx := by
  induction h with
  | nil =>
    refine ⟨⟨by simp, by simp, by simp, fun q hq => ?_, by simp⟩, by simp⟩
    exact absurd hq.2.1 (by simp)
  | @wellNested C w v _ hv ih =>
    obtain ⟨hB, hS⟩ := ih
    obtain ⟨hB', hS'⟩ := hB.append_wellNested hv
    refine ⟨hB', fun x hx => ?_⟩
    by_cases hx₁ : x < w.length
    · obtain ⟨Cx, hCx⟩ := hS x hx₁
      exact ⟨Cx, hCx.append hx₁⟩
    · exact ⟨_, hS' x (by omega) hx⟩
  | hole _ hC hb ih =>
    obtain ⟨hB, hS⟩ := ih
    obtain ⟨hB', hS', -⟩ := hb.boundary rfl hC hB hS
    exact ⟨hB', hS'⟩
  | @pop pre post w ps i p γ b _ hpost ih =>
    obtain ⟨hB, hS⟩ := ih
    have hB' := hB.append_pop (b := b) hpost
    refine ⟨hB', fun x hx => ?_⟩
    by_cases hx₁ : x < w.length
    · obtain ⟨Cx, hCx⟩ := hS x hx₁
      exact ⟨Cx, hCx.append hx₁⟩
    · have hidx : (w ++ [(b, Op.pop i γ)]).length - 1 = x := by
        simp at hx hx₁ ⊢
        omega
      exact ⟨_, hidx ▸ hB'.snapshot⟩
  | close _ ih => exact ⟨ih.1.close, ih.2⟩

/-- **Words built by hole derivations are hole-bounded**: a hole derivation with at most `K` open
holes builds a `K`-hole-bounded sequence. -/
theorem HoleDerivation.holeBounded {K : ℕ} {C : List (HoleChain n Γ)} {w : List (α × Op n Γ)}
    (h : HoleDerivation K C w) : HoleBounded K w := fun x hx => by
  obtain ⟨Cx, hCx⟩ := h.invariant.2 x hx
  exact hCx.openHoles_le.trans hCx.1

end Invariant

end Cslib.Automata.MPDA
