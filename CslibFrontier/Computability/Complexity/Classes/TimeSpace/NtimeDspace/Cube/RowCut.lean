/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PieceFacts
public import Mathlib.Data.Int.Interval

/-!
# Two cuts (Lemma 5.4 and Corollary 5.5)

`nUp_lower` and `nDown_lower` are the exponent bounds of Lemma 5.4: every exponent of
`N↑(x, y; m)` is at least `wt m - (wt x + wt y)`, and every exponent of `N↓(u, v; m)` at least
`wt m - (wt u + wt v)`. `rowCut_finsum` is the identity of Lemma 5.4 in `ℤ((z))`, coefficientwise:
for views with `wt x = wt v = a` and `wt y = wt u = b`, `H = a + b`, and every integer `e`, the
coefficient of `z^e` in `Π` is that of `∑_m N↑(x, y; m) · N↓(u, v; m)`, a sum over all messages
with finitely many nonzero terms; `rowCut_coeff` is the same sum over the messages of weight at
most `(2H + e)/2`, the only ones that contribute (`wt_le_of_coeff_ne_zero`). `rowCut` and
`colCut` are Corollary 5.5: for every `k` (every even `k` for the column cut),

  `Π_k = ∑_{m ∈ Λ_≤(H + k/2)} ∑_c [z^{k-c}] N↑(x, y; m) · [z^c] N↓(u, v; m)`        (row cut),
  `Π_k = ∑_{m ∈ Λ_≤(H - k/2)} ∑_c [z^{-k-c}] N↑(x, u; m) · [z^c] N↓(y, v; m)`       (column cut),

where `c` runs over `wt m - H ≤ c ≤ H ± k - wt m` (only these `c` contribute). For the
coefficient of `z^e`, the proof replaces the diagonal rule `[i = j]` by `[i = j](1 - z^{2^{L+1}})`
with `L = 2H + max(e, 0)`, which changes only exponents above `e`, inserts an intermediate type
into every request between the rows by the finite Walsh–Hadamard form `sum_C_mul_C`, and glues
half-routings by the multinomial expansion of the source forms, with message types below `2^L`
and multiplicities at most `L + 1`.

## Proof structure

* `transport_zero`, `transport_cons`: the recursion of a transport sum (the first source chooses
  its target); `transport_congr`, `transport_map` (renaming places).
* `LB b f` (every exponent of `f` is at least `b`) and `transport_lb`: if every rule `R s t` has
  exponents at least `φ s + φ t`, the transport sum has exponents at least the total of `φ`.
  With `φw` (a corner occurrence counts `-(i + 1)`, a message request `n + 1`) this gives
  `nUp_lower` and `nDown_lower`. `transport_sub_lb` compares two transport sums whose rules differ
  only in high exponents.
* `glue`: **the gluing lemma**, for an abstract cut place `o`. If the rules within each row are
  those of the half-transports and every rule across the cut is `∑_{n < N}` of an upper half-rule
  times a lower one, the transport sum equals `glueRHS`, the sum over messages `(η, ζ)` (types
  below `N`, multiplicities at most `K`) of the upper half-transport times the lower one. The
  proof is an induction on the sources: a source sending down a request of type `n` matches a
  message `n ::ₘ η`, reindexed by `sum_msgs_reindex`; `card_le_of_transport_ne_zero` bounds the
  messages that can occur.
* `rowCut`: the routing polynomial is a transport on the places `some c` (`piece_eq_transport`);
  replacing the diagonal rule `[i = j]` by its finite form `[i = j](1 - z^{2^{L+1}})`
  (`ruleCut`, via `sum_C_mul_C`) changes only exponents above `2H` (`transport_sub_lb`), and the
  modified rules satisfy the gluing hypotheses (`glueHyp_piece`). The exponent bounds then cut
  the sum over messages down to `Λ_≤(H + k/2)` and the convolution to the window of `c`
  (`coeff_mul_eq_sum_Icc`). `colCut` is the row cut of the transposed rectangle
  (`piece_transpose`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset LaurentPolynomial

section TransportRec

variable {P : Type} [DecidableEq P]

/-- The transport sum with source forms over an arbitrary finite set `F` of targets. -/
noncomputable def transportOn (F : Finset (P × ℕ)) (src tgt : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) : Lp :=
  ((src.map fun s : P ×
      ℕ => ∑ t ∈ F, MvPolynomial.C (R s.1 s.2 t.1 t.2) * MvPolynomial.X t).prod).coeff
    (Multiset.toFinsupp tgt)

theorem toFinsupp_sub_single (tgt : Multiset (P × ℕ)) (t : P × ℕ) :
    Multiset.toFinsupp tgt - Finsupp.single t 1 = Multiset.toFinsupp (tgt.erase t) := by
  ext a
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Finsupp.single_apply]
  by_cases ha : t = a
  · subst ha; rw [Multiset.count_erase_self]; simp
  · rw [Multiset.count_erase_of_ne (Ne.symm ha)]; simp [ha]

theorem transportOn_zero (F : Finset (P × ℕ)) (tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    transportOn F 0 tgt R = if tgt = 0 then 1 else 0 := by
  unfold transportOn
  rw [Multiset.map_zero, Multiset.prod_zero, MvPolynomial.coeff_one]
  by_cases h : tgt = 0
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    apply h
    have : Multiset.toFinsupp tgt = Multiset.toFinsupp 0 := by rw [← h']; simp
    exact Multiset.toFinsupp.injective this

theorem transportOn_cons (F : Finset (P × ℕ)) (s : P × ℕ) (src tgt : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) :
    transportOn F (s ::ₘ src) tgt R =
      ∑ t ∈ F, R s.1 s.2 t.1 t.2 * (if t ∈ tgt then transportOn F src (tgt.erase t) R else 0) := by
  unfold transportOn
  rw [Multiset.map_cons, Multiset.prod_cons, Finset.sum_mul, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul', Multiset.toFinsupp_support]
  simp only [Multiset.mem_toFinset]
  split_ifs with h
  · rw [toFinsupp_sub_single]
  · rfl

theorem transportOn_cons' (F : Finset (P × ℕ)) (s : P × ℕ) (src tgt : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) (hF : tgt.toFinset ⊆ F) :
    transportOn F (s ::ₘ src) tgt R =
      ∑ t ∈ tgt.toFinset, R s.1 s.2 t.1 t.2 * transportOn F src (tgt.erase t) R := by
  rw [transportOn_cons]
  symm
  refine Finset.sum_subset_zero_on_sdiff hF (fun t ht => ?_) (fun t ht => ?_)
  · rw [Finset.mem_sdiff, Multiset.mem_toFinset] at ht
    rw [ite_eq_right ht.2, mul_zero]
  · rw [ite_eq_left (Multiset.mem_toFinset.mp ht)]

theorem transportOn_congr (R : P → ℕ → P → ℕ → Lp) (src : Multiset (P × ℕ)) :
    ∀ (tgt : Multiset (P × ℕ)) (F F' : Finset (P × ℕ)), tgt.toFinset ⊆ F → tgt.toFinset ⊆ F' →
      transportOn F src tgt R = transportOn F' src tgt R := by
  induction src using Multiset.induction_on with
  | empty => intro tgt F F' _ _; rw [transportOn_zero, transportOn_zero]
  | cons s src ih =>
    intro tgt F F' hF hF'
    rw [transportOn_cons' F s src tgt R hF, transportOn_cons' F' s src tgt R hF']
    refine Finset.sum_congr rfl fun t _ => ?_
    have hsub : (tgt.erase t).toFinset ⊆ tgt.toFinset :=
      Multiset.toFinset_subset.mpr (Multiset.erase_subset _ _)
    rw [ih _ F F' (hsub.trans hF) (hsub.trans hF')]

theorem transport_eq_transportOn (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    transport src tgt R = transportOn tgt.toFinset src tgt R := rfl

/-- The empty transport. -/
theorem transport_zero (tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    transport 0 tgt R = if tgt = 0 then 1 else 0 := transportOn_zero _ _ _

/-- **The recursion of a transport sum**: the first source chooses its target. -/
theorem transport_cons (s : P × ℕ) (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    transport (s ::ₘ src) tgt R =
      ∑ t ∈ tgt.toFinset, R s.1 s.2 t.1 t.2 * transport src (tgt.erase t) R := by
  rw [transport_eq_transportOn, transportOn_cons' _ _ _ _ _ subset_rfl]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [transport_eq_transportOn, transportOn_congr R src (tgt.erase t) _ _
    (Multiset.toFinset_subset.mpr (Multiset.erase_subset _ _)) subset_rfl]

/-- A transport sum only reads its rules on actual sources and targets. -/
theorem transport_congr (R R' : P → ℕ → P → ℕ → Lp) (src : Multiset (P × ℕ)) :
    ∀ tgt : Multiset (P × ℕ), (∀ s ∈ src, ∀ t ∈ tgt, R s.1 s.2 t.1 t.2 = R' s.1 s.2 t.1 t.2) →
      transport src tgt R = transport src tgt R' := by
  induction src using Multiset.induction_on with
  | empty => intro tgt _; rw [transport_zero, transport_zero]
  | cons s src ih =>
    intro tgt h
    rw [transport_cons, transport_cons]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h s (Multiset.mem_cons_self _ _) t (Multiset.mem_toFinset.mp ht),
      ih _ fun s' hs' t' ht' => h s' (Multiset.mem_cons_of_mem hs') t'
        (Multiset.mem_of_mem_erase ht')]

/-- Renaming the places of a transport by an injective map. -/
theorem transport_map {Q : Type} [DecidableEq Q] (f : P → Q) (hf : Function.Injective f)
    (R : Q → ℕ → Q → ℕ → Lp) (src : Multiset (P × ℕ)) :
    ∀ tgt : Multiset (P × ℕ),
      transport (src.map fun s => (f s.1, s.2)) (tgt.map fun t => (f t.1, t.2)) R =
        transport src tgt fun p i p' j => R (f p) i (f p') j := by
  have hg : Function.Injective fun t : P × ℕ => (f t.1, t.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    rw [hf h.1, h.2]
  induction src using Multiset.induction_on with
  | empty => intro tgt; rw [Multiset.map_zero, transport_zero, transport_zero]; simp
  | cons s src ih =>
    intro tgt
    rw [Multiset.map_cons, transport_cons, transport_cons, Multiset.toFinset_map,
      Finset.sum_image fun x _ y _ h => hg h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Multiset.map_erase _ hg, ih]

end TransportRec


/-! ### Lower bounds for exponents -/

/-- Every exponent of `f` is at least `b`. -/
def LB (b : ℤ) (f : Lp) : Prop := ∀ e, f.coeff e ≠ 0 → b ≤ e

theorem LB.zero (b : ℤ) : LB b 0 := fun _ h => absurd rfl h

theorem LB.mono {b b' : ℤ} {f : Lp} (h : LB b f) (hb : b' ≤ b) : LB b' f :=
  fun e he => hb.trans (h e he)

theorem LB.add {b : ℤ} {f g : Lp} (hf : LB b f) (hg : LB b g) : LB b (f + g) := fun e h => by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  by_cases h1 : f.coeff e = 0
  · rw [h1, zero_add] at h; exact hg e h
  · exact hf e h1

theorem LB.neg {b : ℤ} {f : Lp} (hf : LB b f) : LB b (-f) := fun e h => by
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, neg_ne_zero] at h
  exact hf e h

theorem LB.sub {b : ℤ} {f g : Lp} (hf : LB b f) (hg : LB b g) : LB b (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem LB.mul {b c : ℤ} {f g : Lp} (hf : LB b f) (hg : LB c g) : LB (b + c) (f * g) := by
  classical
  intro e h
  rw [AddMonoidAlgebra.coeff_mul] at h
  obtain ⟨m1, hm1, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨m2, hm2, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  simp only at h2
  split_ifs at h2 with he
  · have := hf m1 (Finsupp.mem_support_iff.mp hm1)
    have := hg m2 (Finsupp.mem_support_iff.mp hm2)
    omega
  · exact absurd rfl h2

theorem LB.sum {ι : Type*} {b : ℤ} (s : Finset ι) (f : ι → Lp) (h : ∀ i ∈ s, LB b (f i)) :
    LB b (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact LB.zero b
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LB.T (n : ℤ) : LB n (T n) := fun e h => by
  rw [T_apply] at h
  split_ifs at h with h'
  · exact h'.le
  · exact absurd rfl h

theorem LB.one : LB 0 1 := by rw [← T_zero]; exact LB.T 0

theorem LB.C (a : ℤ) : LB 0 (LaurentPolynomial.C a) := fun e h => by
  rw [C_apply] at h
  split_ifs at h with h'
  · exact h'.ge
  · exact absurd rfl h

theorem LB.C_mul {b : ℤ} {f : Lp} (a : ℤ) (h : LB b f) : LB b (LaurentPolynomial.C a * f) := by
  have := (LB.C a).mul h; rwa [zero_add] at this

/-! ### General facts on transport sums -/

section TransportFacts

variable {P : Type} [DecidableEq P]

/-- **The exponent bound of a transport sum.** If every rule `R s t` has exponents at least
`φ s + φ t`, the transport sum has exponents at least the sum of `φ` over sources and targets. -/
theorem transport_lb (φ : P × ℕ → ℤ) (R : P → ℕ → P → ℕ → Lp) (src : Multiset (P × ℕ)) :
    ∀ tgt : Multiset (P × ℕ), (∀ s ∈ src, ∀ t ∈ tgt, LB (φ s + φ t) (R s.1 s.2 t.1 t.2)) →
      LB ((src.map φ).sum + (tgt.map φ).sum) (transport src tgt R) := by
  induction src using Multiset.induction_on with
  | empty =>
    intro tgt _
    rw [transport_zero]
    split_ifs with h
    · subst h; simpa using LB.one
    · exact LB.zero _
  | cons s src ih =>
    intro tgt h
    rw [transport_cons]
    refine LB.sum _ _ fun t ht => ?_
    have ht' := Multiset.mem_toFinset.mp ht
    refine ((h s (Multiset.mem_cons_self _ _) t ht').mul (ih (tgt.erase t) fun s' hs' t' ht'' =>
      h s' (Multiset.mem_cons_of_mem hs') t' (Multiset.mem_of_mem_erase ht''))).mono (le_of_eq ?_)
    rw [Multiset.map_cons, Multiset.sum_cons, ← Multiset.sum_map_erase ht']
    ring

/-- **Comparing two transport sums.** If `R` and `R'` differ on every pair by exponents at least
`φ s + φ t + M`, then so do their transport sums, by the total plus `M`. -/
theorem transport_sub_lb (φ : P × ℕ → ℤ) (M : ℤ) (hM : 0 ≤ M) (R R' : P → ℕ → P → ℕ → Lp)
    (src : Multiset (P × ℕ)) :
    ∀ tgt : Multiset (P × ℕ), (∀ s ∈ src, ∀ t ∈ tgt, LB (φ s + φ t) (R s.1 s.2 t.1 t.2)) →
      (∀ s ∈ src, ∀ t ∈ tgt,
        LB (φ s + φ t + M) (R s.1 s.2 t.1 t.2 - R' s.1 s.2 t.1 t.2)) →
      LB ((src.map φ).sum + (tgt.map φ).sum + M) (transport src tgt R - transport src tgt R') := by
  induction src using Multiset.induction_on with
  | empty => intro tgt _ _; rw [transport_zero, transport_zero, sub_self]; exact LB.zero _
  | cons s src ih =>
    intro tgt h h'
    rw [transport_cons, transport_cons, ← Finset.sum_sub_distrib]
    refine LB.sum _ _ fun t ht => ?_
    have ht' := Multiset.mem_toFinset.mp ht
    have hs := Multiset.mem_cons_self s src
    have hsum : φ s + φ t + ((src.map φ).sum + ((tgt.erase t).map φ).sum) =
        ((s ::ₘ src).map φ).sum + (tgt.map φ).sum := by
      rw [Multiset.map_cons, Multiset.sum_cons, ← Multiset.sum_map_erase ht']; ring
    have hR := h s hs t ht'
    have hD := h' s hs t ht'
    have hR' : LB (φ s + φ t) (R' s.1 s.2 t.1 t.2) := by
      have := hR.sub (hD.mono (by omega)); rwa [sub_sub_cancel] at this
    have h1 := transport_lb φ R src (tgt.erase t) fun s' hs' t' ht'' =>
      h s' (Multiset.mem_cons_of_mem hs') t' (Multiset.mem_of_mem_erase ht'')
    have h2 := ih (tgt.erase t) (fun s' hs' t' ht'' =>
      h s' (Multiset.mem_cons_of_mem hs') t' (Multiset.mem_of_mem_erase ht''))
      (fun s' hs' t'
          ht'' => h' s' (Multiset.mem_cons_of_mem hs') t' (Multiset.mem_of_mem_erase ht''))
    have e : R s.1 s.2 t.1 t.2 * transport src (tgt.erase t) R -
        R' s.1 s.2 t.1 t.2 * transport src (tgt.erase t) R' =
        (R s.1 s.2 t.1 t.2 - R' s.1 s.2 t.1 t.2) * transport src (tgt.erase t) R +
        R' s.1 s.2 t.1 t.2 * (transport src (tgt.erase t) R - transport src (tgt.erase t) R') := by
      ring
    rw [e]
    refine LB.add ((hD.mul h1).mono (le_of_eq ?_)) ((hR'.mul h2).mono (le_of_eq ?_))
    · rw [← hsum]; ring
    · rw [← hsum]; ring

/-- **Counting.** If no rule joins two requests at the place `o`, a nonzero transport sum has at
most as many targets at `o` as sources elsewhere. -/
theorem card_le_of_transport_ne_zero (o : P) (R : P → ℕ → P → ℕ → Lp)
    (hR : ∀ i j, R o i o j = 0) (src : Multiset (P × ℕ)) :
    ∀ tgt : Multiset (P × ℕ), transport src tgt R ≠ 0 →
      Multiset.card (tgt.filter fun t => t.1 = o) ≤
        Multiset.card (src.filter fun s => s.1 ≠ o) := by
  induction src using Multiset.induction_on with
  | empty =>
    intro tgt h
    rw [transport_zero] at h
    split_ifs at h with h'
    · subst h'; simp
    · exact absurd rfl h
  | cons s src ih =>
    intro tgt h
    rw [transport_cons] at h
    obtain ⟨t, ht, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have ht' := Multiset.mem_toFinset.mp ht
    have hRt := left_ne_zero_of_mul h1
    have hi := ih _ (right_ne_zero_of_mul h1)
    rw [← Multiset.cons_erase ht', Multiset.filter_cons, Multiset.filter_cons]
    by_cases hto : t.1 = o
    · have hso : s.1 ≠ o := by
        intro hso; apply hRt; rw [hso, hto]; exact hR _ _
      rw [ite_eq_left hto, ite_eq_left hso]
      simp only [Multiset.singleton_add, Multiset.card_cons]
      omega
    · rw [ite_eq_right hto]
      simp only [zero_add]
      split_ifs <;> simp only [Multiset.singleton_add, Multiset.card_cons, zero_add] <;> omega

end TransportFacts


/-! ### Gluing two half-transports through messages -/

section Glue

variable {P : Type} [DecidableEq P]

/-- The multiset bounding the messages: every type below `N`, each `K` times. -/
noncomputable def msgBound (N K : ℕ) : Multiset ℕ :=
  ∑ n ∈ Finset.range N, Multiset.replicate K n

/-- The messages with types below `N` and multiplicities at most `K`. -/
noncomputable def msgs (N K : ℕ) : Finset (Multiset ℕ) := (msgBound N K).powerset.toFinset

theorem count_msgBound (N K n : ℕ) : (msgBound N K).count n = if n < N then K else 0 := by
  unfold msgBound
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]

theorem mem_msgs {N K : ℕ} {η : Multiset ℕ} :
    η ∈ msgs N K ↔ ∀ n, η.count n ≤ if n < N then K else 0 := by
  unfold msgs
  rw [Multiset.mem_toFinset, Multiset.mem_powerset, Multiset.le_iff_count]
  simp only [count_msgBound]

theorem zero_mem_msgs (N K : ℕ) : (0 : Multiset ℕ) ∈ msgs N K :=
  mem_msgs.mpr fun n => by simp

theorem lt_of_mem_msgs {N K : ℕ} {η : Multiset ℕ} (h : η ∈ msgs N K) {n : ℕ} (hn : n ∈ η) :
    n < N := by
  have := mem_msgs.mp h n
  have hc := Multiset.count_pos.mpr hn
  split_ifs at this with h'
  · exact h'
  · omega

theorem erase_mem_msgs {N K : ℕ} {η : Multiset ℕ} (h : η ∈ msgs N K) (n : ℕ) :
    η.erase n ∈ msgs N K :=
  mem_msgs.mpr fun m => (Multiset.count_le_of_le _ (Multiset.erase_le _ _)).trans (mem_msgs.mp h m)

theorem card_of_cons_not_mem_msgs {N K : ℕ} {η : Multiset ℕ} (h : η ∈ msgs N K) {n : ℕ}
    (hn : n < N) (hc : n ::ₘ η ∉ msgs N K) : K ≤ Multiset.card η := by
  rw [mem_msgs] at hc
  push Not at hc
  obtain ⟨m, hm⟩ := hc
  have hη := mem_msgs.mp h m
  by_cases hmn : m = n
  · subst hmn
    rw [Multiset.count_cons_self, ite_eq_left hn] at hm
    rw [ite_eq_left hn] at hη
    have : η.count m = K := by omega
    rw [← this]; exact Multiset.count_le_card _ _
  · rw [Multiset.count_cons_of_ne hmn] at hm
    omega

theorem located_cons {Q : Type} (p : Q) (n : ℕ) (σ : Multiset ℕ) :
    located p (n ::ₘ σ) = (p, n) ::ₘ located p σ := Multiset.map_cons _ _ _

theorem mem_located {Q : Type} {p : Q} {σ : Multiset ℕ} {t : Q × ℕ} :
    t ∈ located p σ ↔ ∃ i ∈ σ, (p, i) = t := Multiset.mem_map

theorem card_filter_eq_located (o : P) (A : Multiset (P × ℕ)) (η : Multiset ℕ)
    (hA : ∀ t ∈ A, t.1 ≠ o) :
    Multiset.card ((A + located o η).filter fun t => t.1 = o) = Multiset.card η := by
  rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr hA, zero_add,
    Multiset.filter_eq_self.mpr, located, Multiset.card_map]
  intro t ht
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ht
  rfl

theorem card_filter_ne_located (o : P) (A : Multiset (P × ℕ)) (η : Multiset ℕ)
    (hA : ∀ t ∈ A, t.1 ≠ o) :
    Multiset.card ((A + located o η).filter fun t => t.1 ≠ o) = Multiset.card A := by
  rw [Multiset.filter_add, Multiset.filter_eq_self.mpr hA, Multiset.filter_eq_nil.mpr, add_zero]
  intro t ht
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ht
  simp

/-- A nonzero half-transport sends at most as many requests to the cut as it has corner
sources. -/
theorem card_msg_le (o : P) (R : P → ℕ → P → ℕ → Lp) (hR : ∀ i j, R o i o j = 0)
    (A B : Multiset (P × ℕ)) (ζ η : Multiset ℕ) (hA : ∀ t ∈ A, t.1 ≠ o)
    (hB : ∀ t ∈ B, t.1 ≠ o) (h : transport (A + located o ζ) (B + located o η) R ≠ 0) :
    Multiset.card η ≤ Multiset.card A := by
  have := card_le_of_transport_ne_zero o R hR _ _ h
  rwa [card_filter_eq_located o B η hB, card_filter_ne_located o A ζ hA] at this

/-- Expanding the first source of a transport whose targets are `A` and messages `η` at `o`. -/
theorem transport_cons_split (o : P) (R : P → ℕ → P → ℕ → Lp) (s : P × ℕ)
    (A B : Multiset (P × ℕ)) (η : Multiset ℕ) (hA : ∀ t ∈ A, t.1 ≠ o) :
    transport (s ::ₘ B) (A + located o η) R =
      ∑ t ∈ A.toFinset, R s.1 s.2 t.1 t.2 * transport B (A.erase t + located o η) R +
      ∑ n ∈ η.toFinset, R s.1 s.2 o n * transport B (A + located o (η.erase n)) R := by
  rw [transport_cons, Multiset.toFinset_add, Finset.sum_union]
  · congr 1
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [Multiset.erase_add_left_pos _ (Multiset.mem_toFinset.mp ht)]
    · rw [located, Multiset.toFinset_map,
        Finset.sum_image fun x _ y _ h => (Prod.mk_right_injective o) h]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Multiset.erase_add_right_pos _ (Multiset.mem_map_of_mem _ (Multiset.mem_toFinset.mp hn)),
        ← Multiset.map_erase _ (Prod.mk_right_injective o)]
      rfl
  · rw [Finset.disjoint_left]
    intro t ht ht'
    rw [Multiset.mem_toFinset] at ht ht'
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ht'
    exact hA _ ht rfl

/-- The hypotheses of the gluing lemma: upper sources and targets `Su`, `Tu`, lower ones `Sd`,
`Td`, none at the cut `o`; the rule `R` is the upper rule `ru` within the upper row, the lower
rule `rd` within the lower row, and a sum over an intermediate type `n < N` across the cut. -/
structure GlueHyp (o : P) (ru rd R : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (Su Sd Tu Td : Multiset (P × ℕ)) : Prop where
  neSu : ∀ p ∈ Su, p.1 ≠ o
  neSd : ∀ p ∈ Sd, p.1 ≠ o
  neTu : ∀ p ∈ Tu, p.1 ≠ o
  neTd : ∀ p ∈ Td, p.1 ≠ o
  disj : ∀ t ∈ Tu, ∀ t' ∈ Td, t ≠ t'
  uu : ∀ s ∈ Su, ∀ t ∈ Tu, R s.1 s.2 t.1 t.2 = ru s.1 s.2 t.1 t.2
  dd : ∀ s ∈ Sd, ∀ t ∈ Td, R s.1 s.2 t.1 t.2 = rd s.1 s.2 t.1 t.2
  ud : ∀ s ∈ Su, ∀ t ∈ Td, R s.1 s.2 t.1 t.2 = ∑ n ∈ range N, ru s.1 s.2 o n * rd o n t.1 t.2
  du : ∀ s ∈ Sd, ∀ t ∈ Tu, R s.1 s.2 t.1 t.2 = ∑ n ∈ range N, rd s.1 s.2 o n * ru o n t.1 t.2
  cu : Multiset.card Su < K
  cd : Multiset.card Sd < K

omit [DecidableEq P] in
theorem GlueHyp.mono {o : P} {ru rd R : P → ℕ → P → ℕ → Lp} {N K : ℕ}
    {Su Sd Tu Td Su' Sd' Tu' Td' : Multiset (P × ℕ)} (h : GlueHyp o ru rd R N K Su Sd Tu Td)
    (h1 : Su' ≤ Su) (h2 : Sd' ≤ Sd) (h3 : Tu' ≤ Tu) (h4 : Td' ≤ Td) :
    GlueHyp o ru rd R N K Su' Sd' Tu' Td' where
  neSu p hp := h.neSu p (Multiset.subset_of_le h1 hp)
  neSd p hp := h.neSd p (Multiset.subset_of_le h2 hp)
  neTu p hp := h.neTu p (Multiset.subset_of_le h3 hp)
  neTd p hp := h.neTd p (Multiset.subset_of_le h4 hp)
  disj t ht t' ht' := h.disj t (Multiset.subset_of_le h3 ht) t' (Multiset.subset_of_le h4 ht')
  uu s hs t ht := h.uu s (Multiset.subset_of_le h1 hs) t (Multiset.subset_of_le h3 ht)
  dd s hs t ht := h.dd s (Multiset.subset_of_le h2 hs) t (Multiset.subset_of_le h4 ht)
  ud s hs t ht := h.ud s (Multiset.subset_of_le h1 hs) t (Multiset.subset_of_le h4 ht)
  du s hs t ht := h.du s (Multiset.subset_of_le h2 hs) t (Multiset.subset_of_le h3 ht)
  cu := lt_of_le_of_lt (Multiset.card_le_card h1) h.cu
  cd := lt_of_le_of_lt (Multiset.card_le_card h2) h.cd

omit [DecidableEq P] in
theorem GlueHyp.symm {o : P} {ru rd R : P → ℕ → P → ℕ → Lp} {N K : ℕ}
    {Su Sd Tu Td : Multiset (P × ℕ)} (h : GlueHyp o ru rd R N K Su Sd Tu Td) :
    GlueHyp o rd ru R N K Sd Su Td Tu where
  neSu := h.neSd
  neSd := h.neSu
  neTu := h.neTd
  neTd := h.neTu
  disj t ht t' ht' := (h.disj t' ht' t ht).symm
  uu := h.dd
  dd := h.uu
  ud := h.du
  du := h.ud
  cu := h.cd
  cd := h.cu

/-- The glued sum over messages `m = (η, ζ)` of an upper half-transport times a lower one. -/
noncomputable def glueRHS (o : P) (ru rd : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (Su Sd Tu Td : Multiset (P × ℕ)) : Lp :=
  ∑ η ∈ msgs N K, ∑ ζ ∈ msgs N K,
    transport (Su + located o ζ) (Tu + located o η) ru *
      transport (Sd + located o η) (Td + located o ζ) rd

theorem glueRHS_symm (o : P) (ru rd : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (Su Sd Tu Td : Multiset (P × ℕ)) :
    glueRHS o ru rd N K Su Sd Tu Td = glueRHS o rd ru N K Sd Su Td Tu := by
  unfold glueRHS
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem sum_msgs_reindex (N K : ℕ) (G : Multiset ℕ → ℕ → Lp)
    (hG : ∀ η ∈ msgs N K, ∀ n < N, n ::ₘ η ∉ msgs N K → G η n = 0) :
    ∑ η ∈ msgs N K, ∑ n ∈ η.toFinset, G (η.erase n) n =
      ∑ η ∈ msgs N K, ∑ n ∈ range N, G η n := by
  have e1 : ∀ η ∈ msgs N K, ∑ n ∈ η.toFinset, G (η.erase n) n =
      ∑ n ∈ range N, if n ∈ η then G (η.erase n) n else 0 := by
    intro η hη
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Multiset.mem_toFinset, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨lt_of_mem_msgs hη h, h⟩, fun h => h.2⟩
  calc ∑ η ∈ msgs N K, ∑ n ∈ η.toFinset, G (η.erase n) n
      = ∑ η ∈ msgs N K, ∑ n ∈ range N, if n ∈ η then G (η.erase n) n else 0 :=
        Finset.sum_congr rfl e1
    _ = ∑ x ∈ msgs N K ×ˢ range N, if x.2 ∈ x.1 then G (x.1.erase x.2) x.2 else 0 :=
        (Finset.sum_product' (msgs N K) (range N)
          (fun η n => if n ∈ η then G (η.erase n) n else 0)).symm
    _ = ∑ x ∈ (msgs N K ×ˢ range N).filter (fun x => x.2 ∈ x.1), G (x.1.erase x.2) x.2 :=
        (Finset.sum_filter _ _).symm
    _ = ∑ x ∈ (msgs N K ×ˢ range N).filter (fun x => x.2 ::ₘ x.1 ∈ msgs N K), G x.1 x.2 := by
      apply Finset.sum_nbij' (fun x => (x.1.erase x.2, x.2)) (fun x => (x.2 ::ₘ x.1, x.2))
      · rintro ⟨η, n⟩ hx
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
        exact ⟨⟨erase_mem_msgs hx.1.1 n, hx.1.2⟩, by rw [Multiset.cons_erase hx.2]; exact hx.1.1⟩
      · rintro ⟨η, n⟩ hx
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
        exact ⟨⟨hx.2, hx.1.2⟩, Multiset.mem_cons_self _ _⟩
      · rintro ⟨η, n⟩ hx
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
        simp only [Multiset.cons_erase hx.2]
      · rintro ⟨η, n⟩ _
        simp only [Multiset.erase_cons_head]
      · intro _ _; rfl
    _ = ∑ x ∈ msgs N K ×ˢ range N, G x.1 x.2 := by
      refine Finset.sum_filter_of_ne fun x hx hne => ?_
      simp only [Finset.mem_product, Finset.mem_range] at hx
      by_contra hc
      exact hne (hG x.1 hx.1 x.2 hx.2 hc)
    _ = ∑ η ∈ msgs N K, ∑ n ∈ range N, G η n := Finset.sum_product' _ _ _


theorem glue_base (o : P) (ru rd R : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (hu : ∀ i j, ru o i o j = 0) (hd : ∀ i j, rd o i o j = 0) (Tu Td : Multiset (P × ℕ))
    (h : GlueHyp o ru rd R N K 0 0 Tu Td) :
    transport (0 + 0) (Tu + Td) R = glueRHS o ru rd N K 0 0 Tu Td := by
  have h0 : ∀ p ∈ (0 : Multiset (P × ℕ)), p.1 ≠ o := fun p hp => absurd hp (Multiset.notMem_zero _)
  unfold glueRHS
  rw [Finset.sum_eq_single (0 : Multiset ℕ)]
  · rw [Finset.sum_eq_single (0 : Multiset ℕ)]
    · simp only [located, Multiset.map_zero, add_zero, transport_zero, add_eq_zero]
      split_ifs <;> simp_all
    · intro ζ _ hζ
      refine mul_eq_zero_of_right _ ?_
      by_contra hne
      have := card_msg_le o rd hd 0 Td 0 ζ h0 h.neTd hne
      exact hζ (Multiset.card_eq_zero.mp (by simpa using this))
    · intro h0'; exact absurd (zero_mem_msgs N K) h0'
  · intro η _ hη
    refine Finset.sum_eq_zero fun ζ _ => mul_eq_zero_of_left ?_ _
    by_contra hne
    have := card_msg_le o ru hu 0 Tu ζ η h0 h.neTu hne
    exact hη (Multiset.card_eq_zero.mp (by simpa using this))
  · intro h0'; exact absurd (zero_mem_msgs N K) h0'

theorem glue_step (o : P) (ru rd R : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (hd : ∀ i j, rd o i o j = 0) (hu : ∀ i j, ru o i o j = 0)
    (s : P × ℕ) (Su Sd Tu Td : Multiset (P × ℕ))
    (h : GlueHyp o ru rd R N K (s ::ₘ Su) Sd Tu Td)
    (ih : ∀ Tu' Td', GlueHyp o ru rd R N K Su Sd Tu' Td' →
      transport (Su + Sd) (Tu' + Td') R = glueRHS o ru rd N K Su Sd Tu' Td') :
    transport (s ::ₘ Su + Sd) (Tu + Td) R = glueRHS o ru rd N K (s ::ₘ Su) Sd Tu Td := by
  have hs : s ∈ s ::ₘ Su := Multiset.mem_cons_self s Su
  have hle : Su ≤ s ::ₘ Su := Multiset.le_cons_self _ _
  have hSu : ∀ p ∈ Su, p.1 ≠ o := fun p hp => h.neSu p (Multiset.mem_cons_of_mem hp)
  have hL : transport (s ::ₘ Su + Sd) (Tu + Td) R =
      ∑ t ∈ Tu.toFinset, ru s.1 s.2 t.1 t.2 * glueRHS o ru rd N K Su Sd (Tu.erase t) Td +
      ∑ t ∈ Td.toFinset, (∑ n ∈ range N, ru s.1 s.2 o n * rd o n t.1 t.2) *
        glueRHS o ru rd N K Su Sd Tu (Td.erase t) := by
    rw [Multiset.cons_add, transport_cons, Multiset.toFinset_add, Finset.sum_union]
    · congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        have ht' := Multiset.mem_toFinset.mp ht
        rw [h.uu s hs t ht', Multiset.erase_add_left_pos _ ht',
          ih _ _ (h.mono hle le_rfl (Multiset.erase_le _ _) le_rfl)]
      · refine Finset.sum_congr rfl fun t ht => ?_
        have ht' := Multiset.mem_toFinset.mp ht
        rw [h.ud s hs t ht', Multiset.erase_add_right_pos _ ht',
          ih _ _ (h.mono hle le_rfl le_rfl (Multiset.erase_le _ _))]
    · rw [Finset.disjoint_left]
      intro t ht ht'
      exact h.disj t (Multiset.mem_toFinset.mp ht) t (Multiset.mem_toFinset.mp ht') rfl
  have hU : ∀ η ζ : Multiset ℕ, transport (s ::ₘ Su + located o ζ) (Tu + located o η) ru =
      ∑ t ∈ Tu.toFinset, ru s.1 s.2 t.1 t.2 *
        transport (Su + located o ζ) (Tu.erase t + located o η) ru +
      ∑ n ∈ η.toFinset, ru s.1 s.2 o n *
        transport (Su + located o ζ) (Tu + located o (η.erase n)) ru := by
    intro η ζ
    rw [Multiset.cons_add]
    exact transport_cons_split o ru s Tu _ η h.neTu
  have hD : ∀ (n : ℕ) (η ζ : Multiset ℕ),
      transport (Sd + located o (n ::ₘ η)) (Td + located o ζ) rd =
      ∑ t ∈ Td.toFinset, rd o n t.1 t.2 *
        transport (Sd + located o η) (Td.erase t + located o ζ) rd := by
    intro n η ζ
    rw [located_cons, Multiset.add_cons, transport_cons_split o rd (o, n) Td _ ζ h.neTd]
    simp only [hd, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hL]
  unfold glueRHS
  simp only [hU, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · -- reindex the messages sent down by `s`
    have key : ∀ ζ ∈ msgs N K, ∑ η ∈ msgs N K,
        (∑ n ∈ η.toFinset, ru s.1 s.2 o n *
          transport (Su + located o ζ) (Tu + located o (η.erase n)) ru) *
          transport (Sd + located o η) (Td + located o ζ) rd =
        ∑ η ∈ msgs N K, ∑ n ∈ range N, ∑ t ∈ Td.toFinset,
          (ru s.1 s.2 o n * rd o n t.1 t.2) *
          (transport (Su + located o ζ) (Tu + located o η) ru *
            transport (Sd + located o η) (Td.erase t + located o ζ) rd) := by
      intro ζ _
      set G : Multiset ℕ → ℕ → Lp := fun η n => ru s.1 s.2 o n *
        transport (Su + located o ζ) (Tu + located o η) ru *
        transport (Sd + located o (n ::ₘ η)) (Td + located o ζ) rd with hGdef
      have e : ∀ η ∈ msgs N K, (∑ n ∈ η.toFinset, ru s.1 s.2 o n *
          transport (Su + located o ζ) (Tu + located o (η.erase n)) ru) *
          transport (Sd + located o η) (Td + located o ζ) rd =
          ∑ n ∈ η.toFinset, G (η.erase n) n := by
        intro η _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hGdef]
        simp only
        rw [Multiset.cons_erase (Multiset.mem_toFinset.mp hn)]
      rw [Finset.sum_congr rfl e, sum_msgs_reindex N K G]
      · refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun n _ => ?_
        rw [hGdef]
        simp only
        rw [hD, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · intro η hη n hn hc
        have hK := card_of_cons_not_mem_msgs hη hn hc
        rw [hGdef]
        simp only
        refine mul_eq_zero_of_left (mul_eq_zero_of_right _ ?_) _
        by_contra hne
        have := card_msg_le o ru hu Su Tu ζ η hSu h.neTu hne
        have := h.cu
        rw [Multiset.card_cons] at this
        omega
    rw [Finset.sum_comm, Finset.sum_congr rfl key]
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- (t, n, η, ζ) on the left, (ζ, η, n, t) on the right
    symm
    calc _ = ∑ ζ ∈ msgs N K, ∑ η ∈ msgs N K, ∑ t ∈ Td.toFinset, ∑ n ∈ range N,
          (ru s.1 s.2 o n * rd o n t.1 t.2) *
          (transport (Su + located o ζ) (Tu + located o η) ru *
            transport (Sd + located o η) (Td.erase t + located o ζ) rd) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ ζ ∈ msgs N K, ∑ t ∈ Td.toFinset, ∑ η ∈ msgs N K, ∑ n ∈ range N,
          (ru s.1 s.2 o n * rd o n t.1 t.2) *
          (transport (Su + located o ζ) (Tu + located o η) ru *
            transport (Sd + located o η) (Td.erase t + located o ζ) rd) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ t ∈ Td.toFinset, ∑ ζ ∈ msgs N K, ∑ η ∈ msgs N K, ∑ n ∈ range N,
          (ru s.1 s.2 o n * rd o n t.1 t.2) *
          (transport (Su + located o ζ) (Tu + located o η) ru *
            transport (Sd + located o η) (Td.erase t + located o ζ) rd) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem glue_zero (o : P) (ru rd R : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (hu : ∀ i j, ru o i o j = 0) (hd : ∀ i j, rd o i o j = 0) (Su : Multiset (P × ℕ)) :
    ∀ Tu Td : Multiset (P × ℕ), GlueHyp o ru rd R N K Su 0 Tu Td →
      transport (Su + 0) (Tu + Td) R = glueRHS o ru rd N K Su 0 Tu Td := by
  induction Su using Multiset.induction_on with
  | empty => exact glue_base o ru rd R N K hu hd
  | cons s Su ih => exact fun Tu Td h => glue_step o ru rd R N K hd hu s Su 0 Tu Td h ih

/-- **The gluing lemma.** A transport whose rules across the cut factor through an intermediate
type is the sum over messages of an upper half-transport times a lower one. -/
theorem glue (o : P) (ru rd R : P → ℕ → P → ℕ → Lp) (N K : ℕ)
    (hu : ∀ i j, ru o i o j = 0) (hd : ∀ i j, rd o i o j = 0) (Su : Multiset (P × ℕ)) :
    ∀ Sd Tu Td : Multiset (P × ℕ), GlueHyp o ru rd R N K Su Sd Tu Td →
      transport (Su + Sd) (Tu + Td) R = glueRHS o ru rd N K Su Sd Tu Td := by
  induction Su using Multiset.induction_on with
  | empty =>
    intro Sd Tu Td h
    have := glue_zero o rd ru R N K hd hu Sd Td Tu h.symm
    rw [add_zero, add_comm Td] at this
    rw [zero_add, this, glueRHS_symm]
  | cons s Su ih =>
    exact fun Sd Tu Td h => glue_step o ru rd R N K hd hu s Su Sd Tu Td h (ih Sd)

end Glue


/-! ### Exponents of the rules -/

theorem LB_eqL {b : ℤ} {i j : ℕ} (h : i = j → b ≤ 0) : LB b (eqL i j) := by
  unfold eqL
  split_ifs with hij
  · exact LB.one.mono (h hij)
  · exact LB.zero _

theorem LB_Cij (i j : ℕ) : LB (d i j) (Cube.C i j) := by
  unfold Cube.C; exact LB.C_mul _ (LB.T _)

theorem bar_C_eq (i j : ℕ) :
    bar (Cube.C i j) = LaurentPolynomial.C (chi i j) * T (-(d i j : ℤ)) := by
  unfold bar Cube.C; rw [map_mul, invert_C, invert_T]

theorem LB_barC (i j : ℕ) : LB (-(d i j : ℤ)) (bar (Cube.C i j)) := by
  rw [bar_C_eq]; exact LB.C_mul _ (LB.T _)

theorem LB_oneSubZ2 : LB 0 oneSubZ2 := LB.one.sub ((LB.T 2).mono (by norm_num))

theorem LB_oneSubZm2 : LB (-2) oneSubZm2 := (LB.one.mono (by norm_num)).sub (LB.T (-2))

theorem lb_side (i j : ℕ) {b : ℤ} (hb : b + i + j + 2 ≤ 0) : LB b (oneSubZm2 * bar (Cube.C i j)) :=
  (LB_oneSubZm2.mul (LB_barC i j)).mono (by have := d_le_add i j; omega)

theorem lb_step (i n : ℕ) {b : ℤ} (hb : b + i ≤ n) : LB b (oneSubZ2 * Cube.C i n) :=
  (LB_oneSubZ2.mul (LB_Cij i n)).mono (by have := le_add_d i n; omega)

theorem lb_copy (i n : ℕ) {b : ℤ} (hb : b + i ≤ n) (hb' : b + n ≤ i) : LB b (eqL i n) :=
  LB_eqL fun h => by subst h; omega

theorem lb_C (i j : ℕ) {b : ℤ} (hb : b ≤ 0) : LB b (Cube.C i j) :=
  (LB_Cij i j).mono (by omega)

theorem lb_Cstep (i n : ℕ) {b : ℤ} (hb : b + i ≤ n) : LB b (Cube.C i n) :=
  (LB_Cij i n).mono (by have := le_add_d i n; omega)

theorem lb_barC (i j : ℕ) {b : ℤ} (hb : b + i + j ≤ 0) : LB b (bar (Cube.C i j)) :=
  (LB_barC i j).mono (by have := d_le_add i j; omega)

/-- The weight bookkeeping of Lemma 5.4: a corner occurrence of type `i` counts `-(i + 1)`, a
request of the message of type `n` counts `n + 1`. -/
def φw : HPlace × ℕ → ℤ
  | (none, n) => n + 1
  | (some _, i) => -(i + 1)

theorem sum_φw_some (c : Corner) (σ : Multiset ℕ) :
    ((located (some c) σ).map φw).sum = -(wt σ : ℤ) := by
  unfold located
  rw [Multiset.map_map]
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons i σ ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, wt_cons]
    simp only [Function.comp, φw]
    push_cast; ring

theorem sum_φw_none (σ : Multiset ℕ) : ((located none σ).map φw).sum = (wt σ : ℤ) := by
  unfold located
  rw [Multiset.map_map]
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons i σ ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, wt_cons]
    simp only [Function.comp, φw]
    push_cast; ring

/-- Close a lower-bound goal of the row cut by one of its bound lemmas. -/
macro (name := lbRule) "lb_rule" : tactic => `(tactic| first
  | with_reducible exact LB.zero _
  | (with_reducible refine lb_side _ _ ?_); omega
  | (with_reducible refine lb_step _ _ ?_); omega
  | (with_reducible refine lb_copy _ _ ?_ ?_) <;> omega
  | (with_reducible refine lb_C _ _ ?_); omega
  | (with_reducible refine lb_Cstep _ _ ?_); omega
  | (with_reducible refine lb_barC _ _ ?_); omega
  | (with_reducible refine LB_eqL fun _ => ?_); omega)

theorem upRule_lb (s t : HPlace × ℕ) : LB (φw s + φw t) (upRule s.1 s.2 t.1 t.2) := by
  rcases s with ⟨_ | (_ | _ | _ | _), i⟩ <;> rcases t with ⟨_ | (_ | _ | _ | _), j⟩ <;> simp only
      [upRule, φw] <;> lb_rule

theorem downRule_lb (s t : HPlace × ℕ) : LB (φw s + φw t) (downRule s.1 s.2 t.1 t.2) := by
  rcases s with ⟨_ | (_ | _ | _ | _), i⟩ <;> rcases t with ⟨_ | (_ | _ | _ | _), j⟩ <;> simp only
      [downRule, φw] <;> lb_rule

theorem nUp_LB (x y m : Label) :
    LB ((labelWt m : ℤ) - (labelWt x + labelWt y)) (nUp x y m) := by
  unfold nUp
  refine (transport_lb φw upRule _ _ fun s _ t _ => upRule_lb s t).mono (le_of_eq ?_)
  simp only [Multiset.map_add, Multiset.sum_add, sum_φw_some, sum_φw_none, labelWt]
  push_cast; ring

theorem nDown_LB (u v m : Label) :
    LB ((labelWt m : ℤ) - (labelWt u + labelWt v)) (nDown u v m) := by
  unfold nDown
  refine (transport_lb φw downRule _ _ fun s _ t _ => downRule_lb s t).mono (le_of_eq ?_)
  simp only [Multiset.map_add, Multiset.sum_add, sum_φw_some, sum_φw_none, labelWt]
  push_cast; ring


/-! ### The routing polynomial through the cut -/

/-- The rules of a routing, on the places `some c` of the half-routings. -/
noncomputable def ruleO : HPlace → ℕ → HPlace → ℕ → Lp
  | some c, i, some c', j => rule c i c' j
  | _, _, _, _ => 0

/-- The rules of a routing with the diagonal `xv` replaced by its finite Walsh–Hadamard form
`[i = j] (1 - z^M)` (with `M = 2^{L+1}`). -/
noncomputable def ruleCut (M : ℤ) : HPlace → ℕ → HPlace → ℕ → Lp
  | some .x, i, some .v, j => eqL i j * (1 - T M)
  | some .v, i, some .x, j => eqL j i * (1 - T M)
  | some c, i, some c', j => rule c i c' j
  | _, _, _, _ => 0

/-- The sources of the upper row, on the places of the half-routings. -/
def upSrc (V : Corner → Label) : Multiset (HPlace × ℕ) :=
  located (some .x) (V .x).1 + located (some .y) (V .y).1

/-- The sources of the lower row. -/
def downSrc (V : Corner → Label) : Multiset (HPlace × ℕ) :=
  located (some .u) (V .u).1 + located (some .v) (V .v).1

/-- The targets of the upper row. -/
def upTgt (V : Corner → Label) : Multiset (HPlace × ℕ) :=
  located (some .x) (V .x).2 + located (some .y) (V .y).2

/-- The targets of the lower row. -/
def downTgt (V : Corner → Label) : Multiset (HPlace × ℕ) :=
  located (some .u) (V .u).2 + located (some .v) (V .v).2

theorem located_map_some (c : Corner) (σ : Multiset ℕ) :
    (located c σ).map (fun s => (some s.1, s.2)) = located (some c) σ := by
  unfold located; rw [Multiset.map_map]; rfl

theorem piece_eq_transport (V : Corner → Label) :
    piece V = transport (upSrc V + downSrc V) (upTgt V + downTgt V) ruleO := by
  have e1 : upSrc V + downSrc V = (sourcesOf V).map fun s => (some s.1, s.2) := by
    simp only [sourcesOf, Multiset.map_add, located_map_some, upSrc, downSrc, add_assoc]
  have e2 : upTgt V + downTgt V = (targetsOf V).map fun s => (some s.1, s.2) := by
    simp only [targetsOf, Multiset.map_add, located_map_some, upTgt, downTgt, add_assoc]
  rw [e1, e2, transport_map some (Option.some_injective _)]
  rfl

theorem eqL_comm (i j : ℕ) : eqL i j = eqL j i := by
  unfold eqL; by_cases h : i = j <;> simp [h, eq_comm]

theorem sum_mul_eqL (f : ℕ → Lp) (N j : ℕ) (hj : j < N) :
    ∑ n ∈ range N, f n * eqL j n = f j := by
  unfold eqL
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [hj]

theorem sum_eqL_mul (f : ℕ → Lp) (N i : ℕ) (hi : i < N) :
    ∑ n ∈ range N, eqL i n * f n = f i := by
  unfold eqL
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [hi]

theorem sum_step_C (L i j : ℕ) (hi : i < 2 ^ L) (hj : j < 2 ^ L) :
    ∑ n ∈ range (2 ^ L), oneSubZ2 * Cube.C i n * Cube.C j n =
      eqL i j * (1 - T (2 ^ (L + 1))) := by
  rw [← sum_C_mul_C L i j hi hj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [C_comm j n, mul_assoc]

theorem type_lt_out {V : Corner → Label} {c : Corner} {i N : ℕ} (hN : labelWt (V c) ≤ N)
    (h : i ∈ (V c).1) : i < N := by
  have := lt_wt_of_mem h; unfold labelWt at hN; omega

theorem type_lt_in {V : Corner → Label} {c : Corner} {i N : ℕ} (hN : labelWt (V c) ≤ N)
    (h : i ∈ (V c).2) : i < N := by
  have := lt_wt_of_mem h; unfold labelWt at hN; omega

theorem card_located_le {Q : Type} (p : Q) (σ : Multiset ℕ) :
    Multiset.card (located p σ) ≤ wt σ := by
  unfold located; rw [Multiset.card_map]; exact card_le_wt σ

/-- The routing with the finite Walsh–Hadamard diagonal satisfies the hypotheses of the gluing
lemma, with intermediate types below `2^L`. -/
theorem glueHyp_piece (V : Corner → Label) (L K : ℕ) (hL : ∀ c, labelWt (V c) ≤ 2 ^ L)
    (hK1 : labelWt (V .x) + labelWt (V .y) < K) (hK2 : labelWt (V .u) + labelWt (V .v) < K) :
    GlueHyp none upRule downRule (ruleCut (2 ^ (L + 1))) (2 ^ L) K
      (upSrc V) (downSrc V) (upTgt V) (downTgt V) where
  neSu := by
    simp only [upSrc, located, Multiset.mem_add, Multiset.mem_map]
    rintro p (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> simp
  neSd := by
    simp only [downSrc, located, Multiset.mem_add, Multiset.mem_map]
    rintro p (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> simp
  neTu := by
    simp only [upTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro p (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> simp
  neTd := by
    simp only [downTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro p (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> simp
  disj := by
    simp only [upTgt, downTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro t (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) t' (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) <;> simp
  uu := by
    simp only [upSrc, upTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro s (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) t (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) <;> rfl
  dd := by
    simp only [downSrc, downTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro s (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) t (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) <;> rfl
  ud := by
    simp only [upSrc, downTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) t (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;>
      simp only [ruleCut, rule, upRule, downRule]
    · exact (sum_mul_eqL (fun n => oneSubZ2 * Cube.C i n) _ _ (type_lt_in (hL _) hj)).symm
    · exact (sum_step_C L i j (type_lt_out (hL _) hi) (type_lt_in (hL _) hj)).symm
    · exact (sum_mul_eqL _ _ _ (type_lt_in (hL _) hj)).symm
    · exact (sum_eqL_mul _ _ _ (type_lt_out (hL _) hi)).symm
  du := by
    simp only [downSrc, upTgt, located, Multiset.mem_add, Multiset.mem_map]
    rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) t (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;>
      simp only [ruleCut, rule, upRule, downRule]
    · exact (sum_eqL_mul (fun n => oneSubZ2 * Cube.C j n) _ _ (type_lt_out (hL _) hi)).symm
    · exact (sum_mul_eqL _ _ _ (type_lt_in (hL _) hj)).symm
    · rw [← sum_step_C L j i (type_lt_in (hL _) hj) (type_lt_out (hL _) hi)]
      exact Finset.sum_congr rfl fun n _ => by ring
    · exact (sum_mul_eqL _ _ _ (type_lt_in (hL _) hj)).symm
  cu := by
    have := card_located_le (some Corner.x) (V .x).1
    have := card_located_le (some Corner.y) (V .y).1
    simp only [upSrc, Multiset.card_add]; unfold labelWt at hK1; omega
  cd := by
    have := card_located_le (some Corner.u) (V .u).1
    have := card_located_le (some Corner.v) (V .v).1
    simp only [downSrc, Multiset.card_add]; unfold labelWt at hK2; omega

theorem ruleO_lb (s t : HPlace × ℕ) : LB (φw s + φw t) (ruleO s.1 s.2 t.1 t.2) := by
  rcases s with ⟨_ | (_ | _ | _ | _), i⟩ <;> rcases t with ⟨_ | (_ | _ | _ | _), j⟩ <;>
    simp only [ruleO, rule, φw] <;> lb_rule

theorem lb_rem (i j : ℕ) (M b : ℤ) (hb : b ≤ M) : LB b (eqL i j - eqL i j * (1 - T M)) := by
  have e : eqL i j - eqL i j * (1 - T M) = eqL i j * T M := by ring
  rw [e]
  exact ((LB_eqL (b := 0) fun _ => le_rfl).mul (LB.T M)).mono (by omega)

theorem ruleO_sub_lb (M : ℤ) (s t : HPlace × ℕ) :
    LB (φw s + φw t + M) (ruleO s.1 s.2 t.1 t.2 - ruleCut M s.1 s.2 t.1 t.2) := by
  rcases s with ⟨_ | (_ | _ | _ | _), i⟩ <;> rcases t with ⟨_ | (_ | _ | _ | _), j⟩ <;>
    simp only [ruleO, ruleCut, rule, φw, sub_self] <;> first
    | with_reducible exact LB.zero _
    | (with_reducible refine lb_rem _ _ _ _ ?_); omega
    | (rw [eqL_comm j i]; (with_reducible refine lb_rem _ _ _ _ ?_); omega)

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Lp) (k : ℤ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

/-- A coefficient of a product, summed over the window where both factors can contribute. -/
theorem coeff_mul_eq_sum_Icc (f g : Lp) (k lo hi : ℤ) (hg : LB lo g)
    (hf : ∀ c, f.coeff (k - c) ≠ 0 → c ≤ hi) :
    (f * g).coeff k = ∑ c ∈ Icc lo hi, f.coeff (k - c) * g.coeff c := by
  rw [AddMonoidAlgebra.coeff_mul_apply_right]
  unfold Finsupp.sum
  calc ∑ h ∈ g.coeff.support, f.coeff (k + -h) * g.coeff h
      = ∑ h ∈ g.coeff.support ∩ Icc lo hi, f.coeff (k + -h) * g.coeff h := by
        refine (Finset.sum_subset Finset.inter_subset_left fun h h1 h2 => ?_).symm
        have hlo := hg h (Finsupp.mem_support_iff.mp h1)
        have hh : ¬ h ≤ hi := fun hh =>
          h2 (Finset.mem_inter.mpr ⟨h1, Finset.mem_Icc.mpr ⟨hlo, hh⟩⟩)
        have : f.coeff (k - h) = 0 := by
          by_contra hne; exact hh (hf h hne)
        rw [← sub_eq_add_neg, this, zero_mul]
    _ = ∑ h ∈ g.coeff.support ∩ Icc lo hi, f.coeff (k - h) * g.coeff h :=
        Finset.sum_congr rfl fun h _ => by rw [← sub_eq_add_neg]
    _ = ∑ h ∈ Icc lo hi, f.coeff (k - h) * g.coeff h := by
        refine Finset.sum_subset Finset.inter_subset_right fun h h1 h2 => ?_
        have : g.coeff h = 0 := by
          by_contra hne
          exact h2 (Finset.mem_inter.mpr ⟨Finsupp.mem_support_iff.mpr hne, h1⟩)
        rw [this, mul_zero]



/-- **Lemma 5.4, the bound for the upper factor.** -/
theorem nUp_lower (x y m : Label) (e : ℤ) (h : (nUp x y m).coeff e ≠ 0) :
    (labelWt m : ℤ) - (labelWt x + labelWt y) ≤ e :=
  nUp_LB x y m e h

/-- **Lemma 5.4, the bound for the lower factor.** -/
theorem nDown_lower (u v m : Label) (e : ℤ) (h : (nDown u v m).coeff e ≠ 0) :
    (labelWt m : ℤ) - (labelWt u + labelWt v) ≤ e :=
  nDown_LB u v m e h

/-- A message whose product of factors has a nonzero coefficient of `z^e` has weight at most
`(2H + e)/2`, by the exponent bounds of Lemma 5.4. -/
theorem wt_le_of_coeff_ne_zero (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a)
    (hv : labelWt (V .v) = a) (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (e : ℤ)
    (m : Label) (hne : (nUp (V .x) (V .y) m * nDown (V .u) (V .v) m).coeff e ≠ 0) :
    labelWt m ≤ ((2 * ((a : ℤ) + b) + e) / 2).toNat := by
  have := ((nUp_LB (V .x) (V .y) m).mul (nDown_LB (V .u) (V .v) m)) _ hne
  rw [hx, hy, hu, hv] at this
  have h1 : (labelWt m : ℤ) ≤ (2 * ((a : ℤ) + b) + e) / 2 := by omega
  have h2 : (2 * ((a : ℤ) + b) + e) / 2 ≤ (((2 * ((a : ℤ) + b) + e) / 2).toNat : ℤ) :=
    Int.self_le_toNat _
  exact_mod_cast h1.trans h2

/-- **Lemma 5.4, the identity, coefficientwise.** For views with `wt x = wt v = a` and
`wt y = wt u = b`, every coefficient of the piece polynomial is the coefficient of the same power of
`z` in `∑_m N↑(x, y; m) · N↓(u, v; m)`, where only the messages of weight at most `(2H + e)/2`
contribute (`wt_le_of_coeff_ne_zero`). -/
theorem rowCut_coeff (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a)
    (hv : labelWt (V .v) = a) (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (e : ℤ) :
    (piece V).coeff e = ∑ m ∈ labelsLE ((2 * ((a : ℤ) + b) + e) / 2).toNat,
      (nUp (V .x) (V .y) m * nDown (V .u) (V .v) m).coeff e := by
  have hte := Int.self_le_toNat e
  set L := 2 * (a + b) + e.toNat with hLdef
  set K := 2 * (a + b) + e.toNat + 1 with hKdef
  have hpow : L < 2 ^ L := Nat.lt_two_pow_self
  have hpowZ : (L : ℤ) < (2 : ℤ) ^ L := by exact_mod_cast hpow
  have hLZ : (L : ℤ) = 2 * ((a : ℤ) + b) + (e.toNat : ℤ) := by rw [hLdef]; push_cast; ring
  set M : ℤ := 2 ^ (L + 1) with hMdef
  have hM : M = 2 * 2 ^ L := by rw [hMdef, pow_succ]; ring
  -- the routing polynomial with the finite Walsh–Hadamard diagonal
  have hsum : ((upSrc V + downSrc V).map φw).sum + ((upTgt V + downTgt V).map φw).sum =
      -(2 * ((a : ℤ) + b)) := by
    simp only [upSrc, downSrc, upTgt, downTgt, Multiset.map_add, Multiset.sum_add, sum_φw_some]
    unfold labelWt at hx hy hu hv
    omega
  have hdiff := transport_sub_lb φw M (by rw [hM]; positivity) ruleO (ruleCut M)
    (upSrc V + downSrc V) (upTgt V + downTgt V) (fun s _ t _ => ruleO_lb s t)
    (fun s _ t _ => ruleO_sub_lb M s t)
  rw [hsum] at hdiff
  have e1 : (transport (upSrc V + downSrc V) (upTgt V + downTgt V) ruleO).coeff e =
      (transport (upSrc V + downSrc V) (upTgt V + downTgt V) (ruleCut M)).coeff e := by
    rw [← sub_eq_zero, ← Finsupp.sub_apply, ← AddMonoidAlgebra.coeff_sub]
    by_contra hne
    have := hdiff _ hne
    omega
  have hL : ∀ c, labelWt (V c) ≤ 2 ^ L := by
    intro c; cases c <;> omega
  have hglue := glue none upRule downRule (ruleCut M) (2 ^ L) K (fun _ _ => rfl) (fun _ _ => rfl)
    (upSrc V) (downSrc V) (upTgt V) (downTgt V)
    (glueHyp_piece V L K hL (by omega) (by omega))
  rw [piece_eq_transport, e1, hglue]
  unfold glueRHS
  simp only [coeff_finset_sum]
  have e2 : ∑ η ∈ msgs (2 ^ L) K, ∑ ζ ∈ msgs (2 ^ L) K,
      (transport (upSrc V + located none ζ) (upTgt V + located none η) upRule *
        transport (downSrc V + located none η) (downTgt V + located none ζ) downRule).coeff e =
      ∑ m ∈ msgs (2 ^ L) K ×ˢ msgs (2 ^ L) K,
        (nUp (V .x) (V .y) m * nDown (V .u) (V .v) m).coeff e := by
    rw [Finset.sum_product]; rfl
  rw [e2]
  have hN : ((((2 * ((a : ℤ) + b) + e) / 2).toNat : ℕ) : ℤ) ≤ a + b + e.toNat := by
    rw [Int.toNat_eq_max]; exact max_le (by omega) (by omega)
  have hsub : labelsLE ((2 * ((a : ℤ) + b) + e) / 2).toNat ⊆
      msgs (2 ^ L) K ×ˢ msgs (2 ^ L) K := by
    intro m hm
    rw [mem_labelsLE] at hm
    have hmZ : (labelWt m : ℤ) ≤ ((((2 * ((a : ℤ) + b) + e) / 2).toNat : ℕ) : ℤ) := by
      exact_mod_cast hm
    have hm' : (labelWt m : ℤ) ≤ a + b + e.toNat := hmZ.trans hN
    unfold labelWt at hm'
    have h1 := card_le_wt m.1
    have h2 := card_le_wt m.2
    rw [Finset.mem_product, mem_msgs, mem_msgs]
    constructor
    · intro n
      by_cases hn : n ∈ m.1
      · have := lt_wt_of_mem hn
        have := Multiset.count_le_card n m.1
        rw [ite_eq_left (by omega)]; omega
      · rw [Multiset.count_eq_zero.mpr hn]; exact Nat.zero_le _
    · intro n
      by_cases hn : n ∈ m.2
      · have := lt_wt_of_mem hn
        have := Multiset.count_le_card n m.2
        rw [ite_eq_left (by omega)]; omega
      · rw [Multiset.count_eq_zero.mpr hn]; exact Nat.zero_le _
  rw [← Finset.sum_subset hsub]
  intro m _ hm
  by_contra hne
  exact hm (mem_labelsLE.mpr (wt_le_of_coeff_ne_zero V a b hx hv hy hu e m hne))

/-- **Lemma 5.4, the identity in `ℤ((z))`.** Every coefficient of the piece polynomial is the
coefficient of the same power of `z` in the sum, over all messages `m`, of
`N↑(x, y; m) · N↓(u, v; m)`; for each power only finitely many messages contribute. -/
theorem rowCut_finsum (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a)
    (hv : labelWt (V .v) = a) (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (e : ℤ) :
    (piece V).coeff e = ∑ᶠ m : Label, (nUp (V .x) (V .y) m * nDown (V .u) (V .v) m).coeff e := by
  rw [rowCut_coeff V a b hx hv hy hu e]
  refine (finsum_eq_sum_of_support_subset _ fun m hm => ?_).symm
  rw [Finset.mem_coe, mem_labelsLE]
  exact wt_le_of_coeff_ne_zero V a b hx hv hy hu e m hm

/-- **Corollary 5.5, the row cut.** -/
theorem rowCut (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a) (hv : labelWt (V .v) = a)
    (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (k : ℤ) :
    (piece V).coeff k = ∑ m ∈ labelsLE ((a + b : ℤ) + k / 2).toNat,
      ∑ c ∈ Icc ((labelWt m : ℤ) - (a + b)) ((a + b : ℤ) + k - labelWt m),
        (nUp (V .x) (V .y) m).coeff (k - c) * (nDown (V .u) (V .v) m).coeff c := by
  rw [rowCut_coeff V a b hx hv hy hu k]
  have e3 : (2 * ((a : ℤ) + b) + k) / 2 = (a + b : ℤ) + k / 2 := by omega
  rw [e3]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine coeff_mul_eq_sum_Icc _ _ _ _ _ ((nDown_LB _ _ m).mono (by rw [hu, hv]; omega))
    fun c hc => ?_
  have := nUp_LB _ _ m _ hc
  rw [hx, hy] at this
  omega

/-- **Corollary 5.5, the column cut.** -/
theorem colCut (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a) (hv : labelWt (V .v) = a)
    (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (k : ℤ) (hk : Even k) :
    (piece V).coeff k = ∑ m ∈ labelsLE ((a + b : ℤ) - k / 2).toNat,
      ∑ c ∈ Icc ((labelWt m : ℤ) - (a + b)) ((a + b : ℤ) - k - labelWt m),
        (nUp (V .x) (V .u) m).coeff (-k - c) * (nDown (V .y) (V .v) m).coeff c := by
  have hT := rowCut (transposeView V) a b hx hv hu hy (-k)
  rw [piece_transpose, invert_apply, neg_neg] at hT
  have e : ((a : ℤ) + b + -k / 2) = (a : ℤ) + b - k / 2 := by
    rw [Int.neg_ediv_of_dvd hk.two_dvd]; ring
  have e2 : ∀ m : Label, ((a : ℤ) + b + -k - labelWt m) = (a : ℤ) + b - k - labelWt m :=
    fun m => by ring
  rw [e] at hT
  simp only [e2] at hT
  exact hT

end Cslib.Complexity.NtimeDspace.Cube
