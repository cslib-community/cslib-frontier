/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactArith
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Bits of a number from its residues, elementarily

This is the mathematics of the elementary Chinese remainder step. A number `0 ≤ Z ≤ 2^E` is known
through its residues `res p = Z mod p` at the primes `p` of a window `(H, X]` whose product exceeds
`2^(E+1)`. Every bit of `Z` is a function `out` of these residues, built only from bounded sums,
products, comparisons and divisions of numbers below `2^(O(W))`, for a width `W` with
`X^r < 2^W` and `E / r < g`. The program computing `out` is in `ExactBits`.

The construction (instead of the logspace conversion of Chiu, Davida and Litow):

* *Selection.* The first `E + 1` primes of the window are used (`sel`); their product `Qt`
  exceeds `2^(E+1) ≥ 2Z` (`two_pow_lt_Qt`). The selected prime of rank `ρ` joins group `ρ / r`,
  so `Qt` is the product of `g` group products `Qm m < 2^W` (`Qt_eq_prod_Qm`, `Qm_lt`).
* *Chinese remainders.* With `bco p = res p · (Qt/p)^(p-2) mod p`, the number
  `A = ∑_p bco p · Qt/p` is `≡ Z (mod Qt)` (`A_mod_Qt`), so `A = kq · Qt + Z` where
  `kq = ⌊∑_p bco p / p⌋` is computed from `W` bits of each fraction, since `Z / Qt < 1/2`
  (`kq_eq`).
* *Bits.* Each term of `A`, and `Qt`, is a product of `g` factors below `2^W`, whose columns are
  counted over packed tuples (`prod_eq_sum_pbits`). The carry chain gives the bits of `kq · Qt`,
  and the carry chain of the columns of `A + 2^J - kq · Qt = Z + 2^J` gives the bits of `Z`
  (`out_eq`).

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.Exact.out_eq`: `out j` is bit `j` of `Z`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open Finset

/-! ### The selected primes and their groups -/

section Defs

variable (H X E W r g : ℕ) (res : ℕ → ℕ)

/-- A prime of the window `(H, X]`. -/
def cand (x : ℕ) : Prop := H < x ∧ x ≤ X ∧ x.Prime

instance : DecidablePred (cand H X) := fun x => by unfold cand; infer_instance

/-- The number of window primes below `x`. -/
def rank (x : ℕ) : ℕ := Nat.count (cand H X) x

/-- The first `E + 1` primes of the window. -/
def sel (x : ℕ) : Prop := cand H X x ∧ rank H X x < E + 1

instance : DecidablePred (sel H X E) := fun x => by unfold sel; infer_instance

/-- The group of a selected prime. -/
def grp (x : ℕ) : ℕ := rank H X x / r

/-- The product of group `m`. -/
def Qm (m : ℕ) : ℕ := ∏ x ∈ range (X + 1), if sel H X E x ∧ grp H X r x = m then x else 1

/-- The product of the selected primes. -/
def Qt : ℕ := ∏ x ∈ range (X + 1), if sel H X E x then x else 1

/-- The selected primes. -/
def selSet : Finset ℕ := (range (X + 1)).filter (sel H X E)

/-- `(Qt / p)^(p-2) mod p`, the inverse of `Qt / p` modulo `p`. -/
def invc (p : ℕ) : ℕ :=
  ((∏ x ∈ range (X + 1), if sel H X E x ∧ x ≠ p then x else 1) % p) ^ (p - 2) % p

/-- The Chinese-remainder coefficient at `p`. -/
def bco (p : ℕ) : ℕ := res p * invc H X E p % p

/-- The factors of the term of `p`: the coefficient times `Qm m / p` in its own group, `Qm m`
in the others. -/
def fac (p m : ℕ) : ℕ :=
  if m = grp H X r p then bco H X E res p * (Qm H X E r m / p) else Qm H X E r m

/-- The columns of `A = ∑_p bco p · Qt / p`. -/
def colA (i : ℕ) : ℕ :=
  ∑ p ∈ range (X + 1), if sel H X E p then
    ∑ u ∈ range (W ^ g), (if sdig W g u = i then pbits W g (fac H X E r res p) u else 0) else 0

/-- The columns of `Qt`. -/
def colQ (i : ℕ) : ℕ :=
  ∑ u ∈ range (W ^ g), if sdig W g u = i then pbits W g (Qm H X E r) u else 0

/-- The quotient `⌊A / Qt⌋`, from `W` bits of every fraction `bco p / p`. -/
def kq : ℕ :=
  ((∑ p ∈ range (X + 1), if sel H X E p then bco H X E res p * 2 ^ W / p else 0) +
    ∑ p ∈ range (X + 1), if sel H X E p then 1 else 0) / 2 ^ W

/-- The columns of `A + 2^J - kq · Qt`. -/
def colZ (i : ℕ) : ℕ :=
  colA H X E W r g res i + (1 - bitOf (fun i => kq H X E W res * colQ H X E W r g i) i) +
    if i = 0 then 1 else 0

/-- **The bits of `Z`.** -/
def out (j : ℕ) : ℕ := if j < (g + 1) * W then bitOf (colZ H X E W r g res) j else 0

end Defs

variable {H X E W r g : ℕ} {res : ℕ → ℕ}

theorem mem_selSet {x : ℕ} : x ∈ selSet H X E ↔ x ≤ X ∧ sel H X E x := by
  simp [selSet]

theorem sel_prime {x : ℕ} (h : sel H X E x) : x.Prime := h.1.2.2

theorem sel_le {x : ℕ} (h : sel H X E x) : x ≤ X := h.1.2.1

theorem Qt_eq_prod_selSet : Qt H X E = ∏ x ∈ selSet H X E, x := by
  rw [Qt, selSet, prod_filter]

theorem grp_lt (hg : E / r < g) {x : ℕ} (h : sel H X E x) : grp H X r x < g :=
  lt_of_le_of_lt (Nat.div_le_div_right (Nat.lt_succ_iff.mp h.2)) hg

/-- `Qt` is the product of the group products. -/
theorem Qt_eq_prod_Qm (hg : E / r < g) : Qt H X E = ∏ m ∈ range g, Qm H X E r m := by
  unfold Qt Qm
  rw [prod_comm]
  refine prod_congr rfl fun x _ => ?_
  by_cases hx : sel H X E x
  · simp only [hx, true_and]
    rw [prod_ite_eq (range g) (grp H X r x) (fun _ => x)]
    simp [grp_lt hg hx]
  · simp [hx]

theorem dvd_Qm {p : ℕ} (hp : p ∈ selSet H X E) : p ∣ Qm H X E r (grp H X r p) := by
  obtain ⟨hpX, hps⟩ := mem_selSet.mp hp
  have := dvd_prod_of_mem (fun x => if sel H X E x ∧ grp H X r x = grp H X r p then x else 1)
    (mem_range.mpr (Nat.lt_succ_of_le hpX))
  rw [Qm]
  refine dvd_trans ?_ this
  simp [hps]

/-- A group has at most `r` primes, so its product is below `2^W`. -/
theorem Qm_lt (hW : 1 ≤ W) (hr : 1 ≤ r) (hXr : X ^ r < 2 ^ W) (m : ℕ) :
    Qm H X E r m < 2 ^ W := by
  set T := (range (X + 1)).filter fun x => sel H X E x ∧ grp H X r x = m
  have hQ : Qm H X E r m = ∏ x ∈ T, x := by rw [Qm, prod_filter]
  have hcard : T.card ≤ r := by
    have hmaps : ∀ x ∈ T, rank H X x ∈ Ico (m * r) (m * r + r) := by
      intro x hx
      obtain ⟨-, -, hg⟩ := by simpa [T] using hx
      have h1 := Nat.div_mul_le_self (rank H X x) r
      have h2 := Nat.lt_div_mul_add (a := rank H X x) (b := r)
      simp only [grp] at hg
      rw [mem_Ico]
      have h2 := h2 (by omega)
      rw [hg] at h1 h2
      constructor <;> nlinarith
    have hinj : Set.InjOn (rank H X) T := by
      intro x hx y hy hxy
      have hx' := (mem_filter.mp hx).2.1.1
      have hy' := (mem_filter.mp hy).2.1.1
      exact Nat.count_injective hx' hy' hxy
    have := card_le_card_of_injOn (rank H X) hmaps hinj
    simpa using this
  have hle : ∀ x ∈ T, x ≤ X := fun x hx => sel_le (mem_filter.mp hx).2.1
  rw [hQ]
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · have hT : T = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have := (sel_prime (mem_filter.mp hx).2.1).two_le
      have := hle x hx
      omega
    simp only [hT, prod_empty]
    exact Nat.one_lt_two_pow (by omega)
  · calc ∏ x ∈ T, x ≤ X ^ T.card := prod_le_pow_card _ _ _ hle
      _ ≤ X ^ r := Nat.pow_le_pow_right hX0 hcard
      _ < 2 ^ W := hXr

/-- **The selected primes have product above `2^(E+1)`.** Either all window primes are selected,
or the `E + 1` selected primes are each at least `3`. -/
theorem two_pow_lt_Qt (h2H : 2 ≤ H)
    (hprod : 2 ^ (E + 1) < ∏ p ∈ (Ioc H X).filter Nat.Prime, p) : 2 ^ (E + 1) < Qt H X E := by
  rw [Qt_eq_prod_selSet]
  by_cases hall : ∀ x, cand H X x → rank H X x < E + 1
  · have : selSet H X E = (Ioc H X).filter Nat.Prime := by
      ext x
      simp only [mem_selSet, mem_filter, mem_Ioc, sel, cand]
      constructor
      · rintro ⟨-, ⟨h1, h2, h3⟩, -⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, ⟨h1, h2, h3⟩, hall x ⟨h1, h2, h3⟩⟩
    rwa [this]
  · push_neg at hall
    classical
    let q := Nat.find hall
    have hq : cand H X q ∧ E + 1 ≤ rank H X q := Nat.find_spec hall
    have hmin : ∀ y < q, cand H X y → rank H X y < E + 1 := fun y hy hc => by
      by_contra hne
      exact Nat.find_min hall hy ⟨hc, by omega⟩
    set Tq := (range q).filter (cand H X)
    have hcard : E + 1 ≤ Tq.card := by
      have := hq.2
      rwa [rank, Nat.count_eq_card_filter_range] at this
    have hsub : Tq ⊆ selSet H X E := by
      intro y hy
      obtain ⟨hyq, hyc⟩ := mem_filter.mp hy
      rw [mem_range] at hyq
      exact mem_selSet.mpr ⟨by have := hq.1.2.1; omega, hyc, hmin y hyq hyc⟩
    have h3 : ∀ y ∈ Tq, 3 ≤ y := fun y hy => by
      have := (mem_filter.mp hy).2.1; omega
    calc 2 ^ (E + 1) < 3 ^ (E + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
      _ ≤ 3 ^ Tq.card := Nat.pow_le_pow_right (by norm_num) hcard
      _ ≤ ∏ y ∈ Tq, y := pow_card_le_prod _ _ _ h3
      _ ≤ ∏ y ∈ selSet H X E, y :=
          prod_le_prod_of_subset_of_one_le hsub fun y hy _ =>
            (sel_prime (mem_selSet.mp hy).2).one_lt.le

theorem Qt_pos (h2H : 2 ≤ H) (hprod : 2 ^ (E + 1) < ∏ p ∈ (Ioc H X).filter Nat.Prime, p) :
    0 < Qt H X E := lt_trans (Nat.two_pow_pos _) (two_pow_lt_Qt h2H hprod)

/-! ### Chinese remainders -/

/-- The product of the other selected primes. -/
theorem prod_other_eq {p : ℕ} :
    (∏ x ∈ range (X + 1), if sel H X E x ∧ x ≠ p then x else 1) =
      ∏ x ∈ (selSet H X E).erase p, x := by
  rw [← prod_filter]
  congr 1
  ext x
  simp only [mem_filter, mem_range, mem_erase, mem_selSet]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, by omega, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h3, h1⟩

theorem Qt_eq_mul_other {p : ℕ} (hp : p ∈ selSet H X E) :
    Qt H X E = p * ∏ x ∈ (selSet H X E).erase p, x := by
  rw [Qt_eq_prod_selSet]
  exact (mul_prod_erase _ (fun x => x) hp).symm

theorem Qt_div_eq {p : ℕ} (hp : p ∈ selSet H X E) :
    Qt H X E / p = ∏ x ∈ (selSet H X E).erase p, x := by
  rw [Qt_eq_mul_other hp, Nat.mul_div_cancel_left _ (sel_prime (mem_selSet.mp hp).2).pos]

theorem dvd_Qt {p : ℕ} (hp : p ∈ selSet H X E) : p ∣ Qt H X E :=
  ⟨_, Qt_eq_mul_other hp⟩

theorem not_dvd_other {p : ℕ} (hp : p ∈ selSet H X E) :
    ¬ p ∣ ∏ x ∈ (selSet H X E).erase p, x := by
  intro hd
  have hpp := sel_prime (mem_selSet.mp hp).2
  obtain ⟨a, ha, hpa⟩ := (Nat.Prime.prime hpp).exists_mem_finset_dvd hd
  have hap := sel_prime (mem_selSet.mp (mem_of_mem_erase ha)).2
  exact (ne_of_mem_erase ha) ((Nat.prime_dvd_prime_iff_eq hpp hap).mp hpa).symm

/-- `bco p · Qt / p ≡ Z (mod p)`, by Fermat's little theorem. -/
theorem bco_mul_cast {Z p : ℕ} (hp : p ∈ selSet H X E) (hres : res p = Z % p) :
    ((bco H X E res p * (Qt H X E / p) : ℕ) : ZMod p) = Z := by
  have hpp := sel_prime (mem_selSet.mp hp).2
  have := Fact.mk hpp
  have hR : ((∏ x ∈ (selSet H X E).erase p, x : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_other hp
  have hp2 : p - 2 + 1 = p - 1 := by have := hpp.two_le; omega
  rw [Qt_div_eq hp, bco, invc, prod_other_eq, hres]
  push_cast [ZMod.natCast_mod] at hR ⊢
  rw [mul_assoc, ← pow_succ, hp2, ZMod.pow_card_sub_one_eq_one hR, mul_one]

/-- The number `A = ∑_p bco p · Qt / p`. -/
def bigA (H X E : ℕ) (res : ℕ → ℕ) : ℕ :=
  ∑ p ∈ selSet H X E, bco H X E res p * (Qt H X E / p)

theorem bigA_cast {Z p : ℕ} (hp : p ∈ selSet H X E)
    (hres : ∀ q ∈ selSet H X E, res q = Z % q) : ((bigA H X E res : ℕ) : ZMod p) = Z := by
  unfold bigA
  push_cast
  rw [sum_eq_single_of_mem p hp]
  · exact_mod_cast bco_mul_cast hp (hres p hp)
  · intro q hq hqp
    have hdvd : p ∣ Qt H X E / q := by
      rw [Qt_div_eq hq]
      exact dvd_prod_of_mem _ (mem_erase.mpr ⟨hqp.symm, hp⟩)
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left hdvd _

/-- **The Chinese remainder theorem**: `A ≡ Z (mod Qt)`. -/
theorem bigA_modEq {Z : ℕ} (hres : ∀ q ∈ selSet H X E, res q = Z % q) :
    bigA H X E res ≡ Z [MOD Qt H X E] := by
  rw [Nat.modEq_iff_dvd, Qt_eq_prod_selSet]
  push_cast
  refine prod_dvd_of_coprime (fun p hp q hq hpq => ?_) fun p hp => ?_
  · have hpp := sel_prime (mem_selSet.mp hp).2
    have hqq := sel_prime (mem_selSet.mp hq).2
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpp hqq).mpr hpq)
  · have := bigA_cast (res := res) (H := H) (X := X) (E := E) hp hres
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [this, sub_self]

/-! ### The quotient -/

theorem card_selSet_le : (selSet H X E).card ≤ X + 1 := by
  calc (selSet H X E).card ≤ (range (X + 1)).card := card_filter_le _ _
    _ = X + 1 := card_range _

theorem bco_lt {p : ℕ} (hp : p ∈ selSet H X E) : bco H X E res p < p :=
  Nat.mod_lt _ (sel_prime (mem_selSet.mp hp).2).pos

theorem bco_mul_le {p : ℕ} (hp : p ∈ selSet H X E) :
    bco H X E res p * (Qt H X E / p) ≤ Qt H X E := by
  calc bco H X E res p * (Qt H X E / p) ≤ p * (Qt H X E / p) :=
        Nat.mul_le_mul_right _ (bco_lt hp).le
    _ = Qt H X E := Nat.mul_div_cancel' (dvd_Qt hp)

theorem bigA_le : bigA H X E res ≤ (selSet H X E).card * Qt H X E := by
  unfold bigA
  calc ∑ p ∈ selSet H X E, bco H X E res p * (Qt H X E / p)
      ≤ ∑ _p ∈ selSet H X E, Qt H X E := sum_le_sum fun p hp => bco_mul_le hp
    _ = _ := by rw [sum_const_nat (fun _ _ => rfl)]

/-- **The quotient from `W` bits of every fraction.** -/
theorem kq_eq {Z : ℕ} (hW : 1 ≤ W) (hK : X + 1 ≤ 2 ^ (W - 1))
    (hres : ∀ q ∈ selSet H X E, res q = Z % q) (hZQ : 2 * Z < Qt H X E) :
    kq H X E W res = bigA H X E res / Qt H X E := by
  set Q := Qt H X E
  set A := bigA H X E res
  set S := selSet H X E
  have hQpos : 0 < Q := by omega
  have hAmod : A % Q = Z := by
    rw [bigA_modEq hres, Nat.mod_eq_of_lt (by omega)]
  set k := A / Q
  have hA : A = Q * k + Z := by rw [← hAmod]; exact (Nat.div_add_mod A Q).symm
  set S' := ∑ p ∈ S, bco H X E res p * 2 ^ W / p
  have hS'def : (∑ p ∈ range (X + 1), if sel H X E p then bco H X E res p * 2 ^ W / p else 0)
      = S' := by rw [← sum_filter]; rfl
  have hKdef : (∑ p ∈ range (X + 1), if sel H X E p then 1 else 0) = S.card := by
    rw [← sum_filter, sum_const_nat (fun _ _ => rfl), mul_one]; rfl
  have hkq : kq H X E W res = (S' + S.card) / 2 ^ W := by rw [kq, hS'def, hKdef]
  -- the two estimates, multiplied by `Q`
  have hup : S' * Q ≤ 2 ^ W * A := by
    simp only [S', A, bigA, sum_mul, mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hdq := Nat.mul_div_cancel' (dvd_Qt hp)
    calc bco H X E res p * 2 ^ W / p * Q = bco H X E res p * 2 ^ W / p * p * (Q / p) := by
          rw [mul_assoc, hdq]
      _ ≤ bco H X E res p * 2 ^ W * (Q / p) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = 2 ^ W * (bco H X E res p * (Q / p)) := by ring
  have hlo : 2 ^ W * A ≤ (S' + S.card) * Q := by
    simp only [S', A, bigA, add_mul, mul_sum, sum_mul]
    rw [← sum_const_nat (s := S) (m := Q) (f := fun _ => Q) (fun _ _ => rfl), ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have hpp := (sel_prime (mem_selSet.mp hp).2).pos
    have hdq := Nat.mul_div_cancel' (dvd_Qt hp)
    have h1 : bco H X E res p * 2 ^ W < (bco H X E res p * 2 ^ W / p + 1) * p := by
      have := Nat.lt_div_mul_add (a := bco H X E res p * 2 ^ W) hpp
      rw [add_mul, one_mul]; exact this
    calc 2 ^ W * (bco H X E res p * (Q / p)) = bco H X E res p * 2 ^ W * (Q / p) := by ring
      _ ≤ (bco H X E res p * 2 ^ W / p + 1) * p * (Q / p) := Nat.mul_le_mul_right _ h1.le
      _ = bco H X E res p * 2 ^ W / p * Q + Q := by rw [mul_assoc, hdq]; ring
  have hcardK : S.card ≤ 2 ^ (W - 1) := card_selSet_le.trans hK
  have hW2 : 2 ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hkq]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · -- `k · 2^W ≤ S' + |S|`
    refine Nat.le_of_mul_le_mul_right ?_ hQpos
    calc k * 2 ^ W * Q ≤ 2 ^ W * A := by rw [hA]; nlinarith
      _ ≤ (S' + S.card) * Q := hlo
  · -- `S' + |S| < (k + 1) · 2^W`
    refine Nat.lt_of_mul_lt_mul_right (a := Q) ?_
    have h1 : 2 ^ W * Z < 2 ^ (W - 1) * Q := by rw [hW2]; nlinarith
    have h2 : S.card * Q ≤ 2 ^ (W - 1) * Q := Nat.mul_le_mul_right _ hcardK
    calc (S' + S.card) * Q = S' * Q + S.card * Q := add_mul _ _ _
      _ ≤ 2 ^ W * A + S.card * Q := Nat.add_le_add_right hup _
      _ = 2 ^ W * k * Q + 2 ^ W * Z + S.card * Q := by rw [hA]; ring
      _ < 2 ^ W * k * Q + 2 ^ (W - 1) * Q + 2 ^ (W - 1) * Q := by omega
      _ = (k + 1) * 2 ^ W * Q := by rw [hW2]; ring

/-! ### The bits -/

theorem fac_eq_Qm {p m : ℕ} (h : m ≠ grp H X r p) : fac H X E r res p m = Qm H X E r m := by
  simp [fac, h]

theorem fac_lt (hW : 1 ≤ W) (hr : 1 ≤ r) (hXr : X ^ r < 2 ^ W) {p : ℕ} (hp : p ∈ selSet H X E)
    (m : ℕ) :
    fac H X E r res p m < 2 ^ W := by
  unfold fac
  split_ifs with h
  · subst h
    calc bco H X E res p * (Qm H X E r (grp H X r p) / p)
        ≤ p * (Qm H X E r (grp H X r p) / p) := Nat.mul_le_mul_right _ (bco_lt hp).le
      _ = Qm H X E r (grp H X r p) := Nat.mul_div_cancel' (dvd_Qm hp)
      _ < 2 ^ W := Qm_lt hW hr hXr _
  · exact Qm_lt hW hr hXr _

/-- The term of `p` is the product of its factors. -/
theorem prod_fac (hg : E / r < g) {p : ℕ} (hp : p ∈ selSet H X E) :
    ∏ m ∈ range g, fac H X E r res p m = bco H X E res p * (Qt H X E / p) := by
  set gp := grp H X r p
  have hgp : gp ∈ range g := mem_range.mpr (grp_lt hg (mem_selSet.mp hp).2)
  have hrest : ∏ m ∈ (range g).erase gp, fac H X E r res p m =
      ∏ m ∈ (range g).erase gp, Qm H X E r m :=
    prod_congr rfl fun m hm => fac_eq_Qm (ne_of_mem_erase hm)
  have hQt : Qt H X E = p * (Qm H X E r gp / p * ∏ m ∈ (range g).erase gp, Qm H X E r m) := by
    rw [Qt_eq_prod_Qm hg, ← mul_prod_erase _ _ hgp, ← mul_assoc, Nat.mul_div_cancel' (dvd_Qm hp)]
  rw [← mul_prod_erase _ _ hgp, hrest, hQt,
    Nat.mul_div_cancel_left _ (sel_prime (mem_selSet.mp hp).2).pos]
  simp only [fac, gp, if_true]
  ring

theorem sum_two_pow_add_one : ∀ J : ℕ, ∑ i ∈ range J, 2 ^ i + 1 = 2 ^ J
  | 0 => by simp
  | J + 1 => by rw [sum_range_succ, pow_succ]; have := sum_two_pow_add_one J; omega

/-- **The Chinese remainder step, elementary version: `out j` is bit `j` of `Z`.** Hypotheses: the
window `(H, X]` has prime product above `2^(E+1)`, `H ≥ 2`; `0 ≤ Z ≤ 2^E`; the residues are those
of `Z`; the width satisfies `X^r < 2^W` and `X + 1 ≤ 2^(W-1)`; and `E / r < g`. -/
theorem out_eq {Z : ℕ} (h2H : 2 ≤ H) (hW : 1 ≤ W) (hr : 1 ≤ r) (hXr : X ^ r < 2 ^ W)
    (hK : X + 1 ≤ 2 ^ (W - 1)) (hg : E / r < g) (hZ : Z ≤ 2 ^ E)
    (hprod : 2 ^ (E + 1) < ∏ p ∈ (Ioc H X).filter Nat.Prime, p)
    (hres : ∀ p, p.Prime → H < p → p ≤ X → res p = Z % p) (j : ℕ) :
    out H X E W r g res j = Z / 2 ^ j % 2 := by
  have hres' : ∀ q ∈ selSet H X E, res q = Z % q := fun q hq => by
    obtain ⟨hqX, ⟨hH, -, hqp⟩, -⟩ := mem_selSet.mp hq
    exact hres q hqp hH hqX
  set Q := Qt H X E
  set A := bigA H X E res
  set S := selSet H X E
  set J := (g + 1) * W
  have hg1 : 1 ≤ g := Nat.lt_of_le_of_lt (Nat.zero_le _) hg
  have hQ : 2 ^ (E + 1) < Q := two_pow_lt_Qt h2H hprod
  have hZQ : 2 * Z < Q := by rw [pow_succ] at hQ; omega
  set k := kq H X E W res
  have hk : k = A / Q := kq_eq hW hK hres' hZQ
  have hAmod : A % Q = Z := by rw [bigA_modEq hres', Nat.mod_eq_of_lt (by omega)]
  have hA : A = k * Q + Z := by
    rw [hk, ← hAmod, mul_comm]; exact (Nat.div_add_mod A Q).symm
  -- sizes
  have hQle : Q ≤ 2 ^ (g * W) := by
    rw [show Q = ∏ m ∈ range g, Qm H X E r m from Qt_eq_prod_Qm hg, mul_comm, pow_mul]
    calc ∏ m ∈ range g, Qm H X E r m ≤ ∏ _m ∈ range g, 2 ^ W :=
          prod_le_prod fun m _ => (Qm_lt hW hr hXr m).le
      _ = (2 ^ W) ^ g := by rw [prod_const, card_range]
  have hJ : 2 ^ J = 2 ^ W * 2 ^ (g * W) := by rw [← pow_add]; congr 1; ring
  have hAJ : A < 2 ^ J := by
    have h1 : A ≤ S.card * Q := bigA_le
    have h2 : S.card ≤ 2 ^ (W - 1) := card_selSet_le.trans hK
    have h3 : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [hJ]
    calc A ≤ S.card * Q := h1
      _ ≤ 2 ^ (W - 1) * 2 ^ (g * W) := Nat.mul_le_mul h2 hQle
      _ < 2 ^ W * 2 ^ (g * W) := Nat.mul_lt_mul_of_pos_right h3 (Nat.two_pow_pos _)
  have hKJ : k * Q < 2 ^ J := lt_of_le_of_lt (by omega) hAJ
  have hZJ : Z < 2 ^ J := lt_of_le_of_lt (by omega) hAJ
  have hs : ∀ u < W ^ g, sdig W g u < J := fun u _ =>
    lt_of_lt_of_le (sdig_lt hW hg1 u) (Nat.mul_le_mul_right _ (Nat.le_succ g))
  -- `A` and `k · Q` as column sums
  have hAcols : A = ∑ i ∈ range J, colA H X E W r g res i * 2 ^ i := by
    have : A = ∑ p ∈ S, ∑ u ∈ range (W ^ g), pbits W g (fac H X E r res p) u * 2 ^ sdig W g u := by
      refine sum_congr rfl fun p hp => ?_
      rw [← prod_fac hg hp, prod_eq_sum_pbits hW g _ fun m _ => fac_lt hW hr hXr hp m]
    rw [this, sum_congr rfl fun p _ => sum_mul_two_pow_regroup _ _ _ J hs, sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [colA, sum_mul, show S = (range (X + 1)).filter (sel H X E) from rfl, sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have hKcols : k * Q = ∑ i ∈ range J, (k * colQ H X E W r g i) * 2 ^ i := by
    rw [show Q = ∏ m ∈ range g, Qm H X E r m from Qt_eq_prod_Qm hg,
      prod_eq_sum_pbits hW g _ fun m
          _ => Qm_lt hW hr hXr m, sum_mul_two_pow_regroup _ _ _ J hs, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [colQ]; ring
  -- the bits of `k · Q`
  set bK := fun i => bitOf (fun i => k * colQ H X E W r g i) i
  have hbK : ∀ i < J, bK i = k * Q / 2 ^ i % 2 := fun i hi =>
    (div_two_pow_mod_two_eq_bitOf hKcols hi).symm
  have hcompl : ∑ i ∈ range J, (1 - bK i) * 2 ^ i + k * Q + 1 = 2 ^ J := by
    have hb : ∑ i ∈ range J, bK i * 2 ^ i = k * Q := by
      rw [← sum_bits_eq hKJ]; exact sum_congr rfl fun i hi => by rw [hbK i (mem_range.mp hi)]
    rw [← hb, ← sum_add_distrib, ← sum_two_pow_add_one J]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have := bitOf_le_one (fun i => k * colQ H X E W r g i) i
    have h : bK i ≤ 1 := this
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  have hJpos : 0 < J := Nat.mul_pos (by omega) (by omega)
  have hone : ∑ i ∈ range J, (if i = 0 then 1 else 0) * 2 ^ i = 1 := by
    rw [sum_eq_single_of_mem 0 (mem_range.mpr hJpos) (fun i _ hi => by simp [hi])]; simp
  have hZcols : Z + 2 ^ J = ∑ i ∈ range J, colZ H X E W r g res i * 2 ^ i := by
    simp only [colZ, add_mul, sum_add_distrib]
    rw [← hAcols, hone]
    have : ∑ i ∈ range J, (1 - bitOf (fun i => kq H X E W res * colQ H X E W r g i) i) * 2 ^ i =
        ∑ i ∈ range J, (1 - bK i) * 2 ^ i := rfl
    rw [this]
    omega
  -- the bits of `Z`
  unfold out
  split_ifs with hj
  · rw [← div_two_pow_mod_two_eq_bitOf hZcols hj]
    obtain ⟨d, hd⟩ : ∃ d, J = j + (d + 1) := ⟨J - j - 1, by omega⟩
    rw [hd, pow_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), pow_succ]
    omega
  · rw [Nat.div_eq_of_lt (lt_of_lt_of_le hZJ (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end Cslib.Complexity.NtimeDspace.Cross.Exact
