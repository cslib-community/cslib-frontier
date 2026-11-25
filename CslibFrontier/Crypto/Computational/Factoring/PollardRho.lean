/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Pollard's rho factoring and Floyd cycle-detection bounds

Pollard's rho algorithm ([KatzLindell2020], Section 10.1.2, Algorithm 10.2, pp. 368–369) searches
for a nontrivial factor of a composite integer $N$ by iterating a pseudorandom walk
$F : (\mathbb{Z}/N\mathbb{Z})^\times \to (\mathbb{Z}/N\mathbb{Z})^\times$ with Floyd's
tortoise-and-hare cycle-finding schedule $(x_t, y_t) = (F^{[t]}(x_0), F^{[2t]}(x_0))$ and testing
whether $d = \gcd(|x_t - y_t|, N)$ is a nontrivial divisor $1 < d < N$:

1. **Soundness (`isNontrivialFactor_of_rhoFactorLoop_eq_some`,
   `eq_prime_of_rhoFactorLoop_eq_some`)**:
   Every output `some d` of `rhoFactorLoop N F B x y` satisfies `IsNontrivialFactor N d`
   (`d ∣ N ∧ 1 < d ∧ d < N`). When $N = p \cdot q$ is a product of two primes, any returned factor
   satisfies `d = p ∨ d = q`.
2. **Exact failure characterization (`rhoFactorLoop_eq_none_iff`,
   `rhoFactorLoop_start_eq_none_iff`)**:
   `rhoFactorLoop N F B x₀ x₀ = none` if and only if for every step $1 \le t \le B$, the tortoise
   and hare states $(F^{[t]}(x_0), F^{[2t]}(x_0))$ fail to yield a nontrivial GCD with $N$.
3. **Nontrivial GCD from a modulo-$p$ collision (`isNontrivialFactor_rhoGcd_of_modEq`)**:
   Whenever $p \mid N$ ($1 < p$), $a \ne b$ in $(\mathbb{Z}/N\mathbb{Z})^\times$, and
   $a \equiv b \pmod p$, their GCD candidate `rhoGcd N a b` is a nontrivial divisor of $N$.
4. **Floyd's cycle-detection persistence theorem (`floyd_cycle_modEq`)**:
   If $F$ is congruence-compatible modulo $p$, any collision $F^{[i]}(x) \equiv F^{[j]}(x) \pmod p$
   at indices $i < j$ implies a tortoise-and-hare collision
   $F^{[t]}(x) \equiv F^{[2t]}(x) \pmod p$ at some step $1 \le t \le j$.

The birthday-bound analysis (via [KatzLindell2020], Lemma A.15) and the heuristic
$O(N^{1/4} \cdot \mathrm{polylog}(N))$ running time are not formalised here.

## Main definitions

* `Cslib.Crypto.rhoGcd`: candidate GCD `(((a : ZMod N).val : ℤ) - (b : ZMod N).val).natAbs.gcd N`
  of the difference of two units in `(ZMod N)ˣ` with `N`.
* `Cslib.Crypto.IsNontrivialFactor`: predicate `d ∣ N ∧ 1 < d ∧ d < N`.
* `Cslib.Crypto.rhoFactorLoop`: `B`-step Floyd tortoise-and-hare loop of Pollard's rho algorithm
  ([KatzLindell2020], Algorithm 10.2, p. 369).

## Main results

* `Cslib.Crypto.isNontrivialFactor_of_rhoFactorLoop_eq_some`,
  `Cslib.Crypto.eq_prime_of_isNontrivialFactor_mul`,
  `Cslib.Crypto.eq_prime_of_rhoFactorLoop_eq_some`: soundness of `rhoFactorLoop` on general
  composites and semiprimes `N = p * q`.
* `Cslib.Crypto.rhoFactorLoop_eq_none_iff`, `Cslib.Crypto.rhoFactorLoop_start_eq_none_iff`: exact
  stepwise characterization of when `rhoFactorLoop` returns `none`.
* `Cslib.Crypto.isNontrivialFactor_rhoGcd_of_modEq`: any distinct pair in `(ZMod N)ˣ` that is
  congruent modulo a proper factor `p ∣ N` yields a nontrivial divisor via `rhoGcd`.
* `Cslib.Crypto.floyd_cycle_modEq`: Floyd's tortoise-and-hare cycle-detection theorem for
  congruence-compatible walks modulo `p`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 10.1.2 (Pollard's Rho Algorithm, Algorithm 10.2, pp. 368–369) and Section 6.4.2
  (Algorithm 6.9, p. 180, the small-space cycle-finding technique credited to Floyd).
-/

@[expose] public section

namespace Cslib.Crypto

/-- Candidate divisor `gcd(|a - b|, N)` computed at each step of Pollard's rho algorithm
([KatzLindell2020], Algorithm 10.2, p. 369). -/
def rhoGcd (N : ℕ) (a b : (ZMod N)ˣ) : ℕ :=
  (((a : ZMod N).val : ℤ) - (b : ZMod N).val).natAbs.gcd N

/-- A natural number `d` is a nontrivial factor of `N` if `d ∣ N` and `1 < d < N`. -/
def IsNontrivialFactor (N d : ℕ) : Prop :=
  d ∣ N ∧ 1 < d ∧ d < N

instance (N d : ℕ) : Decidable (IsNontrivialFactor N d) :=
  inferInstanceAs (Decidable (d ∣ N ∧ 1 < d ∧ d < N))

/-- Floyd tortoise-and-hare loop of Pollard's rho factoring algorithm ([KatzLindell2020],
Section 10.1.2, Algorithm 10.2, p. 369): iterate `(x, y) ↦ (F x, F (F y))` for at most `B` steps
and return the first nontrivial GCD `rhoGcd N x' y'`. -/
def rhoFactorLoop (N : ℕ) (F : (ZMod N)ˣ → (ZMod N)ˣ) :
    ℕ → (ZMod N)ˣ → (ZMod N)ˣ → Option ℕ
  | 0, _, _ => none
  | B + 1, x, y =>
    let x' := F x
    let y' := F (F y)
    let d := rhoGcd N x' y'
    if 1 < d ∧ d < N then some d else rhoFactorLoop N F B x' y'

/-! ### Soundness and exact failure characterization -/

/-- **Soundness of `rhoFactorLoop`**: every `some d` returned by `rhoFactorLoop N F B x y` is a
nontrivial divisor of `N` (`IsNontrivialFactor N d`). -/
theorem isNontrivialFactor_of_rhoFactorLoop_eq_some {N : ℕ} {F : (ZMod N)ˣ → (ZMod N)ˣ} :
    ∀ {B : ℕ} {x y : (ZMod N)ˣ} {d : ℕ},
      rhoFactorLoop N F B x y = some d → IsNontrivialFactor N d
  | 0, _, _, _, h => by simp [rhoFactorLoop] at h
  | B + 1, x, y, d, h => by
    simp only [rhoFactorLoop] at h
    split_ifs at h with h1
    · exact Option.some.inj h ▸ ⟨Nat.gcd_dvd_right _ _, h1⟩
    · exact isNontrivialFactor_of_rhoFactorLoop_eq_some h

/-- Any nontrivial factor of a semiprime `p * q` (with `p, q` prime) equals `p` or `q`. -/
theorem eq_prime_of_isNontrivialFactor_mul {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsNontrivialFactor (p * q) d) : d = p ∨ d = q := by
  obtain ⟨hd, h1, hlt⟩ := h
  by_cases hpd : p ∣ d
  · obtain ⟨e, rfl⟩ := hpd
    rcases (Nat.dvd_prime hq).mp ((Nat.mul_dvd_mul_iff_left hp.pos).mp hd) with rfl | rfl
    · exact .inl (mul_one p)
    · exact absurd rfl hlt.ne
  · rcases (Nat.dvd_prime hq).mp
        (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm.dvd_of_dvd_mul_left hd) with rfl | rfl
    · exact absurd rfl h1.ne'
    · exact .inr rfl

/-- **Semiprime soundness of `rhoFactorLoop`**: for `N = p * q` with `p, q` prime, any factor `d`
returned by `rhoFactorLoop (p * q) F B x y` satisfies `d = p ∨ d = q`. -/
theorem eq_prime_of_rhoFactorLoop_eq_some {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    {F : (ZMod (p * q))ˣ → (ZMod (p * q))ˣ} {x y : (ZMod (p * q))ˣ} {d : ℕ}
    (h : rhoFactorLoop (p * q) F B x y = some d) : d = p ∨ d = q :=
  eq_prime_of_isNontrivialFactor_mul hp hq (isNontrivialFactor_of_rhoFactorLoop_eq_some h)

/-- Stepwise characterization of when `rhoFactorLoop N F B x y` returns `none`. -/
theorem rhoFactorLoop_eq_none_iff (N : ℕ) (F : (ZMod N)ˣ → (ZMod N)ˣ) :
    ∀ (B : ℕ) (x y : (ZMod N)ˣ),
      rhoFactorLoop N F B x y = none ↔
        ∀ t, 1 ≤ t → t ≤ B →
          ¬ IsNontrivialFactor N (rhoGcd N (F^[t] x) ((F ∘ F)^[t] y))
  | 0, _, _ => by simp only [rhoFactorLoop, true_iff]; omega
  | B + 1, x, y => by
    rw [rhoFactorLoop]
    split_ifs with h1
    · exact ⟨by rintro ⟨⟩, fun h => (h 1 le_rfl (by omega) ⟨Nat.gcd_dvd_right _ _, h1⟩).elim⟩
    · rw [rhoFactorLoop_eq_none_iff N F B (F x) (F (F y))]
      refine ⟨fun hB t ht1 htB => ?_, fun h k hk1 hkB => ?_⟩
      · rcases t with _ | _ | k
        · omega
        · exact fun h => h1 h.2
        · simpa only [Function.iterate_succ_apply, Function.comp_apply] using
            hB (k + 1) (by omega) (by omega)
      · simpa only [Function.iterate_succ_apply, Function.comp_apply] using
          h (k + 1) (by omega) (by omega)

/-- **Exact failure characterization from a common start state `x₀`**:
`rhoFactorLoop N F B x₀ x₀ = none` if and only if no step `1 ≤ t ≤ B` produces a nontrivial GCD
between `F^[t] x₀` and `F^[2 * t] x₀`. -/
theorem rhoFactorLoop_start_eq_none_iff (N : ℕ) (F : (ZMod N)ˣ → (ZMod N)ˣ) (B : ℕ)
    (x₀ : (ZMod N)ˣ) :
    rhoFactorLoop N F B x₀ x₀ = none ↔
      ∀ t, 1 ≤ t → t ≤ B →
        ¬ IsNontrivialFactor N (rhoGcd N (F^[t] x₀) (F^[2 * t] x₀)) := by
  simp_rw [rhoFactorLoop_eq_none_iff, Function.iterate_mul F 2, show F^[2] = F ∘ F from rfl]

/-! ### Nontrivial GCD from a modulo-`p` collision -/

/-- **Good-pair GCD lemma** ([KatzLindell2020], Section 10.1.2, p. 368): if `p ∣ N` (`1 < p`) and
two distinct units `a ≠ b` in `(ZMod N)ˣ` are congruent modulo `p`, then `rhoGcd N a b` is a
nontrivial factor of `N`. -/
theorem isNontrivialFactor_rhoGcd_of_modEq {N p : ℕ} (hpN : p ∣ N) (hp1 : 1 < p)
    [NeZero N] {a b : (ZMod N)ˣ} (hne : a ≠ b)
    (hmod : (a : ZMod N).val ≡ (b : ZMod N).val [MOD p]) :
    IsNontrivialFactor N (rhoGcd N a b) := by
  have ha : (a : ZMod N).val < N := ZMod.val_lt _
  have hb : (b : ZMod N).val < N := ZMod.val_lt _
  set z : ℤ := ((a : ZMod N).val : ℤ) - (b : ZMod N).val
  have hz0 : z ≠ 0 := sub_ne_zero.mpr <| mod_cast fun h => hne (Units.ext (ZMod.val_injective N h))
  have hzlt : z.natAbs < N := by rcases Int.natAbs_eq z with h | h <;> omega
  have hpz : p ∣ z.natAbs := Int.ofNat_dvd_left.mp <| by
    simpa only [neg_sub] using dvd_neg.mpr (Nat.ModEq.dvd hmod)
  exact ⟨Nat.gcd_dvd_right _ _,
    hp1.trans_le (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) (NeZero.pos N))
      (Nat.dvd_gcd hpz hpN)),
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) (Nat.gcd_dvd_left _ _)).trans_lt hzlt⟩

/-! ### Floyd's tortoise-and-hare cycle-detection theorem -/

/-- **Floyd's cycle-detection persistence theorem** (the technique of [KatzLindell2020],
Section 6.4.2, Algorithm 6.9, p. 180, as used for Pollard's rho in Section 10.1.2, p. 369):
if `F` is congruence-compatible modulo `p`, then any collision
`(F^[i] x : ZMod N).val ≡ (F^[j] x : ZMod N).val [MOD p]` at indices `i < j` implies that there
exists a step `1 ≤ t ≤ j` at which the tortoise `F^[t] x` and hare `F^[2 * t] x` collide
modulo `p`. -/
theorem floyd_cycle_modEq {N p : ℕ} {F : (ZMod N)ˣ → (ZMod N)ˣ}
    (hF : ∀ u v : (ZMod N)ˣ,
      (u : ZMod N).val ≡ (v : ZMod N).val [MOD p] →
        (F u : ZMod N).val ≡ (F v : ZMod N).val [MOD p])
    {x : (ZMod N)ˣ} {i j : ℕ} (hij : i < j)
    (hcoll : (F^[i] x : ZMod N).val ≡ (F^[j] x : ZMod N).val [MOD p]) :
    ∃ t, 1 ≤ t ∧ t ≤ j ∧
      (F^[t] x : ZMod N).val ≡ (F^[2 * t] x : ZMod N).val [MOD p] := by
  set L := j - i
  have shift (m) : (F^[i + m] x : ZMod N).val ≡ (F^[j + m] x : ZMod N).val [MOD p] := by
    induction m with
    | zero => simpa using hcoll
    | succ m ih =>
      rw [← add_assoc, ← add_assoc, Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hF _ _ ih
  have period (c) : ∀ m,
      (F^[i + m] x : ZMod N).val ≡ (F^[i + m + L * c] x : ZMod N).val [MOD p] := by
    induction c with
    | zero => intro _; simp [Nat.ModEq.refl]
    | succ c ih =>
      intro m
      refine (ih m).trans ?_
      simpa only [show i + (m + L * c) = i + m + L * c by ring,
        show j + (m + L * c) = i + m + L * (c + 1) by rw [Nat.mul_succ]; omega]
        using shift (m + L * c)
  have hdiv := Nat.div_add_mod i L
  have hr := Nat.mod_lt i (by omega : 0 < L)
  refine ⟨L * (i / L) + L, by omega, by omega, ?_⟩
  simpa only [show i + (L - i % L) = L * (i / L) + L by omega,
    show L * (i / L) + L + L * (i / L + 1) = 2 * (L * (i / L) + L) by rw [Nat.mul_succ]; omega]
    using period (i / L + 1) (L - i % L)

end Cslib.Crypto
