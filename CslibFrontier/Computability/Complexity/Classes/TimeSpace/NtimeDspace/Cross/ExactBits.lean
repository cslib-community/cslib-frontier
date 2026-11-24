/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactCRT
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactTerm

/-!
# The residue-to-binary program: terms and meanings

The terms of this file compute the functions of `ExactCRT` (selection of primes, group
products, Chinese-remainder coefficients, columns, carry chains) from a residue program `q`
closed over `[τ, n, p]`. A context `Ctx` holds the terms of the parameters `τ, n, H, X, E, W, r,
g, W^g`; `Ctx.Good` says that they have the values of a semantic context `SC`. Each piece has a
`val_` lemma stating its meaning. The value bounds are in `ExactBitsBd`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset

variable {w : List Bool} {env : List ℕ}

/-! ### Primality -/

/-- `1` if `x` is prime: `x > 1` and no `d + 2 < x` divides `x`. -/
def primeT (x : Term) : Term :=
  mul (lt (const 1) x) (prodT (sub x (const 2)) fun d => lt (const 0) (mod x (add d (const 2))))

theorem prime_iff_forall {p : ℕ} (h2 : 1 < p) : (∀ d ∈ range (p - 2), 0 < p % (d + 2)) ↔
    p.Prime := by
  rw [Nat.prime_def_lt]
  constructor
  · intro h
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases m with _ | _ | m
    · rw [Nat.zero_dvd] at hdvd; omega
    · rfl
    · have := h m (mem_range.mpr (by omega))
      rw [Nat.mod_eq_zero_of_dvd hdvd] at this
      omega
  · rintro ⟨_, h⟩ d hd
    rw [mem_range] at hd
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := h (d + 2) (by omega) (Nat.dvd_of_mod_eq_zero h0)
    omega

theorem val_primeT {x : Term} {v : ℕ} (hx : Val w x env v) :
    Val w (primeT x) env (if v.Prime then 1 else 0) := by
  have hb : FVal w (fun d => lt (const 0) (mod x (add d (const 2)))) env
      (fun d => if 0 < v % (d + 2) then 1 else 0) := fun pre u p hu =>
    val_lt (val_const 0 _) (val_mod (hx.ext pre) (val_add hu (val_const 2 _)))
  have := val_mul (val_lt (val_const 1 env) hx) (val_prodT (val_sub hx (val_const 2 env)) hb)
  refine fun extra => (this extra).trans ?_
  rw [prod_boole]
  by_cases h1 : 1 < v
  · rw [ite_eq_left h1, one_mul]
    by_cases hp : v.Prime
    · rw [ite_eq_left ((prime_iff_forall h1).mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp ((prime_iff_forall h1).mp h)), ite_eq_right hp]
  · rw [ite_eq_right h1, zero_mul, ite_eq_right (fun hp => h1 hp.one_lt)]

/-! ### The context -/

/-- The terms of the parameters. -/
structure Ctx where
  /-- The term of `τ`, the first argument of the residue program. -/
  τ : Term
  /-- The term of `n`, the second argument of the residue program. -/
  n : Term
  /-- The term of the lower end `H` of the prime window `(H, X]`. -/
  H : Term
  /-- The term of the upper end `X` of the prime window `(H, X]`. -/
  X : Term
  /-- The term of the bit bound `E`: the number decoded is at most `2^E`. -/
  E : Term
  /-- The term of the width `W`, the base in which tuples of `g` factors are packed. -/
  W : Term
  /-- The term of the group size `r`: the selected primes are grouped `r` at a time. -/
  r : Term
  /-- The term of the number `g` of groups. -/
  g : Term
  /-- The term of `W^g`, the number of packed tuples. -/
  Wg : Term

/-- The values of the parameters. -/
structure SC where
  /-- The first argument `τ` of the residue program. -/
  τ : ℕ
  /-- The second argument `n` of the residue program. -/
  n : ℕ
  /-- The lower end `H` of the prime window `(H, X]`. -/
  H : ℕ
  /-- The upper end `X` of the prime window `(H, X]`. -/
  X : ℕ
  /-- The bit bound `E`: the number decoded is at most `2^E`. -/
  E : ℕ
  /-- The width `W`, the base in which tuples of `g` factors are packed. -/
  W : ℕ
  /-- The group size `r`: the selected primes are grouped `r` at a time. -/
  r : ℕ
  /-- The number `g` of groups. -/
  g : ℕ

variable (w) in
/-- The parameter terms have the values of `s`. -/
def Ctx.Good (c : Ctx) (s : SC) (env : List ℕ) : Prop :=
  Val w c.τ env s.τ ∧ Val w c.n env s.n ∧ Val w c.H env s.H ∧ Val w c.X env s.X ∧
    Val w c.E env s.E ∧ Val w c.W env s.W ∧ Val w c.r env s.r ∧ Val w c.g env s.g ∧
    Val w c.Wg env (s.W ^ s.g)

theorem Ctx.Good.ext {c : Ctx} {s : SC} (h : c.Good w s env) (pre : List ℕ) :
    c.Good w s (pre ++ env) :=
  ⟨h.1.ext pre, h.2.1.ext pre, h.2.2.1.ext pre, h.2.2.2.1.ext pre, h.2.2.2.2.1.ext pre,
    h.2.2.2.2.2.1.ext pre, h.2.2.2.2.2.2.1.ext pre, h.2.2.2.2.2.2.2.1.ext pre,
    h.2.2.2.2.2.2.2.2.ext pre⟩

variable {c : Ctx} {s : SC} {q : Prog}

/-- The residues computed by `q`. -/
def resOf (w : List Bool) (q : Prog) (s : SC) (p : ℕ) : ℕ := q.eval w [s.τ, s.n, p]

/-! ### Selection -/

/-- `1` on the primes of the window. -/
def candT (c : Ctx) (x : Term) : Term :=
  mul (mul (lt c.H x) (lt x (add c.X (const 1)))) (primeT x)

theorem val_candT (hc : c.Good w s env) {x : Term} {v : ℕ} (hx : Val w x env v) :
    Val w (candT c x) env (if cand s.H s.X v then 1 else 0) := by
  have := val_mul (val_mul (val_lt hc.2.2.1 hx) (val_lt hx (val_add hc.2.2.2.1 (val_const 1 env))))
    (val_primeT hx)
  refine fun extra => (this extra).trans ?_
  unfold cand
  have e : v < s.X + 1 ↔ v ≤ s.X := Nat.lt_succ_iff
  by_cases h1 : s.H < v <;> by_cases h2 : v ≤ s.X <;> by_cases h3 : v.Prime <;>
    simp only [h1, h2, h3, e, ite_true, ite_false, and_self, and_true, and_false,
      mul_one, mul_zero]

/-- The rank of `x` among the window primes. -/
def rankT (c : Ctx) (x : Term) : Term := sumT x fun y => candT c y

theorem val_rankT (hc : c.Good w s env) {x : Term} {v : ℕ} (hx : Val w x env v) :
    Val w (rankT c x) env (rank s.H s.X v) := by
  have := val_sumT hx (fun pre u p hu => val_candT (hc.ext pre) hu)
  refine fun extra => (this extra).trans ?_
  rw [rank, Nat.count_eq_card_filter_range, sum_boole]
  simp

/-- `1` on the selected primes. -/
def selT (c : Ctx) (x : Term) : Term := mul (candT c x) (lt (rankT c x) (add c.E (const 1)))

theorem val_selT (hc : c.Good w s env) {x : Term} {v : ℕ} (hx : Val w x env v) :
    Val w (selT c x) env (if sel s.H s.X s.E v then 1 else 0) := by
  have := val_mul (val_candT hc hx) (val_lt (val_rankT hc hx)
      (val_add hc.2.2.2.2.1 (val_const 1 env)))
  refine fun extra => (this extra).trans ?_
  unfold sel
  by_cases h1 : cand s.H s.X v <;> by_cases h2 : rank s.H s.X v < s.E + 1 <;> simp [h1, h2]

/-- The group of `x`. -/
def grpT (c : Ctx) (x : Term) : Term := div (rankT c x) c.r

theorem val_grpT (hc : c.Good w s env) {x : Term} {v : ℕ} (hx : Val w x env v) :
    Val w (grpT c x) env (grp s.H s.X s.r v) :=
  val_div (val_rankT hc hx) hc.2.2.2.2.2.2.1

/-- The product of group `m`. -/
def QmT (c : Ctx) (m : Term) : Term :=
  prodT (add c.X (const 1)) fun x => ite (mul (selT c x) (eqT (grpT c x) m)) x (const 1)

theorem val_QmT (hc : c.Good w s env) {m : Term} {v : ℕ} (hm : Val w m env v) :
    Val w (QmT c m) env (Qm s.H s.X s.E s.r v) := by
  have hb : FVal w (fun x => ite (mul (selT c x) (eqT (grpT c x) m)) x (const 1)) env
      (fun x => if sel s.H s.X s.E x ∧ grp s.H s.X s.r x = v then x else 1) := by
    intro pre u p hu
    have := val_ite (val_mul (val_selT (hc.ext pre) hu) (val_eqT (val_grpT (hc.ext pre) hu)
      (hm.ext pre))) hu (val_const 1 _)
    refine fun extra => (this extra).trans ?_
    by_cases h1 : sel s.H s.X s.E p <;> by_cases h2 : grp s.H s.X s.r p = v <;> simp [h1, h2]
  exact val_prodT (val_add hc.2.2.2.1 (val_const 1 env)) hb

/-- `(Qt / p)^(p-2) mod p`. -/
def invT (c : Ctx) (p : Term) : Term :=
  letT (prodModT p (add c.X (const 1)) fun x =>
      ite (mul (selT c x) (sub (const 1) (eqT x p))) x (const 1)) fun base =>
    prodModT p (sub p (const 2)) fun _ => base

theorem val_invT (hc : c.Good w s env) {p : Term} {v : ℕ} (hp : Val w p env v) (hv : 2 ≤ v) :
    Val w (invT c p) env (invc s.H s.X s.E v) := by
  have hb : FVal w (fun x => ite (mul (selT c x) (sub (const 1) (eqT x p))) x (const 1)) env
      (fun x => if sel s.H s.X s.E x ∧ x ≠ v then x else 1) := by
    intro pre u y hu
    have := val_ite (val_mul (val_selT (hc.ext pre) hu)
      (val_sub (val_const 1 _) (val_eqT hu (hp.ext pre)))) hu (val_const 1 _)
    refine fun extra => (this extra).trans ?_
    by_cases h1 : sel s.H s.X s.E y <;> by_cases h2 : y = v <;> simp [h1, h2]
  refine val_letT (val_prodModT hp hv (val_add hc.2.2.2.1 (val_const 1 env)) hb) ?_
  intro pre u hu
  have := val_prodModT (hp.ext pre) hv (val_sub (hp.ext pre) (val_const 2 _))
    (F := fun _ => (∏ x ∈ range (s.X + 1), if sel s.H s.X s.E x ∧ x ≠ v then x else 1) % v)
    (fun pre' u' y _ => hu.ext pre')
  refine fun extra => (this extra).trans ?_
  rw [prod_const, card_range, invc]

/-- The Chinese-remainder coefficient at `p`. -/
def bT (q : Prog) (c : Ctx) (p : Term) : Term := mod (mul (call3 q c.τ c.n p) (invT c p)) p

theorem val_bT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) {p : Term} {v : ℕ}
    (hp : Val w p env v) (hv : 2 ≤ v) :
    Val w (bT q c p) env (bco s.H s.X s.E (resOf w q s) v) :=
  val_mod (val_mul (val_call3 hq hc.1 hc.2.1 hp) (val_invT hc hp hv)) hp

/-- The factors of the term of `p`. -/
def facT (q : Prog) (c : Ctx) (p m : Term) : Term :=
  ite (eqT m (grpT c p)) (mul (bT q c p) (div (QmT c m) p)) (QmT c m)

theorem val_facT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) {p m : Term} {v k : ℕ}
    (hp : Val w p env v) (hv : 2 ≤ v) (hm : Val w m env k) :
    Val w (facT q c p m) env (fac s.H s.X s.E s.r (resOf w q s) v k) := by
  have := val_ite (val_eqT hm (val_grpT hc hp))
    (val_mul (val_bT hq hc hp hv) (val_div (val_QmT hc hm) hp)) (val_QmT hc hm)
  refine fun extra => (this extra).trans ?_
  unfold fac
  by_cases h : k = grp s.H s.X s.r v <;> simp [h]

/-! ### Packed tuples -/

/-- `x ^ e`. -/
def pwT (x e : Term) : Term := prodT e fun _ => x

theorem val_pwT {x e : Term} {a b : ℕ} (hx : Val w x env a) (he : Val w e env b) :
    Val w (pwT x e) env (a ^ b) := by
  have := val_prodT he (F := fun _ => a) (fun pre _ _ _ => hx.ext pre)
  rwa [prod_const, card_range] at this

/-- Digit `m` of `u` in base `W`. -/
def digT (c : Ctx) (u m : Term) : Term := mod (div u (pwT c.W m)) c.W

theorem val_digT (hc : c.Good w s env) {u m : Term} {a b : ℕ} (hu : Val w u env a)
    (hm : Val w m env b) : Val w (digT c u m) env (dig s.W a b) :=
  val_mod (val_div hu (val_pwT hc.2.2.2.2.2.1 hm)) hc.2.2.2.2.2.1

/-- The digit sum of `u`. -/
def sdigT (c : Ctx) (u : Term) : Term := sumT c.g fun m => digT c u m

theorem val_sdigT (hc : c.Good w s env) {u : Term} {a : ℕ} (hu : Val w u env a) :
    Val w (sdigT c u) env (sdig s.W s.g a) :=
  val_sumT hc.2.2.2.2.2.2.2.1 fun pre _m _b hm => val_digT (hc.ext pre) (hu.ext pre) hm

/-- The product of the bits of the factors `f m` at the digits of `u`. -/
def pbitsT (c : Ctx) (f : Term → Term) (u : Term) : Term :=
  prodT c.g fun m => bit (f m) (digT c u m)

theorem val_pbitsT (hc : c.Good w s env) {f : Term → Term} {F : ℕ → ℕ} (hf : FVal w f env F)
    {u : Term} {a : ℕ} (hu : Val w u env a) : Val w (pbitsT c f u) env (pbits s.W s.g F a) :=
  val_prodT hc.2.2.2.2.2.2.2.1 fun pre m b hm =>
    val_bit (hf pre m b hm) (val_digT (hc.ext pre) (hu.ext pre) hm)

/-! ### Columns, quotient and carry chains -/

/-- The columns of `A`. -/
def colAT (q : Prog) (c : Ctx) (i : Term) : Term :=
  sumT (add c.X (const 1)) fun p => ite (selT c p)
    (sumT c.Wg fun u => ite (eqT (sdigT c u) i) (pbitsT c (facT q c p) u) (const 0)) (const 0)

theorem val_colAT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) {i : Term} {a : ℕ}
    (hi : Val w i env a) :
    Val w (colAT q c i) env (colA s.H s.X s.E s.W s.r s.g (resOf w q s) a) := by
  refine val_sumT (val_add hc.2.2.2.1 (val_const 1 env)) fun pre p v hp => ?_
  have hc' := hc.ext pre
  by_cases hs : sel s.H s.X s.E v
  · have hv : 2 ≤ v := (sel_prime hs).two_le
    have hin := val_sumT (n := c.Wg) hc'.2.2.2.2.2.2.2.2
      (body := fun u => ite (eqT (sdigT c u) i) (pbitsT c (facT q c p) u) (const 0))
      (F := fun u => if sdig s.W s.g u = a then
        pbits s.W s.g (fac s.H s.X s.E s.r (resOf w q s) v) u else 0)
      fun pre' u b hu => by
        have hc'' := hc'.ext pre'
        have := val_ite (val_eqT (val_sdigT hc'' hu) ((hi.ext pre).ext pre'))
          (val_pbitsT hc'' (fun pre'' m k
              hm => val_facT hq (hc''.ext pre'') ((hp.ext pre').ext pre'')
            hv hm) hu) (val_const 0 _)
        refine fun extra => (this extra).trans ?_
        by_cases h : sdig s.W s.g b = a <;> simp [h]
    have := val_ite (val_selT hc' hp) hin (val_const 0 _)
    refine fun extra => (this extra).trans ?_
    simp [hs]
  · have := val_ite (val_selT hc' hp) (val_const 0 (pre ++ env)) (val_const 0 _)
    refine fun extra => ?_
    have h1 := val_selT hc' hp extra
    change (ite (selT c p) _ (const 0)).denote w _ = _
    rw [denote_ite, h1]
    simp [hs]

/-- The columns of `Qt`. -/
def colQT (c : Ctx) (i : Term) : Term :=
  sumT c.Wg fun u => ite (eqT (sdigT c u) i) (pbitsT c (QmT c) u) (const 0)

theorem val_colQT (hc : c.Good w s env) {i : Term} {a : ℕ} (hi : Val w i env a) :
    Val w (colQT c i) env (colQ s.H s.X s.E s.W s.r s.g a) := by
  refine val_sumT hc.2.2.2.2.2.2.2.2 fun pre u b hu => ?_
  have hc' := hc.ext pre
  have := val_ite (val_eqT (val_sdigT hc' hu) (hi.ext pre))
    (val_pbitsT hc' (fun pre' m k hm => val_QmT (hc'.ext pre') hm) hu) (val_const 0 _)
  refine fun extra => (this extra).trans ?_
  by_cases h : sdig s.W s.g b = a <;> simp [h]

/-- The quotient `⌊A / Qt⌋`. -/
def kqT (q : Prog) (c : Ctx) : Term :=
  div (add (sumT (add c.X (const 1)) fun p =>
        ite (selT c p) (div (mul (bT q c p) (pwT (const 2) c.W)) p) (const 0))
      (sumT (add c.X (const 1)) fun p => selT c p))
    (pwT (const 2) c.W)

theorem val_kqT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) :
    Val w (kqT q c) env (kq s.H s.X s.E s.W (resOf w q s)) := by
  have h2W := val_pwT (val_const 2 env) hc.2.2.2.2.2.1
  have h1 := val_sumT (val_add hc.2.2.2.1 (val_const 1 env))
    (body := fun p => ite (selT c p) (div (mul (bT q c p) (pwT (const 2) c.W)) p) (const 0))
    (F := fun p => if sel s.H s.X s.E p then bco s.H s.X s.E (resOf w q s) p * 2 ^ s.W / p else 0)
    fun pre p v hp => by
      have hc' := hc.ext pre
      by_cases hs : sel s.H s.X s.E v
      · have := val_ite (val_selT hc' hp) (val_div (val_mul (val_bT hq hc' hp
          (sel_prime hs).two_le) (h2W.ext pre)) hp) (val_const 0 _)
        refine fun extra => (this extra).trans ?_
        simp [hs]
      · refine fun extra => ?_
        change (ite (selT c p) _ (const 0)).denote w _ = _
        rw [denote_ite, val_selT hc' hp extra]
        simp [hs]
  have h2 := val_sumT (val_add hc.2.2.2.1 (val_const 1 env)) (body := fun p => selT c p)
    (F := fun p => if sel s.H s.X s.E p then 1 else 0) fun pre p v hp => val_selT (hc.ext pre) hp
  exact val_div (val_add h1 h2) h2W

/-- The carry into position `j` of the columns `col`. -/
def chainT (col : Term → Term) (j : Term) : Term :=
  foldT j (const 0) fun acc i => div (add (col i) acc) (const 2)

theorem val_chainT {col : Term → Term} {C : ℕ → ℕ} (hcol : FVal w col env C) {j : Term} {a : ℕ}
    (hj : Val w j env a) : Val w (chainT col j) env (chain C a) :=
  val_foldT hj (val_const 0 env) (fun acc i => (C i + acc) / 2)
    fun pre _u u' _p k hu hu' => val_div (val_add (hcol pre u' k hu') hu) (val_const 2 _)

/-- Bit `j` of `∑ col i · 2^i`. -/
def bitOfT (col : Term → Term) (j : Term) : Term := mod (add (col j) (chainT col j)) (const 2)

theorem val_bitOfT {col : Term → Term} {C : ℕ → ℕ} (hcol : FVal w col env C) {j : Term} {a : ℕ}
    (hj : Val w j env a) : Val w (bitOfT col j) env (bitOf C a) :=
  val_mod (val_add (hcol [] j a (by simpa using hj)) (val_chainT hcol hj)) (val_const 2 env)

/-- The columns of `A + 2^J - kq · Qt`. -/
def colZT (q : Prog) (c : Ctx) (k i : Term) : Term :=
  add (add (colAT q c i) (sub (const 1) (bitOfT (fun i => mul k (colQT c i)) i)))
    (eqT i (const 0))

theorem val_colZT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) {k : Term}
    (hk : Val w k env (kq s.H s.X s.E s.W (resOf w q s))) {i : Term} {a : ℕ}
    (hi : Val w i env a) :
    Val w (colZT q c k i) env (colZ s.H s.X s.E s.W s.r s.g (resOf w q s) a) := by
  have hcol : FVal w (fun i => mul k (colQT c i)) env
      (fun i => kq s.H s.X s.E s.W (resOf w q s) * colQ s.H s.X s.E s.W s.r s.g i) :=
    fun pre u b hu => val_mul (hk.ext pre) (val_colQT (hc.ext pre) hu)
  have := val_add (val_add (val_colAT hq hc hi) (val_sub (val_const 1 env) (val_bitOfT hcol hi)))
    (val_eqT hi (val_const 0 env))
  exact this

/-- The output bit. -/
def outT (q : Prog) (c : Ctx) (k j : Term) : Term :=
  ite (lt j (mul (add c.g (const 1)) c.W)) (bitOfT (colZT q c k) j) (const 0)

theorem val_outT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) {k : Term}
    (hk : Val w k env (kq s.H s.X s.E s.W (resOf w q s))) {j : Term} {a : ℕ}
    (hj : Val w j env a) :
    Val w (outT q c k j) env (out s.H s.X s.E s.W s.r s.g (resOf w q s) a) := by
  have hcol : FVal w (colZT q c k) env (colZ s.H s.X s.E s.W s.r s.g (resOf w q s)) :=
    fun pre u b hu => val_colZT hq (hc.ext pre) (hk.ext pre) hu
  have := val_ite (val_lt hj (val_mul (val_add hc.2.2.2.2.2.2.2.1 (val_const 1 env))
    hc.2.2.2.2.2.1)) (val_bitOfT hcol hj) (val_const 0 env)
  refine fun extra => (this extra).trans ?_
  unfold out
  by_cases h : a < (s.g + 1) * s.W <;> simp [h]

end Cslib.Complexity.NtimeDspace.Cross.Exact
