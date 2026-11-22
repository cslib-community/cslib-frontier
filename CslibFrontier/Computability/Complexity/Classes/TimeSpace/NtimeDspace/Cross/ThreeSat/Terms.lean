/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactProg
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Decode

/-!
# The 3-SAT network, read by terms

Terms (`ProgTerm.Term`) that read the network `(rawW w s).net` of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Net.lean` from
the input word `w`, given a term for the size `s`:

* the decoding `lenT`, `offT`, `nT`, `widT`, `mT`, `svT` (`rawW`);
* the slot functions `presT`, `varT`, `signT`, `sameT`, `nextT`, `hasNextT`, `prevT`, `hasPrevT`;
* the accessors `edgesT`, `vertsT`, `endUT`, `endWT`, `degT`, `portT`, `funT`: the numbers of
  edges and vertices, the ends of an edge, the degree and the ports of a vertex, and the value
  of a vertex function at the bits of a number on its ports.

Each term has a `val_` lemma (`Exact.Val`: its value, in every extension of the environment, as a
function of the values of its arguments) and a `bd_` lemma (`Exact.Bd`: every value arising in its
evaluation is at most `M`, for arguments in range and `M ≥ 64 (s+2)^4`). Every loop runs over at
most `(s + 2)^2 + 1` positions or `3s` slots, so the accessors use `O(log s)` bits.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset

variable {w : List Bool} {M : ℕ} {env : List ℕ}

/-! ### Generic blocks -/

theorem val_input {a : Term} {x : ℕ} (ha : Val w a env x) : Val w (input a) env (ib w x) :=
  fun extra => by simp [ha extra]

theorem bd_input {a : Term} (ha : Bd w M a env) : Bd w M (input a) env := fun extra => ha extra

theorem val_pow2 {e : Term} {x : ℕ} (he : Val w e env x) : Val w (pow2 e) env (2 ^ x) :=
  fun extra => by simp [he extra]

theorem bd_pow2 {e : Term} {x : ℕ} (he : Val w e env x) (hbe : Bd w M e env) (h : 2 ^ x ≤ M) :
    Bd w M (pow2 e) env :=
  fun extra => ProgTerm.Term.bnd_pow2 w M e _ (hbe extra) (by rw [he extra]; exact h)

/-- A function of one term whose values are Booleans. -/
def FValB (w : List Bool) (f : Term → Term) (env : List ℕ) (p : ℕ → Bool) : Prop :=
  FVal w f env fun q => (p q).toNat

theorem val_ofBitsT {n : Term} {g : Term → Term} {N : ℕ} {b : ℕ → ℕ} (hn : Val w n env N)
    (hg : FVal w g env b) : Val w (TermBlocks.ofBitsT n g) env (TermBlocks.bitsNum N b) := by
  have := val_sumT hn (body := fun i => mul (bit (g i) (const 0)) (pow2 i))
    (F := fun k => b k % 2 * 2 ^ k) fun pre u q hu => by
      have := val_mul (val_bit (hg pre u q hu) (val_const 0 _)) (val_pow2 hu)
      simpa using this
  exact this

theorem bd_ofBitsT {n : Term} {g : Term → Term} {N : ℕ} {b : ℕ → ℕ} (hn : Val w n env N)
    (hbn : Bd w M n env) (hg : FVal w g env b)
    (hbg : ∀ pre u q, q < N → Val w u (pre ++ env) q → Bd w M u (pre ++ env) →
      Bd w M (g u) (pre ++ env))
    (hN : N ≤ M) (h2 : 2 ^ N ≤ M) : Bd w M (TermBlocks.ofBitsT n g) env := by
  refine bd_sumT hn (body := fun i => mul (bit (g i) (const 0)) (pow2 i))
    (F := fun k => b k % 2 * 2 ^ k) (fun pre u q hu => by
      have := val_mul (val_bit (hg pre u q hu) (val_const 0 _)) (val_pow2 hu)
      simpa using this) hbn hN ?_ fun pre u q hq hu hbu => ?_
  · exact ((TermBlocks.bitsNum_lt N b).le).trans h2
  · have h2q : 2 ^ q ≤ M := (Nat.pow_le_pow_right (by norm_num) hq.le).trans h2
    refine bd_mul (bd_bit (hbg pre u q hq hu hbu) (bd_const (Nat.zero_le _) _)) (bd_pow2 hu hbu h2q)
      (val_bit (hg pre u q hu) (val_const 0 _)) (val_pow2 hu) ?_
    have : b q / 2 ^ 0 % 2 ≤ 1 := by omega
    calc b q / 2 ^ 0 % 2 * 2 ^ q ≤ 1 * 2 ^ q := Nat.mul_le_mul_right _ this
      _ ≤ M := by simpa using h2q

theorem val_findT {n : Term} {test : Term → Term} {N : ℕ} {p : ℕ → Bool} (hn : Val w n env N)
    (ht : FValB w test env p) : Val w (TermBlocks.findT n test) env
        (TermBlocks.firstNat N p N) := by
  have := val_foldT (f := fun acc i => ite (lt acc n) acc (ite (test i) i acc)) hn hn
    (fun acc i => if acc < N then acc else if p i then i else acc) fun pre u u' a q hu hu' => by
      have := val_ite (val_lt hu (hn.ext pre)) hu (val_ite (ht pre u' q hu') hu' hu)
      refine fun extra => (this extra).trans ?_
      by_cases h1 : a < N
      · simp [h1]
      · cases hp : p q <;> simp [h1, hp]
  exact this

theorem bd_findT {n : Term} {test : Term → Term} {N : ℕ} {p : ℕ → Bool} (hn : Val w n env N)
    (hbn : Bd w M n env) (hN : N ≤ M) (ht : FValB w test env p)
    (hbt : ∀ pre u q, q < N → Val w u (pre ++ env) q → Bd w M u (pre ++ env) →
      Bd w M (test u) (pre ++ env)) : Bd w M (TermBlocks.findT n test) env := by
  refine bd_foldT (f := fun acc i => ite (lt acc n) acc (ite (test i) i acc)) hn hn
    (fun acc i => if acc < N then acc else if p i then i else acc) (fun pre u u' a q hu hu' => by
      have := val_ite (val_lt hu (hn.ext pre)) hu (val_ite (ht pre u' q hu') hu' hu)
      refine fun extra => (this extra).trans ?_
      by_cases h1 : a < N
      · simp [h1]
      · cases hp : p q <;> simp [h1, hp]) hbn hbn hN
    fun pre u u' a q hq _ hu hu' hbu hbu' => ?_
  exact bd_ite (bd_lt hbu (hbn.ext pre)) (val_lt hu (hn.ext pre)) (fun _ => hbu)
    (fun _ => bd_ite (hbt pre u' q hq hu' hbu') (ht pre u' q hu') (fun _ => hbu') (fun _ => hbu))

/-- The last `i < k` whose test is positive, or `d`. -/
def lastT (d k : Term) (test : Term → Term) : Term := foldT k d fun acc i => ite (test i) i acc

theorem val_lastT {d k : Term} {test : Term → Term} {D K : ℕ} {p : ℕ → Bool} (hd : Val w d env D)
    (hk : Val w k env K) (ht : FValB w test env p) : Val w (lastT d k test) env
        (lastNat D K p) := by
  have := val_foldT (f := fun acc i => ite (test i) i acc) hk hd
    (fun acc i => if p i then i else acc) fun pre u u' a q hu hu' => by
      have := val_ite (ht pre u' q hu') hu' hu
      refine fun extra => (this extra).trans ?_
      cases hp : p q <;> simp [hp]
  exact this

theorem bd_lastT {d k : Term} {test : Term → Term} {D K : ℕ} {p : ℕ → Bool} (hd : Val w d env D)
    (hbd : Bd w M d env) (hk : Val w k env K) (hbk : Bd w M k env) (hK : K ≤ M)
    (ht : FValB w test env p)
    (hbt : ∀ pre u q, q < K → Val w u (pre ++ env) q → Bd w M u (pre ++ env) →
      Bd w M (test u) (pre ++ env)) : Bd w M (lastT d k test) env := by
  refine bd_foldT (f := fun acc i => ite (test i) i acc) hk hd
    (fun acc i => if p i then i else acc) (fun pre u u' a q hu hu' => by
      have := val_ite (ht pre u' q hu') hu' hu
      refine fun extra => (this extra).trans ?_
      cases hp : p q <;> simp [hp]) hbk hbd hK fun pre u u' a q hq _ hu hu' hbu hbu' => ?_
  exact bd_ite (hbt pre u' q hq hu' hbu') (ht pre u' q hu') (fun _ => hbu') (fun _ => hbu)

/-- `min a b`. -/
def minT' (a b : Term) : Term := ite (lt b a) b a

theorem val_minT' {a b : Term} {x y : ℕ} (ha : Val w a env x) (hb : Val w b env y) :
    Val w (minT' a b) env (min x y) := by
  have := val_ite (val_lt hb ha) hb ha
  refine fun extra => (this extra).trans ?_
  by_cases h : y < x
  · simp [h, min_eq_right h.le]
  · simp [h, min_eq_left (by omega : x ≤ y)]

theorem bd_minT' {a b : Term} {x y : ℕ} (ha : Bd w M a env) (hb : Bd w M b env)
    (hva : Val w a env x)
    (hvb : Val w b env y) : Bd w M (minT' a b) env :=
  bd_ite (bd_lt hb ha) (val_lt hvb hva) (fun _ => hb) (fun _ => ha)

/-! ### Decoding -/

/-- `bnd s = (s + 2)^2`. -/
def bndT (sT : Term) : Term := mul (add sT (const 2)) (add sT (const 2))

/-- `lenW`. -/
def lenT (sT : Term) : Term :=
  TermBlocks.findT (add (bndT sT) (const 1)) fun i => Exact.eqT (input i) (const 2)

/-- `offW`. -/
def offT (sT : Term) : Term :=
  add (TermBlocks.findT (lenT sT) fun i =>
    mul (Exact.eqT (mod i (const 2)) (const 0)) (sub (const 1) (Exact.eqT (input i) (const 1))))
    (const 1)

/-- `nW`. -/
def nT (sT : Term) : Term :=
  TermBlocks.findT (sub (lenT sT) (offT sT)) fun k =>
    sub (const 1) (Exact.eqT (input (add (offT sT) k)) (const 1))

/-- `widW`. -/
def widT (sT : Term) : Term := bitLenT (add (mul (const 2) (nT sT)) (const 1))

/-- `mW`. -/
def mT (sT : Term) : Term :=
  minT' (div (sub (sub (sub (lenT sT) (offT sT)) (nT sT)) (const 1)) (mul (const 3) (widT sT))) sT

/-- `svW`. -/
def svT (sT tT : Term) : Term :=
  TermBlocks.ofBitsT (widT sT) fun b =>
    input (add (add (add (add (offT sT) (nT sT)) (const 1)) (mul tT (widT sT))) b)

section Decoding

variable {sT : Term} {s : ℕ}

theorem eqT_toNat {x y : ℕ} : (if x = y then 1 else 0) = (x == y).toNat := by
  symm; by_cases h : x = y <;> simp [h]

theorem val_bndT (hs : Val w sT env s) : Val w (bndT sT) env (bnd s) := by
  have := val_mul (val_add hs (val_const 2 env)) (val_add hs (val_const 2 env))
  rw [bnd, sq]; exact this

theorem val_lenT (hs : Val w sT env s) : Val w (lenT sT) env (lenW w s) := by
  refine val_findT (val_add (val_bndT hs) (val_const 1 env)) fun pre u q hu => ?_
  have := val_eqT (val_input hu) (val_const 2 (pre ++ env))
  rwa [eqT_toNat] at this

theorem val_offT (hs : Val w sT env s) : Val w (offT sT) env (offW w s) := by
  refine val_add (val_findT (val_lenT hs) fun pre u q hu => ?_) (val_const 1 env)
  have := val_mul (val_eqT (val_mod hu (val_const 2 _)) (val_const 0 _))
    (val_sub (val_const 1 _) (val_eqT (val_input hu) (val_const 1 _)))
  refine fun extra => (this extra).trans ?_
  symm; by_cases h1 : q % 2 = 0 <;> by_cases h2 : ib w q = 1 <;> simp [h1, h2]

theorem val_nT (hs : Val w sT env s) : Val w (nT sT) env (nW w s) := by
  refine val_findT (val_sub (val_lenT hs) (val_offT hs)) fun pre u q hu => ?_
  have := val_sub (val_const 1 _) (val_eqT (val_input (val_add ((val_offT hs).ext pre) hu))
    (val_const 1 _))
  refine fun extra => (this extra).trans ?_
  symm; by_cases h : ib w (offW w s + q) = 1 <;> simp [h]

theorem val_widT (hs : Val w sT env s) : Val w (widT sT) env (widW w s) :=
  val_bitLenT (val_add (val_mul (val_const 2 env) (val_nT hs)) (val_const 1 env)) (by omega)

theorem val_mT (hs : Val w sT env s) : Val w (mT sT) env (rawW w s).m :=
  val_minT' (val_div (val_sub (val_sub (val_sub (val_lenT hs) (val_offT hs)) (val_nT hs))
    (val_const 1 env)) (val_mul (val_const 3 env) (val_widT hs))) hs

theorem val_svT {tT : Term} {t : ℕ} (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (svT sT tT) env (svW w s t) := by
  refine val_ofBitsT (val_widT hs) fun pre u q hu => ?_
  have := val_input (val_add (val_add (val_add
      (val_add ((val_offT hs).ext pre) ((val_nT hs).ext pre))
    (val_const 1 _)) (val_mul (ht.ext pre) ((val_widT hs).ext pre))) hu)
  exact this

end Decoding

/-! ### Slot functions -/

/-- `pres`. -/
def presT (sT tT : Term) : Term := lt (const 0) (svT sT tT)
/-- `var`. -/
def varT (sT tT : Term) : Term := div (sub (svT sT tT) (const 1)) (const 2)
/-- `sign`. -/
def signT (sT tT : Term) : Term := mod (sub (svT sT tT) (const 1)) (const 2)
/-- `same`. -/
def sameT (sT tT t'T : Term) : Term := mul (presT sT t'T) (Exact.eqT (varT sT t'T) (varT sT tT))
/-- `3 m`. -/
def m3T (sT : Term) : Term := mul (const 3) (mT sT)
/-- `next`. -/
def nextT (sT tT : Term) : Term :=
  TermBlocks.findT (m3T sT) fun t' => mul (lt tT t') (sameT sT tT t')
/-- `hasNext`. -/
def hasNextT (sT tT : Term) : Term := mul (presT sT tT) (lt (nextT sT tT) (m3T sT))
/-- `prev`. -/
def prevT (sT tT : Term) : Term := lastT tT tT fun i => sameT sT tT i
/-- `hasPrev`. -/
def hasPrevT (sT tT : Term) : Term := mul (presT sT tT) (lt (prevT sT tT) tT)

section Slots

variable {sT tT t'T : Term} {s t t' : ℕ}

theorem val_presT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (presT sT tT) env ((rawW w s).pres t).toNat := by
  have := val_lt (val_const 0 env) (val_svT hs ht)
  refine fun extra => (this extra).trans ?_
  simp only [Raw.pres, rawW]
  symm; by_cases h : svW w s t = 0 <;> simp [h, Nat.pos_iff_ne_zero]

theorem val_varT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (varT sT tT) env ((rawW w s).var t) := by
  have h := val_div (val_sub (val_svT hs ht) (val_const 1 env)) (val_const 2 env)
  unfold Raw.var
  exact h

theorem val_signT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (signT sT tT) env ((rawW w s).sign t).toNat := by
  have := val_mod (val_sub (val_svT hs ht) (val_const 1 env)) (val_const 2 env)
  refine fun extra => (this extra).trans ?_
  simp only [Raw.sign, rawW]
  symm; rcases Nat.mod_two_eq_zero_or_one (svW w s t - 1) with h | h <;> simp [h]

theorem val_sameT (hs : Val w sT env s) (ht : Val w tT env t) (ht' : Val w t'T env t') :
    Val w (sameT sT tT t'T) env ((rawW w s).same t t').toNat := by
  have := val_mul (val_presT hs ht') (val_eqT (val_varT hs ht') (val_varT hs ht))
  refine fun extra => (this extra).trans ?_
  simp only [Raw.same]
  symm; cases (rawW w s).pres t' <;> by_cases h : (rawW w s).var t' = (rawW w s).var t <;> simp [h]

theorem val_m3T (hs : Val w sT env s) : Val w (m3T sT) env (3 * (rawW w s).m) := by
  have h := val_mul (val_const 3 env) (val_mT hs)
  exact h

theorem val_nextT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (nextT sT tT) env ((rawW w s).next t) := by
  refine val_findT (val_m3T hs) fun pre u q hu => ?_
  have := val_mul (val_lt (ht.ext pre) hu) (val_sameT (hs.ext pre) (ht.ext pre) hu)
  refine fun extra => (this extra).trans ?_
  symm; by_cases h : t < q <;> simp [h]

theorem val_hasNextT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (hasNextT sT tT) env ((rawW w s).hasNext t).toNat := by
  have := val_mul (val_presT hs ht) (val_lt (val_nextT hs ht) (val_m3T hs))
  refine fun extra => (this extra).trans ?_
  simp only [Raw.hasNext]
  symm; cases (rawW w s).pres t <;> by_cases h : (rawW w s).next t < 3 * (rawW w s).m <;> simp [h]

theorem val_prevT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (prevT sT tT) env ((rawW w s).prev t) :=
  val_lastT ht ht fun pre _u _q hu => val_sameT (hs.ext pre) (ht.ext pre) hu

theorem val_hasPrevT (hs : Val w sT env s) (ht : Val w tT env t) :
    Val w (hasPrevT sT tT) env ((rawW w s).hasPrev t).toNat := by
  have := val_mul (val_presT hs ht) (val_lt (val_prevT hs ht) ht)
  refine fun extra => (this extra).trans ?_
  simp only [Raw.hasPrev]
  symm; cases (rawW w s).pres t <;> by_cases h : (rawW w s).prev t < t <;> simp [h]

end Slots

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
