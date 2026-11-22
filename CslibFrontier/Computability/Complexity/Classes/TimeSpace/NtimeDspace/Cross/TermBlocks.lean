/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.InnerLoopTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ParserTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Building blocks for terms

Small `Term`s (`ProgTerm`) used by the explicit 3-CNF network (`ThreeSat/`), each with a
`denote_*` lemma, stability, and a tier lemma (`tm_*`) under explicit size hypotheses.

## Main definitions

* `sliceT`: a block of binary digits.
* `bitsNum`, `ofBitsT`: the number with given binary digits, and a term computing it.
* `firstNat`, `findT`: the first `i < N` with a given property (or `N`), and a term computing it.
* `anyT`: whether some `i < n` passes a test.
* `ImplLt`: a term implements a numeric function below a bound.

## Main results

* `firstNat_spec`, `firstNat_eq_iff`: the characterization of `firstNat`.
* `denote_ofBitsT`, `denote_findT`, `denote_anyT`, `allT_denote_lt'`: the values of the terms.
* `tm_sliceT`, `tm_ofBitsT`, `tm_findT`, `tm_allTv`, `tm_anyTv`: their tiers.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.TermBlocks

open ProgTerm ProgTerm.Term Finset

variable {w : List Bool}

/-! ### Building blocks -/

section Blocks

/-- `(x / 2^off) % 2^len`: the `len` bits of `x` from position `off`. -/
def sliceT (x off len : Term) : Term := mod (div x (pow2 off)) (pow2 len)

@[simp] theorem denote_sliceT (x off len : Term) (env : List ℕ) :
    (sliceT x off len).denote w env = x.denote w env / 2 ^ off.denote w env % 2 ^
        len.denote w env := by
  simp [sliceT]

theorem stableAt_pow2 {a : Term} {env : List ℕ} (h : StableAt w a env) : StableAt w (pow2 a) env :=
  fun extra => by simp only [denote_pow2, h extra]

theorem stableAt_sliceT {x off len : Term} {env : List ℕ} (hx : StableAt w x env)
    (ho : StableAt w off env) (hl : StableAt w len env) : StableAt w (sliceT x off len) env :=
  hx.div (stableAt_pow2 ho) |>.mod (stableAt_pow2 hl)

/-- The number whose `k`-th binary digit is `b k % 2`, for `k < n`. -/
def bitsNum (n : ℕ) (b : ℕ → ℕ) : ℕ := ∑ k ∈ range n, b k % 2 * 2 ^ k

theorem bitsNum_eq_fin (n : ℕ) (b : ℕ → ℕ) :
    bitsNum n b = (finFunctionFinEquiv (fun k : Fin
        n => (⟨b k % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) : ℕ) := by
  rw [finFunctionFinEquiv_apply, bitsNum]
  exact (Fin.sum_univ_eq_sum_range (fun k => b k % 2 * 2 ^ k) n).symm

theorem bitsNum_lt (n : ℕ) (b : ℕ → ℕ) : bitsNum n b < 2 ^ n := by
  rw [bitsNum_eq_fin]; exact Fin.isLt _

/-- The digits of `bitsNum`. -/
theorem bitsNum_digit (n : ℕ) (b : ℕ → ℕ) (i : ℕ) :
    bitsNum n b / 2 ^ i % 2 = if i < n then b i % 2 else 0 := by
  split_ifs with hi
  · have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv
      (fun k : Fin n => (⟨b k % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))) ⟨i, hi⟩
    rw [Equiv.symm_apply_apply] at this
    rw [bitsNum_eq_fin]; exact this.symm
  · have hlt : bitsNum n b / 2 ^ i = 0 :=
      Nat.div_eq_of_lt ((bitsNum_lt n b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hlt]

theorem testBit_bitsNum (n : ℕ) (b : ℕ → ℕ) (i : ℕ) :
    ((bitsNum n b).testBit i).toNat = if i < n then b i % 2 else 0 := by
  rw [Nat.toNat_testBit, bitsNum_digit]

theorem bitsNum_congr {n : ℕ} {b b' : ℕ → ℕ} (h : ∀ i < n, b i % 2 = b' i % 2) :
    bitsNum n b = bitsNum n b' :=
  sum_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]

/-- Two numbers below `2^n` with the same first `n` digits are equal. -/
theorem eq_of_digits {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ i < n, a / 2 ^ i % 2 = b / 2 ^ i % 2) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < n
  · have := h i hi
    rw [← Nat.toNat_testBit, ← Nat.toNat_testBit] at this
    cases h1 : a.testBit i <;> cases h2 : b.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (hb.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- A number below `2^n` is the number of its digits. -/
theorem bitsNum_digits {n a : ℕ} (ha : a < 2 ^ n) : bitsNum n (fun i => a / 2 ^ i % 2) = a :=
  eq_of_digits (bitsNum_lt _ _) ha fun i hi => by rw [bitsNum_digit, ite_eq_left hi, Nat.mod_mod]

theorem bitsNum_zero (n : ℕ) : bitsNum n (fun _ => 0) = 0 := by simp [bitsNum]

/-- `ofBitsT n g`: the number whose `k`-th digit is the parity of `g k`, for `k < n`. -/
def ofBitsT (n : Term) (g : Term → Term) : Term := sumT
    n fun i => mul (bit (g i) (const 0)) (pow2 i)

theorem denote_ofBitsT (n : Term) (g : Term → Term) (env : List ℕ) (b : ℕ → ℕ)
    (hg : ∀ acc k, (g (lvl env.length)).denote w (acc :: k :: env) = b k) :
    (ofBitsT n g).denote w env = bitsNum (n.denote w env) b := by
  rw [ofBitsT, denote_sumT _ _ env (fun k => b k % 2 * 2 ^ k) (fun acc k => by
    simp only [denote_mul, denote_bit, denote_const, denote_pow2, denote_lvl_index, hg,
      Nat.toNat_testBit, pow_zero, Nat.div_one])]
  rfl

/-- The value of `ofBitsT n g` is below `2^n`, whatever `g` computes. -/
theorem ofBitsT_lt (n : Term) (g : Term → Term) (env : List ℕ) :
    (ofBitsT n g).denote w env < 2 ^ n.denote w env := by
  simp only [ofBitsT, sumT, denote_foldT, denote_const]
  suffices ∀ k, foldAcc w (fun acc i => add acc (mul (bit (g i) (const 0)) (pow2 i))) env
      0 k < 2 ^ k from
    this _
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [foldAcc_succ]
    simp only [denote_add, denote_mul, denote_bit, denote_pow2, denote_lvl_acc, denote_lvl_index]
    have key : ∀ (b : Bool) (acc : ℕ), acc < 2 ^ k → acc + b.toNat * 2 ^ k < 2 ^ (k + 1) := by
      intro b acc h
      have h2 := Nat.mul_le_mul_right (2 ^ k) (Bool.toNat_le b)
      rw [pow_succ]; omega
    exact key _ _ ih

/-- The first `i < N` with `p i`, or `N` (the fold of `findT`). -/
def firstNat (N : ℕ) (p : ℕ → Bool) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => if acc < N then acc else if p i then i else acc) N

theorem firstNat_spec (N : ℕ) (p : ℕ → Bool) (k : ℕ) (hk : k ≤ N) :
    (firstNat N p k < N → firstNat N p k < k ∧ p (firstNat N p k) = true) ∧
      (firstNat N p k = N ∨ firstNat N p k < N) ∧ ∀ j < min k (firstNat N p k), p j = false := by
  induction k with
  | zero => simp [firstNat]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hs : firstNat N p (k + 1) =
        if firstNat N p k < N then firstNat N p k else if p k then k else firstNat N p k := by
      rw [firstNat, List.range_succ, List.foldl_append]
      rfl
    rw [hs]
    by_cases hlt : firstNat N p k < N
    · rw [ite_eq_left hlt]
      obtain ⟨hk1, hk2⟩ := h1 hlt
      refine ⟨fun _ => ⟨by omega, hk2⟩, Or.inr hlt, fun j hj => h3 j (by omega)⟩
    · rw [ite_eq_right hlt]
      have heq : firstNat N p k = N := by omega
      by_cases hp : p k = true
      · rw [ite_eq_left hp]
        refine ⟨fun _ => ⟨by omega, hp⟩, Or.inr (by omega), fun j hj => h3 j (by omega)⟩
      · rw [ite_eq_right hp]
        refine ⟨fun h => absurd h hlt, h2, fun j hj => ?_⟩
        rcases Nat.lt_or_ge j k with hjk | hjk
        · exact h3 j (by omega)
        · have : j = k := by omega
          subst this; simpa using hp

/-- The characterization of `firstNat N p N`: below `N` it is the first `j` with `p j`. -/
theorem firstNat_eq_iff (N : ℕ) (p : ℕ → Bool) (j : ℕ) (hj : j < N) :
    firstNat N p N = j ↔ p j = true ∧ ∀ i < j, p i = false := by
  obtain ⟨h1, h2, h3⟩ := firstNat_spec N p N le_rfl
  constructor
  · rintro rfl
    exact ⟨(h1 hj).2, fun i hi => h3 i (by omega)⟩
  · rintro ⟨hpj, hlt⟩
    rcases h2 with h | h
    · exact absurd hpj (by rw [h3 j (by omega)]; simp)
    · obtain ⟨-, hp⟩ := h1 h
      rcases lt_trichotomy (firstNat N p N) j with h' | h' | h'
      · rw [hlt _ h'] at hp; exact absurd hp (by simp)
      · exact h'
      · rw [h3 j (by omega)] at hpj; exact absurd hpj (by simp)

theorem firstNat_eq_N (N : ℕ) (p : ℕ → Bool) (h : ∀ i < N, p i = false) : firstNat N p N = N := by
  obtain ⟨h1, h2, -⟩ := firstNat_spec N p N le_rfl
  rcases h2 with h2 | h2
  · exact h2
  · rw [h _ h2] at h1; exact absurd (h1 h2).2 (by simp)

/-- `List.find?` over `List.finRange N` is `firstNat`. -/
theorem find?_finRange (N : ℕ) (p : Fin N → Bool) :
    ((List.finRange N).find? p).map Fin.val =
      if firstNat N (fun i => if h : i < N then p ⟨i, h⟩ else false) N < N then
        some (firstNat N (fun i => if h : i < N then p ⟨i, h⟩ else false) N) else none := by
  set q : ℕ → Bool := fun i => if h : i < N then p ⟨i, h⟩ else false
  cases hf : (List.finRange N).find? p with
  | none =>
    rw [List.find?_eq_none] at hf
    have : ∀ i < N, q i = false := fun i hi => by
      simp only [q, dite_eq_left hi]
      simpa using hf ⟨i, hi⟩ (List.mem_finRange _)
    rw [firstNat_eq_N N q this]; simp
  | some b =>
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨hb, i, hi, hib, hbefore⟩ := hf
    have hbv : firstNat N q N = b := by
      rw [firstNat_eq_iff N q b b.2]
      refine ⟨by simp only [q, dite_eq_left b.2]; exact hb, fun k hk => ?_⟩
      have hkN : k < N := hk.trans b.2
      simp only [q, dite_eq_left hkN]
      have hib' : i = b := by rw [← hib]; simp
      have := hbefore k (by omega)
      simpa using this
    rw [hbv, ite_eq_left b.2]; rfl

/-- `findT n test`: the first `i < n` whose test is positive, or `n`. -/
def findT (n : Term) (test : Term → Term) : Term :=
  foldT n n fun acc i => ite (lt acc n) acc (ite (test i) i acc)

theorem denote_findT (n : Term) (test : Term → Term) (env : List ℕ) (hn : StableAt w n env)
    (p : ℕ → Bool) (ht : ∀ acc k, 0 < (test (lvl env.length)).denote w (acc :: k :: env) ↔ p k =
        true) :
    (findT n test).denote w env = firstNat (n.denote w env) p (n.denote w env) := by
  simp only [findT, denote_foldT]
  rw [foldAcc_eq _ env (fun acc i => if acc < n.denote w env then acc else if p i then i else acc)
    (fun acc k => ?_)]
  · rfl
  · simp only [denote_ite, denote_lt, denote_lvl_acc, denote_lvl_index, hn.cons₂, ht]
    by_cases h1 : acc < n.denote w env
    · simp [h1]
    · by_cases h2 : p k = true <;> simp [h1, h2]

/-- `1` if some test `i < n` gives `1`, for `0/1`-valued tests. -/
def anyT (n : Term) (test : Term → Term) : Term := lt (const 0) (sumT n test)

theorem denote_anyT (n : Term) (test : Term → Term) (env : List ℕ) (Pr : ℕ → Prop)
    [DecidablePred Pr]
    (ht : ∀ acc i, (test (lvl env.length)).denote w (acc :: i :: env) = if Pr i then 1 else 0) :
    (anyT n test).denote w env = if ∃ i < n.denote w env, Pr i then 1 else 0 := by
  rw [anyT, denote_lt, denote_const, denote_sumT _ _ env (fun i => if Pr i then 1 else 0)
    (fun acc i => ht acc i)]
  by_cases h : ∃ i < n.denote w env, Pr i
  · obtain ⟨i, hi, hp⟩ := h
    have hpos : 0 < ∑ k ∈ range (n.denote w env), if Pr k then 1 else 0 :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i, mem_range.mpr hi, by simp [hp]⟩
    simp only [hpos, ite_true]
    exact (ite_eq_left ⟨i, hi, hp⟩).symm
  · have h0 : ∑ k ∈ range (n.denote w env), (if Pr k then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => ite_eq_right fun hp => h ⟨i, mem_range.mp hi, hp⟩
    simp only [h0, lt_irrefl, ite_false]
    exact (ite_eq_right h).symm

/-- A sum over `k < n` whose body is known only for `k < n`. -/
theorem denote_sumT_lt (n : Term) (body : Term → Term) (env : List ℕ) (c : ℕ → ℕ)
    (hb : ∀ acc k, k < n.denote w env → (body (lvl env.length)).denote w (acc :: k :: env) = c k) :
    (sumT n body).denote w env = ∑ k ∈ range (n.denote w env), c k := by
  simp only [sumT, denote_foldT, denote_const]
  suffices ∀ j ≤ n.denote w env, foldAcc w (fun acc i => add acc (body i)) env 0 j = ∑ k ∈
      range j, c k from
    this _ le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [foldAcc_succ, sum_range_succ, ← ih (by omega)]
    simp only [denote_add, denote_lvl_acc, hb _ j (by omega)]

/-- `f` maps stable arguments to stable results, and computes `F` on arguments below `V`. -/
def ImplLt (w : List Bool) (env : List ℕ) (f : Term → Term) (V : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
    StableAt w (f a) (pre ++ env) ∧ (a.denote w (pre ++ env) < V → (f a).denote w (pre ++ env) = F
        (a.denote w (pre ++ env)))

theorem ImplLt.extend {env : List ℕ} {f : Term → Term} {V : ℕ} {F : ℕ → ℕ} (h : ImplLt w env f V F)
    (pre : List ℕ) : ImplLt w (pre ++ env) f V F := fun pre' a ha => by
  rw [← List.append_assoc] at ha ⊢; exact h _ a ha

/-- `ImplLt` at an environment of the form `acc :: k :: env`. -/
theorem ImplLt.at₂ {env : List ℕ} {f : Term → Term} {V : ℕ} {F : ℕ → ℕ} (h : ImplLt w env f V F)
    (acc k : ℕ) {a : Term} (ha : StableAt w a (acc :: k :: env)) :
    StableAt w (f a) (acc :: k :: env) ∧
      (a.denote w (acc :: k :: env) < V → (f a).denote w (acc :: k :: env) = F
          (a.denote w (acc :: k :: env))) :=
  h [acc, k] a ha

theorem ImplLt.comp {env : List ℕ} {f g : Term → Term} {V V' : ℕ} {F G : ℕ → ℕ}
    (hf : ImplLt w env f V F) (hg : ImplLt w env g V' G) (hFV : ∀ a < V, F a < V') :
    ImplLt w env (fun a => g (f a)) V (fun a => G (F a)) := fun pre a ha => by
  obtain ⟨h1, h2⟩ := hf pre a ha
  obtain ⟨h3, h4⟩ := hg pre (f a) h1
  refine ⟨h3, fun hlt => ?_⟩
  rw [h4 (by rw [h2 hlt]; exact hFV _ hlt), h2 hlt]

/-- `allT` with tests known only below the bound. -/
theorem allT_denote_lt' (n : Term) (test : Term → Term) (env : List ℕ) (Pr : ℕ → Prop)
    [DecidablePred Pr]
    (ht : ∀ acc i, i < n.denote w env →
      (test (lvl env.length)).denote w (acc :: i :: env) = if Pr i then 1 else 0) :
    (allT n test).denote w env = if ∀ i < n.denote w env, Pr i then 1 else 0 := by
  rw [allT, denote_eqT, denote_sumT_lt _ _ env (fun i => if Pr i then 0 else 1) (fun acc i hi => by
    simp only [denote_sub, denote_const, ht acc i hi]; split_ifs <;> rfl), denote_const]
  by_cases hall : ∀ i < n.denote w env, Pr i
  · rw [ite_eq_left hall, ite_eq_left (Finset.sum_eq_zero fun i
      hi => ite_eq_left (hall i (Finset.mem_range.mp hi)))]
  · rw [ite_eq_right hall, ite_eq_right]
    obtain ⟨i, hi, hni⟩ : ∃ i < n.denote w env, ¬ Pr i := by
      by_contra h; exact hall fun i hi => by_contra fun hp => h ⟨i, hi, hp⟩
    intro hzero
    have := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_range.mpr hi)
    simp [hni] at this

/-- A fold whose step is known only below the count. -/
theorem foldAcc_eq_lt (f : Term → Term → Term) (env : List ℕ) (step : ℕ → ℕ → ℕ) (init N : ℕ)
    (hstep : ∀ acc k, k < N → (f (lvl (env.length + 1)) (lvl env.length)).denote w
        (acc :: k :: env) =
      step acc k) : foldAcc w f env init N = (List.range N).foldl step init := by
  suffices ∀ j ≤ N, foldAcc w f env init j = (List.range j).foldl step init from this N le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j
      ih => rw [foldAcc_succ, hstep _ _ (by omega), ih (by omega), List.range_succ,
          List.foldl_append]; rfl

theorem foldl_max_eq_sup (g : ℕ → ℕ) (init N : ℕ) :
    (List.range N).foldl (fun acc k => max acc (g k)) init = max init ((range N).sup g) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.range_add_one, Finset.sup_insert]
    simp only [List.foldl_cons, List.foldl_nil]
    change max (max init _) (g N) = max init (max (g N) _)
    omega

/-! #### Tiers of the blocks -/

variable {L : ℕ}

/-- `x / 2^off % 2^len` keeps the tier of `x`. -/
theorem tm_sliceT {x off len : Term} {env : List ℕ} {dx d1 d2 : ℕ} (hx : Tm w L dx x env)
    (ho : Tm w L d1 off env) (hd1 : d1 ≤ 32) (hoV : Sm w L off (32 * L) env)
    (hl : Tm w L d2 len env) (hd2 : d2 ≤ 32) (hlV : Sm w L len (32 * L) env) (hL : 2 ≤ L) :
    Tm w L dx (sliceT x off len) env :=
  t_mod_left (t_div hx (t_pow2 ho hd1 hoV le_rfl hL)) (t_pow2 hl hd2 hlV le_rfl hL)

/-- `x / 2^off % 2^len` has tier `d` when `len < d·L`. -/
theorem tm_sliceT_len {x off len : Term} {env : List ℕ} {dx d1 d2 d : ℕ} (hx : Tm w L dx x env)
    (ho : Tm w L d1 off env) (hd1 : d1 ≤ 32) (hoV : Sm w L off (32 * L) env)
    (hl : Tm w L d2 len env) (hd2 : d2 ≤ 32) (hlV : Sm w L len (d * L) env) (hd : d ≤ 32)
    (hL : 2 ≤ L) : Tm w L d (sliceT x off len) env :=
  t_mod (t_div hx (t_pow2 ho hd1 hoV le_rfl hL)) (t_pow2 hl hd2 hlV hd hL) Pos.pow2'

/-- `ofBitsT n g` has tier `d` when `n ≤ V ≤ d·L`. -/
theorem tm_ofBitsT {n : Term} {g : Term → Term} {env : List ℕ} {dn dg d V : ℕ}
    (hn : Tm w L dn n env) (hnV : Le w L n V env) (hV : V ≤ d * L)
    (hg : TmFv w L g dn V dg env) (hd : dn + 1 + d ≤ 32) (hL : 2 ≤ L) :
    Tm w L d (ofBitsT n g) env := by
  have hsum : Tm w L (dn + (1 + d)) (ofBitsT n g) env := by
    refine t_sumTv' hn hnV (fun env' he y hy hys hyv => ?_) (by omega) (by omega)
    exact t_mul (t_bit (hg.app he hy hys hyv) (t_const (by
      have : (0 : ℕ) < 2 ^ L := by positivity
      exact this)) (by omega))
      (t_pow2_lt hy (by omega) hyv hV (by omega) hL) (by omega)
  intro pre hp
  refine ⟨(hsum pre hp).1, (ofBitsT_lt n g _).trans_le ?_⟩
  exact (Nat.pow_le_pow_right (by norm_num) (hnV pre hp)).trans
      (Nat.pow_le_pow_right (by norm_num) hV)

/-- `findT n test` keeps the tier of `n`. -/
theorem tm_findT {n : Term} {test : Term → Term} {env : List ℕ} {dn dt V : ℕ}
    (hn : Tm w L dn n env) (hdn : dn ≤ 32) (hnV : Le w L n V env)
    (ht : TmFv w L test dn V dt env) (hL : 1 ≤ L) : Tm w L dn (findT n test) env := by
  refine tm_foldTv hn hdn hnV hn (fun env' he x y hx hy hys hyv => ?_) hdn
  exact (t_ite (t_lt hx (hn.ext he) hL) hx (t_ite (ht.app he hy hys hyv) hy hx)).mono
    (by simp)

theorem tm_eqT {a b : Term} {env : List ℕ} {da db : ℕ} (ha : Tm w L da a env) (hb : Tm w L db b env)
    (hL : 1 ≤ L) : Tm w L 1 (eqT a b) env :=
  t_sub (t_const (Nat.one_lt_two_pow (by omega)))
      (t_add (t_lt ha hb hL) (t_lt hb ha hL) hL (by norm_num))

theorem tm_leT {a b : Term} {env : List ℕ} {da db : ℕ} (ha : Tm w L da a env) (hb : Tm w L db b env)
    (hL : 1 ≤ L) : Tm w L 1 (leT a b) env :=
  t_sub (t_const (Nat.one_lt_two_pow (by omega))) (t_lt hb ha hL)

/-- `allT` has tier `1`, for tests of any tier. -/
theorem tm_allTv {n : Term} {test : Term → Term} {env : List ℕ} {dn V dt : ℕ} (hn : Tm w L dn n env)
    (hnV : Le w L n V env) (ht : TmFv w L test dn V dt env) (hdn : dn + 1 ≤ 32) (hL : 1 ≤ L) :
    Tm w L 1 (allT n test) env :=
  tm_eqT (t_sumTv' hn hnV (db := 1) (fun env' he y hy hys hyv =>
    t_sub (t_const (Nat.one_lt_two_pow (by omega))) (ht.app he hy hys hyv)) hL hdn)
    (t_const (k := 0) (by positivity)) hL

/-- `anyT` has tier `1`, for tests of tier `1`. -/
theorem tm_anyTv {n : Term} {test : Term → Term} {env : List ℕ} {dn V : ℕ} (hn : Tm w L dn n env)
    (hnV : Le w L n V env) (ht : TmFv w L test dn V 1 env) (hdn : dn + 1 ≤ 32) (hL : 1 ≤ L) :
    Tm w L 1 (anyT n test) env :=
  t_lt (t_const (k := 0) (by positivity)) (t_sumTv' hn hnV ht hL hdn) hL

end Blocks

end Cslib.Complexity.NtimeDspace.Cross.TermBlocks
