/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameIte
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameLib

/-!
# Programs on label codes

Program terms (`ProgTerm.Term`) computing the functions of `CodeNum.lean` exactly, with value
lemmas (`val_*`: the term is stable and denotes the numeric function of its arguments' values) and
tier lemmas (`tm_*`: in the tier calculus of `Tame.lean`, every value is below `2^(d·L)`).

Arguments are stable terms with known values (`Val`, as in LeafTerm). User steps of
the generic fold are term functions with a value contract (`ValF3`, `ValF2`, `ValF1`) and a
boundedness contract on stable arguments (`TmV3`, `TmV2`, `TmV1`).

The tier lemmas assume `4 ≤ L` (`10 ≤ L` for `codeWidthT`), a fuel `B` and a width `W` of tier `1`
with values at most `L`, and positions of tier `1 ≤ dq ≤ 64`; codes may have any tier. Garbage
costs no more than a code: a reader runs at most `B` entries with at most `B` leading zeros per
gamma code, and a writer writes nothing past bit `W`. The parse state is packed as
`(position - q) + 2^(2B+2) · weight`, the writer state as `code + 2^(W+1) (length + 2^(W+1) prev)`.

## Main definitions

* `zeroRunT`, `readBitsT`, `gammaValT`, `gammaEndT`: reading a gamma code.
* `ctrlT` (the packed parse state), `msNT`, `entET`, `entMT`, `msEndT`: the entries of a multiset
  code and its end; `msFoldT g a B c q` and `msSumT f B c q`: a fold and a sum over the entries.
* `wtT`, `cardT`, `countT`, `topT`, `kthT`, `msLeT`, `labelWtT`, `validT`, `sqrtT`, `codeWidthT`.
* `topBitT`, `gammaNumT`, `appendAccT`, `appendPosT`: writing a gamma code; `ocCodeT`, `ocLenT`:
  the code of a multiset with given multiplicities; `addCodeT`, `addLenT`, `subCodeT`, `subLenT`.

## Main results

* Values: `val_*` for every term; on genuine codes `val_wtT_msCode`, `val_countT_msCode`,
  `val_kthT_msCode`, `val_msLeT_msCode`, `val_msEndT_msCode`, `val_addCodeT_msCode`,
  `val_subCodeT_msCode`, `val_labelWtT_labelCode`, `val_validT_decode`, `val_labelWtT_decode`.
* Tiers: `tm_msFoldT` (accumulator tier along the run), `tm_msFoldT_cl` (a step closed in tier
  `du`), `tm_msSumT`; `tm_entET` (`3`), `tm_entMT` (`2`), `tm_msNT` (`1`), `tm_msEndT`
  (`max dq 3 + 1`), `tm_wtT` (`5`), `tm_cardT` (`3`), `tm_countT` (`2`), `tm_topT` (`4`),
  `tm_kthT`, `tm_msLeT` (`1`), `tm_labelWtT` (`6`), `tm_validT` (`1`), `tm_codeWidthT`,
  `tm_appendAccT`, `tm_appendPosT` (`1`), `tm_ocCodeT`, `tm_ocLenT` (`1`), `tm_addCodeT`,
  `tm_subCodeT` (`1`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term

variable {w : List Bool} {env : List ℕ}

/-! ### Stable terms with known values -/

/-- `t` is stable at `env` with value `n`. -/
def Val (w : List Bool) (env : List ℕ) (t : Term) (n : ℕ) : Prop :=
  StableAt w t env ∧ t.denote w env = n

namespace Val

variable {t : Term} {n m : ℕ}

theorem ext (h : Val w env t n) (pre : List ℕ) : Val w (pre ++ env) t n :=
  ⟨h.1.extend pre, (h.1 pre).trans h.2⟩

theorem at2 (h : Val w env t n) (pre : List ℕ) (a k : ℕ) : Val w (a :: k :: (pre ++ env)) t n :=
  h.ext (a :: k :: pre)

theorem congr (h : Val w env t n) (e : n = m) : Val w env t m := e ▸ h

theorem extE {L : ℕ} (h : Val w env t n) {E : List ℕ} (hE : Ext L E env) : Val w E t n := by
  obtain ⟨p, _, rfl⟩ := hE; exact h.ext p

theorem of_denote (F : ℕ) (h : ∀ pre : List ℕ, t.denote w (pre ++ env) = F) : Val w env t F :=
  ⟨fun pre => (h pre).trans (by simpa using (h []).symm), by simpa using h []⟩

end Val

section Combinators

variable {a b c t e i n : Term} {A B' C T E I N : ℕ}

theorem val_const (k : ℕ) : Val w env (const k) k := ⟨stableAt_const k env, rfl⟩
theorem val_add (ha : Val w env a A) (hb : Val w env b B') : Val w env (add a b) (A + B') :=
  ⟨ha.1.add hb.1, by rw [denote_add, ha.2, hb.2]⟩
theorem val_sub (ha : Val w env a A) (hb : Val w env b B') : Val w env (sub a b) (A - B') :=
  ⟨ha.1.sub hb.1, by rw [denote_sub, ha.2, hb.2]⟩
theorem val_mul (ha : Val w env a A) (hb : Val w env b B') : Val w env (mul a b) (A * B') :=
  ⟨ha.1.mul hb.1, by rw [denote_mul, ha.2, hb.2]⟩
theorem val_div (ha : Val w env a A) (hb : Val w env b B') : Val w env (div a b) (A / B') :=
  ⟨ha.1.div hb.1, by rw [denote_div, ha.2, hb.2]⟩
theorem val_mod (ha : Val w env a A) (hb : Val w env b B') : Val w env (mod a b) (A % B') :=
  ⟨ha.1.mod hb.1, by rw [denote_mod, ha.2, hb.2]⟩
theorem val_lt (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (lt a b) (if A < B' then 1 else 0) :=
  ⟨ha.1.lt hb.1, by rw [denote_lt, ha.2, hb.2]⟩
theorem val_bit (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (bit a b) (A.testBit B').toNat :=
  ⟨ha.1.bit hb.1, by rw [denote_bit, ha.2, hb.2]⟩
theorem val_eqT (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (eqT a b) (if A = B' then 1 else 0) :=
  ⟨ha.1.eqT hb.1, by rw [denote_eqT, ha.2, hb.2]⟩
theorem val_ite (hc : Val w env c C) (ht : Val w env t T) (he : Val w env e E) :
    Val w env (ite c t e) (if 0 < C then T else E) :=
  ⟨hc.1.ite ht.1 he.1, by rw [denote_ite, hc.2, ht.2, he.2]⟩

theorem val_acc (E : List ℕ) (x k : ℕ) : Val w (x :: k :: E) (lvl (E.length + 1)) x :=
  ⟨stableAt_lvl (by simp), denote_lvl_acc _ _ _⟩

theorem val_idx (E : List ℕ) (x k : ℕ) : Val w (x :: k :: E) (lvl E.length) k :=
  ⟨stableAt_lvl (by simp), denote_lvl_index _ _ _⟩

theorem foldl_range_congr {f g : ℕ → ℕ → ℕ} {N : ℕ} (h : ∀ a k, k < N → f a k = g a k) (a : ℕ) :
    (List.range N).foldl f a = (List.range N).foldl g a := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih fun a k hk => h a k (by omega)]
    exact h _ _ (by omega)

/-- A fold whose body has the step `step` for counters below the count. -/
theorem val_foldT {f : Term → Term → Term} {step : ℕ → ℕ → ℕ} (hn : Val w env n N)
    (hi : Val w env i I) (hb : ∀ (pre : List ℕ) (x k : ℕ), k < N →
      Val w (x :: k :: (pre ++ env)) (f (lvl ((pre ++ env).length + 1)) (lvl (pre ++ env).length))
        (step x k)) :
    Val w env (foldT n i f) ((List.range N).foldl step I) :=
  Val.of_denote _ fun pre => by
    rw [denote_foldT, (hn.ext pre).2, (hi.ext pre).2]
    unfold foldAcc
    exact foldl_range_congr (fun x k hk => (hb pre x k hk).2) I

theorem val_sumT {body : Term → Term} {g : ℕ → ℕ} (hn : Val w env n N)
    (hb : ∀ (pre : List ℕ) (x k : ℕ), k < N →
      Val w (x :: k :: (pre ++ env)) (body (lvl (pre ++ env).length)) (g k)) :
    Val w env (sumT n body) (∑ k ∈ Finset.range N, g k) := by
  have := val_foldT (f := fun acc i => add acc (body i)) (step := fun x k => x + g k)
      hn (val_const 0)
    fun pre x k hk => val_add (val_acc _ x k) (hb pre x k hk)
  rw [foldl_add_sum, Nat.zero_add] at this
  exact this

private theorem foldl_mul_two (E : ℕ) : (List.range E).foldl (fun x _ => x * 2) 1 = 2 ^ E := by
  induction E with
  | zero => rfl
  | succ E ih => rw [List.range_succ, List.foldl_append, ih, pow_succ]; rfl

theorem val_pow2 (he : Val w env e E) : Val w env (pow2 e) (2 ^ E) :=
  (val_foldT (f := fun acc _ => mul acc (const 2)) (step := fun x _ => x * 2) he (val_const 1)
    fun _ x k _ => val_mul (val_acc _ x k) (val_const 2)).congr (foldl_mul_two E)

/-- `min a b`. -/
def cminT (a b : Term) : Term := ite (lt a b) a b
/-- `max a b`. -/
def cmaxT (a b : Term) : Term := ite (lt a b) b a

theorem val_cminT (ha : Val w env a A) (hb : Val w env b B') : Val w env (cminT a b) (min A B') :=
  (val_ite (val_lt ha hb) ha hb).congr (by split_ifs <;> omega)

theorem val_cmaxT (ha : Val w env a A) (hb : Val w env b B') : Val w env (cmaxT a b) (max A B') :=
  (val_ite (val_lt ha hb) hb ha).congr (by split_ifs <;> omega)

end Combinators

/-! ### Reading a gamma code -/

/-- `zeroRun B c q`. -/
def zeroRunT (B c q : Term) : Term :=
  foldT B (const 0) fun z i => add z (mul (eqT z i) (sub (const 1) (bit c (add q i))))

/-- `readBits c q n`. -/
def readBitsT (c q n : Term) : Term :=
  foldT n (const 0) fun a j => add (mul (const 2) a) (bit c (add q j))

/-- The value of the gamma code at bit `q`. -/
def gammaValT (B c q : Term) : Term :=
  readBitsT c (add q (zeroRunT B c q)) (add (zeroRunT B c q) (const 1))

/-- The end of the gamma code at bit `q`. -/
def gammaEndT (B c q : Term) : Term := add (add q (mul (const 2) (zeroRunT B c q))) (const 1)

section Gamma

variable {B c q : Term} {Bv cv qv : ℕ}

theorem val_zeroRunT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (zeroRunT B c q) (zeroRun Bv cv qv) := by
  refine val_foldT hB (val_const 0) fun pre x k _ => ?_
  refine (val_add (val_acc _ x k) (val_mul (val_eqT (val_acc _ x k) (val_idx _ x k))
    (val_sub (val_const 1) (val_bit (hc.at2 pre x k) (val_add (hq.at2 pre x k)
      (val_idx _ x k)))))).congr ?_
  by_cases h1 : x = k <;> cases hb : cv.testBit (qv + k) <;> simp [h1]

theorem val_readBitsT {n : Term} {nv : ℕ} (hc : Val w env c cv) (hq : Val w env q qv)
    (hn : Val w env n nv) : Val w env (readBitsT c q n) (readBits cv qv nv) :=
  val_foldT hn (val_const 0) fun pre x k _ =>
    val_add (val_mul (val_const 2) (val_acc _ x k))
      (val_bit (hc.at2 pre x k) (val_add (hq.at2 pre x k) (val_idx _ x k)))

theorem val_gammaValT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (gammaValT B c q) (gammaN Bv cv qv).1 :=
  val_readBitsT hc (val_add hq (val_zeroRunT hB hc hq))
      (val_add (val_zeroRunT hB hc hq) (val_const 1))

theorem val_gammaEndT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (gammaEndT B c q) (gammaN Bv cv qv).2 :=
  val_add (val_add hq (val_mul (val_const 2) (val_zeroRunT hB hc hq))) (val_const 1)

end Gamma

/-! ### The parse state, packed -/

/-- The field base of the packed parse state, `2^(2B + 2)`. -/
def mT (B : Term) : Term := pow2 (add (mul (const 2) B) (const 2))

/-- One parse step on the packed state `(position - q) + 2^(2B+2) · weight`. -/
def ctrlStepT (B c q s : Term) : Term :=
  add (sub (gammaEndT B c (gammaEndT B c (add q (mod s (mT B))))) q)
    (mul (mT B) (add (div s (mT B)) (gammaValT B c (add q (mod s (mT B))))))

/-- The packed parse state after `min k B` entries. -/
def ctrlT (B c q k : Term) : Term :=
  foldT (cminT k B) (sub (gammaEndT B c q) q) fun s _ => ctrlStepT B c q s

/-- The number of entries of the multiset code at bit `q`. -/
def msNT (B c q : Term) : Term := cminT (sub (gammaValT B c q) (const 1)) B

/-- The element of entry `k`. -/
def entET (B c q k : Term) : Term :=
  sub (add (div (ctrlT B c q k) (mT B)) (gammaValT B c (add q (mod (ctrlT B c q k) (mT B)))))
    (const 1)

/-- The multiplicity of entry `k`. -/
def entMT (B c q k : Term) : Term :=
  gammaValT B c (gammaEndT B c (add q (mod (ctrlT B c q k) (mT B))))

/-- The end of the multiset code at bit `q`. -/
def msEndT (B c q : Term) : Term := add q (mod (ctrlT B c q (msNT B c q)) (mT B))

/-- The packed parse state. -/
def ctrlP (B c q k : ℕ) : ℕ := (ctrl B c q k).1 - q + 2 ^ (2 * B + 2) * (ctrl B c q k).2

theorem iterate_stepC_le (B c : ℕ) : ∀ (k : ℕ) (s : ℕ × ℕ),
    ((stepC B c)^[k] s).1 ≤ s.1 + k * (4 * B + 2) ∧ ((stepC B c)^[k] s).2 ≤ s.2 + k * 2 ^ (B + 1)
  | 0, s => by simp
  | k + 1, s => by
    obtain ⟨h1, h2⟩ := iterate_stepC_le B c k s
    rw [Function.iterate_succ_apply']
    obtain ⟨t, ht⟩ : ∃ t, (stepC B c)^[k] s = t := ⟨_, rfl⟩
    rw [ht] at h1 h2 ⊢
    have e1 := gammaN_snd_le B c t.1
    have e2 := gammaN_snd_le B c (gammaN B c t.1).2
    have e3 := gammaN_fst_lt B c t.1
    simp only [stepC]
    constructor <;> nlinarith

theorem two_mul_add_one_lt (B : ℕ) : 2 * B + 1 < 2 ^ (B + 1) := by
  have := Nat.lt_two_pow_self (n := B); rw [pow_succ]; omega

theorem ctrl_bounds (B c q k : ℕ) : q ≤ (ctrl B c q k).1 ∧
    (ctrl B c q k).1 - q < 2 ^ (2 * B + 2) ∧ (ctrl B c q k).2 < 2 ^ (2 * B + 2) := by
  have hmin : min k B ≤ B := min_le_right _ _
  obtain ⟨h1, h2⟩ := iterate_stepC_le B c (min k B) ((gammaN B c q).2, 0)
  have hge := iterate_stepC_fst_ge B c (min k B) ((gammaN B c q).2, 0)
  have e0 := gammaN_snd_le B c q
  have e1 := gammaN_snd B c q
  have hb := two_mul_add_one_lt B
  have hb2 := Nat.lt_two_pow_self (n := B + 1)
  have hsq : 2 ^ (2 * B + 2) = 2 ^ (B + 1) * 2 ^ (B + 1) := by rw [← pow_add]; ring_nf
  simp only [ctrl] at h1 h2 hge ⊢
  refine ⟨by omega, ?_, ?_⟩
  · have : min k B * (4 * B + 2) ≤ B * (4 * B + 2) := Nat.mul_le_mul_right _ hmin
    have : (2 * B + 1) * (2 * B + 1) < 2 ^ (B + 1) * 2 ^ (B + 1) := Nat.mul_lt_mul'' hb hb
    have : (2 * B + 1) * (2 * B + 1) = 2 * B + 1 + B * (4 * B + 2) := by ring
    rw [hsq]; omega
  · have : min k B * 2 ^ (B + 1) ≤ B * 2 ^ (B + 1) := Nat.mul_le_mul_right _ hmin
    have : B * 2 ^ (B + 1) < 2 ^ (B + 1) * 2 ^ (B + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    rw [hsq]; omega

/-- The numeric parse step on packed states. -/
def ctrlStepN (B c q s : ℕ) : ℕ :=
  (gammaN B c (gammaN B c (q + s % 2 ^ (2 * B + 2))).2).2 - q +
    2 ^ (2 * B + 2) * (s / 2 ^ (2 * B + 2) + (gammaN B c (q + s % 2 ^ (2 * B + 2))).1)

theorem unpack_mod {M x o : ℕ} (ho : o < M) : (o + M * x) % M = o := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho]

theorem unpack_div {M x o : ℕ} (ho : o < M) : (o + M * x) / M = x := by
  have hM : 0 < M := by omega
  rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ho, Nat.zero_add]

theorem foldl_ctrlStepN (B c q : ℕ) : ∀ k ≤ B,
    (List.range k).foldl (fun s _ => ctrlStepN B c q s) ((gammaN B c q).2 - q) = ctrlP B c q k := by
  intro k hk
  induction k with
  | zero => simp [ctrlP, ctrl]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨b0, b1, b2⟩ := ctrl_bounds B c q k
    have hm : min (k + 1) B = min k B + 1 := by omega
    have hs : ctrl B c q (k + 1) = stepC B c (ctrl B c q k) := by
      simp only [ctrl, hm, Function.iterate_succ_apply']
    rw [ctrlStepN, ctrlP, unpack_mod b1, unpack_div b1, Nat.add_sub_cancel' b0, ctrlP, hs]
    rfl

section Parse

variable {B c q k : Term} {Bv cv qv kv : ℕ}

theorem val_mT (hB : Val w env B Bv) : Val w env (mT B) (2 ^ (2 * Bv + 2)) :=
  val_pow2 (val_add (val_mul (val_const 2) hB) (val_const 2))

theorem val_ctrlStepT {s : Term} {sv : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hs : Val w env s sv) :
    Val w env (ctrlStepT B c q s) (ctrlStepN Bv cv qv sv) := by
  have hp := val_add hq (val_mod hs (val_mT hB))
  exact val_add (val_sub (val_gammaEndT hB hc (val_gammaEndT hB hc hp)) hq)
    (val_mul (val_mT hB) (val_add (val_div hs (val_mT hB)) (val_gammaValT hB hc hp)))

theorem val_ctrlT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) : Val w env (ctrlT B c q k) (ctrlP Bv cv qv kv) := by
  have := val_foldT (f := fun s _ => ctrlStepT B c q s) (step := fun s _ => ctrlStepN Bv cv qv s)
    (val_cminT hk hB) (val_sub (val_gammaEndT hB hc hq) hq)
    fun pre x j
        _ => val_ctrlStepT (hB.at2 pre x j) (hc.at2 pre x j) (hq.at2 pre x j) (val_acc _ x j)
  rw [foldl_ctrlStepN Bv cv qv _ (min_le_right _ _)] at this
  refine this.congr ?_
  simp only [ctrlP, ctrl, Nat.min_assoc, min_self]

theorem val_msNT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (msNT B c q) (msN Bv cv qv) :=
  val_cminT (val_sub (val_gammaValT hB hc hq) (val_const 1)) hB

theorem ctrl_unpack (B c q k : ℕ) :
    ctrlP B c q k % 2 ^ (2 * B + 2) = (ctrl B c q k).1 - q ∧
      ctrlP B c q k / 2 ^ (2 * B + 2) = (ctrl B c q k).2 := by
  obtain ⟨-, b1, -⟩ := ctrl_bounds B c q k
  exact ⟨unpack_mod b1, unpack_div b1⟩

theorem val_entET (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) : Val w env (entET B c q k) (entE Bv cv qv kv) := by
  have h := val_ctrlT hB hc hq hk
  refine (val_sub (val_add (val_div h (val_mT hB))
    (val_gammaValT hB hc (val_add hq (val_mod h (val_mT hB))))) (val_const 1)).congr ?_
  obtain ⟨u1, u2⟩ := ctrl_unpack Bv cv qv kv
  rw [u1, u2, Nat.add_sub_cancel' (ctrl_bounds Bv cv qv kv).1]
  rfl

theorem val_entMT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) : Val w env (entMT B c q k) (entM Bv cv qv kv) := by
  have h := val_ctrlT hB hc hq hk
  refine (val_gammaValT hB hc (val_gammaEndT hB hc (val_add hq (val_mod h (val_mT hB))))).congr ?_
  rw [(ctrl_unpack Bv cv qv kv).1, Nat.add_sub_cancel' (ctrl_bounds Bv cv qv kv).1]
  rfl

theorem val_msEndT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (msEndT B c q) (msEnd Bv cv qv) := by
  refine (val_add hq (val_mod (val_ctrlT hB hc hq (val_msNT hB hc hq)) (val_mT hB))).congr ?_
  rw [(ctrl_unpack Bv cv qv _).1, Nat.add_sub_cancel' (ctrl_bounds Bv cv qv _).1]
  rfl

end Parse

/-! ### Folds over the entries -/

variable (w) in
/-- `g` computes `G` on stable arguments, in every extension of `env`. -/
def ValF3 (g : Term → Term → Term → Term) (G : ℕ → ℕ → ℕ → ℕ) (env : List ℕ) : Prop :=
  ∀ (pre : List ℕ) (x y z : Term) (X Y Z : ℕ), Val w (pre ++ env) x X → Val w (pre ++ env) y Y →
    Val w (pre ++ env) z Z → Val w (pre ++ env) (g x y z) (G X Y Z)

/-- **A fold over the entries** of the multiset code at bit `q`: `a ← g a e μ` for each element `e`
with multiplicity `μ`, in increasing order. -/
def msFoldT (g : Term → Term → Term → Term) (a B c q : Term) : Term :=
  foldT (msNT B c q) a fun acc k => g acc (entET B c q k) (entMT B c q k)

/-- A sum over the entries. -/
def msSumT (f : Term → Term → Term) (B c q : Term) : Term :=
  sumT (msNT B c q) fun k => f (entET B c q k) (entMT B c q k)

section Fold

variable {B c q a : Term} {Bv cv qv av : ℕ}

theorem val_msFoldT_gen {g : Term → Term → Term → Term} {G : ℕ → ℕ → ℕ → ℕ} {n : Term} {nv : ℕ}
    (hg : ValF3 w g G env) (hn : Val w env n nv) (ha : Val w env a av) (hB : Val w env B Bv)
    (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (foldT n a fun acc k => g acc (entET B c q k) (entMT B c q k))
      ((List.range nv).foldl (fun a k => G a (entE Bv cv qv k) (entM Bv cv qv k)) av) :=
  val_foldT hn ha fun pre x k _ =>
    hg (x :: k :: pre) _ _ _ _ _ _ (val_acc _ x k)
      (val_entET (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))
      (val_entMT (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))

theorem val_msFoldT {g : Term → Term → Term → Term} {G : ℕ → ℕ → ℕ → ℕ} (hg : ValF3 w g G env)
    (ha : Val w env a av) (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (msFoldT g a B c q) (msFoldN G av Bv cv qv) :=
  val_msFoldT_gen hg (val_msNT hB hc hq) ha hB hc hq

variable (w) in
/-- `f` computes `F` on stable arguments, in every extension of `env`. -/
def ValF2 (f : Term → Term → Term) (F : ℕ → ℕ → ℕ) (env : List ℕ) : Prop :=
  ∀ (pre : List ℕ) (y z : Term) (Y Z : ℕ), Val w (pre ++ env) y Y → Val w (pre ++ env) z Z →
    Val w (pre ++ env) (f y z) (F Y Z)

theorem val_msSumT_gen {f : Term → Term → Term} {F : ℕ → ℕ → ℕ} {n : Term} {nv : ℕ}
    (hf : ValF2 w f F env) (hn : Val w env n nv) (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) :
    Val w env (sumT n fun k => f (entET B c q k) (entMT B c q k))
      (∑ k ∈ Finset.range nv, F (entE Bv cv qv k) (entM Bv cv qv k)) :=
  val_sumT hn fun pre x k _ =>
    hf (x :: k :: pre) _ _ _ _
      (val_entET (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))
      (val_entMT (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))

theorem val_msSumT {f : Term → Term → Term} {F : ℕ → ℕ → ℕ} (hf : ValF2 w f F env)
    (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (msSumT f B c q)
      (∑ k ∈ Finset.range (msN Bv cv qv), F (entE Bv cv qv k) (entM Bv cv qv k)) :=
  val_msSumT_gen hf (val_msNT hB hc hq) hB hc hq

end Fold

/-! ### Instances: weight, cardinality, multiplicity, order statistics, inclusion -/

/-- The weight `∑ (e + 1) μ` of the multiset code at bit `q`. -/
def wtT (B c q : Term) : Term := msSumT (fun e μ => mul (add e (const 1)) μ) B c q

/-- The cardinality `∑ μ` of the multiset code at bit `q`. -/
def cardT (B c q : Term) : Term := msSumT (fun _ μ => μ) B c q

/-- The multiplicity of `y` in the multiset code at bit `q`. -/
def countT (B c q y : Term) : Term := msFoldT (fun a e μ => ite (eqT e y) μ a) (const 0) B c q

/-- One more than the largest element of the multiset code at bit `q`. -/
def topT (B c q : Term) : Term := msFoldT (fun a e _ => cmaxT a (add e (const 1))) (const 0) B c q

/-- The fold of `kthT`. -/
def kthFoldT (B c q k : Term) : Term :=
  msFoldT (fun s e μ => ite (lt k s) s (ite (lt s μ) (add (add k (const 1)) e) (sub s μ))) k B c q

/-- The `k`-th element (from `0`) of the sorted multiset code at bit `q`, default `d`. -/
def kthT (B c q k d : Term) : Term :=
  ite (lt k (kthFoldT B c q k)) (sub (kthFoldT B c q k) (add k (const 1))) d

/-- `1` if the multiset code at bit `q` of `c` is included in the one at bit `q'` of `c'`. -/
def msLeT (B c q c' q' : Term) : Term :=
  msFoldT (fun a e μ => ite (lt (countT B c' q' e) μ) (const 0) a) (const 1) B c q

/-- The weight of the label coded by `i` from bit `0`. -/
def labelWtT (B i : Term) : Term := add (wtT B i (const 0)) (wtT B i (msEndT B i (const 0)))

/-- The validity test of an index `i` of `W = w(a)` bits. -/
def validT (a W i : Term) : Term :=
  ite (lt (const 0) a)
    (mul (mul (lt (msEndT W i (msEndT W i (const 0))) (add W (const 1)))
        (lt i (pow2 (cminT (msEndT W i (msEndT W i (const 0))) W))))
      (lt (add (wtT W i (const 0)) (wtT W i (msEndT W i (const 0)))) (add a (const 1))))
    (eqT i (const 0))

/-- `⌊√n⌋`. -/
def sqrtT (n : Term) : Term :=
  sumT (add n (const 1)) fun k => lt (mul (add k (const 1)) (add k (const 1))) (add n (const 1))

/-- The code width `w(a)`. -/
def codeWidthT (a : Term) : Term :=
  ite (lt (const 0) a) (add (sqrtT (mul (const 784) a)) (const 2)) (const 0)

section Instances

variable {B c q c' q' y k d a W i : Term} {Bv cv qv cv' qv' yv kv dv av Wv iv : ℕ}

theorem val_wtT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (wtT B c q) (wtN Bv cv qv) :=
  val_msSumT (fun _ _ _ _ _ hy hz => val_mul (val_add hy (val_const 1)) hz) hB hc hq

theorem val_cardT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (cardT B c q) (cardN Bv cv qv) :=
  val_msSumT (fun _ _ _ _ _ _ hz => hz) hB hc hq

theorem val_countT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hy : Val w env y yv) : Val w env (countT B c q y) (countN Bv cv qv yv) :=
  val_msFoldT (G := fun a e μ => if e = yv then μ else a)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_eqT he (hy.ext pre)) hμ hx).congr
      (by split_ifs <;> simp_all)) (val_const 0) hB hc hq

theorem val_topT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (topT B c q) (topN Bv cv qv) :=
  val_msFoldT (G := fun a e _ => max a (e + 1))
    (fun _ _ _ _ _ _ _ hx he _ => val_cmaxT hx (val_add he (val_const 1))) (val_const 0) hB hc hq

theorem val_kthFoldT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) : Val w env (kthFoldT B c q k) (msFoldN (kthStep kv) kv Bv cv qv) :=
  val_msFoldT (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_lt (hk.ext pre) hx) hx
    (val_ite (val_lt hx hμ) (val_add (val_add (hk.ext pre) (val_const 1)) he)
        (val_sub hx hμ))).congr
      (by unfold kthStep; split_ifs <;> simp_all)) hk hB hc hq

theorem val_kthT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) (hd : Val w env d dv) : Val w env (kthT B c q k d)
        (kthN Bv cv qv kv dv) := by
  have h := val_kthFoldT hB hc hq hk
  refine (val_ite (val_lt hk h) (val_sub h (val_add hk (val_const 1))) hd).congr ?_
  unfold kthN; split_ifs <;> simp_all

theorem val_msLeT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    Val w env (msLeT B c q c' q') (leN Bv cv qv cv' qv') :=
  val_msFoldT (G := fun a e μ => if μ ≤ countN Bv cv' qv' e then a else 0)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_lt (val_countT (hB.ext pre) (hc'.ext pre)
      (hq'.ext pre) he) hμ) (val_const 0) hx).congr (by split_ifs <;> simp_all))
    (val_const 1) hB hc hq

theorem val_labelWtT (hB : Val w env B Bv) (hi : Val w env i iv) :
    Val w env (labelWtT B i) (labelWtN Bv iv) :=
  val_add (val_wtT hB hi (val_const 0)) (val_wtT hB hi (val_msEndT hB hi (val_const 0)))

theorem val_validT (ha : Val w env a av) (hW : Val w env W Wv) (hi : Val w env i iv) :
    Val w env (validT a W i) (validN av Wv iv) := by
  have e1 := val_msEndT hW hi (val_const 0)
  have e2 := val_msEndT hW hi e1
  refine (val_ite (val_lt (val_const 0) ha) (val_mul (val_mul (val_lt e2 (val_add hW (val_const 1)))
    (val_lt hi (val_pow2 (val_cminT e2 hW)))) (val_lt (val_add (val_wtT hW hi (val_const 0))
      (val_wtT hW hi e1)) (val_add ha (val_const 1)))) (val_eqT hi (val_const 0))).congr ?_
  unfold validN
  by_cases h0 : av = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, show 0 < av by omega]
    by_cases hE : msEnd Wv iv (msEnd Wv iv 0) ≤ Wv
    · rw [Nat.min_eq_left hE]; split_ifs <;> simp_all
    · have : ¬ msEnd Wv iv (msEnd Wv iv 0) < Wv + 1 := by omega
      simp [this, hE]

theorem val_sqrtT {n : Term} {nv : ℕ} (hn : Val w env n nv) : Val w env (sqrtT n) (sqrtN nv) :=
  val_sumT (val_add hn (val_const 1)) fun pre x k _ =>
    (val_lt (val_mul (val_add (val_idx _ x k) (val_const 1))
        (val_add (val_idx _ x k) (val_const 1)))
      (val_add (hn.at2 pre x k) (val_const 1))).congr (by split_ifs <;> omega)

theorem val_codeWidthT (ha : Val w env a av) : Val w env (codeWidthT a) (codeWidth av) := by
  refine (val_ite (val_lt (val_const 0) ha) (val_add (val_sqrtT (val_mul (val_const 784) ha))
    (val_const 2)) (val_const 0)).congr ?_
  rw [← codeWidthN_eq, codeWidthN]; split_ifs <;> simp_all

end Instances

/-! ### Writing codes -/

/-- `topBit K x`. -/
def topBitT (K x : Term) : Term := foldT K (const 0) fun a j => ite (bit x j) j a

/-- `gammaNum K x`. -/
def gammaNumT (K x : Term) : Term :=
  mul (pow2 (topBitT K x)) (readBitsT x (const 0) (add (topBitT K x) (const 1)))

/-- The accumulator after appending the gamma code of `x` at bit `q` (`appendN`). -/
def appendAccT (W acc q x : Term) : Term :=
  ite (lt (add (add q (mul (const 2) (topBitT W x))) (const 1)) (add W (const 1)))
    (add acc (mul (pow2 (cminT q W)) (gammaNumT W x))) acc

/-- The position after appending the gamma code of `x` at bit `q` (`appendN`). -/
def appendPosT (W q x : Term) : Term :=
  cminT (add (add q (mul (const 2) (topBitT W x))) (const 1)) (add W (const 1))

section Write

variable {K x W acc q : Term} {Kv xv Wv accv qv : ℕ}

theorem val_topBitT (hK : Val w env K Kv) (hx : Val w env x xv) :
    Val w env (topBitT K x) (topBit Kv xv) := by
  refine val_foldT hK (val_const 0) fun pre a j _ => ?_
  refine (val_ite (val_bit (hx.at2 pre a j) (val_idx _ a j)) (val_idx _ a j)
      (val_acc _ a j)).congr ?_
  cases xv.testBit j <;> simp

theorem val_gammaNumT (hK : Val w env K Kv) (hx : Val w env x xv) :
    Val w env (gammaNumT K x) (gammaNum Kv xv) :=
  val_mul (val_pow2 (val_topBitT hK hx))
    (val_readBitsT hx (val_const 0) (val_add (val_topBitT hK hx) (val_const 1)))

theorem val_appendAccT (hW : Val w env W Wv) (ha : Val w env acc accv) (hq : Val w env q qv)
    (hx : Val w env x xv) : Val w env (appendAccT W acc q x) (appendN Wv accv qv xv).1 := by
  refine (val_ite (val_lt (val_add (val_add hq (val_mul (val_const 2) (val_topBitT hW hx)))
    (val_const 1)) (val_add hW (val_const 1))) (val_add ha (val_mul (val_pow2 (val_cminT hq hW))
      (val_gammaNumT hW hx))) ha).congr ?_
  unfold appendN
  by_cases h : qv + 2 * topBit Wv xv + 1 ≤ Wv
  · have h' : qv + 2 * topBit Wv xv + 1 < Wv + 1 := by omega
    simp [h, h', Nat.min_eq_left (show qv ≤ Wv by omega)]
  · have h' : ¬ qv + 2 * topBit Wv xv + 1 < Wv + 1 := by omega
    simp [h, h']

theorem val_appendPosT (hW : Val w env W Wv) (hq : Val w env q qv) (hx : Val w env x xv) :
    Val w env (appendPosT W q x) (appendN Wv 0 qv xv).2 :=
  val_cminT (val_add (val_add hq (val_mul (val_const 2) (val_topBitT hW hx))) (val_const 1))
    (val_add hW (val_const 1))

end Write

/-! ### The code of a multiset with given multiplicities -/

/-- The packed state `(code, length, previous weight)` of `msOfCount`, in base `2^(W+1)`. -/
def ocP (W : ℕ) (s : ℕ × ℕ × ℕ) : ℕ := s.1 + 2 ^ (W + 1) * (s.2.1 + 2 ^ (W + 1) * s.2.2)

/-- The states of `msOfCount`: the code fits its length and the width. -/
def OcInv (W : ℕ) (s : ℕ × ℕ × ℕ) : Prop := s.1 < 2 ^ min s.2.1 W ∧ s.2.1 ≤ W + 1

theorem appendN_snd_acc (W acc : ℕ) (q x : ℕ) : (appendN W acc q x).2 = (appendN W 0 q x).2 := rfl

theorem ocInv_step {W : ℕ} {cnt : ℕ → ℕ} {s : ℕ × ℕ × ℕ} (h : OcInv W s) (k : ℕ) :
    OcInv W (ocStep W cnt s k) := by
  unfold ocStep
  split_ifs
  · exact ⟨appendN_lt (appendN_lt h.1),
      appendN_snd_le W (appendN W s.1 s.2.1 (k + 1 - s.2.2)).1 _ _⟩
  · exact h

theorem ocInv_foldl {W : ℕ} {cnt : ℕ → ℕ} : ∀ (ks : List ℕ) (s : ℕ × ℕ × ℕ), OcInv W s →
    OcInv W (ks.foldl (ocStep W cnt) s)
  | [], _, h => h
  | k :: ks, _, h => ocInv_foldl ks _ (ocInv_step h k)

theorem ocP_unpack {W : ℕ} {s : ℕ × ℕ × ℕ} (h : OcInv W s) :
    ocP W s % 2 ^ (W + 1) = s.1 ∧ ocP W s / 2 ^ (W + 1) % 2 ^ (W + 1) = s.2.1 ∧
      ocP W s / 2 ^ (W + 1) / 2 ^ (W + 1) = s.2.2 := by
  have h1 : s.1 < 2 ^ (W + 1) :=
    h.1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : s.2.1 < 2 ^ (W + 1) := lt_of_le_of_lt h.2 (Nat.lt_two_pow_self)
  unfold ocP
  rw [unpack_mod h1, unpack_div h1, unpack_mod h2, unpack_div h2]
  exact ⟨rfl, rfl, rfl⟩

/-- The step of `msOfCount` on packed states. -/
def ocStepN (W : ℕ) (cnt : ℕ → ℕ) (sP k : ℕ) : ℕ :=
  if 0 < cnt k then
    (appendN W (appendN W (sP % 2 ^ (W + 1)) (sP / 2 ^ (W + 1) % 2 ^ (W + 1))
        (k + 1 - sP / 2 ^ (W + 1) / 2 ^ (W + 1))).1
      (appendN W 0 (sP / 2 ^ (W + 1) % 2 ^ (W + 1)) (k + 1 - sP / 2 ^ (W + 1) / 2 ^ (W + 1))).2
      (cnt k)).1 +
    2 ^ (W + 1) * ((appendN W 0 (appendN W 0 (sP / 2 ^ (W + 1) % 2 ^ (W + 1))
        (k + 1 - sP / 2 ^ (W + 1) / 2 ^ (W + 1))).2 (cnt k)).2 + 2 ^ (W + 1) * (k + 1))
  else sP

theorem ocStepN_ocP {W : ℕ} {cnt : ℕ → ℕ} {s : ℕ × ℕ × ℕ} (h : OcInv W s) (k : ℕ) :
    ocStepN W cnt (ocP W s) k = ocP W (ocStep W cnt s k) := by
  obtain ⟨u1, u2, u3⟩ := ocP_unpack h
  unfold ocStepN ocStep
  rw [u1, u2, u3]
  split_ifs
  · simp only [ocP, appendN_snd_acc W (appendN W s.1 s.2.1 (k + 1 - s.2.2)).1,
      appendN_snd_acc W s.1]
  · rfl

theorem foldl_ocStepN {W : ℕ} {cnt : ℕ → ℕ} : ∀ (ks : List ℕ) (s : ℕ × ℕ × ℕ), OcInv W s →
    ks.foldl (ocStepN W cnt) (ocP W s) = ocP W (ks.foldl (ocStep W cnt) s)
  | [], _, _ => rfl
  | k :: ks, s, h => by
    rw [List.foldl_cons, List.foldl_cons, ocStepN_ocP h, foldl_ocStepN ks _ (ocInv_step h k)]

/-- The field base `2^(W+1)` of `msOfCount`. -/
def ocNT (W : Term) : Term := pow2 (add W (const 1))

/-- One step of `msOfCount` on packed states. -/
def ocStepT (W : Term) (cnt : Term → Term) (s k : Term) : Term :=
  ite (lt (const 0) (cnt k))
    (add (appendAccT W (appendAccT W (mod s (ocNT W)) (mod (div s (ocNT W)) (ocNT W))
          (sub (add k (const 1)) (div (div s (ocNT W)) (ocNT W))))
        (appendPosT W (mod (div s (ocNT W)) (ocNT W))
            (sub (add k (const 1)) (div (div s (ocNT W)) (ocNT W))))
        (cnt k))
      (mul (ocNT W) (add (appendPosT W (appendPosT W (mod (div s (ocNT W)) (ocNT W))
          (sub (add k (const 1)) (div (div s (ocNT W)) (ocNT W)))) (cnt k))
        (mul (ocNT W) (add k (const 1))))))
    s

/-- The number of `k < X` with `cnt k > 0`. -/
def ocNumT (X : Term) (cnt : Term → Term) : Term := sumT X fun k => lt (const 0) (cnt k)

/-- The packed state after the header. -/
def ocStartT (W X : Term) (cnt : Term → Term) : Term :=
  add (appendAccT W (const 0) (const 0) (add (ocNumT X cnt) (const 1)))
    (mul (ocNT W) (appendPosT W (const 0) (add (ocNumT X cnt) (const 1))))

/-- The packed final state of `msOfCount`. -/
def ocFoldT (W X : Term) (cnt : Term → Term) : Term :=
  foldT X (ocStartT W X cnt) fun s k => ocStepT W cnt s k

/-- **The code of the multiset** with multiplicities `cnt k` for `k < X`, within `W` bits. -/
def ocCodeT (W X : Term) (cnt : Term → Term) : Term := mod (ocFoldT W X cnt) (ocNT W)

/-- The length of that code. -/
def ocLenT (W X : Term) (cnt : Term → Term) : Term :=
  mod (div (ocFoldT W X cnt) (ocNT W)) (ocNT W)

variable (w) in
/-- `cnt` computes `C` on stable arguments, in every extension of `env`. -/
def ValF1 (cnt : Term → Term) (C : ℕ → ℕ) (env : List ℕ) : Prop :=
  ∀ (pre : List ℕ) (y : Term) (Y : ℕ), Val w (pre ++ env) y Y → Val w (pre ++ env) (cnt y) (C Y)

section OfCount

variable {W X : Term} {cnt : Term → Term} {Wv Xv : ℕ} {C : ℕ → ℕ}

theorem val_ocNumT (hX : Val w env X Xv) (hC : ValF1 w cnt C env) :
    Val w env (ocNumT X cnt) (ocNum Xv C) :=
  val_sumT hX fun pre x k
      _ => (val_lt (val_const 0) (hC (x :: k :: pre) _ _ (val_idx _ x k))).congr rfl

theorem val_ocStepT {s k : Term} {sv kv : ℕ} (hW : Val w env W Wv) (hC : ValF1 w cnt C env)
    (hs : Val w env s sv) (hk : Val w env k kv) :
    Val w env (ocStepT W cnt s k) (ocStepN Wv C sv kv) := by
  have hN : Val w env (ocNT W) (2 ^ (Wv + 1)) := val_pow2 (val_add hW (val_const 1))
  have hc := hC [] _ _ hk
  simp only [List.nil_append] at hc
  have hcode := val_mod hs hN
  have hlen := val_mod (val_div hs hN) hN
  have hgap := val_sub (val_add hk (val_const 1)) (val_div (val_div hs hN) hN)
  refine (val_ite (val_lt (val_const 0) hc)
    (val_add (val_appendAccT hW (val_appendAccT hW hcode hlen hgap)
        (val_appendPosT hW hlen hgap) hc)
      (val_mul hN (val_add (val_appendPosT hW (val_appendPosT hW hlen hgap) hc)
        (val_mul hN (val_add hk (val_const 1)))))) hs).congr ?_
  unfold ocStepN
  split_ifs <;> first | rfl | (exfalso; omega)

theorem val_ocFold_gen {n : Term} {nv : ℕ} (hW : Val w env W Wv) (hX : Val w env X Xv)
    (hC : ValF1 w cnt C env) (hn : Val w env n nv) :
    Val w env (foldT n (ocStartT W X cnt) fun s k => ocStepT W cnt s k)
      (ocP Wv ((List.range nv).foldl (ocStep Wv C)
        ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0))) := by
  have hN : Val w env (ocNT W) (2 ^ (Wv + 1)) := val_pow2 (val_add hW (val_const 1))
  have hm := val_add (val_ocNumT hX hC) (val_const 1)
  have hst := val_add (val_appendAccT hW (val_const 0) (val_const 0) hm)
    (val_mul hN (val_appendPosT hW (val_const 0) hm))
  have := val_foldT (f := fun s k => ocStepT W cnt s k) (step := ocStepN Wv C) hn hst
    fun pre x k _ => val_ocStepT (hW.at2 pre x k) (fun pre' y Y hy => by
      have := hC (pre' ++ x :: k :: pre) y Y (by simpa using hy); simpa using this)
      (val_acc _ x k) (val_idx _ x k)
  have hinv : OcInv Wv ((appendN Wv 0 0 (ocNum Xv C + 1)).1,
      (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0) :=
    ⟨appendN_lt (by simp), appendN_snd_le _ 0 0 _⟩
  have e : (appendN Wv 0 0 (ocNum Xv C + 1)).1 + 2 ^ (Wv + 1) *
      (appendN Wv 0 0 (ocNum Xv C + 1)).2 =
      ocP Wv ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0) := by
    simp [ocP]
  rw [e, foldl_ocStepN _ _ hinv] at this
  exact this

theorem val_ocFoldT (hW : Val w env W Wv) (hX : Val w env X Xv) (hC : ValF1 w cnt C env) :
    Val w env (ocFoldT W X cnt) (ocP Wv ((List.range Xv).foldl (ocStep Wv C)
      ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0))) :=
  val_ocFold_gen hW hX hC hX

theorem val_ocCodeT (hW : Val w env W Wv) (hX : Val w env X Xv) (hC : ValF1 w cnt C env) :
    Val w env (ocCodeT W X cnt) (msOfCount Wv Xv C).1 := by
  refine (val_mod (val_ocFoldT hW hX hC) (val_pow2 (val_add hW (val_const 1)))).congr ?_
  exact (ocP_unpack (ocInv_foldl _ _ ⟨appendN_lt (by simp), appendN_snd_le _ 0 0 _⟩)).1

theorem val_ocLenT (hW : Val w env W Wv) (hX : Val w env X Xv) (hC : ValF1 w cnt C env) :
    Val w env (ocLenT W X cnt) (msOfCount Wv Xv C).2 := by
  have hN := val_pow2 (val_add hW (val_const 1))
  refine (val_mod (val_div (val_ocFoldT hW hX hC) hN) hN).congr ?_
  exact (ocP_unpack (ocInv_foldl _ _ ⟨appendN_lt (by simp), appendN_snd_le _ 0 0 _⟩)).2.1

end OfCount

/-- The multiplicities of `σ + τ`. -/
def addCntT (B c q c' q' : Term) (k : Term) : Term := add (countT B c q k) (countT B c' q' k)

/-- The multiplicities of `σ - τ`. -/
def subCntT (B c q c' q' : Term) (k : Term) : Term := sub (countT B c q k) (countT B c' q' k)

/-- The code of `σ + τ`, from the codes of `σ` (bit `q` of `c`) and `τ` (bit `q'` of `c'`). -/
def addCodeT (B W c q c' q' : Term) : Term :=
  ocCodeT W (cmaxT (topT B c q) (topT B c' q')) (addCntT B c q c' q')

/-- The length of the code of `σ + τ`. -/
def addLenT (B W c q c' q' : Term) : Term :=
  ocLenT W (cmaxT (topT B c q) (topT B c' q')) (addCntT B c q c' q')

/-- The code of `σ - τ`. -/
def subCodeT (B W c q c' q' : Term) : Term := ocCodeT W (topT B c q) (subCntT B c q c' q')

/-- The length of the code of `σ - τ`. -/
def subLenT (B W c q c' q' : Term) : Term := ocLenT W (topT B c q) (subCntT B c q c' q')

section AddSub

variable {B W c q c' q' : Term} {Bv Wv cv qv cv' qv' : ℕ}

theorem valF1_addCntT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    ValF1 w (addCntT B c q c' q') (fun k => countN Bv cv qv k + countN Bv cv' qv' k) env :=
  fun pre _ _ hy => val_add (val_countT (hB.ext pre) (hc.ext pre) (hq.ext pre) hy)
    (val_countT (hB.ext pre) (hc'.ext pre) (hq'.ext pre) hy)

theorem valF1_subCntT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    ValF1 w (subCntT B c q c' q') (fun k => countN Bv cv qv k - countN Bv cv' qv' k) env :=
  fun pre _ _ hy => val_sub (val_countT (hB.ext pre) (hc.ext pre) (hq.ext pre) hy)
    (val_countT (hB.ext pre) (hc'.ext pre) (hq'.ext pre) hy)

theorem val_addCodeT (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    Val w env (addCodeT B W c q c' q') (addN Bv Wv cv qv cv' qv').1 :=
  val_ocCodeT hW (val_cmaxT (val_topT hB hc hq) (val_topT hB hc' hq'))
    (valF1_addCntT hB hc hq hc' hq')

theorem val_addLenT (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    Val w env (addLenT B W c q c' q') (addN Bv Wv cv qv cv' qv').2 :=
  val_ocLenT hW (val_cmaxT (val_topT hB hc hq) (val_topT hB hc' hq'))
    (valF1_addCntT hB hc hq hc' hq')

theorem val_subCodeT (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    Val w env (subCodeT B W c q c' q') (subN Bv Wv cv qv cv' qv').1 :=
  val_ocCodeT hW (val_topT hB hc hq) (valF1_subCntT hB hc hq hc' hq')

theorem val_subLenT (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') :
    Val w env (subLenT B W c q c' q') (subN Bv Wv cv qv cv' qv').2 :=
  val_ocLenT hW (val_topT hB hc hq) (valF1_subCntT hB hc hq hc' hq')

end AddSub

/-! ### Tiers: helpers -/

section TierHelpers

variable {L : ℕ}

/-- Retier a term by its known value. -/
theorem tm_val {t : Term} {d d' v : ℕ} (h : Tm w L d' t env) (hv : Val w env t v)
    (hlt : v < 2 ^ (d * L)) : Tm w L d t env := tm_retier h hv.1 (hv.2 ▸ hlt)

theorem lt_two_pow_of_le {n : ℕ} (h : n ≤ L) : n < 2 ^ L := lt_of_le_of_lt h Nat.lt_two_pow_self

theorem lt_tier_one {n : ℕ} (h : n ≤ L) : n < 2 ^
    (1 * L) := by rw [one_mul]; exact lt_two_pow_of_le h

theorem sum_lt_tier {a b d : ℕ} (ha : a < 2 ^ (d * L)) (hb : b < 2 ^ (d * L)) (hL : 1 ≤ L) :
    a + b < 2 ^ ((d + 1) * L) := by
  have : 2 ^ (d * L) * 2 ≤ 2 ^ ((d + 1) * L) := by
    rw [Nat.add_mul, one_mul, pow_add]
    exact Nat.mul_le_mul_left _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL)
  omega

theorem two_mul_add_one_lt_pow (hL : 4 ≤ L) : 2 * L + 1 < 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem t_one (hL : 1 ≤ L) : Tm w L 1 (const 1) env := t_const (Nat.one_lt_two_pow (by omega))

theorem t_small {k : ℕ} (hk : k ≤ 3) (hL : 2 ≤ L) : Tm w L 1 (const k) env :=
  t_const (lit_lt_two_pow hk hL)

theorem t_eqT' {a b : Term} {da db : ℕ} (ha : Tm w L da a env) (hb : Tm w L db b env)
    (hL : 1 ≤ L) : Tm w L 1 (eqT a b) env :=
  t_sub (t_one hL) (t_add (t_lt ha hb hL) (t_lt hb ha hL) hL (by norm_num))

theorem tm_cminT {a b : Term} {d : ℕ} (ha : Tm w L d a env) (hb : Tm w L d b env) (hL : 1 ≤ L) :
    Tm w L d (cminT a b) env := tm_ite (t_lt ha hb hL) ha hb

theorem tm_cmaxT {a b : Term} {d : ℕ} (ha : Tm w L d a env) (hb : Tm w L d b env) (hL : 1 ≤ L) :
    Tm w L d (cmaxT a b) env := tm_ite (t_lt ha hb hL) hb ha

theorem tm_acc {E : List ℕ} {x k d : ℕ} (h : x < 2 ^ (d * L)) :
    Tm w L d (lvl (E.length + 1)) (x :: k :: E) :=
  tm_lvl (by simp) (by rw [denote_lvl_acc]; exact h)

theorem tm_idx {E : List ℕ} {x k d : ℕ} (h : k < 2 ^ (d * L)) :
    Tm w L d (lvl E.length) (x :: k :: E) := tm_second h

theorem denote_foldT_count {n m i : Term} {f : Term → Term → Term} {E : List ℕ}
    (h : n.denote w E = m.denote w E) : (foldT n i f).denote w E = (foldT m i f).denote w E := by
  simp only [denote_foldT, h]

/-- **A fold with stable data**: the accumulator stays below `2^(da·L)` (`hpart`, stated through
the same fold with constant counts), and the body is bounded at every reachable state. -/
theorem tm_foldT_st {n i : Term} {f : Term → Term → Term} {N dn di da : ℕ}
    (hn : Val w env n N) (tn : Tm w L dn n env) (hdn : dn ≤ 32) (ti : Tm w L di i env)
    (hda : da ≤ 32)
    (hpart : ∀ pre, Small L pre → ∀ k ≤ N, (foldT (const k) i f).denote w (pre ++ env) < 2 ^
        (da * L))
    (tf : ∀ (pre : List ℕ) (x k : ℕ), Small L pre → k < N → x < 2 ^ (da * L) →
      Ext L (x :: k :: (pre ++ env)) env →
      Tm w L 128 (f (lvl ((pre ++ env).length + 1)) (lvl (pre ++ env).length))
          (x :: k :: (pre ++ env))) :
    Tm w L da (foldT n i f) env := by
  intro pre hp
  have hN : n.denote w (pre ++ env) = N := (hn.ext pre).2
  have vn := (tn pre hp).2
  rw [hN] at vn
  refine ⟨(bnd_foldT w _ n i f (pre ++ env)).mpr
      ⟨(tn pre hp).1, (ti pre hp).1, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [hN]; exact vn.le.trans (pow_le_pow_tier (by omega))
  · rw [hN] at hk
    have hx := hpart pre hp k hk.le
    simp only [denote_foldT, denote_const] at hx
    have he : Ext L (foldAcc w f (pre ++ env) (i.denote w (pre ++ env)) k :: k ::
        (pre ++ env)) env :=
      ⟨_ :: k :: pre, Small.cons (hx.trans_le (pow_le_pow_tier hda))
        (Small.cons ((hk.trans vn).trans_le (pow_le_pow_tier hdn)) hp), rfl⟩
    exact (tf pre _ k hp hk hx he).bnd
  · have := hpart pre hp N le_rfl
    rwa [denote_foldT_count (m := const N) (by rw [hN]; rfl)]

end TierHelpers

/-! ### Tiers: reading -/

section TierRead

variable {L : ℕ} {B c q : Term} {Bv cv qv : ℕ} {dc dq : ℕ}

theorem tm_zeroRunT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq : dq ≤ 120)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (zeroRunT B c q) env := by
  refine tm_foldT_st hB tB (by norm_num) (t_small (k := 0) (by norm_num) (by omega)) (by norm_num)
    (fun pre _ k hk => ?_) (fun pre x k _ hk hx he => ?_)
  · have := ((val_zeroRunT (val_const k) hc hq).ext pre).2
    exact lt_of_eq_of_lt this (lt_tier_one ((zeroRun_le _ _ _).trans (hk.trans hBL)))
  · have tz : Tm w L 1 (lvl ((pre ++ env).length + 1)) (x :: k :: (pre ++ env)) := tm_acc hx
    have ti : Tm w L 1 (lvl (pre ++ env).length) (x :: k :: (pre ++ env)) :=
      tm_idx (lt_tier_one (by omega))
    exact t_add tz (t_mul (t_eqT' tz ti (by omega)) (t_sub (t_one (by omega))
      (t_bit (tc.ext he) (t_add (tq.ext he) ti (by omega) (by omega)) (by omega))) (by norm_num))
      (by omega) (by norm_num) |>.mono (by norm_num)

theorem tm_readBitsT {n : Term} {nv dn dr : ℕ} (hc : Val w env c cv) (hq : Val w env q qv)
    (hn : Val w env n nv) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (tn : Tm w L dn n env)
    (hdn : dn ≤ 32) (hdq : dq ≤ 120) (hdr : 1 ≤ dr) (hdr' : dr ≤ 32) (hL : 4 ≤ L)
    (hnv : nv ≤ dr * L) : Tm w L dr (readBitsT c q n) env := by
  have vn := tn.lt; rw [hn.2] at vn
  refine tm_foldT_st hn tn hdn (t_small (k := 0) (by norm_num) (by omega)) hdr'
    (fun pre _ k hk => ?_) (fun pre x k _ hk hx he => ?_)
  · have := ((val_readBitsT hc hq (val_const k)).ext pre).2
    exact lt_of_eq_of_lt this ((readBits_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · have tz : Tm w L dr (lvl ((pre ++ env).length + 1)) (x :: k :: (pre ++ env)) := tm_acc hx
    have ti : Tm w L dn (lvl (pre ++ env).length) (x :: k :: (pre ++ env)) := tm_idx (hk.trans vn)
    exact t_add (t_mul (t_small (k := 2) (by norm_num) (by omega)) tz (by omega))
      (t_bit (tc.ext he) (t_add (tq.ext he) ti (by omega) (by omega)) (by omega)) (by omega)
      (by omega) |>.mono (by omega)

theorem tm_gammaValT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq : dq ≤ 100)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 2 (gammaValT B c q) env := by
  have tz := tm_zeroRunT hB hc hq tB tc tq (by omega) hL hBL
  have vz := val_zeroRunT hB hc hq
  exact tm_readBitsT hc (val_add hq vz) (val_add vz (val_const 1)) tc
    (t_add tq tz (by omega) (by omega)) (t_add tz (t_one (by omega)) (by omega) (by norm_num))
    (by norm_num) (by omega) (by norm_num) (by norm_num) hL
    (by have := zeroRun_le Bv cv qv; omega)

theorem tm_gammaEndT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 100) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L (dq + 1) (gammaEndT B c q) env := by
  have tz := tm_zeroRunT hB hc hq tB tc tq (by omega) hL hBL
  refine tm_val (t_add (t_add tq (t_mul (t_small (k := 2) (by norm_num) (by omega))
      tz (by norm_num))
    (by omega) (by omega)) (t_one (by omega)) (by omega) (by omega)) (val_gammaEndT hB hc hq) ?_
  have vq := tq.lt; rw [hq.2] at vq
  have hz := zeroRun_le Bv cv qv
  have h2 := two_mul_add_one_lt_pow hL
  rw [gammaN_snd, Nat.add_assoc]
  exact sum_lt_tier vq ((show 2 * zeroRun Bv cv qv + 1 < 2 ^ L by omega).trans_le
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left L (by omega)))) (by omega)

theorem tm_mT (hB : Val w env B Bv) (tB : Tm w L 1 B env) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 3 (mT B) env :=
  t_pow2 (t_add (t_mul (t_small (k := 2) (by norm_num) (by omega)) tB (by norm_num))
    (t_small (k := 2) (by norm_num) (by omega)) (by omega) (by norm_num)) (by norm_num)
    (fun pre _ => by
      rw [((val_add (val_mul (val_const 2) hB) (val_const 2)).ext pre).2]; omega) (by norm_num)
    (by omega)

end TierRead

/-! ### Tiers: the parse -/

theorem ctrlP_lt (B c q k : ℕ) : ctrlP B c q k < 2 ^ (4 * B + 4) := by
  obtain ⟨-, b1, b2⟩ := ctrl_bounds B c q k
  have : 2 ^ (4 * B + 4) = 2 ^ (2 * B + 2) * 2 ^ (2 * B + 2) := by rw [← pow_add]; ring_nf
  rw [this, ctrlP]
  nlinarith

theorem entE_lt (B c q k : ℕ) : entE B c q k < 2 ^ (2 * B + 3) := by
  obtain ⟨-, -, b2⟩ := ctrl_bounds B c q k
  have := gammaN_fst_lt B c (ctrl B c q k).1
  have h1 : 2 ^ (B + 1) ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * B + 3) = 2 * 2 ^ (2 * B + 2) := by rw [← pow_succ']
  simp only [entE, entryAt]
  omega

theorem entM_lt (B c q k : ℕ) : entM B c q k < 2 ^ (B + 1) := gammaN_fst_lt _ _ _

section TierParse

variable {L : ℕ} {B c q k : Term} {Bv cv qv kv : ℕ} {dc dq dk : ℕ}

theorem tm_ctrlStepT {s : Term} {sv : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hs : Val w env s sv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env)
    (tq : Tm w L dq q env) (ts : Tm w L 6 s env) (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 120 (ctrlStepT B c q s) env := by
  have tM := tm_mT hB tB hL hBL
  have vM := val_mT hB
  have tmod : Tm w L 3 (mod s (mT B)) env := t_mod ts tM Pos.pow2'
  have vp := val_add hq (val_mod hs vM)
  have tp : Tm w L (max dq 3 + 1) (add q (mod s (mT B))) env := t_add tq tmod (by omega) (by omega)
  have te1 := tm_gammaEndT hB hc vp tB tc tp (by omega) (by omega) hL hBL
  have te2 := tm_gammaEndT hB hc (val_gammaEndT hB hc vp) tB tc te1 (by omega) (by omega) hL hBL
  have tv := tm_gammaValT hB hc vp tB tc tp (by omega) hL hBL
  exact (t_add (t_sub te2 tq) (t_mul tM (t_add (t_div ts tM) tv (by omega) (by norm_num))
    (by norm_num)) (by omega) (by omega)).mono (by omega)

theorem tm_ctrlT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env)
    (tk : Tm w L dk k env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hL : 4 ≤ L)
    (hBL : Bv ≤ L) : Tm w L 6 (ctrlT B c q k) env := by
  have vn := val_cminT hk hB
  have tn : Tm w L 1 (cminT k B) env :=
    tm_val (tm_cminT (tk.mono (le_max_left dk 1)) (tB.mono (le_max_right dk 1)) (by omega)) vn
      (lt_tier_one ((min_le_right _ _).trans hBL))
  have ti := t_sub (tm_gammaEndT hB hc hq tB tc tq hdq1 (by omega) hL hBL) tq
  refine tm_foldT_st vn tn (by norm_num) ti (by norm_num) (fun pre _ j hj => ?_)
    (fun pre x j _ _ hx he => ?_)
  · have hv := ((val_ctrlT hB hc hq (val_const j)).ext pre).2
    rw [denote_foldT_count (m := cminT (const j) B) (by
      rw [((val_cminT (val_const j) hB).ext pre).2, denote_const]; omega)]
    refine lt_of_eq_of_lt hv ((ctrlP_lt _ _ _ _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_))
    omega
  · exact tm_ctrlStepT (hB.at2 pre x j) (hc.at2 pre x j) (hq.at2 pre x j) (val_acc _ x j)
      (tB.ext he) (tc.ext he) (tq.ext he) (tm_acc hx) hdq hL hBL |>.mono (by norm_num)

theorem tm_msNT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq : dq ≤ 100)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (msNT B c q) env :=
  tm_val (tm_cminT ((t_sub (tm_gammaValT hB hc hq tB tc tq hdq hL hBL) (t_one (by omega)))) (tB.mono
    (by norm_num)) (by omega)) (val_msNT hB hc hq) (lt_tier_one ((msN_le _ _ _).trans hBL))

theorem tm_entET (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env)
    (tk : Tm w L dk k env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hL : 4 ≤ L)
    (hBL : Bv ≤ L) : Tm w L 3 (entET B c q k) env := by
  have ts := tm_ctrlT hB hc hq hk tB tc tq tk hdq1 hdq hL hBL
  have vs := val_ctrlT hB hc hq hk
  have tM := tm_mT hB tB hL hBL
  have tp : Tm w L (max dq 3 + 1) (add q (mod (ctrlT B c q k) (mT B))) env :=
    t_add tq (t_mod ts tM Pos.pow2') (by omega) (by omega)
  refine tm_val (t_sub (t_add (t_div ts tM)
      (tm_gammaValT hB hc (val_add hq (val_mod vs (val_mT hB)))
    tB tc tp (by omega) hL hBL) (by omega) (by norm_num)) (t_one (by omega)))
    (val_entET hB hc hq hk) ((entE_lt _ _ _ _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_))
  omega

theorem tm_entMT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env)
    (tk : Tm w L dk k env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hL : 4 ≤ L)
    (hBL : Bv ≤ L) : Tm w L 2 (entMT B c q k) env := by
  have ts := tm_ctrlT hB hc hq hk tB tc tq tk hdq1 hdq hL hBL
  have vs := val_ctrlT hB hc hq hk
  have tM := tm_mT hB tB hL hBL
  have vp := val_add hq (val_mod vs (val_mT hB))
  have tp : Tm w L (max dq 3 + 1) (add q (mod (ctrlT B c q k) (mT B))) env :=
    t_add tq (t_mod ts tM Pos.pow2') (by omega) (by omega)
  exact tm_gammaValT hB hc (val_gammaEndT hB hc vp) tB tc
    (tm_gammaEndT hB hc vp tB tc tp (by omega) (by omega) hL hBL) (by omega) hL hBL

theorem tm_msEndT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L (max dq 3 + 1) (msEndT B c q) env :=
  t_add tq (t_mod (tm_ctrlT hB hc hq (val_msNT hB hc hq) tB tc tq
    (tm_msNT hB hc hq tB tc tq (by omega) hL hBL) hdq1 hdq hL hBL)
    (tm_mT hB tB hL hBL) Pos.pow2') (by omega) (by omega)

end TierParse

/-! ### Tiers: folds over the entries and their instances -/

variable (w L) in
/-- A user step on stable arguments: an accumulator of tier `da`, an element of tier `3`, a
multiplicity of tier `2`; only boundedness of the result is asked (tier `128`). -/
def TmV3 (g : Term → Term → Term → Term) (da : ℕ) (env : List ℕ) : Prop :=
  ∀ E, Ext L E env → ∀ (x y z : Term) (X Y Z : ℕ), Val w E x X → Val w E y Y → Val w E z Z →
    Tm w L da x E → Tm w L 3 y E → Tm w L 2 z E → Tm w L 128 (g x y z) E

variable (w L) in
/-- A summand on stable arguments: an element of tier `3`, a multiplicity of tier `2`; only
boundedness of the result is asked (tier `100`). -/
def TmV2 (f : Term → Term → Term) (env : List ℕ) : Prop :=
  ∀ E, Ext L E env → ∀ (y z : Term) (Y Z : ℕ), Val w E y Y → Val w E z Z →
    Tm w L 3 y E → Tm w L 2 z E → Tm w L 100 (f y z) E

theorem entE_lt_L {L B c q k : ℕ} (hBL : B ≤ L) : entE B c q k < 2 ^ (2 * L + 3) :=
  (entE_lt B c q k).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem entM_lt_L {L B c q k : ℕ} (hBL : B ≤ L) : entM B c q k < 2 ^ (L + 1) :=
  (entM_lt B c q k).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

section TierFold

variable {L : ℕ} {B c q a : Term} {Bv cv qv av : ℕ} {dc dq : ℕ}

/-- **The tier of a fold over the entries**, given the tier `du` of its accumulator along the run.
-/
theorem tm_msFoldT {g : Term → Term → Term → Term} {G : ℕ → ℕ → ℕ → ℕ} {du : ℕ}
    (hg : ValF3 w g G env) (tg : TmV3 w L g du env) (hdu : du ≤ 32) (ha : Val w env a av)
    (ta : Tm w L du a env) (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L)
    (hinv : ∀ k ≤ msN Bv cv qv,
      (List.range k).foldl (fun a k => G a (entE Bv cv qv k) (entM Bv cv qv k)) av < 2 ^ (du * L)) :
    Tm w L du (msFoldT g a B c q) env := by
  refine tm_foldT_st (val_msNT hB hc hq) (tm_msNT hB hc hq tB tc tq (by omega) hL hBL) (by norm_num)
    ta hdu (fun pre _ k hk => ?_) (fun pre x k _ hk hx he => ?_)
  · rw [((val_msFoldT_gen hg (val_const k) ha hB hc hq).ext pre).2]; exact hinv k hk
  · have hkL : k < 2 ^ (1 * L) := lt_tier_one (by have := msN_le Bv cv qv; omega)
    exact tg _ he _ _ _ _ _ _ (val_acc _ x k)
      (val_entET (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))
      (val_entMT (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k)) (tm_acc hx)
      (tm_entET (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k) (tB.ext he)
        (tc.ext he) (tq.ext he) (tm_idx hkL) hdq1 hdq hL hBL)
      (tm_entMT (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k) (tB.ext he)
        (tc.ext he) (tq.ext he) (tm_idx hkL) hdq1 hdq hL hBL)

/-- A fold over the entries whose step keeps the tier `du`. -/
theorem tm_msFoldT_cl {g : Term → Term → Term → Term} {G : ℕ → ℕ → ℕ → ℕ} {du : ℕ}
    (hg : ValF3 w g G env) (tg : TmV3 w L g du env) (hdu : du ≤ 32)
    (hG : ∀ a e μ, a < 2 ^ (du * L) → e < 2 ^ (2 * L + 3) → μ < 2 ^ (L + 1) → G a e μ < 2 ^
        (du * L))
    (ha : Val w env a av) (ta : Tm w L du a env) (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env)
    (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    Tm w L du (msFoldT g a B c q) env := by
  refine tm_msFoldT hg tg hdu ha ta hB hc hq tB tc tq hdq1 hdq hL hBL fun k _ => ?_
  induction k with
  | zero => have := ta.lt; rw [ha.2] at this; exact this
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    exact hG _ _ _ (ih (by omega)) (entE_lt_L hBL) (entM_lt_L hBL)

/-- **The tier of a sum over the entries**, with summands below `2^(df·L)`. -/
theorem tm_msSumT {f : Term → Term → Term} {F : ℕ → ℕ → ℕ} {df : ℕ} (hf : ValF2 w f F env)
    (tf : TmV2 w L f env) (hdf : df + 1 ≤ 32)
    (hF : ∀ e μ, e < 2 ^ (2 * L + 3) → μ < 2 ^ (L + 1) → F e μ < 2 ^ (df * L))
    (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L (df + 1) (msSumT f B c q) env := by
  unfold msSumT sumT
  refine tm_foldT_st (val_msNT hB hc hq) (tm_msNT hB hc hq tB tc tq (by omega) hL hBL) (by norm_num)
    (t_small (k := 0) (by norm_num) (by omega)) hdf (fun pre _ k hk => ?_)
    (fun pre x k _ hk hx he => ?_)
  · have := ((val_msSumT_gen hf (val_const k) hB hc hq).ext pre).2
    refine lt_of_eq_of_lt this ?_
    have hle : ∑ j ∈ Finset.range k, F (entE Bv cv qv j) (entM Bv cv qv j) ≤ k * 2 ^ (df * L) := by
      calc _ ≤ ∑ _j ∈ Finset.range k, 2 ^ (df * L) :=
            Finset.sum_le_sum fun j _ => (hF _ _ (entE_lt_L hBL) (entM_lt_L hBL)).le
        _ = k * 2 ^ (df * L) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hk' : k < 2 ^ L := lt_two_pow_of_le (by have := msN_le Bv cv qv; omega)
    have : k * 2 ^ (df * L) < 2 ^ L * 2 ^ (df * L) :=
      Nat.mul_lt_mul_of_pos_right hk' (by positivity)
    rw [Nat.add_mul, one_mul, pow_add, mul_comm]
    omega
  · have hkL : k < 2 ^ (1 * L) := lt_tier_one (by have := msN_le Bv cv qv; omega)
    exact (t_add (tm_acc hx) (tf _ he _ _ _ _
      (val_entET (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))
      (val_entMT (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k))
      (tm_entET (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k) (tB.ext he)
        (tc.ext he) (tq.ext he) (tm_idx hkL) hdq1 hdq hL hBL)
      (tm_entMT (hB.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k) (val_idx _ x k) (tB.ext he)
        (tc.ext he) (tq.ext he) (tm_idx hkL) hdq1 hdq hL hBL)) (by omega) (by omega)).mono
            (by omega)

theorem tm_wtT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 5 (wtT B c q) env := by
  refine tm_msSumT (df := 4) (F := fun e μ => (e + 1) * μ)
    (fun _ _ _ _ _ hy hz => val_mul (val_add hy (val_const 1)) hz)
    (fun E _ y z _ _ _ _ ty tz => (t_mul (t_add ty (t_one (by omega)) (by omega) (by norm_num)) tz
      (by norm_num)).mono (by norm_num)) (by norm_num) (fun e μ he hμ => ?_)
    hB hc hq tB tc tq hdq1 hdq hL hBL
  calc (e + 1) * μ < 2 ^ (2 * L + 3) * 2 ^ (L + 1) :=
        Nat.mul_lt_mul_of_le_of_lt (by omega) hμ (by positivity)
    _ = 2 ^ (3 * L + 4) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem tm_cardT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 3 (cardT B c q) env :=
  tm_msSumT (df := 2) (F := fun _ μ => μ) (fun _ _ _ _ _ _ hz => hz)
    (fun E _ y z _ _ _ _ _ tz => tz.mono (by norm_num)) (by norm_num)
    (fun e μ _ hμ => hμ.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    hB hc hq tB tc tq hdq1 hdq hL hBL

theorem tm_countT {y : Term} {yv dy : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hy : Val w env y yv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env)
    (tq : Tm w L dq q env) (ty : Tm w L dy y env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 2 (countT B c q y) env :=
  tm_msFoldT_cl (G := fun a e μ => if e = yv then μ else a)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_eqT he (hy.ext pre)) hμ hx).congr
      (by split_ifs <;> simp_all))
    (fun E hE x y' z _ _ _ _ _ _ tx ty' tz => (t_ite (t_eqT' ty' (ty.ext hE) (by omega)) tz tx).mono
      (by norm_num)) (by norm_num)
    (fun a e μ ha _ hμ => by
      split_ifs
      · exact hμ.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      · exact ha)
    (val_const 0) (t_small (k := 0) (by norm_num) (by omega) |>.mono (by norm_num))
    hB hc hq tB tc tq hdq1 hdq hL hBL

theorem tm_topT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 4 (topT B c q) env :=
  tm_msFoldT_cl (G := fun a e _ => max a (e + 1))
    (fun _ _ _ _ _ _ _ hx he _ => val_cmaxT hx (val_add he (val_const 1)))
    (fun E _ x y' z _ _ _ _ _ _ tx ty' _ => (tm_cmaxT tx (t_add ty' (t_one (by omega)) (by omega)
      (by norm_num)) (by omega)).mono (by norm_num)) (by norm_num)
    (fun a e μ ha he _ => max_lt ha (by
      have : 2 ^ (2 * L + 3) ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (2 * L + 3) < 2 ^ (4 * L) := by
        calc 2 ^ (2 * L + 3) < 2 ^ (2 * L + 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega))
    (val_const 0) (t_small (k := 0) (by norm_num) (by omega) |>.mono (by norm_num))
    hB hc hq tB tc tq hdq1 hdq hL hBL

theorem tm_kthFoldT {k : Term} {kv dk : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hk : Val w env k kv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env)
    (tq : Tm w L dq q env) (tk : Tm w L dk k env) (hdk : dk ≤ 30) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L (max dk 3 + 1) (kthFoldT B c q k) env := by
  have vk := tk.lt; rw [hk.2] at vk
  refine tm_msFoldT_cl (G := kthStep kv)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_lt (hk.ext pre) hx) hx
      (val_ite (val_lt hx hμ) (val_add (val_add (hk.ext pre) (val_const 1)) he)
          (val_sub hx hμ))).congr
        (by unfold kthStep; split_ifs <;> simp_all))
    (fun E hE x y' z _ _ _ _ _ _ tx ty' tz => (t_ite (t_lt (tk.ext hE) tx (by omega)) tx
      (t_ite (t_lt tx tz (by omega)) (t_add (t_add (tk.ext hE) (t_one (by omega)) (by omega)
        (by omega)) ty' (by omega) (by omega)) (t_sub tx tz))).mono (by omega)) (by omega)
    (fun s e μ hs he _ => ?_) hk (tk.mono (by omega)) hB hc hq tB tc tq hdq1 hdq hL hBL
  unfold kthStep
  split_ifs
  · exact hs
  · have h1 : kv < 2 ^ (max dk 3 * L) := vk.trans_le (pow_le_pow_tier (le_max_left _ _))
    have h2 : 1 + e < 2 ^ (max dk 3 * L) := by
      have : 2 ^ (2 * L + 3) ≤ 2 ^ (3 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (2 * L + 3) < 2 ^ (3 * L) := by
        calc 2 ^ (2 * L + 3) < 2 ^ (2 * L + 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ 2 ^ (3 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := pow_le_pow_tier (L := L) (le_max_right dk 3)
      omega
    have := sum_lt_tier h1 h2 (by omega)
    omega
  · exact (Nat.sub_le _ _).trans_lt hs

theorem tm_kthT {k d : Term} {kv dk dd : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hk : Val w env k kv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env)
    (tq : Tm w L dq q env) (tk : Tm w L dk k env) (td : Tm w L dd d env) (hdk : dk ≤ 30)
    (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    Tm w L (max (max dk 3 + 1) dd) (kthT B c q k d) env := by
  have tS := tm_kthFoldT hB hc hq hk tB tc tq tk hdk hdq1 hdq hL hBL
  exact t_ite (t_lt tk tS (by omega)) (t_sub tS
      (t_add tk (t_one (by omega)) (by omega) (by omega))) td

theorem tm_msLeT {c' q' : Term} {cv' qv' dc' dq' : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') (tB : Tm w L 1 B env)
    (tc : Tm w L dc c env) (tq : Tm w L dq q env) (tc' : Tm w L dc' c' env)
    (tq' : Tm w L dq' q' env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hdq1' : 1 ≤ dq') (hdq' : dq' ≤ 64)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (msLeT B c q c' q') env :=
  tm_msFoldT_cl (G := fun a e μ => if μ ≤ countN Bv cv' qv' e then a else 0)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_lt (val_countT (hB.ext pre) (hc'.ext pre)
      (hq'.ext pre) he) hμ) (val_const 0) hx).congr (by split_ifs <;> simp_all))
    (fun E hE x y' z _ Y _ _ hy' _ tx ty' tz => (t_ite (t_lt (tm_countT (hB.extE hE) (hc'.extE hE)
      (hq'.extE hE) hy' (tB.ext hE) (tc'.ext hE) (tq'.ext hE) ty' hdq1' hdq' hL hBL) tz (by omega))
      (t_small (k := 0) (by norm_num) (by omega)) tx).mono (by norm_num)) (by norm_num)
    (fun a e μ ha _ _ => by split_ifs; exacts [ha, by positivity])
    (val_const 1) (t_small (k := 1) (by norm_num) (by omega)) hB hc hq tB tc tq hdq1 hdq hL hBL

theorem tm_labelWtT {i : Term} {iv di : ℕ} (hB : Val w env B Bv) (hi : Val w env i iv)
    (tB : Tm w L 1 B env) (ti : Tm w L di i env) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 6 (labelWtT B i) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  exact t_add (tm_wtT hB hi (val_const 0) tB ti t0 le_rfl (by norm_num) hL hBL)
    (tm_wtT hB hi (val_msEndT hB hi (val_const 0)) tB ti
      (tm_msEndT hB hi (val_const 0) tB ti t0 le_rfl (by norm_num) hL hBL) (by omega) (by omega)
      hL hBL) (by omega) (by norm_num)

end TierFold

/-! ### Tiers: validity and the code width -/

theorem validN_le_one (a W i : ℕ) : validN a W i ≤ 1 := by unfold validN; split_ifs <;> omega

section TierValid

variable {L : ℕ} {a W i : Term} {av Wv iv da di : ℕ}

theorem tm_validT (ha : Val w env a av) (hW : Val w env W Wv) (hi : Val w env i iv)
    (ta : Tm w L da a env) (tW : Tm w L 1 W env) (ti : Tm w L di i env) (hda : da ≤ 120)
    (hL : 4 ≤ L) (hWL : Wv ≤ L) : Tm w L 1 (validT a W i) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have v1 := val_msEndT hW hi (val_const 0)
  have t1 := tm_msEndT hW hi (val_const 0) tW ti t0 le_rfl (by norm_num) hL hWL
  have v2 := val_msEndT hW hi v1
  have t2 := tm_msEndT hW hi v1 tW ti t1 (by omega) (by omega) hL hWL
  have tm := tm_cminT t2 (tW.mono (by omega)) (by omega)
  have tp : Tm w L 2 (pow2 (cminT (msEndT W i (msEndT W i (const 0))) W)) env :=
    t_pow2 tm (by omega) (fun pre _ => by
      rw [((val_cminT v2 hW).ext pre).2]; have := min_le_right (msEnd Wv iv (msEnd Wv iv 0)) Wv
      omega) (by norm_num) (by omega)
  have tw1 := tm_wtT hW hi (val_const 0) tW ti t0 le_rfl (by norm_num) hL hWL
  have tw2 := tm_wtT hW hi v1 tW ti t1 (by omega) (by omega) hL hWL
  refine tm_val (t_ite (t_lt t0 ta (by omega)) (t_mul (t_mul (t_lt t2 (t_add tW (t_one (by omega))
    (by omega) (by norm_num)) (by omega)) (t_lt ti tp (by omega)) (by norm_num))
      (t_lt (t_add tw1 tw2 (by omega) (by norm_num)) (t_add ta (t_one (by omega)) (by omega)
        (by omega)) (by omega)) (by norm_num)) (t_eqT' ti t0 (by omega)))
    (val_validT ha hW hi) ?_
  exact (validN_le_one _ _ _).trans_lt (lt_tier_one (by omega))

theorem tm_sqrtT {n : Term} {nv dn : ℕ} (hn : Val w env n nv) (tn : Tm w L dn n env)
    (hdn : dn + 2 ≤ 32) (hL : 4 ≤ L) : Tm w L dn (sqrtT n) env := by
  have t1 : Tm w L (max dn 1 + 1) (add n (const 1)) env :=
    t_add tn (t_one (by omega)) (by omega) (by omega)
  refine tm_val (t_sumT t1 (fun E hE x hx => t_lt (t_mul (t_add hx (t_one (by omega)) (by omega)
    (by omega)) (t_add hx (t_one (by omega)) (by omega) (by omega)) (by omega))
      (t_add (tn.ext hE) (t_one (by omega)) (by omega) (by omega)) (by omega))
          (by omega) (by omega))
    (val_sqrtT hn) ?_
  have := tn.lt; rw [hn.2] at this
  rw [sqrtN_eq]; exact (Nat.sqrt_le_self _).trans_lt this

theorem tm_codeWidthT (ha : Val w env a av) (ta : Tm w L da a env) (hda : da + 4 ≤ 32)
    (hL : 10 ≤ L) : Tm w L (da + 1) (codeWidthT a) env := by
  have h784 : 784 < 2 ^ L := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL)
  have tn : Tm w L (1 + da) (mul (const 784) a) env := t_mul (t_const h784) ta (by omega)
  have ts := tm_sqrtT (val_mul (val_const 784) ha) tn (by omega) (by omega)
  refine tm_val (t_ite (t_lt (t_small (k := 0) (by norm_num) (by omega)) ta (by omega))
    (t_add ts (t_small (k := 2) (by norm_num) (by omega)) (by omega) (by omega))
    (t_small (k := 0) (by norm_num) (by omega))) (val_codeWidthT ha) ?_
  have va := ta.lt; rw [ha.2] at va
  have hcw : codeWidth av ≤ 784 * av + 2 := by
    unfold codeWidth; split_ifs
    · omega
    · have := Nat.sqrt_le_self (784 * av); omega
  have h10 : 2 ^ 10 * 2 ^ (da * L) ≤ 2 ^ ((da + 1) * L) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul]; omega)
  omega

end TierValid

/-! ### Tiers: writing -/

theorem topBit_le (K x : ℕ) : topBit K x ≤ K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [topBit, List.range_succ, List.foldl_append, ← topBit, List.foldl_cons, List.foldl_nil]
    split_ifs <;> omega

section TierWrite

variable {L : ℕ} {K x W acc q : Term} {Kv xv Wv accv qv dx da dq : ℕ}

theorem tm_topBitT (hK : Val w env K Kv) (hx : Val w env x xv) (tK : Tm w L 1 K env)
    (tx : Tm w L dx x env) (hL : 4 ≤ L) (hKL : Kv ≤ L) : Tm w L 1 (topBitT K x) env := by
  refine tm_foldT_st hK tK (by norm_num) (t_small (k := 0) (by norm_num) (by omega)) (by norm_num)
    (fun pre _ k hk => ?_) (fun pre y k _ hk hy he => ?_)
  · exact lt_of_eq_of_lt ((val_topBitT (val_const k) hx).ext pre).2
      (lt_tier_one ((topBit_le _ _).trans (hk.trans hKL)))
  · exact (t_ite (t_bit (tx.ext he) (tm_idx (d := 1) (lt_tier_one (by omega))) (by omega))
      (tm_idx (lt_tier_one (by omega))) (tm_acc hy)).mono (by norm_num)

theorem tm_gammaNumT (hK : Val w env K Kv) (hx : Val w env x xv) (tK : Tm w L 1 K env)
    (tx : Tm w L dx x env) (hL : 4 ≤ L) (hKL : Kv ≤ L) : Tm w L 3 (gammaNumT K x) env := by
  have tz := tm_topBitT hK hx tK tx hL hKL
  have vz := val_topBitT hK hx
  have hz := topBit_le Kv xv
  refine tm_val (t_mul (t_pow2 (d := 2) tz (by norm_num)
      (fun pre _ => by rw [(vz.ext pre).2]; omega)
    (by norm_num) (by omega)) (tm_readBitsT (dr := 2) hx (val_const 0) (val_add vz (val_const 1)) tx
      (t_small (k := 0) (by norm_num) (by omega))
          (t_add tz (t_one (by omega)) (by omega) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL (by omega)) (by norm_num))
    (val_gammaNumT hK hx) ((gammaNum_lt _ _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_))
  omega

theorem tm_appendAccT (hW : Val w env W Wv) (hq : Val w env q qv)
    (hx : Val w env x xv) (tW : Tm w L 1 W env) (ta : Tm w L da acc env) (tq : Tm w L dq q env)
    (tx : Tm w L dx x env) (hda : da ≤ 100) (hdq : dq ≤ 100) (hL : 4 ≤ L) (hWL : Wv ≤ L) :
    Tm w L (max da 5 + 1) (appendAccT W acc q x) env := by
  have tz := tm_topBitT hW hx tW tx hL hWL
  have tm := tm_val (d := 1) (tm_cminT (tq.mono (le_max_left dq 1)) (tW.mono (le_max_right dq 1))
    (by omega)) (val_cminT hq hW) (lt_tier_one ((min_le_right _ _).trans hWL))
  have tp : Tm w L 2 (pow2 (cminT q W)) env := t_pow2 tm (by omega) (fun pre _ => by
    rw [((val_cminT hq hW).ext pre).2]; have := min_le_right qv Wv; omega) (by norm_num) (by omega)
  exact (t_ite (t_lt (t_add (t_add tq (t_mul (t_small (k := 2) (by norm_num) (by omega)) tz
    (by norm_num)) (by omega) (by omega)) (t_one (by omega)) (by omega) (by omega))
      (t_add tW (t_one (by omega)) (by omega) (by norm_num)) (by omega))
    (t_add ta (t_mul tp (tm_gammaNumT hW hx tW tx hL hWL) (by norm_num)) (by omega) (by omega))
    ta).mono (by omega)

theorem tm_appendPosT (hW : Val w env W Wv) (hq : Val w env q qv) (hx : Val w env x xv)
    (tW : Tm w L 1 W env) (tq : Tm w L dq q env) (tx : Tm w L dx x env) (hdq : dq ≤ 100)
    (hL : 4 ≤ L) (hWL : Wv ≤ L) : Tm w L 1 (appendPosT W q x) env := by
  have tz := tm_topBitT hW hx tW tx hL hWL
  have t1 : Tm w L (max (max dq 2 + 1) 1 + 1)
      (add (add q (mul (const 2) (topBitT W x))) (const 1)) env :=
    t_add (t_add tq (t_mul (t_small (k := 2) (by norm_num) (by omega)) tz (by norm_num)) (by omega)
      (by omega)) (t_one (by omega)) (by omega) (by omega)
  have t2 : Tm w L (max (max dq 2 + 1) 1 + 1) (add W (const 1)) env :=
    (t_add tW (t_one (by omega)) (by omega) (by norm_num)).mono (by omega)
  refine tm_val (tm_cminT t1 t2 (by omega)) (val_appendPosT hW hq hx) ?_
  rw [one_mul]
  have := appendN_snd_le Wv 0 qv xv
  have := two_mul_add_one_lt_pow hL
  omega

end TierWrite

/-! ### Tiers: the code of a multiset with given multiplicities -/

variable (w L) in
/-- A multiplicity function on stable arguments of tier `dk`; only boundedness of the result is
asked (tier `128`). -/
def TmV1 (cnt : Term → Term) (dk : ℕ) (env : List ℕ) : Prop :=
  ∀ E, Ext L E env → ∀ (y : Term) (Y : ℕ), Val w E y Y → Tm w L dk y E → Tm w L 128 (cnt y) E

theorem ocStep_prev (W : ℕ) (C : ℕ → ℕ) (s : ℕ × ℕ × ℕ) (k : ℕ) :
    (ocStep W C s k).2.2 = if 0 < C k then k + 1 else s.2.2 := by
  unfold ocStep; split_ifs <;> rfl

theorem foldl_ocStep_prev (W : ℕ) (C : ℕ → ℕ) (s : ℕ × ℕ × ℕ) (hs : s.2.2 = 0) (j : ℕ) :
    ((List.range j).foldl (ocStep W C) s).2.2 ≤ j := by
  induction j with
  | zero => simp [hs]
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ocStep_prev]
    split_ifs <;> omega

theorem ocP_lt {W P : ℕ} {s : ℕ × ℕ × ℕ} (h : OcInv W s) (hP : s.2.2 ≤ P) :
    ocP W s < 2 ^ (2 * W + 2) * (P + 1) := by
  have h1 : s.1 < 2 ^ (W + 1) := h.1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : s.2.1 < 2 ^ (W + 1) := lt_of_le_of_lt h.2 Nat.lt_two_pow_self
  have e : 2 ^ (2 * W + 2) = 2 ^ (W + 1) * 2 ^ (W + 1) := by rw [← pow_add]; ring_nf
  rw [e, ocP]
  have : 2 ^ (W + 1) * (2 ^ (W + 1) * s.2.2) ≤ 2 ^ (W + 1) * (2 ^ (W + 1) * P) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP)
  nlinarith

section TierOfCount

variable {L : ℕ} {W X : Term} {cnt : Term → Term} {Wv Xv dX : ℕ} {C : ℕ → ℕ}

theorem tm_ocNT (hW : Val w env W Wv) (tW : Tm w L 1 W env) (hL : 4 ≤ L) (hWL : Wv ≤ L) :
    Tm w L 2 (ocNT W) env :=
  t_pow2 (t_add tW (t_one (by omega)) (by omega) (by norm_num)) (by norm_num) (fun pre _ => by
    rw [((val_add hW (val_const 1)).ext pre).2]; omega) (by norm_num) (by omega)

theorem tm_ocNumT (hX : Val w env X Xv) (hC : ValF1 w cnt C env) (tX : Tm w L dX X env)
    (tC : TmV1 w L cnt dX env) (hdX : dX ≤ 32) (hL : 4 ≤ L) : Tm w L dX (ocNumT X cnt) env := by
  have vX := tX.lt; rw [hX.2] at vX
  unfold ocNumT sumT
  refine tm_foldT_st hX tX hdX (t_small (k := 0) (by norm_num) (by omega)) hdX
    (fun pre _ k hk => ?_) (fun pre x k _ hk hx he => ?_)
  · refine lt_of_eq_of_lt ((val_ocNumT (val_const k) hC).ext pre).2 ?_
    have : ocNum k C ≤ k := by
      unfold ocNum
      calc _ ≤ ∑ _j ∈ Finset.range k, 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> omega
        _ = k := by simp
    omega
  · exact (t_add (tm_acc hx) (t_lt (t_small (k := 0) (by norm_num) (by omega))
      (tC _ he _ _ (val_idx _ x k) (tm_idx (hk.trans vX))) (by omega)) (by omega)
      (by omega)).mono (by omega)

theorem tm_ocStepT {s k : Term} {sv kv ds dk : ℕ} (hW : Val w env W Wv) (hC : ValF1 w cnt C env)
    (hs : Val w env s sv) (hk : Val w env k kv) (tW : Tm w L 1 W env) (tC : TmV1 w L cnt dk env)
    (ts : Tm w L ds s env) (tk : Tm w L dk k env) (hds : ds ≤ 32) (hdk : dk ≤ 32) (hL : 4 ≤ L)
    (hWL : Wv ≤ L) : Tm w L 128 (ocStepT W cnt s k) env := by
  have hN := val_pow2 (val_add hW (val_const 1))
  have tN := tm_ocNT hW tW hL hWL
  have hc := hC [] _ _ hk
  simp only [List.nil_append] at hc
  have tc := tC _ (Ext.refl _) _ _ hk tk
  have vlen := val_mod (val_div hs hN) hN
  have tlen : Tm w L 2 (mod (div s (ocNT W)) (ocNT W)) env := t_mod (t_div ts tN) tN Pos.pow2'
  have tcode : Tm w L 2 (mod s (ocNT W)) env := t_mod ts tN Pos.pow2'
  have vgap := val_sub (val_add hk (val_const 1)) (val_div (val_div hs hN) hN)
  have tgap : Tm w L (max dk 1 + 1) (sub (add k (const 1)) (div (div s (ocNT W)) (ocNT W))) env :=
    t_sub (t_add tk (t_one (by omega)) (by omega) (by omega)) (t_div (t_div ts tN) tN)
  have ta1 := tm_appendAccT hW vlen vgap tW tcode tlen tgap (by norm_num) (by norm_num) hL hWL
  have vp1 := val_appendPosT hW vlen vgap
  have tp1 := tm_appendPosT hW vlen vgap tW tlen tgap (by norm_num) hL hWL
  have ta2 := tm_appendAccT hW vp1 hc tW ta1 tp1 tc (by omega) (by norm_num) hL hWL
  have tp2 := tm_appendPosT hW vp1 hc tW tp1 tc (by norm_num) hL hWL
  exact (t_ite (t_lt (t_small (k := 0) (by norm_num) (by omega)) tc (by omega))
    (t_add ta2 (t_mul tN (t_add tp2 (t_mul tN (t_add tk (t_one (by omega)) (by omega) (by omega))
      (by omega)) (by omega) (by omega)) (by omega)) (by omega) (by omega)) ts).mono (by omega)

theorem tm_ocFoldT (hW : Val w env W Wv) (hX : Val w env X Xv) (hC : ValF1 w cnt C env)
    (tW : Tm w L 1 W env) (tX : Tm w L dX X env) (tC : TmV1 w L cnt dX env) (hdX : dX + 3 ≤ 32)
    (hL : 4 ≤ L) (hWL : Wv ≤ L) : Tm w L (dX + 3) (ocFoldT W X cnt) env := by
  have vX := tX.lt; rw [hX.2] at vX
  have tN := tm_ocNT hW tW hL hWL
  have tm := t_add (tm_ocNumT hX hC tX tC (by omega) hL) (t_one (by omega)) (by omega) (by omega)
  have vm := val_add (val_ocNumT hX hC) (val_const 1)
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have ti := t_add (tm_appendAccT hW (val_const 0) vm tW t0 t0 tm (by norm_num)
      (by norm_num) hL hWL)
    (t_mul tN (tm_appendPosT hW (val_const 0) vm tW t0 tm (by norm_num) hL hWL) (by norm_num))
    (by omega) (by norm_num)
  have hinv : OcInv Wv ((appendN Wv 0 0 (ocNum Xv C + 1)).1,
      (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0) :=
    ⟨appendN_lt (by simp), appendN_snd_le _ 0 0 _⟩
  refine tm_foldT_st hX tX (by omega) ti hdX (fun pre _ j hj => ?_) (fun pre x k _ hk hx he => ?_)
  · refine lt_of_eq_of_lt ((val_ocFold_gen hW hX hC (val_const j)).ext pre).2 ?_
    refine (ocP_lt (ocInv_foldl _ _ hinv) (foldl_ocStep_prev _ _ _ rfl j)).trans_le ?_
    have e : 2 ^ ((dX + 3) * L) = 2 ^ (3 * L) * 2 ^ (dX * L) := by rw [← pow_add]; ring_nf
    rw [e]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega)
  · exact tm_ocStepT (hW.at2 pre x k) (fun pre' y Y hy => by
      have := hC (pre' ++ x :: k :: pre) y Y (by simpa using hy); simpa using this)
      (val_acc _ x k) (val_idx _ x k) (tW.ext he) (fun E hE => tC E (hE.trans he)) (tm_acc hx)
      (tm_idx (hk.trans vX)) (by omega) (by omega) hL hWL

theorem tm_ocCodeT (hW : Val w env W Wv) (hX : Val w env X Xv) (hC : ValF1 w cnt C env)
    (tW : Tm w L 1 W env) (tX : Tm w L dX X env) (tC : TmV1 w L cnt dX env) (hdX : dX + 3 ≤ 32)
    (hL : 4 ≤ L) (hWL : Wv ≤ L) : Tm w L 1 (ocCodeT W X cnt) env := by
  refine tm_val (t_mod (tm_ocFoldT hW hX hC tW tX tC hdX hL hWL) (tm_ocNT hW tW hL hWL) Pos.pow2')
    (val_ocCodeT hW hX hC) ?_
  have hI := ocInv_foldl (W := Wv) (cnt := C) (List.range Xv)
    ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0)
    ⟨appendN_lt (by simp), appendN_snd_le Wv 0 0 _⟩
  have hm : (msOfCount Wv Xv C).1 = ((List.range Xv).foldl (ocStep Wv C)
    ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0)).1 := rfl
  rw [hm]
  refine hI.1.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  rw [one_mul]; exact (min_le_right _ _).trans hWL

theorem tm_ocLenT (hW : Val w env W Wv) (hX : Val w env X Xv) (hC : ValF1 w cnt C env)
    (tW : Tm w L 1 W env) (tX : Tm w L dX X env) (tC : TmV1 w L cnt dX env) (hdX : dX + 3 ≤ 32)
    (hL : 4 ≤ L) (hWL : Wv ≤ L) : Tm w L 1 (ocLenT W X cnt) env := by
  have tN := tm_ocNT hW tW hL hWL
  refine tm_val (t_mod (t_div (tm_ocFoldT hW hX hC tW tX tC hdX hL hWL) tN) tN Pos.pow2')
    (val_ocLenT hW hX hC) ?_
  have hI := ocInv_foldl (W := Wv) (cnt := C) (List.range Xv)
    ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0)
    ⟨appendN_lt (by simp), appendN_snd_le Wv 0 0 _⟩
  have hm : (msOfCount Wv Xv C).2 = ((List.range Xv).foldl (ocStep Wv C)
    ((appendN Wv 0 0 (ocNum Xv C + 1)).1, (appendN Wv 0 0 (ocNum Xv C + 1)).2, 0)).2.1 := rfl
  rw [hm, one_mul]
  have := hI.2
  have := two_mul_add_one_lt_pow hL
  omega

end TierOfCount

section TierAddSub

variable {L : ℕ} {B W c q c' q' : Term} {Bv Wv cv qv cv' qv' dc dq dc' dq' : ℕ}

theorem tmV1_addCntT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hc' : Val w env c' cv') (hq' : Val w env q' qv') (tB : Tm w L 1 B env) (tc : Tm w L dc c env)
    (tq : Tm w L dq q env) (tc' : Tm w L dc' c' env) (tq' : Tm w L dq' q' env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hdq1' : 1 ≤ dq') (hdq' : dq' ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    TmV1 w L (addCntT B c q c' q') 4 env := fun E hE y _ hy ty =>
  (t_add (tm_countT (hB.extE hE) (hc.extE hE) (hq.extE hE) hy (tB.ext hE) (tc.ext hE) (tq.ext hE) ty
    hdq1 hdq hL hBL) (tm_countT (hB.extE hE) (hc'.extE hE) (hq'.extE hE) hy (tB.ext hE) (tc'.ext hE)
      (tq'.ext hE) ty hdq1' hdq' hL hBL) (by omega) (by norm_num)).mono (by norm_num)

theorem tmV1_subCntT (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hc' : Val w env c' cv') (hq' : Val w env q' qv') (tB : Tm w L 1 B env) (tc : Tm w L dc c env)
    (tq : Tm w L dq q env) (tc' : Tm w L dc' c' env) (tq' : Tm w L dq' q' env) (hdq1 : 1 ≤ dq)
    (hdq : dq ≤ 64) (hdq1' : 1 ≤ dq') (hdq' : dq' ≤ 64) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    TmV1 w L (subCntT B c q c' q') 4 env := fun E hE y _ hy ty =>
  (t_sub (tm_countT (hB.extE hE) (hc.extE hE) (hq.extE hE) hy (tB.ext hE) (tc.ext hE) (tq.ext hE) ty
    hdq1 hdq hL hBL) (tm_countT (hB.extE hE) (hc'.extE hE) (hq'.extE hE) hy (tB.ext hE) (tc'.ext hE)
      (tq'.ext hE) ty hdq1' hdq' hL hBL)).mono (by norm_num)

theorem tm_addCodeT (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') (tB : Tm w L 1 B env)
    (tW : Tm w L 1 W env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (tc' : Tm w L dc' c' env)
    (tq' : Tm w L dq' q' env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hdq1' : 1 ≤ dq') (hdq' : dq' ≤ 64)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) (hWL : Wv ≤ L) :
    Tm w L 1 (addCodeT B W c q c' q') env ∧ Tm w L 1 (addLenT B W c q c' q') env := by
  have hX := val_cmaxT (val_topT hB hc hq) (val_topT hB hc' hq')
  have tX := tm_cmaxT (tm_topT hB hc hq tB tc tq hdq1 hdq hL hBL)
    (tm_topT hB hc' hq' tB tc' tq' hdq1' hdq' hL hBL) (by omega)
  have hC := valF1_addCntT hB hc hq hc' hq'
  have tC := tmV1_addCntT hB hc hq hc' hq' tB tc tq tc' tq' hdq1 hdq hdq1' hdq' hL hBL
  exact ⟨tm_ocCodeT hW hX hC tW tX tC (by norm_num) hL hWL, tm_ocLenT hW hX hC tW tX tC
      (by norm_num) hL hWL⟩

theorem tm_subCodeT (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv') (tB : Tm w L 1 B env)
    (tW : Tm w L 1 W env) (tc : Tm w L dc c env) (tq : Tm w L dq q env) (tc' : Tm w L dc' c' env)
    (tq' : Tm w L dq' q' env) (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hdq1' : 1 ≤ dq') (hdq' : dq' ≤ 64)
    (hL : 4 ≤ L) (hBL : Bv ≤ L) (hWL : Wv ≤ L) :
    Tm w L 1 (subCodeT B W c q c' q') env ∧ Tm w L 1 (subLenT B W c q c' q') env := by
  have hX := val_topT hB hc hq
  have tX := tm_topT hB hc hq tB tc tq hdq1 hdq hL hBL
  have hC := valF1_subCntT hB hc hq hc' hq'
  have tC := tmV1_subCntT hB hc hq hc' hq' tB tc tq tc' tq' hdq1 hdq hdq1' hdq' hL hBL
  exact ⟨tm_ocCodeT hW hX hC tW tX tC (by norm_num) hL hWL, tm_ocLenT hW hX hC tW tX tC
      (by norm_num) hL hWL⟩

end TierAddSub

/-! ### The terms on genuine codes -/

section OnCodes

variable {B W c q c' q' y k d a i : Term} {Bv Wv cv qv cv' qv' yv kv dv av iv : ℕ}
  {σ τ : Multiset ℕ}

theorem val_msEndT_msCode (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (h : BitsAt cv qv (msCode σ)) (hl : (msCode σ).length ≤ Bv) :
    Val w env (msEndT B c q) (qv + (msCode σ).length) :=
  (val_msEndT hB hc hq).congr (msParse_msCode h hl).2.1

theorem val_wtT_msCode (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (h : BitsAt cv qv (msCode σ)) (hl : (msCode σ).length ≤ Bv) : Val w env (wtT B c q) (wt σ) :=
  (val_wtT hB hc hq).congr (wtN_msCode h hl)

theorem val_cardT_msCode (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (h : BitsAt cv qv (msCode σ)) (hl : (msCode σ).length ≤ Bv) :
    Val w env (cardT B c q) (Multiset.card σ) :=
  (val_cardT hB hc hq).congr (cardN_msCode h hl)

theorem val_countT_msCode (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hy : Val w env y yv) (h : BitsAt cv qv (msCode σ)) (hl : (msCode σ).length ≤ Bv) :
    Val w env (countT B c q y) (σ.count yv) :=
  (val_countT hB hc hq hy).congr (countN_msCode h hl yv)

theorem val_kthT_msCode (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hk : Val w env k kv) (hd : Val w env d dv) (h : BitsAt cv qv (msCode σ))
    (hl : (msCode σ).length ≤ Bv) : Val w env (kthT B c q k d) ((σ.sort (· ≤ ·)).getD kv dv) :=
  (val_kthT hB hc hq hk hd).congr (kthN_msCode h hl kv dv)

theorem val_msLeT_msCode (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv)
    (hc' : Val w env c' cv') (hq' : Val w env q' qv') (h : BitsAt cv qv (msCode σ))
    (hl : (msCode σ).length ≤ Bv) (h' : BitsAt cv' qv' (msCode τ)) (hl' : (msCode τ).length ≤ Bv) :
    Val w env (msLeT B c q c' q') (if σ ≤ τ then 1 else 0) :=
  (val_msLeT hB hc hq hc' hq').congr (leN_msCode h hl h' hl')

theorem val_addCodeT_msCode (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv')
    (h : BitsAt cv qv (msCode σ)) (hl : (msCode σ).length ≤ Bv) (h' : BitsAt cv' qv' (msCode τ))
    (hl' : (msCode τ).length ≤ Bv) (hw : (msCode (σ + τ)).length ≤ Wv) :
    Val w env (addCodeT B W c q c' q') (ofBits (msCode (σ + τ))) ∧
      Val w env (addLenT B W c q c' q') (msCode (σ + τ)).length := by
  have e := addN_msCode h hl h' hl' hw
  exact ⟨(val_addCodeT hB hW hc hq hc' hq').congr (by rw [e]),
    (val_addLenT hB hW hc hq hc' hq').congr (by rw [e])⟩

theorem val_subCodeT_msCode (hB : Val w env B Bv) (hW : Val w env W Wv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hc' : Val w env c' cv') (hq' : Val w env q' qv')
    (h : BitsAt cv qv (msCode σ)) (hl : (msCode σ).length ≤ Bv) (h' : BitsAt cv' qv' (msCode τ))
    (hl' : (msCode τ).length ≤ Bv) (hw : (msCode (σ - τ)).length ≤ Wv) :
    Val w env (subCodeT B W c q c' q') (ofBits (msCode (σ - τ))) ∧
      Val w env (subLenT B W c q c' q') (msCode (σ - τ)).length := by
  have e := subN_msCode h hl h' hl' hw
  exact ⟨(val_subCodeT hB hW hc hq hc' hq').congr (by rw [e]),
    (val_subLenT hB hW hc hq hc' hq').congr (by rw [e])⟩

theorem val_labelWtT_labelCode {l : Label} (hB : Val w env B Bv) (hi : Val w env i (labelCode av l))
    (ha : av ≠ 0) (hl : labelWt l ≤ av) (hw : codeWidth av ≤ Bv) :
    Val w env (labelWtT B i) (labelWt l) :=
  (val_labelWtT hB hi).congr (labelWtN_labelCode ha hl hw)

theorem val_validT_decode (ha : Val w env a av) (hW : Val w env W (codeWidth av))
    (hi : Val w env i iv) (hlt : iv < 2 ^ codeWidth av) :
    Val w env (validT a W i) (if (decodeLabel av iv).isSome then 1 else 0) :=
  (val_validT ha hW hi).congr (validN_eq hlt)

theorem val_labelWtT_decode {l : Label} (hW : Val w env W (codeWidth av)) (hi : Val w env i iv)
    (hlt : iv < 2 ^ codeWidth av) (h : decodeLabel av iv = some l) :
    Val w env (labelWtT W i) (labelWt l) :=
  (val_labelWtT hW hi).congr (labelWtN_decode hlt h)

end OnCodes

end Cslib.Complexity.NtimeDspace.Cube.Num
