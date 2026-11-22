/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.EntryTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.StepTerm

/-!
# The entry and range states as terms, part 2 (Lemma 6.4)

Terms for the validity tests and the state-level functions of `EntryNum.lean`, built from the
pieces of `EntryTerm.lean`, `CodeTerm.lean` and `BudgetTerm.lean`.

## Main definitions

* `everyE`: a bounded universal test; `fldT`: the field of a label in an argument code.
* `copiesOkT`, `argsOkT`: `copiesOkN`, `argsOkN`.
* `cQT`, `cAT`, `pQT`, `pAT`: the node counts and arrays of the first two cliques of a cache.
* `EIn`: the bundled hypotheses on the inputs (the state code, the field width and the fuel are
  below `2^L`, with `16 ≤ L`, `fw < L`, `w(Φ₀ / 2^e) + 2 ≤ B ≤ L` for `2K = 2^(2^e)` and a good
  setup).
* `clTagT`, `clWidthT`, `clChildT`, `lastChildT`, `entTagT`, `entWidthT`, `entChildT`,
  `rngChildT`, `factorT`, `factorGT`, `psiT`, `rangeT`, `litCT`, `zeroCT`, `rStreamT`;
  the dispatch `eTagT`, `eWidthT`, `eChildT`. The leaf factors of the first clique are a term
  parameter `f0T v x f`.

## Main results

* Values (every term): `val_copiesOkT`, `val_argsOkT`, `val_clTagT`, `val_clWidthT`,
  `val_clChildT`, `val_lastChildT`, `val_entTagT`, `val_entWidthT`, `val_entChildT`,
  `val_rngChildT`, `val_factorT`, `val_factorGT`, `val_psiT`, `val_rangeT`, `val_eTagT`,
  `val_eWidthT`, `val_eChildT`. With `entry_agree`, the dispatch terms compute the tags, widths
  and child codes of `Setup.gen` on the reachable entry states.
* Tiers: `tm_everyE`, `tm_argLabT`, `tm_copiesOkT`, `tm_argsOkT`, `tm_clTagT`, `tm_clWidthT`,
  `tm_entTagT`, `tm_entWidthT`, `tm_lastChildT` (from a bound on the child code), `tm_eTagT`
  (tier `1`) and `tm_eWidthT` (tier `7`) under `EIn` on the reachable entry states.
  `tm_ite2v` needs the tier of the taken branch only, and `tm_encE'` gives a list code the tier
  of any bound on its value.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct

variable {w : List Bool} {env : List ℕ} {L : ℕ}

/-! ### Bounded universal tests -/

/-- `1` if `test k = 1` for every `k < n` (for `0`/`1`-valued tests). -/
def everyE (n : Term) (test : Term → Term) : Term :=
  lt (sumT n fun k => sub (const 1) (test k)) (const 1)

theorem foldl_one_sub_le (F : ℕ → ℕ) : ∀ k, (List.range k).foldl (fun x j => x + (1 - F j)) 0 ≤ k
  | 0 => le_rfl
  | k + 1 => by
    rw [List.range_succ, List.foldl_append]
    have := foldl_one_sub_le F k
    simp only [List.foldl_cons, List.foldl_nil]; omega

theorem val_everyE {n : Term} {test : Term → Term} {N : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hn : Val w env n N)
    (hv : ∀ pre x k, k < N → Val w (x :: k :: (pre ++ env)) (test (lvl (pre ++ env).length))
        (ind (P k))) :
    Val w env (everyE n test) (ind (∀ k < N, P k)) := by
  have hs := val_sumT (body := fun k => sub (const 1) (test k)) (g := fun k => 1 - ind (P k)) hn
    fun pre x k hk => val_sub (val_const 1) (hv pre x k hk)
  refine (val_lt hs (val_const 1)).congr ?_
  have key : (∑ k ∈ Finset.range N, (1 - ind (P k)) < 1) ↔ ∀ k < N, P k := by
    rw [Nat.lt_one_iff, Finset.sum_eq_zero_iff]
    refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
    · have := h k (Finset.mem_range.mpr hk)
      by_contra hp
      simp only [ind, hp, ite_false] at this
      omega
    · simp only [ind, h k (Finset.mem_range.mp hk), ite_true, Nat.sub_self]
  by_cases hall : ∀ k < N, P k
  · simp only [ind, key.mpr hall, ite_true]; exact (ite_eq_left hall).symm
  · simp only [ind, mt key.mp hall, ite_false]; exact (ite_eq_right hall).symm

theorem tm_everyE {n : Term} {test : Term → Term} {N dn : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hn : Val w env n N) (tn : Tm w L dn n env) (hdn1 : 1 ≤ dn) (hdn : dn ≤ 32)
    (hv : ∀ pre x k, k < N → Val w (x :: k :: (pre ++ env)) (test (lvl (pre ++ env).length))
        (ind (P k)))
    (ht : ∀ pre x k, Small L pre → k < N → x < 2 ^ (dn * L) → Ext L (x :: k :: (pre ++ env)) env →
      Tm w L 1 (test (lvl (pre ++ env).length)) (x :: k :: (pre ++ env)))
    (hL : 1 ≤ L) : Tm w L 1 (everyE n test) env := by
  have hNlt : N < 2 ^ (dn * L) := by
    have h1 := (tn [] Small.nil).2; rwa [List.nil_append, hn.2] at h1
  have hs : Tm w L dn (foldT n (const 0) fun acc i => add acc (sub (const 1) (test i))) env := by
    refine tm_foldT_st hn tn hdn ((t_const (k := 0) (by positivity)).mono hdn1) hdn
      (fun pre _ k hk => ?_) (fun pre x k hp hk hx he => ?_)
    · have hf := val_foldT (n := const k) (f := fun acc i => add acc (sub (const 1) (test i)))
        (step := fun x j => x + (1 - ind (P j))) (val_const k) (val_const 0)
        fun pre' x' j
            hj => val_add (val_acc _ x' j) (val_sub (val_const 1) (hv pre' x' j (by omega)))
      rw [(hf.ext pre).2]
      exact (foldl_one_sub_le _ k).trans_lt (lt_of_le_of_lt hk hNlt)
    · exact (t_add (tm_acc hx) (t_sub (t_one hL) (ht pre x k hp hk hx he)) hL (by omega)).mono
        (by omega)
  exact t_lt hs (t_one hL) hL

/-! ### Fields of argument codes -/

/-- The field of the label at `u` in an argument code `x` of node `v`. -/
def fldT (arT qT fwT v x u : Term) : Term :=
  mod (divPowT (const 2) x (argOffT arT qT fwT v u)) (pow2 (codeWidthT (budT arT qT fwT v u)))

section Fields

variable {arT qT fwT v x u : Term} {ar q fw V X U : ℕ}

theorem val_fldT (har : Val w env arT ar) (hq : Val w env qT q) (hfw : Val w env fwT fw)
    (hv : Val w env v V) (hx : Val w env x X) (hu : Val w env u U) :
    Val w env (fldT arT qT fwT v x u)
      (X / 2 ^ argOffN ar q fw V U % 2 ^ codeWidth (budgetN ar q fw V U)) := by
  have hb := (val_budT har.toExact hq.toExact hfw.toExact hv.toExact hu.toExact).toNum
  have ho := (val_argOffT har.toExact hq.toExact hfw.toExact hv.toExact hu.toExact).toNum
  exact val_mod ((val_divPowT (Cross.Exact.val_const 2 env) hx.toExact ho.toExact).toNum)
    (val_pow2 (val_codeWidthT hb))

/-- The dummy grid inputs of a budget array (side `1`, code `0`). -/
theorem inp_dummy (har : Val w env arT ar) (hq : Val w env qT q) (hfw : Val w env fwT fw) :
    Inp w env arT qT fwT (const 1) (const 0) ar q fw 1 0 :=
  ⟨har.toExact, hq.toExact, hfw.toExact, Cross.Exact.val_const 1 env, Cross.Exact.val_const 0 env⟩

theorem tiers_dummy (tA : Tm w L 32 arT env) (tq : Tm w L 1 qT env) (tfw : Tm w L 1 fwT env)
    (hL : 16 ≤ L) (hfwL : fw < L) : Tiers w L env arT qT fwT (const 1) (const 0) fw 1 :=
  ⟨tA, tq, tfw, t_one (by omega), (t_const (k := 0) (by positivity)).mono (by norm_num), hL, hfwL,
    Nat.one_pos⟩

/-- The tiers of the budget, its code width and the field. -/
theorem tm_fld {dv dx du : ℕ} (har : Val w env arT ar) (hq : Val w env qT q)
    (hfw : Val w env fwT fw)
    (hv : Val w env v V) (hx : Val w env x X) (hu : Val w env u U) (tA : Tm w L 32 arT env)
    (tq : Tm w L 1 qT env) (tfw : Tm w L 1 fwT env) (tv : Tm w L dv v env) (tx : Tm w L dx x env)
    (tu : Tm w L du u env) (hdv : dv ≤ 20) (hdu : du ≤ 20) (hdx : dx ≤ 32) (hL : 16 ≤ L)
    (hfwL : fw < L) (hW : codeWidth (budgetN ar q fw V U) ≤ L) :
    Tm w L 1 (budT arT qT fwT v u) env ∧ Tm w L 1 (codeWidthT (budT arT qT fwT v u)) env ∧
      Tm w L 1 (fldT arT qT fwT v x u) env := by
  have inp := inp_dummy har hq hfw
  have tie := tiers_dummy tA tq tfw hL hfwL
  have hb := (val_budT har.toExact hq.toExact hfw.toExact hv.toExact hu.toExact).toNum
  have tb := tm_budT tie hfw.toExact tv tu (by omega)
  have hWv := val_codeWidthT hb
  have tW := tm_val (tm_codeWidthT hb tb (by norm_num) (by omega)) hWv (lt_tier_one hW)
  have tOff := tm_argOffT inp tie tv tu (by omega) (by omega)
  have td := t_divPowT ((t_const (k := 2) (lit_lt_two_pow (by norm_num) (by omega))) : Tm w L 1 _
      env)
    tx tOff (by omega) hdx
  have tp := t_pow2v (d := 2) hWv tW (by norm_num) (by omega) (by norm_num) (by omega)
  refine ⟨tb, tW, tm_val (t_mod td tp Pos.pow2') (val_fldT har hq hfw hv hx hu) ?_⟩
  exact (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The tier of the code of an argument label**: `1`. -/
theorem tm_argLabT {dv dx du : ℕ} (har : Val w env arT ar) (hq : Val w env qT q)
    (hfw : Val w env fwT fw) (hv : Val w env v V) (hx : Val w env x X) (hu : Val w env u U)
    (tA : Tm w L 32 arT env) (tq : Tm w L 1 qT env) (tfw : Tm w L 1 fwT env) (tv : Tm w L dv v env)
    (tx : Tm w L dx x env) (tu : Tm w L du u env) (hdv : dv ≤ 20) (hdu : du ≤ 20) (hdx : dx ≤ 32)
    (hL : 16 ≤ L) (hfwL : fw < L) (hW : codeWidth (budgetN ar q fw V U) ≤ L) :
    Tm w L 1 (argLabT arT qT fwT v x u) env := by
  obtain ⟨tb, tW, tf⟩ := tm_fld har hq hfw hv hx hu tA tq tfw tv tx tu hdv hdu hdx hL hfwL hW
  have hb := (val_budT har.toExact hq.toExact hfw.toExact hv.toExact hu.toExact).toNum
  have tval := tm_validT hb (val_codeWidthT hb) (val_fldT har hq hfw hv hx hu) tb tW tf
      (by norm_num)
    (by omega) hW
  have t1 : Tm w L 1 (const 1) env := t_one (by omega)
  have t3 : Tm w L 1 (const 3) env := t_const (lit_lt_two_pow (by norm_num) (by omega))
  have t0 : Tm w L 1 (const 0) env := t_const (by positivity)
  exact (t_ite (t_lt tv tq (by omega)) (t_ite (t_lt tu tq (by omega))
      (t_ite (t_eqT' tu tv (by omega)) t3
    (t_ite (t_lt t0 tb (by omega)) (t_ite (t_eqT' tval t1 (by omega)) tf t3) t3)) t3) t3).mono
    (by omega)

end Fields

/-- Every digit of a budget array is a budget or `0`. -/
theorem budgetN_le_of_arr {q fw Φ : ℕ} {b : ℕ → ℕ → ℕ} (hb : ArrFits q fw b)
    (hΦ : ∀ u v, u < v → v < q → b u v ≤ Φ) (u v : ℕ) : budgetN (arrN q fw b) q fw u v ≤ Φ := by
  unfold budgetN arrN
  rw [digitN_packN (arrN_digits_lt hb)]
  split_ifs with h1 h2
  · have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; simp at h1
      · exact h0
    exact hΦ _ _ h2 (Nat.mod_lt _ hq)
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The digit bound for the budget array of a clique on a valid path. -/
theorem codeWidth_budgetN_path (S : Setup) (hS : S.Good) {chs : List ℕ} (hp : S.PathOK chs)
    {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {B : ℕ} (hB : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B)
    (a b : ℕ) :
    codeWidth (budgetN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw a
        b) ≤ B := by
  refine le_trans (codeWidth_mono (budgetN_le_of_arr (Φ := S.C₀.potential / 2 ^ e)
    (fits_path S hS hp).arr (fun u v huv hv => ?_) a b)) (by omega)
  rw [extN, dite_eq_left ⟨by omega, hv⟩]
  exact ((S.clique chs).a_le_spair (Fin.mk_lt_mk.mpr huv)).trans (spair_le_path S he hp)

/-! ### Validity of copies -/

/-- The test of the copy of node `nodes p` for the pair with `u`. -/
def copyBodyT (arT qT fwT : Term) (nodes : Term → Term) (ξ p u : Term) : Term :=
  ite (eqT u (nodes p)) (const 1)
    (ite (eqT (validT (budT arT qT fwT (nodes p) u) (codeWidthT (budT arT qT fwT (nodes p) u))
        (fldT arT qT fwT (nodes p) (sliceT arT qT fwT nodes ξ p) u)) (const 1))
      (eqT (labelWtT (codeWidthT (budT arT qT fwT (nodes p) u))
        (fldT arT qT fwT (nodes p) (sliceT arT qT fwT nodes ξ p) u)) (budT arT qT fwT (nodes p) u))
      (const 0))

/-- **All copies decode to labels of exact weight** (`copiesOkN`), as `0`/`1`. -/
def copiesOkT (arT qT fwT gT : Term) (nodes : Term → Term) (ξ : Term) : Term :=
  everyE
      gT fun p => ite (lt (nodes p) qT) (everyE qT fun u => copyBodyT arT qT fwT nodes ξ p u) (const 1)

/-- The condition of the copy of `nodes p` for `u`. -/
def CopyOk (ar q fw : ℕ) (Nd : ℕ → ℕ) (Ξ p u : ℕ) : Prop :=
  u ≠ Nd p →
    validN (budgetN ar q fw (Nd p) u) (codeWidth (budgetN ar q fw (Nd p) u))
        (sliceN ar q fw Nd Ξ p / 2 ^ argOffN ar q fw (Nd p) u % 2 ^ codeWidth
            (budgetN ar q fw (Nd p) u)) = 1 ∧
      labelWtN (codeWidth (budgetN ar q fw (Nd p) u))
        (sliceN ar q fw Nd Ξ p / 2 ^ argOffN ar q fw (Nd p) u % 2 ^ codeWidth
            (budgetN ar q fw (Nd p) u)) =
        budgetN ar q fw (Nd p) u

instance (ar q fw : ℕ) (Nd : ℕ → ℕ) (Ξ p u : ℕ) : Decidable (CopyOk ar q fw Nd Ξ p u) := by
  unfold CopyOk; infer_instance

section Copies

variable {arT qT fwT gT : Term} {nodes : Term → Term} {ξ p u : Term} {ar q fw g Ξ P U : ℕ}
  {Nd : ℕ → ℕ}

theorem val_copyBodyT {E : List ℕ} (har : Val w E arT ar) (hq : Val w E qT q) (hfw : Val w E fwT fw)
    (hn : Cross.Exact.FVal w nodes E Nd) (hξ : Val w E ξ Ξ) (hp : Val w E p P) (hu : Val w E u U) :
    Val w E (copyBodyT arT qT fwT nodes ξ p u) (ind (CopyOk ar q fw Nd Ξ P U)) := by
  have hN : Val w E (nodes p) (Nd P) := (hn [] p P hp.toExact).toNum
  have hs := (val_sliceT har.toExact hq.toExact hfw.toExact hn hξ.toExact hp.toExact).toNum
  have hb := (val_budT har.toExact hq.toExact hfw.toExact hN.toExact hu.toExact).toNum
  have hW := val_codeWidthT hb
  have hf := val_fldT har hq hfw hN hs hu
  refine (val_ite (val_eqT hu hN) (val_const 1)
      (val_ite (val_eqT (val_validT hb hW hf) (val_const 1))
    (val_eqT (val_labelWtT hW hf) hb) (val_const 0))).congr ?_
  unfold CopyOk ind
  split_ifs <;> simp_all

theorem val_copyOuter (har : Val w env arT ar) (hq : Val w env qT q) (hfw : Val w env fwT fw)
    (hn : Cross.Exact.FVal w nodes env Nd) (hξ : Val w env ξ Ξ) (pre : List ℕ) (x k : ℕ) :
    Val w (x :: k :: (pre ++ env)) (ite (lt (nodes (lvl (pre ++ env).length)) qT)
      (everyE qT fun u => copyBodyT arT qT fwT nodes ξ (lvl (pre ++ env).length) u) (const 1))
      (ind (Nd k < q → ∀ u < q, CopyOk ar q fw Nd Ξ k u)) := by
  have hE : ∀ {t : Term} {v : ℕ}, Val w env t v → Val w (x :: k :: (pre ++ env)) t v :=
    fun h => h.ext (x :: k :: pre)
  have hp := val_idx (w := w) (pre ++ env) x k
  have hN : Val w (x :: k :: (pre ++ env)) (nodes (lvl (pre ++ env).length)) (Nd k) :=
    (hn (x :: k :: pre) _ k hp.toExact).toNum
  refine (val_ite (val_lt hN (hE hq)) (val_everyE (P := fun u => CopyOk ar q fw Nd Ξ k u) (hE hq)
    fun pre' x' k' _ => ?_) (val_const 1)).congr ?_
  · have hE' : ∀ {t : Term} {v : ℕ}, Val w (x :: k :: (pre ++ env)) t v →
        Val w (x' :: k' :: (pre' ++ x :: k :: (pre ++ env))) t
            v := fun h => h.ext (x' :: k' :: pre')
    exact val_copyBodyT (hE' (hE har)) (hE' (hE hq)) (hE' (hE hfw))
      (fun pre'' t v ht => by
        have := hn (pre'' ++ x' :: k' :: pre' ++ x :: k :: pre) t v
            (by simpa [List.append_assoc] using ht)
        simpa [List.append_assoc] using this) (hE' (hE hξ)) (hE' hp) (val_idx _ x' k')
  · unfold ind; split_ifs <;> simp_all

theorem val_copiesOkT (har : Val w env arT ar) (hq : Val w env qT q) (hfw : Val w env fwT fw)
    (hg : Val w env gT g) (hn : Cross.Exact.FVal w nodes env Nd) (hξ : Val w env ξ Ξ) :
    Val w env (copiesOkT arT qT fwT gT nodes ξ) (ind (copiesOkN ar q fw g Nd Ξ)) := by
  refine (val_everyE (P := fun p => Nd p < q → ∀ u < q, CopyOk ar q fw Nd Ξ p u) hg
    fun pre x k _ => val_copyOuter har hq hfw hn hξ pre x k).congr ?_
  unfold copiesOkN ind
  congr 1

theorem tm_copyBodyT {E : List ℕ} {dp du dn : ℕ} (har : Val w E arT ar) (hq : Val w E qT q)
    (hfw : Val w E fwT fw) (hn : Cross.Exact.FVal w nodes E Nd) (hξ : Val w E ξ Ξ)
        (hp : Val w E p P)
    (hu : Val w E u U) (tA : Tm w L 32 arT E) (tq : Tm w L 1 qT E) (tfw : Tm w L 1 fwT E)
    (tn : TmF w L nodes dp dn E) (tξ : Tm w L 1 ξ E) (tp : Tm w L dp p E) (tu : Tm w L du u E)
    (hdp : dp + 5 ≤ 20) (hdn : dn ≤ 20) (hdu : du ≤ 20) (hL : 16 ≤ L) (hfwL : fw < L)
    (hW : ∀ a b, codeWidth (budgetN ar q fw a b) ≤ L) (hS : argWidN ar q fw (Nd P) < L) :
    Tm w L 1 (copyBodyT arT qT fwT nodes ξ p u) E := by
  have inp := inp_dummy har hq hfw
  have tie := tiers_dummy tA tq tfw hL hfwL
  have hN : Val w E (nodes p) (Nd P) := (hn [] p P hp.toExact).toNum
  have tN := tn.app (Ext.refl E) tp
  have hs := (val_sliceT har.toExact hq.toExact hfw.toExact hn hξ.toExact hp.toExact).toNum
  have ts := tm_sliceT inp tie hn tn (by omega) tξ (by norm_num) tp hp.toExact (by omega) hS
  obtain ⟨tb, tW, tf⟩ := tm_fld har hq hfw hN hs hu tA tq tfw tN ts tu (by omega) hdu (by norm_num)
    hL hfwL (hW _ _)
  have hb := (val_budT har.toExact hq.toExact hfw.toExact hN.toExact hu.toExact).toNum
  have hWv := val_codeWidthT hb
  have hf := val_fldT har hq hfw hN hs hu
  have tval := tm_validT hb hWv hf tb tW tf (by norm_num) (by omega) (hW _ _)
  have tlw := tm_labelWtT hWv hf tW tf (by omega) (hW _ _)
  have t1 : Tm w L 1 (const 1) E := t_one (by omega)
  have t0 : Tm w L 1 (const 0) E := t_const (by positivity)
  exact (t_ite (t_eqT' tu tN (by omega)) t1 (t_ite (t_eqT' tval t1 (by omega))
    (t_eqT' tlw tb (by omega)) t0)).mono (by omega)

theorem tm_copiesOkT {dn : ℕ} (har : Val w env arT ar) (hq : Val w env qT q)
    (hfw : Val w env fwT fw)
    (hg : Val w env gT g) (hn : Cross.Exact.FVal w nodes env Nd) (hξ : Val w env ξ Ξ)
    (tA : Tm w L 32 arT env) (tq : Tm w L 1 qT env) (tfw : Tm w L 1 fwT env) (tg : Tm w L 1 gT env)
    (tn : TmF w L nodes 1 dn env) (tξ : Tm w L 1 ξ env) (hdn : dn ≤ 20) (hL : 16 ≤ L)
    (hfwL : fw < L) (hW : ∀ a b, codeWidth (budgetN ar q fw a b) ≤ L)
    (hS : ∀ p < g, argWidN ar q fw (Nd p) < L) :
    Tm w L 1 (copiesOkT arT qT fwT gT nodes ξ) env := by
  have hq1 : q < 2 ^ (1 * L) := by have h1 := (tq [] Small.nil).2; rwa [List.nil_append, hq.2] at h1
  refine tm_everyE hg tg le_rfl (by norm_num)
      (fun pre x k _ => val_copyOuter har hq hfw hn hξ pre x k)
    (fun pre x k _ hk hx he => ?_) (by omega)
  have hg1 : g < 2 ^ (1 * L) := by have h1 := (tg [] Small.nil).2; rwa [List.nil_append, hg.2] at h1
  have tp : Tm w L 1 (lvl (pre ++ env).length) (x :: k :: (pre ++ env)) := tm_idx (by omega)
  have hE : ∀ {t : Term} {v : ℕ}, Val w env t v → Val w (x :: k :: (pre ++ env)) t v :=
    fun h => h.ext (x :: k :: pre)
  have hp := val_idx (w := w) (pre ++ env) x k
  have tN := tn.app he tp
  refine (t_ite (t_lt tN (tq.ext he) (by omega)) (tm_everyE (P := fun u => CopyOk ar q fw Nd Ξ k u)
    (hE hq) (tq.ext he) le_rfl (by norm_num)
    (fun pre' x' k' _ => ?_) (fun pre' x' k' _ hk' _ he' => ?_) (by omega)) (t_one (by omega))).mono
    (by omega)
  · have hE' : ∀ {t : Term} {v : ℕ}, Val w (x :: k :: (pre ++ env)) t v →
        Val w (x' :: k' :: (pre' ++ x :: k :: (pre ++ env))) t
            v := fun h => h.ext (x' :: k' :: pre')
    exact val_copyBodyT (hE' (hE har)) (hE' (hE hq)) (hE' (hE hfw))
      (fun pre'' t v ht => by
        have := hn (pre'' ++ x' :: k' :: pre' ++ x :: k :: pre) t v
            (by simpa [List.append_assoc] using ht)
        simpa [List.append_assoc] using this) (hE' (hE hξ)) (hE' hp) (val_idx _ x' k')
  · have hE' : ∀ {t : Term} {v : ℕ}, Val w (x :: k :: (pre ++ env)) t v →
        Val w (x' :: k' :: (pre' ++ x :: k :: (pre ++ env))) t
            v := fun h => h.ext (x' :: k' :: pre')
    have he2 := he'.trans he
    exact tm_copyBodyT (hE' (hE har)) (hE' (hE hq)) (hE' (hE hfw))
      (fun pre'' t v ht => by
        have := hn (pre'' ++ x' :: k' :: pre' ++ x :: k :: pre) t v
            (by simpa [List.append_assoc] using ht)
        simpa [List.append_assoc] using this) (hE' (hE hξ)) (hE' hp) (val_idx _ x' k')
      (tA.ext he2) (tq.ext he2) (tfw.ext he2) (tn.ext he2) (tξ.ext he2) (tp.ext he')
      (tm_idx (d := 1) (by omega)) (by norm_num) hdn (by norm_num) hL hfwL hW (hS k hk)

/-! ### Validity of the arguments -/

/-- **The packed labels of an argument code are valid** (`argsOkN`), as `0`/`1`. -/
def argsOkT (B fwT arT qT Lt v x : Term) : Term :=
  everyE qT fun u => labOkT B Lt (argLabT arT qT fwT v x u)

theorem val_argsOkT {B fwT arT qT Lt v x : Term} {Bv fw ar q Lv V X : ℕ} (hB : Val w env B Bv)
    (hfw : Val w env fwT fw) (har : Val w env arT ar) (hq : Val w env qT q) (hLt : Val w env Lt Lv)
    (hv : Val w env v V) (hx : Val w env x X) :
    Val w env (argsOkT B fwT arT qT Lt v x) (ind (argsOkN Bv fw ar q Lv V X)) :=
  (val_everyE (test := fun u => labOkT B Lt (argLabT arT qT fwT v x u))
    (P := fun u => labOkN Bv Lv (argLabN ar q fw V X u)) hq fun pre y k _ =>
    val_labOkT (hB.ext (y :: k :: pre)) (hLt.ext (y :: k :: pre))
        (val_argLabT (har.ext (y :: k :: pre))
      (hq.ext (y :: k :: pre)) (hfw.ext (y :: k :: pre)) (hv.ext (y :: k :: pre))
          (hx.ext (y :: k :: pre))
      (val_idx _ y k))).congr (by unfold argsOkN; rfl)

theorem tm_argsOkT {B fwT arT qT Lt v x : Term} {Bv fw ar q Lv V X dLt : ℕ} (hB : Val w env B Bv)
    (hfw : Val w env fwT fw) (har : Val w env arT ar) (hq : Val w env qT q) (hLt : Val w env Lt Lv)
    (hv : Val w env v V) (hx : Val w env x X) (tB : Tm w L 1 B env) (tfw : Tm w L 1 fwT env)
    (tA : Tm w L 32 arT env) (tq : Tm w L 1 qT env) (tLt : Tm w L dLt Lt env) (tv : Tm w L 1 v env)
    (tx : Tm w L 32 x env) (hL : 16 ≤ L) (hfwL : fw < L) (hBL : Bv ≤ L)
    (hW : ∀ a b, codeWidth (budgetN ar q fw a b) ≤ L) :
    Tm w L 1 (argsOkT B fwT arT qT Lt v x) env := by
  have hq1 : q < 2 ^ (1 * L) := by have h1 := (tq [] Small.nil).2; rwa [List.nil_append, hq.2] at h1
  refine tm_everyE (test := fun u => labOkT B Lt (argLabT arT qT fwT v x u))
    (P := fun u => labOkN Bv Lv (argLabN ar q fw V X u)) hq tq le_rfl (by norm_num)
    (fun pre y k _ => val_labOkT (hB.ext (y :: k :: pre)) (hLt.ext (y :: k :: pre))
      (val_argLabT (har.ext (y :: k :: pre)) (hq.ext (y :: k :: pre)) (hfw.ext (y :: k :: pre))
        (hv.ext (y :: k :: pre)) (hx.ext (y :: k :: pre)) (val_idx _ y k)))
    (fun pre y k _ hk _ he => ?_) (by omega)
  have hE : ∀ {t : Term} {n : ℕ}, Val w env t n → Val w (y :: k :: (pre ++ env)) t n :=
    fun h => h.ext (y :: k :: pre)
  exact tm_labOkT (hE hB) (hE hLt) (val_argLabT (hE har) (hE hq) (hE hfw) (hE hv) (hE hx)
      (val_idx _ y k))
    (tB.ext he) (tLt.ext he) (tm_argLabT (hE har) (hE hq) (hE hfw) (hE hv) (hE hx) (val_idx _ y k)
      (tA.ext he) (tq.ext he) (tfw.ext he) (tv.ext he) (tx.ext he) (tm_idx (d := 1) (by omega))
      (by norm_num) (by norm_num) le_rfl hL hfwL (hW _ _)) (by omega) hBL

end Copies

/-! ### Conditional branches and long list codes -/

theorem lit16 {k : ℕ} (hk : k < 16) (hL : 4 ≤ L) : k < 2 ^ L :=
  lt_of_lt_of_le (hk.trans_le (by norm_num : 16 ≤ 2 ^ 4)) (Nat.pow_le_pow_right (by norm_num) hL)

/-- An `ite` needs the tier of the branch it takes only. -/
theorem tm_ite2v {c t e : Term} {C dc d : ℕ} (hc : Val w env c C) (tc : Tm w L dc c env)
    (ht : 0 < C → Tm w L d t env) (he : C = 0 → Tm w L d e env) : Tm w L d (ite c t e) env := by
  by_cases h : 0 < C
  · have htm := ht h
    intro pre hp
    have hcv : 0 < c.denote w (pre ++ env) := by rw [(hc.ext pre).2]; exact h
    refine ⟨⟨(tc pre hp).1, ?_⟩, ?_⟩
    · exact (ite_eq_left (show 0 < ProgLang.Prog.eval w (c (pre ++ env).length)
        (pre ++ env) from hcv)).symm ▸
        (htm pre hp).1
    · simp only [denote_ite, ite_eq_left hcv]; exact (htm pre hp).2
  · have htm := he (by omega)
    intro pre hp
    have hcv : ¬ 0 < c.denote w (pre ++ env) := by rw [(hc.ext pre).2]; exact h
    refine ⟨⟨(tc pre hp).1, ?_⟩, ?_⟩
    · exact (ite_eq_right (show ¬ 0 < ProgLang.Prog.eval w (c (pre ++ env).length)
        (pre ++ env) from hcv)).symm ▸
        (htm pre hp).1
    · simp only [denote_ite, ite_eq_right hcv]; exact (htm pre hp).2

/-- The tier of a cons with a small head, from a bound on its value. -/
theorem tm_consE' {x l : Term} {X Lc dx dl d : ℕ} (hx : Val w env x X) (hl : Val w env l Lc)
    (tx : Tm w L dx x env) (tl : Tm w L dl l env) (hdx1 : 1 ≤ dx) (hdx : dx ≤ 15)
    (hd : 2 * dx + dl + 3 ≤ 128) (hL : 2 ≤ L) (hv : consF X Lc < 2 ^ (d * L)) :
    Tm w L d (consE x l) env := by
  have hs := val_sizeE hx
  have ts := tm_sizeE hx tx hdx1 (by omega) (by omega)
  have hX : X < 2 ^ (dx * L) := by have h1 := (tx [] Small.nil).2; rwa [List.nil_append, hx.2] at h1
  have hsz := size_lt_tier hX
  have one : ∀ {E : List ℕ}, Tm w L 1 (const 1) E := t_one (by omega)
  have e1 : dx * L + 1 < (dx + 1) * L := by nlinarith
  have e2 : 2 * (dx * L) + 1 < (2 * dx + 1) * L := by nlinarith
  have p0 := t_pow2v (d := dx + 1) hs ts (by omega) (by omega) (by omega) hL
  have p1 := t_pow2v (d := dx + 1) (val_add hs (val_const 1)) (t_add ts one (by omega) (by omega))
    (by omega) (by omega) (by omega) hL
  have p2 := t_pow2v (d := 2 * dx + 1) (val_add (val_add hs hs) (val_const 1))
    (t_add (t_add ts ts (by omega) (by omega)) one (by omega) (by omega)) (by omega) (by omega)
    (by omega) hL
  exact tm_val (t_add (t_add (t_sub p0 one) (t_mul p1 tx (by omega)) (by omega) (by omega))
    (t_mul p2 tl (by omega)) (by omega) (by omega)) (val_consE hx hl) hv

/-- **The tier of a list code** with entries of tier at most `15`, from a bound on its value
(`d ≤ 90`). -/
theorem tm_encE' {d : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ 90) (hL : 2 ≤ L) : ∀ {ts : List Term}
    {vs : List ℕ},
    List.Forall₂ (fun t v => Val w env t v ∧ ∃ dt, 1 ≤ dt ∧ dt ≤ 15 ∧ Tm w L dt t env) ts vs →
    NatList.enc vs < 2 ^ (d * L) → Tm w L d (encE ts) env
  | [], [], _, _ => ((t_one (by omega) : Tm w L 1 (const 1) env)).mono hd1
  | _ :: _, v :: vs, List.Forall₂.cons ⟨hv, _, h1, h2, ht⟩ hs, hlt => by
    have hl := val_encE (List.Forall₂.imp (fun _ _ h => h.1) hs)
    have hlt' : NatList.enc vs < 2 ^ (d * L) := (NatList.enc_le_enc_cons v vs).trans_lt hlt
    rw [encE]
    exact tm_consE' hv hl ht (tm_encE' hd1 hd hL hs hlt') h1 h2 (by omega) hL
      (by rw [consF_enc]; exact hlt)

/-! ### Fields of state codes -/

/-- The node count of the first clique of a cache term. -/
def cQT (c : Term) : Term := stGetT (stGetT c 0) 0
/-- The budget array of the first clique of a cache term. -/
def cAT (c : Term) : Term := stGetT (stGetT c 0) 1
/-- The node count of the second clique of a cache term. -/
def pQT (c : Term) : Term := stGetT (stGetT c 1) 0
/-- The budget array of the second clique of a cache term. -/
def pAT (c : Term) : Term := stGetT (stGetT c 1) 1

section CacheT

variable {c : Term} {cv : ℕ}

theorem val_cQT (hc : Val w env c cv) : Val w env (cQT c) (cQ cv) := val_stGetT (val_stGetT hc 0) 0
theorem val_cAT (hc : Val w env c cv) : Val w env (cAT c) (cA cv) := val_stGetT (val_stGetT hc 0) 1
theorem val_pQT (hc : Val w env c cv) : Val w env (pQT c) (pQ cv) := val_stGetT (val_stGetT hc 1) 0
theorem val_pAT (hc : Val w env c cv) : Val w env (pAT c) (pA cv) := val_stGetT (val_stGetT hc 1) 1

theorem tm_cache (S : Setup) (chs : List ℕ) (hc : Val w env c (S.cacheC chs)) (tc : Tm w L 1 c env)
    (hL : 2 ≤ L) : Tm w L 1 (cQT c) env ∧ Tm w L 1 (cAT c) env := by
  have h0 : Val w env (stGetT c 0) (NatList.enc [(S.clique chs).q,
      arrN (S.clique chs).q S.fw (extN (S.clique chs).a)]) := by
    have := val_stGetT hc 0; rwa [stGet_cacheC] at this
  have t0 := tm_stGetT (l := S.cacheL chs) hc tc le_rfl (by norm_num) hL 0
      (by cases chs <;> simp [Setup.cacheL])
  exact ⟨tm_stGetT h0 t0 le_rfl (by norm_num) hL 0 (by simp),
    tm_stGetT h0 t0 le_rfl (by norm_num) hL 1 (by simp)⟩

theorem tm_pcache (S : Setup) (i : ℕ) (rest : List ℕ) (hc : Val w env c (S.cacheC (i :: rest)))
    (tc : Tm w L 1 c env) (hL : 2 ≤ L) : Tm w L 1 (pQT c) env ∧ Tm w L 1 (pAT c) env := by
  have h1 : Val w env (stGetT c 1) (NatList.enc [(S.clique rest).q,
      arrN (S.clique rest).q S.fw (extN (S.clique rest).a)]) := by
    have := val_stGetT hc 1
    have e : stGet (S.cacheC (i :: rest)) 1 = stGet (S.cacheC rest) 0 := by
      simp [Setup.cacheC, Setup.cacheL]
    rwa [e, stGet_cacheC] at this
  have t1 := tm_stGetT (l := S.cacheL (i :: rest)) hc tc le_rfl (by norm_num) hL 1
    (by cases rest <;> simp [Setup.cacheL])
  exact ⟨tm_stGetT h1 t1 le_rfl (by norm_num) hL 0 (by simp),
    tm_stGetT h1 t1 le_rfl (by norm_num) hL 1 (by simp)⟩

end CacheT

/-- **The bundled hypotheses on the inputs**: the terms `nT`, `fwT`, `BT` have the values of the
state code, the field width and the fuel, all three are below `2^L` (so every field of the state
code is), and the sizes are compatible: `16 ≤ L`, `fw < L`, `w(Φ₀ / 2^e) + 2 ≤ B ≤ L` for the
exponent `e` of `2K = 2^(2^e)`. -/
structure EIn (S : Setup) (w : List Bool) (L : ℕ) (env : List ℕ) (nT fwT BT : Term) (st : St)
    (B : ℕ) : Prop where
  vn : Val w env nT (S.code st)
  vfw : Val w env fwT S.fw
  vB : Val w env BT B
  tn : Tm w L 1 nT env
  tfw : Tm w L 1 fwT env
  tB : Tm w L 1 BT env
  hL : 16 ≤ L
  hfw : S.fw < L
  hBL : B ≤ L
  hB : ∃ e, 2 * S.K = 2 ^ 2 ^ e ∧ codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B
  hS : S.Good

/-- The digit bound for the budget array of a clique on a valid path, under `EIn`. -/
theorem EIn.codeWidth_budgetN {S : Setup} {nT fwT BT : Term} {st : St} {B : ℕ}
    (h : EIn S w L env nT fwT BT st B) {chs : List ℕ} (hp : S.PathOK chs) (a b : ℕ) :
    codeWidth (budgetN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw a
        b) ≤ B :=
  let ⟨_, he, hB⟩ := h.hB
  codeWidth_budgetN_path S h.hS hp he hB a b

theorem EIn.field {S : Setup} {nT fwT BT : Term} {st : St} {B : ℕ} {l : List ℕ}
    (h : EIn S w L env nT fwT BT st B) (hl : S.code st = NatList.enc l) (k : ℕ) (hk : k < l.length)
        :
    Val w env (stGetT nT k) (l.getD k 0) ∧ Tm w L 1 (stGetT nT k) env := by
  have hv := h.vn; rw [hl] at hv
  refine ⟨(val_stGetT hv k).congr ?_, tm_stGetT hv h.tn le_rfl (by norm_num)
      (by have := h.hL; omega) k hk⟩
  clear hv hl
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k => simp only [stGet_cons_succ, List.getD_cons_succ]; exact ih k (by simpa using hk)

/-! ### Last labels and clique tags and widths -/

/-- The child `b` of `last chs i` (`lastChildN`). -/
def lastChildT (nT b : Term) : Term := encE [const 4, stGetT nT 1, stGetT nT 2, b, stGetT nT 3]

theorem val_lastChildT {nT b : Term} {n bv : ℕ} (hn : Val w env nT n) (hb : Val w env b bv) :
    Val w env (lastChildT nT b) (lastChildN n bv) :=
  val_encE (.cons (val_const 4) (.cons (val_stGetT hn 1) (.cons (val_stGetT hn 2) (.cons hb
    (.cons (val_stGetT hn 3) .nil)))))

/-- The tag of a clique state (`clTagN`). -/
def clTagT (nT : Term) : Term :=
  ite (eqT (cQT (stGetT nT 2)) (const 2)) (const 1)
    (ite (lt (const 3) (cQT (stGetT nT 2)))
      (eqT (cQT (stGetT nT 2)) (mul (sqrtT (cQT (stGetT nT 2))) (sqrtT (cQT (stGetT nT 2)))))
          (const 0))

theorem val_clTagT {nT : Term} {n : ℕ} (hn : Val w env nT n) : Val w env (clTagT nT)
    (clTagN n) := by
  have hq := val_cQT (val_stGetT hn 2)
  have hs := val_sqrtT hq
  rw [sqrtN_eq] at hs
  refine (val_ite (val_eqT hq (val_const 2)) (val_const 1) (val_ite (val_lt (val_const 3) hq)
    (val_eqT hq (val_mul hs hs)) (val_const 0))).congr ?_
  unfold clTagN
  generalize cQ (stGet n 2) = q
  generalize Nat.sqrt q = r
  split_ifs <;> omega

theorem tm_clTagT {nT : Term} {n : ℕ} (hn : Val w env nT n) (tq : Tm w L 1 (cQT (stGetT nT 2)) env)
    (hL : 4 ≤ L) : Tm w L 1 (clTagT nT) env := by
  have hq := val_cQT (val_stGetT hn 2)
  have ts := tm_sqrtT hq tq (by norm_num) hL
  have t0 : Tm w L 1 (const 0) env := t_const (by positivity)
  exact (t_ite (t_eqT' tq (t_small (by norm_num) (by omega)) (by omega)) (t_one (by omega))
    (t_ite (t_lt (t_small (by norm_num) (by omega)) tq (by omega))
      (t_eqT' tq (t_mul ts ts (by norm_num)) (by omega)) t0)).mono (by omega)

/-- The width of a clique state (`clWidthN`). -/
def clWidthT (fwT nT : Term) : Term :=
  ite (eqT (cQT (stGetT nT 2)) (const 2))
    (codeWidthT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0) (const 1)))
    (choiceWidthT (sqrtT (cQT (stGetT nT 2))) fwT)

theorem val_clWidthT {nT fwT : Term} {n fw : ℕ} (hn : Val w env nT n) (hfw : Val w env fwT fw) :
    Val w env (clWidthT fwT nT) (clWidthN fw n) := by
  have hq := val_cQT (val_stGetT hn 2)
  have hA := val_cAT (val_stGetT hn 2)
  have hs := val_sqrtT hq
  rw [sqrtN_eq] at hs
  refine (val_ite (val_eqT hq (val_const 2))
      (val_codeWidthT (val_budT hA.toExact hq.toExact hfw.toExact
    (Cross.Exact.val_const 0 env) (Cross.Exact.val_const 1 env)).toNum)
    (val_choiceWidthT hs.toExact hfw.toExact).toNum).congr ?_
  unfold clWidthN
  split_ifs <;> simp_all

theorem tm_clWidthT {nT fwT : Term} {n fw : ℕ} (hn : Val w env nT n) (hfw : Val w env fwT fw)
    (tq : Tm w L 1 (cQT (stGetT nT 2)) env) (tA : Tm w L 1 (cAT (stGetT nT 2)) env)
    (tfw : Tm w L 1 fwT env) (hL : 16 ≤ L) (hfwL : fw < L) : Tm w L 7 (clWidthT fwT nT) env := by
  have hq := val_cQT (val_stGetT hn 2)
  have hA := val_cAT (val_stGetT hn 2)
  have tie := tiers_dummy (tA.mono (by norm_num)) tq tfw hL hfwL
  have hb := (val_budT hA.toExact hq.toExact hfw.toExact (Cross.Exact.val_const 0 env)
    (Cross.Exact.val_const 1 env)).toNum
  have t0 : Tm w L 1 (const 0) env := t_const (by positivity)
  have tb := tm_budT tie hfw.toExact t0 (t_one (by omega)) (by norm_num)
  have ts := tm_sqrtT hq tq (by norm_num) (by omega)
  exact (t_ite (t_eqT' tq (t_small (by norm_num) (by omega)) (by omega))
    ((tm_codeWidthT hb tb (by norm_num) (by omega)).mono (d' := 7) (by norm_num))
    (tm_choiceWidthT ts tfw hL)).mono (by omega)

/-! ### Entry tags and widths -/

/-- The tag of an entry (`entTagN`). -/
def entTagT (BT fwT nT : Term) : Term :=
  ite (eqT (stGetT nT 1) (const 1)) (const 2)
    (ite (eqT (pQT (stGetT nT 2)) (mul (sqrtT (pQT (stGetT nT 2))) (sqrtT (pQT (stGetT nT 2)))))
      (argsOkT BT fwT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) (packLT (sqrtT (pQT (stGetT nT 2))))
        (stGetT nT 3) (stGetT nT 4)) (const 0))

/-- The width of an entry (`entWidthN`). -/
def entWidthT (fwT nT : Term) : Term :=
  ite (eqT (stGetT nT 1) (const 1)) (const 0)
    (ite (eqT (pQT (stGetT nT 2)) (mul (sqrtT (pQT (stGetT nT 2))) (sqrtT (pQT (stGetT nT 2)))))
      (xiWidT (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
        (stGetT (stGetT nT 1) 0) (stGetT nT 3)) (const 0))

section EntTag

variable {nT fwT BT : Term} {n fw Bv : ℕ}

theorem val_entTagT (hn : Val w env nT n) (hfw : Val w env fwT fw) (hB : Val w env BT Bv) :
    Val w env (entTagT BT fwT nT) (entTagN Bv fw n) := by
  have c := val_stGetT hn 2
  have pq := val_pQT c
  have sq := val_sqrtT pq
  rw [sqrtN_eq] at sq
  have pl := (val_packLT sq.toExact).toNum
  have ok := val_argsOkT hB hfw (val_cAT c) (val_cQT c) pl (val_stGetT hn 3) (val_stGetT hn 4)
  refine (val_ite (val_eqT (val_stGetT hn 1) (val_const 1)) (val_const 2)
    (val_ite (val_eqT pq (val_mul sq sq)) ok (val_const 0))).congr ?_
  unfold entTagN ind
  generalize Nat.sqrt (pQ (stGet n 2)) = r
  split_ifs <;> simp_all

theorem val_entWidthT (hn : Val w env nT n) (hfw : Val w env fwT fw) :
    Val w env (entWidthT fwT nT) (entWidthN fw n) := by
  have c := val_stGetT hn 2
  have pq := val_pQT c
  have sq := val_sqrtT pq
  rw [sqrtN_eq] at sq
  have inp : Inp w env (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
      (stGetT (stGetT nT 1) 0) (pA (stGet n 2)) (pQ (stGet n 2)) fw (Nat.sqrt (pQ (stGet n 2)))
      (stGet (stGet n 1) 0) :=
    ⟨(val_pAT c).toExact, pq.toExact, hfw.toExact, sq.toExact,
        (val_stGetT (val_stGetT hn 1) 0).toExact⟩
  refine (val_ite (val_eqT (val_stGetT hn 1) (val_const 1)) (val_const 0)
    (val_ite (val_eqT pq (val_mul sq sq)) (val_xiWidT inp (val_stGetT hn 3).toExact).toNum
      (val_const 0))).congr ?_
  unfold entWidthN
  generalize Nat.sqrt (pQ (stGet n 2)) = r
  split_ifs <;> simp_all

variable {S : Setup} {chs : List ℕ} {v args B : ℕ}

theorem EIn.fields_ent (h : EIn S w L env nT fwT BT (.ent chs v args) B) :
    (Val w env (stGetT nT 1) (NatList.enc chs) ∧ Tm w L 1 (stGetT nT 1) env) ∧
    (Val w env (stGetT nT 2) (S.cacheC chs) ∧ Tm w L 1 (stGetT nT 2) env) ∧
    (Val w env (stGetT nT 3) v ∧ Tm w L 1 (stGetT nT 3) env) ∧
    (Val w env (stGetT nT 4) args ∧ Tm w L 1 (stGetT nT 4) env) :=
  ⟨h.field (code_ent S chs v args) 1 (by simp), h.field (code_ent S chs v args) 2 (by simp),
    h.field (code_ent S chs v args) 3 (by simp), h.field (code_ent S chs v args) 4 (by simp)⟩

theorem tm_entTagT (h : EIn S w L env nT fwT BT (.ent chs v args) B) (hp : S.PathOK chs) :
    Tm w L 1 (entTagT BT fwT nT) env := by
  have hL := h.hL
  obtain ⟨⟨v1, t1⟩, ⟨vc, tc⟩, ⟨vv, tv⟩, ⟨vx, tx⟩⟩ := h.fields_ent
  have one : Tm w L 1 (const 1) env := t_one (by omega)
  refine tm_ite2v (val_eqT v1 (val_const 1)) (t_eqT' t1 one (by omega))
    (fun _ => t_small (by norm_num) (by omega)) (fun h0 => ?_)
  cases chs with
  | nil => simp at h0
  | cons i rest =>
    have hpq := val_pQT vc
    have hsq := val_sqrtT hpq
    rw [sqrtN_eq, pQ_eq] at hsq
    rw [pQ_eq] at hpq
    obtain ⟨tq, tA⟩ := tm_pcache S i rest vc tc (by omega)
    obtain ⟨tcq, tcA⟩ := tm_cache S (i :: rest) vc tc (by omega)
    have ts := tm_sqrtT hpq tq (by norm_num) (by omega)
    obtain ⟨-, -, hsq', -⟩ := id hp
    refine tm_ite2v (val_eqT hpq (val_mul hsq hsq))
        (t_eqT' tq (t_mul ts ts (by norm_num)) (by omega))
      (fun _ => ?_) (fun h1 => by simp [← hsq'] at h1)
    have vA := val_cAT vc
    have vq := val_cQT vc
    rw [cA_eq] at vA
    rw [cQ_eq] at vq
    exact tm_argsOkT h.vB h.vfw vA vq (val_packLT hsq.toExact).toNum vv vx h.tB h.tfw
        (tcA.mono (by norm_num))
      tcq (tm_packLT ts hL) tv (tx.mono (by norm_num)) hL h.hfw h.hBL
      (fun a b => (h.codeWidth_budgetN hp a b).trans h.hBL)

theorem tm_entWidthT (h : EIn S w L env nT fwT BT (.ent chs v args) B) (hp : S.PathOK chs) :
    Tm w L 6 (entWidthT fwT nT) env := by
  have hL := h.hL
  obtain ⟨⟨v1, t1⟩, ⟨vc, tc⟩, ⟨vv, tv⟩, -⟩ := h.fields_ent
  have one : Tm w L 1 (const 1) env := t_one (by omega)
  refine tm_ite2v (val_eqT v1 (val_const 1)) (t_eqT' t1 one (by omega))
    (fun _ => (t_const (k := 0) (by positivity)).mono (by norm_num)) (fun h0 => ?_)
  cases chs with
  | nil => simp at h0
  | cons i rest =>
    have hpq := val_pQT vc
    have hsq := val_sqrtT hpq
    rw [sqrtN_eq, pQ_eq] at hsq
    rw [pQ_eq] at hpq
    obtain ⟨tq, tA⟩ := tm_pcache S i rest vc tc (by omega)
    have ts := tm_sqrtT hpq tq (by norm_num) (by omega)
    obtain ⟨-, h4, hsq', -⟩ := hp
    have vi := val_stGetT v1 0
    have ti := tm_stGetT v1 t1 le_rfl (by norm_num) (by omega) 0 (by simp)
    have vA := val_pAT vc
    rw [pA_eq] at vA
    have inp : Inp w env (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
        (stGetT (stGetT nT 1) 0) _ _ S.fw _ _ :=
            ⟨vA.toExact, hpq.toExact, h.vfw.toExact, hsq.toExact, vi.toExact⟩
    have tie : Tiers w L env (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
        (stGetT (stGetT nT 1) 0) S.fw (Nat.sqrt (S.clique rest).q) :=
      ⟨tA.mono (by norm_num), tq, h.tfw, ts, ti.mono (by norm_num), hL, h.hfw,
        Nat.sqrt_pos.mpr (by omega)⟩
    exact tm_ite2v (val_eqT hpq (val_mul hsq hsq))
        (t_eqT' tq (t_mul ts ts (by norm_num)) (by omega))
      (fun _ => tm_xiWidT inp tie tv) (fun h1 => by simp [← hsq'] at h1)

end EntTag

/-! ### The children of clique states and last labels -/

/-- The code of the leaf `0`. -/
def zeroCT : Term := encE [const 0]

/-- The child of a clique state (`clChildN`). -/
def clChildT (fwT nT iT : Term) : Term :=
  ite (eqT (cQT (stGetT nT 2)) (const 2))
    (ite (ite (eqT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0) (const 1)) (const 0))
        (eqT iT (const 0))
        (ite (eqT (validT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0) (const 1))
            (codeWidthT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0) (const 1)))
            (mod iT (pow2 (codeWidthT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0)
                (const 1))))))
            (const 1))
          (eqT (labelWtT (codeWidthT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0)
              (const 1)))
            (mod iT (pow2 (codeWidthT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0)
                (const 1))))))
            (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (const 0) (const 1)))
          (const 0)))
      (encE [const 3, stGetT nT 1, stGetT nT 2, iT]) zeroCT)
    (ite (eqT (cQT (stGetT nT 2)) (mul (sqrtT (cQT (stGetT nT 2))) (sqrtT (cQT (stGetT nT 2)))))
      (ite (choiceValidT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (sqrtT (cQT (stGetT nT 2))) iT)
        (encE [const 2, consE iT (stGetT nT 1),
          consE (encE [sqrtT (cQT (stGetT nT 2)),
            childT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (sqrtT (cQT (stGetT nT 2))) iT])
            (stGetT nT 2)]) zeroCT) zeroCT)

theorem val_clChildT {nT fwT iT : Term} {n fw i : ℕ} (hn : Val w env nT n) (hfw : Val w env fwT fw)
    (hi : Val w env iT i) : Val w env (clChildT fwT nT iT) (clChildN fw n i) := by
  have c := val_stGetT hn 2
  have q := val_cQT c
  have A := val_cAT c
  have b := (val_budT A.toExact q.toExact hfw.toExact (Cross.Exact.val_const 0 env)
    (Cross.Exact.val_const 1 env)).toNum
  have W := val_codeWidthT b
  have j := val_mod hi (val_pow2 W)
  have sq := val_sqrtT q
  rw [sqrtN_eq] at sq
  have inp : Inp w env (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (sqrtT (cQT (stGetT nT 2))) iT
      (cA (stGet n 2)) (cQ (stGet n 2)) fw (Nat.sqrt (cQ (stGet n 2))) i :=
    ⟨A.toExact, q.toExact, hfw.toExact, sq.toExact, hi.toExact⟩
  have code3 := val_encE (w := w) (env := env) (.cons (val_const 3) (.cons (val_stGetT hn 1)
    (.cons c (.cons hi .nil))))
  have code2 := val_encE (w := w) (env := env)
      (.cons (val_const 2) (.cons (val_consE hi (val_stGetT hn 1))
    (.cons (val_consE (val_encE (.cons sq (.cons (val_childT inp).toNum .nil))) c) .nil)))
  have z := val_encE (w := w) (env := env) (.cons (val_const 0) .nil)
  refine (val_ite (val_eqT q (val_const 2))
    (val_ite (val_ite (val_eqT b (val_const 0)) (val_eqT hi (val_const 0))
      (val_ite (val_eqT (val_validT b W j) (val_const 1)) (val_eqT (val_labelWtT W j) b)
          (val_const 0)))
      code3 z)
    (val_ite (val_eqT q (val_mul sq sq)) (val_ite (val_choiceValidT inp).toNum code2 z) z)).congr ?_
  unfold clChildN zeroC
  dsimp only
  generalize Nat.sqrt (cQ (stGet n 2)) = r
  split_ifs <;> simp_all

theorem val_lastChildT' {S : Setup} {nT bT : Term} {chs : List ℕ} {i b : ℕ}
    (hn : Val w env nT (S.code (.last chs i))) (hb : Val w env bT b) :
    Val w env (lastChildT nT bT) (S.code (S.gen.child (.last chs i) b)) :=
  (val_lastChildT hn hb).congr (lastChildN_eq S chs i b)

/-- The tier of the child of a last label, from the bound on the child code. -/
theorem tm_lastChildT {S : Setup} {nT fwT BT bT : Term} {chs : List ℕ} {i b B : ℕ}
    (h : EIn S w L env nT fwT BT (.last chs i) B) (hb : Val w env bT b) (tb : Tm w L 1 bT env)
    (hc : S.code (S.gen.child (.last chs i) b) < 2 ^ (1 * L)) : Tm w L 1 (lastChildT nT bT)
        env := by
  have hL := h.hL
  have f1 : Val w env (stGetT nT 1) (NatList.enc chs) ∧ Tm w L 1 (stGetT nT 1) env :=
    h.field (code_last S chs i) 1 (by simp)
  have f2 : Val w env (stGetT nT 2) (S.cacheC chs) ∧ Tm w L 1 (stGetT nT 2) env :=
    h.field (code_last S chs i) 2 (by simp)
  have f3 : Val w env (stGetT nT 3) i ∧ Tm w L 1 (stGetT nT 3) env := h.field (code_last S chs i) 3
      (by simp)
  have hc' : NatList.enc [4, NatList.enc chs, S.cacheC chs, b, i] < 2 ^ (1 * L) := hc
  exact tm_encE' le_rfl (by norm_num) (by omega) (.cons ⟨val_const 4, 1, le_rfl, by norm_num,
    t_const (lit16 (by norm_num) (by omega))⟩ (.cons ⟨f1.1, 1, le_rfl, by norm_num, f1.2⟩
    (.cons ⟨f2.1, 1, le_rfl, by norm_num, f2.2⟩ (.cons ⟨hb, 1, le_rfl, by norm_num, tb⟩
    (.cons ⟨f3.1, 1, le_rfl, by norm_num, f3.2⟩ .nil))))) hc'

/-! ### Factor states -/

theorem ite_pos_ind {α : Type*} (P : Prop) [Decidable P] (a b : α) :
    (if 0 < (if P then 1 else 0) then a else b) = if P then a else b := by
  by_cases h : P <;> simp [h]

/-- The code of a literal with zigzag code `z`. -/
def litCT (z : Term) : Term := encE [const 1, z]

/-- The stream of the rectangle on columns `B < B'` (`rStreamN`). -/
def rStreamT (gT B B' : Term) : Term :=
  add (add (const 1) gT) (add (sumT B fun b => sub (sub gT (const 1)) b) (sub (sub B' B) (const 1)))

/-- The quadruple index of a rectangle. -/
def quadIdxT (gT A₁ A₂ B₁ B₂ : Term) : Term := add (mul (add (mul (add (mul A₁ gT) A₂) gT) B₁) gT)
    B₂

/-- The node `A·g + B`. -/
def ndT (gT A B : Term) : Term := add (mul A gT) B

/-- The rectangle factor inside the grid (`psiN`, after the test of the quadruple). -/
def psiBodyT (BT fwT arT qT gT iT rowT v : Term) (cp : Term → Term → Term) (th : Term → Term)
    (A₁ A₂ B₁ B₂ : Term) : Term :=
  let x := quadIdxT gT A₁ A₂ B₁ B₂
  let D := digT fwT iT (mul (const 2) x)
  let Cs := digT fwT iT (add (mul (const 2) x) (const 1))
  let Q := offT fwT
  let H := diagT arT qT fwT gT x
  let mB := fun o => unpackT BT (packLT gT) (rStreamT gT B₁ B₂) (th o)
  let mA := fun o => unpackT BT (packLT gT) (rStreamT gT A₁ A₂) (th o)
  ite rowT
    (ite (eqT v A₁)
      (ite (leT (add (mul (const 2) (labelWtT BT (mB A₂))) Q) (add (mul (const 2) H) D))
        (trRootT BT true (cp B₁ (ndT gT A₂ B₂)) (cp B₂ (ndT gT A₂ B₁)) (mB A₂) (zzSubT D Cs))
            zeroCT)
      (ite (eqT v A₂)
        (ite (leT (add (mul (const 2) (labelWtT BT (mB A₁))) Q) (add (mul (const 2) H) D))
          (trRootT BT false (swapT BT (cp B₁ (ndT gT A₁ B₂))) (swapT BT (cp B₂ (ndT gT A₁ B₁)))
              (mB A₁)
            (zzSubT Cs Q)) zeroCT)
        (litCT (const 2))))
    (ite (eqT v B₁)
      (ite (leT (add D (mul (const 2) (labelWtT BT (mA B₂))))
          (add (add (mul (const 2) H) Q) (const 1)))
        (trRootT BT true (cp A₁ (ndT gT A₂ B₂)) (swapT BT (cp A₂ (ndT gT A₁ B₂))) (mA B₂)
          (zzSubT (mul (const 2) Q) (add D Cs))) zeroCT)
      (ite (eqT v B₂)
        (ite (leT (add D (mul (const 2) (labelWtT BT (mA B₁))))
            (add (add (mul (const 2) H) Q) (const 1)))
          (trRootT BT false (cp A₁ (ndT gT A₂ B₁)) (swapT BT (cp A₂ (ndT gT A₁ B₁))) (mA B₁)
            (zzSubT Cs Q)) zeroCT)
        (litCT (const 2))))

/-- **The rectangle factor** (`psiN`). -/
def psiT (BT fwT arT qT gT iT rowT v : Term) (cp : Term → Term → Term) (th : Term → Term)
    (A₁ A₂ B₁ B₂ : Term) : Term :=
  ite (lt A₁ A₂) (ite (lt B₁ B₂) (ite (lt A₂ gT) (ite (lt B₂ gT)
    (psiBodyT BT fwT arT qT gT iT rowT v cp th A₁ A₂ B₁ B₂) (litCT (const 2))) (litCT (const 2)))
    (litCT (const 2))) (litCT (const 2))

section Psi

variable {BT fwT arT qT gT iT rowT v : Term} {cp : Term → Term → Term} {th : Term → Term}
  {Bv fw ar q g i V : ℕ} {row : Bool} {CP : ℕ → ℕ → ℕ} {TH : ℕ → ℕ}

theorem val_litCT {z : Term} {Z : ℕ} (hz : Val w env z Z) : Val w env (litCT z) (litC Z) :=
  val_encE (.cons (val_const 1) (.cons hz .nil))

theorem val_zeroCT : Val w env zeroCT zeroC := val_encE (.cons (val_const 0) .nil)

theorem val_rStreamT {B B' : Term} {Bn Bn' : ℕ} (hg : Val w env gT g) (hB : Val w env B Bn)
    (hB' : Val w env B' Bn') : Val w env (rStreamT gT B B') (rStreamN g Bn Bn') :=
  val_add (val_add (val_const 1) hg) (val_add (val_sumT hB fun pre x k _ =>
    val_sub (val_sub (hg.at2 pre x k) (val_const 1)) (val_idx _ x k))
        (val_sub (val_sub hB' hB) (val_const 1)))

theorem val_psiT {A₁ A₂ B₁ B₂ : Term} {a₁ a₂ b₁ b₂ : ℕ} (hB : Val w env BT Bv)
    (h : Inp w env arT qT fwT gT iT ar q fw g i) (hrow : Val w env rowT (ind (row = true)))
    (hv : Val w env v V)
    (hcp : ∀ p u P U, Val w env p P → Val w env u U → Val w env (cp p u) (CP P U))
    (hth : ∀ o O, Val w env o O → Val w env (th o) (TH O))
    (h1 : Val w env A₁ a₁) (h2 : Val w env A₂ a₂) (h3 : Val w env B₁ b₁) (h4 : Val w env B₂ b₂) :
    Val w env (psiT BT fwT arT qT gT iT rowT v cp th A₁ A₂ B₁ B₂)
      (psiN Bv fw ar q g i row V CP TH a₁ a₂ b₁ b₂) := by
  have hg := h.vg.toNum
  have hx : Val w env (quadIdxT gT A₁ A₂ B₁ B₂) (((a₁ * g + a₂) * g + b₁) * g + b₂) :=
    val_add (val_mul (val_add (val_mul (val_add (val_mul h1 hg) h2) hg) h3) hg) h4
  have hD := (val_digT h.vfw h.vi (val_mul (val_const 2) hx).toExact).toNum
  have hC := (val_digT h.vfw h.vi (val_add (val_mul (val_const 2) hx) (val_const 1)).toExact).toNum
  have hQ := (val_offT h.vfw).toNum
  have hH := (val_diagT h hx.toExact).toNum
  have hL := (val_packLT h.vg).toNum
  have sB := val_rStreamT hg h3 h4
  have sA := val_rStreamT hg h1 h2
  have mB := fun o O (ho : Val w env o O) => val_unpackT hB hL sB (hth o O ho)
  have mA := fun o O (ho : Val w env o O) => val_unpackT hB hL sA (hth o O ho)
  have nd := fun (a b : Term) (A' B' : ℕ) (ha : Val w env a A') (hb : Val w env b B') =>
    (val_add (val_mul ha hg) hb : Val w env (ndT gT a b) (A' * g + B'))
  have l2 : Val w env (litCT (const 2)) (litC 2) := val_litCT (val_const 2)
  refine (val_ite (val_lt h1 h2) (val_ite (val_lt h3 h4)
      (val_ite (val_lt h2 hg) (val_ite (val_lt h4 hg)
    (val_ite hrow
      (val_ite (val_eqT hv h1)
        (val_ite (val_lt (val_add (val_mul (val_const 2) (val_labelWtT hB (mB _ _ h2))) hQ)
            (val_add (val_add (val_mul (val_const 2) hH) hD) (val_const 1)))
          (val_trRootT true hB (hcp _ _ _ _ h3 (nd _ _ _ _ h2 h4))
              (hcp _ _ _ _ h4 (nd _ _ _ _ h2 h3))
            (mB _ _ h2) (val_zzSubT hD hC)) val_zeroCT)
        (val_ite (val_eqT hv h2)
          (val_ite (val_lt (val_add (val_mul (val_const 2) (val_labelWtT hB (mB _ _ h1))) hQ)
              (val_add (val_add (val_mul (val_const 2) hH) hD) (val_const 1)))
            (val_trRootT false hB (val_swapT hB (hcp _ _ _ _ h3 (nd _ _ _ _ h1 h4)))
              (val_swapT hB (hcp _ _ _ _ h4 (nd _ _ _ _ h1 h3))) (mB _ _ h1) (val_zzSubT hC hQ))
                  val_zeroCT)
          l2))
      (val_ite (val_eqT hv h3)
        (val_ite (val_lt (val_add hD (val_mul (val_const 2) (val_labelWtT hB (mA _ _ h4))))
            (val_add (val_add (val_add (val_mul (val_const 2) hH) hQ) (val_const 1)) (val_const 1)))
          (val_trRootT true hB (hcp _ _ _ _ h1 (nd _ _ _ _ h2 h4))
              (val_swapT hB (hcp _ _ _ _ h2 (nd _ _ _ _ h1 h4)))
            (mA _ _ h4) (val_zzSubT (val_mul (val_const 2) hQ) (val_add hD hC))) val_zeroCT)
        (val_ite (val_eqT hv h4)
          (val_ite (val_lt (val_add hD (val_mul (val_const 2) (val_labelWtT hB (mA _ _ h3))))
              (val_add (val_add (val_add (val_mul (val_const 2) hH) hQ) (val_const 1))
                  (val_const 1)))
            (val_trRootT false hB (hcp _ _ _ _ h1 (nd _ _ _ _ h2 h3))
                (val_swapT hB (hcp _ _ _ _ h2 (nd _ _ _ _ h1 h3)))
              (mA _ _ h3) (val_zzSubT hC hQ)) val_zeroCT)
          l2)))
    l2) l2) l2) l2).congr ?_
  unfold psiN ind
  simp only [ite_pos_ind, ite_and, Nat.lt_succ_iff]

end Psi

/-- **A factor state of an entry** (`factorGN`), with the holders `holdT` of the parent grid. -/
def factorGT (BT fwT rC cR arT qT gT iT v ξ : Term) (cp : Term → Term → Term) (th : Term → Term)
    (f : Term) : Term :=
  let nodes := holdT arT qT fwT gT iT v
  let t1 := sub f gT
  let t2 := sub (sub f gT) (mul gT gT)
  let t3 := sub (sub (sub f gT) (mul gT gT)) (mul gT gT)
  ite (lt f gT) (encE [const 4, rC, cR, nodes f, sliceT arT qT fwT nodes ξ f])
    (ite (lt f (add gT (mul gT gT)))
      (litCT (ite (lt (div t1 gT) (mod t1 gT))
        (ite (eqT (cp (div t1 gT) (nodes (mod t1 gT))) (cp (mod t1 gT) (nodes (div t1 gT))))
            (const 2) (const 0))
        (const 2)))
      (ite (lt f (add (add gT (mul gT gT)) (mul gT gT)))
        (litCT (ite (eqT (div t2 gT) v) (const 2)
          (ite (eqT (cp (mod t2 gT) (ite (orientT arT qT fwT gT iT)
              (add (mul (div t2 gT) gT) (mod t2 gT))
              (add (mul (mod t2 gT) gT) (div t2 gT))))
            (unpackT BT (packLT gT) (add (const 1) (mod t2 gT)) (th (div t2 gT)))) (const 2)
                (const 0))))
        (psiT BT fwT arT qT gT iT (orientT arT qT fwT gT iT) v cp th (qdT gT t3 3) (qdT gT t3 2)
          (qdT gT t3 1) (qdT gT t3 0))))

section Factor

variable {BT fwT rC cR arT qT gT iT v ξ f : Term} {cp : Term → Term → Term} {th : Term → Term}
  {Bv fw rc cr ar q g i V Ξ F : ℕ} {CP : ℕ → ℕ → ℕ} {TH : ℕ → ℕ}

theorem val_factorGT (hB : Val w env BT Bv) (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hrC : Val w env rC rc) (hcR : Val w env cR cr) (hv : Val w env v V) (hξ : Val w env ξ Ξ)
    (hcp : ∀ p u P U, Val w env p P → Val w env u U → Val w env (cp p u) (CP P U))
    (hth : ∀ o O, Val w env o O → Val w env (th o) (TH O)) (hf : Val w env f F) :
    Val w env (factorGT BT fwT rC cR arT qT gT iT v ξ cp th f)
      (factorGN Bv fw rc cr ar q g i (orientN ar q fw g i) V Ξ CP TH F) := by
  have hg := h.vg.toNum
  have hn : Cross.Exact.FVal w (holdT arT qT fwT gT iT v) env
      (Setup.holders g V (orientN ar q fw g i)) := val_holdT h hv.toExact
  have hN : ∀ p P, Val w env p P → Val w env (holdT arT qT fwT gT iT v p)
      (Setup.holders g V (orientN ar q fw g i) P) := fun p P hp => (hn [] p P hp.toExact).toNum
  have hrow := (val_orientT h).toNum
  have t1 := val_sub hf hg
  have t2 := val_sub (val_sub hf hg) (val_mul hg hg)
  have t3 := val_sub (val_sub (val_sub hf hg) (val_mul hg hg)) (val_mul hg hg)
  have q3 := fun k => (val_qdT h.vg t3.toExact k).toNum
  refine (val_ite (val_lt hf hg) (val_encE
      (.cons (val_const 4) (.cons hrC (.cons hcR (.cons (hN _ _ hf)
      (.cons (val_sliceT h.vA h.vq h.vfw hn hξ.toExact hf.toExact).toNum .nil))))))
    (val_ite (val_lt hf (val_add hg (val_mul hg hg)))
      (val_litCT (val_ite (val_lt (val_div t1 hg) (val_mod t1 hg))
        (val_ite (val_eqT (hcp _ _ _ _ (val_div t1 hg) (hN _ _ (val_mod t1 hg)))
          (hcp _ _ _ _ (val_mod t1 hg) (hN _ _ (val_div t1 hg)))) (val_const 2) (val_const 0))
              (val_const 2)))
      (val_ite (val_lt hf (val_add (val_add hg (val_mul hg hg)) (val_mul hg hg)))
        (val_litCT (val_ite (val_eqT (val_div t2 hg) hv) (val_const 2)
          (val_ite (val_eqT (hcp _ _ _ _ (val_mod t2 hg)
              (val_ite hrow (val_add (val_mul (val_div t2 hg) hg)
              (val_mod t2 hg)) (val_add (val_mul (val_mod t2 hg) hg) (val_div t2 hg))))
            (val_unpackT hB (val_packLT h.vg).toNum (val_add (val_const 1) (val_mod t2 hg))
              (hth _ _ (val_div t2 hg)))) (val_const 2) (val_const 0))))
        (val_psiT hB h hrow hv hcp hth (q3 3) (q3 2) (q3 1) (q3 0))))).congr ?_
  unfold factorGN ind
  simp only [ite_pos_ind, ite_and, ite_not]

end Factor

/-- **The code of a factor state of an entry** (`factorN`), from the path code `chC`, the cache `c`,
the node `v`, the argument code `x` and the code of copies `ξ`. -/
def factorT (fwT BT chC c v x ξ f : Term) : Term :=
  ite (eqT (pQT c) (mul (sqrtT (pQT c)) (sqrtT (pQT c))))
    (factorGT BT fwT (tlE chC) (tlE c) (pAT c) (pQT c) (sqrtT (pQT c)) (stGetT chC 0) v ξ
      (fun p
          u => argLabT (pAT c) (pQT c) fwT (holdT (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0) v p)
        (sliceT (pAT c) (pQT c) fwT (holdT (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0) v) ξ
            p) u)
      (fun o => argLabT (cAT c) (cQT c) fwT v x o) f)
    zeroCT

theorem val_factorT {fwT BT chC c v x ξ f : Term} {fw Bv chv cv V X Ξ F : ℕ}
    (hfw : Val w env fwT fw)
    (hB : Val w env BT Bv) (hch : Val w env chC chv) (hc : Val w env c cv) (hv : Val w env v V)
    (hx : Val w env x X) (hξ : Val w env ξ Ξ) (hf : Val w env f F) :
    Val w env (factorT fwT BT chC c v x ξ f) (factorN fw Bv chv cv V X Ξ F) := by
  have pq := val_pQT hc
  have sq := val_sqrtT pq
  rw [sqrtN_eq] at sq
  have vpA := val_pAT hc
  have hi := val_stGetT hch 0
  have inp : Inp w env (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0) (pA cv) (pQ cv) fw
      (Nat.sqrt (pQ cv)) (stGet chv 0) :=
          ⟨vpA.toExact, pq.toExact, hfw.toExact, sq.toExact, hi.toExact⟩
  have hn := val_holdT inp hv.toExact
  refine (val_ite (val_eqT pq (val_mul sq sq)) (val_factorGT hB inp (val_tlE hch) (val_tlE hc) hv hξ
    (CP := fun P U => argLabN (pA cv) (pQ cv) fw (Setup.holders (Nat.sqrt (pQ cv)) V
      (orientN (pA cv) (pQ cv) fw (Nat.sqrt (pQ cv)) (stGet chv 0)) P)
      (sliceN (pA cv) (pQ cv) fw (Setup.holders (Nat.sqrt (pQ cv)) V
        (orientN (pA cv) (pQ cv) fw (Nat.sqrt (pQ cv)) (stGet chv 0))) Ξ P) U)
    (fun p u P U hp hu => val_argLabT vpA pq hfw (hn [] p P hp.toExact).toNum
      (val_sliceT vpA.toExact pq.toExact hfw.toExact hn hξ.toExact hp.toExact).toNum hu)
    (fun o O ho => val_argLabT (val_cAT hc) (val_cQT hc) hfw hv hx ho) hf) val_zeroCT).congr ?_
  unfold factorN
  simp only [ite_pos_ind]

/-- `rangeN` on terms: the literal `1`, a single factor `mk lo`, or a range `mkR lo hi`. -/
def rangeT (mk : Term → Term) (mkR : Term → Term → Term) (lo hi : Term) : Term :=
  ite (lt lo hi) (ite (eqT hi (add lo (const 1))) (mk lo) (mkR lo hi)) (litCT (const 2))

theorem val_rangeT {mk : Term → Term} {mkR : Term → Term → Term} {lo hi : Term} {MK : ℕ → ℕ}
    {MKR : ℕ → ℕ → ℕ} {Lo Hi : ℕ} (hlo : Val w env lo Lo) (hhi : Val w env hi Hi)
    (hmk : Val w env (mk lo) (MK Lo)) (hmkR : Val w env (mkR lo hi) (MKR Lo Hi)) :
    Val w env (rangeT mk mkR lo hi) (rangeN MK MKR Lo Hi) := by
  refine (val_ite (val_lt hlo hhi) (val_ite (val_eqT hhi (val_add hlo (val_const 1))) hmk hmkR)
    (val_litCT (val_const 2))).congr ?_
  unfold rangeN
  simp only [ite_pos_ind]
  by_cases h : Hi ≤ Lo
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_left (by omega), ite_eq_right h]

/-- The child `b` of a factor range (`rngChildN`). -/
def rngChildT (fwT BT nT b : Term) : Term :=
  ite (eqT b (const 0))
    (rangeT (factorT fwT BT (stGetT nT 1) (stGetT nT 2) (stGetT nT 3) (stGetT nT 4) (stGetT nT 5))
      (fun a
          b' => encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4, stGetT nT 5, a, b'])
      (stGetT nT 6) (div (add (stGetT nT 6) (stGetT nT 7)) (const 2)))
    (rangeT (factorT fwT BT (stGetT nT 1) (stGetT nT 2) (stGetT nT 3) (stGetT nT 4) (stGetT nT 5))
      (fun a
          b' => encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4, stGetT nT 5, a, b'])
      (div (add (stGetT nT 6) (stGetT nT 7)) (const 2)) (stGetT nT 7))

theorem val_rngChildT {fwT BT nT b : Term} {fw Bv n bv : ℕ} (hfw : Val w env fwT fw)
    (hB : Val w env BT Bv) (hn : Val w env nT n) (hb : Val w env b bv) :
    Val w env (rngChildT fwT BT nT b) (rngChildN fw Bv n bv) := by
  have g := fun k => val_stGetT hn k
  have hmid := val_div (val_add (g 6) (g 7)) (val_const 2)
  have hmk := fun (lo : Term) (Lo : ℕ) (hlo : Val w env lo Lo) =>
    val_factorT hfw hB (g 1) (g 2) (g 3) (g 4) (g 5) hlo
  have hmkR := fun (lo hi : Term) (Lo Hi : ℕ) (hlo : Val w env lo Lo) (hhi : Val w env hi Hi) =>
    val_encE (w := w) (env := env) (.cons (val_const 5)
        (.cons (g 1) (.cons (g 2) (.cons (g 3) (.cons (g 4)
      (.cons (g 5) (.cons hlo (.cons hhi .nil))))))))
  refine (val_ite (val_eqT hb (val_const 0))
    (val_rangeT (mk := factorT fwT BT (stGetT nT 1) (stGetT nT 2) (stGetT nT 3) (stGetT nT 4)
        (stGetT nT 5))
      (mkR := fun a
          b' => encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4, stGetT nT 5, a, b'])
      (MK := factorN fw Bv (stGet n 1) (stGet n 2) (stGet n 3) (stGet n 4) (stGet n 5))
      (MKR := fun a
          b => NatList.enc [5, stGet n 1, stGet n 2, stGet n 3, stGet n 4, stGet n 5, a, b])
      (g 6) hmid (hmk _ _ (g 6)) (hmkR _ _ _ _ (g 6) hmid))
    (val_rangeT (mk := factorT fwT BT (stGetT nT 1) (stGetT nT 2) (stGetT nT 3) (stGetT nT 4)
        (stGetT nT 5))
      (mkR := fun a
          b' => encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4, stGetT nT 5, a, b'])
      (MK := factorN fw Bv (stGet n 1) (stGet n 2) (stGet n 3) (stGet n 4) (stGet n 5))
      (MKR := fun a
          b => NatList.enc [5, stGet n 1, stGet n 2, stGet n 3, stGet n 4, stGet n 5, a, b])
      hmid (g 7) (hmk _ _ hmid) (hmkR _ _ _ _ hmid (g 7)))).congr ?_
  unfold rngChildN
  simp only [ite_pos_ind]

/-- The child of an entry (`entChildN`); `f0T v x f` is the code of the literal of the leaf factor
`f` of the first clique. -/
def entChildT (fwT KT VT MT : Term) (f0T : Term → Term → Term → Term) (nT ξ : Term) : Term :=
  ite (eqT (stGetT nT 1) (const 1))
    (ite (eqT ξ (const 0))
      (rangeT (f0T (stGetT nT 3) (stGetT nT 4))
        (fun lo hi => encE [const 6, stGetT nT 2, stGetT nT 3, stGetT nT 4, lo, hi]) (const 0)
        (div (add (const 1) (ite (lt (stGetT nT 3) KT) VT MT)) (const 2)))
      (rangeT (f0T (stGetT nT 3) (stGetT nT 4))
        (fun lo hi => encE [const 6, stGetT nT 2, stGetT nT 3, stGetT nT 4, lo, hi])
        (div (add (const 1) (ite (lt (stGetT nT 3) KT) VT MT)) (const 2))
        (add (const 1) (ite (lt (stGetT nT 3) KT) VT MT))))
    (ite (eqT (pQT (stGetT nT 2)) (mul (sqrtT (pQT (stGetT nT 2))) (sqrtT (pQT (stGetT nT 2)))))
      (ite (copiesOkT (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
          (holdT (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
            (stGetT (stGetT nT 1) 0) (stGetT nT 3)) ξ)
        (encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4, ξ, const 0,
          nFacT (sqrtT (pQT (stGetT nT 2)))]) zeroCT) zeroCT)

theorem val_entChildT {fwT KT VT MT nT ξ : Term} {f0T : Term → Term → Term → Term}
    {f0 : ℕ → ℕ → ℕ → ℕ} {fw K Vv M n Ξ : ℕ} (hfw : Val w env fwT fw) (hK : Val w env KT K)
    (hV : Val w env VT Vv) (hM : Val w env MT M) (hn : Val w env nT n) (hξ : Val w env ξ Ξ)
    (hf0 : ∀ a b c A B C, Val w env a A → Val w env b B → Val w env c C → Val w env (f0T a b c)
        (f0 A B C)) :
    Val w env (entChildT fwT KT VT MT f0T nT ξ) (entChildN fw K Vv M f0 n Ξ) := by
  have g := fun k => val_stGetT hn k
  have hnF := val_add (val_const 1) (val_ite (val_lt (g 3) hK) hV hM)
  have hmid := val_div hnF (val_const 2)
  have hR := fun (lo hi : Term) (Lo Hi : ℕ) (hlo : Val w env lo Lo) (hhi : Val w env hi Hi) =>
    val_rangeT (mk := f0T (stGetT nT 3) (stGetT nT 4)) (MK := f0 (stGet n 3) (stGet n 4))
      (MKR := fun Lo Hi => NatList.enc [6, stGet n 2, stGet n 3, stGet n 4, Lo, Hi])
      (mkR := fun lo hi => encE [const 6, stGetT nT 2, stGetT nT 3, stGetT nT 4, lo, hi]) hlo hhi
      (hf0 _ _ _ _ _ _ (g 3) (g 4) hlo)
      (val_encE (w := w) (env := env) (.cons (val_const 6) (.cons (g 2) (.cons (g 3) (.cons (g 4)
        (.cons hlo (.cons hhi .nil)))))))
  have pq := val_pQT (g 2)
  have sq := val_sqrtT pq
  rw [sqrtN_eq] at sq
  have vpA := val_pAT (g 2)
  have hi := val_stGetT (g 1) 0
  have inp : Inp w env (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
      (stGetT (stGetT nT 1) 0) (pA (stGet n 2)) (pQ (stGet n 2)) fw (Nat.sqrt (pQ (stGet n 2)))
      (stGet (stGet n 1) 0) := ⟨vpA.toExact, pq.toExact, hfw.toExact, sq.toExact, hi.toExact⟩
  have hok := val_copiesOkT vpA pq hfw sq (val_holdT inp (g 3).toExact) hξ
  refine (val_ite (val_eqT (g 1) (val_const 1))
    (val_ite (val_eqT hξ (val_const 0)) (hR _ _ _ _ (val_const 0) hmid) (hR _ _ _ _ hmid hnF))
    (val_ite (val_eqT pq (val_mul sq sq)) (val_ite hok (val_encE (.cons (val_const 5) (.cons (g 1)
      (.cons (g 2) (.cons (g 3) (.cons (g 4) (.cons hξ (.cons (val_const 0)
        (.cons (val_nFacT sq.toExact).toNum .nil))))))))) val_zeroCT) val_zeroCT)).congr ?_
  unfold entChildN ind
  simp only [ite_pos_ind]
  rfl

/-! ### Dispatch on the tag -/

/-- The kind tag of a state with tag `2`–`5` (`eTag`). -/
def eTagT (BT fwT nT : Term) : Term :=
  ite (eqT (stGetT nT 0) (const 2)) (clTagT nT)
    (ite (eqT (stGetT nT 0) (const 4)) (entTagT BT fwT nT) (const 2))

/-- The index width of a state with tag `2`–`5` (`eWidth`). -/
def eWidthT (fwT nT : Term) : Term :=
  ite (eqT (stGetT nT 0) (const 2)) (clWidthT fwT nT)
    (ite (eqT (stGetT nT 0) (const 4)) (entWidthT fwT nT) (const 0))

/-- The code of child `i` of a state with tag `2`–`5` (`eChild`). -/
def eChildT (fwT BT KT VT MT : Term) (f0T : Term → Term → Term → Term) (nT iT : Term) : Term :=
  ite (eqT (stGetT nT 0) (const 2)) (clChildT fwT nT iT)
    (ite (eqT (stGetT nT 0) (const 3)) (lastChildT nT iT)
      (ite (eqT (stGetT nT 0) (const 4)) (entChildT fwT KT VT MT f0T nT iT)
          (rngChildT fwT BT nT iT)))

section Dispatch

variable {BT fwT KT VT MT nT iT : Term} {f0T : Term → Term → Term → Term} {f0 : ℕ → ℕ → ℕ → ℕ}
  {Bv fw K Vv M n i : ℕ}

theorem val_eTagT (hB : Val w env BT Bv) (hfw : Val w env fwT fw) (hn : Val w env nT n) :
    Val w env (eTagT BT fwT nT) (eTag Bv fw n) :=
  (val_ite (val_eqT (val_stGetT hn 0) (val_const 2)) (val_clTagT hn)
    (val_ite (val_eqT (val_stGetT hn 0) (val_const 4)) (val_entTagT hn hfw hB) (val_const 2))).congr
    (by unfold eTag; simp only [ite_pos_ind])

theorem val_eWidthT (hfw : Val w env fwT fw) (hn : Val w env nT n) :
    Val w env (eWidthT fwT nT) (eWidth fw n) :=
  (val_ite (val_eqT (val_stGetT hn 0) (val_const 2)) (val_clWidthT hn hfw)
    (val_ite (val_eqT (val_stGetT hn 0) (val_const 4)) (val_entWidthT hn hfw) (val_const 0))).congr
    (by unfold eWidth; simp only [ite_pos_ind])

theorem val_eChildT (hfw : Val w env fwT fw) (hB : Val w env BT Bv) (hK : Val w env KT K)
    (hV : Val w env VT Vv) (hM : Val w env MT M) (hn : Val w env nT n) (hi : Val w env iT i)
    (hf0 : ∀ a b c A B C, Val w env a A → Val w env b B → Val w env c C → Val w env (f0T a b c)
        (f0 A B C)) :
    Val w env (eChildT fwT BT KT VT MT f0T nT iT) (eChild fw Bv K Vv M f0 n i) :=
  (val_ite (val_eqT (val_stGetT hn 0) (val_const 2)) (val_clChildT hn hfw hi)
    (val_ite (val_eqT (val_stGetT hn 0) (val_const 3)) (val_lastChildT hn hi)
      (val_ite (val_eqT (val_stGetT hn 0) (val_const 4)) (val_entChildT hfw hK hV hM hn hi hf0)
        (val_rngChildT hfw hB hn hi)))).congr (by unfold eChild; simp only [ite_pos_ind])

end Dispatch

section DispatchTiers

variable {S : Setup} {nT fwT BT : Term} {B D : ℕ}

/-- **The tier of the kind tag** on the reachable entry states: `1`. -/
theorem tm_eTagT {st : St} (h : EIn S w L env nT fwT BT st B) (hst : EntrySt st) (hinv : S.Inv D st)
    :
    Tm w L 1 (eTagT BT fwT nT) env := by
  have hL := h.hL
  have c2 : Tm w L 1 (const 2) env := t_small (by norm_num) (by omega)
  have c4 : Tm w L 1 (const 4) env := t_const (lit16 (by norm_num) (by omega))
  cases st with
  | cl chs =>
    have f0 := h.field (code_cl S chs) 0 (by simp)
    have f2 := h.field (code_cl S chs) 2 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
      (fun _ => tm_clTagT h.vn (tm_cache S chs f2.1 f2.2 (by omega)).1 (by omega))
          (fun h0 => by simp at h0)
  | last chs j =>
    have f0 := h.field (code_last S chs j) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega)) (fun h0 => by simp at h0)
        (fun _ => c2))
  | ent chs v args =>
    have f0 := h.field (code_ent S chs v args) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega))
        (fun _ => tm_entTagT h hinv.1) (fun h0 => by simp at h0))
  | rng chs v args ξ lo hi =>
    have f0 := h.field (code_rng S chs v args ξ lo hi) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega)) (fun h0 => by simp at h0)
        (fun _ => c2))
  | _ => exact hst.elim

/-- **The tier of the index width** on the reachable entry states: `7`. -/
theorem tm_eWidthT {st : St} (h : EIn S w L env nT fwT BT st B) (hst : EntrySt st)
    (hinv : S.Inv D st) :
    Tm w L 7 (eWidthT fwT nT) env := by
  have hL := h.hL
  have c2 : Tm w L 1 (const 2) env := t_small (by norm_num) (by omega)
  have c4 : Tm w L 1 (const 4) env := t_const (lit16 (by norm_num) (by omega))
  have c0 : Tm w L 7 (const 0) env := (t_const (k := 0) (by positivity)).mono (by norm_num)
  cases st with
  | cl chs =>
    have f0 := h.field (code_cl S chs) 0 (by simp)
    have f2 := h.field (code_cl S chs) 2 (by simp)
    obtain ⟨tq, tA⟩ := tm_cache S chs f2.1 f2.2 (by omega)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
      (fun _ => tm_clWidthT h.vn h.vfw tq tA h.tfw hL h.hfw) (fun h0 => by simp at h0)
  | last chs j =>
    have f0 := h.field (code_last S chs j) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega)) (fun h0 => by simp at h0)
        (fun _ => c0))
  | ent chs v args =>
    have f0 := h.field (code_ent S chs v args) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega))
        (fun _ => (tm_entWidthT h hinv.1).mono (by norm_num)) (fun h0 => by simp at h0))
  | rng chs v args ξ lo hi =>
    have f0 := h.field (code_rng S chs v args ξ lo hi) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega)) (fun h0 => by simp at h0)
        (fun _ => c0))
  | _ => exact hst.elim

end DispatchTiers

end Cslib.Complexity.NtimeDspace.Cube.Num
