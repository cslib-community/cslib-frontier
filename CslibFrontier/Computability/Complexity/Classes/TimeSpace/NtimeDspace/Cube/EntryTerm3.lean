/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.EntryTerm2

/-!
# Tiers of the child programs of the entry states (Lemma 6.4)

The child terms of `EntryTerm2.lean` (`clChildT`, `entChildT`, `rngChildT`, `factorT`, `factorGT`,
`psiT`, `rangeT` and the dispatch `eChildT`) have the tier of any bound on the child code, on the
reachable entry states. Every output is a list code (`encE`), whose tier `d ≤ 29` comes from a bound
on its value (`tm_encE`); the bound is carried down the branches that are taken (`tm_iteD`), and the
untaken branches need no tier.

The consumer supplies the bundled inputs `EIn`, the invariant `S.Inv D st`, an index term of tier
`1`, the size conditions `SizeOK S L` (the child array of a clique, `q·fw` bits, and every argument
code fit in `L` bits, at every clique of a valid path) and a bound `S.code (S.gen.child st i) <
2^(d·L)` with `1 ≤ d ≤ 29`; everything else (paths, field widths, label weights, the shape of the
grids) is derived from the invariant.

## Main definitions

* `SizeOK S L`: the size conditions on `L` along the valid paths.

## Main results

* `tm_iteD`: an `ite` with a bound on its value needs the tier of the taken branch only, under that
  bound.
* `tm_rangeT`, `tm_psiT`, `tm_factorGT`: tiers of the range, rectangle-factor and factor-state
  terms on abstract inputs (codes of labels of weight at most `Φ`, `w(Φ) + 2 ≤ B ≤ L`).
* `tm_factorT`, `tm_clChildT`, `tm_lastChildD`, `tm_entChildT`, `tm_rngChildT`: the tiers on the
  codes of reachable states.
* `tm_eChildT`: **the tier of the child dispatch** on the reachable entry states.
* `SizeOK.of_lt`: the size conditions from `q₀·(fw + B) < L` and `w(Φ₀ / 2^e) + 2 ≤ B`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct

variable {w : List Bool} {env : List ℕ} {L : ℕ}

/-! ### Branches under a bound on the value -/

theorem ind_of_pos' {P : Prop} [Decidable P] (h : 0 < (if P then 1 else 0 : ℕ)) : P := by
  by_contra hp
  rw [ite_eq_right hp] at h
  exact Nat.lt_irrefl 0 h

/-- **An `ite` under a bound on its value**: the taken branch gets the bound and must have the
tier; the other branch needs nothing. -/
theorem tm_iteD {c t e : Term} {C dc d : ℕ} (hc : Val w env c C) (tc : Tm w L dc c env)
    (ht : 0 < C → t.denote w env < 2 ^ (d * L) → Tm w L d t env)
    (he : C = 0 → e.denote w env < 2 ^ (d * L) → Tm w L d e env)
    (hv : (ite c t e).denote w env < 2 ^ (d * L)) : Tm w L d (ite c t e) env := by
  rw [denote_ite, hc.2] at hv
  refine tm_ite2v hc tc (fun h => ht h ?_) (fun h => he h ?_)
  · rwa [ite_eq_left h] at hv
  · rwa [ite_eq_right (by omega : ¬ 0 < C)] at hv

/-- Every entry of a list is at most its code. -/
theorem le_enc_of_mem {x : ℕ} : ∀ {l : List ℕ}, x ∈ l → x ≤ NatList.enc l
  | [], h => by simp at h
  | y :: l, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact NatList.le_enc_cons _ _
    · exact (le_enc_of_mem h).trans (NatList.enc_le_enc_cons y l)

/-- A list code under a bound on its value (entries of any tier). -/
theorem tm_encD {d : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 2 ≤ L) {ts : List Term} {vs : List ℕ}
    (hs : List.Forall₂ (fun t v => Val w env t v ∧ ∃ dt, Tm w L dt t env) ts vs)
    (hv : (encE ts).denote w env < 2 ^ (d * L)) : Tm w L d (encE ts) env :=
  tm_encE hd1 hd hL hs (by rwa [← (val_encE (List.Forall₂.imp (fun _ _ h => h.1) hs)).2])

theorem tm_zeroCT {d : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 2 ≤ L)
    (hv : zeroCT.denote w env < 2 ^ (d * L)) : Tm w L d zeroCT env :=
  tm_encD hd1 hd hL (.cons ⟨val_const 0, 1, t_small (by norm_num) hL⟩ .nil) hv

theorem tm_litCT {z : Term} {Z dz d : ℕ} (hz : Val w env z Z) (tz : Tm w L dz z env) (hd1 : 1 ≤ d)
    (hd : d ≤ 29) (hL : 2 ≤ L) (hv : (litCT z).denote w env < 2 ^ (d * L)) :
    Tm w L d (litCT z) env :=
  tm_encD hd1 hd hL (.cons ⟨val_const 1, 1, t_one (by omega)⟩ (.cons ⟨hz, dz, tz⟩ .nil)) hv

theorem tm_lit2 {d : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 2 ≤ L)
    (hv : (litCT (const 2)).denote w env < 2 ^ (d * L)) : Tm w L d (litCT (const 2)) env :=
  tm_litCT (val_const 2) (t_small (by norm_num) hL) hd1 hd hL hv

/-- **The tier of a range** (`rangeT`) under a bound on its value: the single factor and the range
need their tiers only when they are taken. -/
theorem tm_rangeT {mk : Term → Term} {mkR : Term → Term → Term} {lo hi : Term} {Lo Hi dlo dhi d : ℕ}
    (hlo : Val w env lo Lo) (hhi : Val w env hi Hi) (tlo : Tm w L dlo lo env)
    (thi : Tm w L dhi hi env) (hdlo : dlo + 1 ≤ 128)
    (hmk : Lo < Hi → Hi = Lo + 1 → (mk lo).denote w env < 2 ^ (d * L) → Tm w L d (mk lo) env)
    (hmkR : Lo < Hi → (mkR lo hi).denote w env < 2 ^ (d * L) → Tm w L d (mkR lo hi) env)
    (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 2 ≤ L)
    (hv : (rangeT mk mkR lo hi).denote w env < 2 ^ (d * L)) : Tm w L d
        (rangeT mk mkR lo hi) env := by
  unfold rangeT at hv ⊢
  refine tm_iteD (val_lt hlo hhi) (t_lt tlo thi (by omega)) (fun h hb => ?_)
    (fun _ hb => tm_lit2 hd1 hd hL hb) hv
  have hlt : Lo < Hi := ind_of_pos' h
  exact tm_iteD (val_eqT hhi (val_add hlo (val_const 1)))
    (t_eqT' thi (t_add tlo (t_one (by omega)) (by omega) (by omega)) (by omega))
    (fun h' hb' => hmk hlt (ind_of_pos' h') hb') (fun _ hb' => hmkR hlt hb') hb

/-- A trRoot code under a bound on its value. -/
theorem tm_trRootD (up : Bool) {B xC yC mC zc : Term} {Bv zv dz d : ℕ} {x y m : Label}
    (hB : Val w env B Bv) (hx : Val w env xC (lcode x)) (hy : Val w env yC (lcode y))
    (hm : Val w env mC (lcode m)) (hz : Val w env zc zv) (tB : Tm w L 1 B env)
        (tx : Tm w L 1 xC env)
    (ty : Tm w L 1 yC env) (tm : Tm w L 1 mC env) (tz : Tm w L dz zc env) (lx : LB Bv x)
    (ly : LB Bv y) (lm : LB Bv m) (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 4 ≤ L) (hBL : Bv ≤ L)
    (hv : (trRootT B up xC yC mC zc).denote w env < 2 ^ (d * L)) :
    Tm w L d (trRootT B up xC yC mC zc) env :=
  tm_trRootT up hB hx hy hm hz tB tx ty tm tz lx ly lm hd1 hd hL hBL
    (by rwa [← (val_trRootT up hB hx hy hm hz).2])

/-! ### The size conditions -/

/-- **The size conditions on `L`** at the cliques of the valid paths: the child array of a clique
(`q·fw` bits) and every argument code fit in `L` bits. -/
structure SizeOK (S : Setup) (L : ℕ) : Prop where
  arr : ∀ chs, S.PathOK chs → (S.clique chs).q * S.fw ≤ L
  arg : ∀ chs, S.PathOK chs → ∀ u,
    argWidN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw u < L

theorem q_le_first (S : Setup) : ∀ chs, S.PathOK chs → (S.clique chs).q ≤ S.C₀.q
  | [], _ => le_rfl
  | i :: rest, ⟨hp, _, hsq, _⟩ => by
    have hq' : (S.clique (i :: rest)).q = Nat.sqrt (S.clique rest).q := by
      change (childAt S.fw (S.clique rest) i).q = _
      unfold childAt; rw [dite_eq_left hsq]; exact mergeStep_q _ _ _
    rw [hq']
    exact (Nat.sqrt_le_self _).trans (q_le_first S rest hp)

theorem argWidN_le {ar q fw B : ℕ} (hW : ∀ a b, codeWidth (budgetN ar q fw a b) ≤ B) (v : ℕ) :
    argWidN ar q fw v ≤ q * B := by
  unfold argWidN argOffN
  calc ∑ u' ∈ Finset.range q, (if u' < q ∧ v < q then
        (if u' = v then 0 else codeWidth (budgetN ar q fw v u')) else 0)
      ≤ ∑ _u' ∈ Finset.range q, B := Finset.sum_le_sum fun u' _ => by
        split_ifs
        · exact Nat.zero_le _
        · exact hW _ _
        · exact Nat.zero_le _
    _ = q * B := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The size conditions from one bound at the first clique: `q₀·(fw + B) < L`. -/
theorem SizeOK.of_lt {S : Setup} (hS : S.Good) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {B : ℕ}
    (hB : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B) (h : S.C₀.q * (S.fw + B) < L) :
    SizeOK S L where
  arr chs hp := by
    have := q_le_first S chs hp
    have : (S.clique chs).q * S.fw ≤ S.C₀.q * (S.fw + B) :=
      Nat.mul_le_mul this (Nat.le_add_right _ _)
    omega
  arg chs hp u := by
    have h1 := argWidN_le (codeWidth_budgetN_path S hS hp he hB) u
    have h2 : (S.clique chs).q * B ≤ S.C₀.q * (S.fw + B) :=
      Nat.mul_le_mul (q_le_first S chs hp) (Nat.le_add_left _ _)
    omega

/-! ### Last labels -/

/-- The tier of the child of a last label, from a bound on the child code (`d ≤ 29`). -/
theorem tm_lastChildD {S : Setup} {nT fwT BT bT : Term} {chs : List ℕ} {i b B d : ℕ}
    (h : EIn S w L env nT fwT BT (.last chs i) B) (hb : Val w env bT b) (tb : Tm w L 1 bT env)
    (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hc : S.code (S.gen.child (.last chs i) b) < 2 ^ (d * L)) : Tm w L d
        (lastChildT nT bT) env := by
  have hL := h.hL
  have f1 : Val w env (stGetT nT 1) (NatList.enc chs) ∧ Tm w L 1 (stGetT nT 1) env :=
    h.field (code_last S chs i) 1 (by simp)
  have f2 : Val w env (stGetT nT 2) (S.cacheC chs) ∧ Tm w L 1 (stGetT nT 2) env :=
    h.field (code_last S chs i) 2 (by simp)
  have f3 : Val w env (stGetT nT 3) i ∧ Tm w L 1 (stGetT nT 3) env :=
    h.field (code_last S chs i) 3 (by simp)
  have hc' : NatList.enc [4, NatList.enc chs, S.cacheC chs, b, i] < 2 ^ (d * L) := hc
  exact tm_encE hd1 hd (by omega) (.cons ⟨val_const 4, 1, t_const (lit16 (by norm_num) (by omega))⟩
    (.cons ⟨f1.1, 1, f1.2⟩ (.cons ⟨f2.1, 1, f2.2⟩
        (.cons ⟨hb, 1, tb⟩ (.cons ⟨f3.1, 1, f3.2⟩ .nil)))))
    hc'

/-! ### Clique states -/

/-- **The tier of the child of a clique state**, from a bound on the child code (`d ≤ 29`). -/
theorem tm_clChildT {S : Setup} {nT fwT BT iT : Term} {chs : List ℕ} {i B D d : ℕ}
    (h : EIn S w L env nT fwT BT (.cl chs) B) (hinv : S.Inv D (.cl chs)) (hZ : SizeOK S L)
    (hI : Val w env iT i) (tI : Tm w L 1 iT env) (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hc : S.code (S.gen.child (.cl chs) i) < 2 ^ (d * L)) : Tm w L d (clChildT fwT nT iT) env := by
  have hL := h.hL
  obtain ⟨hp, hq2, -⟩ := hinv
  have hden : (clChildT fwT nT iT).denote w env < 2 ^ (d * L) := by
    rw [(val_clChildT h.vn h.vfw hI).2, clChildN_eq S h.hS hp i]; exact hc
  have f1 : Val w env (stGetT nT 1) (NatList.enc chs) ∧ Tm w L 1 (stGetT nT 1) env :=
    h.field (code_cl S chs) 1 (by simp)
  have f2 : Val w env (stGetT nT 2) (S.cacheC chs) ∧ Tm w L 1 (stGetT nT 2) env :=
    h.field (code_cl S chs) 2 (by simp)
  obtain ⟨tq, tA⟩ := tm_cache S chs f2.1 f2.2 (by omega)
  have vq := val_cQT f2.1
  rw [cQ_eq] at vq
  have vA := val_cAT f2.1
  rw [cA_eq] at vA
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have t1 : Tm w L 1 (const 1) env := t_one (by omega)
  unfold clChildT at hden ⊢
  refine tm_iteD (val_eqT vq (val_const 2))
      (t_eqT' tq (t_small (by norm_num) (by omega)) (by omega))
    (fun _ hb => ?_) (fun _ hb => ?_) hden
  · -- two nodes: `last` at a label code of exact weight
    have tie := tiers_dummy (tA.mono (by norm_num)) tq h.tfw hL h.hfw
    have vb := (val_budT vA.toExact vq.toExact h.vfw.toExact (Cross.Exact.val_const 0 env)
      (Cross.Exact.val_const 1 env)).toNum
    have tb := tm_budT tie h.vfw.toExact t0 t1 (by norm_num)
    have hW := (h.codeWidth_budgetN hp 0 1).trans h.hBL
    have vW := val_codeWidthT vb
    have tW := tm_val (tm_codeWidthT vb tb (by norm_num) (by omega)) vW (lt_tier_one hW)
    have tp := t_pow2v (d := 2) vW tW (by norm_num) (by omega) (by norm_num) (by omega)
    have vj := val_mod hI (val_pow2 vW)
    have tj : Tm w L 1 (mod iT (pow2 (codeWidthT (budT (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT
        (const 0) (const 1))))) env := t_mod_left tI tp
    have tval := tm_validT vb vW vj tb tW tj (by norm_num) (by omega) hW
    have tlw := tm_labelWtT vW vj tW tj (by omega) hW
    refine tm_iteD (val_ite (val_eqT vb (val_const 0)) (val_eqT hI (val_const 0))
      (val_ite (val_eqT (val_validT vb vW vj) (val_const 1)) (val_eqT (val_labelWtT vW vj) vb)
        (val_const 0)))
      (t_ite (t_eqT' tb t0 (by omega)) (t_eqT' tI t0 (by omega))
        (t_ite (t_eqT' tval t1 (by omega)) (t_eqT' tlw tb (by omega)) t0))
      (fun _ hb' => ?_) (fun _ hb' => tm_zeroCT hd1 hd (by omega) hb') hb
    exact tm_encD hd1 hd (by omega) (.cons ⟨val_const 3, 1, t_small (by norm_num) (by omega)⟩
      (.cons ⟨f1.1, 1, f1.2⟩ (.cons ⟨f2.1, 1, f2.2⟩ (.cons ⟨hI, 1, tI⟩ .nil)))) hb'
  · -- a grid: the clique one level down at a valid choice code
    have vs := val_sqrtT vq
    rw [sqrtN_eq] at vs
    have ts := tm_sqrtT vq tq (by norm_num) (by omega)
    refine tm_iteD (val_eqT vq (val_mul vs vs)) (t_eqT' tq (t_mul ts ts (by norm_num)) (by omega))
      (fun hsq hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
    have hsq : (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q :=
      ind_of_pos' hsq
    have hq1 : 0 < (S.clique chs).q := by rw [hq2]; positivity
    have inp : Inp w env (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT (sqrtT (cQT (stGetT nT 2))) iT
        (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw
        (Nat.sqrt (S.clique chs).q) i :=
      ⟨vA.toExact, vq.toExact, h.vfw.toExact, vs.toExact, hI.toExact⟩
    have tie : Tiers w L env (cAT (stGetT nT 2)) (cQT (stGetT nT 2)) fwT
        (sqrtT (cQT (stGetT nT 2))) iT
        S.fw (Nat.sqrt (S.clique chs).q) :=
      ⟨tA.mono (by norm_num), tq, h.tfw, ts, tI.mono (by norm_num), hL, h.hfw, Nat.sqrt_pos.mpr hq1⟩
    refine tm_iteD (val_choiceValidT inp).toNum (tm_choiceValidT inp tie) (fun _ hb' => ?_)
      (fun _ hb' => tm_zeroCT hd1 hd (by omega) hb') hb
    have vC := (val_childT inp).toNum
    have tC := tm_childT inp tie (by rw [← hsq]; exact hZ.arr chs hp)
    have vX := val_encE (w := w) (env := env) (.cons vs (.cons vC .nil))
    have v2 := val_consE hI f1.1
    have v3 := val_consE vX f2.1
    have hall := val_encE (w := w) (env := env) (.cons (val_const 2) (.cons v2 (.cons v3 .nil)))
    have hvs := hall.2 ▸ hb'
    have b2 := (le_enc_of_mem (x := consF i (NatList.enc chs)) (by simp)).trans_lt hvs
    have b3 := (le_enc_of_mem (x := consF (NatList.enc [Nat.sqrt (S.clique chs).q,
      childN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw
        (Nat.sqrt (S.clique chs).q) i]) (S.cacheC chs)) (by simp)).trans_lt hvs
    have bX := (consF_ge _ _ (NatList.enc_pos (S.cacheL chs))).1.trans_lt b3
    have tX := tm_encE hd1 hd (by omega) (.cons ⟨vs, 1, ts⟩ (.cons ⟨vC, 16, tC⟩ .nil)) bX
    have t2 := tm_consE hI f1.1 tI f1.2 (NatList.enc_pos chs) hd1 hd (by omega) b2
    have t3 := tm_consE vX f2.1 tX f2.2 (NatList.enc_pos (S.cacheL chs)) hd1 hd (by omega) b3
    exact tm_encE hd1 hd (by omega) (.cons ⟨val_const 2, 1, t_small (by norm_num) (by omega)⟩
      (.cons ⟨v2, d, t2⟩ (.cons ⟨v3, d, t3⟩ .nil))) hvs

/-! ### Rectangle factors -/

section Psi

variable {BT fwT arT qT gT iT rowT v A₁ A₂ B₁ B₂ : Term} {cp : Term → Term → Term}
  {th : Term → Term} {Bv fw ar q g i R V a₁ a₂ b₁ b₂ Φ d : ℕ} {CL : ℕ → ℕ → Label}
  {TL : ℕ → Label}

theorem tm_rStreamT {B B' : Term} (tg : Tm w L 1 gT env) (tB : Tm w L 1 B env)
    (tB' : Tm w L 1 B' env) (hL : 1 ≤ L) : Tm w L 4 (rStreamT gT B B') env := by
  have ts : Tm w L 2 (sumT B fun b => sub (sub gT (const 1)) b) env :=
    t_sumT tB (fun e he y hy => t_sub (t_sub (tg.ext he) (t_one hL)) hy) hL (by omega)
  have t1 : Tm w L 2 (add (const 1) gT) env := (t_add (t_one hL) tg hL (by omega)).mono (by omega)
  have t2 : Tm w L 3 (add (sumT B fun b => sub (sub gT (const 1)) b) (sub (sub B' B) (const 1)))
      env :=
    (t_add ts (t_sub (t_sub tB' tB) (t_one hL)) hL (by omega)).mono (by omega)
  exact (t_add t1 t2 hL (by omega)).mono (by omega)

/-- The rectangle factor inside the grid (`psiBodyT`), under a bound on its value. The copies `cp`
and the packed labels `th` are codes of labels of weight at most `Φ`. -/
theorem tm_psiBodyT (hB : Val w env BT Bv) (tB : Tm w L 1 BT env) (hBL : Bv ≤ L)
    (hΦ : codeWidth Φ + 2 ≤ Bv) (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hrow : Val w env rowT R) (trow : Tm w L 1 rowT env)
    (hv : Val w env v V) (tv : Tm w L 1 v env)
    (hcp : ∀ p u P U, Val w env p P → Val w env u U → Val w env (cp p u) (lcode (CL P U)))
    (tcp : ∀ p u P U, Val w env p P → Val w env u U → Tm w L 1 p env → Tm w L 3 u env →
      Tm w L 1 (cp p u) env)
    (hCL : ∀ P U, labelWt (CL P U) ≤ Φ)
    (hth : ∀ o O, Val w env o O → Val w env (th o) (lcode (TL O)))
    (tth : ∀ o O, Val w env o O → Tm w L 1 o env → Tm w L 1 (th o) env)
    (hTL : ∀ O, labelWt (TL O) ≤ Φ)
    (h1 : Val w env A₁ a₁) (h2 : Val w env A₂ a₂) (h3 : Val w env B₁ b₁) (h4 : Val w env B₂ b₂)
    (t1 : Tm w L 1 A₁ env) (t2 : Tm w L 1 A₂ env) (t3 : Tm w L 1 B₁ env) (t4 : Tm w L 1 B₂ env)
    (ha : a₁ < a₂) (hb : b₁ < b₂) (ha2 : a₂ < g) (hb2 : b₂ < g) (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hden : (psiBodyT BT fwT arT qT gT iT rowT v cp th A₁ A₂ B₁ B₂).denote w env < 2 ^ (d * L)) :
    Tm w L d (psiBodyT BT fwT arT qT gT iT rowT v cp th A₁ A₂ B₁ B₂) env := by
  have hL := t.hL
  have hg := h.vg.toNum
  have c1 : Tm w L 1 (const 1) env := t_one (by omega)
  have c2 : Tm w L 1 (const 2) env := t_small (by norm_num) (by omega)
  have vx : Val w env (quadIdxT gT A₁ A₂ B₁ B₂) (((a₁ * g + a₂) * g + b₁) * g + b₂) :=
    val_add (val_mul (val_add (val_mul (val_add (val_mul h1 hg) h2) hg) h3) hg) h4
  have tx : Tm w L 7 (quadIdxT gT A₁ A₂ B₁ B₂) env :=
    (t_add (t_mul (t_add (t_mul (t_add (t_mul t1 t.tg (by norm_num)) t2 (by omega) (by omega)) t.tg
      (by omega)) t3 (by omega) (by omega)) t.tg (by omega)) t4 (by omega) (by omega)).mono
          (by omega)
  have vD := (val_digT h.vfw h.vi (val_mul (val_const 2) vx).toExact).toNum
  have tD : Tm w L 1 (digT fwT iT (mul (const 2) (quadIdxT gT A₁ A₂ B₁ B₂))) env :=
    tm_digT t.tfw h.vfw t.hfw hL t.ti le_rfl (t_mul c2 tx (by norm_num)) (by norm_num)
  have vC := (val_digT h.vfw h.vi (val_add (val_mul (val_const 2) vx) (val_const 1)).toExact).toNum
  have tC : Tm w L 1 (digT fwT iT (add (mul (const 2) (quadIdxT gT A₁ A₂ B₁ B₂)) (const 1))) env :=
    tm_digT t.tfw h.vfw t.hfw hL t.ti le_rfl
      (t_add (t_mul c2 tx (by norm_num)) c1 (by omega) (by omega)) (by omega)
  have vQ := (val_offT h.vfw).toNum
  have tQ := tm_offT t h.vfw
  have vH := (val_diagT h vx.toExact).toNum
  have tH := tm_diagT h t tx
  have vLt := (val_packLT h.vg).toNum
  have tLt := tm_packLT t.tg hL
  have sB := val_rStreamT hg h3 h4
  have tsB := tm_rStreamT t.tg t3 t4 (by omega)
  have sA := val_rStreamT hg h1 h2
  have tsA := tm_rStreamT t.tg t1 t2 (by omega)
  have hsB := rStreamN_lt hb hb2
  have hsA := rStreamN_lt ha ha2
  have mv : ∀ {s : Term} {sv : ℕ}, Val w env s sv → sv < packL g → ∀ o O, Val w env o O →
      Val w env (unpackT BT (packLT gT) s (th o)) (lcode (unpack (packL g) (TL O) sv)) :=
    fun hs hsl o O ho => (val_unpackT hB vLt hs (hth o O ho)).congr (unpackN_lcode hsl (hTL O) hΦ)
  have mt : ∀ {s : Term} {sv : ℕ}, Val w env s sv → Tm w L 4 s env → sv < packL g → ∀ o O,
      Val w env o O → Tm w L 1 o env → Tm w L 1 (unpackT BT (packLT gT) s (th o)) env :=
    fun hs ts hsl o O ho tO => tm_unpackT hB vLt hs (hth o O ho) tB tLt ts (tth o O ho tO)
      (by norm_num) hsl (hTL O) hΦ (by omega) hBL
  have mw : ∀ O s, LB Bv (unpack (packL g) (TL O) s) :=
    fun O s => lb_of_le ((labelWt_unpack_le _ _ _).trans (hTL O)) hΦ
  have nd : ∀ {a b : Term} {A' B' : ℕ}, Val w env a A' → Val w env b B' → Tm w L 1 a env →
      Tm w L 1 b env → Val w env (ndT gT a b) (A' * g + B') ∧ Tm w L 3 (ndT gT a b) env :=
    fun ha hb ta tb => ⟨val_add (val_mul ha hg) hb,
      (t_add (t_mul ta t.tg (by norm_num)) tb (by omega) (by omega)).mono (by omega)⟩
  have swv : ∀ {c : Term} {l : Label}, Val w env c (lcode l) → labelWt l ≤ Φ →
      Val w env (swapT BT c) (lcode (swapLabel l)) :=
    fun hc hl => (val_swapT hB hc).congr (swapN_lcode (lb_of_le hl hΦ))
  have swt : ∀ {c : Term} {l : Label}, Val w env c (lcode l) → Tm w L 1 c env → labelWt l ≤ Φ →
      Tm w L 1 (swapT BT c) env :=
    fun hc tc hl => tm_swapT hB hc tB tc (lb_of_le hl hΦ) (by omega) hBL
  have sww : ∀ l : Label, labelWt l ≤ Φ → LB Bv (swapLabel l) :=
    fun l hl => lb_of_le ((labelWt_swap l).trans_le hl) hΦ
  unfold psiBodyT at hden ⊢
  dsimp only at hden ⊢
  refine tm_iteD hrow trow (fun _ hb => ?_) (fun _ hb => ?_) hden
  · -- rows
    refine tm_iteD (val_eqT hv h1) (t_eqT' tv t1 (by omega)) (fun _ hb => ?_) (fun _ hb => ?_) hb
    · have vm := mv sB hsB A₂ a₂ h2
      have tm := mt sB tsB hsB A₂ a₂ h2 t2
      refine tm_iteD (val_lt (val_add (val_mul (val_const 2) (val_labelWtT hB vm)) vQ)
          (val_add (val_add (val_mul (val_const 2) vH) vD) (val_const 1)))
        (tm_leT (t_add (t_mul c2 (tm_labelWtT hB vm tB tm (by omega) hBL) (by norm_num)) tQ
            (by omega)
          (by omega)) (t_add (t_mul c2 tH (by norm_num)) tD (by omega) (by omega)) hL (by omega))
        (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
      obtain ⟨n1, tn1⟩ := nd h2 h4 t2 t4
      obtain ⟨n2, tn2⟩ := nd h2 h3 t2 t3
      exact tm_trRootD true hB (hcp _ _ _ _ h3 n1) (hcp _ _ _ _ h4 n2) vm (val_zzSubT vD vC) tB
        (tcp _ _ _ _ h3 n1 t3 tn1) (tcp _ _ _ _ h4 n2 t4 tn2) tm
        (tm_zzSubT tD tC (by omega) (by norm_num)) (lb_of_le (hCL _ _) hΦ) (lb_of_le (hCL _ _) hΦ)
        (mw _ _) hd1 hd (by omega) hBL hb
    · refine tm_iteD (val_eqT hv h2) (t_eqT' tv t2 (by omega)) (fun _ hb => ?_)
        (fun _ hb => tm_lit2 hd1 hd (by omega) hb) hb
      have vm := mv sB hsB A₁ a₁ h1
      have tm := mt sB tsB hsB A₁ a₁ h1 t1
      refine tm_iteD (val_lt (val_add (val_mul (val_const 2) (val_labelWtT hB vm)) vQ)
          (val_add (val_add (val_mul (val_const 2) vH) vD) (val_const 1)))
        (tm_leT (t_add (t_mul c2 (tm_labelWtT hB vm tB tm (by omega) hBL) (by norm_num)) tQ
            (by omega)
          (by omega)) (t_add (t_mul c2 tH (by norm_num)) tD (by omega) (by omega)) hL (by omega))
        (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
      obtain ⟨n1, tn1⟩ := nd h1 h4 t1 t4
      obtain ⟨n2, tn2⟩ := nd h1 h3 t1 t3
      exact tm_trRootD false hB (swv (hcp _ _ _ _ h3 n1) (hCL _ _))
          (swv (hcp _ _ _ _ h4 n2) (hCL _ _))
        vm (val_zzSubT vC vQ) tB (swt (hcp _ _ _ _ h3 n1) (tcp _ _ _ _ h3 n1 t3 tn1) (hCL _ _))
        (swt (hcp _ _ _ _ h4 n2) (tcp _ _ _ _ h4 n2 t4 tn2) (hCL _ _)) tm
        (tm_zzSubT tC tQ (by omega) (by norm_num)) (sww _ (hCL _ _)) (sww _ (hCL _ _)) (mw _ _)
        hd1 hd (by omega) hBL hb
  · -- columns
    refine tm_iteD (val_eqT hv h3) (t_eqT' tv t3 (by omega)) (fun _ hb => ?_) (fun _ hb => ?_) hb
    · have vm := mv sA hsA B₂ b₂ h4
      have tm := mt sA tsA hsA B₂ b₂ h4 t4
      refine tm_iteD (val_lt (val_add vD (val_mul (val_const 2) (val_labelWtT hB vm)))
          (val_add (val_add (val_add (val_mul (val_const 2) vH) vQ) (val_const 1)) (val_const 1)))
        (tm_leT (t_add tD (t_mul c2 (tm_labelWtT hB vm tB tm (by omega) hBL) (by norm_num))
            (by omega)
          (by omega)) (t_add (t_add (t_mul c2 tH (by norm_num)) tQ (by omega) (by omega)) c1
              (by omega)
          (by omega)) hL (by omega))
        (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
      obtain ⟨n1, tn1⟩ := nd h2 h4 t2 t4
      obtain ⟨n2, tn2⟩ := nd h1 h4 t1 t4
      exact tm_trRootD true hB (hcp _ _ _ _ h1 n1) (swv (hcp _ _ _ _ h2 n2) (hCL _ _)) vm
        (val_zzSubT (val_mul (val_const 2) vQ) (val_add vD vC)) tB (tcp _ _ _ _ h1 n1 t1 tn1)
        (swt (hcp _ _ _ _ h2 n2) (tcp _ _ _ _ h2 n2 t2 tn2) (hCL _ _)) tm
        (tm_zzSubT (t_mul c2 tQ (by norm_num)) (t_add tD tC (by omega) (by omega)) (by omega)
          (by omega)) (lb_of_le (hCL _ _) hΦ) (sww _ (hCL _ _)) (mw _ _) hd1 hd (by omega) hBL hb
    · refine tm_iteD (val_eqT hv h4) (t_eqT' tv t4 (by omega)) (fun _ hb => ?_)
        (fun _ hb => tm_lit2 hd1 hd (by omega) hb) hb
      have vm := mv sA hsA B₁ b₁ h3
      have tm := mt sA tsA hsA B₁ b₁ h3 t3
      refine tm_iteD (val_lt (val_add vD (val_mul (val_const 2) (val_labelWtT hB vm)))
          (val_add (val_add (val_add (val_mul (val_const 2) vH) vQ) (val_const 1)) (val_const 1)))
        (tm_leT (t_add tD (t_mul c2 (tm_labelWtT hB vm tB tm (by omega) hBL) (by norm_num))
            (by omega)
          (by omega)) (t_add (t_add (t_mul c2 tH (by norm_num)) tQ (by omega) (by omega)) c1
              (by omega)
          (by omega)) hL (by omega))
        (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
      obtain ⟨n1, tn1⟩ := nd h2 h3 t2 t3
      obtain ⟨n2, tn2⟩ := nd h1 h3 t1 t3
      exact tm_trRootD false hB (hcp _ _ _ _ h1 n1) (swv (hcp _ _ _ _ h2 n2) (hCL _ _)) vm
        (val_zzSubT vC vQ) tB (tcp _ _ _ _ h1 n1 t1 tn1)
        (swt (hcp _ _ _ _ h2 n2) (tcp _ _ _ _ h2 n2 t2 tn2) (hCL _ _)) tm
        (tm_zzSubT tC tQ (by omega) (by norm_num)) (lb_of_le (hCL _ _) hΦ)
            (sww _ (hCL _ _)) (mw _ _)
        hd1 hd (by omega) hBL hb

/-- **The tier of a rectangle factor** (`psiT`), under a bound on its value (`d ≤ 29`). The copies
`cp p u` and the packed labels `th o` are codes of labels of weight at most `Φ`, of tier `1` at
arguments of tier `1` (`p`, `o`) and `3` (`u`); `w(Φ) + 2 ≤ B ≤ L`. -/
theorem tm_psiT (hB : Val w env BT Bv) (tB : Tm w L 1 BT env) (hBL : Bv ≤ L)
    (hΦ : codeWidth Φ + 2 ≤ Bv) (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hrow : Val w env rowT R) (trow : Tm w L 1 rowT env)
    (hv : Val w env v V) (tv : Tm w L 1 v env)
    (hcp : ∀ p u P U, Val w env p P → Val w env u U → Val w env (cp p u) (lcode (CL P U)))
    (tcp : ∀ p u P U, Val w env p P → Val w env u U → Tm w L 1 p env → Tm w L 3 u env →
      Tm w L 1 (cp p u) env)
    (hCL : ∀ P U, labelWt (CL P U) ≤ Φ)
    (hth : ∀ o O, Val w env o O → Val w env (th o) (lcode (TL O)))
    (tth : ∀ o O, Val w env o O → Tm w L 1 o env → Tm w L 1 (th o) env)
    (hTL : ∀ O, labelWt (TL O) ≤ Φ)
    (h1 : Val w env A₁ a₁) (h2 : Val w env A₂ a₂) (h3 : Val w env B₁ b₁) (h4 : Val w env B₂ b₂)
    (t1 : Tm w L 1 A₁ env) (t2 : Tm w L 1 A₂ env) (t3 : Tm w L 1 B₁ env) (t4 : Tm w L 1 B₂ env)
    (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hden : (psiT BT fwT arT qT gT iT rowT v cp th A₁ A₂ B₁ B₂).denote w env < 2 ^ (d * L)) :
    Tm w L d (psiT BT fwT arT qT gT iT rowT v cp th A₁ A₂ B₁ B₂) env := by
  have hL := t.hL
  have hg := h.vg.toNum
  unfold psiT at hden ⊢
  refine tm_iteD (val_lt h1 h2) (t_lt t1 t2 (by omega)) (fun e1 hb => ?_)
    (fun _ hb => tm_lit2 hd1 hd (by omega) hb) hden
  refine tm_iteD (val_lt h3 h4) (t_lt t3 t4 (by omega)) (fun e2 hb => ?_)
    (fun _ hb => tm_lit2 hd1 hd (by omega) hb) hb
  refine tm_iteD (val_lt h2 hg) (t_lt t2 t.tg (by omega)) (fun e3 hb => ?_)
    (fun _ hb => tm_lit2 hd1 hd (by omega) hb) hb
  refine tm_iteD (val_lt h4 hg) (t_lt t4 t.tg (by omega)) (fun e4 hb => ?_)
    (fun _ hb => tm_lit2 hd1 hd (by omega) hb) hb
  exact tm_psiBodyT hB tB hBL hΦ h t hrow trow hv tv hcp tcp hCL hth tth hTL h1 h2 h3 h4 t1 t2 t3 t4
    (ind_of_pos' e1) (ind_of_pos' e2) (ind_of_pos' e3) (ind_of_pos' e4) hd1 hd hb

end Psi

/-! ### Factor states -/

section Factor

variable {BT fwT rC cR arT qT gT iT v ξ f : Term} {cp : Term → Term → Term} {th : Term → Term}
  {Bv fw rc cr ar q g i V Ξ F Φ d : ℕ} {CL : ℕ → ℕ → Label} {TL : ℕ → Label}

/-- **The tier of a factor state** (`factorGT`), under a bound on its value (`d ≤ 29`): an old table
entry (its slice of `ξ` needs `argWidN < L`), a test, or a rectangle factor. The copies and packed
labels are as in `tm_psiT`. -/
theorem tm_factorGT (hB : Val w env BT Bv) (tB : Tm w L 1 BT env) (hBL : Bv ≤ L)
    (hΦ : codeWidth Φ + 2 ≤ Bv) (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hrC : Val w env rC rc) (trC : Tm w L 1 rC env)
    (hcR : Val w env cR cr) (tcR : Tm w L 1 cR env) (hv : Val w env v V) (tv : Tm w L 1 v env)
    (hξ : Val w env ξ Ξ) (tξ : Tm w L 1 ξ env) (hW : ∀ u, argWidN ar q fw u < L)
    (hcp : ∀ p u P U, Val w env p P → Val w env u U → Val w env (cp p u) (lcode (CL P U)))
    (tcp : ∀ p u P U, Val w env p P → Val w env u U → Tm w L 1 p env → Tm w L 3 u env →
      Tm w L 1 (cp p u) env)
    (hCL : ∀ P U, labelWt (CL P U) ≤ Φ)
    (hth : ∀ o O, Val w env o O → Val w env (th o) (lcode (TL O)))
    (tth : ∀ o O, Val w env o O → Tm w L 1 o env → Tm w L 1 (th o) env)
    (hTL : ∀ O, labelWt (TL O) ≤ Φ) (hf : Val w env f F) (tf : Tm w L 1 f env) (hd1 : 1 ≤ d)
    (hd : d ≤ 29)
    (hden : (factorGT BT fwT rC cR arT qT gT iT v ξ cp th f).denote w env < 2 ^ (d * L)) :
    Tm w L d (factorGT BT fwT rC cR arT qT gT iT v ξ cp th f) env := by
  have hL := t.hL
  have hg := h.vg.toNum
  have c0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have c1 : Tm w L 1 (const 1) env := t_one (by omega)
  have c2 : Tm w L 1 (const 2) env := t_small (by norm_num) (by omega)
  have hn := val_holdT h hv.toExact
  have tn := tm_holdT h t tv
  have nv : ∀ p P, Val w env p P → Val w env (holdT arT qT fwT gT iT v p)
      (Setup.holders g V (orientN ar q fw g i) P) := fun p P hp => (hn [] p P hp.toExact).toNum
  have nt : ∀ p, Tm w L 1 p env → Tm w L 3 (holdT arT qT fwT gT iT v p) env :=
    fun p tp => tn.app (Ext.refl env) tp
  have tgg : Tm w L 2 (mul gT gT) env := t_mul t.tg t.tg (by norm_num)
  unfold factorGT at hden ⊢
  dsimp only at hden ⊢
  refine tm_iteD (val_lt hf hg) (t_lt tf t.tg (by omega)) (fun _ hb => ?_) (fun _ hb => ?_) hden
  · -- an old table entry
    exact tm_encD hd1 hd (by omega) (.cons
        ⟨val_const 4, 1, t_const (lit16 (by norm_num) (by omega))⟩
      (.cons ⟨hrC, 1, trC⟩ (.cons ⟨hcR, 1, tcR⟩ (.cons ⟨nv f F hf, 3, nt f tf⟩
      (.cons ⟨(val_sliceT h.vA h.vq h.vfw hn hξ.toExact hf.toExact).toNum, 1,
        tm_sliceT h t hn tn (by norm_num) tξ (by norm_num) tf hf.toExact (by norm_num) (hW _)⟩
        .nil))))) hb
  refine tm_iteD (val_lt hf (val_add hg (val_mul hg hg)))
    (t_lt tf (t_add t.tg tgg (by omega) (by omega)) (by omega)) (fun _ hb => ?_) (fun _ hb => ?_) hb
  · -- a test of two copies
    have v1 := val_sub hf hg
    have tt1 : Tm w L 1 (sub f gT) env := t_sub tf t.tg
    have vq1 := val_div v1 hg
    have tq1 : Tm w L 1 (div (sub f gT) gT) env := t_div tt1 t.tg
    have vr1 := val_mod v1 hg
    have tr1 : Tm w L 1 (mod (sub f gT) gT) env := t_mod_left tt1 t.tg
    exact tm_litCT (val_ite (val_lt vq1 vr1) (val_ite (val_eqT (hcp _ _ _ _ vq1 (nv _ _ vr1))
        (hcp _ _ _ _ vr1 (nv _ _ vq1))) (val_const 2) (val_const 0)) (val_const 2))
      (t_ite (t_lt tq1 tr1 (by omega)) (t_ite (t_eqT' (tcp _ _ _ _ vq1 (nv _ _ vr1) tq1 (nt _ tr1))
        (tcp _ _ _ _ vr1 (nv _ _ vq1) tr1 (nt _ tq1)) (by omega)) c2 c0) c2) hd1 hd (by omega) hb
  refine tm_iteD (val_lt hf (val_add (val_add hg (val_mul hg hg)) (val_mul hg hg)))
    (t_lt tf (t_add (t_add t.tg tgg (by omega) (by omega)) tgg (by omega) (by omega)) (by omega))
    (fun _ hb => ?_) (fun _ hb => ?_) hb
  · -- a test of a copy against a packed label
    have v2 := val_sub (val_sub hf hg) (val_mul hg hg)
    have tt2 : Tm w L 1 (sub (sub f gT) (mul gT gT)) env := t_sub (t_sub tf t.tg) tgg
    have vq2 := val_div v2 hg
    have tq2 : Tm w L 1 (div (sub (sub f gT) (mul gT gT)) gT) env := t_div tt2 t.tg
    have vr2 := val_mod v2 hg
    have tr2 : Tm w L 1 (mod (sub (sub f gT) (mul gT gT)) gT) env := t_mod_left tt2 t.tg
    have vo := (val_orientT h).toNum
    have tO := tm_orientT h t
    have vu := val_ite vo (val_add (val_mul vq2 hg) vr2) (val_add (val_mul vr2 hg) vq2)
    have tu : Tm w L 3 (ite (orientT arT qT fwT gT iT)
        (add (mul (div (sub (sub f gT) (mul gT gT)) gT) gT) (mod (sub (sub f gT) (mul gT gT)) gT))
        (add (mul (mod (sub (sub f gT) (mul gT gT)) gT) gT) (div (sub (sub f gT) (mul gT gT)) gT)))
            env :=
      (t_ite tO (t_add (t_mul tq2 t.tg (by norm_num)) tr2 (by omega) (by omega))
        (t_add (t_mul tr2 t.tg (by norm_num)) tq2 (by omega) (by omega))).mono (by omega)
    have vs := val_add (val_const 1) vr2
    have ts : Tm w L 2 (add (const 1) (mod (sub (sub f gT) (mul gT gT)) gT)) env :=
      (t_add c1 tr2 (by omega) (by omega)).mono (by omega)
    have hsl : 1 + (F - g - g * g) % g < packL g := by
      have := Nat.mod_lt (F - g - g * g) t.hg
      unfold packL; omega
    have vm := val_unpackT hB (val_packLT h.vg).toNum vs (hth _ _ vq2)
    have tm := tm_unpackT hB (val_packLT h.vg).toNum vs (hth _ _ vq2) tB (tm_packLT t.tg hL) ts
      (tth _ _ vq2 tq2) (by norm_num) hsl (hTL _) hΦ (by omega) hBL
    exact tm_litCT (val_ite (val_eqT vq2 hv) (val_const 2)
        (val_ite (val_eqT (hcp _ _ _ _ vr2 vu) vm) (val_const 2) (val_const 0)))
      (t_ite (t_eqT' tq2 tv (by omega)) c2 (t_ite (t_eqT' (tcp _ _ _ _ vr2 vu tr2 tu) tm (by omega))
        c2 c0)) hd1 hd (by omega) hb
  · -- a rectangle factor
    have v3 := val_sub (val_sub (val_sub hf hg) (val_mul hg hg)) (val_mul hg hg)
    have tt3 : Tm w L 1 (sub (sub (sub f gT) (mul gT gT)) (mul gT gT)) env :=
      t_sub (t_sub (t_sub tf t.tg) tgg) tgg
    exact tm_psiT hB tB hBL hΦ h t (val_orientT h).toNum (tm_orientT h t) hv tv hcp tcp hCL hth tth
      hTL (val_qdT h.vg v3.toExact 3).toNum (val_qdT h.vg v3.toExact 2).toNum
      (val_qdT h.vg v3.toExact 1).toNum (val_qdT h.vg v3.toExact 0).toNum
      (tm_qdT t h.vg tt3 3 (by norm_num)) (tm_qdT t h.vg tt3 2 (by norm_num))
      (tm_qdT t h.vg tt3 1 (by norm_num)) (tm_qdT t h.vg tt3 0 (by norm_num)) hd1 hd hb

end Factor

/-- **The tier of a factor state of an entry** (`factorT`) at a valid path `j :: rest`, under a
bound on its value (`d ≤ 29`): the path code `chC`, the cache `c`, the node `v`, the argument code
`x`,
the copies `ξ` and the factor index `f` have tier `1`. The labels of the copies and of the
arguments, their weights and the grid of the parent are derived from the path. -/
theorem tm_factorT {S : Setup} {fwT BT chC c v x ξ f : Term} {j : ℕ} {rest : List ℕ}
    {V X Ξ F B d : ℕ} (hS : S.Good) (hp : S.PathOK (j :: rest)) (hZ : SizeOK S L)
    (hfw : Val w env fwT S.fw) (tfw : Tm w L 1 fwT env) (hB : Val w env BT B)
    (tB : Tm w L 1 BT env) (hL : 16 ≤ L) (hfwL : S.fw < L) (hBL : B ≤ L)
    {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) (hΦ : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B)
    (hch : Val w env chC (NatList.enc (j :: rest))) (tch : Tm w L 1 chC env)
    (hc : Val w env c (S.cacheC (j :: rest))) (tc : Tm w L 1 c env)
    (hv : Val w env v V) (tv : Tm w L 1 v env) (hx : Val w env x X) (tx : Tm w L 1 x env)
    (hξ : Val w env ξ Ξ) (tξ : Tm w L 1 ξ env) (hf : Val w env f F) (tf : Tm w L 1 f env)
    (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hden : (factorT fwT BT chC c v x ξ f).denote w env < 2 ^ (d * L)) :
    Tm w L d (factorT fwT BT chC c v x ξ f) env := by
  obtain ⟨hp', h4, hsq', -⟩ := id hp
  have hfP := fits_path S hS hp'
  have hfC := fits_path S hS hp
  have vpq := val_pQT hc
  rw [pQ_eq] at vpq
  have vpA := val_pAT hc
  rw [pA_eq] at vpA
  obtain ⟨tq, tA⟩ := tm_pcache S j rest hc tc (by omega)
  have vcq := val_cQT hc
  rw [cQ_eq] at vcq
  have vcA := val_cAT hc
  rw [cA_eq] at vcA
  obtain ⟨tcq, tcA⟩ := tm_cache S (j :: rest) hc tc (by omega)
  have vs := val_sqrtT vpq
  rw [sqrtN_eq] at vs
  have ts := tm_sqrtT vpq tq (by norm_num) (by omega)
  have vj : Val w env (stGetT chC 0) j := (val_stGetT hch 0).congr (stGet_cons_zero _ _)
  have tj := tm_stGetT hch tch le_rfl (by norm_num) (by omega) 0 (by simp)
  have vrC : Val w env (tlE chC) (NatList.enc rest) := (val_tlE hch).congr (tlF_enc_cons _ _)
  have trC := (tm_hdE_tlE hch tch le_rfl (by norm_num) (by omega)).2
  have hc' : Val w env c (NatList.enc (S.arrAt (j :: rest) :: S.cacheL rest)) := hc
  have vcR : Val w env (tlE c) (S.cacheC rest) := (val_tlE hc).congr (tlF_cacheC S j rest)
  have tcR := (tm_hdE_tlE hc' tc le_rfl (by norm_num) (by omega)).2
  have hg0 : 0 < Nat.sqrt (S.clique rest).q := Nat.sqrt_pos.mpr (by omega)
  have inp : Inp w env (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0)
      (arrN (S.clique rest).q S.fw (extN (S.clique rest).a)) (S.clique rest).q S.fw
      (Nat.sqrt (S.clique rest).q) j :=
    ⟨vpA.toExact, vpq.toExact, hfw.toExact, vs.toExact, vj.toExact⟩
  have tie : Tiers w L env (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0) S.fw
      (Nat.sqrt (S.clique rest).q) :=
    ⟨tA.mono (by norm_num), tq, tfw, ts, tj.mono (by norm_num), hL, hfwL, hg0⟩
  have hn := val_holdT inp hv.toExact
  have tn := tm_holdT inp tie tv
  have hWP : ∀ a b, codeWidth (budgetN (arrN (S.clique rest).q S.fw (extN (S.clique rest).a))
      (S.clique rest).q S.fw a b) ≤ L :=
    fun a b => (codeWidth_budgetN_path S hS hp' he hΦ a b).trans hBL
  have hWC : ∀ a b, codeWidth (budgetN (arrN (S.clique (j :: rest)).q S.fw
      (extN (S.clique (j :: rest)).a)) (S.clique (j :: rest)).q S.fw a b) ≤ L :=
    fun a b => (codeWidth_budgetN_path S hS hp he hΦ a b).trans hBL
  have hcp : ∀ p u P U, Val w env p P → Val w env u U →
      Val w env (argLabT (pAT c) (pQT c) fwT
          (holdT (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0) v p)
        (sliceT (pAT c) (pQT c) fwT (holdT (pAT c) (pQT c) fwT (sqrtT (pQT c))
            (stGetT chC 0) v) ξ p) u)
      (lcode (argLab (S.clique rest) (Setup.holders (Nat.sqrt (S.clique rest).q) V
        (orientN (arrN (S.clique rest).q S.fw (extN (S.clique rest).a)) (S.clique rest).q S.fw
          (Nat.sqrt (S.clique rest).q) j) P)
        (sliceN (arrN (S.clique rest).q S.fw (extN (S.clique rest).a)) (S.clique rest).q S.fw
          (Setup.holders (Nat.sqrt (S.clique rest).q) V
            (orientN (arrN (S.clique rest).q S.fw (extN (S.clique rest).a)) (S.clique rest).q S.fw
              (Nat.sqrt (S.clique rest).q) j)) Ξ P) U)) :=
    fun p u P U hp hu => (val_argLabT vpA vpq hfw (hn [] p P hp.toExact).toNum
      (val_sliceT vpA.toExact vpq.toExact hfw.toExact hn hξ.toExact hp.toExact).toNum hu).congr
      (argLabN_eq _ hfP _ _ _)
  have tcp : ∀ p u P U, Val w env p P → Val w env u U → Tm w L 1 p env → Tm w L 3 u env →
      Tm w L 1 (argLabT (pAT c) (pQT c) fwT
        (holdT (pAT c) (pQT c) fwT (sqrtT (pQT c)) (stGetT chC 0) v p)
        (sliceT (pAT c) (pQT c) fwT (holdT (pAT c) (pQT c) fwT (sqrtT (pQT c))
            (stGetT chC 0) v) ξ p)
        u) env :=
    fun p u P U hp hu tp tu => tm_argLabT vpA vpq hfw (hn [] p P hp.toExact).toNum
      (val_sliceT vpA.toExact vpq.toExact hfw.toExact hn hξ.toExact hp.toExact).toNum hu
      (tA.mono (by norm_num)) tq tfw (tn.app (Ext.refl env) tp)
      (tm_sliceT inp tie hn tn (by norm_num) tξ (by norm_num) tp hp.toExact (by norm_num)
        (hZ.arg rest hp' _)) tu (by norm_num) (by norm_num) (by norm_num) hL hfwL (hWP _ _)
  have hth : ∀ o O, Val w env o O → Val w env (argLabT (cAT c) (cQT c) fwT v x o)
      (lcode (argLab (S.clique (j :: rest)) V X O)) :=
    fun o O ho => (val_argLabT vcA vcq hfw hv hx ho).congr (argLabN_eq _ hfC _ _ _)
  have tth : ∀ o O, Val w env o O → Tm w L 1 o env → Tm w L 1 (argLabT (cAT c) (cQT c) fwT v x o)
      env :=
    fun o O ho tO => tm_argLabT vcA vcq hfw hv hx ho (tcA.mono (by norm_num)) tcq tfw tv tx tO
      (by norm_num) (by norm_num) (by norm_num) hL hfwL (hWC _ _)
  unfold factorT at hden ⊢
  refine tm_iteD (val_eqT vpq (val_mul vs vs)) (t_eqT' tq (t_mul ts ts (by norm_num)) (by omega))
    (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hden
  exact tm_factorGT hB tB hBL hΦ inp tie vrC trC vcR tcR hv tv hξ tξ (hZ.arg rest hp') hcp tcp
    (fun _ _ => labelWt_argLab_le _ (budget_le_path S he hp') _ _ _) hth tth
    (fun _ => labelWt_argLab_le _ (budget_le_path S he hp) _ _ _) hf tf hd1 hd hb

/-! ### Factor ranges -/

/-- **The tier of the child of a factor range**, from a bound on the child code (`d ≤ 29`). -/
theorem tm_rngChildT {S : Setup} {nT fwT BT iT : Term} {chs : List ℕ} {v args ξ lo hi i B D d : ℕ}
    (h : EIn S w L env nT fwT BT (.rng chs v args ξ lo hi) B)
    (hinv : S.Inv D (.rng chs v args ξ lo hi)) (hZ : SizeOK S L) (hI : Val w env iT i)
    (tI : Tm w L 1 iT env) (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hc : S.code (S.gen.child (.rng chs v args ξ lo hi) i) < 2 ^ (d * L)) :
    Tm w L d (rngChildT fwT BT nT iT) env := by
  rcases chs with _ | ⟨j, rest⟩
  · exact hinv.elim
  have hL := h.hL
  have hp := hinv.1
  obtain ⟨_, he, hB⟩ := h.hB
  have hden : (rngChildT fwT BT nT iT).denote w env < 2 ^ (d * L) := by
    rw [(val_rngChildT h.vfw h.vB h.vn hI).2, rngChildN_eq S h.hS he hB hp v args ξ lo hi i]; exact
        hc
  have e := code_rng S (j :: rest) v args ξ lo hi
  have f1 : Val w env (stGetT nT 1) (NatList.enc (j :: rest)) ∧ Tm w L 1 (stGetT nT 1) env :=
    h.field e 1 (by simp)
  have f2 : Val w env (stGetT nT 2) (S.cacheC (j :: rest)) ∧ Tm w L 1 (stGetT nT 2) env :=
    h.field e 2 (by simp)
  have f3 : Val w env (stGetT nT 3) v ∧ Tm w L 1 (stGetT nT 3) env := h.field e 3 (by simp)
  have f4 : Val w env (stGetT nT 4) args ∧ Tm w L 1 (stGetT nT 4) env := h.field e 4 (by simp)
  have f5 : Val w env (stGetT nT 5) ξ ∧ Tm w L 1 (stGetT nT 5) env := h.field e 5 (by simp)
  have f6 : Val w env (stGetT nT 6) lo ∧ Tm w L 1 (stGetT nT 6) env := h.field e 6 (by simp)
  have f7 : Val w env (stGetT nT 7) hi ∧ Tm w L 1 (stGetT nT 7) env := h.field e 7 (by simp)
  have hlo := f6.2.lt
  rw [f6.1.2] at hlo
  have hhi := f7.2.lt
  rw [f7.1.2] at hhi
  have vmid := val_div (val_add f6.1 f7.1) (val_const 2)
  have tmid : Tm w L 1 (div (add (stGetT nT 6) (stGetT nT 7)) (const 2)) env :=
    tm_val (t_div (t_add f6.2 f7.2 (by omega) (by omega)) (t_small (by norm_num) (by omega))) vmid
      (by omega)
  have mkR : ∀ {a b : Term} {A' B' da db : ℕ}, Val w env a A' → Val w env b B' →
      Tm w L da a env → Tm w L db b env →
      (encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4, stGetT nT 5, a, b]).denote
        w env < 2 ^ (d * L) →
      Tm w L d (encE [const 5, stGetT nT 1, stGetT nT 2, stGetT nT 3, stGetT nT 4,
          stGetT nT 5, a, b])
        env :=
    fun ha hb ta tb hv => tm_encD hd1 hd (by omega)
      (.cons ⟨val_const 5, 1, t_const (lit16 (by norm_num) (by omega))⟩ (.cons ⟨f1.1, 1, f1.2⟩
      (.cons ⟨f2.1, 1, f2.2⟩ (.cons ⟨f3.1, 1, f3.2⟩ (.cons ⟨f4.1, 1, f4.2⟩ (.cons ⟨f5.1, 1, f5.2⟩
      (.cons ⟨ha, _, ta⟩ (.cons ⟨hb, _, tb⟩ .nil)))))))) hv
  have mk : ∀ {a : Term} {A' : ℕ}, Val w env a A' → Tm w L 1 a env →
      (factorT fwT BT (stGetT nT 1) (stGetT nT 2) (stGetT nT 3) (stGetT nT 4)
          (stGetT nT 5) a).denote
        w env < 2 ^ (d * L) →
      Tm w L d (factorT fwT BT (stGetT nT 1) (stGetT nT 2) (stGetT nT 3) (stGetT nT 4)
          (stGetT nT 5) a)
        env :=
    fun ha ta hv => tm_factorT h.hS hp hZ h.vfw h.tfw h.vB h.tB hL h.hfw h.hBL he hB f1.1 f1.2 f2.1
      f2.2 f3.1 f3.2 f4.1 f4.2 f5.1 f5.2 ha ta hd1 hd hv
  unfold rngChildT at hden ⊢
  refine tm_iteD (val_eqT hI (val_const 0))
      (t_eqT' tI (t_small (by norm_num) (by omega)) (by omega))
    (fun _ hb => ?_) (fun _ hb => ?_) hden
  · exact tm_rangeT f6.1 vmid f6.2 tmid (by norm_num) (fun _ _ hv => mk f6.1 f6.2 hv)
      (fun _ hv => mkR f6.1 vmid f6.2 tmid hv) hd1 hd (by omega) hb
  · exact tm_rangeT vmid f7.1 tmid f7.2 (by norm_num) (fun _ _ hv => mk vmid tmid hv)
      (fun _ hv => mkR vmid f7.1 tmid f7.2 hv) hd1 hd (by omega) hb

/-! ### Entries -/

/-- `entChildN` reads the leaf factors `f0` at the node field `stGet n 3` of a first-clique entry
only. -/
theorem entChildN_congr {fw K V M : ℕ} {f0 f0' : ℕ → ℕ → ℕ → ℕ} {n : ℕ}
    (h : stGet n 1 = 1 → ∀ x f, f0 (stGet n 3) x f = f0' (stGet n 3) x f) (ξ : ℕ) :
    entChildN fw K V M f0 n ξ = entChildN fw K V M f0' n ξ := by
  unfold entChildN
  dsimp only
  by_cases h1 : stGet n 1 = 1
  · rw [show f0 (stGet n 3) = f0' (stGet n 3) from funext fun x => funext (h h1 x)]
  · rw [ite_eq_right h1, ite_eq_right h1]


/-- **The tier of the child of an entry**, from a bound on the child code (`d ≤ 29`). At the first
clique the leaf factors are `f0T v x f`: `hf0v`, `hf0` give their values (the codes of the literals
`factor0`, at the nodes `v < 2K`) and `hf0t` some tier at a factor index of tier `1` (e.g. from
`tm_factor0T` of
`FirstTerm.lean`; the code is retiered by its value); `KT`, `VT`, `MT` are the numbers `K`, `V`, `M`
of the network. -/
theorem tm_entChildT {S : Setup} {nT fwT BT KT VT MT iT : Term} {f0T : Term → Term → Term → Term}
    {f0 : ℕ → ℕ → ℕ → ℕ} {chs : List ℕ} {v args i B D d : ℕ}
    (h : EIn S w L env nT fwT BT (.ent chs v args) B) (hinv : S.Inv D (.ent chs v args))
    (hZ : SizeOK S L) (hK : Val w env KT S.K) (hV : Val w env VT S.V) (hM : Val w env MT S.G.M)
    (tK : Tm w L 1 KT env) (tV : Tm w L 1 VT env) (tM : Tm w L 1 MT env)
    (hf0v : ∀ a b c A B C, Val w env a A → Val w env b B → Val w env c C →
      Val w env (f0T a b c) (f0 A B C))
    (hf0 : ∀ v < 2 * S.K, ∀ x f, f0 v x f = S.code (.lit (S.factor0 v x f)))
    (hf0t : ∀ fT f, Val w env fT f → Tm w L 1 fT env →
      ∃ d0, Tm w L d0 (f0T (stGetT nT 3) (stGetT nT 4) fT) env)
    (hI : Val w env iT i) (tI : Tm w L 1 iT env) (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hc : S.code (S.gen.child (.ent chs v args) i) < 2 ^ (d * L)) :
    Tm w L d (entChildT fwT KT VT MT f0T nT iT) env := by
  have hL := h.hL
  have hp := hinv.1
  have hden : (entChildT fwT KT VT MT f0T nT iT).denote w env < 2 ^ (d * L) := by
    classical
    -- the leaf factors are read at the node `v < 2K` only
    let f0' : ℕ → ℕ → ℕ → ℕ := fun v' x f =>
      if v' < 2 * S.K then f0 v' x f else S.code (.lit (S.factor0 v' x f))
    have hf0' : ∀ v' x f, f0' v' x f = S.code (.lit (S.factor0 v' x f)) := by
      intro v' x f
      by_cases hv' : v' < 2 * S.K
      · exact (ite_eq_left hv').trans (hf0 v' hv' x f)
      · exact ite_eq_right hv'
    have hcg : entChildN S.fw S.K S.V S.G.M f0 (S.code (.ent chs v args)) i =
        entChildN S.fw S.K S.V S.G.M f0' (S.code (.ent chs v args)) i := by
      refine entChildN_congr (fun h1 x f => ?_) i
      cases chs with
      | nil =>
        have hv : v < 2 * S.K := hinv.2
        have e3 : stGet (S.code (.ent [] v args)) 3 = v := by simp [Setup.code]
        rw [e3]
        exact (ite_eq_left hv).symm
      | cons j rest =>
        exfalso
        have e : stGet (S.code (.ent (j :: rest) v args)) 1 = NatList.enc (j :: rest) := by
          simp [Setup.code]
        exact enc_cons_ne_one j rest (e ▸ h1)
    rw [(val_entChildT h.vfw hK hV hM h.vn hI hf0v).2, hcg, entChildN_eq S h.hS hf0' hp v args i]
    exact hc
  obtain ⟨⟨v1, t1⟩, ⟨vc, tc⟩, ⟨vv, tv⟩, ⟨vx, tx⟩⟩ := h.fields_ent
  have c0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have c1 : Tm w L 1 (const 1) env := t_one (by omega)
  unfold entChildT at hden ⊢
  refine tm_iteD (val_eqT v1 (val_const 1)) (t_eqT' t1 c1 (by omega)) (fun h0 hb => ?_)
    (fun h0 hb => ?_) hden
  · -- the first clique: the two halves of the factors
    rcases chs with _ | ⟨j, rest⟩
    swap
    · exact absurd (ind_of_pos' h0) (enc_cons_ne_one j rest)
    have vX := val_ite (val_lt vv hK) hV hM
    have tX : Tm w L 1 (ite (lt (stGetT nT 3) KT) VT MT) env :=
      (t_ite (t_lt tv tK (by omega)) tV tM).mono (by omega)
    have hX := tX.lt
    rw [vX.2] at hX
    have vF := val_add (val_const 1) vX
    have tF : Tm w L 2 (add (const 1) (ite (lt (stGetT nT 3) KT) VT MT)) env :=
      (t_add c1 tX (by omega) (by omega)).mono (by omega)
    have vmid := val_div vF (val_const 2)
    have key : ∀ X N : ℕ, X < N → (1 + X) / 2 < N := fun X N h => by omega
    have tmid : Tm w L 1 (div (add (const 1) (ite (lt (stGetT nT 3) KT) VT MT)) (const 2)) env :=
      tm_val (t_div tF (t_small (by norm_num) (by omega))) vmid (key _ _ hX)
    have mkR : ∀ {a b : Term} {A' B' da db : ℕ}, Val w env a A' → Val w env b B' →
        Tm w L da a env → Tm w L db b env →
        (encE [const 6, stGetT nT 2, stGetT nT 3, stGetT nT 4, a, b]).denote w env < 2 ^ (d * L) →
        Tm w L d (encE [const 6, stGetT nT 2, stGetT nT 3, stGetT nT 4, a, b]) env :=
      fun ha hb ta tb hv => tm_encD hd1 hd (by omega)
        (.cons ⟨val_const 6, 1, t_const (lit16 (by norm_num) (by omega))⟩ (.cons ⟨vc, 1, tc⟩
        (.cons ⟨vv, 1, tv⟩ (.cons ⟨vx, 1, tx⟩ (.cons ⟨ha, _, ta⟩ (.cons ⟨hb, _, tb⟩ .nil)))))) hv
    have f0tier : ∀ {a : Term} {A' : ℕ}, Val w env a A' → Tm w L 1 a env →
        (f0T (stGetT nT 3) (stGetT nT 4) a).denote w env < 2 ^ (d * L) →
        Tm w L d (f0T (stGetT nT 3) (stGetT nT 4) a) env := fun ha ta hv => by
      obtain ⟨d0, t0'⟩ := hf0t _ _ ha ta
      have hv0 := hf0v _ _ _ _ _ _ vv vx ha
      rw [hv0.2] at hv
      exact tm_val t0' hv0 hv
    refine tm_iteD (val_eqT hI (val_const 0)) (t_eqT' tI c0 (by omega)) (fun _ hb => ?_)
      (fun _ hb => ?_) hb
    · exact tm_rangeT (val_const 0) vmid c0 tmid (by norm_num)
        (fun _ _ hv => f0tier (val_const 0) c0 hv) (fun _ hv => mkR (val_const 0) vmid c0 tmid hv)
        hd1 hd (by omega) hb
    · exact tm_rangeT vmid vF tmid tF (by norm_num) (fun _ _ hv => f0tier vmid tmid hv)
        (fun _ hv => mkR vmid vF tmid tF hv) hd1 hd (by omega) hb
  · -- higher up: the range of all the factors, if the copies are valid
    rcases chs with _ | ⟨j, rest⟩
    · exact absurd h0 (by simp [NatList.enc_nil])
    obtain ⟨hp', h4, hsq', -⟩ := hp
    have hpq := val_pQT vc
    rw [pQ_eq] at hpq
    have vpA := val_pAT vc
    rw [pA_eq] at vpA
    obtain ⟨tq, tA⟩ := tm_pcache S j rest vc tc (by omega)
    have hsq := val_sqrtT hpq
    rw [sqrtN_eq] at hsq
    have ts := tm_sqrtT hpq tq (by norm_num) (by omega)
    have vi := val_stGetT v1 0
    have ti0 := tm_stGetT v1 t1 le_rfl (by norm_num) (by omega) 0 (by simp)
    have inp : Inp w env (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
        (stGetT (stGetT nT 1) 0) _ _ S.fw _ _ :=
      ⟨vpA.toExact, hpq.toExact, h.vfw.toExact, hsq.toExact, vi.toExact⟩
    have tie : Tiers w L env (pAT (stGetT nT 2)) (pQT (stGetT nT 2)) fwT (sqrtT (pQT (stGetT nT 2)))
        (stGetT (stGetT nT 1) 0) S.fw (Nat.sqrt (S.clique rest).q) :=
      ⟨tA.mono (by norm_num), tq, h.tfw, ts, ti0.mono (by norm_num), hL, h.hfw,
        Nat.sqrt_pos.mpr (by omega)⟩
    refine tm_iteD (val_eqT hpq (val_mul hsq hsq))
        (t_eqT' tq (t_mul ts ts (by norm_num)) (by omega))
      (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
    refine tm_iteD (val_copiesOkT vpA hpq h.vfw hsq (val_holdT inp vv.toExact) hI)
      (tm_copiesOkT vpA hpq h.vfw hsq (val_holdT inp vv.toExact) hI (tA.mono (by norm_num)) tq h.tfw
        ts (tm_holdT inp tie tv) tI (by norm_num) hL h.hfw
        (fun a b => (h.codeWidth_budgetN hp' a b).trans h.hBL)
        (fun _ _ => hZ.arg rest hp' _))
      (fun _ hb => ?_) (fun _ hb => tm_zeroCT hd1 hd (by omega) hb) hb
    exact tm_encD hd1 hd (by omega) (.cons
        ⟨val_const 5, 1, t_const (lit16 (by norm_num) (by omega))⟩
      (.cons ⟨v1, 1, t1⟩ (.cons ⟨vc, 1, tc⟩ (.cons ⟨vv, 1, tv⟩ (.cons ⟨vx, 1, tx⟩ (.cons ⟨hI, 1, tI⟩
      (.cons ⟨val_const 0, 1, c0⟩ (.cons ⟨(val_nFacT hsq.toExact).toNum, 6, tm_nFacT ts hL⟩
        .nil)))))))) hb

/-! ### Dispatch on the tag -/

/-- **The tier of the child dispatch** (`eChildT`) on the reachable entry states: under the bundled
inputs `EIn`, the invariant, the size conditions `SizeOK S L`, an index term of tier `1`, the
network numbers `K`, `V`, `M` and the leaf factors `f0T` of the first clique (as in
`tm_entChildT`), the child code has the tier `d ≤ 29` of any bound on it. -/
theorem tm_eChildT {S : Setup} {nT fwT BT KT VT MT iT : Term} {f0T : Term → Term → Term → Term}
    {f0 : ℕ → ℕ → ℕ → ℕ} {st : St} {i B D d : ℕ}
    (h : EIn S w L env nT fwT BT st B) (hst : EntrySt st) (hinv : S.Inv D st) (hZ : SizeOK S L)
    (hK : Val w env KT S.K) (hV : Val w env VT S.V) (hM : Val w env MT S.G.M)
    (tK : Tm w L 1 KT env) (tV : Tm w L 1 VT env) (tM : Tm w L 1 MT env)
    (hf0v : ∀ a b c A B C, Val w env a A → Val w env b B → Val w env c C →
      Val w env (f0T a b c) (f0 A B C))
    (hf0 : ∀ v < 2 * S.K, ∀ x f, f0 v x f = S.code (.lit (S.factor0 v x f)))
    (hf0t : ∀ fT f, Val w env fT f → Tm w L 1 fT env →
      ∃ d0, Tm w L d0 (f0T (stGetT nT 3) (stGetT nT 4) fT) env)
    (hI : Val w env iT i) (tI : Tm w L 1 iT env) (hd1 : 1 ≤ d) (hd : d ≤ 29)
    (hc : S.code (S.gen.child st i) < 2 ^ (d * L)) :
    Tm w L d (eChildT fwT BT KT VT MT f0T nT iT) env := by
  have hL := h.hL
  have c2 : Tm w L 1 (const 2) env := t_small (by norm_num) (by omega)
  have c3 : Tm w L 1 (const 3) env := t_small (by norm_num) (by omega)
  have c4 : Tm w L 1 (const 4) env := t_const (lit16 (by norm_num) (by omega))
  unfold eChildT
  cases st with
  | cl chs =>
    have f0 := h.field (code_cl S chs) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
      (fun _ => tm_clChildT h hinv hZ hI tI hd1 hd hc) (fun h0 => by simp at h0)
  | last chs j =>
    have f0 := h.field (code_last S chs j) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 3)) (t_eqT' f0.2 c3 (by omega))
        (fun _ => tm_lastChildD h hI tI hd1 hd hc) (fun h0 => by simp at h0))
  | ent chs v args =>
    have f0 := h.field (code_ent S chs v args) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 3)) (t_eqT' f0.2 c3 (by omega))
        (fun h0 => by simp at h0)
        (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega))
          (fun _ => tm_entChildT h hinv hZ hK hV hM tK tV tM hf0v hf0 hf0t hI tI hd1 hd hc)
          (fun h0 => by simp at h0)))
  | rng chs v args ξ lo hb =>
    have f0 := h.field (code_rng S chs v args ξ lo hb) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 3)) (t_eqT' f0.2 c3 (by omega))
        (fun h0 => by simp at h0)
        (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega))
          (fun h0 => by simp at h0) (fun _ => tm_rngChildT h hinv hZ hI tI hd1 hd hc)))
  | _ => exact hst.elim

end Cslib.Complexity.NtimeDspace.Cube.Num
