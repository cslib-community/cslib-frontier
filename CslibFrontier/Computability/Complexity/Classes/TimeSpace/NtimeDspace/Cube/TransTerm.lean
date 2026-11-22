/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.TransNum

/-!
# Programs of the transport machine

Program terms (`ProgTerm.Term`) computing the numeric steps of `TransNum.lean` on the codes of the
transport states, with value lemmas in the style of `CodeTerm.lean` (`Val`: the term is stable and
denotes the numeric function of the values of its arguments) and tier lemmas (`Tm w L d`). Every
term takes stable arguments; no binder is used (`letT`-free list access `hdV`, `tlV`, `dropV`,
`getV`, `consV`, `encV`). The readers of label codes are those of `CodeTerm.lean`.

## Main definitions

* List codes: `getV e k` (entry `k`, `getF`), `encV ts` (the code of a list of terms).
* Sources and weights: `msgPosT`, `srcLenT`, `srcPlT`, `srcTyT`, `srcWtT`, `tWtT`, `trWT`.
* Pivot indices: `pivWT`, `pivOffT`, `pdigT` (the fields), `partOkT`, `leCntT`, `restCntT`,
  `pivL1T`, `pivOkT` (the test `PivOkN`, as `1` or `0`), `restT` (the parts of `T₂`).
* Small terms: `trZzSubT`, `zzAddT`, `plOfT`, `plIdxT`, `xorT'` (`d a b`), `ipT`, `ruleT` (`ruleN`).
* **The steps**: `trTagT`, `trWidthT`, `trLeafT`, `trChildT`, `trmChildT`, `trrChildT`,
  `trChildAllT`.

## Main results

* `val_*`: every term computes its numeric function, for arbitrary stable arguments; in
  particular `val_trChildAllT`, `val_trTagT`, `val_trWidthT`, `val_trLeafT`.
* **`val_tr_agree`**: on the code of a state of `TrInv A B`, the four step terms denote the tag,
  the index length, the leaf value (as `trLeafN`, equal to `gen.leafVal`) and the code of the
  child at every index.
* Tiers: `tm_getV`, `val_tm_encV'`, `tm_srcWtT`, `tm_trWT` (tier `1`), `tm_pdigT`, `tm_pivOkT`,
  `tm_restT`, `tm_ruleT`, and **`tm_tr_agree`**: with the fuel `B` of tier `1` and value at most
  `L` (`10 ≤ L`), the state code of tier `de ≤ 15`, and any index, the tag, index length and leaf
  have tier `1`, and the child has tier `dc` whenever the code of the child is below `2^(dc·L)`
  (`1 ≤ dc ≤ 15`). The intermediate values are bounded through the invariant: all weights are at
  most `A < 2^L` (from `w(A) ≤ B ≤ L`), pivot offsets are below `8L`, and the codes read inside a
  valid pivot index have at most `B` bits.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct

variable {w : List Bool} {env : List ℕ}

/-! ### List codes without binders -/

/-- The head of a list code. -/
def hdV (e : Term) : Term := mod (div e (pow2 (add (tOnesT e) (const 1)))) (pow2 (tOnesT e))

/-- The tail of a list code. -/
def tlV (e : Term) : Term := div e (pow2 (add (add (tOnesT e) (tOnesT e)) (const 1)))

/-- `k` tails of a list code. -/
def dropV (e k : Term) : Term := foldT k e fun acc _ => tlV acc

/-- Entry `k` of a list code. -/
def getV (e k : Term) : Term := hdV (dropV e k)

/-- The cons of list codes. -/
def consV (x l : Term) : Term :=
  add (add (sub (pow2 (sizeT x)) (const 1)) (mul (pow2 (add (sizeT x) (const 1))) x))
    (mul (pow2 (add (add (sizeT x) (sizeT x)) (const 1))) l)

/-- The code of a list of terms. -/
def encV : List Term → Term
  | [] => const 1
  | t :: ts => consV t (encV ts)

section ListVal

variable {e x l k : Term} {E X Lv K : ℕ}

theorem val_tOnesT (he : Val w env e E) : Val w env (tOnesT e) (tOnesF E) :=
  val_foldT he (val_const 0) fun pre x k _ =>
    (val_ite (val_lt (val_acc _ x k) (val_idx _ x k)) (val_acc _ x k)
      (val_ite (val_lt (val_idx _ x k) (val_acc _ x k)) (val_acc _ x k)
        (val_ite (val_bit (he.at2 pre x k) (val_idx _ x k)) (val_add (val_idx _ x k) (val_const 1))
          (val_acc _ x k)))).congr (by unfold tOnesStep; split_ifs <;> simp_all)

theorem val_sizeT (hx : Val w env x X) : Val w env (sizeT x) X.size :=
  (val_foldT hx (val_const 0) fun pre a k _ =>
    (val_ite (val_bit (hx.at2 pre a k) (val_idx _ a k)) (val_add (val_idx _ a k) (val_const 1))
      (val_acc _ a k)).congr (by unfold sizeStep; split_ifs <;> simp_all)).congr (sizeF_eq X)

theorem val_hdV (he : Val w env e E) : Val w env (hdV e) (hdF E) :=
  val_mod (val_div he (val_pow2 (val_add (val_tOnesT he) (val_const 1)))) (val_pow2 (val_tOnesT he))

theorem val_tlV (he : Val w env e E) : Val w env (tlV e) (tlF E) :=
  val_div he (val_pow2 (val_add (val_add (val_tOnesT he) (val_tOnesT he)) (val_const 1)))

theorem foldl_tlF (E : ℕ) : ∀ K, (List.range K).foldl (fun a _ => tlF a) E = dropF K E
  | 0 => rfl
  | K + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_tlF E K, dropF, dropF,
      Function.iterate_succ_apply']
    rfl

theorem val_dropV (he : Val w env e E) (hk : Val w env k K) : Val w env (dropV e k) (dropF K E) :=
  (val_foldT hk he fun _ a b _ => val_tlV (val_acc _ a b)).congr (foldl_tlF E K)

theorem val_getV (he : Val w env e E) (hk : Val w env k K) : Val w env (getV e k) (getF E K) :=
  val_hdV (val_dropV he hk)

theorem val_consV (hx : Val w env x X) (hl : Val w env l Lv) : Val w env (consV x l) (consF X Lv) :=
  (val_add (val_add (val_sub (val_pow2 (val_sizeT hx)) (val_const 1))
    (val_mul (val_pow2 (val_add (val_sizeT hx) (val_const 1))) hx))
    (val_mul (val_pow2 (val_add (val_add (val_sizeT hx) (val_sizeT hx)) (val_const 1))) hl)).congr
    (by rw [consF, sizeF_eq])

theorem val_encV_cons {t : Term} {ts : List Term} {T : ℕ} {Ts : List ℕ} (ht : Val w env t T)
    (hts : Val w env (encV ts) (NatList.enc Ts)) : Val w env (encV (t :: ts))
        (NatList.enc (T :: Ts)) :=
  (val_consV ht hts).congr (consF_enc T Ts)

theorem val_encV_nil : Val w env (encV []) (NatList.enc []) := val_const 1

end ListVal

/-! ### Sources and weights -/

/-- `msgPos`. -/
def msgPosT (B up M : Term) : Term := ite (eqT up (const 1)) (msEndT B M (const 0)) (const 0)

/-- `srcLenN`. -/
def srcLenT (B up X Y M : Term) : Term :=
  add (add (cardT B X (const 0)) (cardT B Y (const 0))) (cardT B M (msgPosT B up M))

/-- `srcPlN`. -/
def srcPlT (B X Y k : Term) : Term :=
  ite (lt k (cardT B X (const 0))) (const 0)
    (ite (lt k (add (cardT B X (const 0)) (cardT B Y (const 0)))) (const 1) (const 2))

/-- `srcTyN`. -/
def srcTyT (B up X Y M k : Term) : Term :=
  ite (lt k (cardT B X (const 0))) (kthT B X (const 0) k (const 0))
    (ite (lt k (add (cardT B X (const 0)) (cardT B Y (const 0))))
      (kthT B Y (const 0) (sub k (cardT B X (const 0))) (const 0))
      (kthT B M (msgPosT B up M) (sub (sub k (cardT B X (const 0))) (cardT B Y (const 0)))
          (const 0)))

/-- `srcWtN`. -/
def srcWtT (B up X Y M lo hi : Term) : Term :=
  sumT (sub hi lo) fun k =>
    ite (lt (add lo k) (srcLenT B up X Y M)) (add (srcTyT B up X Y M (add lo k)) (const 1))
        (const 0)

/-- `tWtN`. -/
def tWtT (B Tc : Term) : Term :=
  add (add (wtT B (getV Tc (const 0)) (const 0)) (wtT B (getV Tc (const 1)) (const 0)))
    (wtT B (getV Tc (const 2)) (const 0))

/-- `trWN`. -/
def trWT (B up X Y M lo hi Tc : Term) : Term := add (srcWtT B up X Y M lo hi) (tWtT B Tc)

section SrcVal

variable {B up X Y M k lo hi Tc : Term} {Bv upv Xv Yv Mv kv lov hiv Tcv : ℕ}

theorem val_msgPosT (hB : Val w env B Bv) (hup : Val w env up upv) (hM : Val w env M Mv) :
    Val w env (msgPosT B up M) (msgPos Bv upv Mv) :=
  (val_ite (val_eqT hup (val_const 1)) (val_msEndT hB hM (val_const 0)) (val_const 0)).congr
    (by unfold msgPos; split_ifs <;> simp_all)

theorem val_srcLenT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) :
    Val w env (srcLenT B up X Y M) (srcLenN Bv upv Xv Yv Mv) :=
  val_add (val_add (val_cardT hB hX (val_const 0)) (val_cardT hB hY (val_const 0)))
    (val_cardT hB hM (val_msgPosT hB hup hM))

theorem val_srcPlT (hB : Val w env B Bv) (hX : Val w env X Xv) (hY : Val w env Y Yv)
    (hk : Val w env k kv) : Val w env (srcPlT B X Y k) (srcPlN Bv Xv Yv kv) :=
  (val_ite (val_lt hk (val_cardT hB hX (val_const 0))) (val_const 0)
    (val_ite (val_lt hk (val_add (val_cardT hB hX (val_const 0)) (val_cardT hB hY (val_const 0))))
      (val_const 1) (val_const 2))).congr (by unfold srcPlN; split_ifs <;> simp_all)

theorem val_srcTyT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (hk : Val w env k kv) :
    Val w env (srcTyT B up X Y M k) (srcTyN Bv upv Xv Yv Mv kv) := by
  have c1 := val_cardT hB hX (val_const 0)
  have c2 := val_cardT hB hY (val_const 0)
  exact (val_ite (val_lt hk c1) (val_kthT hB hX (val_const 0) hk (val_const 0))
    (val_ite (val_lt hk (val_add c1 c2))
        (val_kthT hB hY (val_const 0) (val_sub hk c1) (val_const 0))
      (val_kthT hB hM (val_msgPosT hB hup hM) (val_sub (val_sub hk c1) c2) (val_const 0)))).congr
    (by unfold srcTyN; split_ifs <;> simp_all)

theorem val_srcWtT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (hlo : Val w env lo lov) (hhi : Val w env hi hiv) :
    Val w env (srcWtT B up X Y M lo hi) (srcWtN Bv upv Xv Yv Mv lov hiv) :=
  val_sumT (val_sub hhi hlo) fun pre a k _ => by
    have hk := val_add (hlo.at2 pre a k) (val_idx _ a k)
    exact (val_ite (val_lt hk (val_srcLenT (hB.at2 pre a k) (hup.at2 pre a k) (hX.at2 pre a k)
      (hY.at2 pre a k) (hM.at2 pre a k)))
      (val_add (val_srcTyT (hB.at2 pre a k) (hup.at2 pre a k) (hX.at2 pre a k) (hY.at2 pre a k)
        (hM.at2 pre a k) hk) (val_const 1)) (val_const 0)).congr (by split_ifs <;> simp_all)

theorem val_tWtT (hB : Val w env B Bv) (hT : Val w env Tc Tcv) : Val w env (tWtT B Tc)
    (tWtN Bv Tcv) :=
  val_add (val_add (val_wtT hB (val_getV hT (val_const 0)) (val_const 0))
    (val_wtT hB (val_getV hT (val_const 1)) (val_const 0)))
    (val_wtT hB (val_getV hT (val_const 2)) (val_const 0))

theorem val_trWT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (hlo : Val w env lo lov) (hhi : Val w env hi hiv)
    (hT : Val w env Tc Tcv) :
    Val w env (trWT B up X Y M lo hi Tc) (trWN Bv upv Xv Yv Mv lov hiv Tcv) :=
  val_add (val_srcWtT hB hup hX hY hM hlo hhi) (val_tWtT hB hT)

end SrcVal


/-! ### Tests -/

/-- `a ≤ b` as `1` or `0`. -/
def trLeT (a b : Term) : Term := lt a (add b (const 1))

/-- A conjunction of tests. -/
def trAndT (a b : Term) : Term := mul a b

section TestVal

variable {a b : Term} {A B' : ℕ}

theorem val_trLeT (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (trLeT a b) (if A ≤ B' then 1 else 0) :=
  (val_lt ha (val_add hb (val_const 1))).congr (by split_ifs <;> omega)

theorem val_lt' (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (lt a b) (if A < B' then 1 else 0) := val_lt ha hb

theorem val_trAndT {p q : Prop} [Decidable p] [Decidable q] (ha : Val w env a (if p then 1 else 0))
    (hb : Val w env b (if q then 1 else 0)) : Val w env (trAndT a b) (if p ∧ q then 1 else 0) :=
  (val_mul ha hb).congr (by by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq])

theorem val_eqT' (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (eqT a b) (if A = B' then 1 else 0) := val_eqT ha hb

theorem forall_lt_three {P : ℕ → Prop} : (∀ k < 3, P k) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega)⟩
  · rintro ⟨h0, h1, h2⟩ k hk; interval_cases k <;> assumption

end TestVal

/-! ### Pivot fields and the pivot test -/

/-- The width of field `j` of a pivot code. -/
def pivWT (W : Term) : ℕ → Term
  | 0 => sizeT W
  | 1 => sizeT (add (mul (const 3) W) (const 3))
  | 2 | 3 | 4 => codeWidthT W
  | _ => sizeT (mul (const 2) W)

/-- The offset of field `j` of a pivot code. -/
def pivOffT (W : Term) : ℕ → Term
  | 0 => const 0
  | j + 1 => add (pivOffT W j) (pivWT W j)

/-- Field `j` of a pivot index. -/
def pdigT (W i : Term) (j : ℕ) : Term := mod (div i (pow2 (pivOffT W j))) (pow2 (pivWT W j))

/-- `PartOkN`. -/
def partOkT (B W d : Term) : Term :=
  trAndT (eqT (validT W (codeWidthT W) d) (const 1))
      (eqT (wtT B d (msEndT B d (const 0))) (const 0))

/-- `leCntN`. -/
def leCntT (B c q : Term) (cnt : Term → Term) : Term :=
  msFoldT (fun a e μ => ite (lt (cnt e) μ) (const 0) a) (const 1) B c q

/-- `restCnt`. -/
def restCntT (B Tc p j : Term) (k : ℕ) : Term → Term := fun e =>
  sub (countT B (getV Tc (const k)) (const 0) e)
      (ite (mul (eqT (const k) p) (eqT e j)) (const 1) (const 0))

/-- `pivL1N`. -/
def pivL1T (B up X Y M lo W i : Term) : Term :=
  add (add (add (srcWtT B up X Y M lo (add lo (pdigT W i 0))) (wtT B (pdigT W i 2) (const 0)))
    (wtT B (pdigT W i 3) (const 0))) (wtT B (pdigT W i 4) (const 0))

/-- `PivOkN`, as `1` or `0`. -/
def pivOkT (B up X Y M lo hi Tc W i : Term) : Term :=
  trAndT (trAndT (lt i (pow2 (pivOffT W 7))) (trAndT (partOkT B W (pdigT W i 2))
      (trAndT (partOkT B W (pdigT W i 3)) (partOkT B W (pdigT W i 4)))))
    (trAndT (lt (pdigT W i 0) (cminT (sub hi lo) (sub (srcLenT B up X Y M) lo)))
    (trAndT (lt (const 0) (countT B (getV Tc (mod (pdigT W i 1) (const 3))) (const 0)
        (div (pdigT W i 1) (const 3))))
    (trAndT (trAndT (eqT (leCntT B (pdigT W i 2) (const 0)
          (restCntT B Tc (mod (pdigT W i 1) (const 3)) (div (pdigT W i 1) (const 3)) 0)) (const 1))
        (trAndT (eqT (leCntT B (pdigT W i 3) (const 0)
          (restCntT B Tc (mod (pdigT W i 1) (const 3)) (div (pdigT W i 1) (const 3)) 1)) (const 1))
        (eqT (leCntT B (pdigT W i 4) (const 0)
          (restCntT B Tc (mod (pdigT W i 1) (const 3)) (div (pdigT W i 1) (const 3)) 2))
              (const 1))))
    (trAndT (trAndT (lt (mul (const 2) (pivL1T B up X Y M lo W i)) W)
        (trLeT W (mul (const 2) (add (add (pivL1T B up X Y M lo W i)
          (add (srcTyT B up X Y M (add lo (pdigT W i 0))) (const 1)))
          (add (div (pdigT W i 1) (const 3)) (const 1))))))
    (trAndT (trLeT (pdigT W i 5) (mul (const 2) W)) (trLeT (pdigT W i 6) (mul (const 2) W)))))))

/-- `restN`. -/
def restT (B Tc p j : Term) (k : ℕ) (dk : Term) : Term :=
  ocCodeT B (topT B (getV Tc (const k)) (const 0)) fun e =>
    sub (sub (countT B (getV Tc (const k)) (const 0) e) (countT B dk (const 0) e))
      (ite (mul (eqT (const k) p) (eqT e j)) (const 1) (const 0))

section PivVal

variable {B up X Y M lo hi Tc W i d p j : Term} {Bv upv Xv Yv Mv lov hiv Tcv Wv iv dv pv jv : ℕ}

theorem val_pivWT (hW : Val w env W Wv) (j : ℕ) : Val w env (pivWT W j) (pivW Wv j) := by
  rcases j with _ | _ | _ | _ | _ | j
  · exact (val_sizeT hW).congr (by simp [pivW])
  · exact (val_sizeT (val_add (val_mul (val_const 3) hW) (val_const 3))).congr (by simp [pivW])
  · exact (val_codeWidthT hW).congr (by simp [pivW])
  · exact (val_codeWidthT hW).congr (by simp [pivW])
  · exact (val_codeWidthT hW).congr (by simp [pivW])
  · exact (val_sizeT (val_mul (val_const 2) hW)).congr (by unfold pivW; simp)

theorem val_pivOffT (hW : Val w env W Wv) : ∀ j, Val w env (pivOffT W j) (Radix.off (pivW Wv) j)
  | 0 => (val_const 0).congr (by simp)
  | j +
      1 => (val_add (val_pivOffT hW j) (val_pivWT hW j)).congr (by simp [Radix.off, Finset.sum_range_succ])

theorem val_pdigT (hW : Val w env W Wv) (hi : Val w env i iv) (j : ℕ) :
    Val w env (pdigT W i j) (Radix.dig (pivW Wv) iv j) :=
  val_mod (val_div hi (val_pow2 (val_pivOffT hW j))) (val_pow2 (val_pivWT hW j))

theorem val_partOkT (hB : Val w env B Bv) (hW : Val w env W Wv) (hd : Val w env d dv) :
    Val w env (partOkT B W d) (if PartOkN Bv Wv dv then 1 else 0) :=
  (val_trAndT (val_eqT (val_validT hW (val_codeWidthT hW) hd) (val_const 1))
    (val_eqT (val_wtT hB hd (val_msEndT hB hd (val_const 0))) (val_const 0))).congr (by rfl)

theorem val_leCntT {c q : Term} {cv qv : ℕ} {cnt : Term → Term} {C : ℕ → ℕ}
    (hcnt : ValF1 w cnt C env)
    (hB : Val w env B Bv) (hc : Val w env c cv) (hq : Val w env q qv) :
    Val w env (leCntT B c q cnt) (leCntN Bv cv qv C) :=
  val_msFoldT (G := fun a e μ => if μ ≤ C e then a else 0)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_lt (hcnt pre _ _ he) hμ) (val_const 0) hx).congr
      (by dsimp only; split_ifs <;> first | rfl | omega)) (val_const 1) hB hc hq

theorem valF1_restCntT (hB : Val w env B Bv) (hT : Val w env Tc Tcv) (hp : Val w env p pv)
    (hj : Val w env j jv) (k : ℕ) : ValF1 w (restCntT B Tc p j k) (restCnt Bv Tcv pv jv k) env :=
  fun pre _ _ hy => (val_sub (val_countT (hB.ext pre) (val_getV (hT.ext pre) (val_const k))
    (val_const 0) hy) (val_ite (val_mul (val_eqT (val_const k) (hp.ext pre))
        (val_eqT hy (hj.ext pre)))
      (val_const 1) (val_const 0))).congr (by unfold restCnt; congr 1; split_ifs <;> simp_all)

theorem val_pivL1T (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (hlo : Val w env lo lov) (hW : Val w env W Wv)
    (hi : Val w env i iv) : Val w env (pivL1T B up X Y M lo W i)
        (pivL1N Bv upv Xv Yv Mv lov Wv iv) :=
  val_add (val_add (val_add (val_srcWtT hB hup hX hY hM hlo (val_add hlo (val_pdigT hW hi 0)))
    (val_wtT hB (val_pdigT hW hi 2) (val_const 0))) (val_wtT hB (val_pdigT hW hi 3) (val_const 0)))
    (val_wtT hB (val_pdigT hW hi 4) (val_const 0))

theorem val_pivOkT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (hlo : Val w env lo lov) (hhi : Val w env hi hiv)
    (hT : Val w env Tc Tcv) (hW : Val w env W Wv) (hix : Val w env i iv) :
    Val w env (pivOkT B up X Y M lo hi Tc W i)
      (if PivOkN Bv upv Xv Yv Mv lov hiv Tcv Wv iv then 1 else 0) := by
  have d1 := val_pdigT hW hix 1
  have hp := val_mod d1 (val_const 3)
  have hj := val_div d1 (val_const 3)
  have L1 := val_pivL1T hB hup hX hY hM hlo hW hix
  refine (val_trAndT (val_trAndT (val_lt' hix (val_pow2 (val_pivOffT hW 7)))
      (val_trAndT (val_partOkT hB hW (val_pdigT hW hix 2))
        (val_trAndT (val_partOkT hB hW (val_pdigT hW hix 3))
            (val_partOkT hB hW (val_pdigT hW hix 4)))))
    (val_trAndT (val_lt' (val_pdigT hW hix 0) (val_cminT (val_sub hhi hlo)
        (val_sub (val_srcLenT hB hup hX hY hM) hlo)))
    (val_trAndT (val_lt' (val_const 0) (val_countT hB (val_getV hT hp) (val_const 0) hj))
    (val_trAndT (val_trAndT (val_eqT' (val_leCntT (valF1_restCntT hB hT hp hj 0) hB
        (val_pdigT hW hix 2)
          (val_const 0)) (val_const 1))
        (val_trAndT (val_eqT' (val_leCntT (valF1_restCntT hB hT hp hj 1) hB (val_pdigT hW hix 3)
          (val_const 0)) (val_const 1))
        (val_eqT' (val_leCntT (valF1_restCntT hB hT hp hj 2) hB (val_pdigT hW hix 4)
          (val_const 0)) (val_const 1))))
    (val_trAndT (val_trAndT (val_lt' (val_mul (val_const 2) L1) hW)
        (val_trLeT hW (val_mul (val_const 2) (val_add (val_add L1
          (val_add (val_srcTyT hB hup hX hY hM (val_add hlo (val_pdigT hW hix 0))) (val_const 1)))
          (val_add hj (val_const 1))))))
    (val_trAndT (val_trLeT (val_pdigT hW hix 5) (val_mul (val_const 2) hW))
      (val_trLeT (val_pdigT hW hix 6) (val_mul (val_const 2) hW)))))))).congr ?_
  refine if_congr ?_ rfl rfl
  unfold PivOkN
  rw [forall_lt_three, pivWidth_eq]

theorem val_restT (hB : Val w env B Bv) (hT : Val w env Tc Tcv) (hp : Val w env p pv)
    (hj : Val w env j jv) (k : ℕ) (hd : Val w env d dv) :
    Val w env (restT B Tc p j k d) (restN Bv Tcv pv jv k dv) :=
  val_ocCodeT hB (val_topT hB (val_getV hT (val_const k)) (val_const 0)) fun pre _ _ hy =>
    (val_sub (val_sub (val_countT (hB.ext pre) (val_getV (hT.ext pre) (val_const k)) (val_const 0)
        hy)
      (val_countT (hB.ext pre) (hd.ext pre) (val_const 0) hy))
      (val_ite (val_mul (val_eqT (val_const k) (hp.ext pre)) (val_eqT hy (hj.ext pre)))
        (val_const 1) (val_const 0))).congr (by congr 1; split_ifs <;> simp_all)

end PivVal


/-! ### Integers, places and conditionals -/

/-- `zzSubN`. -/
def trZzSubT (a b : Term) : Term :=
  ite (lt a b) (sub (mul (const 2) (sub b a)) (const 1)) (mul (const 2) (sub a b))

/-- `zzAddN`. -/
def zzAddT (z a b : Term) : Term :=
  ite (mod z (const 2)) (trZzSubT a (add b (div (add z (const 1)) (const 2))))
    (trZzSubT (add (div z (const 2)) a) b)

/-- `plOfN`. -/
def plOfT (up p : Term) : Term :=
  ite (eqT p (const 0)) (ite (eqT up (const 1)) (const 1) (const 3))
    (ite (eqT p (const 1)) (ite (eqT up (const 1)) (const 2) (const 4)) (const 0))

/-- `¬`, on `1` or `0`. -/
def notT (a : Term) : Term := sub (const 1) a

/-- `∨`, on `1` or `0`. -/
def orT (a b : Term) : Term := lt (const 0) (add a b)

/-- `plIdxN`. -/
def plIdxT (pn : Term) : Term :=
  ite (eqT pn (const 0)) (const 2)
    (ite (orT (eqT pn (const 1)) (eqT pn (const 3))) (const 0) (const 1))

section SmallVal

variable {a b z c t e : Term} {A B' Z T E : ℕ}

theorem val_iteP {P : Prop} [Decidable P] (hc : Val w env c (if P then 1 else 0))
    (ht : Val w env t T)
    (he : Val w env e E) : Val w env (ite c t e) (if P then T else E) :=
  (val_ite hc ht he).congr (by by_cases hP : P <;> simp [hP])

theorem val_iteProp {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (hc : Val w env c (if P then 1 else 0)) (ht : Val w env t (if Q then 1 else 0))
    (he : Val w env e (if R then 1 else 0)) :
    Val w env (ite c t e) (if (if P then Q else R) then 1 else 0) :=
  (val_ite hc ht he).congr (by by_cases hP : P <;> simp [hP])

theorem val_notT {P : Prop} [Decidable P] (ha : Val w env a (if P then 1 else 0)) :
    Val w env (notT a) (if ¬ P then 1 else 0) :=
  (val_sub (val_const 1) ha).congr (by by_cases hP : P <;> simp [hP])

theorem val_orT {P Q : Prop} [Decidable P] [Decidable Q] (ha : Val w env a (if P then 1 else 0))
    (hb : Val w env b (if Q then 1 else 0)) : Val w env (orT a b) (if P ∨ Q then 1 else 0) :=
  (val_lt (val_const 0) (val_add ha hb)).congr
      (by by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ])

theorem val_trZzSubT (ha : Val w env a A) (hb : Val w env b B') : Val w env (trZzSubT a b)
    (zzSubN A B') :=
  (val_ite (val_lt ha hb) (val_sub (val_mul (val_const 2) (val_sub hb ha)) (val_const 1))
    (val_mul (val_const 2) (val_sub ha hb))).congr (by unfold zzSubN; split_ifs <;> omega)

theorem val_zzAddT (hz : Val w env z Z) (ha : Val w env a A) (hb : Val w env b B') :
    Val w env (zzAddT z a b) (zzAddN Z A B') :=
  (val_ite (val_mod hz (val_const 2))
    (val_trZzSubT ha (val_add hb (val_div (val_add hz (val_const 1)) (val_const 2))))
    (val_trZzSubT (val_add (val_div hz (val_const 2)) ha) hb)).congr
    (by unfold zzAddN; split_ifs <;> first | rfl | omega)

theorem val_plOfT (ha : Val w env a A) (hb : Val w env b B') : Val w env (plOfT a b) (plOfN A B') :=
  (val_iteP (val_eqT hb (val_const 0)) (val_iteP (val_eqT ha (val_const 1)) (val_const 1)
      (val_const 3))
    (val_iteP (val_eqT hb (val_const 1))
        (val_iteP (val_eqT ha (val_const 1)) (val_const 2) (val_const 4))
      (val_const 0))).congr rfl

theorem val_plIdxT (ha : Val w env a A) : Val w env (plIdxT a) (plIdxN A) :=
  (val_iteP (val_eqT ha (val_const 0)) (val_const 2)
    (val_iteP (val_orT (val_eqT ha (val_const 1)) (val_eqT ha (val_const 3))) (val_const 0)
      (val_const 1))).congr rfl

end SmallVal

/-! ### Exclusive or and common bits -/

/-- `d a b = a ^^^ b`, over the bits below the size of `a + b`. -/
def xorT' (a b : Term) : Term :=
  sumT (sizeT (add a b)) fun e => mul (pow2 e) (mod (add (bit a e) (bit b e)) (const 2))

/-- `ip a b`. -/
def ipT (a b : Term) : Term := sumT (add a (const 1)) fun e => mul (bit a e) (bit b e)

theorem xor_mod_two_pow (a b : ℕ) : ∀ K, (a ^^^ b) % 2 ^ K =
    ∑ e ∈ Finset.range K, 2 ^ e * (((a.testBit e).toNat + (b.testBit e).toNat) % 2)
  | 0 => by rw [pow_zero, Nat.mod_one, Finset.sum_range_zero]
  | K + 1 => by
    rw [Nat.mod_pow_succ, xor_mod_two_pow a b K, Finset.sum_range_succ, ← Nat.toNat_testBit,
      Nat.testBit_xor]
    congr 2
    cases a.testBit K <;> cases b.testBit K <;> rfl

theorem xor_eq_sum (a b : ℕ) : a ^^^ b =
    ∑ e ∈ Finset.range (a + b).size, 2 ^ e * (((a.testBit e).toNat + (b.testBit e).toNat) % 2) := by
  have h := NatList.lt_two_pow_size (a + b)
  rw [← xor_mod_two_pow, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by omega) (by omega))]

theorem ip_eq_sum (a b : ℕ) : ip a b = ∑ e ∈ Finset.range (a + 1), (a.testBit e).toNat *
    (b.testBit e).toNat := by
  rw [ip, Finset.card_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  cases a.testBit e <;> cases b.testBit e <;> rfl

section BitVal

variable {a b : Term} {A B' : ℕ}

theorem val_xorT' (ha : Val w env a A) (hb : Val w env b B') : Val w env (xorT' a b) (d A B') := by
  have h : Val w env (xorT' a b) (∑ e ∈ Finset.range (A + B').size,
      2 ^ e * (((A.testBit e).toNat + (B'.testBit e).toNat) % 2)) :=
    val_sumT (body := fun e => mul (pow2 e) (mod (add (bit a e) (bit b e)) (const 2)))
      (val_sizeT (val_add ha hb)) fun pre x k _ =>
      val_mul (val_pow2 (val_idx _ x k))
          (val_mod (val_add (val_bit (ha.at2 pre x k) (val_idx _ x k))
        (val_bit (hb.at2 pre x k) (val_idx _ x k))) (val_const 2))
  exact h.congr (xor_eq_sum A B').symm

theorem val_ipT (ha : Val w env a A) (hb : Val w env b B') : Val w env (ipT a b) (ip A B') := by
  have h : Val w env (ipT a b) (∑ e ∈ Finset.range (A + 1), (A.testBit e).toNat *
      (B'.testBit e).toNat) :=
    val_sumT (body := fun e => mul (bit a e) (bit b e)) (val_add ha (val_const 1)) fun pre x k _ =>
      val_mul (val_bit (ha.at2 pre x k) (val_idx _ x k)) (val_bit (hb.at2 pre x k) (val_idx _ x k))
  exact h.congr (ip_eq_sum A B').symm

end BitVal

/-! ### The rule coefficients and the children -/

/-- `ruleN`. -/
def ruleT (up ps i pt j z : Term) : Term :=
  ite (eqT ps pt) (const 0)
    (ite (trAndT (notT (eqT ps (const 2))) (notT (eqT pt (const 2))))
      (ite (eqT up (const 1))
        (ite (eqT z (trZzSubT (const 0) (xorT' i j)))
          (ite (eqT (mod (ipT i j) (const 2)) (const 0)) (const 2) (const 1))
          (ite (eqT z (add (mul (const 2) (xorT' i j)) (const 3)))
            (ite (eqT (mod (ipT i j) (const 2)) (const 0)) (const 1) (const 2)) (const 0)))
        (ite (eqT z (trZzSubT (const 0) (xorT' i j)))
          (ite (eqT (mod (ipT i j) (const 2)) (const 0)) (const 2) (const 1)) (const 0)))
      (ite (ite (eqT up (const 1)) (orT (eqT ps (const 0)) (eqT pt (const 0)))
          (orT (eqT ps (const 1)) (eqT pt (const 1))))
        (ite (eqT up (const 1))
          (ite (eqT z (mul (const 2) (xorT' i j)))
            (ite (eqT (mod (ipT i j) (const 2)) (const 0)) (const 2) (const 1))
            (ite (eqT z (add (mul (const 2) (xorT' i j)) (const 4)))
              (ite (eqT (mod (ipT i j) (const 2)) (const 0)) (const 1) (const 2)) (const 0)))
          (ite (eqT z (mul (const 2) (xorT' i j)))
            (ite (eqT (mod (ipT i j) (const 2)) (const 0)) (const 2) (const 1)) (const 0)))
        (ite (trAndT (eqT i j) (eqT z (const 0))) (const 2) (const 0))))

/-- `trChildN`. -/
def trChildT (B e i : Term) : Term :=
  let up := getV e (const 1); let X := getV e (const 2); let Y := getV e (const 3)
  let M := getV e (const 4); let lo := getV e (const 5); let hi := getV e (const 6)
  let Tc := getV e (const 7)
  let W := trWT B up X Y M lo hi Tc
  let p := mod (pdigT W i 1) (const 3); let j := div (pdigT W i 1) (const 3)
  ite (pivOkT B up X Y M lo hi Tc W i)
    (encV [const 8, up, X, Y, M, lo, add lo (pdigT W i 0), hi, add (plOfT up p) (mul (const 8) j),
      encV [mod (pdigT W i 2) (pow2 (cminT (msEndT B (pdigT W i 2) (const 0)) B)),
        mod (pdigT W i 3) (pow2 (cminT (msEndT B (pdigT W i 3) (const 0)) B)),
        mod (pdigT W i 4) (pow2 (cminT (msEndT B (pdigT W i 4) (const 0)) B))],
      encV [restT B Tc p j 0 (pdigT W i 2), restT B Tc p j 1 (pdigT W i 3), restT B Tc p j 2
          (pdigT W i 4)],
      trZzSubT (pdigT W i 5) W, trZzSubT (pdigT W i 6) W,
      zzAddT (getV e (const 8)) (mul (const 2) W) (add (pdigT W i 5) (pdigT W i 6))])
    (encV [const 0])

/-- `trmChildN`. -/
def trmChildT (e b : Term) : Term :=
  ite (eqT b (const 0))
    (encV [const 7, getV e (const 1), getV e (const 2), getV e (const 3), getV e (const 4),
      getV e (const 5), getV e (const 6), getV e (const 9), getV e (const 11)])
    (encV [const 9, getV e (const 1), getV e (const 2), getV e (const 3), getV e (const 4),
      getV e (const 6), getV e (const 7), getV e (const 8), getV e (const 10), getV e (const 12),
      getV e (const 13)])

/-- `trrChildN`. -/
def trrChildT (B e b : Term) : Term :=
  let up := getV e (const 1); let X := getV e (const 2); let Y := getV e (const 3)
  let M := getV e (const 4); let pos := getV e (const 5); let tn := getV e (const 7)
  ite (eqT b (const 0))
    (encV [const 1, ruleT up
      (ite (lt pos (srcLenT B up X Y M)) (srcPlT B X Y pos) (plIdxT (mod tn (const 8))))
      (ite (lt pos (srcLenT B up X Y M)) (srcTyT B up X Y M pos) (div tn (const 8)))
      (plIdxT (mod tn (const 8))) (div tn (const 8)) (getV e (const 9))])
    (encV [const 7, up, X, Y, M, add pos (const 1), getV e (const 6), getV e (const 8),
      getV e (const 10)])

/-- `trTagN`. -/
def trTagT (e : Term) : Term :=
  ite (eqT (getV e (const 0)) (const 7)) (lt (getV e (const 5)) (getV e (const 6))) (const 2)

/-- `trWidthN`. -/
def trWidthT (B e : Term) : Term :=
  ite (eqT (getV e (const 0)) (const 7))
    (pivOffT (trWT B (getV e (const 1)) (getV e (const 2)) (getV e (const 3)) (getV e (const 4))
      (getV e (const 5)) (getV e (const 6)) (getV e (const 7))) 7) (const 0)

/-- `trLeafN`. -/
def trLeafT (B e : Term) : Term :=
  trAndT (eqT (getV e (const 0)) (const 7))
    (trAndT (eqT (cardT B (getV (getV e (const 7)) (const 0)) (const 0)) (const 0))
    (trAndT (eqT (cardT B (getV (getV e (const 7)) (const 1)) (const 0)) (const 0))
    (trAndT (eqT (cardT B (getV (getV e (const 7)) (const 2)) (const 0)) (const 0))
      (eqT (getV e (const 8)) (const 0)))))

/-- **`trChildAllN`**: the child of a transport state. -/
def trChildAllT (B e i : Term) : Term :=
  ite (eqT (getV e (const 0)) (const 7)) (trChildT B e i)
    (ite (eqT (getV e (const 0)) (const 8)) (trmChildT e i) (trrChildT B e i))

section ChildVal

variable {B e i up ps a pt b z : Term} {Bv ev iv upv psv av ptv bv zv : ℕ}

theorem val_ruleT (hup : Val w env up upv) (hps : Val w env ps psv) (ha : Val w env a av)
    (hpt : Val w env pt ptv) (hb : Val w env b bv) (hz : Val w env z zv) :
    Val w env (ruleT up ps a pt b z) (ruleN upv psv av ptv bv zv) := by
  have hx := val_xorT' ha hb
  have hpar := val_eqT (val_mod (val_ipT ha hb) (val_const 2)) (val_const 0)
  have hpos := val_iteP hpar (val_const 2) (val_const 1)
  have hneg := val_iteP hpar (val_const 1) (val_const 2)
  have hu := val_eqT hup (val_const 1)
  exact (val_iteP (val_eqT hps hpt) (val_const 0)
    (val_iteP (val_trAndT (val_notT (val_eqT hps (val_const 2)))
        (val_notT (val_eqT hpt (val_const 2))))
      (val_iteP hu
        (val_iteP (val_eqT hz (val_trZzSubT (val_const 0) hx)) hpos
          (val_iteP (val_eqT hz (val_add (val_mul (val_const 2) hx) (val_const 3))) hneg
              (val_const 0)))
        (val_iteP (val_eqT hz (val_trZzSubT (val_const 0) hx)) hpos (val_const 0)))
      (val_iteP (val_iteProp hu (val_orT (val_eqT hps (val_const 0)) (val_eqT hpt (val_const 0)))
          (val_orT (val_eqT hps (val_const 1)) (val_eqT hpt (val_const 1))))
        (val_iteP hu
          (val_iteP (val_eqT hz (val_mul (val_const 2) hx)) hpos
            (val_iteP (val_eqT hz (val_add (val_mul (val_const 2) hx) (val_const 4))) hneg
                (val_const 0)))
          (val_iteP (val_eqT hz (val_mul (val_const 2) hx)) hpos (val_const 0)))
        (val_iteP (val_trAndT (val_eqT ha hb) (val_eqT hz (val_const 0))) (val_const 2)
            (val_const 0))))).congr
    rfl

theorem val_trChildT (hB : Val w env B Bv) (he : Val w env e ev) (hix : Val w env i iv) :
    Val w env (trChildT B e i) (trChildN Bv ev iv) := by
  have f : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  have hW := val_trWT hB (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  have dg := fun j => val_pdigT hW hix j
  have hp := val_mod (dg 1) (val_const 3)
  have hj := val_div (dg 1) (val_const 3)
  have m3 := fun j => val_mod (dg j) (val_pow2 (val_cminT (val_msEndT hB (dg j) (val_const 0)) hB))
  refine (val_iteP (val_pivOkT hB (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) hW hix)
    (val_encV_cons (val_const 8) (val_encV_cons (f 1) (val_encV_cons (f 2) (val_encV_cons (f 3)
      (val_encV_cons (f 4) (val_encV_cons (f 5) (val_encV_cons (val_add (f 5) (dg 0))
      (val_encV_cons (f 6) (val_encV_cons (val_add (val_plOfT (f 1) hp) (val_mul (val_const 8) hj))
      (val_encV_cons (val_encV_cons (m3 2)
          (val_encV_cons (m3 3) (val_encV_cons (m3 4) val_encV_nil)))
      (val_encV_cons (val_encV_cons (val_restT hB (f 7) hp hj 0 (dg 2)) (val_encV_cons
        (val_restT hB (f 7) hp hj 1 (dg 3)) (val_encV_cons (val_restT hB (f 7) hp hj 2 (dg 4))
          val_encV_nil)))
      (val_encV_cons (val_trZzSubT (dg 5) hW) (val_encV_cons (val_trZzSubT (dg 6) hW)
      (val_encV_cons (val_zzAddT (f 8) (val_mul (val_const 2) hW) (val_add (dg 5) (dg 6)))
        val_encV_nil))))))))))))))
    (val_encV_cons (val_const 0) val_encV_nil)).congr rfl

theorem val_trmChildT (he : Val w env e ev) (hb : Val w env b bv) :
    Val w env (trmChildT e b) (trmChildN ev bv) := by
  have f : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  exact (val_iteP (val_eqT hb (val_const 0))
    (val_encV_cons (val_const 7) (val_encV_cons (f 1) (val_encV_cons (f 2) (val_encV_cons (f 3)
      (val_encV_cons (f 4) (val_encV_cons (f 5) (val_encV_cons (f 6) (val_encV_cons (f 9)
      (val_encV_cons (f 11) val_encV_nil)))))))))
    (val_encV_cons (val_const 9) (val_encV_cons (f 1) (val_encV_cons (f 2) (val_encV_cons (f 3)
      (val_encV_cons (f 4) (val_encV_cons (f 6) (val_encV_cons (f 7) (val_encV_cons (f 8)
      (val_encV_cons (f 10) (val_encV_cons (f 12)
          (val_encV_cons (f 13) val_encV_nil)))))))))))).congr rfl

theorem val_trrChildT (hB : Val w env B Bv) (he : Val w env e ev) (hb : Val w env b bv) :
    Val w env (trrChildT B e b) (trrChildN Bv ev bv) := by
  have f : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  have hl := val_srcLenT hB (f 1) (f 2) (f 3) (f 4)
  have hpt := val_plIdxT (val_mod (f 7) (val_const 8))
  have hjt := val_div (f 7) (val_const 8)
  exact (val_iteP (val_eqT hb (val_const 0))
    (val_encV_cons (val_const 1) (val_encV_cons (val_ruleT (f 1)
      (val_iteP (val_lt (f 5) hl) (val_srcPlT hB (f 2) (f 3) (f 5)) hpt)
      (val_iteP (val_lt (f 5) hl) (val_srcTyT hB (f 1) (f 2) (f 3) (f 4) (f 5)) hjt) hpt hjt (f 9))
      val_encV_nil))
    (val_encV_cons (val_const 7) (val_encV_cons (f 1) (val_encV_cons (f 2) (val_encV_cons (f 3)
      (val_encV_cons (f 4) (val_encV_cons (val_add (f 5) (val_const 1)) (val_encV_cons (f 6)
      (val_encV_cons (f 8) (val_encV_cons (f 10) val_encV_nil)))))))))).congr rfl

theorem val_trTagT (he : Val w env e ev) : Val w env (trTagT e) (trTagN ev) :=
  (val_iteP (val_eqT (val_getV he (val_const 0)) (val_const 7))
    (val_lt (val_getV he (val_const 5)) (val_getV he (val_const 6))) (val_const 2)).congr rfl

theorem val_trWidthT (hB : Val w env B Bv) (he : Val w env e ev) : Val w env (trWidthT B e)
    (trWidthN Bv ev) := by
  have f : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  exact (val_iteP (val_eqT (f 0) (val_const 7))
    (val_pivOffT (val_trWT hB (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)) 7) (val_const 0)).congr
    (by rw [trWidthN, pivWidth_eq])

theorem val_trLeafT (hB : Val w env B Bv) (he : Val w env e ev) : Val w env (trLeafT B e)
    (trLeafN Bv ev) := by
  have f : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  have
      c := fun k => val_eqT (val_cardT hB (val_getV (f 7) (val_const k)) (val_const 0)) (val_const 0)
  exact (val_trAndT (val_eqT (f 0) (val_const 7))
      (val_trAndT (c 0) (val_trAndT (c 1) (val_trAndT (c 2)
    (val_eqT (f 8) (val_const 0)))))).congr rfl

theorem val_trChildAllT (hB : Val w env B Bv) (he : Val w env e ev) (hix : Val w env i iv) :
    Val w env (trChildAllT B e i) (trChildAllN Bv ev iv) :=
  (val_iteP (val_eqT (val_getV he (val_const 0)) (val_const 7)) (val_trChildT hB he hix)
    (val_iteP (val_eqT (val_getV he (val_const 0)) (val_const 8)) (val_trmChildT he hix)
      (val_trrChildT hB he hix))).congr rfl

end ChildVal


/-! ### Tiers: list codes -/

/-- The body of `tOnesT`. -/
def tOnesBody (e : Term) : Term → Term → Term := fun acc i =>
  ite (lt acc i) acc (ite (lt i acc) acc (ite (bit e i) (add i (const 1)) acc))

theorem tOnesT_eq (e : Term) : tOnesT e = foldT e (const 0) (tOnesBody e) := rfl

/-- The body of `sizeT`. -/
def sizeBody (x : Term) : Term → Term → Term := fun acc i => ite (bit x i) (add i (const 1)) acc

theorem sizeT_eq (x : Term) : sizeT x = foldT x (const 0) (sizeBody x) := rfl

theorem tOnes_fold (E : ℕ) : ∀ m, (List.range m).foldl (tOnesStep E) 0 ≤ m ∧
    ∀ j < (List.range m).foldl (tOnesStep E) 0, E.testBit j = true
  | 0 => by simp
  | m + 1 => by
    obtain ⟨h1, h2⟩ := tOnes_fold E m
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (tOnesStep E) 0 = a at h1 h2 ⊢
    unfold tOnesStep
    by_cases ha : a < m
    · rw [ite_eq_left ha]; exact ⟨by omega, h2⟩
    · obtain rfl : a = m := by omega
      rw [ite_eq_right ha, ite_eq_right (lt_irrefl a)]
      by_cases hb : E.testBit a
      · rw [ite_eq_left hb]
        refine ⟨by omega, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj
        · exact hb
      · rw [ite_eq_right hb]; exact ⟨by omega, h2⟩

theorem le_size_of_bits {E n : ℕ} (h : ∀ j < n, E.testBit j = true) : n ≤ E.size := by
  by_contra hn
  have := h E.size (by omega)
  rw [Nat.testBit_lt_two_pow (NatList.lt_two_pow_size E)] at this
  exact absurd this (by decide)

theorem tOnes_le_size (E m : ℕ) : (List.range m).foldl (tOnesStep E) 0 ≤ E.size :=
  le_size_of_bits (tOnes_fold E m).2

theorem tOnesF_le_size (E : ℕ) : tOnesF E ≤ E.size := tOnes_le_size E E

theorem size_fold_le (X m : ℕ) : (List.range m).foldl (sizeStep X) 0 ≤ X.size := by
  rw [foldl_sizeStep]; exact Nat.size_le_size (Nat.mod_le _ _)

theorem dropF_le (E : ℕ) : ∀ K, dropF K E ≤ E
  | 0 => le_rfl
  | K + 1 => by
    rw [dropF, Function.iterate_succ_apply']
    exact (Nat.div_le_self _ _).trans (dropF_le E K)

theorem hdF_le (E : ℕ) : hdF E ≤ E := (Nat.mod_le _ _).trans (Nat.div_le_self _ _)

section TierList

variable {L : ℕ} {e x l k : Term} {E X Lv K : ℕ} {de dx dl dk : ℕ}

theorem val_tOnesFold {n : Term} {N : ℕ} (hn : Val w env n N) (he : Val w env e E) :
    Val w env (foldT n (const 0) (tOnesBody e)) ((List.range N).foldl (tOnesStep E) 0) :=
  val_foldT hn (val_const 0) fun pre x k _ =>
    (val_ite (val_lt (val_acc _ x k) (val_idx _ x k)) (val_acc _ x k)
      (val_ite (val_lt (val_idx _ x k) (val_acc _ x k)) (val_acc _ x k)
        (val_ite (val_bit (he.at2 pre x k) (val_idx _ x k)) (val_add (val_idx _ x k) (val_const 1))
          (val_acc _ x k)))).congr (by unfold tOnesStep; split_ifs <;> simp_all)

theorem val_sizeFold {n : Term} {N : ℕ} (hn : Val w env n N) (hx : Val w env x X) :
    Val w env (foldT n (const 0) (sizeBody x)) ((List.range N).foldl (sizeStep X) 0) :=
  val_foldT hn (val_const 0) fun pre a k _ =>
    (val_ite (val_bit (hx.at2 pre a k) (val_idx _ a k)) (val_add (val_idx _ a k) (val_const 1))
      (val_acc _ a k)).congr (by unfold sizeStep; split_ifs <;> simp_all)

theorem mul_lt_two_pow (hL : 9 ≤ L) {d : ℕ} (hd : d ≤ 32) : d * L < 2 ^ L := by
  have h : 32 * L < 2 ^ L := by
    induction L, hL using Nat.le_induction with
    | base => norm_num
    | succ m hm ih => rw [pow_succ]; omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hd) h

theorem size_le_tier {X d : ℕ} (h : X < 2 ^ (d * L)) : X.size ≤ d * L := Nat.size_le.mpr h

theorem Val.lt_tier {t : Term} {v d : ℕ} (hv : Val w env t v) (ht : Tm w L d t env) : v < 2 ^
    (d * L) :=
  hv.2 ▸ ht.lt

theorem tm_tOnesT (he : Val w env e E) (te : Tm w L de e env) (hde : de ≤ 32) (hL : 9 ≤ L) :
    Tm w L 1 (tOnesT e) env := by
  have hE := he.lt_tier te
  have hs := size_le_tier hE
  have hdl := mul_lt_two_pow hL hde
  rw [tOnesT_eq]
  refine tm_foldT_st he te hde (t_small (k := 0) (by norm_num) (by omega)) (by norm_num)
    (fun pre _ j hj => ?_) (fun pre x j _ hj hx he' => ?_)
  · rw [((val_tOnesFold (val_const j) he).ext pre).2, one_mul]
    exact lt_of_le_of_lt ((tOnes_le_size E j).trans hs) hdl
  · have ta : Tm w L 1 (lvl ((pre ++ env).length + 1)) (x :: j :: (pre ++ env)) := tm_acc hx
    have ti : Tm w L de (lvl (pre ++ env).length) (x :: j :: (pre ++ env)) := tm_idx (hj.trans hE)
    exact (t_ite (t_lt ta ti (by omega)) ta (t_ite (t_lt ti ta (by omega)) ta
      (t_ite (t_bit (te.ext he') ti (by omega)) (t_add ti (t_one (by omega)) (by omega) (by omega))
        ta))).mono (by omega)

theorem tm_sizeT (hx : Val w env x X) (tx : Tm w L dx x env) (hdx : dx ≤ 32) (hL : 9 ≤ L) :
    Tm w L 1 (sizeT x) env := by
  have hX := hx.lt_tier tx
  have hs := size_le_tier hX
  have hdl := mul_lt_two_pow hL hdx
  rw [sizeT_eq]
  refine tm_foldT_st hx tx hdx (t_small (k := 0) (by norm_num) (by omega)) (by norm_num)
    (fun pre _ j hj => ?_) (fun pre a j _ hj ha he' => ?_)
  · rw [((val_sizeFold (val_const j) hx).ext pre).2, one_mul]
    exact lt_of_le_of_lt ((size_fold_le X j).trans hs) hdl
  · have ta : Tm w L 1 (lvl ((pre ++ env).length + 1)) (a :: j :: (pre ++ env)) := tm_acc ha
    have ti : Tm w L dx (lvl (pre ++ env).length) (a :: j :: (pre ++ env)) := tm_idx (hj.trans hX)
    exact (t_ite (t_bit (tx.ext he') ti (by omega))
        (t_add ti (t_one (by omega)) (by omega) (by omega))
      ta).mono (by omega)

theorem pow2_tier {t : Term} {v n d : ℕ} (hv : Val w env t v) (ht : Tm w L 1 t env) (hle : v ≤ n)
    (hn : n < d * L) (hd : d ≤ 32) (hL : 2 ≤ L) : Tm w L d (pow2 t) env :=
  t_pow2 ht (by norm_num) (fun pre _ => by rw [(hv.ext pre).2]; omega) hd hL

theorem tm_hdV (he : Val w env e E) (te : Tm w L de e env) (hde : de + 1 ≤ 32) (hL : 9 ≤ L) :
    Tm w L de (hdV e) env := by
  have hs := size_le_tier (he.lt_tier te)
  have vt := val_tOnesT he
  have tt := tm_tOnesT he te (by omega) hL
  have hb := tOnesF_le_size E
  have e1 : (de + 1) * L = de * L + L := by ring
  have hdl := mul_lt_two_pow hL (d := 1) (by norm_num)
  exact t_mod_left (t_div te (t_pow2 (t_add tt (t_one (by omega)) (by omega) (by norm_num))
      (by norm_num)
    (fun pre _ => by rw [((val_add vt (val_const 1)).ext pre).2]; omega) hde (by omega)))
    (pow2_tier vt tt hb (show E.size < (de + 1) * L by omega) hde (by omega))

theorem tm_tlV (he : Val w env e E) (te : Tm w L de e env) (hde : 2 * de + 1 ≤ 32) (hL : 9 ≤ L) :
    Tm w L de (tlV e) env := by
  have hs := size_le_tier (he.lt_tier te)
  have vt := val_tOnesT he
  have tt := tm_tOnesT he te (by omega) hL
  have hb := tOnesF_le_size E
  have e1 : (2 * de + 1) * L = 2 * (de * L) + L := by ring
  exact t_div te (t_pow2 (t_add (t_add tt tt (by omega) (by norm_num)) (t_one (by omega)) (by omega)
    (by norm_num)) (by norm_num)
    (fun pre _ => by rw [((val_add (val_add vt vt) (val_const 1)).ext pre).2]; omega) hde
        (by omega))

theorem tm_dropV (he : Val w env e E) (te : Tm w L de e env) (hde : 2 * de + 1 ≤ 32)
    (hk : Val w env k K) (tk : Tm w L dk k env) (hdk : dk ≤ 32) (hL : 9 ≤ L) :
    Tm w L de (dropV e k) env := by
  have hE := he.lt_tier te
  unfold dropV
  refine tm_foldT_st hk tk hdk te (by omega) (fun pre _ j _ => ?_) (fun pre x j _ _ hx _ => ?_)
  · exact lt_of_eq_of_lt ((val_dropV he (val_const j)).ext pre).2 (lt_of_le_of_lt (dropF_le E j) hE)
  · exact (tm_tlV (val_acc _ x j) (tm_acc hx) hde hL).mono (by omega)

theorem tm_getV (he : Val w env e E) (te : Tm w L de e env) (hde : 2 * de + 1 ≤ 32)
    (hk : Val w env k K) (tk : Tm w L dk k env) (hdk : dk ≤ 32) (hL : 9 ≤ L) :
    Tm w L de (getV e k) env :=
  tm_hdV (val_dropV he hk) (tm_dropV he te hde hk tk hdk hL) (by omega) hL

theorem getF_le (E K : ℕ) : getF E K ≤ E := (hdF_le _).trans (dropF_le E K)

theorem tm_consV (hx : Val w env x X) (tx : Tm w L dx x env) (hl : Val w env l Lv)
    (tl : Tm w L dl l env) (hdx : 2 * dx + 1 ≤ 32) (hdl : dl + 2 * dx + 4 ≤ 128) (hL : 9 ≤ L)
    {d : ℕ} (hv : consF X Lv < 2 ^ (d * L)) : Tm w L d (consV x l) env := by
  have hs := size_le_tier (hx.lt_tier tx)
  have vs := val_sizeT hx
  have ts := tm_sizeT hx tx (by omega) hL
  have e1 : (dx + 1) * L = dx * L + L := by ring
  have e2 : (2 * dx + 1) * L = 2 * (dx * L) + L := by ring
  have p0 := pow2_tier vs ts le_rfl (show X.size < (dx + 1) * L by omega) (by omega) (by omega)
  have p1 := t_pow2 (d := dx + 1) (t_add ts (t_one (by omega)) (by omega) (by norm_num))
      (by norm_num)
    (fun pre _ => by rw [((val_add vs (val_const 1)).ext pre).2]; omega) (by omega) (by omega)
  have p2 := t_pow2 (d := 2 * dx + 1) (t_add (t_add ts ts (by omega) (by norm_num))
      (t_one (by omega))
    (by omega) (by norm_num)) (by norm_num)
    (fun pre _ => by rw [((val_add (val_add vs vs) (val_const 1)).ext pre).2]; omega) hdx (by omega)
  have coarse := t_add (t_add (t_sub p0 (t_one (by omega))) (t_mul p1 tx (by omega)) (by omega)
    (by omega)) (t_mul p2 tl (by omega)) (by omega) (by omega)
  exact tm_val coarse (val_consV hx hl) hv

/-- **The code of a list of terms**, of tier `d` when its value is below `2^(d·L)` and every entry
has tier `dt`. -/
theorem val_tm_encV {dt d : ℕ} (hdt : 2 * dt + 1 ≤ 32) (hd : d + 2 * dt + 4 ≤ 128) (hd1 : 1 ≤ d)
    (hL : 9 ≤ L) : ∀ {ts : List Term} {vs : List ℕ},
      List.Forall₂ (fun t v => Val w env t v ∧ Tm w L dt t env) ts vs →
      NatList.enc vs < 2 ^ (d * L) → Val w env (encV ts) (NatList.enc vs) ∧ Tm w L d (encV ts) env
  | [], [], .nil, h => ⟨val_encV_nil, tm_const h (by omega)⟩
  | _ :: _, v :: vs, .cons ⟨hv, ht⟩ hr, h => by
    have ih := val_tm_encV hdt hd hd1 hL hr (lt_of_le_of_lt (NatList.enc_le_enc_cons v vs) h)
    exact ⟨val_encV_cons hv ih.1, tm_consV hv ht ih.1 ih.2 hdt hd hL (by rw [consF_enc]; exact h)⟩

end TierList


/-! ### Tiers: sums, sources and weights -/

section TierSrc

variable {L : ℕ} {B up X Y M lo hi Tc k : Term} {Bv upv Xv Yv Mv lov hiv Tcv kv : ℕ}
  {dX dY dM dlo dhi dT dk dup : ℕ}

/-- **A sum with stable data**: the sum has tier `da` when its total does, the body being bounded.
-/
theorem tm_sumT_st {n : Term} {body : Term → Term} {g : ℕ → ℕ} {N dn da : ℕ} (hn : Val w env n N)
    (tn : Tm w L dn n env) (hdn : dn ≤ 32) (hda : da ≤ 32) (hL : 2 ≤ L)
    (hg : ∀ (pre : List ℕ) (x j : ℕ), j < N →
      Val w (x :: j :: (pre ++ env)) (body (lvl (pre ++ env).length)) (g j))
    (hsum : ∑ j ∈ Finset.range N, g j < 2 ^ (da * L))
    (tb : ∀ (pre : List ℕ) (x j : ℕ), Small L pre → j < N → x < 2 ^ (da * L) →
      Ext L (x :: j :: (pre ++ env)) env →
      Tm w L 127 (body (lvl (pre ++ env).length)) (x :: j :: (pre ++ env))) :
    Tm w L da (sumT n body) env := by
  unfold sumT
  refine tm_foldT_st hn tn hdn (t_small (k := 0) (by norm_num) hL) hda
    (fun pre _ j hj => ?_) (fun pre x j hp hj hx he => ?_)
  · have v := val_sumT (n := const j) (body := body) (val_const j) fun pre' x' i hi =>
      hg pre' x' i (by omega)
    refine lt_of_eq_of_lt (v.ext pre).2 (lt_of_le_of_lt ?_ hsum)
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hj)
  · exact (t_add (tm_acc hx) (tb pre x j hp hj hx he) (by omega) (by omega)).mono (by omega)

theorem tm_msgPosT (hB : Val w env B Bv) (hM : Val w env M Mv) (tB : Tm w L 1 B env)
    (tup : Tm w L dup up env) (tM : Tm w L dM M env) (hL : 10 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 4 (msgPosT B up M) env :=
  (t_ite (t_eqT' tup (t_one (by omega)) (by omega))
    (tm_msEndT hB hM (val_const 0) tB tM (t_small (k := 0) (by norm_num) (by omega)) le_rfl
      (by norm_num) (by omega) hBL)
    (t_small (k := 0) (by norm_num) (by omega))).mono (by omega)

theorem tm_srcLenT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (tB : Tm w L 1 B env) (tup : Tm w L dup up env)
    (tX : Tm w L dX X env) (tY : Tm w L dY Y env) (tM : Tm w L dM M env) (hL : 10 ≤ L)
    (hBL : Bv ≤ L) : Tm w L 5 (srcLenT B up X Y M) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  exact (t_add (t_add (tm_cardT hB hX (val_const 0) tB tX t0 le_rfl (by norm_num) (by omega) hBL)
    (tm_cardT hB hY (val_const 0) tB tY t0 le_rfl (by norm_num) (by omega) hBL) (by omega)
        (by omega))
    (tm_cardT hB hM (val_msgPosT hB hup hM) tB tM (tm_msgPosT hB hM tB tup tM hL hBL) (by norm_num)
      (by norm_num) (by omega) hBL) (by omega) (by omega)).mono (by omega)

theorem tm_srcTyT (hB : Val w env B Bv) (hup : Val w env up upv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (hM : Val w env M Mv) (hk : Val w env k kv) (tB : Tm w L 1 B env)
    (tup : Tm w L dup up env) (tX : Tm w L dX X env) (tY : Tm w L dY Y env) (tM : Tm w L dM M env)
    (tk : Tm w L dk k env) (hdk : dk ≤ 30) (hL : 10 ≤ L) (hBL : Bv ≤ L) :
    Tm w L (max dk 3 + 1) (srcTyT B up X Y M k) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have c1 := tm_cardT hB hX (val_const 0) tB tX t0 le_rfl (by norm_num) (by omega) hBL
  have c2 := tm_cardT hB hY (val_const 0) tB tY t0 le_rfl (by norm_num) (by omega) hBL
  have v1 := val_cardT hB hX (val_const 0)
  have v2 := val_cardT hB hY (val_const 0)
  have k1 := tm_kthT hB hX (val_const 0) hk tB tX t0 tk t0 hdk le_rfl (by norm_num) (by omega) hBL
  have k2 := tm_kthT hB hY (val_const 0) (val_sub hk v1) tB tY t0 (t_sub tk c1) t0 hdk le_rfl
    (by norm_num) (by omega) hBL
  have k3 := tm_kthT hB hM (val_msgPosT hB hup hM) (val_sub (val_sub hk v1) v2) tB tM
    (tm_msgPosT hB hM tB tup tM hL hBL) (t_sub (t_sub tk c1) c2) t0 hdk (by norm_num) (by norm_num)
    (by omega) hBL
  exact (t_ite (t_lt tk c1 (by omega)) k1 (t_ite (t_lt tk (t_add c1 c2 (by omega) (by omega))
    (by omega)) k2 k3)).mono (by omega)

theorem srcWtN_le {A Bv : ℕ} {up : Bool} {x y m : Label} (hx : LFits Bv x) (hy : LFits Bv y)
    (hm : LFits Bv m) (hwt : labelWt x + labelWt y + labelWt m ≤ A) (lo hi : ℕ) :
    srcWtN Bv up.toNat (lcode x) (lcode y) (lcode m) lo hi ≤ A := by
  rw [srcWtN_eq up hx hy hm]
  have h1 := sum_lwt_srcSub_le up x y m lo hi
  have h2 := sum_lwt_srcList up x y m
  have h3 := wt_msgMs_le up m
  unfold labelWt at hwt h3
  omega

theorem tm_srcWtT {A : ℕ} {up' : Bool} {x y m : Label} (hB : Val w env B Bv)
    (hup : Val w env up up'.toNat) (hX : Val w env X (lcode x)) (hY : Val w env Y (lcode y))
    (hM : Val w env M (lcode m)) (hlo : Val w env lo lov) (hhi : Val w env hi hiv)
    (tB : Tm w L 1 B env) (tup : Tm w L dup up env) (tX : Tm w L dX X env) (tY : Tm w L dY Y env)
    (tM : Tm w L dM M env) (tlo : Tm w L dlo lo env) (thi : Tm w L dhi hi env) (hdlo : dlo ≤ 28)
    (hdhi : dhi ≤ 28) (hL : 10 ≤ L) (hBL : Bv ≤ L) (hx : LFits Bv x) (hy : LFits Bv y)
    (hm : LFits Bv m) (hwt : labelWt x + labelWt y + labelWt m ≤ A) (hAL : A < 2 ^ L) :
    Tm w L 1 (srcWtT B up X Y M lo hi) env := by
  have hN := (val_sub hhi hlo).lt_tier (t_sub thi tlo)
  refine tm_sumT_st (val_sub hhi hlo) (t_sub thi tlo) (by omega) (by norm_num) (by omega)
    (g := fun j => if lov + j < srcLenN Bv up'.toNat (lcode x) (lcode y) (lcode m)
      then srcTyN Bv up'.toNat (lcode x) (lcode y) (lcode m) (lov + j) + 1 else 0)
    (fun pre a j _ => ?_) ?_ (fun pre a j _ hj _ he => ?_)
  · have hk := val_add (hlo.at2 pre a j) (val_idx _ a j)
    exact (val_ite (val_lt hk (val_srcLenT (hB.at2 pre a j) (hup.at2 pre a j) (hX.at2 pre a j)
      (hY.at2 pre a j) (hM.at2 pre a j)))
      (val_add (val_srcTyT (hB.at2 pre a j) (hup.at2 pre a j) (hX.at2 pre a j) (hY.at2 pre a j)
        (hM.at2 pre a j) hk) (val_const 1)) (val_const 0)).congr (by split_ifs <;> simp_all)
  · rw [one_mul]
    exact lt_of_le_of_lt (srcWtN_le (up := up') hx hy hm hwt lov hiv) hAL
  · have ti : Tm w L dhi (lvl (pre ++ env).length) (a :: j :: (pre ++ env)) := tm_idx (hj.trans hN)
    have hk := t_add (tlo.ext he) ti (by omega) (by omega)
    have vk := val_add (hlo.at2 pre a j) (val_idx _ a j)
    exact (t_ite (t_lt hk (tm_srcLenT (hB.at2 pre a j) (hup.at2 pre a j) (hX.at2 pre a j)
      (hY.at2 pre a j) (hM.at2 pre a j) (tB.ext he) (tup.ext he) (tX.ext he) (tY.ext he) (tM.ext he)
      hL hBL) (by omega))
      (t_add (tm_srcTyT (hB.at2 pre a j) (hup.at2 pre a j) (hX.at2 pre a j) (hY.at2 pre a j)
        (hM.at2 pre a j) vk (tB.ext he) (tup.ext he) (tX.ext he) (tY.ext he) (tM.ext he) hk
        (by omega) hL hBL) (t_one (by omega)) (by omega) (by omega))
      (t_small (k := 0) (by norm_num) (by omega))).mono (by omega)

theorem tm_tWtT (hB : Val w env B Bv) (hT : Val w env Tc Tcv) (tB : Tm w L 1 B env)
    (tT : Tm w L dT Tc env) (hdT : 2 * dT + 1 ≤ 32) (hL : 10 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 7 (tWtT B Tc) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have g : ∀ j ≤ 3, Tm w L 5 (wtT B (getV Tc (const j)) (const 0)) env := fun j hj =>
    tm_wtT hB (val_getV hT (val_const j)) (val_const 0) tB
      (tm_getV hT tT hdT (val_const j) (t_small hj (by omega)) (by norm_num) (by omega)) t0 le_rfl
      (by norm_num) (by omega) hBL
  exact (t_add (t_add (g 0 (by norm_num)) (g 1 (by norm_num)) (by omega) (by omega))
      (g 2 (by norm_num))
    (by omega) (by omega)).mono (by omega)

theorem tm_trWT {A : ℕ} {up' : Bool} {x y m : Label} {T : Multiset (HPlace × ℕ)}
    (hB : Val w env B Bv) (hup : Val w env up up'.toNat) (hX : Val w env X (lcode x))
    (hY : Val w env Y (lcode y)) (hM : Val w env M (lcode m)) (hlo : Val w env lo lov)
    (hhi : Val w env hi hiv) (hT : Val w env Tc (tcode up' T)) (tB : Tm w L 1 B env)
    (tup : Tm w L dup up env) (tX : Tm w L dX X env) (tY : Tm w L dY Y env) (tM : Tm w L dM M env)
    (tlo : Tm w L dlo lo env) (thi : Tm w L dhi hi env) (tT : Tm w L dT Tc env) (hdlo : dlo ≤ 28)
    (hdhi : dhi ≤ 28) (hdT : 2 * dT + 1 ≤ 32) (hL : 10 ≤ L) (hBL : Bv ≤ L)
    (hf : TrFit A Bv up' x y m T) (hAL : A < 2 ^ L) :
    Tm w L 1 (trWT B up X Y M lo hi Tc) env := by
  refine tm_val (t_add (tm_srcWtT hB hup hX hY hM hlo hhi tB tup tX tY tM tlo thi hdlo hdhi hL hBL
    hf.lx hf.ly hf.lm (by have := hf.wt_le; omega) hAL) (tm_tWtT hB hT tB tT hdT hL hBL) (by omega)
    (by omega)) (val_trWT hB hup hX hY hM hlo hhi hT) ?_
  rw [one_mul, trWN_eq up' hf.lx hf.ly hf.lm lov hiv hf.valid hf.tf]
  exact lt_of_le_of_lt (hf.tWt_le lov hiv) hAL

end TierSrc


/-! ### Tiers: pivot fields and the pivot test -/

theorem size_le_add {a b : ℕ} (h : a < 2 ^ b) : a.size ≤ b := Nat.size_le.mpr h

theorem pivW_le {Wv L : ℕ} (hW : Wv < 2 ^ L) (hcw : codeWidth Wv ≤ L) (j : ℕ) : pivW Wv j ≤ L +
    2 := by
  have h1 : Wv.size ≤ L := size_le_add hW
  have h2 : (3 * Wv + 3).size ≤ L + 2 := size_le_add (by rw [pow_add]; omega)
  have h3 : (2 * Wv).size ≤ L + 1 := size_le_add (by rw [pow_succ]; omega)
  unfold pivW; split_ifs <;> omega

theorem off_pivW_le {Wv L : ℕ} (hW : Wv < 2 ^ L) (hcw : codeWidth Wv ≤ L) :
    ∀ j ≤ 7, Radix.off (pivW Wv) j ≤ 7 * L + 4 := by
  have h1 : Wv.size ≤ L := size_le_add hW
  have h2 : (3 * Wv + 3).size ≤ L + 2 := size_le_add (by rw [pow_add]; omega)
  have h3 : (2 * Wv).size ≤ L + 1 := size_le_add (by rw [pow_succ]; omega)
  intro j hj
  have e : Radix.off (pivW Wv) 7 = Wv.size + (3 * Wv + 3).size + 3 * codeWidth Wv + 2 *
      (2 * Wv).size := by
    rw [← pivWidth_eq]; rfl
  have hmono : Radix.off (pivW Wv) j ≤ Radix.off (pivW Wv) 7 :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hj)
  omega

section TierPiv

variable {L : ℕ} {B up X Y M lo hi Tc W i d p j : Term}
  {Bv upv Xv Yv Mv lov hiv Tcv Wv iv dv pv jv : ℕ} {dup dX dY dM dlo dhi dT di dd dp dj : ℕ}

theorem tm_pivWT (hW : Val w env W Wv) (tW : Tm w L 1 W env) (hcw : codeWidth Wv ≤ L) (hL : 10 ≤ L)
    (j : ℕ) : Tm w L 1 (pivWT W j) env := by
  rcases j with _ | _ | _ | _ | _ | j
  · exact tm_sizeT hW tW (by norm_num) (by omega)
  · exact tm_sizeT (val_add (val_mul (val_const 3) hW) (val_const 3))
      (t_add (t_mul (t_small (k := 3) le_rfl (by omega)) tW (by norm_num))
        (t_small (k := 3) le_rfl (by omega)) (by omega) (by norm_num)) (by norm_num) (by omega)
  all_goals first
    | exact tm_val (tm_codeWidthT hW tW (by norm_num) hL) (val_codeWidthT hW)
        (by rw [one_mul]; exact lt_of_le_of_lt hcw Nat.lt_two_pow_self)
    | exact tm_sizeT (val_mul (val_const 2) hW)
        (t_mul (t_small (k := 2) (by norm_num) (by omega)) tW
        (by norm_num)) (by norm_num) (by omega)

theorem tm_pivOffT (hW : Val w env W Wv) (tW : Tm w L 1 W env) (hWL : Wv < 2 ^ L)
    (hcw : codeWidth Wv ≤ L) (hL : 10 ≤ L) : ∀ j ≤ 7, Tm w L 1 (pivOffT W j) env
  | 0, _ => t_small (by norm_num) (by omega)
  | j + 1, hj => tm_val (t_add (tm_pivOffT hW tW hWL hcw hL j (by omega)) (tm_pivWT hW tW hcw hL j)
      (by omega) (by norm_num)) (val_pivOffT hW (j + 1)) (by
        rw [one_mul]
        have := off_pivW_le hWL hcw (j + 1) hj
        have := mul_lt_two_pow (L := L) (by omega) (d := 8) (by norm_num)
        omega)

theorem tm_pdigT (hW : Val w env W Wv) (tW : Tm w L 1 W env) (hWL : Wv < 2 ^ L)
    (hcw : codeWidth Wv ≤ L) (hL : 10 ≤ L) (ti : Tm w L di i env) {j : ℕ} (hj : j ≤ 6) :
    Tm w L 2 (pdigT W i j) env := by
  have h1 := off_pivW_le hWL hcw j (by omega)
  have h2 := pivW_le hWL hcw j
  exact t_mod (t_div ti (pow2_tier (val_pivOffT hW j) (tm_pivOffT hW tW hWL hcw hL j (by omega)) h1
    (show 7 * L + 4 < 8 * L by omega) (by norm_num) (by omega)))
    (pow2_tier (val_pivWT hW j) (tm_pivWT hW tW hcw hL j) h2 (show L + 2 < 2 * L by omega)
      (by norm_num) (by omega)) Pos.pow2'

theorem tm_partOkT (hB : Val w env B Bv) (hW : Val w env W Wv) (hd : Val w env d dv)
    (tB : Tm w L 1 B env) (tW : Tm w L 1 W env) (td : Tm w L dd d env)
    (hcw : codeWidth Wv ≤ L) (hL : 10 ≤ L) (hBL : Bv ≤ L) : Tm w L 2 (partOkT B W d) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have tc := tm_val (tm_codeWidthT hW tW (by norm_num) hL) (val_codeWidthT hW)
    (by rw [one_mul]; exact lt_of_le_of_lt hcw Nat.lt_two_pow_self)
  exact t_mul (t_eqT' (tm_validT hW (val_codeWidthT hW) hd tW tc td (by omega) (by omega) hcw)
    (t_one (by omega)) (by omega))
    (t_eqT' (tm_wtT hB hd (val_msEndT hB hd (val_const 0)) tB td
      (tm_msEndT hB hd (val_const 0) tB td t0 le_rfl (by norm_num) (by omega) hBL) (by omega)
      (by omega) (by omega) hBL) t0 (by omega)) (by norm_num)

theorem tm_leCntT {c q : Term} {cv qv dc dq : ℕ} {cnt : Term → Term} {C : ℕ → ℕ}
    (hcnt : ValF1 w cnt C env) (tcnt : TmV1 w L cnt 3 env) (hB : Val w env B Bv)
        (hc : Val w env c cv)
    (hq : Val w env q qv) (tB : Tm w L 1 B env) (tc : Tm w L dc c env) (tq : Tm w L dq q env)
    (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hL : 10 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (leCntT B c q cnt)
        env :=
  tm_msFoldT_cl (G := fun a e μ => if μ ≤ C e then a else 0)
    (fun pre _ _ _ _ _ _ hx he hμ => (val_ite (val_lt (hcnt pre _ _ he) hμ) (val_const 0) hx).congr
      (by dsimp only; split_ifs <;> first | rfl | omega))
    (fun E hE x y z _ Y _ _ hy _ tx ty tz => (t_ite (t_lt (tcnt E hE y Y hy ty) tz (by omega))
      (t_small (k := 0) (by norm_num) (by omega)) tx).mono (by omega)) (by norm_num)
    (fun a e μ ha _ _ => by
      show (if μ ≤ C e then a else 0) < _
      split_ifs
      exacts [ha, by positivity])
    (val_const 1) (t_one (by omega)) hB hc hq tB tc tq hdq1 hdq (by omega) hBL

theorem tm_restCntT (hB : Val w env B Bv) (hT : Val w env Tc Tcv) (tB : Tm w L 1 B env)
    (tT : Tm w L dT Tc env) (tp : Tm w L dp p env)
    (tj : Tm w L dj j env) (hdT : 2 * dT + 1 ≤ 32) (hL : 10 ≤ L) (hBL : Bv ≤ L) (k : ℕ) (hk : k ≤ 3)
    (dy : ℕ) : TmV1 w L (restCntT B Tc p j k) dy env := fun E hE y Y hy ty => by
  have t0 : Tm w L 1 (const 0) E := t_small (by norm_num) (by omega)
  have tk : Tm w L 1 (const k) E := t_small hk (by omega)
  exact (t_sub (tm_countT (hB.extE hE) (val_getV (hT.extE hE) (val_const k)) (val_const 0) hy
      (tB.ext hE)
    (tm_getV (hT.extE hE) (tT.ext hE) hdT (val_const k) tk (by norm_num) (by omega)) t0 ty le_rfl
    (by norm_num) (by omega) hBL)
    (t_ite (t_mul (t_eqT' tk (tp.ext hE) (by omega)) (t_eqT' ty (tj.ext hE) (by omega))
        (by norm_num))
      (t_one (by omega)) t0)).mono (by norm_num)


theorem tm_pivL1T {A : ℕ} {up' : Bool} {x y m : Label} {T : Multiset (HPlace × ℕ)}
    (hf : TrFit A Bv up' x y m T) (hAL : A < 2 ^ L) (hB : Val w env B Bv)
    (hup : Val w env up up'.toNat) (hX : Val w env X (lcode x)) (hY : Val w env Y (lcode y))
    (hM : Val w env M (lcode m)) (hlo : Val w env lo lov) (hW : Val w env W Wv)
        (hix : Val w env i iv)
    (tB : Tm w L 1 B env) (tup : Tm w L dup up env) (tX : Tm w L dX X env) (tY : Tm w L dY Y env)
    (tM : Tm w L dM M env) (tlo : Tm w L dlo lo env) (tW : Tm w L 1 W env) (ti : Tm w L di i env)
    (hdlo : dlo ≤ 27) (hWL : Wv < 2 ^ L) (hcw : codeWidth Wv ≤ L) (hL : 10 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 8 (pivL1T B up X Y M lo W i) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have wk : ∀ j ≤ 6, Tm w L 5 (wtT B (pdigT W i j) (const 0)) env := fun j hj =>
    tm_wtT hB (val_pdigT hW hix j) (val_const 0) tB (tm_pdigT hW tW hWL hcw hL ti hj) t0 le_rfl
      (by norm_num) (by omega) hBL
  have sw := tm_srcWtT hB hup hX hY hM hlo (val_add hlo (val_pdigT hW hix 0)) tB tup tX tY tM tlo
    (t_add tlo (tm_pdigT hW tW hWL hcw hL ti (j := 0) (by norm_num)) (by omega) (by omega))
    (by omega) (by omega) hL hBL hf.lx hf.ly hf.lm (by have := hf.wt_le; omega) hAL
  exact (t_add (t_add (t_add sw (wk 2 (by norm_num)) (by omega) (by omega)) (wk 3 (by norm_num))
    (by omega) (by omega)) (wk 4 (by norm_num)) (by omega) (by omega)).mono (by omega)

theorem tm_pivOkT {A : ℕ} {up' : Bool} {x y m : Label} {T : Multiset (HPlace × ℕ)}
    (hf : TrFit A Bv up' x y m T) (hAL : A < 2 ^ L) (hB : Val w env B Bv)
    (hup : Val w env up up'.toNat) (hX : Val w env X (lcode x)) (hY : Val w env Y (lcode y))
    (hM : Val w env M (lcode m)) (hlo : Val w env lo lov) (hhi : Val w env hi hiv)
    (hT : Val w env Tc Tcv) (hW : Val w env W Wv) (hix : Val w env i iv)
    (tB : Tm w L 1 B env) (tup : Tm w L dup up env) (tX : Tm w L dX X env) (tY : Tm w L dY Y env)
    (tM : Tm w L dM M env) (tlo : Tm w L dlo lo env) (thi : Tm w L dhi hi env)
    (tT : Tm w L dT Tc env) (tW : Tm w L 1 W env) (ti : Tm w L di i env)
    (hdlo : dlo ≤ 27) (hdT : 2 * dT + 1 ≤ 32) (hWL : Wv < 2 ^ L) (hcw : codeWidth Wv ≤ L)
    (hL : 10 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (pivOkT B up X Y M lo hi Tc W i) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have dg := fun (j : ℕ) (hj : j ≤ 6) => tm_pdigT hW tW hWL hcw hL ti hj
  have vd := fun j => val_pdigT hW hix j
  have tp : Tm w L 2 (mod (pdigT W i 1) (const 3)) env := t_mod_left (dg 1 (by norm_num))
      (t_small le_rfl (by omega))
  have tj : Tm w L 2 (div (pdigT W i 1) (const 3)) env := t_div (dg 1 (by norm_num))
      (t_small le_rfl (by omega))
  have vp := val_mod (vd 1) (val_const 3)
  have vj := val_div (vd 1) (val_const 3)
  have po := fun (j : ℕ) (hj : j ≤ 6) => tm_partOkT hB hW (vd j) tB tW (dg j hj) hcw hL hBL
  have lc := fun (k : ℕ) (hk : k ≤ 3) (hk' : k + 2 ≤ 6) =>
    t_eqT' (tm_leCntT (valF1_restCntT hB hT vp vj k)
        (tm_restCntT hB hT tB tT tp tj hdT hL hBL k hk 3)
      hB (vd (k + 2)) (val_const 0) tB (dg (k + 2) hk') t0 le_rfl (by norm_num) hL hBL)
      (t_one (by omega)) (by omega)
  have tlen := tm_srcLenT hB hup hX hY hM tB tup tX tY tM (by omega) hBL
  have L1 := tm_pivL1T hf hAL hB hup hX hY hM hlo hW hix tB tup tX tY tM tlo tW ti hdlo hWL hcw hL
      hBL
  have tk := t_add tlo (dg 0 (by norm_num)) (by omega) (by omega)
  have tty := tm_srcTyT hB hup hX hY hM (val_add hlo (vd 0)) tB tup tX tY tM tk (by omega) hL hBL
  have h7 := off_pivW_le hWL hcw 7 le_rfl
  have coarse : Tm w L 16 (pivOkT B up X Y M lo hi Tc W i) env := by
    unfold pivOkT trAndT trLeT
    refine (t_mul (t_mul (t_lt ti (pow2_tier (val_pivOffT hW 7)
        (tm_pivOffT hW tW hWL hcw hL 7 le_rfl) h7
        (show 7 * L + 4 < 8 * L by omega) (by norm_num) (by omega)) (by omega))
      (t_mul (po 2 (by norm_num)) (t_mul (po 3 (by norm_num)) (po 4 (by norm_num)) (by norm_num))
        (by norm_num)) (by norm_num))
      (t_mul (t_lt (dg 0 (by norm_num)) (tm_cminT ((t_sub thi tlo).mono (le_max_left dhi 5))
          ((t_sub tlen tlo).mono (le_max_right dhi 5)) (by omega)) (by omega))
      (t_mul (t_lt t0 (tm_countT hB (val_getV hT vp) (val_const 0) vj tB
          (tm_getV hT tT hdT vp tp (by norm_num) (by omega)) t0 tj le_rfl (by norm_num) (by omega)
              hBL)
          (by omega))
      (t_mul (t_mul (lc 0 (by norm_num) (by norm_num)) (t_mul (lc 1 (by norm_num) (by norm_num))
          (lc 2 (by norm_num) (by norm_num)) (by norm_num)) (by norm_num))
      (t_mul (t_mul (t_lt (t_mul (t_small (k := 2) (by norm_num) (by omega)) L1 (by norm_num)) tW
          (by omega))
        (t_lt tW (t_add (t_mul (t_small (k := 2) (by norm_num) (by omega)) (t_add (t_add L1
          (t_add tty (t_one (by omega)) (by omega) (by omega)) (by omega) (by omega))
          (t_add tj (t_one (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega))
          (t_one (by omega)) (by omega) (by omega)) (by omega)) (by norm_num))
      (t_mul (t_lt (dg 5 (by norm_num)) (t_add (t_mul (t_small (k := 2) (by norm_num) (by omega)) tW
          (by norm_num)) (t_one (by omega)) (by omega) (by omega)) (by omega))
        (t_lt (dg 6 (by norm_num)) (t_add (t_mul (t_small (k := 2) (by norm_num) (by omega)) tW
          (by norm_num)) (t_one (by omega)) (by omega) (by omega)) (by omega)) (by norm_num))
        (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)).mono
            (by norm_num)
  refine tm_val coarse (val_pivOkT hB hup hX hY hM hlo hhi hT hW hix) ?_
  rw [one_mul]
  split_ifs
  · exact Nat.one_lt_two_pow (by omega)
  · exact Nat.two_pow_pos _

theorem tm_restT (hB : Val w env B Bv) (hT : Val w env Tc Tcv) (hp : Val w env p pv)
    (hj : Val w env j jv) (hd : Val w env d dv) (tB : Tm w L 1 B env) (tT : Tm w L dT Tc env)
    (tp : Tm w L dp p env) (tj : Tm w L dj j env) (td : Tm w L dd d env) (hdT : 2 * dT + 1 ≤ 32)
    (hL : 10 ≤ L) (hBL : Bv ≤ L) (k : ℕ) (hk : k ≤ 3) : Tm w L 1 (restT B Tc p j k d) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have tk : Tm w L 1 (const k) env := t_small hk (by omega)
  have hC : ValF1 w
      (fun e => sub (sub (countT B (getV Tc (const k)) (const 0) e) (countT B d (const 0) e))
      (ite (mul (eqT (const k) p) (eqT e j)) (const 1) (const 0)))
      (fun e => countN Bv (getF Tcv k) 0 e - countN Bv dv 0 e - if k = pv ∧ e = jv then 1 else 0)
          env :=
    fun pre _ _
        hy => (val_sub (val_sub (val_countT (hB.ext pre) (val_getV (hT.ext pre) (val_const k))
      (val_const 0) hy) (val_countT (hB.ext pre) (hd.ext pre) (val_const 0) hy))
      (val_ite (val_mul (val_eqT (val_const k) (hp.ext pre)) (val_eqT hy (hj.ext pre)))
        (val_const 1) (val_const 0))).congr (by congr 1; split_ifs <;> simp_all)
  refine tm_ocCodeT hB (val_topT hB (val_getV hT (val_const k)) (val_const 0)) hC tB
    (tm_topT hB (val_getV hT (val_const k)) (val_const 0) tB
      (tm_getV hT tT hdT (val_const k) tk (by norm_num) (by omega)) t0 le_rfl (by norm_num)
          (by omega) hBL)
    (fun E hE y Y hy ty => ?_) (by norm_num) (by omega) hBL
  have t0' : Tm w L 1 (const 0) E := t_small (by norm_num) (by omega)
  have tk' : Tm w L 1 (const k) E := t_small hk (by omega)
  exact (t_sub (t_sub (tm_countT (hB.extE hE) (val_getV (hT.extE hE) (val_const k)) (val_const 0) hy
      (tB.ext hE) (tm_getV (hT.extE hE) (tT.ext hE) hdT (val_const k) tk' (by norm_num) (by omega))
          t0' ty
      le_rfl (by norm_num) (by omega) hBL)
    (tm_countT (hB.extE hE) (hd.extE hE) (val_const 0) hy (tB.ext hE) (td.ext hE) t0' ty le_rfl
      (by norm_num) (by omega) hBL))
    (t_ite (t_mul (t_eqT' tk' (tp.ext hE) (by omega)) (t_eqT' ty (tj.ext hE) (by omega))
        (by norm_num))
      (t_one (by omega)) t0')).mono (by norm_num)

end TierPiv


/-! ### Tiers: small terms, bits and rules -/

section TierRule

variable {L : ℕ} {a b z c t e up ps pt : Term} {A B' Z C : ℕ} {da db dz dc dup dps dpt : ℕ}

/-- A conditional with a stable condition needs only the taken branch. -/
theorem tm_ite_val {d : ℕ} (hc : Val w env c C) (tc : Tm w L dc c env) (ht : 0 < C → Tm w L d t env)
    (he : ¬ 0 < C → Tm w L d e env) : Tm w L d (ite c t e) env := by
  intro pre hp
  have hcv : c.denote w (pre ++ env) = C := (hc.ext pre).2
  by_cases h : 0 < C
  · have htm := ht h pre hp
    have h' : 0 < c.denote w (pre ++ env) := by rw [hcv]; exact h
    refine ⟨⟨(tc pre hp).1, ?_⟩, ?_⟩
    · exact (ite_eq_left (show 0 < ProgLang.Prog.eval w (c (pre ++ env).length) (pre ++ env)
        from h')).symm ▸ htm.1
    · simp only [Term.denote_ite, h', ↓reduceIte]; exact htm.2
  · have htm := he h pre hp
    have h' : ¬ 0 < c.denote w (pre ++ env) := by rw [hcv]; exact h
    refine ⟨⟨(tc pre hp).1, ?_⟩, ?_⟩
    · exact (ite_eq_right (show ¬ 0 < ProgLang.Prog.eval w (c (pre ++ env).length) (pre ++ env)
        from h')).symm ▸ htm.1
    · simp only [Term.denote_ite, h', ↓reduceIte]; exact htm.2

theorem tm_trZzSubT (ta : Tm w L da a env) (tb : Tm w L db b env) (hd : max da db + 1 ≤ 128)
    (hL : 2 ≤ L) :
    Tm w L (max da db + 1) (trZzSubT a b) env :=
  (t_ite (t_lt ta tb (by omega)) (t_sub (t_mul (t_small (k := 2) (by norm_num) hL) (t_sub tb ta)
    (by omega)) (t_one (by omega))) (t_mul (t_small (k := 2) (by norm_num) hL) (t_sub ta tb)
    (by omega))).mono (by omega)

theorem tm_zzAddT (tz : Tm w L dz z env) (ta : Tm w L da a env) (tb : Tm w L db b env)
    (hd : max (max da db) (max dz 1) + 3 ≤ 128) (hL : 2 ≤ L) :
    Tm w L (max (max da db) (max dz 1) + 3) (zzAddT z a b) env := by
  have t2 : Tm w L 1 (const 2) env := t_small (by norm_num) hL
  have h1 : Tm w L (max dz 1 + 1) (add z (const 1)) env := t_add tz (t_one (by omega)) (by omega)
      (by omega)
  have h2 : Tm w L (max db (max dz 1 + 1) + 1) (add b (div (add z (const 1)) (const 2))) env :=
    t_add tb (t_div h1 t2) (by omega) (by omega)
  have h3 : Tm w L (max dz da + 1) (add (div z (const 2)) a) env := t_add (t_div tz t2) ta
      (by omega) (by omega)
  exact (t_ite (t_mod_left tz t2) (tm_trZzSubT ta h2 (by omega) hL)
      (tm_trZzSubT h3 tb (by omega) hL)).mono
    (by omega)

theorem tm_plOfT (ta : Tm w L da a env) (tb : Tm w L db b env) (hL : 3 ≤ L) :
    Tm w L 1 (plOfT a b) env := by
  have k := fun (n : ℕ) (hn : n ≤ 3) => (t_small (env := env) (w := w) (L := L) hn (by omega))
  have k4 : Tm w L 1 (const 4) env := t_const (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right
    (by norm_num) hL))
  exact (t_ite (t_eqT' tb (k 0 (by norm_num)) (by omega))
      (t_ite (t_eqT' ta (k 1 (by norm_num)) (by omega))
    (k 1 (by norm_num)) (k 3 le_rfl)) (t_ite (t_eqT' tb (k 1 (by norm_num)) (by omega))
    (t_ite (t_eqT' ta (k 1 (by norm_num)) (by omega)) (k 2 (by norm_num)) k4)
        (k 0 (by norm_num)))).mono
    (by omega)

theorem tm_plIdxT (ta : Tm w L da a env) (hL : 3 ≤ L) : Tm w L 1 (plIdxT a) env := by
  have k := fun (n : ℕ) (hn : n ≤ 3) => (t_small (env := env) (w := w) (L := L) hn (by omega))
  exact (t_ite (t_eqT' ta (k 0 (by norm_num)) (by omega)) (k 2 (by norm_num))
    (t_ite (t_lt (k 0 (by norm_num)) (t_add (t_eqT' ta (k 1 (by norm_num)) (by omega))
      (t_eqT' ta (k 3 le_rfl) (by omega)) (by omega) (by omega)) (by omega)) (k 0 (by norm_num))
      (k 1 (by norm_num)))).mono (by omega)

theorem tm_xorT' (ha : Val w env a A) (hb : Val w env b B') (ta : Tm w L da a env)
    (tb : Tm w L db b env) (hd : max da db + 1 ≤ 31) (hL : 9 ≤ L) :
    Tm w L (max da db + 1) (xorT' a b) env := by
  have hA := ha.lt_tier ta
  have hB := hb.lt_tier tb
  have hA' : A < 2 ^ ((max da db + 1) * L) := hA.trans_le (pow_le_pow_tier (by omega))
  have hB' : B' < 2 ^ ((max da db + 1) * L) := hB.trans_le (pow_le_pow_tier (by omega))
  have hAB : A + B' < 2 ^ ((max da db + 1) * L) := by
    have h1 : A < 2 ^ (max da db * L) := hA.trans_le (pow_le_pow_tier (le_max_left _ _))
    have h2 : B' < 2 ^ (max da db * L) := hB.trans_le (pow_le_pow_tier (le_max_right _ _))
    exact sum_lt_tier h1 h2 (by omega)
  have hs := size_le_tier hAB
  have hsL := mul_lt_two_pow hL (d := max da db + 1) (by omega)
  have tn := tm_sizeT (val_add ha hb) (t_add ta tb (by omega) (by omega)) (by omega) hL
  unfold xorT'
  refine tm_sumT_st (val_sizeT (val_add ha hb)) tn (by norm_num) (by omega) (by omega)
    (g := fun j => 2 ^ j * (((A.testBit j).toNat + (B'.testBit j).toNat) % 2))
    (fun pre x j _ => val_mul (val_pow2 (val_idx _ x j)) (val_mod (val_add (val_bit (ha.at2 pre x j)
      (val_idx _ x j)) (val_bit (hb.at2 pre x j) (val_idx _ x j))) (val_const 2)))
    (by rw [← xor_eq_sum]; exact Nat.xor_lt_two_pow hA' hB') (fun pre x j _ hj _ he => ?_)
  have tj : Tm w L 1 (lvl (pre ++ env).length) (x :: j :: (pre ++ env)) :=
    tm_idx (by rw [one_mul]; omega)
  exact (t_mul (pow2_tier (val_idx _ x j) tj le_rfl (show j < (max da db + 1) * L by omega)
      (by omega)
    (by omega)) (t_mod (t_add (t_bit (ta.ext he) tj (by omega)) (t_bit (tb.ext he) tj (by omega))
      (by omega) (by omega)) (t_small (k := 2) (by norm_num) (by omega)) (Pos.const' (by norm_num)))
      (by omega)).mono (by omega)

theorem tm_ipT (ha : Val w env a A) (hb : Val w env b B') (ta : Tm w L da a env)
    (tb : Tm w L db b env) (hda : da + 1 ≤ 32) (hL : 9 ≤ L) : Tm w L (da + 1) (ipT a b) env := by
  have hA := ha.lt_tier ta
  have e1 : (da + 1) * L = da * L + L := by ring
  have h2 : 2 ^ ((da + 1) * L) = 2 ^ (da * L) * 2 ^ L := by rw [e1, pow_add]
  have h3 : 2 ≤ 2 ^ L := Nat.le_self_pow (by omega) 2
  unfold ipT
  refine tm_sumT_st (val_add ha (val_const 1)) (t_add ta (t_one (by omega)) (by omega) (by omega))
    (by omega) hda (by omega) (g := fun j => (A.testBit j).toNat * (B'.testBit j).toNat)
    (fun pre x j _ => val_mul (val_bit (ha.at2 pre x j) (val_idx _ x j))
      (val_bit (hb.at2 pre x j) (val_idx _ x j))) ?_ (fun pre x j _ hj _ he => ?_)
  · calc ∑ j ∈ Finset.range (A + 1), (A.testBit j).toNat * (B'.testBit j).toNat
        ≤ ∑ j ∈ Finset.range (A + 1), 1 := Finset.sum_le_sum fun j _ => by
          cases A.testBit j <;> cases B'.testBit j <;> simp
      _ = A + 1 := by simp
      _ < 2 ^ ((da + 1) * L) := by
        rw [h2]
        have h4 : 2 ^ (da * L) * 2 ≤ 2 ^ (da * L) * 2 ^ L := Nat.mul_le_mul_left _ h3
        have h5 := Nat.one_le_two_pow (n := da * L)
        omega
  · have hN := (val_add ha (val_const 1)).lt_tier (t_add ta (t_one (L := L) (by omega)) (by omega)
      (by omega))
    have tj : Tm w L (max da 1 + 1) (lvl (pre ++ env).length) (x :: j :: (pre ++ env)) :=
      tm_idx (by omega)
    exact (t_mul (t_bit (ta.ext he) tj (by omega)) (t_bit (tb.ext he) tj (by omega))
        (by norm_num)).mono
      (by norm_num)


theorem tm_ruleT (ha : Val w env a A) (hb : Val w env b B') (tup : Tm w L dup up env)
    (tps : Tm w L dps ps env) (ta : Tm w L da a env) (tpt : Tm w L dpt pt env)
        (tb : Tm w L db b env)
    (tz : Tm w L dz z env) (hd : max da db + 1 ≤ 30) (hL : 10 ≤ L) :
    Tm w L 1 (ruleT up ps a pt b z) env := by
  have k := fun (n : ℕ) (hn : n ≤ 3) => (t_small (env := env) (w := w) (L := L) hn (by omega))
  have k4 : Tm w L 1 (const 4) env := t_const (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right
    (by norm_num) (show 3 ≤ L by omega)))
  have tx := tm_xorT' ha hb ta tb (by omega) (by omega)
  have tpar : Tm w L 1 (eqT (mod (ipT a b) (const 2)) (const 0)) env :=
    t_eqT' (t_mod (tm_ipT ha hb ta tb (by omega) (by omega)) (k 2 (by norm_num))
      (Pos.const' (by norm_num))) (k 0 (by norm_num)) (by omega)
  have pos := (t_ite tpar (k 2 (by norm_num)) (k 1 (by norm_num))).mono (d' := 1) (by norm_num)
  have neg := (t_ite tpar (k 1 (by norm_num)) (k 2 (by norm_num))).mono (d' := 1) (by norm_num)
  have cz1 := t_eqT' tz (tm_trZzSubT (k 0 (by norm_num)) tx (by omega) (by omega)) (by omega)
  have cz2 := t_eqT' tz (t_add (t_mul (k 2 (by norm_num)) tx (by omega)) (k 3 le_rfl) (by omega)
    (by omega)) (by omega)
  have cz3 := t_eqT' tz (t_mul (k 2 (by norm_num)) tx (by omega)) (by omega)
  have cz4 := t_eqT' tz (t_add (t_mul (k 2 (by norm_num)) tx (by omega)) k4 (by omega) (by omega))
    (by omega)
  have cu := t_eqT' tup (k 1 (by norm_num)) (by omega)
  have cnn := t_mul (t_sub (k 1 (by norm_num)) (t_eqT' tps (k 2 (by norm_num)) (by omega)))
    (t_sub (k 1 (by norm_num)) (t_eqT' tpt (k 2 (by norm_num)) (by omega))) (by norm_num)
  have cor := fun (n : ℕ)
      (hn : n ≤ 3) => t_lt (k 0 (by norm_num)) (t_add (t_eqT' tps (k n hn) (by omega))
    (t_eqT' tpt (k n hn) (by omega)) (by omega) (by omega)) (by omega)
  have cand := t_mul (t_eqT' ta tb (by omega)) (t_eqT' tz (k 0 (by norm_num)) (by omega))
      (by norm_num)
  unfold ruleT notT orT trAndT
  exact (t_ite (t_eqT' tps tpt (by omega)) (k 0 (by norm_num))
    (t_ite cnn (t_ite cu (t_ite cz1 pos (t_ite cz2 neg (k 0 (by norm_num))))
        (t_ite cz1 pos (k 0 (by norm_num))))
      (t_ite (t_ite cu (cor 0 (by norm_num)) (cor 1 (by norm_num)))
        (t_ite cu (t_ite cz3 pos (t_ite cz4 neg (k 0 (by norm_num))))
            (t_ite cz3 pos (k 0 (by norm_num))))
        (t_ite cand (k 2 (by norm_num)) (k 0 (by norm_num)))))).mono (by omega)

end TierRule

/-! ### Tiers: codes of children -/

theorem mem_le_enc {v : ℕ} : ∀ {vs : List ℕ}, v ∈ vs → v ≤ NatList.enc vs
  | x :: vs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact NatList.le_enc_cons _ _
    · exact (mem_le_enc h).trans (NatList.enc_le_enc_cons x vs)

theorem sq_lt_two_pow : ∀ n, 5 ≤ n → n ^ 2 < 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : 2 * n + 1 ≤ n ^ 2 := by nlinarith
    rw [pow_succ 2 n]
    nlinarith

theorem lt_two_pow_of_codeWidth {A L : ℕ} (hA : 1 ≤ A) (hw : codeWidth A ≤ L) (hL : 5 ≤ L) :
    A < 2 ^ L := by
  unfold codeWidth at hw
  rw [ite_eq_right (by omega)] at hw
  have h1 := Nat.lt_succ_sqrt' (784 * A)
  have h4 : (Nat.sqrt (784 * A)).succ ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h5 := sq_lt_two_pow L hL
  omega


theorem elen_le_of_entries {K : ℕ} : ∀ vs : List ℕ, (∀ v ∈ vs, v < 2 ^ K) →
    NatList.elen vs ≤ vs.length * (2 * K + 1) + 1
  | [], _ => by simp
  | v :: vs, h => by
    have ih := elen_le_of_entries vs (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have hs : v.size ≤ K := Nat.size_le.mpr (h v List.mem_cons_self)
    rw [NatList.elen_cons, List.length_cons]
    nlinarith

theorem enc_lt_of_entries {K : ℕ} (vs : List ℕ) (h : ∀ v ∈ vs, v < 2 ^ K) :
    NatList.enc vs < 2 ^ (vs.length * (2 * K + 1) + 1) :=
  lt_of_lt_of_le (NatList.enc_lt vs) (Nat.pow_le_pow_right (by norm_num) (elen_le_of_entries vs h))

section TierChild

variable {L : ℕ}

/-- **The code of a list of terms** has tier `d` when its value is below `2^(d·L)`, whatever the
(bounded) tiers of its entries: every entry lies below the code. -/
theorem val_tm_encV' {d : ℕ} (hd : 2 * d + 1 ≤ 32) (hd1 : 1 ≤ d) (hL : 9 ≤ L) :
    ∀ {ts : List Term} {vs : List ℕ},
      List.Forall₂ (fun t v => Val w env t v ∧ ∃ d', d' ≤ 128 ∧ Tm w L d' t env) ts vs →
      NatList.enc vs < 2 ^ (d * L) → Val w env (encV ts) (NatList.enc vs) ∧ Tm w L d (encV ts) env
  | [], [], .nil, h => ⟨val_encV_nil, tm_const h (by omega)⟩
  | _ :: _, v :: vs, .cons ⟨hv, _, _, ht⟩ hr, h => by
    have ih := val_tm_encV' hd hd1 hL hr (lt_of_le_of_lt (NatList.enc_le_enc_cons v vs) h)
    have htv := tm_val ht hv (lt_of_le_of_lt (NatList.le_enc_cons v vs) h)
    exact ⟨val_encV_cons hv ih.1, tm_consV hv htv ih.1 ih.2 hd (by omega) hL
      (by rw [consF_enc]; exact h)⟩

theorem small_lt_two_pow {k : ℕ} (hk : k ≤ 13) (hL : 10 ≤ L) : k < 2 ^ L :=
  lt_of_lt_of_le (lt_of_le_of_lt hk (by norm_num)) (Nat.pow_le_pow_right (by norm_num) hL)

theorem enc_zero_lt {d : ℕ} (hd : 1 ≤ d) (hL : 2 ≤ L) : NatList.enc [0] < 2 ^ (d * L) := by
  have : NatList.enc [0] = 2 := rfl
  rw [this]
  exact lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num)
    (show 2 ≤ d * L from le_trans hL (Nat.le_mul_of_pos_left _ hd)))

variable (S : Setup) {A Bv : ℕ} {B e i : Term} {iv de di dc : ℕ}

theorem tm_trChildT {up : Bool} {x y m : Label} {lo hi : ℕ} {T : Multiset (HPlace × ℕ)} {c : ℤ}
    (hf : TrFit A Bv up x y m T) (hB : Val w env B Bv) (tB : Tm w L 1 B env) (hBL : Bv ≤ L)
    (hL : 10 ≤ L) (he : Val w env e (S.code (.tr up x y m lo hi T c))) (te : Tm w L de e env)
    (hde : de ≤ 15) (hix : Val w env i iv) (ti : Tm w L di i env) (hdc1 : 1 ≤ dc)
    (hdc : dc ≤ 15) (hcode : S.code (S.gen.child (.tr up x y m lo hi T c) iv) < 2 ^ (dc * L)) :
    Tm w L dc (trChildT B e i) env := by
  obtain ⟨-, f1, f2, f3, f4, f5, f6, f7, -⟩ := fields_tr S up x y m lo hi T c
  have vf : ∀ k, Val w env (getV e (const k)) (getF (S.code (.tr up x y m lo hi T c)) k) :=
    fun k => val_getV he (val_const k)
  have tf : ∀ k ≤ 13, Tm w L de (getV e (const k)) env := fun k hk =>
    tm_getV he te (by omega) (val_const k) (t_const (small_lt_two_pow hk hL)) (by norm_num)
        (by omega)
  have vup := (vf 1).congr f1
  have vX := (vf 2).congr f2
  have vY := (vf 3).congr f3
  have vM := (vf 4).congr f4
  have vlo := (vf 5).congr f5
  have vhi := (vf 6).congr f6
  have vT := (vf 7).congr f7
  have hAL := lt_two_pow_of_codeWidth hf.one_le (hf.width_le.trans hBL) (by omega)
  have hWA := hf.tWt_le lo hi
  have hWL : tWt (srcSub up x y m lo hi) T < 2 ^ L := lt_of_le_of_lt hWA hAL
  have hcw : codeWidth (tWt (srcSub up x y m lo hi) T) ≤ L :=
    (codeWidth_le_of_le hWA).trans (hf.width_le.trans hBL)
  have vW := (val_trWT hB (vf 1) (vf 2) (vf 3) (vf 4) (vf 5) (vf 6) (vf 7)).congr
    (by rw [f1, f2, f3, f4, f5, f6, f7, trWN_eq up hf.lx hf.ly hf.lm lo hi hf.valid hf.tf])
  have tW := tm_trWT hB vup vX vY vM vlo vhi vT tB (tf 1 (by omega)) (tf 2 (by omega))
      (tf 3 (by omega))
    (tf 4 (by omega)) (tf 5 (by omega)) (tf 6 (by omega)) (tf 7 (by omega)) (by omega) (by omega)
    (by omega) hL hBL hf hAL
  have vc := val_pivOkT hB (vf 1) (vf 2) (vf 3) (vf 4) (vf 5) (vf 6) (vf 7)
    (val_trWT hB (vf 1) (vf 2) (vf 3) (vf 4) (vf 5) (vf 6) (vf 7)) hix
  have tc := tm_pivOkT hf hAL hB vup vX vY vM vlo vhi vT vW hix tB (tf 1 (by omega))
      (tf 2 (by omega))
    (tf 3 (by omega)) (tf 4 (by omega)) (tf 5 (by omega)) (tf 6 (by omega)) (tf 7 (by omega)) tW ti
    (by omega) (by omega) hWL hcw hL hBL
  have hval := val_trChildT hB he hix
  rw [trChildN_code S hf c iv] at hval
  unfold trChildT at hval ⊢
  dsimp only at hval ⊢
  refine tm_ite_val vc tc (fun hp => ?_) (fun hp => ?_)
  · have hpiv : PivOkN Bv (getF (S.code (.tr up x y m lo hi T c)) 1)
      (getF (S.code (.tr up x y m lo hi T c)) 2)
        (getF (S.code (.tr up x y m lo hi T c)) 3) (getF (S.code (.tr up x y m lo hi T c)) 4)
        (getF (S.code (.tr up x y m lo hi T c)) 5) (getF (S.code (.tr up x y m lo hi T c)) 6)
        (getF (S.code (.tr up x y m lo hi T c)) 7)
        (trWN Bv (getF (S.code (.tr up x y m lo hi T c)) 1)
            (getF (S.code (.tr up x y m lo hi T c)) 2)
          (getF (S.code (.tr up x y m lo hi T c)) 3) (getF (S.code (.tr up x y m lo hi T c)) 4)
          (getF (S.code (.tr up x y m lo hi T c)) 5) (getF (S.code (.tr up x y m lo hi T c)) 6)
          (getF (S.code (.tr up x y m lo hi T c)) 7)) iv := by
      by_contra hn; rw [ite_eq_right hn] at hp; exact absurd hp (lt_irrefl 0)
    have hbound : trChildN Bv (S.code (.tr up x y m lo hi T c)) iv < 2 ^ (dc * L) := by
      rw [trChildN_code S hf c iv]; exact hcode
    unfold trChildN at hbound
    dsimp only at hbound
    rw [ite_eq_left hpiv] at hbound
    have vWr := val_trWT hB (vf 1) (vf 2) (vf 3) (vf 4) (vf 5) (vf 6) (vf 7)
    have dg := fun (j : ℕ) (hj : j ≤ 6) => tm_pdigT vW tW hWL hcw hL ti hj
    have vd := fun j => val_pdigT vWr hix j
    have hp3 := val_mod (vd 1) (val_const 3)
    have hj3 := val_div (vd 1) (val_const 3)
    have tp3 := t_mod_left (dg 1 (by norm_num))
        (t_small (k := 3) (L := L) (env := env) (w := w) le_rfl
      (by omega))
    have tj3 := t_div (dg 1 (by norm_num)) (t_small (k := 3) (L := L) (env := env) (w := w) le_rfl
      (by omega))
    have
        vm := fun j => val_mod (vd j) (val_pow2 (val_cminT (val_msEndT hB (vd j) (val_const 0)) hB))
    have tm := fun (j : ℕ) (hj : j ≤ 6) => t_mod_left (dg j hj) (pow2_tier (d := 2)
      (val_cminT (val_msEndT hB (vd j) (val_const 0)) hB)
      (tm_val (tm_cminT (tm_msEndT hB (vd j) (val_const 0) tB (dg j hj)
        (t_small (k := 0) (by norm_num) (by omega)) le_rfl (by norm_num) (by omega) hBL)
        (tB.mono (by norm_num)) (by omega)) (val_cminT (val_msEndT hB (vd j) (val_const 0)) hB)
        (by rw [one_mul]; exact lt_of_le_of_lt ((min_le_right _ _).trans hBL) Nat.lt_two_pow_self))
      (min_le_right _ _) (by omega) (by norm_num) (by omega))
    have hm := fun (j : ℕ) (hj : j ≤ 6) => (vm j).lt_tier (tm j hj)
    have inner1 := (val_tm_encV' (d := 13) (env := env) (w := w) (L := L) (by norm_num)
        (by norm_num)
      (by omega) (.cons ⟨vm 2, 2, by norm_num, tm 2 (by norm_num)⟩ (.cons ⟨vm 3, 2, by norm_num,
        tm 3 (by norm_num)⟩ (.cons ⟨vm 4, 2, by norm_num, tm 4 (by norm_num)⟩ .nil)))
      (lt_of_lt_of_le (enc_lt_of_entries (K := 2 * L) _ (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        exacts [hm 2 (by norm_num), hm 3 (by norm_num), hm 4 (by norm_num)]))
        (Nat.pow_le_pow_right (by norm_num)
            (by simp only [List.length_cons, List.length_nil]; omega)))).2
    have vr := fun (k : ℕ) j => val_restT hB (vf 7) hp3 hj3 k (vd j)
    have tr := fun (k : ℕ) (hk : k ≤ 3) (j : ℕ) (hj : j ≤ 6) => tm_restT hB (vf 7) hp3 hj3 (vd j) tB
      (tf 7 (by omega)) tp3 tj3 (dg j hj) (by omega) hL hBL k hk
    have hr := fun (k : ℕ) (hk : k ≤ 3) (j : ℕ) (hj : j ≤ 6) => (vr k j).lt_tier (tr k hk j hj)
    have inner2 := (val_tm_encV' (d := 7) (env := env) (w := w) (L := L) (by norm_num) (by norm_num)
      (by omega) (.cons ⟨vr 0 2, 1, by norm_num, tr 0 (by norm_num) 2 (by norm_num)⟩
        (.cons ⟨vr 1 3, 1, by norm_num, tr 1 (by norm_num) 3 (by norm_num)⟩
        (.cons ⟨vr 2 4, 1, by norm_num, tr 2 (by norm_num) 4 (by norm_num)⟩ .nil)))
      (lt_of_lt_of_le (enc_lt_of_entries (K := 1 * L) _ (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        exacts [hr 0 (by norm_num) 2 (by norm_num), hr 1 (by norm_num) 3 (by norm_num),
          hr 2 (by norm_num) 4 (by norm_num)]))
        (Nat.pow_le_pow_right (by norm_num)
            (by simp only [List.length_cons, List.length_nil]; omega)))).2
    refine (val_tm_encV' (d := dc) (by omega) hdc1 (by omega)
      (.cons ⟨val_const 8, 1, by norm_num, t_const (small_lt_two_pow (by norm_num) hL)⟩
      (.cons ⟨vf 1, _, by omega, tf 1 (by norm_num)⟩ (.cons ⟨vf 2, _, by omega, tf 2 (by norm_num)⟩
      (.cons ⟨vf 3, _, by omega, tf 3 (by norm_num)⟩ (.cons ⟨vf 4, _, by omega, tf 4 (by norm_num)⟩
      (.cons ⟨vf 5, _, by omega, tf 5 (by norm_num)⟩
      (.cons ⟨val_add (vf 5) (vd 0), _, by omega, t_add (tf 5 (by norm_num)) (dg 0 (by norm_num))
        (by omega) (by omega)⟩
      (.cons ⟨vf 6, _, by omega, tf 6 (by norm_num)⟩
      (.cons ⟨val_add (val_plOfT (vf 1) hp3) (val_mul (val_const 8) hj3), _, by omega,
        t_add (tm_plOfT (tf 1 (by norm_num)) tp3 (by omega))
          (t_mul (t_const (small_lt_two_pow (k := 8) (by norm_num) hL)) tj3 (by norm_num))
          (by omega) (by omega)⟩
      (.cons ⟨val_encV_cons (vm 2) (val_encV_cons (vm 3) (val_encV_cons (vm 4) val_encV_nil)), 13,
        by norm_num, inner1⟩
      (.cons ⟨val_encV_cons (vr 0 2) (val_encV_cons (vr 1 3) (val_encV_cons (vr 2 4) val_encV_nil)),
          7,
        by norm_num, inner2⟩
      (.cons
          ⟨val_trZzSubT (vd 5) vWr,
          _, by omega, tm_trZzSubT (dg 5 (by norm_num)) tW (by omega) (by omega)⟩
      (.cons
          ⟨val_trZzSubT (vd 6) vWr,
          _, by omega, tm_trZzSubT (dg 6 (by norm_num)) tW (by omega) (by omega)⟩
      (.cons ⟨val_zzAddT (vf 8) (val_mul (val_const 2) vWr) (val_add (vd 5) (vd 6)), _, by omega,
        tm_zzAddT (tf 8 (by norm_num)) (t_mul (t_small (k := 2) (by norm_num) (by omega)) tW
            (by norm_num))
          (t_add (dg 5 (by norm_num)) (dg 6 (by norm_num)) (by omega) (by omega)) (by omega)
              (by omega)⟩
        .nil)))))))))))))) hbound).2
  · exact (val_tm_encV' (d := dc) (by omega) hdc1 (by omega)
      (.cons ⟨val_const 0, 1, by norm_num, t_small (by norm_num) (by omega)⟩ .nil)
      (enc_zero_lt hdc1 (by omega))).2


theorem tm_srcPlT {X Y k : Term} {Xv Yv dX dY dk : ℕ} (hB : Val w env B Bv) (hX : Val w env X Xv)
    (hY : Val w env Y Yv) (tB : Tm w L 1 B env) (tX : Tm w L dX X env) (tY : Tm w L dY Y env)
    (tk : Tm w L dk k env) (hL : 10 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (srcPlT B X Y k) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have c1 := tm_cardT hB hX (val_const 0) tB tX t0 le_rfl (by norm_num) (by omega) hBL
  have c2 := tm_cardT hB hY (val_const 0) tB tY t0 le_rfl (by norm_num) (by omega) hBL
  exact (t_ite (t_lt tk c1 (by omega)) t0
      (t_ite (t_lt tk (t_add c1 c2 (by omega) (by omega)) (by omega))
    (t_one (by omega)) (t_small (k := 2) (by norm_num) (by omega)))).mono (by omega)

theorem tm_trmChildT {up : Bool} {x y m : Label} {lo pos hi : ℕ} {t : HPlace × ℕ}
    {T₁ T₂ : Multiset (HPlace × ℕ)} {c₁ c₀ c₂ : ℤ}
    (he : Val w env e (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂))) (te : Tm w L de e env)
    (hde : de ≤ 15) (hL : 10 ≤ L) (hix : Val w env i iv) (ti : Tm w L di i env) (hdc1 : 1 ≤ dc)
    (hdc : dc ≤ 15) (hcode : S.code (S.gen.child (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂) iv) <
      2 ^ (dc * L)) : Tm w L dc (trmChildT e i) env := by
  set ev := S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)
  have vf : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  have tf : ∀ k ≤ 13, Tm w L de (getV e (const k)) env := fun k hk =>
    tm_getV he te (by omega) (val_const k) (t_const (small_lt_two_pow hk hL)) (by norm_num)
        (by omega)
  have hbound : trmChildN ev iv < 2 ^ (dc * L) := by
    rw [trmChildN_code S up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ iv]; exact hcode
  unfold trmChildN at hbound
  have F := fun k (hk : k ≤ 13) => (⟨vf k, de, by omega, tf k hk⟩ :
    Val w env (getV e (const k)) (getF ev k) ∧ ∃ d', d' ≤ 128 ∧ Tm w L d' (getV e (const k)) env)
  have K := fun (k : ℕ)
      (hk : k ≤ 13) => (⟨val_const k, 1, by norm_num, t_const (small_lt_two_pow hk hL)⟩ :
    Val w env (const k) k ∧ ∃ d', d' ≤ 128 ∧ Tm w L d' (const k) env)
  unfold trmChildT
  refine tm_ite_val (val_eqT hix (val_const 0))
      (t_eqT' ti (t_small (k := 0) (by norm_num) (by omega))
    (by omega)) (fun hp => ?_) (fun hp => ?_)
  · have h0 : iv = 0 := by by_contra hn; rw [ite_eq_right hn] at hp; exact absurd hp (lt_irrefl 0)
    rw [ite_eq_left h0] at hbound
    exact (val_tm_encV' (d := dc) (by omega) hdc1 (by omega) (.cons (K 7 (by norm_num))
      (.cons (F 1 (by norm_num)) (.cons (F 2 (by norm_num)) (.cons (F 3 (by norm_num))
      (.cons (F 4 (by norm_num)) (.cons (F 5 (by norm_num)) (.cons (F 6 (by norm_num))
      (.cons (F 9 (by norm_num)) (.cons (F 11 (by norm_num)) .nil))))))))) hbound).2
  · have h0 : ¬ iv = 0 := fun hn => hp (by rw [ite_eq_left hn]; exact Nat.one_pos)
    rw [ite_eq_right h0] at hbound
    exact (val_tm_encV' (d := dc) (by omega) hdc1 (by omega) (.cons (K 9 (by norm_num))
      (.cons (F 1 (by norm_num)) (.cons (F 2 (by norm_num)) (.cons (F 3 (by norm_num))
      (.cons (F 4 (by norm_num)) (.cons (F 6 (by norm_num)) (.cons (F 7 (by norm_num))
      (.cons (F 8 (by norm_num)) (.cons (F 10 (by norm_num)) (.cons (F 12 (by norm_num))
      (.cons (F 13 (by norm_num)) .nil))))))))))) hbound).2

theorem tm_trrChildT {up : Bool} {x y m : Label} {pos hi : ℕ} {t : HPlace × ℕ}
    {T₂ : Multiset (HPlace × ℕ)} {c₀ c₂ : ℤ} (hf : TrFit A Bv up x y m T₂) (ht : ValidPl up t.1)
    (hB : Val w env B Bv) (tB : Tm w L 1 B env) (hBL : Bv ≤ L)
    (he : Val w env e (S.code (.trr up x y m pos hi t T₂ c₀ c₂))) (te : Tm w L de e env)
    (hde : de ≤ 15) (hL : 10 ≤ L) (hix : Val w env i iv) (ti : Tm w L di i env) (hdc1 : 1 ≤ dc)
    (hdc : dc ≤ 15) (hcode : S.code (S.gen.child (.trr up x y m pos hi t T₂ c₀ c₂) iv) < 2 ^
        (dc * L)) :
    Tm w L dc (trrChildT B e i) env := by
  set ev := S.code (.trr up x y m pos hi t T₂ c₀ c₂)
  have vf : ∀ k, Val w env (getV e (const k)) (getF ev k) := fun k => val_getV he (val_const k)
  have tf : ∀ k ≤ 13, Tm w L de (getV e (const k)) env := fun k hk =>
    tm_getV he te (by omega) (val_const k) (t_const (small_lt_two_pow hk hL)) (by norm_num)
        (by omega)
  have hbound : trrChildN Bv ev iv < 2 ^ (dc * L) := by
    rw [trrChildN_code S hf ht c₀ c₂ iv]; exact hcode
  unfold trrChildN at hbound
  have F := fun k (hk : k ≤ 13) => (⟨vf k, de, by omega, tf k hk⟩ :
    Val w env (getV e (const k)) (getF ev k) ∧ ∃ d', d' ≤ 128 ∧ Tm w L d' (getV e (const k)) env)
  have K := fun (k : ℕ)
      (hk : k ≤ 13) => (⟨val_const k, 1, by norm_num, t_const (small_lt_two_pow hk hL)⟩ :
    Val w env (const k) k ∧ ∃ d', d' ≤ 128 ∧ Tm w L d' (const k) env)
  unfold trrChildT
  dsimp only
  refine tm_ite_val (val_eqT hix (val_const 0))
      (t_eqT' ti (t_small (k := 0) (by norm_num) (by omega))
    (by omega)) (fun hp => ?_) (fun hp => ?_)
  · have h0 : iv = 0 := by by_contra hn; rw [ite_eq_right hn] at hp; exact absurd hp (lt_irrefl 0)
    rw [ite_eq_left h0] at hbound
    have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
    have hl := val_srcLenT hB (vf 1) (vf 2) (vf 3) (vf 4)
    have tl := tm_srcLenT hB (vf 1) (vf 2) (vf 3) (vf 4) tB (tf 1 (by norm_num))
        (tf 2 (by norm_num))
      (tf 3 (by norm_num)) (tf 4 (by norm_num)) hL hBL
    have tm8 := t_mod_left (tf 7 (by norm_num)) (t_const (L := L) (env := env) (w := w)
      (small_lt_two_pow (k := 8) (by norm_num) hL))
    have td8 := t_div (tf 7 (by norm_num)) (t_const (L := L) (env := env) (w := w)
      (small_lt_two_pow (k := 8) (by norm_num) hL))
    have vpt := val_plIdxT (val_mod (vf 7) (val_const 8))
    have vjt := val_div (vf 7) (val_const 8)
    have tpt := tm_plIdxT tm8 (by omega)
    have va := val_iteP (val_lt (vf 5) hl) (val_srcTyT hB (vf 1) (vf 2) (vf 3) (vf 4) (vf 5)) vjt
    have ta := t_ite (t_lt (tf 5 (by norm_num)) tl (by omega))
        (tm_srcTyT hB (vf 1) (vf 2) (vf 3) (vf 4)
      (vf 5) tB (tf 1 (by norm_num)) (tf 2 (by norm_num)) (tf 3 (by norm_num)) (tf 4 (by norm_num))
      (tf 5 (by norm_num)) (by omega) hL hBL) td8
    have tps := t_ite (t_lt (tf 5 (by norm_num)) tl (by omega)) (tm_srcPlT hB (vf 2) (vf 3) tB
      (tf 2 (by norm_num)) (tf 3 (by norm_num)) (tf 5 (by norm_num)) hL hBL) tpt
    have vr := val_ruleT (vf 1) (val_iteP (val_lt (vf 5) hl) (val_srcPlT hB (vf 2) (vf 3) (vf 5))
        vpt)
      va vpt vjt (vf 9)
    exact (val_tm_encV' (d := dc) (by omega) hdc1 (by omega) (.cons (K 1 (by norm_num))
      (.cons
          ⟨vr,
          1, by norm_num, tm_ruleT va vjt (tf 1 (by norm_num)) tps ta tpt td8 (tf 9 (by norm_num))
        (by omega) hL⟩ .nil)) hbound).2
  · have h0 : ¬ iv = 0 := fun hn => hp (by rw [ite_eq_left hn]; exact Nat.one_pos)
    rw [ite_eq_right h0] at hbound
    exact (val_tm_encV' (d := dc) (by omega) hdc1 (by omega) (.cons (K 7 (by norm_num))
      (.cons (F 1 (by norm_num)) (.cons (F 2 (by norm_num)) (.cons (F 3 (by norm_num))
      (.cons (F 4 (by norm_num)) (.cons ⟨val_add (vf 5) (val_const 1), _, by omega,
        t_add (tf 5 (by norm_num)) (t_one (by omega)) (by omega) (by omega)⟩
            (.cons (F 6 (by norm_num))
      (.cons (F 8 (by norm_num)) (.cons (F 10 (by norm_num)) .nil))))))))) hbound).2


theorem tr_W_facts {up : Bool} {x y m : Label} {lo hi : ℕ} {T : Multiset (HPlace × ℕ)} {c : ℤ}
    (hf : TrFit A Bv up x y m T) (hB : Val w env B Bv) (tB : Tm w L 1 B env) (hBL : Bv ≤ L)
    (hL : 10 ≤ L) (he : Val w env e (S.code (.tr up x y m lo hi T c))) (te : Tm w L de e env)
    (hde : de ≤ 15) :
    Val w env (trWT B (getV e (const 1)) (getV e (const 2)) (getV e (const 3)) (getV e (const 4))
        (getV e (const 5)) (getV e (const 6)) (getV e (const 7))) (tWt (srcSub up x y m lo hi) T) ∧
      Tm w L 1 (trWT B (getV e (const 1)) (getV e (const 2)) (getV e (const 3)) (getV e (const 4))
        (getV e (const 5)) (getV e (const 6)) (getV e (const 7))) env ∧
      tWt (srcSub up x y m lo hi) T < 2 ^ L ∧ codeWidth (tWt (srcSub up x y m lo hi) T) ≤ L := by
  obtain ⟨-, f1, f2, f3, f4, f5, f6, f7, -⟩ := fields_tr S up x y m lo hi T c
  have vf : ∀ k, Val w env (getV e (const k)) (getF (S.code (.tr up x y m lo hi T c)) k) :=
    fun k => val_getV he (val_const k)
  have tf : ∀ k ≤ 13, Tm w L de (getV e (const k)) env := fun k hk =>
    tm_getV he te (by omega) (val_const k) (t_const (small_lt_two_pow hk hL)) (by norm_num)
        (by omega)
  have hAL := lt_two_pow_of_codeWidth hf.one_le (hf.width_le.trans hBL) (by omega)
  have hWA := hf.tWt_le lo hi
  refine ⟨(val_trWT hB (vf 1) (vf 2) (vf 3) (vf 4) (vf 5) (vf 6) (vf 7)).congr
    (by rw [f1, f2, f3, f4, f5, f6, f7, trWN_eq up hf.lx hf.ly hf.lm lo hi hf.valid hf.tf]),
    tm_trWT hB ((vf 1).congr f1) ((vf 2).congr f2) ((vf 3).congr f3) ((vf 4).congr f4)
        ((vf 5).congr f5)
      ((vf 6).congr f6) ((vf 7).congr f7) tB (tf 1 (by omega)) (tf 2 (by omega)) (tf 3 (by omega))
      (tf 4 (by omega)) (tf 5 (by omega)) (tf 6 (by omega)) (tf 7 (by omega)) (by omega) (by omega)
      (by omega) hL hBL hf hAL, lt_of_le_of_lt hWA hAL, (codeWidth_le_of_le hWA).trans
          (hf.width_le.trans hBL)⟩

/-- **Tiers of the transport machine**: on the code of a state of the invariant, given in a term of
tier `de ≤ 15`, with a fuel term `B` of tier `1` whose value is at most `L`, the tag, the index
length and the leaf have tier `1`, and the child at any index has tier `dc` as soon as the code of
the child is below `2^(dc·L)` (`dc ≤ 15`). -/
theorem tm_tr_agree {st : St} (h : TrInv A Bv st) (hB : Val w env B Bv) (tB : Tm w L 1 B env)
    (hBL : Bv ≤ L) (hL : 10 ≤ L) (he : Val w env e (S.code st)) (te : Tm w L de e env)
    (hde : de ≤ 15) (hix : Val w env i iv) (ti : Tm w L di i env) (hdc1 : 1 ≤ dc)
    (hdc : dc ≤ 15) (hcode : S.code (S.gen.child st iv) < 2 ^ (dc * L)) :
    Tm w L 1 (trTagT e) env ∧ Tm w L 1 (trWidthT B e) env ∧ Tm w L 1 (trLeafT B e) env ∧
      Tm w L dc (trChildAllT B e i) env := by
  have vf : ∀ k, Val w env (getV e (const k))
      (getF (S.code st) k) := fun k => val_getV he (val_const k)
  have tf : ∀ k ≤ 13, Tm w L de (getV e (const k)) env := fun k hk =>
    tm_getV he te (by omega) (val_const k) (t_const (small_lt_two_pow hk hL)) (by norm_num)
        (by omega)
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have k7 : Tm w L 1 (const 7) env := t_const (small_lt_two_pow (by norm_num) hL)
  have k8 : Tm w L 1 (const 8) env := t_const (small_lt_two_pow (by norm_num) hL)
  have c7 := t_eqT' (tf 0 (by norm_num)) k7 (by omega)
  have c8 := t_eqT' (tf 0 (by norm_num)) k8 (by omega)
  have v7 := val_eqT (vf 0) (val_const 7)
  have v8 := val_eqT (vf 0) (val_const 8)
  have tag : Tm w L 1 (trTagT e) env :=
    (t_ite c7 (t_lt (tf 5 (by norm_num)) (tf 6 (by norm_num)) (by omega))
      (t_small (k := 2) (by norm_num) (by omega))).mono (by omega)
  have leaf : Tm w L 1 (trLeafT B e) env := by
    have cc := fun (k : ℕ)
        (hk : k ≤ 3) => t_eqT' (tm_cardT hB (val_getV (vf 7) (val_const k)) (val_const 0)
      tB (tm_getV (vf 7) (tf 7 (by norm_num)) (by omega) (val_const k) (t_small hk (by omega))
        (by norm_num) (by omega)) t0 le_rfl (by norm_num) (by omega) hBL) t0 (by omega)
    refine tm_val (t_mul c7 (t_mul (cc 0 (by norm_num))
        (t_mul (cc 1 (by norm_num)) (t_mul (cc 2 (by norm_num))
      (t_eqT' (tf 8 (by norm_num)) t0 (by omega)) (by norm_num)) (by norm_num)) (by norm_num))
          (by norm_num))
      (val_trLeafT hB he) ?_
    rw [one_mul]; unfold trLeafN; split_ifs
    exacts [Nat.one_lt_two_pow (by omega), Nat.two_pow_pos _]
  refine ⟨tag, ?_, leaf, ?_⟩
  · unfold trWidthT
    refine tm_ite_val v7 c7 (fun hp => ?_) (fun _ => t0)
    cases st with
    | tr up x y m lo hi T c =>
      obtain ⟨vW, tW, hWL, hcw⟩ := tr_W_facts S h hB tB hBL hL he te hde
      exact tm_pivOffT vW tW hWL hcw hL 7 le_rfl
    | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
      rw [(fields_trm S up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂).1] at hp; exact absurd hp (by decide)
    | trr up x y m pos hi t T₂ c₀ c₂ =>
      rw [(fields_trr S up x y m pos hi t T₂ c₀ c₂).1] at hp; exact absurd hp (by decide)
    | _ => exact (h : False).elim
  · unfold trChildAllT
    cases st with
    | tr up x y m lo hi T c =>
      refine tm_ite_val v7 c7
          (fun _ => tm_trChildT S h hB tB hBL hL he te hde hix ti hdc1 hdc hcode)
        (fun hp => ?_)
      rw [(fields_tr S up x y m lo hi T c).1] at hp; exact absurd (by decide) hp
    | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
      have f0 := (fields_trm S up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂).1
      refine tm_ite_val v7 c7 (fun hp => ?_) (fun _ => tm_ite_val v8 c8
        (fun _ => tm_trmChildT S he te hde hL hix ti hdc1 hdc hcode) (fun hp => ?_))
      · rw [f0] at hp; exact absurd hp (by decide)
      · rw [f0] at hp; exact absurd (by decide) hp
    | trr up x y m pos hi t T₂ c₀ c₂ =>
      have f0 := (fields_trr S up x y m pos hi t T₂ c₀ c₂).1
      refine tm_ite_val v7 c7 (fun hp => ?_) (fun _ => tm_ite_val v8 c8 (fun hp => ?_)
        (fun _ => tm_trrChildT S h.1 h.2 hB tB hBL he te hde hL hix ti hdc1 hdc hcode))
      · rw [f0] at hp; exact absurd hp (by decide)
      · rw [f0] at hp; exact absurd hp (by decide)
    | _ => exact (h : False).elim

/-- **Values of the transport machine**: on the code of a state of the invariant, the terms compute
the tag, the index length, the leaf value and the code of every child. -/
theorem val_tr_agree {st : St} (h : TrInv A Bv st) (hB : Val w env B Bv)
    (he : Val w env e (S.code st))
    (hix : Val w env i iv) :
    Val w env (trTagT e) (AGen.kindTag (S.gen.kind st)) ∧ Val w env (trWidthT B e) (S.gen.width st)
        ∧
      Val w env (trLeafT B e) (trLeafN Bv (S.code st)) ∧
      ((trLeafN Bv (S.code st) : ℕ) : ℤ) = S.gen.leafVal st ∧
      Val w env (trChildAllT B e i) (S.code (S.gen.child st iv)) := by
  obtain ⟨-, hTag, hWid, hLeaf, hCh⟩ := tr_agree S h
  exact ⟨(val_trTagT he).congr hTag, (val_trWidthT hB he).congr hWid, val_trLeafT hB he, hLeaf,
    (val_trChildAllT hB he hix).congr (hCh iv)⟩

end TierChild

end Cslib.Complexity.NtimeDspace.Cube.Num
