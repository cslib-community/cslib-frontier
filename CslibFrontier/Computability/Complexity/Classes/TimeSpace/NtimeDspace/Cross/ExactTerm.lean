/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactArith
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Closed
public import Mathlib.Data.List.GetD

/-!
# Values and bounds of terms in every extension of an environment

`Val w t env v` says that `t` has value `v` in `env` and in every extension `extra ++ env`;
`Bd w M t env` says that every value arising in `t` is at most `M` in every such extension. Both
are closed under extension by definition, so the bodies of `letT` and `foldT`, which are
instantiated at deeper environments, compose without separate stability arguments. Each
combinator has a `val_` and a `bd_` lemma.

`call1 q a` and `call3 q a b c` run programs closed in one and three variables on argument terms,
and `closeAt n p` makes any program closed in `n` variables without changing its meaning on
environments of length `n` (this is the closing of `Cross.WalkTermBase`, restated here so that
the module does not depend on the walker).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset

variable {w : List Bool} {M : ℕ}

/-- `t` has value `v` in every extension of `env`. -/
def Val (w : List Bool) (t : Term) (env : List ℕ) (v : ℕ) : Prop :=
  ∀ extra : List ℕ, t.denote w (extra ++ env) = v

/-- Every value arising in `t` is at most `M`, in every extension of `env`. -/
def Bd (w : List Bool) (M : ℕ) (t : Term) (env : List ℕ) : Prop :=
  ∀ extra : List ℕ, t.Bnd w M (extra ++ env)

variable {t a b c e i n init : Term} {env : List ℕ} {x y z v : ℕ}

theorem Val.ext (h : Val w t env v) (pre : List ℕ) : Val w t (pre ++ env) v := fun extra => by
  rw [← List.append_assoc]; exact h _

theorem Val.eq (h : Val w t env v) : t.denote w env = v := by simpa using h []

theorem Val.cons (h : Val w t env v) (u : ℕ) : Val w t (u :: env) v := h.ext [u]

theorem Bd.ext (h : Bd w M t env) (pre : List ℕ) : Bd w M t (pre ++ env) := fun extra => by
  rw [← List.append_assoc]; exact h _

theorem Bd.bnd (h : Bd w M t env) : t.Bnd w M env := by simpa using h []

/-! ### Variables -/

theorem val_lvl {l : ℕ} (hl : l < env.length) :
    Val w (lvl l) env (env.getD (env.length - l - 1) 0) := fun extra => by
  rw [stableAt_lvl hl extra]; rfl

theorem val_top (env : List ℕ) (u : ℕ) : Val w (lvl env.length) (u :: env) u := fun extra => by
  rw [stableAt_lvl (by simp) extra, denote_lvl_let]

theorem val_acc (env : List ℕ) (u k : ℕ) : Val w (lvl (env.length + 1)) (u :: k :: env) u :=
  fun extra => by rw [stableAt_lvl (by simp) extra, denote_lvl_acc]

theorem val_idx (env : List ℕ) (u k : ℕ) : Val w (lvl env.length) (u :: k :: env) k :=
  fun extra => by rw [stableAt_lvl (by simp) extra, denote_lvl_index]

theorem bd_lvl (l : ℕ) (env : List ℕ) : Bd w M (lvl l) env := fun _ => trivial

/-! ### Operations -/

theorem val_const (k : ℕ) (env : List ℕ) : Val w (const k) env k := fun _ => rfl

theorem bd_const {k : ℕ} (h : k ≤ M) (env : List ℕ) : Bd w M (const k) env := fun _ => h

theorem val_add (ha : Val w a env x) (hb : Val w b env y) : Val w (add a b) env (x + y) :=
  fun extra => by simp [ha extra, hb extra]

theorem bd_add (ha : Bd w M a env) (hb : Bd w M b env) (hva : Val w a env x) (hvb : Val w b env y)
    (h : x + y ≤ M) : Bd w M (add a b) env :=
  fun extra => ⟨ha extra, hb extra, by
    show a.denote w (extra ++ env) + b.denote w (extra ++ env) ≤ M
    rw [hva extra, hvb extra]; exact h⟩

theorem val_sub (ha : Val w a env x) (hb : Val w b env y) : Val w (sub a b) env (x - y) :=
  fun extra => by simp [ha extra, hb extra]

theorem bd_sub (ha : Bd w M a env) (hb : Bd w M b env) : Bd w M (sub a b) env :=
  fun extra => ⟨ha extra, hb extra⟩

theorem val_mul (ha : Val w a env x) (hb : Val w b env y) : Val w (mul a b) env (x * y) :=
  fun extra => by simp [ha extra, hb extra]

theorem bd_mul (ha : Bd w M a env) (hb : Bd w M b env) (hva : Val w a env x) (hvb : Val w b env y)
    (h : x * y ≤ M) : Bd w M (mul a b) env :=
  fun extra => ⟨ha extra, hb extra, by
    show a.denote w (extra ++ env) * b.denote w (extra ++ env) ≤ M
    rw [hva extra, hvb extra]; exact h⟩

theorem val_div (ha : Val w a env x) (hb : Val w b env y) : Val w (div a b) env (x / y) :=
  fun extra => by simp [ha extra, hb extra]

theorem bd_div (ha : Bd w M a env) (hb : Bd w M b env) : Bd w M (div a b) env :=
  fun extra => ⟨ha extra, hb extra⟩

theorem val_mod (ha : Val w a env x) (hb : Val w b env y) : Val w (mod a b) env (x % y) :=
  fun extra => by simp [ha extra, hb extra]

theorem bd_mod (ha : Bd w M a env) (hb : Bd w M b env) : Bd w M (mod a b) env :=
  fun extra => ⟨ha extra, hb extra⟩

theorem val_bit (ha : Val w a env x) (hb : Val w b env y) :
    Val w (bit a b) env (x / 2 ^ y % 2) :=
  fun extra => by simp only [denote_bit, ha extra, hb extra, toNat_testBit]

theorem bd_bit (ha : Bd w M a env) (hb : Bd w M b env) : Bd w M (bit a b) env :=
  fun extra => ⟨ha extra, hb extra⟩

theorem val_lt (ha : Val w a env x) (hb : Val w b env y) :
    Val w (lt a b) env (if x < y then 1 else 0) :=
  fun extra => by simp [ha extra, hb extra]

theorem bd_lt (ha : Bd w M a env) (hb : Bd w M b env) : Bd w M (lt a b) env :=
  fun extra => ⟨ha extra, hb extra⟩

theorem val_ite (hc : Val w c env z) (ht : Val w t env x) (he : Val w e env y) :
    Val w (ite c t e) env (if 0 < z then x else y) :=
  fun extra => by simp [hc extra, ht extra, he extra]

theorem bd_ite (hc : Bd w M c env) (hvc : Val w c env z) (ht : 0 < z → Bd w M t env)
    (he : ¬ 0 < z → Bd w M e env) : Bd w M (ite c t e) env := fun extra => by
  refine ⟨hc extra, ?_⟩
  show if 0 < c.denote w (extra ++ env) then t.Bnd w M (extra ++ env) else e.Bnd w M (extra ++ env)
  rw [hvc extra]
  split_ifs with h
  · exact ht h extra
  · exact he h extra

/-! ### Binders -/

theorem val_letT {f : Term → Term} (ha : Val w a env x)
    (hf : ∀ pre u, Val w u (pre ++ env) x → Val w (f u) (pre ++ env) v) :
    Val w (letT a f) env v := fun extra => by
  rw [denote_letT, ha extra]
  have := hf (x :: extra) (lvl (extra ++ env).length) (val_top _ x)
  exact this.eq

theorem bd_letT {f : Term → Term} (ha : Val w a env x) (hba : Bd w M a env)
    (hf : ∀ pre u, Val w u (pre ++ env) x → Bd w M u (pre ++ env) → Bd w M (f u) (pre ++ env)) :
    Bd w M (letT a f) env := fun extra => by
  rw [bnd_letT]
  refine ⟨hba extra, ?_⟩
  rw [ha extra]
  exact (hf (x :: extra) (lvl (extra ++ env).length) (val_top _ x) (bd_lvl _ _)).bnd

theorem foldAcc_val {f : Term → Term → Term} {step : ℕ → ℕ → ℕ}
    (hf : ∀ pre u u' p q, Val w u (pre ++ env) p → Val w u' (pre ++ env) q →
      Val w (f u u') (pre ++ env) (step p q)) (extra : List ℕ) (I k : ℕ) :
    foldAcc w f (extra ++ env) I k = (List.range k).foldl step I :=
  foldAcc_eq _ _ step (fun acc j =>
    (hf (acc :: j :: extra) _ _ acc j (val_acc _ acc j) (val_idx _ acc j)).eq) I k

theorem val_foldT {f : Term → Term → Term} {N I : ℕ} (hn : Val w n env N) (hi : Val w init env I)
    (step : ℕ → ℕ → ℕ)
    (hf : ∀ pre u u' p q, Val w u (pre ++ env) p → Val w u' (pre ++ env) q →
      Val w (f u u') (pre ++ env) (step p q)) :
    Val w (foldT n init f) env ((List.range N).foldl step I) := fun extra => by
  rw [denote_foldT, hn extra, hi extra, foldAcc_val hf]

theorem bd_foldT {f : Term → Term → Term} {N I : ℕ} (hn : Val w n env N) (hi : Val w init env I)
    (step : ℕ → ℕ → ℕ)
    (hf : ∀ pre u u' p q, Val w u (pre ++ env) p → Val w u' (pre ++ env) q →
      Val w (f u u') (pre ++ env) (step p q))
    (hbn : Bd w M n env) (hbi : Bd w M init env) (hN : N ≤ M)
    (hbf : ∀ pre u u' p q, q < N → p = (List.range q).foldl step I →
      Val w u (pre ++ env) p → Val w u' (pre ++ env) q →
      Bd w M u (pre ++ env) → Bd w M u' (pre ++ env) → Bd w M (f u u') (pre ++ env)) :
    Bd w M (foldT n init f) env := fun extra => by
  rw [bnd_foldT]
  refine ⟨hbn extra, hbi extra, by rw [hn extra]; exact hN, fun k hk => ?_⟩
  rw [hn extra] at hk
  rw [hi extra, foldAcc_val hf]
  exact (hbf (_ :: k :: extra) _ _ _ k hk rfl (val_acc _ _ k) (val_idx _ _ k) (bd_lvl _ _)
    (bd_lvl _ _)).bnd

/-! ### Sums and products -/

/-- A function of one term, with its meaning. -/
def FVal (w : List Bool) (f : Term → Term) (env : List ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ pre u p, Val w u (pre ++ env) p → Val w (f u) (pre ++ env) (F p)

theorem FVal.ext {f : Term → Term} {F : ℕ → ℕ} (h : FVal w f env F) (pre : List ℕ) :
    FVal w f (pre ++ env) F := fun pre' u p hu => by
  rw [← List.append_assoc] at hu ⊢; exact h _ u p hu

theorem val_sumT {body : Term → Term} {N : ℕ} {F : ℕ → ℕ} (hn : Val w n env N)
    (hb : FVal w body env F) : Val w (sumT n body) env (∑ k ∈ range N, F k) := by
  have := val_foldT (f := fun acc i => add acc (body i)) hn (val_const 0 env)
    (fun acc k => acc + F k) (fun pre u u' p q hu hu' => val_add hu (hb pre u' q hu'))
  rwa [foldl_add_sum, zero_add] at this

theorem bd_sumT {body : Term → Term} {N : ℕ} {F : ℕ → ℕ} (hn : Val w n env N)
    (hb : FVal w body env F) (hbn : Bd w M n env) (hN : N ≤ M)
    (hsum : ∑ k ∈ range N, F k ≤ M)
    (hbb : ∀ pre u q, q < N → Val w u (pre ++ env) q → Bd w M u (pre ++ env) →
      Bd w M (body u) (pre ++ env)) :
    Bd w M (sumT n body) env := by
  refine bd_foldT (f := fun acc i => add acc (body i)) hn (val_const 0 env)
    (fun acc k => acc + F k) (fun pre u u' p q hu hu' => val_add hu (hb pre u' q hu'))
    hbn (bd_const (Nat.zero_le _) _) hN fun pre u u' p q hq hp hu hu' hbu hbu' => ?_
  refine bd_add hbu (hbb pre u' q hq hu' hbu') hu (hb pre u' q hu') ?_
  rw [hp, foldl_add_sum, zero_add, ← sum_range_succ]
  exact le_trans (sum_le_sum_of_subset (range_subset_range.mpr hq)) hsum

/-- A plain product over `k < n`. -/
def prodT (n : Term) (body : Term → Term) : Term :=
  foldT n (const 1) fun acc i => mul acc (body i)

theorem foldl_mul_prod (F : ℕ → ℕ) (N : ℕ) :
    (List.range N).foldl (fun acc k => acc * F k) 1 = ∏ k ∈ range N, F k := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      prod_range_succ]

theorem val_prodT {body : Term → Term} {N : ℕ} {F : ℕ → ℕ} (hn : Val w n env N)
    (hb : FVal w body env F) : Val w (prodT n body) env (∏ k ∈ range N, F k) := by
  have := val_foldT (f := fun acc i => mul acc (body i)) hn (val_const 1 env)
    (fun acc k => acc * F k) (fun pre u u' p q hu hu' => val_mul hu (hb pre u' q hu'))
  rwa [foldl_mul_prod] at this

theorem bd_prodT {body : Term → Term} {N : ℕ} {F : ℕ → ℕ} (hn : Val w n env N)
    (hb : FVal w body env F) (hbn : Bd w M n env) (hN : N ≤ M) (h1 : 1 ≤ M)
    (hprod : ∀ k < N, ∏ i ∈ range (k + 1), F i ≤ M)
    (hbb : ∀ pre u q, q < N → Val w u (pre ++ env) q → Bd w M u (pre ++ env) →
      Bd w M (body u) (pre ++ env)) :
    Bd w M (prodT n body) env := by
  refine bd_foldT (f := fun acc i => mul acc (body i)) hn (val_const 1 env)
    (fun acc k => acc * F k) (fun pre u u' p q hu hu' => val_mul hu (hb pre u' q hu'))
    hbn (bd_const h1 _) hN fun pre u u' p q hq hp hu hu' hbu hbu' => ?_
  refine bd_mul hbu (hbb pre u' q hq hu' hbu') hu (hb pre u' q hu') ?_
  rw [hp, foldl_mul_prod, ← prod_range_succ]
  exact hprod q hq

/-- A product modulo `p` over `k < n`, reducing after every step. -/
def prodModT (p n : Term) (body : Term → Term) : Term :=
  foldT n (const 1) fun acc i => mod (mul acc (body i)) p

theorem foldl_mul_mod_prod (F : ℕ → ℕ) {P : ℕ} (hP : 2 ≤ P) (N : ℕ) :
    (List.range N).foldl (fun acc k => acc * F k % P) 1 = (∏ k ∈ range N, F k) % P := by
  induction N with
  | zero => simp [Nat.mod_eq_of_lt (by omega : 1 < P)]
  | succ N ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      prod_range_succ, Nat.mod_mul_mod]

theorem val_prodModT {body : Term → Term} {pT : Term} {N P : ℕ} {F : ℕ → ℕ}
    (hp : Val w pT env P) (hP : 2 ≤ P) (hn : Val w n env N) (hb : FVal w body env F) :
    Val w (prodModT pT n body) env ((∏ k ∈ range N, F k) % P) := by
  have := val_foldT (f := fun acc i => mod (mul acc (body i)) pT) hn (val_const 1 env)
    (fun acc k => acc * F k % P)
    (fun pre u u' a q hu hu' => val_mod (val_mul hu (hb pre u' q hu')) (hp.ext pre))
  rwa [foldl_mul_mod_prod F hP] at this

theorem bd_prodModT {body : Term → Term} {pT : Term} {N P B : ℕ} {F : ℕ → ℕ}
    (hp : Val w pT env P) (hP : 2 ≤ P) (hn : Val w n env N) (hb : FVal w body env F)
    (hbp : Bd w M pT env) (hbn : Bd w M n env) (hN : N ≤ M) (h1 : 1 ≤ M)
    (hF : ∀ k < N, F k ≤ B) (hPB : P * B ≤ M)
    (hbb : ∀ pre u q, q < N → Val w u (pre ++ env) q → Bd w M u (pre ++ env) →
      Bd w M (body u) (pre ++ env)) :
    Bd w M (prodModT pT n body) env := by
  refine bd_foldT (f := fun acc i => mod (mul acc (body i)) pT) hn (val_const 1 env)
    (fun acc k => acc * F k % P)
    (fun pre u u' a q hu hu' => val_mod (val_mul hu (hb pre u' q hu')) (hp.ext pre))
    hbn (bd_const h1 _) hN fun pre u u' a q hq ha hu hu' hbu hbu' => ?_
  refine bd_mod (bd_mul hbu (hbb pre u' q hq hu' hbu') hu (hb pre u' q hu') ?_) (hbp.ext pre)
  rw [ha, foldl_mul_mod_prod F hP]
  calc (∏ k ∈ range q, F k) % P * F q ≤ P * B :=
        Nat.mul_le_mul (Nat.mod_lt _ (by omega)).le (hF q hq)
    _ ≤ M := hPB

/-! ### Small tests -/

/-- `1` if the values are equal, `0` otherwise. -/
def eqT (a b : Term) : Term := lt (add (sub a b) (sub b a)) (const 1)

theorem val_eqT (ha : Val w a env x) (hb : Val w b env y) :
    Val w (eqT a b) env (if x = y then 1 else 0) := by
  have := val_lt (val_add (val_sub ha hb) (val_sub hb ha)) (val_const 1 env)
  refine fun extra => (this extra).trans ?_
  by_cases h : x = y
  · simp [h]
  · simp only [h, if_false]; split_ifs <;> omega

theorem bd_eqT (ha : Bd w M a env) (hb : Bd w M b env) (hva : Val w a env x) (hvb : Val w b env y)
    (hx : x ≤ M) (hy : y ≤ M) (h1 : 1 ≤ M) : Bd w M (eqT a b) env :=
  bd_lt (bd_add (bd_sub ha hb) (bd_sub hb ha) (val_sub hva hvb) (val_sub hvb hva) (by omega))
    (bd_const h1 _)

/-! ### Calling closed programs -/

/-- Run a program closed in one variable on an argument term. -/
def call1 (q : Prog) (a : Term) : Term := fun d => .letIn (a d) q

theorem val_call1 {q : Prog} (hq : Prog'.closed 1 q = true) (ha : Val w a env x) :
    Val w (call1 q a) env (q.eval w [x]) := fun extra => by
  show Prog.eval w (.letIn _ q) _ = _
  simp only [Prog.eval]
  have := Prog'.eval_append (w := w) q [x] (extra ++ env) hq
  rw [← this]
  exact congrArg (fun u => q.eval w (u :: (extra ++ env))) (ha extra)

theorem bd_call1 {q : Prog} (hq : Prog'.closed 1 q = true) (ha : Val w a env x)
    (hba : Bd w M a env) (h : q.Bounded w M [x]) : Bd w M (call1 q a) env := fun extra => by
  show Prog.Bounded w M (.letIn _ q) _
  simp only [Prog.Bounded]
  refine ⟨hba extra, ?_⟩
  have : (a (extra ++ env).length).eval w (extra ++ env) = x := ha extra
  rw [this]
  exact (Prog'.bounded_append M q [x] (extra ++ env) hq).mpr h

/-- Run a program closed in three variables on three argument terms. -/
def call3 (q : Prog) (a b c : Term) : Term :=
  fun d => .letIn (c d) (.letIn (b (d + 1)) (.letIn (a (d + 2)) q))

theorem val_call3 {q : Prog} (hq : Prog'.closed 3 q = true) (ha : Val w a env x)
    (hb : Val w b env y) (hc : Val w c env z) :
    Val w (call3 q a b c) env (q.eval w [x, y, z]) := fun extra => by
  show Prog.eval w (.letIn _ (.letIn _ (.letIn _ q))) _ = _
  simp only [Prog.eval]
  have e1 : (c (extra ++ env).length).eval w (extra ++ env) = z := hc extra
  rw [e1]
  have e2 : (b ((extra ++ env).length + 1)).eval w (z :: (extra ++ env)) = y := hb (z :: extra)
  rw [e2]
  have e3 : (a ((extra ++ env).length + 2)).eval w (y :: z :: (extra ++ env)) = x :=
    ha (y :: z :: extra)
  rw [e3]
  exact Prog'.eval_append q [x, y, z] (extra ++ env) hq

theorem bd_call3 {q : Prog} (hq : Prog'.closed 3 q = true) (ha : Val w a env x)
    (hb : Val w b env y) (hc : Val w c env z) (hba : Bd w M a env) (hbb : Bd w M b env)
    (hbc : Bd w M c env) (h : q.Bounded w M [x, y, z]) : Bd w M (call3 q a b c) env :=
  fun extra => by
  show Prog.Bounded w M (.letIn _ (.letIn _ (.letIn _ q))) _
  simp only [Prog.Bounded]
  have e1 : (c (extra ++ env).length).eval w (extra ++ env) = z := hc extra
  have e2 : (b ((extra ++ env).length + 1)).eval w (z :: (extra ++ env)) = y := hb (z :: extra)
  have e3 : (a ((extra ++ env).length + 2)).eval w (y :: z :: (extra ++ env)) = x :=
    ha (y :: z :: extra)
  refine ⟨hbc extra, ?_⟩
  rw [e1]
  refine ⟨hbb (z :: extra), ?_⟩
  rw [e2]
  refine ⟨hba (y :: z :: extra), ?_⟩
  rw [e3]
  exact (Prog'.bounded_append M q [x, y, z] (extra ++ env) hq).mpr h

/-- Value bounds are monotone in the bound. -/
theorem bounded_mono {B B' : ℕ} (hB : B ≤ B') :
    ∀ (P : Prog) (env : List ℕ), P.Bounded w B env → P.Bounded w B' env
  | .const _, _, h => le_trans h hB
  | .var _, _, _ => trivial
  | .add a b, env, ⟨ha, hb, h⟩ =>
    ⟨bounded_mono hB a env ha, bounded_mono hB b env hb, le_trans h hB⟩
  | .sub a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .mul a b, env, ⟨ha, hb, h⟩ =>
    ⟨bounded_mono hB a env ha, bounded_mono hB b env hb, le_trans h hB⟩
  | .div a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .mod a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .bit a i, env, ⟨ha, hi⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB i env hi⟩
  | .lt a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .input a, env, ha => bounded_mono hB a env ha
  | .ite c t e, env, ⟨hc, h⟩ => by
    refine ⟨bounded_mono hB c env hc, ?_⟩
    split_ifs at h ⊢
    · exact bounded_mono hB t env h
    · exact bounded_mono hB e env h
  | .letIn a body, env, ⟨ha, hbody⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB body _ hbody⟩
  | .fold n init body, env, ⟨hn, hi, hle, hk⟩ =>
    ⟨bounded_mono hB n env hn, bounded_mono hB init env hi, le_trans hle hB,
      fun k hk' => bounded_mono hB body _ (hk k hk')⟩

/-! ### Closing a program -/

/-- The variables outside an environment of length `n` replaced by `0`. -/
def closeAt : ℕ → Prog → Prog
  | _, .const k => .const k
  | n, .var i => if i < n then .var i else .const 0
  | n, .add a b => .add (closeAt n a) (closeAt n b)
  | n, .sub a b => .sub (closeAt n a) (closeAt n b)
  | n, .mul a b => .mul (closeAt n a) (closeAt n b)
  | n, .div a b => .div (closeAt n a) (closeAt n b)
  | n, .mod a b => .mod (closeAt n a) (closeAt n b)
  | n, .bit a b => .bit (closeAt n a) (closeAt n b)
  | n, .lt a b => .lt (closeAt n a) (closeAt n b)
  | n, .input a => .input (closeAt n a)
  | n, .ite c t e => .ite (closeAt n c) (closeAt n t) (closeAt n e)
  | n, .letIn a b => .letIn (closeAt n a) (closeAt (n + 1) b)
  | n, .fold m i b => .fold (closeAt n m) (closeAt n i) (closeAt (n + 2) b)

theorem closed_closeAt : ∀ (n : ℕ) (p : Prog), Prog'.closed n (closeAt n p) = true
  | _, .const _ => rfl
  | n, .var i => by
    unfold closeAt
    split_ifs with h
    · simp [Prog'.closed, h]
    · rfl
  | n, .add a b | n, .sub a b | n, .mul a b | n, .div a b | n, .mod a b | n, .bit a b
  | n, .lt a b => by simp [closeAt, Prog'.closed, closed_closeAt n a, closed_closeAt n b]
  | n, .input a => by simp [closeAt, Prog'.closed, closed_closeAt n a]
  | n, .ite c t e => by
    simp [closeAt, Prog'.closed, closed_closeAt n c, closed_closeAt n t, closed_closeAt n e]
  | n, .letIn a b => by simp [closeAt, Prog'.closed, closed_closeAt n a, closed_closeAt (n + 1) b]
  | n, .fold m i b => by
    simp [closeAt, Prog'.closed, closed_closeAt n m, closed_closeAt n i, closed_closeAt (n + 2) b]

theorem eval_closeAt : ∀ (p : Prog) (n : ℕ) (env : List ℕ), env.length = n →
    (closeAt n p).eval w env = p.eval w env
  | .const _, _, _, _ => rfl
  | .var i, n, env, hn => by
    unfold closeAt
    split_ifs with h
    · rfl
    · simp only [Prog.eval]
      rw [List.getD_eq_default _ _ (by omega)]
  | .add a b, n, env, hn | .sub a b, n, env, hn | .mul a b, n, env, hn | .div a b, n, env, hn
  | .mod a b, n, env, hn | .bit a b, n, env, hn
  | .lt a b, n, env, hn => by
    simp only [closeAt, Prog.eval, eval_closeAt a n env hn, eval_closeAt b n env hn]
  | .input a, n, env, hn => by simp only [closeAt, Prog.eval, eval_closeAt a n env hn]
  | .ite c t e, n, env, hn => by
    simp only [closeAt, Prog.eval, eval_closeAt c n env hn, eval_closeAt t n env hn,
      eval_closeAt e n env hn]
  | .letIn a b, n, env, hn => by
    simp only [closeAt, Prog.eval, eval_closeAt a n env hn]
    exact eval_closeAt b (n + 1) (_ :: env) (by simp [hn])
  | .fold m i b, n, env, hn => by
    simp only [closeAt, Prog.eval, eval_closeAt m n env hn, eval_closeAt i n env hn]
    congr 1
    funext acc k
    exact eval_closeAt b (n + 2) (acc :: k :: env) (by simp [hn])

theorem foldAcc_closeAt (b : Prog) (n : ℕ) (env : List ℕ) (hn : env.length = n) (init k : ℕ) :
    Prog.foldAcc w (closeAt (n + 2) b) env init k = Prog.foldAcc w b env init k := by
  unfold Prog.foldAcc
  congr 1
  funext acc i
  exact eval_closeAt b (n + 2) (acc :: i :: env) (by simp [hn])

theorem bounded_closeAt : ∀ (p : Prog) (n : ℕ) (env : List ℕ), env.length = n →
    ((closeAt n p).Bounded w M env ↔ p.Bounded w M env)
  | .const _, _, _, _ => Iff.rfl
  | .var i, n, env, hn => by
    unfold closeAt
    split_ifs with h
    · exact Iff.rfl
    · simp [Prog.Bounded]
  | .add a b, n, env, hn => by
    have := eval_closeAt (w := w) (.add a b) n env hn
    simp only [closeAt] at this
    simp only [closeAt, Prog.Bounded, bounded_closeAt a n env hn, bounded_closeAt b n env hn, this]
  | .mul a b, n, env, hn => by
    have := eval_closeAt (w := w) (.mul a b) n env hn
    simp only [closeAt] at this
    simp only [closeAt, Prog.Bounded, bounded_closeAt a n env hn, bounded_closeAt b n env hn, this]
  | .sub a b, n, env, hn | .div a b, n, env, hn | .mod a b, n, env, hn | .bit a b, n, env, hn
  | .lt a b, n, env, hn => by
    simp only [closeAt, Prog.Bounded, bounded_closeAt a n env hn, bounded_closeAt b n env hn]
  | .input a, n, env, hn => by simp only [closeAt, Prog.Bounded, bounded_closeAt a n env hn]
  | .ite c t e, n, env, hn => by
    simp only [closeAt, Prog.Bounded, bounded_closeAt c n env hn, bounded_closeAt t n env hn,
      bounded_closeAt e n env hn, eval_closeAt c n env hn]
  | .letIn a b, n, env, hn => by
    simp only [closeAt, Prog.Bounded, bounded_closeAt a n env hn, eval_closeAt a n env hn]
    rw [bounded_closeAt b (n + 1) _ (by simp [hn])]
  | .fold m i b, n, env, hn => by
    simp only [closeAt, Prog.Bounded, bounded_closeAt m n env hn, bounded_closeAt i n env hn,
      eval_closeAt m n env hn, eval_closeAt i n env hn, foldAcc_closeAt b n env hn]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      forall_congr' fun k => imp_congr_right fun _ => ?_
    exact bounded_closeAt b (n + 2) _ (by simp [hn])

end Cslib.Complexity.NtimeDspace.Cross.Exact
