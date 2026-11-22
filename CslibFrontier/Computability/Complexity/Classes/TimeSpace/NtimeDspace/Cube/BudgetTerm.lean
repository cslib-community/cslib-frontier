/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactClocked
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Budget arrays as terms (Lemma 6.4)

Terms (`ProgTerm.Term`) for the numeric functions of `BudgetNum.lean`: the machine of Lemma 6.4
reads budgets, diagonal weights, the validity of a choice code, the orientation and the child
array, and the index widths from the budget array of the current clique.

Every term `fooT` comes with
* a value lemma `val_fooT`: `Cross.Exact.Val w (fooT …) env (fooN …)` (the value in every
  extension of `env`) from the values of the arguments;
* a tier lemma `tm_fooT`: `Tm w L d (fooT …) env` for an explicit `d`.

The fixed inputs (array, `q`, `fw`, `g`, code `i`) are bundled in `Inp` (values) and `Tiers`
(tiers and sizes). Digits are read by repeated halving (`divPowT 2`), so reading a digit needs
no bound on its position: the tiers hold with `fw < L` and `16 ≤ L` (`Tiers`). Only building an
array needs a bound on its width, `g·g·fw ≤ L` (`tm_childT`), and slicing a code of copies needs
the widths of the slices below `L` (`tm_sliceT`).

## Main definitions

* `digT`, `budT`, `qdT`, `isRectT`, `diagT`: digits, budgets (`budgetN`), quadruple digits
  (`qd`, the digits of `quad`), rectangles and diagonal weights (`diagN`).
* `rowBT`, `colBT`, `orientT`, `childT`: candidate budgets, orientation, child array.
* `fieldOkT`, `choiceValidT`: validity of a choice code (`ValidN`, which decides `ValidChoiceCode`
by
  `validN_iff`).
* `bCodeWidthT`, `choiceWidthT`, `argOffT`, `argWidT`, `sliceOffT`, `sliceT`, `copiesWidT`,
  `xiWidT`, `packLT`, `nFacT`: widths.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross.Exact

variable {w : List Bool} {env : List ℕ} {L : ℕ}

/-! ### Helpers -/

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.stable {t : Term} {v : ℕ}
    (h : Val w t env v) : StableAt w t env := fun extra =>
  (h extra).trans h.eq.symm

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.congr {t : Term} {v v' : ℕ}
    (h : Val w t env v) (e : v = v') : Val w t env v' := e ▸ h

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.ext' {t : Term} {v : ℕ}
    (h : Val w t env v) {env' : List ℕ} (he : Ext L env' env) :
    Val w t env' v := by
  obtain ⟨p, _, rfl⟩ := he; exact h.ext p

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.sm {t : Term} {v V : ℕ}
    (h : Val w t env v) (hv : v < V) : Sm w L t V env :=
  fun pre _ => (h pre).trans_lt hv

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.le' {t : Term} {v V : ℕ}
    (h : Val w t env v) (hv : v ≤ V) : Le w L t V env :=
  fun pre _ => (h pre).trans_le hv

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.pos {t : Term} {v : ℕ}
    (h : Val w t env v) (hv : 0 < v) : Pos w L t env :=
  fun pre _ => (h pre).symm ▸ hv

/-- A term keeps a lower tier when its value is known to be small. -/
theorem _root_.Cslib.Complexity.NtimeDspace.ProgTerm.Tm.retier {t : Term} {d d' v : ℕ}
    (h : Tm w L d t env) (hv : Val w t env v)
    (hlt : v < 2 ^ (d' * L)) : Tm w L d' t env := fun pre
        hp => ⟨(h pre hp).1, by rw [hv pre]; exact hlt⟩

theorem val_pow2E {e : Term} {E : ℕ} (he : Val w e env E) : Val w (pow2 e) env (2 ^ E) :=
  fun extra => by rw [denote_pow2, he extra]

theorem val_divPowT {x T i : Term} {X Tv I : ℕ} (hx : Val w x env X) (hT : Val w T env Tv)
    (hi : Val w i env I) : Val w (divPowT x T i) env (Tv / X ^ I) := fun extra => by
  rw [divPowT_denote _ _ _ _ (hx.ext extra).stable, hx extra, hT extra, hi extra]

theorem small_lt (hL : 16 ≤ L) {k : ℕ} (hk : k < 2 ^ 16) : k < 2 ^ L :=
  hk.trans_le (Nat.pow_le_pow_right (by norm_num) hL)

theorem tc (hL : 16 ≤ L) {k : ℕ} (hk : k < 2 ^ 16) : Tm w L 1 (const k) env := t_const
    (small_lt hL hk)

/-- `1` if `a ≤ b`. -/
def leT (a b : Term) : Term := lt a (add b (const 1))

/-- `b` if `a` is positive, else `0` (conjunction of `0/1` tests). -/
def andT (a b : Term) : Term := ite a b (const 0)

/-- `1` if every test `k < n` is `1`, for `0/1`-valued tests. -/
def everyT (n : Term) (test : Term → Term) : Term :=
  lt (sumT n fun k => sub (const 1) (test k)) (const 1)

/-- Indicator values. -/
abbrev ind (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

theorem val_leT {a b : Term} {A B : ℕ} (ha : Val w a env A) (hb : Val w b env B) :
    Val w (leT a b) env (ind (A ≤ B)) :=
  (val_lt ha (val_add hb (val_const 1 env))).congr (by by_cases h : A ≤ B <;> simp [h])

theorem val_ltI {a b : Term} {A B : ℕ} (ha : Val w a env A) (hb : Val w b env B) :
    Val w (lt a b) env (ind (A < B)) := val_lt ha hb

theorem val_eqI {a b : Term} {A B : ℕ} (ha : Val w a env A) (hb : Val w b env B) :
    Val w (Cross.Exact.eqT a b) env (ind (A = B)) := val_eqT ha hb

theorem val_andT {a b : Term} {P Q : Prop} [Decidable P] [Decidable Q] (ha : Val w a env (ind P))
    (hb : Val w b env (ind Q)) : Val w (andT a b) env (ind (P ∧ Q)) :=
  (val_ite ha hb (val_const 0 env)).congr (by by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ])

theorem val_iteI {c t e : Term} {P : Prop} [Decidable P] {T E : ℕ} (hc : Val w c env (ind P))
    (ht : Val w t env T) (he : Val w e env E) : Val w (ite c t e) env (if P then T else E) :=
  (val_ite hc ht he).congr (by by_cases hP : P <;> simp [hP])

theorem val_everyT {n : Term} {test : Term → Term} {N : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hn : Val w n env N) (ht : FVal w test env fun k => ind (P k)) :
    Val w (everyT n test) env (ind (∀ k < N, P k)) := by
  have hs := val_sumT hn (F := fun k => 1 - ind (P k))
    (fun pre u p hu => val_sub (val_const 1 _) (ht pre u p hu))
  refine (val_lt hs (val_const 1 env)).congr ?_
  have key : (∑ k ∈ range N, (1 - ind (P k)) < 1) ↔ ∀ k < N, P k := by
    rw [Nat.lt_one_iff, Finset.sum_eq_zero_iff]
    refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
    · have := h k (mem_range.mpr hk)
      by_contra hp
      simp only [ind, hp, ite_false] at this
      omega
    · simp only [ind, h k (mem_range.mp hk), ite_true, Nat.sub_self]
  by_cases hall : ∀ k < N, P k
  · simp only [ind, key.mpr hall, ite_true]; exact (ite_eq_left hall).symm
  · simp only [ind, mt key.mp hall, ite_false]; exact (ite_eq_right hall).symm

theorem tm_leT {a b : Term} {da db : ℕ} (ha : Tm w L da a env) (hb : Tm w L db b env) (hL : 16 ≤ L)
    (hdb : db + 1 ≤ 128) : Tm w L 1 (leT a b) env :=
  t_lt ha (t_add hb (tc hL (by norm_num)) (by omega) (by omega)) (by omega)

theorem tm_eqI {a b : Term} {da db : ℕ} (ha : Tm w L da a env) (hb : Tm w L db b env)
    (hda : da ≤ 32) (hdb : db ≤ 32) (hL : 16 ≤ L) : Tm w L 1 (Cross.Exact.eqT a b) env :=
  t_lt (t_add (t_sub ha hb) (t_sub hb ha) (by omega) (by omega)) (tc hL (by norm_num)) (by omega)

theorem tm_andT {a b : Term} {da : ℕ} (ha : Tm w L da a env) (hb : Tm w L 1 b env) (hL : 16 ≤ L) :
    Tm w L 1 (andT a b) env := (t_ite ha hb (tc hL (by norm_num))).mono (by simp)

theorem tm_everyT {n : Term} {test : Term → Term} {dn dt : ℕ} (hn : Tm w L dn n env)
    (ht : TmF w L test dn dt env) (hL : 16 ≤ L) (hd : dn + 1 ≤ 32) : Tm w L 1 (everyT n test) env :=
  t_lt (t_sumT hn (db := 1) (fun e he y hy => t_sub (tc hL (by norm_num)) (ht.app he hy)) (by omega)
      hd)
    (tc hL (by norm_num)) (by omega)

/-- `g ^ k` by `k` multiplications. -/
def powC (g : Term) : ℕ → Term
  | 0 => const 1
  | k + 1 => mul (powC g k) g

theorem val_powC {g : Term} {G : ℕ} (hg : Val w g env G) : ∀ k, Val w (powC g k) env (G ^ k)
  | 0 => (val_const 1 env).congr (pow_zero G).symm
  | k + 1 => (val_mul (val_powC hg k) hg).congr (pow_succ G k).symm

theorem tm_powC {g : Term} (hg : Tm w L 1 g env) (hL : 16 ≤ L) :
    ∀ k, k + 1 ≤ 128 → Tm w L (k + 1) (powC g k) env
  | 0, _ => tc hL (by norm_num)
  | k + 1, hk => t_mul (tm_powC hg hL k (by omega)) hg hk

/-! ### The inputs -/

/-- The fixed inputs as terms with known values: the array `ar`, the node count `q`, the field
width `fw`, the side `g` of the grid and the choice code `i`. -/
structure Inp (w : List Bool) (env : List ℕ) (arT qT fwT gT iT : Term)
    (ar q fw g i : ℕ) : Prop where
  vA : Val w arT env ar
  vq : Val w qT env q
  vfw : Val w fwT env fw
  vg : Val w gT env g
  vi : Val w iT env i

/-- The tiers of the inputs and the sizes: the array and the code are any bound values (tier `32`),
`q`, `fw`, `g` have tier `1`, `16 ≤ L`, `fw < L` and `0 < g`. -/
structure Tiers (w : List Bool) (L : ℕ) (env : List ℕ) (arT qT fwT gT iT : Term) (fw g : ℕ) :
    Prop where
  tA : Tm w L 32 arT env
  tq : Tm w L 1 qT env
  tfw : Tm w L 1 fwT env
  tg : Tm w L 1 gT env
  ti : Tm w L 32 iT env
  hL : 16 ≤ L
  hfw : fw < L
  hg : 0 < g

variable {arT qT fwT gT iT : Term} {ar q fw g i : ℕ}

theorem Inp.ext' (h : Inp w env arT qT fwT gT iT ar q fw g i) {env' : List ℕ}
    (he : Ext L env' env) :
    Inp w env' arT qT fwT gT iT ar q fw g i :=
  ⟨h.vA.ext' he, h.vq.ext' he, h.vfw.ext' he, h.vg.ext' he, h.vi.ext' he⟩

theorem Tiers.ext' (t : Tiers w L env arT qT fwT gT iT fw g) {env' : List ℕ} (he : Ext L env' env) :
    Tiers w L env' arT qT fwT gT iT fw g :=
  ⟨t.tA.ext he, t.tq.ext he, t.tfw.ext he, t.tg.ext he, t.ti.ext he, t.hL, t.hfw, t.hg⟩

/-! ### Digits and budgets -/

/-- Digit `t` of width `fw` of `x` (`digitN`), by halving `t·fw` times. -/
def digT (fwT x t : Term) : Term := mod (divPowT (const 2) x (mul t fwT)) (pow2 fwT)

theorem val_digT {x t : Term} {X T : ℕ} (hfw : Val w fwT env fw) (hx : Val w x env X)
    (ht : Val w t env T) : Val w (digT fwT x t) env (digitN fw X T) :=
  val_mod (val_divPowT (val_const 2 env) hx (val_mul ht hfw)) (val_pow2E hfw)

theorem tm_digT {x t : Term} {dx dt : ℕ} (hfwT : Tm w L 1 fwT env) (hfw : Val w fwT env fw)
    (hfwL : fw < L) (hL : 16 ≤ L) (hx : Tm w L dx x env) (hdx : dx ≤ 32) (ht : Tm w L dt t env)
    (hdt : dt + 1 ≤ 32) : Tm w L 1 (digT fwT x t) env :=
  t_mod (t_divPowT (tc hL (by norm_num)) hx (t_mul ht hfwT (by omega)) hdt hdx)
    (t_pow2 hfwT (by norm_num) (fun pre _ => by rw [hfw pre]; omega) (by norm_num)
        (by omega)) Pos.pow2'

/-- The budget of `{u, v}` read from the array (`budgetN`). -/
def budT (arT qT fwT u v : Term) : Term :=
  digT fwT arT (add (mul (ite (lt u v) u v) qT) (ite (lt u v) v u))

theorem val_budT {u v : Term} {U V : ℕ} (har : Val w arT env ar) (hq : Val w qT env q)
    (hfw : Val w fwT env fw) (hu : Val w u env U) (hv : Val w v env V) :
    Val w (budT arT qT fwT u v) env (budgetN ar q fw U V) := by
  refine (val_digT hfw har (val_add (val_mul (val_ite (val_lt hu hv) hu hv) hq)
    (val_ite (val_lt hu hv) hv hu))).congr ?_
  rw [budgetN]
  rcases lt_or_ge U V with h' | h'
  · simp [h', min_eq_left h'.le, max_eq_right h'.le]
  · simp [Nat.not_lt.mpr h', min_eq_right h', max_eq_left h']

theorem tm_budT {u v : Term} {du dv : ℕ} (t : Tiers w L env arT qT fwT gT iT fw g)
    (hfw : Val w fwT env fw) (hu : Tm w L du u env) (hv : Tm w L dv v env)
    (hd : max du dv + 3 ≤ 32) : Tm w L 1 (budT arT qT fwT u v) env := by
  have := t.hL
  exact tm_digT t.tfw hfw t.hfw t.hL t.tA le_rfl
    (t_add (t_mul (t_ite (t_lt hu hv (by omega)) hu hv) t.tq (by omega))
      (t_ite (t_lt hu hv (by omega)) hv hu) (by omega) (by omega)) (by omega)

/-! ### Quadruple indices and diagonal weights -/

/-- Digit `k` in base `g` (`qd`). -/
def qdT (gT x : Term) (k : ℕ) : Term := mod (div x (powC gT k)) gT

theorem val_qdT {x : Term} {X : ℕ} (hg : Val w gT env g) (hx : Val w x env X) (k : ℕ) :
    Val w (qdT gT x k) env (qd g X k) := val_mod (val_div hx (val_powC hg k)) hg

theorem tm_qdT {x : Term} {dx : ℕ} (t : Tiers w L env arT qT fwT gT iT fw g) (hg : Val w gT env g)
    (hx : Tm w L dx x env) (k : ℕ) (hk : k + 1 ≤ 128) : Tm w L 1 (qdT gT x k) env :=
  t_mod (t_div hx (tm_powC t.tg t.hL k hk)) t.tg (hg.pos t.hg)

/-- `1` if the index is a rectangle (`IsRectN`). -/
def isRectT (gT x : Term) : Term :=
  andT (lt (qdT gT x 3) (qdT gT x 2)) (lt (qdT gT x 1) (qdT gT x 0))

theorem val_isRectT {x : Term} {X : ℕ} (hg : Val w gT env g) (hx : Val w x env X) :
    Val w (isRectT gT x) env (ind (IsRectN g X)) :=
  val_andT (val_lt (val_qdT hg hx 3) (val_qdT hg hx 2)) (val_lt (val_qdT hg hx 1) (val_qdT hg hx 0))

theorem tm_isRectT {x : Term} {dx : ℕ} (t : Tiers w L env arT qT fwT gT iT fw g)
    (hg : Val w gT env g)
    (hx : Tm w L dx x env) : Tm w L 1 (isRectT gT x) env := by
  have := t.hL
  exact tm_andT (t_lt (tm_qdT t hg hx 3 (by norm_num)) (tm_qdT t hg hx 2 (by norm_num))
      (by have := t.hL; omega))
    (t_lt (tm_qdT t hg hx 1 (by norm_num)) (tm_qdT t hg hx 0 (by norm_num))
        (by have := t.hL; omega)) t.hL

/-- The node `(A, B)` of the grid: `A·g + B`. -/
def nodeT (gT a b : Term) : Term := add (mul a gT) b

/-- The diagonal weight of the rectangle of index `x` (`diagN`). -/
def diagT (arT qT fwT gT x : Term) : Term :=
  add (budT arT qT fwT (nodeT gT (qdT gT x 3) (qdT gT x 1)) (nodeT gT (qdT gT x 2) (qdT gT x 0)))
    (budT arT qT fwT (nodeT gT (qdT gT x 3) (qdT gT x 0)) (nodeT gT (qdT gT x 2) (qdT gT x 1)))

theorem val_diagT {x : Term} {X : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hx : Val w x env X) : Val w (diagT arT qT fwT gT x) env (diagN ar q fw g X) := by
  have hq := fun k => val_qdT h.vg hx k
  exact val_add (val_budT h.vA h.vq h.vfw (val_add (val_mul (hq 3) h.vg) (hq 1))
      (val_add (val_mul (hq 2) h.vg) (hq 0)))
    (val_budT h.vA h.vq h.vfw (val_add (val_mul (hq 3) h.vg) (hq 0))
      (val_add (val_mul (hq 2) h.vg) (hq 1)))

theorem tm_diagT {x : Term} {dx : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hx : Tm w L dx x env) :
    Tm w L 2 (diagT arT qT fwT gT x) env := by
  have := t.hL
  have hq := fun k (hk : k + 1 ≤ 128) => tm_qdT t h.vg hx k hk
  have hn : ∀ k k', k + 1 ≤ 128 → k' + 1 ≤ 128 → Tm w L 3
      (nodeT gT (qdT gT x k) (qdT gT x k')) env :=
    fun k k' hk
        hk' => t_add (t_mul (hq k hk) t.tg (by norm_num)) (hq k' hk') (by have := t.hL; omega)
      (by norm_num)
  exact t_add (tm_budT t h.vfw (hn 3 1 (by norm_num) (by norm_num))
      (hn 2 0 (by norm_num) (by norm_num))
      (by norm_num))
    (tm_budT t h.vfw (hn 3 0 (by norm_num) (by norm_num)) (hn 2 1 (by norm_num) (by norm_num))
      (by norm_num)) (by have := t.hL; omega) (by norm_num)

theorem Inp.extend (h : Inp w env arT qT fwT gT iT ar q fw g i) (pre : List ℕ) :
    Inp w (pre ++ env) arT qT fwT gT iT ar q fw g i :=
  ⟨h.vA.ext pre, h.vq.ext pre, h.vfw.ext pre, h.vg.ext pre, h.vi.ext pre⟩

/-! ### Candidate budgets, orientation and the child array -/

/-- `L = 1 + g + C(g, 2)` (`packL`). -/
def packLT (gT : Term) : Term := add (add (const 1) gT) (div (mul gT (sub gT (const 1))) (const 2))

theorem val_packLT (hg : Val w gT env g) : Val w (packLT gT) env (packL g) :=
  (val_add (val_add (val_const 1 env) hg) (val_div (val_mul hg (val_sub hg (val_const 1 env)))
    (val_const 2 env))).congr (by rw [packL, Nat.choose_two_right])

theorem tm_packLT (hg : Tm w L 1 gT env) (hL : 16 ≤ L) : Tm w L 3 (packLT gT) env :=
  t_add (t_add (tc hL (by norm_num)) hg (by omega) (by norm_num))
    (t_div (t_mul hg (t_sub hg (tc hL (by norm_num))) (by norm_num)) (tc hL (by norm_num)))
    (by omega) (by norm_num)

/-- `2^(fw-1)`, the offset of a field. -/
def offT (fwT : Term) : Term := pow2 (sub fwT (const 1))

theorem val_offT (hfw : Val w fwT env fw) : Val w (offT fwT) env (2 ^ (fw - 1)) :=
  val_pow2E (val_sub hfw (val_const 1 env))

theorem tm_offT (t : Tiers w L env arT qT fwT gT iT fw g) (hfw : Val w fwT env fw) :
    Tm w L 1 (offT fwT) env := by
  have := t.hL
  exact t_pow2 (t_sub t.tfw (tc t.hL (by norm_num))) (by norm_num)
    (fun pre _ => by rw [(val_sub hfw (val_const 1 env)) pre]; have := t.hfw; omega) (by norm_num)
        (by omega)

/-- The grade digit of the rectangle of index `x`: field `2x`. -/
def gradeT (fwT iT x : Term) : Term := digT fwT iT (mul (const 2) x)

/-- The split digit: field `2x + 1`. -/
def splitT (fwT iT x : Term) : Term := digT fwT iT (add (mul (const 2) x) (const 1))

/-- `rowTermN`. -/
def rowTermT (arT qT fwT gT iT x : Term) : Term :=
  div (sub (add (mul (const 2) (diagT arT qT fwT gT x)) (gradeT fwT iT x)) (offT fwT)) (const 2)

/-- `colTermN`. -/
def colTermT (arT qT fwT gT iT x : Term) : Term :=
  div (sub (add (mul (const 2) (diagT arT qT fwT gT x)) (offT fwT)) (gradeT fwT iT x)) (const 2)

theorem val_rowTermT {x : Term} {X : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hx : Val w x env X) : Val w (rowTermT arT qT fwT gT iT x) env (rowTermN ar q fw g i X) :=
  val_div (val_sub (val_add (val_mul (val_const 2 env) (val_diagT h hx))
    (val_digT h.vfw h.vi (val_mul (val_const 2 env) hx))) (val_offT h.vfw)) (val_const 2 env)

theorem val_colTermT {x : Term} {X : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hx : Val w x env X) : Val w (colTermT arT qT fwT gT iT x) env (colTermN ar q fw g i X) :=
  val_div (val_sub (val_add (val_mul (val_const 2 env) (val_diagT h hx)) (val_offT h.vfw))
    (val_digT h.vfw h.vi (val_mul (val_const 2 env) hx))) (val_const 2 env)

theorem tm_gradeT {x : Term} {dx : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hx : Tm w L dx x env) (hdx : dx ≤ 29) :
    Tm w L 1 (gradeT fwT iT x) env := by
  have := t.hL
  exact tm_digT t.tfw h.vfw t.hfw t.hL t.ti le_rfl (t_mul (tc t.hL (by norm_num)) hx (by omega))
    (by omega)

theorem tm_splitT {x : Term} {dx : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hx : Tm w L dx x env) (hdx : dx ≤ 28) :
    Tm w L 1 (splitT fwT iT x) env := by
  have := t.hL
  exact tm_digT t.tfw h.vfw t.hfw t.hL t.ti le_rfl
    (t_add (t_mul (tc t.hL (by norm_num)) hx (by omega)) (tc t.hL (by norm_num)) (by omega)
      (by omega)) (by omega)

theorem tm_rowTermT {x : Term} {dx : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hx : Tm w L dx x env) (hdx : dx ≤ 29) :
    Tm w L 4 (rowTermT arT qT fwT gT iT x) env := by
  have := t.hL
  exact t_div (t_sub (t_add (t_mul (tc t.hL (by norm_num)) (tm_diagT h t hx) (by norm_num))
    (tm_gradeT h t hx hdx) (by omega) (by norm_num)) (tm_offT t h.vfw)) (tc t.hL (by norm_num))

theorem tm_colTermT {x : Term} {dx : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hx : Tm w L dx x env) (hdx : dx ≤ 29) :
    Tm w L 4 (colTermT arT qT fwT gT iT x) env := by
  have := t.hL
  exact t_div (t_sub (t_add (t_mul (tc t.hL (by norm_num)) (tm_diagT h t hx) (by norm_num))
    (tm_offT t h.vfw) (by omega) (by norm_num)) (tm_gradeT h t hx hdx)) (tc t.hL (by norm_num))

/-- **The row budget** of the pair `u < v` (`rowBN`). -/
def rowBT (arT qT fwT gT iT u v : Term) : Term :=
  mul (packLT gT) (add (sumT gT fun B => budT arT qT fwT (add (mul u gT) B) (add (mul v gT) B))
    (sumT (powC gT 4) fun x => ite (isRectT gT x)
      (ite (andT (Cross.Exact.eqT (qdT gT x 3) u) (Cross.Exact.eqT (qdT gT x 2) v))
        (rowTermT arT qT fwT gT iT x) (const 0)) (const 0)))

/-- **The column budget** of the pair `u < v` (`colBN`). -/
def colBT (arT qT fwT gT iT u v : Term) : Term :=
  mul (packLT gT) (add (sumT gT fun A => budT arT qT fwT (add (mul A gT) u) (add (mul A gT) v))
    (sumT (powC gT 4) fun x => ite (isRectT gT x)
      (ite (andT (Cross.Exact.eqT (qdT gT x 1) u) (Cross.Exact.eqT (qdT gT x 0) v))
        (colTermT arT qT fwT gT iT x) (const 0)) (const 0)))

theorem val_rowBT {u v : Term} {U V : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hu : Val w u env U) (hv : Val w v env V) :
    Val w (rowBT arT qT fwT gT iT u v) env (rowBN ar q fw g i U V) :=
  val_mul (val_packLT h.vg) (val_add
    (val_sumT h.vg fun pre _B _b
        hb => val_budT (h.extend pre).vA (h.extend pre).vq (h.extend pre).vfw
      (val_add (val_mul (hu.ext pre) (h.extend pre).vg) hb)
      (val_add (val_mul (hv.ext pre) (h.extend pre).vg) hb))
    (val_sumT (val_powC h.vg 4) fun pre _x _X hx => val_iteI (val_isRectT (h.extend pre).vg hx)
      (val_iteI (val_andT (val_eqI (val_qdT (h.extend pre).vg hx 3) (hu.ext pre))
        (val_eqI (val_qdT (h.extend pre).vg hx 2) (hv.ext pre)))
        (val_rowTermT (h.extend pre) hx) (val_const 0 _)) (val_const 0 _)))

theorem val_colBT {u v : Term} {U V : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hu : Val w u env U) (hv : Val w v env V) :
    Val w (colBT arT qT fwT gT iT u v) env (colBN ar q fw g i U V) :=
  val_mul (val_packLT h.vg) (val_add
    (val_sumT h.vg fun pre _A _b
        hb => val_budT (h.extend pre).vA (h.extend pre).vq (h.extend pre).vfw
      (val_add (val_mul hb (h.extend pre).vg) (hu.ext pre))
      (val_add (val_mul hb (h.extend pre).vg) (hv.ext pre)))
    (val_sumT (val_powC h.vg 4) fun pre _x _X hx => val_iteI (val_isRectT (h.extend pre).vg hx)
      (val_iteI (val_andT (val_eqI (val_qdT (h.extend pre).vg hx 1) (hu.ext pre))
        (val_eqI (val_qdT (h.extend pre).vg hx 0) (hv.ext pre)))
        (val_colTermT (h.extend pre) hx) (val_const 0 _)) (val_const 0 _)))

theorem tm_rowBT {u v : Term} {du dv : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hu : Tm w L du u env) (hv : Tm w L dv v env)
    (hdu : du ≤ 4) (hdv : dv ≤ 4) : Tm w L 13 (rowBT arT qT fwT gT iT u v) env := by
  have := t.hL
  have h1 : Tm w L 2 (sumT gT fun B => budT arT qT fwT (add (mul u gT) B) (add (mul v gT) B)) env :=
    t_sumT t.tg (db := 1) (fun e he B hB => tm_budT (t.ext' he) (h.ext' he).vfw
      (t_add (t_mul (hu.ext he) (t.ext' he).tg (by omega)) hB (by omega) (by omega))
      (t_add (t_mul (hv.ext he) (t.ext' he).tg (by omega)) hB (by omega) (by omega)) (by omega))
      (by omega) (by norm_num)
  have h2 : Tm w L 9 (sumT (powC gT 4) fun x => ite (isRectT gT x)
      (ite (andT (Cross.Exact.eqT (qdT gT x 3) u) (Cross.Exact.eqT (qdT gT x 2) v))
        (rowTermT arT qT fwT gT iT x) (const 0)) (const 0)) env :=
    t_sumT (tm_powC t.tg t.hL 4 (by norm_num)) (db := 4) (fun e he x hx =>
      (t_ite (tm_isRectT (t.ext' he) (h.ext' he).vg hx)
        ((t_ite (tm_andT (tm_eqI (tm_qdT (t.ext' he) (h.ext' he).vg hx 3 (by norm_num)) (hu.ext he)
            (by norm_num) (by omega) t.hL)
          (tm_eqI (tm_qdT (t.ext' he) (h.ext' he).vg hx 2 (by norm_num)) (hv.ext he)
            (by norm_num) (by omega) t.hL) t.hL)
          (tm_rowTermT (h.ext' he) (t.ext' he) hx (by norm_num)) (tc t.hL (by norm_num))).mono
            (d' := 4) (by norm_num)) (tc t.hL (by norm_num))).mono (d' := 4) (by norm_num))
                (by omega) (by norm_num)
  exact t_mul (tm_packLT t.tg t.hL) (t_add h1 h2 (by omega) (by norm_num)) (by norm_num)

theorem tm_colBT {u v : Term} {du dv : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hu : Tm w L du u env) (hv : Tm w L dv v env)
    (hdu : du ≤ 4) (hdv : dv ≤ 4) : Tm w L 13 (colBT arT qT fwT gT iT u v) env := by
  have := t.hL
  have h1 : Tm w L 2 (sumT gT fun A => budT arT qT fwT (add (mul A gT) u) (add (mul A gT) v)) env :=
    t_sumT t.tg (db := 1) (fun e he A hA => tm_budT (t.ext' he) (h.ext' he).vfw
      (t_add (t_mul hA (t.ext' he).tg (by omega)) (hu.ext he) (by omega) (by omega))
      (t_add (t_mul hA (t.ext' he).tg (by omega)) (hv.ext he) (by omega) (by omega)) (by omega))
      (by omega) (by norm_num)
  have h2 : Tm w L 9 (sumT (powC gT 4) fun x => ite (isRectT gT x)
      (ite (andT (Cross.Exact.eqT (qdT gT x 1) u) (Cross.Exact.eqT (qdT gT x 0) v))
        (colTermT arT qT fwT gT iT x) (const 0)) (const 0)) env :=
    t_sumT (tm_powC t.tg t.hL 4 (by norm_num)) (db := 4) (fun e he x hx =>
      (t_ite (tm_isRectT (t.ext' he) (h.ext' he).vg hx)
        ((t_ite (tm_andT (tm_eqI (tm_qdT (t.ext' he) (h.ext' he).vg hx 1 (by norm_num)) (hu.ext he)
            (by norm_num) (by omega) t.hL)
          (tm_eqI (tm_qdT (t.ext' he) (h.ext' he).vg hx 0 (by norm_num)) (hv.ext he)
            (by norm_num) (by omega) t.hL) t.hL)
          (tm_colTermT (h.ext' he) (t.ext' he) hx (by norm_num)) (tc t.hL (by norm_num))).mono
            (d' := 4) (by norm_num)) (tc t.hL (by norm_num))).mono (d' := 4) (by norm_num))
                (by omega) (by norm_num)
  exact t_mul (tm_packLT t.tg t.hL) (t_add h1 h2 (by omega) (by norm_num)) (by norm_num)

/-- The sum of `F u v` over the pairs `u < v < g` (`pairSumN`). -/
def pairSumT (gT : Term) (F : Term → Term → Term) : Term :=
  sumT gT fun u => sumT gT fun v => ite (lt u v) (F u v) (const 0)

theorem val_pairSumT {F : Term → Term → Term} {F' : ℕ → ℕ → ℕ} (hg : Val w gT env g)
    (hF : ∀ pre u v U V, Val w u (pre ++ env) U → Val w v (pre ++ env) V →
      Val w (F u v) (pre ++ env) (F' U V)) : Val w (pairSumT gT F) env (pairSumN g F') :=
  val_sumT hg fun pre u U hu => val_sumT (hg.ext pre) fun pre' v V hv => by
    have hu' : Val w u ((pre' ++ pre) ++ env) U := by
      rw [List.append_assoc]; exact hu.ext pre'
    have hv' : Val w v ((pre' ++ pre) ++ env) V := by rw [List.append_assoc]; exact hv
    have := hF (pre' ++ pre) u v U V hu' hv'
    rw [List.append_assoc] at this
    exact val_iteI (val_ltI (hu.ext pre') hv) this (val_const 0 _)

theorem tm_pairSumT {F : Term → Term → Term} {dF : ℕ} (hg : Tm w L 1 gT env)
    (hF : TmF2 w L F 1 1 dF env) (h1 : 1 ≤ dF) (hd : dF + 2 ≤ 32) (hL : 16 ≤ L) :
    Tm w L (1 + (1 + dF)) (pairSumT gT F) env :=
  t_sumT hg (fun e he u hu => t_sumT (hg.ext he) (fun e' he' v hv =>
    (t_ite (t_lt (hu.ext he') hv (by omega)) (hF.app (he'.trans he) (hu.ext he') hv)
      (tc hL (by norm_num))).mono (d' := dF) (by omega)) (by omega) (by omega)) (by omega)
          (by omega)

/-- **The orientation** (`orientN`): `1` for rows. -/
def orientT (arT qT fwT gT iT : Term) : Term :=
  leT (pairSumT gT (rowBT arT qT fwT gT iT)) (pairSumT gT (colBT arT qT fwT gT iT))

theorem val_orientT (h : Inp w env arT qT fwT gT iT ar q fw g i) :
    Val w (orientT arT qT fwT gT iT) env (ind (orientN ar q fw g i = true)) :=
  (val_leT (val_pairSumT h.vg fun pre _ _ _ _ hu hv => val_rowBT (h.extend pre) hu hv)
    (val_pairSumT h.vg fun pre _ _ _ _ hu hv => val_colBT (h.extend pre) hu hv)).congr
    (by simp only [orientN, decide_eq_true_eq])

theorem tm_orientT (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) : Tm w L 1 (orientT arT qT fwT gT iT) env :=
  tm_leT (tm_pairSumT t.tg (fun e he u v hu hv => tm_rowBT (h.ext' he) (t.ext' he) hu hv
      (by norm_num) (by norm_num)) (by norm_num) (by norm_num) t.hL)
    (tm_pairSumT t.tg (fun e he u v hu hv => tm_colBT (h.ext' he) (t.ext' he) hu hv
      (by norm_num) (by norm_num)) (by norm_num) (by norm_num) t.hL) t.hL (by norm_num)

/-- **The child array** (`childN`): the cheaper candidate budgets, packed. -/
def childT (arT qT fwT gT iT : Term) : Term :=
  sumT (mul gT gT) fun x => ite (lt (div x gT) (mod x gT))
    (mul (ite (orientT arT qT fwT gT iT) (rowBT arT qT fwT gT iT (div x gT) (mod x gT))
      (colBT arT qT fwT gT iT (div x gT) (mod x gT))) (pow2 (mul x fwT))) (const 0)

theorem val_childT (h : Inp w env arT qT fwT gT iT ar q fw g i) :
    Val w (childT arT qT fwT gT iT) env (childN ar q fw g i) := by
  refine (val_sumT (val_mul h.vg h.vg) (F := fun x => if x / g < x % g then
      (if orientN ar q fw g i = true then rowBN ar q fw g i (x / g) (x % g)
        else colBN ar q fw g i (x / g) (x % g)) * 2 ^ (x * fw) else 0)
    fun pre _x X
        hx => val_iteI (val_ltI (val_div hx (h.extend pre).vg) (val_mod hx (h.extend pre).vg))
      (val_mul (val_iteI (val_orientT (h.extend pre))
        (val_rowBT (h.extend pre) (val_div hx (h.extend pre).vg) (val_mod hx (h.extend pre).vg))
        (val_colBT (h.extend pre) (val_div hx (h.extend pre).vg) (val_mod hx (h.extend pre).vg)))
        (val_pow2E (val_mul hx (h.extend pre).vfw))) (val_const 0 _)).congr ?_
  rw [childN, arrN, packN]
  refine sum_congr rfl fun x _ => ?_
  by_cases hc : x / g < x % g
  · rw [ite_eq_left hc, ite_eq_left hc, ← pow_mul, Nat.mul_comm fw x, Nat.mul_comm]
  · rw [ite_eq_right hc, ite_eq_right hc, Nat.mul_zero]

theorem tm_childT (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hsz : g * g * fw ≤ L) :
    Tm w L 16 (childT arT qT fwT gT iT) env := by
  have := t.hL
  refine t_sumTv' (t_mul t.tg t.tg (by norm_num)) ((val_mul h.vg h.vg).le' le_rfl) (db := 14)
    (fun e he x hx _ hxV => ?_) (by omega) (by norm_num)
  have h' := h.ext' he
  have t' := t.ext' he
  have hu : Tm w L 2 (div x gT) e := t_div hx t'.tg
  have hv : Tm w L 2 (mod x gT) e := t_mod_left hx t'.tg
  have hp : Tm w L 1 (pow2 (mul x fwT)) e := t_pow2 (t_mul hx t'.tfw (by norm_num)) (by norm_num)
    (fun pre hp => by
      rw [denote_mul, h'.vfw pre]
      have hxl := hxV pre hp
      have h1 : (x.denote w (pre ++ e) + 1) * fw ≤ g * g * fw := Nat.mul_le_mul_right _ hxl
      rw [Nat.add_mul, Nat.one_mul] at h1
      rcases Nat.eq_zero_or_pos fw with h0 | h0
      · subst h0; simp only [Nat.mul_zero]; omega
      · omega) (by norm_num) (by omega)
  exact (t_ite (t_lt hu hv (by omega))
    (t_mul ((t_ite (tm_orientT h' t') (tm_rowBT h' t' hu hv (by norm_num) (by norm_num))
      (tm_colBT h' t' hu hv (by norm_num) (by norm_num))).mono (d' := 13) (by norm_num)) hp
      (by norm_num)) (tc t.hL (by norm_num))).mono (d' := 14) (by norm_num)

/-- The child array has tier `1` when its budgets fit in the field width. -/
theorem tm_childT_fit (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hsz : g * g * fw ≤ L)
    (hfit : ArrFits g fw fun u v => if orientN ar q fw g i then rowBN ar q fw g i u v
      else colBN ar q fw g i u v) : Tm w L 1 (childT arT qT fwT gT iT) env :=
  (tm_childT h t hsz).retier (val_childT h) ((arrN_lt hfit).trans_le
    (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-! ### Validity of a choice code -/

/-- `RectOkN`: even grade, `|k| ≤ 2 H_R`, `|c| ≤ 3 H_R`. -/
def rectOkT (arT qT fwT gT iT x : Term) : Term :=
  andT (andT (Cross.Exact.eqT (mod (add (gradeT fwT iT x) (offT fwT)) (const 2)) (const 0))
      (andT (leT (gradeT fwT iT x) (add (offT fwT) (mul (const 2) (diagT arT qT fwT gT x))))
        (leT (offT fwT) (add (gradeT fwT iT x) (mul (const 2) (diagT arT qT fwT gT x))))))
    (andT (leT (splitT fwT iT x) (add (offT fwT) (mul (const 3) (diagT arT qT fwT gT x))))
      (leT (offT fwT) (add (splitT fwT iT x) (mul (const 3) (diagT arT qT fwT gT x)))))

/-- `PadOkN`: both fields hold the offset. -/
def padOkT (fwT iT x : Term) : Term :=
  andT (Cross.Exact.eqT (gradeT fwT iT x) (offT fwT)) (Cross.Exact.eqT (splitT fwT iT x) (offT fwT))

/-- `FieldOkN`. -/
def fieldOkT (arT qT fwT gT iT x : Term) : Term :=
  ite (isRectT gT x) (rectOkT arT qT fwT gT iT x) (padOkT fwT iT x)

/-- `choiceWidth g fw = 2 g^4 fw`. -/
def choiceWidthT (gT fwT : Term) : Term := mul (mul (const 2) (powC gT 4)) fwT

/-- **Validity of the choice code** (`ValidN`). -/
def choiceValidT (arT qT fwT gT iT : Term) : Term :=
  andT (Cross.Exact.eqT (divPowT (const 2) iT (choiceWidthT gT fwT)) (const 0))
    (everyT (powC gT 4) (fieldOkT arT qT fwT gT iT))

theorem val_choiceWidthT (hg : Val w gT env g) (hfw : Val w fwT env fw) :
    Val w (choiceWidthT gT fwT) env (choiceWidth g fw) :=
  val_mul (val_mul (val_const 2 env) (val_powC hg 4)) hfw

theorem tm_choiceWidthT (hg : Tm w L 1 gT env) (hfw : Tm w L 1 fwT env) (hL : 16 ≤ L) :
    Tm w L 7 (choiceWidthT gT fwT) env :=
  t_mul (t_mul (tc hL (by norm_num)) (tm_powC hg hL 4 (by norm_num)) (by norm_num)) hfw
      (by norm_num)

theorem val_fieldOkT {x : Term} {X : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hx : Val w x env X) : Val w (fieldOkT arT qT fwT gT iT x) env
        (ind (FieldOkN ar q fw g i X)) := by
  have hD := val_digT h.vfw h.vi (val_mul (val_const 2 env) hx)
  have hC := val_digT h.vfw h.vi (val_add (val_mul (val_const 2 env) hx) (val_const 1 env))
  have hQ := val_offT h.vfw
  have hH := val_diagT h hx
  have hr : Val w (rectOkT arT qT fwT gT iT x) env (ind (RectOkN ar q fw g i X)) :=
    val_andT (val_andT (val_eqI (val_mod (val_add hD hQ) (val_const 2 env)) (val_const 0 env))
        (val_andT (val_leT hD (val_add hQ (val_mul (val_const 2 env) hH)))
          (val_leT hQ (val_add hD (val_mul (val_const 2 env) hH)))))
      (val_andT (val_leT hC (val_add hQ (val_mul (val_const 3 env) hH)))
        (val_leT hQ (val_add hC (val_mul (val_const 3 env) hH))))
  have hp : Val w (padOkT fwT iT x) env (ind (PadOkN fw i X)) :=
    val_andT (val_eqI hD hQ) (val_eqI hC hQ)
  refine (val_iteI (val_isRectT h.vg hx) hr hp).congr ?_
  by_cases hc : IsRectN g X
  · simp only [FieldOkN, hc, ite_true]
  · simp only [FieldOkN, hc, ite_false]

theorem tm_fieldOkT {x : Term} {dx : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hx : Tm w L dx x env) (hdx : dx ≤ 28) :
    Tm w L 1 (fieldOkT arT qT fwT gT iT x) env := by
  have := t.hL
  have hD := tm_gradeT h t hx (by omega)
  have hC := tm_splitT h t hx hdx
  have hQ := tm_offT t h.vfw
  have hH := tm_diagT h t hx
  have h2H : Tm w L 3 (mul (const 2) (diagT arT qT fwT gT x)) env :=
    t_mul (tc t.hL (by norm_num)) hH (by norm_num)
  have h3H : Tm w L 3 (mul (const 3) (diagT arT qT fwT gT x)) env :=
    t_mul (tc t.hL (by norm_num)) hH (by norm_num)
  exact (t_ite (tm_isRectT t h.vg hx)
    (tm_andT (tm_andT (tm_eqI (t_mod_left (t_add hD hQ (by omega) (by norm_num))
        (tc t.hL (by norm_num)))
          (tc t.hL (by norm_num)) (by norm_num) (by norm_num) t.hL)
        (tm_andT (tm_leT hD (t_add hQ h2H (by omega) (by norm_num)) t.hL (by norm_num))
          (tm_leT hQ (t_add hD h2H (by omega) (by norm_num)) t.hL (by norm_num)) t.hL) t.hL)
      (tm_andT (tm_leT hC (t_add hQ h3H (by omega) (by norm_num)) t.hL (by norm_num))
        (tm_leT hQ (t_add hC h3H (by omega) (by norm_num)) t.hL (by norm_num)) t.hL) t.hL)
    (tm_andT (tm_eqI hD hQ (by norm_num) (by norm_num) t.hL)
      (tm_eqI hC hQ (by norm_num) (by norm_num) t.hL) t.hL)).mono (d' := 1) (by norm_num)

theorem val_choiceValidT (h : Inp w env arT qT fwT gT iT ar q fw g i) :
    Val w (choiceValidT arT qT fwT gT iT) env (ind (ValidN ar q fw g i)) := by
  refine (val_andT (val_eqI (val_divPowT (val_const 2 env) h.vi (val_choiceWidthT h.vg h.vfw))
    (val_const 0 env)) (val_everyT (val_powC h.vg 4) (P := FieldOkN ar q fw g i)
      fun pre _x _X hx => val_fieldOkT (h.extend pre) hx)).congr ?_
  simp only [ind, ValidN, Nat.div_eq_zero_iff_lt (show 0 < 2 ^ choiceWidth g fw by positivity)]

theorem tm_choiceValidT (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) : Tm w L 1 (choiceValidT arT qT fwT gT iT) env := by
  have := t.hL
  exact tm_andT (tm_eqI (t_divPowT (tc t.hL (by norm_num)) t.ti (tm_choiceWidthT t.tg t.tfw t.hL)
      (by norm_num) le_rfl) (tc t.hL (by norm_num)) le_rfl (by norm_num) t.hL)
    (tm_everyT (tm_powC t.tg t.hL 4 (by norm_num))
      (fun e he x hx => tm_fieldOkT (h.ext' he) (t.ext' he) hx (by norm_num)) t.hL
          (by norm_num)) t.hL

open Classical in
/-- **The validity term decides `ValidChoiceCode`** for the array of a clique on `g × g` nodes
whose budgets fit in the field width. -/
theorem val_choiceValidT_iff {a : Fin (g * g) → Fin (g * g) → ℕ}
    (h : Inp w env arT qT fwT gT iT (arrN (g * g) fw (extN a)) (g * g) fw g i) (hfit : Fits fw a)
    (hfw : 1 ≤ fw) : Val w (choiceValidT arT qT fwT gT iT) env (ind (ValidChoiceCode a fw i)) :=
  (val_choiceValidT h).congr (by simp only [ind, validN_iff hfit hfw])

/-! ### Widths -/

/-- **The code width** `w(a)` (`codeWidth`), with `⌊√·⌋` by counting (`sqrtT'`). -/
def bCodeWidthT (aT : Term) : Term :=
  ite (lt (const 0) aT) (add (sqrtT' (mul (const 784) aT)) (const 2)) (const 0)

theorem val_bCodeWidthT {aT : Term} {A : ℕ} (ha : Val w aT env A) :
    Val w (bCodeWidthT aT) env (codeWidth A) := by
  refine (val_ite (val_lt (val_const 0 env) ha)
    (val_add (val_sqrtT' (val_mul (val_const 784 env) ha)) (val_const 2 env))
        (val_const 0 env)).congr ?_
  rcases Nat.eq_zero_or_pos A with h0 | h0
  · simp [h0, codeWidth]
  · simp [h0, codeWidth, Nat.pos_iff_ne_zero.mp h0]

theorem tm_bCodeWidthT {aT : Term} (ha : Tm w L 1 aT env) (hL : 16 ≤ L) :
    Tm w L 4 (bCodeWidthT aT) env := by
  have hx : Tm w L 2 (mul (const 784) aT) env := t_mul (tc hL (by norm_num)) ha (by norm_num)
  have hs : Tm w L 3 (sqrtT' (mul (const 784) aT)) env :=
    t_sumT hx (db := 1) (fun e he r hr => t_lt (t_mul (t_add hr (tc hL (by norm_num)) (by omega)
      (by norm_num)) (t_add hr (tc hL (by norm_num)) (by omega) (by norm_num)) (by norm_num))
      (t_add (hx.ext he) (tc hL (by norm_num)) (by omega) (by norm_num)) (by omega)) (by omega)
      (by norm_num)
  exact (t_ite (t_lt (tc hL (by norm_num)) ha (by omega)) (t_add hs (tc hL (by norm_num)) (by omega)
    (by norm_num)) (tc hL (by norm_num))).mono (d' := 4) (by norm_num)

/-- The offset of the label to `u` in an argument code of node `v` (`argOffN`). -/
def argOffT (arT qT fwT v u : Term) : Term :=
  sumT u fun u' => ite (andT (lt u' qT) (lt v qT))
    (ite (Cross.Exact.eqT u' v) (const 0) (bCodeWidthT (budT arT qT fwT v u'))) (const 0)

theorem val_argOffT {v u : Term} {V U : ℕ} (har : Val w arT env ar) (hq : Val w qT env q)
    (hfw : Val w fwT env fw) (hv : Val w v env V) (hu : Val w u env U) :
    Val w (argOffT arT qT fwT v u) env (argOffN ar q fw V U) :=
  val_sumT hu fun pre _u' _U hu' => val_iteI (val_andT (val_ltI hu' (hq.ext pre))
    (val_ltI (hv.ext pre) (hq.ext pre))) (val_iteI (val_eqI hu' (hv.ext pre)) (val_const 0 _)
      (val_bCodeWidthT (val_budT (har.ext pre) (hq.ext pre) (hfw.ext pre) (hv.ext pre) hu')))
    (val_const 0 _)

theorem tm_argOffT {v u : Term} {dv du : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hv : Tm w L dv v env) (hu : Tm w L du u env)
    (hdv : dv ≤ 28) (hdu : du ≤ 28) : Tm w L (du + 4) (argOffT arT qT fwT v u) env := by
  have := t.hL
  exact t_sumT hu (fun e he u' hu' => (t_ite (tm_andT (t_lt hu' (t.ext' he).tq (by omega))
    (t_lt (hv.ext he) (t.ext' he).tq (by omega)) t.hL)
    ((t_ite (tm_eqI hu' (hv.ext he) (by omega) (by omega) t.hL) (tc t.hL (by norm_num))
      (tm_bCodeWidthT (tm_budT (t.ext' he) (h.ext' he).vfw (hv.ext he) hu' (by omega)) t.hL)).mono
        (d' := 4) (by norm_num)) (tc t.hL (by norm_num))).mono (d' := 4) (by norm_num))
    (by omega) (by omega)

/-- The width of an argument code of node `v` (`argWidN`). -/
def argWidT (arT qT fwT v : Term) : Term := argOffT arT qT fwT v qT

theorem val_argWidT {v : Term} {V : ℕ} (har : Val w arT env ar) (hq : Val w qT env q)
    (hfw : Val w fwT env fw) (hv : Val w v env V) :
    Val w (argWidT arT qT fwT v) env (argWidN ar q fw V) := val_argOffT har hq hfw hv hq

theorem tm_argWidT {v : Term} {dv : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hv : Tm w L dv v env) (hdv : dv ≤ 28) :
    Tm w L 5 (argWidT arT qT fwT v) env := tm_argOffT h t hv t.tq hdv (by norm_num)

/-- The offset of the slice of position `p` (`sliceOffN`), for holders `nodes`. -/
def sliceOffT (arT qT fwT : Term) (nodes : Term → Term) (p : Term) : Term :=
  sumT p fun p' => argWidT arT qT fwT (nodes p')

theorem val_sliceOffT {nodes : Term → Term} {Nd : ℕ → ℕ} {p : Term} {P : ℕ}
    (har : Val w arT env ar) (hq : Val w qT env q) (hfw : Val w fwT env fw)
    (hn : FVal w nodes env Nd) (hp : Val w p env P) :
    Val w (sliceOffT arT qT fwT nodes p) env (sliceOffN ar q fw Nd P) :=
  val_sumT hp fun pre u U hu => val_argWidT (har.ext pre) (hq.ext pre) (hfw.ext pre) (hn pre u U hu)

theorem tm_sliceOffT {nodes : Term → Term} {p : Term} {dp dn : ℕ}
    (h : Inp w env arT qT fwT gT iT ar q fw g i) (t : Tiers w L env arT qT fwT gT iT fw g)
    (hn : TmF w L nodes dp dn env) (hdn : dn ≤ 28) (hp : Tm w L dp p env) (hdp : dp + 5 ≤ 32) :
    Tm w L (dp + 5) (sliceOffT arT qT fwT nodes p) env := by
  have := t.hL
  exact t_sumT hp (fun e he p' hp' => tm_argWidT (h.ext' he) (t.ext' he) (hn.app he hp') hdn)
    (by omega) hdp

/-- The width of a code of copies held by `n` nodes (`copiesWidN`). -/
def copiesWidT (arT qT fwT : Term) (nodes : Term → Term) (n : Term) : Term :=
  sliceOffT arT qT fwT nodes n

theorem val_copiesWidT {nodes : Term → Term} {Nd : ℕ → ℕ} {n : Term} {N : ℕ}
    (har : Val w arT env ar) (hq : Val w qT env q) (hfw : Val w fwT env fw)
    (hn : FVal w nodes env Nd) (hN : Val w n env N) :
    Val w (copiesWidT arT qT fwT nodes n) env (copiesWidN ar q fw Nd N) :=
  val_sliceOffT har hq hfw hn hN

/-- The slice of position `p` of a code of copies `ξ` (`sliceN`). -/
def sliceT (arT qT fwT : Term) (nodes : Term → Term) (ξ p : Term) : Term :=
  mod (divPowT (const 2) ξ (sliceOffT arT qT fwT nodes p)) (pow2 (argWidT arT qT fwT (nodes p)))

theorem val_sliceT {nodes : Term → Term} {Nd : ℕ → ℕ} {ξ p : Term} {Ξ P : ℕ}
    (har : Val w arT env ar) (hq : Val w qT env q) (hfw : Val w fwT env fw)
    (hn : FVal w nodes env Nd) (hξ : Val w ξ env Ξ) (hp : Val w p env P) :
    Val w (sliceT arT qT fwT nodes ξ p) env (sliceN ar q fw Nd Ξ P) := by
  have hn0 := hn [] p P hp
  exact val_mod (val_divPowT (val_const 2 env) hξ (val_sliceOffT har hq hfw hn hp))
    (val_pow2E (val_argWidT har hq hfw hn0))

/-- A slice has tier `1` when its width is below `L`. -/
theorem tm_sliceT {nodes : Term → Term} {Nd : ℕ → ℕ} {ξ p : Term} {P dp dn dξ : ℕ}
    (h : Inp w env arT qT fwT gT iT ar q fw g i) (t : Tiers w L env arT qT fwT gT iT fw g)
    (hnv : FVal w nodes env Nd) (hn : TmF w L nodes dp dn env) (hdn : dn ≤ 28)
    (hξ : Tm w L dξ ξ env) (hdξ : dξ ≤ 32) (hp : Tm w L dp p env) (hpv : Val w p env P)
    (hdp : dp + 5 ≤ 32) (hW : argWidN ar q fw (Nd P) < L) :
    Tm w L 1 (sliceT arT qT fwT nodes ξ p) env := by
  have := t.hL
  have hwv := val_argWidT h.vA h.vq h.vfw (hnv [] p P hpv)
  exact t_mod (t_divPowT (tc t.hL (by norm_num)) hξ (tm_sliceOffT h t hn hdn hp hdp) hdp hdξ)
    (t_pow2 (tm_argWidT h t (hn.app (Ext.refl env) hp) hdn) (by norm_num)
      (fun pre _ => by rw [hwv pre]; omega) (by norm_num) (by omega)) Pos.pow2'

/-- The holders of the copies of node `v` of the child: row `v` (`v·g + p`) or column `v`
(`p·g + v`) of the parent grid, by the orientation (`Setup.holders`). -/
def holdT (arT qT fwT gT iT v : Term) (p : Term) : Term :=
  ite (orientT arT qT fwT gT iT) (add (mul v gT) p) (add (mul p gT) v)

/-- **The width of the copies** of node `v` of the child (`xiWidN`). -/
def xiWidT (arT qT fwT gT iT v : Term) : Term :=
  copiesWidT arT qT fwT (holdT arT qT fwT gT iT v) gT

theorem val_holdT {v : Term} {V : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hv : Val w v env V) :
    FVal w (holdT arT qT fwT gT iT v) env
      (fun p => if orientN ar q fw g i then V * g + p else p * g + V) :=
  fun pre _p _P hp => val_iteI (val_orientT (h.extend pre))
    (val_add (val_mul (hv.ext pre) (h.extend pre).vg) hp)
    (val_add (val_mul hp (h.extend pre).vg) (hv.ext pre))

theorem tm_holdT {v : Term} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hv : Tm w L 1 v env) :
    TmF w L (holdT arT qT fwT gT iT v) 1 3 env := fun e he p hp => by
  have := t.hL
  exact (t_ite (tm_orientT (h.ext' he) (t.ext' he))
    (t_add (t_mul (hv.ext he) (t.ext' he).tg (by norm_num)) hp (by omega) (by norm_num))
    (t_add (t_mul hp (t.ext' he).tg (by norm_num)) (hv.ext he) (by omega) (by norm_num))).mono
      (d' := 3) (by norm_num)

theorem val_xiWidT {v : Term} {V : ℕ} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (hv : Val w v env V) : Val w (xiWidT arT qT fwT gT iT v) env (xiWidN ar q fw g i V) :=
  val_copiesWidT h.vA h.vq h.vfw (val_holdT h hv) h.vg

theorem tm_xiWidT {v : Term} (h : Inp w env arT qT fwT gT iT ar q fw g i)
    (t : Tiers w L env arT qT fwT gT iT fw g) (hv : Tm w L 1 v env) :
    Tm w L 6 (xiWidT arT qT fwT gT iT v) env :=
  tm_sliceOffT h t (tm_holdT h t hv) (by norm_num) t.tg (by norm_num)

/-- The number of factors `g + g² + g² + g⁴` of a summand on a `g × g` grid (`nFac`). -/
def nFacT (gT : Term) : Term := add (add (add gT (mul gT gT)) (mul gT gT)) (powC gT 4)

theorem val_nFacT (hg : Val w gT env g) :
    Val w (nFacT gT) env (g + g * g + g * g + g ^ 4) :=
  val_add (val_add (val_add hg (val_mul hg hg)) (val_mul hg hg)) (val_powC hg 4)

theorem tm_nFacT (hg : Tm w L 1 gT env) (hL : 16 ≤ L) : Tm w L 6 (nFacT gT) env :=
  t_add (t_add (t_add hg (t_mul hg hg (by norm_num)) (by omega) (by norm_num))
    (t_mul hg hg (by norm_num)) (by omega) (by norm_num)) (tm_powC hg hL 4 (by norm_num))
    (by omega) (by norm_num)

/-! ### The terms on the arrays of cliques -/

/-- The budget term reads `budget a u v` from the array of a clique whose budgets fit. -/
theorem val_budT_budget {q : ℕ} {a : Fin q → Fin q → ℕ} {u v : Term} {U V : Fin q}
    (har : Val w arT env (arrN q fw (extN a))) (hq : Val w qT env q) (hfw : Val w fwT env fw)
    (hfit : Fits fw a) (hu : Val w u env U) (hv : Val w v env V) (huv : U ≠ V) :
    Val w (budT arT qT fwT u v) env (budget a U V) :=
  (val_budT har hq hfw hu hv).congr (budgetN_ext hfit huv)

/-- The diagonal-weight term at the index of a rectangle is `diagWt`. -/
theorem val_diagT_diagWt {a : Fin (g * g) → Fin (g * g) → ℕ} {x : Term} {r : Rect g}
    (h : Inp w env arT qT fwT gT iT (arrN (g * g) fw (extN a)) (g * g) fw g i) (hfit : Fits fw a)
    (hx : Val w x env (rectIdx r)) : Val w (diagT arT qT fwT gT x) env (diagWt a r) :=
  (val_diagT h hx).congr (diagN_eq hfit r)

/-- The orientation term computes `orientRow` (even grades). -/
theorem val_orientT_orientRow {a : Fin (g * g) → Fin (g * g) → ℕ}
    (h : Inp w env arT qT fwT gT iT (arrN (g * g) fw (extN a)) (g * g) fw g i) (hfit : Fits fw a)
    (he : ∀ r, Even (decodeChoice g fw i r).1) :
    Val w (orientT arT qT fwT gT iT) env
      (ind (orientRow a (fun r => (decodeChoice g fw i r).1) = true)) :=
  (val_orientT h).congr (by rw [orientN_eq hfit he])

/-- **The child-array term** computes the array of the child clique `childAt fw C i`, for a
clique on `g × g` nodes (`g = ⌊√q⌋`) whose budgets fit, at a valid choice code. -/
theorem val_childT_childAt {C : Clique} (hsq : C.q = Nat.sqrt C.q * Nat.sqrt C.q)
    (h : Inp w env arT qT fwT gT iT (arrN C.q fw (extN C.a)) C.q fw (Nat.sqrt C.q) i)
    (hfit : Fits fw C.a) (hv : ValidChoiceCode (C.recast _ hsq).a fw i) :
    Val w (childT arT qT fwT gT iT) env (arrN (Nat.sqrt C.q) fw (extN (childAt fw C i).a)) :=
  (val_childT h).congr (childN_eq_childAt C hsq hfit (ValidChoiceCode.even hv)).symm

end Cslib.Complexity.NtimeDspace.Cube.Num
