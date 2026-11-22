/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.EntryTerm2
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.FirstTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.TransTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.GenQuery

/-!
# The programs of the formula (Lemma 6.4)

The numeric generator `Num.cubeFun` of `GenNum.lean` as closed programs (`SumProduct.GenProg`).
The construction is generic in the inputs: a bundle `CubeT` of terms over the parameter `[par]`
(the network accessors `NetT`, the precision `P`, the reader fuel `B`, the field width `fw`, the
number `K` of vertex groups and the fuel `H` of the unfolding), so it serves every instance of the
network interface (`famNetT` for a `LogspaceNetFamily`, `blockNetT` for block networks), with the
values of the inputs read from fields of `par` or computed from them.

## Main definitions

* `inRangeT`, `litBitT` (`litBitN`), `rng0ChildT` (`rng0ChildN`).
* `cubeTagT`, `cubeWidthT`, `cubeBitT`, `cubeChildT`: the dispatch on the kind field (`cubeTag`,
  `cubeWidth`, `cubeBit`, `cubeChild`), from the terms `eTagT`, `eWidthT`, `eChildT` of
  `EntryTerm2.lean` and `trTagT`, `trWidthT`, `trLeafT`, `trChildAllT` of `TransTerm.lean`.
* `CubeT`, `CubeIn`: the input terms over `[par]` and their values.
* `firstOf T a b`, `f0T T a b c`: the leaf factors of the first clique (`factor0T` of
  `FirstTerm.lean`), as literal codes; `initT T`: the code of the root `cl []`, with the budget
  array of the first clique (`firstArrT`).
* `cubeProg T`: the `GenProg` (each program is the term closed by `Cross.Exact.closeAt`).

## Main results

* `val_litBitT`, `val_rng0ChildT`, `val_cubeTagT`, `val_cubeWidthT`, `val_cubeBitT`,
  `val_cubeChildT`, `val_f0T`, `val_initT`.
* `cubeProg_toFun`: at every input `w` and parameter `par` whose fields have the values of a setup,
  `(cubeProg T).toFun w par` is `cubeFun` with the leaf codes `f0C`.
* `cubeProg_init`, `cubeProg_fuel`: the root code and the fuel `H`.
* `cubeProg_value`, `cubeProg_cost`: the generated recursion has value `Z(G) mod 2^P` and the cost
  of the formula, for a fuel `H ≥ c / ℓ + 1`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct NtimeDspace.Cross

variable {w : List Bool} {env : List ℕ}

/-! ### Small terms -/

/-- `1` if `a ≤ t ≤ b`, else `0`. -/
def inRangeT (t : Term) (a b : ℕ) : Term := mul (lt (const a) (add t (const 1)))
    (lt t (const (b + 1)))

theorem val_inRangeT {t : Term} {T : ℕ} (ht : Val w env t T) (a b : ℕ) :
    Val w env (inRangeT t a b) (if a ≤ T ∧ T ≤ b then 1 else 0) :=
  (val_mul (val_lt (val_const a) (val_add ht (val_const 1))) (val_lt ht (val_const (b + 1)))).congr
    (by split_ifs <;> omega)

/-- `litBitN` (as `0` or `1`). -/
def litBitT (z k : Term) : Term :=
  ite (eqT (mod z (const 2)) (const 0)) (bit (div z (const 2)) k)
    (sub (const 1) (bit (div (sub z (const 1)) (const 2)) k))

theorem val_litBitT {z k : Term} {Z Kv : ℕ} (hz : Val w env z Z) (hk : Val w env k Kv) :
    Val w env (litBitT z k) (litBitN Z Kv).toNat := by
  refine (val_ite (val_eqT (val_mod hz (val_const 2)) (val_const 0))
    (val_bit (val_div hz (val_const 2)) hk)
    (val_sub (val_const 1) (val_bit (val_div (val_sub hz (val_const 1))
        (val_const 2)) hk))).congr ?_
  unfold litBitN
  simp only [ite_ind]
  split_ifs
  · rfl
  · cases ((Z - 1) / 2).testBit Kv <;> rfl

/-- `rng0ChildN`, with the leaf codes `f0T v x f`. -/
def rng0ChildT (f0T : Term → Term → Term → Term) (n b : Term) : Term :=
  ite (eqT b (const 0))
    (rangeT (f0T (stGetT n 2) (stGetT n 3))
      (fun lo hi => encE [const 6, stGetT n 1, stGetT n 2, stGetT n 3, lo, hi])
      (stGetT n 4) (div (add (stGetT n 4) (stGetT n 5)) (const 2)))
    (rangeT (f0T (stGetT n 2) (stGetT n 3))
      (fun lo hi => encE [const 6, stGetT n 1, stGetT n 2, stGetT n 3, lo, hi])
      (div (add (stGetT n 4) (stGetT n 5)) (const 2)) (stGetT n 5))

theorem val_rng0ChildT {f0T : Term → Term → Term → Term} {f0 : ℕ → ℕ → ℕ → ℕ} {n b : Term}
    {nv bv : ℕ} (hn : Val w env n nv) (hb : Val w env b bv)
    (hf0 : ∀ a b c A B C, Val w env a A → Val w env b B → Val w env c C →
      Val w env (f0T a b c) (f0 A B C)) :
    Val w env (rng0ChildT f0T n b) (rng0ChildN f0 nv bv) := by
  have g := fun k => val_stGetT hn k
  have hmid := val_div (val_add (g 4) (g 5)) (val_const 2)
  have hR := fun (lo hi : Term) (Lo Hi : ℕ) (hlo : Val w env lo Lo) (hhi : Val w env hi Hi) =>
    val_rangeT (mk := f0T (stGetT n 2) (stGetT n 3)) (MK := f0 (stGet nv 2) (stGet nv 3))
      (MKR := fun Lo Hi => NatList.enc [6, stGet nv 1, stGet nv 2, stGet nv 3, Lo, Hi])
      (mkR := fun lo hi => encE [const 6, stGetT n 1, stGetT n 2, stGetT n 3, lo, hi]) hlo hhi
      (hf0 _ _ _ _ _ _ (g 2) (g 3) hlo)
      (val_encE (w := w) (env := env) (.cons (val_const 6) (.cons (g 1) (.cons (g 2) (.cons (g 3)
        (.cons hlo (.cons hhi .nil)))))))
  refine (val_ite (val_eqT hb (val_const 0)) (hR _ _ _ _ (g 4) hmid)
      (hR _ _ _ _ hmid (g 5))).congr ?_
  unfold rng0ChildN
  simp only [ite_ind]

/-! ### The dispatch -/

/-- `cubeTag`. -/
def cubeTagT (BT fwT n : Term) : Term :=
  ite (inRangeT (stGetT n 0) 2 5) (eTagT BT fwT n)
    (ite (eqT (stGetT n 0) (const 6)) (const 2)
      (ite (inRangeT (stGetT n 0) 7 9) (trTagT n) (const 0)))

/-- `cubeWidth`. -/
def cubeWidthT (BT fwT n : Term) : Term :=
  ite (inRangeT (stGetT n 0) 2 5) (eWidthT fwT n)
    (ite (inRangeT (stGetT n 0) 7 9) (trWidthT BT n) (const 0))

/-- `cubeBit` (as `0` or `1`). -/
def cubeBitT (BT n k : Term) : Term :=
  ite (eqT (stGetT n 0) (const 1)) (litBitT (stGetT n 1) k)
    (ite (inRangeT (stGetT n 0) 7 9) (bit (trLeafT BT n) k) (const 0))

/-- `cubeChild`. -/
def cubeChildT (fwT BT KT VT MT : Term) (f0T : Term → Term → Term → Term) (n i : Term) : Term :=
  ite (inRangeT (stGetT n 0) 2 5) (eChildT fwT BT KT VT MT f0T n i)
    (ite (eqT (stGetT n 0) (const 6)) (rng0ChildT f0T n i)
      (ite (inRangeT (stGetT n 0) 7 9) (trChildAllT BT n i) zeroCT))

section Dispatch

variable {BT fwT KT VT MT n i k : Term} {f0T : Term → Term → Term → Term} {f0 : ℕ → ℕ → ℕ → ℕ}
  {Bv fw K Vv M nv iv kv : ℕ}

theorem val_cubeTagT (hB : Val w env BT Bv) (hfw : Val w env fwT fw) (hn : Val w env n nv) :
    Val w env (cubeTagT BT fwT n) (cubeTag Bv fw nv) := by
  have g0 := val_stGetT hn 0
  refine (val_ite (val_inRangeT g0 2 5) (val_eTagT hB hfw hn)
    (val_ite (val_eqT g0 (val_const 6)) (val_const 2)
      (val_ite (val_inRangeT g0 7 9) (val_trTagT hn) (val_const 0)))).congr ?_
  unfold cubeTag
  simp only [ite_ind]

theorem val_cubeWidthT (hB : Val w env BT Bv) (hfw : Val w env fwT fw) (hn : Val w env n nv) :
    Val w env (cubeWidthT BT fwT n) (cubeWidth Bv fw nv) := by
  have g0 := val_stGetT hn 0
  refine (val_ite (val_inRangeT g0 2 5) (val_eWidthT hfw hn)
    (val_ite (val_inRangeT g0 7 9) (val_trWidthT hB hn) (val_const 0))).congr ?_
  unfold cubeWidth
  simp only [ite_ind]

theorem val_cubeBitT (hB : Val w env BT Bv) (hn : Val w env n nv) (hk : Val w env k kv) :
    Val w env (cubeBitT BT n k) (cubeBit Bv nv kv).toNat := by
  have g0 := val_stGetT hn 0
  refine (val_ite (val_eqT g0 (val_const 1)) (val_litBitT (val_stGetT hn 1) hk)
    (val_ite (val_inRangeT g0 7 9) (val_bit (val_trLeafT hB hn) hk) (val_const 0))).congr ?_
  unfold cubeBit
  simp only [ite_ind]
  split_ifs <;> rfl

theorem val_cubeChildT (hfw : Val w env fwT fw) (hB : Val w env BT Bv) (hK : Val w env KT K)
    (hV : Val w env VT Vv) (hM : Val w env MT M) (hn : Val w env n nv) (hi : Val w env i iv)
    (hf0 : ∀ a b c A B C, Val w env a A → Val w env b B → Val w env c C →
      Val w env (f0T a b c) (f0 A B C)) :
    Val w env (cubeChildT fwT BT KT VT MT f0T n i) (cubeChild fw Bv K Vv M f0 nv iv) := by
  have g0 := val_stGetT hn 0
  refine (val_ite (val_inRangeT g0 2 5) (val_eChildT hfw hB hK hV hM hn hi hf0)
    (val_ite (val_eqT g0 (val_const 6)) (val_rng0ChildT hn hi hf0)
      (val_ite (val_inRangeT g0 7 9) (val_trChildAllT hB hn hi) val_zeroCT))).congr ?_
  unfold cubeChild
  simp only [ite_ind]

end Dispatch

/-! ### The inputs -/

/-- The input terms, over the parameter `[par]`: the network accessors, the precision, the reader
fuel, the field width, the number of vertex groups and the fuel of the unfolding. -/
structure CubeT where
  N : NetT
  PT : Term
  BT : Term
  fwT : Term
  KT : Term
  HT : Term

variable {V : ℕ} (G : EdgeNet ℤ (Fin V))

/-- The values of the inputs at the parameter `par`. -/
structure CubeIn (w : List Bool) (par : ℕ) (T : CubeT) (P B fw K H : ℕ) : Prop where
  hA : NetAcc G w [par] T.N
  vP : Val w [par] T.PT P
  vB : Val w [par] T.BT B
  vfw : Val w [par] T.fwT fw
  vK : Val w [par] T.KT K
  vH : Val w [par] T.HT H

variable {G}

/-- The terms of the first clique at the node `a` and the argument code `b`. -/
def firstOf (T : CubeT) (a b : Term) : FirstT :=
  ⟨T.N, T.KT, mul (const 2) T.KT, T.fwT, firstArrT T.N T.KT (mul (const 2) T.KT) T.fwT, a, b⟩

/-- The code of the literal of the leaf factor `c` at the node `a` and the argument code `b`. -/
def f0T (T : CubeT) (a b c : Term) : Term := litCT (mul (const 2) (factor0T (firstOf T a b) c))

/-- The code of the root `cl []`: the empty path and the budget array of the first clique. -/
def initT (T : CubeT) : Term :=
  encE [const 2, const 1, encE [encE [mul (const 2) T.KT, firstArrT T.N T.KT
      (mul (const 2) T.KT) T.fwT]]]

section Inputs

variable {T : CubeT} {par P B fw K H : ℕ} {E : List ℕ}

theorem val_f0T (hT : CubeIn G w par T P B fw K H) (hE : Above [par] E) {a b c : Term} {A Bv C : ℕ}
    (ha : Val w E a A) (hb : Val w E b Bv) (hc : Val w E c C) :
    Val w E (f0T T a b c) (f0C G K fw A Bv C) := by
  have hA := hT.hA.up hE
  have vK := hT.vK.up hE
  have vq : Val w E (mul (const 2) T.KT) (2 * K) := val_mul (val_const 2) vK
  have vfw := hT.vfw.up hE
  have h : FIn G w E (firstOf T a b) K fw (arrN (2 * K) fw (extN (firstBudget G K))) A Bv :=
    ⟨hA, vK, vq, vfw, val_firstArrT hA vK vq vfw, ha, hb⟩
  exact val_litCT (val_mul (val_const 2) (val_factor0T h hc))

theorem val_initT (S : Setup) (hT : CubeIn S.G w par T P B S.fw S.K H) (hE : Above [par] E) :
    Val w E (initT T) (S.code (.cl [])) := by
  have hA := hT.hA.up hE
  have vK := hT.vK.up hE
  have vq : Val w E (mul (const 2) T.KT) (2 * S.K) := val_mul (val_const 2) vK
  have vfw := hT.vfw.up hE
  have va := val_firstArrT hA vK vq vfw
  exact val_encE (.cons (val_const 2) (.cons (val_const 1)
    (.cons (val_encE (.cons (val_encE (.cons vq (.cons va .nil))) .nil)) .nil)))

end Inputs

/-! ### The programs -/

/-- **The programs of the formula**: the root code and the fuel from `[par]`, the tag, precision
and index width from `[st, par]`, the leaf bits from `[k, st, par]`, and the child codes from
`[st, i, par]`. -/
def cubeProg (T : CubeT) : GenProg where
  init := Exact.closeAt 1 (initT T 1)
  fuel := Exact.closeAt 1 (T.HT 1)
  child := Exact.closeAt 3 (cubeChildT T.fwT T.BT T.KT T.N.VT T.N.MT (f0T T) (lvl 2) (lvl 1) 3)
  tag := Exact.closeAt 2 (cubeTagT T.BT T.fwT (lvl 1) 2)
  prec := Exact.closeAt 2 (T.PT 2)
  param := Exact.closeAt 2 (cubeWidthT T.BT T.fwT (lvl 1) 2)
  bit := Exact.closeAt 3 (cubeBitT T.BT (lvl 1) (lvl 2) 3)
  init_closed := Exact.closed_closeAt _ _
  fuel_closed := Exact.closed_closeAt _ _
  child_closed := Exact.closed_closeAt _ _
  tag_closed := Exact.closed_closeAt _ _
  prec_closed := Exact.closed_closeAt _ _
  param_closed := Exact.closed_closeAt _ _
  bit_closed := Exact.closed_closeAt _ _

theorem eval_close (t : Term) (e : List ℕ) :
    (Exact.closeAt e.length (t e.length)).eval w e = t.denote w e :=
  Exact.eval_closeAt _ _ _ rfl

theorem val_lvl_at {e : List ℕ} {l : ℕ} (hl : l < e.length) :
    Val w e (lvl l) (e.getD (e.length - l - 1) 0) :=
  ⟨stableAt_lvl hl, rfl⟩

section Programs

variable {T : CubeT} {par B H : ℕ}

theorem above_one (pre : List ℕ) (par : ℕ) : Above [par] (pre ++ [par]) := ⟨pre, rfl⟩

/-- **The programs compute the numeric generator** at every state code. -/
theorem cubeProg_toFun (S : Setup) (hT : CubeIn S.G w par T S.P B S.fw S.K H) :
    (cubeProg T).toFun w par = cubeFun S.P B S.fw S.K S.V S.G.M (f0C S.G S.K S.fw) := by
  have e2 : ∀ (t : Term) (st : ℕ), (Exact.closeAt 2 (t 2)).eval w [st, par] =
      t.denote w [st, par] :=
    fun t st => eval_close t [st, par]
  have e3 : ∀ (t : Term) (a b : ℕ), (Exact.closeAt 3 (t 3)).eval w [a, b, par] =
      t.denote w [a, b, par] := fun t a b => eval_close t [a, b, par]
  unfold GenProg.toFun cubeFun
  congr 1
  · funext st
    have hE := above_one [st] par
    exact (e2 _ st).trans (val_cubeTagT (hT.vB.up hE) (hT.vfw.up hE)
      (val_lvl_at (e := [st, par]) (l := 1) (by simp))).2
  · funext st
    exact (e2 _ st).trans (hT.vP.up (above_one [st] par)).2
  · funext st
    have hE := above_one [st] par
    exact (e2 _ st).trans (val_cubeWidthT (hT.vB.up hE) (hT.vfw.up hE)
      (val_lvl_at (e := [st, par]) (l := 1) (by simp))).2
  · funext st k
    have hE := above_one [k, st] par
    have := (e3 (cubeBitT T.BT (lvl 1) (lvl 2)) k st).trans (val_cubeBitT (hT.vB.up hE)
      (val_lvl_at (e := [k, st, par]) (l := 1) (by simp))
      (val_lvl_at (e := [k, st, par]) (l := 2) (by simp))).2
    change decide (0 < (Exact.closeAt 3 (cubeBitT T.BT (lvl 1) (lvl 2) 3)).eval w [k, st, par]) = _
    rw [this]
    change decide (0 < (cubeBit B st k).toNat) = cubeBit B st k
    cases cubeBit B st k <;> rfl
  · funext st i
    have hE := above_one [st, i] par
    exact (e3 _ st i).trans (val_cubeChildT (hT.vfw.up hE) (hT.vB.up hE) (hT.vK.up hE)
      ((hT.hA.up hE).vV) ((hT.hA.up hE).vM)
      (val_lvl_at (e := [st, i, par]) (l := 2) (by simp))
      (val_lvl_at (e := [st, i, par]) (l := 1) (by simp))
      fun _ _ _ _ _ _ ha hb hc => val_f0T hT hE ha hb hc).2

theorem cubeProg_init (S : Setup) (hT : CubeIn S.G w par T S.P B S.fw S.K H) :
    (cubeProg T).init₀ w par = S.code (.cl []) :=
  (eval_close (initT T) [par]).trans (val_initT S hT (Above.refl _)).2

theorem cubeProg_fuel (S : Setup) (hT : CubeIn S.G w par T S.P B S.fw S.K H) :
    (cubeProg T).fuel₀ w par = H :=
  (eval_close T.HT [par]).trans hT.vH.2

/-- **The value of the generated recursion**: `Z(G) mod 2^P`, for a good setup with
`2K = 2^(2^D)`, a network with nonnegative vertex functions, a weight bound
`A ≥ 12 (Φ₀ / 2^D) + 1`, a reader fuel `B ≥ len(A) + 2`, `ℓ ≥ 1`, a bound `c` on the cost of the
formula at every fuel, and a fuel `H ≥ c / ℓ + 1`. -/
theorem cubeProg_value (S : Setup) (hS : S.Good) {D A : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A + 2 ≤ B) (hnn : EvalNonneg S.G)
    (hT : CubeIn S.G w par T S.P B S.fw S.K H) {ℓ c : ℕ} (hℓ : 1 ≤ ℓ)
    (hc : ∀ n, (S.gen.tree S.P n (.cl [])).cost ℓ ≤ c) (hH : c / ℓ + 1 ≤ H) :
    ((cubeProg T).tree w par).value = AGen.res S.P S.G.value := by
  rw [GenProg.tree, cubeProg_toFun S hT, cubeProg_init S hT, cubeProg_fuel S hT]
  exact cube_value S hS he hA hB (f0C_eq S hS hnn) hℓ hc H hH

/-- **The cost of the generated recursion** is the cost of the formula at the fuel `H`. -/
theorem cubeProg_cost (S : Setup) (hS : S.Good) {D A : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A + 2 ≤ B) (hnn : EvalNonneg S.G)
    (hT : CubeIn S.G w par T S.P B S.fw S.K H) (ℓ : ℕ) :
    ((cubeProg T).tree w par).cost ℓ = (S.gen.tree S.P H (.cl [])).cost ℓ := by
  rw [GenProg.tree, cubeProg_toFun S hT, cubeProg_init S hT, cubeProg_fuel S hT]
  exact cube_cost S hS he hA hB (f0C_eq S hS hnn) ℓ H

end Programs

end Cslib.Complexity.NtimeDspace.Cube.Num
