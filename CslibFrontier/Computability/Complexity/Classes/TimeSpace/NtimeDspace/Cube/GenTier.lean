/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.ArgWidth
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.StSize

/-!
# Tiers of the programs of the formula (Lemma 6.4)

The programs `cubeProg T` of `GenTerm.lean` read one state code. This module shows that on the codes
of the states reached from the root, their values stay below `2^(128 L)` (the tiers of
`Tame.lean`), so that the generated recursion is evaluated in space `O(L)`.

* **The states along a path.** Every valid path of `(cubeProg T).tree w par` leads to the code of a
  state reached from the root (`Setup.Reach` of `StSize.lean`) that satisfies the invariant
  `Setup.CubeInv` (`cubeProg_pathState`, from the generic `AGen.path_state`).
* **The tiers.** Under the input values `CubeIn` and the bundle `CubeTiers` of tier and size
  hypotheses, on a state code of tier `1` of a state of `CubeInv`: the kind tag has tier `1`
  (`tm_cubeTagT`), the index width tier `7` (`tm_cubeWidthT`), the leaf bits tier `1` at any bit
  index of some tier (`tm_cubeBitT`), the leaf factors of the first clique tier `9`
  (`tm_f0T`), and the child at an index of tier `1` tier `1` when the code of the child is
  below `2^L` (`tm_rng0ChildT`, `tm_cubeChildT`).
* **The programs.** At the environments the evaluator uses, the closed programs are bounded by
  `2^(128 L)`: `cubeProg_init_bnd`, `cubeProg_fuel_bnd` at `[par]`; `cubeProg_tag_bnd`,
  `cubeProg_prec_bnd`, `cubeProg_param_bnd` at `[code st, par]`; `cubeProg_bit_bnd` at
  `[k, code st, par]`; `cubeProg_child_bnd` at `[code st, i, par]`; and `cubeProg_pathBounded`
  gives `GenProg.PathBounded` along a valid path whose code fits the bound and whose indices are
  below `2^L`.

## Main definitions

* `CubeTiers S w L par T D A B`: the tiers of the input terms at `[par]` (`NetTiers` and tier `1`
  for `P`, `B`, `fw`, `K`, `H`), a good setup with nonnegative vertex functions and
  `2K = 2^(2^D)`, the weight bound `12 (Φ₀ / 2^D) + 1 ≤ A` and fuel `w(A) + 2 ≤ B ≤ L`, the size
  conditions `fw + q₀ < L`, `q₀² fw ≤ L` (`q₀ = 2K`) and `3600 Φ₀ < L² · 2^D` (the argument codes,
  `SizeOK.of_potential`), and the bound `S.code st < 2^L` on the codes of the reached states.

## Main results

* `AGen.path_state`, `cubeProg_pathState`.
* `tm_tr_info`, `tm_f0T`, `tm_cubeTagT`, `tm_cubeWidthT`, `tm_cubeBitT`, `tm_rng0ChildT`,
  `tm_eChildT_cube`, `tm_cubeChildT`, and the instances at the evaluator's environments
  `tm_cubeTag_at`, `tm_cubeWidth_at`, `tm_cubeBit_at`, `tm_cubeChild_at`, `tm_initT`.
* `cubeProg_*_bnd`, `cubeProg_pathBounded`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube

open SumProduct

/-! ### The states along a path -/

namespace AGen

variable {St : Type} (g : AGen St)

/-- **The states along a valid path** of the numeric unfolding: for a numeric generator agreeing
with `g` under `e` on an invariant `inv`, and a predicate `R` closed under the valid children, every
valid path from the code of a state of `inv ∧ R` leads to the code of a state of `inv ∧ R`. -/
theorem path_state {gn : GenFun} {e : St → ℕ} {inv : St → Prop} {P : ℕ} (h : g.Agrees gn e inv P)
    (R : St → Prop)
    (hsum : ∀ st, R st → g.kind st = .sum → ∀ i < 2 ^ g.width st, R (g.child st i))
    (hprod : ∀ st, R st → g.kind st = .prod → ∀ b < 2, R (g.child st b))
    (n : ℕ) {st₀ : St} (h0 : inv st₀) (hR0 : R st₀) :
    ∀ π : List ℕ, SPTree.Valid (gn.tree n (e st₀)) π →
      ∃ st, gn.stateAt (e st₀) π = e st ∧ inv st ∧ R st
  | [], _ => ⟨st₀, rfl, h0, hR0⟩
  | i :: π, ⟨hπ, hi⟩ => by
    obtain ⟨st, hst, hinv, hR⟩ := path_state h R hsum hprod n h0 hR0 π hπ
    obtain ⟨-, hnode⟩ := gn.node_tree n (e st₀) π hπ
    rw [hnode, hst] at hi
    have hc : gn.stateAt (e st₀) (i :: π) = e (g.child st i) := by
      show gn.child (gn.stateAt (e st₀) π) i = _
      rw [hst, h.child st hinv]
    have ht := h.tag st hinv
    rcases hm : n - π.length with _ | m
    · rw [hm] at hi
      exact absurd hi (by simp only [GenFun.tree, SPTree.ValidChild, not_false_eq_true])
    rw [hm] at hi
    rcases hk : g.kind st with _ | _ | _ <;> rw [hk] at ht <;> simp only [kindTag] at ht
    · exact absurd hi (by
        simp only [GenFun.tree, ht, show ¬ ((0 : ℕ) = 1) by omega, show ¬ ((0 : ℕ) = 2) by omega,
          show ¬ ((0 : ℕ) = 3) by omega, ite_false, SPTree.ValidChild, not_false_eq_true])
    · simp only [GenFun.tree, ht, ite_true, SPTree.ValidChild] at hi
      rw [h.param st hinv hk] at hi
      exact ⟨_, hc, h.closed_sum st hinv hk i hi, hsum st hR hk i hi⟩
    · simp only [GenFun.tree, ht, show ¬ ((2 : ℕ) = 1) by omega, ite_false, ite_true,
        SPTree.ValidChild] at hi
      obtain ⟨h0', h1'⟩ := h.closed_prod st hinv hk
      refine ⟨_, hc, ?_, hprod st hR hk i hi⟩
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      exacts [h0', h1']

/-- **A valid step of a path**: the state before the step and the state after it are states of
`inv ∧ R` and `R`, and the code of the child is the code of the state after the step. -/
theorem path_step {gn : GenFun} {e : St → ℕ} {inv : St → Prop} {P : ℕ} (h : g.Agrees gn e inv P)
    (R : St → Prop)
    (hsum : ∀ st, R st → g.kind st = .sum → ∀ i < 2 ^ g.width st, R (g.child st i))
    (hprod : ∀ st, R st → g.kind st = .prod → ∀ b < 2, R (g.child st b))
    (n : ℕ) {st₀ : St} (h0 : inv st₀) (hR0 : R st₀) (i : ℕ) (ρ : List ℕ)
    (hρ : SPTree.Valid (gn.tree n (e st₀)) (i :: ρ)) :
    ∃ st st', gn.stateAt (e st₀) ρ = e st ∧ inv st ∧ R st ∧ R st' ∧ e (g.child st i) = e st' := by
  obtain ⟨st, h1, h2, h3⟩ := g.path_state h R hsum hprod n h0 hR0 ρ hρ.1
  obtain ⟨st', h1', -, h3'⟩ := g.path_state h R hsum hprod n h0 hR0 (i :: ρ) hρ
  refine ⟨st, st', h1, h2, h3, h3', ?_⟩
  rw [← h1', ← h.child st h2, ← h1]
  rfl

end AGen

namespace Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross

variable {w : List Bool} {L : ℕ}

/-- **The states along a valid path of the programs** are the codes of states reached from the root
that satisfy the invariant `CubeInv D A B`. -/
theorem cubeProg_pathState (S : Setup) (hS : S.Good) {D A B H par : ℕ} {T : CubeT}
    (he : 2 * S.K = 2 ^ 2 ^ D) (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A)
    (hB : codeWidth A + 2 ≤ B)
    (hnn : EvalNonneg S.G) (hT : CubeIn S.G w par T S.P B S.fw S.K H) (π : List ℕ)
    (hπ : SPTree.Valid ((cubeProg T).tree w par) π) :
    ∃ st, ((cubeProg T).toFun w par).stateAt ((cubeProg T).init₀ w par) π = S.code st ∧
      S.Reach st ∧ S.CubeInv D A B st := by
  rw [GenProg.tree, cubeProg_toFun S hT, cubeProg_init S hT] at hπ
  rw [cubeProg_toFun S hT, cubeProg_init S hT]
  obtain ⟨st, h1, h2, h3⟩ := S.gen.path_state (cube_agrees S hS he hA hB (f0C_eq S hS hnn)) S.Reach
    (fun st hR hk i hi => Setup.Reach.sum st i hR hk hi)
    (fun st hR hk b hb => Setup.Reach.prod st b hR hk hb) _ (S.cubeInv_root he) Setup.Reach.root
    π hπ
  exact ⟨st, h1, h3, h2⟩

/-! ### The bundled hypotheses -/

/-- **The tiers and sizes of the inputs** at budget `L`: the network terms satisfy `NetTiers` and
the terms `P`, `B`, `fw`, `K`, `H` have tier `1` at `[par]`; the setup is good with nonnegative
vertex functions; `2K = 2^(2^D)`, `12 (Φ₀ / 2^D) + 1 ≤ A` and `w(A) + 2 ≤ B ≤ L`; the field width
and the first clique (`q₀ = 2K` nodes) fit: `fw + q₀ < L` and `q₀² fw ≤ L`; the argument codes fit:
`3600 Φ₀ < L² · 2^D` (`SizeOK.of_potential`); and every state reached from the root has a code below
`2^L` (`state_size` of `StSize.lean`). -/
structure CubeTiers (S : Setup) (w : List Bool) (L par : ℕ) (T : CubeT) (D A B : ℕ) : Prop where
  hT : NetTiers S.G w L [par] T.N
  tP : Tm w L 1 T.PT [par]
  tB : Tm w L 1 T.BT [par]
  tfw : Tm w L 1 T.fwT [par]
  tK : Tm w L 1 T.KT [par]
  tH : Tm w L 1 T.HT [par]
  hS : S.Good
  hnn : EvalNonneg S.G
  he : 2 * S.K = 2 ^ 2 ^ D
  hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A
  hB : codeWidth A + 2 ≤ B
  hBL : B ≤ L
  hq : S.fw + 2 * S.K < L
  harg : 3600 * S.C₀.potential < L ^ 2 * 2 ^ D
  hArr : 2 * S.K * (2 * S.K) * S.fw ≤ L
  hcode : ∀ st, S.Reach st → S.code st < 2 ^ L

section Tiers

variable {S : Setup} {par A B H D : ℕ} {T : CubeT} {E : List ℕ}

namespace CubeTiers

variable (hG : CubeTiers S w L par T D A B)
include hG

theorem hL : 16 ≤ L := hG.hT.hL

theorem hB0 : codeWidth (S.C₀.potential / 2 ^ D) + 2 ≤ B :=
  le_trans (Nat.add_le_add_right (codeWidth_mono (by have := hG.hA; omega)) 2) hG.hB

theorem hK1 : 1 ≤ S.K := hG.hS.1

theorem hfw : S.fw < L := by have := hG.hq; omega

theorem hqL : 2 * S.K < L := by have := hG.hq; omega

theorem sizeOK : SizeOK S L := SizeOK.of_potential hG.hS hG.he hG.hArr hG.harg

/-- The bundle `EIn` of `EntryTerm2.lean` at an extension of `[par]`. -/
theorem ein (hI : CubeIn S.G w par T S.P B S.fw S.K H) (hE : Ext L E [par]) {nT : Term} {st : St}
    (hn : Val w E nT (S.code st)) (tn : Tm w L 1 nT E) : EIn S w L E nT T.fwT T.BT st B :=
  ⟨hn, hI.vfw.up (ext_above hE), hI.vB.up (ext_above hE), tn, hG.tfw.ext hE, hG.tB.ext hE, hG.hL,
    hG.hfw, hG.hBL, ⟨D, hG.he, hG.hB0⟩, hG.hS⟩

end CubeTiers

theorem code_enc (S : Setup) (st : St) : ∃ l : List ℕ, S.code st = NatList.enc l ∧ 0 <
    l.length := by
  cases st <;> exact ⟨_, rfl, by simp⟩

theorem entrySt_of_tag {st : St} (S : Setup) (h : 2 ≤ stGet (S.code st) 0 ∧ stGet (S.code st) 0 ≤ 5)
    :
    EntrySt st := by
  rw [stGet_code_zero S] at h
  cases st <;> first | trivial | simp at h

theorem trInv_of_tag {st : St} (hinv : S.CubeInv D A B st)
    (h : 7 ≤ stGet (S.code st) 0 ∧ stGet (S.code st) 0 ≤ 9) : TrInv A B st := by
  rw [stGet_code_zero S] at h
  cases st <;> first | exact hinv.2 | simp at h

/-- The tier of a range test: `2`. -/
theorem tm_inRangeT {t : Term} {env : List ℕ} (ht : Tm w L 1 t env) (hL : 16 ≤ L) {a b : ℕ}
    (ha : a < 16) (hb : b + 1 < 16) : Tm w L 2 (inRangeT t a b) env :=
  t_mul (t_lt (t_const (lit16 ha (by omega))) (t_add ht (t_one (by omega)) (by omega) (by norm_num))
    (by omega)) (t_lt ht (t_const (lit16 hb (by omega))) (by omega)) (by norm_num)

theorem lit_of_tag {st : St} (S : Setup) (h : stGet (S.code st) 0 = 1) : ∃ z, st = .lit z := by
  rw [stGet_code_zero S] at h
  cases st <;> first | exact ⟨_, rfl⟩ | simp at h

theorem rng0_of_tag {st : St} (S : Setup) (h : stGet (S.code st) 0 = 6) :
    ∃ v args lo hi, st = .rng0 v args lo hi := by
  rw [stGet_code_zero S] at h
  cases st <;> first | exact ⟨_, _, _, _, rfl⟩ | simp at h

/-! ### The transport states -/

/-- **The tag, index length and leaf of a transport state** have tier `1` (the first three parts
of `tm_tr_agree`, without a bound on a child). -/
theorem tm_tr_info (S : Setup) {A Bv de : ℕ} {B e : Term} {env : List ℕ} {st : St}
    (h : TrInv A Bv st) (hB : Val w env B Bv) (tB : Tm w L 1 B env) (hBL : Bv ≤ L) (hL : 10 ≤ L)
    (he : Val w env e (S.code st)) (te : Tm w L de e env) (hde : de ≤ 15) :
    Tm w L 1 (trTagT e) env ∧ Tm w L 1 (trWidthT B e) env ∧ Tm w L 1 (trLeafT B e) env := by
  have vf : ∀ k, Val w env (getV e (const k))
      (getF (S.code st) k) := fun k => val_getV he (val_const k)
  have tf : ∀ k ≤ 13, Tm w L de (getV e (const k)) env := fun k hk =>
    tm_getV he te (by omega) (val_const k) (t_const (small_lt_two_pow hk hL)) (by norm_num)
        (by omega)
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have k7 : Tm w L 1 (const 7) env := t_const (small_lt_two_pow (by norm_num) hL)
  have c7 := t_eqT' (tf 0 (by norm_num)) k7 (by omega)
  have v7 := val_eqT (vf 0) (val_const 7)
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
  refine ⟨tag, ?_, leaf⟩
  unfold trWidthT
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

/-! ### The leaf factors of the first clique -/

/-- **The tier of a leaf factor of the first clique** (`f0T`): `9`, at a node `v < 2K` of tier
`1`, an argument code of tier `32` and a factor index of tier `1`. -/
theorem tm_f0T (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    (hE : Ext L E [par]) {a b c : Term} {Av Bv Cv : ℕ} (ha : Val w E a Av) (ta : Tm w L 1 a E)
    (hav : Av < 2 * S.K) (hb : Val w E b Bv) (tb : Tm w L 32 b E) (hc : Val w E c Cv)
    (tc : Tm w L 1 c E) : Tm w L 9 (f0T T a b c) E := by
  have hL := hG.hL
  have hE' := ext_above hE
  have hA := hI.hA.up hE'
  have tT := hG.hT.up hE
  have vK := hI.vK.up hE'
  have tK := hG.tK.ext hE
  have vq : Val w E (mul (const 2) T.KT) (2 * S.K) := val_mul (val_const 2) vK
  have tq : Tm w L 1 (mul (const 2) T.KT) E :=
    tm_val (t_mul (t_small (k := 2) (by norm_num) (by omega)) tK (by norm_num)) vq
      (lt_tier_one hG.hqL.le)
  have vfw := hI.vfw.up hE'
  have tfw := hG.tfw.ext hE
  have hC : Fits S.fw (firstBudget S.G S.K) := fits_path S hG.hS (chs := []) trivial
  have tArr := tm_firstArrT (d := 1) hA tT vK tK hG.hK1 vq tq vfw tfw hG.hfw hC
    (by rw [one_mul]; exact hG.hArr) le_rfl (by norm_num)
  have fin : FIn S.G w E (firstOf T a b) S.K S.fw
      (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) Av Bv :=
    ⟨hA, vK, vq, vfw, val_firstArrT hA vK vq vfw, ha, hb⟩
  have ftr : FTiers S.G w L E (firstOf T a b) S.K S.fw
      (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) Av :=
    ⟨tT, tK, tq, tfw, tArr.mono (by norm_num), ta, tb, hG.hK1, hav, hG.hfw,
      fun n
          _ => (codeWidth_budgetN_path S hG.hS (chs := []) trivial hG.he hG.hB0 Av n).trans hG.hBL⟩
  have vz := val_mul (val_const 2) (val_factor0T fin hc)
  have tz : Tm w L 2 (mul (const 2) (factor0T (firstOf T a b) c)) E :=
    t_mul (t_small (k := 2) (by norm_num) (by omega)) (tm_factor0T ftr fin hc tc) (by norm_num)
  refine tm_litCT vz tz (by norm_num) (by norm_num) (by omega) ?_
  rw [(val_litCT vz).2]
  have hz := tz.lt
  rw [vz.2] at hz
  unfold litC
  refine (enc_lt_of_lt (N := 2 * L) ?_).trans_le (Nat.pow_le_pow_right (by norm_num)
    (by simp only [List.length_cons, List.length_nil]; omega))
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Nat.one_lt_two_pow (by omega)
  · exact hz

/-! ### Tags, widths and leaf bits -/

/-- **The tier of the kind tag** (`cubeTagT`): `1`, on the code (of tier `1`) of a state of the
invariant. -/
theorem tm_cubeTagT (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    (hE : Ext L E [par]) {nT : Term} {st : St} (hn : Val w E nT (S.code st)) (tn : Tm w L 1 nT E)
    (hinv : S.CubeInv D A B st) : Tm w L 1 (cubeTagT T.BT T.fwT nT) E := by
  have hL := hG.hL
  have h := hG.ein hI hE hn tn
  obtain ⟨l, hl, hlen⟩ := code_enc S st
  have g0 := val_stGetT hn 0
  have t0 := (h.field hl 0 hlen).2
  unfold cubeTagT
  refine tm_ite2v (val_inRangeT g0 2 5) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
    (fun hp => tm_eTagT h (entrySt_of_tag S (ind_of_pos' hp)) hinv.1) (fun _ => ?_)
  refine tm_ite2v (val_eqT g0 (val_const 6))
    (t_eqT' t0 (t_const (lit16 (by norm_num) (by omega))) (by omega))
    (fun _ => t_small (by norm_num) (by omega)) (fun _ => ?_)
  exact tm_ite2v (val_inRangeT g0 7 9) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
    (fun hp => (tm_tr_info S (trInv_of_tag hinv (ind_of_pos' hp)) (hI.vB.up (ext_above hE))
      (hG.tB.ext hE) hG.hBL (by omega) hn tn (by norm_num)).1)
    (fun _ => t_small (by norm_num) (by omega))

/-- **The tier of the index width** (`cubeWidthT`): `7`, on the code (of tier `1`) of a state of
the invariant. -/
theorem tm_cubeWidthT (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    (hE : Ext L E [par]) {nT : Term} {st : St} (hn : Val w E nT (S.code st)) (tn : Tm w L 1 nT E)
    (hinv : S.CubeInv D A B st) : Tm w L 7 (cubeWidthT T.BT T.fwT nT) E := by
  have hL := hG.hL
  have h := hG.ein hI hE hn tn
  obtain ⟨l, hl, hlen⟩ := code_enc S st
  have g0 := val_stGetT hn 0
  have t0 := (h.field hl 0 hlen).2
  unfold cubeWidthT
  refine tm_ite2v (val_inRangeT g0 2 5) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
    (fun hp => tm_eWidthT h (entrySt_of_tag S (ind_of_pos' hp)) hinv.1) (fun _ => ?_)
  exact tm_ite2v (val_inRangeT g0 7 9) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
    (fun hp => (tm_tr_info S (trInv_of_tag hinv (ind_of_pos' hp)) (hI.vB.up (ext_above hE))
      (hG.tB.ext hE) hG.hBL (by omega) hn tn (by norm_num)).2.1.mono (by norm_num))
    (fun _ => (t_small (k := 0) (by norm_num) (by omega)).mono (by norm_num))

/-- **The tier of a leaf bit** (`cubeBitT`): `1`, on the code (of tier `1`) of a state of the
invariant, at a bit index of any tier. -/
theorem tm_cubeBitT (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    (hE : Ext L E [par]) {nT kT : Term} {st : St} {dk : ℕ} (hn : Val w E nT (S.code st))
    (tn : Tm w L 1 nT E) (hinv : S.CubeInv D A B st) (tk : Tm w L dk kT E) :
    Tm w L 1 (cubeBitT T.BT nT kT) E := by
  have hL := hG.hL
  have h := hG.ein hI hE hn tn
  obtain ⟨l, hl, hlen⟩ := code_enc S st
  have g0 := val_stGetT hn 0
  have t0 := (h.field hl 0 hlen).2
  have c0 : Tm w L 1 (const 0) E := t_small (by norm_num) (by omega)
  have c1 : Tm w L 1 (const 1) E := t_one (by omega)
  have c2 : Tm w L 1 (const 2) E := t_small (by norm_num) (by omega)
  unfold cubeBitT
  refine tm_ite2v (val_eqT g0 (val_const 1)) (t_eqT' t0 c1 (by omega)) (fun hp => ?_) (fun _ => ?_)
  · obtain ⟨z, rfl⟩ := lit_of_tag S (ind_of_pos' hp)
    have f1 : Val w E (stGetT nT 1) (zz z) ∧ Tm w L 1 (stGetT nT 1) E := h.field rfl 1 (by simp)
    unfold litBitT
    exact tm_ite (t_eqT' (t_mod_left f1.2 c2) c0 (by omega)) (t_bit (t_div f1.2 c2) tk (by omega))
      (t_sub c1 (t_bit (t_div (t_sub f1.2 c1) c2) tk (by omega)))
  · exact tm_ite2v (val_inRangeT g0 7 9) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
      (fun hp => t_bit (tm_tr_info S (trInv_of_tag hinv (ind_of_pos' hp)) (hI.vB.up (ext_above hE))
        (hG.tB.ext hE) hG.hBL (by omega) hn tn (by norm_num)).2.2 tk (by omega)) (fun _ => c0)

/-! ### Children -/

/-- **The tier of the child of a first-clique factor range** (`rng0ChildT`): `1`, under a bound
`2^L` on its value, for a node `v < 2K` and an index of tier `1`. -/
theorem tm_rng0ChildT (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    (hE : Ext L E [par]) {nT iT : Term} {v args lo hi i : ℕ}
    (hn : Val w E nT (S.code (.rng0 v args lo hi))) (tn : Tm w L 1 nT E) (hv : v < 2 * S.K)
    (hiv : Val w E iT i) (ti : Tm w L 1 iT E)
    (hc : (rng0ChildT (f0T T) nT iT).denote w E < 2 ^ (1 * L)) :
    Tm w L 1 (rng0ChildT (f0T T) nT iT) E := by
  have hL := hG.hL
  have h := hG.ein hI hE hn tn
  have e : S.code (.rng0 v args lo hi) = NatList.enc [6, S.cacheC [], v, args, lo, hi] := rfl
  have f1 : Val w E (stGetT nT 1) (S.cacheC []) ∧ Tm w L 1 (stGetT nT 1) E := h.field e 1 (by simp)
  have f2 : Val w E (stGetT nT 2) v ∧ Tm w L 1 (stGetT nT 2) E := h.field e 2 (by simp)
  have f3 : Val w E (stGetT nT 3) args ∧ Tm w L 1 (stGetT nT 3) E := h.field e 3 (by simp)
  have f4 : Val w E (stGetT nT 4) lo ∧ Tm w L 1 (stGetT nT 4) E := h.field e 4 (by simp)
  have f5 : Val w E (stGetT nT 5) hi ∧ Tm w L 1 (stGetT nT 5) E := h.field e 5 (by simp)
  have c0 : Tm w L 1 (const 0) E := t_small (by norm_num) (by omega)
  have c2 : Tm w L 1 (const 2) E := t_small (by norm_num) (by omega)
  have vmid := val_div (val_add f4.1 f5.1) (val_const 2)
  have hlo := f4.2.lt
  rw [f4.1.2] at hlo
  have hhi := f5.2.lt
  rw [f5.1.2] at hhi
  have tmid : Tm w L 1 (div (add (stGetT nT 4) (stGetT nT 5)) (const 2)) E :=
    tm_val (t_div (t_add f4.2 f5.2 (by omega) (by norm_num)) c2) vmid (by omega)
  have mk : ∀ {a : Term} {A' : ℕ}, Val w E a A' → Tm w L 1 a E →
      (f0T T (stGetT nT 2) (stGetT nT 3) a).denote w E < 2 ^ (1 * L) →
      Tm w L 1 (f0T T (stGetT nT 2) (stGetT nT 3) a) E := fun ha ta hb' => by
    have hv0 := val_f0T hI (ext_above hE) f2.1 f3.1 ha
    rw [hv0.2] at hb'
    exact tm_val (tm_f0T hG hI hE f2.1 f2.2 hv f3.1 (f3.2.mono (by norm_num)) ha ta) hv0 hb'
  have mkR : ∀ {a b : Term} {A' B' : ℕ}, Val w E a A' → Val w E b B' → Tm w L 1 a E →
      Tm w L 1 b E →
      (encE [const 6, stGetT nT 1, stGetT nT 2, stGetT nT 3, a, b]).denote w E < 2 ^ (1 * L) →
      Tm w L 1 (encE [const 6, stGetT nT 1, stGetT nT 2, stGetT nT 3, a, b]) E :=
    fun ha hb ta tb hv' => tm_encD le_rfl (by norm_num) (by omega)
      (.cons ⟨val_const 6, 1, t_const (lit16 (by norm_num) (by omega))⟩ (.cons ⟨f1.1, 1, f1.2⟩
        (.cons ⟨f2.1, 1, f2.2⟩ (.cons ⟨f3.1, 1, f3.2⟩ (.cons ⟨ha, 1, ta⟩
          (.cons ⟨hb, 1, tb⟩ .nil)))))) hv'
  unfold rng0ChildT at hc ⊢
  refine tm_iteD (val_eqT hiv (val_const 0)) (t_eqT' ti c0 (by omega)) (fun _ hb => ?_)
    (fun _ hb => ?_) hc
  · exact tm_rangeT f4.1 vmid f4.2 tmid (by norm_num) (fun _ _ hv' => mk f4.1 f4.2 hv')
      (fun _ hv' => mkR f4.1 vmid f4.2 tmid hv') le_rfl (by norm_num) (by omega) hb
  · exact tm_rangeT vmid f5.1 tmid f5.2 (by norm_num) (fun _ _ hv' => mk vmid tmid hv')
      (fun _ hv' => mkR vmid f5.1 tmid f5.2 hv') le_rfl (by norm_num) (by omega) hb

/-- **The tier of the child of an entry state** (`eChildT` with the leaf factors `f0T T`): `1`,
when the code of the child is below `2^L`. As `tm_eChildT` of `EntryTerm3.lean`, with the tier of
the leaf factors supplied at the entries (whose nodes are below `2K`). -/
theorem tm_eChildT_cube (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) (hE : Ext L E [par]) {nT iT : Term} {st : St}
    {i : ℕ} (hn : Val w E nT (S.code st)) (tn : Tm w L 1 nT E) (hst : EntrySt st)
    (hinv : S.Inv D st) (hiv : Val w E iT i) (ti : Tm w L 1 iT E)
    (hc : S.code (S.gen.child st i) < 2 ^ (1 * L)) :
    Tm w L 1 (eChildT T.fwT T.BT T.KT T.N.VT T.N.MT (f0T T) nT iT) E := by
  have hL := hG.hL
  have h := hG.ein hI hE hn tn
  have hE' := ext_above hE
  have hZ := hG.sizeOK
  have c2 : Tm w L 1 (const 2) E := t_small (by norm_num) (by omega)
  have c3 : Tm w L 1 (const 3) E := t_small (by norm_num) (by omega)
  have c4 : Tm w L 1 (const 4) E := t_const (lit16 (by norm_num) (by omega))
  unfold eChildT
  cases st with
  | cl chs =>
    have f0 := h.field (code_cl S chs) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
      (fun _ => tm_clChildT h hinv hZ hiv ti le_rfl (by norm_num) hc) (fun h0 => by simp at h0)
  | last chs j =>
    have f0 := h.field (code_last S chs j) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 3)) (t_eqT' f0.2 c3 (by omega))
        (fun _ => tm_lastChildD h hiv ti le_rfl (by norm_num) hc) (fun h0 => by simp at h0))
  | ent chs v args =>
    have f0 := h.field (code_ent S chs v args) 0 (by simp)
    have f3 : Val w E (stGetT nT 3) v ∧ Tm w L 1 (stGetT nT 3) E :=
      h.field (code_ent S chs v args) 3 (by simp)
    have f4 : Val w E (stGetT nT 4) args ∧ Tm w L 1 (stGetT nT 4) E :=
      h.field (code_ent S chs v args) 4 (by simp)
    have hv : v < 2 * S.K := lt_of_lt_of_le hinv.2 (q_le_first S chs hinv.1)
    have hA := hI.hA.up hE'
    have tT := hG.hT.up hE
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 3)) (t_eqT' f0.2 c3 (by omega))
        (fun h0 => by simp at h0)
        (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega))
          (fun _ => tm_entChildT h hinv hZ (hI.vK.up hE') hA.vV hA.vM (hG.tK.ext hE) tT.tV tT.tM
            (fun _ _ _ _ _ _ ha hb hc => val_f0T hI hE' ha hb hc) (f0C_eq S hG.hS hG.hnn)
            (fun _ _ hf
                tf => ⟨9, tm_f0T hG hI hE f3.1 f3.2 hv f4.1 (f4.2.mono (by norm_num)) hf tf⟩)
            hiv ti le_rfl (by norm_num) hc)
          (fun h0 => by simp at h0)))
  | rng chs v args ξ lo hb =>
    have f0 := h.field (code_rng S chs v args ξ lo hb) 0 (by simp)
    exact tm_ite2v (val_eqT f0.1 (val_const 2)) (t_eqT' f0.2 c2 (by omega))
        (fun h0 => by simp at h0)
      (fun _ => tm_ite2v (val_eqT f0.1 (val_const 3)) (t_eqT' f0.2 c3 (by omega))
        (fun h0 => by simp at h0)
        (fun _ => tm_ite2v (val_eqT f0.1 (val_const 4)) (t_eqT' f0.2 c4 (by omega))
          (fun h0 => by simp at h0)
              (fun _ => tm_rngChildT h hinv hZ hiv ti le_rfl (by norm_num) hc)))
  | _ => exact hst.elim

/-- **The tier of the child** (`cubeChildT`): `1`, on the code (of tier `1`) of a state of the
invariant, at an index of tier `1`, when the code of the child is below `2^L`. -/
theorem tm_cubeChildT (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    (hE : Ext L E [par]) {nT iT : Term} {st : St} {i : ℕ} (hn : Val w E nT (S.code st))
    (tn : Tm w L 1 nT E) (hinv : S.CubeInv D A B st) (hiv : Val w E iT i) (ti : Tm w L 1 iT E)
    (hc : S.code (S.gen.child st i) < 2 ^ L) :
    Tm w L 1 (cubeChildT T.fwT T.BT T.KT T.N.VT T.N.MT (f0T T) nT iT) E := by
  have hL := hG.hL
  have hE' := ext_above hE
  have hA := hI.hA.up hE'
  have h := hG.ein hI hE hn tn
  obtain ⟨l, hl, hlen⟩ := code_enc S st
  have g0 := val_stGetT hn 0
  have t0 := (h.field hl 0 hlen).2
  have hc1 : S.code (S.gen.child st i) < 2 ^ (1 * L) := by rwa [one_mul]
  have vch := val_cubeChildT (hI.vfw.up hE') (hI.vB.up hE') (hI.vK.up hE') hA.vV hA.vM hn hiv
    (f0T := f0T T) (fun _ _ _ _ _ _ ha hb hc => val_f0T hI hE' ha hb hc)
  have hden : (cubeChildT T.fwT T.BT T.KT T.N.VT T.N.MT (f0T T) nT iT).denote w E <
      2 ^ (1 * L) := by
    rw [vch.2, (cube_local S hG.hS hG.he hG.hA hG.hB (f0C_eq S hG.hS hG.hnn) st hinv).2.2.2 i]
    exact hc1
  unfold cubeChildT at hden ⊢
  refine tm_iteD (val_inRangeT g0 2 5) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
    (fun hp _ => tm_eChildT_cube hG hI hE hn tn (entrySt_of_tag S (ind_of_pos' hp)) hinv.1 hiv ti
      hc1) (fun _ hb => ?_) hden
  refine tm_iteD (val_eqT g0 (val_const 6))
    (t_eqT' t0 (t_const (lit16 (by norm_num) (by omega))) (by omega)) (fun hp hb' => ?_)
    (fun _ hb' => ?_) hb
  · obtain ⟨v, args, lo, hi, rfl⟩ := rng0_of_tag S (ind_of_pos' hp)
    exact tm_rng0ChildT hG hI hE hn tn hinv.2 hiv ti hb'
  · exact tm_iteD (val_inRangeT g0 7 9) (tm_inRangeT t0 hL (by norm_num) (by norm_num))
      (fun hp _ => (tm_tr_agree S (trInv_of_tag hinv (ind_of_pos' hp)) (hI.vB.up hE')
        (hG.tB.ext hE) hG.hBL (by omega) hn tn (by norm_num) hiv ti le_rfl (by norm_num)
        hc1).2.2.2)
      (fun _ hb'' => tm_zeroCT le_rfl (by norm_num) (by omega) hb'') hb'

/-! ### At the environments of the evaluator -/

theorem small_of_lt {x : ℕ} (hx : x < 2 ^ L) : x < 2 ^ (32 * L) :=
  hx.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem ext_one {x : ℕ} (hx : x < 2 ^ L) : Ext L [x, par] [par] :=
  ⟨[x], Small.cons (small_of_lt hx) Small.nil, rfl⟩

theorem ext_two {x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L) : Ext L [x, y, par] [par] :=
  ⟨[x, y], Small.cons (small_of_lt hx) (Small.cons (small_of_lt hy) Small.nil), rfl⟩

theorem tm_at {e : List ℕ} {l : ℕ} (hl : l < e.length) (hx : e.getD (e.length - l - 1) 0 < 2 ^ L) :
    Tm w L 1 (lvl l) e := tm_lvl hl (by rw [one_mul]; exact hx)

/-- The tag program at `[code st, par]`, for a reached state of the invariant. -/
theorem tm_cubeTag_at (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    {st : St} (hR : S.Reach st) (hinv : S.CubeInv D A B st) :
    Tm w L 1 (cubeTagT T.BT T.fwT (lvl 1)) [S.code st, par] :=
  tm_cubeTagT hG hI (ext_one (hG.hcode st hR)) (val_lvl_at (by simp))
    (tm_at (by simp) (hG.hcode st hR)) hinv

/-- The width program at `[code st, par]`, for a reached state of the invariant. -/
theorem tm_cubeWidth_at (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {st : St} (hR : S.Reach st)
    (hinv : S.CubeInv D A B st) : Tm w L 7 (cubeWidthT T.BT T.fwT (lvl 1)) [S.code st, par] :=
  tm_cubeWidthT hG hI (ext_one (hG.hcode st hR)) (val_lvl_at (by simp))
    (tm_at (by simp) (hG.hcode st hR)) hinv

/-- The bit program at `[k, code st, par]`, for a reached state of the invariant and `k < 2^L`. -/
theorem tm_cubeBit_at (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H)
    {st : St} {k : ℕ} (hR : S.Reach st) (hinv : S.CubeInv D A B st) (hk : k < 2 ^ L) :
    Tm w L 1 (cubeBitT T.BT (lvl 1) (lvl 2)) [k, S.code st, par] :=
  tm_cubeBitT hG hI (ext_two hk (hG.hcode st hR)) (val_lvl_at (by simp))
    (tm_at (by simp) (hG.hcode st hR)) hinv (tm_at (by simp) hk)

/-- The child program at `[code st, i, par]`, for a reached state of the invariant, `i < 2^L` and
a child code below `2^L`. -/
theorem tm_cubeChild_at (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {st : St} {i : ℕ} (hR : S.Reach st)
    (hinv : S.CubeInv D A B st) (hi : i < 2 ^ L) (hc : S.code (S.gen.child st i) < 2 ^ L) :
    Tm w L 1 (cubeChildT T.fwT T.BT T.KT T.N.VT T.N.MT (f0T T) (lvl 2) (lvl 1))
      [S.code st, i, par] :=
  tm_cubeChildT hG hI (ext_two (hG.hcode st hR) hi) (val_lvl_at (by simp))
    (tm_at (by simp) (hG.hcode st hR)) hinv (val_lvl_at (by simp)) (tm_at (by simp) hi) hc

/-- **The tier of the root code** (`initT`): `1`. -/
theorem tm_initT (hG : CubeTiers S w L par T D A B) (hI : CubeIn S.G w par T S.P B S.fw S.K H) :
    Tm w L 1 (initT T) [par] := by
  have hL := hG.hL
  have vK := hI.vK
  have vq : Val w [par] (mul (const 2) T.KT) (2 * S.K) := val_mul (val_const 2) vK
  have tq : Tm w L 1 (mul (const 2) T.KT) [par] :=
    tm_val (t_mul (t_small (k := 2) (by norm_num) (by omega)) hG.tK (by norm_num)) vq
      (lt_tier_one hG.hqL.le)
  have hC : Fits S.fw (firstBudget S.G S.K) := fits_path S hG.hS (chs := []) trivial
  have va := val_firstArrT hI.hA vK vq hI.vfw
  have ta := tm_firstArrT (d := 1) hI.hA hG.hT vK hG.tK hG.hK1 vq tq hI.vfw hG.tfw hG.hfw hC
    (by rw [one_mul]; exact hG.hArr) le_rfl (by norm_num)
  have v1 := val_encE (w := w) (env := [par]) (.cons vq (.cons va .nil))
  have v2 := val_encE (w := w) (env := [par]) (.cons v1 .nil)
  have v3 := val_encE (w := w) (env := [par])
    (.cons (val_const 2) (.cons (val_const 1) (.cons v2 .nil)))
  have heq : NatList.enc [2, 1, NatList.enc [NatList.enc [2 * S.K,
      arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))]]] = S.code (.cl []) :=
    v3.2.symm.trans (val_initT S hI (Above.refl _)).2
  have b3 : NatList.enc [2, 1, NatList.enc [NatList.enc [2 * S.K,
      arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))]]] < 2 ^ (1 * L) := by
    rw [one_mul, heq]; exact hG.hcode _ Setup.Reach.root
  have b2 : NatList.enc [NatList.enc [2 * S.K,
      arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))]] < 2 ^ (1 * L) :=
    (le_enc_of_mem (by simp)).trans_lt b3
  have b1 : NatList.enc [2 * S.K, arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))] < 2 ^ (1 * L) :=
    (le_enc_of_mem (by simp)).trans_lt b2
  have t1 := tm_encE (w := w) le_rfl (by norm_num) (by omega)
      (.cons ⟨vq, 1, tq⟩ (.cons ⟨va, 1, ta⟩ .nil)) b1
  have t2 := tm_encE (w := w) le_rfl (by norm_num) (by omega) (.cons ⟨v1, 1, t1⟩ .nil) b2
  exact tm_encE le_rfl (by norm_num) (by omega)
      (.cons ⟨val_const 2, 1, t_small (by norm_num) (by omega)⟩
    (.cons ⟨val_const 1, 1, t_one (by omega)⟩ (.cons ⟨v2, 1, t2⟩ .nil))) b3

/-! ### The closed programs -/

theorem cubeProg_init_bnd (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) :
    (cubeProg T).init.Bounded w (2 ^ (128 * L)) [par] :=
  (Exact.bounded_closeAt _ 1 _ rfl).mpr (tm_initT hG hI).bnd

theorem cubeProg_fuel_bnd (hG : CubeTiers S w L par T D A B) :
    (cubeProg T).fuel.Bounded w (2 ^ (128 * L)) [par] :=
  (Exact.bounded_closeAt _ 1 _ rfl).mpr hG.tH.bnd

theorem cubeProg_tag_bnd (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {st : St} (hR : S.Reach st)
    (hinv : S.CubeInv D A B st) : (cubeProg T).tag.Bounded w (2 ^ (128 * L)) [S.code st, par] :=
  (Exact.bounded_closeAt _ 2 _ rfl).mpr (tm_cubeTag_at hG hI hR hinv).bnd

theorem cubeProg_prec_bnd (hG : CubeTiers S w L par T D A B) {st : St} (hR : S.Reach st) :
    (cubeProg T).prec.Bounded w (2 ^ (128 * L)) [S.code st, par] :=
  (Exact.bounded_closeAt _ 2 _ rfl).mpr (hG.tP.ext (ext_one (hG.hcode st hR))).bnd

theorem cubeProg_param_bnd (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {st : St} (hR : S.Reach st)
    (hinv : S.CubeInv D A B st) : (cubeProg T).param.Bounded w (2 ^ (128 * L)) [S.code st, par] :=
  (Exact.bounded_closeAt _ 2 _ rfl).mpr (tm_cubeWidth_at hG hI hR hinv).bnd

theorem cubeProg_bit_bnd (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {st : St} {k : ℕ} (hR : S.Reach st)
    (hinv : S.CubeInv D A B st) (hk : k < 2 ^ L) :
    (cubeProg T).bit.Bounded w (2 ^ (128 * L)) [k, S.code st, par] :=
  (Exact.bounded_closeAt _ 3 _ rfl).mpr (tm_cubeBit_at hG hI hR hinv hk).bnd

theorem cubeProg_child_bnd (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {st : St} {i : ℕ} (hR : S.Reach st)
    (hinv : S.CubeInv D A B st) (hi : i < 2 ^ L) (hc : S.code (S.gen.child st i) < 2 ^ L) :
    (cubeProg T).child.Bounded w (2 ^ (128 * L)) [S.code st, i, par] :=
  (Exact.bounded_closeAt _ 3 _ rfl).mpr (tm_cubeChild_at hG hI hR hinv hi hc).bnd

theorem valid_drop {t : SPTree} : ∀ {π : List ℕ}, SPTree.Valid t π → ∀ j, SPTree.Valid t (π.drop j)
  | [], _, _ => by simp
  | _ :: _, h, 0 => h
  | _ :: π, h, j + 1 => by rw [List.drop_succ_cons]; exact valid_drop h.1 j

/-- **The state before a valid step** of a path: the code of a reached state of the invariant whose
child at the step has a code below `2^L`. -/
theorem cubeProg_stepState (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) {i : ℕ} {ρ : List ℕ}
    (hρ : SPTree.Valid ((cubeProg T).tree w par) (i :: ρ)) :
    ∃ st, ((cubeProg T).toFun w par).stateAt ((cubeProg T).init₀ w par) ρ = S.code st ∧
      S.Reach st ∧ S.CubeInv D A B st ∧ S.code (S.gen.child st i) < 2 ^ L := by
  rw [GenProg.tree, cubeProg_toFun S hI, cubeProg_init S hI] at hρ
  rw [cubeProg_toFun S hI, cubeProg_init S hI]
  obtain ⟨st, st', h1, h2, h3, h3', h4⟩ := S.gen.path_step
    (cube_agrees S hG.hS hG.he hG.hA hG.hB (f0C_eq S hG.hS hG.hnn)) S.Reach
    (fun st hR hk i hi => Setup.Reach.sum st i hR hk hi)
    (fun st hR hk b hb => Setup.Reach.prod st b hR hk hb) _ (S.cubeInv_root hG.he) Setup.Reach.root
    i ρ hρ
  refine ⟨st, h1, h3, h2, ?_⟩
  rw [h4]
  exact hG.hcode st' h3'

/-- **The value bounds along a valid path** (`GenProg.PathBounded`) at `2^(128 L)`, for a path
whose code fits the bound and whose indices are below `2^L`. -/
theorem cubeProg_pathBounded (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) (π : List ℕ)
    (hπ : SPTree.Valid ((cubeProg T).tree w par) π)
    (hcodeπ : max (NatList.enc π) 8 + 1 ≤ 2 ^ (128 * L)) (hidx : ∀ i ∈ π, i < 2 ^ L) :
    (cubeProg T).PathBounded (w := w) par (2 ^ (128 * L)) π where
  code := hcodeπ
  init := cubeProg_init_bnd hG hI
  fuel := cubeProg_fuel_bnd hG
  child j hj := by
    have hd : π.drop j = π[j]! :: π.drop (j + 1) := by
      rw [getElem!_pos π j hj]; exact List.drop_eq_getElem_cons hj
    have hv := valid_drop hπ j
    rw [hd] at hv
    obtain ⟨st, h1, h2, h3, h4⟩ := cubeProg_stepState hG hI hv
    rw [h1]
    exact cubeProg_child_bnd hG hI h2 h3
      (hidx _ (by rw [getElem!_pos π j hj]; exact List.getElem_mem hj)) h4
  tag := by
    obtain ⟨st, h1, h2, h3⟩ := cubeProg_pathState S hG.hS hG.he hG.hA hG.hB hG.hnn hI π hπ
    rw [h1]; exact cubeProg_tag_bnd hG hI h2 h3
  prec := by
    obtain ⟨st, h1, h2, -⟩ := cubeProg_pathState S hG.hS hG.he hG.hA hG.hB hG.hnn hI π hπ
    rw [h1]; exact cubeProg_prec_bnd hG h2
  param := by
    obtain ⟨st, h1, h2, h3⟩ := cubeProg_pathState S hG.hS hG.he hG.hA hG.hB hG.hnn hI π hπ
    rw [h1]; exact cubeProg_param_bnd hG hI h2 h3

/-- **The leaf bits along a valid path** are bounded by `2^(128 L)` at every bit index `k < 2^L`. -/
theorem cubeProg_bitBounded (hG : CubeTiers S w L par T D A B)
    (hI : CubeIn S.G w par T S.P B S.fw S.K H) (π : List ℕ)
    (hπ : SPTree.Valid ((cubeProg T).tree w par) π) {k : ℕ} (hk : k < 2 ^ L) :
    (cubeProg T).bit.Bounded w (2 ^ (128 * L))
      [k, ((cubeProg T).toFun w par).stateAt ((cubeProg T).init₀ w par) π, par] := by
  obtain ⟨st, h1, h2, h3⟩ := cubeProg_pathState S hG.hS hG.he hG.hA hG.hB hG.hnn hI π hπ
  rw [h1]; exact cubeProg_bit_bnd hG hI h2 h3 hk

end Tiers

end Num

end Cslib.Complexity.NtimeDspace.Cube
