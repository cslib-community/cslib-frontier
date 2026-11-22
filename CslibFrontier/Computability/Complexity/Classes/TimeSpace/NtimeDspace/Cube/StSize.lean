/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Paths

/-!
# The sizes of the states (proof of Lemma 6.4)

The machine of Lemma 6.4 follows an address from the root and keeps the code `Setup.code st` of one
state. This module bounds these codes: in the setting of Lemma 6.3 every state reached from the root
along valid indices has a code of `O(s / √log s)` bits (`state_size`), as in the appendix proof of
Lemma 6.4 ("since `q_*² ≤ s^{2/3}`, the total workspace is `O(F)`").

* `Setup.Reach`: the states reached from the root `cl []` through the children `i < 2^width` of sum
  nodes and the children `0, 1` of product nodes.
* `Setup.Ext`: the extra invariant of the reached states, beside `Setup.Inv` (`Sound.lean`) and
  `Setup.inv` (`PathsAux.lean`): the choice codes of the path fit their index lengths
  (`Setup.PathW`), a last label code has at most `Λ` bits, argument codes at most `Λ + Ξ` bits and
  codes of copies at most `Ξ` bits, the labels of a transport state weigh at most `Wm` in total,
  literals are bounded by the bound `Ev` on the vertex functions, and the exponents of the transport
  recursion satisfy `|c| + 4 W ≤ Kc` with `W` the weight of the subproblem. `Setup.reach_inv`.
* `Setup.code_lt`: then every field of the code of a reached state is below `2^N` for any `N`
  above the descent and the cache (`O(log h_* · q_*² log s)` bits), the codes of labels and
  multisets of targets of weight `Wm` (`O(√Wm)` bits), `Λ + Ξ`, and the bit size of a polynomial
  bound on the counters, so the code is below `2^(28 N + 15)`.
* `state_size`: the asymptotics, `N = O(s / √log s)`. The vertex functions are assumed to take
  values of absolute value at most `(s + 2)^C₁` (Definition 2.1 (a) of
  `separating-ntime-from-space.tex`), since their
  values appear as literals of the formula.

## Main results

* `Setup.reach_inv`: the invariants of the reached states.
* `Setup.reach_cubeInv`: the reached states satisfy `Setup.CubeInv` of the numeric generator
  (`GenNum.lean`) with `A = 2 Wm + 1`, `B = w(A)`.
* `Setup.code_lt`: the code of a reached state is below `2^(28 N + 15)`.
* `state_size`: the code of a reached state has `O(s / √log s)` bits.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

open SumProduct.NatList (elen elen_cons enc_lt)

/-! ### Reached states and the extra invariant -/

namespace Setup

variable (S : Setup)

/-- **The states reached from the root** along valid indices: the root `cl []`, the children
`i < 2^width` of sum nodes, and the children `0, 1` of product nodes. -/
inductive Reach (S : Setup) : St → Prop
  | root : Reach S (.cl [])
  | sum (st : St) (i : ℕ) : Reach S st → S.gen.kind st = .sum → i < 2 ^ S.gen.width st →
      Reach S (S.gen.child st i)
  | prod (st : St) (b : ℕ) : Reach S st → S.gen.kind st = .prod → b < 2 →
      Reach S (S.gen.child st b)

/-- The choice codes of a path fit their index lengths. -/
def PathW : List ℕ → Prop
  | [] => True
  | i :: rest => PathW rest ∧ i < 2 ^ choiceWidth (Nat.sqrt (S.clique rest).q) S.fw

/-- **The extra invariant of the reached states**: the indices read on the path fit their index
lengths, the labels of a transport state weigh at most `Wm`, literals are at most `Ev` in absolute
value, and the exponents of the transport recursion satisfy `|c| + 4 W ≤ Kc`. -/
def Ext (π : BudPar) (Ev Kc : ℕ) : St → Prop
  | .zero => True
  | .lit w => |w| ≤ (Ev : ℤ)
  | .cl chs => S.PathW chs
  | .last chs i => S.PathW chs ∧ i < 2 ^ π.Λ
  | .ent chs _ args => S.PathW chs ∧ args < 2 ^ (π.Λ + π.Ξ)
  | .rng chs _ args ξ _ _ => S.PathW chs ∧ args < 2 ^ (π.Λ + π.Ξ) ∧ ξ < 2 ^ π.Ξ
  | .rng0 v args _ hi => v < S.C₀.q ∧ hi ≤ S.nFac0 v ∧ args < 2 ^ (π.Λ + π.Ξ)
  | .tr up x y m lo hi T c => labelWt x + labelWt y + labelWt m ≤ π.Wm ∧
      |c| + 4 * (tWt (srcSub up x y m lo hi) T : ℤ) ≤ Kc
  | .trm up x y m lo ν hi t T₁ T₂ c₁ c₀ c₂ => labelWt x + labelWt y + labelWt m ≤ π.Wm ∧
      t.2 ≤ Kc ∧ |c₁| + 4 * (tWt (srcSub up x y m lo ν) T₁ : ℤ) ≤ Kc ∧ |c₀| ≤ (Kc : ℤ) ∧
      |c₂| + 4 * (tWt (srcSub up x y m (ν + 1) hi) T₂ : ℤ) ≤ Kc ∧ ValidPl up t.1
  | .trr up x y m ν hi t T₂ c₀ c₂ => labelWt x + labelWt y + labelWt m ≤ π.Wm ∧
      t.2 ≤ Kc ∧ |c₀| ≤ (Kc : ℤ) ∧ |c₂| + 4 * (tWt (srcSub up x y m (ν + 1) hi) T₂ : ℤ) ≤ Kc ∧
      ValidPl up t.1

/-- A state is in `Ext` if it is in the invariant `inv`. -/
def FE (π : BudPar) (Ev Kc : ℕ) (st : St) : Prop := S.inv π st → S.Ext π Ev Kc st

end Setup

/-! ### Small facts -/

theorem abs_add_le_iff {a b K : ℤ} : |a| + b ≤ K ↔ a + b ≤ K ∧ -a + b ≤ K := by
  rw [← le_sub_iff_add_le, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem abs_field_le (fw i t : ℕ) : |field fw i t| ≤ 2 ^ fw := by
  unfold field
  have h1 := Nat.mod_lt (i / 2 ^ (t * fw)) (show 0 < 2 ^ fw by positivity)
  generalize (i / 2 ^ (t * fw)) % 2 ^ fw = n at h1 ⊢
  have h1' : (n : ℤ) < 2 ^ fw := by exact_mod_cast h1
  have h2 : (2 : ℤ) ^ (fw - 1) ≤ 2 ^ fw := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.sub_le fw 1)
  have h3 : (0 : ℤ) ≤ 2 ^ (fw - 1) := by positivity
  have h4 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]
  constructor <;> linarith

theorem zz_le {w : ℤ} {K : ℕ} (h : |w| ≤ K) : Num.zz w ≤ 2 * K := by
  rw [abs_le] at h
  unfold Num.zz
  split_ifs <;> omega

theorem slice_le (C : Clique) (nodes : ℕ → ℕ) (ξ p : ℕ) : slice C nodes ξ p ≤ ξ :=
  (Nat.mod_le _ _).trans (Nat.div_le_self _ _)

theorem length_srcList_le (up : Bool) (x y m : Label) :
    (srcList up x y m).length ≤ labelWt x + labelWt y + labelWt m := by
  rw [← tWt_srcList up x y m]
  exact length_le_tWt _ _

theorem abs_chi (i j : ℕ) : |chi i j| = 1 := abs_neg_one_pow _

theorem abs_ite_chi_le (p : Prop) [Decidable p] (i j : ℕ) : |(if p then chi i j else 0)| ≤ 1 := by
  split_ifs <;> simp [abs_chi]

theorem abs_ite_sub_le {p q : Prop} [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) (i j : ℕ) :
    |(if p then chi i j else 0) - (if q then chi i j else 0)| ≤ 1 := by
  split_ifs with hp hq
  · exact absurd ⟨hp, hq⟩ h
  all_goals simp [abs_chi]

/-- Every coefficient of a half-rule is `0` or `±1`. -/
theorem abs_coeff_hRule_le (up : Bool) (p : HPlace) (i : ℕ) (q : HPlace) (j : ℕ) (c : ℤ) :
    |(hRule up p i q j).coeff c| ≤ 1 := by
  have h1 : ∀ i j, |(Cube.C i j).coeff c| ≤ 1 := fun i j => by
    rw [Num.coeff_cubeC]; exact abs_ite_chi_le _ i j
  have h2 : ∀ i j, |(bar (Cube.C i j)).coeff c| ≤ 1 := fun i j => by
    rw [Num.coeff_bar_cubeC]; exact abs_ite_chi_le _ i j
  have h3 : ∀ i j, |(oneSubZ2 * Cube.C i j).coeff c| ≤ 1 := fun i j => by
    rw [Num.coeff_oneSubZ2_cubeC]; exact abs_ite_sub_le (by omega) i j
  have h4 : ∀ i j, |(oneSubZm2 * bar (Cube.C i j)).coeff c| ≤ 1 := fun i j => by
    rw [Num.coeff_oneSubZm2_bar]; exact abs_ite_sub_le (by omega) i j
  have h5 : ∀ i j, |(eqL i j).coeff c| ≤ 1 := fun i j => by
    rw [Num.coeff_eqL]; split_ifs <;> simp
  have h0 : |(0 : Lp).coeff c| ≤ 1 := by rw [Num.coeff_zero_Lp]; simp
  cases up <;> rcases p with _ | ⟨_ | _ | _ | _⟩ <;> rcases q with _ | ⟨_ | _ | _ | _⟩ <;>
    simp (config := { decide := true }) only [hRule, upRule, downRule, ↓reduceIte, h0, h1, h2, h3,
      h4, h5]

/-! ### Bounds on codes -/

theorem elen_le_of_lt {l : List ℕ} {N : ℕ} (h : ∀ x ∈ l, x < 2 ^ N) :
    elen l ≤ l.length * (2 * N + 1) + 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [elen_cons, List.length_cons]
    have hx : x.size ≤ N := Nat.size_le.mpr (h x List.mem_cons_self)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    nlinarith

theorem enc_lt_of_lt {l : List ℕ} {N : ℕ} (h : ∀ x ∈ l, x < 2 ^ N) :
    SumProduct.NatList.enc l < 2 ^ (l.length * (2 * N + 1) + 1) :=
  (enc_lt l).trans_le (Nat.pow_le_pow_right (by norm_num) (elen_le_of_lt h))

theorem enc_lt_of_mem {l : List ℕ} {N : ℕ} (hl : l.length ≤ 14) (h : ∀ x ∈ l, x < 2 ^ N) :
    SumProduct.NatList.enc l < 2 ^ (14 * (2 * N + 1) + 1) :=
  (enc_lt_of_lt h).trans_le (Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1))

theorem lcode_lt {A : ℕ} {l : Label} (hl : labelWt l ≤ A) : lcode l < 2 ^ codeWidth (A + 1) := by
  rw [← labelCode_eq_lcode (by omega : A + 1 ≠ 0)]
  exact labelCode_lt (by omega)

theorem mcode_lt {A : ℕ} {σ : Multiset ℕ} (h : wt σ ≤ A) : mcode σ < 2 ^ codeWidth (A + 1) :=
  (ofBits_lt _).trans_le (Nat.pow_le_pow_right (by norm_num)
    (Num.msCode_length_le_of_wt (by omega) (by omega)))

theorem tcode_lt {A : ℕ} (up : Bool) {T : Multiset (HPlace × ℕ)} (h : (T.map lwt).sum ≤ A) :
    tcode up T < 2 ^ (6 * codeWidth (A + 1) + 4) := by
  have := enc_lt_of_lt (l := [mcode (tpart up T 0), mcode (tpart up T 1), mcode (tpart up T 2)])
    (N := codeWidth (A + 1)) (by
      simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨mcode_lt ((Num.wt_tpart_le _ _ _).trans h), mcode_lt ((Num.wt_tpart_le _ _ _).trans h),
        mcode_lt ((Num.wt_tpart_le _ _ _).trans h)⟩)
  refine this.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  simp only [List.length_cons, List.length_nil]
  omega

namespace Setup

variable (S : Setup)

theorem q_le {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) {chs : List ℕ} (h : S.ChainOK e chs) :
    (S.clique chs).q ≤ 2 ^ 2 ^ e := by
  rw [(S.chainOK_facts hq h).2.1]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

/-- The choice codes of a path are below `2^X`, `X = 2 q₀² fw`. -/
theorem pathW_lt {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) : ∀ {chs : List ℕ}, S.ChainOK e chs →
    S.PathW chs → ∀ x ∈ chs, x < 2 ^ (2 * (2 ^ 2 ^ e) ^ 2 * S.fw)
  | [], _, _ => by simp
  | i :: rest, hc, hw => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine hw.2.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
      have h1 : Nat.sqrt (S.clique rest).q ^ 2 ≤ (S.clique rest).q := Nat.sqrt_le' _
      have h2 := S.q_le hq hc.1
      have h3 : Nat.sqrt (S.clique rest).q ^ 4 ≤ (2 ^ 2 ^ e) ^ 2 :=
        calc Nat.sqrt (S.clique rest).q ^ 4 = (Nat.sqrt (S.clique rest).q ^ 2) ^ 2 := by ring
          _ ≤ (2 ^ 2 ^ e) ^ 2 := Nat.pow_le_pow_left (h1.trans h2) 2
      unfold choiceWidth
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    · exact pathW_lt hq hc.1 hw.1 x hx

/-- The budget array of a clique on the path is below `2^(4X + 3)`. -/
theorem arrAt_lt (hS : S.Good) {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) {chs : List ℕ}
    (h : S.ChainOK e chs) : S.arrAt chs < 2 ^ (2 * (2 * (2 * (2 ^ 2 ^ e) ^ 2 * S.fw) + 1) + 1) := by
  have hfw := S.one_le_fw hS
  have hql := S.q_le hq h
  have hq1 : 1 ≤ 2 ^ 2 ^ e := Nat.one_le_two_pow
  have hX : 2 ^ 2 ^ e ≤ 2 * (2 ^ 2 ^ e) ^ 2 * S.fw := by nlinarith
  have hfits : Num.Fits S.fw (S.clique chs).a := by
    intro u v huv
    have h1 := (S.clique chs).a_le_spair huv
    have h2 := S.spair_mul_le hq h
    have h3 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have h4 := hS.2.2
    have h5 : 2 ^ (S.fw - 1) ≤ 2 ^ S.fw := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    nlinarith
  have hA := Num.arrN_lt (Num.Fits.arr hfits)
  have hqq : (S.clique chs).q * (S.clique chs).q * S.fw ≤ 2 * (2 ^ 2 ^ e) ^ 2 * S.fw := by
    have := Nat.mul_le_mul hql hql
    nlinarith
  unfold arrAt
  have := enc_lt_of_lt (l := [(S.clique chs).q,
      Num.arrN (S.clique chs).q S.fw (Num.extN (S.clique chs).a)])
    (N := 2 * (2 ^ 2 ^ e) ^ 2 * S.fw) (by
      simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨(hql.trans hX).trans_lt Nat.lt_two_pow_self,
        hA.trans_le (Nat.pow_le_pow_right (by norm_num) hqq)⟩)
  simpa using this

theorem cacheL_lt (hS : S.Good) {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) : ∀ {chs : List ℕ},
    S.ChainOK e chs → ∀ x ∈ S.cacheL chs,
      x < 2 ^ (2 * (2 * (2 * (2 ^ 2 ^ e) ^ 2 * S.fw) + 1) + 1)
  | [], _ => by
    intro x hx
    simp only [cacheL, List.mem_singleton] at hx
    subst hx
    exact S.arrAt_lt hS hq trivial
  | i :: rest, hc => by
    intro x hx
    simp only [cacheL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact S.arrAt_lt hS hq hc
    · exact cacheL_lt hS hq hc.1 x hx

theorem length_cacheL : ∀ chs : List ℕ, (S.cacheL chs).length = chs.length + 1
  | [] => rfl
  | _ :: rest => by simp only [cacheL, List.length_cons, length_cacheL rest]

theorem abs_factor0_le {Ev : ℕ} (hEv : 1 ≤ Ev) (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ))
    (v args f : ℕ) : |S.factor0 v args f| ≤ (Ev : ℤ) := by
  unfold factor0
  dsimp only
  split_ifs <;> first | exact hev _ _ (by simp) | simp [hEv]

/-! ### The extra invariant along the children -/

theorem fe_ite {π : BudPar} {Ev Kc : ℕ} (c : Prop) [Decidable c] (a b : St)
    (ha : c → S.FE π Ev Kc a) (hb : ¬c → S.FE π Ev Kc b) : S.FE π Ev Kc (if c then a else b) := by
  split_ifs with h
  · exact ha h
  · exact hb h

theorem fe_dite {π : BudPar} {Ev Kc : ℕ} (c : Prop) [Decidable c] (a : c → St) (b : ¬c → St)
    (ha : ∀ h, S.FE π Ev Kc (a h)) (hb : ∀ h, S.FE π Ev Kc (b h)) : S.FE π Ev Kc (dite c a b) := by
  split_ifs with h
  · exact ha h
  · exact hb h

theorem fe_rangeSt {π : BudPar} {Ev Kc : ℕ} (hEv : 1 ≤ Ev) (mk : ℕ → St) (mkR : ℕ → ℕ → St)
    (lo hi : ℕ) (hmk : ∀ f, S.FE π Ev Kc (mk f)) (hR : S.FE π Ev Kc (mkR lo hi)) :
    S.FE π Ev Kc (rangeSt mk mkR lo hi) := by
  unfold rangeSt
  split_ifs
  · intro _
    change |(1 : ℤ)| ≤ (Ev : ℤ)
    simp [hEv]
  · exact hmk lo
  · exact hR

/-- The factors of a table entry. -/
theorem fe_factorSt (π : BudPar) {Ev Kc : ℕ} (hEv : 1 ≤ Ev) (hKc : 2 * 2 ^ S.fw + 4 * π.Wm ≤ Kc)
    {i : ℕ} {rest : List ℕ} (hc : S.ChainOK π.e (i :: rest)) (hpw : S.PathW rest) {v args ξ : ℕ}
    (hξ : ξ < 2 ^ π.Ξ) (f : ℕ) : S.FE π Ev Kc (S.factorSt rest i v args ξ f) := by
  obtain ⟨-, -, hsq, -⟩ := hc
  have htr : ∀ up x y m (c : ℤ), |c| ≤ 2 * 2 ^ S.fw →
      S.FE π Ev Kc (.tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) c) := by
    intro up x y m c hc hinv
    have e1 : srcSub up x y m 0 (srcList up x y m).length = srcList up x y m := by simp [srcSub]
    simp only [inv, e1, tWt_srcList] at hinv
    simp only [Ext, e1, tWt_srcList]
    refine ⟨hinv, ?_⟩
    have h1 : ((labelWt x + labelWt y + labelWt m : ℕ) : ℤ) ≤ π.Wm := by exact_mod_cast hinv
    have h2 : ((2 * 2 ^ S.fw + 4 * π.Wm : ℕ) : ℤ) ≤ Kc := by exact_mod_cast hKc
    push_cast at h1 h2 ⊢
    linarith
  have hι : ∀ r, |(decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1| ≤ 2 ^ S.fw ∧
      |(decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).2| ≤ 2 ^ S.fw :=
    fun r => ⟨abs_field_le _ _ _, abs_field_le _ _ _⟩
  have hsub : ∀ r, |(decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1 -
      (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).2| ≤ 2 * 2 ^ S.fw := fun r => by
    obtain ⟨h1, h2⟩ := hι r
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have hneg : ∀ r, |-(decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1 -
      (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).2| ≤ 2 * 2 ^ S.fw := fun r => by
    obtain ⟨h1, h2⟩ := hι r
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have hsnd : ∀ r, |(decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).2| ≤ 2 * 2 ^ S.fw :=
    fun r => by
      have := (hι r).2
      have h0 : (0 : ℤ) ≤ 2 ^ S.fw := by positivity
      linarith
  have hlit : ∀ (c : Prop) [Decidable c], S.FE π Ev Kc (.lit (if c then 0 else 1)) :=
    fun c _ _ => by
      change |(if c then (0 : ℤ) else 1)| ≤ (Ev : ℤ)
      split_ifs <;> simp [hEv]
  have hl1 : S.FE π Ev Kc (.lit 1) := fun _ => by
    change |(1 : ℤ)| ≤ (Ev : ℤ)
    simp [hEv]
  have z : S.FE π Ev Kc .zero := fun _ => trivial
  have hent : ∀ n x, x ≤ ξ → S.FE π Ev Kc (.ent rest n x) := fun n x hx _ =>
    ⟨hpw, lt_of_le_of_lt hx (hξ.trans_le
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)))⟩
  unfold factorSt
  rw [S.parentGrid_eq rest i hsq]
  dsimp only
  refine S.fe_ite _ _ _ (fun _ => hent _ _ (slice_le ..)) fun _ => ?_
  refine S.fe_ite _ _ _ (fun _ => hlit _) fun _ => ?_
  refine S.fe_ite _ _ _ (fun _ => hlit _) fun _ => ?_
  refine S.fe_dite _ _ _ (fun _ => ?_) (fun _ => hl1)
  refine S.fe_ite _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine S.fe_ite _ _ _ (fun _ => S.fe_ite _ _ _ (fun _ => htr _ _ _ _ _ (hsub _)) fun _ => z)
      fun _ => ?_
    exact S.fe_ite _ _ _ (fun _ => S.fe_ite _ _ _ (fun _ => htr _ _ _ _ _ (hsnd _)) fun _ => z)
      fun _ => hl1
  · refine S.fe_ite _ _ _ (fun _ => S.fe_ite _ _ _ (fun _ => htr _ _ _ _ _ (hneg _)) fun _ => z)
      fun _ => ?_
    exact S.fe_ite _ _ _ (fun _ => S.fe_ite _ _ _ (fun _ => htr _ _ _ _ _ (hsnd _)) fun _ => z)
      fun _ => hl1

/-- The value of a clique: a choice code or the code of the last label. -/
theorem ext_cl (π : BudPar) {Ev Kc : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ) {chs : List ℕ}
    (hc : S.ChainOK π.e chs) (hpw : S.PathW chs) {i : ℕ} (hi : i < 2 ^ S.gen.width (.cl chs)) :
    S.Ext π Ev Kc (S.gen.child (.cl chs) i) := by
  have hsp := S.spair_mul_le hq hc
  simp only [Setup.gen] at hi ⊢
  by_cases h2 : (S.clique chs).q = 2
  · rw [dite_pos' h2] at hi ⊢
    have hcw : codeWidth ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) ≤ π.Λ :=
      hΛ _ ((Nat.mul_le_mul_right _ ((S.clique chs).a_le_spair (by simp [Fin.lt_def]))).trans hsp)
    split
    · split_ifs
      · exact ⟨hpw, hi.trans_le (Nat.pow_le_pow_right (by norm_num) hcw)⟩
      · trivial
    · trivial
  · rw [dite_neg' h2] at hi ⊢
    split_ifs
    · exact ⟨hpw, hi⟩
    · trivial
    · trivial

/-- A table entry of a merged clique: the copies. -/
theorem ext_ent (π : BudPar) {Ev Kc : ℕ}
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length)) {i : ℕ} {rest : List ℕ}
    (hc : S.ChainOK π.e (i :: rest)) {v args : ℕ} (he : S.Ext π Ev Kc (.ent (i :: rest) v args))
    {ξ : ℕ} (hξ : ξ < 2 ^ S.gen.width (.ent (i :: rest) v args)) :
    S.Ext π Ev Kc (S.gen.child (.ent (i :: rest) v args) ξ) := by
  have hw : S.gen.width (.ent (i :: rest) v args) = S.xiWidth rest i v := rfl
  have hξ' : ξ < 2 ^ π.Ξ := (hw ▸ hξ).trans_le
    (Nat.pow_le_pow_right (by norm_num) ((hΞ v hc).trans (Nat.div_le_self _ _)))
  obtain ⟨-, -, hsq, -⟩ := hc
  obtain ⟨hpw, ha⟩ := he
  simp only [Setup.gen]
  rw [S.parentGrid_eq rest i hsq]
  dsimp only
  split_ifs
  · exact ⟨hpw, ha, hξ'⟩
  · trivial

/-- A table entry of the first clique. -/
theorem fe_ent0 (π : BudPar) {Ev Kc : ℕ} (hEv : 1 ≤ Ev)
    (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ)) {v args : ℕ} (hv : v < S.C₀.q)
    (ha : args < 2 ^ (π.Λ + π.Ξ)) (b : ℕ) : S.FE π Ev Kc (S.gen.child (.ent [] v args) b) := by
  have key : ∀ lo hi, hi ≤ S.nFac0 v →
      S.FE π Ev Kc (rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo hi) :=
    fun lo hi h => S.fe_rangeSt hEv _ _ _ _ (fun f _ => S.abs_factor0_le hEv hev v args f)
      (fun _ => ⟨hv, h, ha⟩)
  simp only [Setup.gen]
  split_ifs
  · exact key _ _ (Nat.div_le_self _ _)
  · exact key _ _ le_rfl

/-- A product over the factors of an entry of the first clique. -/
theorem fe_rng0 (π : BudPar) {Ev Kc : ℕ} (hEv : 1 ≤ Ev)
    (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ)) {v args lo hi : ℕ}
    (he : S.Ext π Ev Kc (.rng0 v args lo hi)) (hlo : lo ≤ hi) (b : ℕ) :
    S.FE π Ev Kc (S.gen.child (.rng0 v args lo hi) b) := by
  obtain ⟨hv, hhi, ha⟩ := he
  have key : ∀ a c, c ≤ S.nFac0 v →
      S.FE π Ev Kc (rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) a c) :=
    fun a c h => S.fe_rangeSt hEv _ _ _ _ (fun f _ => S.abs_factor0_le hEv hev v args f)
      (fun _ => ⟨hv, h, ha⟩)
  simp only [Setup.gen]
  split_ifs
  · exact key _ _ (by omega)
  · exact key _ _ hhi

/-- A product over the factors of an entry of a merged clique. -/
theorem fe_rng (π : BudPar) {Ev Kc : ℕ} (hEv : 1 ≤ Ev) (hKc : 2 * 2 ^ S.fw + 4 * π.Wm ≤ Kc)
    {j : ℕ} {rest : List ℕ} {v args ξ lo hi : ℕ} (hc : S.ChainOK π.e (j :: rest))
    (he : S.Ext π Ev Kc (.rng (j :: rest) v args ξ lo hi)) (b : ℕ) :
    S.FE π Ev Kc (S.gen.child (.rng (j :: rest) v args ξ lo hi) b) := by
  obtain ⟨hpw, ha, hξ⟩ := he
  have key : ∀ a c, S.FE π Ev Kc
      (rangeSt (S.factorSt rest j v args ξ) (.rng (j :: rest) v args ξ) a c) :=
    fun a c => S.fe_rangeSt hEv _ _ _ _ (fun f => S.fe_factorSt π hEv hKc hc hpw.1 hξ f)
      (fun _ => ⟨hpw, ha, hξ⟩)
  simp only [Setup.gen]
  split_ifs
  · exact key _ _
  · exact key _ _

/-- The transport sum node: the pivot index. -/
theorem ext_tr (π : BudPar) {Ev Kc : ℕ} (up : Bool) (x y m : Label) (lo hi : ℕ)
    (T : Multiset (HPlace × ℕ)) (c : ℤ) (hTv : ∀ s ∈ T, ValidPl up s.1)
    (he : S.Ext π Ev Kc (.tr up x y m lo hi T c)) (i : ℕ) :
    S.Ext π Ev Kc (S.gen.child (.tr up x y m lo hi T c) i) := by
  obtain ⟨hw, hc⟩ := he
  simp only [Setup.gen]
  split_ifs with hv
  · unfold PivotValid at hv
    simp only at hv
    generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d at hv ⊢
    obtain ⟨ν, t, T₁, c₁, c₀⟩ := d
    obtain ⟨-, hν, ht, hT₁, hpc, hc₁, hc₀⟩ := hv
    simp only at hν ht hT₁ hpc hc₁ hc₀ ⊢
    set l := srcSub up x y m lo hi with hl
    have hlen : l.length ≤ hi - lo := by rw [hl, srcSub]; exact List.length_take_le _ _
    have hh := pivot_halves l T ν t T₁ hν ht hT₁ hpc
    simp only [Ext]
    rw [srcSub_take up x y m lo hi ν (by omega), srcSub_drop up x y m lo hi ν, ← hl]
    have hWT : (T.map lwt).sum ≤ tWt l T := Nat.le_add_left _ _
    have htT : lwt t ≤ (T.map lwt).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem lwt ht)
    have h1 : (2 : ℤ) * (tWt (l.take ν) T₁ : ℤ) ≤ tWt l T := by exact_mod_cast hh.1
    have h2 : (2 : ℤ) * (tWt (l.drop (ν + 1)) (T - T₁ - {t}) : ℤ) ≤ tWt l T := by
      exact_mod_cast hh.2
    have hn1 : (0 : ℤ) ≤ (tWt (l.take ν) T₁ : ℤ) := Nat.cast_nonneg _
    have hn2 : (0 : ℤ) ≤ (tWt (l.drop (ν + 1)) (T - T₁ - {t}) : ℤ) := Nat.cast_nonneg _
    rw [abs_add_le_iff] at hc
    rw [abs_le] at hc₁ hc₀
    refine ⟨hw, ?_, ?_, ?_, ?_, hTv t ht⟩
    · have h3 : (tWt l T : ℤ) ≤ Kc := by linarith [hc.1, hc.2]
      have h4 : tWt l T ≤ Kc := by exact_mod_cast h3
      simp only [lwt] at htT
      omega
    · rw [abs_add_le_iff]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_add_le_iff]; constructor <;> linarith
  · trivial

theorem ext_trm (π : BudPar) {Ev Kc : ℕ} (up : Bool) (x y m : Label) (lo pos hi : ℕ)
    (t : HPlace × ℕ) (T₁ T₂ : Multiset (HPlace × ℕ)) (c₁ c₀ c₂ : ℤ)
    (he : S.Ext π Ev Kc (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) (b : ℕ) :
    S.Ext π Ev Kc (S.gen.child (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂) b) := by
  obtain ⟨hw, ht, h1, h0, h2, hv⟩ := he
  change S.Ext π Ev Kc
    (if b = 0 then .tr up x y m lo pos T₁ c₁ else .trr up x y m pos hi t T₂ c₀ c₂)
  split_ifs
  · exact ⟨hw, h1⟩
  · exact ⟨hw, ht, h0, h2, hv⟩

theorem ext_trr (π : BudPar) {Ev Kc : ℕ} (hEv : 1 ≤ Ev) (up : Bool) (x y m : Label) (pos hi : ℕ)
    (t : HPlace × ℕ) (T₂ : Multiset (HPlace × ℕ)) (c₀ c₂ : ℤ)
    (he : S.Ext π Ev Kc (.trr up x y m pos hi t T₂ c₀ c₂)) (b : ℕ) :
    S.Ext π Ev Kc (S.gen.child (.trr up x y m pos hi t T₂ c₀ c₂) b) := by
  obtain ⟨hw, -, -, h2, -⟩ := he
  simp only [Setup.gen]
  split_ifs
  · exact (abs_coeff_hRule_le _ _ _ _ _ _).trans (by exact_mod_cast hEv)
  · exact ⟨hw, h2⟩

/-- **The extra invariant passes to the children** along the paths. -/
theorem ext_child (π : BudPar) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ)
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length))
    {Ev : ℕ} (hEv : 1 ≤ Ev) (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ)) {st : St}
    (hI : S.Inv π.e st) (hinv : S.inv π st) (he : S.Ext π Ev (2 * 2 ^ S.fw + 4 * π.Wm) st)
    {i : ℕ} (hk : (S.gen.kind st = .sum ∧ i < 2 ^ S.gen.width st) ∨ S.gen.kind st = .prod)
    (hinvc : S.inv π (S.gen.child st i)) :
    S.Ext π Ev (2 * 2 ^ S.fw + 4 * π.Wm) (S.gen.child st i) := by
  cases st with
  | zero => trivial
  | lit w => trivial
  | cl chs =>
    have hi : i < 2 ^ S.gen.width (.cl chs) := by
      rcases hk with ⟨-, h⟩ | h
      · exact h
      · exfalso
        simp only [Setup.gen] at h
        split_ifs at h
    exact S.ext_cl π hq hΛ hinv he hi
  | last chs j =>
    exact ⟨he.1, he.2.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))⟩
  | ent chs v args =>
    cases chs with
    | nil => exact S.fe_ent0 π hEv hev hI.2 he.2 i hinvc
    | cons j rest =>
      have hi : i < 2 ^ S.gen.width (.ent (j :: rest) v args) := by
        rcases hk with ⟨-, h⟩ | h
        · exact h
        · exfalso
          simp only [Setup.gen] at h
          split at h
          · cases h
          · split_ifs at h
      exact S.ext_ent π hΞ hinv he hi
  | rng chs v args ξ lo hi =>
    cases chs with
    | nil => exact hinv.elim
    | cons j rest => exact S.fe_rng π hEv le_rfl hinv.1 he i hinvc
  | rng0 v args lo
      hi => exact S.fe_rng0 π hEv hev he (by have := hI; simp only [Inv] at this; omega) i hinvc
  | tr up x y m lo hi T c => exact S.ext_tr π up x y m lo hi T c hI.2.2 he i
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀
      c₂ => exact S.ext_trm π up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ he i
  | trr up x y m pos hi t T₂ c₀ c₂ => exact S.ext_trr π hEv up x y m pos hi t T₂ c₀ c₂ he i

/-- **The invariants of the reached states**: `Inv` (soundness), `inv` (the budget) and `Ext`. -/
theorem reach_inv (π : BudPar) (hS : S.Good) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ)
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length))
    (hD0 : ∀ v, S.nFac0 v ≤ 2 ^ π.D0) (hDm : ∀ k < π.e, nFac (2 ^ 2 ^ k) ≤ 2 ^ π.Dm)
    (hWm : 6 * (S.C₀.potential / 2 ^ π.e) ≤ π.Wm) {Ev : ℕ} (hEv : 1 ≤ Ev)
    (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ)) {st : St} (h : S.Reach st) :
    S.Inv π.e st ∧ S.inv π st ∧ S.Ext π Ev (2 * 2 ^ S.fw + 4 * π.Wm) st := by
  have hB := S.budgeted π hq hΛ hΞ hD0 hDm hWm
  have hSd := S.gen_sound hS (D := π.e) hq
  induction h with
  | root => exact ⟨⟨trivial, by simpa [Setup.clique_nil] using hq, Nat.zero_le _⟩, trivial, trivial⟩
  | sum st i _ hk hi ih =>
    obtain ⟨hI, hinv, he⟩ := ih
    have hc := (hB.sum st hinv hk i hi).1
    exact ⟨((hSd.sum st hI hk).2 i hi).1, hc,
      S.ext_child π hq hΛ hΞ hEv hev hI hinv he (Or.inl ⟨hk, hi⟩) hc⟩
  | prod st b _ hk hb ih =>
    obtain ⟨hI, hinv, he⟩ := ih
    obtain ⟨-, hI0, hI1, -, -⟩ := hSd.prod st hI hk
    obtain ⟨hi0, hi1, -, -⟩ := hB.prod st hinv hk
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · exact ⟨hI0, hi0, S.ext_child π hq hΛ hΞ hEv hev hI hinv he (Or.inr hk) hi0⟩
    · exact ⟨hI1, hi1, S.ext_child π hq hΛ hΞ hEv hev hI hinv he (Or.inr hk) hi1⟩

/-- **The reached states are in the invariant of the numeric generator** (`GenNum.lean`), with the
weight bound `A = 2 Wm + 1` and the fuel `B = w(A)`. -/
theorem reach_cubeInv (π : BudPar) (hS : S.Good) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ)
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length))
    (hD0 : ∀ v, S.nFac0 v ≤ 2 ^ π.D0) (hDm : ∀ k < π.e, nFac (2 ^ 2 ^ k) ≤ 2 ^ π.Dm)
    (hWm : 6 * (S.C₀.potential / 2 ^ π.e) ≤ π.Wm) {Ev : ℕ} (hEv : 1 ≤ Ev)
    (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ)) {st : St} (h : S.Reach st) :
    S.CubeInv π.e (2 * π.Wm + 1) (codeWidth (2 * π.Wm + 1)) st := by
  obtain ⟨hI, hinv, he⟩ := S.reach_inv π hS hq hΛ hΞ hD0 hDm hWm hEv hev h
  refine ⟨hI, ?_⟩
  have hfit : ∀ (up : Bool) (x y m : Label) (l : List (HPlace × ℕ)) (T : Multiset (HPlace × ℕ)),
      labelWt x + labelWt y + labelWt m ≤ π.Wm → tWt l T ≤ π.Wm → (∀ s ∈ T, ValidPl up s.1) →
      Num.TrFit (2 * π.Wm + 1) (codeWidth (2 * π.Wm + 1)) up x y m T :=
    fun up x y m l T h1 h2 h3 => by
      have : (T.map lwt).sum ≤ tWt l T := Nat.le_add_left _ _
      exact ⟨by omega, le_rfl, by omega, h3⟩
  cases st with
  | rng0 v args lo hi => exact he.1
  | tr up x y m lo hi T c => exact hfit _ _ _ _ _ _ he.1 hinv hI.2.2
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
    exact ⟨hfit _ _ _ _ _ _ he.1 hinv.1 hI.2.2.2.1, hfit _ _ _ _ _ _ he.1 hinv.2 hI.2.2.2.2,
      he.2.2.2.2.2⟩
  | trr up x y m pos hi t T₂ c₀ c₂ => exact ⟨hfit _ _ _ _ _ _ he.1 hinv hI.2.2, he.2.2.2.2⟩
  | _ => trivial

/-- **The code of a reached state** is below `2^(28 N + 15)`, for every `N` above the descent and
the cache, the codes of labels and multisets of targets of weight `Wm`, the codes `Λ + Ξ` of the
arguments and copies, and the bit size of a bound on the counters. -/
theorem code_lt (π : BudPar) (hS : S.Good) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ)
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length))
    (hD0 : ∀ v, S.nFac0 v ≤ 2 ^ π.D0) (hDm : ∀ k < π.e, nFac (2 ^ 2 ^ k) ≤ 2 ^ π.Dm)
    (hWm : 6 * (S.C₀.potential / 2 ^ π.e) ≤ π.Wm) {Ev : ℕ} (hEv : 1 ≤ Ev)
    (hev : ∀ x l, l.length = (S.G.ports x).length →
      |S.G.eval x l| ≤ (Ev : ℤ)) {N : ℕ}
    (hNc : (π.e + 1) * (2 * (2 * (2 * (2 * (2 ^ 2 ^ π.e) ^ 2 * S.fw) + 1) + 1) + 1) + 1 ≤ N)
    (hNt : 6 * codeWidth (π.Wm + 1) + 4 ≤ N) (hNl : π.Λ + π.Ξ ≤ N)
    (hNz : Nat.size (16 * (π.Wm + (2 * 2 ^ S.fw + 4 * π.Wm) + Ev + 2 ^ 2 ^ π.e +
      nFac (2 ^ 2 ^ π.e) + S.V + S.G.M + 1)) ≤ N) {st : St} (h : S.Reach st) :
    S.code st < 2 ^ (14 * (2 * N + 1) + 1) := by
  obtain ⟨hI, hinv, he⟩ := S.reach_inv π hS hq hΛ hΞ hD0 hDm hWm hEv hev h
  have hpow : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  generalize hX : 2 * (2 ^ 2 ^ π.e) ^ 2 * S.fw = X at hNc
  generalize hKc : 2 * 2 ^ S.fw + 4 * π.Wm = Kc at he hNz
  generalize hZ : 16 * (π.Wm + Kc + Ev + 2 ^ 2 ^ π.e + nFac (2 ^ 2 ^ π.e) + S.V + S.G.M + 1) = Z
    at hNz
  have hsm : ∀ x, x ≤ Z → x < 2 ^ N := fun x hx =>
    (lt_of_le_of_lt hx (Nat.lt_size_self Z)).trans_le (hpow hNz)
  have hbig : ∀ x, x < 2 ^ (π.Λ + π.Ξ) → x < 2 ^ N := fun x hx => hx.trans_le (hpow hNl)
  have hlc : ∀ l : Label, labelWt l ≤ π.Wm → lcode l < 2 ^ N := fun l hl =>
    (lcode_lt hl).trans_le (hpow (by omega))
  have htc : ∀ up (T : Multiset (HPlace × ℕ)), (T.map lwt).sum ≤ π.Wm → tcode up T < 2 ^ N :=
    fun up T hT => (tcode_lt up hT).trans_le (hpow hNt)
  have hch : ∀ chs, S.ChainOK π.e chs → S.PathW chs → SumProduct.NatList.enc chs < 2 ^ N := by
    intro chs hc hw
    have h1 := enc_lt_of_lt (hX ▸ S.pathW_lt hq hc hw)
    have h2 := (S.chainOK_facts hq hc).1
    refine h1.trans_le (hpow ?_)
    have := Nat.mul_le_mul_right (2 * X + 1) h2
    nlinarith
  have hca : ∀ chs, S.ChainOK π.e chs → S.cacheC chs < 2 ^ N := by
    intro chs hc
    have h1 := enc_lt_of_lt (hX ▸ S.cacheL_lt hS hq hc)
    have h2 := (S.chainOK_facts hq hc).1
    rw [length_cacheL] at h1
    refine h1.trans_le (hpow ?_)
    have := Nat.mul_le_mul_right (2 * (2 * (2 * X + 1) + 1) + 1)
        (show chs.length + 1 ≤ π.e + 1 by omega)
    omega
  have hqle : ∀ chs, S.ChainOK π.e chs → (S.clique chs).q ≤ 2 ^ 2 ^ π.e := fun chs
      hc => S.q_le hq hc
  have hnfq : ∀ chs, S.ChainOK π.e chs → nFac (Nat.sqrt (S.clique chs).q) ≤ nFac (2 ^ 2 ^ π.e) :=
    fun chs hc => nFac_mono ((Nat.sqrt_le_self _).trans (hqle chs hc))
  have hnf0 : ∀ v, S.nFac0 v ≤ 1 + S.V + S.G.M := fun v => by
    change 1 + (if v < S.K then S.V else S.G.M) ≤ 1 + S.V + S.G.M
    split_ifs <;> omega
  have hWT : ∀ l (T : Multiset (HPlace × ℕ)), (T.map lwt).sum ≤ tWt l T := fun _ _ =>
    Nat.le_add_left _ _
  have hcK : ∀ {w : ℤ} {W : ℕ}, |w| + 4 * (W : ℤ) ≤ Kc → |w| ≤ Kc := fun {w W} h => by
    have : (0 : ℤ) ≤ W := Nat.cast_nonneg W
    linarith
  have hWK : ∀ {w : ℤ} {W : ℕ}, |w| + 4 * (W : ℤ) ≤ Kc → W ≤ Kc := fun {w W} h => by
    have : (0 : ℤ) ≤ |w| := abs_nonneg w
    have : (W : ℤ) ≤ Kc := by linarith
    exact_mod_cast this
  have htg : ∀ t : HPlace × ℕ, t.2 ≤ Kc → Num.tgtNum t ≤ Z := fun t ht => by
    have := Num.plNum_lt t.1
    unfold Num.tgtNum
    omega
  have hup : ∀ up : Bool, up.toNat ≤ 1 := fun up => by cases up <;> decide
  cases st with
  | zero =>
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact hsm _ (by omega)
  | lit w =>
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hsm _ ((zz_le he).trans (by omega))⟩
  | cl chs =>
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hch chs hinv he, hca chs hinv⟩
  | last chs i =>
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hch chs hinv he.1, hca chs hinv,
      hbig _ (he.2.trans_le (hpow (Nat.le_add_right _ _)))⟩
  | ent chs v args =>
    have hv : v < 2 ^ 2 ^ π.e := hI.2.trans_le (hqle chs hinv)
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hch chs hinv he.1, hca chs hinv, hsm _ (by omega), hbig _ he.2⟩
  | rng chs v args ξ lo hi =>
    cases chs with
    | nil => exact hinv.elim
    | cons j rest =>
      obtain ⟨-, hv, hlo, hhi⟩ := hI
      have hv' : v < 2 ^ 2 ^ π.e := hv.trans_le ((Nat.sqrt_le_self _).trans (hqle rest hinv.1.1))
      have hn := hnfq rest hinv.1.1
      refine enc_lt_of_mem (by simp) ?_
      simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨hsm _ (by omega), hch _ hinv.1 he.1, hca _ hinv.1, hsm _ (by omega), hbig _ he.2.1,
        hbig _ (he.2.2.trans_le (hpow (Nat.le_add_left _ _))), hsm _ (by omega), hsm _ (by omega)⟩
  | rng0 v args lo hi =>
    have hlo : lo + 2 ≤ hi := hI
    obtain ⟨hv, hhi, ha⟩ := he
    have hn := hnf0 v
    have hv' : v < 2 ^ 2 ^ π.e := hq ▸ hv
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hca [] trivial, hsm _ (by omega), hbig _ ha, hsm _ (by omega),
      hsm _ (by omega)⟩
  | tr up x y m lo hi T c =>
    obtain ⟨hlo, hhi, -⟩ := hI
    obtain ⟨hw, hc⟩ := he
    have hl := length_srcList_le up x y m
    have hT := (hWT _ T).trans hinv
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hsm _ ((hup up).trans (by omega)), hlc x (by omega), hlc y (by omega),
      hlc m (by omega), hsm _ (by omega), hsm _ (by omega), htc up T hT,
      hsm _ ((zz_le (hcK hc)).trans (by omega))⟩
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
    obtain ⟨hlo, hpos, hhi, -, -⟩ := hI
    obtain ⟨hw, ht, hc₁, hc₀, hc₂, -⟩ := he
    have hl := length_srcList_le up x y m
    have hT₁ := (hWT _ T₁).trans hinv.1
    have hT₂ := (hWT _ T₂).trans hinv.2
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hsm _ ((hup up).trans (by omega)), hlc x (by omega), hlc y (by omega),
      hlc m (by omega), hsm _ (by omega), hsm _ (by omega), hsm _ (by omega), hsm _ (htg t ht),
      htc up T₁ hT₁, htc up T₂ hT₂, hsm _ ((zz_le (hcK hc₁)).trans (by omega)),
      hsm _ ((zz_le hc₀).trans (by omega)), hsm _ ((zz_le (hcK hc₂)).trans (by omega))⟩
  | trr up x y m pos hi t T₂ c₀ c₂ =>
    obtain ⟨hpos, hhi, -⟩ := hI
    obtain ⟨hw, ht, hc₀, hc₂, -⟩ := he
    have hl := length_srcList_le up x y m
    have hT₂ := (hWT _ T₂).trans hinv
    refine enc_lt_of_mem (by simp) ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hsm _ (by omega), hsm _ ((hup up).trans (by omega)), hlc x (by omega), hlc y (by omega),
      hlc m (by omega), hsm _ (by omega), hsm _ (by omega), hsm _ (htg t ht), htc up T₂ hT₂,
      hsm _ ((zz_le hc₀).trans (by omega)), hsm _ ((zz_le (hcK hc₂)).trans (by omega))⟩

end Setup

/-! ### The asymptotics -/

theorem part_cache {e L R q₀ s fw : ℕ} (heL : e ≤ L) (hRL : R ≤ L) (hL1 : 1 ≤ L)
    (hfw : fw ≤ 11 * L) (hq1 : 1 ≤ q₀) (hLq : L ^ 3 ≤ q₀) (hq3 : q₀ ^ 3 ≤ s) :
    ((e + 1) * (2 * (2 * (2 * (2 * q₀ ^ 2 * fw) + 1) + 1) + 1) + 1) * R ≤ 528 * s := by
  have hA1 : (e + 1) * (2 * (2 * (2 * (2 * q₀ ^ 2 * fw) + 1) + 1) + 1) + 1 ≤
      8 * (e + 1) * (2 * q₀ ^ 2 * fw + 1) := by nlinarith
  have hX1 : 2 * q₀ ^ 2 * fw + 1 ≤ 33 * L * q₀ ^ 2 := by
    have h1 : q₀ ^ 2 * fw ≤ q₀ ^ 2 * (11 * L) := Nat.mul_le_mul_left _ hfw
    have h2 : 1 ≤ q₀ ^ 2 := Nat.one_le_pow _ _ hq1
    have h3 : q₀ ^ 2 ≤ L * q₀ ^ 2 := Nat.le_mul_of_pos_left _ hL1
    nlinarith
  calc _ ≤ 8 * (e + 1) * (2 * q₀ ^ 2 * fw + 1) * R := Nat.mul_le_mul_right _ hA1
    _ ≤ 8 * (2 * L) * (33 * L * q₀ ^ 2) * L := by gcongr; omega
    _ = 528 * (L ^ 3 * q₀ ^ 2) := by ring
    _ ≤ 528 * (q₀ * q₀ ^ 2) := by gcongr
    _ = 528 * q₀ ^ 3 := by ring
    _ ≤ 528 * s := by gcongr

theorem part_cw {Wm R L cA s : ℕ} (hWR : Wm * R ^ 2 ≤ (48 * cA * s) ^ 2) (hR2 : R ^ 2 ≤ L)
    (hLs : L ≤ s) (hcA1 : 1 ≤ cA) :
    (6 * codeWidth (Wm + 1) + 4) * R ≤ 8820 * cA * s + 4 * s := by
  have hcw : codeWidth (Wm + 1) * R ≤ 1470 * cA * s := by
    apply le_of_sq_le_sq'
    have h1 : s ≤ s * s := Nat.le_mul_self s
    have h2 : s * s ≤ (cA * s) ^ 2 := by
      have := Nat.le_mul_of_pos_left s hcA1
      rw [sq]; exact Nat.mul_le_mul this this
    calc (codeWidth (Wm + 1) * R) ^ 2 = codeWidth (Wm + 1) ^ 2 * R ^ 2 := by ring
      _ ≤ 900 * (Wm + 1) * R ^ 2 := Nat.mul_le_mul_right _ (codeWidth_sq_le _)
      _ = 900 * (Wm * R ^ 2 + R ^ 2) := by ring
      _ ≤ 900 * ((48 * cA * s) ^ 2 + s) := by gcongr; exact hR2.trans hLs
      _ ≤ (1470 * cA * s) ^ 2 := by nlinarith
  have hR : R ≤ s := (Nat.le_self_pow (by norm_num) R).trans (hR2.trans hLs)
  nlinarith

theorem part_counters {Wm R L cA s c' C₁ fw q₀ V M : ℕ} (hsL' : s < 2 ^ (L + 1)) (hL1 : 1 ≤ L)
    (hc' : 384 * cA ^ 2 < 2 ^ c') (hW6 : Wm ≤ 384 * cA ^ 2 * s ^ 2) (hfw : fw = 3 * (L + 1) + 5)
    (hqs : q₀ ≤ s) (hq1 : 1 ≤ q₀) (hV : V ≤ (s + 2) ^ C₁) (hM : M ≤ C₁ * (s + 1)) (hsC : C₁ ≤ s)
    (hRL : R ≤ L) (hL4 : L ^ 4 ≤ s) :
    Nat.size (16 * (Wm + (2 * 2 ^ fw + 4 * Wm) + (s + 2) ^ C₁ + q₀ + nFac q₀ + V + M + 1)) * R ≤
      (c' + 3 * C₁ + 20) * s := by
  set B := c' + (L + 2) * C₁ + 4 * L + 8 with hB
  have hpow : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  have hs2 : s + 2 ≤ 2 ^ (L + 2) := by rw [pow_succ, pow_succ] at *; omega
  have hEvB : (s + 2) ^ C₁ ≤ 2 ^ B :=
    calc (s + 2) ^ C₁ ≤ (2 ^ (L + 2)) ^ C₁ := Nat.pow_le_pow_left hs2 _
      _ = 2 ^ ((L + 2) * C₁) := by rw [← pow_mul]
      _ ≤ 2 ^ B := hpow (by omega)
  have hsB : s ≤ 2 ^ B := hsL'.le.trans (hpow (by omega))
  have hs2B : 2 * s * s ≤ 2 ^ B := by
    calc 2 * s * s ≤ 2 * 2 ^ (L + 1) * 2 ^ (L + 1) := by gcongr
      _ = 2 ^ (2 * L + 3) := by rw [← pow_succ', ← pow_add]; congr 1; omega
      _ ≤ 2 ^ B := hpow (by omega)
  have e1 : Wm ≤ 2 ^ B := by
    have h2 : s ^ 2 ≤ 2 ^ (2 * (L + 1)) := by
      rw [pow_mul']; exact Nat.pow_le_pow_left hsL'.le 2
    calc Wm ≤ 384 * cA ^ 2 * s ^ 2 := hW6
      _ ≤ 2 ^ c' * 2 ^ (2 * (L + 1)) := Nat.mul_le_mul hc'.le h2
      _ = 2 ^ (c' + 2 * (L + 1)) := by rw [pow_add]
      _ ≤ 2 ^ B := hpow (by omega)
  have e2 : 2 ^ fw ≤ 2 ^ B := hpow (by omega)
  have e5 : nFac q₀ ≤ 2 ^ B := by
    have h1 : q₀ ≤ q₀ ^ 4 := Nat.le_self_pow (by norm_num) q₀
    have h2 : q₀ * q₀ ≤ q₀ ^ 4 := by rw [← sq]; exact Nat.pow_le_pow_right hq1 (by norm_num)
    have h3 : q₀ ^ 4 ≤ 2 ^ (4 * (L + 1)) := by
      rw [pow_mul']; exact Nat.pow_le_pow_left (hqs.trans hsL'.le) 4
    have h4 : 4 * 2 ^ (4 * (L + 1)) ≤ 2 ^ B := by
      calc 4 * 2 ^ (4 * (L + 1)) = 2 ^ (4 * L + 6) := by
            rw [show 4 * L + 6 = 2 + 4 * (L + 1) by ring, pow_add]; norm_num
        _ ≤ 2 ^ B := hpow (by omega)
    unfold nFac
    omega
  have e7 : M ≤ 2 ^ B := by
    have : C₁ * (s + 1) ≤ 2 * s * s := by nlinarith
    omega
  have hZB : 16 * (Wm + (2 * 2 ^ fw + 4 * Wm) + (s + 2) ^ C₁ + q₀ + nFac q₀ + V + M + 1) <
      2 ^ (B + 8) := by
    rw [pow_add, show (2 : ℕ) ^ 8 = 256 by norm_num]
    omega
  have hsz := Nat.size_le.mpr hZB
  have hB8 : B + 8 ≤ (c' + 3 * C₁ + 20) * L := by
    have := Nat.mul_le_mul_left c' hL1
    have := Nat.mul_le_mul_left C₁ (show L + 2 ≤ 3 * L by omega)
    nlinarith
  calc _ ≤ ((c' + 3 * C₁ + 20) * L) * L := Nat.mul_le_mul (hsz.trans hB8) hRL
    _ = (c' + 3 * C₁ + 20) * L ^ 2 := by ring
    _ ≤ (c' + 3 * C₁ + 20) * s :=
        Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right hL1 (by norm_num)).trans hL4)

theorem final_le {N R s K : ℕ} (hmain : N * R ≤ K * s) (hR1 : 1 ≤ R) (hK0 : 0 < K) :
    14 * (2 * N + 1) + 1 ≤ (28 * K + 15) * (s / R + 1) := by
  have hlt : s < R * (s / R + 1) := by
    have := Nat.lt_mul_div_succ s (show 0 < R by omega)
    omega
  have hNK : N < K * (s / R + 1) := by
    have : N * R < K * (s / R + 1) * R := by
      calc N * R ≤ K * s := hmain
        _ < K * (R * (s / R + 1)) := Nat.mul_lt_mul_of_pos_left hlt hK0
        _ = K * (s / R + 1) * R := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  generalize s / R + 1 = Q at hNK ⊢
  nlinarith

/-- **The sizes of the states** (Lemma 6.4). For every constant `C₁` there are `C` and `s₀` such
that for every `s ≥ s₀`, every network with at most `(s+2)^C₁` vertices, at most `C₁ (s+1)` edges,
degrees at most `C₁ (log₂ s + 1)` and vertex functions of absolute value at most `(s+2)^C₁` (at
arguments of the right length), and every precision, every state reached from the root along valid
indices has a code below
`2^(C · (s / ⌊√⌊log₂ s⌋⌋ + 1))`. -/
theorem state_size (C₁ : ℕ) : ∃ C s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ {V : ℕ} (G : Cross.EdgeNet ℤ (Fin V))
    (P : ℕ), V ≤ (s + 2) ^ C₁ → G.M ≤ C₁ * (s + 1) →
    (∀ v, (G.ports v).length ≤ C₁ * (Nat.log 2 s + 1)) →
    (∀ v l, l.length = (G.ports v).length → |G.eval v l| ≤ ((s + 2) ^ C₁ : ℕ)) →
    ∀ st, (setupOf s G P).Reach st →
    (setupOf s G P).code st < 2 ^ (C * (s / Nat.sqrt (Nat.log 2 s) + 1)) := by
  obtain ⟨_, s₁, hfc⟩ := formula_cost C₁
  refine ⟨28 * (1080 + 19008 * (4 * C₁ + 3) + Nat.size (384 * (4 * C₁ + 3) ^ 2) + 3 * C₁) + 15,
    s₁ + 2 ^ 192 + 48 * (4 * C₁ + 3) ^ 2 + C₁ + 1, ?_⟩
  intro s hs V G P hV hM hdeg hev st hst
  have hGood := (hfc s (by omega) G P 0 hV hM hdeg (Nat.zero_le _)).1
  generalize hcA : 4 * C₁ + 3 = cA at hs ⊢
  generalize hc' : Nat.size (384 * cA ^ 2) = c'
  have hs48 : 48 * cA ^ 2 + 1 ≤ s := by omega
  have hsC : C₁ ≤ s := by omega
  have hs192 : 2 ^ 192 ≤ s := by omega
  clear hs
  -- the parameters
  generalize hL : Nat.log 2 s = L at hdeg ⊢
  have hL192 : 192 ≤ L := hL ▸ Nat.le_log_of_pow_le (by norm_num) hs192
  have hsL : 2 ^ L ≤ s := hL ▸ Nat.pow_log_le_self 2 (by omega)
  have hsL' : s < 2 ^ (L + 1) := hL ▸ Nat.lt_pow_succ_log_self (by norm_num) s
  clear hs192
  generalize he : Nat.log 2 (L / 3) = e
  have he6 : 6 ≤ e := he ▸ Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hh3 : 2 ^ e ≤ L / 3 := he ▸ Nat.pow_log_le_self 2 (by omega)
  have hh6 : L < 6 * 2 ^ e := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (L / 3)
    rw [he, pow_succ] at this
    omega
  have hhs : hstar s = 2 ^ e := by rw [hstar, hL, he]
  generalize hh : 2 ^ e = h at hh3 hh6 hhs
  have hh1 : 1 ≤ h := hh ▸ Nat.one_le_two_pow
  have heh : e ≤ h := hh ▸ (Nat.lt_two_pow_self).le
  have hLh : h ≤ L := by omega
  have hq3 : (2 ^ h) ^ 3 ≤ s := by
    rw [← pow_mul]; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hsL
  have hLq : L ^ 3 ≤ 2 ^ h := by
    calc L ^ 3 ≤ (6 * h) ^ 3 := Nat.pow_le_pow_left hh6.le 3
      _ = 216 * (2 ^ e) ^ 3 := by rw [hh]; ring
      _ ≤ 2 ^ 2 ^ e := two_pow_cube_le e he6
      _ = 2 ^ h := by rw [hh]
  have hqq : 2 ^ 2 ^ e = 2 ^ h := by rw [hh]
  generalize hq₀ : 2 ^ h = q₀ at hq3 hLq hqq
  have hL1 : 1 ≤ L := by omega
  have hLq0 : L ≤ q₀ := (Nat.le_self_pow (by norm_num) L).trans hLq
  have hq1 : 1 ≤ q₀ := hq₀ ▸ Nat.one_le_two_pow
  have hq2s : q₀ ^ 2 ≤ s := (Nat.pow_le_pow_right hq1 (by norm_num)).trans hq3
  have hqs : q₀ ≤ s := (Nat.le_self_pow (by norm_num) q₀).trans hq2s
  have hL4 : L ^ 4 ≤ s := by
    calc L ^ 4 = L * L ^ 3 := by ring
      _ ≤ q₀ * q₀ := Nat.mul_le_mul hLq0 hLq
      _ = q₀ ^ 2 := by ring
      _ ≤ s := hq2s
  have hLs : L ≤ s := (Nat.le_self_pow (by norm_num) L).trans hL4
  -- the setup
  have hK : (setupOf s G P).K = 2 ^ (h - 1) := by rw [setupOf, hhs]
  have hK1 : 1 ≤ (setupOf s G P).K := hK ▸ Nat.one_le_two_pow
  have h2K : 2 * (setupOf s G P).K = 2 ^ 2 ^ e := by
    rw [hK, ← pow_succ', hh]; congr 1; omega
  have hKq : (setupOf s G P).K ≤ q₀ := by
    rw [hK, ← hq₀]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : (setupOf s G P).C₀.q = 2 ^ 2 ^ e := h2K
  have hfw : (setupOf s G P).fw = 3 * (L + 1) + 5 := by rw [setupOf, hL]
  have hΦ : (setupOf s G P).C₀.potential ≤ 64 * (cA * s) ^ 2 := by
    have hp : (setupOf s G P).C₀.potential ≤
        64 * (G.M + (setupOf s G P).K * (C₁ * (L + 1) + 1) + (setupOf s G P).K ^ 3) ^ 2 :=
      firstClique_potential G _ hK1 (C₁ * (L + 1)) hdeg
    refine hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    have h1 : G.M ≤ 2 * C₁ * s :=
      calc G.M ≤ C₁ * (s + 1) := hM
        _ ≤ C₁ * (2 * s) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * C₁ * s := by ring
    have h2 : (setupOf s G P).K * (C₁ * (L + 1) + 1) ≤ (2 * C₁ + 1) * s := by
      have hc : C₁ * (L + 1) + 1 ≤ (2 * C₁ + 1) * L := by
        have := Nat.mul_le_mul_left C₁ hL1
        rw [Nat.mul_one] at this
        calc C₁ * (L + 1) + 1 = C₁ * L + C₁ + 1 := by ring
          _ ≤ C₁ * L + C₁ * L + L := by omega
          _ = (2 * C₁ + 1) * L := by ring
      calc (setupOf s G P).K * (C₁ * (L + 1) + 1) ≤ q₀ * ((2 * C₁ + 1) * L) :=
            Nat.mul_le_mul hKq hc
        _ = (2 * C₁ + 1) * (q₀ * L) := by ring
        _ ≤ (2 * C₁ + 1) * (q₀ * q₀) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLq0)
        _ = (2 * C₁ + 1) * q₀ ^ 2 := by ring
        _ ≤ (2 * C₁ + 1) * s := Nat.mul_le_mul_left _ hq2s
    have h3 : (setupOf s G P).K ^ 3 ≤ s := (Nat.pow_le_pow_left hKq 3).trans hq3
    have : cA * s = 2 * C₁ * s + (2 * C₁ + 1) * s + s + s := by rw [← hcA]; ring
    omega
  have hnf : ∀ v, (setupOf s G P).nFac0 v ≤
      1 + (setupOf s G P).V + (setupOf s G P).G.M := fun v => by
    change 1 + (if v < (setupOf s G P).K then V else G.M) ≤ 1 + V + G.M
    split_ifs <;> omega
  have hev' : ∀ x l, l.length = ((setupOf s G P).G.ports x).length →
      |(setupOf s G P).G.eval x l| ≤ (((s + 2) ^ C₁ : ℕ) : ℤ) := hev
  have hV' : (setupOf s G P).V ≤ (s + 2) ^ C₁ := hV
  have hM' : (setupOf s G P).G.M ≤ C₁ * (s + 1) := hM
  generalize setupOf s G P = S at hK hK1 h2K hKq hq hfw hΦ hnf hev' hV' hM' hGood hst ⊢
  generalize hΦ₀ : S.C₀.potential = Φ₀ at hΦ
  -- the bound on the codes
  have hEv : 1 ≤ (s + 2) ^ C₁ := Nat.one_le_pow _ _ (by omega)
  have hcode := S.code_lt ⟨e, 0, codeWidth (Φ₀ / 2 ^ e), Nat.sqrt (230400 * Φ₀ / 2 ^ e),
      Nat.clog 2 (1 + S.V + S.G.M), Nat.clog 2 (nFac (2 ^ 2 ^ e)), 6 * (Φ₀ / 2 ^ e)⟩ hGood hq
    (fun a ha => codeWidth_mono ((Nat.le_div_iff_mul_le (by positivity)).mpr (hΦ₀ ▸ ha)))
    (fun v hc => by rw [← hΦ₀]; exact S.xiWidth_le hq hc v)
    (fun v => (hnf v).trans (Nat.le_pow_clog (by norm_num) _))
    (fun k hk => (nFac_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) hk.le))).trans (Nat.le_pow_clog (by norm_num) _))
    (by rw [hΦ₀]) hEv hev'
    (N := ((e + 1) * (2 * (2 * (2 * (2 * (2 ^ 2 ^ e) ^ 2 * S.fw) + 1) + 1) + 1) + 1) +
      (6 * codeWidth (6 * (Φ₀ / 2 ^ e) + 1) + 4) +
      (codeWidth (Φ₀ / 2 ^ e) + Nat.sqrt (230400 * Φ₀ / 2 ^ e)) +
      Nat.size (16 * (6 * (Φ₀ / 2 ^ e) + (2 * 2 ^ S.fw + 4 * (6 * (Φ₀ / 2 ^ e))) + (s + 2) ^ C₁ +
        2 ^ 2 ^ e + nFac (2 ^ 2 ^ e) + S.V + S.G.M + 1)))
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) hst
  rw [hqq] at hcode
  generalize hA : (e + 1) * (2 * (2 * (2 * (2 * q₀ ^ 2 * S.fw) + 1) + 1) + 1) + 1 = A at hcode
  generalize hWm : 6 * (Φ₀ / 2 ^ e) = Wm at hcode
  generalize hΛ : codeWidth (Φ₀ / 2 ^ e) = Λ at hcode
  generalize hΞ : Nat.sqrt (230400 * Φ₀ / 2 ^ e) = Ξ at hcode
  generalize hZ : 16 * (Wm + (2 * 2 ^ S.fw + 4 * Wm) + (s + 2) ^ C₁ + q₀ + nFac q₀ + S.V +
    S.G.M + 1) = Z at hcode
  generalize hR : L.sqrt = R
  have hR2 : R ^ 2 ≤ L := hR ▸ Nat.sqrt_le' L
  have hR1 : 1 ≤ R := hR ▸ Nat.le_sqrt'.mpr (by omega)
  have hRL : R ≤ L := (Nat.le_self_pow (by norm_num) R).trans hR2
  have hfw' : S.fw ≤ 11 * L := by omega
  have heL : e ≤ L := by omega
  have hXh : ∀ Y, Y / 2 ^ e * L ≤ 6 * Y := fun Y =>
    calc Y / 2 ^ e * L ≤ Y / 2 ^ e * (6 * 2 ^ e) := Nat.mul_le_mul_left _ (by rw [hh]; omega)
      _ = 6 * (Y / 2 ^ e * 2 ^ e) := by ring
      _ ≤ 6 * Y := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  -- the labels and targets
  have hWR : Wm * R ^ 2 ≤ (48 * cA * s) ^ 2 := by
    rw [← hWm]
    calc 6 * (Φ₀ / 2 ^ e) * R ^ 2 ≤ 6 * (Φ₀ / 2 ^ e * L) := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hR2)
      _ ≤ 6 * (6 * (64 * (cA * s) ^ 2)) :=
          Nat.mul_le_mul_left _ ((hXh Φ₀).trans (Nat.mul_le_mul_left _ hΦ))
      _ = (48 * cA * s) ^ 2 := by ring
  have hW6 : Wm ≤ 384 * cA ^ 2 * s ^ 2 := by
    rw [← hWm]
    calc 6 * (Φ₀ / 2 ^ e) ≤ 6 * Φ₀ := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
      _ ≤ 6 * (64 * (cA * s) ^ 2) := Nat.mul_le_mul_left _ hΦ
      _ = 384 * cA ^ 2 * s ^ 2 := by ring
  -- the arguments and copies
  have T2 : Λ * R ≤ 588 * cA * s :=
    part_sqrt (c := 900) (hΛ ▸ codeWidth_sq_le _) hR2 (hXh Φ₀) hΦ (by norm_num)
  have hΦ' : 230400 * Φ₀ ≤ 64 * (480 * cA * s) ^ 2 :=
    calc 230400 * Φ₀ ≤ 230400 * (64 * (cA * s) ^ 2) := Nat.mul_le_mul_left _ hΦ
      _ = 64 * (480 * cA * s) ^ 2 := by ring
  have hΞ2 : Ξ ^ 2 ≤ 1 * (230400 * Φ₀ / 2 ^ e) := by
    rw [one_mul, ← hΞ]; exact Nat.sqrt_le' _
  have T4 : Ξ * R ≤ 20 * (480 * cA) * s :=
    part_sqrt hΞ2 hR2 (hXh (230400 * Φ₀)) hΦ' (by norm_num)
  -- the conclusion
  have TA := part_cache heL hRL hL1 hfw' hq1 hLq hq3
  rw [hA] at TA
  have TT := part_cw hWR hR2 hLs (by omega)
  have TZ := part_counters (C₁ := C₁) hsL' hL1 (hc' ▸ Nat.lt_size_self _) hW6 hfw (hq₀ ▸ hqs) hq1
    hV' hM' hsC hRL hL4
  rw [hZ] at TZ
  generalize hN : A + (6 * codeWidth (Wm + 1) + 4) + (Λ + Ξ) + Nat.size Z = N at hcode
  have hmain : N * R ≤ (1080 + 19008 * cA + c' + 3 * C₁) * s := by
    rw [← hN]
    linarith only [TA, TT, T2, T4, TZ]
  refine hcode.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  exact final_le hmain hR1 (by omega)

end Cslib.Complexity.NtimeDspace.Cube
