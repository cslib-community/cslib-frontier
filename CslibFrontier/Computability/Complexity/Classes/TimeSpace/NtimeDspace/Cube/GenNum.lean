/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.EntryNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.FirstNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.TransNum

/-!
# The numeric generator of the formula (Lemma 6.4)

The machine of Lemma 6.4 keeps one state code (`Setup.code`) and computes, from it alone, the kind
of the node, its index width, the bits of a leaf and the code of each child. This module assembles
these computations into one numeric generator `Num.cubeFun` (a `SumProduct.GenFun`) that dispatches
on the kind field `stGet n 0` of the code: `0` zero, `1` literal, `2`–`5` the entry states
(`eTag`, `eWidth`, `eChild` of `EntryNum.lean`), `6` the first-clique factor ranges (`rng0ChildN`),
`7`–`9` the transport states (`trTagN`, `trWidthN`, `trLeafN`, `trChildAllN` of `TransNum.lean`).
The codes of the literal leaf factors of the first clique are a parameter `f0`; `f0C` computes them
from the network (`factor0C`).

## Main definitions

* `AGen.tree_value_succ`, `AGen.value_eq_of_cost`: a tree whose cost stays below `n · ℓ` is not cut
  by the fuel `n`, so the value is stable from the fuel `c / ℓ + 1` on, for a cost bound `c`.
* `Num.litBitN`: bit `k` of the residue modulo `2^P` (`k < P`) of the integer with a given zigzag
  code, without the power `2^P`.
* `Num.rng0ChildN`, `Num.cubeTag`, `Num.cubeWidth`, `Num.cubeBit`, `Num.cubeChild`, `Num.cubeFun`.
* `Num.f0C`: the codes of the literal leaf factors of the first clique.
* `Setup.NumExt A B`: the side conditions of the invariant (first-clique ranges at a node `v < 2K`,
and
  `TrInv A B` at the transport states); `Setup.CubeInv D A B = Setup.Inv D ∧ Setup.NumExt A B`.

## Main results

* `Setup.value_fuel`: the formula has value `Z(G) mod 2^P` at every fuel `n ≥ c / ℓ + 1`, for a
  cost bound `c` valid at every fuel and `ℓ ≥ 1`.
* `Setup.numExt_child`: `NumExt` is closed under all children of reachable states, for a weight
bound
  `A ≥ 12 (Φ₀ / 2^D) + 1` (`Φ₀` the potential of the first clique, `2K = 2^(2^D)`) and a fuel
  `B ≥ w(A)`.
* `Num.cube_agrees`: `cubeFun` agrees with `Setup.gen` under `Setup.code` on `CubeInv`.
* `Num.cube_value`, `Num.cube_cost`: the value `Z(G) mod 2^P` and the cost of the numeric
  unfolding from the code of the root, at every fuel `n ≥ c / ℓ + 1`.
* `Num.f0C_eq`: `f0C` gives the codes of the leaf factors, for nonnegative vertex functions.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset SumProduct

/-! ### Explicit fuel -/

namespace AGen

variable {St : Type} (g : AGen St)

theorem tree_succ_leaf {P n : ℕ} {st : St} (hk : g.kind st = .leaf) :
    g.tree P (n + 1) st = .leaf P (res P (g.leafVal st)) := by
  simp only [tree, hk]

theorem tree_succ_sum {P n : ℕ} {st : St} (hk : g.kind st = .sum) :
    g.tree P (n + 1) st = .sum P (g.width st) fun i => g.tree P n (g.child st i) := by
  simp only [tree, hk]

theorem tree_succ_prod {P n : ℕ} {st : St} (hk : g.kind st = .prod) :
    g.tree P (n + 1) st = .prod P (g.tree P n (g.child st 0)) (g.tree P n (g.child st 1)) := by
  simp only [tree, hk]

/-- **A tree that is not cut by the fuel.** If the cost of the unfolding with fuel `n` is below
`n · ℓ` (every inner node costs at least `ℓ`), one more unit of fuel does not change the value. -/
theorem tree_value_succ {P ℓ : ℕ} : ∀ n st, (g.tree P n st).cost ℓ < n * ℓ →
    (g.tree P (n + 1) st).value = (g.tree P n st).value := by
  intro n
  induction n with
  | zero => intro st h; simp at h
  | succ n ih =>
    intro st h
    have hs : (n + 1) * ℓ = n * ℓ + ℓ := Nat.succ_mul n ℓ
    rcases hk : g.kind st with _ | _ | _
    · rw [g.tree_succ_leaf hk, g.tree_succ_leaf hk]
    · rw [g.tree_succ_sum hk] at h
      rw [g.tree_succ_sum hk, g.tree_succ_sum hk]
      simp only [SPTree.cost] at h
      simp only [SPTree.value]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ih _ ?_
      have := Finset.le_sup (f := fun i => (g.tree P n (g.child st i)).cost ℓ) hi
      omega
    · rw [g.tree_succ_prod hk] at h
      rw [g.tree_succ_prod hk, g.tree_succ_prod hk]
      simp only [SPTree.cost] at h
      simp only [SPTree.value]
      have h0 := le_max_left ((g.tree P n (g.child st 0)).cost ℓ)
          ((g.tree P n (g.child st 1)).cost ℓ)
      have h1 := le_max_right ((g.tree P n (g.child st 0)).cost ℓ)
          ((g.tree P n (g.child st 1)).cost ℓ)
      rw [ih _ (by omega), ih _ (by omega)]

/-- **The value is stable from the fuel `c / ℓ + 1` on**, for a cost bound `c` at every fuel. -/
theorem value_stable {P ℓ c : ℕ} (hℓ : 1 ≤ ℓ) (st : St) (hc : ∀ n, (g.tree P n st).cost ℓ ≤ c)
    (n : ℕ) (hn : c / ℓ + 1 ≤ n) : ∀ m, n ≤ m → (g.tree P m st).value = (g.tree P n st).value := by
  have hlt : c < (c / ℓ + 1) * ℓ := by
    have h1 := Nat.div_add_mod c ℓ
    have h2 := Nat.mod_lt c (show 0 < ℓ by omega)
    rw [Nat.succ_mul, Nat.mul_comm]
    omega
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [g.tree_value_succ (ℓ := ℓ) m st ?_, ih]
    calc (g.tree P m st).cost ℓ ≤ c := hc m
      _ < (c / ℓ + 1) * ℓ := hlt
      _ ≤ m * ℓ := Nat.mul_le_mul_right _ (hn.trans hm)

/-- The value at every fuel `n ≥ c / ℓ + 1`, from its value at all large fuels. -/
theorem value_eq_of_cost {P ℓ c : ℕ} (hℓ : 1 ≤ ℓ) (st : St) (hc : ∀ n, (g.tree P n st).cost ℓ ≤ c)
    {r : ℕ} (hr : ∃ N, ∀ n, N ≤ n → (g.tree P n st).value = r) :
    ∀ n, c / ℓ + 1 ≤ n → (g.tree P n st).value = r := by
  obtain ⟨N, hN⟩ := hr
  intro n hn
  rw [← g.value_stable hℓ st hc n hn (max N n) (le_max_right _ _)]
  exact hN _ (le_max_left _ _)

end AGen

namespace Setup

variable (S : Setup)

/-- **The value of the formula at an explicit fuel**: for a good setup, `ℓ ≥ 1` and a bound `c` on
the cost at every fuel, the unfolding with any fuel `n ≥ c / ℓ + 1` has value `Z(G) mod 2^P`. -/
theorem value_fuel (hS : S.Good) {ℓ c : ℕ} (hℓ : 1 ≤ ℓ)
    (hc : ∀ n, (S.gen.tree S.P n (.cl [])).cost ℓ ≤ c) :
    ∀ n, c / ℓ + 1 ≤ n → (S.gen.tree S.P n (.cl [])).value = AGen.res S.P S.G.value :=
  S.gen.value_eq_of_cost hℓ _ hc (S.formula_value hS)

/-! ### The invariant -/

/-- The side conditions of the invariant: a first-clique range is at a node `v < 2K`, and the
transport states satisfy `TrInv A B`. -/
def NumExt (A B : ℕ) : St → Prop
  | .rng0 v _ _ _ => v < 2 * S.K
  | .tr up x y m _ _ T _ => Num.TrFit A B up x y m T
  | .trm up x y m _ _ _ t T₁ T₂ _ _ _ => Num.TrFit A B up x y m T₁ ∧ Num.TrFit A B up x y m T₂ ∧
      ValidPl up t.1
  | .trr up x y m _ _ t T₂ _ _ => Num.TrFit A B up x y m T₂ ∧ ValidPl up t.1
  | _ => True

/-- **The invariant of the numeric generator**: reachable (`Setup.Inv`) with the side conditions. -/
def CubeInv (D A B : ℕ) (st : St) : Prop := S.Inv D st ∧ S.NumExt A B st

theorem numExt_of_trInv {A B : ℕ} {st : St} (h : Num.TrInv A B st) : S.NumExt A B st := by
  cases st <;> first | exact (h : False).elim | exact h

theorem trInv_of_numExt {A B : ℕ} {up : Bool} {x y m : Label} {lo hi : ℕ}
    {T : Multiset (HPlace × ℕ)}
    {c : ℤ} (h : S.NumExt A B (.tr up x y m lo hi T c)) : Num.TrInv A B
        (.tr up x y m lo hi T c) := h

theorem numExt_rangeSt {A B : ℕ} (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi : ℕ)
    (hmk : ∀ f, S.NumExt A B (mk f)) (hmkR : ∀ a b, S.NumExt A B (mkR a b)) :
    S.NumExt A B (rangeSt mk mkR lo hi) := by
  unfold rangeSt
  split_ifs
  · trivial
  · exact hmk _
  · exact hmkR _ _

/-- **The root transport states of the factors fit the weight bound.** -/
theorem numExt_factorSt {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A ≤ B) {j : ℕ} {rest : List ℕ}
    (hp : S.PathOK (j :: rest)) (v args ξ f : ℕ) : S.NumExt A B (S.factorSt rest j v args ξ f) := by
  have hch := S.pathOK_chainOK he _ hp
  obtain ⟨-, -, hsq, -⟩ := hp
  rcases S.factorSt_shape rest j v args ξ f
      hsq with e | ⟨w, e⟩ | ⟨row, x, -, e⟩ | ⟨up, x, y, m, c, e⟩ <;>
    rw [e]
  · trivial
  · trivial
  · trivial
  · have hq : S.C₀.q = 2 ^ 2 ^ D := he
    have fo := S.factor_ok ⟨D, 0, 0, 0, 0, 0, 6 * (S.C₀.potential / 2 ^ D)⟩ hq le_rfl hch v args ξ f
    rw [e] at fo
    have h1 : tWt (srcSub up x y m 0 (srcList up x y m).length) (tgtMs up x y m) ≤
        6 * (S.C₀.potential / 2 ^ D) := fo.1
    rw [srcSub_root, tWt_srcList] at h1
    have h2 : ((tgtMs up x y m).map lwt).sum ≤ tWt (srcList up x y m) (tgtMs up x y m) :=
      Nat.le_add_left _ _
    rw [tWt_srcList] at h2
    exact ⟨by omega, hB, by omega, tgtMs_valid up x y m⟩

/-- **The side conditions are closed under children** of the reachable states. -/
theorem numExt_child {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A ≤ B) (st : St)
        (hinv : S.Inv D st)
    (hext : S.NumExt A B st) (i : ℕ) : S.NumExt A B (S.gen.child st i) := by
  classical
  cases st with
  | zero => trivial
  | lit w => trivial
  | cl chs =>
    simp only [Setup.gen]
    repeat' split
    all_goals trivial
  | last chs j => trivial
  | ent chs v args =>
    cases chs with
    | nil =>
      have hv : v < 2 * S.K := hinv.2
      have hch : S.gen.child (.ent [] v args) i =
          if i = 0 then rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) 0
              (S.nFac0 v / 2)
          else rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) (S.nFac0 v / 2)
            (S.nFac0 v) := rfl
      rw [hch]
      split_ifs
      · exact S.numExt_rangeSt _ _ _ _ (fun _ => trivial) (fun _ _ => hv)
      · exact S.numExt_rangeSt _ _ _ _ (fun _ => trivial) (fun _ _ => hv)
    | cons j rest =>
      obtain ⟨-, -, h, -⟩ := hinv.1
      have hpg := S.parentGrid_eq rest j h
      simp only [Setup.gen, hpg]
      split_ifs
      · trivial
      · trivial
  | rng chs v args ξ lo hi =>
    cases chs with
    | nil => exact hinv.elim
    | cons j rest =>
      have hch : S.gen.child (.rng (j :: rest) v args ξ lo hi) i =
          if i = 0 then rangeSt (S.factorSt rest j v args ξ) (.rng (j :: rest) v args ξ) lo
              ((lo + hi) / 2)
          else rangeSt (S.factorSt rest j v args ξ) (.rng (j :: rest) v args ξ)
              ((lo + hi) / 2) hi :=
        rfl
      rw [hch]
      split_ifs
      · exact S.numExt_rangeSt _ _ _ _ (S.numExt_factorSt he hA hB hinv.1 v args ξ)
          (fun _ _ => trivial)
      · exact S.numExt_rangeSt _ _ _ _ (S.numExt_factorSt he hA hB hinv.1 v args ξ)
          (fun _ _ => trivial)
  | rng0 v args lo hi =>
    have hv : v < 2 * S.K := hext
    have hch : S.gen.child (.rng0 v args lo hi) i =
        if i = 0 then rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo ((lo + hi) / 2)
        else rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) ((lo + hi) / 2) hi := rfl
    rw [hch]
    split_ifs
    · exact S.numExt_rangeSt _ _ _ _ (fun _ => trivial) (fun _ _ => hv)
    · exact S.numExt_rangeSt _ _ _ _ (fun _ => trivial) (fun _ _ => hv)
  | tr up x y m lo hi T c =>
    rcases Num.trInv_child S (st := .tr up x y m lo hi T c) hext i with h | h | ⟨w, h⟩
    · exact S.numExt_of_trInv h
    · rw [h]; trivial
    · rw [h]; trivial
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
    rcases Num.trInv_child S (st := .trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂) hext
        i with h | h | ⟨w, h⟩
    · exact S.numExt_of_trInv h
    · rw [h]; trivial
    · rw [h]; trivial
  | trr up x y m pos hi t T₂ c₀ c₂ =>
    rcases Num.trInv_child S (st := .trr up x y m pos hi t T₂ c₀ c₂) hext i with h | h | ⟨w, h⟩
    · exact S.numExt_of_trInv h
    · rw [h]; trivial
    · rw [h]; trivial

/-- The invariant holds at the root. -/
theorem cubeInv_root {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D) :
    S.CubeInv D A B (.cl []) := by
  have hq0 : (S.clique []).q = 2 ^ 2 ^ D := he
  exact ⟨⟨trivial, by simpa using hq0, by simp⟩, trivial⟩

end Setup

/-! ### The numeric generator -/

namespace Num

theorem res_zero (P : ℕ) : AGen.res P 0 = 0 := by simp [AGen.res]

theorem testBit_res_nat (P n k : ℕ) (hk : k < P) : (AGen.res P (n : ℤ)).testBit k =
    n.testBit k := by
  have : AGen.res P (n : ℤ) = n % 2 ^ P := by
    unfold AGen.res
    have e : ((n % 2 ^ P : ℕ) : ℤ) = (n : ℤ) % 2 ^ P := by push_cast; rfl
    rw [← e, Int.toNat_natCast]
  rw [this, Nat.testBit_mod_two_pow]
  simp [hk]

/-- Bit `k` of the two's complement of the integer with zigzag code `z`: bit `k` of `z / 2` for
an even code, the complement of bit `k` of `(z - 1) / 2` for an odd code (the value
`-((z - 1) / 2) - 1`). It is bit `k` of the residue modulo `2^P` for every `P > k`, and needs no
power `2^P`. -/
def litBitN (z k : ℕ) : Bool :=
  if z % 2 = 0 then (z / 2).testBit k else !((z - 1) / 2).testBit k

theorem litBitN_eq {P k : ℕ} (hk : k < P) (v : ℤ) : litBitN (zz v) k =
    (AGen.res P v).testBit k := by
  rcases le_or_gt 0 v with hv | hv
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hv
    have hz : zz (n : ℤ) = 2 * n := by simp [zz]
    rw [hz, litBitN, ite_eq_left (by omega), Nat.mul_div_cancel_left _ (by norm_num),
      testBit_res_nat _ _ _ hk]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, v = -((n : ℤ) + 1) := ⟨(-v - 1).toNat, by omega⟩
    subst hn
    have hz : zz (-((n : ℤ) + 1)) = 2 * n + 1 := by
      unfold zz
      rw [ite_eq_right (by omega)]
      omega
    rw [hz, litBitN, ite_eq_right (by omega), show (2 * n + 1 - 1) / 2 = n by omega]
    have hM0 : 0 < 2 ^ P := by positivity
    have hr := Nat.div_add_mod n (2 ^ P)
    have hrl := Nat.mod_lt n hM0
    have hres : AGen.res P (-((n : ℤ) + 1)) = 2 ^ P - (n % 2 ^ P + 1) := by
      unfold AGen.res
      generalize n % 2 ^ P = r at hr hrl
      generalize n / 2 ^ P = q at hr
      generalize hMn : 2 ^ P = M at hr hrl
      have key : -((n : ℤ) + 1) = ((M - (r + 1) : ℕ) : ℤ) + (M : ℤ) * (-(q : ℤ) - 1) := by
        have : ((n : ℕ) : ℤ) = (M : ℤ) * q + r := by exact_mod_cast hr.symm
        push_cast [Nat.cast_sub (show r + 1 ≤ M by omega)] at this ⊢
        linarith
      rw
          [show ((2 : ℤ) ^ P) =
          (M : ℤ) by rw [← hMn]; push_cast; rfl, key, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by positivity) (by omega), Int.toNat_natCast]
    rw [hres, Nat.testBit_two_pow_sub_succ hrl, Nat.testBit_mod_two_pow]
    simp [hk]

/-- The children of a first-clique factor range: its two halves, a single factor by `f0`. -/
def rng0ChildN (f0 : ℕ → ℕ → ℕ → ℕ) (n b : ℕ) : ℕ :=
  if b = 0 then
    rangeN (f0 (stGet n 2) (stGet n 3))
      (fun a b => NatList.enc [6, stGet n 1, stGet n 2, stGet n 3, a, b])
      (stGet n 4) ((stGet n 4 + stGet n 5) / 2)
  else
    rangeN (f0 (stGet n 2) (stGet n 3))
      (fun a b => NatList.enc [6, stGet n 1, stGet n 2, stGet n 3, a, b])
      ((stGet n 4 + stGet n 5) / 2) (stGet n 5)

/-- The kind tag of a state code. -/
def cubeTag (B fw n : ℕ) : ℕ :=
  if 2 ≤ stGet n 0 ∧ stGet n 0 ≤ 5 then eTag B fw n
  else if stGet n 0 = 6 then 2
  else if 7 ≤ stGet n 0 ∧ stGet n 0 ≤ 9 then trTagN n else 0

/-- The index width of a state code. -/
def cubeWidth (B fw n : ℕ) : ℕ :=
  if 2 ≤ stGet n 0 ∧ stGet n 0 ≤ 5 then eWidth fw n
  else if 7 ≤ stGet n 0 ∧ stGet n 0 ≤ 9 then trWidthN B n else 0

/-- Bit `k` of the leaf value of a state code (bit `k < P` of its residue modulo `2^P`). -/
def cubeBit (B n k : ℕ) : Bool :=
  if stGet n 0 = 1 then litBitN (stGet n 1) k
  else if 7 ≤ stGet n 0 ∧ stGet n 0 ≤ 9 then (trLeafN B n).testBit k else false

/-- The code of child `i` of a state code. -/
def cubeChild (fw B K V M : ℕ) (f0 : ℕ → ℕ → ℕ → ℕ) (n i : ℕ) : ℕ :=
  if 2 ≤ stGet n 0 ∧ stGet n 0 ≤ 5 then eChild fw B K V M f0 n i
  else if stGet n 0 = 6 then rng0ChildN f0 n i
  else if 7 ≤ stGet n 0 ∧ stGet n 0 ≤ 9 then trChildAllN B n i else zeroC

/-- **The numeric generator of the formula**, at precision `P`, reader fuel `B`, field width `fw`,
`K` vertex groups, `V` vertices, `M` edges, and the codes `f0` of the first-clique leaf factors. -/
def cubeFun (P B fw K V M : ℕ) (f0 : ℕ → ℕ → ℕ → ℕ) : GenFun where
  tag := cubeTag B fw
  prec := fun _ => P
  param := cubeWidth B fw
  bit := cubeBit B
  child := cubeChild fw B K V M f0

/-- The codes of the literal leaf factors of the first clique, from the network. -/
def f0C {V : ℕ} (G : Cross.EdgeNet ℤ (Fin V)) (K fw : ℕ) (v x f : ℕ) : ℕ :=
  litC (2 * factor0C G K (arrN (2 * K) fw (extN (firstBudget G K))) fw v x f)

theorem eChild_congr {fw B K V M : ℕ} {f0 f0' : ℕ → ℕ → ℕ → ℕ} {n : ℕ}
    (h : stGet n 0 = 4 → stGet n 1 = 1 → ∀ x f, f0 (stGet n 3) x f = f0' (stGet n 3) x f) (i : ℕ) :
    eChild fw B K V M f0 n i = eChild fw B K V M f0' n i := by
  unfold eChild
  by_cases h2 : stGet n 0 = 2
  · rw [ite_eq_left h2, ite_eq_left h2]
  rw [ite_eq_right h2, ite_eq_right h2]
  by_cases h3 : stGet n 0 = 3
  · rw [ite_eq_left h3, ite_eq_left h3]
  rw [ite_eq_right h3, ite_eq_right h3]
  by_cases h4 : stGet n 0 = 4
  · rw [ite_eq_left h4, ite_eq_left h4]
    unfold entChildN
    dsimp only
    by_cases h1 : stGet n 1 = 1
    · rw [show f0 (stGet n 3) = f0' (stGet n 3) from funext fun x => funext (h h4 h1 x)]
    · rw [ite_eq_right h1, ite_eq_right h1]
  · rw [ite_eq_right h4, ite_eq_right h4]

section Agree

variable (S : Setup)

theorem stGet_code_zero : ∀ st : St, stGet (S.code st) 0 =
    match st with
    | .zero => 0 | .lit _ => 1 | .cl _ => 2 | .last _ _ => 3 | .ent _ _ _ => 4 | .rng .. => 5
    | .rng0 .. => 6 | .tr .. => 7 | .trm .. => 8 | .trr .. => 9 := by
  intro st
  cases st <;> simp [Setup.code]

/-- The local agreement of `cubeFun` with `Setup.gen` at a state of the invariant. -/
theorem cube_local (hS : S.Good) {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A)
    (hB : codeWidth A + 2 ≤ B) {f0 : ℕ → ℕ → ℕ → ℕ}
    (hf0 : ∀ v < 2 * S.K, ∀ x f, f0 v x f = S.code (.lit (S.factor0 v x f)))
    (st : St) (hinv : S.CubeInv D A B st) :
    cubeTag B S.fw (S.code st) = AGen.kindTag (S.gen.kind st) ∧
    cubeWidth B S.fw (S.code st) = S.gen.width st ∧
    (S.gen.kind st = .leaf → ∀ k < S.P,
      cubeBit B (S.code st) k = (AGen.res S.P (S.gen.leafVal st)).testBit k) ∧
    ∀ i, cubeChild S.fw B S.K S.V S.G.M f0 (S.code st) i = S.code (S.gen.child st i) := by
  classical
  have hBe : codeWidth (S.C₀.potential / 2 ^ D) + 2 ≤ B :=
    le_trans (Nat.add_le_add_right (codeWidth_mono (by omega)) 2) hB
  set f0' : ℕ → ℕ → ℕ → ℕ := fun v x f =>
    if v < 2 * S.K then f0 v x f else S.code (.lit (S.factor0 v x f)) with hf0'def
  have hf0' : ∀ v x f, f0' v x f = S.code (.lit (S.factor0 v x f)) := by
    intro v x f
    simp only [hf0'def]
    split_ifs with hv
    · exact hf0 v hv x f
    · rfl
  -- the entry states
  have hent : ∀ st, Num.EntrySt st → S.CubeInv D A B st →
      cubeTag B S.fw (S.code st) = AGen.kindTag (S.gen.kind st) ∧
      cubeWidth B S.fw (S.code st) = S.gen.width st ∧
      (S.gen.kind st = .leaf → ∀ k < S.P,
        cubeBit B (S.code st) k = (AGen.res S.P (S.gen.leafVal st)).testBit k) ∧
      ∀ i, cubeChild S.fw B S.K S.V S.G.M f0 (S.code st) i = S.code (S.gen.child st i) := by
    intro st hst hinv
    obtain ⟨e1, e2, e3, e4⟩ := entry_agree S hS he hBe hf0' st hst hinv.1
    have hk : 2 ≤ stGet (S.code st) 0 ∧ stGet (S.code st) 0 ≤ 5 := by
      cases st <;> first | exact (hst : False).elim | simp [stGet_code_zero]
    have hk1 : stGet (S.code st) 0 ≠ 1 := by omega
    have hk7 : ¬ (7 ≤ stGet (S.code st) 0 ∧ stGet (S.code st) 0 ≤ 9) := by omega
    have hcg : ∀ i, eChild S.fw B S.K S.V S.G.M f0 (S.code st) i =
        eChild S.fw B S.K S.V S.G.M f0' (S.code st) i := by
      refine eChild_congr fun h4 h1 x f => ?_
      cases st with
      | ent chs v args =>
        cases chs with
        | nil =>
          have hv : v < 2 * S.K := hinv.1.2
          have e : stGet (S.code (.ent [] v args)) 3 = v := by simp [Setup.code]
          rw [e]
          simp only [hf0'def, ite_eq_left hv]
        | cons j rest =>
          exfalso
          have e : stGet (S.code (.ent (j :: rest) v args)) 1 = NatList.enc (j :: rest) := by
            simp [Setup.code]
          exact enc_cons_ne_one j rest (e ▸ h1)
      | _ => rw [stGet_code_zero] at h4; simp at h4
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · rw [cubeTag, ite_eq_left hk, e1]
    · rw [cubeWidth, ite_eq_left hk, e2]
    · intro _ k _
      rw [cubeBit, ite_eq_right hk1, ite_eq_right hk7, e4, res_zero, Nat.zero_testBit]
    · rw [cubeChild, ite_eq_left hk, hcg, e3]
  -- the transport states
  have htr : ∀ st, Num.TrInv A B st →
      cubeTag B S.fw (S.code st) = AGen.kindTag (S.gen.kind st) ∧
      cubeWidth B S.fw (S.code st) = S.gen.width st ∧
      (S.gen.kind st = .leaf → ∀ k < S.P,
        cubeBit B (S.code st) k = (AGen.res S.P (S.gen.leafVal st)).testBit k) ∧
      ∀ i, cubeChild S.fw B S.K S.V S.G.M f0 (S.code st) i = S.code (S.gen.child st i) := by
    intro st h
    obtain ⟨e0, e1, e2, e3, e4⟩ := tr_agree S h
    have e0' : 7 ≤ stGet (S.code st) 0 ∧ stGet (S.code st) 0 ≤ 9 := by
      change 7 ≤ getF (S.code st) 0 ∧ getF (S.code st) 0 ≤ 9
      omega
    have h25 : ¬ (2 ≤ stGet (S.code st) 0 ∧ stGet (S.code st) 0 ≤ 5) := by omega
    have h6 : stGet (S.code st) 0 ≠ 6 := by omega
    have h1 : stGet (S.code st) 0 ≠ 1 := by omega
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · rw [cubeTag, ite_eq_right h25, ite_eq_right h6, ite_eq_left e0', e1]
    · rw [cubeWidth, ite_eq_right h25, ite_eq_left e0', e2]
    · intro _ k hk
      rw [cubeBit, ite_eq_right h1, ite_eq_left e0', ← e3, testBit_res_nat _ _ _ hk]
    · rw [cubeChild, ite_eq_right h25, ite_eq_right h6, ite_eq_left e0', e4]
  cases st with
  | zero =>
    have h0 : stGet (S.code .zero) 0 = 0 := stGet_code_zero S .zero
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · rw [cubeTag, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega),
        ite_eq_right (by rw [h0]; omega)]; rfl
    · rw [cubeWidth, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega)]; rfl
    · intro _ k _
      rw [cubeBit, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega),
        show S.gen.leafVal .zero = 0 from rfl, res_zero, Nat.zero_testBit]
    · rw [cubeChild, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega),
        ite_eq_right (by rw [h0]; omega)]; rfl
  | lit w =>
    have h0 : stGet (S.code (.lit w)) 0 = 1 := stGet_code_zero S (.lit w)
    have h1 : stGet (S.code (.lit w)) 1 = zz w := by simp [Setup.code]
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · rw [cubeTag, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega),
        ite_eq_right (by rw [h0]; omega)]; rfl
    · rw [cubeWidth, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega)]; rfl
    · intro _ k hk
      rw [cubeBit, ite_eq_left h0, h1, litBitN_eq hk]
      rfl
    · rw [cubeChild, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega),
        ite_eq_right (by rw [h0]; omega)]; rfl
  | rng0 v args lo hi =>
    have hv : v < 2 * S.K := hinv.2
    have h0 : stGet (S.code (.rng0 v args lo hi)) 0 = 6 := stGet_code_zero S _
    have h25 : ¬ (2 ≤ stGet (S.code (.rng0 v args lo hi)) 0 ∧
        stGet (S.code (.rng0 v args lo hi)) 0 ≤ 5) := by omega
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · rw [cubeTag, ite_eq_right h25, ite_eq_left h0]; rfl
    · rw [cubeWidth, ite_eq_right (by rw [h0]; omega), ite_eq_right (by rw [h0]; omega)]; rfl
    · intro hk; exact absurd hk (by simp [Setup.gen])
    · rw [cubeChild, ite_eq_right h25, ite_eq_left h0]
      have hch : S.gen.child (.rng0 v args lo hi) i =
          if i = 0 then Setup.rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo
              ((lo + hi) / 2)
          else Setup.rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args)
              ((lo + hi) / 2) hi := rfl
      have e : f0 v args = fun f => S.code (.lit (S.factor0 v args f)) :=
        funext fun f => hf0 v hv args f
      have hc : S.code (.rng0 v args lo hi) = NatList.enc [6, S.cacheC [], v, args, lo, hi] := rfl
      rw [hch, hc]
      simp only [rng0ChildN, stGet_cons_zero, stGet_cons_succ]
      rw [e]
      by_cases hi0 : i = 0
      · rw [ite_eq_left hi0, ite_eq_left hi0, code_rangeSt]; rfl
      · rw [ite_eq_right hi0, ite_eq_right hi0, code_rangeSt]; rfl
  | cl chs => exact hent _ trivial hinv
  | last chs j => exact hent _ trivial hinv
  | ent chs v args => exact hent _ trivial hinv
  | rng chs v args ξ lo hi =>
    cases chs with
    | nil => exact hinv.1.elim
    | cons j rest => exact hent _ trivial hinv
  | tr up x y m lo hi T c => exact htr _ hinv.2
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ => exact htr _ hinv.2
  | trr up x y m pos hi t T₂ c₀ c₂ => exact htr _ hinv.2

/-- **The numeric generator agrees with the formula** on the states of `CubeInv D A B`, for a good
setup with `2K = 2^(2^D)`, a weight bound `A ≥ 12 (Φ₀ / 2^D) + 1`, a fuel `B ≥ w(A) + 2`, and codes
`f0` of the leaf factors of the first clique at the nodes `v < 2K`. -/
theorem cube_agrees (hS : S.Good) {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A + 2 ≤ B) {f0 : ℕ → ℕ → ℕ → ℕ}
    (hf0 : ∀ v < 2 * S.K, ∀ x f, f0 v x f = S.code (.lit (S.factor0 v x f))) :
    S.gen.Agrees (cubeFun S.P B S.fw S.K S.V S.G.M f0) S.code (S.CubeInv D A B) S.P where
  closed_sum := fun st hinv hk i hi =>
    ⟨(((S.gen_sound hS he).sum st hinv.1 hk).2 i hi).1,
      S.numExt_child he hA (by omega) st hinv.1 hinv.2 i⟩
  closed_prod := fun st hinv hk =>
    ⟨⟨((S.gen_sound hS he).prod st hinv.1 hk).2.1, S.numExt_child he hA (by omega) st hinv.1 hinv.2
        0⟩,
      ⟨((S.gen_sound hS he).prod st hinv.1 hk).2.2.1,
        S.numExt_child he hA (by omega) st hinv.1 hinv.2 1⟩⟩
  tag := fun st hinv => (cube_local S hS he hA hB hf0 st hinv).1
  prec := fun _ _ => rfl
  param := fun st hinv _ => (cube_local S hS he hA hB hf0 st hinv).2.1
  bit := fun st hinv hk => (cube_local S hS he hA hB hf0 st hinv).2.2.1 hk
  child := fun st hinv => (cube_local S hS he hA hB hf0 st hinv).2.2.2

/-- **The value of the numeric unfolding** from the code of the root: `Z(G) mod 2^P` at every fuel
`n ≥ c / ℓ + 1`, for `ℓ ≥ 1` and a bound `c` on the cost of the formula at every fuel. -/
theorem cube_value (hS : S.Good) {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A + 2 ≤ B) {f0 : ℕ → ℕ → ℕ → ℕ}
    (hf0 : ∀ v < 2 * S.K, ∀ x f, f0 v x f = S.code (.lit (S.factor0 v x f)))
    {ℓ c : ℕ} (hℓ : 1 ≤ ℓ) (hc : ∀ n, (S.gen.tree S.P n (.cl [])).cost ℓ ≤ c) (n : ℕ)
    (hn : c / ℓ + 1 ≤ n) :
    ((cubeFun S.P B S.fw S.K S.V S.G.M f0).tree n (S.code (.cl []))).value =
      AGen.res S.P S.G.value := by
  rw [AGen.value_agrees S.gen (cube_agrees S hS he hA hB hf0) n _ (S.cubeInv_root he)]
  exact S.value_fuel hS hℓ hc n hn

/-- **The cost of the numeric unfolding** is the cost of the formula. -/
theorem cube_cost (hS : S.Good) {D A B : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D)
    (hA : 12 * (S.C₀.potential / 2 ^ D) + 1 ≤ A) (hB : codeWidth A + 2 ≤ B) {f0 : ℕ → ℕ → ℕ → ℕ}
    (hf0 : ∀ v < 2 * S.K, ∀ x f, f0 v x f = S.code (.lit (S.factor0 v x f))) (ℓ n : ℕ) :
    ((cubeFun S.P B S.fw S.K S.V S.G.M f0).tree n (S.code (.cl []))).cost ℓ =
      (S.gen.tree S.P n (.cl [])).cost ℓ :=
  AGen.cost_agrees S.gen (cube_agrees S hS he hA hB hf0) ℓ n _ (S.cubeInv_root he)

/-- **The codes of the leaf factors of the first clique**, from the network, for nonnegative
vertex functions. -/
theorem f0C_eq (hS : S.Good) (hnn : EvalNonneg S.G) :
    ∀ v < 2 * S.K, ∀ x f, f0C S.G S.K S.fw v x f = S.code (.lit (S.factor0 v x f)) := by
  intro v hv x f
  have hC : Fits S.fw S.C₀.a := fits_path S hS (chs := []) trivial
  rw [code_lit, ← factor0C_eq S hS.1 hC hnn hv x f, f0C]
  simp [zz]

end Agree

end Num

end Cslib.Complexity.NtimeDspace.Cube
