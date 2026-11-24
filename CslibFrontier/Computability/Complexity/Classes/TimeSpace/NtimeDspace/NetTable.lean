/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetIntervalEntry

/-!
# The table entries of the explicit block network as a term

`tableEntryT` computes Complexitylib's `tableEntryNum`: the entry at index `j`
of the table of vertex `v` of the explicit block network, whose ports are
`explicitPortsNum`. The letters of the block edges at `v` are read from the
bits of `j` at the positions of their ports (`lettersT`), so neither the port
list nor the table is ever stored.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool} {k s : ℕ} {State : Type}

theorem lsbValue_map_range (m : ℕ) (f : ℕ → Bool) :
    Cslib.BitString.lsbValue ((List.range m).map f) =
      ∑ r ∈ Finset.range m, (f r).toNat * 2 ^ r := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Cslib.BitString.lsbValue, ih,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [Function.comp, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    ring

section Terms

variable (k s : ℕ)

/-- The term computing `letterBits k s b`, the number of bits of a letter. -/
def letterBitsT (bT : Term) : Term := mul (const (s + k + 4)) bT

/-- The term computing `halfBase k q m v n`, the first explicit edge of block edge `n` at
vertex `v`. -/
def halfBaseT (qT mT vT nT : Term) : Term :=
  ite (eqT (blockSrcT k qT nT) vT) (mul mT nT) (add (halvesT k qT mT) (mul mT nT))

/-- The letter number of block edge `n` read at vertex `v` from the table index `j`. -/
def lettersT (qT mT σT vT jT : Term) (nT : Term) : Term :=
  sumT mT fun r => mul (bit jT (portIdxT k qT mT σT vT (add (halfBaseT k qT mT vT nT) r)))
    (powT (const 2) r)

end Terms

theorem denote_halfBaseT (qT mT vT nT : Term) (env : List ℕ) :
    (halfBaseT k qT mT vT nT).denote w env =
      halfBase k (qT.denote w env) (mT.denote w env) (vT.denote w env) (nT.denote w env) := by
  simp only [halfBaseT, halfBase, denote_ite, denote_eqT, denote_blockSrcT, denote_mul,
    denote_add, halvesT, denote_const]
  split_ifs <;> simp_all

theorem StableAt.halfBaseT {qT mT vT nT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hm : StableAt w mT env) (hv : StableAt w vT env) (hn : StableAt w nT env) :
    StableAt w (halfBaseT k qT mT vT nT) env := fun extra => by
  rw [denote_halfBaseT, denote_halfBaseT, hq extra, hm extra, hv extra, hn extra]

theorem denote_lettersT {qT mT σT vT jT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hm : StableAt w mT env) (hσ : StableAt w σT env) (hv : StableAt w vT env)
    (hj : StableAt w jT env) {nT : Term} (hn : StableAt w nT env) :
    (lettersT k qT mT σT vT jT nT).denote w env =
      lettersAt k (qT.denote w env) (mT.denote w env)
        (explicitPortsNum k (qT.denote w env) (mT.denote w env) (σT.denote w env)
          (vT.denote w env)) (jT.denote w env) (vT.denote w env) (nT.denote w env) := by
  unfold lettersT lettersAt readNum
  rw [lsbValue_map_range, denote_sumT _ _ env (fun r => ((jT.denote w env).testBit
    ((explicitPortsNum k (qT.denote w env) (mT.denote w env) (σT.denote w env)
      (vT.denote w env)).idxOf (halfBase k (qT.denote w env) (mT.denote w env) (vT.denote w env)
        (nT.denote w env) + r))).toNat * 2 ^ r)]
  intro acc r
  have hx : StableAt w (add (halfBaseT k qT mT vT nT) (lvl env.length)) ([acc, r] ++ env) :=
    ((StableAt.halfBaseT (hq.extend _) (hm.extend _) (hv.extend _) (hn.extend _)).add
      (stableAt_lvl (by simp)))
  have hp := denote_portIdxT k (hq.extend [acc, r]) (hm.extend [acc, r]) (hσ.extend [acc, r])
    (hv.extend [acc, r]) hx
  simp only [List.cons_append, List.nil_append] at hp
  rw [denote_mul, denote_bit, hp, powT_denote _ _ _ (stableAt_const _ _)]
  simp [denote_halfBaseT, hq.cons₂, hm.cons₂, hσ.cons₂, hv.cons₂, hj.cons₂, hn.cons₂]

/-- `lettersT` implements the letter numbers at `v` from `j`. -/
theorem implementsFun_lettersT {qT mT σT vT jT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hm : StableAt w mT env) (hσ : StableAt w σT env) (hv : StableAt w vT env)
    (hj : StableAt w jT env) :
    ImplementsFun w env (lettersT k qT mT σT vT jT)
      (lettersAt k (qT.denote w env) (mT.denote w env)
        (explicitPortsNum k (qT.denote w env) (mT.denote w env) (σT.denote w env)
          (vT.denote w env)) (jT.denote w env) (vT.denote w env)) :=
  implementsFun_of_denote fun extra a ha => by
    rw [denote_lettersT (hq.extend extra) (hm.extend extra) (hσ.extend extra) (hv.extend extra)
      (hj.extend extra) ha, hq extra, hm extra, hσ extra, hv extra, hj extra]

/-! ### Validity, sinks, and the table entry -/

section Terms2

variable (k s : ℕ)

/-- The term computing `letterCount k s b`, the number of letters. -/
def letterCountT (bT : Term) : Term := add (ccountT k s bT) (powT (const 3) bT)

/-- The term computing `validNum` at the explicit ports as `1` or `0`: every block edge at `v`
reads a letter number below `letterCount` from the table index `j`. -/
def validT (qT bT σT vT jT : Term) : Term :=
  allT (mul qT (const (3 * k + 1))) fun n =>
    sub (const 1) (mul (lt (const 0) (add (eqT (blockSrcT k qT n) vT)
        (eqT (edgeTargetT k qT σT n) vT)))
      (sub (const 1) (lt (lettersT k qT (letterBitsT k s bT) σT vT jT n) (letterCountT k s bT))))

/-- The term computing `acceptNum k s b n`, the accepting weight of the letter numbered `n`. -/
def acceptT (bT n : Term) : Term :=
  mul (lt n (ccountT k s bT)) (eqT (mod (mod n (cradT k bT)) (const 3)) (const 1))

variable {State : Type} (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)

/-- The term computing `oldEntryNum`: the tensor of an interval for `v < q`, and otherwise the
sink of edge `v - q`, the accepting weight for the last one and `1` for the others. -/
def oldEntryT (RT NT qT bT σT : Term) (L : Term → Term) (vT : Term) : Term :=
  ite (lt vT qT) (intervalEntryT e machine RT NT qT bT σT L vT)
    (ite (eqT (add (sub vT qT) (const 1)) qT) (acceptT k s bT (L (sub vT qT))) (const 1))

/-- **The table entry** at index `j` of vertex `v`. -/
def tableEntryT (RT NT qT bT σT vT jT : Term) : Term :=
  ite (lt vT (mul qT (const (3 * k + 2))))
    (ite (validT k s qT bT σT vT jT)
      (oldEntryT k s e machine RT NT qT bT σT (lettersT k qT (letterBitsT k s bT) σT vT jT) vT)
      (const 0))
    (eqT (bit jT (portIdxT k qT (letterBitsT k s bT) σT vT
        (sub vT (mul qT (const (3 * k + 2))))))
      (bit jT (portIdxT k qT (letterBitsT k s bT) σT vT
        (add (halvesT k qT (letterBitsT k s bT)) (sub vT (mul qT (const (3 * k + 2))))))))

end Terms2

theorem denote_acceptT {bT : Term} (n : Term) {env : List ℕ} (hb : StableAt w bT env) :
    (acceptT k s bT n).denote w env = acceptNum k s (bT.denote w env) (n.denote w env) := by
  simp only [acceptT, acceptNum, denote_mul, denote_lt, denote_ccountT hb, denote_eqT, denote_mod,
    denote_cradT hb, denote_const, cradix]
  by_cases h1 : n.denote w env < controlCount k s (bT.denote w env) <;>
    by_cases h2 : n.denote w env % (bT.denote w env ^ (k + 1) * 3) % 3 = 1 <;> simp [h1, h2]

theorem denote_letterCountT {bT : Term} {env : List ℕ} (hb : StableAt w bT env) :
    (letterCountT k s bT).denote w env = letterCount k s (bT.denote w env) := by
  simp [letterCountT, letterCount, denote_ccountT hb, powT_denote _ _ _ (stableAt_const _ _)]

open Classical in
theorem denote_validT {qT bT σT vT jT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hb : StableAt w bT env) (hσ : StableAt w σT env) (hv : StableAt w vT env)
    (hj : StableAt w jT env) :
    (validT k s qT bT σT vT jT).denote w env =
      if validNum k (qT.denote w env) s (bT.denote w env) (σT.denote w env)
        (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
          (vT.denote w env)) (jT.denote w env) (vT.denote w env) = true then 1 else 0 := by
  have hm : StableAt w (letterBitsT k s bT) env := (stableAt_const _ _).mul hb
  have hmv : (letterBitsT k s bT).denote w env = letterBits k s (bT.denote w env) := by
    simp [letterBitsT, letterBits]
  unfold validT
  rw [allT_denote _ _ env (fun n => ¬ (blockSrcNum k (qT.denote w env) n = vT.denote w env ∨
      edgeTargetNum k (qT.denote w env) (σT.denote w env) n = vT.denote w env) ∨
      lettersAt k (qT.denote w env) (letterBits k s (bT.denote w env))
        (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
          (vT.denote w env)) (jT.denote w env) (vT.denote w env) n <
        letterCount k s (bT.denote w env)) fun acc n => by
      have hn : StableAt w (lvl env.length) ([acc, n] ++ env) := stableAt_lvl (by simp)
      have hl := denote_lettersT (k := k) (hq.extend [acc, n]) (hm.extend [acc, n])
        (hσ.extend [acc, n]) (hv.extend [acc, n]) (hj.extend [acc, n]) hn
      have he := denote_edgeTargetT k (hq.extend [acc, n]) (hσ.extend [acc, n]) hn
      have hc := denote_letterCountT (k := k) (s := s) (hb.extend [acc, n])
      simp only [List.cons_append, List.nil_append] at hl he hc
      simp only [denote_sub, denote_const, denote_mul, denote_lt, denote_add, denote_eqT,
        denote_blockSrcT, hl, he, hc, hq.cons₂, hv.cons₂, hσ.cons₂, hj.cons₂, hb.cons₂, hm.cons₂,
        hmv, denote_lvl_index]
      by_cases h1 : blockSrcNum k (qT.denote w env) n = vT.denote w env <;>
        by_cases h2 : edgeTargetNum k (qT.denote w env) (σT.denote w env) n = vT.denote w env <;>
        by_cases h3 : lettersAt k (qT.denote w env) (letterBits k s (bT.denote w env))
          (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env))
            (σT.denote w env) (vT.denote w env)) (jT.denote w env) (vT.denote w env) n <
          letterCount k s (bT.denote w env) <;> simp [h1, h2, h3]]
  apply ite_iff
  unfold validNum
  simp only [denote_mul, denote_const, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]

variable {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

theorem denote_oldEntryT [DecidableEq State] {RT NT qT bT σT vT : Term} {L : Term → Term}
    {Lv : ℕ → ℕ} {env : List ℕ} (hR : StableAt w RT env) (hN : StableAt w NT env)
    (hq : StableAt w qT env) (hb : StableAt w bT env) (hσ : StableAt w σT env)
    (hv : StableAt w vT env) (hL : ImplementsFun w env L Lv) (hbpos : 0 < bT.denote w env)
    (hRv : RT.denote w env = radix (bT.denote w env) w.length s)
    (hNv : NT.denote w env = w.length) :
    (oldEntryT k s e machine RT NT qT bT σT L vT).denote w env =
      oldEntryNum e (bT.denote w env) machine w (qT.denote w env) (σT.denote w env) Lv
        (vT.denote w env) := by
  unfold oldEntryT oldEntryNum
  rw [denote_ite, denote_lt]
  by_cases h1 : vT.denote w env < qT.denote w env
  · rw [ite_eq_left (by simp [h1]), ite_eq_left h1, intervalEntryT_denote hR hN hq hb hσ hv
      hL hbpos hRv hNv]
  · rw [ite_eq_right (by simp [h1]), ite_eq_right h1, denote_ite, denote_eqT]
    have hd : (add (sub vT qT) (const 1)).denote w env = vT.denote w env - qT.denote w env + 1 := by
      simp
    by_cases h2 : vT.denote w env - qT.denote w env + 1 = qT.denote w env
    · rw [ite_eq_left (by rw [ite_eq_left (hd.trans h2)]; exact Nat.one_pos), ite_eq_left h2,
        denote_acceptT _ hb,
        hL.den (hv.sub hq), denote_sub]
    · rw [ite_eq_right (by rw [ite_eq_right (fun h => h2 (hd.symm.trans h))]; exact lt_irrefl 0),
        ite_eq_right h2]
      rfl

/-- **The table entry term computes the table entry of the explicit block network.** -/
theorem denote_tableEntryT [DecidableEq State] {RT NT qT bT σT vT jT : Term} {env : List ℕ}
    (hR : StableAt w RT env) (hN : StableAt w NT env) (hq : StableAt w qT env)
    (hb : StableAt w bT env) (hσ : StableAt w σT env) (hv : StableAt w vT env)
    (hj : StableAt w jT env) (hbpos : 0 < bT.denote w env)
    (hRv : RT.denote w env = radix (bT.denote w env) w.length s)
    (hNv : NT.denote w env = w.length) :
    (tableEntryT k s e machine RT NT qT bT σT vT jT).denote w env =
      tableEntryNum e (bT.denote w env) machine w (qT.denote w env) (σT.denote w env)
        (vT.denote w env)
        (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
          (vT.denote w env)) (jT.denote w env) := by
  have hm : StableAt w (letterBitsT k s bT) env := (stableAt_const _ _).mul hb
  have hmv : (letterBitsT k s bT).denote w env = letterBits k s (bT.denote w env) := by
    simp [letterBitsT, letterBits]
  unfold tableEntryT tableEntryNum
  rw [denote_ite, denote_lt]
  by_cases h1 : vT.denote w env < qT.denote w env * (3 * k + 2)
  · rw [ite_eq_left (by simp [h1]), ite_eq_left h1, denote_ite, denote_validT hq hb hσ hv hj]
    by_cases h2 : validNum k (qT.denote w env) s (bT.denote w env) (σT.denote w env)
        (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
          (vT.denote w env)) (jT.denote w env) (vT.denote w env) = true
    · rw [ite_eq_left (by simp [h2]), ite_eq_left h2,
        denote_oldEntryT hR hN hq hb hσ hv (implementsFun_lettersT hq hm hσ hv hj) hbpos hRv hNv,
        hmv]
    · rw [ite_eq_right (by simp [h2]), ite_eq_right h2]; rfl
  · rw [ite_eq_right (by simp [h1]), ite_eq_right h1, denote_eqT, denote_bit, denote_bit]
    have hx1 : StableAt w (sub vT (mul qT (const (3 * k + 2)))) env :=
      hv.sub (hq.mul (stableAt_const _ _))
    have hx2 : StableAt w (add (halvesT k qT (letterBitsT k s bT))
        (sub vT (mul qT (const (3 * k + 2))))) env :=
      ((hq.mul (stableAt_const _ _)).mul hm).add hx1
    rw [denote_portIdxT k hq hm hσ hv hx1, denote_portIdxT k hq hm hσ hv hx2, hmv]
    simp only [denote_sub, denote_mul, denote_const, denote_add, halvesT, hmv]
    by_cases h3 : (jT.denote w env).testBit ((explicitPortsNum k (qT.denote w env)
        (letterBits k s (bT.denote w env)) (σT.denote w env) (vT.denote w env)).idxOf
          (vT.denote w env - qT.denote w env * (3 * k + 2))) =
      (jT.denote w env).testBit ((explicitPortsNum k (qT.denote w env)
        (letterBits k s (bT.denote w env)) (σT.denote w env) (vT.denote w env)).idxOf
          (qT.denote w env * (3 * k + 1) * letterBits k s (bT.denote w env) +
            (vT.denote w env - qT.denote w env * (3 * k + 2))))
    · rw [ite_eq_left h3, h3]; simp
    · rw [ite_eq_right h3]
      cases ha : (jT.denote w env).testBit ((explicitPortsNum k (qT.denote w env)
        (letterBits k s (bT.denote w env)) (σT.denote w env) (vT.denote w env)).idxOf
          (vT.denote w env - qT.denote w env * (3 * k + 2))) <;>
      cases hb' : (jT.denote w env).testBit ((explicitPortsNum k (qT.denote w env)
        (letterBits k s (bT.denote w env)) (σT.denote w env) (vT.denote w env)).idxOf
          (qT.denote w env * (3 * k + 1) * letterBits k s (bT.denote w env) +
            (vT.denote w env - qT.denote w env * (3 * k + 2)))) <;> simp_all

end Cslib.Complexity.NtimeDspace.LocalSim
