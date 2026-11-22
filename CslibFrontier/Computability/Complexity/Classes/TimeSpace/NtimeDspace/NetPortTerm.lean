/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetGraphTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ParserTerm

/-!
# Edges and ports of the explicit block network as terms

Terms for edge targets and sources, and for the ports of a vertex: the number
of ports and the position of a port (`List.idxOf` in `explicitPortsNum`),
both as counts, so the port list is never stored.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool}

theorem StableAt.firstAfterT (k : ℕ) {qT σT cT iT δT : Term} {env : List ℕ}
    (h0 : StableAt w qT env) (h1 : StableAt w σT env) (h2 : StableAt w cT env)
    (h3 : StableAt w iT env) (h4 : StableAt w δT env) :
    StableAt w (firstAfterT k qT σT cT iT δT) env := fun extra => by
  rw [denote_firstAfterT k (h1.extend extra) (h2.extend extra) (h3.extend extra) (h4.extend extra),
    denote_firstAfterT k h1 h2 h3 h4, h0 extra, h1 extra, h2 extra, h3 extra, h4 extra]

theorem StableAt.lastBeforeT (k : ℕ) {σT cT iT δT : Term} {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env)
    (h3 : StableAt w iT env) (h4 : StableAt w δT env) :
    StableAt w (lastBeforeT k σT cT iT δT) env := fun extra => by
  rw [denote_lastBeforeT k (h1.extend extra) (h2.extend extra) (h3.extend extra) (h4.extend extra),
    denote_lastBeforeT k h1 h2 h3 h4, h1 extra, h2 extra, h3 extra, h4 extra]

theorem getD_eq_optCode (o : Option ℕ) (d : ℕ) :
    o.getD d = if optCode o = 0 then d else optCode o - 1 := by
  cases o <;> simp [optCode]

/-! ### Edge endpoints -/

/-- The term computing `edgeTargetNum k q σ n`, the vertex at which the block edge numbered `n`
ends. -/
def edgeTargetT (k : ℕ) (qT σT nT : Term) : Term :=
  ite (lt nT qT) (ite (lt (add nT (const 1)) qT) (add nT (const 1)) (add qT nT))
    (ite (eqT (firstAfterT k qT σT
        (add (div (mod (sub nT qT) (const (k * 3))) (const 3)) (const 1))
        (div (sub nT qT) (const (k * 3))) (mod (sub nT qT) (const 3))) (const 0))
      (add qT nT)
      (sub (firstAfterT k qT σT
        (add (div (mod (sub nT qT) (const (k * 3))) (const 3)) (const 1))
        (div (sub nT qT) (const (k * 3))) (mod (sub nT qT) (const 3))) (const 1)))

theorem denote_edgeTargetT (k : ℕ) {qT σT nT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hσ : StableAt w σT env) (hn : StableAt w nT env) :
    (edgeTargetT k qT σT nT).denote w env =
      edgeTargetNum k (qT.denote w env) (σT.denote w env) (nT.denote w env) := by
  have hc : StableAt w (add (div (mod (sub nT qT) (const (k * 3))) (const 3)) (const 1)) env :=
    ((((hn.sub hq).mod (stableAt_const _ _)).div (stableAt_const _ _)).add (stableAt_const _ _))
  have hi : StableAt w (div (sub nT qT) (const (k * 3))) env :=
    (hn.sub hq).div (stableAt_const _ _)
  have hd : StableAt w (mod (sub nT qT) (const 3)) env := (hn.sub hq).mod (stableAt_const _ _)
  unfold edgeTargetT edgeTargetNum
  simp only [denote_ite, denote_lt, denote_add, denote_const, denote_eqT,
    denote_firstAfterT k hσ hc hi hd, denote_sub, denote_div, denote_mod, getD_eq_optCode]
  by_cases h1 : nT.denote w env < qT.denote w env
  · by_cases h2 : nT.denote w env + 1 < qT.denote w env <;> simp [h1, h2]
  · simp only [h1, ite_false, Nat.lt_irrefl]
    split_ifs <;> simp_all

theorem StableAt.edgeTargetT (k : ℕ) {qT σT nT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hσ : StableAt w σT env) (hn : StableAt w nT env) :
    StableAt w (edgeTargetT k qT σT nT) env := fun extra => by
  rw [denote_edgeTargetT k (hq.extend extra) (hσ.extend extra) (hn.extend extra),
    denote_edgeTargetT k hq hσ hn, hq extra, hσ extra, hn extra]

/-- The term computing `blockSrcNum k q n`, the interval that the block edge numbered `n` leaves. -/
def blockSrcT (k : ℕ) (qT nT : Term) : Term :=
  ite (lt nT qT) nT (div (sub nT qT) (const (k * 3)))

@[simp] theorem denote_blockSrcT (k : ℕ) (qT nT : Term) (env : List ℕ) :
    (blockSrcT k qT nT).denote w env = blockSrcNum k (qT.denote w env) (nT.denote w env) := by
  simp [blockSrcT, blockSrcNum]

/-- The number of block-edge halves, `q (3k + 1) m`. -/
def halvesT (k : ℕ) (qT mT : Term) : Term := mul (mul qT (const (3 * k + 1))) mT

/-- The term computing `explicitSrcNum k q m σ j`, the vertex at which the explicit edge numbered
`j` starts. -/
def explicitSrcT (k : ℕ) (qT mT σT jT : Term) : Term :=
  ite (lt jT (halvesT k qT mT)) (blockSrcT k qT (div jT mT))
    (edgeTargetT k qT σT (div (sub jT (halvesT k qT mT)) mT))

theorem denote_explicitSrcT (k : ℕ) {qT mT σT jT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hm : StableAt w mT env) (hσ : StableAt w σT env) (hj : StableAt w jT env) :
    (explicitSrcT k qT mT σT jT).denote w env =
      explicitSrcNum k (qT.denote w env) (mT.denote w env) (σT.denote w env) (jT.denote w env) := by
  have hn : StableAt w (div (sub jT (halvesT k qT mT)) mT) env :=
    (hj.sub ((hq.mul (stableAt_const _ _)).mul hm)).div hm
  unfold explicitSrcT explicitSrcNum
  rw [denote_ite, denote_edgeTargetT k hq hσ hn]
  simp only [denote_lt, denote_blockSrcT, halvesT, denote_mul, denote_const, denote_div, denote_sub]
  by_cases h : jT.denote w env < qT.denote w env * (3 * k + 1) * mT.denote w env <;> simp [h]

theorem StableAt.explicitSrcT (k : ℕ) {qT mT σT jT : Term} {env : List ℕ}
    (hq : StableAt w qT env) (hm : StableAt w mT env) (hσ : StableAt w σT env)
    (hj : StableAt w jT env) : StableAt w (explicitSrcT k qT mT σT jT) env := fun extra => by
  rw [denote_explicitSrcT k (hq.extend extra) (hm.extend extra) (hσ.extend extra)
    (hj.extend extra), denote_explicitSrcT k hq hm hσ hj, hq extra, hm extra, hσ extra, hj extra]

/-- The term computing `explicitTgtNum k q m j`, the vertex at which the explicit edge numbered
`j` ends. -/
def explicitTgtT (k : ℕ) (qT mT jT : Term) : Term :=
  add (mul qT (const (3 * k + 2)))
    (ite (lt jT (halvesT k qT mT)) jT (sub jT (halvesT k qT mT)))

@[simp] theorem denote_explicitTgtT (k : ℕ) (qT mT jT : Term) (env : List ℕ) :
    (explicitTgtT k qT mT jT).denote w env =
      explicitTgtNum k (qT.denote w env) (mT.denote w env) (jT.denote w env) := by
  simp only [explicitTgtT, explicitTgtNum, halvesT, denote_add, denote_mul, denote_const,
    denote_ite, denote_lt, denote_sub]
  by_cases h : jT.denote w env < qT.denote w env * (3 * k + 1) * mT.denote w env <;> simp [h]

/-! ### Ports -/

/-- Whether explicit edge `j` is a port of vertex `v`. -/
def portPredT (k : ℕ) (qT mT σT vT jT : Term) : Term :=
  lt (const 0) (add (eqT (explicitSrcT k qT mT σT jT) vT) (eqT (explicitTgtT k qT mT jT) vT))

/-- The port predicate on numbers. -/
def portPred (k q m σ v j : ℕ) : Bool :=
  decide (explicitSrcNum k q m σ j = v ∨ explicitTgtNum k q m j = v)

theorem denote_portPredT (k : ℕ) {qT mT σT vT jT : Term} {env : List ℕ}
    (hq : StableAt w qT env) (hm : StableAt w mT env) (hσ : StableAt w σT env)
    (hj : StableAt w jT env) :
    (portPredT k qT mT σT vT jT).denote w env =
      (portPred k (qT.denote w env) (mT.denote w env) (σT.denote w env) (vT.denote w env)
        (jT.denote w env)).toNat := by
  unfold portPredT portPred
  simp only [denote_lt, denote_const, denote_add, denote_eqT, denote_explicitSrcT k hq hm hσ hj,
    denote_explicitTgtT]
  by_cases h1 : explicitSrcNum k (qT.denote w env) (mT.denote w env) (σT.denote w env)
      (jT.denote w env) = vT.denote w env <;>
    by_cases h2 : explicitTgtNum k (qT.denote w env) (mT.denote w env) (jT.denote w env) =
      vT.denote w env <;> simp [h1, h2]

/-- The number of ports below `lim`. -/
def portCountT (k : ℕ) (qT mT σT vT limT : Term) : Term :=
  sumT limT fun j => portPredT k qT mT σT vT j

theorem denote_portCountT (k : ℕ) {qT mT σT vT : Term} (limT : Term) {env : List ℕ}
    (hq : StableAt w qT env) (hm : StableAt w mT env) (hσ : StableAt w σT env)
    (hv : StableAt w vT env) :
    (portCountT k qT mT σT vT limT).denote w env =
      (List.range (limT.denote w env)).countP (portPred k (qT.denote w env) (mT.denote w env)
        (σT.denote w env) (vT.denote w env)) := by
  unfold portCountT
  rw [denote_sumT _ _ env (fun j => (portPred k (qT.denote w env) (mT.denote w env)
    (σT.denote w env) (vT.denote w env) j).toNat), countP_eq_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    cases portPred k (qT.denote w env) (mT.denote w env) (σT.denote w env) (vT.denote w env) j <;>
      rfl
  · intro acc j
    have hp := denote_portPredT k (vT := vT) (hq.extend [acc, j]) (hm.extend [acc, j])
      (hσ.extend [acc, j]) (stableAt_lvl (w := w) (l := env.length) (by simp))
    simp only [List.cons_append, List.nil_append] at hp
    rw [hp]
    simp [hq.cons₂, hm.cons₂, hσ.cons₂, hv.cons₂]

theorem StableAt.portCountT (k : ℕ) {qT mT σT vT limT : Term} {env : List ℕ}
    (hq : StableAt w qT env) (hm : StableAt w mT env) (hσ : StableAt w σT env)
    (hv : StableAt w vT env) (hl : StableAt w limT env) :
    StableAt w (portCountT k qT mT σT vT limT) env := fun extra => by
  rw [denote_portCountT k limT (hq.extend extra) (hm.extend extra) (hσ.extend extra)
    (hv.extend extra), denote_portCountT k limT hq hm hσ hv, hq extra, hm extra, hσ extra,
    hv extra, hl extra]

theorem idxOf_filter_range (p : ℕ → Bool) (x : ℕ) : ∀ n,
    ((List.range n).filter p).idxOf x =
      if x < n ∧ p x then (List.range x).countP p else (List.range n).countP p := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.countP_append]
    by_cases hx : x ∈ (List.range n).filter p
    · rw [List.idxOf_append_of_mem hx, ih]
      have hx' := List.mem_filter.mp hx
      have hxn : x < n := List.mem_range.mp hx'.1
      rw [ite_eq_left ⟨hxn, hx'.2⟩, ite_eq_left ⟨by omega, hx'.2⟩]
    · rw [List.idxOf_append_of_notMem hx, ← List.countP_eq_length_filter]
      have hnot : ¬ (x < n ∧ p x = true) := fun h =>
        hx (List.mem_filter.mpr ⟨List.mem_range.mpr h.1, h.2⟩)
      by_cases hxn : x = n
      · subst hxn
        by_cases hp : p x
        · simp [hp]
        · simp [hp]
      · by_cases hp : p n
        · have : ¬ (x < n + 1 ∧ p x = true) := fun h => hnot ⟨by omega, h.2⟩
          simp only [hp, List.filter_cons_of_pos, List.filter_nil, List.idxOf_cons_ne _
              (Ne.symm hxn), List.not_mem_nil,
    not_false_eq_true, List.idxOf_of_notMem, List.length_nil, Nat.succ_eq_add_one, zero_add,
        Order.lt_add_one_iff,
    List.countP_cons_of_pos, List.countP_nil, right_eq_ite_iff, and_imp]
          intro h1 h2; exact absurd ⟨lt_of_le_of_ne h1 hxn, h2⟩ hnot
        · have : ¬ (x < n + 1 ∧ p x = true) := fun h => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp h.1 with h1 | h1
            · exact hnot ⟨h1, h.2⟩
            · exact hxn h1
          simp only [hp, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
              List.filter_nil,
    List.not_mem_nil, List.idxOf_of_notMem, List.length_nil, add_zero, Order.lt_add_one_iff,
        List.countP_cons_of_neg,
    List.countP_nil, right_eq_ite_iff, and_imp]
          intro h1 h2; exact absurd ⟨lt_of_le_of_ne h1 hxn, h2⟩ hnot

/-- The position of `x` in the ports of `v` (their number when `x` is not a port). -/
def portIdxT (k : ℕ) (qT mT σT vT xT : Term) : Term :=
  ite (mul (lt xT (mul (const 2) (halvesT k qT mT))) (portPredT k qT mT σT vT xT))
    (portCountT k qT mT σT vT xT) (portCountT k qT mT σT vT (mul (const 2) (halvesT k qT mT)))

theorem denote_portIdxT (k : ℕ) {qT mT σT vT xT : Term} {env : List ℕ}
    (hq : StableAt w qT env) (hm : StableAt w mT env) (hσ : StableAt w σT env)
    (hv : StableAt w vT env) (hx : StableAt w xT env) :
    (portIdxT k qT mT σT vT xT).denote w env =
      (explicitPortsNum k (qT.denote w env) (mT.denote w env) (σT.denote w env)
        (vT.denote w env)).idxOf (xT.denote w env) := by
  unfold portIdxT explicitPortsNum
  rw [show (fun j => decide (explicitSrcNum k (qT.denote w env) (mT.denote w env)
      (σT.denote w env) j = vT.denote w env ∨ explicitTgtNum k (qT.denote w env) (mT.denote w env)
      j = vT.denote w env)) = portPred k (qT.denote w env) (mT.denote w env) (σT.denote w env)
      (vT.denote w env) from rfl, idxOf_filter_range]
  simp only [denote_ite, denote_mul, denote_lt, denote_const, denote_portPredT k hq hm hσ hx,
    denote_portCountT k _ hq hm hσ hv, halvesT]
  by_cases h1 : xT.denote w env < 2 * (qT.denote w env * (3 * k + 1) * mT.denote w env) <;>
    by_cases h2 : portPred k (qT.denote w env) (mT.denote w env) (σT.denote w env)
      (vT.denote w env) (xT.denote w env) <;> simp [h1, h2]

theorem StableAt.portIdxT (k : ℕ) {qT mT σT vT xT : Term} {env : List ℕ}
    (hq : StableAt w qT env) (hm : StableAt w mT env) (hσ : StableAt w σT env)
    (hv : StableAt w vT env) (hx : StableAt w xT env) :
    StableAt w (portIdxT k qT mT σT vT xT) env := fun extra => by
  rw [denote_portIdxT k (hq.extend extra) (hm.extend extra) (hσ.extend extra) (hv.extend extra)
    (hx.extend extra), denote_portIdxT k hq hm hσ hv hx, hq extra, hm extra, hσ extra, hv extra,
    hx extra]

/-- The number of ports of `v`. -/
theorem length_explicitPortsNum (k q m σ v : ℕ) :
    (explicitPortsNum k q m σ v).length =
      (List.range (2 * (q * (3 * k + 1) * m))).countP (portPred k q m σ v) := by
  unfold explicitPortsNum
  rw [List.countP_eq_length_filter]
  rfl

end Cslib.Complexity.NtimeDspace.LocalSim
