/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Basic
import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.CallIndex

/-!
# Incremental completion extensions and Herlihy–Wing Theorem 2 (Nonblocking)

Incremental invariants for appending pending invocations, linearizing pending operations in a
completion extension, flushing already-linearized responses into the observed history, and
**Herlihy–Wing Theorem 2** (`exists_linearizable_append_resp_of_total`, the nonblocking completion
property of linearizability for pending total operations; [HerlihyWing1990], §3.2, Theorem 2,
pp. 471–472; [SelaHerlihyPetrank2021], §5.3, Theorem 5.2, p. 9).

## Main results

* `Cslib.Distributed.ConcurrentObjects.History.append_pending_inv_extension`,
  `Cslib.Distributed.ConcurrentObjects.History.linearize_pending_in_extension`,
  `Cslib.Distributed.ConcurrentObjects.History.flush_resp_from_extension`: reusable forward
  simulation step lemmas maintaining `(H ++ R, S)` across invocation, linearization point, and
  response emission.
* `Cslib.Distributed.ConcurrentObjects.exists_linearizable_append_resp_of_total`: **Herlihy–Wing
  Theorem 2 (Nonblocking)** — any pending invocation of a total operation in a linearizable history
  admits a matching response whose append remains linearizable.

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

/-- Appending a new invocation `Event.inv p x op` for an idle process `p` (whose subhistory in `H`
consists solely of completed calls `cs_p` and has no pending response in `R`) preserves
well-formedness of `(H ++ [Event.inv p x op]) ++ R`, leaves `complete` unchanged, and preserves
real-time precedence into `S`. -/
theorem History.append_pending_inv_extension {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R S : History P Op Resp} {p : P} {x : Obj} (op : Op x)
    {cs_p : List (OpCall P Op Resp)}
    (hwf' : History.WellFormed (H ++ R))
    (heqS : History.Equivalent (History.complete (H ++ R)) S)
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ → History.prec H e₀ e₁ → History.prec S e₀ e₁)
    (hHp : History.procSubhistory H p = cs_p.flatMap OpCall.toEvents)
    (hRp_nil : History.procSubhistory R p = []) :
    let H₁ := H ++ [Event.inv p x op]
    History.WellFormed (H₁ ++ R) ∧
      History.Equivalent (History.complete (H₁ ++ R)) S ∧
      ∀ e₀ e₁, History.IsCompletedOp (H₁ ++ R) e₀ →
        History.IsCompletedOp (H₁ ++ R) e₁ → History.prec H₁ e₀ e₁ → History.prec S e₀ e₁ := by
  intro H₁
  have hwf_H₁R : History.WellFormed (H₁ ++ R) := fun q => by
    simp only [H₁, List.append_assoc, History.procSubhistory_append, History.procSubhistory_cons,
      Event.proc_inv, History.procSubhistory_nil]
    rcases eq_or_ne p q with rfl | hqp
    · simp only [↓reduceIte, hRp_nil, List.append_nil, hHp]
      exact History.isSequential_flatMap_toEvents_append_inv cs_p p x op
    · simpa only [hqp, ↓reduceIte, List.nil_append, ← History.procSubhistory_append] using hwf' q
  have hcomp_eq : History.Equivalent (History.complete (H₁ ++ R)) (History.complete (H ++ R)) :=
    fun q => by
      simp only [H₁, History.procSubhistory_complete, List.append_assoc,
        History.procSubhistory_append, History.procSubhistory_cons, Event.proc_inv,
        History.procSubhistory_nil]
      rcases eq_or_ne p q with rfl | hqp
      · simp only [↓reduceIte, hRp_nil, List.append_nil, hHp, History.complete_flatMap_append_inv]
        exact (History.complete_eq_self_of_isSequential_even
          (History.isSequential_flatMap_toEvents cs_p)
          (by rw [History.length_flatMap_toEvents]; omega)).symm
      · simp only [hqp, ↓reduceIte, List.nil_append]
  refine ⟨hwf_H₁R, hcomp_eq.trans heqS, fun e₀ e₁ hc₀ hc₁ ⟨r₀, i₁, hr₀, hi₁, hri⟩ => ?_⟩
  have hc_HR {e} (hc : History.IsCompletedOp (H₁ ++ R) e) : History.IsCompletedOp (H ++ R) e :=
    (History.isCompletedOp_complete_iff hwf' e).mp
      ((hcomp_eq.isCompletedOp_iff e).mp ((History.isCompletedOp_complete_iff hwf_H₁R e).mpr hc))
  have hc₁_HR := hc_HR hc₁
  have hlt_i₁ : 2 * e₁.idx < (History.procSubhistory H e₁.proc).length := by
    by_cases hep : e₁.proc = p
    · have hlen := (History.isCompletedOp_iff_lt_length (H ++ R) e₁).mp hc₁_HR
      simp only [hep, History.procSubhistory_append, hRp_nil, List.append_nil, hHp,
        History.length_flatMap_toEvents] at hlen ⊢
      omega
    · have hlen₁ := (History.nthProcPos_isSome_iff e₁.proc H₁ (2 * e₁.idx)).mp
        (by dsimp only [History.invPos] at hi₁; rw [hi₁]; rfl)
      simpa only [H₁, History.procSubhistory_append, History.procSubhistory_cons, Event.proc_inv,
        Ne.symm hep, ↓reduceIte, History.procSubhistory_nil, List.append_nil] using hlen₁
  have hi₁_H : History.invPos H e₁ = some i₁ := by
    rwa [History.invPos, History.nthProcPos_append_left [Event.inv p x op] hlt_i₁] at hi₁
  obtain ⟨hi₁_lt_H, _⟩ := History.nthProcPos_lt_length hi₁_H
  exact hprecS e₀ e₁ (hc_HR hc₀) hc₁_HR
    ⟨r₀, i₁, History.nthProcPos_of_append_lt hr₀ (by omega), hi₁_H, hri⟩

/-- Linearizing an uncompleted pending invocation `Event.inv p x op` of process `p` by appending
`Event.resp p x res` to the response extension `R` and `[Event.inv p x op, Event.resp p x res]` to
the sequential witness `S` preserves well-formedness, sequentiality, equivalence of `complete`, and
real-time precedence `<_H`. -/
theorem History.linearize_pending_in_extension {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R S : History P Op Resp} {p : P} {x : Obj} {op : Op x} (res : Resp x)
    {cs_p : List (OpCall P Op Resp)}
    (hR_resp : History.IsRespList R)
    (hwf' : History.WellFormed (H ++ R))
    (hseqS : History.IsSequential S)
    (heqS : History.Equivalent (History.complete (H ++ R)) S)
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ → History.prec H e₀ e₁ → History.prec S e₀ e₁)
    (hHp : History.procSubhistory H p = cs_p.flatMap OpCall.toEvents ++ [Event.inv p x op])
    (hRp_nil : History.procSubhistory R p = []) :
    let R₁ := R ++ [Event.resp p x res]
    let S' := S ++ [Event.inv p x op, Event.resp p x res]
    History.IsRespList R₁ ∧
      History.WellFormed (H ++ R₁) ∧
      History.IsSequential S' ∧
      History.Equivalent (History.complete (H ++ R₁)) S' ∧
      ∀ e₀ e₁, History.IsCompletedOp (H ++ R₁) e₀ →
        History.IsCompletedOp (H ++ R₁) e₁ → History.prec H e₀ e₁ → History.prec S' e₀ e₁ := by
  intro R₁ S'
  have hR₁_resp : History.IsRespList R₁ := fun e hm =>
    (List.mem_append.mp hm).elim (hR_resp e) fun h => by rw [List.mem_singleton.mp h]; rfl
  have hpair_seq : History.IsSequential
      (cs_p.flatMap OpCall.toEvents ++ [Event.inv p x op, Event.resp p x res]) :=
    History.isSequential_append_pair (History.isSequential_flatMap_toEvents cs_p)
      (by rw [History.length_flatMap_toEvents]; omega) p x op res
  have hwf_HR₁ : History.WellFormed (H ++ R₁) := fun q => by
    simp only [R₁, ← List.append_assoc, History.procSubhistory_append, History.procSubhistory_cons,
      Event.proc_resp, History.procSubhistory_nil]
    rcases eq_or_ne p q with rfl | hqp
    · simpa only [↓reduceIte, hRp_nil, List.append_nil, hHp, List.append_assoc, List.cons_append,
        List.nil_append] using hpair_seq
    · simpa only [hqp, ↓reduceIte, List.append_nil, ← History.procSubhistory_append] using hwf' q
  have hseqS' : History.IsSequential S' :=
    History.isSequential_append_pair hseqS
      (History.even_length_of_equivalent_complete hwf' hseqS heqS) p x op res
  have heqS' : History.Equivalent (History.complete (H ++ R₁)) S' := fun q => by
    simp only [R₁, S', History.procSubhistory_complete, History.procSubhistory_append,
      History.procSubhistory_cons, Event.proc_inv, Event.proc_resp, History.procSubhistory_nil]
    rcases eq_or_ne p q with rfl | hqp
    · simp only [↓reduceIte, hRp_nil, List.nil_append, hHp, ← heqS p,
        History.procSubhistory_complete, History.procSubhistory_append, List.append_nil,
        History.complete_flatMap_append_inv, List.append_assoc, List.cons_append]
      exact History.complete_eq_self_of_isSequential_even hpair_seq (by
        simp only [List.length_append, History.length_flatMap_toEvents, List.length_cons,
          List.length_nil]
        omega)
    · simpa only [hqp, ↓reduceIte, List.append_nil, ← History.procSubhistory_append,
        ← History.procSubhistory_complete] using heqS q
  refine ⟨hR₁_resp, hwf_HR₁, hseqS', heqS', fun e₀ e₁ _ hc₁ ⟨r₀, i₁, hr₀_H, hi₁_H, hri⟩ => ?_⟩
  have hc₀_HR : History.IsCompletedOp (H ++ R) e₀ := by
    rw [History.isCompletedOp_iff_lt_length, History.procSubhistory_append, List.length_append]
    exact Nat.lt_add_right _ ((History.nthProcPos_isSome_iff e₀.proc H (2 * e₀.idx + 1)).mp
      (by rw [← History.respPos, hr₀_H]; rfl))
  have hc₀_S : History.IsCompletedOp S e₀ :=
    (heqS.isCompletedOp_iff e₀).mp ((History.isCompletedOp_complete_iff hwf' e₀).mpr hc₀_HR)
  have hresp_S' {rS : ℕ} (hrS : History.respPos S e₀ = some rS) :
      History.respPos S' e₀ = some rS := by
    rwa [History.respPos,
      History.nthProcPos_append_left _ ((History.isCompletedOp_iff_lt_length S e₀).mp hc₀_S)]
  by_cases hc₁_HR : History.IsCompletedOp (H ++ R) e₁
  · obtain ⟨rS, iS, hrS, hiS, hltS⟩ := hprecS e₀ e₁ hc₀_HR hc₁_HR ⟨r₀, i₁, hr₀_H, hi₁_H, hri⟩
    have hc₁_S : History.IsCompletedOp S e₁ :=
      (heqS.isCompletedOp_iff e₁).mp ((History.isCompletedOp_complete_iff hwf' e₁).mpr hc₁_HR)
    exact ⟨rS, iS, hresp_S' hrS, by
      rwa [History.invPos, History.nthProcPos_append_left _ (Nat.lt_of_succ_lt
        ((History.isCompletedOp_iff_lt_length S e₁).mp hc₁_S))], hltS⟩
  · obtain ⟨rS₀, hrS₀⟩ := Option.isSome_iff_exists.mp hc₀_S
    have he₁_p : e₁.proc = p := Decidable.byContradiction fun hne => hc₁_HR <| by
      simpa only [R₁, History.isCompletedOp_iff_lt_length, History.procSubhistory_append,
        History.procSubhistory_cons, Event.proc_resp, Ne.symm hne, ↓reduceIte,
        History.procSubhistory_nil, List.append_nil] using hc₁
    have he₁_idx : e₁.idx = cs_p.length := by
      have hlen₁ := (History.isCompletedOp_iff_lt_length _ e₁).mp hc₁
      have hlen₀ : ¬ (2 * e₁.idx + 1 < (History.procSubhistory (H ++ R) e₁.proc).length) :=
        fun h => hc₁_HR ((History.isCompletedOp_iff_lt_length _ e₁).mpr h)
      rw [he₁_p, History.procSubhistory_append, hRp_nil, List.append_nil, hHp,
        List.length_append, History.length_flatMap_toEvents, List.length_singleton] at hlen₀
      simp only [R₁, he₁_p, History.procSubhistory_append, hRp_nil, List.nil_append, hHp,
        History.procSubhistory_cons, Event.proc_resp, ↓reduceIte, History.procSubhistory_nil,
        List.length_append, History.length_flatMap_toEvents, List.length_cons,
        List.length_nil] at hlen₁
      omega
    have hSp_len : (History.procSubhistory S p).length = 2 * cs_p.length := by
      rw [← heqS p, History.procSubhistory_complete, History.procSubhistory_append,
        hRp_nil, List.append_nil, hHp, History.complete_flatMap_append_inv,
        History.length_flatMap_toEvents]
    have hiS' : History.invPos S' e₁ = some S.length := by
      simp only [S', History.invPos, he₁_p, he₁_idx]
      rw [History.nthProcPos_append_right S _ (by rw [hSp_len]), hSp_len, Nat.sub_self]
      simp only [History.nthProcPos, List.nthFilterPos, Event.proc_inv, decide_true, ↓reduceIte,
        Option.map_some, Nat.zero_add]
    exact ⟨rS₀, S.length, hresp_S' hrS₀, hiS', (History.nthProcPos_lt_length hrS₀).1⟩

/-- Moving an already-linearized pending response `Event.resp p x res` of process `p` from the
extension `R` into `H₁ := H ++ [Event.resp p x res]` (leaving `R' := R.filter (·.proc ≠ p)`)
preserves every process subhistory of `H₁ ++ R'` and maintains real-time precedence into `S`. -/
theorem History.flush_resp_from_extension {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R S : History P Op Resp} {p : P} {x : Obj} {res : Resp x}
    (hR_resp : History.IsRespList R)
    (hwf' : History.WellFormed (H ++ R))
    (heqS : History.Equivalent (History.complete (H ++ R)) S)
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ → History.prec H e₀ e₁ → History.prec S e₀ e₁)
    (hRp_eq : History.procSubhistory R p = [Event.resp p x res]) :
    let H₁ := H ++ [Event.resp p x res]
    let R' := R.filter fun e => decide (e.proc ≠ p)
    History.IsRespList R' ∧
      (∀ q, History.procSubhistory (H₁ ++ R') q = History.procSubhistory (H ++ R) q) ∧
      History.WellFormed (H₁ ++ R') ∧
      History.Equivalent (History.complete (H₁ ++ R')) S ∧
      ∀ e₀ e₁, History.IsCompletedOp (H₁ ++ R') e₀ →
        History.IsCompletedOp (H₁ ++ R') e₁ → History.prec H₁ e₀ e₁ → History.prec S e₀ e₁ := by
  intro H₁ R'
  have hR'_resp : History.IsRespList R' :=
    fun e hm => hR_resp e (List.mem_filter.mp hm).1
  have hproc_eq_all : ∀ q, History.procSubhistory (H₁ ++ R') q =
      History.procSubhistory (H ++ R) q := fun q => by
    simp only [H₁, R', List.append_assoc, History.procSubhistory_append,
      History.procSubhistory_cons, Event.proc_resp, History.procSubhistory_nil]
    rcases eq_or_ne p q with rfl | hqp
    · rw [hRp_eq]
      simp +contextual [History.procSubhistory, List.filter_filter]
    · simp only [hqp, ↓reduceIte, List.nil_append, History.procSubhistory, List.filter_filter]
      exact congrArg (List.filter _ H ++ ·)
        (List.filter_congr fun e _ => by by_cases h : e.proc = q <;> simp [h, Ne.symm hqp])
  have hwf_H₁R' : History.WellFormed (H₁ ++ R') := fun q => hproc_eq_all q ▸ hwf' q
  have heq_H₁R' : History.Equivalent (History.complete (H₁ ++ R')) S := fun q => by
    simpa only [History.procSubhistory_complete, hproc_eq_all q] using heqS q
  refine ⟨hR'_resp, hproc_eq_all, hwf_H₁R', heq_H₁R',
    fun e₀ e₁ hc₀ hc₁ ⟨r₀, i₁, hr₀, hi₁, hri⟩ => ?_⟩
  have hc_HR {e} (hc : History.IsCompletedOp (H₁ ++ R') e) : History.IsCompletedOp (H ++ R) e :=
    (History.isCompletedOp_iff_lt_length _ e).mpr
      (hproc_eq_all e.proc ▸ (History.isCompletedOp_iff_lt_length _ e).mp hc)
  have hi₁_lt : i₁ < H.length := by
    obtain ⟨hlt_H₁, _⟩ := History.nthProcPos_lt_length hi₁
    simp only [H₁, List.length_append, List.length_singleton] at hlt_H₁
    by_cases heq_len : i₁ = H.length
    · have hseq_q : History.IsSequential (History.procSubhistory H₁ e₁.proc) :=
        History.isSequential_append_left (History.procSubhistory_append H₁ R' _ ▸ hwf_H₁R' e₁.proc)
      have hev_eq : (History.procSubhistory H₁ e₁.proc)[2 * e₁.idx]? = some (.resp p x res) := by
        simpa [H₁, heq_len] using (History.nthProcPos_getElem? hi₁).symm
      exact Bool.noConfusion (isSequential_getElem?_even_isResp_false hseq_q hev_eq)
    · omega
  exact hprecS e₀ e₁ (hc_HR hc₀) (hc_HR hc₁)
    ⟨r₀, i₁, History.nthProcPos_of_append_lt hr₀ (by omega),
      History.nthProcPos_of_append_lt hi₁ hi₁_lt, hri⟩

/-- **Herlihy–Wing Theorem 2 (Nonblocking Property of Linearizability)**
([HerlihyWing1990], §3.2, Theorem 2, pp. 471–472; amended L2 proof of [SelaHerlihyPetrank2021],
§5.3, Theorem 5.2, p. 9): if process `p` has a pending invocation of a total operation `op : Op x`
in a linearizable history `H`, then there exists a response `res : Resp x` such that
`H ++ [Event.resp p x res]` is also linearizable. -/
theorem exists_linearizable_append_resp_of_total {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {spec : ∀ y, SeqSpec P Op Resp y}
    {H : History P Op Resp} {p : P} {x : Obj} {op : Op x}
    (hlin : IsLinearizable spec H) (htot : (spec x).IsTotalOp op)
    (hpending : ∃ cs : List (OpCall P Op Resp),
      History.procSubhistory H p = cs.flatMap OpCall.toEvents ++ [.inv p x op]) :
    ∃ res : Resp x, IsLinearizable spec (H ++ [.resp p x res]) := by
  obtain ⟨cs_p, hHp⟩ := hpending
  obtain ⟨H', ⟨R, hR_resp, rfl, hwf'⟩, S, hseqS, hlegS, heqS, hprecS⟩ := hlin
  have hwfH : History.WellFormed H := fun q =>
    History.isSequential_append_left (History.procSubhistory_append H R q ▸ hwf' q)
  have hresp_Rp : History.IsRespList (History.procSubhistory R p) :=
    fun e hm => hR_resp e (List.mem_filter.mp hm).1
  rcases History.isRespList_le_one_of_isSequential (hwfH p) hresp_Rp
      (History.procSubhistory_append H R p ▸ hwf' p) with
    hRp_nil | ⟨cs', p', x', op', res, hL_eq, hRp_eq⟩
  · have hev_Sx : (History.objSubhistory S x).length % 2 = 0 := by
      have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
      obtain ⟨csS, rfl⟩ := History.exists_calls_of_isSequential_even hseqS hevS
      rw [History.objSubhistory_flatMap_toEvents, History.length_flatMap_toEvents]
      omega
    obtain ⟨res, hSx_ext⟩ := htot (History.objSubhistory S x) (hlegS x) hev_Sx p
    obtain ⟨hR₁_resp, hwf_HR₁, hseqS', heqS', hprecS'⟩ :=
      History.linearize_pending_in_extension res hR_resp hwf' hseqS heqS hprecS hHp hRp_nil
    have hR₁p : History.procSubhistory (R ++ [Event.resp p x res]) p = [Event.resp p x res] := by
      simp only [History.procSubhistory_append, hRp_nil, List.nil_append,
        History.procSubhistory_cons, Event.proc_resp, ↓reduceIte, History.procSubhistory_nil]
    obtain ⟨hR'_resp, _, hwf_fl, heq_fl, hprec_fl⟩ :=
      History.flush_resp_from_extension hR₁_resp hwf_HR₁ heqS' hprecS' hR₁p
    refine ⟨res, _, ⟨_, hR'_resp, rfl, hwf_fl⟩, _, hseqS', ?_, heq_fl, hprec_fl⟩
    intro y
    rcases eq_or_ne x y with rfl | hxy
    · simpa [History.objSubhistory_append, History.objSubhistory_cons] using hSx_ext
    · simpa [History.objSubhistory_append, History.objSubhistory_cons, hxy] using hlegS y
  · have hm : .resp p' x' res ∈ History.procSubhistory R p := hRp_eq ▸ List.mem_singleton_self _
    obtain rfl : p' = p := of_decide_eq_true (List.mem_filter.mp hm).2
    have hlast : (Event.inv p' x' op' : Event P Op Resp) = Event.inv p' x op := by
      simpa only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast?_singleton,
        Option.some.injEq] using congrArg List.getLast? (hL_eq.symm.trans hHp)
    obtain ⟨-, rfl, -⟩ := Event.inv.inj hlast
    obtain ⟨hR'_resp, _, hwf_fl, heq_fl, hprec_fl⟩ :=
      History.flush_resp_from_extension hR_resp hwf' heqS hprecS hRp_eq
    exact ⟨res, _, ⟨_, hR'_resp, rfl, hwf_fl⟩, S, hseqS, hlegS, heq_fl, hprec_fl⟩

end Cslib.Distributed.ConcurrentObjects
