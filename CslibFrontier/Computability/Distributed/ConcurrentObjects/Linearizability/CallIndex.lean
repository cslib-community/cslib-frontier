/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Basic

/-!
# Sequential call indexing and completion helpers

Shared internal lemmas on `History`, `OpCall`, `nthProcPos`, and sequential call indexing (`opIdAt`,
`countProcCalls`) used across the locality, nonblocking, and register-separation modules.

## Main definitions

* `Cslib.Distributed.ConcurrentObjects.countProcCalls`,
  `Cslib.Distributed.ConcurrentObjects.opIdAt`: per-process call counts and operation identifier of
  the `j`-th call in a sequential `OpCall` list.

## Main results

* `Cslib.Distributed.ConcurrentObjects.History.even_length_of_equivalent_complete`,
  `Cslib.Distributed.ConcurrentObjects.History.isRespList_le_one_of_isSequential`: parity of
  sequential histories equivalent to `complete H` and classification of response-only extensions of
  sequential histories.
* `Cslib.Distributed.ConcurrentObjects.prec_flatMap_toEvents_opIdAt_iff`,
  `Cslib.Distributed.ConcurrentObjects.exists_opIdAt_of_lt_countProcCalls`: order isomorphism
  between call-list indices `j` and real-time precedence `<_S` on `calls.flatMap OpCall.toEvents`.
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

namespace History

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- Every event retained in `complete M` belongs to `M`. -/
theorem mem_of_mem_complete [DecidableEq P] {M : History P Op Resp} {e : Event P Op Resp}
    (hm : e ∈ complete M) : e ∈ M := by
  induction M with
  | nil => exact hm
  | cons a rest ih =>
    cases a with
    | inv _ _ _ =>
      simp only [complete] at hm
      split at hm
      · exact List.mem_cons.mpr ((List.mem_cons.mp hm).imp_right ih)
      · exact List.mem_cons_of_mem _ (ih hm)
    | resp _ _ _ => exact List.mem_cons.mpr ((List.mem_cons.mp hm).imp_right ih)

/-- Prefix closure of `IsSequential` under `++`. -/
theorem isSequential_append_left :
    ∀ {L₁ L₂ : History P Op Resp}, IsSequential (L₁ ++ L₂) → IsSequential L₁
  | [], _, _ | [.inv _ _ _], _, _ => trivial
  | [.resp _ _ _], [], h | [.resp _ _ _], _ :: _, h
  | .resp _ _ _ :: _ :: _, _, h | .inv _ _ _ :: .inv _ _ _ :: _, _, h => False.elim h
  | .inv _ _ _ :: .resp _ _ _ :: _, _, h => ⟨h.1, h.2.1, isSequential_append_left h.2.2⟩

/-- Completed `OpCall`s followed by a single pending invocation form a sequential history. -/
theorem isSequential_flatMap_toEvents_append_inv (cs : List (OpCall P Op Resp)) (p : P) (x : Obj)
    (op : Op x) : IsSequential (cs.flatMap OpCall.toEvents ++ [.inv p x op]) := by
  induction cs with
  | nil => trivial
  | cons _ _ ih => exact ⟨rfl, rfl, ih⟩

/-- `complete` drops a trailing pending invocation after a list of completed `OpCall`s. -/
theorem complete_flatMap_append_inv [DecidableEq P] (cs : List (OpCall P Op Resp)) (q : P)
    (y : Obj) (op : Op y) :
    complete (cs.flatMap OpCall.toEvents ++ [.inv q y op]) = cs.flatMap OpCall.toEvents := by
  induction cs with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, complete, List.any_nil, Bool.false_eq_true,
      ↓reduceIte]
  | cons c cs' ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append, complete,
      List.any_cons, Event.proc_resp, decide_true, Bool.true_or, ↓reduceIte]
    exact congrArg (fun t => .inv c.proc c.obj c.op :: .resp c.proc c.obj c.res :: t) ih

/-- Completing a well-formed history preserves the set of completed operations. -/
theorem isCompletedOp_complete_iff [DecidableEq P] {M : History P Op Resp} (hwf : WellFormed M)
    (e : OpId P) : IsCompletedOp (complete M) e ↔ IsCompletedOp M e := by
  rw [isCompletedOp_iff_lt_length, isCompletedOp_iff_lt_length, procSubhistory_complete]
  have hseq := hwf e.proc
  rcases isSequential_decomp hseq with ⟨cs, hcs⟩ | ⟨cs, q, y, op, hcs⟩
  · rw [hcs, complete_eq_self_of_isSequential_even (hcs ▸ hseq)
      (by rw [length_flatMap_toEvents]; omega)]
  · rw [hcs, complete_flatMap_append_inv, List.length_append, length_flatMap_toEvents,
      List.length_singleton]
    omega

/-- Any sequential history equivalent to `complete H` (for well-formed `H`) has even length. -/
theorem even_length_of_equivalent_complete [DecidableEq P] {H S : History P Op Resp}
    (hwf : WellFormed H) (hseq : IsSequential S) (heq : Equivalent (complete H) S) :
    S.length % 2 = 0 := by
  rcases isSequential_decomp hseq with ⟨cs, rfl⟩ | ⟨cs, p, x, op, rfl⟩
  · rw [length_flatMap_toEvents]; omega
  · obtain ⟨_, hev_p⟩ := complete_isSequential (hwf p)
    rw [← procSubhistory_complete, heq p] at hev_p
    simp only [procSubhistory_append, procSubhistory_flatMap_toEvents, procSubhistory_cons,
      Event.proc_inv, ↓reduceIte, procSubhistory_nil, List.length_append, length_flatMap_toEvents,
      List.length_singleton] at hev_p
    omega

/-- An even-length sequential history admits no nonempty response-only sequential suffix. -/
theorem isRespList_eq_nil_of_isSequential_even {L R : History P Op Resp}
    (hseq : IsSequential L) (heven : L.length % 2 = 0) (hresp : IsRespList R)
    (hseq_app : IsSequential (L ++ R)) : R = [] := by
  match L with
  | [] =>
    cases R with
    | nil => rfl
    | cons e rs =>
      cases e with
      | inv _ _ _ => exact Bool.noConfusion (hresp _ List.mem_cons_self)
      | resp _ _ _ =>
        simp only [List.nil_append] at hseq_app
        cases rs <;> exact False.elim hseq_app
  | [.inv _ _ _] => simp only [List.length_singleton] at heven; omega
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv _ _ _ :: .resp _ _ _ :: _ =>
    simp only [List.length_cons] at heven
    exact isRespList_eq_nil_of_isSequential_even hseq.2.2 (by omega) hresp hseq_app.2.2

/-- A response-only sequential extension `R` of a sequential history `L` is either empty or a single
matching response to `L`'s trailing pending invocation. -/
theorem isRespList_le_one_of_isSequential {L R : History P Op Resp}
    (hseq : IsSequential L) (hresp : IsRespList R) (hseq_app : IsSequential (L ++ R)) :
    R = [] ∨ ∃ (cs : List (OpCall P Op Resp)) (p : P) (x : Obj) (op : Op x) (res : Resp x),
      L = cs.flatMap OpCall.toEvents ++ [.inv p x op] ∧ R = [.resp p x res] := by
  rcases isSequential_decomp hseq with ⟨cs, rfl⟩ | ⟨cs, p, x, op, rfl⟩
  · exact Or.inl (isRespList_eq_nil_of_isSequential_even hseq
      (by rw [length_flatMap_toEvents]; omega) hresp hseq_app)
  · cases R with
    | nil => exact Or.inl rfl
    | cons e rs =>
      cases e with
      | inv _ _ _ => exact Bool.noConfusion (hresp _ List.mem_cons_self)
      | resp q y res =>
        right
        have hseq' : IsSequential (cs.flatMap OpCall.toEvents ++
            (.inv p x op :: .resp q y res :: rs)) := by
          simpa only [List.append_assoc, List.singleton_append] using hseq_app
        have htail : IsSequential (.inv p x op :: .resp q y res :: rs) := by
          clear hseq hseq_app
          induction cs with
          | nil => exact hseq'
          | cons _ _ ih => exact ih hseq'.2.2
        obtain ⟨rfl, rfl, hrs⟩ := htail
        cases rs with
        | nil => exact ⟨cs, p, x, op, res, rfl, rfl⟩
        | cons e' rs' =>
          cases e' with
          | inv _ _ _ =>
            exact Bool.noConfusion (hresp _ (List.mem_cons_of_mem _ List.mem_cons_self))
          | resp _ _ _ => cases rs' <;> exact False.elim hrs

/-- `nthProcPos p H n` is `some` iff `n < (H | p).length`. -/
theorem nthProcPos_isSome_iff [DecidableEq P] (p : P) (H : History P Op Resp) (n : ℕ) :
    (nthProcPos p H n).isSome = true ↔ n < (procSubhistory H p).length :=
  List.nthFilterPos_isSome_iff (fun e : Event P Op Resp => decide (e.proc = p)) H n

/-- Bounds and process projection at `nthProcPos p H n = some pos`. -/
theorem nthProcPos_lt_length [DecidableEq P] {p : P} {H : History P Op Resp} {n pos : ℕ}
    (h : nthProcPos p H n = some pos) : pos < H.length ∧ H[pos]?.map Event.proc = some p := by
  obtain ⟨hlt, _, hpr⟩ := List.nthFilterPos_lt_length h
  rw [List.getElem?_eq_getElem hlt] at hpr ⊢
  exact ⟨hlt, congrArg some (of_decide_eq_true (Option.some.inj hpr))⟩

/-- Lookup at `nthProcPos p H n = some pos` agrees with `(H | p)[n]?`. -/
theorem nthProcPos_getElem? [DecidableEq P] {p : P} {H : History P Op Resp} {n pos : ℕ}
    (h : nthProcPos p H n = some pos) : H[pos]? = (procSubhistory H p)[n]? :=
  (List.nthFilterPos_lt_length h).2.1

/-- `nthProcPos p H` is strictly monotone in the rank `m < n`. -/
theorem nthProcPos_strictMono [DecidableEq P] {p : P} {H : History P Op Resp} {m n i j : ℕ}
    (hmn : m < n) (hm : nthProcPos p H m = some i) (hn : nthProcPos p H n = some j) : i < j :=
  List.nthFilterPos_strictMono hmn hm hn

/-- `nthProcPos` on `H₁ ++ H₂` for ranks within `H₁ | p`. -/
theorem nthProcPos_append_left [DecidableEq P] {p : P} {H₁ : History P Op Resp}
    (H₂ : History P Op Resp) {n : ℕ} (hn : n < (procSubhistory H₁ p).length) :
    nthProcPos p (H₁ ++ H₂) n = nthProcPos p H₁ n :=
  List.nthFilterPos_append_left H₂ hn

/-- `nthProcPos` on `H₁ ++ H₂` for ranks at or beyond `(H₁ | p).length`. -/
theorem nthProcPos_append_right [DecidableEq P] {p : P} (H₁ H₂ : History P Op Resp) {n : ℕ}
    (hn : (procSubhistory H₁ p).length ≤ n) :
    nthProcPos p (H₁ ++ H₂) n =
      (nthProcPos p H₂ (n - (procSubhistory H₁ p).length)).map (· + H₁.length) :=
  List.nthFilterPos_append_right H₁ H₂ hn

/-- Any `nthProcPos` match in `H₁ ++ H₂` landing before `H₁.length` comes from `H₁`. -/
theorem nthProcPos_of_append_lt [DecidableEq P] {p : P} {H₁ H₂ : History P Op Resp}
    {n pos : ℕ} (h : nthProcPos p (H₁ ++ H₂) n = some pos) (hlt : pos < H₁.length) :
    nthProcPos p H₁ n = some pos :=
  List.nthFilterPos_of_append_lt h hlt

end History

section CallIndexing

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- `List.flatMap OpCall.toEvents` is injective on call lists. -/
theorem flatMap_toEvents_injective :
    ∀ {cs₁ cs₂ : List (OpCall P Op Resp)},
      cs₁.flatMap OpCall.toEvents = cs₂.flatMap OpCall.toEvents → cs₁ = cs₂
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by
    simp only [List.flatMap_nil, List.flatMap_cons, OpCall.toEvents, List.cons_append] at h
    nomatch h
  | ⟨_, _, _, _⟩ :: rest₁, ⟨_, _, _, _⟩ :: rest₂, h => by
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    rcases h with ⟨hinv, hresp, hrest⟩
    cases hinv
    cases hresp
    exact congrArg _ (flatMap_toEvents_injective hrest)

/-- Even positions `2 * k` of `cs.flatMap OpCall.toEvents` hold the invocation of `cs[k]`. -/
theorem flatMap_toEvents_getElem?_even :
    ∀ (cs : List (OpCall P Op Resp)) (k : ℕ) (hk : k < cs.length),
      (cs.flatMap OpCall.toEvents)[2 * k]? = some (.inv cs[k].proc cs[k].obj cs[k].op)
  | [], _, hk => by simp only [List.length_nil] at hk; omega
  | _ :: _, 0, _ => by
    simp only [Nat.mul_zero, List.flatMap_cons, OpCall.toEvents, List.cons_append,
      List.getElem?_cons_zero, List.getElem_cons_zero]
  | _ :: rest, k + 1, hk => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem_cons_succ,
      flatMap_toEvents_getElem?_even rest k (Nat.lt_of_succ_lt_succ hk)]

/-- Every event at an even index `2 * k` of a sequential history is an invocation
(`isResp = false`). -/
theorem isSequential_getElem?_even_isResp_false {L : History P Op Resp} {k : ℕ}
    {ev : Event P Op Resp} (hseq : History.IsSequential L) (hget : L[2 * k]? = some ev) :
    ev.isResp = false := by
  rcases History.isSequential_decomp hseq with ⟨cs, rfl⟩ | ⟨cs, p, x, op, rfl⟩
  · have hk : k < cs.length := by
      have := (List.getElem?_eq_some_iff.mp hget).1
      rw [History.length_flatMap_toEvents] at this; omega
    rw [flatMap_toEvents_getElem?_even cs k hk] at hget
    exact Option.some.inj hget ▸ rfl
  · rw [List.getElem?_append, History.length_flatMap_toEvents] at hget
    split_ifs at hget with hk
    · rw [flatMap_toEvents_getElem?_even cs k (by omega)] at hget
      exact Option.some.inj hget ▸ rfl
    · rw [List.getElem?_singleton] at hget
      split_ifs at hget
      exact Option.some.inj hget ▸ rfl

/-- Number of calls in `calls` invoked by process `p`. -/
@[expose]
def countProcCalls [DecidableEq P] (p : P) (calls : List (OpCall P Op Resp)) : ℕ :=
  (calls.filter fun c => decide (c.proc = p)).length

@[simp]
theorem countProcCalls_nil [DecidableEq P] (p : P) :
    countProcCalls p ([] : List (OpCall P Op Resp)) = 0 :=
  rfl

theorem countProcCalls_cons [DecidableEq P] (p : P) (c : OpCall P Op Resp)
    (rest : List (OpCall P Op Resp)) :
    countProcCalls p (c :: rest) =
      if c.proc = p then countProcCalls p rest + 1 else countProcCalls p rest := by
  simp only [countProcCalls, List.filter]
  by_cases h : c.proc = p <;> simp only [h, decide_true, decide_false, ↓reduceIte, List.length_cons]

/-- Per-process `OpId` of the `j`-th completed call in `calls`. -/
@[expose]
def opIdAt [DecidableEq P] (calls : List (OpCall P Op Resp)) (j : ℕ)
    (_hj : j < calls.length) : OpId P :=
  ⟨calls[j].proc, countProcCalls calls[j].proc (calls.take j)⟩

/-- Filtered positions in `calls.flatMap OpCall.toEvents` of the invocation and response of
`calls[k]` whenever `pred calls[k] = true`. -/
theorem nthFilterPos_flatMap_toEvents (pred : OpCall P Op Resp → Bool)
    (evPred : Event P Op Resp → Bool)
    (hinv_p : ∀ c : OpCall P Op Resp, evPred (.inv c.proc c.obj c.op) = pred c)
    (hresp_p : ∀ c : OpCall P Op Resp, evPred (.resp c.proc c.obj c.res) = pred c)
    (calls : List (OpCall P Op Resp)) (k : ℕ) (hk : k < calls.length)
    (hpk : pred calls[k] = true) :
    List.nthFilterPos evPred (calls.flatMap OpCall.toEvents)
        (2 * ((calls.take k).filter pred).length) = some (2 * k) ∧
      List.nthFilterPos evPred (calls.flatMap OpCall.toEvents)
        (2 * ((calls.take k).filter pred).length + 1) = some (2 * k + 1) := by
  induction calls generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons c rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hpk
      simp only [List.take_zero, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
        List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
        List.nthFilterPos_cons_zero_of_true _ ((hinv_p c).trans hpk),
        List.nthFilterPos_cons_succ_of_true _ 0 ((hinv_p c).trans hpk),
        List.nthFilterPos_cons_zero_of_true _ ((hresp_p c).trans hpk), Option.map_some, and_self]
    | succ k' =>
      obtain ⟨hinv, hresp⟩ := ih k' (Nat.lt_of_succ_lt_succ hk) hpk
      simp only [List.take_succ_cons, List.flatMap_cons, OpCall.toEvents, List.cons_append,
        List.nil_append]
      cases hpc : pred c
      · simp only [List.filter_cons_of_neg (Bool.eq_false_iff.mp hpc),
          List.nthFilterPos_cons_of_false _ _ ((hinv_p c).trans hpc),
          List.nthFilterPos_cons_of_false _ _ ((hresp_p c).trans hpc), hinv, hresp, Option.map_some]
        exact ⟨congrArg some (by omega), congrArg some (by omega)⟩
      · simp only [List.filter_cons_of_pos hpc, List.length_cons]
        rw [show 2 * (((rest.take k').filter pred).length + 1) =
            2 * ((rest.take k').filter pred).length + 1 + 1 by omega]
        simp only [List.nthFilterPos_cons_succ_of_true _ _ ((hinv_p c).trans hpc),
          List.nthFilterPos_cons_succ_of_true _ _ ((hresp_p c).trans hpc), hinv, hresp,
          Option.map_some]
        exact ⟨congrArg some (by omega), congrArg some (by omega)⟩

/-- Invocation and response positions of `opIdAt calls j hj` in `calls.flatMap OpCall.toEvents` are
`2 * j` and `2 * j + 1`. -/
theorem invPos_respPos_opIdAt [DecidableEq P] (calls : List (OpCall P Op Resp))
    (j : ℕ) (hj : j < calls.length) :
    History.invPos (calls.flatMap OpCall.toEvents) (opIdAt calls j hj) = some (2 * j) ∧
      History.respPos (calls.flatMap OpCall.toEvents) (opIdAt calls j hj) = some (2 * j + 1) := by
  dsimp only [History.invPos, History.respPos, History.nthProcPos, opIdAt, countProcCalls]
  exact nthFilterPos_flatMap_toEvents
    (fun c => decide (c.proc = calls[j].proc))
    (fun e => decide (e.proc = calls[j].proc))
    (fun _ => rfl) (fun _ => rfl) calls j hj (decide_eq_true rfl)

/-- `opIdAt calls` is injective on valid call indices. -/
theorem opIdAt_injective [DecidableEq P] {calls : List (OpCall P Op Resp)}
    {j₁ j₂ : ℕ} (hj₁ : j₁ < calls.length) (hj₂ : j₂ < calls.length)
    (heq : opIdAt calls j₁ hj₁ = opIdAt calls j₂ hj₂) : j₁ = j₂ :=
  Nat.mul_left_cancel Nat.zero_lt_two <| Option.some.inj <|
    (invPos_respPos_opIdAt calls j₁ hj₁).1.symm.trans
      (heq ▸ (invPos_respPos_opIdAt calls j₂ hj₂).1)

/-- Real-time precedence in `calls.flatMap OpCall.toEvents` agrees with call-index order `j₁ < j₂`.
-/
theorem prec_flatMap_toEvents_opIdAt_iff [DecidableEq P]
    (calls : List (OpCall P Op Resp)) {j₁ j₂ : ℕ}
    (hj₁ : j₁ < calls.length) (hj₂ : j₂ < calls.length) :
    History.prec (calls.flatMap OpCall.toEvents)
      (opIdAt calls j₁ hj₁) (opIdAt calls j₂ hj₂) ↔ j₁ < j₂ := by
  obtain ⟨_, hr₁⟩ := invPos_respPos_opIdAt calls j₁ hj₁
  obtain ⟨hi₂, _⟩ := invPos_respPos_opIdAt calls j₂ hj₂
  refine ⟨fun ⟨_, _, hr, hi, _⟩ => ?_, fun _ => ⟨2 * j₁ + 1, 2 * j₂, hr₁, hi₂, by omega⟩⟩
  rw [hr₁, Option.some.injEq] at hr
  rw [hi₂, Option.some.injEq] at hi
  omega

/-- Surjectivity of `opIdAt calls` onto all `e : OpId P` with `e.idx < countProcCalls e.proc calls`.
-/
theorem exists_opIdAt_of_lt_countProcCalls [DecidableEq P]
    (calls : List (OpCall P Op Resp)) (e : OpId P) (hlt : e.idx < countProcCalls e.proc calls) :
    ∃ (j : ℕ) (hj : j < calls.length), opIdAt calls j hj = e := by
  induction calls generalizing e with
  | nil => simp only [countProcCalls_nil] at hlt; omega
  | cons c rest ih =>
    obtain ⟨q, n⟩ := e
    dsimp only at hlt
    rw [countProcCalls_cons] at hlt
    by_cases h0 : c.proc = q ∧ n = 0
    · exact ⟨0, Nat.zero_lt_succ _, by
        simp only [opIdAt, List.getElem_cons_zero, h0.1, h0.2, List.take_zero, countProcCalls_nil]⟩
    · have hlt' : (if c.proc = q then n - 1 else n) < countProcCalls q rest := by grind
      obtain ⟨j', hj', heq⟩ := ih ⟨q, if c.proc = q then n - 1 else n⟩ hlt'
      refine ⟨j' + 1, Nat.succ_lt_succ hj', ?_⟩
      simp only [opIdAt, List.getElem_cons_succ, List.take_succ_cons, countProcCalls_cons] at heq ⊢
      grind

end CallIndexing

end Cslib.Distributed.ConcurrentObjects
