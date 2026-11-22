/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Eval

/-!
# Reading a path code

Iterated tails (`dropF`), the length (`lengthF`) and the entries (`getF`) of a code of a
list, as pure functions and as program terms with value bounds.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NatList

/-- `k` tails. -/
def dropF (k e : ℕ) : ℕ := tlF^[k] e

/-- The number of nonempty tails among the first `e`. -/
def lengthF (e : ℕ) : ℕ := ((Finset.range e).filter fun k => 2 ≤ dropF k e).card

/-- Entry `m`. -/
def getF (e m : ℕ) : ℕ := hdF (dropF m e)

theorem tOnesF_zero : tOnesF 0 = 0 := rfl
theorem tOnesF_one : tOnesF 1 = 1 := by decide
theorem tlF_zero : tlF 0 = 0 := by simp [tlF, tOnesF_zero]
theorem tlF_one : tlF 1 = 0 := by simp [tlF, tOnesF_one]

theorem dropF_enc (l : List ℕ) : ∀ k ≤ l.length, dropF k (enc l) = enc (l.drop k) := by
  intro k hk
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil => simp at hk
    | cons x l =>
      simp only [dropF, Function.iterate_succ_apply, tlF_enc_cons]
      exact ih l (by simp at hk; omega)

theorem dropF_zero_of (k : ℕ) : dropF k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k
      ih => simp only [dropF, Function.iterate_succ_apply', tlF_zero] at ih ⊢; rw [ih, tlF_zero]

theorem dropF_enc_ge (l : List ℕ) (k : ℕ) (hk : l.length < k) : dropF k (enc l) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = l.length + 1 + j := ⟨k - l.length - 1, by omega⟩
  have h1 : dropF (l.length + 1) (enc l) = 0 := by
    rw [dropF, Function.iterate_succ_apply', ← dropF, dropF_enc l _ le_rfl, List.drop_length,
      enc_nil, tlF_one]
  rw [dropF, Nat.add_comm, Function.iterate_add_apply, ← dropF, ← dropF, h1, dropF_zero_of]

theorem length_lt_enc (l : List ℕ) : l.length < enc l := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have := two_pow_le_enc_cons x l
    have h2 : 2 * enc l ≤ enc (x :: l) := by
      rw [enc_cons]
      have : 2 ≤ 2 ^ (2 * x.size + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith [Nat.zero_le (2 ^ (x.size + 1) * x)]
    simp; omega

theorem lengthF_enc (l : List ℕ) : lengthF (enc l) = l.length := by
  rw [lengthF]
  have : (Finset.range (enc l)).filter (fun k => 2 ≤ dropF k (enc l)) = Finset.range l.length := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hk
      push_neg at hk
      rcases hk.lt_or_eq with hlt | heq
      · rw [dropF_enc_ge l k hlt] at h2; omega
      · rw [← heq, dropF_enc l _ le_rfl, List.drop_length, enc_nil] at h2; omega
    · intro hk
      refine ⟨hk.trans (length_lt_enc l), ?_⟩
      rw [dropF_enc l k hk.le]
      obtain ⟨x, t, ht⟩ : ∃ x t, l.drop k = x :: t := by
        cases h : l.drop k with
        | nil => simp at h; omega
        | cons x t => exact ⟨x, t, rfl⟩
      rw [ht]; exact two_le_enc_cons x t
  rw [this, Finset.card_range]

theorem getF_enc (l : List ℕ) (m : ℕ) (hm : m < l.length) : getF (enc l) m = l[m] := by
  rw [getF, dropF_enc l m hm.le, List.drop_eq_getElem_cons hm, hdF_enc_cons]

/-- Fold a child function along a path code, root first. -/
def pathStateF (child : ℕ → ℕ → ℕ) (st₀ e : ℕ) : ℕ :=
  (List.range (lengthF e)).foldl (fun acc k => child acc (getF e (lengthF e - 1 - k))) st₀

/-- The state at a path, deepest symbol first (as `GenFun.stateAt`). -/
def stateAtF (child : ℕ → ℕ → ℕ) (st₀ : ℕ) : List ℕ → ℕ
  | [] => st₀
  | i :: π => child (stateAtF child st₀ π) i

theorem foldl_path_enc (child : ℕ → ℕ → ℕ) (st₀ : ℕ) (ν : List ℕ) :
    ∀ k ≤ ν.length, (List.range k).foldl
      (fun acc k => child acc (getF (enc ν) (ν.length - 1 - k))) st₀ =
        stateAtF child st₀ (ν.drop (ν.length - k)) := by
  intro k hk
  induction k with
  | zero => simp [stateAtF]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      getF_enc ν _ (by omega)]
    have hd : ν.drop (ν.length - (k + 1)) = ν[ν.length - 1 - k] :: ν.drop (ν.length - k) := by
      rw [show ν.length - (k + 1) = ν.length - 1 - k by omega, List.drop_eq_getElem_cons
        (by omega)]
      congr 2; omega
    rw [hd]; rfl

theorem pathStateF_enc (child : ℕ → ℕ → ℕ) (st₀ : ℕ) (ν : List ℕ) :
    pathStateF child st₀ (enc ν) = stateAtF child st₀ ν := by
  rw [pathStateF, lengthF_enc, foldl_path_enc child st₀ ν _ le_rfl, Nat.sub_self, List.drop_zero]

/-! ### Terms -/

/-- `k` tails. -/
def dropT (e k : Term) : Term := foldT k e fun acc _ => tlT acc

/-- The length. -/
def lengthT (e : Term) : Term :=
  foldT e (const 0) fun acc
      k => letT (dropT e k) fun d => ite (lt (const 1) d) (add acc (const 1)) acc

/-- Entry `m`. -/
def getT (e m : Term) : Term := letT (dropT e m) fun d => hdT d

variable {w : List Bool} {B : ℕ}

theorem denote_dropT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length) :
    (dropT (lvl a) (lvl b)).denote w env = dropF ((lvl b).denote w env) ((lvl a).denote w env) := by
  rw [dropT, denote_foldT, foldAcc_eq _ env (fun acc _ => tlF acc) (fun acc k => ?_),
    foldl_range_iterate]
  · rfl
  · simp only [denote_tlT (show env.length + 1 < (acc :: k :: env).length by simp), denote_lvl_acc]

theorem foldl_count (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (List.range n).foldl (fun acc k => if p k then acc + 1 else acc) 0 =
      ((Finset.range n).filter p).card := by
  have key : ∀ c, (List.range n).foldl (fun acc k => if p k then acc + 1 else acc) c =
      c + ((Finset.range n).filter p).card := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro c
      rw [List.range_succ, List.foldl_append, ih, Finset.range_add_one, Finset.filter_insert]
      simp only [List.foldl_cons, List.foldl_nil]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]; omega
      · rfl
  simpa using key 0

theorem denote_lengthT {a : ℕ} {env : List ℕ} (ha : a < env.length) :
    (lengthT (lvl a)).denote w env = lengthF ((lvl a).denote w env) := by
  unfold lengthF
  rw [lengthT, denote_foldT, denote_const,
    foldAcc_eq _ env (fun acc k => if 2 ≤ dropF k ((lvl a).denote w env) then acc + 1 else acc)
      (fun acc k => ?_)]
  · exact foldl_count _ _
  · simp (disch := lvl_disch) only [denote_letT, denote_dropT, lvl_cons, denote_lvl_let,
      denote_lvl_index, denote_lvl_acc, denote_ite_lt, denote_add, denote_const]
    rfl

theorem denote_getT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length) :
    (getT (lvl a) (lvl b)).denote w env = getF ((lvl a).denote w env) ((lvl b).denote w env) := by
  simp (disch := lvl_disch) only [getT, denote_letT, denote_dropT, denote_hdT, denote_lvl_let,
    getF]

/-- Fold a closed child program along a path code, root first. -/
def pathStateT (childP : Prog) (st₀ e len : Term) : Term :=
  letT (lengthT e) fun n => foldT n st₀ fun acc k =>
    letT (sub (sub n k) (const 1)) fun idx => letT (getT e idx) fun sym => callT3 childP acc sym len

/-- The child function of a closed program, at an input and a length. -/
def childFun (childP : Prog) (w : List Bool) (n : ℕ) (st i : ℕ) : ℕ := childP.eval w [st, i, n]

theorem denote_pathStateT {childP : Prog} (hc : Prog'.closed 3 childP = true) {s e l : ℕ}
    {env : List ℕ} (hs : s < env.length) (he : e < env.length) (hl : l < env.length) :
    (pathStateT childP (lvl s) (lvl e) (lvl l)).denote w env =
      pathStateF (childFun childP w ((lvl l).denote w env)) ((lvl s).denote w env)
        ((lvl e).denote w env) := by
  rw [pathStateT, denote_letT, denote_foldT, denote_lengthT (by lvl_disch), lvl_cons hs,
    denote_lvl_let, pathStateF]
  rw [foldAcc_eq _ _ (fun acc k => childFun childP w ((lvl l).denote w env) acc
    (getF ((lvl e).denote w env) (lengthF ((lvl e).denote w env) - 1 - k))) (fun acc k => ?_)]
  simp (disch := lvl_disch) only [denote_letT, denote_sub, denote_const, denote_getT,
    denote_callT3 hc, lvl_cons, denote_lvl_let, denote_lvl_index, denote_lvl_acc, childFun]
  rw [Nat.sub_right_comm]

/-! ### Value bounds -/

theorem tOnes_drop_bound (ν : List ℕ) (i : ℕ) :
    dropF i (enc ν) ≤ enc ν ∧
      2 ^ (tOnesF (dropF i (enc ν)) + tOnesF (dropF i (enc ν)) + 1) ≤ max (enc ν) 8 := by
  rcases Nat.lt_or_ge ν.length i with hlt | hge
  · rw [dropF_enc_ge ν i hlt, tOnesF_zero]; exact ⟨Nat.zero_le _, le_max_of_le_right (by norm_num)⟩
  · rw [dropF_enc ν i hge]
    have hle : ∀ j ≤ ν.length, enc (ν.drop j) ≤ enc ν := by
      intro j _
      induction j with
      | zero => simp
      | succ j ih =>
        refine le_trans ?_ (ih (by omega))
        cases h : ν.drop j with
        | nil => simp [List.drop_eq_nil_iff] at h; omega
        | cons x t =>
          rw [show ν.drop (j + 1) = t by rw [← List.drop_drop, h]; rfl]
          exact enc_le_enc_cons x t
    refine ⟨hle i hge, ?_⟩
    cases h : ν.drop i with
    | nil => rw [enc_nil, tOnesF_one]; exact le_max_of_le_right (by norm_num)
    | cons x t =>
      exact le_max_of_le_left ((two_pow_tOnesF_le x t).trans (h ▸ hle i hge))

theorem bnd_dropT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length)
    {ν : List ℕ} (he : (lvl a).denote w env = enc ν) (hB : max (enc ν) 8 ≤ B)
    (hk : (lvl b).denote w env ≤ B) : (dropT (lvl a) (lvl b)).Bnd w B env := by
  rw [dropT, bnd_foldT]
  refine ⟨trivial, trivial, hk, fun k _ => ?_⟩
  have hacc : foldAcc w (fun acc _ => tlT acc) env ((lvl a).denote w env) k = dropF k (enc ν) := by
    rw [foldAcc_eq _ env (fun acc _ => tlF acc) (fun acc j => by
      simp only [denote_tlT (show env.length + 1 < (acc :: j :: env).length by simp),
        denote_lvl_acc]), foldl_range_iterate, he]; rfl
  obtain ⟨h1, h2⟩ := tOnes_drop_bound ν k
  refine bnd_tlT (by simp)
      (by rw [denote_lvl_acc, hacc]; exact h1.trans (le_max_left _ _ |>.trans hB))
    (by rw [denote_lvl_acc, hacc]; exact h2.trans hB)

theorem bnd_lengthT {a : ℕ} {env : List ℕ} (ha : a < env.length) {ν : List ℕ}
    (he : (lvl a).denote w env = enc ν) (hB : max (enc ν) 8 + 1 ≤ B) :
    (lengthT (lvl a)).Bnd w B env := by
  rw [lengthT, bnd_foldT]
  refine ⟨trivial, by simp, by rw [he]; omega, fun k hk => ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_dropT (by simp; omega) (by simp) (by rw [lvl_cons₂ ha, he]) (by omega)
    (by rw [denote_lvl_index]; rw [he] at hk; omega), ?_⟩
  have hacc : foldAcc w (fun acc k => letT (dropT (lvl a) k) fun d =>
      ite (lt (const 1) d) (add acc (const 1)) acc) env ((const 0).denote w env) k ≤ k := by
    rw [denote_const, foldAcc_eq _ env (fun acc j => if 2 ≤ dropF j ((lvl a).denote w env)
      then acc + 1 else acc) (fun acc j => by
        simp (disch := lvl_disch) only [denote_letT, denote_dropT, lvl_cons, denote_lvl_let,
          denote_lvl_index, denote_lvl_acc, denote_ite_lt, denote_add, denote_const]; rfl),
      foldl_count]
    exact (Finset.card_filter_le _ _).trans (by simp)
  simp only [denote_const] at hacc
  refine bnd_ite_of (by simp; omega) ?_ (by simp)
  simp only [bnd_add, bnd_lvl, bnd_const, true_and]
  refine ⟨by omega, ?_⟩
  simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons, denote_lvl_acc, denote_const]
  rw [he] at hk
  omega

theorem bnd_getT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length)
    {ν : List ℕ} (he : (lvl a).denote w env = enc ν) (hB : max (enc ν) 8 ≤ B)
    (hk : (lvl b).denote w env ≤ B) : (getT (lvl a) (lvl b)).Bnd w B env := by
  rw [getT, bnd_letT]
  refine ⟨bnd_dropT ha hb he hB hk, ?_⟩
  rw [denote_dropT ha hb, he]
  obtain ⟨h1, h2⟩ := tOnes_drop_bound ν ((lvl b).denote w env)
  exact bnd_hdT (by simp) (by rw [denote_lvl_let]; exact h1.trans ((le_max_left _ _).trans hB))
    (by rw [denote_lvl_let]; exact h2.trans hB)

theorem bnd_pathStateT {childP : Prog} (hc : Prog'.closed 3 childP = true) {s e l : ℕ}
    {env : List ℕ} (hs : s < env.length) (he : e < env.length) (hl : l < env.length)
    {ν : List ℕ} (hev : (lvl e).denote w env = enc ν) (hB : max (enc ν) 8 + 1 ≤ B)
    (hchild : ∀ j < ν.length, childP.Bounded w B
      [stateAtF (childFun childP w ((lvl l).denote w env)) ((lvl s).denote w env)
        (ν.drop (j + 1)), ν[j]!, (lvl l).denote w env]) :
    (pathStateT childP (lvl s) (lvl e) (lvl l)).Bnd w B env := by
  rw [pathStateT, bnd_letT]
  refine ⟨bnd_lengthT he hev hB, ?_⟩
  rw [denote_lengthT he, hev, lengthF_enc]
  rw [bnd_foldT]
  refine ⟨trivial, trivial, by simp; have := length_lt_enc ν; omega, fun k hk => ?_⟩
  simp only [denote_lvl_let] at hk
  have hlen := length_lt_enc ν
  rw [bnd_letT]
  refine ⟨by simp; omega, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_getT (by simp; omega) (by simp) (by
      simp (disch := lvl_disch) only [lvl_cons]; exact hev) (by omega) (by
      simp (disch := lvl_disch) only [denote_lvl_let, denote_sub, denote_const, lvl_cons,
        denote_lvl_index]; omega), ?_⟩
  refine bnd_callT3 hc (by simp) (by simp) (by simp; omega) ?_
  -- The accumulator is the state of a suffix and the symbol is the next entry.
  have hacc := foldl_path_enc (childFun childP w ((lvl l).denote w env)) ((lvl s).denote w env) ν k
    hk.le
  have hj := hchild (ν.length - 1 - k) (by omega)
  rw [show ν.length - 1 - k + 1 = ν.length - k by omega] at hj
  have hfold : foldAcc w (fun acc k => letT (sub (sub (lvl env.length) k) (const 1)) fun idx =>
      letT (getT (lvl e) idx) fun sym => callT3 childP acc sym (lvl l)) (ν.length :: env)
      ((lvl s).denote w env) k =
        stateAtF (childFun childP w ((lvl l).denote w env)) ((lvl s).denote w env)
          (ν.drop (ν.length - k)) := by
    rw [foldAcc_eq _ _ (fun acc k => childFun childP w ((lvl l).denote w env) acc
      (getF (enc ν) (ν.length - 1 - k))) (fun acc j => by
        simp (disch := lvl_disch) only [denote_letT, denote_sub, denote_const, denote_getT,
          denote_callT3 hc, lvl_cons, denote_lvl_let, denote_lvl_index, denote_lvl_acc, childFun,
          hev]
        rw [Nat.sub_right_comm]), hacc]
  simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_lvl_acc, denote_lvl_index,
    denote_getT, denote_sub, denote_const, hev]
  rw [hfold, getF_enc ν _ (by omega)]
  rw [getElem!_pos ν _ (by omega)] at hj
  convert hj using 3
  simp only [Nat.sub_right_comm]

end Cslib.Complexity.NtimeDspace.SumProduct
