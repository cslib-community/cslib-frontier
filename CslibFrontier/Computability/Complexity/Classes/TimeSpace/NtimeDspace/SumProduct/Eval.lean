/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgLength
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.StepTerm

/-!
# Proposition 3.2: evaluating a sum–product recursion in small space

`sumProduct_decidable` is Proposition 3.2 of the paper for the `ProgLang` machine
model. Let `t a` be a sum–product recursion for every input `a`, explicit
through closed programs (`Queries`) that report the kind, precision and
parameter of the node at a path and the bits of leaf values. If the cost of
`t a` and the other sizes are paid for by a budget `X a` that a closed program
computes from the input length, then bit `k₀ a` of the root value is decided
in time `2^(C·X)` and space `C·X`.

The program runs the evaluator's step (`stepT`) `2^X` times from the initial
state and reads off the returned bit. Every reached state satisfies the
invariant, so its code is below `2^X` (`code_lt`). The run halts, by the
correctness of the machine (`reaches_call`), and by pigeonhole it has halted
after `2^X` steps (`iterate_eq_of_fixed`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NatList SPTree _root_.Turing.MultiTapeTM

/-- Run a program closed in one variable on an argument term. -/
def callT1 (q : Prog) (a : Term) : Term := fun d => .letIn (a d) q

variable {w : List Bool} {B : ℕ}

theorem denote_callT1 {q : Prog} (hq : Prog'.closed 1 q = true) {a : ℕ} {env : List ℕ}
    (_ha : a < env.length) :
    (callT1 q (lvl a)).denote w env = q.eval w [(lvl a).denote w env] := by
  show Prog.eval w (.letIn _ q) env = _
  simp only [Prog.eval]
  exact Prog'.eval_append q [(lvl a).denote w env] env hq

theorem bnd_callT1 {q : Prog} (hq : Prog'.closed 1 q = true) {a : ℕ} {env : List ℕ}
    (_ha : a < env.length) (h : q.Bounded w B [(lvl a).denote w env]) :
    (callT1 q (lvl a)).Bnd w B env := by
  show Prog.Bounded w B (.letIn _ q) env
  simp only [Prog.Bounded]
  exact ⟨trivial, (Prog'.bounded_append B q [(lvl a).denote w env] env hq).mpr h⟩

/-- The evaluator: compute the root bit `k₀` and the budget `X` from the input
length, run `2^X` steps from the initial state, and return the bit. -/
def mainT (Q : Queries) (rootP XP : Prog) : Term :=
  letT (callT1 rootP (lvl 0)) fun k0 => letT (callT1 XP (lvl 0)) fun X =>
    letT (const 1) fun o => letT (mkT o k0 o o) fun S0 =>
      letT (foldT (pow2 X) S0 fun acc _ => stepT Q (lvl 0) acc) fun Sf =>
        letT (tlT Sf) fun r => hdT r

theorem foldl_range_iterate (g : ℕ → ℕ) (x k : ℕ) :
    (List.range k).foldl (fun acc _ => g acc) x = g^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']; rfl

/-- The initial state. -/
def initState (k0 : ℕ) : State := ⟨true, k0, [], []⟩

/-- The final state returning the bit `b`. -/
def finalState (b : ℕ) : State := ⟨false, b, [], []⟩

theorem cost_node_le (ℓ : ℕ) (t : SPTree) {π : List ℕ} (h : Valid t π) :
    (node t π).cost ℓ ≤ t.cost ℓ := by
  have := pathCost_le ℓ t π h
  omega

theorem param_le_cost_of_tag {ℓ : ℕ} {u : SPTree} (h : u.tag = 1) : u.param ≤ u.cost ℓ := by
  cases u with
  | sum P w f => simp only [SPTree.param, SPTree.cost]; omega
  | _ => simp [SPTree.tag] at h

theorem tag_lt_four (u : SPTree) : u.tag < 4 := by cases u <;> simp [SPTree.tag]

section Run

variable (Q : Queries) (w : List Bool) (n : ℕ) (t : SPTree) (ℓ V X k0 : ℕ)

/-- The numeric step at input `w` and length `n`. -/
def gStep : ℕ → ℕ := stepF (Q.qt w n) (Q.qp w n) (Q.qa w n) (Q.qb w n)

/-- The hypotheses of the evaluator, for one input. -/
structure RunHyp : Prop where
  hℓ : 1 ≤ ℓ
  hprec : t.PrecLe (2 ^ ℓ)
  hV : ∀ π, Valid t π → (node t π).prec + (node t π).param ≤ V
  hk0V : k0 ≤ V
  hXcost : 34 * t.cost ℓ + 2 * V.size + 16 ≤ X
  hq : ∀ π, Valid t π →
    Q.tag.eval w [enc π, n] = (node t π).tag ∧ Q.prec.eval w [enc π, n] = (node t π).prec ∧
    Q.param.eval w [enc π, n] = (node t π).param ∧ Q.tag.Bounded w (2 ^ (X + 1)) [enc π, n] ∧
    Q.prec.Bounded w (2 ^ (X + 1)) [enc π, n] ∧ Q.param.Bounded w (2 ^ (X + 1)) [enc π, n]
  hbit : ∀ π k, Valid t π → (node t π).tag = 0 → k < (node t π).prec →
    (0 < Q.bit.eval w [k, enc π, n] ↔ (node t π).value.testBit k = true) ∧
    Q.bit.Bounded w (2 ^ (X + 1)) [k, enc π, n]

/-- The abstract run from the initial state. -/
def run (m : ℕ) : State :=
  (step (numQ (Q.qt w n) (Q.qp w n) (Q.qa w n)) (numLB (Q.qb w n)))^[m] (initState k0)

variable {Q w n t ℓ V X k0}

theorem RunHyp.agrees (h : RunHyp Q w n t ℓ V X k0) :
    Agrees (numQ (Q.qt w n) (Q.qp w n) (Q.qa w n)) (numLB (Q.qb w n)) t [] := by
  intro ρ hρ
  rw [List.append_nil]
  obtain ⟨e1, e2, e3, -⟩ := h.hq ρ hρ
  refine ⟨?_, fun k ht hk => ?_⟩
  · simp only [numQ, Queries.qt, Queries.qp, Queries.qa, e1, e2, e3, SPTree.info]
  · simp only [numLB, Queries.qb]
    have hiff := (h.hbit ρ k hρ ht hk).1
    by_cases hb : (node t ρ).value.testBit k = true
    · simp [hb, hiff.mpr hb]
    · have : ¬ 0 < Q.bit.eval w [k, enc ρ, n] := fun h0 => hb (hiff.mp h0)
      simp only [this, decide_false]
      simpa using hb

theorem RunHyp.inv (h : RunHyp Q w n t ℓ V X k0) (m : ℕ) : Inv t V (run Q w n k0 m) := by
  have hinit : Inv t V (initState k0) :=
    ⟨trivial, fun _ => h.hk0V, fun h' => absurd h' (by simp [initState])⟩
  refine inv_iterate (fun π hπ => ?_) h.hV hinit m
  have := (h.agrees π hπ).1
  rwa [List.append_nil] at this

theorem StackOK.shape {t : SPTree} {fr : List Frame} {π : List ℕ} (h : StackOK t fr π) :
    fr ≠ [] → π ≠ [] := by
  intro hfr hπ
  cases fr with
  | nil => exact hfr rfl
  | cons f fr => subst hπ; exact h.elim

theorem RunHyp.code_run (h : RunHyp Q w n t ℓ V X k0) (m : ℕ) :
    (gStep Q w n)^[m] (initState k0).code = (run Q w n k0 m).code := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, gStep, stepF_code _ (h.inv m).1.shape, run, run,
      Function.iterate_succ_apply']

theorem RunHyp.code_lt (h : RunHyp Q w n t ℓ V X k0) (m : ℕ) : (run Q w n k0 m).code < 2 ^ X :=
  (SumProduct.code_lt h.hℓ h.hprec (h.inv m)).trans_le
    (Nat.pow_le_pow_right (by norm_num) h.hXcost)

/-- **The run halts with the requested bit** within `2^X` steps. -/
theorem RunHyp.iterate_final (h : RunHyp Q w n t ℓ V X k0) :
    (gStep Q w n)^[2 ^ X] (initState k0).code = (finalState (t.value.testBit k0).toNat).code := by
  set y := (finalState (t.value.testBit k0).toNat).code
  refine iterate_eq_of_fixed _ _ y _ (fun m => by rw [h.code_run]; exact h.code_lt m) ?_ ?_
  · rw [gStep, stepF_code _ (fun h' => absurd rfl h')]
    rfl
  · obtain ⟨m, hm⟩ := reaches_call t [] k0 [] h.agrees
    exact ⟨m, by rw [h.code_run]; simp only [run, initState]; rw [hm]; rfl⟩

theorem initState_code (k0 : ℕ) : (initState k0).code = mkF 1 k0 1 1 := by
  rw [code_eq]; rfl

theorem RunHyp.valid_path (h : RunHyp Q w n t ℓ V X k0) (m : ℕ) :
    Valid t (run Q w n k0 m).path := (h.inv m).1.valid

theorem RunHyp.valid_tail (h : RunHyp Q w n t ℓ V X k0) (m : ℕ)
    (hfr : (run Q w n k0 m).frames ≠ []) : Valid t (run Q w n k0 m).path.tail := by
  have hs := (h.inv m).1
  generalize (run Q w n k0 m).frames = fr at hs hfr
  generalize (run Q w n k0 m).path = π at hs
  cases fr with
  | nil => exact absurd rfl hfr
  | cons f fr =>
    cases π with
    | nil => exact hs.elim
    | cons i ρ => exact hs.1.valid

/-- The evaluator program on one input: its value is the requested bit, and its
values are below `2^(X+1)`. -/
theorem RunHyp.main_spec (h : RunHyp Q w n t ℓ V X k0) {rootP XP : Prog}
    (hroot : Prog'.closed 1 rootP = true) (hXP : Prog'.closed 1 XP = true)
    (hrootv : rootP.eval w [n] = k0 ∧ rootP.Bounded w (2 ^ (X + 1)) [n])
    (hXv : XP.eval w [n] = X ∧ XP.Bounded w (2 ^ (X + 1)) [n]) :
    (mainT Q rootP XP).denote w [n] = (t.value.testBit k0).toNat ∧
      (mainT Q rootP XP).Bnd w (2 ^ (X + 1)) [n] := by
  have hX16 : 16 ≤ X := by have := h.hXcost; omega
  have hpow : 2 ^ X ≤ 2 ^ (X + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ 2 ^ (X + 1) :=
    (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 2 ≤ X + 1 by omega)).trans' (by norm_num)
  -- The fold computes the iterates of the numeric step.
  have hfold : ∀ (env : List ℕ) (hn : (lvl 0).denote w env = n) (h0 : 0 < env.length) (x m : ℕ),
      foldAcc w (fun acc _ => stepT Q (lvl 0) acc) env x m = (gStep Q w n)^[m] x := by
    intro env hn h0 x m
    rw [foldAcc_eq _ env (fun acc _ => gStep Q w n acc) (fun acc k => ?_), foldl_range_iterate]
    rw [denote_stepT Q (by lvl_disch) (by lvl_disch)]
    try simp (disch := lvl_disch) only [lvl_cons, denote_lvl_acc, hn, gStep]
  have hS0 : mkF 1 k0 1 1 = (initState k0).code := (initState_code k0).symm
  have hfin := h.iterate_final
  have hfinal : (finalState (t.value.testBit k0).toNat).code =
      enc [0, (t.value.testBit k0).toNat, 1, 1] := rfl
  have hl0 : (lvl 0).denote w [n] = n := rfl
  constructor
  · simp (disch := lvl_disch) only [mainT, hl0, denote_letT, denote_callT1 hroot, denote_callT1 hXP,
      denote_const, denote_mkT, denote_foldT, denote_pow2, denote_tlT, denote_hdT, lvl_cons,
      denote_lvl_let, hrootv.1, hXv.1]
    rw [hfold _ rfl (by simp), hS0, hfin, hfinal, tlF_enc_cons, hdF_enc_cons]
  · rw [mainT, bnd_letT]
    refine ⟨bnd_callT1 hroot (by simp) (by rw [hl0]; exact hrootv.2), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_callT1 hXP (by lvl_disch) (by
      simp (disch := lvl_disch) only [lvl_cons, hl0]; exact hXv.2), ?_⟩
    rw [bnd_letT]
    refine ⟨by simp; omega, ?_⟩
    rw [bnd_letT]
    have hcode0 := h.code_lt 0
    simp only [run, Function.iterate_zero, id] at hcode0
    refine ⟨bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by
      simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_callT1 hroot, hrootv.1,
        hl0, denote_const]
      rw [hS0]; omega), ?_⟩
    rw [bnd_letT]
    refine ⟨?_, ?_⟩
    · rw [bnd_foldT]
      simp (disch := lvl_disch) only [denote_pow2, lvl_cons, denote_lvl_let,
        denote_callT1 hXP, hXv.1, hl0, denote_const, denote_callT1 hroot, hrootv.1, denote_mkT]
      refine ⟨bnd_pow2 _ _ _ _ trivial (by
        simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_callT1 hXP, hXv.1, hl0]
        exact hpow), trivial, hpow, fun k hk => ?_⟩
      have hacc : foldAcc w (fun acc _ => stepT Q (lvl 0) acc) [mkF 1 k0 1 1, 1, X, k0, n]
          (mkF 1 k0 1 1) k = (run Q w n k0 k).code := by
        rw [hfold _ rfl (by simp), hS0, h.code_run]
      have hinv := h.inv k
      have hlt := h.code_lt k
      have hlt' := h.code_lt (k + 1)
      have hst : step (numQ (Q.qt w n) (Q.qp w n) (Q.qa w n)) (numLB (Q.qb w n)) (run Q w n k0 k) =
          run Q w n k0 (k + 1) := by
        simp only [run]; rw [Function.iterate_succ_apply']
      refine bnd_stepT Q (by simp) (by simp) (run Q w n k0 k) (by
        simp only [denote_lvl_acc]; exact hacc) hinv.1.shape (by omega) h4
        (fun hc => hinv.2.2 hc) (fun hc => ?_) (fun hc hfr => ?_) ?_
      · have hπ := h.valid_path k
        obtain ⟨e1, e2, e3, b1, b2, b3⟩ := h.hq _ hπ
        have hl0' : (lvl 0).denote w [foldAcc w (fun acc x => stepT Q (lvl 0) acc)
            [mkF 1 k0 1 1, 1, X, k0, n] (mkF 1 k0 1 1) k, k, mkF 1 k0 1 1, 1, X, k0, n] = n := rfl
        simp only [hl0', Queries.qt, Queries.qp, e1, e2]
        refine ⟨b1, b2, b3, fun hk hk0 => (h.hbit _ _ hπ (by omega) hk).2,
          fun _ => tag_lt_four _⟩
      · have hρ := h.valid_tail k hfr
        obtain ⟨e1, e2, e3, b1, b2, b3⟩ := h.hq _ hρ
        have hl0' : (lvl 0).denote w [foldAcc w (fun acc x => stepT Q (lvl 0) acc)
            [mkF 1 k0 1 1, 1, X, k0, n] (mkF 1 k0 1 1) k, k, mkF 1 k0 1 1, 1, X, k0, n] = n := rfl
        simp only [hl0', Queries.qt, Queries.qa, e1, e3]
        refine ⟨b1, b3, fun htag => ?_⟩
        have hw := param_le_cost_of_tag (ℓ := ℓ) htag
        have hc := cost_node_le ℓ t hρ
        have : (node t (run Q w n k0 k).path.tail).param ≤ X + 1 := by
          have := h.hXcost; omega
        exact Nat.pow_le_pow_right (by norm_num) this
      · have hl0' : (lvl 0).denote w [foldAcc w (fun acc x => stepT Q (lvl 0) acc)
            [mkF 1 k0 1 1, 1, X, k0, n] (mkF 1 k0 1 1) k, k, mkF 1 k0 1 1, 1, X, k0, n] = n := rfl
        rw [hl0', ← gStep, gStep, stepF_code _ hinv.1.shape, hst]
        omega
    · have hfinB : enc [0, (t.value.testBit k0).toNat, 1, 1] < 2 ^ X := by
        rw [← hfinal, ← hfin, h.code_run]; exact h.code_lt _
      have hSf : foldAcc w (fun acc _ => stepT Q (lvl 0) acc) [mkF 1 k0 1 1, 1, X, k0, n]
          (mkF 1 k0 1 1) (2 ^ X) = enc [0, (t.value.testBit k0).toNat, 1, 1] := by
        rw [hfold _ rfl (by simp), hS0, hfin, hfinal]
      have e2 := enc_le_enc_cons 0 [(t.value.testBit k0).toNat, 1, 1]
      simp (disch := lvl_disch) only [denote_foldT, denote_pow2, lvl_cons, denote_lvl_let,
        denote_callT1 hXP, hXv.1, hl0, denote_const, denote_callT1 hroot, hrootv.1, denote_mkT]
      rw [bnd_letT]
      refine ⟨bnd_tlT_code (by lvl_disch) (by simp only [denote_lvl_let]; exact hSf) (by omega),
        bnd_hdT_code (by lvl_disch) (by
          simp (disch := lvl_disch) only [denote_lvl_let, denote_tlT, hSf, tlF_enc_cons]; rfl)
          (by omega)⟩

end Run

/-- **Proposition 3.2.** A sum–product recursion explicit through closed programs is
evaluated bitwise in time `2^(C·X)` and space `C·X`, where `X` bounds the
cost and the logarithms of the precisions and parameters. -/
theorem sumProduct_decidable {α : Type} {encA : α ↪ List Bool} (t : α → SPTree) (k0 : α → ℕ)
    (Q : Queries) (rootP XP : Prog) (hroot : Prog'.closed 1 rootP = true)
    (hXP : Prog'.closed 1 XP = true) (ℓ V X : α → ℕ)
    (hℓ : ∀ a, 1 ≤ ℓ a) (hprec : ∀ a, (t a).PrecLe (2 ^ ℓ a))
    (hV : ∀ a π, Valid (t a) π → (node (t a) π).prec + (node (t a) π).param ≤ V a)
    (hk0V : ∀ a, k0 a ≤ V a)
    (hXcost : ∀ a, 34 * (t a).cost (ℓ a) + 2 * (V a).size + 16 ≤ X a)
    (hXlog : ∀ a, (encA a).length.log2 + 1 ≤ X a)
    (hrootv : ∀ a, rootP.eval (encA a) [(encA a).length] = k0 a ∧
      rootP.Bounded (encA a) (2 ^ (X a + 1)) [(encA a).length])
    (hXv : ∀ a, XP.eval (encA a) [(encA a).length] = X a ∧
      XP.Bounded (encA a) (2 ^ (X a + 1)) [(encA a).length])
    (hq : ∀ a π, Valid (t a) π →
      Q.tag.eval (encA a) [enc π, (encA a).length] = (node (t a) π).tag ∧
      Q.prec.eval (encA a) [enc π, (encA a).length] = (node (t a) π).prec ∧
      Q.param.eval (encA a) [enc π, (encA a).length] = (node (t a) π).param ∧
      Q.tag.Bounded (encA a) (2 ^ (X a + 1)) [enc π, (encA a).length] ∧
      Q.prec.Bounded (encA a) (2 ^ (X a + 1)) [enc π, (encA a).length] ∧
      Q.param.Bounded (encA a) (2 ^ (X a + 1)) [enc π, (encA a).length])
    (hbit : ∀ a π k, Valid (t a) π → (node (t a) π).tag = 0 → k < (node (t a) π).prec →
      (0 < Q.bit.eval (encA a) [k, enc π, (encA a).length] ↔
        (node (t a) π).value.testBit k = true) ∧
      Q.bit.Bounded (encA a) (2 ^ (X a + 1)) [k, enc π, (encA a).length]) :
    ∃ C, DecidableInTimeAndSpace {a | (t a).value.testBit (k0 a) = true} encA
      (fun a => 2 ^ (C * X a)) (fun a => C * X a) := by
  have key (a : α) := RunHyp.main_spec (rootP := rootP) (XP := XP)
    ⟨hℓ a, hprec a, hV a, hk0V a, hXcost a, hq a, hbit a⟩ hroot hXP (hrootv a) (hXv a)
  refine ProgLang.decidable_of_prog_len _ (mainT Q rootP XP 1) X (fun a => X a + 1) 2 hXlog
    (fun a => by omega) (fun a => by have := hXcost a; omega) (fun a => ?_) (fun a => (key a).2)
    (fun a => ?_)
  · have h1 := Nat.lt_log2_self (n := (encA a).length)
    have h2 : 2 ^ ((encA a).length.log2 + 1) ≤ 2 ^ (X a + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := hXlog a; omega)
    omega
  · have hv : (mainT Q rootP XP 1).eval (encA a) [(encA a).length] =
        ((t a).value.testBit (k0 a)).toNat := (key a).1
    rw [hv, Set.mem_setOf_eq]
    cases (t a).value.testBit (k0 a) <;> simp

end Cslib.Complexity.NtimeDspace.SumProduct
