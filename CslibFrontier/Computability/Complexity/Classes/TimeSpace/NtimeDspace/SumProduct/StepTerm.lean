/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Closed
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.StepFun

/-!
# The step of the evaluator as a program term

`stepT` is a program term computing `stepF` (`denote_stepT`). It is built from
small pieces, each taking variables as arguments, so that every piece has a
meaning lemma and a value-bound lemma of its own.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NatList

/-- Discharge the side conditions `a < env.length` of variable lemmas. -/
macro "lvl_disch" : tactic => `(tactic| ((try simp only [List.length_cons]); omega))

/-! ### Building codes -/

/-- The code of a four-entry list. -/
def mkT (a b c d : Term) : Term :=
  letT (const 1) fun e => letT (consT d e) fun x1 => letT (consT c x1) fun x2 =>
    letT (consT b x2) fun x3 => consT a x3

/-- Push a frame. -/
def pushT (k j l c F : Term) : Term :=
  letT (consT c F) fun x1 => letT (consT l x1) fun x2 => letT (consT j x2) fun x3 => consT k x3

variable {w : List Bool} {B : ℕ}

theorem denote_mkT {a b c d : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length)
    (hc : c < env.length) (hd : d < env.length) :
    (mkT (lvl a) (lvl b) (lvl c) (lvl d)).denote w env =
      mkF ((lvl a).denote w env) ((lvl b).denote w env) ((lvl c).denote w env)
        ((lvl d).denote w env) := by
  simp (disch := lvl_disch) only [mkT, denote_letT, denote_const, denote_consT, denote_lvl_let,
    lvl_cons, mkF]

theorem denote_pushT {k j l c F : ℕ} {env : List ℕ} (hk : k < env.length) (hj : j < env.length)
    (hl : l < env.length) (hc : c < env.length) (hF : F < env.length) :
    (pushT (lvl k) (lvl j) (lvl l) (lvl c) (lvl F)).denote w env =
      pushF ((lvl k).denote w env) ((lvl j).denote w env) ((lvl l).denote w env)
        ((lvl c).denote w env) ((lvl F).denote w env) := by
  simp (disch := lvl_disch) only [pushT, denote_letT, denote_consT, denote_lvl_let, lvl_cons,
    pushF]

theorem le_consF_right (x l : ℕ) (hl : 1 ≤ l) : l ≤ consF x l :=
  (Nat.le_mul_of_pos_left l (by positivity)).trans (consF_ge x l hl).2.2.2.1

theorem bnd_mkT {a b c d : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length)
    (hc : c < env.length) (hd : d < env.length)
    (hB : mkF ((lvl a).denote w env) ((lvl b).denote w env) ((lvl c).denote w env)
        ((lvl d).denote w env) ≤ B) :
    (mkT (lvl a) (lvl b) (lvl c) (lvl d)).Bnd w B env := by
  set va := (lvl a).denote w env
  set vb := (lvl b).denote w env
  set vc := (lvl c).denote w env
  set vd := (lvl d).denote w env
  have h1 : 1 ≤ consF vd 1 := le_consF_right _ _ le_rfl
  have h2 : 1 ≤ consF vc (consF vd 1) := h1.trans (le_consF_right _ _ h1)
  have h3 : 1 ≤ consF vb (consF vc (consF vd 1)) := h2.trans (le_consF_right _ _ h2)
  have hB3 : consF vb (consF vc (consF vd 1)) ≤ B := (le_consF_right _ _ h3).trans hB
  have hB2 : consF vc (consF vd 1) ≤ B := (le_consF_right _ _ h2).trans hB3
  have hB1 : consF vd 1 ≤ B := (le_consF_right _ _ h1).trans hB2
  simp only [mkT, bnd_letT, bnd_const, denote_const]
  refine ⟨h1.trans hB1, ?_, ?_⟩
  · exact bnd_consT (by lvl_disch) (by lvl_disch) (by simp) (by
      rw [lvl_cons hd, denote_lvl_let]; exact hB1)
  · simp (disch := lvl_disch) only [denote_consT, denote_lvl_let, lvl_cons]
    refine ⟨bnd_consT (by lvl_disch) (by lvl_disch) ?_ ?_, ?_⟩
    · simp (disch := lvl_disch) only [denote_lvl_let]; exact h1
    · simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]; exact hB2
    · refine ⟨bnd_consT (by lvl_disch) (by lvl_disch) ?_ ?_, ?_⟩
      · simp (disch := lvl_disch) only [denote_lvl_let]; exact h2
      · simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]; exact hB3
      · refine bnd_consT (by lvl_disch) (by lvl_disch) ?_ ?_
        · simp (disch := lvl_disch) only [denote_lvl_let]; exact h3
        · simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]; exact hB

theorem bnd_pushT {k j l c F : ℕ} {env : List ℕ} (hk : k < env.length) (hj : j < env.length)
    (hl : l < env.length) (hc : c < env.length) (hF : F < env.length)
    (h1 : 1 ≤ (lvl F).denote w env)
    (hB : pushF ((lvl k).denote w env) ((lvl j).denote w env) ((lvl l).denote w env)
        ((lvl c).denote w env) ((lvl F).denote w env) ≤ B) :
    (pushT (lvl k) (lvl j) (lvl l) (lvl c) (lvl F)).Bnd w B env := by
  set vk := (lvl k).denote w env
  set vj := (lvl j).denote w env
  set vl := (lvl l).denote w env
  set vc := (lvl c).denote w env
  set vF := (lvl F).denote w env
  have g1 : 1 ≤ consF vc vF := h1.trans (le_consF_right _ _ h1)
  have g2 : 1 ≤ consF vl (consF vc vF) := g1.trans (le_consF_right _ _ g1)
  have g3 : 1 ≤ consF vj (consF vl (consF vc vF)) := g2.trans (le_consF_right _ _ g2)
  have hB3 : consF vj (consF vl (consF vc vF)) ≤ B := (le_consF_right _ _ g3).trans hB
  have hB2 : consF vl (consF vc vF) ≤ B := (le_consF_right _ _ g2).trans hB3
  have hB1 : consF vc vF ≤ B := (le_consF_right _ _ g1).trans hB2
  simp only [pushT, bnd_letT]
  refine ⟨bnd_consT hc hF h1 hB1, ?_⟩
  simp (disch := lvl_disch) only [denote_consT, denote_lvl_let, lvl_cons]
  refine ⟨bnd_consT (by lvl_disch) (by lvl_disch) ?_ ?_, ?_⟩
  · simp (disch := lvl_disch) only [denote_lvl_let]; exact g1
  · simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]; exact hB2
  · refine ⟨bnd_consT (by lvl_disch) (by lvl_disch) ?_ ?_, ?_⟩
    · simp (disch := lvl_disch) only [denote_lvl_let]; exact g2
    · simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]; exact hB3
    · refine bnd_consT (by lvl_disch) (by lvl_disch) ?_ ?_
      · simp (disch := lvl_disch) only [denote_lvl_let]; exact g3
      · simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]; exact hB

/-! ### The branches -/

@[simp] theorem zero_lt_ite_one_zero (p : Prop) [Decidable p] :
    (0 < if p then (1 : ℕ) else 0) ↔ p := by
  split_ifs with h <;> simp [h]

theorem denote_ite_lt (a b t e : Term) (env : List ℕ) :
    (ite (lt a b) t e).denote w env =
      if a.denote w env < b.denote w env then t.denote w env else e.denote w env := by
  rw [denote_ite, denote_lt]
  by_cases h : a.denote w env < b.denote w env <;> simp [h]

/-- After a split of a product node. -/
def advT (k j l c Fr ρ z o : Term) : Term :=
  ite (lt l j)
    (letT (add l o) fun l1 => letT (pushT k j l1 c Fr) fun F' => letT (consT z ρ) fun P' =>
      mkT o l1 F' P')
    (ite (lt j k)
      (letT (add j o) fun j1 => letT (div c (const 2)) fun ch => letT (pushT k j1 z ch Fr) fun F' =>
        letT (consT z ρ) fun P' => mkT o z F' P')
      (letT (mod c (const 2)) fun cm => mkT z cm Fr ρ))

/-- A return to a sum node. -/
def sumRetT (v k j l c Fr i ρ par z o : Term) : Term :=
  letT (add c v) fun cv => letT (add i o) fun i1 =>
    ite (lt i1 (pow2 par))
      (letT (pushT k j l cv Fr) fun F' => letT (consT i1 ρ) fun P' => mkT o j F' P')
      (ite (lt j k)
        (letT (add j o) fun j1 => letT (div cv (const 2)) fun ch =>
          letT (pushT k j1 l ch Fr) fun F' => letT (consT z ρ) fun P' => mkT o j1 F' P')
        (letT (mod cv (const 2)) fun cm => mkT z cm Fr ρ))

/-- A return to a product node. -/
def prodRetT (v k j l c Fr i ρ z o : Term) : Term :=
  ite (lt z i) (letT (add c v) fun cv => advT k j l cv Fr ρ z o)
    (ite (lt z v)
      (letT (sub j l) fun jl => letT (pushT k j l c Fr) fun F' => letT (consT o ρ) fun P' =>
        mkT o jl F' P')
      (advT k j l c Fr ρ z o))

/-- The values of variables, for the `simp` calls below. -/
theorem lvl_val {a : ℕ} {env : List ℕ} {x : ℕ} (h : (lvl a).denote w env = x) :
    (lvl a).denote w env = x := h

theorem denote_advT {k j l c Fr ρ z o : ℕ} {env : List ℕ} (hk : k < env.length)
    (hj : j < env.length) (_hl : l < env.length) (hc : c < env.length) (hFr : Fr < env.length)
    (hρ : ρ < env.length) (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1) :
    (advT (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr) (lvl ρ) (lvl z) (lvl o)).denote w env =
      advF ((lvl k).denote w env) ((lvl j).denote w env) ((lvl l).denote w env)
        ((lvl c).denote w env) ((lvl Fr).denote w env) ((lvl ρ).denote w env) := by
  simp (disch := lvl_disch) only [advT, advF, denote_ite_lt,
    denote_letT, denote_add, denote_div, denote_mod, denote_const, denote_pushT, denote_consT,
    denote_mkT, denote_lvl_let, lvl_cons, hz0, ho1]

theorem denote_sumRetT {v k j l c Fr i ρ par z o : ℕ} {env : List ℕ} (_hv : v < env.length)
    (hk : k < env.length) (hj : j < env.length) (hl : l < env.length) (_hc : c < env.length)
    (hFr : Fr < env.length) (hi : i < env.length) (hρ : ρ < env.length)
    (hpar : par < env.length) (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1) :
    (sumRetT (lvl v) (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr) (lvl i) (lvl ρ) (lvl par) (lvl z)
        (lvl o)).denote w env =
      sumRetF ((lvl v).denote w env) ((lvl k).denote w env) ((lvl j).denote w env)
        ((lvl l).denote w env) ((lvl c).denote w env) ((lvl Fr).denote w env)
        ((lvl i).denote w env) ((lvl ρ).denote w env) ((lvl par).denote w env) := by
  simp (disch := lvl_disch) only [sumRetT, sumRetF, denote_ite_lt,
    denote_letT, denote_add, denote_div, denote_mod, denote_const, denote_pow2, denote_pushT,
    denote_consT, denote_mkT, denote_lvl_let, lvl_cons, hz0, ho1]

theorem denote_prodRetT {v k j l c Fr i ρ z o : ℕ} {env : List ℕ} (_hv : v < env.length)
    (hk : k < env.length) (hj : j < env.length) (hl : l < env.length) (hc : c < env.length)
    (hFr : Fr < env.length) (_hi : i < env.length) (hρ : ρ < env.length)
    (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1) :
    (prodRetT (lvl v) (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr) (lvl i) (lvl ρ) (lvl z)
        (lvl o)).denote w env =
      prodRetF ((lvl v).denote w env) ((lvl k).denote w env) ((lvl j).denote w env)
        ((lvl l).denote w env) ((lvl c).denote w env) ((lvl Fr).denote w env)
        ((lvl i).denote w env) ((lvl ρ).denote w env) := by
  have hz0' : ∀ x, (lvl z).denote w (x :: env) = 0 := fun x => by rw [lvl_cons hz, hz0]
  have ho1' : ∀ x, (lvl o).denote w (x :: env) = 1 := fun x => by rw [lvl_cons ho, ho1]
  simp (disch := lvl_disch) only [prodRetT, prodRetF, denote_ite_lt,
    denote_letT, denote_sub, denote_add, denote_pushT, denote_consT, denote_mkT,
    denote_lvl_let, lvl_cons, hz0, ho1]
  rw [denote_advT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
    (by lvl_disch) (by lvl_disch) (by lvl_disch) (hz0' _) (ho1' _),
    denote_advT hk hj hl hc hFr hρ hz ho hz0 ho1]
  simp (disch := lvl_disch) only [denote_lvl_let, lvl_cons]

/-- The explicit machine: programs closed in `[path, len]` for the tag, the
precision and the parameter of a node, and closed in `[k, path, len]` for bit `k`
of a leaf. -/
structure Queries where
  tag : Prog
  prec : Prog
  param : Prog
  bit : Prog
  tag_closed : Prog'.closed 2 tag = true
  prec_closed : Prog'.closed 2 prec = true
  param_closed : Prog'.closed 2 param = true
  bit_closed : Prog'.closed 3 bit = true

/-- A call. -/
def callT (Q : Queries) (len v F Pa z o : Term) : Term :=
  letT (callT2 Q.tag Pa len) fun tag => letT (callT2 Q.prec Pa len) fun P =>
    letT (callT2 Q.param Pa len) fun par =>
      ite (lt v P)
        (ite (lt tag o)
          (letT (callT3 Q.bit v Pa len) fun qb => letT (lt z qb) fun bb => mkT z bb F Pa)
          (letT (pushT v z z z F) fun F' => letT (consT z Pa) fun P' =>
            ite (lt tag (const 3)) (mkT o z F' P')
              (ite (lt tag (const 4)) (letT (add v par) fun vp => mkT o vp F' P')
                (mkT z z F Pa))))
        (mkT z z F Pa)

/-- A return. -/
def retT (Q : Queries) (len v F Pa z o : Term) : Term :=
  ite (lt F (const 2)) (mkT z v F Pa)
    (letT (hdT F) fun k => letT (tlT F) fun F1 => letT (hdT F1) fun j => letT (tlT F1) fun F2 =>
      letT (hdT F2) fun l => letT (tlT F2) fun F3 => letT (hdT F3) fun c => letT (tlT F3) fun Fr =>
        letT (hdT Pa) fun i => letT (tlT Pa) fun ρ =>
          letT (callT2 Q.tag ρ len) fun tag => letT (callT2 Q.param ρ len) fun par =>
            ite (lt tag o) (mkT z v Fr ρ)
              (ite (lt tag (const 2)) (sumRetT v k j l c Fr i ρ par z o)
                (ite (lt tag (const 3)) (prodRetT v k j l c Fr i ρ z o) (mkT z v Fr ρ))))

/-- One step of the evaluator. -/
def stepT (Q : Queries) (len S : Term) : Term :=
  letT (hdT S) fun m => letT (tlT S) fun r1 => letT (hdT r1) fun v => letT (tlT r1) fun r2 =>
    letT (hdT r2) fun F => letT (tlT r2) fun r3 => letT (hdT r3) fun Pa =>
      letT (const 0) fun z => letT (const 1) fun o =>
        ite m (callT Q len v F Pa z o) (retT Q len v F Pa z o)

/-- The numeric oracles of the queries, at input `w` and length `n`. -/
def Queries.qt (Q : Queries) (w : List Bool) (n : ℕ) (pc : ℕ) : ℕ := Q.tag.eval w [pc, n]
def Queries.qp (Q : Queries) (w : List Bool) (n : ℕ) (pc : ℕ) : ℕ := Q.prec.eval w [pc, n]
def Queries.qa (Q : Queries) (w : List Bool) (n : ℕ) (pc : ℕ) : ℕ := Q.param.eval w [pc, n]
def Queries.qb (Q : Queries) (w : List Bool) (n : ℕ) (k pc : ℕ) : ℕ := Q.bit.eval w [k, pc, n]

theorem denote_callT (Q : Queries) {len v F Pa z o : ℕ} {env : List ℕ} (hlen : len < env.length)
    (hv : v < env.length) (hF : F < env.length) (hPa : Pa < env.length)
    (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1) :
    (callT Q (lvl len) (lvl v) (lvl F) (lvl Pa) (lvl z) (lvl o)).denote w env =
      callF (Q.qt w ((lvl len).denote w env)) (Q.qp w ((lvl len).denote w env))
        (Q.qa w ((lvl len).denote w env)) (Q.qb w ((lvl len).denote w env))
        ((lvl v).denote w env) ((lvl F).denote w env) ((lvl Pa).denote w env) := by
  simp (disch := lvl_disch) only [callT, callF, denote_ite_lt,
    denote_letT, denote_add, denote_const, denote_pushT, denote_consT, denote_mkT,
    denote_lvl_let, lvl_cons, hz0, ho1, denote_callT2 Q.tag_closed, denote_callT2 Q.prec_closed,
    denote_callT2 Q.param_closed, denote_callT3 Q.bit_closed, Queries.qt, Queries.qp, Queries.qa,
    Queries.qb, denote_lt]
  congr

theorem denote_retT (Q : Queries) {len v F Pa z o : ℕ} {env : List ℕ} (hlen : len < env.length)
    (hv : v < env.length) (hF : F < env.length) (hPa : Pa < env.length)
    (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1) :
    (retT Q (lvl len) (lvl v) (lvl F) (lvl Pa) (lvl z) (lvl o)).denote w env =
      retF (Q.qt w ((lvl len).denote w env)) (Q.qa w ((lvl len).denote w env))
        ((lvl v).denote w env) ((lvl F).denote w env) ((lvl Pa).denote w env) := by
  simp only [retT, retF, denote_ite_lt, denote_const]
  by_cases h : (lvl F).denote w env < 2
  · simp only [h, ite_true]
    exact denote_mkT hz hv hF hPa |>.trans (by rw [hz0])
  · simp only [h, ite_false]
    simp (disch := first | lvl_disch | simp (disch := lvl_disch) only [lvl_cons, hz0, ho1])
      only [denote_letT, denote_hdT, denote_tlT, denote_callT2 Q.tag_closed,
      denote_callT2 Q.param_closed, denote_lvl_let, lvl_cons, denote_ite_lt,
      denote_const, denote_mkT, denote_sumRetT, denote_prodRetT, hz0, ho1,
      Queries.qt, Queries.qa]
    congr

theorem denote_stepT (Q : Queries) {len S : ℕ} {env : List ℕ} (hlen : len < env.length)
    (hS : S < env.length) :
    (stepT Q (lvl len) (lvl S)).denote w env =
      stepF (Q.qt w ((lvl len).denote w env)) (Q.qp w ((lvl len).denote w env))
        (Q.qa w ((lvl len).denote w env)) (Q.qb w ((lvl len).denote w env))
        ((lvl S).denote w env) := by
  simp (disch := lvl_disch) only [stepT, stepF, denote_letT, denote_hdT, denote_tlT,
    denote_const, denote_lvl_let, lvl_cons, denote_ite]
  split_ifs with h
  · rw [denote_callT Q (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let])
      (by simp (disch := lvl_disch) only [denote_lvl_let])]
    simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let]
  · rw [denote_retT Q (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let])
      (by simp (disch := lvl_disch) only [denote_lvl_let])]
    simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let]

/-! ### Value bounds of the branches -/

theorem one_le_consF (x l : ℕ) (hl : 1 ≤ l) : 1 ≤ consF x l := hl.trans (le_consF_right x l hl)

theorem le_consF_left (x l : ℕ) (hl : 1 ≤ l) : x ≤ consF x l := (consF_ge x l hl).1

theorem mkF_le (a b c d : ℕ) :
    a ≤ mkF a b c d ∧ b ≤ mkF a b c d ∧ c ≤ mkF a b c d ∧ d ≤ mkF a b c d := by
  unfold mkF
  have h1 := one_le_consF d 1 le_rfl
  have h2 := one_le_consF c _ h1
  have h3 := one_le_consF b _ h2
  refine ⟨le_consF_left _ _ h3, (le_consF_left _ _ h2).trans (le_consF_right _ _ h3),
    ((le_consF_left _ _ h1).trans (le_consF_right _ _ h2)).trans (le_consF_right _ _ h3),
    (((le_consF_left _ _ le_rfl).trans (le_consF_right _ _ h1)).trans
      (le_consF_right _ _ h2)).trans (le_consF_right _ _ h3)⟩

theorem pushF_le (k j l c F : ℕ) (hF : 1 ≤ F) :
    1 ≤ pushF k j l c F ∧ k ≤ pushF k j l c F ∧ j ≤ pushF k j l c F ∧ l ≤ pushF k j l c F ∧
      c ≤ pushF k j l c F ∧ F ≤ pushF k j l c F := by
  unfold pushF
  have h1 := one_le_consF c F hF
  have h2 := one_le_consF l _ h1
  have h3 := one_le_consF j _ h2
  refine ⟨one_le_consF k _ h3, le_consF_left _ _ h3,
    (le_consF_left _ _ h2).trans (le_consF_right _ _ h3),
    ((le_consF_left _ _ h1).trans (le_consF_right _ _ h2)).trans (le_consF_right _ _ h3),
    (((le_consF_left _ _ hF).trans (le_consF_right _ _ h1)).trans
      (le_consF_right _ _ h2)).trans (le_consF_right _ _ h3),
    (((le_consF_right _ _ hF).trans (le_consF_right _ _ h1)).trans
      (le_consF_right _ _ h2)).trans (le_consF_right _ _ h3)⟩

/-- A branch that pushes a frame and a symbol and returns a call. -/
theorem bnd_pushBranch {a b k j l c Fr x ρ : ℕ} {env : List ℕ} (ha : a < env.length)
    (hb : b < env.length) (hk : k < env.length) (hj : j < env.length) (hl : l < env.length)
    (hc : c < env.length) (hFr : Fr < env.length) (hx : x < env.length) (hρ : ρ < env.length)
    (hFr1 : 1 ≤ (lvl Fr).denote w env) (hρ1 : 1 ≤ (lvl ρ).denote w env)
    (hout : mkF ((lvl a).denote w env) ((lvl b).denote w env)
      (pushF ((lvl k).denote w env) ((lvl j).denote w env) ((lvl l).denote w env)
        ((lvl c).denote w env) ((lvl Fr).denote w env))
      (consF ((lvl x).denote w env) ((lvl ρ).denote w env)) ≤ B) :
    (letT (pushT (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr)) fun F' =>
      letT (consT (lvl x) (lvl ρ)) fun P' => mkT (lvl a) (lvl b) F' P').Bnd w B env := by
  obtain ⟨-, -, hc3, hd4⟩ := mkF_le _ _ _ _
  rw [bnd_letT]
  refine ⟨bnd_pushT hk hj hl hc hFr hFr1 (hc3.trans hout), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_consT (by lvl_disch) (by lvl_disch)
      (by simp (disch := lvl_disch) only [lvl_cons]; exact hρ1) (by
    simp (disch := lvl_disch) only [lvl_cons]; exact hd4.trans hout), ?_⟩
  refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
  simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_pushT, denote_consT]
  exact hout

theorem bnd_advT {k j l c Fr ρ z o : ℕ} {env : List ℕ} (hk : k < env.length)
    (hj : j < env.length) (_hl : l < env.length) (hc : c < env.length) (hFr : Fr < env.length)
    (hρ : ρ < env.length) (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1)
    (hFr1 : 1 ≤ (lvl Fr).denote w env) (hρ1 : 1 ≤ (lvl ρ).denote w env)
    (hsmall : (lvl l).denote w env + 1 ≤ B ∧ (lvl j).denote w env + 1 ≤ B ∧ 2 ≤ B)
    (hout : advF ((lvl k).denote w env) ((lvl j).denote w env) ((lvl l).denote w env)
        ((lvl c).denote w env) ((lvl Fr).denote w env) ((lvl ρ).denote w env) ≤ B) :
    (advT (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr) (lvl ρ) (lvl z) (lvl o)).Bnd w B env := by
  have hz0' : ∀ x, (lvl z).denote w (x :: env) = 0 := fun x => by rw [lvl_cons hz, hz0]
  have ho1' : ∀ x, (lvl o).denote w (x :: env) = 1 := fun x => by rw [lvl_cons ho, ho1]
  unfold advT advF at *
  rw [bnd_ite]
  refine ⟨by simp, ?_⟩
  rw [denote_lt]
  by_cases h1 : (lvl l).denote w env < (lvl j).denote w env
  · simp only [h1, ite_true, zero_lt_one] at hout ⊢
    rw [bnd_letT]
    refine ⟨by simp only [bnd_add, bnd_lvl, ho1, Order.add_one_le_iff,
        true_and]; exact hsmall.1, ?_⟩
    refine bnd_pushBranch (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by simp (disch := lvl_disch) only [lvl_cons]; exact hFr1)
      (by simp (disch := lvl_disch) only [lvl_cons]; exact hρ1) ?_
    simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_add, ho1, hz0]
    exact hout
  · simp only [h1, ite_false, lt_irrefl] at hout ⊢
    rw [bnd_ite]
    refine ⟨by simp, ?_⟩
    rw [denote_lt]
    by_cases h2 : (lvl j).denote w env < (lvl k).denote w env
    · simp only [h2, ite_true, zero_lt_one] at hout ⊢
      rw [bnd_letT]
      refine ⟨by simp only [bnd_add, bnd_lvl, ho1, Order.add_one_le_iff,
          true_and]; exact hsmall.2.1, ?_⟩
      rw [bnd_letT]
      refine ⟨by simp [hsmall.2.2], ?_⟩
      refine bnd_pushBranch (a := o) (b := z) (k := k) (l := z) (Fr := Fr) (x := z) (ρ := ρ)
        (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
        (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
        ?_ ?_ ?_
      · simp (disch := lvl_disch) only [lvl_cons]; exact hFr1
      · simp (disch := lvl_disch) only [lvl_cons]; exact hρ1
      · simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_add, denote_div,
          denote_const, ho1, hz0]
        exact hout
    · simp only [h2, ite_false, lt_irrefl] at hout ⊢
      rw [bnd_letT]
      refine ⟨by simp [hsmall.2.2], ?_⟩
      refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
      simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_mod, denote_const, hz0]
      exact hout

theorem bnd_sumRetT {v k j l c Fr i ρ par z o : ℕ} {env : List ℕ} (_hv : v < env.length)
    (hk : k < env.length) (hj : j < env.length) (hl : l < env.length) (_hc : c < env.length)
    (hFr : Fr < env.length) (hi : i < env.length) (hρ : ρ < env.length)
    (hpar : par < env.length) (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1)
    (hFr1 : 1 ≤ (lvl Fr).denote w env) (hρ1 : 1 ≤ (lvl ρ).denote w env)
    (hsmall : (lvl c).denote w env + (lvl v).denote w env ≤ B ∧ (lvl i).denote w env + 1 ≤ B ∧
      (lvl j).denote w env + 1 ≤ B ∧ 2 ≤ B)
    (hpow : 2 ^ (lvl par).denote w env ≤ B)
    (hout : sumRetF ((lvl v).denote w env) ((lvl k).denote w env) ((lvl j).denote w env)
        ((lvl l).denote w env) ((lvl c).denote w env) ((lvl Fr).denote w env)
        ((lvl i).denote w env) ((lvl ρ).denote w env) ((lvl par).denote w env) ≤ B) :
    (sumRetT (lvl v) (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr) (lvl i) (lvl ρ) (lvl par) (lvl z)
        (lvl o)).Bnd w B env := by
  unfold sumRetT sumRetF at *
  rw [bnd_letT]
  refine ⟨by simp only [bnd_add, bnd_lvl, true_and]; exact hsmall.1, ?_⟩
  rw [bnd_letT]
  refine ⟨by
    simp (disch := lvl_disch) only [bnd_add, bnd_lvl, denote_add, true_and, lvl_cons, ho1]
    exact hsmall.2.1, ?_⟩
  rw [bnd_ite]
  refine ⟨?_, ?_⟩
  · simp only [bnd_lt, bnd_lvl, true_and]
    refine bnd_pow2 w B _ _ trivial ?_
    simp (disch := lvl_disch) only [lvl_cons]; exact hpow
  simp (disch := lvl_disch) only [denote_lt, denote_pow2, denote_add, lvl_cons, denote_lvl_let,
    ho1]
  by_cases h1 : (lvl i).denote w env + 1 < 2 ^ (lvl par).denote w env
  · simp only [h1, ite_true, zero_lt_one] at hout ⊢
    refine bnd_pushBranch (a := o) (b := j) (k := k) (l := l) (Fr := Fr) (ρ := ρ)
      (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_ ?_ ?_
    · simp (disch := lvl_disch) only [lvl_cons]; exact hFr1
    · simp (disch := lvl_disch) only [lvl_cons]; exact hρ1
    · simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, ho1]
      exact hout
  · simp only [h1, ite_false, lt_irrefl] at hout ⊢
    rw [bnd_ite]
    refine ⟨by simp, ?_⟩
    simp (disch := lvl_disch) only [denote_lt, lvl_cons]
    by_cases h2 : (lvl j).denote w env < (lvl k).denote w env
    · simp only [h2, ite_true, zero_lt_one] at hout ⊢
      rw [bnd_letT]
      refine ⟨by
        simp (disch := lvl_disch) only [bnd_add, bnd_lvl, true_and, lvl_cons, ho1]
        exact hsmall.2.2.1, ?_⟩
      rw [bnd_letT]
      refine ⟨by simp [hsmall.2.2.2], ?_⟩
      refine bnd_pushBranch (a := o) (k := k) (l := l) (Fr := Fr) (x := z) (ρ := ρ)
        (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
        (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_ ?_ ?_
      · simp (disch := lvl_disch) only [lvl_cons]; exact hFr1
      · simp (disch := lvl_disch) only [lvl_cons]; exact hρ1
      · simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_add, denote_div,
          denote_const, ho1, hz0]
        exact hout
    · simp only [h2, ite_false, lt_irrefl] at hout ⊢
      rw [bnd_letT]
      refine ⟨by simp [hsmall.2.2.2], ?_⟩
      refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
      simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_mod, denote_const, hz0]
      exact hout

theorem bnd_prodRetT {v k j l c Fr i ρ z o : ℕ} {env : List ℕ} (_hv : v < env.length)
    (hk : k < env.length) (hj : j < env.length) (hl : l < env.length) (hc : c < env.length)
    (hFr : Fr < env.length) (_hi : i < env.length) (hρ : ρ < env.length)
    (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1)
    (hFr1 : 1 ≤ (lvl Fr).denote w env) (hρ1 : 1 ≤ (lvl ρ).denote w env)
    (hsmall : (lvl c).denote w env + (lvl v).denote w env ≤ B ∧ (lvl l).denote w env + 1 ≤ B ∧
      (lvl j).denote w env + 1 ≤ B ∧ 2 ≤ B)
    (hout : prodRetF ((lvl v).denote w env) ((lvl k).denote w env) ((lvl j).denote w env)
        ((lvl l).denote w env) ((lvl c).denote w env) ((lvl Fr).denote w env)
        ((lvl i).denote w env) ((lvl ρ).denote w env) ≤ B) :
    (prodRetT (lvl v) (lvl k) (lvl j) (lvl l) (lvl c) (lvl Fr) (lvl i) (lvl ρ) (lvl z)
        (lvl o)).Bnd w B env := by
  unfold prodRetT prodRetF at *
  rw [bnd_ite]
  refine ⟨by simp, ?_⟩
  simp (disch := lvl_disch) only [denote_lt, hz0]
  by_cases h1 : 0 < (lvl i).denote w env
  · simp only [h1, ite_true, zero_lt_one] at hout ⊢
    rw [bnd_letT]
    refine ⟨by simp only [bnd_add, bnd_lvl, true_and]; exact hsmall.1, ?_⟩
    refine bnd_advT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_ ?_ ?_ ?_ ?_ ?_
    · simp (disch := lvl_disch) only [lvl_cons]; exact hz0
    · simp (disch := lvl_disch) only [lvl_cons]; exact ho1
    · simp (disch := lvl_disch) only [lvl_cons]; exact hFr1
    · simp (disch := lvl_disch) only [lvl_cons]; exact hρ1
    · simp (disch := lvl_disch) only [lvl_cons]; exact hsmall.2
    · simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_add]; exact hout
  · simp only [h1, ite_false, lt_irrefl] at hout ⊢
    rw [bnd_ite]
    refine ⟨by simp, ?_⟩
    simp (disch := lvl_disch) only [denote_lt, hz0]
    by_cases h2 : 0 < (lvl v).denote w env
    · simp only [h2, ite_true, zero_lt_one] at hout ⊢
      rw [bnd_letT]
      refine ⟨by simp, ?_⟩
      refine bnd_pushBranch (a := o) (k := k) (j := j) (l := l) (c := c) (Fr := Fr) (x := o)
        (ρ := ρ) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
        (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_ ?_ ?_
      · simp (disch := lvl_disch) only [lvl_cons]; exact hFr1
      · simp (disch := lvl_disch) only [lvl_cons]; exact hρ1
      · simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_sub, ho1]
        exact hout
    · simp only [h2, ite_false, lt_irrefl] at hout ⊢
      exact bnd_advT hk hj hl hc hFr hρ hz ho hz0 ho1 hFr1 hρ1 hsmall.2 hout

theorem bnd_hdT_code {a : ℕ} {env : List ℕ} (ha : a < env.length) {x : ℕ} {l : List ℕ}
    (he : (lvl a).denote w env = enc (x :: l)) (hB : enc (x :: l) ≤ B) :
    (hdT (lvl a)).Bnd w B env :=
  bnd_hdT ha (he ▸ hB) (by rw [he]; exact (two_pow_tOnesF_le x l).trans hB)

theorem bnd_tlT_code {a : ℕ} {env : List ℕ} (ha : a < env.length) {x : ℕ} {l : List ℕ}
    (he : (lvl a).denote w env = enc (x :: l)) (hB : enc (x :: l) ≤ B) :
    (tlT (lvl a)).Bnd w B env :=
  bnd_tlT ha (he ▸ hB) (by rw [he]; exact (two_pow_tOnesF_le x l).trans hB)

theorem bnd_callT (Q : Queries) {len v F Pa z o : ℕ} {env : List ℕ} (hlen : len < env.length)
    (hv : v < env.length) (hF : F < env.length) (hPa : Pa < env.length)
    (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1)
    (hF1 : 1 ≤ (lvl F).denote w env) (hPa1 : 1 ≤ (lvl Pa).denote w env) (h4 : 4 ≤ B)
    (hqt : Q.tag.Bounded w B [(lvl Pa).denote w env, (lvl len).denote w env])
    (hqp : Q.prec.Bounded w B [(lvl Pa).denote w env, (lvl len).denote w env])
    (hqa : Q.param.Bounded w B [(lvl Pa).denote w env, (lvl len).denote w env])
    (hqb : (lvl v).denote w env < Q.qp w ((lvl len).denote w env) ((lvl Pa).denote w env) →
      Q.qt w ((lvl len).denote w env) ((lvl Pa).denote w env) < 1 →
      Q.bit.Bounded w B [(lvl v).denote w env, (lvl Pa).denote w env, (lvl len).denote w env])
    (htag : (lvl v).denote w env < Q.qp w ((lvl len).denote w env) ((lvl Pa).denote w env) →
      Q.qt w ((lvl len).denote w env) ((lvl Pa).denote w env) < 4)
    (hout : callF (Q.qt w ((lvl len).denote w env)) (Q.qp w ((lvl len).denote w env))
        (Q.qa w ((lvl len).denote w env)) (Q.qb w ((lvl len).denote w env))
        ((lvl v).denote w env) ((lvl F).denote w env) ((lvl Pa).denote w env) ≤ B) :
    (callT Q (lvl len) (lvl v) (lvl F) (lvl Pa) (lvl z) (lvl o)).Bnd w B env := by
  unfold callT
  unfold callF at hout
  simp only [Queries.qt, Queries.qp, Queries.qa, Queries.qb] at hout hqb htag
  rw [bnd_letT]
  refine ⟨bnd_callT2 Q.tag_closed hPa hlen hqt, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT2 Q.prec_closed (by lvl_disch) (by lvl_disch) (by
    simp (disch := lvl_disch) only [lvl_cons]; exact hqp), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT2 Q.param_closed (by lvl_disch) (by lvl_disch) (by
    simp (disch := lvl_disch) only [lvl_cons]; exact hqa), ?_⟩
  rw [bnd_ite]
  refine ⟨by simp, ?_⟩
  simp (disch := lvl_disch) only [denote_lt, lvl_cons, denote_lvl_let, denote_callT2 Q.tag_closed,
    denote_callT2 Q.prec_closed, denote_callT2 Q.param_closed]
  by_cases h1 : (lvl v).denote w env < Q.prec.eval w [(lvl Pa).denote w env, (lvl len).denote w env]
  · simp only [h1, ite_true, zero_lt_one] at hout ⊢
    rw [bnd_ite]
    refine ⟨by simp, ?_⟩
    simp (disch := lvl_disch) only [denote_lt, lvl_cons, denote_lvl_let, ho1]
    by_cases h2 : Q.tag.eval w [(lvl Pa).denote w env, (lvl len).denote w env] < 1
    · simp only [h2, ite_true, zero_lt_one] at hout ⊢
      rw [bnd_letT]
      refine ⟨bnd_callT3 Q.bit_closed (by lvl_disch) (by lvl_disch) (by lvl_disch) (by
        simp (disch := lvl_disch) only [lvl_cons]; exact hqb h1 h2), ?_⟩
      rw [bnd_letT]
      refine ⟨by simp, ?_⟩
      refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
      simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_lt, hz0,
        denote_callT3 Q.bit_closed]
      exact hout
    · simp only [h2, ite_false, lt_irrefl] at hout ⊢
      have ht4 := htag h1
      -- The pushed frame and symbol are parts of the result.
      have hparts : pushF ((lvl v).denote w env) 0 0 0 ((lvl F).denote w env) ≤ B ∧
          consF 0 ((lvl Pa).denote w env) ≤ B := by
        by_cases h3 : Q.tag.eval w [(lvl Pa).denote w env, (lvl len).denote w env] < 3
        · simp only [h3, ite_true] at hout
          exact ⟨(mkF_le _ _ _ _).2.2.1.trans hout, (mkF_le _ _ _ _).2.2.2.trans hout⟩
        · simp only [h3, ite_false, ht4, ite_true] at hout
          exact ⟨(mkF_le _ _ _ _).2.2.1.trans hout, (mkF_le _ _ _ _).2.2.2.trans hout⟩
      rw [bnd_letT]
      refine ⟨bnd_pushT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
        (by lvl_disch) (by simp (disch := lvl_disch) only [lvl_cons]; exact hF1) (by
          simp (disch := lvl_disch) only [lvl_cons, hz0]; exact hparts.1), ?_⟩
      rw [bnd_letT]
      refine ⟨bnd_consT (by lvl_disch) (by lvl_disch) (by
          simp (disch := lvl_disch) only [lvl_cons]; exact hPa1) (by
          simp (disch := lvl_disch) only [lvl_cons, hz0]; exact hparts.2), ?_⟩
      rw [bnd_ite]
      refine ⟨by simp; omega, ?_⟩
      simp (disch := lvl_disch) only [denote_lt, lvl_cons, denote_lvl_let, denote_const]
      by_cases h3 : Q.tag.eval w [(lvl Pa).denote w env, (lvl len).denote w env] < 3
      · simp only [h3, ite_true, zero_lt_one] at hout ⊢
        refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
        simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_pushT, denote_consT, hz0,
          ho1]
        exact hout
      · simp only [h3, ite_false, lt_irrefl] at hout ⊢
        rw [bnd_ite]
        refine ⟨by simp [h4], ?_⟩
        simp (disch := lvl_disch) only [denote_lt, lvl_cons, denote_lvl_let, denote_const]
        simp only [ht4, ite_true, zero_lt_one] at hout ⊢
        rw [bnd_letT]
        refine ⟨by
          simp (disch := lvl_disch) only [bnd_add, bnd_lvl, true_and, lvl_cons, denote_lvl_let]
          exact (mkF_le _ _ _ _).2.1.trans hout, ?_⟩
        refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
        simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let, denote_pushT, denote_consT, hz0,
          ho1, denote_add]
        exact hout
  · simp only [h1, ite_false, lt_irrefl] at hout ⊢
    refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
    simp (disch := lvl_disch) only [lvl_cons, hz0]
    exact hout

set_option hygiene false in
/-- Compute the values of variables in the return branch. -/
macro "ret_vals" : tactic => `(tactic| simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let,
  denote_hdT, denote_tlT, denote_callT2 Q.tag_closed, denote_callT2 Q.param_closed, hFv, hPav,
  hdF_enc_cons, tlF_enc_cons, hz0, ho1])

theorem bnd_retT (Q : Queries) {len v F Pa z o : ℕ} {env : List ℕ} (hlen : len < env.length)
    (hv : v < env.length) (hF : F < env.length) (hPa : Pa < env.length)
    (hz : z < env.length) (ho : o < env.length)
    (hz0 : (lvl z).denote w env = 0) (ho1 : (lvl o).denote w env = 1)
    (fr : List Frame) (π : List ℕ) (hFv : (lvl F).denote w env = enc (flatFrames fr))
    (hPav : (lvl Pa).denote w env = enc π) (hshape : fr ≠ [] → π ≠ [])
    (hFB : enc (flatFrames fr) + 1 ≤ B) (hPaB : enc π + 1 ≤ B) (hv1 : (lvl v).denote w env ≤ 1)
    (h4 : 4 ≤ B)
    (hq : fr ≠ [] → Q.tag.Bounded w B [enc π.tail, (lvl len).denote w env] ∧
      Q.param.Bounded w B [enc π.tail, (lvl len).denote w env] ∧
      (Q.qt w ((lvl len).denote w env) (enc π.tail) = 1 →
        2 ^ Q.qa w ((lvl len).denote w env) (enc π.tail) ≤ B))
    (hout : retF (Q.qt w ((lvl len).denote w env)) (Q.qa w ((lvl len).denote w env))
        ((lvl v).denote w env) ((lvl F).denote w env) ((lvl Pa).denote w env) ≤ B) :
    (retT Q (lvl len) (lvl v) (lvl F) (lvl Pa) (lvl z) (lvl o)).Bnd w B env := by
  unfold retT
  unfold retF at hout
  rw [bnd_ite]
  refine ⟨by simp; omega, ?_⟩
  simp only [denote_lt, denote_const]
  by_cases h : (lvl F).denote w env < 2
  · simp only [h, ite_true, zero_lt_one] at hout ⊢
    refine bnd_mkT hz hv hF hPa ?_
    rw [hz0]; exact hout
  · simp only [h, ite_false, lt_irrefl] at hout ⊢
    have hfr : fr ≠ [] := fun he => h (by rw [hFv, he]; simp [flatFrames])
    obtain ⟨f, fr', rfl⟩ := List.exists_cons_of_ne_nil hfr
    obtain ⟨i, ρ, rfl⟩ := List.exists_cons_of_ne_nil (hshape hfr)
    obtain ⟨hqt, hqa, hpow⟩ := hq hfr
    simp only [List.tail_cons] at hqt hqa hpow
    obtain ⟨k, j, l, c⟩ := f
    rw [flatFrames_cons] at hFv hFB
    dsimp only at hFv hFB
    simp only [hFv, hPav, hdF_enc_cons, tlF_enc_cons] at hout
    -- Sizes of the decoded fields.
    have e1 := enc_le_enc_cons k (j :: l :: c :: flatFrames fr')
    have e2 := enc_le_enc_cons j (l :: c :: flatFrames fr')
    have e3 := enc_le_enc_cons l (c :: flatFrames fr')
    have e4 := enc_le_enc_cons c (flatFrames fr')
    have ec := le_enc_cons c (flatFrames fr')
    have ej := le_enc_cons j (l :: c :: flatFrames fr')
    have el := le_enc_cons l (c :: flatFrames fr')
    have ei := le_enc_cons i ρ
    have eρ := enc_le_enc_cons i ρ
    have hFr1 := enc_pos (flatFrames fr')
    have hρ1 := enc_pos ρ
    -- Decode the frame and the path.
    rw [bnd_letT]
    refine ⟨bnd_hdT_code hF hFv (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_tlT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_hdT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_tlT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_hdT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_tlT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_hdT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_tlT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_hdT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_tlT_code (by lvl_disch) (by ret_vals; rfl) (by omega), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_callT2 Q.tag_closed (by lvl_disch) (by lvl_disch) (by ret_vals; exact hqt), ?_⟩
    rw [bnd_letT]
    refine ⟨bnd_callT2 Q.param_closed (by lvl_disch) (by lvl_disch) (by ret_vals; exact hqa), ?_⟩
    simp only [Queries.qt, Queries.qa] at hout hpow
    rw [bnd_ite]
    refine ⟨by simp, ?_⟩
    simp only [denote_lt]
    ret_vals
    by_cases t0 : Q.tag.eval w [enc ρ, (lvl len).denote w env] < 1
    · simp only [t0, ite_true, zero_lt_one] at hout ⊢
      refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
      ret_vals; exact hout
    · simp only [t0, ite_false, lt_irrefl] at hout ⊢
      rw [bnd_ite]
      refine ⟨by simp; omega, ?_⟩
      simp only [denote_lt, denote_const]
      ret_vals
      by_cases t1 : Q.tag.eval w [enc ρ, (lvl len).denote w env] < 2
      · simp only [t1, ite_true, zero_lt_one] at hout ⊢
        refine bnd_sumRetT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
          (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
          (by lvl_disch) (by lvl_disch) (by ret_vals) (by ret_vals) (by ret_vals; exact hFr1)
          (by ret_vals; exact hρ1) (by ret_vals; omega) (by ret_vals; exact hpow (by omega))
          (by ret_vals; exact hout)
      · simp only [t1, ite_false, lt_irrefl] at hout ⊢
        rw [bnd_ite]
        refine ⟨by simp; omega, ?_⟩
        simp only [denote_lt, denote_const]
        ret_vals
        by_cases t2 : Q.tag.eval w [enc ρ, (lvl len).denote w env] < 3
        · simp only [t2, ite_true, zero_lt_one] at hout ⊢
          refine bnd_prodRetT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
            (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
            (by lvl_disch) (by ret_vals) (by ret_vals) (by ret_vals; exact hFr1)
            (by ret_vals; exact hρ1) (by ret_vals; omega) (by ret_vals; exact hout)
        · simp only [t2, ite_false, lt_irrefl] at hout ⊢
          refine bnd_mkT (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) ?_
          ret_vals; exact hout

set_option hygiene false in
/-- Compute the values of variables in the step. -/
macro "step_vals" : tactic => `(tactic| simp (disch := lvl_disch) only [lvl_cons, denote_lvl_let,
  denote_hdT, denote_tlT, denote_const, hSv, State.code, hdF_enc_cons, tlF_enc_cons])

/-- **Value bounds of one step.** -/
theorem bnd_stepT (Q : Queries) {len S : ℕ} {env : List ℕ} (hlen : len < env.length)
    (hS : S < env.length) (st : State) (hSv : (lvl S).denote w env = st.code)
    (hshape : st.frames ≠ [] → st.path ≠ []) (hB : st.code + 1 ≤ B) (h4 : 4 ≤ B)
    (hv1 : st.call = false → st.v ≤ 1)
    (hcall : st.call = true →
      Q.tag.Bounded w B [enc st.path, (lvl len).denote w env] ∧
      Q.prec.Bounded w B [enc st.path, (lvl len).denote w env] ∧
      Q.param.Bounded w B [enc st.path, (lvl len).denote w env] ∧
      (st.v < Q.qp w ((lvl len).denote w env) (enc st.path) →
        Q.qt w ((lvl len).denote w env) (enc st.path) < 1 →
        Q.bit.Bounded w B [st.v, enc st.path, (lvl len).denote w env]) ∧
      (st.v < Q.qp w ((lvl len).denote w env) (enc st.path) →
        Q.qt w ((lvl len).denote w env) (enc st.path) < 4))
    (hret : st.call = false → st.frames ≠ [] →
      Q.tag.Bounded w B [enc st.path.tail, (lvl len).denote w env] ∧
      Q.param.Bounded w B [enc st.path.tail, (lvl len).denote w env] ∧
      (Q.qt w ((lvl len).denote w env) (enc st.path.tail) = 1 →
        2 ^ Q.qa w ((lvl len).denote w env) (enc st.path.tail) ≤ B))
    (hout : stepF (Q.qt w ((lvl len).denote w env)) (Q.qp w ((lvl len).denote w env))
        (Q.qa w ((lvl len).denote w env)) (Q.qb w ((lvl len).denote w env)) st.code ≤ B) :
    (stepT Q (lvl len) (lvl S)).Bnd w B env := by
  obtain ⟨call, v, fr, π⟩ := st
  dsimp only at hshape hv1 hcall hret
  have hc : State.code ⟨call, v, fr, π⟩ =
      enc [call.toNat, v, enc (flatFrames fr), enc π] := rfl
  rw [hc] at hB hSv
  unfold stepF at hout
  rw [hc] at hout
  simp only [hdF_enc_cons, tlF_enc_cons] at hout
  have s1 := enc_le_enc_cons call.toNat [v, enc (flatFrames fr), enc π]
  have s2 := enc_le_enc_cons v [enc (flatFrames fr), enc π]
  have s3 := enc_le_enc_cons (enc (flatFrames fr)) [enc π]
  have sF := le_enc_cons (enc (flatFrames fr)) [enc π]
  have sP := le_enc_cons (enc π) []
  have sv := le_enc_cons v [enc (flatFrames fr), enc π]
  unfold stepT
  rw [bnd_letT]
  refine ⟨bnd_hdT_code hS hSv (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_tlT_code (by lvl_disch) (by step_vals; rfl) (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_hdT_code (by lvl_disch) (by step_vals; rfl) (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_tlT_code (by lvl_disch) (by step_vals; rfl) (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_hdT_code (by lvl_disch) (by step_vals; rfl) (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_tlT_code (by lvl_disch) (by step_vals; rfl) (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_hdT_code (by lvl_disch) (by step_vals; rfl) (by omega), ?_⟩
  rw [bnd_letT]
  refine ⟨by simp, ?_⟩
  rw [bnd_letT]
  refine ⟨by simp; omega, ?_⟩
  rw [bnd_ite]
  refine ⟨trivial, ?_⟩
  step_vals
  have hF1 := enc_pos (flatFrames fr)
  have hP1 := enc_pos π
  cases call with
  | true =>
    simp only [Bool.toNat_true, zero_lt_one, ite_true] at hout ⊢
    obtain ⟨hqt, hqp, hqa, hqb, htag⟩ := hcall rfl
    refine bnd_callT Q (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by step_vals) (by step_vals) (by step_vals; exact hF1)
      (by step_vals; exact hP1) h4 (by step_vals; exact hqt) (by step_vals; exact hqp)
      (by step_vals; exact hqa) (by step_vals; exact hqb) (by step_vals; exact htag)
      (by step_vals; exact hout)
  | false =>
    simp only [Bool.toNat_false, lt_irrefl, ite_false] at hout ⊢
    refine bnd_retT Q (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch) (by lvl_disch)
      (by lvl_disch) (by step_vals) (by step_vals) fr π (by step_vals) (by step_vals) hshape
      (by omega) (by omega) (by step_vals; exact hv1 rfl) h4 (fun h => by
        step_vals; exact hret rfl h) (by step_vals; exact hout)

end Cslib.Complexity.NtimeDspace.SumProduct
