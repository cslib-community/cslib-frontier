/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Interp
import CslibFrontier.Foundations.Data.List.Forall2
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq

/-!
# The interpreter

`Interpreter.IF` at `(IF, (f, (x, t)))` simulates the formula `f` at `x` with the budgets `t`;
instead of multiplying by a named constant it subtracts `1` from the budget of that name. Its value
is the value of the run and the budgets that are left. `Interpreter.simS` describes the simulated
runs.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `NS1.Eval`.

## Main definitions

* `Interpreter.IF`, `Interpreter.env`.
* `Interpreter.SimRun`: a simulated run, with the run of the formula (`run`) and the budgets left
  after its bill (`left`); `Interpreter.simS t l`: the simulated runs of `l` that fit into `t`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Rel

variable {α β γ δ : Type*}

/-- A `Forall₂` relation also records that both elements come from the lists. -/
private theorem forall₂_mem {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : List.Forall₂ (fun a b => a ∈ l ∧ b ∈ l' ∧ R a b) l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons ⟨List.mem_cons_self, List.mem_cons_self, hab⟩
      (ih.imp fun a b ⟨ha, hb, h⟩ => ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, h⟩)

/-- `let`, for lists that correspond to other lists. -/
theorem lett_rel {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le) {Q : List β}
    {R : Run A → β → Prop} (hR : List.Forall₂ R le Q) {Q2 : β → List γ} {R2 : Run A → γ → Prop}
    (h : ∀ s ∈ le, ∀ b ∈ Q, R s b → ∃ l2, Ev θ body s.out l2 ∧
      List.Forall₂ (fun t c => R2 ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩ c) l2
          (Q2 b)) :
    ∃ l, Ev θ (lett e body) x l ∧ List.Forall₂ R2 l (Q.flatMap Q2) := by
  refine ⟨_, Ev.lett he fun s hs => ?_,
      List.rel_flatMap (forall₂_mem hR) fun s b ⟨hs, hb, hsb⟩ => ?_⟩
  · obtain ⟨b, hb, hsb⟩ := hR.exists_mem_of_mem hs
    obtain ⟨l2, h2, -⟩ := h s hs b hb hsb
    exact h2.hl
  · obtain ⟨l2, h2, h3⟩ := h s hs b hb hsb
    rw [h2.evl, List.forall₂_map_left_iff]
    exact h3

end Rel

section Cases

/-- Choose by the length of the value of `b`. -/
@[expose] def selF : List Fm → Fm → Fm
  | [], _ => .fail
  | c :: cs, b => .ite b (selF cs (.tl b)) c

theorem selF_ev {cs : List Fm} {b : Fm} {x o : Tree} {k : ℕ} (hb : Dt θ b x o k) {l : List (Run A)}
    (h : ∀ c, cs[o.len]? = some c → Ev θ c x l) (h0 : cs.length ≤ o.len → l = []) :
    ∃ k' ≤ cs.length * (k + cs.length + 1), Ev θ (selF cs b) x (l.map (Run.delay k')) := by
  induction cs generalizing b o k with
  | nil => exact ⟨0, Nat.zero_le _, h0 (Nat.zero_le _) ▸ .fail x⟩
  | cons c cs ih =>
    cases o with
    | nil => exact ⟨k + 1, by simp only [List.length_cons]; nlinarith, Ev.ite_false hb (h c rfl)⟩
    | cons a o =>
      obtain ⟨k', hk', h'⟩ := ih (b := .tl b) (o := o) hb.tl
        (fun c hc => h c (by simpa [len] using hc))
        fun hl => h0 (by simp only [List.length_cons, len]; omega)
      refine ⟨k + 1 + k', by simp only [List.length_cons]; linarith,
        Eq.mp (congrArg (Ev θ _ _) ?_) (Ev.ite_true (c := c) hb (by simp) h')⟩
      rw [List.map_map]
      exact List.map_congr_left fun r _ => by
        simp only [Run.delay, Function.comp_apply, Run.mk.injEq, and_true]; omega

end Cases

section Code

/-- The formula in the environment. -/
@[expose] def fF (b : Fm) : Fm := .hd (.tl b)
/-- The argument in the environment. -/
@[expose] def fX (b : Fm) : Fm := .hd (.tl (.tl b))
/-- The budgets in the environment. -/
@[expose] def fS (b : Fm) : Fm := .tl (.tl (.tl b))
/-- The opcode. -/
@[expose] def fO (b : Fm) : Fm := .hd (fF b)
/-- The arguments of the formula. -/
@[expose] def fA (b : Fm) : Fm := .tl (fF b)
/-- Recursive call. -/
@[expose] def rec' (b a x s : Fm) : Fm := .run (.hd b) (.cons (.hd b) (.cons a (.cons x s)))

/-- First call, with the environment kept. -/
@[expose] def call1 : Fm := .cons .id (rec' .id (.hd (fA .id)) (fX .id) (fS .id))

/-- Second call, with everything kept. -/
@[expose] def call2 : Fm :=
    .cons .id (rec' (.hd .id) (.tl (fA (.hd .id))) (fX (.hd .id)) (.tl (.tl .id)))

/-- The cases of the interpreter. -/
@[expose] def caseL : List Fm := [
  -- quote
  .cons (fA .id) (fS .id),
  -- id
  .cons (fX .id) (fS .id),
  -- hd
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.hd (.hd .id)) (.tl .id)),
  -- tl
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.tl (.hd .id)) (.tl .id)),
  -- cons
  lett call1 (lett call2 (.cons (.cons (.hd (.tl (.hd .id))) (.hd (.tl .id))) (.tl (.tl .id)))),
  -- ite
  lett call1 (.ite (.hd (.tl .id))
    (rec' (.hd .id) (.hd (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))
    (rec' (.hd .id) (.tl (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))),
  -- run
  lett call1
      (lett call2 (rec' (.hd (.hd .id)) (.hd (.tl (.hd .id))) (.hd (.tl .id)) (.tl (.tl .id)))),
  -- guess
  .cons .guess (fS .id),
  -- fail
  .fail,
  -- theta
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.theta (.hd .id)) (.tl .id)),
  -- mul
  lett (rec' .id (fA .id) (fX .id) (fS .id))
      (.cons (.quote .nil) (.run (.quote DC.code) (.cons (.quote DC.code) .id)))
  ]

/-- The interpreter. -/
@[expose] def IF : Fm := selF caseL (fO .id)

/-- The environment of the interpreter. -/
@[expose] def env (f x : Tree) (t : Bt) : Tree := .cons IF.code (.cons f (.cons x t.enc))

theorem Dt.fX {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fX b) y
    x (k + 3) :=
  .hd (.tl (.tl h))

theorem Dt.fS {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fS b) y
    t.enc (k + 3) :=
  .tl (.tl (.tl h))

theorem Dt.fO {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fO b) y
    f.hd (k + 3) :=
  .hd (.hd (.tl h))

theorem Dt.fA {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fA b) y
    f.tl (k + 3) :=
  .tl (.hd (.tl h))

/-- A recursive call. -/
theorem rec_ev {b a x s : Fm} {y g z : Tree} {f' x' : Tree} {t t' : Bt} {kb ka kx ks : ℕ}
    (hb : Dt θ b y (env f' x' t') kb) (ha : Dt θ a y g ka) (hx : Dt θ x y z kx)
        (hs : Dt θ s y t.enc ks)
    {l : List (Run A)} (h : Ev θ IF (env g z t) l) :
    Ev θ (rec' b a x s) y (l.map (Run.delay (2 * kb + ka + kx + ks + 6))) := by
  have := Ev.run_det (Dt.hd hb) (.cons (.hd hb) (.cons ha (.cons hx hs))) (l := l) (by
    change Ev θ (Fm.ofTree IF.code) _ l
    rw [Fm.ofTree_code]
    exact h)
  refine Eq.mp ?_ this
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.delay, Run.mk.injEq, and_true]
  omega

/-- A simulated run: a run of the formula, together with the budgets left after its bill. -/
structure SimRun (A : Type) where
  /-- the run of the simulated formula -/
  run : Run A
  /-- the budgets left after paying its bill -/
  left : Bt

/-- The simulated runs of `l` with the budgets `t`: those whose bill fits into `t`. -/
@[expose] def simS (t : Bt) (l : List (Run A)) : List (SimRun A) :=
  l.filterMap fun r => (Bt.decAll r.bill t).map fun t' => ⟨r, t'⟩

omit [CommRing A] in
theorem mem_simS {t : Bt} {l : List (Run A)} {q : SimRun A} (h : q ∈ simS t l) :
    q.run ∈ l ∧ Bt.decAll q.run.bill t = some q.left := by
  obtain ⟨r, hr, h⟩ := List.mem_filterMap.1 h
  obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨hr, ht⟩

omit [CommRing A] in
theorem simS_map {t : Bt} {l : List (Run A)} {G : Run A → Run A} (h : ∀ r, (G r).bill = r.bill) :
    simS t (l.map G) = (simS t l).map fun q => ⟨G q.run, q.left⟩ := by
  simp only [simS, List.filterMap_map, List.map_filterMap]
  exact List.filterMap_congr fun r _ => by simp [Function.comp_def, h]

omit [CommRing A] in
theorem simS_append {t : Bt} {l l' : List (Run A)} : simS t (l ++ l') = simS t l ++ simS t l' := by
  simp [simS]

omit [CommRing A] in
theorem simS_flatMap {t : Bt} {la : List (Run A)} {L : Run A → List (Run A)}
    {G : Run A → Run A → Run A}
    (h : ∀ r s, (G r s).bill = r.bill ++ s.bill) : simS t (la.flatMap fun r => (L r).map (G r)) =
      (simS t la).flatMap fun q => (simS q.left (L q.run)).map fun p => ⟨G q.run p.run, p.left⟩ :=
          by
  induction la with
  | nil => rfl
  | cons r la ih =>
    rw [List.flatMap_cons, simS_append, ih]
    simp only [simS, List.filterMap_cons, List.filterMap_map]
    cases hd : Bt.decAll r.bill t with
    | none =>
      simpa [List.filterMap_eq_nil_iff] using fun s _ => by simp [h, Bt.decAll_append, hd]
    | some t' =>
      simp only [Option.map_some, List.flatMap_cons, List.map_filterMap]
      congr 1
      exact List.filterMap_congr fun s _ => by simp [Function.comp_def, h, Bt.decAll_append, hd]

end Code

end Cslib.Circuits.Arithmetic.Separation.Interpreter
