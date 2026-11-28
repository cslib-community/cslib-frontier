/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.Primrec.List

/-!
# The stack machine of a partial recursive code on finitely many labels

Mathlib compiles a code `c : Turing.ToPartrec.Code` to the stack machine `Turing.PartrecToTM2.tr`,
whose labels `Λ'` form an infinite type, and shows that a run from `PartrecToTM2.init c v` only
visits the finite set `codeSupp c Cont'.halt` (`PartrecToTM2.tr_supports`). This file turns the
compiled program into a program on that finite set of labels, with the same runs.

Restriction renames the jump targets of each statement. A target outside the
support goes to a fixed label of the support, so the restricted program is defined without proofs,
and the support hypothesis is used only to show that a run is unchanged
(`Turing.TM2.eval_restrict`).

## Main definitions

* `Turing.TM2.Cfg.mapLabel`: rename the label of a configuration.
* `Turing.TM2.restrict`: the program on a finite set of labels.
* `Turing.PartrecToTM2.finProgram`, `Turing.PartrecToTM2.finInit`: the compiled program of a code
  on its finite support, and its initial configuration on an input list.

## Main results

* `Turing.TM2.eval_restrict`: a supported program and its restriction have the same runs.
* `Turing.PartrecToTM2.eval_finProgram`: the restricted program evaluates the code, with the output
  list on the main stack.
* `Turing.PartrecToTM2.trNat_eq_map_bits`: the stack encoding of a number lists its binary digits,
  least significant first.
* `Turing.PartrecToTM2.primrec_trNat`, `Turing.PartrecToTM2.primrec_bits`: the stack encoding of
  numbers and their binary digits `Nat.bits` are primitive recursive.
-/

public section

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ Λ₂ σ : Type*}

/-- Rename the jump targets of a statement. -/
private def Stmt.mapLabel (f : Λ → Λ₂) : Stmt Γ Λ σ → Stmt Γ Λ₂ σ
  | .push k g q => .push k g (q.mapLabel f)
  | .peek k g q => .peek k g (q.mapLabel f)
  | .pop k g q => .pop k g (q.mapLabel f)
  | .load g q => .load g (q.mapLabel f)
  | .branch p q₁ q₂ => .branch p (q₁.mapLabel f) (q₂.mapLabel f)
  | .goto l => .goto fun v => f (l v)
  | .halt => .halt

/-- Rename the label of a configuration, keeping its state and stacks. -/
@[expose] def Cfg.mapLabel (f : Λ → Λ₂) (c : Cfg Γ Λ σ) : Cfg Γ Λ₂ σ :=
  ⟨c.l.map f, c.var, c.stk⟩

variable [DecidableEq K]

/-- Executing a renamed statement renames the label reached. -/
private theorem stepAux_mapLabel (f : Λ → Λ₂) (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux (q.mapLabel f) v S = (stepAux q v S).mapLabel f := by
  induction q generalizing v S with
  | push _ _ _ ih => exact ih _ _
  | peek _ _ _ ih => exact ih _ _
  | pop _ _ _ ih => exact ih _ _
  | load _ _ ih => exact ih _ _
  | branch p _ _ ih₁ ih₂ =>
    simp only [Stmt.mapLabel, stepAux]
    cases p v
    exacts [ih₂ _ _, ih₁ _ _]
  | goto => rfl
  | halt => rfl

variable [DecidableEq Λ] {M : Λ → Stmt Γ Λ σ} {S : Finset Λ}

/-- The program on the labels in `S`. A jump to a label outside `S` goes to `d`. -/
def restrict (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) (d : S) : S → Stmt Γ S σ :=
  fun l => (M l).mapLabel fun l' => if h : l' ∈ S then ⟨l', h⟩ else d

/-- On a configuration in `S`, a step of the restricted program is a step of the program. -/
private theorem step_restrict (hS : ∀ q ∈ S, SupportsStmt S (M q)) (d : S) (c : Cfg Γ S σ) :
    (step (restrict M S d) c).map (Cfg.mapLabel Subtype.val) =
      step M (c.mapLabel Subtype.val) := by
  rcases c with ⟨_ | l, v, T⟩
  · rfl
  let : Inhabited Λ := ⟨d⟩
  have hmem := step_supports M (S := S) ⟨d.property, hS⟩ (c := ⟨some l.val, v, T⟩)
    (Option.mem_def.2 rfl) (Finset.some_mem_insertNone.2 l.property)
  simp only [step, restrict, stepAux_mapLabel, Option.map_some, Cfg.mapLabel, Option.map_map]
  congr 2
  rcases h : (stepAux (M l) v T).l with _ | l'
  · rfl
  · rw [h, Finset.some_mem_insertNone] at hmem
    simp [hmem]

/-- **Restriction preserves runs**: from a configuration in `S`, the program halts exactly when
its restriction does, in the corresponding configuration. -/
theorem eval_restrict (hS : ∀ q ∈ S, SupportsStmt S (M q)) (d : S) (c : Cfg Γ S σ) :
    StateTransition.eval (step M) (c.mapLabel Subtype.val) =
      Cfg.mapLabel Subtype.val <$> StateTransition.eval (step (restrict M S d)) c := by
  refine StateTransition.tr_eval' _ _ _ (StateTransition.fun_respects.2 fun a => ?_) c
  have h := step_restrict hS d a
  rcases ha : step (restrict M S d) a with _ | b <;> rw [ha] at h
  exacts [h.symm, .single h.symm]

end TM2

namespace PartrecToTM2

open ToPartrec

/-- The four stacks of `PartrecToTM2` form a finite type. -/
instance fintypeK' : Fintype K' :=
  ⟨⟨{K'.main, K'.rev, K'.aux, K'.stack}, by decide⟩, fun k => by cases k <;> decide⟩

/-- The binary stack encoding of a positive number starts with its lowest digit. -/
private theorem trNat_eq (n : ℕ) :
    trNat n = if n = 0 then [] else (if n.bodd then Γ'.bit1 else Γ'.bit0) :: trNat n.div2 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn]
    have hnum : trNat n = trNum (Num.bit n.bodd (Num.ofNat' n.div2)) := by
      conv_lhs => rw [← Nat.bit_bodd_div2 n]
      rw [trNat, ← Num.ofNat'_eq, Num.ofNat'_bit]
      cases n.bodd <;> rfl
    rw [hnum, trNat, ← Num.ofNat'_eq]
    cases hb : n.bodd
    · rcases h : Num.ofNat' n.div2 with _ | p
      · have hd : n.div2 = 0 := by rw [← Num.to_of_nat n.div2, ← Num.ofNat'_eq, h]; rfl
        exact absurd (by rw [← Nat.bit_bodd_div2 n, hb, hd]; rfl) hn
      · rfl
    · cases Num.ofNat' n.div2 <;> rfl

/-- The stack encoding of a number lists its binary digits (`Nat.bits`), least significant first,
as `bit0` and `bit1`. -/
theorem trNat_eq_map_bits (n : ℕ) :
    trNat n = n.bits.map fun b => if b then Γ'.bit1 else Γ'.bit0 := by
  induction n using Nat.binaryRec with
  | zero => simp
  | bit b n ih =>
    by_cases h0 : b = false ∧ n = 0
    · rcases h0 with ⟨rfl, rfl⟩
      simp
    · have hne : Nat.bit b n ≠ 0 := by
        cases b <;> simp_all [Nat.bit]
      rw [trNat_eq, ite_eq_right hne, Nat.bodd_bit, Nat.div2_bit,
        Nat.bits_append_bit n b (by cases b <;> simp_all), List.map_cons, ih]

/-- The stack alphabet of `PartrecToTM2` is primcodable through an enumeration. -/
noncomputable instance primcodableΓ' : Primcodable Γ' :=
  Primcodable.ofEquiv _ (Fintype.equivFin Γ')

/-- The stack encoding of numbers is primitive recursive. -/
theorem primrec_trNat : Primrec trNat := by
  have hdig : Primrec fun b : Bool => if b then Γ'.bit1 else Γ'.bit0 := Primrec.dom_finite _
  have hl : Primrec fun p : Unit × List (List Γ') => p.2 := Primrec.snd
  have hlen : Primrec fun p : Unit × List (List Γ') => p.2.length := Primrec.list_length.comp hl
  have hget : Primrec fun p : Unit × List (List Γ') => p.2[p.2.length.div2]? :=
    Primrec.list_getElem?.comp hl (Primrec.nat_div2.comp hlen)
  have hcons : Primrec₂ fun (p : Unit × List (List Γ')) (t : List Γ') =>
      (if p.2.length.bodd then Γ'.bit1 else Γ'.bit0) :: t :=
    Primrec.list_cons.comp₂ (hdig.comp (Primrec.nat_bodd.comp (hlen.comp Primrec.fst))).to₂
      Primrec₂.right
  have hg : Primrec₂ fun (_ : Unit) (l : List (List Γ')) =>
      some (((l[l.length.div2]?).map fun t =>
        (if l.length.bodd then Γ'.bit1 else Γ'.bit0) :: t).getD []) :=
    (Primrec.option_some.comp (Primrec.option_getD.comp (Primrec.option_map hget hcons)
      (Primrec.const ([] : List Γ')))).to₂
  have := Primrec.nat_strong_rec (fun (_ : Unit) n => trNat n) hg fun _ n => by
    rw [show (List.range n).map (fun m => trNat m) = (List.range n).map trNat from rfl,
      List.length_map, List.length_range]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · have hlt : n.div2 < n := by rw [Nat.div2_val]; omega
      rw [List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.map_some,
        Option.getD_some, trNat_eq n, ite_eq_right hn.ne']
  exact (this.comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

/-- The binary digits of a number are primitive recursive. -/
theorem primrec_bits : Primrec Nat.bits :=
  (Primrec.list_map primrec_trNat
    ((Primrec.dom_finite fun x : Γ' => x == Γ'.bit1).comp Primrec.snd).to₂).of_eq fun n => by
    rw [trNat_eq_map_bits, List.map_map]
    exact (List.map_congr_left fun b _ => by cases b <;> rfl).trans (List.map_id _)

/-- The labels that a run of the compiled program of `c` can visit. -/
abbrev Label (c : Code) : Type := (codeSupp c Cont'.halt : Finset Λ')

/-- The initial label of the compiled program of `c`. -/
@[expose] def Label.start (c : Code) : Label c :=
  ⟨trNormal c Cont'.halt, (tr_supports c Cont'.halt).1⟩

/-- The compiled program of `c` on the finitely many labels its runs visit. -/
@[expose] def finProgram (c : Code) :
    Label c → TM2.Stmt (fun _ : K' => Γ') (Label c) (Option Γ') :=
  TM2.restrict tr _ (Label.start c)

/-- The initial configuration of `finProgram c` on the input list `v`: Mathlib's `init c v`, at the
start label. -/
@[expose] def finInit (c : Code) (v : List ℕ) :
    TM2.Cfg (fun _ : K' => Γ') (Label c) (Option Γ') :=
  (init c v).mapLabel fun _ => Label.start c

/-- **The finite program evaluates the code**: it halts on `v` exactly when `c` does, and then
holds the encoded output list on the main stack and nothing on the others. -/
theorem eval_finProgram (c : Code) (v : List ℕ) :
    TM2.Cfg.mapLabel Subtype.val <$> StateTransition.eval (TM2.step (finProgram c)) (finInit c v) =
      halt <$> c.eval v := by
  rw [finProgram, ← TM2.eval_restrict (tr_supports c Cont'.halt).2]
  exact tr_eval c v

end PartrecToTM2

end Turing
