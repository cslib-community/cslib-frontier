/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.TableauDNF
import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Hardness
import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Membership
public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Completeness
import CslibFrontier.Logics.Propositional.CNF.ThreeCNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Complexity.Classes.PH.Closure

/-!
# Width-three quantified normal-form completeness

Apply the 3CNF splitting transformation or its dual under fixed original assignments.
The fresh variables join the final block at its existing polarity. This gives the bounded-
alternation normal forms based on Exercise 5 §1 of [Arora and Barak][AroraBarak07].

## Main definitions

* `SigmaWidthThree` and `PiWidthThree`: width-three problems at each alternation level.

## Main results

* `sigmaWidthThree_complete` and `piWidthThree_complete`: completeness at every positive level.

## References

* [Arora and Barak, Computational Complexity, Exercise 5 §1][AroraBarak07]
-/

public section

namespace Cslib.Complexity.QuantifiedSAT.WidthThree

open Cslib.Logic.PL Cslib.Complexity _root_.Turing.MultiTapeTM ComputableInPolyTime

private def widthThree (d : DNF ℕ) : DNF (ℕ ⊕ (ℕ × ℕ)) :=
  d.negate.to3CNF.negate

/-- A 3DNF matrix preserves truth with the original assignment fixed and all fresh chain
variables universally quantified. The extension lemma keeps the original variable values. -/
private theorem widthThree_eval (d : DNF ℕ) (σ : ℕ → Bool) :
    (∀ τ : ℕ × ℕ → Bool, (widthThree d).eval (Sum.elim σ τ) = true) ↔
      d.eval σ = true := by
  constructor
  · intro h
    cases hd : d.eval σ with
    | true => rfl
    | false =>
      have hcnf : d.negate.eval σ = true := by simp [hd]
      let τ (i : ℕ × ℕ) := d.negate.to3CNFAssignment σ (.inr i)
      have extend : Sum.elim σ τ = d.negate.to3CNFAssignment σ := by
        funext i
        cases i <;> rfl
      have bad := h τ
      rw [extend, widthThree, CNF.eval_negate,
        CNF.eval_to3CNF_to3CNFAssignment hcnf] at bad
      contradiction
  · intro hd τ
    cases h : d.negate.to3CNF.eval (Sum.elim σ τ) with
    | false => simp [widthThree, h]
    | true =>
      have hcnf := CNF.eval_comp_inl_of_eval_to3CNF h
      change d.negate.eval σ = true at hcnf
      simp [hd] at hcnf

/-- Fresh names in occurrence order. Repeated occurrences are harmless because the same
assignment bit is copied for each occurrence when witnessing a particular assignment. -/
private def freshVariables (d : DNF ℕ) : List (ℕ × ℕ) :=
  d.negate.to3CNF.vars.flatMap (Sum.elim (fun _ => []) fun v => [v])

private theorem freshVariables_mem (d : DNF ℕ) (v : ℕ × ℕ) :
    v ∈ freshVariables d ↔ Sum.inr v ∈ d.negate.to3CNF.vars := by
  constructor
  · intro h
    obtain ⟨w, hw, hv⟩ := List.mem_flatMap.mp h
    cases w with
    | inl w => simp at hv
    | inr w => simpa using (List.mem_singleton.mp hv) ▸ hw
  · intro h
    exact List.mem_flatMap.mpr ⟨Sum.inr v, h, by simp⟩

private theorem polytime_freshVariables : ComputableInPolyTime freshVariables (encCNFOver encNat)
    (encList (encPair encUnary encUnary)) := by
  let e := encPair encUnary encUnary
  let name := encSum encNat e
  have hd : ComputableInPolyTime (DNF.negate (V := ℕ))
      (encCNFOver encNat) (encCNFOver encNat) := DNF.computableInPolyTime_negate encNat
  have vars := (CNF.computableInPolyTime_vars name).comp ((CNF.isPolyTime_to3CNF encNat).comp hd)
  have hsingle : ComputableInPolyTime (fun v : ℕ × ℕ => [v]) e (encList e) :=
    (cons e).comp (id'.prod (const []))
  have hget := sumElim (const (encIn := encNat) (encOut := encList e) []) hsingle
  exact flatMapWithInput vars (hget.comp (snd (encCNFOver encNat) name))

private def finiteWidthThree (d : DNF ℕ) : QBF (ℕ ⊕ (ℕ × ℕ)) :=
  QBF.alls ((freshVariables d).map Sum.inr) (QBF.ofCNF d.negate.to3CNF).not

private theorem updates_map_agree {V : Type} [DecidableEq V] (names : List V)
    (σ τ : V → Bool) (v : V) (h : v ∈ names) :
    QBF.updates σ names (names.map τ) v = τ v := by
  induction names generalizing σ with
  | nil => simp at h
  | cons w ws ih =>
    simp only [List.map_cons, QBF.updates]
    by_cases hm : v ∈ ws
    · exact ih _ hm
    · have eq : v = w := (List.mem_cons.mp h).resolve_right hm
      subst w
      rw [QBF.updates_of_notMem hm, Function.update_self]

private theorem finiteWidthThree_eval (d : DNF ℕ) (σ : ℕ → Bool) :
    (finiteWidthThree d).eval (Sum.elim σ (fun _ => false)) = true ↔ d.eval σ = true := by
  let names := (freshVariables d).map (Sum.inr (α := ℕ))
  let φ := d.negate.to3CNF
  let base : ℕ ⊕ (ℕ × ℕ) → Bool := Sum.elim σ (fun _ => false)
  change (QBF.alls names (QBF.ofCNF φ).not).eval base = true ↔ _
  rw [QBF.eval_alls_iff_word, ← widthThree_eval d σ]
  have old (w : List Bool) (v : ℕ) : QBF.updates base names w (.inl v) = σ v := by
    rw [QBF.updates_of_notMem (by simp [names])]
    rfl
  constructor
  · intro h τ
    let assign : ℕ ⊕ (ℕ × ℕ) → Bool := Sum.elim σ τ
    have hh := h (names.map assign) (by simp)
    have he : φ.eval (QBF.updates base names (names.map assign)) = φ.eval assign := by
      refine CNF.eval_congr fun v hv => ?_
      cases v with
      | inl v => exact old _ v
      | inr v =>
        apply updates_map_agree
        exact List.mem_map.mpr ⟨v, (freshVariables_mem d v).mpr hv, rfl⟩
    simpa [QBF.eval_not, QBF.eval_ofCNF, widthThree, ← he, assign, φ] using hh
  · intro h w _
    let τ (v : ℕ × ℕ) := QBF.updates base names w (.inr v)
    have he : Sum.elim σ τ = QBF.updates base names w := by
      funext v
      cases v with
      | inl v => exact (old w v).symm
      | inr v => rfl
    have hh := h τ
    rw [he] at hh
    simpa [QBF.eval_not, QBF.eval_ofCNF, widthThree, φ] using hh

/-- The finite auxiliary prefix and numbered width-three matrix, in the natural-number format
used by Frontier's prenex encoding. Old variables occupy the even names. -/
private def numberedWidthThree (d : DNF ℕ) : List ℕ × DNF ℕ :=
  ((freshVariables d).map (splitVarToNat ∘ Sum.inr),
    CNF.negate (toThreeSAT (DNF.negate d)))

private theorem polytime_numberedWidthThree : ComputableInPolyTime numberedWidthThree
    (encCNFOver encNat) (encPair (encList encNat) (encCNFOver encNat)) := by
  let e := encPair encUnary encUnary
  have dneg : ComputableInPolyTime (DNF.negate (V := ℕ))
      (encCNFOver encNat) (encCNFOver encNat) := DNF.computableInPolyTime_negate encNat
  have named : ComputableInPolyTime (toThreeSAT ∘ DNF.negate)
      (encCNFOver encNat) (encCNFOver encNat) :=
    computableInPolyTime_toThreeSAT.comp dneg
  have aux := (map (computableInPolyTime_splitVarToNat.comp (sumInr encNat e))).comp
    polytime_freshVariables
  exact aux.prod ((CNF.computableInPolyTime_negate encNat).comp named)

private theorem updates_numbered {V : Type} [DecidableEq V] (f : V → ℕ)
    (injective : Function.Injective f) (names : List V) (w : List Bool) (σ : ℕ → Bool) :
    QBF.updates σ (names.map f) w ∘ f = QBF.updates (σ ∘ f) names w := by
  induction names generalizing w σ with
  | nil => cases w <;> rfl
  | cons v vs ih =>
    cases w with
    | nil => rfl
    | cons b w =>
      simp only [List.map_cons, QBF.updates]
      rw [ih]
      congr 1
      funext u
      by_cases h : u = v
      · subst u
        simp
      · have ne : f u ≠ f v := fun e => h (injective e)
        simp [Function.comp_apply, Function.update_of_ne h, Function.update_of_ne ne]

private theorem numberedWidthThree_eval (d : DNF ℕ) (σ : ℕ → Bool) :
    (QBF.alls (numberedWidthThree d).1 (matrix (numberedWidthThree d).2)).eval σ =
      true ↔
      d.eval (fun n => σ (2 * n)) = true := by
  have compare : (QBF.alls (numberedWidthThree d).1 (matrix (numberedWidthThree d).2)).eval σ =
      true ↔
      (finiteWidthThree d).eval (σ ∘ splitVarToNat) = true := by
    simp only [numberedWidthThree, toThreeSAT, finiteWidthThree, QBF.eval_alls_iff_word,
      List.length_map]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    simp only [eval_matrix, CNF.eval_negate, QBF.eval_not, QBF.eval_ofCNF, CNF.eval_relabel]
    rw [← List.map_map, updates_numbered _ splitVarToNat_injective]
  rw [compare]
  have h := finiteWidthThree_eval d (fun n => σ (2 * n))
  rw [← h]
  have agreement (v : ℕ ⊕ (ℕ × ℕ)) (hv : v ∈ (finiteWidthThree d).freeVars) :
      (σ ∘ splitVarToNat) v = (Sum.elim (fun n => σ (2 * n)) (fun _ => false)) v := by
    cases v with
    | inl v => rfl
    | inr v =>
      simp only [finiteWidthThree, QBF.freeVars_alls, QBF.freeVars_not, Finset.mem_sdiff,
        QBF.mem_freeVars_ofCNF, List.mem_toFinset, List.mem_map] at hv
      exact (hv.2 ⟨v, (freshVariables_mem d v).mpr hv.1, rfl⟩).elim
  rw [QBF.eval_congr agreement]

private theorem eval_blocks_map {q : Bool} (bs : List (List ℕ)) (φ ψ : QBF ℕ)
    (h : ∀ σ, φ.eval σ = true ↔ ψ.eval (σ ∘ (2 * ·)) = true)
    (σ : ℕ → Bool) :
    (QBF.blocks q (bs.map (List.map (2 * ·))) φ).eval σ = true ↔
      (QBF.blocks q bs ψ).eval (σ ∘ (2 * ·)) = true := by
  have injective : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b he
    dsimp at he
    omega
  rw [QBF.eval_blocks_eq_true_iff, QBF.eval_blocks_eq_true_iff]
  have lengths : (bs.map (List.map (2 * ·))).map List.length = bs.map List.length := by
    simp [List.map_map, Function.comp_def]
  rw [lengths]
  apply alternation_congr
  intro word
  rw [h]
  have flatten : (bs.map (List.map (2 * ·))).flatten = bs.flatten.map (2 * ·) := by
    clear lengths
    induction bs with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.flatten_cons, List.map_append, ih]
  rw [flatten, updates_numbered _ injective]

/-- For any starting polarity and any nonempty prefix ending universally, the width-three
conversion appends its fresh variables to the existing last block and preserves truth. -/
private theorem widthThree_blocks_eval (q : Bool) (bs : List (List ℕ)) (d : DNF ℕ)
    (hb : bs ≠ []) (hLast : (Bool.not)^[bs.length] q = true) (σ : ℕ → Bool) :
    (QBF.blocks q (QBF.appendLast (bs.map (List.map (2 * ·))) (numberedWidthThree d).1)
      (matrix (numberedWidthThree d).2)).eval σ = true ↔
      (QBF.blocks q bs (matrix d)).eval (σ ∘ (2 * ·)) = true := by
  rw [QBF.blocks_appendLast q false (by simpa using hb) (by simpa using hLast)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact eval_blocks_map bs _ _ (fun τ => by
    rw [numberedWidthThree_eval, eval_matrix]
    rfl) σ

private theorem eval_exists_dual (names : List ℕ) (d : DNF ℕ) (σ : ℕ → Bool) :
    (QBF.exs names (QBF.ofCNF d.negate)).eval σ = true ↔
      ¬ (QBF.alls names (matrix d)).eval σ = true := by
  simp only [QBF.eval_exs_iff_word, QBF.eval_alls_iff_word, not_forall,
    QBF.eval_ofCNF, eval_matrix, DNF.eval_negate, Bool.not_eq_true', Bool.not_eq_true, exists_prop]

/-- For any starting polarity and any nonempty prefix ending existentially, the dual
construction appends its 3CNF chain variables to the existing last block. -/
private theorem widthThreeCNF_blocks_eval (q : Bool) (bs : List (List ℕ)) (c : CNF ℕ)
    (hb : bs ≠ []) (hLast : (Bool.not)^[bs.length] q = false) (σ : ℕ → Bool) :
    let converted := numberedWidthThree c.negate
    (QBF.blocks q (QBF.appendLast (bs.map (List.map (2 * ·))) converted.1)
      (QBF.ofCNF converted.2.negate)).eval σ = true ↔
      (QBF.blocks q bs (QBF.ofCNF c)).eval (σ ∘ (2 * ·)) = true := by
  dsimp only
  rw [QBF.blocks_appendLast q true (by simpa using hb) (by simpa using hLast)]
  simp only [↓reduceIte]
  refine eval_blocks_map bs _ _ (fun τ => ?_) σ
  rw [eval_exists_dual, numberedWidthThree_eval]
  simp [CNF.eval_negate, QBF.eval_ofCNF, Function.comp_def]

private theorem numbered_width (d : DNF ℕ) (t : Term ℕ) (ht : t ∈ (numberedWidthThree d).2) :
    t.length ≤ 3 := by
  obtain ⟨cl, hc, rfl⟩ := List.mem_map.mp ht
  rw [toThreeSAT] at hc
  obtain ⟨c, hcl, rfl⟩ := List.mem_map.mp hc
  rw [Clause.length_negate]
  exact (List.length_map ..).trans_le (CNF.length_le_three_of_mem_to3CNF hcl)

private theorem width_mem_P : {i : Instance | ∀ t ∈ i.matrix, t.length ≤ 3} ∈ P encoding := by
  let literal := encPair encNat encBool
  have test := unary_le' (length_list literal) (const 3)
  have check := allWithInput (test := fun (_ : Instance) (c : Term ℕ) => decide (c.length ≤ 3))
    (encoding_matrix_polyTime id')
    (test.comp (snd encoding (encList literal)))
  refine ⟨_, check, fun i => ?_⟩
  simp

/-- Width restriction of the last-polarity normal form for existential-first formulas. -/
@[expose] def SigmaWidthThree (i : ℕ) : Set Instance :=
  {p | prenexAt (!(Bool.not^[i] true)) p ∈ PrenexQBF.SigmaSAT i} ∩
    {p | ∀ t ∈ p.matrix, t.length ≤ 3}

private instance (p : Instance) : Decidable (∀ t ∈ p.matrix, t.length ≤ 3) :=
  decidable_of_iff (p.matrix.all (fun t => decide (t.length ≤ 3)) = true) (by simp)

/-- Membership is decidable by testing both the quantified formula and the matrix width. -/
instance (i : ℕ) : DecidablePred (fun p => p ∈ SigmaWidthThree i) := fun p =>
  let q := prenexAt (!(Bool.not^[i] true)) p
  inferInstanceAs (Decidable ((q.WellFormed i ∧ (q.formula true).eval (fun _ => false) = true) ∧
    ∀ t ∈ p.matrix, t.length ≤ 3))

private def compileDNF (p : Instance) : Instance :=
  let d := numberedWidthThree p.matrix
  ⟨QBF.appendLast (p.blocks.map (List.map (2 * ·))) d.1, d.2⟩

private theorem polytime_compileDNF :
    ComputableInPolyTime compileDNF encoding encoding := by
  let e := encList encNat
  have rename : ComputableInPolyTime (fun n : ℕ => 2 * n) encNat encNat :=
    binary_mul.comp ((const 2).prod id')
  have blocks := (map (map rename)).comp (encoding_blocks_polyTime id')
  have conv := polytime_numberedWidthThree.comp (encoding_matrix_polyTime id')
  have aux := conv.fst'
  unfold compileDNF
  simp only [QBF.appendLast_eq_reverse]
  have hrev := (listReverse e).comp blocks
  exact encoding_mk_polyTime ((listReverse e).comp ((cons e).comp
    (((listAppend encNat).comp (((headD []).comp hrev).prod aux)).prod
      ((tail (encA := e)).comp hrev)))) conv.snd'

private theorem compileDNF_wellFormed (p : Instance) {i : ℕ} (hi : 1 ≤ i)
    (hp : (prenexAt false p).WellFormed i) : (prenexAt false (compileDNF p)).WellFormed i := by
  have hne : p.blocks.map (List.map (2 * ·)) ≠ [] := by
    have hl : p.blocks.length = i := hp.1
    intro h
    have := congrArg List.length h
    simp [hl] at this
    omega
  have hlen : p.blocks.length = i := hp.1
  refine ⟨(QBF.length_appendLast hne _).trans (by simp only [List.length_map, hlen]),
    QBF.quantifierFree_not.mpr (QBF.quantifierFree_ofCNF _), ?_⟩
  intro v hv
  change v ∈ (matrix (numberedWidthThree p.matrix).2).freeVars at hv
  simp only [matrix, numberedWidthThree, toThreeSAT, QBF.freeVars_not, CNF.negate_negate,
    QBF.mem_freeVars_ofCNF, CNF.vars_relabel, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  change splitVarToNat u ∈
    (QBF.appendLast (p.blocks.map (List.map (2 * ·)))
      (numberedWidthThree p.matrix).1).flatten.toFinset
  rw [QBF.flatten_appendLast]
  simp only [List.mem_toFinset, List.mem_append]
  cases u with
  | inl n =>
    left
    have hm := hp.2.2 (show n ∈ (matrix p.matrix).freeVars by
      simpa only [matrix, QBF.freeVars_not, QBF.mem_freeVars_ofCNF] using
        CNF.mem_vars_of_inl_mem_vars_to3CNF p.matrix.negate n hu)
    obtain ⟨b, hb, hn⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hm)
    exact List.mem_flatten.mpr ⟨b.map (2 * ·), List.mem_map.mpr ⟨b, hb, rfl⟩,
      List.mem_map.mpr ⟨n, hn, rfl⟩⟩
  | inr n => exact Or.inr (List.mem_map.mpr ⟨n, (freshVariables_mem p.matrix n).mpr hu, rfl⟩)

private def compileWidthThree (r : Bool) (p : Instance) : Instance :=
  orientMatrix r (compileDNF (orientMatrix r p))

private theorem polytime_compileWidthThree (r : Bool) :
    ComputableInPolyTime (compileWidthThree r) encoding encoding :=
  (polytime_orientMatrix r).comp (polytime_compileDNF.comp (polytime_orientMatrix r))

private theorem compileWidthThree_wellFormed (r : Bool) (p : Instance) {i : ℕ} (hi : 1 ≤ i)
    (hp : (prenexAt false p).WellFormed i) :
    (prenexAt false (compileWidthThree r p)).WellFormed i :=
  (orientMatrix_wf r _ i).mpr (compileDNF_wellFormed _ hi ((orientMatrix_wf r _ i).mpr hp))

private theorem negateMatrix_width (p : Instance) :
    (∀ t ∈ (negateMatrix p).matrix, t.length ≤ 3) ↔ ∀ t ∈ p.matrix, t.length ≤ 3 := by
  simp [negateMatrix, DNF.negate]

private theorem compileWidthThree_width (r : Bool) (p : Instance) :
    ∀ t ∈ (compileWidthThree r p).matrix, t.length ≤ 3 := by
  have h : ∀ t ∈ (compileDNF (orientMatrix r p)).matrix, t.length ≤ 3 :=
    fun t ht => numbered_width _ t ht
  cases r
  · exact h
  · exact (negateMatrix_width _).mpr h

private theorem compileWidthThree_eval (q r : Bool) (p : Instance) (h : p.blocks ≠ [])
    (hr : (Bool.not)^[p.blocks.length] q = !r) :
    ((prenexAt r (compileWidthThree r p)).formula q).eval (fun _ => false) = true ↔
      ((prenexAt r p).formula q).eval (fun _ => false) = true := by
  cases r with
  | false => exact widthThree_blocks_eval q p.blocks p.matrix h hr _
  | true =>
    have hc := widthThreeCNF_blocks_eval q p.blocks p.matrix h hr (fun _ => false)
    have hz : ((fun _ : ℕ => false) ∘ (2 * ·)) = (fun _ => false) := rfl
    simpa only [compileWidthThree, compileDNF, orientMatrix, negateMatrix, prenexAt,
      PrenexQBF.formula, hz, ↓reduceIte,
      show CNF.negate p.matrix = DNF.negate p.matrix from rfl] using hc

private theorem sigmaWidthThree_hard_valid {α : Type} (enc : α ↪ List Bool)
    (A : Set α) {i : ℕ} (hi : 1 ≤ i) (hA : A ∈ SigmaP i enc) :
    ∃ f : α → Instance, ComputableInPolyTime f enc encoding ∧
      (∀ a, (prenexAt false (f a)).WellFormed i ∧ ∀ t ∈ (f a).matrix, t.length ≤ 3) ∧
      ∀ a, a ∈ A ↔ f a ∈ SigmaWidthThree i := by
  obtain ⟨f, hf, hw, hc⟩ := exists_normalFormReduction hi hA
  let r := !(Bool.not^[i] true)
  refine ⟨compileWidthThree r ∘ f, (polytime_compileWidthThree r).comp hf, fun a => ?_, fun a => ?_⟩
  · exact ⟨compileWidthThree_wellFormed r _ hi (hw a).1, compileWidthThree_width r _⟩
  · have valid := compileWidthThree_wellFormed r _ hi (hw a).1
    have length : (f a).blocks.length = i := (hw a).1.1
    have nonempty : (f a).blocks ≠ [] := by
      intro e
      rw [e, List.length_nil] at length
      omega
    have truth := compileWidthThree_eval true (!(Bool.not^[i] true))
      (f a) nonempty (by rw [length, Bool.not_not])
    have short : ∀ t ∈ (compileWidthThree r (f a)).2, t.length ≤ 3 :=
      compileWidthThree_width r _
    change _ ↔ (((prenexAt _ (compileWidthThree r (f a))).WellFormed i ∧
      ((prenexAt _ (compileWidthThree r (f a))).formula true).eval (fun _ => false) = true) ∧
      ∀ t ∈ (compileWidthThree r (f a)).2, t.length ≤ 3)
    rw [and_iff_left short, and_iff_right ((prenexAt_wf_iff _ _ _).mpr valid), truth]
    exact hc a

/-- All positive existential-first levels are complete with width-three matrices. Odd
levels use a 3CNF and even levels a 3DNF, as determined by the last block's polarity. -/
theorem sigmaWidthThree_complete {i : ℕ} (hi : 1 ≤ i) :
    SigmaPComplete i encoding (SigmaWidthThree i) := by
  have red : PolyTimeReducible encoding encPrenexQBF
      {p | prenexAt (!(Bool.not^[i] true)) p ∈ PrenexQBF.SigmaSAT i}
      (PrenexQBF.SigmaSAT i) :=
    ⟨_, polytime_prenexAt _, fun _ => Iff.rfl⟩
  have hw : {p : Instance | ∀ t ∈ p.matrix, t.length ≤ 3} ∈ SigmaP 0 encoding := by
    rw [SigmaP_zero]
    exact width_mem_P
  refine ⟨inter_mem_SigmaP (red.mem_SigmaP (PrenexQBF.mem_SigmaP i))
    (SigmaP_mono (Nat.zero_le _) hw), ?_⟩
  intro α enc A hA
  obtain ⟨f, hf, _, hc⟩ := sigmaWidthThree_hard_valid enc A hi hA
  exact ⟨f, hf, hc⟩

/-- Universal-first width-three formulas use the complementary matrix polarity. -/
@[expose] def PiWidthThree (i : ℕ) : Set Instance :=
  {p | prenexAt (Bool.not^[i] true) p ∈ PrenexQBF.PiSAT i} ∩
    {p | ∀ t ∈ p.matrix, t.length ≤ 3}

/-- Membership is decidable by testing both the quantified formula and the matrix width. -/
instance (i : ℕ) : DecidablePred (fun p => p ∈ PiWidthThree i) := fun p =>
  let q := prenexAt (Bool.not^[i] true) p
  inferInstanceAs (Decidable ((q.WellFormed i ∧ (q.formula false).eval (fun _ => false) = true) ∧
    ∀ t ∈ p.matrix, t.length ≤ 3))

private theorem dual_starts (r : Bool) (p : Instance) :
    ((prenexAt (!r) (negateMatrix p)).formula false).eval (fun _ => false) = true ↔
      ¬ ((prenexAt r p).formula true).eval (fun _ => false) = true := by
  rw [PrenexQBF.formula, PrenexQBF.formula, QBF.eval_blocks_eq_true_iff,
    QBF.eval_blocks_eq_true_iff, not_alternation]
  apply alternation_congr
  intro word
  cases r <;> simp [prenexAt, negateMatrix, matrix, QBF.eval_not,
    show DNF.negate p.matrix = CNF.negate p.matrix from rfl]

/-- At each positive universal-first level, odd levels use 3DNF and even levels
use 3CNF. The reduction always emits well-formed instances, including on no inputs. -/
theorem piWidthThree_complete {i : ℕ} (hi : 1 ≤ i) :
    PiPComplete i encoding (PiWidthThree i) := by
  have red : PolyTimeReducible encoding encPrenexQBF
      {p | prenexAt (Bool.not^[i] true) p ∈ PrenexQBF.PiSAT i}
      (PrenexQBF.PiSAT i) :=
    ⟨_, polytime_prenexAt _, fun _ => Iff.rfl⟩
  have hw : {p : Instance | ∀ t ∈ p.matrix, t.length ≤ 3} ∈ PiP 0 encoding := by
    rw [PiP_zero]
    exact width_mem_P
  refine ⟨inter_mem_PiP (red.mem_PiP (PrenexQBF.mem_PiP i))
    (PiP_mono (Nat.zero_le _) hw), ?_⟩
  intro α enc A hA
  obtain ⟨f, hf, hvalid, hc⟩ := sigmaWidthThree_hard_valid enc Aᶜ hi
    (compl_mem_SigmaP_of_mem_PiP hA)
  refine ⟨negateMatrix ∘ f, polytime_negateMatrix.comp hf, fun a => ?_⟩
  obtain ⟨hwell, hwidth⟩ := hvalid a
  have eq := hc a
  change a ∉ A ↔ (((prenexAt _ (f a)).WellFormed i ∧
    ((prenexAt (!(Bool.not^[i] true)) (f a)).formula true).eval (fun _ => false) = true) ∧
    ∀ t ∈ (f a).matrix, t.length ≤ 3) at eq
  change a ∈ A ↔ (((prenexAt _ (negateMatrix (f a))).WellFormed i ∧
    ((prenexAt (Bool.not^[i] true) (negateMatrix (f a))).formula false).eval
      (fun _ => false) = true) ∧ ∀ t ∈ (negateMatrix (f a)).matrix, t.length ≤ 3)
  have wellDual : (prenexAt false (negateMatrix (f a))).WellFormed i :=
    (orientMatrix_wf true _ _).mpr hwell
  rw [and_iff_left hwidth, and_iff_right ((prenexAt_wf_iff _ _ _).mpr hwell)] at eq
  rw [and_iff_left ((negateMatrix_width _).mpr hwidth),
    and_iff_right ((prenexAt_wf_iff _ _ _).mpr wellDual)]
  have dual := dual_starts (!(Bool.not^[i] true)) (f a)
  rw [Bool.not_not] at dual
  rw [dual, ← eq, not_not]

end Cslib.Complexity.QuantifiedSAT.WidthThree
