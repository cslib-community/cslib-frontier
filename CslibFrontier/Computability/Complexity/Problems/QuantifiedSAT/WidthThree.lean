/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.TableauDNF
public import CslibFrontier.Logics.Propositional.CNF.ThreeCNF.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Complexity.Classes.PH.Closure

/-!
# Width-three existential-universal quantified DNF

Apply the dual of the existing 3CNF splitting transformation under a fixed
assignment to the original variables. Append the fresh variables to the
universal block and preserve the truth and well-formedness of the input.
-/

@[expose] public section

namespace Cslib.Complexity.QuantifiedSAT.WidthThree

open Cslib.Logic.PL Cslib.Complexity _root_.Turing.MultiTapeTM ComputableInPolyTime

def widthThree (d : DNF Nat) : DNF (Nat ⊕ (Nat × Nat)) :=
  d.negate.to3CNF.negate

theorem widthThree_terms (d : DNF Nat) (t : Term (Nat ⊕ (Nat × Nat)))
    (ht : t ∈ widthThree d) : t.length ≤ 3 := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
  rw [Clause.length_negate]
  exact CNF.length_le_three_of_mem_to3CNF hc

/-- A 3DNF matrix preserves truth with the original assignment fixed and all fresh chain
variables universally quantified. The extension lemma keeps the original variable values. -/
theorem widthThree_eval (d : DNF Nat) (σ : Nat → Bool) :
    (∀ τ : Nat × Nat → Bool, (widthThree d).eval (Sum.elim σ τ) = true) ↔
      d.eval σ = true := by
  constructor
  · intro h
    cases hd : d.eval σ with
    | true => rfl
    | false =>
      have hcnf : d.negate.eval σ = true := by simp [hd]
      let τ (i : Nat × Nat) := d.negate.to3CNFAssignment σ (.inr i)
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

theorem polytime_widthThree : ComputableInPolyTime widthThree (encCNFOver encNat)
    (encCNFOver (encSum encNat (encPair encUnary encUnary))) := by
  have h : ComputableInPolyTime (DNF.negate (V := Nat))
      (encCNFOver encNat) (encCNFOver encNat) := by
    change ComputableInPolyTime (List.map (List.map Std.Sat.Literal.negate)) _ _
    exact map (map (Literal.computableInPolyTime_negate encNat))
  exact (polytime_negateCNF _).comp ((CNF.isPolyTime_to3CNF encNat).comp h)

/-- Fresh names in occurrence order. Repeated occurrences are harmless because the same
assignment bit is copied for each occurrence when witnessing a particular assignment. -/
def freshVariables (d : DNF Nat) : List (Nat × Nat) :=
  d.negate.to3CNF.vars.flatMap (Sum.elim (fun _ => []) fun v => [v])

theorem freshVariables_mem (d : DNF Nat) (v : Nat × Nat) :
    v ∈ freshVariables d ↔ Sum.inr v ∈ d.negate.to3CNF.vars := by
  constructor
  · intro h
    obtain ⟨w, hw, hv⟩ := List.mem_flatMap.mp h
    cases w with
    | inl w => simp at hv
    | inr w => simpa using (List.mem_singleton.mp hv) ▸ hw
  · intro h
    exact List.mem_flatMap.mpr ⟨Sum.inr v, h, by simp⟩

theorem polytime_freshVariables : ComputableInPolyTime freshVariables (encCNFOver encNat)
    (encList (encPair encUnary encUnary)) := by
  let e := encPair encUnary encUnary
  let name := encSum encNat e
  have hd : ComputableInPolyTime (DNF.negate (V := Nat))
      (encCNFOver encNat) (encCNFOver encNat) := by
    change ComputableInPolyTime (List.map (List.map Std.Sat.Literal.negate)) _ _
    exact map (map (Literal.computableInPolyTime_negate encNat))
  have vars := (CNF.computableInPolyTime_vars name).comp ((CNF.isPolyTime_to3CNF encNat).comp hd)
  have hsingle : ComputableInPolyTime (fun v : Nat × Nat => [v]) e (encList e) :=
    (cons e).comp (id'.prod (const []))
  have hget := sumElim (const (encIn := encNat) (encOut := encList e) []) hsingle
  exact flatMapWithInput vars (hget.comp (snd (encCNFOver encNat) name))

def finiteWidthThree (d : DNF Nat) : QBF (Nat ⊕ (Nat × Nat)) :=
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

theorem finiteWidthThree_eval (d : DNF Nat) (σ : Nat → Bool) :
    (finiteWidthThree d).eval (Sum.elim σ (fun _ => false)) = true ↔ d.eval σ = true := by
  let names := (freshVariables d).map (Sum.inr (α := Nat))
  let φ := d.negate.to3CNF
  let base : Nat ⊕ (Nat × Nat) → Bool := Sum.elim σ (fun _ => false)
  change (QBF.alls names (QBF.ofCNF φ).not).eval base = true ↔ _
  rw [QBF.eval_alls_iff_word, ← widthThree_eval d σ]
  have old (w : List Bool) (v : Nat) : QBF.updates base names w (.inl v) = σ v := by
    rw [QBF.updates_of_notMem (by simp [names])]
    rfl
  constructor
  · intro h τ
    let assign : Nat ⊕ (Nat × Nat) → Bool := Sum.elim σ τ
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
    let τ (v : Nat × Nat) := QBF.updates base names w (.inr v)
    have he : Sum.elim σ τ = QBF.updates base names w := by
      funext v
      cases v with
      | inl v => exact (old w v).symm
      | inr v => rfl
    have hh := h τ
    rw [he] at hh
    simpa [QBF.eval_not, QBF.eval_ofCNF, widthThree, φ] using hh

def widthThreeName : Nat ⊕ (Nat × Nat) → Nat :=
  Sum.elim (fun n => 2 * n) fun p => 2 * Nat.pair p.1 p.2 + 1

theorem widthThreeName_injective : Function.Injective widthThreeName := by
  rintro (a | ⟨a₁, a₂⟩) (b | ⟨b₁, b₂⟩) h <;>
    simp only [widthThreeName, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (by omega)
  · omega
  · omega
  · have hp : Nat.pair a₁ a₂ = Nat.pair b₁ b₂ := by omega
    exact congrArg Sum.inr ((Nat.unpair_pair a₁ a₂).symm.trans
      ((congrArg Nat.unpair hp).trans (Nat.unpair_pair b₁ b₂)))

theorem polytime_widthThreeName : ComputableInPolyTime widthThreeName
    (encSum encNat (encPair encUnary encUnary)) encNat := by
  have twice : ComputableInPolyTime (fun n : Nat => 2 * n) encNat encNat :=
    binary_mul.comp ((const 2).prod id')
  have pair := unary_to_binary.comp unary_pair
  have right := binary_add' (twice.comp pair) (const 1)
  exact sumElim twice right

/-- The finite auxiliary prefix and numbered width-three matrix, in the natural-number format
used by Frontier's prenex encoding. Old variables occupy the even names. -/
def numberedWidthThree (d : DNF Nat) : List Nat × DNF Nat :=
  ((freshVariables d).map (widthThreeName ∘ Sum.inr),
    (d.negate.to3CNF.relabel widthThreeName).negate)

theorem polytime_numberedWidthThree : ComputableInPolyTime numberedWidthThree
    (encCNFOver encNat) (encPair (encList encNat) (encCNFOver encNat)) := by
  let e := encPair encUnary encUnary
  have dneg : ComputableInPolyTime (DNF.negate (V := Nat))
      (encCNFOver encNat) (encCNFOver encNat) := by
    change ComputableInPolyTime (List.map (List.map Std.Sat.Literal.negate)) _ _
    exact map (map (Literal.computableInPolyTime_negate encNat))
  have named := (CNF.computableInPolyTime_relabel polytime_widthThreeName).comp
    ((CNF.isPolyTime_to3CNF encNat).comp dneg)
  have aux := (map (polytime_widthThreeName.comp (sumInr encNat e))).comp
    polytime_freshVariables
  exact aux.prod ((polytime_negateCNF encNat).comp named)

private theorem updates_numbered {V : Type} [DecidableEq V] (f : V → Nat)
    (injective : Function.Injective f) (names : List V) (w : List Bool) (σ : Nat → Bool) :
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

theorem numberedWidthThree_eval (d : DNF Nat) (σ : Nat → Bool) :
    (QBF.alls (numberedWidthThree d).1 (matrix (numberedWidthThree d).2)).eval σ =
      true ↔
      d.eval (fun n => σ (2 * n)) = true := by
  have compare : (QBF.alls (numberedWidthThree d).1 (matrix (numberedWidthThree d).2)).eval σ =
      true ↔
      (finiteWidthThree d).eval (σ ∘ widthThreeName) = true := by
    simp only [numberedWidthThree, finiteWidthThree, QBF.eval_alls_iff_word, List.length_map]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    simp only [eval_matrix, CNF.eval_negate, QBF.eval_not, QBF.eval_ofCNF, CNF.eval_relabel]
    rw [← List.map_map, updates_numbered _ widthThreeName_injective]
  rw [compare]
  have h := finiteWidthThree_eval d (fun n => σ (2 * n))
  rw [← h]
  have agreement (v : Nat ⊕ (Nat × Nat)) (hv : v ∈ (finiteWidthThree d).freeVars) :
      (σ ∘ widthThreeName) v = (Sum.elim (fun n => σ (2 * n)) (fun _ => false)) v := by
    cases v with
    | inl v => rfl
    | inr v =>
      simp only [finiteWidthThree, QBF.freeVars_alls, QBF.freeVars_not, Finset.mem_sdiff,
        QBF.mem_freeVars_ofCNF, List.mem_toFinset, List.mem_map] at hv
      exact (hv.2 ⟨v, (freshVariables_mem d v).mpr hv.1, rfl⟩).elim
  rw [QBF.eval_congr agreement]

private theorem eval_blocks_map {q : Bool} (bs : List (List Nat)) (φ ψ : QBF Nat)
    (h : ∀ σ, φ.eval σ = true ↔ ψ.eval (σ ∘ (2 * ·)) = true)
    (σ : Nat → Bool) :
    (QBF.blocks q (bs.map (List.map (2 * ·))) φ).eval σ = true ↔
      (QBF.blocks q bs ψ).eval (σ ∘ (2 * ·)) = true := by
  have injective : Function.Injective (fun n : Nat => 2 * n) := by
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
theorem widthThree_blocks_eval (q : Bool) (bs : List (List Nat)) (d : DNF Nat)
    (hb : bs ≠ []) (hLast : (Bool.not)^[bs.length] q = true) (σ : Nat → Bool) :
    (QBF.blocks q (QBF.appendLast (bs.map (List.map (2 * ·))) (numberedWidthThree d).1)
      (matrix (numberedWidthThree d).2)).eval σ = true ↔
      (QBF.blocks q bs (matrix d)).eval (σ ∘ (2 * ·)) = true := by
  rw [QBF.blocks_appendLast q false (by simpa using hb) (by simpa using hLast)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact eval_blocks_map bs _ _ (fun τ => by
    rw [numberedWidthThree_eval, eval_matrix]
    rfl) σ

private theorem eval_exists_dual (names : List Nat) (d : DNF Nat) (σ : Nat → Bool) :
    (QBF.exs names (QBF.ofCNF d.negate)).eval σ = true ↔
      ¬ (QBF.alls names (matrix d)).eval σ = true := by
  simp only [QBF.eval_exs_iff_word, QBF.eval_alls_iff_word, not_forall,
    QBF.eval_ofCNF, eval_matrix, DNF.eval_negate, Bool.not_eq_true', Bool.not_eq_true, exists_prop]

/-- For any starting polarity and any nonempty prefix ending existentially, the dual
construction appends its 3CNF chain variables to the existing last block. -/
theorem widthThreeCNF_blocks_eval (q : Bool) (bs : List (List Nat)) (c : CNF Nat)
    (hb : bs ≠ []) (hLast : (Bool.not)^[bs.length] q = false) (σ : Nat → Bool) :
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

private theorem splitAux_old (fresh : Nat → Nat × Nat) (j : Nat)
    (carry : Literal (Nat ⊕ (Nat × Nat)))
    (rest : Clause (Nat ⊕ (Nat × Nat))) (v : Nat) :
    Sum.inl v ∈ (Clause.splitAux (Sum.inr ∘ fresh) j carry rest).vars →
      ∃ b, (Sum.inl v, b) ∈ carry :: rest := by
  fun_induction Clause.splitAux (Sum.inr ∘ fresh) j carry rest with
  | case1 j carry a b c rest ih =>
    rw [CNF.mem_vars]
    rintro ⟨clause, hc, sign, hm⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e | e | e
      · exact ⟨sign, List.mem_cons.mpr (Or.inl e)⟩
      · exact ⟨sign, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))⟩
      · cases e
    · obtain ⟨bit, he⟩ := ih (CNF.mem_vars.mpr ⟨clause, hc, sign, hm⟩)
      rcases List.mem_cons.mp he with h | h
      · cases h
      · exact ⟨bit, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)⟩
  | case2 j carry rest hrest =>
    simp [CNF.mem_vars]

private theorem to3CNF_old (φ : CNF Nat) (v : Nat) (hv : Sum.inl v ∈ φ.to3CNF.vars) :
    v ∈ φ.vars := by
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp hv
  obtain ⟨⟨orig, i⟩, horig, hc⟩ := List.mem_flatMap.mp hc
  have hsrc : orig ∈ φ := by
    exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp horig)
  have hsplit : ∃ sign, (Sum.inl v, sign) ∈ orig.relabel (Sum.inl (β := Nat × Nat)) := by
    cases h : orig.relabel (Sum.inl (β := Nat × Nat)) with
    | nil => simp [h, Clause.split3] at hc; subst c; simp at hb
    | cons r rs =>
      rw [h, Clause.split3] at hc
      exact splitAux_old (fun j => (i, j)) 0 r rs v (CNF.mem_vars.mpr ⟨c, hc, b, hb⟩)
  obtain ⟨sign, hsign⟩ := hsplit
  obtain ⟨lit, hl, he⟩ := List.mem_map.mp hsign
  have eq : lit.1 = v := Sum.inl.inj (congrArg Prod.fst he)
  exact CNF.mem_vars.mpr ⟨orig, hsrc, lit.2, by rwa [← eq]⟩

def compile3DNF (i : Instance) : Instance :=
  let converted := numberedWidthThree i.2
  ⟨[(i.1.getD 0 []).map (2 * ·), (i.1.getD 1 []).map (2 * ·) ++ converted.1], converted.2⟩

theorem polytime_compile3DNF : ComputableInPolyTime compile3DNF encoding encoding := by
  let b := encList encNat
  let d := encCNFOver encNat
  have blocks := fst (encList b) d
  have matrix := snd (encList b) d
  have twice : ComputableInPolyTime (fun n : Nat => 2 * n) encNat encNat :=
    binary_mul.comp ((const 2).prod id')
  have first := (map twice).comp (listGetDWithInput blocks (const (encOut := encUnary) 0) [])
  have second := (map twice).comp (listGetDWithInput blocks (const (encOut := encUnary) 1) [])
  have out := polytime_numberedWidthThree.comp matrix
  have appended := (listAppend encNat).comp (second.prod out.fst')
  have pairs := (cons b).comp (first.prod ((cons b).comp (appended.prod (const []))))
  exact (pairs.prod out.snd').of_enc_eq fun _ => rfl

private theorem numbered_width (d : DNF Nat) (t : Term Nat) (ht : t ∈ (numberedWidthThree d).2) :
    t.length ≤ 3 := by
  obtain ⟨cl, hc, rfl⟩ := List.mem_map.mp ht
  obtain ⟨c, hcl, rfl⟩ := List.mem_map.mp hc
  rw [Clause.length_negate]
  exact (List.length_map ..).trans_le (CNF.length_le_three_of_mem_to3CNF hcl)

private theorem compile3_wellFormed (a b : List Nat) (d : DNF Nat)
    (h : (prenex ([a, b], d)).WellFormed 2) : (prenex (compile3DNF ([a, b], d))).WellFormed 2 := by
  refine ⟨rfl, QBF.quantifierFree_not.mpr (QBF.quantifierFree_ofCNF _), ?_⟩
  intro v hv
  change v ∈ (matrix (numberedWidthThree d).2).freeVars at hv
  simp only [matrix, numberedWidthThree, QBF.freeVars_not, negate_twice,
    QBF.mem_freeVars_ofCNF, CNF.vars_relabel, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  have old : ∀ n ∈ d.negate.vars, n ∈ a ++ b := by
    intro n hn
    have := h.2.2 (show n ∈ (matrix d).freeVars by
      simpa only [matrix, QBF.freeVars_not, QBF.mem_freeVars_ofCNF] using hn)
    simpa [prenex] using this
  change widthThreeName u ∈
    ((a.map (2 * ·)) ++ ((b.map (2 * ·) ++ (numberedWidthThree d).1) ++ [])).toFinset
  simp only [List.append_nil, List.mem_toFinset, List.mem_append]
  cases u with
  | inl n =>
    rcases List.mem_append.mp (old n (to3CNF_old d.negate n hu)) with ha | hb
    · exact Or.inl (List.mem_map.mpr ⟨n, ha, rfl⟩)
    · exact Or.inr (Or.inl (List.mem_map.mpr ⟨n, hb, rfl⟩))
  | inr n => exact Or.inr (Or.inr (List.mem_map.mpr ⟨n, (freshVariables_mem d n).mpr hu, rfl⟩))

private theorem compile3_truth (a b : List Nat) (d : DNF Nat) :
    ((prenex (compile3DNF ([a, b], d))).formula true).eval (fun _ => false) = true ↔
      ((prenex ([a, b], d)).formula true).eval (fun _ => false) = true := by
  change (QBF.exs (a.map (2 * ·)) (QBF.alls (b.map (2 * ·) ++ (numberedWidthThree d).1)
    (matrix (numberedWidthThree d).2))).eval (fun _ => false) = true ↔
      (QBF.exs a (QBF.alls b (matrix d))).eval (fun _ => false) = true
  simp only [QBF.alls_append, QBF.eval_exs_iff_word, QBF.eval_alls_iff_word, List.length_map]
  refine exists_congr fun x => and_congr_right fun _ =>
    forall_congr' fun y => imp_congr_right fun _ => ?_
  rw [← QBF.eval_alls_iff_word, numberedWidthThree_eval, eval_matrix]
  have injective : Function.Injective (fun n : Nat => 2 * n) := by
    intro p q e
    change 2 * p = 2 * q at e
    omega
  change d.eval (QBF.updates (QBF.updates (fun _ => false) (a.map (2 * ·)) x)
    (b.map (2 * ·)) y ∘ (2 * ·)) = true ↔ _
  rw [updates_numbered _ injective, updates_numbered _ injective]
  rfl

def DNF3Two : Set Instance := DNF2 ∩ {i | ∀ t ∈ i.2, t.length ≤ 3}

private theorem width_mem_P : {i : Instance | ∀ t ∈ i.2, t.length ≤ 3} ∈ P encoding := by
  let literal := encPair encNat encBool
  have test := unary_le' (length_list literal) (const 3)
  have check := allWithInput (test := fun (_ : Instance) (c : Term Nat) => decide (c.length ≤ 3))
    (snd (encList (encList encNat)) (encCNFOver encNat))
    (test.comp (snd encoding (encList literal)))
  refine ⟨_, check, fun i => ?_⟩
  simp

theorem compile3DNF_correct (i : Instance) (hwi : (prenex i).WellFormed 2) :
    i ∈ DNF2 ↔ compile3DNF i ∈ DNF3Two := by
  obtain ⟨bs, d⟩ := i
  rcases bs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp [prenex, PrenexQBF.WellFormed] at hwi
  · simp [prenex, PrenexQBF.WellFormed] at hwi
  · have hw := compile3_wellFormed x y d hwi
    have bound : compile3DNF ([x, y], d) ∈ {i : Instance | ∀ t ∈ i.2, t.length ≤ 3} :=
      fun t ht => numbered_width d t ht
    change ((prenex ([x, y], d)).WellFormed 2 ∧ _) ↔
      (((prenex (compile3DNF ([x, y], d))).WellFormed 2 ∧ _) ∧ _)
    rw [and_iff_right hwi, and_iff_right hw, and_iff_left bound, compile3_truth]
  · simp [prenex, PrenexQBF.WellFormed] at hwi

theorem dnf3Two_complete : SigmaPComplete 2 encoding DNF3Two := by
  have width0 : {i : Instance | ∀ t ∈ i.2, t.length ≤ 3} ∈ SigmaP 0 encoding := by
    rw [SigmaP_zero]
    exact width_mem_P
  refine ⟨inter_mem_SigmaP dnf2_mem (SigmaP_mono (by decide : 0 ≤ 2) width0), ?_⟩
  intro α enc A hA
  obtain ⟨f, hf, hwf, hcorrect⟩ := dnf2_hard_wellFormed enc A hA
  exact ⟨compile3DNF ∘ f, polytime_compile3DNF.comp hf,
    fun a => (hcorrect a).trans (compile3DNF_correct (f a) (hwf a))⟩

end Cslib.Complexity.QuantifiedSAT.WidthThree
