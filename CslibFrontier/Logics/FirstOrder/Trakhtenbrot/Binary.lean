/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Graph
public import CslibFrontier.Logics.FirstOrder.Raw.Uniformize
public import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Undecidability
import CslibFrontier.Foundations.Computability.ComputablePred

/-!
# Trakhtenbrot's theorem for a fixed vocabulary with a relation of arity at least two

**Trakhtenbrot's theorem** for a fixed relational vocabulary (extending [Libkin2004], Theorem 9.2):
for every relational vocabulary `σ` containing a relation symbol of arity `l ≥ 2`, finite
satisfiability of first-order sentences over `σ` is undecidable
(`Cslib.Logic.FO.RawFormula.not_exists_computable_finSat_of_mem`). Since finite satisfiability is
r.e. (`Cslib.Logic.FO.RawFormula.rePred_finSat`), the finitely valid sentences over `σ` do not
form an r.e. set (compare [Libkin2004], Corollary 9.3;
`Cslib.Logic.FO.RawFormula.not_exists_rePred_finValid_of_mem`), so no effective proof system for
sentences over `σ` is sound and complete for finite validity
(`Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_unprovable`).

The proof reduces finite satisfiability of arbitrary raw formulas, undecidable by
`Cslib.Logic.FO.RawFormula.not_computablePred_finSat`, along the primitive recursive map
`Cslib.Logic.FO.RawFormula.singleRel s l`, whose values for `2 ≤ l` are sentences over `{(s, l)}`:

1. `uniformize` rewrites all relation symbols as the single symbol `0`, coding each symbol and
   arity in the length of a padded argument list
   (`CslibFrontier/Logics/FirstOrder/Raw/Uniformize.lean`);
2. `toGraph` interprets the resulting structure in one binary relation by tuple gadgets
   (`CslibFrontier/Logics/FirstOrder/Raw/Graph.lean`);
3. the existential closure turns the result into a sentence
   (`CslibFrontier/Logics/FirstOrder/Raw/Sentence.lean`), and `rename [s]` moves the binary symbol
   `0` to `s`;
4. `padArgs l` pads each binary atom `R_s(x, y)` to arity `l` as `R_s(x, y, …, y)`.

[Libkin2004], Theorem 9.2 and Corollary 9.3, state the binary case `l = 2`; step 4 extends it to
every arity `l ≥ 2`. Each step preserves finite satisfiability
(`Cslib.Logic.FO.RawFormula.finSat_singleRel`).

**Relation to `not_computablePred_finSat`.** `Cslib.Logic.FO.RawFormula.not_computablePred_finSat`
rules out a decision procedure that is correct on all raw formulas. The theorems here only ask the
procedure to be correct on sentences over `σ`, a set that may contain a single relation symbol of
arity `l ≥ 2`, so they are strictly stronger statements.

**Scope.** The sentences are library-local `Cslib.Logic.FO.RawFormula`s, with equality and
relation symbols named by natural numbers; a vocabulary is a set of pairs (symbol, arity). The
same theorems for Mathlib's `L.Sentence`, over a finite relational language with a relation symbol
of arity at least `2`, are in `CslibFrontier/Logics/FirstOrder/Trakhtenbrot/Sentence.lean`.

## Main definitions

* `Cslib.Logic.FO.RawFormula.padArgs`: pad binary atoms `R(x, y)` to `R(x, y, …, y)` of arity `l`.
* `Cslib.Logic.FO.RawFormula.singleRel`: the reduction to a single relation symbol `s` of arity `l`.

## Main results

* `Cslib.Logic.FO.RawFormula.finSat_padArgs`, `Cslib.Logic.FO.RawFormula.isSentenceOver_padArgs`,
  `Cslib.Logic.FO.RawFormula.primrec₂_padArgs`: argument padding from arity `2` to arity `l ≥ 2`.
* `Cslib.Logic.FO.RawFormula.finSat_singleRel`,
  `Cslib.Logic.FO.RawFormula.isSentenceOver_singleRel`,
  `Cslib.Logic.FO.RawFormula.primrec_singleRel`: the reduction.
* `Cslib.Logic.FO.RawFormula.not_exists_computable_finSat_of_mem`: **Trakhtenbrot's theorem** for a
  vocabulary containing a relation symbol of arity at least `2`.
* `Cslib.Logic.FO.RawFormula.not_exists_rePred_finValid_of_mem`: finite validity of sentences over
  such a vocabulary is not r.e.
* `Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_not_of_rePred`,
  `Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_unprovable`: no sound and complete
  proof system for finite validity of sentences over such a vocabulary.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-! ### Padding binary atoms to arity `l ≥ 2` -/

/-- Pad every binary atom `rel r [x, y]` to arity `l` as
`rel r (x :: y :: List.replicate (l - 2) y)`, leaving atoms of other arities unchanged. -/
def padArgs (l : ℕ) : RawFormula → RawFormula
  | falsum => falsum
  | equal x y => equal x y
  | rel r [x, y] => rel r (x :: y :: List.replicate (l - 2) y)
  | rel r args => rel r args
  | imp φ ψ => imp (padArgs l φ) (padArgs l ψ)
  | all x φ => all x (padArgs l φ)

@[simp] theorem padArgs_falsum (l : ℕ) : padArgs l falsum = falsum := by rfl

@[simp] theorem padArgs_equal (l x y : ℕ) : padArgs l (equal x y) = equal x y := by rfl

@[simp] theorem padArgs_rel_pair (l r x y : ℕ) :
    padArgs l (rel r [x, y]) = rel r (x :: y :: List.replicate (l - 2) y) := by rfl

theorem padArgs_rel_of_length_ne (l r : ℕ) {args : List ℕ} (h : args.length ≠ 2) :
    padArgs l (rel r args) = rel r args := by
  rcases args with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp [padArgs] at h ⊢

@[simp] theorem padArgs_imp (l : ℕ) (φ ψ : RawFormula) :
    padArgs l (imp φ ψ) = imp (padArgs l φ) (padArgs l ψ) := by rfl

@[simp] theorem padArgs_all (l x : ℕ) (φ : RawFormula) :
    padArgs l (all x φ) = all x (padArgs l φ) := by rfl

@[simp] theorem padArgs_neg (l : ℕ) (φ : RawFormula) :
    padArgs l (neg φ) = neg (padArgs l φ) := by rfl

theorem mem_freeVars_padArgs (l : ℕ) :
    ∀ (φ : RawFormula) {z : ℕ}, z ∈ (padArgs l φ).freeVars ↔ z ∈ φ.freeVars
  | falsum, _ | equal _ _, _ => Iff.rfl
  | rel _ [_, _], _ => by simp only [padArgs_rel_pair, freeVars, List.mem_cons,
      List.mem_replicate, List.not_mem_nil, or_false]; tauto
  | rel _ [], _ | rel _ [_], _ | rel _ (_ :: _ :: _ :: _), _ => Iff.rfl
  | imp φ ψ, _ => by
    simp only [padArgs_imp, freeVars, List.mem_append, mem_freeVars_padArgs l φ,
      mem_freeVars_padArgs l ψ]
  | all _ φ, _ => by simp only [padArgs_all, mem_freeVars_all, mem_freeVars_padArgs l φ]

@[simp] theorem isSentence_padArgs {l : ℕ} {φ : RawFormula} :
    IsSentence (padArgs l φ) ↔ IsSentence φ := by
  simp only [IsSentence, List.eq_nil_iff_forall_not_mem, mem_freeVars_padArgs]

theorem atoms_padArgs {l : ℕ} (hl : 2 ≤ l) :
    ∀ φ : RawFormula,
      (padArgs l φ).atoms = φ.atoms.map fun (r, k) => (r, if k = 2 then l else k)
  | falsum | equal _ _ => rfl
  | rel _ [_, _] => by simp [atoms]; omega
  | rel _ [] | rel _ [_] | rel _ (_ :: _ :: _ :: _) => by simp [padArgs, atoms]
  | imp φ ψ => by simp [atoms, atoms_padArgs hl φ, atoms_padArgs hl ψ]
  | all _ φ => atoms_padArgs hl φ

theorem isSentenceOver_padArgs {s l : ℕ} (hl : 2 ≤ l) {φ : RawFormula}
    (hφ : IsSentenceOver {(s, 2)} φ) :
    IsSentenceOver {(s, l)} (padArgs l φ) := by
  refine ⟨isSentence_padArgs.2 hφ.1, fun a ha => ?_⟩
  obtain ⟨⟨r, k⟩, hb, rfl⟩ := List.mem_map.1 (atoms_padArgs hl φ ▸ ha)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hφ.2 _ hb)
  simp

/-- The binary relation interpretation induced by padding binary tuples `(a, b)` to
`a :: b :: List.replicate (l - 2) b`. -/
private def unpadInterp {M : Type*} (l : ℕ) (J : ℕ → List M → Prop) : ℕ → List M → Prop
  | r, [a, b] => J r (a :: b :: List.replicate (l - 2) b)
  | r, as => J r as

private theorem realize_padArgs {M : Type*} (l : ℕ) (J : ℕ → List M → Prop) :
    ∀ (φ : RawFormula) (v : ℕ → M),
      (padArgs l φ).Realize J v ↔ φ.Realize (unpadInterp l J) v
  | falsum, _ | equal _ _, _ => Iff.rfl
  | rel _ [_, _], _ => by simp [padArgs_rel_pair, unpadInterp]
  | rel _ [], _ | rel _ [_], _ | rel _ (_ :: _ :: _ :: _), _ => Iff.rfl
  | imp φ ψ, _ => by simp [realize_padArgs l J φ, realize_padArgs l J ψ]
  | all _ φ, _ => by simp [realize_padArgs l J φ]

/-- Padding binary atoms preserves finite satisfiability for formulas whose atoms are all
binary. -/
theorem finSat_padArgs (l : ℕ) {φ : RawFormula} (hφ : ∀ a ∈ φ.atoms, a.2 = 2) :
    FinSat (padArgs l φ) ↔ FinSat φ := by
  refine ⟨fun ⟨M, hf, hn, J, v, h⟩ => ⟨M, hf, hn, _, v, (realize_padArgs l J φ v).1 h⟩, ?_⟩
  rintro ⟨M, hf, hn, I, v, h⟩
  refine ⟨M, hf, hn, fun r as => match as with | a :: b :: _ => I r [a, b] | _ => False, v,
    (realize_padArgs l _ φ v).2 ((realize_congr_rel φ v fun r as hr => ?_).1 h)⟩
  have has : as.length = 2 := hφ _ hr
  rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at has; exact Iff.rfl

open Primrec in
theorem primrec₂_padArgs : Primrec₂ padArgs := by
  have has : Primrec fun p : ℕ × ℕ × List ℕ => p.2.2 := snd.comp snd
  have hy : Primrec fun p : ℕ × ℕ × List ℕ => p.2.2.getD 1 0 :=
    (list_getD 0).comp has (const 1)
  refine primrec₂_of_rec (α := ℕ) (σ := RawFormula) padArgs (const falsum)
    (e := fun _ p => equal p.1 p.2) (primrec_equal (fst.comp snd) (snd.comp snd)).to₂
    (r := fun l p => if p.2.length = 2 then
      rel p.1 (p.2.getD 0 0 :: p.2.getD 1 0 :: List.replicate (l - 2) (p.2.getD 1 0))
      else rel p.1 p.2)
    (Primrec.ite (Primrec.eq.comp (list_length.comp has) (const 2))
      (primrec_rel (fst.comp snd) (list_cons.comp ((list_getD 0).comp has (const 0))
        (list_cons.comp hy (primrec₂_replicate.comp (nat_sub.comp fst (const 2)) hy))))
      (primrec_rel (fst.comp snd) has)).to₂
    (i := fun _ p => imp p.2.1 p.2.2)
    (primrec_imp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun _ p => all p.1.1 p.2)
    (primrec_all (fst.comp (fst.comp snd)) (snd.comp snd)).to₂
    (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ as => by rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp [padArgs])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-! ### Reduction to a single relation symbol of arity `l ≥ 2` -/

/-- Renaming the binary symbol `0` to `s` preserves finite satisfiability. -/
private theorem finSat_rename_singleton {φ : RawFormula} (hφ : ∀ a ∈ φ.atoms, a = (0, 2)) (s : ℕ) :
    FinSat (rename [s] φ) ↔ FinSat φ :=
  ⟨fun ⟨M, hf, hn, I, v, h⟩ => ⟨M, hf, hn, _, v, (realize_rename [s] I φ v).1 h⟩,
   fun ⟨M, hf, hn, I, v, h⟩ => ⟨M, hf, hn, fun _ => I 0, v, (realize_rename [s] _ φ v).2 <|
     (realize_congr_rel φ v fun _ _ hr => (Prod.mk.inj (hφ _ hr)).1 ▸ Iff.rfl).1 h⟩⟩

/-- **The reduction to one relation symbol `s` of arity `l`** (for `2 ≤ l`): a sentence over
`{(s, l)}` that is finitely satisfiable iff `φ` is. -/
def singleRel (s l : ℕ) (φ : RawFormula) : RawFormula :=
  let ψ := uniformize φ.varBound φ
  padArgs l (rename [s] (exClosure (toGraph ψ.varBound ψ)))

private theorem atoms_rename_exClosure_toGraph (s : ℕ) (ψ : RawFormula) :
    ∀ a ∈ (rename [s] (exClosure (toGraph ψ.varBound ψ))).atoms, a = (s, 2) := fun a ha => by
  rw [atoms_rename, List.mem_map, atoms_exClosure] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [atoms_toGraph _ _ b hb]; rfl

theorem isSentenceOver_singleRel {s l : ℕ} (hl : 2 ≤ l) (φ : RawFormula) :
    IsSentenceOver {(s, l)} (singleRel s l φ) :=
  isSentenceOver_padArgs hl
    ⟨by rw [IsSentence, freeVars_rename]; exact isSentence_exClosure _,
      atoms_rename_exClosure_toGraph s _⟩

theorem finSat_singleRel (s l : ℕ) (φ : RawFormula) : FinSat (singleRel s l φ) ↔ FinSat φ := by
  rw [singleRel, finSat_padArgs l (fun a ha => by rw [atoms_rename_exClosure_toGraph s _ a ha]),
    finSat_rename_singleton (by rw [atoms_exClosure]; exact atoms_toGraph _ _),
    finSat_exClosure, finSat_toGraph (atoms_uniformize _ φ), finSat_uniformize]

open Primrec in
theorem primrec_singleRel (s l : ℕ) : Primrec (singleRel s l) :=
  let hu := primrec₂_uniformize.comp primrec_varBound Primrec.id
  primrec₂_padArgs.comp (const l) (primrec₂_rename.comp (const [s])
    (primrec_exClosure.comp (primrec₂_toGraph.comp (primrec_varBound.comp hu) hu)))

/-! ### Trakhtenbrot's theorem and its corollaries for a fixed vocabulary -/

/-- **Trakhtenbrot's theorem** (extending [Libkin2004], Theorem 9.2): for every vocabulary `σ`
containing a relation symbol of arity at least `2`, no computable procedure decides finite
satisfiability of sentences over `σ`. -/
theorem not_exists_computable_finSat_of_mem {σ : Set (ℕ × ℕ)} {s l : ℕ} (hs : (s, l) ∈ σ)
    (hl : 2 ≤ l) :
    ¬∃ f : RawFormula → Bool, Computable f ∧
      ∀ φ, IsSentenceOver σ φ → (f φ = true ↔ FinSat φ) := fun ⟨f, hf, hfφ⟩ =>
  not_computablePred_finSat <| ComputablePred.computable_iff.2
    ⟨fun φ => f (singleRel s l φ), hf.comp (primrec_singleRel s l).to_comp, funext fun φ =>
      propext <| by
        have h := isSentenceOver_singleRel (s := s) hl φ
        rw [hfφ _ ⟨h.1, fun a ha => h.2 a ha ▸ hs⟩, finSat_singleRel]⟩

/-- **Finite validity is not r.e.** (extending [Libkin2004], Corollary 9.3): for every vocabulary
`σ` containing a relation symbol of arity at least `2`, the finitely valid sentences over `σ` do
not form an r.e. set. -/
theorem not_exists_rePred_finValid_of_mem {σ : Set (ℕ × ℕ)} {s l : ℕ} (hs : (s, l) ∈ σ)
    (hl : 2 ≤ l) :
    ¬∃ S : RawFormula → Prop, REPred S ∧ ∀ φ, IsSentenceOver σ φ → (S φ ↔ FinValid φ) :=
  fun ⟨S, hS, hSφ⟩ => not_rePred_finValid <|
    (hS.comp (primrec_neg ((primrec_singleRel s l).comp (primrec_neg Primrec.id))).to_comp).of_eq
      fun φ => by
        have h := isSentenceOver_singleRel (s := s) hl (neg φ)
        change S (neg (singleRel s l (neg φ))) ↔ _
        rw [hSφ _ (isSentenceOver_neg.2 ⟨h.1, fun a ha => h.2 a ha ▸ hs⟩),
          finValid_neg_iff, finSat_singleRel, finValid_iff_not_finSat_neg]

/-- **Incompleteness for finite validity.** For every vocabulary `σ` containing a relation symbol of
arity at least `2`, every r.e. set of finitely valid sentences misses some finitely valid sentence
over `σ`. -/
theorem exists_isSentenceOver_finValid_not_of_rePred {σ : Set (ℕ × ℕ)} {s l : ℕ} (hs : (s, l) ∈ σ)
    (hl : 2 ≤ l) {S : RawFormula → Prop} (hS : REPred S) (hsound : ∀ φ, S φ → FinValid φ) :
    ∃ φ, IsSentenceOver σ φ ∧ FinValid φ ∧ ¬S φ :=
  hS.exists_not_of_not_exists_rePred_iff (not_exists_rePred_finValid_of_mem hs hl) hsound

/-- **No sound and complete proof system for finite validity.** If `P φ π` ("`π` is a proof of
`φ`") is a decidable relation and only finitely valid sentences have proofs, then for every
vocabulary `σ` containing a relation symbol of arity at least `2` some finitely valid sentence over
`σ` has no proof. -/
theorem exists_isSentenceOver_finValid_unprovable {σ : Set (ℕ × ℕ)} {s l : ℕ} (hs : (s, l) ∈ σ)
    (hl : 2 ≤ l) {β : Type*} [Primcodable β] {P : RawFormula → β → Prop}
    (hP : ComputablePred (Function.uncurry P)) (hsound : ∀ φ π, P φ π → FinValid φ) :
    ∃ φ, IsSentenceOver σ φ ∧ FinValid φ ∧ ∀ π, ¬P φ π :=
  hP.exists_forall_not_of_not_exists_rePred_iff (not_exists_rePred_finValid_of_mem hs hl) hsound

end RawFormula

end Cslib.Logic.FO
