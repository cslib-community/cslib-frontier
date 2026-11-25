/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Languages.RegularLanguage
public import CslibFrontier.Logics.SecondOrder.WordMSO.Basic

/-!
# MSO-definable languages are regular

The direction "MSO-definable ⇒ regular" of the Büchi–Elgot–Trakhtenbrot theorem
[Büchi][Buchi1960], [Elgot][Elgot1961], [Libkin, Theorem 7.21][Libkin2004],
[Thomas, Section 3][Thomas1997].

Following Thomas, a formula `φ : Formula α m n` with free variables is read over the extended
alphabet `ExtLetter α m n`, whose letters carry, besides a letter of `α`, one bit per free
first-order variable and one per free set variable. An extended word encodes the word of its
`α`-components together with an assignment: set variable `X` is assigned the positions whose
`X`-bit is set, and first-order variable `x` the unique position whose `x`-bit is set. The
language `Formula.extLanguage φ` consists of the extended words in which every first-order
variable is marked exactly once and whose encoded word and assignment satisfy `φ`. It is regular
by induction on `φ`: atoms are positional conditions, implication is handled by complement and
union, and both quantifiers by the image along the letter map forgetting the bit of the bound
variable (`Cslib.Language.IsRegular.map`). For a sentence, there are no bits, and the language of
the sentence is the image of its extended language along the projection to `α`.

The alphabet `α` is arbitrary here; finiteness is only needed for the converse.

## Main definitions

* `Cslib.Logic.WordMSO.ExtLetter`: letters of the extended alphabet.
* `Cslib.Logic.WordMSO.Formula.extLanguage`: the language of a formula over the extended alphabet.

## Main results

* `Cslib.Logic.WordMSO.Formula.isRegular_extLanguage`: the extended language of every formula is
  regular.
* `Cslib.Logic.WordMSO.Sentence.isRegular_language`,
  `Cslib.Logic.WordMSO.Definable.isRegular`: MSO-definable languages are regular.

## References

* [J. R. Büchi, *Weak second-order arithmetic and finite automata*][Buchi1960]
* [C. C. Elgot, *Decision problems of finite automata design and related arithmetics*][Elgot1961]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

public section

universe u

namespace Cslib.Logic.WordMSO

variable {α : Type u}

/-- A letter of the extended alphabet for formulas with `m` free first-order and `n` free set
variables: a letter of `α` together with one bit per free variable, recording whether the
current position is the value of the first-order variable, respectively belongs to the value of
the set variable. -/
structure ExtLetter (α : Type u) (m n : ℕ) where
  /-- The underlying letter. -/
  letter : α
  /-- The bits of the first-order variables. -/
  vars : Fin m → Bool
  /-- The bits of the set variables. -/
  sets : Fin n → Bool

namespace ExtLetter

variable {m n : ℕ}

/-- Forget the bit of the last first-order variable. -/
private def dropVar (e : ExtLetter α (m + 1) n) : ExtLetter α m n :=
  ⟨e.letter, Fin.init e.vars, e.sets⟩

/-- Forget the bit of the last set variable. -/
private def dropSet (e : ExtLetter α m (n + 1)) : ExtLetter α m n :=
  ⟨e.letter, e.vars, Fin.init e.sets⟩

end ExtLetter

namespace Formula

open ExtLetter

variable {m n : ℕ}

/-- The language of `φ` over the extended alphabet: the extended words in which every first-order
variable `x` is marked at exactly one position `v x`, and whose letters satisfy `φ` under the
assignment `v` and the assignment of the set of marked positions to each set variable. -/
def extLanguage (φ : Formula α m n) : Language (ExtLetter α m n) :=
  {u | ∃ v : Fin m → Fin u.length, (∀ i x, u[i].vars x = true ↔ v x = i) ∧
    φ.Realize (fun i => u[i].letter) v (fun X => {i | u[i].sets X = true})}

theorem mem_extLanguage {φ : Formula α m n} {u : List (ExtLetter α m n)} :
    u ∈ φ.extLanguage ↔ ∃ v : Fin m → Fin u.length, (∀ i x, u[i].vars x = true ↔ v x = i) ∧
      φ.Realize (fun i => u[i].letter) v (fun X => {i | u[i].sets X = true}) :=
  Iff.rfl

/-! ### Regularity toolkit for languages given by predicates on letter functions -/

section Toolkit

variable {β γ : Type*}

private theorem isRegular_of_iff {P Q : List β → Prop} (h : Language.IsRegular {u | P u})
    (hPQ : ∀ u, P u ↔ Q u) : Language.IsRegular {u | Q u} :=
  Set.ext hPQ ▸ h

/-- Transport a predicate on letter functions along an equality of lengths. -/
private theorem transport {P : (ℓ : ℕ) → (Fin ℓ → β) → Prop} {ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    {g : Fin ℓ → β} {g' : Fin ℓ' → β} (hg : ∀ i, g' (Fin.cast h i) = g i) :
    P ℓ' g' ↔ P ℓ g := by
  subst h; exact (congrArg (P _) (funext hg)).to_iff

/-- The image along a letter map `f` of a regular language given by a predicate `P` on letter
functions is the regular language given by `Q`, provided `Q` holds of a letter function exactly
when it is `f` applied to a letter function satisfying `P`. -/
private theorem isRegular_map {P : (ℓ : ℕ) → (Fin ℓ → β) → Prop}
    {Q : (ℓ : ℕ) → (Fin ℓ → γ) → Prop} (f : β → γ)
    (hP : Language.IsRegular {u : List β | P u.length (fun i => u[i])})
    (hPQ : ∀ ℓ (g' : Fin ℓ → γ), Q ℓ g' ↔ ∃ g : Fin ℓ → β, f ∘ g = g' ∧ P ℓ g) :
    Language.IsRegular {u' : List γ | Q u'.length (fun i => u'[i])} := by
  refine isRegular_of_iff (Cslib.Language.IsRegular.map f hP) fun u' => ?_
  change u' ∈ List.map f '' {u : List β | P u.length (fun i => u[i])} ↔ _
  rw [hPQ]
  refine ⟨?_, fun ⟨g, hfg, hg⟩ => ⟨List.ofFn g,
    (transport (List.length_ofFn (f := g)).symm fun _ => List.getElem_ofFn ..).2 hg,
    by rw [List.map_ofFn, hfg]; exact List.ofFn_getElem⟩⟩
  rintro ⟨u, hu, rfl⟩
  have hlen : u.length = (u.map f).length := (List.length_map _).symm
  exact ⟨fun i => u[Fin.cast hlen.symm i], funext fun _ => (List.getElem_map ..).symm,
    (transport hlen fun _ => rfl).2 hu⟩

end Toolkit

/-! ### Satisfaction over extended words -/

/-- An assignment `v` of positions to the first-order variables is the one marked by the letter
function `g`. -/
private def Marks {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (v : Fin m → Fin ℓ) : Prop :=
  ∀ i x, (g i).vars x = true ↔ v x = i

/-- Satisfaction of `φ` by the word and assignment encoded by the letter function `g`. -/
private def Sat (φ : Formula α m n) (ℓ : ℕ) (g : Fin ℓ → ExtLetter α m n) : Prop :=
  ∃ v, Marks g v ∧ φ.Realize (fun i => (g i).letter) v (fun X => {i | (g i).sets X = true})

/-- Every first-order variable is marked exactly once. -/
private def Valid {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) : Prop := ∃ v, Marks g v

private theorem Marks.unique {ℓ : ℕ} {g : Fin ℓ → ExtLetter α m n} {v v' : Fin m → Fin ℓ}
    (hv : Marks g v) (hv' : Marks g v') : v = v' :=
  funext fun x => ((hv' (v x) x).1 ((hv (v x) x).2 rfl)).symm

private theorem valid_iff {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) :
    Valid g ↔ ∀ x, (∃ i, (g i).vars x = true) ∧
      ¬ ∃ i j : Fin ℓ, i < j ∧ (g i).vars x = true ∧ (g j).vars x = true := by
  refine ⟨fun ⟨v, hv⟩ x => ⟨⟨v x, (hv _ x).2 rfl⟩, fun ⟨i, j, hij, hi, hj⟩ =>
    hij.ne (((hv i x).1 hi).symm.trans ((hv j x).1 hj))⟩, fun h => ?_⟩
  choose v hv using fun x => (h x).1
  refine ⟨v, fun i x => ⟨fun hi => by_contra fun hne => ?_, fun hi => hi ▸ hv x⟩⟩
  exact (lt_or_gt_of_ne hne).elim (fun hlt => (h x).2 ⟨v x, i, hlt, hv x, hi⟩)
    fun hlt => (h x).2 ⟨i, v x, hlt, hi, hv x⟩

private theorem isRegular_valid :
    Language.IsRegular {u : List (ExtLetter α m n) | Valid (fun i : Fin u.length => u[i])} :=
  isRegular_of_iff (Cslib.Language.IsRegular.setOf_forall fun x =>
    (Cslib.Language.IsRegular.setOf_exists_getElem fun e : ExtLetter α m n => e.vars x = true).inf
      (Cslib.Language.IsRegular.setOf_exists_lt (fun e : ExtLetter α m n => e.vars x = true)
        fun e => e.vars x = true).compl) fun _ => (valid_iff _).symm

/-- For a formula whose satisfaction at the marked assignment is a condition `Q` on the marked
positions, satisfaction amounts to validity together with `Q` at all candidate positions. -/
private theorem sat_iff_of_marks {φ : Formula α m n} {ℓ : ℕ} {g : Fin ℓ → ExtLetter α m n}
    {Q : Prop} (hQ : ∀ v, Marks g v → (φ.Realize (fun i => (g i).letter) v
      (fun X => {i | (g i).sets X = true}) ↔ Q)) :
    Sat φ ℓ g ↔ Valid g ∧ Q :=
  ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, (hQ v hv).1 h⟩, fun ⟨⟨v, hv⟩, h⟩ => ⟨v, hv, (hQ v hv).2 h⟩⟩

private theorem sat_letter {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (a : α) (x : Fin m) :
    Sat (letter a x) ℓ g ↔ Valid g ∧ ∀ i, (g i).vars x = true → (g i).letter = a :=
  sat_iff_of_marks fun v hv =>
    ⟨fun h i hi => (hv i x).1 hi ▸ h, fun h => h (v x) ((hv _ x).2 rfl)⟩

private theorem sat_lt {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (x y : Fin m) :
    Sat (lt x y) ℓ g ↔
      Valid g ∧ ∃ i j : Fin ℓ, i < j ∧ (g i).vars x = true ∧ (g j).vars y = true :=
  sat_iff_of_marks fun v hv =>
    ⟨fun h => ⟨v x, v y, h, (hv _ x).2 rfl, (hv _ y).2 rfl⟩,
      fun ⟨i, j, hij, hi, hj⟩ => by change v x < v y; rwa [(hv i x).1 hi, (hv j y).1 hj]⟩

private theorem sat_mem {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (x : Fin m) (X : Fin n) :
    Sat (mem x X) ℓ g ↔ Valid g ∧ ∀ i, (g i).vars x = true → (g i).sets X = true :=
  sat_iff_of_marks fun v hv =>
    ⟨fun h i hi => (hv i x).1 hi ▸ h, fun h => h (v x) ((hv _ x).2 rfl)⟩

private theorem sat_falsum {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) :
    Sat (falsum : Formula α m n) ℓ g ↔ False :=
  ⟨fun ⟨_, _, h⟩ => h, False.elim⟩

private theorem sat_imp {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (φ ψ : Formula α m n) :
    Sat (imp φ ψ) ℓ g ↔ Valid g ∧ (¬ Sat φ ℓ g ∨ Sat ψ ℓ g) := by
  classical
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨⟨v, hv⟩, if hφ : Sat φ ℓ g then
      let ⟨v', hv', hφ'⟩ := hφ; Or.inr ⟨v, hv, h ((hv.unique hv').symm ▸ hφ')⟩
      else Or.inl hφ⟩
  · rintro ⟨⟨v, hv⟩, h | ⟨v', hv', hψ⟩⟩
    · exact ⟨v, hv, fun hφ => absurd ⟨v, hv, hφ⟩ h⟩
    · exact ⟨v, hv, fun _ => (hv.unique hv').symm ▸ hψ⟩

private theorem sat_ex {ℓ : ℕ} (g' : Fin ℓ → ExtLetter α m n) (φ : Formula α (m + 1) n) :
    Sat (ex φ) ℓ g' ↔ ∃ g : Fin ℓ → ExtLetter α (m + 1) n, dropVar ∘ g = g' ∧ Sat φ ℓ g := by
  classical
  constructor
  · rintro ⟨v, hv, j, hφ⟩
    exact ⟨fun i => ⟨(g' i).letter, Fin.snoc (g' i).vars (decide (i = j)), (g' i).sets⟩,
      funext fun _ => by simp only [Function.comp_apply, dropVar, Fin.init_snoc],
      Fin.snoc v j, fun i x => Fin.lastCases (by simp [eq_comm])
        (fun x => by simpa only [Fin.snoc_castSucc] using hv i x) x, hφ⟩
  · rintro ⟨g, rfl, v, hv, hφ⟩
    exact ⟨Fin.init v, fun i x => hv i x.castSucc, v (Fin.last m), by rwa [Fin.snoc_init_self]⟩

private theorem sat_exSet {ℓ : ℕ} (g' : Fin ℓ → ExtLetter α m n) (φ : Formula α m (n + 1)) :
    Sat (exSet φ) ℓ g' ↔ ∃ g : Fin ℓ → ExtLetter α m (n + 1), dropSet ∘ g = g' ∧ Sat φ ℓ g := by
  classical
  constructor
  · rintro ⟨v, hv, S, hφ⟩
    refine ⟨fun i => ⟨(g' i).letter, (g' i).vars, Fin.snoc (g' i).sets (decide (i ∈ S))⟩,
      funext fun _ => by simp only [Function.comp_apply, dropSet, Fin.init_snoc], v, hv, ?_⟩
    refine (congrArg (φ.Realize _ v) ?_).mpr hφ
    exact funext fun X => Fin.lastCases (by ext; simp) (fun _ => by simp only [Fin.snoc_castSucc]) X
  · rintro ⟨g, rfl, v, hv, hφ⟩
    refine ⟨v, hv, {i | (g i).sets (Fin.last n) = true}, ?_⟩
    refine (congrArg (φ.Realize _ v) ?_).mp hφ
    exact funext fun X => Fin.lastCases (by simp only [Fin.snoc_last])
      (fun _ => by simp only [Fin.snoc_castSucc]; rfl) X

private theorem isRegular_sat : ∀ {m n : ℕ} (φ : Formula α m n),
    Language.IsRegular {u : List (ExtLetter α m n) | Sat φ u.length (fun i => u[i])}
  | _, _, letter a x => isRegular_of_iff (isRegular_valid.inf
      (Cslib.Language.IsRegular.setOf_forall_getElem fun e => e.vars x = true → e.letter = a))
      fun _ => (sat_letter _ a x).symm
  | _, _, lt x y => isRegular_of_iff (isRegular_valid.inf
      (Cslib.Language.IsRegular.setOf_exists_lt (fun e => e.vars x = true) fun e =>
        e.vars y = true))
      fun _ => (sat_lt _ x y).symm
  | _, _, mem x X => isRegular_of_iff (isRegular_valid.inf
      (Cslib.Language.IsRegular.setOf_forall_getElem fun e => e.vars x = true → e.sets X = true))
      fun _ => (sat_mem _ x X).symm
  | _, _, falsum => isRegular_of_iff Cslib.Language.IsRegular.zero fun _ => (sat_falsum _).symm
  | _, _, imp φ ψ => isRegular_of_iff
      (isRegular_valid.inf ((isRegular_sat φ).compl.add (isRegular_sat ψ)))
      fun _ => (sat_imp _ φ ψ).symm
  | _, _, ex φ => isRegular_map dropVar (isRegular_sat φ) fun _ g' => sat_ex g' φ
  | _, _, exSet φ => isRegular_map dropSet (isRegular_sat φ) fun _ g' => sat_exSet g' φ

/-- **MSO ⇒ regular, with free variables.** The language over the extended alphabet of any MSO
formula is regular [Thomas, Section 3][Thomas1997]. -/
theorem isRegular_extLanguage (φ : Formula α m n) : φ.extLanguage.IsRegular :=
  isRegular_sat φ

end Formula

/-- **MSO ⇒ regular.** The language of an MSO sentence is regular, over any alphabet
[Büchi][Buchi1960], [Libkin, Theorem 7.21][Libkin2004]. -/
theorem Sentence.isRegular_language (φ : Sentence α) : φ.language.IsRegular :=
  Formula.isRegular_map (P := fun ℓ g => Formula.Sat φ ℓ g)
    (Q := fun ℓ w => φ.Realize w Fin.elim0 Fin.elim0) ExtLetter.letter
    (Formula.isRegular_sat φ) fun ℓ w => ⟨fun h =>
      ⟨fun i => ⟨w i, Fin.elim0, Fin.elim0⟩, rfl, Fin.elim0, fun _ x => x.elim0, by
        rwa [Subsingleton.elim (fun X : Fin 0 => {i : Fin ℓ | (Fin.elim0 : Fin 0 → Bool) X = true})
          Fin.elim0]⟩,
      by
        rintro ⟨g, rfl, v, _, h⟩
        rwa [Subsingleton.elim v Fin.elim0,
          Subsingleton.elim (fun X : Fin 0 => {i : Fin ℓ | (g i).sets X = true}) Fin.elim0] at h⟩

/-- **MSO-definable languages are regular**, over any alphabet. -/
theorem Definable.isRegular {L : Language α} (h : Definable L) : L.IsRegular :=
  let ⟨φ, hL⟩ := h; hL ▸ φ.isRegular_language

/-- First-order definable languages are regular. -/
theorem FODefinable.isRegular {L : Language α} (h : FODefinable L) : L.IsRegular :=
  h.definable.isRegular

end Cslib.Logic.WordMSO
