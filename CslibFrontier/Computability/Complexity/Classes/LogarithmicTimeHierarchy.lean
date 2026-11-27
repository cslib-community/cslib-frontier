/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.AC0
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Logics.FirstOrder.Ordered.Query
public import CslibFrontier.Logics.SecondOrder.WordMSO.FirstOrder
import CslibFrontier.Computability.Circuit.Boolean.FirstOrder.Ordered
import CslibFrontier.Computability.Circuit.Simps
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple
import CslibFrontier.Logics.SecondOrder.Encoding

/-!
# The logarithmic-time hierarchy

We use the descriptive characterization of LH from [Immerman1999, Theorem 5.30]:
bounded-alternation logarithmic time with random access captures first-order logic on
canonically ordered inputs with BIT. On a binary word, the input relation tests the letter
at a position. We reuse the word vocabulary, in which the two letter predicates are
complements and strict order is recoverable from the canonical weak order. The canonical
numeric constants are definable from the order.

The convention that the universe has distinct zero and one leaves words of length zero
and one outside the formula test. Their membership is unrestricted because they form
a finite set and can be decided by finite control. The machine characterization is cited
here; the definitions and proofs use ordered first-order semantics.

LH is contained in `L` for every encoding. A word is given to the logspace model checker of
ordered first-order sentences (`Cslib.Logic.FO.Ordered.queryLanguage_mem_L`) as the structure
with one unary relation, its own bits, and the defining sentence is pulled back along the
first-order interpretation of the word structure in it, whose strict order is the canonical weak
order without equality. The at most three words of length below two are sent to fixed members or
non-members of the target query.

On bit strings, LH is contained in nonuniform AC⁰: the ordered first-order model checker compiles
the defining sentence, at each length `n ≥ 2`, into a polynomial-size constant-depth formula over
the atomic facts of the word structure, in which order atoms are constants and letter atoms are
input bits or their negations. Lengths zero and one are decided by formulas of constant size.
Barrington, Immerman and Straubing show that LH is exactly DLOGTIME-uniform AC⁰
[BarringtonImmermanStraubing1990]; uniformity is not proved here.

## Main definitions

* `Cslib.Logic.FO.Ordered.ofWord`: the canonical ordered structure of a word of length at least two.
* `Cslib.Complexity.LH`: the logarithmic-time hierarchy of languages on binary encodings.

## Main results

* `Cslib.Complexity.compl_mem_LH`: LH is closed under complement.
* `Cslib.Complexity.LH_subset_L`: LH is contained in logarithmic space.
* `Cslib.Complexity.LH_subset_AC0`: LH on bit strings is contained in nonuniform AC⁰.
-/

public section

namespace Cslib.Logic.FO.Ordered

open Cslib.Logic.WordMSO

/-- Interpret the word vocabulary on positions, with the canonical numeric vocabulary
provided by the ordered structure. -/
@[expose] def ofWord {α : Type} (w : List α) (hw : 2 ≤ w.length) :
    Structure (wordLanguage α) :=
  ⟨w.length, hw, wordStructure w⟩

end Cslib.Logic.FO.Ordered

namespace Cslib.Complexity

open FirstOrder.Language
open Cslib.Logic.WordMSO (wordLanguage)
open Cslib.Logic.FO.Ordered (language ofWord)

/-- A language is in LH if one ordered first-order sentence decides it on all encoded
words of length at least two. -/
@[expose] def LH {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ φ : (language (wordLanguage Bool)).Sentence,
    ∀ a (ha : 2 ≤ (enc a).length), a ∈ A ↔ φ.Realize (ofWord (enc a) ha)}

/-- Negating the defining ordered sentence decides the complement. -/
theorem compl_mem_LH {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ LH enc) :
    Aᶜ ∈ LH enc := by
  obtain ⟨φ, hφ⟩ := hA
  refine ⟨φ.not, fun a ha => (not_congr (hφ a ha)).trans ?_⟩
  exact (Sentence.realize_not (ofWord (enc a) ha)).symm

/-! ### LH is contained in `L` -/

section L

open FirstOrder Cslib.Logic
open Cslib.Logic.WordMSO (wordStructure WordRel)
open Cslib.Logic.FO.Ordered (FullTupleInterpretation queryLanguage)
open Turing.MultiTapeTM

/-- The vocabulary of bit strings: one unary relation, the positions holding `true`. -/
private abbrev BitLanguage : FirstOrder.Language := ESO.varLanguage fun _ : Unit => 1

/-- The relation symbol of `BitLanguage`. -/
private noncomputable def bitRel : BitLanguage.Relations 1 := ⟨(), rfl⟩

/-- The vocabulary of `BitLanguage`: a single table, of the relation `bitRel`. -/
private def bitVocabulary : Vocabulary BitLanguage :=
  ESO.varLanguage.vocabulary _ finOneEquiv

/-- A bit string as a structure: its length, then its own bits as the table of `bitRel`. -/
private def bitEncode (w : List Bool) : EncodedStructure := (w.length, [w])

private theorem wellFormed_bitEncode (w : List Bool) : bitVocabulary.WellFormed (bitEncode w) :=
  ⟨rfl, fun i => by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    exact (pow_one _).symm⟩

private theorem relMap_decode_bitEncode (w : List Bool) (x : Fin 1 → Fin (bitEncode w).1) :
    (bitVocabulary.decode (bitEncode w)).RelMap bitRel x ↔ w.getD (x 0) false = true := by
  rw [Vocabulary.relMap_decode, tupleIndex_apply]
  simp [Vocabulary.table, bitEncode, bitVocabulary, ESO.varLanguage.index_vocabulary, bitRel]

/-- The positions holding `true`, as a formula of the ordered bit-string language. -/
private noncomputable def bitAt {α : Type} (t : (language BitLanguage).Term α) :
    (language BitLanguage).Formula α :=
  Relations.formula₁ ((LHom.sumInl : BitLanguage →ᴸ language BitLanguage).onRelation bitRel) t

/-- The word structure of a bit string, interpreted in its bit-string structure on the same
positions: strict order from the canonical weak order, and letters from the bits. -/
private noncomputable def wordInterpretation :
    FullTupleInterpretation BitLanguage (wordLanguage Bool) 1 where
  rel {r} R := match r, R with
    | _, .lt => FO.Ordered.le BitLanguage (.var (0, 0)) (.var (1, 0)) ⊓
        ∼((Term.var (0, 0)).equal (.var (1, 0)))
    | _, .letter true => bitAt (.var (0, 0))
    | _, .letter false => ∼(bitAt (.var (0, 0)))

/-- A bit string of length at least two satisfies the pulled-back sentence exactly when its word
structure satisfies the original one. -/
private theorem bitEncode_mem_queryLanguage_iff (φ : (language (wordLanguage Bool)).Sentence)
    (w : List Bool) (hw : 2 ≤ w.length) :
    bitEncode w ∈ queryLanguage bitVocabulary (wordInterpretation.onSentence φ) ↔
      φ.Realize (ofWord w hw) := by
  let : Fact (2 ≤ (bitEncode w).1) := ⟨hw⟩
  rw [FO.Ordered.mem_queryLanguage, and_iff_right (wellFormed_bitEncode w)]
  let := bitVocabulary.decode (bitEncode w)
  rw [wordInterpretation.realize_onSentence Nat.one_pos]
  have heq : (⟨(bitEncode w).1 ^ 1, FullTupleInterpretation.two_le_pow (k := 1) Nat.one_pos,
      wordInterpretation.inputStructure⟩ : FO.Ordered.Structure (wordLanguage Bool)) =
      ofWord w hw := by
    refine FO.Ordered.Structure.ext (pow_one _) fun R xs => ?_
    have hval (i) : ((FO.Ordered.lexEquiv.symm (xs i) 0 : Fin (bitEncode w).1) : ℕ) = xs i := by
      rw [FO.Ordered.lexEquiv_symm_apply_val]
      have := (xs i).isLt
      simp only [Fin.rev_zero, Fin.val_last, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt (by simpa using this)
    revert xs
    dsimp only [ofWord]
    intro xs hval
    cases R with
    | lt =>
      refine Iff.trans ?_ (wordStructure.relMap_ltSymb w _).symm
      change (wordInterpretation.rel WordRel.lt).Realize
        (fun p => FO.Ordered.lexEquiv.symm (xs p.1) p.2) ↔ (xs 0 : ℕ) < xs 1
      simp only [wordInterpretation, Formula.realize_inf, Formula.realize_not,
        FO.Ordered.realize_le, Formula.realize_equal, Term.realize_var, Fin.le_def, Fin.ext_iff,
        hval]
      omega
    | letter b =>
      refine Iff.trans ?_ (wordStructure.relMap_letterSymb w b _).symm
      change (wordInterpretation.rel (WordRel.letter b)).Realize
        (fun p => FO.Ordered.lexEquiv.symm (xs p.1) p.2) ↔ _
      have hbit : (bitAt (.var ((0 : Fin 1), (0 : Fin 1)))).Realize
          (fun p => FO.Ordered.lexEquiv.symm (xs p.1) p.2) ↔
            w[(Fin.cast (pow_one _) ∘ xs) 0] = true := by
        simp only [bitAt, Formula.realize_rel₁, LHom.map_onRelation, Term.realize_var]
        rw [relMap_decode_bitEncode]
        have hlt : (xs 0 : ℕ) < w.length := by simpa [bitEncode] using (xs 0).isLt
        simp only [Matrix.cons_val_zero, hval, Function.comp_apply, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
        rfl
      cases b
      · simp only [wordInterpretation, Formula.realize_not, hbit, Bool.not_eq_true]
        exact Iff.rfl
      · exact hbit
  rw [← heq]

private theorem computableInLogSpace_bitEncode {α : Type} (enc : α ↪ List Bool) :
    ComputableInLogSpace (fun a => bitEncode (enc a)) enc encStructure := by
  have hw : ComputableInLogSpace (fun a => enc a) enc encBits := .of_eq fun _ => rfl
  have hlen : ComputableInLogSpace (fun a => (enc a).length) enc encUnary :=
    ComputableInLogSpace.bitsLength.comp hw
  exact ComputableInLogSpace.pair hlen (ComputableInLogSpace.listSingleton.comp hw)

/-- A problem that agrees, on inputs encoded by words of length at least two, with the preimage
of a problem in `L` under a logspace map is in `L`, provided the target has a member and a
non-member: the at most three shorter words are mapped to these. -/
private theorem mem_L_of_forall_two_le {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {T : Set EncodedStructure} (hT : T ∈ L encStructure) {f : α → EncodedStructure}
    (hf : ComputableInLogSpace f enc encStructure) {yes no : EncodedStructure} (hyes : yes ∈ T)
    (hno : no ∉ T) (hA : ∀ a, 2 ≤ (enc a).length → (a ∈ A ↔ f a ∈ T)) : A ∈ L enc := by
  classical
  let c : List Bool → EncodedStructure := fun w => if ∃ a ∈ A, enc a = w then yes else no
  have hw : ComputableInLogSpace (fun a => enc a) enc encBits := .of_eq fun _ => rfl
  have hlen : ComputableInLogSpace (fun a => (enc a).length) enc encUnary :=
    ComputableInLogSpace.bitsLength.comp hw
  refine LogSpaceReducible.mem_L ⟨fun a => if decide ((enc a).length ≤ 1) then
      (if (enc a).isEmpty then c [] else if (enc a).headD false then c [true] else c [false])
    else f a, ?_, fun a => ?_⟩ hT
  · exact ComputableInLogSpace.ite (ComputableInLogSpace.unaryLeConst 1 hlen)
      (ComputableInLogSpace.ite (ComputableInLogSpace.of_isEmpty fun _ => rfl)
        (ComputableInLogSpace.const _) (ComputableInLogSpace.ite
          ((ComputableInLogSpace.bitsHeadD false).comp hw) (ComputableInLogSpace.const _)
          (ComputableInLogSpace.const _))) hf
  · by_cases hshort : (enc a).length ≤ 1
    · have hc : (if (enc a).isEmpty then c [] else if (enc a).headD false then c [true]
          else c [false]) = c (enc a) := by
        rcases h : enc a with _ | ⟨b, _ | ⟨b', w⟩⟩
        · rfl
        · cases b <;> rfl
        · simp [h] at hshort
      simp only [decide_eq_true hshort, ite_true, hc, c]
      by_cases ha : a ∈ A
      · simp only [ha, true_iff]
        rw [ite_eq_left ⟨a, ha, rfl⟩]
        exact hyes
      · simp only [ha, false_iff]
        rw [ite_eq_right fun ⟨a', ha', he⟩ => ha (enc.injective he ▸ ha')]
        exact hno
    · simp only [decide_eq_false hshort]
      exact hA a (by omega)

/-- **LH is contained in `L`**, for every encoding. The defining ordered first-order sentence is
pulled back to the structure of the encoded word with one unary relation, and checked there by
the logarithmic-space model checker of ordered first-order logic
(`Cslib.Logic.FO.Ordered.queryLanguage_mem_L`, after [Immerman1999]). -/
theorem LH_subset_L {α : Type} {enc : α ↪ List Bool} : LH enc ⊆ L enc := by
  rintro A ⟨φ, hφ⟩
  have hno (ψ) : ((0, []) : EncodedStructure) ∉ queryLanguage bitVocabulary ψ :=
    FO.Ordered.notMem_queryLanguage_of_lt_two _ (by decide) ψ
  by_cases hT : ∃ y, y ∈ queryLanguage bitVocabulary (wordInterpretation.onSentence φ)
  · obtain ⟨y, hy⟩ := hT
    exact mem_L_of_forall_two_le (FO.Ordered.queryLanguage_mem_L _ _)
      (computableInLogSpace_bitEncode enc) hy (hno _)
      fun a ha => (hφ a ha).trans (bitEncode_mem_queryLanguage_iff φ _ ha).symm
  · have htop : bitEncode [false, false] ∈ queryLanguage bitVocabulary
        (wordInterpretation.onSentence ⊤) :=
      (bitEncode_mem_queryLanguage_iff ⊤ _ le_rfl).2 (Sentence.realize_top _)
    refine mem_L_of_forall_two_le (FO.Ordered.queryLanguage_mem_L _ _)
      (ComputableInLogSpace.const (0, [])) htop (hno _) fun a ha => ?_
    exact iff_of_false (fun h => hT ⟨_, (bitEncode_mem_queryLanguage_iff φ _ ha).2
      ((hφ a ha).1 h)⟩) (hno _)

end L

/-! ### LH is contained in nonuniform AC⁰ -/

section AC0

open Cslib.Logic.WordMSO (wordStructure WordRel)
open Cslib.Logic.FO (Atom atomsOf)
open Turing.MultiTapeTM (encBits)
open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ModelChecking
  Cslib.Circuits.Boolean.ModelChecking.Ordered

/-- The word structure of `y` on the canonical universe `Fin n`. -/
@[instance_reducible]
private def bitsStructure {n : ℕ} (y : Fin n → Bool) :
    (wordLanguage Bool).Structure (Fin n) where
  funMap := fun f => Empty.elim f
  RelMap := fun {r} R xs => match r, R with
    | _, .lt => xs 0 < xs 1
    | _, .letter b => y (xs 0) = b

private theorem ofWord_ofFn {n : ℕ} (hn : 2 ≤ n) (y : Fin n → Bool)
    (h : 2 ≤ (List.ofFn y).length) :
    ofWord (List.ofFn y) h = ⟨n, hn, bitsStructure y⟩ := by
  refine Cslib.Logic.FO.Ordered.Structure.ext (List.length_ofFn) fun R xs => ?_
  revert xs
  dsimp only [ofWord]
  intro xs
  cases R with
  | lt => exact (wordStructure.relMap_ltSymb (List.ofFn y) xs).trans Iff.rfl
  | letter b =>
    refine (wordStructure.relMap_letterSymb (List.ofFn y) b xs).trans ?_
    change _ ↔ y (Fin.cast List.length_ofFn (xs 0)) = b
    simp only [Fin.getElem_fin, List.getElem_ofFn]
    rfl

/-- The unbounded fan-in formula reading the truth of a word atom off the input bits: order atoms
are constants, letter atoms are an input bit or its negation. -/
private def atomFormula {n : ℕ} :
    Atom (wordLanguage Bool) n → Circuits.Formula Unbounded.signature n
  | ⟨⟨_, .lt⟩, t⟩ => constUnbounded (decide (t 0 < t 1))
  | ⟨⟨_, .letter true⟩, t⟩ => .input (t 0)
  | ⟨⟨_, .letter false⟩, t⟩ => .gate .not ![.input (t 0)]

private theorem eval_atomFormula {n : ℕ} (y : Fin n → Bool) (a : Atom (wordLanguage Bool) n) :
    (atomFormula a).eval Unbounded.interpretation y =
      letI := bitsStructure y; atomsOf (L := wordLanguage Bool) (Equiv.refl (Fin n)) a := by
  obtain ⟨⟨_, R⟩, t⟩ := a
  rw [Bool.eq_iff_iff]
  have key : (letI := bitsStructure y; atomsOf (L := wordLanguage Bool) (Equiv.refl (Fin n))
      ⟨⟨_, R⟩, t⟩) = true ↔ @Structure.RelMap _ _ (bitsStructure y) _ R t := by
    classical
    exact decide_eq_true_iff
  rw [key]
  cases R with
  | lt =>
    simp only [atomFormula, eval_constUnbounded, decide_eq_true_iff]
    exact Iff.rfl
  | letter b =>
    change _ ↔ y (t 0) = b
    cases b <;> simp [atomFormula]

private theorem bounds_atomFormula {n : ℕ} (a : Atom (wordLanguage Bool) n) :
    (atomFormula a).depth ≤ 1 ∧ (atomFormula a).size ≤ 1 := by
  obtain ⟨⟨_, R⟩, t⟩ := a
  cases R with
  | lt => constructor <;> circuit_bound [atomFormula, constUnbounded]
  | letter b => cases b <;> constructor <;> circuit_bound [atomFormula]

private theorem exists_formula_slice {A : Set (List Bool)}
    {φ : (language (wordLanguage Bool)).Sentence}
    (hφ : ∀ w (hw : 2 ≤ w.length), w ∈ A ↔ φ.Realize (ofWord w hw)) {n : ℕ} (hn : 2 ≤ n) :
    ∃ F : Circuits.Formula Unbounded.signature n,
      F.Computes Unbounded.interpretation (Language.slice A n) ∧
        F.depth ≤ foDepth φ + 1 ∧ F.size ≤ (foSize φ + 2) * (n + 2) ^ foSize φ := by
  classical
  have := Fintype.ofFinite (Σ l, (wordLanguage Bool).Relations l)
  let : Fact (2 ≤ n) := ⟨hn⟩
  let e : Atom (wordLanguage Bool) n ≃ Fin (Fintype.card (Atom (wordLanguage Bool) n)) :=
    Fintype.equivFin _
  let G := toUnbounded e φ Fin.elim0
  let sub := fun j => atomFormula (e.symm j)
  have hsubd : ∀ j, (sub j).depth ≤ 1 := fun j => (bounds_atomFormula (e.symm j)).1
  have hsubs : ∀ j, (sub j).size ≤ 1 := fun j => (bounds_atomFormula (e.symm j)).2
  refine ⟨G.bind sub, fun y => ?_, ?_, ?_⟩
  · let := bitsStructure y
    have hatoms : (fun j => (sub j).eval Unbounded.interpretation y) =
        atomsOf (L := wordLanguage Bool) (Equiv.refl _) ∘ e.symm :=
      funext fun j => eval_atomFormula y (e.symm j)
    rw [Circuits.Formula.eval_bind, hatoms, Bool.eq_iff_iff, eval_toUnbounded_atomsOf e φ Fin.elim0]
    have hlen : 2 ≤ (List.ofFn y).length := by simpa using hn
    have hslice : Language.slice A n y = true ↔ φ.Realize (ofWord (List.ofFn y) hlen) :=
      Language.slice_eq_true_iff.trans (hφ _ hlen)
    rw [hslice, ofWord_ofFn hn y]
    rw [Sentence.Realize, Formula.Realize, Subsingleton.elim (Empty.elim : Empty → Fin n) default,
      Subsingleton.elim (Fin.elim0 : Fin 0 → Fin n) default]
  · have := depth_toUnbounded_le e φ Fin.elim0
    circuit_bound
  · have := size_toUnbounded_le e φ Fin.elim0
    have := leafSize_toUnbounded_le e φ Fin.elim0
    have : 1 ≤ (n + 2) ^ foSize φ := Nat.one_le_pow _ _ (by omega)
    circuit_bound

/-- **LH is contained in nonuniform AC⁰.** Every language of bit strings in the logarithmic-time
hierarchy is decided, at each input length, by unbounded fan-in circuits of constant depth and
polynomial size: compile the defining ordered sentence with the formula-expansion argument of
[Immerman1999, Chapter 5] and read the letter atoms off the input bits. The stronger
DLOGTIME-uniform statement [BarringtonImmermanStraubing1990] is not proved here. -/
theorem LH_subset_AC0 : LH encBits ⊆ AC0 := by
  rintro A ⟨φ, hφ⟩
  refine ConstDepth.mem_iff.2 ⟨foDepth φ + 1, fun n => (foSize φ + 2) * (n + 2) ^ foSize φ,
    by fun_prop, fun n => ?_⟩
  suffices ∃ F : Circuits.Formula Unbounded.signature n,
      F.Computes Unbounded.interpretation (Language.slice A n) ∧ F.depth ≤ foDepth φ + 1 ∧
        F.size ≤ (foSize φ + 2) * (n + 2) ^ foSize φ by
    obtain ⟨F, hF, hd, hs⟩ := this
    exact ⟨F.toCircuit, hF.toCircuit, F.depth_toCircuit_le.trans hd, by simpa using hs⟩
  by_cases hn : 2 ≤ n
  · exact exists_formula_slice (A := A) (φ := φ) hφ hn
  have hs : 1 ≤ (foSize φ + 2) * (n + 2) ^ foSize φ :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · refine ⟨constUnbounded (Language.slice A 0 Fin.elim0), fun x => ?_, ?_, ?_⟩
    · rw [eval_constUnbounded, Subsingleton.elim x Fin.elim0]
    · simp
    · simpa using hs
  · refine ⟨if Language.slice A 1 ![false] = Language.slice A 1 ![true]
      then constUnbounded (Language.slice A 1 ![true])
      else if Language.slice A 1 ![true] then .input 0 else .gate .not ![.input 0],
      fun x => ?_, ?_, ?_⟩
    · have hx : x = ![x 0] := funext fun i => by rw [Subsingleton.elim i 0]; rfl
      rw [hx]
      cases h : x 0 <;> split_ifs <;> simp_all
    · split_ifs <;> simp
    · split_ifs <;> simp [hs]

end AC0

end Cslib.Complexity
