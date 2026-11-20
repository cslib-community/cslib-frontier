/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Computability.ArithmeticHierarchy
public import CslibFrontier.Foundations.Computability.DiagonalHalting
public import CslibFrontier.Foundations.Computability.OracleJump

/-!
# Post’s theorem for oracle recursive codes

An existential number quantifier over a relation decidable in an oracle is implemented by
unbounded search. A universal quantifier searches for a counterexample and complements
the answer from the next jump. The induction keeps the matrix uniform in its free input
and the witnesses already chosen.

Conversely, bounded evaluation writes a halting run as a finite transcript. Lists of witnesses
combine the formulas for all oracle answers into one alternating prefix. The transcript
and the first list of witnesses share the first existential block.

The hierarchy uses one natural number per alternating block and a computable matrix.
Relative enumeration means the domain of an oracle recursive code, and relative decision
means total computation of the characteristic function. Membership queries return one
for membership and zero otherwise. The jump iterates diagonal halting in the oracle-code
numbering. Its first jump and the ordinary diagonal halting set in Mathlib's code
numbering decide each other.

## Main results

* `mem_arithmeticSigma_succ_iff`: the existential level k + 1 consists of the sets
  enumerable in the kth jump.
* `mem_arithmeticPi_succ_iff`: the universal level k + 1 consists of the complements of
  those sets.
* `mem_arithmeticDelta_succ_iff`: the ambiguous level k + 1 consists of the sets
  decidable in the kth jump.

## References

* [Kelly, *The Arithmetical Hierarchy*][KellyArithmeticalHierarchy], §13.3,
  Proposition 13.4(3)–(4) and Corollary 13.5(1)–(2), pp. 104–105. The results use the
  empty-base-oracle specialization for subsets of `ℕ`; the universal-level result is
  the complement dual of the existential-level result.
  The model here is oracle recursive codes. The correspondence with an explicit oracle
  Turing machine remains a separate milestone of
  [#6650](https://github.com/cslib-community/cslib-frontier/issues/6650).
-/

public section

open Encodable Denumerable

namespace Cslib.Computability

open Nat.RecursiveIn (Code)

private theorem quantify_not (k : ℕ) (b : Bool) (p : List ℕ → Prop) :
    (¬arithmeticQuantify k b p) ↔ arithmeticQuantify k (!b) (fun ns => ¬p ns) := by
  classical
  induction k generalizing b p with
  | zero => rfl
  | succ k ih =>
    cases b
    · exact not_forall.trans (exists_congr fun n => ih true _)
    · exact not_exists.trans (forall_congr' fun n => ih false _)

/-- The universal level consists of complements of sets in the existential level. -/
theorem mem_arithmeticPi_iff_compl_mem_sigma {A : Set ℕ} {k : ℕ} :
    A ∈ ArithmeticPi k ↔ Aᶜ ∈ ArithmeticSigma k := by
  classical
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨fun x => ¬p x, hp.not, fun a => (not_congr (h a)).trans (quantify_not k false _)⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨fun x => ¬p x, hp.not, fun a =>
      (not_not.symm.trans (not_congr (h a))).trans (quantify_not k true _)⟩

private theorem emptyOracle_eq :
    (membershipOracle (∅ : Set ℕ) : ℕ →. ℕ) = fun _ => Part.some 0 := by
  funext n
  change Part.some (membershipOracle ∅ n) = _
  simp [membershipOracle]

/-- Computable predicates are exactly the sets decidable with the empty membership oracle. -/
theorem decidableIn_empty_iff {A : Set ℕ} :
    DecidableIn A ∅ ↔ ComputablePred (· ∈ A) := by
  classical
  have hchar : Computable (membershipOracle A) ↔ ComputablePred (· ∈ A) := by
    constructor
    · intro h
      exact ((Primrec.eq.comp Primrec.id (Primrec.const 1)).computablePred.comp h).of_eq
        fun _ => membershipOracle_eq_one
    · intro h
      refine ((Primrec.dom_bool Bool.toNat).to_comp.comp h.decide).of_eq fun n => ?_
      by_cases hn : n ∈ A <;> simp [membershipOracle, hn]
  unfold DecidableIn
  rw [emptyOracle_eq, ← hchar]
  exact ⟨fun h => (RecursiveIn.iff_nat.mpr h).partrec_of_const, fun h =>
    RecursiveIn.iff_nat.mp h.partrec.recursiveIn⟩

/-- Empty-oracle enumeration coincides with ordinary computable enumerability. -/
theorem enumerableIn_empty_iff {A : Set ℕ} : EnumerableIn A ∅ ↔ REPred (· ∈ A) := by
  constructor
  · rintro ⟨c, hc⟩
    have hr := RecursiveIn.iff_nat.mpr ((Code.exists_code (g := membershipOracle ∅)).mpr ⟨c, rfl⟩)
    rw [emptyOracle_eq] at hr
    exact hr.partrec_of_const.dom_re.of_eq fun n => by
      rw [← emptyOracle_eq]
      exact (hc n).symm
  · intro h
    obtain ⟨c, hc⟩ := rePred_iff_exists_code.mp h
    have hpart : Partrec (Nat.Partrec.Code.eval c) :=
      Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id
    obtain ⟨d, hd⟩ := (Code.exists_code (g := membershipOracle ∅)).mp
      (RecursiveIn.iff_nat.mp hpart.recursiveIn)
    exact ⟨d, fun n => by simpa only [hd, Encodable.encode_nat] using hc n⟩

private theorem primrec_prepend_witness :
    Primrec fun q : ℕ × List ℕ => (q.1.unpair.1, q.1.unpair.2 :: q.2) := by
  let u : Primrec fun q : ℕ × List ℕ => q.1.unpair := Primrec.unpair.comp Primrec.fst
  exact (Primrec.fst.comp u).pair (Primrec.list_cons.comp (Primrec.snd.comp u) Primrec.snd)

private theorem quantify_decidableIn (k : ℕ) (b : Bool) {p : ℕ × List ℕ → Prop}
    (hp : ComputablePred p) :
    DecidableIn {a | arithmeticQuantify k b (fun ns => p (a, ns))} (iteratedJump k) := by
  induction k generalizing b p with
  | zero =>
    exact decidableIn_empty_iff.mpr (hp.comp (Computable.id.pair (Computable.const [])))
  | succ k ih =>
    rw [show iteratedJump (k + 1) = oracleJump (iteratedJump k) from rfl]
    cases b
    · have h := (ih true (hp.comp primrec_prepend_witness.to_comp)).compl.exists_pair
        |>.decidableIn_jump.compl
      convert h using 1
      ext a
      simp [arithmeticQuantify]
    · have h := (ih false (hp.comp primrec_prepend_witness.to_comp)).exists_pair.decidableIn_jump
      convert h using 1
      ext a
      simp [arithmeticQuantify]

/-- An existential arithmetic definition at level k + 1 yields a semidecision procedure
relative to the kth jump. -/
private theorem enumerableIn_iteratedJump_of_mem_arithmeticSigma {A : Set ℕ} {k : ℕ}
    (h : A ∈ ArithmeticSigma (k + 1)) : EnumerableIn A (iteratedJump k) := by
  obtain ⟨p, hp, he⟩ := h
  have hd := quantify_decidableIn k false (hp.comp primrec_prepend_witness.to_comp)
  obtain ⟨c, hc⟩ := hd.exists_pair
  refine ⟨c, fun a => (he a).trans ((?_ : _ ↔ _).trans (hc a))⟩
  simp [arithmeticQuantify]

private theorem quantify_congr (k : ℕ) (b : Bool) {p q : List ℕ → Prop}
    (h : ∀ ns, p ns ↔ q ns) :
    arithmeticQuantify k b p ↔ arithmeticQuantify k b q := by
  induction k generalizing b p q with
  | zero => exact h []
  | succ k ih =>
    cases b
    · exact forall_congr' fun n => ih true (fun ns => h (n :: ns))
    · exact exists_congr fun n => ih false (fun ns => h (n :: ns))

private theorem quantify_take (k : ℕ) (b : Bool) (p : List ℕ → Prop) :
    arithmeticQuantify (k + 1) b (fun ns => p (ns.take k)) ↔ arithmeticQuantify k b p := by
  induction k generalizing b p with
  | zero => cases b <;> simp [arithmeticQuantify]
  | succ k ih =>
    cases b
    · exact forall_congr' fun n => ih true (fun ns => p (n :: ns))
    · exact exists_congr fun n => ih false (fun ns => p (n :: ns))

private theorem quantify_and (k : ℕ) (b : Bool) (P : Prop) (p : List ℕ → Prop) :
    arithmeticQuantify k b (fun ns => P ∧ p ns) ↔ P ∧ arithmeticQuantify k b p := by
  induction k generalizing b p with
  | zero => rfl
  | succ k ih =>
    cases b
    · simp only [arithmeticQuantify, ih]
      exact ⟨fun h => ⟨(h 0).1, fun n => (h n).2⟩, fun h n => ⟨h.1, h.2 n⟩⟩
    · simp only [arithmeticQuantify, ih]
      exact ⟨fun ⟨n, hP, hn⟩ => ⟨hP, n, hn⟩, fun ⟨hP, n, hn⟩ => ⟨n, hP, hn⟩⟩

private def atIndex (w i : ℕ) : ℕ := (ofNat (List ℕ) w).getD i 0

private theorem primrec_atIndex : Primrec₂ atIndex :=
  (Primrec.list_getD 0).comp
    ((Primrec.ofNat (List ℕ)).comp Primrec.fst) Primrec.snd

-- One encoded list supplies the next witness for each component of a bounded conjunction.
private theorem quantify_forall_lt (k : ℕ) (b : Bool) (N : ℕ) (p : ℕ → List ℕ → Prop) :
    arithmeticQuantify k b (fun ws => ∀ i < N, p i (ws.map fun w => atIndex w i)) ↔
      ∀ i < N, arithmeticQuantify k b (p i) := by
  classical
  have pack (f : Fin N → ℕ) (i : ℕ) (hi : i < N) :
      atIndex (encode (List.ofFn f)) i = f ⟨i, hi⟩ := by
    simp [atIndex, List.getD, hi]
  induction k generalizing b p with
  | zero => rfl
  | succ k ih =>
    have step (b : Bool) (w : ℕ) :
        arithmeticQuantify k b (fun ws => ∀ i < N, p i ((w :: ws).map (atIndex · i))) ↔
          ∀ i < N, arithmeticQuantify k b (fun ns => p i (atIndex w i :: ns)) :=
      ih b (fun i ns => p i (atIndex w i :: ns))
    cases b
    · simp only [arithmeticQuantify, step]
      constructor
      · intro h i hi n
        have hh := h (encode (List.ofFn fun _ : Fin N => n)) i hi
        rw [pack _ _ hi] at hh
        exact hh
      · exact fun h w i hi => h i hi (atIndex w i)
    · simp only [arithmeticQuantify, step]
      refine ⟨fun ⟨w, hw⟩ i hi => ⟨atIndex w i, hw i hi⟩, fun h => ?_⟩
      choose f hf using fun i : Fin N => h i i.isLt
      exact ⟨encode (List.ofFn f), fun i hi => by
        rw [pack _ _ hi]
        exact hf ⟨i, hi⟩⟩

private theorem dom_eval_iff {B : Set ℕ} (c : Code) (n : ℕ) :
    (c.eval (membershipOracle B) n).Dom ↔ ∃ σ : List ℕ, ∃ s,
      (c.evaln σ s n).isSome ∧ ∀ i < σ.length, membershipOracle B i = σ.getD i 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨s, hs⟩ := Code.mem_eval_iff_exists_evaln.mp hx
    refine ⟨Code.prefixOf (membershipOracle B) s, s, ?_, fun i hi => ?_⟩
    · exact Option.isSome_iff_exists.mpr ⟨x, hs⟩
    · rw [← List.getElem_eq_getD (h := hi), Code.getElem_prefixOf]
  · rintro ⟨σ, s, hs, hagree⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    refine Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound (fun i hi => ?_) hx⟩
    rw [List.getElem_eq_getD (h := hi) 0, ← hagree i hi]
    exact Part.mem_some _

-- Encoding a stage, a prefix, and the packed first witnesses together absorbs the
-- transcript existential quantifier into the first existential block.
private theorem sigma_of_oracle_halting {B A : Set ℕ} {k : ℕ} {c : ℕ → Code}
    (hc : Primrec c)
    (hA : ∀ n, n ∈ A ↔ ((c n).eval (membershipOracle B) n).Dom)
    (hB : {n | membershipOracle B n.unpair.1 = n.unpair.2} ∈ ArithmeticSigma (k + 1)) :
    A ∈ ArithmeticSigma (k + 1) := by
  obtain ⟨p, hp, hp'⟩ := hB
  let packet (ns : List ℕ) := ofNat (ℕ × List ℕ × ℕ) (ns.getD 0 0)
  let matrix (q : ℕ × List ℕ) : Prop :=
    let (s, σ, w) := packet q.2
    ((c q.1).evaln σ s q.1).isSome ∧
      ∀ i < σ.length, p (i.pair (σ.getD i 0), (w :: q.2.drop 1).map (fun v => atIndex v i))
  have hpacket : Primrec packet :=
    (Primrec.ofNat (ℕ × List ℕ × ℕ)).comp
      ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0))
  have hq : Primrec fun q : ℕ × List ℕ => packet q.2 := hpacket.comp Primrec.snd
  let hσ : Primrec fun q : ℕ × List ℕ => (packet q.2).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hq)
  let hw : Primrec fun q : ℕ × List ℕ => (packet q.2).2.2 :=
    Primrec.snd.comp (Primrec.snd.comp hq)
  have heval : Primrec fun q : ℕ × List ℕ =>
      ((c q.1).evaln (packet q.2).2.1 (packet q.2).1 q.1).isSome :=
    Primrec.option_isSome.comp (Code.primrec_evaln.comp (hσ.pair
      (((Primrec.fst.comp hq).pair (hc.comp Primrec.fst)).pair Primrec.fst)))
  have hcoords : Primrec fun z : (ℕ × List ℕ) × ℕ =>
      (z.2.pair ((packet z.1.2).2.1.getD z.2 0),
        ((packet z.1.2).2.2 :: z.1.2.drop 1).map (fun v => atIndex v z.2)) :=
    (Primrec₂.natPair.comp Primrec.snd
      ((Primrec.list_getD 0).comp (hσ.comp Primrec.fst) Primrec.snd)).pair
      (Primrec.list_map ((Primrec.list_cons.comp hw
        (Primrec.list_drop.comp (Primrec.const 1) Primrec.snd)).comp Primrec.fst)
        (primrec_atIndex.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂)
  have hm : ComputablePred matrix :=
    (ComputablePred.computable_iff.mpr ⟨_, heval.to_comp, rfl⟩).and
      (ComputablePred.forall_lt (hp.comp hcoords.to_comp) (Primrec.list_length.comp hσ).to_comp)
  refine ⟨matrix, hm, fun n => (hA n).trans ((dom_eval_iff (c n) n).trans ?_)⟩
  simp only [arithmeticQuantify]
  have unpack (t : ℕ) (ns : List ℕ) :
      packet (t :: ns) = ofNat (ℕ × List ℕ × ℕ) t := by
    simp [packet]
  have step (s : ℕ) (σ : List ℕ) (w : ℕ) :
      arithmeticQuantify k false (fun ns =>
        ((c n).evaln σ s n).isSome ∧
          ∀ i < σ.length, p (i.pair (σ.getD i 0), (w :: ns).map (fun v => atIndex v i))) ↔
        ((c n).evaln σ s n).isSome ∧ ∀ i < σ.length,
          arithmeticQuantify k false (fun ns => p (i.pair (σ.getD i 0), atIndex w i :: ns)) :=
    (quantify_and k false _ _).trans (and_congr_right fun _ =>
      quantify_forall_lt k false σ.length
        (fun i ns => p (i.pair (σ.getD i 0), atIndex w i :: ns)))
  have answers (σ : List ℕ) (i : ℕ) :
      membershipOracle B i = σ.getD i 0 ↔
      ∃ w, arithmeticQuantify k false (fun ns => p (i.pair (σ.getD i 0), w :: ns)) := by
    simpa [arithmeticQuantify] using hp' (i.pair (σ.getD i 0))
  constructor
  · rintro ⟨σ, s, hs, hσ⟩
    have hall : ∀ i < σ.length, arithmeticQuantify (k + 1) true
        (fun ns => p (i.pair (σ.getD i 0), ns)) :=
      fun i hi => (answers σ i).mp (hσ i hi)
    obtain ⟨w, hw⟩ := (quantify_forall_lt (k + 1) true σ.length
      (fun i ns => p (i.pair (σ.getD i 0), ns))).mpr hall
    refine ⟨encode (s, σ, w), (quantify_congr k false (fun ns => ?_)).mpr
      ((quantify_and k false _ _).mpr ⟨hs, hw⟩)⟩
    simp [matrix, unpack]
  · rintro ⟨t, ht⟩
    rcases htup : ofNat (ℕ × List ℕ × ℕ) t with ⟨s, σ, w⟩
    have h := (step s σ w).mp ((quantify_congr k false (fun ns => by
      simp only [matrix, unpack, htup, List.drop_succ_cons, List.drop_zero])).mp ht)
    exact ⟨σ, s, h.1, fun i hi => (answers σ i).mpr ⟨atIndex w i, h.2 i hi⟩⟩


private theorem sigma_oracle_answers_succ {B : Set ℕ} {k : ℕ}
    (h : B ∈ ArithmeticSigma (k + 1)) :
    {n | membershipOracle B n.unpair.1 = n.unpair.2} ∈ ArithmeticSigma (k + 2) := by
  obtain ⟨p, hp, h⟩ := h
  let matrix (q : ℕ × List ℕ) : Prop :=
    (q.1.unpair.2 = 1 ∧ p (q.1.unpair.1, q.2.take (k + 1))) ∨
      (q.1.unpair.2 = 0 ∧ ¬p (q.1.unpair.1, q.2.drop 1))
  let u : Primrec fun q : ℕ × List ℕ => q.1.unpair := Primrec.unpair.comp Primrec.fst
  let i := Primrec.fst.comp u
  let a := Primrec.snd.comp u
  have htest (b : ℕ) : ComputablePred fun q : ℕ × List ℕ => q.1.unpair.2 = b :=
    (Primrec.eq.comp a (Primrec.const b)).computablePred
  have htake := i.pair (Primrec.list_take.comp (Primrec.const (k + 1)) Primrec.snd)
  have hdrop := i.pair (Primrec.list_drop.comp (Primrec.const 1) Primrec.snd)
  refine ⟨matrix, ((htest 1).and (hp.comp htake.to_comp)).or
    ((htest 0).and (hp.comp hdrop.to_comp).not), ?_⟩
  intro n
  change membershipOracle B n.unpair.1 = n.unpair.2 ↔ _
  by_cases h₁ : n.unpair.2 = 1
  · rw [h₁, membershipOracle_eq_one, h]
    exact (quantify_take (k + 1) true _).symm.trans
      (quantify_congr (k + 2) true fun ns => by simp [matrix, h₁])
  · have he :
        membershipOracle B n.unpair.1 = n.unpair.2 ↔
          n.unpair.2 = 0 ∧ n.unpair.1 ∉ B := by
      classical
      by_cases hb : n.unpair.1 ∈ B
      · simp [membershipOracle, hb, Ne.symm h₁]
      · simp [membershipOracle, hb, eq_comm]
    have hn : (n.unpair.1 ∉ B) ↔ arithmeticQuantify (k + 2) true
        (fun ns => ¬p (n.unpair.1, ns.drop 1)) := by
      rw [show (n.unpair.1 ∉ B) ↔ ¬arithmeticQuantify (k + 1) true
        (fun ns => p (n.unpair.1, ns)) from not_congr (h _), quantify_not]
      simp [arithmeticQuantify]
    rw [he, hn, ← quantify_and (k + 2) true]
    apply quantify_congr
    intro ns
    simp [matrix, h₁]

private theorem sigma_empty_answers :
    {n | membershipOracle ∅ n.unpair.1 = n.unpair.2} ∈ ArithmeticSigma 1 := by
  refine ⟨fun q => 0 = q.1.unpair.2, ?_, fun n => ?_⟩
  · exact (Primrec.eq.comp (Primrec.const 0)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).computablePred
  · simp [arithmeticQuantify, membershipOracle]

private theorem sigma_iteratedJump_answers (k : ℕ) :
    {n | membershipOracle (iteratedJump k) n.unpair.1 = n.unpair.2} ∈
      ArithmeticSigma (k + 1) := by
  induction k with
  | zero => exact sigma_empty_answers
  | succ k ih =>
    apply sigma_oracle_answers_succ
    exact sigma_of_oracle_halting (Primrec.ofNat Code) (fun _ => Iff.rfl) ih

/-- The next diagonal halting set has an existential definition at level k + 1. -/
theorem iteratedJump_succ_mem_arithmeticSigma (k : ℕ) :
    iteratedJump (k + 1) ∈ ArithmeticSigma (k + 1) :=
  sigma_of_oracle_halting (Primrec.ofNat Code) (fun _ => Iff.rfl) (sigma_iteratedJump_answers k)

/-- Post's theorem for the existential levels. -/
theorem mem_arithmeticSigma_succ_iff {A : Set ℕ} {k : ℕ} :
    A ∈ ArithmeticSigma (k + 1) ↔ EnumerableIn A (iteratedJump k) := by
  refine ⟨enumerableIn_iteratedJump_of_mem_arithmeticSigma, fun ⟨c, hc⟩ => ?_⟩
  exact sigma_of_oracle_halting (Primrec.const c) hc (sigma_iteratedJump_answers k)

/-- Post's theorem for the universal levels. -/
theorem mem_arithmeticPi_succ_iff {A : Set ℕ} {k : ℕ} :
    A ∈ ArithmeticPi (k + 1) ↔ EnumerableIn Aᶜ (iteratedJump k) :=
  mem_arithmeticPi_iff_compl_mem_sigma.trans mem_arithmeticSigma_succ_iff

/-- Post's theorem for the ambiguous levels. -/
theorem mem_arithmeticDelta_succ_iff {A : Set ℕ} {k : ℕ} :
    A ∈ ArithmeticDelta (k + 1) ↔ DecidableIn A (iteratedJump k) :=
  (and_congr mem_arithmeticSigma_succ_iff mem_arithmeticPi_succ_iff).trans
    decidableIn_iff_enumerableIn_compl.symm

/-- The first existential level consists of the computably enumerable sets. -/
theorem mem_arithmeticSigma_one_iff {A : Set ℕ} :
    A ∈ ArithmeticSigma 1 ↔ REPred (· ∈ A) :=
  mem_arithmeticSigma_succ_iff.trans enumerableIn_empty_iff

/-- The first universal level consists of the co-computably enumerable sets. -/
theorem mem_arithmeticPi_one_iff {A : Set ℕ} :
    A ∈ ArithmeticPi 1 ↔ REPred (· ∉ A) :=
  mem_arithmeticPi_succ_iff.trans enumerableIn_empty_iff

/-- The first ambiguous level consists of the computable sets. -/
theorem mem_arithmeticDelta_one_iff {A : Set ℕ} :
    A ∈ ArithmeticDelta 1 ↔ ComputablePred (· ∈ A) :=
  mem_arithmeticDelta_succ_iff.trans decidableIn_empty_iff

open Nat.RecursiveIn.KleenePost (halting exists_primrec_reduce_dom_to_halting)

/-- The first jump in the oracle-code numbering reduces to ordinary diagonal halting. -/
theorem decidableIn_firstJump_halting : DecidableIn (iteratedJump 1) halting := by
  have hr : REPred (· ∈ iteratedJump 1) :=
    mem_arithmeticSigma_one_iff.mp (iteratedJump_succ_mem_arithmeticSigma 0)
  obtain ⟨c, hc⟩ := rePred_iff_exists_code.mp hr
  have hp : Partrec c.eval :=
    Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id
  obtain ⟨_, hk, he⟩ := exists_primrec_reduce_dom_to_halting hp
  exact decidableIn_of_primrec_preimage hk fun n => (hc n).trans (he n)

/-- Ordinary diagonal halting reduces to the first jump in the oracle-code numbering. -/
theorem decidableIn_halting_firstJump : DecidableIn halting (iteratedJump 1) := by
  have hp : Partrec fun n : ℕ => (ofNat Nat.Partrec.Code n).eval n :=
    Nat.Partrec.Code.eval_part.comp (Primrec.ofNat Nat.Partrec.Code).to_comp Computable.id
  exact (enumerableIn_empty_iff.mpr hp.dom_re).decidableIn_jump

/-- At level two one may use the ordinary diagonal halting set as the oracle. -/
theorem mem_arithmeticSigma_two_iff {A : Set ℕ} :
    A ∈ ArithmeticSigma 2 ↔ EnumerableIn A halting :=
  mem_arithmeticSigma_succ_iff.trans
    ⟨fun h => h.of_decidableIn decidableIn_firstJump_halting,
      fun h => h.of_decidableIn decidableIn_halting_firstJump⟩

end Cslib.Computability
