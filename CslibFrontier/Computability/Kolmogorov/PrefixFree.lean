/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Partrec
public import CslibFrontier.Foundations.Computability.ComputablePred
public import Mathlib.InformationTheory.Coding.PrefixFree
import CslibFrontier.Computability.Kolmogorov.Incompleteness
import CslibFrontier.Computability.Kolmogorov.Incompressibility
import CslibFrontier.Computability.Kolmogorov.Uncomputability
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Foundations.Data.List.Primrec
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Foundations.Data.List.UnaryCode
import Mathlib.Computability.Primrec.List

/-!
# Prefix-free Kolmogorov complexity and the invariance theorem

A description method `M : DescriptionMethod α` is *prefix-free* (`M.IsPrefixFree`) when its
halting domain `M.haltingSet = {p | ∃ x, M.Produces p x}` is prefix-free in the sense of
`InformationTheory.IsPrefixFree`: no halting program is a strict prefix of another halting
program [LiVitanyi2019].

Given any partial recursive code `c : Nat.Partrec.Code`, `ofPrefixCode c` dovetails the clocked
evaluations of `c` and accepts a halting pair `(q, x)` only when `q` is prefix-incomparable with
every previously accepted program. Thus `ofPrefixCode c` is always both partial recursive and
prefix-free, and agrees exactly with `ofCode c` whenever `ofCode c` is already prefix-free.

The *universal prefix-free description method* `universalPrefix : DescriptionMethod ℕ` parses a
strict self-delimiting code header `codeHeader c` (`parseCodeHeader`) followed by a program `p`,
and runs `p` under `ofPrefixCode c`. Because `Set.range codeHeader` is prefix-free and each
`ofPrefixCode c` is prefix-free, `universalPrefix` is prefix-free (`isPrefixFree_universalPrefix`),
partial recursive (`isPartrec_universalPrefix`), and additively optimal for the class of prefix-free
partial recursive description methods (`isAdditivelyOptimal_universalPrefix`: the **prefix-free
invariance theorem**). Pushing `universalPrefix` forward along binary-string decoding yields the
universal prefix-free description method `universalPrefixBits : DescriptionMethod (List Bool)` on
binary strings.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.haltingSet`: the set of programs on which `M` halts.
* `Cslib.Kolmogorov.DescriptionMethod.IsPrefixFree`: prefix-freeness of `M.haltingSet`.
* `Cslib.Kolmogorov.decodeSelfDelimiting?`: strict partial decoder for `selfDelimitingCode`.
* `Cslib.Kolmogorov.DescriptionMethod.parseCodeHeader`: strict parser for `codeHeader c ++ p`.
* `Cslib.Kolmogorov.DescriptionMethod.prefixAccepted`,
  `Cslib.Kolmogorov.DescriptionMethod.ofPrefixCode`: prefix-free restriction of `ofCode c`.
* `Cslib.Kolmogorov.DescriptionMethod.universalPrefix`: the universal prefix-free description
  method for natural numbers.
* `Cslib.Kolmogorov.DescriptionMethod.universalPrefixBits`: the universal prefix-free description
  method for binary strings.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPrefixPartrec`: prefix-free minorization predicate
  for arbitrary `Primcodable` types.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.isPrefixFree_ofPrefixCode`,
  `Cslib.Kolmogorov.DescriptionMethod.isPartrec_ofPrefixCode`: every `ofPrefixCode c` is
  prefix-free and partial recursive.
* `Cslib.Kolmogorov.DescriptionMethod.ofPrefixCode_produces_iff_of_isPrefixFree`: `ofPrefixCode c`
  preserves `ofCode c` whenever `ofCode c` is already prefix-free.
* `Cslib.Kolmogorov.DescriptionMethod.isPrefixFree_universalPrefix`,
  `Cslib.Kolmogorov.DescriptionMethod.isPartrec_universalPrefix`: `universalPrefix` is
  prefix-free and partial recursive.
* `Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universalPrefix`: **prefix-free
  invariance theorem** for `{M : DescriptionMethod ℕ | M.IsPartrec ∧ M.IsPrefixFree}`.
* `Cslib.Kolmogorov.DescriptionMethod.minorizesPrefixPartrec_universalPrefix`,
  `Cslib.Kolmogorov.DescriptionMethod.minorizesPrefixPartrec_universalPrefixBits`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universalPrefixBits_le_of_partrec_eval`:
  prefix-free minorization and invariance for natural numbers and binary strings.
* `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universalPrefixBits_le_selfDelimiting`:
  `K(x) ≤ |x| + 2 size |x| + O(1)` for binary strings under `universalPrefixBits`.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPrefixPartrec.not_computable_complexity`:
  prefix-free complexity is uncomputable.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPrefixPartrec.exists_forall_le_of_rePred`:
  Chaitin's incompleteness theorem for prefix-free complexity.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
* [G. J. Chaitin, *Information-Theoretic Limitations of Formal Systems*][Chaitin1974]
-/

public section

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec

/-! ### Strict self-delimiting decoder -/

private theorem eq_bits_foldr_of_length_eq_size {l : List Bool}
    (h : l.length = (l.foldr Nat.bit 0).size) : l = (l.foldr Nat.bit 0).bits := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil =>
      cases a <;> simp at h ⊢
    | cons b t' =>
      set m := (b :: t').foldr Nat.bit 0
      have hpos : m ≠ 0 := fun hm => by cases a <;> simp [m, hm] at h
      have hbits := Nat.bits_append_bit m a fun hm => absurd hm hpos
      have hsize : (Nat.bit a m).size = m.size + 1 := by
        simpa only [← Nat.size_eq_bits_len, List.length_cons] using congrArg List.length hbits
      rw [List.foldr_cons, hbits, ← ih (Nat.succ.inj (h.trans hsize))]

private theorem size_eq_iff_pow_le_of_lt {n k : ℕ} (hn : n < 2 ^ k) :
    n.size = k ↔ k = 0 ∨ 2 ^ (k - 1) ≤ n := by
  cases k with
  | zero => simp [Nat.lt_one_iff.mp hn]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or, Nat.add_sub_cancel,
      ← not_lt (a := n), ← Nat.size_le]
    have hle := Nat.size_le.mpr hn
    omega

/-- Strict partial decoder for `selfDelimitingCode`: `decodeSelfDelimiting? q = some (b, p)` if and
only if `selfDelimitingCode b ++ p = q`. -/
@[expose] def decodeSelfDelimiting? (q : List Bool) : Option (List Bool × List Bool) :=
  let k := q.idxOf false
  let r := q.drop (k + 1)
  let n := (r.take k).foldr Nat.bit 0
  if k < q.length ∧ k + n ≤ r.length ∧ n.size = k then
    some ((r.drop k).take n, (r.drop k).drop n)
  else
    none

private theorem drop_take_foldr_eq {r : List Bool} {k : ℕ} (hk : k ≤ r.length)
    (hsize : ((r.take k).foldr Nat.bit 0).size = k) :
    r.take k = ((r.take k).foldr Nat.bit 0).bits :=
  eq_bits_foldr_of_length_eq_size (by rw [List.length_take_of_le hk, hsize])

/-- `decodeSelfDelimiting?` succeeds with `(b, p)` exactly when `q = selfDelimitingCode b ++ p`. -/
theorem decodeSelfDelimiting?_eq_some_iff {q b p : List Bool} :
    decodeSelfDelimiting? q = some (b, p) ↔ selfDelimitingCode b ++ p = q := by
  constructor
  · intro h
    simp only [decodeSelfDelimiting?] at h
    split_ifs at h with hcond
    obtain ⟨hk, hkn, hsize⟩ := hcond
    cases h
    set k := q.idxOf false
    set r := q.drop (k + 1)
    set n := (r.take k).foldr Nat.bit 0
    set b' := (r.drop k).take n
    set p' := (r.drop k).drop n
    have hq_split : q = List.replicate k true ++ false :: r :=
      List.eq_replicate_idxOf_false (List.idxOf_lt_length_iff.mp hk)
    have hbits : r.take k = n.bits := drop_take_foldr_eq (by omega) hsize
    have hblen : b'.length = n := List.length_take_of_le (by simp; omega)
    have hr_split : r = n.bits ++ (b' ++ p') := by
      rw [← hbits, List.take_append_drop n (r.drop k), List.take_append_drop]
    rw [hq_split, hr_split]
    simp only [selfDelimitingCode, hblen, hsize, List.append_assoc, List.cons_append]
  · rintro rfl
    have hidx : (selfDelimitingCode b ++ p).idxOf false = b.length.size := by
      rw [selfDelimitingCode, List.append_assoc, List.idxOf_append_of_notMem (by simp),
        List.length_replicate, List.cons_append, List.idxOf_cons_self, Nat.add_zero]
    have hdrop :
        (selfDelimitingCode b ++ p).drop (b.length.size + 1) = b.length.bits ++ (b ++ p) := by
      rw [← List.drop_drop, selfDelimitingCode, List.append_assoc,
        List.drop_left' (List.length_replicate ..), List.cons_append, List.drop_one, List.tail_cons,
        List.append_assoc]
    have hfold : ((b.length.bits ++ (b ++ p)).take b.length.size).foldr Nat.bit 0 = b.length := by
      rw [List.take_left' (Nat.size_eq_bits_len _), Nat.foldr_bit_bits]
    simp only [decodeSelfDelimiting?, hidx, hdrop, hfold, List.drop_left' (Nat.size_eq_bits_len _),
      List.take_left, List.drop_left]
    simp [selfDelimitingCode, Nat.size_eq_bits_len]

@[simp]
theorem decodeSelfDelimiting?_selfDelimitingCode_append (b p : List Bool) :
    decodeSelfDelimiting? (selfDelimitingCode b ++ p) = some (b, p) :=
  decodeSelfDelimiting?_eq_some_iff.mpr rfl

@[simp]
theorem decodeSelfDelimiting?_selfDelimitingCode (b : List Bool) :
    decodeSelfDelimiting? (selfDelimitingCode b) = some (b, []) := by
  simpa using decodeSelfDelimiting?_selfDelimitingCode_append b []

/-- `selfDelimitingCode` has a prefix-free range. -/
theorem isPrefixFree_range_selfDelimitingCode :
    InformationTheory.IsPrefixFree (Set.range selfDelimitingCode) := by
  rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩ ⟨r, hr⟩
  obtain ⟨rfl, -⟩ := selfDelimitingCode_append_inj (q' := []) (by simpa using hr)
  rfl

theorem primrec_two_pow : Primrec (fun n : ℕ => 2 ^ n) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

/-- The strict self-delimiting decoder is primitive recursive. -/
theorem primrec_decodeSelfDelimiting? : Primrec decodeSelfDelimiting? := by
  have hk : Primrec fun q : List Bool => q.idxOf false :=
    Primrec.list_idxOf.comp (Primrec.const false) Primrec.id
  have hr : Primrec fun q : List Bool => q.drop (q.idxOf false + 1) :=
    Primrec.list_drop.comp (Primrec.succ.comp hk) Primrec.id
  have hn : Primrec fun q : List Bool =>
      ((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0 :=
    Primrec.list_foldr_nat_bit.comp (Primrec.list_take.comp hk hr)
  have h1 : PrimrecPred fun q : List Bool => q.idxOf false < q.length :=
    PrimrecRel.comp Primrec.nat_lt hk Primrec.list_length
  have h2 : PrimrecPred fun q : List Bool =>
      q.idxOf false + ((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0 ≤
        (q.drop (q.idxOf false + 1)).length :=
    PrimrecRel.comp Primrec.nat_le (Primrec.nat_add.comp hk hn) (Primrec.list_length.comp hr)
  have hpow : PrimrecPred fun q : List Bool =>
      q.idxOf false = 0 ∨
        2 ^ (q.idxOf false - 1) ≤
          ((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0 :=
    (Primrec.eq.comp hk (Primrec.const 0)).or
      (PrimrecRel.comp Primrec.nat_le (primrec_two_pow.comp (Primrec.pred.comp hk)) hn)
  have hcond : PrimrecPred fun q : List Bool =>
      q.idxOf false < q.length ∧
        q.idxOf false + ((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0 ≤
          (q.drop (q.idxOf false + 1)).length ∧
        (q.idxOf false = 0 ∨
          2 ^ (q.idxOf false - 1) ≤
            ((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0) :=
    h1.and (h2.and hpow)
  have hsome : Primrec fun q : List Bool =>
      some (((q.drop (q.idxOf false + 1)).drop (q.idxOf false)).take
          (((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0),
        ((q.drop (q.idxOf false + 1)).drop (q.idxOf false)).drop
          (((q.drop (q.idxOf false + 1)).take (q.idxOf false)).foldr Nat.bit 0)) :=
    Primrec.option_some.comp <| Primrec.pair
      (Primrec.list_take.comp hn (Primrec.list_drop.comp hk hr))
      (Primrec.list_drop.comp hn (Primrec.list_drop.comp hk hr))
  refine (Primrec.ite hcond hsome (Primrec.const Option.none)).of_eq fun q => ?_
  simp only [decodeSelfDelimiting?]
  set k := q.idxOf false
  set r := q.drop (k + 1)
  set n := (r.take k).foldr Nat.bit 0
  have hn_lt : n < 2 ^ k := (Nat.foldr_bit_lt _).trans_le
    (Nat.pow_le_pow_right Nat.two_pos (List.length_take_le (i := k) (l := r)))
  simp only [size_eq_iff_pow_le_of_lt hn_lt]

theorem primrecPred_length_eq_size_foldr_bit :
    PrimrecPred fun b : List Bool => b.length = (b.foldr Nat.bit 0).size := by
  have hpow : PrimrecPred fun b : List Bool =>
      b.length = 0 ∨ 2 ^ (b.length - 1) ≤ b.foldr Nat.bit 0 :=
    (Primrec.eq.comp Primrec.list_length (Primrec.const 0)).or
      (PrimrecRel.comp Primrec.nat_le
        (primrec_two_pow.comp (Primrec.pred.comp Primrec.list_length))
        Primrec.list_foldr_nat_bit)
  refine hpow.of_eq fun b => ?_
  simpa only [eq_comm] using (size_eq_iff_pow_le_of_lt (Nat.foldr_bit_lt b)).symm

namespace DescriptionMethod

/-! ### Prefix-free description methods -/

/-- The halting set of a description method `M`: the programs that eventually output some object. -/
@[expose] def haltingSet {α : Type*} (M : DescriptionMethod α) : Set (List Bool) :=
  {p | ∃ x, M.Produces p x}

/-- A description method is *prefix-free* when its halting set is prefix-free: no halting program
is a prefix of a distinct halting program. -/
@[expose] def IsPrefixFree {α : Type*} (M : DescriptionMethod α) : Prop :=
  InformationTheory.IsPrefixFree M.haltingSet

@[simp]
theorem haltingSet_map {α β : Type*} (f : α → β) (M : DescriptionMethod α) :
    (M.map f).haltingSet = M.haltingSet := by
  ext p
  simp only [haltingSet, Set.mem_ofPred_eq, map_produces_iff]
  exact ⟨fun ⟨_, x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨f x, x, hx, rfl⟩⟩

theorem IsPrefixFree.map {α β : Type*} {M : DescriptionMethod α} (hM : M.IsPrefixFree)
    (f : α → β) : (M.map f).IsPrefixFree := by
  simpa only [IsPrefixFree, haltingSet_map] using hM

/-! ### Strict code-header parser -/

/-- Strict parser for `codeHeader c ++ p`: returns `some (c, p)` if and only if
`codeHeader c ++ p = q`. -/
@[expose] def parseCodeHeader (q : List Bool) : Option (Code × List Bool) :=
  match decodeSelfDelimiting? q with
  | Option.none => Option.none
  | some (b, p) =>
    if b.length = (b.foldr Nat.bit 0).size then
      some (ofNat Code (b.foldr Nat.bit 0), p)
    else
      Option.none

/-- `parseCodeHeader q = some (c, p)` if and only if `codeHeader c ++ p = q`. -/
theorem parseCodeHeader_eq_some_iff {q : List Bool} {c : Code} {p : List Bool} :
    parseCodeHeader q = some (c, p) ↔ codeHeader c ++ p = q := by
  constructor
  · intro h
    rcases hd : decodeSelfDelimiting? q with _ | ⟨b, p'⟩ <;>
      simp only [parseCodeHeader, hd, reduceCtorEq] at h
    split_ifs at h with hsz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [codeHeader, encode_ofNat, ← eq_bits_foldr_of_length_eq_size hsz,
      decodeSelfDelimiting?_eq_some_iff.mp hd]
  · rintro rfl
    simp [parseCodeHeader, codeHeader, Nat.foldr_bit_bits, Nat.size_eq_bits_len]

@[simp]
theorem parseCodeHeader_codeHeader_append (c : Code) (p : List Bool) :
    parseCodeHeader (codeHeader c ++ p) = some (c, p) :=
  parseCodeHeader_eq_some_iff.mpr rfl

theorem codeHeader_injective : Function.Injective codeHeader := fun c₁ c₂ h => by
  have h1 := congrArg (fun q => parseCodeHeader (q ++ [])) h
  simpa only [parseCodeHeader_codeHeader_append, Option.some.injEq, Prod.mk.injEq, and_true]
    using h1

/-- The set of code headers `codeHeader c` is prefix-free. -/
theorem isPrefixFree_range_codeHeader :
    InformationTheory.IsPrefixFree (Set.range codeHeader) :=
  isPrefixFree_range_selfDelimitingCode.anti fun _ ⟨c, hc⟩ => ⟨(encode c).bits, hc⟩

theorem prefix_of_parseCodeHeader_eq_some {q₁ q₂ : List Bool} {c₁ c₂ : Code} {p₁ p₂ : List Bool}
    (h₁ : parseCodeHeader q₁ = some (c₁, p₁)) (h₂ : parseCodeHeader q₂ = some (c₂, p₂))
    (hp : q₁ <+: q₂) : c₁ = c₂ ∧ p₁ <+: p₂ := by
  rw [← parseCodeHeader_eq_some_iff.mp h₁, ← parseCodeHeader_eq_some_iff.mp h₂] at hp
  exact (Cslib.BitString.prefix_append_of_isPrefixFree isPrefixFree_range_codeHeader
    ⟨c₁, rfl⟩ ⟨c₂, rfl⟩ hp).imp_left fun h => codeHeader_injective h

/-- `parseCodeHeader` is primitive recursive. -/
theorem primrec_parseCodeHeader : Primrec parseCodeHeader := by
  have hsome : Primrec fun bp : List Bool × List Bool =>
      some (ofNat Code (bp.1.foldr Nat.bit 0), bp.2) :=
    Primrec.option_some.comp
      (Primrec.pair ((Primrec.ofNat Code).comp (Primrec.list_foldr_nat_bit.comp Primrec.fst))
        Primrec.snd)
  have hf : Primrec fun bp : List Bool × List Bool =>
      if bp.1.length = (bp.1.foldr Nat.bit 0).size then
        some (ofNat Code (bp.1.foldr Nat.bit 0), bp.2)
      else Option.none :=
    Primrec.ite (primrecPred_length_eq_size_foldr_bit.comp Primrec.fst) hsome
      (Primrec.const Option.none)
  refine (Primrec.option_bind primrec_decodeSelfDelimiting? (hf.comp Primrec.snd).to₂).of_eq
    fun q => ?_
  simp only [parseCodeHeader]
  cases decodeSelfDelimiting? q <;> rfl

/-! ### Prefix-free trimming of partial recursive codes -/

/-- Candidate `(q, x)` at dovetailing index `k`: decodes `k` to `(q, t)` and returns `(q, x)`
when `Code.evaln t c (encode q) = some x`. -/
@[expose] def prefixCand (c : Code) (k : ℕ) : Option (List Bool × ℕ) :=
  (decode (α := List Bool × ℕ) k).bind fun qt =>
    (Code.evaln qt.2 c (encode qt.1)).map fun x => (qt.1, x)

/-- The list of prefix-free `(program, output)` pairs accepted for code `c` after `n` dovetailing
steps. -/
@[expose] def prefixAccepted (c : Code) : ℕ → List (List Bool × ℕ)
  | 0 => []
  | n + 1 =>
    let acc := prefixAccepted c n
    match prefixCand c n with
    | Option.none => acc
    | some (q, x) =>
      if acc.any (fun entry => decide (q <+: entry.1) || decide (entry.1 <+: q)) then
        acc
      else
        acc ++ [(q, x)]

theorem prefixAccepted_prefix_succ (c : Code) (n : ℕ) :
    prefixAccepted c n <+: prefixAccepted c (n + 1) := by
  rw [prefixAccepted]
  rcases prefixCand c n with _ | ⟨q, x⟩ <;> dsimp only
  · exact List.prefix_rfl
  · split_ifs <;> simp

theorem prefixAccepted_prefix (c : Code) {m n : ℕ} (h : m ≤ n) :
    prefixAccepted c m <+: prefixAccepted c n := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (prefixAccepted_prefix_succ c _)

private theorem prefixAccepted_invariants (c : Code) (n : ℕ) :
    InformationTheory.IsPrefixFree {q | ∃ x, (q, x) ∈ prefixAccepted c n} ∧
      ((prefixAccepted c n).map Prod.fst).Nodup ∧
      ∀ q x, (q, x) ∈ prefixAccepted c n → x ∈ c.eval (encode q) := by
  induction n with
  | zero =>
    simp [prefixAccepted, InformationTheory.IsPrefixFree]
  | succ n ih =>
    rcases ih with ⟨hpf, hnodup, hsound⟩
    simp only [prefixAccepted]
    rcases hcand : prefixCand c n with _ | ⟨q, x⟩
    · exact ⟨hpf, hnodup, hsound⟩
    · dsimp only
      split_ifs with hconf
      · exact ⟨hpf, hnodup, hsound⟩
      · have hno : ∀ entry ∈ prefixAccepted c n, ¬ (q <+: entry.1) ∧ ¬ (entry.1 <+: q) := by
          intro entry hent
          simpa [List.any_eq_true, not_or] using fun h : q <+: entry.1 ∨ entry.1 <+: q =>
            hconf (List.any_eq_true.mpr ⟨entry, hent, by simpa using h⟩)
        have hq_notMem : q ∉ (prefixAccepted c n).map Prod.fst := fun hmem =>
          let ⟨entry, hent, heq⟩ := List.mem_map.mp hmem
          (hno entry hent).1 (heq ▸ List.prefix_rfl)
        have hq_eval : x ∈ c.eval (encode q) := by
          simp only [prefixCand, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcand
          obtain ⟨⟨_, _⟩, _, _, hx', rfl, rfl⟩ := hcand
          exact Code.evaln_sound hx'
        refine ⟨?_, ?_, ?_⟩
        · rintro p₁ ⟨y₁, hy₁⟩ p₂ ⟨y₂, hy₂⟩ hp
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hy₁ hy₂
          rcases hy₁ with hy₁ | ⟨rfl, rfl⟩ <;> rcases hy₂ with hy₂ | ⟨rfl, rfl⟩
          exacts [hpf p₁ ⟨y₁, hy₁⟩ p₂ ⟨y₂, hy₂⟩ hp, absurd hp (hno (p₁, y₁) hy₁).2,
            absurd hp (hno (p₂, y₂) hy₂).1, rfl]
        · exact List.map_append .. ▸
            hnodup.append (List.nodup_singleton q) (by simpa using hq_notMem)
        · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
          rintro p y (hy | ⟨rfl, rfl⟩)
          exacts [hsound p y hy, hq_eval]

theorem mem_prefixAccepted_iff_lookup {c : Code} {n : ℕ} {p : List Bool} {x : ℕ} :
    (p, x) ∈ prefixAccepted c n ↔ (prefixAccepted c n).lookup p = some x :=
  (List.lookup_eq_some_iff_mem (prefixAccepted_invariants c n).2.1).symm

theorem lookup_prefixAccepted_mono {c : Code} {m n : ℕ} (hmn : m ≤ n) {p : List Bool} {x : ℕ}
    (hx : x ∈ (prefixAccepted c m).lookup p) : x ∈ (prefixAccepted c n).lookup p := by
  obtain ⟨R, hR⟩ := prefixAccepted_prefix c hmn
  rw [← hR, Option.mem_def, List.lookup_append, Option.mem_def.mp hx, Option.some_or]

/-- The prefix-free restriction of `ofCode c`: a program `p` outputs `x` at stage `n` if `(p, x)`
appears in `prefixAccepted c n`. -/
def ofPrefixCode (c : Code) : DescriptionMethod ℕ where
  run p := ⟨fun n => (prefixAccepted c n).lookup p,
    fun n _ hx => lookup_prefixAccepted_mono n.le_succ hx⟩

theorem mem_ofPrefixCode_runFor {c : Code} {p : List Bool} {n x : ℕ} :
    x ∈ ((ofPrefixCode c).run p).runFor n ↔ (p, x) ∈ prefixAccepted c n :=
  mem_prefixAccepted_iff_lookup.symm

theorem ofPrefixCode_produces_iff {c : Code} {p : List Bool} {x : ℕ} :
    (ofPrefixCode c).Produces p x ↔ ∃ n, (p, x) ∈ prefixAccepted c n :=
  produces_iff_exists_mem_runFor.trans (exists_congr fun _ => mem_ofPrefixCode_runFor)

/-- Every `ofPrefixCode c` is prefix-free. -/
theorem isPrefixFree_ofPrefixCode (c : Code) : (ofPrefixCode c).IsPrefixFree := by
  rintro p₁ ⟨x₁, h₁⟩ p₂ ⟨x₂, h₂⟩ hp
  obtain ⟨n₁, hn₁⟩ := ofPrefixCode_produces_iff.mp h₁
  obtain ⟨n₂, hn₂⟩ := ofPrefixCode_produces_iff.mp h₂
  exact (prefixAccepted_invariants c (max n₁ n₂)).1 p₁
    ⟨x₁, (prefixAccepted_prefix c (le_max_left n₁ n₂)).subset hn₁⟩ p₂
    ⟨x₂, (prefixAccepted_prefix c (le_max_right n₁ n₂)).subset hn₂⟩ hp

/-- Every program halting under `ofPrefixCode c` halts with the same output under `ofCode c`. -/
theorem ofCode_produces_of_ofPrefixCode_produces {c : Code} {p : List Bool} {x : ℕ}
    (h : (ofPrefixCode c).Produces p x) : (ofCode c).Produces p x := by
  obtain ⟨n, hn⟩ := ofPrefixCode_produces_iff.mp h
  exact ofCode_produces_iff.mpr ((prefixAccepted_invariants c n).2.2 p x hn)

theorem ofPrefixCode_haltingSet_subset (c : Code) :
    (ofPrefixCode c).haltingSet ⊆ (ofCode c).haltingSet :=
  fun _ ⟨x, hx⟩ => ⟨x, ofCode_produces_of_ofPrefixCode_produces hx⟩

/-- When `ofCode c` is already prefix-free, `ofPrefixCode c` has the exact same outputs as
`ofCode c`. -/
theorem ofPrefixCode_produces_iff_of_isPrefixFree {c : Code} (hpf : (ofCode c).IsPrefixFree)
    {p : List Bool} {x : ℕ} : (ofPrefixCode c).Produces p x ↔ (ofCode c).Produces p x := by
  refine ⟨ofCode_produces_of_ofPrefixCode_produces, fun h => ?_⟩
  obtain ⟨t, ht⟩ := Code.evaln_complete.mp (ofCode_produces_iff.mp h)
  let k := encode (p, t)
  have hcand : prefixCand c k = some (p, x) := by
    simp only [prefixCand, k, encodek, Option.bind_some, Option.mem_def.mp ht, Option.map_some]
  by_cases hmem : p ∈ (prefixAccepted c k).map Prod.fst
  · obtain ⟨⟨p', x'⟩, hent, rfl⟩ := List.mem_map.mp hmem
    obtain rfl := Part.mem_unique ((prefixAccepted_invariants c k).2.2 p' x' hent)
      (ofCode_produces_iff.mp h)
    exact ofPrefixCode_produces_iff.mpr ⟨k, hent⟩
  · have hno : (prefixAccepted c k).any
        (fun entry => decide (p <+: entry.1) || decide (entry.1 <+: p)) = false := by
      refine List.any_eq_false.mpr fun entry hent => ?_
      have he_halt : entry.1 ∈ (ofCode c).haltingSet :=
        ⟨entry.2, ofCode_produces_iff.mpr ((prefixAccepted_invariants c k).2.2 _ _ hent)⟩
      have hne : p ≠ entry.1 := fun heq => hmem (List.mem_map.mpr ⟨entry, hent, heq.symm⟩)
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
      exact ⟨fun hp' => hne (hpf p ⟨x, h⟩ entry.1 he_halt hp'),
        fun hp' => hne (hpf entry.1 he_halt p ⟨x, h⟩ hp').symm⟩
    exact ofPrefixCode_produces_iff.mpr ⟨k + 1, by simp [prefixAccepted, hcand, hno]⟩

private theorem primrec₂_prefixCand : Primrec₂ prefixCand := by
  have hdec : Primrec (decode (α := List Bool × ℕ)) := Primrec.decode
  have heval : Primrec₂ fun (c : Code) (qt : List Bool × ℕ) =>
      Code.evaln qt.2 c (encode qt.1) :=
    Primrec₂.mk <| Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst)
        (Primrec.encode.comp (Primrec.fst.comp Primrec.snd)))
  have hmap : Primrec₂ fun (c : Code) (qt : List Bool × ℕ) =>
      (Code.evaln qt.2 c (encode qt.1)).map fun x => (qt.1, x) :=
    Primrec₂.mk <| (Primrec.option_map heval
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  exact Primrec₂.mk <| (Primrec.option_bind (hdec.comp Primrec.snd)
    ((hmap.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).of_eq fun _ => rfl

private theorem primrec₂_prefixAccepted : Primrec₂ prefixAccepted := by
  have hconf : PrimrecRel fun (acc : List (List Bool × ℕ)) (q : List Bool) =>
      ∃ entry ∈ acc, entry.1 <+: q ∨ q <+: entry.1 :=
    PrimrecRel.exists_mem_list (R := fun (entry : List Bool × ℕ) (q : List Bool) =>
        entry.1 <+: q ∨ q <+: entry.1)
      ((Primrec.list_isPrefix.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).or
        (Primrec.list_isPrefix.comp Primrec.snd (Primrec.fst.comp Primrec.fst)))
  have hstep_some : Primrec fun arg : (Code × ℕ × List (List Bool × ℕ)) × (List Bool × ℕ) =>
      if arg.1.2.2.any (fun entry => decide (arg.2.1 <+: entry.1) || decide (entry.1 <+: arg.2.1))
      then arg.1.2.2
      else arg.1.2.2 ++ [arg.2] := by
    have hpred : PrimrecPred fun arg : (Code × ℕ × List (List Bool × ℕ)) × (List Bool × ℕ) =>
        ∃ entry ∈ arg.1.2.2, entry.1 <+: arg.2.1 ∨ arg.2.1 <+: entry.1 :=
      hconf.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
    have happend : Primrec fun arg : (Code × ℕ × List (List Bool × ℕ)) × (List Bool × ℕ) =>
        arg.1.2.2 ++ [arg.2] :=
      Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    refine (Primrec.ite hpred (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) happend).of_eq
      fun _ => by
        simp only [List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        congr 1
        exact propext (exists_congr fun _ => and_congr_right' or_comm)
  have hg : Primrec₂ fun (c : Code) (p : ℕ × List (List Bool × ℕ)) =>
      match prefixCand c p.1 with
      | Option.none => p.2
      | some qx =>
        if p.2.any (fun entry => decide (qx.1 <+: entry.1) || decide (entry.1 <+: qx.1)) then p.2
        else p.2 ++ [qx] :=
    Primrec₂.mk <| (Primrec.option_casesOn
      (primrec₂_prefixCand.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      hstep_some.to₂).of_eq fun ⟨c, n, _⟩ => by cases prefixCand c n <;> rfl
  refine (Primrec.nat_rec (Primrec.const []) hg).of_eq fun c n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    change (match prefixCand c n with | Option.none => _ | some qx => _) = prefixAccepted c (n + 1)
    rw [ih]
    rcases h : prefixCand c n with _ | ⟨q, x⟩ <;> simp [prefixAccepted, h]

theorem primrec₂_prefixAccepted_lookup :
    Primrec₂ fun (cp : Code × List Bool) (n : ℕ) => (prefixAccepted cp.1 n).lookup cp.2 := by
  refine Primrec₂.mk <| (Primrec.listLookup.comp (Primrec.snd.comp Primrec.fst)
    (primrec₂_prefixAccepted.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq
    fun ⟨cp, n⟩ => ?_
  induction prefixAccepted cp.1 n with
  | nil => rfl
  | cons kv tl ih =>
    rcases kv with ⟨k, v⟩
    have heq : @BEq.beq (List Bool) instBEqOfDecidableEq cp.2 k =
        @BEq.beq (List Bool) List.instBEq cp.2 k := by simp
    simp only [List.lookup_cons, heq, ih]

/-- Joint partial recursive evaluation of `ofPrefixCode c` in `(c, p)`. -/
theorem partrec₂_ofPrefixCode_eval :
    Partrec₂ fun (c : Code) (p : List Bool) =>
      Nat.rfindOpt fun n => (prefixAccepted c n).lookup p :=
  Partrec.rfindOpt primrec₂_prefixAccepted_lookup.to_comp

private theorem ofPrefixCode_produces_iff_mem_rfindOpt {c : Code} {p : List Bool} {x : ℕ} :
    (ofPrefixCode c).Produces p x ↔
      x ∈ Nat.rfindOpt fun n => (prefixAccepted c n).lookup p :=
  ofPrefixCode_produces_iff.trans <|
    (exists_congr fun _ => mem_prefixAccepted_iff_lookup.trans Option.mem_def.symm).trans
      (Nat.rfindOpt_mono fun hmn => lookup_prefixAccepted_mono hmn).symm

/-- Every `ofPrefixCode c` is partial recursive. -/
theorem isPartrec_ofPrefixCode (c : Code) : (ofPrefixCode c).IsPartrec :=
  ⟨fun p => Nat.rfindOpt fun n => (prefixAccepted c n).lookup p,
    partrec₂_ofPrefixCode_eval.comp (Computable.const c) Computable.id,
    fun _ _ => ofPrefixCode_produces_iff_mem_rfindOpt⟩

private theorem exists_produces_ofPrefixCode_of_exists {c : Code}
    (h : ∃ p x, (ofCode c).Produces p x) :
    ∃ p x, (ofPrefixCode c).Produces p x := by
  classical
  have hex : ∃ k, (prefixCand c k).isSome := by
    obtain ⟨p, x, hx⟩ := h
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp (ofCode_produces_iff.mp hx)
    exact ⟨encode (p, t), by simp [prefixCand, Option.mem_def.mp ht]⟩
  let k₀ := Nat.find hex
  obtain ⟨⟨p₀, x₀⟩, hcand⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  have hacc0 : prefixAccepted c k₀ = [] := by
    suffices ∀ m ≤ k₀, prefixAccepted c m = [] from this k₀ le_rfl
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      have hm_lt : m < k₀ := by omega
      simp [prefixAccepted, ih hm_lt.le, Option.not_isSome_iff_eq_none.mp (Nat.find_min hex hm_lt)]
  exact ⟨p₀, x₀, ofPrefixCode_produces_iff.mpr ⟨k₀ + 1, by
    rw [prefixAccepted, hacc0, hcand]
    exact .head []⟩⟩

/-! ### The universal prefix-free description method -/

/-- The *universal prefix-free* description method for natural numbers: `parseCodeHeader` strictly
parses a program into `codeHeader c ++ p`, and then runs `p` under `ofPrefixCode c`. -/
def universalPrefix : DescriptionMethod ℕ where
  run q := match parseCodeHeader q with
    | Option.none => Computation.empty ℕ
    | some (c, p) => (ofPrefixCode c).run p

@[simp]
theorem universalPrefix_run_codeHeader_append (c : Code) (p : List Bool) :
    universalPrefix.run (codeHeader c ++ p) = (ofPrefixCode c).run p := by
  simp [universalPrefix, parseCodeHeader_codeHeader_append]

theorem universalPrefix_produces_iff {q : List Bool} {x : ℕ} :
    universalPrefix.Produces q x ↔
      ∃ c p, parseCodeHeader q = some (c, p) ∧ (ofPrefixCode c).Produces p x := by
  simp only [Produces, universalPrefix]
  rcases parseCodeHeader q with _ | ⟨c, p⟩ <;> simp [Computation.notMem_empty]

theorem universalPrefix_produces_codeHeader_append {c : Code} {p : List Bool} {x : ℕ} :
    universalPrefix.Produces (codeHeader c ++ p) x ↔ (ofPrefixCode c).Produces p x := by
  rw [Produces, universalPrefix_run_codeHeader_append, Produces]

/-- `universalPrefix` is prefix-free. -/
theorem isPrefixFree_universalPrefix : universalPrefix.IsPrefixFree := by
  rintro q₁ ⟨x₁, h₁⟩ q₂ ⟨x₂, h₂⟩ hpref
  obtain ⟨c₁, p₁, hp₁, hprod₁⟩ := universalPrefix_produces_iff.mp h₁
  obtain ⟨c₂, p₂, hp₂, hprod₂⟩ := universalPrefix_produces_iff.mp h₂
  obtain ⟨rfl, hp'⟩ := prefix_of_parseCodeHeader_eq_some hp₁ hp₂ hpref
  rw [← parseCodeHeader_eq_some_iff.mp hp₁, ← parseCodeHeader_eq_some_iff.mp hp₂,
    isPrefixFree_ofPrefixCode c₁ p₁ ⟨x₁, hprod₁⟩ p₂ ⟨x₂, hprod₂⟩ hp']

/-- `universalPrefix` is partial recursive. -/
theorem isPartrec_universalPrefix : universalPrefix.IsPartrec := by
  let step : List Bool × ℕ → Option ℕ := fun qn =>
    (parseCodeHeader qn.1).bind fun cp => (prefixAccepted cp.1 qn.2).lookup cp.2
  have hstep : Primrec step :=
    Primrec.option_bind (primrec_parseCodeHeader.comp Primrec.fst)
      (primrec₂_prefixAccepted_lookup.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  refine ⟨fun q => Nat.rfindOpt fun n => step (q, n), Partrec.rfindOpt hstep.to_comp,
    fun q x => ?_⟩
  rw [universalPrefix_produces_iff]
  have hmono : ∀ {y m n : ℕ}, m ≤ n → y ∈ step (q, m) → y ∈ step (q, n) := by
    simp only [step, Option.mem_def, Option.bind_eq_some_iff]
    exact fun hmn ⟨cp, hcp, hlook⟩ => ⟨cp, hcp, lookup_prefixAccepted_mono hmn hlook⟩
  rw [Nat.rfindOpt_mono hmono]
  constructor
  · rintro ⟨c, p, hp, hprod⟩
    obtain ⟨n, hn⟩ := ofPrefixCode_produces_iff.mp hprod
    exact ⟨n, by simp [step, hp, mem_prefixAccepted_iff_lookup.mp hn]⟩
  · rintro ⟨n, hn⟩
    obtain ⟨⟨c, p⟩, hp, hlook⟩ := Option.bind_eq_some_iff.mp (Option.mem_def.mp hn)
    exact ⟨c, p, hp, ofPrefixCode_produces_iff.mpr ⟨n, mem_prefixAccepted_iff_lookup.mpr hlook⟩⟩

/-- **Prefix-free invariance theorem** [LiVitanyi2019]: `universalPrefix` is additively optimal
for the class of prefix-free partial recursive description methods of natural numbers. -/
theorem isAdditivelyOptimal_universalPrefix :
    universalPrefix.IsAdditivelyOptimal {M | M.IsPartrec ∧ M.IsPrefixFree} := by
  refine isAdditivelyOptimal_of_simulation ⟨isPartrec_universalPrefix, isPrefixFree_universalPrefix⟩
    fun M ⟨hpart, hpf⟩ => ?_
  obtain ⟨c, hc⟩ := IsPartrec.exists_produces_iff hpart
  have hcode_pf : (ofCode c).IsPrefixFree := fun p₁ ⟨x₁, h₁⟩ p₂ ⟨x₂, h₂⟩ =>
    hpf p₁ ⟨x₁, (hc p₁ x₁).mpr h₁⟩ p₂ ⟨x₂, (hc p₂ x₂).mpr h₂⟩
  exact ⟨(codeHeader c).length, exists_simulation_of_produces (codeHeader c ++ ·)
    (fun p => by rw [List.length_append, Nat.add_comm]) fun {p x} hx =>
      universalPrefix_produces_codeHeader_append.mpr
        ((ofPrefixCode_produces_iff_of_isPrefixFree hcode_pf).mpr ((hc p x).mp hx))⟩

/-- Every natural number has a finite complexity under `universalPrefix`. -/
theorem ecomplexity_universalPrefix_ne_top (x : ℕ) : universalPrefix.ecomplexity x ≠ ⊤ := by
  obtain ⟨p₀, y₀, hp₀⟩ := exists_produces_ofPrefixCode_of_exists (c := Code.const x)
    ⟨[], x, ofCode_produces_iff.mpr (by simp)⟩
  have hy₀ : y₀ = x := by
    simpa using ofCode_produces_iff.mp (ofCode_produces_of_ofPrefixCode_produces hp₀)
  exact ecomplexity_ne_top_iff.mpr
    ⟨codeHeader (Code.const x) ++ p₀, universalPrefix_produces_codeHeader_append.mpr (hy₀ ▸ hp₀)⟩

@[simp]
theorem natCast_complexity_universalPrefix (x : ℕ) :
    (universalPrefix.complexity x : ℕ∞) = universalPrefix.ecomplexity x :=
  natCast_complexity (ecomplexity_universalPrefix_ne_top x)

/-- There exists a code header of `universalPrefix` that is prefix-incomparable with every halting
program of `universalPrefix`, witnessing `haltingSet ≠ univ` and `Ω < 1`. -/
theorem universalPrefix_exists_incomparable_prefix :
    ∃ q : List Bool, ∀ r ∈ universalPrefix.haltingSet, ¬ (q <+: r) ∧ ¬ (r <+: q) := by
  let cLoop : Code := Code.rfind' Code.succ
  have hcLoop : ∀ n : ℕ, cLoop.eval n = Part.none := fun n =>
    Part.eq_none_iff.mpr fun y hy => by
      simp only [cLoop, Code.eval, Nat.unpaired, Part.mem_map_iff] at hy
      obtain ⟨k, hk, -⟩ := hy
      exact absurd (Nat.rfind_spec hk) (by simp)
  refine ⟨codeHeader cLoop, fun r ⟨x, hr⟩ => ?_⟩
  obtain ⟨c, p, hcp, hprod⟩ := universalPrefix_produces_iff.mp hr
  have hne : c ≠ cLoop := fun h => by
    have hev := ofCode_produces_iff.mp (ofCode_produces_of_ofPrefixCode_produces hprod)
    simp [h, hcLoop] at hev
  have hloop_hdr := parseCodeHeader_codeHeader_append cLoop []
  rw [List.append_nil] at hloop_hdr
  exact ⟨fun hp => hne (prefix_of_parseCodeHeader_eq_some hloop_hdr hcp hp).1.symm,
    fun hp => hne (prefix_of_parseCodeHeader_eq_some hcp hloop_hdr hp).1⟩

/-! ### Prefix-free minorization and binary strings -/

/-- The description method `U` *minorizes prefix-free partial recursive decoders*: for every
partial recursive `g : List Bool →. α` whose halting domain `{p | (g p).Dom}` is prefix-free,
there is a constant `c` with `K_U(x) ≤ |p| + c` whenever `x ∈ g p`. -/
@[expose]
def MinorizesPrefixPartrec {α : Type*} [Primcodable α] (U : DescriptionMethod α) : Prop :=
  ∀ g : List Bool →. α, Partrec g → InformationTheory.IsPrefixFree {p | (g p).Dom} →
    ∃ c : ℕ, ∀ p x, x ∈ g p → U.ecomplexity x ≤ p.length + c

theorem IsAdditivelyOptimal.minorizesPrefixPartrec {U : DescriptionMethod ℕ}
    (hU : U.IsAdditivelyOptimal {M | M.IsPartrec ∧ M.IsPrefixFree}) :
    U.MinorizesPrefixPartrec := by
  intro g hg hg_pf
  obtain ⟨c, hc⟩ := Code.exists_code.mp hg
  have hcode_pf : (ofCode c).IsPrefixFree := fun p₁ ⟨x₁, h₁⟩ p₂ ⟨x₂, h₂⟩ =>
    hg_pf p₁ (Part.dom_iff_mem.mpr ⟨x₁, by simpa [hc, encodek] using ofCode_produces_iff.mp h₁⟩)
      p₂ (Part.dom_iff_mem.mpr ⟨x₂, by simpa [hc, encodek] using ofCode_produces_iff.mp h₂⟩)
  obtain ⟨d, hd⟩ := hU.exists_ecomplexity_le (ofCode c) ⟨isPartrec_ofCode c, hcode_pf⟩
  exact ⟨d, fun p x hx => (hd x).trans (add_le_add_left (ecomplexity_le_length
    (ofCode_produces_iff.mpr (by simpa [hc, encodek] using hx))) d)⟩

/-- `universalPrefix` minorizes every prefix-free partial recursive decoder. -/
theorem minorizesPrefixPartrec_universalPrefix : universalPrefix.MinorizesPrefixPartrec :=
  isAdditivelyOptimal_universalPrefix.minorizesPrefixPartrec

/-- Pushing forward along `f` preserves prefix-free minorization when `f` has a computable
section `s`. -/
theorem MinorizesPrefixPartrec.map {α β : Type*} [Primcodable α] [Primcodable β]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) {f : α → β} {s : β → α}
    (hs : Computable s) (hfs : ∀ y, f (s y) = y) :
    (U.map f).MinorizesPrefixPartrec := by
  intro g hg hg_pf
  obtain ⟨c, hc⟩ := hU (fun p => (g p).map s) (hg.map (hs.comp Computable.snd).to₂)
    (by simpa using hg_pf)
  refine ⟨c, fun p y hy => ?_⟩
  calc (U.map f).ecomplexity y = (U.map f).ecomplexity (f (s y)) := by rw [hfs]
    _ ≤ U.ecomplexity (s y) := U.ecomplexity_map_le f (s y)
    _ ≤ p.length + c := hc p (s y) (Part.mem_map s hy)

/-- Prefix-free invariance for partial recursive decoders over any `Primcodable` type. -/
theorem MinorizesPrefixPartrec.exists_ecomplexity_le_of_partrec_eval {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) {M : DescriptionMethod α}
    (hM_pf : M.IsPrefixFree) {eval : List Bool →. α} (heval : Partrec eval)
    (hprod : ∀ p x, M.Produces p x ↔ x ∈ eval p) :
    ∃ c : ℕ, ∀ x : α, U.ecomplexity x ≤ M.ecomplexity x + c := by
  have hdom : InformationTheory.IsPrefixFree {p | (eval p).Dom} := fun p₁ h₁ p₂ h₂ hp =>
    let ⟨x₁, hx₁⟩ := Part.dom_iff_mem.mp h₁
    let ⟨x₂, hx₂⟩ := Part.dom_iff_mem.mp h₂
    hM_pf p₁ ⟨x₁, (hprod p₁ x₁).mpr hx₁⟩ p₂ ⟨x₂, (hprod p₂ x₂).mpr hx₂⟩ hp
  obtain ⟨c, hc⟩ := hU eval heval hdom
  refine ⟨c, fun x => ?_⟩
  by_cases h : M.ecomplexity x = ⊤
  · simp [h]
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity h
  rw [← hlen]
  exact hc p x ((hprod p x).mp hp)

/-- The universal prefix-free description method for binary strings: `universalPrefix`, read
through the decoding of `ℕ`. -/
@[expose] noncomputable def universalPrefixBits : DescriptionMethod (List Bool) :=
  universalPrefix.map fun n => (decode (α := List Bool) n).getD []

theorem isPrefixFree_universalPrefixBits : universalPrefixBits.IsPrefixFree :=
  isPrefixFree_universalPrefix.map _

@[simp]
theorem haltingSet_universalPrefixBits :
    universalPrefixBits.haltingSet = universalPrefix.haltingSet :=
  haltingSet_map _ _

theorem minorizesPrefixPartrec_universalPrefixBits : universalPrefixBits.MinorizesPrefixPartrec :=
  minorizesPrefixPartrec_universalPrefix.map Computable.encode fun y => by simp [encodek]

theorem ecomplexity_universalPrefixBits_ne_top (x : List Bool) :
    universalPrefixBits.ecomplexity x ≠ ⊤ :=
  ne_top_of_le_ne_top (ecomplexity_universalPrefix_ne_top (encode x)) (by
    simpa [universalPrefixBits, encodek] using
      universalPrefix.ecomplexity_map_le (fun n => (decode (α := List Bool) n).getD []) (encode x))

@[simp]
theorem natCast_complexity_universalPrefixBits (x : List Bool) :
    (universalPrefixBits.complexity x : ℕ∞) = universalPrefixBits.ecomplexity x :=
  natCast_complexity (ecomplexity_universalPrefixBits_ne_top x)

/-- **Prefix-free invariance theorem for binary strings**: `universalPrefixBits` is at most an
additive constant worse than every prefix-free description method of binary strings with a partial
recursive evaluator. -/
theorem exists_ecomplexity_universalPrefixBits_le_of_partrec_eval
    {M : DescriptionMethod (List Bool)} (hM_pf : M.IsPrefixFree)
    {eval : List Bool →. List Bool} (heval : Partrec eval)
    (hprod : ∀ p x, M.Produces p x ↔ x ∈ eval p) :
    ∃ c : ℕ, ∀ x : List Bool, universalPrefixBits.ecomplexity x ≤ M.ecomplexity x + c :=
  minorizesPrefixPartrec_universalPrefixBits.exists_ecomplexity_le_of_partrec_eval hM_pf heval hprod

private theorem mem_range_selfDelimitingCode_of_snd_nil {q : List Bool}
    (h : ∃ b, decodeSelfDelimiting? q = some (b, [])) : q ∈ Set.range selfDelimitingCode :=
  let ⟨b, hb⟩ := h
  ⟨b, by simpa using decodeSelfDelimiting?_eq_some_iff.mp hb⟩

/-- **Self-delimiting upper bound**: `K(x) ≤ |x| + 2 size |x| + O(1)` for every binary string. -/
theorem exists_ecomplexity_universalPrefixBits_le_selfDelimiting :
    ∃ c : ℕ, ∀ x : List Bool,
      universalPrefixBits.ecomplexity x ≤ (x.length + 2 * x.length.size + 1 + c : ℕ) := by
  let f : List Bool → Option (List Bool) := fun q =>
    (decodeSelfDelimiting? q).bind fun bp => if bp.2 = [] then some bp.1 else Option.none
  have hf : Primrec f :=
    Primrec.option_bind primrec_decodeSelfDelimiting? <| Primrec₂.mk <|
      Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
        (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const Option.none)
  have hg_pf : InformationTheory.IsPrefixFree {q | ((f q : Part (List Bool))).Dom} :=
    isPrefixFree_range_selfDelimitingCode.anti fun q hq => by
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hq
      obtain ⟨⟨b', p⟩, hd, hp⟩ := Option.bind_eq_some_iff.mp (Part.mem_ofOption.mp hb)
      split_ifs at hp with hp0
      exact mem_range_selfDelimitingCode_of_snd_nil ⟨b', hp0 ▸ hd⟩
  obtain ⟨c, hc⟩ :=
    minorizesPrefixPartrec_universalPrefixBits _ (Computable.ofOption hf.to_comp) hg_pf
  refine ⟨c, fun x => ?_⟩
  have hle := hc (selfDelimitingCode x) x (by simp [f])
  rw [length_selfDelimitingCode] at hle
  exact_mod_cast hle

/-! ### Uncomputability and Chaitin's incompleteness for prefix-free complexity -/

/-- **No computable unbounded lower bound on prefix-free complexity**: if `U` minorizes prefix-free
partial recursive decoders, no computable unbounded function `f : α → ℕ` satisfies `f x ≤ K_U(x)`
everywhere (Berry's paradox with self-delimiting programs). -/
theorem MinorizesPrefixPartrec.exists_ecomplexity_lt_of_computable {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) {f : α → ℕ} (hf : Computable f)
    (hunb : ∀ k, ∃ x, k ≤ f x) : ∃ x, U.ecomplexity x < f x := by
  by_contra! hle
  let validHeader : List Bool → Bool := fun r =>
    match decodeSelfDelimiting? r with
    | Option.none => false
    | some bp => decide (bp.2 = [])
  have hvalid : Primrec validHeader :=
    (Primrec.option_casesOn primrec_decodeSelfDelimiting? (Primrec.const false)
      ((Primrec.eq.decide.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])).to₂)).of_eq
      fun r => by cases hd : decodeSelfDelimiting? r <;> simp [validHeader, hd]
  let step : List Bool → ℕ → Option α := fun r n =>
    bif validHeader r then
      (decode (α := α) n).bind fun x => bif decide (2 * r.length ≤ f x) then some x else Option.none
    else Option.none
  have hstep : Computable₂ step := by
    have hcond : Computable fun rnx : (List Bool × ℕ) × α =>
        decide (2 * rnx.1.1.length ≤ f rnx.2) :=
      Primrec.nat_le.decide.to_comp.comp
        ((Primrec.nat_double.comp Primrec.list_length).to_comp.comp
          (Computable.fst.comp Computable.fst))
        (hf.comp Computable.snd)
    exact Computable.cond (hvalid.to_comp.comp Computable.fst)
      (Computable.option_bind (Computable.decode.comp Computable.snd)
        (Computable.cond hcond (Computable.option_some.comp Computable.snd)
          (Computable.const Option.none)))
      (Computable.const Option.none)
  let search : List Bool →. α := fun r => Nat.rfindOpt (step r)
  have hsearch_pf : InformationTheory.IsPrefixFree {r | (search r).Dom} :=
    isPrefixFree_range_selfDelimitingCode.anti fun r hr => by
      obtain ⟨n, x, hx⟩ := Nat.rfindOpt_dom.mp hr
      cases hv : validHeader r <;> simp only [step, hv, Bool.cond_false, Option.mem_def,
        reduceCtorEq] at hx
      cases hd : decodeSelfDelimiting? r with
      | none => simp [validHeader, hd] at hv
      | some bp =>
        simp only [validHeader, hd, decide_eq_true_eq] at hv
        exact mem_range_selfDelimitingCode_of_snd_nil ⟨bp.1, hv ▸ hd⟩
  obtain ⟨c, hc⟩ := hU search (Partrec.rfindOpt hstep) hsearch_pf
  let r : List Bool := selfDelimitingCode (List.replicate (c + 1) true)
  have hrlen : c + 1 ≤ r.length := by simp [r, length_selfDelimitingCode]
  have hr_valid : validHeader r = true := by simp [validHeader, r]
  obtain ⟨x, hx⟩ := hunb (2 * r.length)
  have hstep_mem : x ∈ step r (encode x) := by
    simp [step, hr_valid, encodek, hx]
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr ⟨encode x, x, hstep_mem⟩)
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hy
  obtain ⟨y', -, hcmp⟩ := Option.bind_eq_some_iff.mp (by simpa [step, hr_valid] using hn)
  split_ifs at hcmp with h2r
  obtain rfl := Option.some.inj hcmp
  have hcomp_nat : f y' ≤ r.length + c := by exact_mod_cast (hle y').trans (hc r y' hy)
  omega

/-- A minorizing prefix-free description method on an infinite type with finite complexities
cannot have a computable complexity function. -/
theorem MinorizesPrefixPartrec.not_computable_complexity {α : Type*} [Primcodable α] [Infinite α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec)
    (hfin : ∀ x, U.ecomplexity x ≠ ⊤) : ¬ Computable U.complexity := by
  intro hcomp
  obtain ⟨x, hx⟩ := hU.exists_ecomplexity_lt_of_computable hcomp fun k =>
    let ⟨x, hx⟩ := (U.eventually_natCast_le_ecomplexity k).exists
    ⟨x, Nat.cast_le.mp (hx.trans_eq (natCast_complexity (hfin x)).symm)⟩
  exact lt_irrefl _ (hx.trans_eq (natCast_complexity (hfin x)))

/-- **The prefix-free Kolmogorov complexity of natural numbers is not computable.** -/
theorem not_computable_complexity_universalPrefix : ¬ Computable universalPrefix.complexity :=
  minorizesPrefixPartrec_universalPrefix.not_computable_complexity
    ecomplexity_universalPrefix_ne_top

/-- **The prefix-free Kolmogorov complexity of binary strings is not computable.** -/
theorem not_computable_complexity_universalPrefixBits :
    ¬ Computable universalPrefixBits.complexity :=
  minorizesPrefixPartrec_universalPrefixBits.not_computable_complexity
    ecomplexity_universalPrefixBits_ne_top

/-- **Chaitin's incompleteness theorem for prefix-free complexity**, quantitative form for theories
[Chaitin1974], [LiVitanyi2019]: a sound r.e. theory semi-decided by `e` proves `n ≤ K_U(x)` only
for `n ≤ K(encode e) + c`, where `K` is the prefix-free complexity under `universalPrefix`. -/
theorem MinorizesPrefixPartrec.exists_forall_le_complexity_universalPrefix_add_of_read
    {α σ : Type*} [Primcodable α] [Primcodable σ]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec)
    {read : σ → Option (α × ℕ)} (hread : Computable read) :
    ∃ c : ℕ, ∀ (e : Code) (T : σ → Prop), (∀ t, T t ↔ (e.eval (encode t)).Dom) →
      (∀ t, T t → ∀ x n, read t = some (x, n) → (n : ℕ∞) ≤ U.ecomplexity x) →
      ∀ t, T t → ∀ x n, read t = some (x, n) → n ≤ universalPrefix.complexity (encode e) + c := by
  obtain ⟨f, hf, hfU⟩ := isPartrec_universalPrefix
  have hD := partrec_chaitinBerryDecoder hread hf
  set B : List Bool → ℕ := fun p => p.length + p.idxOf false
  set D : List Bool →. α := fun p => (f (p.drop (p.idxOf false + 1))).bind fun m =>
    Nat.rfindOpt (chaitinSearch read m (B p))
  have hD_pf : InformationTheory.IsPrefixFree {p | (D p).Dom} := by
    have hdom : ∀ {p}, (D p).Dom →
        false ∈ p ∧ p.drop (p.idxOf false + 1) ∈ universalPrefix.haltingSet := by
      intro p hp
      obtain ⟨_, hm⟩ := Part.dom_iff_mem.mp hp
      obtain ⟨m, hm', _⟩ := Part.mem_bind_iff.mp hm
      have hprod := (hfU _ m).mpr hm'
      refine ⟨by_contra fun hnot => ?_, m, hprod⟩
      rw [List.idxOf_of_notMem hnot, List.drop_of_length_le (Nat.le_succ _)] at hprod
      obtain ⟨c, p', hparse, _⟩ := universalPrefix_produces_iff.mp hprod
      simp [parseCodeHeader, decodeSelfDelimiting?] at hparse
    rintro p₁ h₁ _ h₂ ⟨t, rfl⟩
    obtain ⟨hf₁, hr₁⟩ := hdom h₁
    obtain ⟨-, hr₂⟩ := hdom h₂
    have hlt₁ : p₁.idxOf false + 1 ≤ p₁.length := List.idxOf_lt_length_iff.mpr hf₁
    have hdrop : (p₁ ++ t).drop ((p₁ ++ t).idxOf false + 1) =
        p₁.drop (p₁.idxOf false + 1) ++ t := by
      rw [List.idxOf_append_of_mem hf₁, List.drop_append_of_le_length hlt₁]
    have hdrop_eq := isPrefixFree_universalPrefix _ hr₁ _ hr₂ (hdrop ▸ List.prefix_append _ _)
    rw [hdrop] at hdrop_eq
    simp [List.self_eq_append_right.mp hdrop_eq]
  obtain ⟨k, hk⟩ := hU D hD hD_pf
  refine ⟨2 * k + 1, fun e T hT hsound t ht x n hxn => ?_⟩
  obtain ⟨r, hr, hrlen⟩ :=
    exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top (encode e))
  rw [← natCast_complexity_universalPrefix, Nat.cast_inj] at hrlen
  exact hrlen ▸ chaitin_berry_bound hk hT hsound ((hfU r (encode e)).mp hr) ht hxn

/-- **Chaitin's incompleteness theorem for prefix-free complexity**, quantitative form
[Chaitin1974], [LiVitanyi2019]: every sound code `e` semi-deciding pairs `(x, n)` with
`n ≤ K_U(x)` satisfies `n ≤ K(encode e) + c`. -/
theorem MinorizesPrefixPartrec.exists_forall_le_complexity_universalPrefix_add
    {α : Type*} [Primcodable α] {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) :
    ∃ c : ℕ, ∀ (e : Code) (S : Set (α × ℕ)), (∀ xn, xn ∈ S ↔ (e.eval (encode xn)).Dom) →
      (∀ x n, (x, n) ∈ S → (n : ℕ∞) ≤ U.ecomplexity x) →
      ∀ x n, (x, n) ∈ S → n ≤ universalPrefix.complexity (encode e) + c := by
  obtain ⟨c, hc⟩ :=
    hU.exists_forall_le_complexity_universalPrefix_add_of_read (σ := α × ℕ) Computable.option_some
  exact ⟨c, fun e S hS hsound x n hxn => hc e (· ∈ S) hS
    (fun t ht x n h => by cases Option.some.inj h; exact hsound _ _ ht) (x, n) hxn x n rfl⟩

/-- **Chaitin's incompleteness theorem for prefix-free complexity**: a sound r.e. theory proves
`n ≤ K_U(x)` only for boundedly many `n`. -/
theorem MinorizesPrefixPartrec.exists_forall_le_of_rePred_of_read
    {α σ : Type*} [Primcodable α] [Primcodable σ]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec)
    {read : σ → Option (α × ℕ)} (hread : Computable read) {T : σ → Prop} (hT : REPred T)
    (hsound : ∀ t, T t → ∀ x n, read t = some (x, n) → (n : ℕ∞) ≤ U.ecomplexity x) :
    ∃ c : ℕ, ∀ t, T t → ∀ x n, read t = some (x, n) → n ≤ c := by
  obtain ⟨c, hc⟩ := hU.exists_forall_le_complexity_universalPrefix_add_of_read hread
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp hT
  exact ⟨_, hc e T he hsound⟩

/-- **Chaitin's incompleteness theorem for prefix-free complexity**: an r.e. set of pairs
`(x, n)` with `n ≤ K_U(x)` for every member has bounded `n`. -/
theorem MinorizesPrefixPartrec.exists_forall_le_of_rePred {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) {S : Set (α × ℕ)}
    (hS : REPred (· ∈ S)) (hsound : ∀ x n, (x, n) ∈ S → (n : ℕ∞) ≤ U.ecomplexity x) :
    ∃ c : ℕ, ∀ x n, (x, n) ∈ S → n ≤ c := by
  obtain ⟨c, hc⟩ := hU.exists_forall_le_complexity_universalPrefix_add
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp hS
  exact ⟨_, hc e S he hsound⟩

end DescriptionMethod

end Cslib.Kolmogorov
