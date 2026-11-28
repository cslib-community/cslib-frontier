/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformExtend
import all CslibFrontier.Crypto.Primitives.ByteString

/-!
# Finite random XOFs shared by the ML-DSA algorithms and quantum queries

A coherent address encodes the SHAKE variant, a delimiter and the input bits. A random
table supplies independent bytes on the encoded words and a fixed background supplies the
remaining inputs and suffixes. The byte-table factorization is used for both the SHAKE128
public matrix and the SHAKE256 signing masks.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability ExtendableOutput

namespace Xofs

/-- Encode a raw word of at most `a` bits in the coherent address register. The first bit
selects SHAKE256 when set and SHAKE128 otherwise. Leading zero padding and a one-bit delimiter
preserve the input length, including empty inputs and inputs starting with zero. -/
def queryAddress (a : ℕ) (strength : Bool) (x : List Bool) (_ : x.length ≤ a) :
    BitString (a + 2) :=
  Fin.cons strength (BitString.ofList (a + 1) (List.replicate (a - x.length) false ++ true :: x))

private def unpad : List Bool → Option (List Bool)
  | [] => none
  | true :: x => some x
  | false :: x => unpad x

/-- Decode a measured SHAKE256 address. A missing address, SHAKE128 tag or missing delimiter
has no SHAKE256 input. -/
def shake256QueryInput {a : ℕ} (addr : Option (BitString (a + 2))) : Option (List Bool) :=
  addr.bind fun v => if v 0 then unpad (List.ofFn fun i : Fin (a + 1) => v i.succ) else none

private theorem unpad_word (k : ℕ) (x : List Bool) :
    unpad (List.replicate k false ++ true :: x) = some x := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.cons_append, unpad] using ih

/-- The XOR oracle's output bits in FIPS 202 least-significant-bit-first order.
An address without a delimiter has the all-zero response. -/
def queryTable (H : Xofs) (a bytes : ℕ) (address : BitString (a + 2)) : BitString (8 * bytes) :=
  match unpad (List.ofFn (fun i : Fin (a + 1) => address i.succ)) with
  | none => 0
  | some x => BitString.ofList (8 * bytes)
      (Keccak.bytesToBitsLE ((if address 0 then H.h256 else H.h128).read x bytes))

/-- When the SHAKE128 streams agree, unequal coherent responses identify a successfully
decoded SHAKE256 address whose two raw byte reads differ. -/
theorem shake256QueryInput_of_queryTable_ne {a b : ℕ} {H G : Xofs} (h128 : H.h128 = G.h128)
    {addr : Option (BitString (a + 2))}
    (hit : addr.any (fun v => decide (H.queryTable a b v ≠ G.queryTable a b v)) = true) :
    ∃ raw, shake256QueryInput addr = some raw ∧ H.h256.read raw b ≠ G.h256.read raw b := by
  obtain _ | v := addr
  · contradiction
  change decide (_ ≠ _) = true at hit
  replace hit := of_decide_eq_true hit
  simp only [queryTable] at hit
  cases h : unpad (List.ofFn fun i : Fin (a + 1) => v i.succ) with
  | none => exact (hit (by rw [h])).elim
  | some raw =>
    rw [h] at hit
    cases tag : v 0 with
    | false => exact (hit (by simp only [tag, Bool.false_eq_true, ↓reduceIte, h128])).elim
    | true =>
      exact ⟨raw, by simp only [shake256QueryInput, Option.bind_some, tag, ↓reduceIte, h],
        fun eq => hit (by simp only [tag, ↓reduceIte, eq])⟩

/-- A coherent query at each encodable raw word reads the very stream used by FIPS, at
the full device response length. Shorter reads use its prefix. -/
theorem queryTable_queryAddress (H : Xofs) (a bytes : ℕ) (strength : Bool) (x : List Bool)
    (hx : x.length ≤ a) :
    List.ofFn (H.queryTable a bytes (queryAddress a strength x hx)) =
      Keccak.bytesToBitsLE ((if strength then H.h256 else H.h128).read x bytes) := by
  have len : (List.replicate (a - x.length) false ++ true :: x).length = a + 1 := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    lia
  simp only [queryTable, queryAddress, Fin.cons_succ, BitString.ofFn_ofList len, unpad_word,
    Fin.cons_zero]
  apply BitString.ofFn_ofList
  let stream := if strength then H.h256 else H.h128
  change (Keccak.bytesToBitsLE (stream.read x bytes)).length = 8 * bytes
  rw [Keccak.length_bytesToBitsLE, stream.length_read]

/-- Sample one finite prefix table for both raw XOFs before the execution. Each raw input of
at most `a` bits receives `bytes` independent uniform bytes for each SHAKE variant. The
background supplies longer inputs and bytes beyond these prefixes. -/
noncomputable def uniformPrefixes (background : Xofs) (a bytes : ℕ) : PMF Xofs :=
  (PMF.uniformOfFintype (BitString (a + 2) → FixedBytes bytes)).map fun T =>
    let row (strength : Bool) (x : List Bool) :=
      if h : x.length ≤ a then some ((T (queryAddress a strength x h)).toList) else none
    ⟨background.h128.withPrefixes (row false), background.h256.withPrefixes (row true)⟩

end Xofs

private abbrev RawWord (a : ℕ) := (n : Fin (a + 1)) × BitString n.val

private def word {a : ℕ} (x : List Bool) (h : x.length ≤ a) : RawWord a :=
  ⟨⟨x.length, by lia⟩, BitString.ofList x.length x⟩

private abbrev Table (a b : ℕ) := RawWord a × Fin b → Byte

private def install {a b : ℕ} (base : ExtendableOutput) (t : Table a b) : ExtendableOutput :=
  base.withPrefixes fun x => if h : x.length ≤ a then
    some (List.ofFn (fun i => t (word x h, i))) else none

private theorem word_inj {a : ℕ} {x y : List Bool} {hx : x.length ≤ a} {hy : y.length ≤ a}
    (h : word x hx = word y hy) : x = y := by
  simpa only [word, BitString.ofFn_ofList rfl] using
    congrArg (fun w : RawWord a => List.ofFn w.2) h

private def rows (a b : ℕ) : (Table a b × Table a b) ≃ (Bool × RawWord a → FixedBytes b) where
  toFun t w i := if w.1 then t.1 (w.2, i) else t.2 (w.2, i)
  invFun f := (fun p => f (true, p.1) p.2, fun p => f (false, p.1) p.2)
  left_inv _ := rfl
  right_inv f := by funext ⟨tag, w⟩; cases tag <;> rfl

private def addressOf (a : ℕ) (w : Bool × RawWord a) : BitString (a + 2) :=
  Xofs.queryAddress a w.1 (List.ofFn w.2.2) (by
    rw [List.length_ofFn]
    exact Nat.le_of_lt_succ w.2.1.isLt)

private theorem addressOf_word {a : ℕ} (tag : Bool) (x : List Bool) (hx : x.length ≤ a) :
    addressOf a (tag, word x hx) = Xofs.queryAddress a tag x hx := by
  unfold addressOf Xofs.queryAddress word
  simp only [BitString.ofFn_ofList rfl]

private theorem addressOf_injective (a : ℕ) : Function.Injective (addressOf a) := by
  rintro ⟨t, ⟨⟨n, hn⟩, x⟩⟩ ⟨u, ⟨⟨m, hm⟩, y⟩⟩ h
  have ht : t = u := congrFun h 0
  subst u
  let decode (v : BitString (a + 2)) := Xofs.unpad (List.ofFn fun i : Fin (a + 1) => v i.succ)
  have dec (w : RawWord a) : decode (addressOf a (t, w)) = some (List.ofFn w.2) := by
    have len : (List.replicate (a - (List.ofFn w.2).length) false ++ true :: List.ofFn w.2).length
        = a + 1 := by
      simp only [List.length_append, List.length_replicate, List.length_cons, List.length_ofFn]
      have := w.1.isLt
      lia
    simp only [decode, addressOf, Xofs.queryAddress, Fin.cons_succ, BitString.ofFn_ofList len,
      Xofs.unpad_word]
  have he := congrArg decode h
  rw [dec, dec] at he
  have words : List.ofFn x = List.ofFn y := Option.some.inj he
  have sizes : n = m := by simpa only [List.length_ofFn] using congrArg List.length words
  subst m
  obtain rfl := List.ofFn_inj.mp words
  rfl

/-- The literal table used by the coherent device restricts to independent byte tables on
the valid raw words for SHAKE128 and SHAKE256. Unused delimiter encodings disappear by
restriction along an injection. -/
private theorem independent_tables (base : Xofs) (a b : ℕ) :
    base.uniformPrefixes a b = (PMF.uniformOfFintype (Table a b)).bind fun t₂ =>
      (PMF.uniformOfFintype (Table a b)).map fun t₁ =>
        ⟨install base.h128 t₁, install base.h256 t₂⟩ := by
  let E : Bool × RawWord a ↪ BitString (a + 2) := ⟨addressOf a, addressOf_injective a⟩
  let fromRows (T : Bool × RawWord a → FixedBytes b) : Xofs :=
    ⟨install base.h128 (fun (w, i) => T (false, w) i),
      install base.h256 (fun (w, i) => T (true, w) i)⟩
  have restricted := PMF.uniformOfFintype_pi_map_comp_embedding (α := FixedBytes b) E
  have eq := congrArg (PMF.map fromRows) restricted
  rw [← PMF.uniformOfFintype_map_equiv (rows a b)] at eq
  rw [PMF.map_comp, PMF.map_comp] at eq
  rw [PMF.uniformOfFintype_bind_map]
  refine Eq.trans ?_ eq
  unfold Xofs.uniformPrefixes
  congr 1
  funext T
  simp only [fromRows, install, Function.comp_def, E, Function.Embedding.coeFn_mk,
    addressOf_word, FixedBytes.toList]

private theorem byteAt_install {a b : ℕ} (base : ExtendableOutput) (t : Table a b)
    (x : List Bool) (i : ℕ) :
    byteAt (install base t) x i =
      if h : x.length ≤ a ∧ i < b then t (word x h.1, ⟨i, h.2⟩) else byteAt base x i := by
  unfold install
  rw [byteAt_withPrefixes]
  by_cases hx : x.length ≤ a <;> by_cases hi : i < b <;>
    simp [hx, hi]

/-- Replace the prefix bytes at every `n`-bit SHAKE256 input with the supplied byte list,
retaining longer suffixes, other input lengths and SHAKE128. -/
@[expose] def Xofs.withPrefixLists (H : Xofs) (n : ℕ)
    (R : BitString n → List Byte) : Xofs :=
  { H with h256 := H.h256.withPrefixes fun x =>
      if x.length = n then some (R (BitString.ofList _ x)) else none }

/-- Replace the first `k` bytes at every `n`-bit SHAKE256 input using little-endian register
words, retaining the other bytes and SHAKE128. -/
@[expose] def Xofs.withPrefixRegister (H : Xofs) (n k : ℕ)
    (D : BitString n → BitString (8 * k)) : Xofs :=
  H.withPrefixLists n fun x => ((Keccak.fixedBytesEquivBitsLE k).symm (D x)).toList

/-- Installing `k`-byte rows directly as lists agrees with installing their little-endian
bit-string encodings. -/
theorem Xofs.withPrefixLists_toList (H : Xofs) (n k : ℕ)
    (R : BitString n → FixedBytes k) :
    H.withPrefixLists n (fun x => (R x).toList) =
      H.withPrefixRegister n k (fun x => Keccak.fixedBytesEquivBitsLE k (R x)) := by
  simp only [Xofs.withPrefixRegister, Equiv.symm_apply_apply]

/-- Read the first `k` SHAKE256 bytes on every `n`-bit input as little-endian bit strings. -/
def Xofs.readPrefixRegister (H : Xofs) (n k : ℕ) (x : BitString n) :
    BitString (8 * k) :=
  Keccak.fixedBytesEquivBitsLE _ (fun j => H.h256.byteAt (List.ofFn x) j)

/-- Reading all `k`-byte prefixes at `n`-bit inputs from the current streams and reinstalling
them preserves every raw query, including SHAKE256 output beyond the prefix. -/
theorem Xofs.withPrefixRegister_readPrefixRegister (H : Xofs) (n k : ℕ) :
    H.withPrefixRegister n k (H.readPrefixRegister n k) = H := by
  cases H with
  | mk h128 h256 =>
    unfold Xofs.withPrefixRegister Xofs.withPrefixLists
    congr 1
    apply ExtendableOutput.ext_byteAt
    intro x i
    by_cases len : x.length = n
    · by_cases small : i < k <;>
        simp [Xofs.readPrefixRegister, ExtendableOutput.byteAt_withPrefixes, len,
          FixedBytes.toList, small, BitString.ofFn_ofList len]
    · simp [ExtendableOutput.byteAt_withPrefixes, len]

private def prefixCells {a b : ℕ} (n k : ℕ) (ha : n ≤ a)
    (hb : k ≤ b) : BitString n × Fin k ↪
      RawWord a × Fin b :=
  (show BitString n ↪ RawWord a from
    ⟨fun x => word (List.ofFn x) (List.length_ofFn.le.trans ha), fun _ _ h =>
      List.ofFn_inj.mp (word_inj h)⟩).prodMap (Fin.castLEEmb hb)

private abbrev flatten (n k : ℕ) :=
  ((Equiv.refl (BitString n)).arrowCongr
    (Keccak.fixedBytesEquivBitsLE k).symm).trans (Equiv.curry _ _ Byte).symm

private theorem overwrite {a b : ℕ} (n k : ℕ) (ha : n ≤ a)
    (hb : k ≤ b) (H : ExtendableOutput) (t : Table a b)
    (D : BitString n → BitString (8 * k)) :
    (install H t).withPrefixes (fun x =>
      if x.length = n then
        some (((Keccak.fixedBytesEquivBitsLE _).symm (D (BitString.ofList _ x))).toList)
      else none) =
      install H (Function.extend (prefixCells n k ha hb) (flatten n k D) t) := by
  apply ExtendableOutput.ext_byteAt
  intro x j
  rw [ExtendableOutput.byteAt_withPrefixes, byteAt_install, byteAt_install]
  by_cases hx : x.length = n ∧ j < k
  · obtain ⟨len, small⟩ := hx
    let v := BitString.ofList n x
    let p := (v, (⟨j, small⟩ : Fin k))
    have atCell : prefixCells n k ha hb p =
        (word x (len.le.trans ha), ⟨j, small.trans_le hb⟩) := by
      refine Prod.ext ?_ rfl
      change word (List.ofFn (BitString.ofList n x))
        (List.length_ofFn.le.trans ha) = word x (len.le.trans ha)
      simp only [BitString.ofFn_ofList len]
    simp only [len, small, ↓reduceIte, Option.bind_some, FixedBytes.toList, List.getElem?_ofFn,
      ↓reduceDIte, Option.getD_some, ha, small.trans_le hb, and_self]
    rw [← atCell, (prefixCells n k ha hb).injective.extend_apply]
    rfl
  · have miss {fit : x.length ≤ a} {idx : j < b} :
        ¬ ∃ p, prefixCells n k ha hb p = (word x fit, ⟨j, idx⟩) := by
      rintro ⟨⟨r, k⟩, h⟩
      have eq : List.ofFn r = x := word_inj (hx := List.length_ofFn.le.trans ha) (hy := fit)
        (congrArg Prod.fst h)
      have off : k.val = j := congrArg (fun z => z.2.val) h
      exact hx ⟨eq ▸ List.length_ofFn, off ▸ k.isLt⟩
    have off : ((if x.length = n then
        some (((Keccak.fixedBytesEquivBitsLE _).symm (D (BitString.ofList _ x))).toList)
      else none).bind (fun r => r[j]?)) = none := by
      split_ifs with len
      · have far : ¬ j < k := fun small => hx ⟨len, small⟩
        simp [FixedBytes.toList, far]
      · rfl
    rw [off, Option.getD_none]
    split
    · exact (Function.extend_apply' _ _ _ miss).symm
    · rfl

/-- Independently replacing the first `k` SHAKE256 bytes at every `n`-bit input preserves the
joint law of the replacement register and both full raw XOFs. The finite prefix limits must
cover these inputs and outputs. -/
theorem Xofs.uniformPrefixes_prefixRegister (base : Xofs) (n k : ℕ) {a b : ℕ}
    (ha : n ≤ a) (hb : k ≤ b) :
    ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (BitString n → BitString (8 * k))).map
        fun D => (D, H.withPrefixRegister n k D)) =
      (base.uniformPrefixes a b).map fun H => (H.readPrefixRegister n k, H) := by
  let e := prefixCells n k ha hb
  let close (u t : Table a b) :=
    ((fun x => Keccak.fixedBytesEquivBitsLE k (fun i => t (e (x, i)))),
      (⟨install base.h128 u, install base.h256 t⟩ : Xofs))
  have read (u t : Table a b) :
      close u t = ((⟨install base.h128 u, install base.h256 t⟩ : Xofs).readPrefixRegister n k,
        ⟨install base.h128 u, install base.h256 t⟩) :=
    Prod.ext (funext fun x => congrArg (Keccak.fixedBytesEquivBitsLE _) (funext fun i => by
      simp only [byteAt_install, List.length_ofFn, ha, i.isLt.trans_le hb, and_self, ↓reduceDIte]
      rfl)) rfl
  have restore (u t : Table a b) (D : BitString n → _) :
      close u (Function.extend e (flatten n k D) t) =
        (D, (⟨install base.h128 u, install base.h256 t⟩ : Xofs).withPrefixRegister n k D) := by
    apply Prod.ext
    · funext x
      dsimp only [close]
      simp only [e.injective.extend_apply]
      exact (Keccak.fixedBytesEquivBitsLE _).apply_symm_apply (D x)
    · exact congrArg (Xofs.mk (install base.h128 u) ·) (overwrite n k ha hb _ _ D).symm
  rw [independent_tables]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs => simp only [← PMF.bind_pure_comp]; rw [PMF.bind_comm]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Table a b)) ·)
  funext u
  have law := PMF.uniformOfFintype_bind_bind_extend (κ := Byte) e (fun t => PMF.pure (close u t))
  rw [← PMF.uniformOfFintype_map_equiv (flatten n k)] at law
  simp only [PMF.bind_map, Function.comp_def, restore] at law
  simpa only [← PMF.bind_pure_comp, Function.comp_def, read] using law

/-- Decode the raw input wires for a fixed-length SHAKE256 prefix lookup. A malformed
address selects zero, and the native raw response ignores the selected word there. -/
def Xofs.prefixLookup (n : ℕ) {a : ℕ} (x : BitString (a + 2)) : BitString n :=
  match Xofs.unpad (List.ofFn fun i : Fin (a + 1) => x i.succ) with
  | none => 0
  | some word => BitString.ofList _ word

/-- A native raw query to an installed byte-list prefix table reads at most one entry. The
equality also covers SHAKE128, malformed words and requests extending beyond the installed
prefix. -/
theorem Xofs.queryTable_withPrefixLists (H : Xofs) (n a b : ℕ)
    (R : BitString n → List Byte) :
    (H.withPrefixLists n R).queryTable a b = fun x =>
      (H.withPrefixLists n fun _ => R (Xofs.prefixLookup n x)).queryTable a b x := by
  funext x
  unfold Xofs.queryTable Xofs.prefixLookup
  split
  · rfl
  · rename_i word _
    cases tag : x 0 <;> by_cases h : word.length = n <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte, Xofs.withPrefixLists,
        ExtendableOutput.withPrefixes]

/-- A native raw query to the installed table reads at most one register value. The equality
also covers SHAKE128, malformed words and requests extending beyond the installed prefix. -/
theorem Xofs.queryTable_withPrefixRegister (H : Xofs) (n k a b : ℕ)
    (D : BitString n → BitString (8 * k)) :
    (H.withPrefixRegister n k D).queryTable a b = fun x =>
      (H.withPrefixRegister n k fun _ => D (Xofs.prefixLookup n x)).queryTable a b x :=
  H.queryTable_withPrefixLists n a b fun x => ((Keccak.fixedBytesEquivBitsLE k).symm (D x)).toList

end Cslib.Crypto.MLDSA.FIPS204
