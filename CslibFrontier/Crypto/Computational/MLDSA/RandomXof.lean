/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Probability.PMF.Uniform
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

end Cslib.Crypto.MLDSA.FIPS204
