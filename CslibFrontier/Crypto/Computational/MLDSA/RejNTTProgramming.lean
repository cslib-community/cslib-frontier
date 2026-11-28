/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import CslibFrontier.Probability.PMF.Uniform

/-!
# Programming the byte stream of RejNTTPoly

For the bounded matrix sampler in [FIPS 204][NISTFIPS204], Algorithms 14 and 30,
interchange the first accepted coefficients with an external polynomial. The transformation
retains the ignored high bits, rejected triples and remaining bytes of the XOF prefix.
Applying it twice recovers the entire original input, including when the sampler exhausts its
prefix. This gives an exact coupling on the joint space of raw bytes and NTT coefficients.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

private abbrev F := ZMod 8380417

private def lowByte (x : F) : Byte := Fin.ofNat 256 x.val

private def midByte (x : F) : Byte := Fin.ofNat 256 (x.val / 256)

private def highByte (x : F) (c : Byte) : Byte :=
  Fin.ofNat 256 (x.val / 65536 + 128 * (c.val / 128))

private theorem candidate_encode (x : F) (c : Byte) :
    nttCandidate (lowByte x) (midByte x) (highByte x c) = x.val := by
  have hx := x.val_lt
  have hc := c.isLt
  simp only [nttCandidate, lowByte, midByte, highByte, Fin.val_ofNat]; omega

private theorem encode_candidate (a b c : Byte) (x : F) (h : nttCandidate a b c < 8380417) :
    lowByte (nttCandidate a b c : F) = a ∧ midByte (nttCandidate a b c : F) = b ∧
      highByte (nttCandidate a b c : F) (highByte x c) = c := by
  have hv : (nttCandidate a b c : F).val = nttCandidate a b c := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hx := x.val_lt
  simp only [lowByte, midByte, highByte, Fin.ext_iff, Fin.val_ofNat, hv]
  unfold nttCandidate at *
  omega

private def exchange : List Byte → List F → List Byte × List F
  | a :: b :: c :: rest, v :: vs =>
    if nttCandidate a b c < 8380417 then
      let p := exchange rest vs
      (lowByte v :: midByte v :: highByte v c :: p.1, (nttCandidate a b c : F) :: p.2)
    else
      let p := exchange rest (v :: vs)
      (a :: b :: c :: p.1, p.2)
  | bytes, [] => (bytes, [])
  | [], target => ([], target)
  | [a], target => ([a], target)
  | [a, b], target => ([a, b], target)

private theorem exchange_lengths (bytes : List Byte) (target : List F) :
    (exchange bytes target).1.length = bytes.length ∧
    (exchange bytes target).2.length = target.length := by
  fun_induction exchange bytes target <;> simp_all +zetaDelta

private theorem exchange_exchange (bytes : List Byte) (target : List F) :
    exchange (exchange bytes target).1 (exchange bytes target).2 = (bytes, target) := by
  fun_induction exchange bytes target with
  | case1 a b c rest v vs h p ih =>
    obtain ⟨ha, hb, hc⟩ := encode_candidate a b c v h
    simp [p, exchange, candidate_encode, ZMod.val_lt, ih, ha, hb, hc]
  | case2 a b c rest v vs h p ih =>
    have hlen := (exchange_lengths rest (v :: vs)).2
    cases he : (exchange rest (v :: vs)).2 with
    | nil => simp [he] at hlen
    | cons w ws => simp [p, exchange, h, ← he, ih]
  | case3 | case4 | case5 | case6 => simp [exchange]

private theorem exchange_coefficients (bytes : List Byte) (target : List F) :
    let original := rejNTTCoefficients bytes
    rejNTTCoefficients (exchange bytes target).1 =
      target.take original.length ++ original.drop target.length ∧
    (exchange bytes target).2 = original.take target.length ++ target.drop original.length := by
  fun_induction exchange bytes target with
  | case1 a b c rest v vs h p ih =>
    simpa [p, rejNTTCoefficients, h, candidate_encode, ZMod.val_lt] using ih
  | case2 a b c rest v vs h p ih =>
    simpa [p, rejNTTCoefficients, h] using ih
  | case3 | case4 | case5 | case6 => simp [rejNTTCoefficients]

private def readFixed {α : Type*} {n : ℕ} (xs : List α) (h : xs.length = n) :
    Fin n → α := fun i => xs[i.val]'(h ▸ i.isLt)

private theorem ofFn_readFixed {α : Type*} {n : ℕ} (xs : List α) (h : xs.length = n) :
    List.ofFn (readFixed xs h) = xs := by
  subst n
  exact List.ofFn_getElem

private def exchangeFixed {n : ℕ} (z : FixedBytes n × Poly) : FixedBytes n × Poly :=
  let p := exchange (List.ofFn z.1) (List.ofFn z.2)
  have h := exchange_lengths (List.ofFn z.1) (List.ofFn z.2)
  (readFixed p.1 (h.1.trans List.length_ofFn),
    readFixed p.2 (h.2.trans List.length_ofFn))

private theorem lists_exchangeFixed {n : ℕ} (z : FixedBytes n × Poly) :
    List.ofFn (exchangeFixed z).1 = (exchange (List.ofFn z.1) (List.ofFn z.2)).1 ∧
    List.ofFn (exchangeFixed z).2 = (exchange (List.ofFn z.1) (List.ofFn z.2)).2 := by
  simp only [exchangeFixed, ofFn_readFixed, and_self]

/-- Interchange the first 256 accepted coefficients of a finite SHAKE128 byte prefix with a
polynomial in NTT order. On exhaustion the exchange stops at the last accepted coefficient. -/
def exchangeRejNTT (n : ℕ) : Equiv.Perm (FixedBytes n × Poly) :=
  let inv : Function.Involutive (exchangeFixed (n := n)) := by
    intro z
    have he := lists_exchangeFixed (exchangeFixed z)
    have he' := lists_exchangeFixed z
    rw [he'.1, he'.2, exchange_exchange] at he
    dsimp only at he
    apply Prod.ext
    · apply List.ofFn_injective
      exact he.1
    · apply List.ofFn_injective
      exact he.2
  ⟨exchangeFixed, exchangeFixed, inv, inv⟩

/-- Two forward exchanges restore the complete byte row and supplied polynomial, also
when too few coefficients were accepted. -/
theorem exchangeRejNTT_involutive (n : ℕ) : Function.Involutive (exchangeRejNTT n) :=
  (exchangeRejNTT n).left_inv

/-- When Algorithm 30 succeeds, the programmed bytes decode to the supplied polynomial and the
exchange returns the original polynomial. -/
theorem exchangeRejNTT_of_some {n : ℕ} {bytes : FixedBytes n} {u : Poly}
    (h : rejNTTPoly (List.ofFn bytes) = some u) (v : Poly) :
    let z := exchangeRejNTT n (bytes, v)
    rejNTTPoly (List.ofFn z.1) = some v ∧ z.2 = u := by
  have hu := (rejNTTPoly_eq_some_iff _ _).mp h
  have enough : 256 ≤ (rejNTTCoefficients (List.ofFn bytes)).length := by
    have hlen := congrArg List.length hu
    simp only [List.length_take, List.length_ofFn] at hlen; omega
  obtain ⟨ha, hb⟩ := exchange_coefficients (List.ofFn bytes) (List.ofFn v)
  have he := lists_exchangeFixed (bytes, v)
  change rejNTTPoly (List.ofFn (exchangeFixed (bytes, v)).1) = some v ∧
    (exchangeFixed (bytes, v)).2 = u
  refine ⟨?_, List.ofFn_injective ?_⟩
  · rw [rejNTTPoly_eq_some_iff, he.1, ha]
    simp only [List.length_ofFn, List.take_of_length_le (List.length_ofFn.trans_le enough),
      List.take_append, List.take_of_length_le List.length_ofFn.le,
      Nat.sub_self, List.take_zero, List.append_nil]
  · rw [he.2, hb, List.length_ofFn, hu,
      List.drop_of_length_le (List.length_ofFn.trans_le enough), List.append_nil]

/-- The bounded sampler exhausts exactly the same prefixes after programming. -/
theorem exchangeRejNTT_of_none {n : ℕ} {bytes : FixedBytes n}
    (h : rejNTTPoly (List.ofFn bytes) = none) (v : Poly) :
    rejNTTPoly (List.ofFn (exchangeRejNTT n (bytes, v)).1) = none := by
  have hlt := (rejNTTPoly_eq_none_iff _).mp h
  change rejNTTPoly (List.ofFn (exchangeFixed (bytes, v)).1) = none
  rw [rejNTTPoly_eq_none_iff, (lists_exchangeFixed (bytes, v)).1,
    (exchange_coefficients (List.ofFn bytes) (List.ofFn v)).1]
  simp only [List.length_append, List.length_take, List.length_drop, List.length_ofFn]; omega

/-- Joint law of the entire raw SHAKE128 prefix and the bounded Algorithm 30 answer.
Drawing uniform bytes and an independent uniform polynomial, exchanging them and reporting the
external polynomial on success gives the very same law as reading the polynomial from the bytes.
The equality includes the finite-prefix failure event. -/
theorem uniform_exchangeRejNTT (n : ℕ) :
    (PMF.uniformOfFintype (FixedBytes n × Poly)).map (fun (bytes, v) =>
      ((exchangeRejNTT n (bytes, v)).1, (rejNTTPoly (List.ofFn bytes)).map fun _ => v)) =
    (PMF.uniformOfFintype (FixedBytes n)).map (fun bytes =>
      (bytes, rejNTTPoly (List.ofFn bytes))) :=
  PMF.uniformOfFintype_map_exchange_option (exchangeRejNTT n)
    (fun bytes => rejNTTPoly (List.ofFn bytes)) id exchangeRejNTT_of_none
    (fun h v => (exchangeRejNTT_of_some h v).1)

end Cslib.Crypto.MLDSA.FIPS204
