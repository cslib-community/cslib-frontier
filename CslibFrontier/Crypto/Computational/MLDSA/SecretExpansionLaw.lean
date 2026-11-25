/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.MatrixOracle
public import CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import CslibFrontier.Foundations.Data.Option
import all CslibFrontier.Crypto.Computational.MLDSA.MatrixOracle
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.IID
import Mathlib.Data.List.Nodup

/-!
# The FIPS secret expansion and the short-secret MLWE law

[FIPS 204][NISTFIPS204], Algorithms 15 and 31, read two nibbles per byte and keep the first
256 accepted short coefficients. The accepted positions determine whether the capped sampler
fails. On success their values are independently uniform in the same interval used in MLWE.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability
open MatrixOracle (shortCoeff)

private abbrev Digit (s : Level) := Fin (2 * s.params.η + 1)
private abbrev Pos (n : ℕ) := Fin n × Fin 2

private def accepted (s : Level) (h : Fin 16) : Bool :=
  if s.params.η = 2 then h.val < 15 else h.val < 9

-- Each accepted nibble retains its quotient within the 0..14 alphabet when η = 2.
-- Its residue (or the whole value for η = 4) is exchanged with the supplied short digit.
private def swapDigit (s : Level) (z : Fin 16 × Digit s) : Fin 16 × Digit s :=
  let k := 2 * s.params.η + 1
  if accepted s z.1 then
    (Fin.ofNat 16 (z.1.val / k * k + (k - 1 - z.2.val)),
     Fin.ofNat k (k - 1 - (z.1.val % k)))
  else z

private def digitExchange (s : Level) : Equiv.Perm (Fin 16 × Digit s) :=
  let inv : Function.Involutive (swapDigit s) := by
    change ∀ z, swapDigit s (swapDigit s z) = z
    cases s <;> decide +kernel
  ⟨swapDigit s, swapDigit s, inv, inv⟩

private theorem read_exchanged (s : Level) :
    ∀ (h : Fin 16) (d : Digit s),
      boundedCoeff s.params.η ((digitExchange s (h, d)).1.val) =
        (if accepted s h then some (shortCoeff s d) else none) := by
  cases s <;> decide +kernel

private def byteHalves : Byte ≃ (Fin 2 → Fin 16) where
  toFun b := ![Fin.ofNat 16 b.val, Fin.ofNat 16 (b.val / 16)]
  invFun h := Fin.ofNat 256 ((h 0).val + 16 * (h 1).val)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def halves (n : ℕ) : FixedBytes n ≃ (Pos n → Fin 16) :=
  (Equiv.piCongrRight fun _ => byteHalves).trans (Equiv.curry _ _ _).symm

private def positions (n : ℕ) : List (Pos n) := (List.finRange n).product (List.finRange 2)

private theorem read_halves {n : ℕ} (s : Level) (t : FixedBytes n) :
    rejBoundedPoly s (List.ofFn t) =
      asPoly ((positions n).filterMap fun j => boundedCoeff s.params.η (halves n t j).val) := by
  have two : List.finRange 2 = [0, 1] := rfl
  simp only [rejBoundedPoly, List.ofFn_eq_map, List.flatMap_map, positions,
    List.product, List.filterMap_flatMap, List.filterMap_map, two]
  congr 1
  apply List.flatMap_congr
  intro i _
  have eq : ∀ b : Byte, ((byteHalves b 0).val, (byteHalves b 1).val) = (b.val % 16, b.val / 16) :=
    by decide +kernel
  simp only [show halves n t (i, 0) = byteHalves (t i) 0 from rfl,
    show halves n t (i, 1) = byteHalves (t i) 1 from rfl,
    show (byteHalves (t i) 0).val = (t i).val % 16 from congrArg Prod.fst (eq (t i)),
    show (byteHalves (t i) 1).val = (t i).val / 16 from congrArg Prod.snd (eq (t i)),
    List.filterMap_cons, List.filterMap_nil, Function.comp_apply]

private def tapeExchange (s : Level) (n : ℕ) :
    Equiv.Perm ((Pos n → Fin 16) × (Pos n → Digit s)) :=
  let e := Equiv.arrowProdEquivProdArrow (Pos n) (fun _ => Fin 16) (fun _ => Digit s)
  e.symm.trans ((Equiv.piCongrRight fun _ => digitExchange s).trans e)

private abbrev nibbleRead {n : ℕ} (s : Level) (t : Pos n → Fin 16) : Option Poly :=
  asPoly ((positions n).filterMap fun j => boundedCoeff s.params.η (t j).val)

private def acceptedPositions {n : ℕ} (s : Level) (t : Pos n → Fin 16) : List (Pos n) :=
  (positions n).filter fun j => accepted s (t j)

private theorem exchanged_poly {n : ℕ} (s : Level) (t : Pos n → Fin 16) (d : Pos n → Digit s) :
    nibbleRead s ((tapeExchange s n (t, d)).1) =
      asPoly ((acceptedPositions s t).map fun j => shortCoeff s (d j)) := by
  apply congrArg asPoly
  have read (j : Pos n) : boundedCoeff s.params.η ((tapeExchange s n (t, d)).1 j).val =
      (if accepted s (t j) then some (shortCoeff s (d j)) else none) := read_exchanged s _ _
  simp only [read, acceptedPositions]
  induction positions n with
  | nil => rfl
  | cons j l ih => cases h : accepted s (t j) <;> simp [h, ih]

private theorem selected_poly {n : ℕ} (s : Level) (l : List (Pos n)) (hl : l.Nodup) :
    ((PMF.uniformOfFintype (Pos n → Digit s)).map fun d =>
      asPoly (l.map fun j => shortCoeff s (d j))) =
      if 256 ≤ l.length then (MatrixOracle.shortPolyLaw s).map some else PMF.pure none := by
  split_ifs with enough
  · let e : Fin 256 ↪ Pos n := ⟨fun j => l.get (Fin.castLE enough j), fun _ _ eq =>
      Fin.castLE_injective enough (hl.injective_get eq)⟩
    let value (v : Fin 256 → Digit s) : Option Poly := some (fun j => shortCoeff s (v j))
    have parse (d : Pos n → Digit s) :
        asPoly (l.map fun j => shortCoeff s (d j)) = value (fun i => d (e i)) := by
      simp only [asPoly, List.size_toArray, List.length_map, Nat.not_lt.mpr enough, ↓reduceIte]
      apply congrArg some
      funext j
      rw [getElem!_pos _ _ (by simpa using j.isLt.trans_le enough)]
      simp [e, List.get_eq_getElem]
    simp_rw [parse]
    change (PMF.uniformOfFintype (Pos n → Digit s)).map (value ∘ fun d j => d (e j)) = _
    rw [← PMF.map_comp, PMF.uniformOfFintype_pi_map_comp_embedding, MatrixOracle.shortPolyLaw,
      MatrixOracle.shortCoefficientLaw, PMF.pi_map, PMF.pi_uniformOfFintype, PMF.map_comp]
    rfl
  · simp [asPoly, Nat.lt_of_not_ge enough, PMF.map_const, Function.const_def]

/-- Algorithm 31 on uniform bytes has an exact two-stage law: test the native prefix for
exhaustion, then on success return one independent short-secret MLWE polynomial. This
applies at every input length, including the 481-byte Appendix C limit. -/
theorem uniform_rejBoundedPoly (s : Level) (n : ℕ) :
    let U := PMF.uniformOfFintype (FixedBytes n)
    (U.map fun t => rejBoundedPoly s (List.ofFn t)) = U.bind fun t =>
      if (rejBoundedPoly s (List.ofFn t)).isSome then (MatrixOracle.shortPolyLaw s).map some
      else PMF.pure none := by
  intro U
  let V := PMF.uniformOfFintype (Pos n → Fin 16)
  have half : U.map (halves n) = V := PMF.uniformOfFintype_map_equiv _
  simp_rw [read_halves]
  change U.map (nibbleRead s ∘ halves n) = U.bind fun t =>
    if (nibbleRead s (halves n t)).isSome then _ else _
  rw [← PMF.map_comp, half]
  let score (t : Pos n → Fin 16) : PMF (Option Poly) :=
    if (nibbleRead s t).isSome then (MatrixOracle.shortPolyLaw s).map some else PMF.pure none
  change _ = U.bind (score ∘ halves n)
  rw [← PMF.bind_map, half]
  have swap := PMF.uniformOfFintype_bind_map_fst_equiv (tapeExchange s n)
  have law := congrArg (PMF.map (nibbleRead s)) swap
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, exchanged_poly] at law
  rw [← law]
  apply congrArg (PMF.bind V ·)
  funext t
  have nd : (acceptedPositions s t).Nodup :=
    ((List.nodup_finRange n).product (List.nodup_finRange 2)).filter _
  rw [selected_poly s (acceptedPositions s t) nd]
  have count : ((positions n).filterMap fun j => boundedCoeff s.params.η (t j).val).length =
      (acceptedPositions s t).length := by
    have one : ∀ (h : Fin 16), (boundedCoeff s.params.η h.val).isSome = accepted s h := by
      cases s <;> decide +kernel
    unfold acceptedPositions
    induction positions n with
    | nil => rfl
    | cons j l ih =>
      cases h : boundedCoeff s.params.η (t j).val <;> simp [h, ← one (t j), ih]
  by_cases ok : 256 ≤ (acceptedPositions s t).length <;>
    simp [score, nibbleRead, asPoly, count, ok]

/-- Parse the ordered nonce prefixes for one vector of Algorithm 33, failing when any
component exhausts its input before producing 256 coefficients. -/
private def rejBoundedVector (s : Level) {r n : ℕ} (rows : Fin r → FixedBytes n) :
    Option (Fin r → Poly) := tabulate r fun i => rejBoundedPoly s (List.ofFn (rows i))

private theorem vector_law (s : Level) (n r : ℕ) :
    let U := PMF.uniformOfFintype (Fin r → FixedBytes n)
    (U.map (rejBoundedVector s)) = U.bind fun t =>
      if (rejBoundedVector s t).isSome then (MatrixOracle.shortVectorLaw s r).map some
      else PMF.pure none := by
  intro U
  let decode (t : FixedBytes n) := rejBoundedPoly s (List.ofFn t)
  let P := MatrixOracle.shortPolyLaw s
  let B := PMF.uniformOfFintype (FixedBytes n)
  have single : B.map decode = B.bind fun t => P.map fun p => (decode t).map fun _ => p := by
    rw [uniform_rejBoundedPoly]
    apply congrArg (PMF.bind B ·)
    funext t
    change (if (decode t).isSome then P.map some else PMF.pure none) = _
    cases decode t
    exacts [(PMF.map_const ..).symm, rfl]
  have joint := congrArg (PMF.pi (ι := Fin r) ∘ Function.const (Fin r)) single
  change PMF.pi (fun _ : Fin r => B.map decode) = PMF.pi (fun _ : Fin r => B.bind _) at joint
  rw [PMF.pi_map, PMF.pi_bind] at joint
  simp only [B, PMF.pi_uniformOfFintype] at joint
  have score := congrArg (PMF.map (tabulate r)) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.pi_map] at score
  change U.map (fun v => tabulate r fun i => decode (v i)) = _
  rw [score]
  apply congrArg (PMF.bind U ·)
  funext v
  have exchange (p : Fin r → Poly) : tabulate r (fun i => (decode (v i)).map fun _ => p i) =
      (rejBoundedVector s v).map fun _ => p := by
    simp only [tabulate, rejBoundedVector, Vector.ofFnM_option_replace, Functor.map, Option.map_map]
    cases Vector.ofFnM (fun i => decode (v i)) with
    | none => rfl
    | some _ => exact congrArg some (funext (Vector.get_ofFn p))
  simp_rw [exchange]
  cases h : rejBoundedVector s v
  exacts [PMF.map_const .., rfl]

/-- Independent 481-byte streams at the distinct secret-vector nonces of Algorithm 33.
The actual Algorithm 31 parser is applied separately at every nonce used for the MLWE secret
and error. The joint law retains failure of either vector and, on success, gives independent
samples from the two short-vector laws of the decision-MLWE game. -/
private theorem uniform_vector_pair (s : Level) :
    let U := PMF.uniformOfFintype (Fin s.params.ℓ → FixedBytes 481)
    let V := PMF.uniformOfFintype (Fin s.params.k → FixedBytes 481)
    let parse := fun x y => do
      let secret ← rejBoundedVector s x
      let error ← rejBoundedVector s y
      return (secret, error)
    (U.bind fun x => V.map (parse x)) = U.bind fun x => V.bind fun y =>
      if (parse x y).isSome then
        (MatrixOracle.shortVectorLaw s s.params.ℓ).bind fun secret =>
          (MatrixOracle.shortVectorLaw s s.params.k).map fun error => some (secret, error)
      else PMF.pure none := by
  intro U V parse
  let pair (x : Option (Fin s.params.ℓ → Poly)) (y : Option (Fin s.params.k → Poly)) := do
    let a ← x
    let b ← y
    return (a, b)
  have law := congrArg₂ (fun p q => PMF.bind p fun x => PMF.map (pair x) q)
    (vector_law s 481 s.params.ℓ) (vector_law s 481 s.params.k)
  simp only [PMF.bind_map, PMF.map_comp, Function.comp_def, PMF.map_bind, PMF.bind_bind] at law
  change (U.bind _) = _ at law
  apply law.trans
  apply congrArg (PMF.bind U ·)
  funext x
  rw [PMF.bind_comm _ V]
  apply congrArg (PMF.bind V ·)
  funext y
  cases hx : rejBoundedVector s x <;> cases hy : rejBoundedVector s y <;>
    simp only [parse, pair, hx, hy, Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.pure_def,
      PMF.pure_bind, PMF.pure_map, PMF.bind_map, PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_const ..

private abbrev Nonce (s : Level) := Fin s.params.ℓ ⊕ Fin s.params.k
private abbrev SecretRows (s : Level) := (Fin s.params.ℓ → FixedBytes 481) ×
  (Fin s.params.k → FixedBytes 481)

private def nonceWord (s : Level) (rho : FixedBytes 64) (j : Nonce s) : List Bool :=
  Keccak.bytesToBitsLE (nonceInput rho.toList (finSumFinEquiv j).val)

private theorem nonceWord_injective (s : Level) (rho : FixedBytes 64) :
    Function.Injective (nonceWord s rho) := by
  intro i j h
  have size : s.params.ℓ + s.params.k ≤ 65536 := by cases s <;> decide
  exact finSumFinEquiv.injective (Fin.ext (eq_of_nonceInput_eq
    ((finSumFinEquiv i).isLt.trans_le size) ((finSumFinEquiv j).isLt.trans_le size)
    (Keccak.bytesToBitsLE_injective h)))

private def secretPoint {a b : ℕ} (s : Level) (rho : FixedBytes 64) (ha : 528 ≤ a)
    (hb : 481 ≤ b) : (Nonce s × Fin 481) ↪ (RawWord a × Fin b) where
  toFun p := (word (nonceWord s rho p.1) ((length_nonceInput_bits rho _).le.trans ha),
    p.2.castLE hb)
  inj' := by
    intro p q h
    have raw := word_inj (hx := (length_nonceInput_bits rho (finSumFinEquiv p.1).val).le.trans ha)
      (hy := (length_nonceInput_bits rho (finSumFinEquiv q.1).val).le.trans ha)
      (congrArg Prod.fst h)
    exact Prod.ext (nonceWord_injective s rho raw) (Fin.castLE_injective hb (congrArg Prod.snd h))

private def rowPair (s : Level) : ((Nonce s × Fin 481) → Byte) ≃ SecretRows s :=
  (Equiv.curry _ _ _).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private def vectors (s : Level) (p : SecretRows s) :
    Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly)) := do
  let x ← rejBoundedVector s p.1
  let y ← rejBoundedVector s p.2
  return (x, y)

private theorem expandS_install {a b : ℕ} (s : Level) (rho : FixedBytes 64)
    (ha : 528 ≤ a) (hb : 481 ≤ b) (H : Xofs) (T : Table a b) :
    ({H with h256 := install H.h256 T} : Xofs).expandS s rho.toList =
      vectors s (rowPair s (fun p => T (secretPoint s rho ha hb p))) := by
  let p := secretPoint s rho ha hb
  have read (j : Nonce s) :
      (install H.h256 T).read (nonceWord s rho j) 481 = List.ofFn (fun i => T (p (j, i))) := by
    apply List.ext_getElem
    · exact ((install H.h256 T).length_read _ _).trans (List.length_ofFn ..).symm
    · intro i hi _
      have h : i < 481 := by simpa only [ExtendableOutput.length_read] using hi
      rw [ExtendableOutput.getElem_read _ _ h, byteAt_install,
        dite_eq_left ⟨(length_nonceInput_bits rho _).le.trans ha, h.trans_le hb⟩, List.getElem_ofFn]
      rfl
  have row (j : Nonce s) :
      ({H with h256 := install H.h256 T} : Xofs).secretPoly s rho.toList
        (finSumFinEquiv j).val = rejBoundedPoly s (List.ofFn fun i => T (p (j, i))) :=
    congrArg (rejBoundedPoly s) (read j)
  let G : Xofs := {H with h256 := install H.h256 T}
  have first (i : Fin s.params.ℓ) : G.secretPoly s rho.toList i.val =
      rejBoundedPoly s (List.ofFn fun j => T (p (.inl i, j))) := row (.inl i)
  have second (i : Fin s.params.k) : G.secretPoly s rho.toList (s.params.ℓ + i.val) =
      rejBoundedPoly s (List.ofFn fun j => T (p (.inr i, j))) := row (.inr i)
  change G.expandS s _ = _
  simp only [Xofs.expandS, first, second, vectors, rejBoundedVector]
  rfl

private theorem uniformPrefixes_secretRows (base : Xofs) (s : Level) (rho : FixedBytes 64)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) :
    ((base.uniformPrefixes a b).map fun H => H.expandS s rho.toList) =
      (PMF.uniformOfFintype (Fin s.params.ℓ → FixedBytes 481)).bind fun x =>
      (PMF.uniformOfFintype (Fin s.params.k → FixedBytes 481)).map fun y => vectors s (x, y) := by
  rw [independent_tables]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  have read (t u : Table a b) :
      (⟨install base.h128 u, install base.h256 t⟩ : Xofs).expandS s rho.toList =
        vectors s (rowPair s (fun j => t (secretPoint s rho ha hb j))) :=
    expandS_install s rho ha hb {base with h128 := install base.h128 u} t
  simp_rw [read]
  let take (t : Table a b) := rowPair s (fun j => t (secretPoint s rho ha hb j))
  have ignore (t : Table a b) : (PMF.uniformOfFintype (Table a b)).map
      (fun _ => vectors s (take t)) = PMF.pure (vectors s (take t)) := PMF.map_const ..
  change (PMF.uniformOfFintype (Table a b)).bind (fun t =>
    (PMF.uniformOfFintype (Table a b)).map fun _ => vectors s (take t)) = _
  simp_rw [ignore]
  change (PMF.uniformOfFintype (Table a b)).map
    ((vectors s ∘ rowPair s) ∘ fun t j => t (secretPoint s rho ha hb j)) = _
  have eq := congrArg (PMF.map (vectors s ∘ rowPair s))
    (PMF.uniformOfFintype_pi_map_comp_embedding (α := Byte) (secretPoint s rho ha hb))
  rw [PMF.map_comp] at eq
  exact eq.trans (by
    rw [← PMF.map_comp, PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_bind_map])

/-- Algorithm 33 on the finite random SHAKE256 stream at a fixed 64-byte seed has exactly
the joint short-secret MLWE law on success. The two vectors use disjoint little-endian nonces.
Both sides retain the native failure probability of the 481-byte cap at every nonce. -/
theorem uniformPrefixes_expandS (base : Xofs) (s : Level) (rho : FixedBytes 64) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) :
    let R := base.uniformPrefixes a b
    (R.map fun H => H.expandS s rho.toList) = R.bind fun H =>
      if (H.expandS s rho.toList).isSome then
        (MatrixOracle.shortVectorLaw s s.params.ℓ).bind fun x =>
          (MatrixOracle.shortVectorLaw s s.params.k).map fun y => some (x, y)
      else PMF.pure none := by
  intro R
  let U := PMF.uniformOfFintype (Fin s.params.ℓ → FixedBytes 481)
  let V := PMF.uniformOfFintype (Fin s.params.k → FixedBytes 481)
  let parse x y := vectors s (x, y)
  have joint : (R.map fun H => H.expandS s rho.toList) = U.bind fun x => V.map (parse x) :=
    uniformPrefixes_secretRows base s rho ha hb
  let test (o : Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly))) : PMF _ :=
    if o.isSome then (MatrixOracle.shortVectorLaw s s.params.ℓ).bind fun x =>
      (MatrixOracle.shortVectorLaw s s.params.k).map fun y => some (x, y) else PMF.pure none
  change _ = R.bind (test ∘ fun H => H.expandS s rho.toList)
  rw [← PMF.bind_map, joint, PMF.bind_bind]
  simpa only [PMF.bind_map, Function.comp_def, parse, test, vectors] using uniform_vector_pair s

end Cslib.Crypto.MLDSA.FIPS204
