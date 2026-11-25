/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Linear.ToeplitzPacking
public import CslibFrontier.Computability.PolyTime.BinaryField
import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Computing the binary trace kernel

The binary field is represented in the power basis of the least irreducible polynomial of
the requested degree. Searching its coordinate words in order supplies a primitive root
of each requested order dividing the size of the unit group. The trace of the product of
two powers can then be evaluated entirely on bit lists.
-/

public section

namespace Cslib.Circuit.ToeplitzPacking

open Cslib.BinaryField Cslib.BitString
open Turing.MultiTapeTM ComputableInPolyTime

private def wordIsOne (k : ℕ) (w : List Bool) : Bool :=
  (List.range k).all fun i => w.getD i false == [true].getD i false

private theorem wordIsOne_iff {k : ℕ} (hk : k ≠ 0) (w : List Bool) :
    wordIsOne k w = true ↔ fieldOfBits (basis hk) w = 1 := by
  simp only [wordIsOne, List.all_eq_true, List.mem_range, beq_iff_eq]
  rw [← fieldOfBits_one hk, ← (equivBits hk).injective.eq_iff, funext_iff]
  simp only [equivBits_fieldOfBits, Fin.forall_iff]

private def exactOrder (k : ℕ) (tab : List (List (List Bool))) (d : ℕ) (w : List Bool) : Bool :=
  wordIsOne k (powerWord tab w d) &&
    (List.range d).all fun i => i == 0 || !wordIsOne k (powerWord tab w i)

private theorem exactOrder_iff {k d : ℕ} (hk : k ≠ 0) (hd : 0 < d) (w : List Bool) :
    exactOrder k (fieldTable k) d w = true ↔ IsPrimitiveRoot (fieldOfBits (basis hk) w) d := by
  simp only [exactOrder, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true', ← Bool.not_eq_true, wordIsOne_iff hk, fieldOfBits_powerWord hk,
    IsPrimitiveRoot.iff_orderOf, orderOf_eq_iff hd]
  grind

/-- The first coordinate word with multiplicative order `d` in the explicit degree-`k`
binary field, or the empty word if the order is absent. -/
def rootWord (k d : ℕ) : List Bool :=
  ((enumList k).find? (exactOrder k (fieldTable k) d)).getD []

/-- The field element computed by the bounded coordinate search for an order-`d` root. -/
noncomputable def root {k : ℕ} (hk : k ≠ 0) (d : ℕ) : BinaryField k :=
  fieldOfBits (basis hk) (rootWord k d)

/-- The search finds a primitive root whenever the requested order divides the unit group size. -/
theorem isPrimitiveRoot_root {k d : ℕ} (hk : k ≠ 0) (hd : 0 < d) (hdvd : d ∣ 2 ^ k - 1) :
    IsPrimitiveRoot (root hk d) d := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (BinaryField k)ˣ)
  have hgen : IsPrimitiveRoot (g : BinaryField k) (2 ^ k - 1) := by
    apply IsPrimitiveRoot.coe_units_iff.mpr
    rw [IsPrimitiveRoot.iff_orderOf, hg, Nat.card_units, Nat.card_eq_fintype_card, card hk]
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < 2 ^ k - 1 := by
    have := Nat.one_lt_two_pow hk
    lia
  have hprim : IsPrimitiveRoot ((g : BinaryField k) ^ c) d :=
    hgen.pow hpos (hc.trans (Nat.mul_comm d c))
  let v := List.ofFn (equivBits hk ((g : BinaryField k) ^ c))
  have hv : v ∈ enumList k := mem_enumList.mpr (List.length_ofFn ..)
  have hpass : exactOrder k (fieldTable k) d v = true := by
    rw [exactOrder_iff hk hd, fieldOfBits_ofFn, AddEquiv.symm_apply_apply]
    exact hprim
  unfold root rootWord
  cases h : (enumList k).find? (exactOrder k (fieldTable k) d) with
  | none => exact False.elim ((List.find?_eq_none.mp h v hv) hpass)
  | some x => exact (exactOrder_iff hk hd x).mp (List.find?_some h)

/-- A bit-list algorithm for the absolute trace of the product of two root powers. The
arguments are the field degree, two root orders, and their respective exponents. -/
def tracePowers (k n ℓ e b : ℕ) : Bool :=
  let tab := fieldTable k
  listDot (traceVector tab)
    (fieldMul tab (powerWord tab (rootWord k n) e) (powerWord tab (rootWord k ℓ) b))

/-- The trace computed on words agrees with the algebraic field trace. -/
theorem tracePowers_eq {k : ℕ} (hk : k ≠ 0) (n ℓ e b : ℕ) :
    tracePowers k n ℓ e b = bitEquiv (Algebra.trace (ZMod 2) (BinaryField k)
      (root hk n ^ e * root hk ℓ ^ b)) := by
  simp only [tracePowers, listDot_traceVector (isMulTable_fieldTable hk),
    fieldOfBits_fieldMul (isMulTable_fieldTable hk), fieldOfBits_powerWord hk, root]

/-- The finite-field kernel of the packing construction, computed by the word algorithm
at the long chirp exponent and short coordinate. -/
theorem tracePowers_eq_kernel {k n ℓ : ℕ} [NeZero n] [NeZero ℓ]
    (hk : k ≠ 0) (hn : n ∣ 2 ^ k - 1) (hℓ : ℓ ∣ 2 ^ k - 1)
    (u : ZMod n) (p : ZMod n × ZMod ℓ) :
    tracePowers k n ℓ (-u * p.1 ^ 2).val p.2.val =
      bitEquiv (kernel
        (AddChar.zmodChar n (isPrimitiveRoot_root hk (NeZero.pos n) hn).pow_eq_one)
        (AddChar.zmodChar ℓ (isPrimitiveRoot_root hk (NeZero.pos ℓ) hℓ).pow_eq_one) u p) := by
  rw [tracePowers_eq hk]
  rfl


attribute [local irreducible] ComputableInPolyTime
attribute [local fun_prop] powerWord_polyTime

variable {I : Type} {enc : I ↪ List Bool}

private theorem wordIsOne_polyTime {k : I → ℕ} {w : I → List Bool}
    (hk : ComputableInPolyTime k enc encUnary) (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun i => wordIsOne (k i) (w i)) enc encBool := by
  unfold wordIsOne
  fun_prop

attribute [local fun_prop] wordIsOne_polyTime

private theorem exactOrder_polyTime {k d : I → ℕ} {tab : I → List (List (List Bool))}
    {w : I → List Bool} (hk : ComputableInPolyTime k enc encUnary)
    (htab : ComputableInPolyTime tab enc encTable) (hd : ComputableInPolyTime d enc encUnary)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun i => exactOrder (k i) (tab i) (d i) (w i)) enc encBool := by
  unfold exactOrder
  fun_prop

private theorem rootWord_polyTime {k d : I → ℕ} (hk : ComputableInPolyTime k enc encUnary)
    (htab : ComputableInPolyTime (fun i => fieldTable (k i)) enc encTable)
    (henum : ComputableInPolyTime (fun i => enumList (k i)) enc (encList encBits))
    (hd : ComputableInPolyTime d enc encUnary) :
    ComputableInPolyTime (fun i => rootWord (k i) (d i)) enc encBits := by
  unfold rootWord
  exact (findWithInput henum (exactOrder_polyTime (hk.comp (fst _ _)) (htab.comp (fst _ _))
    (hd.comp (fst _ _)) (snd _ _))).optionGetDWithInput (const [])

/-- The trace kernel is polynomial-time when the field cardinality is polynomially bounded in
the input length. The degree, orders and exponents are supplied in unary. The algorithm builds
the field and finds both roots from these inputs. -/
theorem tracePowers_polyTime {k n ℓ e b : I → ℕ}
    (hk : ComputableInPolyTime k enc encUnary)
    (hsize : PolyBounded (fun i => (enc i).length) (fun i => 2 ^ k i))
    (hn : ComputableInPolyTime n enc encUnary) (hℓ : ComputableInPolyTime ℓ enc encUnary)
    (he : ComputableInPolyTime e enc encUnary) (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun i => tracePowers (k i) (n i) (ℓ i) (e i) (b i))
      enc encBool := by
  have henum := bitsEnumList_of_polyBounded hk hsize
  have htab := computableInPolyTime_fieldTable hk hsize
  unfold tracePowers
  exact bitsListDot (computableInPolyTime_traceVector htab)
    (computableInPolyTime_fieldMul' htab
      (powerWord_polyTime htab (rootWord_polyTime hk htab henum hn) he)
      (powerWord_polyTime htab (rootWord_polyTime hk htab henum hℓ) hb))


end Cslib.Circuit.ToeplitzPacking
