/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.RelationMinor
import CslibFrontier.Foundations.BooleanAnalysis.OddForm
import CslibFrontier.Logics.Propositional.CSP.Affine
import CslibFrontier.Foundations.Data.BitString.Hamming
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered minors for nonselfdual Boolean languages

The arbitrary-arity parity and majority minor arguments are an original reconstruction of the
expressibility argument omitted after Lemma 4 of
[DvorakKupec2015], printed pp. 438–439. They are not attributed to a printed proof of that lemma.
All relations use the existing `CSP.booleanRelation`/`IsPolymorphism` interface. Traces preserve
survivor order. These are finite semantic constructions; geometric realization, native reduction,
runtime and planar hardness are separate obligations.

## Main results

* `Cslib.Logic.PL.CSP.RelationMinor.exists_majority_minor`: a normalized ternary majority failure.
* `Cslib.Logic.PL.CSP.RelationMinor.exists_binary_parity_minor`: a binary parity failure.
* `Cslib.Logic.PL.CSP.RelationMinor.exists_nand_trace`: an actual ordered trace to NAND.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

open Cslib.BitString

variable {m n : ℕ}

/-- Choose an arity-minimal failing relation among actual finite traces. No bound on the
starting arity or truth-table enumeration is used. -/
private theorem exists_minimal_failure {R : Set (Fin m → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool} (h : ¬IsPolymorphism f R) :
    ∃ (n : ℕ) (S : Set (Fin n → Bool)), Nonempty (Trace R S) ∧ ¬IsPolymorphism f S ∧
      ∀ (l : ℕ) (T : Set (Fin l → Bool)), Nonempty (Trace S T) → l < n → IsPolymorphism f T := by
  classical
  let P (n : ℕ) := ∃ S : Set (Fin n → Bool), Nonempty (Trace R S) ∧ ¬IsPolymorphism f S
  have hex : ∃ n, P n := ⟨m, R, ⟨.refl⟩, h⟩
  obtain ⟨S, ⟨trace⟩, hS⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, S, ⟨trace⟩, hS, ?_⟩
  intro l T ⟨tail⟩ hlt
  by_contra hT
  exact (Nat.find_min hex hlt) ⟨T, ⟨trace.trans tail⟩, hT⟩

/-- Translation commutation lets a minimum failure be normalized to a missing zero tuple.
Every smaller minor, including every projection and cofactor, preserves the operation. -/
private theorem exists_normalized_minimal_failure {R : Set (Fin m → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool}
    (htranslate : ∀ (a : Fin k → Bool) b,
      f (fun j => a j + b) = f a + b)
    (h : ¬IsPolymorphism f R) :
    ∃ (n : ℕ) (S : Set (Fin n → Bool)), Nonempty (Trace R S) ∧
      (0 : Fin n → Bool) ∉ S ∧ ¬IsPolymorphism f S ∧
      (∃ a : Fin k → Fin n → Bool, (∀ j, a j ∈ S) ∧
        (fun i => f (fun j => a j i)) = 0) ∧
      ∀ (l : ℕ) (T : Set (Fin l → Bool)), Nonempty (Trace S T) → l < n → IsPolymorphism f T := by
  classical
  obtain ⟨n, S, ⟨trace⟩, hS, hmin⟩ := exists_minimal_failure h
  simp only [IsPolymorphism, not_forall] at hS
  obtain ⟨a, ha, hout⟩ := hS
  let t : Fin n → Bool := fun i => f (fun j => a j i)
  let T := twist S t
  have hin (j : Fin k) : a j + t ∈ T := by
    change (a j + t) + t ∈ S
    have ht : t + t = 0 := by ext i; exact BooleanRing.add_self _
    simpa only [add_assoc, ht, add_zero] using ha j
  have hz : (0 : Fin n → Bool) ∉ T := by
    simpa [T, twist, t] using hout
  have ho : (fun i => f (fun j => (a j + t) i)) = (0 : Fin n → Bool) := by
    ext i
    change f (fun j => a j i + t i) = (0 : Bool)
    rw [htranslate]
    exact BooleanRing.add_self _
  have hb : ¬IsPolymorphism f T := fun hT => hz (ho ▸ hT (fun j => a j + t) hin)
  refine ⟨n, T, ⟨trace.translate t⟩, hz, hb, ⟨_, hin, ho⟩, ?_⟩
  intro l U ⟨tail⟩ hl
  exact hmin l U ⟨(Trace.refl.translate t).trans tail⟩ hl

private theorem parity_const (b : Bool) : Cslib.parity 3 (fun _ => b) = b := by
  cases b <;> decide

private theorem parity_translate (a : Fin 3 → Bool) (b : Bool) :
    Cslib.parity 3 (fun j => a j + b) = Cslib.parity 3 a + b := by
  change Cslib.parity 3 (a + fun _ => b) = _
  rw [Cslib.parity, Cslib.parityOn_add]
  exact congrArg (Cslib.parity 3 a + ·) (parity_const b)

private theorem majority_translate (a : Fin 3 → Bool) (b : Bool) :
    Cslib.majority 3 (fun j => a j + b) = Cslib.majority 3 a + b := by
  revert a b
  decide

/-- Every relation of arity at most one is preserved by ternary parity, including empty
and nullary relations. -/
theorem parity_preserves_of_arity_le_one {R : Set (Fin n → Bool)} (hn : n ≤ 1) :
    IsPolymorphism (Cslib.parity 3) R := fun a ha => by
  obtain ⟨j, hj⟩ : ∃ j, (fun i => Cslib.parity 3 (fun k => a k i)) = a j := by
    clear ha R
    interval_cases n
    · exact ⟨0, Subsingleton.elim _ _⟩
    · revert a
      decide
  exact hj ▸ ha j

/-- Every relation of arity at most two is majority-preserved, including empty and nullary
relations. The finite check concerns the operation's two-coordinate selector law only. -/
theorem majority_preserves_of_arity_le_two {R : Set (Fin n → Bool)} (hn : n ≤ 2) :
    IsPolymorphism (Cslib.majority 3) R := fun a ha => by
  obtain ⟨j, hj⟩ : ∃ j, (fun i => Cslib.majority 3 (fun k => a k i)) = a j := by
    clear ha R
    interval_cases n
    · exact ⟨0, Subsingleton.elim _ _⟩
    · revert a
      decide
    · revert a
      decide
  exact hj ▸ ha j

/-- If a projected zero output is forced by closure, its unique feasible lift is the unit
at the deleted port. This works for any operation fixing the constant zero input. -/
theorem units_of_projection_closure {R : Set (Fin (n + 1) → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool} (hz : (0 : Fin (n + 1) → Bool) ∉ R)
    (a : Fin k → Fin (n + 1) → Bool) (ha : ∀ j, a j ∈ R)
    (hout : (fun i => f (fun j => a j i)) = 0)
    (hp : ∀ j, IsPolymorphism f (project R j)) :
    ∀ j, Pi.single j true ∈ R := by
  intro j
  have he : (fun i => f (fun k => j.removeNth (a k) i)) = 0 := congrArg j.removeNth hout
  exact single_mem_of_zero_mem_project hz j <|
    he ▸ hp j (fun k => j.removeNth (a k)) fun k => remove_mem_project (ha k) j

/-- Cofactor closure applied to tuples sharing the pinned bit, lifted back to the original
relation. The operation must fix that constant bit. -/
theorem mem_of_cofactor_closure {R : Set (Fin (n + 1) → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool} {j : Fin (n + 1)} {b : Bool}
    (hf : f (fun _ => b) = b) (h : IsPolymorphism f (cofactor R j b))
    (a : Fin k → Fin (n + 1) → Bool) (ha : ∀ i, a i ∈ R)
    (hb : ∀ i, a i j = b) : (fun i => f (fun k => a k i)) ∈ R := by
  have hout : j.insertNth b _ ∈ R :=
    h (fun i => j.removeNth (a i)) (fun i => hb i ▸ remove_mem_cofactor (ha i) j)
  convert hout using 1
  exact Fin.eq_insertNth_iff.mpr ⟨funext hb ▸ hf, rfl⟩

private theorem majority_const (b : Bool) : Cslib.majority 3 (fun _ => b) = b := by
  cases b <;> decide

private theorem parity_three_pointwise {ι : Type*} (a : Fin 3 → ι → Bool) :
    (fun i => Cslib.parity 3 (fun j => a j i)) = a 0 + a 1 + a 2 := by
  funext i
  simp only [Cslib.parity, Cslib.parityOn_eq_sum, Fin.sum_univ_three, Pi.add_apply, add_assoc]

private theorem sum_three_mem_of_cofactor {R : Set (Fin (n + 1) → Bool)}
    {j : Fin (n + 1)} {b : Bool} (h : IsPolymorphism (Cslib.parity 3) (cofactor R j b))
    {x y z : Fin (n + 1) → Bool} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R)
    (hxj : x j = b) (hyj : y j = b) (hzj : z j = b) : x + y + z ∈ R := by
  simpa only [parity_three_pointwise, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    mem_of_cofactor_closure (parity_const b) h ![x, y, z]
      (Fin.forall_fin_succ.mpr ⟨hx, Fin.forall_fin_two.mpr ⟨hy, hz⟩⟩)
      (Fin.forall_fin_succ.mpr ⟨hxj, Fin.forall_fin_two.mpr ⟨hyj, hzj⟩⟩)

private theorem median_units {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    median (Pi.single i true) (Pi.single j true) (Pi.single k true) = 0 := by
  ext l
  by_cases hi : l = i
  · subst l
    simp [median, hij, hik]
  · by_cases hj : l = j
    · subst l
      simp [median, hi, hjk]
    · simp [median, hi, hj, Bool.zero_eq_false]

/-- A majority failure has an actual ordered ternary minor containing the three units and
missing zero. This original reconstruction works at every starting arity; it assumes neither
pins as language symbols nor a minor oracle. Interpreting cofactors as gadgets still needs pins. -/
theorem exists_majority_minor {R : Set (Fin m → Bool)}
    (h : ¬IsPolymorphism (Cslib.majority 3) R) :
    ∃ S : Set (Fin 3 → Bool), Nonempty (Trace R S) ∧
      (0 : Fin 3 → Bool) ∉ S ∧ (∀ i, Pi.single i true ∈ S) := by
  obtain ⟨n, S, trace, hz, hb, ⟨a, ha, hout⟩, hmin⟩ :=
    exists_normalized_minimal_failure majority_translate h
  have hn : 3 ≤ n := not_lt.1 fun hh => hb (majority_preserves_of_arity_le_two (by omega))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp (j : Fin (n + 1)) : IsPolymorphism (Cslib.majority 3) (project S j) :=
    hmin n _ ⟨.project .refl j⟩ (by omega)
  have hu := units_of_projection_closure hz a ha hout hp
  have hn3 : n + 1 = 3 := by
    by_contra hh
    have hn4 : 4 ≤ n + 1 := by omega
    let i : Fin (n + 1) := ⟨0, by omega⟩
    let j : Fin (n + 1) := ⟨1, by omega⟩
    let k : Fin (n + 1) := ⟨2, by omega⟩
    let l : Fin (n + 1) := ⟨3, by omega⟩
    have hc := hmin n (cofactor S l false) ⟨.cofactor .refl l false⟩ (by omega)
    have hm := mem_of_cofactor_closure (majority_const false) hc
      ![Pi.single i true, Pi.single j true, Pi.single k true]
      (by intro q; fin_cases q <;> exact hu _)
      (by intro q; fin_cases q <;> simp [i, j, k, l, Bool.zero_eq_false])
    have he' : (fun p => Cslib.majority 3
        (fun q => (![Pi.single i true, Pi.single j true, Pi.single k true] :
          Fin 3 → Fin (n + 1) → Bool) q p)) = 0 :=
      (funext fun p => (median_apply_eq_majority _ _ _ p).symm).trans
        (median_units (by simp [i, j]) (by simp [i, k]) (by simp [j, k]))
    exact hz (he' ▸ hm)
  obtain rfl : n = 2 := by omega
  exact ⟨S, trace, hz, hu⟩

private theorem parity_eq_true_of_units {R : Set (Fin n → Bool)}
    (hp : IsPolymorphism (Cslib.parity 3) R) (hz : (0 : Fin n → Bool) ∉ R)
    (hu : ∀ i, Pi.single i true ∈ R) {x : Fin n → Bool} (hx : x ∈ R) :
    Cslib.parityOn Finset.univ x = true := by
  classical
  obtain ⟨⟨vs, b⟩, he, he0⟩ := exists_separating_affineEquation hp hz
  have hb : b = true := by
    cases b
    · refine False.elim (he0 ?_)
      change (vs.map fun _ => (0 : Bool)).sum = 0
      simp
    · rfl
  let f : (Fin n → Bool) → Bool := fun a => (vs.map a).sum
  have hadd (a b : Fin n → Bool) : f (a + b) = (f a ^^ f b) := by
    change (vs.map (fun i => a i + b i)).sum = _
    rw [List.sum_map_add, Bool.add_eq_xor]
  obtain ⟨s, hs⟩ := BitString.exists_eq_parityOn_iff.mpr hadd
  have hsall : s = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi := he _ (hu i)
    change f (Pi.single i true) = b at hi
    rw [hs, hb, parityOn_single] at hi
    exact of_decide_eq_true hi
  have h : f x = b := he x hx
  rwa [hs, hsall, hb] at h

private theorem insert_false_single (j : Fin (n + 1)) (i : Fin n) :
    j.insertNth false (Pi.single i true) =
      (Pi.single (j.succAbove i) true : Fin (n + 1) → Bool) := by
  refine Fin.insertNth_eq_iff.mpr ⟨by simp [Ne.symm (Fin.succAbove_ne j i), Bool.zero_eq_false], ?_⟩
  ext k
  simp [Fin.removeNth, Pi.single_apply, Fin.succAbove_inj]

private theorem proper_even_impossible {R : Set (Fin (n + 1) → Bool)}
    (hz : (0 : Fin (n + 1) → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R)
    (hc : ∀ j, IsPolymorphism (Cslib.parity 3) (cofactor R j false))
    {v : Fin (n + 1) → Bool} (hv : v ∈ R)
    (heven : Cslib.parityOn Finset.univ v = false) (j : Fin (n + 1)) : v j = true := by
  by_contra hh
  have hj : v j = false := Bool.eq_false_iff.mpr hh
  have hz' : (0 : Fin n → Bool) ∉ cofactor R j false := fun h =>
    hz ((Fin.insertNth_eq_iff.2 ⟨rfl, rfl⟩ : j.insertNth (α := fun _ => Bool) false 0 = 0) ▸ h)
  have hodd := parity_eq_true_of_units (hc j) hz'
    (fun i => show j.insertNth false (Pi.single i true) ∈ R from
      (insert_false_single j i).symm ▸ hu _)
    (hj ▸ remove_mem_cofactor hv j)
  simp only [Cslib.parityOn_eq_sum, Fin.sum_univ_succAbove _ j, hj, ← Bool.zero_eq_false,
    zero_add] at heven hodd
  exact Bool.false_ne_true (heven.symm.trans hodd)

/-- Every parity-failing Boolean relation has a binary parity-failing ordered minor. This
arbitrary-arity reconstruction uses actual projection/cofactor/twist traces. Affine separation
is used only to prove the even-tuple cancellation step, not as a gadget or minor oracle. -/
theorem exists_binary_parity_minor {R : Set (Fin m → Bool)}
    (h : ¬IsPolymorphism (Cslib.parity 3) R) :
    ∃ S : Set (Fin 2 → Bool), Nonempty (Trace R S) ∧ ¬IsPolymorphism (Cslib.parity 3) S ∧
      (0 : Fin 2 → Bool) ∉ S ∧ (∀ i, Pi.single i true ∈ S) := by
  obtain ⟨n, S, trace, hz, hb, ⟨a, ha, hout⟩, hmin⟩ :=
    exists_normalized_minimal_failure parity_translate h
  have hn : 2 ≤ n := not_lt.1 fun hh => hb (parity_preserves_of_arity_le_one (by omega))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp (j : Fin (n + 1)) : IsPolymorphism (Cslib.parity 3) (project S j) :=
    hmin n _ ⟨.project .refl j⟩ (by omega)
  have hc (j : Fin (n + 1)) (b : Bool) :
      IsPolymorphism (Cslib.parity 3) (cofactor S j b) :=
    hmin n _ ⟨.cofactor .refl j b⟩ (by omega)
  have hu := units_of_projection_closure hz a ha hout hp
  have heven_full {v : Fin (n + 1) → Bool} (hv : v ∈ S)
      (he : Cslib.parityOn Finset.univ v = false) : v = fun _ => true := by
    ext j
    exact proper_even_impossible hz hu (fun j => hc j false) hv he j
  obtain ⟨q, hq⟩ : ∃ k : Fin 3, Cslib.parityOn Finset.univ (a k) = false := by
    by_contra hh
    simp only [not_exists, Bool.not_eq_false] at hh
    have heq := (parity_three_pointwise a).symm.trans hout
    have he := congrArg (Cslib.parityOn Finset.univ) heq
    rw [Cslib.parityOn_add, Cslib.parityOn_add, hh, hh, hh, Cslib.parityOn_eq_sum] at he
    simp at he
  have hfull : (fun _ : Fin (n + 1) => true) ∈ S := heven_full (ha q) hq ▸ ha q
  have hefull : Cslib.parityOn Finset.univ (fun _ : Fin (n + 1) => true) = false := by
    rwa [heven_full (ha q) hq] at hq
  have hn2 : n + 1 = 2 := by
    by_contra hh
    have hmod : (n + 1) % 2 ≠ 1 := by simpa [Cslib.parityOn] using hefull
    have hn4 : 4 ≤ n + 1 := by lia
    let i : Fin (n + 1) := ⟨0, by lia⟩
    let j : Fin (n + 1) := ⟨1, by lia⟩
    let k : Fin (n + 1) := ⟨2, by lia⟩
    let l : Fin (n + 1) := ⟨3, by lia⟩
    let w : Fin (n + 1) → Bool := Pi.single i true + Pi.single j true + Pi.single k true
    have hw : w ∈ S := sum_three_mem_of_cofactor (hc l false) (hu i) (hu j) (hu k)
      (by simp [i, l, Bool.zero_eq_false]) (by simp [j, l, Bool.zero_eq_false])
      (by simp [k, l, Bool.zero_eq_false])
    have hv := sum_three_mem_of_cofactor (hc i true) hfull (hu i) hw
      rfl (Pi.single_eq_same i _) (by simp [w, i, j, k])
    have he : Cslib.parityOn Finset.univ
        ((fun _ : Fin (n + 1) => true) + Pi.single i true + w) = false := by
      simp [w, Cslib.parityOn_add, hefull, parityOn_single]
    have hj := congrFun (heven_full hv he) j
    simp [w, i, j, k] at hj
  obtain rfl : n = 1 := by omega
  exact ⟨S, trace, hb, hz, hu⟩

/-- A normalized binary parity failure has exactly the three nonzero tuples. In particular
the minimum-failure argument has not produced an empty or two-tuple relation. -/
theorem binary_parity_failure_eq {S : Set (Fin 2 → Bool)}
    (h : ¬IsPolymorphism (Cslib.parity 3) S) (hz : (0 : Fin 2 → Bool) ∉ S)
    (hu : ∀ i, Pi.single i true ∈ S) : S = {x | x ≠ 0} := by
  have rows (x : Fin 2 → Bool) : x = 0 ∨ x = Pi.single 0 true ∨
      x = Pi.single 1 true ∨ x = fun _ => true := by revert x; decide
  have hfull : (fun _ : Fin 2 => true) ∈ S := by
    by_contra hh
    have he : S = disequality := by
      ext x
      rcases rows x with rfl | rfl | rfl | rfl <;>
        simp [disequality, hz, hu, hh]
    rw [he] at h
    apply h
    intro a ha
    have hcol : (fun i => a i 0) = fun i => a i 1 + true := funext fun i => by
      simpa only [Bool.add_eq_xor, Bool.xor_true] using Bool.eq_not_of_ne (ha i)
    change Cslib.parity 3 (fun i => a i 0) ≠ Cslib.parity 3 (fun i => a i 1)
    rw [hcol, parity_translate, Bool.add_eq_xor, Bool.xor_true]
    exact (Bool.not_eq_self _).mp
  have hne0 : (fun _ : Fin 2 => true) ≠ 0 := by decide
  ext x
  rcases rows x with rfl | rfl | rfl | rfl <;> simp [hz, hu, hfull, hne0]

/-- Every relation failing ternary parity has an actual finite ordered trace to NAND.
Only projections, cofactors and single-port twists occur in the returned trace. -/
theorem exists_nand_trace {R : Set (Fin m → Bool)}
    (h : ¬IsPolymorphism (Cslib.parity 3) R) : Nonempty (Trace R nand) := by
  obtain ⟨S, ⟨trace⟩, hb, hz, hu⟩ := exists_binary_parity_minor h
  have ht : twist S (fun _ => true) = nand := by
    rw [binary_parity_failure_eq hb hz hu]
    ext x
    change (x + (fun _ => true) ≠ 0) ↔ ¬(x 0 = true ∧ x 1 = true)
    revert x
    decide
  exact ⟨ht ▸ trace.translate (fun _ => true)⟩

end Cslib.Logic.PL.CSP.RelationMinor
