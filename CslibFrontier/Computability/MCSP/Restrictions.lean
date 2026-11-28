/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CountingBound
public import CslibFrontier.Computability.Circuit.Support
public import CslibFrontier.Computability.MCSP.Basic
public import Mathlib.Data.Finset.Piecewise
import CslibFrontier.Computability.Circuit.Boolean.BinaryCost
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum

/-!
# Restrictions and two-corner lower bounds for quadratic MCSP

The two-corner certificate bound and quadratic-slice restriction analysis in this file are
original to this formalization, while [KabanetsCai2000] and [OliveiraPichSanthanam2019] are cited
for the MCSP and GapMCSP definitions and circuit counting.

Every circuit deciding exact MCSP at quadratic cutoff `s m = m ^ 2` accepts at most
`2 ^ descriptionBitBound m` truth tables (`card_accepting_mcspSquare_le`), using
`card_computableFunctions_le_two_pow` [KabanetsCai2000; OliveiraPichSanthanam2019]. In any
restriction around an accepted truth table, inessential free positions span an accepting subcube
(`pow_card_inessential_le`), yielding an `N - descriptionBitBound m - 1` size lower bound
(`mcspSquare_near_linear`).

Tracking backward certificate requests from both constant truth tables (`0^N` and `1^N`) shows
that disjoint input polarities cannot share input demands, while binary gates contribute at most
three distinct argument requests when demanded at both polarities (`CornerCertificates`), giving
the unconditional De Morgan circuit lower bound
`2 * 2 ^ m ≤ complexity interpretation (single (mcspSquare m)) + 1 + 2 * descriptionBitBound m`
(`mcspSquare_two_certificate_lower_bound`), and
`120277 ≤ complexity interpretation (single (mcspSquare 16))` (`mcspSquare_sixteen_lower_bound`).

## Main definitions

* `Cslib.MCSP.Restrictions.mcspSquare`: exact MCSP slice at gate cutoff `m ^ 2` on `2 ^ m` bits.
* `Cslib.MCSP.Restrictions.descriptionBitBound`: binary description bit bound
  `computableFunctionsLogBound m (m ^ 2)`.
* `Cslib.MCSP.Restrictions.CornerCertificates.selectedPins`,
  `Cslib.MCSP.Restrictions.CornerCertificates.cornerValue`,
  `Cslib.MCSP.Restrictions.CornerCertificates.Needed`,
  `Cslib.MCSP.Restrictions.CornerCertificates.cornerInputs`: two-corner backward certificate
  demands for the constant inputs `0^N` and `1^N`.

## Main results

* `Cslib.MCSP.Restrictions.pow_card_inessential_le`: inessential free positions in an accepting
  restriction generate an accepting subcube.
* `Cslib.MCSP.Restrictions.card_accepting_mcspSquare_le`: upper bound on accepted tables of
  `mcspSquare m`.
* `Cslib.MCSP.Restrictions.mcspSquare_near_linear`: near-linear gate lower bound `N - B(m) - 1`.
* `Cslib.MCSP.Restrictions.CornerCertificates.card_cornerInputs_le`,
  `Cslib.MCSP.Restrictions.CornerCertificates.agrees_on_cornerInputs`: combined two-corner input
  demand bound `g + 1` and soundness of corner input certificates.
* `Cslib.MCSP.Restrictions.mcspSquare_two_certificate_lower_bound`: unconditional two-corner
  lower bound `2 * N - 2 * B(m) - 1`.
* `Cslib.MCSP.Restrictions.mcspSquare_sixteen_lower_bound`: finite bound at `m = 16` (`120277`).

## References

* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

public section

namespace Cslib.MCSP.Restrictions

open Cslib.Circuits Cslib.Circuits.Boolean

section Restrictions

variable {n : ℕ}

/-- Subset of `free` coordinates that are essential for `f`. -/
noncomputable def essentialPositions (f : BitString n → Bool) (free : Finset (Fin n)) :
    Finset (Fin n) :=
  open scoped Classical in free.filter (EssentialAt f)

/-- Finset of all truth tables accepted by `f`. -/
noncomputable def acceptingTables (f : BitString n → Bool) : Finset (BitString n) :=
  Finset.univ.filter fun t => f t = true

/-- Membership in `acceptingTables f` characterizes accepted truth tables. -/
@[simp] theorem mem_acceptingTables {f : BitString n → Bool} {t : BitString n} :
    t ∈ acceptingTables f ↔ f t = true := by
  simp [acceptingTables]

/-- Inessential coordinates can be changed together without changing the result. -/
private theorem eq_of_agree_off {f : BitString n → Bool} (ignored : Finset (Fin n))
    (h : ∀ i ∈ ignored, ¬ EssentialAt f i) {x y : BitString n}
    (agree : ∀ i ∉ ignored, x i = y i) : f x = f y := by
  induction ignored using Finset.induction_on generalizing x with
  | empty =>
    have hxy : x = y := funext fun i => agree i (Finset.notMem_empty i)
    rw [hxy]
  | @insert i tail hiTail ih =>
    let next := Function.update x i (y i)
    have heq : f x = f next := by
      by_contra hne
      apply h i (Finset.mem_insert_self ..)
      exact ⟨x, next, fun j hj => by simp [next, Function.update_of_ne hj], hne⟩
    apply heq.trans
    apply ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [next]
    · simpa [next, Function.update_of_ne hji] using
        agree j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩)

/-- Inessential free positions in an accepting restriction generate an accepting subcube. -/
theorem pow_card_inessential_le (f : BitString n → Bool) (center : BitString n)
    (free : Finset (Fin n)) (hCenter : f center = true) :
    2 ^ (free \ essentialPositions (fun x => f (free.piecewise x center)) free).card ≤
      (acceptingTables f).card := by
  classical
  let restricted := fun x => f (free.piecewise x center)
  let ignored := free \ essentialPositions restricted free
  have hFree : ignored ⊆ free := Finset.sdiff_subset
  have hInessential : ∀ i ∈ ignored, ¬EssentialAt restricted i := by
    intro i hi he
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨hFree hi, he⟩)
  let table (bits : (i : ignored) → Bool) : BitString n :=
    fun i => if h : i ∈ ignored then bits ⟨i, h⟩ else center i
  have hAccept (bits : (i : ignored) → Bool) : table bits ∈ acceptingTables f := by
    have hAgree : ∀ i ∉ ignored, table bits i = center i := by
      intro i hi
      simp [table, hi]
    have hRestricted := eq_of_agree_off ignored hInessential hAgree
    have hTable : free.piecewise (table bits) center = table bits := by
      funext i
      by_cases hi : i ∈ free
      · simp [Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp [Finset.piecewise_eq_of_notMem _ _ _ hi, table,
          show i ∉ ignored from fun h => hi (hFree h)]
    have hSelf : free.piecewise center center = center := by
      funext i
      simp [Finset.piecewise]
    simpa [restricted, hTable, hSelf, acceptingTables, hCenter] using hRestricted
  let into (bits : (i : ignored) → Bool) : acceptingTables f := ⟨table bits, hAccept bits⟩
  have hInjective : Function.Injective into := by
    intro a b h
    funext i
    have hi := congrFun (congrArg Subtype.val h) i.val
    simpa [into, table, i.property] using hi
  change 2 ^ ignored.card ≤ (acceptingTables f).card
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using
    Fintype.card_le_of_injective into hInjective

end Restrictions

/-- The exact MCSP slice with a quadratic cutoff on the represented function's arity. -/
noncomputable def mcspSquare (m : ℕ) : BitString (2 ^ m) → Bool :=
  (GapMCSP.yesSet fun j => j ^ 2).slice (2 ^ m)

/-- Characterization of truth tables accepted by `mcspSquare m`. -/
@[simp] theorem mcspSquare_eq_true_iff (m : ℕ) (T : BitString (2 ^ m)) :
    mcspSquare m T = true ↔
      complexity interpretation (single ((MCSP.truthTable m).symm T)) ≤ m ^ 2 :=
  GapMCSP.slice_yesSet_eq_true_iff

/-- An upper bound on the number of binary digits needed to index the accepted tables. -/
abbrev descriptionBitBound (m : ℕ) : ℕ :=
  computableFunctionsLogBound m (m ^ 2)

/-- Sparsity upper bound on the accepted tables of `mcspSquare m`. -/
theorem card_accepting_mcspSquare_le (m : ℕ) :
    (acceptingTables (mcspSquare m)).card ≤ 2 ^ descriptionBitBound m := by
  have hAccepted : (↑(acceptingTables (mcspSquare m)) : Set (BitString (2 ^ m))) =
      {T | (⟨m, T, m ^ 2⟩ : MCSP.Instance) ∈ Cslib.MCSP} := by
    ext T
    simp [MCSP.mem_iff, MCSP.Instance.function]
  rw [← Set.ncard_coe_finset, hAccepted, MCSP.ncard_setOf_mem]
  exact card_computableFunctions_le_two_pow m (m ^ 2)

/-- Both constant truth tables are accepted by `mcspSquare m` for `1 ≤ m`. -/
theorem mcspSquare_constant_table (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    mcspSquare m (fun _ => b) = true := by
  rw [mcspSquare_eq_true_iff]
  change complexity interpretation (single (fun _ : BitString m => b)) ≤ m ^ 2
  rw [Boolean.complexity_const]
  exact Nat.one_le_pow _ _ hm

/-- Essential-coordinate lower bound for any accepting restriction of `mcspSquare m`. -/
theorem mcspSquare_restriction_loss (m : ℕ) (center : BitString (2 ^ m))
    (free : Finset (Fin (2 ^ m))) (accepted : mcspSquare m center = true) :
    free.card ≤
      (essentialPositions (fun x => mcspSquare m (free.piecewise x center)) free).card +
        descriptionBitBound m := by
  classical
  let ess := essentialPositions (fun x => mcspSquare m (free.piecewise x center)) free
  have hPow := (pow_card_inessential_le (mcspSquare m) center free accepted).trans
    (card_accepting_mcspSquare_le m)
  change 2 ^ (free \ ess).card ≤ 2 ^ descriptionBitBound m at hPow
  have hLost := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPow
  have hSubset : ess ⊆ free := Finset.filter_subset _ _
  have hParts := Finset.card_sdiff_add_card_eq_card hSubset
  change free.card ≤ ess.card + descriptionBitBound m
  omega

/-- A near-linear lower bound in `N = 2^m`, with an explicit `O(m^2 log m)` loss. -/
theorem mcspSquare_near_linear (m : ℕ) (hm : 1 ≤ m) :
    2 ^ m ≤ complexity interpretation (single (mcspSquare m)) + 1 + descriptionBitBound m := by
  classical
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  have hRestricted := mcspSquare_restriction_loss m (fun _ => false) Finset.univ
    (mcspSquare_constant_table m hm false)
  have hUniv : (fun x => mcspSquare m (Finset.univ.piecewise x fun _ => false)) =
      mcspSquare m := by
    funext x
    exact congrArg (mcspSquare m)
      (funext fun i => Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_univ i))
  rw [hUniv] at hRestricted
  simp only [Finset.card_univ, Fintype.card_fin] at hRestricted
  have hEss : ∀ i ∈ essentialPositions (mcspSquare m) Finset.univ,
      EssentialAt (single (mcspSquare m)) i := by
    intro i hi
    obtain ⟨x, y, hxy, hne⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨x, y, hxy, fun h => hne (congrFun h 0)⟩
  have hCard := (c.essential_le_cost_binaryCost hc hEss).trans
    (Nat.add_le_add_left c.program.cost_binaryCost_le 1)
  change 2 ^ m ≤ (essentialPositions (mcspSquare m) Finset.univ).card +
    descriptionBitBound m at hRestricted
  omega

namespace CornerCertificates

/-- Select argument pins sufficient to certify a gate's value at an assignment. -/
@[expose] def selectedPins :
    (op : Op) → (Fin (signature.Arity op) → Bool) → Finset (Fin (signature.Arity op))
  | .const _, _ => ∅
  | .not, _ => {0}
  | .and, x => if x 0 then (if x 1 then Finset.univ else {1}) else {0}
  | .or, x => if x 0 then {0} else (if x 1 then {1} else Finset.univ)

/-- Agreeing on `selectedPins op x` certifies `interpretation op y = interpretation op x`. -/
theorem agrees_of_selectedPins (op : Op) (x y : Fin (signature.Arity op) → Bool)
    (h : ∀ a ∈ selectedPins op x, y a = x a) : interpretation op y = interpretation op x := by
  cases op with
  | const b => rfl
  | not => simpa [interpretation] using congrArg Bool.not (h 0 (by simp [selectedPins]))
  | and | or =>
    cases hx₀ : x 0 <;> cases hx₁ : x 1 <;>
      simp_all [selectedPins, interpretation, Fin.forall_fin_two]

private def argumentStates {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x : Fin (signature.Arity op) → Bool) :
    Finset (W × Bool) :=
  (selectedPins op x).image fun a => (sources a, x a)

private theorem card_argumentStates_le {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x : Fin (signature.Arity op) → Bool) :
    (argumentStates op sources x).card ≤ 2 :=
  Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by cases op <;> simp))

private theorem union_bound_of_short {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x y : Fin (signature.Arity op) → Bool)
    (b : Bool)
    (hshort : ∀ z, interpretation op z = b → (argumentStates op sources z).card ≤ 1)
    (hunique : ∀ z z', interpretation op z ≠ b → interpretation op z' ≠ b → z = z') :
    (argumentStates op sources x ∪ argumentStates op sources y).card ≤
      if interpretation op x = interpretation op y then 2 else 3 := by
  have hx := card_argumentStates_le op sources x
  have hy := card_argumentStates_le op sources y
  have hu := Finset.card_union_le (argumentStates op sources x) (argumentStates op sources y)
  by_cases hx' : interpretation op x = b <;> by_cases hy' : interpretation op y = b
  · rw [ite_eq_left (hx'.trans hy'.symm)]
    exact hu.trans (Nat.add_le_add (hshort x hx') (hshort y hy'))
  · rw [ite_eq_right (fun h => hy' (h.symm.trans hx'))]
    exact hu.trans (Nat.add_le_add (hshort x hx') hy)
  · rw [ite_eq_right (fun h => hx' (h.trans hy'))]
    exact hu.trans (Nat.add_le_add hx (hshort y hy'))
  · obtain rfl := hunique x y hx' hy'
    simpa using hx

private theorem union_bound {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x y : Fin (signature.Arity op) → Bool) :
    (argumentStates op sources x ∪ argumentStates op sources y).card ≤
      if interpretation op x = interpretation op y then 2 else 3 := by
  cases op with
  | const b => simp [argumentStates, selectedPins]
  | not =>
    have hcard (z : Fin 1 → Bool) : (argumentStates .not sources z).card ≤ 1 := by
      simp [argumentStates, selectedPins]
    have hu := (Finset.card_union_le _ _).trans (Nat.add_le_add (hcard x) (hcard y))
    split <;> omega
  | and =>
    apply union_bound_of_short _ _ _ _ false
    · intro z hz
      apply Finset.card_image_le.trans
      cases hz₀ : z 0 <;> cases hz₁ : z 1 <;> simp_all [selectedPins, interpretation]
    · intro z z' hz hz'
      simp only [Bool.not_eq_false, interpretation, Bool.and_eq_true] at hz hz'
      exact funext (Fin.forall_fin_two.2 ⟨hz.1.trans hz'.1.symm, hz.2.trans hz'.2.symm⟩)
  | or =>
    apply union_bound_of_short _ _ _ _ true
    · intro z hz
      apply Finset.card_image_le.trans
      cases hz₀ : z 0 <;> cases hz₁ : z 1 <;> simp_all [selectedPins, interpretation]
    · intro z z' hz hz'
      simp only [Bool.not_eq_true, interpretation, Bool.or_eq_false_iff] at hz hz'
      exact funext (Fin.forall_fin_two.2 ⟨hz.1.trans hz'.1.symm, hz.2.trans hz'.2.symm⟩)

variable {n g : ℕ}

/-- Value of wire `w` when every input is set to the constant `b`. -/
@[expose] def cornerValue (p : Program signature n g) (b : Bool) (w : Wire n g) : Bool :=
  p.trace interpretation (fun _ => b) w

private def cornerArguments (p : Program signature n g) (k : Fin g) (b : Bool) :
    Finset (Wire n g × Bool) :=
  argumentStates (p.lines k).op (p.lines k).wires
    (fun a => cornerValue p b ((p.lines k).wires a))

private theorem cornerValue_gate (p : Program signature n g) (b : Bool) (k : Fin g) :
    cornerValue p b (.gate k) = interpretation (p.lines k).op
      (fun a => cornerValue p b ((p.lines k).wires a)) :=
  p.trace_gate interpretation (fun _ => b) k

/-- Follow the certificates for both constant inputs. A common `(wire, value)` pair is shared. -/
inductive Needed (p : Program signature n g) (root : Wire n g) : Wire n g × Bool → Prop where
  | output : Needed p root (root, true)
  | argument {k : Fin g} {b : Bool} (h : Needed p root (.gate k, cornerValue p b (.gate k)))
      {a : Fin (signature.Arity (p.lines k).op)}
      (ha : a ∈ selectedPins (p.lines k).op
        (fun j => cornerValue p b ((p.lines k).wires j))) :
      Needed p root ((p.lines k).wires a, cornerValue p b ((p.lines k).wires a))

private noncomputable def neededStates (p : Program signature n g) (root : Wire n g) :
    Finset (Wire n g × Bool) :=
  open scoped Classical in Finset.univ.filter (Needed p root)

private noncomputable def neededValues (p : Program signature n g) (root : Wire n g)
    (w : Wire n g) : Finset Bool :=
  open scoped Classical in Finset.univ.filter fun b => Needed p root (w, b)

/-- Input coordinates whose constant value `b` is needed by a corner certificate. -/
noncomputable def cornerInputs (p : Program signature n g) (root : Wire n g) (b : Bool) :
    Finset (Fin n) :=
  open scoped Classical in Finset.univ.filter fun i => Needed p root (.input i, b)

open scoped Classical in
private noncomputable def requestedArguments (p : Program signature n g) (root : Wire n g)
    (k : Fin g) : Finset (Wire n g × Bool) :=
  (if Needed p root (.gate k, cornerValue p false (.gate k)) then cornerArguments p k false
    else ∅) ∪
    (if Needed p root (.gate k, cornerValue p true (.gate k)) then cornerArguments p k true
      else ∅)

private theorem card_requestedArguments_le (p : Program signature n g) (root : Wire n g)
    (k : Fin g) :
    (requestedArguments p root k).card ≤ (neededValues p root (.gate k)).card + 1 := by
  classical
  let v₀ := cornerValue p false (.gate k)
  let v₁ := cornerValue p true (.gate k)
  let S := neededValues p root (.gate k)
  have hv (b : Bool) : b ∈ S ↔ Needed p root (.gate k, b) := by simp [S, neededValues]
  have hOne (b : Bool) : (cornerArguments p k b).card ≤ 2 := card_argumentStates_le ..
  have hUnion : (cornerArguments p k false ∪ cornerArguments p k true).card ≤
      if v₀ = v₁ then 2 else 3 := by
    have h := union_bound (p.lines k).op (p.lines k).wires
      (fun a => cornerValue p false ((p.lines k).wires a))
      (fun a => cornerValue p true ((p.lines k).wires a))
    simpa only [v₀, v₁, cornerArguments, cornerValue_gate] using h
  change ((if Needed p root (.gate k, v₀) then cornerArguments p k false else ∅) ∪
    (if Needed p root (.gate k, v₁) then cornerArguments p k true else ∅)).card ≤ S.card + 1
  by_cases h0 : Needed p root (.gate k, v₀) <;>
    by_cases h1 : Needed p root (.gate k, v₁) <;>
    simp only [h0, h1, ↓reduceIte, Finset.union_empty, Finset.empty_union,
      Finset.card_empty, Nat.zero_le]
  · by_cases heq : v₀ = v₁
    · have hcard := Finset.card_pos.mpr ⟨v₀, (hv _).mpr h0⟩
      simp only [heq, ↓reduceIte] at hUnion
      omega
    · have hset : ({v₀, v₁} : Finset Bool) ⊆ S := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact (hv _).mpr h0
        · exact (hv _).mpr h1
      have hcard := Finset.card_le_card hset
      simp only [heq, ↓reduceIte] at hUnion
      simp only [Finset.card_insert_of_notMem (by simp [heq] : v₀ ∉ ({v₁} : Finset Bool)),
        Finset.card_singleton] at hcard
      omega
  · have hcard := Finset.card_pos.mpr ⟨v₀, (hv _).mpr h0⟩
    have hh := hOne false
    omega
  · have hcard := Finset.card_pos.mpr ⟨v₁, (hv _).mpr h1⟩
    have hh := hOne true
    omega

open scoped Classical in
private theorem card_stateSet (marked : Wire n g × Bool → Prop) :
    (Finset.univ.filter marked).card =
      (Finset.univ.filter fun i => marked (.input i, false)).card +
        (Finset.univ.filter fun i => marked (.input i, true)).card +
        ∑ k : Fin g, (Finset.univ.filter fun b => marked (.gate k, b)).card := by
  let stateSet := Finset.univ.filter marked
  let stateValues (w : Wire n g) : Finset Bool := Finset.univ.filter fun b => marked (w, b)
  let stateInputs (b : Bool) : Finset (Fin n) := Finset.univ.filter fun i => marked (.input i, b)
  let counts := fun w : Wire n g => (stateValues w).card
  have hMap : (Finset.univ.sigma stateValues).map
      (Equiv.sigmaEquivProd (Wire n g) Bool).toEmbedding = stateSet := by
    ext key
    rw [Finset.mem_map_equiv]
    simp [Equiv.sigmaEquivProd, stateValues, stateSet]
  have hCard := congrArg Finset.card hMap
  rw [Finset.card_map, Finset.card_sigma] at hCard
  change ∑ w : Wire n g, counts w = stateSet.card at hCard
  have hSplit : ∑ w : Wire n g, counts w = (∑ i : Fin n, counts (.input i)) +
      ∑ k : Fin g, counts (.gate k) := by
    rw [← (Wire.equiv n g).symm.sum_comp counts, Fintype.sum_sum_type]
    rfl
  have hInputs : (∑ i : Fin n, counts (.input i)) =
      (stateInputs false).card + (stateInputs true).card := by
    simp only [counts, stateValues, stateInputs, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm, Fintype.sum_bool]
    exact Nat.add_comm ..
  exact hCard.symm.trans (hSplit.trans (congrArg (· + ∑ k : Fin g, counts (.gate k)) hInputs))

private theorem card_neededStates (p : Program signature n g) (root : Wire n g) :
    (neededStates p root).card = (cornerInputs p root false).card +
      (cornerInputs p root true).card + ∑ k : Fin g, (neededValues p root (.gate k)).card := by
  classical
  simpa [neededStates, cornerInputs, neededValues] using card_stateSet (Needed p root)

/-- Total input corner demands for both constant inputs are bounded by `g + 1`. -/
theorem card_cornerInputs_le (p : Program signature n g) (root : Wire n g) :
    (cornerInputs p root false).card + (cornerInputs p root true).card ≤ g + 1 := by
  classical
  let allArgs := (Finset.univ : Finset (Fin g)).biUnion (requestedArguments p root)
  have hSub : neededStates p root ⊆ insert (root, true) allArgs := by
    intro key hKey
    have hKey' : Needed p root key := (Finset.mem_filter.mp hKey).2
    induction hKey' with
    | output => exact Finset.mem_insert_self ..
    | @argument k b h a ha =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_univ _, ?_⟩
      have hArg : ((p.lines k).wires a, cornerValue p b ((p.lines k).wires a)) ∈
          cornerArguments p k b :=
        Finset.mem_image.mpr ⟨a, ha, rfl⟩
      cases b
      · simpa [requestedArguments, h] using Finset.mem_union_left _ hArg
      · simpa [requestedArguments, h] using Finset.mem_union_right _ hArg
  have hSize := Finset.card_le_card hSub
  have hDistinct : allArgs.card ≤ ∑ k : Fin g, (requestedArguments p root k).card :=
    Finset.card_biUnion_le
  have hSum : (∑ k : Fin g, (requestedArguments p root k).card) ≤
      ∑ k : Fin g, ((neededValues p root (.gate k)).card + 1) :=
    Finset.sum_le_sum fun k _ => card_requestedArguments_le p root k
  have hInsert := Finset.card_insert_le (root, true) allArgs
  rw [card_neededStates] at hSize
  have hSum' : (∑ k : Fin g, (requestedArguments p root k).card) ≤
      (∑ k : Fin g, (neededValues p root (.gate k)).card) + g := by
    simpa [Finset.sum_add_distrib] using hSum
  omega

/-- Agreeing on the needed corner inputs forces the circuit output to `true`. -/
theorem agrees_on_cornerInputs (p : Program signature n g) (root : Wire n g) (b : Bool)
    (hRoot : cornerValue p b root = true) (x : BitString n)
    (agree : ∀ i ∈ cornerInputs p root b, x i = b) : p.trace interpretation x root = true := by
  classical
  have hTrace : ∀ w, Needed p root (w, cornerValue p b w) →
      p.trace interpretation x w = cornerValue p b w := by
    intro w
    refine p.wire_induction (P := fun w => Needed p root (w, cornerValue p b w) →
      p.trace interpretation x w = cornerValue p b w) ?_ ?_ w
    · intro i hi
      exact agree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro k ih hk
      rw [p.trace_gate, cornerValue_gate]
      apply agrees_of_selectedPins
      intro a ha
      exact ih a (Needed.argument hk ha)
  exact (hTrace root (hRoot.symm ▸ Needed.output)).trans hRoot

end CornerCertificates

open CornerCertificates

private theorem mcspSquare_cornerInputs_bound (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (b : Bool) : 2 ^ m ≤ (cornerInputs c.program (c.outputs 0) b).card + descriptionBitBound m := by
  classical
  let fixed := cornerInputs c.program (c.outputs 0) b
  let free := Finset.univ \ fixed
  let center : BitString (2 ^ m) := fun _ => b
  have hCenter : mcspSquare m center = true := mcspSquare_constant_table m hm b
  have hRoot : cornerValue c.program b (c.outputs 0) = true := by
    change c.eval interpretation center 0 = true
    exact (congrFun (hc center) 0).trans hCenter
  have hAll (x : BitString (2 ^ m)) : mcspSquare m (free.piecewise x center) = true := by
    have hTrace := agrees_on_cornerInputs c.program (c.outputs 0) b hRoot
      (free.piecewise x center) (fun i hi => by
        have hNot : i ∉ free := fun h => (Finset.mem_sdiff.mp h).2 hi
        simp [Finset.piecewise_eq_of_notMem _ _ _ hNot, center])
    change c.eval interpretation (free.piecewise x center) 0 = true at hTrace
    rw [hc] at hTrace
    exact hTrace
  have hEmpty :
      essentialPositions (fun x => mcspSquare m (free.piecewise x center)) free = ∅ := by
    ext i
    simp [essentialPositions, EssentialAt, hAll]
  have hLoss := mcspSquare_restriction_loss m center free hCenter
  rw [hEmpty, Finset.card_empty, Nat.zero_add] at hLoss
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ fixed)
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  change free.card + fixed.card = 2 ^ m at hSplit
  change 2 ^ m ≤ fixed.card + descriptionBitBound m
  omega

/-- Near twice the truth-table length, with an explicit loss of order `m^2 log m`. -/
theorem mcspSquare_two_certificate_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    2 * 2 ^ m ≤ complexity interpretation (single (mcspSquare m)) +
      1 + 2 * descriptionBitBound m := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  have h0 := mcspSquare_cornerInputs_bound m hm c hc false
  have h1 := mcspSquare_cornerInputs_bound m hm c hc true
  have hSum := card_cornerInputs_le c.program (c.outputs 0)
  omega

/-- Finite circuit size lower bound for `mcspSquare 16` (`N = 65536`, cutoff `256`). -/
theorem mcspSquare_sixteen_lower_bound :
    120277 ≤ complexity interpretation (single (mcspSquare 16)) := by
  have h := mcspSquare_two_certificate_lower_bound 16 (by decide)
  have hBits : descriptionBitBound 16 = 5397 := by decide
  rw [hBits] at h
  omega

end Cslib.MCSP.Restrictions
