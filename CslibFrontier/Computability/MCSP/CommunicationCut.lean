/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ShannonConstruction
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.MCSP.Restrictions
import CslibFrontier.Computability.Circuit.Boolean.Synthesis

/-!
# Communication cuts for quadratic MCSP

The balanced equality-cut construction and crossing-wire lower bound in this file are original
to this formalization, while [KushilevitzNisan1997] and [OliveiraPichSanthanam2019] are cited for
the fooling-set method and MCSP context.

A balanced partition of the `2 ^ (r + s + 1)` truth-table positions (`card_mask_side`), indexed by
an `r`-bit prefix, a split bit, and an `s`-bit suffix via a selector `h : BooleanFunction s`,
embeds `2 ^ r`-bit equality into `mcspSquare (r + (s + 1))` whenever `2 ^ r`-input prefix functions
fit the quadratic gate budget and `2 ^ r + 2 ^ r + descriptionBitBound (r + (s + 1)) < 2 ^ s`
(`exists_equality_restriction`).

At arity `m = 32` (`r = 9`, `s = 22`), Shannon synthesis constructs every `9`-bit prefix function
within the `1024`-gate cutoff (`probe_is_accepted_shannon`), embedding `512`-bit equality across
the balanced cut (`mcspSquare_32_equality_cut`). Any deterministic protocol solving this restricted
problem requires depth at least `513` (`protocol_depth_lower_bound`), and any placement of the
gates in a De Morgan circuit computing `mcspSquare 32` consistent with the input partition forces
at least `512` distinct crossing wires (`mcspSquare_32_crossing_cut`).

## Main definitions

* `Cslib.MCSP.CommunicationCut.position`, `Cslib.MCSP.CommunicationCut.probe`,
  `Cslib.MCSP.CommunicationCut.mask`, `Cslib.MCSP.CommunicationCut.splice`: prefix-split-suffix
  indexing and balanced cut splicing.
* `Cslib.MCSP.CommunicationCut.badSelectors`: suffix selectors on which some mixed splice of two
  distinct prefix probes is accepted by `mcspSquare`.
* `Cslib.MCSP.CommunicationCut.crossingWires`: distinct source wires feeding a gate on the
  opposite side of a circuit partition.

## Main results

* `Cslib.MCSP.CommunicationCut.card_mask_side`: every mask `mask r h` splits the `2 ^ (r + s + 1)`
  truth-table positions into two balanced halves of size `2 ^ (r + s)`.
* `Cslib.MCSP.CommunicationCut.exists_equality_restriction`: equality embedding across a good
  balanced selector cut.
* `Cslib.MCSP.CommunicationCut.mcspSquare_32_equality_cut`: `512`-bit equality cut at `m = 32`.
* `Cslib.MCSP.CommunicationCut.protocol_depth_lower_bound`: deterministic communication depth
  lower bound (`2 ^ r + 1`) via `card_lt_two_pow_of_run_eq_equality`.
* `Cslib.MCSP.CommunicationCut.crossingWires_lower_bound`: at least `2 ^ r` crossing wires for
  every circuit gate placement.
* `Cslib.MCSP.CommunicationCut.mcspSquare_32_crossing_cut`: concrete `512`-wire cut lower bound
  at arity `32`.

## References

* [E. Kushilevitz, N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

public section

namespace Cslib.MCSP.CommunicationCut

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication Cslib.MCSP.Restrictions

variable {r s n : ℕ}

/-- Positions are indexed by a prefix, a split bit, and a suffix. -/
def position (a : BitString r) (b : Bool) (t : BitString s) :
    Fin (2 ^ (r + (s + 1))) :=
  BitString.equivFin _ (Fin.append a (Fin.cons b t))

private def positionEquiv (r s : ℕ) :
    BitString r × Bool × BitString s ≃ Fin (2 ^ (r + (s + 1))) :=
  (((Equiv.refl (BitString r)).prodCongr (Fin.consEquiv (fun _ : Fin (s + 1) => Bool))).trans
    (Fin.appendEquiv r (s + 1))).trans (BitString.equivFin _)

/-- Repeat the table of a function on the prefix across all split bits and suffixes. -/
def probe (s : ℕ) (f : BooleanFunction r) : BitString (2 ^ (r + (s + 1))) :=
  MCSP.truthTable _ (fun x => f (x ∘ Fin.castAdd (s + 1)))

/-- Pick one position from each pair that differs only in the split bit. -/
def mask (r : ℕ) (h : BooleanFunction s) : BitString (2 ^ (r + (s + 1))) :=
  MCSP.truthTable _ (fun x => x (Fin.natAdd r (0 : Fin (s + 1))) ^^
    h (fun j => x (Fin.natAdd r j.succ)))

/-- Select entries from `x` where `selector` is `true` and from `y` otherwise. -/
@[expose] def splice (selector x y : BitString n) : BitString n :=
  fun i => if selector i then x i else y i

/-- Splicing a table with itself returns that table. -/
@[simp] theorem splice_self (selector x : BitString n) : splice selector x x = x := by
  funext i
  simp [splice]

/-- Value of a prefix probe at `(a, b, t)`. -/
@[simp] theorem probe_at_position (f : BooleanFunction r) (a : BitString r) (b : Bool)
    (t : BitString s) : probe s f (position a b t) = f a := by
  simp [probe, position, Function.comp_def]

/-- Value of a cut mask at `(a, b, t)`. -/
@[simp] theorem mask_at_position (h : BooleanFunction s) (a : BitString r) (b : Bool)
    (t : BitString s) : mask r h (position a b t) = (b ^^ h t) := by
  simp only [mask, position, MCSP.truthTable_apply, Equiv.symm_apply_apply]
  congr 1
  · simp [Fin.append_right]
  · congr 1
    funext j
    simp [Fin.append_right]

open scoped Classical in
/-- Each side of `mask r h` contains exactly `2 ^ (r + s)` truth-table positions. -/
theorem card_mask_side (h : BooleanFunction s) (side : Bool) :
    ((Finset.univ : Finset (Fin (2 ^ (r + (s + 1))))).filter
      (fun i => mask r h i = side)).card = 2 ^ (r + s) := by
  classical
  let pick (q : BitString r × BitString s) := position q.1 (side ^^ h q.2) q.2
  have hPick (q : BitString r × BitString s) : mask r h (pick q) = side := by
    change mask r h (position q.1 (side ^^ h q.2) q.2) = side
    rw [mask_at_position]
    cases side <;> cases h q.2 <;> rfl
  have hinj : Function.Injective pick := by
    intro a b hab
    change positionEquiv r s (a.1, side ^^ h a.2, a.2) =
      positionEquiv r s (b.1, side ^^ h b.2, b.2) at hab
    have heq := (positionEquiv r s).injective hab
    exact Prod.ext (congrArg (fun x : BitString r × Bool × BitString s => x.1) heq)
      (congrArg (fun x : BitString r × Bool × BitString s => x.2.2) heq)
  have hImage : Finset.univ.image pick =
      Finset.univ.filter (fun i => mask r h i = side) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, rfl⟩
      exact hPick q
    · intro hi
      obtain ⟨⟨a, b, t⟩, rfl⟩ := (positionEquiv r s).surjective i
      change mask r h (position a b t) = side at hi
      rw [mask_at_position] at hi
      have xor_inv (x y z : Bool) (hxy : (x ^^ y) = z) : (z ^^ y) = x := by
        cases x <;> cases y <;> cases z <;> simp_all
      exact ⟨(a, t), congrArg (fun v => position a v t) (xor_inv b (h t) side hi)⟩
  rw [← hImage, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    BitString.card, BitString.card, pow_add]

/-- Every prefix probe is accepted by `mcspSquare` when the DNF synthesis budget fits. -/
theorem probe_is_accepted (f : BooleanFunction r)
    (budget : 2 ^ r * (2 * r + 2) + 1 ≤ (r + (s + 1)) ^ 2) :
    mcspSquare (r + (s + 1)) (probe s f) = true := by
  rw [mcspSquare_eq_true_iff, probe, Equiv.symm_apply_apply]
  exact (Synthesis.selected (Fin.castAdd (s + 1)) f).complexity_le.trans budget

/-- The Shannon synthesis construction also gives accepted prefix probes at a smaller budget. -/
theorem probe_is_accepted_shannon {k d : ℕ} (f : BooleanFunction (k + d))
    (budget : ShannonSynthesis.bound k d ≤ (k + d + (s + 1)) ^ 2) :
    mcspSquare (k + d + (s + 1)) (probe s f) = true := by
  let c := ShannonSynthesis.circuit f
  let select : Fin (k + d) → Fin (k + d + (s + 1)) := Fin.castAdd (s + 1)
  let lifted := c.comp (Circuit.wiring signature select)
  have hc : lifted.Computes interpretation (single fun x => f (x ∘ select)) := by
    intro x
    funext o
    simp [lifted, c, Circuit.eval_comp, Circuit.eval_wiring]
  have hSize : lifted.size ≤ ShannonSynthesis.bound k d := by
    simpa [lifted, c, Circuit.size_comp] using ShannonSynthesis.size_circuit_le f
  rw [mcspSquare_eq_true_iff, probe, Equiv.symm_apply_apply]
  exact (complexity_le_of_computes lifted hc).trans (hSize.trans budget)

private theorem splice_injective_in_mask {f g : BooleanFunction r} (hne : f ≠ g) :
    Function.Injective
      (fun h : BooleanFunction s => splice (mask r h) (probe s f) (probe s g)) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ g a := by
    by_contra! h
    exact hne (funext h)
  intro h₀ h₁ hEq
  funext t
  have ht := congrFun hEq (position a false t)
  simp only [splice, mask_at_position, Bool.false_xor, probe_at_position] at ht
  cases h₀t : h₀ t <;> cases h₁t : h₁ t
  · rfl
  · simp only [h₀t, h₁t, Bool.false_eq_true, ↓reduceIte] at ht
    exact absurd ht.symm ha
  · simp only [h₀t, h₁t, Bool.false_eq_true, ↓reduceIte] at ht
    exact absurd ht ha
  · rfl

private theorem card_functions (k : ℕ) : Fintype.card (BooleanFunction k) = 2 ^ 2 ^ k := by
  classical
  simp

private noncomputable def badMasks (s : ℕ) (pair : BooleanFunction r × BooleanFunction r) :
    Finset (BooleanFunction s) :=
  open scoped Classical in
  if pair.1 = pair.2 then ∅ else Finset.univ.filter fun h =>
    mcspSquare (r + (s + 1)) (splice (mask r h) (probe s pair.1) (probe s pair.2)) = true

private theorem card_badMasks_le (pair : BooleanFunction r × BooleanFunction r) :
    (badMasks s pair).card ≤ 2 ^ descriptionBitBound (r + (s + 1)) := by
  classical
  by_cases heq : pair.1 = pair.2
  · simp [badMasks, heq]
  · apply le_trans _ (card_accepting_mcspSquare_le (r + (s + 1)))
    apply Finset.card_le_card_of_injOn
      (fun h => splice (mask r h) (probe s pair.1) (probe s pair.2))
    · intro h hh
      simp only [SetLike.mem_coe, mem_acceptingTables]
      simp only [SetLike.mem_coe, badMasks, ite_eq_right heq, Finset.mem_filter, Finset.mem_univ,
        true_and] at hh
      exact hh
    · intro h₁ _ h₂ _ h
      exact splice_injective_in_mask heq h

/-- Union of bad selectors across all ordered pairs of `r`-bit prefix functions. -/
noncomputable def badSelectors (r s : ℕ) : Finset (BooleanFunction s) :=
  open scoped Classical in
  (Finset.univ : Finset (BooleanFunction r × BooleanFunction r)).biUnion (badMasks s)

/-- Union bound on the number of bad suffix selectors. -/
theorem card_badSelectors_le (r s : ℕ) :
    (badSelectors r s).card ≤ 2 ^ (2 ^ r + 2 ^ r + descriptionBitBound (r + (s + 1))) := by
  classical
  let pairs := (Finset.univ : Finset (BooleanFunction r × BooleanFunction r))
  have hpairs : pairs.card = 2 ^ (2 ^ r + 2 ^ r) := by
    simp [pairs, Fintype.card_prod, pow_add]
  calc
    _ ≤ ∑ pair ∈ pairs, (badMasks s pair).card := Finset.card_biUnion_le
    _ ≤ ∑ _pair ∈ pairs, 2 ^ descriptionBitBound (r + (s + 1)) :=
      Finset.sum_le_sum fun pair _ => card_badMasks_le pair
    _ = _ := by simp [Finset.sum_const, hpairs, pow_add, Nat.mul_assoc]

private theorem separates_of_notMem_badSelectors {selector : BooleanFunction s}
    (hSelector : selector ∉ badSelectors r s) (f g : BooleanFunction r) (hfg : f ≠ g) :
    mcspSquare (r + (s + 1)) (splice (mask r selector) (probe s f) (probe s g)) = false := by
  classical
  cases hResult : mcspSquare (r + (s + 1)) (splice (mask r selector) (probe s f) (probe s g)) with
  | false => rfl
  | true =>
    exfalso
    apply hSelector
    apply Finset.mem_biUnion.mpr
    refine ⟨(f, g), Finset.mem_univ _, ?_⟩
    simp only [badMasks, ite_eq_right hfg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hResult

private theorem exists_notMem_badSelectors
    (gap : 2 ^ r + 2 ^ r + descriptionBitBound (r + (s + 1)) < 2 ^ s) :
    ∃ h : BooleanFunction s, h ∉ badSelectors r s := by
  classical
  let bad := badSelectors r s
  have huniv : (Finset.univ : Finset (BooleanFunction s)).card = 2 ^ 2 ^ s := by
    rw [Finset.card_univ, card_functions]
  have hlt : bad.card < (Finset.univ : Finset (BooleanFunction s)).card := by
    rw [huniv]
    exact (card_badSelectors_le r s).trans_lt (Nat.pow_lt_pow_right (by decide) gap)
  by_contra! hall
  have heq : bad = Finset.univ := Finset.eq_univ_of_forall hall
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

/-- Evaluation of `mcspSquare` on the splice of two prefix probes across `mask r h`. -/
noncomputable def mixedTest (h : BooleanFunction s) (f g : BooleanFunction r) : Bool :=
  mcspSquare (r + (s + 1)) (splice (mask r h) (probe s f) (probe s g))

private theorem equality_restriction_of_notMem_badSelectors {h : BooleanFunction s}
    (accepted : ∀ f : BooleanFunction r, mcspSquare (r + (s + 1)) (probe s f) = true)
    (hGood : h ∉ badSelectors r s) (f g : BooleanFunction r) : mixedTest h f g = true ↔ f = g := by
  constructor
  · intro hTrue
    by_contra hf
    have hFalse := separates_of_notMem_badSelectors hGood f g hf
    simp only [mixedTest, hFalse, Bool.false_eq_true] at hTrue
  · rintro rfl
    rw [mixedTest, splice_self]
    exact accepted _

/-- Accepted prefix probes and a counting gap suffice to embed equality across the cut. -/
theorem exists_equality_restriction_of_accepted
    (accepted : ∀ f : BooleanFunction r, mcspSquare (r + (s + 1)) (probe s f) = true)
    (gap : 2 ^ r + 2 ^ r + descriptionBitBound (r + (s + 1)) < 2 ^ s) :
    ∃ h : BooleanFunction s, ∀ f g : BooleanFunction r, mixedTest h f g = true ↔ f = g := by
  obtain ⟨h, hGood⟩ := exists_notMem_badSelectors gap
  exact ⟨h, equality_restriction_of_notMem_badSelectors accepted hGood⟩

/-- Exact equality on `2^r` bits embeds in MCSP across a balanced partition. -/
theorem exists_equality_restriction
    (budget : 2 ^ r * (2 * r + 2) + 1 ≤ (r + (s + 1)) ^ 2)
    (gap : 2 ^ r + 2 ^ r + descriptionBitBound (r + (s + 1)) < 2 ^ s) :
    ∃ h : BooleanFunction s, ∀ f g : BooleanFunction r, mixedTest h f g = true ↔ f = g :=
  exists_equality_restriction_of_accepted (fun f => probe_is_accepted f budget) gap

/-- The equal-prefix pairs force deterministic communication depth at least `2^r + 1`. -/
theorem protocol_depth_lower_bound (h : BooleanFunction s)
    (hEq : ∀ f g : BooleanFunction r, mixedTest h f g = true ↔ f = g)
    (p : Protocol (BooleanFunction r) (BooleanFunction r) Bool) (hp : p.run = mixedTest h) :
    2 ^ r + 1 ≤ p.depth := by
  classical
  have hCard : 1 < Fintype.card (BooleanFunction r) :=
    Fintype.one_lt_card_iff.mpr ⟨fun _ => false, fun _ => true,
      fun heq => Bool.false_ne_true (congrFun heq (fun _ => false))⟩
  have hRun : p.run = equality := by
    refine hp.trans ?_
    funext f g
    exact Bool.eq_iff_iff.mpr ((hEq f g).trans (by simp [equality]))
  have hDepth := card_lt_two_pow_of_run_eq_equality hCard hRun
  rw [card_functions] at hDepth
  have hSize := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hDepth
  omega

section CircuitCuts

variable {q : ℕ}

/-- Distinct source wires that feed at least one gate owned by the other side. -/
def crossingWires (p : Program signature n q) (owner : Wire n q → Bool) : Finset (Wire n q) :=
  Finset.univ.filter fun w => ∃ (k : Fin q) (a : Fin (signature.Arity (p.lines k).op)),
    (p.lines k).wires a = w ∧ owner w ≠ owner (.gate k)

/-- Membership in `crossingWires p owner` characterizes source wires crossing `owner`. -/
@[simp] theorem mem_crossingWires {p : Program signature n q} {owner : Wire n q → Bool}
    {w : Wire n q} :
    w ∈ crossingWires p owner ↔
      ∃ (k : Fin q) (a : Fin (signature.Arity (p.lines k).op)),
        (p.lines k).wires a = w ∧ owner w ≠ owner (.gate k) := by
  simp [crossingWires]

/-- If two runs agree on crossing wires, the spliced run agrees with each reference run
on its own side of the cut. -/
theorem trace_splice_of_agree_crossing (p : Program signature n q) (owner : Wire n q → Bool)
    (selector x y : BitString n) (hOwner : ∀ i, owner (.input i) = selector i)
    (hAgree : ∀ w ∈ crossingWires p owner, p.trace interpretation x w = p.trace interpretation y w)
    (w : Wire n q) : p.trace interpretation (splice selector x y) w =
      p.trace interpretation (if owner w then x else y) w := by
  classical
  refine p.wire_induction (P := fun w => p.trace interpretation (splice selector x y) w =
    p.trace interpretation (if owner w then x else y) w) ?_ ?_ w
  · intro i
    change splice selector x y i = (if owner (.input i) then x else y) i
    rw [hOwner]
    cases hi : selector i <;> simp [splice, hi]
  · intro k ih
    rw [p.trace_gate, p.trace_gate]
    congr 1
    funext a
    rw [ih a]
    let source := (p.lines k).wires a
    change p.trace interpretation (if owner source then x else y) source =
      p.trace interpretation (if owner (.gate k) then x else y) source
    by_cases hSame : owner source = owner (.gate k)
    · rw [hSame]
    · have hSource : source ∈ crossingWires p owner :=
        mem_crossingWires.mpr ⟨k, a, rfl, hSame⟩
      have hs := hAgree source hSource
      cases h0 : owner source <;> cases h1 : owner (.gate k)
      · exact absurd (h0.trans h1.symm) hSame
      · simp [hs]
      · simp [hs]
      · exact absurd (h0.trans h1.symm) hSame

/-- An equality restriction forces the traces on the distinct crossing wires
to encode the entire diagonal label. -/
theorem crossingWires_lower_bound_of_family_equality {A : Type*} [Fintype A] {k : ℕ}
    (hCard : Fintype.card A = 2 ^ k) (selector : BitString n)
    (table : A → BitString n) (solve : BooleanFunction n)
    (hEq : ∀ a b, solve (splice selector (table a) (table b)) = true ↔ a = b)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single solve))
    (owner : Wire n c.size → Bool) (hOwner : ∀ i, owner (.input i) = selector i) :
    k ≤ (crossingWires c.program owner).card := by
  classical
  let send (a : A) (w : crossingWires c.program owner) : Bool :=
    c.program.trace interpretation (table a) w.val
  have hinj : Function.Injective send := by
    intro a b hRecord
    have hTrace := trace_splice_of_agree_crossing c.program owner selector
      (table a) (table b) hOwner (fun w hw => congrFun hRecord ⟨w, hw⟩) (c.outputs 0)
    have hOutput (u : A) :
        c.program.trace interpretation (table u) (c.outputs 0) = true :=
      (congrFun (hc (table u)) 0).trans (by simpa using (hEq u u).mpr rfl)
    apply (hEq a b).mp
    have hCompute := congrFun (hc (splice selector (table a) (table b))) 0
    change c.program.trace interpretation (splice selector (table a) (table b))
      (c.outputs 0) = solve (splice selector (table a) (table b)) at hCompute
    rw [← hCompute, hTrace]
    cases owner (c.outputs 0)
    · exact hOutput b
    · exact hOutput a
  have hCount := Fintype.card_le_of_injective send hinj
  rw [hCard] at hCount
  have hPow : 2 ^ k ≤ 2 ^ (crossingWires c.program owner).card := by
    simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using hCount
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPow

/-- Every gate placement on the separating MCSP cut has at least `2^r` crossing wires. -/
theorem crossingWires_lower_bound (h : BooleanFunction s)
    (hEq : ∀ f g : BooleanFunction r, mixedTest h f g = true ↔ f = g)
    (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (r + (s + 1)))))
    (owner : Wire (2 ^ (r + (s + 1))) c.size → Bool)
    (hOwner : ∀ i, owner (.input i) = mask r h i) :
    2 ^ r ≤ (crossingWires c.program owner).card :=
  crossingWires_lower_bound_of_family_equality (card_functions r) (mask r h)
    (probe s) (mcspSquare (r + (s + 1))) hEq c hc owner hOwner

end CircuitCuts

/-- A concrete cut on the arity-32 slice has a 512-bit equality subproblem. -/
theorem mcspSquare_32_equality_cut :
    ∃ h : BooleanFunction 22, ∀ f g : BooleanFunction 9, mixedTest h f g = true ↔ f = g := by
  exact exists_equality_restriction_of_accepted
    (r := 9) (s := 22) (fun f => probe_is_accepted_shannon (k := 2) (d := 7) f (by decide))
    (by decide)

/-- Every gate placement for an arity-32 `mcspSquare` circuit has at least 512 crossing wires
on the separating balanced cut. -/
theorem mcspSquare_32_crossing_cut :
    ∃ h : BooleanFunction 22,
      ∀ c : Circuit signature (2 ^ 32) 1,
        c.Computes interpretation (single (mcspSquare 32)) →
        ∀ owner : Wire (2 ^ 32) c.size → Bool,
          (∀ i, owner (.input i) = mask 9 h i) →
          512 ≤ (crossingWires c.program owner).card := by
  obtain ⟨h, hEq⟩ := mcspSquare_32_equality_cut
  exact ⟨h, fun c hc owner hOwner => crossingWires_lower_bound h hEq c hc owner hOwner⟩

end Cslib.MCSP.CommunicationCut
