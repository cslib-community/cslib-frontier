/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Operations

/-!
# Constructing an augmenting walk from an improving labeling

The two phases of Lemma 31 in [KazdaKolmogorovRolinek2018], arXiv v6, Section 6.1,
printed p. 15, use deterministic scans of the actual positional incidence records. The first
phase repairs defects of the comparison labeling outside the original defect set; the second
phase follows remaining disagreements. Each exchange removes exactly two disagreements.
The clock counts exchanges, not native-machine steps; native encoding and runtime certification
belong to the solver integration. An improving valid comparison labeling is an input, not an
assumed solver result. The construction works for any specified excluded start, strengthening
the source's hypothesis that this variable is inconsistent; it may be the terminal variable.

## Main definitions

* `EdgeInstance.repair`, `EdgeInstance.buildWalk`: the two clocked exchange phases.
* `EdgeInstance.augmentingWalk`: their total, choice-free composition.

## Main results

* `EdgeInstance.repair_spec`, `EdgeInstance.buildWalk_spec`: phase invariants and exact progress.
* `EdgeInstance.augmentingWalk_spec`: Lemma 31 with a bound on the combined exchange count.
* `EdgeInstance.isOptimalLabeling_iff_no_augmentingWalk`: the augmenting-walk characterization.
-/

public section

namespace Cslib.Logic.PL.CSP

open BitString Finset
open scoped symmDiff

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]


namespace EdgeInstance

/-- First satisfying incidence pair in positional order. This scan examines pairs, not trails. -/
@[expose] def findPair (F : CSP Rel V) (P : Occurrence F × Occurrence F → Prop)
    [DecidablePred P] : Option (Occurrence F × Occurrence F) :=
  ((incidenceList F).product (incidenceList F)).find? fun a => decide (P a)

omit [DecidableEq V] in
/-- A returned scan pair satisfies the predicate. -/
theorem findPair_spec {P : Occurrence F × Occurrence F → Prop} [DecidablePred P]
    {a : Occurrence F × Occurrence F} (ha : findPair F P = some a) : P a :=
  of_decide_eq_true (List.find?_some (p := fun a => decide (P a)) ha)

omit [DecidableEq V] in
/-- A failed scan rules out every pair, since all incidences are enumerated. -/
theorem findPair_none {P : Occurrence F × Occurrence F → Prop} [DecidablePred P]
    (hn : findPair F P = none) (o p : Occurrence F) : ¬ P (o, p) := by
  simpa only [decide_eq_true_eq] using List.find?_eq_none.mp hn (o, p)
    (List.mem_product.mpr ⟨mem_incidenceList o, mem_incidenceList p⟩)

/-- A first-phase exchange repairs an f-consistent variable at which g has a new defect. -/
@[expose] def RepairMove (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) (a : Occurrence F × Occurrence F) : Prop :=
  let (o, p) := a
  o.1 = p.1 ∧ o ≠ p ∧ g o ≠ f o ∧ g p ≠ f p ∧
    ¬ Inconsistent f o.var ∧ Inconsistent g o.var ∧
    ValidLabeling sem (flipOn {o, p} g)

instance (sem : Rel → List Bool → Bool) (f g : OccurrenceLabeling F Bool)
    (a : Occurrence F × Occurrence F) : Decidable (RepairMove sem f g a) :=
  inferInstanceAs (Decidable (a.1.1 = a.2.1 ∧ a.1 ≠ a.2 ∧ g a.1 ≠ f a.1 ∧ g a.2 ≠ f a.2 ∧
    ¬ Inconsistent f a.1.var ∧ Inconsistent g a.1.var ∧
    ValidLabeling sem (flipOn {a.1, a.2} g)))

/-- Clocked first phase. The second output counts exchanges. No choice or partner operation
occurs in this routine; an exhausted clock returns its current labeling. -/
@[expose] def repair (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool) :
    ℕ → OccurrenceLabeling F Bool → OccurrenceLabeling F Bool × ℕ
  | 0, g => (g, 0)
  | n + 1, g =>
    match findPair F (RepairMove sem f g) with
    | none => (g, 0)
    | some (o, p) =>
      let (g', k) := repair sem f n (flipOn {o, p} g)
      (g', k + 1)

omit [DecidableEq V] in
/-- A new defect provides a first-phase exchange using the local even delta-matroid axiom. -/
theorem exists_repairMove {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    {v : V} (hvf : ¬ Inconsistent f v) (hvg : Inconsistent g v) :
    ∃ a, RepairMove sem f g a := by
  obtain ⟨o, p, hov, hpv, hgp⟩ := hvg
  obtain ⟨a, hav, ha⟩ : ∃ a : Occurrence F, a.var = v ∧ g a ≠ f a := by
    by_contra! hn
    exact hgp ((hn o hov).trans
      ((not_not.1 fun hh => hvf ⟨o, p, hov, hpv, hh⟩).trans (hn p hpv).symm))
  obtain ⟨b, hc, hne, hb, hv⟩ := exists_valid_exchange hM hg hf a ha
  exact ⟨(a, b), hc, hne, ha, hb, hav.symm ▸ hvf, hav.symm ▸ ⟨o, p, hov, hpv, hgp⟩, hv⟩

/-- The clocked repair preserves validity and never increases defects. It removes two
occurrence disagreements per exchange, and a clock at least the initial Hamming distance
suffices to leave no new defects. -/
theorem repair_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g) (fuel : ℕ) :
    let (g', k) := repair sem f fuel g
    ValidLabeling sem g' ∧ (defects g').card ≤ (defects g).card ∧
      hammingDist f g' + 2 * k = hammingDist f g ∧ k ≤ fuel ∧
      (hammingDist f g ≤ fuel → defects g' ⊆ defects f) := by
  fun_induction repair sem f fuel g with
  | case1 g => -- fuel exhausted
    refine ⟨hg, le_rfl, by simp, le_rfl, fun hd => ?_⟩
    obtain rfl : f = g := hammingDist_eq_zero.mp (by omega)
    exact Subset.rfl
  | case2 n g hs => -- no repair move
    refine ⟨hg, le_rfl, by simp, Nat.zero_le _, ?_⟩
    intro _ v hvg
    by_contra hvf
    obtain ⟨a, ha⟩ := exists_repairMove hM hf hg
      (mt mem_defects.mpr hvf) (mem_defects.mp hvg)
    exact findPair_none hs a.1 a.2 ha
  | case3 n g o p hs g' k hrep ih => -- repair move (o, p): flip and recurse
    obtain ⟨hc, hne, ho, hp, hcf, hcg, hv⟩ := findPair_spec hs
    have hrec := ih hv
    rw [hrep] at hrec
    have hd := hammingDist_flipOn_pair_add_two hne ho hp
    rw [hammingDist_comm g f, hammingDist_comm (flipOn {o, p} g) f] at hd
    have hcard := h.card_defects_flipOn_pair_le g hne hcg
    dsimp only at hrec ⊢
    exact ⟨hrec.1, hrec.2.1.trans hcard, by omega, by omega,
      fun hb => hrec.2.2.2.2 (by omega)⟩

/-- Two fewer defects and containment provide a starting defect different from any specified
variable. Only the start is excluded; the walk may end at that variable. -/
theorem exists_start_ne (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects f).card) (x : V) :
    ∃ r, r ≠ x ∧ Inconsistent f r ∧ ¬ Inconsistent g r := by
  have hp := h.card_defects_mod_two_eq hM hf hg
  by_contra hn
  have hcover : defects f ⊆ insert x (defects g) := fun v hv => by
    by_cases he : v = x
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert_of_mem (mem_defects.mpr (of_not_not fun hh =>
        hn ⟨v, he, mem_defects.mp hv, hh⟩))
  have := (card_le_card hcover).trans (card_insert_le x (defects g))
  omega

/-- A second-phase move follows an incidence disagreement at the current endpoint. -/
@[expose] def WalkMove (sem : Rel → List Bool → Bool)
    (g current : OccurrenceLabeling F Bool) (v : V)
    (a : Occurrence F × Occurrence F) : Prop :=
  let (o, p) := a
  o.var = v ∧ o.1 = p.1 ∧ o ≠ p ∧ current o ≠ g o ∧ current p ≠ g p ∧
    ValidLabeling sem (flipOn {o, p} current)

instance (sem : Rel → List Bool → Bool) (g current : OccurrenceLabeling F Bool)
    (v : V) (a : Occurrence F × Occurrence F) : Decidable (WalkMove sem g current v a) :=
  inferInstanceAs (Decidable (a.1.var = v ∧ a.1.1 = a.2.1 ∧ a.1 ≠ a.2 ∧
    current a.1 ≠ g a.1 ∧ current a.2 ≠ g a.2 ∧
    ValidLabeling sem (flipOn {a.1, a.2} current)))

/-- Clocked second phase. It extends the current trail by one local exchange and stops on the
first original defect reached. The scan and recursion contain no noncomputable choice. -/
@[expose] def buildWalk (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) : ℕ → Walk F → Option (Walk F)
  | 0, _ => none
  | n + 1, w =>
    match findPair F (WalkMove sem g (w.flip f) w.finish) with
    | none => none
    | some (o, p) =>
      let w' := w.snoc o p
      if Inconsistent f p.var then some w' else buildWalk sem f g n w'

omit [DecidableEq V] in
private theorem exists_disagreement {f g : OccurrenceLabeling F Bool} {v : V}
    (hf : Inconsistent f v) (hg : ¬ Inconsistent g v) :
    ∃ o : Occurrence F, o.var = v ∧ f o ≠ g o := by
  obtain ⟨o, p, hov, hpv, hop⟩ := hf
  by_cases ho : f o = g o
  · exact ⟨p, hpv, fun hp => hg ⟨o, p, hov, hpv, by rwa [← ho, ← hp]⟩⟩
  · exact ⟨o, hov, ho⟩

omit [DecidableEq V] in
/-- A defective current endpoint, consistent in the target, always admits an exchange. -/
theorem exists_walkMove {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {g current : OccurrenceLabeling F Bool}
    (hg : ValidLabeling sem g) (hc : ValidLabeling sem current) {v : V}
    (hcv : Inconsistent current v) (hgv : ¬ Inconsistent g v) :
    ∃ a, WalkMove sem g current v a := by
  obtain ⟨o, hov, ho⟩ := exists_disagreement hcv hgv
  obtain ⟨p, hcon, hne, hp, hv⟩ := exists_valid_exchange hM hc hg o ho
  exact ⟨(o, p), hov, hcon, hne, ho, hp, hv⟩

omit [DecidableEq V] in
private theorem other_endpoint_eq (h : EdgeInstance F)
    {f g : OccurrenceLabeling F Bool} {o a : Occurrence F}
    (hf : Inconsistent f o.var) (hg : ¬ Inconsistent g o.var) (ho : f o ≠ g o)
    (ha : a.var = o.var) (hne : a ≠ o) : f a = g a := by
  have hi := (h.inconsistent_iff f o).mp hf
  have hj := not_not.mp (mt (h.inconsistent_iff g o).mpr hg)
  rcases h.eq_or_eq_partner ha with he | he
  · exact (hne he).elim
  · subst a
    cases hf0 : f o <;> cases hf1 : f (h.partner o) <;>
      cases hg0 : g o <;> cases hg1 : g (h.partner o) <;> simp_all

/-- The second-phase invariant. Already-used incidences agree with the target, so scans of
remaining disagreements cannot reuse them. Once the first step is taken, every incidence of
the starting variable agrees with the target, preventing a return to that start. -/
structure WalkState (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) (w : Walk F) : Prop where
  prefix_valid : w.IsFPrefix sem f
  endpoint_defect : Inconsistent (w.flip f) w.finish
  target_endpoint : ¬ Inconsistent g w.finish
  internal_endpoint : w.steps = [] ∨ ¬ Inconsistent f w.finish
  start_defect : Inconsistent f w.start
  target_start : ¬ Inconsistent g w.start
  used_agrees : ∀ a ∈ w.edges, w.flip f a = g a
  start_cleared : w.steps ≠ [] → ∀ a, a.var = w.start → w.flip f a = g a

private theorem WalkState.extend (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} {f g : OccurrenceLabeling F Bool} {w : Walk F}
    (hw : WalkState sem f g w) (hsub : defects g ⊆ defects f)
    {o p : Occurrence F} (hm : WalkMove sem g (w.flip f) w.finish (o, p)) :
    (w.snoc o p).IsFPrefix sem f ∧ p.var ≠ w.start ∧
      (¬ Inconsistent f p.var → WalkState sem f g (w.snoc o p)) := by
  obtain ⟨hov, hc, hne, ho, hp, hv⟩ := hm
  have hno : o ∉ w.edges := fun he => ho (hw.used_agrees o he)
  have hnp : p ∉ w.edges := fun he => hp (hw.used_agrees p he)
  have hvar := h.var_ne_of_constraint_eq hc hne
  have hps : p.var ≠ w.start := by
    by_cases he : w.steps = []
    · have hfin : w.finish = w.start := by simp [Walk.finish, he, Walk.finishFrom]
      exact fun hh => hvar (hov.trans (hfin.trans hh.symm))
    · exact fun hh => hp (hw.start_cleared he p hh)
  have hvp := hw.prefix_valid.snoc hov hc hne hno hnp hw.internal_endpoint hv
  have hflip := Walk.flip_snoc w f o p hw.prefix_valid.1 hno hnp hne
  have hflip_o : flipOn {o, p} (w.flip f) o = g o := by
    cases hx : w.flip f o <;> cases hy : g o <;> simp_all [flipOn_apply]
  have hflip_p : flipOn {o, p} (w.flip f) p = g p := by
    cases hx : w.flip f p <;> cases hy : g p <;> simp_all [flipOn_apply]
  have hused (a : Occurrence F) (ha : a ∈ (w.snoc o p).edges) :
      (w.snoc o p).flip f a = g a := by
    rw [hflip]
    rw [Walk.snoc, Walk.edges, Walk.edgesOf_append] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [flipOn_apply, ite_eq_right (by simp [ne_of_mem_of_not_mem ha hno,
        ne_of_mem_of_not_mem ha hnp])]
      exact hw.used_agrees a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      exacts [hflip_o, List.mem_singleton.mp ha ▸ hflip_p]
  refine ⟨hvp, hps, fun hpf =>
    ⟨hvp, ?_, Walk.finish_snoc w o p ▸ fun he => hpf (mem_defects.mp (hsub (mem_defects.mpr he))),
      Or.inr (Walk.finish_snoc w o p ▸ hpf), hw.start_defect, hw.target_start, hused, ?_⟩⟩
  · rw [Walk.finish_snoc, ← mem_defects, hvp.1.defects_flip h, Walk.finish_snoc]
    change p.var ∈ defects f ∆ {w.start} ∆ {p.var}
    simp [mem_symmDiff, mem_defects, hps, hpf]
  · intro _ a ha
    rw [hflip]
    have hap : a ≠ p := fun he => hps (he ▸ ha)
    by_cases he : w.steps = []
    · have hfin : w.finish = w.start := by simp [Walk.finish, he, Walk.finishFrom]
      rcases eq_or_ne a o with rfl | heo
      · exact hflip_o
      · rw [flipOn_apply, ite_eq_right (by simp [heo, hap])]
        exact other_endpoint_eq h (hov ▸ hw.endpoint_defect) (hov ▸ hw.target_endpoint)
          ho (ha.trans (hov.trans hfin).symm) heo
    · have hao : a ≠ o := fun hao => ho (hw.start_cleared he o (hao ▸ ha))
      rw [flipOn_apply, ite_eq_right (by simp [hao, hap])]
      exact hw.start_cleared he a ha

/-- The second phase returns an augmenting prefix-valid incidence trail. Its clock counts
exchanges, and each appended step removes exactly two remaining occurrence disagreements. -/
theorem buildWalk_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hg : ValidLabeling sem g) (hsub : defects g ⊆ defects f)
    (fuel : ℕ) {w : Walk F} (hw : WalkState sem f g w)
    (hclock : hammingDist (w.flip f) g ≤ fuel) :
    ∃ w' k, buildWalk sem f g fuel w = some w' ∧ w'.IsAugmenting sem f ∧
      w'.start = w.start ∧ w'.steps.length = w.steps.length + k ∧
      hammingDist (w'.flip f) g + 2 * k = hammingDist (w.flip f) g ∧ k ≤ fuel := by
  induction fuel generalizing w with
  | zero =>
    have he : w.flip f = g := hammingDist_eq_zero.mp (by omega)
    exact (hw.target_endpoint (he ▸ hw.endpoint_defect)).elim
  | succ n ih =>
    match hs : findPair F (WalkMove sem g (w.flip f) w.finish) with
    | none =>
      obtain ⟨a, ha⟩ := exists_walkMove hM hg hw.prefix_valid.valid_flip
        hw.endpoint_defect hw.target_endpoint
      exact (findPair_none hs a.1 a.2 ha).elim
    | some (o, p) =>
      have hm := findPair_spec hs
      obtain ⟨hov, hc, hne, ho, hp, hv⟩ := id hm
      have hno : o ∉ w.edges := fun he => ho (hw.used_agrees o he)
      have hnp : p ∉ w.edges := fun he => hp (hw.used_agrees p he)
      have hd := (Walk.flip_snoc w f o p hw.prefix_valid.1 hno hnp hne ▸
        hammingDist_flipOn_pair_add_two hne ho hp)
      obtain ⟨hprefix, hps, hstate⟩ := hw.extend h hsub hm
      by_cases hpf : Inconsistent f p.var
      · exact ⟨w.snoc o p, 1, by simp only [buildWalk, hs, ite_eq_left hpf],
          ⟨⟨hprefix, Walk.finish_snoc w o p ▸ hps.symm⟩, hw.start_defect,
            Walk.finish_snoc w o p ▸ hpf⟩,
          rfl, by simp [Walk.snoc], by omega, by omega⟩
      · obtain ⟨w', k, hr, ha, hstart, hlen, hdist, hk⟩ := ih (hstate hpf) (by omega)
        simp only [Walk.snoc, List.length_append, List.length_singleton] at hlen
        exact ⟨w', k + 1, by simpa only [buildWalk, hs, ite_eq_right hpf] using hr, ha, hstart,
          by omega, by omega, by omega⟩

/-- Start the second phase at a chosen original defect absent from the comparison labeling. -/
theorem buildWalk_from_start (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g) (hsub : defects g ⊆ defects f)
    (r : V) (hrf : Inconsistent f r) (hrg : ¬ Inconsistent g r) :
    ∃ w k, buildWalk sem f g (hammingDist f g) ⟨r, []⟩ = some w ∧
      w.IsAugmenting sem f ∧ w.start = r ∧ w.steps.length = k ∧
      hammingDist (w.flip f) g + 2 * k = hammingDist f g ∧ k ≤ hammingDist f g := by
  have he : (⟨r, []⟩ : Walk F).flip f = f := by
    simp [Walk.flip, Walk.edges, Walk.edgesOf]
  have hw : WalkState sem f g ⟨r, []⟩ := {
    prefix_valid := ⟨⟨trivial, List.nodup_nil⟩, trivial, hf⟩
    endpoint_defect := by simpa only [he, Walk.finish, Walk.finishFrom] using hrf
    target_endpoint := hrg
    internal_endpoint := Or.inl rfl
    start_defect := hrf
    target_start := hrg
    used_agrees := by simp [Walk.edges, Walk.edgesOf]
    start_cleared := by simp }
  have hb := h.buildWalk_spec hM hg hsub (hammingDist f g) hw (by rw [he])
  simpa only [he, List.length_nil, Nat.zero_add] using hb

private theorem repair_full_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g) :
    let fixed := repair sem f (hammingDist f g) g
    ValidLabeling sem fixed.1 ∧ (defects fixed.1).card ≤ (defects g).card ∧
      hammingDist f fixed.1 + 2 * fixed.2 = hammingDist f g ∧ defects fixed.1 ⊆ defects f := by
  obtain ⟨hvalid, hcard, hdist, -, hsub⟩ := h.repair_spec hM hf hg (hammingDist f g)
  exact ⟨hvalid, hcard, hdist, hsub le_rfl⟩

/-- Full Lemma 31 existence conclusion, obtained by the actual two phases. The specified
variable is excluded only as the start. No solver or augmenting-walk assumption is used. -/
theorem exists_augmentingWalk_start_ne (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} (hM : EvenConstraints sem F)
    {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects f).card) (x : V) :
    ∃ w : Walk F, w.IsAugmenting sem f ∧ w.start ≠ x ∧
      2 * w.steps.length ≤ hammingDist f g := by
  obtain ⟨hvalid, hcard, hrepair, hsub⟩ := h.repair_full_spec hM hf hg
  obtain ⟨r, hrx, hrf, hrg⟩ := h.exists_start_ne hM hf hvalid
    (hcard.trans_lt hlt) x
  obtain ⟨w, k, _, hw, hstart, hlen, hdist, _⟩ :=
    h.buildWalk_from_start hM hf hvalid hsub r hrf hrg
  exact ⟨w, hw, hstart ▸ hrx, by omega⟩

/-- First original defect absent from the comparison labeling, excluding the specified start.
Incidences are scanned in positional order; no arbitrary occurrence is chosen. -/
@[expose] def findStart (F : CSP Rel V) (f g : OccurrenceLabeling F Bool) (x : V) :
    Option (Occurrence F) :=
  (incidenceList F).find? fun o =>
    decide (o.var ≠ x ∧ Inconsistent f o.var ∧ ¬ Inconsistent g o.var)

/-- The full two-phase construction of Lemma 31. The clocks are occurrence Hamming distances;
failed or insufficient inputs return `none`. Correctness under the mathematical hypotheses
is `augmentingWalk_spec`. The routine does not solve for the improving comparison labeling. -/
@[expose] def augmentingWalk (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) (x : V) : Option (Walk F) :=
  let fixed := (repair sem f (hammingDist f g) g).1
  match findStart F f fixed x with
  | none => none
  | some o => buildWalk sem f fixed (hammingDist f fixed) ⟨o.var, []⟩

/-- Lemma 31 with a concrete total routine: given an improving valid comparison labeling,
`augmentingWalk` returns an augmenting f-walk starting away from the specified variable.
Both phases together perform at most half the original occurrence disagreements in exchanges.
This bounds local exchanges; no native-machine runtime bound is asserted. -/
theorem augmentingWalk_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects f).card) (x : V) :
    ∃ w : Walk F, augmentingWalk sem f g x = some w ∧ w.IsAugmenting sem f ∧
      w.start ≠ x ∧
      2 * ((repair sem f (hammingDist f g) g).2 + w.steps.length) ≤ hammingDist f g := by
  let fixed := repair sem f (hammingDist f g) g
  obtain ⟨hvalid, hcard, hrepair, hsub⟩ := h.repair_full_spec hM hf hg
  cases hs : findStart F f fixed.1 x with
  | none =>
    obtain ⟨_, hrx, ⟨o, p, rfl, hpr, hop⟩, hrg⟩ :=
      h.exists_start_ne hM hf hvalid (hcard.trans_lt hlt) x
    exact (List.find?_eq_none.mp hs o (mem_incidenceList o)
      (decide_eq_true ⟨hrx, ⟨o, p, rfl, hpr, hop⟩, hrg⟩)).elim
  | some o =>
    have hfind := List.find?_some (l := incidenceList F) hs
    have ho := of_decide_eq_true hfind
    obtain ⟨w, k, hw, ha, hstart, hlen, hdist, _⟩ :=
      h.buildWalk_from_start hM hf hvalid hsub o.var ho.2.1 ho.2.2
    exact ⟨w, by simpa only [augmentingWalk, fixed, hs] using hw, ha, hstart ▸ ho.1, by omega⟩

/-- Nonoptimality is equivalent to existence of an augmenting walk, without assuming a solver. -/
theorem exists_improvement_iff_exists_augmentingWalk (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} (hM : EvenConstraints sem F)
    {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f) :
    (∃ g : OccurrenceLabeling F Bool,
      ValidLabeling sem g ∧ (defects g).card < (defects f).card) ↔
      ∃ w : Walk F, w.IsAugmenting sem f := by
  constructor
  · rintro ⟨g, hg, hlt⟩
    obtain ⟨x, _⟩ := card_pos.mp (Nat.zero_lt_of_lt hlt)
    exact (h.exists_augmentingWalk_start_ne hM hf hg hlt x).imp fun _ hw => hw.1
  · rintro ⟨w, hw⟩
    have hd := hw.card_defects_flip_add_two h
    exact ⟨w.flip f, hw.1.1.valid_flip, by omega⟩

/-- An optimal valid labeling has no augmenting walk, and conversely. -/
theorem isOptimalLabeling_iff_no_augmentingWalk (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} (hM : EvenConstraints sem F)
    {f : OccurrenceLabeling F Bool} :
    IsOptimalLabeling sem f ↔ ValidLabeling sem f ∧ ¬ ∃ w : Walk F, w.IsAugmenting sem f := by
  refine ⟨fun ⟨hf, hopt⟩ => ⟨hf, fun hw => ?_⟩,
    fun ⟨hf, hn⟩ => ⟨hf, fun g hg => not_lt.mp fun hlt =>
      hn ((h.exists_improvement_iff_exists_augmentingWalk hM hf).mp ⟨g, hg, hlt⟩)⟩⟩
  obtain ⟨g, hg, hlt⟩ := (h.exists_improvement_iff_exists_augmentingWalk hM hf).mpr hw
  exact (hopt g hg).not_gt hlt

end EdgeInstance

end Cslib.Logic.PL.CSP
