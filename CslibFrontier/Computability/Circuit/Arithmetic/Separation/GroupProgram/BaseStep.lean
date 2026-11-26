/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.RoleSums
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.BaseSums
import CslibFrontier.Foundations.Data.List.NodupFlatMap

/-!
# The instructions of a base party do what its step does

The instructions of a base party in the script of a group of the evaluator of [AnthropicVPVNP2026]
(`baseInstructions`) are the instruction of its block or of its input part, which cuts the letters
of the tapes for the partners and writes and reads the units of the strings, followed by the
comparisons of the two copies of the units from the party to itself. From a trie that stores the
contents of the cells, they make the sum over the choices of the step of the base party
(`baseWriteStep`) of its weight times the trie of the contents that it writes: they simulate the
step (`simulates_base`).

## Main results

* `simulates_base`: the instructions of a base party simulate its step.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source module
`Nc.Grp.StepBase`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset Interpreter Interpreter.Tree List.StairRefinement

/-! ### The step of a base party -/

section Step

variable {F : Type} [CommRing F] {θ : List Bool → F} {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ]
  [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {A' E K U0 U1 ub c T : ℕ}
  {G : Type} [DecidableEq G] {M : Moves F (K + K + A') E}
  (mu : Tape.Letter S Unit Γ → Matrix Q Q F) (cb : Option Γ → Fin c → Bool)
  (kinds : List (Σ L : Cut.Law F, L.Role)) {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.Channel → Fin U1} {grp : Fin (K + K + A') → G} {g : G} {key : Cell M U0 U1 → List Bool}
  {dkey : Fin (K + K) × Fin U0 → List Bool}

omit [DecidableEq Γ] [DecidableEq Q] in
/-- The comparisons of the copies of the units from a base party to itself. -/
private theorem weightedSum_scriptSem_agree {ι : Type*} (l : List ι) (f f' : ι → List Bool)
    (t : Tree) (Ψ : Tree → F) :
    (scriptSem θ mu cb kinds T ub (l.map fun a => .agree (f a) (f' a)) t).weightedSum Ψ =
      if ∀ a ∈ l, tget (f a) t = tget (f' a) t then Ψ t else 0 := by
  classical
  rw [scriptSem_of_checks mu cb kinds T (fun i => instructionSem θ mu cb kinds T ub i t ≠ [])
    fun i hi => ?_]
  · simp only [List.forall_mem_map, instructionSem, ne_eq, ite_eq_right_iff, List.cons_ne_nil,
      imp_false, not_not]
    split_ifs <;> simp
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hi
    simp only [instructionSem]
    split_ifs <;> simp_all

omit [DecidableEq Q] in
/-- **What a base party does with given letters.** If the base party `p` has the letters
`w (s, d)` on the sides of the tapes, its cuts, the writing of the units and the comparisons of
the copies of the units from `p` to itself make, from a trie that stores `σ`, the sum over what it
writes (`R`) and reads (`C`), under the conditions `InitialFits`, of `Ψ'` at the contents after
it. -/
private theorem weightedSum_packSem_base (hκ : Function.Injective (Sum.elim key dkey))
    (hub : 0 < ub) {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g)
    (hρ : ∀ s, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last)
    {w : Option S × Bool → List Γ} (hw : ∀ z, (w z).length ≤ T) {out : Outputs S}
    (ho : ∀ j, out j = ((w (outputSide j)).map (letterCode cb)).reverse) {t : Tree}
    {σ : Cell M U0 U1 → UnitContent ub} (hst : Stores ub key t σ) {Ψ : Tree → F}
    {Ψ' : (Cell M U0 U1 → UnitContent ub) → F} (hΨ : ∀ t' σ', Stores ub key t' σ' → Ψ t' = Ψ' σ') :
    (packSem F (separator cb) ub (baseBody ρ n key dkey p) out t).weightedSum (fun t' =>
      (scriptSem θ mu cb kinds T ub ((indicesBelow (n p p)).map fun k =>
        .agree (key ⟨Fin.castAdd A' p, .init p p k⟩) (dkey (p, k))) t').weightedSum Ψ) =
      ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) =>
          List.wordsLe Γ T, ∑ C ∈ Fintype.piFinset fun _ : Option S =>
          Fintype.piFinset fun _ : Fin (K + K) => List.wordsLe Γ T,
        if (∀ s, cat (R s) = w (s, false)) ∧ (∀ s, cat (C s) = w (s, true)) ∧
          InitialFits ub U0 cb (fun s => ρ s p) (fun a b => n a b) p R C then
          Ψ' ((baseCells n o grp g p).piecewise (fun c => initialContents cb R C p c.unit) σ)
        else 0 := by
  simp only [weightedSum_scriptSem_agree]
  rw [List.weightedSum_of_fst_eq_one (one_of_mem_packSem _ _ _ _ _),
    sum_map_packSem cb ρ n key dkey hρ hw ho t]
  refine sum_congr rfl fun R _ => ?_
  -- the strings that `p` writes
  set WR : List (List (Cell M U0 U1 ⊕ (Fin (K + K) × Fin U0)) × List Bool) :=
    List.ofFn fun b => ((indicesBelow (n p b)).map fun k => .inl ⟨Fin.castAdd A' p, .init p b k⟩,
      segmentString cb fun s => R s b) with hWR
  obtain ⟨t₁, h1, h2⟩ := putStrings_spec hκ hub
    (v := Sum.elim (fun c => initialContents cb R R p c.unit) fun _ => none) WR (by
      rw [hWR, List.ofFn_eq_map, List.flatMap_map]
      exact List.nodup_flatMap_map (List.nodup_finRange _) (fun _ => nodup_indicesBelow _)
        fun b k b' k' h => by simpa using h) (by simp [WR, List.mem_ofFn, initialContents]) t
  rw [show (baseBody ρ n key dkey p).writeKeys = WR.map fun w => w.1.map (Sum.elim key dkey) by
      simp [WR, baseBody, List.map_ofFn, Function.comp_def],
    show (List.ofFn fun b => segmentString cb (fun s => R s b) ++ [true]) =
      WR.map fun w => w.2 ++ [true] by simp [WR, List.map_ofFn, Function.comp_def], h2]
  have hcR : (∀ w ∈ WR, unitCount ub w.2 = w.1.length) ↔
      ∀ b, unitCount ub (segmentString cb fun s => R s b) = n p b := by
    simp [WR]
  simp only [hcR, InitialFits]
  split_ifs with hc1 hc2
  swap
  · simp only [List.map_nil, List.sum_nil]
    exact (sum_eq_zero fun C _ => ite_eq_right_iff.2 fun h => absurd h.2.2.2.1 hc2).symm
  swap
  · exact (sum_eq_zero fun C _ => ite_eq_right_iff.2 fun h => absurd ⟨h.1, h.2.2.1⟩ hc1).symm
  rw [List.map_singleton, List.sum_singleton]
  refine sum_congr rfl fun C _ => ?_
  -- the strings that `p` reads
  set WC : List (List (Cell M U0 U1 ⊕ (Fin (K + K) × Fin U0)) × List Bool) :=
    List.ofFn fun b => ((indicesBelow (n b p)).map fun k => if b = p then .inr (p, k) else
      .inl ⟨Fin.castAdd A' p, .init b p k⟩, segmentString cb fun s => C s b) with hWC
  obtain ⟨t₂, h3, h4⟩ := putStrings_spec hκ hub (v := Sum.elim
    (fun c => initialContents cb R C p c.unit) fun d =>
      unitsOf ub (segmentString cb fun s => C s p) d.2)
    WC (by
      rw [hWC, List.ofFn_eq_map, List.flatMap_map]
      exact List.nodup_flatMap_map (List.nodup_finRange _) (fun _ => nodup_indicesBelow _)
        fun b k b' k' h => by by_cases hb : b = p <;> by_cases hb' : b' = p <;> simp_all)
    (by
      simp only [WC, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, List.getElem_map]
      intro b i hi
      split_ifs with hb <;> simp [initialContents, hb]) t₁
  rw [show (baseBody ρ n key dkey p).readKeys = WC.map fun w => w.1.map (Sum.elim key dkey) by
      simp [WC, baseBody, List.map_ofFn, Function.comp_def, apply_ite],
    show (List.ofFn fun b => segmentString cb (fun s => C s b) ++ [true]) =
      WC.map fun w => w.2 ++ [true] by simp [WC, List.map_ofFn, Function.comp_def], h4]
  have hcC : (∀ w ∈ WC, unitCount ub w.2 = w.1.length) ↔
      ∀ b, unitCount ub (segmentString cb fun s => C s b) = n b p := by
    simp [WC]
  simp only [hcC, hc1.1, hc1.2, hc2, implies_true, true_and]
  by_cases hC : ∀ s, cat (C s) = w (s, true)
  swap
  · simp [hC]
  by_cases hn : ∀ b, unitCount ub (segmentString cb fun s => C s b) = n b p
  swap
  · simp [hC, hn]
  have hget (a : Cell M U0 U1 ⊕ (Fin (K + K) × Fin U0)) := (h3 (hcC.2 hn)).2 a
  simp only [(h1 (hcR.2 hc2)).2] at hget
  have hmR (c : Cell M U0 U1) : Sum.inl c ∈ WR.flatMap Prod.fst ↔
      ∃ (b : Fin (K + K)) (k : Fin U0), (k : ℕ) < n p b ∧ c = ⟨Fin.castAdd A' p, .init p b k⟩ := by
    simp [WR, List.mem_flatMap, List.mem_ofFn, eq_comm]
  have hmC (c : Cell M U0 U1) : Sum.inl c ∈ WC.flatMap Prod.fst ↔
      ∃ (b : Fin (K + K)) (k : Fin U0), (k : ℕ) < n b p ∧ b ≠ p ∧
        c = ⟨Fin.castAdd A' p, .init b p k⟩ := by
    simp [WC, List.mem_flatMap, List.mem_ofFn, apply_ite, eq_comm]
  have hdC (k : Fin U0) : Sum.inr (p, k) ∈ WC.flatMap Prod.fst ↔ (k : ℕ) < n p p := by
    simp only [WC, List.mem_flatMap, List.mem_ofFn, exists_exists_eq_and, List.mem_map,
      mem_indicesBelow]
    refine ⟨fun ⟨b, k', hk', h⟩ => ?_, fun hk => ⟨p, k, hk, by simp⟩⟩
    split_ifs at h with hbp; simp_all
  have hdR (k : Fin U0) : Sum.inr (p, k) ∉ WR.flatMap Prod.fst := by
    simp [WR, List.mem_flatMap, List.mem_ofFn]
  have hD : (∀ k ∈ indicesBelow (n p p), tget (key ⟨Fin.castAdd A' p, .init p p k⟩) t₂ =
      tget (dkey (p, k)) t₂) ↔ ∀ k : Fin U0, unitsOf ub (segmentString cb fun s => R s p) k =
        unitsOf ub (segmentString cb fun s => C s p) k := by
    have e (k : Fin U0) (hk : (k : ℕ) < n p p) : tget (key ⟨Fin.castAdd A' p, .init p p k⟩) t₂ =
        tget (dkey (p, k)) t₂ ↔ unitsOf ub (segmentString cb fun s => R s p) k =
          unitsOf ub (segmentString cb fun s => C s p) k := by
      have e1 := hget (.inl ⟨Fin.castAdd A' p, .init p p k⟩)
      have e2 := hget (.inr (p, k))
      simp only [Sum.elim_inl, Sum.elim_inr, hmC, hmR, hdC, hdR, hk] at e1 e2
      simp only [ne_eq, Cell.mk.injEq, UnitId.init.injEq, true_and, ↓existsAndEq, and_true,
        exists_eq_right_right', hk, not_true_eq_false, and_false, ↓reduceIte, exists_eq_right',
        initialContents] at e1 e2
      rw [e1, e2]
      exact (ofBits_bits_injective hub).eq_iff
    refine ⟨fun h k => ?_, fun h k hk => (e k ((mem_indicesBelow _).1 hk)).2 (h k)⟩
    by_cases hk : (k : ℕ) < n p p
    · exact (e k hk).1 (h k ((mem_indicesBelow _).2 hk))
    · rw [unitsOf_eq_none.2 (by rw [hc2 p]; omega), unitsOf_eq_none.2 (by rw [hn p]; omega)]
  have hst₂ : Stores ub key t₂
      ((baseCells n o grp g p).piecewise (fun c => initialContents cb R C p c.unit) σ) := by
    refine ⟨(h3 (hcC.2 hn)).1 ((h1 (hcR.2 hc2)).1 hst.1), fun c => ?_⟩
    have e := hget (.inl c)
    simp only [Sum.elim_inl] at e
    by_cases hb : c ∈ baseCells n o grp g p
    · obtain ⟨a, b, k, hk, hab, rfl⟩ := (mem_baseCells hp).1 hb
      rcases eq_or_ne a p with rfl | ha
      · simp [Finset.piecewise, hb, e, hmC, hmR, hk, initialContents]
      · obtain rfl := hab.resolve_left ha
        simp [Finset.piecewise, hb, e, hmC, hk, ha, initialContents]
    · have h1c : Sum.inl c ∉ WC.flatMap Prod.fst := fun h =>
        let ⟨b, k, hk, _, hc⟩ := (hmC c).1 h
        hb ((mem_baseCells hp).2 ⟨b, p, k, hk, .inr rfl, hc⟩)
      have h2c : Sum.inl c ∉ WR.flatMap Prod.fst := fun h =>
        let ⟨b, k, hk, hc⟩ := (hmR c).1 h
        hb ((mem_baseCells hp).2 ⟨p, b, k, hk, .inl rfl, hc⟩)
      simp only [e, h1c, h2c, ite_false, Finset.piecewise, hb, hst.2 c]
  simp only [hC, hn, implies_true, ite_true, true_and, List.map_singleton, List.sum_singleton,
    hD, hΨ _ _ hst₂]

omit [Fintype Γ] [DecidableEq Γ] [Fintype S] in
/-- The letters of a run on the sides of the tapes are those that a block writes and reads exactly
when the block writes nothing on the input and emits them. -/
private theorem sides_iff_blockEmission (u : List (Tape.Letter S Unit Γ)) {A : ℕ}
    (R C : Option S → Fin A → List Γ) :
    ((∀ s, cat (R s) = sideLetters u (s, false)) ∧ ∀ s, cat (C s) = sideLetters u (s, true)) ↔
      (∀ b, R none b = []) ∧ Tape.emit u = blockEmission R C := by
  have e1 (s : S) (d : Bool) : sideLetters u (some s, d) = Tape.emit u (.tp s d) :=
    sideLetters_channelSide u (.tp s d)
  have e2 : sideLetters u (none, true) = Tape.emit u (.inp ()) :=
    sideLetters_channelSide u (.inp ())
  simp only [Option.forall, sideLetters_none_false, cat_eq_nil, e1, e2, funext_iff]
  refine ⟨fun ⟨⟨h0, h1⟩, h2, h3⟩ => ⟨h0, fun ch => by
    rcases ch with ⟨s, _ | _⟩ | ⟨⟨⟩⟩ <;> simp [blockEmission, *]⟩,
    fun ⟨h0, h⟩ => ⟨⟨h0, fun s => (h (.tp s false)).symm⟩, (h (.inp ())).symm,
      fun s => (h (.tp s true)).symm⟩⟩

/-- **The instructions of a base party simulate its step.** -/
theorem simulates_base (hκ : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x κ).length ≤ T) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g)
    (hρ : ∀ s, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last) :
    Simulates θ mu cb kinds T key
      (baseInstructions (fun z => (Fintype.equivFin Q z : ℕ)) cb q x ρ n key dkey p)
      (baseWriteStep (ub := ub) mu T cb q x ρ n o grp g p) := by
  intro t σ Ψ Ψ' hst hΨ
  rw [baseInstructions, scriptSem_cons, List.weightedSum_weightedBind]
  simp only [baseWriteStep]
  rw [sum_product]
  induction p using Fin.addCases with
  | left κ =>
    rw [Fin.addCases_left, instructionSem, dite_eq_left_of_eq_true
      (eq_true ⟨(Fintype.equivFin Q _).2, (Fintype.equivFin Q _).2⟩), List.weightedSum_weightedBind]
    simp only [Fin.eta]
    rw [weightedSum_simSem mu cb hmu]
    refine (sum_congr rfl fun u _ => by rw [weightedSum_packSem_base mu cb kinds hκ hub hp hρ
      (o := o) (w := sideLetters (List.ofFn u))
      (fun z => (length_sideLetters_le _ z).trans (by simp))
      (fun j => rfl) hst hΨ]).trans ?_
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun R _ => sum_comm.trans (sum_congr rfl fun C _ => ?_)
    rw [partyWeight_block, blockWeight]
    by_cases hF : InitialFits ub U0 cb (fun s => ρ s (Fin.castAdd K κ)) (fun a b => n a b)
      (Fin.castAdd K κ) R C
    swap
    · simp [hF]
    simp only [hF, and_true, ↓reduceIte, sides_iff_blockEmission]
    by_cases h0 : ∀ b, R none b = []
    · simp only [h0, implies_true, true_and, ↓reduceIte, mul_ite, mul_zero, ite_mul, zero_mul,
        sum_mul]
      exact sum_congr rfl fun _ _ => by split_ifs <;> rfl
    · simp [h0]
  | right κ =>
    rw [Fin.addCases_right, instructionSem,
      weightedSum_packSem_base mu cb kinds hκ hub hp hρ (o := o)
      (w := fun z => if z = (none, false) then x κ else [])
      (fun z => by split_ifs; exacts [hx κ, Nat.zero_le _])
      (fun j => by simp only [inputOutputs]; split_ifs <;> simp) hst hΨ]
    refine sum_congr rfl fun R _ => sum_congr rfl fun C _ => ?_
    rw [partyWeight_input]
    have h : ((∀ s, cat (R s) = if (s, false) = ((none : Option S), false) then x κ else []) ∧
        ∀ s, cat (C s) = if (s, true) = ((none : Option S), false) then x κ else []) ↔
        (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ := by
      simp only [Option.forall, Prod.mk.injEq, reduceCtorEq, and_false, and_true, ite_true,
        ite_false, cat_eq_nil]
      tauto
    by_cases hF : InitialFits ub U0 cb (fun s => ρ s (Fin.natAdd K κ)) (fun a b => n a b)
      (Fin.natAdd K κ) R C <;> simp_all only [Prod.mk.injEq, and_true, Bool.true_eq_false,
        and_false, ↓reduceIte, Fin.natAdd_eq_addNat, ite_mul, one_mul, zero_mul]
    exact if_congr Iff.rfl rfl rfl

end Step

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
