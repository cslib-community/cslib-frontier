/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Time.CountingBarrier
import CslibFrontier.Computability.Complexity.Classes.Time.RandomAccessATM
import CslibFrontier.Computability.Complexity.Classes.Time.SigmaThree
import CslibFrontier.Computability.Complexity.Classes.Time.TseitinObstruction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Checked clients for `Σ₂TIME(T)` vs `Σ₃TIME(T / √(log T))`

Non-vacuous client checks covering all four library modules:
1. Odd-charge Tseitin unsatisfiability on `K₄` contrasted with local-extension acceptance
   (`S = ∅`, `q = 2 < 4`) via `Cslib.Complexity.tseitinLocalExtension_iff_exists_large_component`,
   and the finite-DAG `forkConeProtocol` counterexample (`J = ∅` accepts vs `J = {2}` sound).
2. `SigmaThreeTIME` clients (`evenBits`, `oddBits`, `interleave`, `encSigmaThreeWitness`,
   `SigmaTwoTIME_subset_SigmaThreeTIME`, `compl_mem_SigmaThreeTIME_of_mem_SigmaTwoTIME`,
   `mem_SigmaP_three_of_mem_SigmaThreeTIME`) plus non-vacuous
   `mem_SigmaThreeTIME_of_composition_of_le`.
3. Concrete `lastBitLanguage` separation (`RADTIME(log n)` vs `SigmaTwoTIME(o(n))`),
   `OracleAltTree` query-set preservation, `RACfgCompact.unpack_pack` round-trip, uniform `(H)`
   bridge + `RAATM.accepts_iff_accCount_pos`, positive/negative `sigma2AsymmetricBlockSimulation`,
   and `sqrt_mul_le_div_sqrt_log`.
4. `CountingBarrier` Toda collapse consequences, adaptive `RA_query_log_elimination`,
   `linear_le_sq_div_sqrt_log`, and a non-vacuous `remaining_lemmas_imply_containment` client
   placing `{x | x ∈ lastBitLanguage}` in `SigmaThreeTIME encBits id`.
-/

namespace CslibFrontierTests.SigmaThreeSpeedup

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Tseitin local-extension obstruction on `K₄` -/

private def k4Graph : SimpleGraph (Fin 4) := ⊤

private instance : DecidableRel k4Graph.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v))

private theorem k4Graph_connected : k4Graph.Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl u
  · exact SimpleGraph.Adj.reachable (show k4Graph.Adj u v from huv)

private def oddChargeK4 : Fin 4 → Bool
  | 0 => true
  | _ => false

private theorem oddChargeK4_sum : (∑ v : Fin 4, oddChargeK4 v) = true := by
  decide

/-- Globally, the odd-charge Tseitin system on `K₄` is unsatisfiable. -/
example : ¬ TseitinSatisfiable k4Graph oddChargeK4 :=
  not_tseitinSatisfiable_of_sum_eq_true k4Graph oddChargeK4 oddChargeK4_sum

/-- Yet with `S = ∅` and query budget `q = 2 < 4`, the local-extension protocol accepts on `K₄`. -/
example : ∃ α : Sym2 (Fin 4) → Bool, ∀ Q : Finset (Fin 4), Q.card ≤ 2 →
    ∃ β : Sym2 (Fin 4) → Bool,
      TseitinSatisfies k4Graph oddChargeK4
        (fun e => if e ∈ (∅ : Finset (Sym2 (Fin 4))) then α e else β e) Q := by
  classical
  rw [tseitinLocalExtension_iff_exists_large_component k4Graph k4Graph_connected oddChargeK4
    oddChargeK4_sum ∅ 2]
  let delG := k4Graph.deleteEdges ((∅ : Finset (Sym2 (Fin 4))) : Set (Sym2 (Fin 4)))
  refine ⟨delG.connectedComponentMk 0, ?_⟩
  rw [Set.ncard_eq_toFinset_card']
  have hcomp : (delG.connectedComponentMk 0).supp.toFinset = Finset.univ := by
    ext v
    simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff, Finset.mem_univ,
      iff_true]
    apply SimpleGraph.ConnectedComponent.eq.mpr
    by_cases hv : v = 0
    · subst hv; exact SimpleGraph.Reachable.refl 0
    · refine SimpleGraph.Adj.reachable ?_
      exact SimpleGraph.deleteEdges_adj.2 ⟨by simp [k4Graph, hv], by simp⟩
  rw [hcomp, Finset.card_fin]
  omega

/-- Concrete segregator cheating vs separator soundness on the 3-vertex fork DAG `forkConeProtocol`:
`J = ∅` accepts locally despite global unsatisfiability, while pinning ancestor `2 ∈ J` yields
`IsSeparator {2}` and restores soundness (`¬ Accepts {2}`). -/
example :
    (¬ ∃ y : Fin 3 → Bool, ∀ q : Fin 2, forkConeProtocol.ValidAt q y) ∧
    forkConeProtocol.Accepts ∅ ∧
    (forkConeProtocol.IsSeparator {2} ∧ ¬ forkConeProtocol.Accepts {2}) :=
  segregator_shared_ancestor_unsound

/-! ### 1b. `SigmaThreeTIME`, `encSigmaThreeWitness`, and composition checks -/

example : evenBits (interleave [true, false] [false, true] ++ [true]) = [true, false] :=
  evenBits_interleave_append rfl (by decide)

example : oddBits (interleave [true, false] [false, true] ++ [true]) = [false, true] :=
  oddBits_interleave_append rfl (by decide)

example : 0 < (encSigmaThreeWitness ⟨[true], [], [false]⟩).length ∧
    Function.Injective encSigmaThreeWitness :=
  ⟨by decide, encSigmaThreeWitness.injective⟩

example : lastBitLanguage ∈ SigmaThreeTIME encBits id :=
  SigmaTwoTIME_subset_SigmaThreeTIME encBits id lastBitLanguage_mem_SigmaTwoTIME

example : lastBitLanguageᶜ ∈ SigmaThreeTIME encBits id :=
  compl_mem_SigmaThreeTIME_of_mem_SigmaTwoTIME (NTIME_subset_SigmaTwoTIME
    (DTIME_subset_NTIME lastBitLanguage_mem_DTIME))

example : lastBitLanguage ∈ SigmaP 3 encBits :=
  mem_SigmaP_three_of_mem_SigmaThreeTIME
    (SigmaThreeTIME_mono (t₂ := fun n => (n + 1) ^ 1) (fun _ => by dsimp; rw [pow_one]; omega)
      (SigmaTwoTIME_subset_SigmaThreeTIME encBits id lastBitLanguage_mem_SigmaTwoTIME))

/-! ### 2. `lastBitLanguage`, `OracleAltTree`, and `RACfgCompact` checks -/

example : [false, true] ∈ lastBitLanguage := by simp [lastBitLanguage]

example : [true, false] ∉ lastBitLanguage := by simp [lastBitLanguage]

example : lastBitLanguage ∈ RADTIME (fun n => Nat.log 2 (n + 2)) :=
  lastBitLanguage_mem_RADTIME_log

example : ¬ (SigmaTwoTIME encBits id ⊆
    ATIME encBits (fun n => n / Nat.sqrt (Nat.log 2 n))) :=
  not_SigmaTwoTIME_subset_ATIME_seq

/-- Concrete `OracleAltTree` evaluation depends only on `witnessQueriedSet` (`≤ 2 ^ depth`). -/
example :
    let tree : OracleAltTree :=
      .query [false] (.leaf false) (.query [true] (.leaf true) (.leaf false))
    let oracle : List Bool → Bool := fun w => w == [true]
    tree.eval oracle = true ∧
      (witnessQueriedSet oracle tree).card ≤ 2 ^ tree.depth ∧
      tree.eval (fun w => if w ∈ witnessQueriedSet oracle tree then oracle w else false) = true :=
  ⟨by decide, witnessQueriedSet_card_le _ _,
    eval_eq_true_of_eqOn_witnessQueriedSet (A := fun w => w == [true]) (by decide)
      (fun q hq => by simp [hq])⟩

/-- Concrete `RACfgCompact` round-trip and bit-width bound. -/
example : ((RACfg.init (0 : Fin 2) : RACfg 1 (Fin 2)).pack 4).unpack = RACfg.init 0 :=
  RACfgCompact.unpack_pack (RACfg.init_withinWindow 0 4)

example : compactCfgBitWidth 1 1 4 ≤ 52 := by
  decide

example :
    Nat.sqrt (65536 * 4096) ≤
      2 * (Nat.sqrt 1 + 1) * (65536 / Nat.sqrt (Nat.log 2 65536)) :=
  sqrt_mul_le_div_sqrt_log (by omega) (by decide)

/-- Positive instance of `sigma2AsymmetricBlockSimulation`: merged `∃ ∀ ∃` acceptance. -/
example :
    let step₁ : Bool → Bool → Bool := fun s b => s || b
    let step₂ : (Fin 1 → Bool) → Bool → Bool := fun _ s => s
    let acc : Bool → Bool := fun s => s
    ∃ cu : Bool × (Fin (1 + 1) → Bool),
      ∀ svp : (side : Bool) × cond side ((Fin 1 → Bool) × (Fin (1 + 1) → Bool)) (Fin 1),
        ∃ wq : cond svp.1 (Fin 1) (Fin 2 → Bool),
          sigma2AsymEval step₁ step₂ acc false 1 2 1 1 cu.1 cu.2 svp wq := by
  intro step₁ step₂ acc
  rw [← sigma2AsymmetricBlockSimulation (C := Bool) (r := 1) step₁ step₂ acc false
    1 2 1 1 (by omega) (by omega) (by omega)]
  refine ⟨fun _ => true, fun _ => ?_⟩
  decide

/-- Negative instance of `sigma2AsymmetricBlockSimulation`: rejecting challenge rules out `∃∀∃`. -/
example :
    let step₁ : Bool → Bool → Bool := fun s b => s || b
    let step₂ : (Fin 1 → Bool) → Bool → Bool := fun y s => s && !(y 0)
    let acc : Bool → Bool := fun s => s
    ¬ ∃ cu : Bool × (Fin (1 + 1) → Bool),
      ∀ svp : (side : Bool) × cond side ((Fin 1 → Bool) × (Fin (1 + 1) → Bool)) (Fin 1),
        ∃ wq : cond svp.1 (Fin 1) (Fin 2 → Bool),
          sigma2AsymEval step₁ step₂ acc false 1 2 1 1 cu.1 cu.2 svp wq := by
  intro step₁ step₂ acc
  rw [← sigma2AsymmetricBlockSimulation (C := Bool) (r := 1) step₁ step₂ acc false
    1 2 1 1 (by omega) (by omega) (by omega)]
  rintro ⟨w₁, hw₁⟩
  have hfalse := hw₁ (fun _ => true)
  simp [step₂, acc] at hfalse

/-! ### 3. Counting barrier, separation barrier, and conditional reduction checks -/

example (hCB : CountingBitInSigmaP 3) : PH encBits = SigmaP 3 encBits :=
  countingBitInSigmaP_three_collapses_PH_to_SigmaP_three hCB encBits

example (hCB : CountingBitInSigmaP 1) : PH encBits = NP encBits :=
  countingBitInSigmaP_one_collapses_PH_to_NP hCB encBits

example : 16 ≤ 16 ^ 2 / Nat.sqrt (Nat.log 2 (16 ^ 2 + 2)) :=
  linear_le_sq_div_sqrt_log (by omega)

example : HasSharpNTimeGap (fun n => (n + 1) ^ 0) (fun n => (n + 1) ^ 14) :=
  polynomial_NTIME_gap_witness (by omega)

example (input : List Bool) :
    let queries : (Fin 2 → Option Bool) → Fin 1 → Unit → Unit → Fin 2 → ℕ :=
      fun a u _ _ i => if i.val = 0 then u.val else if a 0 = some true then 1 else 2
    (∃ u : Fin 1, ∀ _v : Unit, ∃ _w : Unit,
      (adaptiveQueryTrace input queries u () () 1 == some true) = true) ↔
      ∃ u : Fin 1, ∀ _v : Unit, ∃ (_w : Unit) (ans : Fin 2 → Option Bool),
        (ans 1 == some true) = true ∧
          ∀ i : Fin 2, ans i = input[queries ans u () () i]? := by
  intro queries
  refine RA_query_log_elimination (t := 2) input queries
    ?_ (fun ans _ _ _ => ans 1 == some true)
  intro a₁ a₂ u v w i hpref
  fin_cases i
  · rfl
  · have h0 : a₁ 0 = a₂ 0 := hpref 0 (by decide)
    simp [queries, h0]

/-- Concrete model-compatibility check uniting `RAATM.accepts_iff_accCount_pos` and uniform
`exists_RAATIME_evaluator_of_H`. -/
example {T F : ℕ → ℕ} (hH : HypothesisH T F) {k : ℕ} {State : Type} [Finite State]
    (M : RAATM k State) (hphase : RAATM.HasPhaseBound 1 false M)
    (hhalt : ∀ x, M.ClockedHalts x (T x.length)) :
    ∃ (kE : ℕ) (StateE : Type) (_ : Finite StateE) (E : RAATM (kE + 1) StateE),
      ∀ x : List Bool,
        M.Accepts x ↔ ∃ b : List Bool, b.length = Nat.log 2 (T x.length) + 1 ∧
          E.AcceptsFromAux x b := by
  obtain ⟨_c₁, _c₂, kE, StateE, hfinE, E, hE⟩ := exists_RAATIME_evaluator_of_H hH M hphase hhalt
  exact ⟨kE, StateE, hfinE, E, fun x =>
    (M.accepts_iff_accCount_pos hphase hhalt x).trans (hE x).2.symm⟩

/-- Non-vacuous `remaining_lemmas_imply_containment` and `mem_SigmaThreeTIME_of_composition_of_le`
client deriving `lastBitLanguage ∈ SigmaThreeTIME encBits id` from a length-1 switch witness
`c = [true]`, `Σ₃` reachability `E`, and `Σ₂` rejection test `B`. -/
example : lastBitLanguage ∈ SigmaThreeTIME encBits id := by
  let s : ℕ → ℕ := fun _ => 1
  let E : Set (List Bool × List Bool) := {p | p.1 ∈ lastBitLanguage ∧ (p.2.drop 1).isEmpty}
  let B : Set (List Bool × List Bool) := {p | p.2.isEmpty}
  have hle_enc (bs : List Bool) : (encList encBool bs).length ≤ bs.length * 3 :=
    length_encList_le encBool bs (b := 1) fun _ _ => by simp [encBool_apply]
  have h1 := computableInO_indicator_lastBitLanguage.comp_linear
    (ComputableInO.fst encBits encBits)
  have h2l := ComputableInDegree.bitsToList.inO_one.comp_linear
    (ComputableInO.snd encBits encBits)
  have hdrop := ComputableInO.drop' h2l (ComputableInO.const (α := List Bool × List Bool) 1)
  have his := ComputableInO.isEmpty' hdrop
  have hind := ComputableInO.and' h1 his
  have hE_d : E ∈ DTIME (encPair encBits encBits) id := by
    have hmem : {x : List Bool × List Bool | ((indicator lastBitLanguage ∘ Prod.fst) x &&
        (List.drop 1 (((fun word => word) ∘ Prod.snd) x)).isEmpty) = true} ∈
        DTIME (encPair encBits encBits) (fun n => 30 * n + 30) :=
      setOf_mem_DTIME_of_computableInO hind fun x => by
        have ha := hle_enc x.2
        have hdl : (x.2.drop 1).length ≤ x.2.length := by simp
        have hb := (hle_enc (x.2.drop 1)).trans (Nat.mul_le_mul_right 3 hdl)
        simp only [Function.comp_apply, length_encPair, encBits_apply, encUnary_apply,
          List.length_replicate] at ha hb ⊢
        omega
    have hset : E = {x : List Bool × List Bool | ((indicator lastBitLanguage ∘ Prod.fst) x &&
        (List.drop 1 (((fun word => word) ∘ Prod.snd) x)).isEmpty) = true} := by
      ext x
      simp [E, indicator]
    rw [hset]
    exact DTIME_mono_of_le_mul_add (C := 30) (fun _ => le_rfl) hmem
  have hE : E ∈ SigmaThreeTIME (encPair encBits encBits) id :=
    SigmaTwoTIME_subset_SigmaThreeTIME _ id (NTIME_subset_SigmaTwoTIME (DTIME_subset_NTIME hE_d))
  have hB_ind := ComputableInO.isEmpty' h2l
  have hB : B ∈ SigmaTwoTIME (encPair encBits encBits) id := by
    have hmem : {x : List Bool × List Bool |
        (((fun word => word) ∘ Prod.snd) x).isEmpty = true} ∈
        DTIME (encPair encBits encBits) (fun n => 10 * n + 10) :=
      setOf_mem_DTIME_of_computableInO hB_ind fun x => by
        have ha := hle_enc x.2
        simp only [Function.comp_apply, length_encPair, encBits_apply] at ha ⊢
        omega
    have hset : B = {x : List Bool × List Bool |
        (((fun word => word) ∘ Prod.snd) x).isEmpty = true} := by
      ext x
      simp [B]
    rw [hset]
    exact NTIME_subset_SigmaTwoTIME (DTIME_subset_NTIME
      (DTIME_mono_of_le_mul_add (C := 10) (fun _ => le_rfl) hmem))
  have hs_comp : ComputableInO (fun x : List Bool => s x.length) encBits encUnary
      (fun x => x.length + id x.length) (fun x => x.length + id x.length) :=
    (ComputableInO.const 1).mono_le (fun _ => by simp) (fun _ => by simp)
  have hA : HasSwitchCompression encBits id lastBitLanguage s id E B := by
    refine ⟨⟨1, fun _ => by simp [s], hs_comp⟩, hE, ⟨3, fun a c hc => ?_⟩, ?_, fun a => ?_⟩
    · have hs1 : c.length ≤ 1 := hc
      simp only [id_eq, length_encPair, encBits_apply]
      omega
    · intro a c hc
      cases c with
      | nil => simp [s]
      | cons _ t =>
        have ht : t = [] := by simpa [E] using hc.2
        subst ht
        simp [s]
    · constructor
      · intro ha
        exact ⟨[true], ⟨ha, by simp⟩, by simp [B]⟩
      · rintro ⟨c, ⟨ha, _⟩, _⟩
        exact ha
  have hB' : HasTwoBlockRejection encBits id s id B := by
    refine ⟨hB, 3, fun a c hc => ?_⟩
    have hs1 : c.length ≤ 1 := hc
    simp only [id_eq, length_encPair, encBits_apply]
    omega
  exact remaining_lemmas_imply_containment (fun _ => le_rfl) hA hB'

private def constHeadRAATM (out : Option Bool → Bool) : RAATM 2 Unit where
  q₀ := ()
  univ _ := false
  tr _ _ _ inSym _ :=
    { nextState := none
      outBit := out inSym
      idxWrite := none
      idxMove := 0
      workWrite _ := none
      workMove _ := 0 }

private theorem constHeadRAATM_det (out : Option Bool → Bool) :
    (constHeadRAATM out).IsDeterministic :=
  ⟨fun _ => rfl, fun _ _ _ _ _ _ => rfl⟩

private theorem raComputableBound_zero : RAComputableBound (fun _ => 1) (fun _ => 0) := by
  refine ⟨0, 1, 2, Unit, inferInstance, constHeadRAATM (fun _ => false),
    constHeadRAATM_det _, fun x => ⟨1, by omega, rfl, rfl⟩⟩

private theorem radetVerify_constHeadRAATM (out : Option Bool → Bool) (x aux : List Bool) :
    RADetVerify (constHeadRAATM out) x aux 1 = out x[0]? := rfl

private theorem headBit_compression :
    RASwitchCompression (fun _ => 1) (fun _ => 1)
      ({x : List Bool | x[0]? = some true} : Set (List Bool)) (fun _ => 0) (fun _ _ => False) := by
  refine ⟨0, 0, 0, 1, 1, fun _ => 0, Unit, inferInstance,
    constHeadRAATM (fun inSym => inSym == some true), constHeadRAATM_det _,
    raComputableBound_zero, fun _ => by simp, raComputableBound_zero, fun _ => by simp,
    fun _ _ _ _ _ _ _ _ _ => rfl, fun x => ?_⟩
  constructor
  · intro hx
    refine ⟨[], le_rfl, ⟨[], le_rfl, fun _ _ => ⟨[], le_rfl, ?_⟩⟩, False.elim⟩
    dsimp only
    rw [show 0 * 1 + 1 = 1 from rfl, radetVerify_constHeadRAATM]
    simpa using hx
  · rintro ⟨_, _, ⟨_, _, hw⟩, _⟩
    obtain ⟨_, _, hx⟩ := hw [] (by simp)
    dsimp only at hx
    rw [show 0 * 1 + 1 = 1 from rfl, radetVerify_constHeadRAATM] at hx
    simpa using hx

private theorem headBit_rejection :
    RATwoBlockRejection (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ _ => False) := by
  refine ⟨0, 0, 1, 1, fun _ => 0, Unit, inferInstance, constHeadRAATM (fun _ => false),
    constHeadRAATM_det _, raComputableBound_zero, fun _ => by simp,
    fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => ?_⟩
  refine ⟨False.elim, fun ⟨_, _, hq⟩ => ?_⟩
  have h := hq [] (by simp)
  dsimp only at h
  rw [show 0 * 1 + 1 = 1 from rfl, radetVerify_constHeadRAATM] at h
  exact Bool.false_ne_true h

/-- Non-vacuous `RA_remaining_lemmas_imply_containment` client verifying `headBitLanguage`
`{x | x[0]? = some true}` satisfies both `RASwitchCompression` and `RATwoBlockRejection`
(including `RAComputableBound`) at `T = F = 1`, `s = ℓE = ℓB = 0`. -/
example :
    RASwitchCompression (fun _ => 1) (fun _ => 1)
      ({x : List Bool | x[0]? = some true} : Set (List Bool)) (fun _ => 0) (fun _ _ => False) ∧
      RATwoBlockRejection (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ _ => False) :=
  ⟨headBit_compression, headBit_rejection⟩

example :
    ∃ (Cs KE cE₁ cE₂ kE KB cB₁ cB₂ kB : ℕ) (ℓE ℓB : ℕ → ℕ)
      (StateE : Type) (_ : Finite StateE) (ME : RAATM (kE + 1) StateE)
      (StateB : Type) (_ : Finite StateB) (MB : RAATM (kB + 1) StateB),
      ME.IsDeterministic ∧ MB.IsDeterministic ∧
      RAComputableBound (fun _ => 1) (fun _ => 0) ∧
      (∀ _n : ℕ, 0 ≤ Cs * 1 + Cs) ∧
      RAComputableBound (fun _ => 1) ℓE ∧
      (∀ n : ℕ, ℓE n ≤ KE * 1 + KE) ∧
      RAComputableBound (fun _ => 1) ℓB ∧
      (∀ n : ℕ, ℓB n ≤ KB * 1 + KB) ∧
      (∀ (x c u v w : List Bool), c.length ≤ 0 → u.length ≤ ℓE x.length →
        v.length ≤ ℓE x.length → w.length ≤ ℓE x.length →
        (ME.runCoins x (RACfg.initWithAux ME.q₀ (Nat.succ_pos kE)
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
            (c, ⟨u, v, w⟩)))
          (List.replicate (cE₁ * 1 + cE₂) false)).state = none) ∧
      (∀ (x c p q : List Bool), c.length ≤ 0 → p.length ≤ ℓB x.length →
        q.length ≤ ℓB x.length →
        (MB.runCoins x (RACfg.initWithAux MB.q₀ (Nat.succ_pos kB)
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
            (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
            (c, (p, q))))
          (List.replicate (cB₁ * 1 + cB₂) false)).state = none) ∧
      ∀ x : List Bool, x ∈ ({x | x[0]? = some true} : Set (List Bool)) ↔
        ∃ cu : {c : List Bool // c.length ≤ 0} × {u : List Bool // u.length ≤ ℓE x.length},
          ∀ svp : (side : Bool) × cond side {p : List Bool // p.length ≤ ℓB x.length}
              {v : List Bool // v.length ≤ ℓE x.length},
            ∃ wq : cond svp.1 {q : List Bool // q.length ≤ ℓB x.length}
                {w : List Bool // w.length ≤ ℓE x.length},
              selectorEval
                (fun (_ : Unit) (cs : {c : List Bool // c.length ≤ 0}) u v w =>
                  RADetVerify ME x
                    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
                      (cs.1, ⟨u.1, v.1, w.1⟩))
                    (cE₁ * 1 + cE₂))
                (fun (_ : Unit) (cs : {c : List Bool // c.length ≤ 0}) p q =>
                  RADetVerify MB x
                    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
                      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
                        Turing.MultiTapeTM.encBits)
                      (cs.1, (p.1, q.1)))
                    (cB₁ * 1 + cB₂))
                Unit.unit cu svp wq :=
  RA_remaining_lemmas_imply_containment headBit_compression headBit_rejection

end CslibFrontierTests.SigmaThreeSpeedup
