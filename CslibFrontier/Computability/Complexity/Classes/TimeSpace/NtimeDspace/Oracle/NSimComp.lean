/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.NSimStep
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Mathlib.Data.List.GetD

/-!
# Nondeterministic linear oracle time within linear space

If the oracle `A` is decidable within linear space, then `NTIME^A[n] ⊆ SPACE[n]`
(`NTIMEO_subset_DSPACE`): for a nondeterministic oracle machine `M` running within time
`T = c₁ n + c₂`, try every choice number `r < B^T` (`B` the number of instructions of `M`) one at
a time, each time simulating `T` steps of the choice run with universal steps
(`Cslib.Complexity.NtimeDspace.Oracle.OracleNTM.istep`), and accept when one of them halts with
output `[true]` (`Cslib.Complexity.NtimeDspace.Oracle.OracleNTM.accepts_iff_exists_choice`). The
counter `r` takes
`O(T)` bits and
a simulated configuration `O(T + log n)` bits, so the whole search runs in space `O(n)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
    _root_.Turing.MultiTapeTM.ComputableInSpace
  Cslib.Complexity

/-! ### One step of a deterministic oracle machine, with the input in the state -/

namespace OracleTM

variable {k : ℕ} {State : Type} [Fintype State] (D : OracleTM k State) (eS : State ↪ ℕ)
  {A : Set (List Bool)}

/-- The linear bound on the states of the simulated choice run. -/
noncomputable abbrev LZ (z : OracleNTM.Z) : ℕ := (OracleNTM.encZ z).length

lemma zxs_inSpace : ComputableInSpace (fun z : OracleNTM.Z => z.1) OracleNTM.encZ
    (encList encUnary) LZ := fst _ _

lemma zcur_inSpace : ComputableInSpace (fun z : OracleNTM.Z => z.2.1) OracleNTM.encZ encNat LZ :=
  (snd _ _).fst'

lemma zsim_inSpace : ComputableInSpace (fun z : OracleNTM.Z => z.2.2.1) OracleNTM.encZ encSim LZ :=
  (snd _ _).snd'.fst'

lemma zsum_inSpace : ComputableInSpace (fun z : OracleNTM.Z => z.2.2.2) OracleNTM.encZ
    (encFinite (Fin 3)) LZ :=
  (snd _ _).snd'.snd'

lemma zcfg_inSpace : ComputableInSpace (fun z : OracleNTM.Z => z.2.2.1.1) OracleNTM.encZ eCfg LZ :=
  zsim_inSpace.fst'

lemma zbuf_inSpace : ComputableInSpace (fun z : OracleNTM.Z => z.2.2.1.2) OracleNTM.encZ encBits
    LZ :=
  zsim_inSpace.snd'

lemma zstep_inSpace (d : Desc) : ComputableInSpace (fun z : OracleNTM.Z =>
    Universal.step d z.1 z.2.2.1.1) OracleNTM.encZ (encPair eCfg eSym) LZ := by
  have hctx : ComputableInSpace (fun z : OracleNTM.Z => (((d, z.1), z.2.2.1.1) : Ctx))
      OracleNTM.encZ eCtx LZ :=
    budget_prod (budget_prod (budget_const d (.refl _)) zxs_inSpace) zcfg_inSpace
  have hstep : ComputableInSpace (fun c : Ctx => Universal.step c.desc c.input c.cfg) eCtx
      (encPair eCfg eSym) fun c => (eCtx c).length := of_inO step_inO
  have h := budget_comp_lin hstep (.refl _) hctx
  exact h

lemma zflag_inSpace (d : Desc) : ComputableInSpace (fun z : OracleNTM.Z =>
    (Universal.step d z.1 z.2.2.1.1).2.isSome) OracleNTM.encZ encBool LZ :=
  budget_comp_lin (of_inO (ComputableInDegree.isSome encUnary).inO_one) (.refl _)
    (zstep_inSpace d).snd'

open scoped Classical in
lemma simNextX_inSpace
    (hA : ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    ComputableInSpace (fun z : OracleNTM.Z => D.simNextX eS A z.1 z.2.2.1) OracleNTM.encZ encSim
      LZ := by
  have hmem : ComputableInSpace (fun z : OracleNTM.Z => decide (z.2.2.1.2 ∈ A))
      OracleNTM.encZ encBool LZ :=
    budget_comp_lin hA (.of_le fun _ => le_rfl) zbuf_inSpace
  have hask := budget_prod (encC := encBits) (budget_ite hmem
    (zstep_inSpace (desc eS eBit (D.answerTM true))).fst'
    (zstep_inSpace (desc eS eBit (D.answerTM false))).fst') (budget_const [] (.refl _))
  have hbit := budget_finite (encC := encBits) (fun q : Bool × Bool => bitOf q.1 q.2)
    (budget_prod (zflag_inSpace (desc eS eBit (D.outTM (querySym true))))
      (zflag_inSpace (desc eS eBit (D.outTM (querySym false)))))
  have happ : ComputableInSpace (fun z : OracleNTM.Z =>
      z.2.2.1.2 ++ bitOf (Universal.step (desc eS eBit (D.outTM (querySym true))) z.1
        z.2.2.1.1).2.isSome (Universal.step (desc eS eBit (D.outTM (querySym false))) z.1
        z.2.2.1.1).2.isSome) OracleNTM.encZ encBits LZ :=
    (append zbuf_inSpace hbit (encD := encBits) fun _ => rfl).weaken (.add (.refl _) (.refl _))
  have hord := budget_prod (zstep_inSpace (desc eS eBit D.plainTM)).fst' happ
  refine (budget_ite (zflag_inSpace (desc eS eBit (D.outTM flagSym))) hask hord).of_enc_eq
    fun z => ?_
  simp only [simNextX]
  split_ifs <;> simp_all

lemma emitFlags_inSpace : ComputableInSpace (fun z : OracleNTM.Z => D.emitFlags eS z.1 z.2.2.1)
    OracleNTM.encZ (encPair encBool (encPair encBool encBool)) LZ :=
  budget_prod (zflag_inSpace _) (budget_prod (zflag_inSpace _) (zflag_inSpace _))

end OracleTM

/-! ### The simulated choice run is computable -/

namespace OracleNTM

variable {k : ℕ} {State : Type} [Fintype State] (M : OracleNTM k State) (eS : State ↪ ℕ)
  {A : Set (List Bool)}

open OracleTM in
/-- A step of the simulated choice run, in linear space. -/
theorem istep_inSpace
    (hA : open scoped Classical in
      ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    ComputableInSpace (M.istep eS A) encZ encZ LZ := by
  classical
  set B := nActs (k := k) (State := State)
  have hF : ∀ c : ℕ, ComputableInSpace (fun z : Z => ((M.choiceTM c).simNextX eS A z.1 z.2.2.1,
      supd z.2.2.2 ((M.choiceTM c).emitFlags eS z.1 z.2.2.1))) encZ
      (encPair encSim (encFinite (Fin 3))) LZ := fun c =>
    budget_prod (simNextX_inSpace (M.choiceTM c) eS hA)
      (budget_finite (encC := encFinite (Fin 3))
        (fun p : Fin 3 × (Bool × Bool × Bool) => supd p.1 p.2)
        (budget_prod zsum_inSpace (emitFlags_inSpace (M.choiceTM c) eS)))
  have hi : ComputableInSpace (fun z : Z => z.2.1 % B) encZ encNat LZ :=
    budget_comp_lin natMod ⟨32, fun _ => by simp only; omega⟩ (budget_prod zcur_inSpace
      (budget_const B (.refl _)))
  have hd := dispatch (List.range B) 0 _ hF hi
  have hdiv : ComputableInSpace (fun z : Z => z.2.1 / B) encZ encNat LZ :=
    budget_comp_lin natDiv ⟨32, fun _ => by simp only; omega⟩ (budget_prod zcur_inSpace
      (budget_const B (.refl _)))
  have hrun := budget_prod zxs_inSpace (budget_prod hdiv hd)
  have hh : ComputableInSpace (fun z : Z => z.2.2.1.1.state.isNone) encZ encBool LZ :=
    budget_comp_lin (g := fun s : SCfg × List Bool => s.1.state.isNone) simHalted_inSpace (.refl _)
      zsim_inSpace
  have hid : ComputableInSpace (fun z : Z => z) encZ encZ LZ := of_inO ComputableInO.id'
  refine (budget_ite hh hid hrun).of_enc_eq fun z => ?_
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (two_le_nActs (k := k) (State := State))
  have hg : (List.range B).getD (z.2.1 % B) 0 = z.2.1 % B := by
    rw [List.getD_eq_getElem _ _ (by simpa using Nat.mod_lt _ hB), List.getElem_range]
  simp only [istep, hg]
  split_ifs <;> rfl

/-! ### The search over choice numbers -/

/-- The states of the search: the numbered input and the time bound in unary, the next choice
number and whether an accepting choice was found. -/
abbrev Y := (List ℕ × ℕ) × (ℕ × Bool)

/-- The encoding of the states of the search. -/
abbrev encY : Y ↪ List Bool :=
  encPair (encPair (encList encUnary) encUnary) (encPair encNat encBool)

noncomputable abbrev LY (y : Y) : ℕ := (encY y).length

/-- Whether the choice number `y.2.1` is accepting, simulating `y.1.2` steps. -/
noncomputable def accY (A : Set (List Bool)) (y : Y) : Bool :=
  ((M.istep eS A)^[y.1.2] (M.z0 eS y.1.1 y.2.1)).2.2.1.1.state.isNone &&
    decide (((M.istep eS A)^[y.1.2] (M.z0 eS y.1.1 y.2.1)).2.2.2 = 1)

/-- A step of the search. -/
noncomputable def ostep (A : Set (List Bool)) (y : Y) : Y :=
  (y.1, (y.2.1 + 1, y.2.2 || M.accY eS A y))

lemma unary_to_nat {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f : α → ℕ}
    (h : ComputableInSpace f enc encUnary S) : ComputableInSpace f enc encNat S := by
  have h' : ComputableInSpace (fun a => List.replicate (f a) true) enc encBits S :=
    h.of_enc_eq fun _ => rfl
  have h2 := budget_comp_lin (g := fun l : List Bool => l.length) (of_inO ComputableInO.lengthNat)
    ⟨1, fun l => by simp [encBits_apply]⟩ h'
  exact h2.of_enc_eq fun a => by simp

theorem accY_inSpace
    (hA : open scoped Classical in
      ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    ComputableInSpace (M.accY eS A) encY encBool LY := by
  have hT : ComputableInSpace (fun y : Y => y.1.2) encY encUnary LY := (fst _ _).snd'
  have hn := unary_to_nat hT
  have hinit : ComputableInSpace (fun y : Y => M.z0 eS y.1.1 y.2.1) encY encZ LY :=
    budget_prod (fst _ _).fst' (budget_prod (snd _ _).fst'
      (budget_const (((M.sInit eS, []), 0) : (SCfg × List Bool) × Fin 3) (.refl _)))
  have hiter := budget_iterate (B := fun y : Y => (400 * k + 10 * OracleTM.stateBound eS + 100) *
      ((encList encUnary y.1.1).length + (encNat y.2.1).length + y.1.2 + 1))
    hn hinit (M.istep_inSpace eS hA)
    (fun y m hm => by
      have := M.length_encZ_le (eS := eS) (A := A) y.1.1 y.2.1 m
      exact this.trans (Nat.mul_le_mul_left _ (by omega)))
    ⟨400 * k + 10 * OracleTM.stateBound eS + 100, fun y => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      nlinarith⟩
  have hg : ComputableInSpace (fun z : Z => z.2.2.1.1.state.isNone && decide (z.2.2.2 = 1)) encZ
      encBool OracleTM.LZ :=
    budget_finite (encC := encBool) (fun p : Bool × Fin 3 => p.1 && decide (p.2 = 1))
      (budget_prod (budget_comp_lin (g := fun s : SCfg × List Bool => s.1.state.isNone)
        OracleTM.simHalted_inSpace (.refl _) OracleTM.zsim_inSpace)
        OracleTM.zsum_inSpace)
  have h := budget_comp_lin hg (.refl _) hiter
  exact h

theorem ostep_inSpace
    (hA : open scoped Classical in
      ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    ComputableInSpace (M.ostep eS A) encY encY LY :=
  budget_prod (fst _ _) (budget_prod (budget_comp_lin natSucc linear_succ (snd _ _).fst')
    (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 || p.2)
      (budget_prod (snd _ _).snd' (M.accY_inSpace eS hA))))

variable {M eS}

/-- Acceptance of a choice number, read off the simulated choice run. -/
lemma accY_iff (x : List Bool) (T r : ℕ) (f : Bool) :
    M.accY eS A ((x.map eBit, T), (r, f)) = true ↔
      ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.state = none ∧
      ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.output = [true] := by
  obtain ⟨hrel, -, -, hsum⟩ := istep_rel (M := M) (eS := eS) (A := A) x r T
  simp only [accY, Bool.and_eq_true, decide_eq_true_eq]
  rw [hsum, summ_eq_one, hrel.state]
  cases ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.state <;> simp

lemma ostep_iterate (xs : List ℕ) (T m : ℕ) : (M.ostep eS A)^[m] ((xs, T), (0, false)) =
    ((xs, T), (m, decide (∃ r < m, M.accY eS A ((xs, T), (r, false)) = true))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [ostep, Prod.mk.injEq, true_and]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨r, hr, h⟩ | h)
      · exact ⟨r, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨r, hr, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact .inl ⟨r, hr, h⟩
      · exact .inr h

end OracleNTM

lemma length_encList_map_eBit (x : List Bool) :
    (encList encUnary (x.map eBit)).length ≤ 3 * x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    simp only [List.map_cons, encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate, List.length_cons]
    have : eBit b ≤ 1 := by cases b <;> decide
    omega

lemma iterate_mul_one (B m : ℕ) : (fun n => n * B)^[m] 1 = B ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ]

lemma lin_bound (c₁ c₂ n : ℕ) : c₁ * n + c₂ ≤ (c₁ + c₂ + 1) * (n + 1) := by nlinarith

lemma length_encNat_pow_le (B m : ℕ) : (encNat (B ^ m)).length ≤ m * (encNat B).length + 1 := by
  induction m with
  | zero => simp [encNat_apply]
  | succ m ih =>
    rw [pow_succ]
    have := length_encNat_mul_le (B ^ m) B
    rw [Nat.succ_mul]
    omega

open OracleNTM in
/-- **Nondeterministic linear oracle time within linear space.** If the oracle `A` is decidable
within linear space, every language in `NTIME^A[n]` is in `DSPACE[n]`. -/
theorem NTIMEO_subset_DSPACE {A : Set (List Bool)}
    (hA : open scoped Classical in
      ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    NTIMEO A (fun n => n) ⊆ DSPACE encBits (fun n => n) := by
  classical
  rintro L ⟨c₁, c₂, k, State, hfin, M, hM⟩
  have := Fintype.ofFinite State
  set eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set B := nActs (k := k) (State := State)
  -- the time bound, in binary and in unary
  have hlen : ComputableInSpace (fun x : List Bool => x.length) encBits encNat
      fun x => x.length :=
    (of_inO ComputableInO.lengthNat).weaken ⟨1, fun x => by simp⟩
  have hT : ComputableInSpace (fun x : List Bool => c₁ * x.length + c₂) encBits encNat
      fun x => x.length := by
    have h1 := budget_comp_lin natMul ⟨64, fun _ => by simp only; omega⟩
      (budget_prod (budget_const c₁ (.of_le fun _ => by simp)) hlen)
    have h2 := budget_comp_lin natAdd ⟨64, fun _ => by simp only; omega⟩
      (budget_prod h1 (budget_const c₂ (.of_le fun _ => by simp)))
    exact h2
  have hTu : ComputableInSpace (fun x : List Bool => c₁ * x.length + c₂) encBits encUnary
      fun x => x.length :=
    budget_comp (of_inO ComputableInO.natToUnary) hT ⟨c₁ + c₂, fun x => by simp only; nlinarith⟩
  have hxs : ComputableInSpace (fun x : List Bool => x.map eBit) encBits (encList encUnary)
      fun x => x.length :=
    (of_inO Universal.computableInO_map_eBit).weaken
      ⟨1, fun x => by simp⟩
  have hinit : ComputableInSpace (fun x : List Bool =>
      (((x.map eBit, c₁ * x.length + c₂), (0, false)) : Y)) encBits encY fun x => x.length :=
    budget_prod (budget_prod hxs hTu) (budget_const ((0, false) : ℕ × Bool) (.of_le fun _ => by
      simp))
  -- the number of choice numbers, `B ^ T`
  have hpow : ComputableInSpace (fun x : List Bool => B ^ (c₁ * x.length + c₂)) encBits encNat
      fun x => x.length := by
    have hstep : ComputableInSpace (fun m : ℕ => m * B) encNat encNat fun m => (encNat m).length :=
      budget_comp_lin natMul ⟨64, fun _ => by simp only; omega⟩
        (budget_prod (of_inO ComputableInO.id') (budget_const B (.refl _)))
    have h := budget_iterate (n := fun x : List Bool => c₁ * x.length + c₂)
      (init := fun _ => 1) (step := fun m => m * B)
      (B := fun x => (c₁ * x.length + c₂) * (encNat B).length + 1) hT
          (budget_const 1 (.of_le fun _ => by simp))
      hstep (fun x m hm => by
        rw [iterate_mul_one]
        exact (length_encNat_pow_le B m).trans (by
          have := Nat.mul_le_mul_right (encNat B).length hm; omega))
      ⟨(c₁ + c₂ + 1) * ((encNat B).length + 1), fun x => by
        simp only
        have h := Nat.mul_le_mul_right (encNat B).length (lin_bound c₁ c₂ x.length)
        have h1 : 1 ≤ (c₁ + c₂ + 1) * (x.length + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        calc (c₁ * x.length + c₂) * (encNat B).length + 1
            ≤ (c₁ + c₂ + 1) * (x.length + 1) * (encNat B).length + (c₁ + c₂ + 1) *
                (x.length + 1) := by omega
          _ = (c₁ + c₂ + 1) * ((encNat B).length + 1) * (x.length + 1) := by ring⟩
    exact h.of_enc_eq fun x => by rw [iterate_mul_one]
  -- the search
  have hsearch := budget_iterate (n := fun x : List Bool => B ^ (c₁ * x.length + c₂))
    (init := fun x : List Bool => (((x.map eBit, c₁ * x.length + c₂), (0, false)) : Y))
    (step := M.ostep eS A)
    (B := fun x => 12 * x.length + 2 * (c₁ * x.length + c₂) +
      2 * ((c₁ * x.length + c₂) * (encNat B).length + 1) + 10) hpow hinit (M.ostep_inSpace eS hA)
    (fun x m hm => by
      rw [ostep_iterate]
      have h1 := length_encList_map_eBit x
      have h2 : (encNat m).length ≤ (c₁ * x.length + c₂) * (encNat B).length + 1 :=
        (length_encNat_mono hm).trans (length_encNat_pow_le B _)
      simp only [encY, length_encPair, encUnary_apply, List.length_replicate, encBool_apply,
        List.length_singleton]
      omega)
    ⟨30 * (c₁ + c₂ + 1) * ((encNat B).length + 1), fun x => by
      simp only
      have hP := lin_bound c₁ c₂ x.length
      have hn : x.length + 1 ≤ (c₁ + c₂ + 1) * (x.length + 1) := Nat.le_mul_of_pos_left _ (by omega)
      have h3 := Nat.mul_le_mul_right (encNat B).length hP
      have e : 30 * (c₁ + c₂ + 1) * ((encNat B).length + 1) * (x.length + 1) =
          30 * ((c₁ + c₂ + 1) * (x.length + 1) * (encNat B).length) + 30 *
              ((c₁ + c₂ + 1) * (x.length + 1)) := by
        ring
      omega⟩
  have hres : ComputableInSpace (fun x : List Bool =>
      ((M.ostep eS A)^[B ^ (c₁ * x.length + c₂)]
        (((x.map eBit, c₁ * x.length + c₂), (0, false)) : Y)).2.2) encBits encBool
      fun x => x.length :=
    budget_comp_lin (g := fun y : Y => y.2.2) (snd _ _).snd' (.refl _) hsearch
  have hind : ∀ x, ((M.ostep eS A)^[B ^ (c₁ * x.length + c₂)]
      (((x.map eBit, c₁ * x.length + c₂), (0, false)) : Y)).2.2 = MultiTapeTM.indicator L x := by
    intro x
    rw [ostep_iterate]
    simp only [MultiTapeTM.indicator]
    have hacc := accepts_iff_exists_choice (M := M) (A := A) (x := x) (hM x).1
    rw [← (hM x).2] at hacc
    by_cases hx : x ∈ L
    · simp only [hx, ite_true, decide_eq_true_eq]
      obtain ⟨r, hr, h⟩ := hacc.mp hx
      exact ⟨r, hr, (accY_iff x _ r false).mpr h⟩
    · simp only [hx, ite_false, decide_eq_false_iff_not, not_exists, not_and]
      intro r hr h
      exact hx (hacc.mpr ⟨r, hr, (accY_iff x _ r false).mp h⟩)
  obtain ⟨t, c, hc, -⟩ := hres.of_enc_eq (encC := encBool) (g := MultiTapeTM.indicator L)
    fun x => by rw [hind]
  refine mem_DSPACE_iff.mpr ⟨c, c, t, ?_⟩
  refine hc.mono (fun _ => le_rfl) fun x => ?_
  simp only [encBits_apply]
  ring_nf
  omega


end Cslib.Complexity.NtimeDspace.Oracle
