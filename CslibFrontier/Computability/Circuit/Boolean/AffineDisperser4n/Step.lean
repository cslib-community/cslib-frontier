/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Normal

/-!
# Case 5b and Lemma 4.2 (`State.Valid.exists_step`) for `4n - 9d` gate elimination

In a normal state `S` with `d < S.a`, `S.gates` is nonempty (`State.Valid.exists_gate_of_normal`),
and its minimal gate `G` reads no other gates (`State.exists_minGate`) and is non-affine.

* While `G` reads an auxiliary variable `Q ∈ S.aux` (`0 < S.auxIn G`), we find a parameter
  `y` in `Q`'s affine representation distinct from the other input of `G`, perform `(AR)`
  `S.swap y Q c T` (`State.Valid.preparation_swap_auxIn`), which is a preparatory operation keeping
  `gates` unchanged and strictly decreasing `auxIn G`.
* Once `G` reads two distinct unpaired parameters `t₁, t₂ ∈ S.unpaired`, `S.out` cannot read `G`,
  so some gate `K ≠ G` reads `G`. Pair creation `(PC)` (`State.addPair ⟨t₁, α, t₂, β⟩`) makes `G`
  constant `γ` on `Z(P')` and turns `t₁, t₂` from weight `5` into paired (`Δq = +1`, `ΔW = -7`).
  Deleting `G` and then `K` yields `Δm = 0, Δs = -2, Δa = -1, ΔW ≤ -9 = 9 Δa`
  (`State.Valid.step_of_pairCreation`).

Combining with Cases 1–5a gives Lemma 4.2 (`State.Valid.exists_step`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.auxArg`: indicator that an argument is
  auxiliary.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.auxIn`: number of auxiliary arguments of a gate.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_gate_of_normal`: a normal state
  with `d < S.a` has at least one gate.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.preparation_swap_auxIn`: swapping an
  auxiliary input of the minimal gate preserves validity with `ΔW ≤ 0` and lowers `auxIn`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.preparation_swap_auxIn_of`: the concrete
  swap `S.swap y a c T` for a given auxiliary input `a` and unpaired parameter `y`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_deleteGate_affineIn`: deleting a gate
  whose auxiliary input's affine representation uses only the gate's other input.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_pairCreation_of`: the concrete Case
  5b state, pair creation followed by deleting `G` and a gate `K` reading it.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_of_pairCreation`: Case 5b `(PC)`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_step`: Lemma 4.2, every valid
  state with `d < S.a` admits a step reducing `m + s` with `Δa ∈ {0, -1, -2}` and `ΔW ≤ 9 Δa`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  labels follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ}

/-! ### Minimal gate and auxiliary inputs -/

/-- Indicator (`0` or `1`) of whether a gate argument is an auxiliary variable of `S`. -/
@[expose] def auxArg (S : State n) : Arg → ℕ
  | .const _ => 0
  | .node x => if x ∈ S.aux then 1 else 0

/-- The number of arguments of gate `G` that belong to `S.aux` (`0`, `1`, or `2`). -/
@[expose] def auxIn (S : State n) (G : ℕ) : ℕ :=
  S.auxArg (S.gate G).left + S.auxArg (S.gate G).right

/-- In a normal state with `d < S.a`, `S.gates` is nonempty. -/
theorem Valid.exists_gate_of_normal {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a) (_hN : S.Normal) :
    S.gates.Nonempty := by
  refine Finset.nonempty_iff_ne_empty.2 fun hne => ?_
  cases hout : S.out.arg with
  | const b =>
    refine Valid.out_not_affine hS hf ha (b ^^ S.out.neg) (Finset.empty_subset _) fun val _ _ => ?_
    simp [Lit.eval, hout, Arg.eval_const]
  | node i =>
    have hilive := hS.wf.out_live i hout
    simp only [SemiCircuit.live, hne, Finset.union_empty, Finset.mem_union] at hilive
    rcases hilive with hi | hi
    · exact Valid.not_out_reads_param hS hf ha hi hout
    · obtain ⟨c, T, haff⟩ := hS.wf.exists_affineIn hi
      refine Valid.out_not_affine hS hf ha (c ^^ S.out.neg) haff.1 fun val hcons _ => ?_
      simp only [Lit.eval, hout, Arg.eval_node, haff.2 val hcons.1]
      generalize ∑ j ∈ T, val j = s
      cases c <;> cases S.out.neg <;> cases s <;> rfl

/-- The minimum gate identifier in `S.gates` reads no gates. -/
theorem Valid.minGate_reads {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hne : S.gates.Nonempty) :
    let G := S.gates.min' hne
    G ∈ S.gates ∧ ∀ i, (S.gate G).Reads i → i ∉ S.gates :=
  ⟨Finset.min'_mem S.gates hne, fun i hread hi =>
    not_lt_of_ge (Finset.min'_le S.gates i hi)
      (hS.wf.reads_lt _ (Finset.min'_mem S.gates hne) i hi hread)⟩

/-- If gate `G` reads distinct inputs `a ≠ b` and the affine representation `c + ∑ T` of `a`
uses no parameter other than `b`, then substituting that representation for `a` into `G` gives a
literal reading only inputs of `G` and agreeing with `G` on every equation solution. -/
private theorem lit_subst_affineIn {S : State n} {G a b : ℕ} {c : Bool} {T : Finset ℕ}
    (hab : a ≠ b) (hGa : (S.gate G).Reads a) (hGb : (S.gate G).Reads b)
    (haff : S.AffineIn a c T) (hT : T ⊆ {b}) :
    let ℓ := ((S.gate G).subst a (if T = ∅ then Lit.const c else ⟨.node b, c⟩)).lit
    (∀ t, ℓ.Reads t → (S.gate G).Reads t) ∧
      ∀ val, S.EqnsHold val → S.Locus val → (S.gate G).eval val = ℓ.eval val := by
  intro ℓ
  by_cases hTe : T = ∅
  · simp only [ℓ, hTe, ↓reduceIte]
    have hg'deg : ((S.gate G).subst a (Lit.const c)).Degenerate :=
      hGa.imp (fun h => ⟨c, by simp [Gate.subst, h, Arg.substArg, Lit.const]⟩)
        fun h => Or.inl ⟨c, by simp [Gate.subst, h, Arg.substArg, Lit.const]⟩
    exact ⟨fun t ht => (Gate.reads_of_reads_subst (Gate.reads_of_lit_reads ht)).elim id
        fun ⟨_, harg⟩ => by simp [Lit.const] at harg,
      fun val hval _ =>
        (Gate.eval_subst (by simp [haff.2 val hval, hTe, Lit.eval_const])).symm.trans
          (Gate.eval_lit hg'deg val)⟩
  · simp only [ℓ, hTe, ↓reduceIte]
    have hT_eq : T = {b} := (Finset.subset_singleton_iff.1 hT).resolve_left hTe
    have hg'deg : ((S.gate G).subst a ⟨.node b, c⟩).Degenerate := Or.inr <| Or.inr <| by
      rcases Gate.args_of_reads hab hGa hGb with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
        simp [Gate.subst, hl, hr, Arg.substArg, hab.symm]
    exact ⟨fun t ht => (Gate.reads_of_reads_subst (Gate.reads_of_lit_reads ht)).elim id
        fun ⟨_, harg⟩ => Arg.node.inj harg ▸ hGb,
      fun val hval _ => (Gate.eval_subst <| by
        rw [haff.2 val hval, hT_eq, Finset.sum_singleton]
        exact Bool.xor_comm c (val b)).symm.trans (Gate.eval_lit hg'deg val)⟩

/-- If a gate of a normal state reads distinct inputs `a ≠ b` with `a ∈ S.aux`, then `a`'s
affine representation contains some unpaired parameter `y ≠ b` of degree at least `2`. -/
private theorem exists_param_for_swap_of_aux_input {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) (hN : S.Normal) {G a b : ℕ} (hG : G ∈ S.gates) (hab : a ≠ b)
    (hGa : (S.gate G).Reads a) (hGb : (S.gate G).Reads b) (ha : a ∈ S.aux) :
    ∃ y c T, S.AffineIn a c T ∧ y ∈ T ∧ y ≠ b ∧ y ∈ S.unpaired ∧ 2 ≤ S.deg y := by
  obtain ⟨c, T, haff⟩ := hS.wf.exists_affineIn ha
  by_cases hT : T ⊆ {b}
  · obtain ⟨hreads, heval⟩ := lit_subst_affineIn hab hGa hGb haff hT
    exact absurd (Or.inl ⟨G, hG, _, hreads, heval⟩) hN.no_deletion
  · obtain ⟨y, hyT, hyb⟩ := Finset.not_subset.1 hT
    obtain ⟨e, he, hye⟩ :=
      haff.mem_terms hS.wf (fun hp => hS.wf.notMem_aux_of_mem_params hp ha) hyT
    obtain ⟨hyunp, hdeg⟩ := hN.unpaired_of_mem_terms he hye (haff.1 hyT)
    exact ⟨y, c, T, haff, hyT, by simpa using hyb, hyunp, hdeg⟩

/-- When gate `G` reads distinct inputs `a ≠ b` and the affine representation `c + ∑ T` of `a`
uses no parameter other than `b`, deleting `G` in favour of the literal obtained by substituting
that representation for `a` is a valid step. -/
theorem Valid.step_deleteGate_affineIn {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {G a b : ℕ} {c : Bool} {T : Finset ℕ} (hG : G ∈ S.gates) (hab : a ≠ b)
    (hGa : (S.gate G).Reads a) (hGb : (S.gate G).Reads b) (haff : S.AffineIn a c T)
    (hT : T ⊆ {b}) :
    Step f S (S.deleteGate G
      ((S.gate G).subst a (if T = ∅ then Lit.const c else ⟨.node b, c⟩)).lit) := by
  obtain ⟨hreads, heval⟩ := lit_subst_affineIn hab hGa hGb haff hT
  exact Reduction.step_of_delete (hS.reduction_deleteGate ⟨hG, hreads, Or.inl heval⟩
    fun _ _ => List.mem_singleton_self _) hS

/-- Swapping an auxiliary input `a` of the minimal gate with a parameter `y` of `a`'s affine
representation, unpaired and distinct from the gate's other input `b`, is a preparatory operation
keeping `gates` unchanged and strictly lowering `auxIn` of the minimal gate. -/
theorem Valid.preparation_swap_auxIn_of {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hne : S.gates.Nonempty) {a b y : ℕ} {c : Bool} {T : Finset ℕ} (hab : a ≠ b)
    (hGa : (S.gate (S.gates.min' hne)).Reads a) (hGb : (S.gate (S.gates.min' hne)).Reads b)
    (ha_aux : a ∈ S.aux) (haff : S.AffineIn a c T) (hyT : y ∈ T) (hyb : y ≠ b)
    (hyunp : y ∈ S.unpaired) :
    Preparation f S (S.swap y a c T) ∧ (S.swap y a c T).gates = S.gates ∧
      auxIn (S.swap y a c T) (S.gates.min' hne) < S.auxIn (S.gates.min' hne) := by
  generalize S.gates.min' hne = G at hGa hGb ⊢
  have hypar : y ∈ S.params := (mem_unpaired.1 hyunp).1
  have hswap : S.SwapOK y a c T := ⟨hypar, (mem_unpaired.1 hyunp).2, ha_aux, haff, hyT⟩
  have hy_ne_a : y ≠ a := fun h => hS.wf.notMem_aux_of_mem_params hypar (h ▸ ha_aux)
  have hydeg : 1 ≤ S.deg y := by
    obtain ⟨e, he, hye⟩ :=
      haff.mem_terms hS.wf (fun hp => hS.wf.notMem_aux_of_mem_params hp ha_aux) hyT
    exact Finset.card_pos.2 ⟨_, (SemiCircuit.inr_mem_children _).2 ⟨he, hye⟩⟩
  refine ⟨⟨Valid.swap hS hswap, hS.swap_m hswap, swap_size S y a c T, rfl,
    Valid.swap_W_le hS hswap hydeg⟩, rfl, ?_⟩
  -- `G` reads exactly `a` and `b`; `a` leaves `aux`, and `b ≠ y` does not enter it.
  have haux : (S.swap y a c T).aux = insert y (S.aux.erase a) := rfl
  have hgate : (S.swap y a c T).gate G = S.gate G := rfl
  rcases Gate.args_of_reads hab hGa hGb with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    simp [auxIn, auxArg, hgate, haux, hl, hr, ha_aux, hy_ne_a.symm, hyb.symm, hab.symm]

/-- Swapping an auxiliary input of the minimal gate with a suitable parameter preserves validity,
keeps `gates` and potential non-increasing, and strictly lowers `auxIn G`. -/
theorem Valid.preparation_swap_auxIn {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hN : S.Normal) (hne : S.gates.Nonempty) (hpos : 0 < S.auxIn (S.gates.min' hne)) :
    ∃ S' : State n, Preparation f S S' ∧ S'.gates = S.gates ∧
      S'.auxIn (S.gates.min' hne) < S.auxIn (S.gates.min' hne) := by
  have hG : S.gates.min' hne ∈ S.gates := Finset.min'_mem S.gates hne
  obtain ⟨u, v, huv, hGu, hGv⟩ := hN.two_reads_of_gate hG
  obtain ⟨a, b, hab, hGa, hGb, ha_aux⟩ : ∃ a b, a ≠ b ∧ (S.gate (S.gates.min' hne)).Reads a ∧
      (S.gate (S.gates.min' hne)).Reads b ∧ a ∈ S.aux := by
    by_cases hu : u ∈ S.aux
    · exact ⟨u, v, huv, hGu, hGv, hu⟩
    · refine ⟨v, u, huv.symm, hGv, hGu, by_contra fun hv => ?_⟩
      rcases Gate.args_of_reads huv hGu hGv with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
        simp [auxIn, auxArg, hl, hr, hu, hv] at hpos
  obtain ⟨y, c, T, haff, hyT, hyb, hyunp, -⟩ :=
    exists_param_for_swap_of_aux_input hS hN hG hab hGa hGb ha_aux
  exact ⟨_, Valid.preparation_swap_auxIn_of hS hne hab hGa hGb ha_aux haff hyT hyb hyunp⟩

/-! ### Case 5b: Pair creation (PC) on the minimal gate -/

/-- Pair creation `(PC)` on two distinct unpaired inputs `t₁, t₂` of a gate `G` computing
`((t₁ ⊕ α) ∧ (t₂ ⊕ β)) ⊕ γ`, followed by deleting `G` (now constant `γ`) and a gate `K` reading
`G`, is a valid step with `Δm = 0`, `Δs = -2`, `Δa = -1`, and `ΔW ≤ -9`. -/
theorem Valid.step_pairCreation_of {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {G t₁ t₂ : ℕ} (hG : G ∈ S.gates) (htne : t₁ ≠ t₂) (hGt₁ : (S.gate G).Reads t₁)
    (hGt₂ : (S.gate G).Reads t₂) (ht₁unp : t₁ ∈ S.unpaired) (ht₂unp : t₂ ∈ S.unpaired)
    {α β γ : Bool} (hG_eval : ∀ val, (S.gate G).eval val = (((val t₁ ^^ α) && (val t₂ ^^ β)) ^^ γ))
    {K : ℕ} (hK : K ∈ S.gates) (hKr : (S.gate K).Reads G) :
    Step f S
      (((S.addPair ⟨t₁, α, t₂, β⟩).deleteGate G (Lit.const γ)).deleteConstraint (.inl K)) := by
  have hdeg : ∀ {t}, (S.gate G).Reads t → 1 ≤ S.deg t := fun ht =>
    Finset.card_pos.2 ⟨_, (SemiCircuit.inl_mem_children _).2 ⟨hG, ht⟩⟩
  have hKG : K ≠ G := fun he => hS.not_reads_self hK (he ▸ hKr)
  have hpc : S.AddPairOK ⟨t₁, α, t₂, β⟩ := ⟨ht₁unp, ht₂unp, htne⟩
  have hS₁ := Valid.addPair hS hpc
  have hW₁ := Valid.addPair_W_eq hS hpc (hdeg hGt₁) (hdeg hGt₂)
  have hq₁ : (S.addPair ⟨t₁, α, t₂, β⟩).q = S.q + 1 := addPair_q hpc
  have hs₁ : (S.addPair ⟨t₁, α, t₂, β⟩).s = S.s := addPair_size S _
  have hm₁ : (S.addPair ⟨t₁, α, t₂, β⟩).m = S.m := rfl
  -- On the locus of the new pair, `G` is the constant `γ`.
  have hred₂ := hS₁.reduction_deleteConst (J := G) hG fun val _ hlocus => by
    have hholds := (ZeroPair.holds_iff_and_eq_false _ val).1
      (hlocus _ (Finset.mem_insert_self _ _))
    change (S.gate G).eval val = γ
    rw [hG_eval, hholds, Bool.false_xor]
  have hred := hred₂.trans_delete (hred₂.valid.reduction_deleteConstraint
    (deletable_deleteGate_child γ hK hKG hKr))
  have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u _ => Nat.add_le_add_right
    (Reduction.wt_le hred hS₁ fun _ hx => absurd hx (Finset.notMem_empty _)) 0
  have hm := hred.m_add
  have hs := hred.s_add
  have hq := hred.q_add
  have hqm := hred.valid.q_le_m
  rw [show (S.addPair ⟨t₁, α, t₂, β⟩).pairsMeeting ∅ = ∅ by ext; simp [pairsMeeting]] at hW hq
  simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.singleton_append,
    List.length_cons, List.length_nil, mul_zero, add_zero] at hW hm hs hq
  refine ⟨hred.valid, by omega, ?_, ?_, ?_⟩ <;> simp only [a] <;> omega

/-- When the minimal gate `G` is non-affine and reads two distinct parameters `t₁, t₂`, pair
creation `(PC)` plus deleting `G` and a gate reading `G` gives a valid step with `Δm = 0`,
`Δs = -2`, `Δa = -1`, and `ΔW ≤ -9`. -/
theorem Valid.step_of_pairCreation {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal)
    {G t₁ t₂ : ℕ} (hG : G ∈ S.gates) (hnotaff : ¬ IsAffineOp (S.gate G).op)
    (htne : t₁ ≠ t₂) (hGt₁ : (S.gate G).Reads t₁) (hGt₂ : (S.gate G).Reads t₂)
    (ht₁par : t₁ ∈ S.params) (ht₂par : t₂ ∈ S.params) :
    ∃ S', Step f S S' := by
  obtain ⟨ht₁unp, -⟩ := hN.unpaired_of_and_reads hG hnotaff htne ht₁par ht₂par hGt₁ hGt₂
  obtain ⟨ht₂unp, -⟩ := hN.unpaired_of_and_reads hG hnotaff htne.symm ht₂par ht₁par hGt₂ hGt₁
  obtain ⟨α, β, γ, hG_eval⟩ : ∃ α β γ, ∀ val,
      (S.gate G).eval val = (((val t₁ ^^ α) && (val t₂ ^^ β)) ^^ γ) := by
    obtain ⟨α, β, γ, hop⟩ := exists_and_form hnotaff
    rcases Gate.args_of_reads htne hGt₁ hGt₂ with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨α, β, γ, fun val => by rw [Gate.eval_of_args hl hr, hop]⟩
    · exact ⟨β, α, γ, fun val => by rw [Gate.eval_of_args hl hr, hop, Bool.and_comm]⟩
  have houtG : ¬ S.out.Reads G := fun hread =>
    Valid.false_of_fix hS hf ha ht₁par α ∅ (Finset.empty_subset _) (Finset.notMem_empty _)
      (γ ^^ S.out.neg) fun val hcons _ hfix => by
        have hout_eq : S.out.arg = .node G := hread
        have hv1 : val t₁ = α := by simpa using hfix
        simp [Lit.eval, hout_eq, Arg.eval_node, hcons.2 G hG, hG_eval, hv1]
  obtain ⟨K, hK, hKr⟩ : ∃ K ∈ S.gates, (S.gate K).Reads G :=
    by_contra fun hno =>
      hN.no_deletion (Or.inr (Or.inl ⟨G, hG, fun K hK hr => hno ⟨K, hK, hr⟩, houtG⟩))
  exact ⟨_, Valid.step_pairCreation_of hS hG htne hGt₁ hGt₂ ht₁unp ht₂unp hG_eval hK hKr⟩

/-! ### Lemma 4.2: Every valid state with `d < S.a` admits a step -/

private theorem Valid.exists_step_aux {f : BooleanFunction n} {d : ℕ} (hf : IsAffineDisperser f d) :
    ∀ (k₁ k₂ : ℕ) {S : State n}, S.Valid f → d < S.a → S.gates.card ≤ k₁ →
      (∀ hne : S.gates.Nonempty, S.auxIn (S.gates.min' hne) ≤ k₂) →
      ∃ S', Step f S S' := by
  intro k₁
  induction k₁ using Nat.strong_induction_on with
  | ind k₁ ih₁ =>
    intro k₂
    induction k₂ using Nat.strong_induction_on with
    | ind k₂ ih₂ =>
      intro S hS ha hk₁ hk₂
      by_cases hmov : S.Movable
      · obtain ⟨J, hJ, haff, hin⟩ := hmov
        obtain ⟨hprep, hlt⟩ := Valid.preparation_moveAffine hS hJ haff hin
        let S₁ := S.moveAffine J S.freshEqn
        obtain ⟨S', hstep⟩ := ih₁ S₁.gates.card (lt_of_lt_of_le hlt hk₁)
          (if hne : S₁.gates.Nonempty then auxIn S₁ (S₁.gates.min' hne) else 0) hprep.valid
          (by rwa [hprep.a_eq]) le_rfl fun hne => by rw [dite_eq_left hne]
        exact ⟨S', Step.of_preparation hprep hstep⟩
      · rcases Valid.step_or_normal hS hf ha hmov with hstep | hN
        · exact hstep
        · have hne := Valid.exists_gate_of_normal hS hf ha hN
          let G := S.gates.min' hne
          obtain ⟨hG, hmin⟩ := Valid.minGate_reads hS hne
          by_cases hpos : 0 < S.auxIn G
          · obtain ⟨S₁, hprep, hgates, hlt⟩ := Valid.preparation_swap_auxIn hS hN hne hpos
            obtain ⟨S', hstep⟩ := ih₂ (S₁.auxIn G) (lt_of_lt_of_le hlt (hk₂ hne)) hprep.valid
              (by rwa [hprep.a_eq]) (hgates ▸ hk₁) fun hne₁ => by simp only [G, hgates, le_refl]
            exact ⟨S', Step.of_preparation hprep hstep⟩
          · have haux0 : S.auxIn G = 0 := by omega
            have hnotaff : ¬ IsAffineOp (S.gate G).op := fun haff =>
              hmov ⟨G, hG, haff, hmin⟩
            obtain ⟨t₁, t₂, htne, hGt₁, hGt₂⟩ := hN.two_reads_of_gate hG
            have hmem_par : ∀ t, (S.gate G).Reads t → t ∈ S.params := fun t ht =>
              (Finset.mem_union.1 (hS.wf.reads_live G hG t ht)).elim
                (fun h => (Finset.mem_union.1 h).resolve_right fun hta => by
                  rcases ht with h | h <;> simp [auxIn, auxArg, h, hta] at haux0)
                fun hg => absurd hg (hmin t ht)
            exact Valid.step_of_pairCreation hS hf ha hN hG hnotaff htne hGt₁ hGt₂
              (hmem_par t₁ hGt₁) (hmem_par t₂ hGt₂)

/-- Lemma 4.2 (framework per issue `#4322`, unverified against [MishraSanthanam2027]; tightened
here from `ΔW ≤ 10 Δa` to `ΔW ≤ 9 Δa`): if `S` is a valid state for a `d`-affine disperser `f`
and `d < S.a`, then there is a valid step from `S` strictly reducing `m + s` with
`Δa ∈ {0, -1, -2}` and `ΔW ≤ 9 Δa`. -/
theorem Valid.exists_step {S : State n} {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) : ∃ S', Step f S S' :=
  let k₂ := if hne : S.gates.Nonempty then S.auxIn (S.gates.min' hne) else 0
  Valid.exists_step_aux hf S.gates.card k₂ hS ha le_rfl fun hne => by simp [k₂, hne]

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
