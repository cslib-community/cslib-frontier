/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.InterdomainRouting.StablePaths
public import Mathlib.Logic.Relation

/-!
# Gao–Rexford Commercial Routing Conditions and BGP Stability

Autonomous systems on the Internet maintain commercial relationships (`CommercialRel`): a neighbor
is a **customer**, a **peer**, or a **provider** ([GaoRexford2001];
[FeigenbaumSchapiraShenker2007], Chapter 14). These relationships induce three structural
conditions (`GaoRexfordConditions`) on an instance `S : SPP V` of the Stable Paths Problem:

1. **No Customer–Provider Cycles (`NoCustomerProviderCycle`)**: the directed provider-to-customer
   relation `IsProviderOf` is acyclic (`∀ u, ¬ Relation.TransGen (IsProviderOf G rel) u u`).
2. **Valley-Free Permitted Paths (`IsValleyFree`)**: along any permitted path toward `dest`, once a
   path traverses a `peer` or `customer` edge, every subsequent edge must be a `customer` edge
   (equivalently, edges follow the pattern `provider* → peer? → customer*`, capturing export
   filtering where ASes export peer and provider routes only to customers).
3. **Prefer-Customer (`PreferCustomer`)**: every AS strictly prefers any permitted path whose next
   hop is a customer over any permitted path whose next hop is a peer or provider (Gao–Rexford
   Guideline A; in particular, any strict `customer ≻ peer ≻ provider` ranking satisfies it).

## Main definitions

* `Cslib.GameTheory.InterdomainRouting.CommercialRel`: commercial AS-to-AS relationship
  (`customer`, `peer`, `provider`) and its orientation reversal `CommercialRel.flip`.
* `Cslib.GameTheory.InterdomainRouting.IsValleyFree`: the valley-free export condition on a path.
* `Cslib.GameTheory.InterdomainRouting.IsProviderOf`: directed provider-to-customer relation.
* `Cslib.GameTheory.InterdomainRouting.NoCustomerProviderCycle`: acyclicity of `IsProviderOf`.
* `Cslib.GameTheory.InterdomainRouting.PreferCustomer`: customer routes strictly outrank peer and
  provider routes.
* `Cslib.GameTheory.InterdomainRouting.GaoRexfordConditions`: bundle of commercial symmetry,
  acyclicity, valley-free permitted paths, and prefer-customer preferences on an `SPP`.

## Main results

* `Cslib.GameTheory.InterdomainRouting.GaoRexfordConditions.isEmpty_disputeWheel`:
  **Gao–Rexford theorem (no dispute wheel)** ([GaoRexford2001]; [FeigenbaumSchapiraShenker2007],
  Chapter 14): every `SPP` satisfying the Gao–Rexford commercial conditions has no dispute wheel.
* `Cslib.GameTheory.InterdomainRouting.GaoRexfordConditions.existsUnique_isStable`:
  **Gao–Rexford stability** ([GaoRexford2001]): every `SPP` satisfying the Gao–Rexford conditions
  admits a unique stable path assignment.
* `Cslib.GameTheory.InterdomainRouting.GaoRexfordConditions.exists_converges`:
  **Gao–Rexford safety** ([GaoRexford2001]; [GriffinShepherdWilfong2002]; atomic best-response
  model of [FeigenbaumSchapiraShenker2007], Chapter 14): asynchronous per-node atomic
  best-response BGP dynamics from `initAssignment` converge under every fair activation schedule
  to the unique stable path assignment.

## References

* [FeigenbaumSchapiraShenker2007]
* [GaoRexford2001]
* [GriffinShepherdWilfong2002]
-/

public section

namespace Cslib.GameTheory.InterdomainRouting

variable {V : Type*}

/-! ### Commercial relationships and valley-free paths -/

/-- Commercial relationship of neighbor `v` as seen from AS `u`: `v` is a `customer`, `peer`, or
`provider` of `u`. -/
inductive CommercialRel
  | customer
  | peer
  | provider
  deriving DecidableEq, Repr

/-- Reversing the perspective across an AS peering edge: a customer sees its neighbor as a
provider, a provider sees its neighbor as a customer, and peering is symmetric. -/
@[expose] def CommercialRel.flip : CommercialRel → CommercialRel
  | .customer => .provider
  | .peer => .peer
  | .provider => .customer

@[simp] theorem CommercialRel.flip_flip (r : CommercialRel) : r.flip.flip = r := by
  cases r <;> rfl

/-- The valley-free condition on a vertex list `p` with respect to edge relationship labels `rel`:
whenever an edge `a → b` is not a `provider` edge (i.e., it is `peer` or `customer`), any
immediately following edge `b → c` must be a `customer` edge. Equivalently, next-hop labels along
`p` follow the pattern `provider* → peer? → customer*`. -/
@[expose] def IsValleyFree (rel : V → V → CommercialRel) : List V → Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | a :: b :: c :: rest =>
    (rel a b ≠ .provider → rel b c = .customer) ∧ IsValleyFree rel (b :: c :: rest)

instance instDecidableIsValleyFree (rel : V → V → CommercialRel) :
    DecidablePred (IsValleyFree rel)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | [_, _] => isTrue trivial
  | a :: b :: c :: rest =>
    letI : Decidable (IsValleyFree rel (b :: c :: rest)) :=
      instDecidableIsValleyFree rel (b :: c :: rest)
    inferInstanceAs (Decidable ((rel a b ≠ .provider → rel b c = .customer) ∧
      IsValleyFree rel (b :: c :: rest)))

/-- Directed provider-to-customer edge: `u` is a provider of `v` (equivalently `v` is a customer
of `u`) in `G`. -/
@[expose] def IsProviderOf (G : SimpleGraph V) (rel : V → V → CommercialRel) (u v : V) : Prop :=
  G.Adj u v ∧ rel u v = .customer

/-- **No Customer–Provider Cycles (NCPC)**: the directed provider-to-customer relation has no
directed cycle. -/
@[expose] def NoCustomerProviderCycle (G : SimpleGraph V) (rel : V → V → CommercialRel) : Prop :=
  ∀ u, ¬ Relation.TransGen (IsProviderOf G rel) u u

/-- **Prefer-Customer** (Gao–Rexford Guideline A): every AS strictly prefers any permitted path
whose next hop is a customer over any permitted path whose next hop is a peer or provider.
In particular, any strict `customer ≻ peer ≻ provider` preference ranking satisfies this
condition. -/
@[expose] def PreferCustomer [Fintype V] [DecidableEq V] (S : SPP V)
    (rel : V → V → CommercialRel) : Prop :=
  ∀ u v₁ v₂ t₁ t₂,
    S.permitted u (u :: v₁ :: t₁) → S.permitted u (u :: v₂ :: t₂) →
    rel u v₁ = .customer → rel u v₂ ≠ .customer →
    S.rank u (some (u :: v₂ :: t₂)) < S.rank u (some (u :: v₁ :: t₁))

/-- The **Gao–Rexford commercial routing conditions** ([GaoRexford2001]) on an `SPP` instance:
consistent commercial edge labels, no customer–provider cycles, valley-free permitted paths, and
prefer-customer routing preferences. -/
structure GaoRexfordConditions [Fintype V] [DecidableEq V] (S : SPP V) where
  /-- Commercial relationship of the second AS as viewed from the first. -/
  rel : V → V → CommercialRel
  /-- Edge symmetry: `v`'s relationship to `u` reverses `u`'s relationship to `v`. -/
  rel_symm : ∀ u v, S.graph.Adj u v → rel v u = (rel u v).flip
  /-- Acyclicity of the provider–customer hierarchy (`NCPC`). -/
  noCustomerProviderCycle : NoCustomerProviderCycle S.graph rel
  /-- Every permitted path is valley-free. -/
  valleyFree : ∀ u p, S.permitted u p → IsValleyFree rel p
  /-- Customer routes are strictly preferred to peer and provider routes. -/
  preferCustomer : PreferCustomer S rel

/-! ### Valley-free propagation lemmas -/

/-- Forward customer propagation: if `q` is nonempty, `q ++ x :: y :: t` is a valley-free chain in
`G`, and its first edge is a `customer` edge, then `q.head` reaches `x` via `IsProviderOf` and
`rel x y = .customer`. -/
private theorem valleyFree_customer_propagate {G : SimpleGraph V} {rel : V → V → CommercialRel} :
    ∀ {q : List V} {u x y : V} {t : List V},
      q.head? = some u →
      (q ++ x :: y :: t).IsChain G.Adj →
      IsValleyFree rel (q ++ x :: y :: t) →
      (match q ++ x :: y :: t with | a :: b :: _ => rel a b = .customer | _ => False) →
      Relation.TransGen (IsProviderOf G rel) u x ∧ rel x y = .customer
  | [], _, _, _, _, hhead, _, _, _ => by simp at hhead
  | [a], u, x, y, t, hhead, hchain, hvf, hfirst => by
    obtain rfl : a = u := Option.some.inj hhead
    simp only [List.singleton_append] at hchain hvf hfirst
    exact ⟨.single ⟨(List.isChain_cons_cons.mp hchain).1, hfirst⟩, hvf.1 (by simp [hfirst])⟩
  | a :: b :: r, u, x, y, t, hhead, hchain, hvf, hfirst => by
    obtain rfl : a = u := Option.some.inj hhead
    simp only [List.cons_append] at hchain hvf hfirst
    cases hr : r ++ x :: y :: t with
    | nil => exact (List.append_ne_nil_of_right_ne_nil r (List.cons_ne_nil x (y :: t)) hr).elim
    | cons c rest =>
      rw [hr] at hvf
      have hbc : rel b c = .customer := hvf.1 (by simp [hfirst])
      obtain ⟨hreach, hxy⟩ := valleyFree_customer_propagate (q := b :: r) rfl
        (List.isChain_cons_cons.mp hchain).2
        (by simpa only [List.cons_append, hr] using hvf.2)
        (by simpa only [List.cons_append, hr] using hbc)
      exact ⟨.head ⟨(List.isChain_cons_cons.mp hchain).1, hfirst⟩ hreach, hxy⟩

/-- Backward provider propagation: if `q` is nonempty, `q ++ x :: y :: t` is a valley-free chain
in `G`, and `rel x y ≠ .customer`, then every edge of `q` into `x` is a `provider` edge; hence `x`
reaches `q.head` via `IsProviderOf`. -/
private theorem valleyFree_provider_backprop {G : SimpleGraph V} {rel : V → V → CommercialRel}
    (hsymm : ∀ a b, G.Adj a b → rel b a = (rel a b).flip) :
    ∀ {q : List V} {u x y : V} {t : List V},
      q.head? = some u →
      (q ++ x :: y :: t).IsChain G.Adj →
      IsValleyFree rel (q ++ x :: y :: t) →
      rel x y ≠ .customer →
      Relation.TransGen (IsProviderOf G rel) x u ∧
        (match q ++ x :: y :: t with | a :: b :: _ => rel a b = .provider | _ => False)
  | [], _, _, _, _, hhead, _, _, _ => by simp at hhead
  | [a], u, x, y, t, hhead, hchain, hvf, hxy => by
    obtain rfl : a = u := Option.some.inj hhead
    simp only [List.singleton_append] at hchain hvf ⊢
    have hadj : G.Adj a x := (List.isChain_cons_cons.mp hchain).1
    have hax : rel a x = .provider := by_contra fun hne => hxy (hvf.1 hne)
    have hxa : rel x a = .customer := by simp [hsymm a x hadj, hax, CommercialRel.flip]
    exact ⟨.single ⟨hadj.symm, hxa⟩, hax⟩
  | a :: b :: r, u, x, y, t, hhead, hchain, hvf, hxy => by
    obtain rfl : a = u := Option.some.inj hhead
    simp only [List.cons_append] at hchain hvf ⊢
    have hadj : G.Adj a b := (List.isChain_cons_cons.mp hchain).1
    cases hr : r ++ x :: y :: t with
    | nil => exact (List.append_ne_nil_of_right_ne_nil r (List.cons_ne_nil x (y :: t)) hr).elim
    | cons c rest =>
      rw [hr] at hvf
      obtain ⟨hreach, hbc⟩ := valleyFree_provider_backprop hsymm (q := b :: r) rfl
        (List.isChain_cons_cons.mp hchain).2
        (by simpa only [List.cons_append, hr] using hvf.2) hxy
      have hbc' : rel b c = .provider := by simpa only [List.cons_append, hr] using hbc
      have hab : rel a b = .provider := by_contra fun hne => by simpa [hbc'] using hvf.1 hne
      have hba : rel b a = .customer := by simp [hsymm a b hadj, hab, CommercialRel.flip]
      exact ⟨.tail hreach ⟨hadj.symm, hba⟩, hab⟩

private theorem transGen_cycle_forward {R : V → V → Prop} {k : ℕ} (hk : 0 < k) (f : Fin k → V)
    (hstep : ∀ i : Fin k, Relation.TransGen R (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩)) :
    Relation.TransGen R (f ⟨0, hk⟩) (f ⟨0, hk⟩) := by
  have hwalk : ∀ m, 1 ≤ m →
      Relation.TransGen R (f ⟨0, hk⟩) (f ⟨m % k, Nat.mod_lt _ hk⟩) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hstep ⟨0, hk⟩
    | succ m hm ihm =>
      have hs := hstep ⟨m % k, Nat.mod_lt _ hk⟩
      simp only [Nat.mod_add_mod] at hs
      exact ihm.trans hs
  simpa only [Nat.mod_self] using hwalk k hk

private theorem transGen_cycle_backward {R : V → V → Prop} {k : ℕ} (hk : 0 < k) (f : Fin k → V)
    (hstep : ∀ i : Fin k, Relation.TransGen R (f ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) (f i)) :
    Relation.TransGen R (f ⟨0, hk⟩) (f ⟨0, hk⟩) :=
  Relation.transGen_swap.mp
    (transGen_cycle_forward hk f fun i => Relation.transGen_swap.mpr (hstep i))

/-! ### Gao–Rexford main theorems -/

namespace GaoRexfordConditions

variable [Fintype V] [DecidableEq V] {S : SPP V}

/-- **Gao–Rexford theorem (absence of dispute wheels)** ([GaoRexford2001];
[FeigenbaumSchapiraShenker2007], Chapter 14): under commercial symmetry, no customer–provider
cycles, valley-free permitted paths, and prefer-customer routing preferences, no dispute wheel can
exist. -/
theorem isEmpty_disputeWheel (hGR : GaoRexfordConditions S) : IsEmpty (DisputeWheel S) := by
  refine ⟨fun W => ?_⟩
  -- For each spoke `i`, decompose `W.pivot i = W.node i :: v_i :: t_i`.
  have hpiv_decomp : ∀ i : Fin W.size,
      ∃ v t, W.pivot i = W.node i :: v :: t ∧ S.graph.Adj (W.node i) v := fun i =>
    S.exists_cons_cons_of_permitted (W.node_ne_dest i) (W.pivot_permitted i)
  choose nextHop pivTail hpiv_eq _ using hpiv_decomp
  have hrp_perm : ∀ i : Fin W.size, S.permitted (W.node i) (W.rim i ++ W.pivot (W.next i)) :=
    W.rim_pivot_permitted
  have hrp_sp : ∀ i : Fin W.size,
      IsSimplePath S.graph (W.node i) S.dest (W.rim i ++ W.pivot (W.next i)) := fun i =>
    S.permitted_isSimplePath (W.node i) _ (hrp_perm i)
  have hrp_vf : ∀ i : Fin W.size, IsValleyFree hGR.rel (W.rim i ++ W.pivot (W.next i)) :=
    fun i => hGR.valleyFree (W.node i) _ (hrp_perm i)
  have hrim_head : ∀ i : Fin W.size, (W.rim i).head? = some (W.node i) := fun i => by
    simpa only [List.head?_append_of_ne_nil _ (W.rim_nonempty i)] using (hrp_sp i).1
  have hchain : ∀ i : Fin W.size, (W.rim i ++
      W.node (W.next i) :: nextHop (W.next i) :: pivTail (W.next i)).IsChain S.graph.Adj :=
    fun i => by rw [← hpiv_eq (W.next i)]; exact (hrp_sp i).2.2.1
  have hvf : ∀ i : Fin W.size, IsValleyFree hGR.rel
      (W.rim i ++ W.node (W.next i) :: nextHop (W.next i) :: pivTail (W.next i)) :=
    fun i => by rw [← hpiv_eq (W.next i)]; exact hrp_vf i
  by_cases hex : ∃ i₀ : Fin W.size, hGR.rel (W.node i₀) (nextHop i₀) = .customer
  · -- Case 1: some spoke has a customer pivot path; forward propagation forces a customer–provider
    -- cycle around the entire wheel.
    have hprop : ∀ i : Fin W.size, hGR.rel (W.node i) (nextHop i) = .customer →
        Relation.TransGen (IsProviderOf S.graph hGR.rel) (W.node i) (W.node (W.next i)) ∧
          hGR.rel (W.node (W.next i)) (nextHop (W.next i)) = .customer := by
      intro i hcust_i
      obtain ⟨w, t', hrp_eq, _⟩ := S.exists_cons_cons_of_permitted (W.node_ne_dest i) (hrp_perm i)
      have hcust_rim : hGR.rel (W.node i) w = .customer := by
        by_contra hne
        have hlt := hGR.preferCustomer (W.node i) (nextHop i) w (pivTail i) t'
          (hpiv_eq i ▸ W.pivot_permitted i) (hrp_eq ▸ hrp_perm i) hcust_i hne
        have hpref : S.rank (W.node i) (some (W.pivot i)) <
            S.rank (W.node i) (some (W.rim i ++ W.pivot (W.next i))) := W.prefers i
        rw [hpiv_eq i, hrp_eq] at hpref
        omega
      exact valleyFree_customer_propagate (hrim_head i) (hchain i) (hvf i)
        (by simpa only [← hpiv_eq (W.next i), hrp_eq] using hcust_rim)
    obtain ⟨i₀, hi₀⟩ := hex
    -- The customer property spreads from `i₀` to spoke `(i₀ + m) % W.size` for every `m`, hence to
    -- every spoke.
    have hshift : ∀ m : ℕ,
        hGR.rel (W.node ⟨(i₀.val + m) % W.size, Nat.mod_lt _ W.size_pos⟩)
          (nextHop ⟨(i₀.val + m) % W.size, Nat.mod_lt _ W.size_pos⟩) = .customer := by
      intro m
      induction m with
      | zero => simpa only [Nat.add_zero, Nat.mod_eq_of_lt i₀.isLt, Fin.eta] using hi₀
      | succ m ihm =>
        have hidx : W.next ⟨(i₀.val + m) % W.size, Nat.mod_lt _ W.size_pos⟩ =
            ⟨(i₀.val + (m + 1)) % W.size, Nat.mod_lt _ W.size_pos⟩ :=
          Fin.ext (by simp only [DisputeWheel.next, Nat.mod_add_mod, Nat.add_assoc])
        simpa only [hidx] using (hprop _ ihm).2
    have hall_cust : ∀ i : Fin W.size, hGR.rel (W.node i) (nextHop i) = .customer := fun i => by
      have hadd : i₀.val + (i.val + W.size - i₀.val) = i.val + W.size := by omega
      have hidx : (⟨(i₀.val + (i.val + W.size - i₀.val)) % W.size, Nat.mod_lt _ W.size_pos⟩ :
          Fin W.size) = i := Fin.ext (by simp [hadd, Nat.mod_eq_of_lt i.isLt])
      simpa only [hidx] using hshift (i.val + W.size - i₀.val)
    have hcyc := transGen_cycle_forward W.size_pos W.node fun i => (hprop i (hall_cust i)).1
    exact hGR.noCustomerProviderCycle _ hcyc
  · -- Case 2: no spoke has a customer pivot path; backward propagation forces a reverse
    -- customer–provider cycle around the entire wheel.
    push Not at hex
    have hback : ∀ i : Fin W.size,
        Relation.TransGen (IsProviderOf S.graph hGR.rel) (W.node (W.next i)) (W.node i) := fun i =>
      (valleyFree_provider_backprop hGR.rel_symm (hrim_head i) (hchain i) (hvf i)
        (hex (W.next i))).1
    have hcyc := transGen_cycle_backward W.size_pos W.node hback
    exact hGR.noCustomerProviderCycle _ hcyc

/-- **Gao–Rexford stability** ([GaoRexford2001]): under the Gao–Rexford commercial routing
conditions, an `SPP` instance has a unique stable path assignment. -/
theorem existsUnique_isStable (hGR : GaoRexfordConditions S) : ∃! π, S.IsStable π :=
  S.existsUnique_isStable_of_isEmpty_disputeWheel hGR.isEmpty_disputeWheel

/-- **Gao–Rexford safety** ([GaoRexford2001]; [GriffinShepherdWilfong2002], proved here for the
asynchronous per-node atomic best-response activation model `SPP.run` of
[FeigenbaumSchapiraShenker2007], Chapter 14, rather than FIFO link-queue `SPVP`): under the
Gao–Rexford commercial routing conditions, asynchronous best-response BGP dynamics from
`initAssignment` converge under every fair activation schedule to the unique stable path
assignment. -/
theorem exists_converges (hGR : GaoRexfordConditions S) (sched : ℕ → V)
    (hfair : SPP.IsFair sched) :
    ∃ π, S.IsStable π ∧ ∃ T, ∀ t ≥ T, S.run sched S.initAssignment t = π :=
  S.exists_converges_of_isEmpty_disputeWheel hGR.isEmpty_disputeWheel sched hfair

end GaoRexfordConditions

end Cslib.GameTheory.InterdomainRouting
