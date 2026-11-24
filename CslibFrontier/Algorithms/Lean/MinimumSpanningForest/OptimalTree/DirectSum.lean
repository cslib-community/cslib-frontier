/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
public import Mathlib.Data.Finset.Sum

/-!
# Comparison budgets of independent minimum spanning forest problems

Lemmas 5.4–5.5 of [PettieRamachandran2002] restrict to weight orders in which every edge of the
first component is lighter than every edge of the second. On such inputs, a cross comparison has
a fixed answer, while a local comparison restricts only one factor of the product promise.
The direct-sum argument below applies to arbitrary deterministic CSLib comparison programs.
-/

public section

namespace Cslib.Query.LEQuery

variable {E F X Y O P : Type}

/-- Comparisons on independent input blocks, with every left key below every right key. -/
@[expose] def separated (l : E → E → Bool) (r : F → F → Bool) : E ⊕ F → E ⊕ F → Bool
  | .inl a, .inl b => l a b
  | .inr a, .inr b => r a b
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false

/-- Existence of a comparison program that returns the prescribed answer within `d` queries
on each member of the promise `S`. -/
@[expose] def feasible (ask : X → E → E → Bool) (out : X → O) (S : Set X) (d : ℕ) : Prop :=
  ∃ p : FreeM (LEQuery E) O, ∀ x ∈ S,
    p.eval (oracleOf (ask x)) = out x ∧ p.countQueries (oracleOf (ask x)) ≤ d

private abbrev SplitBudget (L R : ℕ → Prop) (d : ℕ) : Prop :=
  ∃ a b, L a ∧ R b ∧ a + b ≤ d

private theorem swapBudget {L R : ℕ → Prop} {d : ℕ} :
    SplitBudget L R d → SplitBudget R L d := by
  rintro ⟨a, b, hl, hr, h⟩
  exact ⟨b, a, hr, hl, by omega⟩

private theorem extendBudget {L R : ℕ → Prop} {d : ℕ} :
    SplitBudget L R d → SplitBudget L R (d+1) := by
  rintro ⟨a, b, hl, hr, h⟩
  exact ⟨a, b, hl, hr, by omega⟩

private theorem splitLocal {ask : X → E → E → Bool} {out : X → O} {S : Set X}
    (nonempty : S.Nonempty) (a b : E) (R : ℕ → Prop) (d : ℕ)
    (split : ∀ bit : Bool, {x | x ∈ S ∧ ask x a b = bit}.Nonempty →
      SplitBudget (feasible ask out {x | x ∈ S ∧ ask x a b = bit}) R d) :
    SplitBudget (feasible ask out S) R (d+1) := by
  classical
  let T (bit : Bool) : Set X := {x | x ∈ S ∧ ask x a b = bit}
  have only (bit : Bool) (forced : ∀ x ∈ S, ask x a b = bit) :
      SplitBudget (feasible ask out S) R (d+1) := by
    have eq : T bit = S := Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, forced x h⟩⟩
    have h := split bit (by change (T bit).Nonempty; rwa [eq])
    change SplitBudget (feasible ask out (T bit)) R d at h
    rw [eq] at h
    exact extendBudget h
  by_cases ht : (T true).Nonempty
  · by_cases hf : (T false).Nonempty
    · obtain ⟨lt, rt, ⟨pt, hpt⟩, brt, bt⟩ := split true ht
      obtain ⟨lf, rf, ⟨pf, hpf⟩, brf, bf⟩ := split false hf
      have joined : feasible ask out S (max lt lf + 1) := by
        refine ⟨.liftBind (.le a b) (fun bit => if bit then pt else pf), ?_⟩
        intro x hx
        cases e : ask x a b with
        | true =>
          obtain ⟨v, c⟩ := hpt x ⟨hx, e⟩
          simp [e, v]; omega
        | false =>
          obtain ⟨v, c⟩ := hpf x ⟨hx, e⟩
          simp [e, v]; omega
      by_cases h : lt ≤ lf
      · exact ⟨_, rf, joined, brf, by omega⟩
      · exact ⟨_, rt, joined, brt, by omega⟩
    · apply only true
      intro x hx
      cases e : ask x a b with
      | true => rfl
      | false => exact False.elim (hf ⟨x, hx, e⟩)
  · apply only false
    intro x hx
    cases e : ask x a b with
    | false => rfl
    | true => exact False.elim (ht ⟨x, hx, e⟩)

/-- Extract two single-factor programs whose budgets add up to at most the budget of any
joint program on the product of two nonempty promises. The joint program can interleave
local comparisons and ask cross comparisons. -/
theorem separated_directSum {askL : X → E → E → Bool} {askR : Y → F → F → Bool}
    {outL : X → O} {outR : Y → P} {S : Set X} {T : Set Y} {d : ℕ}
    (p : FreeM (LEQuery (E ⊕ F)) (O × P)) (hs : S.Nonempty) (ht : T.Nonempty)
    (ok : ∀ x ∈ S, ∀ y ∈ T,
      p.eval (oracleOf (separated (askL x) (askR y))) = (outL x, outR y) ∧
      p.countQueries (oracleOf (separated (askL x) (askR y))) ≤ d) :
    ∃ a b, feasible askL outL S a ∧ feasible askR outR T b ∧ a+b ≤ d := by
  induction p generalizing S T d with
  | pure o =>
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    refine ⟨0, 0, ⟨.pure o.1, fun u hu => ?_⟩, ⟨.pure o.2, fun v hv => ?_⟩, by omega⟩
    · exact ⟨congrArg Prod.fst (ok u hu y hy).1, Nat.zero_le _⟩
    · exact ⟨congrArg Prod.snd (ok x hx v hv).1, Nat.zero_le _⟩
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      cases d with
      | zero =>
        obtain ⟨x, hx⟩ := hs
        obtain ⟨y, hy⟩ := ht
        have h := (ok x hx y hy).2
        simp at h
      | succ d =>
        have sub (bit : Bool) {S' : Set X} {T' : Set Y} (hS : S'.Nonempty) (hT : T'.Nonempty)
            (sS : S' ⊆ S) (sT : T' ⊆ T)
            (forced : ∀ x ∈ S', ∀ y ∈ T', separated (askL x) (askR y) a b = bit) :
            SplitBudget (feasible askL outL S') (feasible askR outR T') d := by
          apply ih bit hS hT
          intro x hx y hy
          have h := ok x (sS hx) y (sT hy)
          change (cont (separated (askL x) (askR y) a b)).eval _ = _ ∧
            1 + (cont (separated (askL x) (askR y) a b)).countQueries _ ≤ d + 1 at h
          rw [forced x hx y hy] at h
          exact ⟨h.1, Nat.le_of_succ_le_succ (by simpa only [Nat.add_comm 1] using h.2)⟩
        cases a with
        | inl a =>
          cases b with
          | inl b =>
            apply splitLocal hs a b _ d
            intro bit h
            exact sub bit h ht (fun _ z => z.1) (fun _ z => z) (fun _ z _ _ => z.2)
          | inr b => exact extendBudget (sub true hs ht (fun _ z => z) (fun _ z => z)
              (fun _ _ _ _ => rfl))
        | inr a =>
          cases b with
          | inl b => exact extendBudget (sub false hs ht (fun _ z => z) (fun _ z => z)
              (fun _ _ _ _ => rfl))
          | inr b =>
            apply swapBudget
            apply splitLocal ht a b _ d
            intro bit h
            exact swapBudget (sub bit hs h (fun _ z => z) (fun _ z => z.1)
              (fun _ _ _ z => z.2))

end Cslib.Query.LEQuery

namespace Cslib.Multigraph.OptimalTree

variable {m n k v t u : ℕ} {E V : Type}

open Cslib.Query

/-- Embed two rank permutations into one ordering with every left edge below every right edge. -/
@[expose] def separatedRank (l : Fin m → Fin m) (r : Fin k → Fin k) : Fin m ⊕ Fin k → ℕ
  | .inl e => l e
  | .inr e => m + r e

theorem separatedRank_injective {l : Fin m → Fin m} {r : Fin k → Fin k}
    (hl : Function.Injective l) (hr : Function.Injective r) :
    Function.Injective (separatedRank l r) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (hl (Fin.ext h))
    | inr b => simp [separatedRank] at h; have := (l a).isLt; omega
  | inr a =>
    cases b with
    | inl b => simp [separatedRank] at h; have := (l b).isLt; omega
    | inr b => exact congrArg Sum.inr (hr (Fin.ext (Nat.add_left_cancel h)))

private theorem separatedRank_oracle (l : Fin m → Fin m) (r : Fin k → Fin k) :
    @LEQuery.keyOracle _ _ _ _ (separatedRank l r) = @LEQuery.oracleOf _
      (LEQuery.separated (fun a b => decide (l a ≤ l b)) (fun a b => decide (r a ≤ r b))) := by
  funext i op
  cases op with
  | le a b =>
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr b =>
        apply decide_eq_true
        change (l a : ℕ) ≤ m + r b
        have := (l a).isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        apply decide_eq_false
        change ¬m + (r a : ℕ) ≤ l b
        have := (l b).isLt
        omega
      | inr b => simp [separatedRank, LEQuery.separated]

/-- Every joint program computing two prescribed minimum spanning forests requires at least the
sum of their independently synthesized optimal budgets. It suffices to require correctness and a
comparison budget on the separated permutations of the two edge sets. -/
theorem add_optimalMSFComparisons_le (L : Fin m → Sym2 (Fin n)) (R : Fin k → Sym2 (Fin v))
    (p : FreeM (LEQuery (Fin m ⊕ Fin k)) (Finset (Fin m) × Finset (Fin k))) (d : ℕ)
    (ok : ∀ (l : Fin m → Fin m) (r : Fin k → Fin k), Function.Injective l → Function.Injective r →
      p.eval (LEQuery.keyOracle (separatedRank l r)) = (msf L l Finset.univ, msf R r Finset.univ) ∧
      p.countQueries (LEQuery.keyOracle (separatedRank l r)) ≤ d) :
    optimalMSFComparisons L + optimalMSFComparisons R ≤ d := by
  obtain ⟨a, b, ⟨pl, hl⟩, ⟨pr, hr⟩, bound⟩ := LEQuery.separated_directSum
    (askL := fun (l : Fin m → Fin m) a b => decide (l a ≤ l b))
    (askR := fun (r : Fin k → Fin k) a b => decide (r a ≤ r b))
    (outL := fun l => msf L l Finset.univ) (outR := fun r => msf R r Finset.univ)
    (S := {l | Function.Injective l}) (T := {r | Function.Injective r})
    (d := d) p ⟨id, Function.injective_id⟩ ⟨id, Function.injective_id⟩
    (fun l hl r hr => by simpa only [separatedRank_oracle] using ok l r hl hr)
  exact (Nat.add_le_add (optimalMSFComparisons_le L pl a hl)
    (optimalMSFComparisons_le R pr b hr)).trans bound

/-- A joint program attaining the sum of the two comparison budgets. Its first phase queries
only left labels and its second phase queries only right labels. -/
@[expose] def pairProgram (L : Fin m → Sym2 (Fin n)) (R : Fin k → Sym2 (Fin v)) :
    FreeM (LEQuery (Fin m ⊕ Fin k)) (Finset (Fin m) × Finset (Fin k)) := do
  let l ← LEQuery.relabel Sum.inl (optimalMSFProgram L)
  let r ← LEQuery.relabel Sum.inr (optimalMSFProgram R)
  return (l, r)

/-- The sequential program works for arbitrary interleavings of the two sets of weights. -/
theorem pairProgram_spec {W : Type*} [LinearOrder W] (L : Fin m → Sym2 (Fin n))
    (R : Fin k → Sym2 (Fin v)) (w : Fin m ⊕ Fin k → W)
    (hl : Function.Injective (w ∘ Sum.inl)) (hr : Function.Injective (w ∘ Sum.inr)) :
    (pairProgram L R).eval (LEQuery.keyOracle w) =
        (msf L (w ∘ Sum.inl) Finset.univ, msf R (w ∘ Sum.inr) Finset.univ) ∧
      (pairProgram L R).countQueries (LEQuery.keyOracle w) ≤
        optimalMSFComparisons L + optimalMSFComparisons R := by
  obtain ⟨lv, lc⟩ := LEQuery.relabel_spec Sum.inl (optimalMSFProgram L) w
  obtain ⟨rv, rc⟩ := LEQuery.relabel_spec Sum.inr (optimalMSFProgram R) w
  obtain ⟨vl, cl⟩ := optimalMSFProgram_spec L _ hl
  obtain ⟨vr, cr⟩ := optimalMSFProgram_spec R _ hr
  simpa [pairProgram, lv, lc, rv, rc, vl, vr] using Nat.add_le_add cl cr

private theorem msf_congr_lt {W W' : Type*} [LinearOrder W] [LinearOrder W']
    (ends : E → Sym2 V) (w : E → W) (w' : E → W') (S : Finset E)
    (lt : ∀ a b, w a < w b ↔ w' a < w' b) : msf ends w S = msf ends w' S := by
  classical
  ext e
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) := by
    induction ends e using Sym2.ind with | _ a b => exact ⟨a, b, rfl⟩
  rw [mem_msf_iff w hab, mem_msf_iff w' hab]
  simp only [lt]

/-- The two-block case of Property 5.3. The bijection identifies the labeled component edges
with the edges of the union. Vertices of the components may overlap. -/
@[expose] def ForestsSplit (L : Fin m → Sym2 (Fin n)) (R : Fin k → Sym2 (Fin v))
    (G : Fin t → Sym2 (Fin u)) (e : (Fin m ⊕ Fin k) ≃ Fin t) : Prop :=
  ∀ {W : Type} [LinearOrder W] (w : Fin m ⊕ Fin k → W), Function.Injective w →
    (msf G (w ∘ e.symm) Finset.univ).map e.symm.toEmbedding =
      (msf L (w ∘ Sum.inl) Finset.univ).disjSum (msf R (w ∘ Sum.inr) Finset.univ)

/-- The two-block case of Lemma 5.5 of [PettieRamachandran2002]. Whenever the labeled union's
forest splits for every order of the weights, its fixed-topology optimum is exactly the sum of
the two component optima. The lower bound applies to all comparison programs. -/
theorem optimalMSFComparisons_eq_add_of_forestsSplit
    (L : Fin m → Sym2 (Fin n)) (R : Fin k → Sym2 (Fin v))
    (G : Fin t → Sym2 (Fin u)) (e : (Fin m ⊕ Fin k) ≃ Fin t) (hs : ForestsSplit L R G e) :
    optimalMSFComparisons G = optimalMSFComparisons L + optimalMSFComparisons R := by
  classical
  apply le_antisymm
  · let join (o : Finset (Fin m) × Finset (Fin k)) := (o.1.disjSum o.2).map e.toEmbedding
    apply optimalMSFComparisons_le G (join <$> LEQuery.relabel e (pairProgram L R)) _
    intro w hw
    have inj := hw.comp e.injective
    obtain ⟨v, c⟩ := LEQuery.relabel_spec e (pairProgram L R) w
    obtain ⟨val, cost⟩ := pairProgram_spec L R (w ∘ e)
      (inj.comp Sum.inl_injective) (inj.comp Sum.inr_injective)
    have split := hs (w ∘ e) inj
    have eq : (w ∘ e) ∘ e.symm = w := funext fun x => by simp
    rw [eq] at split
    simp only [FreeM.eval_map, FreeM.countQueries_map, v, c, val]
    refine ⟨?_, cost⟩
    dsimp only [join]
    rw [← split]
    ext i
    simp
  · let unpack (s : Finset (Fin t)) := ((s.map e.symm.toEmbedding).toLeft,
        (s.map e.symm.toEmbedding).toRight)
    apply add_optimalMSFComparisons_le L R
      (unpack <$> LEQuery.relabel e.symm (optimalMSFProgram G)) _
    intro l r hl hr
    let w := separatedRank l r
    have inj : Function.Injective w := separatedRank_injective hl hr
    obtain ⟨v, c⟩ := LEQuery.relabel_spec e.symm (optimalMSFProgram G) w
    obtain ⟨val, cost⟩ := optimalMSFProgram_spec G (w ∘ e.symm) (inj.comp e.symm.injective)
    have left : msf L (w ∘ Sum.inl) Finset.univ = msf L l Finset.univ :=
      msf_congr_lt _ _ _ _ fun _ _ => Iff.rfl
    have right : msf R (w ∘ Sum.inr) Finset.univ = msf R r Finset.univ := by
      apply msf_congr_lt
      intro a b
      change m + (r a : ℕ) < m + (r b : ℕ) ↔ (r a : ℕ) < r b
      omega
    change _ = _ ∧ _ ≤ _
    simp only [FreeM.eval_map, FreeM.countQueries_map]
    change unpack ((LEQuery.relabel e.symm _).eval (LEQuery.keyOracle w)) = _ ∧
      (LEQuery.relabel e.symm _).countQueries (LEQuery.keyOracle w) ≤ _
    rw [v, c, val]
    exact ⟨by simp [unpack, hs w inj, left, right], cost⟩

end Cslib.Multigraph.OptimalTree
