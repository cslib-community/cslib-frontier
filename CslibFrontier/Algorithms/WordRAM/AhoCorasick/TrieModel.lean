/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic
public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Input

/-!
# Pure Integer-State Trie Model for Word-RAM Aho–Corasick

Pure Lean specification of the integer-indexed array trie (`PTrie`) built by inserting all keywords
`P` (`Algorithm 2` of `[AhoCorasick1975]`). Depends only on `AhoCorasick.Basic` and
`AhoCorasick.Input` (no `SymbolicExec`, `Allocation`, or `PreservesMask` imports).

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.PTrie`: integer-state trie record with `numStates`,
  `trie`, `depth`, `isTerm`, and ghost string map `strOf`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.PTrie.build`: insert a keyword list starting from root `0`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.TreeInv`: tree invariant linking state numbers to strings.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.treeInv_init`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.stepChar_spec`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.insertChars_spec`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.build_trie_spec`: correctness of `PTrie.build`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.trie_char_pos_iff`: transition positivity equivalence
  with `IsNode`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.depth_le_self`: state depth is bounded by state index.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.Algorithms.Lean.AhoCorasick

/-! ## Pure integer-state trie model -/

/-- Pure integer-state trie model built by `PTrie.build`. -/
structure PTrie where
  /-- Number of allocated trie states (`≥ 1`, with root `0`). -/
  numStates : ℕ
  /-- Ghost mapping assigning each state ID to the keyword prefix it represents. -/
  strOf : ℕ → List ℕ
  /-- Flat goto transition table (`0` denotes an absent child). -/
  trie : ℕ → ℕ → ℕ
  /-- Depth `|(strOf u)|` of each trie state `u`. -/
  depth : ℕ → ℕ
  /-- Nonzero indicator marking terminal states whose string belongs to `P`. -/
  isTerm : ℕ → ℕ

/-- Initial single-state trie containing only the root `0`. -/
@[expose] def PTrie.init : PTrie where
  numStates := 1
  strOf _ := []
  trie _ _ := 0
  depth _ := 0
  isTerm _ := 0

/-- Traverse or allocate the child of state `u` on symbol `a`, returning the updated trie and
child state ID. -/
@[expose] def PTrie.stepChar (T : PTrie) (u a : ℕ) : PTrie × ℕ :=
  if T.trie u a = 0 then
    let s := T.numStates
    ({ numStates := s + 1
       strOf := Function.update T.strOf s (T.strOf u ++ [a])
       trie := fun x c => if x = u ∧ c = a then s else T.trie x c
       depth := Function.update T.depth s (T.depth u + 1)
       isTerm := T.isTerm }, s)
  else
    (T, T.trie u a)

/-- Insert a character suffix into `T` starting from state `u`, returning the updated trie and
final state ID. -/
@[expose] def PTrie.insertChars : PTrie → ℕ → List ℕ → PTrie × ℕ
  | T, u, [] => (T, u)
  | T, u, a :: as =>
    let res := T.stepChar u a
    res.1.insertChars res.2 as

/-- Insert a single keyword `p` from root `0` and mark its nonempty terminal state. -/
@[expose] def PTrie.insertPat (T : PTrie) (p : List ℕ) : PTrie :=
  let res := T.insertChars 0 p
  if 0 < res.2 then { res.1 with isTerm := Function.update res.1.isTerm res.2 1 } else res.1

/-- Build the integer-state trie for keyword list `P` starting from `PTrie.init`. -/
@[expose] def PTrie.build (P : List (List ℕ)) : PTrie :=
  P.foldl PTrie.insertPat PTrie.init

/-- Structural tree invariant relating a `PTrie`'s tables to its ghost string map `strOf`. -/
structure TreeInv (σ : ℕ) (T : PTrie) : Prop where
  one_le : 1 ≤ T.numStates
  str_zero : T.strOf 0 = []
  depth_zero : T.depth 0 = 0
  term_zero : T.isTerm 0 = 0
  str_ne_nil : ∀ u, 0 < u → u < T.numStates → T.strOf u ≠ []
  depth_eq : ∀ u < T.numStates, T.depth u = (T.strOf u).length
  str_inj : ∀ u < T.numStates, ∀ v < T.numStates, T.strOf u = T.strOf v → u = v
  trie_lt : ∀ u < T.numStates, ∀ a < σ, T.trie u a < T.numStates
  trie_spec : ∀ u < T.numStates, ∀ a < σ,
    T.trie u a = 0 ∨ (0 < T.trie u a ∧ T.strOf (T.trie u a) = T.strOf u ++ [a])
  parent_exists : ∀ w, 0 < w → w < T.numStates →
    ∃ u < w, ∃ a < σ, T.trie u a = w ∧ T.strOf w = T.strOf u ++ [a]
  trie_oob : ∀ u, T.numStates ≤ u → ∀ a, T.trie u a = 0
  depth_oob : ∀ u, T.numStates ≤ u → T.depth u = 0
  term_oob : ∀ u, T.numStates ≤ u → T.isTerm u = 0

theorem treeInv_init (σ : ℕ) : TreeInv σ PTrie.init where
  one_le := Nat.le_refl 1
  str_zero := rfl
  depth_zero := rfl
  term_zero := rfl
  str_ne_nil := fun _ hpos hlt => by simp only [PTrie.init] at hlt; omega
  depth_eq := fun u hlt => (Nat.lt_one_iff.mp hlt).symm ▸ rfl
  str_inj := fun u hu v hv _ => by simp only [PTrie.init] at hu hv; omega
  trie_lt := fun _ _ _ _ => Nat.zero_lt_one
  trie_spec := fun _ _ _ _ => Or.inl rfl
  parent_exists := fun _ hpos hlt => by simp only [PTrie.init] at hlt; omega
  trie_oob := fun _ _ _ => rfl
  depth_oob := fun _ _ => rfl
  term_oob := fun _ _ => rfl

private theorem TreeInv.trie_eq_of_strOf {σ : ℕ} {T : PTrie} (hT : TreeInv σ T)
    {u v a : ℕ} (hu : u < T.numStates) (hv : v < T.numStates)
    (hstr : T.strOf v = T.strOf u ++ [a]) :
    0 < v ∧ T.trie u a = v := by
  have hv_pos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | hp
    · rw [hT.str_zero] at hstr
      exact absurd hstr.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a []))
    · exact hp
  obtain ⟨u', hu'v, a', _, htrie', hstr'⟩ := hT.parent_exists v hv_pos hv
  have hinj := List.append_inj' (hstr'.symm.trans hstr) rfl
  have ha_eq : a' = a := List.head_eq_of_cons_eq hinj.2
  have hu_eq : u' = u := hT.str_inj u' (by omega) u hu hinj.1
  subst ha_eq; subst hu_eq
  exact ⟨hv_pos, htrie'⟩

theorem stepChar_spec {σ : ℕ} {T : PTrie} (hT : TreeInv σ T) {u a : ℕ}
    (hu : u < T.numStates) (ha : a < σ) :
    let res := T.stepChar u a
    TreeInv σ res.1 ∧
      T.numStates ≤ res.1.numStates ∧
      res.1.numStates ≤ T.numStates + 1 ∧
      0 < res.2 ∧ res.2 < res.1.numStates ∧
      res.1.strOf res.2 = T.strOf u ++ [a] ∧
      (∀ v < T.numStates, res.1.strOf v = T.strOf v ∧ res.1.isTerm v = T.isTerm v) := by
  dsimp only [PTrie.stepChar]
  split_ifs with h0
  · dsimp only
    set s := T.numStates
    have hs_pos : 0 < s := hT.one_le
    have hfresh : ∀ v < s, T.strOf v ≠ T.strOf u ++ [a] := fun v hv heq => by
      have := hT.trie_eq_of_strOf hu hv heq
      omega
    refine ⟨?_, by omega, by omega, hs_pos, by omega, Function.update_self s _ T.strOf,
      fun v hv => ⟨Function.update_of_ne (by omega) _ _, rfl⟩⟩
    refine
      { one_le := by dsimp only; omega
        str_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT.str_zero
        depth_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT.depth_zero
        term_zero := hT.term_zero
        str_ne_nil := fun w hw0 hws => by
          dsimp only at hws ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hws) with hlt | rfl
          · rw [Function.update_of_ne (by omega)]; exact hT.str_ne_nil w hw0 hlt
          · rw [Function.update_self]
            exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a [])
        depth_eq := fun w hws => by
          dsimp only at hws ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hws) with hlt | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hT.depth_eq w hlt
          · rw [Function.update_self, Function.update_self, hT.depth_eq u hu,
              List.length_append, List.length_singleton]
        str_inj := fun x hx y hy hxy => by
          dsimp only at hx hy hxy
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hxl | rfl <;>
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy) with hyl | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hxy
            exact hT.str_inj x hxl y hyl hxy
          · rw [Function.update_of_ne (by omega), Function.update_self] at hxy
            exact absurd hxy (hfresh x hxl)
          · rw [Function.update_self, Function.update_of_ne (by omega)] at hxy
            exact absurd hxy.symm (hfresh y hyl)
          · rfl
        trie_lt := fun x hx c hc => by
          dsimp only at hx ⊢
          split_ifs with hxc
          · omega
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hxl | rfl
            · have := hT.trie_lt x hxl c hc; omega
            · rw [hT.trie_oob s (Nat.le_refl s) c]; omega
        trie_spec := fun x hx c hc => by
          dsimp only at hx ⊢
          split_ifs with hxc
          · obtain ⟨rfl, rfl⟩ := hxc
            refine Or.inr ⟨hs_pos, ?_⟩
            rw [Function.update_self, Function.update_of_ne (by omega)]
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hxl | rfl
            · have hlt_s := hT.trie_lt x hxl c hc
              refine (hT.trie_spec x hxl c hc).imp_right fun ⟨hpos, hstr⟩ => ⟨hpos, ?_⟩
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hstr]
            · exact Or.inl (hT.trie_oob s (Nat.le_refl s) c)
        parent_exists := fun w hw0 hws => by
          dsimp only at hws ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hws) with hwl | rfl
          · obtain ⟨u₀, hu₀w, a₀, ha₀, ht₀, hs₀⟩ := hT.parent_exists w hw0 hwl
            have hne_ua : ¬(u₀ = u ∧ a₀ = a) := by
              rintro ⟨rfl, rfl⟩; omega
            refine ⟨u₀, hu₀w, a₀, ha₀, ?_, ?_⟩
            · simp only [hne_ua, ↓reduceIte]; exact ht₀
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hs₀
          · refine ⟨u, hu, a, ha, by simp, ?_⟩
            rw [Function.update_self, Function.update_of_ne (by omega)]
        trie_oob := fun x hx c => by
          dsimp only at hx ⊢
          rw [ite_eq_right (by omega)]
          exact hT.trie_oob x (by omega) c
        depth_oob := fun x hx => by
          dsimp only at hx ⊢
          rw [Function.update_of_ne (by omega), hT.depth_oob x (by omega)]
        term_oob := fun x hx => hT.term_oob x (by dsimp only at hx; omega) }
  · rcases hT.trie_spec u hu a ha with hnil | ⟨hpos, hstr⟩
    · exact absurd hnil h0
    · exact ⟨hT, Nat.le_refl _, Nat.le_succ _, hpos, hT.trie_lt u hu a ha, hstr,
        fun _ _ => ⟨rfl, rfl⟩⟩

theorem insertChars_spec {σ : ℕ} :
    ∀ (xs : List ℕ) (T : PTrie) (u : ℕ),
      TreeInv σ T → u < T.numStates → (∀ a ∈ xs, a < σ) →
      let res := T.insertChars u xs
      TreeInv σ res.1 ∧
        T.numStates ≤ res.1.numStates ∧
        res.1.numStates ≤ T.numStates + xs.length ∧
        res.2 < res.1.numStates ∧
        res.1.strOf res.2 = T.strOf u ++ xs ∧
        (xs ≠ [] → 0 < res.2) ∧
        (∀ v < T.numStates, res.1.strOf v = T.strOf v ∧ res.1.isTerm v = T.isTerm v) ∧
        (∀ w, T.numStates ≤ w → w < res.1.numStates →
          res.1.isTerm w = 0 ∧ ∃ q, q ≠ [] ∧ q <+: xs ∧ res.1.strOf w = T.strOf u ++ q) ∧
        (∀ q, q <+: xs → ∃ v < res.1.numStates, res.1.strOf v = T.strOf u ++ q)
  | [], T, u, hT, hu, _ => by
    dsimp only [PTrie.insertChars]
    refine ⟨hT, Nat.le_refl _, by simp, hu, by simp, fun h => absurd rfl h,
      fun _ _ => ⟨rfl, rfl⟩, fun _ hge hlt => by omega, fun q hq => ?_⟩
    rw [List.prefix_nil.mp hq, List.append_nil]
    exact ⟨u, hu, rfl⟩
  | a :: as, T, u, hT, hu, hxs => by
    dsimp only [PTrie.insertChars]
    have ha : a < σ := hxs a List.mem_cons_self
    have has : ∀ b ∈ as, b < σ := fun b hb => hxs b (List.mem_cons_of_mem a hb)
    obtain ⟨hT₁, hle₁, hub₁, hs_pos, hs_lt, hs_str, hpres₁⟩ := stepChar_spec hT hu ha
    set T₁ := (T.stepChar u a).1
    set s := (T.stepChar u a).2
    obtain ⟨hT₂, hle₂, hub₂, hu₂_lt, hu₂_str, hu₂_pos, hpres₂, hnew₂, hpref₂⟩ :=
      insertChars_spec as T₁ s hT₁ hs_lt has
    set T₂ := (T₁.insertChars s as).1
    set u₂ := (T₁.insertChars s as).2
    refine ⟨hT₂, le_trans hle₁ hle₂, by simp only [List.length_cons]; omega, hu₂_lt, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [hu₂_str, hs_str, List.append_assoc, List.singleton_append]
    · intro _
      by_cases hnil : as = []
      · subst hnil
        simpa only [u₂, PTrie.insertChars] using hs_pos
      · exact hu₂_pos hnil
    · exact fun v hv => (hpres₂ v (lt_of_lt_of_le hv hle₁)).imp (·.trans (hpres₁ v hv).1)
        (·.trans (hpres₁ v hv).2)
    · intro w hge hlt
      rcases lt_or_ge w T₁.numStates with hw₁ | hw₁
      · have hw_eq : w = T.numStates := by omega
        have hs_eq : s = w := by
          dsimp only [T₁, s, PTrie.stepChar] at hle₁ hub₁ hs_lt hw₁ ⊢
          split_ifs at hle₁ hub₁ hs_lt hw₁ ⊢ with h0 <;>
            dsimp only at hle₁ hub₁ hs_lt hw₁ ⊢ <;> omega
        obtain ⟨hs2, ht2⟩ := hpres₂ w hw₁
        have ht1_0 : T₁.isTerm w = 0 := by
          dsimp only [T₁, PTrie.stepChar]; split_ifs <;> exact hT.term_oob w hge
        refine ⟨ht2.trans ht1_0, [a], List.cons_ne_nil a [], List.cons_prefix_cons.mpr
          ⟨rfl, List.nil_prefix⟩, ?_⟩
        rw [hs2, ← hs_eq, hs_str]
      · obtain ⟨ht_0, q', hq'_ne, hq'_pref, hq'_str⟩ := hnew₂ w hw₁ hlt
        refine ⟨ht_0, a :: q', List.cons_ne_nil a q',
          List.cons_prefix_cons.mpr ⟨rfl, hq'_pref⟩, ?_⟩
        rw [hq'_str, hs_str, List.append_assoc, List.singleton_append]
    · intro q hq
      rcases q with _ | ⟨b, q'⟩
      · refine ⟨u, lt_of_lt_of_le hu (le_trans hle₁ hle₂), ?_⟩
        rw [List.append_nil, (hpres₂ u (lt_of_lt_of_le hu hle₁)).1, (hpres₁ u hu).1]
      · obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
        obtain ⟨v, hv, hv_str⟩ := hpref₂ q' hq'
        refine ⟨v, hv, ?_⟩
        rw [hv_str, hs_str, List.append_assoc, List.singleton_append]

theorem build_trie_spec (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    TreeInv σ (PTrie.build P) ∧
      (PTrie.build P).numStates ≤ totalPatternLen P + 1 ∧
      (∀ u < (PTrie.build P).numStates, IsNode P ((PTrie.build P).strOf u)) ∧
      (∀ w, IsNode P w → ∃ u < (PTrie.build P).numStates, (PTrie.build P).strOf u = w) ∧
      (∀ u < (PTrie.build P).numStates,
        (PTrie.build P).isTerm u =
          if (PTrie.build P).strOf u ≠ [] ∧ (PTrie.build P).strOf u ∈ P then 1 else 0) := by
  suffices ∀ (ps Q : List (List ℕ)) (T : PTrie),
      (∀ p ∈ ps, ∀ a ∈ p, a < σ) →
      TreeInv σ T →
      T.numStates ≤ totalPatternLen Q + 1 →
      (∀ u < T.numStates, IsNode Q (T.strOf u)) →
      (∀ w, IsNode Q w → ∃ u < T.numStates, T.strOf u = w) →
      (∀ u < T.numStates, T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ Q then 1 else 0) →
      TreeInv σ (ps.foldl PTrie.insertPat T) ∧
        (ps.foldl PTrie.insertPat T).numStates ≤ totalPatternLen (Q ++ ps) + 1 ∧
        (∀ u < (ps.foldl PTrie.insertPat T).numStates,
          IsNode (Q ++ ps) ((ps.foldl PTrie.insertPat T).strOf u)) ∧
        (∀ w, IsNode (Q ++ ps) w →
          ∃ u < (ps.foldl PTrie.insertPat T).numStates,
            (ps.foldl PTrie.insertPat T).strOf u = w) ∧
        (∀ u < (ps.foldl PTrie.insertPat T).numStates,
          (ps.foldl PTrie.insertPat T).isTerm u =
            if (ps.foldl PTrie.insertPat T).strOf u ≠ [] ∧
              (ps.foldl PTrie.insertPat T).strOf u ∈ Q ++ ps then 1 else 0) by
    exact this P [] PTrie.init hvalid (treeInv_init σ) (Nat.le_refl 1)
        (fun u hu => (Nat.lt_one_iff.mp hu).symm ▸ isNode_nil [])
        (fun w hw => hw.elim (fun h => ⟨0, Nat.zero_lt_one, h.symm⟩)
          fun ⟨_, hp, _⟩ => (List.not_mem_nil hp).elim)
        (fun u hu => by simp [PTrie.init, Nat.lt_one_iff.mp hu])
  intro ps
  induction ps with
  | nil =>
    intro Q T _ hT hnum hnode hcomp hterm
    simpa only [List.foldl_nil, List.append_nil] using ⟨hT, hnum, hnode, hcomp, hterm⟩
  | cons p ps ih =>
    intro Q T hps hT hnum hnode hcomp hterm
    have hp_val : ∀ a ∈ p, a < σ := hps p List.mem_cons_self
    have hps_val : ∀ q ∈ ps, ∀ a ∈ q, a < σ := fun q hq => hps q (List.mem_cons_of_mem p hq)
    obtain ⟨hT₁, hle₁, hub₁, hu_lt, hu_str, hu_pos, hpres₁, hnew₁, hpref₁⟩ :=
      insertChars_spec p T 0 hT hT.one_le hp_val
    simp only [hT.str_zero, List.nil_append] at hu_str hnew₁ hpref₁
    set T₁ := (T.insertChars 0 p).1
    set u := (T.insertChars 0 p).2
    set T₂ := PTrie.insertPat T p
    have hT₂_str : T₂.strOf = T₁.strOf := by
      dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
    have hT₂_num : T₂.numStates = T₁.numStates := by
      dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
    have hT₂_inv : TreeInv σ T₂ := by
      dsimp only [T₂, PTrie.insertPat]
      split_ifs with hpos
      · refine { hT₁ with
          term_zero := by
            dsimp only; rw [Function.update_of_ne (by omega)]; exact hT₁.term_zero
          term_oob := fun x hx => by
            dsimp only [T₁, u] at hu_lt hx ⊢
            rw [Function.update_of_ne (by omega)]; exact hT₁.term_oob x hx }
      · exact hT₁
    have hnum₂ : T₂.numStates ≤ totalPatternLen (Q ++ [p]) + 1 := by
      rw [hT₂_num]
      have htot : totalPatternLen (Q ++ [p]) = totalPatternLen Q + p.length := by
        simp [totalPatternLen, List.map_append, List.sum_append]
      omega
    have hnode₂ : ∀ v < T₂.numStates, IsNode (Q ++ [p]) (T₂.strOf v) := by
      intro v hv
      rw [hT₂_num] at hv
      rw [hT₂_str]
      rcases lt_or_ge v T.numStates with hv₀ | hv₀
      · rw [(hpres₁ v hv₀).1]
        rcases hnode v hv₀ with hnil | ⟨r, hr, hvr⟩
        · exact Or.inl hnil
        · exact Or.inr ⟨r, List.mem_append_left _ hr, hvr⟩
      · obtain ⟨_, q, _, hqp, hqstr⟩ := hnew₁ v hv₀ hv
        rw [hqstr]
        exact Or.inr ⟨p, List.mem_append_right _ (by simp), hqp⟩
    have hcomp₂ : ∀ w, IsNode (Q ++ [p]) w → ∃ v < T₂.numStates, T₂.strOf v = w := by
      intro w hw
      rw [hT₂_num, hT₂_str]
      rcases hw with rfl | ⟨r, hr, hwr⟩
      · exact ⟨0, hT₁.one_le, hT₁.str_zero⟩
      · rcases List.mem_append.mp hr with hrQ | hrp
        · obtain ⟨v, hv, hvw⟩ := hcomp w (Or.inr ⟨r, hrQ, hwr⟩)
          exact ⟨v, lt_of_lt_of_le hv hle₁, (hpres₁ v hv).1.trans hvw⟩
        · rw [List.mem_singleton.mp hrp] at hwr
          exact hpref₁ w hwr
    have hterm₂ : ∀ v < T₂.numStates,
        T₂.isTerm v = if T₂.strOf v ≠ [] ∧ T₂.strOf v ∈ Q ++ [p] then 1 else 0 := by
      intro v hv
      rw [hT₂_num] at hv
      rw [hT₂_str]
      have hT₂_term : T₂.isTerm v =
          (if 0 < u then Function.update T₁.isTerm u 1 else T₁.isTerm) v := by
        dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
      rw [hT₂_term]
      by_cases hp_nil : p = []
      · subst hp_nil
        change T₁.isTerm v = _
        rw [(hpres₁ v hv).2, (hpres₁ v hv).1, hterm v hv]
        by_cases hne : T.strOf v = [] <;> simp [hne]
      · have hu_p : 0 < u := hu_pos hp_nil
        simp only [hu_p, ↓reduceIte]
        by_cases hvu : v = u
        · subst hvu
          rw [Function.update_self]
          simp [hu_str, hp_nil]
        · rw [Function.update_of_ne hvu]
          have hne_p : T₁.strOf v ≠ p := fun heq =>
            hvu (hT₁.str_inj v hv u hu_lt (heq.trans hu_str.symm))
          rcases lt_or_ge v T.numStates with hv₀ | hv₀
          · rw [(hpres₁ v hv₀).2, hterm v hv₀, ← (hpres₁ v hv₀).1]
            simp [List.mem_append, hne_p]
          · obtain ⟨ht0, _⟩ := hnew₁ v hv₀ hv
            have hnot_Q : T₁.strOf v ∉ Q := fun hmQ => by
              obtain ⟨w, hw, hws⟩ := hcomp _ (isNode_of_mem hmQ)
              have := hT₁.str_inj w (lt_of_lt_of_le hw hle₁) v hv ((hpres₁ w hw).1.trans hws)
              omega
            rw [ht0]
            simp [List.mem_append, hnot_Q, hne_p]
    have hRes := ih (Q ++ [p]) T₂ hps_val hT₂_inv hnum₂ hnode₂ hcomp₂ hterm₂
    rwa [List.append_assoc, List.singleton_append] at hRes

private theorem trie_char_iff (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    ∀ u < (PTrie.build P).numStates, ∀ a < σ,
      (IsNode P ((PTrie.build P).strOf u ++ [a]) →
        0 < (PTrie.build P).trie u a ∧
          (PTrie.build P).trie u a < (PTrie.build P).numStates ∧
          (PTrie.build P).strOf ((PTrie.build P).trie u a) = (PTrie.build P).strOf u ++ [a]) ∧
      (¬IsNode P ((PTrie.build P).strOf u ++ [a]) → (PTrie.build P).trie u a = 0) := by
  obtain ⟨hT, _, hnode, hcomp, _⟩ := build_trie_spec P σ hvalid
  intro u hu a ha
  refine ⟨fun his => ?_, fun hnot => ?_⟩
  · obtain ⟨w, hw, hws⟩ := hcomp _ his
    obtain ⟨hw_pos, htw⟩ := hT.trie_eq_of_strOf hu hw hws
    rw [htw]
    exact ⟨hw_pos, hw, hws⟩
  · exact (hT.trie_spec u hu a ha).resolve_right fun ⟨_, hstr⟩ =>
      hnot (hstr ▸ hnode _ (hT.trie_lt u hu a ha))

theorem trie_char_pos_iff (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    ∀ u < (PTrie.build P).numStates, ∀ a < σ,
      IsNode P ((PTrie.build P).strOf u ++ [a]) ↔ 0 < (PTrie.build P).trie u a := by
  intro u hu a ha
  have h := trie_char_iff P σ hvalid u hu a ha
  exact ⟨fun his => (h.1 his).1, fun hpos => of_not_not fun hnot => hpos.ne' (h.2 hnot)⟩

theorem depth_le_self {σ : ℕ} {T : PTrie} (hT : TreeInv σ T) :
    ∀ w < T.numStates, T.depth w ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases Nat.eq_zero_or_pos w with rfl | hpos
    · rw [hT.depth_zero]
    · obtain ⟨u, huw, a, _, _, hstr⟩ := hT.parent_exists w hpos hw
      have hdu := ih u huw (lt_trans huw hw)
      rw [hT.depth_eq w hw, hstr, List.length_append, List.length_singleton,
        ← hT.depth_eq u (lt_trans huw hw)]
      omega

end Cslib.Algorithms.WordRAM.AhoCorasick
