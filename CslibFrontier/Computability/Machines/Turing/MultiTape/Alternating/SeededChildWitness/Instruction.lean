/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Joined
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCountNative
public import CslibFrontier.Computability.PolyTime.SeededChildWitness.CountingRequest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# The executable terminal of a descendant endpoint word

A completed choice word produces either a Boolean verdict or one parent endpoint request.
Each local arithmetic operation uses the split's four shared seed coefficients. Both the
route and the proposed parent coordinates have short native encodings.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts.Joined

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery SeededChildWitness Dispatch
open MultiTapeTM ComputableInPolyTime

/-- Public header for a nonempty descendant request. -/
structure Header where
  graph : Public
  seed : SeededPredecessor.Context
  coordinate : ℕ
  group : ℕ
  answer : ℕ × ℕ

/-- The coordinate stays unary and all four seed coefficients and vertex keys stay binary. -/
enc_structure encHeader : Header where graph : encPublic, seed : SeededPredecessor.encContext,
  coordinate : encUnary, group : encNat, answer : (encPair encNat encNat)

/-- A closed verdict or one parent edge and its two claimed endpoints. -/
abbrev Instruction := Bool ⊕ (ℕ × (ℕ × ℕ))

/-- Tagged binary output for the finite endpoint controller. -/
abbrev encInstruction := encSum encBool (encPair encNat (encPair encNat encNat))

/-- Arguments to the singleton branch. -/
structure Singleton where
  header : Header
  index : ℕ
  value : ℕ
  ends : ℕ × ℕ
  challenge : Bool

/-- The candidate keys and subtotal are represented in binary. -/
enc_structure encSingleton : Singleton where header : encHeader, index : encNat, value : encNat,
  ends : (encPair encNat encNat), challenge : encBool

private def select (s : Singleton) (needs test : Bool) : Instruction :=
  if s.challenge then
    if needs then .inr (s.index, s.ends) else .inl true
  else .inl (decide (s.value = (if test then 1 else 0)))

private def digit (h : Header) (v : ℕ) :=
  if v < h.seed.universeSize then RootPortFinish.symbol h.seed h.coordinate v else 0

private def hash (h : Header) (v : ℕ) :=
  if v < h.seed.universeSize then SeededPacketPlacement.code h.seed v else 0

/-- Compute a signed vertex, port or packing-class singleton from the same split seed. -/
def singleton (s : Singleton) (c : Count) : Instruction :=
  let h := s.header
  match c with
  | .inl n => select s false (decide (s.index < min n h.graph.vertices) &&
      decide (digit h s.index = h.group))
  | .inr (.inl (col, n)) =>
    let needs := decide (s.index < n) && decide (s.index < h.graph.edges)
    select s needs (needs && decide (digit h (if col then s.ends.2 else s.ends.1) = h.group))
  | .inr (.inr (e, ref)) =>
    let needs := decide (s.index < h.graph.edges) && decide (s.index < e)
    select s needs (needs && (decide (hash h s.ends.1 = hash h ref.1) &&
      decide (hash h s.ends.2 = hash h ref.2)))

/-- A recursive singleton request keeps the proposed endpoints and names an actual parent
edge. This bound holds for every choice word, including choices on rejecting branches. -/
theorem singleton_inr_bounds {s : Singleton} {c : Count} {query : ℕ × (ℕ × ℕ)}
    (h : singleton s c = .inr query) :
    query = (s.index, s.ends) ∧ s.index < s.header.graph.edges := by
  rcases c with n | (⟨col, n⟩ | ⟨edge, ends⟩) <;>
    simp only [singleton, select] at h
  all_goals split_ifs at h; simp_all

private theorem select_polyTime {α : Type} {enc : α ↪ List Bool} {s : α → Singleton}
    {n v : α → Bool} (hs : ComputableInPolyTime s enc encSingleton)
    (hn : ComputableInPolyTime n enc encBool) (hv : ComputableInPolyTime v enc encBool) :
    ComputableInPolyTime (fun x => select (s x) (n x) (v x)) enc encInstruction := by
  have he := encSingleton_ends_polyTime hs
  let yes := sumInl encBool (encPair encNat (encPair encNat encNat))
  let rec' := sumInr encBool (encPair encNat (encPair encNat encNat))
  exact ite (encSingleton_challenge_polyTime hs)
    (ite hn (rec'.comp ((encSingleton_index_polyTime hs).prod he)) (yes.comp (const true)))
    (yes.comp (decide_eq' (encSingleton_value_polyTime hs) (ite hv (const 1) (const 0))))

private theorem digit_polyTime {α : Type} {enc : α ↪ List Bool} {h : α → Header} {v : α → ℕ}
    (hh : ComputableInPolyTime h enc encHeader) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => digit (h x) (v x)) enc encNat := by
  have hs := encHeader_seed_polyTime hh
  exact ite_decide (binary_lt' hv (SeededPredecessor.encContext_universeSize_polyTime hs))
    (RootPortFinish.computableInPolyTime_symbol hs (encHeader_coordinate_polyTime hh) hv) (const 0)

private theorem hash_polyTime {α : Type} {enc : α ↪ List Bool} {h : α → Header} {v : α → ℕ}
    (hh : ComputableInPolyTime h enc encHeader) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => hash (h x) (v x)) enc encNat := by
  have hs := encHeader_seed_polyTime hh
  exact ite_decide (binary_lt' hv (SeededPredecessor.encContext_universeSize_polyTime hs))
    (SeededPacketPlacement.computableInPolyTime_code hs hv) (const 0)

/-- All three count leaves produce their actual controller instruction in polynomial time. -/
theorem computableInPolyTime_singleton : ComputableInPolyTime (Function.uncurry singleton)
    (encPair encSingleton encCount) encInstruction := by
  let vert := fun (s : Singleton) (n : ℕ) => singleton s (.inl n)
  let port := fun (s : Singleton) (p : Bool × ℕ) => singleton s (.inr (.inl p))
  let pack := fun (s : Singleton) (ref : ℕ × (ℕ × ℕ)) => singleton s (.inr (.inr ref))
  have hv : ComputableInPolyTime (Function.uncurry vert) (encPair encSingleton encNat)
      encInstruction := by
    have hs := fst encSingleton encNat
    have hh := encSingleton_header_polyTime hs
    have hi := encSingleton_index_polyTime hs
    have hl := decide_eq' (digit_polyTime hh hi) (encHeader_group_polyTime hh)
    have n := snd encSingleton encNat
    have hu := encPublic_vertices_polyTime (encHeader_graph_polyTime hh)
    have hm := ite_decide (binary_lt' n hu) n hu
    have hmin : ComputableInPolyTime (fun x : Singleton × ℕ => min x.2 x.1.header.graph.vertices)
        (encPair encSingleton encNat) encNat := hm.of_enc_eq fun x => by
      by_cases h : x.2 < x.1.header.graph.vertices
      · rw [ite_eq_left h, Nat.min_eq_left h.le]
      · rw [ite_eq_right h, Nat.min_eq_right (Nat.le_of_not_gt h)]
    exact select_polyTime hs (const false) (bool_and' (binary_lt' hi hmin) hl)
  have hp : ComputableInPolyTime (Function.uncurry port)
      (encPair encSingleton (encPair encBool encNat)) encInstruction := by
    let e := encPair encBool encNat
    have hs := fst encSingleton e
    have hh := encSingleton_header_polyTime hs
    have hi := encSingleton_index_polyTime hs
    have he := encSingleton_ends_polyTime hs
    have ht := snd encSingleton e
    have hn := bool_and' (binary_lt' hi ht.snd')
      (binary_lt' hi (encPublic_edges_polyTime (encHeader_graph_polyTime hh)))
    have hsel := ite ht.fst' he.snd' he.fst'
    exact select_polyTime hs hn (bool_and' hn
      (decide_eq' (digit_polyTime hh hsel) (encHeader_group_polyTime hh)))
  have hk : ComputableInPolyTime (Function.uncurry pack)
      (encPair encSingleton (encPair encNat (encPair encNat encNat))) encInstruction := by
    let e := encPair encNat (encPair encNat encNat)
    have hs := fst encSingleton e
    have hh := encSingleton_header_polyTime hs
    have hi := encSingleton_index_polyTime hs
    have he := encSingleton_ends_polyTime hs
    have ht := snd encSingleton e
    have hn := bool_and' (binary_lt' hi (encPublic_edges_polyTime (encHeader_graph_polyTime hh)))
      (binary_lt' hi ht.fst')
    have h₁ := decide_eq' (hash_polyTime hh he.fst') (hash_polyTime hh ht.snd'.fst')
    have h₂ := decide_eq' (hash_polyTime hh he.snd') (hash_polyTime hh ht.snd'.snd')
    exact select_polyTime hs hn (bool_and' hn (bool_and' h₁ h₂))
  have hr := ComputableInPolyTime.sumElimSnd hp hk
  exact (ComputableInPolyTime.sumElimSnd
    (right := fun s c => c.elim (port s) (pack s))
    hv hr).of_enc_eq fun p => by
    rcases p with ⟨s, n | (p | e)⟩ <;> rfl

/-- Operational interpretation of an emitted instruction. -/
@[expose] def holds (q : EndpointQuery) : Instruction → Prop
  | .inl b => b = true
  | .inr (j, p) => q.accepts j p

/-- An actual choice of seed, with all its graph parameters and the requested child ends. -/
@[expose] def headerOf {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a)
    (g edges child : ℕ) (answer : ℕ × ℕ) : Header :=
  ⟨⟨edges, U, child⟩, ⟨U, a, seed 0, seed 1, seed 2, seed 3, 0, 0⟩, i.val, g, answer⟩

private theorem digit_header {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a)
    (g : ℕ) (q : EndpointQuery) (j : ℕ) (ans : ℕ × ℕ) (v : ℕ) :
    digit (headerOf seed i g q.size j ans) v = ((Labels.ofSeed U a seed i g).split q).label v := by
  by_cases hv : v < U
  · simpa only [digit, headerOf, hv, ↓reduceIte] using symbol_of_seed seed i g 0 ⟨v, hv⟩ q
  · simp only [digit, headerOf, hv, ↓reduceIte, Labels.split, Labels.symbol, Labels.ofSeed]

private theorem hash_header {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a)
    (g edges j : ℕ) (ans : ℕ × ℕ) (v : ℕ) :
    hash (headerOf seed i g edges j ans) v = ((Labels.ofSeed U a seed i g).code v).val := by
  by_cases hv : v < U
  · simpa only [hash, headerOf, hv, ↓reduceIte, Labels.ofSeed, dite_true] using
      SeededPacketPlacement.code_eq U a seed ⟨v, hv⟩ 0 0
  · simp only [hash, headerOf, hv, ↓reduceIte, Labels.ofSeed]
    rfl

private theorem holds_select (q : EndpointQuery) (s : Singleton) (needs test : Bool) :
    holds q (select s needs test) ↔
      if s.challenge then (needs = true → q.accepts s.index s.ends) else s.value = test.toNat := by
  cases hb : s.challenge <;> cases needs <;> cases test <;> simp [select, holds, hb]

/-- The emitted instruction exactly implements the signed singleton task, even when the chosen
keys do not belong to the vertex universe or the selected candidate is padded. -/
theorem singleton_spec {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a) (g : ℕ)
    (q : EndpointQuery) (j : ℕ) (ans : ℕ × ℕ) (r : Count) (k v : ℕ) (p : ℕ × ℕ) (b : Bool) :
    let h := headerOf seed i g q.size j ans
    let l := Labels.ofSeed U a seed i g
    holds q (singleton ⟨h,k,v,p,b⟩ r) ↔ leaf q l (request r) (some (k,v)) p b := by
  intro h l
  have hd x : digit h x = (l.split q).label x := digit_header seed i g q j ans x
  have hh x : hash h x = (l.code x).val := hash_header seed i g q.size j ans x
  have hg : h.group = l.group := rfl
  have he : h.graph.edges = q.size := rfl
  have hu : h.graph.vertices = l.vertices := rfl
  rcases r with bound | (⟨col, bound⟩ | ⟨e,ref⟩) <;> cases b <;>
    simp [singleton, holds_select, leaf, request, Request.onPair, Request.needsParent,
      Request.size, hd, hh, he, hu, hg, Fin.ext_iff, Bool.and_assoc]
  all_goals by_cases h₁ : k < bound <;> by_cases h₂ : k < q.size <;> simp [h₁, h₂]

end Turing.MultiTapeATM.SeededChildCounts.Joined
