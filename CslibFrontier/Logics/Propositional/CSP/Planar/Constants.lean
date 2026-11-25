/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Construction
import CslibFrontier.Logics.Propositional.CSP.Planar.NonSelfDual
import Mathlib.Tactic.FinCases

/-!
# Constants and disequality from ordered constructions

This is the semantic descent of [DvorakKupec2015], Lemma 3, printed pp. 437–438.
Equality restriction is always followed immediately by deletion of the first of the adjacent
ports, so minimum arity suffices. Unary constant operations are kept distinct from unary pin
relations. Different language symbols may witness the failures of the different polymorphisms.

The conclusions give finite `RelationMinor.Construction` trees, with all enabling relations
constructed from original symbols. Geometric interpretation and complexity are not claimed.

## Main results

* `Cslib.Logic.PL.CSP.RelationMinor.disequality_of_not_hasSchaeferPolymorphism`: disequality.
* `Cslib.Logic.PL.CSP.RelationMinor.constants_of_not_hasSchaeferPolymorphism`: both pins as well.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool} {m n : ℕ}

private theorem minimal_available (P : ∀ n, Set (Fin n → Bool) → Prop)
    {R : Set (Fin m → Bool)} (hR : Available arity sem R) (hp : P m R) :
    ∃ (n : ℕ) (S : Set (Fin n → Bool)), Available arity sem S ∧ P n S ∧
      ∀ (k : ℕ) (T : Set (Fin k → Bool)), Available arity sem T → k < n → ¬P k T := by
  classical
  have hex : ∃ n, ∃ S : Set (Fin n → Bool), Available arity sem S ∧ P n S := ⟨m, R, hR, hp⟩
  obtain ⟨S, hc, hs⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, S, hc, hs, fun k T hT hlt hp => Nat.find_min hex hlt ⟨T, hT, hp⟩⟩

private def spike (b : Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !b else b

/-- A unary Boolean tuple is a given one or its complement. -/
private theorem eq_or_eq_not (x y : Fin 1 → Bool) : y = x ∨ y = fun i => !(x i) := by
  revert x y
  decide

private theorem mem_adjacent {R : Set (Fin (n + 2) → Bool)} {a : Fin (n + 2) → Bool}
    (ha : a ∈ R) (d : Bool) (he : a 0 = (a 1 ^^ d)) : Fin.tail a ∈ adjacent R d := by
  change Fin.cons (a 1 ^^ d) (Fin.tail a) ∈ R
  rwa [← he, Fin.cons_self_tail]

private theorem constant_not_mem_adjacent {R : Set (Fin (n + 2) → Bool)} (b : Bool)
    (hz : (fun _ => b) ∉ R) : (fun _ => b) ∉ adjacent R false := by
  intro h
  change Fin.cons (b ^^ false) (Fin.tail fun _ => b) ∈ R at h
  rw [Bool.xor_false, Fin.cons_self_tail (fun _ : Fin (n + 2) => b)] at h
  exact hz h

private theorem spike_mem {R : Set (Fin (n + 1) → Bool)} (b : Bool)
    (hz : (fun _ => b) ∉ R) (j : Fin (n + 1))
    (hp : (fun _ => b) ∈ project R j) : spike b j ∈ R := by
  obtain ⟨v, hv⟩ := hp
  have hvb : v ≠ b := by
    rintro rfl
    exact hz ((Fin.insertNth_eq_iff.2 ⟨rfl, rfl⟩ : j.insertNth v (fun _ => v) = fun _ => v) ▸ hv)
  have heq : (j.insertNth v (fun _ : Fin n => b) : Fin (n + 1) → Bool) = spike b j :=
    Fin.insertNth_eq_iff.2 ⟨by cases v <;> cases b <;> simp_all [spike],
      funext fun k => by simp [spike, Fin.removeNth, Fin.succAbove_ne]⟩
  exact heq ▸ hv

/-- Failure of a unary constant yields disequality or the opposite unary pin, by projections
and immediate adjacent equality-deletions alone. This includes arbitrary and nullary arities. -/
theorem disequality_or_pin_of_missing_constant {R : Set (Fin m → Bool)}
    (hR : Available arity sem R) (b : Bool) (hne : R.Nonempty)
    (hz : (fun _ => b) ∉ R) :
    Available arity sem disequality ∨ Available arity sem (pin (!b)) := by
  obtain ⟨n, S, ⟨c⟩, ⟨⟨a, ha⟩, hz⟩, hmin⟩ :=
    minimal_available (fun n S => S.Nonempty ∧ (fun _ : Fin n => b) ∉ S) hR ⟨hne, hz⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact hz ((Subsingleton.elim a (fun _ => b)) ▸ ha)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hu (j : Fin (n + 1)) : spike b j ∈ S := spike_mem b hz j <| by
    by_contra hh
    exact hmin n _ ⟨.project c j⟩ (by omega) ⟨⟨j.removeNth a, remove_mem_project ha j⟩, hh⟩
  have hn2 : n + 1 ≤ 2 := by
    by_contra hh
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact hmin (k + 2) _ ⟨.equalDrop c⟩ (by omega)
      ⟨⟨_, mem_adjacent (hu ⟨2, by omega⟩) false (by simp [spike])⟩, constant_not_mem_adjacent b hz⟩
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · have ha' : a = fun _ => !b := (eq_or_eq_not (fun _ => b) a).resolve_left fun h => hz (h ▸ ha)
    have heq : S = pin (!b) := by
      ext x
      rcases eq_or_eq_not (fun _ => b) x with rfl | rfl
      · simp [pin, hz]
      · simp [pin, show (fun _ : Fin 1 => !b) ∈ S from ha' ▸ ha]
    exact .inr ⟨heq ▸ c⟩
  · have hlast : (fun _ : Fin 2 => !b) ∉ S := fun h => hmin 1 _ ⟨.equalDrop c⟩ (by omega)
      ⟨⟨_, mem_adjacent h false (by simp)⟩, constant_not_mem_adjacent b hz⟩
    have rows (x : Fin 2 → Bool) : x = (fun _ => b) ∨ x = spike b 0 ∨
        x = spike b 1 ∨ x = fun _ => !b := by cases b <;> revert x <;> decide
    have heq : S = disequality := by
      ext x
      rcases rows x with rfl | rfl | rfl | rfl <;> simp [disequality, hz, hlast, hu, spike]
    exact .inl ⟨heq ▸ c⟩

private theorem binary_minor_of_failure {R : Set (Fin m → Bool)}
    (hR : Available arity sem R) (pins : ∀ b, Available arity sem (pin b))
    (b : Bool) (f : (Fin 2 → Bool) → Bool)
    (hid : ∀ d, f (fun _ => d) = d)
    (hdiff : ∀ a, a 0 ≠ a 1 → f a = b)
    (h : ¬IsPolymorphism f R) :
    ∃ S : Set (Fin 2 → Bool), Available arity sem S ∧
      disequality ⊆ S ∧ (fun _ => b) ∉ S := by
  classical
  obtain ⟨n, S, ⟨c⟩, hb, hmin⟩ :=
    minimal_available (fun _ S => ¬IsPolymorphism f S) hR h
  have hn : n ≠ 0 := by
    rintro rfl
    exact hb fun a ha => (Subsingleton.elim (a 0) fun i => f fun j => a j i) ▸ ha 0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have bad_pair (z : Fin 2 → Fin (n + 1) → Bool) (hz : ∀ q, z q ∈ S)
      (hout : (fun i => f (fun q => z q i)) ∉ S) (j : Fin (n + 1)) :
      z 0 j ≠ z 1 j := by
    intro heq
    have hc : IsPolymorphism f (cofactor S j (z 0 j)) := by
      by_contra hh
      exact hmin n _ ⟨.cofactor c j _ (Classical.choice (pins _))⟩ (by omega) hh
    refine hout (mem_of_cofactor_closure (hid _) hc z hz fun q => ?_)
    fin_cases q
    exacts [rfl, heq.symm]
  obtain ⟨a, ha, hout⟩ : ∃ a : Fin 2 → Fin (n + 1) → Bool,
      (∀ q, a q ∈ S) ∧ (fun i => f (fun q => a q i)) ∉ S := by
    simpa only [IsPolymorphism, not_forall, exists_prop] using hb
  have heout : (fun i => f (fun q => a q i)) = fun _ => b :=
    funext fun i => hdiff _ (bad_pair a ha hout i)
  have hz : (fun _ : Fin (n + 1) => b) ∉ S := heout ▸ hout
  have hu (j : Fin (n + 1)) : spike b j ∈ S := by
    apply spike_mem b hz j
    have hp : IsPolymorphism f (project S j) := by
      by_contra hh
      exact hmin n _ ⟨.project c j⟩ (by omega) hh
    have hm := hp (fun q => j.removeNth (a q)) (fun q => remove_mem_project (ha q) j)
    have heq : (fun i => f (fun q => j.removeNth (a q) i)) = fun _ : Fin n => b :=
      congrArg j.removeNth heout
    exact heq ▸ hm
  have hn2 : 2 ≤ n + 1 := by
    by_contra hh
    obtain rfl : n = 0 := by omega
    have heq (q : Fin 2) : a q = fun _ => !b :=
      (eq_or_eq_not (fun _ => b) (a q)).resolve_left fun h => hz (h ▸ ha q)
    exact bad_pair a ha hout 0 (by rw [heq 0, heq 1])
  have hnle : n + 1 ≤ 2 := by
    by_contra hh
    let i : Fin (n + 1) := ⟨0, by omega⟩
    let j : Fin (n + 1) := ⟨1, by omega⟩
    let z : Fin 2 → Fin (n + 1) → Bool := ![spike b i, spike b j]
    have hez : (fun p => f (fun q => z q p)) = fun _ => b := by
      ext p
      by_cases hi : p = i
      · exact hdiff _ (by simp [z, spike, hi, i, j])
      by_cases hj : p = j
      · exact hdiff _ (by simp [z, spike, hj, i, j])
      have hconst : (fun q => z q p) = fun _ => b := by
        ext q
        fin_cases q <;> simp [z, spike, hi, hj]
      rw [hconst, hid]
    exact bad_pair z (fun q => by fin_cases q <;> exact hu _) (hez.symm ▸ hz) ⟨2, by omega⟩
      (by simp [z, spike, i, j])
  obtain rfl : n = 1 := by omega
  refine ⟨S, ⟨c⟩, fun x hx => ?_, hz⟩
  have rows : ∀ b (x : Fin 2 → Bool), x 0 ≠ x 1 → x = spike b 0 ∨ x = spike b 1 := by decide
  rcases rows b x hx with rfl | rfl <;> exact hu _

/-- With actual unary pins, separate AND and OR failures construct disequality by the
specific binary intersection of Lemma 3. No ternary or unrestricted intersection is used. -/
theorem disequality_of_pins {R : Set (Fin m → Bool)} {S : Set (Fin n → Bool)}
    (hR : Available arity sem R) (hS : Available arity sem S)
    (pins : ∀ b, Available arity sem (pin b))
    (ha : ¬IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) R)
    (ho : ¬IsPolymorphism (fun a : Fin 2 → Bool => a 0 || a 1) S) :
    Available arity sem disequality := by
  obtain ⟨P, ⟨p⟩, hinP, hzP⟩ := binary_minor_of_failure hR pins false
    (fun a => a 0 && a 1) (fun b => by cases b <;> rfl)
    (by intro a h; cases h0 : a 0 <;> cases h1 : a 1 <;> simp_all) ha
  obtain ⟨Q, ⟨q⟩, hinQ, hzQ⟩ := binary_minor_of_failure hS pins true
    (fun a => a 0 || a 1) (fun b => by cases b <;> rfl)
    (by intro a h; cases h0 : a 0 <;> cases h1 : a 1 <;> simp_all) ho
  have heq : P ∩ Q = disequality := by
    refine Set.Subset.antisymm (fun x ⟨hp, hq⟩ he => ?_) fun x hx => ⟨hinP hx, hinQ hx⟩
    have hconst : x = fun _ => x 0 := by
      ext i
      fin_cases i
      exacts [rfl, he.symm]
    cases hb : x 0
    · exact hzP (hconst.trans (funext fun _ => hb) ▸ hp)
    · exact hzQ (hconst.trans (funext fun _ => hb) ▸ hq)
  exact ⟨heq ▸ Construction.binaryMeet p q⟩

/-- Disequality and failure of complement construct both unary pins. Each descent uses only
the first adjacent pair, with its first coordinate immediately deleted. -/
theorem pins_of_disequality {R : Set (Fin m → Bool)}
    (hR : Available arity sem R) (hd : Available arity sem disequality)
    (h : ¬IsPolymorphism (fun a : Fin 1 → Bool => !(a 0)) R) :
    ∀ b, Available arity sem (pin b) := by
  classical
  obtain ⟨n, S, ⟨c⟩, hb, hmin⟩ := minimal_available
    (fun _ S => ¬IsPolymorphism (fun a : Fin 1 → Bool => !(a 0)) S) hR h
  obtain ⟨a, ha, hout⟩ : ∃ a : Fin 1 → Fin n → Bool,
      (∀ q, a q ∈ S) ∧ (fun i => !(a 0 i)) ∉ S := by
    simpa only [IsPolymorphism, not_forall, exists_prop] using hb
  let x := a 0
  have hx : x ∈ S := ha 0
  have hnot : (fun i => !(x i)) ∉ S := hout
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnot ((Subsingleton.elim x (fun i => !(x i))) ▸ hx)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain rfl : n = 0 := by
    by_contra hh
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh
    let d := x 0 ^^ x 1
    have hd' : ∀ u v : Bool, u = (v ^^ (u ^^ v)) ∧ (!u) = (!v ^^ (u ^^ v)) := by decide
    have hc : Available arity sem (adjacent S d) := by
      cases he : d
      exacts [⟨.equalDrop c⟩, ⟨.differentDrop c (Classical.choice hd)⟩]
    refine hmin (k + 1) _ hc (by omega) fun hf => hnot ?_
    have hh := hf (fun _ => Fin.tail x) (fun _ => mem_adjacent hx d (hd' _ _).1)
    change Fin.cons (!(x 1) ^^ d) (Fin.tail (fun i => !(x i))) ∈ S at hh
    rwa [← (hd' (x 0) (x 1)).2, Fin.cons_self_tail (fun i => !(x i))] at hh
  have heq : S = pin (x 0) := by
    ext y
    rcases eq_or_eq_not x y with rfl | rfl <;> simp [pin, hx, hnot]
  have hp : Construction arity sem (pin (x 0)) := heq ▸ c
  have htwist : twist (pin (x 0)) (Pi.single 0 true) = pin (!(x 0)) := by
    ext y
    change (y 0 + true) = x 0 ↔ y 0 = !(x 0)
    cases y 0 <;> cases x 0 <;> decide
  intro b
  obtain rfl | rfl : b = x 0 ∨ b = !(x 0) := by cases b <;> cases x 0 <;> simp
  exacts [⟨hp⟩, ⟨htwist ▸ Construction.flip hp 0 (Classical.choice hd)⟩]

/-- The non-Schaefer hypothesis constructs disequality from original language symbols.
The ZERO/ONE witnesses and the AND/OR witnesses are selected independently. -/
theorem disequality_of_not_hasSchaeferPolymorphism
    (h : ¬HasSchaeferPolymorphism arity sem) : Available arity sem disequality := by
  classical
  simp only [HasSchaeferPolymorphism, not_or] at h
  obtain ⟨hzero, hone, hand, hor, -⟩ := h
  rw [hasPolymorphism_const_iff] at hzero hone
  simp only [not_forall] at hzero hone
  obtain ⟨r, hr, hz⟩ := hzero
  obtain ⟨s, hs, ho⟩ := hone
  rcases disequality_or_pin_of_missing_constant ⟨.atom r⟩ false hr hz with hd | h1
  · exact hd
  rcases disequality_or_pin_of_missing_constant ⟨.atom s⟩ true hs ho with hd | h0
  · exact hd
  obtain ⟨r, hr⟩ := not_forall.1 hand
  obtain ⟨s, hs⟩ := not_forall.1 hor
  exact disequality_of_pins ⟨.atom r⟩ ⟨.atom s⟩ (fun b => by cases b; exacts [h0, h1]) hr hs

/-- Lemma 3's nonselfdual endpoint, with no adjoined-constant premise: disequality and both
unary pins have finite ordered constructions from the original language. Complement, constant,
AND and OR failures may belong to different symbols. -/
theorem constants_of_not_hasSchaeferPolymorphism
    (h : ¬HasSchaeferPolymorphism arity sem)
    (hn : ¬HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0))) :
    Available arity sem disequality ∧ ∀ b, Available arity sem (pin b) := by
  have hd := disequality_of_not_hasSchaeferPolymorphism h
  obtain ⟨r, hr⟩ := not_forall.1 hn
  exact ⟨hd, pins_of_disequality ⟨.atom r⟩ hd hr⟩

end Cslib.Logic.PL.CSP.RelationMinor
