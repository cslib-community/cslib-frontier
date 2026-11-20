/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Computability.RecursiveInEvalnPrimrec
public import Mathlib.Algebra.Notation.Indicator

/-!
# Membership oracles and the diagonal jump

A query to a set oracle returns its natural-number characteristic value (one for membership,
zero otherwise). A code enumerates a set when its domain is that set, and decides a set when
it computes the characteristic function on every input.

The diagonal jump asks whether an oracle code halts on its own index. A primitive recursive
map sends each input of a fixed code to a diagonal instance by specialization.

The jump overlaps the `SingleOracle` construction in
[mathlib4#38973](https://github.com/leanprover-community/mathlib4/pull/38973).
Here the jump specializes `RecursiveIn.Code` to total set-membership oracles,
using the existing finite-prefix evaluator.

## Main definitions

* `EnumerableIn`, `DecidableIn`: relative enumeration and decision of sets of naturals.
* `oracleJump`, `iteratedJump`: diagonal oracle halting and its iteration from the empty set.

## Main results

* `EnumerableIn.decidableIn_jump`: the jump decides every set enumerable in its oracle.
* `decidableIn_iff_enumerableIn_compl`: a relative decider is equivalent to two relative
  semideciders for the set and its complement.
-/

public section

open Encodable Denumerable

namespace Cslib.Computability

open Nat.RecursiveIn (Code)
open Nat.RecursiveIn.Code (zero succ comp eval encodeCode_eq encodeCode)

/-- Construction of a composition code is primitive recursive. -/
private theorem primrec₂_comp : Primrec₂ comp := by
  apply Primrec₂.encode_iff.mp
  have h : Primrec₂ fun a b : Code => Nat.pair (encode a) (encode b) :=
    Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd)
  have hd := Primrec.nat_double.comp (Primrec.nat_double_succ.comp h)
  exact (Primrec.nat_add.comp hd (Primrec₂.const 5)).of_eq fun _ => by
    simp only [encodeCode_eq, encodeCode]

/-- The code for a constant natural number. -/
private def constCode : ℕ → Code
  | 0 => zero
  | n + 1 => comp succ (constCode n)

/-- Constant codes ignore the oracle and the input. -/
@[simp] private theorem eval_const (g : ℕ →. ℕ) (a n : ℕ) :
    eval g (constCode a) n = Part.some a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change (eval g (constCode a) n).bind (fun x => Part.some x.succ) = _
    rw [ih, Part.bind_some]

/-- Construction of a constant code is primitive recursive. -/
private theorem primrec_const : Primrec constCode := by
  have hs : Primrec fun _ : ℕ × Code => succ := Primrec.const succ
  exact (Primrec.nat_rec₁ zero
    (primrec₂_comp.comp hs Primrec.snd).to₂).of_eq fun n => by
      induction n with
      | zero => rfl
      | succ n ih => exact congrArg (comp succ) ih

/-- The total membership oracle of a set, with answers in `{0, 1}`. -/
@[expose] noncomputable def membershipOracle (A : Set ℕ) : ℕ → ℕ := A.indicator 1

/-- Computable enumerability relative to a set membership oracle, witnessed by halting. -/
@[expose] def EnumerableIn (A B : Set ℕ) : Prop :=
  ∃ c : Code, ∀ n, n ∈ A ↔ (c.eval (membershipOracle B) n).Dom

/-- Computability relative to a set membership oracle, witnessed by total characteristic output. -/
@[expose] def DecidableIn (A B : Set ℕ) : Prop :=
  Nat.RecursiveIn {(membershipOracle B : ℕ →. ℕ)} (membershipOracle A)

/-- Deciding a set means computing its total characteristic function with an oracle code. -/
theorem decidableIn_iff_exists_code {A B : Set ℕ} :
    DecidableIn A B ↔ ∃ c : Code, c.eval (membershipOracle B) = membershipOracle A :=
  Code.exists_code

/-- The diagonal oracle halting set. -/
@[expose] def oracleJump (A : Set ℕ) : Set ℕ :=
  {n | ((ofNat Code n).eval (membershipOracle A) n).Dom}

/-- The iterated diagonal jumps starting from the empty set. -/
@[expose] def iteratedJump : ℕ → Set ℕ
  | 0 => ∅
  | k + 1 => oracleJump (iteratedJump k)

/-- A fixed-code halting question is a primitive recursive preimage of the diagonal jump. -/
theorem exists_primrec_reduce_oracleJump (c : Code) :
    ∃ f : ℕ → ℕ, Primrec f ∧ ∀ A n,
      (c.eval (membershipOracle A) n).Dom ↔ f n ∈ oracleJump A := by
  let specialize := fun n => Code.comp c (constCode n)
  refine ⟨fun n => encode (specialize n), Primrec.encode.comp
    (primrec₂_comp.comp (Primrec.const c) primrec_const), ?_⟩
  intro A n
  change _ ↔ (Code.eval _ (ofNat Code (encode (specialize n))) (encode (specialize n))).Dom
  rw [ofNat_encode]
  change _ ↔ ((Code.eval _ (constCode n) _).bind (fun x => Code.eval (membershipOracle A) c x)).Dom
  rw [eval_const, Part.bind_some]

/-- Every relatively enumerable set many-one reduces to the diagonal jump. -/
theorem EnumerableIn.exists_primrec_reduce_oracleJump {A B : Set ℕ} (h : EnumerableIn A B) :
    ∃ f : ℕ → ℕ, Primrec f ∧ ∀ n, n ∈ A ↔ f n ∈ oracleJump B := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨f, hf, h⟩ := Cslib.Computability.exists_primrec_reduce_oracleJump c
  exact ⟨f, hf, fun n => (hc n).trans (h B n)⟩

/-- A primitive recursive preimage is decidable from the target set. -/
theorem decidableIn_of_primrec_preimage {A B : Set ℕ} {f : ℕ → ℕ}
    (hf : Primrec f) (hmem : ∀ n, n ∈ A ↔ f n ∈ B) : DecidableIn A B := by
  have h₀ : Nat.RecursiveIn {(membershipOracle B : ℕ →. ℕ)} (membershipOracle B) :=
    .oracle _ (Set.mem_singleton _)
  have h := h₀.comp (Primrec.nat_iff.mp hf).recursiveIn
  apply h.of_eq
  intro n
  change (Part.some (f n)).bind (fun m => Part.some (membershipOracle B m)) = _
  rw [Part.bind_some]
  congr 1
  classical
  by_cases hn : n ∈ A
  · simp [membershipOracle, hn, (hmem n).mp hn]
  · simp [membershipOracle, hn, mt (hmem n).mpr hn]

/-- An enumerable set is decidable from the jump of its oracle. -/
theorem EnumerableIn.decidableIn_jump {A B : Set ℕ} (h : EnumerableIn A B) :
    DecidableIn A (oracleJump B) := by
  obtain ⟨_, hf, hmem⟩ := h.exists_primrec_reduce_oracleJump
  exact decidableIn_of_primrec_preimage hf hmem

/-- An enumeration can simulate its oracle using a relative decider for that oracle. -/
theorem EnumerableIn.of_decidableIn {A B D : Set ℕ} (h : EnumerableIn A B)
    (hBD : DecidableIn B D) : EnumerableIn A D := by
  obtain ⟨c, hc⟩ := h
  have hrec := (Code.exists_code (g := membershipOracle B)).mpr ⟨c, rfl⟩
  obtain ⟨d, hd⟩ := (Code.exists_code (g := membershipOracle D)).mp
    (hrec.subst fun g hg => (Set.mem_singleton_iff.mp hg).symm ▸ hBD)
  exact ⟨d, fun n => hd ▸ hc n⟩

/-- The oracle indicator detects membership. -/
@[simp] theorem membershipOracle_eq_one {A : Set ℕ} {n : ℕ} :
    membershipOracle A n = 1 ↔ n ∈ A := by
  classical
  by_cases h : n ∈ A <;> simp [membershipOracle, h]

/-- The oracle indicator detects nonmembership. -/
@[simp] theorem membershipOracle_eq_zero {A : Set ℕ} {n : ℕ} :
    membershipOracle A n = 0 ↔ n ∉ A := by
  classical
  by_cases h : n ∈ A <;> simp [membershipOracle, h]

/-- Relatively decidable sets are closed under complement. -/
theorem DecidableIn.compl {A B : Set ℕ} (h : DecidableIn A B) : DecidableIn Aᶜ B := by
  have hs : Nat.RecursiveIn {(membershipOracle B : ℕ →. ℕ)}
      (fun n => Part.some (1 - n)) :=
    (Primrec.nat_iff.mp (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id)).recursiveIn
  apply (hs.comp h).of_eq
  intro n
  classical
  by_cases hn : n ∈ A <;> simp [membershipOracle, hn, Part.bind_eq_bind]

/-- An existential number quantifier over a relatively decidable relation gives an enumerable set.
The matrix receives its input and its witness encoded by `Nat.pair`. -/
theorem DecidableIn.exists_pair {A B : Set ℕ} (h : DecidableIn A B) :
    EnumerableIn {n | ∃ m, Nat.pair n m ∈ A} B := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Nat.RecursiveIn.rfind h.compl)
  refine ⟨c, fun n => ?_⟩
  rw [hc]
  refine Iff.trans ?_ Nat.rfind_dom.symm
  change (∃ m, n.pair m ∈ A) ↔ ∃ m,
    true ∈ (Part.some (membershipOracle Aᶜ (n.pair m))).map (fun x => decide (x = 0)) ∧
      ∀ {i : ℕ}, i < m →
        ((Part.some (membershipOracle Aᶜ (n.pair i))).map (fun x => decide (x = 0))).Dom
  classical
  simp [membershipOracle_eq_zero]

/-- A decidable oracle predicate is semidecidable. -/
theorem DecidableIn.enumerableIn {A B : Set ℕ} (h : DecidableIn A B) : EnumerableIn A B := by
  have he : DecidableIn {p | p.unpair.1 ∈ A} B := by
    apply (h.comp Nat.RecursiveIn.left).of_eq
    intro p
    classical
    change (Part.some p.unpair.1).bind (fun n => Part.some (membershipOracle A n)) = _
    rw [Part.bind_some]
    by_cases hp : p.unpair.1 ∈ A <;> simp [membershipOracle, hp]
  obtain ⟨c, hc⟩ := he.exists_pair
  exact ⟨c, fun n => (show n ∈ A ↔ ∃ m, (n.pair m).unpair.1 ∈ A by simp).trans (hc n)⟩


private theorem recursiveIn_encode_prefix (f : ℕ → ℕ) :
    Nat.RecursiveIn {(f : ℕ →. ℕ)} (fun s => Part.some (encode (Code.prefixOf f s))) := by
  have hf : Nat.RecursiveIn {(f : ℕ →. ℕ)} (f : ℕ →. ℕ) :=
    .oracle _ (Set.mem_singleton _)
  have happ : Primrec fun p : ℕ =>
      encode (((decode (α := List ℕ) p.unpair.1).getD []) ++ [p.unpair.2]) := by
    have hlist : Primrec fun p : ℕ => (decode (α := List ℕ) p.unpair.1).getD [] :=
      Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.const [])
    exact Primrec.encode.comp (Primrec.list_concat.comp hlist (Primrec.snd.comp Primrec.unpair))
  let step (n : ℕ) := Part.some (encode
    (((decode (α := List ℕ) n.unpair.2.unpair.2).getD []) ++ [f n.unpair.2.unpair.1]))
  have hstep : Nat.RecursiveIn {(f : ℕ →. ℕ)} step := by
    apply ((Primrec.nat_iff.mp happ).recursiveIn.comp
      ((Nat.RecursiveIn.right.comp Nat.RecursiveIn.right).pair
        (hf.comp (Nat.RecursiveIn.left.comp Nat.RecursiveIn.right)))).of_eq
    intro n
    simp only [step, Seq.seq, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
      Part.map_eq_map, Part.map_some, decode_eq_ofNat, Option.getD_some]
    have hvalue (i : ℕ) : Part.some i >>= (f : ℕ →. ℕ) = Part.some (f i) :=
      Part.bind_some i (fun x => Part.some (f x))
    rw [hvalue, Part.map_some, Part.bind_some, Nat.unpair_pair]
  have hbase : Nat.RecursiveIn {(f : ℕ →. ℕ)} (fun _ => Part.some (encode ([] : List ℕ))) :=
    (Primrec.nat_iff.mp (Primrec.const _)).recursiveIn
  have hpair : Nat.Primrec (Nat.pair 0) := Nat.Primrec.pair (Nat.Primrec.const 0) Nat.Primrec.id
  apply ((hbase.prec hstep).comp hpair.recursiveIn).of_eq
  intro s
  change (Part.some (Nat.pair 0 s)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction s with
  | zero => rfl
  | succ s ih =>
    change (Nat.rec (motive := fun _ => Part ℕ) (Part.some (encode ([] : List ℕ)))
        (fun i prev => prev.bind fun v => step (Nat.pair 0 (Nat.pair i v))) s).bind
      (fun v => step (Nat.pair 0 (Nat.pair s v))) = _
    simp only [Part.bind_eq_bind] at ih
    rw [ih, Part.bind_some]
    simp [step, Code.prefixOf, List.range_succ]


private theorem recursiveIn_stage {f : ℕ → ℕ} {test : ℕ × List ℕ → ℕ}
    (ht : Primrec test) :
    Nat.RecursiveIn {(f : ℕ →. ℕ)}
      (fun p => Part.some (test (p, Code.prefixOf f p.unpair.2.unpair.1))) := by
  have h : Primrec fun x : ℕ =>
      test (x.unpair.1, ((decode (α := List ℕ) x.unpair.2).getD [])) :=
    ht.comp ((Primrec.fst.comp Primrec.unpair).pair
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.const [])))
  have hp := (recursiveIn_encode_prefix f).comp
    (Nat.RecursiveIn.left.comp Nat.RecursiveIn.right)
  apply ((Primrec.nat_iff.mp h).recursiveIn.comp (Nat.Primrec.id.recursiveIn.pair hp)).of_eq
  intro p
  simp [Part.bind_eq_bind, Seq.seq, Part.map_eq_map]

/-- A set and its complement are relatively enumerable exactly when the set is relatively
decidable. The decider searches stages for either code to halt and returns the corresponding
characteristic value. -/
theorem decidableIn_iff_enumerableIn_compl {A B : Set ℕ} :
    DecidableIn A B ↔ EnumerableIn A B ∧ EnumerableIn Aᶜ B := by
  refine ⟨fun h => ⟨h.enumerableIn, h.compl.enumerableIn⟩, ?_⟩
  rintro ⟨⟨pos, hpos⟩, ⟨neg, hneg⟩⟩
  let select (t : ℕ) := if t = 0 then pos else neg
  let hit (p : ℕ) (σ : List ℕ) :=
    ((select p.unpair.2.unpair.2).evaln σ p.unpair.2.unpair.1 p.unpair.1).isSome
  have hselect : Primrec select := Primrec.ite
    (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const pos) (Primrec.const neg)
  let u : Primrec fun x : ℕ × List ℕ => x.1.unpair := Primrec.unpair.comp Primrec.fst
  let v : Primrec fun x : ℕ × List ℕ => x.1.unpair.2.unpair :=
    Primrec.unpair.comp (Primrec.snd.comp u)
  have hhit : Primrec fun x : ℕ × List ℕ => hit x.1 x.2 :=
    Primrec.option_isSome.comp (Code.primrec_evaln.comp
      (Primrec.snd.pair (((Primrec.fst.comp v).pair
        (hselect.comp (Primrec.snd.comp v))).pair (Primrec.fst.comp u))))
  have htest : Primrec fun x : ℕ × List ℕ => bif hit x.1 x.2 then 0 else 1 :=
    Primrec.cond hhit (Primrec.const 0) (Primrec.const 1)
  let test (n w : ℕ) :=
    hit (n.pair w) (Code.prefixOf (membershipOracle B) w.unpair.1)
  have hfind : Nat.RecursiveIn {(membershipOracle B : ℕ →. ℕ)}
      (fun n => Nat.rfind fun w => Part.some (test n w)) := by
    apply (Nat.RecursiveIn.rfind (recursiveIn_stage htest)).of_eq
    intro n
    congr 1
    funext w
    change (Part.some (bif
      hit (n.pair w) (Code.prefixOf (membershipOracle B) (n.pair w).unpair.2.unpair.1)
      then 0 else 1)).map (fun x : ℕ => decide (x = 0)) = _
    simp only [Nat.unpair_pair, Part.map_some]
    change Part.some (decide ((bif test n w then 0 else 1) = 0)) = Part.some (test n w)
    have key (b : Bool) : decide ((bif b then (0 : ℕ) else 1) = 0) = b := by
      cases b <;> rfl
    rw [key]
  have hhalt (n w : ℕ) :
      test n w = true → ((select w.unpair.2).eval (membershipOracle B) n).Dom := by
    intro h
    dsimp [test, hit] at h
    simp only [Nat.unpair_pair] at h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact Part.dom_iff_mem.mpr ⟨x, Code.mem_eval_iff_exists_evaln.mpr ⟨_, hx⟩⟩
  have hexists (n : ℕ) : ∃ w, test n w = true := by
    classical
    have hcase (t : ℕ) (ht : ((select t).eval (membershipOracle B) n).Dom) :
        ∃ w, test n w = true := by
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp ht
      obtain ⟨s, hs⟩ := Code.mem_eval_iff_exists_evaln.mp hx
      refine ⟨s.pair t, ?_⟩
      simpa [test, hit] using Option.isSome_iff_exists.mpr ⟨x, hs⟩
    by_cases hn : n ∈ A
    · exact hcase 0 (by simpa [select] using (hpos n).mp hn)
    · exact hcase 1 (by simpa [select] using (hneg n).mp hn)
  let result (w : ℕ) : ℕ := if w.unpair.2 = 0 then 1 else 0
  have hresult : Primrec result :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
      (Primrec.const 1) (Primrec.const 0)
  apply ((Primrec.nat_iff.mp hresult).recursiveIn.comp hfind).of_eq
  intro n
  obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp (show (Nat.rfind fun w =>
    Part.some (test n w)).Dom from Nat.rfind_dom.mpr (by
      obtain ⟨w, hw⟩ := hexists n
      exact ⟨w, Part.mem_some_iff.mpr hw.symm, fun _ => trivial⟩))
  have hh := hhalt n w ((Part.mem_some_iff.mp (Nat.mem_rfind.mp hw).1).symm)
  have heq : Nat.rfind (fun w => Part.some (test n w)) = Part.some w := Part.eq_some_iff.mpr hw
  change (Nat.rfind (fun w => Part.some (test n w))).bind
    (fun w => Part.some (result w)) = _
  rw [heq, Part.bind_some]
  congr 1
  by_cases hz : w.unpair.2 = 0
  · simpa only [result, ite_eq_left hz] using
      (membershipOracle_eq_one.mpr ((hpos n).mpr (by simpa [select, hz] using hh))).symm
  · simpa only [result, ite_eq_right hz] using
      (membershipOracle_eq_zero.mpr ((hneg n).mpr (by simpa [select, hz] using hh))).symm

end Cslib.Computability
