/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Vals
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Positivity

/-!
# Matched runs are runs of the pointer machine

Decodes every matched universal-program run `x : XP P` (`Uni.MX x bits`) into a globally valid
pointer-machine trace `x.steps.map nst` (`Uni.MX.gv`), and proves that `x` is uniquely determined
by that trace (`Uni.MX.unique`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.Trace`.

## Main definitions

* `Uni.unb`: bit-slice columns representing `q` natural numbers at fixed width `L`.
* `Uni.nst`: decode a bit-sliced step `P.Rl × List (Fin 9 → Bool)` into `P.Step`.
* `Uni.σi`: initial configuration of pointer machine `P` on input `bits`.
* `Uni.cN`, `Uni.kyN`: record key representations of numeric records `Rec K`.
* `Uni.dfN`, `Uni.lsN`: list of defined numeric records and combined input to the radix sort.

## Main results

* `Uni.closed_σi`: the initial configuration is closed.
* `Uni.cols_ext`, `Uni.unb_proj`, `Uni.unb_bv`: column-slice representation lemmas.
* `Uni.chain_len`, `Uni.chain_val`: length and value invariants along matched chains.
* `Uni.MX.len_cn`, `Uni.MX.len`, `Uni.MX.length_eq`, `Uni.MX.vals`, `Uni.MX.size_eq`.
* `Uni.MX.gv`: every matched run decodes to a valid global trace `Mach.GV (σi P bits)`.
* `Uni.MX.unique`: a matched run is uniquely determined by its decoded machine trace.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Cslib.BitString (binaryValue binaryValue_append binaryValue_binaryWord binaryValue_cons
  binaryValue_lt_two_pow binaryValue_replicate_false binaryValue_succ_carry binaryWord
  binaryWord_binaryValue binaryWord_zero carry_cut_unique length_binaryWord)

section Columns

theorem cols_ext {q : ℕ} {c c' : List (Fin (q + 1) → Bool)}
    (h : ∀ j, c.map (fun v => v j) = c'.map fun v => v j) : c = c' := by
  refine List.ext_getElem (by simpa using congrArg List.length (h 0)) fun i h1 h2 => ?_
  funext j
  simpa [h1, h2] using congrArg (·[i]?) (h j)

/-- Column-major `L`-bit big-endian slices of a `q`-tuple of natural numbers (reduced modulo
`2 ^ L` so every column has unconditional length `L`). -/
@[expose] def unb (L : ℕ) {q : ℕ} (a : Fin q → ℕ) : List (Fin q → Bool) :=
  List.ofFn fun t : Fin L => fun j =>
    (binaryWord L (a j % 2 ^ L)).get
      (t.cast (length_binaryWord (Nat.mod_lt _ (by positivity))).symm)

theorem length_unb (L : ℕ) {q : ℕ} (a : Fin q → ℕ) : (unb L a).length = L := by simp [unb]

theorem unb_proj (L : ℕ) {q : ℕ} (a : Fin q → ℕ) (j : Fin q) :
    (unb L a).map (fun v => v j) = binaryWord L (a j % 2 ^ L) :=
  List.ext_getElem (by simp [length_unb, length_binaryWord (Nat.mod_lt (a j) (by positivity))])
    fun _ _ _ => by simp [unb]

/-- Re-encoding the decoded big-endian column values recovers the column list. -/
theorem unb_bv {q : ℕ} (w : List (Fin (q + 1) → Bool)) :
    unb w.length (fun j => binaryValue (w.map fun v => v j)) = w :=
  cols_ext fun j => by
    have hlt := binaryValue_lt_two_pow (w.map fun v => v j)
    rw [List.length_map] at hlt
    rw [unb_proj, Nat.mod_eq_of_lt hlt]
    simpa only [List.length_map] using binaryWord_binaryValue (w.map fun v => v j)

end Columns

section Chains

theorem chain_len {ι : Type*} (l : List ι) (f g : ι → List Bool) (a b : List Bool)
    (h : a :: l.map f = l.map g ++ [b]) (hfg : ∀ r ∈ l, (f r).length = (g r).length) :
    (∀ r ∈ l, (g r).length = a.length) ∧ b.length = a.length := by
  induction l generalizing a with
  | nil => simpa using congrArg (List.map List.length) h.symm
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := ih (f r) h.2 fun r hr => hfg r (List.mem_cons_of_mem _ hr)
    have h3 : (f r).length = a.length :=
      (hfg r List.mem_cons_self).trans (congrArg List.length h.1.symm)
    exact ⟨List.forall_mem_cons.2 ⟨congrArg List.length h.1.symm,
      fun r' hr' => (h1 r' hr').trans h3⟩, h2.trans h3⟩

theorem chain_val {ι : Type*} (l : List ι) (f g : ι → List Bool) (a b : List Bool)
    (h : a :: l.map f = l.map g ++ [b])
    (hfg : ∀ r ∈ l, binaryValue (f r) = binaryValue (g r) + 1) :
    l.map (fun r => binaryValue (g r)) =
        (List.range l.length).map (fun j => binaryValue a + j) ∧
      binaryValue b = binaryValue a + l.length := by
  induction l generalizing a with
  | nil => simpa using congrArg (List.map binaryValue) h.symm
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := ih (f r) h.2 fun r hr => hfg r (List.mem_cons_of_mem _ hr)
    have h3 : binaryValue (f r) = binaryValue a + 1 := by rw [hfg r List.mem_cons_self, h.1]
    rw [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      h1, h2, h3, h.1]
    exact ⟨congrArg _ (List.map_congr_left fun j _ => by simp only [Function.comp]; omega),
      by omega⟩

end Chains

section Trace

variable {A M K : Type}

/-- Decode a bit-sliced step into a pointer-machine step with numeric variable assignments. -/
@[expose] def nst {P : Mach A M K} (s : P.Rl × List (Fin 9 → Bool)) : P.Step :=
  (s.1, fun i => binaryValue (cw s.2 i))

/-- Initial configuration of pointer machine `P` on input `bits`. -/
@[expose] def σi (P : Mach A M K) (bits : List Bool) : Mach.State M K :=
  ⟨P.m0, fun _ => 0, [(P.kN, ![0, 0, 0, 0])], 0, bits⟩

/-- The initial configuration is closed: its counter, its registers and the entries of its only
record `(P.kN, ![0, 0, 0, 0])` are `0`. -/
theorem closed_σi (P : Mach A M K) (bits : List Bool) : Mach.Closed (σi P bits) := by
  refine ⟨fun c hc i => ?_, fun j hj => ⟨_, List.mem_singleton_self _, (Nat.le_zero.1 hj).symm⟩,
    fun _ => le_rfl⟩
  rw [List.mem_singleton.1 hc]
  fin_cases i <;> exact le_rfl

/-- Key-letter content list of an `L`-bit numeric record `ρ : Rec K`. -/
@[expose] def cN (L : ℕ) (ρ : Rec K) : List (Bl K) := cont ρ.1 (unb L ρ.2)

theorem length_cN (L : ℕ) (ρ : Rec K) : (cN L ρ).length = L + 1 := by
  simp [cN, cont, length_unb]

/-- Indexed radix-sort key `Fin (L + 1) → Bl K` of an `L`-bit numeric record `ρ`. -/
@[expose] def kyN (L : ℕ) (ρ : Rec K) : Fin (L + 1) → Bl K :=
  fun i => (cN L ρ).get (i.cast (length_cN L ρ).symm)

theorem ofFn_kyN (L : ℕ) (ρ : Rec K) : List.ofFn (kyN L ρ) = cN L ρ :=
  List.ext_getElem (by rw [List.length_ofFn, length_cN]) fun _ _ _ => List.getElem_ofFn _

theorem kyN_inj {L : ℕ} {ρ ρ' : Rec K} (h : ∀ j, ρ.2 j < 2 ^ L)
    (h' : ∀ j, ρ'.2 j < 2 ^ L) (e : kyN L ρ = kyN L ρ') : ρ = ρ' := by
  have h1 : cN L ρ = cN L ρ' := by rw [← ofFn_kyN, ← ofFn_kyN, e]
  simp only [cN, cont, List.cons.injEq, Sum.inl.injEq] at h1
  have h2 := List.map_injective_iff.2 Sum.inr_injective h1.2
  refine Prod.ext h1.1 (funext fun j => ?_)
  have h3 := congrArg (List.map fun v : Fin 4 → Bool => v j) h2
  rw [unb_proj, unb_proj, Nat.mod_eq_of_lt (h j), Nat.mod_eq_of_lt (h' j)] at h3
  simpa [binaryValue_binaryWord] using congrArg binaryValue h3

theorem length_cn (r : List Bool × List Unit) : (cn1 r).length = (cn r).length := by
  simp [cn, cn1]

theorem bv_cn (r : List Bool × List Unit) : binaryValue (cn1 r) = binaryValue (cn r) + 1 :=
  binaryValue_succ_carry _ _

theorem bv_i1 (l : List Unit) : binaryValue (i1 l) = 1 := by
  simp only [i1, binaryValue_append, binaryValue_replicate_false]; rfl

theorem length_i1 (l : List Unit) : (i1 l).length = l.length + 1 := by simp [i1]

theorem length_i0 (l : List Unit) : (i0 l).length = l.length + 1 := by simp [i0]

theorem bv_i0 (l : List Unit) : binaryValue (i0 l) = 0 := binaryValue_replicate_false _

private theorem cols_four_eq_unb {L : ℕ} {w : List (Fin 9 → Bool)} (hl : w.length = L)
    (i0 i1 i2 i3 : Fin 9) :
    (w.map fun v => ![v i0, v i1, v i2, v i3]) =
      unb L ![binaryValue (cw w i0), binaryValue (cw w i1),
        binaryValue (cw w i2), binaryValue (cw w i3)] := by
  have key : ∀ i, cw w i = binaryWord L (binaryValue (cw w i) % 2 ^ L) := fun i => by
    have hlen : (cw w i).length = L := by simp [cw, hl]
    rw [Nat.mod_eq_of_lt (hlen ▸ binaryValue_lt_two_pow _), ← hlen, binaryWord_binaryValue]
  refine cols_ext fun j => ?_
  rw [unb_proj, List.map_map]
  fin_cases j <;> exact key _

theorem alc_eq {P : Mach A M K} {L : ℕ} {s : P.Rl × List (Fin 9 → Bool)}
    (hl : s.2.length = L) : alc P s.1 s.2 = unb L (Mach.al (nst s)).2 :=
  cols_four_eq_unb hl 8 (P.af s.1 0) (P.af s.1 1) (P.af s.1 2)

theorem ldc_eq {P : Mach A M K} {L : ℕ} {s : P.Rl × List (Fin 9 → Bool)}
    (hl : s.2.length = L) : ldc P s.1 s.2 = unb L (Mach.ld (nst s)).2 :=
  cols_four_eq_unb hl (rv (P.la s.1)) 5 6 7

section Facts

variable [Fintype K] [DecidableEq K] {P : Mach A M K} {x : XP P} {bits : List Bool}
  (hx : MX x bits)

include hx

theorem MX.len_cn :
    (∀ r ∈ x.counter, (cn r).length = x.init.length + 1) ∧
      x.finalCounter.length + 1 = x.init.length + 1 := by
  simpa [length_i1] using chain_len x.counter cn1 cn _ _ hx.cp fun r _ => length_cn r

theorem MX.len : ∀ s ∈ x.steps, s.2.length = x.init.length + 1 := fun s hs => by
  obtain ⟨r, hr, e⟩ := List.mem_map.1 (hx.fr ▸ List.mem_map.2 ⟨s, hs, rfl⟩)
  simpa [cw, e] using hx.len_cn.1 r hr

theorem MX.length_eq : x.counter.length = x.steps.length := by
  simpa using congrArg List.length hx.fr

theorem MX.vals :
    x.steps.map (fun s => binaryValue (cw s.2 8)) =
        (List.range x.steps.length).map (fun j => 1 + j) ∧
      binaryValue (true :: x.finalCounter) = 1 + x.steps.length := by
  have h1 := chain_val x.counter cn1 cn _ _ hx.cp fun r _ => bv_cn r
  rw [bv_i1, hx.length_eq] at h1
  have h2 := congrArg (List.map binaryValue) hx.fr
  rw [List.map_map, List.map_map] at h2
  exact ⟨h2.symm.trans h1.1, h1.2⟩

theorem MX.size_eq : Nat.size (x.steps.length + 1) = x.init.length + 1 := by
  have h1 := hx.vals.2
  have h3 := binaryValue_lt_two_pow x.finalCounter
  rw [binaryValue_cons, Bool.toNat_true, one_mul, Nat.succ.inj hx.len_cn.2] at h1
  rw [Nat.succ.inj hx.len_cn.2] at h3
  exact le_antisymm (Nat.size_le.2 (by rw [pow_succ]; omega))
    (Nat.succ_le_iff.2 (Nat.lt_size.2 (by omega)))

end Facts

/-- The initial record `0` followed by all records allocated during trace `tr`. -/
@[expose] def dfN {P : Mach A M K} (tr : List P.Step) : List (Rec K) :=
  (P.kN, ![0, 0, 0, 0]) :: tr.map Mach.al

/-- The flagged list `(defined records) ++ (loaded records)` passed to the radix sort. -/
@[expose] def lsN {P : Mach A M K} (L : ℕ) (tr : List P.Step) :
    List (List.RadixSort.Rc (L + 1) (Bl K)) :=
  ((dfN tr).map (kyN L)).map (fun k => (false, k)) ++
    ((tr.map Mach.ld).map (kyN L)).map fun k => (true, k)

theorem recs_lsN {P : Mach A M K} (L : ℕ) (tr : List P.Step) :
    recs 0 (lsN L tr) =
      ((dfN tr).map (cN L)).map (fun c => (false, oc c)) ++
        ((tr.map Mach.ld).map (cN L)).map fun c => (true, oc c) := by
  simp only [recs, lsN, List.map_append, List.map_map, Function.comp_def, rot_zero, ofFn_kyN, oc]

theorem lsN_ne {P : Mach A M K} (L : ℕ) (tr : List P.Step) : lsN L tr ≠ [] := by
  simp [lsN, dfN]

theorem unb_zero (L : ℕ) : unb L ![0, 0, 0, 0] = List.replicate L fun _ : Fin 4 => false :=
  cols_ext fun j => by fin_cases j <;> simp [unb_proj, binaryWord_zero]

theorem block_of {P : Mach A M K} {x : XP P}
    (hx : ∀ s ∈ x.steps, s.2.length = x.init.length + 1) :
    (dfs x).map (fun c => (false, oc c)) ++ (lks x).map (fun c => (true, oc c)) =
      recs 0 (lsN (x.init.length + 1) (x.steps.map nst)) := by
  rw [recs_lsN, dfs, dfN, lks]
  simp only [List.map_cons, List.map_map, Function.comp_def, cN, unb_zero]
  exact congrArg₂ (· ++ ·) (congrArg (List.cons _)
    (List.map_congr_left fun s hs => by rw [alc_eq (hx s hs)]; rfl))
    (List.map_congr_left fun s hs => by rw [ldc_eq (hx s hs)]; rfl)

theorem MX.block [Fintype K] [DecidableEq K] {P : Mach A M K} {x : XP P} {bits : List Bool}
    (hx : MX x bits) :
    (dfs x).map (fun c => (false, oc c)) ++ (lks x).map (fun c => (true, oc c)) =
      recs 0 (lsN (x.init.length + 1) (x.steps.map nst)) :=
  block_of hx.len

theorem nst_lt [Fintype K] [DecidableEq K] {P : Mach A M K} {x : XP P} {bits : List Bool}
    (hx : MX x bits) {s : P.Rl × List (Fin 9 → Bool)} (hs : s ∈ x.steps) (i : Fin 9) :
    (nst s).2 i < 2 ^ (x.init.length + 1) := by
  simpa only [nst, cw, List.length_map, hx.len s hs] using binaryValue_lt_two_pow (cw s.2 i)

private theorem four_lt {a b c d n : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (j : Fin 4) : (![a, b, c, d] : Fin 4 → ℕ) j < n := by
  fin_cases j <;> assumption

/-- A matched run `MX x bits` decodes to a globally valid pointer-machine trace `Mach.GV`. -/
theorem MX.gv [Fintype K] [DecidableEq K] {P : Mach A M K} {x : XP P} {bits : List Bool}
    (hx : MX x bits) : Mach.GV (σi P bits) (x.steps.map nst) := by
  refine ⟨?_, fun i => ⟨binaryValue (x.finalRegs.map fun v => v i), ?_⟩, ?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def, nst, σi] using hx.md
  · have h := congrArg (List.map binaryValue) (hx.rg i)
    rw [List.map_cons, List.map_append, List.map_map, List.map_map, bv_i0] at h
    rwa [List.map_map, List.map_map]
  · rw [List.map_map, List.length_map]
    exact hx.vals.1.trans (List.map_congr_left fun j _ => by simp [σi])
  · simpa only [List.flatMap_map, nst, σi] using hx.inp
  · have h2 := (imu_table (M := M)
      ((dfN (x.steps.map nst)).map (kyN (x.init.length + 1)))
      (((x.steps.map nst).map Mach.ld).map (kyN (x.init.length + 1)))
      (by simp [dfN])).1 ⟨_, hx.block ▸ hx.ls⟩
    intro st hst
    obtain ⟨ρ, hρ, e⟩ := List.mem_map.1 (h2 (kyN (x.init.length + 1) (Mach.ld st))
      (List.mem_map.2 ⟨_, List.mem_map.2 ⟨st, hst, rfl⟩, rfl⟩))
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst
    have hb2 : ∀ j, ρ.2 j < 2 ^ (x.init.length + 1) := by
      rcases List.mem_cons.1 hρ with rfl | hρ'
      · exact four_lt (by positivity) (by positivity) (by positivity) (by positivity)
      · obtain ⟨_, hst', rfl⟩ := List.mem_map.1 hρ'
        obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hst'
        exact four_lt (nst_lt hx hs' _) (nst_lt hx hs' _) (nst_lt hx hs' _) (nst_lt hx hs' _)
    rwa [← kyN_inj hb2
      (four_lt (nst_lt hx hs _) (nst_lt hx hs _) (nst_lt hx hs _) (nst_lt hx hs _)) e]

private theorem unit_list {l l' : List Unit} (h : l.length = l'.length) : l = l' :=
  List.ext_getElem h fun _ _ _ => rfl

/-- A matched run is uniquely determined by its decoded machine trace `x.steps.map nst`. -/
theorem MX.unique [Fintype K] [DecidableEq K] {P : Mach A M K} {x x' : XP P}
    {bits : List Bool} (hx : MX x bits) (hx' : MX x' bits)
    (e : x.steps.map nst = x'.steps.map nst) : x = x' := by
  have hT : x.steps.length = x'.steps.length := by simpa using congrArg List.length e
  have hL : x.init.length = x'.init.length :=
    Nat.succ.inj ((hx.size_eq.symm.trans (congrArg (fun n => Nat.size (n + 1)) hT)).trans
      hx'.size_eq)
  have e1 : x.init = x'.init := unit_list hL
  have e3 : x.steps = x'.steps :=
    List.ext_getElem hT fun i h1 h2 => by
      have h3 : nst x.steps[i] = nst x'.steps[i] := by simpa [h1, h2] using congrArg (·[i]?) e
      refine Prod.ext (Prod.mk.inj h3).1 ?_
      rw [← unb_bv (x.steps[i]).2, ← unb_bv (x'.steps[i]).2,
        hx.len _ (List.getElem_mem h1), hx'.len _ (List.getElem_mem h2), hL]
      exact congrArg (unb _) (Prod.mk.inj h3).2
  have e2 : x.counter = x'.counter :=
    (List.map_injective_iff (f := cn)).2
      (fun ⟨u, k⟩ ⟨u', k'⟩ h =>
        let ⟨a1, a2⟩ := carry_cut_unique h
        Prod.ext a1 (unit_list a2))
      (by rw [hx.fr, hx'.fr, e3])
  have e4r : x.finalRegs = x'.finalRegs := cols_ext fun i => by
    simpa [e1, e3, hx'.rg i] using (hx.rg i).symm
  have e4c : x.finalCounter = x'.finalCounter := by
    simpa [e1, e2, hx'.cp] using hx.cp.symm
  have e6 : x.sort = x'.sort :=
    imu_unique (lsN_ne _ _) (e1 ▸ e3 ▸ hx.block ▸ hx.ls) (hx'.block ▸ hx'.ls)
  exact XP.ext e1 e2 e3 e4r e4c (by rw [hx.lk, hx'.lk, lks, lks, e3]) e6

end Trace

end Cslib.Circuits.Arithmetic.Separation.Uni
