/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.TrieRep
-- `import all` bridges unexposed `HoldsTrie` to `TrieRep` via `HoldsTrie.iff_exists_trieRep`.
import all CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Depth-`d` binary trie operations in flat word memory

Allocation (`trieInit`), `O(d + 1)` lookup (`trieGet`), and `O(d + 1)` lazy-allocating point update
(`trieSet`) for depth-`d` binary tries stored in flat Word-RAM memory without assuming pre-zeroed
scratch space.

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.trieInit`, `trieGet`, `trieSet`: fresh root allocation,
  bit-indexed lookup, and lazy-allocating point update on depth-`d` binary tries.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_trieInit`, `exec_trieGet`, `exec_trieSet`:
  `ExecWithin` specifications with explicit bump-pointer footprints and register/memory frames.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Cslib.WordRAM

/-- Unfold `HoldsTrie` into an owned cell footprint `S ⊆ Set.Ico 1 bound` with `TrieRep`. -/
theorem HoldsTrie.iff_exists_trieRep {mem : ℕ → ℕ} {bound d root : ℕ} {fn : ℕ → ℕ} :
    HoldsTrie mem bound d root fn ↔ ∃ S ⊆ Set.Ico 1 bound, TrieRep mem d root S fn := by
  rfl

/-- Allocate a fresh 2-word zeroed trie root at `Reg.free`. -/
def trieInit : Code .standard numRegs := ram[
  rTrieRoot ← Reg.free;
  *Reg.free ← rZero;
  Reg.free ← Reg.free + rOne;
  *Reg.free ← rZero;
  Reg.free ← Reg.free + rOne ]

theorem trieInit_preserves (i : Fin numRegs) :
    i ≠ rTrieRoot ∧ i ≠ Reg.free → trieInit.Preserves i := by
  decide +kernel +revert

theorem exec_trieInit {w d free : ℕ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hf : x.regs Reg.free = free)
    (hpos : 0 < free) (hfit : Fits w (free + 2)) :
    ∃ y, ExecWithin w trieInit x y 5 ∧
      y.regs rTrieRoot = free ∧ y.regs Reg.free = free + 2 ∧
      TrieRep y.mem d free {free, free + 1} (fun _ => 0) ∧
      (∀ a, a ≠ free ∧ a ≠ free + 1 → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieRoot ∧ i ≠ Reg.free → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin w trieInit x y 5 ∧
      y.regs rTrieRoot = free ∧ y.regs Reg.free = free + 2 ∧
      y.mem = Function.update (Function.update x.mem free 0) (free + 1) 0 := by
    unfold trieInit
    wram_exec [hz, ho, hf]
    wram_simp
  obtain ⟨y, he, hroot, hfree, hmem⟩ := hrun
  refine ⟨y, he, hroot, hfree, ?_, ?_, fun i hi => he.regs_eq (trieInit_preserves i hi)⟩
  · apply TrieRep.fresh_node d hpos
    · rw [hmem, Function.update_of_ne (by omega), Function.update_self]
    · rw [hmem, Function.update_self]
  · intro a ⟨ha0, ha1⟩
    rw [hmem, Function.update_of_ne ha1, Function.update_of_ne ha0]

/-- One bit-step of `trieGet`. -/
private def trieGetStep : Code .standard numRegs := ram[
  if rTrieCur = rZero then [
    rTrieBit ← rTrieBit + rOne
  ] else [
    rTrieTmp ← rTrieRem &&& rOne;
    rTrieRem ← rTrieRem >>> rOne;
    rTrieTmp ← rTrieCur + rTrieTmp;
    rTrieCur ← *rTrieTmp;
    rTrieBit ← rTrieBit + rOne
  ] ]

/-- Lookup `rTrieKey` in depth-`Reg.dim` trie `rTrieRoot`, placing result in `rTrieVal`. -/
def trieGet : Code .standard numRegs :=
  .seq (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ])
    (.seq (.loop (.lt rTrieBit Reg.dim) trieGetStep)
      (ram[ if rTrieCur = rZero then [ rTrieVal ← #0 ] else [ rTrieVal ← *rTrieCur ] ]))

theorem trieGet_preserves (i : Fin numRegs) :
    i.val < 18 ∨ 23 ≤ i.val → trieGet.Preserves i := by
  decide +kernel +revert

theorem exec_trieGet {w bound d root key : ℕ} {fn : ℕ → ℕ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hr : x.regs rTrieRoot = root) (hk : x.regs rTrieKey = key)
    (htrie : HoldsTrie x.mem bound d root fn)
    (hfit_bound : Fits w bound) (hfit_d : Fits w d) (hfit_key : Fits w key) :
    ∃ y, ExecWithin w trieGet x y (9 * d + 8) ∧
      y.regs rTrieVal = fn key ∧ y.mem = x.mem ∧
      ∀ i : Fin numRegs, i.val < 18 ∨ 23 ≤ i.val → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin w trieGet x y (9 * d + 8) ∧
      y.regs rTrieVal = fn key ∧ y.mem = x.mem := by
    let P (b : ℕ) (s : Data numRegs) : Prop :=
      s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧ s.mem = x.mem ∧
      Fits w (s.regs rTrieRem) ∧
      ∃ S ⊆ Set.Ico 1 bound, ∃ subFn,
        TrieRep x.mem (d - b) (s.regs rTrieCur) S subFn ∧ fn key = subFn (s.regs rTrieRem)
    have hbody (s : Data numRegs) (hs : P (s.regs rTrieBit) s) (hlt : s.regs rTrieBit < d) :
        ∃ z, ExecWithin w trieGetStep s z 7 ∧ P (s.regs rTrieBit + 1) z ∧
          z.regs rTrieBit = s.regs rTrieBit + 1 := by
      obtain ⟨hsz, hso, hsd, hsm, hfrem, S, hS, subFn, hrep, hval⟩ := hs
      have hrem_and : Fits w (s.regs rTrieRem &&& 1) :=
        hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
      have hrem_shr : Fits w (s.regs rTrieRem >>> 1) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact hfrem.of_le (Nat.div_le_self _ _)
      have hbit_next : Fits w (s.regs rTrieBit + 1) := hfit_d.of_le (by omega)
      have hsplit : d - s.regs rTrieBit = (d - (s.regs rTrieBit + 1)) + 1 := by omega
      rw [hsplit] at hrep
      dsimp only [TrieRep] at hrep
      by_cases hcur0 : s.regs rTrieCur = 0
      · have hfn0 : ∀ m, subFn m = 0 := by
          rcases hrep with ⟨_, _, hf0⟩ | ⟨hp, _⟩
          · exact hf0
          · omega
        have hstep : ∃ z, ExecWithin w trieGetStep s z 7 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs Reg.dim = d ∧ z.mem = s.mem ∧
            z.regs rTrieCur = 0 ∧ z.regs rTrieRem = s.regs rTrieRem ∧
            z.regs rTrieBit = s.regs rTrieBit + 1 := by
          unfold trieGetStep
          wram_exec [hsz, hso, hcur0]
          wram_simp [hsz, hso, hsd, hcur0]
        obtain ⟨z, hz, hzz, hzo, hzd, hzm, hzc, hzr, hzb⟩ := hstep
        refine ⟨z, hz, ⟨hzz, hzo, hzd, hzm.trans hsm, hzr ▸ hfrem,
          ∅, Set.empty_subset _, fun _ => 0, ?_, ?_⟩, hzb⟩
        · rw [hzc]; exact TrieRep.zero_root x.mem _
        · rw [hval, hfn0]
      · rcases hrep with ⟨hc0, _⟩ | ⟨_, S₀, S₁, fn₀, fn₁, _, _, rfl, ht₀, ht₁, hfn⟩
        · exact absurd hc0 hcur0
        have hcur_bound : s.regs rTrieCur + 1 < bound :=
          (hS (by simp : s.regs rTrieCur + 1 ∈ _)).2
        have hbit_le : (s.regs rTrieRem &&& 1) ≤ 1 := by
          rw [Nat.and_one_is_mod]; omega
        have haddr_fit : Fits w (s.regs rTrieCur + (s.regs rTrieRem &&& 1)) :=
          hfit_bound.of_le (by omega)
        have hstep : ∃ z, ExecWithin w trieGetStep s z 7 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs Reg.dim = d ∧ z.mem = s.mem ∧
            z.regs rTrieCur = s.mem (s.regs rTrieCur + (s.regs rTrieRem &&& 1)) ∧
            z.regs rTrieRem = s.regs rTrieRem >>> 1 ∧
            z.regs rTrieBit = s.regs rTrieBit + 1 := by
          unfold trieGetStep
          wram_exec [hsz, hso, hcur0]
          wram_simp [hsz, hso, hsd]
        obtain ⟨z, hz, hzz, hzo, hzd, hzm, hzc, hzr, hzb⟩ := hstep
        rw [hsm, Nat.and_one_is_mod] at hzc
        rw [Nat.shiftRight_eq_div_pow, pow_one] at hzr
        refine ⟨z, hz, ⟨hzz, hzo, hzd, hzm.trans hsm, hzr ▸ hrem_shr, ?_⟩, hzb⟩
        by_cases hmod : s.regs rTrieRem % 2 = 0
        · refine ⟨S₀, fun a ha => hS (by simp [ha]), fn₀, ?_, ?_⟩
          · simpa [hzc, hmod] using ht₀
          · rw [hval, hfn, ite_eq_left hmod, hzr]
        · have hmod1 : s.regs rTrieRem % 2 = 1 := by omega
          refine ⟨S₁, fun a ha => hS (by simp [ha]), fn₁, ?_, ?_⟩
          · simpa [hzc, hmod1] using ht₁
          · rw [hval, hfn, ite_eq_right hmod, hzr]
    let x₀ := ((x.set rTrieCur root).set rTrieRem key).set rTrieBit 0
    have hinit : ExecWithin (B := .standard) w
        (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ]) x x₀ 3 := by
      wram_exec [hr, hk]
    obtain ⟨S_init, hS_init, hrep_init⟩ := htrie
    have hx₀ : P (x₀.regs rTrieBit) x₀ := by
      refine ⟨by simp [x₀, hz], by simp [x₀, ho], by simp [x₀, hd], rfl,
        by simpa [x₀] using hfit_key, S_init, hS_init, fn, ?_, by simp [x₀]⟩
      simpa [x₀] using hrep_init
    obtain ⟨u, hloop, huP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨huz, _, _, hum, _, _, _, subFn, hrep_end, hval_end⟩ := huP
    rw [Nat.sub_self] at hrep_end
    dsimp only [TrieRep] at hrep_end
    have hfin : ∃ y, ExecWithin (B := .standard) w
        (ram[ if rTrieCur = rZero then [ rTrieVal ← #0 ] else [ rTrieVal ← *rTrieCur ] ]) u y 3 ∧
        y.regs rTrieVal = fn key ∧ y.mem = u.mem := by
      rcases hrep_end with ⟨hc0, _, hf0⟩ | ⟨hpos, _, hmem_eq⟩
      · wram_exec [huz, hc0]
        wram_simp [hval_end, hf0]
      · have hne : u.regs rTrieCur ≠ 0 := by omega
        wram_exec [huz, hne]
        wram_simp [hval_end, hmem_eq, hum]
    obtain ⟨y, hfy, hyval, hymem⟩ := hfin
    refine ⟨y, (hinit.seq (hloop.seq hfy)).mono (by simp [x₀]; omega), hyval, hymem.trans hum⟩
  obtain ⟨y, he, hyval, hymem⟩ := hrun
  exact ⟨y, he, hyval, hymem, fun i hi => he.regs_eq (trieGet_preserves i hi)⟩

/-- One bit-step of `trieSet`, allocating a 2-word zeroed child at `Reg.free` if absent. -/
private def trieSetStep : Code .standard numRegs := ram[
  rTrieTmp ← rTrieRem &&& rOne;
  rTrieRem ← rTrieRem >>> rOne;
  rTrieTmp ← rTrieCur + rTrieTmp;
  rTrieCur ← *rTrieTmp;
  if rTrieCur = rZero then [
    rTrieCur ← Reg.free;
    *rTrieTmp ← Reg.free;
    *Reg.free ← rZero;
    Reg.free ← Reg.free + rOne;
    *Reg.free ← rZero;
    Reg.free ← Reg.free + rOne
  ] else [
    rTrieCur ← rTrieCur
  ];
  rTrieBit ← rTrieBit + rOne ]

/-- Set `rTrieKey` to `rTrieVal` in depth-`Reg.dim` trie `rTrieRoot` (`0 < rTrieRoot`). -/
def trieSet : Code .standard numRegs :=
  .seq (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ])
    (.seq (.loop (.lt rTrieBit Reg.dim) trieSetStep)
      (ram[ *rTrieCur ← rTrieVal ]))

theorem trieSet_preserves (i : Fin numRegs) :
    i ≠ Reg.free ∧ (i.val < 19 ∨ 23 ≤ i.val) → trieSet.Preserves i := by
  decide +kernel +revert

private theorem mod_two_pow_succ_eq_iff {a b k : ℕ} :
    a % 2 ^ (k + 1) = b % 2 ^ (k + 1) ↔ a % 2 = b % 2 ∧ (a / 2) % 2 ^ k = (b / 2) % 2 ^ k := by
  rw [pow_succ']
  have hdvd : 2 ∣ 2 * 2 ^ k := dvd_mul_right 2 (2 ^ k)
  constructor
  · intro h
    have h2 : a % 2 = b % 2 := by
      have := congrArg (· % 2) h
      rwa [Nat.mod_mod_of_dvd a hdvd, Nat.mod_mod_of_dvd b hdvd] at this
    refine ⟨h2, ?_⟩
    have ha := Nat.mod_mul_right_div_self a 2 (2 ^ k)
    have hb := Nat.mod_mul_right_div_self b 2 (2 ^ k)
    omega
  · rintro ⟨h2, hdiv⟩
    have ha : a % (2 * 2 ^ k) = a % 2 + 2 * ((a / 2) % 2 ^ k) := by
      have := Nat.div_add_mod (a % (2 * 2 ^ k)) 2
      have hd := Nat.mod_mul_right_div_self a 2 (2 ^ k)
      have hm : (a % (2 * 2 ^ k)) % 2 = a % 2 := Nat.mod_mod_of_dvd a hdvd
      omega
    have hb : b % (2 * 2 ^ k) = b % 2 + 2 * ((b / 2) % 2 ^ k) := by
      have := Nat.div_add_mod (b % (2 * 2 ^ k)) 2
      have hd := Nat.mod_mul_right_div_self b 2 (2 ^ k)
      have hm : (b % (2 * 2 ^ k)) % 2 = b % 2 := Nat.mod_mod_of_dvd b hdvd
      omega
    omega

private theorem exec_trieSetLoop :
    ∀ (k : ℕ) {w lo d b cur rem val free : ℕ} {S : Set ℕ} {fn : ℕ → ℕ} (s : Data numRegs),
      k = d - b → b ≤ d →
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs Reg.dim = d →
      s.regs rTrieBit = b → s.regs rTrieCur = cur → s.regs rTrieRem = rem →
      s.regs rTrieVal = val → s.regs Reg.free = free →
      1 ≤ lo → lo ≤ free → 0 < cur → S ⊆ Set.Ico lo free →
      TrieRep s.mem k cur S fn →
      Fits w (free + 2 * k) → Fits w d → Fits w rem →
      ∃ y S' free',
        ExecWithin w (.seq (.loop (.lt rTrieBit Reg.dim) trieSetStep) (ram[ *rTrieCur ← rTrieVal ]))
          s y (14 * k + 3) ∧
        y.regs Reg.free = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * k ∧
        S' ⊆ S ∪ Set.Ico free free' ∧
        (∀ a, a ∉ S ∪ Set.Ico free free' → y.mem a = s.mem a) ∧
        TrieRep y.mem k cur S' (fun m => if m % 2 ^ k = rem % 2 ^ k then val else fn m) := by
  intro k
  induction k with
  | zero =>
    intro w lo d b cur rem val free S fn s hk hle hz ho hd hb hcur hrem hval hfree
      hlo hfree_lo hcur_pos hS hrep hfit_free hfit_d hfit_rem
    obtain rfl : b = d := by omega
    dsimp only [TrieRep] at hrep
    rcases hrep with ⟨hc0, _⟩ | ⟨_, rfl, _⟩
    · omega
    have hexit : Exec w (.loop (.lt rTrieBit Reg.dim) trieSetStep) s s 2 :=
      Exec.loop_exit (by simp [Cond.holds_lt, hb, hd])
    have hst : ∃ y, ExecWithin (B := .standard) w (ram[ *rTrieCur ← rTrieVal ]) s y 1 ∧
        y.regs Reg.free = free ∧ y.mem = Function.update s.mem cur val := by
      wram_exec [hcur, hval]
      wram_simp [hfree]
    obtain ⟨y, hy, hyfree, hymem⟩ := hst
    refine ⟨y, {cur, cur + 1}, free, (hexit.within.seq hy).mono (by omega), hyfree,
      le_rfl, by omega, Set.subset_union_left, ?_, ?_⟩
    · intro a ha
      rw [hymem, Function.update_of_ne]
      intro hEq; subst hEq; exact ha (by simp)
    · refine Or.inr ⟨hcur_pos, rfl, fun m => ?_⟩
      simp [pow_zero, Nat.mod_one, hymem]
  | succ k ih =>
    intro w lo d b cur rem val free S fn s hk hle hz ho hd hb hcur hrem hval hfree
      hlo hfree_lo hcur_pos hS hrep hfit_free hfit_d hfit_rem
    have hlt_bd : b < d := by omega
    dsimp only [TrieRep] at hrep
    rcases hrep with ⟨hc0, _⟩ | ⟨_, S₀, S₁, fn₀, fn₁, hd_cur, hd_01, hS_eq, ht₀, ht₁, hfn⟩
    · omega
    have hcur_mem : cur ∈ S := by rw [hS_eq]; simp
    have hcur1_mem : cur + 1 ∈ S := by rw [hS_eq]; simp
    have hcur1_lt : cur + 1 < free := (hS hcur1_mem).2
    have hrem_and_fit : Fits w (rem &&& 1) := hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hrem_shr_fit : Fits w (rem >>> 1) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact hfit_rem.of_le (Nat.div_le_self _ _)
    have haddr_fit : Fits w (cur + (rem &&& 1)) :=
      hfit_free.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hb1_fit : Fits w (b + 1) := hfit_d.of_le (by omega)
    have hfree2_fit : Fits w (free + 2) := hfit_free.of_le (by omega)
    let bit := rem % 2
    have hbit01 : bit = 0 ∨ bit = 1 := by dsimp [bit]; omega
    have hbit_eq : rem &&& 1 = bit := Nat.and_one_is_mod rem
    let slot := cur + bit
    have hstep : ∃ u, ExecWithin w trieSetStep s u 12 ∧
        u.regs rZero = 0 ∧ u.regs rOne = 1 ∧ u.regs Reg.dim = d ∧
        u.regs rTrieBit = b + 1 ∧ u.regs rTrieRem = rem / 2 ∧ u.regs rTrieVal = val ∧
        ((s.mem slot = 0 ∧ u.regs rTrieCur = free ∧ u.regs Reg.free = free + 2 ∧
          u.mem = Function.update
            (Function.update (Function.update s.mem slot free) free 0) (free + 1) 0) ∨
         (s.mem slot ≠ 0 ∧ u.regs rTrieCur = s.mem slot ∧
           u.regs Reg.free = free ∧ u.mem = s.mem)) := by
      by_cases hslot0 : s.mem slot = 0
      · have hload : s.mem (cur + (rem &&& 1)) = 0 := by rwa [hbit_eq]
        unfold trieSetStep
        wram_exec [hz, ho, hcur, hrem, hfree, hload]
        refine ⟨hz, ho, hd, ?_, ?_, hval, Or.inl ⟨hslot0, ?_, ?_, ?_⟩⟩
        · wram_simp [hb]
        · wram_simp; rw [Nat.shiftRight_eq_div_pow, pow_one]
        · wram_simp
        · wram_simp
        · wram_simp [hbit_eq]; rfl
      · have hload : s.mem (cur + (rem &&& 1)) ≠ 0 := by rwa [hbit_eq]
        unfold trieSetStep
        wram_exec [hz, ho, hcur, hrem, hfree, hload]
        refine ⟨hz, ho, hd, ?_, ?_, hval, Or.inr ⟨hslot0, ?_, ?_, ?_⟩⟩
        · wram_simp [hb]
        · wram_simp; rw [Nat.shiftRight_eq_div_pow, pow_one]
        · wram_simp [hbit_eq, slot]
        · wram_simp [hfree]
        · wram_simp
    obtain ⟨u, hstep_exec, huz, huo, hud, hub, hurem, huval, hbranch⟩ := hstep
    have hslot_mem_cur : slot ∈ ({cur, cur + 1} : Set ℕ) := by
      rcases hbit01 with hb0 | hb1
      · simp [slot, hb0]
      · simp [slot, hb1]
    have hother_mem_cur : cur + (1 - bit) ∈ ({cur, cur + 1} : Set ℕ) := by
      rcases hbit01 with hb0 | hb1
      · simp [hb0]
      · simp [hb1]
    have hprep : ∃ child free₁ S_c S_o fn_c fn_o,
        u.regs rTrieCur = child ∧ u.regs Reg.free = free₁ ∧
        free ≤ free₁ ∧ free₁ ≤ free + 2 ∧ 0 < child ∧
        u.mem slot = child ∧ u.mem (cur + (1 - bit)) = s.mem (cur + (1 - bit)) ∧
        S_c ⊆ S ∪ Set.Ico free free₁ ∧ S_o ⊆ S ∧
        Disjoint ({cur, cur + 1} : Set ℕ) (S_c ∪ S_o) ∧ Disjoint S_c S_o ∧
        S_c ⊆ Set.Ico lo free₁ ∧
        (∀ a, a ∉ ({slot} : Set ℕ) ∪ Set.Ico free free₁ → u.mem a = s.mem a) ∧
        TrieRep u.mem k child S_c fn_c ∧
        TrieRep u.mem k (u.mem (cur + (1 - bit))) S_o fn_o ∧
        (bit = 0 → fn_c = fn₀ ∧ fn_o = fn₁) ∧
        (bit = 1 → fn_c = fn₁ ∧ fn_o = fn₀) := by
      rcases hbranch with ⟨hslot0, hucur, hufree, humem⟩ | ⟨hslot_ne, hucur, hufree, humem⟩
      · refine ⟨free, free + 2, {free, free + 1}, if bit = 0 then S₁ else S₀,
          fun _ => 0, if bit = 0 then fn₁ else fn₀, hucur, hufree, by omega, le_rfl,
          by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [humem, Function.update_of_ne (by dsimp [slot]; omega),
            Function.update_of_ne (by dsimp [slot]; omega), Function.update_self]
        · rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp [slot]; omega)]
        · intro a ha
          rcases ha with rfl | ha1
          · exact Or.inr ⟨le_rfl, by omega⟩
          · have : a = free + 1 := by simpa using ha1
            subst this; exact Or.inr ⟨by omega, by omega⟩
        · intro a ha
          rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · rw [Set.disjoint_left]
          intro a ha hso
          have ha_lt : a < free := by
            rcases ha with rfl | ha1
            · omega
            · have : a = cur + 1 := by simpa using ha1
              omega
          rcases hso with hsc | hso
          · rcases hsc with rfl | hsc1
            · omega
            · have : a = free + 1 := by simpa using hsc1
              omega
          · have h01 : a ∈ S₀ ∪ S₁ := by
              rcases hbit01 with hb0 | hb1
              · simp only [hb0, ↓reduceIte] at hso; exact Or.inr hso
              · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at hso; exact Or.inl hso
            exact Set.disjoint_left.mp hd_cur ha h01
        · rw [Set.disjoint_left]
          intro a ha hso
          have ha_ge : free ≤ a := by
            rcases ha with rfl | ha1
            · exact le_rfl
            · have : a = free + 1 := by simpa using ha1
              omega
          have haS : a ∈ S := by
            rw [hS_eq]
            rcases hbit01 with hb0 | hb1
            · simp only [hb0, ↓reduceIte] at hso; simp [hso]
            · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at hso; simp [hso]
          have := (hS haS).2
          omega
        · intro a ha
          rcases ha with rfl | ha1
          · exact ⟨by omega, by omega⟩
          · have : a = free + 1 := by simpa using ha1
            subst this; exact ⟨by omega, by omega⟩
        · intro a ha
          rw [humem, Function.update_of_ne (by intro h; exact ha (Or.inr ⟨by omega, by omega⟩)),
            Function.update_of_ne (by intro h; exact ha (Or.inr ⟨by omega, by omega⟩)),
            Function.update_of_ne (by intro h; exact ha (Or.inl (by simp [h])))]
        · apply TrieRep.fresh_node k (by omega)
          · rw [humem, Function.update_of_ne (by omega), Function.update_self]
          · rw [humem, Function.update_self]
        · have hu_other : u.mem (cur + (1 - bit)) = s.mem (cur + (1 - bit)) := by
            rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp [slot]; omega)]
          rw [hu_other]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte, Nat.sub_zero]
            refine ht₁.congr_mem fun a ha => ?_
            have ha_lt : a < free := (hS (by rw [hS_eq]; simp [ha])).2
            have ha_ne : a ≠ slot := fun h =>
              Set.disjoint_left.mp hd_cur (h ▸ hslot_mem_cur) (Or.inr ha)
            rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne ha_ne]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte, Nat.sub_self, Nat.add_zero]
            refine ht₀.congr_mem fun a ha => ?_
            have ha_lt : a < free := (hS (by rw [hS_eq]; simp [ha])).2
            have ha_ne : a ≠ slot := fun h =>
              Set.disjoint_left.mp hd_cur (h ▸ hslot_mem_cur) (Or.inl ha)
            rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne ha_ne]
        · intro hb0
          have hm0 : s.mem cur = 0 := by simpa [slot, hb0] using hslot0
          rw [hm0] at ht₀
          have hfn0_zero : fn₀ = fun _ => 0 := by
            funext m
            cases k <;> {
              dsimp only [TrieRep] at ht₀
              rcases ht₀ with ⟨_, _, hf⟩ | ⟨hp, _⟩
              · exact hf m
              · omega }
          exact ⟨hfn0_zero.symm, by simp [hb0]⟩
        · intro hb1
          have hm1 : s.mem (cur + 1) = 0 := by simpa [slot, hb1] using hslot0
          rw [hm1] at ht₁
          have hfn1_zero : fn₁ = fun _ => 0 := by
            funext m
            cases k <;> {
              dsimp only [TrieRep] at ht₁
              rcases ht₁ with ⟨_, _, hf⟩ | ⟨hp, _⟩
              · exact hf m
              · omega }
          exact ⟨hfn1_zero.symm, by simp [hb1]⟩
      · refine ⟨s.mem slot, free, if bit = 0 then S₀ else S₁, if bit = 0 then S₁ else S₀,
          if bit = 0 then fn₀ else fn₁, if bit = 0 then fn₁ else fn₀,
          hucur, hufree, le_rfl, by omega, by omega, by rw [humem], by rw [humem],
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro a ha
          left; rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · intro a ha
          rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte]; exact hd_cur
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte, Set.union_comm]; exact hd_cur
        · rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte]; exact hd_01
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte]; exact hd_01.symm
        · intro a ha
          refine hS ?_
          rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · intro a _; rw [humem]
        · rw [humem]
          rcases hbit01 with hb0 | hb1
          · simpa [slot, hb0] using ht₀
          · simpa [slot, hb1] using ht₁
        · rw [humem]
          rcases hbit01 with hb0 | hb1
          · simpa [hb0] using ht₁
          · simpa [hb1] using ht₀
        · intro hb0; simp [hb0]
        · intro hb1; simp [hb1]
    obtain ⟨child, free₁, S_c, S_o, fn_c, fn_o, hucur, hufree, hfree_le1, hfree1_le, hchild_pos,
      humem_slot, _, hSc_sub, hSo_sub, hdisj_cur, hdisj_co, hSc_ico, hu_frame,
      ht_c, ht_o, hbit0_fn, hbit1_fn⟩ := hprep
    obtain ⟨y, S_c', free₂, hrec_exec, hyfree, hfree12, hfree2_le, hSc'_sub, hy_frame, ht_c'⟩ :=
      ih u (by omega) (by omega) huz huo hud hub hucur hurem huval hufree hlo
        (hfree_lo.trans hfree_le1) hchild_pos hSc_ico ht_c
        (hfit_free.of_le (by omega)) hfit_d (hfit_rem.of_le (Nat.div_le_self _ _))
    have hcond : (Cond.lt rTrieBit Reg.dim).Holds s := by simp [Cond.holds_lt, hb, hd, hlt_bd]
    obtain ⟨n_step, hn_step, hex_step⟩ := hstep_exec
    obtain ⟨n_rec, hn_rec, hex_rec⟩ := hrec_exec
    cases hex_rec with
    | seq hex_loop hex_store =>
      have hex_full : ExecWithin w
          (.seq (.loop (.lt rTrieBit Reg.dim) trieSetStep) (ram[ *rTrieCur ← rTrieVal ])) s y
          (14 * (k + 1) + 3) :=
        ⟨_, by omega, Exec.seq (Exec.loop_iter hcond hex_step hex_loop) hex_store⟩
      have hdisj_cur' : Disjoint ({cur, cur + 1} : Set ℕ) (S_c' ∪ S_o) := by
        rw [Set.disjoint_left]
        intro a ha hso
        rcases hso with hsc' | hso
        · rcases hSc'_sub hsc' with hsc | hnew
          · exact Set.disjoint_left.mp hdisj_cur ha (Or.inl hsc)
          · have ha_lt : a < free := by
              rcases ha with rfl | ha1
              · omega
              · have : a = cur + 1 := by simpa using ha1
                omega
            have := hnew.1; omega
        · exact Set.disjoint_left.mp hdisj_cur ha (Or.inr hso)
      have hdisj_co' : Disjoint S_c' S_o := by
        rw [Set.disjoint_left]
        intro a hsc' hso
        rcases hSc'_sub hsc' with hsc | hnew
        · exact Set.disjoint_left.mp hdisj_co hsc hso
        · have ha_lt : a < free := (hS (hSo_sub hso)).2
          have := hnew.1; omega
      have hy_cur_slot : y.mem slot = child := by
        rw [hy_frame slot (by
          intro h; rcases h with hsc | hnew
          · exact Set.disjoint_left.mp hdisj_cur hslot_mem_cur (Or.inl hsc)
          · have : slot < free := by dsimp [slot, bit]; omega
            have := hnew.1; omega), humem_slot]
      have hy_cur_other : y.mem (cur + (1 - bit)) = u.mem (cur + (1 - bit)) := by
        apply hy_frame
        intro h; rcases h with hsc | hnew
        · exact Set.disjoint_left.mp hdisj_cur hother_mem_cur (Or.inl hsc)
        · have : cur + (1 - bit) < free := by dsimp [bit]; omega
          have := hnew.1; omega
      have ht_o' : TrieRep y.mem k (y.mem (cur + (1 - bit))) S_o fn_o := by
        rw [hy_cur_other]
        exact ht_o.congr_mem fun a ha => hy_frame a fun h => by
          rcases h with hsc | hnew
          · exact Set.disjoint_left.mp hdisj_co hsc ha
          · have := (hS (hSo_sub ha)).2; have := hnew.1; omega
      refine ⟨y, {cur, cur + 1} ∪ (if bit = 0 then S_c' else S_o) ∪ (if bit = 0 then S_o else S_c'),
        free₂, hex_full, hyfree, hfree_le1.trans hfree12, by omega, ?_, ?_, ?_⟩
      · intro a ha
        have hsub_c' : S_c' ⊆ S ∪ Set.Ico free free₂ := fun x hx => by
          rcases hSc'_sub hx with hxc | hnew
          · rcases hSc_sub hxc with hxs | hnew0
            · exact Or.inl hxs
            · exact Or.inr ⟨hnew0.1, hnew0.2.trans_le hfree12⟩
          · exact Or.inr ⟨hfree_le1.trans hnew.1, hnew.2⟩
        rcases hbit01 with hb0 | hb1
        · simp only [hb0, ↓reduceIte] at ha
          rcases ha with (ha_cur | ha_c) | ha_o
          · exact Or.inl (by rw [hS_eq]; simp [ha_cur])
          · exact hsub_c' ha_c
          · exact Or.inl (hSo_sub ha_o)
        · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha
          rcases ha with (ha_cur | ha_o) | ha_c
          · exact Or.inl (by rw [hS_eq]; simp [ha_cur])
          · exact Or.inl (hSo_sub ha_o)
          · exact hsub_c' ha_c
      · intro a ha
        have ha_not_rec : a ∉ S_c ∪ Set.Ico free₁ free₂ := by
          intro h; apply ha
          rcases h with hsc | hnew
          · rcases hSc_sub hsc with hxs | hnew0
            · exact Or.inl hxs
            · exact Or.inr ⟨hnew0.1, hnew0.2.trans_le hfree12⟩
          · exact Or.inr ⟨hfree_le1.trans hnew.1, hnew.2⟩
        rw [hy_frame a ha_not_rec]
        apply hu_frame
        intro h; apply ha
        rcases h with hslot | hnew0
        · have : a = slot := by simpa using hslot
          subst this; left; rw [hS_eq]
          exact Or.inl (Or.inl hslot_mem_cur)
        · exact Or.inr ⟨hnew0.1, hnew0.2.trans_le hfree12⟩
      · dsimp only [TrieRep]
        rcases hbit01 with hb0 | hb1
        · obtain ⟨hc_eq, ho_eq⟩ := hbit0_fn hb0
          subst hc_eq; subst ho_eq
          simp only [hb0, ↓reduceIte]
          have hm0 : y.mem cur = child := by simpa [slot, hb0] using hy_cur_slot
          refine Or.inr ⟨hcur_pos, S_c', S_o, _, fn_o, hdisj_cur', hdisj_co', rfl,
            hm0 ▸ ht_c', by simpa [hb0] using ht_o', fun m => ?_⟩
          simp only [mod_two_pow_succ_eq_iff, hfn m]
          have hrem2 : rem % 2 = 0 := hb0
          by_cases hm2 : m % 2 = 0 <;> simp [hm2, hrem2]
        · obtain ⟨hc_eq, ho_eq⟩ := hbit1_fn hb1
          subst hc_eq; subst ho_eq
          simp only [hb1, Nat.reduceEqDiff, ↓reduceIte]
          have hm1 : y.mem (cur + 1) = child := by simpa [slot, hb1] using hy_cur_slot
          refine Or.inr ⟨hcur_pos, S_o, S_c', fn_o, _,
            by simpa [Set.union_comm] using hdisj_cur', hdisj_co'.symm, rfl,
            by simpa [hb1] using ht_o', hm1 ▸ ht_c', fun m => ?_⟩
          simp only [mod_two_pow_succ_eq_iff, hfn m]
          have hrem2 : rem % 2 = 1 := hb1
          by_cases hm2 : m % 2 = 0
          · simp [hm2, hrem2]
          · have hm2' : m % 2 = 1 := by omega
            simp [hm2', hrem2]

theorem exec_trieSet {w lo d root key val free : ℕ} {S : Set ℕ} {fn : ℕ → ℕ}
    (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hr : x.regs rTrieRoot = root) (hk : x.regs rTrieKey = key)
    (hv : x.regs rTrieVal = val) (hfree : x.regs Reg.free = free)
    (hlo : 1 ≤ lo) (hfree_lo : lo ≤ free) (hroot : 0 < root) (hS : S ⊆ Set.Ico lo free)
    (hrep : TrieRep x.mem d root S fn) (hkey_lt : key < 2 ^ d)
    (hfit_free : Fits w (free + 2 * d)) (hfit_d : Fits w d) (hfit_key : Fits w key) :
    ∃ y S' free', ExecWithin w trieSet x y (14 * d + 6) ∧
      y.regs Reg.free = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * d ∧
      S' ⊆ Set.Ico lo free' ∧
      (∀ a, a < lo ∨ free' ≤ a → y.mem a = x.mem a) ∧
      TrieRep y.mem d root S' (fun m => if m % 2 ^ d = key then val else fn m) ∧
      ∀ i : Fin numRegs, i ≠ Reg.free ∧ (i.val < 19 ∨ 23 ≤ i.val) → y.regs i = x.regs i := by
  let x₀ := ((x.set rTrieCur root).set rTrieRem key).set rTrieBit 0
  have hinit : ExecWithin (B := .standard) w
      (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ]) x x₀ 3 := by
    wram_exec [hr, hk]
  obtain ⟨y, S', free', hbody, hyfree, hle1, hle2, hS', hyframe, hyrep⟩ :=
    exec_trieSetLoop d (val := val) (free := free) x₀ (by omega) (Nat.zero_le d)
      (by simp [x₀, hz]) (by simp [x₀, ho]) (by simp [x₀, hd])
      (by simp [x₀]) (by simp [x₀]) (by simp [x₀])
      (by simpa [x₀] using hv) (by simpa [x₀] using hfree)
      hlo hfree_lo hroot hS (by simpa [x₀] using hrep) hfit_free hfit_d hfit_key
  have htot : ExecWithin w trieSet x y (14 * d + 6) := (hinit.seq hbody).mono (by omega)
  rw [Nat.mod_eq_of_lt hkey_lt] at hyrep
  refine ⟨y, S', free', htot, hyfree, hle1, hle2, ?_, ?_, hyrep,
    fun i hi => htot.regs_eq (trieSet_preserves i hi)⟩
  · intro a ha
    rcases hS' ha with haS | haNew
    · exact ⟨(hS haS).1, (hS haS).2.trans_le hle1⟩
    · exact ⟨hfree_lo.trans haNew.1, haNew.2⟩
  · intro a ha
    have hnot : a ∉ S ∪ Set.Ico free free' := by
      intro h; rcases h with haS | haNew
      · have h1 := (hS haS).1; have h2 := (hS haS).2
        rcases ha with ha1 | ha2 <;> omega
      · have h1 := haNew.1; have h2 := haNew.2
        rcases ha with ha1 | ha2 <;> omega
    exact hyframe a hnot

end Cslib.Algorithms.WordRAM.TrimmedYates
