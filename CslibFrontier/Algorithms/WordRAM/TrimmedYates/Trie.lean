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
  wram_exec [trieInit, hz, ho, hf]
  refine ⟨?_, ?_, TrieRep.fresh_node d hpos ?_ ?_,
    fun a ⟨ha0, ha1⟩ => by wram_simp [ha0, ha1],
    fun i ⟨hi1, hi2⟩ => by wram_simp [hi1, hi2]⟩
  all_goals wram_simp

/-- The empty trie at address `0` represents only the zero function. -/
private theorem TrieRep.fn_eq_zero {mem : ℕ → ℕ} {k : ℕ} {S : Set ℕ} {fn : ℕ → ℕ}
    (h : TrieRep mem k 0 S fn) (m : ℕ) : fn m = 0 := by
  cases k <;> dsimp only [TrieRep] at h <;> rcases h with ⟨-, -, h⟩ | ⟨h, -⟩
  all_goals first | exact h m | omega

/-- `TrieRep` at an allocated node of depth `k + 1`, with its children named by a key bit `bit`:
the child at `node + bit` holds the keys with low bit `bit`, the one at `node + (1 - bit)` the
others. -/
private theorem trieRep_succ_iff {mem : ℕ → ℕ} {k node bit : ℕ} {S : Set ℕ} {fn : ℕ → ℕ}
    (hpos : 0 < node) (hbit : bit < 2) :
    TrieRep mem (k + 1) node S fn ↔ ∃ Sc So fnc fno,
      Disjoint ({node, node + 1} : Set ℕ) (Sc ∪ So) ∧ Disjoint Sc So ∧
      S = {node, node + 1} ∪ Sc ∪ So ∧
      TrieRep mem k (mem (node + bit)) Sc fnc ∧ TrieRep mem k (mem (node + (1 - bit))) So fno ∧
      ∀ m, fn m = if m % 2 = bit then fnc (m / 2) else fno (m / 2) := by
  simp only [TrieRep, Nat.pos_iff_ne_zero.1 hpos, hpos, false_and, false_or, true_and]
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  · rfl
  · constructor <;> rintro ⟨S₀, S₁, fn₀, fn₁, hd, hd', rfl, h₀, h₁, hfn⟩ <;>
      refine ⟨S₁, S₀, fn₁, fn₀, by rwa [Set.union_comm], hd'.symm, Set.union_right_comm _ _ _,
        by simpa using h₁, by simpa using h₀, fun m => ?_⟩ <;>
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h, hfn m]

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
    have hrem_shr : Fits w (s.regs rTrieRem >>> 1) :=
      hfrem.of_le (Nat.shiftRight_eq_div_pow .. ▸ Nat.div_le_self _ _)
    have hbit_next : Fits w (s.regs rTrieBit + 1) := hfit_d.of_le (by omega)
    have hsub : d - s.regs rTrieBit = d - (s.regs rTrieBit + 1) + 1 := by omega
    rw [hsub] at hrep
    unfold trieGetStep
    by_cases hcur0 : s.regs rTrieCur = 0
    · rw [hcur0] at hrep
      wram_exec [hsz, hso, hcur0]
      exact ⟨⟨hsz, hso, hsd, hsm, hfrem, ∅, Set.empty_subset _, fun _ => 0,
        by simpa [hcur0] using TrieRep.zero_root x.mem _, hval.trans (hrep.fn_eq_zero _)⟩, rfl⟩
    · obtain ⟨Sc, So, fnc, fno, -, -, rfl, htc, -, hfn⟩ :=
        (trieRep_succ_iff (Nat.pos_of_ne_zero hcur0) (Nat.mod_lt _ two_pos)).1 hrep
      have hcur1 := (hS (by simp : s.regs rTrieCur + 1 ∈ _)).2
      have haddr_fit : Fits w (s.regs rTrieCur + (s.regs rTrieRem &&& 1)) :=
        hfit_bound.of_le (by rw [Nat.and_one_is_mod]; omega)
      wram_exec [hsz, hso, hcur0]
      refine ⟨⟨by wram_simp [hsz], by wram_simp [hso], by wram_simp [hsd], hsm,
        by wram_simp [hrem_shr], Sc, fun a ha => hS (by simp [ha]), fnc, ?_, ?_⟩, by wram_simp⟩
      · wram_simp [hsm, Nat.and_one_is_mod]; exact htc
      · wram_simp [hval, hfn, Nat.shiftRight_one]
  let x₀ := ((x.set rTrieCur root).set rTrieRem key).set rTrieBit 0
  have hinit : ExecWithin (B := .standard) w
      (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ]) x x₀ 3 := by
    wram_exec [hr, hk]
  obtain ⟨S_init, hS_init, hrep_init⟩ := htrie
  have hx₀ : P (x₀.regs rTrieBit) x₀ :=
    ⟨by simp [x₀, hz], by simp [x₀, ho], by simp [x₀, hd], rfl,
      by simpa [x₀] using hfit_key, S_init, hS_init, fn,
      by simpa [x₀] using hrep_init, by simp [x₀]⟩
  obtain ⟨u, hloop, huP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
    (by simp [x₀]) hx₀
  obtain ⟨huz, _, _, hum, _, _, _, subFn, hrep_end, hval_end⟩ := huP
  simp only [Nat.sub_self, TrieRep] at hrep_end
  obtain ⟨y, hfy, hyval, hymem⟩ : ∃ y, ExecWithin (B := .standard) w
      (ram[ if rTrieCur = rZero then [ rTrieVal ← #0 ] else [ rTrieVal ← *rTrieCur ] ]) u y 3 ∧
      y.regs rTrieVal = fn key ∧ y.mem = u.mem := by
    rcases hrep_end with ⟨hc0, _, hf0⟩ | ⟨hpos, _, hmem_eq⟩
    · wram_exec [huz, hc0]
      wram_simp [hval_end, hf0]
    · wram_exec [huz, Nat.pos_iff_ne_zero.mp hpos]
      wram_simp [hval_end, hmem_eq, hum]
  have htot : ExecWithin w trieGet x y (9 * d + 8) :=
    (hinit.seq (hloop.seq hfy)).mono (by simp [x₀]; omega)
  exact ⟨y, htot, hyval, hymem.trans hum, fun i hi => htot.regs_eq (trieGet_preserves i hi)⟩

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
  rw [pow_succ', Nat.ext_div_mod_iff 2 (a % _) (b % _)]
  have hdvd : 2 ∣ 2 * 2 ^ k := dvd_mul_right 2 (2 ^ k)
  simp only [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd, and_comm]

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
    obtain ⟨y, hy, hyfree, hymem⟩ : ∃ y, ExecWithin (B := .standard) w
        (ram[ *rTrieCur ← rTrieVal ]) s y 1 ∧
        y.regs Reg.free = free ∧ y.mem = Function.update s.mem cur val := by
      wram_exec [hcur, hval]
      wram_simp [hfree]
    refine ⟨y, {cur, cur + 1}, free, (hexit.within.seq hy).mono (by omega), hyfree,
      le_rfl, by omega, Set.subset_union_left, fun a ha => ?_,
      Or.inr ⟨hcur_pos, rfl, fun m => by simp [hymem, Nat.mod_one]⟩⟩
    rw [hymem, Function.update_of_ne (by rintro rfl; simp at ha)]
  | succ k ih =>
    intro w lo d b cur rem val free S fn s hk hle hz ho hd hb hcur hrem hval hfree
      hlo hfree_lo hcur_pos hS hrep hfit_free hfit_d hfit_rem
    obtain ⟨Sc, So, fnc, fno, hdisj, hdisj', rfl, htc, hto, hfn⟩ :=
      (trieRep_succ_iff hcur_pos (Nat.mod_lt rem two_pos)).1 hrep
    -- The node's cells `N = {cur, cur + 1}`, holding the child slot `cur + rem % 2` and the other
    -- slot, and both subtrees lie below `free`; the subtrees avoid `N`.
    have hlt : ∀ a ∈ ({cur, cur + 1} : Set ℕ) ∪ Sc ∪ So, a < free := fun a ha => (hS ha).2
    have hN : ∀ a ∈ ({cur, cur + 1} : Set ℕ), a ∉ Sc ∪ So :=
      fun _ ha => Set.disjoint_left.1 hdisj ha
    have hslot : cur + rem % 2 ∈ ({cur, cur + 1} : Set ℕ) := by
      rcases Nat.mod_two_eq_zero_or_one rem with h | h <;> simp [h]
    have hother : cur + (1 - rem % 2) ∈ ({cur, cur + 1} : Set ℕ) := by
      rcases Nat.mod_two_eq_zero_or_one rem with h | h <;> simp [h]
    have hcur1 : cur + 1 < free := hlt _ (by simp)
    have hrem_and_fit : Fits w (rem &&& 1) := hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hrem_shr_fit : Fits w (rem >>> 1) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact hfit_rem.of_le (Nat.div_le_self _ _)
    have haddr_fit : Fits w (cur + (rem &&& 1)) :=
      hfit_free.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hb1_fit : Fits w (b + 1) := hfit_d.of_le (by omega)
    have hfree2_fit : Fits w (free + 2) := hfit_free.of_le (by omega)
    -- One step descends to the child at the slot, allocating a fresh zeroed node if it is absent.
    obtain ⟨u, hstep, huz, huo, hud, hub, hurem, huval, hfree₁, hfree₁', hupos, huslot, huframe,
        S_c, hSc_sub, htu⟩ : ∃ u, ExecWithin w trieSetStep s u 12 ∧
        u.regs rZero = 0 ∧ u.regs rOne = 1 ∧ u.regs Reg.dim = d ∧ u.regs rTrieBit = b + 1 ∧
        u.regs rTrieRem = rem / 2 ∧ u.regs rTrieVal = val ∧
        free ≤ u.regs Reg.free ∧ u.regs Reg.free ≤ free + 2 ∧ 0 < u.regs rTrieCur ∧
        u.mem (cur + rem % 2) = u.regs rTrieCur ∧
        (∀ a, a ≠ cur + rem % 2 → a ∉ Set.Ico free (u.regs Reg.free) → u.mem a = s.mem a) ∧
        ∃ S_c ⊆ Sc ∪ Set.Ico free (u.regs Reg.free), TrieRep u.mem k (u.regs rTrieCur) S_c fnc := by
      wram_exec [trieSetStep, hz, ho, hcur, hrem, hfree]
      · rw [Nat.and_one_is_mod] at hc
        rw [hc] at htc
        obtain rfl : fnc = fun _ => 0 := funext htc.fn_eq_zero
        wram_simp [hz, ho, hd, hb, hval, Nat.and_one_is_mod, Nat.shiftRight_one]
        refine ⟨by omega, le_rfl, by omega, fun a h1 h2 => ?_, {free, free + 1}, fun a ha => ?_,
          TrieRep.fresh_node k (by omega) (by simp) (by simp)⟩
        · simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at h2
          wram_simp
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          exact Or.inr ⟨by omega, by omega⟩
      · wram_simp [hz, ho, hd, hb, hval, Nat.and_one_is_mod, Nat.shiftRight_one]
        exact ⟨by omega, by omega, Nat.pos_of_ne_zero (by rwa [Nat.and_one_is_mod] at hc),
          fun _ _ _ => trivial, Sc, Set.subset_union_left, htc⟩
    have hSc_lo : S_c ⊆ Set.Ico lo (u.regs Reg.free) := fun a ha => by
      rcases hSc_sub ha with ha | ha
      · exact ⟨(hS (by simp [ha])).1, (hlt a (by simp [ha])).trans_le hfree₁⟩
      · exact ⟨hfree_lo.trans ha.1, ha.2⟩
    obtain ⟨y, S_c', free₂, hrec, hyfree, hfree₂, hfree₂', hSc'_sub, hyframe, htc'⟩ :=
      ih u (by omega) (by omega) huz huo hud hub rfl hurem huval rfl hlo (by omega) hupos hSc_lo
        htu (hfit_free.of_le (by omega)) hfit_d (hfit_rem.of_le (Nat.div_le_self _ _))
    have hbd : b < d := by omega
    have hcond : (Cond.lt rTrieBit Reg.dim).Holds s := by
      simp [Cond.holds_lt, hb, hd, hbd]
    obtain ⟨n₁, hn₁, hex₁⟩ := hstep
    obtain ⟨n₂, hn₂, hex₂⟩ := hrec
    cases hex₂ with
    | seq hex_loop hex_store =>
    -- The rebuilt child's cells are old child cells or fresh; below `free`, `y` agrees with `u`
    -- off the old child cells, and with `s` off the slot too.
    have hSc' : ∀ a ∈ S_c', a ∈ Sc ∨ a ∈ Set.Ico free free₂ := fun a ha => by
      rcases hSc'_sub ha with ha | ha
      · rcases hSc_sub ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr ⟨ha.1, ha.2.trans_le hfree₂⟩
      · exact Or.inr ⟨hfree₁.trans ha.1, ha.2⟩
    have hyu : ∀ a, a < free → a ∉ Sc → y.mem a = u.mem a := fun a ha haS => hyframe a <| by
      rintro (h | h)
      · rcases hSc_sub h with h | h
        exacts [haS h, absurd h.1 (by omega)]
      · exact absurd h.1 (by omega)
    have hys : ∀ a, a < free → a ∉ Sc → a ≠ cur + rem % 2 → y.mem a = s.mem a :=
      fun a ha haS hne => (hyu a ha haS).trans (huframe a hne fun h => absurd h.1 (by omega))
    refine ⟨y, {cur, cur + 1} ∪ S_c' ∪ So, free₂,
      ⟨_, by omega, Exec.seq (Exec.loop_iter hcond hex₁ hex_loop) hex_store⟩, hyfree,
      by omega, by omega, ?_, fun a ha => ?_, ?_⟩
    · rintro a ((ha | ha) | ha)
      · exact Or.inl (Or.inl (Or.inl ha))
      · exact (hSc' a ha).imp (fun h => Or.inl (Or.inr h)) id
      · exact Or.inl (Or.inr ha)
    · have haS : a ∉ Sc := fun h => ha (Or.inl (Or.inl (Or.inr h)))
      have haF : ¬ (free ≤ a ∧ a < free₂) := fun h => ha (Or.inr h)
      refine (hyframe a ?_).trans (huframe a ?_ fun h => haF ⟨h.1, h.2.trans_le hfree₂⟩)
      · rintro (h | h)
        · rcases hSc_sub h with h | h
          exacts [haS h, haF ⟨h.1, h.2.trans_le hfree₂⟩]
        · exact haF ⟨hfree₁.trans h.1, h.2⟩
      · rintro rfl; exact ha (Or.inl (Or.inl (Or.inl hslot)))
    · refine (trieRep_succ_iff hcur_pos (Nat.mod_lt rem two_pos)).2 ⟨S_c', So,
        fun m => if m % 2 ^ k = rem / 2 % 2 ^ k then val else fnc m, fno, ?_, ?_, rfl, ?_, ?_,
        fun m => ?_⟩
      · refine Set.disjoint_left.2 fun a haN ha => ha.elim
          (fun ha => (hSc' a ha).elim (fun h => hN a haN (Or.inl h)) fun h =>
            absurd h.1 (not_le_of_gt (hlt a (Or.inl (Or.inl haN)))))
          (fun ha => hN a haN (Or.inr ha))
      · refine Set.disjoint_left.2 fun a ha ha' => (hSc' a ha).elim
          (fun h => Set.disjoint_left.1 hdisj' h ha') fun h =>
            absurd h.1 (not_le_of_gt (hlt a (Or.inr ha')))
      · rwa [hyu _ (hlt _ (Or.inl (Or.inl hslot))) fun h => hN _ hslot (Or.inl h), huslot]
      · rw [hys _ (hlt _ (Or.inl (Or.inl hother))) (fun h => hN _ hother (Or.inl h)) (by omega)]
        exact hto.congr_mem fun a ha => hys a (hlt a (Or.inr ha)) (Set.disjoint_right.1 hdisj' ha)
          (by rintro rfl; exact hN _ hslot (Or.inr ha))
      · simp only [mod_two_pow_succ_eq_iff, hfn m]
        by_cases h : m % 2 = rem % 2 <;> simp [h]

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
  refine ⟨y, S', free', htot, hyfree, hle1, hle2,
    fun a ha => (hS' ha).elim (fun h => ⟨(hS h).1, (hS h).2.trans_le hle1⟩)
      fun h => ⟨hfree_lo.trans h.1, h.2⟩,
    fun a ha => hyframe a ?_, Nat.mod_eq_of_lt hkey_lt ▸ hyrep,
    fun i hi => htot.regs_eq (trieSet_preserves i hi)⟩
  rintro (h | ⟨h1, h2⟩)
  · obtain ⟨h1, h2⟩ := hS h; omega
  · omega

end Cslib.Algorithms.WordRAM.TrimmedYates
