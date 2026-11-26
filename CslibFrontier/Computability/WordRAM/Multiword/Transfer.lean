/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Workspace
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Checked transfers between scalar words and digit lists

Register lists and supplied constants determine the unrolled standard-basis code. Digits are
little endian in the half-word radix. Registers zero through three are reserved workspace.

## Main definitions

* `Cslib.WordRAM.Multiword.Transfer.copy`: copy disjoint equal-length register lists.
* `Cslib.WordRAM.Multiword.Transfer.constants`: install a supplied list of constants.
* `Cslib.WordRAM.Multiword.Transfer.accumulate`, `Cslib.WordRAM.Multiword.Transfer.assemble`:
  Horner accumulation and scalar reconstruction from digit registers.
* `Cslib.WordRAM.Multiword.Transfer.extract`, `Cslib.WordRAM.Multiword.Transfer.split`: digit
  extraction and splitting of a physical scalar into digit registers.

## Main results

* `Cslib.WordRAM.Multiword.Transfer.exec_copy`: exact copying and register preservation.
* `Cslib.WordRAM.Multiword.Transfer.exec_constants`: exact installation of bounded constants.
* `Cslib.WordRAM.Multiword.Transfer.exec_assemble`: reconstruction when the scalar fits.
* `Cslib.WordRAM.Multiword.Transfer.exec_split`: exact conversion with sufficient capacity.
* `Cslib.WordRAM.Multiword.Transfer.exec_split_eighteen`: exact eighteen-digit conversion.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Transfer

open Workspace

variable {r : ℕ}

/-- Copy one register per instruction, with a final workspace self-copy. -/
def copy : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, d :: ds => .seq (.op (.copy d a)) (copy as ds)
  | _, _ => .op (.copy carry carry)

/-- Exact width-independent code size. -/
theorem size_copy (as ds : List (Fin (r + 4))) (hlen : as.length = ds.length) :
    (copy as ds).size = ds.length + 1 := by
  induction as generalizing ds with
  | nil => cases ds <;> simp_all [copy]
  | cons a as ih => cases ds <;> simp_all [copy, Code.size, Nat.add_comm]

/-- Copying preserves the exact digit sequence, memory, and every register outside the outputs.
Source registers need not be distinct. -/
theorem exec_copy {w : ℕ} (as ds : List (Fin (r + 4)))
    (hlen : as.length = ds.length) (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) :
    ∃ y, Exec w (copy as ds) x y (ds.length + 1) ∧
      ds.map y.regs = as.map x.regs ∧ Frame x y ds ∧
      ∀ i ∉ ds, y.regs i = x.regs i := by
  induction as generalizing ds x with
  | nil =>
    cases ds with
    | cons => simp_all
    | nil =>
      exact ⟨x.set carry (x.regs carry), Exec.copy, rfl,
        frame_set_carry x (x.regs carry) [], fun i _ => by simp⟩
  | cons a as ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hlen' : as.length = ds.length := by simpa using hlen
      have hdis' : List.Disjoint ds as :=
        fun i hi hj => hdis (List.mem_cons_of_mem d hi) (List.mem_cons_of_mem a hj)
      let z := x.set d (x.regs a)
      have hz (i : Fin (r + 4)) (hi : i ∈ a :: as) : z.regs i = x.regs i := by
        simp [z, show i ≠ d from fun h => hdis (h ▸ List.mem_cons_self) hi]
      obtain ⟨y, hey, hym, hyf, hyp⟩ := ih ds hlen' (List.nodup_cons.mp hnd).2 hdis' z
      have hp : ∀ i ∉ d :: ds, y.regs i = x.regs i := fun i hi => by
        simp [hyp i (List.not_mem_of_not_mem_cons hi), z, List.ne_of_not_mem_cons hi]
      refine ⟨y, ?_, ?_, ⟨hyf.1, fun i hi _ _ => hp i hi⟩, hp⟩
      · simpa only [copy, List.length_cons, Nat.add_comm 1] using
          (show Exec w (.op (.copy (B := .standard) d a)) x z 1 from Exec.copy).seq hey
      · exact congrArg₂ List.cons (by simp [z, hyp d (List.nodup_cons.mp hnd).1])
          (hym.trans (List.map_congr_left fun i hi => hz i (List.mem_cons_of_mem a hi)))

/-- Exact reconstruction follows from the copied digit sequence, at any radix. -/
theorem value_copy {β : ℕ} {x y : Data (r + 4)} {as ds : List (Fin (r + 4))}
    (h : ds.map y.regs = as.map x.regs) : value β y ds = value β x as := by
  simp only [value, h]

/-- Copying an exact digit sequence preserves its digit bound. -/
theorem bounded_copy {β : ℕ} {x y : Data (r + 4)} {as ds : List (Fin (r + 4))}
    (h : ds.map y.regs = as.map x.regs) (hb : Bounded β x as) : Bounded β y ds := by
  intro i hi
  obtain ⟨j, hj, he⟩ := List.mem_map.mp (h ▸ List.mem_map_of_mem (f := y.regs) hi)
  exact he ▸ hb j hj

/-- Install supplied constants; they may depend on the physical width but not runtime data. -/
def constants : List (Fin (r + 4)) → List ℕ → Code .standard (r + 4)
  | d :: ds, c :: cs => .seq (.op (.const d c)) (constants ds cs)
  | _, _ => .op (.copy carry carry)

/-- Exact width-independent instruction count for supplied constants. -/
theorem size_constants (ds : List (Fin (r + 4))) (cs : List ℕ)
    (hlen : ds.length = cs.length) : (constants ds cs).size = ds.length + 1 := by
  induction ds generalizing cs with
  | nil => cases cs <;> simp_all [constants]
  | cons d ds ih => cases cs <;> simp_all [constants, Code.size]; omega

/-- Constants are checked against the physical width. No initial destination contents matter. -/
theorem exec_constants {w : ℕ} (ds : List (Fin (r + 4))) (cs : List ℕ)
    (hlen : ds.length = cs.length) (hnd : ds.Nodup) (hfit : ∀ c ∈ cs, Fits w c)
    (x : Data (r + 4)) :
    ∃ y, Exec w (constants ds cs) x y (ds.length + 1) ∧
      ds.map y.regs = cs ∧ Frame x y ds ∧ ∀ i ∉ ds, y.regs i = x.regs i := by
  induction ds generalizing cs x with
  | nil =>
    cases cs with
    | cons => simp_all
    | nil =>
      exact ⟨x.set carry (x.regs carry), Exec.copy, rfl,
        frame_set_carry x (x.regs carry) [], fun i _ => by simp⟩
  | cons d ds ih =>
    cases cs with
    | nil => simp_all
    | cons c cs =>
      have hlen' : ds.length = cs.length := by simpa using hlen
      let z := x.set d c
      obtain ⟨y, hey, hym, hyf, hyp⟩ := ih cs hlen' (List.nodup_cons.mp hnd).2
        (fun c hc => hfit c (by simp [hc])) z
      have hp : ∀ i ∉ d :: ds, y.regs i = x.regs i := fun i hi => by
        simp [hyp i (List.not_mem_of_not_mem_cons hi), z, List.ne_of_not_mem_cons hi]
      refine ⟨y, ?_, ?_, ⟨hyf.1, fun i hi _ _ => hp i hi⟩, hp⟩
      · simpa only [constants, List.length_cons, Nat.add_comm 1] using
          (show Exec w (.op (.const (B := .standard) d c)) x z 1 from
            Exec.const (hfit c (by simp))).seq hey
      · exact congrArg₂ List.cons (by simp [z, hyp d (List.nodup_cons.mp hnd).1]) hym

/-- Installing bounded digits gives the requested value in the half-word radix. -/
theorem exec_digits {w : ℕ} (hw : 2 ≤ w) (ds : List (Fin (r + 4))) (cs : List ℕ)
    (hlen : ds.length = cs.length) (hnd : ds.Nodup) (hb : ∀ c ∈ cs, c < radix w)
    (x : Data (r + 4)) :
    ∃ y, Exec w (constants ds cs) x y (ds.length + 1) ∧
      Bounded (radix w) y ds ∧ value (radix w) y ds = Nat.ofDigits (radix w) cs ∧
      Frame x y ds ∧ ∀ i ∉ ds, y.regs i = x.regs i := by
  obtain ⟨y, he, hm, hf, hp⟩ := exec_constants ds cs hlen hnd
    (fun c hc => (hb c hc).trans (radix_fits hw)) x
  exact ⟨y, he, fun i hi => hb _ (hm ▸ List.mem_map_of_mem (f := y.regs) hi),
    by rw [value, hm], hf, hp⟩

/-- Reconstruct by Horner evaluation, high digits first, into workspace register zero. -/
def accumulate : List (Fin (r + 4)) → Code .standard (r + 4)
  | [] => .op (.const total 0)
  | a :: as => .seq (accumulate as)
      (ram[ total ← total * base; total ← total + a ])

/-- Horner evaluation costs two instructions per digit plus initialization. -/
theorem size_accumulate (as : List (Fin (r + 4))) :
    (accumulate as).size = 2 * as.length + 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [accumulate, Code.size, ih, List.length_cons]; omega

private theorem exec_accumulate {w : ℕ} (hw : 2 ≤ w) (as : List (Fin (r + 4)))
    (hin : ∀ i ∈ as, IsDigit i) (x : Data (r + 4)) (hbase : x.regs base = radix w)
    (hfit : Fits w (value (radix w) x as)) :
    ∃ y, Exec w (accumulate as) x y (2 * as.length + 1) ∧
      y.regs total = value (radix w) x as ∧ y.mem = x.mem ∧
      ∀ i, i ≠ total → y.regs i = x.regs i := by
  induction as generalizing x with
  | nil =>
    refine WP.Exact.exists_exec ?_
    unfold accumulate
    wram_exec [List.length_nil]
    exact ⟨by simp [value], rfl, fun _ _ => by wram_simp⟩
  | cons a as ih =>
    have hv : value (radix w) x as ≤ value (radix w) x (a :: as) := by
      rw [value_cons]
      exact (Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt (one_lt_radix hw))).trans
        (Nat.le_add_left _ _)
    have hat := (digit_ne (hin a List.mem_cons_self)).1
    refine WP.Exact.exists_exec ?_
    unfold accumulate
    wram_call (ih (fun i hi => hin i (List.mem_cons_of_mem a hi)) x hbase (hfit.of_le hv))
      with z ⟨hzv, hzm, hzp⟩
    have hzb : z.regs base = radix w := (hzp base (by simp [base, total])).trans hbase
    have hza : z.regs a = x.regs a := hzp a hat
    have hs : Fits w (value (radix w) x as * radix w + x.regs a) := by
      simpa only [value_cons, Nat.add_comm, Nat.mul_comm] using hfit
    wram_exec [hzv, hzb, hza, hs]
    refine ⟨by simp only [List.length_cons]; omega, ?_, hzm,
      fun i hi => by wram_simp [hzp i hi]⟩
    wram_simp
    rw [value_cons]
    ring

/-- Initialize the radix, reconstruct, and copy to the physical destination register. -/
def assemble (as : List (Fin (r + 4))) (d : Fin (r + 4)) : Code .standard (r + 4) :=
  .seq Workspace.setup (.seq (accumulate as) (.op (.copy d total)))

/-- Assembly has a linear instruction count independent of the physical width. -/
theorem size_assemble (as : List (Fin (r + 4))) (d : Fin (r + 4)) :
    (assemble as d).size = 2 * as.length + 8 := by
  simp only [assemble, Code.size, Workspace.setup, size_accumulate]; omega

/-- Reconstruction is checked at the original physical width. All intermediate Horner values
fit because the nonnegative final scalar fits. Inputs are preserved when disjoint from `d`.
The frame includes the radix and zero workspace alongside the destination. -/
theorem exec_assemble {w : ℕ} (hw : 2 ≤ w) (as : List (Fin (r + 4)))
    (d : Fin (r + 4)) (hin : ∀ i ∈ as, IsDigit i) (x : Data (r + 4))
    (hfit : Fits w (value (radix w) x as)) :
    ∃ y, Exec w (assemble as d) x y (2 * as.length + 8) ∧
      y.regs d = value (radix w) x as ∧ Frame x y [base, zero, d] ∧
      ∀ i, IsDigit i → i ≠ d → y.regs i = x.regs i := by
  have hval : value (radix w) (Workspace.setupResult w x) as = value (radix w) x as :=
    value_congr fun i hi => Workspace.setup_digit w x (hin i hi)
  refine WP.Exact.exists_exec ?_
  unfold assemble
  wram_call (Workspace.exec_setup hw x)
  wram_call (exec_accumulate hw as hin _ (by simp [Workspace.setupResult, base, zero])
    (hval ▸ hfit)) with u ⟨huv, hum, hup⟩
  wram_exec [huv, hval]
  refine ⟨by wram_simp, ⟨hum, fun i hi ht hc => ?_⟩,
    fun i hi hid => by wram_simp [hup i (digit_ne hi).1, Workspace.setup_digit w x hi]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨hb, hz, hd⟩ := hi
  wram_simp [hup i ht]
  unfold Workspace.setupResult
  wram_simp

/-- Extract low digits by remainder and division, retaining the final quotient in `total`. -/
def extract : List (Fin (r + 4)) → Code .standard (r + 4)
  | [] => .op (.copy carry carry)
  | d :: ds => .seq (ram[ d ← total % base; total ← total / base ]) (extract ds)

/-- Two checked instructions per extracted digit, followed by a workspace self-copy. -/
theorem size_extract (ds : List (Fin (r + 4))) :
    (extract ds).size = 2 * ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [extract, Code.size, ih, List.length_cons]; omega

private theorem exec_extract {w : ℕ} (ds : List (Fin (r + 4)))
    (hout : ∀ i ∈ ds, IsDigit i) (hnd : ds.Nodup) (x : Data (r + 4))
    (hbase : x.regs base = radix w) (hfit : Fits w (x.regs total)) :
    ∃ y, Exec w (extract ds) x y (2 * ds.length + 1) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds + radix w ^ ds.length * y.regs total = x.regs total ∧
      Fits w (y.regs total) ∧ y.mem = x.mem ∧
      ∀ i, i ∉ ds → i ≠ total → y.regs i = x.regs i := by
  induction ds generalizing x with
  | nil =>
    refine WP.Exact.exists_exec ?_
    unfold extract
    wram_exec [List.length_nil]
    exact ⟨by simp [Bounded], by simp [value], hfit, rfl, fun _ _ _ => by simp⟩
  | cons d ds ih =>
    obtain ⟨hdt, _, hdb, _⟩ := digit_ne (hout d List.mem_cons_self)
    refine WP.Exact.exists_exec ?_
    unfold extract
    wram_exec [hbase, hfit]
    wram_call (ih (fun i hi => hout i (List.mem_cons_of_mem d hi))
      (List.nodup_cons.mp hnd).2 _ (by wram_simp [hbase])
      (by wram_simp; exact hfit.of_le (Nat.div_le_self _ _)))
      with y ⟨hyb, hyv, hyfit, hym, hyp⟩
    wram_simp at hyv
    have hyd : y.regs d = x.regs total % radix w := by
      rw [hyp d (List.nodup_cons.mp hnd).1 hdt]; wram_simp
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_, ?_, hyfit, hym,
      fun i hi ht => by
        rw [hyp i (fun hm => hi (List.mem_cons_of_mem d hm)) ht]
        have : i ≠ d := fun h => hi (h ▸ List.mem_cons_self)
        wram_simp⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact hyd ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact hyb i hi
    · rw [value_cons, hyd, List.length_cons, pow_succ]
      calc x.regs total % radix w + radix w * value (radix w) y ds +
              radix w ^ ds.length * radix w * y.regs total
          = x.regs total % radix w +
              radix w * (value (radix w) y ds + radix w ^ ds.length * y.regs total) := by ring
        _ = x.regs total % radix w + radix w * (x.regs total / radix w) := by rw [hyv]
        _ = x.regs total := Nat.mod_add_div _ _

/-- Initialize the half-word radix and extract a scalar into fixed output registers. -/
def split (a : Fin (r + 4)) (ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq Workspace.setup (.seq (.op (.copy total a)) (extract ds))

/-- Conversion has a linear width-independent instruction count, including radix setup. -/
theorem size_split (a : Fin (r + 4)) (ds : List (Fin (r + 4))) :
    (split a ds).size = 2 * ds.length + 8 := by
  simp only [split, Code.size, Workspace.setup, size_extract]; omega

/-- Exact conversion when the supplied digit list has enough capacity. The input may occur
among the outputs: its value is copied into workspace before any digit is written. -/
theorem exec_split {w : ℕ} (hw : 2 ≤ w) (a : Fin (r + 4))
    (ds : List (Fin (r + 4))) (ha : IsDigit a) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (x : Data (r + 4)) (hfit : Fits w (x.regs a))
    (hcap : x.regs a < radix w ^ ds.length) :
    ∃ y, Exec w (split a ds) x y (2 * ds.length + 8) ∧
      Bounded (radix w) y ds ∧ value (radix w) y ds = x.regs a ∧
      Frame x y (base :: zero :: ds) ∧
      ∀ i, IsDigit i → i ∉ ds → y.regs i = x.regs i := by
  have hza : (Workspace.setupResult w x).regs a = x.regs a := Workspace.setup_digit w x ha
  refine WP.Exact.exists_exec ?_
  unfold split
  wram_call (Workspace.exec_setup hw x)
  wram_exec [hza]
  wram_call (exec_extract ds hout hnd _
    (by wram_simp; simp [Workspace.setupResult, base, zero])
    (by wram_simp [hfit])) with y ⟨hyb, hyv, _, hym, hyp⟩
  wram_simp at hyv
  have hyzero : y.regs total = 0 := by
    by_contra hn
    have hm := Nat.le_mul_of_pos_right (radix w ^ ds.length) (Nat.pos_of_ne_zero hn)
    omega
  refine ⟨trivial, hyb, by simpa only [hyzero, mul_zero, add_zero] using hyv,
    ⟨hym, fun i hi ht hc => ?_⟩, fun i hi hid => by
      rw [hyp i hid (digit_ne hi).1]; wram_simp [Workspace.setup_digit w x hi]⟩
  simp only [List.mem_cons, not_or] at hi
  obtain ⟨hb, hz, hd⟩ := hi
  rw [hyp i hd ht]
  wram_simp; unfold Workspace.setupResult; wram_simp

/-- Eighteen half-word digits suffice for every physical scalar at widths at least two,
including odd widths. This conversion always executes exactly 44 instructions. -/
theorem exec_split_eighteen {w : ℕ} (hw : 2 ≤ w) (a : Fin (r + 4))
    (ds : List (Fin (r + 4))) (hlen : ds.length = 18) (ha : IsDigit a)
    (hout : ∀ i ∈ ds, IsDigit i) (hnd : ds.Nodup)
    (x : Data (r + 4)) (hfit : Fits w (x.regs a)) :
    ∃ y, Exec w (split a ds) x y 44 ∧
      Bounded (radix w) y ds ∧ value (radix w) y ds = x.regs a ∧
      Frame x y (base :: zero :: ds) ∧
      ∀ i, IsDigit i → i ∉ ds → y.regs i = x.regs i := by
  have hpow : 2 ^ w ≤ radix w ^ ds.length := by
    rw [radix, ← pow_mul, hlen]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  simpa only [hlen] using exec_split hw a ds ha hout hnd x hfit (hfit.trans_le hpow)

end Cslib.WordRAM.Multiword.Transfer

end
