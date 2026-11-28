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
# Checked multiword right shifts

Whole half-word digits are skipped by subtracting the half width from a physical scalar.
The remaining shift is division by a power of two, performed from high digits to low digits
with a remainder carry. Each intermediate is strictly below the square of the digit radix.

## Main definitions

* `Cslib.WordRAM.Multiword.Shift.cell`, `Cslib.WordRAM.Multiword.Shift.digits`,
  `Cslib.WordRAM.Multiword.Shift.finish`: single-digit division, high-to-low digit division, and
  residual power-of-two shift completion.
* `Cslib.WordRAM.Multiword.Shift.dispatch`, `Cslib.WordRAM.Multiword.Shift.codeSize`: whole-digit
  shift dispatch and its static instruction count.
* `Cslib.WordRAM.Multiword.Shift.program`: variable right shift with fixed register lists.

## Main results

* `Cslib.WordRAM.Multiword.Shift.exec`: bounded digits, exact reconstruction and a frame.
* `Cslib.WordRAM.Multiword.Shift.exec_eighteen`: the eighteen-digit bank interface.

The code may depend on the physical width through constants. Its size and runtime bounds
depend only on the digit counts. Inputs and outputs are disjoint little-endian digit lists;
the scalar is a separate physical word. All four reserved registers may change.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Shift

open Workspace

variable {r : ℕ}

/-- One division digit. `base` is the radix, `zero` the divisor, and `total` the shift. -/
def cell (a d : Fin (r + 4)) : Code .standard (r + 4) := ram[
  carry ← carry * base;
  carry ← carry + a;
  d ← carry >>> total;
  carry ← carry % zero ]

private theorem exec_cell {w : ℕ} (x : Data (r + 4))
    (a d : Fin (r + 4)) (ha : IsDigit a) (hd : IsDigit d)
    (hb : x.regs base = radix w) (hz : x.regs zero = 2 ^ x.regs total)
    (hs : x.regs total < w / 2) (had : x.regs a < radix w)
    (hc : x.regs carry < 2 ^ x.regs total) :
    ∃ y, Exec w (cell a d) x y 4 ∧
      y.regs d < radix w ∧
      y.regs carry < 2 ^ x.regs total ∧
      y.regs d * 2 ^ x.regs total + y.regs carry = x.regs carry * radix w + x.regs a ∧
      y.regs total = x.regs total ∧ Frame x y [d] := by
  obtain ⟨_, hac, _, _⟩ := digit_ne ha
  obtain ⟨hdt, hdc, _, hdz⟩ := digit_ne hd
  have hp : 0 < 2 ^ x.regs total := Nat.two_pow_pos _
  have hple : 2 ^ x.regs total ≤ radix w :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : x.regs carry * radix w + x.regs a < radix w * 2 ^ x.regs total := by nlinarith
  have hf : Fits w (x.regs carry * radix w + x.regs a) := by
    have hsq := radix_sq_le w
    unfold Fits
    nlinarith
  have hq : Fits w ((x.regs carry * radix w + x.regs a) >>> x.regs total) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact hf.of_le (Nat.div_le_self _ _)
  have hr := hf.of_le (Nat.mod_le (x.regs carry * radix w + x.regs a) (2 ^ x.regs total))
  refine WP.Exact.exists_exec ?_
  wram_exec [cell, hb, hz, hf, hq, hr]
  refine ⟨?_, ?_, ?_, by wram_simp, ⟨rfl, fun i hi _ hic => by
    simp only [List.mem_singleton] at hi; wram_simp⟩⟩
  · wram_simp [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul hp).mpr hlt
  · wram_simp
    exact Nat.mod_lt _ hp
  · wram_simp [Nat.shiftRight_eq_div_pow]
    rw [Nat.mul_comm, Nat.add_comm]
    exact Nat.mod_add_div _ _

/-- Divide from high to low, padding the high output digits with zeros. -/
def digits : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, d :: ds => .seq (digits as ds) (cell a d)
  | [], d :: ds => .seq (digits [] ds) (.op (.const d 0))
  | _, [] => .op (.const carry 0)

/-- The static instruction size of `digits as ds` when `as.length ≤ ds.length`. -/
theorem size_digits (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length) :
    (digits as ds).size = ds.length + 3 * as.length + 1 := by
  induction ds generalizing as with
  | nil => cases as <;> simp_all [digits]
  | cons d ds ih =>
    cases as with
    | nil => simp only [digits, Code.size, ih [] (by simp), List.length_nil,
        List.length_cons]
    | cons a as => simp only [digits, Code.size, cell,
        ih as (by simpa using hlen), List.length_cons]; omega

private theorem exec_digits {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) (hb : x.regs base = radix w)
    (hz : x.regs zero = 2 ^ x.regs total) (hs : x.regs total < w / 2)
    (ha : Bounded (radix w) x as) :
    ∃ y, Exec w (digits as ds) x y (ds.length + 3 * as.length + 1) ∧
      Bounded (radix w) y ds ∧ y.regs carry < 2 ^ x.regs total ∧
      value (radix w) y ds * 2 ^ x.regs total + y.regs carry =
        value (radix w) x as ∧ y.regs total = x.regs total ∧ Frame x y ds := by
  induction ds generalizing as x with
  | nil =>
    cases as with
    | cons => simp_all
    | nil =>
      refine WP.Exact.exists_exec ?_
      wram_exec [digits, List.length_nil]
      refine ⟨by simp [Bounded], by wram_simp; exact Nat.two_pow_pos _, by simp [value],
        by wram_simp, frame_set_carry x 0 []⟩
  | cons d ds ih =>
    have hd := digit_ne (hout d (by simp))
    have hds : ∀ i ∈ ds, IsDigit i := fun i hi => hout i (by simp [hi])
    have hnd' := (List.nodup_cons.mp hnd).2
    have hdnot := (List.nodup_cons.mp hnd).1
    cases as with
    | nil =>
      refine WP.Exact.exists_exec ?_
      wram_exec [digits]
      wram_call (ih [] (by simp) (by simp) hds hnd' (by simp) x hb hz hs
        (by simp [Bounded])) with z ⟨hzb, hzc, hzv, hzt, hzf⟩
      wram_exec [List.length_cons, List.length_nil]
      obtain ⟨hyb, hyv, hyframe⟩ := hzf.step_cons (frame_set_mem (d := d) z 0) hds hdnot hzb
        (by wram_simp; exact lt_trans zero_lt_one (one_lt_radix hw))
      refine ⟨hyb, by wram_simp [hzc], ?_, by wram_simp [hzt], hyframe⟩
      change ((z.set d 0).regs d + radix w * value (radix w) (z.set d 0) ds) * _ + _ = _
      wram_simp [hyv]
      simp only [value, List.map_nil, Nat.ofDigits_nil] at hzv ⊢
      obtain ⟨hz1, hzc0⟩ := Nat.add_eq_zero_iff.mp hzv
      rw [mul_assoc, hz1, mul_zero, hzc0, zero_add]
    | cons a as =>
      have hdis' : List.Disjoint ds as := List.disjoint_left.mpr fun i hi hj =>
        List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi) (List.mem_cons_of_mem a hj)
      refine WP.Exact.exists_exec ?_
      wram_exec [digits]
      wram_call (ih as (by simpa using hlen) (fun i hi => hin i (by simp [hi])) hds hnd' hdis'
        x hb hz hs (fun i hi => ha i (by simp [hi]))) with z ⟨hzb, hzc, hzv, hzt, hzf⟩
      have hza : z.regs a = x.regs a := hzf.digit_regs (hin a (by simp))
        (fun hi => List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi) List.mem_cons_self)
      wram_call (exec_cell z a d (hin a (by simp)) (hout d (by simp))
        ((hzf.base_regs hds).trans hb) ((hzf.zero_regs hds).trans (hzt ▸ hz)) (by rwa [hzt])
        (hza ▸ ha a (by simp)) (by rwa [hzt])) with y ⟨hy_d, hyc, hyv, hyt, hyf⟩
      obtain ⟨hyb, hyval, hyframe⟩ := hzf.step_cons hyf hds hdnot hzb hy_d
      refine ⟨by simp only [List.length_cons]; omega, hyb, by rwa [hzt] at hyc, ?_,
        hyt.trans hzt, hyframe⟩
      change (y.regs d + radix w * value (radix w) y ds) * _ + _ =
        x.regs a + radix w * value (radix w) x as
      rw [hzt, hza] at hyv
      rw [hyval]
      nlinarith [congrArg (radix w * ·) hzv]

/-- Set up the residual power-of-two divisor and divide the remaining digits. -/
def finish (as ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq (ram[ zero ← #1; zero ← zero <<< total ]) (digits as ds)

private theorem exec_finish {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) (hb : x.regs base = radix w)
    (hs : x.regs total < w / 2) (ha : Bounded (radix w) x as) :
    ∃ y, Exec w (finish as ds) x y (ds.length + 3 * as.length + 3) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs total ∧
      Frame x y (zero :: ds) := by
  have h1 := fits_one (w := w) (by omega)
  have hpow : Fits w (2 ^ x.regs total) :=
    (radix_fits hw).of_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hshift : 1 <<< x.regs total = 2 ^ x.regs total := by
    rw [Nat.shiftLeft_eq, one_mul]
  refine WP.Exact.exists_exec ?_
  wram_exec [finish, h1, hpow, hshift]
  refine WP.Exact.name fun z hzx => ?_
  have hzf : Frame x z [zero] := by
    rw [hzx, Data.set_set]
    exact frame_set_mem x _
  have hdis_z : ∀ i ∈ as, i ∉ [zero] :=
    fun i hi hm => (digit_ne (hin i hi)).2.2.2 (List.mem_singleton.mp hm)
  wram_call (exec_digits hw as ds hlen hin hout hnd hdis z
    (by rw [hzx]; wram_simp [hb]) (by rw [hzx]; wram_simp) (by rw [hzx]; wram_simp; exact hs)
    (hzf.bounded_of_digits hin hdis_z ha)) with y ⟨hyb, hyc, hyv, _, hyf⟩
  have hzt : z.regs total = x.regs total := by rw [hzx]; wram_simp
  rw [hzt, hzf.value_eq_of_digits hin hdis_z] at hyv
  rw [hzt] at hyc
  refine ⟨trivial, hyb, ?_, frame_trans (frame_mono hzf (by simp)) (frame_mono hyf (by simp))⟩
  rw [Nat.shiftRight_eq_div_pow]
  exact (Nat.div_eq_of_lt_le (by omega) (by nlinarith)).symm

/-- Branch through the possible whole-digit shifts. Exhausting the input clears the output. -/
def dispatch : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | [], ds => .seq (.op (.const total 0)) (finish [] ds)
  | a :: as, ds => .branch (.lt total zero) (finish (a :: as) ds)
      (.seq (.op (.bin .sub total total zero)) (dispatch as ds))

/-- Exact instruction-list size before the three-instruction initialization. -/
def codeSize : ℕ → ℕ → ℕ
  | 0, n => n + 4
  | m + 1, n => codeSize m n + n + 3 * (m + 1) + 6

/-- The static instruction size of `dispatch as ds` equals `codeSize as.length ds.length`. -/
theorem size_dispatch (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length) :
    (dispatch as ds).size = codeSize as.length ds.length := by
  induction as with
  | nil => simp only [dispatch, Code.size, finish, size_digits [] ds (by simp),
      List.length_nil, codeSize]; omega
  | cons a as ih =>
    have hlen' : as.length ≤ ds.length := by simp only [List.length_cons] at hlen; omega
    simp only [dispatch, Code.size, finish, size_digits _ _ hlen,
      ih hlen', List.length_cons, codeSize]
    omega

private theorem exec_dispatch {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) (hb : x.regs base = radix w) (hz : x.regs zero = w / 2)
    (hs : Fits w (x.regs total)) (ha : Bounded (radix w) x as) :
    ∃ y, ExecWithin w (dispatch as ds) x y (ds.length + 3 * as.length + 4) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs total ∧
      Frame x y (base :: zero :: ds) := by
  induction as generalizing x with
  | nil =>
    refine WP.exists_execWithin (WP.Exact.toWP ?_)
    wram_exec [dispatch]
    wram_call (exec_finish hw [] ds (by simp) (by simp) hout hnd (by simp) _
      (by wram_simp [hb]) (by wram_simp; omega) (by simp [Bounded])) with y ⟨hyb, hyv, hyf⟩
    refine ⟨by simp only [List.length_nil]; omega, hyb, ?_,
      frame_trans (frame_set_total x 0 _) (frame_mono hyf (by simp))⟩
    simpa only [value, List.map_nil, Nat.ofDigits_nil, Nat.zero_shiftRight] using hyv
  | cons a as ih =>
    have hlen' : as.length ≤ ds.length := by simp only [List.length_cons] at hlen; omega
    have hin' : ∀ i ∈ as, IsDigit i := fun i hi => hin i (by simp [hi])
    have hdis' : List.Disjoint ds as := List.disjoint_left.mpr fun i hi hj =>
      List.disjoint_left.mp hdis hi (List.mem_cons_of_mem a hj)
    have hf : Fits w (x.regs total - w / 2) := hs.of_le (Nat.sub_le _ _)
    refine WP.exists_execWithin ?_
    wram_exec [dispatch, hz, hf]
    case pos =>
      obtain ⟨y, he, hyb, hyv, hyf⟩ :=
        exec_finish hw (a :: as) ds hlen hin hout hnd hdis x hb hc ha
      exact WP.of_execWithin he.within
        ⟨by simp only [List.length_cons]; omega, hyb, hyv, frame_mono hyf (by simp)⟩
    case neg =>
      have hza (i : Fin (r + 4)) (hi : i ∈ as) :
          (x.set total (x.regs total - w / 2)).regs i = x.regs i := by
        have := (digit_ne (hin' i hi)).1
        wram_simp
      wram_call (ih hlen' hin' hdis' _ (by wram_simp [hb]) (by wram_simp [hz])
        (by wram_simp [hf]) (fun i hi => by rw [hza i hi]; exact ha i (by simp [hi]))) with
        y ⟨hyb, hyv, hyf⟩
      have hdrop : value (radix w) x (a :: as) >>> (w / 2) = value (radix w) x as := by
        rw [Nat.shiftRight_eq_div_pow]
        change (x.regs a + radix w * value (radix w) x as) / radix w = _
        rw [Nat.add_mul_div_left _ _ (by have := one_lt_radix hw; omega),
          Nat.div_eq_of_lt (ha a (by simp)), zero_add]
      refine ⟨by simp only [List.length_cons]; omega, hyb, ?_,
        frame_trans (frame_set_total x _ _) hyf⟩
      rw [show x.regs total = w / 2 + (x.regs total - w / 2) by omega,
        Nat.shiftRight_add, hdrop, ← value_congr hza]
      wram_simp at hyv
      exact hyv

/-- Initialize the radix, half width and scalar shift, then execute checked division. -/
def program (w : ℕ) (as ds : List (Fin (r + 4))) (s : Fin (r + 4)) :
    Code .standard (r + 4) :=
  .seq (ram[ base ← #(radix w); zero ← #(w / 2); total ← s ]) (dispatch as ds)

/-- The static instruction size of `program w as ds s` is `3 + codeSize as.length ds.length`. -/
theorem size_program (w : ℕ) (as ds : List (Fin (r + 4))) (s : Fin (r + 4))
    (hlen : as.length ≤ ds.length) :
    (program w as ds s).size = 3 + codeSize as.length ds.length := by
  simp [program, size_dispatch as ds hlen]

/-- Variable right shift from a physical scalar word. The output is padded to its fixed length.
All arithmetic, including construction of the residual power of two, is checked at width `w`.
The frame preserves memory and every register outside the output and reserved workspace. -/
theorem exec {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (s : Fin (r + 4)) (hlen : as.length ≤ ds.length)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i) (hsdigit : IsDigit s)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as) (hsout : s ∉ ds)
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hs : Fits w (x.regs s)) :
    ∃ y, ExecWithin w (program w as ds s) x y (ds.length + 3 * as.length + 7) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs s ∧
      Frame x y (base :: zero :: ds) ∧ y.regs s = x.regs s := by
  obtain ⟨hst, hsc, hsb, hsz⟩ := digit_ne hsdigit
  have hhalf := (fits_self w).of_le (Nat.div_le_self w 2)
  have hβ := radix_fits hw
  refine WP.exists_execWithin ?_
  wram_exec [program, hhalf, hβ]
  refine WP.name fun z hzx => ?_
  have hzi (i : Fin (r + 4)) (hi : IsDigit i) : z.regs i = x.regs i := by
    obtain ⟨ht, _, hb, hz⟩ := digit_ne hi
    rw [hzx]; wram_simp
  wram_call (exec_dispatch hw as ds hlen hin hout hnd hdis z (by rw [hzx]; wram_simp)
    (by rw [hzx]; wram_simp) (by rw [hzx]; wram_simp [hs])
    (fun i hi => by rw [hzi i (hin i hi)]; exact ha i hi)) with y ⟨hyb, hyv, hyf⟩
  have hzf : Frame x z (base :: zero :: ds) := by
    rw [hzx]
    exact frame_trans (frame_set_mem x (radix w))
      (frame_trans (frame_set_mem (d := zero) _ (w / 2)) (frame_set_total _ _ _))
  have hf := frame_trans hzf hyf
  refine ⟨by omega, hyb, ?_, hf, hf.2 s (by simp [hsb, hsz, hsout]) hst hsc⟩
  have hzt : z.regs total = x.regs s := by rw [hzx]; wram_simp
  rwa [hzt, value_congr fun i hi => hzi i (hin i hi)] at hyv

/-- Extract the outside-output register guarantee from the complete four-register frame. -/
private theorem regs_eq_of_frame {x y : Data (r + 4)} {ds : List (Fin (r + 4))}
    (hf : Frame x y (base :: zero :: ds)) {i : Fin (r + 4)}
    (hi : IsDigit i) (hnot : i ∉ ds) : y.regs i = x.regs i := by
  obtain ⟨ht, hc, hb, hz⟩ := digit_ne hi
  exact hf.2 i (by simp only [List.mem_cons, not_or]; exact ⟨hb, hz, hnot⟩) ht hc

/-- A shift beyond the full digit capacity is zero. Combined with `exec`, this also describes
the runtime's large-shift branch, without requiring its scalar to fit the digit radix. -/
theorem shiftRight_eq_zero {w s : ℕ} (hw : 2 ≤ w) (x : Data (r + 4))
    (as : List (Fin (r + 4))) (ha : Bounded (radix w) x as)
    (hs : (w / 2) * as.length ≤ s) : value (radix w) x as >>> s = 0 := by
  have hv : value (radix w) x as < radix w ^ as.length := by
    simpa only [value, List.length_map] using
      Nat.ofDigits_lt_base_pow_length (one_lt_radix hw) (List.forall_mem_map.mpr ha)
  rw [radix, ← pow_mul] at hv
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (hv.trans_le (Nat.pow_le_pow_right (by decide) hs))

/-- A quadratic instruction-list bound, independent of the physical word width. -/
theorem codeSize_le (m n : ℕ) : codeSize m n ≤ (m + 1) * (n + 3 * m + 6) := by
  induction m with
  | zero => simp [codeSize]
  | succ m ih => simp only [codeSize]; nlinarith

/-- Eighteen input and output digits have exactly 970 compiled instructions. -/
theorem size_program_eighteen (w : ℕ) (as ds : List (Fin (r + 4))) (s : Fin (r + 4))
    (has : as.length = 18) (hds : ds.length = 18) :
    (program w as ds s).size = 970 := by
  rw [size_program w as ds s (by omega), has, hds]
  decide

/-- The MSB bank's eighteen-digit shift takes at most 79 instructions, including initialization.
Every non-output register numbered at least four is preserved, including the scalar. -/
theorem exec_eighteen {w : ℕ} (hw : 2 ≤ w)
    (as ds : List (Fin (r + 4))) (s : Fin (r + 4))
    (has : as.length = 18) (hds : ds.length = 18)
    (hin : ∀ i ∈ as, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i) (hsdigit : IsDigit s)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds as) (hsout : s ∉ ds)
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hs : Fits w (x.regs s)) :
    ∃ y, ExecWithin w (program w as ds s) x y 79 ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = value (radix w) x as >>> x.regs s ∧
      Frame x y (base :: zero :: ds) ∧
      (∀ i, IsDigit i → i ∉ ds → y.regs i = x.regs i) := by
  obtain ⟨y, he, hyb, hyv, hyf, _⟩ := exec hw as ds s (by omega) hin hout hsdigit
    hnd hdis hsout x ha hs
  exact ⟨y, by simpa only [has, hds] using he, hyb, hyv, hyf,
    fun _ hi hnot => regs_eq_of_frame hyf hi hnot⟩

end Cslib.WordRAM.Multiword.Shift

end
