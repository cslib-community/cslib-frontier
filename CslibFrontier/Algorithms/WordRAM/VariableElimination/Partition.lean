/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Realize

/-!
# Live Factor-Descriptor Partitioning (`partitionLive`)

Partitions the active array of 4-word factor descriptors into two freshly allocated descriptor
arrays: `bucket` (those whose scope contains `x`) and `rest` (all other live factors).

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.partitionLive`: bucket/rest descriptor splitter.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Arguments `(x, livePtr, liveLen)` for `partitionLive`. -/
structure PartitionArgs where
  /-- Field `x` of `PartitionArgs`. -/
  x : ℕ
  /-- Field `livePtr` of `PartitionArgs`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `PartitionArgs`. -/
  liveLen : ℕ

/-- Product equivalence encoding `PartitionArgs` as words. -/
@[expose] def PartitionArgs.equiv : PartitionArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.livePtr), s.liveLen)
  invFun := fun ((x, livePtr), liveLen) => ⟨x, livePtr, liveLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PartitionArgs := .ofEquiv PartitionArgs.equiv

private structure PartitionState where
  curDesc : ℕ
  bDst : ℕ
  bCnt : ℕ
  rDst : ℕ
  rCnt : ℕ

private def PartitionState.equiv : PartitionState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.curDesc, s.bDst), s.bCnt), s.rDst), s.rCnt)
  invFun := fun ((((curDesc, bDst), bCnt), rDst), rCnt) => ⟨curDesc, bDst, bCnt, rDst, rCnt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding PartitionState := .ofEquiv PartitionState.equiv

/-- Return record holding pointer/length pairs for bucket and rest factors. -/
structure PartitionRes where
  /-- Field `bucketPtr` of `PartitionRes`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `PartitionRes`. -/
  bucketLen : ℕ
  /-- Field `newLiveBuf` of `PartitionRes`. -/
  newLiveBuf : ℕ
  /-- Field `restLen` of `PartitionRes`. -/
  restLen : ℕ

/-- Product equivalence encoding `PartitionRes` as words. -/
@[expose] def PartitionRes.equiv : PartitionRes ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.bucketPtr, s.bucketLen), s.newLiveBuf), s.restLen)
  invFun := fun (((bucketPtr, bucketLen), newLiveBuf), restLen) =>
    ⟨bucketPtr, bucketLen, newLiveBuf, restLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PartitionRes := .ofEquiv PartitionRes.equiv

private def partitionStep (p : ℕ × PartitionState) : Memory.Prog PartitionState :=
  Memory.read p.2.curDesc >>= fun scPtr =>
  Memory.read (p.2.curDesc + 1) >>= fun scLen =>
  Memory.read (p.2.curDesc + 2) >>= fun enPtr =>
  Memory.read (p.2.curDesc + 3) >>= fun enLen =>
  memScan ⟨p.1, scPtr, scLen⟩ >>= fun flag =>
  if flag = 1 then
    writeDesc ⟨p.2.bDst, scPtr, scLen, enPtr, enLen⟩ >>= fun _ =>
      pure ⟨p.2.curDesc + 4, p.2.bDst + 4, p.2.bCnt + 1, p.2.rDst, p.2.rCnt⟩
  else
    writeDesc ⟨p.2.rDst, scPtr, scLen, enPtr, enLen⟩ >>= fun _ =>
      pure ⟨p.2.curDesc + 4, p.2.bDst, p.2.bCnt, p.2.rDst + 4, p.2.rCnt + 1⟩

/-- A descriptor list and the bound on its data survive a step that preserves memory below `F`
and the list's descriptor cells. -/
private theorem holdsFactorList_frame {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : HoldsFactorList base fs s₀ ∧ AllDataBelow F base fs s₀)
    (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, base ≤ a → a < base + 4 * fs.length → s₁.mem a = s₀.mem a) :
    HoldsFactorList base fs s₁ ∧ AllDataBelow F base fs s₁ :=
  ⟨h.1.frame_outside h.2 hpres hdesc, h.2.frame hdesc⟩

/-- Writing the descriptor of `f` just past a descriptor list extends the list by `f`. -/
private theorem holdsFactorList_snoc {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {f : FactorTable ℕ ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsFactorList base fs s₀ ∧ AllDataBelow F base fs s₀)
    (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, a < base + 4 * fs.length → s₁.mem a = s₀.mem a)
    (hf : HoldsFactor (base + 4 * fs.length) f s₁)
    (hsc : s₁.mem (base + 4 * fs.length) + f.scope.length ≤ F)
    (hen : s₁.mem (base + 4 * fs.length + 2) + f.entries.size ≤ F) :
    HoldsFactorList base (fs ++ [f]) s₁ ∧ AllDataBelow F base (fs ++ [f]) s₁ := by
  obtain ⟨hl, hd⟩ := holdsFactorList_frame h hpres fun a _ ha => hdesc a ha
  exact ⟨holdsFactorList_append.mpr ⟨hl, hf, by have := hf.1; dsimp only [HoldsFactorList]; omega⟩,
    allDataBelow_append.mpr ⟨hd, hsc, hen, trivial⟩⟩

/-- Split the live descriptor array into bucket (containing `x`) and rest. -/
def partitionLive (args : PartitionArgs) : Memory.Prog PartitionRes :=
  Memory.allocDirty (4 * args.liveLen) >>= fun bucketPtr =>
  Memory.allocDirty (4 + 4 * args.liveLen) >>= fun newLiveBuf =>
  iterate partitionStep args.x args.liveLen
    ⟨args.livePtr, bucketPtr, 0, newLiveBuf + 4, 0⟩ >>= fun res =>
  pure ⟨bucketPtr, res.bCnt, newLiveBuf, res.rCnt⟩

/-- The bucket factors (containing `x`) among the first `k` live factors. -/
private abbrev partBucket (x k : ℕ) (live : List (FactorTable ℕ ℕ)) : List (FactorTable ℕ ℕ) :=
  (live.take k).filter fun f => decide (x ∈ f.scope)

/-- The rest factors (not containing `x`) among the first `k` live factors. -/
private abbrev partRest (x k : ℕ) (live : List (FactorTable ℕ ℕ)) : List (FactorTable ℕ ℕ) :=
  (live.take k).filter fun f => decide (x ∉ f.scope)

/-- Invariant of the loop of `partitionLive` after `k` descriptors, for the input state `s`: the
bucket and rest descriptors among the first `k` sit at `s.frontier` and `s.frontier + 4 * L + 4`. -/
private abbrev PartInv (w x livePtr L : ℕ) (live : List (FactorTable ℕ ℕ)) (s : Memory.State)
    (k : ℕ) (st : PartitionState) (t : Memory.State) : Prop :=
  Memory.WellFormed w t ∧ t.frontier = s.frontier + 4 + 8 * L ∧ st.curDesc = livePtr + 4 * k ∧
    st.bDst = s.frontier + 4 * (partBucket x k live).length ∧
    st.bCnt = (partBucket x k live).length ∧
    st.rDst = s.frontier + 4 * L + 4 + 4 * (partRest x k live).length ∧
    st.rCnt = (partRest x k live).length ∧
    (HoldsFactorList s.frontier (partBucket x k live) t ∧
      AllDataBelow s.frontier s.frontier (partBucket x k live) t) ∧
    (HoldsFactorList (s.frontier + 4 * L + 4) (partRest x k live) t ∧
      AllDataBelow s.frontier (s.frontier + 4 * L + 4) (partRest x k live) t)

/-- Descriptor `k` of a descriptor list. -/
private theorem HoldsFactorList.getElem {base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (h : HoldsFactorList base fs s) {k : ℕ} (hk : k < fs.length) :
    HoldsFactor (base + 4 * k) fs[k] s := by
  rw [← List.take_append_drop k fs, holdsFactorList_append, List.drop_eq_getElem_cons hk,
    List.length_take_of_le hk.le] at h
  exact h.2.1

/-- One step of the loop of `partitionLive` copies descriptor `k` to the bucket array if its scope
contains `x`, and to the rest array otherwise. -/
private theorem partitionStep_framed {w x livePtr L maxScope k : ℕ}
    {live : List (FactorTable ℕ ℕ)} {s t : Memory.State} {st : PartitionState}
    (hlive : HoldsFactorList livePtr live s) (hlen : live.length = L) (hk : k < L)
    (hmax : ∀ f ∈ live, f.scope.length ≤ maxScope) (hpres : PreservesBelow s.frontier s t)
    (hinv : PartInv w x livePtr L live s k st t) :
    Memory.FramedTriple w t (partitionStep (x, st)) (8 + maxScope) (Set.Ici s.frontier)
      (PartInv w x livePtr L live s (k + 1)) := by
  obtain ⟨cur, bDst, bCnt, rDst, rCnt⟩ := st
  obtain ⟨hwf_t, hfr, hcur, hbD, hbC, hrD, hrC, hb, hr⟩ := hinv
  dsimp only at hcur hbD hbC hrD hrC; subst hcur hbD hbC hrD hrC
  have hlb := hlive.bound
  have hkl : k < live.length := by omega
  obtain ⟨-, hsl, hel, hsc', hent'⟩ := (hlive.getElem hkl).mono_frontier hpres
  obtain ⟨hd, -, -, hsc, hent⟩ := hlive.getElem hkl
  have hm0 : t.mem (livePtr + 4 * k) = s.mem (livePtr + 4 * k) :=
    hpres.2.2 _ (by omega)
  have hm2 : t.mem (livePtr + 4 * k + 2) = s.mem (livePtr + 4 * k + 2) :=
    hpres.2.2 _ (by omega)
  have hscF := hsc.1
  have henF := hent.1
  rw [Array.length_toList] at henF
  have hBk : (partBucket x k live).length ≤ k :=
    (List.length_filter_le _ _).trans (List.length_take_le ..)
  have hRk : (partRest x k live).length ≤ k :=
    (List.length_filter_le _ _).trans (List.length_take_le ..)
  have hwd (dst) (h1 : s.frontier ≤ dst) (h2 : dst + 4 ≤ t.frontier) :=
    writeDesc_spec (w := w) (F := s.frontier) ⟨dst, t.mem (livePtr + 4 * k),
      t.mem (livePtr + 4 * k + 1), t.mem (livePtr + 4 * k + 2),
      t.mem (livePtr + 4 * k + 3)⟩ hwf_t h1 h2 (by dsimp only; omega)
      (by dsimp only; omega) hsl hel hsc' hent'
  have hwt (dst) (h1 : s.frontier ≤ dst) (h2 : dst + 4 ≤ t.frontier) :=
    writeDesc_framed (w := w) _ (hwd dst h1 h2).1 h1
  have hwB := hwt (s.frontier + 4 * (partBucket x k live).length) (by omega) (by omega)
  have hwR := hwt (s.frontier + 4 * L + 4 + 4 * (partRest x k live).length) (by omega) (by omega)
  have hms := memScan_framed (w := w) ⟨x, t.mem (livePtr + 4 * k),
    t.mem (livePtr + 4 * k + 1)⟩ hsc'.2 hsl.symm (by have := hsc'.1; dsimp only; omega)
  have hB : partBucket x (k + 1) live =
      if x ∈ live[k].scope then partBucket x k live ++ [live[k]] else partBucket x k live := by
    simp only [partBucket, List.take_add_one, List.getElem?_eq_getElem hkl, Option.toList_some,
      List.filter_append, List.filter_singleton, Bool.cond_decide]
    split_ifs <;> simp only [List.append_nil]
  have hR : partRest x (k + 1) live =
      if x ∈ live[k].scope then partRest x k live else partRest x k live ++ [live[k]] := by
    simp only [partRest, List.take_add_one, List.getElem?_eq_getElem hkl, Option.toList_some,
      List.filter_append, List.filter_singleton, Bool.cond_decide]
    split_ifs <;> simp only [List.append_nil]
  have hmx := hmax _ (List.getElem_mem hkl)
  unfold partitionStep
  framed_triple
  · rename_i hc
    have hx : x ∈ live[k].scope := by simpa using hc
    obtain ⟨-, hfrB, hwfB, hpB, houtB, hfB, hm0B, hm2B⟩ :=
      hwd (s.frontier + 4 * (partBucket x k live).length) (by omega) (by omega)
    dsimp only [PartInv]
    rw [hB, hR, ite_eq_left hx, ite_eq_left hx, List.length_append, List.length_singleton]
    dsimp only at hm0B hm2B hfB houtB ⊢
    exact ⟨hwfB, hfrB.trans hfr, by omega, by omega, rfl, rfl, rfl,
      holdsFactorList_snoc hb hpB (fun a ha => houtB a (Or.inl (by omega))) hfB
        (by rw [hm0B, hm0]; exact hscF) (by rw [hm2B, hm2]; exact henF),
      holdsFactorList_frame hr hpB fun a ha _ => houtB a (Or.inr (by omega))⟩
  · rename_i hc
    have hx : x ∉ live[k].scope := by simpa using hc
    obtain ⟨-, hfrR, hwfR, hpR, houtR, hfR, hm0R, hm2R⟩ :=
      hwd (s.frontier + 4 * L + 4 + 4 * (partRest x k live).length) (by omega) (by omega)
    dsimp only [PartInv]
    rw [hB, hR, ite_eq_right hx, ite_eq_right hx, List.length_append, List.length_singleton]
    dsimp only at hm0R hm2R hfR houtR ⊢
    exact ⟨hwfR, hfrR.trans hfr, by omega, rfl, rfl, by omega, rfl,
      holdsFactorList_frame hb hpR (fun a _ ha => houtR a (Or.inl (by omega))),
      holdsFactorList_snoc hr hpR (fun a ha => houtR a (Or.inl (by omega))) hfR
        (by rw [hm0R, hm0]; exact hscF) (by rw [hm2R, hm2]; exact henF)⟩

theorem partitionLive_spec {w : ℕ} {args : PartitionArgs}
    {live : List (FactorTable ℕ ℕ)} {maxScope : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hlive : HoldsFactorList args.livePtr live s) (hlen : live.length = args.liveLen)
    (hmax : ∀ f ∈ live, f.scope.length ≤ maxScope)
    (hfit : Fits w (s.frontier + 4 + 8 * args.liveLen)) :
    let res := (Memory.spec 0).clientResult s (partitionLive args)
    let s' := (Memory.spec 0).clientState s (partitionLive args)
    let bucket := live.filter fun f => decide (args.x ∈ f.scope)
    let rest := live.filter fun f => decide (args.x ∉ f.scope)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partitionLive args)) ∧
      s'.frontier = s.frontier + 4 + 8 * args.liveLen ∧
      PreservesBelow s.frontier s s' ∧
      res.bucketPtr = s.frontier ∧
      res.newLiveBuf = s.frontier + 4 * args.liveLen ∧
      res.bucketLen = bucket.length ∧
      res.restLen = rest.length ∧
      HoldsFactorList res.bucketPtr bucket s' ∧
      AllDataBelow s.frontier res.bucketPtr bucket s' ∧
      HoldsFactorList (res.newLiveBuf + 4) rest s' ∧
      AllDataBelow s.frontier (res.newLiveBuf + 4) rest s' ∧
      memoryCost (partitionLive args) s ≤ 2 + args.liveLen * (8 + maxScope) := by
  have hfit1 : Fits w (s.frontier + 4 * args.liveLen) := hfit.of_le (by omega)
  have hfit2 : Fits w (s.frontier + 4 * args.liveLen + (4 + 4 * args.liveLen)) :=
    hfit.of_le (by omega)
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (body := partitionStep)
    (safe := fun _ _ _ => True) (d := args.x) (n := args.liveLen) (c := 8 + maxScope)
    (s := ⟨s.mem, s.frontier + 4 * args.liveLen + (4 + 4 * args.liveLen)⟩)
    (a₀ := ⟨args.livePtr, s.frontier, 0, s.frontier + 4 * args.liveLen + 4, 0⟩)
    (S := Set.Ici s.frontier) (PartInv w args.x args.livePtr args.liveLen live s)
    ⟨(hwf.step (o := .allocDirty _) hfit1).step (o := .allocDirty _) hfit2, by dsimp only; omega,
      rfl, rfl, rfl, rfl, rfl, ⟨show s.frontier ≤ s.frontier + _ + _ by omega, trivial⟩,
      ⟨show s.frontier + 4 * args.liveLen + 4 ≤ s.frontier + _ + _ by omega, trivial⟩⟩
    (fun k hk _ t hinv hmod => ⟨trivial, partitionStep_framed hlive hlen hk hmax
      (preservesBelow_of_modifies hmod ⟨le_rfl, by dsimp only; omega, fun _ _ => rfl⟩) hinv⟩)
    fun _ _ h _ => h
  have hft : Memory.FramedTriple w s (partitionLive args) (2 + args.liveLen * (8 + maxScope))
      (Set.Ici s.frontier) fun r t => t.frontier = s.frontier + 4 + 8 * args.liveLen ∧
        r.bucketPtr = s.frontier ∧ r.newLiveBuf = s.frontier + 4 * args.liveLen ∧
        r.bucketLen = (partBucket args.x args.liveLen live).length ∧
        r.restLen = (partRest args.x args.liveLen live).length ∧
        (HoldsFactorList r.bucketPtr (partBucket args.x args.liveLen live) t ∧
          AllDataBelow s.frontier r.bucketPtr (partBucket args.x args.liveLen live) t) ∧
        (HoldsFactorList (r.newLiveBuf + 4) (partRest args.x args.liveLen live) t ∧
          AllDataBelow s.frontier (r.newLiveBuf + 4) (partRest args.x args.liveLen live) t) := by
    unfold partitionLive
    exact Memory.FramedTriple.mono (Memory.FramedTriple.allocDirty_bind hfit1
      (Memory.FramedTriple.allocDirty_bind hfit2 (Memory.FramedTriple.call (c₂ := 0) hloop
        subset_rfl fun _ _ h _ => Memory.FramedTriple.pure ⟨h.2.1, rfl, rfl, h.2.2.2.2.1,
          h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩))) (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, hm, hfr, h1, h2, h3, h4, ⟨h5, h6⟩, h7, h8⟩ := framedTriple_iff_realization.mp hft
  simp only [partBucket, partRest, ← hlen, List.take_length] at h3 h4 h5 h6 h7 h8
  exact ⟨hv, hfr, preservesBelow_of_modifies hm (.refl le_rfl), h1, h2, h3, h4, h5,
    h6, h7, h8, hc⟩

theorem partitionLive_realizes :
    Realizes .exact partitionLive WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧ Fits w (s.frontier + 4 + 8 * args.liveLen) ∧
        ∃ live, live.length = args.liveLen ∧ HoldsFactorList args.livePtr live s)
      (fun _ _ => 0) := by
  unfold partitionLive
  realize [memScan_realizes, writeDesc_realizes]
  iterate 4 · exact h.2.1.of_le (by omega)
  · obtain ⟨h1, hfit, live, hlen, hlive⟩ := h
    have hlb := hlive.bound
    have hscK (f) (hf : f ∈ live) : f.scope.length ≤ (live.flatMap FactorTable.scope).length := by
      rw [List.length_flatMap]; exact List.le_sum_of_mem (List.mem_map_of_mem hf)
    refine (Memory.FramedTriple.iterate (w := w) (c := 8 + (live.flatMap FactorTable.scope).length)
      (S := Set.Ici s.frontier) (Q := fun _ _ => True) (PartInv w d.x d.livePtr d.liveLen live s)
      ⟨(hmem.step (o := .allocDirty (4 * d.liveLen)) (hfit.of_le (by omega))).step
        (o := .allocDirty (4 + 4 * d.liveLen))
        (hfit.of_le (show s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen) ≤ _ by omega)),
        show s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen) = _ by omega,
        rfl, rfl, rfl, rfl, rfl,
        ⟨show s.frontier ≤ s.frontier + _ + _ by omega, trivial⟩,
        ⟨show s.frontier + 4 * d.liveLen + 4 ≤ s.frontier + _ + _ by omega, trivial⟩⟩
      (fun k hk st t hinv hmod => ?_) fun _ _ _ _ => trivial).1
    have hpres : PreservesBelow s.frontier s t := preservesBelow_of_modifies hmod
      ⟨le_rfl, (Nat.le_add_right _ _).trans (Nat.le_add_right _ _), fun _ _ => rfl⟩
    refine ⟨?_, partitionStep_framed hlive hlen hk hscK hpres hinv⟩
    obtain ⟨-, hfr, hcur, hbD, hbC, hrD, hrC, -, -⟩ := hinv
    obtain ⟨hd, hsl, -, hsc, -⟩ := hlive.getElem (by omega : k < live.length)
    have hm0 : t.mem st.curDesc = s.mem st.curDesc := hpres.2.2 _ (by omega)
    have hm1 : t.mem (st.curDesc + 1) = s.mem (st.curDesc + 1) := hpres.2.2 _ (by omega)
    have hBk : (partBucket d.x k live).length ≤ k :=
      (List.length_filter_le _ _).trans (List.length_take_le ..)
    have hRk : (partRest d.x k live).length ≤ k :=
      (List.length_filter_le _ _).trans (List.length_take_le ..)
    dsimp only
    refine ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
      ⟨h1, hfit.of_le (by rw [hm0, hm1, hcur, hsl]; have := hsc.1; omega)⟩, h1, ?_⟩
    split_ifs <;> exact ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
      hfit.of_le (by omega)⟩

end Cslib.Algorithms.WordRAM.VariableElimination
