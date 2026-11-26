/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Prog
public import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder

/-!
# Tape contents and matched runs of the universal program

Evaluates `Uni.emX P x z` on every channel `z : Zc K` and characterizes the matched-run
condition `Tape.Mt (emX P) (fun _ => bits.map .bit) x` as the structured predicate `Uni.MX x bits`
(`Uni.mt_X`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.Vals`.

## Main definitions

* `Uni.bws`: concatenation of semicolon-terminated bit words `bw`.
* `Uni.oc`: record key content tagged with `some` and terminated by `none`.
* `Uni.dfs`, `Uni.lks`: defined and looked-up record lists extracted from an `XP` run.
* `Uni.MX`: channel-matched run condition for `XP P` on input `bits`.

## Main results

* `Uni.bw_inj`, `Uni.bws_inj`: unique decodability of semicolon-terminated bit words.
* `Uni.emX_rg_true`, `Uni.emX_rg_false`, `Uni.emX_md_true`, `Uni.emX_md_false`,
  `Uni.emX_cp_true`, `Uni.emX_cp_false`, `Uni.emX_fr_true`, `Uni.emX_fr_false`,
  `Uni.emX_lk_true`, `Uni.emX_lk_false`, `Uni.emX_ls_true`, `Uni.emX_ls_false`,
  `Uni.emX_bk`, `Uni.emX_cm`, `Uni.emX_inp`.
* `Uni.mt_X`: equivalence between `Tape.Mt (emX P) … x` and `Uni.MX x bits`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Cslib.Circuits.Arithmetic.Separation.Tape

/-- Concatenation of semicolon-terminated binary words. -/
@[expose] def bws {M K : Type} (ws : List (List Bool)) : List (Sy M K) := ws.flatMap bw

theorem bws_cons {M K : Type} (w : List Bool) (ws : List (List Bool)) :
    (bws (w :: ws) : List (Sy M K)) = bw w ++ bws ws := rfl

theorem bw_inj {M K : Type} {w w' : List Bool} {u v : List (Sy M K)}
    (h : bw w ++ u = bw w' ++ v) : w = w' ∧ u = v := by
  simp only [bw, List.append_assoc, List.singleton_append] at h
  have hs (w : List Bool) : (Sy.semi : Sy M K) ∉ w.map .bit := by simp
  obtain ⟨h1, h2⟩ := cut_inj (hs w) (hs w') h
  exact ⟨List.map_injective_iff.2 (fun _ _ e => by simpa using e) h1, h2⟩

theorem bws_inj {M K : Type} : Function.Injective (bws : List (List Bool) → List (Sy M K)) :=
  flatMap_inj (fun _ => by simp [bw]) fun _ _ _ _ h => (bw_inj h).1

/-- Wrap the key letters of a record with `some` and append the rotation mark `none`. -/
@[expose] def oc {K : Type} (c : List (Bl K)) : List (Option (Bl K)) := c.map some ++ [none]

theorem encW_append {M K : Type} (l l' : List (Bool × List (Option (Bl K)))) :
    (encW (l ++ l') : List (Sy M K)) = encW l ++ encW l' := by
  simp [encW]

theorem encW_cons {M K : Type} (r : Bool × List (Option (Bl K)))
    (l : List (Bool × List (Option (Bl K)))) :
    (encW (r :: l) : List (Sy M K)) = rw' r.1 r.2 ++ encW l := rfl

section EmX

variable {A M K : Type} {P : Mach A M K}

/-- The defined (allocated) record contents of a run `x : XP P`, starting with record `0`. -/
@[expose] def dfs (x : XP P) : List (List (Bl K)) :=
  cont P.kN (List.replicate (x.init.length + 1) fun _ => false) ::
    x.steps.map fun s => cont (P.ak s.1) (alc P s.1 s.2)

/-- The looked-up record contents of a run `x : XP P`. -/
@[expose] def lks (x : XP P) : List (List (Bl K)) :=
  x.steps.map fun s => cont (P.lk s.1) (ldc P s.1 s.2)

private theorem flatMap_const_nil {α β : Type*} (l : List α) :
    (l.flatMap fun _ => ([] : List β)) = [] :=
  List.flatMap_eq_nil_iff.2 fun _ _ => rfl

variable [Fintype K] [DecidableEq K]

private theorem emX_simp_other (x : XP P) {z : Zc K}
    (h1 : z ≠ lsT) (h2 : z ≠ lsF) (h3 : ∀ b s, z ≠ .tp (.bk b) s)
    (h4 : ∀ k s, z ≠ .tp (.cm k) s) :
    emX P x z = emIn P.m0 P.kN x.init z ++
      ((x.counter.flatMap fun r => emCt r z) ++
        ((x.steps.flatMap fun s => emSt P s z) ++
          (emEd P.mh (x.finalRegs, x.finalCounter) z ++ emAp x.lookups z))) := by
  simp [emX, emU_other _ h1 h2 h3 h4]

theorem emX_rg_true (x : XP P) (i : Fin 5) :
    emX P x (tp (.rg i) true) =
      bws (x.steps.map (fun s => cw s.2 (rv i)) ++ [x.finalRegs.map fun v => v i]) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, rgw, emEd, emAp, on, mem_rgs, bws, List.flatMap_map, flatMap_const_nil]

theorem emX_rg_false (x : XP P) (i : Fin 5) :
    emX P x (tp (.rg i) false) =
      bws (i0 x.init :: x.steps.map fun s => cw s.2 (P.dr s.1 i)) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, rgw, emEd, emAp, on, mem_rgs, bws, List.flatMap_map, flatMap_const_nil]

theorem emX_md_true (x : XP P) :
    emX P x (tp .md true) = (x.steps.map (fun s => P.src s.1) ++ [P.mh]).map .md := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, flatMap_const_nil, ← List.map_eq_flatMap,
    List.map_map, Function.comp_def]

theorem emX_md_false (x : XP P) :
    emX P x (tp .md false) = (P.m0 :: x.steps.map fun s => P.dst s.1).map .md := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, flatMap_const_nil, ← List.map_eq_flatMap,
    List.map_map, Function.comp_def]

theorem emX_cp_true (x : XP P) :
    emX P x (tp .cp true) = bws (x.counter.map cn ++ [true :: x.finalCounter]) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, bws, List.flatMap_map, flatMap_const_nil]

theorem emX_cp_false (x : XP P) :
    emX P x (tp .cp false) = bws (i1 x.init :: x.counter.map cn1) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, bws, List.flatMap_map, flatMap_const_nil]

theorem emX_fr_true (x : XP P) :
    emX P x (tp .fr true) = bws (x.steps.map fun s => cw s.2 8) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, bws, List.flatMap_map, flatMap_const_nil]

theorem emX_fr_false (x : XP P) :
    emX P x (tp .fr false) = bws (x.counter.map cn) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, bws, List.flatMap_map, flatMap_const_nil]

theorem emX_lk_true (x : XP P) : emX P x (tp .lk true) = x.lookups := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, flatMap_const_nil]

theorem emX_lk_false (x : XP P) :
    emX P x (tp .lk false) = encW ((lks x).map fun c => (true, oc c)) := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, encW, lks, List.flatMap_map, oc, rec',
    flatMap_const_nil]

theorem emX_ls_true (x : XP P) : emX P x lsT = emU x.sort lsT := by
  simp [emX, emIn, emCt, emSt, emEd, emAp, on, mem_rgs, flatMap_const_nil]

theorem emX_ls_false (x : XP P) :
    emX P x lsF =
      encW ((dfs x).map fun c => (false, oc c)) ++ (x.lookups ++ .bar :: emU x.sort lsF) := by
  simp [emX, emIn, emCt, emSt, emEd, emAp, on, mem_rgs, encW, dfs, List.flatMap_map, oc, rec',
    flatMap_const_nil]

theorem emX_bk (x : XP P) (b : Bl K) (s : Bool) :
    emX P x (tp (.bk b) s) = emU x.sort (tp (.bk b) s) := by
  simp [emX, emIn, emCt, emSt, emEd, emAp, on, mem_rgs, flatMap_const_nil]

theorem emX_cm (x : XP P) (k s : Bool) :
    emX P x (tp (.cm k) s) = emU x.sort (tp (.cm k) s) := by
  simp [emX, emIn, emCt, emSt, emEd, emAp, on, mem_rgs, flatMap_const_nil]

theorem emX_inp (x : XP P) :
    emX P x (.inp ()) = (x.steps.flatMap fun s => (P.rd s.1).toList).map .bit := by
  rw [emX_simp_other _ (by simp) (by simp) (by simp) (by simp)]
  simp [emIn, emCt, emSt, emEd, emAp, on, mem_rgs, List.map_flatMap, flatMap_const_nil]

/-- The decoded tape-matching conditions for a run `x : XP P` on input `bits`. -/
structure MX (x : XP P) (bits : List Bool) : Prop where
  /-- register tape values chain from `0` to `finalRegs` -/
  rg : ∀ i, i0 x.init :: x.steps.map (fun s => cw s.2 (P.dr s.1 i)) =
    x.steps.map (fun s => cw s.2 (rv i)) ++ [x.finalRegs.map fun v => v i]
  /-- mode tape chains from `P.m0` to `P.mh` -/
  md : P.m0 :: x.steps.map (fun s => P.dst s.1) = x.steps.map (fun s => P.src s.1) ++ [P.mh]
  /-- counter tape increments from `1` to `true :: finalCounter` -/
  cp : i1 x.init :: x.counter.map cn1 = x.counter.map cn ++ [true :: x.finalCounter]
  /-- fresh addresses emitted in `steps` match the counter words -/
  fr : x.counter.map cn = x.steps.map fun s => cw s.2 8
  /-- lookup word copied onto `lsF` matches the lookup tape -/
  lk : x.lookups = encW ((lks x).map fun c => (true, oc c))
  /-- sorting loop `x.sort` matches the encoded `(defs ++ lookups)` record list -/
  ls : IMU x.sort
    (encW ((dfs x).map (fun c => (false, oc c)) ++ (lks x).map fun c => (true, oc c)))
  /-- concatenated input bits consumed by `steps` equal `bits` -/
  inp : (x.steps.flatMap fun s => (P.rd s.1).toList) = bits

theorem mt_X (x : XP P) (bits : List Bool) :
    Mt (emX P) (fun _ => bits.map .bit) x ↔ MX x bits := by
  have hmd : Function.Injective (Sy.md : M → Sy M K) := fun _ _ e => by simpa using e
  have hbit : Function.Injective (Sy.bit : Bool → Sy M K) := fun _ _ e => by simpa using e
  constructor
  · rintro ⟨h1, h2⟩
    have hlk : x.lookups = encW ((lks x).map fun c => (true, oc c)) := by
      simpa only [emX_lk_false, emX_lk_true] using (h1 .lk).symm
    exact ⟨fun i => bws_inj (by simpa only [emX_rg_false, emX_rg_true] using h1 (.rg i)),
      List.map_injective_iff.2 hmd (by simpa only [emX_md_false, emX_md_true] using h1 .md),
      bws_inj (by simpa only [emX_cp_false, emX_cp_true] using h1 .cp),
      bws_inj (by simpa only [emX_fr_false, emX_fr_true] using h1 .fr),
      hlk,
      ⟨by simpa only [emX_ls_false, emX_ls_true, hlk, ← List.append_assoc, ← encW_append]
          using h1 .ls,
        fun b => by simpa only [emX_bk] using h1 (.bk b),
        fun k => by simpa only [emX_cm] using h1 (.cm k)⟩,
      List.map_injective_iff.2 hbit (by simpa only [emX_inp] using h2 ())⟩
  · rintro ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, h9⟩
    refine ⟨fun s => ?_, fun ⟨⟩ => by rw [emX_inp, h9]⟩
    cases s <;> simp [emX_rg_false, emX_rg_true, emX_md_false, emX_md_true, emX_cp_false,
      emX_cp_true, emX_fr_false, emX_fr_true, emX_lk_false, emX_lk_true, emX_ls_false,
      emX_ls_true, emX_bk, emX_cm, ← List.append_assoc, ← encW_append, *]

end EmX

end Cslib.Circuits.Arithmetic.Separation.Uni
