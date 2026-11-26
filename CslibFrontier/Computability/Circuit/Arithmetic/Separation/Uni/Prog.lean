/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.SpecU2
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.PM

/-!
# A tape program simulating a pointer machine

Constructs the structured-run tape program `Uni.emX P` (and its rational-series realization
`Uni.runs_X` of dimension `Uni.dimX P`) simulating a pointer machine `P : Mach A M K`. The run
type `Uni.XP P` is a record with named fields covering all six simulation phases: initialization,
counter increments, bit-sliced steps, final register/counter tail, lookup append, and the
universal radix-sorting / neighbour-comparison loop `Uni.XU`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.Prog`.

## Main definitions

* `Uni.bw`, `Uni.cont`, `Uni.rec'`: bit words and encoded records on tapes.
* `Uni.tp`, `Uni.rgs`: side-of-tape channel helper and register tape set.
* `Uni.cn`, `Uni.cn1`, `Uni.emCt`: counter-increment round emissions.
* `Uni.i0`, `Uni.i1`, `Uni.emIn`: initial words (`0` registers, `1` counter, initial record).
* `Uni.cw`, `Uni.ldc`, `Uni.alc`, `Uni.rgw`, `Uni.emSt`, `Uni.dimSt`: bit-sliced step emissions.
* `Uni.emEd`, `Uni.ed1`, `Uni.emAp`: halting tail and lookup append phase.
* `Uni.XP`, `Uni.emX`, `Uni.dimX`: structured simulation run record and full emission map.

## Main results

* `Uni.runs_rep`, `Uni.runs_ct`, `Uni.runs_in`, `Uni.runs_st`, `Uni.runs_ed`, `Uni.runs_ap`.
* `Uni.runs_X`: bounded-dimension rational realization of the full universal program `emX P`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Cslib.Automata.Weighted Cslib.Circuits.Arithmetic.Separation.Tape

/-- A tape-encoded binary word terminated by a semicolon `semi`. -/
@[expose] def bw {M K : Type} (w : List Bool) : List (Sy M K) := w.map .bit ++ [.semi]

/-- Record content as a key-letter list: leading kind letter followed by bit-slice columns. -/
@[expose] def cont {K : Type} (κ : K) (cs : List (Fin 4 → Bool)) : List (Bl K) :=
  .inl κ :: cs.map .inr

/-- A record serialized onto a tape with leading flag `f` and trailing rotation mark. -/
@[expose] def rec' {M K : Type} (f : Bool) (κ : K) (cs : List (Fin 4 → Bool)) : List (Sy M K) :=
  rw' f ((cont κ cs).map some ++ [none])

theorem rec'_eq {M K : Type} (f : Bool) (κ : K) (cs : List (Fin 4 → Bool)) :
    (rec' f κ cs : List (Sy M K)) = .flag f :: .kd κ :: (cs.map .col ++ [.mark, .dot]) := by
  simp [rec', rw', cont, ol, be, List.map_map, Function.comp_def]

/-- Channel corresponding to side `b` of tape `s`. -/
abbrev tp {K : Type} (s : Tp K) (b : Bool) : Zc K := .tp s b

/-- The five register-tape channels on side `b`. -/
@[expose] def rgs {K : Type} [DecidableEq K] (b : Bool) : Finset (Zc K) :=
  univ.image fun i => tp (.rg i) b

theorem mem_rgs {K : Type} [DecidableEq K] (b : Bool) (z : Zc K) :
    z ∈ rgs b ↔ ∃ i, z = tp (.rg i) b := by
  simp [rgs, eq_comm]

private theorem card_rgs {K : Type} [DecidableEq K] (b : Bool) :
    (rgs (K := K) b : Finset (Zc K)).card = 5 := by
  rw [rgs, card_image_of_injective _ fun _ _ h => by simpa using h, card_univ, Fintype.card_fin]

private theorem flatMap_unit {γ : Type*} (l : List Unit) (a : γ) :
    (l.flatMap fun _ => [a]) = List.replicate l.length a := by
  induction l <;> simp [List.replicate_succ, *]

/-- Repeat a fixed non-empty channel emission `w` arbitrarily many times. -/
theorem runs_rep {A : Type*} [CommRing A] {M K : Type} [Finite M] [Fintype K] [DecidableEq K]
    (w : Zc K → List (Sy M K)) (hw : ∃ z, w z ≠ []) :
    Runs (2 * ∑ z, (w z).length + 1 + 1)
      (fun (l : List Unit) z => l.flatMap fun _ => w z) (fun _ => (1 : A)) := by
  classical
  exact ((Runs.const (F := A) w).kstar fun _ => hw).congr (Equiv.refl _) (fun _ _ => rfl)
    fun _ => by simp

/-- Counter value before an increment: `u ++ false :: true^k`. -/
@[expose] def cn (r : List Bool × List Unit) : List Bool :=
  r.1 ++ false :: List.replicate r.2.length true

/-- Counter value after an increment: `u ++ true :: false^k`. -/
@[expose] def cn1 (r : List Bool × List Unit) : List Bool :=
  r.1 ++ true :: List.replicate r.2.length false

/-- Emissions of one round of the binary counter increment phase. -/
@[expose] def emCt {M K : Type} [DecidableEq K] (r : List Bool × List Unit) :
    Zc K → List (Sy M K) := fun z =>
  on {tp .cp true, tp .fr false} (bw (cn r)) z ++ on {tp .cp false} (bw (cn1 r)) z

theorem runs_ct {A : Type*} [CommRing A] {M K : Type} [Finite M] [Fintype K] [DecidableEq K] :
    Runs 60 (emCt : List Bool × List Unit → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hc : ({tp .cp true, tp .fr false, tp .cp false} : Finset (Zc K)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
  have hc2 : ({tp .cp true, tp .fr false} : Finset (Zc K)).card = 2 :=
    Finset.card_pair (by simp)
  have h1 := Runs.wordstar (F := A) (Z := Zc K) {tp .cp true, tp .fr false, tp .cp false}
    ⟨tp .cp true, by simp⟩ (fun b : Bool => (Sy.bit b : Sy M K))
  have h2 := Runs.const (F := A) fun z : Zc K =>
    on {tp .cp true, tp .fr false} [(Sy.bit false : Sy M K)] z ++
      on {tp .cp false} [Sy.bit true] z
  have h3 := runs_rep (A := A) (M := M) (K := K)
    (fun z : Zc K => on {tp .cp true, tp .fr false} [(Sy.bit true : Sy M K)] z ++
      on {tp .cp false} [Sy.bit false] z)
    ⟨tp .cp false, by simp [on]⟩
  have h4 := Runs.word (F := A) (Z := Zc K) {tp .cp true, tp .fr false, tp .cp false}
    [(Sy.semi : Sy M K)]
  refine ((((h1.mul h2).mul h3).mul h4).congr
    ⟨fun r => (((r.1, ()), r.2), ()), fun (((w, _), l), _) => (w, l),
      fun _ => rfl, fun _ => rfl⟩
    (fun r z => ?_) fun _ => by simp).mono ?_
  · obtain ⟨w, l⟩ := r
    rcases eq_or_ne z (tp .cp true) with rfl | h1
    · simp [emCt, cn, bw, on, flatMap_unit]
    rcases eq_or_ne z (tp .fr false) with rfl | h2
    · simp [emCt, cn, bw, on, flatMap_unit]
    rcases eq_or_ne z (tp .cp false) with rfl | h3
    · simp [emCt, cn1, bw, on, flatMap_unit]
    simp [emCt, on, h1, h2, h3]
  · simp only [List.length_append, Finset.sum_add_distrib, sum_on, hc, hc2]
    simp

/-- Initial register word: `0` of length `l.length + 1`. -/
@[expose] def i0 (l : List Unit) : List Bool := List.replicate (l.length + 1) false

/-- Initial fresh-address word: `1` of length `l.length + 1`. -/
@[expose] def i1 (l : List Unit) : List Bool := List.replicate l.length false ++ [true]

/-- Emissions at program initialization (initial registers, counter `1`, record `0`, mode `m0`). -/
@[expose] def emIn {M K : Type} [DecidableEq K] (m0 : M) (kN : K) (l : List Unit) :
    Zc K → List (Sy M K) := fun z =>
  on (rgs false) (bw (i0 l)) z ++ on {tp .cp false} (bw (i1 l)) z ++
    on {lsF} (rec' false kN (List.replicate (l.length + 1) fun _ => false)) z ++
    on {tp .md false} [.md m0] z

theorem runs_in {A : Type*} [CommRing A] {M K : Type} [Finite M] [Fintype K] [DecidableEq K]
    (m0 : M) (kN : K) :
    Runs 80 (emIn m0 kN : List Unit → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h1 := Runs.const (F := A) fun z : Zc K =>
    on {lsF} [(Sy.flag false : Sy M K), .kd kN] z ++ on {tp .md false} [.md m0] z
  have h2 := runs_rep (A := A) (M := M) (K := K)
    (fun z : Zc K => on (insert (tp .cp false) (rgs false)) [(Sy.bit false : Sy M K)] z ++
      on {lsF} [.col fun _ => false] z)
    ⟨lsF, by simp [on, mem_rgs]⟩
  have h3 := Runs.const (F := A) fun z : Zc K =>
    on (rgs false) [(Sy.bit false : Sy M K), .semi] z ++
      on {tp .cp false} [.bit true, .semi] z ++
      on {lsF} [.col fun _ => false, .mark, .dot] z
  refine (((h1.mul h2).mul h3).congr
    ⟨fun l => (((), l), ()), fun ((_, l), _) => l, fun _ => rfl, fun _ => rfl⟩
    (fun l z => ?_) fun _ => by simp).mono ?_
  · by_cases h1 : z ∈ rgs false
    · obtain ⟨i, rfl⟩ := (mem_rgs _ _).1 h1
      simp [emIn, i0, bw, on, mem_rgs, flatMap_unit, List.replicate_succ']
    rcases eq_or_ne z (tp .cp false) with rfl | h2
    · simp [emIn, i1, bw, on, mem_rgs, flatMap_unit]
    rcases eq_or_ne z lsF with rfl | h3
    · simp [emIn, rec'_eq, on, mem_rgs, flatMap_unit, List.replicate_succ']
    simp [emIn, on, h1, h2, h3]
  · have hc : (insert (tp .cp false) (rgs false) : Finset (Zc K)).card = 6 := by
      rw [Finset.card_insert_of_notMem (by simp [mem_rgs]), card_rgs]
    simp only [List.length_append, Finset.sum_add_distrib, sum_on, hc, card_rgs]
    simp

section Steps

variable {A : Type} {M K : Type} (P : Mach A M K)

/-- Extract the bit word of step variable `i : Fin 9` from a column list. -/
@[expose] def cw (w : List (Fin 9 → Bool)) (i : Fin 9) : List Bool := w.map fun v => v i

/-- Bit-slice columns of the record loaded by rule `r`. -/
@[expose] def ldc (r : P.Rl) (w : List (Fin 9 → Bool)) : List (Fin 4 → Bool) :=
  w.map fun v => ![v (rv (P.la r)), v 5, v 6, v 7]

/-- Bit-slice columns of the record allocated by rule `r`. -/
@[expose] def alc (r : P.Rl) (w : List (Fin 9 → Bool)) : List (Fin 4 → Bool) :=
  w.map fun v => ![v 8, v (P.af r 0), v (P.af r 1), v (P.af r 2)]

/-- Bit word written by rule `r` onto side `s` of register tape `i`. -/
@[expose] def rgw (s : Bool) (r : P.Rl) (w : List (Fin 9 → Bool)) (i : Fin 5) : List Bool :=
  if s then cw w (rv i) else cw w (P.dr r i)

/-- Complete channel emissions of a single bit-sliced machine step. -/
@[expose] def emSt (x : P.Rl × List (Fin 9 → Bool)) : Zc K → List (Sy M K)
  | .tp (.rg i) s => bw (rgw P s x.1 x.2 i)
  | .tp .md s => [.md (if s then P.src x.1 else P.dst x.1)]
  | .tp .cp _ => []
  | .tp .fr s => if s then bw (cw x.2 8) else []
  | .tp .lk s => if s then [] else rec' true (P.lk x.1) (ldc P x.1 x.2)
  | .tp .ls s => if s then [] else rec' false (P.ak x.1) (alc P x.1 x.2)
  | .tp (.bk _) _ => []
  | .tp (.cm _) _ => []
  | .inp _ => (P.rd x.1).toList.map .bit

/-- Opening header emission of rule `r` before its bit-slice columns. -/
@[expose] def st0 (r : P.Rl) : Zc K → List (Sy M K)
  | .tp .md s => [.md (if s then P.src r else P.dst r)]
  | .tp .lk s => if s then [] else [.flag true, .kd (P.lk r)]
  | .tp .ls s => if s then [] else [.flag false, .kd (P.ak r)]
  | .inp _ => (P.rd r).toList.map .bit
  | _ => []

/-- Single bit-slice column emission of rule `r` at bit vector `v`. -/
@[expose] def st1 (r : P.Rl) (v : Fin 9 → Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => [.bit (if s then v (rv i) else v (P.dr r i))]
  | .tp .fr s => if s then [.bit (v 8)] else []
  | .tp .lk s => if s then [] else [.col ![v (rv (P.la r)), v 5, v 6, v 7]]
  | .tp .ls s => if s then [] else [.col ![v 8, v (P.af r 0), v (P.af r 1), v (P.af r 2)]]
  | _ => []

/-- Closing terminator emission of a step after its bit-slice columns. -/
@[expose] def st2 : Zc K → List (Sy M K)
  | .tp (.rg _) _ => [.semi]
  | .tp .fr s => if s then [.semi] else []
  | .tp .lk s => if s then [] else [.mark, .dot]
  | .tp .ls s => if s then [] else [.mark, .dot]
  | _ => []

private theorem emSt_eq (x : P.Rl × List (Fin 9 → Bool)) (z : Zc K) :
    st0 P x.1 z ++ (x.2.flatMap (fun v => st1 P x.1 v z) ++ st2 z) = emSt P x z := by
  obtain ⟨r, w⟩ := x
  cases z with
  | tp s b =>
    cases s <;> cases b <;>
      simp [st0, st1, st2, emSt, rgw, bw, cw, rec'_eq, ldc, alc, ← List.map_eq_flatMap,
        List.map_map, Function.comp_def]
  | inp _ => simp [st0, st1, st2, emSt]

private theorem st1_ne (r : P.Rl) (v : Fin 9 → Bool) : ∃ z, st1 P r v z ≠ [] :=
  ⟨tp .fr true, by simp [st1]⟩

/-- Dimension upper bound for the single-step automaton of `P`. -/
@[expose] def dimSt [Fintype K] : ℕ :=
  ∑ r : P.Rl,
    (2 * ∑ z, (st0 P r z).length + 1 +
      ((∑ v : Fin 9 → Bool, (2 * ∑ z, (st1 P r v z).length + 1)) + 1 +
        (2 * ∑ z, ((st2 z : List (Sy M K))).length + 1)))

theorem runs_st [CommRing A] [Finite M] [Fintype K] [DecidableEq K] :
    Runs (dimSt P) (emSt P : P.Rl × List (Fin 9 → Bool) → Zc K → List (Sy M K))
      (fun x => P.wt x.1) := by
  classical
  have h := Runs.sum (F := A) fun r : P.Rl =>
    (Runs.pick (F := A) (fun _ : Unit => st0 P r) fun _ => P.wt r).mul
      (((Runs.pick (F := A) (fun v : Fin 9 → Bool => st1 P r v) fun _ => 1).kstar
          fun v => st1_ne P r v).mul
        (Runs.const (F := A) (st2 : Zc K → List (Sy M K))))
  exact (h.congr
    ⟨fun x => ⟨x.1, ((), x.2, ())⟩, fun ⟨r, (_, w, _)⟩ => (r, w), fun _ => rfl, fun _ => rfl⟩
    (fun x z => emSt_eq P x z) fun _ => by simp).mono (Finset.sum_le_sum fun _ _ => by simp)

end Steps

/-- Emissions at program termination: final registers, halting mode `mh`, and `true :: u` on the
counter read side. -/
@[expose] def emEd {M K : Type} (mh : M) (x : List (Fin 5 → Bool) × List Bool) :
    Zc K → List (Sy M K)
  | .tp (.rg i) s => if s then bw (x.1.map fun v => v i) else []
  | .tp .md s => if s then [.md mh] else []
  | .tp .cp s => if s then bw (true :: x.2) else []
  | _ => []

/-- Single final-register bit-slice emission. -/
@[expose] def ed1 {M K : Type} (v : Fin 5 → Bool) : Zc K → List (Sy M K)
  | .tp (.rg i) s => if s then [.bit (v i)] else []
  | _ => []

theorem runs_ed {A : Type*} [CommRing A] {M K : Type} [Finite M] [Fintype K] [DecidableEq K]
    (mh : M) :
    Runs ((∑ v : Fin 5 → Bool, (2 * ∑ z, (ed1 v z : List (Sy M K)).length + 1)) + 1 + 30)
      (emEd mh : List (Fin 5 → Bool) × List Bool → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  classical
  have h1 := (Runs.pick (F := A) (fun v : Fin 5 → Bool => (ed1 v : Zc K → List (Sy M K)))
    fun _ => 1).kstar fun _ => ⟨tp (.rg 0) true, by simp [ed1]⟩
  have h2 := Runs.const (F := A) fun z : Zc K =>
    on (rgs true) [(Sy.semi : Sy M K)] z ++
      on {tp .md true} [.md mh] z ++ on {tp .cp true} [.bit true] z
  have h3 := Runs.wordstar (F := A) (Z := Zc K) {tp .cp true} ⟨tp .cp true, by simp⟩
    (fun b : Bool => (Sy.bit b : Sy M K))
  have h4 := Runs.word (F := A) (Z := Zc K) {tp .cp true} [(Sy.semi : Sy M K)]
  refine ((((h1.mul h2).mul h3).mul h4).congr
    ⟨fun x => (((x.1, ()), x.2), ()), fun (((w, _), u), _) => (w, u),
      fun _ => rfl, fun _ => rfl⟩
    (fun x z => ?_) fun _ => by simp).mono ?_
  · obtain ⟨w, u⟩ := x
    match z with
    | .tp (.rg i) true =>
      simp [ed1, emEd, on, mem_rgs, ← List.map_eq_flatMap, bw, List.map_map, Function.comp_def]
    | .tp .cp true => simp [ed1, emEd, on, mem_rgs, bw]
    | .tp (.rg _) false | .tp .md _ | .tp .cp false | .tp .fr _ | .tp .lk _ | .tp .ls _
    | .tp (.bk _) _ | .tp (.cm _) _ | .inp _ => simp [ed1, emEd, on, mem_rgs]
  · simp only [List.length_append, Finset.sum_add_distrib, sum_on, card_rgs]
    simp

/-- Emissions copying the lookup tape onto the list tape followed by the block separator `bar`. -/
@[expose] def emAp {M K : Type} [DecidableEq K] (w : List (Sy M K)) :
    Zc K → List (Sy M K) := fun z =>
  on {tp .lk true, lsF} w z ++ on {lsF} [.bar] z

theorem runs_ap {A : Type*} [CommRing A] {M K : Type} [Fintype M] [Fintype K] [DecidableEq K] :
    Runs (Fintype.card (Sy M K) * 5 + 1 + 3)
      (emAp : List (Sy M K) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := (Runs.wordstar (F := A) (Z := Zc K) {tp .lk true, lsF} ⟨lsF, by simp⟩
    (fun γ : Sy M K => γ)).mul
    (Runs.word (F := A) (Z := Zc K) {lsF} [(Sy.bar : Sy M K)])
  refine (h.congr ⟨fun w => (w, ()), Prod.fst, fun _ => rfl, fun _ => rfl⟩
    (fun w z => by simp [emAp]) fun _ => by simp).mono ?_
  rw [Finset.card_pair (by simp)]
  simp

/-- A complete structured run of the universal tape program simulating pointer machine `P`. -/
@[ext]
structure XP {A : Type} {M K : Type} (P : Mach A M K) where
  /-- unary witness fixing the bit-width `L = init.length + 1` -/
  init : List Unit
  /-- sequence of binary counter increment rounds -/
  counter : List (List Bool × List Unit)
  /-- sequence of bit-sliced machine steps -/
  steps : List (P.Rl × List (Fin 9 → Bool))
  /-- final register values (bit-sliced columns) -/
  finalRegs : List (Fin 5 → Bool)
  /-- tail bits of the halting counter `true :: finalCounter` -/
  finalCounter : List Bool
  /-- copied word of lookup records appended to `lsF` -/
  lookups : List (Sy M K)
  /-- radix-sorting and neighbour-comparison phase run -/
  sort : XU M K

/-- Channel emissions of a full universal tape program run `x : XP P`. -/
@[expose] noncomputable def emX {A M K : Type} [Fintype K] [DecidableEq K]
    (P : Mach A M K) (x : XP P) : Zc K → List (Sy M K) := fun z =>
  emIn P.m0 P.kN x.init z ++
    ((x.counter.flatMap fun r => emCt r z) ++
      ((x.steps.flatMap fun s => emSt P s z) ++
        (emEd P.mh (x.finalRegs, x.finalCounter) z ++
          (emAp x.lookups z ++ emU x.sort z))))

/-- Dimension upper bound for the rational series realizing `emX P`. -/
@[expose] noncomputable def dimX {A M K : Type} [Fintype M] [Fintype K]
    (P : Mach A M K) : ℕ :=
  80 + ((60 + 1) + ((dimSt P + 1) +
    (((∑ v : Fin 5 → Bool, (2 * ∑ z, (ed1 v z : List (Sy M K)).length + 1)) + 1 + 30) +
      ((Fintype.card (Sy M K) * 5 + 1 + 3) +
        dimU (Fintype.card (Sy M K)) (Fintype.card (Bl K))))))

private theorem emSt_ne {A M K : Type} (P : Mach A M K) (x : P.Rl × List (Fin 9 → Bool)) :
    ∃ z, emSt P x z ≠ [] :=
  ⟨tp .md true, by simp [emSt]⟩

theorem runs_X {A : Type} [CommRing A] {M K : Type} [Fintype M] [Fintype K] [DecidableEq K]
    (P : Mach A M K) :
    Runs (dimX P) (emX P : XP P → Zc K → List (Sy M K))
      (fun x => (x.steps.map fun s => P.wt s.1).prod) := by
  have h := (runs_in (A := A) (M := M) (K := K) P.m0 P.kN).mul
    (((runs_ct (A := A) (M := M) (K := K)).kstar
        fun r => ⟨tp .cp true, by simp [emCt, on, bw]⟩).mul
      (((runs_st P).kstar fun s => emSt_ne P s).mul
        ((runs_ed (A := A) (M := M) (K := K) P.mh).mul
          ((runs_ap (A := A) (M := M) (K := K)).mul
            (runs_U (A := A) (M := M) (K := K))))))
  refine h.congr
    ⟨fun x => (x.init, x.counter, x.steps, (x.finalRegs, x.finalCounter), x.lookups, x.sort),
     fun (i, c, s, (fr, fc), l, u) => ⟨i, c, s, fr, fc, l, u⟩,
     fun _ => rfl, fun _ => rfl⟩
    (fun _ _ => rfl) fun _ => by simp

end Cslib.Circuits.Arithmetic.Separation.Uni
