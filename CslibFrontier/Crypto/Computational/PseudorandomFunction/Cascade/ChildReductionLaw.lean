/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildReduction
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.FiniteChildTable
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Fixed-channel law for the cascade child challenge

With the challenge channel, external function, and key word fixed, the simulated child oracle
has the same output law as an eager table. Earlier channels read independent uniform
functions, the selected channel reads the external function, and later channels evaluate
the keyed family. The law holds for adaptive clients with private coins.

## Main results

* `Cslib.Crypto.evalWith_cascadeChildChallengeAtProgram_eq_eager`: the fixed-channel output law.
  Averaging over the challenge channel and key draws and certifying strict oracle PPT are
  separate steps toward the reduction in #5801.

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid argument.
-/

public section

namespace Cslib.Crypto

open Probability

private abbrev Point (count width : ℕ) := Fin count × BitString width

/-- The first-use cursor paired with either the lazy cache or the completed table. -/
private structure TableState (Table : Type) where
  /-- Number of channels assigned so far. -/
  assigned : ℕ
  /-- The retained ideal entries. -/
  table : Table

private abbrev LazyState (count width n : ℕ) :=
  TableState (List (Point count width × BitString n))

private abbrev EagerState (count width n : ℕ) :=
  TableState (Point count width → BitString n)

private def keyEncoding (count width : ℕ) : Point count width ↪ ℕ × List Bool :=
  ⟨fun p => (p.1.val, List.ofFn p.2), fun _ _ h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (List.ofFn_injective (congrArg Prod.snd h))⟩

private def represent {count width n : ℕ} (s : LazyState count width n) :
    CascadeChildChallengeState :=
  ⟨s.assigned, s.table.map fun entry => (keyEncoding count width entry.1, List.ofFn entry.2)⟩

private def challengeTable {count width n : ℕ}
    (family : List Bool → List Bool → List Bool) (selected : Fin count) (keys : List Bool)
    (challenge : BitString width → BitString n) (ideal : Point count width → BitString n)
    (channel : Fin count) (block : BitString width) : BitString n :=
  if channel < selected then ideal (channel, block)
  else if channel = selected then challenge block
  else BitString.ofList n (family (BitString.listRow n channel.val keys) (List.ofFn block))

private noncomputable def lazyChild {count width n : ℕ}
    (family : List Bool → List Bool → List Bool) (selected : Fin count) (keys : List Bool)
    (challenge : BitString width → BitString n) (request : ℕ × List Bool) :
    StateT (LazyState count width n) PMF (List Bool) := fun s =>
  if h : request.1 < count ∧ request.1 ≤ s.assigned then
    let channel : Fin count := ⟨request.1, h.1⟩
    let block := BitString.ofList width request.2
    let next := max s.assigned (request.1 + 1)
    if channel < selected then
      (memoize (fun _ => PMF.uniformOfFintype (BitString n)) (channel, block) s.table).map
        (fun x => (List.ofFn x.1, ⟨next, x.2⟩))
    else PMF.pure
      (List.ofFn (challengeTable family selected keys challenge (fun _ _ => false) channel block),
        ⟨next, s.table⟩)
  else PMF.pure ([], s)

private noncomputable def eagerChild {count width n : ℕ}
    (family : List Bool → List Bool → List Bool) (selected : Fin count) (keys : List Bool)
    (challenge : BitString width → BitString n) (request : ℕ × List Bool) :
    StateT (EagerState count width n) PMF (List Bool) := fun s =>
  (cascadeChildFiniteOracle (challengeTable family selected keys challenge s.table)
    request s.assigned).map (fun x => (x.1, ⟨x.2, s.table⟩))

private noncomputable def completeTable {count width n : ℕ} (s : LazyState count width n) :
    PMF (EagerState count width n) :=
  (RandomOracle.complete (fun _ => PMF.uniformOfFintype (BitString n))
    (RandomOracle.ofList s.table)).map (fun table => ⟨s.assigned, table⟩)

private theorem lazyChild_repr {count width n : ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key block, key.length = n → block.length = width →
      (family key block).length = n)
    (selected : Fin count) (keys : List Bool) (challenge : BitString width → BitString n)
    (request : ℕ × List Bool) (s : LazyState count width n) :
    (lazyChild family selected keys challenge request s).map
        (fun x => (x.1, represent x.2)) =
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle width challenge req.2)))
        (cascadeChildChallengeHandler family width n count selected.val keys request
          (represent s)) := by
  by_cases hg : request.1 < count ∧ request.1 ≤ s.assigned
  · let channel : Fin count := ⟨request.1, hg.1⟩
    let block := BitString.ofList width request.2
    let point : Point count width := (channel, block)
    have hblock : BitString.listRow width 0 request.2 = List.ofFn block :=
      BitString.listRow_zero _ _
    simp only [lazyChild, cascadeChildChallengeHandler, dite_eq_left hg, hblock,
      show (represent s).assigned = s.assigned from rfl, ite_eq_left hg]
    by_cases hlt : channel < selected
    · have hlt' : request.1 < selected.val := hlt
      rw [ite_eq_left hlt, ite_eq_left hlt']
      rw [OracleComp.evalWith_bind, ProbOracleComp.evalWith_sumHandler_unifOracle_sample]
      simp only [OracleComp.evalWith_pure, ProbComp.eval_memoize,
        BitString.eval_sampleList, PMF.map_comp, Function.comp_def]
      have hmemo := memoize_map (m := PMF) (keyEncoding count width) List.ofFn
        (fun _ => PMF.uniformOfFintype (BitString n)) (fun _ => BitString.uniformList n)
        (fun _ => rfl) point s.table
      have hpoint : keyEncoding count width point = (request.1, List.ofFn block) := rfl
      rw [hpoint] at hmemo
      simpa only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, represent, point,
        channel, block, PMF.map, PMF.bind_bind, PMF.pure_bind] using
        congrArg (PMF.map fun x =>
          (x.1, CascadeChildChallengeState.mk (max s.assigned (request.1 + 1)) x.2)) hmemo
    · have hlt' : ¬ request.1 < selected.val := hlt
      rw [ite_eq_right hlt, ite_eq_right hlt', PMF.pure_map]
      change ¬ (⟨request.1, hg.1⟩ : Fin count) < selected at hlt
      by_cases heq : channel = selected
      · have heq' : request.1 = selected.val := congrArg Fin.val heq
        change (⟨request.1, hg.1⟩ : Fin count) = selected at heq
        simp only [challengeTable, ite_eq_right hlt, ite_eq_left heq, ite_eq_left heq',
          OracleComp.evalWith_bind, ProbOracleComp.evalWith_sumHandler_query,
          randomFunctionOracle, List.length_ofFn, ↓reduceIte, BitString.ofList_ofFn,
          PMF.pure_bind, OracleComp.evalWith_pure, List.take_of_length_le List.length_ofFn.le]
        rfl
      · have heq' : request.1 ≠ selected.val := fun h => heq (Fin.ext h)
        change (⟨request.1, hg.1⟩ : Fin count) ≠ selected at heq
        have hlen := hlength (BitString.listRow n request.1 keys) (List.ofFn block)
          (BitString.length_listRow _ _ _) List.length_ofFn
        dsimp only [block] at hlen ⊢
        simp only [challengeTable, ite_eq_right hlt, ite_eq_right heq, ite_eq_right heq',
          OracleComp.evalWith_pure,
          BitString.ofFn_ofList hlen, List.take_of_length_le hlen.le]
        rfl
  · simp only [lazyChild, dite_eq_right hg, cascadeChildChallengeHandler,
      show (represent s).assigned = s.assigned from rfl, ite_eq_right hg,
      PMF.pure_map, OracleComp.evalWith_pure]

private theorem lazyChild_complete {count width n : ℕ}
    (family : List Bool → List Bool → List Bool) (selected : Fin count) (keys : List Bool)
    (challenge : BitString width → BitString n) (request : ℕ × List Bool)
    (s : LazyState count width n) :
    (lazyChild family selected keys challenge request s).bind
        (fun x => (completeTable x.2).map (x.1, ·)) =
      (completeTable s).bind (eagerChild family selected keys challenge request) := by
  by_cases hg : request.1 < count ∧ request.1 ≤ s.assigned
  · let channel : Fin count := ⟨request.1, hg.1⟩
    let block := BitString.ofList width request.2
    let point : Point count width := (channel, block)
    let next := max s.assigned (request.1 + 1)
    by_cases hlt : channel < selected
    · have h := congrArg (PMF.map fun x : BitString n × (Point count width → BitString n) =>
        (List.ofFn x.1, (⟨next, x.2⟩ : EagerState count width n)))
        (RandomOracle.answer_complete (fun _ => PMF.uniformOfFintype (BitString n))
          (RandomOracle.ofList s.table) point)
      rw [← RandomOracle.memoize_map_ofList] at h
      simp only [PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def] at h
      simpa only [lazyChild, eagerChild, cascadeChildFiniteOracle, completeTable,
        dite_eq_left hg, ite_eq_left hlt, challengeTable, PMF.bind_map, PMF.pure_map, PMF.map,
        PMF.bind_bind, PMF.pure_bind, Function.comp_def, point, channel, block, next] using h
    · change ¬ (⟨request.1, hg.1⟩ : Fin count) < selected at hlt
      simp only [lazyChild, eagerChild, cascadeChildFiniteOracle, completeTable,
        dite_eq_left hg, ite_eq_right hlt, challengeTable, PMF.pure_bind, PMF.bind_map,
        PMF.map_comp, PMF.pure_map, Function.comp_def]
      rfl
  · simp only [lazyChild, eagerChild, cascadeChildFiniteOracle, completeTable,
      dite_eq_right hg, PMF.pure_bind, PMF.bind_map, PMF.map_comp, PMF.pure_map, Function.comp_def]
    rfl

/-- Fixed-channel step of the cascade reduction. For a width-preserving keyed family, running the
word program against a fixed challenge function gives the eager finite-table law with independent
uniform earlier rows, the supplied challenge row, and later rows keyed from `keys`. -/
theorem evalWith_cascadeChildChallengeAtProgram_eq_eager {count width n : ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key block, key.length = n → block.length = width →
      (family key block).length = n)
    (selected : Fin count) (keys : List Bool) (challenge : BitString width → BitString n)
    (program : WordOracleComp ℕ Bool) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle width challenge req.2)))
        (cascadeChildChallengeAtProgram family width n count selected.val keys program) =
      (PMF.uniformOfFintype (Fin count × BitString width → BitString n)).bind fun ideal =>
        let table (channel : Fin count) (block : BitString width) :=
          if channel < selected then ideal (channel, block)
          else if channel = selected then challenge block
          else BitString.ofList n (family (BitString.listRow n channel.val keys) (List.ofFn block))
        (ProbOracleComp.runWith (cascadeChildFiniteOracle table) program 0).map Prod.fst := by
  let start : LazyState count width n := ⟨0, []⟩
  let oracle (req : Unit × List Bool) := PMF.pure (randomFunctionOracle width challenge req.2)
  have hrepr := ProbOracleComp.runWith_map_state (lazyChild family selected keys challenge)
    (fun request s => OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      (cascadeChildChallengeHandler family width n count selected.val keys request s))
    represent (lazyChild_repr family hlength selected keys challenge) program start
  have hrun := congrArg (PMF.map Prod.fst) hrepr
  simp only [PMF.map_comp, Function.comp_def] at hrun
  unfold cascadeChildChallengeAtProgram
  rw [OracleComp.evalWith_map, ProbOracleComp.evalWith_run_interpret]
  change (ProbOracleComp.runWith (fun req s =>
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      (cascadeChildChallengeHandler family width n count selected.val keys req s))
      program (represent start)).map Prod.fst = _
  rw [← hrun]
  have hcomplete := ProbOracleComp.runWith_simulation (lazyChild family selected keys challenge)
    (eagerChild family selected keys challenge) completeTable
    (lazyChild_complete family selected keys challenge) program start
  have hproject : (ProbOracleComp.runWith (lazyChild family selected keys challenge)
      program start).map Prod.fst = (completeTable start).bind fun table =>
        (ProbOracleComp.runWith (eagerChild family selected keys challenge) program table).map
          Prod.fst := by
    simpa only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const] using
      congrArg (PMF.map Prod.fst) hcomplete
  rw [hproject, completeTable, PMF.bind_map]
  simp only [start, RandomOracle.ofList_nil, RandomOracle.complete_empty, PMF.pi_uniformOfFintype]
  congr 1 with table : 1
  have htable := ProbOracleComp.runWith_map_state_of_invariant
    (eagerChild family selected keys challenge)
    (cascadeChildFiniteOracle (challengeTable family selected keys challenge table))
    TableState.assigned (fun s => s.table = table) (fun req s hs a s' hmem => by
      simp only [eagerChild, PMF.mem_support_map_iff] at hmem
      obtain ⟨⟨_, _⟩, _, heq⟩ := hmem
      exact (congrArg TableState.table (Prod.mk.inj heq).2).symm.trans hs)
    (fun req s hs => by
      simp only [eagerChild, hs, PMF.map_comp, Function.comp_def]
      exact PMF.map_id _)
    program (⟨0, table⟩ : EagerState count width n) rfl
  have hout := congrArg (PMF.map Prod.fst) htable
  simp only [PMF.map_comp, Function.comp_def] at hout
  exact hout

end Cslib.Crypto
