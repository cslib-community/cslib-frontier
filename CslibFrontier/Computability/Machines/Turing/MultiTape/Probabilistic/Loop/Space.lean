/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential.CoinTape

/-!
# Round-independent workspace bounds for `repeatUntilBlank`

Every round of a `RunsWords` phase starts from a `wordsCfg` (where every work-tape head sits at
position `0`), runs for at most `t` steps (moving each head by at most `1` cell per step, so all
heads stay in `window t`), and halts in a `wordsCfg` (returning all work-tape heads back to `0`).
Repeating such a phase any number of `rounds` via `Turing.MultiTapePTM.repeatUntilBlank` therefore
keeps every work-tape head inside `window t` along every prefix of every branch, regardless of how
large `rounds` is.

## Main results

* `Turing.MultiTapePTM.workTapePos_runsWords_mem_window`: a closed `RunsWords` phase of time `t`
  keeps every work-tape head in `window t` along every fixed-coin replay.
* `Turing.MultiTapePTM.workTapePos_repeatUntilBlank_mem_window`: `repeatUntilBlank` of a closed
  `RunsWords` loop body of per-round time `t` keeps every work-tape head in `window t` for any
  number of rounds.
* `Turing.MultiTapePTM.runsInSpace_toNTM_seq_repeatUntilBlank`: sequencing an initial `RunsWords`
  preparation (`t₁`), `repeatUntilBlank` (`t` per round), and a final `RunsWords` phase (`t₂`) runs
  in nondeterministic workspace `k * (2 * max t₁ (max t t₂) + 1)`, independent of `rounds`.
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM

section Helpers

variable {k : ℕ} {State : Type} {x : List Bool}

private theorem natAbs_workTapePos_step_le (M : MultiTapePTM k Bool State) (bit : Bool)
    (c : Config k Bool State Empty x) (j : Fin k) :
    (((M.withCoin bit).step c).tapes.workTapePos j).natAbs ≤
      (c.tapes.workTapePos j).natAbs + 1 := by
  cases hs : c.tapes.state with
  | none => simp only [MultiTapeMachine.step, hs]; omega
  | some q =>
    simp only [MultiTapeMachine.step, withCoin, hs]
    cases htr : M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
    | step action symbol move =>
      change ((action.apply c.tapes).workTapePos j).natAbs ≤ (c.tapes.workTapePos j).natAbs + 1
      have hmove := abs_le.mp (workTapePos_apply_le action c.tapes j)
      omega
    | query op _ => exact op.elim

private theorem natAbs_workTapePos_replay_le (M : MultiTapePTM k Bool State)
    (coins : List Bool) (c : Config k Bool State Empty x)
    (hzero : ∀ j, c.tapes.workTapePos j = 0) (j : Fin k) :
    ((M.runClosedConfigFromCoins coins c).tapes.workTapePos j).natAbs ≤ coins.length := by
  suffices ∀ (cs : List Bool) (cfg : Config k Bool State Empty x),
      ((M.runClosedConfigFromCoins cs cfg).tapes.workTapePos j).natAbs ≤
        (cfg.tapes.workTapePos j).natAbs + cs.length by
    simpa only [hzero j, Int.natAbs_zero, Nat.zero_add] using this coins c
  intro cs cfg
  induction cs generalizing cfg with
  | nil => simp [runClosedConfigFromCoins]
  | cons bit rest ih =>
    have h1 := natAbs_workTapePos_step_le M bit cfg j
    have h2 := ih ((M.withCoin bit).step cfg)
    simp only [runClosedConfigFromCoins, List.foldl_cons, List.length_cons] at h2 ⊢; omega

private theorem replay_cons (M : MultiTapePTM k Bool State) (bit : Bool) (rest : List Bool)
    (c : Config k Bool State Empty x) :
    M.runClosedConfigFromCoins (bit :: rest) c =
      M.runClosedConfigFromCoins rest ((M.withCoin bit).step c) :=
  rfl


private noncomputable def emptyOracle : Empty × List Bool → StateT Unit PMF (List Bool) :=
  fun q => q.1.elim

/-- Running an oracle configuration with an `Empty` operation signature samples its closed run. -/
theorem runOracleConfigFrom_empty (M : MultiTapePTM k Bool State) (fuel : ℕ)
    (cfg : Config k Bool State Empty x) :
    M.runOracleConfigFrom fuel cfg = ProbOracleComp.sample (M.runClosedConfigFrom fuel cfg) := by
  simp only [runOracleConfigFrom, runClosedConfigFrom, runConfigFrom, ProbOracleComp.sample,
    OracleComp.substitute_eq_interpret, MultiTapeMachine.interpret_runConfigFrom]
  congr 2 with op : 1
  exact op.elim

private theorem runsWords_closed_halted {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t : ℕ}
    {α : Type} {prog : ProbOracleComp (fun _ : Empty × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (M : MultiTapePTM k Bool State)
    (h : M.RunsWords x ws₀ out₀ t prog ws₁ emit)
    (cfg : Config k Bool State Empty x)
    (htapes : cfg.tapes = wordsCfg x (some M.initial) ws₀ out₀) :
    ∀ final ∈ (ProbComp.eval (M.runClosedConfigFrom t cfg)).support,
      final.tapes.state = none := by
  intro final hfinal
  have hh := h.halted emptyOracle () cfg htapes (fun op => op.elim) (final, ())
  rw [runOracleConfigFrom_empty, ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hh
  exact hh ⟨final, hfinal, rfl⟩

private theorem runsWords_closed_completed {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t : ℕ}
    {α : Type} {prog : ProbOracleComp (fun _ : Empty × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (M : MultiTapePTM k Bool State)
    (h : M.RunsWords x ws₀ out₀ t prog ws₁ emit)
    (cfg : Config k Bool State Empty x)
    (htapes : cfg.tapes = wordsCfg x (some M.initial) ws₀ out₀)
    (coins : List Bool)
    (hstate : (M.runClosedConfigFromCoins coins cfg).tapes.state = none) :
    ∃ a, (a, ()) ∈ (ProbOracleComp.runWith emptyOracle prog ()).support ∧
      (M.runClosedConfigFromCoins coins cfg).tapes =
        wordsCfg x none (ws₁ a) (out₀ ++ emit a) := by
  have hmem : (M.runClosedConfigFromCoins coins cfg, ()) ∈
      (ProbOracleComp.runWith emptyOracle (M.runOracleConfigFrom t cfg) ()).support := by
    rw [runOracleConfigFrom_empty, ProbOracleComp.runWith_sample, PMF.mem_support_map_iff]
    exact ⟨_, completed_replay_mem_support M cfg t (runsWords_closed_halted M h cfg htapes)
      coins hstate, rfl⟩
  exact (h.mem_support emptyOracle () cfg htapes (fun op => op.elim) hmem).1

/-- Along any fixed-coin replay of a closed `RunsWords` phase of step bound `t`, every work-tape
head remains in `window t`. -/
theorem workTapePos_runsWords_mem_window {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t : ℕ}
    {α : Type} {prog : ProbOracleComp (fun _ : Empty × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (M : MultiTapePTM k Bool State)
    (h : M.RunsWords x ws₀ out₀ t prog ws₁ emit)
    (cfg : Config k Bool State Empty x)
    (htapes : cfg.tapes = wordsCfg x (some M.initial) ws₀ out₀)
    (coins : List Bool) (j : Fin k) :
    (M.runClosedConfigFromCoins coins cfg).tapes.workTapePos j ∈ window t := by
  by_cases hdone : (M.runClosedConfigFromCoins coins cfg).tapes.state = none
  · obtain ⟨_, _, hfin⟩ := runsWords_closed_completed M h cfg htapes coins hdone
    rw [hfin]
    simp only [wordsCfg, mem_window, Int.natAbs_zero, Nat.zero_le]
  · have hlt : coins.length < t := by_contra fun hge => by
      have hhalt := runsWords_closed_halted M h cfg htapes
      have hm := M.runClosedConfigFromCoins_mem_support coins cfg
      rw [eval_runClosedConfigFrom_eq_of_halted M cfg (Nat.le_of_not_lt hge) hhalt] at hm
      exact hdone (hhalt _ hm)
    exact mem_window.mpr
      ((natAbs_workTapePos_replay_le M coins cfg (fun i => by rw [htapes]; rfl) j).trans hlt.le)

/-- Split `coins` at the first point where `M` reaches `state = none`. -/
private def splitUntilHalted (M : MultiTapePTM k Bool State)
    (c : Config k Bool State Empty x) : List Bool → List Bool × List Bool
  | [] => ([], [])
  | bit :: rest =>
    if c.tapes.state = none then
      ([], bit :: rest)
    else
      let pair := splitUntilHalted M ((M.withCoin bit).step c) rest
      (bit :: pair.1, pair.2)

/-- With a fixed coin, a running round of `repeatUntilBlank` steps as its body. -/
theorem step_withCoin_repeatUntilBlank_live (i : Fin k) (body : MultiTapePTM k Bool State)
    (bit : Bool) (c : Config k Bool State Empty x) (hlive : c.tapes.state ≠ none) :
    ((repeatUntilBlank i body).withCoin bit).step (RepeatUntilBlank.runConfig c) =
      RepeatUntilBlank.runConfig ((body.withCoin bit).step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
  rw [Config.eq_iff_tapes_eq]
  have hstate : (RepeatUntilBlank.runConfig c).tapes.state = some (.inl q) := by
    simp only [RepeatUntilBlank.runConfig, Cfg.mapState, hq, handOver, Option.elim_some]
  have hinp : (RepeatUntilBlank.runConfig c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
  have hwork : (RepeatUntilBlank.runConfig c).tapes.workTapeSymbols =
      c.tapes.workTapeSymbols := rfl
  simp only [MultiTapeMachine.step, withCoin, repeatUntilBlank, hstate, hq, hinp, hwork,
    Subsingleton.elim (RepeatUntilBlank.runConfig c).answerSymbols c.answerSymbols]
  cases body.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
  | step action symbol move =>
    simp only [RepeatUntilBlank.runAction, RepeatUntilBlank.runConfig, Config.step,
      Turing.Action.apply, Cfg.mapState]
  | query op _ => exact op.elim

private theorem splitUntilHalted_spec (i : Fin k) (body : MultiTapePTM k Bool State)
    (c : Config k Bool State Empty x) (coins : List Bool) :
    let pair := splitUntilHalted body c coins
    coins = pair.1 ++ pair.2 ∧
      (repeatUntilBlank i body).runClosedConfigFromCoins pair.1 (RepeatUntilBlank.runConfig c) =
        RepeatUntilBlank.runConfig (body.runClosedConfigFromCoins pair.1 c) ∧
      (pair.2 = [] ∨ (body.runClosedConfigFromCoins pair.1 c).tapes.state = none) := by
  fun_induction splitUntilHalted body c coins with
  | case1 => -- no coins
    simp only [List.nil_append, runClosedConfigFromCoins, List.foldl_nil, true_or, and_self]
  | case2 c bit rest hhalt => -- halted
    simp only [hhalt, List.nil_append, runClosedConfigFromCoins, List.foldl_nil, or_true, and_self]
  | case3 c bit rest hhalt pair ih => -- running: step, then recurse
    obtain ⟨happ, hrep, hpost⟩ := ih
    refine ⟨congrArg (bit :: ·) happ, ?_, hpost⟩
    simpa only [runClosedConfigFromCoins, List.foldl_cons,
      step_withCoin_repeatUntilBlank_live i body bit c hhalt] using hrep

/-- With a fixed coin, the blank test on an empty word halts. -/
theorem step_withCoin_repeatUntilBlank_check_nil (i : Fin k)
    (body : MultiTapePTM k Bool State) (bit : Bool) (ws : Fin k → List Bool) (out₀ : List Bool)
    (hi : ws i = []) (c : Config k Bool (State ⊕ Unit) Empty x)
    (hc : c.tapes = wordsCfg x (some (.inr ())) ws out₀) :
    ((repeatUntilBlank i body).withCoin bit).step c =
      { tapes := wordsCfg x none ws out₀, channels := Empty.elim } := by
  rw [Config.eq_iff_tapes_eq]
  have hsym : c.tapes.workTapeSymbols i = none := by
    simp only [hc, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi, List.head?_nil]
  simp only [MultiTapeMachine.step, withCoin, repeatUntilBlank,
    (hc ▸ rfl : c.tapes.state = some (.inr ())),
    RepeatUntilBlank.checkAction, hsym, Option.map_none, Config.step]
  rw [hc, RepeatUntilBlank.apply_idle_wordsCfg]

/-- With a fixed coin, the blank test on a non-empty word restarts the body. -/
theorem step_withCoin_repeatUntilBlank_check_ne_nil (i : Fin k)
    (body : MultiTapePTM k Bool State) (bit : Bool) (ws : Fin k → List Bool) (out₀ : List Bool)
    (hi : ws i ≠ []) (c : Config k Bool (State ⊕ Unit) Empty x)
    (hc : c.tapes = wordsCfg x (some (.inr ())) ws out₀) :
    ((repeatUntilBlank i body).withCoin bit).step c =
      RepeatUntilBlank.runConfig
        { tapes := wordsCfg x (some body.initial) ws out₀, channels := Empty.elim } := by
  obtain ⟨b, _, hb⟩ := List.exists_cons_of_ne_nil hi
  rw [Config.eq_iff_tapes_eq]
  have hsym : c.tapes.workTapeSymbols i = some b := by
    simp only [hc, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hb, List.head?_cons]
  simp only [MultiTapeMachine.step, withCoin, repeatUntilBlank,
    (hc ▸ rfl : c.tapes.state = some (.inr ())),
    RepeatUntilBlank.checkAction, hsym, Option.map_some, Config.step, RepeatUntilBlank.runConfig]
  rw [hc, RepeatUntilBlank.apply_idle_wordsCfg]
  simp only [mapState_wordsCfg, handOver, Option.elim_some]

private theorem repeatUntilBlank_round_mem_window (i : Fin k) {body : MultiTapePTM k Bool State}
    {σ : Type} {ws : σ → Fin k → List Bool}
    {prog : ProbOracleComp (fun _ : Empty × List Bool => List Bool) σ}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t : ℕ}
    (hbody : body.RunsWords x ws₀ out₀ t prog ws (fun _ => []))
    (cfg : Config k Bool State Empty x)
    (hcfg : cfg.tapes = wordsCfg x (some body.initial) ws₀ out₀) (cs : List Bool) (j : Fin k)
    (hnext : ∀ s' bit rest (c : Config k Bool (State ⊕ Unit) Empty x),
      (s', ()) ∈ (ProbOracleComp.runWith emptyOracle prog ()).support →
      c.tapes = wordsCfg x (some (.inr ())) (ws s') out₀ →
      ((repeatUntilBlank i body).runClosedConfigFromCoins rest
        (((repeatUntilBlank i body).withCoin bit).step c)).tapes.workTapePos j ∈ window t) :
    ((repeatUntilBlank i body).runClosedConfigFromCoins cs
      (RepeatUntilBlank.runConfig cfg)).tapes.workTapePos j ∈ window t := by
  obtain ⟨happ, hrep, hpost⟩ := splitUntilHalted_spec i body cfg cs
  set before := (splitUntilHalted body cfg cs).1
  set after := (splitUntilHalted body cfg cs).2
  rw [happ, replay_append, hrep]
  rcases after with _ | ⟨bit, rest⟩
  · simp only [runClosedConfigFromCoins, List.foldl_nil, RepeatUntilBlank.runConfig,
      Cfg.mapState]
    exact workTapePos_runsWords_mem_window body hbody cfg hcfg before j
  · obtain ⟨s', hs', htapes'⟩ := runsWords_closed_completed body hbody cfg hcfg before
      (hpost.resolve_left (List.cons_ne_nil bit rest))
    rw [List.append_nil] at htapes'
    rw [replay_cons]
    refine hnext s' bit rest _ hs' ?_
    simp only [RepeatUntilBlank.runConfig, htapes', mapState_wordsCfg, handOver_none]

/-- **Round-independent head window for `repeatUntilBlank`.** Under the closed `RunsWords`
invariants of `RunsWords.repeatUntilBlank` with per-round step bound `t`, every fixed-coin replay of
`repeatUntilBlank i body` keeps every work-tape head inside `window t`, for any `rounds`. -/
theorem workTapePos_repeatUntilBlank_mem_window (i : Fin k)
    {body : MultiTapePTM k Bool State} {σ : Type} {ws : σ → Fin k → List Bool}
    {step last : σ → ProbOracleComp (fun _ : Empty × List Bool => List Bool) σ}
    {out₀ : List Bool} {t rounds : ℕ} {s₀ : σ}
    (invariant : ℕ → σ → Prop) (hbase : invariant 0 s₀)
    (hstep : ∀ n < rounds, ∀ s, invariant n s →
      body.RunsWords x (ws s) out₀ t (step s) ws (fun _ => []))
    (hlast : ∀ s, invariant rounds s →
      body.RunsWords x (ws s) out₀ t (last s) ws (fun _ => []))
    (hpreserve : ∀ n < rounds, ∀ s, invariant n s →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ (ProbOracleComp.runWith oracle (step s) st).support →
          invariant (n + 1) s' ∧ ws s' i ≠ [])
    (hstop : ∀ s, invariant rounds s →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ (ProbOracleComp.runWith oracle (last s) st).support → ws s' i = [])
    (cfg₀ : Config k Bool State Empty x)
    (hcfg₀ : cfg₀.tapes = wordsCfg x (some body.initial) (ws s₀) out₀)
    (coins : List Bool) (j : Fin k) :
    ((repeatUntilBlank i body).runClosedConfigFromCoins coins
      (RepeatUntilBlank.runConfig cfg₀)).tapes.workTapePos j ∈ window t := by
  suffices ∀ m n s (cfg : Config k Bool State Empty x) (cs : List Bool),
      n + m = rounds → invariant n s →
      cfg.tapes = wordsCfg x (some body.initial) (ws s) out₀ →
      ((repeatUntilBlank i body).runClosedConfigFromCoins cs
        (RepeatUntilBlank.runConfig cfg)).tapes.workTapePos j ∈ window t from
    this rounds 0 s₀ cfg₀ coins (Nat.zero_add _) hbase hcfg₀
  intro m
  induction m with
  | zero =>
    intro n s cfg cs hnm hs hcfg
    subst hnm
    refine repeatUntilBlank_round_mem_window i (hlast s hs) cfg hcfg cs j
      fun s' bit rest c hs' hc => ?_
    rw [step_withCoin_repeatUntilBlank_check_nil i body bit (ws s') out₀
      (hstop s hs Unit emptyOracle () () s' hs') c hc, replay_halted _ rest _ rfl]
    simp only [wordsCfg, mem_window, Int.natAbs_zero, Nat.zero_le]
  | succ m ih =>
    intro n s cfg cs hnm hs hcfg
    have hn : n < rounds := by omega
    refine repeatUntilBlank_round_mem_window i (hstep n hn s hs) cfg hcfg cs j
      fun s' bit rest c hs' hc => ?_
    obtain ⟨hinv', hne'⟩ := hpreserve n hn s hs Unit emptyOracle () () s' hs'
    rw [step_withCoin_repeatUntilBlank_check_ne_nil i body bit (ws s') out₀ hne' c hc]
    exact ih (n + 1) s'
      { tapes := wordsCfg x (some body.initial) (ws s') out₀, channels := Empty.elim }
      rest (by omega) hinv' rfl

/-- **Workspace bound for `first.seq ((repeatUntilBlank i body).seq last)`.** When `first` (`t₁`),
each round of `body` (`t`), and `last` (`t₂`) satisfy closed `RunsWords` specifications, the
combined machine visits at most `k * (2 * max t₁ (max t t₂) + 1)` work-tape cells on `x`,
independently of `rounds`. -/
theorem runsInSpace_toNTM_seq_repeatUntilBlank {S₀ S₁ S₂ : Type} (i : Fin k)
    (first : MultiTapePTM k Bool S₀) (body : MultiTapePTM k Bool S₁)
    (lastM : MultiTapePTM k Bool S₂) {σ : Type} {ws : σ → Fin k → List Bool}
    (hws : Function.Injective ws)
    {step last : σ → ProbOracleComp (fun _ : Empty × List Bool => List Bool) σ}
    {emitFinal : σ → List Bool} {t₁ t t₂ rounds : ℕ} {s₀ : σ}
    (hfirst : first.RunsWords x (fun _ => []) [] t₁ (pure ()) (fun _ => ws s₀) (fun _ => []))
    (invariant : ℕ → σ → Prop) (hbase : invariant 0 s₀)
    (hstep : ∀ n < rounds, ∀ s, invariant n s →
      body.RunsWords x (ws s) [] t (step s) ws (fun _ => []))
    (hlast : ∀ s, invariant rounds s →
      body.RunsWords x (ws s) [] t (last s) ws (fun _ => []))
    (hpreserve : ∀ n < rounds, ∀ s, invariant n s →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ (ProbOracleComp.runWith oracle (step s) st).support →
          invariant (n + 1) s' ∧ ws s' i ≠ [])
    (hstop : ∀ s, invariant rounds s →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ (ProbOracleComp.runWith oracle (last s) st).support → ws s' i = [])
    (hlastM : ∀ (OracleState : Type)
        (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s : σ),
      (s, st') ∈ (ProbOracleComp.runWith oracle
        (OracleComp.iterate rounds step s₀ >>= last) st).support →
      lastM.RunsWords x (ws s) [] t₂ (pure ()) (fun _ _ => []) (fun _ => emitFinal s)) :
    (first.seq ((repeatUntilBlank i body).seq lastM)).toNTM.RunsInSpace x
      (k * (2 * max t₁ (max t t₂) + 1)) := by
  let B := max t₁ (max t t₂)
  have hmono {s : ℕ} {z : ℤ} (hz : z ∈ window s) (hle : s ≤ B) : z ∈ window B :=
    mem_window.mpr ((mem_window.mp hz).trans hle)
  have hB₁ : t₁ ≤ B := le_max_left _ _
  have hBt : t ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB₂ : t₂ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let M_loop := repeatUntilBlank i body
  let M_tail := M_loop.seq lastM
  let M_all := first.seq M_tail
  have hloop_rw : M_loop.RunsWords x (ws s₀) [] ((rounds + 1) * (t + 1))
      (OracleComp.iterate rounds step s₀ >>= last) ws (fun _ => []) :=
    RunsWords.repeatUntilBlank i hws invariant hbase hstep hlast hpreserve hstop
  have hreach (coins : List Bool) (j : Fin k) :
      (M_all.runClosedConfigFromCoins coins (M_all.initialConfig x)).tapes.workTapePos j ∈
        window B := by
    have hinit_tapes : (first.initialConfig x).tapes =
        wordsCfg x (some first.initial) (fun _ => []) [] :=
      Cfg.init_eq_wordsCfg first.initial x
    rcases replay_seq_cases first M_tail (first.initialConfig x) coins with
      ⟨b₁, hb₁⟩ | ⟨b₁, a₁, hh₁, hs₁⟩
    · erw [hb₁]
      simpa only [Sequential.left, Cfg.mapState] using
        hmono (workTapePos_runsWords_mem_window first hfirst _ hinit_tapes b₁ j) hB₁
    · erw [hs₁]
      simp only [Sequential.right, Cfg.mapState]
      obtain ⟨_, _, ht₁⟩ := runsWords_closed_completed first hfirst _ hinit_tapes b₁ hh₁
      rw [List.append_nil] at ht₁
      let cfgBody : Config k Bool S₁ Empty x :=
        { tapes := wordsCfg x (some body.initial) (ws s₀) [], channels := Empty.elim }
      have hstart₁ :
          Sequential.start M_tail (first.runClosedConfigFromCoins b₁ (first.initialConfig x)) =
            Sequential.left lastM (RepeatUntilBlank.runConfig cfgBody) := by
        simp only [Config.eq_iff_tapes_eq, Sequential.start, ht₁, Cfg.withState, M_tail, M_loop,
          Sequential.left, RepeatUntilBlank.runConfig, cfgBody, mapState_wordsCfg, handOver,
          Option.elim_some]
        rfl
      rw [hstart₁]
      rcases replay_seq_cases M_loop lastM (RepeatUntilBlank.runConfig cfgBody) a₁ with
        ⟨b₂, hb₂⟩ | ⟨b₂, a₂, hh₂, hs₂⟩
      · rw [hb₂]
        simp only [Sequential.left, Cfg.mapState]
        exact hmono (workTapePos_repeatUntilBlank_mem_window i invariant hbase hstep hlast
          hpreserve hstop cfgBody rfl b₂ j) hBt
      · rw [hs₂]
        simp only [Sequential.right, Cfg.mapState]
        obtain ⟨sf, hsf, ht₂⟩ := runsWords_closed_completed M_loop hloop_rw _ rfl b₂ hh₂
        rw [List.append_nil] at ht₂
        exact hmono (workTapePos_runsWords_mem_window lastM
          (hlastM Unit emptyOracle () () sf hsf) _
          (by simp only [Sequential.start, ht₂, Cfg.withState, wordsCfg]) a₂ j) hB₂
  intro path
  apply MultiTapeNTM.RunPath.InWindow.space_le
  rintro _ ⟨idx, rfl⟩ j
  obtain ⟨coins, _, hcoins⟩ := M_all.exists_runPath_toNTM_iff.mp
    ⟨path.toRunPath.take idx, RelSeries.head_take _ _, rfl, RelSeries.last_take _ _⟩
  rw [← hcoins, path.head_eq, initCfg_toNTM, ← tapes_runClosedConfigFromCoins]
  exact hreach coins j

end Helpers

end Turing.MultiTapePTM
