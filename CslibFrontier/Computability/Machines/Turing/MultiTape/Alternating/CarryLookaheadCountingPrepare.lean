/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingInitialLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveDepthPrepare.Embedded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunctionLayout

/-!
# Physical preparation of an ordinary count-bit evaluator

The initial work tapes contain only a separately stored predicate context and one raw parameter
word. Native word computations install count, width, query metadata, header and status. The
checked depth machine then derives the binary height and unary frontier. No derived field is
supplied in advance, and the long context is preserved throughout initialization. For a known
binary tree height, the same field installer writes that height directly and expands only the
unary frontier and binary power-of-two count, in linear time in the height.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingPrepare

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open CarryLookaheadCountingInitialLayout

/-- Reusable initializer scratch, the complete evaluator, then raw parameters and a marker. -/
abbrev size (scratch k r q : ℕ) : ℕ :=
  scratch + CarryLookaheadCountingLayout.size k r q + 2

/-- The evaluator runs in the protected middle block. -/
@[expose] def evaluatorTapes (scratch k r q : ℕ) :
    Fin (CarryLookaheadCountingLayout.size k r q) ↪ Fin (size scratch k r q) :=
  (Fin.natAddEmb scratch).trans (Fin.castAddEmb 2)

/-- Actual ambient words with reusable scratch and the untouched raw parameter source. -/
@[expose] def ambientWords (scratch k r q : ℕ) (context : List Bool) (a : CountingInput.Input)
    (fields : Fields) : Fin (size scratch k r q) → List Bool :=
  Fin.append (Fin.append (fun _ : Fin scratch => []) (words k r q context fields))
    ![CountingInput.encInput a, []]

/-- Every initializer stage has all work heads at zero and the host at its left blank. -/
@[expose] def config (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input)
    (fields : Fields) : Cfg (size scratch k r q) Bool Unit input :=
  { tapesCfg input (ambientWords scratch k r q context a fields) 0 0 [] with inputPos := 0 }

/-- Initially only the context and raw parameter word are present; every derived word is blank. -/
@[expose] def initial (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    Cfg (size scratch k r q) Bool Unit input :=
  config scratch k r q input context a {}

/-- The protected context and the binary source live on distinct tapes. -/
theorem context_ne_request (scratch k r q : ℕ) :
    evaluatorTapes scratch k r q (contextTape k r q) ≠
      Fin.natAdd (scratch + CarryLookaheadCountingLayout.size k r q) 0 :=
  Fin.castAdd_ne_natAdd _ _

/-- Loading exactly these two words gives the physical initial configuration. -/
theorem ready_eq_initial (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    TwoWordInput.ready (evaluatorTapes scratch k r q (contextTape k r q))
      (Fin.natAdd (scratch + CarryLookaheadCountingLayout.size k r q) 0)
      input context (CountingInput.encInput a) = initial scratch k r q input context a := by
  have hw : TwoWordInput.words (evaluatorTapes scratch k r q (contextTape k r q))
      (Fin.natAdd (scratch + CarryLookaheadCountingLayout.size k r q) 0)
      context (CountingInput.encInput a) = ambientWords scratch k r q context a {} := by
    let E := CarryLookaheadCountingLayout.size k r q
    let u : Fin E := contextTape k r q
    change TwoWordInput.words ((Fin.natAdd scratch u).castAdd 2) (Fin.natAdd (scratch + E) 0)
      _ _ = _
    funext i
    rw [TwoWordInput.words, ambientWords, words_empty]
    cases i using Fin.addCases with
    | left i =>
      rw [Fin.append_left, ite_eq_right (Fin.castAdd_ne_natAdd _ _)]
      cases i using Fin.addCases with
      | left i =>
        rw [Fin.append_left, ite_eq_right]
        exact fun h => Fin.castAdd_ne_natAdd _ _ (Fin.castAdd_injective _ _ h)
      | right i =>
        rw [Fin.append_right, Function.update_apply]
        by_cases h : i = u
        · subst i; simp [u]
        · rw [ite_eq_right h, ite_eq_right]
          exact fun he => h (Fin.natAdd_injective _ _ (Fin.castAdd_injective _ _ he))
    | right i =>
      rw [ite_eq_right (Fin.castAdd_ne_natAdd _ _).symm, Fin.append_right]
      fin_cases i <;> simp
  simp only [TwoWordInput.ready, initial, config, hw]
  apply Cfg.ext <;> try rfl
  funext i z
  simp [wordsCfg, tapesCfg]

/-- Lift a field update through the scratch prefix and the retained parameter tapes. -/
theorem ambientWords_update_of_eq (scratch k r q : ℕ) (context : List Bool)
    (a : CountingInput.Input) (fields fields' : Fields)
    (dest : Fin (CarryLookaheadCountingLayout.size k r q)) (word : List Bool)
    (hwords : Function.update (words k r q context fields) dest word =
      words k r q context fields') :
    Function.update (ambientWords scratch k r q context a fields)
      (evaluatorTapes scratch k r q dest) word =
      ambientWords scratch k r q context a fields' := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i =>
      simp [ambientWords, evaluatorTapes, Function.update_of_ne
        (show (i.castAdd (CarryLookaheadCountingLayout.size k r q)).castAdd 2 ≠
          (Fin.natAdd scratch dest).castAdd 2 from by
            intro h
            have hv := congrArg Fin.val h
            have := i.isLt
            change i.val = scratch + dest.val at hv
            omega)]
    | right i =>
      have h := congrFun hwords i
      simpa [ambientWords, evaluatorTapes, Function.update_apply] using h
  | right i =>
    simp [ambientWords, evaluatorTapes,
      Function.update_of_ne (Fin.castAdd_ne_natAdd _ _).symm]

private theorem ambientWords_update (scratch k r q : ℕ) (context : List Bool)
    (a : CountingInput.Input) (fields : Fields) (field : CountingInput.Field)
    (word : List Bool) :
    Function.update (ambientWords scratch k r q context a fields)
      (evaluatorTapes scratch k r q (destination k r q field)) word =
      ambientWords scratch k r q context a (fields.set field word) :=
  ambientWords_update_of_eq scratch k r q context a fields _ _ word
    (words_update_field k r q context fields field word)

/-- The evaluator observes the prepared fields independently of the retained parameter word. -/
theorem view_prepared_of_retained (scratch k r q : ℕ) (input context : List Bool)
    (source a : CountingInput.Input) :
    viewCfg (evaluatorTapes scratch k r q)
      (config scratch k r q input context source (canonical a)) =
      CarryLookaheadCounting.initial k r q input context a.count a.query.width a.query.bit
        a.query.claim := by
  rw [initial_eq_tapesCfg]
  apply Cfg.ext <;> try rfl
  · funext i
    simp [viewCfg, evaluatorTapes, config, ambientWords, tapesCfg]

/-- The prepared protected block is exactly the existing native evaluator's initial storage. -/
theorem view_prepared (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    viewCfg (evaluatorTapes scratch k r q)
      (config scratch k r q input context a (canonical a)) =
      CarryLookaheadCounting.initial k r q input context a.count a.query.width a.query.bit
        a.query.claim := view_prepared_of_retained scratch k r q input context a a

private def projectionDestination (direct : Bool) (k r q : ℕ)
    (field : CountingInput.Field) : Fin (CarryLookaheadCountingLayout.size k r q) :=
  if direct && field == .count then height k r q else destination k r q field

private def projectionGet (direct : Bool) (fields : Fields) (field : CountingInput.Field) :
    List Bool :=
  if direct && field == .count then fields.height else fields.get field

private def projectionSet (direct : Bool) (fields : Fields) (field : CountingInput.Field)
    (word : List Bool) : Fields :=
  if direct && field == .count then { fields with height := word } else fields.set field word

private def projected (direct : Bool) (a : CountingInput.Input) : Fields where
  height := if direct then encNat a.count else []
  count := if direct then [] else encNat a.count
  width := encNat a.query.width
  metadata := Routing.encPosition (Initial.position a.query)
  header := [a.query.claim, false]
  status := [false]

private theorem words_projection (direct : Bool) (k r q : ℕ) (context : List Bool)
    (fields : Fields) (field : CountingInput.Field) :
    words k r q context fields (projectionDestination direct k r q field) =
      projectionGet direct fields field := by
  cases direct <;> cases field <;>
    simp [projectionDestination, projectionGet]

private theorem ambientWords_projection_update (direct : Bool) (scratch k r q : ℕ)
    (context : List Bool) (a : CountingInput.Input) (fields : Fields)
    (field : CountingInput.Field) (word : List Bool) :
    Function.update (ambientWords scratch k r q context a fields)
      (evaluatorTapes scratch k r q (projectionDestination direct k r q field)) word =
      ambientWords scratch k r q context a (projectionSet direct fields field word) := by
  unfold projectionDestination projectionSet
  split_ifs
  · exact ambientWords_update_of_eq scratch k r q context a fields _ _ word
      (words_update_height k r q context fields word)
  · exact ambientWords_update scratch k r q context a fields field word

private theorem exists_project (direct : Bool) (k r q reserve : ℕ) :
    ∃ (scratch : ℕ) (_ : reserve ≤ scratch) (S : Type) (_ : Finite S)
      (tm : MultiTapeTM (size scratch k r q) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input),
        tm.runFrom ((initial scratch k r q input context a).withState (some tm.q₀))
          (c * ((CountingInput.encInput a).length + 1) ^ d) =
          (config scratch k r q input context a (projected direct a)).withState none := by
  classical
  have hfields (field : CountingInput.Field) :=
    WordFunctionLayout.exists_of_polyTime (CountingInput.word_polyTime field)
  choose fieldScratch Q hQ fieldMachine cField dField hField using hfields
  let (field : CountingInput.Field) : Finite (Q field) := hQ field
  let scratch := fieldScratch .count + fieldScratch .width + fieldScratch .metadata +
    fieldScratch .header + fieldScratch .status + reserve
  let E := CarryLookaheadCountingLayout.size k r q
  have hfield (field : CountingInput.Field) : fieldScratch field ≤ scratch := by
    cases field <;> dsimp only [scratch] <;> omega
  let write := fun field =>
    ((fieldMachine field).extendTapes
      (WordFunctionLayout.outputTapes (hfield field)
        (projectionDestination direct k r q field))).fromLeftBlank
  let prepare := (write .count).seq ((write .width).seq ((write .metadata).seq
    ((write .header).seq (write .status))))
  let bound (m : ℕ) := (cField .count * (m + 1) ^ dField .count + 2) +
    ((cField .width * (m + 1) ^ dField .width + 2) +
      ((cField .metadata * (m + 1) ^ dField .metadata + 2) +
        ((cField .header * (m + 1) ^ dField .header + 2) +
          (cField .status * (m + 1) ^ dField .status + 2))))
  have hbound : Cslib.PolynomiallyBounded bound := by unfold bound; fun_prop
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  refine ⟨scratch, by dsimp only [scratch]; omega, _, inferInstance, prepare, c, d, ?_⟩
  intro input context a
  have hwrite (field : CountingInput.Field) (fields : Fields)
      (hblank : projectionGet direct fields field = []) :
      RunsBetween (write field) (config scratch k r q input context a fields)
        (config scratch k r q input context a
          (projectionSet direct fields field (CountingInput.word field a)))
        (cField field * ((CountingInput.encInput a).length + 1) ^ dField field + 2)
        ((scratch + E + 2) *
          (cField field * ((CountingInput.encInput a).length + 1) ^ dField field + 1) +
            4 * (scratch + E + 2)) := by
    have hr := hField field scratch E (hfield field)
      (projectionDestination direct k r q field) input a
      (ambientWords scratch k r q context a fields) []
      (by intro i; simp [ambientWords, E])
      (by simpa [ambientWords, words_projection] using hblank)
      (by simp [ambientWords, E]) (by simp [ambientWords, E])
    simp only [encBits_apply] at hr
    rw [show (Fin.natAdd scratch (projectionDestination direct k r q field)).castAdd 2 =
      evaluatorTapes scratch k r q (projectionDestination direct k r q field) from rfl,
      ambientWords_projection_update] at hr
    exact hr
  let f₀ : Fields := {}
  let f₁ := projectionSet direct f₀ .count (CountingInput.word .count a)
  let f₂ := projectionSet direct f₁ .width (CountingInput.word .width a)
  let f₃ := projectionSet direct f₂ .metadata (CountingInput.word .metadata a)
  let f₄ := projectionSet direct f₃ .header (CountingInput.word .header a)
  have h₀ := hwrite .count f₀ (by cases direct <;> rfl)
  have h₁ := hwrite .width f₁ (by cases direct <;> rfl)
  have h₂ := hwrite .metadata f₂ (by cases direct <;> rfl)
  have h₃ := hwrite .header f₃ (by cases direct <;> rfl)
  have h₄ := hwrite .status f₄ (by cases direct <;> rfl)
  have hfinish : projectionSet direct f₄ .status (CountingInput.word .status a) =
      projected direct a := by cases direct <;> rfl
  have hr := h₀.seq (h₁.seq (h₂.seq (h₃.seq h₄)))
  rw [hfinish] at hr
  exact (hr.mono (hc _) (Nat.le_refl _)).1

private theorem core_eq_evaluator (scratch k r q : ℕ)
    (hsize : 12 ≤ CarryLookaheadCountingLayout.size k r q) (i : Fin 12) :
    CarrySaveDepthPrepare.Embedded.coreTapes scratch
      (CarryLookaheadCountingLayout.size k r q) hsize i =
      evaluatorTapes scratch k r q ⟨i.val, by have := i.isLt; omega⟩ := by
  apply Fin.ext
  simp [CarrySaveDepthPrepare.Embedded.coreTapes_val, evaluatorTapes]

private theorem ambientWords_middle (scratch k r q : ℕ) (context : List Bool)
    (a : CountingInput.Input) (fields : Fields)
    (i : Fin (CarryLookaheadCountingLayout.size k r q)) :
    ambientWords scratch k r q context a fields (evaluatorTapes scratch k r q i) =
      words k r q context fields i := by
  change Fin.append _ _ ((Fin.natAdd scratch i).castAdd 2) = _
  rw [Fin.append_left, Fin.append_right]

private theorem ambientWords_scratch (scratch k r q : ℕ) (context : List Bool)
    (a : CountingInput.Input) (fields : Fields) (i : Fin (size scratch k r q))
    (hi : i.val < scratch) : ambientWords scratch k r q context a fields i = [] := by
  have he : i = ((⟨i.val, hi⟩ : Fin scratch).castAdd
      (CarryLookaheadCountingLayout.size k r q)).castAdd 2 := Fin.ext rfl
  rw [he]
  simp only [ambientWords, Fin.append_left]

/-- Construct all seven derived words from the raw parameter source using fixed finite native
machines. The supplied context is preserved without copying it during preparation. -/
theorem exists_prepare (k r q : ℕ) :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (tm : MultiTapeTM (size scratch k r q) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input),
        tm.runFrom ((initial scratch k r q input context a).withState (some tm.q₀))
          (c * ((CountingInput.encInput a).length + 1) ^ d) =
          (config scratch k r q input context a (canonical a)).withState none := by
  obtain ⟨depthScratch, QD, hQD, depthMachine, cD, dD, hDepth⟩ :=
    CarrySaveDepthPrepare.Embedded.exists_prepare
  obtain ⟨scratch, hdepth, QP, hQP, project, cP, dP, hProject⟩ :=
    exists_project false k r q depthScratch
  let := hQD
  let := hQP
  let E := CarryLookaheadCountingLayout.size k r q
  have hsize : 12 ≤ E := by
    unfold E CarryLookaheadCountingLayout.size CountingTerminalLayout.size
    omega
  let depth := depthMachine.extendTapes
    (CarrySaveDepthPrepare.Embedded.embedding depthScratch scratch E hdepth hsize)
  have hbound : Cslib.PolynomiallyBounded
      (fun m => cP * (m + 1) ^ dP + cD * (m + 1) ^ dD) := by fun_prop
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  refine ⟨scratch, _, inferInstance, project.seq depth, c, d, ?_⟩
  intro input context a
  have hcore₀ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 0 =
      evaluatorTapes scratch k r q (height k r q) := core_eq_evaluator ..
  have hcore₄ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 4 =
      evaluatorTapes scratch k r q (unary k r q) := core_eq_evaluator ..
  have hcore₇ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 7 =
      evaluatorTapes scratch k r q (destination k r q .count) := core_eq_evaluator ..
  have hd := hDepth scratch E hdepth hsize input a.count
    (ambientWords scratch k r q context a (projected false a)) []
    (by rw [hcore₇, ambientWords_middle, words_destination]; rfl)
    (by rw [hcore₀, ambientWords_middle, words_height]; rfl)
    (by rw [hcore₄, ambientWords_middle, words_unary]; rfl)
    (fun i hi => ambientWords_scratch _ _ _ _ _ _ _ i hi)
  have hw₀ := ambientWords_update_of_eq scratch k r q context a (projected false a)
    { projected false a with height := encNat (Nat.clog 2 a.count) } (height k r q)
    (encNat (Nat.clog 2 a.count)) (words_update_height k r q context (projected false a) _)
  have hw₄ := ambientWords_update_of_eq scratch k r q context a
    { projected false a with height := encNat (Nat.clog 2 a.count) } (canonical a) (unary k r q)
    (encUnary (Nat.clog 2 a.count)) (words_update_unary k r q context _ _)
  rw [hcore₀, hcore₄, hw₀, hw₄] at hd
  have hp := RunsBetween.of_runFrom (hProject input context a)
  have hr := hp.seq hd
  have hlen : (encNat a.count).length ≤ (CountingInput.encInput a).length := by
    rw [CountingInput.length_encInput]
    simp only [encNat_apply, ← Nat.size_eq_bits_len]
    omega
  have ht := Nat.mul_le_mul_left cD
    (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dD)
  exact (hr.mono ((Nat.add_le_add_left ht _).trans (hc _)) (Nat.le_refl _)).1

/-- Construct the native sum layout directly from a binary height and query. The retained raw
record stores the height in `count`; only the protected evaluator count expands to `2 ^ height`.
The expansion is linear in the height and every other setup cost is polynomial in the original
binary record. The context is preserved without being scanned or copied. -/
theorem exists_prepare_height (k r q : ℕ) :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (tm : MultiTapeTM (size scratch k r q) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input),
        tm.runFrom ((initial scratch k r q input context a).withState (some tm.q₀))
          (c * (a.count + ((CountingInput.encInput a).length + 1) ^ d + 1)) =
          (config scratch k r q input context a
            (canonical ⟨2 ^ a.count, a.query⟩)).withState none := by
  obtain ⟨depthScratch, QD, hQD, depthMachine, cD, hDepth⟩ :=
    CarrySaveDepthPrepare.Embedded.exists_prepare_height
  obtain ⟨scratch, hdepth, QP, hQP, project, cP, dP, hProject⟩ :=
    exists_project true k r q depthScratch
  let := hQD
  let := hQP
  let E := CarryLookaheadCountingLayout.size k r q
  have hsize : 12 ≤ E := by
    unfold E CarryLookaheadCountingLayout.size CountingTerminalLayout.size
    omega
  let depth := depthMachine.extendTapes
    (CarrySaveDepthPrepare.Embedded.embedding depthScratch scratch E hdepth hsize)
  refine ⟨scratch, _, inferInstance, project.seq depth, cP + cD, dP, ?_⟩
  intro input context a
  have hcore₀ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 0 =
      evaluatorTapes scratch k r q (height k r q) := core_eq_evaluator ..
  have hcore₄ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 4 =
      evaluatorTapes scratch k r q (unary k r q) := core_eq_evaluator ..
  have hcore₇ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 7 =
      evaluatorTapes scratch k r q (destination k r q .count) := core_eq_evaluator ..
  have hd := hDepth scratch E hdepth hsize input a.count
    (ambientWords scratch k r q context a (projected true a)) []
    (by rw [hcore₀, ambientWords_middle, words_height]; rfl)
    (by rw [hcore₇, ambientWords_middle, words_destination]; rfl)
    (by rw [hcore₄, ambientWords_middle, words_unary]; rfl)
    (fun i hi => ambientWords_scratch _ _ _ _ _ _ _ i hi)
  have hw₇ := ambientWords_update scratch k r q context a (projected true a) .count
    (encNat (2 ^ a.count))
  have hw₄ := ambientWords_update_of_eq scratch k r q context a
    ((projected true a).set .count (encNat (2 ^ a.count)))
    { (projected true a).set .count (encNat (2 ^ a.count)) with unary := encUnary a.count }
    (unary k r q) (encUnary a.count) (words_update_unary k r q context _ _)
  have hcanonical :
      { (projected true a).set .count (encNat (2 ^ a.count)) with unary := encUnary a.count } =
        canonical ⟨2 ^ a.count, a.query⟩ := by
    simp only [canonical, Nat.clog_pow 2 a.count one_lt_two]
    rfl
  rw [hcore₇, hcore₄, hw₇, hw₄, hcanonical] at hd
  have hp := RunsBetween.of_runFrom (hProject input context a)
  have hr := hp.seq hd
  exact (hr.mono (t' := (cP + cD) *
    (a.count + ((CountingInput.encInput a).length + 1) ^ dP + 1))
    (by nlinarith [Nat.zero_le (cP * a.count),
      Nat.zero_le (cD * ((CountingInput.encInput a).length + 1) ^ dP)]) (Nat.le_refl _)).1

end Turing.MultiTapeATM.CarryLookaheadCountingPrepare
