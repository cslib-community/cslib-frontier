/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Helpers
import CslibFrontier.Tactic.Realize

/-!
# Internal Deamortized Trie Clear Loop (`bufClearLoopGenProg`)

Internal `ClearableBufTrie` iterative edge-popping and node-clearing loop consumed privately by
`Clear`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufClearLoopGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufClearLoopGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufClearLoop_spec`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private theorem child_idx_lt {c n_max v c' : ℕ} (hv : v < maxTrieNodesWhp c n_max)
    (hc : c' < 2 ^ bCharWhp n_max) : v * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max :=
  (Nat.add_lt_add_left hc _).trans_le <| by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hv

/-- Clear `trieChild par ch := 0` when `ch < 2 ^ bChar` (`d = (rt, (par, ch))`,
`par < maxNodes`). -/
@[irreducible] private def bufClearEdgeRtProg (d : BufRt × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1
  if d.2.2 < brPowBChar rt then
    let idxC ← pure (d.2.1 * brPowBChar rt + d.2.2)
    let zero_v ← pure 0
    writePackedGenProg ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idxC), zero_v)
  else
    pure ()

private theorem bufClearEdgeRtProg_eq (d : BufRt × (ℕ × ℕ)) :
    bufClearEdgeRtProg d = (do
      let rt := d.1
      if d.2.2 < brPowBChar rt then
        let idxC ← pure (d.2.1 * brPowBChar rt + d.2.2)
        let zero_v ← pure 0
        writePackedGenProg ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idxC), zero_v)
      else
        pure ()) := by
  unfold bufClearEdgeRtProg; rfl

private theorem realizes_bufClearEdgeRt :
    Realizes .exact bufClearEdgeRtProg
      (WordEncoding.encode (α := BufRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2.1 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufClearEdgeRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨rt, ⟨par, ch⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hpar⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brPowBChar] at *
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hidx_lt : ch < 2 ^ bCharWhp n_max →
        par * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := child_idx_lt hpar
    first
    | exact henv.fits_of_le_n_max ((hidx_lt (by omega)).le.trans htc_n)
    | exact rt_child_safe henv hep (hidx_lt (by omega))

/-- Tail writes of `bufClearOne` (`1 < na`, `u = na - 1`): clear `nodeLeafItem u := 0` and update
`(hdrNA, hdrIA) := (u, 0)`. -/
@[irreducible] private def bufClearPopTailRtProg (d : BufRt × ℕ) : Memory.Prog Unit := do
  let rt := d.1
  let idxLI ← pure (4 * d.2 + 2)
  let zero_v ← pure 0
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let addrIA ← pure (brBase rt + brHdrIA rt)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI), zero_v)
  Memory.write addrNA d.2
  Memory.write addrIA zero_v

private theorem bufClearPopTailRtProg_eq (d : BufRt × ℕ) :
    bufClearPopTailRtProg d = (do
      let rt := d.1
      let idxLI ← pure (4 * d.2 + 2)
      let zero_v ← pure 0
      let addrNA ← pure (brBase rt + brHdrNA rt)
      let addrIA ← pure (brBase rt + brHdrIA rt)
      writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI), zero_v)
      Memory.write addrNA d.2
      Memory.write addrIA zero_v) := by
  unfold bufClearPopTailRtProg; rfl

private theorem realizes_bufClearPopTailRt :
    Realizes .exact bufClearPopTailRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufClearPopTailRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨rt, u⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hu⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hu ⊢
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    obtain ⟨hna32, hia32, _⟩ := rt_disj_le c U V w n_max base ep hep
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hna32
    | exact henv.fits_hdr_addr hia32
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

/-- Pop branch of `bufClearOne` (`1 < na`, `u = na - 1`). -/
@[irreducible] private def bufClearPopRtProg (d : BufRt × ℕ) : Memory.Prog Unit := do
  let rt := d.1
  let u ← pure d.2
  let idxP ← pure (4 * u)
  let idxC ← pure (4 * u + 1)
  let par ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxP)
  let ch ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxC)
  bufClearEdgeRtProg (rt, (par, ch))
  bufClearPopTailRtProg (rt, u)

private theorem bufClearPopRtProg_eq (d : BufRt × ℕ) :
    bufClearPopRtProg d = (do
      let rt := d.1
      let u ← pure d.2
      let idxP ← pure (4 * u)
      let idxC ← pure (4 * u + 1)
      let par ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxP)
      let ch ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxC)
      bufClearEdgeRtProg (rt, (par, ch))
      bufClearPopTailRtProg (rt, u)) := by
  unfold bufClearPopRtProg; rfl

private theorem realizes_bufClearPopRt :
    Realizes .exact bufClearPopRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d s => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1 ∧
        readPacked (brBase d.1 + brOffMeta d.1) (brGBits d.1) (brW d.1) s.mem (4 * d.2) <
          brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufClearPopRtProg
  have hrp := realizes_readPackedGen
  have hce := realizes_bufClearEdgeRt
  have hpt := realizes_bufClearPopTailRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, u⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hu, hpar_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hu hpar_lt ⊢
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | exact hu
    | (simp only [mkBufRt, brMaxNodes, clientResult_readPackedGen] at *; exact hpar_lt)

/-- Root branch of `bufClearOne` (`na ≤ 1`): clear `nodeLeafItem 0 := 0` and set
`(hdrNA, hdrIA) := (1, 0)`. -/
@[irreducible] private def bufClearRootRtProg (rt : BufRt) : Memory.Prog Unit := do
  let two_v ← pure 2
  let one_v ← pure 1
  let zero_v ← pure 0
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let addrIA ← pure (brBase rt + brHdrIA rt)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), two_v), zero_v)
  Memory.write addrNA one_v
  Memory.write addrIA zero_v

private theorem bufClearRootRtProg_eq (rt : BufRt) :
    bufClearRootRtProg rt = (do
      let two_v ← pure 2
      let one_v ← pure 1
      let zero_v ← pure 0
      let addrNA ← pure (brBase rt + brHdrNA rt)
      let addrIA ← pure (brBase rt + brHdrIA rt)
      writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), two_v), zero_v)
      Memory.write addrNA one_v
      Memory.write addrIA zero_v) := by
  unfold bufClearRootRtProg; rfl

private theorem realizes_bufClearRootRt :
    Realizes .exact bufClearRootRtProg
      (WordEncoding.encode (α := BufRt))
      (WordEncoding.encode (α := Unit))
      (fun w rt _ => BufRtEnvGen w rt)
      (fun _ _ => 0) := by
  unfold bufClearRootRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    obtain ⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hmt2 : 2 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    obtain ⟨hna32, hia32, _⟩ := rt_disj_le c U V w n_max base ep hep
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hna32
    | exact henv.fits_hdr_addr hia32
    | exact rt_meta_safe henv hep (by omega)

/-- Precondition for `bufClearOneRtProg`. -/
def BufClearOnePre (w : ℕ) (p : BufRt × Unit) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max base ep tr,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    p.1 = mkBufRt c U V w₀ n_max base ep ∧
    BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
    ClearableBufTrie tr

/-- One elementary cleanup step `bufClearOne`. -/
def bufClearOneRtProg (p : BufRt × Unit) : Memory.Prog Unit := do
  let rt := p.1
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let na ← Memory.read addrNA
  let one_v ← pure 1
  if one_v < na then
    let u ← pure (na - 1)
    bufClearPopRtProg (rt, u)
  else
    bufClearRootRtProg rt

private theorem memoryCost_bufClearOneRtProg_pos (p : BufRt × Unit) (s : Memory.State) :
    1 ≤ memoryCost (bufClearOneRtProg p) s := by
  unfold bufClearOneRtProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_memRead_and_write.1]
  omega

private theorem realizes_bufClearOneRt :
    Realizes .exact bufClearOneRtProg
      (WordEncoding.encode (α := BufRt × Unit))
      (WordEncoding.encode (α := Unit))
      BufClearOnePre
      (fun _ _ => 0) := by
  unfold bufClearOneRtProg
  have hcp := realizes_bufClearPopRt
  have hcr := realizes_bufClearRootRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, ⟨⟩⟩
    obtain ⟨c, U, V, w₀, n_max, base, ep, tr, henv, hep, rfl, hrep, hclr⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hna32 : brHdrNA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).1
    have hmem_na : s.mem (base + brHdrNA (mkBufRt c U V w n_max base ep)) = tr.nodeAlloc := by
      have hn := hrep.2.2.1; rcases hep with rfl | rfl <;> exact hn
    simp only [hcs_r, hcr_r] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hna32
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrNA] at hmem_na
       simp only [mkBufRt, brBase, brHdrNA, brMaxNodes, brOffMeta, brGBits, brW, hmem_na] at *
       have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
       have hna_max := hrep.1
       have hgt : 1 < tr.nodeAlloc := by omega
       set u := tr.nodeAlloc - 1
       have hu1 : 1 ≤ u := by omega
       have hu_lt : u < tr.nodeAlloc := by omega
       have hpar_u : tr.nodeParent u < u := hclr.bounds.2 u hu1 hu_lt
       have hrep_par : readPacked (base + if ep = 0 then offTrieMeta0 c U V w n_max
           else offTrieMeta1 c U V w n_max) (globalPtrBits n_max) w s.mem (4 * u) =
           tr.nodeParent u := (hrep.2.2.2.2.2.1 u hu1 hu_lt).1
       try rw [hrep_par]
       omega)

private theorem bufClearOneRtProg_spec {c U V w n_max base ep : ℕ}
    {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hclr : ClearableBufTrie tr) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufClearOneRtProg (rt, ())
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufClearOne tr
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 15 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  obtain ⟨hna_lt_sp, hia_lt_sp, hc_seg, hm_seg, _⟩ := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hna32, hia32, hna_ne_ia, h32_c, hc_le_m, hm_le_i⟩ := rt_disj_le c U V w n_max base ep hep
  obtain ⟨hna_max, -, hhna, -, hch, hpar, hlf, -⟩ := bufTrieMemRep_iff_rt.mp hrep
  set rt := mkBufRt c U V w n_max base ep with hrt
  have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
  have h0_g : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
  have h0_fit : Fits w 0 := Nat.two_pow_pos w
  have hmem_na : s.mem (brBase rt + brHdrNA rt) = tr.nodeAlloc := hhna
  -- The program reads `nodeAlloc`, then runs `k`.
  obtain ⟨hst_k, hmc_k, hvp_k⟩ :
      let k := if 1 < tr.nodeAlloc then bufClearPopRtProg (rt, tr.nodeAlloc - 1)
        else bufClearRootRtProg rt
      (Memory.spec 0).clientState s (bufClearOneRtProg (rt, ())) =
        (Memory.spec 0).clientState s k ∧
      memoryCost (bufClearOneRtProg (rt, ())) s = 1 + memoryCost k s ∧
      (ValidProg w (base + largeSpaceWhp c U V w n_max) s k →
        ValidProg w (base + largeSpaceWhp c U V w n_max) s (bufClearOneRtProg (rt, ()))) := by
    unfold bufClearOneRtProg
    simp only [pure_bind]
    refine ⟨?_, ?_, fun h => validProg_bind (validProg_read hna_lt_sp) ?_⟩
    · rw [clientState_bind, clientState_memRead, clientResult_memRead, hmem_na]
    · rw [memoryCost_bind', memoryCost_memRead_and_write.1, clientState_memRead,
        clientResult_memRead, hmem_na]
    · rwa [clientState_memRead, clientResult_memRead, hmem_na]
  dsimp only [bufClearOne]
  by_cases hgt : 1 < tr.nodeAlloc
  · rw [ite_eq_left hgt] at hst_k hmc_k hvp_k
    rw [ite_eq_left hgt]
    set u := tr.nodeAlloc - 1
    have hu1 : 1 ≤ u := by omega
    have hu_lt : u < tr.nodeAlloc := by omega
    have hu_max : u < maxTrieNodesWhp c n_max := hu_lt.trans_le hna_max
    set par := tr.nodeParent u
    set ch := tr.nodeChar u
    have hpar_max : par < maxTrieNodesWhp c n_max := (hclr.bounds.2 u hu1 hu_lt).trans hu_max
    have hP : readPacked (brBase rt + brOffMeta rt) (brGBits rt) (brW rt) s.mem (4 * u) = par :=
      (hpar u hu1 hu_lt).1
    have hC : readPacked (brBase rt + brOffMeta rt) (brGBits rt) (brW rt) s.mem (4 * u + 1) = ch :=
      (hpar u hu1 hu_lt).2
    have hiP : 4 * u < 6 * maxTrieNodesWhp c n_max := by omega
    have hiC : 4 * u + 1 < 6 * maxTrieNodesWhp c n_max := by omega
    have hi2 : 4 * u + 2 < 6 * maxTrieNodesWhp c n_max := by omega
    have hupd : ∀ v c', ¬(v = par ∧ c' = ch) →
        Function.update tr.trieChild par (Function.update (tr.trieChild par) ch 0) v c' =
          tr.trieChild v c' := fun v c' h => by
      by_cases hvp : v = par
      · rw [hvp, Function.update_self, Function.update_of_ne fun h' => h ⟨hvp, h'⟩]
      · rw [Function.update_of_ne hvp]
    set se := (Memory.spec 0).clientState s (bufClearEdgeRtProg (rt, (par, ch)))
    obtain ⟨hse_fr, hse_mc, hse_vp, hse_bfr, hse_ch, hse_out⟩ :
        se.frontier = s.frontier ∧
        memoryCost (bufClearEdgeRtProg (rt, (par, ch))) s ≤ 4 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s (bufClearEdgeRtProg (rt, (par, ch))) ∧
        BufEpFrame base c U V w n_max ep s.mem se.mem ∧
        (∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w se.mem
            (v * 2 ^ bCharWhp n_max + c') =
            Function.update tr.trieChild par (Function.update (tr.trieChild par) ch 0) v c') ∧
        (∀ a, ¬(base + brOffChild rt ≤ a ∧ a < base + brOffChild rt +
            packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w) →
          se.mem a = s.mem a) := by
      dsimp only [se]
      rw [bufClearEdgeRtProg_eq]
      dsimp only
      by_cases hch_lt : ch < 2 ^ bCharWhp n_max
      · have hidxE := child_idx_lt hpar_max hch_lt
        rw [ite_eq_left (show ch < brPowBChar rt from hch_lt)]
        simp only [pure_bind]
        rw [clientState_writePackedGen, memoryCost_writePackedGen]
        refine ⟨rfl, le_rfl, validProg_writePacked hw hgk hidxE hc_seg,
          bufEpFrame_writeChild hw hep hidxE, fun v hv c' hc' => ?_,
          fun a ha => writePacked_outside hw _ hidxE _ ha⟩
        by_cases hvc : v = par ∧ c' = ch
        · obtain ⟨rfl, rfl⟩ := hvc
          rw [Function.update_self, Function.update_self]
          exact readPacked_writePacked_self _ _ _ s.mem _ h0_g
        · exact (readPacked_writePacked_of_ne hw s.mem
            (fun heq => hvc ((child_idx_eq_iff hc' hch_lt).mp heq)) 0).trans
            ((hch v hv c' hc').trans (hupd v c' hvc).symm)
      · rw [ite_eq_right (show ¬ch < brPowBChar rt from hch_lt),
          StateTransitionSpec.clientState_pure]
        exact ⟨rfl, Nat.zero_le 4, validProg_pure _, BufEpFrame.refl _, fun v hv c' hc' =>
          (hch v hv c' hc').trans (hupd v c' fun h => hch_lt (h.2 ▸ hc')).symm, fun _ _ => rfl⟩
    set m1 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w se.mem (4 * u + 2) 0
    set m3 := Function.update (Function.update m1 (base + brHdrNA rt) u) (base + brHdrIA rt) 0
    have hst_p : (Memory.spec 0).clientState s (bufClearPopRtProg (rt, u)) =
        { mem := m3, frontier := s.frontier } := by
      rw [bufClearPopRtProg_eq]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen, clientResult_readPackedGen, hP,
        clientState_bind, clientState_readPackedGen, clientResult_readPackedGen, hC,
        clientState_bind, bufClearPopTailRtProg_eq]
      simp only [pure_bind]
      rw [clientState_bind, clientState_writePackedGen, clientState_bind, clientState_memWrite,
        clientState_memWrite]
      exact Memory.State.ext rfl hse_fr
    have hmc_p : memoryCost (bufClearPopRtProg (rt, u)) s ≤ 14 := by
      rw [bufClearPopRtProg_eq]
      simp only [pure_bind]
      rw [memoryCost_bind', memoryCost_readPackedGen, clientState_readPackedGen,
        clientResult_readPackedGen, hP, memoryCost_bind', memoryCost_readPackedGen,
        clientState_readPackedGen, clientResult_readPackedGen, hC, memoryCost_bind',
        bufClearPopTailRtProg_eq]
      simp only [pure_bind, memoryCost_bind', memoryCost_writePackedGen,
        memoryCost_memRead_and_write.2]
      omega
    have hvp_p : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (bufClearPopRtProg (rt, u)) := by
      rw [bufClearPopRtProg_eq]
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw hiP hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, hP]
      refine validProg_bind (validProg_readPacked hw hiC hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, hC]
      refine validProg_bind hse_vp ?_
      rw [bufClearPopTailRtProg_eq]
      simp only [pure_bind]
      refine validProg_bind (validProg_writePacked hw hgk hi2 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validProg_bind (validProg_write hna_lt_sp (henv.fits_of_le_n_max (by omega))) ?_
      rw [clientState_memWrite]
      exact validProg_write hia_lt_sp h0_fit
    rw [hst_k, hst_p]
    refine ⟨rfl, by omega, hvp_k hvp_p, ?_,
      ((hse_bfr.trans (bufEpFrame_writeMeta hw hep hi2)).trans
        (bufEpFrame_write_hdrNA hw hep)).trans (bufEpFrame_write_hdrIA hw hep)⟩
    have hm3_meta : ∀ idx < 6 * maxTrieNodesWhp c n_max, idx ≠ 4 * u + 2 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w m3 idx =
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem idx := fun idx hidx hne =>
      (readPacked_update_outside hw hidx (Or.inl (by omega))).trans
        ((readPacked_update_outside hw hidx (Or.inl (by omega))).trans
          ((readPacked_writePacked_of_ne hw se.mem hne 0).trans
            (readPacked_congr hw (hidx := hidx) fun a ⟨ha1, _⟩ => hse_out a (by omega))))
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    rw [← hrt]
    refine ⟨by omega, Nat.zero_le _,
      (Function.update_of_ne (by omega) ..).trans (Function.update_self ..),
      Function.update_self .., fun v hv c' hc' => ?_,
      fun v hv1 hv => ⟨(hm3_meta _ (by omega) (by omega)).trans (hpar v hv1 (by omega)).1,
        (hm3_meta _ (by omega) (by omega)).trans (hpar v hv1 (by omega)).2⟩,
      fun v hv => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · have hvc := child_idx_lt hv hc'
      exact (readPacked_update_outside hw hvc (Or.inl (by omega))).trans
        ((readPacked_update_outside hw hvc (Or.inl (by omega))).trans
          ((readPacked_writePacked_disjoint hw hvc hi2 (Or.inl (by omega))).trans
            (hse_ch v hv c' hc')))
    · rw [Function.update_of_ne (show v ≠ u by omega)]
      exact ⟨(hm3_meta _ (by omega) (by omega)).trans (hlf v (by omega)).1,
        fun hnz => (hm3_meta _ (by omega) (by omega)).trans ((hlf v (by omega)).2 hnz)⟩
  · rw [ite_eq_right hgt] at hst_k hmc_k hvp_k
    rw [ite_eq_right hgt]
    have hi2_0 : 2 < 6 * maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    set m1 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem 2 0
    set m3 := Function.update (Function.update m1 (base + brHdrNA rt) 1) (base + brHdrIA rt) 0
    have hst_r : (Memory.spec 0).clientState s (bufClearRootRtProg rt) =
        { mem := m3, frontier := s.frontier } := by
      rw [bufClearRootRtProg_eq]
      simp only [pure_bind]
      rw [clientState_bind, clientState_writePackedGen, clientState_bind, clientState_memWrite,
        clientState_memWrite]
      rfl
    have hmc_r : memoryCost (bufClearRootRtProg rt) s = 6 := by
      rw [bufClearRootRtProg_eq]
      simp only [pure_bind, memoryCost_bind', memoryCost_writePackedGen,
        memoryCost_memRead_and_write.2]
    have hvp_r : ValidProg w (base + largeSpaceWhp c U V w n_max) s (bufClearRootRtProg rt) := by
      rw [bufClearRootRtProg_eq]
      simp only [pure_bind]
      refine validProg_bind (validProg_writePacked hw hgk hi2_0 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validProg_bind (validProg_write hna_lt_sp (henv.fits_const (by decide))) ?_
      rw [clientState_memWrite]
      exact validProg_write hia_lt_sp h0_fit
    rw [hst_k, hst_r]
    refine ⟨rfl, by omega, hvp_k hvp_r, ?_,
      ((bufEpFrame_writeMeta hw hep hi2_0).trans (bufEpFrame_write_hdrNA hw hep)).trans
        (bufEpFrame_write_hdrIA hw hep)⟩
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    rw [← hrt]
    refine ⟨by omega, Nat.zero_le _,
      (Function.update_of_ne (by omega) ..).trans (Function.update_self ..),
      Function.update_self .., fun v hv c' hc' => ?_, fun v hv1 hv => by omega,
      fun v hv => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · have hvc := child_idx_lt hv hc'
      exact (readPacked_update_outside hw hvc (Or.inl (by omega))).trans
        ((readPacked_update_outside hw hvc (Or.inl (by omega))).trans
          ((readPacked_writePacked_disjoint hw hvc hi2_0 (Or.inl (by omega))).trans
            (hch v hv c' hc')))
    · obtain rfl : v = 0 := by omega
      rw [Function.update_self]
      exact ⟨(readPacked_update_outside hw hi2_0 (Or.inl (by omega))).trans
          ((readPacked_update_outside hw hi2_0 (Or.inl (by omega))).trans
            (readPacked_writePacked_self _ _ _ s.mem 2 h0_g)),
        fun h => absurd rfl h⟩

/-- Parameter-free wrapper for `iterate bufClearOneRtProg`. -/
def bufClearLoopGenProg : (BufRt × Unit) × ℕ → Memory.Prog Unit
  | ((rt, x), k) => iterate bufClearOneRtProg rt k x

theorem realizes_bufClearLoopGen :
    Realizes .exact bufClearLoopGenProg
      (WordEncoding.encode (α := (BufRt × Unit) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((rt, x), k) s => iterationSafe bufClearOneRtProg BufClearOnePre w rt k x s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := BufRt))
    (WordEncoding.encode (α := Unit))
    realizes_bufClearOneRt
    memoryCost_bufClearOneRtProg_pos

theorem bufClearLoop_spec {c U V w n_max base ep : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    ∀ k (tr : BufTrie) (s : Memory.State),
      BufTrieMemRep base c U V w n_max ep tr s.mem →
      ClearableBufTrie tr →
      let prog := bufClearLoopGenProg ((rt, ()), k)
      let s' := (Memory.spec 0).clientState s prog
      let tr' := bufClearSteps k tr
      iterationSafe bufClearOneRtProg BufClearOnePre w rt k () s ∧
      s'.frontier = s.frontier ∧
      memoryCost prog s ≤ 15 * k ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
      BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  intro rt k
  induction k with
  | zero =>
    intro tr s hrep _
    exact ⟨trivial, rfl, Nat.zero_le _, validProg_pure _, hrep, BufEpFrame.refl _⟩
  | succ k ih =>
    intro tr s hrep hclr
    obtain ⟨hfr1, hmc1, hvp1, hrep1, hbfr1⟩ := bufClearOneRtProg_spec henv hep hrep hclr (s := s)
    obtain ⟨hsafe_k, hfr_k, hmc_k, hvp_k, hrep_k, hbfr_k⟩ :=
      ih (bufClearOne tr) _ hrep1 hclr.clearOne_step.1
    have hprog : bufClearLoopGenProg ((rt, ()), k + 1) =
        bufClearOneRtProg (rt, ()) >>= fun _ => bufClearLoopGenProg ((rt, ()), k) := rfl
    dsimp only
    rw [hprog, clientState_bind, memoryCost_bind']
    exact ⟨⟨⟨c, U, V, w, n_max, base, ep, tr, henv, hep, rfl, hrep, hclr⟩, hsafe_k⟩,
      hfr_k.trans hfr1, (Nat.add_le_add hmc1 hmc_k).trans_eq (by ring), validProg_bind hvp1 hvp_k,
      hrep_k, hbfr1.trans hbfr_k⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
