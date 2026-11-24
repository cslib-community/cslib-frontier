/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.LocallyDecodable.LowerBound
import CslibFrontier.Computability.LocallyDecodable.Smoothing

/-!
# Collected results: Katz–Trevisan smoothing and lower bounds for locally decodable codes
-/

register_result "katz-trevisan-ldc-smoothing" where
  title := "Katz–Trevisan smoothing: every locally decodable code is smooth"
  topic := "codes"
  sources := [
    { paper := KatzTrevisan2000, theorem := "Theorem 1", locator := unverified },
    { paper := KerenidisDeWolf2004, theorem := "Theorem 9", locator := unverified },
    { paper := Yekhanin2012, theorem := "Lemma 5.2", locator := unverified }
  ]
  theorems := [
    Cslib.Code.isSmoothDecoder_mask_heavyPositions,
    Cslib.Code.isSmoothDecoder_mask_nonadaptivePlan,
    Cslib.Code.IsLocalDecoder.isSmoothDecoder_adaptive,
    Cslib.Code.IsLocallyDecodable.isSmoothCode
  ]
  scope := "For messages ι → Bool and codewords P → Γ over a finite alphabet Γ, local decoders \
    are worst-case q-query ProbOracleComp programs (IsQueryBounded q) and IsSmoothDecoder bounds \
    expected reads of each position by c / |P| (which upper-bounds per-position read probability). \
    Masking heavy positions against a fixed word smooths any (q, δ, ε) decoder with oblivious \
    expected reads (isSmoothDecoder_mask_heavyPositions) or non-adaptive query plans \
    (isSmoothDecoder_mask_nonadaptivePlan) to a (q, q / δ, ε) smooth decoder with no loss in \
    advantage. For arbitrary adaptive q-query decoders over a finite nonempty alphabet Γ, \
    guessing the first q - 1 oracle answers uniformly at random with early-stop attenuation \
    (nonadaptivize) scales output bias by |Γ| ^ -(q - 1) and yields a \
    (q, q / δ, ε / |Γ| ^ (q - 1)) smooth decoder and smooth code \
    (IsLocalDecoder.isSmoothDecoder_adaptive, IsLocallyDecodable.isSmoothCode; no loss at \
    q ≤ 1). Source page locators were not re-verified against primary PDFs in this session; \
    pending independent outside-fleet source check."

register_result "katz-trevisan-ldc-lower-bound" where
  title := "Katz–Trevisan Ω(k^(q/(q-1))) length lower bound for q-query locally decodable codes"
  topic := "codes"
  sources := [
    { paper := KatzTrevisan2000, theorem := unverified, locator := unverified },
    { paper := Yekhanin2012, theorem := "Lemma 5.3 and Theorem 5.4", locator := unverified }
  ]
  theorems := [
    Cslib.Code.IsLocalDecoder.pow_le_pow_of_nonadaptivePlan,
    Cslib.Code.IsLocalDecoder.rpow_le_card_of_nonadaptivePlan,
    Cslib.Code.IsLocallyDecodable.pow_le_pow,
    Cslib.Code.IsLocallyDecodable.rpow_le_card
  ]
  scope := "Unconditional information-theoretic length lower bounds for (q, δ, ε) locally \
    decodable codes C : (ι → Bool) → P → Γ (k = |ι|, n = |P|) over an arbitrary finite alphabet Γ, \
    with worst-case query budget IsQueryBounded q (ProbOracleComp) and no linearity or binary \
    XOR-normal-form assumption (proved via deterministic edge-predictor hypergraph matchings, \
    DecodingMatching). The sharp binary-entropy bounds pow_le_pow_of_nonadaptivePlan and \
    IsLocallyDecodable.pow_le_pow hold for all 1 ≤ q, 0 < δ, 0 < ε, and [Nonempty Γ] (giving a \
    logarithmic-in-|Γ| upper bound on |ι| at q = 1). For 2 ≤ q, 2 ≤ |Γ|, 0 < δ, and 0 < ε, \
    rpow_le_card_of_nonadaptivePlan and IsLocallyDecodable.rpow_le_card apply Pinsker's inequality \
    to give |P| ≥ c(q, δ, ε, |Γ|) * |ι| ^ (q / (q - 1)) with explicit constants \
    (δ * ε ^ (2q + 1) / (q ^ 2 * (4 log₂ |Γ|) ^ q)) ^ (1 / (q - 1)) (non-adaptive) and \
    (δ * ε ^ (2q + 1) / (q ^ 2 * |Γ| ^ ((q - 1)(2q + 1)) * (4 log₂ |Γ|) ^ q)) ^ (1 / (q - 1)) \
    (adaptive). Two-query exponential lower bounds (#2929) are not covered. Source page locators \
    (and exact KatzTrevisan2000 theorem numbering) were not re-verified against primary PDFs in \
    this session; pending independent outside-fleet source check."
