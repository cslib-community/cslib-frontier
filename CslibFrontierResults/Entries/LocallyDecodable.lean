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
    { paper := KatzTrevisan2000,
      theorem := "Theorem 1",
      locator := unverified },
    { paper := KerenidisDeWolf2004,
      theorem := "Theorem 9",
      locator := "Appendix B, p. 14 (arXiv:quant-ph/0208062v2)" },
    { paper := Yekhanin2012,
      theorem := "Lemma 5.2 (Steps 1–2)",
      locator := "§5.1, pp. 57–58 (author draft LDC_now.pdf; published monograph pagination \
        unverified)" }
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
    q ≤ 1). Formalizes Steps 1–2 of Yekhanin2012 Lemma 5.2 (Step 3 hypergraph matchings are in \
    Matching.lean; Step 4's binary XOR normal form, Definition 5.1, is not formalized here). \
    Checked against KerenidisDeWolf2004 (arXiv:quant-ph/0208062v2, Appendix B, p. 14) and \
    Yekhanin2012 (author draft LDC_now.pdf, §5.1, pp. 57–58; published monograph pagination \
    unverified); KatzTrevisan2000 page locators remain unverified."

register_result "katz-trevisan-ldc-lower-bound" where
  title := "Katz–Trevisan Ω(k^(q/(q-1))) length lower bound for q-query locally decodable codes"
  topic := "codes"
  sources := [
    { paper := KatzTrevisan2000,
      theorem := unverified,
      locator := unverified },
    { paper := Yekhanin2012,
      theorem := "Lemma 5.3 and Theorem 5.4",
      locator := "§5.2, pp. 61–63 (author draft LDC_now.pdf; published monograph pagination \
        unverified)" }
  ]
  theorems := [
    Cslib.Code.card_mul_one_sub_binEntropy_le_logb_card,
    Cslib.Code.IsLocalDecoder.pow_le_pow_of_nonadaptivePlan,
    Cslib.Code.IsLocalDecoder.rpow_le_card_of_nonadaptivePlan,
    Cslib.Code.IsLocallyDecodable.pow_le_pow,
    Cslib.Code.IsLocallyDecodable.rpow_le_card
  ]
  scope := "Unconditional information-theoretic length lower bounds for (q, δ, ε) locally \
    decodable codes C : (ι → Bool) → P → Γ (k = |ι|, n = |P|) over an arbitrary finite alphabet Γ, \
    with worst-case query budget IsQueryBounded q (ProbOracleComp) and no linearity or binary \
    XOR-normal-form assumption (proved via deterministic edge-predictor hypergraph matchings, \
    DecodingMatching). For Lemma 5.3, card_mul_one_sub_binEntropy_le_logb_card takes deterministic \
    per-coordinate predictors g i : R → Bool recovering each i ∈ T with probability ≥ 1 / 2 + η \
    and gives |T| * (1 - h₂(1 / 2 + η)) ≤ log₂ |R| (implying Yekhanin's randomized-decoder \
    statement by averaging). The sharp binary-entropy bounds pow_le_pow_of_nonadaptivePlan and \
    IsLocallyDecodable.pow_le_pow hold for all 1 ≤ q, 0 < δ, 0 < ε, and [Nonempty Γ] (giving a \
    logarithmic-in-|Γ| upper bound on |ι| at q = 1). For 2 ≤ q, 2 ≤ |Γ|, 0 < δ, and 0 < ε, \
    rpow_le_card_of_nonadaptivePlan and IsLocallyDecodable.rpow_le_card apply Pinsker's inequality \
    to give |P| ≥ c(q, δ, ε, |Γ|) * |ι| ^ (q / (q - 1)) with explicit constants \
    (δ * ε ^ (2q + 1) / (q ^ 2 * (4 log₂ |Γ|) ^ q)) ^ (1 / (q - 1)) (non-adaptive) and \
    (δ * ε ^ (2q + 1) / (q ^ 2 * |Γ| ^ ((q - 1)(2q + 1)) * (4 log₂ |Γ|) ^ q)) ^ (1 / (q - 1)) \
    (adaptive). Neither the binary XOR normal form (Yekhanin2012 Definition 5.1 / Lemma 5.2 Step \
    4) nor two-query exponential lower bounds (#2929) are covered. Checked against Yekhanin2012 \
    (author draft LDC_now.pdf, §5.2, pp. 61–63; published monograph pagination unverified); \
    KatzTrevisan2000 theorem numbering and page locators remain unverified."
