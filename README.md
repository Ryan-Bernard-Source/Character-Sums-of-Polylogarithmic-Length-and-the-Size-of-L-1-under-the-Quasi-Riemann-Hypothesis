# Character Sums of Polylogarithmic Length and the Size of L(1, χ) under the Quasi-Riemann Hypothesis

*Research Report prepared with Claude (Anthropic) Assistance · 25 November 2026*

## Abstract

Let χ be a non-principal Dirichlet character modulo q. Under the generalised Riemann hypothesis, Granville and Soundararajan proved that Σ_{n≤x} χ(n) = o(x) as soon as log x / log log q → ∞. This range is best possible, and unconditionally nothing better than x ≥ q^{1/4+ε} (Burgess) is known.

We assume only that no Dirichlet L-function vanishes in a half-plane Re s > σ₀ with σ₀ < 1. OpenAI has announced this with σ₀ = 7/8, and Liu has announced it with σ₀ ≈ 0.874957. Under this assumption we prove that Σ_{n≤x} χ(n) = o(x) uniformly once log x ≥ K · log log q · log log log q with K → ∞. This is the Granville–Soundararajan range up to a factor log log log q in the exponent.

The proof gives an explicit Rankin-type bound,

  |Σ_{n≤x} χ(n)| ≪ x (log x)(log y) e^{−u log u + O(u / log u)},

with y = (log qx)^{6/(1−σ₀)} and u = log x / log y. By the same method we prove the Littlewood-type bounds (log log q)⁻¹ ≪ |L(1, χ)| ≪ log log q, with effective constants. These give √d / log log d ≪ h(−d) ≪ √d log log d for imaginary quadratic class numbers.

We test the results numerically on two examples:
- a constructed "pretentious" character of modulus ≈ 3 × 10¹⁷;
- L(1, χ) for 360 prime moduli.

We also give a Lean 4 formalisation. In it the hypothesis, the definitions and the elementary lemmas are fully proved; the main theorems are stated but not yet proved. Every result is conditional on the half-plane hypothesis, whose published proofs have not been peer reviewed.

## Files

| File | Contents |
|---|---|
| `QRH_character_sums_report.pdf` | Full report (15 pp.): theorems, proofs, figures, numerical experiments, Lean appendix |
| `CharacterSums.lean` | Lean 4 module (Mathlib); `QRH σ₀`, smooth-number definitions, Theorems 1 and 3, Corollary 2 |

## Status

- **Mathematics:** proved on paper. Conditional on the half-plane hypothesis Q(σ₀). Not refereed.
- **Lean:** `QRH.mono`, `qrh_of_QRH78Dirichlet` and the two elementary bounds have complete proofs. The three main results are stated exactly and left as `sorry`. **Not yet compiled.**
