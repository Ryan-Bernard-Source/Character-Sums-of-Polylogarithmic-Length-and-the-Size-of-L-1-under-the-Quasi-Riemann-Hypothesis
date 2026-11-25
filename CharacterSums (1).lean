import LFun.Inputs

/-!
# Character sums of polylogarithmic length under a zero-free half-plane

Companion to the report *Character sums of polylogarithmic length and `L(1,χ)` under the
quasi-Riemann hypothesis* (Sections 2–5).

Everything is stated for a general zero-free half-plane `Re s > σ₀` (`QRH σ₀`), so it applies to:
* OpenAI's `σ₀ = 7/8`, via `qrh_of_QRH78Dirichlet`;
* B. Liu's improvement `σ₀ ≈ 0.874957` (arXiv:2610.12234), via `QRH.mono`;
* GRH itself (`σ₀ = 1/2`).

Fully proved in this file:
* `qrh_of_QRH78Dirichlet`;
* `QRH.mono`;
* `norm_charSum_le`, the trivial bound;
* `norm_smoothCharSum_le`, i.e. `|Ψ(x,y;χ)| ≤ Ψ(x,y)`.

Proved on paper, still `sorry` here:
* `char_sum_rankin` (Theorem 1);
* `char_sum_little_o_polylog` (Corollary 2);
* `L1_bounds` (Theorem 3).

STATUS: not yet compiled. The Lean toolchain could not be run in the environment where this
file was written.
-/

open Complex Real

noncomputable section

namespace LFun

open scoped Classical

/-! ## The hypothesis -/

/-- `QRH σ₀`: no Dirichlet `L`-function (principal or not, primitive or not) vanishes in
`Re s > σ₀`, apart from the pole of the principal one at `s = 1`. -/
def QRH (σ₀ : ℝ) : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    σ₀ < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- OpenAI's theorem (family 003) is `QRH (7/8)`. -/
theorem qrh_of_QRH78Dirichlet (h : QRH78Dirichlet) : QRH (7 / 8) := h

/-- A zero-free half-plane implies every smaller one. -/
theorem QRH.mono {σ₀ σ₁ : ℝ} (h : QRH σ₀) (hle : σ₀ ≤ σ₁) : QRH σ₁ := by
  intro q _ χ s hs hne
  exact h χ (lt_of_le_of_lt hle hs) hne

/-! ## Character sums and smooth numbers -/

/-- `n` is `y`-smooth: every prime factor of `n` is at most `y`. -/
def IsSmooth (y : ℝ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y

/-- `S(x,χ) = ∑_{1 ≤ n ≤ x} χ(n)`. -/
def charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, χ (n : ZMod q)

/-- `Ψ(x,y;χ) = ∑_{n ≤ x, n y-smooth} χ(n)`. -/
def smoothCharSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 x).filter (IsSmooth y), χ (n : ZMod q)

/-- `Ψ(x,y) = #{n ≤ x : n is y-smooth}`. -/
def Psi (x : ℕ) (y : ℝ) : ℕ := ((Finset.Icc 1 x).filter (IsSmooth y)).card

/-- The trivial bound `|S(x,χ)| ≤ x`. -/
theorem norm_charSum_le {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℕ) :
    ‖charSum χ x‖ ≤ x := by
  unfold charSum
  calc ‖∑ n ∈ Finset.Icc 1 x, χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc 1 x, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 x, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
    _ = x := by simp

/-- `|Ψ(x,y;χ)| ≤ Ψ(x,y)`. -/
theorem norm_smoothCharSum_le {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℕ) (y : ℝ) :
    ‖smoothCharSum χ x y‖ ≤ Psi x y := by
  unfold smoothCharSum Psi
  calc ‖∑ n ∈ (Finset.Icc 1 x).filter (IsSmooth y), χ (n : ZMod q)‖
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (IsSmooth y), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ (Finset.Icc 1 x).filter (IsSmooth y), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
    _ = ((Finset.Icc 1 x).filter (IsSmooth y)).card := by simp

/-! ## Rankin parameters (Section 2 of the report) -/

/-- `y = (log qx)^{6/(1-σ₀)}`. -/
def rankinY (σ₀ : ℝ) (q x : ℕ) : ℝ := (Real.log ((q : ℝ) * x)) ^ (6 / (1 - σ₀))

/-- `u = log x / log y`. -/
def rankinU (σ₀ : ℝ) (q x : ℕ) : ℝ := Real.log x / Real.log (rankinY σ₀ q x)

/-! ## Main results -/

/-- **Theorem 1 (Rankin-type bound for character sums under `QRH σ₀`).**
Let `y = (log qx)^{6/(1-σ₀)}` and `u = log x / log y ≥ e`. Every non-principal `χ` mod `q`
satisfies
`|∑_{n ≤ x} χ(n)| ≤ C x (log x)(log y) exp(-u log u + C u / log u) + C log x`,
where `C` depends only on `σ₀`. -/
theorem char_sum_rankin {σ₀ : ℝ} (h0 : 1 / 2 ≤ σ₀) (h1 : σ₀ < 1) (hQ : QRH σ₀) :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ x : ℕ,
      Real.exp 1 ≤ rankinU σ₀ q x →
      ‖charSum χ x‖ ≤
        C * x * Real.log x * Real.log (rankinY σ₀ q x) *
            Real.exp (-(rankinU σ₀ q x * Real.log (rankinU σ₀ q x)) +
              C * rankinU σ₀ q x / Real.log (rankinU σ₀ q x))
          + C * Real.log x := by
  sorry

/-- **Corollary 2 (`o(x)` at length `(log q)^{K log log log q}`).** For every `η > 0` there is
`K` such that `|∑_{n ≤ x} χ(n)| ≤ η x` for every non-principal `χ` mod `q ≥ 16` and every `x`
with `log x ≥ K · log log q · log log log q`. Under GRH, Granville–Soundararajan obtain this
with `K · log log q`. Unconditionally the range cannot be pushed below `log x = A log log q`
for any fixed `A`. -/
theorem char_sum_little_o_polylog {σ₀ : ℝ} (h0 : 1 / 2 ≤ σ₀) (h1 : σ₀ < 1) (hQ : QRH σ₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 16 ≤ q →
      ∀ x : ℕ, K * Real.log (Real.log q) * Real.log (Real.log (Real.log q)) ≤ Real.log x →
        ‖charSum χ x‖ ≤ η * x := by
  sorry

/-- **Theorem 3 (Littlewood-type bounds for `L(1,χ)`).** Every non-principal `χ` mod `q ≥ 16`
satisfies `(C log log q)⁻¹ ≤ |L(1,χ)| ≤ C log log q`, with `C` depending only on `σ₀` and
effectively computable. -/
theorem L1_bounds {σ₀ : ℝ} (h0 : 1 / 2 ≤ σ₀) (h1 : σ₀ < 1) (hQ : QRH σ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 16 ≤ q →
      ‖χ.LFunction 1‖ ≤ C * Real.log (Real.log q) ∧
      1 ≤ C * Real.log (Real.log q) * ‖χ.LFunction 1‖ := by
  sorry

/-- Corollary 2 for OpenAI's half-plane. -/
theorem char_sum_little_o_polylog_78 (hQ : QRH78Dirichlet) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 16 ≤ q →
      ∀ x : ℕ, K * Real.log (Real.log q) * Real.log (Real.log (Real.log q)) ≤ Real.log x →
        ‖charSum χ x‖ ≤ η * x :=
  char_sum_little_o_polylog (by norm_num) (by norm_num) (qrh_of_QRH78Dirichlet hQ) hη

end LFun

end
