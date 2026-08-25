import VersoManual
import Lean

import Mathlib.Analysis.Distribution.Sobolev

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false

#doc (Manual) "Solving the linear Schrödinger equation" =>

We start by considering the initial value problem for the linear Schrödinger equation on
$`\mathbb{R}^n`,

$$`\left\{\begin{aligned}i∂_t u(t, x) &= Δ u \\ u(0, x) &= u₀.\end{aligned}\right.`

We want to prove that for sufficiently regular $`u₀` there exists a unique solution $`u` solving
the initial value problem and $`u` has some regularity.

# Well-posedness in Schwartz functions

The best possible class of initial data is if $`u₀ ∈ 𝓢(ℝ^n)`. Then we can use the Fourier transform
to obtain a candidate for the solution as

$$`u(t, x) = 𝓕⁻ \left( e ^ {-i t ‖ξ‖ ^ 2 / (4 π ^ 2)} (𝓕 u₀)(ξ) \right)`

We claim that $`u ∈ C^∞(ℝ, 𝓢(ℝ^n))` and $`u` solves the Schrödinger equation with initial data `u₀`.

# Well-posedness in tempered distributions

By duality, we have that the solution operator defines a map $`𝓢'(ℝ^n) → C(ℝ, 𝓢'(ℝ^n))`.

# Well-posedness on Sobolev space

We have the equality

$$`‖u(t, x)‖_{H^s} = ‖u₀‖_{H^s}`

as a consequence of the fact that the solution operator is a Fourier multiplier. By density, we can
thus extend the solution operator to a map $`H^s → C(ℝ, H^2)`.

# Explicit representation of the solution operator

Every Fourier multiplier $`M_f` can be represented as a convolution operator with kernel
$`K = 𝓕⁻ f`. Therefore, the explicit representation of the solution operator follows from the
calculation of the Fourier transform of the complex Gaussian.

test
