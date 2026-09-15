import VersoManual
import DispersiveEquations.Bibliography

import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Distribution.Sobolev

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open DispersiveEquations.Refs

set_option linter.hashCommand false

#doc (Manual) "The Fourier transform of a complex Gaussian" =>
%%%
tag := "FTGaussian"
htmlSplit := .never
%%%

The derivation of the explicit form of the kernel of the Schrödinger propagator hinges on the fact
that we can calculate the Fourier transform of the Gaussians

$$`u(x) = e^{-⟨A x, x⟩ / 2}`

for some non-degenerate symmetric matrix $`A` with $`\operatorname{Re}(A) ≥ 0`.


If $`A` is real, symmetric and non-degenerate, then the Fourier transform of

$$`u(x) = e^{-i⟨A x, x⟩ / 2}`

is given by

$$`\hat{u}(ξ) = ∣\operatorname{det}(A)|^{-1/2} e^{iπ \operatorname{sgn}(A)/4} e^{i ⟨A⁻¹ ξ, ξ⟩ / 2}`

(This is not entirely correct, there will be funny factors of $`2π`).

This chapter follows {citet Hormander1}[Section 7.6].

# Sketch of the proof

There are various proofs of this calculation and it is impossible to completely avoid using a basis
and a diagonalizing $`A`.

## Step 0: Complex Gaussians as tempered distributions

The very first step to even state the theorem in Lean is to define the complex Gaussian as a
tempered distribution. Along the way, one should also define the real Gaussian
$$`u(x) = e^{-⟨A x, x⟩}`
for $`A` positive definite as a Schwartz function.

Writing $`A = A₀ + i B₀`, we have that
$$`\begin{aligned}
e^{-⟨A x, x⟩ / 2} &= e^{-⟨A₀ x, x⟩} e^{-i ⟨B₀ x, x⟩}
\end{aligned}`
Since by assumption $`A₀` is strictly positive, the first factor is a Schwartz function. The second
factor has temperate growth and therefore the product defines a tempered distribution.

## Step 1: A simple regularity theorem

First we prove that a tempered distribution $`u` that satisfies $`∂_x u = 0` for all $`x` is
constant. An equivalent statement is that if $`u` satisfies $`x u = 0` for all $`x`, then
$`u = c δ₀` for some constant $`c`.
This is Theorem 3.1.16 in {citet Hormander1}[].

The proof of Theorem 3.1.16 is straightforward: let $`φ` be a test function and using Taylor's
theorem, write
$$`φ x = φ 0 + ∑ x_j φ_j x`
for some $`φ_j`. Then plug this expression into $`u` and use the assumption.

## Step 2: ODE of the Gaussian

Next we observe that $`(∂_x + A x) u = 0` if and only if $`u(x) = c · e^{-⟨A x, x⟩ / 2}`. This
relies on Step 0 and Step 1.

One direction is trivial, for the other direction apply Step 1 to $`e^{⟨A x, x⟩ / 2} u`.

## Step 3: Calculate the Fourier transform up to a constant

From Step 2 we derive that the Fourier transform of a complex Gaussian is again a complex Gaussian.

## Step 4: Calculate the constant: part 1

tba

## Step 5: Calculate the constant: part 2

tba
