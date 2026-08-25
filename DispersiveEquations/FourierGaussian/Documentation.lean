import VersoManual
import Lean

import Mathlib.Analysis.Distribution.Sobolev

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false

#doc (Manual) "The Fourier transform of a complex Gaussian" =>

The derivation of the explicit form of the kernel of the Schrödinger propagator hinges on the fact
that we can calculate the Fourier transform of the Gaussians

$$`u(x) = e^{-⟨A x, x⟩ / 2}`

for some non-degenerate symmetric matrix $`A` with $`\operatorname{Re}(A) ≥ 0`.


If $`A` is real, symmetric and non-degenerate, then the Fourier transform of

$$`u(x) = e^{-i⟨A x, x⟩ / 2}`

is given by

$$`\hat{u}(ξ) = ∣\operatorname{det}(A)|^{-1/2} e^{iπ \operatorname{sgn}(A)/4} e^{i ⟨A⁻¹ ξ, ξ⟩ / 2}`

(This is not entirely correct, there will be funny factors of $`2π`).

# Sketch of the proof

There are various proofs of this calculation and it is impossible to completely avoid using a basis
and a diagonalizing $`A`.

## Step 1: A simple regularity theorem

First we prove that a tempered distribution $`u` that satisfies $`∂_x u` for all $`x` is constant.
This is Theorem 3.1.16 in Hörmander.

## Step 2: ODE of the Gaussian

Next we observe that $`(∂_x + A x) u = 0` if and only if $`u(x) = c · e^{-⟨A x, x⟩ / 2}`.

## Step 3: calculating the constant

tba
