import VersoManual
import DispersiveEquations.FourierGaussian.Documentation
import DispersiveEquations.SchroedingerPropagator.Documentation

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.style.setOption false
set_option linter.hashCommand false

set_option pp.rawOnError true

open Verso Doc Elab in
@[role_expander leanVersion]
def leanVersion : RoleExpander
  | #[], #[] => do
    return #[← ``(Verso.Doc.Inline.code $(Lean.Quote.quote Lean.versionString))]
  | _, _ => throwError "Unexpected arguments"

#doc (Manual) "Dispersive equations" =>

This project formalizes some fundamental results in nonlinear dispersive partial differential
equations.

The code is hosted on [Github](https://github.com/mcdoll/DispersiveEquations) and compiled with
Lean {leanVersion}[].

{include 1 DispersiveEquations.FourierGaussian.Documentation}
{include 1 DispersiveEquations.SchroedingerPropagator.Documentation}
