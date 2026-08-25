import VersoManual
import DispersiveEquations.Documentation

open Verso.Genre Manual

def main := manualMain (%doc DispersiveEquations.Documentation) (options := ["--output", "html"])
