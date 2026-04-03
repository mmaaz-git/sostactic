import Lean
import Lean.Data.Json

open Lean

namespace Sostactic

-- BACKEND DATA

structure SerializedPoly where
  expr : String
  deriving Inhabited, FromJson

structure SerializedWeightedSOSTerm where
  weight : String
  poly : SerializedPoly
  deriving Inhabited, FromJson

structure SerializedCoeffWitness where
  exponents : List Nat
  coeff : String
  deriving Inhabited, FromJson

structure BackendResult where
  success : Bool
  exact_sos : Option (List SerializedWeightedSOSTerm) := none
  exact_num_sos : Option (List SerializedWeightedSOSTerm) := none
  exact_den_sos : Option (List SerializedWeightedSOSTerm) := none
  exact_den_poly : Option SerializedPoly := none
  exact_den_nonzero_coeff_witness : Option SerializedCoeffWitness := none
  suggestion : Option String := none
  deriving Inhabited, FromJson

structure SerializedCertBlock where
  multiplier : SerializedPoly
  sos_poly : SerializedPoly
  weighted_sos : List SerializedWeightedSOSTerm
  multiplier_factors : List SerializedPoly := []
  multiplier_factor_indices : List Nat := []
  deriving Inhabited, FromJson

structure PstvResult where
  success : Bool
  exact_certificate_blocks : Option (List SerializedCertBlock) := none
  suggestion : Option String := none
  deriving Inhabited, FromJson

-- BACKEND PATHS

partial def findBundledScript? (dir : System.FilePath) : IO (Option System.FilePath) := do
  let candidate := dir / "python" / "sos.py"
  if ← System.FilePath.pathExists candidate then
    return some candidate
  let parent := dir.parent.getD dir
  if parent == dir then
    return none
  findBundledScript? parent

def defaultScriptPath : IO System.FilePath := do
  match ← IO.getEnv "SOSTACTIC_SCRIPT" with
  | some path => pure <| System.FilePath.mk path
  | none =>
      let olean ← Lean.findOLean `Sostactic.Backend
      match ← findBundledScript? (olean.parent.getD olean) with
      | some path => pure path
      | none => pure <| System.FilePath.mk "python/sos.py"

def defaultPythonPath : IO String := do
  match ← IO.getEnv "SOSTACTIC_PYTHON" with
  | some path => return path
  | none =>
    let venvPython := System.FilePath.mk ".venv" / "bin" / "python3"
    if ← System.FilePath.pathExists venvPython then
      return venvPython.toString
    return "python3"

-- UTILS

def leanToBackend (text : String) : String :=
  text.replace "^" "**"

def backendToLean (text : String) : String :=
  text.replace "**" "^"

def parseBackendResult (text : String) : Except String BackendResult := do
  let json ← Json.parse text
  fromJson? json

def backendSetupMessage : String :=
  String.intercalate "\n" [
    "sostactic backend is unavailable.",
    "",
    "Required:",
    "  python3",
    "  sympy",
    "  numpy",
    "  cvxpy",
    "  clarabel",
    "",
    "Suggested setup:",
    "  python3 -m venv .venv",
    "  . .venv/bin/activate",
    "  pip install -r python/requirements.txt",
    "",
    "Optional environment variables:",
    "  SOSTACTIC_PYTHON=/path/to/python",
    "  SOSTACTIC_SCRIPT=/path/to/sos.py",
  ]

-- BACKEND CALL

def runSosBackend (poly : String) (denomDegreeBound : Nat := 0)
    (denomTemplate : Option String := none) : CoreM BackendResult := do
  let python ← defaultPythonPath
  let script ← defaultScriptPath
  if !(← System.FilePath.pathExists script) then
    throwError "sostactic backend script not found at '{script}'.\n\n{backendSetupMessage}"

  let mut args := #[
    toString script,
    "sos_decomp",
    "--poly",
    leanToBackend poly,
    "--denom-degree-bound",
    toString denomDegreeBound,
  ]
  if let some tmpl := denomTemplate then
    args := args ++ #["--denom-template", leanToBackend tmpl]
  let out ← IO.Process.output {
    cmd := python
    args := args
  }
  if out.exitCode != 0 then
    throwError m!"sostactic backend failed.\ncommand: {python} {String.intercalate " " args.toList}\n\nstderr:\n{out.stderr}\n\n{backendSetupMessage}"

  match parseBackendResult out.stdout with
  | .error err =>
      throwError m!"failed to parse backend JSON:{indentD err}\n\nstdout:\n{out.stdout}"
  | .ok result =>
      return result

def parsePstvResult (text : String) : Except String PstvResult := do
  let json ← Json.parse text
  fromJson? json

def runPstvBackend (command : String) (poly : String) (constraints : String)
    (order : Nat) (basisOverrides : Option String := none) : CoreM PstvResult := do
  let python ← defaultPythonPath
  let script ← defaultScriptPath
  if !(← System.FilePath.pathExists script) then
    throwError "sostactic backend script not found at '{script}'.\n\n{backendSetupMessage}"

  let mut args := #[
    toString script,
    command,
    "--poly",
    leanToBackend poly,
    "--constraints",
    leanToBackend constraints,
    "--order",
    toString order,
  ]
  if let some bo := basisOverrides then
    args := args ++ #["--basis-overrides", bo]
  let out ← IO.Process.output {
    cmd := python
    args := args
  }
  if out.exitCode != 0 then
    throwError m!"sostactic backend failed.\ncommand: {python} {String.intercalate " " args.toList}\n\nstderr:\n{out.stderr}\n\n{backendSetupMessage}"

  match parsePstvResult out.stdout with
  | .error err =>
      throwError m!"failed to parse backend JSON:{indentD err}\n\nstdout:\n{out.stdout}"
  | .ok result =>
      return result

-- CERTIFICATE LOADING

def loadBackendResult (path : System.FilePath) : CoreM BackendResult := do
  unless ← System.FilePath.pathExists path do
    throwError "certificate file not found: '{path}'"
  let text ← IO.FS.readFile path
  match parseBackendResult text with
  | .error err =>
      throwError m!"failed to parse certificate file '{path}':{indentD err}"
  | .ok result =>
      unless result.success do
        throwError "certificate file '{path}' contains a failed result (success = false)"
      return result

def loadPstvResult (path : System.FilePath) : CoreM PstvResult := do
  unless ← System.FilePath.pathExists path do
    throwError "certificate file not found: '{path}'"
  let text ← IO.FS.readFile path
  match parsePstvResult text with
  | .error err =>
      throwError m!"failed to parse certificate file '{path}':{indentD err}"
  | .ok result =>
      unless result.success do
        throwError "certificate file '{path}' contains a failed result (success = false)"
      return result

end Sostactic
