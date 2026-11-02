import Lean
import Lake.Check.Compare

open Lean

structure Spec where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  deriving FromJson

def loadConstants (mod : Name) : IO LeanExport.ExportedEnv := do
  let env ← importModules #[{ module := mod }] {}
  let mut constants := {}
  for (name, info) in env.constants do
    constants := constants.insert name info
  return { constMap := constants, constOrder := #[] }

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let spec : Spec ← IO.ofExcept (Json.parse (← IO.FS.readFile args[0]!) >>= fromJson?)
  IO.println s!"Loading challenge {spec.challenge_module}"
  let challenge ← loadConstants spec.challenge_module.toName
  IO.println s!"Loading solution {spec.solution_module}"
  let solution ← loadConstants spec.solution_module.toName
  match Lake.Check.compareAt challenge solution (spec.theorem_names.map String.toName) #[] #[] with
  | .ok () => IO.println s!"MATCH: all {spec.theorem_names.size} selected statements and their supporting declaration closure"
  | .error message => throw (IO.userError message)
