import Mathlib.Lean.CoreM
import Mathlib.Lean.Expr.Basic
import ImportGraph.RequiredModules
import Cli
import Lean
import LeanExtras

open Lean Cli

def runSubtermCommand (p : Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let options : Options := maxHeartbeats.set {} 0
  let fpath := p.positionalArg! "fpath" |>.as! String
  let cores := p.positionalArg! "cores" |>.as! Nat
  let fpath : System.FilePath := fpath
  let handle ← IO.FS.Handle.mk fpath .write
  CoreM.withImportModules (options := options) #[`Mathlib] do
    let env ← getEnv
    let mut ds := #[]
    for (n,c) in env.constants do
      if ← n.isBlackListed then continue
      ds := ds.push (n,c)
    let state ← get
    let ctx ← read
    let res ← ds.runInParallel cores fun _idx (n,c) => 
      Prod.fst <$> Core.CoreM.toIO (s := state) (ctx := ctx) (Meta.MetaM.run' <| go handle n c)
    match res with 
    | .ok () => return 0
    | .error e => show IO _ from throw e
where go handle nm cinfo := do
  let some mod := (← getEnv).getModuleFor? nm | return .ok ()
  println! s!"{nm} :: {mod}"
  Meta.forEachExpr cinfo.type fun e => do
    let j : Json := .mkObj [
      ("val", false),
      ("pp", toString <| ← Meta.ppExpr e),
      ("nm", toString nm),
      ("mod", toJson <| mod),
      ("cs", toJson e.getUsedConstants),
    ]
    handle.putStrLn j.compress
  if let some val := cinfo.value? then Meta.forEachExpr val fun e => do
    let j : Json := .mkObj [
      ("val", true),
      ("pp", toString <| ← Meta.ppExpr val),
      ("nm", toString nm),
      ("mod", toJson <| mod),
      ("cs", toJson e.getUsedConstants)
    ]
    handle.putStrLn j.compress
  return .ok ()

def subtermCommand := `[Cli|
  constant_prep_data VIA runSubtermCommand ; "Generate subterm data"
  FLAGS:
  ARGS:
    cores : Nat ; "Number of cores to use"
    fpath : String ; "Path"
]

def main (args : List String) : IO UInt32 := do
  subtermCommand.validate args
