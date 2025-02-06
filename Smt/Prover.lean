/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Std.Data.HashMap

import Smt.Reconstruct
import Smt.Translate.Query
import Smt.Solver
namespace Smt

open Lean hiding Command
open Translate

inductive SOSKind where
  | tsds
  | schd

deriving DecidableEq, Inhabited, Hashable

def allSOSKinds : List SOSKind := [
  SOSKind.tsds,
  SOSKind.schd,
]

instance : ToString SOSKind where
  toString
    | .tsds => "tsds"
    | .schd => "schd"

instance : Lean.KVMap.Value SOSKind where
  toDataValue k := toString k
  ofDataValue?
    | "tsds" => SOSKind.tsds
    | "schd" => SOSKind.schd
    | _      => none

inductive SosResult where
  | unsat : String → SosResult
  | except  : String → SosResult
  | timeout : String → SosResult
deriving DecidableEq, Inhabited

instance : ToString SosResult where
  toString : SosResult → String
    | .unsat msg   => "unsat. " ++ msg
    | .except msg  => "except. " ++ msg
    | .timeout msg => "timeout. " ++ msg

/-- What the binary for a given solver is usually called. -/
def SOSKind.toDefaultPath : SOSKind → String
  | k      => toString k

/-- The data-structure for the state of the generic SMT-LIB solver. -/
structure ProverState where
  commands : List Command
  args : Std.HashMap SOSKind (Array String)

abbrev ProverT (m) [Monad m] [MonadLiftT IO m] := StateT ProverState m

abbrev ProverM := ProverT IO

namespace Prover

variable [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]

def addCommand (c : Command) : ProverT m Unit := do
  let state ← get
  set { state with commands := c :: state.commands }

def addCommands : List Command → ProverT m Unit := (List.forM · addCommand)

/-- Create an instance of a pre-configured SMT solver. -/
def create (timeoutSecs : Nat) (solvers : List SOSKind): IO ProverState := do
  let allArgs : Std.HashMap SOSKind (Array String) := Std.HashMap.ofList [
    (.tsds,      #["--timeout", toString timeoutSecs]),
    (.schd,      #["--timeout", toString timeoutSecs]),
  ]
  let args := solvers.foldl (fun acc solver =>
    match allArgs.get? solver with
    | some args => acc.insert solver args
    | none => acc
  ) Std.HashMap.empty
  return ⟨[], args⟩

/-- Set the SMT query logic to `l`. -/
def setLogic (l : String) : ProverT m Unit := addCommand (.setLogic l)

/-- Set option `k` to value `v`. -/
def setOption (k : String) (v : String) : ProverT m Unit := addCommand (.setOption k v)

/-- Define a sort with name `id` and arity `n`. -/
def declareSort (id : String) (n : Nat) : ProverT m Unit := addCommand (.declareSort id n)

/-- Define a sort with name `id`. -/
def defineSort (id : String) (ss : List Term) (s : Term) : ProverT m Unit :=
  addCommand (.defineSort id ss s)

/-- Declare a symbolic constant with name `id` and sort `s`. -/
def declareConst (id : String) (s : Term) : ProverT m Unit := addCommand (.declare id s)

/-- Declare an uninterpreted function with name `id` and sort `s`. -/
def declareFun (id : String) (s : Term) : ProverT m Unit := addCommand (.declare id s)

/-- Define a function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFun (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  ProverT m Unit := addCommand (.defineFun id ps s t false)

/-- Define a recursive function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFunRec (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  ProverT m Unit := addCommand (.defineFun id ps s t true)

/-- Assert that proposition `t` is true. -/
def assert (t : Term) : ProverT m Unit := addCommand (.assert t)

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat : ProverT m SosResult := do
  let state ← get

  let mut args : Array String := #[]

  for kind in allSOSKinds do
    match state.args.get? kind with
    | some argArray =>
        args := args.push s!"--{kind.toDefaultPath}"
        let combinedArgs := argArray.foldl (fun r s => r ++ " " ++ s) ""
        args := args.push combinedArgs
    | none => continue

  let proc ← IO.Process.spawn {
    cmd := "mtprove"
    args := args
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

  for c in state.commands.reverse ++ [.exit] do
    proc.stdin.putStr s!"{c}\n"

  proc.stdin.flush
  let (_, proc) ← proc.takeStdin
  let _ ← proc.wait

  let res := (← proc.stdout.readToEnd).trim
  let msg := (← proc.stderr.readToEnd).trim

  match res with
  | "False"     => return (.except msg)
  | "True"   => return (.unsat msg)
  | _ => (throw (IO.userError s!"unexpected solver output\nstdout: {res}\nstderr: {msg}") : IO _)

end Smt.Prover
