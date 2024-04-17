/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean
import Std.Data.HashMap
import Smt.Commands
import Smt.Data.Sexp
import Smt.Term

open Std

namespace Smt

inductive Kind where
  --| boolector
  | cvc5
  | vampire
  --| yices
  | z3
  | sysol
  | syopt
  | bottema

deriving DecidableEq, Inhabited, Hashable

def allKinds : List Kind := [
  -- Kind.boolector,
  Kind.cvc5,
  Kind.vampire,
  -- Kind.yices,
  Kind.z3,
  Kind.sysol,
  Kind.syopt,
  Kind.bottema
]

instance : ToString Kind where
  toString
    --| .boolector => "boolector"
    | .cvc5      => "cvc5"
    | .vampire   => "vampire"
    --| .yices     => "yices"
    | .z3        => "z3"
    | .sysol     => "sysol"
    | .syopt     => "syopt"
    | .bottema   => "bottema"

instance : Lean.KVMap.Value Kind where
  toDataValue k := toString k
  ofDataValue?
    --| "boolector" => Kind.boolector
    | "cvc5"      => Kind.cvc5
    | "vampire"   => Kind.vampire
    --| "yices"     => Kind.yices
    | "z3"        => Kind.z3
    | "sysol"     => Kind.sysol
    | "syopt"     => Kind.syopt
    | "bottema"   => Kind.bottema
    | _           => none

/-- What the binary for a given solver is usually called. -/
def Kind.toDefaultPath : Kind → String
  --| .yices => "yices-smt2"
  | k      => toString k

inductive Result where
  | sat : String → Result
  | unsat : String → Result
  | unknown : String → Result
  | except  : String → Result
  | timeout : String → Result
deriving DecidableEq, Inhabited

instance : ToString Result where
  toString : Result → String
    | .sat msg     => "sat. " ++ msg
    | .unsat msg   => "unsat. " ++ msg
    | .unknown msg => "unknown. " ++ msg
    | .except msg  => "except. " ++ msg
    | .timeout msg => "timeout. " ++ msg

/-- The data-structure for the state of the generic SMT-LIB solver. -/
structure SolverState where
  commands : List Command
  args : HashMap Kind (Array String)

abbrev SolverT (m) [Monad m] [MonadLiftT IO m] := StateT SolverState m

abbrev SolverM := SolverT IO

namespace Solver

variable [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]

def addCommand (c : Command) : SolverT m Unit := do
  let state ← get
  set { state with commands := c :: state.commands }

def addCommands : List Command → SolverT m Unit := (List.forM · addCommand)

/-- Create an instance of a pre-configured SMT solver. -/
def create (timeoutSecs : Nat) : IO SolverState := do
  let args : HashMap Kind (Array String) := HashMap.ofList [
    --(.boolector, #["--smt2", "--time", toString timeoutSecs]),
    -- (.cvc5,      #["--timeout", toString timeoutSecs]), -- #["--quiet", "--incremental", "--lang", "smt", "--dag-thresh=0",
                                                        -- "--produce-proofs", "--proof-granularity=theory-rewrite",
                                                        -- "--proof-format=lean", "--enum-inst"]
    -- (.vampire,   #["--input_syntax", "smtlib2", "--output_mode", "smtcomp", "--time_limit", toString timeoutSecs]),
    --(.yices,     #["--timeout", toString timeoutSecs]),
    (.z3,        #["--timeout", toString timeoutSecs]), -- #["-in", "-smt2"]
    -- (.sysol,     #["--timeout", toString timeoutSecs]),
    -- (.syopt,     #["--timeout", toString timeoutSecs]),
    -- (.bottema,   #["--timeout", toString timeoutSecs]),
  ]
  return ⟨[], args⟩

/-- Set the SMT query logic to `l`. -/
def setLogic (l : String) : SolverT m Unit := addCommand (.setLogic l)

/-- Set option `k` to value `v`. -/
def setOption (k : String) (v : String) : SolverT m Unit := addCommand (.setOption k v)

/-- Define a sort with name `id` and arity `n`. -/
def declareSort (id : String) (n : Nat) : SolverT m Unit := addCommand (.declareSort id n)

/-- Define a sort with name `id`. -/
def defineSort (id : String) (ss : List Term) (s : Term) : SolverT m Unit :=
  addCommand (.defineSort id ss s)

/-- Declare a symbolic constant with name `id` and sort `s`. -/
def declareConst (id : String) (s : Term) : SolverT m Unit := addCommand (.declare id s)

/-- Declare an uninterpreted function with name `id` and sort `s`. -/
def declareFun (id : String) (s : Term) : SolverT m Unit := addCommand (.declare id s)

/-- Define a function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFun (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  SolverT m Unit := addCommand (.defineFun id ps s t false)

/-- Define a recursive function with name `id`, parameters `ps`, co-domain `s`,
    and body `t`. -/
def defineFunRec (id : String) (ps : List (String × Term)) (s : Term) (t : Term) :
  SolverT m Unit := addCommand (.defineFun id ps s t true)

/-- Assert that proposition `t` is true. -/
def assert (t : Term) : SolverT m Unit := addCommand (.assert t)

/-- Check if the query given so far is satisfiable and return the result. -/
def checkSat : SolverT m Result := do
  let state ← get

  let mut args : Array String := #[]

  for kind in allKinds do
    args := args.push s!"--{kind.toDefaultPath}"
    args := args.push $ state.args[kind].get!.foldl (fun r s => r ++ " " ++ s) ""

  let proc ← IO.Process.spawn {
    cmd := "mtsolve"
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
  | "sat"     => return (.sat msg)
  | "unsat"   => return (.unsat msg)
  | "unknown" => return (.unknown msg)
  | "timeout" => return (.timeout msg)
  | "except"  => return (.except msg)
  | out => (throw (IO.userError s!"unexpected solver output\nstdout: {res}\nstderr: {msg}") : IO _)

end Smt.Solver
