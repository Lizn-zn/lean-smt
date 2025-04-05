/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Dsl.Sexp
import Smt.Reconstruct
import Smt.Reconstruct.Prop.Lemmas
import Smt.Translate.Query
import Smt.Preprocess
import Smt.Solver
import Smt.Prover
import Smt.Util

namespace Sos

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

def genUniqueFVarNames : MetaM (HashMap FVarId String × HashMap String FVarId) := do
  let lCtx ← getLCtx
  let st : NameSanitizerState := { options := {}}
  let (lCtx, _) := (lCtx.sanitizeNames st).run
  return lCtx.getFVarIds.foldl (init := ({}, {})) fun (m₁, m₂) fvarId =>
    let m₁ := m₁.insert fvarId (lCtx.getRoundtrippingUserName? fvarId).get!.toString
    let m₂ := m₂.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString fvarId
    (m₁, m₂)

def prepareSmtQuery (hs : List Expr) (goalType : Expr) (fvNames : HashMap FVarId String) : MetaM (List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g =>
  Query.generateQuery g hs fvNames

def withProcessedHints (mv : MVarId) (hs : List Expr) (k : MVarId → List Expr → MetaM α): MetaM α :=
  go mv hs [] k
where
  go (mv : MVarId) (hs : List Expr) (fvs : List Expr) (k : MVarId → List Expr → MetaM α): MetaM α := do
    match hs with
    | [] => k mv fvs
    | h :: hs =>
      if h.isFVar || h.isConst then
        go mv hs (h :: fvs) k
      else
        let mv ← mv.assert (← mkFreshId) (← Meta.inferType h) h
        let ⟨fv, mv⟩ ← mv.intro1
        go mv hs (.fvar fv :: fvs) k


namespace Tactic

syntax smtHints := ("[" term,* "]")?
syntax smtTimeout := ("(timeout := " num ")")?
syntax smtSolver := ("(solver := " term,* ")")?

/-- `sos` calls sum-of-squares prover
use `sos [h₁, h₂, ..., hₙ]` to pass hints and solver to the solver
use `sos (solver := schd, tsds)` to pass the solver options
use `sos (timeout := 10)` to pass the timeout to the solver
-/
syntax (name := sos) "sos" smtHints smtTimeout smtSolver : tactic
syntax (name := sos!) "sos!" smtHints smtTimeout smtSolver : tactic


def parseHints : TSyntax `smtHints → TacticM (List Expr)
  | `(smtHints| [ $[$hs],* ]) => hs.toList.mapM (fun h => elabTerm h.raw none)
  | `(smtHints| ) => return []
  | _ => throwUnsupportedSyntax

def parseTimeout : TSyntax `smtTimeout → TacticM (Option Nat)
  | `(smtTimeout| (timeout := $n)) => return some n.getNat
  | `(smtTimeout| ) => return some 5
  | _ => throwUnsupportedSyntax

def parseSolver : TSyntax `smtSolver → TacticM (List SOSKind)
  | `(smtSolver| (solver := $[$hs],*)) =>
      hs.toList.mapM (fun h =>
        match h.raw.getId.getString! with
        | "schd"    => return SOSKind.schd
        | "tsds"    => return SOSKind.tsds
        | msg => throwError s!"Invalid solver name {msg}")
  | `(smtSolver| ) => return [SOSKind.schd, SOSKind.tsds]
  | _ => throwUnsupportedSyntax

axiom SMT_VERIF (P : Prop) : P

/-
  Close the current goal using the above axiom.
  It is crucial to ensure that this is only invoked when an `unsat` result is returned
-/
def closeWithAxiom : TacticM Unit := do
  let _ ← evalTactic (← `(tactic| apply SMT_VERIF))
  return ()

def withProcessedHintsOnly (hs : List Expr) (k : List Expr → TacticM α): TacticM α :=
  withProcessHints' hs [] k
where
  withProcessHints' (hs : List Expr) (fvs : List Expr) (k : List Expr → TacticM α): TacticM α := do
    match hs with
    | [] => k fvs
    | h :: hs =>
      if h.isFVar || h.isConst then
        withProcessHints' hs (h :: fvs) k
      else
        let mv ← Tactic.getMainGoal
        let mv ← mv.assert (← mkFreshId) (← Meta.inferType h) h
        let ⟨fv, mv⟩ ← mv.intro1
        Tactic.replaceMainGoal [mv]
        withMainContext (withProcessHints' hs (.fvar fv :: fvs) k)

@[tactic sos] def evalSos : Tactic := fun stx => withMainContext do
  let g ← Meta.mkFreshExprMVar (← getMainTarget)
  let mv := g.mvarId!
  let goalType ← mv.getType
  -- 1. Get the hints and solvers and timeout passed to the tactic.
  let mut hs ← parseHints ⟨stx[1]⟩
  hs := hs.eraseDups
  let mut timeout ← parseTimeout ⟨stx[2]⟩
  let mut solvers ← parseSolver ⟨stx[3]⟩
  withProcessedHintsOnly hs fun hs => do
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs (← mv.getType) (← genUniqueFVarNames).fst
  let cmds := cmds ++ [.checkSat]
  let cmds := cmds ++ [.getModel]
  let query := Prover.addCommands cmds *> Prover.checkSat
  logInfo m!"goal: {goalType}"
  logInfo m!"query:\n{Command.cmdsAsQuery cmds}"
  -- 3. Run the solver.
  let ss ← Prover.create timeout.get! solvers
  let res ← StateT.run' query ss
  -- 4. Print the result.
  logInfo m!"result: {res}"
  match res with
  | .except msg => throwError s!"solver failed: {msg}"
  | .timeout _ => throwError "the solver timed out"
  | .unsat _ => closeWithAxiom

def getLocalHypotheses : MetaM (List Expr) := do
  let ctx ← getLCtx
  let mut hs := #[]
  for localDecl in ctx do
    if localDecl.isImplementationDetail then
      continue
    let e ← instantiateMVars localDecl.toExpr
    let et ← Meta.inferType e >>= instantiateMVars
    if (← Meta.isProp et) then
      hs := hs.push localDecl.toExpr
  return hs.toList.eraseDups

@[tactic sos!] def evalSos! : Tactic := fun stx => withMainContext do
  -- 1. Get the hints passed to the tactic.
  let hs ← getLocalHypotheses
  let g ← Meta.mkFreshExprMVar (← getMainTarget)
  let mv := g.mvarId!
  let goalType ← Tactic.getMainTarget
  let timeout ← parseTimeout ⟨stx[2]⟩
  let solvers ← parseSolver ⟨stx[3]⟩
  withProcessedHintsOnly hs fun hs => do
    -- 2. Generate the SMT query.
    let cmds ← prepareSmtQuery hs (← mv.getType) (← genUniqueFVarNames).fst
    let cmds := cmds ++ [.checkSat]
    let cmds := cmds ++ [.getModel]
    let query := Prover.addCommands cmds *> Prover.checkSat
    logInfo m!"goal: {goalType}"
    logInfo m!"query:\n{Command.cmdsAsQuery cmds}"
    -- 3. Run the solver.
    let ss ← Prover.create timeout.get! solvers
    let res ← StateT.run' query ss
    -- 4. Print the result.
    logInfo m!"result: {res}"
    match res with
    | .except msg => throwError s!"solver failed: {msg}"
    | .timeout msg => throwError s!"solver timed out: {msg}"
    | .unsat _ => closeWithAxiom


end Sos.Tactic
