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
import Smt.Util

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

def genUniqueFVarNames : MetaM (Std.HashMap FVarId String × Std.HashMap String FVarId) := do
  let lCtx ← getLCtx
  let st : NameSanitizerState := { options := {}}
  let (lCtx, _) := (lCtx.sanitizeNames st).run
  return lCtx.getFVarIds.foldl (init := ({}, {})) fun (m₁, m₂) fvarId =>
    let m₁ := m₁.insert fvarId (lCtx.getRoundtrippingUserName? fvarId).get!.toString
    let m₂ := m₂.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString fvarId
    (m₁, m₂)

def prepareSmtQuery (hs : List Expr) (goalType : Expr) (fvNames : Std.HashMap FVarId String) : MetaM (List Command) := do
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

def smt (mv : MVarId) (hs : List Expr) (timeout : Option Nat := none) : MetaM (List MVarId) := mv.withContext do
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv hs fun mv hs => mv.withContext do
  let (hs, mv) ← Preprocess.elimIff mv hs
  mv.withContext do
  let goalType : Q(Prop) ← mv.getType
  -- 2. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  let cmds ← prepareSmtQuery hs (← mv.getType) fvNames₁
  let cmds := .setLogic "ALL" :: cmds
  trace[smt] "goal: {goalType}"
  trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- 3. Run the solver.
  let res ← solve (Command.cmdsAsQuery cmds) timeout
  -- 4. Print the result.
  -- trace[smt] "\nresult: {res}"
  match res with
  | .error e =>
    -- 4a. Print error reason.
    trace[smt] "\nerror reason:\n{repr e}\n"
    throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
  | .ok pf =>
    -- 4b. Reconstruct proof.
    let (p, hp, mvs) ← reconstructProof pf fvNames₂
    let mv ← mv.assert (← mkFreshId) p hp
    let ⟨_, mv⟩ ← mv.intro1
    let ts ← hs.mapM Meta.inferType
    let mut gs ← mv.apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ts q(Prop), goalType])
    mv.withContext (gs.forM (·.assumption))
    return mvs

namespace Tactic

syntax smtHints := ("[" term,* "]")?
syntax smtTimeout := ("(" "timeout" " := " num ")")?
syntax smtSolver := ("(" "solvers" " := " term,* ")")?

/-- `smt` converts the current goal into an SMT query and checks if it is
satisfiable. By default, `smt` generates the minimum valid SMT query needed to
assert the current goal. However, that is not always enough:
```lean
def modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt
```
For the theorem above, `smt` generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(check-sat)
```
which is missing the hypotheses `hp` and `hpq` required to prove the theorem. To
pass hypotheses to the solver, use `smt [h₁, h₂, ..., hₙ]` syntax:
```lean
def modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
```
The tactic then generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(declare-const p Bool)
(assert p)
(assert (=> p q))
(check-sat)
```
-/
syntax (name := smt) "smt" smtHints smtTimeout smtSolver : tactic

/-- `smt_decide` calls smt solver but does NOT try to reconstruct the proof
use `smt_decide [h₁, h₂, ..., hₙ]` to pass hints and solver to the solver
use `smt_decide (solvers := cvc5, z3, sysol, syopt, mplrc, mplbt, mmard, mmafi)` to pass the solver options
use `smt_decide (timeout := 10)` to pass the timeout to the solver
-/
syntax (name := smt_decide) "smt_decide" smtHints smtTimeout smtSolver : tactic
syntax (name := smt_decide!) "smt_decide!" smtHints smtTimeout smtSolver : tactic

/-- Like `smt`, but just shows the query without invoking a solver. -/
syntax (name := smtShow) "smt_show" smtHints : tactic

def parseHints : TSyntax `smtHints → TacticM (List Expr)
  | `(smtHints| [ $[$hs],* ]) => hs.toList.mapM (fun h => elabTerm h.raw none)
  | `(smtHints| ) => return []
  | _ => throwUnsupportedSyntax

def parseTimeout : TSyntax `smtTimeout → TacticM (Option Nat)
  | `(smtTimeout| (timeout := $n)) => return some n.getNat
  | `(smtTimeout| ) => return some 5
  | _ => throwUnsupportedSyntax

def parseSolver : TSyntax `smtSolver → TacticM (List Kind)
  | `(smtSolver| (solvers := $[$hs],*)) =>
      hs.toList.mapM (fun h =>
        match h.raw.getId.getString! with
        | "cvc5"    => return Kind.cvc5
        | "z3"      => return Kind.z3
        | "mplbt"   => return Kind.mplbt
        | "mplrc"   => return Kind.mplrc
        | "sysol"   => return Kind.sysol
        | "syopt"   => return Kind.syopt
        | "mmard"   => return Kind.mmard
        | "mmafi"   => return Kind.mmafi
        | msg => throwError s!"Invalid solver name {msg}")
  | `(smtSolver| ) => return [Kind.cvc5, Kind.z3, Kind.mplrc, Kind.mplbt, Kind.mmard, Kind.mmafi]
  | _ => throwUnsupportedSyntax

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  let mvs ← Smt.smt (← Tactic.getMainGoal) (← parseHints ⟨stx[1]⟩) (← parseTimeout ⟨stx[2]⟩)
  Tactic.replaceMainGoal mvs

@[tactic smtShow] def evalSmtShow : Tactic := fun stx => withMainContext do
  let g ← Meta.mkFreshExprMVar (← getMainTarget)
  let mv := g.mvarId!
  let hs ← parseHints ⟨stx[1]⟩
  withProcessedHints mv hs fun mv hs => mv.withContext do
  let (hs, mv) ← Preprocess.elimIff mv hs
  mv.withContext do
  let goalType ← mv.getType
  let cmds ← prepareSmtQuery hs (← mv.getType) (← genUniqueFVarNames).fst
  let cmds := cmds ++ [.checkSat]
  logInfo m!"goal: {goalType}\n\nquery:\n{Command.cmdsAsQuery cmds}"


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

@[tactic smt_decide] def evalSmtDecide : Tactic := fun stx => withMainContext do
  let g ← Meta.mkFreshExprMVar (← getMainTarget)
  let mv := g.mvarId!
  let goalType ← mv.getType
  -- 1. Get the hints and solvers and timeout passed to the tactic.
  let mut hs ← parseHints ⟨stx[1]⟩
  hs := hs.eraseDups
  let mut timelimit ← parseTimeout ⟨stx[2]⟩
  let mut solverlist ← parseSolver ⟨stx[3]⟩
  withProcessedHintsOnly hs fun hs => do
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs (← mv.getType) (← genUniqueFVarNames).fst
  let cmds := cmds ++ [.checkSat]
  let cmds := cmds ++ [.getModel]
  let query := Solver.addCommands cmds *> Solver.checkSat
  logInfo m!"goal: {goalType}"
  logInfo m!"query:\n{Command.cmdsAsQuery cmds}"
  -- 3. Run the solver.
  let ss ← Solver.create timelimit.get! solverlist
  let res ← StateT.run' query ss
  -- 4. Print the result.
  logInfo m!"result: {res}"
  match res with
  | .sat msg =>
    -- 4a. Print model.
    throwError s!"counter example exists: {msg}"
  | .unknown msg => throwError s!"unable to prove goal {msg}"
  | .except msg => throwError s!"solver exceptions {msg}"
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

@[tactic smt_decide!] def evalSmtDecide! : Tactic := fun stx => withMainContext do
  -- 1. Get the hints passed to the tactic.
  let hs ← getLocalHypotheses
  let g ← Meta.mkFreshExprMVar (← getMainTarget)
  let mv := g.mvarId!
  let goalType ← Tactic.getMainTarget
  let timelimit ← parseTimeout ⟨stx[2]⟩
  let solverlist ← parseSolver ⟨stx[3]⟩
  withProcessedHintsOnly hs fun hs => do
    -- 2. Generate the SMT query.
    let cmds ← prepareSmtQuery hs (← mv.getType) (← genUniqueFVarNames).fst
    let cmds := cmds ++ [.checkSat]
    let cmds := cmds ++ [.getModel]
    let query := Solver.addCommands cmds *> Solver.checkSat
    logInfo m!"goal: {goalType}"
    logInfo m!"query:\n{Command.cmdsAsQuery cmds}"
    -- 3. Run the solver.
    let ss ← Solver.create timelimit.get! solverlist
    let res ← StateT.run' query ss
    -- 4. Print the result.
    logInfo m!"result: {res}"
    match res with
    | .sat msg =>
      -- 4a. Print model.
      throwError s!"counter example exists: {msg}"
    | .unknown msg => throwError s!"unable to prove goal {msg}"
    | .except msg => throwError s!"solver exceptions {msg}"
    | .timeout _ => throwError "the solver timed out"
    | .unsat _ => closeWithAxiom

end Smt.Tactic
