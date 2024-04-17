/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

import Smt.Dsl.Sexp
import Smt.Query
-- import Smt.Reconstruction.Certifying
import Mathlib.Lean.Expr
import Smt.Solver
import Smt.Util

namespace Smt

open Lean Meta Elab Tactic
open Smt Query Solver

initialize
  registerTraceClass `smt.debug
  registerTraceClass `smt.debug.attr
  registerTraceClass `smt.debug.reconstruct
  registerTraceClass `smt.debug.translate.query
  registerTraceClass `smt.debug.translate.expr

syntax smtHints := ("[" term,* "]")?
syntax smtTimeout := ("(timeout := " num ")")?

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
syntax (name := smt) "smt" smtHints smtTimeout : tactic

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

def withProcessedHints (hs : List Expr) (k : List Expr → TacticM α): TacticM α :=
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

def prepareSmtQuery (hs : List Expr) : TacticM (List Command) := do
  let goalType ← Tactic.getMainTarget
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g =>
  Query.generateQuery g hs

def elabProof (text : String) : TacticM Name := do
  let name ← mkFreshId
  let name := Name.str name.getPrefix ("th0" ++ name.getString)
  let text := text.replace "th0" s!"{name}"
  let (env, log) ← process text (← getEnv) .empty "<proof>"
  _ ← modifyEnv (fun _ => env)
  for m in log.msgs do
    trace[smt.debug.reconstruct] (← m.toString)
  if log.hasErrors then
    throwError "encountered errors elaborating cvc5 proof"
  return name

def evalAnyGoals (tactic : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tactic
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch _ =>
        mvarIdsNew := mvarIdsNew.push mvarId
  setGoals mvarIdsNew.toList

private def addDeclToUnfoldOrTheorem (thms : Meta.SimpTheorems) (e : Expr) : MetaM Meta.SimpTheorems := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← Meta.isProp info.type) then
      thms.addConst declName
    else
      thms.addDeclToUnfold declName
  else
    thms.add (.fvar e.fvarId!) #[] e

axiom SMT_VERIF (P : Prop) : P

/-
  Close the current goal using the above axiom.
  It is crucial to ensure that this is only invoked when an `unsat` result is returned
-/
def closeWithAxiom : TacticM Unit := do
  let _ ← evalTactic (← `(tactic| apply SMT_VERIF))

@[tactic smt] def evalSmt : Tactic := fun stx => withMainContext do
  let goalType ← Tactic.getMainTarget
  -- 1. Get the hints passed to the tactic.
  let mut hs ← parseHints ⟨stx[1]⟩
  hs := hs.eraseDups
  withProcessedHints hs fun hs => do
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs
  let cmds := .checkSat :: cmds
  let cmds := .getModel :: cmds
  let query := addCommands cmds.reverse *> checkSat
  logInfo m!"goal: {goalType}"
  logInfo m!"query:\n{Command.cmdsAsQuery cmds}"
  -- 3. Run the solver.
  let timeout ← parseTimeout ⟨stx[2]⟩
  let ss ← create timeout.get!
  let res ← StateT.run' query ss
  -- 4. Print the result.
  logInfo m!"result: {res}"
  match res with
  | .sat msg =>
    -- 4a. Print model.
    throwError s!"counter example exists: {msg}"
  | .unknown msg => throwError s!"unable to prove goal {msg}"
  | .timeout _ => throwError "the solver timed out"
  | .unsat _ => closeWithAxiom
  /-
  try
    -- 4b. Reconstruct proof.
    let (.expr [.atom "proof", .atom nnp], _) ← StateT.run getProof ss
      | throwError "encountered error parsing cvc5 proof"
    let nnp := skipImports (unquote nnp)
    trace[smt.debug.reconstruct] "proof:\n{nnp}"
    let name ← elabProof nnp
    rconsProof name hs
  catch e =>
    logInfo m!"failed to reconstruct proof: {e.toMessageData}"
  -/
/-
where
  unquote s := s.extract ⟨1⟩ (s.endPos - ⟨1⟩)
  skipImports (s : String) := Id.run do
    let mut s := s
    while s.startsWith "import" do
      s := s.dropWhile (· != '\n')
      s := s.drop 1
    return s
-/

@[tactic smtShow] def evalSmtShow : Tactic := fun stx => withMainContext do
  let goalType ← Tactic.getMainTarget
  let mut hs ← parseHints ⟨stx[1]⟩
  hs := hs.eraseDups
  withProcessedHints hs fun hs => do
  let cmds ← prepareSmtQuery hs
  let cmds := .checkSat :: cmds
  logInfo m!"goal: {goalType}\n\nquery:\n{Command.cmdsAsQuery cmds}"

-- syntax "smt_preprocess" : tactic
-- syntax "smt!" : tactic

-- elab_rules : tactic
--   | `(tactic | smt_preprocess) => smtPreprocess
--   | `(tactic | smt!) => do
--     smtPreprocess
--     smtSolve

end Smt
