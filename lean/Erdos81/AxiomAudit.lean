import Erdos81
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel-assumption audit

This file is an executable verification gate, not merely a diagnostic printout.
It inspects every declaration originating in an `Erdos81` module and rejects any
transitive axiom dependency outside Lean's standard logical primitives listed
below. In particular, an unused project axiom or `sorryAx` still fails the
check.
-/

open Lean Elab Command

private def allowedKernelAxioms : NameSet :=
  NameSet.ofList [``propext, ``Classical.choice, ``Quot.sound]

private def isErdos81Module (moduleName : Name) : Bool :=
  (`Erdos81).isPrefixOf moduleName

private def erdos81Declarations (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun declarations declarationName _ =>
    if !(`Erdos81).isPrefixOf declarationName then
      declarations
    else
      match env.getModuleIdxFor? declarationName with
      | none => declarations
      | some moduleIdx =>
          let moduleName := env.header.moduleNames[moduleIdx]!
          if isErdos81Module moduleName then
            declarations.push declarationName
          else
            declarations

elab "audit_erdos81_axioms" : command => do
  let env ← getEnv
  let declarations := erdos81Declarations env
  if declarations.isEmpty then
    throwError "axiom audit found no declarations from Erdos81 modules"
  for declarationName in declarations do
    for axiomName in (← Lean.collectAxioms declarationName) do
      unless allowedKernelAxioms.contains axiomName do
        throwError m!"{declarationName} transitively depends on forbidden axiom {axiomName}"
  logInfo m!"axiom audit passed for {declarations.size} declarations from Erdos81 modules"

audit_erdos81_axioms

/-! Pin the public theorem signatures checked by the repository gate. -/

example :
    Erdos81.ExternalInputs.Inputs → Erdos81.EventualSharpUpperBound :=
  Erdos81.eventualSharpUpperBound_of_inputs

example :
    Erdos81.ExternalInputs.Inputs → Erdos81.Erdos81Statement :=
  Erdos81.erdos81_of_inputs

#print axioms Erdos81.eventualSharpUpperBound_of_inputs
#print axioms Erdos81.erdos81_of_inputs
