module
public meta import Lean.Replay
-- PROJECT_IMPORTS are generated from the current source inventory by verify.py.

set_option maxHeartbeats 0
open Lean Elab Command

structure AuditClosure where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  deriving Inhabited

/-- Read actual declaration bodies, without the precomputed axiom extension. -/
partial def auditClosure (env : Environment) (n : Name) : StateM AuditClosure Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  let some ci := env.find? n | do
    modify fun s => { s with missing := s.missing.insert n }
    return
  if ci.isAxiom then modify fun s => { s with axioms := s.axioms.insert n }
  if let .quotInfo _ := ci then auditClosure env ``Eq
  ci.type.getUsedConstants.forM (auditClosure env)
  if let some value := ci.value? true then value.getUsedConstants.forM (auditClosure env)
  if let .inductInfo i := ci then
    i.all.forM (auditClosure env)
    i.ctors.forM (auditClosure env)

run_cmd do
  liftIO enableInitializersExecution
  let moduleText ← IO.FS.readFile "project-modules.txt"
  let projectModules := (moduleText.splitOn "\n").filterMap fun s =>
    if s.isEmpty then none else some s.toName
  let imports := projectModules.toArray.map fun n => ({ module := n } : Import)
  let env ← liftIO <| importModules imports {} (loadExts := true) (level := .private)
  let mut roots : List Name := []
  let mut allRoots : List Name := []
  let mut excluded : Array String := #[]
  let mut seenModules : List Name := []
  let mut inventory : Array String := #[]
  let mut theoremCount : Nat := 0
  let mut duplicateLines : Array String := #[]
  for i in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    if projectModules.contains moduleName then
      seenModules := moduleName :: seenModules
      for name in env.header.moduleData[i]!.constNames, localInfo in env.header.moduleData[i]!.constants do
        let some ci := env.find? name | throwError "Missing project declaration {name}"
        unless ci.type == localInfo.type && ci.value? true == localInfo.value? true &&
            ci.levelParams == localInfo.levelParams && ci.isUnsafe == localInfo.isUnsafe &&
            ci.isPartial == localInfo.isPartial do
          throwError "Loaded declaration differs from module's declaration: {moduleName}.{name}"
        if allRoots.contains name then
          duplicateLines := duplicateLines.push s!"{moduleName}|{name}|identical type, body and universe parameters"
          continue
        allRoots := name :: allRoots
        if ci.isUnsafe || ci.isPartial then
          excluded := excluded.push s!"{moduleName}|{name}|unsafe={ci.isUnsafe}|partial={ci.isPartial}|compiler auxiliary; must not occur in any safe root's logical closure"
        else
          roots := name :: roots
        if ci.isTheorem then theoremCount := theoremCount + 1
        let axioms ← withEnv env <| Lean.collectAxioms name
        inventory := inventory.push (s!"{moduleName}|{name}|theorem={ci.isTheorem}|" ++
          String.intercalate "," (axioms.toList.map Name.toString))
  for moduleName in projectModules do
    unless seenModules.contains moduleName do throwError "Missing project module {moduleName}"
  if roots.isEmpty then throwError "Empty root set"
  IO.FS.writeFile "declaration-inventory.txt"
    (String.intercalate "\n" inventory.toList ++ "\n")
  IO.FS.writeFile "duplicate-declaration-origins.txt"
    (String.intercalate "\n" duplicateLines.toList ++ "\n")
  IO.FS.writeFile "compiler-auxiliary-exclusions.txt"
    (String.intercalate "\n" excluded.toList ++ "\n")
  logInfo m!"DUPLICATE MODULE OCCURRENCES {duplicateLines.size}; all exact matches"
  logInfo m!"PROJECT INVENTORY {seenModules.length} modules; {allRoots.length} declarations; {theoremCount} theorems"
  logInfo m!"LOGICAL ROOTS {roots.length}; excluded compiler auxiliaries {excluded.size}"
  let finalRoots := roots.eraseDups
  let (_, s) := (finalRoots.forM (auditClosure env)).run {}
  let finalName := `MathCollab.Density.Stronger.stronger_density_bound_native
  let (_, finalState) := (auditClosure env finalName).run {}
  IO.FS.writeFile "final-theorem-dependencies.txt"
    (String.intercalate "\n" ((finalState.seen.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  for required in [`MathCollab.Density.Stronger.stronger_density_bound_native,
      `MathCollab.Density.Stronger.zeta_twelfth_physical_native,
      `MathCollab.Density.Stronger.PointMean.pointMeanInput_native,
      `MathCollab.Density.Stronger.Atkinson.localMeanStationaryInput_native] do
    unless finalState.seen.contains required do throwError "Native bridge absent: {required}"
  unless s.missing.isEmpty do throwError "Missing declarations: {s.missing.toArray}"
  for ax in s.axioms.toArray do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Disallowed axiom: {ax}"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in s.seen.toArray do
    let some ci := env.find? name | throwError "Missing declaration: {name}"
    if ci.isUnsafe || ci.isPartial then
      throwError "Unsafe or partial declaration in replay closure: {name}"
    constants := constants.insert name ci
  IO.FS.writeFile "proof-dependencies.txt"
    (String.intercalate "\n" ((s.seen.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  IO.FS.writeFile "replay-roots.txt"
    (String.intercalate "\n" ((finalRoots.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"REPLAY INPUT: {constants.size} declarations for {finalRoots.length} runtime-enumerated safe production roots"
  let empty ← mkEmptyEnvironment
  let replayed ← empty.toKernelEnv.replay constants
  for root in finalRoots do
    unless (replayed.find? root).isSome do throwError "Missing replayed root: {root}"
  let receipt := Json.mkObj [
    ("status", toJson "passed"),
    ("scope", toJson "all runtime-enumerated safe production declarations"),
    ("production_modules", toJson seenModules.length),
    ("production_declarations", toJson allRoots.length),
    ("production_theorems", toJson theoremCount),
    ("duplicate_occurrences", toJson duplicateLines.size),
    ("excluded_compiler_auxiliaries", toJson excluded.size),
    ("replay_roots", toJson finalRoots.length),
    ("replayed_declarations", toJson constants.size),
    ("final_density_closure", toJson finalState.seen.toArray.size),
    ("axioms", toJson ((s.axioms.toArray.qsort Name.lt).map Name.toString)),
    ("all_roots_present_after_replay", toJson true)]
  IO.FS.writeFile "audit-receipt.json" (receipt.pretty ++ "\n")
  logInfo m!"RUNTIME PRODUCTION REPLAY PASS: {constants.size} declarations, {finalRoots.length} roots"
