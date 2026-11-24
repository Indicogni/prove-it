/-
  Tools/Check.lean (`lake exe check`)
  Learner Progress & Proof-Completion CLI for ProveIt!

  Supports:
    lake exe check               -- Audit learner progress across all chapters, checkpoints & capstones
    lake exe check list          -- List all curriculum units and their file paths
    lake exe check ch01..ch16    -- Check specific chapter(s)
    lake exe check cp1..cp4      -- Check closed-notes checkpoint(s)
    lake exe check capstones     -- Check all 4 production capstones (or `cedar-lite`, `fencing-kv`, `stack-vm`, `verigate`)
    lake exe check --solutions   -- Verify zero-`sorry` model answers under `Solutions/`
-/
import Lean

set_option autoImplicit false

namespace Tools.Check

inductive UnitCategory where
  | chapter
  | checkpoint
  | capstone
  deriving Repr, DecidableEq

structure CurriculumUnit where
  id : String
  aliases : List String
  category : UnitCategory
  title : String
  relPath : String
  deriving Repr

def allUnits : List CurriculumUnit := [
  -- Part I–IV Chapters (Ch01–Ch16)
  { id := "ch01", aliases := ["ch1", "1"], category := .chapter,
    title := "Ch 01 — The Silent Truncation Bug", relPath := "Ch01.lean" },
  { id := "ch02", aliases := ["ch2", "2"], category := .chapter,
    title := "Ch 02 — Illegal States & Domain Modeling", relPath := "Ch02.lean" },
  { id := "ch03", aliases := ["ch3", "3"], category := .chapter,
    title := "Ch 03 — Compile-Time Exhaustion & Boolean Reflection", relPath := "Ch03.lean" },
  { id := "ch04", aliases := ["ch4", "4"], category := .chapter,
    title := "Ch 04 — Gear 1: A TLA+ Model Checker in 35 Lines", relPath := "Ch04.lean" },
  { id := "ch05", aliases := ["ch5", "5"], category := .chapter,
    title := "Ch 05 — Proofs Are Programs, Goals Are Stack Traces", relPath := "Ch05.lean" },
  { id := "ch06", aliases := ["ch6", "6"], category := .chapter,
    title := "Ch 06 — Control Flow, Rewriting & Linear Arithmetic", relPath := "Ch06.lean" },
  { id := "ch07", aliases := ["ch7", "7"], category := .chapter,
    title := "Ch 07 — Unprovable on Purpose", relPath := "Ch07.lean" },
  { id := "ch08", aliases := ["ch8", "8"], category := .chapter,
    title := "Ch 08 — Gear 2: Inductive Invariants & Strengthening", relPath := "Ch08.lean" },
  { id := "ch09", aliases := ["ch9", "9"], category := .chapter,
    title := "Ch 09 — Packing Proofs into Types", relPath := "Ch09.lean" },
  { id := "ch10", aliases := ["10"], category := .chapter,
    title := "Ch 10 — 64-Bit Hardware Truth (`UInt64` & `BitVec`)", relPath := "Ch10.lean" },
  { id := "ch11", aliases := ["11"], category := .chapter,
    title := "Ch 11 — Pure Effects & Termination as DoS Defense", relPath := "Ch11.lean" },
  { id := "ch12", aliases := ["12"], category := .chapter,
    title := "Ch 12 — Refinement Mappings & Stuttering Steps", relPath := "Ch12.lean" },
  { id := "ch13", aliases := ["13"], category := .chapter,
    title := "Ch 13 — How AI Cheats Formal Verification", relPath := "Ch13.lean" },
  { id := "ch14", aliases := ["14"], category := .chapter,
    title := "Ch 14 — Spec-First Agentic Co-Design", relPath := "Ch14.lean" },
  { id := "ch15", aliases := ["15"], category := .chapter,
    title := "Ch 15 — Verified Wire Formats", relPath := "Ch15.lean" },
  { id := "ch16", aliases := ["16"], category := .chapter,
    title := "Ch 16 — Monday-Morning Transfer", relPath := "Ch16.lean" },

  -- Closed-Notes Checkpoints (Cp1–Cp4)
  { id := "cp1", aliases := ["cp01", "checkpoint1"], category := .checkpoint,
    title := "Checkpoint 1 — Zero-Panic Rollout & Canary Router", relPath := "Checkpoints/Cp1.lean" },
  { id := "cp2", aliases := ["cp02", "checkpoint2"], category := .checkpoint,
    title := "Checkpoint 2 — Crash-Safe Idempotent Write-Ahead Ledger", relPath := "Checkpoints/Cp2.lean" },
  { id := "cp3", aliases := ["cp03", "checkpoint3"], category := .checkpoint,
    title := "Checkpoint 3 — Verified Fixed-Capacity Ring Buffer", relPath := "Checkpoints/Cp3.lean" },
  { id := "cp4", aliases := ["cp04", "checkpoint4"], category := .checkpoint,
    title := "Checkpoint 4 — Red-Team & Repair AI Batch Escrow", relPath := "Checkpoints/Cp4.lean" },

  -- Production Capstones
  { id := "cedar-lite", aliases := ["cedar", "cap1", "capstone1"], category := .capstone,
    title := "Capstone 1 — CedarLite Cloud Authorization Engine", relPath := "Capstones/CedarLite.lean" },
  { id := "fencing-kv", aliases := ["fencing", "kv", "cap2", "capstone2"], category := .capstone,
    title := "Capstone 2 — FencingKV Distributed Lease & Tombstone Store", relPath := "Capstones/FencingKV.lean" },
  { id := "stack-vm", aliases := ["stackvm", "vm", "cap3", "capstone3"], category := .capstone,
    title := "Capstone 3 — StackVM Optimizing Compiler & Bytecode VM", relPath := "Capstones/StackVM.lean" },
  { id := "verigate", aliases := ["verigate-lab", "cap4", "capstone4"], category := .capstone,
    title := "Capstone 4 — VeriGateLab Multi-Tenant Quota & Settlement", relPath := "Capstones/VeriGateLab.lean" }
]

def CurriculumUnit.filePath (u : CurriculumUnit) (useSolutions : Bool) : System.FilePath :=
  let root := if useSolutions then "Solutions" else "ProveIt"
  System.FilePath.mk s!"{root}/{u.relPath}"

def dropLastChars (s : String) (k : Nat) : String :=
  let cs := s.toList
  String.ofList (cs.take (cs.length - k))

def pathToModuleName (path : System.FilePath) : Lean.Name := Id.run do
  let norm := path.toString.replace "\\" "/"
  let withoutExt := if norm.endsWith ".lean" then dropLastChars norm 5 else norm
  let parts := (withoutExt.splitOn "/").filter (fun s => !s.isEmpty && s != ".")
  let mut acc := Lean.Name.anonymous
  for p in parts do
    acc := Lean.Name.str acc p
  return acc

def findLeanBinary : IO String := do
  let probe ← IO.Process.output { cmd := "which", args := #["lean"] }
  if probe.exitCode == 0 && !probe.stdout.trimAscii.isEmpty then
    return probe.stdout.trimAscii.toString
  else
    match ← IO.getEnv "HOME" with
    | some home => return s!"{home}/.elan/bin/lean"
    | none => return "lean"

def getEffectiveSearchPath : IO Lean.SearchPath := do
  let envPath := System.SearchPath.parse ((← IO.getEnv "LEAN_PATH").getD "")
  let lakeLib : System.FilePath := ".lake/build/lib/lean"
  if ← lakeLib.pathExists then
    return lakeLib :: envPath
  else
    return envPath

inductive UnitStatus where
  | proven (totalThms : Nat)
  | inProgress (totalThms : Nat) (sorryNames : List String)
  | missing
  | compileError (msg : String)
  deriving Repr

/-- Inspect a curriculum file's kernel declarations to count theorems and `sorryAx` holes. -/
def checkUnitFile (filePath : System.FilePath) : IO UnitStatus := do
  if !(← filePath.pathExists) then
    return .missing
  let leanBin ← findLeanBinary
  let sysroot ← Lean.findSysroot leanBin
  let baseSp ← getEffectiveSearchPath
  let modName := pathToModuleName filePath
  Lean.initSearchPath sysroot baseSp

  let existingOlean? ← baseSp.findWithExt "olean" modName
  let mut usePrebuilt := false
  if let some oleanPath := existingOlean? then
    if ← oleanPath.pathExists then
      let srcMeta ← filePath.metadata
      let oleanMeta ← oleanPath.metadata
      if oleanMeta.modified >= srcMeta.modified then
        usePrebuilt := true

  let inspectMod (env : Lean.Environment) (modData : Lean.ModuleData) : IO UnitStatus := do
    let mut thmCount : Nat := 0
    let mut sorryDecls : List String := []
    for cinfo in modData.constants do
      let name := cinfo.name
      if !name.isInternalDetail then
        let isThmOrDef :=
          match cinfo with
          | .thmInfo _ => true
          | .defnInfo _ => true
          | _ => false
        if cinfo matches .thmInfo _ then
          thmCount := thmCount + 1
        if isThmOrDef then
          let (axs, _) ← Lean.Core.CoreM.toIO (Lean.collectAxioms name)
            { fileName := filePath.toString, fileMap := default }
            { env := env }
          if axs.contains ``sorryAx then
            sorryDecls := name.toString :: sorryDecls
    let holes := sorryDecls.reverse.eraseDups
    if holes.isEmpty then
      return .proven thmCount
    else
      return .inProgress thmCount holes

  if usePrebuilt then
    try
      let env ← Lean.importModules #[{ module := modName }] {} 0 #[] false false
      match env.allImportedModuleNames.idxOf? modName with
      | none => return .compileError s!"module `{modName}` missing from imported headers"
      | some idx =>
        if h : idx < env.header.moduleData.size then
          inspectMod env env.header.moduleData[idx]
        else
          return .compileError "moduleData index out of bounds"
    catch e =>
      return .compileError s!"{e}"
  else
    IO.FS.withTempDir fun tmpDir => do
      let tempMod := Lean.Name.str .anonymous s!"CheckUnit_{modName.toString.replace "." "_"}"
      let outOlean := tmpDir / s!"{tempMod}.olean"
      let envPathStr := String.intercalate ":" (baseSp.map (·.toString))
      let proc ← IO.Process.output {
        cmd := leanBin
        args := #["-o", outOlean.toString, filePath.toString]
        env := #[("LEAN_PATH", some envPathStr)]
      }
      if proc.exitCode != 0 then
        return .compileError (proc.stderr.trimAscii.toString ++ proc.stdout.trimAscii.toString)
      let activeSp := tmpDir :: baseSp
      Lean.initSearchPath sysroot activeSp
      try
        let env ← Lean.importModules #[{ module := tempMod }] {} 0 #[] false false
        match env.allImportedModuleNames.idxOf? tempMod with
        | none => return .compileError "compiled module missing from imported headers"
        | some idx =>
          if h : idx < env.header.moduleData.size then
            inspectMod env env.header.moduleData[idx]
          else
            return .compileError "moduleData index out of bounds"
      catch e =>
        return .compileError s!"{e}"

def resolveSelector (sel : String) : List CurriculumUnit :=
  let key := sel.trimAscii.toString.toLower
  if key == "all" then allUnits
  else if key == "chapters" then allUnits.filter (·.category == .chapter)
  else if key == "checkpoints" then allUnits.filter (·.category == .checkpoint)
  else if key == "capstones" then allUnits.filter (·.category == .capstone)
  else
    allUnits.filter fun u => u.id == key || u.aliases.contains key

def printList : IO UInt32 := do
  IO.println "================================================================================"
  IO.println "  ProveIt! Curriculum Units (`lake exe check <unit> [--solutions]`)"
  IO.println "================================================================================"
  for u in allUnits do
    let padId := u.id ++ String.ofList (List.replicate (12 - min 12 u.id.length) ' ')
    IO.println s!"  {padId}  {u.title}"
    IO.println s!"                starter:  ProveIt/{u.relPath}  |  solution: Solutions/{u.relPath}"
  return 0

def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  lake exe check                        Check progress across all units"
  IO.println "  lake exe check list                   List all unit IDs and file paths"
  IO.println "  lake exe check ch01..ch16             Check specific chapter(s)"
  IO.println "  lake exe check cp1..cp4               Check closed-notes checkpoint(s)"
  IO.println "  lake exe check capstones              Check all 4 capstones (`cedar-lite`, `fencing-kv`, `stack-vm`, `verigate`)"
  IO.println "  lake exe check [unit...] --solutions  Verify zero-`sorry` model solutions"

end Tools.Check

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    Tools.Check.printUsage
    return 0
  if args == ["list"] then
    return (← Tools.Check.printList)

  let useSolutions := args.contains "--solutions"
  let rawSelectors := args.filter (fun a => a != "--solutions")

  let mut selected : List Tools.Check.CurriculumUnit := []
  if rawSelectors.isEmpty then
    selected := Tools.Check.allUnits
  else
    for sel in rawSelectors do
      let matched := Tools.Check.resolveSelector sel
      if matched.isEmpty then
        IO.eprintln s!"Error: unknown unit selector `{sel}`. Run `lake exe check list` to view IDs."
        return 2
      selected := selected ++ matched

  let targetLabel := if useSolutions then "Model Solutions (`Solutions/`)" else "Learner Starters (`ProveIt/`)"
  IO.println "========================================================================"
  IO.println s!"  ProveIt! Verification Check — {targetLabel}"
  IO.println "========================================================================"

  let verboseSingle := selected.length <= 4
  let mut provenUnits : Nat := 0
  let mut totalHoles : Nat := 0
  let mut anyMissingOrError := false

  for u in selected do
    let path := u.filePath useSolutions
    let st ← Tools.Check.checkUnitFile path
    match st with
    | .proven thms =>
        provenUnits := provenUnits + 1
        IO.println s!"  [PROVEN]      {u.title} ({thms} theorems verified, 0 sorry)"
    | .inProgress thms holes =>
        totalHoles := totalHoles + holes.length
        IO.println s!"  [IN PROGRESS] {u.title} ({holes.length} sorry remaining, {thms} theorems total)"
        if verboseSingle || useSolutions then
          for h in holes do
            IO.println s!"                  • `{h}` still uses `sorry`"
    | .missing =>
        anyMissingOrError := true
        IO.println s!"  [MISSING]     {u.title} (`{path}` not found)"
    | .compileError msg =>
        anyMissingOrError := true
        IO.println s!"  [ERROR]       {u.title} (`{path}` failed to compile)"
        IO.println s!"                  {msg}"

  IO.println "------------------------------------------------------------------------"
  IO.println s!"  Summary: {provenUnits} / {selected.length} units completely proven | {totalHoles} `sorry` holes remaining."

  if !anyMissingOrError && provenUnits == selected.length then
    return 0
  else
    return 1
