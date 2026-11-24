/-
  Tools/VeriGate.lean (`lake exe verigate`)
  Production Proof-Carrying Code (PCC) & AI Verification Gate

  Audits target `.lean` modules against both source-level invariants (SHA-256 spec lock,
  comment-stripped token hygiene) and the elaborated `Lean.Environment` kernel constants:
  - Tier 0 (`--strict-kernel`, default): allows ONLY `{propext, Quot.sound, Classical.choice}`;
    rejects `sorryAx`, custom `axiom`/`opaque`, `native_decide` / `bv_decide` compiler trust,
    `@[implemented_by]`, `@[extern]`, `@[csimp]`, `unsafe`, `partial`, vacuous `False → ...`
    theorems, spec-lock SHA-256 mismatches, and missing `non_vacuous` witnesses.
  - Tier 1 (`--trust-tier=bv-lrat`): additionally allows `bv_decide` LRAT trust axioms ONLY
    when zero raw `native_decide` tokens or `native_decide` axioms exist.
-/
import Lean

set_option autoImplicit false

namespace Tools.VeriGate

/-! ## 1. Pure RFC 6234 SHA-256 Digest Engine -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

def padSha256 (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let mut out := msg.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0x00
  for i in [0:8] do
    let shift : UInt64 := ((7 - i) * 8).toUInt64
    out := out.push ((bitLen >>> shift).toUInt8)
  return out

def readUInt32BE (bs : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := bs.get! offset |>.toUInt32
  let b1 := bs.get! (offset + 1) |>.toUInt32
  let b2 := bs.get! (offset + 2) |>.toUInt32
  let b3 := bs.get! (offset + 3) |>.toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

def hexChar (nibble : UInt32) : Char :=
  let v := nibble.toNat
  if v < 10 then Char.ofNat ('0'.toNat + v)
  else Char.ofNat ('a'.toNat + (v - 10))

def uint32ToHex (x : UInt32) : String := Id.run do
  let mut chars : List Char := []
  for i in [0:8] do
    let shift : UInt32 := ((7 - i) * 4).toUInt32
    chars := hexChar ((x >>> shift) &&& 0x0f) :: chars
  return String.ofList chars.reverse

def sha256Hex (input : String) : String := Id.run do
  let padded := padSha256 input.toUTF8
  let numBlocks := padded.size / 64
  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19
  for blk in [0:numBlocks] do
    let base := blk * 64
    let mut w := Array.replicate 64 (0 : UInt32)
    for i in [0:16] do
      w := w.set! i (readUInt32BE padded (base + i * 4))
    for i in [16:64] do
      let w15 := w[i - 15]!
      let w2 := w[i - 2]!
      let s0 := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
      let s1 := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    let mut f := h5
    let mut g := h6
    let mut h := h7
    for i in [0:64] do
      let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let temp1 := h + s1 + ch + sha256K[i]! + w[i]!
      let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := s0 + maj
      h := g
      g := f
      f := e
      e := d + temp1
      d := c
      c := b
      b := a
      a := temp1 + temp2
    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e
    h5 := h5 + f
    h6 := h6 + g
    h7 := h7 + h
  return uint32ToHex h0 ++ uint32ToHex h1 ++ uint32ToHex h2 ++ uint32ToHex h3 ++
         uint32ToHex h4 ++ uint32ToHex h5 ++ uint32ToHex h6 ++ uint32ToHex h7

/-! ## 2. Spec-Block Extraction & Comment-Aware Source Lexing -/

/-- Drop the last `k` characters of a `String`. -/
def dropLastChars (s : String) (k : Nat) : String :=
  let cs := s.toList
  String.ofList (cs.take (cs.length - k))

/-- Extract locked lines between `-- BEGIN VERIGATE SPEC` and `-- END VERIGATE SPEC`. -/
def extractSpecRegion (src : String) : Option String := Id.run do
  let lines := src.splitOn "\n"
  let mut inside := false
  let mut collected : List String := []
  let mut foundEnd := false
  for rawLine in lines do
    let line := if rawLine.endsWith "\r" then dropLastChars rawLine 1 else rawLine
    let trimmed := line.trimAscii.toString
    if trimmed == "-- BEGIN VERIGATE SPEC" then
      inside := true
    else if trimmed == "-- END VERIGATE SPEC" then
      if inside then
        foundEnd := true
        inside := false
    else if inside then
      collected := line :: collected
  if foundEnd then
    some (String.intercalate "\n" collected.reverse)
  else
    none

/-- Compute the canonical SHA-256 spec hash of a source string. -/
def computeSpecHash (src : String) : String :=
  match extractSpecRegion src with
  | some region => sha256Hex region
  | none => sha256Hex src

/-- Strip `--` line comments, nested `/- ... -/` block comments, and string literals. -/
partial def stripCommentsAndStringsAux : List Char → Nat → Bool → List Char → List Char
  | [], _, _, acc => acc.reverse
  | c :: rest, blockDepth, inStr, acc =>
      if blockDepth > 0 then
        match c, rest with
        | '/', '-' :: rest' => stripCommentsAndStringsAux rest' (blockDepth + 1) false (' ' :: acc)
        | '-', '/' :: rest' => stripCommentsAndStringsAux rest' (blockDepth - 1) false (' ' :: acc)
        | '\n', _ => stripCommentsAndStringsAux rest blockDepth false ('\n' :: acc)
        | _, _ => stripCommentsAndStringsAux rest blockDepth false (' ' :: acc)
      else if inStr then
        match c, rest with
        | '\\', _ :: rest' => stripCommentsAndStringsAux rest' 0 true (' ' :: acc)
        | '"', _ => stripCommentsAndStringsAux rest 0 false (' ' :: acc)
        | '\n', _ => stripCommentsAndStringsAux rest 0 true ('\n' :: acc)
        | _, _ => stripCommentsAndStringsAux rest 0 true (' ' :: acc)
      else
        match c, rest with
        | '/', '-' :: rest' => stripCommentsAndStringsAux rest' 1 false (' ' :: acc)
        | '-', '-' :: rest' =>
            let afterLine := rest'.dropWhile (fun ch => ch != '\n')
            stripCommentsAndStringsAux afterLine 0 false (' ' :: acc)
        | '"', _ => stripCommentsAndStringsAux rest 0 true (' ' :: acc)
        | _, _ => stripCommentsAndStringsAux rest 0 false (c :: acc)

def tokenizeCodeIdentifiers (src : String) : List String := Id.run do
  let cleaned := stripCommentsAndStringsAux src.toList 0 false []
  let mut tokens : List String := []
  let mut cur : List Char := []
  for ch in cleaned do
    if ch.isAlphanum || ch == '_' || ch == '\'' then
      cur := ch :: cur
    else
      if !cur.isEmpty then
        tokens := String.ofList cur.reverse :: tokens
        cur := []
  if !cur.isEmpty then
    tokens := String.ofList cur.reverse :: tokens
  return tokens.reverse

/-! ## 3. Trust Tiers & Audit Configuration -/

inductive TrustTier where
  | tier0StrictKernel
  | tier1BvLrat
  deriving Repr, DecidableEq

structure AuditConfig where
  tier : TrustTier := .tier0StrictKernel
  expectedSpecHash? : Option String := none
  skipWitnessCheck : Bool := false
  deriving Repr, DecidableEq

structure AuditVerdict where
  target : String
  specHash : String
  passed : Bool
  violations : List String
  checkedDecls : Nat
  deriving Repr

/-! ## 4. Kernel `Lean.Environment` Inspection Helpers -/

def isStdKernelAxiom (n : Lean.Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

def nameContainsSubstr (n : Lean.Name) (needle : String) : Bool :=
  ((n.toString.splitOn needle).length > 1)

def isNativeDecideAxiom (n : Lean.Name) : Bool :=
  nameContainsSubstr n "._native.native_decide."

def isBvDecideAxiom (n : Lean.Name) : Bool :=
  nameContainsSubstr n "._native.bv_decide."

def isLegacyCompilerTrustAxiom (n : Lean.Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.trustCompiler

/--
  Recognize Lean 4.36's compiler-synthesized `Ind.ctorIdx -> Ind.ctorIdx._impl`
  generated automatically for every multi-constructor `inductive` declaration.
-/
def isBuiltinCtorIdxImpl (env : Lean.Environment) (decl target : Lean.Name) : Bool :=
  match decl with
  | .str indName "ctorIdx" =>
      target == .str decl "_impl" && (env.find? indName matches some (.inductInfo _))
  | _ => false

/--
  Recognize `deriving Repr` helper `instRepr<T>.repr` generated by Lean for nested
  inductive types when no user `opaque` keyword appears in source.
-/
def isDerivedReprHelper (decl : Lean.Name) (hasRawOpaque : Bool) : Bool :=
  if hasRawOpaque then false
  else
    match decl with
    | .str (.str _ parent) "repr" => parent.startsWith "instRepr"
    | _ => false

/-- Detect vacuous `False → ...` premises in a theorem's kernel `Expr` type. -/
def hasVacuousFalsePremise : Lean.Expr → Bool
  | .forallE _ dom body _ =>
      if dom.isConstOf ``False then true
      else hasVacuousFalsePremise body
  | .mdata _ inner => hasVacuousFalsePremise inner
  | _ => false

/-- Check whether `n` has a trailing identifier equal to `non_vacuous` or `non_vacuous_*`. -/
def isNonVacuousDeclName (n : Lean.Name) : Bool :=
  match n with
  | .str _ s => s == "non_vacuous" || s.startsWith "non_vacuous_"
  | _ => false

/-- Map a `.lean` path such as `Solutions/Capstones/VeriGateLab.lean` to a module `Name`. -/
def pathToModuleName (path : System.FilePath) : Lean.Name := Id.run do
  let norm := path.toString.replace "\\" "/"
  let withoutExt := if norm.endsWith ".lean" then dropLastChars norm 5 else norm
  let parts := (withoutExt.splitOn "/").filter (fun s => !s.isEmpty && s != ".")
  let mut acc := Lean.Name.anonymous
  for p in parts do
    acc := Lean.Name.str acc p
  return acc

/-- Locate the `lean` compiler binary (preferring `~/.elan/bin/lean` if not in PATH). -/
def findLeanBinary : IO String := do
  let probe ← IO.Process.output { cmd := "which", args := #["lean"] }
  if probe.exitCode == 0 && !probe.stdout.trimAscii.isEmpty then
    return probe.stdout.trimAscii.toString
  else
    match ← IO.getEnv "HOME" with
    | some home => return s!"{home}/.elan/bin/lean"
    | none => return "lean"

/-- Build search path combining `LEAN_PATH` and `.lake/build/lib/lean` if present. -/
def getEffectiveSearchPath : IO Lean.SearchPath := do
  let envPath := System.SearchPath.parse ((← IO.getEnv "LEAN_PATH").getD "")
  let lakeLib : System.FilePath := ".lake/build/lib/lean"
  if ← lakeLib.pathExists then
    return lakeLib :: envPath
  else
    return envPath

/--
  Load `(Lean.Environment × Lean.ModuleData)` for `filePath`.
  Uses precompiled `.olean` when fresh in `searchPath`; otherwise compiles `filePath`
  to a temporary `.olean` via `lean -o` and imports it cleanly with `loadExts := false`.
-/
def loadModuleEnvironment (filePath : System.FilePath) :
    IO (Except String (Lean.Environment × Lean.ModuleData)) := do
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
  if usePrebuilt then
    try
      let env ← Lean.importModules #[{ module := modName }] {} 0 #[] false false
      match env.allImportedModuleNames.idxOf? modName with
      | none => return .error s!"INTERNAL_ERROR: module `{modName}` missing from imported headers"
      | some idx =>
        if h : idx < env.header.moduleData.size then
          return .ok (env, env.header.moduleData[idx])
        else
          return .error "INTERNAL_ERROR: moduleData index out of bounds"
    catch e =>
      return .error s!"IMPORT_FAILED: {e}"
  else
    IO.FS.withTempDir fun tmpDir => do
      let activeMod := Lean.Name.str .anonymous s!"VeriGateAudit_{(computeSpecHash filePath.toString).take 12}"
      let outOlean := tmpDir / s!"{activeMod}.olean"
      let envPathStr := String.intercalate ":" (baseSp.map (·.toString))
      let proc ← IO.Process.output {
        cmd := leanBin
        args := #["-o", outOlean.toString, filePath.toString]
        env := #[("LEAN_PATH", some envPathStr)]
      }
      if proc.exitCode != 0 then
        return .error s!"ELABORATION_FAILED: {proc.stderr.trimAscii.toString}{proc.stdout.trimAscii.toString}"
      let activeSp := tmpDir :: baseSp
      Lean.initSearchPath sysroot activeSp
      try
        let env ← Lean.importModules #[{ module := activeMod }] {} 0 #[] false false
        match env.allImportedModuleNames.idxOf? activeMod with
        | none => return .error s!"INTERNAL_ERROR: module `{activeMod}` missing from imported headers"
        | some idx =>
          if h : idx < env.header.moduleData.size then
            return .ok (env, env.header.moduleData[idx])
          else
            return .error "INTERNAL_ERROR: moduleData index out of bounds"
      catch e =>
        return .error s!"IMPORT_FAILED: {e}"

/-! ## 5. Full Source + Kernel Environment Audit -/

def auditFile (filePath : System.FilePath) (cfg : AuditConfig) : IO AuditVerdict := do
  if !(← filePath.pathExists) then
    return {
      target := filePath.toString
      specHash := ""
      passed := false
      violations := [s!"FILE_NOT_FOUND: `{filePath}` does not exist"]
      checkedDecls := 0
    }
  let src ← IO.FS.readFile filePath
  let specHash := computeSpecHash src
  let mut violations : List String := []

  -- 1. SHA-256 Spec-Lock Check
  if let some expected := cfg.expectedSpecHash? then
    if specHash != expected.trimAscii.toString.toLower then
      violations := s!"SPEC_HASH_MISMATCH: expected `{expected}`, computed `{specHash}`" :: violations

  -- 2. Comment-Aware Source Token Scan
  let tokens := tokenizeCodeIdentifiers src
  let hasRawNativeDecide := tokens.contains "native_decide"
  let hasRawOpaque := tokens.contains "opaque"
  if hasRawNativeDecide then
    violations := "RAW_NATIVE_DECIDE: source invokes `native_decide` (bypasses kernel reduction)" :: violations

  -- 3. Kernel `Lean.Environment` Inspection
  match ← loadModuleEnvironment filePath with
  | .error errMsg =>
      violations := errMsg :: violations
      return {
        target := filePath.toString
        specHash := specHash
        passed := false
        violations := violations.reverse
        checkedDecls := 0
      }
  | .ok (env, modData) =>
      let csimpState := Lean.Compiler.CSimp.ext.getState env
      let mut hasValidWitness := false
      let mut userDeclCount : Nat := 0

      for cinfo in modData.constants do
        let name := cinfo.name
        let isInternal := name.isInternalDetail

        -- 3a. Direct Axiom Declarations in Module
        if cinfo matches .axiomInfo _ then
          if isNativeDecideAxiom name then
            violations := s!"AXIOM_NATIVE_DECIDE: `{name}` trusts compiled native evaluation" :: violations
          else if isBvDecideAxiom name then
            match cfg.tier with
            | .tier0StrictKernel =>
                violations := s!"AXIOM_BV_TRUST_TIER0: `{name}` rejected under `--strict-kernel` (use `--trust-tier=bv-lrat`)" :: violations
            | .tier1BvLrat =>
                if hasRawNativeDecide then
                  violations := s!"AXIOM_BV_TAINTED: `{name}` rejected because raw `native_decide` appears in source" :: violations
          else
            violations := s!"CUSTOM_AXIOM: module declares unverified axiom `{name}`" :: violations

        if !isInternal then
          userDeclCount := userDeclCount + 1

          -- 3b. Opaque / Unsafe / Partial Checks
          match cinfo with
          | .opaqueInfo _ =>
              if !isDerivedReprHelper name hasRawOpaque then
                violations := s!"OPAQUE_DECL: `{name}` hides implementation via `opaque`" :: violations
          | .defnInfo dv =>
              match dv.safety with
              | .unsafe =>
                  violations := s!"UNSAFE_DEF: `{name}` is marked `unsafe`" :: violations
              | .partial =>
                  violations := s!"PARTIAL_DEF: `{name}` is marked `partial` (unproven termination)" :: violations
              | .safe => pure ()
          | _ => pure ()

          -- 3c. Compiler Attribute Overrides (`@[implemented_by]`, `@[extern]`, `@[csimp]`)
          if let some target := Lean.Compiler.implementedByAttr.getParam? env name then
            if !isBuiltinCtorIdxImpl env name target && !isDerivedReprHelper name hasRawOpaque then
              violations := s!"IMPLEMENTED_BY: `{name}` swaps runtime code to `{target}`" :: violations
          if Lean.isExtern env name then
            violations := s!"EXTERN_DECL: `{name}` links unverified FFI via `@[extern]`" :: violations
          if csimpState.map.contains name || csimpState.thmNames.contains name then
            violations := s!"CSIMP_OVERRIDE: `{name}` alters compiler codegen via `@[csimp]`" :: violations

          -- 3d. Transitive Kernel Axiom Collection
          let (axs, _) ← Lean.Core.CoreM.toIO (Lean.collectAxioms name)
            { fileName := filePath.toString, fileMap := default }
            { env := env }
          for ax in axs do
            if ax == ``sorryAx then
              violations := s!"SORRY_AXIOM: `{name}` depends on `sorryAx`" :: violations
            else if isStdKernelAxiom ax then
              pure ()
            else if isNativeDecideAxiom ax then
              violations := s!"COMPILER_TRUST_AXIOM: `{name}` depends on `native_decide` axiom `{ax}`" :: violations
            else if isBvDecideAxiom ax || isLegacyCompilerTrustAxiom ax then
              match cfg.tier with
              | .tier0StrictKernel =>
                  violations := s!"COMPILER_TRUST_AXIOM: `{name}` depends on `{ax}` (forbidden in Tier 0)" :: violations
              | .tier1BvLrat =>
                  if hasRawNativeDecide then
                    violations := s!"COMPILER_TRUST_AXIOM: `{name}` depends on `{ax}` with raw `native_decide` present" :: violations
            else
              violations := s!"CUSTOM_AXIOM_DEP: `{name}` transitively depends on custom axiom `{ax}`" :: violations

          -- 3e. Vacuous `False → ...` Premise & Non-Vacuity Witness Tracking
          if let .thmInfo tv := cinfo then
            let isVacuous := hasVacuousFalsePremise tv.type
            if isVacuous then
              violations := s!"VACUOUS_THEOREM: `{name}` has a contradictory `False → ...` premise" :: violations
            if isNonVacuousDeclName name && !isVacuous then
              hasValidWitness := true

      if !cfg.skipWitnessCheck && !hasValidWitness then
        violations := "MISSING_NON_VACUOUS: module lacks a valid `non_vacuous` witness theorem" :: violations

      let deduped := violations.reverse.eraseDups
      return {
        target := filePath.toString
        specHash := specHash
        passed := deduped.isEmpty
        violations := deduped
        checkedDecls := userDeclCount
      }

/-! ## 6. Built-In Red-Team Self-Test Suite (`--self-test`) -/

structure SelfTestCase where
  label : String
  path : String
  cfg : AuditConfig
  expectPass : Bool

def runSelfTest : IO UInt32 := do
  IO.println "========================================================================"
  IO.println "  VeriGate Proof-Carrying Code Gate — Built-In Adversarial Self-Test"
  IO.println "========================================================================"

  -- 1. Cryptographic SHA-256 NIST FIPS 180-4 Self-Check
  let abcDigest := sha256Hex "abc"
  let emptyDigest := sha256Hex ""
  let shaOk :=
    abcDigest == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
    emptyDigest == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  if !shaOk then
    IO.println s!"[FATAL] SHA-256 self-check failed: got {abcDigest}"
    return 1
  IO.println "[OK] RFC 6234 SHA-256 engine verified against NIST FIPS 180-4 vectors"

  -- Pin the human-locked spec hash from CleanKernel.lean
  let cleanSrc ← IO.FS.readFile "RedTeam/CleanKernel.lean"
  let lockedVaultHash := computeSpecHash cleanSrc

  let cases : List SelfTestCase := [
    { label := "Capstone 4 Model Solution (Tier 0)"
      path := "Solutions/Capstones/VeriGateLab.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := true },
    { label := "Clean Baseline + Locked SHA-256 (Tier 0)"
      path := "RedTeam/CleanKernel.lean"
      cfg := { tier := .tier0StrictKernel, expectedSpecHash? := some lockedVaultHash }
      expectPass := true },
    { label := "BitVec `bv_decide` Module under Tier 0 (`--strict-kernel`)"
      path := "RedTeam/BvLratClean.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := false },
    { label := "BitVec `bv_decide` Module under Tier 1 (`--trust-tier=bv-lrat`)"
      path := "RedTeam/BvLratClean.lean"
      cfg := { tier := .tier1BvLrat }
      expectPass := true },
    { label := "Exploit 1: Silenced `sorry` (`set_option warn.sorry false`)"
      path := "RedTeam/SorryCheat.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := false },
    { label := "Exploit 2: Custom `axiom` Smuggling"
      path := "RedTeam/AxiomCheat.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := false },
    { label := "Exploit 3a: `native_decide` Bypass under Tier 0"
      path := "RedTeam/NativeDecideCheat.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := false },
    { label := "Exploit 3b: `native_decide` Bypass under Tier 1 (`bv-lrat`)"
      path := "RedTeam/NativeDecideCheat.lean"
      cfg := { tier := .tier1BvLrat }
      expectPass := false },
    { label := "Exploit 4: `@[implemented_by]` Runtime Code Swap"
      path := "RedTeam/ImplementedByCheat.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := false },
    { label := "Exploit 5: Vacuous `False → ...` Theorem & Witness"
      path := "RedTeam/VacuousSpecCheat.lean"
      cfg := { tier := .tier0StrictKernel }
      expectPass := false },
    { label := "Exploit 6: Tampered `VERIGATE SPEC` vs Locked SHA-256"
      path := "RedTeam/SpecTamperCheat.lean"
      cfg := { tier := .tier0StrictKernel, expectedSpecHash? := some lockedVaultHash }
      expectPass := false }
  ]

  let mut allMatched := true
  for tc in cases do
    let verdict ← auditFile tc.path tc.cfg
    let gateTag := if verdict.passed then "PASS  " else "REJECT"
    let matched := (verdict.passed == tc.expectPass)
    if !matched then
      allMatched := false
    let statusIcon := if matched then "[OK]" else "[FAIL]"
    IO.println s!"{statusIcon} [{gateTag}] {tc.label}"
    if !verdict.violations.isEmpty then
      for v in verdict.violations do
        IO.println s!"             ↳ {v}"

  IO.println "------------------------------------------------------------------------"
  if allMatched then
    IO.println "SELF-TEST RESULT: ALL 11 VERIFICATION GATE CHECKS BEHAVED AS EXPECTED."
    return 0
  else
    IO.println "SELF-TEST RESULT: FAILURE — UNEXPECTED GATE VERDICT DETECTED!"
    return 1

/-! ## 7. CLI Entrypoint -/

def printUsage : IO Unit := do
  IO.println "Usage: lake exe verigate [OPTIONS] <file.lean ...>"
  IO.println ""
  IO.println "Options:"
  IO.println "  --self-test              Run built-in NIST SHA-256 & Red-Team exploit suite"
  IO.println "  --strict-kernel          Tier 0 (default): allow ONLY {propext, Quot.sound, Classical.choice}"
  IO.println "  --trust-tier=bv-lrat     Tier 1: allow `bv_decide` LRAT axioms when zero raw `native_decide` exist"
  IO.println "  --spec-hash=<sha256>     Require exact SHA-256 match on `VERIGATE SPEC` block"
  IO.println "  --print-spec-hash <file> Print SHA-256 digest of `VERIGATE SPEC` block and exit"
  IO.println "  --skip-witness-check     Do not require a `non_vacuous` theorem in exploratory files"
  IO.println "  --help, -h               Show this help message"

partial def parseArgs : List String → AuditConfig → Bool → Option String → List String →
    Except String (AuditConfig × Bool × Option String × List String)
  | [], cfg, selfTest, printHash?, files => .ok (cfg, selfTest, printHash?, files.reverse)
  | "--self-test" :: rest, cfg, _, printHash?, files =>
      parseArgs rest cfg true printHash? files
  | "--strict-kernel" :: rest, cfg, selfTest, printHash?, files =>
      parseArgs rest { cfg with tier := .tier0StrictKernel } selfTest printHash? files
  | "--trust-tier=strict-kernel" :: rest, cfg, selfTest, printHash?, files =>
      parseArgs rest { cfg with tier := .tier0StrictKernel } selfTest printHash? files
  | "--trust-tier=bv-lrat" :: rest, cfg, selfTest, printHash?, files =>
      parseArgs rest { cfg with tier := .tier1BvLrat } selfTest printHash? files
  | "--skip-witness-check" :: rest, cfg, selfTest, printHash?, files =>
      parseArgs rest { cfg with skipWitnessCheck := true } selfTest printHash? files
  | "--print-spec-hash" :: target :: rest, cfg, selfTest, _, files =>
      parseArgs rest cfg selfTest (some target) files
  | "--spec-hash" :: hash :: rest, cfg, selfTest, printHash?, files =>
      parseArgs rest { cfg with expectedSpecHash? := some hash } selfTest printHash? files
  | arg :: rest, cfg, selfTest, printHash?, files =>
      if arg.startsWith "--spec-hash=" then
        let hash := (arg.drop 12).toString
        parseArgs rest { cfg with expectedSpecHash? := some hash } selfTest printHash? files
      else if arg.startsWith "-" then
        .error s!"Unknown flag `{arg}`"
      else
        parseArgs rest cfg selfTest printHash? (arg :: files)

end Tools.VeriGate

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "--help" || args.contains "-h" then
    Tools.VeriGate.printUsage
    return if args.isEmpty then 1 else 0
  match Tools.VeriGate.parseArgs args {} false none [] with
  | .error msg =>
      IO.eprintln s!"Error: {msg}"
      Tools.VeriGate.printUsage
      return 2
  | .ok (_, true, _, _) =>
      Tools.VeriGate.runSelfTest
  | .ok (_, false, some target, _) =>
      if !(← System.FilePath.pathExists target) then
        IO.eprintln s!"Error: file `{target}` not found"
        return 1
      let src ← IO.FS.readFile target
      IO.println (Tools.VeriGate.computeSpecHash src)
      return 0
  | .ok (cfg, false, none, files) =>
      if files.isEmpty then
        IO.eprintln "Error: no `.lean` target files specified."
        Tools.VeriGate.printUsage
        return 2
      let mut allPassed := true
      for f in files do
        let verdict ← Tools.VeriGate.auditFile f cfg
        if verdict.passed then
          IO.println s!"[PASS] {verdict.target} (decls={verdict.checkedDecls}, spec_sha256={verdict.specHash.take 16}...)"
        else
          allPassed := false
          IO.println s!"[REJECT] {verdict.target} (spec_sha256={verdict.specHash.take 16}...)"
          for v in verdict.violations do
            IO.println s!"  ✗ {v}"
      return if allPassed then 0 else 1
