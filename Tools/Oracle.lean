/-
  Tools/Oracle.lean (`lake exe oracle`)
  Verified Differential Fuzzing Oracle CLI for `CedarLite` and `FencingKV`

  Allows Rust, Go, TypeScript, and Python property-based test suites to differential-test
  production authorization engines and fenced storage servers against Lean-proven specs
  via single-shot CLI arguments or streaming JSONL / line-protocol `stdin` batches.
-/
import Solutions.Capstones.CedarLite
import Solutions.Capstones.FencingKV

set_option autoImplicit false

namespace Tools.Oracle

/-! ## 1. Minimal Zero-Dependency JSON Parser & Serializer -/

inductive JsonVal where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (items : List JsonVal)
  | obj (fields : List (String × JsonVal))
  deriving Repr

def escapeJsonStr (s : String) : String := Id.run do
  let mut out : List Char := ['"']
  for c in s.toList do
    match c with
    | '"' => out := '"' :: '\\' :: out
    | '\\' => out := '\\' :: '\\' :: out
    | '\n' => out := 'n' :: '\\' :: out
    | '\r' => out := 'r' :: '\\' :: out
    | '\t' => out := 't' :: '\\' :: out
    | _ => out := c :: out
  out := '"' :: out
  return String.ofList out.reverse

mutual
def renderJson : JsonVal → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num n => toString n
  | .str s => escapeJsonStr s
  | .arr items => "[" ++ String.intercalate "," (renderJsonList items) ++ "]"
  | .obj fields => "{" ++ String.intercalate "," (renderJsonFields fields) ++ "}"

def renderJsonList : List JsonVal → List String
  | [] => []
  | v :: rest => renderJson v :: renderJsonList rest

def renderJsonFields : List (String × JsonVal) → List String
  | [] => []
  | (k, v) :: rest => (escapeJsonStr k ++ ":" ++ renderJson v) :: renderJsonFields rest
end

def skipWs : List Char → List Char
  | [] => []
  | c :: rest => if c.isWhitespace then skipWs rest else c :: rest

def parseStringChars : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | '"' :: rest, acc => some (String.ofList acc.reverse, rest)
  | '\\' :: 'n' :: rest, acc => parseStringChars rest ('\n' :: acc)
  | '\\' :: 'r' :: rest, acc => parseStringChars rest ('\r' :: acc)
  | '\\' :: 't' :: rest, acc => parseStringChars rest ('\t' :: acc)
  | '\\' :: c :: rest, acc => parseStringChars rest (c :: acc)
  | c :: rest, acc => parseStringChars rest (c :: acc)

def parseDigits : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | c :: rest, acc =>
      if c.isDigit then parseDigits rest (c :: acc)
      else (acc.reverse, c :: rest)

def parseIntChars (cs : List Char) : Option (Int × List Char) :=
  match cs with
  | '-' :: rest =>
      let (digits, rem) := parseDigits rest []
      if digits.isEmpty then none
      else
        match (String.ofList digits).toNat? with
        | some n => some (-Int.ofNat n, rem)
        | none => none
  | _ =>
      let (digits, rem) := parseDigits cs []
      if digits.isEmpty then none
      else
        match (String.ofList digits).toNat? with
        | some n => some (Int.ofNat n, rem)
        | none => none

mutual
def parseJsonVal (fuel : Nat) (cs : List Char) : Option (JsonVal × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match skipWs cs with
      | [] => none
      | '"' :: rest =>
          match parseStringChars rest [] with
          | some (s, rem) => some (.str s, rem)
          | none => none
      | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
      | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
      | '[' :: rest =>
          match skipWs rest with
          | ']' :: rem => some (.arr [], rem)
          | _ => parseJsonArr fuel' rest []
      | '{' :: rest =>
          match skipWs rest with
          | '}' :: rem => some (.obj [], rem)
          | _ => parseJsonObj fuel' rest []
      | rest =>
          match parseIntChars rest with
          | some (n, rem) => some (.num n, rem)
          | none => none

def parseJsonArr (fuel : Nat) (cs : List Char) (acc : List JsonVal) :
    Option (JsonVal × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match parseJsonVal fuel' cs with
      | none => none
      | some (v, rem) =>
          match skipWs rem with
          | ',' :: next => parseJsonArr fuel' next (v :: acc)
          | ']' :: next => some (.arr (v :: acc).reverse, next)
          | _ => none

def parseJsonObj (fuel : Nat) (cs : List Char) (acc : List (String × JsonVal)) :
    Option (JsonVal × List Char) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match skipWs cs with
      | '"' :: restKey =>
          match parseStringChars restKey [] with
          | none => none
          | some (key, afterKey) =>
              match skipWs afterKey with
              | ':' :: afterColon =>
                  match parseJsonVal fuel' afterColon with
                  | none => none
                  | some (v, rem) =>
                      match skipWs rem with
                      | ',' :: next => parseJsonObj fuel' next ((key, v) :: acc)
                      | '}' :: next => some (.obj ((key, v) :: acc).reverse, next)
                      | _ => none
              | _ => none
      | _ => none
end

def parseJson (s : String) : Option JsonVal :=
  let cs := s.toList
  match parseJsonVal (cs.length + 16) cs with
  | some (v, rem) => if (skipWs rem).isEmpty then some v else none
  | none => none

def JsonVal.field? (j : JsonVal) (key : String) : Option JsonVal :=
  match j with
  | .obj fields =>
      match fields.find? (fun (k, _) => k == key) with
      | some (_, v) => some v
      | none => none
  | _ => none

def JsonVal.asStr? : JsonVal → Option String
  | .str s => some s
  | _ => none

def JsonVal.asNat? : JsonVal → Option Nat
  | .num n => if n ≥ 0 then some n.toNat else none
  | _ => none

/-! ## 2. `CedarLite` Verified Oracle Adapter -/

open CedarLite in
def jsonToAttrVal (j : JsonVal) : Option AttrVal :=
  match j with
  | .str s => some (.str s)
  | .num n => some (.int n)
  | .bool b => some (.bool b)
  | _ => none

open CedarLite in
def jsonToAttrs (j : Option JsonVal) : List (String × AttrVal) :=
  match j with
  | some (.obj fields) =>
      fields.filterMap fun (k, v) =>
        match jsonToAttrVal v with
        | some av => some (k, av)
        | none => none
  | _ => []

open CedarLite in
def jsonToStrList (j : Option JsonVal) : List String :=
  match j with
  | some (.arr items) => items.filterMap JsonVal.asStr?
  | _ => []

open CedarLite in
def jsonToEntity (j : JsonVal) : Option Entity :=
  match j with
  | .str id => some { id := id }
  | .obj _ =>
      match j.field? "id" >>= JsonVal.asStr? with
      | some id =>
          some {
            id := id
            groups := jsonToStrList (j.field? "groups")
            attrs := jsonToAttrs (j.field? "attrs")
          }
      | none => none
  | _ => none

open CedarLite in
def decodeScope (j : Option JsonVal) : Scope :=
  match j with
  | some (.str "any") | none => .any
  | some (.obj _) =>
      if let some id := (j >>= fun x => x.field? "eq") >>= JsonVal.asStr? then .eq id
      else if let some g := (j >>= fun x => x.field? "inGroup") >>= JsonVal.asStr? then .inGroup g
      else .any
  | some (.str s) =>
      if s.startsWith "group:" then .inGroup (s.drop 6).toString else .eq s
  | _ => .any

open CedarLite in
def decodeActionScope (j : Option JsonVal) : ActionScope :=
  match j with
  | some (.str "any") | none => .any
  | some (.str act) => .eq act
  | some (.arr items) => .oneOf (items.filterMap JsonVal.asStr?)
  | _ => .any

open CedarLite in
def decodePolicy (j : JsonVal) : Option Policy := do
  let id ← (j.field? "id" >>= JsonVal.asStr?).orElse (fun _ => some "rule")
  let effStr ← j.field? "effect" >>= JsonVal.asStr?
  let eff ← if effStr == "permit" then some Effect.permit
            else if effStr == "forbid" then some Effect.forbid
            else none
  return {
    id := id
    effect := eff
    principalScope := decodeScope (j.field? "principalScope")
    actionScope := decodeActionScope (j.field? "actionScope")
    resourceScope := decodeScope (j.field? "resourceScope")
    condition := .always
  }

open CedarLite in
def parseCompactAttrVal (raw : String) : AttrVal :=
  if raw == "true" then .bool true
  else if raw == "false" then .bool false
  else match raw.toInt? with
    | some n => .int n
    | none => .str raw

open CedarLite in
/--
  Parse compact key=value CedarLite query format, e.g.:
  `principal=alice groups=eng,ops action=write resource=doc-42 owner=alice mfa=true riskScore=10`
-/
def parseCompactCedarRequest (query : String) : Request := Id.run do
  let parts := (query.splitOn " ").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let mut principalId := "anonymous"
  let mut groups : List String := []
  let mut action := "read"
  let mut resourceId := "default"
  let mut resAttrs : List (String × AttrVal) := []
  let mut ctxAttrs : List (String × AttrVal) := []
  for part in parts do
    match part.splitOn "=" with
    | [k, v] =>
        if k == "principal" then principalId := v
        else if k == "groups" then groups := (v.splitOn ",").filter (!·.isEmpty)
        else if k == "action" then action := v
        else if k == "resource" then resourceId := v
        else if k == "owner" then resAttrs := ("owner", .str v) :: resAttrs
        else ctxAttrs := (k, parseCompactAttrVal v) :: ctxAttrs
    | _ => pure ()
  return {
    principal := { id := principalId, groups := groups }
    action := action
    resource := { id := resourceId, attrs := resAttrs.reverse }
    context := ctxAttrs.reverse
  }

open CedarLite in
def evalCedarOracle (input : String) : String :=
  let trimmed := input.trimAscii.toString
  let (policies, req?) : List Policy × Option Request :=
    if trimmed.startsWith "{" then
      match parseJson trimmed with
      | none => ([], none)
      | some j =>
          let reqOpt : Option Request := do
            let pJson ← j.field? "principal"
            let p ← jsonToEntity pJson
            let act ← j.field? "action" >>= JsonVal.asStr?
            let rJson ← j.field? "resource"
            let r ← jsonToEntity rJson
            let ctx := jsonToAttrs (j.field? "context")
            return { principal := p, action := act, resource := r, context := ctx }
          let pols :=
            match j.field? "policies" with
            | some (.arr items) => items.filterMap decodePolicy
            | _ => samplePolicies
          (pols, reqOpt)
    else
      (samplePolicies, some (parseCompactCedarRequest trimmed))
  match req? with
  | none =>
      renderJson (.obj [("engine", .str "CedarLite"), ("error", .str "invalid request payload")])
  | some req =>
      let optPolicies := optimizePolicies policies
      let dec := authorize policies req
      let optDec := authorize optPolicies req
      let decStr := match dec with | .allow => "allow" | .deny => "deny"
      let optStr := match optDec with | .allow => "allow" | .deny => "deny"
      renderJson (.obj [
        ("engine", .str "CedarLite"),
        ("decision", .str decStr),
        ("optimizedDecision", .str optStr),
        ("optimizerEquivalent", .bool (decide (dec = optDec))),
        ("policiesCount", .num (Int.ofNat policies.length)),
        ("optimizedPoliciesCount", .num (Int.ofNat optPolicies.length))
      ])

/-! ## 3. `FencingKV` Verified Oracle Adapter -/

inductive OracleKVOp where
  | put (token : Nat) (key : String) (val : String)
  | del (token : Nat) (key : String)
  | compact
  | get (key : String)
  deriving Repr

def parseKVLineOp (raw : String) : Option OracleKVOp :=
  let toks := (raw.splitOn " ").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  match toks with
  | ["put", tokStr, k, v] =>
      tokStr.toNat?.map fun tok => .put tok k v
  | ["del", tokStr, k] =>
      tokStr.toNat?.map fun tok => .del tok k
  | ["compact"] => some .compact
  | ["get", k] => some (.get k)
  | _ => none

def parseKVJsonOp (j : JsonVal) : Option OracleKVOp := do
  let kind ← j.field? "op" >>= JsonVal.asStr?
  if kind == "put" then
    let tok ← j.field? "token" >>= JsonVal.asNat?
    let k ← j.field? "key" >>= JsonVal.asStr?
    let v ← j.field? "val" >>= JsonVal.asStr?
    return .put tok k v
  else if kind == "del" then
    let tok ← j.field? "token" >>= JsonVal.asNat?
    let k ← j.field? "key" >>= JsonVal.asStr?
    return .del tok k
  else if kind == "compact" then
    return .compact
  else if kind == "get" then
    let k ← j.field? "key" >>= JsonVal.asStr?
    return .get k
  else
    none

open FencingKV in
def evalKVOracle (input : String) : String := Id.run do
  let trimmed := input.trimAscii.toString
  let ops? : Option (List OracleKVOp) :=
    if trimmed.startsWith "{" || trimmed.startsWith "[" then
      match parseJson trimmed with
      | some (.arr items) => some (items.filterMap parseKVJsonOp)
      | some j =>
          match j.field? "ops" with
          | some (.arr items) => some (items.filterMap parseKVJsonOp)
          | _ => none
      | none => none
    else
      let chunks := (trimmed.splitOn ";").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
      let parsed := chunks.filterMap parseKVLineOp
      if parsed.length == chunks.length then some parsed else none
  match ops? with
  | none =>
      return renderJson (.obj [("engine", .str "FencingKV"), ("error", .str "invalid KV operations")])
  | some ops =>
      let mut st := initDistState
      let mut events : List JsonVal := []
      let mut reads : List JsonVal := []
      for op in ops do
        match op with
        | .put tok k v =>
            let accepted := decide (st.storageFence ≤ tok)
            st := deliverFencedExec st { token := tok, payload := .put k v }
            events := (.obj [
              ("op", .str "put"),
              ("token", .num (Int.ofNat tok)),
              ("key", .str k),
              ("status", .str (if accepted then "committed" else "rejected_stale"))
            ]) :: events
        | .del tok k =>
            let accepted := decide (st.storageFence ≤ tok)
            st := deliverFencedExec st { token := tok, payload := .del k }
            events := (.obj [
              ("op", .str "del"),
              ("token", .num (Int.ofNat tok)),
              ("key", .str k),
              ("status", .str (if accepted then "committed" else "rejected_stale"))
            ]) :: events
        | .compact =>
            st := { st with store := TombstoneKV.compact st.store }
            events := (.obj [
              ("op", .str "compact"),
              ("physicalEntries", .num (Int.ofNat st.store.length))
            ]) :: events
        | .get k =>
            let valJson := match TombstoneKV.get st.store k with
              | some v => JsonVal.str v
              | none => JsonVal.null
            reads := (.obj [("key", .str k), ("value", valJson)]) :: reads
      return renderJson (.obj [
        ("engine", .str "FencingKV"),
        ("storageFence", .num (Int.ofNat st.storageFence)),
        ("committedEpoch", .num (Int.ofNat st.committedEpoch)),
        ("noSplitBrain", .bool (NoSplitBrainOverwrite st)),
        ("physicalStoreSize", .num (Int.ofNat st.store.length)),
        ("events", .arr events.reverse),
        ("reads", .arr reads.reverse)
      ])

/-! ## 4. Demo & Batch Modes -/

def runDemo : IO UInt32 := do
  IO.println "========================================================================"
  IO.println "  Verified Differential Fuzzing Oracle (`CedarLite` + `FencingKV`)"
  IO.println "========================================================================"
  IO.println ""
  IO.println "1. CedarLite Query A — Low-Risk MFA Owner Write (Expected: allow)"
  IO.println ("   " ++ evalCedarOracle
    "principal=alice groups=eng action=write resource=doc-42 owner=alice mfa=true riskScore=10")
  IO.println ""
  IO.println "2. CedarLite Query B — High-Risk Admin Delete (Expected: deny via forbidOverridesPermit)"
  IO.println ("   " ++ evalCedarOracle
    "{\"principal\":{\"id\":\"root\",\"groups\":[\"admins\"]},\"action\":\"delete\",\"resource\":\"prod-db\",\"context\":{\"riskScore\":95}}")
  IO.println ""
  IO.println "3. FencingKV Trace — Stale Leader Rejection + Tombstone Compaction"
  IO.println ("   " ++ evalKVOracle
    "put 1 cfg v1; put 2 cfg v2; put 1 cfg stale_zombie; put 3 tmp scratch; del 4 tmp; compact; get cfg; get tmp")
  return 0

partial def runBatchLoop (stdin : IO.FS.Stream) (defaultMode : String) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then
    return 0
  let trimmed := line.trimAscii.toString
  if !trimmed.isEmpty then
    if defaultMode == "cedar" then
      IO.println (evalCedarOracle trimmed)
    else if defaultMode == "kv" then
      IO.println (evalKVOracle trimmed)
    else if trimmed.startsWith "cedar " then
      IO.println (evalCedarOracle (trimmed.drop 6).toString)
    else if trimmed.startsWith "kv " then
      IO.println (evalKVOracle (trimmed.drop 3).toString)
    else
      IO.println (renderJson (.obj [("error", .str "prefix batch line with `cedar ` or `kv `")]))
  runBatchLoop stdin defaultMode

def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  lake exe oracle --demo"
  IO.println "  lake exe oracle cedar <json-or-key=val-query>"
  IO.println "  lake exe oracle kv \"put 1 k v1; put 2 k v2; put 1 k stale; compact; get k\""
  IO.println "  lake exe oracle [cedar|kv] --stdin"

end Tools.Oracle

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] =>
      Tools.Oracle.printUsage
      return if args.isEmpty then 1 else 0
  | ["--demo"] =>
      Tools.Oracle.runDemo
  | ["--stdin"] | ["batch"] =>
      Tools.Oracle.runBatchLoop (← IO.getStdin) "auto"
  | ["cedar", "--stdin"] =>
      Tools.Oracle.runBatchLoop (← IO.getStdin) "cedar"
  | ["kv", "--stdin"] =>
      Tools.Oracle.runBatchLoop (← IO.getStdin) "kv"
  | "cedar" :: rest =>
      if rest.isEmpty then
        Tools.Oracle.printUsage
        return 1
      IO.println (Tools.Oracle.evalCedarOracle (String.intercalate " " rest))
      return 0
  | "kv" :: rest =>
      if rest.isEmpty then
        Tools.Oracle.printUsage
        return 1
      IO.println (Tools.Oracle.evalKVOracle (String.intercalate " " rest))
      return 0
  | _ =>
      Tools.Oracle.printUsage
      return 1
