import MorphoMidnight.Import
import Compiler.SoliditySlice.Coverage

open Compiler.CompilationModel
open Compiler.CompilationModel.SoliditySlice
open Compiler.CompilationModel.Denote

/-- Places the two position words and the market-state word for `id = 1`,
`user = 2`. `mappingSlot base key := base + key + 1` is not Keccak. The
numeric checks are about the values the packed reads return. -/
def sliceOracle : DenoteOracle where
  mappingSlot base key := base + key + 1
  keccakMemorySlice _ _ _ := 0

def packHalves (lo hi : Nat) : Nat := lo + hi * 2 ^ 128

def witnessWorld (credit pending lossFactor lastLoss lastAccrual : Nat) : Verity.ContractState :=
  Verity.defaultState.withStorageWords fun key =>
    let word :=
      match key with
      | .slot 5 => packHalves credit pending
      | .slot 6 => packHalves lastLoss lastAccrual
      | .slot 3 => packHalves 0 lossFactor
      | _ => 0
    Verity.Core.Uint256.ofNat word

def witnessBindings (maturity : Nat) : Env :=
  [("market_maturity", maturity), ("id", 1), ("user", 2)]

def midnightBody : List Stmt :=
  match midnight.model.functions with
  | fn :: _ => fn.body
  | [] => []

def runWitness (credit pending lossFactor lastLoss lastAccrual timestamp maturity : Nat) :
    Option (List Nat) :=
  denoteScalarBody sliceOracle midnight.model.fields
    (witnessWorld credit pending lossFactor lastLoss lastAccrual)
    timestamp (witnessBindings maturity) midnightBody

-- Interpreter checks of the two required witnesses. A failure here fails the build.
-- These are not kernel proofs of the five properties.
#eval show IO Unit from do
  let success := runWitness 100 10 0 0 0 50 100
  unless success == some [95, 5, 5] do
    throw (IO.userError s!"witness A returned {success}")
  let reverted := runWitness 1 2 0 0 0 1 1
  unless reverted == none do
    throw (IO.userError s!"witness B returned {reverted}")
  IO.println s!"imported {midnight.report.includedFunctions.length} functions"
  let mut manifest := s!"importer {midnight.report.importerVersion}\n"
  manifest := manifest ++ s!"solc {midnight.report.solcLongVersion}\n"
  manifest := manifest ++ s!"solcSha256 {midnight.report.solcSha256}\n"
  manifest := manifest ++ s!"digest {midnight.report.sourceDigest}\n"
  manifest := manifest ++ s!"contract {midnight.report.contract}\n"
  manifest := manifest ++ s!"root {midnight.report.rootFunction}\n"
  manifest := manifest ++ s!"settings {midnight.report.settingsJson}\n"
  for fn in midnight.report.includedFunctions do
    let line := s!"include {fn.contract}.{fn.name} decl {fn.declId} params {fn.paramTypes}\n"
    manifest := manifest ++ line
    IO.println line
  for fn in midnight.report.excludedFunctions do
    manifest := manifest ++ s!"exclude {fn.contract}.{fn.name} decl {fn.declId}\n"
  for proj in midnight.report.projections do
    manifest := manifest ++
      s!"projection {proj.parameter}.{proj.member} head {proj.headWord} as {proj.modelParam} ignored {proj.ignoredMembers}\n"
  for name in midnight.report.storageFields do
    manifest := manifest ++ s!"storage {name}\n"
  for o in midnight.report.opaqueMembers do
    manifest := manifest ++ s!"opaque {o.field}.{o.name} {o.solcType} word {o.wordOffset} byte {o.byteOffset}\n"
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/slice-report.txt" manifest
  IO.println manifest
