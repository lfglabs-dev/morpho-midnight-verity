import MorphoMidnight.Witness
import Lean.Data.Json

/-!
Compare `denoteScalarBody` on the imported Midnight model with the results
`forge` recorded from the original `updatePositionView`. Inputs live in
`test/vectors.json`. Solidity results live in `out/solidity-results.txt`.
-/

open Lean
open Compiler.CompilationModel.SoliditySlice

structure SliceVector where
  name : String
  credit : Nat
  pending : Nat
  lossFactor : Nat
  lastLoss : Nat
  lastAccrual : Nat
  timestamp : Nat
  maturity : Nat

def natField (obj : Json) (key : String) : Except String Nat := do
  let text ← obj.getObjValAs? String key
  let some n := text.toNat? | throw s!"{key} is not a nat"
  return n

def parseVector (v : Json) : Except String SliceVector := do
  return {
    name := ← v.getObjValAs? String "name"
    credit := ← natField v "credit"
    pending := ← natField v "pending"
    lossFactor := ← natField v "lossFactor"
    lastLoss := ← natField v "lastLoss"
    lastAccrual := ← natField v "lastAccrual"
    timestamp := ← natField v "timestamp"
    maturity := ← natField v "maturity"
  }

def parseResult (line : String) : Except String (String × Option (List Nat)) := do
  let parts := line.trimAscii.toString.splitOn " "
  match parts with
  | [name, "revert"] => return (name, none)
  | [name, "ok", a, b, c] =>
      let some na := a.toNat? | throw s!"bad {a}"
      let some nb := b.toNat? | throw s!"bad {b}"
      let some nc := c.toNat? | throw s!"bad {c}"
      return (name, some [na, nb, nc])
  | _ => throw s!"bad result line: {line}"

def compareResults : IO UInt32 := do
  let vectorsJson ← IO.FS.readFile "test/vectors.json"
  let vectors ← IO.ofExcept <| do
    let arr ← Json.parse vectorsJson
    let vs ← arr.getArr?
    vs.toList.mapM parseVector
  let solidityText ← IO.FS.readFile "out/solidity-results.txt"
  let mut solidity : List (String × Option (List Nat)) := []
  for line in solidityText.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    solidity := solidity.concat (← IO.ofExcept (parseResult line))
  if solidity.length != vectors.length then
    throw <| IO.userError s!"solidity produced {solidity.length} lines for {vectors.length} vectors"
  for (v, got) in vectors.zip solidity do
    if got.1 != v.name then
      throw <| IO.userError s!"order mismatch {v.name} vs {got.1}"
    let model := runWitness v.credit v.pending v.lossFactor v.lastLoss v.lastAccrual v.timestamp v.maturity
    unless model == got.2 do
      throw <| IO.userError s!"{v.name}: model {model} solidity {got.2}"
    IO.println s!"match {v.name}"
  return 0
