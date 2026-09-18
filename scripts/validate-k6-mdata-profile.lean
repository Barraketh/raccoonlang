import Lean

open Lean

private def values : Array DataValue := #[
  .ofString "",
  .ofString "true",
  .ofString "Lean.DataValue.ofNat 0",
  .ofString "quote: \" slash: \\ newline:\n scalar: λ",
  .ofBool false,
  .ofBool true,
  .ofName .anonymous,
  .ofName (.str .anonymous "1"),
  .ofName (.num .anonymous 1),
  .ofName (.str (.str .anonymous "a") "1"),
  .ofName (.num (.str .anonymous "a") 1),
  .ofNat 0,
  .ofNat 1,
  .ofNat (2 ^ 256),
  .ofInt 0,
  .ofInt (-1),
  .ofInt (Int.ofNat (2 ^ 256)),
  .ofSyntax .missing,
  .ofSyntax (.atom .none ""),
  .ofSyntax (.atom .none "true"),
  .ofSyntax (.node .none `collision #[.atom .none "a", .atom .none "b"])
]

private def names : Array Name := #[
  .anonymous,
  .str .anonymous "",
  .str .anonymous "1",
  .num .anonymous 1,
  .str (.str .anonymous "a") "1",
  .num (.str .anonymous "a") 1,
  .str .anonymous "a.b",
  .str .anonymous "quote\"slash\\",
  .str .anonymous "λ",
  .num (.num .anonymous 1) 2
]

private def canonical (map : KVMap) : List (String × String) :=
  List.mergeSort
    (map.entries.map fun (key, value) => (key.toString, reprStr value))
    fun left right => left.1 <= right.1

private def checkPairwise [BEq α] [Inhabited α]
    (label : String) (items : Array α) (encode : α → String) : IO Unit := do
  for left in [0:items.size] do
    for right in [0:items.size] do
      let sourceEqual := items[left]! == items[right]!
      let encodedEqual := encode items[left]! == encode items[right]!
      if sourceEqual != encodedEqual then
        throw <| IO.userError s!"{label} serialization collision at {left}/{right}: {encode items[left]!}"

def main : IO Unit := do
  checkPairwise "DataValue.reprStr" values reprStr
  checkPairwise "Name.toString" names Name.toString

  let forward := KVMap.empty |>.insert `z (.ofString "last") |>.insert `a (.ofNat 1)
  let reverse := KVMap.empty |>.insert `a (.ofNat 1) |>.insert `z (.ofString "last")
  unless canonical forward == canonical reverse do
    throw <| IO.userError "canonical metadata serialization depends on KVMap insertion order"

  let replaced := forward.insert `a (.ofNat 2)
  if canonical replaced == canonical forward then
    throw <| IO.userError "canonical metadata serialization lost a replaced value"

  IO.println s!"validated {values.size} DataValue and {names.size} Name adversarial cases"
