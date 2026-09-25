import JuliaBase.Float

/-!
# Minimal JSON writer for benchmark results

The bench executable deliberately avoids `import Lean` (its `Json` type would pull the whole
compiler into the binary), so results are serialized by hand. Floats use Julia's shortest
round-trip printing (`F64.showString`), which is valid JSON for finite values; non-finite
values become `null`.
-/

namespace Bench.Json

open JuliaBase

/-- A JSON value (only what the result files need). -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (x : Float)
  | nat (n : Nat)
  | str (s : String)
  | arr (xs : Array Value)
  | obj (kvs : Array (String × Value))
  deriving Inhabited

/-- Escape a string for a JSON string literal (quotes included). -/
def escape (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | '\r' => out ++ "\\r"
      | '\t' => out ++ "\\t"
      | c =>
        if c.toNat < 0x20 then
          let h := Nat.toDigits 16 c.toNat
          out ++ "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
        else out.push c
  return out.push '"'

/-- A JSON number for a float: shortest round-trip digits, `null` if not finite. -/
def floatLit (x : Float) : String :=
  if x.isFinite then F64.showString x else "null"

/-- Serialize with two-space indentation at the top level (one result per line). -/
partial def render : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num x => floatLit x
  | .nat n => toString n
  | .str s => escape s
  | .arr xs => "[" ++ ", ".intercalate (xs.toList.map render) ++ "]"
  | .obj kvs => "{" ++ ", ".intercalate (kvs.toList.map fun (k, v) => escape k ++ ": " ++ render v) ++ "}"

end Bench.Json
