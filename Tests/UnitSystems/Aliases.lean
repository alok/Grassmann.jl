import Tests.UnitSystems.Systems

/-!
# UnitSystems: the system aliases

Against the `aliases` table of `oracle/golden/unitsystems/systems.json`
(`oracle/unitsystems/systems.jl:53-54`), which pins Julia's alternative
spellings from `initdata.jl:158` and `:162-165`. The golden has been generated
since the systems oracle was written but no test read it until now.

Julia aliases the `const`, not the name, so `unitname(SI)` is `"SI2019"`: the
golden's value for each alias is its **canonical** system's display name, and
that is what this suite checks both spellings against.

The `Sys`-index and `UnitSystem`-value aliases are `abbrev`s, so the equalities
below hold by `rfl` — they are checked at elaboration, and the golden then
independently pins that the canonical target is the one Julia chose.
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

-- The `Sys` aliases reduce to their canonical constructor.
example : Sys.SI = .SI2019 := rfl
example : Sys.MKS = .Metric := rfl
example : Sys.MetricEngineering = .Engineering := rfl
example : Sys.ME = .Engineering := rfl
example : Sys.GravitationalMetric = .Gravitational := rfl
example : Sys.GM = .Gravitational := rfl
example : Sys.CGS = .Gauss := rfl
example : Sys.CGSm = .EMU := rfl
example : Sys.CGSe = .ESU := rfl
example : Sys.HLU = .LorentzHeaviside := rfl
example : Sys.EnglishEngineering = .English := rfl
example : Sys.EE = .English := rfl
example : Sys.BritishGravitational = .British := rfl
example : Sys.BG = .British := rfl
example : Sys.EnglishUS = .Survey := rfl
example : Sys.AbsoluteEnglish = .FPS := rfl
example : Sys.AE = .FPS := rfl

-- `@[match_pattern]` means they may also appear on the left of a `match`.
example : Bool := match Sys.Gauss with | Sys.CGS => true | _ => false
example : (match Sys.Gauss with | Sys.CGS => true | _ => false) = true := rfl

-- The `UnitSystem`-valued aliases are the canonical systems, at any scalar.
example : (SI Num) = SI2019 Num := rfl
example : (MKS Num) = Metric Num := rfl
example : (ME Num) = Engineering Num := rfl
example : (GM Num) = Gravitational Num := rfl
example : (CGS Num) = Gauss Num := rfl
example : (CGSm Num) = EMU Num := rfl
example : (CGSe Num) = ESU Num := rfl
example : (HLU Num) = LorentzHeaviside Num := rfl
example : (EnglishEngineering Num) = English Num := rfl
example : (EE Num) = English Num := rfl
example : (BritishGravitational Num) = British Num := rfl
example : (BG Num) = British Num := rfl
example : (EnglishUS Num) = Survey Num := rfl
example : (AbsoluteEnglish Num) = FPS Num := rfl
example : (AE Num) = FPS Num := rfl
example : (MetricEngineering Num) = Engineering Num := rfl
example : (GravitationalMetric Num) = Gravitational Num := rfl

/-- Every alias identifier, paired with the golden key that names it. `IAU` is in
the golden but is not an alias here: Julia's `IAU = IAU☉` renames the display,
and this port already spells the constructor `IAU` and displays it `IAU☉`. -/
def aliasTable : List (String × Sys) :=
  [("SI", .SI), ("MKS", .MKS), ("MetricEngineering", .MetricEngineering), ("ME", .ME),
   ("GravitationalMetric", .GravitationalMetric), ("GM", .GM), ("CGS", .CGS), ("CGSm", .CGSm),
   ("CGSe", .CGSe), ("HLU", .HLU), ("EnglishEngineering", .EnglishEngineering), ("EE", .EE),
   ("BritishGravitational", .BritishGravitational), ("BG", .BG), ("EnglishUS", .EnglishUS),
   ("AbsoluteEnglish", .AbsoluteEnglish), ("AE", .AE), ("IAU", .IAU)]

/-- The alias table against Julia's. -/
def aliasesSuite : IO (Suite × Suite) := do
  let j ← loadJson "unitsystems/systems.json"
  let al := fld j "aliases"
  let mut s : Suite := { name := "system aliases" }
  let e : Suite := { name := "system aliases (bit-exact)" }
  -- every alias Julia defines is one we know, and no others
  let keys : List String := match al.getObj? with
    | .ok m => m.keys
    | .error _ => []
  s := s.check (keys.length == aliasTable.length) fun _ =>
    s!"golden has {keys.length} aliases, table has {aliasTable.length}"
  for k in keys do
    s := s.check (aliasTable.any (·.1 == k)) fun _ => s!"golden alias {k} is missing from the table"
  for (nm, u) in aliasTable do
    let want := str (fld al nm)
    -- the identifier's canonical display name is Julia's
    s := s.check (u.name == want) fun _ => s!"{nm}: identifier names {u.name}, Julia says {want}"
    -- and the string lookup agrees with the identifier
    match Sys.ofName? nm with
    | none => s := s.check false fun _ => s!"{nm}: ofName? does not know it"
    | some v => s := s.check (v == u) fun _ => s!"{nm}: ofName? gives {v.name}, identifier is {u.name}"
    -- the value-level alias is the canonical system: same eleven parameters
    s := s.check (params (u.sys Num) == params ((Sys.ofName? want).getD .Metric |>.sys Num)) fun _ =>
      s!"{nm}: parameters differ from {want}"
  return (s, e)

end Tests.UnitSystemsTests
