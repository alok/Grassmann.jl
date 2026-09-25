import FlowGeometry.Param

/-!
# Profiles and airfoils

Julia's `Profile{P}` (FlowGeometry.jl `src/profiles.jl:26`) is an abstract type whose concrete
subtypes carry every shape parameter and the sample count `P` as type parameters, and
`Airfoil{p}` (`src/airfoils.jl:15`) combines profiles. Floats are not usable type indices in Lean,
so both are ordinary runtime data here, one constructor per Julia type, with the parameters in
Julia's order. `UpperArc`/`LowerArc` wrap an airfoil *as* a profile (`airfoils.jl:29-42`), which
makes the two types mutually recursive.

`Joukowski{R,f,g,b,p}` is an `Airfoil` in Julia too, but it has neither `upper` nor `lower` (only
`complex`), so the port keeps it apart (`Joukowski`, `FlowGeometry.Airfoil`), and `Airfoil`
holds the four surface constructions, which all have both surfaces.

The Julia type strings (`typeString`) are part of the oracle: `NACA"2412"` is
`American{NACA4{24, 150}, ClarkY{12, 0.21, 150}, 298}`.
-/

namespace FlowGeometry

open JuliaBase

mutual

/-- A 1-D profile over the chord `x ∈ [0, 1]` sampled at `P` points (Julia `Profile{P}`): a camber
line or a thickness distribution, or a surface of an airfoil. -/
inductive Profile where
  /-- Julia `FlatPlate{p}` (`profiles.jl:57-66`): `y ≡ 0`. -/
  | flatPlate (p : Nat)
  /-- Julia `ParabolicArc{t,p}` (`profiles.jl:70-77`): `(t/25)·x(1-x)`, `t` in percent. -/
  | parabolicArc (t : Num) (p : Nat)
  /-- Julia `CircularArc{t,p}` (`profiles.jl:81-102`): the circular arc of height `t` percent. -/
  | circularArc (t : Num) (p : Nat)
  /-- Julia `ClarkY{t,te,p}` (`profiles.jl:107-127`): the NACA 4-digit thickness polynomial,
  `t` and trailing-edge parameter `te` in percent. -/
  | clarkY (t te : Num) (p : Nat)
  /-- Julia `Thickness{t,x,te,p}` (`profiles.jl:132-148`): a 4-digit-style thickness polynomial
  with its maximum at `x/10`, fitted by a 5×5 solve. -/
  | thickness (t x te : Num) (p : Nat)
  /-- Julia `Modified{t,m,te,p}` (`profiles.jl:153-185`): the NACA modified 4-digit thickness,
  `m` = the two digits "IM" (leading-edge radius index, maximum-thickness position). -/
  | modified (t m te : Num) (p : Nat)
  /-- Julia `NACA4{n,p}` (`profiles.jl:190-219`): the 4-digit camber line, `n` = digits "MP". -/
  | naca4 (n : Nat) (p : Nat)
  /-- Julia `NACA5{n,p}` (`profiles.jl:224-268`): the 5-digit camber line, `n` = digits "CPR". -/
  | naca5 (n : Nat) (p : Nat)
  /-- Julia `NACA6{c,n,p}` (`profiles.jl:273-317`): a sum of `n` 6-series mean lines with chord
  loadings `a` and design lift coefficients `cl`; `c = 10·sum(cl)` is only a label. -/
  | naca6 (a cl : FloatArray) (p : Nat)
  /-- Julia `NACA6A{c,p}` (`profiles.jl:322-338`): the 6A-series mean line of design lift `c/10`. -/
  | naca6A (c : Num) (p : Nat)
  /-- Julia `UpperArc{A,p}` (`airfoils.jl:29-42`): the upper surface of an airfoil as a profile. -/
  | upperArc (a : Airfoil)
  /-- Julia `LowerArc{A,p}`: the lower surface of an airfoil as a profile. -/
  | lowerArc (a : Airfoil)

/-- An airfoil built from profiles (Julia `Airfoil{p}` with an upper and a lower surface,
`airfoils.jl:65-146`). -/
inductive Airfoil where
  /-- Julia `American{C,T,P}` (`airfoils.jl:131-146`): thickness `t` laid off perpendicular to
  the camber line `c` (the standard NACA construction). -/
  | american (c t : Profile)
  /-- Julia `British{C,T,P}` (`airfoils.jl:108-122`): thickness perpendicular to the chord. -/
  | british (c t : Profile)
  /-- Julia `SymmetricArc{S,P}` (`airfoils.jl:72-81`): `x ± i·s(x)`. -/
  | symmetric (s : Profile)
  /-- Julia `DoubleArc{U,L,P}` (`airfoils.jl:90-99`): independent upper and lower profiles. -/
  | double (u l : Profile)

end

instance : Inhabited Profile := ⟨.flatPlate 0⟩
instance : Inhabited Airfoil := ⟨.symmetric default⟩

/-- Julia `Joukowski{R,f,g,b,p}` (`airfoils.jl:171-183`): the image of the circle of radius `R`
centred at `-f + ig` under `z ↦ z + b²/z`, sampled at `2p-1` angles. -/
structure Joukowski where
  /-- circle radius -/
  R : Num
  /-- the centre is `-f + i·g` -/
  f : Num
  /-- the centre is `-f + i·g` -/
  g : Num
  /-- the map is `z + b²/z` -/
  b : Num
  /-- Julia's point parameter (`2p-1` samples) -/
  p : Nat
  deriving Inhabited

mutual

/-- Julia's `P` of a profile: the number of samples (`Profile{P}`). For `UpperArc`/`LowerArc`
it is the length of the wrapped airfoil's surface (`airfoils.jl:36`). -/
def Profile.samples : Profile → Nat
  | .flatPlate p | .parabolicArc _ p | .circularArc _ p | .clarkY _ _ p | .thickness _ _ _ p
  | .modified _ _ _ p | .naca4 _ p | .naca5 _ p | .naca6 _ _ p | .naca6A _ p => p
  | .upperArc a => a.upperSamples
  | .lowerArc a => a.lowerSamples

/-- The number of samples of the upper surface (`length(upper(a))`). -/
def Airfoil.upperSamples : Airfoil → Nat
  | .american c _ | .british c _ => c.samples
  | .symmetric s => s.samples
  | .double u _ => u.samples

/-- The number of samples of the lower surface (`length(lower(a))`). -/
def Airfoil.lowerSamples : Airfoil → Nat
  | .american c _ | .british c _ => c.samples
  | .symmetric s => s.samples
  | .double _ l => l.samples

end

/-- Julia's `p` of an airfoil (`Airfoil{p}`): `2P-2` for the constructions from one sample count
(`airfoils.jl:77, 115, 138`), `P+Q-2` for `DoubleArc` (`airfoils.jl:96`). It is the number of
distinct outline points (`points`). -/
def Airfoil.samples : Airfoil → Nat
  | .american c _ | .british c _ => 2 * c.samples - 2
  | .symmetric s => 2 * s.samples - 2
  | .double u l => u.samples + l.samples - 2

/-- Julia `typeof(t)` printed: `NACA6{2.0, 1, 150}`-style type strings. -/
def typeParams (name : String) (ps : List String) : String :=
  name ++ "{" ++ ", ".intercalate ps ++ "}"

/-- Julia `10sum(Cl)` (the `c` of `NACA6{c,n,p}`, `profiles.jl:276`): StaticVectors' left-to-right
sum, times `10`. -/
def naca6Label (cl : FloatArray) : Float :=
  if cl.size == 0 then 0
  else 10 * (List.range (cl.size - 1)).foldl (fun acc i => acc + cl.get! (i + 1)) (cl.get! 0)

mutual

/-- Julia `string(typeof(p))` of a profile. -/
def Profile.typeString : Profile → String
  | .flatPlate p => typeParams "FlatPlate" [toString p]
  | .parabolicArc t p => typeParams "ParabolicArc" [t.jshow, toString p]
  | .circularArc t p => typeParams "CircularArc" [t.jshow, toString p]
  | .clarkY t te p => typeParams "ClarkY" [t.jshow, te.jshow, toString p]
  | .thickness t x te p => typeParams "Thickness" [t.jshow, x.jshow, te.jshow, toString p]
  | .modified t m te p => typeParams "Modified" [t.jshow, m.jshow, te.jshow, toString p]
  | .naca4 n p => typeParams "NACA4" [toString n, toString p]
  | .naca5 n p => typeParams "NACA5" [toString n, toString p]
  | .naca6 _ cl p => typeParams "NACA6" [F64.showString (naca6Label cl), toString cl.size, toString p]
  | .naca6A c p => typeParams "NACA6A" [c.jshow, toString p]
  | .upperArc a => typeParams "UpperArc" [a.typeString, toString a.upperSamples]
  | .lowerArc a => typeParams "LowerArc" [a.typeString, toString a.lowerSamples]

/-- Julia `string(typeof(a))` of an airfoil. -/
def Airfoil.typeString : Airfoil → String
  | .american c t => typeParams "American" [c.typeString, t.typeString, toString (2 * c.samples - 2)]
  | .british c t => typeParams "British" [c.typeString, t.typeString, toString (2 * c.samples - 2)]
  | .symmetric s => typeParams "SymmetricArc" [s.typeString, toString (2 * s.samples - 2)]
  | .double u l => typeParams "DoubleArc" [u.typeString, l.typeString, toString (u.samples + l.samples - 2)]

end

/-- Julia `string(typeof(j))` of a Joukowski airfoil. -/
def Joukowski.typeString (j : Joukowski) : String :=
  typeParams "Joukowski" [j.R.jshow, j.f.jshow, j.g.jshow, j.b.jshow, toString j.p]

instance : ToString Profile := ⟨Profile.typeString⟩
instance : ToString Airfoil := ⟨Airfoil.typeString⟩
instance : ToString Joukowski := ⟨Joukowski.typeString⟩

/-! ## Julia's default-parameter constructors -/

namespace Profile

/-- Julia `ParabolicArc{p}()` (`profiles.jl:72`): `t = 6`. -/
def parabolicArcDefault (p : Nat) : Profile := .parabolicArc 6 p
/-- Julia `CircularArc{p}()` (`profiles.jl:83`): `t = 6`. -/
def circularArcDefault (p : Nat) : Profile := .circularArc 6 p
/-- Julia `ClarkY{t,p}()` (`profiles.jl:109`): `te = 0.21`. -/
def clarkYDefault (t : Num) (p : Nat) : Profile := .clarkY t 0.21 p
/-- Julia `Thickness{t,x,p}()` (`profiles.jl:134`): `te = t/100`. -/
def thicknessX (t x : Num) (p : Nat) : Profile := .thickness t x (.float (t.toFloat / 100)) p
/-- Julia `Thickness{t,p}()` (`profiles.jl:135`): `x = 3`, `te = t/100`. -/
def thicknessDefault (t : Num) (p : Nat) : Profile := thicknessX t 3 p
/-- Julia `Modified{t,m,p}()` (`profiles.jl:155`): `te = 0.2`. -/
def modifiedM (t m : Num) (p : Nat) : Profile := .modified t m 0.2 p
/-- Julia `Modified{t,p}()` (`profiles.jl:156`): `m = 63`, `te = 0.2`. -/
def modifiedDefault (t : Num) (p : Nat) : Profile := modifiedM t 63 p
/-- Julia `NACA6{c,p}()` (`profiles.jl:277`): one mean line with `a = 1`, `Cl = c/10`. -/
def naca6Default (c : Num) (p : Nat) : Profile :=
  .naca6 (FloatArray.empty.push 1) (FloatArray.empty.push (c.toFloat / 10)) p

end Profile

end FlowGeometry
