/-
  Grassmann/StorageCompare.lean - Compare storage strategies for performance
-/

namespace StorageCompare

/-! ## Strategy 1: Function (Fin n → Float) -/

structure MVFun (n : Nat) where
  coeffs : Fin (2^n) → Float

def MVFun.add (a b : MVFun n) : MVFun n :=
  ⟨fun i => a.coeffs i + b.coeffs i⟩

def MVFun.dot (a b : MVFun n) : Float :=
  let rec go (i : Nat) (acc : Float) : Float :=
    if h : i < 2^n then
      go (i + 1) (acc + a.coeffs ⟨i, h⟩ * b.coeffs ⟨i, h⟩)
    else acc
  termination_by 2^n - i
  go 0 0

/-! ## Strategy 2: Array (dynamic size) -/

structure MVArr where
  coeffs : Array Float

def MVArr.add (a b : MVArr) : MVArr := Id.run do
  let size := min a.coeffs.size b.coeffs.size
  let mut result := Array.mkEmpty size
  for i in [:size] do
    result := result.push (a.coeffs[i]! + b.coeffs[i]!)
  return ⟨result⟩

def MVArr.dot (a b : MVArr) : Float := Id.run do
  let size := min a.coeffs.size b.coeffs.size
  let mut acc : Float := 0
  for i in [:size] do
    acc := acc + a.coeffs[i]! * b.coeffs[i]!
  return acc

/-! ## Strategy 3: Unboxed struct for n=2 (4 coefficients) -/

structure MV4 where
  c0 : Float
  c1 : Float
  c2 : Float
  c3 : Float

def MV4.add (a b : MV4) : MV4 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

def MV4.dot (a b : MV4) : Float :=
  a.c0 * b.c0 + a.c1 * b.c1 + a.c2 * b.c2 + a.c3 * b.c3

/-! ## Strategy 4: Unboxed struct for n=3 (8 coefficients) -/

structure MV8 where
  c0 : Float
  c1 : Float
  c2 : Float
  c3 : Float
  c4 : Float
  c5 : Float
  c6 : Float
  c7 : Float

def MV8.add (a b : MV8) : MV8 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3,
   a.c4 + b.c4, a.c5 + b.c5, a.c6 + b.c6, a.c7 + b.c7⟩

def MV8.dot (a b : MV8) : Float :=
  a.c0*b.c0 + a.c1*b.c1 + a.c2*b.c2 + a.c3*b.c3 +
  a.c4*b.c4 + a.c5*b.c5 + a.c6*b.c6 + a.c7*b.c7

/-! ## Test functions for IR inspection -/

@[noinline] def testFunAdd2 (a b : MVFun 2) : MVFun 2 := MVFun.add a b
@[noinline] def testFunDot2 (a b : MVFun 2) : Float := MVFun.dot a b
@[noinline] def testArrAdd (a b : MVArr) : MVArr := MVArr.add a b
@[noinline] def testArrDot (a b : MVArr) : Float := MVArr.dot a b
@[noinline] def testMV4Add (a b : MV4) : MV4 := MV4.add a b
@[noinline] def testMV4Dot (a b : MV4) : Float := MV4.dot a b
@[noinline] def testMV8Add (a b : MV8) : MV8 := MV8.add a b
@[noinline] def testMV8Dot (a b : MV8) : Float := MV8.dot a b

end StorageCompare
