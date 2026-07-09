import Grassmann.MV

namespace Grassmann.FixedKernelTests

private def maxAbsDiff (a b : DataArray) : Float :=
  (Array.range (min a.size b.size)).foldl
    (fun acc i =>
      let d := Float.abs (a.get! i - b.get! i)
      if d > acc then d else acc)
    0.0

private def basisArray (size index : Nat) : DataArray :=
  (DataArray.zeros size).set! index 1.0

private def maxBasisPairDiff (size : Nat)
    (reference candidate : DataArray → DataArray → DataArray) : Float :=
  (Array.range size).foldl (init := 0.0) fun acc i =>
    (Array.range size).foldl (init := acc) fun acc j =>
      let d := maxAbsDiff
        (reference (basisArray size i) (basisArray size j))
        (candidate (basisArray size i) (basisArray size j))
      if d > acc then d else acc

private def requireZero (label : String) (value : Float) : IO Unit :=
  unless value == 0.0 do
    throw <| IO.userError s!"{label}: maximum coefficient difference was {value}"

def run : IO Unit := do
  let r3Reference : DataArray → DataArray → DataArray :=
    MV.mulKernelEvenEven 3 EvenMV.Kernel.evenMulSignR3
  let pga3Reference : DataArray → DataArray → DataArray :=
    MV.mulKernelEvenEven 4 EvenMV.Kernel.evenMulSignPGA3
  requireZero "R3 straight-line kernel"
    (maxBasisPairDiff 4 r3Reference MV.mulKernelR3EvenEven)
  requireZero "R3 direct dispatch"
    (maxBasisPairDiff 4 r3Reference (MV.mulKernelDirect R3 .even .even))
  requireZero "PGA3 straight-line kernel"
    (maxBasisPairDiff 8 pga3Reference MV.mulKernelPGA3EvenEven)
  requireZero "PGA3 direct dispatch"
    (maxBasisPairDiff 8 pga3Reference (MV.mulKernelDirect PGA3 .even .even))
  let r3a := DataArray.ofArray #[1.25, -2.0, 0.75, 4.5]
  let r3b := DataArray.ofArray #[-0.5, 3.0, 2.25, -1.0]
  let pga3a := DataArray.ofArray #[1.25, -2.0, 0.75, 4.5, 3.0, -1.5, 2.0, 0.25]
  let pga3b := DataArray.ofArray #[-0.5, 3.0, 2.25, -1.0, 1.5, 0.5, -3.0, 4.0]
  requireZero "R3 mixed coefficients"
    (maxAbsDiff (r3Reference r3a r3b) (MV.mulKernelR3EvenEven r3a r3b))
  requireZero "PGA3 mixed coefficients"
    (maxAbsDiff (pga3Reference pga3a pga3b) (MV.mulKernelPGA3EvenEven pga3a pga3b))
  IO.println "fixed packed-kernel tests passed"

end Grassmann.FixedKernelTests

def main : IO Unit := Grassmann.FixedKernelTests.run
