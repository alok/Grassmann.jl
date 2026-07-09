/-
  Grassmann/SignTablesCore.lean - Proof-free cached sign tables

  This module contains only the signature-specific lookup tables needed by the
  packed runtime.  Dense `Multivector` integration remains in `SignTables` so
  importing `MV` does not transitively import proof-oriented dense machinery.
-/
import Grassmann.Parity

namespace Grassmann

/-! ## Precomputed Sign Tables for Standard Signatures -/

/-- Precomputed sign table for R2 (4×4 = 16 entries). -/
def R2SignTable : SignTable 2 := buildSignTable R2

/-- Precomputed sign table for R3 (8×8 = 64 entries). -/
def R3SignTable : SignTable 3 := buildSignTable R3

/-- Precomputed sign table for R4 (16×16 = 256 entries). -/
def R4SignTable : SignTable 4 := buildSignTable R4

/-- Precomputed sign table for STA Cl(1,3) (16×16 = 256 entries). -/
def STASignTable : SignTable 4 := buildSignTable STA

/-- Precomputed sign table for PGA3 Cl(3,0,1) (16×16 = 256 entries). -/
def PGA3SignTable : SignTable 4 := buildSignTable PGA3

/-- Precomputed sign table for CGA3 Cl(4,1) (32×32 = 1024 entries). -/
def CGA3SignTable : SignTable 5 := buildSignTable CGA3

/-! ## Cached Sign Table Selection -/

/-- Lookup a cached sign table for common `Signature`s. -/
@[inline]
def cachedSignTable {n : ℕ} (sig : Signature n) : Option (SignTable n) :=
  match n with
  | 2 => if sig == R2 then some R2SignTable else none
  | 3 => if sig == R3 then some R3SignTable else none
  | 4 =>
      if sig == R4 then some R4SignTable
      else if sig == STA then some STASignTable
      else if sig == PGA3 then some PGA3SignTable
      else none
  | 5 => if sig == CGA3 then some CGA3SignTable else none
  | _ => none

end Grassmann
