/-
Dense eigen-decomposition of real square matrices (`Float`), replacing the
LAPACK calls of Julia's `eigen(Matrix(X))` (Grassmann.jl `src/forms.jl:1374-1439`;
port-notes/grassmann-forms.md §4.10, §8.2).

Julia's `LinearAlgebra.eigen` of a real matrix dispatches on symmetry:

* symmetric (`issymmetric`): `eigen(Symmetric(A))` (LAPACK `syevr`): real
  eigenvalues in ascending order, orthonormal eigenvectors. Here: Householder
  tridiagonalisation and the implicit QL iteration (EISPACK `tred2`/`tql2`, as in
  the public-domain JAMA), sorted ascending;
* otherwise LAPACK `geev`: Hessenberg reduction and the Francis double-shift QR
  iteration, eigenvectors from the Schur form, each normalised to unit 2-norm;
  Julia then sorts by `(real, imag)` (`eigsortby`). Here: EISPACK
  `orthes`/`hqr2` (JAMA), with the same normalisation and ordering, and complex
  eigenvectors rotated so that their largest component is real (LAPACK's
  convention).

The eigenvalues agree with LAPACK's to rounding (the algorithms are the same
family); eigenvectors agree up to the sign/phase LAPACK leaves free, so the tests
compare residuals `‖Av - λv‖`. Julia's result is real-typed when every
eigenvalue is real (`geev`'s imaginary parts all zero), complex otherwise
(`Forms.Spectrum`).

This is setup code for small matrices (it runs once per `eigen` call on an
`n × n` matrix with `n` up to a few dozen): the iterations are written with
mutable locals over row-major `FloatArray`s, not as the tail-recursive kernels
of the hot paths.
-/
import Grassmann.Forms.Roots

namespace Grassmann.Forms.Eigen

open StaticVectors JuliaBase

/-- `2⁻⁵²`, the relative precision the EISPACK iterations test against. -/
def epsilon : Float := Float.ofBits 0x3CB0000000000000

/-- Row-major read `A[i][j]` of an `n × n` buffer. -/
@[inline] def rd (a : FloatArray) (n i j : Nat) : Float := a.get! (i * n + j)

/-- Row-major write `A[i][j] := x`. -/
@[inline] def wr (a : FloatArray) (n i j : Nat) (x : Float) : FloatArray := a.set! (i * n + j) x

/-- Julia `issymmetric(A)` on a row-major buffer (exact equality). -/
def isSymmetric (a : FloatArray) (n : Nat) : Bool :=
  (List.range n).all fun i => (List.range i).all fun j => rd a n i j == rd a n j i

/-- Symmetric eigen-decomposition (EISPACK `tred2` + `tql2`): eigenvalues
ascending and the orthonormal eigenvectors as the columns of a row-major
buffer. -/
def symmetric (A : FloatArray) (n : Nat) : FloatArray × FloatArray := Id.run do
  if n == 0 then return (.empty, .empty)
  let mut V := A
  let mut d : FloatArray := FloatArray.mk (Array.replicate n 0)
  let mut e : FloatArray := FloatArray.mk (Array.replicate n 0)
  -- tred2: Householder reduction to tridiagonal form
  for j in [0:n] do d := d.set! j (rd V n (n - 1) j)
  for i' in [0:n - 1] do
    let i := n - 1 - i'
    let mut scale : Float := 0
    let mut h : Float := 0
    for k in [0:i] do scale := scale + (d.get! k).abs
    if scale == 0 then
      e := e.set! i (d.get! (i - 1))
      for j in [0:i] do
        d := d.set! j (rd V n (i - 1) j)
        V := wr V n i j 0
        V := wr V n j i 0
    else
      for k in [0:i] do
        d := d.set! k (d.get! k / scale)
        h := h + d.get! k * d.get! k
      let mut f := d.get! (i - 1)
      let mut g := Float.sqrt h
      if f > 0 then g := -g
      e := e.set! i (scale * g)
      h := h - f * g
      d := d.set! (i - 1) (f - g)
      for j in [0:i] do e := e.set! j 0
      for j in [0:i] do
        f := d.get! j
        V := wr V n j i f
        g := e.get! j + rd V n j j * f
        for k in [j + 1:i] do
          g := g + rd V n k j * d.get! k
          e := e.set! k (e.get! k + rd V n k j * f)
        e := e.set! j g
      f := 0
      for j in [0:i] do
        e := e.set! j (e.get! j / h)
        f := f + e.get! j * d.get! j
      let hh := f / (h + h)
      for j in [0:i] do e := e.set! j (e.get! j - hh * d.get! j)
      for j in [0:i] do
        f := d.get! j
        g := e.get! j
        for k in [j:i] do
          V := wr V n k j (rd V n k j - (f * e.get! k + g * d.get! k))
        d := d.set! j (rd V n (i - 1) j)
        V := wr V n i j 0
    d := d.set! i h
  -- accumulate transformations
  for i in [0:n - 1] do
    V := wr V n (n - 1) i (rd V n i i)
    V := wr V n i i 1
    let h := d.get! (i + 1)
    if h != 0 then
      for k in [0:i + 1] do d := d.set! k (rd V n k (i + 1) / h)
      for j in [0:i + 1] do
        let mut g : Float := 0
        for k in [0:i + 1] do g := g + rd V n k (i + 1) * rd V n k j
        for k in [0:i + 1] do V := wr V n k j (rd V n k j - g * d.get! k)
    for k in [0:i + 1] do V := wr V n k (i + 1) 0
  for j in [0:n] do
    d := d.set! j (rd V n (n - 1) j)
    V := wr V n (n - 1) j 0
  V := wr V n (n - 1) (n - 1) 1
  e := e.set! 0 0
  -- tql2: implicit QL on the tridiagonal matrix
  for i in [1:n] do e := e.set! (i - 1) (e.get! i)
  e := e.set! (n - 1) 0
  let mut f : Float := 0
  let mut tst1 : Float := 0
  for l in [0:n] do
    tst1 := F64.max tst1 ((d.get! l).abs + (e.get! l).abs)
    let mut m := l
    while m < n do
      if (e.get! m).abs ≤ epsilon * tst1 then break
      m := m + 1
    if m > l then
      let mut iter := 0
      repeat
        iter := iter + 1
        let mut g := d.get! l
        let mut p := (d.get! (l + 1) - g) / (2 * e.get! l)
        let mut r := F64.hypot p 1
        if p < 0 then r := -r
        d := d.set! l (e.get! l / (p + r))
        d := d.set! (l + 1) (e.get! l * (p + r))
        let dl1 := d.get! (l + 1)
        let mut h := g - d.get! l
        for i in [l + 2:n] do d := d.set! i (d.get! i - h)
        f := f + h
        p := d.get! m
        let mut c : Float := 1
        let mut c2 := c
        let mut c3 := c
        let el1 := e.get! (l + 1)
        let mut s : Float := 0
        let mut s2 : Float := 0
        for i' in [0:m - l] do
          let i := m - 1 - i'
          c3 := c2
          c2 := c
          s2 := s
          g := c * e.get! i
          h := c * p
          r := F64.hypot p (e.get! i)
          e := e.set! (i + 1) (s * r)
          s := e.get! i / r
          c := p / r
          p := c * d.get! i - s * g
          d := d.set! (i + 1) (h + s * (c * g + s * d.get! i))
          for k in [0:n] do
            h := rd V n k (i + 1)
            V := wr V n k (i + 1) (s * rd V n k i + c * h)
            V := wr V n k i (c * rd V n k i - s * h)
        p := -s * s2 * c3 * el1 * e.get! l / dl1
        e := e.set! l (s * p)
        d := d.set! l (c * p)
        if !((e.get! l).abs > epsilon * tst1) || iter > 60 then break
    d := d.set! l (d.get! l + f)
    e := e.set! l 0
  -- sort ascending (selection sort, as JAMA)
  for i in [0:n - 1] do
    let mut k := i
    let mut p := d.get! i
    for j in [i + 1:n] do
      if d.get! j < p then
        k := j
        p := d.get! j
    if k != i then
      d := d.set! k (d.get! i)
      d := d.set! i p
      for j in [0:n] do
        let t := rd V n j i
        V := wr V n j i (rd V n j k)
        V := wr V n j k t
  return (d, V)

/-- EISPACK complex division `(xr + i xi) / (yr + i yi)` (Smith's algorithm, JAMA `cdiv`). -/
@[inline] def cdiv (xr xi yr yi : Float) : Float × Float :=
  if yr.abs > yi.abs then
    let r := yi / yr
    let d := yr + r * yi
    ((xr + r * xi) / d, (xi - r * xr) / d)
  else
    let r := yr / yi
    let d := yi + r * yr
    ((r * xr + xi) / d, (r * xi - xr) / d)

/-- Reduction to upper Hessenberg form by orthogonal similarity (EISPACK
`orthes`): returns `(H, V)` with `A = V H Vᵀ`, row-major. -/
def orthes (A : FloatArray) (n : Nat) : FloatArray × FloatArray := Id.run do
  let mut H := A
  let mut ort : FloatArray := FloatArray.mk (Array.replicate n 0)
  let high := n - 1
  for m in [1:high] do
    let mut scale : Float := 0
    for i in [m:high + 1] do scale := scale + (rd H n i (m - 1)).abs
    if scale != 0 then
      let mut h : Float := 0
      for i' in [0:high + 1 - m] do
        let i := high - i'
        ort := ort.set! i (rd H n i (m - 1) / scale)
        h := h + ort.get! i * ort.get! i
      let mut g := Float.sqrt h
      if ort.get! m > 0 then g := -g
      h := h - ort.get! m * g
      ort := ort.set! m (ort.get! m - g)
      for j in [m:n] do
        let mut f : Float := 0
        for i' in [0:high + 1 - m] do
          let i := high - i'
          f := f + ort.get! i * rd H n i j
        f := f / h
        for i in [m:high + 1] do H := wr H n i j (rd H n i j - f * ort.get! i)
      for i in [0:high + 1] do
        let mut f : Float := 0
        for j' in [0:high + 1 - m] do
          let j := high - j'
          f := f + ort.get! j * rd H n i j
        f := f / h
        for j in [m:high + 1] do H := wr H n i j (rd H n i j - f * ort.get! j)
      ort := ort.set! m (scale * ort.get! m)
      H := wr H n m (m - 1) (scale * g)
  let mut V : FloatArray := FloatArray.mk (Array.replicate (n * n) 0)
  for i in [0:n] do V := wr V n i i 1
  for m' in [0:high - 1] do
    let m := high - 1 - m'
    if m ≥ 1 && rd H n m (m - 1) != 0 then
      for i in [m + 1:high + 1] do ort := ort.set! i (rd H n i (m - 1))
      for j in [m:high + 1] do
        let mut g : Float := 0
        for i in [m:high + 1] do g := g + ort.get! i * rd V n i j
        g := (g / ort.get! m) / rd H n m (m - 1)
        for i in [m:high + 1] do V := wr V n i j (rd V n i j + g * ort.get! i)
  return (H, V)

/-- The real Schur iteration and eigenvector back-substitution (EISPACK `hqr2`)
on a Hessenberg `H` with accumulated transformations `V`: the eigenvalues
`(d, e)` (real and imaginary parts; a complex pair has `e > 0` first) and the
eigenvectors in real form (a complex pair `a ± bi` at `j, j+1` has the
eigenvector `V[:,j] ± i V[:,j+1]`). -/
def hqr2 (H0 V0 : FloatArray) (nn : Nat) : FloatArray × FloatArray × FloatArray := Id.run do
  let mut H := H0
  let mut V := V0
  let mut d : FloatArray := FloatArray.mk (Array.replicate nn 0)
  let mut e : FloatArray := FloatArray.mk (Array.replicate nn 0)
  if nn == 0 then return (d, e, V)
  let N := nn
  let h := fun (a : FloatArray) (i j : Int) => rd a N i.toNat j.toNat
  let hs := fun (a : FloatArray) (i j : Int) (x : Float) => wr a N i.toNat j.toNat x
  let mut n : Int := nn - 1
  let low : Int := 0
  let high : Int := nn - 1
  let mut exshift : Float := 0
  let mut p : Float := 0
  let mut q : Float := 0
  let mut r : Float := 0
  let mut s : Float := 0
  let mut z : Float := 0
  let mut w : Float := 0
  let mut x : Float := 0
  let mut y : Float := 0
  let mut norm : Float := 0
  for i in [0:nn] do
    for j in [(if i ≥ 1 then i - 1 else 0):nn] do
      norm := norm + (rd H N i j).abs
  let mut iter := 0
  let mut total := 0
  while n ≥ low do
    total := total + 1
    if total > 100 * nn + 100 then break
    let mut l := n
    while l > low do
      s := (h H (l - 1) (l - 1)).abs + (h H l l).abs
      if s == 0 then s := norm
      if (h H l (l - 1)).abs < epsilon * s then break
      l := l - 1
    if l == n then
      H := hs H n n (h H n n + exshift)
      d := d.set! n.toNat (h H n n)
      e := e.set! n.toNat 0
      n := n - 1
      iter := 0
    else if l == n - 1 then
      w := h H n (n - 1) * h H (n - 1) n
      p := (h H (n - 1) (n - 1) - h H n n) / 2
      q := p * p + w
      z := Float.sqrt q.abs
      H := hs H n n (h H n n + exshift)
      H := hs H (n - 1) (n - 1) (h H (n - 1) (n - 1) + exshift)
      x := h H n n
      if q ≥ 0 then
        z := if p ≥ 0 then p + z else p - z
        d := d.set! (n - 1).toNat (x + z)
        d := d.set! n.toNat (d.get! (n - 1).toNat)
        if z != 0 then d := d.set! n.toNat (x - w / z)
        e := e.set! (n - 1).toNat 0
        e := e.set! n.toNat 0
        x := h H n (n - 1)
        s := x.abs + z.abs
        p := x / s
        q := z / s
        r := Float.sqrt (p * p + q * q)
        p := p / r
        q := q / r
        for j in [(n - 1).toNat:nn] do
          z := h H (n - 1) j
          H := hs H (n - 1) j (q * z + p * h H n j)
          H := hs H n j (q * h H n j - p * z)
        for i in [0:n.toNat + 1] do
          z := h H i (n - 1)
          H := hs H i (n - 1) (q * z + p * h H i n)
          H := hs H i n (q * h H i n - p * z)
        for i in [low.toNat:high.toNat + 1] do
          z := h V i (n - 1)
          V := hs V i (n - 1) (q * z + p * h V i n)
          V := hs V i n (q * h V i n - p * z)
      else
        d := d.set! (n - 1).toNat (x + p)
        d := d.set! n.toNat (x + p)
        e := e.set! (n - 1).toNat z
        e := e.set! n.toNat (-z)
      n := n - 2
      iter := 0
    else
      x := h H n n
      y := 0
      w := 0
      if l < n then
        y := h H (n - 1) (n - 1)
        w := h H n (n - 1) * h H (n - 1) n
      if iter == 10 then
        exshift := exshift + x
        for i in [low.toNat:n.toNat + 1] do H := hs H i i (h H i i - x)
        s := (h H n (n - 1)).abs + (h H (n - 1) (n - 2)).abs
        x := 0.75 * s
        y := x
        w := -0.4375 * s * s
      if iter == 30 then
        s := (y - x) / 2
        s := s * s + w
        if s > 0 then
          s := Float.sqrt s
          if y < x then s := -s
          s := x - w / ((y - x) / 2 + s)
          for i in [low.toNat:n.toNat + 1] do H := hs H i i (h H i i - s)
          exshift := exshift + s
          x := 0.964
          y := x
          w := x
      iter := iter + 1
      let mut m := n - 2
      while m ≥ l do
        z := h H m m
        r := x - z
        s := y - z
        p := (r * s - w) / h H (m + 1) m + h H m (m + 1)
        q := h H (m + 1) (m + 1) - z - r - s
        r := h H (m + 2) (m + 1)
        s := p.abs + q.abs + r.abs
        p := p / s
        q := q / s
        r := r / s
        if m == l then break
        if (h H m (m - 1)).abs * (q.abs + r.abs) <
            epsilon * (p.abs * ((h H (m - 1) (m - 1)).abs + z.abs + (h H (m + 1) (m + 1)).abs)) then
          break
        m := m - 1
      for i in [(m + 2).toNat:n.toNat + 1] do
        H := hs H i (i - 2) 0
        if (i : Int) > m + 2 then H := hs H i (i - 3) 0
      for k in [m.toNat:n.toNat] do
        let notlast := (k : Int) != n - 1
        let mut skip := false
        if (k : Int) != m then
          p := h H k (k - 1)
          q := h H (k + 1) (k - 1)
          r := if notlast then h H (k + 2) (k - 1) else 0
          x := p.abs + q.abs + r.abs
          if x == 0 then skip := true
          else
            p := p / x
            q := q / x
            r := r / x
        if !skip then
          s := Float.sqrt (p * p + q * q + r * r)
          if p < 0 then s := -s
          if s != 0 then
            if (k : Int) != m then H := hs H k (k - 1) (-s * x)
            else if l != m then H := hs H k (k - 1) (-(h H k (k - 1)))
            p := p + s
            x := p / s
            y := q / s
            z := r / s
            q := q / p
            r := r / p
            for j in [k:nn] do
              p := h H k j + q * h H (k + 1) j
              if notlast then
                p := p + r * h H (k + 2) j
                H := hs H (k + 2) j (h H (k + 2) j - p * z)
              H := hs H k j (h H k j - p * x)
              H := hs H (k + 1) j (h H (k + 1) j - p * y)
            for i in [0:(min n.toNat (k + 3)) + 1] do
              p := x * h H i k + y * h H i (k + 1)
              if notlast then
                p := p + z * h H i (k + 2)
                H := hs H i (k + 2) (h H i (k + 2) - p * r)
              H := hs H i k (h H i k - p)
              H := hs H i (k + 1) (h H i (k + 1) - p * q)
            for i in [low.toNat:high.toNat + 1] do
              p := x * h V i k + y * h V i (k + 1)
              if notlast then
                p := p + z * h V i (k + 2)
                V := hs V i (k + 2) (h V i (k + 2) - p * r)
              V := hs V i k (h V i k - p)
              V := hs V i (k + 1) (h V i (k + 1) - p * q)
  -- back-substitution
  if norm == 0 then return (d, e, V)
  for n' in [0:nn] do
    let nb : Int := nn - 1 - n'
    p := d.get! nb.toNat
    q := e.get! nb.toNat
    if q == 0 then
      let mut l := nb
      H := hs H nb nb 1
      for i' in [0:nb.toNat] do
        let i : Int := nb - 1 - i'
        w := h H i i - p
        r := 0
        for j in [l.toNat:nb.toNat + 1] do r := r + h H i j * h H j nb
        if e.get! i.toNat < 0 then
          z := w
          s := r
        else
          l := i
          if e.get! i.toNat == 0 then
            if w != 0 then H := hs H i nb (-r / w)
            else H := hs H i nb (-r / (epsilon * norm))
          else
            x := h H i (i + 1)
            y := h H (i + 1) i
            q := (d.get! i.toNat - p) * (d.get! i.toNat - p) + e.get! i.toNat * e.get! i.toNat
            let t := (x * s - z * r) / q
            H := hs H i nb t
            if x.abs > z.abs then H := hs H (i + 1) nb ((-r - w * t) / x)
            else H := hs H (i + 1) nb ((-s - y * t) / z)
          let t := (h H i nb).abs
          if (epsilon * t) * t > 1 then
            for j in [i.toNat:nb.toNat + 1] do H := hs H j nb (h H j nb / t)
    else if q < 0 then
      let mut l := nb - 1
      if (h H nb (nb - 1)).abs > (h H (nb - 1) nb).abs then
        H := hs H (nb - 1) (nb - 1) (q / h H nb (nb - 1))
        H := hs H (nb - 1) nb (-(h H nb nb - p) / h H nb (nb - 1))
      else
        let (cr, ci) := cdiv 0 (-(h H (nb - 1) nb)) (h H (nb - 1) (nb - 1) - p) q
        H := hs H (nb - 1) (nb - 1) cr
        H := hs H (nb - 1) nb ci
      H := hs H nb (nb - 1) 0
      H := hs H nb nb 1
      for i' in [0:(nb - 1).toNat] do
        let i : Int := nb - 2 - i'
        let mut ra : Float := 0
        let mut sa : Float := 0
        for j in [l.toNat:nb.toNat + 1] do
          ra := ra + h H i j * h H j (nb - 1)
          sa := sa + h H i j * h H j nb
        w := h H i i - p
        if e.get! i.toNat < 0 then
          z := w
          r := ra
          s := sa
        else
          l := i
          if e.get! i.toNat == 0 then
            let (cr, ci) := cdiv (-ra) (-sa) w q
            H := hs H i (nb - 1) cr
            H := hs H i nb ci
          else
            x := h H i (i + 1)
            y := h H (i + 1) i
            let mut vr := (d.get! i.toNat - p) * (d.get! i.toNat - p) + e.get! i.toNat * e.get! i.toNat - q * q
            let vi := (d.get! i.toNat - p) * 2 * q
            if vr == 0 && vi == 0 then
              vr := epsilon * norm * (w.abs + q.abs + x.abs + y.abs + z.abs)
            let (cr, ci) := cdiv (x * r - z * ra + q * sa) (x * s - z * sa - q * ra) vr vi
            H := hs H i (nb - 1) cr
            H := hs H i nb ci
            if x.abs > z.abs + q.abs then
              H := hs H (i + 1) (nb - 1) ((-ra - w * h H i (nb - 1) + q * h H i nb) / x)
              H := hs H (i + 1) nb ((-sa - w * h H i nb - q * h H i (nb - 1)) / x)
            else
              let (cr, ci) := cdiv (-r - y * h H i (nb - 1)) (-s - y * h H i nb) z q
              H := hs H (i + 1) (nb - 1) cr
              H := hs H (i + 1) nb ci
          let t := F64.max (h H i (nb - 1)).abs (h H i nb).abs
          if (epsilon * t) * t > 1 then
            for j in [i.toNat:nb.toNat + 1] do
              H := hs H j (nb - 1) (h H j (nb - 1) / t)
              H := hs H j nb (h H j nb / t)
  -- back transformation
  for j' in [0:nn] do
    let j := nn - 1 - j'
    for i in [0:nn] do
      let mut zz : Float := 0
      for k in [0:j + 1] do zz := zz + rd V N i k * rd H N k j
      V := wr V N i j zz
  return (d, e, V)

/-- An eigen-decomposition: eigenvalues and eigenvectors (unit 2-norm columns),
real or complex, ordered as Julia orders them. -/
structure Decomposition where
  /-- Dimension. -/
  n : Nat
  /-- Real parts of the eigenvalues. -/
  re : FloatArray
  /-- Imaginary parts of the eigenvalues (all zero when real). -/
  im : FloatArray
  /-- Real parts of the eigenvectors, row-major (eigenvector `j` is column `j`). -/
  vre : FloatArray
  /-- Imaginary parts of the eigenvectors. -/
  vim : FloatArray
  /-- Whether Julia's result is real-typed (every eigenvalue real). -/
  real : Bool

/-- Julia `eigen(A)` of a real `n × n` matrix given row-major: the symmetric
path (ascending) or the general path (sorted by `(re, im)`), eigenvectors
normalised to unit 2-norm (complex ones with their largest component made
real). -/
def eigen (A : FloatArray) (n : Nat) : Decomposition := Id.run do
  let zeros := FloatArray.mk (Array.replicate n 0)
  let zerosM := FloatArray.mk (Array.replicate (n * n) 0)
  if isSymmetric A n then
    let (d, V) := symmetric A n
    return ⟨n, d, zeros, V, zerosM, true⟩
  let (H, V0) := orthes A n
  let (d, e, V) := hqr2 H V0 n
  -- complex eigenvectors from the real form
  let mut vre := zerosM
  let mut vim := zerosM
  let mut j := 0
  while j < n do
    if e.get! j == 0 then
      for i in [0:n] do vre := wr vre n i j (rd V n i j)
      j := j + 1
    else
      for i in [0:n] do
        vre := wr vre n i j (rd V n i j)
        vim := wr vim n i j (rd V n i (j + 1))
        vre := wr vre n i (j + 1) (rd V n i j)
        vim := wr vim n i (j + 1) (-rd V n i (j + 1))
      j := j + 2
  -- normalise (unit 2-norm; complex vectors rotated so the largest component is real)
  for c in [0:n] do
    let mut nrm : Float := 0
    for i in [0:n] do nrm := nrm + rd vre n i c * rd vre n i c + rd vim n i c * rd vim n i c
    nrm := Float.sqrt nrm
    if nrm != 0 then
      let mut big := 0
      let mut bigv : Float := -1
      for i in [0:n] do
        let a := rd vre n i c * rd vre n i c + rd vim n i c * rd vim n i c
        if a > bigv then
          big := i
          bigv := a
      let (cr, ci) := if e.get! c == 0 then (1 / nrm, (0 : Float))
        else
          let br := rd vre n big c
          let bi := rd vim n big c
          let m := F64.hypot br bi
          -- multiply by conj(b)/(|b| nrm)
          (br / (m * nrm), -bi / (m * nrm))
      for i in [0:n] do
        let a := rd vre n i c
        let b := rd vim n i c
        vre := wr vre n i c (a * cr - b * ci)
        vim := wr vim n i c (a * ci + b * cr)
  -- sort by (re, im) (Julia `eigsortby`), stable
  let perm := ((List.range n).toArray.qsort fun a b =>
      let ra := d.get! a
      let rb := d.get! b
      ra < rb || (ra == rb && (e.get! a < e.get! b || (e.get! a == e.get! b && a < b)))).toList
  let mut re := zeros
  let mut im := zeros
  let mut sre := zerosM
  let mut sim := zerosM
  for (k, idx) in perm.zipIdx.map (fun (a, b) => (b, a)) do
    re := re.set! k (d.get! idx)
    im := im.set! k (e.get! idx)
    for i in [0:n] do
      sre := wr sre n i k (rd vre n i idx)
      sim := wr sim n i k (rd vim n i idx)
  let real := (List.range n).all fun k => e.get! k == 0
  return ⟨n, re, im, sre, sim, real⟩

end Grassmann.Forms.Eigen
