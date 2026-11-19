/-
  Grassmann/Server.lean — Pure-Lean 4.36 Persistent HTTP/1.1 Keep-Alive +
  RFC 6455 WebSocket Binary `GSIR` v1 Server (`lake exe ga-server`)

  100% pure Lean 4 ("it's all in Lean" — ZERO Python, ZERO C socket shims,
  ZERO per-request process spawning!). Uses Lean 4.36's built-in libuv TCP
  runtime (`Std.Internal.UV.TCP`) + `IO.asTask` concurrent workers +
  `Std.BaseMutex` + `Grassmann.CABI.Studio`.

  Note: `Grassmann.CABI` remains strictly `Init`-only (2.5 MB dylib / 73 KB
  gzipped WASM); this server module lives cleanly above it for native execution.
-/
import Std.Internal.UV.TCP
import Std.Sync.Mutex
import Grassmann.CABI.Studio

namespace Grassmann.Server

open Std.Internal.UV.TCP
open Std.Net
open Grassmann.CABI
open Grassmann.CABI.ScenePack

/-! ### Pure-Lean SHA-1 & Base64 (RFC 6455 `Sec-WebSocket-Accept`) -/

@[inline] private def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- Pure-Lean SHA-1 digest returning 20 bytes. -/
def sha1 (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  -- Pad: 0x80, then zeros until size % 64 == 56, then 64-bit big-endian bitLen
  let mut padded := msg.push 0x80
  while padded.size % 64 != 56 do
    padded := padded.push 0x00
  for shift in #[56, 48, 40, 32, 24, 16, 8, 0] do
    padded := padded.push ((bitLen >>> shift.toUInt64) &&& 0xFF).toUInt8

  let mut h0 : UInt32 := 0x67452301
  let mut h1 : UInt32 := 0xEFCDAB89
  let mut h2 : UInt32 := 0x98BADCFE
  let mut h3 : UInt32 := 0x10325476
  let mut h4 : UInt32 := 0xC3D2E1F0

  let nBlocks := padded.size / 64
  for blk in [:nBlocks] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.replicate 80 0
    for i in [:16] do
      let o := base + i * 4
      let v : UInt32 :=
        ((getU8 padded o).toUInt32 <<< 24)
        ||| ((getU8 padded (o + 1)).toUInt32 <<< 16)
        ||| ((getU8 padded (o + 2)).toUInt32 <<< 8)
        ||| (getU8 padded (o + 3)).toUInt32
      w := w.set! i v
    for i in [16:80] do
      let x := w[i - 3]! ^^^ w[i - 8]! ^^^ w[i - 14]! ^^^ w[i - 16]!
      w := w.set! i (rotl32 x 1)

    let mut a := h0; let mut b := h1; let mut c := h2; let mut d := h3; let mut e := h4
    for i in [:80] do
      let (f, k) : UInt32 × UInt32 :=
        if i < 20 then ((b &&& c) ||| ((~~~b) &&& d), 0x5A827999)
        else if i < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
        else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
        else (b ^^^ c ^^^ d, 0xCA62C1D6)
      let temp := rotl32 a 5 + f + e + k + w[i]!
      e := d; d := c; c := rotl32 b 30; b := a; a := temp
    h0 := h0 + a; h1 := h1 + b; h2 := h2 + c; h3 := h3 + d; h4 := h4 + e

  let mut out := ByteArray.emptyWithCapacity 20
  for h in #[h0, h1, h2, h3, h4] do
    out := out
      |>.push ((h >>> 24) &&& 0xFF).toUInt8
      |>.push ((h >>> 16) &&& 0xFF).toUInt8
      |>.push ((h >>> 8) &&& 0xFF).toUInt8
      |>.push (h &&& 0xFF).toUInt8
  return out

private def b64Table : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- Pure-Lean Base64 encoder. -/
def base64Encode (data : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  while i < data.size do
    let b0 := (getU8 data i).toNat
    let has1 := i + 1 < data.size
    let has2 := i + 2 < data.size
    let b1 := if has1 then (getU8 data (i + 1)).toNat else 0
    let b2 := if has2 then (getU8 data (i + 2)).toNat else 0
    let triple := (b0 <<< 16) ||| (b1 <<< 8) ||| b2
    out := out.push b64Table[(triple >>> 18) &&& 0x3F]!
    out := out.push b64Table[(triple >>> 12) &&& 0x3F]!
    out := out.push (if has1 then b64Table[(triple >>> 6) &&& 0x3F]! else '=')
    out := out.push (if has2 then b64Table[triple &&& 0x3F]! else '=')
    i := i + 3
  return out

/-- Compute RFC 6455 `Sec-WebSocket-Accept` header value from `Sec-WebSocket-Key`. -/
def wsAcceptKey (clientKey : String) : String :=
  base64Encode (sha1 (clientKey.trimAscii.toString ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").toUTF8)

/-! ### Socket Buffered I/O Helpers -/

private structure ConnBuf where
  sock : Socket
  buf : IO.Ref ByteArray

private def sendBytes (sock : Socket) (data : ByteArray) : IO Bool := do
  let p ← sock.send #[data]
  match p.result?.get with
  | some (.ok ()) => return true
  | _ => return false

private def sendChunks (sock : Socket) (chunks : Array ByteArray) : IO Bool := do
  let p ← sock.send chunks
  match p.result?.get with
  | some (.ok ()) => return true
  | _ => return false

/-- Ensure at least `n` bytes are buffered in `cb`, reading from socket until satisfied or EOF. -/
private def readExact (cb : ConnBuf) (n : Nat) : IO (Option ByteArray) := do
  let mut cur ← cb.buf.get
  while cur.size < n do
    let p ← cb.sock.recv? 65536
    match p.result?.get with
    | some (.ok (some chunk)) =>
      if chunk.size == 0 then return none
      cur := cur.append chunk
    | _ =>
      cb.buf.set cur
      return none
  let out := cur.extract 0 n
  cb.buf.set (cur.extract n cur.size)
  return some out

/-- Find index of `\r\n\r\n` inside `b`, returning the byte offset of the first `\r`. -/
private def findHeaderEnd (b : ByteArray) : Option Nat := Id.run do
  if b.size < 4 then return none
  for i in [:b.size - 3] do
    if getU8 b i == 13 && getU8 b (i + 1) == 10 &&
       getU8 b (i + 2) == 13 && getU8 b (i + 3) == 10 then
      return some i
  return none

/-- Read one HTTP request header block (up to `\r\n\r\n`). -/
private def readHttpHeader (cb : ConnBuf) : IO (Option String) := do
  let mut cur ← cb.buf.get
  while true do
    match findHeaderEnd cur with
    | some idx =>
      let hdrBytes := cur.extract 0 idx
      cb.buf.set (cur.extract (idx + 4) cur.size)
      return some (String.fromUTF8! hdrBytes)
    | none =>
      if cur.size > 65536 then return none
      let p ← cb.sock.recv? 65536
      match p.result?.get with
      | some (.ok (some chunk)) =>
        if chunk.size == 0 then return none
        cur := cur.append chunk
      | _ =>
        cb.buf.set cur
        return none
  return none

/-! ### RFC 6455 WebSocket Frame Reader / Writer -/

/-- Encode a single unmasked server→client RFC 6455 WebSocket frame. -/
def encodeWsFrame (opcode : UInt8) (payload : ByteArray) : ByteArray :=
  let len := payload.size
  let hdr := ByteArray.emptyWithCapacity 10
  let hdr := hdr.push (0x80 ||| (opcode &&& 0x0F))
  let hdr :=
    if len < 126 then
      hdr.push len.toUInt8
    else if len < 65536 then
      hdr |>.push 126
          |>.push ((len >>> 8) &&& 0xFF).toUInt8
          |>.push (len &&& 0xFF).toUInt8
    else
      let u : UInt64 := len.toUInt64
      hdr |>.push 127
          |>.push ((u >>> 56) &&& 0xFF).toUInt8
          |>.push ((u >>> 48) &&& 0xFF).toUInt8
          |>.push ((u >>> 40) &&& 0xFF).toUInt8
          |>.push ((u >>> 32) &&& 0xFF).toUInt8
          |>.push ((u >>> 24) &&& 0xFF).toUInt8
          |>.push ((u >>> 16) &&& 0xFF).toUInt8
          |>.push ((u >>> 8) &&& 0xFF).toUInt8
          |>.push (u &&& 0xFF).toUInt8
  hdr.append payload

/-- Read one RFC 6455 WebSocket frame, returning `(opcode, unmaskedPayload)`. -/
private def readWsFrame (cb : ConnBuf) : IO (Option (UInt8 × ByteArray)) := do
  let some h2 ← readExact cb 2 | return none
  let b0 := getU8 h2 0
  let b1 := getU8 h2 1
  let opcode := b0 &&& 0x0F
  let masked := (b1 &&& 0x80) != 0
  let len7 := (b1 &&& 0x7F).toNat
  let payloadLen : Nat ←
    if len7 < 126 then pure len7
    else if len7 == 126 then
      let some ext ← readExact cb 2 | return none
      pure (((getU8 ext 0).toNat <<< 8) ||| (getU8 ext 1).toNat)
    else
      let some ext ← readExact cb 8 | return none
      let mut n : Nat := 0
      for i in [:8] do
        n := (n <<< 8) ||| (getU8 ext i).toNat
      pure n
  if payloadLen > 16 * 1024 * 1024 then return none
  let maskKey : ByteArray ←
    if masked then
      let some m ← readExact cb 4 | return none
      pure m
    else pure ByteArray.empty
  let some raw ← readExact cb payloadLen | return none
  if !masked then return some (opcode, raw)
  let m0 := getU8 maskKey 0; let m1 := getU8 maskKey 1
  let m2 := getU8 maskKey 2; let m3 := getU8 maskKey 3
  let unmasked := Id.run do
    let mut out := ByteArray.emptyWithCapacity raw.size
    for i in [:raw.size] do
      let k := match i % 4 with | 0 => m0 | 1 => m1 | 2 => m2 | _ => m3
      out := out.push ((getU8 raw i) ^^^ k)
    return out
  return some (opcode, unmasked)

/-! ### HTTP Parsing, Static File Serving & Studio Dispatch -/

structure ServerConfig where
  host : String := "127.0.0.1"
  port : UInt16 := 8787
  staticDir : Option String := none

private structure ServerCtx where
  cfg : ServerConfig
  studioLock : Std.BaseMutex
  defaultSid : UInt64

private def withStudioLock {α : Type} (ctx : ServerCtx) (act : IO α) : IO α := do
  ctx.studioLock.lock
  try
    let res ← act
    ctx.studioLock.unlock
    return res
  catch e =>
    ctx.studioLock.unlock
    throw e

private def lowerAscii (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c >= 'A' && c <= 'Z' then
      out := out.push (Char.ofNat (c.toNat + 32))
    else
      out := out.push c
  return out

private def parseHeaders (hdrText : String) : String × String × Array (String × String) := Id.run do
  let lines := hdrText.splitOn "\r\n"
  let reqLine := lines.headD ""
  let parts := reqLine.splitOn " "
  let method := parts.headD "GET"
  let rawPath := (parts.drop 1).headD "/"
  let path := (rawPath.splitOn "?").headD "/"
  let mut hdrs : Array (String × String) := #[]
  for line in lines.drop 1 do
    match line.splitOn ":" with
    | k :: rest =>
      let v := (":".intercalate rest).trimAscii.toString
      hdrs := hdrs.push (lowerAscii k.trimAscii.toString, v)
    | _ => pure ()
  return (method, path, hdrs)

private def getHeader (hdrs : Array (String × String)) (name : String) : Option String := Id.run do
  for (k, v) in hdrs do
    if k == name then return some v
  return none

private def mimeTypeFor (path : String) : String :=
  if path.endsWith ".html" then "text/html; charset=utf-8"
  else if path.endsWith ".js" || path.endsWith ".mjs" then "application/javascript; charset=utf-8"
  else if path.endsWith ".css" then "text/css; charset=utf-8"
  else if path.endsWith ".wasm" then "application/wasm"
  else if path.endsWith ".json" then "application/json; charset=utf-8"
  else if path.endsWith ".svg" then "image/svg+xml"
  else if path.endsWith ".png" then "image/png"
  else if path.endsWith ".ico" then "image/x-icon"
  else if path.endsWith ".map" then "application/json"
  else "application/octet-stream"

private def sendHttpResp (sock : Socket) (status : String) (contentType : String)
    (body : ByteArray) (keepAlive : Bool) : IO Bool := do
  let conn := if keepAlive then "keep-alive" else "close"
  let hdr :=
    s!"HTTP/1.1 {status}\r\n" ++
    s!"Content-Type: {contentType}\r\n" ++
    s!"Content-Length: {body.size}\r\n" ++
    s!"Connection: {conn}\r\n" ++
    "Access-Control-Allow-Origin: *\r\n" ++
    "Access-Control-Allow-Methods: GET, POST, DELETE, OPTIONS\r\n" ++
    "Access-Control-Allow-Headers: Content-Type\r\n" ++
    "\r\n"
  sendChunks sock #[hdr.toUTF8, body]

private def parseSessionIdFromPath (path : String) : Option (UInt64 × String) :=
  -- Matches /api/session/<id> or /api/session/<id>/<action>
  if !path.startsWith "/api/session/" then none
  else
    let rest := (path.drop 13).toString
    match rest.splitOn "/" with
    | [idStr] => idStr.toNat?.map fun n => (n.toUInt64, "")
    | [idStr, action] => idStr.toNat?.map fun n => (n.toUInt64, action)
    | _ => none

/-- Handle an upgraded RFC 6455 WebSocket connection with a dedicated Studio session. -/
private def handleWebSocket (ctx : ServerCtx) (cb : ConnBuf) (wsKey : String) : IO Unit := do
  let accept := wsAcceptKey wsKey
  let resp :=
    "HTTP/1.1 101 Switching Protocols\r\n" ++
    "Upgrade: websocket\r\n" ++
    "Connection: Upgrade\r\n" ++
    s!"Sec-WebSocket-Accept: {accept}\r\n\r\n"
  let ok ← sendBytes cb.sock resp.toUTF8
  if !ok then return

  let sid ← withStudioLock ctx Studio.createSession
  try
    while true do
      match ← readWsFrame cb with
      | none => break
      | some (opcode, payload) =>
        if opcode == 0x8 then
          -- Close frame
          let _ ← sendBytes cb.sock (encodeWsFrame 0x8 ByteArray.empty)
          break
        else if opcode == 0x9 then
          -- Ping -> Pong
          let _ ← sendBytes cb.sock (encodeWsFrame 0xA payload)
        else if opcode == 0x2 then
          -- Binary GSIR InputEvent -> Binary GSIR v1 frame!
          let (rc, frame) ← withStudioLock ctx (Studio.dispatchBin sid payload)
          if rc == 0 then
            let sent ← sendBytes cb.sock (encodeWsFrame 0x2 frame)
            if !sent then break
        else if opcode == 0x1 then
          -- Text JSON InputEvent -> Binary GSIR v1 frame!
          let json := String.fromUTF8! payload
          let (rc, frame) ← withStudioLock ctx (Studio.dispatchJson sid json)
          if rc == 0 then
            let sent ← sendBytes cb.sock (encodeWsFrame 0x2 frame)
            if !sent then break
  finally
    withStudioLock ctx (Studio.destroySession sid)

/-- Serve static files from `staticDir`, strictly rejecting `..` path traversal. -/
private def serveStatic (sock : Socket) (staticDir : String) (reqPath : String)
    (keepAlive : Bool) : IO Bool := do
  let rel := if reqPath == "/" then "/index.html" else reqPath
  if rel.contains ".." || rel.contains "\\" then
    return ← sendHttpResp sock "403 Forbidden" "text/plain" "forbidden".toUTF8 keepAlive
  let fullPath : System.FilePath := System.FilePath.mk (staticDir ++ rel)
  if ← fullPath.pathExists then
    try
      let bytes ← IO.FS.readBinFile fullPath
      return ← sendHttpResp sock "200 OK" (mimeTypeFor rel) bytes keepAlive
    catch _ =>
      return ← sendHttpResp sock "500 Internal Server Error" "text/plain" "read error".toUTF8 keepAlive
  else
    return ← sendHttpResp sock "404 Not Found" "application/json" "{\"error\":\"not found\"}".toUTF8 keepAlive

/-- Handle one persistent HTTP/1.1 connection (may upgrade to WebSocket). -/
private def handleClient (ctx : ServerCtx) (client : Socket) : IO Unit := do
  try
    client.noDelay
  catch _ => pure ()
  let bufRef ← IO.mkRef ByteArray.empty
  let cb : ConnBuf := { sock := client, buf := bufRef }
  try
    while true do
      let some hdrText ← readHttpHeader cb | break
      let (method, path, hdrs) := parseHeaders hdrText
      let connHdr := lowerAscii ((getHeader hdrs "connection").getD "")
      let keepAlive := connHdr != "close"

      -- WebSocket upgrade check (`GET /ws`)
      let upgradeHdr := lowerAscii ((getHeader hdrs "upgrade").getD "")
      if method == "GET" && (path == "/ws" || path == "/ws/") && upgradeHdr == "websocket" then
        match getHeader hdrs "sec-websocket-key" with
        | some wsKey =>
          handleWebSocket ctx cb wsKey
          break
        | none =>
          let _ ← sendHttpResp client "400 Bad Request" "text/plain" "missing ws key".toUTF8 false
          break

      -- Read request body if Content-Length present
      let contentLen := ((getHeader hdrs "content-length").bind String.toNat?).getD 0
      if contentLen > 16 * 1024 * 1024 then
        let _ ← sendHttpResp client "413 Payload Too Large" "text/plain" "too large".toUTF8 false
        break
      let body : ByteArray ←
        if contentLen > 0 then
          match ← readExact cb contentLen with
          | some b => pure b
          | none => break
        else pure ByteArray.empty

      let ok ←
        if method == "OPTIONS" then
          sendHttpResp client "204 No Content" "text/plain" ByteArray.empty keepAlive
        else if method == "GET" && path == "/health" then
          let payload := "{\"ok\":true,\"version\":1,\"protocol\":\"GSIR/1\",\"server\":\"ga-server\",\"cabiVersion\":\"2.0\"}"
          sendHttpResp client "200 OK" "application/json" payload.toUTF8 keepAlive
        else if method == "POST" && path == "/api/session" then
          let sid ← withStudioLock ctx Studio.createSession
          sendHttpResp client "200 OK" "application/json" s!"\{\"session\":{sid}}".toUTF8 keepAlive
        else if method == "GET" && path == "/api/frame" then
          let (rc, frame) ← withStudioLock ctx (Studio.getCachedFrame ctx.defaultSid)
          if rc == 0 then sendHttpResp client "200 OK" "application/octet-stream" frame keepAlive
          else sendHttpResp client "404 Not Found" "application/json" "{\"error\":\"bad session\"}".toUTF8 keepAlive
        else if method == "POST" && (path == "/api/dispatch/bin" || path == "/api/event/bin") then
          let (rc, frame) ← withStudioLock ctx (Studio.dispatchBin ctx.defaultSid body)
          if rc == 0 then sendHttpResp client "200 OK" "application/octet-stream" frame keepAlive
          else sendHttpResp client "400 Bad Request" "application/json" s!"\{\"error\":{rc}}".toUTF8 keepAlive
        else if method == "POST" && (path == "/api/dispatch/json" || path == "/api/event/json") then
          let (rc, frame) ← withStudioLock ctx (Studio.dispatchJson ctx.defaultSid (String.fromUTF8! body))
          if rc == 0 then sendHttpResp client "200 OK" "application/octet-stream" frame keepAlive
          else sendHttpResp client "400 Bad Request" "application/json" s!"\{\"error\":{rc}}".toUTF8 keepAlive
        else match parseSessionIdFromPath path with
        | some (sid, "") =>
          if method == "DELETE" then
            withStudioLock ctx (Studio.destroySession sid)
            sendHttpResp client "200 OK" "application/json" "{\"ok\":true}".toUTF8 keepAlive
          else
            sendHttpResp client "405 Method Not Allowed" "text/plain" "method not allowed".toUTF8 keepAlive
        | some (sid, "frame") =>
          let (rc, frame) ← withStudioLock ctx (Studio.getCachedFrame sid)
          if rc == 0 then sendHttpResp client "200 OK" "application/octet-stream" frame keepAlive
          else sendHttpResp client "404 Not Found" "application/json" "{\"error\":\"session not found\"}".toUTF8 keepAlive
        | some (sid, "bin") =>
          let (rc, frame) ← withStudioLock ctx (Studio.dispatchBin sid body)
          if rc == 0 then sendHttpResp client "200 OK" "application/octet-stream" frame keepAlive
          else sendHttpResp client "400 Bad Request" "application/json" s!"\{\"error\":{rc}}".toUTF8 keepAlive
        | some (sid, "json") =>
          let (rc, frame) ← withStudioLock ctx (Studio.dispatchJson sid (String.fromUTF8! body))
          if rc == 0 then sendHttpResp client "200 OK" "application/octet-stream" frame keepAlive
          else sendHttpResp client "400 Bad Request" "application/json" s!"\{\"error\":{rc}}".toUTF8 keepAlive
        | _ =>
          match ctx.cfg.staticDir with
          | some dir => serveStatic client dir path keepAlive
          | none =>
            sendHttpResp client "404 Not Found" "application/json" "{\"error\":\"not found\"}".toUTF8 keepAlive

      if !ok || !keepAlive then break
  catch _ =>
    pure ()
  try
    let _ ← client.shutdown
  catch _ => pure ()

/-- Self-test built-in crypto & protocol invariants (RFC 6455 test vector). -/
def runSelfTest : IO UInt32 := do
  let got := wsAcceptKey "dGhlIHNhbXBsZSBub25jZQ=="
  let expected := "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
  if got != expected then
    IO.eprintln s!"FAIL: RFC 6455 wsAcceptKey got '{got}', expected '{expected}'"
    return 1
  let sid ← Studio.createSession
  let (rc, frame) ← Studio.getCachedFrame sid
  Studio.destroySession sid
  if rc != 0 || frame.size < 64 then
    IO.eprintln s!"FAIL: Studio initial frame rc={rc} size={frame.size}"
    return 1
  IO.println s!"[ga-server self-test] PASS (RFC 6455 SHA-1/Base64 verified, initial GSIR frame={frame.size} B)"
  return 0

/-- Start the persistent HTTP/1.1 + WebSocket `GSIR` v1 server. -/
def serve (cfg : ServerConfig) : IO UInt32 := do
  let some ipv4 := IPv4Addr.ofString cfg.host
    | do IO.eprintln s!"[ga-server] invalid IPv4 host: {cfg.host}"; return 2
  let addr : SocketAddress := .v4 { addr := ipv4, port := cfg.port }
  let listener ← Socket.new
  listener.bind addr
  listener.listen 128

  let lock ← Std.BaseMutex.new
  let defaultSid ← Studio.createSession
  let ctx : ServerCtx := { cfg, studioLock := lock, defaultSid }

  IO.println s!"[ga-server] listening on http://{cfg.host}:{cfg.port} (WS: ws://{cfg.host}:{cfg.port}/ws, GSIR v1)"
  match cfg.staticDir with
  | some d => IO.println s!"[ga-server] serving static assets from {d}"
  | none => pure ()
  (← IO.getStdout).flush

  while true do
    let p ← listener.accept
    match p.result?.get with
    | some (.ok client) =>
      let _ ← IO.asTask (prio := .dedicated) (handleClient ctx client)
    | some (.error err) =>
      IO.eprintln s!"[ga-server] accept error: {err}"
    | none => break
  return 0

end Grassmann.Server
