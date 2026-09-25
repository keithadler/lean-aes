import AES

/-!
# `aes256`: the specification, compiled

The same `encrypt` and `decrypt` the theorems are about, as a command-line tool, so the definitions can be
checked against other implementations (`tools/crosscheck.py` compares it with OpenSSL).

    aes256 encrypt <64 hex digits of key> <32 hex digits of block>
    aes256 decrypt <key> <block>
    aes256 batch            lines of "<key> <block>" on stdin, one ciphertext per line out
-/

open AES

def parseHex (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c =>
    if '0' ≤ c ∧ c ≤ '9' then some (16 * acc + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * acc + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c ∧ c ≤ 'F' then some (16 * acc + (c.toNat - 'A'.toNat + 10))
    else none) 0

def hexByte (b : Byte) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d.getD (b.toNat / 16) '0', d.getD (b.toNat % 16) '0']

def AES.State.toHex (s : State) : String := String.join (s.toList.map hexByte)

def parseArgs (key block : String) : Except String (Key × State) := do
  unless key.length == 64 do throw s!"a key is 64 hex digits, got {key.length}"
  unless block.length == 32 do throw s!"a block is 32 hex digits, got {block.length}"
  let some k := parseHex key | throw "the key is not hexadecimal"
  let some b := parseHex block | throw "the block is not hexadecimal"
  return (Key.ofNat k, State.ofNat b)

def usage : String :=
  "usage: aes256 encrypt|decrypt <64-hex key> <32-hex block>\n       aes256 batch   (\"<key> <block>\" lines on stdin)"

partial def batch (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  match (line.trimAscii.toString.splitOn " ").filter (· ≠ "") with
  | [k, b] =>
    match parseArgs k b with
    | .ok (key, blk) => stdout.putStrLn (encrypt key blk).toHex; batch stdin stdout
    | .error e => IO.eprintln e; return 1
  | [] => batch stdin stdout
  | _ => IO.eprintln s!"expected \"<key> <block>\", got {line}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["encrypt", k, b] | ["decrypt", k, b] =>
    match parseArgs k b with
    | .ok (key, blk) =>
      IO.println (if args.head! == "encrypt" then encrypt key blk else decrypt key blk).toHex
      return 0
    | .error e => IO.eprintln e; return 1
  | ["batch"] => batch (← IO.getStdin) (← IO.getStdout)
  | _ => IO.eprintln usage; return 1
