// Apple CommonCrypto (what CryptoKit and the rest of macOS and iOS use for AES-ECB/CTR/CBC).
import CommonCrypto
import Foundation

func bytes(_ h: String) -> [UInt8] {
    var out = [UInt8](); var i = h.startIndex
    while i < h.endIndex { let j = h.index(i, offsetBy: 2); out.append(UInt8(h[i..<j], radix: 16)!); i = j }
    return out
}
func hex(_ b: [UInt8]) -> String { b.map { String(format: "%02x", $0) }.joined() }

func run(mode: CCMode, op: CCOperation, padding: CCPadding, options: CCModeOptions, key: [UInt8], iv: [UInt8]?, input: [UInt8]) -> String {
    var ref: CCCryptorRef?
    var st = CCCryptorCreateWithMode(op, mode, CCAlgorithm(kCCAlgorithmAES), padding, iv, key, key.count, nil, 0, 0, options, &ref)
    guard st == kCCSuccess, let c = ref else { return "ERR:create \(st)" }
    defer { CCCryptorRelease(c) }
    var out = [UInt8](repeating: 0, count: input.count + 32)
    var moved = 0, total = 0
    st = CCCryptorUpdate(c, input, input.count, &out, out.count, &moved)
    guard st == kCCSuccess else { return "ERR:update \(st)" }
    total += moved
    st = out.withUnsafeMutableBufferPointer { p in CCCryptorFinal(c, p.baseAddress! + total, p.count - total, &moved) }
    guard st == kCCSuccess else { return "ERR:final \(st)" }
    total += moved
    return hex(Array(out[0..<total]))
}

while let line = readLine() {
    let f = line.split(separator: "\t", omittingEmptySubsequences: false).map(String.init)
    let (suite, id, op) = (f[0], f[1], f[2])
    let key = bytes(f[3]), iv = f[4].isEmpty ? nil : bytes(f[4]), input = bytes(f[5])
    var out = "NA"
    switch suite {
    case "block":
        out = run(mode: CCMode(kCCModeECB), op: CCOperation(op == "decrypt" ? kCCDecrypt : kCCEncrypt), padding: CCPadding(ccNoPadding), options: 0, key: key, iv: nil, input: input)
    case "ctr":
        out = run(mode: CCMode(kCCModeCTR), op: CCOperation(kCCEncrypt), padding: CCPadding(ccNoPadding), options: CCModeOptions(kCCModeOptionCTR_BE), key: key, iv: iv, input: input)
    case "cbc":
        out = run(mode: CCMode(kCCModeCBC), op: CCOperation(kCCDecrypt), padding: CCPadding(ccPKCS7Padding), options: 0, key: key, iv: iv, input: input)
    default: break
    }
    print("\(suite)\t\(id)\t\(out)")
}
