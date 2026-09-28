// Go crypto/aes and crypto/cipher. Go's standard library has no PKCS #7 unpadding, so cbc is n/a.
package main

import (
	"bufio"
	"crypto/aes"
	"crypto/cipher"
	"encoding/hex"
	"fmt"
	"os"
	"strings"
)

func main() {
	sc := bufio.NewScanner(os.Stdin)
	sc.Buffer(make([]byte, 1<<20), 1<<20)
	for sc.Scan() {
		f := strings.Split(sc.Text(), "\t")
		suite, id, op := f[0], f[1], f[2]
		key, _ := hex.DecodeString(f[3])
		iv, _ := hex.DecodeString(f[4])
		in, _ := hex.DecodeString(f[5])
		out := "NA"
		b, err := aes.NewCipher(key)
		if err != nil {
			out = "ERR:" + err.Error()
		} else {
			switch suite {
			case "block":
				dst := make([]byte, 16)
				if op == "decrypt" {
					b.Decrypt(dst, in)
				} else {
					b.Encrypt(dst, in)
				}
				out = hex.EncodeToString(dst)
			case "ctr":
				dst := make([]byte, len(in))
				cipher.NewCTR(b, iv).XORKeyStream(dst, in)
				out = hex.EncodeToString(dst)
			}
		}
		fmt.Printf("%s\t%s\t%s\n", suite, id, out)
	}
}
