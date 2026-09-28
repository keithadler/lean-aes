// Java JCE (OpenJDK's SunJCE provider): AES/ECB/NoPadding, AES/CTR/NoPadding, AES/CBC/PKCS5Padding.
import java.io.*;
import java.util.HexFormat;
import javax.crypto.Cipher;
import javax.crypto.spec.*;

public class Main {
    public static void main(String[] a) throws Exception {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        HexFormat hx = HexFormat.of();
        for (String line; (line = in.readLine()) != null; ) {
            String[] f = line.split("\t", -1);
            String out;
            try {
                SecretKeySpec key = new SecretKeySpec(hx.parseHex(f[3]), "AES");
                byte[] data = hx.parseHex(f[5]);
                Cipher c;
                switch (f[0]) {
                    case "block" -> { c = Cipher.getInstance("AES/ECB/NoPadding");
                        c.init(f[2].equals("decrypt") ? Cipher.DECRYPT_MODE : Cipher.ENCRYPT_MODE, key); }
                    case "ctr" -> { c = Cipher.getInstance("AES/CTR/NoPadding");
                        c.init(Cipher.ENCRYPT_MODE, key, new IvParameterSpec(hx.parseHex(f[4]))); }
                    default -> { c = Cipher.getInstance("AES/CBC/PKCS5Padding");
                        c.init(Cipher.DECRYPT_MODE, key, new IvParameterSpec(hx.parseHex(f[4]))); }
                }
                out = hx.formatHex(c.doFinal(data));
            } catch (Exception e) {
                out = "ERR:" + e.getClass().getSimpleName() + ": " + e.getMessage();
            }
            System.out.println(f[0] + "\t" + f[1] + "\t" + out.replace("\n", " "));
        }
    }
}
