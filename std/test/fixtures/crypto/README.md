# Test keys and signatures for `std/test/crypto_test.qz`

Made once with OpenSSL 3.5 (test keys only: nothing here protects
anything). `message.txt` is the signed text, without a newline.

```sh
openssl genrsa -traditional -out rsa2048_pkcs1.pem 2048
openssl pkcs8 -topk8 -nocrypt -in rsa2048_pkcs1.pem -out rsa2048_pkcs8.pem
openssl rsa -in rsa2048_pkcs1.pem -pubout -out rsa2048_spki.pem
openssl rsa -in rsa2048_pkcs1.pem -RSAPublicKey_out -out rsa2048_pkcs1_pub.pem
printf 'the quick brown fox' > message.txt
for h in sha256 sha384 sha512; do
  openssl dgst -$h -sign rsa2048_pkcs8.pem -out sig_pkcs1v15_$h.bin message.txt
done
for h in sha256 sha512; do
  openssl dgst -$h -sign rsa2048_pkcs8.pem -sigopt rsa_padding_mode:pss \
    -sigopt rsa_pss_saltlen:digest -out sig_pss_$h.bin message.txt
done
# Other salt lengths, which verify_pss accepts:
openssl dgst -sha256 -sign rsa2048_pkcs8.pem -sigopt rsa_padding_mode:pss \
  -sigopt rsa_pss_saltlen:max -out sig_pss_sha256_saltmax.bin message.txt
openssl dgst -sha384 -sign rsa2048_pkcs8.pem -sigopt rsa_padding_mode:pss \
  -sigopt rsa_pss_saltlen:0 -out sig_pss_sha384_salt0.bin message.txt
# What is refused, or read but not generated:
openssl pkcs8 -topk8 -v2 aes-256-cbc -passout pass:test -in rsa2048_pkcs1.pem -out rsa2048_encrypted.pem
openssl rsa -in rsa2048_pkcs1.pem -traditional -aes128 -passout pass:test -out rsa2048_proc_type.pem
openssl ecparam -name prime256v1 -genkey -noout | openssl pkcs8 -topk8 -nocrypt -out ec_p256_pkcs8.pem
openssl genrsa -out rsa1024_pkcs8.pem 1024   # read and used (old keys exist)
openssl genrsa -out rsa512_pkcs8.pem 512     # read, but too small to sign with
```
