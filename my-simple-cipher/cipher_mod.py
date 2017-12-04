#!/usr/bin/python2

key = pyState.String(13)
flag = '**CENSORED**'

assert len(key) == 13
assert max([ord(char) for char in key]) < 128
assert max([ord(char) for char in flag]) < 128

message = flag + "|" + key

#encrypted = chr(random.randint(0, 128))
encrypted = pyState.String(1)
assert ord(encrypted) <= 128
assert ord(encrypted) >= 0

for i in range(0, len(message)):
  encrypted += chr((ord(message[i]) + ord(key[i % len(key)]) + ord(encrypted[i])) % 128)

print(encrypted.encode('hex'))
