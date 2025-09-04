# Linked List Implementation in Verus

This simple linked list provides only `push_front` and `pop_back`.

## Building

Make sure you have a recent version of verus installed

[https://github.com/verus-lang/verus/blob/main/INSTALL.md]

```
$ verus --version
Verus
  Version: 0.2025.08.25.63ab0cb
  Profile: release
  Platform: linux_x86_64
  Toolchain: 1.88.0-x86_64-unknown-linux-gnu
```

Run the verification with cargo-verus:

```
cargo verus verify
```
