# Vendored dependency

`cubical/` is the complete, unmodified source snapshot of the official [Cubical Agda Library](https://github.com/agda/cubical) at commit [`87af036ebd1c87956cf08fea44e62c7cf76392ca`](https://github.com/agda/cubical/commit/87af036ebd1c87956cf08fea44e62c7cf76392ca).

The snapshot contains 1,226 manifest-listed distribution files, including the original license and individual notices. Compiler interfaces, runtime caches, and repository metadata are not part of the snapshot. Identity and integrity are pinned by:

- [`agda/deps.lock.json`](../agda/deps.lock.json): compiler version, upstream commit, library identity, options, and manifest digest;
- [`agda/deps/cubical-files.sha256.json`](../agda/deps/cubical-files.sha256.json): SHA-256 of every distribution file.

The tree digest is SHA-256 of `<file digest>  <relative path>\n`, concatenated in sorted path order. Configuration verifies the full file set, not just imported modules, and neither downloads nor silently substitutes dependencies.

## Library identity and compatibility

`cubical-0.9` is the library identifier in this snapshot. It does **not** mean release `v0.9`; that older release lacks the required CW homology and Hurewicz modules.

The eight-line project module [`DeloopS3.Compat.Whitehead`](../agda/src/DeloopS3/Compat/Whitehead.agda) publicly reexports exactly these official `Cubical.Homotopy.Whitehead` declarations:

- `joinTo⋁`;
- `Iso-Susp×Susp-cofibJoinTo⋁`;
- `Susp×Susp→cofibW≡`.

The adapter adds no mathematical definitions or proof bodies. No library source is patched. The two final entries import 416 modules from this dependency, in addition to 467 project modules; compiler builtins are counted separately from that source closure.

## Licensing

The [original full license](cubical/LICENSE) is MIT with per-file exceptions identified by SPDX markers, including the BSD-3-Clause file `Cubical/Tactics/Reflection.agda`. Preserve the original license and all file notices when redistributing. See [third-party notices](../THIRD_PARTY_NOTICES.md) for the exception list and attribution. The project's root MIT license neither relicenses these sources nor overrides their terms.
