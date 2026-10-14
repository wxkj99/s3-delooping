# Delooping the 3-sphere in homotopy type theory

A Cubical Agda formalization of a connected pointed delooping of S³, together with a maximal torus for the same constructed type.

**Jiatong Yang** · Qiuzhen College, Tsinghua University · <yangjt22@mails.tsinghua.edu.cn>

[Paper (PDF)](docs/s3-delooping-paper.pdf) · [LaTeX source](docs/paper/main.tex)

This repository distributes the formalization sources, reproducibility tooling, and the accompanying paper. Other local documentation, audit records, and verification logs are maintained separately.

## Results

[`DeloopS3.Assembly.Complete`](agda/src/DeloopS3/Assembly/Complete.agda) constructs an element of the **untruncated** dependent sum

```agda
Deloop-S3 : Σ[ B ∈ Pointed ℓ-zero ]
  (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
```

Here `isConnected 2` means connected. The theorem supplies the pointed type, its connectedness, and a pointed loop-space equivalence; it has no module parameters or outstanding input assumptions.

[`DeloopS3.HPInf.Complete`](agda/src/DeloopS3/HPInf/Complete.agda) supplies a pointed map `t : K₂∙ →∙ B` with `fiber (fst t) (pt B) ≃ S₊ 2`, where `K₂∙` is pointed K(ℤ,2). This is a maximal torus for the **same concrete B**, packaged as `S³-delooping-with-maximal-torus`.

### Strategy

Finite Seifert covers of indices 3 and 10 give compatible fibre sequences with fibre S³. Ordinary cellular homology and finite-dimensional Moore recognition prove that the total spaces become contractible after the corresponding localizations. Fibre preservation identifies the loops of the localized bases with localized spheres; a common comparison after inverting 30 and arithmetic fracture glue these bases into B. A cartesian comparison at the common corner then constructs the maximal torus. The argument does not assume a fully coherent multiplication on S³ in advance.

### Scope

The formalization uses `--safe --cubical --guardedness`, with `--lossy-unification` in some auxiliary modules, and adds no axioms. It does **not** establish an equivalence with an independently defined HP∞ model or compatibility of the loop equivalence with the Cayley–Dickson H-space multiplication. Classically, Dwyer–Miller–Wilkerson, Theorem 1.1 and Remark 1.2, together with the Rector–McGibbon maximal-torus criterion, identify this homotopy type with HP∞. That recognition argument is cited in the accompanying paper, not formalized here.

## Check the formalization

Requirements: **Agda 2.8.0.2** with GHC RTS support, **Python ≥ 3.9**, Bash, `flock`, and GNU `timeout`. The verified platform is Linux. Install these tools separately; checking is offline and needs no global Agda library registration.

From the repository root:

```sh
# Verify the compiler and dependency; generate local configuration.
bash agda/check.sh --configure-only

# Check both final entries, in order, with a per-entry timeout.
DELOOP_TIMEOUT=18000 bash agda/check.sh

# Optional: check a single file (path relative to agda/).
bash agda/check.sh src/DeloopS3/HPInf/Complete.agda 600

# Run the tooling tests; these are not proof checks.
python3 -m unittest discover -s agda/tools -p 'test_*.py'
```

The runner serializes checks and defaults to a 12-GiB **heap** cap, not a total-process memory cap. Its default 600-second timeout is for quick incremental checks, not an expected cold-build time. The tooling suite has 48 passing tests.

## Dependency and source layout

The complete, **unmodified official Cubical** snapshot at commit [`87af036ebd1c87956cf08fea44e62c7cf76392ca`](https://github.com/agda/cubical/commit/87af036ebd1c87956cf08fea44e62c7cf76392ca) is vendored with its original notices. The lock and SHA-256 manifest pin all 1,226 distribution files. `cubical-0.9` is its library identifier, **not** a claim to use release `v0.9`; that release lacks required modules. The eight-line project adapter `DeloopS3.Compat.Whitehead` only reexports three existing official declarations; it is not a library patch.

Vendoring is an offline distribution choice, not a requirement of the proof. The runner also accepts an external copy through `CUBICAL_DIR`; it must match the same pinned file manifest. For example:

```sh
CUBICAL_DIR=/absolute/path/to/cubical bash agda/check.sh --configure-only
```

The final import closure contains 467 project modules and 416 external Cubical modules, excluding compiler builtins. The distribution contains formalization sources, tooling, and the paper's LaTeX sources and PDF. Other local documentation, compiler interfaces, and machine-local configuration are excluded.

| Path | Contents |
| --- | --- |
| `agda/src/DeloopS3/` | Formal proofs; final entries in `Assembly/Complete.agda` and `HPInf/Complete.agda` |
| `agda/check.sh`, `agda/tools/` | Offline configuration, bounded checking, dependency/options audits, and tests |
| `agda/roots.txt`, `agda/deps.lock.json`, `agda/deps/` | Entry-point manifest, dependency lock, and file checksums |
| `vendor/cubical/` | Full official dependency source and original license |
| `docs/paper/` | Paper LaTeX sources and build script |
| `docs/s3-delooping-paper.pdf` | Compiled paper |

## Build the paper

With a LaTeX installation providing `pdflatex` and the packages used by `main.tex`, Bash, and GNU `timeout`, run:

```sh
bash docs/paper/build.sh
```

The script compiles three times, checks for layout and reference warnings, and writes `docs/s3-delooping-paper.pdf`. Intermediate files remain in the ignored `docs/paper/.build/` directory.

## Licensing

Project-owned formalization code and tooling are licensed under the [MIT License](LICENSE), copyright © 2026 Jiatong Yang. This does not relicense vendored code or override third-party file terms. Cubical retains its own MIT license and SPDX-marked BSD-3-Clause exception; see [third-party notices](THIRD_PARTY_NOTICES.md) and the [original dependency license](vendor/cubical/LICENSE).

The paper's LaTeX sources and PDF are copyright © 2026 Jiatong Yang and are not covered by the code's MIT license.
