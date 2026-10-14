# Third-party notices

The root MIT license applies to project-owned material only. It does not relicense the vendored dependency or supersede any third-party file's license, copyright notice, or attribution. Vendoring does not transfer authorship to the author of this project.

## Cubical Agda Library

- **Official source:** <https://github.com/agda/cubical>
- **Pinned commit:** [`87af036ebd1c87956cf08fea44e62c7cf76392ca`](https://github.com/agda/cubical/commit/87af036ebd1c87956cf08fea44e62c7cf76392ca)
- **Location:** [`vendor/cubical/`](vendor/cubical/)
- **Original full license:** [`vendor/cubical/LICENSE`](vendor/cubical/LICENSE)
- **Upstream copyright notice:** `Copyright (c) 2018 github.com/agda/cubical contributors`

The complete snapshot is distributed unmodified, including its original license and per-file notices. Its license is MIT **with exceptions for individual files**, identified by SPDX markers. The dependency is not uniformly MIT-licensed.

### BSD-3-Clause exception

The following file carries `SPDX-License-Identifier: BSD-3-Clause` in this pinned snapshot:

- [`Cubical/Tactics/Reflection.agda`](vendor/cubical/Cubical/Tactics/Reflection.agda). Its original comment states that most utilities are copied/adapted from 1Lab; that attribution is preserved.

The original dependency license refers to the [BSD-3-Clause license text](https://opensource.org/license/bsd-3-clause/). Its redistribution conditions include retention of applicable copyright notices, conditions, and disclaimers, and prohibit using copyright-holder or contributor names to endorse derived products without permission. Consult the original license and file notices for the controlling terms; this summary does not replace them or assign additional copyright ownership.

Keep the original dependency license and all individual notices with redistributions. The lock and full file manifest are [`agda/deps.lock.json`](agda/deps.lock.json) and [`agda/deps/cubical-files.sha256.json`](agda/deps/cubical-files.sha256.json).

## Project compatibility adapter

[`DeloopS3.Compat.Whitehead`](agda/src/DeloopS3/Compat/Whitehead.agda) is a project-owned import/reexport adapter. It reexports three existing declarations from `Cubical.Homotopy.Whitehead`; it copies no upstream mathematical definitions or proof bodies and changes no dependency file. The upstream declarations remain governed by their original licenses.
