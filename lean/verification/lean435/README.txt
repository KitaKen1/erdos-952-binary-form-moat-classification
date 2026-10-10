Pinned all-degree binary-form moat classification Lake project

This standalone entry point preserves the legacy root 4.34.1 project.
Lean: 4.35.0-rc3
Mathlib: f6090c7095e1e56b3464c1daba5f24631f1290d2

The vendor directory contains only the selected unchanged source closures:
TauCeti 271 files, lean-pool 13 files, PFR 27 files, with upstream licenses.
source-lock.json identifies every source and upstream commit. The original
302 local Lean files are read from ../.., with output in ../../build/lake435.
The complete selected source set therefore has 613 distinct modules.

On a machine with the pinned toolchain, from this directory:
  lake exe cache get
  lake --wfail --no-cache build +Integrations.Unified435:olean +Moat:olean

The --no-cache option disables automatic package build-cache fetching during
the proof build; the preceding command intentionally supplies mathlib's cache.
allowNonModules=true explicitly permits the exact original legacy source files
to interoperate with module-system dependencies. It does not change declarations,
axioms, imports or proof terms. Lean compiler warnings are still errors.

Portable source-only reproduction, from the repository root:
  python3 scripts/prepare_classification_bundle.py --destination /tmp/moat-classification-review

Use a new destination. Change to that bundle directory, then run:
  python3 scripts/verify_classification_project.py --fresh-dependencies
  python3 scripts/compare_classification.py --lake
  python3 scripts/replay_classification.py --lake

The portable verifier checks initially absent dependency/object/cache directories,
downloads the exact locked git packages and official mathlib object cache, then
builds all 613 selected proof modules with compiler warnings treated as errors.
It reuses the installed pinned compiler. It does not build the compiler and all
mathlib sources from zero. Receipts include source/object/config/log hashes and
all 1730 standard-axiom audits. After a network interruption, --resume preserves
the initial baseline and logs; do not delete that evidence and call it fresh.
No historical research checkout in /tmp is required by this portable route.
The manual workflow in .github/workflows/classification-reproduction.yml uses it;
a prepared workflow is separate from an actual successful Linux CI run.

The default target imports and audits the original proved classification in
Moat.Conjectures. The root BinaryFormMoat module remains the light core.

Developer preparation using the existing pinned research checkouts, from the
repository root (not required when these vendor sources are already present):
  python3 scripts/prepare_classification_lake.py --local-cache

That preparation validates every selected source against its exact git blob.
--local-cache creates mathlib/package checkout links; it does not download fresh
dependencies or count as a proof build. It refuses to replace existing package
directories. Source-lock flags describe preparation; successful builds have a
separate classification-lake-verification.json receipt.

After a successful build, from the repository root:
  python3 scripts/report_classification_lake.py
  python3 scripts/replay_classification.py --lake --reuse-certified-export

The replay command exports all proof dependencies of the original three main
theorems, permits only propext, Classical.choice and Quot.sound, and checks with
the exact bundled independent nanoda kernel and Lean default kernel. A previous
successful replay is reused only for a byte-identical full export and identical
checker binaries; otherwise the checkers are executed again.

Original statement and definition comparison:
  python3 scripts/compare_classification.py --lake

That comparison restores the byte-exact pre-removal main source as a challenge,
compares all three theorem types, referenced definitions and kernel primitives
with the stock bundled Lake comparator, and checks the proved solution's axioms.
The challenge's old sorry is not accepted as a solution axiom and the generated
challenge is excluded from the verified proof-source closure.

Receipts and logs live in research/ and build/. A successful source build,
independent export replay, new dependency download in an isolated local bundle,
another-machine/Linux CI run, and external publication/submission are separate
recorded events. See research/classification-publication-roadmap.txt for the
current status and the full publication/submission/review tail.
