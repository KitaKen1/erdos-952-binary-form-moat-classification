# Lean4Web

[Open the current proof snapshot in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-952-binary-form-moat-classification%2Fa0d2c03836009eba943fb4f709656042256b1f83%2Flean4web%2FBinaryFormMoatLean4Web.lean).
This link uses an immutable commit URL to avoid loading a cached `main` file.

Select **v4.35.0-rc4** at [Lean4Web](https://live.lean-lang.org/) and paste
[BinaryFormMoatLean4Web.lean](BinaryFormMoatLean4Web.lean).

This single file contains the complete all-degree binary-form moat classification
and its custom proof dependencies. It imports only Mathlib.
The file uses the definitions and sequence-form statements from [FClikelean/](../FClikelean/).
Its final proof entries are the same three targets as the modular [lean/](../lean/) project:

- `Erdos952.erdos_952_openai`
- `Erdos952.erdos_952_openai_generalized_variant`
- `BinaryFormMoatClassification.binary_form_moat_classification`

Each target theorem is followed by `#print axioms`. Both `FewPrimeFactors`
definitions are reproduced from the corresponding FC files. FC's `answer(False)`
is written as `False`, and FC catalogue attributes are omitted.
Intermediate axiom prints are omitted to reduce Lean4Web diagnostics; the modular
sources retain those audits.

A previous complete-file compilation with Lean **v4.35.0-rc4** was interrupted
by a host restart before the final axiom audits completed. The current generated
file includes a compatibility fix for Latest Mathlib and has not been fully verified.
[Current compilation status](../lean/evidence/direct-fc-browser-verification.json).
The unchanged modular counterparts were checked with Lean **v4.35.0-rc3**;
all three use only `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
[Modular entry-point verification](../lean/evidence/entry-points.json).

```bash
lake exe cache get
lake --wfail build
```

To regenerate the file from the modular proof entries, run this from the repository root:

```bash
python3 lean/scripts/make_lean4web.py
```

The generator checks definitions and target statements against the FC files before
embedding the complete proof dependencies and the three final proof entries.
The browser file proves `spanSingleton` multiplication and its value at one
directly through their submodules. These proofs replace the four deprecated
alias references and use no version-dependent tactic branches.
