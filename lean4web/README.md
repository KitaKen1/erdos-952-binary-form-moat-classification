# Lean4Web

Select **v4.35.0-rc4** at [Lean4Web](https://live.lean-lang.org/) and paste
[BinaryFormMoatLean4Web.lean](BinaryFormMoatLean4Web.lean).

This single file contains the complete all-degree binary-form moat classification
and its custom proof dependencies. It imports only Mathlib.
The file proves the three FC targets: `gaussian_moat`,
`gaussian_moat.generalizedvariant` and `binary_form_moat_classification`,
in namespace `BinaryFormMoatCatalogue`. It ends with `#print axioms` for each.
Intermediate axiom prints are omitted to reduce Lean4Web diagnostics; the modular
sources retain those audits.

The file compiled locally and on the public Lean4Web rc4 server with no `sorry`.
All three targets use only `propext`, `Classical.choice` and `Quot.sound`.

```bash
lake exe cache get
lake --wfail build
```
