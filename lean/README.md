# Complete Lean proofs

Lean **v4.35.0-rc3**, with pinned dependencies. Three independent proof entries:

- [OpenAIVariant.lean](OpenAIVariant.lean): OpenAI's uniform Gaussian moat variant.
- [GeneralizedVariant.lean](GeneralizedVariant.lean): the generalized binary-form variant.
- [BinaryFormMoatClassification.lean](BinaryFormMoatClassification.lean):
  the independent all-degree classification.

Each entry matches its counterpart in [FClikelean/](../FClikelean/)
and ends with `#print axioms` for its target. They share one Lean project,
the checked classification in [Moat/Conjectures.lean](Moat/Conjectures.lean),
and the graph-to-walk bridge in [Moat/Catalogue.lean](Moat/Catalogue.lean).

The definitions and target statements also appear at the end of the
[single-file Lean4Web proof](../lean4web/BinaryFormMoatLean4Web.lean).
FC's `answer(False)` is written as `False` in these standalone proofs;
FC catalogue attributes are omitted. The generator checks each definition and
target statement against its FC counterpart before producing the browser file.

```bash
lake exe cache get
lake --wfail build
```

[Entry-point verification](evidence/entry-points.json).
[Partial recheck: two completed strict compilations and axiom audits](evidence/direct-fc-modular-verification.json).
The classification recheck stopped during import with a host file-limit error.
All three modular source files are unchanged from the complete entry-point verification above.
[Original core build and independent kernel-check records](evidence/build_results.json).
