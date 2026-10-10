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

```bash
lake exe cache get
lake --wfail build
```

[Entry-point verification](evidence/entry-points.json).
[Original core build and independent kernel-check records](evidence/build_results.json).
