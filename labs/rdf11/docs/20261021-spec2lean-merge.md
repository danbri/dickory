# Spec2Lean requirements merge review

Date: 2026-10-21. Status: requirements merged; no implementation of the new catalogue, viewer, registry or certificates is claimed.

The canonical working document is [spec2lean-requirements.md](../spec2lean-requirements.md). The separately supplied root-level `spec2lean-draft.md` was read in full and left unchanged. All merge writes are confined to `_LEAN`.

## Inputs and provenance

- [Incoming draft snapshot](../evidence/spec2lean-merge-20261021/incoming-draft.md): SHA-256 `caea196dd4193803963990576208fc9c267224c83597cd22fa6c50ade87eec6e`.
- [Previous requirements snapshot](../evidence/spec2lean-merge-20261021/requirements-before.md): SHA-256 `cff2d1a8f7288908c3b0f9e13553da7873d8d0ad6bbad0fbe1986ba40e4831d7`.
- [Input manifest](../evidence/spec2lean-merge-20261021/inputs.json) retains byte lengths, source paths and snapshot timestamp. The [result manifest](../evidence/spec2lean-merge-20261021/result.json) records the merged digest and structural checks; [requirements.diff](../evidence/spec2lean-merge-20261021/requirements.diff) shows the complete change.

## What the incoming draft contributed

| Incoming material | Merge treatment |
|---|---|
| Purpose, two reviews and scoped RDF 1.1 corpus | Already aligned; preserved the existing stronger separation of source, extraction, formalization and product evidence |
| Source acquisition, hashes and stable IDs | Added HTTP/fetch provenance, parser version/ancestry, independent evidence hashes and split/merge lineage in SRC-01/05/08 |
| Source-role/normativity/disposition distinctions | Added orthogonal fields and explicit Semantics §2 inheritance policy in CAT-09 |
| Atomic claims, scope identifiers and relationship vocabulary | Added CAT-10, preserving the existing four-category taxonomy |
| Controlled English and explicit mapping strength | Added structured intermediate-form requirements in BIND-09 and correspondence classifications in LEAN-07 |
| Recursive adequacy and model comparisons | Added LEAN-08/09, including a second worked example for interpretations and explicit fulfillment criteria |
| Proof/trust inventory | Expanded LEAN-04 to distinguish actual dependency use and the different implications of axioms, opacity, unsafe code and external evaluators |
| Source/intermediate/Lean comparison and reviewer decisions | Expanded UI-03/04 and BIND-09, retaining separately solicitable review packets |
| Illustrative YAML record | Consolidated into the existing graph/set/triple example; did not introduce invented certified offsets, missing dependencies or unresolved normativity for the already identified sethood sources |
| CI, mutation checks and permissible badges | Added CI-01–04, including valid-draft versus completed-coverage states and independently scoped evidence statuses |
| Phased plan, reconnaissance and open decisions | Extended the existing gates and implementation sequence without discarding stable requirement IDs |
| Suggested upstream location | Kept `_LEAN/spec2lean-requirements.md`, following the user's explicit isolation instruction |

## Differences resolved during review

1. **Partition versus overlaps.** The incoming wording allows one or more covering spans per character while also calling them a partition. Accountability atoms remain a unique nonoverlapping partition; the independent claim-annotation layer may overlap and use noncontiguous spans.
2. **Normativity fields.** “Example”, “diagram” and “authoring guideline” are source roles that inform normative status; they are not interchangeable values with “normative”. The archive's Semantics §2 was read to confirm the classification policy.
3. **Exclusions and completion.** A reviewed exclusion cannot make a required in-scope normative obligation disappear. Genuine non-propositional requirements may receive an appropriate reviewed fulfillment criterion; excluding substantive obligations narrows the advertised scope.
4. **Machine detection versus expert judgment.** CI can invalidate changed classifications, premises and approvals. It cannot generally establish that a newly approved English interpretation is semantically right. Semantic mutation scenarios therefore include curated expert challenge cases.
5. **Audited mapping versus audited product.** The incoming `end_to_end_audited` badge described source/formalization reviews but could be read as product verification. The merged statuses explicitly separate `spec_mapping_audited` and `implementation_refinement_audited`.
6. **Opaque declarations and trust.** An opaque declaration is not automatically an axiom or defective proof. The inventory must identify the actual proof/execution dependency and its implications.
7. **Comments versus declarations.** Inspection confirmed the introductory “deliberate enlargements” discussion in `RDF/Semantics.lean`. It also found a later `interpolationComplete` theorem with triple-term-free hypotheses despite the header describing a missing completeness direction. The requirements demand auditing actual declarations and comparison models instead of adopting either comment or theorem name as authority.

## Additions from the user's subsequent instructions

- **CTX-01–05:** resolve indexicals, anaphora, ellipsis and inherited context; retain antecedent ranges and reviewed expansion rationale; represent “thus” and similar markers as inference links rather than deleting them.
- **ART-01–08:** register the complete formal source tree, including unimported/untracked files, and all elaborated term dependencies; require ownership, lifecycle and grounding; certify structural coverage and closure while exposing extractor trust; prepare target-neutral catalogue data and target-specific adapters for future formalization systems.
- **LEAN-10 and the product-obligation table:** use the completed npm review to identify certified graph/dataset structures, recursive scoping, versioned protocols, preserved execution context, validated serializers and evidence-bearing reasoning verdicts. Audit actual refinement predicates rather than trusting names such as `WfIri`.
- **TEST-05:** record comparator limits and require packed-artifact regressions. A graph-isomorphism comparison can conceal duplicate enumeration; a native suite result cannot stand in for a different public call path.

## Validation and limits

The merge checks requirement-ID uniqueness and preservation, Markdown fence balance, local document links, pinned source hashes, and unchanged input snapshots. A diff and result digest are retained. This is a documentation change; no Lean code changed in this merge and no Lean rebuild was needed. The earlier isolated graph-invariant prototype and its completed validation remain documented in the separate local implementation-repair worknote (not included in this source-first lab).
