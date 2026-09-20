# JSP-000745 / Erdős 894: complete statement checked locally

All five proof/audit modules have been compiled afresh locally with warnings
treated as errors and trust level zero. The complete root has only the standard
logical axioms listed in verification/Audit.log. This is not a claim of a new
mathematical result, first formalization, official verification or prize eligibility. The mathematical
target is a finite coloring of all integers avoiding every term of an arbitrary
positive integer sequence with a uniform ratio greater than one.

Known prior work must remain disclosed: plby/lean-proofs contains a complete
implementation; official PR344 presents another complete implementation at
87ea0ab4ebf1d04d9a62341f8a9025e3a713bfd6. PR1186/1271 record upstream work;
PR928/2014 must not be conflated with complete independent proofs. Earlier
qualifying submissions can take priority over this later implementation.

The new source uses the standard nested-middle-half interval argument,
residue-class decomposition of the sequence and a product coloring. Prior
source audits informed the choice of topic. This is not a clean-room or
independent-discovery claim; no prior problem-specific Lean source is copied.

Gott-L initiated the project, set its objectives and planned the research
direction. Codex carries out the proof development, Lean implementation and
internal checks. Historical mathematical and formalization credits remain
with their authors. Maintainer acceptance and any prize determination remain pending;
this local status is not evidence that a contribution has been accepted.
