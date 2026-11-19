# Exact decision proof split: proposed new leaves only

The independently reviewed append-only adequacy exact check passed its
340-module closure at original caps. The first append-only decision proof
was instead resource-stopped at its final leaf after 344 passing rows,
observed 527056 KiB against the unchanged 524288 KiB cap, receipt
`1795071150044944343-6`. There was no theorem failure or available axiom
result; no decision pass is inferred. The old thin leaf and its failed
source, log and receipt are byte-identically preserved (old leaf SHA-256
`9c53c11226793580c3f00a566c7a0833876eca1c537a246f538db39d8f922f98`).

The proposed materially split, append-only proof has two new modules:

1. `ProtectedSpineDecisionLogicProof` (63-module local closure, SHA-256
   `b425b8ea6b520036a2eae33a244dce4ad93fd46644e12333fa801168e7767d14`)
   contains the original type annotation equalities and exclusion of
   weak/strict judgments on unequal annotations, the original literal
   type-support test correctness, the same blank-context field-to-root
   equation, and the original four-Boolean case logic. This file needs
   only the frozen targets and original type-annotation proof. No fixed-point
   sound/completeness proof objects are imported to elaborate any of the
   simp-heavy decision case logic. Its intermediate same-type hypothesis
   is paid exactly by the next leaf, not added to the numbered theorem.
2. `ProtectedSpineDecisionSplitChecks` (new exact alias, SHA-256
   `7baabff13316f38cc6ec18eab07e949a0417929779ccffd63a0f10c0e93c4a36`)
   applies that logical assembly. At same-typed ordinary input it supplies
   the unchanged original Inputs, blank port context, actual original
   source and observation guards from DecisionClosureInitialProof, and
   the verified exact least-fixed-point adequacy proof. It has one
   proof-level assembly call plus original root witnesses; it does not
   run simplification over the large adequacy import closure. The total
   346-module closure is one module larger, but all substantial
   elaboration is in the 63-module leaf. The resource-stopped decision
   leaf is not imported by either new file.

Endpoint is still explicitly
`ProtectedSpineDecisionTargets.Decidability`, with all ordinary well-typed
input pairs including unequal types, original weak and strict judgments and
both original confined judgments. No changed Boolean code, type/domain
support, observations, finite iteration, method, premise, comparators or
checker flags. Neither new leaf ran yet. Independent scope review and a
fresh coordinator ticket are needed; no unchanged stop retry.
