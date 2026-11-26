# Internal type packet native request

Status: **complete — gate09 passed**, 2026-11-23 05:33:53 UTC. Root alone ran the fixed-limit serialized compiler. Final receipt: `build-reports/1795412014343677355-11.json`.

Frozen statement checkpoint: `LEDGER.md`; both Targets modules passed unchanged in receipt `build-reports/1795411295477093868-11.json`. Source map: `INTERNAL-TYPES-SOURCE-MAP.md`. All seven exact aliases subsequently passed the final proof gate with only `propext`, `Classical.choice`, and `Quot.sound`.

## Modules

- `LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipProof` imports the new SupportProof and provides five exact aliases.
- `LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainProof` imports the membership proof and provides two exact aliases.

## Exact aliases and frozen targets

Namespace `LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipProof`:

- `exact_LiteralTypeMembership : ExactLiteralTypeMembership`.
- `exact_FiniteProgramGuardTransfer : ExactFiniteProgramGuardTransfer`.
- `exact_FiniteProgramImageTransfer : ExactFiniteProgramImageTransfer`.
- `exact_FiniteActualTypeGuard : ExactFiniteActualTypeGuard`.
- `exact_FiniteWindowRefitGuard : ExactFiniteWindowRefitGuard`.

Their target names belong to `NumberedWindowInternalLiteralTypeMembershipTargets`.

Namespace `LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainProof`:

- `exact_OpenFiniteGrammarCodomain : ExactOpenFiniteGrammarCodomain`.
- `exact_FiniteGrammarCodomainInversion : ExactFiniteGrammarCodomainInversion`.

Their target names belong to `NumberedWindowInternalGrammarCodomainTargets`.

Every exact alias has a local `#print axioms`. Acceptance requires the exact frozen type and only `propext`, `Classical.choice`, and `Quot.sound` as foundations. Preserve any failed submitted proof bytes before repair; the frozen target/map files remain unchanged.

## Final proof hashes and scope

- Membership SupportProof: `686d49d31127a3df074bd72d62e9b4b6775611692054ef0b53cb3beadcd57123`.
- Membership Proof: `ab41683cc043a3b922c6f1c4a016bb95006fc40db488ca8b8e0faf84888a90b7`.
- Grammar Codomain Proof: `db9cc902b8f7a0014726c083fb5e5552a377f09d394955537a9cb4cfbf1d970f`.

The frozen target/map hashes remain unchanged. The three failed support editions and one failed main edition are preserved under `failed-drafts/`, with their receipts and hashes recorded in `LEDGER.md`.

Supporting-only result: actual internal finite-list membership and program transfer, followed by the original grammar codomain rule under explicit finite numeric closure. No arbitrary-settings closure, unrestricted all-type inversion, full application-guard discharge, or numbered theorem completion is claimed. No further native check is requested.
