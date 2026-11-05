Isolated conditional patch; no shared checkout was edited.

Apply this one-label promotion only after the coordinator has accepted and integrated the unchanged 654-module supplier closure and its portable evidence into the publication candidate, verified the intended aggregate/root inclusion and run the required integration gate. This prepared patch does not assert that integration, publication or those checks have occurred.

Base is staged tree b788319b33b505d71285dfe4f4b74f704baa5d9f in /workspace/scratch/d6452c0f74c7/bounded-plain-integration-20261105.
Run `python3 verify_application.py /path/to/integration/repo` before applying. The checker is read-only and requires unchanged base register/audit/checksum bytes plus all integrated supplier source/receipt/log files at their verified hashes. SHA256SUMS is based on the staged base, so regenerate/rebase its narrow changes if supplier integration has updated it. Do not overwrite a newer aggregate checksum file.

Patch: promotion.patch. Proposed files: after/. Full before hashes and required supplier hashes: REVIEW.json. No commit/push or compiler action is included.
