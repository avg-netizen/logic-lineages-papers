# Independent witness refactor review

Approved for coordinator native checking. Verified archived original8218a75c9a4f190bf3c3cf60f6516de786a1d39f94fdfcc42d4c1b4cca42f9f7, actual two proposed hashes, and byte-identical entire matrixWitness public signature. Actual diff adds helper import and replaces body only; no target/AST/definitions/limit change.

Generic helper uses the already reviewed exact eleven-slot matrix with arbitrary pair/enumeration/member Program2 and opaque Meaning. Substitution vector is exactly node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound. Result retains four actual pairing observations, actual enumeration, and both membership↔Meaning directions. Helper premise is only syntactic substitution equality, not derivability/success. It normalizes Sum.elim embedding and uses original graph2Subst/witnessLift.

Original proof instantiates exact original pairing/enumeration n/contains. The syntactic Meaning premise is discharged with original meaningSubst and witnessLift fixing the free fuel; no new public premise. Definitionally identical generic matrix must elaborate under native checking. Ordinary opaque theorem factoring, not acceptance inheritance or native-code reflection. Resource benefit unverified, prior failure preserved, full original primary gate remains unpaid. Reviewer ran no compiler.
