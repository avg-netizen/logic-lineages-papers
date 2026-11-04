# Generic indexed computable existing ordinal fold

Target-only supporting effectivity proposal for paper09 hardness.tex lines316–319. No typed source evaluator or semantic equality is claimed here.

IndexedFold is exactly a wrapper around the existing OrdinalSyntax.fold. P and A are first-order Primcodable types; no function type is encoded. Leaf and branch are explicit computable maps on P×Nat and P×(Nat×A×A). Joint computability includes both the parameter and arbitrary raw code.

ExactRawRecursion preserves the original tag behavior: tags0,1,2,3,7 invoke leaf on the entire raw natural code; tags4,5,6 recurse on the two unpaired n/8 children, both strictly less than n. Malformed payloads and omega are not rejected or assigned a semantic value by this theorem; their behavior is precisely the supplied leaf. No typedness follows from total raw folding.

The planned computation proof uses Computable.nat_strong_rec with a finite list of all previous fold values. Out-of-range table access uses the explicit leaf(parameter,0) default, and child-decrease proves correct accesses are in range. It cannot use the existing PR-fold theorem with merely Computable branches.

The actual encoding-to-structural-term fold theorem already exists separately. Concrete leaf/branch choices, finite typed variable environment calibration, generic-G denotation correctness, full source evaluation, upper bound, runtime and publication remain separate.
