# Closed original first-order program theorems

Baseline e413aa1f8035a92b4e4b8182a1c4b9a390505b0e. Accepted recursion-free
Total/Functional supplies genuine Derivation trees for every ordinary term
instance. This component closes those free parameters using the ORIGINAL
forallFin binder, producing actual Empty-variable first-order sentences.

Five frozen targets cover exact empty/last universal binder equations and
Fin order, embedding of original forallFin, finite universal introduction
and elimination from the original singleton rules, and the closed existence/
uniqueness sentences. The last target uses the original graphFormula and
existing recursionFree predicate. The total sentence binds n inputs then
one output; uniqueness binds two outputs followed by n inputs. It is not
a replacement graph, new primitive relation or altered source predicate.

Arbitrary formula contexts and terms are allowed in the binder suppliers;
no positivity or semantic truth premise. The final fragment theorem has no
caller correctness premise. Primitive recursion remains excluded. No all-PR
representability, encoded typed-preservation/application, C_tau closure,
all-term accessibility, II5, well-foundedness or whole lem:id1 claim.
No existing code, manuscript, register, checker, dependency, root import
or CI changes. Comparator sources are frozen before candidate proofs.
