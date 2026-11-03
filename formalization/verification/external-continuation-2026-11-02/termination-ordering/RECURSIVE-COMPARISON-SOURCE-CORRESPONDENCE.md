# First reconstructed paper06 component — original finite recursive comparison

Current remote baseline is the verified resume checkpoint df8b48e3c69469fbf8bc1becdedbd30e3f980d83
on the cumulative external-continuation branch. Prior November 1 conversation
supplies design guidance only: no lost proof bytes or acceptance are presumed.

Source: 06-godel-t-termination-ordering/paper.tex, recursive comparison section
(ordinary clauses Var, Abs, Fun, Put, Select, F-Abs, Copy, Stat; strict marking;
occurrence-preserving generalized multiset explanation).

The five mutually inductive predicates are exactly Weak, Strict, WeakMatch,
StrictMultiset and ReplacementMatch. All derivations are finite. Fun uses an
actual permutation of target occurrences and aligned weak comparisons. Stat
uses only source base arguments, not extras. Its replacement keeps aligned
weak pairs, removes a nonempty source part, and requires each inserted target
occurrence strictly below some removed source occurrence; removal with no
replacement is allowed. No injection of distinct replacements is required.

Select includes zero arguments, uses the original simultaneous special
application (never unary iteration), and supplies retyped copies of the entire
marked source for every requested suffix argument. F-Abs weakens every actual
base/extra term to the fresh de Bruijn binder and appends that variable.
Copy and Stat retain every whole-source target-argument premise. Head classes
match native/application/ranked precedence in the paper. Ranked precedence is
a parameter; native-above-application is fixed. Strict marking traverses the
initial lambda spine, fails at variables and already marked heads, and marks
ordinary heads. This differs intentionally from the helper's idempotent
markSpine behavior on already-marked syntax.

The six exact targets are type preservation for Weak and Strict, impossibility
of Strict from an already marked source, successful strict-mark agreement with
the existing helper, Strict inclusion in Weak, and Weak reflexivity on ordinary
embedded terms. The last is not claimed for arbitrary marked targets. These
are a small source-semantic prerequisite component, not the finite comparator,
strong-pair theorem, whole finite closure, well-foundedness or adequacy.

Only this one component may be outstanding until its fresh exact gates,
independent acceptance, and remote publication are verified. No candidate
proof exists before clean comparator compilation and prospective freeze.
