# Minimal source correspondence for lem:elementary

Do not duplicate the named derivation calculus: foundations.tex explicitly
permits typed de Bruijn implementation. The independent Alpha relation now has
checked exact encoding characterization, both roundtrips, actual typing and
signature-validity equivalences. OpeningBridge is the actual same-fresh-name
binder operation, not a postulated identification. Full original-spine calls
already have literal original-head branching, simultaneous binder substitution,
typed result and success-only substitution covariance; arbitrary arrow prefixes
were retained in Select. Occurrence Split/Remove/At witnesses preserve actual
positions, repeatable supply and discard, and Stat omits extras.

Add one exact operation identity needed to transfer the elementary statement:
mark(encode env q) = Option.map (encode env) (Term.mark q), for every outside
typed-name environment. Both are existing actual persistent mark definitions.
It includes variable blocking, lambda spines and already-marked owners. No
comparison oracle or pre-supplied preservation assumption is introduced.

Source lem:elementary has three assertions. Target ordinariness is already
proved on the complete reviewed mutual relation: every rule's actual target
is treated (fresh opening reflection for Abs/FAbs, occurrence matching for Fun,
Whole premises for Copy/Stat, inherited target for Put/Select/Strict). Remaining
StrictIncluded will peel the actual successful mark, using Put at an ordinary
head, identity at an already-marked head, and Abs under fresh opening. Prove
mark's actual free-name preservation and actual bound-substitution covariance
internally to transport that opening. OrdinaryReflexive will use Var/Fun with
identity positional matching and Abs with a constructed fresh name, actual
opening typing/validity and a constructor-count induction. No weak reflexivity
of arbitrary marked terms is substituted for ordinary reflexivity.

Please independently review whether these existing exact correspondences plus
the new MarkEncoding identity suffice for this specific source lemma on the
explicitly permitted DB presentation. This is not a claim that all later cut,
context, support, or decidability arguments have been transported or proved.
