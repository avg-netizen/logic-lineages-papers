# A total cograph JEP algorithm through ranked-tree ideals

Source-repair working proof,30 October2026. This is a mathematical algorithm
and proof, not an implementation or Lean certification. It uses independent
standard ideal-decomposition and Parikh theorems, with new transfer lemmas
proved below. NO theorem of Carter is an input.

## 1. Exact input and the three standard inputs

Let F be a finite forbidden induced-subgraph family containing P4, and
let K=Forb(F). We decide whether K has the joint embedding property under
INDUCED graph embeddings. For paper03 take in addition C4 and the
comparability graphs of the input forbidden order forests. The already
proved forest/graph bridge then preserves and reflects graph JEP.

The proof uses these standard mathematical theorems:

* **Ranked-tree ideal decomposition.** Given a regular language L of
  finite ranked trees, a finite family of regular nonempty ideals can be
  constructed whose union is its homeomorphic downward closure. This is
  Goubault-Larrecq--Schmitz2016, Section5: the automaton-to-STRE construction,
  normalization, and tree-product characterization, Proposition18,
  Fact19, Lemma20 and Theorem23. The relation is EXACTLY their Example7,
  stated recursively in section2 below. Empty output is allowed for L empty.
* **Effective Parikh theorem.** From a finite context-free grammar and a
  specified start nonterminal one computes a Presburger description of
  its terminal-count vectors. For an explicit independent construction,
  Esparza--Ganty--Kiefer--Luttenberger, arXiv1006.3825v3, Theorem1.1 and
  Section3, constructs a Parikh-equivalent finite automaton and explains
  effective semilinear extraction. Ordinary Presburger arithmetic over N
  is decidable and closed under Boolean operations.
* **Finite-tree automata.** Determinization and Boolean operations for
  ranked regular languages are effective. These standard finite-state
  operations do not decide graph JEP by themselves.

These are explicit cited theorems; the graph decision conclusion is NOT
one of the inputs. Root's companion cotree-restriction note proves the
canonical reduced-cotree uniqueness and faithful induced restriction.
We repeat the precise uses, so a reader need not import a private convention.

## 2. Binary parses and a one-way embedding fact

We first recall the cograph characterization, with a short proof to avoid
another source dependency. Every connected P4-free graph G on at least
two vertices has disconnected complement. Induct on its size. The two-
vertex case is immediate. For larger G choose a leaf v of a spanning tree;
then H=G-v is connected. Its complement has at least two components C_i
by induction. If v is mixed on some C_i, a path in the COMPLEMENT on C_i
gives a,b there with va an edge, vb and ab nonedges. For c in any other
C_j, the cross edges ac,bc are present. If vc were absent, v,a,c,b would
be an induced P4. Hence v is complete to every other C_j, leaving those
C_j disconnected in the complement of G. If v is uniform on each C_i,
connectedness makes it complete to at least one of them, which again is
an isolated component of the complement. This proves the assertion.

Every P4-free graph therefore decomposes recursively by disjoint union
when disconnected and join of its complement-components when connected.
Conversely those two operations preserve P4-freeness: P4 is connected
and its complement is again P4. Thus binary union/join expressions from
K1 represent EXACTLY the nonempty P4-free graphs. The spanning-tree
choice above is finite and requires no additional uniformity theorem.

Use the FINITE RANKED alphabet A={a:0,U:2,J:2}. A term evaluates to a
nonempty cograph: a is one vertex, U disjoint union and J join. Terms
are ordered syntactically, although graph evaluation forgets child order.
Define s<=t recursively by either

 (dive) t=o(t1,t2) and s<=t1 or s<=t2;
 (couple) s=o(s1,s2), t=o(t1,t2), and si<=ti for i1,2;
 (leaf) s=t=a.                                             (1)

This is exactly the ranked ordered homeomorphic order in the2016 primary.
Its coupling preserves BOTH the operation symbol and arity. It is not
arbitrary parent-label contraction on general cotrees.

**Lemma1.** If s<=t then ev(s) is an induced subgraph of ev(t).

Proof by(1). Diving embeds into one child graph and then into the full
union/join. Coupling combines the two child embeddings on disjoint vertex
sets; all cross edges are absent for U and present for J on BOTH sides.
The leaf case is immediate. No converse is asserted.

**Lemma2.** For any nonempty subset B of the leaves of a binary term t,
there is a binary term t|B<=t with ev(t|B)=ev(t)[B].

Restrict children recursively. If neither contributes, return empty as
an intermediate instruction; if only one contributes, return that child
restriction, retaining its OWN operation label; if both contribute, use
the original root operation. At the nonempty root the result is a term
over A. The dive/couple clauses prove t|B<=t by induction, simultaneously
with the graph equality. Do NOT flatten adjacent equal operators here:
the result is a binary parse, not yet a reduced cotree. This is why the
lemma is valid under the exact ranked order.

## 3. The permitted parse language is effectively regular and downward

Let n be at least the size of every forbidden graph. A finite state can
record the SET of induced graph isomorphism types of size at most n,
including the empty graph. There are finitely many such types and hence
finitely many states; all are finite computable objects. The leaf state
is {empty,K1}. For o=U,J the transition on states S,T is

 {o(G,H): G in S,H in T, |G|+|H|<=n},                      (2)

where empty is the identity for either operation and graphs are replaced
by finite canonical isomorphism representatives. Every induced subgraph
of a union/join is exactly an operation on its two restrictions, so an
induction proves that (2) computes the claimed profile EXACTLY. Accept
precisely states containing none of F. Thus the binary parse language

                  L={t:ev(t) in K}                        (3)

is an effectively given regular language. Since K is hereditary, Lemma1
makes L downward under(1). The2016 construction therefore produces

                  L=I1 union ... union Im,                (4)

with each Ii a nonempty regular IDEAL for(1), not just a regular component
of a guessed decomposition. All tree products have finite regular syntax,
so ordinary tree automata for the individual Ii are effective. We use no
recognizer for graph JEP and no Carter main or corollary in this step.

If F contains the empty graph, K is empty; report YES under the vacuous
JEP convention. Otherwise empty belongs to K. If L is empty, K consists
only of the empty graph, so again report YES. The finite automaton's
emptiness test settles this case. Henceforth m>=1.

## 4. The projected ideals and the finite-cover criterion

For each i let Di={empty} union {ev(t) up to isomorphism:t in Ii}.

**Lemma3.** Each Di is a hereditary directed graph class contained in K,
and their finite union is K.

Containment and covering follow from(3)--(4) and the fact that every
nonempty cograph has a binary union/join expression. To check heredity,
choose a representation t in Ii and a nonempty induced restriction.
Lemma2 realizes that restriction by t|B<=t, which belongs to Ii because
Ii is downward. The empty restriction is included explicitly. To check
directedness, choose two representing terms s,t in Ii. Its TERM ideal
property gives a common u in Ii with s,t<=u. Lemma1 gives the required
common GRAPH host ev(u). Empty graphs cause no difficulty. This proves
all three assertions without a graph-to-term converse.

**Lemma4 (finite ideal cover).** K has graph JEP if and only if K=Di
for at least one i.

One direction is Lemma3. Conversely suppose K has JEP but no Di equals
K. Choose Gi in K\Di for each of the FINITELY many i. Iterating JEP
gives one H in K containing every Gi. By the cover, H belongs to some Dj.
Heredity of Dj then puts Gj in Dj, a contradiction. The argument uses
one common graph host; it never assumes its chosen binary parse contains
the originally selected parses s,t.

The remaining effective task is therefore the FINITE list of inclusions
K subset Di. We now give an independent decision procedure for each.

## 5. Binary association and permutation: exact AC semantics

A reduced cotree has leaves a, and internal labels U,J of arity at least
two, with adjacent internal labels unequal. Children are unordered. Binary
terms normalize by flattening adjacent equal operators. Associativity
and commutativity of union and join preserve graph evaluation. Conversely
the reduced cotree is uniquely determined by its graph: at a U root its
children are the connected graph components; at a J root they are the
connected components of the complement. Induction proves uniqueness.

Consequently ALL binary representations of one reduced cotree T are
obtained as follows: independently represent each child; at an operation
node, choose ANY full binary tree with that SAME operation everywhere,
and place the represented children at its leaves in ANY permutation.
There are no other graph equalities to quotient by. In particular
different associativity shapes must NOT be identified by a strict tree
embedding; they are identified here by this exact graph normalization.

Let M=(Q,q_a,delta_U,delta_J,F_M) be any deterministic complete binary
tree automaton. We construct a deterministic automaton with Presburger
horizontal transitions on reduced cotrees that accepts T exactly when
SOME binary representation of T is accepted by M. Its state at T will be

 S_M(T)={q in Q: some binary representation of T has M-state q}. (5)

The entire SUBSET is stored, not one arbitrary state or one chosen parse.

## 6. The constructive Parikh transition

For each operation o, make a finite context-free grammar G_o. Its
nonterminals are N_q for q in Q. Its terminal alphabet has one symbol
b_B for EVERY subset B of Q. Add the productions

 N_delta_o(r,s) -> N_r N_s      for all r,s in Q;
 N_q -> b_B                    whenever q belongs to B.     (6)

For each start N_q use the effective Parikh theorem to compute a
Presburger predicate P_(o,q)((c_B)_(B subset Q)) describing its terminal
count vectors. The grammar is finite even though its alphabet is large.

Suppose an o-node has canonical children T1,...,Tk with k>=2 and child
state subsets B1,...,Bk. Set c_B=|{j:Bj=B}|. Then

 q in S_M(T) iff P_(o,q)((c_B)).                            (7)

Proof in BOTH directions: a binary representation of this node has a
full binary o-skeleton whose leaves choose one state r_j in Bj for each
actual child. Reading the skeleton as a derivation gives (6), with the
specified multiset of terminal symbols. Conversely, a derivation with
those counts supplies a binary o-skeleton and, at EACH leaf occurrence,
a choice q in its terminal subset B. Match occurrences bijectively to
the actual children having that B, and independently choose a child
representation realizing its selected q. Assemble them in the order
specified by the skeleton. The constructed term represents the original
unordered node and has root state q. Repeated equal children and repeated
state types are counted WITH MULTIPLICITY throughout.

For a leaf, S_M={q_a}. For an o-node the deterministic transition into a
specified subset S is the Presburger formula

 AND_(q in S) P_(o,q)(c) AND AND_(q notin S) NOT P_(o,q)(c). (8)

Include the root label in the finite state, so states are (a,S),(U,S),
(J,S). Enforce k>=2 and disallow children whose operation label is o;
leaves are allowed. Counts c_B in(8) are the sums of the child-type counts
over the permitted root labels with that same subset B. All these are
linear expressions. This enforces exactly the reduced-cotree domain.
Acceptance is S intersect F_M nonempty. Equations(5)--(8), by induction,
prove its COMPLETE semantic correspondence to graph images of M's language.
No choice of a single binary association or a falsely regular AC closure
has been used: Presburger transitions are genuinely needed in general.

## 7. Effective Boolean inclusion and emptiness, not a finite search guess

For completeness, the required decision procedure for these deterministic
finite-state Presburger cotree automata is elementary. Boolean complements
just change the accepting set on the canonical domain. For products, use
pairs of states; replace each component's child-type count by the sum of
the pair-type counts with that component. Conjoin the two horizontal
predicates. These are again finite Presburger formulas. The root tag is
shared; canonical arity and alternation are enforced in the product.

Compute productive states by a least fixed point. Start with actual leaf
states. Given the current finite set R, mark state q productive if for
some root operation there is a vector of nonnegative child-type counts
that satisfies its transition, has total at least two, and is ZERO on
every child type outside R. This is a Presburger satisfiability question.
Repeat until no state is added; there are only finitely many states.

Soundness follows by selecting, for each used child type, its already
constructed finite representative and taking the finite number of copies
specified by a satisfying count vector. Completeness follows by induction
on the height of an actual finite cotree. Therefore the language is empty
exactly when no accepting state is productive. This is a TOTAL algorithm,
not a heuristic size cap or unbounded enumeration of candidate trees.

Apply sections5--7 to the automaton for L and to each automaton for Ii.
The first canonical language is exactly K without its empty graph; the
second is Di without its empty graph. Their inclusion is decided by
emptiness of the first language intersected with the complement of the
second. By Lemma3, testing this one inclusion tests equality K=Di.

For comparison, Seidl--Schwentick--Muscholl's primary *Counting in trees*,
Section3 Theorems3.2--3.3, independently gives emptiness, determinization
and Boolean closure for UNORDERED Presburger tree automata. We have given
the needed simple deterministic instance in full. We do NOT use the
different ordered/mixed models whose universality properties differ.

## 8. The total algorithm and the compulsory countercontrol

The algorithm is now explicit:

1. Handle a forbidden empty graph. Build the profile automaton(2) for L
   and handle L empty as above.
2. Use the independent2016 ideal-decomposition construction to obtain
   the finite regular ideals Ii with union L.
3. For each Ii construct the canonical Presburger automaton(6)--(8).
   Decide K subset Di by the product/emptiness calculation of section7.
4. Return YES iff one inclusion holds; return NO otherwise.

Every step terminates by a cited effective standard theorem or the explicit
finite-state procedures above. Lemmas1--4 and(5)--(8) prove correctness.
This decides the ACTUAL graph JEP relation, and the preserved forest graph
bridge supplies the intended total finite-forbidden order-forest decision.

Consider independent graphs through size4. Their all-union binary parse
language fails tree JEP, as the companion note proves. Our algorithm does
NOT test that language's JEP. Instead it decomposes it into finitely many
term ideals. The finite language is covered by principal ideals generated
by its maximal four-leaf parses (all ordered shapes are allowed). Each
such principal ideal has graph image EXACTLY the independent graphs of
sizes1 through4, by Lemma2 and leaf counts. Thus every one projects to
the whole nonempty graph class, and the algorithm correctly returns YES.
Balanced and comb parses need not have a common binary host anywhere.

## 9. Evidence grade and remaining work

This repairs the MATHEMATICAL total-decision transfer using independent
standard inputs. Its new graph-image/AC-state/inclusion lemmas require
separate review before adoption in the manuscript. No Carter main,
Corollary1.5, unranked topological encoding or unproved finite bad-pair
bound is assumed. The reported explicit dependence is on2016 ranked
ideal decomposition, effective Parikh conversion and Presburger decision.

No implementation of the full ideal/Presburger procedure or Lean proof
is claimed. A bounded control of state semantics can check an implementation
but cannot replace the all-size proof. The width classification, negative
certificate proposition, graph bridge and age theorem remain separate
valid results. After a NO result the existing finite bad-pair search still
terminates and returns a certificate, exactly as before. Historical novelty
of this repaired route is unchecked; no new original-problem count or
formal/independent-model claim follows merely from writing it.

## Primary references

* J.Goubault-Larrecq and S.Schmitz, *Deciding Piecewise Testable Separability
  for Regular Tree Languages*, ICALP2016,97:1--97:15. Example7 and Section5,
  especially Proposition18, Fact19, Lemma20 and Theorem23.
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol055-icalp2016/LIPIcs.ICALP.2016.97/LIPIcs.ICALP.2016.97.pdf
* J.Esparza, P.Ganty, S.Kiefer and M.Luttenberger, *Parikh's Theorem:
  A simple and direct automaton construction*, arXiv1006.3825v3,
  Theorem1.1 and Section3. https://arxiv.org/pdf/1006.3825
* H.Seidl, T.Schwentick and A.Muscholl, *Counting in trees*, Section3,
  Theorems3.2--3.3. https://www.labri.fr/perso/anca/Publications/ssm07wt.pdf
* D.Carter, *On the joint embedding property for cographs and trees*,
  arXiv2409.06127v1, was read for the source diagnosis only. It is NOT a
  theorem dependency of the amended proof. https://arxiv.org/html/2409.06127v1
