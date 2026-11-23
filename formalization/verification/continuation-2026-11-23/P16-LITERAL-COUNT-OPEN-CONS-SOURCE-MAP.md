# Original open count at one scratch cons
The checked local literal counter is the one installed in #1548. Given
the actual scratch cons graph and a real count of the tail, the exact
step counts one extra occurrence when the head is queried, and leaves
the count unchanged for each provably different query. This only
removes a known head. A search for one arbitrary occurrence and its
whole object induction are separate.
