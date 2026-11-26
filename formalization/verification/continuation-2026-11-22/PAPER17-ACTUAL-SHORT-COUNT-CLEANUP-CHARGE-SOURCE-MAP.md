# Monotone charge for the literal short-count deletion

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
164–195 defines support charge after combining duplicate signed fields,
and 197–224 removes short counts before continuing exact normalization.

The cleanup predicate depends only on the original operand key. Every
occurrence of one key is therefore kept or discarded together, even
with repeated or canceling signed coefficients. The grouped coefficient
of any retained key is unchanged; a discarded key has coefficient zero.
Hence the actual ranked ordinary value column is unchanged and its
value count is unchanged. The actual ranked count column is literally
the original count column filtered by its same original count key's
short classifier. Its support is a subset, so its positive finite
rank charge cannot increase. The installed signed constant does not
enter either column's charge. This structural statement needs no
actual read/domain assumption; #908 is what authorizes the numeric
value and domain results for that actual deletion.

The combined exact step starts with the original #905 antecedents.
On the same #905 output, #908 installs the exact signed short offset
and gives the literal retained live reads, long-count shape, original
rank witnesses and unchanged value. The cleanup charge bound composes
with the previous strict zero-step charge. The intermediate compared
row/witness remains exposed, and the cleaned output is a distinct
deletion, not claimed to be another abstract ZeroClassReplacement.

No next-node annotation tail, guard closure, arbitrary replay,
repeated loop, dimension induction or effectivity claim.
