This repository contains the formalisation accompanying the examples given in Section 7 of the paper

 &nbsp;&nbsp;&nbsp;&nbsp; D. Ahman. **Handling Fibred Algebraic Effects.** Proc. ACM Program. Lang., v. 2, issue POPL, article 7, 2018. ([pdf](https://danelahman.github.io/papers/popl18.pdf))

In these examples, we show that effect handlers provide a useful mechanism for reasoning about effectful programs.
This formalisation is based on an embedding of the relevant value fragment of the language we present in the
paper (eMLTT) in the dependently typed programming language/proof
assistant [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) (tested to work with version 2.5.3).

We have disabled Axiom K and limited Agda's pattern-matching to the definitions of the elimination forms for the embeddings
of eMLTT types, and to the occasional simulation of the definitional eta-equation of eMLTT's unit type.

The formalisation consists of the following files:

- `eMLTT.agda` - contains the shallow embedding of eMLTT's propositional equality (including the derivations of the transport and
congruence rules), the empty type, the unit type, the coproduct type, the product type, and the universe a la Tarski used in Section 7; the
embeddings of the types of thunks are given in example-specific files.

Section 7.1 (Lifting predicates from return values to IO-computations):

- `IOLifting.agda` - demonstrates how handlers can be used to define the possibility and necessity modalities.

Section 7.1 (Lifting predicates from return values to stateful computations):

- `StatePassing.agda` - contains the shallow embedding of the types of locations and values stored at them; assumes that the
propositional equality on locations is decidable; uses [Hedberg's theorem](http://dblp.org/rec/journals/jfp/Hedberg98) to show that as the type of locations has decidable equality, it is also a
set in the sense of Homotopy Type Theory (Def. 3.1.1 in the [Homotopy Type Theory book](https://homotopytypetheory.org/book/)); and defines the natural state-passing representation of stateful computations.

- `StateEquations.agda` - contains witnesses for the propositional proof obligations corresponding to the five equations of the algebraic
theory of global state given in Section 3.2 of the above-mentioned paper, highlighting that the proof of the second
equation needs the type of locations to be a set (which follows from it having a decidable equality using Hedberg's theorem, as shown in `StatePassing.agda`).

- `StateLifting.agda` - contains the definition of the handling construct that handles stateful computations into their natural state-passing
representation; defines Dijkstra's weakest precondition predicate transformer using this handling construct; and demonstrates that
the natural equations listed in the paper indeed hold definitionally.

- `DecExamples.agda` - shows that decidability of propositional equality is closed under finite products and coproducts;
in particular, demonstrating that the natural candidate type of locations \(1 + ... + 1\), i.e., the finite set of memory
locations, indeed comes with a decidable propositional equality as required in Section 3.2 of the paper.
Note that these proofs do not need the
univalence axiom, and thus fit in the language we present in the paper.

- `SimpleStatePassing.agda`, `SimpleStateEquations.agda`, `SimpleStateLifting.agda` - are variants of the above files
for a simpler variant of
this example where the types of stored values do not depend on memory locations.

Section 7.2 (Disabling writes):

- `IONoWrites.agda` - demonstrates how handlers can be used to define the predicate that disallows all writes. 

Section 7.2 (Patterns of IO-effects):

- `IOPatterns.agda` - contains the definition of the type of protocols; and demonstrates how handlers can be used to define the predicate
that holds when the computation follows the given protocol.
