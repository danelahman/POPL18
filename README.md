This repository contains the formalisation accompanying the examples given in Section 7 of the paper

 &nbsp;&nbsp;&nbsp;&nbsp; D. Ahman. Handling fibred algebraic effects. (Conditionally accepted to POPL 2018, link to appear here)

In these examples, we show that effect handlers provide a useful mechanism for reasoning about effectful programs.
This formalisation is based on an embedding of the relevant value fragment of the language we present in the
above-mentioned paper (eMLTT) in the dependently typed programming language/proof assistant [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php).

We have disabled Axiom K and limited Agda's pattern-matching to the definitions of the elimination forms for the embeddings
of eMLTT types, and to the occasional simulation of the definitional eta equation of eMLTT's unit type.

The formalisation consists of the following files:

- `eMLTT.agda` - contains the shallow embedding of eMLTT's propositional equality (including the derivations of the transport and
congruence rules), the empty type, the unit type, the coproduct type, the product type, and the universe a la Tarski; the
embeddings of the types of thunks are given in example-specific files.

Chapter 7.1 (Lifting predicates from return values to IO-computations):

- `IOLifting.agda` - demonstrates how handlers can be used to define the possibility and necessity modalities.

Chapter 7.1 (Lifting predicates from return values to stateful computations):

- `StatePassing.agda` - contains the shallow embedding of the types of locations and values stored at them; assumes the equality on
locations is decidable and that the type of locations is a set, in the sense of Homotopy Type Theory; and defines the natural
state-passing representation of stateful computations.

- `StateEquations.agda` - contains witnesses for the propositional proof obligations corresponding to the five equations of the algebraic
theory of global state given in Section 3.2 of the above-mentioned paper, highlighting that the definition of the witness for the second
equation needs the type of locations to be a set.

- `StateLifting.agda` - contains the definition of the handling construct that handles stateful computations into their natural state-passing
representation; defines Dijkstra's weakest precondition predicate transformer using this handling construct; and demonstrates that
the natural equations listed in the paper indeed hold definitionally.

- `Sets.agda` - shows that being a set is closed under finite products and coproducts (by spelling out details of the relevant
examples and exercises from the [Homotopy Type Theory book](https://homotopytypetheory.org/book/)); in particular, demonstrating that
the natural candidate type of locations \(1 + ... + 1\), i.e., the finite set of memory locations, is indeed a set in the sense of HoTT.
These proofs do not need the univalence axiom, and thus fit in the language we present in the paper.

- `SimpleStatePassing.agda`, `SimpleStateEquations.agda`, `SimpleStateLifting.agda` - are variants of the files described above for a version of
this example where the types of values stored in the memory do not depend on memory locations, meaning that we do not need to assume the
type of locations to be a set for the proofs.

Section 7.2 (Disabling writes):

- `IONoWrites.agda` - demonstrates how handlers can be used to define the predicate that disallows all writes. 

Section 7.2 (Patterns of IO-effects):

- `IOPatterns.agda` - contains the definition of the type of protocols; and demonstrates how handlers can be used to define the predicate
that holds when the computation follows the given protocol.
